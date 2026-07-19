//! Optimized machine to evaluate polynomials over sumcheck messages,
//! which are univariate polynomials.
//! It allocates no additional memory, and has decent cache locality.
//! It does not utilize the abstraction in `automata`, as generalizing
//! them for this unique use case would add too much complexity.

use crate::symbolic::{evaluate::MvIr, expression::VarOrChall};
use ark_ff::Field;
use std::cmp::Ord;

/// Instruction set optimized for univariate polynomials
/// (in evaluation form) as operands.
#[derive(Debug, Clone, Copy)]
enum Instruction<V> {
    Add,
    Mul,
    Load(V),
    Eval,
    EvalWithCoeff,
    LoadChall(V),
    LoadChallWithCoeff(V),
    AddCoeff,
}

/// Translate instruction set, also extracting coeffcients into a
/// Vec<F>.
fn translate<F: Field, V>(
    program: Vec<MvIr<F, VarOrChall<V, V>>>,
) -> (Vec<Instruction<V>>, Vec<F>) {
    use Instruction::*;
    let mut instructions: Vec<Instruction<V>> = vec![];
    let mut coeffs = vec![];
    for instruction in program {
        match instruction {
            MvIr::PushChild(coeff, var) => {
                // if coeff = 1 we can just skip the multiplication.
                let coeff_one: bool = coeff.is_one();
                coeffs.extend((!coeff_one).then_some(coeff));
                match var {
                    VarOrChall::Var(var) => {
                        instructions.push(Load(var));
                        instructions.push(if coeff_one { Eval } else { EvalWithCoeff });
                    }
                    VarOrChall::Challenge(chall) => {
                        let c1 = coeff_one;
                        let load = if c1 { LoadChall } else { LoadChallWithCoeff };
                        instructions.push(load(chall));
                    }
                }
            }
            MvIr::Add => {
                instructions.push(Add);
            }
            MvIr::Mul(var) => match var {
                VarOrChall::Var(var) => {
                    instructions.extend([Load(var), Eval, Mul]);
                }
                VarOrChall::Challenge(chall) => {
                    instructions.extend([LoadChall(chall), Mul]);
                }
            },
            MvIr::AddConstantTerm(coeff) => {
                coeffs.push(coeff);
                instructions.push(AddCoeff);
            }
        }
    }
    (instructions, coeffs)
}

/// Splits off, 2 &mut [F] of length message_len from the top of the stack.
fn pop_2<F>(stack: &mut [F], message_len: usize) -> [&mut [F]; 2] {
    let split_at = stack.len() - (message_len * 2);
    let (_, right) = stack.split_at_mut(split_at);
    let (left, right) = right.split_at_mut(message_len);
    [left, right]
}

/// Based on `Message::new_degree_n`, extends the stack with the evals.
fn eval<F: Field>(e0: F, e1: F, stack: &mut Vec<F>, message_len: usize) {
    // P(x) = (e1 - e0)x + e0
    let original_len = stack.len();
    stack.resize(original_len + message_len, e0);
    let (_, evals) = stack.split_at_mut(original_len);

    let diff = e1 - e0;
    let mut last = F::zero();
    for e in evals {
        let e: &mut F = e;
        *e += last;
        last += diff;
    }
}

/// Stack machine optimized to operate over univariate polynomials, the
/// sumcheck messages specifically.
#[derive(Debug, Clone)]
pub(crate) struct MessageEvaluator<F, V> {
    program: Vec<Instruction<V>>,
    coefficients: Vec<F>,
    vars: Vec<(F, F)>,
    challenges: Vec<F>,
    stack: Vec<F>,
    message_len: usize,
}

/// Could be implemented for a bigger integer than u8.
impl<F: Field> MessageEvaluator<F, u8> {
    pub(crate) fn new(ir: Vec<MvIr<F, VarOrChall<u8, u8>>>, message_len: usize) -> Self {
        let (program, coefficients) = translate(ir);
        let (bound, vars, challs) = Self::analyze(&program, message_len);
        let vars = vec![(F::zero(), F::zero()); vars as usize + 1];
        let challenges = vec![F::zero(); challs as usize + 1];
        // Add space for an extra message, the accumulated value.
        let stack = Vec::with_capacity(bound + message_len);
        Self {
            program,
            coefficients,
            vars,
            challenges,
            stack,
            message_len,
        }
    }
    /// Returns (stack_bound, highest_var, highest_chall).
    fn analyze(program: &[Instruction<u8>], message_size: usize) -> (usize, u8, u8) {
        use Instruction::*;
        let mut bound = 0;
        let mut stack = 0;
        let mut highest_var = 0;
        let mut highest_chall = 0;
        for instruction in program {
            let instruction: &Instruction<u8> = instruction;
            stack = match instruction {
                Add | Mul => stack - message_size,
                Load(var) => {
                    highest_var = Ord::max(highest_var, *var);
                    stack + 2
                }
                LoadChall(chall) | LoadChallWithCoeff(chall) => {
                    highest_chall = Ord::max(highest_chall, *chall);
                    stack + message_size
                }
                Eval | EvalWithCoeff => (stack - 2) + message_size,
                AddCoeff => stack,
            };
            bound = Ord::max(bound, stack);
        }
        (bound, highest_var, highest_chall)
    }
    /// Eval leaving the result as the only elements in the stack.
    /// Before call, variables should be set, and stack must be empty.
    pub(crate) fn eval(&mut self) {
        let stack = &mut self.stack;
        let mut coeffs = self.coefficients.iter();
        let message_len = self.message_len;
        let memory = &self.vars;
        let challenges = &self.challenges;

        for instruction in &self.program {
            let instruction: &Instruction<u8> = instruction;
            match instruction {
                Instruction::Add => {
                    let [left, right] = pop_2(stack, message_len);
                    for (a, b) in left.iter_mut().zip(right) {
                        a.add_assign(b)
                    }
                    stack.truncate(stack.len() - message_len);
                }
                Instruction::Mul => {
                    let [left, right] = pop_2(stack, message_len);
                    for (a, b) in left.iter_mut().zip(right) {
                        *a *= b;
                    }
                    stack.truncate(stack.len() - message_len);
                }
                Instruction::Load(var) => {
                    let (e0, e1) = memory[*var as usize];
                    stack.push(e0);
                    stack.push(e1);
                }
                Instruction::LoadChall(chall_idx) => {
                    let chall = challenges[*chall_idx as usize];
                    let original_len = stack.len();
                    stack.resize(original_len + message_len, chall);
                }
                Instruction::LoadChallWithCoeff(chall_idx) => {
                    let coeff: &F = coeffs.next().unwrap();
                    let chall: F = challenges[*chall_idx as usize];
                    let original_len = stack.len();
                    stack.resize(original_len + message_len, chall * coeff);
                }
                Instruction::Eval => {
                    let e1 = stack.pop().unwrap();
                    let e0 = stack.pop().unwrap();
                    eval(e0, e1, stack, message_len);
                }
                Instruction::EvalWithCoeff => {
                    let coeff: &F = coeffs.next().unwrap();
                    let mut e1 = stack.pop().unwrap();
                    let mut e0 = stack.pop().unwrap();
                    e0 *= coeff;
                    e1 *= coeff;
                    eval(e0, e1, stack, message_len);
                }
                Instruction::AddCoeff => {
                    let coeff: &F = coeffs.next().unwrap();
                    let [_, right] = pop_2(stack, message_len);
                    for x in right.iter_mut() {
                        *x += coeff;
                    }
                }
            }
        }
    }

    /// Returns result left on the stack, panics on unexpected
    /// stack size.
    pub(crate) fn result(&self) -> &[F] {
        assert_eq!(self.stack.len(), self.message_len);
        &self.stack
    }

    /// Truncates stack to length 0, then extends it
    /// with the provided elements.
    pub(crate) fn set_stack(&mut self, new_stack: &[F]) {
        self.stack.clear();
        self.stack.extend(new_stack);
    }

    pub(crate) fn set_var(&mut self, idx: usize, eval: (F, F)) {
        self.vars[idx] = eval;
    }

    pub(crate) fn set_chall(&mut self, idx: usize, chall: F) {
        self.challenges[idx] = chall;
    }
}
