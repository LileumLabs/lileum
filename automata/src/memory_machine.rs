//! Extension to `StackMachine` with a read-only memory.

use alloc::vec::Vec;

use crate::stack_machine::{PopableStack, StackMachine};
use core::marker::PhantomData;

/// Extends inner intruction with a load instruction in a
/// `A` addressable memory.
pub enum MemoryInstruction<I, A> {
    Inner(I),
    LoadImmediate(A),
}

impl<I, A> From<I> for MemoryInstruction<I, A> {
    fn from(value: I) -> Self {
        Self::Inner(value)
    }
}

/// Read-only memory, `A` addresses, `V` values.
pub trait Memory<A, V> {
    fn read(&self, address: A) -> V;
}

/// Stack machine extended with a read-only, fixed access memory.
/// A LoadImmediate instruction is added to push an element from
/// a literal address into the stack.
pub struct MemoryMachine<S, M, A>(PhantomData<(S, M, A)>)
where
    S: StackMachine,
    M: Memory<A, S::StackElem>;

impl<S, M, A> MemoryMachine<S, M, A>
where
    A: Copy,
    S: StackMachine,
    M: Memory<A, S::StackElem>,
{
    /// Runs instructions, like `StackMachine::run_program`, also accepting
    /// a memory.
    pub fn run_program(
        program: &[MemoryInstruction<S::Instruction, A>],
        initial_stack: Vec<S::StackElem>,
        input: Vec<S::Input>,
        memory: &M,
    ) -> Vec<S::StackElem> {
        let mut stack: Vec<S::StackElem> = initial_stack;
        let mut input = input.into_iter();
        for instruction in program {
            match instruction {
                MemoryInstruction::Inner(instruction) => {
                    let stack = PopableStack::new(&mut stack, &mut input);
                    let _ = S::transition(instruction, stack);
                }
                MemoryInstruction::LoadImmediate(address) => {
                    let elem = memory.read(*address);
                    stack.push(elem);
                }
            }
        }
        stack
    }

    /// Finds the smallest stack size for the given program.
    pub fn bound_program(
        program: &[MemoryInstruction<S::Instruction, A>],
        initial_stack: Vec<S::StackElem>,
        input: Vec<S::Input>,
        memory: &M,
    ) -> usize {
        let mut stack: Vec<S::StackElem> = initial_stack;
        let mut input = input.into_iter();
        let mut bound = 0;
        for instruction in program {
            match instruction {
                MemoryInstruction::Inner(instruction) => {
                    let stack = PopableStack::new(&mut stack, &mut input);
                    let _ = S::transition(instruction, stack);
                }
                MemoryInstruction::LoadImmediate(address) => {
                    let elem = memory.read(*address);
                    stack.push(elem);
                }
            }
            bound = bound.max(stack.len());
        }
        bound
    }
}
