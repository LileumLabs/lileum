use alloc::vec::Vec;

/// Stack from which elements cab be popped.
pub struct PopableStack<'a, S: StackMachine> {
    pub(crate) stack: &'a mut Vec<S::StackElem>,
    input: Input<'a, S::Input>,
}

/// Stach to which elements can be pushed.
pub struct PushableStack<'a, T, const N: usize> {
    pub(crate) stack: &'a mut Vec<T>,
}

/// Allows to take an input element, taking an input is optional.
pub struct Input<'a, T> {
    input: &'a mut alloc::vec::IntoIter<T>,
}

/// obtained after pop, contains elements, stack, and input.
pub struct PopResult<'a, S: StackMachine, const P: usize, const N: usize> {
    pub popped_elements: [S::StackElem; P],
    pub stack: PushableStack<'a, S::StackElem, N>,
    pub input: Input<'a, S::Input>,
}

impl<'a, S: StackMachine> PopableStack<'a, S> {
    pub(crate) fn new(
        stack: &'a mut Vec<S::StackElem>,
        input: &'a mut alloc::vec::IntoIter<S::Input>,
    ) -> Self {
        let input = Input { input };
        Self { stack, input }
    }

    pub fn pop<const P: usize, const N: usize>(self) -> PopResult<'a, S, P, N> {
        let Self { stack, input } = self;
        let popped_elements = [(); P].map(|_| stack.pop().unwrap());
        let stack = PushableStack { stack };
        PopResult {
            popped_elements,
            stack,
            input,
        }
    }
}

/// Type that must be returned at the end of each transition
/// to ensure elements poped and pushed from the stack as
/// expected.
pub struct End(());

impl<T, const N: usize> PushableStack<'_, T, N> {
    /// Pushes N elements, gives back `End` needed to return from transition.
    pub fn push(self, elems: [T; N]) -> End {
        self.stack.extend(elems);
        End(())
    }
}

impl<T> Input<'_, T> {
    /// Take an input element
    pub fn take(self) -> T {
        // There should always be enough input
        self.input.next().expect("no more input")
    }
}

/// Stack machine, types aim to guarantee control flow remaining constant for a given
/// program, allowing to bound the stack for a given program.
/// It can be considered as a pushdown automaton for arbitrary programns, and a fsm for
/// a given program.
pub trait StackMachine: Sized {
    /// Type of stack elements.
    type StackElem;
    type Instruction;
    /// type of input, being optional it can be just ().
    type Input;
    /// Machine transition, control flow should depend only on the instraction.
    /// The stack enforces that by allowing to pop N elements once, and at the
    /// same time determining how many elements will be pushed.
    /// Finally, this function must return `End`, which can only be obtained
    /// by pushing the defined number of elements.
    fn transition(instruction: &Self::Instruction, stack: PopableStack<Self>) -> End;
    /// Runs instructions, returning final stack.
    fn run_program(
        program: &[Self::Instruction],
        initial_stack: Vec<Self::StackElem>,
        input: Vec<Self::Input>,
    ) -> Vec<Self::StackElem> {
        let mut stack: Vec<Self::StackElem> = initial_stack;
        let mut input = input.into_iter();
        for instruction in program {
            let stack = PopableStack::new(&mut stack, &mut input);
            let _ = Self::transition(instruction, stack);
        }
        stack
    }
    /// Finds the smallest stack size for the given program.
    fn bound_program(
        program: &[Self::Instruction],
        initial_stack: Vec<Self::StackElem>,
        input: Vec<Self::Input>,
    ) -> usize {
        let mut stack: Vec<Self::StackElem> = initial_stack;
        let mut input = input.into_iter();
        let mut bound = stack.len();
        for instruction in program {
            let stack_wrapped = PopableStack::new(&mut stack, &mut input);
            let _ = Self::transition(instruction, stack_wrapped);
            bound = stack.len().max(bound);
        }
        bound
    }
}
