# Lileum

A customizable proof system.

- [x] Generic over field and (homomorphic) commitment scheme.
- [x] Arbitrary degree, circuit-level, user defined custom gates.
- [x] Folding.
- [x] High-level API for building circuits in Rust with witness generation.
- [x] Generic and composable circuits.
- [x] Small in code and number of dependencies.
- [ ] Private recursion (IVC).
- [ ] Public recursion (PCD?).
- [ ] Support for lookups and lookup gates.

## Introduction

Lileum is an argument of knowledge for arithmetic circuits.
If a digital circuit has bits for values and OR and AND for gates.
An arithmetic circuit has field (like natural module some prime) elements for
values and addition and multiplication for gates.
An arithmetic circuit is a set of variables and gates/constraints connecting them.
Lileum allows you to prove that you know a value assignment for each variable such
that all constraints are satisfied, and most importantly, without revealing
the values.

For example this circuit:

$$x - 3 = 0$$

If you $$x = 3$$, then you can prove it without revealing the value of x.
The/a witness can be said to be 3.

But this:

$$x^2 + 1 = 0$$

There is not possible witness, and you can not know something which
doesn't exits.
What about this? It should have some solution:

$$x^6 - 1 + x^5 = 0$$

But if you don't know it, you can't prove it. Existence is not enough,
you need knowledge.

### Why to use it

#### Example 1

Let's say you have some number X you really like, and want to keep it only
for yourself, and let's say that X is also a square.
But some day, someone claims that your number is not a square, you can't
ignore such accusation, you need to prove that X is a square.
The easiest would be to provide X and some w, then anyone can check that
X = w^2, but everyone would get not know your X, something unacceptable.
Is it possible to prove that X is a square without revealing X?

#### Example 2

Given the Fibonacci sequence:
fib(0) = 0
fib(1) = 1
fib(i+2) = fib(i) + fib(i+1)

You want to know fib(1000), there is nothing secret, anyone can compute it,
but it takes time. It would be useful if someone could compute it for you.
Can someone prove that fib(1000) = X, without you having to evaluate fib()
1000 times to verify it is correct?

#### Example 3

You want to prove your bank account has at least $30, but you don't
to reveal exactly how much money you have ($31).
Can you prove x >= 30 without revealing x?

### How to use it

The answer to these 3 examples is yes, but how?
The overall approach is the same:

- Create a circuit representing our statement, or a family of statement
of which ours is a particular instance.
- Create a circuit key for the circuit using lileum.
- Make a proof of our statement using the key.
- Verify the proof using the key.

The full examples can be found in [lileum/examples/](./lileum/examples/).

#### Creating a circuit

A circuit is just a type implementing the Circuit trait, you
can implement it for a particular field, or generically.

```rust
pub trait Circuit<F: Field, const IN: usize, const OUT: usize> {
    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; IN],
    ) -> ([Var<V>; OUT], ());
}

struct MyCircuit;

impl<F: Field> Circuit<F> for MyCircuit {
  ...
}

```

In this simplified version of the trait you can see most of what matters.
A circuit takes some variables as inputs, and some value implementing ConstraintSystem,
you use cs to create new variables and gates connecting and constraining them.
At the end you output some variables which make up the public output.

### Proving and verifying

Once you have your circuit, you can create a key and start making proofs.

```rust
fn main() {
    use field_and_pcs::{Fr, FrScheme};

    let circuit_key: CircuitKey<Fr, MyCircuit, FrScheme, 0> = CircuitKey::new();

    let inputs = [];

    let (instance, proof, _output) = circuit_key.prove_from_inputs(inputs);

    let instance: LcsInstance<Fr, FrScheme, 0> = instance;
    let proof: Proof<Fr, FrScheme> = proof;

    assert!(circuit_key.verify(instance, proof));
    println!("verification successful");
}
```

#### Example 1 implementation

To prove that $x$ is a square, we need to prove that there exists
some $w$ such that $w^2 = x$, and we can't reveal any of them.

Our circuit will look like this simplified a bit:

```rust
fn circuit<V, C>(
    cs: &mut C,
    []: [Var<V>; 0],
) {
    let x = cs.free_variable(|_, _| my_number());
    let w = cs.free_variable(|_, _| my_number::<F>().sqrt().expect("not square"));

    let w_square = cs.square(w);

    cs.assert_equals(x, w_square);
}
```

We have 2 free variables, one has it's value set to x and the other to w.
Then we a square gate to compute $w^2$.
And at the end an equality gate enforcing that $w^2 = x$.

#### Example 2 implementation

This is a case were we are less interested in zero-knowledge (as anyone can
compute fib(x) for any x), and more interested in succinctness.
Succinctness allows use to verify the proof of some statement in a smaller time
than it took to prove it.

Note: The example is not succinct in practice, see (TODO: add link) for
details on succinctness.

The circuit this time will have 2 public inputs which expect the values
of $fib(0)$ and $fib(1)$, and a public output for $fib(1000)$.

```rust
fn circuit<V: Val, C: ConstraintSystem<F, V>>(
    cs: &mut C,
    public_input: [Var<V>; 2],
) -> ([Var<V>; 1], [Var<V>; 0]) {
    let [_, res] = (0..N).fold(public_input, |last_two, _| {
        let [a, b] = last_two;
        let c = cs.add(a, b.clone());
        [b, c]
    });

    ([res], [])
}
```

This one is closer to the exact code, as you will see in [example2.rs](./lileum/examples/example2.rs).

#### Example 3 implementation

We now make use of circuit types, the only one currently available: Uint.
Circuit types enable simple implementations of functionality that would
require many variables and gates.
`Uint::new` for example creates about 32 variables and 96 constraints.
`Uint::new(cs,x)` creates a new variable with the same value of x, but
constrained to fit in an N bits number, the $[0..2^32]$ interval in this case.
As the value is the same it can be discarded like `_int`.
The original variable is now constrained to be a `u32` greater than 0.
But we want it to be greater than 30, for that we subtract 30 from
the original amount and check with another range check that it is $>30$.

```rust
fn circuit<V: Val, C: ConstraintSystem<F, V>>(
    cs: &mut C,
    public_input: [Var<V>; 1],
) -> ([Var<V>; 0], [Var<V>; 1]) {
    let [minimum] = public_input;

    let amount = cs.free_variable(|_, _| balance());
    let _int: Uint<V, 32> = Uint::new(cs, amount.clone());

    let amount_less_minimum = cs.sub(amount.clone(), minimum);
    let _int: Uint<V, 32> = Uint::new(cs, amount_less_minimum);

    ([], [amount])
}

```

What you see at the end is not a public output, as there are 0 of those here.
It is instead a private output, which looks similar, but it is only information
that the prover gets after making a proof, and which the verifier will never see.

## Features

### Custom gates

A gate is an implementation of the [Gate](./ccs/src/gates.rs) trait:

```rust
pub trait Gate<const IO: usize, const I: usize, const O: usize> {
    fn gate<V: Val>(i: [V; I]) -> [V; O];
    fn check<V: Val>(i: [V; I], o: [V; O]) -> Constraints<V>;
}
```

With a `gate` method mapping inputs to outputs, and a `check` method
creating constraints between inputs and outputs. A constraint
is just some equation which evaluates to 0 when satisfied.

Gates are currently defined irrespective of a particular field, they
can have arbitrary degree, number of inputs, outputs and 1 or more
constraints.

> Note: Folding currently requires all gates used in the circuit to
> have a single constraint.

The circuit builder API allows to use any number and type of gates,
and a `CircuitKey` can be created for any circuit as long as the proper
configuration is set.

A couple examples below, see [ccs/src/gates.rs](./ccs/src/gates.rs) for
more.

```rust
pub enum Equality {}

impl Gate<2, 2, 0> for Equality {
    fn gate<V: Val>(_i: [V; 2]) -> [V; 0] {
        []
    }

    fn check<V: Val>(i: [V; 2], _o: [V; 0]) -> Constraints<V> {
        let [a, b] = i;
        Constraints::from(a - b)
    }
}

pub enum Square {}

impl Gate<2, 1, 1> for Square {
    fn gate<V: Val>(i: [V; 1]) -> [V; 1] {
        let [x] = i;
        [x.clone() * x]
    }

    fn check<V: Val>(i: [V; 1], o: [V; 1]) -> Constraints<V> {
        let ([x], [expected]) = (i, o);
        let xx = x.clone() * x;
        Constraints::from(xx - expected)
    }
}
```

As you can see, `IO` is just `I + O`.
`Constraints` is a list of variable which must be enforced to be 0.
If you have single constraint like it is the case for most gates,
you can make use of the `From<V>` implementation like here.

### Circuit-level gates

Some proof systems, like those based on R1CS and some plonk implementations,
offer a single generic gate, which does some form of addition and multiplication.
Your entire circuit is made from many instances of that single gate.

Other proof systems add implementation-level custom gates, giving a selection
of gates to define your circuit. A custom gate can be specialized for a particular
application, outperforming the generic gate in different ways.
Many implementations of plonk fit here.

A limitation of implementation-level custom gates is that as a user of the library,
you can at most chose to use a given gate. To add a new gate requires changing the
implementation of the library. For the user of the library, gates are not that custom.
Going a step further, a proof system can expose an interface to create your own
gates and make use of them.

A minor problem of all types so far, is that they are examples of proof system level
gates. That means the gates, fixed or custom, are set in the proof system, and the
circuit then makes use of them.
It isn't the end of the world, but we can do better. Circuit-level custom gates
allow you to just use any gate you want in your circuit, the proof system then
just infers the gates to be used from your circuit without any extra configuration.
This is overall easier to use and facilitates other features like circuit composition,
as the gates used by the composition of 2 circuits are just the union of the gates
used by each of them.

There is also some variation in how custom a particular gate can be, there are 3
main points:

- Degree: While you can most of the time add as many times as you want, multiplication
increases the degree of the gate, some implementations may restrict you to a maximum
degree, then for example an square gate would be allowed, but a cube gate not.
Even if allowed, prover performance may suffer more in some implementations
than others as degree increases.
- Arity: How many inputs and outputs can a gate have, it may be fixed, or it may
be flexible. A common option is N -> 1 gates, where you can have as many inputs
as you want, but only 1 output.
- Number of constraints: A useful gate has 1 or more constraints, most have 1, while
some advanced gates have several constraints. A constraint is some equation you
want to hold between inputs and outputs.
For example $a + b = c$ would be the constraint for an addition gate.
For most N -> 1 gates a single constraint is enough, but for N -> M gates you are
likely to need several of them.

Lileum currently implements circuit-level custom gates of arbitrary degree and
arity. Gates may have any number of constraints, but if you want to use folding,
it currently accepts only circuit with single-constraint gates.
The performance with respect to degree is linear, meaning a degree 3 gate takes
twice the prover time of a degree 1 gate (we count from 0).

### Circuit composition

As the core of a circuit is just a function, you can call a circuit inside another
circuit.
For example the poseidon2 permutation circuit:

```rust
pub struct TestingHash;

impl<F: Field> Circuit<F, 3, 3, 3> for TestingHash {
    type PrivateInput = ();

    type PrivateOutput = [F; 3];

    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; 3],
    ) -> ([Var<V>; 3], [Var<V>; 3]) {
        ...
    }

    fn handle_output(out: [F; 3]) -> Self::PrivateOutput {
        out
    }
}
```

It can now just be called several times to create a hash chain circuit:

```rust
pub struct HashChain<const N: usize>;

impl<F: Field, const N: usize> Circuit<F, 1, 1, 1> for HashChain<N> {
    type PrivateInput = ();

    type PrivateOutput = F;

    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; 1],
    ) -> ([Var<V>; 1], [Var<V>; 1]) {
        let [x] = public_input;
        let mut state = [(); 3].map(|_| x.clone());

        for _ in 0..N {
            //HERE
            let (new_state, _) = TestingHash::circuit(cs, state);
            state = new_state;
        }

        let [out, _, _] = state;
        ([out.clone()], [out])
    }

    fn handle_output([out]: [F; 1]) -> Self::PrivateOutput {
        out
    }
}
```

### Folding

Folding allows you to merge 2 instances into a single one, such that
the new instance is valid only if the 2 original instances were valid
too.
The process can be repeated and fold N instance into 1, but even if
folding is successful every single time, nothing can be said about
any original instance until the folded instance is proved.

```rust
let key = CircuitKey::<Fr, Sponge, MyCircuit, Scheme>::new();

let (instance1, witness1, _) = key.commit_witness([input1]);
let (instance2, witness2, _) = key.commit_witness([input2]);

let instances = (instance1, instance2);
let witnesses = [witness1, witness2];

// Prover fold both instance-witness pairs, getting a new
// instance-witness pair, and a folding proof.
let (prover_instance, witness, fold_proof) = key.fold(instances, witnesses);

// Verifier does the same, but without witnesses, receives only an instance.
let verifier_instance = key.fold_instances(instances, fold_proof);
// The same instance as the prover.
assert_eq!(prover_instance, verifier_instance);
```

Why would I want folding? There are 3 main applications:

- You want a smaller circuit: And if your circuit can be split into smaller chunks,
you still need to fold every chunk, but you only have only have to prove a single
small chunk at the end.
For the same size of circuit, the performance of folding is much better than that
of full proving.
- Your computation is unbounded or variable: If it can be defined as an arbitrary
number of smaller steps, then you only need to prove as many steps as you need in
each particular instance. Without it, you would have to define a big circuit for
the worst case scenario.
- Smaller verification time: Verifying Lileum proofs is O(log n) + pcs.open.
Which means that if the commitment scheme you are using has O(n) verification
time, verification can take several seconds, and is definitively not succinct.
Folding on the other hand, has always O(1) verification time regardless of
the commitment scheme used.

## Benchmarks

The benchmarks are found in `lileum/benches` and come in two suites: execution-time
benchmarks (`exectime`) and peak-memory benchmarks (`memory`). Both are built with
Criterion, so the usual Criterion CLI options and HTML reports work.

To run all of the benchmarks just run

```
cargo bench
```

To run only the execution time benchmarks run

```
cargo bench Time
```

or

```
cargo bench --bench exectime
```

To run only the memory benchmarks run

```
cargo bench Memory
```

or

```
cargo bench --bench memory
```

The memory benchmarks report the peak heap allocated during the measured operation itself,
relative to a baseline taken after setup. The circuit key and SRS are excluded, and have
their own groups (Setup Memory, SRS Memory).

The HTML report is written to `target/criterion` and you can serve it locally with

```
python3 -m http.server 8000 --directory target/criterion
```

and then point your browser to `http://localhost:8000/report/index.html`

You can save a baseline for comparison with

```
cargo bench -- --save-baseline foo
```

and you can compare against it with

```
cargo bench -- --baseline foo
```

### Single-threaded

All the benchmarks are based on the [HashChain](https://github.com/LileumLabs/lileum/blob/master/lileum/src/testing/utils.rs#L87)
circuit.
A circuit which computes aposeidon2 chain of desired length.
The lengths are chosen so that the number of constraints is just
below the next power of 2, and the reports show the number of constraints,
not chain length. If you are interested in chain length, the values measured
correspond to `[11, 22, 44, 89, 178, 356, 712, 1424, 2849, 5698]` and result
in constraint counts from $2^{12}$ to $2^{21}$.
The benchmarks were run in an Azure Standard FX2mds VM.

#### Proving time

![Proving time benchmark](https://github.com/LileumLabs/lileum/blob/master/data/benchmarks/single_threaded/Proving%20Time/report/lines.svg)

#### Folding time

![Folding time benchmark](https://github.com/LileumLabs/lileum/blob/master/data/benchmarks/single_threaded/Folding%20Time/report/lines.svg)

#### Commit and fold

You rarely just have 2 instances around to fold, most commonly you have 1 running
instance and create a new instance to fold with it.
This benchmark measures the time of committing to an instance in addition to that
of folding, providing a more realistic point of comparison with proving.

![Commmit and fold benchmark](https://github.com/LileumLabs/lileum/blob/master/data/benchmarks/single_threaded/Commit%20and%20fold/report/lines.svg)

## Design considerations

This section will explain internal design considerations of the library, it
goes beyond what is needed to just use the library and can be safely ignored.

### History

This project started as a plain implementation of Hypernova, aiming to implement
an argument of knowledge for the relation and the folding scheme defined in the
paper.
Over time, I increased the scope towards more useful and powerful library, deviating
from Hypernova and CCS.
The main design goal while moving away from CCS, is for the arithmetization to be
the direct target of circuits, disregarding compatibility with R1CS, Plonk or AIR.

- Matrices are used like in CCS, but more restricted, being isomorphic to one-hot
encodings.
- There are explicit selectors as plain polynomials instead of extra matrices.
- Public inputs work a bit differently, for simplicity and optimization.
- I plan some more changes to better support constants and add lookups.

I never implemented Hypernova's folding, as NeutronNova came up and I liked that
approach more, which is the one currently implemented. I don't think NeutronNova's
folding can work with the sparse polynomials I will need for lookups. And to support
that I will likely end up using the 3 approaches (Nova, Hypernova, NeutronNova).

### Dependencies

I have very few external dependencies, ark-ff, and ark-ec if you use the
IPA based polynomial commitment scheme available by default.
As for internal dependencies, I have the next crates:

#### Ccs

Implements all regarding circuits:

- The `Circuit`.
- Constraint generation from circuits.
- Witness generation.
- Structure representing circuits
- Implementation of common gates.

As you may notice, I have things still to rename into lcs.

#### Commit

Defines traits representing folding schemes, utilities to commit and open
several polynomials and batching.
There is also an implementation of an IPA-based polynomial commitment used
as the default commitment scheme when needed.

#### Hash-to-curve

This is a dependency of the IPA commitment scheme, it started as separate crate
because I thought I would need more functionality to support folding.
But for now further development won't be needed until starting with public recursion.

#### Spark

A partial implementation of the spark sparse polynomial commitment scheme, which
allows committing to big polynomials with a lot of zeros, paying only the cost
of non-zero elements.
It implements a variant I call "static spark", where the commitment is assumed
to be well formed, and less checks are needed accordingly.
This works for committing to the matrices in circuit keys, but wouldn't work
for lookups for example.
Depending on how I implement lookups in the future, the implementation may be
expanded to full spark, allowing opening proofs to untrusted commitments.

#### Sponge

Implements a generic sponge/duplex, compatible with any permutation, a trait
defining permutations, and a generic implementation of the poseidon2 permutation.
The poseidon2 permutation should work with any field, but there are a few cases
not yet handled, still enough for most 256 bits or bigger prime fields.

#### Sumcheck

This is the most complex crate so far, it implements a generic and efficient
sumcheck prover and verifier and several utilities required for them.
There is also a sumfold implementation, and specialized zerocheck provers.

#### Transcript

Implements the Fiat-Shamir transcript, and defines the `Protocol` and
`Reduction`, which are an argument of knowledge and a reduction of
knowledge, respectively.
As I created it before knowing about reductions of knowledge, it doesn't
strictly match the formal definition. Their main goal is to aid a structured
and composable definition of protocols while guarding against many of the
common bugs that compromise soundness.
Somewhat predictably now, I didn't use much of `Protocol`, and even in the few
cases I did, not fully. In the future I will probably get rid of it and use
only `Reduction`, which I will also get closer to the formal definition.

## Q&A

Here some topics I couldn't fit in other sections.

> Support for small fields (<128 bits)?

As long as you had a suitable commitment scheme, everything will run as expected.
But it won't be secure enough. As the security of sumcheck depends on the size
of challenges.
Sumcheck would have to be updated to use a big enough extension of the field to
provide enough security.

> Stabilization?

The requirements for 1.0 are currently:

- Address all TODOs.
- Document public interfaces in all crates.
- Improve proving performance, which amounts mostly to redesigning spark.
- Do certain refactorings I have in mind.

> Parallelism?

Currently the entire codebase is single-threaded.
I want to think of a clean approach which generalizes to hardware acceleration
in the future.
But if desired, it isn't much work to add now, just ask for it.
About 99% of runtime is 3-4 algorithms which are trivial to make multi-threaded.

> Wasm or no-std support?

The codebase currently makes use of std just because it wasn't a concern so far.
But it isn't required anywhere and a simple refactoring should allow to make all
crates no-std.

## References

TODO: Add references to papers and such.


## Ownership and licensing

Lileum is developed and maintained by **Lileum Labs Ltd**.

Copyright © 2026 Lileum Labs Ltd.

The software and associated documentation in this repository are made
available under your choice of:

- the [Apache License, Version 2.0](LICENSE-APACHE); or
- the [MIT License](LICENSE-MIT).

You may use, reproduce, modify and distribute the software in accordance
with the terms of either license, at your option.

The full license terms are set out in
[`LICENSE-APACHE`](LICENSE-APACHE) and [`LICENSE-MIT`](LICENSE-MIT).

For customers requiring enterprise-grade terms and services,
Lileum Labs Ltd also offers commercial licenses, including professional
services, service-level commitments and warranties.
Please contact licensing@lileum-labs.com for licensing inquiries.
