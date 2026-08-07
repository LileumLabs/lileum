//! Transcript tests
//!
//! Each test exercises a single invariant of the transcript abstraction with
//! no dependency on ccs/sumcheck/spark/commit. A failure here localizes the
//! regression to the transcript layer.

use ark_vesta::Fr;
use sponge::poseidon2::PoseidonDefault;
use sponge::sponge::Sponge;

use crate::{
    messages::SingleElement, params::ParamResolver, Error, TranscriptBuilder, TranscriptDescriptor,
};

type F = Fr;
type TestSponge = Sponge<F, PoseidonDefault<F>, 2, 1, 3>;
const VARS: usize = 2;

fn one_round_protocol() -> TranscriptDescriptor<F, TestSponge> {
    // Building transcript pattern (a contract the prover must follow)
    TranscriptBuilder::new(VARS, ParamResolver::new())
        // Round 1: prover sends one field element; verifier replies with one challenge
        .round::<F, SingleElement<F>, 1>()
        // Freeze the builder into an immutable TranscriptDescriptor
        .finish::<F, TestSponge>()
}

// Descriptor determinism: two independently-built descriptors with the same
// pattern must produce the same challenges given the same input
#[test]
fn descriptor_determinism() {
    let d1 = one_round_protocol();
    let d2 = one_round_protocol();
    let mut t1 = d1.instantiate();
    let mut t2 = d2.instantiate();
    let msg = SingleElement(F::from(1337u64));
    let c1: [F; 1] = t1.send_message(&msg).unwrap();
    let c2: [F; 1] = t2.send_message(&msg).unwrap();
    assert_eq!(
        c1, c2,
        "Challenges from identically-built descriptors must match"
    );
    t1.finish().unwrap();
    t2.finish().unwrap();
}

// Prover and verifier agreement: two transcripts created from the same descriptor
// and fed the same prover messages must produce identical challenges round-by-round
#[test]
fn prover_verifier_agreement() {
    let descriptor = one_round_protocol();
    let mut prover = descriptor.instantiate();
    let mut verifier = descriptor.instantiate();
    let msg = SingleElement(F::from(1729u64));
    let p_chal: [F; 1] = prover.send_message(&msg).unwrap();
    let v_chal: [F; 1] = verifier.send_message(&msg).unwrap();
    assert_eq!(
        p_chal, v_chal,
        "Prover and verifier must derive identical challenges"
    );
    prover.finish().unwrap();
    verifier.finish().unwrap();
}

// Divergence detection: different absorbed inputs must produce different challenges,
// proving the sponge actually consumes the message data
#[test]
fn divergence_detection() {
    let descriptor = one_round_protocol();
    let mut t_a = descriptor.instantiate();
    let mut t_b = descriptor.instantiate();
    let c_a: [F; 1] = t_a.send_message(&SingleElement(F::from(1u64))).unwrap();
    let c_b: [F; 1] = t_b.send_message(&SingleElement(F::from(2u64))).unwrap();
    assert_ne!(
        c_a, c_b,
        "Different absorbed inputs must yield different challenges"
    );
    t_a.finish().unwrap();
    t_b.finish().unwrap();
}

// Wrong message type rejected: sending a message whose TypeId does not match the
// expected round must return UnexpectedMessage
#[test]
fn wrong_message_type_rejected() {
    let descriptor = one_round_protocol();
    let mut transcript = descriptor.instantiate();
    // [SingleElement<F>; 1] has a different TypeId than expected SingleElement<F>
    let wrong = [SingleElement(F::from(101u64))];
    let result: Result<[F; 1], Error> = transcript.send_message(&wrong);
    assert!(matches!(result, Err(Error::UnexpectedMessage)));
    // Sponge is mid-pattern after the absorb; finish() clears it without panicking on drop
    let cleanup = transcript.finish();
    assert!(matches!(cleanup, Err(Error::SpongeError(_))));
}

// Wrong challenge count are rejected: asking for N challenges when the round
// expects M != N must return UnexpectedMessage
#[test]
fn wrong_challenge_count_rejected() {
    let descriptor = one_round_protocol();
    let mut transcript = descriptor.instantiate();

    // Ask send_message to return [F; 2] (two challenges) for this round (incompatible with protocol)
    let result: Result<[F; 2], Error> = transcript.send_message(&SingleElement(F::from(103u64)));

    // The transcript layer caught the arity mismatch before touching the sponge
    assert!(matches!(result, Err(Error::UnexpectedMessage)));

    // After the failed send_message, sponge absorbed 1 element but never squeezed.
    // Its state is running_pattern = [Absorb(1)], pattern = [Absorb(1), Squeeze(1)].
    // finish() detects the mismatch, returns Err, and — critically — sets
    // running_pattern = pattern so the Sponge::drop() impl doesn't panic.
    let cleanup = transcript.finish();

    // Confirm sponge noticed the unconsumed Squeeze(1) at cleanup time
    assert!(matches!(cleanup, Err(Error::SpongeError(_))));
}

// Late send rejected: after every round has been consumed, the next request must return
// TranscriptFinished rather than silently succeed.
#[test]
fn late_send_rejected() {
    // round + point lets us drive every round to completion and then probe exhaustion
    // via point() (checks the round iterator before touching sponge, so no extra panic risk)
    let descriptor = TranscriptBuilder::new(VARS, ParamResolver::new())
        // Round 1: prover sends one field element; verifier replies with one challenge
        .round::<F, SingleElement<F>, 1>()
        // Round 2: prover sends no message; verifier squeezes VARS challenge scalars and replies with point
        .point()
        .finish::<F, TestSponge>();
    let mut transcript = descriptor.instantiate();
    transcript
        .send_message::<SingleElement<F>, 1>(&SingleElement(F::from(109u64)))
        .unwrap();
    transcript.point().unwrap();
    let result = transcript.point(); // Extra step
    assert!(matches!(result, Err(Error::TranscriptFinished)));
    transcript.finish().unwrap();
}

// Premature finish rejected: calling `finish()` before any rounds have been consumed must fail.
#[test]
fn premature_finish_rejected() {
    let descriptor = one_round_protocol();
    let transcript = descriptor.instantiate();
    let result = transcript.finish();
    assert!(matches!(result, Err(Error::SpongeError(_))));
}

// Multi-round agreement: the sponge state must chain correctly across rounds so
// that the challenge at round N is influenced by every message absorbed in
// rounds 1..N. (Above single-round tests do not cover cross-round accumulation)
#[test]
fn multi_round_agreement() {
    let descriptor = TranscriptBuilder::new(VARS, ParamResolver::new())
        .round::<F, SingleElement<F>, 1>()
        .round::<F, [SingleElement<F>; 3], 1>()
        .round::<F, SingleElement<F>, 2>()
        .finish::<F, TestSponge>();
    let mut prover = descriptor.instantiate();
    let mut verifier = descriptor.instantiate();

    let m1 = SingleElement(F::from(10u64));
    let m2 = [
        SingleElement(F::from(20u64)),
        SingleElement(F::from(21u64)),
        SingleElement(F::from(22u64)),
    ];
    let m3 = SingleElement(F::from(30u64));

    let p1: [F; 1] = prover.send_message(&m1).unwrap();
    let v1: [F; 1] = verifier.send_message(&m1).unwrap();
    assert_eq!(p1, v1, "Challenges must match at round 1");

    let p2: [F; 1] = prover.send_message(&m2).unwrap();
    let v2: [F; 1] = verifier.send_message(&m2).unwrap();
    assert_eq!(p2, v2, "Challenges must match at round 2");

    let p3: [F; 2] = prover.send_message(&m3).unwrap();
    let v3: [F; 2] = verifier.send_message(&m3).unwrap();
    assert_eq!(p3, v3, "Challenges must match at round 3");

    prover.finish().unwrap();
    verifier.finish().unwrap();
}

// Point agreement: two transcripts with the same absorbed history must derive
// the same evaluation point from point()
#[test]
fn point_agreement() {
    let descriptor = TranscriptBuilder::new(VARS, ParamResolver::new())
        .round::<F, SingleElement<F>, 1>()
        .point()
        .finish::<F, TestSponge>();
    let mut prover = descriptor.instantiate();
    let mut verifier = descriptor.instantiate();
    let msg = SingleElement(F::from(1000003u64));
    let _: [F; 1] = prover.send_message(&msg).unwrap();
    let _: [F; 1] = verifier.send_message(&msg).unwrap();
    let p_point = prover.point().unwrap();
    let v_point = verifier.point().unwrap();
    assert_eq!(
        p_point, v_point,
        "Prover and verifier must derive the same evaluation point"
    );
    assert_eq!(p_point.len(), VARS, "Point must have VARS elements");
    prover.finish().unwrap();
    verifier.finish().unwrap();
}

// Message order sensitivity: absorbing the same messages in a different order must
// produce different challenges (confirming the transcript is order-sensitive)
#[test]
fn message_order_matters() {
    let descriptor = TranscriptBuilder::new(VARS, ParamResolver::new())
        .round::<F, SingleElement<F>, 1>()
        .round::<F, SingleElement<F>, 1>()
        .finish::<F, TestSponge>();
    let mut ab = descriptor.instantiate();
    let mut ba = descriptor.instantiate();
    let m1 = SingleElement(F::from(31u64));
    let m2 = SingleElement(F::from(32u64));
    let _: [F; 1] = ab.send_message(&m1).unwrap();
    let c_ab: [F; 1] = ab.send_message(&m2).unwrap();
    let _: [F; 1] = ba.send_message(&m2).unwrap();
    let c_ba: [F; 1] = ba.send_message(&m1).unwrap();
    assert_ne!(
        c_ab, c_ba,
        "Swapping message order must produce different challenges"
    );
    ab.finish().unwrap();
    ba.finish().unwrap();
}
