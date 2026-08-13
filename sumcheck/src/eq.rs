//! To eq(x,e) polynomial for n variables has this shape
//!          n-1
//! eq(x,e) = 𝜫 (xi * ei + (1 - xi)(1 - ei))
//!          i=0
//! it can be cheaply evaluated in a point, but evaluating it over
//! the 2^n points of the domain require n*log(n) multiplications if
//! done point by point and precomputing each 1-ei
//!
//! The original idea was to iterate a gray code so that each element
//! differs from the previous one in only one bit, then we can use that
//! previous element to compute the current one with only 1 multiplication
//! to swap the bit in question.
//! But a gray code has the issue of a rather unpredictable memory access if used
//! as an index, or having to sort the result at the end. And it doesn't seem
//! to even be necessary.
//!
//! The algorithem then looks like a gray code without the reversing part.
//! We start with eq(0,e), make 2 copies, keep one for 0 and modify the other
//! with a single multiplication to get 1.
//! Then having the 2 evaluations for 1 varible, we duplicate them, keep 1 copy
//! for 0x and modify the other copy into the 1x evaluations with 2 multiplications.
//! And so on we continue until having all the evaluations.

use crate::MultiPoint;
use ark_ff::Field;
use std::ops::Mul;

// computing a gray code as example, ultimately not used as
// there was a simpler and better way.
/*fn write_code(v: &mut [u32]) {
    assert!(v.len().is_power_of_two());
    if v.len() == 2 {
        v[0] = 0;
        v[1] = 1;
        return;
    }
    let half_len = v.len() / 2;
    let (left, right) = v.split_at_mut(half_len);
    write_code(left);
    let prefix = half_len as u32;
    for (l, r) in left.iter().zip(right.iter_mut().rev()) {
        //add proper shift
        *r = l | prefix;
    }
}

#[test]
fn gray() {
    let len = 1 << 3;
    let mut gray_code = vec![0; len];
    write_code(&mut gray_code);
    println!("code:");
    for e in gray_code {
        println!("{:#b}", e);
    }
}*/

fn eval_eq<F: Field>(dest: &mut [F], mut vars: Vec<F>, zero: F) {
    assert!(dest.len().is_power_of_two());
    if dest.len() == 2 {
        assert_eq!(vars.len(), 1);
        let var = vars.pop().unwrap();
        dest[0] = zero;
        dest[1] = zero * var;
    } else {
        assert_eq!(dest.len().ilog2() as usize, vars.len());
        let half_len = dest.len() / 2;
        let var = vars.pop().unwrap();
        let (left, right) = dest.split_at_mut(half_len);
        eval_eq(left, vars, zero);
        for (l, r) in left.iter().zip(right.iter_mut()) {
            // to avoid lsp false positive
            let r: &mut F = r;
            *r = var * l;
        }
    }
}

/// Computes eq(x,point) for each x in 0..(2^vars)
pub fn eq<F: Field>(point: &MultiPoint<F>) -> Vec<F> {
    let n_log = point.vars();
    eq_subset(point, n_log)
}

/// Computes eq(x,point) for each x in 0..(2^n_log)
pub fn eq_subset<F: Field>(point: &MultiPoint<F>, n_log: usize) -> Vec<F> {
    // these are the values corresponding to a 1 in the corresponding bit
    let vars = point.inner_ref();
    assert!(vars.len() >= n_log, "subset bigger than full set");
    assert!(n_log > 0, "subset must not be empty");
    let len = 1 << n_log;
    // These are the values corresponding to a 0 in the corresponding bit.
    let one_minus_v: Vec<F> = vars
        .iter()
        .map(|x| {
            // The fast evaluator inverts (1 - x_i) below, so x_i == 1 is unsupported:
            // The batch_inversion silently skips zeros and would silently yield a
            // wrong eq vector, so fail hard.
            assert!(
                *x != F::one(),
                "eq: opening coordinate == 1 is unsupported (1 - x must be invertible)"
            );
            F::one() - x
        })
        .collect();
    // the inverse of above, multiplying by it will undo multiplying by the value.
    let mut one_minus_v_inv = one_minus_v.clone();
    ark_ff::fields::batch_inversion(&mut one_minus_v_inv);
    // this have the effect of setting the value of an evaluation from 0 to 1
    // for any particular bit.
    // combines the effect of v and one_minus_v_inv
    let mut vars: Vec<F> = vars
        .iter()
        .zip(one_minus_v_inv)
        .map(|(a, b)| *a * b)
        .collect();
    vars.truncate(n_log);

    let zero: F = one_minus_v.iter().cloned().reduce(Mul::mul).unwrap();
    let mut eq = Vec::with_capacity(len);
    eq.resize(len, F::zero());
    eval_eq(&mut eq, vars, zero);
    eq
}

#[test]
fn test_eq() {
    use crate::evals::eval_simple_mle;
    use ark_vesta::Fr;
    use rand::{Rng, thread_rng};

    // let point = MultiPoint::r
    let mut rng = thread_rng();
    let mut r_point = || rng.r#gen::<Fr>();
    let vars = 4;
    let point = vec![r_point(); vars];
    let point = MultiPoint::new(point);

    let eq_evals = eq(&point);

    let check_poly = vec![r_point(); eq_evals.len()];

    let eq_eval = eq_evals
        .iter()
        .cloned()
        .zip(check_poly.iter())
        .fold(Fr::ZERO, |sum, (a, b)| sum + a * b);

    let check_eval = eval_simple_mle(&check_poly, &point);
    assert_eq!(eq_eval, check_eval);
}

#[test]
fn test_subset() {
    use ark_vesta::Fr;
    let vars: [Fr; 4] = [2_u32, 3, 4, 5].map(Fr::from);
    let point: MultiPoint<Fr> = MultiPoint::new(vars.to_vec());

    let full_eq = eq(&point);
    let subset_eq = eq_subset(&point, 2);

    for i in 0..4 {
        assert_eq!(full_eq[i], subset_eq[i]);
    }
}

// eq inverts (1 - x_i), so a coordinate == 1 must panic rather than silently compute invalid result
#[test]
#[should_panic]
fn eq_one_coordinate_unsupported() {
    use ark_vesta::Fr;
    let vars: [Fr; 4] = [2_u32, 3, 1, 5].map(Fr::from);
    let point: MultiPoint<Fr> = MultiPoint::new(vars.to_vec());
    let _ = eq(&point);
}
