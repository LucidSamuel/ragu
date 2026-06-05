use alloc::vec::Vec;

use ff::Field as _;
use pasta_curves::Fp;

use crate::{
    ctx::StepCtx,
    hooks::FrameworkHooks,
    polynomial::Polynomial,
    relations::{enforce_poly_product, enforce_poly_shifted_sum},
};

/// Distinct nonzero values, so any reordering or substitution is detectable.
fn values(n: u32) -> Vec<Fp> {
    (0..n)
        .map(|i| Fp::from(u64::from(i) + 1) * Fp::from(7u64))
        .collect()
}

#[test]
fn product_returns_the_union() {
    let a = Polynomial::from_roots(&[Fp::from(1u64), Fp::from(2u64)]);
    let b = Polynomial::from_roots(&[Fp::from(3u64)]);
    let union = a.multiply(&b);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    let product = enforce_poly_product(&mut ctx, &a, &b, union.commit(Fp::ZERO)).unwrap();
    assert_eq!(product, union);
}

#[test]
fn product_rejects_a_wrong_commitment() {
    let a = Polynomial::from_roots(&[Fp::from(1u64), Fp::from(2u64)]);
    let b = Polynomial::from_roots(&[Fp::from(3u64)]);
    let wrong = Polynomial::from_roots(&[Fp::from(4u64)]).commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_product(&mut ctx, &a, &b, wrong).is_err());
}

#[test]
fn shifted_sum_returns_the_concatenation() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    // cat = head ++ tail is the full coefficient list; the shift = len(head) = 2
    // is derived internally by the relation, never passed.
    let cat = Polynomial::from_coeffs(&v);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    let result = enforce_poly_shifted_sum(&mut ctx, &head, &tail, cat.commit(Fp::ZERO)).unwrap();
    assert_eq!(result, cat);
}

#[test]
fn shifted_sum_rejects_a_wrong_commitment() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    // Swap two coefficients so the witnessed commitment is not the concatenation.
    let mut bad = v.clone();
    bad.swap(0, 5);
    let wrong = Polynomial::from_coeffs(&bad).commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_shifted_sum(&mut ctx, &head, &tail, wrong).is_err());
}

#[test]
fn shifted_sum_shift_follows_len_of_first_operand() {
    // Different split points (len(head)) of the same vector both concatenate
    // back to it; mixing parts from different split points does not.
    let v = values(6);
    let cat = Polynomial::from_coeffs(&v);
    let cat_com = cat.commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);

    let a2 = Polynomial::from_coeffs(&v[..2]);
    let b2 = Polynomial::from_coeffs(&v[2..]);
    assert!(enforce_poly_shifted_sum(&mut ctx, &a2, &b2, cat_com).is_ok());

    let a4 = Polynomial::from_coeffs(&v[..4]);
    let b4 = Polynomial::from_coeffs(&v[4..]);
    assert!(enforce_poly_shifted_sum(&mut ctx, &a4, &b4, cat_com).is_ok());

    // Mixing parts from different split points breaks the relation.
    assert!(enforce_poly_shifted_sum(&mut ctx, &a2, &b4, cat_com).is_err());
}
