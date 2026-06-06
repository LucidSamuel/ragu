use alloc::vec::Vec;

use ff::Field as _;
use pasta_curves::Fp;

use crate::{
    ctx::StepCtx,
    hooks::FrameworkHooks,
    polynomial::Polynomial,
    relations::{enforce_poly_concat, enforce_poly_product, enforce_poly_splice},
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
fn concat_accepts_the_concatenation() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    // result = head ++ tail is prover-supplied; the shift offset = 2 is a witness
    // the relation confirms against the three committed sequences.
    let result = Polynomial::from_coeffs(&v);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, result.commit(Fp::ZERO)).unwrap();
}

#[test]
fn concat_rejects_mismatched_result_commitment() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    let result = Polynomial::from_coeffs(&v);
    // A commitment to a different polynomial than the supplied result.
    let wrong_com = Polynomial::from_coeffs(&v[..4]).commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, wrong_com).is_err());
}

#[test]
fn concat_rejects_a_result_that_is_not_the_concatenation() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    // A self-consistent (poly, commitment) pair, but not head ++ tail.
    let mut bad = v.clone();
    bad.swap(0, 5);
    let result = Polynomial::from_coeffs(&bad);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(
        enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, result.commit(Fp::ZERO)).is_err()
    );
}

#[test]
fn concat_rejects_a_wrong_offset() {
    // The genuine concatenation with the genuine result commitment, but a wrong
    // shift: only offset = len(head) = 2 satisfies the point-wise identity.
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    let result = Polynomial::from_coeffs(&v);
    let result_com = result.commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, result_com).is_ok());
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 3, &result, result_com).is_err());
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 1, &result, result_com).is_err());
}

#[test]
fn splice_accepts_the_splice() {
    // combined = left ++ [mid] ++ right with left = v[..2], mid = v[2],
    // right = v[3..]; the spliced scalar lands at degree offset = len(left) = 2.
    let v = values(6);
    let left = Polynomial::from_coeffs(&v[..2]);
    let right = Polynomial::from_coeffs(&v[3..]);
    let mid = v[2];
    let combined = Polynomial::from_coeffs(&v);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    enforce_poly_splice(
        &mut ctx,
        &left,
        mid,
        &right,
        2,
        &combined,
        combined.commit(Fp::ZERO),
    )
    .unwrap();
}

#[test]
fn splice_rejects_mismatched_result_commitment() {
    let v = values(6);
    let left = Polynomial::from_coeffs(&v[..2]);
    let right = Polynomial::from_coeffs(&v[3..]);
    let mid = v[2];
    let combined = Polynomial::from_coeffs(&v);
    // A commitment to a different polynomial than the supplied combined.
    let wrong_com = Polynomial::from_coeffs(&v[..4]).commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_splice(&mut ctx, &left, mid, &right, 2, &combined, wrong_com).is_err());
}

#[test]
fn splice_rejects_a_result_that_is_not_the_splice() {
    let v = values(6);
    let left = Polynomial::from_coeffs(&v[..2]);
    let right = Polynomial::from_coeffs(&v[3..]);
    let mid = v[2];
    // A self-consistent (poly, commitment) pair, but not left ++ [mid] ++ right.
    let mut bad = v.clone();
    bad.swap(0, 5);
    let combined = Polynomial::from_coeffs(&bad);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(
        enforce_poly_splice(
            &mut ctx,
            &left,
            mid,
            &right,
            2,
            &combined,
            combined.commit(Fp::ZERO)
        )
        .is_err()
    );
}

#[test]
fn splice_rejects_a_wrong_offset() {
    // The genuine splice with the genuine result commitment and the genuine
    // mid, but a wrong offset: only offset = len(left) = 2 satisfies the
    // point-wise identity when mid is held fixed.
    let v = values(6);
    let left = Polynomial::from_coeffs(&v[..2]);
    let right = Polynomial::from_coeffs(&v[3..]);
    let mid = v[2];
    let combined = Polynomial::from_coeffs(&v);
    let combined_com = combined.commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_splice(&mut ctx, &left, mid, &right, 2, &combined, combined_com).is_ok());
    assert!(enforce_poly_splice(&mut ctx, &left, mid, &right, 3, &combined, combined_com).is_err());
    assert!(enforce_poly_splice(&mut ctx, &left, mid, &right, 1, &combined, combined_com).is_err());
}

#[test]
fn splice_with_a_free_mid_proves_an_arbitrary_result() {
    // CHARACTERIZATION (not a soundness guarantee): this demonstrates WHY the
    // splice's `mid` MUST be bound before the challenge. The identity is linear
    // in `mid`, so for a `combined` that is NOT the splice of `left`/`right`, a
    // prover who is free to choose `mid` after seeing the challenge can solve
    // for the unique `mid` that satisfies the point-wise check, and the relation
    // accepts. Callers avoid this by passing a `mid` that is already bound
    // upstream (e.g. a value committed before the challenge), not a fresh
    // witness.
    let v = values(6);
    let left = Polynomial::from_coeffs(&v[..2]);
    let right = Polynomial::from_coeffs(&v[3..]);
    let offset = 2usize;
    // An arbitrary `combined` unrelated to any splice of left/right.
    let combined = Polynomial::from_coeffs(&values(9)[3..]);
    let combined_com = combined.commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    // Reproduce the relation's challenge (derive_challenge is a pure hash of the
    // three commitments, in the same order the relation uses).
    let z = ctx
        .derive_challenge(&[left.commit(Fp::ZERO), right.commit(Fp::ZERO), combined_com])
        .unwrap();
    let zo = z.pow_vartime([offset as u64]);
    let zo_inv = Option::<Fp>::from(zo.invert()).expect("challenge is nonzero");
    // Solve mid = (combined(z) - left(z) - z^(offset+1)·right(z)) · z^{-offset}.
    let forged_mid = (combined.eval(z) - left.eval(z) - zo * z * right.eval(z)) * zo_inv;

    // The relation accepts the forged mid even though combined is not the splice.
    enforce_poly_splice(
        &mut ctx,
        &left,
        forged_mid,
        &right,
        offset,
        &combined,
        combined_com,
    )
    .unwrap();
}
