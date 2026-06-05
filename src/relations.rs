//! Mock equivalents of ragu's enforce-only polynomial relation free functions.

use ff::Field as _;
use pasta_curves::Fp;

use crate::{
    ctx::StepCtx,
    error::{Error, Result},
    polynomial::{Commitment, Polynomial},
};

pub fn enforce_poly_product(
    ctx: &mut StepCtx<'_>,
    multiplicand: &Polynomial,
    multiplier: &Polynomial,
    product_com_witness: Commitment,
) -> Result<Polynomial> {
    let product = multiplicand.multiply(multiplier);
    if product_com_witness != product.commit(Fp::ZERO) {
        return Err(Error("poly product: product commitment witness mismatch"));
    }

    let multiplicand_com = multiplicand.commit(Fp::ZERO);
    let multiplier_com = multiplier.commit(Fp::ZERO);
    let z = ctx.derive_challenge(&[multiplicand_com, multiplier_com, product_com_witness])?;

    ctx.enforce_poly_query(multiplicand_com, z, multiplicand.eval(z))?;
    ctx.enforce_poly_query(multiplier_com, z, multiplier.eval(z))?;
    ctx.enforce_poly_query(product_com_witness, z, product.eval(z))?;

    Ok(product)
}

pub fn enforce_poly_shifted_sum(
    ctx: &mut StepCtx<'_>,
    head: &Polynomial,
    tail: &Polynomial,
    result_com_witness: Commitment,
) -> Result<Polynomial> {
    // `head + X^len(head)·tail` is `head`'s coefficients followed by `tail`'s.
    let mut coeffs = head.coefficients().to_vec();
    coeffs.extend_from_slice(tail.coefficients());
    let result = Polynomial::from_coeffs(&coeffs);
    if result_com_witness != result.commit(Fp::ZERO) {
        return Err(Error(
            "poly shifted-sum: result commitment witness mismatch",
        ));
    }

    let head_com = head.commit(Fp::ZERO);
    let tail_com = tail.commit(Fp::ZERO);
    let z = ctx.derive_challenge(&[head_com, tail_com, result_com_witness])?;

    ctx.enforce_poly_query(head_com, z, head.eval(z))?;
    ctx.enforce_poly_query(tail_com, z, tail.eval(z))?;
    ctx.enforce_poly_query(result_com_witness, z, result.eval(z))?;

    Ok(result)
}
