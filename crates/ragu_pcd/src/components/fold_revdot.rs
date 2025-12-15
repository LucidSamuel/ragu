//! Operations and utilities for reasoning about folded revdot claims.

use ragu_core::{Result, drivers::Driver};
use ragu_primitives::{
    Element,
    vec::{ConstLen, FixedVec, Len},
};

/// Represents the number of "error" terms produced during a folding operation
/// of many `revdot` claims.
///
/// Given $m$ claims being folded, the error terms are defined as the
/// off-diagonal entries of an $m \times m$ matrix, which by definition has $m *
/// (m - 1)$ terms.
///
/// See the book entry on [folding revdot
/// claims](https://tachyon.z.cash/_ragu_INTERNAL_ONLY_H83J19XK1/design/structured.html#folding)
/// for more information.
pub struct ErrorTermsLen<const NUM_REVDOT_CLAIMS: usize>;

impl<const NUM_REVDOT_CLAIMS: usize> Len for ErrorTermsLen<NUM_REVDOT_CLAIMS> {
    fn len() -> usize {
        // NUM_REVDOT_CLAIMS * (NUM_REVDOT_CLAIMS - 1) =
        NUM_REVDOT_CLAIMS * NUM_REVDOT_CLAIMS - NUM_REVDOT_CLAIMS
    }
}

pub fn compute_c<'dr, D: Driver<'dr>, const NUM_REVDOT_CLAIMS: usize>(
    dr: &mut D,
    mu: &Element<'dr, D>,
    nu: &Element<'dr, D>,
    error_terms: &FixedVec<Element<'dr, D>, ErrorTermsLen<NUM_REVDOT_CLAIMS>>,
    ky_values: &FixedVec<Element<'dr, D>, ConstLen<NUM_REVDOT_CLAIMS>>,
) -> Result<Element<'dr, D>> {
    let munu = mu.mul(dr, nu)?;
    let mu_inv = mu.invert(dr)?;

    let mut error_terms = error_terms.iter();
    let mut ky_values = ky_values.iter();

    let mut result = Element::zero(dr);
    let mut row_power = Element::one();

    for i in 0..NUM_REVDOT_CLAIMS {
        let mut col_power = row_power.clone();
        for j in 0..NUM_REVDOT_CLAIMS {
            let term = if i == j {
                ky_values.next().expect("should exist")
            } else {
                error_terms.next().expect("should exist")
            };

            let contribution = col_power.mul(dr, term)?;
            result = result.add(dr, &contribution);
            col_power = col_power.mul(dr, &munu)?;
        }
        row_power = row_power.mul(dr, &mu_inv)?;
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use ragu_core::{drivers::emulator::Emulator, maybe::Maybe};
    use ragu_pasta::Fp;
    use ragu_primitives::{Simulator, vec::CollectFixed};
    use rand::rngs::OsRng;

    #[test]
    fn test_revdot_folding() -> Result<()> {
        const NUM_REVDOT_CLAIMS: usize = 3;

        let a: Vec<Fp> = (0..NUM_REVDOT_CLAIMS).map(|_| Fp::random(OsRng)).collect();
        let b: Vec<Fp> = (0..NUM_REVDOT_CLAIMS).map(|_| Fp::random(OsRng)).collect();

        let mut ky = vec![];
        let mut error = vec![];

        for (i, a) in a.iter().enumerate() {
            for (j, b) in b.iter().enumerate() {
                if i == j {
                    ky.push(a * b);
                } else {
                    error.push(a * b);
                }
            }
        }

        let mu = Fp::random(OsRng);
        let nu = Fp::random(OsRng);
        let mu_inv = mu.invert().unwrap();

        let expected_c = arithmetic::eval(a.iter(), mu_inv) * arithmetic::eval(b.iter(), mu * nu);

        // Run routine with Emulator.
        let dr = &mut Emulator::execute();

        let mu = Element::constant(dr, mu);
        let nu = Element::constant(dr, nu);

        let error_terms = error
            .iter()
            .map(|&v| Element::constant(dr, v))
            .collect_fixed()
            .unwrap();

        let ky_values = ky
            .iter()
            .map(|&v| Element::constant(dr, v))
            .collect_fixed()
            .unwrap();

        let result = compute_c::<_, NUM_REVDOT_CLAIMS>(dr, &mu, &nu, &error_terms, &ky_values)?;
        let computed_c = result.value().take();

        assert_eq!(
            *computed_c, expected_c,
            "C routine computed value doesn't match expected"
        );

        Ok(())
    }

    #[test]
    fn test_compute_c_constraints() -> Result<()> {
        fn measure<const M: usize>() -> Result<usize> {
            let sim = Simulator::simulate((), |dr, _| {
                let mu = Element::constant(dr, Fp::random(OsRng));
                let nu = Element::constant(dr, Fp::random(OsRng));
                let error_terms = (0..ErrorTermsLen::<M>::len())
                    .map(|_| Element::constant(dr, Fp::random(OsRng)))
                    .collect_fixed()?;
                let ky_values = (0..M)
                    .map(|_| Element::constant(dr, Fp::random(OsRng)))
                    .collect_fixed()?;

                compute_c::<_, M>(dr, &mu, &nu, &error_terms, &ky_values)?;
                Ok(())
            })?;

            Ok(sim.num_multiplications())
        }

        // Formula: 2*m^2 + m + 2
        assert_eq!(measure::<5>()?, 57);
        assert_eq!(measure::<15>()?, 467);
        assert_eq!(measure::<30>()?, 1832);
        assert_eq!(measure::<60>()?, 7262);

        Ok(())
    }

    #[test]
    fn test_multireduce() -> Result<()> {
        fn measure<const M: usize, const N: usize>() -> Result<usize> {
            let rng = OsRng;
            let sim = Simulator::simulate(rng, |dr, mut rng| {
                let mu = Element::alloc(dr, rng.view_mut().map(|r| Fp::random(r)))?;
                let nu = Element::alloc(dr, rng.view_mut().map(|r| Fp::random(r)))?;
                let error_terms = (0..ErrorTermsLen::<M>::len())
                    .map(|_| Element::alloc(dr, rng.view_mut().map(|r| Fp::random(r))))
                    .try_collect_fixed()?;
                let ky_values = (0..M)
                    .map(|_| Element::alloc(dr, rng.view_mut().map(|r| Fp::random(r))))
                    .try_collect_fixed()?;

                let mut collapsed = vec![];
                for _ in 0..N {
                    let v = compute_c::<_, M>(dr, &mu, &nu, &error_terms, &ky_values)?;
                    collapsed.push(v);
                }
                let collapsed = FixedVec::new(collapsed)?;
                let error_terms = (0..ErrorTermsLen::<N>::len())
                    .map(|_| Element::alloc(dr, rng.view_mut().map(|r| Fp::random(r))))
                    .try_collect_fixed()?;

                compute_c::<_, N>(dr, &mu, &nu, &error_terms, &collapsed)?;

                Ok(())
            })?;

            let num = sim.num_multiplications();

            // N * cost(M) + cost(N) where cost(x) = 2x² + x + 2
            let expected = |m: usize, n: usize| {
                let cost = |x: usize| 2 * x * x + x + 2;
                n * cost(m) + cost(n)
            };

            assert_eq!(num, expected(M, N));

            Ok(sim.num_multiplications())
        }

        assert_eq!(measure::<2, 2>()?, 36);
        assert_eq!(measure::<3, 7>()?, 268);
        assert_eq!(measure::<6, 11>()?, 1135);
        assert_eq!(measure::<5, 10>()?, 782);
        assert_eq!(measure::<10, 10>()?, 2332);

        Ok(())
    }
}
