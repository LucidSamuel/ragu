//! A field element that remembers when it is a special value.

use udon::field::Field;

/// A field element, typically a coefficient, that may be one of a few special
/// values. Keeping the case explicit lets arithmetic on coefficients skip
/// the multiplications that zero, one, two, and negation make trivial, and
/// lets drivers building group arithmetic over them do the same.
#[derive(Copy, Clone, Debug)]
pub enum Coeff<F: Field> {
    /// Zero.
    Zero,
    /// One.
    One,
    /// Two.
    Two,
    /// Negative one.
    NegativeOne,
    /// Any element.
    Arbitrary(F),
    /// The negation of any element.
    NegativeArbitrary(F),
}

impl<F: Field> Coeff<F> {
    /// Whether the coefficient is zero, including an [`Arbitrary`](Self::Arbitrary)
    /// that happens to hold zero.
    pub fn is_zero(&self) -> bool {
        match self {
            Coeff::Zero => true,
            Coeff::Arbitrary(value) | Coeff::NegativeArbitrary(value) => value.is_zero(),
            _ => false,
        }
    }

    /// The field element the coefficient stands for.
    pub fn value(&self) -> F {
        match self {
            Coeff::Zero => F::ZERO,
            Coeff::One => F::ONE,
            Coeff::Two => F::ONE.double(),
            Coeff::NegativeOne => -F::ONE,
            Coeff::Arbitrary(value) => *value,
            Coeff::NegativeArbitrary(value) => -*value,
        }
    }
}

impl<F: Field> From<F> for Coeff<F> {
    fn from(value: F) -> Self {
        Coeff::Arbitrary(value)
    }
}

impl<F: Field> core::ops::Mul for Coeff<F> {
    type Output = Coeff<F>;

    fn mul(self, other: Self) -> Self::Output {
        match (self, other) {
            (Coeff::Zero, _) | (_, Coeff::Zero) => Coeff::Zero,
            (Coeff::One, other) | (other, Coeff::One) => other,
            (Coeff::Two, other) | (other, Coeff::Two) => Coeff::Arbitrary(other.value().double()),
            (Coeff::NegativeOne, Coeff::NegativeOne) => Coeff::One,
            (Coeff::NegativeOne, Coeff::Arbitrary(value))
            | (Coeff::Arbitrary(value), Coeff::NegativeOne) => Coeff::NegativeArbitrary(value),
            (Coeff::NegativeOne, Coeff::NegativeArbitrary(value))
            | (Coeff::NegativeArbitrary(value), Coeff::NegativeOne) => Coeff::Arbitrary(value),
            (Coeff::Arbitrary(lhs), Coeff::Arbitrary(rhs))
            | (Coeff::NegativeArbitrary(lhs), Coeff::NegativeArbitrary(rhs)) => {
                Coeff::Arbitrary(lhs * rhs)
            }
            (Coeff::Arbitrary(lhs), Coeff::NegativeArbitrary(rhs))
            | (Coeff::NegativeArbitrary(rhs), Coeff::Arbitrary(lhs)) => {
                Coeff::NegativeArbitrary(lhs * rhs)
            }
        }
    }
}

impl<F: Field> core::ops::Add for Coeff<F> {
    type Output = Coeff<F>;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (Coeff::Zero, other) | (other, Coeff::Zero) => other,

            (Coeff::One, Coeff::One) => Coeff::Two,
            (Coeff::One, Coeff::NegativeOne) | (Coeff::NegativeOne, Coeff::One) => Coeff::Zero,
            (Coeff::NegativeOne, Coeff::NegativeOne) => Coeff::Arbitrary(-F::ONE.double()),

            (Coeff::Two, Coeff::NegativeOne) | (Coeff::NegativeOne, Coeff::Two) => Coeff::One,
            (Coeff::Two, other) | (other, Coeff::Two) => {
                Coeff::Arbitrary(other.value() + F::ONE.double())
            }

            (Coeff::One, Coeff::Arbitrary(value)) | (Coeff::Arbitrary(value), Coeff::One) => {
                Coeff::Arbitrary(value + F::ONE)
            }
            (Coeff::NegativeOne, Coeff::Arbitrary(value))
            | (Coeff::Arbitrary(value), Coeff::NegativeOne) => Coeff::Arbitrary(value - F::ONE),

            (Coeff::One, Coeff::NegativeArbitrary(value))
            | (Coeff::NegativeArbitrary(value), Coeff::One) => Coeff::Arbitrary(F::ONE - value),
            (Coeff::NegativeOne, Coeff::NegativeArbitrary(value))
            | (Coeff::NegativeArbitrary(value), Coeff::NegativeOne) => {
                Coeff::NegativeArbitrary(F::ONE + value)
            }

            (Coeff::Arbitrary(lhs), Coeff::Arbitrary(rhs)) => Coeff::Arbitrary(lhs + rhs),
            (Coeff::NegativeArbitrary(lhs), Coeff::NegativeArbitrary(rhs)) => {
                Coeff::NegativeArbitrary(lhs + rhs)
            }
            (Coeff::Arbitrary(lhs), Coeff::NegativeArbitrary(rhs))
            | (Coeff::NegativeArbitrary(rhs), Coeff::Arbitrary(lhs)) => Coeff::Arbitrary(lhs - rhs),
        }
    }
}

#[cfg(test)]
mod tests {
    use udon::field::Field;

    use super::Coeff;
    use crate::pasta::Fp;

    /// Coefficient arithmetic agrees with the field arithmetic of the values it
    /// stands for, commutes, and reports zero exactly when the value is zero.
    #[test]
    fn coeff_arithmetic_agrees_with_its_values() {
        let value = Fp::from(7u64);
        let cases = [
            Coeff::Zero,
            Coeff::One,
            Coeff::Two,
            Coeff::NegativeOne,
            Coeff::Arbitrary(value),
            Coeff::NegativeArbitrary(value),
            Coeff::Arbitrary(Fp::ZERO),
            Coeff::NegativeArbitrary(Fp::ONE),
            Coeff::from(Fp::from(2u64)),
        ];
        for lhs in cases {
            assert_eq!(lhs.is_zero(), lhs.value().is_zero());
            for rhs in cases {
                assert_eq!((lhs * rhs).value(), lhs.value() * rhs.value());
                assert_eq!((lhs * rhs).value(), (rhs * lhs).value());
                assert_eq!((lhs + rhs).value(), lhs.value() + rhs.value());
                assert_eq!((lhs + rhs).value(), (rhs + lhs).value());
            }
        }
    }
}
