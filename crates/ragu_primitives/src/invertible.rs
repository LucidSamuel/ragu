use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Error, Result,
    drivers::{Driver, DriverValue},
    gadgets::Gadget,
    maybe::Maybe,
};

use crate::{Element, consistent::Consistent};

/// An [`Element`] that has been constrained nonzero in the constraint system.
///
/// See [`Element::enforce_nonzero`].
///
/// [`Nonzero`] dereferences to the underlying [`Element`], so all of
/// [`Element`]'s methods are available directly on a [`Nonzero`].
#[derive(Gadget)]
pub struct Nonzero<'dr, D: Driver<'dr>> {
    element: Element<'dr, D>,
}

impl<'dr, D: Driver<'dr>> Nonzero<'dr, D> {
    /// Wraps `element` without checking the nonzero invariant.
    ///
    /// The caller is responsible for having emitted constraints that prove
    /// `element` is nonzero.
    pub(crate) fn new_unchecked(element: Element<'dr, D>) -> Self {
        Self { element }
    }

    /// Consumes `self` and returns the underlying [`Element`].
    pub fn into_inner(self) -> Element<'dr, D> {
        self.element
    }
}

impl<'dr, D: Driver<'dr>> core::ops::Deref for Nonzero<'dr, D> {
    type Target = Element<'dr, D>;

    fn deref(&self) -> &Element<'dr, D> {
        &self.element
    }
}

impl<'dr, D: Driver<'dr>> Consistent<'dr, D> for Nonzero<'dr, D> {
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        self.enforce_invertible(dr)?;
        Ok(())
    }
}

/// An invertible [`Element`].
///
/// This gadget represents a nonzero [`Element`] with a known multiplicative
/// inverse, accessible via [`element`](Self::element) and
/// [`inverse`](Self::inverse).
///
/// Inversion is free, since the inverse is located within the gadget.
#[derive(Gadget)]
pub struct Invertible<'dr, D: Driver<'dr>> {
    element: Nonzero<'dr, D>,
    inverse: Nonzero<'dr, D>,
}

impl<'dr, D: Driver<'dr>> Invertible<'dr, D> {
    /// Allocate an [`Invertible`] field element.
    ///
    /// This will be unsatisfied (and fail to synthesize) if `value` is zero.
    ///
    /// Computing the inverse witness costs a field inversion. If the inverse
    /// is already known, prefer
    /// [`alloc_with_advice`](Invertible::alloc_with_advice).
    ///
    /// This costs one gate and one constraint.
    pub fn alloc(dr: &mut D, value: DriverValue<D, D::F>) -> Result<Self> {
        let inverse_value = D::try_just(|| {
            value
                .snag()
                .invert()
                .into_option()
                .ok_or_else(|| Error::InvalidWitness("division by zero".into()))
        })?;
        Self::alloc_with_advice(dr, value, inverse_value)
    }

    /// Allocate an [`Invertible`] field element given its inverse as advice.
    ///
    /// This will be unsatisfied if `value` is zero or if `inverse_value` is not
    /// really its multiplicative inverse.
    ///
    /// This costs one gate and one constraint.
    pub fn alloc_with_advice(
        dr: &mut D,
        value: DriverValue<D, D::F>,
        inverse_value: DriverValue<D, D::F>,
    ) -> Result<Self> {
        let (a, b, c) = dr.mul(|| {
            Ok((
                Coeff::Arbitrary(*value.snag()),
                Coeff::Arbitrary(*inverse_value.snag()),
                Coeff::One,
            ))
        })?;
        dr.enforce_equal(&c, &D::ONE)?;

        Ok(Self {
            element: Nonzero::new_unchecked(Element::promote(a, value)),
            inverse: Nonzero::new_unchecked(Element::promote(b, inverse_value)),
        })
    }

    /// Returns the multiplicative inverse of `self`. This is free.
    pub fn invert(&self) -> Self {
        Self {
            element: self.inverse.clone(),
            inverse: self.element.clone(),
        }
    }

    /// Returns the underlying [`Nonzero`] element.
    pub fn element(&self) -> &Nonzero<'dr, D> {
        &self.element
    }

    /// Returns the inverse of the underlying element, also as a [`Nonzero`].
    pub fn inverse(&self) -> &Nonzero<'dr, D> {
        &self.inverse
    }

    /// Consumes `self` and returns the underlying [`Nonzero`] element.
    pub fn into_element(self) -> Nonzero<'dr, D> {
        self.element
    }

    /// Consumes `self` and returns the inverse as a [`Nonzero`].
    pub fn into_inverse(self) -> Nonzero<'dr, D> {
        self.inverse
    }
}

impl<'dr, D: Driver<'dr>> Consistent<'dr, D> for Invertible<'dr, D> {
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        let value = D::just(|| *self.element.value().take());
        let inverse_value = D::just(|| *self.inverse.value().take());
        Self::alloc_with_advice(dr, value, inverse_value)?.enforce_equal(dr, self)
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;

    use super::*;
    use crate::{Simulator, allocator::Standard};

    type F = ragu_pasta::Fp;
    type Sim = Simulator<F>;

    #[test]
    fn test_alloc_nonzero() -> Result<()> {
        let alloc = |a: F| {
            let sim = Sim::simulate(a, |dr, witness| {
                let inv = Invertible::alloc(dr, witness.clone())?;
                assert_eq!(*inv.element().value().take(), *witness.snag());
                assert_eq!(
                    *inv.element().value().take() * inv.inverse().value().take(),
                    F::ONE
                );
                Ok(())
            })?;
            assert_eq!(sim.num_gates(), 1);
            assert_eq!(sim.num_constraints(), 1);
            Ok(())
        };

        alloc(F::from(4578u64))?;
        alloc(F::from(1u64))?;
        Ok(())
    }

    #[test]
    fn test_alloc_zero_fails() {
        let result = Sim::simulate(F::ZERO, |dr, witness| {
            Invertible::alloc(dr, witness.clone())?;
            Ok(())
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_invert_swaps_for_free() -> Result<()> {
        Sim::simulate(F::from(7u64), |dr, witness| {
            let inv = Invertible::alloc(dr, witness.clone())?;
            let a_wire = *inv.element().wire();
            let b_wire = *inv.inverse().wire();

            dr.reset();
            let swapped = inv.invert();

            assert_eq!(*swapped.element().wire(), b_wire);
            assert_eq!(*swapped.inverse().wire(), a_wire);
            Ok(())
        })?;

        let sim = Sim::simulate(F::from(7u64), |dr, witness| {
            let inv = Invertible::alloc(dr, witness.clone())?;
            dr.reset();
            let _ = inv.invert();
            Ok(())
        })?;
        assert_eq!(sim.num_gates(), 0);
        assert_eq!(sim.num_constraints(), 0);

        Ok(())
    }

    #[test]
    fn test_enforce_consistent() -> Result<()> {
        let sim = Sim::simulate(F::from(5u64), |dr, witness| {
            let inv = Invertible::alloc(dr, witness.clone())?;
            dr.reset();
            inv.enforce_consistent(dr)?;
            Ok(())
        })?;
        assert_eq!(sim.num_gates(), 1);
        assert_eq!(sim.num_constraints(), 3);
        Ok(())
    }

    #[test]
    fn test_enforce_nonzero_succeeds() -> Result<()> {
        let sim = Sim::simulate(F::from(7u64), |dr, witness| {
            let allocator = &mut Standard::new();
            let element = Element::alloc(dr, allocator, witness.clone())?;
            dr.reset();
            let nonzero = element.enforce_nonzero(dr)?;
            assert_eq!(*nonzero.value().take(), *witness.snag());
            Ok(())
        })?;
        assert_eq!(sim.num_gates(), 1);
        assert_eq!(sim.num_constraints(), 2);
        Ok(())
    }

    #[test]
    fn test_enforce_nonzero_fails_for_zero() {
        let result = Sim::simulate(F::ZERO, |dr, witness| {
            let allocator = &mut Standard::new();
            let element = Element::alloc(dr, allocator, witness.clone())?;
            element.enforce_nonzero(dr)?;
            Ok(())
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_nonzero_enforce_consistent() -> Result<()> {
        let sim = Sim::simulate(F::from(5u64), |dr, witness| {
            let allocator = &mut Standard::new();
            let element = Element::alloc(dr, allocator, witness.clone())?;
            let nonzero = element.enforce_nonzero(dr)?;
            dr.reset();
            nonzero.enforce_consistent(dr)?;
            Ok(())
        })?;
        assert_eq!(sim.num_gates(), 1);
        assert_eq!(sim.num_constraints(), 2);
        Ok(())
    }
}
