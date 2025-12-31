//! Streaming Horner's method evaluation via the Buffer trait.

use ragu_core::{Result, drivers::Driver};
use ragu_primitives::{Element, io::Buffer};

/// A buffer that evaluates a polynomial at a point using Horner's method.
///
/// Unlike [`Ky`](super::ky::Ky), this does not add a trailing constant term.
pub struct Horner<'a, 'dr, D: Driver<'dr>> {
    point: &'a Element<'dr, D>,
    result: Element<'dr, D>,
}

impl<'a, 'dr, D: Driver<'dr>> Clone for Horner<'a, 'dr, D> {
    fn clone(&self) -> Self {
        Horner {
            point: self.point,
            result: self.result.clone(),
        }
    }
}

impl<'a, 'dr, D: Driver<'dr>> Horner<'a, 'dr, D> {
    /// Creates a new buffer that evaluates a polynomial at `point`.
    pub fn new(dr: &mut D, point: &'a Element<'dr, D>) -> Self {
        Horner {
            point,
            result: Element::zero(dr),
        }
    }

    /// Finishes the evaluation, returning the accumulated result.
    pub fn finish(self) -> Element<'dr, D> {
        self.result
    }
}

impl<'a, 'dr, D: Driver<'dr>> Buffer<'dr, D> for Horner<'a, 'dr, D> {
    fn write(&mut self, dr: &mut D, value: &Element<'dr, D>) -> Result<()> {
        // Horner's step: result = result * point + value
        self.result = self.result.mul(dr, self.point)?.add(dr, value);
        Ok(())
    }
}
