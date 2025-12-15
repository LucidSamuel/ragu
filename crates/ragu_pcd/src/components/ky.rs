//! Streaming Horner's method evaluation of k(Y) via the Buffer trait.

use ff::Field;
use ragu_circuits::Circuit;
use ragu_core::{
    Result,
    drivers::{Driver, emulator::Emulator},
    maybe::{Always, Maybe},
};
use ragu_primitives::{Element, GadgetExt, io::Buffer};

/// Evaluate k(Y) at point `y` for a circuit instance.
pub fn eval<F: Field, C: Circuit<F>>(circuit: &C, instance: C::Instance<'_>, y: F) -> Result<F> {
    let mut dr = Emulator::extractor();
    let output = circuit.instance(&mut dr, Always::maybe_just(|| instance))?;
    let y_elem = Element::constant(&mut dr, y);
    let mut ky = Ky::new(&mut dr, y_elem);
    output.write(&mut dr, &mut ky)?;
    Ok(*ky.finish(&mut dr)?.value().take())
}

/// A buffer that evaluates k(Y) at a point `y` using Horner's method.
pub struct Ky<'dr, D: Driver<'dr>> {
    y: Element<'dr, D>,
    result: Element<'dr, D>,
}

impl<'dr, D: Driver<'dr>> Ky<'dr, D> {
    pub fn new(dr: &mut D, y: Element<'dr, D>) -> Self {
        Ky {
            y,
            result: Element::zero(dr),
        }
    }

    /// Finishes the evaluation by adding the trailing constant (one) term.
    /// Returns the final k(y) value.
    pub fn finish(self, dr: &mut D) -> Result<Element<'dr, D>> {
        // Final Horner step: result = result * y + 1
        Ok(self.result.mul(dr, &self.y)?.add(dr, &Element::one()))
    }
}

impl<'dr, D: Driver<'dr>> Buffer<'dr, D> for Ky<'dr, D> {
    fn write(&mut self, dr: &mut D, value: &Element<'dr, D>) -> Result<()> {
        // Horner's step: result = result * y + value.
        self.result = self.result.mul(dr, &self.y)?.add(dr, value);

        Ok(())
    }
}
