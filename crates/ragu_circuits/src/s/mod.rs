//! Wiring polynomial `s(X,Y)` evaluation modules.
//!
//! # Design
//!
//! This module provides functionality to evaluate circuit polynomials by
//! interpreting circuit gadgets as polynomial operations. Unlike traditional
//! constraint system builders that track wire indices and witness values
//! separately, these implementations directly compute polynomial coefficients
//! by "running" the circuit with monomial evaluations.
//!
//! The wiring polynomial is defined as (see Ragu book for details):
//!
//! $$
//! s(X,Y)=\sum_{j=0}^{q-1} Y^j\cdot\left(\sum_{i=0}^{n-1} (
//!   \mathbf{u}_j^{(i)}\cdot X^{2n-1-i} +
//!   \mathbf{v}_j^{(i)}\cdot X^{2n+i} +
//!   \mathbf{w}_j^{(i)}\cdot X^{4n-1-i}
//! )\right)
//! $$
//!
//! Naively, one can construct linear constraint vectors $\mathbf{u},\mathbf{v},\mathbf{w}$
//! during circuit execution (i.e. `Circuit::witness`) and then evaluate
//! on the arithemtized wiring polynomial.
//! Ragu's Driver design allows clever re-interpretation of the circuit logic
//! to directly (partial) evaluate the arithmetized polynomial **without explicitly
//! constructing it**.
//!
//! See `sx` module doc as an example of such re-interpretation for evaluating $s(x,Y)$.

pub mod sx;
pub mod sxy;
pub mod sy;

use arithmetic::Coeff;
use ff::Field;
use ragu_core::drivers::LinearExpression;

/// A monomial evaluation in the polynomial basis.
///
/// During polynomial evaluation, this type represents specific powers of the
/// evaluation variable(s) at concrete points. Unlike traditional wire handles
/// that index into a constraint system, a `Monomial` directly contains the
/// computed value at a particular position in the polynomial basis.
///
/// # Variants
///
/// * `Value(F)`: monomial evaluations (e.g., `x^i`, `x^i * y^j`)
/// * `One`: a special monomial term that corresponds to the ONE wire
///
/// Note, `One` here has nothing to do with `x^0=1` (the constant monomial).
/// During circuit arithmetization, the `ONE` wire corresponds to a monomial term
/// in the overall wiring polynomial `s(X,Y)`. While the evaluation of this
/// monomial depends on evaluation point `x` (or `y`), the type system requires
/// `const Driver::ONE: Wire` a constant value. Thus we introduce this special
/// variant to represent the monomial evaluation for the `ONE` wire.
/// Categorically, `Monomial::One` is just another `Monomial::Value(_)`.
///
/// # Relationship to `Driver::Wire`
///
/// When a circuit is executed under a standard constraint system driver,
/// `Wire` represents an index. When executed under a polynomial evaluation
/// driver (like `Evaluator`), `Wire` is bound to this `Monomial` type,
/// allowing the same gadget code to compute polynomial coefficients instead
/// of building constraints.
#[derive(Clone)]
enum Monomial<F> {
    Value(F),
    One,
}

/// Accumulator for linear combinations of monomials (a part of arbitrary
/// polynomial evaluation expression).
struct MonomialSum<F: Field> {
    value: F,
    one: F,
    gain: Coeff<F>,
}

impl<F: Field> MonomialSum<F> {
    fn new(one: F) -> Self {
        Self {
            value: F::ZERO,
            one,
            gain: Coeff::One,
        }
    }
}

impl<F: Field> LinearExpression<Monomial<F>, F> for MonomialSum<F> {
    fn add_term(mut self, monomial: &Monomial<F>, coeff: Coeff<F>) -> Self {
        self.value += match monomial {
            Monomial::Value(v) => *v,
            Monomial::One => self.one,
        } * (coeff * self.gain).value();
        self
    }

    fn gain(mut self, coeff: Coeff<F>) -> Self {
        self.gain = self.gain * coeff;
        self
    }
}
