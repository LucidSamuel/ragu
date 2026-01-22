//! Shared types for wire evaluation during polynomial synthesis.
//!
//! # Design
//!
//! The [`sx`] and [`sxy`] evaluators compute polynomial coefficients directly
//! as field elements during circuit synthesis. Since both evaluators produce
//! immediate field element results, they can share the same wire representation
//! types defined here.
//!
//! In contrast, [`sy`] requires deferred computation through a virtual wire
//! system with reference counting, because $s(X, y)$ coefficients cannot be
//! computed in streaming order during synthesis (see [`sy`] module
//! documentation).
//!
//! ### Immediate Evaluation
//!
//! Both [`sx`] and [`sxy`] evaluate the wiring polynomial by interpreting
//! circuit synthesis operations directly. Wires become evaluated monomials
//! (field elements) rather than indices, and linear combinations become
//! immediate field arithmetic.
//!
//! ### `ONE` Wire Evaluation
//!
//! The `ONE` wire corresponds to the $c$ wire from gate 0, with monomial
//! $x^{4n-1}$. Since [`Driver::ONE`] must be a compile-time constant, it cannot
//! hold this computed value. Instead, [`WireEval::One`] serves as a sentinel
//! that [`WireEvalSum::add_term`] resolves to the cached $x^{4n - 1}$ value
//! at runtime.
//!
//! [`sx`]: super::sx
//! [`sxy`]: super::sxy
//! [`sy`]: super::sy
//! [`Driver::ONE`]: ragu_core::drivers::Driver::ONE

use arithmetic::Coeff;
use ff::Field;
use ragu_core::{
    Result,
    drivers::{Driver, LinearExpression},
};

/// Represents a wire's evaluated monomial during polynomial synthesis.
///
/// In the wiring polynomial $s(X, Y)$, each wire corresponds to a monomial
/// $x^j$ for some exponent $j$. When evaluating $s(x, y)$ at concrete points,
/// wires become field elements rather than indices.
///
/// # Variants
///
/// - `Value(F)` — Holds the evaluated monomial for a wire from [`Driver::mul`],
///   or a linear combination of such evaluations from [`Driver::add`].
///
/// - `One` — Represents the ONE wire. This variant exists because `Driver::ONE`
///   must be a compile-time constant, but the `ONE` wire's actual evaluation
///   (e.g., $x^{4n-1}$) depends on the evaluation point.
///   [`WireEvalSum::add_term`] resolves `One` to the cached evaluation at
///   runtime.
///
/// [`Driver::mul`]: ragu_core::drivers::Driver::mul
/// [`Driver::add`]: ragu_core::drivers::Driver::add
/// [`WireEvalSum::add_term`]: WireEvalSum::add_term
#[derive(Clone)]
pub(super) enum WireEval<F> {
    Value(F),
    One,
}

/// An accumulator for linear combinations of [`WireEval`]s during polynomial
/// evaluation.
///
/// Implements [`LinearExpression`] to support [`Driver::add`], which builds
/// linear combinations of wires. The accumulator tracks both the running sum
/// and the context needed to resolve [`WireEval::One`] variants.
///
/// [`Driver::add`]: ragu_core::drivers::Driver::add
pub(super) struct WireEvalSum<F: Field> {
    /// Running sum of accumulated wire evaluations.
    pub(super) value: F,

    /// Cached evaluation of the `ONE` wire, used to resolve [`WireEval::One`].
    one: F,

    /// Coefficient multiplier for subsequently added terms.
    gain: Coeff<F>,
}

impl<F: Field> WireEvalSum<F> {
    pub(super) fn new(one: F) -> Self {
        Self {
            value: F::ZERO,
            one,
            gain: Coeff::One,
        }
    }
}

impl<F: Field> LinearExpression<WireEval<F>, F> for WireEvalSum<F> {
    fn add_term(mut self, wire_eval: &WireEval<F>, coeff: Coeff<F>) -> Self {
        self.value += match wire_eval {
            WireEval::Value(v) => *v,
            WireEval::One => self.one,
        } * (coeff * self.gain).value();
        self
    }

    fn gain(mut self, coeff: Coeff<F>) -> Self {
        self.gain = self.gain * coeff;
        self
    }
}

/// Extension trait for [`Driver`] for wiring polynomial evaluators in
/// [`s` module][super].
///
/// # Public Input Enforcement
///
/// Public inputs are encoded in the wiring polynomial through a dual
/// interpretation of [`enforce_zero`]. While user code sees [`enforce_zero`] as
/// constraining wire values to equal zero, the protocol actually uses these
/// constraints to bind public input values.
///
/// ### The User API
///
/// Circuit implementations call [`enforce_zero`] to create linear constraints.
/// Within [`Circuit::witness`], these calls do exactly what they appear to do:
/// they constrain linear combinations of wire assignments to equal zero.
///
/// ### Public Input Binding
///
/// Calls to [`enforce_zero`] on public output wires (from [`Circuit::instance`])
/// and the `ONE` wire do NOT enforce that these wires equal zero. Instead, they
/// bind these wire values as coefficients in the public input polynomial $k(Y)$.
///
/// For example, calling `enforce_zero(|lc| lc.add(output_wire))` on a public
/// output with value $v$ creates a constraint that binds $v$ as a coefficient
/// in $k(Y)$, not a constraint that $v = 0$.
///
/// This dual interpretation allows the same [`enforce_zero`] API to serve both
/// purposes: internal zero constraints and public input binding.
///
/// [`Circuit::witness`]: crate::Circuit::witness
/// [`Circuit::instance`]: crate::Circuit::instance
/// [`enforce_zero`]: ragu_core::drivers::Driver::enforce_zero
pub(super) trait DriverExt<'dr>: Driver<'dr> {
    /// Enforces public output constraints by binding output wires to polynomial coefficients.
    ///
    /// Creates one constraint per output wire. These constraints do NOT enforce
    /// output == 0; instead, they bind output wires to k(Y) coefficients.
    fn enforce_public_outputs<'w>(
        &mut self,
        outputs: impl IntoIterator<Item = &'w Self::Wire>,
    ) -> Result<()>
    where
        Self::Wire: 'w,
    {
        outputs
            .into_iter()
            .try_for_each(|output| self.enforce_zero(|lc| lc.add(output)))
    }

    /// Enforces the ONE wire constraint.
    ///
    /// This does NOT enforce one == 0; instead, it binds the ONE wire to the
    /// first k(Y) coefficient.
    fn enforce_one(&mut self) -> Result<()> {
        self.enforce_zero(|lc| lc.add(&Self::ONE))
    }
}

impl<'dr, D: Driver<'dr>> DriverExt<'dr> for D {}
