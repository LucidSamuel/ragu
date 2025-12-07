//! Reusable or isolated internal components.

use ragu_primitives::vec::Len;

pub mod fold_revdot;

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
