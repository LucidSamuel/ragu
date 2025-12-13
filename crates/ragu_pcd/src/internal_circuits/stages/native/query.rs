//! Query stage for merge operations.

use arithmetic::Cycle;
use ragu_circuits::{polynomials::Rank, staging};
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::{Gadget, GadgetKind, Kind},
    maybe::Maybe,
};
use ragu_primitives::{
    Element, Point,
    vec::{CollectFixed, FixedVec, Len},
};

use core::marker::PhantomData;

pub use crate::internal_circuits::InternalCircuitIndex::QueryStage as STAGING_ID;

/// The number of query elements in the query stage.
pub struct Queries;

impl Len for Queries {
    fn len() -> usize {
        5
    }
}

/// Witness data for the query stage.
pub struct Witness<C: Cycle> {
    /// The x challenge derived from hashing mu and nested_ab_commitment.
    pub x: C::CircuitField,
    /// The nested s commitment (mesh polynomial at (x, y)).
    pub nested_s_commitment: C::NestedCurve,
    /// Query elements.
    pub queries: FixedVec<C::CircuitField, Queries>,
}

/// Output gadget for the query stage.
#[derive(Gadget)]
pub struct Output<'dr, D: Driver<'dr>, C: Cycle> {
    /// The witnessed x challenge element.
    #[ragu(gadget)]
    pub x: Element<'dr, D>,
    /// The nested s commitment (mesh polynomial at (x, y)).
    #[ragu(gadget)]
    pub nested_s_commitment: Point<'dr, D, C::NestedCurve>,
    /// Query elements.
    #[ragu(gadget)]
    pub queries: FixedVec<Element<'dr, D>, Queries>,
}

/// The query stage of the merge witness.
#[derive(Default)]
pub struct Stage<C: Cycle, R, const HEADER_SIZE: usize> {
    _marker: PhantomData<(C, R)>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> staging::Stage<C::CircuitField, R>
    for Stage<C, R, HEADER_SIZE>
{
    type Parent = super::preamble::Stage<C, R, HEADER_SIZE>;
    type Witness<'source> = &'source Witness<C>;
    type OutputKind = Kind![C::CircuitField; Output<'_, _, C>];

    fn values() -> usize {
        // x challenge + nested_s_commitment (2 coords) + queries
        1 + 2 + Queries::len()
    }

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness<'source>>,
    ) -> Result<<Self::OutputKind as GadgetKind<C::CircuitField>>::Rebind<'dr, D>>
    where
        Self: 'dr,
    {
        let x = Element::alloc(dr, witness.view().map(|w| w.x))?;
        let nested_s_commitment = Point::alloc(dr, witness.view().map(|w| w.nested_s_commitment))?;
        let queries = Queries::range()
            .map(|i| Element::alloc(dr, witness.view().map(|w| w.queries[i])))
            .try_collect_fixed()?;
        Ok(Output {
            x,
            nested_s_commitment,
            queries,
        })
    }
}
