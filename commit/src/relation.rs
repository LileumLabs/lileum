use crate::CommitmentSchemeCore;
use ark_ff::Field;
use reduction::{Message, Relation};
use std::{fmt::Debug, marker::PhantomData};
use sumcheck::{MultiPoint, evals::eval_simple_mle, oracles::UnexpectedVars};

/// For structure pcs.
/// For multilineal polynomial P, point x and eval y.
/// And for commitment C.
/// (pcs,(C,x,y),P) is in the relation if:
/// P(x) = y
/// And:
/// C = pcs(P)
#[derive(Clone, Copy, Debug)]
pub struct OpeningRelation<F, C>(PhantomData<(F, C)>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenInstance<F: Field, C: CommitmentSchemeCore<F>> {
    pub commit: C::Commitment,
    pub point: MultiPoint<F>,
    pub eval: F,
}

impl<F: Field, C: CommitmentSchemeCore<F>> Message<F> for OpenInstance<F, C> {
    type Params = usize;

    type Error = UnexpectedVars;

    fn len(params: &Self::Params) -> usize {
        C::Commitment::len(&()) + MultiPoint::<F>::len(params) + 1
    }

    fn to_field_elements(&self, params: &usize) -> Result<Vec<F>, Self::Error> {
        let Ok(mut elems) = self.commit.to_field_elements(&());
        elems.extend(self.point.to_field_elements(params)?);
        elems.push(self.eval);
        Ok(elems)
    }
}

impl<F: Field, C: CommitmentSchemeCore<F>> Relation for OpeningRelation<F, C> {
    type Structure = C;

    type Instance = OpenInstance<F, C>;

    // NOTE: It may be of interest to add a randomness in the future, having
    // (Vec<F>, F) instead.
    type Witness = Vec<F>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let OpenInstance {
            commit,
            point,
            eval,
        } = instance;
        assert_eq!(witness.len(), 1 << point.vars());

        let expected_eval = eval_simple_mle(witness, point);

        if expected_eval != *eval {
            return false;
        }

        let expected_commit = structure.commit_mle(witness);

        expected_commit == commit.clone()
    }
}
