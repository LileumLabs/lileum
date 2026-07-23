/// A relation between a structure, an instance and a witness.
pub trait Relation {
    type Structure;
    type Instance;
    type Witness;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool;
}

/// The unit relation.
impl Relation for () {
    type Structure = ();

    type Instance = ();

    type Witness = ();

    fn check(structure: &(), instance: &(), witness: &()) -> bool {
        #[allow(clippy::match_single_binding)]
        match (structure, instance, witness) {
            ((), (), ()) => true,
        }
    }
}

/// The compound relation (R1,R2) is essentially R1, but
/// with the structures of both R1 and R2.
pub struct CompoundRelation<R1, R2>(R1, R2);

impl<R1: Relation, R2: Relation> Relation for CompoundRelation<R1, R2> {
    type Structure = (R1::Structure, R2::Structure);

    type Instance = R1::Instance;

    type Witness = R1::Witness;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        R1::check(&structure.0, instance, witness)
    }
}

impl<R1: Relation, R2: Relation> Relation for (R1, R2) {
    type Structure = (R1::Structure, R2::Structure);

    type Instance = (R1::Instance, R2::Instance);

    type Witness = (R1::Witness, R2::Witness);

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let (structure1, structure2) = structure;
        let (instance1, instance2) = instance;
        let (witness1, witness2) = witness;
        R1::check(structure1, instance1, witness1) && R2::check(structure2, instance2, witness2)
    }
}

impl<R: Relation, const N: usize> Relation for [R; N] {
    type Structure = [R::Structure; N];

    type Instance = [R::Instance; N];

    type Witness = [R::Witness; N];

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        for ((structure, instance), witness) in structure.iter().zip(instance).zip(witness) {
            if !R::check(structure, instance, witness) {
                return false;
            }
        }
        true
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FoldingRelation<R: Relation>(R);

impl<R: Relation> Relation for FoldingRelation<R> {
    type Structure = R::Structure;

    type Instance = [R::Instance; 2];

    type Witness = [R::Witness; 2];

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let [instance1, instance2] = instance;
        let [witness1, witness2] = witness;

        R::check(structure, instance1, witness1) && R::check(structure, instance2, witness2)
    }
}
