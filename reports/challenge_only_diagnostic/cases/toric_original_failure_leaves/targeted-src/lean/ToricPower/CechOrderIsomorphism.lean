module

public import ToricPower.CechChainTuples
public import ToricPower.DowkerFacePosets

/-!
# Order isomorphisms on the actual tuple complexes

An order isomorphism gives an actual simplicial isomorphism on all chain
tuples, hence an integral chain isomorphism preserving the literal
augmentation. The final order isomorphism removes only a redundant `True`
subtype on relation witnesses; it leaves the finite faces unchanged.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

open CategoryTheory
open ToricPower.CechChainTuples

namespace ToricPower.CechOrderIsomorphism

variable {P Q : Type} [Preorder P] [Preorder Q]

def orderTupleIso (equivalence : P ≃o Q) : orderTupleSet P ≅ orderTupleSet Q where
  hom := monotoneOrderTupleMap equivalence equivalence.monotone
  inv := monotoneOrderTupleMap equivalence.symm equivalence.symm.monotone
  hom_inv_id := by
    ext simplex tuple
    apply Subtype.ext
    funext column
    change equivalence.symm (equivalence (tuple.val column)) = tuple.val column
    exact equivalence.symm_apply_apply _
  inv_hom_id := by
    ext simplex tuple
    apply Subtype.ext
    funext column
    change equivalence (equivalence.symm (tuple.val column)) = tuple.val column
    exact equivalence.apply_symm_apply _

def orderTupleChainsIso (equivalence : P ≃o Q) :
    orderTupleChains P ≅ orderTupleChains Q :=
  ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).mapIso
    (orderTupleIso equivalence)

theorem orderTupleChainsIso_hom_augmentation (equivalence : P ≃o Q) :
    (orderTupleChainsIso equivalence).hom.f 0 ≫ orderTupleAugmentation Q =
      orderTupleAugmentation P :=
  orderTupleChainMap_augmentation equivalence
    (fun _ _ h => h.elim
      (fun h => Or.inl (equivalence.monotone h))
      (fun h => Or.inr (equivalence.monotone h)))

theorem orderTupleChainsIso_inv_augmentation (equivalence : P ≃o Q) :
    (orderTupleChainsIso equivalence).inv.f 0 ≫ orderTupleAugmentation P =
      orderTupleAugmentation Q :=
  orderTupleChainMap_augmentation equivalence.symm
    (fun _ _ h => h.elim
      (fun h => Or.inl (equivalence.symm.monotone h))
      (fun h => Or.inr (equivalence.symm.monotone h)))

variable {Row Column : Type*}

/-- Removing a `True` subtype from witnesses changes no face or inclusion.
The inverse uses the actual original witness with its trivial proof. -/
def trueWitnessFaceOrderIso (relation : Row → Column → Prop) :
    Dowker.Face (fun row : {r : Row // True} => fun column => relation row.val column) ≃o
      Dowker.Face relation where
  toFun face := ⟨face.val, face.property.1, by
    obtain ⟨row, contains⟩ := face.property.2
    exact ⟨row.val, contains⟩⟩
  invFun face := ⟨face.val, face.property.1, by
    obtain ⟨row, contains⟩ := face.property.2
    exact ⟨⟨row, trivial⟩, contains⟩⟩
  left_inv face := Subtype.ext rfl
  right_inv face := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

end ToricPower.CechOrderIsomorphism
