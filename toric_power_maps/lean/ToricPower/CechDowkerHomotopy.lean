module

public import ToricPower.DowkerFacePosets
public import ToricPower.CechOrderClosureHomotopy

/-!
# The actual common-neighbor chain homotopy equivalence

Both common-neighbor maps are antitone. They therefore act directly on all
chain tuples of the face posets, which retain every ordering of each chain.
Each composite is a monotone enlargement. Its homotopy to the identity is
constructed using the genuinely contracted bounded-downset carriers.

This file compares the two face-order chain complexes. The separate comparison
with the original incidence cochain complexes is still required; this result
does not define those complexes to be equivalent.
Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

open CategoryTheory
open ToricPower.CechChainTuples ToricPower.CechOrderClosure

namespace ToricPower.Dowker

variable {Row Column : Type} [Fintype Row] [Fintype Column]

def doubleNeighbors (relation : Row → Column → Prop) (face : Face relation) : Face relation :=
  commonNeighbors (fun column row => relation row column) (commonNeighbors relation face)

theorem doubleNeighbors_monotone (relation : Row → Column → Prop) :
    Monotone (doubleNeighbors relation) := by
  intro first second subset
  exact commonNeighbors_antitone (fun column row => relation row column)
    (commonNeighbors_antitone relation subset)

theorem le_doubleNeighbors (relation : Row → Column → Prop) (face : Face relation) :
    face ≤ doubleNeighbors relation face :=
  le_double_commonNeighbors relation face

def commonNeighborTupleMap (relation : Row → Column → Prop) :
    orderTupleSet (Face relation) ⟶
      orderTupleSet (Face (fun column row => relation row column)) :=
  antitoneOrderTupleMap (commonNeighbors relation) (commonNeighbors_antitone relation)

theorem commonNeighborTupleMap_comp (relation : Row → Column → Prop) :
    commonNeighborTupleMap relation ≫
        commonNeighborTupleMap (fun column row => relation row column) =
      monotoneOrderTupleMap (doubleNeighbors relation) (doubleNeighbors_monotone relation) := by
  ext simplex tuple
  apply Subtype.ext
  rfl

def commonNeighborChainMap (relation : Row → Column → Prop) :
    orderTupleChains (Face relation) ⟶
      orderTupleChains (Face (fun column row => relation row column)) :=
  SSet.chainComplexMap (commonNeighborTupleMap relation) (AddCommGrpCat.of ℤ)

/-- Both comparison maps preserve the literal augmentation, including when
the relation has no nonempty faces. -/
theorem commonNeighborChainMap_augmentation (relation : Row → Column → Prop) :
    (commonNeighborChainMap relation).f 0 ≫
      orderTupleAugmentation (Face (fun column row => relation row column)) =
      orderTupleAugmentation (Face relation) :=
  orderTupleChainMap_augmentation (commonNeighbors relation)
    (fun _ _ h => h.elim
      (fun h => Or.inr (commonNeighbors_antitone relation h))
      (fun h => Or.inl (commonNeighbors_antitone relation h)))

theorem commonNeighborChainMap_comp (relation : Row → Column → Prop) :
    commonNeighborChainMap relation ≫
        commonNeighborChainMap (fun column row => relation row column) =
      SSet.chainComplexMap
        (monotoneOrderTupleMap (doubleNeighbors relation) (doubleNeighbors_monotone relation))
        (AddCommGrpCat.of ℤ) := by
  change ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _ ≫
    ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _ = _
  rw [← Functor.map_comp, commonNeighborTupleMap_comp]

def commonNeighborCompositeHomotopy (relation : Row → Column → Prop) :
    Homotopy
      (commonNeighborChainMap relation ≫
        commonNeighborChainMap (fun column row => relation row column))
      (𝟙 (orderTupleChains (Face relation))) := by
  rw [commonNeighborChainMap_comp]
  exact (inflationaryMapHomotopy (doubleNeighbors relation)
    (doubleNeighbors_monotone relation) (le_doubleNeighbors relation)).symm

/-- An explicit homotopy equivalence, including both all-degree homotopies.
Finiteness is used only to form all common-neighbor sets. -/
def commonNeighborChainHomotopyEquiv (relation : Row → Column → Prop) :
    HomotopyEquiv (orderTupleChains (Face relation))
      (orderTupleChains (Face (fun column row => relation row column))) where
  hom := commonNeighborChainMap relation
  inv := commonNeighborChainMap (fun column row => relation row column)
  homotopyHomInvId := commonNeighborCompositeHomotopy relation
  homotopyInvHomId := commonNeighborCompositeHomotopy (fun column row => relation row column)

end ToricPower.Dowker
