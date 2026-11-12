module

public import ToricPower.CechChainTuples

/-!
# Explicit carried homotopies on all chain tuples of a preorder

The carrier of a tuple is the actual order complex of a bounded downset.
It is a cone on its greatest element.  Thus both augmented exactness and
positive-degree exactness are consequences of the explicit contraction,
not hypotheses asserting a missing nerve theorem.

Every comparable-vertex map whose values lie in these downsets has an
explicit carried chain map, and two such maps have an actual chain homotopy.
Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open ToricPower.CechChainTuples ToricPower.CechIncidenceChains
open scoped Classical Simplicial

namespace ToricPower.CechOrderClosure

variable {P : Type} [Preorder P]

def downsetChainInclusion (apex : P) :
    orderTupleChains (BoundedDownset apex) ⟶ orderTupleChains P :=
  SSet.chainComplexMap (boundedDownsetInclusion apex) (AddCommGrpCat.of ℤ)

theorem downsetChainInclusion_mono (apex : P) (degree : ℕ) :
    Mono ((downsetChainInclusion apex).f degree) :=
  orderTupleChainMap_mono Subtype.val (fun _ _ h => h) Subtype.val_injective degree

def downsetChainRefinement {first second : P} (inclusion : first ≤ second) :
    orderTupleChains (BoundedDownset first) ⟶ orderTupleChains (BoundedDownset second) :=
  SSet.chainComplexMap (boundedDownsetRefinement inclusion) (AddCommGrpCat.of ℤ)

theorem downsetChainRefinement_inclusion {first second : P} (inclusion : first ≤ second) :
    downsetChainRefinement inclusion ≫ downsetChainInclusion second =
      downsetChainInclusion first := by
  apply HomologicalComplex.hom_ext
  intro degree
  apply SSet.chainComplex_hom_ext
  intro tuple
  change (orderTupleSet (BoundedDownset first)).ιChainComplex tuple ≫
      ((SSet.chainComplexMap (boundedDownsetRefinement inclusion)
        (AddCommGrpCat.of ℤ)).f degree ≫
       (SSet.chainComplexMap (boundedDownsetInclusion second)
        (AddCommGrpCat.of ℤ)).f degree) =
    (orderTupleSet (BoundedDownset first)).ιChainComplex tuple ≫
      (SSet.chainComplexMap (boundedDownsetInclusion first)
        (AddCommGrpCat.of ℤ)).f degree
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f,
    SSet.ι_chainComplexMap_f]
  rfl

@[reassoc]
theorem downsetChainInclusion_augmentation (apex : P) :
    (downsetChainInclusion apex).f 0 ≫ orderTupleAugmentation P =
      orderTupleAugmentation (BoundedDownset apex) :=
  orderTupleChainMap_augmentation Subtype.val (fun _ _ h => h)

variable (bound : ∀ degree, (orderTupleSet P) _⦋degree⦌ → P)
variable (bound_face : ∀ degree (deleted : Fin (degree + 2))
  (tuple : (orderTupleSet P) _⦋degree + 1⦌),
    bound degree ((orderTupleSet P).δ deleted tuple) ≤ bound (degree + 1) tuple)

def boundedOrderCarrier :
    CechAcyclicCarrier.IntegralAcyclicCarrier
      (orderTupleSet P) (orderTupleChains P) (orderTupleAugmentation P) where
  complex degree tuple := orderTupleChains (BoundedDownset (bound degree tuple))
  inclusion degree tuple := downsetChainInclusion (bound degree tuple)
  inclusion_mono degree tuple component := downsetChainInclusion_mono (bound degree tuple) component
  faceMap degree deleted tuple := downsetChainRefinement (bound_face degree deleted tuple)
  faceMap_inclusion degree deleted tuple :=
    downsetChainRefinement_inclusion (bound_face degree deleted tuple)
  augmentation_zero degree tuple := by
    rw [downsetChainInclusion_augmentation]
    exact incidenceChainAugmentation_zero _ _
  exact_zero degree tuple := by
    simpa only [downsetChainInclusion_augmentation] using
      boundedDownset_augmentedExact (bound degree tuple)
  exact_positive degree tuple component :=
    boundedDownset_exactAt_positive (bound degree tuple) component

variable (f : P → P)
variable (comparable : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ f q ∨ f q ≤ f p)
variable (bounded : ∀ degree (tuple : (orderTupleSet P) _⦋degree⦌) column,
  f (tuple.val column) ≤ bound degree tuple)

/-- A literal lift of each tuple to its bounded downset, retaining every
vertex and every repetition. -/
def boundedImageTuple (degree : ℕ) (tuple : (orderTupleSet P) _⦋degree⦌) :
    (orderTupleSet (BoundedDownset (bound degree tuple))) _⦋degree⦌ := by
  refine ⟨fun column => ⟨f (tuple.val column), bounded degree tuple column⟩, ?_⟩
  apply (orderTupleAllowed_iff _ degree _).mpr
  intro first second
  exact comparable _ _ ((orderTupleAllowed_iff P degree tuple.val).mp tuple.property first second)

def orderMapCarried : (boundedOrderCarrier bound bound_face).CarriedIntegralChainMap
    (SSet.chainComplexMap (orderTupleMap f comparable) (AddCommGrpCat.of ℤ)) where
  value degree tuple :=
    (orderTupleSet (BoundedDownset (bound degree tuple))).ιChainComplex
      (boundedImageTuple bound f comparable bounded degree tuple)
  value_inclusion degree tuple := by
    change (orderTupleSet (BoundedDownset (bound degree tuple))).ιChainComplex _ ≫
      (SSet.chainComplexMap (boundedDownsetInclusion (bound degree tuple))
        (AddCommGrpCat.of ℤ)).f degree = _
    rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
    rfl

/-- Two actual tuple maps contained in the same contracted carriers are
chain-homotopic, with the common augmentation proved by the tuple formulas. -/
def boundedOrderMapsHomotopy (g : P → P)
    (comparable_g : ∀ p q, p ≤ q ∨ q ≤ p → g p ≤ g q ∨ g q ≤ g p)
    (bounded_g : ∀ degree (tuple : (orderTupleSet P) _⦋degree⦌) column,
      g (tuple.val column) ≤ bound degree tuple) :
    Homotopy
      (SSet.chainComplexMap (orderTupleMap f comparable) (AddCommGrpCat.of ℤ))
      (SSet.chainComplexMap (orderTupleMap g comparable_g) (AddCommGrpCat.of ℤ)) :=
  (boundedOrderCarrier bound bound_face).carriedMapsHomotopy
    (orderMapCarried bound bound_face f comparable bounded)
    (orderMapCarried bound bound_face g comparable_g bounded_g)
    ((orderTupleChainMap_augmentation f comparable).trans
      (orderTupleChainMap_augmentation g comparable_g).symm)

/-- A monotone map which enlarges every element induces a chain map
homotopic to the identity.  The actual carrier bound is the image of a
greatest member of the tuple, so deleting a vertex gives a smaller carrier. -/
def inflationaryMapHomotopy (closure : P → P) (monotone : Monotone closure)
    (inflationary : ∀ p, p ≤ closure p) :
    Homotopy (𝟙 (orderTupleChains P))
      (SSet.chainComplexMap (monotoneOrderTupleMap closure monotone)
        (AddCommGrpCat.of ℤ)) := by
  let bounds : ∀ degree, (orderTupleSet P) _⦋degree⦌ → P :=
    fun _ tuple => closure (greatestValue tuple)
  have bounds_face : ∀ degree (deleted : Fin (degree + 2))
      (tuple : (orderTupleSet P) _⦋degree + 1⦌),
      bounds degree ((orderTupleSet P).δ deleted tuple) ≤ bounds (degree + 1) tuple := by
    intro degree deleted tuple
    exact monotone (greatest_face_le degree deleted tuple)
  let comparable_id : ∀ p q : P, p ≤ q ∨ q ≤ p → id p ≤ id q ∨ id q ≤ id p :=
    fun _ _ h => h
  let comparable_closure : ∀ p q, p ≤ q ∨ q ≤ p →
      closure p ≤ closure q ∨ closure q ≤ closure p :=
    fun _ _ h => h.elim (fun h => Or.inl (monotone h)) (fun h => Or.inr (monotone h))
  have bounds_id : ∀ degree (tuple : (orderTupleSet P) _⦋degree⦌) column,
      id (tuple.val column) ≤ bounds degree tuple := by
    intro degree tuple column
    exact (tuple_le_greatest tuple column).trans (inflationary (greatestValue tuple))
  have bounds_closure : ∀ degree (tuple : (orderTupleSet P) _⦋degree⦌) column,
      closure (tuple.val column) ≤ bounds degree tuple := by
    intro degree tuple column
    exact monotone (tuple_le_greatest tuple column)
  have identity_map : orderTupleMap id comparable_id = 𝟙 (orderTupleSet P) :=
    orderTupleMap_id comparable_id
  have closure_map : orderTupleMap closure comparable_closure =
      monotoneOrderTupleMap closure monotone := rfl
  have homotopy := boundedOrderMapsHomotopy bounds bounds_face id comparable_id bounds_id
    closure comparable_closure bounds_closure
  rw [identity_map, closure_map] at homotopy
  have map_identity : SSet.chainComplexMap (𝟙 (orderTupleSet P)) (AddCommGrpCat.of ℤ) =
      𝟙 (orderTupleChains P) := by
    apply HomologicalComplex.hom_ext
    intro degree
    apply SSet.chainComplex_hom_ext
    intro tuple
    rw [SSet.ι_chainComplexMap_f, HomologicalComplex.id_f, Category.comp_id]
    rfl
  rw [map_identity] at homotopy
  exact homotopy

end ToricPower.CechOrderClosure
