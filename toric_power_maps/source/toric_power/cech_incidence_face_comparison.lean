module

public import ToricPower.CechOrderClosureHomotopy
public import ToricPower.CechDowkerFaces

/-!
# Actual incidence chains and all tuples of chains of faces

An incidence tuple is carried by the bounded downset of its literal support
face. The inverse selects an actual member of each nonempty face. Both
composites are compared with the identity by explicit acyclic carriers:
a simplex on the support on the incidence side, and a bounded downset on
the face side. Every exactness assertion comes from an actual cone.

No ordered nerve, subdivision equivalence, nonempty-ray assumption, or
assumed comparison theorem occurs. Candidate source, pending compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open ToricPower.NegativeSupportCech ToricPower.NegativeSupportRelative
open ToricPower.CechIncidenceChains ToricPower.CechChainTuples
open ToricPower.CechOrderClosure
open scoped Classical Simplicial

namespace ToricPower.CechIncidenceFace

section GenericBoundedCarrier

variable {P : Type} [Preorder P] (simplicial : SSet)
variable (bound : ∀ degree, simplicial _⦋degree⦌ → P)
variable (bound_face : ∀ degree (deleted : Fin (degree + 2))
  (tuple : simplicial _⦋degree + 1⦌),
    bound degree (simplicial.δ deleted tuple) ≤ bound (degree + 1) tuple)

/-- The actual bounded-downset carrier works for any source simplicial set. -/
def boundedTargetCarrier : CechAcyclicCarrier.IntegralAcyclicCarrier
    simplicial (orderTupleChains P) (orderTupleAugmentation P) where
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

end GenericBoundedCarrier

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

abbrev Faces := Dowker.Face (negativeRayChartRelation incidence negative)

theorem face_present (face : Faces incidence negative) :
    face.val ∈ negativeChartComplex incidence negative := by
  obtain ⟨ray, contains⟩ := face.property.2
  exact ⟨face.property.1, ray.val, ray.property, contains⟩

/-- The actual support of the original tuple, regarded as its face. -/
def tupleFace {degree : ℕ} (tuple : forbiddenTuple incidence negative degree) :
    Faces incidence negative := by
  refine ⟨Finset.univ.image tuple.val, ?_, ?_⟩
  · exact ⟨tuple.val 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  · obtain ⟨ray, negativeRay, contains⟩ := tuple.property
    refine ⟨⟨ray, negativeRay⟩, ?_⟩
    intro chart present
    obtain ⟨column, _, rfl⟩ := Finset.mem_image.mp present
    exact contains column

theorem tuple_mem_face {degree : ℕ} (tuple : forbiddenTuple incidence negative degree)
    (column : Fin (degree + 1)) : tuple.val column ∈ (tupleFace incidence negative tuple).val :=
  Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩

theorem tupleFace_precomp_le {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : forbiddenTuple incidence negative next) :
    tupleFace incidence negative
      ⟨tuple.val ∘ selection, tupleForbidden_precomp incidence negative selection tuple.val tuple.property⟩ ≤
        tupleFace incidence negative tuple := by
  intro chart present
  obtain ⟨column, _, same⟩ := Finset.mem_image.mp present
  exact Finset.mem_image.mpr ⟨selection column, Finset.mem_univ _, same⟩

def incidenceFaceCarrier : CechAcyclicCarrier.IntegralAcyclicCarrier
    (incidenceSimplicialSet incidence negative)
    (orderTupleChains (Faces incidence negative)) (orderTupleAugmentation (Faces incidence negative)) :=
  boundedTargetCarrier (incidenceSimplicialSet incidence negative)
    (fun _ tuple => tupleFace incidence negative tuple)
    (fun _ deleted tuple => tupleFace_precomp_le incidence negative deleted.succAbove tuple)

/-- A vertex maps to its actual support face, inside its bounded downset. -/
def incidenceFaceVertexTuple (tuple : forbiddenTuple incidence negative 0) :
    (orderTupleSet (BoundedDownset (tupleFace incidence negative tuple))) _⦋0⦌ :=
  ⟨fun _column => ⟨tupleFace incidence negative tuple, le_rfl⟩,
    (orderTupleAllowed_iff _ 0 _).mpr (fun _ _ => Or.inl le_rfl)⟩

def incidenceFaceVertices : (incidenceFaceCarrier incidence negative).CarrierMapValues 0 :=
  fun tuple => (orderTupleSet (BoundedDownset (tupleFace incidence negative tuple))).ιChainComplex
    (incidenceFaceVertexTuple incidence negative tuple)

theorem incidenceFaceVertices_augmentation (tuple : forbiddenTuple incidence negative 0) :
    incidenceFaceVertices incidence negative tuple ≫
      ((incidenceFaceCarrier incidence negative).inclusion 0 tuple).f 0 ≫
        orderTupleAugmentation (Faces incidence negative) =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  change incidenceFaceVertices incidence negative tuple ≫
    (downsetChainInclusion (tupleFace incidence negative tuple)).f 0 ≫ _ = _
  rw [downsetChainInclusion_augmentation]
  exact incidenceChainAugmentation_generator _ _ _

def incidenceToFaceChains : incidenceChains incidence negative ⟶
    orderTupleChains (Faces incidence negative) :=
  (incidenceFaceCarrier incidence negative).extendCarriedVertexMap
    (incidenceFaceVertices incidence negative) (by
      intro tuple
      rw [incidenceFaceVertices_augmentation, incidenceFaceVertices_augmentation])

def incidenceToFaceChains_carried :
    (incidenceFaceCarrier incidence negative).CarriedIntegralChainMap
      (incidenceToFaceChains incidence negative) :=
  (incidenceFaceCarrier incidence negative).extendCarriedVertexMap_carried
    (incidenceFaceVertices incidence negative) (by
      intro tuple
      rw [incidenceFaceVertices_augmentation, incidenceFaceVertices_augmentation])

@[reassoc]
theorem incidenceToFaceChains_augmentation :
    (incidenceToFaceChains incidence negative).f 0 ≫
      orderTupleAugmentation (Faces incidence negative) = incidenceChainAugmentation incidence negative := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  change (incidenceSimplicialSet incidence negative).ιChainComplex tuple ≫
    (incidenceFaceCarrier incidence negative).carrierMapComponent 0
      (incidenceFaceVertices incidence negative) ≫ _ = _
  rw [← Category.assoc,
    CechAcyclicCarrier.IntegralAcyclicCarrier.carrierMapComponent_generator,
    Category.assoc, incidenceFaceVertices_augmentation]
  exact (incidenceChainAugmentation_generator _ _ tuple).symm

/-- A selected member of each actual nonempty face. -/
def faceVertex (face : Faces incidence negative) : Chart := face.property.1.choose

theorem faceVertex_mem (face : Faces incidence negative) :
    faceVertex incidence negative face ∈ face.val := face.property.1.choose_spec

/-- Selecting a vertex in every face of a chain gives an actual allowed
incidence tuple: every selected vertex lies in the greatest face. -/
def faceToIncidenceSet : orderTupleSet (Faces incidence negative) ⟶
    incidenceSimplicialSet incidence negative where
  app simplex := ↾fun tuple => ⟨faceVertex incidence negative ∘ tuple.val, by
    obtain ⟨ray, contains⟩ := (greatestValue tuple).property.2
    refine ⟨ray.val, ray.property, ?_⟩
    intro column
    exact contains _ ((tuple_le_greatest tuple column)
      (faceVertex_mem incidence negative (tuple.val column)))⟩
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    rfl

def faceToIncidenceChains : orderTupleChains (Faces incidence negative) ⟶
    incidenceChains incidence negative :=
  SSet.chainComplexMap (faceToIncidenceSet incidence negative) (AddCommGrpCat.of ℤ)

@[reassoc]
theorem faceToIncidenceChains_augmentation :
    (faceToIncidenceChains incidence negative).f 0 ≫
      incidenceChainAugmentation incidence negative = orderTupleAugmentation (Faces incidence negative) := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, faceToIncidenceChains, SSet.ι_chainComplexMap_f]
  exact (incidenceChainAugmentation_generator _ _ _).trans
    (incidenceChainAugmentation_generator _ _ _).symm

/-- The inverse tuple map restricted to a bounded downset lands in the
literal simplex on the bounding face. -/
def downsetToSimplexSet (face : Faces incidence negative) :
    orderTupleSet (BoundedDownset face) ⟶ simplexTupleSet face.val where
  app simplex := ↾fun tuple => ⟨fun column => faceVertex incidence negative (tuple.val column).val, by
    apply (simplexTupleAllowed_iff face.val simplex.unop.len _).mpr
    intro column
    exact (tuple.val column).property (faceVertex_mem incidence negative (tuple.val column).val)⟩
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    rfl

theorem downsetToSimplexSet_inclusion (face : Faces incidence negative) :
    downsetToSimplexSet incidence negative face ≫
      simplexTupleInclusion incidence negative face.val (face_present incidence negative face) =
    boundedDownsetInclusion face ≫ faceToIncidenceSet incidence negative := by
  ext simplex tuple
  apply Subtype.ext
  rfl

def downsetToSimplexChains (face : Faces incidence negative) :
    orderTupleChains (BoundedDownset face) ⟶ simplexTupleChains face.val :=
  SSet.chainComplexMap (downsetToSimplexSet incidence negative face) (AddCommGrpCat.of ℤ)

theorem downsetToSimplexChains_inclusion (face : Faces incidence negative) :
    downsetToSimplexChains incidence negative face ≫
      simplexTupleChainInclusion incidence negative face.val (face_present incidence negative face) =
    downsetChainInclusion face ≫ faceToIncidenceChains incidence negative := by
  change ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _ ≫
    ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _ =
      ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _ ≫
        ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, downsetToSimplexSet_inclusion]

section IncidenceComposite

def simplexChainRefinement {smaller larger : Finset Chart} (subset : smaller ⊆ larger) :
    simplexTupleChains smaller ⟶ simplexTupleChains larger :=
  SSet.chainComplexMap (simplexTupleRefinement subset) (AddCommGrpCat.of ℤ)

theorem simplexChainRefinement_inclusion {smaller larger : Finset Chart}
    (subset : smaller ⊆ larger)
    (smallerPresent : smaller ∈ negativeChartComplex incidence negative)
    (largerPresent : larger ∈ negativeChartComplex incidence negative) :
    simplexChainRefinement subset ≫
      simplexTupleChainInclusion incidence negative larger largerPresent =
        simplexTupleChainInclusion incidence negative smaller smallerPresent := by
  change ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _ ≫
    ((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map _ = _
  rw [← Functor.map_comp, simplexTupleRefinement_inclusion]
  rfl

/-- The literal simplex on the support of each original incidence tuple. -/
def incidenceSupportCarrier : CechAcyclicCarrier.IntegralAcyclicCarrier
    (incidenceSimplicialSet incidence negative) (incidenceChains incidence negative)
      (incidenceChainAugmentation incidence negative) where
  complex _ tuple := simplexTupleChains (tupleFace incidence negative tuple).val
  inclusion _ tuple := simplexTupleChainInclusion incidence negative
    (tupleFace incidence negative tuple).val (face_present incidence negative _)
  inclusion_mono _ tuple degree := simplexTupleChainInclusion_mono incidence negative
    (tupleFace incidence negative tuple).val (face_present incidence negative _) degree
  faceMap _ deleted tuple := simplexChainRefinement
    (tupleFace_precomp_le incidence negative deleted.succAbove tuple)
  faceMap_inclusion _ deleted tuple := simplexChainRefinement_inclusion incidence negative
    (tupleFace_precomp_le incidence negative deleted.succAbove tuple) _ _
  augmentation_zero _ tuple := by
    rw [simplexTupleChainInclusion_augmentation]
    exact incidenceChainAugmentation_zero _ _
  exact_zero _ tuple := by
    simpa only [simplexTupleChainInclusion_augmentation] using
      simplexTuple_augmentedExact (tupleFace incidence negative tuple).val
        (tupleFace incidence negative tuple).property.1
  exact_positive _ tuple degree := simplexTuple_exactAt_positive
    (tupleFace incidence negative tuple).val (tupleFace incidence negative tuple).property.1 degree

def incidenceTupleInSupport (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    (simplexTupleSet (tupleFace incidence negative tuple).val) _⦋degree⦌ :=
  ⟨tuple.val, (simplexTupleAllowed_iff _ degree tuple.val).mpr
    (tuple_mem_face incidence negative tuple)⟩

def incidenceIdentityCarried :
    (incidenceSupportCarrier incidence negative).CarriedIntegralChainMap
      (𝟙 (incidenceChains incidence negative)) where
  value degree tuple := (simplexTupleSet (tupleFace incidence negative tuple).val).ιChainComplex
    (incidenceTupleInSupport incidence negative degree tuple)
  value_inclusion degree tuple := by
    change (simplexTupleSet (tupleFace incidence negative tuple).val).ιChainComplex _ ≫
      (SSet.chainComplexMap (simplexTupleInclusion incidence negative
        (tupleFace incidence negative tuple).val (face_present incidence negative _))
        (AddCommGrpCat.of ℤ)).f degree = _
    rw [SSet.ι_chainComplexMap_f, HomologicalComplex.id_f, Category.comp_id]
    rfl

def incidenceCompositeCarried :
    (incidenceSupportCarrier incidence negative).CarriedIntegralChainMap
      (incidenceToFaceChains incidence negative ≫ faceToIncidenceChains incidence negative) where
  value degree tuple := (incidenceToFaceChains_carried incidence negative).value degree tuple ≫
    (downsetToSimplexChains incidence negative (tupleFace incidence negative tuple)).f degree
  value_inclusion degree tuple := by
    change ((incidenceToFaceChains_carried incidence negative).value degree tuple ≫
      (downsetToSimplexChains incidence negative (tupleFace incidence negative tuple)).f degree) ≫
        (simplexTupleChainInclusion incidence negative (tupleFace incidence negative tuple).val
          (face_present incidence negative _)).f degree = _
    have carried := (incidenceToFaceChains_carried incidence negative).value_inclusion degree tuple
    change (incidenceToFaceChains_carried incidence negative).value degree tuple ≫
      (downsetChainInclusion (tupleFace incidence negative tuple)).f degree = _ at carried
    rw [Category.assoc, ← HomologicalComplex.comp_f, downsetToSimplexChains_inclusion,
      HomologicalComplex.comp_f, ← Category.assoc, carried,
      Category.assoc, ← HomologicalComplex.comp_f]

def incidenceCompositeHomotopy :
    Homotopy (incidenceToFaceChains incidence negative ≫ faceToIncidenceChains incidence negative)
      (𝟙 (incidenceChains incidence negative)) :=
  (incidenceSupportCarrier incidence negative).carriedMapsHomotopy
    (incidenceCompositeCarried incidence negative) (incidenceIdentityCarried incidence negative) (by
      simp only [HomologicalComplex.comp_f, Category.assoc,
        faceToIncidenceChains_augmentation, incidenceToFaceChains_augmentation,
        HomologicalComplex.id_f, Category.id_comp])

end IncidenceComposite

section FaceComposite

/-- The actual vertices chosen from a chain of faces lie in its greatest
face. This gives the refinement of carriers for the second composite. -/
theorem faceToIncidenceSet_support_le (degree : ℕ)
    (tuple : (orderTupleSet (Faces incidence negative)) _⦋degree⦌) :
    tupleFace incidence negative ((faceToIncidenceSet incidence negative).app _ tuple) ≤
      greatestValue tuple := by
  intro chart present
  obtain ⟨column, _, rfl⟩ := Finset.mem_image.mp present
  exact (tuple_le_greatest tuple column) (faceVertex_mem incidence negative (tuple.val column))

def faceSupportCarrier : CechAcyclicCarrier.IntegralAcyclicCarrier
    (orderTupleSet (Faces incidence negative)) (orderTupleChains (Faces incidence negative))
      (orderTupleAugmentation (Faces incidence negative)) :=
  boundedOrderCarrier (fun _ tuple => greatestValue tuple)
    (fun degree deleted tuple => greatest_face_le degree deleted tuple)

def faceTupleInSupport (degree : ℕ)
    (tuple : (orderTupleSet (Faces incidence negative)) _⦋degree⦌) :
    (orderTupleSet (BoundedDownset (greatestValue tuple))) _⦋degree⦌ :=
  ⟨fun column => ⟨tuple.val column, tuple_le_greatest tuple column⟩,
    (orderTupleAllowed_iff _ degree _).mpr (fun first second =>
      (orderTupleAllowed_iff _ degree tuple.val).mp tuple.property first second)⟩

def faceIdentityCarried :
    (faceSupportCarrier incidence negative).CarriedIntegralChainMap
      (𝟙 (orderTupleChains (Faces incidence negative))) where
  value degree tuple := (orderTupleSet (BoundedDownset (greatestValue tuple))).ιChainComplex
    (faceTupleInSupport incidence negative degree tuple)
  value_inclusion degree tuple := by
    change (orderTupleSet (BoundedDownset (greatestValue tuple))).ιChainComplex _ ≫
      (SSet.chainComplexMap (boundedDownsetInclusion (greatestValue tuple))
        (AddCommGrpCat.of ℤ)).f degree = _
    rw [SSet.ι_chainComplexMap_f, HomologicalComplex.id_f, Category.comp_id]
    rfl

def faceCompositeCarried :
    (faceSupportCarrier incidence negative).CarriedIntegralChainMap
      (faceToIncidenceChains incidence negative ≫ incidenceToFaceChains incidence negative) where
  value degree tuple := (incidenceToFaceChains_carried incidence negative).value degree
      ((faceToIncidenceSet incidence negative).app _ tuple) ≫
    (downsetChainRefinement (faceToIncidenceSet_support_le incidence negative degree tuple)).f degree
  value_inclusion degree tuple := by
    change ((incidenceToFaceChains_carried incidence negative).value degree
      ((faceToIncidenceSet incidence negative).app _ tuple) ≫
        (downsetChainRefinement (faceToIncidenceSet_support_le incidence negative degree tuple)).f degree) ≫
          (downsetChainInclusion (greatestValue tuple)).f degree = _
    have carried := (incidenceToFaceChains_carried incidence negative).value_inclusion degree
      ((faceToIncidenceSet incidence negative).app _ tuple)
    change (incidenceToFaceChains_carried incidence negative).value degree
      ((faceToIncidenceSet incidence negative).app _ tuple) ≫
        (downsetChainInclusion (tupleFace incidence negative
          ((faceToIncidenceSet incidence negative).app _ tuple))).f degree = _ at carried
    rw [Category.assoc, ← HomologicalComplex.comp_f, downsetChainRefinement_inclusion,
      carried, HomologicalComplex.comp_f, ← Category.assoc, faceToIncidenceChains,
      SSet.ι_chainComplexMap_f]

def faceCompositeHomotopy :
    Homotopy (faceToIncidenceChains incidence negative ≫ incidenceToFaceChains incidence negative)
      (𝟙 (orderTupleChains (Faces incidence negative))) :=
  (faceSupportCarrier incidence negative).carriedMapsHomotopy
    (faceCompositeCarried incidence negative) (faceIdentityCarried incidence negative) (by
      simp only [HomologicalComplex.comp_f, Category.assoc,
        incidenceToFaceChains_augmentation, faceToIncidenceChains_augmentation,
        HomologicalComplex.id_f, Category.id_comp])

end FaceComposite

/-- The full actual integral chain homotopy equivalence between original
incidence tuples and all chain tuples of their genuine face poset. -/
def incidenceFaceChainsHomotopyEquiv :
    HomotopyEquiv (incidenceChains incidence negative)
      (orderTupleChains (Dowker.Face (negativeRayChartRelation incidence negative))) where
  hom := incidenceToFaceChains incidence negative
  inv := faceToIncidenceChains incidence negative
  homotopyHomInvId := incidenceCompositeHomotopy incidence negative
  homotopyInvHomId := faceCompositeHomotopy incidence negative

@[reassoc]
theorem incidenceFaceChainsHomotopyEquiv_hom_augmentation :
    (incidenceFaceChainsHomotopyEquiv incidence negative).hom.f 0 ≫
      orderTupleAugmentation (Dowker.Face (negativeRayChartRelation incidence negative)) =
        incidenceChainAugmentation incidence negative :=
  incidenceToFaceChains_augmentation incidence negative

@[reassoc]
theorem incidenceFaceChainsHomotopyEquiv_inv_augmentation :
    (incidenceFaceChainsHomotopyEquiv incidence negative).inv.f 0 ≫
      incidenceChainAugmentation incidence negative =
        orderTupleAugmentation (Dowker.Face (negativeRayChartRelation incidence negative)) :=
  faceToIncidenceChains_augmentation incidence negative

end ToricPower.CechIncidenceFace
