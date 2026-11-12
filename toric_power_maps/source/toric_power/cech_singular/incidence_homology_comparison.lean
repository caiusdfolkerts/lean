module

public import ToricPower.CechSingular.ReducedCochainAcyclicity

@[expose] public noncomputable section

open ToricPower.CechIncidenceChains ToricPower.CechAcyclicCarrier
open ToricPower.NegativeSupportCech ToricPower.NegativeSupportRelative

/-! ## Exact generic source: IncidenceHomologyComparison -/
section Source_IncidenceHomologyComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open ToricPower.NegativeSupportCech
open ToricPower.NegativeSupportRelative
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveIncidenceHomologyComparison

section IncidenceChains

variable {Ray : Type*} {Chart : Type}

variable [Finite Chart]

noncomputable def affineSingularSimplicialMap (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    incidenceSimplicialSet incidence negative ⟶
      TopCat.toSSet.obj (TopCat.of (incidenceRealization incidence negative)) where
  app simplex := ↾tupleSingularSimplex incidence negative simplex.unop.len
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    exact (tupleSingularSimplex_precomp incidence negative selection.unop tuple).symm

noncomputable def affineSingularChainMap (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    incidenceChains incidence negative ⟶ integralSingularChains (incidenceRealization incidence negative) :=
  SSet.chainComplexMap (affineSingularSimplicialMap incidence negative) (AddCommGrpCat.of ℤ)

end IncidenceChains





section ConeRealizations

variable {Vertex : Type} [Finite Vertex] [DecidableEq Vertex]

noncomputable def coneRealizationContraction (complex : AbstractSimplicialComplex Vertex)
    (anchor : Vertex) (cone : PreAbstractSimplicialComplex.IsCone
      complex.toPreAbstractSimplicialComplex anchor) :
    (ContinuousMap.id (AbstractSimplicialComplex.Realization complex)).Homotopy
      (ContinuousMap.const _ (AbstractSimplicialComplex.vertex complex anchor)) :=
  realizationAffineHomotopy complex (ContinuousMap.id _)
    (ContinuousMap.const _ (AbstractSimplicialComplex.vertex complex anchor)) (by
      intro point
      have enlarged := cone.insert_mem (AbstractSimplicialComplex.support_mem complex point)
      change insert anchor point.val.support ∈ complex at enlarged
      simp only [ContinuousMap.id_apply, ContinuousMap.const_apply,
        AbstractSimplicialComplex.vertex_val, Finsupp.support_single _ one_ne_zero,
        Finset.union_singleton]
      convert enlarged using 1; ext vertex; simp)

theorem coneRealization_contractible (complex : AbstractSimplicialComplex Vertex)
    (anchor : Vertex) (cone : PreAbstractSimplicialComplex.IsCone
      complex.toPreAbstractSimplicialComplex anchor) :
    ContractibleSpace (AbstractSimplicialComplex.Realization complex) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨AbstractSimplicialComplex.vertex complex anchor,
      ⟨coneRealizationContraction complex anchor cone⟩⟩

end ConeRealizations

section ConeComparison

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop) (anchor : Chart)
variable (cone : PreAbstractSimplicialComplex.IsCone
  (negativeChartComplex incidence negative) anchor)

def incidenceConeActiveAnchor : ActiveIndex (incidencePatches incidence negative) :=
  ⟨anchor, by
    obtain ⟨ray, negativeRay, contains⟩ := cone.apex_mem.2
    exact ⟨ray, negativeRay, contains anchor (Finset.mem_singleton_self _)⟩⟩

omit [Finite Chart] in
theorem activeIncidenceNerve_isCone :
    PreAbstractSimplicialComplex.IsCone
      (activeNerve (incidencePatches incidence negative)).toPreAbstractSimplicialComplex
      (incidenceConeActiveAnchor incidence negative anchor cone) where
  apex_mem := by
    change Finset.image Subtype.val {incidenceConeActiveAnchor incidence negative anchor cone} ∈
      coverNerve (incidencePatches incidence negative)
    rw [incidencePatches_coverNerve]
    simpa only [Finset.image_singleton, incidenceConeActiveAnchor] using cone.apex_mem
  insert_mem := by
    intro face present
    change face.image Subtype.val ∈ coverNerve (incidencePatches incidence negative) at present
    change (insert (incidenceConeActiveAnchor incidence negative anchor cone) face).image Subtype.val ∈
      coverNerve (incidencePatches incidence negative)
    rw [incidencePatches_coverNerve] at present ⊢
    simpa only [Finset.image_insert, incidenceConeActiveAnchor] using cone.insert_mem present

include anchor cone in
theorem incidenceCone_realization_contractible :
    ContractibleSpace (incidenceRealization incidence negative) :=
  coneRealization_contractible (activeNerve (incidencePatches incidence negative))
    (incidenceConeActiveAnchor incidence negative anchor cone)
    (activeIncidenceNerve_isCone incidence negative anchor cone)

end ConeComparison

section FaceCarriers

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

def faceCarrierNegative (face : Finset Chart) (ray : Ray) : Prop :=
  negative ray ∧ ∀ chart ∈ face, incidence ray chart

theorem faceCarrier_face_iff (face support : Finset Chart) :
    support ∈ negativeChartComplex incidence (faceCarrierNegative incidence negative face) ↔
      support.Nonempty ∧ support ∪ face ∈ negativeChartComplex incidence negative := by
  constructor
  · rintro ⟨nonempty, ray, ⟨negativeRay, onFace⟩, onSupport⟩
    refine ⟨nonempty, nonempty.mono Finset.subset_union_left, ray, negativeRay, ?_⟩
    intro chart present
    rcases Finset.mem_union.mp present with onLeft | onRight
    · exact onSupport chart onLeft
    · exact onFace chart onRight
  · rintro ⟨nonempty, _unionNonempty, ray, negativeRay, onUnion⟩
    exact ⟨nonempty, ray, ⟨negativeRay,
      fun chart present => onUnion chart (Finset.mem_union_right _ present)⟩,
      fun chart present => onUnion chart (Finset.mem_union_left _ present)⟩

theorem faceCarrier_tuple_iff (face : Finset Chart) (degree : ℕ)
    (tuple : Fin (degree + 1) → Chart) :
    tupleForbidden incidence (faceCarrierNegative incidence negative face) degree tuple ↔
      Finset.univ.image tuple ∪ face ∈ negativeChartComplex incidence negative := by
  rw [tupleForbidden_iff_face, faceCarrier_face_iff]
  exact and_iff_right ⟨tuple 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

theorem faceCarrier_isCone (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (anchor : Chart)
    (onFace : anchor ∈ face) :
    PreAbstractSimplicialComplex.IsCone
      (negativeChartComplex incidence (faceCarrierNegative incidence negative face)) anchor where
  apex_mem := by
    obtain ⟨_nonempty, ray, negativeRay, contains⟩ := present
    exact ⟨Finset.singleton_nonempty _, ray, ⟨negativeRay, contains⟩,
      fun chart member => (Finset.mem_singleton.mp member) ▸ contains anchor onFace⟩
  insert_mem := by
    intro support supported
    obtain ⟨nonempty, ray, ⟨negativeRay, containsFace⟩, containsSupport⟩ := supported
    refine ⟨Finset.insert_nonempty _ _, ray, ⟨negativeRay, containsFace⟩, ?_⟩
    intro chart member
    rcases Finset.mem_insert.mp member with same | inSupport
    · exact containsFace chart (same ▸ onFace)
    · exact containsSupport chart inSupport

def faceCarrierSimplicialInclusion (face : Finset Chart) :
    incidenceSimplicialSet incidence (faceCarrierNegative incidence negative face) ⟶
      incidenceSimplicialSet incidence negative where
  app _simplex := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨ray, ⟨negativeRay, _onFace⟩, contains⟩ := tuple.property
    exact ⟨ray, negativeRay, contains⟩⟩
  naturality {source target} _selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    rfl

noncomputable def faceCarrierChainInclusion (face : Finset Chart) :
    incidenceChains incidence (faceCarrierNegative incidence negative face) ⟶
      incidenceChains incidence negative :=
  SSet.chainComplexMap (faceCarrierSimplicialInclusion incidence negative face) (AddCommGrpCat.of ℤ)

theorem faceCarrierChainInclusion_generator (face : Finset Chart) (degree : ℕ)
    (tuple : forbiddenTuple incidence (faceCarrierNegative incidence negative face) degree) :
    incidenceChainInclusion incidence (faceCarrierNegative incidence negative face) degree tuple ≫
      (faceCarrierChainInclusion incidence negative face).f degree =
    incidenceChainInclusion incidence negative degree
      ((faceCarrierSimplicialInclusion incidence negative face).app (Opposite.op ⦋degree⦌) tuple) := by
  exact SSet.ι_chainComplexMap_f _ _ (faceCarrierSimplicialInclusion incidence negative face)
    (AddCommGrpCat.of ℤ) tuple

def faceCarrierRefinement (smaller larger : Finset Chart) (subset : smaller ⊆ larger) :
    incidenceSimplicialSet incidence (faceCarrierNegative incidence negative larger) ⟶
      incidenceSimplicialSet incidence (faceCarrierNegative incidence negative smaller) where
  app _simplex := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨ray, ⟨negativeRay, onLarger⟩, contains⟩ := tuple.property
    exact ⟨ray, ⟨negativeRay, fun chart member => onLarger chart (subset member)⟩, contains⟩⟩
  naturality {source target} _selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    rfl

noncomputable def faceCarrierChainRefinement (smaller larger : Finset Chart) (subset : smaller ⊆ larger) :
    incidenceChains incidence (faceCarrierNegative incidence negative larger) ⟶
      incidenceChains incidence (faceCarrierNegative incidence negative smaller) :=
  SSet.chainComplexMap (faceCarrierRefinement incidence negative smaller larger subset) (AddCommGrpCat.of ℤ)

theorem faceCarrierChainRefinement_inclusion (smaller larger : Finset Chart) (subset : smaller ⊆ larger) :
    faceCarrierChainRefinement incidence negative smaller larger subset ≫
      faceCarrierChainInclusion incidence negative smaller =
    faceCarrierChainInclusion incidence negative larger := by
  exact (((SSet.chainComplexFunctor.{0, 0, 1} AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map_comp
    (faceCarrierRefinement incidence negative smaller larger subset)
    (faceCarrierSimplicialInclusion incidence negative smaller)).symm

end FaceCarriers

end BondalThomsen.ConvexNerveIncidenceHomologyComparison

end Source_IncidenceHomologyComparison
