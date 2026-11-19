module

public import ToricPower.CechSingular.GlobalCarrierHomotopy

/-!
# Nerve comparison through an arbitrary compact carrier

Only the individual cover patches need be convex. The global carrier
used by the partition-of-unity argument may be any compact subspace
containing the actual barycentric witness image. This separates the
local convexity of intersections from the geometry of the whole union.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open Set
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveBarycentricHomotopy
open BondalThomsen.ConvexNerveOpenNeighborhoods
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveGlobalCarrierHomotopy
open ToricPower.NegativeSupportCech
open scoped Classical
attribute [local instance] Classical.decEq

namespace ToricPower.CompactCarrierNerve

variable {Index : Type} {E : Type*} [Finite Index]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual restriction of a closed cover patch to the compact carrier. -/
def carrierPatch (core : Set E) (patches : Index → Set E) (index : Index) : Set E :=
  core ∩ patches index

theorem carrierPatch_isCompact (core region : Set E) (patches : Index → Set E)
    (compact : IsCompact core) (inside : core ⊆ region)
    (closed : ∀ index, IsClosed {point : region | point.val ∈ patches index}) (index : Index) :
    IsCompact (carrierPatch core patches index) := by
  obtain ⟨closed_set,hclosed,restriction⟩ := isClosed_induced_iff.mp (closed index)
  have same : carrierPatch core patches index = core ∩ closed_set := by
    ext point
    constructor
    · rintro ⟨in_core,in_patch⟩
      have equal := Set.ext_iff.mp restriction (⟨point,inside in_core⟩ : region)
      exact ⟨in_core,equal.mpr in_patch⟩
    · rintro ⟨in_core,in_closed⟩
      have equal := Set.ext_iff.mp restriction (⟨point,inside in_core⟩ : region)
      exact ⟨in_core,equal.mp in_closed⟩
  rw [same]
  exact compact.inter_right hclosed

theorem carrierPatch_cover (core region : Set E) (patches : Index → Set E)
    (inside : core ⊆ region) (cover : (⋃ index,patches index) = region) :
    core ⊆ ⋃ index,carrierPatch core patches index := by
  intro point in_core
  obtain ⟨index,present⟩ := Set.mem_iUnion.mp (cover ▸ inside in_core)
  exact Set.mem_iUnion.mpr ⟨index,in_core,present⟩

/-- The same witness map, with its actual compact carrier as codomain. -/
def carrierSimultaneousPatch (core : Set E) (patches : Index → Set E)
    (witness : C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches),core))
    (radius : ℝ) (index : ActiveIndex patches) :
    Set (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
  {point | 0 < (subdivisionBarycenterMap patches point).val index ∧
    (witness point).val ∈ Metric.thickening radius (carrierPatch core patches index.val)}

theorem carrierSimultaneousPatch_isOpen (core : Set E) (patches : Index → Set E)
    (witness : C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches),core))
    (radius : ℝ) (index : ActiveIndex patches) :
    IsOpen (carrierSimultaneousPatch core patches witness radius index) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const
      ((continuous_into_realization_iff (activeNerve patches) _).mp
        (subdivisionBarycenterMap patches).continuous index)
  · exact Metric.isOpen_thickening.preimage
      (continuous_subtype_val.comp witness.continuous)

theorem carrierSimultaneousPatch_cover (core : Set E) (patches : Index → Set E)
    (witness : C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches),core))
    (witness_value : ∀ point, (witness point).val = witnessEvaluation patches point)
    (convex : ∀ index, Convex ℝ (patches index)) (radius : ℝ) (positive : 0 < radius) :
    (⋃ index,carrierSimultaneousPatch core patches witness radius index) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro point
  obtain ⟨least,present,minimal⟩ := barycentricFace_has_minimum patches point.val.support
    (AbstractSimplicialComplex.support_mem _ point)
  obtain ⟨index,contains⟩ := ((mem_coverNerve_iff patches least.val).mp least.property).1
  let active : ActiveIndex patches := ⟨index,intersectionWitness patches least,
    intersectionWitness_mem patches least index contains⟩
  refine Set.mem_iUnion.mpr ⟨active,
    subdivisionBarycenter_positive_of_face patches point least present active contains,
    Metric.self_subset_thickening positive _ ⟨(witness point).property,?_⟩⟩
  rw [witness_value]
  have in_carrier := witnessEvaluation_face_mem_carrier patches
    ⟨point.val.support,AbstractSimplicialComplex.support_mem _ point⟩ least minimal
    ⟨point.val,AbstractSimplicialComplex.mem_convexHull_carrier _ point⟩
  exact cofaceWitnessCarrier_subset_patch patches convex least index contains in_carrier

omit [Finite Index] in
theorem thickenedCarrierFace_mem_activeNerve (core : Set E) (patches : Index → Set E)
    (radius : ℝ)
    (preserves : ∀ face : Finset Index,
      (∃ point ∈ core,∀ index ∈ face,
        point ∈ Metric.thickening radius (carrierPatch core patches index)) ↔
      ∃ point ∈ core,∀ index ∈ face,point ∈ carrierPatch core patches index)
    (point : core) (face : Finset (ActiveIndex patches)) (nonempty : face.Nonempty)
    (contains : ∀ index ∈ face,
      point.val ∈ Metric.thickening radius (carrierPatch core patches index.val)) :
    face ∈ activeNerve patches := by
  change face.image Subtype.val ∈ coverNerve patches
  apply (mem_coverNerve_iff patches _).mpr
  refine ⟨nonempty.image _,?_⟩
  obtain ⟨witness,_,present⟩ := (preserves (face.image Subtype.val)).mp
    ⟨point.val,point.property,by
      intro index member
      obtain ⟨active,active_member,rfl⟩ := Finset.mem_image.mp member
      exact contains active active_member⟩
  exact ⟨witness,fun index member => (present index member).2⟩

/-- The full barycentric comparison uses only compactness of its
carrier, relative closedness, and convexity of the individual patches. -/
theorem exists_carrier_subdivision_comparison (core region : Set E) (patches : Index → Set E)
    (compact : IsCompact core) (inside : core ⊆ region)
    (convex : ∀ index,Convex ℝ (patches index))
    (closed : ∀ index,IsClosed {point : region | point.val ∈ patches index})
    (cover : (⋃ index,patches index) = region)
    (witness : C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches),core))
    (witness_value : ∀ point,(witness point).val = witnessEvaluation patches point) :
    ∃ mapping : C(core,AbstractSimplicialComplex.Realization (activeNerve patches)),
      Nonempty ((subdivisionBarycenterMap patches).Homotopy (mapping.comp witness)) := by
  classical
  letI : DecidableEq (ActiveIndex patches) := Classical.decEq _
  letI : CompactSpace core := isCompact_iff_compactSpace.mp compact
  letI : CompactSpace (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    finiteRealization_compactSpace _
  letI : T2Space (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    (realizationCoordinates_isClosedEmbedding _).isEmbedding.t2Space
  obtain ⟨radius,positive,preserves⟩ := exists_uniform_nerve_preserving_radius
    core (carrierPatch core patches) compact
    (fun index => (carrierPatch_isCompact core region patches compact inside closed index).isClosed)
  have core_cover := carrierPatch_cover core region patches inside cover
  obtain ⟨core_partition,core_subordinate⟩ := PartitionOfUnity.exists_isSubordinate
    (s := (Set.univ : Set core)) isClosed_univ
    (relativeOpenPatch core (carrierPatch core patches) radius)
    (relativeOpenPatch_isOpen _ _ _)
    (by rw [relativeOpenPatch_cover _ _ core_cover radius positive])
  have core_supported : ∀ point : core,
      (partitionCoordinates core_partition point).weights.support ∈ coverNerve patches := by
    intro point
    rw [partitionCoordinates_support]
    apply (mem_coverNerve_iff patches _).mpr
    refine ⟨partitionCoordinates_nonempty core_partition point,?_⟩
    obtain ⟨chosen,_,present⟩ := (preserves (core_partition.finsupport point)).mp
      ⟨point.val,point.property,by
        intro index member
        apply core_subordinate index
        apply subset_tsupport
        exact (core_partition.mem_finsupport point).mp member⟩
    exact ⟨chosen,fun index member => (present index member).2⟩
  let mapping : C(core,AbstractSimplicialComplex.Realization (activeNerve patches)) := {
    toFun point := coordinatesToNerve patches (partitionCoordinates core_partition point)
      (core_supported point)
    continuous_toFun := (continuous_into_realization_iff (activeNerve patches) _).mpr
      fun index => (core_partition index.val).continuous }
  obtain ⟨source_partition,source_subordinate⟩ := PartitionOfUnity.exists_isSubordinate
    (s := (Set.univ : Set (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches))))
    isClosed_univ (carrierSimultaneousPatch core patches witness radius)
    (carrierSimultaneousPatch_isOpen core patches witness radius)
    (by rw [carrierSimultaneousPatch_cover core patches witness witness_value convex radius positive])
  have simultaneous : ∀ point,∀ index ∈ source_partition.finsupport point,
      point ∈ carrierSimultaneousPatch core patches witness radius index := by
    intro point index member
    apply source_subordinate index
    apply subset_tsupport
    exact (source_partition.mem_finsupport point).mp member
  have source_supported : ∀ point,source_partition.finsupport point ∈ activeNerve patches := by
    intro point
    exact thickenedCarrierFace_mem_activeNerve core patches radius preserves (witness point)
      (source_partition.finsupport point) (partitionCoordinates_nonempty source_partition point)
      (fun index member => (simultaneous point index member).2)
  let intermediate := activePartitionNerveMap patches source_partition source_supported
  have source_contiguous : ∀ point,
      (subdivisionBarycenterMap patches point).val.support ∪ (intermediate point).val.support ∈
        activeNerve patches := by
    intro point
    have contained : (intermediate point).val.support ⊆
        (subdivisionBarycenterMap patches point).val.support := by
      rw [activePartitionNerveMap_support]
      intro index member
      exact Finsupp.mem_support_iff.mpr (ne_of_gt (simultaneous point index member).1)
    rw [Finset.union_eq_left.mpr contained]
    exact AbstractSimplicialComplex.support_mem _ _
  have composite_contiguous : ∀ point,
      (intermediate point).val.support ∪ (mapping (witness point)).val.support ∈
        activeNerve patches := by
    intro point
    apply thickenedCarrierFace_mem_activeNerve core patches radius preserves (witness point)
    · apply Finset.Nonempty.mono Finset.subset_union_left
      rw [activePartitionNerveMap_support]
      exact partitionCoordinates_nonempty source_partition point
    · intro index member
      rcases Finset.mem_union.mp member with source_member | core_member
      · rw [activePartitionNerveMap_support] at source_member
        exact (simultaneous point index source_member).2
      · apply core_subordinate index.val
        apply subset_tsupport
        apply (core_partition.mem_finsupport _).mp
        have nonzero := Finsupp.mem_support_iff.mp core_member
        change (coordinatesActiveSimplex patches
          (partitionCoordinates core_partition (witness point))
          (core_supported _)).weights index ≠ 0 at nonzero
        exact (core_partition.mem_finsupport _).mpr nonzero
  exact ⟨mapping,⟨(realizationAffineHomotopy _ (subdivisionBarycenterMap patches)
    intermediate source_contiguous).trans
    (realizationAffineHomotopy _ intermediate (mapping.comp witness) composite_contiguous)⟩⟩

/-- A contractible compact carrier for the actual witness image makes
the entire nerve contractible, without any convexity assumption on the union. -/
theorem entireNerve_contractible_of_compact_carrier
    (core region : Set E) (patches : Index → Set E)
    (compact : IsCompact core) (inside : core ⊆ region) [ContractibleSpace core]
    (convex : ∀ index,Convex ℝ (patches index))
    (closed : ∀ index,IsClosed {point : region | point.val ∈ patches index})
    (cover : (⋃ index,patches index) = region)
    (witness : C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches),core))
    (witness_value : ∀ point,(witness point).val = witnessEvaluation patches point) :
    ContractibleSpace (AbstractSimplicialComplex.Realization (activeNerve patches)) := by
  obtain ⟨mapping,⟨comparison⟩⟩ := exists_carrier_subdivision_comparison
    core region patches compact inside convex closed cover witness witness_value
  let inverse : C(AbstractSimplicialComplex.Realization (activeNerve patches),
      AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    ⟨(subdivisionBarycenterHomeomorph patches).symm,
      (subdivisionBarycenterHomeomorph patches).symm.continuous⟩
  have start : (subdivisionBarycenterMap patches).comp inverse =
      ContinuousMap.id (AbstractSimplicialComplex.Realization (activeNerve patches)) := by
    apply ContinuousMap.ext
    intro point
    exact (subdivisionBarycenterHomeomorph patches).apply_symm_apply point
  have null := ((id_nullhomotopic core).comp_left (witness.comp inverse)).comp_right mapping
  obtain ⟨point,⟨contraction⟩⟩ := null
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨point,⟨?_⟩⟩
  exact ((comparison.compContinuousMap inverse).cast start rfl).trans contraction

end ToricPower.CompactCarrierNerve

end
