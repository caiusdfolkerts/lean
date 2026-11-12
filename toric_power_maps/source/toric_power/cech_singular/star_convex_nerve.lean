module

public import ToricPower.CechSingular.CompactCarrierComparison

/-!
# Contractibility of the nerve of a star-convex union

The patches are a finite relatively closed convex cover. Their union
may be star-convex rather than convex. The actual barycentric witness
image is compact and lies in the union; adjoining its radial segments
to a star center gives a compact contractible carrier still inside the
union. The full partition-of-unity comparison then contracts the nerve.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveBarycentricHomotopy
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveGlobalCarrierHomotopy
open ToricPower.NegativeSupportCech

namespace ToricPower.CompactCarrierNerve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal union of radial segments from the chosen center. -/
def radialCarrier (center : E) (points : Set E) : Set E :=
  ⋃ point ∈ points,segment ℝ center point

theorem subset_radialCarrier (center : E) (points : Set E) :
    points ⊆ radialCarrier center points := by
  intro point present
  exact mem_iUnion₂.mpr ⟨point,present,right_mem_segment ℝ center point⟩

theorem radialCarrier_starConvex (center : E) (points : Set E) :
    StarConvex ℝ center (radialCarrier center points) :=
  starConvex_iUnion₂ fun point _ =>
    (convex_segment center point).starConvex (left_mem_segment ℝ center point)

theorem radialCarrier_eq_image (center : E) (points : Set E) :
    radialCarrier center points =
      (fun pair : ℝ × E => (1-pair.1) • center + pair.1 • pair.2) ''
        (Icc (0 : ℝ) 1 ×ˢ points) := by
  ext point
  constructor
  · intro present
    obtain ⟨endpoint,endpoint_mem,segment_mem⟩ := mem_iUnion₂.mp present
    rw [segment_eq_image] at segment_mem
    obtain ⟨time,time_mem,equal⟩ := segment_mem
    exact ⟨(time,endpoint),⟨time_mem,endpoint_mem⟩,equal⟩
  · rintro ⟨⟨time,endpoint⟩,⟨time_mem,endpoint_mem⟩,rfl⟩
    apply mem_iUnion₂.mpr
    refine ⟨endpoint,endpoint_mem,?_⟩
    rw [segment_eq_image]
    exact ⟨time,time_mem,rfl⟩

theorem radialCarrier_isCompact (center : E) (points : Set E)
    (compact : IsCompact points) : IsCompact (radialCarrier center points) := by
  rw [radialCarrier_eq_image]
  exact (isCompact_Icc.prod compact).image
    ((continuous_const.sub continuous_fst).smul continuous_const |>.add
      (continuous_fst.smul continuous_snd))

theorem radialCarrier_subset (center : E) (points region : Set E)
    (star : StarConvex ℝ center region) (inside : points ⊆ region) :
    radialCarrier center points ⊆ region := by
  intro point present
  obtain ⟨endpoint,endpoint_mem,segment_mem⟩ := mem_iUnion₂.mp present
  exact star.segment_subset (inside endpoint_mem) segment_mem

variable {Index : Type} [Finite Index]

/-- The witness map stays in one convex patch on each flag simplex,
even when the union of all patches is not convex. -/
theorem witnessEvaluation_mem_union (patches : Index → Set E)
    (convex : ∀ index,Convex ℝ (patches index))
    (point : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :
    witnessEvaluation patches point ∈ ⋃ index,patches index := by
  obtain ⟨least,present,minimal⟩ := barycentricFace_has_minimum patches point.val.support
    (AbstractSimplicialComplex.support_mem _ point)
  obtain ⟨index,contains⟩ := ((mem_coverNerve_iff patches least.val).mp least.property).1
  have in_carrier := witnessEvaluation_face_mem_carrier patches
    ⟨point.val.support,AbstractSimplicialComplex.support_mem _ point⟩ least minimal
    ⟨point.val,AbstractSimplicialComplex.mem_convexHull_carrier _ point⟩
  exact mem_iUnion.mpr ⟨index,
    cofaceWitnessCarrier_subset_patch patches convex least index contains in_carrier⟩

/-- A nonempty union gives a genuine vertex in the full subdivided nerve. -/
theorem nerveBarycentricRealization_nonempty (patches : Index → Set E)
    (nonempty : (⋃ index,patches index).Nonempty) :
    Nonempty (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) := by
  obtain ⟨point,present⟩ := nonempty
  obtain ⟨index,contains⟩ := mem_iUnion.mp present
  have singleton : ({index} : Finset Index) ∈ coverNerve patches :=
    (mem_coverNerve_iff patches _).mpr ⟨Finset.singleton_nonempty index,point,
      fun selected member => by simpa only [Finset.mem_singleton.mp member] using contains⟩
  exact ⟨AbstractSimplicialComplex.vertex (nerveBarycentricComplex patches)
    ⟨{index},singleton⟩⟩

/-- The entire finite nerve is contractible for a relatively closed
convex cover of any nonempty star-convex region. -/
theorem entireNerve_contractible_of_starConvex (patches : Index → Set E) (region : Set E)
    (center : E) (star : StarConvex ℝ center region) (nonempty : region.Nonempty)
    (convex : ∀ index,Convex ℝ (patches index))
    (closed : ∀ index,IsClosed {point : region | point.val ∈ patches index})
    (cover : (⋃ index,patches index) = region) :
    ContractibleSpace (AbstractSimplicialComplex.Realization (activeNerve patches)) := by
  letI : CompactSpace (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    finiteRealization_compactSpace _
  letI : Nonempty (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    nerveBarycentricRealization_nonempty patches (cover.symm ▸ nonempty)
  let points : Set E := Set.range (witnessEvaluation patches)
  let core : Set E := radialCarrier center points
  have compactPoints : IsCompact points := isCompact_range (witnessEvaluation_continuous patches)
  have insidePoints : points ⊆ region := by
    rintro point ⟨source,rfl⟩
    rw [← cover]
    exact witnessEvaluation_mem_union patches convex source
  have core_nonempty : core.Nonempty :=
    (Set.range_nonempty (witnessEvaluation patches)).mono (subset_radialCarrier center points)
  letI : ContractibleSpace core := (radialCarrier_starConvex center points).contractibleSpace
    core_nonempty
  let witness : C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches),core) := {
    toFun point := ⟨witnessEvaluation patches point,
      subset_radialCarrier center points ⟨point,rfl⟩⟩
    continuous_toFun := (witnessEvaluation_continuous patches).subtype_mk _ }
  exact entireNerve_contractible_of_compact_carrier core region patches
    (radialCarrier_isCompact center points compactPoints)
    (radialCarrier_subset center points region star insidePoints)
    convex closed cover witness (fun _ => rfl)

end ToricPower.CompactCarrierNerve

end
