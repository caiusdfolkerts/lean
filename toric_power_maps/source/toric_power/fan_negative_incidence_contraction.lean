module

public import ToricPower.FanNegativeContraction
public import ToricPower.CechSingular.ReducedCochainAcyclicity

/-! # The contraction on the actual negative-ray incidence realization

This specialization supplies every geometric hypothesis of the coordinate
contraction from the actual fan, a surjective chart enumeration, and a full
ray enumeration. It retains arbitrary zero rays of the recession form.
-/

@[expose] public noncomputable section

open TauCeti.Toric
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open ToricPower.NegativeSupportCech
open scoped Classical

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.decEq

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Ray Index : Type} [Finite Ray]

variable (fan : Fan i) (charts : Index → fan.cones)
  (surjective : Function.Surjective charts) (rays : Ray ≃ fan.Ray)
  (negative : fan.Ray → Prop)

def fanNegativeRayIncidence : Index → {r : Ray // negative (rays r)} → Prop :=
  fun index ray => (rays ray.val).toCone ≤ charts index

abbrev fanNegativeActiveVertex :=
  ActiveIndex (incidencePatches (fanNegativeRayIncidence fan charts rays negative) (fun _ => True))

def fanNegativeVertexEmbedding : fanNegativeActiveVertex fan charts rays negative ↪ fan.Ray where
  toFun v := rays v.val.val
  inj' := by
    intro a b equality
    apply Subtype.ext
    exact Subtype.ext (rays.injective equality)

def fanNegativeVertexOfRay (ρ : fan.Ray) (member : negative ρ) :
    fanNegativeActiveVertex fan charts rays negative := by
  let index := Classical.choose (surjective ρ.toCone)
  have same : charts index = ρ.toCone := Classical.choose_spec (surjective ρ.toCone)
  refine ⟨⟨rays.symm ρ, ?_⟩, index, trivial, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using member
  · change (rays (rays.symm ρ)).toCone ≤ charts index
    rw [Equiv.apply_symm_apply, same]

@[simp]
theorem fanNegativeVertexEmbedding_ofRay (ρ : fan.Ray) (member : negative ρ) :
    fanNegativeVertexEmbedding fan charts rays negative
      (fanNegativeVertexOfRay fan charts surjective rays negative ρ member) = ρ := by
  exact rays.apply_symm_apply ρ

private theorem activeNerve_membership {J : Type} {E : Type*} (patches : J → Set E)
    (face : Finset (ActiveIndex patches)) :
    face ∈ activeNerve patches ↔ face.image Subtype.val ∈
      BondalThomsen.ClosedConvexNerveComparison.coverNerve patches := by
  rfl

include surjective in
theorem fanNegativeActive_faces
    (face : Finset (fanNegativeActiveVertex fan charts rays negative)) :
    face ∈ activeNerve (incidencePatches
      (fanNegativeRayIncidence fan charts rays negative) (fun _ => True)) ↔
      face.Nonempty ∧ ∃ σ : fan.cones,
        ∀ v ∈ face, (fanNegativeVertexEmbedding fan charts rays negative v).toCone ≤ σ := by
  letI : DecidableEq {r : Ray // negative (rays r)} := Classical.decEq _
  rw [activeNerve_membership, incidencePatches_coverNerve]
  constructor
  · rintro ⟨nonempty, index, _, contained⟩
    refine ⟨Finset.image_nonempty.mp nonempty, charts index, ?_⟩
    intro v present
    exact contained v.val (Finset.mem_image.mpr ⟨v, present, rfl⟩)
  · rintro ⟨nonempty, σ, contained⟩
    obtain ⟨index, rfl⟩ := surjective σ
    refine ⟨nonempty.image _, index, trivial, ?_⟩
    rintro v present
    obtain ⟨original, member, rfl⟩ := Finset.mem_image.mp present
    exact contained original member

theorem linearForm_exists_negative {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : E →ₗ[ℝ] ℝ) (nonzero : d ≠ 0) : ∃ w, d w < 0 := by
  have existsNonzero : ∃ x, d x ≠ 0 := by
    by_contra h
    apply nonzero
    ext x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := existsNonzero
  rcases lt_or_gt_of_ne hx with neg | pos
  · exact ⟨x, neg⟩
  · exact ⟨-x, by simpa only [map_neg] using neg_neg_of_pos pos⟩

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

include surjective in
/-- A recession direction contracts the exact negative-ray realization,
not merely its incidence poset or a surrogate topological space. -/
theorem fanNegativeIncidence_contractible (regular : fan.IsRegular)
    (complete : fan.IsComplete) (d : V →ₗ[ℝ] ℝ) (nonzero : d ≠ 0)
    (inside : ∀ ρ : fan.Ray, negative ρ → d (fanRayRealVector fan ρ) ≤ 0)
    (outside : ∀ ρ : fan.Ray, ¬ negative ρ → 0 ≤ d (fanRayRealVector fan ρ)) :
    ContractibleSpace (incidenceRealization
      (fanNegativeRayIncidence fan charts rays negative) (fun _ => True)) := by
  obtain ⟨w, hw⟩ := linearForm_exists_negative d nonzero
  apply fanNegativeRealization_contractible fan
    (activeNerve (incidencePatches
      (fanNegativeRayIncidence fan charts rays negative) (fun _ => True)))
    (fanNegativeVertexEmbedding fan charts rays negative)
    (fanNegativeActive_faces fan charts surjective rays negative) complete d
    ?_ ?_ regular w hw
  · intro ρ hρ
    have member : negative ρ := by
      by_contra h
      exact (not_lt_of_ge (outside ρ h)) hρ
    exact ⟨fanNegativeVertexOfRay fan charts surjective rays negative ρ member,
      fanNegativeVertexEmbedding_ofRay fan charts surjective rays negative ρ member⟩
  · intro v
    exact inside (rays v.val.val) v.val.property

end ToricPower
