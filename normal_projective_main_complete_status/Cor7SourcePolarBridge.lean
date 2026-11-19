module
public import normal_projective.complete
public import Cor7FiniteHullExposure
public import Cor7PairFreeSupport
/-! Proof-interface work only. The polar realization below does not yet supply
the standalone labelled crosspolytope conclusion. No final Solution is claimed. -/
@[expose] public section
noncomputable section
open Set
namespace PalomarNormalCorollary7Bridge
open NormalProjective
/-- Choose an arbitrary interior centre and recover the complete proved polar
cube recognition, directly from the paper's actual open-segment hypotheses. -/
theorem translated_polar_realizes_cube (n : ℕ)
    (v : RootedGeometry.Labels (n+1) → CanonicalModel.Space (n+1))
    (hfull : (interior (NormalHull.hull v)).Nonempty)
    (hpair : ∀ i : Fin (n+1),
      (openSegment ℝ (v (Sum.inl i)) (v (Sum.inr i)) ∩
        interior (NormalHull.hull v)).Nonempty) :
    ∃ O ∈ interior (NormalHull.hull v),
      NormalizedCubeMoves.Realizes (fun l => v l - O) := by
  classical
  obtain ⟨O,hO⟩ := hfull
  have hp : ∀ i : Fin (n+1), ∃ t : ℝ, 0<t ∧ t<1 ∧
      (1-t) • v (Sum.inl i) + t • v (Sum.inr i) ∈ interior (NormalHull.hull v) := by
    intro i
    obtain ⟨z,hseg,hz⟩ := hpair i
    rw [openSegment_eq_image] at hseg
    obtain ⟨t,ht,rfl⟩ := hseg
    exact ⟨t,ht.1,ht.2,hz⟩
  choose t ht0 ht1 ht using hp
  let w := fun l => v l - O
  have hz : (0 : CanonicalModel.Space (n+1)) ∈ interior (NormalHull.hull w) := by
    simpa only [sub_self] using DiagonalSites.interior_translation v O hO
  let sites : DiagonalSites.Sites w := {
    value := fun i => ((1-t i) • v (Sum.inl i) + t i • v (Sum.inr i)) - O
    parameter := t
    parameter_pos := ht0
    parameter_lt_one := ht1
    value_eq := by
      intro i
      ext j
      simp only [w, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    interior := fun i => DiagonalSites.interior_translation v O (ht i) }
  exact ⟨O,hO,NormalizedCubeMoves.realizes_of_sites w hz sites⟩

/-- Every supplied point is strictly separated from every other supplied label.
This extracts actual affine supporting data, not a finite incidence assertion. -/
theorem strict_exposure_each_label (n : ℕ)
    (v : RootedGeometry.Labels (n+1) → CanonicalModel.Space (n+1))
    (hfull : (interior (NormalHull.hull v)).Nonempty)
    (hpair : ∀ i : Fin (n+1),
      (openSegment ℝ (v (Sum.inl i)) (v (Sum.inr i)) ∩
        interior (NormalHull.hull v)).Nonempty)
    (i : RootedGeometry.Labels (n+1)) :
    ∃ (ℓ : CanonicalModel.Space (n+1) →L[ℝ] ℝ) (a : ℝ),
      ℓ (v i) = a ∧ ∀ j, j ≠ i → ℓ (v j) < a := by
  obtain ⟨O,hO,hr⟩ := translated_polar_realizes_cube n v hfull hpair
  obtain ⟨ℓ,hi,hj⟩ := NormalizedCubeMoves.exposed_normals (fun l => v l - O) hr i
  refine ⟨ℓ,1 + ℓ O,?_,?_⟩
  · rw [map_sub] at hi
    linarith
  · intro j hji
    have hs := hj j hji
    rw [map_sub] at hs
    linarith

/-- Distinctness is derived from the paper hypotheses; it is not added as an
input assumption to avoid the actual geometric recognition step. -/
theorem paired_labels_injective (n : ℕ)
    (v : RootedGeometry.Labels (n+1) → CanonicalModel.Space (n+1))
    (hfull : (interior (NormalHull.hull v)).Nonempty)
    (hpair : ∀ i : Fin (n+1),
      (openSegment ℝ (v (Sum.inl i)) (v (Sum.inr i)) ∩
        interior (NormalHull.hull v)).Nonempty) : Function.Injective v := by
  intro i j hij
  by_contra hne
  obtain ⟨ℓ,a,hi,hlt⟩ := strict_exposure_each_label n v hfull hpair i
  have hs := hlt j (Ne.symm hne)
  rw [← hij,hi] at hs
  exact (lt_irrefl a) hs

/-- All and only the supplied actual points are extreme vertices; this follows
from their proved strict supporting functionals and the full hull-level lemma. -/
theorem paired_extremePoints (n : ℕ)
    (v : RootedGeometry.Labels (n+1) → CanonicalModel.Space (n+1))
    (hfull : (interior (NormalHull.hull v)).Nonempty)
    (hpair : ∀ i : Fin (n+1),
      (openSegment ℝ (v (Sum.inl i)) (v (Sum.inr i)) ∩
        interior (NormalHull.hull v)).Nonempty) :
    (NormalHull.hull v).extremePoints ℝ = Set.range v := by
  apply Set.Subset.antisymm
  · exact extremePoints_convexHull_subset
  · rintro x ⟨i,rfl⟩
    obtain ⟨ℓ,a,hi,hs⟩ := strict_exposure_each_label n v hfull hpair i
    apply PalomarNormalCorollary7Exposure.strict_generator_extreme v ℓ.toLinearMap i
    intro j hji
    simpa only [ContinuousLinearMap.coe_coe,hi] using hs j hji

/-- Every nonempty pair-free subset of the original labels is exactly the
maximizer set of an actual supporting functional of the original points. -/
theorem pairfree_support (n : ℕ)
    (v : RootedGeometry.Labels (n+1) → CanonicalModel.Space (n+1))
    (hfull : (interior (NormalHull.hull v)).Nonempty)
    (hpair : ∀ i : Fin (n+1),
      (openSegment ℝ (v (Sum.inl i)) (v (Sum.inr i)) ∩
        interior (NormalHull.hull v)).Nonempty)
    (S : Finset (RootedGeometry.Labels (n+1))) (hne : S.Nonempty)
    (hfree : ∀ i : Fin (n+1), ¬(Sum.inl i ∈ S ∧ Sum.inr i ∈ S)) :
    ∃ (ℓ : CanonicalModel.Space (n+1) →L[ℝ] ℝ) (a : ℝ), ℓ ≠ 0 ∧
      (∀ i, ℓ (v i) ≤ a) ∧ (∀ i, ℓ (v i) = a ↔ i ∈ S) := by
  classical
  obtain ⟨O,hO,hr⟩ := translated_polar_realizes_cube n v hfull hpair
  let w := fun l => v l - O
  have hz : (0 : CanonicalModel.Space (n+1)) ∈ interior (NormalHull.hull w) :=
    NormalizedCubeMoves.zero_interior_hull w hr
  have hp : ∀ i : Fin (n+1), ∃ t : ℝ, 0<t ∧ t<1 ∧
      (1-t) • w (Sum.inl i) + t • w (Sum.inr i) ∈ interior (NormalHull.hull w) := by
    intro i
    obtain ⟨z,hseg,hz'⟩ := hpair i
    rw [openSegment_eq_image] at hseg
    obtain ⟨t,ht,rfl⟩ := hseg
    refine ⟨t,ht.1,ht.2,?_⟩
    have hh := DiagonalSites.interior_translation v O hz'
    have he : (1-t) • w (Sum.inl i) + t • w (Sum.inr i) =
        ((1-t) • v (Sum.inl i) + t • v (Sum.inr i)) - O := by
      ext j
      simp only [w,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he]
    exact hh
  obtain ⟨ℓ,hℓ,hle,heq⟩ :=
    PalomarNormalCorollary7Support.centered_pairfree_support n w hz hp S hne hfree
  refine ⟨ℓ,1+ℓ O,hℓ,?_,?_⟩
  · intro i
    have hi := hle i
    change ℓ (v i - O) ≤ 1 at hi
    rw [map_sub] at hi
    linarith
  · intro i
    have hi := heq i
    change (ℓ (v i - O) = 1 ↔ i ∈ S) at hi
    rw [map_sub] at hi
    exact (by constructor <;> intro he <;> linarith :
      ℓ (v i) = 1 + ℓ O ↔ ℓ (v i) - ℓ O = 1).trans hi
end PalomarNormalCorollary7Bridge
