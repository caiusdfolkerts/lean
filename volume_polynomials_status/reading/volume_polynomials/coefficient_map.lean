module
public import VolumePolynomials.VolumePolynomialExistence
public import VolumePolynomials.ClosedVolumeLocus

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The actual continuous coefficient map

Polynomial existence and uniqueness identify the coefficient vector of every
tuple of compact convex bodies. The definition chooses that uniquely determined
vector; it does not choose a polynomial approximation or assume mixed-volume
continuity. Continuity follows from volume continuity and the finite-dimensional
evaluation embedding proved before polynomial existence.
-/

open Set Topology

namespace VolumePolynomials

def coefficientMap {n d : ℕ} (K : Fin n → Body d) : Coefficients n d :=
  Classical.choose (exists_volume_polynomial K)

theorem coefficientMap_realizes {n d : ℕ} (K : Fin n → Body d) :
    Realizes K (coefficientMap K) :=
  Classical.choose_spec (exists_volume_polynomial K)

theorem Realizes.eq_coefficientMap {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) : c = coefficientMap K :=
  hc.unique (coefficientMap_realizes K)

theorem realizes_iff_eq_coefficientMap {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} : Realizes K c ↔ c = coefficientMap K :=
  ⟨Realizes.eq_coefficientMap, fun h => h.symm ▸ coefficientMap_realizes K⟩

theorem coefficientMap_nonnegative {n d : ℕ} (K : Fin n → Body d)
    (α : MultiIndex n d) : 0 ≤ coefficientMap K α :=
  (coefficientMap_realizes K).coefficients_nonnegative α

theorem evaluation_coefficientMap {n d : ℕ} (K : Fin n → Body d) :
    evaluationEmbedding n d (coefficientMap K) = volumeEvaluation K :=
  realizes_iff_evaluation_eq.mp (coefficientMap_realizes K)

theorem continuous_coefficientMap (n d : ℕ) :
    Continuous (coefficientMap (n := n) (d := d)) := by
  first
  | apply (isClosedEmbedding_evaluation n d).isEmbedding.continuous_iff.mpr
    have heq : evaluationEmbedding n d ∘ coefficientMap =
        (volumeEvaluation : (Fin n → Body d) → _) := by
      funext K
      exact evaluation_coefficientMap K
    rw [heq]
    exact continuous_volumeEvaluation n d

theorem range_coefficientMap (n d : ℕ) :
    Set.range (coefficientMap (n := n) (d := d)) = VolumeLocus n d := by
  first
  | ext c
    constructor
    · rintro ⟨K, rfl⟩
      exact ⟨K, coefficientMap_realizes K⟩
    · rintro ⟨K, hK⟩
      exact ⟨K, hK.eq_coefficientMap.symm⟩

theorem boundedVolumeLocus_eq_coefficientMap_image (n d : ℕ) (C : Set (Space d)) :
    boundedVolumeLocus n d C = coefficientMap '' boundedTuples n d C := by
  first
  | ext c
    constructor
    · rintro ⟨K, hK, hc⟩
      exact ⟨K, hK, hc.eq_coefficientMap.symm⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, hK, coefficientMap_realizes K⟩

/-- Proposition 2.4 for every Hausdorff-dense class of tuples, with its
coefficient image interpreted using the actual volume polynomial. -/
theorem closure_coefficientMap_image_of_dense {n d : ℕ} (hd : 0 < d)
    {S : Set (Fin n → Body d)} (hS : Dense S) :
    closure (coefficientMap '' S) = VolumeLocus n d := by
  first
  | apply Set.Subset.antisymm
    · apply closure_minimal _ (isClosed_volumeLocus n d hd)
      rintro c ⟨K, _, rfl⟩
      exact ⟨K, coefficientMap_realizes K⟩
    · rw [← range_coefficientMap]
      exact (continuous_coefficientMap n d).range_subset_closure_image_dense hS

end VolumePolynomials
