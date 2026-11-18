module

public import VolumePolynomials.MixedVolumeMultilinear
public import Mathlib.LinearAlgebra.Multilinear.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The actual mixed-volume functional as a multilinear map over `ℝ≥0`.
Mathlib's convex bodies form a module over this semiring, so no formal
differences of convex bodies and no negative dilations are introduced. -/

open MeasureTheory Module
open scoped NNReal BigOperators Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolumeMultilinear (d : ℕ) :
    MultilinearMap ℝ≥0 (fun _ : Fin d => ConvexBody E) ℝ :=
  MultilinearMap.mk' (mixedVolume μ)
    (fun K i A B => mixedVolume_add μ K i A B)
    (fun K i r A => by
      first
      | change mixedVolume μ (Function.update K i ((r : ℝ) • A)) =
          (r : ℝ) * mixedVolume μ (Function.update K i A)
        exact mixedVolume_smul μ K i A r.coe_nonneg)

@[simp] theorem mixedVolumeMultilinear_apply {d : ℕ} (K : Fin d → ConvexBody E) :
    mixedVolumeMultilinear μ d K = mixedVolume μ K := rfl

theorem mixedVolume_independent_smul {d : ℕ} (K : Fin d → ConvexBody E)
    (r : Fin d → ℝ) (hr : ∀ i, 0 ≤ r i) :
    mixedVolume μ (fun i => r i • K i) = (∏ i, r i) * mixedVolume μ K := by
  first
  | let c : Fin d → ℝ≥0 := fun i => ⟨r i, hr i⟩
    have h := MultilinearMap.map_smul_univ (mixedVolumeMultilinear μ d) c K
    have hprod : ((∏ i, c i : ℝ≥0) : ℝ) = ∏ i, r i :=
      NNReal.coe_prod Finset.univ c
    change mixedVolume μ (fun i => r i • K i) =
      ((∏ i, c i : ℝ≥0) : ℝ) * mixedVolume μ K at h
    rw [hprod] at h
    exact h

theorem mixedVolume_add_all {d : ℕ} (K L : Fin d → ConvexBody E) :
    mixedVolume μ (fun i => K i + L i) =
      ∑ s : Finset (Fin d), mixedVolume μ (s.piecewise K L) := by
  first
  | have h := MultilinearMap.map_add_univ (mixedVolumeMultilinear μ d) K L
    change mixedVolume μ (K + L) =
      ∑ s : Finset (Fin d), mixedVolume μ (s.piecewise K L) at h
    have he : K + L = (fun i => K i + L i) := rfl
    rw [he] at h
    exact h

end VolumePolynomials
