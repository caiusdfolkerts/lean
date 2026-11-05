module

public import Projection.Hyperplane
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem centeredSegment_zero : centeredSegment (0 : E) = 0 := by
  apply ConvexBody.ext
  change segment ℝ (-(1 / 2 : ℝ) • (0 : E)) ((1 / 2 : ℝ) • (0 : E)) = {0}
  simp

section Measure
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem mixedVolume_zero_first {d : ℕ} (K : Fin d → ConvexBody E) :
    mixedVolume volume (Fin.cons (0 : ConvexBody E) K) = 0 := by
  simpa only [Fin.update_cons_zero] using
    mixedVolume_zero_arg volume (Fin.cons (0 : ConvexBody E) K) 0

/-- A repeated segment contributes zero to actual mixed volume.  The proof
sends its direction to the first coordinate and uses interval-fiber extrusion;
it does not define the diagonal of a matrix to be zero. -/
theorem mixedVolume_repeated_segment_zero {d : ℕ}
    (K : Fin d → ConvexBody E) (v : E) :
    mixedVolume volume
      (Fin.cons (centeredSegment v) (Fin.cons (centeredSegment v) K)) = 0 := by
  by_cases hv : v = 0
  · subst v
    rw [centeredSegment_zero, mixedVolume_zero_first]
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  let l : E →L[ℝ] ℝ := f.toContinuousLinearMap
  have hl : l v = 1 := hf
  let F := LinearMap.ker l.toLinearMap
  letI : MeasureSpace F := ⟨Measure.addHaar⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure F) := by
    change Measure.IsAddHaarMeasure (Measure.addHaar : Measure F)
    infer_instance
  let T : E ≃L[ℝ] ℝ × F := LinearFrame.continuousEquiv l v hl
  have hTv : T v = (1, 0) := by
    apply Prod.ext
    · exact hl
    · apply Subtype.ext
      change v - l v • v = 0
      simp only [hl, one_smul, sub_self]
  let K' : Fin d → ConvexBody (ℝ × F) :=
    fun i => mapBody T.toContinuousLinearMap (K i)
  have hmap :
      (fun i => mapBody T.toContinuousLinearMap
        ((Fin.cons (centeredSegment v) (Fin.cons (centeredSegment v) K) :
          Fin (d + 2) → ConvexBody E) i)) =
      Fin.cons (centeredSegment (1, (0 : F)))
        (Fin.cons (centeredSegment (1, (0 : F))) K') := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, map_centeredSegment,
        ContinuousLinearEquiv.coe_coe, hTv]
    · refine Fin.cases ?_ (fun k => rfl) j
      simp only [Fin.cons_succ, Fin.cons_zero, map_centeredSegment,
        ContinuousLinearEquiv.coe_coe, hTv]
  have hz : mixedVolume volume
      (Fin.cons (centeredSegment (1, (0 : F)))
        (Fin.cons (centeredSegment (1, (0 : F))) K')) = 0 := by
    have he := mixedVolume_centered_axis
      (Fin.cons (centeredSegment (1, (0 : F))) K')
    have hp :
        (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ F)
          ((Fin.cons (centeredSegment (1, (0 : F))) K' :
            Fin (d + 1) → ConvexBody (ℝ × F)) i)) =
        Fin.cons (0 : ConvexBody F)
          (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ F) (K' i)) := by
      funext i
      refine Fin.cases ?_ (fun j => rfl) i
      simp only [Fin.cons_zero, map_centeredSegment]
      change centeredSegment (0 : F) = 0
      exact centeredSegment_zero
    rw [hp, mixedVolume_zero_first] at he
    exact (mul_eq_zero.mp he).resolve_left (by positivity)
  rw [mixedVolume_eq_frameFactor_mul volume volume T, hmap, hz, mul_zero]

end Measure
end RankThreeProjection
