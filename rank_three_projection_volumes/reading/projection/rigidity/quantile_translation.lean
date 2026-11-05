module

public import Projection.Basic
public import Projection.QuantileEnergy
public import TauCeti.Probability.Quantile.Map
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Exact translation of conditional height laws and quantiles

Translating the comparison body by `v` translates its Minkowski ray at time
`t` by `t • v`. The height quantile is consequently shifted by `t * ⟪e,v⟫`.
These are identities of the actual bodies and their normalized Haar measures.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Pointwise RealInnerProductSpace

namespace RankThreeProjection.Rigidity
open VolumePolynomials QuantileStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Normalizing Haar measure on a translated set commutes with translation. -/
theorem map_cond_vadd (v : E) (K : Set E) :
    (volume[|K]).map (fun x : E => v + x) = volume[|v +ᵥ K] := by
  have hpre : (fun x : E => v + x) ⁻¹' (v +ᵥ K) = K := by
    ext x
    simp only [mem_preimage, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_cancel_left]
  have hrestrict : (volume.restrict K).map (fun x : E => v + x) =
      volume.restrict (v +ᵥ K) := by
    have h := (MeasurableEquiv.addLeft v).measurableEmbedding.restrict_map
      (volume : Measure E) (v +ᵥ K)
    change ((volume : Measure E).map (fun x => v + x)).restrict (v +ᵥ K) =
      (volume.restrict ((fun x => v + x) ⁻¹' (v +ᵥ K))).map (fun x => v + x) at h
    rw [map_add_left_eq_self, hpre] at h
    exact h.symm
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul _ (by fun_prop), measure_vadd, hrestrict]

/-- The one-dimensional height law shifts by the corresponding scalar. -/
theorem heightLaw_vadd (K : Set E) (v e : E) :
    (volume[|v +ᵥ K]).map (fun x => ⟪e, x⟫) =
      ((volume[|K]).map (fun x => ⟪e, x⟫)).map (fun s : ℝ => ⟪e, v⟫ + s) := by
  rw [← map_cond_vadd, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact inner_add_right e v x

theorem conditional_ridge_integral_vadd (K : Set E) (v e : E)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    (∫ x, ψ ⟪e, x⟫ ∂volume[|v +ᵥ K]) =
      ∫ x, ψ (⟪e, v⟫ + ⟪e, x⟫) ∂volume[|K] := by
  rw [← map_cond_vadd, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_add_right]

theorem heightQuantile_translateBody (K : ConvexBody E) (v e : E)
    (hK : volume (K : Set E) ≠ 0) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    heightQuantile (translateBody v K : Set E) e u =
      heightQuantile (K : Set E) e u + ⟪e, v⟫ := by
  letI : IsProbabilityMeasure (volume[|(K : Set E)]) :=
    cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  letI : IsProbabilityMeasure ((volume[|(K : Set E)]).map (fun x => ⟪e, x⟫)) :=
    inferInstance
  unfold heightQuantile
  rw [coe_translateBody, heightLaw_vadd]
  rw [Measure.quantile_map_of_monotone (fun _ _ h => add_le_add le_rfl h)
    (by fun_prop) hu.1 hu.2]
  exact add_comm _ _

/-- Translation acts on the actual Minkowski ray with its usual factor. -/
theorem minkowskiRay_translate_comparison (K C : ConvexBody E) (v : E) (t : ℝ) :
    K + t • translateBody v C = translateBody (t • v) (K + t • C) := by
  simp only [translateBody, smul_add, ← pointBody_smul]
  ac_rfl

theorem minkowskiRay_volume_translate_comparison (K C : ConvexBody E) (v : E) (t : ℝ) :
    volume.real ((K + t • translateBody v C : ConvexBody E) : Set E) =
      volume.real ((K + t • C : ConvexBody E) : Set E) := by
  simp only [minkowskiRay_translate_comparison, coe_translateBody,
    Measure.real, measure_vadd]

theorem volume_minkowskiRay_ne_zero (K C : ConvexBody E)
    (hK : volume (K : Set E) ≠ 0) (t : ℝ) :
    volume ((K + t • C : ConvexBody E) : Set E) ≠ 0 := by
  obtain ⟨c, hc⟩ := C.nonempty
  have hsub : translateBody (t • c) K ≤ K + t • C := by
    intro x hx
    change x ∈ (translateBody (t • c) K : Set E) at hx
    rw [coe_translateBody] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k, hk, t • c, smul_mem_smul_set hc, by simp only [vadd_eq_add, add_comm]⟩
  have hm := measure_mono (μ := volume) hsub
  rw [coe_translateBody, measure_vadd] at hm
  intro hz
  exact hK (le_zero_iff.mp (hz ▸ hm))

/-- This exact shift removes the centroid drift in every projected quantile. -/
theorem heightQuantile_minkowskiRay_translate (K C : ConvexBody E)
    (v e : E) (hK : volume (K : Set E) ≠ 0) (t : ℝ)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    heightQuantile ((K + t • translateBody v C : ConvexBody E) : Set E) e u =
      heightQuantile ((K + t • C : ConvexBody E) : Set E) e u + t * ⟪e, v⟫ := by
  rw [minkowskiRay_translate_comparison,
    heightQuantile_translateBody (K + t • C) (t • v) e
      (volume_minkowskiRay_ne_zero K C hK t) hu, real_inner_smul_right]

theorem heightQuantile_minkowskiRay_sub_translation (K C : ConvexBody E)
    (v e : E) (hK : volume (K : Set E) ≠ 0) (t : ℝ)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    heightQuantile ((K + t • translateBody (-v) C : ConvexBody E) : Set E) e u =
      heightQuantile ((K + t • C : ConvexBody E) : Set E) e u - t * ⟪e, v⟫ := by
  rw [heightQuantile_minkowskiRay_translate K C (-v) e hK t hu, inner_neg_right]
  ring

end RankThreeProjection.Rigidity
