module

public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Homothety
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

/-!
# Exact planar comparison from ordinary area

The paper's equality case is used here only after its hypotheses have been
recovered from literal Lebesgue areas.  The plane `ℝ × ℝ` has the max norm in
Mathlib, so the inner-product Brunn–Minkowski theorem is applied after a
measure-preserving linear transport to `WithLp 2 (ℝ × ℝ)`.
-/

open MeasureTheory Set
open scoped Pointwise ENNReal

namespace VolumePolynomials

private theorem equal_area_translates_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 2)
    {K L : Set E} (hK : Convex ℝ K) (hKc : IsCompact K)
    (hL : Convex ℝ L) (hLc : IsCompact L)
    (hpos : 0 < volume.real K)
    (heq : volume.real L = volume.real K)
    (hsum : volume.real (K + L) = 4 * volume.real K) :
    ∃ v : E, L = v +ᵥ K := by
  first
  | have hK0 : volume K ≠ 0 := by
      intro h
      simp [Measure.real, h] at hpos
    have hvol : volume L = volume K := by
      calc
        volume L = ENNReal.ofReal (volume.real L) :=
          (ofReal_measureReal hLc.measure_lt_top.ne).symm
        _ = ENNReal.ofReal (volume.real K) := congrArg ENNReal.ofReal heq
        _ = volume K := ofReal_measureReal hKc.measure_lt_top.ne
    have hL0 : volume L ≠ 0 := hvol.symm ▸ hK0
    have hmidc : IsCompact ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L) :=
      (hKc.smul (1 / 2 : ℝ)).add (hLc.smul (1 / 2 : ℝ))
    have hmidReal : volume.real ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L) =
        volume.real K := by
      rw [← smul_add]
      change (volume ((1 / 2 : ℝ) • (K + L))).toReal = (volume K).toReal
      rw [Measure.addHaar_smul_of_nonneg volume (show 0 ≤ (1 / 2 : ℝ) by norm_num),
        hdim, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
      change (1 / 2 : ℝ) ^ 2 * volume.real (K + L) = volume.real K
      rw [hsum]
      ring
    have hmid : volume ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L) = volume K := by
      calc
        _ = ENNReal.ofReal (volume.real ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L)) :=
          (ofReal_measureReal hmidc.measure_lt_top.ne).symm
        _ = ENNReal.ofReal (volume.real K) := congrArg ENNReal.ofReal hmidReal
        _ = volume K := ofReal_measureReal hKc.measure_lt_top.ne
    apply hK.exists_eq_vadd_of_volume_le hKc hK0 hL hLc hL0
      (show 0 < (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hmid, hvol,
      ← ENNReal.rpow_add _ _ hK0 hKc.measure_lt_top.ne]
    norm_num

/-- Two compact convex planar sets of the same positive area are translates if
the area of their sum is four times their common area. -/
theorem equal_area_translates
    {K L : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKc : IsCompact K)
    (hL : Convex ℝ L) (hLc : IsCompact L)
    (hpos : 0 < volume.real K)
    (heq : volume.real L = volume.real K)
    (hsum : volume.real (K + L) = 4 * volume.real K) :
    ∃ v : ℝ × ℝ, L = v +ᵥ K := by
  first
  | let e : (ℝ × ℝ) ≃L[ℝ] WithLp 2 (ℝ × ℝ) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm
    have he : MeasurePreserving e volume volume := WithLp.volume_preserving_toLp ℝ ℝ
    have harea (S : Set (ℝ × ℝ)) : volume.real (e '' S) = volume.real S := by
      have hm := he.measure_preimage_emb
        e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (e '' S)
      rw [Set.preimage_image_eq _ e.injective] at hm
      simpa only [measureReal_def] using congrArg ENNReal.toReal hm.symm
    have hdim : Module.finrank ℝ (WithLp 2 (ℝ × ℝ)) = 2 := by
      rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq]
      simp
    have hsum' : volume.real (e '' K + e '' L) = 4 * volume.real (e '' K) := by
      rw [← Set.image_add e, harea, harea]
      exact hsum
    obtain ⟨v, hv⟩ := equal_area_translates_inner hdim
      (hK.linear_image e.toLinearMap) (hKc.image e.continuous)
      (hL.linear_image e.toLinearMap) (hLc.image e.continuous)
      (by
        change 0 < volume.real (e '' K)
        rwa [harea])
      (by
        change volume.real (e '' L) = volume.real (e '' K)
        simpa only [harea] using heq) hsum'
    refine ⟨e.symm v, ?_⟩
    have hi := congrArg (Set.image e.symm) hv
    change e.symm '' (e '' L) = e.symm '' (v +ᵥ e '' K) at hi
    simpa only [← Set.image_vadd, Set.image_image, Function.comp_apply,
      vadd_eq_add, map_add, e.symm_apply_apply, Set.image_id'] using hi


end VolumePolynomials
