module

public import Ellipsoid.RectangleFaces
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : d < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have h := hf.tendsto_slope_zero_right.eventually (Iio_mem_nhds hd)
  filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
  simp only [zero_add, smul_eq_mul] at ht
  exact sub_neg.mp (neg_of_mul_neg_right ht (inv_nonneg.mpr ht0.le))

set_option backward.isDefEq.respectTransparency false in
/-- At a point strictly above the lower corner, diagonal stability gives
a simultaneous descent of all coordinates and all output coordinates. -/
theorem rectangle_strict_descent [Nonempty ι]
    {F : (ι → ℝ) → (ι → ℝ)} {a c : ι → ℝ} {A : Matrix ι ι ℝ}
    (hac : ∀ i, a i < c i) (hF : HasFDerivAt F (matrixDerivative A) c)
    (hA : DiagonallyStable A) {U : Set (ι → ℝ)} (hU : U ∈ 𝓝 c) :
    ∃ z ∈ U, a ≤ z ∧ z ≤ c ∧ F z ≤ F c ∧ (∑ i, z i) < ∑ i, c i := by
  obtain ⟨v, hv, hAv⟩ := hA.exists_pos_mulVec_pos
  let line : ℝ → (ι → ℝ) := fun t => c - t • v
  have hline : HasDerivAt line (-v) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_sub c
    change HasDerivAt (fun t : ℝ => c - t • v) (-v) 0
    exact h.congr_deriv (by rw [one_smul])
  have hcomp : HasDerivAt (fun t => F (line t)) (-(A *ᵥ v)) 0 := by
    have hFline : HasFDerivAt F (matrixDerivative A) (line 0) := by
      simpa only [line, zero_smul, sub_zero] using hF
    have hh := hFline.comp_hasDerivAt 0 hline
    change HasDerivAt (F ∘ line) (-(A *ᵥ v)) 0
    exact hh.congr_deriv (by rw [matrixDerivative_apply, Matrix.mulVec_neg])
  have hdecrease : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, F (line t) i < F c i := by
    apply Filter.eventually_all.mpr
    intro i
    have hh := eventually_lt_of_hasDerivAt_neg ((hasDerivAt_pi.mp hcomp) i)
      (neg_lt_zero.mpr (hAv i))
    simpa [line] using hh
  have hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, a i < line t i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => line t i) 0 := by dsimp [line]; fun_prop
    have hh := hc.eventually (Ioi_mem_nhds (show a i < line 0 i by simpa [line] using hac i))
    exact hh.filter_mono nhdsWithin_le_nhds
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), line t ∈ U := by
    have hc : ContinuousAt line 0 := hline.continuousAt
    have hh := hc.eventually (show U ∈ 𝓝 (line 0) by simpa [line] using hU)
    exact hh.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hlow, hdec, hmemt⟩ :=
    (hpos.and (hlower.and (hdecrease.and hmem))).exists
  refine ⟨line t, hmemt, fun i => (hlow i).le, fun i => ?_,
    fun i => (hdec i).le, ?_⟩
  · change c i - t * v i ≤ c i
    nlinarith [mul_pos ht (hv i)]
  · have hsum : 0 < ∑ i, v i :=
      Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
    simp only [line, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    nlinarith [mul_pos ht hsum]

end EllipsoidVerification
