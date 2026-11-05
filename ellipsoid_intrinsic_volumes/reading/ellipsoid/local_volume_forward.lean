module

public import Ellipsoid.AugmentedCoefficientRecovery
public import Ellipsoid.CoefficientVolumeBounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace EllipsoidVerification

def geometricCoefficientMap (n : ℕ) (e : Coefficients n) : Fin n → ℝ := fun k =>
  if k.val + 1 = n then unitBallVolume n * Real.sqrt (e (Fin.last n))
  else unitBallVolume (k.val + 1) * coefficientTransform e (k.val + 1)

theorem contDiffAt_geometricCoefficientMap {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) : ContDiffAt ℝ 1 (geometricCoefficientMap n) e := by
  apply contDiffAt_pi.mpr
  intro k
  unfold geometricCoefficientMap
  split_ifs with hk
  · exact contDiffAt_const.mul
      ((contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).contDiffAt.sqrt he.2.2.ne')
  · have hU := (isOpen_positiveCoefficientDomain n).mem_nhds
      (admissible_mem_positiveCoefficientDomain he)
    have htransform : ContDiffAt ℝ ∞
        (fun e : Coefficients n => coefficientTransform e (k.val + 1)) e :=
      (contDiffOn_coefficientTransform (k := k.val + 1) (by omega) (by omega)).contDiffAt hU
    exact contDiffAt_const.mul (htransform.of_le (by simp))

theorem geometricCoefficientMap_axisCoefficients {n : ℕ} (E : FullEllipsoid n) :
    geometricCoefficientMap n (axisCoefficients E.semiaxis) =
      fun k : Fin n => E.volume (k.val + 1) := by
  funext k
  unfold geometricCoefficientMap
  split_ifs with hk
  · rw [hk, E.volume_top (by omega), axisCoefficients_last,
      Real.sqrt_sq_eq_abs, abs_of_pos (Finset.prod_pos fun i _ => E.semiaxis_pos i)]
  · exact (E.volume_eq_coefficientTransform (by omega) (by omega)).symm

theorem FullEllipsoid.volumeDistance_eq_norm {n : ℕ} (hn : 0 < n)
    (E F : FullEllipsoid n) : E.volumeDistance F =
      ‖(fun k : Fin n => E.volume (k.val + 1)) -
        (fun k : Fin n => F.volume (k.val + 1))‖ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro k
    change |E.volume (k.val + 1) - F.volume (k.val + 1)| ≤
      ‖fun j : Fin n => E.volume (j.val + 1) - F.volume (j.val + 1)‖
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (fun j : Fin n => E.volume (j.val + 1) - F.volume (j.val + 1)) k)
  · apply (pi_norm_le_iff_of_nonneg (E.volumeDistance_nonneg hn F)).mpr
    exact fun k => E.volume_error_le F k

/-- Smoothness of the literal coefficient integral yields a local upper
Lipschitz bound for the actual geometric measurements. -/
theorem local_volume_forward_lipschitz {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    ∃ L : ℝ, 0 < L ∧ ∃ U ∈ 𝓝 e, ∀ E F : FullEllipsoid n,
      axisCoefficients E.semiaxis ∈ U → axisCoefficients F.semiaxis ∈ U →
      E.volumeDistance F ≤ L * ‖axisCoefficients E.semiaxis - axisCoefficients F.semiaxis‖ := by
  obtain ⟨L, U, hU, hLip⟩ := (contDiffAt_geometricCoefficientMap he).exists_lipschitzOnWith
  refine ⟨(L : ℝ) + 1, by positivity, U, hU, ?_⟩
  intro E F hE hF
  have h := hLip.dist_le_mul _ hE _ hF
  rw [dist_eq_norm, dist_eq_norm, geometricCoefficientMap_axisCoefficients,
    geometricCoefficientMap_axisCoefficients, ← E.volumeDistance_eq_norm hn F] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end EllipsoidVerification
