module

public import Ellipsoid.CoefficientVolumeBounds

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace EllipsoidVerification

/-- The exact quantitative assertion of Theorem 1.2. The coefficient inverse
estimate and the multiplicity-preserving polynomial root bound are both
proved dependencies; no separation of semiaxes is assumed. -/
theorem uniform_holder_recovery : UniformHolderRecovery := by
  intro n hn a b ha hab
  cases n with
  | zero => omega
  | succ m =>
    have hb : 0 < b := ha.trans_le hab
    obtain ⟨L, hL, hcoeff⟩ := axisCoefficientData_inverse_lipschitz m ha hab
    obtain ⟨R, hR, hroots⟩ := uniform_real_root_holder (n := m + 1) (by omega)
      (b ^ 2) (sq_nonneg b)
    let M := volumeCoefficientBound (m + 1) b
    have hM : 0 < M := volumeCoefficientBound_pos hb.le
    let η : ℝ := 1 / (m + 1 : ℕ)
    have hη : 0 < η := one_div_pos.mpr (by positivity)
    let C : ℝ := R * (L * M) ^ η / (2 * a)
    have hC : 0 < C := div_pos
      (mul_pos hR (Real.rpow_pos_of_pos (mul_pos hL hM) _)) (by positivity)
    refine ⟨C, hC, ?_⟩
    intro E F hE hF
    have hEbox : E.semiaxis ∈ Icc (fun _ => a) (fun _ => b) :=
      ⟨fun i => (hE i).1, fun i => (hE i).2⟩
    have hFbox : F.semiaxis ∈ Icc (fun _ => a) (fun _ => b) :=
      ⟨fun i => (hF i).1, fun i => (hF i).2⟩
    have hnormE : ‖fun i => E.semiaxis i ^ 2‖ ≤ b ^ 2 := by
      apply (pi_norm_le_iff_of_nonneg (sq_nonneg b)).mpr
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [E.semiaxis_pos i, (hE i).2]
    have hnormF : ‖fun i => F.semiaxis i ^ 2‖ ≤ b ^ 2 := by
      apply (pi_norm_le_iff_of_nonneg (sq_nonneg b)).mpr
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [F.semiaxis_pos i, (hF i).2]
    have hD := E.volumeDistance_nonneg (by omega) F
    have hfull : ‖realRootCoefficients (fun i => E.semiaxis i ^ 2) -
        realRootCoefficients (fun i => F.semiaxis i ^ 2)‖ ≤
        L * M * E.volumeDistance F := by
      calc
        _ ≤ ‖axisCoefficientData E.semiaxis - axisCoefficientData F.semiaxis‖ :=
          rootCoefficients_squared_axes_bound _ _
        _ ≤ L * ‖augmentedCoefficientMap m (axisCoefficientData E.semiaxis) -
            augmentedCoefficientMap m (axisCoefficientData F.semiaxis)‖ :=
          hcoeff _ _ hEbox hFbox
        _ ≤ L * (M * E.volumeDistance F) := mul_le_mul_of_nonneg_left
          (augmentedCoefficientMap_axisData_volume_bound E F hb.le
            (fun i => (hE i).2) (fun i => (hF i).2)) hL.le
        _ = _ := by ring
    obtain ⟨σ, hσ⟩ := hroots (fun i => E.semiaxis i ^ 2)
      (fun i => F.semiaxis i ^ 2) hnormE hnormF
    have hroot (i : Fin (m + 1)) :
        |E.semiaxis i ^ 2 - F.semiaxis (σ i) ^ 2| ≤
          R * (L * M) ^ η * (E.volumeDistance F) ^ η := by
      apply (hσ i).trans
      calc
        _ ≤ R * (L * M * E.volumeDistance F) ^ η :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hfull hη.le) hR.le
        _ = _ := by rw [Real.mul_rpow (mul_pos hL hM).le hD]; ring
    apply E.axisDistance_le_of_perm F σ (mul_nonneg hC.le (Real.rpow_nonneg hD _))
    intro i
    have hsum : 2 * a ≤ E.semiaxis i + F.semiaxis (σ i) := by
      linarith [(hE i).1, (hF (σ i)).1]
    have hfactor : |E.semiaxis i ^ 2 - F.semiaxis (σ i) ^ 2| =
        |E.semiaxis i - F.semiaxis (σ i)| * (E.semiaxis i + F.semiaxis (σ i)) := by
      rw [sq_sub_sq, abs_mul, abs_of_pos (add_pos (E.semiaxis_pos i) (F.semiaxis_pos (σ i)))]
      ring
    have hsmall : |E.semiaxis i - F.semiaxis (σ i)| * (2 * a) ≤
        R * (L * M) ^ η * (E.volumeDistance F) ^ η := by
      calc
        _ ≤ |E.semiaxis i - F.semiaxis (σ i)| *
            (E.semiaxis i + F.semiaxis (σ i)) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        _ = _ := hfactor.symm
        _ ≤ _ := hroot i
    have h := (le_div_iff₀ (show 0 < 2 * a by positivity)).mpr hsmall
    simpa only [C, η, div_mul_eq_mul_div] using h

end EllipsoidVerification
