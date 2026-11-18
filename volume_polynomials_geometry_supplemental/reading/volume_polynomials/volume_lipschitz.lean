module
public import VolumePolynomials.VolumePolynomialExistence
public import VolumePolynomials.RealizationCone
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# An explicit volume modulus on a bounded box

Coefficient nonnegativity bounds the volume added by a small Minkowski summand.
Hausdorff distance in `Space d` is the supremum norm, so its unit ball is a cube.
Combining these facts gives a rational uniform modulus for the effective nets.
This follows polynomiality; the qualitative continuity used to prove
polynomiality was established independently by dominated convergence.
-/

open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

def coordinateCube (d : ℕ) : Body d where
  carrier := Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
  convex' := convex_Icc _ _
  isCompact' := isCompact_Icc
  nonempty' := ⟨0, ⟨fun _ => neg_nonpos.mpr zero_le_one, fun _ => zero_le_one⟩⟩

/-- Every nonconstant power of a number in `[0,1]` is bounded by that number. -/
theorem bodyVolume_add_smul_sub_le {d : ℕ} (K L : Body d) {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    bodyVolume (K + h • L) - bodyVolume K ≤ h * bodyVolume (K + L) := by
  first
  | obtain ⟨c, hc, hr⟩ := exists_nonnegative_volume_polynomial ![K, L]
    have heval (s : ℝ) (hs : 0 ≤ s) :
        (∑ α : MultiIndex 2 d, c α * s ^ (α.1 1 : ℕ)) = bodyVolume (K + s • L) := by
      first
      | have hnonneg : ∀ i : Fin 2, 0 ≤ (![1, s] : Fin 2 → ℝ) i := by
          intro i
          fin_cases i <;> simp [hs]
        simpa [evaluate, volumeFunction, weightedSum, Fin.sum_univ_two,
          Fin.prod_univ_two] using hr ![1, s] hnonneg
    have heval0 : (∑ α : MultiIndex 2 d, c α * (0 : ℝ) ^ (α.1 1 : ℕ)) = bodyVolume K := by
      first
      | simpa only [body_zero_smul, add_zero] using heval 0 le_rfl
    have heval1 : (∑ α : MultiIndex 2 d, c α) = bodyVolume (K + L) := by
      first
      | simpa only [one_pow, mul_one, one_smul] using heval 1 zero_le_one
    rw [← heval h hh0, ← heval0, ← heval1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    by_cases hk : (α.1 1 : ℕ) = 0
    · simpa only [hk, pow_zero, mul_one, sub_self] using mul_nonneg hh0 (hc α)
    · simp only [zero_pow hk, mul_zero, sub_zero]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (pow_le_of_le_one hh0 hh1 hk) (hc α)

/-- Hausdorff control gives literal Minkowski containment in the coordinate cube. -/
theorem body_le_add_coordinateCube_of_dist_le {d : ℕ} (K L : Body d)
    {h : ℝ} (hh : 0 ≤ h) (hKL : dist K L ≤ h) : K ≤ L + h • coordinateCube d := by
  first
  | rcases hh.eq_or_lt with heq | hpos
    · have hz : h = 0 := heq.symm
      rw [hz] at hKL ⊢
      have hsame : K = L := dist_le_zero.mp hKL
      rw [hsame, body_zero_smul, add_zero]
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
      have hnorm : ‖x - y‖ ≤ h := by
        first
        | rw [← dist_eq_norm, ← hxy]
          exact (infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top).trans hKL
      let u : Space d := h⁻¹ • (x - y)
      have hu : u ∈ coordinateCube d := by
        first
        | have habs : ∀ i, |u i| ≤ 1 := by
            intro i
            have hi : |(x - y) i| ≤ h := by
              calc
                |(x - y) i| = ‖(x - y) i‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
                _ ≤ h := hnorm
            change |h⁻¹ * (x - y) i| ≤ 1
            rw [abs_mul, abs_inv, abs_of_pos hpos]
            calc
              h⁻¹ * |(x - y) i| ≤ h⁻¹ * h :=
                mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hpos.le)
              _ = 1 := inv_mul_cancel₀ hpos.ne'
          exact ⟨fun i => (abs_le.mp (habs i)).1, fun i => (abs_le.mp (habs i)).2⟩
      have hscaled : h • u = x - y := by
        first
        | simp only [u, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      exact Set.mem_add.mpr ⟨y, hy, x - y, ⟨u, hu, hscaled⟩, by abel⟩

theorem bodyVolume_add_coordinateCube_le {d : ℕ} (K : Body d) {R : ℝ}
    (hR : 0 ≤ R) (hK : (K : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R)) :
    bodyVolume (K + coordinateCube d) ≤ (2 * R + 2) ^ d := by
  first
  | have hsub : ((K + coordinateCube d : Body d) : Set (Space d)) ⊆
        Icc (fun _ => -(R + 1)) (fun _ => R + 1) := by
      first
      | rintro _ ⟨x, hx, y, hy, rfl⟩
        have hx' := hK hx
        change y ∈ Icc (fun _ : Fin d => (-1 : ℝ)) (fun _ => (1 : ℝ)) at hy
        constructor
        · intro i
          change -(R + 1) ≤ x i + y i
          linarith [hx'.1 i, hy.1 i]
        · intro i
          change x i + y i ≤ R + 1
          linarith [hx'.2 i, hy.2 i]
    have hbound := measureReal_mono hsub
      (show volume (Icc (fun _ : Fin d => -(R + 1)) (fun _ => R + 1)) ≠ ⊤ from
        isCompact_Icc.measure_lt_top.ne)
    have hbox : volume.real (Icc (fun _ : Fin d => -(R + 1)) (fun _ => R + 1)) =
        (2 * R + 2) ^ d := by
      first
      | rw [measureReal_def, Real.volume_Icc_pi_toReal
          (show (fun _ : Fin d => -(R + 1)) ≤ (fun _ => R + 1) from
            fun _ => by linarith)]
        simp only [show R + 1 - -(R + 1) = 2 * R + 2 by ring,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hbound.trans_eq hbox

/-- Explicit uniform continuity of volume on all convex bodies in the box,
including arbitrarily thin and lower-dimensional ones. -/
theorem abs_bodyVolume_sub_le_of_dist_le {d : ℕ} (K L : Body d) {R h : ℝ}
    (hR : 0 ≤ R) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hK : (K : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R))
    (hL : (L : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R))
    (hKL : dist K L ≤ h) :
    |bodyVolume K - bodyVolume L| ≤ h * (2 * R + 2) ^ d := by
  first
  | have hforward : bodyVolume K - bodyVolume L ≤ h * (2 * R + 2) ^ d := by
      first
      | calc
          _ ≤ bodyVolume (L + h • coordinateCube d) - bodyVolume L :=
            sub_le_sub_right (bodyVolume_mono (body_le_add_coordinateCube_of_dist_le K L hh0 hKL)) _
          _ ≤ h * bodyVolume (L + coordinateCube d) := bodyVolume_add_smul_sub_le L _ hh0 hh1
          _ ≤ h * (2 * R + 2) ^ d :=
            mul_le_mul_of_nonneg_left (bodyVolume_add_coordinateCube_le L hR hL) hh0
    have hreverse : bodyVolume L - bodyVolume K ≤ h * (2 * R + 2) ^ d := by
      first
      | calc
          _ ≤ bodyVolume (K + h • coordinateCube d) - bodyVolume K :=
            sub_le_sub_right (bodyVolume_mono (body_le_add_coordinateCube_of_dist_le L K hh0
              (by rwa [dist_comm]))) _
          _ ≤ h * bodyVolume (K + coordinateCube d) := bodyVolume_add_smul_sub_le K _ hh0 hh1
          _ ≤ h * (2 * R + 2) ^ d :=
            mul_le_mul_of_nonneg_left (bodyVolume_add_coordinateCube_le K hR hK) hh0
    exact abs_le.mpr ⟨by linarith, hforward⟩

end VolumePolynomials
