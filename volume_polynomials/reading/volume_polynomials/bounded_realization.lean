module
public import VolumePolynomials.ExplicitNormalization
public import VolumePolynomials.RealizationContinuity

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# An explicit box for unnormalized realizations

A bound on the sum of coefficients yields a bound on all realizing bodies
after a volume-preserving normalization and a common dilation. This permits
the rational reconstruction procedure to work with the original coefficients;
it need not decide whether their total is zero or compute its reciprocal.
The proof itself treats the zero case separately.
-/

open Set MeasureTheory Finset
open scoped Pointwise BigOperators

namespace VolumePolynomials

theorem zero_mem_boundedVolumeLocus_box (n d : ℕ) (hd : 0 < d)
    {R : ℝ} (hR : 0 ≤ R) :
    (0 : Coefficients n d) ∈ boundedVolumeLocus n d
      (Icc (fun _ => -R) (fun _ => R)) := by
  first
  | letI : NeZero d := ⟨hd.ne'⟩
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i
      constructor
      · change (0 : Space d) ∈ ({0} : Set (Space d))
        exact Set.mem_singleton 0
      · intro x hx
        change x ∈ ({0} : Set (Space d)) at hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact ⟨fun _ => neg_nonpos.mpr hR, fun _ => hR⟩
    · intro t _
      simp [evaluate, volumeFunction, weightedSum, bodyVolume, Measure.real]
      change 0 = (volume {(0 : Space d)}).toReal
      simp

/-- Every realizable coefficient vector with bounded total admits an actual
tuple in a specified box, including the zero coefficient vector. -/
theorem bounded_realization_of_sum_le {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} (hc : c ∈ VolumeLocus n d)
    {B : ℝ} (hB : 0 ≤ B) (hsB : (∑ α, c α) ≤ B) :
    c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -((d : ℝ) * (B + 1))) (fun _ => (d : ℝ) * (B + 1))) := by
  first
  | obtain ⟨K, hK⟩ := hc
    let s : ℝ := ∑ α, c α
    have hs0 : 0 ≤ s := hK.sum_coefficients_nonneg
    have hR : 0 ≤ (d : ℝ) * (B + 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    by_cases hs : s = 0
    · have hc0 : c = 0 := hK.eq_zero_of_sum_eq_zero hs
      rw [hc0]
      exact zero_mem_boundedVolumeLocus_box n d hd hR
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hmem : s⁻¹ • c ∈ VolumeLocus n d :=
        smul_mem_volumeLocus hd ⟨K, hK⟩ (inv_nonneg.mpr hs0)
      obtain ⟨N, hN⟩ := hmem
      have hsum : ∑ α, (s⁻¹ • c) α = 1 := by
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        exact inv_mul_cancel₀ hs
      have hvol : bodyVolume (∑ i, N i) = 1 := hN.sum_coefficients.symm.trans hsum
      obtain ⟨g, p, hg, hp, hzero, hbox⟩ := explicit_normalization hd N hvol
      let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (N i))
      have hL : Realizes L (s⁻¹ • c) :=
        (hN.translate (fun i => -p i)).map_of_abs_det_one g hg
      have hLbox : ∀ i, (L i : Set (Space d)) ⊆
          Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ)) := by
        intro i x hx
        exact hbox (body_le_sum_of_zero_mem L hzero i hx)
      let r : ℝ := s ^ ((d : ℝ)⁻¹)
      have hr0 : 0 ≤ r := Real.rpow_nonneg hs0 _
      have hrpow : r ^ d = s := Real.rpow_inv_natCast_pow hs0 hd.ne'
      have hrB : r ≤ B + 1 := by
        apply (pow_le_pow_iff_left₀ hr0 (by linarith : 0 ≤ B + 1) hd.ne').mp
        rw [hrpow]
        exact hsB.trans ((le_add_of_nonneg_right zero_le_one).trans
          (le_self_pow₀ (by linarith : 1 ≤ B + 1) hd.ne'))
      have hreal : Realizes (fun i => r • L i) c := by
        have h := hL.dilate hr0
        simpa only [hrpow, smul_smul, mul_inv_cancel₀ hs, one_smul] using h
      refine ⟨fun i => r • L i, ?_, hreal⟩
      intro i
      constructor
      · exact ⟨0, hzero i, smul_zero r⟩
      · rintro x ⟨y, hy, rfl⟩
        have hybox := hLbox i hy
        have habs (j : Fin d) : |r * y j| ≤ (d : ℝ) * (B + 1) := by
          rw [abs_mul, abs_of_nonneg hr0]
          have hcoord : |y j| ≤ d := abs_le.mpr ⟨hybox.1 j, hybox.2 j⟩
          calc
            r * |y j| ≤ r * (d : ℝ) := mul_le_mul_of_nonneg_left hcoord hr0
            _ ≤ (B + 1) * (d : ℝ) := mul_le_mul_of_nonneg_right hrB (Nat.cast_nonneg _)
            _ = (d : ℝ) * (B + 1) := mul_comm _ _
        exact ⟨fun j => (abs_le.mp (habs j)).1, fun j => (abs_le.mp (habs j)).2⟩

theorem bounded_realization_of_sum_le_of_radius_le {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} (hc : c ∈ VolumeLocus n d)
    {B R : ℝ} (hB : 0 ≤ B) (hsB : (∑ α, c α) ≤ B)
    (hR : (d : ℝ) * (B + 1) ≤ R) :
    c ∈ boundedVolumeLocus n d (Icc (fun _ => -R) (fun _ => R)) := by
  first
  | obtain ⟨K, hK, hreal⟩ := bounded_realization_of_sum_le hd hc hB hsB
    refine ⟨K, ?_, hreal⟩
    intro i
    refine ⟨(hK i).1, ?_⟩
    intro x hx
    have h := (hK i).2 hx
    exact ⟨fun j => (neg_le_neg hR).trans (h.1 j), fun j => (h.2 j).trans hR⟩

end VolumePolynomials
