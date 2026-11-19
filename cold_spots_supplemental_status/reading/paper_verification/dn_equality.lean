module
public import PaperVerification.DnMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators
open MeasureTheory

lemma prod_eq_const_forces_factors {n : ℕ} (f : Fin n → ℝ) {c : ℝ}
    (hc : 0 < c) (hbound : ∀ i, c ≤ f i) (heq : (∏ i, f i) = c ^ n) :
    ∀ i, f i = c := by
  intro i
  by_contra hne
  have hlt : c < f i := lt_of_le_of_ne (hbound i) (Ne.symm hne)
  have hp := Finset.prod_lt_prod₀ (s := Finset.univ) (f := fun _ : Fin n ↦ c)
    (g := f) (fun _ _ ↦ hc) (fun i _ ↦ hbound i) ⟨i, Finset.mem_univ i, hlt⟩
  have hp' : c ^ n < c ^ n := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, heq] using hp
  exact (lt_irrefl (c ^ n)) hp'

lemma half_interval_two_mul_integer_iff {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (∃ z : ℤ, 2 * t = (z : ℝ)) ↔ t = 0 ∨ t = 1 / 2 := by
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ z by linarith)
    have hz1 : z ≤ (1 : ℤ) := by exact_mod_cast (show (z : ℝ) ≤ 1 by linarith)
    have hcases : z = 0 ∨ z = 1 := by omega
    rcases hcases with rfl | rfl
    · left
      norm_num at hz
      linarith
    · right
      norm_num at hz
      linarith
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩

theorem folded_endpoints_of_product_equalities {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ)
    (hA : foldedAProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2))
    (hC : foldedCProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2)) :
    ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2 := by
  let c := gaussian α 0 * gaussian α (1 / 2)
  have hc : 0 < c := mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))
  have hprod : (∏ i, gaussian α (foldedRadius x i) *
      gaussian α (foldedRadius x i - 1 / 2)) = c ^ n := by
    rw [Finset.prod_mul_distrib]
    change foldedAProduct α x * foldedCProduct α x = _
    rw [hA, hC]
    change c ^ ((n : ℝ) / 2) * c ^ ((n : ℝ) / 2) = c ^ n
    rw [← Real.rpow_add hc, show (n : ℝ) / 2 + (n : ℝ) / 2 = n by ring,
      Real.rpow_natCast]
  have hpoint := prod_eq_const_forces_factors _ hc
    (fun i ↦ gaussian_shift_product_min hα (foldedRadius x i)) hprod
  intro i
  apply (half_interval_two_mul_integer_iff (foldedRadius_nonneg x i)
    (foldedRadius_le_half x i)).mp
  exact (gaussian_shift_product_min_iff hα (foldedRadius x i)).mp (hpoint i)

lemma log_foldedAProduct_of_endpoints {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) (hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) :
    Real.log (foldedAProduct α x) = (n : ℝ) * Real.log (gaussian α 0) +
      2 * (∑ i, foldedRadius x i) *
        (Real.log (gaussian α (1 / 2)) - Real.log (gaussian α 0)) := by
  unfold foldedAProduct
  rw [Real.log_prod (fun i _ ↦ (gaussian_pos hα _).ne')]
  have hi (i : Fin n) : Real.log (gaussian α (foldedRadius x i)) =
      Real.log (gaussian α 0) + 2 * foldedRadius x i *
        (Real.log (gaussian α (1 / 2)) - Real.log (gaussian α 0)) := by
    rcases hx i with h | h <;> rw [h] <;> ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum]

lemma log_foldedCProduct_of_endpoints {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) (hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) :
    Real.log (foldedCProduct α x) = (n : ℝ) * Real.log (gaussian α (1 / 2)) +
      2 * (∑ i, foldedRadius x i) *
        (Real.log (gaussian α 0) - Real.log (gaussian α (1 / 2))) := by
  unfold foldedCProduct
  rw [Real.log_prod (fun i _ ↦ (gaussian_pos hα _).ne')]
  have hi (i : Fin n) : Real.log (gaussian α (foldedRadius x i - 1 / 2)) =
      Real.log (gaussian α (1 / 2)) + 2 * foldedRadius x i *
        (Real.log (gaussian α 0) - Real.log (gaussian α (1 / 2))) := by
    rcases hx i with h | h
    · rw [h, zero_sub, gaussian_even]
      ring
    · rw [h, sub_self]
      ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum]

theorem balanced_of_folded_product_equalities {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ)
    (hA : foldedAProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2))
    (hC : foldedCProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2)) :
    BalancedHalfGrid x := by
  have hx := folded_endpoints_of_product_equalities hα x hA hC
  refine ⟨hx, ?_⟩
  have hlog := congrArg Real.log (hA.trans hC.symm)
  rw [log_foldedAProduct_of_endpoints hα x hx,
    log_foldedCProduct_of_endpoints hα x hx] at hlog
  have hlt : Real.log (gaussian α (1 / 2)) < Real.log (gaussian α 0) :=
    Real.log_lt_log (gaussian_pos hα _) (gaussian_half_lt_zero hα)
  have hp : ((n : ℝ) - 4 * ∑ i, foldedRadius x i) *
      (Real.log (gaussian α 0) - Real.log (gaussian α (1 / 2))) = 0 := by
    nlinarith only [hlog]
  have hzero := (mul_eq_zero.mp hp).resolve_right (sub_pos.mpr hlt).ne'
  linarith

lemma foldedProducts_of_balanced {n : ℕ} {α : ℝ} (hα : 0 < α)
    {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    foldedAProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ∧
    foldedCProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) := by
  have hac := mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))
  have hloga := log_foldedAProduct_of_endpoints hα x hx.1
  have hlogc := log_foldedCProduct_of_endpoints hα x hx.1
  rw [hx.2] at hloga hlogc
  constructor
  · rw [← Real.exp_log (foldedAProduct_pos hα x), hloga, Real.rpow_def_of_pos hac,
      Real.log_mul (gaussian_pos hα 0).ne' (gaussian_pos hα (1 / 2)).ne']
    congr 1
    ring
  · rw [← Real.exp_log (foldedCProduct_pos hα x), hlogc, Real.rpow_def_of_pos hac,
      Real.log_mul (gaussian_pos hα 0).ne' (gaussian_pos hα (1 / 2)).ne']
    congr 1
    ring

lemma balanced_has_both_endpoints {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : BalancedHalfGrid x) :
    (∃ i, foldedRadius x i = 0) ∧ ∃ i, foldedRadius x i = 1 / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · by_contra h
    push_neg at h
    have hall : ∀ i, foldedRadius x i = 1 / 2 := fun i ↦ (hx.1 i).resolve_left (h i)
    have hs := hx.2
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    linarith
  · by_contra h
    push_neg at h
    have hall : ∀ i, foldedRadius x i = 0 := fun i ↦ (hx.1 i).resolve_right (h i)
    have hs := hx.2
    simp only [hall, Finset.sum_const_zero] at hs
    linarith

theorem dPlusGaussian_of_balanced {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) := by
  classical
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := balanced_has_both_endpoints hn hx
  have hB : (∏ k, alternatingGaussian α (x k)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply abs_eq_zero.mp
    rw [alternatingGaussian_fold hα]
    change alternatingGaussian α (foldedRadius x j) = 0
    rw [hj, alternatingGaussian_half]
  have hD : (∏ k, alternatingGaussian α (x k - 1 / 2)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply abs_eq_zero.mp
    rw [alternatingGaussian_halfshift_fold hα]
    change alternatingGaussian α (foldedRadius x i - 1 / 2) = 0
    rw [hi, zero_sub, alternatingGaussian_even, alternatingGaussian_half]
  obtain ⟨hA, hC⟩ := foldedProducts_of_balanced hα hx
  rw [dPlusGaussian_eq_product hα, hB, hD]
  have hpA : (∏ i, gaussian α (x i)) = foldedAProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_fold α (x i)
  have hpC : (∏ i, gaussian α (x i - 1 / 2)) = foldedCProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_halfshift_fold α (x i)
  rw [hpA, hpC, hA, hC]
  ring

/-- Exact equivalence to the geometric deep-hole locus in every even n>8,
conditional only on the displayed theta measure theorem being supplied. -/
theorem coldSpot_dPlus_iff_deepHole_of_theta {n : ℕ} (hn : 8 < n) (heven : Even n)
    {α : ℝ} (hα : 0 < α)
    (hbase : ∀ μ : ProbabilityMeasure HalfInterval,
      2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaMomentNumerator hα μ)
    (x : Fin n → ℝ) : IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x := by
  have hn0 : 0 < n := by omega
  rw [isDeepHole_dPlus_iff_balanced hn heven x]
  constructor
  · intro hcold
    obtain ⟨y, hy⟩ := exists_balancedHalfGrid heven
    have hxy := hcold y
    rw [setGaussian_dPlus_eq hn0 hα, setGaussian_dPlus_eq hn0 hα,
      dPlusGaussian_of_balanced hn0 hα hy] at hxy
    have heq := le_antisymm hxy (dPlusGaussian_lower_of_theta hn.le hα x
      (hbase (foldedEmpirical hn0 x)))
    obtain ⟨_, _, hA, hC⟩ := dPlusGaussian_equality_products_of_theta hn hα x
      (hbase (foldedEmpirical hn0 x)) heq
    exact balanced_of_folded_product_equalities hα x hA hC
  · intro hx y
    rw [setGaussian_dPlus_eq hn0 hα, setGaussian_dPlus_eq hn0 hα,
      dPlusGaussian_of_balanced hn0 hα hx]
    exact dPlusGaussian_lower_of_theta hn.le hα y (hbase (foldedEmpirical hn0 y))

end PaperVerification.ColdSpots
