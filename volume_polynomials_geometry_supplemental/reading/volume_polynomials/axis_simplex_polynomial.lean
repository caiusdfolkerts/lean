module

public import VolumePolynomials.AxisSimplexVolume
public import VolumePolynomials.PrismFirstVariation
public import VolumePolynomials.RealizationContinuity
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The complete two-simplex volume formula

Axes are ordered increasingly, so the product in the coefficient of
`t^(n-i) s^i` is the product of the final `i` axes. This is exactly (A.2)
after reversing the coordinate order. All nonnegative axes are included.
-/

open Set MeasureTheory Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

def upperProduct {n : ℕ} (lam : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => n - i ≤ j.val), lam j

def orderedCoefficient {n : ℕ} (lam : Fin n → ℝ) (i : ℕ) : ℝ :=
  upperProduct lam i / ((n - i).factorial * i.factorial : ℕ)

def orderedValue {n : ℕ} (lam : Fin n → ℝ) (t s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), orderedCoefficient lam i * t ^ (n - i) * s ^ i

theorem upperProduct_top {n : ℕ} (lam : Fin n → ℝ) :
    upperProduct lam n = ∏ j, lam j := by
  first
  | simp [upperProduct]

theorem upperProduct_zero {n : ℕ} (lam : Fin n → ℝ) : upperProduct lam 0 = 1 := by
  first
  | have hempty : Finset.univ.filter (fun j : Fin n => n - 0 ≤ j.val) = ∅ := by
      first
      | apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have h := (Finset.mem_filter.mp hj).2
        omega
    simp only [upperProduct, hempty, Finset.prod_empty]

theorem upperProduct_tail {n i : ℕ} (lam : Fin (n + 1) → ℝ) (hi : i ≤ n) :
    upperProduct lam i = upperProduct (Fin.tail lam) i := by
  first
  | simp only [upperProduct, Finset.prod_filter, Fin.prod_univ_succ]
    have hzero : ¬n + 1 - i ≤ (0 : Fin (n + 1)).val := by simp only [Fin.val_zero]; omega
    rw [if_neg hzero, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    have htest : n + 1 - i ≤ j.succ.val ↔ n - i ≤ j.val := by
      first
      | simp only [Fin.val_succ]
        omega
    simp only [htest, Fin.tail_def]

theorem orderedCoefficient_succ {n i : ℕ} (lam : Fin (n + 1) → ℝ) (hi : i ≤ n) :
    orderedCoefficient lam i = orderedCoefficient (Fin.tail lam) i / (n - i + 1) := by
  first
  | have hsub : n + 1 - i = (n - i) + 1 := by omega
    simp only [orderedCoefficient, upperProduct_tail lam hi, hsub,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub hi, div_eq_mul_inv, mul_inv_rev]
    ring

theorem orderedCoefficient_top {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) :
    orderedCoefficient lam (n + 1) =
      lam 0 / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
  first
  | rw [orderedCoefficient, upperProduct_top, Fin.prod_univ_succ, axisBody_volume]
    rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => hlam i.succ))]
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.one_mul, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Fin.tail_def, div_eq_mul_inv, mul_inv_rev]
    ring

theorem orderedValue_zero (lam : Fin 0 → ℝ) (t s : ℝ) : orderedValue lam t s = 1 := by
  first
  | simp [orderedValue, orderedCoefficient, upperProduct_zero]

theorem integral_orderedValue_tail {n : ℕ} (lam : Fin (n + 1) → ℝ) (t s : ℝ) :
    (∫ u in 0..t, orderedValue (Fin.tail lam) u s) =
      ∑ i ∈ Finset.range (n + 1), orderedCoefficient lam i * t ^ (n + 1 - i) * s ^ i := by
  first
  | unfold orderedValue
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_pow]
      have hsub : n + 1 - i = (n - i) + 1 := by omega
      rw [hsub, orderedCoefficient_succ lam hin]
      simp only [zero_pow (Nat.succ_ne_zero (n - i)), sub_zero, Nat.cast_sub hin]
      ring
    · intro i _
      exact ((continuous_const.mul (continuous_id.pow (n - i))).mul continuous_const).intervalIntegrable _ _

theorem orderedValue_recurrence {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (t s : ℝ) :
    orderedValue lam t s =
      (∫ u in 0..t, orderedValue (Fin.tail lam) u s) +
        lam 0 * s ^ (n + 1) / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
  first
  | rw [integral_orderedValue_tail]
    unfold orderedValue
    rw [Finset.sum_range_succ]
    congr 1
    rw [orderedCoefficient_top hlam]
    simp only [Nat.sub_self, pow_zero, mul_one]
    ring

theorem volume_sum_positive {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmono : Monotone lam)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body n + s • axisBody lam) = orderedValue lam t s := by
  first
  | induction n generalizing t s with
    | zero =>
        have hbody : t • body 0 + s • axisBody lam = body 0 := by
          first
          | apply ConvexBody.ext
            ext x
            constructor
            · intro _
              simp [SimplexCoordinates.body, simplex]
            · intro _
              obtain ⟨y, hy⟩ := (t • body 0 + s • axisBody lam).nonempty
              simpa only [Subsingleton.elim y x] using hy
        rw [hbody, simplex_volume_zero, orderedValue_zero]
    | succ n ih =>
        have hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ := fun i => hmono (Fin.zero_le _)
        rw [volume_sum_recurrence hlam hmin ht hs, orderedValue_recurrence (fun i => (hlam i).le)]
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le ht
        intro u hu
        exact ih (fun i => hlam i.succ) (fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij))
          hu.1.le hs

theorem continuous_upperProduct (n i : ℕ) : Continuous (fun lam : Fin n → ℝ => upperProduct lam i) := by
  first
  | unfold upperProduct
    fun_prop

theorem continuous_orderedValue (n : ℕ) (t s : ℝ) :
    Continuous (fun lam : Fin n → ℝ => orderedValue lam t s) := by
  first
  | unfold orderedValue orderedCoefficient
    apply continuous_finsetSum
    intro i _
    exact (((continuous_upperProduct n i).div_const _).mul continuous_const).mul continuous_const

set_option maxHeartbeats 1000000 in
/-- Formula (A.2), including zero axis lengths. -/
theorem volume_sum {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hmono : Monotone lam)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body n + s • axisBody lam) = orderedValue lam t s := by
  first
  | let axes : ℝ → Fin n → ℝ := fun eps i => lam i + eps
    have hcaxes : Continuous axes := continuous_pi (fun i => continuous_const.add continuous_id)
    have hleft : Tendsto (fun eps : ℝ => bodyVolume (t • body n + s • axisBody (axes eps)))
        (𝓝[>] (0 : ℝ)) (𝓝 (bodyVolume (t • body n + s • axisBody lam))) := by
      first
      | have hK : Continuous (fun eps : ℝ => axisBody (axes eps)) :=
          (continuous_axisBody n).comp hcaxes
        have hsum : Continuous (fun eps : ℝ => t • body n + s • axisBody (axes eps)) :=
          continuous_const.fun_add (hK.fun_const_smul s)
        have hc : Continuous (fun eps : ℝ => bodyVolume (t • body n + s • axisBody (axes eps))) :=
          (continuous_bodyVolume n).comp hsum
        simpa only [axes, add_zero] using
          (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hright : Tendsto (fun eps : ℝ => orderedValue (axes eps) t s)
        (𝓝[>] (0 : ℝ)) (𝓝 (orderedValue lam t s)) := by
      first
      | simpa only [Function.comp_def, axes, add_zero] using
          (((continuous_orderedValue n t s).comp' hcaxes).continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun eps : ℝ => bodyVolume (t • body n + s • axisBody (axes eps)))
        =ᶠ[𝓝[>] (0 : ℝ)] fun eps => orderedValue (axes eps) t s := by
      first
      | filter_upwards [self_mem_nhdsWithin] with eps heps
        exact volume_sum_positive (fun i => add_pos_of_nonneg_of_pos (hlam i) heps)
          (fun i j hij => by
            change lam i + eps ≤ lam j + eps
            linarith [hmono hij]) ht hs
    exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

theorem orderedCoefficient_eq_choose {n i : ℕ} (lam : Fin n → ℝ) (hi : i ≤ n) :
    orderedCoefficient lam i =
      1 / (n.factorial : ℝ) * (n.choose i : ℝ) * upperProduct lam i := by
  first
  | have hchoose : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) =
        (n.factorial : ℝ) := by
      first
      | exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have h0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have h1 : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have h2 : ((n - i).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - i)
    unfold orderedCoefficient
    push_cast
    field_simp
    nlinarith [congrArg (fun q : ℝ => q * upperProduct lam i) hchoose]

theorem volume_sum_choose {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hmono : Monotone lam)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body n + s • axisBody lam) =
      1 / (n.factorial : ℝ) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * upperProduct lam i * t ^ (n - i) * s ^ i := by
  first
  | rw [volume_sum hlam hmono ht hs, orderedValue, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [orderedCoefficient_eq_choose lam (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    ring

end VolumePolynomials.AxisSimplex
