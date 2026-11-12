module

public import ToricPower.OrthantCircuits
public import ToricPower.ZonotopeSeparation

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

def orthantExcess (sign a : Fin s → ℤ) : (Fin s → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, ((a i : ℝ) + if sign i = 1 then 0 else 1) • LinearMap.proj i

theorem orthantExcess_eq_support (sign a : Fin s → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) (x : Fin s → ℝ)
    (hx : ∀ i, 0 ≤ (sign i : ℝ) * x i) :
    orthantExcess sign a x =
      (∑ i, x i * (a i : ℝ)) - ∑ i, max (-x i) 0 := by
  simp only [orthantExcess, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases hsign i with hi | hi
  · have hxi : 0 ≤ x i := by simpa [hi] using hx i
    simp [hi, max_eq_right (neg_nonpos.mpr hxi), mul_comm]
  · have hxi : x i ≤ 0 := by simpa [hi] using hx i
    simp only [hi, Int.reduceNeg, Int.reduceEq, if_false, max_eq_left (by linarith : 0 ≤ -x i)]
    ring

theorem exists_circuit_separating_zonotope
    (A : Matrix (Fin s) (Fin n) ℤ) (a : Fin s → ℤ)
    (ha : realDivisorClass A a ∉ realZonotope A) :
    ∃ h : Fin s → ℤ, IsCircuit A h ∧ cubeSupport h < ∑ i, h i * a i := by
  obtain ⟨h, hker, hviol⟩ := exists_real_relation_separating_zonotope A a ha
  let sign : Fin s → ℤ := fun i => if 0 ≤ h i then 1 else -1
  have hsign : ∀ i, sign i = 1 ∨ sign i = -1 := by
    intro i
    dsimp [sign]
    split_ifs <;> simp
  have hsignabs (i : Fin s) : (sign i : ℝ) * h i = |h i| := by
    by_cases hi : 0 ≤ h i
    · simp [sign, hi, abs_of_nonneg hi]
    · simp [sign, hi, abs_of_neg (lt_of_not_ge hi)]
  have hne : h ≠ 0 := by
    intro hz
    simp [hz] at hviol
  obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hne
  let N : ℝ := ∑ i, |h i|
  have hN : 0 < N :=
    lt_of_lt_of_le (abs_pos.mpr hi)
      (Finset.single_le_sum (fun j _ => abs_nonneg (h j)) (Finset.mem_univ i))
  let x : Fin s → ℝ := N⁻¹ • h
  have hx : x ∈ orthantKernel A sign := by
    rw [mem_orthantKernel_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro j
      change (∑ i, (A i j : ℝ) * (N⁻¹ * h i)) = 0
      calc
        _ = N⁻¹ * ∑ i, (A i j : ℝ) * h i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [hker j, mul_zero]
    · intro i
      change 0 ≤ (sign i : ℝ) * (N⁻¹ * h i)
      have heq : (sign i : ℝ) * (N⁻¹ * h i) = N⁻¹ * |h i| := by
        rw [← hsignabs i]
        ring
      rw [heq]
      exact mul_nonneg (inv_pos.mpr hN).le (abs_nonneg _)
    · change (∑ i, (sign i : ℝ) * (N⁻¹ * h i)) = 1
      calc
        _ = N⁻¹ * ∑ i, |h i| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [← hsignabs i]
          ring
        _ = 1 := inv_mul_cancel₀ hN.ne'
  have hLh : 0 < orthantExcess sign a h := by
    rw [orthantExcess_eq_support sign a hsign h
      (fun i => by rw [hsignabs]; exact abs_nonneg _)]
    linarith
  have hLx : 0 < orthantExcess sign a x := by
    change 0 < orthantExcess sign a (N⁻¹ • h)
    rw [map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hN) hLh
  have hvertex : ∃ q ∈ (orthantKernel A sign).extremePoints ℝ,
      0 < orthantExcess sign a q := by
    by_contra hn
    push_neg at hn
    have hconv : Convex ℝ {v : Fin s → ℝ | orthantExcess sign a v ≤ 0} :=
      (convex_Iic (0 : ℝ)).linear_preimage (orthantExcess sign a)
    have hsub : (orthantKernel A sign).extremePoints ℝ ⊆
        {v : Fin s → ℝ | orthantExcess sign a v ≤ 0} := hn
    have hxHull : x ∈ convexHull ℝ ((orthantKernel A sign).extremePoints ℝ) := by
      have hHull : orthantKernel A sign =
          convexHull ℝ ((orthantKernel A sign).extremePoints ℝ) :=
        NormalProjective.compact_halfspace_eq_convexHull_extremePoints
          (matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)))
          (fun i => (orthantRhs i : ℝ)) (isCompact_orthantKernel A sign hsign)
      rw [← hHull]
      exact hx
    exact (not_le_of_gt hLx) (convexHull_min hsub hconv hxHull)
  obtain ⟨q, hq, hLq⟩ := hvertex
  obtain ⟨k, hk, c, hc, hqeq⟩ :=
    primitive_circuit_of_orthant_extreme A sign hsign hq
  have hksign (i : Fin s) : 0 ≤ (sign i : ℝ) * (k i : ℝ) := by
    have hqi := ((mem_orthantKernel_iff A sign q).mp hq.1).2.1 i
    rw [hqeq] at hqi
    change 0 ≤ (sign i : ℝ) * (c * (k i : ℝ)) at hqi
    have heq : (sign i : ℝ) * (c * (k i : ℝ)) =
        c * ((sign i : ℝ) * (k i : ℝ)) := by ring
    rw [heq] at hqi
    exact (mul_nonneg_iff_of_pos_left hc).mp hqi
  rw [hqeq, map_smul, smul_eq_mul] at hLq
  have hLk : 0 < orthantExcess sign a (fun i => (k i : ℝ)) :=
    (mul_pos_iff_of_pos_left hc).mp hLq
  rw [orthantExcess_eq_support sign a hsign _ hksign] at hLk
  refine ⟨k, hk, ?_⟩
  have hh : (∑ i, max (-(k i : ℝ)) 0) < ∑ i, (k i : ℝ) * (a i : ℝ) := by
    linarith
  exact_mod_cast hh

theorem rayRelation_dot_realRayMap (A : Matrix (Fin s) (Fin n) ℤ)
    (h : Fin s → ℤ) (hh : h ∈ rayRelations A) (x : Fin n → ℝ) :
    ∑ i, (h i : ℝ) * realRayMap A x i = 0 := by
  have hker (j : Fin n) : ∑ i, (A i j : ℝ) * (h i : ℝ) = 0 := by
    exact_mod_cast ((mem_rayRelations A h).mp hh j)
  change (∑ i, (h i : ℝ) * ∑ j, (A i j : ℝ) * x j) = 0
  calc
    _ = ∑ j, (∑ i, (A i j : ℝ) * (h i : ℝ)) * x j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp [hker]

theorem rayRelation_zonotope_bound (A : Matrix (Fin s) (Fin n) ℤ)
    (a : Fin s → ℤ) (ha : realDivisorClass A a ∈ realZonotope A)
    (h : Fin s → ℤ) (hh : h ∈ rayRelations A) :
    (∑ i, h i * a i) ≤ cubeSupport h := by
  obtain ⟨x, hx⟩ := (realDivisorClass_mem_zonotope_iff A a).mp ha
  have hzero := rayRelation_dot_realRayMap A h hh x
  have hbound : (∑ i, (h i : ℝ) * ((a i : ℝ) - realRayMap A x i)) ≤
      ∑ i, max (-(h i : ℝ)) 0 := by
    apply Finset.sum_le_sum
    intro i _
    have hlo := (hx i).1
    have hup := (hx i).2
    by_cases hi : 0 ≤ (h i : ℝ)
    · have hmul := mul_nonpos_of_nonneg_of_nonpos hi hup
      exact hmul.trans (le_max_right _ _)
    · have hineg : (h i : ℝ) < 0 := lt_of_not_ge hi
      have hmul := mul_le_mul_of_nonpos_left hlo hineg.le
      calc
        _ ≤ -(h i : ℝ) := by nlinarith [hmul]
        _ ≤ max (-(h i : ℝ)) 0 := le_max_left _ _
  simp only [mul_sub, Finset.sum_sub_distrib, hzero, sub_zero] at hbound
  change (∑ i, h i * a i) ≤ ∑ i, max (-h i) 0
  exact_mod_cast hbound

/-- The exact finite primitive-circuit halfspace description of the projected cube. -/
theorem realDivisorClass_mem_zonotope_iff_circuits
    (A : Matrix (Fin s) (Fin n) ℤ) (a : Fin s → ℤ) :
    realDivisorClass A a ∈ realZonotope A ↔
      ∀ h ∈ circuits A, (∑ i, h i * a i) ≤ cubeSupport h := by
  constructor
  · intro ha h hh
    exact rayRelation_zonotope_bound A a ha h ((mem_circuits A h).mp hh).2.1
  · intro hh
    by_contra ha
    obtain ⟨h, hc, hviol⟩ := exists_circuit_separating_zonotope A a ha
    exact (not_le_of_gt hviol) (hh h ((mem_circuits A h).mpr hc))

end ToricPower

