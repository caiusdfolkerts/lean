module

public import Unimodular
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Unimodular.IntegerGenericHeights

/-- Finitely many nonzero integral linear forms can be avoided by an actual
integer vector. The proof uses a single integer geometric progression. -/
theorem exists_avoiding {E K : Type*} [Fintype E] [Fintype K]
    (L : K → (E → ℤ) →ₗ[ℤ] ℤ) (hL : ∀ k, L k ≠ 0) :
    ∃ w : E → ℤ, ∀ k, L k w ≠ 0 := by
  classical
  let e := Fintype.equivFin E
  let a : K → Fin (Fintype.card E) → ℤ :=
    fun k i => L k (Pi.single (e.symm i) 1)
  have hdecomp (w : E → ℤ) :
      w = ∑ i : Fin (Fintype.card E), w (e.symm i) • Pi.single (e.symm i) (1 : ℤ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (e j)]
    · simp
    · intro i hi hij
      have he : e.symm i ≠ j := by
        intro h
        apply hij
        simpa using congrArg e h
      simp [he, Ne.symm he]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hne (k : K) : ∃ i, a k i ≠ 0 := by
    by_contra! h
    apply hL k
    apply LinearMap.ext
    intro w
    change L k w = 0
    rw [hdecomp w, map_sum]
    simp only [map_smul, smul_eq_mul]
    exact Finset.sum_eq_zero (fun i hi => by rw [show L k (Pi.single (e.symm i) 1) = 0 from h i, mul_zero])
  obtain ⟨t, ht, havoid⟩ := GenericWeights.exists_geometric_progression a hne
  let w : E → ℤ := fun j => t ^ (e j).val
  refine ⟨w, fun k => ?_⟩
  have heval : L k w = ∑ i, a k i * t ^ i.val := by
    rw [hdecomp w, map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp [w, a, mul_comm]
  rw [heval]
  exact havoid k

/-- An integral perturbation of a positive constant vector can avoid every
nonzero wall, preserving the signs of all nonzero constant wall values. -/
theorem exists_positive_regular_height {E K : Type*} [Fintype E] [Fintype K]
    (L : K → (E → ℤ) →ₗ[ℤ] ℤ) (hL : ∀ k, L k ≠ 0) :
    ∃ h : E → ℤ, (∀ e, 0 < h e) ∧
      (∀ k, L k h ≠ 0) ∧
      (∀ k, 0 < L k (fun _ => 1) → 0 < L k h) := by
  classical
  obtain ⟨w, hw⟩ := exists_avoiding L hL
  let N : ℤ := 1 + ∑ k, |L k w| + ∑ e, |w e|
  have hsumK : 0 ≤ ∑ k, |L k w| := Finset.sum_nonneg (fun k hk => abs_nonneg _)
  have hsumE : 0 ≤ ∑ e, |w e| := Finset.sum_nonneg (fun e he => abs_nonneg _)
  have hN : 0 < N := by dsimp [N]; omega
  have hKw (k : K) : |L k w| < N := by
    have hs := Finset.single_le_sum (fun j hj => abs_nonneg (L j w)) (Finset.mem_univ k)
    dsimp [N]
    omega
  have hEw (e : E) : |w e| < N := by
    have hs := Finset.single_le_sum (fun j hj => abs_nonneg (w j)) (Finset.mem_univ e)
    dsimp [N]
    omega
  let h : E → ℤ := fun e => N + w e
  have heq (k : K) : L k h = N * L k (fun _ => 1) + L k w := by
    have hh : h = N • (fun _ : E => (1 : ℤ)) + w := by ext e; simp [h]
    rw [hh, map_add, map_smul, smul_eq_mul]
  have hpositive (k : K) (ha : 0 < L k (fun _ => 1)) : 0 < L k h := by
    rw [heq]
    have ha1 : 1 ≤ L k (fun _ => 1) := ha
    have hmul : N ≤ N * L k (fun _ => 1) := by
      simpa using mul_le_mul_of_nonneg_left ha1 hN.le
    have hb := neg_le_abs (L k w)
    have hk := hKw k
    omega
  refine ⟨h, ?_, ?_, hpositive⟩
  · intro e
    have hb := neg_le_abs (w e)
    have he := hEw e
    dsimp [h]
    omega
  · intro k
    by_cases ha : L k (fun _ => 1) = 0
    · rw [heq, ha, mul_zero, zero_add]
      exact hw k
    · rcases lt_or_gt_of_ne ha with hneg | hpos
      · rw [heq]
        have ha1 : L k (fun _ => 1) ≤ -1 := by omega
        have hmul : N * L k (fun _ => 1) ≤ -N := by
          simpa using mul_le_mul_of_nonneg_left ha1 hN.le
        have hb := le_abs_self (L k w)
        have hk := hKw k
        omega
      · exact (hpositive k hpos).ne'

end Unimodular.IntegerGenericHeights

#print axioms Unimodular.IntegerGenericHeights.exists_avoiding
#print axioms Unimodular.IntegerGenericHeights.exists_positive_regular_height
#check Unimodular.IntegerGenericHeights.exists_positive_regular_height
