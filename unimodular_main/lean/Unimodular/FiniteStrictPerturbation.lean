module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

/-! UNVERIFIED quantitative finite strict-inequality preservation. This
provides the small-perturbation step used in Section 7.1, once the actual
old-wall inequalities and their strict canonical values have been proved.
No projectivity or convexity criterion is assumed or encoded here. -/

namespace Unimodular.FiniteStrictPerturbation

theorem one_inequality (a b t : ℝ) (ha : 0 < a)
    (ht : |t| < a / (|b| + 1)) : 0 < a + t * b := by
  have hb : 0 < |b| + 1 := by positivity
  have hta : |t| * (|b| + 1) < a := (lt_div_iff₀ hb).mp ht
  have hprod : |t * b| < a := by
    rw [abs_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (by linarith : |b| ≤ |b| + 1) (abs_nonneg t)) hta
  have hlow := neg_le_abs (t * b)
  linarith

theorem finite_inequalities {K : Type*} [DecidableEq K]
    (s : Finset K) (a b : K → ℝ) (ha : ∀ k ∈ s, 0 < a k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ s, ∀ t : ℝ, |t| < ε → 0 < a k + t * b k := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert k s hks ih =>
      have hak : 0 < a k := ha k (Finset.mem_insert_self k s)
      have has : ∀ j ∈ s, 0 < a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      obtain ⟨ε, hε, hrest⟩ := ih has
      let δ := a k / (|b k| + 1)
      have hδ : 0 < δ := div_pos hak (by positivity)
      refine ⟨min ε δ, lt_min hε hδ, ?_⟩
      intro j hj t ht
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact one_inequality (a j) (b j) t hak (lt_of_lt_of_le ht (min_le_right _ _))
      · exact hrest j hj t (lt_of_lt_of_le ht (min_le_left _ _))

theorem all_inequalities {K : Type*} [Fintype K]
    (a b : K → ℝ) (ha : ∀ k, 0 < a k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ k, 0 < a k + t * b k := by
  classical
  obtain ⟨ε, hε, h⟩ := finite_inequalities Finset.univ a b (fun k _ => ha k)
  exact ⟨ε, hε, fun t ht k => h k (Finset.mem_univ k) t ht⟩

/-- All strict values of a finite family of actual real linear
functionals survive every sufficiently small perturbation. -/
theorem preserves_linear_inequalities {K V : Type*} [Fintype K]
    [AddCommGroup V] [Module ℝ V]
    (L : K → V →ₗ[ℝ] ℝ) (v w : V) (hv : ∀ k, 0 < L k v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ k, 0 < L k (v + t • w) := by
  obtain ⟨ε, hε, h⟩ := all_inequalities (fun k => L k v) (fun k => L k w) hv
  refine ⟨ε, hε, ?_⟩
  intro t ht k
  simpa only [map_add, map_smul, smul_eq_mul] using h t ht k

/-- Every finite family with a positive leading coefficient is positive
for all sufficiently large natural-number scales. The threshold is an
actual natural number, so it can preserve an integral height assignment. -/
theorem positive_for_all_large_nat_scales {K : Type*} [Fintype K]
    (a b : K → ℝ) (ha : ∀ k, 0 < a k) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ k, 0 < (n : ℝ) * a k + b k := by
  classical
  have hbound : ∀ k, ∃ m : ℕ, -b k / a k < m := fun k => exists_nat_gt _
  choose m hm using hbound
  let N : ℕ := (∑ k, m k) + 1
  refine ⟨N, Nat.succ_pos _, ?_⟩
  intro n hn k
  have hk : m k ≤ N :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ k)).trans
      (Nat.le_succ _)
  have hcast : (m k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk.trans hn
  have hprod : -b k < (n : ℝ) * a k := (div_lt_iff₀ (ha k)).mp ((hm k).trans_le hcast)
  linarith

/-- A positive integral dilation preserves every strict inequality of a
finite family of actual linear functionals, after any fixed perturbation.
No geometric projectivity criterion is included in the hypothesis. -/
theorem exists_positive_nat_scale {K V : Type*} [Fintype K]
    [AddCommGroup V] [Module ℝ V]
    (L : K → V →ₗ[ℝ] ℝ) (v w : V) (hv : ∀ k, 0 < L k v) :
    ∃ N : ℕ, 0 < N ∧ ∀ k, 0 < L k ((N : ℝ) • v + w) := by
  obtain ⟨N, hN, h⟩ := positive_for_all_large_nat_scales
    (fun k => L k v) (fun k => L k w) hv
  refine ⟨N, hN, ?_⟩
  intro k
  simpa only [map_add, map_smul, smul_eq_mul] using h N (le_refl N) k

end Unimodular.FiniteStrictPerturbation

#print axioms Unimodular.FiniteStrictPerturbation.one_inequality
#print axioms Unimodular.FiniteStrictPerturbation.finite_inequalities
#print axioms Unimodular.FiniteStrictPerturbation.preserves_linear_inequalities
#print axioms Unimodular.FiniteStrictPerturbation.positive_for_all_large_nat_scales
#print axioms Unimodular.FiniteStrictPerturbation.exists_positive_nat_scale
#check "UNIMODULAR_FINITE_STRICT_PERTURBATION_EOF_V1"
