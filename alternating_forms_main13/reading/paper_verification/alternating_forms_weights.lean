module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Strict weights in the odd straightening arguments

This file checks the two numerical termination arguments in Sections 3.1
and 3.3: a later power-of-two pair costs more than all prefix pairs, and
meet/join sorting strictly decreases the prescribed Hibi weight.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

theorem sum_prefix_pair_costs (h : ℕ) :
    (∑ i ∈ Finset.range h, (2 : ℕ) ^ (i + 1)) + 2 = 2 ^ (h + 1) := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [Finset.sum_range_succ, pow_succ (2 : ℕ) (h + 1)]
    omega

/-- A pair strictly after a prefix has larger cost than every subset of
the prefix pairs together.  This is uniform in the prefix and ambient size. -/
theorem later_pair_cost_gt_prefix (P : Finset ℕ) (h j : ℕ)
    (hP : P ⊆ Finset.range h) (hj : h ≤ j) :
    (∑ i ∈ P, (2 : ℕ) ^ (i + 1)) < 2 ^ (j + 1) := by
  have hsum : (∑ i ∈ P, (2 : ℕ) ^ (i + 1)) ≤
      ∑ i ∈ Finset.range h, (2 : ℕ) ^ (i + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => Nat.zero_le _)
  have hpow : (2 : ℕ) ^ (h + 1) ≤ 2 ^ (j + 1) :=
    pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega)
  have hfull := sum_prefix_pair_costs h
  omega

theorem replacement_pair_cost_strict (P T : Finset ℕ) (h j : ℕ)
    (hP : P ⊆ Finset.range h) (hj : h ≤ j) :
    (∑ i ∈ P, (2 : ℕ) ^ (i + 1)) <
      (∑ i ∈ T, (2 : ℕ) ^ (i + 1)) + 2 ^ (j + 1) :=
  (later_pair_cost_gt_prefix P h j hP hj).trans_le (Nat.le_add_left _ _)

section VertexWeights

/-- Any integral edge costs on a path have integral vertex costs whose
consecutive sums are the prescribed edge costs. -/
def pathVertexCost (e : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => e j - pathVertexCost e j

theorem pathVertexCost_adjacent (e : ℕ → ℤ) (j : ℕ) :
    pathVertexCost e j + pathVertexCost e (j + 1) = e j := by
  simp only [pathVertexCost]
  omega

variable {ι : Type*} [Fintype ι]

/-- An explicit common shift making all finitely many vertex weights
strictly positive. -/
def positiveWeightShift (u : ι → ℤ) : ℤ := 1 + ∑ i, |u i|

theorem shiftedVertexWeight_pos (u : ι → ℤ) (i : ι) :
    0 < positiveWeightShift u - u i := by
  have hu : u i ≤ |u i| := le_abs_self _
  have hsum : |u i| ≤ ∑ j, |u j| :=
    Finset.single_le_sum (fun j hj => abs_nonneg (u j)) (Finset.mem_univ i)
  unfold positiveWeightShift
  omega

/-- On fixed-degree squarefree monomials the positive shifted weight
reverses the original integral cost order exactly. -/
theorem shiftedWeight_strict_of_cost {u : ι → ℤ} {S T : Finset ι}
    (hcard : S.card = T.card) (hcost : (∑ i ∈ S, u i) < ∑ i ∈ T, u i) (C : ℤ) :
    (∑ i ∈ T, (C - u i)) < ∑ i ∈ S, (C - u i) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  omega

end VertexWeights

section HibiWeights

variable {ι : Type*} [Fintype ι]

/-- The rank function of the interval lattice, with an arbitrary fixed
lower endpoint.  For interval elements this agrees with the paper's
nonnegative integer rank. -/
def intervalRank (α I : ι → ℕ) : ℤ := ∑ i, ((I i : ℤ) - (α i : ℤ))

theorem intervalRank_meet_add_join (α I J : ι → ℕ) :
    intervalRank α (fun i => min (I i) (J i)) +
        intervalRank α (fun i => max (I i) (J i)) =
      intervalRank α I + intervalRank α J := by
  rw [intervalRank, intervalRank, intervalRank, intervalRank,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases le_total (I i) (J i) with h | h <;> simp [h] <;> ring

theorem intervalRank_meet_lt_left (α I J : ι → ℕ) (hIJ : ¬I ≤ J) :
    intervalRank α (fun i => min (I i) (J i)) < intervalRank α I := by
  classical
  have hex : ∃ i, J i < I i := by
    obtain ⟨i, hi⟩ := not_forall.mp hIJ
    exact ⟨i, Nat.lt_of_not_ge hi⟩
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_lt_sum
  · intro j hj
    exact sub_le_sub_right (Int.ofNat_le.mpr (min_le_left _ _)) _
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    exact sub_lt_sub_right (Int.ofNat_lt.mpr (by simpa [min_eq_right hi.le] using hi)) _

/-- The weight `C-ρ²` strictly decreases under meet/join sorting of every
incomparable pair, exactly as required in the Hibi Gröbner argument. -/
theorem hibi_sort_weight_decreases (α I J : ι → ℕ)
    (hIJ : ¬I ≤ J) (hJI : ¬J ≤ I) (C : ℤ) :
    (C - intervalRank α (fun i => min (I i) (J i)) ^ 2) +
        (C - intervalRank α (fun i => max (I i) (J i)) ^ 2) <
      (C - intervalRank α I ^ 2) + (C - intervalRank α J ^ 2) := by
  have hleft := intervalRank_meet_lt_left α I J hIJ
  have hright := intervalRank_meet_lt_left α J I hJI
  simp only [min_comm] at hright
  have hsum := intervalRank_meet_add_join α I J
  have hprod := mul_pos (sub_pos.mpr hleft) (sub_pos.mpr hright)
  have hjoin : intervalRank α (fun i => max (I i) (J i)) =
      intervalRank α I + intervalRank α J -
        intervalRank α (fun i => min (I i) (J i)) := by omega
  rw [hjoin]
  nlinarith [hprod]

end HibiWeights

end PaperVerification.AlternatingForms
