module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Actual bounded walks and the high-strip reflection formula

This new source is a candidate until its recorded ordinary compiler and
axiom audit succeed. The walk number is the cardinality of the actual
length-restricted walks of a path graph. No binomial expression is used
as the definition of a walk number.

The proof uses the integral heat equation on a cycle of twice the distance
between the two absorbing walls. An antisymmetric difference imposes both
walls, without division or an unproved reflection principle.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms.StripWalks

/-- Integer coefficients of the genuine cyclic nearest-neighbor walk operator. -/
def cyclicCount (H N : ℕ) (x : ZMod (2 * H)) : ℤ :=
  (((AddMonoidAlgebra.single (1 : ZMod (2 * H)) (1 : ℤ) +
    AddMonoidAlgebra.single (-1 : ZMod (2 * H)) (1 : ℤ)) ^ N).coeff x)

@[simp] theorem cyclicCount_zero (H : ℕ) (x : ZMod (2 * H)) :
    cyclicCount H 0 x = if x = 0 then 1 else 0 := by
  classical
  simp [cyclicCount, AddMonoidAlgebra.one_def, Finsupp.single_apply, eq_comm]

/-- The recurrence counts the two actual directions, including their multiplicities. -/
theorem cyclicCount_succ (H N : ℕ) (x : ZMod (2 * H)) :
    cyclicCount H (N + 1) x = cyclicCount H N (x - 1) + cyclicCount H N (x + 1) := by
  simp [cyclicCount, pow_succ', add_mul, sub_eq_add_neg, add_comm]

theorem cyclicCount_neg (H N : ℕ) (x : ZMod (2 * H)) :
    cyclicCount H N (-x) = cyclicCount H N x := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
      rw [cyclicCount_succ, cyclicCount_succ,
        show -x - 1 = -(x + 1) by ring,
        show -x + 1 = -(x - 1) by ring, ih, ih]
      exact add_comm _ _

/-- The complete binomial expansion of the cyclic walk operator. -/
theorem cyclicCount_binomial (H N : ℕ) (x : ZMod (2 * H)) :
    cyclicCount H N x =
      ∑ i ∈ Finset.range (N + 1),
        if (N : ZMod (2 * H)) - 2 * i = x then (N.choose i : ℤ) else 0 := by
  classical
  unfold cyclicCount
  rw [add_comm, add_pow]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hindex : i • (-1 : ZMod (2 * H)) + (N - i) • (1 : ZMod (2 * H)) =
      (N : ZMod (2 * H)) - 2 * i := by
    simp only [nsmul_neg, nsmul_one, Nat.cast_sub hiN]
    ring
  simp only [AddMonoidAlgebra.single_pow, one_pow,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single,
    one_mul, mul_one, add_zero, hindex, AddMonoidAlgebra.coeff_single_apply]

/-- Cancellation of the factor two occurs in integers, not in the residue ring. -/
theorem cyclic_index_eq_iff (H N i a : ℕ) :
    ((N : ZMod (2 * H)) - 2 * i = (N : ZMod (2 * H)) - 2 * a) ↔
      (H : ℤ) ∣ (i : ℤ) - a := by
  have h :
      ((N : ZMod (2 * H)) - 2 * i = (N : ZMod (2 * H)) - 2 * a) ↔
        (((2 : ℤ) * ((i : ℤ) - a) : ℤ) : ZMod (2 * H)) = 0 := by
    push_cast
    constructor <;> intro h <;> linear_combination -h
  rw [h, ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)

theorem two_residues (H N a i : ℕ) (ha : a < H) (hN : N < a + 2 * H)
    (hi : i ≤ N) :
    ((H : ℤ) ∣ (i : ℤ) - a) ↔ i = a ∨ i = a + H := by
  constructor
  · rintro ⟨q, hq⟩
    have hH : (0 : ℤ) < H := by exact_mod_cast (Nat.zero_lt_of_lt ha)
    have ha' : (a : ℤ) < H := by exact_mod_cast ha
    have hi' : (i : ℤ) ≤ N := by exact_mod_cast hi
    have hN' : (N : ℤ) < a + 2 * H := by exact_mod_cast hN
    have hq0 : 0 ≤ q := by
      by_contra hn
      have hh : q ≤ -1 := by omega
      have hm := mul_le_mul_of_nonneg_left hh hH.le
      nlinarith
    have hq2 : q < 2 := by
      by_contra hn
      have hh : 2 ≤ q := by omega
      have hm := mul_le_mul_of_nonneg_left hh hH.le
      nlinarith
    have hh : q = 0 ∨ q = 1 := by omega
    rcases hh with rfl | rfl
    · left
      simp only [mul_zero] at hq
      omega
    · right
      simp only [mul_one] at hq
      omega
  · rintro (rfl | rfl)
    · simp
    · simp

/-- Exactly two images contribute in the indicated range; this is an
unrestricted finite coefficient calculation, not a finite-instance check. -/
theorem cyclicCount_binomial_two (H N a : ℕ) (ha : a < H)
    (haN : a + H ≤ N) (hN : N < a + 2 * H) :
    cyclicCount H N ((N : ZMod (2 * H)) - 2 * a) =
      (N.choose a : ℤ) + N.choose (a + H) := by
  classical
  rw [cyclicCount_binomial]
  have hne : a ≠ a + H := by omega
  have hH : H ≠ 0 := by omega
  have hf (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
      (if (N : ZMod (2 * H)) - 2 * i = (N : ZMod (2 * H)) - 2 * a
        then (N.choose i : ℤ) else 0) =
      (if i = a then (N.choose i : ℤ) else 0) +
        (if i = a + H then (N.choose i : ℤ) else 0) := by
    simp only [cyclic_index_eq_iff, two_residues H N a i ha hN
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    by_cases hia : i = a
    · subst i
      simp [hne, hH]
    · by_cases hiah : i = a + H
      · subst i
        simp [hne, Ne.symm hne, hH]
      · simp [hia, hiah]
  rw [Finset.sum_congr rfl hf, Finset.sum_add_distrib]
  simp [Finset.mem_range, show a < N + 1 by omega,
    show a + H < N + 1 by omega]

/-- The antisymmetric heat kernel with absorbing walls at -1 and w+1. -/
def stripKernel (w N : ℕ) (j : ℤ) : ℤ :=
  cyclicCount (w + 2) N (j : ZMod (2 * (w + 2))) -
    cyclicCount (w + 2) N ((j + 2 : ℤ) : ZMod (2 * (w + 2)))

theorem stripKernel_succ (w N : ℕ) (j : ℤ) :
    stripKernel w (N + 1) j = stripKernel w N (j - 1) + stripKernel w N (j + 1) := by
  unfold stripKernel
  simp only [cyclicCount_succ, Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_ofNat]
  rw [show ((j : ZMod (2 * (w + 2))) + 2) - 1 = j + 1 by ring,
    show ((j : ZMod (2 * (w + 2))) - 1) + 2 = j + 1 by ring,
    show ((j : ZMod (2 * (w + 2))) + 2) + 1 = (j + 1) + 2 by ring]
  ring

theorem stripKernel_lower (w N : ℕ) : stripKernel w N (-1) = 0 := by
  simp [stripKernel, cyclicCount_neg]

theorem stripKernel_upper (w N : ℕ) : stripKernel w N (w + 1) = 0 := by
  have hh : (2 : ZMod (2 * (w + 2))) * (w + 2) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      (ZMod.natCast_self (2 * (w + 2)))
  have he : (w : ZMod (2 * (w + 2))) + 1 + 2 = -(w + 1) := by
    linear_combination hh
  unfold stripKernel
  push_cast
  rw [he, cyclicCount_neg, sub_self]

/-- The two possible neighbors of a path-graph vertex, with no out-of-strip
vertex inserted at either endpoint. -/
theorem path_neighbor_sum (w : ℕ) (j : Fin (w + 1)) (f : Fin (w + 1) → ℤ) :
    (∑ k : Fin (w + 1),
      if k.val + 1 = j.val ∨ j.val + 1 = k.val then f k else 0) =
      (if h : 0 < j.val then f ⟨j.val - 1, by omega⟩ else 0) +
      (if h : j.val < w then f ⟨j.val + 1, by omega⟩ else 0) := by
  classical
  have hs (k : Fin (w + 1)) :
      (if k.val + 1 = j.val ∨ j.val + 1 = k.val then f k else 0) =
        (if k.val + 1 = j.val then f k else 0) +
        (if j.val + 1 = k.val then f k else 0) := by
    by_cases h₁ : k.val + 1 = j.val
    · have h₂ : ¬j.val + 1 = k.val := by omega
      simp [h₁, h₂]
    · by_cases h₂ : j.val + 1 = k.val <;> simp [h₁, h₂]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hj : 0 < j.val
    · rw [dite_eq_left hj]
      let v : Fin (w + 1) := ⟨j.val - 1, by omega⟩
      have hv (k : Fin (w + 1)) : k.val + 1 = j.val ↔ k = v := by
        constructor
        · intro hk
          apply Fin.ext
          dsimp [v]
          omega
        · rintro rfl
          dsimp [v]
          omega
      simp_rw [hv]
      simp [v]
    · have hz (k : Fin (w + 1)) : ¬ k.val + 1 = j.val := by omega
      simp [hz, hj]
  · by_cases hj : j.val < w
    · rw [dite_eq_left hj]
      let v : Fin (w + 1) := ⟨j.val + 1, by omega⟩
      have hv (k : Fin (w + 1)) : j.val + 1 = k.val ↔ k = v := by
        constructor
        · intro hk
          apply Fin.ext
          exact hk.symm
        · rintro rfl
          rfl
      simp_rw [hv]
      simp [v]
    · have hz (k : Fin (w + 1)) : ¬ j.val + 1 = k.val := by omega
      simp [hz, hj]

/-- Extending a function by its zero wall values turns the finite path sum
into the ordinary nearest-neighbor recurrence. -/
theorem path_neighbor_sum_of_walls (w : ℕ) (j : Fin (w + 1)) (f : ℤ → ℤ)
    (hlo : f (-1) = 0) (hhi : f (w + 1) = 0) :
    (∑ k : Fin (w + 1),
      if k.val + 1 = j.val ∨ j.val + 1 = k.val then f k.val else 0) =
      f ((j.val : ℤ) - 1) + f ((j.val : ℤ) + 1) := by
  rw [path_neighbor_sum]
  congr 1
  · by_cases hj : 0 < j.val
    · rw [dite_eq_left hj]
      congr 1
      exact Nat.cast_sub (by omega : 1 ≤ j.val)
    · have hz : j.val = 0 := by omega
      simp [hj, hz, hlo]
  · by_cases hj : j.val < w
    · rw [dite_eq_left hj]
      congr 1
    · have hz : j.val = w := by omega
      simp [hj, hz, hhi]

theorem cyclicCount_zero_nat (H j : ℕ) (hj : j < 2 * H) :
    cyclicCount H 0 (j : ZMod (2 * H)) = if j = 0 then 1 else 0 := by
  rw [cyclicCount_zero]
  have h : (j : ZMod (2 * H)) = 0 ↔ j = 0 := by
    simpa only [Nat.cast_zero, Nat.mod_eq_of_lt hj, Nat.zero_mod] using
      (ZMod.natCast_eq_natCast_iff' j 0 (2 * H))
  simp only [h]

theorem stripKernel_zero (w : ℕ) (j : Fin (w + 1)) :
    stripKernel w 0 j.val = if j = 0 then 1 else 0 := by
  unfold stripKernel
  have hj : j.val < 2 * (w + 2) := by omega
  have hj₂ : j.val + 2 < 2 * (w + 2) := by omega
  have he : (((j.val : ℤ) + 2 : ℤ) : ZMod (2 * (w + 2))) =
      ((j.val + 2 : ℕ) : ZMod (2 * (w + 2))) := by push_cast; rfl
  rw [he]
  simp only [Int.cast_natCast]
  rw [cyclicCount_zero_nat _ _ hj, cyclicCount_zero_nat _ _ hj₂]
  have hz : j.val = 0 ↔ j = 0 := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      exact congrArg Fin.val h
  have hne : j.val + 2 ≠ 0 := by omega
  simp only [hz, hne, ite_false, sub_zero]

/-- The cyclic antisymmetric kernel equals the actual path adjacency power
in every degree, not only in the high-strip range. -/
theorem path_adjacency_power (w N : ℕ) (j : Fin (w + 1)) :
    ((SimpleGraph.pathGraph (w + 1)).adjMatrix ℤ ^ N) 0 j =
      stripKernel w N j.val := by
  classical
  induction N generalizing j with
  | zero =>
      rw [stripKernel_zero]
      simp [Matrix.one_apply, eq_comm]
  | succ N ih =>
      rw [pow_succ, Matrix.mul_apply]
      simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.pathGraph_adj,
        mul_ite, mul_one, mul_zero, ih]
      rw [path_neighbor_sum_of_walls w j (stripKernel w N)
        (stripKernel_lower w N) (stripKernel_upper w N), stripKernel_succ]

/-- The exact number of length-N walks in the closed strip [0,w]. -/
def walkCount (w N : ℕ) : ℕ :=
  Fintype.card {p : (SimpleGraph.pathGraph (w + 1)).Walk 0 (Fin.last w) // p.length = N}

/-- The matrix recurrence is connected to Mathlib's actual length-restricted
walk type, so the analytic expression is not a substitute definition. -/
theorem walkCount_eq_stripKernel (w N : ℕ) :
    (walkCount w N : ℤ) = stripKernel w N w := by
  calc
    (walkCount w N : ℤ) =
        ((SimpleGraph.pathGraph (w + 1)).adjMatrix ℤ ^ N) 0 (Fin.last w) := by
      exact (SimpleGraph.adjMatrix_pow_apply_eq_card_walk
        (G := SimpleGraph.pathGraph (w + 1)) (α := ℤ) N 0 (Fin.last w)).symm
    _ = stripKernel w N w := path_adjacency_power w N (Fin.last w)

/-- Two applications of Pascal's identity, over the integers. -/
theorem choose_add_two (n k : ℕ) :
    ((n + 2).choose (k + 2) : ℤ) =
      (n.choose (k + 2) : ℤ) + 2 * n.choose (k + 1) + n.choose k := by
  have h₀ := Nat.choose_succ_succ' (n + 1) (k + 1)
  have h₁ := Nat.choose_succ_succ' n k
  have h₂ := Nat.choose_succ_succ' n (k + 1)
  rw [h₀, h₁, h₂]
  push_cast
  ring

theorem second_binomial_difference (n s : ℕ) (hs : 4 ≤ s) :
    ((n + 2).choose s : ℤ) - 2 * (n + 2).choose (s - 1) +
        (n + 2).choose (s - 2) =
      (n.choose s : ℤ) - 2 * n.choose (s - 2) + n.choose (s - 4) := by
  have h₀ := choose_add_two n (s - 2)
  have h₁ := choose_add_two n (s - 3)
  have h₂ := choose_add_two n (s - 4)
  rw [show s - 2 + 2 = s by omega, show s - 2 + 1 = s - 1 by omega] at h₀
  rw [show s - 3 + 2 = s - 1 by omega, show s - 3 + 1 = s - 2 by omega] at h₁
  rw [show s - 4 + 2 = s - 2 by omega, show s - 4 + 1 = s - 3 by omega] at h₂
  linear_combination h₀ - 2 * h₁ + h₂

/-- The paper's actual strip-walk count. All applications below prove that
the displayed width is nonnegative before using its natural-number form. -/
def paperWalkCount (n s : ℕ) : ℕ := walkCount (n + 2 - 2 * s) (n + 2)

/-- The complete high-strip identity needed for every prime in Theorem 7.2.
The lower bound s≥4 is automatic when s=2p and p is prime. Neither n nor p
has a finite upper bound. All subtractions in the formula are integer ones. -/
theorem high_strip_count (n s : ℕ) (hs : 4 ≤ s) (hn : 3 * s - 3 ≤ n) :
    (paperWalkCount n s : ℤ) =
      (n.choose s : ℤ) - 2 * n.choose (s - 2) + n.choose (s - 4) := by
  let w := n + 2 - 2 * s
  let H := w + 2
  have hw : n + 2 = w + 2 * s := by dsimp [w]; omega
  have hwidth : s - 1 ≤ w := by dsimp [w]; omega
  have ha : s < H := by dsimp [H]; omega
  have hsa : s - 1 < H := by omega
  have haN : s + H ≤ n + 2 := by dsimp [H]; omega
  have hsaN : s - 1 + H ≤ n + 2 := by omega
  have hN : n + 2 < s + 2 * H := by dsimp [H]; omega
  have hsN : n + 2 < s - 1 + 2 * H := by dsimp [H]; omega
  have hwZ : (n + 2 : ZMod (2 * H)) = (w : ZMod (2 * H)) + 2 * s := by
    have h := congrArg (fun a : ℕ ↦ (a : ZMod (2 * H))) hw
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  have harg : (n + 2 : ZMod (2 * H)) - 2 * s = w := by
    linear_combination hwZ
  have harg₂ : (n + 2 : ZMod (2 * H)) - 2 * (s - 1 : ℕ) = w + 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    linear_combination hwZ
  have h₀ := cyclicCount_binomial_two H (n + 2) s ha haN hN
  have h₂ := cyclicCount_binomial_two H (n + 2) (s - 1) hsa hsaN hsN
  simp only [Nat.cast_add, Nat.cast_ofNat] at h₀ h₂
  rw [harg, show s + H = (n + 2) - (s - 2) by dsimp [H]; omega,
    Nat.choose_symm (by omega : s - 2 ≤ n + 2)] at h₀
  rw [harg₂, show s - 1 + H = (n + 2) - (s - 1) by dsimp [H]; omega,
    Nat.choose_symm (by omega : s - 1 ≤ n + 2)] at h₂
  change (walkCount w (n + 2) : ℤ) = _
  rw [walkCount_eq_stripKernel]
  unfold stripKernel
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat]
  change cyclicCount H (n + 2) (w : ZMod (2 * H)) -
    cyclicCount H (n + 2) ((w : ZMod (2 * H)) + 2) = _
  rw [h₀, h₂]
  have h := second_binomial_difference n s hs
  linear_combination h


end PaperVerification.AlternatingForms.StripWalks
