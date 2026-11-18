module

public import Mathlib.Algebra.Order.Floor.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-!
# Exact integral height and balancing for graphic polytopes

The anchored coordinates include the constant zero coordinate.  Thus all
inequalities have the uniform form `x i - x j ≤ b`, including coordinate
upper and lower bounds.  The height below is twice the height in the paper;
its definition is a sum of squares, so all comparisons are integral.

This module is a development source until its own native receipt succeeds.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicSectionRing

abbrev Lattice (n : ℕ) := Fin n → ℤ
abbrev Coordinate (n : ℕ) := Option (Fin n)

def anchored {n : ℕ} (x : Lattice n) : Coordinate n → ℤ
  | none => 0
  | some i => x i

@[simp] theorem anchored_none {n : ℕ} (x : Lattice n) : anchored x none = 0 := rfl
@[simp] theorem anchored_some {n : ℕ} (x : Lattice n) (i : Fin n) :
    anchored x (some i) = x i := rfl

def difference {n : ℕ} (x : Lattice n) (a b : Coordinate n) : ℤ :=
  anchored x a - anchored x b

def height {n : ℕ} (x : Lattice n) : ℤ :=
  ∑ ab : Coordinate n × Coordinate n, (difference x ab.1 ab.2)^2

theorem height_nonneg {n : ℕ} (x : Lattice n) : 0 ≤ height x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- This is the edge relation of the global staircase triangulation. -/
def Compatible {n : ℕ} (x y : Lattice n) : Prop :=
  ∀ a b, -1 ≤ difference x a b - difference y a b ∧
    difference x a b - difference y a b ≤ 1

theorem compatible_refl {n : ℕ} (x : Lattice n) : Compatible x x := by
  intro a b
  simp

theorem compatible_symm {n : ℕ} {x y : Lattice n}
    (h : Compatible x y) : Compatible y x := by
  intro a b
  have := h a b
  omega

def lower {n : ℕ} (x y : Lattice n) : Lattice n :=
  fun i => (x i + y i) / 2

def upper {n : ℕ} (x y : Lattice n) : Lattice n :=
  fun i => x i + y i - lower x y i

@[simp] theorem anchored_lower {n : ℕ} (x y : Lattice n) (a : Coordinate n) :
    anchored (lower x y) a = (anchored x a + anchored y a) / 2 := by
  cases a <;> simp [lower]

@[simp] theorem anchored_upper {n : ℕ} (x y : Lattice n) (a : Coordinate n) :
    anchored (upper x y) a = anchored x a + anchored y a -
      (anchored x a + anchored y a) / 2 := by
  cases a <;> simp [upper, lower]

theorem lower_add_upper {n : ℕ} (x y : Lattice n) : lower x y + upper x y = x + y := by
  funext i
  simp [lower, upper]

theorem difference_lower_add_upper {n : ℕ} (x y : Lattice n) (a b : Coordinate n) :
    difference (lower x y) a b + difference (upper x y) a b =
      difference x a b + difference y a b := by
  simp only [difference, anchored_lower, anchored_upper]
  ring

theorem compatible_lower_upper {n : ℕ} (x y : Lattice n) :
    Compatible (lower x y) (upper x y) := by
  intro a b
  simp only [difference, anchored_lower, anchored_upper]
  omega

theorem scalar_balanced_minimum (a b c d : ℤ)
    (hs : a + b = c + d) (hc : -1 ≤ c - d) (hd : c - d ≤ 1) :
    c^2 + d^2 ≤ a^2 + b^2 := by
  have hp : 0 ≤ (a - c) * (a - d) := by
    by_cases hac : a ≤ c
    · by_cases had : a ≤ d
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hac) (sub_nonpos.mpr had)
      · have ha : a = c := by omega
        simp [ha]
    · have had : d ≤ a := by omega
      exact mul_nonneg (by omega) (sub_nonneg.mpr had)
  have hb : b = c + d - a := by omega
  rw [hb]
  nlinarith

theorem scalar_balanced_minimum_eq_iff (a b c d : ℤ)
    (hs : a + b = c + d) (hc : -1 ≤ c - d) (hd : c - d ≤ 1) :
    c^2 + d^2 = a^2 + b^2 ↔ -1 ≤ a - b ∧ a - b ≤ 1 := by
  constructor
  · intro he
    have hcd : (c - d)^2 ≤ 1 := by nlinarith
    have hsum := congrArg (fun t : ℤ => t^2) hs
    have hab : (a - b)^2 ≤ 1 := by nlinarith [hsum]
    constructor <;> nlinarith
  · intro hab
    exact le_antisymm (scalar_balanced_minimum a b c d hs hc hd)
      (scalar_balanced_minimum c d a b hs.symm hab.1 hab.2)

theorem height_balance_le {n : ℕ} (x y : Lattice n) :
    height (lower x y) + height (upper x y) ≤ height x + height y := by
  rw [height, height, height, height, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ab _
  exact scalar_balanced_minimum _ _ _ _
    (difference_lower_add_upper x y ab.1 ab.2).symm
    ((compatible_lower_upper x y) ab.1 ab.2).1
    ((compatible_lower_upper x y) ab.1 ab.2).2

/-- Every forbidden pair is replaced by a strictly smaller integral height. -/
theorem height_balance_lt {n : ℕ} (x y : Lattice n) (h : ¬ Compatible x y) :
    height (lower x y) + height (upper x y) < height x + height y := by
  classical
  change ¬ (∀ a b, -1 ≤ difference x a b - difference y a b ∧
    difference x a b - difference y a b ≤ 1) at h
  push_neg at h
  obtain ⟨a, b, hab⟩ := h
  rw [height, height, height, height, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro ab _
    exact scalar_balanced_minimum _ _ _ _
      (difference_lower_add_upper x y ab.1 ab.2).symm
      ((compatible_lower_upper x y) ab.1 ab.2).1
      ((compatible_lower_upper x y) ab.1 ab.2).2
  · refine ⟨(a,b), Finset.mem_univ _, ?_⟩
    apply lt_of_le_of_ne (scalar_balanced_minimum _ _ _ _
      (difference_lower_add_upper x y a b).symm
      ((compatible_lower_upper x y) a b).1
      ((compatible_lower_upper x y) a b).2)
    intro he
    have he' := (scalar_balanced_minimum_eq_iff _ _ _ _
      (difference_lower_add_upper x y a b).symm
      ((compatible_lower_upper x y) a b).1
      ((compatible_lower_upper x y) a b).2).mp he
    omega

structure Constraint (n : ℕ) where
  left : Coordinate n
  right : Coordinate n
  bound : ℤ

def Satisfies {n : ℕ} (C : Set (Constraint n)) (x : Lattice n) : Prop :=
  ∀ c ∈ C, difference x c.left c.right ≤ c.bound

theorem lower_satisfies {n : ℕ} {C : Set (Constraint n)} {x y : Lattice n}
    (hx : Satisfies C x) (hy : Satisfies C y) : Satisfies C (lower x y) := by
  intro c hc
  have hx' := hx c hc
  have hy' := hy c hc
  simp only [difference, anchored_lower] at *
  omega

theorem upper_satisfies {n : ℕ} {C : Set (Constraint n)} {x y : Lattice n}
    (hx : Satisfies C x) (hy : Satisfies C y) : Satisfies C (upper x y) := by
  intro c hc
  have hx' := hx c hc
  have hy' := hy c hc
  simp only [difference, anchored_upper] at *
  omega

/-- Canonical balanced points for a degree `k` lattice target. -/
def balanced {n k : ℕ} (m : Lattice n) (r : Fin k) : Lattice n :=
  fun i => (m i + (r : ℕ)) / (k : ℤ)

theorem anchored_balanced {n k : ℕ} (m : Lattice n) (r : Fin k) (a : Coordinate n) :
    anchored (balanced m r) a = (anchored m a + (r : ℕ)) / (k : ℤ) := by
  cases a with
  | none =>
    simp only [anchored_none, zero_add]
    symm
    exact Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast r.isLt)
  | some i => rfl

theorem balanced_sum {n k : ℕ} (hk : 0 < k) (m : Lattice n) :
    ∑ r : Fin k, balanced m r = m := by
  funext i
  simp only [Finset.sum_apply, balanced]
  exact (Fin.sum_univ_eq_sum_range (fun r : ℕ => (m i + (r : ℤ)) / (k : ℤ)) k).trans
    (Int.sum_range_add_ediv (m i) hk)

theorem ediv_difference_le (a b z k r : ℤ) (hk : 0 < k)
    (h : a - b ≤ k * z) : (a + r) / k - (b + r) / k ≤ z := by
  have hs : a + r ≤ (b + r) + z * k := by nlinarith
  have hd := Int.ediv_le_ediv hk hs
  rw [Int.add_mul_ediv_right _ _ hk.ne'] at hd
  omega

/-- Every lattice point of every positive integral dilate decomposes
into the canonical `k` lattice points of the original difference polytope. -/
theorem balanced_satisfies {n k : ℕ} (hk : 0 < k) {C : Set (Constraint n)}
    (m : Lattice n)
    (hm : ∀ c ∈ C, difference m c.left c.right ≤ (k : ℤ) * c.bound)
    (r : Fin k) : Satisfies C (balanced m r) := by
  intro c hc
  simp only [difference, anchored_balanced]
  exact ediv_difference_le _ _ _ _ _ (by exact_mod_cast hk) (hm c hc)

#print axioms height_balance_lt
#print axioms balanced_sum
#print axioms balanced_satisfies

end Unimodular.GraphicSectionRing
