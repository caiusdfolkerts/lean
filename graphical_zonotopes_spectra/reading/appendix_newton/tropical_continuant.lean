module

public import Mathlib.Data.Real.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Linear minima of the positive path continuant

The pair recursion is the minimum-plus image of the subtraction-free determinant
recursion. Its first component has a local closed formula: triple minima plus
gap-triple minima minus quadruple minima. All weights are arbitrary real numbers.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GraphicalZonotopes.TropicalContinuant

/-- The minimum-plus recursion corresponding to the two positive continuants.
Coordinates and weights are numbered from zero. -/
def pair (w : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | k + 1 =>
      let p := pair w k
      let b := min (w (k + 2) + p.1) (w k + p.2)
      (min b (w (k + 1) + p.1), b)

def first (w : ℕ → ℝ) (k : ℕ) : ℝ := (pair w k).1

def second (w : ℕ → ℝ) (k : ℕ) : ℝ := (pair w k).2

/-- The nonnegative difference between the two minimum weights. -/
def gap (w : ℕ → ℝ) (k : ℕ) : ℝ := second w k - first w k

@[simp] theorem first_zero (w : ℕ → ℝ) : first w 0 = 0 := rfl
@[simp] theorem second_zero (w : ℕ → ℝ) : second w 0 = 0 := rfl
@[simp] theorem gap_zero (w : ℕ → ℝ) : gap w 0 = 0 := by simp [gap]

@[simp] theorem second_succ (w : ℕ → ℝ) (k : ℕ) :
    second w (k + 1) = min (w (k + 2) + first w k) (w k + second w k) := rfl

@[simp] theorem first_succ (w : ℕ → ℝ) (k : ℕ) :
    first w (k + 1) = min (second w (k + 1)) (w (k + 1) + first w k) := rfl

private theorem add_max_zero_sub (a b : ℝ) : a + max 0 (b - a) = max a b := by
  rcases le_total b a with h | h
  · rw [max_eq_left (sub_nonpos.mpr h), add_zero, max_eq_left h]
  · rw [max_eq_right (sub_nonneg.mpr h), max_eq_right h]
    ring

private theorem self_sub_min (a b : ℝ) : a - min a b = max 0 (a - b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, sub_self, max_eq_left (sub_nonpos.mpr h)]
  · rw [min_eq_right h, max_eq_right (sub_nonneg.mpr h)]

private theorem min_max_restrict (a b c d : ℝ) :
    min b (min c (max a (min b d))) = min b (min c (max a d)) := by
  rw [max_min_distrib_left]
  calc
    min b (min c (min (max a b) (max a d))) =
        min (min b (max a b)) (min c (max a d)) := by ac_rfl
    _ = min b (min c (max a d)) := by rw [min_eq_left (le_max_right a b)]

private theorem max_gap_erase {a b e : ℝ} (he : 0 ≤ e)
    (hbound : e ≤ max 0 (a - b)) : max a (b + e) = max a b := by
  rcases le_total b a with h | h
  · rw [max_eq_right (sub_nonneg.mpr h)] at hbound
    rw [max_eq_left (show b + e ≤ a by linarith), max_eq_left h]
  · rw [max_eq_left (sub_nonpos.mpr h)] at hbound
    have heq : e = 0 := le_antisymm hbound he
    simp [heq]

private theorem min_max_expansion (a b t : ℝ) :
    min t (max a b) = min b t + min a t - min a (min b t) := by
  rcases le_total a b with h | h
  · have hab : min a (min b t) = min a t := by
      rw [← min_assoc, min_eq_left h]
    rw [max_eq_right h, hab, min_comm t b]
    ring
  · have hab : min a (min b t) = min b t :=
      min_eq_right ((min_le_left b t).trans h)
    rw [max_eq_left h, hab, min_comm t a]
    ring

theorem second_step (w : ℕ → ℝ) (k : ℕ) :
    second w (k + 1) = first w k + min (w (k + 2)) (w k + gap w k) := by
  rw [second_succ, add_min]
  unfold gap
  congr 1 <;> ring

theorem first_step (w : ℕ → ℝ) (k : ℕ) :
    first w (k + 1) = first w k +
      min (w (k + 1)) (min (w (k + 2)) (w k + gap w k)) := by
  rw [first_succ, second_step, add_comm (w (k + 1)) (first w k), min_add_add_left]
  rw [min_comm (min (w (k + 2)) (w k + gap w k))]

theorem gap_succ (w : ℕ → ℝ) (k : ℕ) :
    gap w (k + 1) =
      max 0 (min (w (k + 2)) (w k + gap w k) - w (k + 1)) := by
  change second w (k + 1) - first w (k + 1) = _
  rw [second_step, first_step]
  calc
    first w k + min (w (k + 2)) (w k + gap w k) -
        (first w k + min (w (k + 1)) (min (w (k + 2)) (w k + gap w k))) =
        min (w (k + 2)) (w k + gap w k) -
          min (min (w (k + 2)) (w k + gap w k)) (w (k + 1)) := by
      rw [min_comm (w (k + 1))]
      ring
    _ = _ := self_sub_min _ _

theorem gap_nonnegative (w : ℕ → ℝ) (k : ℕ) : 0 ≤ gap w k := by
  cases k with
  | zero => simp
  | succ k => rw [gap_succ]; exact le_max_left _ _

theorem gap_bound (w : ℕ → ℝ) (k : ℕ) :
    gap w k ≤ max 0 (w (k + 1) - w k) := by
  cases k with
  | zero => simpa using (le_max_left 0 (w 1 - w 0))
  | succ k =>
      rw [gap_succ]
      exact max_le_max_left 0 (sub_le_sub_right (min_le_left _ _) _)

/-- After the first step, each new minimum depends on just four adjacent weights. -/
theorem first_step_two (w : ℕ → ℝ) (k : ℕ) :
    first w (k + 2) = first w (k + 1) +
      min (w (k + 2)) (min (w (k + 3)) (max (w k) (w (k + 1)))) := by
  calc
    first w (k + 2) = first w (k + 1) +
        min (w (k + 2)) (min (w (k + 3)) (w (k + 1) + gap w (k + 1))) :=
      first_step w (k + 1)
    _ = _ := by
      rw [gap_succ, add_max_zero_sub, min_max_restrict,
        max_gap_erase (gap_nonnegative w k) (gap_bound w k), max_comm (w (k + 1))]

def tripleMinimum (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  min (w i) (min (w (i + 1)) (w (i + 2)))

def gapMinimum (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  min (w i) (min (w (i + 2)) (w (i + 3)))

def quadrupleMinimum (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  min (w i) (min (w (i + 1)) (min (w (i + 2)) (w (i + 3))))

/-- The local expression determined by the exact path Möbius coefficients. -/
def closedFormula (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m, tripleMinimum w i) +
  (∑ i ∈ Finset.range (m - 1), gapMinimum w i) -
  (∑ i ∈ Finset.range (m - 1), quadrupleMinimum w i)

theorem first_one (w : ℕ → ℝ) : first w 1 = tripleMinimum w 0 := by
  simp only [first, pair, second, tripleMinimum, add_zero]
  ac_rfl

theorem closedFormula_step_two (w : ℕ → ℝ) (k : ℕ) :
    closedFormula w (k + 2) = closedFormula w (k + 1) +
      min (w (k + 2)) (min (w (k + 3)) (max (w k) (w (k + 1)))) := by
  have hlocal : tripleMinimum w (k + 1) + gapMinimum w k - quadrupleMinimum w k =
      min (w (k + 2)) (min (w (k + 3)) (max (w k) (w (k + 1)))) := by
    simpa only [tripleMinimum, gapMinimum, quadrupleMinimum, min_assoc,
      min_left_comm, min_comm] using
      (min_max_expansion (w k) (w (k + 1)) (min (w (k + 2)) (w (k + 3)))).symm
  have hfirst : k + 2 - 1 = k + 1 := by omega
  have hsecond : k + 1 - 1 = k := by omega
  simp only [closedFormula, hfirst, hsecond, Finset.sum_range_succ]
  linarith [hlocal]

/-- The complete minimum-plus continuant formula, with no restrictions on weights
or the size, including the empty and one-row continuants. -/
theorem first_eq_closedFormula (w : ℕ → ℝ) (m : ℕ) :
    first w m = closedFormula w m := by
  induction m with
  | zero => simp [closedFormula]
  | succ m ih =>
      cases m with
      | zero => simpa [closedFormula] using first_one w
      | succ k => rw [first_step_two, ih, closedFormula_step_two]

/-- The recursion determines both minimum sequences uniquely. -/
theorem pair_eq_of_recurrences (w a b : ℕ → ℝ)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hb : ∀ k, b (k + 1) = min (w (k + 2) + a k) (w k + b k))
    (ha : ∀ k, a (k + 1) = min (b (k + 1)) (w (k + 1) + a k)) :
    ∀ k, (a k, b k) = pair w k := by
  intro k
  induction k with
  | zero => simp [ha0, hb0, pair]
  | succ k ih =>
      have ha' : a k = (pair w k).1 := congrArg Prod.fst ih
      have hb' : b k = (pair w k).2 := congrArg Prod.snd ih
      apply Prod.ext
      · simpa only [pair, ha, hb, ha', hb']
      · simpa only [pair, hb, ha', hb']

end GraphicalZonotopes.TropicalContinuant
