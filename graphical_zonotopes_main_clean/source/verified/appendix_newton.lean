module

public import verified.appendix_a2
import all verified.appendix_a2
import all verified.extensions
import all verified.main
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section AppendixNewtonPart0
/- Source: Correspondence/PositivePolynomialMinima.lean -/














/-!
# Linear minima of polynomials with nonnegative coefficients

For real polynomials with nonnegative coefficients, sums and products have
exact support union and support Minkowski-sum formulas. Consequently every
real linear weight has the expected minimum formulas, without any generic
Newton-polytope product theorem. The final lemma identifies this minimum
with the ordinary linear minimum on the convex hull of the exponent support.
-/

@[expose] public section

noncomputable section

open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes.PositivePolynomial

variable {σ : Type*}

/-- Coefficientwise nonnegativity in the ordinary real polynomial ring. -/
def Nonnegative (p : MvPolynomial σ ℝ) : Prop :=
  ∀ d, 0 ≤ p.coeff d

theorem nonnegative_one : Nonnegative (1 : MvPolynomial σ ℝ) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_one]
  split_ifs <;> norm_num

theorem nonnegative_X (i : σ) : Nonnegative (MvPolynomial.X i : MvPolynomial σ ℝ) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_X]
  split_ifs <;> norm_num

theorem nonnegative_add {p q : MvPolynomial σ ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) : Nonnegative (p + q) := by
  intro d
  rw [MvPolynomial.coeff_add]
  exact add_nonneg (hp d) (hq d)

theorem nonnegative_mul {p q : MvPolynomial σ ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) : Nonnegative (p * q) := by
  classical
  intro d
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg fun ab _ => mul_nonneg (hp ab.1) (hq ab.2)

theorem positive_coeff_of_mem_support {p : MvPolynomial σ ℝ}
    (hp : Nonnegative p) {d : σ →₀ ℕ} (hd : d ∈ p.support) : 0 < p.coeff d :=
  lt_of_le_of_ne (hp d) (Ne.symm (MvPolynomial.mem_support_iff.mp hd))

theorem add_ne_zero_of_nonnegative {p q : MvPolynomial σ ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) (hp0 : p ≠ 0) : p + q ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hp0
  have hpos : 0 < (p + q).coeff d := by
    rw [MvPolynomial.coeff_add]
    exact add_pos_of_pos_of_nonneg (positive_coeff_of_mem_support hp hd) (hq d)
  intro he
  rw [he, MvPolynomial.coeff_zero] at hpos
  exact lt_irrefl _ hpos

/-- Positive coefficients prevent cancellation in a sum. -/
theorem support_add_eq {p q : MvPolynomial σ ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) :
    (p + q).support = p.support ∪ q.support := by
  classical
  ext d
  simp only [MvPolynomial.mem_support_iff, Finset.mem_union, MvPolynomial.coeff_add]
  constructor
  · intro h
    by_contra hnot
    push_neg at hnot
    exact h (by rw [hnot.1, hnot.2, add_zero])
  · rintro (hd | hd) he
    · have hpos : 0 < p.coeff d := lt_of_le_of_ne (hp d) (Ne.symm hd)
      linarith [hq d]
    · have hpos : 0 < q.coeff d := lt_of_le_of_ne (hq d) (Ne.symm hd)
      linarith [hp d]

/-- Every sum of support exponents survives in a product of nonnegative polynomials. -/
theorem support_mul_eq {p q : MvPolynomial σ ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) :
    (p * q).support = p.support + q.support := by
  classical
  refine Finset.Subset.antisymm (MvPolynomial.support_mul p q) ?_
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hd
  apply MvPolynomial.mem_support_iff.mpr
  have hterm : 0 < p.coeff a * q.coeff b :=
    mul_pos (positive_coeff_of_mem_support hp ha) (positive_coeff_of_mem_support hq hb)
  have hle : p.coeff a * q.coeff b ≤ (p * q).coeff (a + b) := by
    rw [MvPolynomial.coeff_mul]
    exact Finset.single_le_sum
      (fun ab _ => mul_nonneg (hp ab.1) (hq ab.2))
      (by simp : (a, b) ∈ Finset.antidiagonal (a + b))
  exact ne_of_gt (lt_of_lt_of_le hterm hle)

/-- A real weight of an exponent vector. Weights may have either sign. -/
def exponentWeight (w : σ → ℝ) (d : σ →₀ ℕ) : ℝ :=
  d.sum fun i k => w i * (k : ℝ)

@[simp] theorem exponentWeight_zero (w : σ → ℝ) :
    exponentWeight w (0 : σ →₀ ℕ) = 0 := by
  simp [exponentWeight]

@[simp] theorem exponentWeight_single (w : σ → ℝ) (i : σ) (k : ℕ) :
    exponentWeight w (Finsupp.single i k) = w i * (k : ℝ) := by
  classical
  simp [exponentWeight]

theorem exponentWeight_add (w : σ → ℝ) (d e : σ →₀ ℕ) :
    exponentWeight w (d + e) = exponentWeight w d + exponentWeight w e := by
  classical
  unfold exponentWeight
  exact Finsupp.sum_add_index' (fun _ => by simp)
    (fun _ a b => by simp [Nat.cast_add, mul_add])

/-- The real minimum of a linear weight over the finite exponent support.
All uses of the minimum formulas below require nonzero polynomials. -/
def minimum (w : σ → ℝ) (p : MvPolynomial σ ℝ) : ℝ :=
  sInf (exponentWeight w '' (p.support : Set (σ →₀ ℕ)))

theorem minimum_isLeast (w : σ → ℝ) {p : MvPolynomial σ ℝ} (hp : p ≠ 0) :
    IsLeast (exponentWeight w '' (p.support : Set (σ →₀ ℕ))) (minimum w p) := by
  classical
  obtain ⟨d, hd, hmin⟩ := p.support.exists_min_image (exponentWeight w)
    (MvPolynomial.support_nonempty.mpr hp)
  have hleast : IsLeast (exponentWeight w '' (p.support : Set (σ →₀ ℕ)))
      (exponentWeight w d) := by
    refine ⟨⟨d, hd, rfl⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact hmin e he
  change IsLeast _ (sInf _)
  rw [hleast.csInf_eq]
  exact hleast

theorem exists_minimum (w : σ → ℝ) {p : MvPolynomial σ ℝ} (hp : p ≠ 0) :
    ∃ d ∈ p.support, exponentWeight w d = minimum w p :=
  (minimum_isLeast w hp).1

theorem minimum_le (w : σ → ℝ) {p : MvPolynomial σ ℝ} (hp : p ≠ 0)
    {d : σ →₀ ℕ} (hd : d ∈ p.support) : minimum w p ≤ exponentWeight w d :=
  (minimum_isLeast w hp).2 ⟨d, hd, rfl⟩

@[simp] theorem minimum_one (w : σ → ℝ) : minimum w (1 : MvPolynomial σ ℝ) = 0 := by
  classical
  simp [minimum]

@[simp] theorem minimum_X (w : σ → ℝ) (i : σ) :
    minimum w (MvPolynomial.X i : MvPolynomial σ ℝ) = w i := by
  classical
  simp [minimum, MvPolynomial.support_X]

/-- The tropical minimum law for addition, with no cancellation hypothesis hidden. -/
theorem minimum_add (w : σ → ℝ) {p q : MvPolynomial σ ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    minimum w (p + q) = min (minimum w p) (minimum w q) := by
  have hsum0 := add_ne_zero_of_nonnegative hp hq hp0
  obtain ⟨a, ha, haw⟩ := exists_minimum w hp0
  obtain ⟨b, hb, hbw⟩ := exists_minimum w hq0
  apply le_antisymm
  · apply le_min
    · rw [← haw]
      apply minimum_le w hsum0
      rw [support_add_eq hp hq]
      exact Finset.mem_union_left _ ha
    · rw [← hbw]
      apply minimum_le w hsum0
      rw [support_add_eq hp hq]
      exact Finset.mem_union_right _ hb
  · obtain ⟨d, hd, hdw⟩ := exists_minimum w hsum0
    rw [← hdw]
    rw [support_add_eq hp hq] at hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact (min_le_left _ _).trans (minimum_le w hp0 hd)
    · exact (min_le_right _ _).trans (minimum_le w hq0 hd)

/-- The tropical minimum law for multiplication of nonnegative real polynomials. -/
theorem minimum_mul (w : σ → ℝ) {p q : MvPolynomial σ ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    minimum w (p * q) = minimum w p + minimum w q := by
  have hprod0 : p * q ≠ 0 := mul_ne_zero hp0 hq0
  obtain ⟨a, ha, haw⟩ := exists_minimum w hp0
  obtain ⟨b, hb, hbw⟩ := exists_minimum w hq0
  apply le_antisymm
  · calc
      minimum w (p * q) ≤ exponentWeight w (a + b) := by
        apply minimum_le w hprod0
        rw [support_mul_eq hp hq]
        exact Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩
      _ = minimum w p + minimum w q := by rw [exponentWeight_add, haw, hbw]
  · obtain ⟨d, hd, hdw⟩ := exists_minimum w hprod0
    rw [support_mul_eq hp hq] at hd
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hd
    rw [← hdw, exponentWeight_add]
    exact add_le_add (minimum_le w hp0 hu) (minimum_le w hq0 hv)

section FiniteVariables

variable [Fintype σ]

/-- The ordinary real linear functional with coordinate weights `w`. -/
def linearWeight (w : σ → ℝ) (x : σ → ℝ) : ℝ := ∑ i, w i * x i

theorem linearWeight_add (w x y : σ → ℝ) :
    linearWeight w (x + y) = linearWeight w x + linearWeight w y := by
  simp [linearWeight, mul_add, Finset.sum_add_distrib]

theorem linearWeight_smul (w x : σ → ℝ) (a : ℝ) :
    linearWeight w (a • x) = a * linearWeight w x := by
  simp only [linearWeight, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem linearWeight_exponent (w : σ → ℝ) (d : σ →₀ ℕ) :
    linearWeight w (fun i => (d i : ℝ)) = exponentWeight w d := by
  unfold linearWeight exponentWeight
  exact (d.sum_fintype (fun i k => w i * (k : ℝ)) (fun _ => by simp)).symm

/-- The algebraic minimum is exactly the linear minimum on the ordinary
convex hull of the exponent support. No coefficient-sign assumption is needed. -/
theorem minimum_isLeast_convexHull (w : σ → ℝ) {p : MvPolynomial σ ℝ} (hp : p ≠ 0) :
    IsLeast (linearWeight w ''
      convexHull ℝ ((fun d : σ →₀ ℕ => fun i => (d i : ℝ)) ''
        (p.support : Set (σ →₀ ℕ)))) (minimum w p) := by
  obtain ⟨d, hd, hdw⟩ := exists_minimum w hp
  refine ⟨⟨(fun i => (d i : ℝ)), subset_convexHull ℝ _ ⟨d, hd, rfl⟩, ?_⟩, ?_⟩
  · rw [linearWeight_exponent, hdw]
  · rintro _ ⟨x, hx, rfl⟩
    have hconv : Convex ℝ {x : σ → ℝ | minimum w p ≤ linearWeight w x} := by
      intro x hx y hy a b ha hb hab
      change minimum w p ≤ linearWeight w (a • x + b • y)
      rw [linearWeight_add, linearWeight_smul, linearWeight_smul]
      calc
        minimum w p = a * minimum w p + b * minimum w p := by
          rw [← add_mul, hab, one_mul]
        _ ≤ a * linearWeight w x + b * linearWeight w y :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    apply convexHull_min ?_ hconv hx
    rintro _ ⟨e, he, rfl⟩
    change minimum w p ≤ linearWeight w (fun i => (e i : ℝ))
    rw [linearWeight_exponent]
    exact minimum_le w hp he

end FiniteVariables

end GraphicalZonotopes.PositivePolynomial

end
end
end AppendixNewtonPart0

section AppendixNewtonPart1
/- Source: Correspondence/TropicalContinuant.lean -/










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

end
end
end AppendixNewtonPart1

section AppendixNewtonPart2
/- Source: Correspondence/AppendixPositiveContinuant.lean -/





/-!
# A positive recurrence for the literal tridiagonal determinant

The pair `(D_k, E_k)` is defined over a fixed coefficient ring and a fixed
sequence of variables. A trailing Laplace expansion connects its first
coordinate to the determinant already used in Proposition A.2.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix

namespace GraphicalZonotopes.PathDeterminant

section PositiveRecurrence

variable {R : Type*} [CommSemiring R]

/-- The subtraction-free prefix recurrence. The first coordinate is `D_k`
and the second is the auxiliary polynomial `E_k`. -/
def positivePair (t : ℕ → R) : ℕ → R × R
  | 0 => (1, 1)
  | k + 1 =>
      let p := positivePair t k
      let e := t (k + 2) * p.1 + t k * p.2
      (e + t (k + 1) * p.1, e)

@[simp] theorem positivePair_zero (t : ℕ → R) : positivePair t 0 = (1, 1) := rfl

theorem positivePair_snd_succ (t : ℕ → R) (k : ℕ) :
    (positivePair t (k + 1)).2 =
      t (k + 2) * (positivePair t k).1 + t k * (positivePair t k).2 := rfl

theorem positivePair_fst_succ (t : ℕ → R) (k : ℕ) :
    (positivePair t (k + 1)).1 =
      (positivePair t (k + 1)).2 + t (k + 1) * (positivePair t k).1 := rfl

/-- A fixed ambient multivariate polynomial ring suffices for every prefix.
Only indices strictly below `m+2` are used when the prefix has length `m`. -/
def variableSequence (R : Type*) [CommSemiring R] (m : ℕ) (j : ℕ) :
    MvPolynomial (Fin (m + 2)) R :=
  MvPolynomial.X ⟨j % (m + 2), Nat.mod_lt _ (by omega)⟩

@[simp] theorem variableSequence_fin (R : Type*) [CommSemiring R] (m : ℕ)
    (j : Fin (m + 2)) : variableSequence R m j.val = MvPolynomial.X j := by
  unfold variableSequence
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

end PositiveRecurrence

section Ring

variable {R : Type*} [CommRing R]

/-- Deleting the last row and column retains the initial variable sequence. -/
theorem tridiagonal_init {m : ℕ} (t : Fin (m + 3) → R) :
    (tridiagonal t).submatrix Fin.castSucc Fin.castSucc =
      tridiagonal (fun j : Fin (m + 2) => t j.castSucc) := by
  ext i j
  simp only [Matrix.submatrix_apply, tridiagonal, ← Fin.castSucc_succ, Fin.castSucc_inj]

theorem tridiagonal_init_twice {m : ℕ} (t : Fin (m + 4) → R) :
    (tridiagonal t).submatrix (fun i : Fin m => i.castSucc.castSucc)
        (fun j : Fin m => j.castSucc.castSucc) =
      tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc) := by
  calc
    _ = ((tridiagonal t).submatrix Fin.castSucc Fin.castSucc).submatrix
        Fin.castSucc Fin.castSucc := rfl
    _ = _ := by rw [tridiagonal_init, tridiagonal_init]

theorem tridiagonal_last_castSucc_castSucc {m : ℕ} (t : Fin (m + 4) → R)
    (j : Fin m) :
    tridiagonal t (Fin.last (m + 1)) j.castSucc.castSucc = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega

theorem tridiagonal_castSucc_castSucc_last {m : ℕ} (t : Fin (m + 4) → R)
    (i : Fin m) :
    tridiagonal t i.castSucc.castSucc (Fin.last (m + 1)) = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega

private theorem sign_double (k : ℕ) : (-1 : R) ^ (k + k) = 1 := by
  rw [show k + k = 2 * k by omega, pow_mul]
  norm_num

private theorem sign_last_penultimate (k : ℕ) : (-1 : R) ^ (k + 1 + k) = -1 := by
  rw [show k + 1 + k = (k + k) + 1 by omega, pow_succ, sign_double, one_mul]

/-- The penultimate-column cofactor in the trailing Laplace expansion has
only one nonzero entry in its last column. -/
theorem tridiagonal_minor_penultimate_det {m : ℕ} (t : Fin (m + 4) → R) :
    ((tridiagonal t).submatrix Fin.castSucc (Fin.last m).castSucc.succAbove).det =
      -t (Fin.last (m + 1)).castSucc.castSucc *
        (tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc)).det := by
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    (tridiagonal t).submatrix Fin.castSucc (Fin.last m).castSucc.succAbove
  change N.det = _
  have hlast : N (Fin.last m) (Fin.last m) =
      -t (Fin.last (m + 1)).castSucc.castSucc := by
    change tridiagonal t (Fin.last m).castSucc
      ((Fin.last m).castSucc.succAbove (Fin.last m)) = _
    rw [Fin.succAbove_castSucc_self, Fin.succ_last]
    exact tridiagonal_above t (Fin.last m).castSucc (Fin.last (m + 1)) (by simp)
  have hzero : ∀ i : Fin m, N i.castSucc (Fin.last m) = 0 := by
    intro i
    change tridiagonal t i.castSucc.castSucc
      ((Fin.last m).castSucc.succAbove (Fin.last m)) = 0
    rw [Fin.succAbove_castSucc_self, Fin.succ_last]
    exact tridiagonal_castSucc_castSucc_last t i
  have hinit : N.submatrix Fin.castSucc Fin.castSucc =
      tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc) := by
    ext i j
    change tridiagonal t i.castSucc.castSucc
      ((Fin.last m).castSucc.succAbove j.castSucc) = _
    rw [Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last j)]
    exact congrFun (congrFun (tridiagonal_init_twice t) i) j
  rw [Matrix.det_succ_column N (Fin.last m), Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, hzero, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, sign_double, one_mul, Fin.succAbove_last]
  rw [hlast, hinit]

/-- The trailing continuant identity for the actual displayed matrix. -/
theorem tridiagonal_det_recurrence_right {m : ℕ} (t : Fin (m + 4) → R) :
    (tridiagonal t).det =
      (t (Fin.last (m + 1)).castSucc.castSucc +
        t (Fin.last (m + 1)).succ.castSucc + t (Fin.last (m + 1)).succ.succ) *
        (tridiagonal (fun j : Fin (m + 3) => t j.castSucc)).det -
      (t (Fin.last (m + 1)).castSucc.castSucc)^2 *
        (tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc)).det := by
  have hdiag := tridiagonal_diag t (Fin.last (m + 1))
  have hprev : tridiagonal t (Fin.last (m + 1)) (Fin.last m).castSucc =
      -t (Fin.last (m + 1)).castSucc.castSucc :=
    tridiagonal_below t (Fin.last (m + 1)) (Fin.last m).castSucc (by simp)
  rw [Matrix.det_succ_row (tridiagonal t) (Fin.last (m + 1)),
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, tridiagonal_last_castSucc_castSucc,
    mul_zero, zero_mul, Finset.sum_const_zero, zero_add, sign_double,
    sign_last_penultimate, one_mul, Fin.succAbove_last]
  rw [hdiag, hprev, tridiagonal_init, tridiagonal_minor_penultimate_det]
  ring

/-- The determinant of a prefix, over a fixed ambient coefficient ring. -/
def prefixDet (t : ℕ → R) (m : ℕ) : R :=
  (tridiagonal (fun j : Fin (m + 2) => t j.val)).det

@[simp] theorem prefixDet_zero (t : ℕ → R) : prefixDet t 0 = 1 := by
  simp [prefixDet]

theorem prefixDet_one (t : ℕ → R) : prefixDet t 1 = t 0 + t 1 + t 2 := by
  unfold prefixDet
  rw [Matrix.det_fin_one]
  simpa using tridiagonal_diag (fun j : Fin 3 => t j.val) 0

theorem prefixDet_recurrence (t : ℕ → R) (m : ℕ) :
    prefixDet t (m + 2) =
      (t (m + 1) + t (m + 2) + t (m + 3)) * prefixDet t (m + 1) -
        (t (m + 1))^2 * prefixDet t m := by
  unfold prefixDet
  simpa only [Fin.val_castSucc, Fin.val_last, Fin.val_succ] using
    tridiagonal_det_recurrence_right (fun j : Fin (m + 4) => t j.val)

theorem positivePair_fst_recurrence (t : ℕ → R) (m : ℕ) :
    (positivePair t (m + 2)).1 =
      (t (m + 1) + t (m + 2) + t (m + 3)) * (positivePair t (m + 1)).1 -
        (t (m + 1))^2 * (positivePair t m).1 := by
  simp only [positivePair]
  ring

/-- The positive recurrence agrees with the literal determinant at every
size. In particular, the recurrence does not redefine the paper's object. -/
theorem positivePair_fst_eq_prefixDet (t : ℕ → R) (m : ℕ) :
    (positivePair t m).1 = prefixDet t m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [prefixDet_one]
      simp only [positivePair, mul_one]
      ring
  | more m ih₀ ih₁ =>
      rw [positivePair_fst_recurrence, prefixDet_recurrence, ih₀, ih₁]

/-- The fixed-variable polynomial used in Proposition A.2 is exactly the
first coordinate of the subtraction-free recurrence. -/
theorem positivePair_polynomial (R : Type*) [CommRing R] (m : ℕ) :
    (positivePair (variableSequence R m) m).1 = polynomial R m := by
  simpa only [prefixDet, variableSequence_fin, polynomial] using
    positivePair_fst_eq_prefixDet (variableSequence R m) m

end Ring

end GraphicalZonotopes.PathDeterminant

end
end
end AppendixNewtonPart2

section AppendixNewtonPart3
/- Source: Correspondence/AppendixPositiveMinima.lean -/






/-!
# Support minima of the positive determinant recurrence

Both components of the positive recurrence have nonnegative coefficients
and are nonzero. Therefore their support minima obey the exact tropical
recurrence, with no cancellation premise left implicit.
-/

@[expose] public section
noncomputable section

namespace GraphicalZonotopes.PathDeterminant

open PositivePolynomial

variable {σ : Type*}

/-- Positivity and nonzeroness are propagated together at every prefix. -/
theorem positivePair_good (t : ℕ → MvPolynomial σ ℝ)
    (ht : ∀ j, Nonnegative (t j)) (ht0 : ∀ j, t j ≠ 0) (k : ℕ) :
    (Nonnegative (positivePair t k).1 ∧ (positivePair t k).1 ≠ 0) ∧
      (Nonnegative (positivePair t k).2 ∧ (positivePair t k).2 ≠ 0) := by
  induction k with
  | zero => exact ⟨⟨nonnegative_one, one_ne_zero⟩, ⟨nonnegative_one, one_ne_zero⟩⟩
  | succ k ih =>
      have hleft := nonnegative_mul (ht (k + 2)) ih.1.1
      have hright := nonnegative_mul (ht k) ih.2.1
      have hlast := nonnegative_mul (ht (k + 1)) ih.1.1
      have he : Nonnegative (positivePair t (k + 1)).2 := by
        rw [positivePair_snd_succ]
        exact nonnegative_add hleft hright
      have he0 : (positivePair t (k + 1)).2 ≠ 0 := by
        rw [positivePair_snd_succ]
        exact add_ne_zero_of_nonnegative hleft hright (mul_ne_zero (ht0 (k + 2)) ih.1.2)
      have hd : Nonnegative (positivePair t (k + 1)).1 := by
        rw [positivePair_fst_succ]
        exact nonnegative_add he hlast
      have hd0 : (positivePair t (k + 1)).1 ≠ 0 := by
        rw [positivePair_fst_succ]
        exact add_ne_zero_of_nonnegative he hlast he0
      exact ⟨⟨hd, hd0⟩, ⟨he, he0⟩⟩

/-- For arbitrary real weights, the two support minima satisfy exactly the
positive pair's tropical recurrence. The variables can repeat or be replaced
by any nonzero polynomial with nonnegative coefficients. -/
theorem positivePair_minimum (t : ℕ → MvPolynomial σ ℝ) (w : σ → ℝ)
    (ht : ∀ j, Nonnegative (t j)) (ht0 : ∀ j, t j ≠ 0) (m : ℕ) :
    (minimum w (positivePair t m).1, minimum w (positivePair t m).2) =
      TropicalContinuant.pair (fun j => minimum w (t j)) m := by
  refine TropicalContinuant.pair_eq_of_recurrences
    (fun j => minimum w (t j))
    (fun k => minimum w (positivePair t k).1)
    (fun k => minimum w (positivePair t k).2) ?_ ?_ ?_ ?_ m
  · simp
  · simp
  · intro k
    have h := positivePair_good t ht ht0 k
    rw [positivePair_snd_succ,
      minimum_add w (nonnegative_mul (ht (k + 2)) h.1.1)
        (nonnegative_mul (ht k) h.2.1)
        (mul_ne_zero (ht0 (k + 2)) h.1.2) (mul_ne_zero (ht0 k) h.2.2),
      minimum_mul w (ht (k + 2)) h.1.1 (ht0 (k + 2)) h.1.2,
      minimum_mul w (ht k) h.2.1 (ht0 k) h.2.2]
  · intro k
    have h := positivePair_good t ht ht0 k
    have hnext := positivePair_good t ht ht0 (k + 1)
    rw [positivePair_fst_succ,
      minimum_add w hnext.2.1 (nonnegative_mul (ht (k + 1)) h.1.1)
        hnext.2.2 (mul_ne_zero (ht0 (k + 1)) h.1.2),
      minimum_mul w (ht (k + 1)) h.1.1 (ht0 (k + 1)) h.1.2]

/-- Extend finitely many coordinate weights periodically. Every index used
by the determinant prefix lies in the original range. -/
def extendedWeights (m : ℕ) (w : Fin (m + 2) → ℝ) (j : ℕ) : ℝ :=
  w ⟨j % (m + 2), Nat.mod_lt _ (by omega)⟩

@[simp] theorem extendedWeights_fin (m : ℕ) (w : Fin (m + 2) → ℝ)
    (j : Fin (m + 2)) : extendedWeights m w j.val = w j := by
  unfold extendedWeights
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

theorem variableSequence_nonnegative (m j : ℕ) :
    Nonnegative (variableSequence ℝ m j) :=
  nonnegative_X _

theorem variableSequence_ne_zero (m j : ℕ) : variableSequence ℝ m j ≠ 0 :=
  MvPolynomial.X_ne_zero _

@[simp] theorem minimum_variableSequence (m : ℕ) (w : Fin (m + 2) → ℝ) (j : ℕ) :
    minimum w (variableSequence ℝ m j) = extendedWeights m w j := by
  exact minimum_X w _

/-- Nonnegative coefficients are proved for the actual determinant. -/
theorem polynomial_nonnegative (m : ℕ) : Nonnegative (polynomial ℝ m) := by
  rw [← positivePair_polynomial]
  exact (positivePair_good (variableSequence ℝ m)
    (variableSequence_nonnegative m) (variableSequence_ne_zero m) m).1.1

/-- Every real linear support minimum of the literal determinant is the
first component of the tropical recurrence. -/
theorem minimum_polynomial (m : ℕ) (w : Fin (m + 2) → ℝ) :
    minimum w (polynomial ℝ m) = TropicalContinuant.first (extendedWeights m w) m := by
  have h := positivePair_minimum (variableSequence ℝ m) w
    (variableSequence_nonnegative m) (variableSequence_ne_zero m) m
  have hf := congrArg Prod.fst h
  change minimum w (positivePair (variableSequence ℝ m) m).1 =
    TropicalContinuant.first (fun j => minimum w (variableSequence ℝ m j)) m at hf
  rw [positivePair_polynomial] at hf
  simpa only [minimum_variableSequence] using hf

/-- The explicit triple/quadruple minimum formula for the determinant. -/
theorem minimum_polynomial_eq_closedFormula (m : ℕ) (w : Fin (m + 2) → ℝ) :
    minimum w (polynomial ℝ m) = TropicalContinuant.closedFormula (extendedWeights m w) m := by
  rw [minimum_polynomial, TropicalContinuant.first_eq_closedFormula]

end GraphicalZonotopes.PathDeterminant

end
end
end AppendixNewtonPart3

section AppendixNewtonPart4
/- Source: Correspondence/PathNewtonMinima.lean -/






/-!
# Every real linear minimum of the path polytope

The path set function is the sum of its triple and gap-triple unanimity functions
minus its quadruple unanimity functions. Minkowski addition of genuine base
polytopes turns this identity into an equality of linear minima. The resulting
formula is exactly the minimum-plus positive-continuant formula.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes.PathNewtonMinima

open Finset TropicalContinuant

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary linear functional specified by a vector of real weights. -/
def weightMap (w : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ v, w v * x v
  map_add' x y := by simp [mul_add, sum_add_distrib]
  map_smul' a x := by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- An attained minimum of the actual linear functional on the actual set. -/
def HasMinimum (w : V → ℝ) (Q : Set (V → ℝ)) (a : ℝ) : Prop :=
  IsLeast (weightMap w '' Q) a

@[simp] theorem weightMap_apply (w x : V → ℝ) : weightMap w x = ∑ v, w v * x v := rfl

@[simp] theorem weightMap_basisVector (w : V → ℝ) (v : V) :
    weightMap w (basisVector v) = w v := by
  simp [weightMap, basisVector, Pi.single_apply, mul_ite, eq_comm]

/-- Attained linear minima add under actual Minkowski addition. -/
theorem minimum_add {w : V → ℝ} {Q R : Set (V → ℝ)} {a b : ℝ}
    (hQ : HasMinimum w Q a) (hR : HasMinimum w R b) :
    HasMinimum w (Q + R) (a + b) := by
  rcases hQ.1 with ⟨x, hx, hxa⟩
  rcases hR.1 with ⟨y, hy, hyb⟩
  refine ⟨⟨x + y, Set.add_mem_add hx hy, by rw [map_add, hxa, hyb]⟩, ?_⟩
  rintro t ⟨z, ⟨u, hu, v, hv, rfl⟩, rfl⟩
  rw [map_add]
  exact add_le_add (hQ.2 ⟨u, hu, rfl⟩) (hR.2 ⟨v, hv, rfl⟩)

/-- Cancellation of an attained linear minimum from a Minkowski sum. -/
theorem minimum_of_add {w : V → ℝ} {Q R : Set (V → ℝ)} {a b : ℝ}
    (hQR : HasMinimum w (Q + R) a) (hR : HasMinimum w R b) :
    HasMinimum w Q (a - b) := by
  rcases hR.1 with ⟨y, hy, hyb⟩
  have lower : ∀ x ∈ Q, a - b ≤ weightMap w x := by
    intro x hx
    have h := hQR.2 ⟨x + y, Set.add_mem_add hx hy, rfl⟩
    rw [map_add, hyb] at h
    linarith
  rcases hQR.1 with ⟨z, ⟨x, hx, u, hu, rfl⟩, hza⟩
  have huLower := hR.2 ⟨u, hu, rfl⟩
  have hxLower := lower x hx
  have hxEq : weightMap w x = a - b := by
    rw [map_add] at hza
    linarith
  refine ⟨⟨x, hx, hxEq⟩, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  exact lower x hx

/-- A unanimity base polytope has the expected minimum over its supported basis
vectors. The argument allows every nonempty support, including a singleton. -/
theorem minimum_setMonomial (C : Finset V) (w : V → ℝ) (a : ℝ)
    (ha : IsLeast (w '' (C : Set V)) a) :
    HasMinimum w (basePolytope (setMonomial C)) a := by
  rcases ha.1 with ⟨v, hv, hva⟩
  have hvBase : basisVector v ∈ basePolytope (setMonomial C) := by
    refine ⟨by simp [setMonomial], ?_⟩
    intro S
    rw [subsetSum_basisVector]
    by_cases hCS : C ⊆ S
    · simp [setMonomial, hCS, hCS hv]
    · simp only [setMonomial, if_neg hCS]
      split_ifs <;> norm_num
  refine ⟨⟨basisVector v, hvBase, (weightMap_basisVector w v).trans hva⟩, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  have htotal : subsetSum x univ = 1 := by simpa [setMonomial] using hx.1
  have hnonnegative : ∀ j, 0 ≤ x j := by
    intro j
    have hzero : 0 ≤ setMonomial C {j} := by
      unfold setMonomial
      split_ifs <;> norm_num
    have h := hx.2 {j}
    simpa [subsetSum] using hzero.trans h
  have houtside : ∀ j, j ∉ C → x j = 0 := by
    intro j hj
    have hCS : C ⊆ univ.erase j := by
      intro k hk
      exact mem_erase.mpr ⟨fun h => hj (h ▸ hk), mem_univ k⟩
    have hmin : 1 ≤ subsetSum x (univ.erase j) := by
      simpa [setMonomial, hCS] using hx.2 (univ.erase j)
    have hsum : subsetSum x (univ.erase j) + x j = 1 := by
      rw [subsetSum, sum_erase_add _ _ (mem_univ j)]
      exact htotal
    linarith [hnonnegative j]
  have hsum : (∑ j ∈ C, x j) = 1 := by
    calc
      (∑ j ∈ C, x j) = ∑ j ∈ univ, x j :=
        sum_subset (subset_univ _) (fun j _ hj => houtside j hj)
      _ = 1 := htotal
  have hweight : (∑ j ∈ C, w j * x j) = weightMap w x := by
    change (∑ j ∈ C, w j * x j) = ∑ j ∈ univ, w j * x j
    apply sum_subset (subset_univ _)
    intro j _ hj
    simp [houtside j hj]
  calc
    a = a * (∑ j ∈ C, x j) := by rw [hsum, mul_one]
    _ = ∑ j ∈ C, a * x j := by rw [mul_sum]
    _ ≤ ∑ j ∈ C, w j * x j := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (ha.2 ⟨j, hj, rfl⟩) (hnonnegative j)
    _ = weightMap w x := hweight

private theorem image_three_minimum (w : V → ℝ) (a b c : V) :
    IsLeast (w '' (({a, b, c} : Finset V) : Set V))
      (min (w a) (min (w b) (w c))) := by
  simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, Set.singleton_union] using
    (isLeast_singleton : IsLeast ({w a} : Set ℝ) (w a)).union
      ((isLeast_singleton : IsLeast ({w b} : Set ℝ) (w b)).union (isLeast_singleton : IsLeast ({w c} : Set ℝ) (w c)))

private theorem image_four_minimum (w : V → ℝ) (a b c d : V) :
    IsLeast (w '' (({a, b, c, d} : Finset V) : Set V))
      (min (w a) (min (w b) (min (w c) (w d)))) := by
  simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, Set.singleton_union] using
    (isLeast_singleton : IsLeast ({w a} : Set ℝ) (w a)).union
      ((isLeast_singleton : IsLeast ({w b} : Set ℝ) (w b)).union
        ((isLeast_singleton : IsLeast ({w c} : Set ℝ) (w c)).union (isLeast_singleton : IsLeast ({w d} : Set ℝ) (w d))))

/-- Linear minima of a finite sum of normalized supermodular functions. -/
theorem minimum_basePolytope_sum {I : Type*} (s : Finset I)
    (f : I → SetFunction V) (w : V → ℝ) (a : I → ℝ)
    (hn : ∀ i ∈ s, Normalized (f i))
    (hs : ∀ i ∈ s, Supermodular (f i))
    (hm : ∀ i ∈ s, HasMinimum w (basePolytope (f i)) (a i)) :
    HasMinimum w (basePolytope (∑ i ∈ s, f i)) (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa [HasMinimum, basePolytope_zero] using (isLeast_singleton : IsLeast ({0} : Set ℝ) 0)
  | @insert i s hi ih =>
      have hns : Normalized (∑ j ∈ s, f j) := by
        simp only [Normalized, Finset.sum_apply]
        exact sum_eq_zero (fun j hj => hn j (mem_insert_of_mem hj))
      have hss : Supermodular (∑ j ∈ s, f j) :=
        Supermodular.finset_sum s f (fun j hj => hs j (mem_insert_of_mem hj))
      simp only [sum_insert hi]
      rw [basePolytope_add (hn i (mem_insert_self _ _)) hns
        (hs i (mem_insert_self _ _)) hss]
      exact minimum_add (hm i (mem_insert_self _ _))
        (ih (fun j hj => hn j (mem_insert_of_mem hj))
          (fun j hj => hs j (mem_insert_of_mem hj))
          (fun j hj => hm j (mem_insert_of_mem hj)))

private theorem window_nonempty {n p : ℕ} (i : Fin (n - p))
    (C : Finset ℕ) (hC : 0 ∈ C) : (Path.window n i.val C).Nonempty := by
  have hi : i.val < n := i.isLt.trans_le (Nat.sub_le n p)
  refine ⟨⟨i.val, hi⟩, ?_⟩
  simp [Path.mem_window, hC]

private theorem minimum_triple {n : ℕ} (w : ℕ → ℝ) (i : Fin (n - 2)) :
    HasMinimum (fun v : Fin n => w v.val)
      (basePolytope (setMonomial (Path.window n i.val {0, 1, 2})))
      (tripleMinimum w i.val) := by
  apply minimum_setMonomial
  rw [Path.window_triple_eq
    (Path.window_index_bound i (by decide : 0 ≤ 2))
    (Path.window_index_bound i (by decide : 1 ≤ 2))
    (Path.window_index_bound i (by decide : 2 ≤ 2))]
  simpa [tripleMinimum, Path.vertex] using
    image_three_minimum (fun v : Fin n => w v.val)
      (Path.vertex n i.val 0 (Path.window_index_bound i (by decide : 0 ≤ 2)))
      (Path.vertex n i.val 1 (Path.window_index_bound i (by decide : 1 ≤ 2)))
      (Path.vertex n i.val 2 (Path.window_index_bound i (by decide : 2 ≤ 2)))

private theorem minimum_gap {n : ℕ} (w : ℕ → ℝ) (i : Fin (n - 3)) :
    HasMinimum (fun v : Fin n => w v.val)
      (basePolytope (setMonomial (Path.window n i.val {0, 2, 3})))
      (gapMinimum w i.val) := by
  apply minimum_setMonomial
  rw [Path.window_triple_eq
    (Path.window_index_bound i (by decide : 0 ≤ 3))
    (Path.window_index_bound i (by decide : 2 ≤ 3))
    (Path.window_index_bound i (by decide : 3 ≤ 3))]
  simpa [gapMinimum, Path.vertex] using
    image_three_minimum (fun v : Fin n => w v.val)
      (Path.vertex n i.val 0 (Path.window_index_bound i (by decide : 0 ≤ 3)))
      (Path.vertex n i.val 2 (Path.window_index_bound i (by decide : 2 ≤ 3)))
      (Path.vertex n i.val 3 (Path.window_index_bound i (by decide : 3 ≤ 3)))

private theorem minimum_quadruple {n : ℕ} (w : ℕ → ℝ) (i : Fin (n - 3)) :
    HasMinimum (fun v : Fin n => w v.val)
      (basePolytope (setMonomial (Path.window n i.val {0, 1, 2, 3})))
      (quadrupleMinimum w i.val) := by
  apply minimum_setMonomial
  rw [Path.window_quad_eq
    (Path.window_index_bound i (by decide : 0 ≤ 3))
    (Path.window_index_bound i (by decide : 1 ≤ 3))
    (Path.window_index_bound i (by decide : 2 ≤ 3))
    (Path.window_index_bound i (by decide : 3 ≤ 3))]
  simpa [quadrupleMinimum, Path.vertex] using
    image_four_minimum (fun v : Fin n => w v.val)
      (Path.vertex n i.val 0 (Path.window_index_bound i (by decide : 0 ≤ 3)))
      (Path.vertex n i.val 1 (Path.window_index_bound i (by decide : 1 ≤ 3)))
      (Path.vertex n i.val 2 (Path.window_index_bound i (by decide : 2 ≤ 3)))
      (Path.vertex n i.val 3 (Path.window_index_bound i (by decide : 3 ≤ 3)))

/-- The exact local support formula for every real linear functional on the path
base polytope, including attainment of the minimum. -/
theorem path_polytope_minimum_formula (n : ℕ) (w : ℕ → ℝ) :
    HasMinimum (fun v : Fin n => w v.val) (Path.polytope n)
      ((∑ i : Fin (n - 2), tripleMinimum w i.val) +
        (∑ i : Fin (n - 3), gapMinimum w i.val) -
        (∑ i : Fin (n - 3), quadrupleMinimum w i.val)) := by
  let f : Fin (n - 2) → SetFunction (Fin n) := fun i =>
    setMonomial (Path.window n i.val {0, 1, 2})
  let g : Fin (n - 3) → SetFunction (Fin n) := fun i =>
    setMonomial (Path.window n i.val {0, 2, 3})
  let h : Fin (n - 3) → SetFunction (Fin n) := fun i =>
    setMonomial (Path.window n i.val {0, 1, 2, 3})
  have hfn : ∀ i, Normalized (f i) := fun i =>
    setMonomial_normalized (window_nonempty i _ (by simp))
  have hgn : ∀ i, Normalized (g i) := fun i =>
    setMonomial_normalized (window_nonempty i _ (by simp))
  have hhn : ∀ i, Normalized (h i) := fun i =>
    setMonomial_normalized (window_nonempty i _ (by simp))
  have hfs : ∀ i, Supermodular (f i) := fun i => setMonomial_supermodular _
  have hgs : ∀ i, Supermodular (g i) := fun i => setMonomial_supermodular _
  have hhs : ∀ i, Supermodular (h i) := fun i => setMonomial_supermodular _
  have hfmin := minimum_basePolytope_sum univ f (fun v : Fin n => w v.val)
    (fun i => tripleMinimum w i.val) (fun i _ => hfn i) (fun i _ => hfs i)
    (fun i _ => minimum_triple w i)
  have hgmin := minimum_basePolytope_sum univ g (fun v : Fin n => w v.val)
    (fun i => gapMinimum w i.val) (fun i _ => hgn i) (fun i _ => hgs i)
    (fun i _ => minimum_gap w i)
  have hhmin := minimum_basePolytope_sum univ h (fun v : Fin n => w v.val)
    (fun i => quadrupleMinimum w i.val) (fun i _ => hhn i) (fun i _ => hhs i)
    (fun i _ => minimum_quadruple w i)
  have hsumNorm (I : Type) [Fintype I] (q : I → SetFunction (Fin n))
      (hq : ∀ i, Normalized (q i)) : Normalized (∑ i, q i) := by
    simp only [Normalized, Finset.sum_apply]
    exact sum_eq_zero (fun i _ => hq i)
  have hsumSuper (I : Type) [Fintype I] (q : I → SetFunction (Fin n))
      (hq : ∀ i, Supermodular (q i)) : Supermodular (∑ i, q i) :=
    Supermodular.finset_sum univ q (fun i _ => hq i)
  have hidentity : Path.setFunction n + ∑ i, h i = (∑ i, f i) + ∑ i, g i := by
    rw [Path.setFunction_expansion]
    change ((∑ i, f i) + (∑ i, g i) - (∑ i, h i)) + (∑ i, h i) = _
    abel
  have hpoly : Path.polytope n + basePolytope (∑ i, h i) =
      basePolytope (∑ i, f i) + basePolytope (∑ i, g i) := by
    rw [Path.polytope, ← basePolytope_add
      (z := Path.setFunction n) (w := ∑ i, h i)
      (Path.setFunction_normalized n).1 (hsumNorm (Fin (n - 3)) h hhn)
      (Path.setFunction_supermodular n) (hsumSuper (Fin (n - 3)) h hhs),
      hidentity, basePolytope_add (z := ∑ i, f i) (w := ∑ i, g i)
        (hsumNorm (Fin (n - 2)) f hfn) (hsumNorm (Fin (n - 3)) g hgn)
        (hsumSuper (Fin (n - 2)) f hfs) (hsumSuper (Fin (n - 3)) g hgs)]
  have hminimum := minimum_add hfmin hgmin
  rw [← hpoly] at hminimum
  exact minimum_of_add hminimum hhmin

/-- The minimum of any real linear functional on the actual path polytope is the
first minimum-plus continuant coordinate. There is no hypothesis on the weights. -/
theorem path_polytope_minimum (m : ℕ) (w : ℕ → ℝ) :
    IsLeast ((fun x : Fin (m + 2) → ℝ => ∑ i, w i.val * x i) ''
      Path.polytope (m + 2)) (TropicalContinuant.first w m) := by
  change HasMinimum (fun v : Fin (m + 2) => w v.val) (Path.polytope (m + 2))
    (TropicalContinuant.first w m)
  have h := path_polytope_minimum_formula (m + 2) w
  rw [TropicalContinuant.first_eq_closedFormula]
  simpa only [TropicalContinuant.closedFormula, Nat.add_sub_cancel,
    show m + 2 - 3 = m - 1 by omega, Fin.sum_univ_eq_sum_range] using h

/-- Every continuous linear functional on the finite coordinate space is the
ordinary weighted sum of its values on the standard basis. -/
theorem weightMap_of_functional (f : (V → ℝ) →L[ℝ] ℝ) (x : V → ℝ) :
    weightMap (fun v => f (Pi.single v 1)) x = f x := by
  change (∑ v, f (Pi.single v 1) * x v) = f x
  rw [linearFunctional_eq_weighted_sum f x]
  exact sum_congr rfl (fun v _ => mul_comm _ _)

/-- A closed convex set is determined by the attained minima of all real linear
functionals. The comparison set need not itself be convex for this inclusion. -/
theorem subset_of_same_linear_minima {Q R : Set (V → ℝ)}
    (hRconvex : Convex ℝ R) (hRclosed : IsClosed R)
    (hmin : ∀ w : V → ℝ, ∃ a, HasMinimum w Q a ∧ HasMinimum w R a) : Q ⊆ R := by
  intro x hx
  by_contra hout
  obtain ⟨f, c, hxc, hcf⟩ := geometric_hahn_banach_point_closed hRconvex hRclosed hout
  obtain ⟨a, hQmin, hRmin⟩ := hmin (fun v => f (Pi.single v 1))
  have hxa : a ≤ f x := by
    simpa only [weightMap_of_functional] using hQmin.2 ⟨x, hx, rfl⟩
  rcases hRmin.1 with ⟨y, hy, hya⟩
  have hya' : f y = a := by simpa only [weightMap_of_functional] using hya
  have hcy := hcf y hy
  linarith

/-- Equality of actual closed convex sets from their full real linear minima. -/
theorem eq_of_same_linear_minima {Q R : Set (V → ℝ)}
    (hQconvex : Convex ℝ Q) (hQclosed : IsClosed Q)
    (hRconvex : Convex ℝ R) (hRclosed : IsClosed R)
    (hmin : ∀ w : V → ℝ, ∃ a, HasMinimum w Q a ∧ HasMinimum w R a) : Q = R := by
  apply Set.Subset.antisymm (subset_of_same_linear_minima hRconvex hRclosed hmin)
  apply subset_of_same_linear_minima hQconvex hQclosed
  intro w
  obtain ⟨a, hQmin, hRmin⟩ := hmin w
  exact ⟨a, hRmin, hQmin⟩

end GraphicalZonotopes.PathNewtonMinima

end
end
end AppendixNewtonPart4

section AppendixNewtonPart5
/- Source: Correspondence/AppendixNewtonPolytope.lean -/






/-!
# The literal determinant has exactly the path Newton polytope

The positive determinant recurrence and the actual path base polytope have
the same attained minimum for every real coordinate weight. Separation of
closed convex sets therefore proves their equality. No generic Newton-product
formula, graphic-matroid representation, or spanning-tree enumeration is
assumed in this argument.

Together with the separately proved determinant stability, degree and
characteristic-independent irreducibility, this closes Proposition A.2.
-/

@[expose] public section

noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.PathDeterminant

open PositivePolynomial NewtonGeometry PathNewtonMinima

/-- The ordinary real Newton polytope of the displayed determinant is the
literal lower base polytope of the paper's path set function, at every size.
In particular, the theorem includes the empty determinant and its point polytope. -/
theorem polynomial_newtonPolytope (m : ℕ) :
    newtonPolytope (polynomial ℝ m) = Path.polytope (m + 2) := by
  apply eq_of_same_linear_minima
    (newton_lattice (polynomial ℝ m)).convex
    (newton_lattice (polynomial ℝ m)).compact.isClosed
    (Path.polytope_lattice (m + 2)).convex
    (Path.polytope_compact (m + 2)).isClosed
  intro w
  refine ⟨minimum w (polynomial ℝ m), ?_, ?_⟩
  · exact minimum_isLeast_convexHull w (polynomial_ne_zero m)
  · rw [minimum_polynomial]
    change IsLeast ((fun x : Fin (m + 2) → ℝ => ∑ i, w i * x i) ''
      Path.polytope (m + 2)) (TropicalContinuant.first (extendedWeights m w) m)
    simpa only [extendedWeights_fin] using
      path_polytope_minimum m (extendedWeights m w)

/-- All assertions of Proposition A.2 for the determinant as defined by the
displayed matrix. The real Newton identity holds in characteristic zero;
absolute irreducibility is quantified independently over every field.
The paper uses `m = n - 2 ≥ 2`; this statement also includes `m = 1`. -/
theorem proposition_A_2 (K : Type*) [Field K] (m : ℕ) (hm : 0 < m) :
    newtonPolytope (polynomial ℝ m) = Path.polytope (m + 2) ∧
    (polynomial ℝ m).IsHomogeneous m ∧
    (polynomial ℝ m).totalDegree = m ∧
    IsRealStable (polynomial ℝ m) ∧
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
      (polynomial K m)) :=
  ⟨polynomial_newtonPolytope m, polynomial_homogeneous ℝ m,
    polynomial_totalDegree m, polynomial_realStable m,
    proposition_A_2_absoluteIrreducible K m hm⟩

end GraphicalZonotopes.PathDeterminant

end
end
end AppendixNewtonPart5

#print_proof_audit_bundle [
  GraphicalZonotopes.Path.principal_path_theorem,
  GraphicalZonotopes.Path.polytope_defining_equations,
  GraphicalZonotopes.Path.polytope_defining_equations_real,
  GraphicalZonotopes.Path.polytope_defining_equations_sums,
  GraphicalZonotopes.Path.setFunction_expansion,
  GraphicalZonotopes.Path.every_exposed_edge_is_graph_direction,
  GraphicalZonotopes.generalizedPermutahedron_iff_weak_complete,
  GraphicalZonotopes.minkowskiIndecomposable_iff_polytopal,
  GraphicalZonotopes.sharp_direction_bounds,
  GraphicalZonotopes.generalizedPermutahedron_exposed_edge_is_root,
  GraphicalZonotopes.root_parallel_pair_eq,
  GraphicalZonotopes.direction_bounds_polytopal,
  GraphicalZonotopes.ExtremeSupermodular.spanning_tetrahedra,
  GraphicalZonotopes.edge_bound_of_connected_tetrahedra,
  GraphicalZonotopes.maximum_degree_bound_of_connected_tetrahedra,
  GraphicalZonotopes.Path.setFunction_eq_booleanFormula,
  GraphicalZonotopes.Path.polytope_boolean_defining_equations,
  GraphicalZonotopes.DoubledParts.principal_boolean_phase_theorem,
  GraphicalZonotopes.BooleanFourier.boolean_face_line,
  GraphicalZonotopes.BooleanFourier.faceKernel_finrank,
  GraphicalZonotopes.threeTree_classification_polytopal,
  GraphicalZonotopes.threeTree_classification,
  GraphicalZonotopes.threeTree_classification_literal,
  GraphicalZonotopes.admissible_threeTree_lattice_witness,
  GraphicalZonotopes.threeTree_lattice_dilation_sharp,
  GraphicalZonotopes.threeTree_lattice_lower_bound_polytopal,
  GraphicalZonotopes.Separator.induced_separator_capacity_finite,
  GraphicalZonotopes.Separator.positive_response_gluing_finite,
  GraphicalZonotopes.Separator.clique_separator_capacity_finite,
  GraphicalZonotopes.unit_lattice_classification_sharp,
  GraphicalZonotopes.unit_lattice_classification_polytopal,
  GraphicalZonotopes.unit_translated_lattice_classification_polytopal,
  GraphicalZonotopes.threeTree_translated_lattice_lower_bound,
  GraphicalZonotopes.FourPartCompletion.cartesian_completion,
  GraphicalZonotopes.four_partite_spanning_threeTrees,
  GraphicalZonotopes.four_partite_threeTree_dimension_attained,
  GraphicalZonotopes.threeTree_actual_dimension_admissible,
  GraphicalZonotopes.admissible_threeTree_active_witness,
  GraphicalZonotopes.maximumThreeTreeSupportDimension_eq_polytopal,
  GraphicalZonotopes.optimal_k5_free_dilation,
  GraphicalZonotopes.optimal_k5_free_dilation_attained,
  GraphicalZonotopes.optimal_k5_free_dilation_lower_bound_polytopal,
  GraphicalZonotopes.DoubledParts.one_singleton_decomposition,
  GraphicalZonotopes.FourSmallParts.four_small_parts_decomposition,
  GraphicalZonotopes.boolean_decomposition_every_dimension,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books,
  GraphicalZonotopes.BooleanModule.one_outer_lattice_book,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1,
  GraphicalZonotopes.DiamondBook.maximum_dimension,
  GraphicalZonotopes.DiamondBook.diamond_witness_multipartite,
  GraphicalZonotopes.DiamondBook.no_supporting_spanning_threeTree,
  GraphicalZonotopes.BooleanModule.positive_star_interpolation,
  GraphicalZonotopes.BooleanModule.negative_star_interpolation,
  GraphicalZonotopes.BooleanModule.threshold_book_interval,
  GraphicalZonotopes.BooleanModule.book_upper_interval,
  GraphicalZonotopes.maximumIndecomposableDimension_eq_polytopal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_polytopal,
  GraphicalZonotopes.not_fullLatticeSummandAt_zero,
  GraphicalZonotopes.PathJoin.corollary_nine_four,
  GraphicalZonotopes.PathJoin.appendix_B_one,
  GraphicalZonotopes.clique_book_classification,
  GraphicalZonotopes.clique_book_classification_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_geometric,
  GraphicalZonotopes.saturatedHubNeighbors_closed_formula,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2_polytopal,
  GraphicalZonotopes.TwoHub.exponential_lattice_summand,
  GraphicalZonotopes.TwoHub.exponential_family,
  GraphicalZonotopes.TwoHub.exponential_polytopal_summand,
  GraphicalZonotopes.TwoHub.two_singleton_classification,
  GraphicalZonotopes.TwoHub.classification_polytopal,
  GraphicalZonotopes.TwoHub.full_polytopal_iff,
  GraphicalZonotopes.TwoHub.lattice_polytopal_attainment,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum,
  GraphicalZonotopes.threeTree_dimension_and_spectrum,
  GraphicalZonotopes.partial_threeTree_support_classification_polytopal_finite,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum_finite,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum_polytopal_finite,
  GraphicalZonotopes.SupportsFullIndecomposable.triangle_free_components_le_one,
  GraphicalZonotopes.SupportsFullIndecomposable.separator_contains_triangle,
  GraphicalZonotopes.SupportsFullIndecomposable.delete_lt_three_preconnected,
  GraphicalZonotopes.weak_summand_exposed_edge_direction,
  GraphicalZonotopes.weakSummand_indecomposable_iff_polytopal,
  GraphicalZonotopes.isWeakMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.isMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.partial_threeTree_polytope_support,
  GraphicalZonotopes.BooleanModule.cliqueCapacity_int_formula,
  GraphicalZonotopes.TwoHub.paper_corollary_8_5,
  GraphicalZonotopes.HamiltonianDeletion.hamiltonian_component_card_delete_le,
  GraphicalZonotopes.IsThreeTree.admissible_of_hamiltonian,
  GraphicalZonotopes.hamiltonian_threeTree_lattice_polytopal_finite,
  GraphicalZonotopes.actualEdgeDirectionLines_finite,
  GraphicalZonotopes.directionCount_eq_geometric_line_count,
  GraphicalZonotopes.three_hub_book_maximum,
  GraphicalZonotopes.TreeJoin.induced_subcubic_iff_subtree,
  GraphicalZonotopes.TreeJoin.maximum_dimension,
  GraphicalZonotopes.TreeJoin.supports_full_iff,
  GraphicalZonotopes.TreeJoin.paper_corollary_6_9_tree_join,
  GraphicalZonotopes.SparseFamily.complete_family,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_valid,
  GraphicalZonotopes.TwoHub.CellDecisionTree.leaves_card,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_proper,
  GraphicalZonotopes.TwoHub.PartitionData.partitionDilation_eq,
  GraphicalZonotopes.TwoHub.decision_tree_lattice_summand,
  GraphicalZonotopes.TwoHub.paper_lemma_8_6,
  GraphicalZonotopes.paper_corollary_6_4,
  GraphicalZonotopes.paper_corollary_6_4_stacked,
  GraphicalZonotopes.paper_corollary_6_5,
  GraphicalZonotopes.planar_threeTree_lattice_witness_finite,
  GraphicalZonotopes.HasPlaneDrawing.triangle_apex_separated,
  GraphicalZonotopes.TetrahedronComponents.maximumDimension_eq,
  GraphicalZonotopes.TetrahedronComponents.adj_iff_shared_triangle,
  GraphicalZonotopes.boundaryTriangles_after_attachment,
  Graph.IsArcK5.elim,
  GraphicalZonotopes.paper_corollary_5_2,
  GraphicalZonotopes.full_generalized_permutahedron_triangle_separators,
  GraphicalZonotopes.unit_lattice_active_classification_finite,
  GraphicalZonotopes.HasPlaneStraightLineDrawing.hasPlaneDrawing,
  GraphicalZonotopes.PathDrawing.path_hasPlaneDrawing,
  GraphicalZonotopes.IsPartialThreeTree.incidence_isAcyclic,
  GraphicalZonotopes.PolynomialWeights.minWeight_mul,
  GraphicalZonotopes.PolynomialWeights.maxWeight_mul,
  GraphicalZonotopes.BookSpectrum.prescribed_coordinate_criterion,
  GraphicalZonotopes.BookSpectrum.lattice_dimension_spectrum,
  GraphicalZonotopes.BookSpectrum.positive_dimension_spectrum,
  GraphicalZonotopes.Polyhedral.minimal_face_tight_kernel,
  GraphicalZonotopes.Polyhedral.extremeRay_iff_minimal_face_span,
  GraphicalZonotopes.Polyhedral.extremeRay_iff_minimal_face_finrank,
  GraphicalZonotopes.Separator.positive_response_gluing_minimal_face_finite,
  GraphicalZonotopes.NewtonGeometry.newton_mul_of_basePolytope,
  GraphicalZonotopes.NewtonGeometry.irreducible_of_newton_base_extreme_unit_slack,
  GraphicalZonotopes.NewtonGeometry.corollary_A_3_absoluteIrreducible,
  GraphicalZonotopes.PathDeterminant.proposition_A_2_stability,
  GraphicalZonotopes.PathDeterminant.proposition_A_2_absoluteIrreducible,
  GraphicalZonotopes.PathDeterminant.polynomial_irreducible,
  GraphicalZonotopes.PathDeterminant.polynomial_irreducible_map,
  GraphicalZonotopes.PathDeterminant.tridiagonal_det_recurrence,
  GraphicalZonotopes.PathDeterminant.polynomial_newtonPolytope,
  GraphicalZonotopes.PathDeterminant.proposition_A_2
]
