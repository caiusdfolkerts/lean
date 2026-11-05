module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

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
