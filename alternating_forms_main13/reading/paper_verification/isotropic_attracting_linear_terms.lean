module

public import PaperVerification.IsotropicAttractingCoordinates
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Exact linear terms of the attracting-chart equations

The coefficient of each variable is computed in the literal polynomial
equation.  This separates the two possible linear terms from quadratic
terms, whose variables have smaller positive weight.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

/-- The product rule for the coefficient of a single variable. -/
theorem coeff_single_mul (f g : MvPolynomial σ R) (i : σ) :
    (f*g).coeff (Finsupp.single i 1) =
      f.coeff (Finsupp.single i 1) * g.constantCoeff +
        f.constantCoeff * g.coeff (Finsupp.single i 1) := by
  have h := congrArg (fun q : MvPolynomial σ R => q.constantCoeff)
    (pderiv_mul (i := i) (f := f) (g := g))
  simpa only [map_add, map_mul, constantCoeff_eq, coeff_pderiv,
    Finsupp.zero_apply, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using h

/-- A variable in a positive-weight homogeneous polynomial either has
smaller weight, or already occurs in the polynomial's linear part. -/
theorem vars_lt_weight_or_linear (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (f : MvPolynomial σ R) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (j : σ) (hj : j ∈ f.vars) :
    w j < d ∨ f.coeff (Finsupp.single j 1) ≠ 0 := by
  classical
  letI : Finsupp.NonTorsionWeight ℕ w :=
    Finsupp.nonTorsionWeight_of ℕ w (fun i => ne_of_gt (hw i))
  obtain ⟨a, ha, hja⟩ := (mem_vars_iff_mem_support (p := f) j).mp hj
  by_cases he : a = Finsupp.single j 1
  · right
    simpa only [he] using mem_support_iff.mp ha
  · left
    have haj : a j ≠ 0 := Finsupp.mem_support_iff.mp hja
    have hd : Finsupp.weight w a = d := hf (mem_support_iff.mp ha)
    have hres : a - Finsupp.single j 1 ≠ 0 := by
      intro hz
      apply he
      have hh := Finsupp.sub_add_single_one_cancel haj
      rw [hz, zero_add] at hh
      exact hh.symm
    have hpos : 0 < Finsupp.weight w (a - Finsupp.single j 1) :=
      Nat.pos_of_ne_zero (fun hz => hres ((Finsupp.weight_eq_zero_iff_eq_zero w).mp hz))
    have hh := Finsupp.weight_sub_single_add (w := w) haj
    rw [hd] at hh
    omega

variable {n s : ℕ}

@[simp] theorem row_constantCoeff (p : Fin s ↪ Fin n) (i : Fin s) (j : Fin n) :
    (row (R := R) p i j).constantCoeff = if j = p i then 1 else 0 := by
  classical
  rw [row]
  split
  · simp_all
  · split
    · change (X (⟨(i,j), ‹_›⟩ : Coordinate p) : MvPolynomial (Coordinate p) R).constantCoeff = _
      simp_all
    · simp_all

/-- The universal row has exactly its specified variable as linear term. -/
theorem row_coeff_single (p : Fin s ↪ Fin n) (i : Fin s) (j : Fin n)
    (v : Coordinate p) :
    (row (R := R) p i j).coeff (Finsupp.single v 1) =
      if v.val.1 = i ∧ v.val.2 = j then 1 else 0 := by
  classical
  by_cases h : j = p i
  · have hn : ¬ (v.val.1 = i ∧ v.val.2 = j) := by
      rintro ⟨hi, hv⟩
      apply v.property.2
      exact ⟨i, h.symm.trans hv.symm⟩
    have hzero : (0 : Coordinate p →₀ ℕ) ≠ Finsupp.single v 1 := by
      intro hz
      have hh := congrArg (fun f : Coordinate p →₀ ℕ => f v) hz
      simp at hh
    rw [ite_eq_right hn, row, ite_eq_left h]
    simp only [coeff_one, ite_eq_right hzero]
  · rw [row, ite_eq_right h]
    by_cases hj : (p i).val < j.val ∧ j ∉ Set.range p
    · rw [dite_eq_left hj]
      change (X (⟨(i,j),hj⟩ : Coordinate p) : MvPolynomial (Coordinate p) R).coeff
        (Finsupp.single v 1) = _
      have he : ((⟨(i,j),hj⟩ : Coordinate p) = v) ↔
          v.val.1 = i ∧ v.val.2 = j := by
        rw [Subtype.ext_iff, Prod.ext_iff]
        simp only [eq_comm]
      simp [coeff_single_X, he]
    · rw [dite_eq_right hj]
      have hn : ¬ (v.val.1 = i ∧ v.val.2 = j) := by
        rintro ⟨hi, hv⟩
        apply hj
        simpa only [hi, hv] using v.property
      simp [hn]

/-- The linear coefficient is the differential of the original pairing:
one term moves the first row, and one moves the second row. -/
theorem equation_coeff_single (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s)
    (v : Coordinate p) :
    (equation (R := R) p c i j).coeff (Finsupp.single v 1) =
      (if v.val.1 = i then formMatrix c v.val.2 (p j) else 0) +
        (if v.val.1 = j then formMatrix c (p i) v.val.2 else 0) := by
  classical
  simp only [equation, coeff_sum]
  simp_rw [mul_assoc, coeff_C_mul, coeff_single_mul,
    row_coeff_single, row_constantCoeff, mul_add, Finset.sum_add_distrib]
  by_cases hij : i = j
  · subst j
    by_cases hi : v.val.1 = i <;> simp [hi, mul_ite, ite_mul, eq_comm]
  · by_cases hi : v.val.1 = i <;> by_cases hj : v.val.1 = j <;>
      simp [hi, hj, hij, Ne.symm hij, mul_ite, ite_mul, eq_comm]

/-- Nonzero linear coefficients must come from one of the two original
anti-diagonal edges, with the indicated row. -/
theorem equation_linear_support (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s)
    (v : Coordinate p)
    (hv : (equation (R := R) p c i j).coeff (Finsupp.single v 1) ≠ 0) :
    (v.val.1 = i ∧ v.val.2.val + (p j).val = c) ∨
      (v.val.1 = j ∧ (p i).val + v.val.2.val = c) := by
  classical
  rw [equation_coeff_single] at hv
  by_contra h
  have hfirst : (if v.val.1 = i then formMatrix (R := R) c v.val.2 (p j) else 0) = 0 := by
    split_ifs with hi
    · apply formMatrix_eq_zero_of_ne
      intro he
      exact h (Or.inl ⟨hi, he⟩)
    · rfl
  have hsecond : (if v.val.1 = j then formMatrix (R := R) c (p i) v.val.2 else 0) = 0 := by
    split_ifs with hj
    · apply formMatrix_eq_zero_of_ne
      intro he
      exact h (Or.inr ⟨hj, he⟩)
    · rfl
  exact hv (by rw [hfirst, hsecond, zero_add])

end PaperVerification.IsotropicAttractingCoordinates
