module

public import PaperVerification.FermionEndpointIdeal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Weighted homogeneity of the endpoint polynomials

The extra polynomial variable has weight `W`. Coefficient calculations prove
that division by `t-y`, for homogeneous `y` of weight `W`, lowers the total
weight by `W`. This is applied to the actual endpoint recurrence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators
open Polynomial

variable {K ι : Type*} [Field K]

local notation "P" => MvPolynomial ι K

/-- A polynomial of total weight `W*H`, with its precise coefficient
homogeneity and its full degree cutoff. -/
def HomogeneousPolynomial (w : ι → ℕ) (W H : ℕ) (p : Polynomial P) : Prop :=
  (∀ j ≤ H, (p.coeff j).IsWeightedHomogeneous w (W * (H - j))) ∧
    CoefficientBound p (H + 1)

theorem homogeneousPolynomial_zero (w : ι → ℕ) (W H : ℕ) :
    HomogeneousPolynomial w W H (0 : Polynomial P) := by
  refine ⟨?_, coefficientBound_zero _⟩
  intro j hj
  rw [coeff_zero]
  exact MvPolynomial.isWeightedHomogeneous_zero K w _

theorem homogeneousPolynomial_one (w : ι → ℕ) (W : ℕ) :
    HomogeneousPolynomial w W 0 (1 : Polynomial P) := by
  constructor
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using MvPolynomial.isWeightedHomogeneous_one K w
  · exact coefficientBound_of_natDegree_lt _ _ (by simp)

theorem HomogeneousPolynomial.natDegree_le {w : ι → ℕ} {W H : ℕ} {p : Polynomial P}
    (hp : HomogeneousPolynomial w W H p) : p.natDegree ≤ H := by
  by_cases hzero : p = 0
  · simp [hzero]
  · have h := (natDegree_lt_iff_degree_lt hzero).mpr
      ((coefficientBound_iff_degree p (H + 1)).mp hp.2)
    omega

theorem HomogeneousPolynomial.sub {w : ι → ℕ} {W H : ℕ} {p q : Polynomial P}
    (hp : HomogeneousPolynomial w W H p) (hq : HomogeneousPolynomial w W H q) :
    HomogeneousPolynomial w W H (p - q) := by
  refine ⟨?_, hp.2.sub hq.2⟩
  intro j hj
  rw [coeff_sub]
  exact (hp.1 j hj).sub (hq.1 j hj)

/-- Scalar polynomial multiplication adds the actual homogeneous degree. -/
theorem HomogeneousPolynomial.C_mul {w : ι → ℕ} {W H s : ℕ} {p : Polynomial P}
    (hp : HomogeneousPolynomial w W H p) (a : P)
    (ha : a.IsWeightedHomogeneous w (W * s)) :
    HomogeneousPolynomial w W (H + s) (C a * p) := by
  constructor
  · intro j hj
    rw [coeff_C_mul]
    by_cases hjH : j ≤ H
    · have hdegree : W * s + W * (H - j) = W * (H + s - j) := by
        rw [← mul_add]
        congr 1
        omega
      simpa only [hdegree] using ha.mul (hp.1 j hjH)
    · rw [hp.2 j (by omega), mul_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero K w _
  · intro j hj
    rw [coeff_C_mul, hp.2 j (by omega), mul_zero]

/-- Multiplication by `t-y` raises total weight by exactly `W`. -/
theorem HomogeneousPolynomial.linear_mul {w : ι → ℕ} {W H : ℕ} {p : Polynomial P}
    (hp : HomogeneousPolynomial w W H p) (y : P)
    (hy : y.IsWeightedHomogeneous w W) :
    HomogeneousPolynomial w W (H + 1) ((X - C y) * p) := by
  refine ⟨?_, hp.2.linear_mul y⟩
  intro j hj
  rw [sub_mul, coeff_sub, coeff_C_mul]
  cases j with
  | zero =>
    rw [coeff_X_mul_zero, zero_sub]
    have hdegree : W + W * (H - 0) = W * (H + 1 - 0) := by simp; ring
    simpa only [hdegree] using (hy.mul (hp.1 0 (Nat.zero_le _))).neg
  | succ j =>
    rw [coeff_X_mul]
    have hjH : j ≤ H := by omega
    have htarget : H + 1 - (j + 1) = H - j := by omega
    rw [htarget]
    apply (hp.1 j hjH).sub
    by_cases hj1 : j + 1 ≤ H
    · have hdegree : W + W * (H - (j + 1)) = W * (H - j) := by
        calc
          _ = W * (1 + (H - (j + 1))) := by ring
          _ = _ := by congr 1; omega
      simpa only [hdegree] using hy.mul (hp.1 (j + 1) hj1)
    · rw [hp.2 (j + 1) (by omega), mul_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero K w _

/-- Evaluation at a homogeneous node preserves the total weighted degree. -/
theorem HomogeneousPolynomial.eval {w : ι → ℕ} {W H : ℕ} {p : Polynomial P}
    (hp : HomogeneousPolynomial w W H p) (y : P)
    (hy : y.IsWeightedHomogeneous w W) :
    (p.eval y).IsWeightedHomogeneous w (W * H) := by
  rw [Polynomial.eval_eq_sum_range]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  have hjH : j ≤ H := by
    have hj' := Finset.mem_range.mp hj
    have hdeg := hp.natDegree_le
    omega
  have hdegree : W * (H - j) + j * W = W * H := by
    rw [mul_comm j W, ← mul_add, Nat.sub_add_cancel hjH]
  simpa only [nsmul_eq_mul, Nat.cast_id, hdegree] using (hp.1 j hjH).mul (hy.pow j)

/-- The quotient in the actual monic division is homogeneous. The proof
uses the complete coefficient formula for division by `t-y`. -/
theorem HomogeneousPolynomial.quotient {w : ι → ℕ} {W H : ℕ} {p : Polynomial P}
    (hp : HomogeneousPolynomial w W H p) (y : P)
    (hy : y.IsWeightedHomogeneous w W) :
    HomogeneousPolynomial w W (H - 1) (PaperVerification.Fermion.Endpoint.quotient p y) := by
  by_cases hH : H = 0
  · have hbound : CoefficientBound (PaperVerification.Fermion.Endpoint.quotient p y) 0 := by
      apply CoefficientBound.quotient
      simpa only [hH] using hp.2
    have hz : PaperVerification.Fermion.Endpoint.quotient p y = 0 := by
      apply Polynomial.ext
      intro j
      rw [coeff_zero]
      exact hbound j (Nat.zero_le j)
    rw [hz]
    exact homogeneousPolynomial_zero w W _
  · constructor
    · intro j hj
      rw [PaperVerification.Fermion.Endpoint.quotient, coeff_divByMonic_X_sub_C]
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro i hi
      obtain ⟨hji, hiP⟩ := Finset.mem_Icc.mp hi
      have hiH : i ≤ H := hiP.trans hp.natDegree_le
      have hdegree : (i - (j + 1)) * W + W * (H - i) = W * (H - 1 - j) := by
        rw [mul_comm (i - (j + 1)) W, ← mul_add]
        congr 1
        omega
      simpa only [nsmul_eq_mul, Nat.cast_id, hdegree] using
        (hy.pow (i - (j + 1))).mul (hp.1 i hiH)
    · have hbound := hp.2.quotient y
      simpa only [show H - 1 + 1 = H by omega] using hbound

/-- If the original height is zero, the actual division quotient is zero;
its weighted degree may therefore be assigned freely. -/
theorem quotient_eq_zero_of_homogeneous_height_zero
    {w : ι → ℕ} {W : ℕ} {p : Polynomial P}
    (hp : HomogeneousPolynomial w W 0 p) (y : P) : quotient p y = 0 := by
  have hbound : CoefficientBound (PaperVerification.Fermion.Endpoint.quotient p y) 0 := hp.2.quotient y
  apply Polynomial.ext
  intro j
  rw [coeff_zero]
  exact hbound j (Nat.zero_le j)

/-- Weighted homogeneity follows through each of the four literal updates. -/
theorem next_homogeneous (w : ι → ℕ) (W s h h' : ℕ) (hs : 0 < s)
    (T : State P) (d : Datum P)
    (hy : d.node.IsWeightedHomogeneous w W)
    (hγ : d.weight.IsWeightedHomogeneous w (W * s))
    (hA : HomogeneousPolynomial w W h T.A)
    (hB : HomogeneousPolynomial w W (s + h - 1) T.B)
    (hstep : HeightStep d.mark h h') :
    HomogeneousPolynomial w W h' (next T d).A ∧
      HomogeneousPolynomial w W (s + h' - 1) (next T d).B := by
  cases hm : d.mark with
  | unmarked =>
    have hh : h' = h + 1 := by simpa only [HeightStep, hm] using hstep
    subst h'
    simp only [next, hm]
    refine ⟨hA.linear_mul d.node hy, ?_⟩
    apply HomogeneousPolynomial.sub
    · convert hB.linear_mul d.node hy using 1 <;> congr 1 <;> omega
    · convert hA.C_mul (s := s) d.weight hγ using 1 <;> congr 1 <;> omega
  | theta =>
    have hh : h' = h := by simpa only [HeightStep, hm] using hstep
    subst h'
    simp only [next, hm]
    refine ⟨hA, hB.sub ?_⟩
    by_cases hh0 : h = 0
    · subst h
      rw [quotient_eq_zero_of_homogeneous_height_zero hA, mul_zero]
      exact homogeneousPolynomial_zero w W _
    · convert (hA.quotient d.node hy).C_mul (s := s) d.weight hγ using 1 <;> congr 1 <;> omega
  | xi =>
    have hh : h' = h := by simpa only [HeightStep, hm] using hstep
    subst h'
    simp only [next, hm]
    refine ⟨hA, hB.sub ?_⟩
    by_cases hh0 : h = 0
    · subst h
      rw [quotient_eq_zero_of_homogeneous_height_zero hA, mul_zero]
      exact homogeneousPolynomial_zero w W _
    · convert (hA.quotient d.node hy).C_mul (s := s) d.weight hγ using 1 <;> congr 1 <;> omega
  | double =>
    have hh : h = h' + 1 := by simpa only [HeightStep, hm] using hstep
    subst h
    simp only [next, hm]
    have hq := hA.quotient d.node hy
    have hq' : HomogeneousPolynomial w W h' (quotient T.A d.node) := by
      simpa only [Nat.add_sub_cancel] using hq
    refine ⟨hq', ?_⟩
    have hmiddle : HomogeneousPolynomial w W (s + h')
        (T.B - C d.weight * quotient T.A d.node) := by
      apply HomogeneousPolynomial.sub
      · convert hB using 1 <;> congr 1 <;> omega
      · simpa only [Nat.add_comm] using hq'.C_mul (s := s) d.weight hγ
    exact hmiddle.quotient d.node hy

theorem run_homogeneous (w : ι → ℕ) (W s : ℕ) (hs : 0 < s)
    (data : ℕ → Datum P) (height : ℕ → ℕ) (hzero : height 0 = 0)
    (n : ℕ)
    (hy : ∀ j < n, (data j).node.IsWeightedHomogeneous w W)
    (hγ : ∀ j < n, (data j).weight.IsWeightedHomogeneous w (W * s))
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1))) :
    HomogeneousPolynomial w W (height n) (run data n).A ∧
      HomogeneousPolynomial w W (s + height n - 1) (run data n).B := by
  revert hy hγ hsteps
  induction n with
  | zero =>
    intro hy hγ hsteps
    rw [hzero]
    exact ⟨homogeneousPolynomial_one w W, homogeneousPolynomial_zero w W _⟩
  | succ n ih =>
    intro hy hγ hsteps
    obtain ⟨hA, hB⟩ := ih
      (fun j hj ↦ hy j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hγ j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hsteps j (Nat.lt_succ_of_lt hj))
    exact next_homogeneous w W s (height n) (height (n + 1)) hs
      (run data n) (data n) (hy n (Nat.lt_succ_self n))
      (hγ n (Nat.lt_succ_self n)) hA hB (hsteps n (Nat.lt_succ_self n))

end PaperVerification.Fermion.Endpoint
