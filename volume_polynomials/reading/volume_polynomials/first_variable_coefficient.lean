module

public import VolumePolynomials.MixedVolume
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section
set_option autoImplicit false

/-! # Extracting the first added-body coefficient by actual differentiation

The coefficient in the first variable is a polynomial in all the remaining
variables. Its evaluation is the genuine derivative at zero, and its
squarefree coefficient is the squarefree coefficient of the original volume
polynomial. These identities justify coefficient extraction after first
variation without any assumption about a mixed-volume functional.
-/

noncomputable section
open Set Filter MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials

def firstVariableCoefficient {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ := (MvPolynomial.finSuccEquiv ℝ n p).coeff 1

theorem firstVariableCoefficient_coeff {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (m : Fin n →₀ ℕ) :
    (firstVariableCoefficient p).coeff m = p.coeff (m.cons 1) :=
  MvPolynomial.finSuccEquiv_coeff_coeff m p 1

theorem squarefreeExponent_cons (n : ℕ) :
    (squarefreeExponent n).cons 1 = squarefreeExponent (n + 1) := by
  first
  | ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem firstVariableCoefficient_squarefree {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    (firstVariableCoefficient p).coeff (squarefreeExponent n) =
      p.coeff (squarefreeExponent (n + 1)) := by
  first
  | rw [firstVariableCoefficient_coeff, squarefreeExponent_cons]

theorem hasDerivAt_eval_firstVariableCoefficient {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (t : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (Fin.cons s t) p)
      (MvPolynomial.eval t (firstVariableCoefficient p)) 0 := by
  first
  | let q : Polynomial ℝ :=
      Polynomial.map (MvPolynomial.eval t) (MvPolynomial.finSuccEquiv ℝ n p)
    have he (s : ℝ) : q.eval s = MvPolynomial.eval (Fin.cons s t) p :=
      (MvPolynomial.eval_eq_eval_mv_eval' t s p).symm
    have hd : q.derivative.eval 0 = MvPolynomial.eval t (firstVariableCoefficient p) := by
      first
      | rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
        simp only [Nat.zero_add, Nat.cast_zero, Nat.cast_one, zero_add, mul_one, q,
          Polynomial.coeff_map, firstVariableCoefficient]
    simpa only [he, hd] using q.hasDerivAt 0

section Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem volumePolynomial_eval_cons {n : ℕ} (A : ConvexBody E)
    (K : Fin n → ConvexBody E) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {s : ℝ} (hs : 0 ≤ s) :
    MvPolynomial.eval (Fin.cons s t) (volumePolynomial μ (Fin.cons A K)) =
      μ.real ((↑(∑ i, t i • K i) : Set E) + s • (A : Set E)) := by
  first
  | rw [volumePolynomial_eval μ (Fin.cons A K) (Fin.cons s t)
      (by intro i; exact Fin.cases hs ht i)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ConvexBody.coe_add,
      ConvexBody.coe_smul, add_comm]

/-- A genuine right derivative of actual Minkowski volume identifies the
first-variable coefficient, for every fixed nonnegative background tuple. -/
theorem eval_firstVariableCoefficient_eq_of_volume_derivative {n : ℕ}
    (A : ConvexBody E) (K : Fin n → ConvexBody E)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {c : ℝ}
    (hc : HasDerivWithinAt
      (fun s : ℝ => μ.real ((↑(∑ i, t i • K i) : Set E) + s • (A : Set E))) c (Ioi 0) 0) :
    MvPolynomial.eval t (firstVariableCoefficient (volumePolynomial μ (Fin.cons A K))) = c := by
  first
  | let p := volumePolynomial μ (Fin.cons A K)
    have hp := (hasDerivAt_eval_firstVariableCoefficient p t).hasDerivWithinAt
      (s := Ioi (0 : ℝ))
    have he := volumePolynomial_eval_cons μ A K t ht (s := 0) le_rfl
    have hv : HasDerivWithinAt
        (fun s : ℝ => μ.real ((↑(∑ i, t i • K i) : Set E) + s • (A : Set E)))
        (MvPolynomial.eval t (firstVariableCoefficient p)) (Ioi 0) 0 :=
      hp.congr (fun s hs => (volumePolynomial_eval_cons μ A K t ht hs.le).symm) he.symm
    have h₁ := (hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hv
    have h₂ := (hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hc
    exact tendsto_nhds_unique h₁ h₂

end Volume
end VolumePolynomials
