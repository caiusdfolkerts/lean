module

public import sunlet.initial_independence
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Sunlet.InitialIndependence

variable {ι σ : Type*} [Fintype ι]

/-- Rational independence of exponent vectors prevents collisions of all
nonnegative integral exponent combinations. -/
theorem exponentCombination_injective_of_linearIndependent
    (D : ι → σ →₀ ℕ)
    (hD : LinearIndependent ℚ (fun i j => (D i j : ℚ))) :
    Function.Injective (exponentCombination D) := by
  classical
  intro d e hde
  have hsum : Fintype.linearCombination ℚ (fun i j => (D i j : ℚ)) (fun i => (d i : ℚ)) =
      Fintype.linearCombination ℚ (fun i j => (D i j : ℚ)) (fun i => (e i : ℚ)) := by
    ext j
    have hh := congrArg (fun v : σ →₀ ℕ => (v j : ℚ)) hde
    simpa [Fintype.linearCombination_apply, exponentCombination, Finsupp.sum_apply,
      Finsupp.smul_apply, nsmul_eq_mul] using hh
  have h := hD.fintypeLinearCombination_injective hsum
  ext i
  exact Nat.cast_injective (congrFun h i)

/-- The leading-exponent criterion has no characteristic restriction on `K`. -/
theorem algebraicIndependent_of_rational_leading_exponents
    {K : Type*} [Field K] (m : MonomialOrder σ) (f : ι → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0)
    (hD : LinearIndependent ℚ (fun i j => (m.degree (f i) j : ℚ))) :
    AlgebraicIndependent K f :=
  algebraicIndependent_of_injective_exponentCombination m f hf
    (exponentCombination_injective_of_linearIndependent _ hD)

end Sunlet.InitialIndependence
