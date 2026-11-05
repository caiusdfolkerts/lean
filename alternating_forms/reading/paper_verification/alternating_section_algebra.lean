module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

/-!
# Restriction of an alternating form to local frame vectors

This construction retains the original coefficient formula.  It works over
any commutative ring and commutes with every coefficient-ring homomorphism.
The induced functional is on Mathlib's actual second exterior power.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingSectionAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]
variable {P N : Type*} [Fintype P]

/-- The two selected coordinate functionals, as a linear map. -/
def pairProjection (a b : N) : (N → R) →ₗ[R] (Fin 2 → R) where
  toFun v := ![v a, v b]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' r v := by ext i; fin_cases i <;> rfl

/-- One coordinate two-form, with the conventional order of its two indices. -/
def pairForm (a b : N) : AlternatingMap R (N → R) R (Fin 2) :=
  Matrix.detRowAlternating.compLinearMap (pairProjection a b)

@[simp] theorem pairForm_apply (a b : N) (v : Fin 2 → N → R) :
    pairForm a b v = v 0 a * v 1 b - v 0 b * v 1 a := by
  change Matrix.det (fun i => ![v i a, v i b]) = _
  exact Matrix.det_fin_two _

/-- The alternating form determined by the displayed independent coefficients. -/
def coefficientForm (a b : P → N) (c : P → R) :
    AlternatingMap R (N → R) R (Fin 2) :=
  ∑ p, c p • pairForm (a p) (b p)

@[simp] theorem coefficientForm_apply (a b : P → N) (c : P → R)
    (v : Fin 2 → N → R) :
    coefficientForm a b c v =
      ∑ p, c p * (v 0 (a p) * v 1 (b p) - v 0 (b p) * v 1 (a p)) := by
  simp [coefficientForm, sum_apply, smul_eq_mul]

/-- Restriction of the coefficient form is functorial even when the ring changes. -/
theorem coefficientForm_map (φ : R →+* S) (a b : P → N) (c : P → R)
    (v : Fin 2 → N → R) :
    coefficientForm a b (fun p => φ (c p)) (fun i j => φ (v i j)) =
      φ (coefficientForm a b c v) := by
  simp only [coefficientForm_apply, map_sum, map_mul, map_sub]

/-- The universal-property map out of the actual second exterior power. -/
def exteriorFunctional (a b : P → N) (c : P → R) :
    ⋀[R]^2 (N → R) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv (coefficientForm a b c)

@[simp] theorem exteriorFunctional_wedge (a b : P → N) (c : P → R)
    (v : Fin 2 → N → R) :
    exteriorFunctional a b c (exteriorPower.ιMulti R 2 v) =
      ∑ p, c p * (v 0 (a p) * v 1 (b p) - v 0 (b p) * v 1 (a p)) := by
  rw [exteriorFunctional, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    coefficientForm_apply]

end PaperVerification.AlternatingSectionAlgebra
