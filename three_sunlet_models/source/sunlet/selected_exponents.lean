module

public import sunlet.selected_relations
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Sunlet.SelectedExponents

variable {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
open SelectedRelations

def uExponent (π : ι → Equiv.Perm Ω) (ab : ι × Ω) : ParamVar ι Ω →₀ ℕ :=
  (Finsupp.single (.s ab.2) 1 + Finsupp.single (.t (π ab.1 ab.2)) 1) +
    (Finsupp.single (.u ab.1) 1 + Finsupp.single (.h (π ab.1 ab.2)) 1)

def vExponent (π : ι → Equiv.Perm Ω) (ab : ι × Ω) : ParamVar ι Ω →₀ ℕ :=
  (Finsupp.single (.s ab.2) 1 + Finsupp.single (.t (π ab.1 ab.2)) 1) +
    (Finsupp.single (.v ab.1) 1 + Finsupp.single (.h ab.2) 1)

def selectedExponent (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (ab : ι × Ω) : ParamVar ι Ω →₀ ℕ :=
  if selectsU π e o P ab.1 ab.2 then uExponent π ab else vExponent π ab

theorem coordinatePolynomial_eq_monomials {K : Type*} [CommSemiring K]
    (π : ι → Equiv.Perm Ω) (ab : ι × Ω) :
    coordinatePolynomial (K := K) π ab =
      monomial (uExponent π ab) 1 + monomial (vExponent π ab) 1 := by
  simp [coordinatePolynomial, uExponent, vExponent, MvPolynomial.X, mul_add, monomial_mul]

theorem uExponent_dot [Fintype ι] [Fintype Ω]
    (π : ι → Equiv.Perm Ω) (ab : ι × Ω) (w : ParamVar ι Ω → ℚ) :
    (∑ i, (uExponent π ab i : ℚ) * w i) =
      w (.s ab.2) + w (.t (π ab.1 ab.2)) + w (.u ab.1) + w (.h (π ab.1 ab.2)) := by
  simp [uExponent, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Finsupp.single_apply, add_assoc]

theorem vExponent_dot [Fintype ι] [Fintype Ω]
    (π : ι → Equiv.Perm Ω) (ab : ι × Ω) (w : ParamVar ι Ω → ℚ) :
    (∑ i, (vExponent π ab i : ℚ) * w i) =
      w (.s ab.2) + w (.t (π ab.1 ab.2)) + w (.v ab.1) + w (.h ab.2) := by
  simp [vExponent, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Finsupp.single_apply, add_assoc]

end Sunlet.SelectedExponents
