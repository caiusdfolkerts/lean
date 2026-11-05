module

public import PaperVerification.ProjectiveLineLaurentResidue
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Binary forms and the projective-line residue pairing

For `a ≥ 0`, the negative Laurent monomial `X₀^(-i-1) X₁^(i-a-1)`
pairs with the degree-`a` monomial `X₀^i X₁^(a-i)`. This identifies the
complete residue module with the linear dual of the homogeneous forms.
The construction is linear over every commutative coefficient ring.

This file fixes the two ordered coordinates. Equivariance under an arbitrary
change of frame, including the determinant factor, is a separate assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.ProjectiveLineResidueDuality

open Segre.CechMonomials ProjectiveLineLaurentResidue
open scoped BigOperators

universe u

/-- A negative exponent pair of total degree `-a-2` is determined by `-e₀-1`. -/
def negativeExponentFinEquiv (a : ℕ) :
    negativeExponents (-(a : ℤ) - 2) ≃ Fin (a + 1) where
  toFun e := ⟨(-e.val.val 0 - 1).toNat, by
    have hs := e.val.property
    rw [Fin.sum_univ_two] at hs
    have h₀ := e.property 0
    have h₁ := e.property 1
    omega⟩
  invFun i := ⟨⟨(fun j ↦ if j = 0 then -(i.val : ℤ) - 1 else
      (i.val : ℤ) - (a : ℤ) - 1), by
      simp [Fin.sum_univ_two]
      ring⟩, by
    intro j
    have hi := i.isLt
    change (if j = 0 then -(i.val : ℤ) - 1 else (i.val : ℤ) - (a : ℤ) - 1) < 0
    split_ifs <;> omega⟩
  left_inv e := by
    have hs := e.val.property
    rw [Fin.sum_univ_two] at hs
    have h₀ := e.property 0
    have h₁ := e.property 1
    apply Subtype.ext
    apply Subtype.ext
    funext j
    fin_cases j <;> simp <;> omega
  right_inv i := by
    apply Fin.ext
    simp

/-- Pair negative Laurent exponents with the complementary binary monomial exponents. -/
def negativeExponentMonomialEquiv (a : ℕ) :
    negativeExponents (-(a : ℤ) - 2) ≃
      {s : Fin 2 →₀ ℕ // s.degree = a} :=
  (negativeExponentFinEquiv a).trans (TauCeti.finsuppDegreeFinTwoEquiv a).symm

theorem finite_binary_exponents (a : ℕ) :
    Finite {s : Fin 2 →₀ ℕ // s.degree = a} :=
  Finite.of_equiv (Fin (a + 1)) (TauCeti.finsuppDegreeFinTwoEquiv a).symm

/-- The monomial residue pairing is perfect over every commutative ring. -/
def residueDualEquiv (R : Type u) [CommRing R] (a : ℕ) :
    (negativeExponents (-(a : ℤ) - 2) →₀ R) ≃ₗ[R]
      Module.Dual R (MvPolynomial.homogeneousSubmodule (Fin 2) R a) := by
  letI := finite_binary_exponents a
  exact (Finsupp.domLCongr (negativeExponentMonomialEquiv a)).trans
    (TauCeti.homogeneousMonomialBasis (R := R) a).dualBasis.repr.symm

/-- The functional reads the complementary negative Laurent coefficient. -/
theorem residueDualEquiv_monomial (R : Type u) [CommRing R] (a : ℕ)
    (p : negativeExponents (-(a : ℤ) - 2) →₀ R)
    (s : {s : Fin 2 →₀ ℕ // s.degree = a}) :
    residueDualEquiv R a p (TauCeti.homogeneousMonomialBasis (R := R) a s) =
      p ((negativeExponentMonomialEquiv a).symm s) := by
  haveI := finite_binary_exponents a
  let b := TauCeti.homogeneousMonomialBasis (σ := Fin 2) (R := R) a
  let e := negativeExponentMonomialEquiv a
  calc
    residueDualEquiv R a p (b s) = b.dualBasis.repr (residueDualEquiv R a p) s :=
      (b.dualBasis_repr _ s).symm
    _ = (Finsupp.domLCongr e p) s := by
      change (b.dualBasis.repr (b.dualBasis.repr.symm (Finsupp.domLCongr e p))) s = _
      rw [LinearEquiv.apply_symm_apply]
    _ = p (e.symm s) := rfl

end PaperVerification.ProjectiveLineResidueDuality
