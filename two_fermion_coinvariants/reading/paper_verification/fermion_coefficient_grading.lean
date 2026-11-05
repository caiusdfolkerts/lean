module

public import PaperVerification.FermionCoefficientBoxBasis
public import PaperVerification.FermionQuotientDegreeBasis
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# The original polynomial grading of each coefficient colon quotient

The degree pieces are images of the original homogeneous polynomial spaces.
The ordinary ideal is homogeneous, and multiplying by the actual homogeneous
factor f_m shifts components. Its colon is therefore homogeneous. The exact
monomial basis then restricts to a basis in each of those original pieces.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion.TypeA

open MvPolynomial BasisFiltered

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem powerSum_isHomogeneous (k : ℕ) :
    (powerSum (F := F) (n := n) k).IsHomogeneous (k+1) :=
  IsHomogeneous.sum Finset.univ _ _ (fun i _ ↦ isHomogeneous_X_pow i (k+1))

theorem ordinaryIdeal_isHomogeneous :
    (ordinaryIdeal (F := F) (n := n)).IsHomogeneous
      (homogeneousSubmodule (Fin n) F) := by
  apply Ideal.homogeneous_span (homogeneousSubmodule (Fin n) F)
  rintro p ⟨k,rfl⟩
  exact ⟨k.val+1,powerSum_isHomogeneous k.val⟩

def factorDegree (m : MultiplicityVector n) : ℕ :=
  ∑ i,(1+(Finset.Ioi i).card)*(m i).val

theorem factor_isHomogeneous (m : MultiplicityVector n) :
    (factor (F := F) m).IsHomogeneous (factorDegree m) := by
  apply IsHomogeneous.prod Finset.univ _ _
  intro i hi
  apply IsHomogeneous.pow
  apply (isHomogeneous_X F i).mul
  simpa only [Finset.sum_const,smul_eq_mul,mul_one] using
    (IsHomogeneous.prod (Finset.Ioi i) (fun j ↦ (X i-X j : PolynomialRing F n))
      (fun _ ↦ 1) (fun j _ ↦ (isHomogeneous_X F i).sub (isHomogeneous_X F j)))

theorem coefficientIdeal_homogeneousComponent (m : MultiplicityVector n)
    (k : ℕ) (p : PolynomialRing F n) (hp : p∈coefficientIdeal (F := F) m) :
    homogeneousComponent k p∈coefficientIdeal (F := F) m := by
  change p∈principalColon ordinaryIdeal (factor m) at hp
  have hp' := (mem_principalColon _ _ p).mp hp
  have h := ordinaryIdeal_isHomogeneous (F := F) (n := n)
    (k+factorDegree m) hp'
  change (DirectSum.decompose (homogeneousSubmodule (Fin n) F)
    (p*factor m) (k+factorDegree m) : PolynomialRing F n)∈ordinaryIdeal at h
  have key : (DirectSum.decompose (homogeneousSubmodule (Fin n) F)
      (p*factor m) (k+factorDegree m) : PolynomialRing F n)=
      homogeneousComponent (k+factorDegree m) (p*factor m) :=
    MvPolynomial.decomposition.decompose'_apply (p*factor m) (k+factorDegree m)
  rw [key,(factor_isHomogeneous (F := F) m).homogeneousComponent_mul_right,
    if_pos (Nat.le_add_left _ _),Nat.add_sub_cancel_right] at h
  exact (mem_principalColon _ _ _).mpr h

theorem polynomialBasis_component (k : ℕ) (p : PolynomialRing F n) :
    BasisFiltered.component (basisMonomials (Fin n) F) Finsupp.degree k p=
      homogeneousComponent k p := by
  ext a
  change (basisMonomials (Fin n) F).repr
    (BasisFiltered.component (basisMonomials (Fin n) F) Finsupp.degree k p) a=_
  rw [BasisFiltered.repr_component,coeff_homogeneousComponent]
  rfl

theorem polynomialBasis_homogeneousPiece (k : ℕ) :
    BasisFiltered.homogeneousPiece (basisMonomials (Fin n) F) Finsupp.degree k=
      homogeneousSubmodule (Fin n) F k := by
  ext p
  change (∀ a : Fin n →₀ ℕ,p.coeff a≠0 → a.degree=k) ↔ p.IsHomogeneous k
  simp only [MvPolynomial.IsHomogeneous,MvPolynomial.IsWeightedHomogeneous,
    Finsupp.degree_eq_weight_one]
  constructor
  · intro h a ha
    exact h a ha
  · intro h a ha
    exact h ha

def coefficientPolynomialPiece (m : MultiplicityVector n) (k : ℕ) :
    Submodule F (CoefficientQuotient (F := F) m) :=
  (homogeneousSubmodule (Fin n) F k).map
    (Ideal.Quotient.mkₐ F (coefficientIdeal m)).toLinearMap

def coefficientBoxDegree (m : MultiplicityVector n)
    (a : StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m)) : ℕ :=
  a.val.val.degree

theorem coefficientPolynomial_kernel_component (m : MultiplicityVector n)
    (k : ℕ) (p : PolynomialRing F n)
    (hp : p∈(Ideal.Quotient.mkₐ F (coefficientIdeal m)).toLinearMap.ker) :
    BasisFiltered.component (basisMonomials (Fin n) F) Finsupp.degree k p∈
      (Ideal.Quotient.mkₐ F (coefficientIdeal m)).toLinearMap.ker := by
  change Ideal.Quotient.mk (coefficientIdeal m) p=0 at hp
  change Ideal.Quotient.mk (coefficientIdeal m)
    (BasisFiltered.component (basisMonomials (Fin n) F) Finsupp.degree k p)=0
  rw [polynomialBasis_component]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (coefficientIdeal_homogeneousComponent m k p (Ideal.Quotient.eq_zero_iff_mem.mp hp))

/-- A basis of the actual homogeneous image, selected by the original
polynomial exponent degree. -/
def coefficientPolynomialPieceBasis (hn : 0<n) (m : MultiplicityVector n) (k : ℕ) :
    Module.Basis
      {a : StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m) //
        coefficientBoxDegree m a=k} F (coefficientPolynomialPiece (F := F) m k) :=
  (BasisFiltered.quotientPieceBasis
    (basisMonomials (Fin n) F) Finsupp.degree
    (Ideal.Quotient.mkₐ F (coefficientIdeal m)).toLinearMap
    (coefficientBoxBasis hn m) (fun a ↦ monomial a.val.val 1)
    (coefficientBoxDegree m)
    (fun a ↦ BasisFiltered.homogeneous_basis (basisMonomials (Fin n) F)
      Finsupp.degree a.val.val)
    (fun a ↦ (coefficientBoxBasis_apply hn m a).symm)
    (coefficientPolynomial_kernel_component m) k).map
      (LinearEquiv.ofEq _ _ (congrArg
        (fun U : Submodule F (PolynomialRing F n) ↦
          U.map (Ideal.Quotient.mkₐ F (coefficientIdeal m)).toLinearMap)
        (polynomialBasis_homogeneousPiece (F := F) (n := n) k)))

end PaperVerification.Fermion.TypeA
