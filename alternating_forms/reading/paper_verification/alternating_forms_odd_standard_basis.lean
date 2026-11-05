module

public import PaperVerification.AlternatingFormsOddInitialIdeal
public import PaperVerification.WeightedInitialBasis
public import PaperVerification.AlternatingFormsIntervalHilbert

/-!
# The full standard basis in the original odd isotropic Plücker ring

Every interval multichain, of every length, gives the actual product of good
Plücker coordinates.  The exact initial-ideal equality and bounded lifting
of actual relations prove that these same products are a basis of the
original ring. This is not an inference from flatness alone.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open PaperVerification.WeightedInitialFiber
open scoped BigOperators

variable {K : Type*} [Field K]

def OddStandardIndex (k t : ℕ) (hs : t+2≤k+1) :=
  Σ r,BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r

def oddStandardRepresentative (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K :=
  chainPluckerProduct (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) C.2

def oddStandardWeight (k t : ℕ) (hs : t+2≤k+1) (C : OddStandardIndex k t hs) : ℕ :=
  ∑ j : Fin C.1,pluckerVertexWeight (oddNatVertexWeight k)
    ⟨C.2.val j,C.2.property.1 j⟩

theorem oddStandardRepresentative_weighted (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    (oddStandardRepresentative (K := K) k t hs C).IsWeightedHomogeneous (pluckerVertexWeight (oddNatVertexWeight k))
        (oddStandardWeight k t hs C) := by
  apply IsWeightedHomogeneous.prod Finset.univ
  intro j hj
  exact isWeightedHomogeneous_X K _ _

theorem oddStandardRepresentative_homogeneous (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    (oddStandardRepresentative (K := K) k t hs C).IsHomogeneous C.1 :=
  chainPluckerProduct_isHomogeneous _ _ C.2

variable [CharZero K]

def oddInitialStandardBasis (k t : ℕ) (hs : t+2≤k+1) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
          (pluckerVertexWeight (oddNatVertexWeight k))) :=
  (intervalStandardBasis (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)).map
      (Ideal.quotientEquivAlgOfEq K (odd_isotropic_initial_eq_interval k t hs).symm).toLinearEquiv

@[simp] theorem oddInitialStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    oddInitialStandardBasis (K := K) k t hs C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) := by
  unfold oddInitialStandardBasis
  erw [Module.Basis.map_apply]
  simp only [intervalStandardBasis]
  erw [Module.Basis.mk_apply]
  simp only [intervalAllStandardProduct,intervalStandardProduct,
    AlgEquiv.coe_toLinearEquiv,Ideal.quotientEquivAlgOfEq_mk,oddStandardRepresentative]

/-- Every actual good-coordinate standard product, in every polynomial
degree, is retained as a basis vector of the original isotropic ring. -/
def oddPluckerStandardBasis (k t : ℕ) (hs : t+2≤k+1) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  liftedInitialBasis _ (pluckerVertexWeight (oddNatVertexWeight k))
    (oddStandardRepresentative k t hs) (oddStandardWeight k t hs)
    (oddStandardRepresentative_weighted k t hs) (oddInitialStandardBasis k t hs)
    (oddInitialStandardBasis_apply k t hs)

@[simp] theorem oddPluckerStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) :=
  liftedInitialBasis_apply _ _ _ _ _ _ _ C

end PaperVerification.AlternatingForms
