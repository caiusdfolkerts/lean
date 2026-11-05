module

public import PaperVerification.AlternatingFormsOddInitialCharacteristic
public import PaperVerification.AlternatingFormsOddExteriorBasis

/-!
# The full good basis below twice the characteristic

Integral standard monomials give the interval basis over every field.
Lifting through the proved exact initial ideal gives the original Plücker
basis.  Its actual degree-one component is then identified with the genuine
exterior generated-ideal quotient.  No Hilbert-function assumption is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms
namespace DegreeRestricted

open MvPolynomial
open PaperVerification.WeightedInitialFiber
open scoped BigOperators

variable {K : Type*} [Field K]

def oddInitialStandardBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
          (pluckerVertexWeight (oddNatVertexWeight k))) :=
  (intervalStandardBasis (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)).map
      (Ideal.quotientEquivAlgOfEq K (odd_isotropic_initial_eq_interval_of_degree_factorials k t hs hfac).symm).toLinearEquiv

@[simp] theorem oddInitialStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (C : OddStandardIndex k t hs) :
    oddInitialStandardBasis (K := K) k t hs hfac C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) := by
  unfold oddInitialStandardBasis
  erw [Module.Basis.map_apply]
  simp only [intervalStandardBasis]
  erw [Module.Basis.mk_apply]
  simp only [intervalAllStandardProduct,intervalStandardProduct,
    AlgEquiv.coe_toLinearEquiv,Ideal.quotientEquivAlgOfEq_mk,oddStandardRepresentative]

/-- Every actual good-coordinate standard product, in every polynomial
degree, is retained as a basis vector of the original isotropic ring. -/
def oddPluckerStandardBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  liftedInitialBasis _ (pluckerVertexWeight (oddNatVertexWeight k))
    (oddStandardRepresentative k t hs) (oddStandardWeight k t hs)
    (oddStandardRepresentative_weighted k t hs) (oddInitialStandardBasis k t hs hfac)
    (oddInitialStandardBasis_apply k t hs hfac)

@[simp] theorem oddPluckerStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs hfac C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) :=
  liftedInitialBasis_apply _ _ _ _ _ _ _ C

theorem oddPluckerStandardBasis_mem_degree (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs hfac C∈oddPluckerDegree k t C.1 := by
  rw [oddPluckerStandardBasis_apply]
  exact ⟨oddStandardRepresentative k t hs C,
    oddStandardRepresentative_homogeneous k t hs C,rfl⟩

def oddPluckerDegreeBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) (r : ℕ) :
    Module.Basis
      (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r)
      K (oddPluckerDegree (K := K) k t r) :=
  (HomogeneousIdealPieces.componentBasis _ (isotropicPluckerIdeal_isHomogeneous _)
    (oddPluckerStandardBasis k t hs hfac) (fun C => C.1)
    (oddPluckerStandardBasis_mem_degree k t hs hfac) r).reindex
      (oddStandardDegreeEquiv k t hs r)

@[simp] theorem oddPluckerDegreeBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) (r : ℕ)
    (C : BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :
    (oddPluckerDegreeBasis (K := K) k t hs hfac r C :
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))=
      Ideal.Quotient.mk _ (chainPluckerProduct _ _ C) := by
  unfold oddPluckerDegreeBasis
  erw [Module.Basis.reindex_apply,HomogeneousIdealPieces.componentBasis_coe]
  change oddPluckerStandardBasis (K := K) k t hs hfac ⟨r,C⟩ = _
  exact oddPluckerStandardBasis_apply (K := K) k t hs hfac ⟨r,C⟩

theorem oddPluckerDegree_finrank (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) (r : ℕ) :
    Module.finrank K (oddPluckerDegree (K := K) k t r)=
      Fintype.card (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :=
  Module.finrank_eq_card_basis (oddPluckerDegreeBasis k t hs hfac r)

def oddExteriorMiddleBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    Module.Basis (GoodOddIndex k (t+2)) K (OddExteriorQuotientDegree (K := K) k (t+2)) :=
  ((oddPluckerDegreeBasis k t hs hfac 1).map (oddExteriorLinearPieceEquiv k t).symm).reindex
    (goodOddBandEquiv k t hs).symm

@[simp] theorem oddExteriorMiddleBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (I : GoodOddIndex k (t+2)) :
    oddExteriorMiddleBasis (K := K) k t hs hfac I=
      Submodule.Quotient.mk (exteriorPluckerBasis (t+2) (2*k+1) I.val) := by
  apply (oddExteriorLinearPieceEquiv k t).injective
  apply Subtype.ext
  simp only [oddExteriorMiddleBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    Module.Basis.map_apply,LinearEquiv.apply_symm_apply,oddPluckerDegreeBasis_apply,
    oddExteriorLinearPieceEquiv_mk,exteriorPluckerCoordinates_basis,
    goodOddBandEquiv,chainPluckerProduct,Fin.prod_univ_one]
  rfl

/-- Every degree in the permitted range, including zero and one. -/
def oddExteriorBasis (k : ℕ) : (s : ℕ) → (hs : s≤k+1) →
    DegreeFactorials K s →
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s)
  | 0, _, _ => oddExteriorLowBasis k 0 (by decide)
  | 1, _, _ => oddExteriorLowBasis k 1 (by decide)
  | t+2, hs, hfac => oddExteriorMiddleBasis k t hs hfac

@[simp] theorem oddExteriorBasis_apply (k s : ℕ) (hs : s≤k+1)
    (hfac : DegreeFactorials K s) (I : GoodOddIndex k s) :
    oddExteriorBasis (K := K) k s hs hfac I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  cases s with
  | zero => exact oddExteriorLowBasis_apply k 0 (by decide) I
  | succ s =>
      cases s with
      | zero => exact oddExteriorLowBasis_apply k 1 (by decide) I
      | succ t => exact oddExteriorMiddleBasis_apply k t hs hfac I

end DegreeRestricted

/-- The basis assertion of Theorem 7.1 with every original good monomial
identified explicitly.  This proof works over every field of the indicated
prime characteristic, so in particular over the algebraically closed fields
used in the paper. -/
theorem paper_theorem_7_1_exterior_basis
    {K : Type*} [Field K] (p k s : ℕ) [Fact p.Prime] [CharP K p]
    (hs : s≤k+1) (hp : s<2*p) :
    ∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*k+1)) (I.val.val i))) := by
  refine ⟨DegreeRestricted.oddExteriorBasis k s hs
    (degreeFactorials_of_lt_twice_characteristic p s hp),?_⟩
  intro I
  rw [DegreeRestricted.oddExteriorBasis_apply,exteriorPluckerBasis_apply]

end PaperVerification.AlternatingForms
