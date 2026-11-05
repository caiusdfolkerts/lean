module

public import PaperVerification.FermionBlockInitial
public import PaperVerification.FermionMultiplicityTriangular
public import PaperVerification.FermionStrictCoupledBasis
public import PaperVerification.FermionQuotientFactor
public import PaperVerification.FermionFrobenius

/-!
# The actual strict multiplicity initial relation module

The diagonal maps are multiplication by the literal creator products into
the ordinary positive-moment quotient. The actual strict monomial basis,
the actual harmonic creator tests, and tied-weight triangularity supply
every input to `BlockInitial`; none of its substantive hypotheses is left
as a premise of the endpoint.

The resulting coefficientwise colon equality holds for the full coupled
strict data. The paper's type-A specialization is obtained by setting every
covering degree and weight to one and every parameter to its variable.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators TensorProduct

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionStrictMultiplicityInitial_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

abbrev StrictCoefficientQuotient (d : StrictData (K := F) (n := n)) :=
  PolynomialRing F n ⧸ coupledOrdinaryIdeal d.pairedExtension

def strictCoefficientProjection (d : StrictData (K := F) (n := n)) :
    PolynomialRing F n →ₐ[F] StrictCoefficientQuotient d :=
  Ideal.Quotient.mkₐ F (coupledOrdinaryIdeal d.pairedExtension)

theorem superPolynomialBasis_smul (p : PolynomialRing F n) (T : Finset (OddIndex n)) :
    p • superPolynomialBasis (K := F) T=
      p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T := by
  simp only [superPolynomialBasis_apply,TensorProduct.smul_tmul',smul_eq_mul,mul_one]

def strictMultiplicityCreator (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) :
    ExteriorAlgebra (StrictCoefficientQuotient d) (OddModule (StrictCoefficientQuotient d) n) :=
  prefixCreatorWedge (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n))
    (fun i ↦ strictCoefficientProjection d (d.phi i))
    (fun i ↦ algebraMap F (StrictCoefficientQuotient d) (d.beta i))
    (fun i ↦ strictCoefficientProjection d (d.phi i))
    (fun i ↦ strictCoefficientProjection d (d.phi i)) T.card ⟨T,rfl⟩

def strictMultiplicityTest (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) : SuperRing F n →ₗ[F] StrictCoefficientQuotient d :=
  ((((coefficientPairing (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n))).flip
    (strictMultiplicityCreator d T)).restrictScalars F).comp
      (superSpecialization (strictCoefficientProjection d)).toLinearMap)

theorem strictMultiplicityTest_polynomial (d : StrictData (K := F) (n := n))
    (S T : Finset (OddIndex n)) (p : PolynomialRing F n) :
    strictMultiplicityTest d S (p • superPolynomialBasis (K := F) T)=
      strictCoefficientProjection d p*
        (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n)).ExteriorAlgebra.repr
          (strictMultiplicityCreator d S) T := by
  change coefficientPairing (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n))
    (superSpecialization (strictCoefficientProjection d)
      (p • superPolynomialBasis (K := F) T)) (strictMultiplicityCreator d S)=_
  rw [superPolynomialBasis_smul,superSpecialization_polynomial_wedge,map_smul,
    LinearMap.smul_apply,coefficientPairing_basis_left,smul_eq_mul]

theorem strictMultiplicityCreator_diagonal (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) :
    (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n)).ExteriorAlgebra.repr
      (strictMultiplicityCreator d T) T=
        strictCoefficientProjection d (creatorWordPolynomial d.creatorData T) := by
  let b := Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n)
  change b.ExteriorAlgebra.repr
    (prefixCreatorWedge b
      (fun i ↦ strictCoefficientProjection d (d.phi i))
      (fun i ↦ algebraMap F (StrictCoefficientQuotient d) (d.beta i))
      (fun i ↦ strictCoefficientProjection d (d.phi i))
      (fun i ↦ strictCoefficientProjection d (d.phi i)) T.card ⟨T,rfl⟩ :
        ExteriorAlgebra (StrictCoefficientQuotient d) _) T=_
  rw [exteriorPower_coordinate_coe b T.card ⟨T,rfl⟩ _,
    prefixCreatorWedge_coordinate_self,prod_exteriorEnumeration]
  simp only [creatorWordPolynomial,map_prod,creatorDiagonal_map,StrictData.creatorData]

theorem strictMultiplicityTest_same (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) (p : PolynomialRing F n) :
    strictMultiplicityTest d T (p • superPolynomialBasis (K := F) T)=
      multiplyIntoQuotient (K := F) (coupledOrdinaryIdeal d.pairedExtension)
        (creatorWordPolynomial d.creatorData T) p := by
  rw [strictMultiplicityTest_polynomial,strictMultiplicityCreator_diagonal]
  change strictCoefficientProjection d p*
    strictCoefficientProjection d (creatorWordPolynomial d.creatorData T)=
      strictCoefficientProjection d (creatorWordPolynomial d.creatorData T*p)
  rw [map_mul,mul_comm]

theorem strictMultiplicityTest_higher (d : StrictData (K := F) (n := n))
    (S T : Finset (OddIndex n)) (hST : S≠T)
    (hweight : multiplicityWordWeight S≤multiplicityWordWeight T)
    (p : PolynomialRing F n) :
    strictMultiplicityTest d S (p • superPolynomialBasis (K := F) T)=0 := by
  rw [strictMultiplicityTest_polynomial]
  have hz := prefixCreatorWedge_multiplicity_coordinate_zero
    (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n))
    (fun i ↦ strictCoefficientProjection d (d.phi i))
    (fun i ↦ algebraMap F (StrictCoefficientQuotient d) (d.beta i))
    (fun i ↦ strictCoefficientProjection d (d.phi i))
    (fun i ↦ strictCoefficientProjection d (d.phi i)) S T hST hweight
  change (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n)).ExteriorAlgebra.repr
    (strictMultiplicityCreator d S) T=0 at hz
  rw [hz,mul_zero]

theorem strictMultiplicityTest_kills (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) :
    (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap).ker≤
      (strictMultiplicityTest d T).ker := by
  intro z hz
  change strictMultiplicityTest d T z=0
  change coefficientPairing (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n))
    (superSpecialization (strictCoefficientProjection d) z) (strictMultiplicityCreator d T)=0
  apply strict_relation_pairing_zero (strictCoefficientProjection d) d.beta d.phi
    (strictOrdinary_quotient_all_moments d) z
  · exact (strictIdeal d.beta d.phi).ringCon.eq.mp hz
  · exact strict_prefixCreatorWedge_isHarmonic
      (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n)) _ _
      (strictOrdinary_quotient_all_moments d) T.card ⟨T,rfl⟩

def strictMultiplicityPresentation (d : StrictData (K := F) (n := n)) :
    BlockInitial.TriangularPresentation (N := StrictCoefficientQuotient d)
      (superPolynomialBasis (K := F)) multiplicityWordWeight
      (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap)
      (StrictWordPolynomialIndex d.r) where
  polynomial := fun T a ↦ monomial a.val.val 1
  basis := strictCoupledBasis d
  basis_apply := by
    intro z
    rw [strictCoupledBasis_apply,strictCoupledClasses,superPolynomialBasis_smul]
    rfl
  test := strictMultiplicityTest d
  diagonal := fun T ↦ multiplyIntoQuotient (K := F) (coupledOrdinaryIdeal d.pairedExtension)
    (creatorWordPolynomial d.creatorData T)
  test_same := strictMultiplicityTest_same d
  test_higher := strictMultiplicityTest_higher d
  kill := strictMultiplicityTest_kills d
  independent := by
    intro T
    by_cases hT : ValidWord T
    · have hi := (strict_coupled_creator_diagonal_independent d T hT).comp
        (fun a : StrictWordPolynomialIndex d.r T ↦ a.val) Subtype.val_injective
      convert hi using 1
      funext a
      rw [multiplyIntoQuotient_apply,mul_comm]
      rfl
    · haveI : IsEmpty (StrictWordPolynomialIndex d.r T) := ⟨fun a ↦ hT a.property⟩
      exact linearIndependent_empty_type

@[simp] theorem strictMultiplicityPresentation_diagonal
    (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) :
    (strictMultiplicityPresentation d).diagonal T=
      multiplyIntoQuotient (K := F) (coupledOrdinaryIdeal d.pairedExtension)
        (creatorWordPolynomial d.creatorData T) := rfl

@[simp] theorem strictMultiplicityPresentation_basis
    (d : StrictData (K := F) (n := n)) :
    (strictMultiplicityPresentation d).basis=strictCoupledBasis d := rfl

@[simp] theorem strictMultiplicityPresentation_polynomial
    (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n))
    (a : StrictWordPolynomialIndex d.r T) :
    (strictMultiplicityPresentation d).polynomial T a=monomial a.val.val (1 : F) := rfl

def strictMultiplicityInitialGenerators (d : StrictData (K := F) (n := n)) :
    Set (SuperRing F n) :=
  {y | ∃ x∈strictIdeal d.beta d.phi,∃ r,
    BlockInitial.LowerBound (superPolynomialBasis (K := F)) multiplicityWordWeight r x ∧
      BasisFiltered.component (superPolynomialBasis (K := F)) multiplicityWordWeight r x=y}

def strictMultiplicityInitialModule (d : StrictData (K := F) (n := n)) :
    Submodule F (SuperRing F n) :=
  Submodule.span F (strictMultiplicityInitialGenerators d)

/-- The complete smallest-weight relation statement, expressed in the
actual polynomial coefficients of the actual exterior basis. -/
theorem strict_multiplicity_initial_mem_iff (d : StrictData (K := F) (n := n))
    (z : SuperRing F n) :
    z∈strictMultiplicityInitialModule d ↔
      ∀ T,(superPolynomialBasis (K := F)).repr z T∈
        principalColon (coupledOrdinaryIdeal d.pairedExtension)
          (creatorWordPolynomial d.creatorData T) := by
  have he := (strictMultiplicityPresentation d).initialMin_eq_blockKernel
  change BlockInitial.initialMin (superPolynomialBasis (K := F)) multiplicityWordWeight
    (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap).ker=_ at he
  rw [quotient_kernel_eq_twoSidedIdealSubmodule] at he
  change strictMultiplicityInitialModule d=_ at he
  rw [he,BlockInitial.mem_blockKernel]
  change (∀ T,multiplyIntoQuotient (K := F) (coupledOrdinaryIdeal d.pairedExtension)
      (creatorWordPolynomial d.creatorData T) ((superPolynomialBasis (K := F)).repr z T)=0)↔_
  simp only [multiplyIntoQuotient_apply,Ideal.Quotient.eq_zero_iff_mem,
    mem_principalColon,mul_comm]

end PaperVerification.Fermion
