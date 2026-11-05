module

public import PaperVerification.FermionStrictWeightRees
public import PaperVerification.FermionWeightReesFibers
public import PaperVerification.FermionBlockInitialNormalForm

/-!
# Both actual fibers of the strict multiplicity Rees algebra

The zero fiber is identified with the quotient by the literal smallest-weight
initial ideal. Its multiplication is derived by taking the same-weight
component of actual quotient normal forms. Equal dimensions alone are never
used to identify the algebra product.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior BasisFiltered
open scoped BigOperators TensorProduct PaperVerification.Fermion.WeightRees

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionStrictWeightReesFibers_localInst_1 : LinearOrder (OddIndex n) := LinearOrder.lift' modeRank modeRank_injective

abbrev StrictMultiplicityInitialQuotient (d : StrictData (K := F) (n := n)) :=
  (strictMultiplicityInitialIdeal d).ringCon.Quotient

def strictInitialProjection (d : StrictData (K := F) (n := n)) :
    SuperRing F n →ₐ[F] StrictMultiplicityInitialQuotient d :=
  (strictMultiplicityInitialIdeal d).ringCon.mkₐ F

theorem strictInitialModule_eq_kernel (d : StrictData (K := F) (n := n)) :
    BlockInitial.initialMin (superPolynomialBasis (K := F)) multiplicityWordWeight
      (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap).ker =
        (strictInitialProjection d).toLinearMap.ker := by
  rw [quotient_kernel_eq_twoSidedIdealSubmodule]
  change strictMultiplicityInitialModule d = (strictInitialProjection d).toLinearMap.ker
  rw [strictInitialProjection, quotient_kernel_eq_twoSidedIdealSubmodule]
  ext z
  exact (strict_multiplicity_initial_mem_iff d z).trans
    (strict_multiplicity_initialIdeal_mem_iff d z).symm

def strictInitialToRingEquiv (d : StrictData (K := F) (n := n)) :
    (SuperRing F n ⧸ BlockInitial.initialMin (superPolynomialBasis (K := F))
      multiplicityWordWeight (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap).ker)
        ≃ₗ[F] StrictMultiplicityInitialQuotient d :=
  (Submodule.quotEquivOfEq _ _ (strictInitialModule_eq_kernel d)).trans
    ((strictInitialProjection d).toLinearMap.quotKerEquivOfSurjective
      ((strictMultiplicityInitialIdeal d).ringCon.mkₐ_surjective (α := F)))

@[simp] theorem strictInitialToRingEquiv_mk (d : StrictData (K := F) (n := n))
    (x : SuperRing F n) :
    strictInitialToRingEquiv d (Submodule.Quotient.mk x) = strictInitialProjection d x := by
  simp only [strictInitialToRingEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    AlgHom.toLinearMap_apply]

def strictMultiplicityInitialBasis (d : StrictData (K := F) (n := n)) :
    Module.Basis (StrictPowerIndex d.r) F (StrictMultiplicityInitialQuotient d) :=
  (strictMultiplicityPresentation d).initialQuotientBasis.map (strictInitialToRingEquiv d)

@[simp] theorem strictMultiplicityInitialBasis_apply
    (d : StrictData (K := F) (n := n)) (i : StrictPowerIndex d.r) :
    strictMultiplicityInitialBasis d i =
      strictInitialProjection d ((strictMultiplicityPresentation d).representative i) := by
  rw [strictMultiplicityInitialBasis, Module.Basis.map_apply,
    BlockInitial.TriangularPresentation.initialQuotientBasis_apply,
    Submodule.mkQ_apply, strictInitialToRingEquiv_mk]

/-- The normal form in the initial quotient keeps exactly the coefficient block
of the original homogeneous vector. -/
theorem strictInitial_normalForm (d : StrictData (K := F) (n := n))
    (r : ℕ) (x : SuperRing F n)
    (hx : Homogeneous (superPolynomialBasis (K := F)) multiplicityWordWeight r x) :
    strictInitialProjection d x =
      ∑ z : StrictPowerIndex d.r, if strictBasisMultiplicityWeight d z = r then
        (strictCoupledBasis d).repr ((strictIdeal d.beta d.phi).ringCon.mkₐ F x) z •
          strictMultiplicityInitialBasis d z else 0 := by
  have h := (strictMultiplicityPresentation d).initial_component_normal_form r x hx
  have he := congrArg (strictInitialToRingEquiv d) h
  simpa only [map_sum, apply_ite, map_smul, map_zero, Submodule.mkQ_apply,
    AlgHom.toLinearMap_apply, strictInitialToRingEquiv_mk,
    ← strictMultiplicityInitialBasis_apply, strictBasisMultiplicityWeight,
    strictMultiplicityPresentation_basis] using he

/-- Actual ambient multiplication is homogeneous for multiplicity weight. -/
theorem super_word_product_homogeneous (p q : PolynomialRing F n)
    (S T : Finset (OddIndex n)) :
    Homogeneous (superPolynomialBasis (K := F)) multiplicityWordWeight
      (multiplicityWordWeight S + multiplicityWordWeight T)
      ((p • superPolynomialBasis (K := F) S) * (q • superPolynomialBasis (K := F) T)) := by
  obtain ⟨a,U,he,hw⟩ := exterior_basis_mul_weight (K := F) multiplicityModeWeight S T
  rw [superPolynomialBasis_smul, superPolynomialBasis_smul,
    Algebra.TensorProduct.tmul_mul_tmul, he, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', ← superPolynomialBasis_smul]
  by_cases ha : a = 0
  · rw [ha, zero_smul, zero_smul]
    intro V hV
    exact (hV (by simp)).elim
  · have hU := hw ha
    change multiplicityWordWeight U = multiplicityWordWeight S + multiplicityWordWeight T at hU
    rw [← hU]
    exact BlockInitial.homogeneous_single (b := superPolynomialBasis (K := F))
      (weight := multiplicityWordWeight) U (a • (p * q))

theorem super_one_multiplicity_homogeneous :
    Homogeneous (superPolynomialBasis (K := F) (n := n)) multiplicityWordWeight 0 1 := by
  have he : superPolynomialBasis (K := F) (∅ : Finset (OddIndex n)) = 1 := by
    rw [superPolynomialBasis_apply, Module.Basis.exteriorAlgebra_eq_prod_map_sort]
    simp [Algebra.TensorProduct.one_def]
  have h := BlockInitial.homogeneous_single
    (b := superPolynomialBasis (K := F)) (weight := multiplicityWordWeight)
    (∅ : Finset (OddIndex n)) (1 : PolynomialRing F n)
  simpa only [he, one_smul, multiplicityWordWeight, Finset.sum_empty] using h

/-- The exact multiplication constants at zero, in a basis of the actual
initial quotient. -/
theorem strictInitial_basis_mul (d : StrictData (K := F) (n := n))
    (i j : StrictPowerIndex d.r) :
    strictMultiplicityInitialBasis d i * strictMultiplicityInitialBasis d j =
      ∑ k : StrictPowerIndex d.r,
        (WeightRees.multiplicationPolynomial (K := F) (A := StrictQuotient d.beta d.phi)
          (I := StrictPowerIndex d.r)
          (strictCoupledBasis d)
          (strictBasisMultiplicityWeight d) i j k).eval 0 •
            strictMultiplicityInitialBasis d k := by
  classical
  let h := strictMultiplicityPresentation d
  have hx : Homogeneous (superPolynomialBasis (K := F)) multiplicityWordWeight
      (strictBasisMultiplicityWeight d i + strictBasisMultiplicityWeight d j)
      (h.representative i * h.representative j) :=
    super_word_product_homogeneous _ _ _ _
  have he := strictInitial_normalForm d _ _ hx
  have hq (z : StrictPowerIndex d.r) :
      (strictIdeal d.beta d.phi).ringCon.mkₐ F (h.representative z) = strictCoupledBasis d z :=
    (h.basis_apply z).symm
  have hqprod : (strictIdeal d.beta d.phi).ringCon.mkₐ F
      (h.representative i * h.representative j) =
      strictCoupledBasis d i * strictCoupledBasis d j := by
    rw [map_mul, hq, hq]
  rw [hqprod] at he
  rw [strictMultiplicityInitialBasis_apply, strictMultiplicityInitialBasis_apply,
    ← map_mul]
  rw [he]
  apply Finset.sum_congr rfl
  intro k hk
  rw [WeightRees.multiplicationPolynomial_eval_zero
    (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
    (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
    (strictBasisMultiplicityWeight_multiplicative d) i j k]
  split_ifs <;> simp only [zero_smul]

theorem strictInitial_basis_one (d : StrictData (K := F) (n := n)) :
    (1 : StrictMultiplicityInitialQuotient d) =
      ∑ k : StrictPowerIndex d.r,
        (Polynomial.monomial (strictBasisMultiplicityWeight d k)
          ((strictCoupledBasis d).repr 1 k)).eval 0 • strictMultiplicityInitialBasis d k := by
  classical
  have h := strictInitial_normalForm d 0 1 super_one_multiplicity_homogeneous
  rw [show strictInitialProjection d (1 : SuperRing F n) = 1 from
      (strictInitialProjection d).map_one,
    show (strictIdeal d.beta d.phi).ringCon.mkₐ F (1 : SuperRing F n) = 1 from
      ((strictIdeal d.beta d.phi).ringCon.mkₐ F).map_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  rw [WeightRees.unitPolynomial_eval_zero (K := F) (A := StrictQuotient d.beta d.phi)
    (I := StrictPowerIndex d.r)
    (strictCoupledBasis d) (strictBasisMultiplicityWeight d) k]
  split_ifs <;> simp only [zero_smul]

section ZeroFiber

local instance zeroEvaluation : Algebra (Polynomial F) F :=
  (Polynomial.evalRingHom (0 : F)).toAlgebra

set_option maxHeartbeats 1000000 in
/-- The zero fiber, with the canonical polynomial/exterior representatives,
 is the actual smallest-weight quotient as an algebra. -/
def strictMultiplicityFiberZero (d : StrictData (K := F) (n := n)) :
    F ⊗[Polynomial F] StrictMultiplicityRees d ≃ₐ[F]
      StrictMultiplicityInitialQuotient d := by
  let b := strictCoupledBasis d
  let b₀ := strictMultiplicityInitialBasis d
  let w := strictBasisMultiplicityWeight d
  have hweight := strictBasisMultiplicityWeight_multiplicative d
  have h_one := strictInitial_basis_one d
  have h_mul := strictInitial_basis_mul d
  let makeEquiv := WeightRees.fiberAlgEquiv (K := F) (A := StrictQuotient d.beta d.phi)
    (I := StrictPowerIndex d.r) (B := StrictMultiplicityInitialQuotient d)
    (b := b) (weight := w) (hmul := hweight) (c := (0 : F)) (b₀ := b₀)
  let e := makeEquiv (by exact h_one) h_mul
  exact e

end ZeroFiber

section OneFiber

local instance oneEvaluation : Algebra (Polynomial F) F :=
  (Polynomial.evalRingHom (1 : F)).toAlgebra

set_option maxHeartbeats 1000000 in
/-- The unit fiber is the original strict moment algebra. -/
def strictMultiplicityFiberOne (d : StrictData (K := F) (n := n)) :
    F ⊗[Polynomial F] StrictMultiplicityRees d ≃ₐ[F] StrictQuotient d.beta d.phi := by
  let e := WeightRees.fiberOne (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact e

end OneFiber

end PaperVerification.Fermion
