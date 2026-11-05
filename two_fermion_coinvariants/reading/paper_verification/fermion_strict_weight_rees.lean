module

public import PaperVerification.FermionMultiplicityBlocks
public import PaperVerification.FermionWeightRees
public import PaperVerification.FermionWeightReesFiltration

/-!
# The actual strict multiplicity filtration and its finite-free Rees algebra

The filtration is first defined by images of actual ambient vectors whose
exterior coefficients have a specified minimum multiplicity weight. The
triangular normal-form theorem identifies it with the tail filtration of
the actual strict basis. Multiplication of actual exterior words proves
the required product inequality, including zero products.

Fiber identifications and color
actions are developed separately.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators TensorProduct PaperVerification.Fermion.WeightRees

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionStrictWeightRees_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem super_word_product_lowerBound (p q : PolynomialRing F n)
    (S T : Finset (OddIndex n)) :
    BlockInitial.LowerBound (superPolynomialBasis (K := F)) multiplicityWordWeight
      (multiplicityWordWeight S+multiplicityWordWeight T)
      ((p • superPolynomialBasis (K := F) S)*(q • superPolynomialBasis (K := F) T)) := by
  obtain ⟨a,U,he,hw⟩ := exterior_basis_mul_weight (K := F) multiplicityModeWeight S T
  rw [superPolynomialBasis_smul,superPolynomialBasis_smul,
    Algebra.TensorProduct.tmul_mul_tmul,he,TensorProduct.tmul_smul,
    TensorProduct.smul_tmul',←superPolynomialBasis_smul]
  by_cases ha : a=0
  · rw [ha,zero_smul,zero_smul]
    intro V hV
    exact (hV (by simp)).elim
  · have hU := hw ha
    change multiplicityWordWeight U=multiplicityWordWeight S+multiplicityWordWeight T at hU
    rw [←hU]
    exact BlockInitial.lowerBound_single (b := superPolynomialBasis (K := F))
      (weight := multiplicityWordWeight) U (a • (p*q))

def strictBasisMultiplicityWeight (d : StrictData (K := F) (n := n))
    (z : StrictPowerIndex d.r) : ℕ := multiplicityWordWeight z.1

/-- The actual ambient-image descending filtration. -/
def strictMultiplicityFiltration (d : StrictData (K := F) (n := n)) (r : ℕ) :
    Submodule F (StrictQuotient d.beta d.phi) :=
  ((BlockInitial.lowerSubmodule (superPolynomialBasis (K := F)) multiplicityWordWeight r).restrictScalars
    F).map (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap)

theorem strictMultiplicityFiltration_eq_basisTail
    (d : StrictData (K := F) (n := n)) (r : ℕ) :
    strictMultiplicityFiltration d r=
      BlockInitial.lowerSubmodule (strictCoupledBasis d) (strictBasisMultiplicityWeight d) r := by
  ext z
  change (∃ x, BlockInitial.LowerBound (superPolynomialBasis (K := F))
    multiplicityWordWeight r x ∧
    ((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap x = z) ↔
    BlockInitial.LowerBound (strictCoupledBasis d) (strictBasisMultiplicityWeight d) r z
  exact (strictMultiplicityPresentation d).actual_descending_filtration_iff r z

/-- The multiplication inequality is proved on the original quotient product
by lifting the two basis vectors to their actual polynomial/exterior words. -/
theorem strictBasisMultiplicityWeight_multiplicative
    (d : StrictData (K := F) (n := n)) :
    WeightRees.Multiplicative (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d) := by
  intro i j k hk
  let h := strictMultiplicityPresentation d
  let vi : SuperRing F n := monomial i.2.val.val (1 : F) • superPolynomialBasis (K := F) i.1
  let vj : SuperRing F n := monomial j.2.val.val (1 : F) • superPolynomialBasis (K := F) j.1
  let q := ((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap
  have hqi : q vi=strictCoupledBasis d i := by
    simpa only [h,vi,q,strictMultiplicityPresentation_basis,
      strictMultiplicityPresentation_polynomial] using (h.basis_apply i).symm
  have hqj : q vj=strictCoupledBasis d j := by
    simpa only [h,vj,q,strictMultiplicityPresentation_basis,
      strictMultiplicityPresentation_polynomial] using (h.basis_apply j).symm
  have hproduct : q (vi*vj)=strictCoupledBasis d i*strictCoupledBasis d j := by
    change (strictIdeal d.beta d.phi).ringCon.mkₐ F (vi*vj)=_
    rw [map_mul]
    change q vi * q vj = _
    rw [hqi,hqj]
  have hb : BlockInitial.LowerBound (superPolynomialBasis (K := F)) multiplicityWordWeight
      (multiplicityWordWeight i.1+multiplicityWordWeight j.1) (vi*vj) :=
    super_word_product_lowerBound _ _ i.1 j.1
  have hq := (h.actual_descending_filtration_iff
    (multiplicityWordWeight i.1+multiplicityWordWeight j.1) (q (vi*vj))).mp ⟨vi*vj,hb,rfl⟩
  rw [hproduct] at hq
  simp only [h,strictMultiplicityPresentation_basis] at hq
  exact hq k hk

def StrictMultiplicityRees (d : StrictData (K := F) (n := n)) :=
  WeightRees.algebra (K := F) (A := StrictQuotient d.beta d.phi)
    (I := StrictPowerIndex d.r)
    (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
    (strictBasisMultiplicityWeight_multiplicative d)

set_option maxHeartbeats 1000000 in
/-- These instances retain the named Rees subalgebra while selecting exactly
its canonical operations and scalar actions from the Laurent construction. -/
instance strictMultiplicityReesRing (d : StrictData (K := F) (n := n)) :
    Ring (StrictMultiplicityRees d) := by
  let r := WeightRees.algebraRing (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact r

set_option maxHeartbeats 1000000 in
instance strictMultiplicityReesPolynomialAlgebra (d : StrictData (K := F) (n := n)) :
    Algebra (Polynomial F) (StrictMultiplicityRees d) := by
  let a := WeightRees.algebraPolynomialAlgebra (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact a

@[reducible] instance strictMultiplicityReesPolynomialModule
    (d : StrictData (K := F) (n := n)) : Module (Polynomial F) (StrictMultiplicityRees d) :=
  @Algebra.toModule (Polynomial F) (StrictMultiplicityRees d) _ _
    (strictMultiplicityReesPolynomialAlgebra d)

set_option maxHeartbeats 1000000 in
instance strictMultiplicityReesFieldAlgebra (d : StrictData (K := F) (n := n)) :
    Algebra F (StrictMultiplicityRees d) := by
  let a := WeightRees.algebraBaseAlgebra (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact a

@[reducible] instance strictMultiplicityReesFieldModule
    (d : StrictData (K := F) (n := n)) : Module F (StrictMultiplicityRees d) :=
  @Algebra.toModule F (StrictMultiplicityRees d) _ _
    (strictMultiplicityReesFieldAlgebra d)

set_option maxHeartbeats 1000000 in
instance strictMultiplicityReesScalarTower (d : StrictData (K := F) (n := n)) :
    IsScalarTower F (Polynomial F) (StrictMultiplicityRees d) := by
  let h := WeightRees.algebraScalarTower (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact h

set_option maxHeartbeats 1000000 in
def strictMultiplicityReesBasis (d : StrictData (K := F) (n := n)) :
    Module.Basis (StrictPowerIndex d.r) (Polynomial F) (StrictMultiplicityRees d) := by
  let b := WeightRees.basis (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact b

set_option maxHeartbeats 1000000 in
theorem strictMultiplicityRees_finite_free (d : StrictData (K := F) (n := n)) :
    Module.Finite (Polynomial F) (StrictMultiplicityRees d) ∧
      Module.Free (Polynomial F) (StrictMultiplicityRees d) := by
  let h := WeightRees.finite_free (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact h

set_option maxHeartbeats 1000000 in
theorem strictMultiplicityRees_flat (d : StrictData (K := F) (n := n)) :
    Module.Flat (Polynomial F) (StrictMultiplicityRees d) := by
  let h := WeightRees.flat (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact h

/-- The algebra is exactly the extended Rees algebra of the independently
defined actual quotient filtration. -/
theorem strictMultiplicityRees_mem_iff (d : StrictData (K := F) (n := n))
    (z : LaurentPolynomial (StrictQuotient d.beta d.phi)) :
    z∈StrictMultiplicityRees d ↔
      ∀ e,z.coeff e∈strictMultiplicityFiltration d (-e).toNat := by
  rw [StrictMultiplicityRees,WeightRees.mem_algebra_iff_filtration]
  exact forall_congr' fun e ↦ by rw [strictMultiplicityFiltration_eq_basisTail]

end PaperVerification.Fermion
