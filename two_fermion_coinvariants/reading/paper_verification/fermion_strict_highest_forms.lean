module

public import PaperVerification.FermionStrictBaseChange
public import PaperVerification.FermionPairedMomentHighest

/-!
# Strict highest forms with both exterior weights zero

The strict filtration is defined independently of the paired extension:
every theta and xi has weight zero. Ordinary moment k has degree k+1;
the two odd moments and the mixed moment have degree k. Clearing the
positive covering denominators gives the literal integer weights below.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionStrictHighestForms_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def strictPolynomialCoefficient (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    MomentKind → Fin n → PolynomialRing R n
  | .polynomial,i => C (β i)*φ i
  | .theta,_ => 1
  | .xi,i => C (β i)
  | .mixed,_ => 1

theorem strictCoefficients_eq_tensor (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (kind : MomentKind) (i : Fin n) :
    strictCoefficients β φ kind i=
      strictPolynomialCoefficient β φ kind i ⊗ₜ[R]
        (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (pairedMomentWord kind i) := by
  cases kind with
  | polynomial =>
      simpa only [pairedCoefficients,strictCoefficients,pairedPolynomialCoefficient,
        strictPolynomialCoefficient,mul_one] using
        pairedCoefficients_eq_tensor β φ (fun _ ↦ 1) .polynomial i
  | theta =>
      simpa only [pairedCoefficients,strictCoefficients,pairedPolynomialCoefficient,
        strictPolynomialCoefficient,one_smul] using
        pairedCoefficients_eq_tensor β (fun _ ↦ 1) (fun _ ↦ 1) .theta i
  | xi =>
      simpa only [pairedCoefficients,strictCoefficients,pairedPolynomialCoefficient,
        strictPolynomialCoefficient,mul_one] using
        pairedCoefficients_eq_tensor β (fun _ ↦ 1) (fun _ ↦ 1) .xi i
  | mixed =>
      exact pairedCoefficients_eq_tensor β (fun _ ↦ 1) (fun _ ↦ 1) .mixed i

theorem strictMoment_eq_tensor_sum (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (kind : MomentKind) (k : ℕ) :
    moment φ (strictCoefficients β φ kind) k=
      ∑ i,(φ i^k*strictPolynomialCoefficient β φ kind i) ⊗ₜ[R]
        (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (pairedMomentWord kind i) := by
  simp only [moment,strictCoefficients_eq_tensor,TensorProduct.smul_tmul',smul_eq_mul]

def strictSuperWeight (d : StrictData (K := R) (n := n)) : SuperMonomialIndex n → ℕ :=
  superMonomialWeight (coveringWeight d.r) (fun _ ↦ 0)

@[simp] theorem strictSuperWeight_apply (d : StrictData (K := R) (n := n))
    (z : SuperMonomialIndex n) : strictSuperWeight d z=Finsupp.weight (coveringWeight d.r) z.1 := by
  simp only [strictSuperWeight,superMonomialWeight,wordPolynomialWeight,Finset.sum_const_zero,add_zero]

def strictCoefficientDegree (d : StrictData (K := R) (n := n)) : MomentKind → ℕ
  | .polynomial => ∏ i,d.r i
  | .theta | .xi | .mixed => 0

theorem strictCoefficient_hasTop (d : StrictData (K := R) (n := n))
    (kind : MomentKind) (i : Fin n) :
    Filtered.HasTop (coveringWeight d.r) (strictCoefficientDegree d kind)
      (strictPolynomialCoefficient d.beta d.phi kind i)
      (strictPolynomialCoefficient d.beta (fun j ↦ X j^d.r j) kind i) := by
  cases kind with
  | polynomial =>
      simpa only [strictPolynomialCoefficient,strictCoefficientDegree,StrictData.pairedExtension,zero_add] using
        Filtered.HasTop.mul _ (Filtered.HasTop.C _ (d.beta i)) (paired_phi_hasTop d.pairedExtension i)
  | theta => exact Filtered.HasTop.one _
  | xi => exact Filtered.HasTop.C _ (d.beta i)
  | mixed => exact Filtered.HasTop.one _

def strictPowerFiniteRelation (d : StrictData (K := R) (n := n)) :
    MomentKind × Fin n → SuperRing R n := strictFiniteRelation d.power

theorem strictPowerFiniteRelation_ideal (d : StrictData (K := R) (n := n)) :
    TwoSidedIdeal.span (Set.range (strictPowerFiniteRelation d))=
      strictIdeal d.beta (fun i ↦ X i^d.r i) := strictFiniteRelation_ideal d.power

def strictRelationMultipleDegree (d : StrictData (K := R) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) : ℕ :=
  strictSuperWeight d z.1+
    (z.2.1.2.val*(∏ i,d.r i)+strictCoefficientDegree d z.2.1.1)+strictSuperWeight d z.2.2

theorem strictRelationMultiple_hasTop (d : StrictData (K := R) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) :
    BasisFiltered.HasTop (superMonomialBasis (K := R)) (strictSuperWeight d)
      (strictRelationMultipleDegree d z)
      (basisRelationMultiple superMonomialBasis (strictFiniteRelation d) z)
      (basisRelationMultiple superMonomialBasis (strictPowerFiniteRelation d) z) := by
  classical
  unfold basisRelationMultiple strictPowerFiniteRelation strictFiniteRelation
  rw [strictMoment_eq_tensor_sum,strictMoment_eq_tensor_sum]
  simp only [Finset.mul_sum,Finset.sum_mul,StrictData.power]
  apply BasisFiltered.HasTop.sum _ _ Finset.univ _ _ _
  intro i hi
  have hterm := Filtered.HasTop.mul (coveringWeight d.r)
    (Filtered.HasTop.pow _ (paired_phi_hasTop d.pairedExtension i) z.2.1.2.val)
    (strictCoefficient_hasTop d z.2.1.1 i)
  have h := hasTop_basis_multiples (coveringWeight d.r) (fun _ : OddIndex n ↦ 0)
    _ _ _ hterm (pairedMomentWord z.2.1.1 i) z.1 z.2.2
  simpa only [strictRelationMultipleDegree,strictSuperWeight,wordPolynomialWeight,
    StrictData.pairedExtension,Finset.sum_const_zero,add_zero] using h

end PaperVerification.Fermion
