module

public import PaperVerification.FermionSuperHighestForms
public import PaperVerification.FermionTwoSidedBasisSpan

/-!
# Every actual paired relation has its prescribed power highest form

Odd weights are `uᵢ/rᵢ` for theta and `vᵢ/rᵢ` for xi, multiplied by the
common integer denominator. Thus all four moments of index k have the same
weight `(s+k) ∏ rᵢ`. The calculation also covers every left/right ambient
basis multiple, the family that spans the actual two-sided ideal.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators TensorProduct

variable {K : Type*} [CommRing K] {n : ℕ}

local instance FermionPairedMomentHighest_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance FermionPairedMomentHighest_localInst_2 : PartialOrder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPartialOrder
local instance FermionPairedMomentHighest_localInst_3 : Preorder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPreorder
local instance FermionPairedMomentHighest_localInst_4 : LE (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLE
local instance FermionPairedMomentHighest_localInst_5 : LT (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLT
local instance FermionPairedMomentHighest_localInst_6 : DecidableEq (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toDecidableEq

def pairedPolynomialCoefficient (β : Fin n → K)
    (a b : Fin n → PolynomialRing K n) : MomentKind → Fin n → PolynomialRing K n
  | .polynomial,i => C (β i)*a i*b i
  | .theta,i => b i
  | .xi,i => C (β i)*a i
  | .mixed,_ => 1

def pairedMomentWord : MomentKind → Fin n → Finset (OddIndex n)
  | .polynomial,_ => ∅
  | .theta,i => {Sum.inl i}
  | .xi,i => {Sum.inr i}
  | .mixed,i => {Sum.inl i,Sum.inr i}

theorem pairedCoefficients_eq_tensor (β : Fin n → K)
    (a b : Fin n → PolynomialRing K n) (kind : MomentKind) (i : Fin n) :
    pairedCoefficients β a b kind i =
      pairedPolynomialCoefficient β a b kind i ⊗ₜ[K]
        (Pi.basisFun K (OddIndex n)).ExteriorAlgebra (pairedMomentWord kind i) := by
  have hempty : (Pi.basisFun K (OddIndex n)).ExteriorAlgebra (∅ : Finset (OddIndex n)) = 1 := by
    simpa only [Finset.sort_empty, List.map_nil, List.prod_nil] using
      (Module.Basis.exteriorAlgebra_eq_prod_map_sort
        (Pi.basisFun K (OddIndex n)) (∅ : Finset (OddIndex n)))
  have hpair : (Pi.basisFun K (OddIndex n)).ExteriorAlgebra {Sum.inl i,Sum.inr i} =
      ExteriorAlgebra.ι K (Pi.single (Sum.inl i) 1) *
        ExteriorAlgebra.ι K (Pi.single (Sum.inr i) 1) := by
    have hlt : @LT.lt (OddIndex n)
        (LinearOrder.lift' modeRank modeRank_injective).toLT (Sum.inl i) (Sum.inr i) := by
      change i.val < n + i.val
      omega
    simpa only [Pi.basisFun_apply] using
      (@TauCeti.ExteriorAlgebra.basis_pair K (OddModule K n) _ _ _ (OddIndex n)
        (LinearOrder.lift' modeRank modeRank_injective)
        (Pi.basisFun K (OddIndex n)) (Sum.inl i) (Sum.inr i) hlt)
  have hsingle (D : DecidableEq (OddIndex n)) (j : OddIndex n) :
      @Pi.single (OddIndex n) (fun _ ↦ K) (fun _ ↦ inferInstance) D j (1 : K) =
        (Pi.basisFun K (OddIndex n)) j := by
    have hD : D = (inferInstance : DecidableEq (OddIndex n)) := Subsingleton.elim _ _
    cases hD
    rw [Pi.basisFun_apply]
  cases kind with
  | polynomial =>
      simp only [pairedCoefficients,pairedPolynomialCoefficient,pairedMomentWord,hempty,
        Algebra.TensorProduct.one_def,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  | theta =>
      simp only [pairedCoefficients,pairedPolynomialCoefficient,pairedMomentWord,theta,
        Algebra.TensorProduct.includeRight_apply,TauCeti.ExteriorAlgebra.basis_singleton,
        Pi.basisFun_apply,TensorProduct.smul_tmul',smul_eq_mul,mul_one] <;> simp only [hsingle]
  | xi =>
      simp only [pairedCoefficients,pairedPolynomialCoefficient,pairedMomentWord,xi,
        Algebra.TensorProduct.includeRight_apply,TauCeti.ExteriorAlgebra.basis_singleton,
        Pi.basisFun_apply,TensorProduct.smul_tmul',smul_eq_mul,mul_one] <;> simp only [hsingle]
  | mixed =>
      simp only [pairedCoefficients,pairedPolynomialCoefficient,pairedMomentWord,theta,xi,
        Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.tmul_mul_tmul,one_mul,hpair] <;> simp only [hsingle]

theorem pairedMoment_eq_tensor_sum (β : Fin n → K)
    (φ a b : Fin n → PolynomialRing K n) (kind : MomentKind) (k : ℕ) :
    moment φ (pairedCoefficients β a b kind) k =
      ∑ i, (φ i^k * pairedPolynomialCoefficient β a b kind i) ⊗ₜ[K]
        (Pi.basisFun K (OddIndex n)).ExteriorAlgebra (pairedMomentWord kind i) := by
  simp only [moment,pairedCoefficients_eq_tensor,TensorProduct.smul_tmul',smul_eq_mul]

def pairedOddWeight (d : PairedData (K := K) (n := n)) : OddIndex n → ℕ
  | .inl i => d.u i * coveringWeight d.r i
  | .inr i => d.v i * coveringWeight d.r i

def pairedCoefficientDegree (d : PairedData (K := K) (n := n)) : MomentKind → Fin n → ℕ
  | .polynomial,_ => d.s * ∏ j, d.r j
  | .theta,i => d.v i * coveringWeight d.r i
  | .xi,i => d.u i * coveringWeight d.r i
  | .mixed,_ => 0

theorem pairedCoefficientDegree_add_word (d : PairedData (K := K) (n := n))
    (kind : MomentKind) (i : Fin n) :
    pairedCoefficientDegree d kind i +
      wordPolynomialWeight (pairedOddWeight d) (pairedMomentWord kind i) = d.s * ∏ j, d.r j := by
  have hd : d.u i * coveringWeight d.r i+d.v i * coveringWeight d.r i = d.s * ∏ j,d.r j := by
    rw [← Nat.add_mul,d.degree_split i]
    have hw := coveringWeight_mul d.r i
    nlinarith
  cases kind <;>
    simp only [pairedCoefficientDegree,wordPolynomialWeight,pairedMomentWord,
      Finset.sum_empty,Finset.sum_singleton,Finset.sum_pair (Sum.inl_ne_inr),
      pairedOddWeight,add_zero,zero_add] <;> omega

theorem pairedCoefficient_hasTop (d : PairedData (K := K) (n := n))
    (kind : MomentKind) (i : Fin n) :
    Filtered.HasTop (coveringWeight d.r) (pairedCoefficientDegree d kind i)
      (pairedPolynomialCoefficient d.beta d.a d.b kind i)
      (pairedPolynomialCoefficient d.beta (fun j ↦ X j^d.u j) (fun j ↦ X j^d.v j) kind i) := by
  cases kind with
  | polynomial =>
      have h := Filtered.HasTop.mul _
        (Filtered.HasTop.mul _ (Filtered.HasTop.C _ (d.beta i)) (paired_a_hasTop d i))
        (paired_b_hasTop d i)
      have hd : 0+d.u i * coveringWeight d.r i+d.v i * coveringWeight d.r i =
          d.s * ∏ j,d.r j := by
        rw [zero_add,← Nat.add_mul,d.degree_split i]
        have hw := coveringWeight_mul d.r i
        nlinarith
      simpa only [pairedPolynomialCoefficient,pairedCoefficientDegree,hd] using h
  | theta => exact paired_b_hasTop d i
  | xi => simpa only [pairedPolynomialCoefficient,pairedCoefficientDegree,zero_add] using
      Filtered.HasTop.mul _ (Filtered.HasTop.C _ (d.beta i)) (paired_a_hasTop d i)
  | mixed => exact Filtered.HasTop.one _

def pairedFiniteRelation (d : PairedData (K := K) (n := n)) (j : MomentKind × Fin n) : SuperRing K n :=
  moment d.phi (pairedCoefficients d.beta d.a d.b j.1) j.2

def pairedPowerFiniteRelation (d : PairedData (K := K) (n := n)) (j : MomentKind × Fin n) : SuperRing K n :=
  moment (fun i ↦ (X i : PolynomialRing K n)^d.r i)
    (pairedCoefficients d.beta (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) j.1) j.2

theorem pairedFiniteRelation_ideal (d : PairedData (K := K) (n := n)) :
    TwoSidedIdeal.span (Set.range (pairedFiniteRelation d)) = pairedIdeal d.beta d.phi d.a d.b :=
  (pairedIdeal_finite d.beta d.phi d.a d.b).symm

theorem pairedPowerFiniteRelation_ideal (d : PairedData (K := K) (n := n)) :
    TwoSidedIdeal.span (Set.range (pairedPowerFiniteRelation d)) =
      pairedIdeal d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) :=
  (pairedIdeal_finite d.beta (fun i ↦ (X i : PolynomialRing K n)^d.r i)
    (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).symm

def pairedRelationMultipleDegree (d : PairedData (K := K) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) : ℕ :=
  superMonomialWeight (coveringWeight d.r) (pairedOddWeight d) z.1 +
    ((d.s+z.2.1.2.val) * ∏ i,d.r i) +
      superMonomialWeight (coveringWeight d.r) (pairedOddWeight d) z.2.2

theorem pairedRelationMultiple_hasTop (d : PairedData (K := K) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) :
    BasisFiltered.HasTop (superMonomialBasis (K := K))
      (superMonomialWeight (coveringWeight d.r) (pairedOddWeight d))
      (pairedRelationMultipleDegree d z)
      (basisRelationMultiple superMonomialBasis (pairedFiniteRelation d) z)
      (basisRelationMultiple superMonomialBasis (pairedPowerFiniteRelation d) z) := by
  classical
  unfold basisRelationMultiple pairedFiniteRelation pairedPowerFiniteRelation
  rw [pairedMoment_eq_tensor_sum,pairedMoment_eq_tensor_sum]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply BasisFiltered.HasTop.sum _ _ Finset.univ _ _ _
  intro i hi
  have hterm := Filtered.HasTop.mul (coveringWeight d.r)
    (Filtered.HasTop.pow _ (paired_phi_hasTop d i) z.2.1.2.val)
    (pairedCoefficient_hasTop d z.2.1.1 i)
  have h := hasTop_basis_multiples (coveringWeight d.r) (pairedOddWeight d)
    _ _ _ hterm (pairedMomentWord z.2.1.1 i) z.1 z.2.2
  have hd : z.2.1.2.val*(∏ j,d.r j)+pairedCoefficientDegree d z.2.1.1 i+
      wordPolynomialWeight (pairedOddWeight d) (pairedMomentWord z.2.1.1 i) =
        (d.s+z.2.1.2.val)*∏ j,d.r j := by
    rw [Nat.add_assoc,pairedCoefficientDegree_add_word]
    ring
  simpa only [pairedRelationMultipleDegree,hd] using h

end PaperVerification.Fermion
