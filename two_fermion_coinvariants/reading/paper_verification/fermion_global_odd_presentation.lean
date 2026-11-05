module

public import PaperVerification.FermionLocalSuper

/-!
# The global separated quotient as an actual exterior presentation

The ordinary moment relations are first imposed in their literal polynomial
quotient. Scalar extension by this quotient does not change the superalgebra,
since its action already descends. The three remaining odd relation families
are then checked in the exterior algebra over this coefficient ring.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct BigOperators Classical

namespace PaperVerification.Fermion
namespace SeparatedPairedData

variable {F : Type*} [Field F] {n : ℕ} (d : SeparatedPairedData F n)

def ordinaryA (i : Fin n) : d.O.Ordinary := Polynomial.aeval (d.O.ordinaryX i) (d.a i)
def ordinaryB (i : Fin n) : d.O.Ordinary := Polynomial.aeval (d.O.ordinaryX i) (d.b i)

def globalSuperPolynomialBaseEquiv :
    d.SuperQuotient ≃ₐ[d.O.Ordinary] d.O.Ordinary ⊗[PolynomialRing F n] d.SuperQuotient := by
  letI : TensorProduct.CompatibleSMul (PolynomialRing F n) d.O.Ordinary
      d.O.Ordinary d.SuperQuotient :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := PolynomialRing F n) (A := d.O.Ordinary) d.O.Ordinary d.SuperQuotient
      (show Function.Surjective (algebraMap (PolynomialRing F n) d.O.Ordinary)
        from Ideal.Quotient.mk_surjective)
  exact (Algebra.TensorProduct.lid d.O.Ordinary d.SuperQuotient).symm.trans
    (Algebra.TensorProduct.equivOfCompatibleSMul (PolynomialRing F n)
      d.O.Ordinary d.O.Ordinary d.O.Ordinary d.SuperQuotient)

def ordinaryAmbientEquiv :
    d.O.Ordinary ⊗[PolynomialRing F n] SuperRing F n ≃ₐ[d.O.Ordinary]
      ClusterExterior d.O.Ordinary (Fin n) :=
  scalarExteriorBaseChange F (PolynomialRing F n) d.O.Ordinary (OddIndex n)

@[simp] theorem ordinaryAmbientEquiv_theta (i : Fin n) :
    d.ordinaryAmbientEquiv (1 ⊗ₜ[PolynomialRing F n] theta F n i)=clusterTheta i := by
  rw [theta_as_tensor_generator]
  change scalarExteriorBaseChange F (PolynomialRing F n) d.O.Ordinary (OddIndex n)
    (1 ⊗ₜ[PolynomialRing F n] (1 ⊗ₜ[F] exteriorGenerator (A := F) (Sum.inl i))) =
      exteriorGenerator (A := d.O.Ordinary) (Sum.inl i)
  calc
    _ = ((1 : PolynomialRing F n) • (1 : d.O.Ordinary)) •
        exteriorGenerator (A := d.O.Ordinary) (Sum.inl i) :=
      scalarExteriorBaseChange_generator (R := F) (P := PolynomialRing F n)
        (S := d.O.Ordinary) (ι := OddIndex n) 1 1 (Sum.inl i)
    _ = _ := by
      rw [one_smul (PolynomialRing F n) (1 : d.O.Ordinary),
        one_smul d.O.Ordinary (exteriorGenerator (A := d.O.Ordinary) (Sum.inl i))]

@[simp] theorem ordinaryAmbientEquiv_xi (i : Fin n) :
    d.ordinaryAmbientEquiv (1 ⊗ₜ[PolynomialRing F n] xi F n i)=clusterXi i := by
  rw [xi_as_tensor_generator]
  change scalarExteriorBaseChange F (PolynomialRing F n) d.O.Ordinary (OddIndex n)
    (1 ⊗ₜ[PolynomialRing F n] (1 ⊗ₜ[F] exteriorGenerator (A := F) (Sum.inr i))) =
      exteriorGenerator (A := d.O.Ordinary) (Sum.inr i)
  calc
    _ = ((1 : PolynomialRing F n) • (1 : d.O.Ordinary)) •
        exteriorGenerator (A := d.O.Ordinary) (Sum.inr i) :=
      scalarExteriorBaseChange_generator (R := F) (P := PolynomialRing F n)
        (S := d.O.Ordinary) (ι := OddIndex n) 1 1 (Sum.inr i)
    _ = _ := by
      rw [one_smul (PolynomialRing F n) (1 : d.O.Ordinary),
        one_smul d.O.Ordinary (exteriorGenerator (A := d.O.Ordinary) (Sum.inr i))]

def ordinaryPolynomialMap : PolynomialRing F n →ₐ[F] d.O.Ordinary :=
  d.O.ordinaryMk

@[simp] theorem ordinaryPolynomialMap_C (c : F) :
    d.ordinaryPolynomialMap (MvPolynomial.C c) = algebraMap F d.O.Ordinary c := by
  simpa only [MvPolynomial.algebraMap_eq] using d.ordinaryPolynomialMap.commutes c

@[simp] theorem ordinaryPolynomialMap_x (i : Fin n) :
    d.ordinaryPolynomialMap (MvPolynomial.X i)=d.O.ordinaryX i := rfl

@[simp] theorem ordinaryPolynomialMap_phi (i : Fin n) :
    d.ordinaryPolynomialMap (d.phiPolynomial i)=d.O.ordinaryNode i := by
  rw [phiPolynomial,←Polynomial.aeval_algHom_apply,ordinaryPolynomialMap_x]
  rfl

@[simp] theorem ordinaryPolynomialMap_a (i : Fin n) :
    d.ordinaryPolynomialMap (d.aPolynomial i)=d.ordinaryA i := by
  rw [aPolynomial,←Polynomial.aeval_algHom_apply,ordinaryPolynomialMap_x]
  rfl

@[simp] theorem ordinaryPolynomialMap_b (i : Fin n) :
    d.ordinaryPolynomialMap (d.bPolynomial i)=d.ordinaryB i := by
  rw [bPolynomial,←Polynomial.aeval_algHom_apply,ordinaryPolynomialMap_x]
  rfl

def ordinaryAmbientMap :
    SuperRing F n →ₐ[PolynomialRing F n] ClusterExterior (d.O.Ordinary) (Fin n) :=
  ((d.ordinaryAmbientEquiv).toAlgHom.restrictScalars (PolynomialRing F n)).comp
    Algebra.TensorProduct.includeRight

@[simp] theorem ordinaryAmbientMap_theta (i : Fin n) :
    d.ordinaryAmbientMap (theta F n i)=clusterTheta i :=
  d.ordinaryAmbientEquiv_theta i

@[simp] theorem ordinaryAmbientMap_xi (i : Fin n) :
    d.ordinaryAmbientMap (xi F n i)=clusterXi i :=
  d.ordinaryAmbientEquiv_xi i

theorem ordinaryAmbientMap_smul (p : PolynomialRing F n) (a : SuperRing F n) :
    d.ordinaryAmbientMap (p • a)=
      d.ordinaryPolynomialMap p • d.ordinaryAmbientMap a := by
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul d.O.Ordinary p (d.ordinaryAmbientMap a)).symm

theorem ordinaryAmbientMap_polynomial_scalar (p : PolynomialRing F n) :
    d.ordinaryAmbientMap
      ((Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n) p)=
      algebraMap (d.O.Ordinary)
        (ClusterExterior (d.O.Ordinary) (Fin n)) (d.ordinaryPolynomialMap p) := by
  exact (d.ordinaryAmbientMap).commutes p

def ordinaryOddIdeal : TwoSidedIdeal (ClusterExterior (d.O.Ordinary) (Fin n)) :=
  separatedOddIdeal (d.O.ordinaryNode)
    (fun i ↦ algebraMap F (d.O.Ordinary) (d.beta i))
    (d.ordinaryA) (d.ordinaryB)

def ordinaryRelationImage (kind : MomentKind) (k : ℕ) :
    ClusterExterior (d.O.Ordinary) (Fin n) :=
  match kind with
  | .polynomial => 0
  | .theta => separatedOddCurrent (d.O.ordinaryNode)
      (fun i ↦ algebraMap F (d.O.Ordinary) (d.beta i))
      (d.ordinaryA) (d.ordinaryB) .theta k
  | .xi => separatedOddCurrent (d.O.ordinaryNode)
      (fun i ↦ algebraMap F (d.O.Ordinary) (d.beta i))
      (d.ordinaryA) (d.ordinaryB) .xi k
  | .mixed => separatedOddCurrent (d.O.ordinaryNode)
      (fun i ↦ algebraMap F (d.O.Ordinary) (d.beta i))
      (d.ordinaryA) (d.ordinaryB) .mixed k

theorem ordinaryAmbientMap_relation (kind : MomentKind) (k : ℕ) :
    d.ordinaryAmbientMap
      (moment d.phiPolynomial (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k)=
        d.ordinaryRelationImage kind k := by
  cases kind with
  | polynomial =>
    have hs :
        moment d.phiPolynomial
          (pairedCoefficients d.beta d.aPolynomial d.bPolynomial .polynomial) k =
        (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n)
          (moment d.phiPolynomial
            (fun i ↦ MvPolynomial.C (d.beta i)*
              Polynomial.aeval (d.phiPolynomial i) d.G) k) := by
      rw [includeLeft_scalar_moment]
      congr 1
      funext i
      simp only [pairedCoefficients,mul_assoc,d.polynomial_paired_product]
    rw [hs,d.ordinaryAmbientMap_polynomial_scalar]
    have hm :
        d.ordinaryPolynomialMap
          (moment d.phiPolynomial
            (fun i ↦ MvPolynomial.C (d.beta i)*
              Polynomial.aeval (d.phiPolynomial i) d.G) k)=0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (ordinaryMoment_mem d.phiPolynomial d.beta d.G k)
    rw [hm,map_zero]
    rfl
  | theta =>
    simp only [moment,pairedCoefficients,map_sum,d.ordinaryAmbientMap_smul,map_pow,
      ordinaryPolynomialMap_phi,ordinaryPolynomialMap_b,ordinaryAmbientMap_theta,
      ordinaryRelationImage,separatedOddCurrent]
  | xi =>
    simp only [moment,pairedCoefficients,map_sum,d.ordinaryAmbientMap_smul,map_pow,
      ordinaryPolynomialMap_phi,map_mul,ordinaryPolynomialMap_a,ordinaryAmbientMap_xi,
      ordinaryPolynomialMap_C,ordinaryRelationImage,separatedOddCurrent]
  | mixed =>
    simp only [moment,pairedCoefficients,map_sum,d.ordinaryAmbientMap_smul,map_pow,
      ordinaryPolynomialMap_phi,map_mul,ordinaryAmbientMap_theta,ordinaryAmbientMap_xi,
      ordinaryRelationImage,separatedOddCurrent]

theorem ordinaryRelationImage_mem (kind : MomentKind) (k : ℕ) :
    d.ordinaryRelationImage kind k∈d.ordinaryOddIdeal := by
  cases kind with
  | polynomial => exact (d.ordinaryOddIdeal).zero_mem
  | theta => exact TwoSidedIdeal.subset_span ⟨(.theta,k),rfl⟩
  | xi => exact TwoSidedIdeal.subset_span ⟨(.xi,k),rfl⟩
  | mixed => exact TwoSidedIdeal.subset_span ⟨(.mixed,k),rfl⟩

theorem ordinaryAmbientMap_ideal (a : SuperRing F n) (ha : a∈d.superIdeal) :
    d.ordinaryAmbientMap a∈d.ordinaryOddIdeal := by
  have hle : d.superIdeal≤(d.ordinaryOddIdeal).comap (d.ordinaryAmbientMap).toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨kind,k⟩,rfl⟩
    change moment d.phiPolynomial
      (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k ∈
      (d.ordinaryOddIdeal).comap (d.ordinaryAmbientMap).toRingHom
    rw [TwoSidedIdeal.mem_comap]
    change d.ordinaryAmbientMap
      (moment d.phiPolynomial (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k)
      ∈ d.ordinaryOddIdeal
    rw [d.ordinaryAmbientMap_relation]
    exact d.ordinaryRelationImage_mem kind k
  have h := hle ha
  rw [TwoSidedIdeal.mem_comap] at h
  exact h

def ordinaryTensorIdeal :=
  tensorTwoSidedIdeal (PolynomialRing F n) (d.O.Ordinary) (SuperRing F n) d.superIdeal

theorem ordinaryAmbientEquiv_ideal (a : d.O.Ordinary ⊗[PolynomialRing F n] SuperRing F n)
    (ha : a∈d.ordinaryTensorIdeal) :
    d.ordinaryAmbientEquiv a∈d.ordinaryOddIdeal := by
  have hle : d.ordinaryTensorIdeal≤
      (d.ordinaryOddIdeal).comap (d.ordinaryAmbientEquiv).toRingEquiv.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨a,ha,rfl⟩
    change (Algebra.TensorProduct.includeRight : SuperRing F n →ₐ[PolynomialRing F n]
      d.O.Ordinary ⊗[PolynomialRing F n] SuperRing F n) a ∈
      (d.ordinaryOddIdeal).comap (d.ordinaryAmbientEquiv).toRingEquiv.toRingHom
    rw [TwoSidedIdeal.mem_comap]
    exact d.ordinaryAmbientMap_ideal a ha
  have h := hle ha
  rw [TwoSidedIdeal.mem_comap] at h
  exact h

theorem ordinaryAmbientEquiv_symm_ideal
    (b : ClusterExterior (d.O.Ordinary) (Fin n)) (hb : b∈d.ordinaryOddIdeal) :
    (d.ordinaryAmbientEquiv).symm b∈d.ordinaryTensorIdeal := by
  have hgen (kind : MomentKind) (k : ℕ) :
      (d.ordinaryAmbientEquiv).symm (d.ordinaryRelationImage kind k)
        ∈d.ordinaryTensorIdeal := by
    rw [←d.ordinaryAmbientMap_relation kind k]
    change (d.ordinaryAmbientEquiv).symm
      (d.ordinaryAmbientEquiv (1 ⊗ₜ[PolynomialRing F n]
        moment d.phiPolynomial (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k))∈_
    rw [AlgEquiv.symm_apply_apply]
    apply TwoSidedIdeal.subset_span
    refine ⟨_,TwoSidedIdeal.subset_span ⟨(kind,k),rfl⟩,rfl⟩
  have hle : d.ordinaryOddIdeal≤
      (d.ordinaryTensorIdeal).comap (d.ordinaryAmbientEquiv).symm.toRingEquiv.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro b ⟨⟨family,k⟩,rfl⟩
    change separatedOddCurrent d.O.ordinaryNode
      (fun i ↦ algebraMap F d.O.Ordinary (d.beta i)) d.ordinaryA d.ordinaryB family k ∈
      (d.ordinaryTensorIdeal).comap (d.ordinaryAmbientEquiv).symm.toRingEquiv.toRingHom
    rw [TwoSidedIdeal.mem_comap]
    cases family with
    | theta => exact hgen .theta k
    | xi => exact hgen .xi k
    | mixed => exact hgen .mixed k
  have h := hle hb
  rw [TwoSidedIdeal.mem_comap] at h
  exact h

/-- The actual global super quotient is the separated odd exterior quotient
over the actual ordinary moment algebra. -/
def globalSuperEquivOddPresentation :
    d.SuperQuotient ≃ₐ[d.O.Ordinary]
      SeparatedOddQuotient (d.O.ordinaryNode)
        (fun i ↦ algebraMap F (d.O.Ordinary) (d.beta i))
        (d.ordinaryA) (d.ordinaryB) :=
  (d.globalSuperPolynomialBaseEquiv).trans
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.Ordinary) d.superIdeal).trans
      (twoSidedQuotientEquiv (d.ordinaryAmbientEquiv)
        (d.ordinaryTensorIdeal) (d.ordinaryOddIdeal)
        (d.ordinaryAmbientEquiv_ideal) (d.ordinaryAmbientEquiv_symm_ideal)))


end SeparatedPairedData
end PaperVerification.Fermion
