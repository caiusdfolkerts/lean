module

public import PaperVerification.FermionLocalSuper

/-!
# Identification of the actual localized super quotient with its exterior presentation

The image of every original relation is checked. Ordinary relations become
zero in the actual local coefficient algebra, and the three odd relation
families become the literal separated exterior currents.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct BigOperators Classical

namespace PaperVerification.Fermion
namespace SeparatedPairedData

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)

def localPolynomialMap : PolynomialRing F n →ₐ[F] d.O.LocalOrdinary rho :=
  (d.O.localMap rho).comp d.O.ordinaryMk

@[simp] theorem localPolynomialMap_C (c : F) :
    d.localPolynomialMap rho (MvPolynomial.C c)=algebraMap F (d.O.LocalOrdinary rho) c := by
  simpa only [MvPolynomial.algebraMap_eq] using (d.localPolynomialMap rho).commutes c

@[simp] theorem localPolynomialMap_x (i : Fin n) :
    d.localPolynomialMap rho (MvPolynomial.X i)=d.O.localX rho i := rfl

@[simp] theorem localPolynomialMap_phi (i : Fin n) :
    d.localPolynomialMap rho (d.phiPolynomial i)=d.O.localNode rho i := by
  rw [phiPolynomial,←Polynomial.aeval_algHom_apply,localPolynomialMap_x]
  rfl

@[simp] theorem localPolynomialMap_a (i : Fin n) :
    d.localPolynomialMap rho (d.aPolynomial i)=d.localA rho i := by
  rw [aPolynomial,←Polynomial.aeval_algHom_apply,localPolynomialMap_x]
  rfl

@[simp] theorem localPolynomialMap_b (i : Fin n) :
    d.localPolynomialMap rho (d.bPolynomial i)=d.localB rho i := by
  rw [bPolynomial,←Polynomial.aeval_algHom_apply,localPolynomialMap_x]
  rfl

def localAmbientMap :
    SuperRing F n →ₐ[PolynomialRing F n] ClusterExterior (d.O.LocalOrdinary rho) (Fin n) :=
  ((d.localAmbientEquiv rho).toAlgHom.restrictScalars (PolynomialRing F n)).comp
    Algebra.TensorProduct.includeRight

@[simp] theorem localAmbientMap_theta (i : Fin n) :
    d.localAmbientMap rho (theta F n i)=clusterTheta i :=
  d.localAmbientEquiv_theta rho i

@[simp] theorem localAmbientMap_xi (i : Fin n) :
    d.localAmbientMap rho (xi F n i)=clusterXi i :=
  d.localAmbientEquiv_xi rho i

theorem localAmbientMap_smul (p : PolynomialRing F n) (a : SuperRing F n) :
    d.localAmbientMap rho (p • a)=
      d.localPolynomialMap rho p • d.localAmbientMap rho a := by
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul (d.O.LocalOrdinary rho) p (d.localAmbientMap rho a)).symm

theorem localAmbientMap_polynomial_scalar (p : PolynomialRing F n) :
    d.localAmbientMap rho
      ((Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n) p)=
      algebraMap (d.O.LocalOrdinary rho)
        (ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) (d.localPolynomialMap rho p) := by
  exact (d.localAmbientMap rho).commutes p

def localOddIdeal : TwoSidedIdeal (ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) :=
  separatedOddIdeal (d.O.localNode rho)
    (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
    (d.localA rho) (d.localB rho)

def localRelationImage (kind : MomentKind) (k : ℕ) :
    ClusterExterior (d.O.LocalOrdinary rho) (Fin n) :=
  match kind with
  | .polynomial => 0
  | .theta => separatedOddCurrent (d.O.localNode rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.localA rho) (d.localB rho) .theta k
  | .xi => separatedOddCurrent (d.O.localNode rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.localA rho) (d.localB rho) .xi k
  | .mixed => separatedOddCurrent (d.O.localNode rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.localA rho) (d.localB rho) .mixed k

theorem localAmbientMap_relation (kind : MomentKind) (k : ℕ) :
    d.localAmbientMap rho
      (moment d.phiPolynomial (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k)=
        d.localRelationImage rho kind k := by
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
    rw [hs,d.localAmbientMap_polynomial_scalar]
    have hm :
        d.localPolynomialMap rho
          (moment d.phiPolynomial
            (fun i ↦ MvPolynomial.C (d.beta i)*
              Polynomial.aeval (d.phiPolynomial i) d.G) k)=0 := by
      have hz : d.O.ordinaryMk
          (moment d.phiPolynomial
            (fun i ↦ MvPolynomial.C (d.beta i) *
              Polynomial.aeval (d.phiPolynomial i) d.G) k) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (ordinaryMoment_mem d.phiPolynomial d.beta d.G k)
      change d.O.localMap rho (d.O.ordinaryMk _) = 0
      rw [hz, map_zero]
    rw [hm,map_zero]
    rfl
  | theta =>
    simp only [moment,pairedCoefficients,map_sum,d.localAmbientMap_smul,map_pow,
      localPolynomialMap_phi,localPolynomialMap_b,localAmbientMap_theta,
      localRelationImage,separatedOddCurrent]
  | xi =>
    simp only [moment,pairedCoefficients,map_sum,d.localAmbientMap_smul,map_pow,
      localPolynomialMap_phi,map_mul,localPolynomialMap_a,localAmbientMap_xi,
      localPolynomialMap_C,localRelationImage,separatedOddCurrent]
  | mixed =>
    simp only [moment,pairedCoefficients,map_sum,d.localAmbientMap_smul,map_pow,
      localPolynomialMap_phi,map_mul,localAmbientMap_theta,localAmbientMap_xi,
      localRelationImage,separatedOddCurrent]

theorem localRelationImage_mem (kind : MomentKind) (k : ℕ) :
    d.localRelationImage rho kind k∈d.localOddIdeal rho := by
  cases kind with
  | polynomial => exact (d.localOddIdeal rho).zero_mem
  | theta => exact TwoSidedIdeal.subset_span ⟨(.theta,k),rfl⟩
  | xi => exact TwoSidedIdeal.subset_span ⟨(.xi,k),rfl⟩
  | mixed => exact TwoSidedIdeal.subset_span ⟨(.mixed,k),rfl⟩

theorem localAmbientMap_ideal (a : SuperRing F n) (ha : a∈d.superIdeal) :
    d.localAmbientMap rho a∈d.localOddIdeal rho := by
  have hle : d.superIdeal≤(d.localOddIdeal rho).comap (d.localAmbientMap rho).toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨kind,k⟩,rfl⟩
    change moment d.phiPolynomial
      (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k∈
        (d.localOddIdeal rho).comap (d.localAmbientMap rho).toRingHom
    rw [TwoSidedIdeal.mem_comap]
    change d.localAmbientMap rho
      (moment d.phiPolynomial (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k)
      ∈ d.localOddIdeal rho
    rw [d.localAmbientMap_relation]
    exact d.localRelationImage_mem rho kind k
  simpa only [TwoSidedIdeal.mem_comap, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using hle ha

def localTensorIdeal :=
  tensorTwoSidedIdeal (PolynomialRing F n) (d.O.LocalOrdinary rho) (SuperRing F n) d.superIdeal

theorem localAmbientEquiv_ideal (a : d.O.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n)
    (ha : a∈d.localTensorIdeal rho) :
    d.localAmbientEquiv rho a∈d.localOddIdeal rho := by
  letI : Ring (d.O.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n) :=
    Algebra.TensorProduct.instRing (R := PolynomialRing F n)
      (A := d.O.LocalOrdinary rho) (B := SuperRing F n)
  have hle : d.localTensorIdeal rho≤
      (d.localOddIdeal rho).comap (d.localAmbientEquiv rho).toRingEquiv.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨a,ha,rfl⟩
    change (Algebra.TensorProduct.includeRight : SuperRing F n →ₐ[PolynomialRing F n]
      d.O.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n) a ∈
      (d.localOddIdeal rho).comap (d.localAmbientEquiv rho).toRingEquiv.toRingHom
    rw [TwoSidedIdeal.mem_comap]
    exact d.localAmbientMap_ideal rho a ha
  have h := hle ha
  rw [TwoSidedIdeal.mem_comap] at h
  exact h

theorem localAmbientEquiv_symm_ideal
    (b : ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) (hb : b∈d.localOddIdeal rho) :
    (d.localAmbientEquiv rho).symm b∈d.localTensorIdeal rho := by
  letI : Ring (d.O.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n) :=
    Algebra.TensorProduct.instRing (R := PolynomialRing F n)
      (A := d.O.LocalOrdinary rho) (B := SuperRing F n)
  have hgen (kind : MomentKind) (k : ℕ) :
      (d.localAmbientEquiv rho).symm (d.localRelationImage rho kind k)
        ∈d.localTensorIdeal rho := by
    rw [←d.localAmbientMap_relation rho kind k]
    change (d.localAmbientEquiv rho).symm
      (d.localAmbientEquiv rho (1 ⊗ₜ[PolynomialRing F n]
        moment d.phiPolynomial (pairedCoefficients d.beta d.aPolynomial d.bPolynomial kind) k))∈_
    rw [AlgEquiv.symm_apply_apply]
    apply TwoSidedIdeal.subset_span
    refine ⟨_,TwoSidedIdeal.subset_span ⟨(kind,k),rfl⟩,rfl⟩
  have hle : d.localOddIdeal rho≤
      (d.localTensorIdeal rho).comap (d.localAmbientEquiv rho).symm.toRingEquiv.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro b ⟨⟨family,k⟩,rfl⟩
    change separatedOddCurrent (d.O.localNode rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.localA rho) (d.localB rho) family k ∈
      (d.localTensorIdeal rho).comap (d.localAmbientEquiv rho).symm.toRingEquiv.toRingHom
    rw [TwoSidedIdeal.mem_comap]
    cases family with
    | theta => exact hgen .theta k
    | xi => exact hgen .xi k
    | mixed => exact hgen .mixed k
  have h := hle hb
  rw [TwoSidedIdeal.mem_comap] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- The actual central local factor is exactly the separated odd exterior
quotient over the actual ordinary localization. -/
def localSuperEquivOddPresentation :
    d.LocalSuper rho ≃ₐ[d.O.LocalOrdinary rho]
      SeparatedOddQuotient (d.O.localNode rho)
        (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
        (d.localA rho) (d.localB rho) := by
  letI := polynomialAmbientTensorRing (F := F) (n := n) (d.O.LocalOrdinary rho)
  let e1 : d.LocalSuper rho ≃ₐ[d.O.LocalOrdinary rho]
      d.O.LocalOrdinary rho ⊗[PolynomialRing F n] d.SuperQuotient :=
    d.localSuperPolynomialBaseEquiv rho
  let e2 : (d.O.LocalOrdinary rho ⊗[PolynomialRing F n] d.SuperQuotient) ≃ₐ[d.O.LocalOrdinary rho]
      (d.localTensorIdeal rho).ringCon.Quotient :=
    tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) (A := SuperRing F n) d.superIdeal
  let e3 : (d.localTensorIdeal rho).ringCon.Quotient ≃ₐ[d.O.LocalOrdinary rho]
      (d.localOddIdeal rho).ringCon.Quotient :=
    twoSidedQuotientEquiv (R := d.O.LocalOrdinary rho)
      (A := d.O.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n)
      (B := ClusterExterior (d.O.LocalOrdinary rho) (Fin n))
      (d.localAmbientEquiv rho) (d.localTensorIdeal rho) (d.localOddIdeal rho)
      (fun a ha ↦ d.localAmbientEquiv_ideal rho a ha)
      (fun b hb ↦ d.localAmbientEquiv_symm_ideal rho b hb)
  exact e1.trans (e2.trans e3)

/-- The first complete local-super endpoint: all four original families
are converted into the homogeneous cluster presentation over the source
local coefficient ring. -/
def localSuperEquivNormalizedPresentation :
    d.LocalSuper rho ≃ₐ[d.O.LocalOrdinary rho]
      ClusterOddQuotient (d.O.pointCluster rho) (d.O.localZ rho)
        (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
        (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho) :=
  (d.localSuperEquivOddPresentation rho).trans (d.localOddNormalizationEquiv rho)

end SeparatedPairedData
end PaperVerification.Fermion

