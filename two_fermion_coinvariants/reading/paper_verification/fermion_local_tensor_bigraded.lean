module

public import PaperVerification.FermionLocalBigraded
public import PaperVerification.FermionIndependentClusterBigraded
public import PaperVerification.FermionLocalTensorAssembly

/-!
# The original local quotient and its exterior-bigraded tensor factorization

The source pieces are images of the original theta/xi exterior word spans
under the actual localized quotient map. Their definition uses only ambient
scalar base change and quotienting; it does not use formal coordinates,
normalization, the homogeneous cluster isomorphism, or the tensor result.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.Fermion
namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)

local instance FermionLocalTensorBigraded_oddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _
local instance FermionLocalTensorBigraded_wholeOddOrder : LinearOrder
    (((Σ c,(d.localClusterFamily rho).Index c))⊕((Σ c,(d.localClusterFamily rho).Index c))) :=
  finiteIndexLinearOrder _

def localSuperExteriorLift :
    ClusterExterior (d.O.LocalOrdinary rho) (Fin n) →ₐ[d.O.LocalOrdinary rho]
      d.LocalSuper rho :=
  (d.localSuperPolynomialBaseEquiv rho).symm.toAlgHom.comp
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) d.superIdeal).symm.toAlgHom.comp
      (((d.localTensorIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho)).comp
        (d.localAmbientEquiv rho).symm.toAlgHom))

theorem localSuperExteriorLift_theta (i : Fin n) :
    d.localSuperExteriorLift rho (clusterTheta i)=
      (1 : d.O.LocalOrdinary rho) ⊗ₜ[d.O.Ordinary] d.superMk (theta F n i) := by
  have ha : (d.localAmbientEquiv rho).symm (clusterTheta i)=
      (1 : d.O.LocalOrdinary rho) ⊗ₜ[PolynomialRing F n] theta F n i := by
    apply (d.localAmbientEquiv rho).injective
    rw [AlgEquiv.apply_symm_apply,d.localAmbientEquiv_theta]
  have hq :
      (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
        (S := d.O.LocalOrdinary rho) d.superIdeal).symm
        ((d.localTensorIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho)
          ((1 : d.O.LocalOrdinary rho) ⊗ₜ[PolynomialRing F n] theta F n i))=
        (1 : d.O.LocalOrdinary rho) ⊗ₜ[PolynomialRing F n] d.superMk (theta F n i) := by
    apply (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) d.superIdeal).injective
    rw [AlgEquiv.apply_symm_apply]
    convert (tensorTwoSidedQuotientEquiv_tmul_mk (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) (A := SuperRing F n)
      d.superIdeal 1 (theta F n i)).symm using 1 <;> rfl
  change (d.localSuperPolynomialBaseEquiv rho).symm
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) d.superIdeal).symm
      ((d.localTensorIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho)
        ((d.localAmbientEquiv rho).symm (clusterTheta i))))=_
  rw [ha,hq]
  apply (d.localSuperPolynomialBaseEquiv rho).injective
  rw [AlgEquiv.apply_symm_apply,d.localSuperPolynomialBaseEquiv_tmul]

theorem localSuperExteriorLift_xi (i : Fin n) :
    d.localSuperExteriorLift rho (clusterXi i)=
      (1 : d.O.LocalOrdinary rho) ⊗ₜ[d.O.Ordinary] d.superMk (xi F n i) := by
  have ha : (d.localAmbientEquiv rho).symm (clusterXi i)=
      (1 : d.O.LocalOrdinary rho) ⊗ₜ[PolynomialRing F n] xi F n i := by
    apply (d.localAmbientEquiv rho).injective
    rw [AlgEquiv.apply_symm_apply,d.localAmbientEquiv_xi]
  have hq :
      (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
        (S := d.O.LocalOrdinary rho) d.superIdeal).symm
        ((d.localTensorIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho)
          ((1 : d.O.LocalOrdinary rho) ⊗ₜ[PolynomialRing F n] xi F n i))=
        (1 : d.O.LocalOrdinary rho) ⊗ₜ[PolynomialRing F n] d.superMk (xi F n i) := by
    apply (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) d.superIdeal).injective
    rw [AlgEquiv.apply_symm_apply]
    convert (tensorTwoSidedQuotientEquiv_tmul_mk (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) (A := SuperRing F n)
      d.superIdeal 1 (xi F n i)).symm using 1 <;> rfl
  change (d.localSuperPolynomialBaseEquiv rho).symm
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) d.superIdeal).symm
      ((d.localTensorIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho)
        ((d.localAmbientEquiv rho).symm (clusterXi i))))=_
  rw [ha,hq]
  apply (d.localSuperPolynomialBaseEquiv rho).injective
  rw [AlgEquiv.apply_symm_apply,d.localSuperPolynomialBaseEquiv_tmul]

def localSuperBigradedPart (g : ℕ×ℕ) : Submodule (d.O.LocalOrdinary rho) (d.LocalSuper rho) :=
  (exteriorBigradedPart g).map (d.localSuperExteriorLift rho).toLinearMap

set_option maxHeartbeats 1000000 in
theorem localSuperOddPresentation_lift
    (x : ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) :
    d.localSuperEquivOddPresentation rho (d.localSuperExteriorLift rho x)=
      (d.localOddIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho) x := by
  letI := polynomialAmbientTensorRing (F := F) (n := n) (d.O.LocalOrdinary rho)
  let E1 := d.localSuperPolynomialBaseEquiv rho
  let E := tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
    (S := d.O.LocalOrdinary rho) (A := SuperRing F n) d.superIdeal
  let a := d.localAmbientEquiv rho
  let q := (d.localTensorIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho)
  let f := twoSidedQuotientEquiv (R := d.O.LocalOrdinary rho)
    (A := d.O.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n)
    (B := ClusterExterior (d.O.LocalOrdinary rho) (Fin n))
    a (d.localTensorIdeal rho) (d.localOddIdeal rho) (d.localAmbientEquiv_ideal rho) (d.localAmbientEquiv_symm_ideal rho)
  change f (E (E1 (E1.symm (E.symm (q (a.symm x))))))=_
  rw [AlgEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply]
  change (d.localOddIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho) (a (a.symm x)) =
    (d.localOddIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho) x
  exact congrArg ((d.localOddIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho))
    (a.apply_symm_apply x)

theorem localSuperExteriorLift_eq_zero_iff
    (x : ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) :
    d.localSuperExteriorLift rho x=0 ↔ x∈d.localOddIdeal rho := by
  have hq :
      (d.localOddIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho) x=0 ↔
        x∈d.localOddIdeal rho := by
    constructor
    · intro hx
      change ((x : ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) :
        (d.localOddIdeal rho).ringCon.Quotient)=
        ((0 : ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) :
          (d.localOddIdeal rho).ringCon.Quotient) at hx
      exact Quotient.exact hx
    · exact quotientMk_eq_zero_of_mem (R := d.O.LocalOrdinary rho) (d.localOddIdeal rho) x
  rw [←d.localSuperOddPresentation_lift rho x] at hq
  exact ((d.localSuperEquivOddPresentation rho).map_eq_zero_iff).symm.trans hq

theorem localSuperExteriorLift_surjective :
    Function.Surjective (d.localSuperExteriorLift rho) := by
  intro x
  obtain ⟨y,hy⟩ := (d.localOddIdeal rho).ringCon.mk'_surjective
    (d.localSuperEquivOddPresentation rho x)
  refine ⟨y,(d.localSuperEquivOddPresentation rho).injective ?_⟩
  rw [d.localSuperOddPresentation_lift]
  exact hy

set_option maxHeartbeats 1000000 in
/-- Directness and multiplication of the literal localized image pieces
are proved from the homogeneous actual relation ideal. -/
def localSuperBigrading :
    GradedAlgebra (R := d.O.LocalOrdinary rho) (A := d.LocalSuper rho)
      (d.localSuperBigradedPart rho) := by
  letI := exteriorWeightedGrading (A := d.O.LocalOrdinary rho) (oddBidegree (ι := Fin n))
  exact gradedImageAlgebra (R := d.O.LocalOrdinary rho)
    (A := ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) (B := d.LocalSuper rho)
    (Γ := ℕ×ℕ) (exteriorBigradedPart (A := d.O.LocalOrdinary rho) (ι := Fin n))
    (d.localSuperExteriorLift rho)
    (d.localSuperExteriorLift_surjective rho) (by
      intro g a ha
      apply (d.localSuperExteriorLift_eq_zero_iff rho _).mpr
      exact twoSided_span_multihomogeneous exteriorBigradedPart
        (Set.range fun p : LocalOddFamily×ℕ ↦
          separatedOddCurrent (d.O.localNode rho)
            (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
            (d.localA rho) (d.localB rho) p.1 p.2)
        (by
          rintro z ⟨⟨family,k⟩,rfl⟩
          exact ⟨oddFamilyBidegree family,separatedOddCurrent_bidegree _ _ _ _ family k⟩)
        a ((d.localSuperExteriorLift_eq_zero_iff rho a).mp ha) g)

theorem localSuperOddPresentation_bigraded_iff (g : ℕ×ℕ) (x : d.LocalSuper rho) :
    d.localSuperEquivOddPresentation rho x∈
      separatedOddBigradedPart (d.O.localNode rho)
        (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
        (d.localA rho) (d.localB rho) g ↔
      x∈d.localSuperBigradedPart rho g := by
  constructor
  · rintro ⟨y,hy,hey⟩
    refine ⟨y,hy,?_⟩
    apply (d.localSuperEquivOddPresentation rho).injective
    rw [AlgHom.toLinearMap_apply,d.localSuperOddPresentation_lift]
    simpa only [localOddIdeal,AlgHom.toLinearMap_apply,RingCon.mkₐ_apply] using hey
  · rintro ⟨y,hy,rfl⟩
    refine ⟨y,hy,?_⟩
    simpa only [localOddIdeal,AlgHom.toLinearMap_apply,RingCon.mkₐ_apply] using
      (d.localSuperOddPresentation_lift rho y).symm

set_option maxHeartbeats 1000000 in
theorem localOddNormalization_bigraded_iff (g : ℕ×ℕ)
    (x : SeparatedOddQuotient (d.O.localNode rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.localA rho) (d.localB rho)) :
    d.localOddNormalizationEquiv rho x∈
      clusterOddBigradedPart (d.O.pointCluster rho) (d.O.localZ rho)
        (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
        (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho) g ↔
      x∈separatedOddBigradedPart (d.O.localNode rho)
        (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
        (d.localA rho) (d.localB rho) g := by
  let e := d.localOddNormalizationEquiv rho
  let u := pairedOddUnitEquiv (A := d.O.LocalOrdinary rho) (ι := Fin n)
    (d.localUnitA rho) (d.localUnitB rho)
  have he (y : ClusterExterior (d.O.LocalOrdinary rho) (Fin n)) :
      e ((separatedOddIdeal (d.O.localNode rho)
        (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
        (d.localA rho) (d.localB rho)).ringCon.mkₐ (d.O.LocalOrdinary rho) y)=
      (clusterOddIdeal (d.O.pointCluster rho) (d.O.localZ rho)
        (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
        (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho)).ringCon.mkₐ
          (d.O.LocalOrdinary rho) (u.symm y) := by
    rfl
  constructor
  · rintro ⟨y,hy,hey⟩
    have hmem := exteriorDiagonalUnitEquiv_weighted_mem
      (A := d.O.LocalOrdinary rho) (ι := Fin n⊕Fin n) (Γ := ℕ×ℕ)
      (oddBidegree (ι := Fin n)) (Sum.elim (d.localUnitB rho) (d.localUnitA rho))
      (d := g) (x := y) hy
    refine ⟨u y,hmem,?_⟩
    apply e.injective
    change e ((separatedOddIdeal (d.O.localNode rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.localA rho) (d.localB rho)).ringCon.mkₐ (d.O.LocalOrdinary rho) (u y))=e x
    rw [he,AlgEquiv.symm_apply_apply]
    exact hey
  · rintro ⟨y,hy,rfl⟩
    have hmem := exteriorDiagonalUnitEquiv_symm_weighted_mem
      (A := d.O.LocalOrdinary rho) (ι := Fin n⊕Fin n) (Γ := ℕ×ℕ)
      (oddBidegree (ι := Fin n)) (Sum.elim (d.localUnitB rho) (d.localUnitA rho))
      (d := g) (x := y) hy
    refine ⟨u.symm y,hmem,?_⟩
    exact (he y).symm

theorem localSuperEquivHomogeneousCluster_bigraded_iff (g : ℕ×ℕ) (x : d.LocalSuper rho) :
    d.localSuperEquivHomogeneousCluster rho x∈
      homogeneousClusterBigradedPart d.beta (d.O.pointCluster rho)
        (d.O.ramificationOrder rho) (d.O.clusterMultiplicity rho)
        (d.thetaOrder rho) (d.xiOrder rho) g ↔
      x∈d.localSuperBigradedPart rho g := by
  change d.localSuperEquivHomogeneousCluster rho x∈
    clusterOddBigradedPart (d.O.pointCluster rho) (d.O.homogeneousZ rho)
      (fun i ↦ algebraMap F (d.O.HomogeneousOrdinary rho) (d.beta i))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho) g ↔
    x∈d.localSuperBigradedPart rho g
  have hc := clusterOddCoefficientEquiv_bigraded_iff
    (d.O.localOrdinaryEquivHomogeneous rho) (d.O.pointCluster rho) (d.O.localZ rho)
    (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
    (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho) g
    (d.localSuperEquivNormalizedPresentation rho x)
  have hi := twoSidedQuotientEquivOfEq_image_iff (F := F)
    (S := d.O.HomogeneousOrdinary rho)
    (A := ClusterExterior (d.O.HomogeneousOrdinary rho) (Fin n)) (Γ := ℕ×ℕ)
    (exteriorBigradedPart (A := d.O.HomogeneousOrdinary rho) (ι := Fin n))
    (d.localClusterCoefficientIdeal_eq rho) g
    (clusterOddCoefficientEquiv (d.O.localOrdinaryEquivHomogeneous rho)
      (d.O.pointCluster rho) (d.O.localZ rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho)
      (d.localSuperEquivNormalizedPresentation rho x))
  have hn := d.localOddNormalization_bigraded_iff rho g
    (d.localSuperEquivOddPresentation rho x)
  have hp := d.localSuperOddPresentation_bigraded_iff rho g x
  simpa only [localSuperEquivHomogeneousCluster,localHomogeneousCoefficientEquiv,
    localSuperEquivNormalizedPresentation,AlgEquiv.trans_apply,AlgEquiv.restrictScalars_apply,
    homogeneousClusterBigradedPart,restrictGradedPart,clusterOddBigradedPart,
    Submodule.restrictScalars_mem] using hi.trans (hc.trans (hn.trans hp))

/-- The actual local algebra isomorphism preserves every separate theta/xi
degree, with the target's independent natural signed tensor bigrading. -/
theorem localSuperTensorEquiv_bigraded_iff (g : ℕ×ℕ) (x : d.LocalSuper rho) :
    d.localSuperTensorEquiv rho x∈(d.localClusterFamily rho).tensorBigrading.part g ↔
      x∈d.localSuperBigradedPart rho g := by
  let y : (d.localClusterFamily rho).whole.Carrier :=
    (d.localClusterParameterEquiv rho).algEquiv ((d.localSuperEquivHomogeneousCluster rho) x)
  have ht := (d.localClusterFamily rho).independentClusterTensorEquiv_bigraded_iff g y
  have hr := (d.localClusterParameterEquiv rho).algEquiv_bigraded_iff g
    ((d.localSuperEquivHomogeneousCluster rho) x)
  have hl := d.localSuperEquivHomogeneousCluster_bigraded_iff rho g x
  change (d.localClusterFamily rho).independentClusterTensorEquiv y∈
    (d.localClusterFamily rho).tensorBigrading.part g ↔ x∈d.localSuperBigradedPart rho g
  exact ht.trans (hr.trans hl)

end SeparatedPairedData
end PaperVerification.Fermion

