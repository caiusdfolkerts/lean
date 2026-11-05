module

public import PaperVerification.FermionLocalSuperPresentation

/-!
# Transport of the coefficient ring in an exterior presentation

Exterior scalar transport is constructed through the proven finite exterior
base-change equivalences. The canonical odd generators remain fixed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct Classical BigOperators

namespace PaperVerification.Fermion

section Coefficients
variable {F A B ι : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]

def finiteExteriorCoefficientEquiv (e : A ≃ₐ[F] B) :
    ExteriorAlgebra A (ι → A) ≃ₐ[F] ExteriorAlgebra B (ι → B) :=
  ((finiteExteriorBaseChange F A ι).symm.restrictScalars F).trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl : ExteriorAlgebra F (ι → F) ≃ₐ[F] ExteriorAlgebra F (ι → F))).trans
      ((finiteExteriorBaseChange F B ι).restrictScalars F))

@[simp] theorem finiteExteriorCoefficientEquiv_generator (e : A ≃ₐ[F] B) (i : ι) :
    finiteExteriorCoefficientEquiv (ι := ι) e (exteriorGenerator (A := A) i)=
      exteriorGenerator (A := B) i := by
  have hA : (finiteExteriorBaseChange F A ι).symm (exteriorGenerator (A := A) i)=
      1 ⊗ₜ[F] exteriorGenerator (A := F) i := by
    apply (finiteExteriorBaseChange F A ι).injective
    simp only [AlgEquiv.apply_symm_apply,finiteExteriorBaseChange_generator,one_smul]
  rw [finiteExteriorCoefficientEquiv,AlgEquiv.trans_apply,AlgEquiv.restrictScalars_apply,hA,
    AlgEquiv.trans_apply,Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
  simp only [map_one,AlgEquiv.coe_toAlgHom,AlgEquiv.coe_refl,id_eq,AlgEquiv.restrictScalars_apply,
    finiteExteriorBaseChange_generator,one_smul]

@[simp] theorem finiteExteriorCoefficientEquiv_algebraMap (e : A ≃ₐ[F] B) (a : A) :
    finiteExteriorCoefficientEquiv (ι := ι) e
      (algebraMap A (ExteriorAlgebra A (ι → A)) a)=
      algebraMap B (ExteriorAlgebra B (ι → B)) (e a) := by
  have hA : (finiteExteriorBaseChange F A ι).symm
      (algebraMap A (ExteriorAlgebra A (ι → A)) a)=
      a ⊗ₜ[F] (1 : ExteriorAlgebra F (ι → F)) := by
    simpa only [Algebra.TensorProduct.algebraMap_apply,Algebra.algebraMap_self,
      RingHom.id_apply] using
      (finiteExteriorBaseChange F A ι).symm.commutes a
  rw [finiteExteriorCoefficientEquiv,AlgEquiv.trans_apply,AlgEquiv.restrictScalars_apply,hA,
    AlgEquiv.trans_apply,Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
  simpa only [map_one,AlgEquiv.coe_toAlgHom,AlgEquiv.coe_refl,id_eq,AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.algebraMap_apply,Algebra.algebraMap_self,RingHom.id_apply] using (finiteExteriorBaseChange F B ι).commutes (e a)

theorem finiteExteriorCoefficientEquiv_smul (e : A ≃ₐ[F] B)
    (a : A) (x : ExteriorAlgebra A (ι → A)) :
    finiteExteriorCoefficientEquiv (ι := ι) e (a • x)=
      e a • finiteExteriorCoefficientEquiv (ι := ι) e x := by
  rw [Algebra.smul_def,map_mul,finiteExteriorCoefficientEquiv_algebraMap,Algebra.smul_def]

theorem finiteExteriorCoefficientEquiv_symm (e : A ≃ₐ[F] B) :
    (finiteExteriorCoefficientEquiv (ι := ι) e).symm=
      finiteExteriorCoefficientEquiv (ι := ι) e.symm := by
  ext x
  rfl

end Coefficients

section Cluster
variable {F A B ι κ : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι] [Fintype κ]

theorem clusterOddCurrent_coefficient_map (e : A ≃ₐ[F] B)
    (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ)
    (family : LocalOddFamily) (c : κ) (k : ℕ) :
    finiteExteriorCoefficientEquiv e (clusterOddCurrent cluster z beta r u v family c k)=
      clusterOddCurrent cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i))
        r u v family c k := by
  cases family <;>
    simp only [clusterOddCurrent,map_sum,finiteExteriorCoefficientEquiv_smul,
      map_pow,map_mul,clusterTheta,clusterXi,
      finiteExteriorCoefficientEquiv_generator]

theorem clusterOddIdeal_coefficient_map (e : A ≃ₐ[F] B)
    (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ)
    (x : ClusterExterior A ι) (hx : x∈clusterOddIdeal cluster z beta r u v) :
    finiteExteriorCoefficientEquiv e x∈
      clusterOddIdeal cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v := by
  have hle : clusterOddIdeal cluster z beta r u v≤
      (clusterOddIdeal cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v).comap
        (finiteExteriorCoefficientEquiv e).toRingEquiv.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨c,family,k⟩,rfl⟩
    change clusterOddCurrent cluster z beta r u v family c k∈
      (clusterOddIdeal cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v).comap
        (finiteExteriorCoefficientEquiv e).toRingEquiv.toRingHom
    rw [TwoSidedIdeal.mem_comap]
    change finiteExteriorCoefficientEquiv e
      (clusterOddCurrent cluster z beta r u v family c k)∈
        clusterOddIdeal cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v
    rw [clusterOddCurrent_coefficient_map]
    exact TwoSidedIdeal.subset_span ⟨(c,family,k),rfl⟩
  simpa only [TwoSidedIdeal.mem_comap,RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom,AlgEquiv.coe_toRingEquiv] using hle hx

def clusterOddCoefficientEquiv (e : A ≃ₐ[F] B)
    (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    ClusterOddQuotient cluster z beta r u v ≃ₐ[F]
      ClusterOddQuotient cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v :=
  twoSidedQuotientEquiv (finiteExteriorCoefficientEquiv e)
    (clusterOddIdeal cluster z beta r u v)
    (clusterOddIdeal cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v)
    (clusterOddIdeal_coefficient_map e cluster z beta r u v)
    (by
      intro b hb
      rw [finiteExteriorCoefficientEquiv_symm]
      simpa only [AlgEquiv.symm_apply_apply] using
        clusterOddIdeal_coefficient_map e.symm cluster (fun i ↦ e (z i))
          (fun i ↦ e (beta i)) r u v b hb)

end Cluster

namespace SeparatedPairedData
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)

abbrev HomogeneousClusterQuotient :=
  ClusterOddQuotient (d.O.pointCluster rho) (d.O.homogeneousZ rho)
    (fun i ↦ algebraMap F (d.O.HomogeneousOrdinary rho) (d.beta i))
    (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho)

/-- The transported coefficients give exactly the independently defined
homogeneous relation ideal in the fixed target exterior algebra. -/
theorem localClusterCoefficientIdeal_eq :
    clusterOddIdeal (d.O.pointCluster rho)
      (fun i ↦ d.O.localOrdinaryEquivHomogeneous rho (d.O.localZ rho i))
      (fun i ↦ d.O.localOrdinaryEquivHomogeneous rho
        (algebraMap F (d.O.LocalOrdinary rho) (d.beta i)))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho)=
    clusterOddIdeal (d.O.pointCluster rho) (d.O.homogeneousZ rho)
      (fun i ↦ algebraMap F (d.O.HomogeneousOrdinary rho) (d.beta i))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho) := by
  have hz : (fun i ↦ d.O.localOrdinaryEquivHomogeneous rho (d.O.localZ rho i))=
      d.O.homogeneousZ rho := by
    funext i
    exact d.O.localOrdinaryEquivHomogeneous_z rho i
  have hbeta : (fun i ↦ d.O.localOrdinaryEquivHomogeneous rho
      (algebraMap F (d.O.LocalOrdinary rho) (d.beta i)))=
      (fun i ↦ algebraMap F (d.O.HomogeneousOrdinary rho) (d.beta i)) := by
    funext i
    exact (d.O.localOrdinaryEquivHomogeneous rho).commutes (d.beta i)
  rw [hz,hbeta]

set_option maxHeartbeats 1000000 in
/-- Actual coefficient transport, followed only by the identity between
quotients by proved-equal ideals in the same ambient exterior algebra. -/
def localHomogeneousCoefficientEquiv :
    ClusterOddQuotient (d.O.pointCluster rho) (d.O.localZ rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho) ≃ₐ[F]
        d.HomogeneousClusterQuotient rho := by
  let A := d.O.LocalOrdinary rho
  let B := d.O.HomogeneousOrdinary rho
  let e : A ≃ₐ[F] B := d.O.localOrdinaryEquivHomogeneous rho
  let betaA : Fin n → A := fun i ↦ algebraMap F A (d.beta i)
  let I : TwoSidedIdeal (ClusterExterior B (Fin n)) :=
    clusterOddIdeal (d.O.pointCluster rho)
      (fun i ↦ e (d.O.localZ rho i)) (fun i ↦ e (betaA i))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho)
  let J : TwoSidedIdeal (ClusterExterior B (Fin n)) :=
    clusterOddIdeal (d.O.pointCluster rho) (d.O.homogeneousZ rho)
      (fun i ↦ algebraMap F B (d.beta i))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho)
  have hIJ : I=J := d.localClusterCoefficientIdeal_eq rho
  let e₁ :=
    clusterOddCoefficientEquiv (F := F) (A := A) (B := B) (ι := Fin n)
      (κ := d.O.PointCluster rho) e (d.O.pointCluster rho) (d.O.localZ rho) betaA
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho)
  let e₂ :=
    twoSidedQuotientEquivOfEq (R := F) (A := ClusterExterior B (Fin n))
      (I := I) (J := J) hIJ
  let transported := e₁.trans e₂
  exact transported

/-- The literal local factor of the original paper quotient is isomorphic
to the literal homogeneous independent-cluster presentation. -/
def localSuperEquivHomogeneousCluster :
    d.LocalSuper rho ≃ₐ[F] d.HomogeneousClusterQuotient rho :=
  ((d.localSuperEquivNormalizedPresentation rho).restrictScalars F).trans
    (d.localHomogeneousCoefficientEquiv rho)

end SeparatedPairedData
end PaperVerification.Fermion

