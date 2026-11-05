module

public import PaperVerification.FermionIndependentClusterTensor
public import PaperVerification.FermionClusterReindex
public import PaperVerification.FermionLocalSupport

/-!
# Assembly of the actual local signed tensor decomposition

The clusters are exactly the fibers of the original support-point node map.
All multiplicities and weights are inherited from those original indices.
The resulting tensor factors have the literal homogeneous single-cluster
presentations. The original paired-presentation and full bidegree bridges
remain separately visible audit obligations.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.Fermion
namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)

local instance FermionLocalTensorAssembly_sourceOddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _

def localClusterLabels :
    d.O.PointCluster rho ≃ Fin (Fintype.card (d.O.PointCluster rho)) :=
  Fintype.equivFin _

def localClusterFamily : ClusterFamilyData F (Fintype.card (d.O.PointCluster rho)) where
  Index c := {i : Fin n // d.O.pointCluster rho i=(d.localClusterLabels rho).symm c}
  finite _ := inferInstance
  beta c i := d.beta i.1
  r c i := d.O.ramificationOrder rho i.1
  s c := d.O.clusterMultiplicity rho ((d.localClusterLabels rho).symm c)
  u c i := d.thetaOrder rho i.1
  v c i := d.xiOrder rho i.1

def localClusterForget :
    (Σ c,(d.localClusterFamily rho).Index c) → Fin n := fun i ↦ i.2.1

theorem localClusterForget_bijective : Function.Bijective (d.localClusterForget rho) := by
  constructor
  · rintro ⟨c,⟨i,hi⟩⟩ ⟨c',⟨j,hj⟩⟩ h
    change i=j at h
    subst j
    have hc : c=c' := (d.localClusterLabels rho).symm.injective (hi.symm.trans hj)
    subst c'
    rfl
  · intro i
    refine ⟨⟨d.localClusterLabels rho (d.O.pointCluster rho i),⟨i,?_⟩⟩,rfl⟩
    exact ((d.localClusterLabels rho).symm_apply_apply _).symm

def localClusterIndexEquiv :
    Fin n ≃ (Σ c,(d.localClusterFamily rho).Index c) :=
  (Equiv.ofBijective (d.localClusterForget rho) (d.localClusterForget_bijective rho)).symm

@[simp] theorem localClusterIndexEquiv_value (i : Fin n) :
    (d.localClusterIndexEquiv rho i).2.1=i :=
  (Equiv.ofBijective (d.localClusterForget rho) (d.localClusterForget_bijective rho)).apply_symm_apply i

theorem localClusterIndexEquiv_label (i : Fin n) :
    (d.localClusterIndexEquiv rho i).1=d.localClusterLabels rho (d.O.pointCluster rho i) := by
  have h := (d.localClusterIndexEquiv rho i).2.property
  rw [d.localClusterIndexEquiv_value rho i] at h
  have he := congrArg (d.localClusterLabels rho) h
  simpa only [Equiv.apply_symm_apply] using he.symm

local instance FermionLocalTensorAssembly_targetOddOrder :
    LinearOrder (((Σ c,(d.localClusterFamily rho).Index c))⊕
      ((Σ c,(d.localClusterFamily rho).Index c))) := finiteIndexLinearOrder _

def localClusterParameterEquiv :
    ClusterParameterEquiv d.beta (d.O.pointCluster rho)
      (d.O.ramificationOrder rho) (d.O.clusterMultiplicity rho)
      (d.thetaOrder rho) (d.xiOrder rho)
      (d.localClusterFamily rho).wholeBeta Sigma.fst
      (d.localClusterFamily rho).wholeR (d.localClusterFamily rho).s
      (d.localClusterFamily rho).wholeU (d.localClusterFamily rho).wholeV where
  index := d.localClusterIndexEquiv rho
  label := d.localClusterLabels rho
  beta_eq i := by
    change d.beta (d.localClusterIndexEquiv rho i).2.1=d.beta i
    rw [d.localClusterIndexEquiv_value]
  cluster_eq i := d.localClusterIndexEquiv_label rho i
  r_eq i := by
    change d.O.ramificationOrder rho (d.localClusterIndexEquiv rho i).2.1=d.O.ramificationOrder rho i
    rw [d.localClusterIndexEquiv_value]
  s_eq c := by
    change d.O.clusterMultiplicity rho
      ((d.localClusterLabels rho).symm (d.localClusterLabels rho c))=d.O.clusterMultiplicity rho c
    rw [Equiv.symm_apply_apply]
  u_eq i := by
    change d.thetaOrder rho (d.localClusterIndexEquiv rho i).2.1=d.thetaOrder rho i
    rw [d.localClusterIndexEquiv_value]
  v_eq i := by
    change d.xiOrder rho (d.localClusterIndexEquiv rho i).2.1=d.xiOrder rho i
    rw [d.localClusterIndexEquiv_value]

/-- The actual local central factor is the genuine signed tensor product of
the literal homogeneous single-cluster presentations, with exactly the
root and ramification multiplicities of the original separated data. -/
def localSuperTensorEquiv :
    d.LocalSuper rho ≃ₐ[F] (d.localClusterFamily rho).tensor.Carrier :=
  (d.localSuperEquivHomogeneousCluster rho).trans
    ((d.localClusterParameterEquiv rho).algEquiv.trans
      (d.localClusterFamily rho).independentClusterTensorEquiv)

/-- Product over exactly the actual support points, retaining all nilpotents. -/
def globalSuperTensorProductEquiv :
    d.SuperQuotient ≃ₐ[F]
      ∀ rho : d.O.SupportPoint,(d.localClusterFamily rho).tensor.Carrier :=
  d.superProductOverSupport.trans
    (AlgEquiv.piCongrRight fun rho ↦ d.localSuperTensorEquiv rho)

end SeparatedPairedData
end PaperVerification.Fermion

