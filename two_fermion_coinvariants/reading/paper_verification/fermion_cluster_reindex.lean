module

public import PaperVerification.FermionClusterLiftGraded

/-!
# Faithful reindexing of homogeneous cluster presentations

Every parameter and every cluster fiber is transported by an explicit
equivalence. The induced quotient maps are inverse on polynomial and odd
generators. This is the bridge from actual support clusters to a finite
ordered family.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

variable {F ι κ ι' κ' : Type*} [Field F] [CharZero F]
  [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  [LinearOrder (ι⊕ι)] [LinearOrder (ι'⊕ι')]

structure ClusterParameterEquiv
    (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ)
    (beta' : ι' → F) (cluster' : ι' → κ') (r' : ι' → ℕ) (s' : κ' → ℕ) (u' v' : ι' → ℕ) where
  index : ι ≃ ι'
  label : κ ≃ κ'
  beta_eq : ∀ i,beta' (index i)=beta i
  cluster_eq : ∀ i,cluster' (index i)=label (cluster i)
  r_eq : ∀ i,r' (index i)=r i
  s_eq : ∀ c,s' (label c)=s c
  u_eq : ∀ i,u' (index i)=u i
  v_eq : ∀ i,v' (index i)=v i

namespace ClusterParameterEquiv

variable {beta : ι → F} {cluster : ι → κ} {r : ι → ℕ} {s : κ → ℕ} {u v : ι → ℕ}
  {beta' : ι' → F} {cluster' : ι' → κ'} {r' : ι' → ℕ} {s' : κ' → ℕ} {u' v' : ι' → ℕ}
  (e : ClusterParameterEquiv beta cluster r s u v beta' cluster' r' s' u' v')

def symm : ClusterParameterEquiv beta' cluster' r' s' u' v' beta cluster r s u v where
  index := e.index.symm
  label := e.label.symm
  beta_eq j := by simpa only [Equiv.apply_symm_apply] using (e.beta_eq (e.index.symm j)).symm
  cluster_eq j := by
    apply e.label.injective
    simpa only [Equiv.apply_symm_apply] using (e.cluster_eq (e.index.symm j)).symm
  r_eq j := by simpa only [Equiv.apply_symm_apply] using (e.r_eq (e.index.symm j)).symm
  s_eq c := by simpa only [Equiv.apply_symm_apply] using (e.s_eq (e.label.symm c)).symm
  u_eq j := by simpa only [Equiv.apply_symm_apply] using (e.u_eq (e.index.symm j)).symm
  v_eq j := by simpa only [Equiv.apply_symm_apply] using (e.v_eq (e.index.symm j)).symm

def fiberEquiv (c : κ) :
    {i : ι // cluster i=c} ≃ {j : ι' // cluster' j=e.label c} :=
  e.index.subtypeEquiv (by intro i; rw [e.cluster_eq]; exact e.label.apply_eq_iff_eq.symm)

theorem sum_fiber_transport {C : Type*} [AddCommMonoid C] (f : ι' → C) (c : κ) :
    (∑ i : {i : ι // cluster i=c},f (e.index i.1))=
      ∑ j : {j : ι' // cluster' j=e.label c},f j.1 :=
  (e.fiberEquiv c).sum_comp (fun j ↦ f j.1)

def targetRepresentation :
    letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
    ClusterRepresentation (homogeneousClusterPart beta' cluster' r' s' u' v')
      beta cluster r s u v := by
  letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
  let rep := homogeneousClusterRepresentation beta' cluster' r' s' u' v'
  refine {
    z := fun i ↦ rep.z (e.index i)
    theta := fun i ↦ rep.theta (e.index i)
    xi := fun i ↦ rep.xi (e.index i)
    z_degree := fun i ↦ rep.z_degree (e.index i)
    theta_degree := fun i ↦ rep.theta_degree (e.index i)
    xi_degree := fun i ↦ rep.xi_degree (e.index i)
    ordinary := ?_
    theta_moment := ?_
    xi_moment := ?_
    mixed_moment := ?_ }
  · intro c k
    have h := rep.ordinary (e.label c) k
    rw [←e.sum_fiber_transport
      (fun j ↦ algebraMap F _ (beta' j)*rep.z j^(r' j*(s' (e.label c)+k))) c] at h
    simpa only [e.beta_eq,e.r_eq,e.s_eq] using h
  · intro c k
    have h := rep.theta_moment (e.label c) k
    rw [←e.sum_fiber_transport
      (fun j ↦ rep.z j^(r' j*k)*(rep.z j^v' j*rep.theta j)) c] at h
    simpa only [e.r_eq,e.v_eq] using h
  · intro c k
    have h := rep.xi_moment (e.label c) k
    rw [←e.sum_fiber_transport
      (fun j ↦ rep.z j^(r' j*k)*((algebraMap F _ (beta' j)*rep.z j^u' j)*rep.xi j)) c] at h
    simpa only [e.beta_eq,e.r_eq,e.u_eq] using h
  · intro c k
    have h := rep.mixed_moment (e.label c) k
    rw [←e.sum_fiber_transport
      (fun j ↦ rep.z j^(r' j*k)*(rep.theta j*rep.xi j)) c] at h
    simpa only [e.r_eq] using h

def map :
    HomogeneousClusterAlgebra beta cluster r s u v →ₐ[F]
      HomogeneousClusterAlgebra beta' cluster' r' s' u' v' := by
  letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
  exact e.targetRepresentation.lift
    (homogeneousCluster_supercommutative beta' cluster' r' s' u' v')

@[simp] theorem map_z (i : ι) :
    e.map (homogeneousClusterZ beta cluster r s u v i)=
      homogeneousClusterZ beta' cluster' r' s' u' v' (e.index i) := by
  letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
  exact e.targetRepresentation.lift_z _ i

@[simp] theorem map_theta (i : ι) :
    e.map (homogeneousClusterTheta beta cluster r s u v i)=
      homogeneousClusterTheta beta' cluster' r' s' u' v' (e.index i) := by
  letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
  exact e.targetRepresentation.lift_theta _ i

@[simp] theorem map_xi (i : ι) :
    e.map (homogeneousClusterXi beta cluster r s u v i)=
      homogeneousClusterXi beta' cluster' r' s' u' v' (e.index i) := by
  letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
  exact e.targetRepresentation.lift_xi _ i

def algEquiv :
    HomogeneousClusterAlgebra beta cluster r s u v ≃ₐ[F]
      HomogeneousClusterAlgebra beta' cluster' r' s' u' v' :=
  AlgEquiv.ofAlgHom e.map e.symm.map
    (by
      apply homogeneousCluster_hom_ext beta' cluster' r' s' u' v'
      · intro i
        simp only [AlgHom.comp_apply,map_z,symm,Equiv.apply_symm_apply,AlgHom.id_apply]
      · intro i
        simp only [AlgHom.comp_apply,map_theta,symm,Equiv.apply_symm_apply,AlgHom.id_apply]
      · intro i
        simp only [AlgHom.comp_apply,map_xi,symm,Equiv.apply_symm_apply,AlgHom.id_apply])
    (by
      apply homogeneousCluster_hom_ext beta cluster r s u v
      · intro i
        simp only [AlgHom.comp_apply,map_z,symm,Equiv.symm_apply_apply,AlgHom.id_apply]
      · intro i
        simp only [AlgHom.comp_apply,map_theta,symm,Equiv.symm_apply_apply,AlgHom.id_apply]
      · intro i
        simp only [AlgHom.comp_apply,map_xi,symm,Equiv.symm_apply_apply,AlgHom.id_apply])

theorem map_degree {j : ℕ} {x : HomogeneousClusterAlgebra beta cluster r s u v}
    (hx : x∈homogeneousClusterPart beta cluster r s u v j) :
    e.map x∈homogeneousClusterPart beta' cluster' r' s' u' v' j := by
  letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
  exact e.targetRepresentation.lift_degree
    (homogeneousCluster_supercommutative beta' cluster' r' s' u' v') hx

end ClusterParameterEquiv
end PaperVerification.Fermion

