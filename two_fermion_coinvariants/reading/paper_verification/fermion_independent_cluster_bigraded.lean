module

public import PaperVerification.FermionIndependentClusterTensor
public import PaperVerification.FermionClusterReindex
public import PaperVerification.FermionClusterBigrading

/-!
# Exterior-bigraded independent-cluster factorization

Both directions preserve the original theta/xi word counts. The target
bigrading is the natural finite tensor bigrading, not a transported grading.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.Fermion

universe u
namespace ClusterFamilyData

variable {F : Type u} [Field F] [CharZero F] {m : ℕ}
  (d : ClusterFamilyData F m)

local instance FermionIndependentClusterBigraded_factorOddOrder (c : Fin m) : LinearOrder (d.Index c⊕d.Index c) :=
  finiteIndexLinearOrder _
local instance FermionIndependentClusterBigraded_wholeOddOrder :
    LinearOrder ((Σ c,d.Index c)⊕(Σ c,d.Index c)) := finiteIndexLinearOrder _

def factorBigrading (c : Fin m) : NGradedAlgebra.Bigrading (d.factor c) where
  part := homogeneousClusterBigradedPart (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)
  graded := homogeneousClusterBigrading _ _ _ _ _ _
  total := homogeneousCluster_bigraded_total _ _ _ _ _ _

def wholeBigrading : NGradedAlgebra.Bigrading d.whole where
  part := homogeneousClusterBigradedPart d.wholeBeta Sigma.fst d.wholeR d.s d.wholeU d.wholeV
  graded := homogeneousClusterBigrading _ _ _ _ _ _
  total := homogeneousCluster_bigraded_total _ _ _ _ _ _

def tensorBigrading : NGradedAlgebra.Bigrading d.tensor :=
  NGradedAlgebra.Bigrading.tensorFin d.factor d.factorBigrading

theorem factorInclude_bidegree (c : Fin m) {g : ℕ×ℕ} {x : (d.factor c).Carrier}
    (hx : x∈(d.factorBigrading c).part g) :
    (d.factorInclude c).toAlgHom x∈d.tensorBigrading.part g :=
  NGradedAlgebra.Bigrading.tensorFinInclude_bidegree d.factor d.factorBigrading c hx

theorem factorToWhole_bidegree (c : Fin m) {g : ℕ×ℕ} {x : (d.factor c).Carrier}
    (hx : x∈(d.factorBigrading c).part g) :
    (d.factorToWhole c).toAlgHom x∈d.wholeBigrading.part g := by
  change (d.factorToWholeRep c).lift d.whole_supercommutative x∈
    d.wholeBigrading.part g
  letI : GradedAlgebra d.wholeBigrading.part := d.wholeBigrading.graded
  refine (d.factorToWholeRep c).lift_bidegree
    (F := F) (C := d.whole.Carrier) (ι := d.Index c) (κ := Unit)
    (part := d.whole.part) (beta := d.beta c) (cluster := fun _ ↦ ())
    (r := d.r c) (s := fun _ ↦ d.s c) (u := d.u c) (v := d.v c)
    d.whole_supercommutative d.wholeBigrading.part
    (degree := g) (x := x) ?_ ?_ ?_ hx
  · intro i
    exact homogeneousCluster_z_bidegree d.wholeBeta Sigma.fst
      d.wholeR d.s d.wholeU d.wholeV ⟨c,i⟩
  · intro i
    exact homogeneousCluster_theta_bidegree d.wholeBeta Sigma.fst
      d.wholeR d.s d.wholeU d.wholeV ⟨c,i⟩
  · intro i
    exact homogeneousCluster_xi_bidegree d.wholeBeta Sigma.fst
      d.wholeR d.s d.wholeU d.wholeV ⟨c,i⟩

theorem toTensor_bidegree {g : ℕ×ℕ} {x : d.whole.Carrier}
    (hx : x∈d.wholeBigrading.part g) :
    d.toTensor.toAlgHom x∈d.tensorBigrading.part g :=
  d.tensorRep.lift_bidegree d.tensor_supercommutative d.tensorBigrading.part
    (fun i ↦ d.factorInclude_bidegree i.1
      (homogeneousCluster_z_bidegree _ _ _ _ _ _ i.2))
    (fun i ↦ d.factorInclude_bidegree i.1
      (homogeneousCluster_theta_bidegree _ _ _ _ _ _ i.2))
    (fun i ↦ d.factorInclude_bidegree i.1
      (homogeneousCluster_xi_bidegree _ _ _ _ _ _ i.2)) hx

theorem fromTensor_bidegree {g : ℕ×ℕ} {x : d.tensor.Carrier}
    (hx : x∈d.tensorBigrading.part g) :
    d.fromTensor.toAlgHom x∈d.wholeBigrading.part g :=
  NGradedAlgebra.Bigrading.tensorFinLift_bidegree d.factor d.factorBigrading
    d.whole d.wholeBigrading d.whole_supercommutative d.factorToWhole
    (fun i _ _ h ↦ d.factorToWhole_bidegree i h) hx

theorem independentClusterTensorEquiv_bigraded_iff
    (g : ℕ×ℕ) (x : d.whole.Carrier) :
    d.independentClusterTensorEquiv x∈d.tensorBigrading.part g ↔
      x∈d.wholeBigrading.part g := by
  constructor
  · intro hx
    have h := d.fromTensor_bidegree hx
    change d.independentClusterTensorEquiv.symm (d.independentClusterTensorEquiv x)∈_ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact d.toTensor_bidegree

end ClusterFamilyData

namespace ClusterParameterEquiv

variable {F ι κ ι' κ' : Type*} [Field F] [CharZero F]
  [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  [LinearOrder (ι⊕ι)] [LinearOrder (ι'⊕ι')]
  {beta : ι → F} {cluster : ι → κ} {r : ι → ℕ} {s : κ → ℕ} {u v : ι → ℕ}
  {beta' : ι' → F} {cluster' : ι' → κ'} {r' : ι' → ℕ} {s' : κ' → ℕ} {u' v' : ι' → ℕ}
  (e : ClusterParameterEquiv beta cluster r s u v beta' cluster' r' s' u' v')

theorem map_bidegree {g : ℕ×ℕ} {x : HomogeneousClusterAlgebra beta cluster r s u v}
    (hx : x∈homogeneousClusterBigradedPart beta cluster r s u v g) :
    e.map x∈homogeneousClusterBigradedPart beta' cluster' r' s' u' v' g := by
  letI := homogeneousClusterGrading beta' cluster' r' s' u' v'
  letI := homogeneousClusterBigrading beta' cluster' r' s' u' v'
  exact e.targetRepresentation.lift_bidegree
    (homogeneousCluster_supercommutative beta' cluster' r' s' u' v')
    (homogeneousClusterBigradedPart beta' cluster' r' s' u' v')
    (fun i ↦ homogeneousCluster_z_bidegree _ _ _ _ _ _ (e.index i))
    (fun i ↦ homogeneousCluster_theta_bidegree _ _ _ _ _ _ (e.index i))
    (fun i ↦ homogeneousCluster_xi_bidegree _ _ _ _ _ _ (e.index i)) hx

theorem algEquiv_bigraded_iff (g : ℕ×ℕ)
    (x : HomogeneousClusterAlgebra beta cluster r s u v) :
    e.algEquiv x∈homogeneousClusterBigradedPart beta' cluster' r' s' u' v' g ↔
      x∈homogeneousClusterBigradedPart beta cluster r s u v g := by
  constructor
  · intro hx
    have h := e.symm.map_bidegree hx
    change e.algEquiv.symm (e.algEquiv x)∈_ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact e.map_bidegree

end ClusterParameterEquiv
end PaperVerification.Fermion

