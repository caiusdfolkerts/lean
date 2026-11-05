module

public import PaperVerification.FermionClusterLiftGraded
public import PaperVerification.FermionFiniteTensorUniversal

/-!
# Independent homogeneous clusters are an actual finite super tensor product

The factors are literal polynomial/exterior quotients on their own disjoint
variable sets. Both maps are built by evaluating their defining presentations.
The inverse identities are checked on every polynomial, theta, and xi generator.
No dimension comparison is used.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

universe u

def finiteIndexLinearOrder (ι : Type u) [Fintype ι] : LinearOrder ι :=
  LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective

def sigmaFiberAtEquiv {m : ℕ} (ι : Fin m → Type u) (c : Fin m) :
    {x : (Σ j,ι j) // x.1=c} ≃ ι c where
  toFun x := x.property ▸ x.val.2
  invFun i := ⟨⟨c,i⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,i⟩,h⟩; cases h; rfl
  right_inv _ := rfl

/-- The enumeration occurring in an abstract cluster presentation after its
cluster index is specialized to `Fin m`. The equality decision is explicit,
so specializing the index cannot silently replace it with another instance. -/
abbrev sigmaFiberClassicalFintype {m : ℕ} (ι : Fin m → Type u)
    [∀ c,Fintype (ι c)] (c : Fin m) : Fintype {x : (Σ j,ι j) // x.1=c} :=
  @Subtype.fintype (Σ j,ι j) (fun x ↦ x.1=c)
    (fun x ↦ Classical.propDecidable (x.1=c)) inferInstance

theorem sum_sigmaFiber {m : ℕ} (ι : Fin m → Type u)
    [∀ c,Fintype (ι c)] {C : Type*} [AddCommMonoid C]
    (f : (Σ c,ι c) → C) (c : Fin m)
    [fiberFintype : Fintype {x : (Σ j,ι j) // x.1=c}] :
    (∑ x : {x : (Σ j,ι j) // x.1=c},f x.1)=∑ i,f ⟨c,i⟩ :=
  ((sigmaFiberAtEquiv ι c).symm.sum_comp (fun x ↦ f x.1)).symm

/-- The analogous presentation enumeration for a single cluster. -/
abbrev constantFiberClassicalFintype (ι : Type*) [Fintype ι] :
    Fintype {i : ι // (fun _ : ι ↦ ()) i=()} :=
  @Subtype.fintype ι (fun i ↦ (fun _ : ι ↦ ()) i=())
    (fun i ↦ Classical.propDecidable ((fun _ : ι ↦ ()) i=())) inferInstance

theorem sum_constantFiber {ι C : Type*} [Fintype ι] [AddCommMonoid C]
    (f : ι → C)
    [fiberFintype : Fintype {i : ι // (fun _ : ι ↦ ()) i=()}] :
    (∑ x : {i : ι // (fun _ : ι ↦ ()) i=()},f x.1)=∑ i,f i := by
  let e : {i : ι // (fun _ : ι ↦ ()) i=()} ≃ ι :=
    ⟨Subtype.val,fun i ↦ ⟨i,rfl⟩,fun _ ↦ rfl,fun _ ↦ rfl⟩
  exact (e.symm.sum_comp (fun x ↦ f x.1)).symm

/-- Sum reindexing accepts the literal subtype summand, including its proof
argument, so no higher-order inference through `Subtype.val` is required. -/
theorem sum_sigmaFiber_apply {m : ℕ} (ι : Fin m → Type u)
    [∀ c,Fintype (ι c)] {C : Type*} [AddCommMonoid C] (c : Fin m)
    [fiberFintype : Fintype {x : (Σ j,ι j) // x.1=c}]
    (f : {x : (Σ j,ι j) // x.1=c} → C) :
    (∑ x,f x)=∑ i,f ⟨⟨c,i⟩,rfl⟩ :=
  ((sigmaFiberAtEquiv ι c).symm.sum_comp f).symm

/-- The corresponding literal summand form for a one-cluster fiber. -/
theorem sum_constantFiber_apply {ι C : Type*} [Fintype ι] [AddCommMonoid C]
    [fiberFintype : Fintype {i : ι // (fun _ : ι ↦ ()) i=()}]
    (f : {i : ι // (fun _ : ι ↦ ()) i=()} → C) :
    (∑ x,f x)=∑ i,f ⟨i,rfl⟩ := by
  let e : {i : ι // (fun _ : ι ↦ ()) i=()} ≃ ι :=
    ⟨Subtype.val,fun i ↦ ⟨i,rfl⟩,fun _ ↦ rfl,fun _ ↦ rfl⟩
  exact (e.symm.sum_comp f).symm

structure ClusterFamilyData (F : Type u) [Field F] (m : ℕ) where
  Index : Fin m → Type u
  [finite : ∀ c,Fintype (Index c)]
  beta : ∀ c,Index c → F
  r : ∀ c,Index c → ℕ
  s : Fin m → ℕ
  u : ∀ c,Index c → ℕ
  v : ∀ c,Index c → ℕ

attribute [instance] ClusterFamilyData.finite

namespace ClusterFamilyData

variable {F : Type u} [Field F] [CharZero F] {m : ℕ}
  (d : ClusterFamilyData F m)

local instance FermionIndependentClusterTensor_factorOddOrder (c : Fin m) : LinearOrder (d.Index c⊕d.Index c) :=
  finiteIndexLinearOrder _
local instance FermionIndependentClusterTensor_wholeOddOrder :
    LinearOrder ((Σ c,d.Index c)⊕(Σ c,d.Index c)) :=
  finiteIndexLinearOrder _

def wholeBeta (i : Σ c,d.Index c) : F := d.beta i.1 i.2
def wholeR (i : Σ c,d.Index c) : ℕ := d.r i.1 i.2
def wholeU (i : Σ c,d.Index c) : ℕ := d.u i.1 i.2
def wholeV (i : Σ c,d.Index c) : ℕ := d.v i.1 i.2

def factor (c : Fin m) : NGradedAlgebra F where
  Carrier := HomogeneousClusterAlgebra (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)
  ring := inferInstance
  algebra := inferInstance
  part := homogeneousClusterPart (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)
  graded := homogeneousClusterGrading (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)

def whole : NGradedAlgebra F where
  Carrier := HomogeneousClusterAlgebra d.wholeBeta Sigma.fst d.wholeR d.s d.wholeU d.wholeV
  ring := inferInstance
  algebra := inferInstance
  part := homogeneousClusterPart d.wholeBeta Sigma.fst d.wholeR d.s d.wholeU d.wholeV
  graded := homogeneousClusterGrading d.wholeBeta Sigma.fst d.wholeR d.s d.wholeU d.wholeV

def tensor : NGradedAlgebra F := NGradedAlgebra.tensorFin d.factor

theorem factor_supercommutative (c : Fin m) : IsSupercommutative (d.factor c).part :=
  homogeneousCluster_supercommutative _ _ _ _ _ _

theorem whole_supercommutative : IsSupercommutative d.whole.part :=
  homogeneousCluster_supercommutative _ _ _ _ _ _

theorem tensor_supercommutative : IsSupercommutative d.tensor.part :=
  NGradedAlgebra.tensorFin_supercommutative d.factor d.factor_supercommutative

def factorRep (c : Fin m) :
    ClusterRepresentation (d.factor c).part (d.beta c) (fun _ ↦ ()) (d.r c)
      (fun _ ↦ d.s c) (d.u c) (d.v c) :=
  homogeneousClusterRepresentation _ _ _ _ _ _

def wholeRep :
    ClusterRepresentation d.whole.part d.wholeBeta Sigma.fst d.wholeR d.s d.wholeU d.wholeV :=
  homogeneousClusterRepresentation _ _ _ _ _ _

def factorToWholeRep (c : Fin m) :
    ClusterRepresentation d.whole.part (d.beta c) (fun _ ↦ ()) (d.r c)
      (fun _ ↦ d.s c) (d.u c) (d.v c) where
  z i := d.wholeRep.z ⟨c,i⟩
  theta i := d.wholeRep.theta ⟨c,i⟩
  xi i := d.wholeRep.xi ⟨c,i⟩
  z_degree i := d.wholeRep.z_degree ⟨c,i⟩
  theta_degree i := d.wholeRep.theta_degree ⟨c,i⟩
  xi_degree i := d.wholeRep.xi_degree ⟨c,i⟩
  ordinary := by
    intro c' k
    cases c'
    exact (sum_constantFiber (ι := d.Index c) (C := d.whole.Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ algebraMap F d.whole.Carrier (d.beta c i) *
        d.wholeRep.z ⟨c,i⟩ ^ (d.r c i * (d.s c+k)))).trans
      ((sum_sigmaFiber d.Index (C := d.whole.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
        (fun i ↦ algebraMap F d.whole.Carrier (d.wholeBeta i) *
          d.wholeRep.z i ^ (d.wholeR i * (d.s c+k))) c).symm.trans
        (d.wholeRep.ordinary c k))
  theta_moment := by
    intro c' k
    cases c'
    exact (sum_constantFiber (ι := d.Index c) (C := d.whole.Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ d.wholeRep.z ⟨c,i⟩ ^ (d.r c i*k) *
        (d.wholeRep.z ⟨c,i⟩ ^ d.v c i * d.wholeRep.theta ⟨c,i⟩))).trans
      ((sum_sigmaFiber d.Index (C := d.whole.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
        (fun i ↦ d.wholeRep.z i ^ (d.wholeR i*k) *
          (d.wholeRep.z i ^ d.wholeV i * d.wholeRep.theta i)) c).symm.trans
        (d.wholeRep.theta_moment c k))
  xi_moment := by
    intro c' k
    cases c'
    exact (sum_constantFiber (ι := d.Index c) (C := d.whole.Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ d.wholeRep.z ⟨c,i⟩ ^ (d.r c i*k) *
        ((algebraMap F d.whole.Carrier (d.beta c i) *
          d.wholeRep.z ⟨c,i⟩ ^ d.u c i) * d.wholeRep.xi ⟨c,i⟩))).trans
      ((sum_sigmaFiber d.Index (C := d.whole.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
        (fun i ↦ d.wholeRep.z i ^ (d.wholeR i*k) *
          ((algebraMap F d.whole.Carrier (d.wholeBeta i) *
            d.wholeRep.z i ^ d.wholeU i) * d.wholeRep.xi i)) c).symm.trans
        (d.wholeRep.xi_moment c k))
  mixed_moment := by
    intro c' k
    cases c'
    exact (sum_constantFiber (ι := d.Index c) (C := d.whole.Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ d.wholeRep.z ⟨c,i⟩ ^ (d.r c i*k) *
        (d.wholeRep.theta ⟨c,i⟩ * d.wholeRep.xi ⟨c,i⟩))).trans
      ((sum_sigmaFiber d.Index (C := d.whole.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
        (fun i ↦ d.wholeRep.z i ^ (d.wholeR i*k) *
          (d.wholeRep.theta i * d.wholeRep.xi i)) c).symm.trans
        (d.wholeRep.mixed_moment c k))

def factorToWhole (c : Fin m) : NGradedHom (d.factor c) d.whole :=
  ⟨(d.factorToWholeRep c).lift d.whole_supercommutative,
    fun _ _ hx ↦ (d.factorToWholeRep c).lift_degree d.whole_supercommutative hx⟩

def factorInclude (c : Fin m) : NGradedHom (d.factor c) d.tensor :=
  NGradedAlgebra.tensorFinInclude d.factor c

def tensorRep :
    ClusterRepresentation d.tensor.part d.wholeBeta Sigma.fst d.wholeR d.s d.wholeU d.wholeV where
  z i := (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).z i.2)
  theta i := (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).theta i.2)
  xi i := (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).xi i.2)
  z_degree i := (d.factorInclude i.1).degree 0 _ ((d.factorRep i.1).z_degree i.2)
  theta_degree i := (d.factorInclude i.1).degree 1 _ ((d.factorRep i.1).theta_degree i.2)
  xi_degree i := (d.factorInclude i.1).degree 1 _ ((d.factorRep i.1).xi_degree i.2)
  ordinary := by
    intro c k
    refine (sum_sigmaFiber d.Index (C := d.tensor.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
      (fun i ↦ algebraMap F d.tensor.Carrier (d.wholeBeta i) *
        (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).z i.2) ^
          (d.wholeR i * (d.s c+k))) c).trans ?_
    have h := (sum_constantFiber (ι := d.Index c) (C := (d.factor c).Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ algebraMap F (d.factor c).Carrier (d.beta c i) *
        (d.factorRep c).z i ^ (d.r c i * (d.s c+k)))).symm.trans
          ((d.factorRep c).ordinary () k)
    have he := congrArg (d.factorInclude c).toAlgHom h
    simpa only [map_sum,map_mul,map_pow,map_zero,AlgHom.commutes,wholeBeta,wholeR] using he
  theta_moment := by
    intro c k
    refine (sum_sigmaFiber d.Index (C := d.tensor.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
      (fun i ↦ (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).z i.2) ^
          (d.wholeR i*k) *
        ((d.factorInclude i.1).toAlgHom ((d.factorRep i.1).z i.2) ^ d.wholeV i *
          (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).theta i.2))) c).trans ?_
    have h := (sum_constantFiber (ι := d.Index c) (C := (d.factor c).Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ (d.factorRep c).z i ^ (d.r c i*k) *
        ((d.factorRep c).z i ^ d.v c i * (d.factorRep c).theta i))).symm.trans
          ((d.factorRep c).theta_moment () k)
    have he := congrArg (d.factorInclude c).toAlgHom h
    simpa only [map_sum,map_mul,map_pow,map_zero,wholeR,wholeV] using he
  xi_moment := by
    intro c k
    refine (sum_sigmaFiber d.Index (C := d.tensor.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
      (fun i ↦ (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).z i.2) ^
          (d.wholeR i*k) *
        ((algebraMap F d.tensor.Carrier (d.wholeBeta i) *
            (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).z i.2) ^ d.wholeU i) *
          (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).xi i.2))) c).trans ?_
    have h := (sum_constantFiber (ι := d.Index c) (C := (d.factor c).Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ (d.factorRep c).z i ^ (d.r c i*k) *
        ((algebraMap F (d.factor c).Carrier (d.beta c i) *
          (d.factorRep c).z i ^ d.u c i) * (d.factorRep c).xi i))).symm.trans
          ((d.factorRep c).xi_moment () k)
    have he := congrArg (d.factorInclude c).toAlgHom h
    simpa only [map_sum,map_mul,map_pow,map_zero,AlgHom.commutes,wholeBeta,wholeR,wholeU] using he
  mixed_moment := by
    intro c k
    refine (sum_sigmaFiber d.Index (C := d.tensor.Carrier)
        (fiberFintype := sigmaFiberClassicalFintype d.Index c)
      (fun i ↦ (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).z i.2) ^
          (d.wholeR i*k) *
        ((d.factorInclude i.1).toAlgHom ((d.factorRep i.1).theta i.2) *
          (d.factorInclude i.1).toAlgHom ((d.factorRep i.1).xi i.2))) c).trans ?_
    have h := (sum_constantFiber (ι := d.Index c) (C := (d.factor c).Carrier)
      (fiberFintype := constantFiberClassicalFintype (d.Index c))
      (fun i ↦ (d.factorRep c).z i ^ (d.r c i*k) *
        ((d.factorRep c).theta i * (d.factorRep c).xi i))).symm.trans
          ((d.factorRep c).mixed_moment () k)
    have he := congrArg (d.factorInclude c).toAlgHom h
    simpa only [map_sum,map_mul,map_pow,map_zero,wholeR] using he

def toTensor : NGradedHom d.whole d.tensor :=
  ⟨d.tensorRep.lift d.tensor_supercommutative,
    fun _ _ hx ↦ d.tensorRep.lift_degree d.tensor_supercommutative hx⟩

def fromTensor : NGradedHom d.tensor d.whole :=
  NGradedAlgebra.tensorFinLift d.factor d.whole d.whole_supercommutative d.factorToWhole

@[simp] theorem factorToWhole_z (c : Fin m) (i : d.Index c) :
    (d.factorToWhole c).toAlgHom ((d.factorRep c).z i)=d.wholeRep.z ⟨c,i⟩ :=
  ClusterRepresentation.lift_z (d.factorToWholeRep c) d.whole_supercommutative i

@[simp] theorem factorToWhole_theta (c : Fin m) (i : d.Index c) :
    (d.factorToWhole c).toAlgHom ((d.factorRep c).theta i)=d.wholeRep.theta ⟨c,i⟩ :=
  ClusterRepresentation.lift_theta (d.factorToWholeRep c) d.whole_supercommutative i

@[simp] theorem factorToWhole_xi (c : Fin m) (i : d.Index c) :
    (d.factorToWhole c).toAlgHom ((d.factorRep c).xi i)=d.wholeRep.xi ⟨c,i⟩ :=
  ClusterRepresentation.lift_xi (d.factorToWholeRep c) d.whole_supercommutative i

@[simp] theorem toTensor_z (c : Fin m) (i : d.Index c) :
    d.toTensor.toAlgHom (d.wholeRep.z ⟨c,i⟩)=
      (d.factorInclude c).toAlgHom ((d.factorRep c).z i) :=
  ClusterRepresentation.lift_z d.tensorRep d.tensor_supercommutative ⟨c,i⟩

@[simp] theorem toTensor_theta (c : Fin m) (i : d.Index c) :
    d.toTensor.toAlgHom (d.wholeRep.theta ⟨c,i⟩)=
      (d.factorInclude c).toAlgHom ((d.factorRep c).theta i) :=
  ClusterRepresentation.lift_theta d.tensorRep d.tensor_supercommutative ⟨c,i⟩

@[simp] theorem toTensor_xi (c : Fin m) (i : d.Index c) :
    d.toTensor.toAlgHom (d.wholeRep.xi ⟨c,i⟩)=
      (d.factorInclude c).toAlgHom ((d.factorRep c).xi i) :=
  ClusterRepresentation.lift_xi d.tensorRep d.tensor_supercommutative ⟨c,i⟩

@[simp] theorem fromTensor_include (c : Fin m) (a : (d.factor c).Carrier) :
    d.fromTensor.toAlgHom ((d.factorInclude c).toAlgHom a)=
      (d.factorToWhole c).toAlgHom a :=
  NGradedAlgebra.tensorFinLift_include _ _ _ _ _ _

/-- The full actual algebra factorization for an arbitrary finite family of
independent homogeneous moment clusters. -/
def independentClusterTensorEquiv : d.whole.Carrier ≃ₐ[F] d.tensor.Carrier :=
  AlgEquiv.ofAlgHom d.toTensor.toAlgHom d.fromTensor.toAlgHom
    (by
      apply NGradedAlgebra.tensorFin_hom_ext d.factor
      intro c
      apply homogeneousCluster_hom_ext (d.beta c) (fun _ ↦ ()) (d.r c)
        (fun _ ↦ d.s c) (d.u c) (d.v c)
      · intro i
        change d.toTensor.toAlgHom (d.fromTensor.toAlgHom
          ((d.factorInclude c).toAlgHom ((d.factorRep c).z i)))=
            (d.factorInclude c).toAlgHom ((d.factorRep c).z i)
        rw [d.fromTensor_include,d.factorToWhole_z,d.toTensor_z]
      · intro i
        change d.toTensor.toAlgHom (d.fromTensor.toAlgHom
          ((d.factorInclude c).toAlgHom ((d.factorRep c).theta i)))=
            (d.factorInclude c).toAlgHom ((d.factorRep c).theta i)
        rw [d.fromTensor_include,d.factorToWhole_theta,d.toTensor_theta]
      · intro i
        change d.toTensor.toAlgHom (d.fromTensor.toAlgHom
          ((d.factorInclude c).toAlgHom ((d.factorRep c).xi i)))=
            (d.factorInclude c).toAlgHom ((d.factorRep c).xi i)
        rw [d.fromTensor_include,d.factorToWhole_xi,d.toTensor_xi])
    (by
      apply homogeneousCluster_hom_ext d.wholeBeta Sigma.fst d.wholeR d.s d.wholeU d.wholeV
      · rintro ⟨c,i⟩
        change d.fromTensor.toAlgHom (d.toTensor.toAlgHom (d.wholeRep.z ⟨c,i⟩))=
          d.wholeRep.z ⟨c,i⟩
        rw [d.toTensor_z,d.fromTensor_include,d.factorToWhole_z]
      · rintro ⟨c,i⟩
        change d.fromTensor.toAlgHom (d.toTensor.toAlgHom (d.wholeRep.theta ⟨c,i⟩))=
          d.wholeRep.theta ⟨c,i⟩
        rw [d.toTensor_theta,d.fromTensor_include,d.factorToWhole_theta]
      · rintro ⟨c,i⟩
        change d.fromTensor.toAlgHom (d.toTensor.toAlgHom (d.wholeRep.xi ⟨c,i⟩))=
          d.wholeRep.xi ⟨c,i⟩
        rw [d.toTensor_xi,d.fromTensor_include,d.factorToWhole_xi])

end ClusterFamilyData
end PaperVerification.Fermion

