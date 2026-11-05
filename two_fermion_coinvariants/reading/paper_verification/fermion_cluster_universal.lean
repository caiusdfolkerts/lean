module

public import PaperVerification.FermionSupercommutative
public import PaperVerification.FermionClusterOrdinary
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Universal property of the literal homogeneous cluster algebra

The target relations are checked in a genuine graded supercommutative algebra.
The coefficient map factors through its actual degree-zero subalgebra, whose
commutativity and centrality are proved from the sign law. The odd map is the
exterior-algebra lift of the actual degree-one generators.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section DegreeZero

variable {F C : Type*} [CommRing F] [Ring C] [Algebra F C]
  (part : ℕ → Submodule F C) [GradedAlgebra part]

def degreeZeroSubalgebra : Subalgebra F C where
  carrier := {x : C | x∈part 0}
  zero_mem' := (part 0).zero_mem
  add_mem' := (part 0).add_mem
  one_mem' := SetLike.one_mem_graded part
  mul_mem' := by
    intro x y hx hy
    change x*y∈part 0
    exact SetLike.mul_mem_graded (i := (0 : ℕ)) (j := 0) hx hy
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (part 0).smul_mem r (SetLike.one_mem_graded part)

def degreeZeroCommRing (h : IsSupercommutative part) :
    CommRing (degreeZeroSubalgebra part) where
  toRing := inferInstance
  mul_comm a b := Subtype.ext <|
    (supercommutative_degree_zero_central part h a.property (b : C)).eq

end DegreeZero

section Presentation

variable {F ι κ : Type*} [Field F] [CharZero F] [Fintype ι] [Fintype κ]

abbrev HomogeneousClusterAlgebra (beta : ι → F) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ) :=
  ClusterOddQuotient cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v

def homogeneousClusterMk (beta : ι → F) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ) :
    ClusterExterior (ClusterOrdinary beta cluster r s) ι →ₐ[
      ClusterOrdinary beta cluster r s] HomogeneousClusterAlgebra beta cluster r s u v :=
  (clusterOddIdeal cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v).ringCon.mkₐ _

def homogeneousClusterZ (beta : ι → F) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ) (i : ι) :
    HomogeneousClusterAlgebra beta cluster r s u v :=
  algebraMap (ClusterOrdinary beta cluster r s) _ (clusterZ beta cluster r s i)

def homogeneousClusterTheta (beta : ι → F) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ) (i : ι) :
    HomogeneousClusterAlgebra beta cluster r s u v :=
  homogeneousClusterMk beta cluster r s u v (clusterTheta i)

def homogeneousClusterXi (beta : ι → F) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ) (i : ι) :
    HomogeneousClusterAlgebra beta cluster r s u v :=
  homogeneousClusterMk beta cluster r s u v (clusterXi i)

variable {C : Type*} [Ring C] [Algebra F C]
  (part : ℕ → Submodule F C) [GradedAlgebra part]

/-- A representation consists of images of the literal generators, with
the literal defining relations. These are evaluation data, not assumptions
on the homogeneous quotient itself. -/
structure ClusterRepresentation (beta : ι → F) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ) where
  z : ι → C
  theta : ι → C
  xi : ι → C
  z_degree : ∀ i,z i∈part 0
  theta_degree : ∀ i,theta i∈part 1
  xi_degree : ∀ i,xi i∈part 1
  ordinary : ∀ c k,∑ i : {i : ι // cluster i=c},
    algebraMap F C (beta i.1)*z i.1^(r i.1*(s c+k))=0
  theta_moment : ∀ c k,∑ i : {i : ι // cluster i=c},
    z i.1^(r i.1*k)*(z i.1^v i.1*theta i.1)=0
  xi_moment : ∀ c k,∑ i : {i : ι // cluster i=c},
    z i.1^(r i.1*k)*((algebraMap F C (beta i.1)*z i.1^u i.1)*xi i.1)=0
  mixed_moment : ∀ c k,∑ i : {i : ι // cluster i=c},
    z i.1^(r i.1*k)*(theta i.1*xi i.1)=0

namespace ClusterRepresentation

variable {part}
  {beta : ι → F} {cluster : ι → κ} {r u v : ι → ℕ} {s : κ → ℕ}
  (rep : ClusterRepresentation part beta cluster r s u v) (hC : IsSupercommutative part)

def coefficientMapToDegreeZero :
    letI := degreeZeroCommRing part hC
    ClusterOrdinary beta cluster r s →ₐ[F] degreeZeroSubalgebra part := by
  letI := degreeZeroCommRing part hC
  refine clusterOrdinaryLift beta cluster r s
    (fun i ↦ ⟨rep.z i,rep.z_degree i⟩) ?_
  intro c k
  apply Subtype.ext
  change (degreeZeroSubalgebra part).val _ = (0 : C)
  rw [map_sum]
  simp only [map_mul,map_pow,AlgHom.commutes]
  simpa only [Subalgebra.val_apply] using rep.ordinary c k

def coefficientMap : ClusterOrdinary beta cluster r s →ₐ[F] C := by
  letI := degreeZeroCommRing part hC
  exact (degreeZeroSubalgebra part).val.comp (rep.coefficientMapToDegreeZero hC)

@[simp] theorem coefficientMap_z (i : ι) :
    rep.coefficientMap hC (clusterZ beta cluster r s i)=rep.z i := by
  simp [coefficientMap,coefficientMapToDegreeZero]

theorem coefficientMap_degree (a : ClusterOrdinary beta cluster r s) :
    rep.coefficientMap hC a∈part 0 := by
  letI := degreeZeroCommRing part hC
  exact (rep.coefficientMapToDegreeZero hC a).property

def coefficientAlgebra : Algebra (ClusterOrdinary beta cluster r s) C :=
  (rep.coefficientMap hC).toRingHom.toAlgebra' (fun a c ↦
    (supercommutative_degree_zero_central part hC (rep.coefficientMap_degree hC a) c).eq)

@[simp] theorem coefficientAlgebra_algebraMap (a : ClusterOrdinary beta cluster r s) :
    letI := rep.coefficientAlgebra hC
    algebraMap (ClusterOrdinary beta cluster r s) C a=rep.coefficientMap hC a := rfl

def coefficientTower :
    letI := rep.coefficientAlgebra hC
    IsScalarTower F (ClusterOrdinary beta cluster r s) C :=
  letI := rep.coefficientAlgebra hC
  IsScalarTower.of_algebraMap_eq fun a ↦ (rep.coefficientMap hC).commutes a |>.symm

def oddLinearMap :
    letI := rep.coefficientAlgebra hC
    ((ι⊕ι) → ClusterOrdinary beta cluster r s) →ₗ[ClusterOrdinary beta cluster r s] C :=
  letI := rep.coefficientAlgebra hC
  (Pi.basisFun (ClusterOrdinary beta cluster r s) (ι⊕ι)).constr
    (ClusterOrdinary beta cluster r s) (Sum.elim rep.theta rep.xi)

theorem oddLinearMap_degree
    (m : (ι⊕ι) → ClusterOrdinary beta cluster r s) :
    rep.oddLinearMap hC m∈part 1 := by
  letI := rep.coefficientAlgebra hC
  letI := rep.coefficientTower hC
  rw [oddLinearMap,Module.Basis.constr_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  rw [Algebra.smul_def]
  change rep.coefficientMap hC _*Sum.elim rep.theta rep.xi i∈part 1
  have hi : Sum.elim rep.theta rep.xi i∈part 1 := by
    cases i with
    | inl i => exact rep.theta_degree i
    | inr i => exact rep.xi_degree i
  simpa only [Nat.zero_add] using
    SetLike.mul_mem_graded (rep.coefficientMap_degree hC _) hi

def exteriorMap :
    letI := rep.coefficientAlgebra hC
    ClusterExterior (ClusterOrdinary beta cluster r s) ι →ₐ[
      ClusterOrdinary beta cluster r s] C :=
  letI := rep.coefficientAlgebra hC
  ExteriorAlgebra.lift (ClusterOrdinary beta cluster r s)
    ⟨rep.oddLinearMap hC,fun m ↦
      supercommutative_odd_square_zero part hC (rep.oddLinearMap_degree hC m)⟩

@[simp] theorem exteriorMap_theta (i : ι) :
    rep.exteriorMap hC (clusterTheta i)=rep.theta i := by
  letI := rep.coefficientAlgebra hC
  simp only [exteriorMap,clusterTheta,exteriorGenerator,ExteriorAlgebra.lift_ι_apply,
    oddLinearMap,←Pi.basisFun_apply,Module.Basis.constr_basis,Sum.elim_inl]

@[simp] theorem exteriorMap_xi (i : ι) :
    rep.exteriorMap hC (clusterXi i)=rep.xi i := by
  letI := rep.coefficientAlgebra hC
  simp only [exteriorMap,clusterXi,exteriorGenerator,ExteriorAlgebra.lift_ι_apply,
    oddLinearMap,←Pi.basisFun_apply,Module.Basis.constr_basis,Sum.elim_inr]

theorem exteriorMap_smul (a : ClusterOrdinary beta cluster r s)
    (x : ClusterExterior (ClusterOrdinary beta cluster r s) ι) :
    rep.exteriorMap hC (a • x)=rep.coefficientMap hC a*rep.exteriorMap hC x := by
  letI := rep.coefficientAlgebra hC
  rw [map_smul,Algebra.smul_def]
  rfl

theorem exteriorMap_kills :
    ∀ x∈clusterOddIdeal cluster (clusterZ beta cluster r s)
      (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v,
      rep.exteriorMap hC x=0 := by
  letI := rep.coefficientAlgebra hC
  rw [clusterOddIdeal_killed_iff]
  refine ⟨?_,?_,?_⟩
  · intro c k
    change ∑ i : {i : ι // cluster i=c},
      _ • (_ • rep.exteriorMap hC (clusterTheta i.1))=0
    simp only [Algebra.smul_def,exteriorMap_theta,coefficientAlgebra_algebraMap,
      coefficientMap_z,map_pow]
    exact rep.theta_moment c k
  · intro c k
    change ∑ i : {i : ι // cluster i=c},
      _ • (_ • rep.exteriorMap hC (clusterXi i.1))=0
    simp only [Algebra.smul_def,exteriorMap_xi,coefficientAlgebra_algebraMap,
      coefficientMap_z,map_mul,map_pow,
      (rep.coefficientMap hC).commutes]
    exact rep.xi_moment c k
  · intro c k
    change ∑ i : {i : ι // cluster i=c},
      _ • (rep.exteriorMap hC (clusterTheta i.1)*rep.exteriorMap hC (clusterXi i.1))=0
    simp only [Algebra.smul_def,exteriorMap_theta,exteriorMap_xi,
      coefficientAlgebra_algebraMap,coefficientMap_z,map_pow]
    exact rep.mixed_moment c k

/-- Evaluation on the actual two-sided quotient. -/
def lift : HomogeneousClusterAlgebra beta cluster r s u v →ₐ[F] C := by
  letI := rep.coefficientAlgebra hC
  letI := rep.coefficientTower hC
  let I := clusterOddIdeal cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v
  exact (I.ringCon.liftₐ (rep.exteriorMap hC)
    (ringCon_le_ker_of_kills I (rep.exteriorMap hC) (rep.exteriorMap_kills hC))).restrictScalars F

@[simp] theorem lift_mk (x : ClusterExterior (ClusterOrdinary beta cluster r s) ι) :
    rep.lift hC (homogeneousClusterMk beta cluster r s u v x)=rep.exteriorMap hC x := rfl

@[simp] theorem lift_z (i : ι) :
    rep.lift hC (homogeneousClusterZ beta cluster r s u v i)=rep.z i := by
  letI := rep.coefficientAlgebra hC
  letI := rep.coefficientTower hC
  simp only [homogeneousClusterZ,lift,AlgHom.restrictScalars_apply,AlgHom.commutes,
    coefficientAlgebra_algebraMap,coefficientMap_z]

@[simp] theorem lift_theta (i : ι) :
    rep.lift hC (homogeneousClusterTheta beta cluster r s u v i)=rep.theta i :=
  rep.exteriorMap_theta hC i

@[simp] theorem lift_xi (i : ι) :
    rep.lift hC (homogeneousClusterXi beta cluster r s u v i)=rep.xi i :=
  rep.exteriorMap_xi hC i

end ClusterRepresentation
end Presentation

section Extensionality

variable {F C ι κ : Type*} [Field F] [CharZero F] [Ring C] [Algebra F C]
  [Fintype ι] [Fintype κ]
  (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ)

theorem homogeneousCluster_hom_ext
    {f g : HomogeneousClusterAlgebra beta cluster r s u v →ₐ[F] C}
    (hz : ∀ i,f (homogeneousClusterZ beta cluster r s u v i)=
      g (homogeneousClusterZ beta cluster r s u v i))
    (ht : ∀ i,f (homogeneousClusterTheta beta cluster r s u v i)=
      g (homogeneousClusterTheta beta cluster r s u v i))
    (hx : ∀ i,f (homogeneousClusterXi beta cluster r s u v i)=
      g (homogeneousClusterXi beta cluster r s u v i)) : f=g := by
  let B := ClusterOrdinary beta cluster r s
  let Q := HomogeneousClusterAlgebra beta cluster r s u v
  let q := homogeneousClusterMk beta cluster r s u v
  have hcoeff : f.comp (IsScalarTower.toAlgHom F B Q)=
      g.comp (IsScalarTower.toAlgHom F B Q) := by
    apply Ideal.Quotient.algHom_ext F
    apply MvPolynomial.algHom_ext
    intro i
    exact hz i
  have hcoeff' (a : B) : f (algebraMap B Q a)=g (algebraMap B Q a) :=
    AlgHom.congr_fun hcoeff a
  have hodd (i : ι⊕ι) :
      f (q (exteriorGenerator i))=g (q (exteriorGenerator i)) := by
    cases i with
    | inl i => exact ht i
    | inr i => exact hx i
  have hiota (i : ι⊕ι) :
      ExteriorAlgebra.ι (ClusterOrdinary beta cluster r s) (Pi.single i 1)=
        exteriorGenerator i := by
    unfold exteriorGenerator
    apply congrArg (ExteriorAlgebra.ι (ClusterOrdinary beta cluster r s))
    funext j
    by_cases hji : j=i
    · subst j
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_apply,hji,ite_false]
  apply RingCon.Quotient.hom_extₐ
  apply AlgHom.ext
  intro a
  change f (q a)=g (q a)
  induction a using ExteriorAlgebra.induction with
  | algebraMap a =>
      rw [q.commutes]
      exact hcoeff' a
  | ι m =>
      rw [pi_eq_sum_univ' m]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul,map_smul,Algebra.smul_def,map_mul,map_mul,hcoeff']
      rw [hiota,hodd]
  | mul a b ha hb => simp only [map_mul,ha,hb]
  | add a b ha hb => simp only [map_add,ha,hb]

end Extensionality

section Canonical

variable {F ι κ : Type*} [Field F] [CharZero F] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]
  (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ)

def homogeneousClusterPart :
    ℕ → Submodule F (HomogeneousClusterAlgebra beta cluster r s u v) :=
  restrictGradedPart (R := F)
    (clusterOddTotalPart cluster (clusterZ beta cluster r s)
      (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v)

def homogeneousClusterGrading :
    GradedAlgebra (homogeneousClusterPart beta cluster r s u v) := by
  letI := clusterOddTotalGrading cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v
  exact restrictGradedAlgebra _

theorem homogeneousCluster_supercommutative :
    IsSupercommutative (homogeneousClusterPart beta cluster r s u v) :=
  clusterOddTotalPart_supercommutative cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v

theorem homogeneousCluster_z_degree (i : ι) :
    homogeneousClusterZ beta cluster r s u v i∈
      homogeneousClusterPart beta cluster r s u v 0 := by
  letI := exteriorWeightedGrading (A := ClusterOrdinary beta cluster r s)
    (fun _ : ι⊕ι ↦ (1:ℕ))
  refine ⟨algebraMap (ClusterOrdinary beta cluster r s)
    (ClusterExterior (ClusterOrdinary beta cluster r s) ι) (clusterZ beta cluster r s i),?_,?_⟩
  · rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (SetLike.one_mem_graded exteriorTotalPart)
  · exact (homogeneousClusterMk beta cluster r s u v).commutes _

theorem homogeneousCluster_theta_degree (i : ι) :
    homogeneousClusterTheta beta cluster r s u v i∈
      homogeneousClusterPart beta cluster r s u v 1 :=
  ⟨clusterTheta i,exteriorGenerator_weighted_mem _ (Sum.inl i),rfl⟩

theorem homogeneousCluster_xi_degree (i : ι) :
    homogeneousClusterXi beta cluster r s u v i∈
      homogeneousClusterPart beta cluster r s u v 1 :=
  ⟨clusterXi i,exteriorGenerator_weighted_mem _ (Sum.inr i),rfl⟩

def homogeneousClusterRepresentation :
    letI := homogeneousClusterGrading beta cluster r s u v
    ClusterRepresentation (homogeneousClusterPart beta cluster r s u v)
      beta cluster r s u v := by
  letI := homogeneousClusterGrading beta cluster r s u v
  let B := ClusterOrdinary beta cluster r s
  let Q := HomogeneousClusterAlgebra beta cluster r s u v
  let q := homogeneousClusterMk beta cluster r s u v
  have hscalar (a : F) :
      algebraMap (ClusterOrdinary beta cluster r s)
        (HomogeneousClusterAlgebra beta cluster r s u v)
        (algebraMap F (ClusterOrdinary beta cluster r s) a)=
      algebraMap F (HomogeneousClusterAlgebra beta cluster r s u v) a :=
    (IsScalarTower.algebraMap_apply F (ClusterOrdinary beta cluster r s)
      (HomogeneousClusterAlgebra beta cluster r s u v) a).symm
  refine {
    z := homogeneousClusterZ beta cluster r s u v
    theta := homogeneousClusterTheta beta cluster r s u v
    xi := homogeneousClusterXi beta cluster r s u v
    z_degree := homogeneousCluster_z_degree beta cluster r s u v
    theta_degree := homogeneousCluster_theta_degree beta cluster r s u v
    xi_degree := homogeneousCluster_xi_degree beta cluster r s u v
    ordinary := ?_
    theta_moment := ?_
    xi_moment := ?_
    mixed_moment := ?_ }
  · intro c k
    have hm := congrArg (algebraMap (ClusterOrdinary beta cluster r s)
      (HomogeneousClusterAlgebra beta cluster r s u v))
        (clusterZ_moments beta cluster r s c k)
    simpa only [map_sum,map_mul,map_pow,map_zero,hscalar,
      homogeneousClusterZ] using hm
  all_goals
    intro c k
    have hm (family : LocalOddFamily) :
        q (clusterOddCurrent cluster (clusterZ beta cluster r s)
          (fun i ↦ algebraMap F B (beta i)) r u v family c k)=0 :=
      quotientMk_eq_zero_of_mem _ _ (TwoSidedIdeal.subset_span ⟨(c,family,k),rfl⟩)
  · have h := hm .theta
    simpa only [clusterOddCurrent,map_sum,map_smul,Algebra.smul_def,map_pow,
      homogeneousClusterZ,homogeneousClusterTheta] using h
  · have h := hm .xi
    simpa only [B,Q,q,clusterOddCurrent,map_sum,map_smul,Algebra.smul_def,map_mul,map_pow,
      hscalar,homogeneousClusterZ,homogeneousClusterXi] using h
  · have h := hm .mixed
    simpa only [clusterOddCurrent,map_sum,map_smul,map_mul,Algebra.smul_def,map_pow,
      homogeneousClusterZ,homogeneousClusterTheta,homogeneousClusterXi] using h

end Canonical

end PaperVerification.Fermion
