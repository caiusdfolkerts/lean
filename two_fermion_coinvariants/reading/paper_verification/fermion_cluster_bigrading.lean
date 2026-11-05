module

public import PaperVerification.FermionClusterLiftGraded
public import PaperVerification.FermionFiniteTensorBigrading

/-!
# The actual exterior bigrading of homogeneous cluster presentations

-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section Exterior

variable {A ι : Type*} [CommRing A] [Fintype ι] [LinearOrder (ι⊕ι)]

theorem exteriorWordDegree_bidegree_total (T : Finset (ι⊕ι)) :
    totalBidegree (exteriorWordDegree oddBidegree T)=
      exteriorWordDegree (fun _ : ι⊕ι ↦ (1:ℕ)) T := by
  simp only [exteriorWordDegree,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases i <;> rfl

theorem exteriorBigradedPart_le_total (g : ℕ×ℕ) :
    exteriorBigradedPart (A := A) (ι := ι) g≤exteriorTotalPart (totalBidegree g) := by
  apply Submodule.span_le.mpr
  rintro x ⟨T,hT,rfl⟩
  apply Submodule.subset_span
  refine ⟨T,?_,rfl⟩
  change exteriorWordDegree oddBidegree T=g at hT
  exact (exteriorWordDegree_bidegree_total T).symm.trans (congrArg totalBidegree hT)

end Exterior

section Canonical

variable {F ι κ : Type*} [Field F] [CharZero F] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]
  (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ)

def homogeneousClusterBigradedPart :
    (ℕ×ℕ) → Submodule F (HomogeneousClusterAlgebra beta cluster r s u v) :=
  restrictGradedPart (R := F)
    (clusterOddBigradedPart cluster (clusterZ beta cluster r s)
      (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v)

def homogeneousClusterBigrading :
    GradedAlgebra (homogeneousClusterBigradedPart beta cluster r s u v) := by
  letI := clusterOddBigrading cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v
  exact restrictGradedAlgebra _

theorem homogeneousCluster_bigraded_total (g : ℕ×ℕ) :
    homogeneousClusterBigradedPart beta cluster r s u v g≤
      homogeneousClusterPart beta cluster r s u v (totalBidegree g) := by
  rintro x ⟨y,hy,rfl⟩
  exact ⟨y,exteriorBigradedPart_le_total g hy,rfl⟩

theorem homogeneousCluster_z_bidegree (i : ι) :
    homogeneousClusterZ beta cluster r s u v i∈
      homogeneousClusterBigradedPart beta cluster r s u v (0,0) := by
  letI := exteriorWeightedGrading (A := ClusterOrdinary beta cluster r s)
    (oddBidegree (ι := ι))
  refine ⟨algebraMap (ClusterOrdinary beta cluster r s)
    (ClusterExterior (ClusterOrdinary beta cluster r s) ι) (clusterZ beta cluster r s i),?_,?_⟩
  · rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (SetLike.one_mem_graded exteriorBigradedPart)
  · exact (homogeneousClusterMk beta cluster r s u v).commutes _

theorem homogeneousCluster_theta_bidegree (i : ι) :
    homogeneousClusterTheta beta cluster r s u v i∈
      homogeneousClusterBigradedPart beta cluster r s u v (1,0) :=
  ⟨clusterTheta i,exteriorGenerator_weighted_mem oddBidegree (Sum.inl i),rfl⟩

theorem homogeneousCluster_xi_bidegree (i : ι) :
    homogeneousClusterXi beta cluster r s u v i∈
      homogeneousClusterBigradedPart beta cluster r s u v (0,1) :=
  ⟨clusterXi i,exteriorGenerator_weighted_mem oddBidegree (Sum.inr i),rfl⟩

end Canonical

namespace ClusterRepresentation

variable {F C ι κ : Type*} [Field F] [CharZero F] [Ring C] [Algebra F C]
  [Fintype ι] [Fintype κ] [LinearOrder (ι⊕ι)]
  {part : ℕ → Submodule F C} [GradedAlgebra part]
  {beta : ι → F} {cluster : ι → κ} {r u v : ι → ℕ} {s : κ → ℕ}
  (rep : ClusterRepresentation part beta cluster r s u v) (hC : IsSupercommutative part)
  (qC : (ℕ×ℕ) → Submodule F C) [GradedAlgebra qC]
  (hz : ∀ i,rep.z i∈qC (0,0))
  (ht : ∀ i,rep.theta i∈qC (1,0))
  (hx : ∀ i,rep.xi i∈qC (0,1))

include hz in
theorem coefficientMap_bidegree (a : ClusterOrdinary beta cluster r s) :
    rep.coefficientMap hC a∈qC (0,0) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective F (clusterPowerIdeal beta cluster r s) a
  let g := (rep.coefficientMap hC).comp (Ideal.Quotient.mkₐ F (clusterPowerIdeal beta cluster r s))
  change g p∈qC (0,0)
  have hX (i : ι) : g (MvPolynomial.X i)=rep.z i := rep.coefficientMap_z hC i
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [←MvPolynomial.algebraMap_eq,g.commutes,Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ a (SetLike.one_mem_graded qC)
  | add p q hp hq =>
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul,hX]
      exact SetLike.mul_mem_graded hp (hz i)

include hz ht hx in
theorem exteriorMap_bidegree {degree : ℕ×ℕ}
    {x : ClusterExterior (ClusterOrdinary beta cluster r s) ι}
    (h : x∈exteriorBigradedPart degree) :
    rep.exteriorMap hC x∈qC degree := by
  letI := rep.coefficientAlgebra hC
  letI := rep.coefficientTower hC
  let gen := Sum.elim rep.theta rep.xi
  have hgen (i : ι⊕ι) : gen i∈qC (oddBidegree i) := by
    cases i with
    | inl i => exact ht i
    | inr i => exact hx i
  have hegen (i : ι⊕ι) : rep.exteriorMap hC (exteriorGenerator i)=gen i := by
    cases i with
    | inl i => exact rep.exteriorMap_theta hC i
    | inr i => exact rep.exteriorMap_xi hC i
  induction h using Submodule.span_induction with
  | mem x h =>
      obtain ⟨T,hT,rfl⟩ := h
      rw [←hT,Module.Basis.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
      have hs : (T.sort.map oddBidegree).sum=exteriorWordDegree oddBidegree T := by
        simpa only [exteriorWordDegree,Finset.sort_toFinset] using
          (List.sum_toFinset oddBidegree (Finset.sort_nodup T (· ≤ ·))).symm
      have hbase (i : ι⊕ι) :
          (ExteriorAlgebra.ι (ClusterOrdinary beta cluster r s))
            ((Pi.basisFun (ClusterOrdinary beta cluster r s) (ι⊕ι)) i)=
          exteriorGenerator (A := ClusterOrdinary beta cluster r s) i := by
        unfold exteriorGenerator
        apply congrArg (ExteriorAlgebra.ι (ClusterOrdinary beta cluster r s))
        funext j
        by_cases hij : i=j
        · subst j
          simp [Pi.basisFun_apply]
        · simp [Pi.basisFun_apply,Pi.single_apply,hij,Ne.symm hij]
      have h := graded_list_prod_mem qC oddBidegree gen hgen T.sort
      simpa only [List.map_map,Function.comp_def,hbase,
        hegen,hs] using h
  | zero => simpa only [map_zero] using (qC degree).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [rep.exteriorMap_smul]
      simpa only [show ((0,0) : ℕ×ℕ)=0 from rfl,zero_add] using
        SetLike.mul_mem_graded (rep.coefficientMap_bidegree hC qC hz a) ih

include hz ht hx in
theorem lift_bidegree {degree : ℕ×ℕ}
    {x : HomogeneousClusterAlgebra beta cluster r s u v}
    (h : x∈homogeneousClusterBigradedPart beta cluster r s u v degree) :
    rep.lift hC x∈qC degree := by
  obtain ⟨y,hy,rfl⟩ := h
  exact rep.exteriorMap_bidegree hC qC hz ht hx hy

end ClusterRepresentation
end PaperVerification.Fermion

