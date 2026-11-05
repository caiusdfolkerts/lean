module

public import PaperVerification.FermionExteriorWordGrading
public import PaperVerification.FermionMultihomogeneousTwoSided
public import PaperVerification.FermionOddPresentation

/-!
# The actual exterior multigradings on local presentations

The components are spans of the genuine ordered exterior basis words.
Their directness comes from that basis, their multiplication from the
exterior shuffle identity, and quotient gradings from homogeneous ideals.
The bidegree records theta and xi separately.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion


def oddBidegree {ι : Type*} : ι ⊕ ι → ℕ×ℕ :=
  Sum.elim (fun _ ↦ (1,0)) (fun _ ↦ (0,1))

def oddFamilyBidegree : LocalOddFamily → ℕ×ℕ
  | .theta => (1,0)
  | .xi => (0,1)
  | .mixed => (1,1)

def oddFamilyDegree : LocalOddFamily → ℕ
  | .theta => 1
  | .xi => 1
  | .mixed => 2

section Cluster
variable {A ι κ : Type*} [CommRing A] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]

abbrev exteriorBigradedPart : ℕ×ℕ → Submodule A (ClusterExterior A ι) :=
  exteriorWeightedPart (A := A) (oddBidegree (ι := ι))

abbrev exteriorTotalPart : ℕ → Submodule A (ClusterExterior A ι) :=
  exteriorWeightedPart (A := A) (fun _ : ι⊕ι ↦ 1)

theorem clusterOddCurrent_bidegree (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ)
    (family : LocalOddFamily) (c : κ) (k : ℕ) :
    clusterOddCurrent cluster z beta r u v family c k∈
      exteriorBigradedPart (oddFamilyBidegree family) := by
  letI := exteriorWeightedGrading (A := A) (oddBidegree (ι := ι))
  have ht (i : ι) : clusterTheta (A := A) i∈exteriorBigradedPart (1,0) :=
    exteriorGenerator_weighted_mem oddBidegree (Sum.inl i)
  have hx (i : ι) : clusterXi (A := A) i∈exteriorBigradedPart (0,1) :=
    exteriorGenerator_weighted_mem oddBidegree (Sum.inr i)
  cases family
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (ht i.1))
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hx i.1))
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (SetLike.mul_mem_graded (ht i.1) (hx i.1))

theorem clusterOddCurrent_degree (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ)
    (family : LocalOddFamily) (c : κ) (k : ℕ) :
    clusterOddCurrent cluster z beta r u v family c k∈
      exteriorTotalPart (oddFamilyDegree family) := by
  letI := exteriorWeightedGrading (A := A) (fun _ : ι⊕ι ↦ (1:ℕ))
  have ht (i : ι) : clusterTheta (A := A) i∈exteriorTotalPart 1 :=
    exteriorGenerator_weighted_mem _ (Sum.inl i)
  have hx (i : ι) : clusterXi (A := A) i∈exteriorTotalPart 1 :=
    exteriorGenerator_weighted_mem _ (Sum.inr i)
  cases family
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (ht i.1))
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hx i.1))
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (SetLike.mul_mem_graded (ht i.1) (hx i.1))

def clusterOddBigradedPart (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    ℕ×ℕ → Submodule A (ClusterOddQuotient cluster z beta r u v) :=
  gradedImagePart exteriorBigradedPart ((clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A)

def clusterOddTotalPart (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    ℕ → Submodule A (ClusterOddQuotient cluster z beta r u v) :=
  gradedImagePart exteriorTotalPart ((clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A)

def clusterOddBigrading (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    GradedAlgebra (clusterOddBigradedPart cluster z beta r u v) := by
  letI := exteriorWeightedGrading (A := A) (oddBidegree (ι := ι))
  exact multihomogeneousTwoSidedQuotientGrading exteriorBigradedPart
    (Set.range fun p : κ×(LocalOddFamily×ℕ) ↦
      clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2) (by
        rintro g ⟨⟨c,family,k⟩,rfl⟩
        exact ⟨oddFamilyBidegree family,clusterOddCurrent_bidegree cluster z beta r u v family c k⟩)

def clusterOddTotalGrading (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    GradedAlgebra (clusterOddTotalPart cluster z beta r u v) := by
  letI := exteriorWeightedGrading (A := A) (fun _ : ι⊕ι ↦ (1:ℕ))
  exact multihomogeneousTwoSidedQuotientGrading exteriorTotalPart
    (Set.range fun p : κ×(LocalOddFamily×ℕ) ↦
      clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2) (by
        rintro g ⟨⟨c,family,k⟩,rfl⟩
        exact ⟨oddFamilyDegree family,clusterOddCurrent_degree cluster z beta r u v family c k⟩)

end Cluster
end PaperVerification.Fermion

