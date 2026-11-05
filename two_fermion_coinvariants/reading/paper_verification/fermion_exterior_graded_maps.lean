module

public import PaperVerification.FermionExteriorMultigrading
public import PaperVerification.FermionExteriorWordMaps
public import PaperVerification.FermionLocalCoefficientTransport

/-!
# Preservation of the actual exterior multigrading

The components are the original spans of exterior basis words. Their
preservation is derived from the images of the odd generators and from the
coefficient action. The grading is never defined by transporting it along
the normalization isomorphism.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

theorem twoSidedQuotientEquivOfEq_image_iff
    {F S A Γ : Type*} [CommRing F] [CommRing S] [Ring A]
    [Algebra F A] [Algebra S A]
    (part : Γ → Submodule S A) {I J : TwoSidedIdeal A}
    (h : I=J) (g : Γ) (x : I.ringCon.Quotient) :
    twoSidedQuotientEquivOfEq (R := F) h x∈
      gradedImagePart part (J.ringCon.mkₐ S) g ↔
      x∈gradedImagePart part (I.ringCon.mkₐ S) g := by
  subst J
  rfl


section Coefficients

variable {F A B ι Γ : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]

theorem exteriorWeighted_coefficient_map_mem (w : ι → Γ) (e : A ≃ₐ[F] B)
    {d : Γ} {x : ExteriorAlgebra A (ι → A)}
    (hx : x∈exteriorWeightedPart w d) :
    finiteExteriorCoefficientEquiv (ι := ι) e x∈exteriorWeightedPart w d := by
  letI := exteriorWeightedGrading (A := B) w
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨T,hT,rfl⟩ := hx
      rw [←hT,Module.Basis.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
      have hs : (T.sort.map w).sum=exteriorWordDegree w T := by
        simpa only [exteriorWordDegree,Finset.sort_toFinset] using
          (List.sum_toFinset w (Finset.sort_nodup T (· ≤ ·))).symm
      have hbase (i : ι) : (ExteriorAlgebra.ι A) ((Pi.basisFun A ι) i)=
          exteriorGenerator (A := A) i := by
        unfold exteriorGenerator
        apply congrArg (ExteriorAlgebra.ι A)
        funext j
        by_cases hij : i=j
        · subst j
          simp [Pi.basisFun_apply]
        · simp [Pi.basisFun_apply,Pi.single_apply,hij,Ne.symm hij]
      have hgen (i : ι) : finiteExteriorCoefficientEquiv (ι := ι) e
          ((ExteriorAlgebra.ι A) ((Pi.basisFun A ι) i))=
          exteriorGenerator (A := B) i := by
        rw [hbase]
        exact finiteExteriorCoefficientEquiv_generator e i
      have h := graded_list_prod_mem (exteriorWeightedPart (A := B) w)
        w (fun i ↦ exteriorGenerator (A := B) i) (exteriorGenerator_weighted_mem w) T.sort
      simpa only [List.map_map,Function.comp_def,hgen,hs] using h
  | zero => simpa only [map_zero] using (exteriorWeightedPart (A := B) w d).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [finiteExteriorCoefficientEquiv_smul]
      exact Submodule.smul_mem _ _ ih

theorem exteriorWeighted_coefficient_map_iff (w : ι → Γ) (e : A ≃ₐ[F] B)
    (d : Γ) (x : ExteriorAlgebra A (ι → A)) :
    finiteExteriorCoefficientEquiv (ι := ι) e x∈exteriorWeightedPart w d ↔
      x∈exteriorWeightedPart w d := by
  constructor
  · intro hx
    have h := exteriorWeighted_coefficient_map_mem w e.symm hx
    rw [←finiteExteriorCoefficientEquiv_symm,AlgEquiv.symm_apply_apply] at h
    exact h
  · exact exteriorWeighted_coefficient_map_mem w e

end Coefficients

section Separated

variable {A ι : Type*} [CommRing A] [Fintype ι] [LinearOrder (ι⊕ι)]

theorem separatedOddCurrent_bidegree (node beta a b : ι → A)
    (family : LocalOddFamily) (k : ℕ) :
    separatedOddCurrent node beta a b family k∈
      exteriorBigradedPart (oddFamilyBidegree family) := by
  letI := exteriorWeightedGrading (A := A) (oddBidegree (ι := ι))
  have ht (i : ι) : clusterTheta (A := A) i∈exteriorBigradedPart (1,0) :=
    exteriorGenerator_weighted_mem oddBidegree (Sum.inl i)
  have hx (i : ι) : clusterXi (A := A) i∈exteriorBigradedPart (0,1) :=
    exteriorGenerator_weighted_mem oddBidegree (Sum.inr i)
  cases family
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (ht i))
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hx i))
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (SetLike.mul_mem_graded (ht i) (hx i))

def separatedOddBigradedPart (node beta a b : ι → A) :
    ℕ×ℕ → Submodule A (SeparatedOddQuotient node beta a b) :=
  gradedImagePart exteriorBigradedPart ((separatedOddIdeal node beta a b).ringCon.mkₐ A)

def separatedOddBigrading (node beta a b : ι → A) :
    GradedAlgebra (separatedOddBigradedPart node beta a b) := by
  letI := exteriorWeightedGrading (A := A) (oddBidegree (ι := ι))
  exact multihomogeneousTwoSidedQuotientGrading exteriorBigradedPart
    (Set.range fun p : LocalOddFamily×ℕ ↦ separatedOddCurrent node beta a b p.1 p.2) (by
      rintro g ⟨⟨family,k⟩,rfl⟩
      exact ⟨oddFamilyBidegree family,separatedOddCurrent_bidegree node beta a b family k⟩)

end Separated

end PaperVerification.Fermion

