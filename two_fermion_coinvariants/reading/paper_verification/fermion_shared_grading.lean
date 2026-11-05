module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import PaperVerification.FermionTensorQuotient
public import PaperVerification.FermionExteriorWordGrading

set_option maxErrors 40
set_option Elab.async false

section BatchFile_0
/- Literal source: PaperVerification/FermionGradedQuotient.lean -/


/-!
# Grading an actual surjective algebra image

A homogeneous kernel descends the direct-sum decomposition. The construction
uses the actual image submodules under a surjective algebra map, including
noncommutative algebra quotients. It introduces no assumed decomposition of
the target and no assumption of flatness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open DirectSum
variable {R A B Γ : Type*} [AddMonoid Γ] [DecidableEq Γ] [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (part : Γ → Submodule R A) [GradedAlgebra part] (q : A →ₐ[R] B)

def gradedImagePart (n : Γ) : Submodule R B := (part n).map q.toLinearMap

def gradedImageComponent (n : Γ) :
    part n →ₗ[R] gradedImagePart part q n :=
  (q.toLinearMap.comp (part n).subtype).codRestrict _
    (fun a ↦ ⟨a,a.property,rfl⟩)

def gradedImageDecomposeSource :
    A →ₗ[R] ⨁ n,gradedImagePart part q n :=
  (DirectSum.lmap (gradedImageComponent part q)).comp
    (DirectSum.decomposeLinearEquiv part).toLinearMap

@[simp] theorem gradedImageDecomposeSource_coe (n : Γ) (a : part n) :
    gradedImageDecomposeSource part q (a : A)=
      DirectSum.lof R Γ (gradedImagePart part q ·) n
        (gradedImageComponent part q n a) := by
  simp only [gradedImageDecomposeSource,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,DirectSum.decomposeLinearEquiv_apply_coe,DirectSum.lmap_lof]

theorem gradedImageDecomposeSource_recompose (a : A) :
    DirectSum.coeLinearMap (gradedImagePart part q)
      (gradedImageDecomposeSource part q a)=q a := by
  have hcomm :
      (DirectSum.coeLinearMap (gradedImagePart part q)).comp
        (DirectSum.lmap (gradedImageComponent part q)) =
      q.toLinearMap.comp (DirectSum.coeLinearMap part) := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply,DirectSum.lmap_lof,DirectSum.coeLinearMap_lof]
    rfl
  change ((DirectSum.coeLinearMap (gradedImagePart part q)).comp
    (DirectSum.lmap (gradedImageComponent part q)))
      (DirectSum.decomposeLinearEquiv part a)=_
  rw [hcomm]
  change q ((DirectSum.decomposeLinearEquiv part).symm
    (DirectSum.decomposeLinearEquiv part a))=q a
  rw [LinearEquiv.symm_apply_apply]

variable (hq : Function.Surjective q)
variable (hker : ∀ n a,q a=0 → q (GradedAlgebra.proj part n a)=0)

include hker in
theorem gradedImageDecomposeSource_ker :
    LinearMap.ker q.toLinearMap ≤ LinearMap.ker (gradedImageDecomposeSource part q) := by
  intro a ha
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  change q (GradedAlgebra.proj part n a)=0
  exact hker n a ha

set_option maxHeartbeats 800000 in
def gradedImageDecompose (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    B →ₗ[R] ⨁ n, gradedImagePart part q n := by
  let descended : (A ⧸ LinearMap.ker q.toLinearMap) →ₗ[R]
      (⨁ n, gradedImagePart part q n) :=
    (LinearMap.ker q.toLinearMap).liftQ
      (R₂ := R) (M₂ := ⨁ n, gradedImagePart part q n) (τ₁₂ := RingHom.id R)
      (gradedImageDecomposeSource part q)
      (gradedImageDecomposeSource_ker part q hker)
  let quotientEquiv : (A ⧸ LinearMap.ker q.toLinearMap) ≃ₗ[R] B :=
    q.toLinearMap.quotKerEquivOfSurjective hq
  exact descended.comp quotientEquiv.symm.toLinearMap

@[simp] theorem gradedImageDecompose_q (a : A) :
    gradedImageDecompose part q hq hker (q a)=gradedImageDecomposeSource part q a := by
  simp only [gradedImageDecompose,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap]
  have he : (q.toLinearMap.quotKerEquivOfSurjective hq).symm (q a) =
      Submodule.Quotient.mk a :=
    LinearMap.quotKerEquivOfSurjective_symm_apply q.toLinearMap hq a
  rw [he,Submodule.liftQ_apply]

def gradedImageDecomposition (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    DirectSum.Decomposition (gradedImagePart part q) := by
  exact DirectSum.Decomposition.ofLinearMap (gradedImagePart part q)
    (gradedImageDecompose part q hq hker)
    (by
      apply LinearMap.ext
      intro b
      obtain ⟨a,rfl⟩ := hq b
      simp only [LinearMap.comp_apply,gradedImageDecompose_q,
        gradedImageDecomposeSource_recompose,LinearMap.id_apply])
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      rintro ⟨b,hb⟩
      obtain ⟨a,ha,rfl⟩ := hb
      simp only [LinearMap.comp_apply,DirectSum.coeLinearMap_lof,LinearMap.id_apply]
      change gradedImageDecompose part q hq hker (q a) =
        DirectSum.lof R Γ (gradedImagePart part q ·) n
          (gradedImageComponent part q n ⟨a,ha⟩)
      rw [gradedImageDecompose_q]
      exact gradedImageDecomposeSource_coe part q n ⟨a,ha⟩)

instance gradedImageGradedMonoid :
    SetLike.GradedMonoid (gradedImagePart part q) where
  one_mem := ⟨1,SetLike.one_mem_graded part,map_one q⟩
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨y,hy,rfl⟩ := hb
    exact ⟨x*y,SetLike.mul_mem_graded hx hy,map_mul q x y⟩

/-- The image grading is genuine: multiplication and the unique direct-sum
decomposition are both constructed from the source grading. -/
def gradedImageAlgebra (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    GradedAlgebra (gradedImagePart part q) where
  toGradedMonoid := gradedImageGradedMonoid part q
  toDecomposition := gradedImageDecomposition part q hq hker

section RestrictScalars

variable {S C : Type*} [CommRing S] [Ring C] [Algebra R S]
  [Algebra S C] [Algebra R C] [IsScalarTower R S C]
variable (piece : Γ → Submodule S C) [GradedAlgebra piece]

def restrictGradedPart (n : Γ) : Submodule R C := (piece n).restrictScalars R

/-- Restricting the coefficient ring leaves the actual homogeneous subspaces
and their unique additive decomposition unchanged. -/
def restrictGradedAlgebra : GradedAlgebra (restrictGradedPart (R := R) piece) :=
  inferInstanceAs (GradedAlgebra (fun n ↦ (piece n).restrictScalars R))

end RestrictScalars

end PaperVerification.Fermion
end
end
end BatchFile_0

run_cmd Lean.logInfo "BATCH_SOURCE_END: PaperVerification/FermionGradedQuotient.lean"
section BatchFile_1
/- Literal source: PaperVerification/FermionMultihomogeneousTwoSided.lean -/


/-!
# Homogeneous two-sided ideals for arbitrary additive degree indices

UNCOMPILED CANDIDATE.
The finite double decomposition proof applies in particular to the actual
exterior bidegree N × N, without reducing it to total degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PaperVerification.Fermion

variable {R A Γ : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddMonoid Γ] [DecidableEq Γ]
variable (part : Γ → Submodule R A) [GradedAlgebra part]

theorem homogeneousIdeal_component_mul_left (I : TwoSidedIdeal A) (a b : A)
    (ha : ∀ j,GradedAlgebra.proj part j a∈I) (n : Γ) :
    GradedAlgebra.proj part n (b*a)∈I := by
  classical
  rw [←DirectSum.sum_support_decompose part b,←DirectSum.sum_support_decompose part a]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply sum_mem
  intro j hj
  apply sum_mem
  intro i hi
  have hp : (DirectSum.decompose part b i : A)*(DirectSum.decompose part a j : A)
      ∈part (i+j) := SetLike.mul_mem_graded
        (DirectSum.decompose part b i).property (DirectSum.decompose part a j).property
  by_cases hn : i+j=n
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_same part (hn ▸ hp)]
    exact I.mul_mem_left _ _ (ha j)
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_ne part hp hn]
    exact I.zero_mem

theorem homogeneousIdeal_component_mul_right (I : TwoSidedIdeal A) (a b : A)
    (ha : ∀ j,GradedAlgebra.proj part j a∈I) (n : Γ) :
    GradedAlgebra.proj part n (a*b)∈I := by
  classical
  rw [←DirectSum.sum_support_decompose part a,←DirectSum.sum_support_decompose part b]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply sum_mem
  intro j hj
  apply sum_mem
  intro i hi
  have hp : (DirectSum.decompose part a i : A)*(DirectSum.decompose part b j : A)
      ∈part (i+j) := SetLike.mul_mem_graded
        (DirectSum.decompose part a i).property (DirectSum.decompose part b j).property
  by_cases hn : i+j=n
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_same part (hn ▸ hp)]
    exact I.mul_mem_right _ _ (ha i)
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_ne part hp hn]
    exact I.zero_mem

theorem twoSided_span_multihomogeneous (generators : Set A)
    (hgen : ∀ g∈generators,∃ n,g∈part n) :
    ∀ a∈TwoSidedIdeal.span generators,∀ n,
      GradedAlgebra.proj part n a∈TwoSidedIdeal.span generators := by
  intro a ha
  induction ha using TwoSidedIdeal.span_induction with
  | mem g hg =>
      obtain ⟨i,hi⟩ := hgen g hg
      intro n
      by_cases hn : i=n
      · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_same part (hn ▸ hi)]
        exact TwoSidedIdeal.subset_span hg
      · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_ne part hi hn]
        exact TwoSidedIdeal.zero_mem _
  | zero =>
      intro n
      simpa only [map_zero] using (TwoSidedIdeal.span generators).zero_mem
  | add a b ha hb iha ihb =>
      intro n
      rw [map_add]
      exact (TwoSidedIdeal.span generators).add_mem (iha n) (ihb n)
  | neg a ha iha =>
      intro n
      rw [map_neg]
      exact (TwoSidedIdeal.span generators).neg_mem (iha n)
  | left_absorb b a ha iha =>
      exact homogeneousIdeal_component_mul_left part _ a b iha
  | right_absorb b a ha iha =>
      exact homogeneousIdeal_component_mul_right part _ a b iha

def multihomogeneousTwoSidedQuotientGrading (generators : Set A)
    (hgen : ∀ g∈generators,∃ n,g∈part n) :
    GradedAlgebra
      (gradedImagePart part ((TwoSidedIdeal.span generators).ringCon.mkₐ R)) :=
  gradedImageAlgebra part ((TwoSidedIdeal.span generators).ringCon.mkₐ R)
    (RingCon.mkₐ_surjective (α := R) _) (by
      intro n a ha
      have hamem : a∈TwoSidedIdeal.span generators := by
        change ((a : A) : (TwoSidedIdeal.span generators).ringCon.Quotient)=
          ((0 : A) : (TwoSidedIdeal.span generators).ringCon.Quotient) at ha
        exact Quotient.exact ha
      exact quotientMk_eq_zero_of_mem _ _
        (twoSided_span_multihomogeneous part generators hgen a hamem n))

end PaperVerification.Fermion

end
end
end BatchFile_1

run_cmd Lean.logInfo "BATCH_SOURCE_END: PaperVerification/FermionMultihomogeneousTwoSided.lean"
section BatchFile_2
/- Literal source: PaperVerification/FermionExteriorWordMaps.lean -/


/-!
# Exterior word maps preserve their original weighted degrees

UNCOMPILED CANDIDATE. Extracted without mathematical changes from
FermionExteriorGradedMaps; no local-coordinate or coefficient-transport
construction is needed for these statements.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section WordMaps

variable {A B ι Γ : Type*} [CommRing A] [Ring B]
  [Algebra A B] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]

theorem graded_list_prod_mem (part : Γ → Submodule A B)
    [GradedAlgebra part] (w : ι → Γ) (g : ι → B)
    (hg : ∀ i,g i∈part (w i)) (l : List ι) :
    (l.map g).prod∈part (l.map w).sum := by
  induction l with
  | nil => simpa only [List.map_nil,List.prod_nil,List.sum_nil] using
      (SetLike.one_mem_graded part)
  | cons i l ih =>
      simpa only [List.map_cons,List.prod_cons,List.sum_cons] using
        SetLike.mul_mem_graded (hg i) ih

theorem exteriorWeighted_map_mem
    (w : ι → Γ) (part : Γ → Submodule A B) [GradedAlgebra part]
    (f : ExteriorAlgebra A (ι → A) →ₐ[A] B)
    (hg : ∀ i,f (exteriorGenerator i)∈part (w i))
    {d : Γ} {x : ExteriorAlgebra A (ι → A)}
    (hx : x∈exteriorWeightedPart w d) : f x∈part d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨T,hT,rfl⟩ := hx
      rw [←hT,Module.Basis.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
      have hs : (T.sort.map w).sum=exteriorWordDegree w T := by
        simpa only [Finset.sort_toFinset,exteriorWordDegree] using
          (List.sum_toFinset w (Finset.sort_nodup T (· ≤ ·))).symm
      have hgen (i : ι) : ExteriorAlgebra.ι A ((Pi.basisFun A ι) i)=
          exteriorGenerator i := by
        unfold exteriorGenerator
        apply congrArg (ExteriorAlgebra.ι A)
        funext j
        by_cases hji : j=i
        · subst j
          simp only [Pi.basisFun_apply,Pi.single_eq_same]
        · simp only [Pi.basisFun_apply,Pi.single_apply,hji,ite_false]
      have h := graded_list_prod_mem part w (fun i ↦ f (exteriorGenerator i)) hg T.sort
      simpa only [List.map_map,Function.comp_def,hgen,hs] using h
  | zero => simpa only [map_zero] using (part d).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ a ih

end WordMaps

section Diagonal

variable {A ι Γ : Type*} [CommRing A] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]

theorem exteriorDiagonalUnitEquiv_weighted_mem (w : ι → Γ) (units : ι → Aˣ)
    {d : Γ} {x : ExteriorAlgebra A (ι → A)}
    (hx : x∈exteriorWeightedPart w d) :
    exteriorDiagonalUnitEquiv units x∈exteriorWeightedPart w d := by
  letI := exteriorWeightedGrading (A := A) w
  exact exteriorWeighted_map_mem w (exteriorWeightedPart w)
    (exteriorDiagonalUnitEquiv units).toAlgHom
    (fun i ↦ by
      change exteriorDiagonalUnitEquiv units (exteriorGenerator i)∈exteriorWeightedPart w (w i)
      rw [exteriorDiagonalUnitEquiv_generator]
      exact Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem w i)) hx

theorem exteriorDiagonalUnitEquiv_symm_weighted_mem (w : ι → Γ) (units : ι → Aˣ)
    {d : Γ} {x : ExteriorAlgebra A (ι → A)}
    (hx : x∈exteriorWeightedPart w d) :
    (exteriorDiagonalUnitEquiv units).symm x∈exteriorWeightedPart w d := by
  letI := exteriorWeightedGrading (A := A) w
  exact exteriorWeighted_map_mem w (exteriorWeightedPart w)
    (exteriorDiagonalUnitEquiv units).symm.toAlgHom
    (fun i ↦ by
      change (exteriorDiagonalUnitEquiv units).symm (exteriorGenerator i)∈exteriorWeightedPart w (w i)
      rw [exteriorDiagonalUnitEquiv_symm_generator]
      exact Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem w i)) hx

end Diagonal

end PaperVerification.Fermion
end
end
end BatchFile_2

run_cmd Lean.logInfo "BATCH_SOURCE_END: PaperVerification/FermionExteriorWordMaps.lean"
