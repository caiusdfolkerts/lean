module

public import PaperVerification.FermionDescendingAssociatedGraded
public import PaperVerification.FermionHomogeneousDecomposition
public import PaperVerification.FermionBlockNormalForm
public import PaperVerification.FermionWeightReesFibers
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual descending graded pieces and the zero-weight product

The source is the direct sum of the actual quotients F_d/F_(d+1). Component
projection identifies each quotient with its homogeneous basis submodule.
The resulting algebra comparison retains exactly the structure constants
whose weight is the sum of the input weights. These are proved conditions,
not definitions of either the original or target algebra.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators DirectSum

namespace PaperVerification.Fermion.DescendingBasis

open BasisFiltered DescendingAlgebra

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
  (b : Module.Basis I K A) (w : I → ℕ) (hmul : WeightRees.Multiplicative b w)

include hmul in
/-- The actual basis tail is multiplicative in the original algebra. -/
theorem tail_mul {d e : ℕ} {x y : A}
    (hx : x∈BlockInitial.lowerSubmodule b w d)
    (hy : y∈BlockInitial.lowerSubmodule b w e) :
    x*y∈BlockInitial.lowerSubmodule b w (d+e) := by
  rw [←b.sum_repr x,←b.sum_repr y,Finset.sum_mul]
  apply Submodule.sum_mem
  intro i hi
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  intro j hj
  by_cases hxi : b.repr x i=0
  · simp only [hxi,zero_smul,zero_mul]
    exact Submodule.zero_mem _
  by_cases hyj : b.repr y j=0
  · simp only [hyj,zero_smul,mul_zero]
    exact Submodule.zero_mem _
  rw [smul_mul_smul_comm]
  apply Submodule.smul_mem
  intro k hk
  exact (Nat.add_le_add (hx i hxi) (hy j hyj)).trans (hmul i j k hk)

/-- No quotient or candidate initial algebra occurs in this filtration. -/
def filtration : DescendingAlgebra.Filtration K A where
  piece := BlockInitial.lowerSubmodule b w
  antitone := fun d e h x hx i hi ↦ h.trans (hx i hi)
  one_mem := fun i hi ↦ Nat.zero_le _
  mul_mem := tail_mul b w hmul

/-- Project an actual filtered element to its degree-d basis component. -/
def componentMap (d : ℕ) :
    (filtration b w hmul).piece d →ₗ[K] homogeneousPiece b w d where
  toFun x := ⟨component b w d x,homogeneous_component b w d x⟩
  map_add' x y := Subtype.ext ((component b w d).map_add x y)
  map_smul' r x := Subtype.ext ((component b w d).map_smul r x)

/-- The kernel is exactly the next filtration step, not a presumed initial ideal. -/
theorem componentMap_ker (d : ℕ) :
    LinearMap.ker (componentMap b w hmul d)=
      nextRestricted (filtration b w hmul) d := by
  ext x
  rw [LinearMap.mem_ker]
  change componentMap b w hmul d x=0 ↔
    BlockInitial.LowerBound b w (d+1) (x : A)
  constructor
  · intro hz i hi
    have hd := x.property i hi
    have hne : w i≠d := by
      intro he
      have h := congrArg (fun z : homogeneousPiece b w d ↦ b.repr z i) hz
      change b.repr (component b w d x) i=b.repr 0 i at h
      rw [repr_component,if_pos he,map_zero,Finsupp.zero_apply] at h
      exact hi h
    omega
  · intro hx
    apply Subtype.ext
    apply b.repr.injective
    ext i
    change b.repr (component b w d x) i=b.repr 0 i
    rw [repr_component,map_zero,Finsupp.zero_apply]
    by_cases he : w i=d
    · rw [if_pos he]
      by_contra hi
      have h := hx i hi
      omega
    · rw [if_neg he]

theorem componentMap_surjective (d : ℕ) :
    Function.Surjective (componentMap b w hmul d) := by
  intro y
  have hy : (y : A)∈(filtration b w hmul).piece d :=
    fun i hi ↦ (y.property i hi).ge
  refine ⟨⟨y,hy⟩,?_⟩
  apply Subtype.ext
  change component b w d y=y
  rw [component_of_homogeneous b w y.property,if_pos rfl]

/-- The degree-piece comparison is the first isomorphism theorem for the
actual component map, with its kernel proved above. -/
def pieceEquiv (d : ℕ) :
    GradedPiece (filtration b w hmul) d ≃ₗ[K] homogeneousPiece b w d :=
  (Submodule.quotEquivOfEq _ _ (componentMap_ker b w hmul d).symm).trans
    ((componentMap b w hmul d).quotKerEquivOfSurjective
      (componentMap_surjective b w hmul d))

@[simp] theorem pieceEquiv_mk (d : ℕ) (x : (filtration b w hmul).piece d) :
    (pieceEquiv b w hmul d (Submodule.Quotient.mk x) : A)=component b w d x := by
  simp only [pieceEquiv,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The ungraded module is the internal sum of its actual basis components. -/
theorem homogeneous_internal : DirectSum.IsInternal (homogeneousPiece b w) := by
  have h := BasisFiltered.homogeneousQuotient_isInternal b w
    (LinearMap.id : A →ₗ[K] A) b b w
    (fun i ↦ homogeneous_basis b w i) (fun i ↦ rfl)
    (fun d x hx ↦ by
      have hx0 : x=0 := hx
      subst x
      simp only [map_zero,Submodule.zero_mem])
  simpa only [Submodule.map_id] using h

/-- Every actual graded piece is retained, including every zero piece. -/
def totalEquiv : AssociatedGraded (filtration b w hmul) ≃ₗ[K] A :=
  (DirectSum.congrLinearEquiv (pieceEquiv b w hmul)).trans
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (homogeneousPiece b w))
      (homogeneous_internal b w))

@[simp] theorem totalEquiv_of_mk (d : ℕ) (x : (filtration b w hmul).piece d) :
    totalEquiv b w hmul
      (DirectSum.of (GradedPiece (filtration b w hmul)) d (Submodule.Quotient.mk x))=
      component b w d x := by
  change DirectSum.coeLinearMap (homogeneousPiece b w)
    (DirectSum.lmap (fun k ↦ (pieceEquiv b w hmul k).toLinearMap)
      (DirectSum.of (GradedPiece (filtration b w hmul)) d (Submodule.Quotient.mk x)))=_
  rw [DirectSum.lmap_of,DirectSum.coeLinearMap_of]
  exact pieceEquiv_mk b w hmul d x

theorem basis_mem_tail (i : I) : b i∈(filtration b w hmul).piece (w i) := by
  change BlockInitial.LowerBound b w (w i) (b i)
  simpa only [one_smul] using BlockInitial.lowerBound_single (b := b) (weight := w) i (1 : K)

@[simp] theorem totalEquiv_symm_basis (i : I) :
    (totalEquiv b w hmul).symm (b i)=
      DirectSum.of (GradedPiece (filtration b w hmul)) (w i)
        (Submodule.Quotient.mk ⟨b i,basis_mem_tail b w hmul i⟩) := by
  apply (totalEquiv b w hmul).injective
  rw [LinearEquiv.apply_symm_apply,totalEquiv_of_mk,
    component_of_homogeneous b w (homogeneous_basis b w i),if_pos rfl]

/-- An actual basis of the direct sum of filtration quotients. -/
def gradedBasis : Module.Basis I K (AssociatedGraded (filtration b w hmul)) :=
  b.map (totalEquiv b w hmul).symm

@[simp] theorem gradedBasis_apply (i : I) :
    gradedBasis b w hmul i=
      DirectSum.of (GradedPiece (filtration b w hmul)) (w i)
        (Submodule.Quotient.mk ⟨b i,basis_mem_tail b w hmul i⟩) := by
  rw [gradedBasis,Module.Basis.map_apply,totalEquiv_symm_basis]

section Target

variable {B : Type*} [Ring B] [Algebra K B] (c : Module.Basis I K B)

def comparison : AssociatedGraded (filtration b w hmul) ≃ₗ[K] B :=
  (totalEquiv b w hmul).trans (b.equiv c (Equiv.refl I))

@[simp] theorem comparison_basis (i : I) :
    comparison b w hmul c (gradedBasis b w hmul i)=c i := by
  simp only [comparison,gradedBasis,Module.Basis.map_apply,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply,Module.Basis.equiv_apply,Equiv.refl_apply]

theorem equiv_component (d : ℕ) (x : A) :
    b.equiv c (Equiv.refl I) (component b w d x)=
      ∑ i,if w i=d then b.repr x i • c i else 0 := by
  rw [←b.sum_repr (component b w d x),map_sum]
  simp only [map_smul,Module.Basis.equiv_apply,Equiv.refl_apply,repr_component]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp only [zero_smul]

theorem comparison_one
    (hone : (1 : B)=∑ i,if w i=0 then b.repr 1 i • c i else 0) :
    comparison b w hmul c 1=1 := by
  rw [←associatedGraded_of_gradedOne,gradedOne_def]
  change b.equiv c (Equiv.refl I)
    (totalEquiv b w hmul
      (DirectSum.of (GradedPiece (filtration b w hmul)) 0
        (Submodule.Quotient.mk ⟨1,one_mem_filtration _⟩)))=1
  rw [totalEquiv_of_mk,equiv_component]
  exact hone.symm

theorem comparison_basis_mul
    (hprod : ∀ i j,c i*c j=∑ k,
      if w k=w i+w j then b.repr (b i*b j) k • c k else 0) (i j : I) :
    comparison b w hmul c (gradedBasis b w hmul i*gradedBasis b w hmul j)=c i*c j := by
  rw [gradedBasis_apply,gradedBasis_apply,associatedGraded_of_mul_of,gradedMul_apply_mk]
  change b.equiv c (Equiv.refl I)
    (totalEquiv b w hmul
      (DirectSum.of (GradedPiece (filtration b w hmul)) (w i+w j)
        (Submodule.Quotient.mk ⟨b i*b j,_⟩)))=c i*c j
  rw [totalEquiv_of_mk,equiv_component]
  exact (hprod i j).symm

theorem comparison_mul
    (hprod : ∀ i j,c i*c j=∑ k,
      if w k=w i+w j then b.repr (b i*b j) k • c k else 0)
    (x y : AssociatedGraded (filtration b w hmul)) :
    comparison b w hmul c (x*y)=comparison b w hmul c x*comparison b w hmul c y := by
  let E := comparison b w hmul c
  let B := gradedBasis b w hmul
  have hgen (i j : I) : E (B i*B j)=E (B i)*E (B j) := by
    simpa only [E,B,comparison_basis] using comparison_basis_mul b w hmul c hprod i j
  have hx := B.mem_span x
  have hy := B.mem_span y
  have hright (i : I) : E (B i*y)=E (B i)*E y := by
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨j,rfl⟩ := hz; exact hgen i j
    | zero => simp only [mul_zero,map_zero]
    | add z t hz ht ihz iht => simp only [mul_add,map_add,ihz,iht]
    | smul r z hz ih => simp only [mul_smul_comm,map_smul,ih]
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨i,rfl⟩ := hz; exact hright i
  | zero => simp only [zero_mul,map_zero]
  | add z t hz ht ihz iht => simp only [add_mul,map_add,ihz,iht]
  | smul r z hz ih =>
      change E ((r • z)*y)=E (r • z)*E y
      calc
        E ((r • z)*y)=E (r • (z*y)) :=
          congrArg E (Algebra.smul_mul_assoc r z y)
        _=r • E (z*y) := E.map_smul r (z*y)
        _=r • (E z*E y) := congrArg (fun t ↦ r • t) ih
        _=E (r • z)*E y := by
          rw [E.map_smul]
          exact (Algebra.smul_mul_assoc r (E z) (E y)).symm

/-- An algebra equivalence from the independently constructed associated
graded, once the target's actual unit and products have been proved. -/
def comparisonAlgEquiv
    (hone : (1 : B)=∑ i,if w i=0 then b.repr 1 i • c i else 0)
    (hprod : ∀ i j,c i*c j=∑ k,
      if w k=w i+w j then b.repr (b i*b j) k • c k else 0) :
    AssociatedGraded (filtration b w hmul) ≃ₐ[K] B :=
  AlgEquiv.ofLinearEquiv (comparison b w hmul c)
    (comparison_one b w hmul c hone) (comparison_mul b w hmul c hprod)

end Target
end PaperVerification.Fermion.DescendingBasis
