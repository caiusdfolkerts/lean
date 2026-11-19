module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The genuine internal grading determined by degrees of basis vectors

The pieces are defined by literal coordinate support.  Their direct-sum
property and their equality with spans of the corresponding basis vectors
are proved; no decomposition assumption is supplied by an application.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BasisDegree

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (B : Module.Basis I R V) (δ : I → ℕ)

def piece (N : ℕ) : Submodule R V :=
  (Finsupp.supported R R {i | δ i=N}).comap B.repr.toLinearMap

theorem mem_piece (N : ℕ) (x : V) :
    x∈piece B δ N ↔ ∀ i,δ i≠N → B.repr x i=0 :=
  Finsupp.mem_supported' R (B.repr x)

theorem basis_mem_piece (i : I) : B i∈piece B δ (δ i) := by
  rw [mem_piece]
  intro j hj
  rw [Module.Basis.repr_self]
  exact Finsupp.single_eq_of_ne (fun hji ↦ hj (congrArg δ hji))

theorem piece_iSupIndep : iSupIndep (piece B δ) := by
  intro N
  rw [Submodule.disjoint_def]
  intro x hx hother
  apply B.repr.injective
  rw [map_zero]
  apply Finsupp.ext
  intro i
  change B.repr x i=0
  by_cases hi : δ i=N
  · have hle : (⨆ M≠N,piece B δ M)≤(B.coord i).ker := by
      apply iSup_le
      intro M
      apply iSup_le
      intro hMN
      intro y hy
      exact LinearMap.mem_ker.mpr ((mem_piece B δ M y).mp hy i
        (by rw [hi]; exact Ne.symm hMN))
    exact LinearMap.mem_ker.mp (hle hother)
  · exact (mem_piece B δ N x).mp hx i hi

theorem piece_iSup : (⨆ N,piece B δ N)=⊤ := by
  apply top_unique
  rw [←B.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact (le_iSup (piece B δ) (δ i)) (basis_mem_piece B δ i)

def grading : TauCeti.InternalGrading R V ℕ where
  piece := piece B δ
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (piece_iSupIndep B δ) (piece_iSup B δ)

theorem piece_eq_span (N : ℕ) :
    piece B δ N=Submodule.span R (B '' {i | δ i=N}) := by
  apply le_antisymm
  · intro x hx
    rw [←B.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    by_cases h : δ i=N
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,h,rfl⟩)
    · rw [(mem_piece B δ N x).mp hx i h,zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    rw [←hi]
    exact basis_mem_piece B δ i

end PaperVerification.AlternatingForms.BasisDegree
