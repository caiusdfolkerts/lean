module

public import PaperVerification.AlternatingFormsBasisDegree
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Coordinate support of a diagonal eigenspace

If a linear endomorphism acts diagonally on a genuine basis, with distinct
eigenvalues assigned to the natural-number degrees, its eigenspaces are
exactly the subspaces supported in those degrees.  The index set of the
basis can be infinite; no finite-dimensionality assumption is introduced.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.EigenBasisGrading

open AlternatingForms.BasisDegree

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  (B : Module.Basis I K V) (δ : I → ℕ) (eigenScalar : ℕ → K)
  (F : V →ₗ[K] V) (hF : ∀ i,F (B i)=eigenScalar (δ i) • B i)

include hF in
theorem coordinate_map (i : I) (x : V) :
    B.repr (F x) i=eigenScalar (δ i)*B.repr x i := by
  have h : (B.coord i).comp F=eigenScalar (δ i) • B.coord i := by
    apply B.ext
    intro j
    simp only [LinearMap.comp_apply,hF,map_smul,LinearMap.smul_apply,
      Module.Basis.coord_apply,Module.Basis.repr_self]
    classical
    by_cases hji : j=i
    · subst j
      simp
    · simp [Finsupp.single_apply,hji,Ne.symm hji]
  exact LinearMap.congr_fun h x

include hF in
theorem eigenvector_iff_degree_support (hEigen : Function.Injective eigenScalar)
    (d : ℕ) (x : V) :
    F x=eigenScalar d • x ↔ x∈piece B δ d := by
  rw [mem_piece]
  constructor
  · intro hx i hi
    by_contra hc
    have he := congrArg (fun y => B.repr y i) hx
    rw [coordinate_map B δ eigenScalar F hF,map_smul,Finsupp.smul_apply,smul_eq_mul] at he
    exact hi (hEigen (mul_right_cancel₀ hc he))
  · intro hx
    apply B.repr.injective
    apply Finsupp.ext
    intro i
    rw [coordinate_map B δ eigenScalar F hF,map_smul,Finsupp.smul_apply,smul_eq_mul]
    by_cases hi : δ i=d
    · rw [hi]
    · rw [hx i hi,mul_zero,mul_zero]

include hF in
theorem eigenspace_eq_piece (hEigen : Function.Injective eigenScalar) (d : ℕ) :
    Module.End.eigenspace F (eigenScalar d)=piece B δ d := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  exact eigenvector_iff_degree_support B δ eigenScalar F hF hEigen d x

theorem span_degree_eq_piece (d : ℕ) :
    Submodule.span K (Set.range (fun i : {i // δ i=d} => B i))=piece B δ d := by
  rw [piece_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

/-- Restricting a genuine basis gives a basis of every exact degree piece. -/
def degreeBasis (d : ℕ) : Module.Basis {i // δ i=d} K (piece B δ d) :=
  (Module.Basis.span (B.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_eq_piece B δ d))

theorem finrank_piece (d : ℕ) :
    Module.finrank K (piece B δ d)=Nat.card {i // δ i=d} :=
  Module.finrank_eq_nat_card_basis (degreeBasis B δ d)

end PaperVerification.EigenBasisGrading
