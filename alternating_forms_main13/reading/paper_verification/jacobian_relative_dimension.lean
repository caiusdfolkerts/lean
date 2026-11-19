module

public import TauCeti.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.Locally

/-!
# The relative dimension of a quotient with independent Jacobian rows

The minors used here belong to the original polynomial presentation. Inverting
one such minor gives a standard smooth presentation with exactly the expected
number of free coordinates. Independence over every maximal residue field makes
these principal opens cover the entire spectrum, including nonreduced bases.
-/

@[expose] public section
noncomputable section

universe u v w
open Algebra MvPolynomial
open scoped Matrix

namespace PaperVerification.JacobianRelativeDimension

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

/-- Localizing the chosen Jacobian minor turns the original presentation into a
standard smooth presentation of its original dimension. -/
theorem standardSmooth_away_jacobian (P : PreSubmersivePresentation R S ι κ) :
    IsStandardSmoothOfRelativeDimension (Fintype.card ι - Fintype.card κ)
      R (Localization.Away P.jacobian) := by
  classical
  let T := Localization.Away P.jacobian
  let Q := PreSubmersivePresentation.localizationAway T P.jacobian
  have hunit : IsUnit ((Q.comp P).jacobian) := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
      (by simpa only [Q, PreSubmersivePresentation.localizationAway_jacobian] using
        (IsLocalization.Away.algebraMap_isUnit P.jacobian :
          IsUnit (algebraMap S T P.jacobian)))
  let E : SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ κ) :=
    { Q.comp P with jacobian_isUnit := hunit }
  apply E.isStandardSmoothOfRelativeDimension
  change (Q.comp P).dimension = _
  rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Q, Presentation.dimension, Nat.card_eq_fintype_card]

/-- The maximal minors generate the unit ideal when the rows are independent in
every maximal residue field. -/
theorem span_maximalMinors_eq_top [DecidableEq κ] (A : Matrix κ ι S)
    (hA : ∀ (J : Ideal S) [J.IsMaximal],
      LinearIndependent (S ⧸ J) (A.map (Ideal.Quotient.mk J))) :
    Ideal.span (Set.range (fun e : κ ↪ ι ↦ (A.submatrix id e).det)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ h
  letI : J.IsMaximal := hJ
  letI : Field (S ⧸ J) := Ideal.Quotient.field J
  obtain ⟨e, he⟩ := Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero.mp (hA J)
  have hmem : (A.submatrix id e).det ∈ J :=
    hle (Ideal.subset_span (Set.mem_range_self e))
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  apply he
  have hm : (Matrix.of (fun i j ↦ (Ideal.Quotient.mk J) (A i j))).submatrix id e =
      (Ideal.Quotient.mk J).mapMatrix (A.submatrix id e) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply,
      RingHom.mapMatrix_apply] <;> rfl
  rw [hm, ← RingHom.map_det]
  exact hz

variable {K : Type u} [CommRing K] {τ : Type u} {σ : Type u}
  [Fintype τ] [Fintype σ] [DecidableEq σ]

/-- The literal Jacobian of the literal quotient by the supplied polynomials. -/
def quotientJacobian (f : σ → MvPolynomial τ K) :
    Matrix σ τ (MvPolynomial τ K ⧸ Ideal.span (Set.range f)) :=
  fun j t ↦ Ideal.Quotient.mk _ (pderiv t (f j))

/-- The chosen pre-submersive Jacobian is precisely the corresponding original
maximal minor; its transpose has the same determinant. -/
theorem naive_jacobian_eq_minor (f : σ → MvPolynomial τ K) (e : σ ↪ τ) :
    (PreSubmersivePresentation.naive (v := f) e e.injective).jacobian =
      ((quotientJacobian f).submatrix id e).det := by
  classical
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    RingHom.map_det]
  let P := PreSubmersivePresentation.naive (v := f) e e.injective
  have hmatrix : (algebraMap P.Ring (MvPolynomial τ K ⧸ Ideal.span (Set.range f))).mapMatrix
      P.jacobiMatrix = ((quotientJacobian f).submatrix id e).transpose := by
    ext i j
    simp only [P, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      PreSubmersivePresentation.jacobiMatrix_naive, Matrix.transpose_apply,
      Matrix.submatrix_apply, id_eq, quotientJacobian] <;> rfl
  exact (congrArg Matrix.det hmatrix).trans (Matrix.det_transpose _)

/-- A polynomial quotient whose original Jacobian rows are independent in every
maximal residue field is locally standard smooth of the full expected relative
dimension. No reducedness or regular-sequence hypothesis is introduced. -/
theorem locally_standardSmoothOfRelativeDimension
    (f : σ → MvPolynomial τ K)
    (hJ : ∀ (J : Ideal (MvPolynomial τ K ⧸ Ideal.span (Set.range f))) [J.IsMaximal],
      LinearIndependent ((MvPolynomial τ K ⧸ Ideal.span (Set.range f)) ⧸ J)
        ((quotientJacobian f).map (Ideal.Quotient.mk J))) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension (Fintype.card τ - Fintype.card σ))
      (algebraMap K (MvPolynomial τ K ⧸ Ideal.span (Set.range f))) := by
  classical
  let S := MvPolynomial τ K ⧸ Ideal.span (Set.range f)
  let minor : (σ ↪ τ) → S := fun e ↦ ((quotientJacobian f).submatrix id e).det
  refine ⟨Set.range minor, span_maximalMinors_eq_top _ hJ, ?_⟩
  rintro z ⟨e, rfl⟩
  rw [← IsScalarTower.algebraMap_eq K S (Localization.Away (minor e)),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have h := standardSmooth_away_jacobian
    (PreSubmersivePresentation.naive (v := f) e e.injective)
  have he : (PreSubmersivePresentation.naive (v := f) e e.injective).jacobian = minor e :=
    naive_jacobian_eq_minor f e
  rw [he] at h
  exact h

end PaperVerification.JacobianRelativeDimension
