module

public import PaperVerification.AlternatingFormsConnectedGrading
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# The actual graded ring and projective spectrum of a homogeneous quotient

The homogeneous pieces are the images of the original polynomial pieces.
Their previously proved internal direct sum and multiplication laws give
Mathlib's genuine GradedAlgebra instance.  A surjective polynomial
presentation by degree-one elements gives an actual basic-open cover of Proj.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousQuotientProjective

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- The same internal grading already constructed from the original quotient. -/
def grading (Q : Ideal P) (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) :
    ℕ → Submodule K (P⧸Q) := (HomogeneousIdealPieces.grading Q hQ).piece

@[simp] theorem grading_eq_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (d : ℕ) :
    grading Q hQ d=HomogeneousIdealPieces.piece Q d :=
  HomogeneousIdealPieces.grading_piece Q hQ d

instance quotientGradedMonoid (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) :
    SetLike.GradedMonoid (grading Q hQ) where
  one_mem := by
    rw [grading_eq_piece,AlternatingForms.homogeneousQuotient_degree_zero]
    exact Submodule.mem_one.mpr ⟨1,map_one _⟩
  mul_mem := by
    intro a b x y hx hy
    rw [grading_eq_piece] at hx hy ⊢
    exact AlternatingForms.homogeneousQuotient_mul_mem Q a b x y hx hy

/-- A genuine GradedRing instance, with the original multiplication and
original homogeneous pieces; no grading is assumed at the application. -/
instance quotientGradedAlgebra (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) :
    GradedAlgebra (grading Q hQ) := by
  letI : SetLike.GradedMonoid (HomogeneousIdealPieces.grading Q hQ).piece :=
    quotientGradedMonoid Q hQ
  exact (HomogeneousIdealPieces.grading Q hQ).isInternal.gradedAlgebra

theorem quotient_X_mem_one (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (i : σ) :
    Ideal.Quotient.mk Q (X i)∈grading Q hQ 1 := by
  rw [grading_eq_piece]
  exact ⟨X i,isHomogeneous_X K i,rfl⟩

/-- Every surjective polynomial presentation generates the actual quotient
as an algebra, with the literal images of its variables. -/
theorem adjoin_range_variable_eq_top {τ : Type*} (Q : Ideal P)
    (F : MvPolynomial τ K →ₐ[K] (P⧸Q)) (hF : Function.Surjective F) :
    Algebra.adjoin K (Set.range (fun i ↦ F (X i)))=⊤ := by
  change Algebra.adjoin K (Set.range (F ∘ (X : τ → MvPolynomial τ K)))=⊤
  rw [Set.range_comp,Algebra.adjoin_image,adjoin_range_X,Algebra.map_top]
  exact (AlgHom.range_eq_top F).mpr hF

/-- A degree-one presentation supplies the standard cover on the actual
projective spectrum, rather than a cover imposed on a separate point model. -/
theorem presentation_basicOpen_cover {τ : Type*} (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
    (F : MvPolynomial τ K →ₐ[K] (P⧸Q)) (hF : Function.Surjective F)
    (hdeg : ∀ i,F (X i)∈grading Q hQ 1) :
    (⨆ i,Proj.basicOpen (grading Q hQ) (F (X i)))=⊤ := by
  apply Proj.iSup_basicOpen_eq_top' _ _ (fun i ↦ ⟨1,hdeg i⟩)
  apply top_unique
  intro a ha
  obtain ⟨p,rfl⟩ := hF a
  clear ha
  induction p using MvPolynomial.induction_on with
  | C c =>
      have hFC : F (C c)=Ideal.Quotient.mk Q (C c) := by
        change F (algebraMap K (MvPolynomial τ K) c)=algebraMap K (P⧸Q) c
        exact F.commutes c
      have hc : F (C c)∈grading Q hQ 0 := by
        rw [hFC,grading_eq_piece]
        refine ⟨C c, ?_, rfl⟩
        change (C c : P).IsHomogeneous 0
        exact isHomogeneous_C σ c
      exact Subalgebra.algebraMap_mem
        (Algebra.adjoin (grading Q hQ 0) (Set.range (fun i ↦ F (X i))))
        ⟨F (C c),hc⟩
  | add p q hp hq =>
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i,rfl⟩)

end PaperVerification.HomogeneousQuotientProjective
