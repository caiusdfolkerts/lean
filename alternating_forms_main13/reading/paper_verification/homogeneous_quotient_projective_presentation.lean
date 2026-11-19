module

public import PaperVerification.GradedProjScalarMap
public import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective

/-!
# A genuine projective presentation of a homogeneous polynomial quotient

The embedding is the actual `Proj` morphism of the quotient graded ring.
A finite renumbering of the original variables places its target in the
standard projective space used by the complex-point library.  This is only
packaging of a proved closed immersion; no topological hypothesis is added.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.HomogeneousQuotientProjective

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K]
  (I : Ideal (MvPolynomial σ K))
  (hI : I.IsHomogeneous (homogeneousSubmodule σ K))

def polynomialQuotientGradedHom : homogeneousSubmodule σ K →+*ᵍ grading I hI where
  __ := Ideal.Quotient.mk I
  map_mem {d} {x} hx := by
    rw [grading_eq_piece]
    exact ⟨x,hx,rfl⟩

theorem polynomialQuotientGradedHom_surjective :
    GradedSurjective (polynomialQuotientGradedHom I hI) := by
  intro d x hx
  rw [grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  exact ⟨p,hp,rfl⟩

/-- The original closed embedding into its unquotiented polynomial Proj. -/
def polynomialQuotientProjEmbedding : Proj (grading I hI) ⟶ Proj (homogeneousSubmodule σ K) :=
  Proj.map (polynomialQuotientGradedHom I hI)
    (irrelevant_le_map_of_gradedSurjective _ (polynomialQuotientGradedHom_surjective I hI))

instance polynomialQuotientProjEmbedding_isClosedImmersion :
    IsClosedImmersion (polynomialQuotientProjEmbedding I hI) :=
  isClosedImmersion_projMap_of_gradedSurjective _ (polynomialQuotientGradedHom_surjective I hI)

theorem polynomialQuotientProjEmbedding_over :
    polynomialQuotientProjEmbedding I hI ≫ gradedProjStructureMap (homogeneousSubmodule σ K) =
      HomogeneousQuotientCharts.structureMap I hI :=
  gradedProjMap_over_hom _ _ (fun _ => rfl)

variable [Fintype σ] [Nonempty σ]

/-- The original variable set is nonempty in every relevant Grassmannian
range. Its finite cardinal gives the standard ambient projective dimension. -/
def projectiveVariableEquiv : σ ≃ Fin ((Fintype.card σ - 1) + 1) :=
  (Fintype.equivFin σ).trans
    (finCongr (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)).symm)

def polynomialProjStandardIso :
    Proj (homogeneousSubmodule σ K) ≅
      Proj (homogeneousSubmodule (Fin ((Fintype.card σ - 1)+1)) K) :=
  projIsoOfGradedAlgEquiv (renameEquiv K (projectiveVariableEquiv (σ := σ)).symm)
    (fun _ _ hp => hp.rename_isHomogeneous)
    (fun _ _ hp => hp.rename_isHomogeneous)

theorem polynomialProjStandardIso_hom_over :
    (polynomialProjStandardIso (K := K) (σ := σ)).hom ≫
      gradedProjStructureMap (homogeneousSubmodule (Fin ((Fintype.card σ - 1)+1)) K) =
        gradedProjStructureMap (homogeneousSubmodule σ K) :=
  projIsoOfGradedAlgEquiv_hom_over _ _ _

/-- An actual closed projective embedding over the complex numbers. -/
def projectivePresentation
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      (Proj (grading I hI)) (HomogeneousQuotientCharts.structureMap I hI) where
  ambientDimension := Fintype.card σ - 1
  embedding := polynomialQuotientProjEmbedding I hI ≫
    (polynomialProjStandardIso (K := ℂ) (σ := σ)).hom
  closedImmersion := by infer_instance
  over_base := by
    change _ ≫ gradedProjStructureMap
      (homogeneousSubmodule (Fin ((Fintype.card σ - 1)+1)) ℂ) = _
    rw [Category.assoc, polynomialProjStandardIso_hom_over,
      polynomialQuotientProjEmbedding_over]

end PaperVerification.HomogeneousQuotientProjective
