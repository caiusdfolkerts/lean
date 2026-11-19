module

public import PaperVerification.ProjGradedSurjection
public import PaperVerification.HomogeneousQuotientProjective

/-!
# Closed immersions between homogeneous polynomial quotients

Inclusion of the original homogeneous ideals induces the canonical graded
quotient map and hence a closed immersion of their projective schemes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.HomogeneousQuotientProjective

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K]
  (I J : Ideal (MvPolynomial σ K))
  (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
  (hJ : J.IsHomogeneous (homogeneousSubmodule σ K))
  (hIJ : I ≤ J)

/-- The canonical quotient map, retaining the original polynomial grading. -/
def quotientGradedHom : grading I hI →+*ᵍ grading J hJ where
  __ := Ideal.Quotient.factor hIJ
  map_mem {d} {x} hx := by
    rw [grading_eq_piece] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, rfl⟩

@[simp]
theorem quotientGradedHom_mk (p : MvPolynomial σ K) :
    quotientGradedHom I J hI hJ hIJ (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk J p := rfl

theorem quotientGradedHom_surjective :
    GradedSurjective (quotientGradedHom I J hI hJ hIJ) := by
  intro d b hb
  rw [grading_eq_piece] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  refine ⟨Ideal.Quotient.mk I p, ?_, rfl⟩
  rw [grading_eq_piece]
  exact ⟨p, hp, rfl⟩

/-- The actual projective closed immersion induced by inclusion of ideals. -/
def quotientProjMap : Proj (grading J hJ) ⟶ Proj (grading I hI) :=
  Proj.map (quotientGradedHom I J hI hJ hIJ)
    (irrelevant_le_map_of_gradedSurjective _
      (quotientGradedHom_surjective I J hI hJ hIJ))

instance quotientProjMap_isClosedImmersion :
    IsClosedImmersion (quotientProjMap I J hI hJ hIJ) :=
  isClosedImmersion_projMap_of_gradedSurjective _
    (quotientGradedHom_surjective I J hI hJ hIJ)

@[simp]
theorem quotientProjMap_preimage_variable (i : σ) :
    quotientProjMap I J hI hJ hIJ ⁻¹ᵁ
      Proj.basicOpen (grading I hI) (Ideal.Quotient.mk I (X i)) =
      Proj.basicOpen (grading J hJ) (Ideal.Quotient.mk J (X i)) := rfl

end PaperVerification.HomogeneousQuotientProjective
