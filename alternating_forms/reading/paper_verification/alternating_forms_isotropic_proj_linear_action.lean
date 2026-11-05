module

public import PaperVerification.AlternatingFormsIsotropicLinearAction
public import PaperVerification.AlternatingFormsProjAtlas
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Scheme isomorphisms induced by linear changes of the alternating forms

The coordinate-ring equivalence is graded in both directions.  Functoriality
of Mathlib's actual projective spectrum therefore supplies an isomorphism of
the original common-isotropic projective schemes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory HomogeneousIdeal
open scoped HomogeneousIdeal

namespace PaperVerification

section GradedEquivalence

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

def gradedRingHomOfEquiv (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d) : 𝒜 →+*ᵍ ℬ where
  __ := e.toRingHom
  map_mem hx := he _ _ hx

theorem irrelevant_le_map_of_inverse
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : ∀ x, f (g x) = x) : ℬ₊ ≤ 𝒜₊.map f := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro d hd x hx
  have hg : g x ∈ 𝒜₊ :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd (g.map_mem hx)
  change x ∈ (𝒜₊.map f).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, ← hfg x]
  exact Ideal.mem_map_of_mem f hg

/-- A graded algebra equivalence induces an isomorphism of the actual schemes Proj. -/
def projIsoOfGradedAlgEquiv (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hi : ∀ d x, x ∈ ℬ d → e.symm x ∈ 𝒜 d) : Proj ℬ ≅ Proj 𝒜 := by
  let f := gradedRingHomOfEquiv e he
  let g := gradedRingHomOfEquiv e.symm hi
  have hf : ℬ₊ ≤ 𝒜₊.map f :=
    irrelevant_le_map_of_inverse f g e.apply_symm_apply
  have hg : 𝒜₊ ≤ ℬ₊.map g :=
    irrelevant_le_map_of_inverse g f e.symm_apply_apply
  have hfg : f.comp g = GradedRingHom.id ℬ := by
    ext x
    exact e.apply_symm_apply x
  have hgf : g.comp f = GradedRingHom.id 𝒜 := by
    ext x
    exact e.symm_apply_apply x
  refine ⟨Proj.map f hf, Proj.map g hg, ?_, ?_⟩
  · rw [← Proj.map_comp]
    simpa only [hfg] using (Proj.map_id (𝒜 := ℬ))
  · rw [← Proj.map_comp]
    simpa only [hgf] using (Proj.map_id (𝒜 := 𝒜))

end GradedEquivalence

namespace AlternatingForms

open MvPolynomial

variable {K : Type} [Field K] [CharZero K] {t n m : ℕ}

@[simp] theorem isotropicPluckerLinearEquiv_symm_mk
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (p : MvPolynomial (PluckerIndex (t+2) n) K) :
    (isotropicPluckerLinearEquiv e forms forms' hforms).symm (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (pluckerLinearAction e.symm.toLinearMap (t+2) p) := rfl

theorem isotropicPluckerLinearEquiv_graded
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (d : ℕ) (x : MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms)
    (hx : x ∈ isotropicProjectiveGrading forms d) :
    isotropicPluckerLinearEquiv e forms forms' hforms x ∈
      isotropicProjectiveGrading forms' d := by
  change x ∈ HomogeneousQuotientProjective.grading _ _ d at hx
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  change _ ∈ HomogeneousQuotientProjective.grading _ _ d
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact ⟨pluckerLinearAction e.toLinearMap (t+2) p,
    pluckerLinearAction_homogeneous e.toLinearMap p d hp,rfl⟩

theorem isotropicPluckerLinearEquiv_symm_graded
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (d : ℕ) (x : MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms')
    (hx : x ∈ isotropicProjectiveGrading forms' d) :
    (isotropicPluckerLinearEquiv e forms forms' hforms).symm x ∈
      isotropicProjectiveGrading forms d := by
  change x ∈ HomogeneousQuotientProjective.grading _ _ d at hx
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  change _ ∈ HomogeneousQuotientProjective.grading _ _ d
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact ⟨pluckerLinearAction e.symm.toLinearMap (t+2) p,
    pluckerLinearAction_homogeneous e.symm.toLinearMap p d hp,rfl⟩

/-- Linearly equivalent tuples define isomorphic genuine common-isotropic schemes. -/
def isotropicProjLinearIso
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    Proj (isotropicProjectiveGrading (t := t) forms') ≅
      Proj (isotropicProjectiveGrading (t := t) forms) :=
  projIsoOfGradedAlgEquiv (isotropicPluckerLinearEquiv e forms forms' hforms)
    (isotropicPluckerLinearEquiv_graded e forms forms' hforms)
    (isotropicPluckerLinearEquiv_symm_graded e forms forms' hforms)

end AlternatingForms
end PaperVerification
