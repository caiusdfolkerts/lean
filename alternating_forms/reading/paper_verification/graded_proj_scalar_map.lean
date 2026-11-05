module

public import PaperVerification.HomogeneousQuotientClosedImmersion
public import PaperVerification.AlternatingFormsSectionFourGeometry

/-!
# Scalar compatibility for genuine graded Proj maps

A graded ring map preserving the original coefficient algebra induces a
morphism over its spectrum.  This applies to all homogeneous quotient
closed immersions, without an invertibility hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

section GradedHom

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- A scalar-preserving graded ring map induces an actual morphism over
the scalar spectrum.  Invertibility is unnecessary. -/
theorem gradedProjMap_over_hom (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hc : ∀ c : K, f (algebraMap K A c) = algebraMap K B c) :
    Proj.map f hf ≫ gradedProjStructureMap 𝒜 = gradedProjStructureMap ℬ := by
  have haway (s : A) (c : K) :
      Away.map f s (fromZeroRingHom 𝒜 _ (algebraMap K (𝒜 0) c)) =
        fromZeroRingHom ℬ _ (algebraMap K (ℬ 0) c) := by
    apply _root_.HomogeneousLocalization.val_injective
    change Localization.mk (f (algebraMap K A c)) ⟨f 1,_⟩ =
      Localization.mk (algebraMap K B c) ⟨1,_⟩
    simp only [map_one,hc]
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι ℬ (f s.2.1) (f.map_mem s.2.2) s.1.2 ≫
      Proj.map f hf ≫ gradedProjStructureMap 𝒜 =
    Proj.awayι ℬ (f s.2.1) (f.map_mem s.2.2) s.1.2 ≫ gradedProjStructureMap ℬ
  simp only [gradedProjStructureMap, Category.assoc,
    Proj.awayι_comp_map_assoc f hf s.1.2 s.2.1 s.2.2,
    Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact congrArg _root_.HomogeneousLocalization.val (haway s.2.1 c)

end GradedHom

namespace HomogeneousQuotientProjective

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K]
  (I J : Ideal (MvPolynomial σ K))
  (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
  (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) (hIJ : I ≤ J)

theorem quotientProjMap_over :
    quotientProjMap I J hI hJ hIJ ≫ HomogeneousQuotientCharts.structureMap I hI =
      HomogeneousQuotientCharts.structureMap J hJ :=
  gradedProjMap_over_hom _ _ (fun _ => rfl)

end HomogeneousQuotientProjective

end PaperVerification
