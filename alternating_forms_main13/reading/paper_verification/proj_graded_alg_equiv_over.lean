module

public import PaperVerification.AlternatingFormsIsotropicProjLinearAction

/-!
# Proj functoriality over the coefficient algebra

The structure morphism is the standard morphism through the degree-zero
part of the graded algebra.  A graded algebra equivalence preserves this
morphism, so geometric properties over the coefficient field transport.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory HomogeneousIdeal _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

def gradedProjStructureMap (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜] :
    Proj 𝒜 ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0)))

theorem gradedAwayMap_constant (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d) (s : A) (c : K) :
    Away.map (gradedRingHomOfEquiv e he) s
      (fromZeroRingHom 𝒜 _ (algebraMap K (𝒜 0) c)) =
      fromZeroRingHom ℬ _ (algebraMap K (ℬ 0) c) := by
  apply _root_.HomogeneousLocalization.val_injective
  change Localization.mk (e (algebraMap K A c)) ⟨e 1, _⟩ =
    Localization.mk (algebraMap K B c) ⟨1, _⟩
  simp only [map_one, e.commutes]

/-- Every graded algebra morphism arising from an equivalence is over Spec K. -/
theorem gradedProjMap_over (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hf : ℬ₊ ≤ 𝒜₊.map (gradedRingHomOfEquiv e he)) :
    Proj.map (gradedRingHomOfEquiv e he) hf ≫ gradedProjStructureMap 𝒜 =
      gradedProjStructureMap ℬ := by
  let f := gradedRingHomOfEquiv e he
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
  exact congrArg _root_.HomogeneousLocalization.val
    (gradedAwayMap_constant e he s.2.1 c)

theorem projIsoOfGradedAlgEquiv_hom_over (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hi : ∀ d x, x ∈ ℬ d → e.symm x ∈ 𝒜 d) :
    (projIsoOfGradedAlgEquiv e he hi).hom ≫ gradedProjStructureMap 𝒜 =
      gradedProjStructureMap ℬ :=
  gradedProjMap_over e he _

theorem projIsoOfGradedAlgEquiv_inv_over (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hi : ∀ d x, x ∈ ℬ d → e.symm x ∈ 𝒜 d) :
    (projIsoOfGradedAlgEquiv e he hi).inv ≫ gradedProjStructureMap ℬ =
      gradedProjStructureMap 𝒜 := by
  rw [← projIsoOfGradedAlgEquiv_hom_over e he hi, Iso.inv_hom_id_assoc]

end PaperVerification
