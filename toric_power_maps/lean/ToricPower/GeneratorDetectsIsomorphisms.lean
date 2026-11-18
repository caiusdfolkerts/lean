module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# A genuine right generator detects isomorphisms

Bijectivity on morphisms from every shift of a right generator forces a
morphism to be an isomorphism. The proof uses an actual distinguished
cone, including the shift equivalence needed for the boundary map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Right generation here has its literal all-shifts, all-targets meaning. -/
def IsRightGenerator (G : C) : Prop :=
  ∀ (Y : C), (∀ (n : ℤ) (f : G⟦n⟧ ⟶ Y), f = 0) → IsZero Y

theorem shifted_postcomp_zero {A B X : C} (f : A ⟶ B)
    (injective : ∀ (g : X⟦(-1 : ℤ)⟧ ⟶ A), g ≫ f = 0 → g = 0)
    (g : X ⟶ A⟦(1 : ℤ)⟧) (killed : g ≫ f⟦(1 : ℤ)⟧' = 0) : g = 0 := by
  let e := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
  let unshift : X⟦(-1 : ℤ)⟧ ⟶ A := g⟦(-1 : ℤ)⟧' ≫ e.hom.app A
  have natural : f⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' ≫ e.hom.app B = e.hom.app A ≫ f :=
    e.hom.naturality f
  have unshiftZero : unshift = 0 := by
    apply injective
    dsimp only [unshift]
    rw [Category.assoc, ← natural, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, killed, CategoryTheory.Functor.map_zero, zero_comp]
  apply (shiftFunctor C (-1 : ℤ)).map_injective
  rw [CategoryTheory.Functor.map_zero]
  apply (cancel_mono (e.hom.app A)).mp
  simpa only [zero_comp] using unshiftZero

/-- Actual bijectivity on all shifted-generator Hom groups detects an
isomorphism, without a boundedness restriction on either target. -/
theorem isIso_of_generator_hom_bijective (G : C) (generator : IsRightGenerator G)
    {A B : C} (f : A ⟶ B)
    (bijective : ∀ n : ℤ, Function.Bijective (fun g : G⟦n⟧ ⟶ A => g ≫ f)) :
    IsIso f := by
  obtain ⟨Z, q, d, distinguished⟩ := distinguished_cocone_triangle f
  let T : Triangle C := Triangle.mk f q d
  apply (T.isZero₃_iff_isIso₁ distinguished).mp
  apply generator
  intro n g
  have boundaryZero : g ≫ d = 0 := by
    apply shifted_postcomp_zero f
    · intro h killed
      let e := shiftAdd G n (-1 : ℤ)
      apply (cancel_epi e.hom).mp
      apply (bijective (n + (-1))).injective
      simpa only [Category.assoc, killed, comp_zero, zero_comp]
    · rw [Category.assoc]
      rw [show d ≫ f⟦(1 : ℤ)⟧' = 0 from
        comp_distTriang_mor_zero₃₁ T distinguished, comp_zero]
  obtain ⟨h, hg⟩ := T.coyoneda_exact₃ distinguished g boundaryZero
  obtain ⟨k, hk⟩ := (bijective n).surjective h
  rw [hg, ← hk, Category.assoc]
  rw [show f ≫ T.mor₂ = 0 from comp_distTriang_mor_zero₁₂ T distinguished, comp_zero]

end ToricPower.CompactExtraction

end
