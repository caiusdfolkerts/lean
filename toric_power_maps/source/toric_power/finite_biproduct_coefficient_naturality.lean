module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Naturality of the canonical finite biproduct comparison

The same original finite biproducts are used on both sides. This lemma
allows coefficient transformations, including postcomposition in Hom,
to pass through the canonical comparison without unfolding chosen limits.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w z

variable {B : Type u} [Category.{v} B] [Preadditive B] [HasFiniteBiproducts B]
  {D : Type w} [Category.{z} D] [Preadditive D] [HasFiniteBiproducts D]
  {F G : B ⥤ D} [F.Additive] [G.Additive]
  {I : Type} [Finite I] (P : I → B) (α : F ⟶ G)

@[reassoc]
theorem mapBiproduct_coefficient_naturality :
    α.app (⨁ P) ≫ (G.mapBiproduct P).hom =
      (F.mapBiproduct P).hom ≫ biproduct.map (fun i => α.app (P i)) := by
  classical
  apply biproduct.hom_ext
  intro i
  dsimp only [Function.comp_def]
  simp only [Functor.mapBiproduct_hom, Category.assoc, biproduct.map_π,
    biproduct.lift_π_assoc, biproduct.lift_π]
  exact (α.naturality (biproduct.π P i)).symm

end ToricPower

end

