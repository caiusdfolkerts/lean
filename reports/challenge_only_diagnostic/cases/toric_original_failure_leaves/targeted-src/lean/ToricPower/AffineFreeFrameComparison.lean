module

public import ToricPower.SchemeAffineLinear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Finite affine free modules in arbitrary chosen sheaf frames

The comparison and its generator equation are established once with
abstract labels and an abstract additive image functor. Geometric
specializations then use this universal calculation directly, without
expanding the construction of a toric chart or a Cartier sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower

universe u v

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

theorem affineTilde_map_sum (R : CommRingCat.{0})
    {J : Type} [Fintype J] {M N : ModuleCat.{0} R} (f : J → (M ⟶ N)) :
    tilde.map (∑ j, f j) = ∑ j, tilde.map (f j) := by
  letI : PreservesFiniteLimits (tilde.functor R) :=
    TauCeti.AlgebraicGeometry.preservesFiniteLimits_tildeFunctor
  letI : (tilde.functor R).Additive :=
    (tilde.functor R).additive_of_preserves_binary_products
  exact (tilde.functor R).map_sum f Finset.univ

variable (R : CommRingCat.{0}) (I : Type) [Finite I]
  {C : Type u} [Category.{v} C] [Preadditive C]
  (P : C ⥤ (Spec R).Modules) [P.PreservesZeroMorphisms]
  (L : I → C) [HasBiproduct L] [PreservesBiproduct L P]
  (frame : ∀ i, SheafOfModules.unit (Spec R).ringCatSheaf ≅ P.obj (L i))

/-- The actual affine free module identified with the actual image of
the finite sum of labels in their specified unit frames. -/
def affineFreeFrameComparison :
    tilde (ModuleCat.of R (I →₀ R)) ≅ P.obj (⨁ L) :=
  tildeFiniteFreeBiproductIso R I ≪≫ biproduct.mapIso frame ≪≫
    (P.mapBiproduct L).symm

@[reassoc]
theorem affineFreeFrameComparison_generator (i : I) :
    (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] I →₀ R)) ≫
        (affineFreeFrameComparison R I P L frame).hom =
      (frame i).hom ≫ P.map (biproduct.ι L i) := by
  simp only [affineFreeFrameComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, biproduct.mapIso_hom, Functor.mapBiproduct_inv]
  erw [tildeFiniteFreeBiproductIso_single_assoc, biproduct.ι_map_assoc,
    biproduct.ι_desc]

end ToricPower
