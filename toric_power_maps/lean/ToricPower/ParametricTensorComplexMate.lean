module

public import ToricPower.ComplexAdjunction
public import ToricPower.SingleAugmentationComponent
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Source-natural transposition of actual tensor-complex maps

The construction uses the literal termwise tensor/internal-Hom
adjunction and the original braiding. A compatible family of right
tensor evaluations therefore gives an actual natural transformation of
complex-valued functors. The single-target component is its original
curried coefficient; no homology comparison is substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe u v w z

variable {C : Type u} [Category.{v} C]
  {B : Type w} [Category.{z} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B]
  [BraidedCategory B] [MonoidalClosed B]
  (R : C ⥤ B) (Z : CochainComplex B ℕ)

/-- Internal Hom in the varying original source, degree by degree. -/
def internalHomComplexSource : Cᵒᵖ ⥤ CochainComplex B ℕ where
  obj c := ((ihom (R.obj c.unop)).mapHomologicalComplex (.up ℕ)).obj Z
  map f := ((pre (R.map f.unop)).mapHomologicalComplex (.up ℕ)).app Z
  map_id c := by
    ext q
    change (pre (R.map (𝟙 c.unop))).app (Z.X q) = 𝟙 _
    simp only [R.map_id, pre_id, NatTrans.id_app]
  map_comp f g := by
    ext q
    change (pre (R.map (g.unop ≫ f.unop))).app (Z.X q) =
      (pre (R.map f.unop)).app (Z.X q) ≫ (pre (R.map g.unop)).app (Z.X q)
    simp only [R.map_comp, pre_map, NatTrans.comp_app]

variable (Φ : Cᵒᵖ ⥤ CochainComplex B ℕ)
  (evaluation : ∀ c : C,
    (((tensoringRight B).obj (R.obj c)).mapHomologicalComplex (.up ℕ)).obj
      (Φ.obj (op c)) ⟶ Z)
  (compatible : ∀ {c d : C} (f : c ⟶ d),
    (((tensoringRight B).obj (R.obj c)).mapHomologicalComplex (.up ℕ)).map
        (Φ.map f.op) ≫ evaluation c =
      (((tensoringRight B).map (R.map f)).mapHomologicalComplex (.up ℕ)).app
        (Φ.obj (op d)) ≫ evaluation d)

/-- Transposition retains every original source arrow. -/
def parametricTensorComplexMate : Φ ⟶ internalHomComplexSource R Z where
  app c := (complexAdjunction (ihom.adjunction (R.obj c.unop)) (.up ℕ)).homEquiv _ _
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight (R.obj c.unop))
      (.up ℕ)).hom.app (Φ.obj c) ≫ evaluation c.unop)
  naturality {c d} f := by
    apply HomologicalComplex.Hom.ext
    funext q
    change (Φ.map f).f q ≫
        curry ((β_ (R.obj d.unop) ((Φ.obj d).X q)).hom ≫ (evaluation d.unop).f q) =
      curry ((β_ (R.obj c.unop) ((Φ.obj c).X q)).hom ≫ (evaluation c.unop).f q) ≫
        (pre (R.map f.unop)).app (Z.X q)
    rw [← curry_natural_left, curry_pre_app]
    apply congrArg curry
    rw [BraidedCategory.braiding_naturality_right_assoc,
      BraidedCategory.braiding_naturality_left_assoc]
    exact congrArg (fun g => (β_ (R.obj d.unop) ((Φ.obj c).X q)).hom ≫ g)
      (congrArg (fun g => g.f q) (compatible f.unop))

variable (J : B) (n : ℕ)

/-- The same original source diagram in one degree. -/
def internalHomComplexSingleIso :
    internalHomComplexSource R ((HomologicalComplex.single B (.up ℕ) n).obj J) ≅
      (R.op ⋙ MonoidalClosed.internalHom.flip.obj J) ⋙
        HomologicalComplex.single B (.up ℕ) n :=
  NatIso.ofComponents (fun c =>
    (HomologicalComplex.singleMapHomologicalComplex (ihom (R.obj c.unop))
      (.up ℕ) n).app J) (by
    intro c d f
    change ((pre (R.map f.unop)).mapHomologicalComplex (.up ℕ)).app
        ((HomologicalComplex.single B (.up ℕ) n).obj J) ≫
        (HomologicalComplex.singleMapHomologicalComplex (ihom (R.obj d.unop))
          (.up ℕ) n).hom.app J =
      (HomologicalComplex.singleMapHomologicalComplex (ihom (R.obj c.unop))
        (.up ℕ) n).hom.app J ≫
        (HomologicalComplex.single B (.up ℕ) n).map ((pre (R.map f.unop)).app J)
    rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    erw [Category.comp_id])

end ToricPower

end
