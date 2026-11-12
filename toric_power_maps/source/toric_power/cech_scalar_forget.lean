module

public import ToricPower.AdditiveAlternatingCoface
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Forgetting scalars in the complete Čech complex

The comparison uses preservation of actual categorical products and
retains every tuple, every face map, and every alternating differential.
It is natural in all coefficient maps. The homology comparison is the
one supplied by the exact scalar-forgetting functor.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace ToricPower.CechScalar

universe u v w

variable (k : Type u) [CommRing k] {C : Type v} [Category.{w} C]

abbrev forgetScalars : ModuleCat.{u} k ⥤ AddCommGrpCat.{u} := forget₂ _ _

/-- Product preservation identifies evaluation on every actual formal
coproduct before and after forgetting the scalar structure. -/
def formalCoproductForgetIso (P : Cᵒᵖ ⥤ ModuleCat.{u} k) :
    (FormalCoproduct.evalOp.{u} C (ModuleCat.{u} k)).obj P ⋙ forgetScalars k ≅
      (FormalCoproduct.evalOp.{u} C AddCommGrpCat.{u}).obj (P ⋙ forgetScalars k) :=
  NatIso.ofComponents (fun X => PreservesProduct.iso (forgetScalars k)
      (fun a : X.unop.I => P.obj (op (X.unop.obj a)))) (by
    intro X Y f
    apply Limits.Pi.hom_ext
    intro a
    dsimp only [Functor.comp_map, Functor.comp_obj, FormalCoproduct.evalOp_obj_map,
      FormalCoproduct.evalOp_obj_obj]
    simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π,
      Limits.Pi.lift_comp_π, ← CategoryTheory.Functor.map_comp]
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, piComparison_comp_π])

/-- The product comparison is natural in the presheaf coefficients. -/
theorem formalCoproductForgetIso_naturality
    {P Q : Cᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ Q)
    (X : (FormalCoproduct.{u} C)ᵒᵖ) :
    (forgetScalars k).map (((FormalCoproduct.evalOp C (ModuleCat.{u} k)).map f).app X) ≫
        (formalCoproductForgetIso k Q).hom.app X =
      (formalCoproductForgetIso k P).hom.app X ≫
        (((FormalCoproduct.evalOp C AddCommGrpCat.{u}).map
          (Functor.whiskerRight f (forgetScalars k))).app X) := by
  change (forgetScalars k).map
      (Limits.Pi.map (fun a : X.unop.I => f.app (op (X.unop.obj a)))) ≫
        piComparison (forgetScalars k) (fun a : X.unop.I => Q.obj (op (X.unop.obj a))) =
    piComparison (forgetScalars k) (fun a : X.unop.I => P.obj (op (X.unop.obj a))) ≫
      Limits.Pi.map (fun a : X.unop.I => (forgetScalars k).map (f.app (op (X.unop.obj a))))
  apply Limits.Pi.hom_ext
  intro a
  simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
    ← CategoryTheory.Functor.map_comp]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, piComparison_comp_π]

variable (E : SimplicialObject (FormalCoproduct.{u} C))

/-- Scalar forgetting commutes with the full cosimplicial object. -/
def cosimplicialForgetIso (P : Cᵒᵖ ⥤ ModuleCat.{u} k) :
    (FormalCoproduct.cosimplicialObjectFunctor E).obj P ⋙ forgetScalars k ≅
      (FormalCoproduct.cosimplicialObjectFunctor E).obj (P ⋙ forgetScalars k) :=
  Functor.isoWhiskerLeft E.rightOp (formalCoproductForgetIso k P)

/-- The complete alternating cochain complexes are actually isomorphic. -/
def cochainForgetIso (P : Cᵒᵖ ⥤ ModuleCat.{u} k) :
    ((forgetScalars k).mapHomologicalComplex (.up ℕ)).obj
        ((FormalCoproduct.cochainComplexFunctor E).obj P) ≅
      (FormalCoproduct.cochainComplexFunctor E).obj (P ⋙ forgetScalars k) :=
  (additiveAlternatingCofaceIso (forgetScalars k)
      ((FormalCoproduct.cosimplicialObjectFunctor E).obj P)).symm ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (cosimplicialForgetIso k E P)

/-- The degree comparison is the actual categorical product comparison. -/
theorem cochainForgetIso_hom_f (P : Cᵒᵖ ⥤ ModuleCat.{u} k) (q : ℕ) :
    (cochainForgetIso k E P).hom.f q =
      (formalCoproductForgetIso k P).hom.app (E.rightOp.obj ⦋q⦌) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Naturality holds before taking homology, in every degree. -/
theorem cochainForgetIso_naturality
    {P Q : Cᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ Q) :
    ((forgetScalars k).mapHomologicalComplex (.up ℕ)).map
        ((FormalCoproduct.cochainComplexFunctor E).map f) ≫
        (cochainForgetIso k E Q).hom =
      (cochainForgetIso k E P).hom ≫
        (FormalCoproduct.cochainComplexFunctor E).map
          (Functor.whiskerRight f (forgetScalars k)) := by
  apply HomologicalComplex.hom_ext
  intro q
  simp only [HomologicalComplex.comp_f, cochainForgetIso_hom_f]
  exact formalCoproductForgetIso_naturality k f (E.rightOp.obj ⦋q⦌)

/-- Exact scalar forgetting commutes naturally with actual complex homology. -/
def homologyForgetNatIso (degree : ℕ) :
    (forgetScalars k).mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) degree ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℕ) degree ⋙
        forgetScalars k :=
  NatIso.ofComponents (fun K => (K.sc degree).mapHomologyIso (forgetScalars k))
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℕ) degree).map f)
      (forgetScalars k))

end ToricPower.CechScalar

end
