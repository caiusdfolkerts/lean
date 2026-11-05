module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import tau_ceti.algebra.homology.short_complex.short_exact
import all tau_ceti.algebra.homology.short_complex.short_exact
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive

set_option Elab.async false

section GeometryLiteralSource000
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sheaf cohomology at a terminal object

Mathlib carries two accounts of the cohomology of an abelian sheaf `F` on a site `(C, J)`:

* `CategoryTheory.Sheaf.H F n`, the `Ext`-groups from the constant sheaf `ℤ`, which is the
  cohomology of the site as a whole;
* `CategoryTheory.Sheaf.H' F n X`, the `Ext`-groups from the sheafification of the free abelian
  presheaf on `yoneda.obj X`, which is the cohomology of the object `X`.

They agree when `X` is a terminal object, and this file supplies that comparison. The abstract
Mayer-Vietoris sequence of `Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris` is stated
in terms of `Sheaf.H'`, so the comparison is what lets a covering of the whole site compute
`Sheaf.H`.

## Main declarations

* `CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH`: the comparison as a natural
  isomorphism in the coefficient sheaf;
* `CategoryTheory.Sheaf.cohomologyPresheafObjIsoH`: its specialization
  `Hⁿ(T, F) ≅ Hⁿ(F)` at a terminal object `T`, as an isomorphism of abelian groups.
-/

public section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

private noncomputable def yonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ≅ (Functor.const Cᵒᵖ).obj PUnit.{v + 1} :=
  (hT.isTerminalObj yoneda).uniqueUpToIso (Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit)

private def freeObjPUnitIso :
    AddCommGrpCat.free.obj PUnit.{v + 1} ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  AddEquiv.toAddCommGrpIso ((FreeAbelianGroup.uniqueEquiv PUnit).trans AddEquiv.ulift.symm)

private noncomputable def freeYonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  Functor.isoWhiskerRight (yonedaObjIsoConst hT) AddCommGrpCat.free ≪≫
    Functor.constComp (J := Cᵒᵖ) PUnit.{v + 1} AddCommGrpCat.free ≪≫
      (Functor.const Cᵒᵖ).mapIso freeObjPUnitIso

noncomputable section

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

-- Mathlib's `extFunctorObj` and `functorH` use definitionally equal object and map data.
-- Naming that identification here isolates the definitional coincidence used below.
private def extFunctorObjIsoFunctorH (n : ℕ) :
    (_root_.CategoryTheory.Abelian.extFunctor n).obj
        (op ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)))) ≅
      _root_.CategoryTheory.Sheaf.functorH J n :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      intros
      ext
      rfl)

end

end CategoryTheory

end TauCeti

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (J) in
/-- At a terminal object `T`, the cohomology presheaf evaluated at `T` is the cohomology of the
site, naturally in the coefficient sheaf. -/
noncomputable def cohomologyPresheafEvaluationIsoFunctorH (n : ℕ) {T : C} (hT : IsTerminal T) :
    cohomologyPresheafFunctor J n ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T) ≅
      functorH J n :=
  (Abelian.extFunctor n).mapIso
      ((presheafToSheaf J _).mapIso
        (TauCeti.CategoryTheory.freeYonedaObjIsoConst hT)).symm.op ≪≫
    TauCeti.CategoryTheory.extFunctorObjIsoFunctorH n

/-- At a terminal object, the cohomology of the object is the cohomology of the site. -/
noncomputable abbrev cohomologyPresheafObjIsoH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {T : C} (hT : IsTerminal T) :
    H' F n T ≅ AddCommGrpCat.of (H F n) :=
  (cohomologyPresheafEvaluationIsoFunctorH J n hT).app F

end CategoryTheory.Sheaf
end
end GeometryLiteralSource000

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal"

section GeometryLiteralSource001
/- Original source: TauCeti.AlgebraicGeometry.Cohomology.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cohomology of sheaves of modules on a scheme

Mathlib defines the cohomology `CategoryTheory.Sheaf.H` of an abelian sheaf on a site as an
`Ext` group from the constant sheaf `ℤ`. This file applies that construction to the underlying
abelian sheaf of an `𝒪_X`-module and packages the result in the scheme-module API.

For a scheme `X` and `M : X.Modules`, the main declarations are:

* `Scheme.Modules.Cohomology M i`, the group `Hⁱ(X, M)`;
* `Scheme.Modules.cohomologyFunctor X i`, functoriality in the coefficient sheaf;
* `Scheme.Modules.cohomologyZeroEquiv`, the canonical equivalence
  `H⁰(X, M) ≃+ Γ(M, ⊤)` with global sections;
* `Scheme.Modules.cohomologyOn M n U`, the cohomology `Hⁿ(U, M)` of an open subset,
  `Scheme.Modules.cohomologyOnRes` its restriction maps, and
  `Scheme.Modules.cohomologyOnTopIso` the identification of `Hⁿ(⊤, M)` with `Hⁿ(X, M)`.

The construction is stated for every sheaf of modules, which is the natural generality of sheaf
cohomology. In particular it applies to finitely presented sheaves through their underlying
objects, and hence supplies the `Hⁱ(X, ℱ)` used for coherent sheaves in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer B. Finite-dimensionality for proper schemes,
vanishing on curves, and the comparison with Čech cohomology remain later Layer B work.

No formalization is vendored. The definitions reuse Mathlib's `Sheaf.H`, `Sheaf.functorH`,
`Sheaf.H.equiv₀` and `Sheaf.H'`, and the comparison at the terminal open subset is
`TauCeti/CategoryTheory/Sites/SheafCohomology/Terminal.lean`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The `i`th cohomology group `Hⁱ(X, M)` of a sheaf of modules on a scheme.

This is sheaf cohomology on the small Zariski site of `X`, obtained by forgetting the
`𝒪_X`-module structure and applying Mathlib's `CategoryTheory.Sheaf.H`. -/
abbrev Cohomology (M : X.Modules) (i : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) i

/-- Degree-`i` cohomology as an additive functor from sheaves of modules to abelian groups. -/
abbrev cohomologyFunctor (X : Scheme.{u}) (i : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i

/-- Degreewise scheme-module cohomology preserves addition and zero morphisms. -/
instance (X : Scheme.{u}) (i : ℕ) : (cohomologyFunctor X i).Additive :=
  inferInstanceAs ((_root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i).Additive)

/-- Zeroth cohomology is canonically equivalent to the group of global sections.

Naturality in the coefficient sheaf follows from `CategoryTheory.Sheaf.H.equiv₀_naturality`
and `CategoryTheory.Sheaf.H.equiv₀_symm_naturality`, applied to `isTerminalTop` and the
underlying sheaf morphism. -/
def cohomologyZeroEquiv (M : X.Modules) :
    Cohomology M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop

/-- The identification of zeroth cohomology with global sections is Mathlib's
`CategoryTheory.Sheaf.H.equiv₀` at the terminal open. -/
lemma cohomologyZeroEquiv_apply {M : X.Modules} (x : Cohomology M 0) :
    cohomologyZeroEquiv M x = CategoryTheory.Sheaf.H.equiv₀
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop x :=
  (rfl)

/-- The degree-zero cohomology equivalence is natural in the coefficient sheaf. -/
lemma cohomologyZeroEquiv_naturality {M N : X.Modules} (f : M ⟶ N) (x : Cohomology M 0) :
    cohomologyZeroEquiv N ((cohomologyFunctor X 0).map f x) =
      f.app ⊤ (cohomologyZeroEquiv M x) :=
  (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) x).symm

section Opens

variable (M : X.Modules)

/-- The cohomology `Hⁿ(U, M)` of an open subset `U` of a scheme `X` with coefficients in a sheaf
of modules `M`, as an abelian group.

This is `CategoryTheory.Sheaf.H'` applied to the underlying abelian sheaf of `M`. At `U = ⊤` it
agrees with `Scheme.Modules.Cohomology`, by `Scheme.Modules.cohomologyOnTopIso`. -/
abbrev cohomologyOn (n : ℕ) (U : Opens X) : AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.H'.{u} ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n U

/-- Restriction in cohomology along an inclusion of open subsets. -/
abbrev cohomologyOnRes (n : ℕ) {U V : Opens X} (h : U ≤ V) :
    cohomologyOn M n V ⟶ cohomologyOn M n U :=
  (CategoryTheory.Sheaf.cohomologyPresheaf.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).map (homOfLE h).op

@[simp]
lemma cohomologyOnRes_refl (n : ℕ) (U : Opens X) :
    cohomologyOnRes M n (le_refl U) = 𝟙 _ := by
  dsimp only [cohomologyOnRes]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]

@[simp, reassoc]
lemma cohomologyOnRes_comp (n : ℕ) {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) :
    cohomologyOnRes M n hVW ≫ cohomologyOnRes M n hUV =
      cohomologyOnRes M n (hUV.trans hVW) := by
  dsimp only [cohomologyOnRes]
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, homOfLE_comp]

/-- The cohomology of the whole space is the cohomology of the scheme. -/
noncomputable abbrev cohomologyOnTopIso (n : ℕ) :
    cohomologyOn M n ⊤ ≅ AddCommGrpCat.of (Cohomology M n) :=
  ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheafObjIsoH
    n isTerminalTop

end Opens

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
end
end GeometryLiteralSource001

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.AlgebraicGeometry.Cohomology.Basic"

section GeometryLiteralSource002
/- Original source: TauCeti.CategoryTheory.Sites.ExtensionByZero -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Extension by zero on a lower interval

For a preordered set `P` and `U : P`, a presheaf on `Over U` with values in a category with a
zero object extends to `P` by assigning zero outside the lower interval of `U`. This extension
preserves finite limits and colimits and is left adjoint to restriction. For the open subsets of
a space, sheafifying this construction gives extension by zero along an open inclusion.

The sheaf exactness instance supports the comparison of cohomology on an open with cohomology
of the restricted sheaf in `TauCeti.CategoryTheory.Sites.SheafCohomology.Over`.

## Main declarations

* `TauCeti.CategoryTheory.PresheafExtensionByZero.functor`: extension by zero of presheaves.
* `TauCeti.CategoryTheory.PresheafExtensionByZero.adjunction`: its adjunction to restriction.
* `TauCeti.CategoryTheory.SheafExtensionByZero.preservesFiniteLimits_sheafPullback`: left
  exactness of Mathlib's canonical extension functor for abelian sheaves.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Exercise 1.19.
-/

public section

open CategoryTheory Limits Opposite ZeroObject

namespace TauCeti.CategoryTheory

universe u v w

noncomputable section

variable {P : Type u} [Preorder P] (U : P)

namespace PresheafExtensionByZero

variable {D : Type v} [Category.{w} D] [HasZeroObject D] [HasZeroMorphisms D]

/-- The extension of a presheaf to an object of the ambient preorder. -/
private def obj (F : (Over U)ᵒᵖ ⥤ D) (V : Pᵒᵖ) : D := by
  classical
  exact if h : V.unop ≤ U then F.obj (op (Over.mk (homOfLE h))) else 0

/-- On an object below `U`, extension by zero recovers the original presheaf. -/
private def objIso (F : (Over U)ᵒᵖ ⥤ D) {V : Pᵒᵖ} (h : V.unop ≤ U) :
    obj U F V ≅ F.obj (op (Over.mk (homOfLE h))) := by
  classical
  exact eqToIso (by simp [obj, h])

private def map (F : (Over U)ᵒᵖ ⥤ D) {V W : Pᵒᵖ} (f : V ⟶ W) :
    obj U F V ⟶ obj U F W := by
  classical
  exact if hV : V.unop ≤ U then
    (objIso U F hV).hom ≫
      F.map (Over.homMk (U := Over.mk (homOfLE (le_trans (leOfHom f.unop) hV)))
        (V := Over.mk (homOfLE hV)) f.unop).op ≫
      (objIso U F (le_trans (leOfHom f.unop) hV)).inv
  else 0

/-- Extension by zero of a presheaf on the lower interval of `U`. -/
private def presheaf (F : (Over U)ᵒᵖ ⥤ D) : Pᵒᵖ ⥤ D where
  obj := obj U F
  map := map U F
  map_id V := by
    classical
    by_cases h : V.unop ≤ U
    · have hi : (Over.homMk (U := Over.mk (homOfLE h))
          (V := Over.mk (homOfLE h)) (𝟙 V.unop)).op = 𝟙 _ := by
        apply Quiver.Hom.op_inj
        ext
        rfl
      simp [map, objIso, obj, h, hi]
    · have hz : IsZero (obj U F V) := by
        rw [obj, dite_eq_right h]
        exact isZero_zero _
      exact hz.eq_of_src _ _
  map_comp f g := by
    classical
    rename_i V W Z
    by_cases h : V.unop ≤ U
    · have hW := le_trans (leOfHom f.unop) h
      have hZ := le_trans (leOfHom g.unop) hW
      have hc : (Over.homMk (U := Over.mk (homOfLE hZ))
          (V := Over.mk (homOfLE h)) (g.unop ≫ f.unop)).op =
          (Over.homMk (U := Over.mk (homOfLE hW))
            (V := Over.mk (homOfLE h)) f.unop).op ≫
          (Over.homMk (U := Over.mk (homOfLE hZ))
            (V := Over.mk (homOfLE hW)) g.unop).op := by
        rw [← op_comp]
        congr 1
      simp [map, objIso, obj, h, hW, hc, Category.assoc]
    · simp only [map, dite_eq_right h]
      exact zero_comp.symm

private def mapApp {F G : (Over U)ᵒᵖ ⥤ D} (α : F ⟶ G) (V : Pᵒᵖ) :
    obj U F V ⟶ obj U G V := by
  classical
  exact if h : V.unop ≤ U then
    (objIso U F h).hom ≫ α.app (op (Over.mk (homOfLE h))) ≫ (objIso U G h).inv
  else 0

/-- Extension by zero as a functor between categories of presheaves. -/
def functor : ((Over U)ᵒᵖ ⥤ D) ⥤ (Pᵒᵖ ⥤ D) where
  obj := presheaf U
  map α :=
    { app := mapApp U α
      naturality := by
        intro V W f
        classical
        dsimp only [presheaf]
        by_cases hV : V.unop ≤ U
        · have hW := le_trans (leOfHom f.unop) hV
          simp [map, mapApp, hV, hW, Category.assoc]
        · simp [map, mapApp, hV] }
  map_id F := by
    apply NatTrans.ext
    funext V
    classical
    dsimp only [presheaf, NatTrans.id_app]
    by_cases h : V.unop ≤ U
    · simp [mapApp, h]
    · have hz : IsZero (obj U F V) := by
        rw [obj, dite_eq_right h]
        exact isZero_zero _
      exact hz.eq_of_src _ _
  map_comp α β := by
    apply NatTrans.ext
    funext V
    classical
    dsimp only [presheaf, NatTrans.comp_app]
    by_cases h : V.unop ≤ U <;> simp [mapApp, h, Category.assoc]

/-- Evaluating the extension below `U` is naturally isomorphic to evaluating the original
presheaf. -/
def evaluationIso {V : P} (h : V ≤ U) :
    functor (D := D) U ⋙ (evaluation Pᵒᵖ D).obj (op V) ≅
      (evaluation (Over U)ᵒᵖ D).obj (op (Over.mk (homOfLE h))) :=
  NatIso.ofComponents (fun F ↦ objIso U F h) (by
    intro F G α
    classical
    dsimp only [functor, presheaf, Functor.comp_map, evaluation_obj_map,
      Functor.comp_obj, evaluation_obj_obj]
    rw [mapApp, dite_eq_left h]
    exact (Category.assoc _ _ _).trans (by simp))

private lemma evaluationIso_hom_app (F : (Over U)ᵒᵖ ⥤ D) {V : P} (h : V ≤ U) :
    (evaluationIso U h).hom.app F = (objIso U F h).hom :=
  rfl

/-- The identification `evaluationIso` is compatible with restriction maps below `U`. -/
@[reassoc]
theorem map_comp_evaluationIso_hom_app (F : (Over U)ᵒᵖ ⥤ D) {V W : P} (hWV : W ≤ V)
    (hV : V ≤ U) :
    ((functor U).obj F).map (homOfLE hWV).op ≫ (evaluationIso U (hWV.trans hV)).hom.app F =
      (evaluationIso U hV).hom.app F ≫
        F.map (Over.homMk (U := Over.mk (homOfLE (hWV.trans hV)))
          (V := Over.mk (homOfLE hV)) (homOfLE hWV)).op := by
  classical
  rw [evaluationIso_hom_app, evaluationIso_hom_app]
  dsimp only [functor, presheaf]
  rw [map, dite_eq_left hV]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- The two sides differ only in how their hom types are written, through `evaluation`.
  rfl

/-- Extension by zero vanishes outside the lower interval. -/
theorem isZero_obj_of_not_le (F : (Over U)ᵒᵖ ⥤ D) {V : P}
    (h : ¬ V ≤ U) : IsZero ((functor (D := D) U).obj F |>.obj (op V)) := by
  classical
  dsimp only [functor, presheaf]
  rw [obj, dite_eq_right h]
  exact isZero_zero _

/-- Extension by zero preserves finite limits. -/
instance [HasFiniteLimits D] : PreservesFiniteLimits (functor (D := D) U) := by
  apply preservesFiniteLimits_of_evaluation
  intro V
  classical
  by_cases h : V.unop ≤ U
  · exact preservesFiniteLimits_of_natIso (evaluationIso U h).symm
  · have hz : IsZero (functor (D := D) U ⋙ (evaluation Pᵒᵖ D).obj V) :=
      (Functor.isZero_iff _).mpr (fun F ↦ isZero_obj_of_not_le U F h)
    have := Functor.preservesLimitsOfSize_of_isZero _ hz
    infer_instance

/-- Extension by zero preserves finite colimits. -/
instance [HasFiniteColimits D] : PreservesFiniteColimits (functor (D := D) U) := by
  apply preservesFiniteColimits_of_evaluation
  intro V
  classical
  by_cases h : V.unop ≤ U
  · exact preservesFiniteColimits_of_natIso (evaluationIso U h).symm
  · have hz : IsZero (functor (D := D) U ⋙ (evaluation Pᵒᵖ D).obj V) :=
      (Functor.isZero_iff _).mpr (fun F ↦ isZero_obj_of_not_le U F h)
    have := Functor.preservesColimitsOfSize_of_isZero _ hz
    infer_instance

private def restrictObjIso (F : (Over U)ᵒᵖ ⥤ D) (V : (Over U)ᵒᵖ) :
    obj U F (op V.unop.left) ≅ F.obj V :=
  objIso U F (leOfHom V.unop.hom)

private def restrictHom {F : (Over U)ᵒᵖ ⥤ D} {G : Pᵒᵖ ⥤ D}
    (α : presheaf U F ⟶ G) : F ⟶ (Over.forget U).op ⋙ G where
  app V := (restrictObjIso U F V).inv ≫ α.app (op V.unop.left)
  naturality V W f := by
    have h := α.naturality ((Over.forget U).op.map f)
    dsimp only [presheaf, Functor.op_map, Functor.op_obj, Over.forget_map,
      Over.forget_obj] at h
    rw [map, dite_eq_left (leOfHom V.unop.hom)] at h
    dsimp only [restrictObjIso, Functor.comp_map, Functor.op_map, Over.forget_map]
    simp only [Category.assoc] at h ⊢
    exact ((Iso.eq_inv_comp _).mpr h).trans (Category.assoc _ _ _).symm

private def extendApp {F : (Over U)ᵒᵖ ⥤ D} {G : Pᵒᵖ ⥤ D}
    (α : F ⟶ (Over.forget U).op ⋙ G) (V : Pᵒᵖ) : obj U F V ⟶ G.obj V := by
  classical
  exact if h : V.unop ≤ U then (objIso U F h).hom ≫ α.app (op (Over.mk (homOfLE h)))
    else 0

private def extendHom {F : (Over U)ᵒᵖ ⥤ D} {G : Pᵒᵖ ⥤ D}
    (α : F ⟶ (Over.forget U).op ⋙ G) : presheaf U F ⟶ G where
  app := extendApp U α
  naturality V W f := by
    classical
    dsimp only [presheaf]
    by_cases hV : V.unop ≤ U
    · have hW := le_trans (leOfHom f.unop) hV
      simp only [map, extendApp, dite_eq_left hV, dite_eq_left hW, Category.assoc,
        Iso.inv_hom_id_assoc]
      exact congrArg ((objIso U F hV).hom ≫ ·)
        (α.naturality (Over.homMk (U := Over.mk (homOfLE hW))
          (V := Over.mk (homOfLE hV)) f.unop).op)
    · simp only [map, extendApp, dite_eq_right hV, zero_comp]

/-- Extension by zero is left adjoint to restriction to the lower interval. -/
def adjunction : functor (D := D) U ⊣
    (Functor.whiskeringLeft (Over U)ᵒᵖ Pᵒᵖ D).obj (Over.forget U).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv F G :=
        { toFun := restrictHom U
          invFun := extendHom U
          left_inv α := by
            apply NatTrans.ext
            funext V
            classical
            by_cases h : V.unop ≤ U
            · dsimp only [extendHom, restrictHom]
              simp only [extendApp, dite_eq_left h, restrictObjIso]
              exact (objIso U F h).hom_inv_id_assoc (α.app V)
            · exact (isZero_obj_of_not_le U F h).eq_of_src _ _
          right_inv α := by
            apply NatTrans.ext
            funext V
            classical
            dsimp only [restrictHom, extendHom]
            simp only [extendApp, dite_eq_left (leOfHom V.unop.hom), restrictObjIso]
            exact (objIso U F (V := op V.unop.left) (leOfHom V.unop.hom)).inv_hom_id_assoc
              (α.app V) }
      homEquiv_naturality_left_symm := by
        intro F F' G α β
        -- Unfold the `Equiv.mk` above and read `presheaf U F` as `(functor U).obj F`. The two
        -- agree only by unfolding `functor`, so `simp` cannot rewrite the application.
        change extendHom U (α ≫ β) = (functor (D := D) U).map α ≫ extendHom U β
        apply NatTrans.ext
        funext V
        classical
        by_cases h : V.unop ≤ U
        · simp [extendHom, extendApp, functor, mapApp, presheaf, h, Category.assoc]
        · exact (isZero_obj_of_not_le U F h).eq_of_src _ _
      homEquiv_naturality_right := by
        intro F G G' α β
        apply NatTrans.ext
        funext V
        exact (Category.assoc _ _ _).symm }

end PresheafExtensionByZero

namespace SheafExtensionByZero

variable (J : GrothendieckTopology P) [HasSheafify J AddCommGrpCat.{u}]

private def extension : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafToPresheaf (J.over U) _ ⋙ PresheafExtensionByZero.functor U ⋙ presheafToSheaf J _

private def extensionAdjunction : extension U J ⊣ J.overPullback AddCommGrpCat.{u} U :=
  ((PresheafExtensionByZero.adjunction U).comp
    (sheafificationAdjunction J AddCommGrpCat.{u})).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf (J.over U) _) (Functor.FullyFaithful.id _)
      (Iso.refl _) (Iso.refl _)

private instance : PreservesFiniteLimits (extension U J) := by
  unfold extension
  infer_instance

/-- On a preorder site, the left adjoint to restriction to a lower interval is exact.
In particular, this applies to extension by zero along an open inclusion. -/
instance preservesFiniteLimits_sheafPullback :
    PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J) :=
  preservesFiniteLimits_of_natIso
    ((extensionAdjunction U J).leftAdjointUniq
      ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{u} (J.over U) J))

end SheafExtensionByZero

end

end TauCeti.CategoryTheory
end
end GeometryLiteralSource002

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.ExtensionByZero"

section GeometryLiteralSource003
/- Original source: TauCeti.Algebra.Homology.Ext.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Transport and exactness lemmas for `Ext` groups

This file collects general `Ext` API that Mathlib does not state in this form:

* the transport of `Extⁿ(X, Y)` along isomorphisms `X ≅ X'` and `Y ≅ Y'`, additively as
  `TauCeti.extAddEquivOfIso` and `R`-linearly as `TauCeti.extLinearEquivOfIso`;
* in degree zero, composition with `CategoryTheory.Abelian.Ext.mk₀ f` corresponds under
  `CategoryTheory.Abelian.Ext.addEquiv₀` to composition with `f`
  (`TauCeti.ext_addEquiv₀_mk₀_comp` and `TauCeti.ext_addEquiv₀_comp_mk₀`);
* the vanishing of `Extⁿ(X, Y)` when either of the two objects is a zero object;
* short exact cokernel sequences, the cokernel sequence of the chosen embedding into an injective
  object with the morphisms of such sequences extending a given morphism
  (`TauCeti.injectiveCokernelSequenceMap`), and a dimension-shift criterion for vanishing of the
  next `Ext` group;
* Mathlib's long exact `Ext` sequences of a short exact sequence `S`, repackaged as
  `Function.Exact` statements about the composition maps: `TauCeti.exact_postcomp` and
  `TauCeti.exact_precomp` for `CategoryTheory.Abelian.Ext.postcomp` and
  `CategoryTheory.Abelian.Ext.precomp`, and `TauCeti.exact_postcompOfLinear` and
  `TauCeti.exact_precompOfLinear` for their `R`-linear forms; `TauCeti.exact_precomp₁` and
  `TauCeti.exact_precompOfLinear₁` (respectively `TauCeti.exact_precomp₃` and
  `TauCeti.exact_precompOfLinear₃`) are the same repackaging one step further along the
  contravariant sequence, where the outgoing (respectively incoming) map is precomposition with
  the extension class;
* extension of morphisms along a short exact sequence `S` whose cokernel `S.X₃` has
  `Ext¹(S.X₃, Y) = 0` (`CategoryTheory.ShortComplex.ShortExact.exists_f_comp_eq_of_ext_eq_zero`).

The exactness statements are `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` and
`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂` with the vanishing of the composite
supplied, which is what makes them usable with the `Function.Exact` API.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4--2.7, for `Ext` and its long
  exact sequences.
-/

public section

namespace TauCeti

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-! ### Transport along isomorphisms -/

variable {X X' Y Y' : C}

/-- Isomorphisms `e : X ≅ X'` and `f : Y ≅ Y'` induce an isomorphism
`Extⁿ(X, Y) ≃ Extⁿ(X', Y')`, by composing with `e.inv` on the left and with `f.hom` on the right.
This is the action of an isomorphism through `CategoryTheory.Abelian.extFunctor`, spelled out so
that `TauCeti.extLinearEquivOfIso` can refine it to an `R`-linear equivalence. -/
noncomputable def extAddEquivOfIso (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w} X' Y' n where
  toFun x := (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun y := (Ext.mk₀ e.hom).comp (y.comp (Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

/-- `TauCeti.extAddEquivOfIso` composes with `e.inv` and `f.hom`. -/
@[simp]
theorem extAddEquivOfIso_apply (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extAddEquivOfIso e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

/-- The `R`-linear refinement of `TauCeti.extAddEquivOfIso`: in an `R`-linear abelian category,
isomorphisms `X ≅ X'` and `Y ≅ Y'` identify `Extⁿ(X, Y)` and `Extⁿ(X', Y')` as `R`-modules. -/
noncomputable def extLinearEquivOfIso (R : Type t) [Ring R] [Linear R C] (e : X ≅ X')
    (f : Y ≅ Y') (n : ℕ) : Ext.{w} X Y n ≃ₗ[R] Ext.{w} X' Y' n where
  __ := extAddEquivOfIso e f n
  map_smul' r x := by simp [extAddEquivOfIso_apply]

/-- `TauCeti.extLinearEquivOfIso` composes with `e.inv` and `f.hom`. -/
@[simp]
theorem extLinearEquivOfIso_apply (R : Type t) [Ring R] [Linear R C] (e : X ≅ X')
    (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extLinearEquivOfIso R e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

/-! ### Composition in degree zero -/

/-- In degree zero, precomposing with `Ext.mk₀ f` is precomposing with `f` in the category. -/
theorem ext_addEquiv₀_mk₀_comp {Z : C} (f : X ⟶ Y) (x : Ext.{w} Y Z 0) :
    Ext.addEquiv₀ ((Ext.mk₀ f).comp x (zero_add 0)) = f ≫ Ext.addEquiv₀ x := by
  apply (Ext.mk₀_bijective _ _).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

/-- In degree zero, postcomposing with `Ext.mk₀ f` is postcomposing with `f` in the category. -/
theorem ext_addEquiv₀_comp_mk₀ {Z : C} (x : Ext.{w} X Y 0) (f : Y ⟶ Z) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective _ _).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

/-! ### Vanishing against a zero object -/

/-- There is no `Ext` out of a zero object, in any degree. -/
theorem subsingleton_ext_of_isZero_left (hX : IsZero X) (Y : C) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Ext.mk₀_id_comp x, hX.eq_of_src (𝟙 X) 0, Ext.mk₀_zero, Ext.zero_comp]

/-- There is no `Ext` into a zero object, in any degree. -/
theorem subsingleton_ext_of_isZero_right (X : C) (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Ext.comp_mk₀_id x, hY.eq_of_src (𝟙 Y) 0, Ext.mk₀_zero, Ext.comp_zero]

/-! ### Dimension shifting along an injective embedding -/

section DimensionShift

/-- The middle object in a cokernel sequence is injective when the target of its first map is. -/
instance injective_cokernelSequence_X₂ {X Y : C} (f : X ⟶ Y) [Injective Y] :
    Injective (ShortComplex.cokernelSequence f).X₂ :=
  (inferInstance : Injective Y)

/-- A dimension-shift criterion along a short exact sequence with injective middle term: if
composition with its extension class vanishes, then the next `Ext` group is subsingleton. -/
lemma subsingleton_ext_succ_of_comp_extClass_eq_zero {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] (X : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X S.X₃ n, x₃.comp hS.extClass rfl = 0) :
    Subsingleton (Ext X S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS y
    (Ext.eq_zero_of_injective _) rfl
  exact hzero x₃

variable [EnoughInjectives C]

/-- The cokernel sequence `Y ⟶ Injective.under Y ⟶ cokernel (Injective.ι Y)` of the chosen
embedding of an object into an injective object. It is written with `ShortComplex.mk`, so that
its three objects are reducibly `Y`, `Injective.under Y` and `cokernel (Injective.ι Y)`. -/
noncomputable abbrev injectiveCokernelSequence (Y : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y)) (cokernel.condition _)

omit [HasExt C] in
/-- The cokernel sequence of the chosen embedding into an injective object is short exact. -/
lemma injectiveCokernelSequence_shortExact (Y : C) :
    (injectiveCokernelSequence Y).ShortExact :=
  cokernelSequence_shortExact _

omit [HasExt C] in
/-- A morphism `f : Y ⟶ Y'` extends to a morphism between the cokernel sequences of the chosen
embeddings of `Y` and `Y'` into injective objects. Its middle component is a factorization of
`f` followed by the embedding of `Y'` through the embedding of `Y`, which exists because the
target is injective; its last component is the induced map of cokernels. The extension is a
choice, not unique. -/
noncomputable def injectiveCokernelSequenceMap {Y Y' : C} (f : Y ⟶ Y') :
    injectiveCokernelSequence Y ⟶ injectiveCokernelSequence Y' where
  τ₁ := f
  τ₂ := Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y)
  τ₃ := cokernel.map (Injective.ι Y) (Injective.ι Y') f
    (Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y))
    (Injective.comp_factorThru _ _)
  comm₁₂ := (Injective.comp_factorThru _ _).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

omit [HasExt C] in
@[simp]
lemma injectiveCokernelSequenceMap_τ₁ {Y Y' : C} (f : Y ⟶ Y') :
    (injectiveCokernelSequenceMap f).τ₁ = f :=
  (rfl)

omit [HasExt C] in
@[simp]
lemma injectiveCokernelSequenceMap_τ₂ {Y Y' : C} (f : Y ⟶ Y') :
    (injectiveCokernelSequenceMap f).τ₂ =
      Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y) :=
  (rfl)

omit [HasExt C] in
@[simp]
lemma injectiveCokernelSequenceMap_τ₃ {Y Y' : C} (f : Y ⟶ Y') :
    (injectiveCokernelSequenceMap f).τ₃ =
      cokernel.map (Injective.ι Y) (Injective.ι Y') f
        (Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y))
        (Injective.comp_factorThru _ _) :=
  (rfl)

/-- The dimension-shift criterion specialised to the chosen embedding into an injective object. -/
lemma subsingleton_ext_succ_of_injectiveCokernelSequence (X Y : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X (injectiveCokernelSequence Y).X₃ n,
      x₃.comp (injectiveCokernelSequence_shortExact Y).extClass rfl = 0) :
    Subsingleton (Ext X Y (n + 1)) :=
  subsingleton_ext_succ_of_comp_extClass_eq_zero
    (injectiveCokernelSequence_shortExact Y) X n hzero

end DimensionShift

/-! ### The long exact sequences as `Function.Exact` statements -/

variable {S : ShortComplex C}

/-- Exactness of `Extⁿ(X, S.X₁) → Extⁿ(X, S.X₂) → Extⁿ(X, S.X₃)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` packaged as a
`Function.Exact` statement about the postcomposition maps. -/
theorem exact_postcomp (hS : S.ShortExact) (X : C) (n : ℕ) :
    Function.Exact (Ext.postcomp (Ext.mk₀ S.f) X (add_zero n))
      (Ext.postcomp (Ext.mk₀ S.g) X (add_zero n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.covariant_sequence_exact₂ X hS x₂ hx, by
    rintro ⟨x₁, rfl⟩
    simp [S.zero]⟩

/-- Exactness of `Extⁿ(S.X₃, Y) → Extⁿ(S.X₂, Y) → Extⁿ(S.X₁, Y)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂` packaged as
a `Function.Exact` statement about the precomposition maps. -/
theorem exact_precomp (hS : S.ShortExact) (Y : C) (n : ℕ) :
    Function.Exact (Ext.precomp (Ext.mk₀ S.g) Y (zero_add n))
      (Ext.precomp (Ext.mk₀ S.f) Y (zero_add n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.contravariant_sequence_exact₂ hS Y x₂ hx, by
    rintro ⟨x₃, rfl⟩
    simp [S.zero]⟩

/-- The linear postcomposition map has `CategoryTheory.Abelian.Ext.postcomp` as its underlying
function. -/
@[simp]
theorem coe_postcompOfLinear (R : Type t) [CommRing R] [Linear R C] {Y Z : C} {n a b : ℕ}
    (beta : Ext.{w} Y Z n) (X : C) (h : a + n = b) :
    ⇑(Ext.postcompOfLinear beta R X h) = Ext.postcomp beta X h :=
  rfl

/-- The linear precomposition map has `CategoryTheory.Abelian.Ext.precomp` as its underlying
function. -/
@[simp]
theorem coe_precompOfLinear (R : Type t) [CommRing R] [Linear R C] {X Y : C} {n a b : ℕ}
    (alpha : Ext.{w} X Y n) (Z : C) (h : n + a = b) :
    ⇑(Ext.precompOfLinear alpha R Z h) = Ext.precomp alpha Z h :=
  rfl

/-- The `R`-linear form of `TauCeti.exact_postcomp`. -/
theorem exact_postcompOfLinear (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (X : C)
    (n : ℕ) :
    Function.Exact (Ext.postcompOfLinear (Ext.mk₀ S.f) R X (add_zero n))
      (Ext.postcompOfLinear (Ext.mk₀ S.g) R X (add_zero n)) := by
  simp only [coe_postcompOfLinear]
  exact exact_postcomp hS X n

/-- The `R`-linear form of `TauCeti.exact_precomp`. -/
theorem exact_precompOfLinear (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n : ℕ) :
    Function.Exact (Ext.precompOfLinear (Ext.mk₀ S.g) R Y (zero_add n))
      (Ext.precompOfLinear (Ext.mk₀ S.f) R Y (zero_add n)) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp hS Y n

/-- Exactness of `Extⁿ⁰(S.X₁, Y) → Extⁿ¹(S.X₃, Y) → Extⁿ¹(S.X₂, Y)` at the middle term, for a
short exact sequence `S` and `n₁ = 1 + n₀`. The first map is precomposition with the extension
class of `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃'` with its
`AddCommGrpCat` wrapper removed. -/
theorem exact_precomp₃ (hS : S.ShortExact) (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precomp hS.extClass Y h)
      (Ext.precomp (Ext.mk₀ S.g) Y (zero_add n₁)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.contravariant_sequence_exact₃' hS Y n₀ n₁ h)

/-- The `R`-linear form of `TauCeti.exact_precomp₃`. -/
theorem exact_precompOfLinear₃ (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precompOfLinear hS.extClass R Y h)
      (Ext.precompOfLinear (Ext.mk₀ S.g) R Y (zero_add n₁)) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp₃ hS Y n₀ n₁ h

/-- Exactness of `Extⁿ⁰(S.X₂, Y) → Extⁿ⁰(S.X₁, Y) → Extⁿ¹(S.X₃, Y)` at the middle term, for a
short exact sequence `S` and `n₁ = 1 + n₀`. The second map is precomposition with the extension
class of `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'` with its
`AddCommGrpCat` wrapper removed. -/
theorem exact_precomp₁ (hS : S.ShortExact) (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precomp (Ext.mk₀ S.f) Y (zero_add n₀))
      (Ext.precomp hS.extClass Y h) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.contravariant_sequence_exact₁' hS Y n₀ n₁ h)

/-- The `R`-linear form of `TauCeti.exact_precomp₁`. -/
theorem exact_precompOfLinear₁ (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precompOfLinear (Ext.mk₀ S.f) R Y (zero_add n₀))
      (Ext.precompOfLinear hS.extClass R Y h) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp₁ hS Y n₀ n₁ h

end TauCeti

namespace CategoryTheory.ShortComplex.ShortExact

open _root_.CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {S : ShortComplex C}
  (hS : S.ShortExact)
include hS

/-- **Extension along a monomorphism with orthogonal cokernel**: if `S` is short exact and
`Ext¹(S.X₃, Y) = 0`, every morphism `S.X₁ ⟶ Y` extends along `S.f`. -/
lemma exists_f_comp_eq_of_ext_eq_zero {Y : C} (h : ∀ x : Ext.{w} S.X₃ Y 1, x = 0)
    (ψ : S.X₁ ⟶ Y) : ∃ g : S.X₂ ⟶ Y, S.f ≫ g = ψ := by
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ ψ) (n₁ := 1) rfl (h _)
  refine ⟨Ext.addEquiv₀ x, Ext.homEquiv₀.symm.injective ?_⟩
  rw [← Ext.mk₀_addEquiv₀_apply x, Ext.mk₀_comp_mk₀] at hx
  exact hx

end CategoryTheory.ShortComplex.ShortExact
end
end GeometryLiteralSource003

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Homology.Ext.Basic"

section GeometryLiteralSource004
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The free abelian sheaf generated by an object of a site

The source object in Mathlib's `CategoryTheory.Sheaf.H'` is obtained by applying the free abelian
group functor to a representable presheaf and then sheafifying. This file packages those objects as
a functor of the object of the site and records their universal property and its naturality.
In degree zero this identifies the cohomology presheaf with the underlying presheaf of sections,
naturally both in the object of the site and in the coefficient sheaf.

## Main declarations

* `TauCeti.CategoryTheory.freeYonedaSheafFunctor J`, the functor sending `U` to the sheafification
  of the free abelian presheaf on `yoneda.obj U`;
* `TauCeti.CategoryTheory.sheafH'_eq`, identifying Mathlib's `Sheaf.H'` with `Ext` from that
  functor, the same identification `CategoryTheory.Sheaf.H'AddEquivExt` as an additive
  equivalence, and `CategoryTheory.Sheaf.cohomologyPresheaf_map_apply`, identifying the
  restriction maps of the cohomology presheaf with precomposition by the induced maps of free
  abelian sheaves;
* `TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv`, the additive equivalence between
  morphisms from that sheaf to `F` and sections of `F` over `U`, and
  `TauCeti.CategoryTheory.freeYonedaSheafCorepresentableBy`, the same universal property phrased
  as a corepresentation of the sections functor;
* `TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv F U`, identifying degree-zero cohomology
  over `U` with sections, and `TauCeti.CategoryTheory.cohomologyPresheafZeroIso F`, identifying
  degree-zero cohomology with sections and their restriction maps, and
  `CategoryTheory.Sheaf.cohomologyPresheaf_zero_map_surjective`, transferring surjectivity of a
  restriction map of sections to degree-zero cohomology;
* `TauCeti.CategoryTheory.mono_freeYonedaSheafFunctor_map`, saying that a monomorphism of site
  objects induces a monomorphism between the corresponding free abelian sheaves.

The equivalence composes the sheafification adjunction, the free-forgetful adjunction for abelian
groups, and the Yoneda equivalence. This is the same model of the free abelian sheaf used
definitionally by Mathlib's `Sheaf.cohomologyPresheafFunctor`.
-/

public section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

noncomputable section

variable [HasSheafify J AddCommGrpCat.{v}]

/-- The sheafification of the free abelian presheaf on `yoneda.obj U`, functorial in `U`. This is
the source-object functor used in Mathlib's definition of `Sheaf.H'`. -/
noncomputable def freeYonedaSheafFunctor :
    C ⥤ _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{v}

/-- Mathlib's cohomology presheaf is the Ext bifunctor from free abelian representable
sheaves. -/
lemma cohomologyPresheafFunctor_eq [HasExt.{w} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n =
      Functor.flip ((freeYonedaSheafFunctor J).op ⋙ Abelian.extFunctor n) :=
  (rfl)

/-- Mathlib's sheaf cohomology over an object of a site is `Ext` from the corresponding free
abelian sheaf. -/
lemma sheafH'_eq [HasExt.{w} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    _root_.CategoryTheory.Sheaf.H'.{w} F n U =
      AddCommGrpCat.of (Abelian.Ext.{w} ((freeYonedaSheafFunctor J).obj U) F n) :=
  (rfl)

/-- Morphisms from the free abelian sheaf on `U` to an abelian sheaf `F` are additively equivalent
to the sections of `F` over `U`. -/
def freeYonedaSheafSectionsEquiv (U : C)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) :
    ((freeYonedaSheafFunctor J).obj U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ _).trans
    { ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{v}).homEquiv _ _).trans yonedaEquiv with
    map_add' := by
      intro f g
      rfl }

private def freeYonedaSheafSectionsFormula (U : C)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})
    (f : (freeYonedaSheafFunctor J).obj U ⟶ F) : F.obj.obj (op U) :=
  yonedaEquiv
    ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{v}).homEquiv _ _
      ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _ f))

private lemma freeYonedaSheafSectionsEquiv_apply (U : C)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})
    (f : (freeYonedaSheafFunctor J).obj U ⟶ F) :
    freeYonedaSheafSectionsEquiv J U F f = freeYonedaSheafSectionsFormula J U F f :=
  (rfl)

/-- The equivalence `freeYonedaSheafSectionsEquiv` is natural in the coefficient sheaf. -/
@[simp]
lemma freeYonedaSheafSectionsEquiv_naturality_right {U : C}
    {F G : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}}
    (f : (freeYonedaSheafFunctor J).obj U ⟶ F) (g : F ⟶ G) :
    freeYonedaSheafSectionsEquiv J U G (f ≫ g) =
      g.hom.app (op U) (freeYonedaSheafSectionsEquiv J U F f) := by
  rw [freeYonedaSheafSectionsEquiv_apply, freeYonedaSheafSectionsEquiv_apply]
  dsimp only [freeYonedaSheafSectionsFormula, freeYonedaSheafFunctor, Functor.comp_obj] at f ⊢
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    yonedaEquiv_comp]
  rfl

/-- The free abelian sheaf on `U` corepresents the functor of sections over `U`. -/
def freeYonedaSheafCorepresentableBy (U : C) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op U) ⋙ forget AddCommGrpCat).CorepresentableBy
      ((freeYonedaSheafFunctor J).obj U) where
  homEquiv := (freeYonedaSheafSectionsEquiv J U _).toEquiv
  homEquiv_comp g f := freeYonedaSheafSectionsEquiv_naturality_right J f g

/-- The equivalence `freeYonedaSheafSectionsEquiv` is natural in the object of the site:
precomposing with the map induced by `i : U ⟶ V` is restricting sections along `i`. -/
lemma freeYonedaSheafSectionsEquiv_naturality_left {U V : C} (i : U ⟶ V)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})
    (f : (freeYonedaSheafFunctor J).obj V ⟶ F) :
    freeYonedaSheafSectionsEquiv J U F ((freeYonedaSheafFunctor J).map i ≫ f) =
      F.obj.map i.op (freeYonedaSheafSectionsEquiv J V F f) := by
  rw [freeYonedaSheafSectionsEquiv_apply, freeYonedaSheafSectionsEquiv_apply]
  dsimp only [freeYonedaSheafSectionsFormula, freeYonedaSheafFunctor, Functor.comp_obj,
    Functor.comp_map] at f ⊢
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

section

variable {J} [HasExt.{w} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})]

/-- Mathlib's sheaf cohomology `Hⁿ(U, F)` is additively equivalent to `Ext` from the free abelian
sheaf on `U`. This is the identity, and transports elements between the two forms. -/
def _root_.CategoryTheory.Sheaf.H'AddEquivExt
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    F.H' n U ≃+ Abelian.Ext ((freeYonedaSheafFunctor J).obj U) F n :=
  AddEquiv.refl _

/-- The restriction maps of Mathlib's cohomology presheaf are precomposition with the induced maps
of free abelian sheaves. -/
lemma _root_.CategoryTheory.Sheaf.cohomologyPresheaf_map_apply
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) {U V : C} (i : U ⟶ V) (n : ℕ)
    (x : F.H' n V) :
    F.H'AddEquivExt n U ((F.cohomologyPresheaf n).map i.op x) =
      (Abelian.Ext.mk₀ ((freeYonedaSheafFunctor J).map i)).comp (F.H'AddEquivExt n V x)
        (zero_add n) :=
  (rfl)

/-- If restriction of sections along `i : U ⟶ V` is surjective, then so is the restriction map
`H⁰(V, F) ⟶ H⁰(U, F)` of the cohomology presheaf. -/
theorem _root_.CategoryTheory.Sheaf.cohomologyPresheaf_zero_map_surjective
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) {U V : C} (i : U ⟶ V)
    (hF : Function.Surjective (F.obj.map i.op)) :
    Function.Surjective ((F.cohomologyPresheaf 0).map i.op) := by
  intro y
  obtain ⟨t, ht⟩ :=
    hF (freeYonedaSheafSectionsEquiv J U F (Abelian.Ext.addEquiv₀ (F.H'AddEquivExt 0 U y)))
  refine ⟨(F.H'AddEquivExt 0 V).symm
    (Abelian.Ext.mk₀ ((freeYonedaSheafSectionsEquiv J V F).symm t)), ?_⟩
  apply (F.H'AddEquivExt 0 U).injective
  refine (F.cohomologyPresheaf_map_apply i 0 _).trans ?_
  rw [AddEquiv.apply_symm_apply, Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_addEquiv₀_apply
    (F.H'AddEquivExt 0 U y)]
  congr 1
  apply (freeYonedaSheafSectionsEquiv J U F).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_left, AddEquiv.apply_symm_apply]
  exact ht

end

section

variable {J} [HasExt.{v} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})]

/-- Degree-zero cohomology over an object of a site is the group of sections over that
object. -/
def cohomologyZeroSectionsEquiv (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  Abelian.Ext.addEquiv₀.trans (freeYonedaSheafSectionsEquiv J U F)

/-- The degree-zero identification with sections commutes with restriction. -/
@[simp]
lemma cohomologyZeroSectionsEquiv_naturality_left
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) {U V : C} (i : U ⟶ V)
    (x : F.H' 0 V) :
    cohomologyZeroSectionsEquiv F U ((F.cohomologyPresheaf 0).map i.op x) =
      F.obj.map i.op (cohomologyZeroSectionsEquiv F V x) :=
  (congrArg (freeYonedaSheafSectionsEquiv J U F)
    ((congrArg Abelian.Ext.addEquiv₀ (F.cohomologyPresheaf_map_apply i 0 x)).trans
      (ext_addEquiv₀_mk₀_comp _ _))).trans
    (freeYonedaSheafSectionsEquiv_naturality_left J i F _)

/-- The degree-zero identification with sections commutes with maps of coefficient sheaves. -/
@[simp]
lemma cohomologyZeroSectionsEquiv_naturality_right
    {F G : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    cohomologyZeroSectionsEquiv G U
        (((_root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      f.hom.app (op U) (cohomologyZeroSectionsEquiv F U x) := by
  have h : Abelian.Ext.addEquiv₀
      (((_root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      Abelian.Ext.addEquiv₀ x ≫ f := by
    -- Mathlib has no coefficient-map computation lemma for `H'`; this identifies that map
    -- with Ext postcomposition, without unfolding the Ext functor implementation.
    change Abelian.Ext ((freeYonedaSheafFunctor J).obj U) F 0 at x
    exact ext_addEquiv₀_comp_mk₀ x f
  exact (congrArg (freeYonedaSheafSectionsEquiv J U G) h).trans
    (freeYonedaSheafSectionsEquiv_naturality_right J _ f)

/-- The degree-zero cohomology presheaf is canonically the underlying presheaf. -/
def cohomologyPresheafZeroIso (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) :
    F.cohomologyPresheaf 0 ≅ F.obj :=
  NatIso.ofComponents (fun U ↦ (cohomologyZeroSectionsEquiv F U.unop).toAddCommGrpIso)
    (fun i ↦ by ext x; exact cohomologyZeroSectionsEquiv_naturality_left F i.unop x)

@[simp]
lemma cohomologyPresheafZeroIso_hom_app_apply
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) (U : C) (x : F.H' 0 U) :
    (cohomologyPresheafZeroIso F).hom.app (op U) x = cohomologyZeroSectionsEquiv F U x :=
  (rfl)

@[simp]
lemma cohomologyPresheafZeroIso_inv_app_apply
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) (U : C) (s : F.obj.obj (op U)) :
    (cohomologyPresheafZeroIso F).inv.app (op U) s = (cohomologyZeroSectionsEquiv F U).symm s :=
  (rfl)

end

end

variable [HasSheafify J AddCommGrpCat.{v}]

/-- A monomorphism of site objects induces a monomorphism between the corresponding free abelian
sheaves. -/
instance mono_freeYonedaSheafFunctor_map {U V : C} (i : U ⟶ V) [Mono i] :
    Mono ((freeYonedaSheafFunctor J).map i) := by
  dsimp only [freeYonedaSheafFunctor, Functor.comp_map]
  infer_instance

end CategoryTheory

end TauCeti
end
end GeometryLiteralSource004

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda"

