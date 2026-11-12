module

public import ToricPower.CellularPointAdjunction
public import ToricPower.CellularVectorCover
public import ToricPower.CellularHomDiagram
public import ToricPower.LinearDualHomology
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Scalar Serre pairing at an actual incidence object

The co-representable injective is the full function space on incoming
incidences. Evaluation gives the scalar-linear pairing with the genuine
representable. No finiteness assumption on the coefficient diagram is
made. The ordinary inverse Nakayama functor below is the literal Hom
diagram from these injectives; its derived properties are proved separately.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

abbrev pointCorepresentable (c : C) : C ⥤ ModuleCat.{u} k :=
  pointCoinduced k c (ModuleCat.of k k)

instance pointCorepresentable_injective (c : C) :
    Injective (pointCorepresentable k c) := by
  letI : Injective (ModuleCat.of k k) := vectorSpace_injective k _
  infer_instance

/-- The coinduction adjunction, retaining its scalar-linear structure. -/
def pointCoinducedHomLinearEquiv (F : C ⥤ ModuleCat.{u} k) (c : C)
    (M : ModuleCat.{u} k) :
    (F ⟶ pointCoinduced k c M) ≃ₗ[k] (F.obj c →ₗ[k] M) where
  toEquiv := ((pointCoinducedAdjunction k c).homEquiv F M).symm.trans
    (ModuleCat.homLinearEquiv (R := k) (S := k) (M := F.obj c) (N := M)).toEquiv
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

/-- The actual pointwise Serre pairing, valid for arbitrary vector spaces. -/
def pointSerreLinearEquiv (c : C) (F : C ⥤ ModuleCat.{u} k) :
    (F ⟶ pointCorepresentable k c) ≃ₗ[k]
      Module.Dual k (representable k c ⟶ F) :=
  (pointCoinducedHomLinearEquiv k F c (ModuleCat.of k k)).trans
    (representableHomLinearEquiv k F c).dualMap

@[simp]
theorem pointSerreLinearEquiv_apply (c : C) (F : C ⥤ ModuleCat.{u} k)
    (f : F ⟶ pointCorepresentable k c) (g : representable k c ⟶ F) :
    pointSerreLinearEquiv k c F f g =
      f.app c (g.app c (ModuleCat.freeMk (𝟙 c))) (𝟙 c) := rfl

theorem pointSerreLinearEquiv_naturality (c : C)
    {E F : C ⥤ ModuleCat.{u} k} (a : E ⟶ F)
    (f : F ⟶ pointCorepresentable k c) :
    pointSerreLinearEquiv k c E (a ≫ f) =
      (pointSerreLinearEquiv k c F f).comp
        (Linear.rightComp k (representable k c) a) := by
  apply LinearMap.ext
  intro g
  rfl

def pointSerreComponent (c : C) (F : C ⥤ ModuleCat.{u} k) :
    ModuleCat.of k (F ⟶ pointCorepresentable k c) ≅
      (scalarDual k).obj (op (ModuleCat.of k (representable k c ⟶ F))) :=
  ((pointSerreLinearEquiv k c F).trans
    (ModuleCat.homLinearEquiv (R := k) (S := k)
      (M := ModuleCat.of k (representable k c ⟶ F))
      (N := ModuleCat.of k k)).symm).toModuleIso

/-- Naturality concerns all morphisms of the coefficient diagram. -/
def pointSerreNatIso (c : C) :
    (linearYoneda k (C ⥤ ModuleCat.{u} k)).obj (pointCorepresentable k c) ≅
      ((linearCoyoneda k (C ⥤ ModuleCat.{u} k)).obj
        (op (representable k c))).op ⋙ scalarDual k :=
  NatIso.ofComponents (fun F => pointSerreComponent k c F.unop) (by
    intro E F a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    rfl)

/-- The contravariant diagram of actual co-representable injectives. -/
def pointCorepresentableDiagram : Cᵒᵖ ⥤ C ⥤ ModuleCat.{u} k where
  obj c := pointCorepresentable k c.unop
  map f :=
    { app d := ModuleCat.ofHom
        { toFun := fun x a => x (a ≫ f.unop)
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      naturality {d e} a := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext b
        change x (a ≫ b ≫ f.unop) = x ((a ≫ b) ≫ f.unop)
        rw [Category.assoc] }
  map_id c := by
    apply NatTrans.ext
    funext d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change x (a ≫ 𝟙 c.unop) = x a
    rw [Category.comp_id]
  map_comp f g := by
    apply NatTrans.ext
    funext d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change x (a ≫ g.unop ≫ f.unop) = x ((a ≫ g.unop) ≫ f.unop)
    rw [Category.assoc]

/-- The ordinary inverse Nakayama functor; no derived assertion is built
into its definition. -/
def inverseNakayama : (C ⥤ ModuleCat.{u} k) ⥤ C ⥤ ModuleCat.{u} k :=
  homDiagram k (pointCorepresentableDiagram k)

instance inverseNakayama_additive : (inverseNakayama k (C := C)).Additive :=
  inferInstanceAs ((homDiagram k (pointCorepresentableDiagram k (C := C))).Additive)

instance inverseNakayama_linear : (inverseNakayama k (C := C)).Linear k :=
  inferInstanceAs ((homDiagram k (pointCorepresentableDiagram k (C := C))).Linear k)

end ToricPower.Cellular

end
