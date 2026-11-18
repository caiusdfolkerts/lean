module

public import ToricPower.FiniteAffineIntersectionSections
public import ToricPower.SchemeAffineLinear
public import ToricPower.CechFunctorLinear

/-!
# Actual scalar-linear sections of a direct image

The literal section identification preserves the base-field action and
all restriction and coefficient maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace ToricPower

universe u

namespace FiniteCover

instance schemeBaseSections_linear (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (U : X.Opens) :
    (schemeBaseSections k X U).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Scheme.Modules.base_smul_app k X r f U x

end FiniteCover

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

/-- The literal section identification with its actual base-field action. -/
def pushforwardBaseSectionsLinearEquiv (M : X.Modules) (U : Y.Opens) :
    (FiniteCover.schemeBaseSections k Y U).obj ((Scheme.Modules.pushforward f).obj M) ≃ₗ[k]
      (FiniteCover.schemeBaseSections k X (f ⁻¹ᵁ U)).obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    let F := Scheme.Modules.pushforward f ⋙ FiniteCover.schemeBaseSections k Y U
    let G := FiniteCover.schemeBaseSections k X (f ⁻¹ᵁ U)
    letI : F.Linear k := by dsimp only [F]; infer_instance
    letI : G.Linear k := by dsimp only [G]; infer_instance
    change (r • x : F.obj M) = r • (show G.obj M from x)
    calc
      _ = F.map (r • 𝟙 M) x := by rw [F.map_smul, F.map_id]; rfl
      _ = G.map (r • 𝟙 M) (show G.obj M from x) := rfl
      _ = _ := by rw [G.map_smul, G.map_id]; rfl

/-- Naturality in every open and every sheaf coefficient. -/
def pushforwardBasePresheafIso :
    Scheme.Modules.pushforward f ⋙ FiniteCover.schemeBasePresheaf k Y ≅
      FiniteCover.schemeBasePresheaf k X ⋙
        (Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ (ModuleCat.{u} k)).obj
          (Opens.map f.base).op :=
  NatIso.ofComponents (fun M =>
    NatIso.ofComponents (fun U =>
      (pushforwardBaseSectionsLinearEquiv k f M U.unop).toModuleIso)
      (by intro U V g; ext x; rfl))
    (by intro M N g; ext U x; rfl)

/-- Restriction to a whole diagram of opens preserves the same identification. -/
def pushforwardChartBaseSectionsIso {B : Type u} [SmallCategory B]
    (opens : B ⥤ Y.Opensᵒᵖ) :
    Scheme.Modules.pushforward f ⋙ FiniteCover.schemeBasePresheaf k Y ⋙
        (Functor.whiskeringLeft B Y.Opensᵒᵖ (ModuleCat.{u} k)).obj opens ≅
      FiniteCover.schemeBasePresheaf k X ⋙
        (Functor.whiskeringLeft B X.Opensᵒᵖ (ModuleCat.{u} k)).obj
          (opens ⋙ (Opens.map f.base).op) :=
  Functor.isoWhiskerRight (pushforwardBasePresheafIso k f)
    ((Functor.whiskeringLeft B Y.Opensᵒᵖ (ModuleCat.{u} k)).obj opens)

end ToricPower

end
