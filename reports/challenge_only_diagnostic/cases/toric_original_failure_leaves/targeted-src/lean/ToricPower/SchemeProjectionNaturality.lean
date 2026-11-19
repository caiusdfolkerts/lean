module

public import ToricPower.SheafTensorLiftValues
public import ToricPower.InvertibleProjectionFormula

/-! # Naturality of the actual invertible projection formula

The comparison sends a genuine pure tensor to the pullback-unit
section multiplied by its source scalar. This gives its naturality
for every source sheaf morphism, before any invertibility assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

namespace ToricPower

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X)

theorem schemeProjectionSectionAction_natural
    {M N : U.Modules} (g : M ⟶ N) (V : X.Opens)
    (r : Γ(U,j ⁻¹ᵁ V)) (x : M.val.obj (op (j ⁻¹ᵁ V))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pushforward j).map g) V
      (BondalThomsen.projectionSectionAction j M V r x) =
    BondalThomsen.projectionSectionAction j N V r
      (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward j).map g) V x) := by
  letI : Module (Γ(U,j ⁻¹ᵁ V)) (M.val.obj (op (j ⁻¹ᵁ V))) :=
    (M.val.obj (op (j ⁻¹ᵁ V))).isModule
  letI : Module (Γ(U,j ⁻¹ᵁ V)) (N.val.obj (op (j ⁻¹ᵁ V))) :=
    (N.val.obj (op (j ⁻¹ᵁ V))).isModule
  exact (g.val.app (op (j ⁻¹ᵁ V))).hom.map_smul r x

theorem schemeProjectionAction_pureSection
    (M : X.Modules) (N : U.Modules)
    (comparison : M ⟶ (Scheme.Modules.pushforward j).obj N)
    (V : X.Opens) (s : Γ(M,V))
    (t : Γ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf),V)) :
    Scheme.Modules.Hom.app (BondalThomsen.projectionAction j M N comparison) V
      (schemeTensorSection M
        ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)) V s t) =
      BondalThomsen.projectionSectionAction j N V t (comparison.val.app (op V) s) := by
  exact (schemeTensorLift_pureSection M _ _
    (BondalThomsen.projectionActionPresheaf j M N comparison) V s t).trans rfl

theorem schemeProjectionFormulaMap_natural {M N : X.Modules} (f : M ⟶ N) :
    (f ▷ (Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)) ≫
        BondalThomsen.schemeProjectionFormulaMap j N =
      BondalThomsen.schemeProjectionFormulaMap j M ≫
        (Scheme.Modules.pushforward j).map ((Scheme.Modules.pullback j).map f) := by
  apply schemeTensorHom_ext
  intro V s t
  simp only [schemeHom_comp_apply,← tensorHom_id,schemeTensorSection_naturality,
    Scheme.Modules.Hom.id_app,ModuleCat.id_apply]
  rw [BondalThomsen.schemeProjectionFormulaMap,schemeProjectionAction_pureSection,
    BondalThomsen.schemeProjectionFormulaMap,schemeProjectionAction_pureSection]
  have naturality := ConcreteCategory.congr_hom
    (congrArg (fun g => Scheme.Modules.Hom.app g V)
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality f)) s
  simp only [schemeHom_comp_apply,Functor.id_map,Functor.comp_map] at naturality
  rw [schemeProjectionSectionAction_natural]
  exact congrArg (BondalThomsen.projectionSectionAction j
    ((Scheme.Modules.pullback j).obj N) V t) naturality

/-- The canonical comparison, natural on all actual module sheaves. -/
def schemeProjectionFormulaTransformation :
    tensorRight ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)) ⟶
      Scheme.Modules.pullback j ⋙ Scheme.Modules.pushforward j where
  app M := BondalThomsen.schemeProjectionFormulaMap j M
  naturality {M N} f := schemeProjectionFormulaMap_natural j f

end ToricPower

end
