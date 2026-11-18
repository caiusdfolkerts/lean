module

public import ToricPower.SchemePushforwardBaseSections
public import ToricPower.QuasicoherentOpenAdjunction

/-! # Actual base-linear sections under open restriction

The section identification is the literal identity on the open image.
Its linearity follows from the specified base action and the genuine
restriction--pullback comparison. All coefficient maps are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u

variable (k : Type u) [Field k] {U X : Scheme.{u}}
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]

instance schemeRestriction_baseLinear : (Scheme.Modules.restrictFunctor j).Linear k :=
  Functor.linear_of_iso k (Scheme.Modules.restrictFunctorIsoPullback j).symm

def restrictionBaseSectionsLinearEquiv (M : X.Modules) (V : U.Opens) :
    (FiniteCover.schemeBaseSections k U V).obj (M.restrict j) ≃ₗ[k]
      (FiniteCover.schemeBaseSections k X (j ''ᵁ V)).obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    let F := Scheme.Modules.restrictFunctor j ⋙ FiniteCover.schemeBaseSections k U V
    let G := FiniteCover.schemeBaseSections k X (j ''ᵁ V)
    letI : F.Linear k := by dsimp only [F]; infer_instance
    letI : G.Linear k := by dsimp only [G]; infer_instance
    change (r • x : F.obj M) = r • (show G.obj M from x)
    calc
      _ = F.map (r • 𝟙 M) x := by rw [F.map_smul,F.map_id]; rfl
      _ = G.map (r • 𝟙 M) (show G.obj M from x) := rfl
      _ = _ := by rw [G.map_smul,G.map_id]; rfl

def restrictionBaseSectionsIso (V : U.Opens) :
    Scheme.Modules.restrictFunctor j ⋙ FiniteCover.schemeBaseSections k U V ≅
      FiniteCover.schemeBaseSections k X (j ''ᵁ V) :=
  NatIso.ofComponents (fun M => (restrictionBaseSectionsLinearEquiv k j M V).toModuleIso)
    (by intro M N f; ext x; rfl)

def restrictionGlobalBaseSectionsIso :
    Scheme.Modules.restrictFunctor j ⋙ FiniteCover.schemeBaseSections k U ⊤ ≅
      FiniteCover.schemeBaseSections k X j.opensRange :=
  restrictionBaseSectionsIso k j ⊤ ≪≫
    eqToIso (congrArg (FiniteCover.schemeBaseSections k X) j.image_top_eq_opensRange)

def pullbackGlobalBaseSectionsIso :
    Scheme.Modules.pullback j ⋙ FiniteCover.schemeBaseSections k U ⊤ ≅
      FiniteCover.schemeBaseSections k X j.opensRange :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback j).symm
    (FiniteCover.schemeBaseSections k U ⊤) ≪≫ restrictionGlobalBaseSectionsIso k j

def pushforwardGlobalBaseSectionsIso :
    Scheme.Modules.pushforward j ⋙ FiniteCover.schemeBaseSections k X ⊤ ≅
      FiniteCover.schemeBaseSections k U ⊤ :=
  NatIso.ofComponents (fun M =>
    (pushforwardBaseSectionsLinearEquiv k j M ⊤).toModuleIso)
    (by intro M N f; ext x; rfl)

end ToricPower

end
