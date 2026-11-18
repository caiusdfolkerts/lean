module

public import ToricPower.SchemeAdjunctUnitSections
public import ToricPower.OpenBaseChangeNaturality

/-!
# Original unit-source sections through an open pullback square

This is the section-level form of the proved base-change mate identity.
The actual pullback, original unit normalization, and ordinary
restriction maps remain visible in every formula.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]
  (square : j ≫ f = g ≫ k)
  {M : Y.Modules} {N : X.Modules}
  (φ : (Scheme.Modules.pullback f).obj M ⟶ N)
  (e : (𝟙_ Y'.Modules) ⟶ (Scheme.Modules.pullback k).obj M)

/-- The original local adjunct of an original unit-source map. -/
theorem normalizedSquareAdjunct_map :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
      (e ≫ (Scheme.Modules.pullback k).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ φ) ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
          ((Scheme.Modules.pushforward f).obj N) ≫
        pushforwardRestrictionMap f g j k square N) =
      (Scheme.Modules.pullback g).map e ≫
        (pullbackSquareIso f g j k square).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.restrictFunctor j).map φ := by
  rw [pullback_pushforwardRestrictionMap_homEquiv,
    ← Adjunction.homEquiv_naturality_left, Equiv.symm_apply_apply]

/-- The literal section of that local adjunct equals the literal
original direct-image section, on every inverse-image open. -/
theorem normalizedSquareAdjunct_section (U : Y'.Opens) :
    Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackObjUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map e ≫
        (pullbackSquareIso f g j k square).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.restrictFunctor j).map φ)
      (g ⁻¹ᵁ U) (1 : Γ(X',g ⁻¹ᵁ U)) =
    Scheme.Modules.Hom.app
      (e ≫ (Scheme.Modules.pullback k).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ φ) ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
          ((Scheme.Modules.pushforward f).obj N) ≫
        pushforwardRestrictionMap f g j k square N)
      U (1 : Γ(Y',U)) := by
  rw [← normalizedSquareAdjunct_map f g j k square φ e]
  exact normalizedUnitAdjunct_section g (N.restrict j) _ U

end ToricPower

end
