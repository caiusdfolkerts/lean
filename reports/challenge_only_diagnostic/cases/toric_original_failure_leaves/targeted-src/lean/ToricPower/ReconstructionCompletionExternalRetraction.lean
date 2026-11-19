module

public import ToricPower.ReconstructionCompletionExternalSquare
public import ToricPower.SchemePullbackSectionCoherence

/-!
# Exterior sections restricted along the genuine diagonal

Every map below is the specified pullback, projection-square, or
ordinary-restriction map. The two sections need not be frames.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

variable {X Y Z W T U : Scheme.{u}}

/-- Transport of an arbitrary local unit-source map through a projection
square, with the canonical unit and composition comparisons. -/
def externalSquareUnitSection (p : Y ⟶ X) (k : Z ⟶ Y)
    (e : T ⟶ X) (l : Z ⟶ T) (hk : k ≫ p = l ≫ e)
    (M : X.Modules) (a : 𝟙_ T.Modules ⟶ (Scheme.Modules.pullback e).obj M) :
    𝟙_ Z.Modules ⟶ (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackObjUnitIso l).inv ≫
    (Scheme.Modules.pullback l).map a ≫
    (Scheme.Modules.pullbackComp l e).hom.app M ≫
    (Scheme.Modules.pullbackCongr hk).inv.app M ≫
    (Scheme.Modules.pullbackComp k p).inv.app M

/-- The actual exterior-section map, transported around the diagonal
square and followed by the genuine diagonal retraction, is the tensor
of the two sections pulled to the overlap along their composites. -/
@[reassoc]
theorem externalSquareUnitSection_retraction
    (d : X ⟶ Y) (p q : Y ⟶ X) (j : W ⟶ X) (k : Z ⟶ Y)
    (g : W ⟶ Z) (e : T ⟶ X) (f : U ⟶ X) (l : Z ⟶ T) (r : Z ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hp : d ≫ p = 𝟙 X) (hq : d ≫ q = 𝟙 X) (hsq : j ≫ d = g ≫ k)
    (hkp : k ≫ p = l ≫ e) (hkq : k ≫ q = r ≫ f)
    (hjp : (g ≫ l) ≫ e = j) (hjq : (g ≫ r) ≫ f = j)
    (L M : X.Modules)
    (a : 𝟙_ T.Modules ⟶ (Scheme.Modules.pullback e).obj L)
    (b : 𝟙_ U.Modules ⟶ (Scheme.Modules.pullback f).obj M) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map
          ((λ_ (𝟙_ Z.Modules)).inv ≫
            (externalSquareUnitSection p k e l hkp L a ⊗ₘ
              externalSquareUnitSection q k f r hkq M b) ≫
            (Scheme.Modules.pullbackTensorIsoOfOpenImmersion k
              ((Scheme.Modules.pullback p).obj L)
              ((Scheme.Modules.pullback q).obj M)).inv) ≫
        (pullbackSquareIso d g j k hsq).hom.app (schemeExteriorSheaf p q L M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((Scheme.Modules.pullback d).obj (schemeExteriorSheaf p q L M)) ≫
        (Scheme.Modules.restrictFunctor j).map
          (schemeExternalSectionRetractionMap d p q hp hq L M) =
      (λ_ (𝟙_ W.Modules)).inv ≫
        (((Scheme.Modules.pullbackObjUnitIso (g ≫ l)).inv ≫
            (Scheme.Modules.pullback (g ≫ l)).map a ≫
            (Scheme.Modules.pullbackComp (g ≫ l) e).hom.app L ≫
            (Scheme.Modules.pullbackCongr hjp).hom.app L ≫
            (Scheme.Modules.restrictFunctorIsoPullback j).inv.app L) ⊗ₘ
          ((Scheme.Modules.pullbackObjUnitIso (g ≫ r)).inv ≫
            (Scheme.Modules.pullback (g ≫ r)).map b ≫
            (Scheme.Modules.pullbackComp (g ≫ r) f).hom.app M ≫
            (Scheme.Modules.pullbackCongr hjq).hom.app M ≫
            (Scheme.Modules.restrictFunctorIsoPullback j).inv.app M)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) L M := by
  rw [schemeExternalSectionRetractionMap, pullbackSquareTensorUnitMaps_map]
  dsimp only [externalSquareUnitSection]
  rw [Scheme.Modules.section_square_frame_pullback_assoc d p j k g e l hp hsq hkp hjp,
    Scheme.Modules.section_square_frame_pullback_assoc d q j k g f r hq hsq hkq hjq]

end ToricPower

end
