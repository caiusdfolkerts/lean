module

public import ToricPower.ReconstructionCompletionExternalRetraction

/-! # The actual diagonal square on arbitrary sections

This comparison is proved before any toric chart is substituted.  It uses
the given diagonal adjunct and exterior retraction, and retains both
original sections in their common ordinary restriction target.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

/-- Equal overlap maps give the same normalized section in a fixed
ordinary restriction target, including their composition comparisons. -/
theorem reconstructionRawOverlapUnit_congr
    {W U X : Scheme.{u}} (m : W ⟶ X) [IsOpenImmersion m] (j : U ⟶ X)
    {f g : W ⟶ U} (equal : f = g) (hf : f ≫ j = m) (hg : g ≫ j = m)
    (L : X.Modules) (a : 𝟙_ U.Modules ⟶ (Scheme.Modules.pullback j).obj L) :
    (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
        (Scheme.Modules.pullbackComp f j).hom.app L ≫
        (Scheme.Modules.pullbackCongr hf).hom.app L ≫
        (Scheme.Modules.restrictFunctorIsoPullback m).inv.app L =
      (Scheme.Modules.pullbackObjUnitIso g).inv ≫ (Scheme.Modules.pullback g).map a ≫
        (Scheme.Modules.pullbackComp g j).hom.app L ≫
        (Scheme.Modules.pullbackCongr hg).hom.app L ≫
        (Scheme.Modules.restrictFunctorIsoPullback m).inv.app L := by
  subst g
  rfl

/-- The original diagonal adjunct of an exterior section is its tensor
evaluation on the overlap whenever the actual top maps agree under retraction. -/
theorem reconstructionDiagonalSectionAdjunct
    {X Y Z W T U : Scheme.{u}}
    (d : X ⟶ Y) (p q : Y ⟶ X) (j : W ⟶ X) (k : Z ⟶ Y)
    (g : W ⟶ Z) (e : T ⟶ X) (f : U ⟶ X) (l : Z ⟶ T) (r : Z ⟶ U)
    (left : W ⟶ T) (right : W ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hp : d ≫ p = 𝟙 X) (hq : d ≫ q = 𝟙 X) (hsq : j ≫ d = g ≫ k)
    (hkp : k ≫ p = l ≫ e) (hkq : k ≫ q = r ≫ f)
    (hleft : g ≫ l = left) (hright : g ≫ r = right)
    (hfirst : left ≫ e = j) (hsecond : right ≫ f = j)
    (H : Y.Modules) (L M : X.Modules)
    (a : 𝟙_ T.Modules ⟶ (Scheme.Modules.pullback e).obj L)
    (b : 𝟙_ U.Modules ⟶ (Scheme.Modules.pullback f).obj M)
    (β : L ⊗ M ⟶ (Scheme.Modules.pullback d).obj H)
    (γ : schemeExteriorSheaf p q L M ⟶ H)
    (target : (Scheme.Modules.pullback k).obj H ⟶
      (Scheme.Modules.pushforward g).obj (((Scheme.Modules.pullback d).obj H).restrict j))
    (comparison : (Scheme.Modules.pullback k).map γ ≫ target =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackSquareIso d g j k hsq).hom.app (schemeExteriorSheaf p q L M) ≫
          (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
            ((Scheme.Modules.pullback d).obj (schemeExteriorSheaf p q L M)) ≫
          (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pullback d).map γ)))
    (top : (Scheme.Modules.pullback d).map γ =
      schemeExternalSectionRetractionMap d p q hp hq L M ≫ β) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          (((λ_ (𝟙_ Z.Modules)).inv ≫
              (externalSquareUnitSection p k e l hkp L a ⊗ₘ
                externalSquareUnitSection q k f r hkq M b) ≫
              (Scheme.Modules.pullbackTensorIsoOfOpenImmersion k
                ((Scheme.Modules.pullback p).obj L) ((Scheme.Modules.pullback q).obj M)).inv) ≫
            (Scheme.Modules.pullback k).map γ ≫ target) =
      (λ_ (𝟙_ W.Modules)).inv ≫
        (((Scheme.Modules.pullbackObjUnitIso left).inv ≫
            (Scheme.Modules.pullback left).map a ≫
            (Scheme.Modules.pullbackComp left e).hom.app L ≫
            (Scheme.Modules.pullbackCongr hfirst).hom.app L ≫
            (Scheme.Modules.restrictFunctorIsoPullback j).inv.app L) ⊗ₘ
          ((Scheme.Modules.pullbackObjUnitIso right).inv ≫
            (Scheme.Modules.pullback right).map b ≫
            (Scheme.Modules.pullbackComp right f).hom.app M ≫
            (Scheme.Modules.pullbackCongr hsecond).hom.app M ≫
            (Scheme.Modules.restrictFunctorIsoPullback j).inv.app M)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) L M ≫
        (Scheme.Modules.restrictFunctor j).map β := by
  rw [comparison, ← (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left,
    Equiv.symm_apply_apply, top, Functor.map_comp]
  have first : (g ≫ l) ≫ e = j := by rw [hleft]; exact hfirst
  have second : (g ≫ r) ≫ f = j := by rw [hright]; exact hsecond
  have actual := externalSquareUnitSection_retraction d p q j k g e f l r
    hp hq hsq hkp hkq first second L M a b
  have firstUnit := reconstructionRawOverlapUnit_congr j e hleft first hfirst L a
  have secondUnit := reconstructionRawOverlapUnit_congr j f hright second hsecond M b
  conv at actual =>
    rhs
    rw [firstUnit, secondUnit]
  have post := congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor j).map β) actual
  simpa only [Functor.map_comp, Category.assoc] using post

/-- When the ordinary restriction target is the second overlap composite,
its normalized section has no reflexive pullback comparison. The simplification
is performed with all schemes and sections still abstract. -/
theorem reconstructionDiagonalSectionAdjunct_rightComposite
    {X Y Z W T U : Scheme.{u}}
    (d : X ⟶ Y) (p q : Y ⟶ X) (k : Z ⟶ Y)
    (g : W ⟶ Z) (e : T ⟶ X) (f : U ⟶ X) (l : Z ⟶ T) (r : Z ⟶ U)
    (left : W ⟶ T) (right : W ⟶ U)
    [IsOpenImmersion (right ≫ f)] [IsOpenImmersion k]
    (hp : d ≫ p = 𝟙 X) (hq : d ≫ q = 𝟙 X) (hsq : (right ≫ f) ≫ d = g ≫ k)
    (hkp : k ≫ p = l ≫ e) (hkq : k ≫ q = r ≫ f)
    (hleft : g ≫ l = left) (hright : g ≫ r = right)
    (hfirst : left ≫ e = (right ≫ f))
    (H : Y.Modules) (L M : X.Modules)
    (a : 𝟙_ T.Modules ⟶ (Scheme.Modules.pullback e).obj L)
    (b : 𝟙_ U.Modules ⟶ (Scheme.Modules.pullback f).obj M)
    (β : L ⊗ M ⟶ (Scheme.Modules.pullback d).obj H)
    (γ : schemeExteriorSheaf p q L M ⟶ H)
    (target : (Scheme.Modules.pullback k).obj H ⟶
      (Scheme.Modules.pushforward g).obj (((Scheme.Modules.pullback d).obj H).restrict (right ≫ f)))
    (comparison : (Scheme.Modules.pullback k).map γ ≫ target =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackSquareIso d g (right ≫ f) k hsq).hom.app (schemeExteriorSheaf p q L M) ≫
          (Scheme.Modules.restrictFunctorIsoPullback (right ≫ f)).inv.app
            ((Scheme.Modules.pullback d).obj (schemeExteriorSheaf p q L M)) ≫
          (Scheme.Modules.restrictFunctor (right ≫ f)).map ((Scheme.Modules.pullback d).map γ)))
    (top : (Scheme.Modules.pullback d).map γ =
      schemeExternalSectionRetractionMap d p q hp hq L M ≫ β) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          (((λ_ (𝟙_ Z.Modules)).inv ≫
              (externalSquareUnitSection p k e l hkp L a ⊗ₘ
                externalSquareUnitSection q k f r hkq M b) ≫
              (Scheme.Modules.pullbackTensorIsoOfOpenImmersion k
                ((Scheme.Modules.pullback p).obj L) ((Scheme.Modules.pullback q).obj M)).inv) ≫
            (Scheme.Modules.pullback k).map γ ≫ target) =
      (λ_ (𝟙_ W.Modules)).inv ≫
        (((Scheme.Modules.pullbackObjUnitIso left).inv ≫
            (Scheme.Modules.pullback left).map a ≫
            (Scheme.Modules.pullbackComp left e).hom.app L ≫
            (Scheme.Modules.pullbackCongr hfirst).hom.app L ≫
            (Scheme.Modules.restrictFunctorIsoPullback (right ≫ f)).inv.app L) ⊗ₘ
          ((Scheme.Modules.pullbackObjUnitIso right).inv ≫
            (Scheme.Modules.pullback right).map b ≫
            (Scheme.Modules.pullbackComp right f).hom.app M ≫
            (Scheme.Modules.restrictFunctorIsoPullback (right ≫ f)).inv.app M)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor (right ≫ f)) L M ≫
        (Scheme.Modules.restrictFunctor (right ≫ f)).map β := by
  have actual := reconstructionDiagonalSectionAdjunct d p q (right ≫ f) k g e f l r
    left right hp hq hsq hkp hkq hleft hright hfirst (show right ≫ f = right ≫ f from rfl)
    H L M a b β γ target comparison top
  have reflCongr :
      (Scheme.Modules.pullbackCongr (show right ≫ f = right ≫ f from rfl)).hom.app M = 𝟙 _ := rfl
  simpa only [reflCongr, Category.id_comp] using actual

end ToricPower

end
