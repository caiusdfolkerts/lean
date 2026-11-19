module

public import ToricPower.SheafFramePullbackNaturality
public import ToricPower.SheafChartSections

/-!
# Coherence of restriction and genuine pullback

The ordinary restriction functor along open immersions and the pullback
functor are identified by the uniqueness of left adjoints. The comparison
also respects composition, as is checked through its right-adjoint mate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable {X Y Z : Scheme.{u}}

/-- The restriction/pullback comparison is the mate of the identity
on the actual pushforward functor. -/
theorem conjugateEquiv_restrictFunctorIsoPullback_hom
    (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (pullbackPushforwardAdjunction f) (restrictAdjunction f)
      (restrictFunctorIsoPullback f).hom = 𝟙 (pushforward f) := by
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

/-- Composition of ordinary restrictions has the same mate as composition
of genuine pullbacks. -/
theorem conjugateEquiv_restrictFunctorComp_hom
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom =
        (pushforwardComp f g).hom := by
  ext M U x
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Hom.comp_app, ConcreteCategory.comp_apply, restrictAdjunction_unit_app_app,
    pushforward_map_app, restrictFunctorComp_hom_app_app,
    restrictAdjunction_counit_app_app, restrictFunctor_map_app,
    pushforwardComp_hom_app_app, ConcreteCategory.id_apply]
  erw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply,
    ← M.presheaf.map_comp_apply]
  change M.presheaf.map (𝟙 (op ((f ≫ g) ⁻¹ᵁ U))) x = x
  rw [M.presheaf.map_id, ConcreteCategory.id_apply]

/-- Compare two successive ordinary restrictions with two successive
pullbacks. -/
def restrictPullbackCompComparison (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctor g ⋙ restrictFunctor f ≅ pullback g ⋙ pullback f :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback g) (restrictFunctor f) ≪≫
    Functor.isoWhiskerLeft (pullback g) (restrictFunctorIsoPullback f)

/-- The twofold comparison still has identity right-adjoint mate. -/
theorem conjugateEquiv_restrictPullbackCompComparison_hom
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictPullbackCompComparison f g).hom = 𝟙 _ := by
  change conjugateEquiv _ _
    (Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
      Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom) = _
  rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction g).comp (restrictAdjunction f))]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_restrictFunctorIsoPullback_hom]
  simp

/-- Restriction and pullback agree coherently under composition of open
immersions. No choice of local frame is involved. -/
theorem restrictFunctorComp_toPullback (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctorComp f g ≪≫ restrictPullbackCompComparison f g ≪≫ pullbackComp f g =
      restrictFunctorIsoPullback (f ≫ g) := by
  have comparison :
      (restrictFunctorComp f g).hom ≫ (restrictPullbackCompComparison f g).hom =
      (restrictFunctorIsoPullback (f ≫ g)).hom ≫ (pullbackComp f g).inv := by
    apply (conjugateEquiv
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (restrictAdjunction (f ≫ g))).injective
    rw [← conjugateEquiv_comp _ ((restrictAdjunction g).comp (restrictAdjunction f)),
      ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (f ≫ g))]
    rw [conjugateEquiv_restrictPullbackCompComparison_hom,
      conjugateEquiv_restrictFunctorComp_hom, conjugateEquiv_pullbackComp_inv,
      conjugateEquiv_restrictFunctorIsoPullback_hom, Category.id_comp, Category.comp_id]
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [← Category.assoc, comparison, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Component form of the restriction/pullback composition comparison. -/
@[reassoc]
theorem restrictFunctorComp_toPullback_app (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (restrictFunctorComp f g).hom.app M ≫
      (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
      (restrictFunctorIsoPullback f).hom.app ((pullback g).obj M) ≫
      (pullbackComp f g).hom.app M =
        (restrictFunctorIsoPullback (f ≫ g)).hom.app M := by
  have comparison := congrArg (fun e => e.hom.app M) (restrictFunctorComp_toPullback f g)
  simpa only [Iso.trans_hom, NatTrans.comp_app, restrictPullbackCompComparison,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using comparison

/-- The inverse structure-sheaf frames respect successive ordinary
restrictions. The assertion follows on sections from preservation of one. -/
@[reassoc]
theorem restrictUnitInverse_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (restrictUnitIso f).inv ≫ (restrictFunctor f).map (restrictUnitIso g).inv ≫
      (restrictFunctorComp f g).inv.app (𝟙_ Z.Modules) =
        (restrictUnitIso (f ≫ g)).inv := by
  apply unitSheafHom_ext_top
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, restrictFunctor_map_app,
    restrictUnitIso_inv_sections, restrictFunctorComp_inv_app_app]
  change Z.presheaf.map _
      ((g.appIso (f ''ᵁ (⊤ : X.Opens))).inv ((f.appIso ⊤).inv (1 : Γ(X, ⊤)))) =
    ((f ≫ g).appIso ⊤).inv (1 : Γ(X, ⊤))
  simp only [map_one]

/-- Normalized restriction of an actual frame respects composition. -/
theorem restrictModuleFrame_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {M : Z.Modules}
    (frame : 𝟙_ Z.Modules ≅ M) :
    restrictModuleFrame f (restrictModuleFrame g frame) ≪≫
      ((restrictFunctorComp f g).app M).symm =
        restrictModuleFrame (f ≫ g) frame := by
  apply Iso.ext
  simp only [restrictModuleFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Iso.app_inv, Category.assoc]
  have naturality := (restrictFunctorComp f g).inv.naturality frame.hom
  change (restrictFunctor f).map ((restrictFunctor g).map frame.hom) ≫
      (restrictFunctorComp f g).inv.app M =
    (restrictFunctorComp f g).inv.app (𝟙_ Z.Modules) ≫
      (restrictFunctor (f ≫ g)).map frame.hom at naturality
  rw [naturality, restrictUnitInverse_comp_assoc]

end ToricPower
