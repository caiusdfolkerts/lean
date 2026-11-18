module

public import ToricPower.SheafPullbackFrames
public import ToricPower.CartierCore

/-!
# Functoriality of genuine pullback frames

A frame is an isomorphism from the structure sheaf to a module sheaf.
Its pullback is normalized by the canonical structure-sheaf isomorphism.
This normalization respects composition and takes a scalar transition
function to its ordinary pullback on scheme sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable {X Y Z : Scheme.{u}}

/-- On global sections of the structure sheaf, the scalar endomorphism
is ordinary multiplication. -/
theorem globalSectionsSmul_unit_top (r x : Γ(X, ⊤)) :
    Hom.app (globalSectionsSmul (𝟙_ X.Modules) r) ⊤ x = r * x := by
  rw [globalSectionsSmul_app]
  change X.presheaf.map (𝟙 (⊤ : X.Opens)).op r * x = r * x
  rw [op_id, X.presheaf.map_id, ConcreteCategory.id_apply]

/-- Pull back a genuine module frame along an arbitrary scheme morphism. -/
def pullbackModuleFrame (f : X ⟶ Y) {M : Y.Modules}
    (frame : 𝟙_ Y.Modules ≅ M) :
    𝟙_ X.Modules ≅ (pullback f).obj M :=
  (pullbackObjUnitIso f).symm ≪≫ (pullback f).mapIso frame

/-- The inverse structure-sheaf identifications respect composition. -/
@[reassoc]
theorem pullbackUnitInverse_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackObjUnitIso f).inv ≫ (pullback f).map (pullbackObjUnitIso g).inv ≫
      (pullbackComp f g).hom.app (𝟙_ Z.Modules) =
        (pullbackObjUnitIso (f ≫ g)).inv := by
  apply (cancel_mono (pullbackObjUnitIso (f ≫ g)).hom).mp
  rw [Iso.inv_hom_id, ← pullbackObjUnitIso_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-- Successive normalized pullback of a frame is the pullback along the
composite, through the canonical composition isomorphism. -/
theorem pullbackModuleFrame_comp (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (frame : 𝟙_ Z.Modules ≅ M) :
    pullbackModuleFrame f (pullbackModuleFrame g frame) ≪≫ (pullbackComp f g).app M =
      pullbackModuleFrame (f ≫ g) frame := by
  apply Iso.ext
  simp only [pullbackModuleFrame, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Iso.app_hom, Category.assoc]
  have naturality := (pullbackComp f g).hom.naturality frame.hom
  change (pullback f).map ((pullback g).map frame.hom) ≫ (pullbackComp f g).hom.app M =
    (pullbackComp f g).hom.app (𝟙_ Z.Modules) ≫ (pullback (f ≫ g)).map frame.hom at naturality
  rw [naturality, pullbackUnitInverse_comp_assoc]

/-- Pullback of a scalar transition is the ordinary scalar pullback.
This uses the actual pullback functor on module sheaves. -/
theorem pullbackModuleFrame_scalar (f : X ⟶ Y) {M : Y.Modules}
    (first second : 𝟙_ Y.Modules ≅ M) (scalar : Γ(Y, ⊤))
    (transition : first.hom =
      globalSectionsSmul (𝟙_ Y.Modules) scalar ≫ second.hom) :
    (pullbackModuleFrame f first).hom =
      globalSectionsSmul (𝟙_ X.Modules) (f.appTop scalar) ≫
        (pullbackModuleFrame f second).hom := by
  simp only [pullbackModuleFrame, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom]
  rw [transition, CategoryTheory.Functor.map_comp, pullback_map_globalSectionsSmul]
  rw [← Category.assoc, ← globalSectionsSmul_naturality, Category.assoc]

/-- For an open immersion, the canonical pullback identification of the
structure sheaf agrees with its ordinary restriction identification. -/
theorem restrictUnitIso_pullback (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app (𝟙_ Y.Modules) ≫
      (pullbackObjUnitIso f).hom = (restrictUnitIso f).hom := by
  apply ((restrictAdjunction f).homEquiv (𝟙_ Y.Modules) (𝟙_ X.Modules)).injective
  have comparison :
      (restrictAdjunction f).homEquiv (𝟙_ Y.Modules) (𝟙_ X.Modules)
        ((restrictFunctorIsoPullback f).hom.app (𝟙_ Y.Modules) ≫ (pullbackObjUnitIso f).hom) =
      (pullbackPushforwardAdjunction f).homEquiv (𝟙_ Y.Modules) (𝟙_ X.Modules)
        (pullbackObjUnitIso f).hom := by
    rw [Adjunction.homEquiv_naturality_right, restrictFunctorIsoPullback,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rfl
  rw [comparison, pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  ext U x
  change f.app U x = (f.appIso (f ⁻¹ᵁ U)).hom
    (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op x)
  have app := congrArg (fun mapping => mapping ≫ (f.appIso (f ⁻¹ᵁ U)).hom)
    (f.app_appIso_inv U)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at app
  exact ConcreteCategory.congr_hom app x

/-- Restriction of a genuine frame along an open immersion. -/
def restrictModuleFrame (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (frame : 𝟙_ Y.Modules ≅ M) : 𝟙_ X.Modules ≅ M.restrict f :=
  (restrictUnitIso f).symm ≪≫ (restrictFunctor f).mapIso frame

/-- Ordinary restriction of a frame is exactly its normalized pullback
through the canonical comparison of the two functors. -/
theorem restrictModuleFrame_pullback (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (frame : 𝟙_ Y.Modules ≅ M) :
    restrictModuleFrame f frame ≪≫ (restrictFunctorIsoPullback f).app M =
      pullbackModuleFrame f frame := by
  apply Iso.ext
  simp only [restrictModuleFrame, pullbackModuleFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [(restrictFunctorIsoPullback f).hom.naturality frame.hom, ← Category.assoc]
  apply congrArg (fun mapping => mapping ≫ (pullback f).map frame.hom)
  apply (cancel_mono (pullbackObjUnitIso f).hom).mp
  rw [Category.assoc, restrictUnitIso_pullback, Iso.inv_hom_id, Iso.inv_hom_id]

end ToricPower
