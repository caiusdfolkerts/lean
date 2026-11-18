module

public import ToricPower.CellularLinearDensityBase
public import ToricPower.CellularRealizationUnit
public import ToricPower.MappedCellularRealization

/-!
# Extending original representable comparisons to all linear diagrams

A source-natural comparison on actual free representables extends over
the original coend presentation. Its construction and uniqueness retain
every vector generator. In particular, its value on a representable is
exactly the specified original comparison under the canonical coend
frame. No finite-dimensional restriction is made.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{u,u} B]
  (Φ : (C ⥤ ModuleCat.{u} k) ⥤ B) [Φ.Additive] [Φ.Linear k]
  [PreservesColimitsOfSize.{u,u} Φ]
  (P : Cᵒᵖ ⥤ B) (β : representableFunctor k ⋙ Φ ⟶ P)

/-- The target coend's genuine unit, precomposed with the specified
original label comparison. -/
def densityTargetUnit :
    𝟭 (C ⥤ ModuleCat.{u} k) ⟶ realization k P ⋙ homDiagram k (representableFunctor k ⋙ Φ) :=
  (realizationHomAdjunction k P).unit ≫
    whiskerLeft (realization k P) (homDiagramPrecompose k β)

@[simp]
theorem densityTargetUnit_generator (M : C ⥤ ModuleCat.{u} k) (c : C) (x : M.obj c) :
    ((densityTargetUnit k Φ P β).app M).app c x =
      β.app (op c) ≫ realizationInclusion k P M c x := by
  change β.app (op c) ≫ ((realizationHomAdjunction k P).unit.app M).app c x = _
  rw [realizationUnit_app_apply]

/-- The extension uses the original density isomorphism and the actual
mapped-coequalizer descent; no new comparison maps are chosen. -/
def densityExtensionComponent (M : C ⥤ ModuleCat.{u} k) :
    Φ.obj M ⟶ (realization k P).obj M :=
  Φ.map ((representableDensityIso k).inv.app M) ≫
    mappedRealizationDesc k Φ (representableFunctor k) ((densityTargetUnit k Φ P β).app M)

@[reassoc]
theorem densityExtension_generator (M : C ⥤ ModuleCat.{u} k) (c : C) (x : M.obj c) :
    Φ.map (fromValue k M c x) ≫ densityExtensionComponent k Φ P β M =
      β.app (op c) ≫ realizationInclusion k P M c x := by
  have cancellation :
      Φ.map ((representableDensityIso k).hom.app M) ≫
        densityExtensionComponent k Φ P β M =
      mappedRealizationDesc k Φ (representableFunctor k) ((densityTargetUnit k Φ P β).app M) := by
    unfold densityExtensionComponent
    rw [← Category.assoc,← Φ.map_comp,Iso.hom_inv_id_app,Φ.map_id,Category.id_comp]
  rw [← representableDensityIso_generator k M c x,Φ.map_comp,Category.assoc,cancellation,
    mappedRealizationInclusion_desc]
  exact densityTargetUnit_generator k Φ P β M c x

/-- Actual free representable maps remain jointly detecting after the
linear colimit-preserving functor. -/
theorem mappedRepresentables_hom_ext {M : C ⥤ ModuleCat.{u} k} {E : B}
    {f g : Φ.obj M ⟶ E}
    (equal : ∀ c (x : M.obj c), Φ.map (fromValue k M c x) ≫ f =
      Φ.map (fromValue k M c x) ≫ g) : f = g := by
  apply (cancel_epi (Φ.map ((representableDensityIso k).hom.app M))).mp
  apply mappedRealization_hom_ext k Φ (representableFunctor k)
  intro c x
  rw [← Φ.map_comp_assoc,← Φ.map_comp_assoc,representableDensityIso_generator]
  exact equal c x

/-- The specified source-natural comparison extends to a natural
transformation on the entire original diagram category. -/
def densityExtension : Φ ⟶ realization k P where
  app M := densityExtensionComponent k Φ P β M
  naturality {M N} f := by
    apply mappedRepresentables_hom_ext k Φ
    intro c x
    rw [← Φ.map_comp_assoc,fromValue_comp,densityExtension_generator]
    rw [densityExtension_generator_assoc]
    exact congrArg (fun h => β.app (op c) ≫ h)
      (realizationInclusion_map k P f c x).symm

/-- On each representable, the extension is the original comparison,
through the canonical realization frame. -/
theorem densityExtension_representable (c : C) :
    (densityExtension k Φ P β).app (representable k c) ≫
      (realizationRepresentableIso k P c).hom = β.app (op c) := by
  have equality := densityExtension_generator k Φ P β (representable k c) c
    (ModuleCat.freeMk (𝟙 c))
  have identity : fromValue k (representable k c) c (ModuleCat.freeMk (𝟙 c)) = 𝟙 _ :=
    fromValue_evaluate k (representable k c) c (𝟙 _)
  rw [identity,Φ.map_id,Category.id_comp] at equality
  change densityExtensionComponent k Φ P β (representable k c) ≫ _ = _
  rw [equality]
  change (β.app (op c) ≫ (realizationRepresentableIso k P c).inv) ≫
      (realizationRepresentableIso k P c).hom = _
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]

end ToricPower.Cellular

end
