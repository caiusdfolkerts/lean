module

public import ToricPower.SchemeExternalSections
public import ToricPower.SchemePullbackSectionCoherence

/-!
# Pullback coherence of the canonical exterior section map

These identities retain the actual structure-sheaf comparison,
pullback composition map, and oplax tensor comparison. They hold for
arbitrary scheme morphisms, including the diagonal, with no affine or
open-immersion assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u
variable (k : Type u) [Field k]

section UnitMaps

variable {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

/-- The linear unit-source pullback map respects the specified
composition comparison of genuine sheaf pullbacks. -/
@[reassoc]
theorem schemePullbackUnitHomLinearMap_comp (L : Z.Modules)
    (s : 𝟙_ Z.Modules ⟶ L) :
    schemePullbackUnitHomLinearMap k f ((Scheme.Modules.pullback g).obj L)
        (schemePullbackUnitHomLinearMap k g L s) ≫
        (Scheme.Modules.pullbackComp f g).hom.app L =
      schemePullbackUnitHomLinearMap k (f ≫ g) L s := by
  exact Scheme.Modules.pullback_unit_map_comp f g s

omit g in
@[reassoc]
theorem schemePullbackUnitHomLinearMap_tensor (L M : Y.Modules)
    (s : 𝟙_ Y.Modules ⟶ L) (t : 𝟙_ Y.Modules ⟶ M) :
    schemePullbackUnitHomLinearMap k f (L ⊗ M)
        (moduleTensorUnitHomBilinear k Y L M s t) ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L M =
      moduleTensorUnitHomBilinear k X _ _
        (schemePullbackUnitHomLinearMap k f L s)
        (schemePullbackUnitHomLinearMap k f M t) := by
  change ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map ((λ_ (𝟙_ Y.Modules)).inv ≫ (s ⊗ₘ t))) ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L M = _
  rw [Category.assoc, Scheme.Modules.pullback_tensor_unit_maps,
    Iso.inv_hom_id_assoc]
  rfl

omit f g in
@[reassoc]
theorem schemePullbackUnitHomLinearMap_id (L : X.Modules)
    (s : 𝟙_ X.Modules ⟶ L) :
    schemePullbackUnitHomLinearMap k (𝟙 X) L s ≫
      (Scheme.Modules.pullbackId X).hom.app L = s := by
  change ((Scheme.Modules.pullbackObjUnitIso (𝟙 X)).inv ≫
    (Scheme.Modules.pullback (𝟙 X)).map s) ≫ _ = _
  rw [Category.assoc]
  erw [(Scheme.Modules.pullbackId X).hom.naturality s]
  change (Scheme.Modules.pullbackObjUnitIso (𝟙 X)).inv ≫
    (Scheme.Modules.pullbackId X).hom.app (𝟙_ X.Modules) ≫ s = s
  rw [← Scheme.Modules.pullbackObjUnitIso_id, Iso.inv_hom_id_assoc]

omit f g in
@[reassoc]
theorem schemePullbackUnitHomLinearMap_congr {f g : X ⟶ Y}
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] (equal : f = g)
    (L : Y.Modules) (s : 𝟙_ Y.Modules ⟶ L) :
    schemePullbackUnitHomLinearMap k f L s ≫
        (Scheme.Modules.pullbackCongr equal).hom.app L =
      schemePullbackUnitHomLinearMap k g L s := by
  exact Scheme.Modules.pullback_unit_map_congr equal s

end UnitMaps

section Exterior

variable {X Y Z W : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [Z.Over (Spec (.of k))] [W.Over (Spec (.of k))]
  (p : Z ⟶ X) (q : Z ⟶ Y) (h : W ⟶ Z)
  [p.IsOver (Spec (.of k))] [q.IsOver (Spec (.of k))]
  [h.IsOver (Spec (.of k))]
  (L : X.Modules) (M : Y.Modules)

/-- The actual tensor/composition map comparing pullback of an exterior
sheaf with the exterior sheaf of the composite morphisms. -/
def schemeExternalPullbackComparison :
    (Scheme.Modules.pullback h).obj (schemeExteriorSheaf p q L M) ⟶
      schemeExteriorSheaf (h ≫ p) (h ≫ q) L M :=
  Functor.OplaxMonoidal.δ (Scheme.Modules.pullback h) _ _ ≫
    ((Scheme.Modules.pullbackComp h p).hom.app L ⊗ₘ
      (Scheme.Modules.pullbackComp h q).hom.app M)

/-- The canonical exterior unit-source map respects pullback and the
actual two composition comparisons. -/
@[reassoc]
theorem schemeExternalUnitHom_pullback
    (s : 𝟙_ X.Modules ⟶ L) (t : 𝟙_ Y.Modules ⟶ M) :
    schemePullbackUnitHomLinearMap k h (schemeExteriorSheaf p q L M)
        (moduleTensorUnitHomBilinear k Z _ _
          (schemePullbackUnitHomLinearMap k p L s)
          (schemePullbackUnitHomLinearMap k q M t)) ≫
        schemeExternalPullbackComparison p q h L M =
      moduleTensorUnitHomBilinear k W _ _
        (schemePullbackUnitHomLinearMap k (h ≫ p) L s)
        (schemePullbackUnitHomLinearMap k (h ≫ q) M t) := by
  rw [schemeExternalPullbackComparison, ← Category.assoc,
    schemePullbackUnitHomLinearMap_tensor]
  change ((λ_ (𝟙_ W.Modules)).inv ≫ (_ ⊗ₘ _)) ≫ (_ ⊗ₘ _) = _
  rw [Category.assoc, tensorHom_comp_tensorHom,
    schemePullbackUnitHomLinearMap_comp, schemePullbackUnitHomLinearMap_comp]
  rfl

omit p q h L M in
/-- Pullback of an actual global section, expressed through its canonical
unit-source morphism and the genuine structure-sheaf comparison. -/
def schemePullbackSectionsLinearMap (h : W ⟶ Z) [h.IsOver (Spec (.of k))]
    (F : Z.Modules) :
    (FiniteCover.schemeBaseSections k Z ⊤).obj F →ₗ[k]
      (FiniteCover.schemeBaseSections k W ⊤).obj ((Scheme.Modules.pullback h).obj F) :=
  (moduleUnitActualSectionsLinearEquiv k W _).toLinearMap.comp
    ((schemePullbackUnitHomLinearMap k h F).comp
      (moduleUnitActualSectionsLinearEquiv k Z F).symm.toLinearMap)

/-- Pulling back the actual exterior section and applying the canonical
tensor/composition map gives the exterior section along the composites. -/
theorem schemeExternalSection_pullback
    (s : (FiniteCover.schemeBaseSections k X ⊤).obj L)
    (t : (FiniteCover.schemeBaseSections k Y ⊤).obj M) :
    (FiniteCover.schemeBaseSections k W ⊤).map
        (schemeExternalPullbackComparison p q h L M)
        (schemePullbackSectionsLinearMap k h (schemeExteriorSheaf p q L M)
          (schemeExternalSection k p q L M s t)) =
      schemeExternalSection k (h ≫ p) (h ≫ q) L M s t := by
  apply (moduleUnitActualSectionsLinearEquiv k W _).symm.injective
  rw [moduleUnitActualSectionsLinearEquiv_symm_naturality]
  simp only [schemePullbackSectionsLinearMap, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, schemeExternalSection, LinearEquiv.symm_apply_apply]
  exact schemeExternalUnitHom_pullback k p q h L M _ _

end Exterior

end ToricPower
end
