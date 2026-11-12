module

public import ToricPower.SchemeExternalSectionPullback

/-!
# Exterior sections pulled back along a common section

When a morphism is a section of both projections, the actual pullback
of an exterior product section is the tensor product of the original
sections. In particular this applies to the diagonal, with all
composition and identity comparisons specified.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u
variable (k : Type u) [Field k]
  {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  (d : X ⟶ Z) (p q : Z ⟶ X)
  [d.IsOver (Spec (.of k))] [p.IsOver (Spec (.of k))] [q.IsOver (Spec (.of k))]

omit q in
@[reassoc]
theorem schemePullbackUnitHomLinearMap_section (sectionEq : d ≫ p = 𝟙 X)
    (L : X.Modules) (s : 𝟙_ X.Modules ⟶ L) :
    schemePullbackUnitHomLinearMap k d ((Scheme.Modules.pullback p).obj L)
        (schemePullbackUnitHomLinearMap k p L s) ≫
        (Scheme.Modules.sectionPullbackIso d p sectionEq).hom.app L = s := by
  simp only [Scheme.Modules.sectionPullbackIso, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
  rw [schemePullbackUnitHomLinearMap_comp_assoc,
    schemePullbackUnitHomLinearMap_congr_assoc, schemePullbackUnitHomLinearMap_id]

/-- The genuine map on the pulled-back exterior sheaf when both
projection composites are the identity. -/
def schemeExternalSectionRetractionMap (firstSection : d ≫ p = 𝟙 X)
    (secondSection : d ≫ q = 𝟙 X) (L M : X.Modules) :
    (Scheme.Modules.pullback d).obj (schemeExteriorSheaf p q L M) ⟶ L ⊗ M :=
  Functor.OplaxMonoidal.δ (Scheme.Modules.pullback d) _ _ ≫
    ((Scheme.Modules.sectionPullbackIso d p firstSection).hom.app L ⊗ₘ
      (Scheme.Modules.sectionPullbackIso d q secondSection).hom.app M)

@[reassoc]
theorem schemeExternalUnitHom_retraction (firstSection : d ≫ p = 𝟙 X)
    (secondSection : d ≫ q = 𝟙 X) (L M : X.Modules)
    (s : 𝟙_ X.Modules ⟶ L) (t : 𝟙_ X.Modules ⟶ M) :
    schemePullbackUnitHomLinearMap k d (schemeExteriorSheaf p q L M)
        (moduleTensorUnitHomBilinear k Z _ _
          (schemePullbackUnitHomLinearMap k p L s)
          (schemePullbackUnitHomLinearMap k q M t)) ≫
        schemeExternalSectionRetractionMap d p q firstSection secondSection L M =
      moduleTensorUnitHomBilinear k X L M s t := by
  rw [schemeExternalSectionRetractionMap, ← Category.assoc,
    schemePullbackUnitHomLinearMap_tensor]
  change ((λ_ (𝟙_ X.Modules)).inv ≫ (_ ⊗ₘ _)) ≫ (_ ⊗ₘ _) = _
  rw [Category.assoc, tensorHom_comp_tensorHom,
    schemePullbackUnitHomLinearMap_section, schemePullbackUnitHomLinearMap_section]
  rfl

/-- Actual global sections, with no frame or affine presentation chosen. -/
theorem schemeExternalSection_retraction (firstSection : d ≫ p = 𝟙 X)
    (secondSection : d ≫ q = 𝟙 X) (L M : X.Modules)
    (s : (FiniteCover.schemeBaseSections k X ⊤).obj L)
    (t : (FiniteCover.schemeBaseSections k X ⊤).obj M) :
    (FiniteCover.schemeBaseSections k X ⊤).map
        (schemeExternalSectionRetractionMap d p q firstSection secondSection L M)
        (schemePullbackSectionsLinearMap k d (schemeExteriorSheaf p q L M)
          (schemeExternalSection k p q L M s t)) =
      moduleUnitActualSectionsLinearEquiv k X (L ⊗ M)
        (moduleTensorUnitHomBilinear k X L M
          ((moduleUnitActualSectionsLinearEquiv k X L).symm s)
          ((moduleUnitActualSectionsLinearEquiv k X M).symm t)) := by
  apply (moduleUnitActualSectionsLinearEquiv k X _).symm.injective
  rw [moduleUnitActualSectionsLinearEquiv_symm_naturality]
  simp only [schemePullbackSectionsLinearMap, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, schemeExternalSection, LinearEquiv.symm_apply_apply]
  exact schemeExternalUnitHom_retraction k d p q firstSection secondSection L M _ _

end ToricPower
end
