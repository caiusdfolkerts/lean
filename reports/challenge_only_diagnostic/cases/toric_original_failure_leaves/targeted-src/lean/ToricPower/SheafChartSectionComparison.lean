module

public import ToricPower.SheafChartSectionTransport

/-!
# Compatible chart maps on actual section groups

A morphism on an open chart induces a morphism on the original sheaf's
sections over the chart image. Compatibility with ordinary restriction
on the charts implies compatibility with the original restriction maps.
All comparisons below use the actual module sheaves and actual open sets.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ToricPower
universe u
variable {A B X : Scheme.{u}}

/-- A chart morphism read on the original open-image section groups. -/
def moduleChartSectionsMap (a : A ⟶ X) [IsOpenImmersion a]
    {M N : X.Modules} (mapping : M.restrict a ⟶ N.restrict a) :
    Γ(M, a.opensRange) ⟶ Γ(N, a.opensRange) :=
  (moduleChartSectionsIso a M).hom ≫ mapping.app ⊤ ≫
    (moduleChartSectionsIso a N).inv

/-- A chart isomorphism gives an isomorphism of the actual section groups. -/
def moduleChartComparisonIso (a : A ⟶ X) [IsOpenImmersion a]
    {M N : X.Modules} (comparison : M.restrict a ≅ N.restrict a) :
    Γ(M, a.opensRange) ≅ Γ(N, a.opensRange) :=
  moduleChartSectionsIso a M ≪≫
    ((toPresheaf A).mapIso comparison).app (op ⊤) ≪≫
      (moduleChartSectionsIso a N).symm

theorem moduleChartComparisonIso_hom (a : A ⟶ X) [IsOpenImmersion a]
    {M N : X.Modules} (comparison : M.restrict a ≅ N.restrict a) :
    (moduleChartComparisonIso a comparison).hom =
      moduleChartSectionsMap a comparison.hom := rfl

/-- Restriction from the larger chart, followed by its canonical
identification with the prescribed smaller chart. -/
def moduleChartRestriction (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') (M : X.Modules) :
    Γ(M.restrict a, ⊤) ⟶ Γ(M.restrict a', ⊤) :=
  (M.restrict a).presheaf.map
    (homOfLE (le_top : c ''ᵁ (⊤ : B.Opens) ≤ ⊤)).op ≫
  ((M.restrict a).restrictAppIso c ⊤).inv ≫
  (chartRestrictionIso c a a' square M).hom.app ⊤

/-- Naturality on global chart sections before the canonical chart comparison. -/
theorem moduleChartRestriction_pre_naturality (c : B ⟶ A) [IsOpenImmersion c]
    {M N : A.Modules} (mapping : M ⟶ N) :
    mapping.app ⊤ ≫ N.presheaf.map
        (homOfLE (le_top : c ''ᵁ (⊤ : B.Opens) ≤ ⊤)).op ≫
      (N.restrictAppIso c ⊤).inv =
    M.presheaf.map (homOfLE (le_top : c ''ᵁ (⊤ : B.Opens) ≤ ⊤)).op ≫
      (M.restrictAppIso c ⊤).inv ≫ ((restrictFunctor c).map mapping).app ⊤ := by
  change mapping.app ⊤ ≫ N.presheaf.map _ =
    M.presheaf.map _ ≫ mapping.app (c ''ᵁ ⊤)
  exact (mapping.mapPresheaf.naturality
    (homOfLE (le_top : c ''ᵁ (⊤ : B.Opens) ≤ ⊤)).op).symm

/-- A compatible pair of actual chart maps commutes with the chart-section
restriction, including the canonical restriction-composition comparisons. -/
theorem moduleChartRestriction_naturality
    (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') {M N : X.Modules}
    (large : M.restrict a ⟶ N.restrict a)
    (small : M.restrict a' ⟶ N.restrict a')
    (compatible : (restrictFunctor c).map large ≫
        (chartRestrictionIso c a a' square N).hom =
      (chartRestrictionIso c a a' square M).hom ≫ small) :
    large.app ⊤ ≫ moduleChartRestriction c a a' square N =
      moduleChartRestriction c a a' square M ≫ small.app ⊤ := by
  have component := congrArg (fun mapping => Hom.app mapping ⊤) compatible
  simp only [Hom.comp_app] at component
  dsimp only [moduleChartRestriction]
  have pre := congrArg (fun mapping => mapping ≫
      (chartRestrictionIso c a a' square N).hom.app ⊤)
    (moduleChartRestriction_pre_naturality c large)
  simp only [Category.assoc] at pre ⊢
  rw [pre, component]

/-- Compatible actual chart maps induce maps commuting with the original
sheaf restriction maps on the chart images. -/
theorem moduleChartSectionsMap_restrict
    (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') {M N : X.Modules}
    (large : M.restrict a ⟶ N.restrict a)
    (small : M.restrict a' ⟶ N.restrict a')
    (compatible : (restrictFunctor c).map large ≫
        (chartRestrictionIso c a a' square N).hom =
      (chartRestrictionIso c a a' square M).hom ≫ small) :
    moduleChartSectionsMap a large ≫
      N.presheaf.map (homOfLE (chartImage_le c a a' square)).op =
    M.presheaf.map (homOfLE (chartImage_le c a a' square)).op ≫
      moduleChartSectionsMap a' small := by
  have rowM : (moduleChartSectionsIso a M).hom ≫
      moduleChartRestriction c a a' square M =
    M.presheaf.map (homOfLE (chartImage_le c a a' square)).op ≫
      (moduleChartSectionsIso a' M).hom :=
    moduleChartSectionsIso_restrict c a a' square M
  have rowN : (moduleChartSectionsIso a N).hom ≫
      moduleChartRestriction c a a' square N =
    N.presheaf.map (homOfLE (chartImage_le c a a' square)).op ≫
      (moduleChartSectionsIso a' N).hom :=
    moduleChartSectionsIso_restrict c a a' square N
  apply (cancel_mono (moduleChartSectionsIso a' N).hom).mp
  simp only [moduleChartSectionsMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← rowN, Iso.inv_hom_id_assoc,
    moduleChartRestriction_naturality c a a' square large small compatible,
    ← Category.assoc, rowM, Category.assoc]

/-- Isomorphism compatibility implies the corresponding morphism square. -/
theorem moduleChartSectionsIso_restrict_of_iso
    (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') {M N : X.Modules}
    (large : M.restrict a ≅ N.restrict a)
    (small : M.restrict a' ≅ N.restrict a')
    (compatible : (chartRestrictionIso c a a' square M).symm ≪≫
      (restrictFunctor c).mapIso large ≪≫ chartRestrictionIso c a a' square N = small) :
    (moduleChartComparisonIso a large).hom ≫
      N.presheaf.map (homOfLE (chartImage_le c a a' square)).op =
    M.presheaf.map (homOfLE (chartImage_le c a a' square)).op ≫
      (moduleChartComparisonIso a' small).hom := by
  rw [moduleChartComparisonIso_hom, moduleChartComparisonIso_hom]
  apply moduleChartSectionsMap_restrict c a a' square
  have component := congrArg Iso.hom compatible
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom] at component
  exact (cancel_epi (chartRestrictionIso c a a' square M).inv).mp
    (by simpa only [Category.assoc, Iso.inv_hom_id_assoc] using component)

end ToricPower
