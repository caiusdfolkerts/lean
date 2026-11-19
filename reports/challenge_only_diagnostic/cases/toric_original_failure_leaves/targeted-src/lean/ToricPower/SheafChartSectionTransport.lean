module

public import ToricPower.SheafChartSections

/-!
# Sections on actual open charts

These comparisons relate sections on an open image to sections of the
ordinary restricted module sheaf on the chart. Refinement is checked by
the actual presheaf restriction maps. They provide a direct route from
compatible chart morphisms to a comparison of ordinary Čech complexes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ToricPower
universe u
variable {A B X : Scheme.{u}}

/-- The actual section isomorphism for an open chart. -/
def moduleChartSectionsIso (a : A ⟶ X) [IsOpenImmersion a] (M : X.Modules) :
    Γ(M, a.opensRange) ≅ Γ(M.restrict a, ⊤) :=
  M.presheaf.mapIso (eqToIso a.image_top_eq_opensRange).op ≪≫
    (M.restrictAppIso a ⊤).symm

theorem moduleChartSectionsIso_hom_apply (a : A ⟶ X) [IsOpenImmersion a]
    (M : X.Modules) (value : Γ(M, a.opensRange)) :
    (moduleChartSectionsIso a M).hom value =
      M.presheaf.map (eqToHom a.image_top_eq_opensRange).op value := by
  rfl

theorem moduleChartSectionsIso_inv_apply (a : A ⟶ X) [IsOpenImmersion a]
    (M : X.Modules) (value : Γ(M.restrict a, ⊤)) :
    (moduleChartSectionsIso a M).inv value =
      M.presheaf.map (eqToHom a.image_top_eq_opensRange.symm).op value := by
  rfl

/-- Comparison of iterated restriction with the prescribed smaller chart. -/
def chartRestrictionIso (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') (M : X.Modules) :
    (M.restrict a).restrict c ≅ M.restrict a' :=
  ((restrictFunctorComp c a).app M).symm ≪≫ (restrictFunctorCongr square).app M

/-- Inclusion of chart images follows from the actual commuting triangle. -/
theorem chartImage_le (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion a'] (square : c ≫ a = a') :
    a'.opensRange ≤ a.opensRange := by
  rintro point ⟨localPoint, same⟩
  refine ⟨c localPoint, ?_⟩
  exact (congrArg (fun mapping => mapping localPoint) square).trans same

/-- Actual restriction on chart-image sections agrees with ordinary
restriction inside the larger chart, followed by its canonical comparison. -/
theorem moduleChartSectionsIso_restrict
    (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') (M : X.Modules) :
    (moduleChartSectionsIso a M).hom ≫
      (M.restrict a).presheaf.map
        (homOfLE (le_top : c ''ᵁ (⊤ : B.Opens) ≤ ⊤)).op ≫
      ((M.restrict a).restrictAppIso c ⊤).inv ≫
      (chartRestrictionIso c a a' square M).hom.app ⊤ =
    M.presheaf.map (homOfLE (chartImage_le c a a' square)).op ≫
      (moduleChartSectionsIso a' M).hom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro value
  simp only [ConcreteCategory.comp_apply, moduleChartSectionsIso_hom_apply,
    chartRestrictionIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Hom.comp_app, restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ value))) =
    M.presheaf.map _ (M.presheaf.map _ value)
  repeat rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun restriction => M.presheaf.map restriction value) (Subsingleton.elim _ _)

end ToricPower
