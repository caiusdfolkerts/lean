module

public import ToricPower.ChartOverHomTransport

/-!
# Chart-map transport respects genuine refinements

This is the compatibility needed for ordinary sheaf gluing. Every
identity is checked on all open subsets, not only on global sections
of an affine chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

namespace ToricPower

universe u

variable {A B X : Scheme.{u}}

/-- Evaluation on equal opens commutes with the canonical transports. -/
theorem overHom_sections_eq_transport {M N : X.Modules} {U W Z : X.Opens}
    (f : M.over U ⟶ N.over U) (hW : W ≤ U) (hZ : Z ≤ U)
    (equal : W = Z) (value : Γ(M,W)) :
    f.val.app (op (Over.mk (homOfLE hW))) value =
      N.presheaf.map (eqToHom equal).op
        (f.val.app (op (Over.mk (homOfLE hZ)))
          (M.presheaf.map (eqToHom equal.symm).op value)) := by
  subst Z
  simp only [eqToHom_refl,op_id,CategoryTheory.Functor.map_id,ConcreteCategory.id_apply]

/-- Reading a local morphism on a smaller actual chart agrees with
first reading it on the larger chart and then restricting. -/
theorem chartHomOfOverHom_refinement
    (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') {M N : X.Modules}
    (f : M.over a.opensRange ⟶ N.over a.opensRange) :
    chartHomOfOverHom a'
        (restrictOverHom X.ringCatSheaf (homOfLE (chartImage_le c a a' square)) f) =
      (chartRestrictionIso c a a' square M).inv ≫
        (restrictFunctor c).map (chartHomOfOverHom a f) ≫
        (chartRestrictionIso c a a' square N).hom := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro value
  have imageEqual : a' ''ᵁ U = a ''ᵁ c ''ᵁ U := by
    subst a'
    exact Scheme.Hom.comp_image c a U
  have expected := overHom_sections_eq_transport f
    ((a'.image_le_opensRange U).trans (chartImage_le c a a' square))
    (a.image_le_opensRange (c ''ᵁ U)) imageEqual value
  simp only [Hom.comp_app,ConcreteCategory.comp_apply,
    chartHomOfOverHom_sections,restrictOverHom_app,restrictFunctor_map_app,
    chartRestrictionIso,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    Iso.app_hom,Iso.app_inv,restrictFunctorComp_hom_app_app,
    restrictFunctorComp_inv_app_app,restrictFunctorCongr_hom_app_app,
    restrictFunctorCongr_inv_app_app] at ⊢
  erw [chartHomOfOverHom_sections a f (c ''ᵁ U)]
  erw [← M.presheaf.map_comp_apply,← N.presheaf.map_comp_apply]
  exact expected

/-- Compatible actual chart maps have literally equal image-open
restrictions, with no supplementary compatibility premise. -/
theorem chartOverIso_refinement
    (c : B ⟶ A) (a : A ⟶ X) (a' : B ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] [IsOpenImmersion a']
    (square : c ≫ a = a') {M N : X.Modules}
    (large : M.restrict a ≅ N.restrict a)
    (small : M.restrict a' ≅ N.restrict a')
    (compatible : (chartRestrictionIso c a a' square M).symm ≪≫
      (restrictFunctor c).mapIso large ≪≫ chartRestrictionIso c a a' square N = small) :
    restrictOverHom X.ringCatSheaf (homOfLE (chartImage_le c a a' square))
        (chartOverIso a large).hom = (chartOverIso a' small).hom := by
  apply chartHomOfOverHom_injective a'
  rw [chartHomOfOverHom_refinement c a a' square,
    chartHomOfOverHom_chartOverIso a,chartHomOfOverHom_chartOverIso a']
  exact congrArg Iso.hom compatible

end ToricPower

end
