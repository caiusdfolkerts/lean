module

public import ToricPower.SheafFiniteFrames
public import ToricPower.SheafChartSectionTransport
public import ToricPower.SheafOverlapRestriction

/-!
# Transport between actual chart maps and their image-open maps

The chart equivalence is the ordinary equivalence with the image open,
followed by the equivalence between its open site and the slice site.
The section formula below records that this transport evaluates the
original local morphism on exactly the same open subset.
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

/-- The genuine equivalence between the image-open slice and the chart. -/
def chartOverEquivalence (a : A ⟶ X) [IsOpenImmersion a] :
    SheafOfModules (X.ringCatSheaf.over a.opensRange) ≌ A.Modules :=
  (overEquiv a.opensRange).trans (residueRestrictSchemeIsoEquivalence a.isoOpensRange)

/-- Read a slice-site morphism as an actual chart morphism. -/
def chartHomOfOverHom (a : A ⟶ X) [IsOpenImmersion a]
    {M N : X.Modules} (f : M.over a.opensRange ⟶ N.over a.opensRange) :
    M.restrict a ⟶ N.restrict a :=
  (cartierOverToAffineRestrictionIso a M).inv ≫
    (cartierOverToAffine a).map f ≫ (cartierOverToAffineRestrictionIso a N).hom

/-- On every open of the chart, transport is evaluation on its image. -/
theorem chartHomOfOverHom_sections (a : A ⟶ X) [IsOpenImmersion a]
    {M N : X.Modules} (f : M.over a.opensRange ⟶ N.over a.opensRange)
    (U : A.Opens) (value : Γ(M.restrict a,U)) :
    (chartHomOfOverHom a f).app U value =
      f.val.app (op (Over.mk (homOfLE (a.image_le_opensRange U)))) value := by
  simp only [chartHomOfOverHom,Hom.comp_app,ConcreteCategory.comp_apply,
    cartierOverToAffineRestrictionIso_inv_sections,cartierOverToAffine_map_sections,
    cartierOverToAffineRestrictionIso_sections]
  let original : Over a.opensRange := Over.mk (homOfLE (a.image_le_opensRange U))
  let transported := (Opens.overEquivalence a.opensRange).symm.functor.obj
    (a.isoOpensRange.hom ''ᵁ U)
  let reindex : original ⟶ transported :=
    Over.homMk (eqToHom (cartierOverToAffine_image a U))
  have naturality := ConcreteCategory.congr_hom (f.val.naturality reindex.op)
    (M.presheaf.map (eqToHom (cartierOverToAffine_image a U).symm).op value)
  change f.val.app (op original)
      (M.presheaf.map (eqToHom (cartierOverToAffine_image a U)).op
        (M.presheaf.map (eqToHom (cartierOverToAffine_image a U).symm).op value)) =
    N.presheaf.map (eqToHom (cartierOverToAffine_image a U)).op
      (f.val.app (op transported)
        (M.presheaf.map (eqToHom (cartierOverToAffine_image a U).symm).op value)) at naturality
  rw [← ConcreteCategory.comp_apply,← CategoryTheory.Functor.map_comp] at naturality
  simp only [← op_comp,eqToHom_trans,eqToHom_refl,op_id,
    CategoryTheory.Functor.map_id,ConcreteCategory.id_apply] at naturality
  exact naturality.symm

/-- Transport an actual chart isomorphism to the slice over its image. -/
def chartOverIso (a : A ⟶ X) [IsOpenImmersion a] {M N : X.Modules}
    (e : M.restrict a ≅ N.restrict a) : M.over a.opensRange ≅ N.over a.opensRange :=
  (chartOverEquivalence a).fullyFaithfulFunctor.preimageIso
    (cartierOverToAffineRestrictionIso a M ≪≫ e ≪≫
      (cartierOverToAffineRestrictionIso a N).symm)

/-- The two actual transports recover the prescribed chart morphism. -/
theorem chartHomOfOverHom_chartOverIso (a : A ⟶ X) [IsOpenImmersion a]
    {M N : X.Modules} (e : M.restrict a ≅ N.restrict a) :
    chartHomOfOverHom a (chartOverIso a e).hom = e.hom := by
  dsimp only [chartHomOfOverHom,chartOverIso]
  change (cartierOverToAffineRestrictionIso a M).inv ≫
    (chartOverEquivalence a).functor.map
      ((chartOverEquivalence a).fullyFaithfulFunctor.preimageIso _).hom ≫
    (cartierOverToAffineRestrictionIso a N).hom = _
  simp only [Functor.FullyFaithful.preimageIso_hom,Functor.FullyFaithful.map_preimage,
    Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id_assoc,
    Iso.inv_hom_id,Category.comp_id]

/-- Transport to the actual chart is injective on local morphisms. -/
theorem chartHomOfOverHom_injective (a : A ⟶ X) [IsOpenImmersion a]
    {M N : X.Modules} :
    Function.Injective (chartHomOfOverHom a (M := M) (N := N)) := by
  intro f g equal
  apply (chartOverEquivalence a).functor.map_injective
  exact (cancel_mono (cartierOverToAffineRestrictionIso a N).hom).mp
    ((cancel_epi (cartierOverToAffineRestrictionIso a M).inv).mp equal)

end ToricPower

end
