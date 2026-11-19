module

public import ToricPower.DivisorWeightLocalComparison
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Restriction of finite sheaf frames

The canonical global rational-monomial sum is compared on each actual
Cartier generator with the proved full affine residue decomposition. The
local comparisons imply that this single global morphism is an
isomorphism. The cover consists of all cones, with no completeness or
full-dimensionality assumption.

The elementary restriction-equivalence and finite-biproduct helpers are
adapted from BondalThomsen/Toric/Frobenius/MultiplicationGlobalResidueIso
at commit 9a2bdcdcf6b25710459f7f476c9c62de3039b7bb.

Development source: the exact current source must pass the pinned checker
before any declaration is reported as verified.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.Toric

namespace ToricPower

universe schemeUniverse

/-- Restriction twice is restriction along the composite, on actual sections. -/
theorem addPresheaf_map_map {C : Type*} [Category* C]
    (F : C ⥤ AddCommGrpCat.{schemeUniverse}) {U V W : C}
    (f : U ⟶ V) (g : V ⟶ W) (s : F.obj U) :
    F.map g (F.map f s) = F.map (f ≫ g) s := by
  rw [CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]

local instance globalResidueFrameSchemeFiniteBiproducts (schemeModel : Scheme.{schemeUniverse}) :
    HasFiniteBiproducts schemeModel.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance globalResidueFrameSheafFiniteBiproducts
    {Site : Type*} [Category Site] {Topology : GrothendieckTopology Site}
    (ringSheaf : Sheaf Topology RingCat) : HasFiniteBiproducts (SheafOfModules.{schemeUniverse} ringSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance globalResidueRestrictAdditive {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] :
    (Scheme.Modules.restrictFunctor inclusion).Additive :=
  CategoryTheory.Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback inclusion).symm

local instance globalResidueRestrictPreservesBiproduct {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {Index : Type schemeUniverse} [Fintype Index] (objects : Index → Target.Modules) :
    PreservesBiproduct objects (Scheme.Modules.restrictFunctor inclusion) :=
  preservesBiproduct_of_preservesCoproduct _

noncomputable def finiteBiproductFrameRestrictionIso {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {Index : Type schemeUniverse} [Fintype Index] (objects : Index → Target.Modules)
    [HasBiproduct objects]
    (frames : ∀ index, SheafOfModules.unit Source.ringCatSheaf ≅
      (objects index).restrict inclusion) :
    (⨁ fun _ : Index => (SheafOfModules.unit Source.ringCatSheaf : Source.Modules)) ≅
      (⨁ objects).restrict inclusion :=
  biproduct.mapIso frames ≪≫
    ((Scheme.Modules.restrictFunctor inclusion).mapBiproduct objects).symm

theorem finiteBiproductFrameRestrictionIso_summand {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {Index : Type schemeUniverse} [Fintype Index] (objects : Index → Target.Modules)
    [HasBiproduct objects]
    (frames : ∀ index, SheafOfModules.unit Source.ringCatSheaf ≅
      (objects index).restrict inclusion) (index : Index) :
    biproduct.ι (fun _ : Index =>
      (SheafOfModules.unit Source.ringCatSheaf : Source.Modules)) index ≫
      (finiteBiproductFrameRestrictionIso inclusion objects frames).hom =
      (frames index).hom ≫
        (Scheme.Modules.restrictFunctor inclusion).map (biproduct.ι objects index) := by
  simp only [finiteBiproductFrameRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    biproduct.mapIso_hom, biproduct.ι_map_assoc,
    CategoryTheory.Functor.mapBiproduct_inv, biproduct.ι_desc]


/-- A comparison of finite sums is determined by its framed summand maps.
All restriction and biproduct manipulations are proved for abstract sheaves
before the lemma is specialized to toric charts. -/
theorem finiteBiproductFrameRestrictionIso_compare {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {Index : Type schemeUniverse} [Fintype Index] (objects : Index → Target.Modules)
    [HasBiproduct objects]
    (frames : ∀ index, SheafOfModules.unit Source.ringCatSheaf ≅
      (objects index).restrict inclusion)
    {targetSheaf : Target.Modules} {result : Source.Modules}
    (comparison : ⨁ objects ⟶ targetSheaf)
    (targetComparison : targetSheaf.restrict inclusion ⟶ result)
    (affineComparison :
      (⨁ fun _ : Index => (SheafOfModules.unit Source.ringCatSheaf : Source.Modules)) ⟶ result)
    (components : ∀ index,
      (frames index).hom ≫ (Scheme.Modules.restrictFunctor inclusion).map
        (biproduct.ι objects index ≫ comparison) ≫ targetComparison =
      biproduct.ι (fun _ : Index =>
        (SheafOfModules.unit Source.ringCatSheaf : Source.Modules)) index ≫ affineComparison) :
    (finiteBiproductFrameRestrictionIso inclusion objects frames).hom ≫
      (Scheme.Modules.restrictFunctor inclusion).map comparison ≫ targetComparison =
        affineComparison := by
  apply biproduct.hom_ext'
  intro index
  rw [← Category.assoc, ← Category.assoc,
    finiteBiproductFrameRestrictionIso_summand]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  exact components index


noncomputable def residueRestrictSchemeIsoEquivalence {Source Target : Scheme.{schemeUniverse}}
    (schemeIso : Source ≅ Target) : Target.Modules ≌ Source.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor schemeIso.hom)
    (Scheme.Modules.restrictFunctor schemeIso.inv)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      Scheme.Modules.restrictFunctorCongr schemeIso.inv_hom_id.symm ≪≫
      Scheme.Modules.restrictFunctorComp schemeIso.inv schemeIso.hom)
    ((Scheme.Modules.restrictFunctorComp schemeIso.hom schemeIso.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr schemeIso.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId)

local instance residueRestrictSchemeIsoReflects {Source Target : Scheme.{schemeUniverse}}
    (schemeIso : Source ≅ Target) :
    (Scheme.Modules.restrictFunctor schemeIso.hom).ReflectsIsomorphisms :=
  inferInstanceAs (residueRestrictSchemeIsoEquivalence schemeIso).functor.ReflectsIsomorphisms

theorem residueRestriction_iso_of_affine {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {sourceSheaf targetSheaf : Target.Modules} (comparison : sourceSheaf ⟶ targetSheaf)
    [IsIso ((Scheme.Modules.restrictFunctor inclusion).map comparison)] :
    IsIso (comparison.over inclusion.opensRange) := by
  let transport := Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom
  have localIso : IsIso ((Scheme.Modules.restrictFunctor inclusion.opensRange.ι).map comparison) := by
    apply (isIso_iff_of_reflects_iso _ transport).mp
    have compositeIso : IsIso
        ((Scheme.Modules.restrictFunctor
          (inclusion.isoOpensRange.hom ≫ inclusion.opensRange.ι)).map comparison) := by
      let comparisonIso := Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_hom_ι
      rw [← isIso_comp_right_iff _ (comparisonIso.hom.app targetSheaf),
        comparisonIso.hom.naturality]
      infer_instance
    let := compositeIso
    let composition := Scheme.Modules.restrictFunctorComp
      inclusion.isoOpensRange.hom inclusion.opensRange.ι
    change IsIso ((Scheme.Modules.restrictFunctor inclusion.opensRange.ι ⋙
      Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom).map comparison)
    rw [← isIso_comp_left_iff (composition.hom.app sourceSheaf),
      ← composition.hom.naturality]
    infer_instance
  let := localIso
  apply (isIso_iff_of_reflects_iso _ (Scheme.Modules.overEquiv inclusion.opensRange).functor).mp
  let overComparison := Scheme.Modules.overFunctorEquiv inclusion.opensRange
  change IsIso ((SheafOfModules.overFunctor Target.ringCatSheaf inclusion.opensRange ⋙
    (Scheme.Modules.overEquiv inclusion.opensRange).functor).map comparison)
  rw [← isIso_comp_right_iff _ (overComparison.hom.app targetSheaf),
    overComparison.hom.naturality]
  infer_instance


end ToricPower
