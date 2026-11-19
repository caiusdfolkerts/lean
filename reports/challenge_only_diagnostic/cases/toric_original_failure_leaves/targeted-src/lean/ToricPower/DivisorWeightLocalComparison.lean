module

public import ToricPower.DivisorWeightFramedSplitting
public import ToricPower.SheafChartSections

/-!
# Comparison of the global residue maps with their affine decompositions

The maps are compared on the actual local Cartier generators and then on
all sections by linearity and sheaf restriction. No overlap equality or
local splitting assertion is supplied as additional toric data.

The elementary open-immersion section formulas are adapted from
BondalThomsen/Toric/Frobenius/MultiplicationResidueMapComparison.lean and
MultiplicationResidueLocalIso.lean at commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb.

Development source: a successful check of the current exact hash is still
required before these declarations count as verified.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Classical

namespace ToricPower

universe schemeUniverse

noncomputable def affinePushforwardStructureSectionsEquiv {Source Target : CommRingCat.{schemeUniverse}}
    (ring_map : Target ⟶ Source) :
    letI := Module.compHom Source ring_map.hom
    (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (Spec.map ring_map)).obj
        (SheafOfModules.unit (Spec Source).ringCatSheaf))) ≃ₗ[Target] Source := by
  letI := Module.compHom Source ring_map.hom
  refine
    { (Scheme.ΓSpecIso Source).commRingCatIsoToRingEquiv.toAddEquiv with
      map_smul' := ?_ }
  intro scalar element
  let value : Γ(Spec Source, ⊤) := element
  change (Scheme.ΓSpecIso Source).hom
      ((Spec.map ring_map).appTop ((Scheme.ΓSpecIso Target).inv scalar) * value) =
    ring_map.hom scalar * (Scheme.ΓSpecIso Source).hom value
  rw [map_mul]
  have naturality := congrArg (fun morphism : Target ⟶ Source => morphism scalar)
    (Scheme.ΓSpecIso_inv_naturality_assoc ring_map (Scheme.ΓSpecIso Source).hom)
  simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] using congrArg (fun coefficient : Source =>
    coefficient * (Scheme.ΓSpecIso Source).hom value) naturality.symm


/-- The affine pushforward section comparison inverts the canonical map
from the coordinate ring to global sections. -/
theorem affinePushforwardStructureSectionsEquiv_affineGlobalSections
    {Source Target : CommRingCat.{schemeUniverse}} (ring_map : Target ⟶ Source)
    (a : Source) :
    letI := Module.compHom Source ring_map.hom
    affinePushforwardStructureSectionsEquiv ring_map
      (affineGlobalSectionsEquiv Source a) = a := by
  exact (Scheme.ΓSpecIso Source).inv_hom_id_apply a


/-- Reading a canonical affine global section recovers its coordinate. -/
theorem affineGlobalSectionsEquiv_to_ring (R : CommRingCat.{schemeUniverse}) (a : R) :
    (Scheme.ΓSpecIso R).hom (affineGlobalSectionsEquiv R a) = a :=
  (Scheme.ΓSpecIso R).inv_hom_id_apply a


noncomputable def affinePushforwardStructureTildeIso {Source Target : CommRingCat.{schemeUniverse}}
    (ring_map : Target ⟶ Source) :
    letI := Module.compHom Source ring_map.hom
    tilde (ModuleCat.of Target Source) ≅
      (Scheme.Modules.pushforward (Spec.map ring_map)).obj
        (SheafOfModules.unit (Spec Source).ringCatSheaf) := by
  letI := Module.compHom Source ring_map.hom
  let pushforward := (Scheme.Modules.pushforward (Spec.map ring_map)).obj
    (SheafOfModules.unit (Spec Source).ringCatSheaf)
  letI : IsIso pushforward.fromTildeΓ := isIso_fromTildeΓ_pushforward ring_map _
  change tilde (ModuleCat.of Target Source) ≅ pushforward
  exact (tilde.functor Target).mapIso
      (affinePushforwardStructureSectionsEquiv ring_map).symm.toModuleIso ≪≫
    asIso pushforward.fromTildeΓ


/-- The actual sheaf morphism associated to a linear map into a restricted
coordinate ring. -/
def affineLinearSheafMap {R S : CommRingCat.{schemeUniverse}} (φ : R ⟶ S)
    (a : ModuleCat.of R R ⟶ affineRestrictedRing φ) :
    SheafOfModules.unit (Spec R).ringCatSheaf ⟶
      (Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec S).ringCatSheaf) :=
  tildeSelf.inv ≫ (tilde.functor R).map a ≫
    (affinePushforwardStructureTildeIso φ).hom

/-- Affine sheafification gives precisely the original linear map on top
sections. This follows from the actual tilde–sections counit. -/
theorem affineLinearSheafMap_top {R S : CommRingCat.{schemeUniverse}} (φ : R ⟶ S)
    (a : ModuleCat.of R R ⟶ affineRestrictedRing φ) (r : R) :
    affinePushforwardStructureSectionsEquiv φ
      (Scheme.Modules.Hom.app (affineLinearSheafMap φ a) ⊤
        (tilde.toOpen (ModuleCat.of R R) ⊤ r)) = a r := by
  let pushforward := (Scheme.Modules.pushforward (Spec.map φ)).obj
    (SheafOfModules.unit (Spec S).ringCatSheaf)
  let comparison : affineRestrictedRing φ ⟶ (moduleSpecΓFunctor (R := R)).obj pushforward :=
    (affinePushforwardStructureSectionsEquiv φ).symm.toModuleIso.hom
  have naturality := tilde.toOpen_map_app a ⊤
  have comparison_naturality := tilde.toOpen_map_app comparison ⊤
  have counit := Scheme.Modules.toOpen_fromTildeΓ_app pushforward ⊤
  have section_eq := ConcreteCategory.congr_hom naturality r
  have comparison_eq := ConcreteCategory.congr_hom comparison_naturality (a r)
  have counit_eq := ConcreteCategory.congr_hom counit (comparison (a r))
  simp only [ConcreteCategory.comp_apply] at section_eq comparison_eq counit_eq
  change affinePushforwardStructureSectionsEquiv φ
    ((modulesSpecToSheaf.map pushforward.fromTildeΓ).hom.app (op ⊤)
      ((modulesSpecToSheaf.map (tilde.map comparison)).hom.app (op ⊤)
        ((modulesSpecToSheaf.map (tilde.map a)).hom.app (op ⊤)
          (tilde.toOpen (ModuleCat.of R R) ⊤ r)))) = _
  rw [section_eq, comparison_eq]
  change affinePushforwardStructureSectionsEquiv φ
    ((modulesSpecToSheaf.map pushforward.fromTildeΓ).hom.app (op ⊤)
      (tilde.toOpen ((modulesSpecToSheaf.obj pushforward).presheaf.obj (op ⊤)) ⊤
        (comparison (a r)))) = _
  rw [counit_eq]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]
  exact (affinePushforwardStructureSectionsEquiv φ).apply_symm_apply _


/-- The same affine map formula expressed only in the coordinate ring.
This statement avoids any conversion between two scalar-restricted module
presentations when it is specialized to an actual toric chart. -/
theorem affineLinearSheafMap_top_coordinate {R S : CommRingCat.{schemeUniverse}} (φ : R ⟶ S)
    (a : ModuleCat.of R R ⟶ affineRestrictedRing φ) (r : R) :
    (Scheme.ΓSpecIso S).hom
      (Scheme.Modules.Hom.app (affineLinearSheafMap φ a) ⊤
        (tilde.toOpen (ModuleCat.of R R) ⊤ r)) = a r := by
  exact affineLinearSheafMap_top φ a r


/-- The canonical module biproduct comparison sends an inclusion to the
corresponding single-coordinate vector. -/
theorem moduleBiproductIsoPi_summand {R : Type schemeUniverse} [Ring R]
    {Index : Type schemeUniverse} [Fintype Index] [DecidableEq Index] (family : Index → ModuleCat.{schemeUniverse} R)
    (index : Index) :
    biproduct.ι family index ≫ (moduleFiniteBiproductIsoPi family).hom =
      ModuleCat.ofHom (LinearMap.single R (fun j => family j) index) := by
  classical
  apply (cancel_mono (moduleFiniteBiproductIsoPi family).inv).mp
  apply biproduct.hom_ext
  intro other
  rw [Category.assoc (biproduct.ι _ index), Iso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, moduleFiniteBiproductIsoPi_inv_comp_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  by_cases equal : index = other
  · subst other
    simp
  · simp [equal]

local instance residueChartSchemeFiniteBiproducts (X : Scheme.{schemeUniverse}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- Sheafification preserves these finite biproducts in the full scheme
universe because it preserves coproducts and zero morphisms. -/
local instance affineTildePreservesBiproduct (R : CommRingCat.{schemeUniverse})
    {Index : Type schemeUniverse} [Fintype Index] (family : Index → ModuleCat.{schemeUniverse} R) :
    PreservesBiproduct family (tilde.functor R) := by
  letI : (tilde.functor R).PreservesZeroMorphisms := ⟨fun _ _ => tilde.map_zero⟩
  letI : (tilde.functor R).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  exact preservesBiproduct_of_preservesCoproduct _

/-- A module isomorphism from a finite free module sheafifies to the actual
affine structure-sheaf direct image. -/
def affineLinearBiproductIso {R S : CommRingCat.{schemeUniverse}} (φ : R ⟶ S)
    {Index : Type schemeUniverse} [Fintype Index]
    (e : ModuleCat.of R (Index → R) ≅ affineRestrictedRing φ) :
    (⨁ fun _ : Index =>
      (SheafOfModules.unit (Spec R).ringCatSheaf : (Spec R).Modules)) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec S).ringCatSheaf) := by
  letI : (tilde.functor R).PreservesZeroMorphisms := ⟨fun _ _ => tilde.map_zero⟩
  letI : (tilde.functor R).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : PreservesBiproduct (fun _ : Index => ModuleCat.of R R) (tilde.functor R) :=
    preservesBiproduct_of_preservesCoproduct _
  exact biproduct.mapIso (fun _ => tildeSelf.symm) ≪≫
    ((tilde.functor R).mapBiproduct (fun _ : Index => ModuleCat.of R R)).symm ≪≫
    (tilde.functor R).mapIso (moduleFiniteBiproductIsoPi (fun _ : Index => ModuleCat.of R R)) ≪≫
    (tilde.functor R).mapIso e ≪≫ affinePushforwardStructureTildeIso φ

theorem affineLinearBiproductIso_summand {R S : CommRingCat.{schemeUniverse}} (φ : R ⟶ S)
    {Index : Type schemeUniverse} [Fintype Index] [DecidableEq Index]
    (e : ModuleCat.of R (Index → R) ≅ affineRestrictedRing φ) (index : Index) :
    biproduct.ι (fun _ : Index =>
      (SheafOfModules.unit (Spec R).ringCatSheaf : (Spec R).Modules)) index ≫
        (affineLinearBiproductIso φ e).hom =
    affineLinearSheafMap φ
      (ModuleCat.ofHom (LinearMap.single R (fun _ : Index => R) index) ≫ e.hom) := by
  simp only [affineLinearBiproductIso, affineLinearSheafMap, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, biproduct.mapIso_hom]
  rw [biproduct.ι_map_assoc]
  rw [← Category.assoc _ ((tilde.functor R).mapBiproduct _).inv,
    CategoryTheory.Functor.mapBiproduct_inv, biproduct.ι_desc]
  rw [← CategoryTheory.Functor.map_comp_assoc, moduleBiproductIsoPi_summand]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

section OpenSquareSections

variable {X X' Y Y' : Scheme.{schemeUniverse}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k]

/-- The literal containment of opens associated to the square. -/
theorem square_image_preimage_le (square : j ≫ f = g ≫ k) (U : Y'.Opens) :
    j ''ᵁ (g ⁻¹ᵁ U) ≤ f ⁻¹ᵁ (k ''ᵁ U) := by
  rintro point ⟨localPoint, member, rfl⟩
  refine ⟨g localPoint, member, ?_⟩
  exact (congrArg (fun morphism : X' ⟶ Y => morphism localPoint) square).symm

/-- Open base change on sections is exactly restriction along the square's
image-preimage containment. -/
theorem pushforwardRestrictionMap_sections (square : j ≫ f = g ≫ k) (M : X.Modules)
    (U : Y'.Opens) (s : Γ(M, f ⁻¹ᵁ (k ''ᵁ U))) :
    Scheme.Modules.Hom.app (pushforwardRestrictionMap f g j k square M) U s =
      M.presheaf.map (homOfLE (square_image_preimage_le f g j k square U)).op s := by
  simp only [pushforwardRestrictionMap, pushforwardSquareIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctor_map_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  erw [← Iso.app_hom, restrictFunctorAdjCounitIso_app]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ s)) = _
  simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  congr 1

end OpenSquareSections



section ToricFrameValues

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

open TauCeti.Toric

/-- The global residue morphism has the expected normalized monomial in
both actual Cartier frames, on the entire chart. -/
theorem toricResidueSheafMap_frame_sections (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell)
    (character : N →+ ℤ) (cone : fan.cones)
    (a : affineCoordinateRing fan.lattice cone.val) :
    letI := toricSchemeIntegral fan nonempty
    let U := (fan.affineToricChartι cone).opensRange
    let source := invariantCartierDivisor fan nonempty regular
      (toricResidueCoefficients fan b ell character)
    let target := invariantCartierDivisor fan nonempty regular b
    Scheme.Modules.Hom.app (toricResidueSheafMap fan nonempty regular b ell hell character) U
      ((invariantCartierSheafChartTrivialization fan nonempty regular
        (toricResidueCoefficients fan b ell character) cone).hom.val.app
          (op (Over.mk (𝟙 U))) (chartCoordinateSectionsEquiv fan cone a)) =
    target.sheaf.presheaf.map
      (eqToHom (toricPower_preimage_chartOpen fan ell hell cone)).op
      ((invariantCartierSheafChartTrivialization fan nonempty regular b cone).hom.val.app
        (op (Over.mk (𝟙 U))) (chartCoordinateSectionsEquiv fan cone
          (chartPowerRingHom fan cone ell a *
            normalizedToricResidueMonomial fan regular b ell hell character cone))) := by
  letI := toricSchemeIntegral fan nonempty
  let U := (fan.affineToricChartι cone).opensRange
  letI := chartOpen_nonempty fan cone
  letI := rationalPullback_nonempty_preimage (toricPowerMap fan ell)
    (toricPower_genericPoint fan nonempty regular ell hell) U
  let source := invariantCartierDivisor fan nonempty regular
    (toricResidueCoefficients fan b ell character)
  let target := invariantCartierDivisor fan nonempty regular b
  let sourceAtlas := (invariantDivisorCharacterAtlas fan regular
    (toricResidueCoefficients fan b ell character)).cartierEquationAtlas nonempty
  let targetAtlas := (invariantDivisorCharacterAtlas fan regular b).cartierEquationAtlas nonempty
  let sourceSection : Γ(source.sheaf, U) := (sourceAtlas.chartTrivialization cone).hom.val.app
    (op (Over.mk (𝟙 U))) (chartCoordinateSectionsEquiv fan cone a)
  let targetSection : Γ(target.sheaf, U) := (targetAtlas.chartTrivialization cone).hom.val.app
    (op (Over.mk (𝟙 U))) (chartCoordinateSectionsEquiv fan cone
      (chartPowerRingHom fan cone ell a *
        normalizedToricResidueMonomial fan regular b ell hell character cone))
  apply target.sheafι_app_injective (toricPowerMap fan ell ⁻¹ᵁ U)
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
    (toricPowerMap fan ell ⁻¹ᵁ U)).injective
  have factor := congrArg (fun comparison => Scheme.Modules.Hom.app comparison U sourceSection)
    (toricResidueSheafMap_rational fan nonempty regular b ell hell character)
  have restriction := ConcreteCategory.congr_hom
    (target.sheafι.mapPresheaf.naturality
      (eqToHom (toricPower_preimage_chartOpen fan ell hell cone)).op) targetSection
  change Scheme.Modules.Hom.app target.sheafι (toricPowerMap fan ell ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app (toricResidueSheafMap fan nonempty regular b ell hell character)
        U sourceSection) = _ at factor
  change Scheme.Modules.Hom.app target.sheafι (toricPowerMap fan ell ⁻¹ᵁ U)
      (target.sheaf.presheaf.map
        (eqToHom (toricPower_preimage_chartOpen fan ell hell cone)).op targetSection) =
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions fan.algebraicRealization).presheaf.map
      (eqToHom (toricPower_preimage_chartOpen fan ell hell cone)).op
      (Scheme.Modules.Hom.app target.sheafι U targetSection) at restriction
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _
    (Scheme.Modules.Hom.app target.sheafι _
      (Scheme.Modules.Hom.app (toricResidueSheafMap fan nonempty regular b ell hell character)
        U sourceSection)) =
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _
      (Scheme.Modules.Hom.app target.sheafι _
        (target.sheaf.presheaf.map
          (eqToHom (toricPower_preimage_chartOpen fan ell hell cone)).op targetSection))
  rw [factor, restriction,
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map]
  erw [cartierRationalMap_value]
  dsimp only [sourceSection, targetSection]
  erw [sourceAtlas.chartTrivialization_value, targetAtlas.chartTrivialization_value]
  change (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
      toricPowerFunctionField fan nonempty regular ell hell
        ((((rationalCharacterUnit fan nonempty
          (coneDivisorCharacter fan regular (toricResidueCoefficients fan b ell character) cone))⁻¹ :
            fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) *
          chartCoordinateGerm fan nonempty cone a) =
    (((rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone))⁻¹ :
      fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) *
      chartCoordinateGerm fan nonempty cone
        (chartPowerRingHom fan cone ell a *
          normalizedToricResidueMonomial fan regular b ell hell character cone)
  rw [map_mul, map_mul,
    ← toricPowerFunctionField_chartCoordinate fan nonempty regular ell hell cone a,
    normalizedToricResidueMonomial_germ fan nonempty regular b ell hell character cone,
    ← toricResidue_ratio_eq_character fan nonempty regular b ell hell character cone]
  let q := rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone)
  have cancellation : ((q⁻¹ : fan.algebraicRealization.functionFieldˣ) :
      fan.algebraicRealization.functionField) * (q : fan.algebraicRealization.functionField) = 1 :=
    Units.inv_mul q
  calc
    _ = (1 : fan.algebraicRealization.functionField) *
        ((rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
          toricPowerFunctionField fan nonempty regular ell hell
            (((rationalCharacterUnit fan nonempty
              (coneDivisorCharacter fan regular (toricResidueCoefficients fan b ell character) cone))⁻¹ :
                fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) *
          toricPowerFunctionField fan nonempty regular ell hell
            (chartCoordinateGerm fan nonempty cone a)) := by ring
    _ = _ := by rw [← cancellation]; ring

end ToricFrameValues

end ToricPower
