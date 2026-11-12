module

public import ToricPower.SheafFiniteFrames
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Cartier frames for actual toric chart direct images

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


universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The actual local Cartier frame on the affine scheme, rather than its
slice-site presentation. -/
def toricCartierAffineFrame (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf ≅
      (invariantCartierDivisor fan nonempty regular b).sheaf.restrict
        (fan.affineToricChartι cone) := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierOverToAffineFrame (fan.affineToricChartι cone)
    (invariantCartierDivisor fan nonempty regular b).sheaf
    (invariantCartierSheafChartTrivialization fan nonempty regular b cone)

theorem toricCartierAffineFrame_top (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones)
    (a : affineCoordinateRing fan.lattice cone.val) :
    letI := toricSchemeIntegral fan nonempty
    Scheme.Modules.Hom.app (toricCartierAffineFrame fan nonempty regular b cone).hom ⊤
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val) a) =
    (invariantCartierDivisor fan nonempty regular b).sheaf.presheaf.map
      (eqToHom (fan.affineToricChartι cone).image_top_eq_opensRange).op
      ((invariantCartierSheafChartTrivialization fan nonempty regular b cone).hom.val.app
        (op (Over.mk (𝟙 (fan.affineToricChartι cone).opensRange)))
          (chartCoordinateSectionsEquiv fan cone a)) := by
  letI := toricSchemeIntegral fan nonempty
  have h := cartierOverToAffineFrame_top_sections (fan.affineToricChartι cone)
    (invariantCartierDivisor fan nonempty regular b).sheaf
    (invariantCartierSheafChartTrivialization fan nonempty regular b cone)
    (chartCoordinateSectionsEquiv fan cone a)
  simpa only [toricCartierAffineFrame, chartCoordinateSectionsEquiv, RingEquiv.trans_apply,
    commRingIsoToRingEquiv_apply, openImmersion_appIso_top_sections] using h

/-- Restricting the genuine global pushforward and choosing the target
Cartier frame gives the actual affine structure-sheaf pushforward. -/
def toricCartierPushforwardGeometricChartIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell)
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    ((Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
      (invariantCartierDivisor fan nonempty regular b).sheaf).restrict
        (fan.affineToricChartι cone) ≅
      (Scheme.Modules.pushforward (affinePowerMap fan ell cone)).obj
        (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf) := by
  letI := toricSchemeIntegral fan nonempty
  exact pushforwardRestrictionIso (toricPowerMap fan ell) (affinePowerMap fan ell cone)
      (fan.affineToricChartι cone) (fan.affineToricChartι cone)
      (toricPowerMap_affine_chart fan ell hell cone)
      (toricPower_preimage_chartOpen fan ell hell cone).le
      (invariantCartierDivisor fan nonempty regular b).sheaf ≪≫
    (Scheme.Modules.pushforward (affinePowerMap fan ell cone)).mapIso
      (toricCartierAffineFrame fan nonempty regular b cone).symm

/-- Top sections of the target chart comparison cancel its chosen Cartier
frame. All transports are the actual scheme-module restriction maps. -/
theorem toricCartierPushforwardGeometricChartIso_top_frame (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) (cone : fan.cones)
    (a : affineCoordinateRing fan.lattice cone.val) :
    letI := toricSchemeIntegral fan nonempty
    let U := (fan.affineToricChartι cone).opensRange
    let D := invariantCartierDivisor fan nonempty regular b
    Scheme.Modules.Hom.app
      (toricCartierPushforwardGeometricChartIso fan nonempty regular b ell hell cone).hom ⊤
      (D.sheaf.presheaf.map (homOfLE (show
        toricPowerMap fan ell ⁻¹ᵁ ((fan.affineToricChartι cone) ''ᵁ ⊤) ≤ U from
          ((toricPowerMap fan ell).preimage_mono
            (fan.affineToricChartι cone).image_top_eq_opensRange.le).trans
            (toricPower_preimage_chartOpen fan ell hell cone).le)).op
        ((invariantCartierSheafChartTrivialization fan nonempty regular b cone).hom.val.app
          (op (Over.mk (𝟙 U))) (chartCoordinateSectionsEquiv fan cone a))) =
      affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val) a := by
  letI := toricSchemeIntegral fan nonempty
  let D := invariantCartierDivisor fan nonempty regular b
  let frame := toricCartierAffineFrame fan nonempty regular b cone
  let sectionValue := (invariantCartierSheafChartTrivialization fan nonempty regular b cone).hom.val.app
    (op (Over.mk (𝟙 (fan.affineToricChartι cone).opensRange)))
      (chartCoordinateSectionsEquiv fan cone a)
  simp only [toricCartierPushforwardGeometricChartIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, pushforwardRestrictionIso, asIso_hom]
  rw [pushforwardRestrictionMap_sections]
  change Scheme.Modules.Hom.app frame.inv ⊤
    (D.sheaf.presheaf.map _ (D.sheaf.presheaf.map _ sectionValue)) = _
  rw [addPresheaf_map_map D.sheaf.presheaf]
  change Scheme.Modules.Hom.app frame.inv ⊤
    (D.sheaf.presheaf.map
      (eqToHom (fan.affineToricChartι cone).image_top_eq_opensRange).op sectionValue) = _
  rw [← toricCartierAffineFrame_top]
  exact ConcreteCategory.congr_hom
    (congrArg (fun morphism => Scheme.Modules.Hom.app morphism ⊤) frame.hom_inv_id) _


end ToricPower
