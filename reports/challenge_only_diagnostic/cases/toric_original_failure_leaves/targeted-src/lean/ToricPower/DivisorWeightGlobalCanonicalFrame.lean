module

public import ToricPower.DivisorWeightGlobalFrames
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

/-- The comparison for equal scheme maps acts identically on global sections.
Keeping this computation generic avoids expanding either actual toric map. -/
theorem pushforwardCongr_top_sections {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (equal : f = g) (M : X.Modules) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pushforwardCongr equal).hom.app M) ⊤ s = s := by
  rw [Scheme.Modules.pushforwardCongr_hom_app_app]
  change M.presheaf.map (𝟙 (op ⊤)) s = s
  rw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The chart comparison with the literal spectrum of the coordinate-ring
power map. The comparison from the geometric map is the actual pushforward
isomorphism induced by their proved equality. -/
def toricCartierPushforwardChartIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell)
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    ((Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
      (invariantCartierDivisor fan nonempty regular b).sheaf).restrict
        (fan.affineToricChartι cone) ≅
      (Scheme.Modules.pushforward (Spec.map (chartPowerRingHom fan cone ell))).obj
        (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf) := by
  letI := toricSchemeIntegral fan nonempty
  exact toricCartierPushforwardGeometricChartIso fan nonempty regular b ell hell cone ≪≫
    (Scheme.Modules.pushforwardCongr (affinePowerMap_eq_chartPowerSpec fan ell cone)).app
      (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf)

/-- Top sections of the target chart comparison cancel its chosen Cartier
frame. All transports are the actual scheme-module restriction maps. -/
theorem toricCartierPushforwardChartIso_top_frame (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) (cone : fan.cones)
    (a : affineCoordinateRing fan.lattice cone.val) :
    letI := toricSchemeIntegral fan nonempty
    let U := (fan.affineToricChartι cone).opensRange
    let D := invariantCartierDivisor fan nonempty regular b
    Scheme.Modules.Hom.app
      (toricCartierPushforwardChartIso fan nonempty regular b ell hell cone).hom ⊤
      (D.sheaf.presheaf.map (homOfLE (show
        toricPowerMap fan ell ⁻¹ᵁ ((fan.affineToricChartι cone) ''ᵁ ⊤) ≤ U from
          ((toricPowerMap fan ell).preimage_mono
            (fan.affineToricChartι cone).image_top_eq_opensRange.le).trans
            (toricPower_preimage_chartOpen fan ell hell cone).le)).op
        ((invariantCartierSheafChartTrivialization fan nonempty regular b cone).hom.val.app
          (op (Over.mk (𝟙 U))) (chartCoordinateSectionsEquiv fan cone a))) =
      affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val) a := by
  letI := toricSchemeIntegral fan nonempty
  dsimp only
  simp only [toricCartierPushforwardChartIso, Iso.trans_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [toricCartierPushforwardGeometricChartIso_top_frame fan nonempty regular b ell hell cone a]

end ToricPower
