module

public import ToricPower.DivisorWeightGlobalCanonicalFrame
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Local comparison of the canonical global residue sum

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
open scoped Classical

namespace ToricPower


universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The canonical global residue map, transported into actual affine frames,
has the literal normalized-coordinate formula on all top sections. -/
theorem toricResidueSheafMap_chart_top_sections (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) (character : N →+ ℤ)
    (cone : fan.cones) (a : affineCoordinateRing fan.lattice cone.val) :
    letI := toricSchemeIntegral fan nonempty
    Scheme.Modules.Hom.app
      ((toricCartierAffineFrame fan nonempty regular
          (toricResidueCoefficients fan b ell character) cone).hom ≫
        (Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
          (toricResidueSheafMap fan nonempty regular b ell hell character) ≫
        (toricCartierPushforwardChartIso fan nonempty regular b ell hell cone).hom) ⊤
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val) a) =
    affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
      (chartPowerRingHom fan cone ell a *
        normalizedToricResidueMonomial fan regular b ell hell character cone) := by
  letI := toricSchemeIntegral fan nonempty
  let D := invariantCartierDivisor fan nonempty regular b
  have frame := cartierOverToAffineFrame_comp_top_sections (fan.affineToricChartι cone)
    (invariantCartierSheafChartTrivialization fan nonempty regular
      (toricResidueCoefficients fan b ell character) cone)
    (toricResidueSheafMap fan nonempty regular b ell hell character)
    (chartCoordinateSectionsEquiv fan cone a)
  simp only [chartCoordinateSectionsEquiv, RingEquiv.trans_apply,
    commRingIsoToRingEquiv_apply, openImmersion_appIso_top_sections] at frame
  rw [← Category.assoc, schemeHom_comp_apply]
  erw [frame]
  erw [toricResidueSheafMap_frame_sections fan nonempty regular b ell hell character cone a]
  change Scheme.Modules.Hom.app
    (toricCartierPushforwardChartIso fan nonempty regular b ell hell cone).hom ⊤
      (D.sheaf.presheaf.map _ (D.sheaf.presheaf.map _ _)) = _
  rw [addPresheaf_map_map D.sheaf.presheaf]
  exact toricCartierPushforwardChartIso_top_frame fan nonempty regular b ell hell cone
    (chartPowerRingHom fan cone ell a *
      normalizedToricResidueMonomial fan regular b ell hell character cone)

end ToricPower
