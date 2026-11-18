module

public import ToricPower.DivisorWeightGlobalComponents
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

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
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

variable {κ : Type u} [Fintype κ]

/-- On every actual chart, the single canonical global morphism agrees
with the full affine isomorphism, not merely with unrelated local objects. -/
theorem toricResidueSheafSum_chart_comparison (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (toricResidueChartFrameIso fan nonempty regular basis b ell cone).hom ≫
      (Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
        (toricResidueSheafSum fan nonempty regular basis b ell hell) ≫
      (toricCartierPushforwardChartIso fan nonempty regular b ell hell cone).hom =
    (affineLinearBiproductIso (chartPowerRingHom fan cone ell)
      (toricFramedResidueModuleIso fan regular basis b ell hell cone)).hom := by
  letI := toricSchemeIntegral fan nonempty
  classical
  apply finiteBiproductFrameRestrictionIso_compare
    (targetSheaf := (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
      (invariantCartierDivisor fan nonempty regular b).sheaf)
    (result := (Scheme.Modules.pushforward (Spec.map (chartPowerRingHom fan cone ell))).obj
      (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf))
    (fan.affineToricChartι cone)
    (toricResidueSheafFamily fan nonempty regular basis b ell)
    (fun residue => toricCartierAffineFrame fan nonempty regular
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue))) cone)
    (toricResidueSheafSum fan nonempty regular basis b ell hell)
    (toricCartierPushforwardChartIso fan nonempty regular b ell hell cone).hom
    (affineLinearBiproductIso (chartPowerRingHom fan cone ell)
      (toricFramedResidueModuleIso fan regular basis b ell hell cone)).hom
  intro residue
  rw [toricResidueSheafSum_summand fan nonempty regular basis b ell hell residue]
  exact (toricResidueSheafMap_chart_component fan nonempty regular basis b ell hell cone residue).trans
    (affineLinearBiproductIso_summand (chartPowerRingHom fan cone ell)
      (toricFramedResidueModuleIso fan regular basis b ell hell cone) residue).symm


/-- The restriction of the canonical global sum to every cone chart is an
isomorphism. This follows from the proved morphism equality above. -/
theorem toricResidueSheafSum_restrict_isIso (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    IsIso ((Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
      (toricResidueSheafSum fan nonempty regular basis b ell hell)) := by
  letI := toricSchemeIntegral fan nonempty
  rw [← isIso_comp_right_iff _
      (toricCartierPushforwardChartIso fan nonempty regular b ell hell cone).hom,
    ← isIso_comp_left_iff
      (toricResidueChartFrameIso fan nonempty regular basis b ell cone).hom,
    toricResidueSheafSum_chart_comparison]
  infer_instance


end ToricPower
