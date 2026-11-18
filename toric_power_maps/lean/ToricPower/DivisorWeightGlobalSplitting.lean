module

public import ToricPower.DivisorWeightGlobalComparison
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Global residue splitting for invariant Cartier divisors

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


variable {κ : Type u} [Fintype κ]

/-- The single canonical residue sum is a global isomorphism of actual
module sheaves, for every invariant divisor and every positive integer. -/
theorem toricResidueSheafSum_isIso (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) :
    letI := toricSchemeIntegral fan nonempty
    IsIso (toricResidueSheafSum fan nonempty regular basis b ell hell) := by
  letI := toricSchemeIntegral fan nonempty
  let comparison := toricResidueSheafSum fan nonempty regular basis b ell hell
  let atlas := (invariantDivisorCharacterAtlas fan regular b).cartierEquationAtlas nonempty
  let forget := SheafOfModules.toSheaf.{u} fan.algebraicRealization.ringCatSheaf
  have globalIso : IsIso (forget.map comparison) := by
    apply CategoryTheory.Sheaf.isIso_of_coversTop
      ((Opens.coversTop_iff (fan.algebraicRealization : Type _)
        (fun cone : fan.cones => (fan.affineToricChartι cone).opensRange)).mpr
          atlas.covers.iSup_eq_top)
    intro cone
    letI := toricResidueSheafSum_restrict_isIso fan nonempty regular basis b ell hell cone
    letI := residueRestriction_iso_of_affine (fan.affineToricChartι cone) comparison
    change IsIso ((SheafOfModules.toSheaf
      (fan.algebraicRealization.ringCatSheaf.over (fan.affineToricChartι cone).opensRange)).map
        (comparison.over (fan.affineToricChartι cone).opensRange))
    infer_instance
  letI := globalIso
  have presheafIso : IsIso ((Scheme.Modules.toPresheaf fan.algebraicRealization).map comparison) := by
    change IsIso ((sheafToPresheaf
      (Opens.grothendieckTopology fan.algebraicRealization) AddCommGrpCat).map
        (forget.map comparison))
    infer_instance
  letI := presheafIso
  exact (isIso_iff_of_reflects_iso comparison
    (Scheme.Modules.toPresheaf fan.algebraicRealization)).mp presheafIso

/-- Full residue decomposition of the actual pushforward of an invariant
Cartier divisor sheaf on an arbitrary nonempty smooth toric fan. Every
lattice residue is present, including all torus-factor directions. -/
def toricPowerInvariantCartierSplitting (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) :
    letI := toricSchemeIntegral fan nonempty
    (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
      (invariantCartierDivisor fan nonempty regular b).sheaf ≅
        ⨁ toricResidueSheafFamily fan nonempty regular basis b ell := by
  letI := toricSchemeIntegral fan nonempty
  letI := toricResidueSheafSum_isIso fan nonempty regular basis b ell hell
  exact (asIso (toricResidueSheafSum fan nonempty regular basis b ell hell)).symm

end ToricPower
