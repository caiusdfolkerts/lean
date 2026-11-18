module

public import ToricPower.ToricInvariantLineBundleClassification
public import ToricPower.DivisorWeightGlobalSplitting

/-!
# Full power-map splitting for arbitrary toric line bundles

The invariant representative is constructed and verified independently in
`ToricInvariantLineBundleClassification`. These wrappers transport the
actual full residue splitting along its genuine module-sheaf isomorphism.
-/

@[expose] public noncomputable section
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.Toric MonoidAlgebra
open scoped Classical
namespace ToricPower
universe u v
variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

section ArbitraryLineBundleSplitting

variable {κ : Type u} [Fintype κ]

/-- Full toric-power splitting for an arbitrary actual line bundle. The
coefficient vector is constructed from its genuine rational frames, and
all residues in the full character lattice are retained. -/
def toricPowerLineBundleSplitting (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ))
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (ell : ℕ) (hell : 0 < ell) :
    letI := toricSchemeIntegral fan nonempty
    (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj F ≅
      ⨁ toricResidueSheafFamily fan nonempty regular basis
        (toricLineBundleInvariantCoefficients fan nonempty regular F) ell := by
  letI := toricSchemeIntegral fan nonempty
  exact (Scheme.Modules.pushforward (toricPowerMap fan ell)).mapIso
    (toricLineBundleInvariantIso fan nonempty regular F) ≪≫
      toricPowerInvariantCartierSplitting fan nonempty regular basis
        (toricLineBundleInvariantCoefficients fan nonempty regular F) ell hell

/-- In particular the full splitting applies to every Cartier divisor,
with no hypothesis that it was presented by an invariant coefficient vector. -/
def toricPowerCartierSplitting (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ))
    (D : letI := toricSchemeIntegral fan nonempty
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
    (ell : ℕ) (hell : 0 < ell) :
    letI := toricSchemeIntegral fan nonempty
    letI := D.isInvertible_sheaf
    (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj D.sheaf ≅
      ⨁ toricResidueSheafFamily fan nonempty regular basis
        (toricLineBundleInvariantCoefficients fan nonempty regular D.sheaf) ell := by
  letI := toricSchemeIntegral fan nonempty
  letI := D.isInvertible_sheaf
  exact toricPowerLineBundleSplitting fan nonempty regular basis D.sheaf ell hell

end ArbitraryLineBundleSplitting

end ToricPower
