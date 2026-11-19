module

public import ToricPower.ModuleUnitExtCohomology
public import ToricPower.CartierTensorEquivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Module Ext and actual sheaf cohomology

The comparison is proved by dimension shifting through actual injective
module sheaves.  Their underlying abelian sheaves are flasque by
`InjectiveModuleFlasque`, so both sides have the required exact connecting
maps.  Degree zero uses the actual unit-section correspondence; degree
one compares the two actual quotient kernels; every higher degree uses
the two actual connecting isomorphisms.

Tensoring by a Cartier sheaf is the proved exact equivalence with inverse
tensoring by its negative divisor.  Its actual Ext adjunction therefore
identifies Ext from a Cartier line bundle with the cohomology of the
dual-twisted target.  No derived tensor or acyclicity is assumed.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

section Cartier

open TauCeti.AlgebraicGeometry.Scheme

variable [IsIntegral X]

/-- The genuine inverse Cartier tensor functor preserves injectives
because it is an actual equivalence, not merely a termwise formula. -/
instance cartierTensor_preservesInjectiveObjects (D : CartierDivisor X) :
    (tensorLeft D.sheaf).PreservesInjectiveObjects := by
  change (cartierTensorEquivalence D).functor.PreservesInjectiveObjects
  infer_instance

/-- The actual tensor duality on Ext, followed by the proved module-Ext
comparison with ordinary sheaf cohomology. -/
def cartierExtCohomology (D : CartierDivisor X) (M : X.Modules) (n : ℕ) :
    Ext.{u} D.sheaf M n ≃+ TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology ((-D).sheaf ⊗ M) n :=
  (TauCeti.extAddEquivOfIso (ρ_ D.sheaf).symm (Iso.refl M) n).trans
    (((cartierTensorEquivalence D).toAdjunction.extEquiv (n := n)).trans
      (moduleUnitExtCohomology k X ((-D).sheaf ⊗ M) n).toAddEquiv)

/-- For a Cartier line-bundle target the twist is literally the sheaf
of the divisor difference, via rational-section multiplication. -/
def cartierExtCartierCohomology (D E : CartierDivisor X) (n : ℕ) :
    Ext.{u} D.sheaf E.sheaf n ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (-D + E).sheaf n :=
  (cartierExtCohomology k X D E.sheaf n).trans
    (((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X n).mapIso
      (CartierDivisor.tensorSheafIso (-D) E)).addCommGroupIsoToAddEquiv)

end Cartier

end ToricPower

end
