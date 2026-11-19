module

public import ToricPower.ExtAdjunctionMates
public import ToricPower.ModuleCohomologyFunctorIso

/-!
# Cartier-source naturality of the actual Ext / cohomology comparison

An actual morphism `O(D) ⟶ O(E)` acts on Ext by precomposition.
Its action on the inverse-Cartier twist is the conjugate transformation
of the proved tensor adjunctions. The comparison intertwines these two
actual maps in every degree. A separate calculation can identify this
conjugate transformation with a specified monomial map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X]

local instance cartierSourceHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The actual dual-twist transformation induced by a Cartier-source
morphism through the exact tensor adjunctions. -/
def cartierDualTwistMap {D E : CartierDivisor X} (f : D.sheaf ⟶ E.sheaf) :
    tensorLeft (-E).sheaf ⟶ tensorLeft (-D).sheaf :=
  conjugateEquiv (cartierTensorEquivalence E).toAdjunction
    (cartierTensorEquivalence D).toAdjunction ((tensoringLeft X.Modules).map f)

/-- The component of the natural Cartier comparison has the stated
actual unit-source Ext formula. -/
theorem cartierExtCohomologyNatIso_hom_apply (D : CartierDivisor X)
    (M : X.Modules) (n : ℕ) (e : Ext.{u} D.sheaf M n) :
    (cartierExtCohomologyNatIso k X D n).hom.app M e =
      moduleUnitExtCohomology k X ((-D).sheaf ⊗ M) n
        ((cartierTensorEquivalence D).toAdjunction.extEquiv
          ((Ext.mk₀ (ρ_ D.sheaf).hom).comp e (zero_add n))) := by
  rfl

/-- The all-degree natural comparison commutes with every actual
Cartier-source map, acting contravariantly on Ext and through its genuine
dual-twist transformation on ordinary sheaf cohomology. -/
@[reassoc]
theorem cartierExtCohomologyNatIso_source_naturality
    {D E : CartierDivisor X} (f : D.sheaf ⟶ E.sheaf)
    (M : X.Modules) (n : ℕ) :
    ((extFunctor n).map f.op).app M ≫
        (cartierExtCohomologyNatIso k X D n).hom.app M =
      (cartierExtCohomologyNatIso k X E n).hom.app M ≫
        (cohomologyFunctor X n).map ((cartierDualTwistMap X f).app M) := by
  ext e
  change (cartierExtCohomologyNatIso k X D n).hom.app M
      ((Ext.mk₀ f).comp e (zero_add n)) =
    cohomologyMap ((cartierDualTwistMap X f).app M) n
      ((cartierExtCohomologyNatIso k X E n).hom.app M e)
  rw [cartierExtCohomologyNatIso_hom_apply,
    cartierExtCohomologyNatIso_hom_apply,
    Ext.mk₀_comp_mk₀_assoc, ← rightUnitor_naturality f,
    ← Ext.mk₀_comp_mk₀_assoc]
  have mate := extEquiv_conjugate (cartierTensorEquivalence E).toAdjunction
    (cartierTensorEquivalence D).toAdjunction ((tensoringLeft X.Modules).map f)
    ((Ext.mk₀ (ρ_ E.sheaf).hom).comp e (zero_add n))
  exact (congrArg (moduleUnitExtCohomology k X ((-D).sheaf ⊗ M) n) mate).trans
    (moduleUnitExtCohomology_naturality k X n
      ((cartierDualTwistMap X f).app M) _)

end ToricPower
