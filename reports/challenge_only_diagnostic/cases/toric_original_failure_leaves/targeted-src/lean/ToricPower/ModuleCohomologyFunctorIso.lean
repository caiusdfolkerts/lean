module

public import ToricPower.ModuleUnitExtNaturality
public import ToricPower.ModuleExtCohomology
public import ToricPower.Cohomology.ExtFunctorAdjunction

/-!
# Natural Ext / cohomology isomorphisms of actual functors

These isomorphisms retain coefficient maps, not just the isomorphism types
of cohomology groups. The unit-source comparison uses the proved all-degree
naturality theorem. The Cartier-source comparison then uses the actual
exact tensor adjunction and the right-unit isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleCohomologyFunctorHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The all-degree comparison is an actual natural isomorphism between
the literal covariant Ext functor and ordinary sheaf cohomology. -/
def moduleUnitExtCohomologyNatIso (n : ℕ) :
    (extFunctor n).obj (op (𝟙_ X.Modules)) ≅
      TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X n :=
  NatIso.ofComponents
    (fun M => (moduleUnitExtCohomology k X M n).toAddEquiv.toAddCommGrpIso)
    (by
      intro M N f
      ext x
      exact moduleUnitExtCohomology_naturality k X n f x)

variable [IsIntegral X]

/-- Ext from a Cartier line bundle is naturally the ordinary cohomology
of the actual inverse-Cartier tensor functor. -/
def cartierExtCohomologyNatIso (D : CartierDivisor X) (n : ℕ) :
    (extFunctor n).obj (op D.sheaf) ≅
      tensorLeft (-D).sheaf ⋙
        TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X n :=
  (extFunctor n).mapIso (ρ_ D.sheaf).op ≪≫
    extRightFunctorIso (cartierTensorEquivalence D).toAdjunction (𝟙_ X.Modules) n ≪≫
    Functor.isoWhiskerLeft (tensorLeft (-D).sheaf)
      (moduleUnitExtCohomologyNatIso k X n)

/-- The natural Cartier comparison exposes an actual commuting square
for every sheaf map and every cohomological degree. -/
theorem cartierExtCohomologyNatIso_naturality
    (D : CartierDivisor X) (n : ℕ) {M N : X.Modules} (f : M ⟶ N) :
    ((extFunctor n).obj (op D.sheaf)).map f ≫
        (cartierExtCohomologyNatIso k X D n).hom.app N =
      (cartierExtCohomologyNatIso k X D n).hom.app M ≫
        (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X n).map
          ((tensorLeft (-D).sheaf).map f) :=
  (cartierExtCohomologyNatIso k X D n).hom.naturality f

end ToricPower

end
