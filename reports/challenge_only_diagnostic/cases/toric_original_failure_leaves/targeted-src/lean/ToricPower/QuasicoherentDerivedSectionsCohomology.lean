module

public import ToricPower.QuasicoherentAffineProjective
public import ToricPower.QuasicoherentCartierExt
public import ToricPower.CartierHomSectionsDiagram
public import ToricPower.DerivedHomPlusExt
public import ToricPower.RightDerivedPlusNatIso

/-!
# Derived quasicoherent global sections and ordinary sheaf cohomology

The ordinary functor of actual scalar sections is naturally Hom from the
actual structure sheaf in QCoh. Its right-derived value on a single sheaf
is compared with actual QCoh Ext. The exact inclusion into module sheaves
preserves these Ext groups because quasicoherent injectives are genuinely
flasque, a fact proved from finite affine covers. Finally, Ext from the
structure sheaf is ordinary sheaf cohomology.

The resulting additive equivalence preserves zero and nonzero classes
in every nonnegative degree. No equivalence of ambient derived categories
or preservation of injectives by the inclusion is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite

namespace ToricPower

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- Global sections are the literal linear Hom from the structure sheaf
in the actual quasicoherent category, naturally in every coefficient map. -/
def quasicoherentUnitSectionsNatIso :
    (linearCoyoneda k (QCoh X)).obj (op (quasicoherentUnitObject X)) ≅
      quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤ :=
  NatIso.ofComponents
    (fun M => ((quasicoherentUnderlyingHomLinearEquiv k X
      (quasicoherentUnitObject X) M).trans
        (moduleUnitActualSectionsLinearEquiv k X M.obj)).toModuleIso)
    (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      rfl)

variable [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]

local instance derivedSectionsQCohHasExt : HasExt.{u} (QCoh X) :=
  hasExt_of_enoughInjectives (QCoh X)
local instance derivedSectionsModulesHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

include k in
/-- The actual inclusion-induced Ext map is bijective for the structure
sheaf source; its acyclicity premise follows from proved flasqueness. -/
theorem quasicoherentUnit_mapExt_bijective (M : QCoh X) (degree : ℕ) :
    Function.Bijective ((quasicoherentInclusion X).mapExtAddHom
      (quasicoherentUnitObject X) M degree) := by
  apply mapExt_bijective_of_injective_images_acyclic (quasicoherentInclusion X)
    (quasicoherentUnitObject X)
  intro J injective q
  letI := injective
  exact (moduleUnitExtCohomology k X J.obj (q+1)).toEquiv.subsingleton_congr.mpr
    (quasicoherentInjective_cohomology_subsingleton J q)

/-- The genuine map on Ext induced by quasicoherent inclusion. -/
def quasicoherentUnitExtComparison (M : QCoh X) (degree : ℕ) :
    Ext.{u} (quasicoherentUnitObject X) M degree ≃+
      Ext.{u} (𝟙_ X.Modules) M.obj degree :=
  AddEquiv.ofBijective
    ((quasicoherentInclusion X).mapExtAddHom (quasicoherentUnitObject X) M degree)
    (quasicoherentUnit_mapExt_bijective k X M degree)

variable [HasDerivedCategory.{u+1} (QCoh X)]
  [HasDerivedCategory.{u+1} (ModuleCat.{u} k)]

/-- The right-derived functor of the actual scalar global sections has
exactly the ordinary sheaf cohomology of a quasicoherent sheaf. -/
def quasicoherentDerivedSectionsSingleCohomology (M : QCoh X) (degree : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) (degree : ℤ)).obj
      ((quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (singlePlusComplex M))) ≃+
    TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M.obj degree := by
  let Hom := (linearCoyoneda k (QCoh X)).obj (op (quasicoherentUnitObject X))
  let derived := (rightDerivedPlusNatIso (quasicoherentUnitSectionsNatIso k X)).symm.app
    (DerivedCategory.Plus.Q.obj (singlePlusComplex M))
  exact ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) (degree : ℤ)).mapIso
      derived).toLinearEquiv.toAddEquiv.trans
    ((rightDerivedPlusSingleHomologyIso Hom M (degree : ℤ)).toLinearEquiv.toAddEquiv.trans
      ((injectiveTermwiseHomExtEquiv k (quasicoherentUnitObject X) M degree).trans
        ((quasicoherentUnitExtComparison k X M degree).trans
          (moduleUnitExtCohomology k X M.obj degree).toAddEquiv)))

end ToricPower
end
