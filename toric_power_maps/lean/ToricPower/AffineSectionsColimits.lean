module

public import ToricPower.FiniteAffineIntersectionSections
public import ToricPower.QuasicoherentOpenAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Actual affine sections preserve arbitrary quasicoherent colimits

Restriction is the original exact open restriction. On an affine chart,
the actual section comparison identifies it with the inverse of the
tilde equivalence. Forgetting to abelian groups detects preservation of
colimits, so the base-field sections retain their specified scalar action.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u

/-- Actual open restriction preserves all small colimits of
quasicoherent sheaves, without a separatedness assumption. -/
instance quasicoherentRestriction_preservesColimits
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesColimitsOfSize.{u,u} (quasicoherentRestriction j) where
  preservesColimitsOfShape {J} _ := by
    letI : PreservesColimitsOfShape J
        (quasicoherentRestriction j ⋙ quasicoherentInclusion U) := by
      change PreservesColimitsOfShape J
        (quasicoherentInclusion X ⋙ Scheme.Modules.restrictFunctor j)
      infer_instance
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (quasicoherentRestriction j) (quasicoherentInclusion U)

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  (U : X.Opens) (affine : IsAffineOpen U)

/-- The original affine section identification, natural in actual
quasicoherent coefficients, after forgetting only the scalar structure. -/
def affineSectionsUnderlyingIso :
    quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X U ⋙
        forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u} ≅
      quasicoherentRestriction affine.fromSpec ⋙
        (tildeEquiv (R := .of Γ(X,U))).inverse ⋙
          forget₂ (ModuleCat.{u} Γ(X,U)) AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun M => (Scheme.Modules.fromSpecSectionsEquiv (M.obj : X.Modules)
      affine).toAddEquiv.toAddCommGrpIso)
    (by
      intro M N f
      ext x
      change Scheme.Modules.fromSpecSectionsEquiv (N.obj : X.Modules) affine
          (Scheme.Modules.Hom.app (f.hom : (M.obj : X.Modules) ⟶ N.obj) U x) =
        Scheme.Modules.Hom.app (f.hom : (M.obj : X.Modules) ⟶ N.obj)
          (affine.fromSpec ''ᵁ ⊤)
          (Scheme.Modules.fromSpecSectionsEquiv (M.obj : X.Modules) affine x)
      exact fromSpecSectionsEquiv_naturality f.hom affine x)

include affine in
/-- The genuine base-field affine section functor preserves arbitrary
small colimits of quasicoherent sheaves. -/
theorem affineBaseSections_preservesColimits :
    PreservesColimitsOfSize.{u,u}
      (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X U) where
  preservesColimitsOfShape {J} _ := by
    let G := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
    letI : PreservesColimitsOfShape J
        ((quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X U) ⋙ G) :=
      preservesColimitsOfShape_of_natIso
        (affineSectionsUnderlyingIso k X U affine).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X U) G

end ToricPower

end
