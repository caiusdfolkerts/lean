module

public import ToricPower.AffineRightDerivedResolved

/-!
# Comparing an unbounded derived model on resolved inputs

The finite affine coresolution is a quasi-isomorphic replacement for
every complex. Consequently a candidate derived model has the genuine
right-derived universal property as soon as its original comparison
is invertible on these resolved inputs. Naturality transports the
comparison back to every object of the full derived category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor CochainComplex TopologicalSpace

namespace ToricPower

universe u v w z

local instance affineComparisonDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (hV : IsOpenCover V) (l : List I) (hl : ∀ i, i ∈ l)
  {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (H : QCoh X ⥤ D) [H.Additive]
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  (G : DerivedCategory (QCoh X) ⥤ DerivedCategory D)
  (β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ G)

include hV hl

/-- Verification on the actual finite coresolution proves the full
unbounded right-derived universal property for the original unit. -/
theorem affine_isRightDerivedFunctor_of_resolvedUnit
    (resolved : ∀ K : CochainComplex (QCoh X) ℤ,
      IsIso (β.app ((affineConeCoresolution V l).obj K))) :
    G.IsRightDerivedFunctor β (HomologicalComplex.quasiIso (QCoh X) (.up ℤ)) := by
  let R := affineConeDerivedStage V H l
  let α := affineRightDerivedUnit V H l
  let W := HomologicalComplex.quasiIso (QCoh X) (.up ℤ)
  letI := affineConeDerivedStage_isRightDerivedFunctor V H l hl hV
  apply (R.isRightDerivedFunctor_iff_isIso_rightDerivedDesc α W G β).mpr
  let γ := R.rightDerivedDesc α W G β
  let pre := Localization.whiskeringLeftFunctor' (DerivedCategory.Q (C := QCoh X))
    W (DerivedCategory D)
  letI : IsIso (pre.map γ) := by
    haveI (K : CochainComplex (QCoh X) ℤ) : IsIso ((pre.map γ).app K) := by
      let J := (affineConeCoresolution V l).obj K
      let η : K ⟶ J := (affineConeCoaugmentation V l).app K
      let f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj J := DerivedCategory.Q.map η
      letI : QuasiIso η := affineConeCoaugmentation_quasiIso V l hl hV K
      letI : IsIso f := inferInstance
      letI : IsIso (α.app J) :=
        affineRightDerivedUnit_isIso V l hl H J
          (affineConeCoresolution_rightOrthogonal V l K)
      have eq : α.app J ≫ γ.app (DerivedCategory.Q.obj J) = β.app J :=
        R.rightDerived_fac_app α W G β J
      letI : IsIso (γ.app (DerivedCategory.Q.obj J)) := by
        apply (isIso_comp_left_iff (α.app J) _).mp
        rw [eq]
        exact resolved K
      change IsIso (γ.app (DerivedCategory.Q.obj K))
      apply (isIso_comp_right_iff _ (G.map f)).mp
      exact (γ.naturality f) ▸
        (inferInstanceAs (IsIso (R.map f ≫ γ.app (DerivedCategory.Q.obj J))))
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso γ pre

end ToricPower

end
