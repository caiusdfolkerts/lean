module

public import ToricPower.ToricPowerProjectionFormula
public import ToricPower.QuasicoherentTensorColimits

/-!
# The toric projection formula, natural in both coefficients

Both naturality laws are retained in the actual quasicoherent categories
before passage to complexes. The right-tensor version uses the genuine
symmetry isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  (ell : ℕ) (positive : 0 < ell)

local notation "Q" => QCoh fan.algebraicRealization
local notation "F" => quasicoherentPullback (toricPowerMap fan ell)

/-- Fix the target coefficient and vary the source coefficient. -/
def toricPowerProjectionCoefficientComparison (M : Q) :
    letI := toricPowerMap_finite fan regular ell positive
    quasicoherentAffinePushforward (toricPowerMap fan ell) ⋙ tensorLeft M ⟶
      tensorLeft ((F).obj M) ⋙ quasicoherentAffinePushforward (toricPowerMap fan ell) := by
  letI := toricPowerMap_finite fan regular ell positive
  exact {
    app := fun P => ObjectProperty.homMk ((monoidalProjectionComparison
      (Scheme.Modules.pullbackPushforwardAdjunction (toricPowerMap fan ell)) P.obj).app M.obj)
    naturality := fun {P P'} g => by
      apply ObjectProperty.hom_ext
      exact monoidalProjectionComparison_naturality_right
        (Scheme.Modules.pullbackPushforwardAdjunction (toricPowerMap fan ell)) g.hom M.obj }

/-- The second naturality law, in the other coefficient. -/
def toricPowerProjectionCurriedComparison :
    letI := toricPowerMap_finite fan regular ell positive
    curriedTensor Q ⋙ (Functor.whiskeringLeft Q Q Q).obj
        (quasicoherentAffinePushforward (toricPowerMap fan ell)) ⟶
      F ⋙ curriedTensor Q ⋙ (Functor.whiskeringRight Q Q Q).obj
        (quasicoherentAffinePushforward (toricPowerMap fan ell)) := by
  letI := toricPowerMap_finite fan regular ell positive
  exact {
    app := toricPowerProjectionCoefficientComparison fan regular ell positive
    naturality := fun {M M'} g => by
      apply NatTrans.ext
      funext P
      apply ObjectProperty.hom_ext
      exact (monoidalProjectionComparison
        (Scheme.Modules.pullbackPushforwardAdjunction (toricPowerMap fan ell)) P.obj).naturality
        g.hom }

/-- The full natural projection isomorphism for two arbitrary coefficients. -/
def toricPowerProjectionCurriedIso :
    letI := toricPowerMap_finite fan regular ell positive
    curriedTensor Q ⋙ (Functor.whiskeringLeft Q Q Q).obj
        (quasicoherentAffinePushforward (toricPowerMap fan ell)) ≅
      F ⋙ curriedTensor Q ⋙ (Functor.whiskeringRight Q Q Q).obj
        (quasicoherentAffinePushforward (toricPowerMap fan ell)) := by
  letI := toricPowerMap_finite fan regular ell positive
  let α := toricPowerProjectionCurriedComparison fan regular ell positive
  letI : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    haveI : IsIso ((quasicoherentInclusion fan.algebraicRealization).map ((α.app M).app P)) := by
      change IsIso ((monoidalProjectionComparison
        (Scheme.Modules.pullbackPushforwardAdjunction (toricPowerMap fan ell)) P.obj).app M.obj)
      exact toricPowerProjectionComparison_isIso fan regular ell positive P M
    exact isIso_of_reflects_iso _ (quasicoherentInclusion fan.algebraicRealization)
  exact asIso α

/-- The same formula with the varying coefficient on the right. -/
def toricPowerProjectionCurriedRightIso :
    letI := toricPowerMap_finite fan regular ell positive
    (curriedTensor Q).flip ⋙ (Functor.whiskeringLeft Q Q Q).obj
        (quasicoherentAffinePushforward (toricPowerMap fan ell)) ≅
      F ⋙ (curriedTensor Q).flip ⋙ (Functor.whiskeringRight Q Q Q).obj
        (quasicoherentAffinePushforward (toricPowerMap fan ell)) := by
  letI := toricPowerMap_finite fan regular ell positive
  exact (Functor.isoWhiskerRight (BraidedCategory.curriedBraidingNatIso Q)
      ((Functor.whiskeringLeft Q Q Q).obj
        (quasicoherentAffinePushforward (toricPowerMap fan ell)))).symm ≪≫
    toricPowerProjectionCurriedIso fan regular ell positive ≪≫
    Functor.isoWhiskerLeft F
      (Functor.isoWhiskerRight (BraidedCategory.curriedBraidingNatIso Q)
        ((Functor.whiskeringRight Q Q Q).obj
          (quasicoherentAffinePushforward (toricPowerMap fan ell))))

def toricPowerProjectionCoefficientIso (M : Q) :
    letI := toricPowerMap_finite fan regular ell positive
    quasicoherentAffinePushforward (toricPowerMap fan ell) ⋙ tensorRight M ≅
      tensorRight ((F).obj M) ⋙ quasicoherentAffinePushforward (toricPowerMap fan ell) := by
  letI := toricPowerMap_finite fan regular ell positive
  exact (toricPowerProjectionCurriedRightIso fan regular ell positive).app M

end ToricPower

end
