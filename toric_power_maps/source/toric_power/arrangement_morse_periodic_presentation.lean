module

public import ToricPower.ArrangementNormalizedMorseDefinitions
public import ToricPower.ArrangementNormalizedSupport

/-! # The actual periodic pullback of the normalized complex model

This comparison is fixed at the level of whole functors. Its components
retain every coefficient, differential, and incidence map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open ToricPower.IntegralArrangement

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

/-- Equality of the whole universal pullback, before evaluation on a
geometric coefficient complex. -/
def normalizedUniversalMorseModel_periodicIso :
    normalizedUniversalMorseModel fan nonempty regular basis rays ≅
      normalizedAffineMorseModel fan nonempty regular basis rays ⋙
        (ElementPushdown.baseRestriction (universalCoverProjection A)
          (D := ModuleCat.{0} ℂ)).mapHomologicalComplex (.up ℤ) :=
  Iso.refl _

/-- This is the literal periodic model, with the same actual differentials. -/
def normalizedUniversalMorseModel_periodicComponent
    (K : CochainComplex (QCoh fan.algebraicRealization) ℤ) :
    (normalizedUniversalMorseModel fan nonempty regular basis rays).obj K ≅
      universalPeriodicComplex A ℂ
        ((normalizedAffineMorseModel fan nonempty regular basis rays).obj K) :=
  (normalizedUniversalMorseModel_periodicIso fan nonempty regular basis rays).app K

end ToricPower
end
