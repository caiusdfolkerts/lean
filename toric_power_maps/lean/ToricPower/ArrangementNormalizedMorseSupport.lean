module

public import ToricPower.ArrangementNormalizedMorseModel
public import ToricPower.ArrangementMorsePeriodicPresentation
public import ToricPower.ArrangementFanMorsePresentation

/-! # Fan-local Morse support of the actual whole complex model

This theorem is proved before choosing a representative of a derived
object; every unbounded input complex is allowed.
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

theorem normalizedAffineMorseModel_hasFanLocalMorseSupport
    (K : CochainComplex (QCoh fan.algebraicRealization) ℤ) :
    HasFanLocalMorseSupport fan regular basis rays
      (universalPeriodicComplex A ℂ
        ((normalizedAffineMorseModel fan nonempty regular basis rays).obj K)) := by
  apply (hasFanLocalMorseSupport_iff_additive fan regular basis rays _).mpr
  intro c ξ outside
  have acyclic := normalizedUniversalMorseModel_acyclic fan nonempty regular basis rays c
    (localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) ξ
    (localStar_convex (augmentedForms A) _)
    (localStar_isOpen (augmentedForms A)
      (fun r => (augmentedForms A r).continuous_of_finiteDimensional) _)
    (mem_localStar_self (augmentedForms A) _) (Set.Subset.refl _) outside
    K
  let comparison := (universalLocalMorse A ℂ c
    (universalNegativeHalf A c
      (localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) ξ)).mapIso
    (normalizedUniversalMorseModel_periodicComponent fan nonempty regular basis rays
      K)
  intro degree
  exact HomologicalComplex.ExactAt.of_iso (acyclic degree) comparison

end ToricPower
end
