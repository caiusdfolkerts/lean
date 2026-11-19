module

public import ToricPower.ArrangementLocalMorse
public import ToricPower.FanArrangementNormals

/-!
# The actual normal cover forced by maximal cohomological support

The local Morse condition is stated on the full integral arrangement.
Every normal covector at a maximal nonzero cell has nonzero Morse
fiber. Consequently it belongs to an actual integral face of the
original fan; the previously proved fan geometry then supplies the
complete linear inclusion and integral affine slice.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TauCeti.Toric Set
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A

/-- Vanishing outside the actual fan conormals, tested using the full
local face region and its genuine derived-section comparison. -/
def HasFanLocalMorseSupport (K : CochainComplex (U ⥤ ModuleCat.{0} ℂ) ℤ) : Prop :=
  ∀ (c : U) (ξ : Module.Dual ℝ (Fin n → ℝ)),
    (∀ σ : fan.cones, (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
      fanIntegralFace fan regular (universalCellCharacter fan basis rays c) σ) →
    ((universalLocalMorse A ℂ c
      (universalNegativeHalf A c
        (localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) ξ)).obj K).Acyclic

/-- The fan cover is a consequence of the genuine Morse calculation;
it is not an extra geometric assumption on the maximal cell. -/
theorem maximalSupport_fanNormal_cover
    (K : CochainComplex (U ⥤ ModuleCat.{0} ℂ) ℤ)
    (morse : HasFanLocalMorseSupport fan regular basis rays K)
    (c : U) (nonzero : ¬ (K.asFunctor.obj c).Acyclic)
    (maximal : ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1) :
    ∀ v ∈ universalCellFanNormal fan basis rays c,
      ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular
        (universalCellCharacter fan basis rays c) σ := by
  intro v normal
  by_contra! outside
  let ξ := -(normalCoordinateEquiv fan.lattice basis v)
  have normalCovector : ξ ∈ cellNormal (augmentedForms A) c.2.val.2 :=
    (cellNormal (augmentedForms A) c.2.val.2).neg_mem normal
  have vanishes := morse c ξ (by
    intro σ
    simpa only [ξ,neg_neg,LinearEquiv.symm_apply_apply] using outside σ)
  exact maximalSupport_negativeHalf_morse_nonacyclic A ℂ K c nonzero maximal
    (localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) ξ normalCovector vanishes

/-- Every maximal nonzero cell determines a complete linear inclusion
in the original fan. -/
theorem maximalSupport_completeLinear
    (K : CochainComplex (U ⥤ ModuleCat.{0} ℂ) ℤ)
    (morse : HasFanLocalMorseSupport fan regular basis rays K)
    (c : U) (nonzero : ¬ (K.asFunctor.obj c).Acyclic)
    (maximal : ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1) :
    universalCellFanNormal fan basis rays c ∈ fanCompleteSubspaces fan :=
  universalCellFanNormal_complete_of_cover fan basis rays regular c
    (maximalSupport_fanNormal_cover fan regular basis rays K morse c nonzero maximal)

end ToricPower

end
