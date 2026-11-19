module

public import ToricPower.MaximalSupportFanNormal

/-! # The original fan-support predicate in the additive complex presentation

The equality is checked with an arbitrary coefficient complex, before
a geometric affine coresolution is substituted.
-/

@[expose] public noncomputable section

open CategoryTheory TauCeti.Toric
open ToricPower.IntegralArrangement

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

theorem hasFanLocalMorseSupport_iff_additive
    (K : CochainComplex (UniversalIncidenceObject A ⥤ ModuleCat.{0} ℂ) ℤ) :
    HasFanLocalMorseSupport fan regular basis rays K ↔
      ∀ (c : UniversalIncidenceObject A) (ξ : Module.Dual ℝ (Fin n → ℝ)),
        (∀ σ : fan.cones, (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
          fanIntegralFace fan regular (universalCellCharacter fan basis rays c) σ) →
        ((universalLocalMorse A ℂ c
          (universalNegativeHalf A c
            (localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) ξ)).obj K).Acyclic :=
  Iff.rfl

end ToricPower
end
