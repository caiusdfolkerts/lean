module

public import ToricPower.DiagonalTopCellLabels
public import ToricPower.DualDiagonalToricResolution

/-!
# The boundary-frame character of an actual top cell is a unit

On a diagonal affine chart, the two genuine top-cell frame characters
sum to minus the boundary equation on every ray. Their sum with the
boundary equation therefore annihilates the cone. Its monomial is a unit
in the actual affine coordinate ring. This is the local distinction
between a nonzero top-class scalar and a possibly vanishing monomial.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (c : NormalizedCell (fanArrangementMatrix fan basis rays) n)

/-- This is the literal sum of the chosen two Cartier frame characters
and the chosen boundary Cartier equation. -/
def diagonalTopCellBoundaryCharacter : N →+ ℤ :=
  coneDivisorCharacter fan regular (diagonalLeftCoefficients fan basis rays c) σ +
    coneDivisorCharacter fan regular (diagonalRightCoefficients fan basis rays c) σ +
      diagonalBoundaryFrameCharacter fan regular σ σ

/-- No regular monomial with positive order remains: the character
vanishes on every ray of the actual affine chart. -/
theorem diagonalTopCellBoundaryCharacter_ray (ρ : fan.Ray) (hρ : ρ.toCone ≤ σ) :
    diagonalTopCellBoundaryCharacter fan regular basis rays σ c
      (fanRayPrimitiveGenerator fan ρ) = 0 := by
  have sum := congrFun (diagonalCoefficient_sum_top fan basis rays c) ρ
  simp only [Pi.add_apply] at sum
  simp only [diagonalTopCellBoundaryCharacter, AddMonoidHom.add_apply,
    coneDivisorCharacter_globalRay fan regular _ σ ρ hρ,
    diagonalBoundaryFrameCharacter_ray fan regular σ σ ρ (le_inf hρ hρ)]
  omega

end ToricPower

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- Integral evaluation respects negation. -/
theorem rayPairing_neg (m : Fin n → ℤ) (i : Fin s) :
    rayPairing A (-m) i = -rayPairing A m i := by
  simpa using rayPairing_sub A 0 m i

variable (S : Set (Fin s))
  (m : Fin n → ℤ) (vanishing : ∀ i ∈ S, rayPairing A m i = 0)

/-- A cone-annihilating integral character and its negative are both
actual regular semigroup characters. -/
def annihilatingRayCharacter : rayCharacterMonoid A S :=
  ⟨m, fun i hi => le_of_eq (vanishing i hi).symm⟩

def negativeAnnihilatingRayCharacter : rayCharacterMonoid A S :=
  ⟨-m, by
    intro i hi
    rw [rayPairing_neg, vanishing i hi]
    exact le_rfl⟩

variable (k : Type) [Field k] (a : k) (nonzero : a ≠ 0)

include nonzero in
/-- Every nonzero scalar multiple of that actual monomial is a unit,
with the inverse given by the negative character and inverse scalar. -/
theorem annihilatingRayCharacter_single_isUnit :
    IsUnit (AddMonoidAlgebra.single (annihilatingRayCharacter A S m vanishing) a :
      AddMonoidAlgebra k (rayCharacterMonoid A S)) := by
  have sum : annihilatingRayCharacter A S m vanishing +
      negativeAnnihilatingRayCharacter A S m vanishing = 0 := by
    apply Subtype.ext
    exact add_neg_cancel m
  refine ⟨⟨_, AddMonoidAlgebra.single
      (negativeAnnihilatingRayCharacter A S m vanishing) a⁻¹, ?_, ?_⟩, rfl⟩
  · change AddMonoidAlgebra.single (annihilatingRayCharacter A S m vanishing) a *
      AddMonoidAlgebra.single (negativeAnnihilatingRayCharacter A S m vanishing) a⁻¹ = 1
    rw [AddMonoidAlgebra.single_mul_single, sum, mul_inv_cancel₀ nonzero]
    rfl
  · change AddMonoidAlgebra.single (negativeAnnihilatingRayCharacter A S m vanishing) a⁻¹ *
      AddMonoidAlgebra.single (annihilatingRayCharacter A S m vanishing) a = 1
    rw [AddMonoidAlgebra.single_mul_single, add_comm, sum, inv_mul_cancel₀ nonzero]
    rfl

end ToricPower.IntegralArrangement

end
