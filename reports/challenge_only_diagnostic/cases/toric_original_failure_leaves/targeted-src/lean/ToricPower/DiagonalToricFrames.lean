module

public import ToricPower.DiagonalCellFrames
public import ToricPower.DiagonalProductCharts
public import ToricPower.DivisorWeightCartierAtlas

/-!
# The actual Cartier characters give the local cellular free basis

The frame characters are the same `coneDivisorCharacter`s used to construct
the actual invariant Cartier divisor sheaves. Their equations on every ray
of each chart prove the hypotheses of the explicit cellular-basis bijection.
Thus the local cellular module is free in precisely the actual Cartier
frames, including the Laurent directions of non-full-dimensional cones.

Candidate source pending the pinned compiler.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ

theorem coneDivisorCharacter_globalRay (b : fan.Ray → ℤ)
    (cone : fan.cones) (ρ : fan.Ray) (hρ : ρ.toCone ≤ cone) :
    coneDivisorCharacter fan regular b cone (fanRayPrimitiveGenerator fan ρ) = b ρ := by
  let r := Fan.Ray.toToricRay fan ρ cone hρ
  have hr : Fan.Ray.ofToricRay fan cone r = ρ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [← hr,fanRayPrimitiveGenerator_ofToricRay,coneDivisorCharacter_ray]
  rfl

def diagonalLeftFrameCharacter {d : ℕ} (j : NormalizedCell A d) : Fin n → ℤ :=
  basis.equivFun
    (coneDivisorCharacter fan regular (diagonalLeftCoefficients fan basis rays j) σ)

def diagonalRightFrameCharacter {d : ℕ} (j : NormalizedCell A d) : Fin n → ℤ :=
  basis.equivFun
    (coneDivisorCharacter fan regular (diagonalRightCoefficients fan basis rays j) τ)

theorem diagonalLeftFrameCharacter_ray {d : ℕ} (j : NormalizedCell A d)
    (ρ : Fin s) (hρ : ρ ∈ S) :
    rayPairing A (diagonalLeftFrameCharacter fan regular basis rays σ j) ρ =
      -reflectedCeiling A j.val ρ := by
  have h := fanArrangementMatrix_character fan basis rays
    (diagonalLeftFrameCharacter fan regular basis rays σ j) (rays ρ)
  simp only [Equiv.symm_apply_apply,diagonalLeftFrameCharacter,
    LinearEquiv.symm_apply_apply] at h
  rw [diagonalLeftFrameCharacter, h,
    coneDivisorCharacter_globalRay fan regular _ σ (rays ρ) hρ]
  simp [diagonalLeftCoefficients]

theorem diagonalRightFrameCharacter_ray {d : ℕ} (j : NormalizedCell A d)
    (ρ : Fin s) (hρ : ρ ∈ T) :
    rayPairing A (diagonalRightFrameCharacter fan regular basis rays τ j) ρ =
      -j.val.val.1 (.inl ρ) := by
  have h := fanArrangementMatrix_character fan basis rays
    (diagonalRightFrameCharacter fan regular basis rays τ j) (rays ρ)
  simp only [Equiv.symm_apply_apply,diagonalRightFrameCharacter,
    LinearEquiv.symm_apply_apply] at h
  rw [diagonalRightFrameCharacter, h,
    coneDivisorCharacter_globalRay fan regular _ τ (rays ρ) hρ]
  simp [diagonalRightCoefficients]

/-- The exact same Cartier character choices on the two actual charts. -/
def toricDiagonalCellFrames (d : ℕ) : DiagonalCellFrames A S T d where
  left := diagonalLeftFrameCharacter fan regular basis rays σ
  right := diagonalRightFrameCharacter fan regular basis rays τ
  left_eq := diagonalLeftFrameCharacter_ray fan regular basis rays σ
  right_eq := diagonalRightFrameCharacter_ray fan regular basis rays τ

/-- The actual local cellular chart module is free on the finite
normalized cells in its literal Cartier frames. -/
def toricDiagonalChartFrameEquiv (d : ℕ) :
    (NormalizedCell A d →₀ DiagonalChartRing ℂ A S T) ≃ₗ[DiagonalChartRing ℂ A S T]
      DiagonalChartChains ℂ A S T d :=
  (toricDiagonalCellFrames fan regular basis rays σ τ d).linearEquiv ℂ

end ToricPower
