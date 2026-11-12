module

public import ToricPower.DiagonalTopCellFrameUnit
public import ToricPower.DualDiagonalFramedTopGenerators

/-!
# The actual top-cell quotient is a unit in its boundary frame

This calculation retains the original free dual basis and the original
top quotient. On a diagonal affine chart the image of a top-cell basis
vector is a single monomial with a nonzero ambient scalar. Its character
annihilates the cone, so both that character and its negative are regular.
The resulting coefficient is therefore a unit in the actual toric ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

include basis rays in
/-- A nonzero scalar times a cone-annihilating character is a unit in
the actual affine toric coordinate ring, including every torus factor. -/
theorem coneAnnihilatingMonomial_isUnit (σ : fan.cones)
    (m : dualSemigroup fan.lattice σ.val)
    (vanishing : ∀ ρ : fan.Ray, ρ.toCone ≤ σ →
      m.val (fanRayPrimitiveGenerator fan ρ) = 0)
    (a : ℂ) (nonzero : a ≠ 0) :
    IsUnit (MonoidAlgebra.single (Multiplicative.ofAdd m) a :
      affineCoordinateRing fan.lattice σ.val) := by
  have coordinates : -basis.equivFun m.val ∈
      rayCharacterMonoid (fanArrangementMatrix fan basis rays)
        (fanConeRaySet fan rays σ) := by
    intro ρ hρ
    rw [rayPairing_neg, fanArrangementMatrix_basis_character,
      vanishing (rays ρ) hρ]
    simp
  have negative : -m.val ∈ dualSemigroup fan.lattice σ.val := by
    have h := (fan_rayCharacterMonoid_iff fan basis rays σ _).mp coordinates
    simpa only [map_neg, LinearEquiv.symm_apply_apply] using h
  let inverseCharacter : dualSemigroup fan.lattice σ.val := ⟨-m.val, negative⟩
  have characterSum : m + inverseCharacter = 0 := by
    apply Subtype.ext
    exact add_neg_cancel m.val
  have characterProduct : Multiplicative.ofAdd m *
      Multiplicative.ofAdd inverseCharacter = 1 :=
    congrArg Multiplicative.ofAdd characterSum
  refine ⟨⟨_, MonoidAlgebra.single (Multiplicative.ofAdd inverseCharacter) a⁻¹,
    ?_, ?_⟩, rfl⟩
  · change MonoidAlgebra.single (Multiplicative.ofAdd m) a *
      MonoidAlgebra.single (Multiplicative.ofAdd inverseCharacter) a⁻¹ = 1
    rw [MonoidAlgebra.single_mul_single, characterProduct, mul_inv_cancel₀ nonzero]
    rfl
  · change MonoidAlgebra.single (Multiplicative.ofAdd inverseCharacter) a⁻¹ *
      MonoidAlgebra.single (Multiplicative.ofAdd m) a = 1
    rw [MonoidAlgebra.single_mul_single, mul_comm, characterProduct,
      inv_mul_cancel₀ nonzero]
    rfl

variable (regular : fan.IsRegular) (σ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "frames" => toricDiagonalCellFrames fan regular basis rays σ σ

/-- The specified affine top quotient sends each original top-cell unit
to a unit of the overlap ring in the actual boundary Cartier frame. -/
theorem toricDiagonalTopCellQuotient_isUnit (c : NormalizedCell A n) :
    @IsUnit (affineCoordinateRing fan.lattice (σ.val ⊓ σ.val)) _
      ((toricDualDiagonalBoundaryFrameIso fan regular basis rays σ σ).hom
      ((diagonalFramedDualTopQuotient ℂ A S S frames)
        ((diagonalFramedDualCoordinates ℂ A S S frames n).symm
          (Finsupp.single c (AddMonoidAlgebra.single 0 1))))) := by
  obtain ⟨w, a, weight, nonzero, value⟩ :=
    diagonalFramedDualTopQuotient_monomial_value ℂ A S S frames c 0
  change @IsUnit (affineCoordinateRing fan.lattice (σ.val ⊓ σ.val)) _
    (diagonalIntersectionCoefficientEquiv fan basis rays σ σ
    (dualDiagonalBoundaryFrameCoefficients fan regular basis rays σ σ
      (diagonalBoundaryFrameCharacter fan regular σ σ)
      (diagonalBoundaryFrameCharacter_ray fan regular σ σ)
      ((diagonalFramedDualTopQuotient ℂ A S S frames)
        ((diagonalFramedDualCoordinates ℂ A S S frames n).symm
          (Finsupp.single c (AddMonoidAlgebra.single 0 1))))))
  rw [value, dualDiagonalBoundaryFrameCoefficients_single,
    diagonalIntersectionCoefficientEquiv_single]
  apply coneAnnihilatingMonomial_isUnit fan basis rays (σ ⊓ σ) _ _ a nonzero
  intro ρ hρ
  change basis.equivFun.symm
    (w.val + basis.equivFun (diagonalBoundaryFrameCharacter fan regular σ σ))
      (fanRayPrimitiveGenerator fan ρ) = 0
  rw [weight]
  change basis.equivFun.symm
      (((basis.equivFun (coneDivisorCharacter fan regular
          (diagonalLeftCoefficients fan basis rays c) σ) + 0) +
        (basis.equivFun (coneDivisorCharacter fan regular
          (diagonalRightCoefficients fan basis rays c) σ) + 0)) +
        basis.equivFun (diagonalBoundaryFrameCharacter fan regular σ σ))
      (fanRayPrimitiveGenerator fan ρ) = 0
  simp only [add_zero, map_add, LinearEquiv.symm_apply_apply]
  exact diagonalTopCellBoundaryCharacter_ray fan regular basis rays σ c ρ
    (le_trans hρ inf_le_left)

end ToricPower

end
