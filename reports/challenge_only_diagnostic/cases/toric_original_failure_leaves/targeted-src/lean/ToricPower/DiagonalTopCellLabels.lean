module

public import ToricPower.DiagonalGlobalAugmentation
public import ToricPower.FanStrictCharacter

/-!
# The literal boundary label on a top-dimensional diagonal cell

An ambient-dimensional arrangement cell lies on no primitive-ray wall:
its direction space is the whole real character space, whereas every
primitive-ray functional is nonzero. The two original Cartier coefficients
therefore sum to minus one on every ray. Their inverse tensor label is
exactly the boundary divisor, including for fans with torus factors.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

/-- No nonzero primitive-ray form can be constant on a cell of full
ambient dimension. This assertion concerns the actual geometric wall set. -/
theorem diagonalTopCell_ray_not_wall (c : NormalizedCell A n) (ρ : fan.Ray) :
    Sum.inl (rays.symm ρ) ∉ c.val.val.2 := by
  intro wall
  have direction : cellDirection (augmentedForms A) c.val.val.2 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using
      c.val.property.2
  obtain ⟨m, positive⟩ := fanCone_exists_strictPositive_character fan ρ.toCone
  have contained : latticeLift (basis.equivFun m) ∈
      cellDirection (augmentedForms A) c.val.val.2 := by
    rw [direction]
    trivial
  have zero := (mem_cellDirection (augmentedForms A) c.val.val.2 _).mp contained
    (.inl (rays.symm ρ)) wall
  rw [augmentedForms_latticeLift] at zero
  change (rayPairing A (basis.equivFun m) (rays.symm ρ) : ℝ) = 0 at zero
  rw [fanArrangementMatrix_character, LinearEquiv.symm_apply_apply] at zero
  have zeroInt : m (fanRayPrimitiveGenerator fan ρ) = 0 := by exact_mod_cast zero
  exact (ne_of_gt (positive ρ le_rfl)) zeroInt

/-- The sum of the original two Cartier labels on every top cell is
literally minus the full toric boundary divisor. -/
theorem diagonalCoefficient_sum_top (c : NormalizedCell A n) :
    diagonalLeftCoefficients fan basis rays c +
      diagonalRightCoefficients fan basis rays c = fun _ => -1 := by
  funext ρ
  change diagonalLeftCoefficients fan basis rays c ρ +
    diagonalRightCoefficients fan basis rays c ρ = -1
  rw [diagonalCoefficient_sum, if_neg (diagonalTopCell_ray_not_wall fan basis rays c ρ)]

/-- The dual exterior-product label restricts to the actual coefficient
one boundary label on every ray. -/
theorem diagonalInverseCoefficient_sum_top (c : NormalizedCell A n) :
    -diagonalLeftCoefficients fan basis rays c +
      -diagonalRightCoefficients fan basis rays c = fun _ => 1 := by
  funext ρ
  have sum := congrFun (diagonalCoefficient_sum_top fan basis rays c) ρ
  simp only [Pi.add_apply, Pi.neg_apply] at sum ⊢
  omega

end ToricPower
