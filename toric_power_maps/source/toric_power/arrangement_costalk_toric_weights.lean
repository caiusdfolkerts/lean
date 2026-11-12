module

public import ToricPower.ArrangementCostalkDuality
public import ToricPower.FanStrictCharacter
public import ToricPower.DiagonalSheafEntries

/-!
# The exact toric weight condition in a cellular costalk

For an actual fan cone, an integral character strictly positive on all
its primitive rays supplies the inward direction in the costalk argument.
Thus there is no unproved interior-direction hypothesis in this toric
specialization. The resulting condition is exactly
`m(vρ) + 1 + coeffρ(L(x)) ≥ 0` on the rays of the cone, including all
equality-wall cases. This file compares these literal integer weights;
the additional sheaf and diagram identifications remain separate maps.
-/

@[expose] public noncomputable section

open Set CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V} (fan : Fan latticeMap)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

/-- Only genuine rays of the selected cone impose monomial inequalities;
the added coordinate rows merely refine the CW decomposition. -/
def fanCostalkSelected (σ : fan.cones) : Set (Fin s ⊕ Fin n) :=
  Sum.inl '' {j | (rays j).toCone ≤ σ}

/-- The full integral character, evaluated on every actual primitive ray. -/
def fanCostalkWeight (m : N →+ ℤ) : Fin s ⊕ Fin n → ℤ :=
  Sum.elim (fun j => m (fanRayPrimitiveGenerator fan (rays j))) (fun _ => 0)

/-- Every actual cone supplies the strict direction required at walls.
No regularity, completeness, or positivity of a divisor is assumed. -/
theorem fanCostalk_strictDirection (σ : fan.cones) :
    ∃ v : Fin n → ℝ, ∀ i ∈ fanCostalkSelected fan rays σ,
      0 < augmentedForms A i v := by
  obtain ⟨m, positive⟩ := fanCone_exists_strictPositive_character fan σ
  refine ⟨latticeLift (basis.equivFun m), ?_⟩
  rintro i ⟨j, hj, rfl⟩
  rw [augmentedForms_latticeLift]
  change (0 : ℝ) < (rayPairing A (basis.equivFun m) j : ℝ)
  have value : rayPairing A (basis.equivFun m) j =
      m (fanRayPrimitiveGenerator fan (rays j)) := by
    simpa only [Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply] using
      fanArrangementMatrix_character fan basis rays (basis.equivFun m) (rays j)
  rw [value]
  exact_mod_cast positive (rays j) hj

/-- The literal shifted right-label monomial condition on a cone. -/
def fanCostalkWeightAllowed {d : ℕ} (c : NormalizedCell A d)
    (σ : fan.cones) (m : N →+ ℤ) : Prop :=
  ∀ ρ : fan.Ray, ρ.toCone ≤ σ →
    0 ≤ 1 + diagonalRightCoefficients fan basis rays c ρ +
      m (fanRayPrimitiveGenerator fan ρ)

/-- Nonemptiness of the actual costalk region is equivalent to the
literal shifted Cartier weight inequalities, with no missing boundary case. -/
theorem fanCostalkRegion_nonempty_iff {d : ℕ} (c : NormalizedCell A d)
    (σ : fan.cones) (m : N →+ ℤ) :
    (costalkRegion (augmentedForms A) (fanCostalkSelected fan rays σ)
      (fanCostalkWeight fan rays m) (cellCenter (augmentedForms A) c.val)).Nonempty ↔
      fanCostalkWeightAllowed fan basis rays c σ m := by
  rw [costalkRegion_nonempty_iff_integer _ _ _ _
    (fanCostalk_strictDirection fan basis rays σ)]
  constructor
  · intro allowed ρ contained
    have inequality := allowed (.inl (rays.symm ρ))
      ⟨rays.symm ρ, by simpa only [Set.mem_setOf_eq, Equiv.apply_symm_apply] using contained,
        rfl⟩
    have ceiling := ceil_eq_of_mem_cell (augmentedForms A) _ _
      (cellCenter_mem (augmentedForms A) c.val) (.inl (rays.symm ρ))
    rw [ceiling] at inequality
    simp only [fanCostalkWeight, Sum.elim_inl, Equiv.apply_symm_apply] at inequality
    change 0 ≤ 1 + -c.val.val.1 (.inl (rays.symm ρ)) +
      m (fanRayPrimitiveGenerator fan ρ)
    omega
  · intro allowed i member
    obtain ⟨j, contained, rfl⟩ := member
    have inequality := allowed (rays j) contained
    change 0 ≤ 1 + -c.val.val.1 (.inl (rays.symm (rays j))) +
      m (fanRayPrimitiveGenerator fan (rays j)) at inequality
    rw [Equiv.symm_apply_apply] at inequality
    rw [ceil_eq_of_mem_cell (augmentedForms A) _ _
      (cellCenter_mem (augmentedForms A) c.val) (.inl j)]
    change c.val.val.1 (.inl j) - 1 ≤ m (fanRayPrimitiveGenerator fan (rays j))
    omega

variable (𝕜 : Type) [Field 𝕜]

/-- The actual scalar cellular cochain complex attached to an arbitrary
integral character of an actual affine toric chart. -/
def fanCostalkCochainComplex {d : ℕ} (c : NormalizedCell A d)
    (σ : fan.cones) (m : N →+ ℤ) : CochainComplex (ModuleCat.{0} 𝕜) ℕ :=
  periodicCostalkCochainComplex A (fanCostalkSelected fan rays σ)
    (fanCostalkWeight fan rays m) (cellCenter (augmentedForms A) c.val) 𝕜

/-- Every permitted actual weight has precisely one top cohomology
coefficient, identified by the coherent ambient orientation. -/
def fanCostalkCochainHomologyIso {d : ℕ} (c : NormalizedCell A d)
    (σ : fan.cones) (m : N →+ ℤ)
    (allowed : fanCostalkWeightAllowed fan basis rays c σ m) :
    (fanCostalkCochainComplex fan basis rays 𝕜 c σ m).homology n ≅ ModuleCat.of 𝕜 𝕜 :=
  periodicCostalkCochainHomologyIso A _ _ _ 𝕜
    ((fanCostalkRegion_nonempty_iff fan basis rays c σ m).mpr allowed)

/-- Every forbidden actual weight has zero cohomology in every degree. -/
theorem fanCostalkCochainComplex_isZero_homology_of_not_allowed {d : ℕ}
    (c : NormalizedCell A d) (σ : fan.cones) (m : N →+ ℤ)
    (forbidden : ¬ fanCostalkWeightAllowed fan basis rays c σ m) (q : ℕ) :
    IsZero ((fanCostalkCochainComplex fan basis rays 𝕜 c σ m).homology q) := by
  apply periodicCostalkCochainComplex_isZero_homology_of_empty
  apply Set.not_nonempty_iff_eq_empty.mp
  exact fun h => forbidden ((fanCostalkRegion_nonempty_iff fan basis rays c σ m).mp h)

/-- For every integral weight, cohomology outside ambient degree is zero. -/
theorem fanCostalkCochainComplex_isZero_homology_off_top {d : ℕ}
    (c : NormalizedCell A d) (σ : fan.cones) (m : N →+ ℤ) (q : ℕ) (different : q ≠ n) :
    IsZero ((fanCostalkCochainComplex fan basis rays 𝕜 c σ m).homology q) := by
  by_cases allowed : fanCostalkWeightAllowed fan basis rays c σ m
  · exact periodicCostalkCochainComplex_isZero_homology A _ _ _ 𝕜
      ((fanCostalkRegion_nonempty_iff fan basis rays c σ m).mpr allowed) q different
  · exact fanCostalkCochainComplex_isZero_homology_of_not_allowed
      fan basis rays 𝕜 c σ m allowed q

end ToricPower
