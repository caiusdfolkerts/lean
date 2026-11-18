module

public import ToricPower.ArrangementMinimalCoface
public import ToricPower.ArrangementCostalkToricWeights
public import ToricPower.DiagonalToricFrames
public import ToricPower.DiagonalTopCellLabels

/-!
# The actual minimal character and top coface on a smooth toric chart

The regular cone's integral Cartier character attains every costalk
lower bound simultaneously. A genuine supported top cell then makes
the inverse-right incidence coefficient a unit on this chart.
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
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ

def arrangementMinimalCharacter (c : IncidenceObject A) : Fin n → ℤ :=
  basis.equivFun (coneDivisorCharacter fan regular
    (fun ρ => -diagonalRightCoefficients fan basis rays c.2 ρ - 1) σ)

theorem arrangementMinimalCharacter_ray (c : IncidenceObject A)
    (j : Fin s) (hj : j ∈ S) :
    rayPairing A (arrangementMinimalCharacter fan regular basis rays σ c) j =
      c.2.val.val.1 (.inl j) - 1 := by
  have value := fanArrangementMatrix_character fan basis rays
    (arrangementMinimalCharacter fan regular basis rays σ c) (rays j)
  simp only [Equiv.symm_apply_apply, arrangementMinimalCharacter,
    LinearEquiv.symm_apply_apply] at value
  unfold arrangementMinimalCharacter
  rw [value, coneDivisorCharacter_globalRay fan regular _ σ (rays j) hj]
  simp only [diagonalRightCoefficients, Equiv.symm_apply_apply, neg_neg]

theorem arrangementMinimalCharacter_strictDirection :
    ∃ v : Fin n → ℝ, ∀ j ∈ Sum.inl '' S, 0 < augmentedForms A j v := by
  simpa only [fanCostalkSelected, fanConeRaySet] using
    fanCostalk_strictDirection fan basis rays σ

/-- A genuine normalized top coface with its literal incidence vector. -/
def arrangementMinimalTopCoface (c : IncidenceObject A) :
    RepresentableCostalkIndex A c S
      (arrangementMinimalCharacter fan regular basis rays σ c) n :=
  representedMinimalTopCoface A S c
    (arrangementMinimalCharacter_strictDirection fan basis rays σ)
    (arrangementMinimalCharacter fan regular basis rays σ c)
    (arrangementMinimalCharacter_ray fan regular basis rays σ c)

/-- The actual inverse-right coefficient has no vanishing or pole
along any chart ray. All equality-wall cases are retained. -/
theorem arrangementMinimalTopCoface_ceiling (c : IncidenceObject A)
    (j : Fin s) (hj : j ∈ S) :
    let p := arrangementMinimalTopCoface fan regular basis rays σ c
    p.val.1.val.val.1 (.inl j) =
      c.2.val.val.1 (.inl j) + rayPairing A p.val.2.val j := by
  let p := arrangementMinimalTopCoface fan regular basis rays σ c
  have lower := (incidence_ceiling_bounds A p.val.2 j).2
  have upper := p.property j hj
  have notWall : Sum.inl j ∉ p.val.1.val.val.2 := by
    simpa only [Equiv.symm_apply_apply] using
      diagonalTopCell_ray_not_wall fan basis rays p.val.1 (rays j)
  rw [rayPairing_add, arrangementMinimalCharacter_ray fan regular basis rays σ c j hj,
    reflectedCeiling, if_neg notWall] at upper
  change p.val.1.val.val.1 (.inl j) =
    c.2.val.val.1 (.inl j) + rayPairing A p.val.2.val j
  change c.2.val.val.1 (.inl j) - p.val.1.val.val.1 (.inl j) ≤
    -rayPairing A p.val.2.val j at lower
  omega

end ToricPower

end

