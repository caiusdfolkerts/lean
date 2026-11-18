module

public import ToricPower.ArrangementIncidenceCategory
public import ToricPower.DiagonalCellWeights

/-!
# Ceiling labels on genuine translated incidences

The two integer ceiling inequalities hold for every literal face
incidence, including equality walls. This combinatorial source is kept
independent of the later Cartier sheaf construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- Both ceiling labels decrease along every actual geometric face
incidence, not only along incidences with a nonzero boundary coefficient. -/
theorem incidence_ceiling_bounds {c d : IncidenceObject A} (f : c ⟶ d)
    (ρ : Fin s) :
    reflectedCeiling A c.2.val ρ - reflectedCeiling A d.2.val ρ ≤
        rayPairing A f.val ρ ∧
      c.2.val.val.1 (.inl ρ) - d.2.val.val.1 (.inl ρ) ≤
        -rayPairing A f.val ρ := by
  obtain ⟨x, hx⟩ := c.2.val.property.1
  have hxt : x + latticeLift f.val ∈
      cell (augmentedForms A) (translateCell A f.val c.2.val).val.1
        (translateCell A f.val c.2.val).val.2 :=
    (add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A f.val) x).mpr hx
  have hxd := f.property x (cell_subset_closedCell _ _ _ hx)
  have hleft : reflectedCeiling A (translateCell A f.val c.2.val) ρ ≤
      reflectedCeiling A d.2.val ρ := by
    rw [reflectedCeiling_eq_ceil A _ hxt]
    apply Int.ceil_le.mpr
    have hr := hxd (.inl ρ)
    change (if Sum.inl ρ ∈ d.2.val.val.2 then
      integralRowForm A ρ (x + latticeLift f.val) = (d.2.val.val.1 (.inl ρ) : ℝ)
      else (d.2.val.val.1 (.inl ρ) : ℝ)-1 ≤
        integralRowForm A ρ (x + latticeLift f.val) ∧
        integralRowForm A ρ (x + latticeLift f.val) ≤
          (d.2.val.val.1 (.inl ρ) : ℝ)) at hr
    unfold reflectedCeiling
    split_ifs with hρ
    · simp only [if_pos hρ] at hr
      simp only [Int.cast_neg]
      linarith
    · simp only [if_neg hρ] at hr
      simp only [Int.cast_sub, Int.cast_one]
      linarith [hr.1]
  have hright : (translateCell A f.val c.2.val).val.1 (.inl ρ) ≤
      d.2.val.val.1 (.inl ρ) := by
    have hceil := ceil_eq_of_mem_cell _ _ _ hxt (.inl ρ)
    have hb := (ceiling_bounds_of_mem_closedCell
      (augmentedForms A) _ _ hxd (.inl ρ)).2
    simpa only [ceilingVector, hceil] using hb
  rw [reflectedCeiling_translate] at hleft
  change c.2.val.val.1 (.inl ρ) + rayPairing A f.val ρ ≤
    d.2.val.val.1 (.inl ρ) at hright
  constructor <;> omega

end ToricPower.IntegralArrangement
