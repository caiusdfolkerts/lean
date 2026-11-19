module

public import ToricPower.CellularIncidenceSupport
public import ToricPower.CellularIncidenceNaturality
public import ToricPower.DiagonalCellWeights

/-!
# Actual incidence support and the global line-bundle inequalities

A nonzero cellular incidence forces a point of the target cell into the
closed source cell: otherwise its attaching map misses that point and the
actual local-degree coefficient vanishes.  Both ceiling labels decrease
along such a face.  After normalizing the target cell by an integer
translation, these inequalities say exactly that the character pair
`(a,-a)` defines a regular morphism between the two diagonal line-bundle
labels on every toric chart.

This proves the regularity condition for global matrix entries from the
actual cellular incidence, rather than postulating a matrix support rule.

Candidate until the pinned compiler checks its full dependency closure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set Metric
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local instance arrangementIncidenceLabelsPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

variable (k : Type) [Ring k]

/-- The attaching map of an actual periodic arrangement cell lands in
its literal closed polyhedron. -/
theorem periodicAttachingMap_mem_closedCell {d : ℕ}
    (j : Cell (augmentedForms A) d) (z : TopCat.diskBoundary d) :
    ((TauCeti.cellAttachingMap (arrangementCarrier A) j z :
      TauCeti.skeletonObj (arrangementCarrier A) d) : Fin n → ℝ) ∈
      closedCell (augmentedForms A) j.val.1 j.val.2 := by
  let zd : TopCat.disk d := TopCat.diskBoundaryInclusion d z
  have hmem :
      ((TauCeti.cellAttachingMap (arrangementCarrier A) j z :
        TauCeti.skeletonObj (arrangementCarrier A) d) : Fin n → ℝ) ∈
      Topology.RelCWComplex.closedCell (C := arrangementCarrier A) d j := by
    erw [TauCeti.coe_cellAttachingMap_apply]
    exact ⟨_, ((EuclideanSpace.equiv (Fin d) ℝ).image_unitBallHomeomorph_closedBall ▸
      Set.mem_image_of_mem _ zd.down.2), rfl⟩
  change _ ∈ periodicCellMap A j '' Metric.closedBall 0 1 at hmem
  rwa [periodicCellMap_image_closedBall] at hmem

/-- A nonzero actual incidence forces every point in the open target
cell into the literal closed source cell. -/
theorem point_mem_closedCell_of_incidence_ne_zero {d : ℕ}
    (i : Cell (augmentedForms A) d) (j : Cell (augmentedForms A) (d+1))
    (hij : TauCeti.cellularIncidence (arrangementCarrier A) k d i j ≠ 0)
    {x : Fin n → ℝ} (hx : x ∈ cell (augmentedForms A) i.val.1 i.val.2) :
    x ∈ closedCell (augmentedForms A) j.val.1 j.val.2 := by
  have hxopen : x ∈ Topology.RelCWComplex.openCell (C := arrangementCarrier A) d i := by
    change x ∈ periodicCellMap A i '' Metric.ball 0 1
    rwa [periodicCellMap_image_ball]
  have hxsk : x ∈ (skeletonLT (arrangementCarrier A) (d+1) : Set (Fin n → ℝ)) :=
    CWComplex.mem_skeletonLT_iff.mpr
      ⟨d, by exact_mod_cast Nat.lt_succ_self d, i, hxopen⟩
  let xs : TauCeti.skeletonObj (arrangementCarrier A) (d+1) := ⟨x,hxsk⟩
  by_contra hnot
  apply hij
  apply cellularIncidence_eq_zero_of_attaching_misses
    (arrangementCarrier A) k xs hxopen j
  intro z hz
  have hc := periodicAttachingMap_mem_closedCell A j z
  have he :
      ((TauCeti.cellAttachingMap (arrangementCarrier A) j z :
        TauCeti.skeletonObj (arrangementCarrier A) (d+1)) : Fin n → ℝ) = x :=
    congrArg Subtype.val hz
  exact hnot (he ▸ hc)

/-- Both of the actual diagonal ceiling labels decrease along every
nonzero incidence.  Equality-wall cases use their correct reflected
ceiling and are not silently rounded as open cells. -/
theorem ceiling_labels_le_of_incidence_ne_zero {d : ℕ}
    (i : Cell (augmentedForms A) d) (j : Cell (augmentedForms A) (d+1))
    (hij : TauCeti.cellularIncidence (arrangementCarrier A) k d i j ≠ 0)
    (ρ : Fin s) :
    reflectedCeiling A i ρ ≤ reflectedCeiling A j ρ ∧
      i.val.1 (.inl ρ) ≤ j.val.1 (.inl ρ) := by
  obtain ⟨x,hx⟩ := i.property.1
  have hy := point_mem_closedCell_of_incidence_ne_zero A k i j hij hx
  constructor
  · rw [reflectedCeiling_eq_ceil A i hx ρ]
    apply Int.ceil_le.mpr
    have h := hy (.inl ρ)
    change (if Sum.inl ρ ∈ j.val.2 then
      integralRowForm A ρ x = (j.val.1 (.inl ρ) : ℝ)
      else (j.val.1 (.inl ρ) : ℝ)-1 ≤ integralRowForm A ρ x ∧
        integralRowForm A ρ x ≤ (j.val.1 (.inl ρ) : ℝ)) at h
    unfold reflectedCeiling
    split_ifs with hρ
    · simp only [if_pos hρ] at h
      simp only [Int.cast_neg]
      linarith
    · simp only [if_neg hρ] at h
      simp only [Int.cast_sub, Int.cast_one]
      linarith [h.1]
  · have hceil := ceil_eq_of_mem_cell (augmentedForms A) i.val.1 i.val.2 hx (.inl ρ)
    have hbounds := ceiling_bounds_of_mem_closedCell
      (augmentedForms A) j.val.1 j.val.2 hy (.inl ρ)
    have hupper := hbounds.2
    change ⌈augmentedForms A (.inl ρ) x⌉ ≤ j.val.1 (.inl ρ) at hupper
    simpa only [hceil] using hupper

/-- The character pair `(a,-a)` of a global boundary entry satisfies
the regularity inequalities for the two actual line-bundle factors,
simultaneously at every ray. -/
theorem normalized_incidence_character_regular {d : ℕ}
    (i : NormalizedCell A d) (j : NormalizedCell A (d+1))
    (a : Fin n → ℤ)
    (hij : TauCeti.cellularIncidence (arrangementCarrier A) k d
      (translateCell A a i.val) j.val ≠ 0) (ρ : Fin s) :
    reflectedCeiling A i.val ρ - reflectedCeiling A j.val ρ ≤ rayPairing A a ρ ∧
      i.val.val.1 (.inl ρ) - j.val.val.1 (.inl ρ) ≤ -rayPairing A a ρ := by
  have h := ceiling_labels_le_of_incidence_ne_zero A k
    (translateCell A a i.val) j.val hij ρ
  rw [reflectedCeiling_translate] at h
  have hright : i.val.val.1 (.inl ρ) + rayPairing A a ρ ≤ j.val.val.1 (.inl ρ) := h.2
  constructor <;> omega

end ToricPower.IntegralArrangement
