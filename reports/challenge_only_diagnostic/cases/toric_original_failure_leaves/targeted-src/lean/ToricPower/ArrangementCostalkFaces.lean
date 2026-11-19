module

public import ToricPower.ArrangementCostalkGeometry
public import ToricPower.ArrangementEquivariant

/-!
# Literal open stars along actual arrangement faces

The closed-cell relation and the open-star relation are equivalent in
opposite directions. Thus a genuine face incidence gives the actual
inclusion of open stars needed for costalk maps. Translation uses the
same integral forms and shifts the full weight, including wall cases.
-/

@[expose] public noncomputable section

open Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- The converse of the geometric open-star implication, with all
integral boundary cases retained. -/
theorem mem_localStar_of_point_mem_closedCell (f : ι → E →ₗ[ℝ] ℝ) {x y : E}
    (hxy : x ∈ closedCell f (ceilingVector f y) (integralIndices f y)) :
    y ∈ localStar f x := by
  intro i
  have h := hxy i
  have hb := ceiling_bounds_of_mem_closedCell f _ _ hxy i
  change ⌈f i y⌉ - 1 ≤ ⌈f i x⌉ ∧ ⌈f i x⌉ ≤ ⌈f i y⌉ at hb
  by_cases hy : f i y = (⌈f i y⌉ : ℝ)
  · have hy' : i ∈ integralIndices f y := hy
    simp only [if_pos hy', ceilingVector] at h
    have he : f i x = f i y := h.trans hy.symm
    simpa only [he] using mem_localStar_self f y i
  · have hy' : i ∉ integralIndices f y := hy
    simp only [if_neg hy', ceilingVector] at h
    have hyLower : (⌈f i y⌉ : ℝ) - 1 < f i y := by
      linarith [Int.ceil_lt_add_one (f i y)]
    have hyUpper : f i y < (⌈f i y⌉ : ℝ) :=
      lt_of_le_of_ne (Int.le_ceil _) hy
    by_cases he : ⌈f i x⌉ = ⌈f i y⌉
    · rw [he]
      constructor
      · exact hyLower
      · split_ifs <;> linarith
    · have he' : ⌈f i x⌉ = ⌈f i y⌉ - 1 := by omega
      have hx : f i x = (⌈f i x⌉ : ℝ) := by
        apply le_antisymm (Int.le_ceil _)
        rw [he', Int.cast_sub, Int.cast_one]
        exact h.1
      rw [if_pos hx, he']
      simp only [Int.cast_sub, Int.cast_one]
      constructor <;> linarith

/-- A point belongs to an open star exactly when the center belongs
to the point's actual closed arrangement cell. -/
theorem mem_localStar_iff_point_mem_closedCell (f : ι → E →ₗ[ℝ] ℝ) (x y : E) :
    y ∈ localStar f x ↔
      x ∈ closedCell f (ceilingVector f y) (integralIndices f y) :=
  ⟨localStar_point_mem_closedCell f x, mem_localStar_of_point_mem_closedCell f⟩

/-- Faces have larger open stars; this is an actual inclusion of the
literal open polyhedra. -/
theorem localStar_subset_of_point_mem_closedCell (f : ι → E →ₗ[ℝ] ℝ) {x y : E}
    (hxy : x ∈ closedCell f (ceilingVector f y) (integralIndices f y)) :
    localStar f y ⊆ localStar f x := by
  intro z hz
  apply mem_localStar_of_point_mem_closedCell f
  exact closedCell_of_point_subset f _ _
    (localStar_point_mem_closedCell f y hz) hxy

/-- Intersecting the open stars with a fixed actual monomial region
preserves the face-restriction inclusion. -/
theorem costalkRegion_subset_of_point_mem_closedCell (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) {x y : E}
    (hxy : x ∈ closedCell f (ceilingVector f y) (integralIndices f y)) :
    costalkRegion f selected weight y ⊆ costalkRegion f selected weight x :=
  Set.inter_subset_inter_left _ (localStar_subset_of_point_mem_closedCell f hxy)

/-- Literal translation by an integral-valued vector preserves the
open-star relation. -/
theorem add_mem_localStar_iff (f : ι → E →ₗ[ℝ] ℝ) (k : ι → ℤ) (z : E)
    (hz : ∀ i, f i z = (k i : ℝ)) (x y : E) :
    y + z ∈ localStar f (x + z) ↔ y ∈ localStar f x := by
  constructor <;> intro h i
  all_goals
    have hi := h i
    simp only [map_add, hz, Int.ceil_add_intCast, Int.cast_add,
      add_left_inj] at hi ⊢
    by_cases hx : f i x = (⌈f i x⌉ : ℝ)
    · simp only [if_pos hx] at hi ⊢
      constructor <;> linarith [hi.1, hi.2]
    · simp only [if_neg hx] at hi ⊢
      constructor <;> linarith [hi.1, hi.2]

/-- Translation shifts every selected character weight by its literal
integer pairing; the added coordinate rows impose no extra condition. -/
theorem add_mem_costalkRegion_iff (f : ι → E →ₗ[ℝ] ℝ) (selected : Set ι)
    (weight k : ι → ℤ) (z : E) (hz : ∀ i, f i z = (k i : ℝ)) (x y : E) :
    y + z ∈ costalkRegion f selected (weight + k) (x + z) ↔
      y ∈ costalkRegion f selected weight x := by
  apply and_congr (add_mem_localStar_iff f k z hz x y)
  constructor <;> intro h i hi
  all_goals
    have inequality := h i hi
    simp only [map_add, hz, Pi.add_apply, Int.cast_add] at inequality ⊢
    linarith

end ToricPower.IntegralArrangement
