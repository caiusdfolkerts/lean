module

public import ToricPower.ArrangementHalfStar

/-! # Strict integral half-spaces and their actual arrangement cells

A strict inequality at an integer level is constant on every open cell.
Its complementary cells form a downward-closed family whose closed
polyhedra cover precisely the geometric complement. These are the cells
used in the open/closed coefficient sequence for the local Morse test.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace ToricPower.IntegralArrangement

section General

variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Finite J]
  (f : J → E →ₗ[ℝ] ℝ) (lower : J → ℤ) (selected : Set J)

def strictCellRegion : Set E :=
  {x | ∀ j ∈ selected, (lower j : ℝ) < f j x}

def cellStrictSupport (e : J → ℤ) : Prop :=
  ∀ j ∈ selected, lower j < e j

/-- The support test uses the literal integer ceiling label. -/
theorem mem_strictCellRegion_iff_of_mem_cell
    (e : J → ℤ) (I : Set J) {x : E} (hx : x ∈ cell f e I) :
    x ∈ strictCellRegion f lower selected ↔ cellStrictSupport lower selected e := by
  constructor
  · intro h j hj
    have inequality := Int.lt_ceil.mpr (h j hj)
    rwa [ceil_eq_of_mem_cell f e I hx j] at inequality
  · intro h j hj
    apply Int.lt_ceil.mp
    rw [ceil_eq_of_mem_cell f e I hx j]
    exact h j hj

/-- Every closed cell in the complementary family is wholly outside
the strict region, including all of its boundary points. -/
theorem closedCell_disjoint_strictCellRegion
    (e : J → ℤ) (I : Set J) (absent : ¬ cellStrictSupport lower selected e) :
    Disjoint (closedCell f e I) (strictCellRegion f lower selected) := by
  classical
  simp only [cellStrictSupport] at absent
  push_neg at absent
  obtain ⟨j,hj,bound⟩ := absent
  apply Set.disjoint_left.mpr
  intro x hx strict
  have upper := (closedCell_form_bounds_generic f e I hx j).2
  have boundReal : (e j : ℝ) ≤ (lower j : ℝ) := by exact_mod_cast bound
  exact (not_lt_of_ge (upper.trans boundReal)) (strict j hj)

/-- The closure of a supported cell satisfies all weak inequalities.
The integral gap in its ceiling label is essential here. -/
theorem strictSupport_closedCell_weak
    (e : J → ℤ) (I : Set J) (supported : cellStrictSupport lower selected e)
    {x : E} (hx : x ∈ closedCell f e I) :
    ∀ j ∈ selected, (lower j : ℝ) ≤ f j x := by
  intro j hj
  have integral : lower j ≤ e j - 1 := by
    have := supported j hj
    omega
  have real : (lower j : ℝ) ≤ (e j : ℝ)-1 := by exact_mod_cast integral
  exact real.trans (closedCell_form_bounds_generic f e I hx j).1

end General

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A
local notation "E" => Fin n → ℝ
local notation "J" => Fin s ⊕ Fin n

variable (lower : (Fin s ⊕ Fin n) → ℤ) (selected : Set (Fin s ⊕ Fin n))

def universalStrictSupport (c : U) : Prop :=
  cellStrictSupport lower selected c.2.val.1

theorem universalIncidence_ceiling_le {c d : U} (below : c ≤ d) (j : J) :
    c.2.val.1 j ≤ d.2.val.1 j := by
  obtain ⟨x,hx⟩ := c.2.property.1
  have bound := (ceiling_bounds_of_mem_closedCell (augmentedForms A)
    d.2.val.1 d.2.val.2 (below (cell_subset_closedCell _ _ _ hx)) j).2
  change ⌈augmentedForms A j x⌉ ≤ d.2.val.1 j at bound
  rwa [ceil_eq_of_mem_cell (augmentedForms A) c.2.val.1 c.2.val.2 hx j] at bound

/-- Open support is upward closed for every actual face incidence. -/
theorem universalStrictSupport_upward : Monotone (universalStrictSupport A lower selected) := by
  intro c d below h j hj
  exact (h j hj).trans_le (universalIncidence_ceiling_le A below j)

/-- A point outside the weak support excludes every coface of its
actual arrangement cell, not merely the central cell. -/
theorem universalStrictSupport_absent_above
    (c : U)
    (outside : ¬ ∀ j ∈ selected, (lower j : ℝ) ≤
      augmentedForms A j (cellCenter (augmentedForms A) c.2))
    {d : U} (above : c ≤ d) :
    ¬ universalStrictSupport A lower selected d := by
  intro supported
  apply outside
  exact strictSupport_closedCell_weak (augmentedForms A) lower selected
    d.2.val.1 d.2.val.2 supported
    (above (cell_subset_closedCell _ _ _ (cellCenter_mem (augmentedForms A) c.2)))

def universalStrictClosedPredicate (c : U) : Prop :=
  ¬ universalStrictSupport A lower selected c

theorem universalStrictClosedPredicate_downward :
    Antitone (universalStrictClosedPredicate A lower selected) := by
  intro c d below hd hc
  exact hd (universalStrictSupport_upward A lower selected below hc)

def faceStarStrictClosedPredicate (c : U) (d : UniversalFaceStar A c) : Prop :=
  universalStrictClosedPredicate A lower selected d.val

theorem faceStarStrictClosedPredicate_downward (c : U) :
    Antitone (faceStarStrictClosedPredicate A lower selected c) :=
  fun _ _ below => universalStrictClosedPredicate_downward A lower selected below

/-- The true closed complementary face family covers exactly the
complement in the chosen local cut; cells merely touching the complement
are not added to this family. -/
theorem faceStarStrictClosedPatch_cover (c : U) (region : Set E)
    (inside : region ⊆ localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) :
    (⋃ d : {d : UniversalFaceStar A c // faceStarStrictClosedPredicate A lower selected c d},
      universalFaceStarPatch A c region d.val) =
        region ∩ (strictCellRegion (augmentedForms A) lower selected)ᶜ := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨d,hcell,hregion⟩ := mem_iUnion.mp hx
    refine ⟨hregion,?_⟩
    exact Set.disjoint_left.mp (closedCell_disjoint_strictCellRegion
      (augmentedForms A) lower selected d.val.val.2.val.1 d.val.val.2.val.2 d.property) hcell
  · rintro x ⟨hregion,outside⟩
    let d : UniversalFaceStar A c :=
      ⟨universalIncidenceOfPoint A x,universalIncidenceOfPoint_mem_faceStar A c (inside hregion)⟩
    have hd : faceStarStrictClosedPredicate A lower selected c d := by
      intro supported
      exact outside ((mem_strictCellRegion_iff_of_mem_cell
        (augmentedForms A) lower selected _ _ (mem_cell_self _ x)).mpr supported)
    exact mem_iUnion.mpr ⟨⟨d,hd⟩,cell_subset_closedCell _ _ _ (mem_cell_self _ x),hregion⟩

end ToricPower.IntegralArrangement

end
