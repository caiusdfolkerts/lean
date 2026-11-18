module

public import ToricPower.ArrangementLocalSupport

/-!
# Actual intersections in a local arrangement face star

A finite family of nonnegative affine functions on a convex set has a
point detecting every function that vanishes identically. Applied to
the two wall slacks in each coordinate, this identifies the intersection
of two incident closed arrangement cells with one actual closed cell.
Thus the finite local face star carries its genuine meet operation.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open Set

namespace ToricPower

section Midpoints

variable {E J : Type*} [AddCommGroup E] [Module ℝ E]

/-- Finitely many affine inequalities can all be made strict whenever
each can be made strict individually and all remain nonnegative. -/
theorem convex_finite_simultaneous_positive {S : Set E}
    (convex : Convex ℝ S) (nonempty : S.Nonempty) (g : J → E → ℝ)
    (nonnegative : ∀ j x, x ∈ S → 0 ≤ g j x)
    (midpoint : ∀ j x y,
      g j ((1/2 : ℝ) • x + (1/2 : ℝ) • y) = (g j x + g j y) / 2)
    (indices : Finset J) :
    ∃ p ∈ S, ∀ j ∈ indices, (∃ x ∈ S, 0 < g j x) → 0 < g j p := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    obtain ⟨p,hp⟩ := nonempty
    exact ⟨p,hp,by simp⟩
  | @insert j indices absent ih =>
    obtain ⟨p,hp,positive⟩ := ih
    by_cases possible_j : ∃ x ∈ S, 0 < g j x
    · obtain ⟨q,hq,hqj⟩ := possible_j
      refine ⟨(1/2 : ℝ) • p + (1/2 : ℝ) • q,
        convex hp hq (by norm_num) (by norm_num) (by norm_num), ?_⟩
      intro a member possible
      rw [midpoint]
      rcases Finset.mem_insert.mp member with rfl | old
      · have := nonnegative a p hp
        linarith
      · have := positive a old possible
        have := nonnegative a q hq
        linarith
    · refine ⟨p,hp,?_⟩
      intro a member possible
      rcases Finset.mem_insert.mp member with rfl | old
      · exact (possible_j possible).elim
      · exact positive a old possible

/-- The selected point detects all identically zero slacks at once. -/
theorem convex_exists_zero_detector [Finite J] {S : Set E}
    (convex : Convex ℝ S) (nonempty : S.Nonempty) (g : J → E → ℝ)
    (nonnegative : ∀ j x, x ∈ S → 0 ≤ g j x)
    (midpoint : ∀ j x y,
      g j ((1/2 : ℝ) • x + (1/2 : ℝ) • y) = (g j x + g j y) / 2) :
    ∃ p ∈ S, ∀ j, g j p = 0 → ∀ x ∈ S, g j x = 0 := by
  classical
  letI : Fintype J := Fintype.ofFinite _
  obtain ⟨p,hp,positive⟩ := convex_finite_simultaneous_positive convex nonempty
    g nonnegative midpoint Finset.univ
  refine ⟨p,hp,?_⟩
  intro j zero x hx
  by_contra nonzero
  have strict := positive j (Finset.mem_univ j)
    ⟨x,hx,lt_of_le_of_ne (nonnegative j x hx) (Ne.symm nonzero)⟩
  rw [zero] at strict
  exact lt_irrefl _ strict

end Midpoints

namespace IntegralArrangement

section ClosedCell

variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Finite J]
  (f : J → E →ₗ[ℝ] ℝ) (e : J → ℤ) (I : Set J)

theorem closedCell_form_bounds_generic {x : E} (hx : x ∈ closedCell f e I) (j : J) :
    (e j : ℝ)-1 ≤ f j x ∧ f j x ≤ (e j : ℝ) := by
  by_cases hj : j ∈ I
  · have eq : f j x = (e j : ℝ) := by simpa only [if_pos hj] using hx j
    rw [eq]
    constructor <;> linarith
  · simpa only [if_neg hj] using hx j

/-- Every convex subset of a closed arrangement cell has a point whose
actual closed cell contains the entire subset. -/
theorem convex_subset_closedCell_has_cell {S : Set E}
    (convex : Convex ℝ S) (nonempty : S.Nonempty) (contained : S ⊆ closedCell f e I) :
    ∃ p ∈ S, S ⊆ closedCell f (ceilingVector f p) (integralIndices f p) := by
  classical
  let g : J × Bool → E → ℝ := fun j x =>
    if j.2 then (e j.1 : ℝ) - f j.1 x else f j.1 x - ((e j.1 : ℝ)-1)
  have nonnegative : ∀ j x, x ∈ S → 0 ≤ g j x := by
    intro j x hx
    have bounds := closedCell_form_bounds_generic f e I (contained hx) j.1
    rcases j with ⟨j,b⟩
    cases b <;> dsimp [g] <;> linarith
  have midpoint : ∀ j x y,
      g j ((1/2 : ℝ) • x + (1/2 : ℝ) • y) = (g j x + g j y) / 2 := by
    rintro ⟨j,b⟩ x y
    cases b <;> simp only [g, Bool.false_eq_true, if_false, if_true,
      map_add, map_smul, smul_eq_mul] <;> ring
  obtain ⟨p,hp,detects⟩ := convex_exists_zero_detector convex nonempty g nonnegative midpoint
  refine ⟨p,hp,?_⟩
  intro x hx j
  have bp := closedCell_form_bounds_generic f e I (contained hp) j
  have bx := closedCell_form_bounds_generic f e I (contained hx) j
  by_cases integral : j ∈ integralIndices f p
  · simp only [if_pos integral, ceilingVector]
    have eqp : f j p = (⌈f j p⌉ : ℝ) := integral
    have bounds := ceiling_bounds_of_mem_closedCell f e I (contained hp) j
    change e j - 1 ≤ ⌈f j p⌉ ∧ ⌈f j p⌉ ≤ e j at bounds
    have either : ⌈f j p⌉ = e j ∨ ⌈f j p⌉ = e j-1 := by omega
    rcases either with upper | lower
    · have zero : g (j,true) p = 0 := by dsimp [g]; rw [eqp,upper]; ring
      have all := detects (j,true) zero x hx
      dsimp [g] at all
      rw [upper]
      linarith
    · have zero : g (j,false) p = 0 := by
        dsimp [g]
        rw [eqp,lower,Int.cast_sub,Int.cast_one]
        ring
      have all := detects (j,false) zero x hx
      dsimp [g] at all
      rw [lower,Int.cast_sub,Int.cast_one]
      linarith
  · simp only [if_neg integral, ceilingVector]
    have above : (e j : ℝ)-1 < f j p := by
      apply lt_of_le_of_ne bp.1
      intro eq
      apply integral
      change f j p = (⌈f j p⌉ : ℝ)
      have eq' : f j p = ((e j-1 : ℤ) : ℝ) := by
        simpa only [Int.cast_sub,Int.cast_one] using eq.symm
      rw [eq',Int.ceil_intCast]
    have ceiling : ⌈f j p⌉ = e j := Int.ceil_eq_iff.mpr ⟨above,bp.2⟩
    rw [ceiling]
    exact bx

end ClosedCell

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A

/-- The actual cell containing an actual ambient point. -/
def universalIncidenceOfPoint (x : Fin n → ℝ) : U :=
  ⟨Module.finrank ℝ (cellDirection (augmentedForms A) (integralIndices (augmentedForms A) x)),
    ⟨(ceilingVector (augmentedForms A) x,integralIndices (augmentedForms A) x),
      ⟨x,mem_cell_self _ x⟩,rfl⟩⟩

/-- Any two cofaces of a fixed face have an actual closed-cell
intersection, including all forced additional active equalities. -/
theorem exists_universalIncidence_intersection (c : U) (d e : UniversalFaceStar A c) :
    ∃ z : UniversalFaceStar A c,
      universalIncidenceClosedCell A z.val =
        universalIncidenceClosedCell A d.val ∩ universalIncidenceClosedCell A e.val := by
  let S := universalIncidenceClosedCell A d.val ∩ universalIncidenceClosedCell A e.val
  have nonempty : S.Nonempty := by
    let x := cellCenter (augmentedForms A) c.2
    have hx := cell_subset_closedCell _ _ _ (cellCenter_mem (augmentedForms A) c.2)
    exact ⟨x,d.property hx,e.property hx⟩
  have convex : Convex ℝ S :=
    (closedCell_convex _ _ _).inter (closedCell_convex _ _ _)
  obtain ⟨p,hp,inside⟩ := convex_subset_closedCell_has_cell (augmentedForms A)
    d.val.2.val.1 d.val.2.val.2 convex nonempty inter_subset_left
  have whole : universalIncidenceClosedCell A (universalIncidenceOfPoint A p) = S := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨closedCell_of_point_subset _ _ _ hp.1 hx,
        closedCell_of_point_subset _ _ _ hp.2 hx⟩
    · exact inside
  refine ⟨⟨universalIncidenceOfPoint A p,?_⟩,whole⟩
  change universalIncidenceClosedCell A c ⊆
    universalIncidenceClosedCell A (universalIncidenceOfPoint A p)
  rw [whole]
  exact subset_inter d.property e.property

instance universalFaceStar_partialOrder (c : U) : PartialOrder (UniversalFaceStar A c) where
  __ := universalFaceStar_preorder A c
  le_antisymm _ _ h h' := Subtype.ext (universalIncidence_antisymm A h h')

/-- The meet is the proved literal polyhedral intersection. -/
def universalFaceStarInf (c : U) (d e : UniversalFaceStar A c) : UniversalFaceStar A c :=
  (exists_universalIncidence_intersection A c d e).choose

theorem universalFaceStarInf_closedCell (c : U) (d e : UniversalFaceStar A c) :
    universalIncidenceClosedCell A (universalFaceStarInf A c d e).val =
      universalIncidenceClosedCell A d.val ∩ universalIncidenceClosedCell A e.val :=
  (exists_universalIncidence_intersection A c d e).choose_spec

instance universalFaceStar_semilatticeInf (c : U) : SemilatticeInf (UniversalFaceStar A c) where
  __ := universalFaceStar_partialOrder A c
  inf := universalFaceStarInf A c
  inf_le_left d e := by
    change universalIncidenceClosedCell A _ ⊆ universalIncidenceClosedCell A d.val
    rw [universalFaceStarInf_closedCell]
    exact inter_subset_left
  inf_le_right d e := by
    change universalIncidenceClosedCell A _ ⊆ universalIncidenceClosedCell A e.val
    rw [universalFaceStarInf_closedCell]
    exact inter_subset_right
  le_inf d e f de df := by
    change universalIncidenceClosedCell A d.val ⊆ universalIncidenceClosedCell A _
    rw [universalFaceStarInf_closedCell]
    exact subset_inter de df

end IntegralArrangement

end ToricPower

end
