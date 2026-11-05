module

public import VolumePolynomials.RationalHullSampling
public import Mathlib.Data.List.Sublists
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Tactic.GCongr
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false

/-!
# Finite rational grids for every bounded convex body

The enumerable objects are ordered sublists of a finite rational grid,
containing the origin. Every compact convex body in the prescribed box and
containing the origin has a listed convex hull at Hausdorff distance at most
`1/(k+1)`. The approximation theorem covers all dimensions and degenerate bodies.
-/

open Set Metric
open scoped BigOperators Pointwise

namespace VolumePolynomials.RationalHulls

def coordinateGrid (R k : ℕ) : List ℚ :=
  List.ofFn (fun i : Fin (2 * R * (k + 1) + 1) =>
    ((i.val : ℚ) - (R : ℚ) * (k + 1)) / (k + 1))

theorem zero_mem_coordinateGrid (R k : ℕ) : (0 : ℚ) ∈ coordinateGrid R k := by
  first
  | apply List.mem_ofFn.mpr
    refine ⟨⟨R * (k + 1),
      Nat.lt_succ_of_le (Nat.mul_le_mul_right (k + 1) (by omega))⟩, ?_⟩
    simp

theorem abs_le_of_mem_coordinateGrid {R k : ℕ} {q : ℚ}
    (hq : q ∈ coordinateGrid R k) : |q| ≤ (R : ℚ) := by
  first
  | obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    have hk : 0 < (k : ℚ) + 1 := by positivity
    have hi : (i.val : ℚ) ≤ 2 * (R : ℚ) * ((k : ℚ) + 1) := by
      exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have hi0 : 0 ≤ (i.val : ℚ) := by positivity
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ hk).mpr
      nlinarith
    · apply (div_le_iff₀ hk).mpr
      nlinarith

theorem exists_coordinateGrid_near {R k : ℕ} {x : ℝ}
    (hx : -(R : ℝ) ≤ x ∧ x ≤ (R : ℝ)) :
    ∃ q ∈ coordinateGrid R k, |x - (q : ℝ)| ≤ 1 / ((k : ℝ) + 1) := by
  first
  | let a : ℝ := ((k : ℝ) + 1) * (x + (R : ℝ))
    have ha : 0 ≤ a := mul_nonneg (by positivity) (by linarith)
    have hb : a ≤ (2 * R * (k + 1) : ℕ) := by
      dsimp [a]
      push_cast
      nlinarith
    let i : Fin (2 * R * (k + 1) + 1) :=
      ⟨⌊a⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hb)⟩
    let q : ℚ := ((i.val : ℚ) - (R : ℚ) * (k + 1)) / (k + 1)
    refine ⟨q, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hlo := Nat.floor_le ha
    have hhi := Nat.lt_floor_add_one a
    have hq : (q : ℝ) * ((k : ℝ) + 1) = (⌊a⌋₊ : ℝ) - (R : ℝ) * ((k : ℝ) + 1) := by
      dsimp [q, i]
      push_cast
      exact div_mul_cancel₀ _ hk.ne'
    have hnonneg : 0 ≤ x - (q : ℝ) := by
      apply (mul_nonneg_iff_of_pos_right hk).mp
      dsimp [a] at hlo
      nlinarith
    rw [abs_of_nonneg hnonneg]
    apply (le_div_iff₀ hk).mpr
    dsimp [a] at hhi
    nlinarith

def vertexGrid (d R k : ℕ) : List (RationalPoint d) :=
  selections (fun _ : Fin d => coordinateGrid R k)

theorem mem_vertexGrid {d R k : ℕ} (v : RationalPoint d) :
    v ∈ vertexGrid d R k ↔ ∀ i, v i ∈ coordinateGrid R k := mem_selections _ _

theorem zero_mem_vertexGrid (d R k : ℕ) : (0 : RationalPoint d) ∈ vertexGrid d R k :=
  Iff.mpr (mem_vertexGrid 0) (fun _ => zero_mem_coordinateGrid R k)

theorem vertexGrid_bounded {d R k : ℕ} {v : RationalPoint d}
    (hv : v ∈ vertexGrid d R k) (i : Fin d) : |v i| ≤ (R : ℚ) :=
  abs_le_of_mem_coordinateGrid (Iff.mp (mem_vertexGrid v) hv i)

theorem exists_vertexGrid_near {d R k : ℕ} {x : Space d}
    (hx : x ∈ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) :
    ∃ v ∈ vertexGrid d R k, dist x (realPoint v) ≤ 1 / ((k : ℝ) + 1) := by
  first
  | choose v hv hdist using fun i => exists_coordinateGrid_near (R := R) (k := k)
      (x := x i) ⟨hx.1 i, hx.2 i⟩
    refine ⟨v, Iff.mpr (mem_vertexGrid v) hv, ?_⟩
    exact (dist_pi_le_iff (by positivity)).mpr
      (fun i => by simpa only [Real.dist_eq, realPoint] using hdist i)

/-- All finite vertex-list candidates. Membership is an executable rational
list predicate, and every candidate is a nonempty actual body. -/
def candidates (d R k : ℕ) : List (List (RationalPoint d)) :=
  (vertexGrid d R k).sublists.filter (fun L => 0 ∈ L)

theorem mem_candidates {d R k : ℕ} (L : List (RationalPoint d)) :
    L ∈ candidates d R k ↔ L.Sublist (vertexGrid d R k) ∧ 0 ∈ L := by
  first
  | simp [candidates, List.mem_sublists]

theorem candidate_bounded {d R k : ℕ} (L : List (RationalPoint d))
    (hL : L ∈ candidates d R k) :
    (body L (Iff.mp (mem_candidates L) hL).2 : Set (Space d)) ⊆
      Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | apply body_subset_box L _ (R : ℚ)
    intro v hv i
    exact vertexGrid_bounded ((Iff.mp (mem_candidates L) hL).1.subset hv) i

/-- Quantitative completeness of the finite rational body enumeration. -/
theorem exists_candidate_near {d R k : ℕ} (K : Body d)
    (h0 : (0 : Space d) ∈ K)
    (hbox : (K : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) :
    ∃ L, ∃ hL : L ∈ candidates d R k,
      dist K (body L (Iff.mp (mem_candidates L) hL).2) ≤ 1 / ((k : ℝ) + 1) := by
  first
  | classical
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 ≤ ε := by positivity
    let P : RationalPoint d → Prop := fun v => ∃ x ∈ K, dist (realPoint v) x ≤ ε
    let L : List (RationalPoint d) := (vertexGrid d R k).filter (fun v => P v)
    have hL0 : (0 : RationalPoint d) ∈ L := by
      apply List.mem_filter.mpr
      refine ⟨zero_mem_vertexGrid d R k, ?_⟩
      simp only [decide_eq_true_eq]
      exact ⟨0, h0, by simpa only [realPoint_zero, dist_self] using hε⟩
    have hL : L ∈ candidates d R k :=
      Iff.mpr (mem_candidates L) ⟨List.filter_sublist, hL0⟩
    let Q := body L hL0
    have hQ : (Q : Set (Space d)) ⊆ (K : Set (Space d)) + closedBall 0 ε := by
      apply convexHull_min _ (K.convex.add (convex_closedBall _ _))
      rintro y ⟨v, hv, rfl⟩
      have hv' : v ∈ vertexGrid d R k ∧ P v := by
        simpa only [L, List.mem_filter, decide_eq_true_eq, Set.mem_setOf_eq] using hv
      obtain ⟨x, hx, hdist⟩ := hv'.2
      refine ⟨x, hx, realPoint v - x, ?_, by abel⟩
      simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hdist
    refine ⟨L, hL, ?_⟩
    change hausdorffDist (K : Set (Space d)) (Q : Set (Space d)) ≤ ε
    apply hausdorffDist_le_of_mem_dist hε
    · intro x hx
      obtain ⟨v, hv, hdist⟩ := exists_vertexGrid_near (hbox hx)
      have hvm : v ∈ L := by
        apply List.mem_filter.mpr
        refine ⟨hv, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨x, hx, by rwa [dist_comm]⟩
      exact ⟨realPoint v, subset_convexHull ℝ _ ⟨v, hvm, rfl⟩, hdist⟩
    · intro y hy
      obtain ⟨x, hx, z, hz, rfl⟩ := hQ hy
      refine ⟨x, hx, ?_⟩
      simpa only [mem_closedBall, dist_eq_norm, sub_zero, add_sub_cancel_left] using hz

/-- All candidate tuples, generated by the same finite-list product algorithm. -/
def candidateTuples (n d R k : ℕ) : List (Fin n → List (RationalPoint d)) :=
  selections (fun _ : Fin n => candidates d R k)

theorem mem_candidateTuples {n d R k : ℕ} (L : Fin n → List (RationalPoint d)) :
    L ∈ candidateTuples n d R k ↔ ∀ i, L i ∈ candidates d R k := mem_selections _ _

end VolumePolynomials.RationalHulls
