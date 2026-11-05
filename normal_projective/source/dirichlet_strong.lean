module

public import dirichlet
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Logic.Relation

/-!
# Strong maximum principles and rising paths

This is part of the genuine finite-graph input to the planar embedding proof.
The graph, boundary, weights, harmonic equations, and paths below are the actual
objects, rather than hypotheses asserting the eventual planar conclusion.
This file is a new candidate until its ordinary pinned Lean check succeeds.
-/

@[expose] public section

namespace NormalProjective.Dirichlet

open Finset Relation

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem harmonic_const (w : V → V → ℝ) (c : ℝ) (i : V) :
    Harmonic w (fun _ => c) i := by simp [Harmonic]

theorem harmonic_neg {w : V → V → ℝ} {x : V → ℝ} {i : V}
    (hx : Harmonic w x i) : Harmonic w (fun j => -x j) i := by
  unfold Harmonic at hx ⊢
  simp only [show ∀ j, -x i - -x j = -(x i - x j) by intro j; ring,
    mul_neg, sum_neg_distrib, hx, neg_zero]

theorem harmonic_affine {w : V → V → ℝ} {x y : V → ℝ} {i : V}
    (hx : Harmonic w x i) (hy : Harmonic w y i) (a b c : ℝ) :
    Harmonic w (fun j => a * x j + b * y j + c) i := by
  unfold Harmonic at hx hy ⊢
  have heq : ∀ j, w i j * ((a * x i + b * y i + c) -
      (a * x j + b * y j + c)) =
      a * (w i j * (x i - x j)) + b * (w i j * (y i - y j)) := by
    intro j
    ring
  simp_rw [heq, sum_add_distrib, ← mul_sum, hx, hy]
  ring

/-- A minimum at a harmonic vertex propagates across every positive-weight
edge. This statement also applies to a minimum on a chosen subdomain, once its
boundary values have been bounded by the weak principle. -/
theorem neighbor_eq_of_minimum (G : SimpleGraph V) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (x : V → ℝ) (c : ℝ) (hmin : ∀ i, c ≤ x i)
    {i j : V} (hi : Harmonic w x i) (hic : x i = c) (hij : G.Adj i j) :
    x j = c := by
  have hnonpos : ∀ k ∈ (univ : Finset V), w i k * (x i - x k) ≤ 0 := by
    intro k _
    exact mul_nonpos_of_nonneg_of_nonpos (hw i k)
      (sub_nonpos.mpr (hic ▸ hmin k))
  have hz : w i j * (x i - x j) = 0 :=
    (sum_eq_zero_iff_of_nonpos hnonpos).mp hi j (mem_univ j)
  have hix : x i = x j := sub_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (he i j hij)))
  exact hix.symm.trans hic

/-- Strict positivity at one accessible boundary vertex gives strict positivity
at an interior vertex. Accessibility is an actual walk after deleting the other
boundary vertices; it will be supplied by the geometric triangulation. -/
theorem strict_minimum_of_accessible (G : SimpleGraph V) (hG : G.Connected)
    (B : Set V) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (x : V → ℝ) (hx : ∀ i, i ∉ B → Harmonic w x i)
    (c : ℝ) (hb : ∀ i ∈ B, c ≤ x i)
    (b : V) (hbB : b ∈ B) (hbc : c < x b)
    (i : V) (hiB : i ∉ B)
    (hpath : (G.induce {v | v ∉ B ∨ v = b}).Reachable
      ⟨i, Or.inl hiB⟩ ⟨b, Or.inr rfl⟩) : c < x i := by
  have hmin := minimum_principle G hG B ⟨b,hbB⟩ w hw he x hx c hb
  by_contra hstrict
  have hic : x i = c := le_antisymm (le_of_not_gt hstrict) (hmin i)
  have hstep : ∀ (v z : {v // v ∉ B ∨ v = b}),
      (G.induce {v | v ∉ B ∨ v = b}).Adj v z → x v = c → x z = c := by
    intro v z hvz hvc
    have hvB : (v : V) ∉ B := by
      rcases v.property with hv | hv
      · exact hv
      · have hxb : x b = c := by simpa only [hv] using hvc
        exact False.elim (hbc.ne' hxb)
    exact neighbor_eq_of_minimum G w hw he x c hmin (hx v hvB) hvc hvz
  obtain ⟨p⟩ := hpath
  have hwalk : ∀ {v z : {v // v ∉ B ∨ v = b}},
      (G.induce {v | v ∉ B ∨ v = b}).Walk v z → x v = c → x z = c := by
    intro v z p
    induction p with
    | nil => exact id
    | @cons v z t hvz p ih => exact fun hv => ih (hstep v z hvz hv)
  exact hbc.ne' (hwalk p hic)

/-- If a harmonic vertex has a lower neighbour, it has a higher neighbour.
The zero-off-edges condition is stated explicitly. -/
theorem exists_higher_neighbor (G : SimpleGraph V) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ G.Adj i j → w i j = 0)
    (x : V → ℝ) {i j : V} (hi : Harmonic w x i)
    (hij : G.Adj i j) (hji : x j < x i) :
    ∃ k, G.Adj i k ∧ x i < x k := by
  by_contra! hnone
  have hnonneg : ∀ k ∈ (univ : Finset V), 0 ≤ w i k * (x i - x k) := by
    intro k _
    by_cases hik : G.Adj i k
    · exact mul_nonneg (hw i k) (sub_nonneg.mpr (hnone k hik))
    · simp [hoff i k hik]
  have hz : w i j * (x i - x j) = 0 :=
    (sum_eq_zero_iff_of_nonneg hnonneg).mp hi j (mem_univ j)
  exact (mul_pos (he i j hij) (sub_pos.mpr hji)).ne' hz

/-- The actual oriented graph of strictly increasing edges. -/
def IncreasingEdge (G : SimpleGraph V) (x : V → ℝ) (i j : V) : Prop :=
  G.Adj i j ∧ x i < x j

theorem increasingPath_le (G : SimpleGraph V) (x : V → ℝ) {i j : V}
    (h : ReflTransGen (IncreasingEdge G x) i j) : x i ≤ x j := by
  induction h with
  | refl => exact le_rfl
  | tail _ hnext ih => exact ih.trans hnext.2.le

theorem increasingPath_reachable (G : SimpleGraph V) (x : V → ℝ) {i j : V}
    (h : ReflTransGen (IncreasingEdge G x) i j) : G.Reachable i j := by
  induction h with
  | refl => exact .refl i
  | tail _ hnext ih => exact ih.trans hnext.1.reachable

/-- Floater's rising-path construction, with the finiteness argument supplied
by an actual maximum over all vertices reachable by strictly increasing edges. -/
theorem exists_rising_path_to_boundary (G : SimpleGraph V) (B : Set V)
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, G.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ G.Adj i j → w i j = 0)
    (x : V → ℝ) (hx : ∀ i, i ∉ B → Harmonic w x i)
    {i j : V} (hij : G.Adj i j) (hji : x j < x i) :
    ∃ b ∈ B, ReflTransGen (IncreasingEdge G x) i b ∧ x i ≤ x b := by
  classical
  let S : Finset V := univ.filter (fun v => ReflTransGen (IncreasingEdge G x) i v)
  have hiS : i ∈ S := by simp [S, ReflTransGen.refl]
  obtain ⟨b,hbS,hbmax⟩ := exists_max_image S x ⟨i,hiS⟩
  have hib : ReflTransGen (IncreasingEdge G x) i b := (mem_filter.mp hbS).2
  refine ⟨b, ?_, hib, increasingPath_le G x hib⟩
  by_contra hbB
  have hpred : ∃ a, G.Adj b a ∧ x a < x b := by
    induction hib with
    | refl => exact ⟨j,hij,hji⟩
    | @tail a b _ hnext _ => exact ⟨a,hnext.1.symm,hnext.2⟩
  obtain ⟨a,hba,hab⟩ := hpred
  obtain ⟨z,hbz,hxz⟩ := exists_higher_neighbor G w hw he hoff x (hx b hbB) hba hab
  have hzS : z ∈ S := by
    exact mem_filter.mpr ⟨mem_univ _,hib.tail ⟨hbz,hxz⟩⟩
  exact (not_lt_of_ge (hbmax z hzS)) hxz

theorem exists_falling_path_to_boundary (G : SimpleGraph V) (B : Set V)
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, G.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ G.Adj i j → w i j = 0)
    (x : V → ℝ) (hx : ∀ i, i ∉ B → Harmonic w x i)
    {i j : V} (hij : G.Adj i j) (hijx : x i < x j) :
    ∃ b ∈ B, ReflTransGen (IncreasingEdge G (fun v => -x v)) i b ∧ x b ≤ x i := by
  obtain ⟨b,hb,hpath,hle⟩ := exists_rising_path_to_boundary G B w hw he hoff
    (fun v => -x v) (fun v hv => harmonic_neg (hx v hv)) hij (neg_lt_neg hijx)
  exact ⟨b,hb,hpath,neg_le_neg_iff.mp hle⟩

end NormalProjective.Dirichlet
