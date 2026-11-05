module
public import consolidated.root_generic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Tauto

set_option Elab.async false

section BundlePart0
/- Source: Papers/FiniteMatchingCovers.lean -/




@[expose] public section

/-!
# The four-vertex matching steps in the rigid-cover argument

These are universal finite graph lemmas.  The six Boolean edge choices
are split by proof tactics; no native-evaluation axiom or external
enumeration result is used.
-/

namespace Papers.FiniteMatchingCovers

open Finset
open scoped Classical

private def flag (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

private theorem four_min_two_matching
    (e₀₁ e₀₂ e₀₃ e₁₂ e₁₃ e₂₃ : Prop)
    (h₀ : 2 ≤ flag e₀₁ + flag e₀₂ + flag e₀₃)
    (h₁ : 2 ≤ flag e₀₁ + flag e₁₂ + flag e₁₃)
    (h₂ : 2 ≤ flag e₀₂ + flag e₁₂ + flag e₂₃)
    (h₃ : 2 ≤ flag e₀₃ + flag e₁₃ + flag e₂₃) :
    (e₀₁ ∧ e₂₃) ∨ (e₀₂ ∧ e₁₃) ∨ (e₀₃ ∧ e₁₂) := by
  by_cases h01 : e₀₁ <;> by_cases h02 : e₀₂ <;>
  by_cases h03 : e₀₃ <;> by_cases h12 : e₁₂ <;>
  by_cases h13 : e₁₃ <;> by_cases h23 : e₂₃ <;>
    simp_all [flag]

private theorem four_one_regular_matching
    (e₀₁ e₀₂ e₀₃ e₁₂ e₁₃ e₂₃ : Prop)
    (h₀ : flag e₀₁ + flag e₀₂ + flag e₀₃ = 1)
    (h₁ : flag e₀₁ + flag e₁₂ + flag e₁₃ = 1)
    (h₂ : flag e₀₂ + flag e₁₂ + flag e₂₃ = 1)
    (h₃ : flag e₀₃ + flag e₁₃ + flag e₂₃ = 1) :
    (e₀₁ ∧ e₂₃) ∨ (e₀₂ ∧ e₁₃) ∨ (e₀₃ ∧ e₁₂) := by
  by_cases h01 : e₀₁ <;> by_cases h02 : e₀₂ <;>
  by_cases h03 : e₀₃ <;> by_cases h12 : e₁₂ <;>
  by_cases h13 : e₁₃ <;> by_cases h23 : e₂₃ <;>
    simp_all [flag]

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

private theorem neighbor_filter_four
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (({a,b,c,d} : Finset V).filter (G.Adj a)).card =
      flag (G.Adj a b) + flag (G.Adj a c) + flag (G.Adj a d) := by
  by_cases hb : G.Adj a b <;> by_cases hc : G.Adj a c <;>
    by_cases hd : G.Adj a d <;>
    simp_all [Finset.filter_insert, Finset.filter_singleton, flag]

theorem matching_cover_of_four_min_degree_two
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hdeg : ∀ v ∈ ({a,b,c,d} : Finset V),
      2 ≤ (({a,b,c,d} : Finset V).filter (G.Adj v)).card) :
    (G.Adj a b ∧ G.Adj c d) ∨
      (G.Adj a c ∧ G.Adj b d) ∨ (G.Adj a d ∧ G.Adj b c) := by
  apply four_min_two_matching
  · simpa only [neighbor_filter_four G a b c d hab hac had hbc hbd hcd]
      using hdeg a (by simp)
  · have h := hdeg b (by simp)
    have hs : ({a,b,c,d} : Finset V) = {b,a,c,d} := by ext; simp [or_comm, or_left_comm]
    rw [hs, neighbor_filter_four G b a c d hab.symm hbc hbd hac had hcd] at h
    simpa only [G.adj_comm] using h
  · have h := hdeg c (by simp)
    have hs : ({a,b,c,d} : Finset V) = {c,a,b,d} := by ext; simp [or_comm, or_left_comm]
    rw [hs, neighbor_filter_four G c a b d hac.symm hbc.symm hcd hab had hbd] at h
    simpa only [G.adj_comm] using h
  · have h := hdeg d (by simp)
    have hs : ({a,b,c,d} : Finset V) = {d,a,b,c} := by ext; simp [or_comm, or_left_comm]
    rw [hs, neighbor_filter_four G d a b c had.symm hbd.symm hcd.symm hab hac hbc] at h
    simpa only [G.adj_comm] using h

theorem matching_cover_of_four_degree_one
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hdeg : ∀ v ∈ ({a,b,c,d} : Finset V),
      (({a,b,c,d} : Finset V).filter (G.Adj v)).card = 1) :
    (G.Adj a b ∧ G.Adj c d) ∨
      (G.Adj a c ∧ G.Adj b d) ∨ (G.Adj a d ∧ G.Adj b c) := by
  apply four_one_regular_matching
  · simpa only [neighbor_filter_four G a b c d hab hac had hbc hbd hcd]
      using hdeg a (by simp)
  · have h := hdeg b (by simp)
    have hs : ({a,b,c,d} : Finset V) = {b,a,c,d} := by ext; simp [or_comm, or_left_comm]
    rw [hs, neighbor_filter_four G b a c d hab.symm hbc hbd hac had hcd] at h
    simpa only [G.adj_comm] using h
  · have h := hdeg c (by simp)
    have hs : ({a,b,c,d} : Finset V) = {c,a,b,d} := by ext; simp [or_comm, or_left_comm]
    rw [hs, neighbor_filter_four G c a b d hac.symm hbc.symm hcd hab had hbd] at h
    simpa only [G.adj_comm] using h
  · have h := hdeg d (by simp)
    have hs : ({a,b,c,d} : Finset V) = {d,a,b,c} := by ext; simp [or_comm, or_left_comm]
    rw [hs, neighbor_filter_four G d a b c had.symm hbd.symm hcd.symm hab hac hbc] at h
    simpa only [G.adj_comm] using h

end Papers.FiniteMatchingCovers

end
end BundlePart0

section BundlePart1
/- Source: Papers/FiniteGraphOptimization.lean -/








@[expose] public section

/-!
# Finite optimization tools

Small perturbations preserve any prescribed finite list of strict
linear inequalities.  A finite graph in which every nonminimum vertex
has a strictly descending neighbour is connected.
-/

noncomputable section
namespace Papers.FiniteGraphOptimization

open Finset
open scoped Classical

theorem exists_small_positive_perturbation {I : Type*}
    (s : Finset I) (a b : I → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t ≤ ε →
      ∀ i ∈ s, 0 < a i + t * b i := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
      intro ha
      refine ⟨1, zero_lt_one, ?_⟩
      intro t ht htle i hi
      simp only [Finset.notMem_empty] at hi
  | @insert i s hi ih =>
      intro ha
      have hai : 0 < a i := ha i (Finset.mem_insert_self i s)
      obtain ⟨ε, hε, hbound⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      let δ := a i / (|b i| + 1)
      have hden : 0 < |b i| + 1 := by positivity
      have hδ : 0 < δ := div_pos hai hden
      refine ⟨min ε δ, lt_min hε hδ, ?_⟩
      intro t ht htle j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have htδ : t ≤ δ := htle.trans (min_le_right ε δ)
        have hmul : t * (|b j| + 1) ≤ a j :=
          (le_div_iff₀ hden).mp htδ
        have hab := mul_le_mul_of_nonneg_left (neg_abs_le (b j)) ht.le
        nlinarith
      · exact hbound t ht (htle.trans (min_le_left ε δ)) j hj

section Graph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def descendingRank (φ : V → ℝ) (v : V) : ℕ :=
  (Finset.univ.filter fun w => φ w < φ v).card

theorem descendingRank_lt {φ : V → ℝ} {v w : V} (h : φ v < φ w) :
    descendingRank φ v < descendingRank φ w := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, lt_trans (Finset.mem_filter.mp hx).2 h⟩
  · intro heq
    have hv : v ∈ Finset.univ.filter (fun x => φ x < φ w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩
    rw [← heq] at hv
    exact lt_irrefl _ (Finset.mem_filter.mp hv).2

theorem connected_of_strict_descent (φ : V → ℝ) (m : V)
    (hdescent : ∀ v, v ≠ m → ∃ w, G.Adj v w ∧ φ w < φ v) :
    G.Connected := by
  have hreach : ∀ k : ℕ, ∀ v : V, descendingRank φ v = k →
      G.Reachable v m := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro v hvk
        by_cases hvm : v = m
        · subst v
          exact SimpleGraph.Reachable.rfl
        · obtain ⟨w, hvw, hwv⟩ := hdescent v hvm
          have hrank : descendingRank φ w < k := by
            rw [← hvk]
            exact descendingRank_lt hwv
          exact hvw.reachable.trans (ih _ hrank w rfl)
  letI : Nonempty V := ⟨m⟩
  exact { preconnected := fun v w =>
    (hreach _ v rfl).trans (hreach _ w rfl).symm }

end Graph
end Papers.FiniteGraphOptimization

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/TriangleCore.lean -/







@[expose] public section

/-!
# The subgraph consisting of edges in triangles

With edge-disjoint triangles this graph is locally linear.  Its degree
is the sum of degrees inside an original neighborhood, provided those
internal degrees are at most one.  The ordinary handshaking identity
then gives the two triangle-divisibility obstructions needed in the
rigid-cover count.
-/

noncomputable section
namespace Papers.GraphCounting
open Finset
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

def triangleCore : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ z, G.Adj x z ∧ G.Adj y z
  symm := ⟨by
    rintro x y ⟨hxy, z, hxz, hyz⟩
    exact ⟨hxy.symm, z, hyz, hxz⟩⟩
  loopless := ⟨by intro x hx; exact hx.1.ne rfl⟩

theorem triangleCore_le : triangleCore G ≤ G := fun _ _ h => h.1

theorem triangleCore_locallyLinear (hG : G.EdgeDisjointTriangles) :
    (triangleCore G).LocallyLinear := by
  refine ⟨SimpleGraph.EdgeDisjointTriangles.mono (triangleCore_le G) hG, ?_⟩
  intro x y hxy
  obtain ⟨hxyG, z, hxz, hyz⟩ := hxy
  refine ⟨{x, y, z}, ?_, by simp, by simp⟩
  apply SimpleGraph.is3Clique_triple_iff.mpr
  exact ⟨⟨hxyG, z, hxz, hyz⟩, ⟨hxz, y, hxyG, hyz.symm⟩,
    ⟨hyz, x, hxyG.symm, hxz.symm⟩⟩

def internalNeighborDegree (v w : V) : ℕ :=
  ((G.neighborFinset w) ∩ G.neighborFinset v).card

theorem triangleCore_neighbors (v : V) :
    (triangleCore G).neighborFinset v =
      (G.neighborFinset v).filter (fun w => internalNeighborDegree G v w ≠ 0) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
    internalNeighborDegree, Finset.card_ne_zero, Finset.Nonempty, Finset.mem_inter]
  change (G.Adj v w ∧ ∃ z, G.Adj v z ∧ G.Adj w z) ↔
    G.Adj v w ∧ ∃ z, G.Adj w z ∧ G.Adj v z
  exact and_congr_right fun _ => exists_congr fun _ => and_comm

theorem triangleCore_degree_eq_internal_sum (v : V)
    (hmatching : ∀ w ∈ G.neighborFinset v, internalNeighborDegree G v w ≤ 1) :
    (triangleCore G).degree v =
      ∑ w ∈ G.neighborFinset v, internalNeighborDegree G v w := by
  rw [SimpleGraph.degree, triangleCore_neighbors, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  have hle := hmatching w hw
  by_cases hz : internalNeighborDegree G v w = 0
  · simp [hz]
  · have hone : internalNeighborDegree G v w = 1 := by omega
    simp [hone]

theorem triangleCore_not_four_regular
    (hG : G.EdgeDisjointTriangles)
    (hcard : Fintype.card V = 10 ∨ Fintype.card V = 14) :
    ∃ v, (triangleCore G).degree v ≠ 4 := by
  by_contra! hreg
  have hs := (triangleCore G).sum_degrees_eq_twice_card_edges
  have he := (triangleCore_locallyLinear G hG).card_edgeFinset
  rw [he] at hs
  simp only [hreg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rcases hcard with hcard | hcard <;> rw [hcard] at hs <;> omega

theorem exists_internal_sum_ne_four
    (hG : G.EdgeDisjointTriangles)
    (hcard : Fintype.card V = 10 ∨ Fintype.card V = 14)
    (hmatching : ∀ v w, w ∈ G.neighborFinset v → internalNeighborDegree G v w ≤ 1) :
    ∃ v, (∑ w ∈ G.neighborFinset v, internalNeighborDegree G v w) ≠ 4 := by
  obtain ⟨v, hv⟩ := triangleCore_not_four_regular G hG hcard
  exact ⟨v, by rwa [← triangleCore_degree_eq_internal_sum G v (hmatching v)]⟩

end Papers.GraphCounting

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/SevenVertexNeighborhoodCounts.lean -/








@[expose] public section

noncomputable section
namespace Papers.NeighborhoodCounts
open Finset
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def localDegree (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

def outsideStar (v : V) : Finset V :=
  Finset.univ \ insert v (G.neighborFinset v)

theorem outsideStar_card (v : V) :
    (outsideStar G v).card = Fintype.card V - (G.degree v + 1) := by
  rw [outsideStar, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Finset.card_insert_of_notMem]
  · simp only [SimpleGraph.card_neighborFinset_eq_degree]
  · exact G.notMem_neighborFinset_self v

theorem localDegree_cut_symmetry (S T : Finset V) :
    ∑ v ∈ S, localDegree G T v = ∑ w ∈ T, localDegree G S w := by
  simp only [localDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

theorem degree_of_neighbor (v u : V) (hu : u ∈ G.neighborFinset v) :
    G.degree u = 1 + localDegree G (G.neighborFinset v) u +
      localDegree G (outsideStar G v) u := by
  have hsets : G.neighborFinset u =
      insert v (((G.neighborFinset v).filter (G.Adj u)) ∪
        ((outsideStar G v).filter (G.Adj u))) := by
    ext w
    have huv : G.Adj u v := ((G.mem_neighborFinset _ _).mp hu).symm
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_union, Finset.mem_filter, outsideStar, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    by_cases hw : w = v
    · subst w; simp [huv]
    · by_cases hvw : G.Adj v w <;> simp [hw, hvw]
  have hv : v ∉ ((G.neighborFinset v).filter (G.Adj u)) ∪
        ((outsideStar G v).filter (G.Adj u)) := by
    simp [outsideStar]
  have hd : Disjoint ((G.neighborFinset v).filter (G.Adj u))
      ((outsideStar G v).filter (G.Adj u)) := by
    apply Finset.disjoint_left.mpr
    intro w hwN hwT
    have hN := (Finset.mem_filter.mp hwN).1
    have hT := (Finset.mem_filter.mp hwT).1
    simp only [outsideStar, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_univ, true_and, not_or] at hT
    exact hT.2 hN
  rw [SimpleGraph.degree, hsets, Finset.card_insert_of_notMem hv,
    Finset.card_union_of_disjoint hd]
  simp only [localDegree]
  omega

theorem degree_outside_star (v u : V) (hu : u ∈ outsideStar G v) :
    G.degree u = localDegree G (G.neighborFinset v) u +
      localDegree G (outsideStar G v) u := by
  have hnu : u ≠ v ∧ ¬G.Adj v u := by
    simpa [outsideStar] using hu
  have hsets : G.neighborFinset u =
      ((G.neighborFinset v).filter (G.Adj u)) ∪
        ((outsideStar G v).filter (G.Adj u)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union,
      Finset.mem_filter, outsideStar, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_univ, true_and]
    by_cases hw : w = v
    · subst w
      have hno : ¬G.Adj u v := fun h => hnu.2 h.symm
      simp [hno]
    · by_cases hvw : G.Adj v w <;> simp [hw, hvw]
  have hd : Disjoint ((G.neighborFinset v).filter (G.Adj u))
      ((outsideStar G v).filter (G.Adj u)) := by
    apply Finset.disjoint_left.mpr
    intro w hwN hwT
    have hN := (Finset.mem_filter.mp hwN).1
    have hT := (Finset.mem_filter.mp hwT).1
    simp only [outsideStar, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_univ, true_and, not_or] at hT
    exact hT.2 hN
  rw [SimpleGraph.degree, hsets, Finset.card_union_of_disjoint hd]
  rfl


theorem sum_degrees_neighbors (v : V) :
    (∑ u ∈ G.neighborFinset v, G.degree u) =
      G.degree v +
        (∑ u ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) u) +
        (∑ u ∈ G.neighborFinset v, localDegree G (outsideStar G v) u) := by
  calc
    _ = ∑ u ∈ G.neighborFinset v,
      (1 + localDegree G (G.neighborFinset v) u +
        localDegree G (outsideStar G v) u) :=
      Finset.sum_congr rfl fun u hu => degree_of_neighbor G v u hu
    _ = _ := by simp [Finset.sum_add_distrib,Nat.add_assoc]

theorem neighborhood_cut_bound (v : V) (k c : ℕ)
    (hmin : ∀ u, k ≤ G.degree u)
    (hcap : ∀ w ∈ outsideStar G v,
      localDegree G (G.neighborFinset v) w ≤ c) :
    G.degree v * k ≤ G.degree v +
      (∑ u ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) u) +
      c * (outsideStar G v).card := by
  have hdeg : G.degree v * k ≤ ∑ u ∈ G.neighborFinset v, G.degree u := by
    calc
      _ = ∑ u ∈ G.neighborFinset v, k := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun u hu => hmin u
  have heq :
      (∑ u ∈ G.neighborFinset v, G.degree u) =
      G.degree v +
        (∑ u ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) u) +
        (∑ u ∈ G.neighborFinset v, localDegree G (outsideStar G v) u) := by
    calc
      _ = ∑ u ∈ G.neighborFinset v,
        (1 + localDegree G (G.neighborFinset v) u +
          localDegree G (outsideStar G v) u) :=
        Finset.sum_congr rfl fun u hu => degree_of_neighbor G v u hu
      _ = _ := by simp [Finset.sum_add_distrib, Nat.add_assoc]
  have hcut :
      (∑ u ∈ G.neighborFinset v, localDegree G (outsideStar G v) u) ≤
        c * (outsideStar G v).card := by
    rw [localDegree_cut_symmetry]
    calc
      _ ≤ ∑ w ∈ outsideStar G v, c := Finset.sum_le_sum hcap
      _ = _ := by simp [Nat.mul_comm]
  omega


theorem seven_max_degree_four
    (hcard : Fintype.card V = 7)
    (hmin : ∀ v, 3 ≤ G.degree v)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1) :
    ∀ v, G.degree v ≤ 4 := by
  intro v
  have hb := neighborhood_cut_bound G v 3 2 hmin (hcap v)
  rw [outsideStar_card, hcard] at hb
  have hlt := G.degree_lt_card_verts v
  rw [hcard] at hlt
  have hsum :
      (∑ w ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) w) ≤
        G.degree v := by
    calc
      _ ≤ ∑ w ∈ G.neighborFinset v, (1 : ℕ) := Finset.sum_le_sum (hmatch v)
      _ = _ := by simp
  omega

theorem exists_degree_four_on_seven
    (hcard : Fintype.card V = 7)
    (hmin : ∀ v, 3 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 4) :
    ∃ v, G.degree v = 4 := by
  by_contra! hn
  have heq : ∀ v, G.degree v = 3 := fun v => by
    have h₁ := hmin v
    have h₂ := hmax v
    have h₃ := hn v
    omega
  have hs := G.sum_degrees_eq_twice_card_edges
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard] at hs
  omega

theorem degree_four_neighborhood_is_matching
    (hcard : Fintype.card V = 7)
    (hmin : ∀ v, 3 ≤ G.degree v)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1)
    {v : V} (hv : G.degree v = 4) :
    ∀ u ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) u = 1 := by
  have ht : (outsideStar G v).card = 2 := by
    rw [outsideStar_card, hv, hcard]
  have hb := neighborhood_cut_bound G v 3 2 hmin (hcap v)
  rw [hv, ht] at hb
  have hN : (G.neighborFinset v).card = 4 := by simpa using hv
  intro u hu
  have hle := hmatch v u hu
  by_contra hn
  have hz : localDegree G (G.neighborFinset v) u = 0 := by omega
  have hslt :
      (∑ w ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) w) <
        ∑ w ∈ G.neighborFinset v, (1 : ℕ) := by
    apply Finset.sum_lt_sum (hmatch v)
    exact ⟨u, hu, by omega⟩
  have hs : (∑ w ∈ G.neighborFinset v, (1 : ℕ)) = 4 := by simp [hN]
  omega

theorem outside_pair_adj
    (hmin : ∀ v, 3 ≤ G.degree v)
    (v u w : V) (huw : u ≠ w)
    (hT : outsideStar G v = {u,w})
    (hcap : localDegree G (G.neighborFinset v) u ≤ 2) :
    G.Adj u w := by
  have hu : u ∈ outsideStar G v := by simp [hT]
  have hdeg := degree_outside_star G v u hu
  have hminu := hmin u
  by_contra hn
  have hz : localDegree G (outsideStar G v) u = 0 := by
    simp [localDegree, hT, hn]
  omega

end Papers.NeighborhoodCounts

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/NeighborhoodParity.lean -/




@[expose] public section

noncomputable section
namespace Papers.NeighborhoodParity
open Finset
open scoped BigOperators Classical
open Papers.NeighborhoodCounts Papers.GraphCounting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem degree_induce_eq_local (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = localDegree G S v := by
  let e : (G.induce (S : Set V)).neighborSet v ≃
      {w // w ∈ S.filter (G.Adj v)} :=
    { toFun := fun w => ⟨w.1.1, Finset.mem_filter.mpr ⟨w.1.2,w.2⟩⟩
      invFun := fun w => ⟨⟨w.1,(Finset.mem_filter.mp w.2).1⟩,
        (Finset.mem_filter.mp w.2).2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  calc
    _ = Fintype.card ((G.induce (S : Set V)).neighborSet v) :=
      (SimpleGraph.card_neighborSet_eq_degree _ _).symm
    _ = Fintype.card {w // w ∈ S.filter (G.Adj v)} := Fintype.card_congr e
    _ = localDegree G S v := by
      change Fintype.card (S.filter (G.Adj v)) = (S.filter (G.Adj v)).card
      exact Fintype.card_coe _

theorem sum_local_degrees_twice (S : Finset V) :
    ∃ e : ℕ, (∑ v ∈ S, localDegree G S v) = 2 * e := by
  have hs := (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  simp_rw [degree_induce_eq_local G S] at hs
  refine ⟨(G.induce (S : Set V)).edgeFinset.card, ?_⟩
  calc
    (∑ v ∈ S, localDegree G S v) = ∑ v : S, localDegree G S v :=
      (Finset.sum_coe_sort S (fun v => localDegree G S v)).symm
    _ = _ := hs

theorem local_degree_neighbor_eq_internal (v w : V) :
    localDegree G (G.neighborFinset v) w = internalNeighborDegree G v w := by
  unfold localDegree internalNeighborDegree
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  tauto

theorem edge_disjoint_triangles_of_neighbor_matchings
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1) :
    G.EdgeDisjointTriangles := by
  intro S hS T hT hST x hx y hy
  by_contra hxy
  have hs : G.IsNClique 3 S := SimpleGraph.mem_cliqueSet_iff.mp hS
  have ht : G.IsNClique 3 T := SimpleGraph.mem_cliqueSet_iff.mp hT
  have hAdj : G.Adj x y := hs.isClique hx.1 hy.1 hxy
  let C := (G.neighborFinset x).filter (G.Adj y)
  let U := insert x (insert y C)
  have hc : C.card ≤ 1 := hmatch x y ((G.mem_neighborFinset _ _).mpr hAdj)
  have hU : U.card ≤ 3 := by
    have h₁ := Finset.card_insert_le x (insert y C)
    have h₂ := Finset.card_insert_le y C
    dsimp [U]
    omega
  have sub (R : Finset V) (hR : G.IsNClique 3 R)
      (hxR : x ∈ R) (hyR : y ∈ R) : R ⊆ U := by
    intro z hz
    by_cases hzx : z = x
    · subst z; exact Finset.mem_insert_self _ _
    by_cases hzy : z = y
    · subst z; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    exact ⟨(G.mem_neighborFinset _ _).mpr (hR.isClique hxR hz (Ne.symm hzx)),
      hR.isClique hyR hz (Ne.symm hzy)⟩
  have hScard := hs.card_eq
  have hTcard := ht.card_eq
  have hSU : S = U := Finset.eq_of_subset_of_card_le
    (sub S hs hx.1 hy.1) (by omega)
  have hTU : T = U := Finset.eq_of_subset_of_card_le
    (sub T ht hx.2 hy.2) (by omega)
  exact hST (hSU.trans hTU.symm)

theorem impossible_min_five_on_fourteen
    (hcard : Fintype.card V = 14)
    (hmin : ∀ v, 5 ≤ G.degree v)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1) :
    False := by
  have hregular : ∀ v, G.degree v = 5 := by
    intro v
    have hb := neighborhood_cut_bound G v 5 2 hmin (hcap v)
    rw [outsideStar_card,hcard] at hb
    have hlt := G.degree_lt_card_verts v
    rw [hcard] at hlt
    have hs : (∑ w ∈ G.neighborFinset v,
        localDegree G (G.neighborFinset v) w) ≤ G.degree v := by
      calc
        _ ≤ ∑ w ∈ G.neighborFinset v, (1 : ℕ) := Finset.sum_le_sum (hmatch v)
        _ = _ := by simp
    have hm := hmin v
    omega
  have hsum : ∀ v, (∑ w ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) = 4 := by
    intro v
    have hb := neighborhood_cut_bound G v 5 2 hmin (hcap v)
    rw [outsideStar_card,hcard,hregular] at hb
    have hs : (∑ w ∈ G.neighborFinset v,
        localDegree G (G.neighborFinset v) w) ≤ 5 := by
      calc
        _ ≤ ∑ w ∈ G.neighborFinset v, (1 : ℕ) := Finset.sum_le_sum (hmatch v)
        _ = 5 := by simp [hregular]
    obtain ⟨e,he⟩ := sum_local_degrees_twice G (G.neighborFinset v)
    omega
  have hedt := edge_disjoint_triangles_of_neighbor_matchings G hmatch
  obtain ⟨v,hv⟩ := triangleCore_not_four_regular G hedt (Or.inr hcard)
  apply hv
  have hmatch' : ∀ w ∈ G.neighborFinset v, internalNeighborDegree G v w ≤ 1 := by
    intro w hw
    simpa only [← local_degree_neighbor_eq_internal] using hmatch v w hw
  rw [triangleCore_degree_eq_internal_sum G v hmatch']
  simpa only [← local_degree_neighbor_eq_internal] using hsum v


theorem impossible_min_five_order_at_most_fourteen [Nonempty V]
    (hcard : Fintype.card V ≤ 14)
    (hmin : ∀ v, 5 ≤ G.degree v)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1) :
    False := by
  let v : V := Classical.choice inferInstance
  have hb := neighborhood_cut_bound G v 5 2 hmin (hcap v)
  rw [outsideStar_card] at hb
  have hlt := G.degree_lt_card_verts v
  have hm := hmin v
  have hs : (∑ w ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) ≤ G.degree v := by
    calc
      _ ≤ ∑ w ∈ G.neighborFinset v, (1 : ℕ) := Finset.sum_le_sum (hmatch v)
      _ = _ := by simp
  have hn : Fintype.card V = 14 := by omega
  exact impossible_min_five_on_fourteen G hn hmin hcap hmatch

end Papers.NeighborhoodParity

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/FourRegularTailCounts.lean -/



@[expose] public section

noncomputable section
namespace Papers.FourRegularTail
open Finset
open scoped BigOperators Classical
open Papers.NeighborhoodCounts Papers.NeighborhoodParity Papers.GraphCounting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem regularity_and_order [Nonempty V]
    (hcard : Fintype.card V ≤ 10)
    (hmin : ∀ v, 4 ≤ G.degree v)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1) :
    (Fintype.card V = 9 ∨ Fintype.card V = 10) ∧ ∀ v, G.degree v = 4 := by
  have hbnd (v : V) :
      9 ≤ Fintype.card V ∧ G.degree v = 4 := by
    have hb := neighborhood_cut_bound G v 4 2 hmin (hcap v)
    rw [outsideStar_card] at hb
    have hlt := G.degree_lt_card_verts v
    have hm := hmin v
    have hs : (∑ w ∈ G.neighborFinset v,
        localDegree G (G.neighborFinset v) w) ≤ G.degree v := by
      calc
        _ ≤ ∑ w ∈ G.neighborFinset v, (1 : ℕ) := Finset.sum_le_sum (hmatch v)
        _ = _ := by simp
    omega
  have hn := (hbnd (Classical.choice inferInstance)).1
  exact ⟨by omega,fun v => (hbnd v).2⟩

theorem triangle_in_nine_vertex_tail
    (hcard : Fintype.card V = 9) (hreg : ∀ v, G.degree v = 4)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2) (v : V) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  have hb := neighborhood_cut_bound G v 4 2 (fun v => (hreg v).ge) (hcap v)
  rw [outsideStar_card,hcard,hreg] at hb
  by_contra hn
  have hz : ∀ a ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) a = 0 := by
    intro a ha
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hbN,hab⟩ := Finset.mem_filter.mp hb
    exact hn ⟨a,b,(G.mem_neighborFinset _ _).mp ha,(G.mem_neighborFinset _ _).mp hbN,hab⟩
  have hsum : (∑ a ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) a) = 0 := Finset.sum_eq_zero hz
  omega

theorem ten_vertex_star_saturated
    (hcard : Fintype.card V = 10) (hreg : ∀ v, G.degree v = 4)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1) :
    ∃ v, (∑ w ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) = 2 ∧
      ∀ w ∈ outsideStar G v,
        localDegree G (G.neighborFinset v) w = 2 := by
  have hedt := edge_disjoint_triangles_of_neighbor_matchings G hmatch
  obtain ⟨v,hv⟩ := triangleCore_not_four_regular G hedt (Or.inl hcard)
  have hmatching : ∀ w ∈ G.neighborFinset v, internalNeighborDegree G v w ≤ 1 := by
    intro w hw
    simpa only [← local_degree_neighbor_eq_internal] using hmatch v w hw
  have hcdeg := triangleCore_degree_eq_internal_sum G v hmatching
  simp_rw [← local_degree_neighbor_eq_internal] at hcdeg
  have hne : (∑ w ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) ≠ 4 := by
    intro h
    exact hv (hcdeg.trans h)
  have hb := neighborhood_cut_bound G v 4 2 (fun w => (hreg w).ge) (hcap v)
  rw [outsideStar_card,hcard,hreg] at hb
  have hsle : (∑ w ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) ≤ 4 := by
    calc
      _ ≤ ∑ w ∈ G.neighborFinset v, (1 : ℕ) := Finset.sum_le_sum (hmatch v)
      _ = _ := by simp [hreg]
  obtain ⟨e,he⟩ := sum_local_degrees_twice G (G.neighborFinset v)
  have hs2 : (∑ w ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) = 2 := by omega
  refine ⟨v,hs2,?_⟩
  have hsplit := sum_degrees_neighbors G v
  have hleft : (∑ u ∈ G.neighborFinset v, G.degree u) = 16 := by simp [hreg]
  rw [hleft,hreg,hs2] at hsplit
  have hcut : (∑ w ∈ outsideStar G v,
      localDegree G (G.neighborFinset v) w) = 10 := by
    rw [← localDegree_cut_symmetry G (G.neighborFinset v) (outsideStar G v)]
    omega
  have hTcard : (outsideStar G v).card = 5 := by rw [outsideStar_card,hcard,hreg]
  intro w hw
  have hle := hcap v w hw
  by_contra hn
  have hlt : localDegree G (G.neighborFinset v) w < 2 := by omega
  have hsumlt :
      (∑ z ∈ outsideStar G v, localDegree G (G.neighborFinset v) z) <
        ∑ _z ∈ outsideStar G v, (2 : ℕ) :=
    Finset.sum_lt_sum (hcap v) ⟨w,hw,hlt⟩
  have hr : (∑ _z ∈ outsideStar G v, (2 : ℕ)) = 10 := by simp [hTcard]
  omega

end Papers.FourRegularTail

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/SevenVertexSmallComponents.lean -/





@[expose] public section

noncomputable section
namespace Papers.SmallNeighborComponents
open Finset
open scoped BigOperators Classical
open Papers.NeighborhoodCounts Papers.NeighborhoodParity

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Every walk of length three without immediate reversal closes a triangle.
This follows when every connected component has at most three vertices. -/
def NoFourVertexPath : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
    a ≠ c → b ≠ d → a = d

theorem matching_neighbors_of_degree_le_two
    (hdeg : ∀ v, G.degree v ≤ 2) :
    ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1 := by
  intro v w hw
  have hsub : (G.neighborFinset v).filter (G.Adj w) ⊆
      (G.neighborFinset v).erase w := by
    intro x hx
    obtain ⟨hxN,hAdj⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨hAdj.ne.symm,hxN⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hw,SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hd := hdeg v
  exact hc.trans (by omega)

theorem locally_linear_of_two_regular_and_short_components
    (hreg : ∀ v, G.degree v = 2) (hpath : NoFourVertexPath G) :
    G.LocallyLinear := by
  have hdeg : ∀ v, G.degree v ≤ 2 := fun v => le_of_eq (hreg v)
  refine ⟨edge_disjoint_triangles_of_neighbor_matchings G
    (matching_neighbors_of_degree_le_two G hdeg), ?_⟩
  intro x y hxy
  have hxcard : ((G.neighborFinset x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hxy),
      SimpleGraph.card_neighborFinset_eq_degree,hreg]
  have hycard : ((G.neighborFinset y).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hxy.symm),
      SimpleGraph.card_neighborFinset_eq_degree,hreg]
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset x).erase y).card)
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset y).erase x).card)
  obtain ⟨hwy,hwN⟩ := Finset.mem_erase.mp hw
  obtain ⟨hzx,hzN⟩ := Finset.mem_erase.mp hz
  have hxw := (G.mem_neighborFinset _ _).mp hwN
  have hyz := (G.mem_neighborFinset _ _).mp hzN
  have hzw : z = w := hpath z y x w hyz.symm hxy.symm hxw hzx (Ne.symm hwy)
  subst z
  refine ⟨{x,y,w}, SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxw,hyz⟩, ?_, ?_⟩ <;> simp

theorem degree_sum_le_twelve_on_seven
    (hcard : Fintype.card V = 7)
    (hdeg : ∀ v, G.degree v ≤ 2)
    (hpath : NoFourVertexPath G) :
    (∑ v, G.degree v) ≤ 12 := by
  have hnot : ∃ v, G.degree v ≠ 2 := by
    by_contra! hreg
    have hLL := locally_linear_of_two_regular_and_short_components G hreg hpath
    have hs := G.sum_degrees_eq_twice_card_edges
    rw [hLL.card_edgeFinset] at hs
    simp only [hreg,Finset.sum_const,Finset.card_univ,hcard,smul_eq_mul] at hs
    omega
  obtain ⟨v,hv⟩ := hnot
  have hsumlt : (∑ w, G.degree w) < ∑ _w : V, (2 : ℕ) := by
    apply Finset.sum_lt_sum (fun w _ => hdeg w)
    exact ⟨v,Finset.mem_univ v,by have h := hdeg v; omega⟩
  have hsum2 : (∑ _w : V, (2 : ℕ)) = 14 := by simp [hcard]
  have hs := G.sum_degrees_eq_twice_card_edges
  omega


/-- The degree-seven obstruction in dimension six, before the geometric
interpretation of small rigid sets. -/
theorem min_six_order_nineteen_degree_at_most_six
    (hcard : Fintype.card V ≤ 19)
    (hmin : ∀ v, 6 ≤ G.degree v)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hneighbor : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hpath : ∀ v, NoFourVertexPath (G.induce (G.neighborFinset v : Set V))) :
    ∀ v, G.degree v ≤ 6 := by
  intro v
  by_contra hn
  have hbig : 7 ≤ G.degree v := by omega
  have hb := neighborhood_cut_bound G v 6 2 hmin (hcap v)
  rw [outsideStar_card] at hb
  have hlt := G.degree_lt_card_verts v
  have hs2 : (∑ w ∈ G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) ≤ 2 * G.degree v := by
    calc
      _ ≤ ∑ w ∈ G.neighborFinset v, (2 : ℕ) := Finset.sum_le_sum (hneighbor v)
      _ = _ := by simp [Nat.mul_comm]
  have hd : G.degree v = 7 := by omega
  have hNcard : Fintype.card (G.neighborFinset v) = 7 := by
    rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
    exact hd
  have hNdeg : ∀ w : G.neighborFinset v,
      (G.induce (G.neighborFinset v : Set V)).degree w ≤ 2 := by
    intro w
    rw [degree_induce_eq_local G (G.neighborFinset v)]
    exact hneighbor v w w.2
  have hs12 : (∑ w : G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) ≤ 12 := by
    have heq : (∑ w : G.neighborFinset v,
        (G.induce (G.neighborFinset v : Set V)).degree w) =
        ∑ w : G.neighborFinset v, localDegree G (G.neighborFinset v) w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact degree_induce_eq_local G (G.neighborFinset v) w
    rw [← heq]
    exact degree_sum_le_twelve_on_seven
      (G.induce (G.neighborFinset v : Set V)) hNcard hNdeg (hpath v)
  have he : (∑ w : G.neighborFinset v,
      localDegree G (G.neighborFinset v) w) =
      ∑ w ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) w :=
    Finset.sum_coe_sort _ _
  rw [he] at hs12
  rw [hd] at hb
  omega

end Papers.SmallNeighborComponents

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/SevenVertexSigmaCover.lean -/





@[expose] public section

noncomputable section
namespace Papers.SevenVertexCover
open Finset
open scoped Classical
open Papers.NeighborhoodCounts Papers.FiniteMatchingCovers

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

private theorem triangles_of_matching
    (v a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcenter : ∀ w ∈ ({a,b,c,d} : Finset V), G.Adj v w)
    (he₁ : G.Adj a b) (he₂ : G.Adj c d) :
    ∃ A B : Finset V, G.IsNClique 3 A ∧ G.IsNClique 3 B ∧
      A ∩ B = {v} ∧ A ∪ B = insert v {a,b,c,d} := by
  have hva := hcenter a (by simp)
  have hvb := hcenter b (by simp)
  have hvc := hcenter c (by simp)
  have hvd := hcenter d (by simp)
  refine ⟨{v,a,b}, {v,c,d},
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hva,hvb,he₁⟩,
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hvc,hvd,he₂⟩, ?_, ?_⟩
  · ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzA,hzB⟩
      rcases hzA with rfl | rfl | rfl
      · rfl
      · rcases hzB with h | h | h
        · exact h
        · exact (hac h).elim
        · exact (had h).elim
      · rcases hzB with h | h | h
        · exact h
        · exact (hbc h).elim
        · exact (hbd h).elim
    · intro h; subst z; simp
  · ext z
    simp [or_assoc, or_left_comm, or_comm]

theorem exists_sigma_clique_cover
    (hcard : Fintype.card V = 7)
    (hmin : ∀ v, 3 ≤ G.degree v)
    (hcap : ∀ v w, w ∈ outsideStar G v →
      localDegree G (G.neighborFinset v) w ≤ 2)
    (hmatch : ∀ v w, w ∈ G.neighborFinset v →
      localDegree G (G.neighborFinset v) w ≤ 1) :
    ∃ v : V, ∃ A B C : Finset V,
      G.IsNClique 3 A ∧ G.IsNClique 3 B ∧ G.IsNClique 2 C ∧
      A ∩ B = {v} ∧ Disjoint (A ∪ B) C ∧
      A ∪ B ∪ C = Finset.univ := by
  have hmax := seven_max_degree_four G hcard hmin hcap hmatch
  obtain ⟨v,hv⟩ := exists_degree_four_on_seven G hcard hmin hmax
  have hNcard : (G.neighborFinset v).card = 4 := by simpa using hv
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hN⟩ := Finset.card_eq_four.mp hNcard
  have hcenter : ∀ w ∈ ({a,b,c,d} : Finset V), G.Adj v w := by
    intro w hw
    exact (G.mem_neighborFinset _ _).mp (hN.symm ▸ hw)
  have hmatch1 := degree_four_neighborhood_is_matching G hcard hmin hcap hmatch hv
  have hdeg : ∀ w ∈ ({a,b,c,d} : Finset V),
      (({a,b,c,d} : Finset V).filter (G.Adj w)).card = 1 := by
    intro w hw
    have h := hmatch1 w (hN.symm ▸ hw)
    simpa only [localDegree, hN] using h
  have hm := matching_cover_of_four_degree_one G a b c d
    hab hac had hbc hbd hcd hdeg
  have hAB : ∃ A B : Finset V, G.IsNClique 3 A ∧ G.IsNClique 3 B ∧
      A ∩ B = {v} ∧ A ∪ B = insert v (G.neighborFinset v) := by
    rw [hN]
    rcases hm with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact triangles_of_matching G v a b c d hab hac had hbc hbd hcd hcenter h₁ h₂
    · have h := triangles_of_matching G v a c b d hac hab had hbc.symm hcd hbd
        (by intro w hw; apply hcenter w; simpa [or_assoc,or_left_comm,or_comm] using hw) h₁ h₂
      obtain ⟨A,B,hA,hB,hinter,hunion⟩ := h
      refine ⟨A,B,hA,hB,hinter,hunion.trans ?_⟩
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · have h := triangles_of_matching G v a d b c had hab hac hbd.symm hcd.symm hbc
        (by intro w hw; apply hcenter w; simpa [or_assoc,or_left_comm,or_comm] using hw) h₁ h₂
      obtain ⟨A,B,hA,hB,hinter,hunion⟩ := h
      refine ⟨A,B,hA,hB,hinter,hunion.trans ?_⟩
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  obtain ⟨A,B,hA,hB,hinter,hunion⟩ := hAB
  have hTcard : (outsideStar G v).card = 2 := by rw [outsideStar_card,hcard,hv]
  obtain ⟨u,w,huw,hT⟩ := Finset.card_eq_two.mp hTcard
  have hu : u ∈ outsideStar G v := by simp [hT]
  have hadj := outside_pair_adj G hmin v u w huw hT (hcap v u hu)
  have hC : G.IsNClique 2 (outsideStar G v) := by
    rw [hT]
    refine ⟨?_, by simp [huw]⟩
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (SimpleGraph.isClique_pair.mpr (fun _ => hadj) : G.IsClique ({u,w} : Set V))
  refine ⟨v,A,B,outsideStar G v,hA,hB,hC,hinter,?_,?_⟩
  · rw [hunion]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  · rw [hunion]
    ext x
    simp only [outsideStar, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_univ, true_and, iff_true]
    exact Classical.em _

end Papers.SevenVertexCover

end
end
end BundlePart7

