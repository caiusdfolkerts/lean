module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Finite graph lemmas for the generic-height proof of Euler's formula in
dimension three.  Proper connected induced subgraphs of a connected graph
of degree at most two are trees.  A strict-descent rule makes each nonempty
sublevel induced graph connected.

DRAFT: these proofs have not compiled in the unavailable execution environment.
-/
namespace Papers.RationalityTen.PolygonMorseGraph

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cycle_support_closed
    (hdeg : ∀ v, G.degree v ≤ 2)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    {v w : V} (hv : v ∈ c.support) (hvw : G.Adj v w) :
    w ∈ c.support := by
  let q := c.rotate v hv
  have hq : q.IsCycle := hc.rotate hv
  have hne : q.snd ≠ q.penultimate := hq.snd_ne_penultimate
  have hs : G.Adj v q.snd := SimpleGraph.Walk.adj_snd hq.not_nil
  have ht : G.Adj v q.penultimate :=
    (SimpleGraph.Walk.adj_penultimate hq.not_nil).symm
  have hsub : ({q.snd,q.penultimate} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hs
    · exact (G.mem_neighborFinset _ _).mpr ht
  have heq : ({q.snd,q.penultimate} : Finset V) = G.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le hsub
    have hh := hdeg v
    change (G.neighborFinset v).card ≤ 2 at hh
    simpa [hne] using hh
  have hw : w ∈ ({q.snd,q.penultimate} : Finset V) := by
    rw [heq]
    exact (G.mem_neighborFinset _ _).mpr hvw
  have hwq : w ∈ q.support := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact q.getVert_mem_support 1
    · exact q.getVert_mem_support (q.length - 1)
  exact (c.mem_support_rotate_iff v hv).mp hwq

theorem cycle_support_all
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    ∀ v, v ∈ c.support := by
  have hwalk : ∀ {a b : V} (p : G.Walk a b),
      a ∈ c.support → b ∈ c.support := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a b d hab p ih =>
        intro ha
        exact ih (cycle_support_closed G hdeg c hc ha hab)
  intro v
  obtain ⟨p⟩ := hconn.preconnected u v
  exact hwalk p c.start_mem_support

/-- This requires a genuinely proper vertex subset.  In particular it does
not assert that the entire polygon graph is acyclic. -/
theorem proper_induce_acyclic
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (S : Set V) (hproper : ∃ v, v ∉ S) :
    (G.induce S).IsAcyclic := by
  classical
  intro v c hc
  let f : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hm : (c.map f).IsCycle := hc.map hf
  obtain ⟨w, hw⟩ := hproper
  have hws := cycle_support_all G hconn hdeg (c.map f) hm w
  rw [SimpleGraph.Walk.support_map] at hws
  obtain ⟨x,hx,hxw⟩ := List.mem_map.mp hws
  exact hw (hxw ▸ x.property)

theorem proper_connected_induce_tree
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (S : Set V) (hproper : ∃ v, v ∉ S)
    (hS : (G.induce S).Connected) :
    (G.induce S).IsTree :=
  ⟨hS, proper_induce_acyclic G hconn hdeg S hproper⟩

theorem proper_connected_induce_edge_count
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (S : Set V) (hproper : ∃ v, v ∉ S)
    (hS : (G.induce S).Connected) :
    Nat.card (G.induce S).edgeSet + 1 = Nat.card S := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype (G.induce S).edgeSet := Fintype.ofFinite _
  have hh := (proper_connected_induce_tree G hconn hdeg S hproper hS).card_edgeFinset
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hh

noncomputable def lowerRank (φ : V → ℝ) (v : V) : Nat :=
  (Finset.univ.filter fun w => φ w < φ v).card

theorem lowerRank_lt {φ : V → ℝ} {v w : V} (h : φ v < φ w) :
    lowerRank φ v < lowerRank φ w := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hx h⟩
  · intro heq
    have hv : v ∈ Finset.univ.filter fun x => φ x < φ w :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← heq] at hv
    exact (lt_irrefl (φ v)) (Finset.mem_filter.mp hv).2

theorem sublevel_connected_of_descent
    (φ : V → ℝ) (m : V)
    (hdescent : ∀ v, v ≠ m → ∃ w, G.Adj v w ∧ φ w < φ v)
    (a : ℝ) (hma : φ m < a) :
    (G.induce {v | φ v < a}).Connected := by
  classical
  let S : Set V := {v | φ v < a}
  let mm : S := ⟨m,hma⟩
  have hreach : ∀ k : Nat, ∀ v : V, lowerRank φ v = k →
      ∀ hv : φ v < a, (G.induce S).Reachable ⟨v,hv⟩ mm := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro v hvk hv
        by_cases hvm : v = m
        · subst v
          exact SimpleGraph.Reachable.rfl
        · obtain ⟨w,hvw,hwv⟩ := hdescent v hvm
          have hw : φ w < a := lt_trans hwv hv
          have hrank : lowerRank φ w < k := by
            rw [← hvk]
            exact lowerRank_lt hwv
          have hadj : (G.induce S).Adj ⟨v,hv⟩ ⟨w,hw⟩ := hvw
          exact hadj.reachable.trans (ih (lowerRank φ w) hrank w rfl hw)
  letI : Nonempty S := ⟨mm⟩
  refine ⟨?_⟩
  intro v w
  exact (hreach _ v.val rfl v.property).trans
    (hreach _ w.val rfl w.property).symm

theorem sublevel_edge_count
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (φ : V → ℝ) (m : V)
    (hdescent : ∀ v, v ≠ m → ∃ w, G.Adj v w ∧ φ w < φ v)
    (a : ℝ) (hma : φ m < a) (hproper : ∃ v, a ≤ φ v) :
    Nat.card (G.induce {v | φ v < a}).edgeSet + 1 =
      Nat.card {v | φ v < a} := by
  classical
  apply proper_connected_induce_edge_count G hconn hdeg
    {v | φ v < a}
  · obtain ⟨v,hv⟩ := hproper
    exact ⟨v, not_lt.mpr hv⟩
  · exact sublevel_connected_of_descent G φ m hdescent a hma

end Papers.RationalityTen.PolygonMorseGraph
