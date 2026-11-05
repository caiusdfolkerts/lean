module

public import Continuation.CycleBounds.GraphDirections
public import Continuation.CycleBounds.CycleWords
public import Recovery.Unimodular.ProductVectorMatroid
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-! # A circuit supplies an actual simple path after one edge is removed

The proof uses an ordinary component indicator to separate two disconnected
vertices. Thus membership in the linear span of the other incidence columns
forces actual graph connectivity; a simple path then comes from Mathlib.
-/

noncomputable section
open scoped BigOperators Matroid
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E : Type*}

/-- The ordinary simple graph supported by a chosen set of multigraph edges.
Parallel labels are retained in the vector matroid, while adjacency forgets them. -/
def supportGraph (G : IncidenceGraph V E) (C : Set E) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ e ∈ C,
    (G.source e = a ∧ G.target e = b) ∨ (G.source e = b ∧ G.target e = a)
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by obtain ⟨e, he, hor⟩ := h.2; exact ⟨e, he, hor.symm⟩⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

theorem supportGraph_adj {G : IncidenceGraph V E} {C : Set E} {a b : V}
    (hC : C ⊆ G.edges) (h : (supportGraph G C).Adj a b) : Adj G a b := by
  obtain ⟨hne, e, he, hor⟩ := h
  exact ⟨hne, e, hC he, hor⟩

/-- Every circuit edge lies in the actual span of the remaining columns. -/
theorem circuit_column_mem_span (G : IncidenceGraph V E) {C : Set E}
    (hC : G.cycleMatroid.IsCircuit C) {e : E} (he : e ∈ C) :
    G.column e ∈ Submodule.span ℝ (G.column '' (C \ {e})) := by
  have hh := VectorMatroid.isBasis_span_eq G.column (hC.sdiff_singleton_isBasis he)
  rw [hh]
  exact Submodule.subset_span ⟨e, he, rfl⟩

/-- A component indicator detects every failure of connectivity. Consequently
an incidence column in the span of a set of other columns has connected endpoints. -/
theorem reachable_of_column_mem_span [Fintype V] (G : IncidenceGraph V E)
    (C : Set E) (e : E)
    (hspan : G.column e ∈ Submodule.span ℝ (G.column '' C)) :
    (supportGraph G C).Reachable (G.source e) (G.target e) := by
  let H := supportGraph G C
  by_contra hn
  let c : V → Bool := fun x ↦ decide (H.Reachable (G.source e) x)
  let φ := componentForm c true
  have hzero (j : E) (hj : j ∈ C) : φ (G.column j) = 0 := by
    have hsame : c (G.source j) = c (G.target j) := by
      dsimp only [c]
      apply Bool.decide_congr
      by_cases hst : G.source j = G.target j
      · rw [hst]
      have hadj : H.Adj (G.source j) (G.target j) :=
        ⟨hst, j, hj, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨fun h ↦ h.trans hadj.reachable, fun h ↦ h.trans hadj.symm.reachable⟩
    change componentForm c true (Pi.single (G.source j) 1 - Pi.single (G.target j) 1) = 0
    rw [componentForm_edge, hsame]
    exact sub_self _
  have hker : Submodule.span ℝ (G.column '' C) ≤ LinearMap.ker φ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact hzero j hj
  have hh : φ (G.column e) = 0 := hker hspan
  have hs : H.Reachable (G.source e) (G.source e) := SimpleGraph.Reachable.refl _
  change ¬H.Reachable (G.source e) (G.target e) at hn
  simpa [φ, column, vertex, componentForm_edge, c, hs, hn] using hh

/-- Removing a distinguished edge from any incidence-matroid circuit leaves a
simple path between its endpoints. Parallel two-edge circuits are included. -/
theorem circuit_exists_path [Fintype V] (G : IncidenceGraph V E) {C : Set E}
    (hC : G.cycleMatroid.IsCircuit C) {e : E} (he : e ∈ C) :
    ∃ p : (supportGraph G (C \ {e})).Walk (G.target e) (G.source e), p.IsPath := by
  have hr := reachable_of_column_mem_span G (C \ {e}) e
    (circuit_column_mem_span G hC he)
  exact hr.symm.exists_isPath

/-- A simple path closed by one additional edge is a genuine cyclic word.
Its vertices are distinct even when the two edges of the cycle are parallel. -/
theorem cycleWord_of_path (G : IncidenceGraph V E) {C : Set E}
    (hC : C ⊆ G.edges) (e : E) (he : e ∈ G.edges)
    (hne : G.source e ≠ G.target e)
    (p : (supportGraph G C).Walk (G.target e) (G.source e)) (hp : p.IsPath) :
    CycleWord G p.support := by
  refine ⟨p.support_ne_nil, hp.support_nodup, ?_⟩
  have hchain : p.support.IsChain (Adj G) :=
    p.isChain_adj_support.imp (fun _ _ h ↦ supportGraph_adj hC h)
  apply hchain.append hchain
  intro x hx y hy
  have hx' : x = G.source e := by
    rw [List.getLast?_eq_getLast_of_ne_nil p.support_ne_nil, p.getLast_support] at hx
    simpa only [Option.mem_some_iff, eq_comm] using hx
  have hy' : y = G.target e := by
    rw [List.head?_eq_some_head p.support_ne_nil, p.head_support] at hy
    simpa only [Option.mem_some_iff, eq_comm] using hy
  subst x
  subst y
  exact ⟨hne, e, he, Or.inl ⟨rfl, rfl⟩⟩

#print axioms circuit_exists_path
#print axioms cycleWord_of_path
end Unimodular.CycleBounds
