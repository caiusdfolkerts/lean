module

public import Continuation.CycleBounds.ActiveComponents
public import Continuation.CycleBounds.GraphDirections
public import Continuation.CycleBounds.CycleSums

@[expose] public section

/-! # The unrestricted graphic wall bound

This is the numerical graph theorem underlying Proposition6.8. The active
space is defined by the actual ray equations, and K4 exclusion is the literal
edge-deletion/edge-contraction hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E N : Type*} [Fintype V] [AddCommGroup N] [Module ℝ N]
    [FiniteDimensional ℝ N]

/-- Every normalized signed simple cycle in a K4-minor-free incidence family
has ceiling wall sum bounded by the dimension of the actual active kernel. -/
theorem graph_wall_bound (G : IncidenceGraph V E) (hK : ¬G.HasK4Minor)
    (v : E → N) (ι : N →ₗ[ℝ] (V → ℝ))
    (hι : ∀ e, ι (v e) = Pi.single (G.source e) 1 - Pi.single (G.target e) 1)
    (h : V → ℝ) (n : ℕ) (hn : 0 < n) (vertices : Fin n → V)
    (edges : Fin n → E) (ε : Fin n → ℤ)
    (hcycle : CycleWord G (List.ofFn vertices))
    (hedges : ∀ i, edges i ∈ G.edges ∧
      ((ε i = 1 ∧ G.source (edges i) = vertices i ∧
          G.target (edges i) = vertices (finRotate n i)) ∨
       (ε i = -1 ∧ G.source (edges i) = vertices (finRotate n i) ∧
          G.target (edges i) = vertices i)))
    (hlo : ∀ i, -1 < h (G.source (edges i)) - h (G.target (edges i)))
    (hhi : ∀ i, h (G.source (edges i)) - h (G.target (edges i)) < 1) :
    (∑ i, ε i * ⌈h (G.source (edges i)) - h (G.target (edges i))⌉) ≤
      (Module.finrank ℝ (activeDirections v
        {e | e ∈ G.edges ∧ h (G.source e) = h (G.target e)}) : ℤ) := by
  let A : Set E := {e | e ∈ G.edges ∧ h (G.source e) = h (G.target e)}
  let c := activeComponent G h
  have hc : ∀ e ∈ A, c (G.source e) = c (G.target e) := by
    intro e he
    exact activeComponent_edge G h e he.1 he.2
  let f := componentDirection v G.source G.target ι hι A c hc
  let labels := c ∘ vertices
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    exact ((hedges i).2).elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  have hnc : Noncrossing (List.ofFn labels) := by
    simpa only [labels, List.map_ofFn] using
      active_components_noncrossing G h hK (List.ofFn vertices) hcycle
  have hpath : (List.ofFn labels).IsChain (IncidenceTest f) := by
    have hwalk : (List.ofFn vertices).IsChain (fun a b ↦ ∃ e,
        (G.source e = a ∧ G.target e = b) ∨
        (G.source e = b ∧ G.target e = a)) := by
      apply hcycle.chain.left_of_append.imp
      intro a b hab
      obtain ⟨_, e, he, hor⟩ := hab
      exact ⟨e, hor⟩
    simpa only [f, labels, List.map_ofFn] using
      componentDirection_path v G.source G.target ι hι A c hc (List.ofFn vertices) hwalk
  apply signed_wall_le_finrank n hn labels (componentPotential G h) f
    (fun i ↦ h (G.source (edges i)) - h (G.target (edges i))) ε hε hlo hhi ?_ hnc hpath
  intro i
  rcases (hedges i).2 with ⟨hε, hs, ht⟩ | ⟨hε, hs, ht⟩
  · simp [labels, c, Function.comp_apply, hε, hs, ht]
  · simp [labels, c, Function.comp_apply, hε, hs, ht]

#print axioms graph_wall_bound
end Unimodular.CycleBounds
