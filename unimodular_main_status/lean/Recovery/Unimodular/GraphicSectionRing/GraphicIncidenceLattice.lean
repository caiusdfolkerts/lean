module

public import Recovery.Unimodular.GraphicSectionRing.GraphicRootedLattice

/-!
# The component-balanced lattice is exactly the integral edge span

A walk telescopes to the difference of its endpoint vectors. Hence every
rooted basis vector is an integral sum of actual graph edges. This identifies
the balanced lattice with the literal integer span, without saturation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicRootedLattice
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- One actual graph vertex in each connected component. -/
def graphRoot (a : G.ConnectedComponent) : V := Quot.out a

 theorem graphRoot_component : Function.RightInverse (graphRoot G) G.connectedComponentMk := by
  intro a
  exact Quot.out_eq a

/-- The literal integral span of all directed edge columns. Parallel copies
and the choice of orientation do not change this integral lattice. -/
def incidenceSpan : Submodule ℤ (V → ℤ) :=
  Submodule.span ℤ {x | ∃ v w, G.Adj v w ∧ x = edge v w}

 theorem edge_mem_incidenceSpan {v w : V} (h : G.Adj v w) : edge v w ∈ incidenceSpan G :=
  Submodule.subset_span ⟨v, w, h, rfl⟩

/-- A path gives an integral, not merely rational, endpoint difference. -/
theorem walk_edge_mem {v w : V} (p : G.Walk v w) : edge v w ∈ incidenceSpan G := by
  induction p with
  | nil => simpa [edge] using (incidenceSpan G).zero_mem
  | @cons u v w h p ih =>
    have he : edge u w = edge u v + edge v w := by
      ext i
      simp only [edge, Pi.sub_apply, Pi.add_apply]
      ring
    rw [he]
    exact (incidenceSpan G).add_mem (edge_mem_incidenceSpan G h) ih

 theorem reachable_edge_mem {v w : V} (h : G.Reachable v w) : edge v w ∈ incidenceSpan G :=
  h.elim (walk_edge_mem G)

/-- Equality with the usual graph incidence lattice, including every
connected component and every isolated vertex. -/
theorem incidenceSpan_eq_balanced : incidenceSpan G = balanced G.connectedComponentMk := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨v, w, h, rfl⟩
    exact edge_mem G.connectedComponentMk (SimpleGraph.ConnectedComponent.sound h.reachable)
  · intro x hx
    let y : balanced G.connectedComponentMk := ⟨x, hx⟩
    have he : x = (balanced G.connectedComponentMk).subtype
        (lift G.connectedComponentMk (graphRoot G) (graphRoot_component G)
          (drop G.connectedComponentMk (graphRoot G) y)) := by
      exact (congrArg (balanced G.connectedComponentMk).subtype
        (lift_drop G.connectedComponentMk (graphRoot G) (graphRoot_component G) y)).symm
    rw [he]
    unfold lift
    rw [map_sum]
    apply (incidenceSpan G).sum_mem
    intro i _
    rw [map_smul]
    apply (incidenceSpan G).smul_mem
    apply reachable_edge_mem G
    apply SimpleGraph.ConnectedComponent.exact
    exact (graphRoot_component G (G.connectedComponentMk i.val)).symm

/-- The actual integer edge span is free, with one coordinate for each
non-root vertex of every connected component. -/
def incidenceCoordinates : incidenceSpan G ≃ₗ[ℤ]
    (FreeVertex G.connectedComponentMk (graphRoot G) → ℤ) :=
  (LinearEquiv.ofEq _ _ (incidenceSpan_eq_balanced G)).trans
    (coordinates G.connectedComponentMk (graphRoot G) (graphRoot_component G))

#print axioms graphRoot_component
#print axioms walk_edge_mem
#print axioms incidenceSpan_eq_balanced
#print axioms incidenceCoordinates

end Unimodular.GraphicRootedLattice

#check Unimodular.GraphicRootedLattice.incidenceSpan_eq_balanced
