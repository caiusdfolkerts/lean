module

public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A standard tree decomposition, with the usual vertex and edge coverage
and connected bag occurrence conditions. The width is maximum bag size minus
one. A natural-number index for the finite tree loses no finite decomposition. -/
def HasTreewidthAtMost (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ m : ℕ, ∃ T : SimpleGraph (Fin m), ∃ bag : Fin m → Finset V,
    T.IsTree ∧ (∀ i, (bag i).card ≤ w+1) ∧
    (∀ v, ∃ i, v ∈ bag i) ∧
    (∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i) ∧
    ∀ v, (T.induce {i | v ∈ bag i}).Connected


end GraphicalZonotopes
