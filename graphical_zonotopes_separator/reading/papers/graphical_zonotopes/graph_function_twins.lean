module

public import Papers.GraphicalZonotopes.Zonotope

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices with identical open neighborhoods have identical induced-edge
marginals in every subset avoiding them. -/
theorem graphFunction_insert_twins (G : SimpleGraph V) {u v : V}
    (htwin : ∀ w,G.Adj u w↔G.Adj v w) (S : Finset V) (hu : u∉S) (hv : v∉S) :
    graphFunction G (insert u S)=graphFunction G (insert v S) := by
  classical
  revert hu hv
  induction S using Finset.induction_on with
  | empty =>
    intro hu hv
    simp only [insert_empty_eq,(graphFunction_translationNormalized G).2]
  | @insert w S hw ih =>
    intro hu hv
    have huS : u∉S := fun h => hu (mem_insert_of_mem h)
    have hvS : v∉S := fun h => hv (mem_insert_of_mem h)
    have huw : u≠w := fun h => hu (by simp [h])
    have hvw : v≠w := fun h => hv (by simp [h])
    have h1 := graphFunction_delta G huw huS hw
    have h2 := graphFunction_delta G hvw hvS hw
    rw [htwin w] at h1
    have he := ih huS hvS
    unfold delta at h1 h2
    linarith

end GraphicalZonotopes
