module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# The six-label obstruction for ten tetrahedra

This is a finite lemma about an ordinary family of four-element subsets.
Every three-element subset must occur in either zero or two members.
The enumeration is evaluated by the Lean kernel through `decide`.
It does not assert that a polytope produces such a family; that geometric
construction is supplied separately.
-/

namespace Papers.SimpleFourFiniteObstruction

def tetrahedra : Finset (Finset (Fin 6)) :=
  (Finset.univ : Finset (Fin 6)).powersetCard 4

def triangles : Finset (Finset (Fin 6)) :=
  (Finset.univ : Finset (Fin 6)).powersetCard 3

def RidgeDegreeTwo (s : Finset (Finset (Fin 6))) : Prop :=
  ∀ r ∈ triangles,
    (s.filter (fun t => r ⊆ t)).card = 0 ∨
      (s.filter (fun t => r ⊆ t)).card = 2

instance (s : Finset (Finset (Fin 6))) : Decidable (RidgeDegreeTwo s) :=
  inferInstanceAs (Decidable (∀ r ∈ triangles,
    (s.filter (fun t => r ⊆ t)).card = 0 ∨
      (s.filter (fun t => r ⊆ t)).card = 2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_ten_tetrahedra :
    ∀ s ∈ tetrahedra.powersetCard 10, ¬ RidgeDegreeTwo s := by
  decide

theorem no_ten_of_pure (s : Finset (Finset (Fin 6)))
    (hpure : ∀ t ∈ s, t.card = 4) (hcard : s.card = 10)
    (hdeg : RidgeDegreeTwo s) : False := by
  have hsub : s ⊆ tetrahedra := by
    intro t ht
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ t, hpure t ht⟩
  exact no_ten_tetrahedra s (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩) hdeg

end Papers.SimpleFourFiniteObstruction
