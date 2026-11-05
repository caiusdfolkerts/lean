module

public import GraphGrowthRuleSoundness
public import FacetCapacityBounds
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Vertex-capacity soundness for graph-conditioned growth

This module connects the natural-number masks used by the finite checker
with the finite-set incidence inequality.  The available mask may contain
extra cells, and it may overlap the selected family.  Neither possibility
invalidates the upper bound.
-/

namespace Papers.RationalityTen.GraphGrowthConstraints

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open scoped BigOperators

variable {n r e v k : Nat}

private def kindIndex (D : Problem n r e v k) (c : Fin n) : Fin k :=
  ⟨D.kind c, D.kind_lt c⟩

private theorem filter_card (L : List (Fin n)) (hL : L.Nodup)
    (p : Fin n → Bool) :
    (L.toFinset.filter fun c => p c = true).card = (L.filter p).length := by
  have hset : L.toFinset.filter (fun c => p c = true) =
      (L.filter p).toFinset := by
    ext c
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter]
  rw [hset, List.toFinset_card_of_nodup (hL.filter p)]

private theorem vertex_card (D : Problem n r e v k)
    (L : List (Fin n)) (hL : L.Nodup) (a : Fin v) :
    (L.toFinset.filter fun c => (D.vertexRows a).testBit c.val = true).card =
      vertexCount D L a :=
  filter_card L hL _

private theorem kind_card (D : Problem n r e v k)
    (L : List (Fin n)) (hL : L.Nodup) (j : Fin k) :
    (L.toFinset.filter fun c => kindIndex D c = j).card =
      kindCount D.kind L j.val := by
  have hset : L.toFinset.filter (fun c => kindIndex D c = j) =
      L.toFinset.filter (fun c => decide (D.kind c = j.val) = true) := by
    ext c
    simp only [Finset.mem_filter, decide_eq_true_eq, Fin.ext_iff, kindIndex]
  rw [hset, filter_card L hL]
  rfl

private theorem available_kind_vertex_card (D : Problem n r e v k)
    (available : Nat) (j : Fin k) (a : Fin v) :
    ((FiniteMaskSets.elements n available).toFinset.filter
      fun c => kindIndex D c = j ∧ (D.vertexRows a).testBit c.val = true).card =
      FiniteMaskSets.card n
        (Nat.land available (Nat.land (D.cache.kinds j.val) (D.vertexRows a))) := by
  have hset : (FiniteMaskSets.elements n available).toFinset.filter
      (fun c => kindIndex D c = j ∧ (D.vertexRows a).testBit c.val = true) =
      (FiniteMaskSets.elements n
        (Nat.land available (Nat.land (D.cache.kinds j.val) (D.vertexRows a)))).toFinset := by
    ext c
    simp only [Finset.mem_filter, List.mem_toFinset, FiniteMaskSets.mem_elements,
      FiniteMaskSets.testBit_land, Bool.and_eq_true_iff, D.kind_exact,
      decide_eq_true_eq, Fin.ext_iff, kindIndex]
  rw [hset, List.toFinset_card_of_nodup (FiniteMaskSets.elements_nodup _ _)]
  rfl

/-- Every graph-growth problem has a sound vertex-capacity rule.  All inputs
of the finite-set counting theorem follow from the target and availability
conditions already enforced by the search checker. -/
theorem vertexCapacitySound (D : Problem n r e v k) : VertexCapacitySound D := by
  intro S B available hB hS hsub havailable a
  have hST : S.toFinset ⊆ B.toFinset := by
    intro c hc
    exact List.mem_toFinset.mpr
      (list_subset_of_included S B hsub (List.mem_toFinset.mp hc))
  have hA : B.toFinset \ S.toFinset ⊆
      (FiniteMaskSets.elements n available).toFinset := by
    intro c hc
    obtain ⟨hcB, hcS⟩ := Finset.mem_sdiff.mp hc
    apply List.mem_toFinset.mpr
    apply (FiniteMaskSets.mem_elements c).mpr
    exact havailable c (List.mem_toFinset.mp hcB)
      (fun h => hcS (List.mem_toFinset.mpr h))
  have hQ (j : Fin k) :
      (B.toFinset.filter fun c => kindIndex D c = j).card ≤ D.quota j.val := by
    rw [kind_card D B hB.nodup, hB.exactQuota]
  have h := FacetCapacityBounds.local_incidence_capacity (kindIndex D)
    (fun c a => (D.vertexRows a).testBit c.val = true)
    S.toFinset B.toFinset (FiniteMaskSets.elements n available).toFinset
    (fun j => D.quota j.val) hST hA hQ a
  rw [vertex_card D B hB.nodup, vertex_card D S hS] at h
  have hsum :
      (∑ j : Fin k, min
        (D.quota j.val - (S.toFinset.filter fun c => kindIndex D c = j).card)
        (((FiniteMaskSets.elements n available).toFinset.filter fun c =>
          kindIndex D c = j ∧ (D.vertexRows a).testBit c.val = true).card)) =
      ((List.finRange k).map fun j =>
        min (D.quota j.val - kindCount D.kind S j.val)
          (FiniteMaskSets.card n
            (Nat.land available (Nat.land (D.cache.kinds j.val) (D.vertexRows a))))).sum := by
    rw [← Fin.sum_univ_def]
    apply Finset.sum_congr rfl
    intro j _
    rw [kind_card D S hS, available_kind_vertex_card]
  rw [hsum] at h
  exact h

#print axioms vertexCapacitySound

end Papers.RationalityTen.GraphGrowthConstraints
