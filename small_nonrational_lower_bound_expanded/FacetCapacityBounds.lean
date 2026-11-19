module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-!
# Necessary incidence-capacity inequalities for finite boundary growth

`S` is a selected partial family, `T` is the complete target, and `A`
contains every still-missing target cell. The local bound accounts for
both remaining kind quotas and the number of available cells incident to
a vertex. The global bound double-counts all vertex-cell incidences.
Neither statement requires `S` and `A` to be disjoint.
-/

namespace Papers.RationalityTen.FacetCapacityBounds

open Finset
open scoped BigOperators

variable {C K V : Type*} [DecidableEq C] [Fintype K] [DecidableEq K]

/-- Splitting off an already selected subfamily splits every filtered count. -/
theorem filter_card_decomposition (S T : Finset C) (hST : S ⊆ T)
    (p : C → Prop) [DecidablePred p] :
    (S.filter p).card + ((T \ S).filter p).card = (T.filter p).card := by
  have hsub : S.filter p ⊆ T.filter p := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨hST (Finset.mem_filter.mp hc).1,
      (Finset.mem_filter.mp hc).2⟩
  have hdiff : (T \ S).filter p = T.filter p \ S.filter p := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hcT, hcS⟩, hp⟩
      exact ⟨⟨hcT, hp⟩, fun h => hcS h.1⟩
    · rintro ⟨⟨hcT, hp⟩, hn⟩
      exact ⟨⟨hcT, fun hcS => hn ⟨hcS, hp⟩⟩, hp⟩
  rw [hdiff, Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- Partition a finite family by its kind, with arbitrary natural weights. -/
theorem sum_kind_weights (T : Finset C) (kind : C → K) (weight : K → ℕ) :
    (∑ k, (T.filter fun c => kind c = k).card * weight k) =
      ∑ c ∈ T, weight (kind c) := by
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using Finset.sum_fiberwise' T kind weight

/-- The complete family is partitioned by kind even after restricting to
one vertex's incidences. -/
theorem sum_kind_incidence (T : Finset C) (kind : C → K)
    (Inc : C → V → Prop) [∀ c v, Decidable (Inc c v)] (v : V) :
    (∑ k, (T.filter fun c => kind c = k ∧ Inc c v).card) =
      (T.filter fun c => Inc c v).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (T.filter fun c => Inc c v) (Finset.univ : Finset K) kind
  simpa only [Finset.filter_filter, Finset.mem_univ, Finset.filter_true,
    and_comm, true_and] using h

/-- Every full target incidence count is bounded by the selected incidences
plus the available, quota-limited contribution of each kind. -/
theorem local_incidence_capacity (kind : C → K) (Inc : C → V → Prop)
    [∀ c v, Decidable (Inc c v)] (S T A : Finset C) (Q : K → ℕ)
    (hST : S ⊆ T) (havailable : T \ S ⊆ A)
    (hquota : ∀ k, (T.filter fun c => kind c = k).card ≤ Q k) (v : V) :
    (T.filter fun c => Inc c v).card ≤
      (S.filter fun c => Inc c v).card +
        ∑ k, min (Q k - (S.filter fun c => kind c = k).card)
          ((A.filter fun c => kind c = k ∧ Inc c v).card) := by
  have hkind (k : K) :
      ((T \ S).filter fun c => kind c = k ∧ Inc c v).card ≤
        min (Q k - (S.filter fun c => kind c = k).card)
          ((A.filter fun c => kind c = k ∧ Inc c v).card) := by
    apply le_min
    · have hsub : ((T \ S).filter fun c => kind c = k ∧ Inc c v) ⊆
          ((T \ S).filter fun c => kind c = k) := by
        intro c hc
        obtain ⟨hc, hk, _⟩ := Finset.mem_filter.mp hc
        exact Finset.mem_filter.mpr ⟨hc, hk⟩
      have hle := Finset.card_le_card hsub
      have hsplit := filter_card_decomposition S T hST (fun c => kind c = k)
      have hbound := hquota k
      have hsum : ((T \ S).filter fun c => kind c = k).card +
          (S.filter fun c => kind c = k).card ≤ Q k := by
        rw [Nat.add_comm, hsplit]
        exact hbound
      exact hle.trans (Nat.le_sub_of_add_le hsum)
    · apply Finset.card_le_card
      intro c hc
      obtain ⟨hc, hkind⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨havailable hc, hkind⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hkind k)
  rw [sum_kind_incidence] at hsum
  rw [← filter_card_decomposition S T hST (fun c => Inc c v)]
  exact Nat.add_le_add_left hsum _

/-- An impossible local capacity certifies that the proposed partial
family cannot extend to any target satisfying the stated geometric bounds. -/
theorem local_capacity_contradiction (kind : C → K) (Inc : C → V → Prop)
    [∀ c v, Decidable (Inc c v)] (S T A : Finset C) (Q : K → ℕ)
    (hST : S ⊆ T) (havailable : T \ S ⊆ A)
    (hquota : ∀ k, (T.filter fun c => kind c = k).card ≤ Q k)
    (v : V) (lower : ℕ) (hdegree : lower ≤ (T.filter fun c => Inc c v).card)
    (hcut : (S.filter fun c => Inc c v).card +
      ∑ k, min (Q k - (S.filter fun c => kind c = k).card)
        ((A.filter fun c => kind c = k ∧ Inc c v).card) < lower) : False :=
  Nat.not_lt_of_ge (hdegree.trans
    (local_incidence_capacity kind Inc S T A Q hST havailable hquota v)) hcut

/-- Double-counting all incidences supplies a global pruning inequality.
The bound `lower` is five for nonsimple vertices of four-polytopes. -/
theorem global_incidence_capacity [Fintype V] (kind : C → K)
    (Inc : C → V → Prop) [∀ c v, Decidable (Inc c v)]
    (S T : Finset C) (Q size : K → ℕ) (lower : ℕ)
    (hST : S ⊆ T) (hdegree : ∀ v, lower ≤ (T.filter fun c => Inc c v).card)
    (hquota : ∀ k, (T.filter fun c => kind c = k).card ≤ Q k)
    (hsize : ∀ c ∈ T, ((Finset.univ : Finset V).filter (Inc c)).card = size (kind c)) :
    (∑ v, max lower ((S.filter fun c => Inc c v).card)) ≤ ∑ k, Q k * size k := by
  have hdouble : (∑ v, (T.filter fun c => Inc c v).card) =
      ∑ c ∈ T, ((Finset.univ : Finset V).filter (Inc c)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  calc
    _ ≤ ∑ v, (T.filter fun c => Inc c v).card := by
      apply Finset.sum_le_sum
      intro v _
      apply max_le (hdegree v)
      apply Finset.card_le_card
      intro c hc
      exact Finset.mem_filter.mpr ⟨hST (Finset.mem_filter.mp hc).1,
        (Finset.mem_filter.mp hc).2⟩
    _ = ∑ c ∈ T, ((Finset.univ : Finset V).filter (Inc c)).card := hdouble
    _ = ∑ c ∈ T, size (kind c) := Finset.sum_congr rfl hsize
    _ = ∑ k, (T.filter fun c => kind c = k).card * size k :=
      (sum_kind_weights T kind size).symm
    _ ≤ ∑ k, Q k * size k :=
      Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right (size k) (hquota k)

end Papers.RationalityTen.FacetCapacityBounds
