module

public import PaperVerification.FermionNewtonSupportedExpansion

/-!
# The initial constant block before a strict multiplicity jump

The block is an actual initial coordinate embedding. Its Newton columns
coincide with the constant-profile columns and vanish in every row outside
the block. Compatibility also proves that all signs inside the block are
nonpositive whenever a strict jump follows it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L : Type*} [Field L] {m n : ℕ}

def prefixEmbedding (hm : m ≤ n) : Fin m ↪ Fin n :=
  ⟨Fin.castLE hm, Fin.castLE_injective hm⟩

@[simp] theorem prefixEmbedding_val (hm : m ≤ n) (i : Fin m) :
    (prefixEmbedding hm i).val = i.val := rfl

@[simp] theorem mem_range_prefixEmbedding (hm : m ≤ n) (i : Fin n) :
    i ∈ Set.range (prefixEmbedding hm) ↔ i.val < m := by
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem earlierPositive_prefix (hm : m ≤ n) (σ : Fin n → ℤ) (i : Fin m) :
    earlierPositive σ (prefixEmbedding hm i) =
      (earlierPositive (σ ∘ prefixEmbedding hm) i).map (prefixEmbedding hm) := by
  ext k
  constructor
  · intro hk
    rcases (mem_earlierPositive σ _ k).mp hk with ⟨hki, hkσ⟩
    have hkm : k.val < m := lt_trans hki i.isLt
    refine Finset.mem_map.mpr ⟨⟨k.val, hkm⟩, ?_, Fin.ext rfl⟩
    exact (mem_earlierPositive _ _ _).mpr ⟨hki, hkσ⟩
  · intro hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
    rcases (mem_earlierPositive (σ ∘ prefixEmbedding hm) i j).mp hj with ⟨hji,hjσ⟩
    exact (mem_earlierPositive σ _ _).mpr ⟨hji,hjσ⟩

theorem earlierNegative_prefix (hm : m ≤ n) (σ : Fin n → ℤ) (i : Fin m) :
    earlierNegative σ (prefixEmbedding hm i) =
      (earlierNegative (σ ∘ prefixEmbedding hm) i).map (prefixEmbedding hm) := by
  ext k
  constructor
  · intro hk
    rcases (mem_earlierNegative σ _ k).mp hk with ⟨hki, hkσ⟩
    have hkm : k.val < m := lt_trans hki i.isLt
    refine Finset.mem_map.mpr ⟨⟨k.val, hkm⟩, ?_, Fin.ext rfl⟩
    exact (mem_earlierNegative _ _ _).mpr ⟨hki, hkσ⟩
  · intro hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
    rcases (mem_earlierNegative (σ ∘ prefixEmbedding hm) i j).mp hj with ⟨hji,hjσ⟩
    exact (mem_earlierNegative σ _ _).mpr ⟨hji,hjσ⟩

theorem activeInterval_prefix (hm : m < n) (δ : Fin n → ℕ) (d : ℕ)
    (hδ : ∀ k, k.val < m → δ k = d) (hjump : d < δ ⟨m, hm⟩) (i : Fin m) :
    activeInterval δ (prefixEmbedding hm.le i) = (activeTail i).map (prefixEmbedding hm.le) := by
  ext k
  constructor
  · intro hk
    rcases (mem_activeInterval _ _ _).mp hk with ⟨hik, hbetween⟩
    have hkm : k.val < m := by
      by_contra hnot
      have hj := hbetween ⟨m, hm⟩ i.isLt (Nat.le_of_not_gt hnot)
      rw [hδ (prefixEmbedding hm.le i) i.isLt] at hj
      exact (not_le_of_gt hjump) hj
    refine Finset.mem_map.mpr ⟨⟨k.val, hkm⟩, ?_, Fin.ext rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩
  · intro hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
    refine (mem_activeInterval _ _ _).mpr ⟨(Finset.mem_filter.mp hj).2, ?_⟩
    intro k hik hkj
    have hkm : k.val < m := lt_of_le_of_lt hkj j.isLt
    rw [hδ k hkm, hδ _ i.isLt]

theorem profileNewtonMatrix_prefix_block
    (hm : m < n) (δ : Fin n → ℕ) (d : ℕ) (σ : Fin n → ℤ) (x β : Fin n → L)
    (hδ : ∀ k, k.val < m → δ k = d) (hjump : d < δ ⟨m, hm⟩) :
    (profileNewtonMatrix δ σ x β).submatrix (prefixEmbedding hm.le) (prefixEmbedding hm.le) =
      profileNewtonMatrix (fun _ ↦ d) (σ ∘ prefixEmbedding hm.le)
        (x ∘ prefixEmbedding hm.le) (β ∘ prefixEmbedding hm.le) := by
  ext k i
  change rationalColumn _ _ _ _ _ _ = rationalColumn _ _ _ _ _ _
  rw [activeInterval_prefix hm δ d hδ hjump, earlierNegative_prefix,
    activeInterval_constant_eq_activeTail]
  have hN : profileNumerator δ σ x (prefixEmbedding hm.le i) =
      profileNumerator (fun _ ↦ d) (σ ∘ prefixEmbedding hm.le)
        (x ∘ prefixEmbedding hm.le) i := by
    rw [profileNumerator, hδ _ i.isLt, earlierPositive_prefix, nodal_map_embedding]
    rfl
  rw [hN]
  exact rationalColumn_map_embedding (prefixEmbedding hm.le) _ _ _ x β k

theorem profileNewtonMatrix_prefix_support
    (hm : m < n) (δ : Fin n → ℕ) (d : ℕ) (σ : Fin n → ℤ) (x β : Fin n → L)
    (hδ : ∀ k, k.val < m → δ k = d) (hjump : d < δ ⟨m, hm⟩)
    (k : Fin n) (hk : k ∉ Set.range (prefixEmbedding hm.le)) (i : Fin m) :
    profileNewtonMatrix δ σ x β k (prefixEmbedding hm.le i) = 0 := by
  have hnactive : k ∉ activeInterval δ (prefixEmbedding hm.le i) := by
    rw [activeInterval_prefix hm δ d hδ hjump]
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp h
    exact hk ⟨j, he⟩
  have hnpoles : k ∉ earlierNegative σ (prefixEmbedding hm.le i) := by
    rw [earlierNegative_prefix]
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp h
    exact hk ⟨j, he⟩
  simp only [profileNewtonMatrix, rationalColumn, if_neg hnactive, if_neg hnpoles]

theorem compatible_prefix_no_positive
    (hm : m < n) (δ : Fin n → ℕ) (d : ℕ) (σ : Fin n → ℤ)
    (hc : Compatible δ σ)
    (hδ : ∀ k, k.val < m → δ k = d) (hjump : d < δ ⟨m, hm⟩) :
    ∀ i, i.val < m → σ i ≠ 1 := by
  intro i hi hσ
  have h := hc.1 i ⟨m, hm⟩ hi hσ
  rw [hδ i hi] at h
  exact (not_le_of_gt hjump) h

theorem earlierPositive_eq_empty_in_initial_block
    (σ : Fin n → ℤ) (m : ℕ) (hσ : ∀ i, i.val < m → σ i ≠ 1)
    (i : Fin n) (hi : i.val < m) : earlierPositive σ i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  rcases (mem_earlierPositive σ i j).mp hj with ⟨hji, hjσ⟩
  exact hσ j (lt_trans hji hi) hjσ

/-- The first strict jump supplies the exact initial constant block. -/
theorem exists_initial_constant_block
    (δ : Fin n → ℕ) (d : ℕ)
    (hmin : ∀ i, d ≤ δ i) (hstrict : ∃ i, d < δ i) :
    ∃ m : ℕ, ∃ hm : m < n,
      (∀ i, i.val < m → δ i = d) ∧ d < δ ⟨m, hm⟩ := by
  let U := Finset.univ.filter (fun i ↦ d < δ i)
  have hU : U.Nonempty := by
    obtain ⟨i, hi⟩ := hstrict
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let b := U.min' hU
  have hb : d < δ b := (Finset.mem_filter.mp (Finset.min'_mem U hU)).2
  refine ⟨b.val, b.isLt, ?_, hb⟩
  intro i hi
  apply le_antisymm _ (hmin i)
  by_contra hnot
  have him : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_of_not_ge hnot⟩
  exact (not_le_of_gt hi) (Finset.min'_le U i him)

end PaperVerification.Fermion.Newton
