module

public import PaperVerification.SeparatedSubsets
import Lean.Elab.Tactic.Omega

/-!
# Counting the odd pencil's coordinate fixed planes

The Jordan-chain order is `b₀, …, bₖ, aₖ, …, a₁`. The two alternating
forms pair distinct coordinates whose indices sum to `2k` or `2k + 1`.
Interleaving the two halves turns those edges into the ordinary path
`b₀, a₁, b₁, …, aₖ, bₖ`. This file proves the reindexing and the complete
binomial count, including the empty subset and the maximal independent subset.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.OddPathIndependent

open SeparatedSubsets

/-- The index in Jordan-chain order of a vertex in alternating path order. -/
def pathToChain (k : ℕ) (i : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  if i.val % 2 = 0 then ⟨i.val / 2, by have := i.isLt; omega⟩
  else ⟨2 * k - i.val / 2, by omega⟩

/-- The path index of a vector in Jordan-chain order. -/
def chainToPath (k : ℕ) (i : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  if h : i.val ≤ k then ⟨2 * i.val, by omega⟩
  else ⟨2 * (2 * k - i.val) + 1, by have := i.isLt; omega⟩

theorem chainToPath_pathToChain (k : ℕ) (i : Fin (2 * k + 1)) :
    chainToPath k (pathToChain k i) = i := by
  apply Fin.ext
  have hi := i.isLt
  by_cases hp : i.val % 2 = 0
  · have hq : i.val / 2 ≤ k := by omega
    simp [pathToChain, hp, chainToPath, hq] <;> omega
  · have hq : ¬ (2 * k - i.val / 2 ≤ k) := by omega
    simp [pathToChain, hp, chainToPath, hq] <;> omega

theorem pathToChain_chainToPath (k : ℕ) (i : Fin (2 * k + 1)) :
    pathToChain k (chainToPath k i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [chainToPath, pathToChain]
  split_ifs <;> dsimp only at * <;> omega

/-- The actual reordering of the two bases. -/
def pathChainEquiv (k : ℕ) : Fin (2 * k + 1) ≃ Fin (2 * k + 1) where
  toFun := pathToChain k
  invFun := chainToPath k
  left_inv := chainToPath_pathToChain k
  right_inv := pathToChain_chainToPath k

/-- The two anti-diagonals become exactly the consecutive edges of the path.
The distinctness clause removes the diagonal middle entry, as alternation does. -/
theorem chain_edge_iff_path_adjacent (k : ℕ) (i j : Fin (2 * k + 1)) :
    (i ≠ j ∧ ((pathToChain k i).val + (pathToChain k j).val = 2 * k ∨
      (pathToChain k i).val + (pathToChain k j).val = 2 * k + 1)) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [ne_eq, Fin.ext_iff, pathToChain]
  split_ifs <;> simp only [Fin.val_mk] <;> omega

/-- The original coordinate condition, expressed on a finite subset. -/
def ChainIndependent (k : ℕ) (S : Finset (Fin (2 * k + 1))) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i = j ∨
    (i.val + j.val ≠ 2 * k ∧ i.val + j.val ≠ 2 * k + 1)

/-- A coordinate subset of a fixed dimension, with the actual two isotropy
conditions on each pair of distinct basis vectors. -/
abbrev CoordinateSubsets (k s : ℕ) :=
  {S : Finset (Fin (2 * k + 1)) // S.card = s ∧ ChainIndependent k S}

theorem chainIndependent_map_iff (k : ℕ) (S : Finset (Fin (2 * k + 1))) :
    ChainIndependent k (S.map (pathChainEquiv k).toEmbedding) ↔
      ∀ i ∈ S, ∀ j ∈ S, i < j → i.val + 2 ≤ j.val := by
  constructor
  · intro h i hi j hj hij
    have hne : i ≠ j := ne_of_lt hij
    have hpi : pathToChain k i ∈ S.map (pathChainEquiv k).toEmbedding :=
      Finset.mem_map.mpr ⟨i, hi, rfl⟩
    have hpj : pathToChain k j ∈ S.map (pathChainEquiv k).toEmbedding :=
      Finset.mem_map.mpr ⟨j, hj, rfl⟩
    have he := h _ hpi _ hpj
    have hpne : pathToChain k i ≠ pathToChain k j :=
      fun hp => hne ((pathChainEquiv k).injective hp)
    have hz : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      intro hbad
      have hedge := (chain_edge_iff_path_adjacent k i j).mpr hbad
      rcases he with he | he
      · exact hpne he
      · exact hedge.2.elim he.1 he.2
    change i.val < j.val at hij
    omega
  · intro h i hi j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hj
    by_cases hab : a = b
    · exact Or.inl (congrArg (pathToChain k) hab)
    · right
      have hn : ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · have hg := h a ha b hb hlt
          change a.val < b.val at hlt
          omega
        · have hg := h b hb a ha hgt
          change b.val < a.val at hgt
          omega
      have he := (chain_edge_iff_path_adjacent k a b).not.mpr hn
      constructor
      · intro hz
        exact he ⟨hab, Or.inl hz⟩
      · intro hz
        exact he ⟨hab, Or.inr hz⟩

/-- Reordering the actual coordinate subsets gives precisely path-independent
subsets of the same cardinality. -/
def coordinateEquivIndependent (k s : ℕ) :
    CoordinateSubsets k s ≃ Independent (2 * k + 1) s where
  toFun S := ⟨S.val.map (pathChainEquiv k).symm.toEmbedding, by
    constructor
    · simpa only [Finset.card_map] using S.property.1
    · apply (chainIndependent_map_iff k _).mp
      simpa only [Finset.map_map, Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,
        Finset.map_refl] using S.property.2⟩
  invFun S := ⟨S.val.map (pathChainEquiv k).toEmbedding, by
    constructor
    · simpa only [Finset.card_map] using S.property.1
    · exact (chainIndependent_map_iff k S.val).mpr S.property.2⟩
  left_inv S := by
    apply Subtype.ext
    simp only [Finset.map_map, Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,
      Finset.map_refl]
  right_inv S := by
    apply Subtype.ext
    simp only [Finset.map_map, Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding,
      Finset.map_refl]

/-- The exact number of isotropic coordinate `s`-planes in an odd pencil. -/
theorem card_coordinateSubsets (k s : ℕ) (hs : s ≤ k + 1) :
    Nat.card (CoordinateSubsets k s) = (2 * k + 2 - s).choose s := by
  rw [Nat.card_congr (coordinateEquivIndependent k s), card_independent]
  omega

end PaperVerification.OddPathIndependent
