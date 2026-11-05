module

public import PaperVerification.AlternatingFormsFrobenius
public import PaperVerification.AlternatingFormsDuality
public import Mathlib.Data.Finset.Card

/-!
# Complementary-degree division by a matching quadratic

A high-degree exterior monomial has more full matching pairs than empty
ones. Keep all empty pairs and exactly one more full pair. On this odd
subuniverse the explicit Boolean inverse applies; every omitted pair meets
the remaining word and therefore annihilates it. This proves division in
prime characteristic using only the factorial of one plus the number of
empty pairs, without imposing a condition on the ambient cardinality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype ι] [DecidableEq ι]

/-- Extract any specified subcollection of a selection as a list
permutation, retaining every multiplicity. -/
theorem selection_split_off_permutation (A C : Finset ι) (hCA : C ⊆ A) :
    A.toList.Perm ((A \ C).toList ++ C.toList) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_append, A.nodup_toList.count, (A \ C).nodup_toList.count,
    C.nodup_toList.count]
  by_cases hiC : i ∈ C
  · simp [hiC, hCA hiC]
  · by_cases hiA : i ∈ A <;> simp [hiC, hiA]

/-- Extracting the same pair labels from both halves produces actual
adjacent exterior pairs after a permutation. -/
theorem selected_pair_word_permutation (u v : ι → M) (A B C : Finset ι)
    (hCA : C ⊆ A) (hCB : C ⊆ B) :
    (A.toList.map u ++ B.toList.map v).Perm
      (((A \ C).toList.map u ++ (B \ C).toList.map v) ++
        C.toList.flatMap (fun i => [u i, v i])) := by
  have h₁ := ((selection_split_off_permutation A C hCA).map u).append
    ((selection_split_off_permutation B C hCB).map v)
  simp only [List.map_append] at h₁
  have h₂ :
      (((A \ C).toList.map u ++ C.toList.map u) ++
        ((B \ C).toList.map v ++ C.toList.map v)).Perm
      (((A \ C).toList.map u ++ (B \ C).toList.map v) ++
        (C.toList.map u ++ C.toList.map v)) := by
    simpa only [List.append_assoc] using
      (((List.perm_append_comm (l₁ := C.toList.map u)
        (l₂ := (B \ C).toList.map v)).append_left
          ((A \ C).toList.map u)).append_right (C.toList.map v))
  have h₃ : (C.toList.map u ++ C.toList.map v).Perm
      (C.toList.flatMap fun i => [u i, v i]) := by
    simpa only [← List.map_eq_flatMap, List.cons_append, List.nil_append] using
      List.flatMap_append_perm C.toList (fun i => [u i]) (fun i => [v i])
  exact h₁.trans (h₂.trans (h₃.append_left _))

/-- Division of every high-degree selection, with exactly the factorial
needed by its empty matching pairs. The vectors need not be independent. -/
theorem matching_high_selection_division_of_factorial
    (u v : ι → M) (A B : Finset ι)
    (hhigh : Fintype.card ι + 1 ≤ A.card + B.card)
    (hfac : ((((A ∪ B)ᶜ).card + 1).factorial : K) ≠ 0) :
    ∃ η : ⋀[K]^(A.card + B.card - 2) M,
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
          (η : ExteriorAlgebra K M) =
        ((A.toList.map u ++ B.toList.map v).map (ExteriorAlgebra.ι K)).prod := by
  classical
  let E : Finset ι := (A ∪ B)ᶜ
  let r := E.card
  have hbalance : (A ∪ B).card + E.card = Fintype.card ι := by
    simpa only [E, Finset.card_univ] using Finset.card_add_card_compl (A ∪ B)
  have hfull : r + 1 ≤ (A ∩ B).card := by
    have hc := Finset.card_union_add_card_inter A B
    dsimp [r]
    omega
  obtain ⟨C, hC, hCc⟩ := Finset.exists_subset_card_eq hfull
  have hCA : C ⊆ A := hC.trans Finset.inter_subset_left
  have hCB : C ⊆ B := hC.trans Finset.inter_subset_right
  have hEC : Disjoint E C := by
    apply Finset.disjoint_left.mpr
    intro i hiE hiC
    exact (Finset.mem_compl.mp hiE) (Finset.mem_union_left _ (hCA hiC))
  let H := E ∪ C
  let S := Hᶜ
  let L := (A \ C).toList.map u ++ (B \ C).toList.map v
  have hH : H.card = 2 * r + 1 := by
    dsimp [H]
    rw [Finset.card_union_of_disjoint hEC, hCc]
    dsimp [r]
    omega
  have hfree : Fintype.card {i : ι // i ∉ S} = 2 * r + 1 := by
    let e : {i : ι // i ∉ S} ≃ H :=
      Equiv.subtypeEquivRight (fun i => by simp only [S, Finset.mem_compl, not_not])
    rw [Fintype.card_congr e, Fintype.card_coe, hH]
  have hCP : ∀ i ∈ C, i ∉ S := by
    intro i hi
    simp only [S, Finset.mem_compl, not_not]
    exact Finset.mem_union_right E hi
  let P : FixedSubsets {i : ι // i ∉ S} (r + 1) :=
    ⟨C.subtype (fun i => i ∉ S), by
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr hCP, hCc]⟩
  have hL : ∀ i ∈ S, u i ∈ L ∨ v i ∈ L := by
    intro i hi
    have hiH : i ∉ H := Finset.mem_compl.mp hi
    have hiE : i ∉ E := fun he => hiH (Finset.mem_union_left _ he)
    have hiC : i ∉ C := fun hc => hiH (Finset.mem_union_right _ hc)
    have hiAB : i ∈ A ∪ B := by
      simpa only [E, Finset.mem_compl, not_not] using hiE
    rcases Finset.mem_union.mp hiAB with hiA | hiB
    · exact Or.inl (List.mem_append_left _ (List.mem_map.mpr
        ⟨i, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hiA, hiC⟩), rfl⟩))
    · exact Or.inr (List.mem_append_right _ (List.mem_map.mpr
        ⟨i, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hiB, hiC⟩), rfl⟩))
  obtain ⟨η, hη⟩ := singleton_state_division_exists_of_factorial
    (K := K) u v S L hL r hfac hfree P
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K)
    (selected_pair_word_permutation u v A B C hCA hCB)
  have hlen : L.length + 2 * r = A.card + B.card - 2 := by
    have h₁ := Finset.card_le_card hCA
    have h₂ := Finset.card_le_card hCB
    simp only [L, List.length_append, List.length_map, Finset.length_toList,
      Finset.card_sdiff_of_subset hCA, Finset.card_sdiff_of_subset hCB]
    omega
  refine ⟨⟨ε • (η : ExteriorAlgebra K M), ?_⟩, ?_⟩
  · rw [← hlen]
    exact Submodule.smul_mem _ _ η.property
  · rw [mul_smul_comm, hη]
    have hpair := pairedMonomial_subtype (K := K) hCP u v
    change ε • ((L.map (ExteriorAlgebra.ι K)).prod *
      pairedMonomial _ _ (C.subtype fun i => i ∉ S)) = _
    rw [hpair]
    simpa only [List.map_append, List.prod_append, pair_word_product, L] using heq.symm

/-- The prime-characteristic specialization has no restriction on the
ambient number of pairs: only the number of empty pairs is bounded. -/
theorem matching_high_selection_division_charP
    (u v : ι → M) (A B : Finset ι)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hhigh : Fintype.card ι + 1 ≤ A.card + B.card)
    (hempty : ((A ∪ B)ᶜ).card + 1 < p) :
    ∃ η : ⋀[K]^(A.card + B.card - 2) M,
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
          (η : ExteriorAlgebra K M) =
        ((A.toList.map u ++ B.toList.map v).map (ExteriorAlgebra.ι K)).prod :=
  matching_high_selection_division_of_factorial u v A B hhigh
    (factorial_cast_ne_zero_of_lt_char p _ hempty)

end PaperVerification.AlternatingForms
