module

public import PaperVerification.AlternatingFormsExteriorStraightening
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.BooleanAlgebra
import Lean.Elab.Tactic.Omega

/-!
# Factoring every prefix monomial into singleton and pair states

The paired-variable inverse keeps singly occupied pairs fixed.  This file
connects that inverse to arbitrary squarefree prefix monomials: two finite sets
record the selected first and second generators of each pair.  Reordering is
proved in the actual exterior algebra, and the occupancy identities supply the
odd universe size required by the Boolean inverse.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Reordering an exterior word changes it by a nonzero scalar.  This is proved
from adjacent transpositions, including the alternating sign at each swap. -/
theorem exterior_word_permutation {A B : List M} (h : A.Perm B) :
    ∃ ε : K, ε ≠ 0 ∧ (A.map (ExteriorAlgebra.ι K)).prod =
      ε • (B.map (ExteriorAlgebra.ι K)).prod := by
  induction h with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons a h ih =>
    obtain ⟨ε, hε, heq⟩ := ih
    refine ⟨ε, hε, ?_⟩
    simp only [List.map_cons, List.prod_cons, heq, mul_smul_comm]
  | swap a b L =>
    refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
    simp only [List.map_cons, List.prod_cons, neg_one_smul, ← mul_assoc]
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b a), neg_mul]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨ε, hε, heq⟩ := ih₁
    obtain ⟨δ, hδ, hdeq⟩ := ih₂
    exact ⟨ε * δ, mul_ne_zero hε hδ, by rw [heq, hdeq, mul_smul]⟩

/-- A list of explicit adjacent pairs multiplies to the product formed in the
center.  The equality retains the order within each individual pair. -/
theorem pair_word_product_list (u v : ι → M) (L : List ι) :
    ((L.flatMap fun i => [u i, v i]).map (ExteriorAlgebra.ι K)).prod =
      (((L.map fun i => exteriorPairCentral (K := K) (u i) (v i)).prod :
        Subalgebra.center K (ExteriorAlgebra K M)) : ExteriorAlgebra K M) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, ih,
      Subalgebra.coe_mul, exteriorPairCentral_coe, mul_assoc]

theorem pair_word_product [DecidableEq ι] (u v : ι → M) (P : Finset ι) :
    ((P.toList.flatMap fun i => [u i, v i]).map (ExteriorAlgebra.ι K)).prod =
      pairedMonomial u v P := by
  rw [pair_word_product_list, Finset.prod_map_toList]
  rfl

section Occupancy

variable [DecidableEq ι] [Fintype ι]

/-- Splitting a finite selection into its singleton and doubly occupied parts
is a genuine list permutation, with multiplicities verified. -/
theorem selection_split_permutation (A B : Finset ι) :
    A.toList.Perm ((A \ B).toList ++ (A ∩ B).toList) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_append, A.nodup_toList.count, (A \ B).nodup_toList.count,
    (A ∩ B).nodup_toList.count]
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
    simp [hiA, hiB]

/-- All singletons precede the remaining pairs after a permutation. -/
theorem singleton_pair_word_permutation {α : Type*} (u v : ι → α) (A B : Finset ι) :
    (A.toList.map u ++ B.toList.map v).Perm
      (((A \ B).toList.map u ++ (B \ A).toList.map v) ++
        (A ∩ B).toList.flatMap (fun i => [u i, v i])) := by
  have h₁ := ((selection_split_permutation A B).map u).append
    ((selection_split_permutation B A).map v)
  rw [Finset.inter_comm B A] at h₁
  simp only [List.map_append] at h₁
  have h₂ :
      (((A \ B).toList.map u ++ (A ∩ B).toList.map u) ++
        ((B \ A).toList.map v ++ (A ∩ B).toList.map v)).Perm
      (((A \ B).toList.map u ++ (B \ A).toList.map v) ++
        ((A ∩ B).toList.map u ++ (A ∩ B).toList.map v)) := by
    simpa only [List.append_assoc] using
      (((List.perm_append_comm (l₁ := (A ∩ B).toList.map u)
        (l₂ := (B \ A).toList.map v)).append_left
          ((A \ B).toList.map u)).append_right ((A ∩ B).toList.map v))
  have h₃ : ((A ∩ B).toList.map u ++ (A ∩ B).toList.map v).Perm
      ((A ∩ B).toList.flatMap fun i => [u i, v i]) := by
    simpa only [← List.map_eq_flatMap, List.cons_append, List.nil_append] using
      List.flatMap_append_perm (A ∩ B).toList (fun i => [u i]) (fun i => [v i])
  exact h₁.trans (h₂.trans (h₃.append_left _))

/-- The decomposition into singleton and pair states is proved for the actual
exterior product and includes the nonzero reordering scalar. -/
theorem exterior_monomial_singleton_pair_factorization (u v : ι → M) (A B : Finset ι) :
    ∃ ε : K, ε ≠ 0 ∧
      ((A.toList.map u ++ B.toList.map v).map (ExteriorAlgebra.ι K)).prod =
        ε • ((((A \ B).toList.map u ++ (B \ A).toList.map v).map
          (ExteriorAlgebra.ι K)).prod * pairedMonomial u v (A ∩ B)) := by
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K)
    (singleton_pair_word_permutation u v A B)
  refine ⟨ε, hε, ?_⟩
  simpa only [List.map_append, List.prod_append, pair_word_product] using heq

/-- The available pair universe has exactly the odd size used by the inverse
matrix.  This is the pigeonhole and degree calculation for every prefix size. -/
theorem prefix_occupancy_counts (A B : Finset ι)
    (hdegree : A.card + B.card = Fintype.card ι + 1) :
    0 < (A ∩ B).card ∧
      Fintype.card {i : ι // i ∉ (A \ B) ∪ (B \ A)} = 2 * ((A ∩ B).card - 1) + 1 ∧
      (A \ B).card + (B \ A).card + 2 * ((A ∩ B).card - 1) =
        Fintype.card ι - 1 := by
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  have hu := Finset.card_union_add_card_inter A B
  have hbound := Finset.card_le_univ (A ∪ B)
  have hdisjoint : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiA).2 (Finset.mem_sdiff.mp hiB).1
  have hcard : ((A \ B) ∪ (B \ A)).card = (A \ B).card + (B \ A).card :=
    Finset.card_union_of_disjoint hdisjoint
  rw [Fintype.card_subtype_compl, Fintype.card_coe, hcard]
  omega

theorem doublePairs_disjoint_singletons (A B : Finset ι) :
    ∀ i ∈ A ∩ B, i ∉ (A \ B) ∪ (B \ A) := by
  intro i hi hs
  obtain ⟨hiA, hiB⟩ := Finset.mem_inter.mp hi
  rcases Finset.mem_union.mp hs with hs | hs
  · exact (Finset.mem_sdiff.mp hs).2 hiB
  · exact (Finset.mem_sdiff.mp hs).2 hiA

theorem pairedMonomial_subtype {S P : Finset ι}
    (hP : ∀ i ∈ P, i ∉ S) (u v : ι → M) :
    pairedMonomial (fun i : {i : ι // i ∉ S} => u i.val)
      (fun i : {i : ι // i ∉ S} => v i.val) (P.subtype fun i => i ∉ S) =
        pairedMonomial (K := K) u v P := by
  unfold pairedMonomial
  congr 1
  exact Finset.prod_subtype_of_mem
    (fun i => exteriorPairCentral (K := K) (u i) (v i)) hP

/-- Lemma 3.1 for every squarefree selection in a `2h`-generator prefix,
with the singleton/pair factorization used to build its inverse.  The vectors
may be mapped into any larger ambient module. -/
theorem prefix_selection_division [CharZero K] (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card + B.card = Fintype.card ι + 1) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) M,
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) * η =
        ((A.toList.map u ++ B.toList.map v).map (ExteriorAlgebra.ι K)).prod := by
  classical
  let S := (A \ B) ∪ (B \ A)
  let L := (A \ B).toList.map u ++ (B \ A).toList.map v
  let n := (A ∩ B).card - 1
  have hcounts := prefix_occupancy_counts A B hdegree
  have hP := doublePairs_disjoint_singletons A B
  let P : FixedSubsets {i : ι // i ∉ S} (n + 1) :=
    ⟨(A ∩ B).subtype fun i => i ∉ S, by
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr hP]
      dsimp [n]
      omega⟩
  have hL : ∀ i ∈ S, u i ∈ L ∨ v i ∈ L := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Or.inl (List.mem_append_left _
        (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩))
    · exact Or.inr (List.mem_append_right _
        (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩))
  obtain ⟨η, hη⟩ := singleton_state_division_exists (K := K) u v S L hL n hcounts.2.1 P
  obtain ⟨ε, hε, heq⟩ := exterior_monomial_singleton_pair_factorization (K := K) u v A B
  have hlen : L.length + 2 * n = Fintype.card ι - 1 := by
    simpa only [L, n, List.length_append, List.length_map, Finset.length_toList] using
      hcounts.2.2
  refine ⟨⟨ε • (η : ExteriorAlgebra K M), ?_⟩, ?_⟩
  · rw [← hlen]
    exact Submodule.smul_mem _ _ η.property
  · rw [mul_smul_comm, hη]
    have hpair := pairedMonomial_subtype (K := K) hP u v
    change ε • ((L.map (ExteriorAlgebra.ι K)).prod *
      pairedMonomial _ _ ((A ∩ B).subtype fun i => i ∉ S)) = _
    rw [hpair]
    exact heq.symm

end Occupancy

end PaperVerification.AlternatingForms
