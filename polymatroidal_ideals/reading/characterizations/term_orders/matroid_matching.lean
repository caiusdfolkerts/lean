import CommAlg.Polymatroid.CloneMatroid
import Mathlib.Combinatorics.Hall.Finite

/-! # One-sided matching of two actual matroid bases

The Hall condition follows from the fundamental circuits and the rank inequality.
Every matched exchange is feasible at the same original base.
-/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.TermOrders
open Classical Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma matroid_basis_matching (M : Matroid α) (A B : Finset α)
    (hA : M.IsBase (A : Set α)) (hB : M.IsBase (B : Set α)) :
    ∃ f : A ≃ B, ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α) := by
  let t : A → Finset B := fun x => univ.filter (fun y => y.val ∈ M.fundCircuit x.val (B : Set α))
  have hhall : ∀ S : Finset A, S.card ≤ (S.biUnion t).card := by
    intro S
    let T : Finset α := S.image Subtype.val
    let N : Finset α := (S.biUnion t).image Subtype.val
    have hTA : (T : Set α) ⊆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact y.property
    have hNB : (N : Set α) ⊆ B := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact y.property
    have hTN : (T : Set α) ⊆ M.closure (N : Set α) := by
      intro x hx
      obtain ⟨x, hxS, rfl⟩ := mem_image.mp hx
      by_cases hxB : x.val ∈ B
      · apply M.subset_closure _ (hNB.trans hB.subset_ground)
        exact mem_image.mpr ⟨⟨x.val, hxB⟩, mem_biUnion.mpr ⟨x, hxS,
          mem_filter.mpr ⟨mem_univ _, M.mem_fundCircuit _ _⟩⟩, rfl⟩
      · have hC := hB.fundCircuit_isCircuit (hA.subset_ground x.property) hxB
        apply M.closure_subset_closure (show M.fundCircuit x.val (B : Set α) \ {x.val} ⊆ (N : Set α) from ?_)
          (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit _ _))
        intro y hy
        have hyB : y ∈ B := by
          rcases M.fundCircuit_subset_insert x.val (B : Set α) hy.1 with h | h
          · exact False.elim (hy.2 h)
          · exact h
        exact mem_image.mpr ⟨⟨y, hyB⟩, mem_biUnion.mpr ⟨x, hxS,
          mem_filter.mpr ⟨mem_univ _, hy.1⟩⟩, rfl⟩
    have hcard : T.card ≤ N.card := by
      have hh := (hA.indep.subset hTA).encard_le_eRk_of_subset hTN
      rw [M.eRk_closure_eq] at hh
      have hh' := hh.trans (M.eRk_le_encard (N : Set α))
      exact_mod_cast hh'
    simpa only [T, N, card_image_of_injective _ Subtype.coe_injective] using hcard
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  have hcard : Fintype.card A = Fintype.card B := by
    have h := hA.encard_eq_encard_of_isBase hB
    simpa only [Fintype.card_coe, Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj] using h
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩), ?_⟩
  intro x
  exact (mem_filter.mp (hft x)).2

lemma matroid_matching_fixes_common (M : Matroid α) (A B : Finset α)
    (f : A ≃ B) (hf : ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α))
    (x : A) (hx : x.val ∈ B) : (f x).val = x.val := by
  have h := hf x
  rw [M.fundCircuit_eq_of_mem hx] at h
  exact h

lemma matroid_matching_exchange (M : Matroid α) (A B : Finset α)
    (hA : M.IsBase (A : Set α)) (hB : M.IsBase (B : Set α))
    (f : A ≃ B) (hf : ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α))
    (x : A) (hx : x.val ∉ B) :
    (f x).val ∉ A ∧ M.IsBase (insert x.val ((B : Set α) \ {(f x).val})) := by
  have hfxA : (f x).val ∉ A := by
    intro hyA
    let y : A := ⟨(f x).val, hyA⟩
    have hy : (f y).val = y.val := matroid_matching_fixes_common M A B f hf y (f x).property
    have he : f y = f x := Subtype.ext hy
    have he' := f.injective he
    exact hx ((congrArg Subtype.val he') ▸ (show y.val ∈ B from (f x).property))
  refine ⟨hfxA, hB.exchange_isBase_of_indep hx ?_⟩
  have hI := (hB.indep.mem_fundCircuit_iff (by rw [hB.closure_eq]; exact hA.subset_ground x.property) hx).mp (hf x)
  have hne : x.val ≠ (f x).val := fun h => hx (h ▸ (f x).property)
  simpa only [Set.insert_sdiff_singleton_comm hne] using hI

end Characterizations.TermOrders
