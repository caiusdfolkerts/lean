module
public import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Papers.RationalityTen.ChirotopeDensity

/-- Three supports of size at most two whose pairwise unions have size four
are pairwise disjoint two-element sets, with six elements in total. -/
theorem three_pair_unions_four {α : Type*} [DecidableEq α]
    (A B C : Finset α) (hA : A.card ≤ 2) (hB : B.card ≤ 2) (hC : C.card ≤ 2)
    (hAB : (A ∪ B).card = 4) (hAC : (A ∪ C).card = 4)
    (hBC : (B ∪ C).card = 4) :
    A.card = 2 ∧ B.card = 2 ∧ C.card = 2 ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ (A ∪ B ∪ C).card = 6 := by
  have hABle := Finset.card_union_le A B
  have hACle := Finset.card_union_le A C
  have hA2 : A.card = 2 := by omega
  have hB2 : B.card = 2 := by omega
  have hC2 : C.card = 2 := by omega
  have hdAB : Disjoint A B := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    have h := Finset.card_union_add_card_inter A B
    omega
  have hdAC : Disjoint A C := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    have h := Finset.card_union_add_card_inter A C
    omega
  have hdBC : Disjoint B C := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    have h := Finset.card_union_add_card_inter B C
    omega
  refine ⟨hA2, hB2, hC2, hdAB, hdAC, hdBC, ?_⟩
  have hd : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hc
    rcases Finset.mem_union.mp hx with ha | hb
    · exact Finset.disjoint_left.mp hdAC ha hc
    · exact Finset.disjoint_left.mp hdBC hb hc
  rw [Finset.card_union_of_disjoint hd, hAB, hC2]

#print axioms three_pair_unions_four

end Papers.RationalityTen.ChirotopeDensity
