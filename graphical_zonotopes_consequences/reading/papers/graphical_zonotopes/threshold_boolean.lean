module

public import Papers.GraphicalZonotopes.BookModuleGeometry
public import Papers.GraphicalZonotopes.ExactlyOneExpansion

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The threshold module of Lemma 7.6. Counting the whole set in the second
disjunct is equivalent to counting the hubs other than `a`: the first
disjunct already makes the value one whenever `a` is present. -/
def thresholdStar (a : H) : SetFunction H :=
  fun S => if a∈S ∨ 2≤S.card then 1 else 0

theorem thresholdStar_literal (a : H) (S : Finset H) :
    thresholdStar a S=if a∈S ∨ 2≤(S.erase a).card then 1 else 0 := by
  by_cases ha : a∈S
  · simp only [thresholdStar,ha,true_or,ite_true]
  · simp only [thresholdStar,ha,false_or,erase_eq_of_notMem ha]

theorem thresholdStar_boolean (a : H) : IsMonotoneBoolean (thresholdStar a) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hS : a∈S ∨ 2≤S.card
    · have hT : a∈T ∨ 2≤T.card := by
        rcases hS with ha | hc
        · exact Or.inl (hST ha)
        · exact Or.inr (hc.trans (card_le_card hST))
      simp only [thresholdStar,if_pos hS,if_pos hT,le_refl]
    · by_cases hT : a∈T ∨ 2≤T.card <;>
        simp only [thresholdStar,if_neg hS,hT,ite_true,ite_false] <;> norm_num
  · intro S
    by_cases hS : a∈S ∨ 2≤S.card <;> simp only [thresholdStar,hS,ite_true,ite_false] <;> simp
  · simp [thresholdStar]
  · simp [thresholdStar]

theorem thresholdStar_eq_zero_iff (a : H) (S : Finset H) :
    thresholdStar a S=0 ↔ a∉S ∧ S.card<2 := by
  by_cases ha : a∈S
  · simp [thresholdStar,ha]
  · by_cases hc : 2≤S.card
    · simp [thresholdStar,ha,hc,Nat.not_lt.mpr hc]
    · have hlt : S.card<2:=Nat.lt_of_not_ge hc
      simp [thresholdStar,ha,hc,hlt]

theorem thresholdStar_eq_one_iff (a : H) (S : Finset H) :
    thresholdStar a S=1 ↔ a∈S ∨ 2≤S.card := by
  by_cases h : a∈S ∨ 2≤S.card <;> simp only [thresholdStar,h,ite_true,ite_false] <;> norm_num

/-- Essentiality is witnessed by literal Boolean covers, including all
ambient hubs rather than only the distinguished one. -/
theorem thresholdStar_essential (hs : 3≤Fintype.card H) (a i : H) :
    Essential (thresholdStar a) i := by
  by_cases hi : i=a
  · subst i
    refine ⟨∅,notMem_empty _,?_⟩
    simp [thresholdStar]
  · have hb : ∃ b : H,b≠a ∧ b≠i := by
      by_contra hn
      have hsub : (univ : Finset H)⊆{a,i} := by
        intro b hb
        by_cases hba : b=a
        · simp only [hba,mem_insert_self]
        · by_cases hbi : b=i
          · simp only [hbi,mem_insert,mem_singleton,or_true]
          · exact False.elim (hn ⟨b,hba,hbi⟩)
      have hc:=card_le_card hsub
      rw [card_univ,card_pair (Ne.symm hi)] at hc
      omega
    obtain ⟨b,hba,hbi⟩:=hb
    refine ⟨{b},by simpa only [mem_singleton] using Ne.symm hbi,?_⟩
    have hai : a≠i:=Ne.symm hi
    have hab : a≠b:=Ne.symm hba
    simp only [thresholdStar,mem_insert,mem_singleton,hai,hab,false_or,
      card_pair (Ne.symm hbi),card_singleton]
    norm_num

/-- Every actual pair response is the exactly-one indicator on its context,
with the distinguished hub excluded. The formula also covers pairs incident
with `a`, since their legitimate contexts already omit `a`. -/
theorem thresholdStar_negativeResponse (a : H) {u v : H} (huv : u≠v)
    (S : Finset H) (hu : u∉S) (hv : v∉S) :
    negativeResponse (thresholdStar a) u v S=
      if a∈S then 0 else exactlyOne S := by
  have hone : negativeResponse (thresholdStar a) u v S=1 ↔ a∉S ∧ S.card=1 := by
    rw [negativeResponse_eq_one_iff (thresholdStar_boolean a),
      thresholdStar_eq_zero_iff,thresholdStar_eq_one_iff,thresholdStar_eq_one_iff]
    simp only [mem_insert,card_insert_of_notMem hu,card_insert_of_notMem hv]
    constructor
    · rintro ⟨⟨ha,hc⟩,hu',hv'⟩
      refine ⟨ha,?_⟩
      by_cases hpos : 1≤S.card
      · omega
      · have hau : a=u := by
          rcases hu' with (hau | haS) | hcard
          · exact hau
          · exact False.elim (ha haS)
          · omega
        have hav : a=v := by
          rcases hv' with (hav | haS) | hcard
          · exact hav
          · exact False.elim (ha haS)
          · omega
        exact False.elim (huv (hau.symm.trans hav))
    · rintro ⟨ha,hc⟩
      exact ⟨⟨ha,by omega⟩,Or.inr (by omega),Or.inr (by omega)⟩
  rcases negativeResponse_values (thresholdStar_boolean a) u v S with hz | ho
  · have hn : ¬(a∉S ∧ S.card=1) := by
      intro h
      have hh:=hone.mpr h
      rw [hz] at hh
      norm_num at hh
    by_cases ha : a∈S
    · simp only [hz,if_pos ha]
    · have hc : S.card≠1:=fun h => hn ⟨ha,h⟩
      simp only [hz,if_neg ha,exactlyOne,if_neg hc]
  · obtain ⟨ha,hc⟩:=hone.mp ho
    simp only [ho,if_neg ha,exactlyOne,if_pos hc]

end BooleanModule
end GraphicalZonotopes
