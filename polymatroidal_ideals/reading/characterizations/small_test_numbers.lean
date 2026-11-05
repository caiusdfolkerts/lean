import Characterizations.SmallCases
import Mathlib.Data.Fintype.Perm

/-! # The exact zero-, one-, and six-test small cases -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem variableOrder_card : Fintype.card (VariableOrder V) = (Fintype.card V).factorial :=
  Fintype.card_equiv (Fintype.equivFin V)

theorem finalPair_card_three_values (hcard : Fintype.card V = 3)
    {o : VariableOrder V} {i j : V} (hij : i ≠ j) (h : FinalPair o i j) :
    (o i).val = 1 ∧ (o j).val = 2 ∧ ∀ x, x ≠ i → x ≠ j → (o x).val = 0 := by
  obtain ⟨q,_,hq⟩ := exists_mem_notMem_of_card_lt_card
    (show ({i,j} : Finset V).card < (univ : Finset V).card by simp [hij,hcard])
  have hqi : q ≠ i := fun he => hq (by simp [he])
  have hqj : q ≠ j := fun he => hq (by simp [he])
  have hlt1 := h.1
  have hlt0 := h.2 q hqi hqj
  have hiBound := (o i).isLt
  have hjBound := (o j).isLt
  have hqBound := (o q).isLt
  change (o i).val < (o j).val at hlt1
  change (o q).val < (o i).val at hlt0
  refine ⟨by omega, by omega, ?_⟩
  intro x hxi hxj
  have hh := h.2 x hxi hxj
  change (o x).val < (o i).val at hh
  omega

theorem finalPair_unique_card_three (hcard : Fintype.card V = 3)
    {o o' : VariableOrder V} {i j : V} (hij : i ≠ j)
    (h : FinalPair o i j) (h' : FinalPair o' i j) : o = o' := by
  obtain ⟨hi,hj,hrest⟩ := finalPair_card_three_values hcard hij h
  obtain ⟨hi',hj',hrest'⟩ := finalPair_card_three_values hcard hij h'
  ext x
  by_cases hxi : x = i
  · subst x; omega
  by_cases hxj : x = j
  · subst x; omega
  rw [hrest x hxi hxj,hrest' x hxi hxj]

theorem order_has_finalPair_card_three (hcard : Fintype.card V = 3) (o : VariableOrder V) :
    ∃ i j : V, i ≠ j ∧ FinalPair o i j := by
  let i := o.symm ⟨1,by omega⟩
  let j := o.symm ⟨2,by omega⟩
  have hi : (o i).val = 1 := by simp [i]
  have hj : (o j).val = 2 := by simp [j]
  have hij : i ≠ j := by intro he; rw [he] at hi; omega
  refine ⟨i,j,hij,?_,?_⟩
  · change (o i).val < (o j).val
    omega
  · intro x hxi hxj
    have hni : (o x).val ≠ 1 := fun he => hxi (o.injective (Fin.ext (he.trans hi.symm)))
    have hnj : (o x).val ≠ 2 := fun he => hxj (o.injective (Fin.ext (he.trans hj.symm)))
    have hb := (o x).isLt
    change (o x).val < (o i).val
    omega

theorem degree_tests_card_three_iff_univ {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) (F : Finset (VariableOrder V)) :
    DegreeOrderTests k d (F : Set (VariableOrder V)) ↔ F = univ := by
  constructor
  · intro htest
    apply eq_univ_of_forall
    intro o
    by_contra hn
    obtain ⟨i,j,hij,hfinal⟩ := order_has_finalPair_card_three hcard o
    let c : Exponent V := Finsupp.single i (d-2)
    have hbase : Equigenerated (pairFamily i j) 2 := by simpa [hcard] using pairFamily_equigenerated i j
    have hcdeg : c.degree = d-2 := by simp only [c,Finsupp.degree_single]
    have hgen : Equigenerated (translatedFamily c (pairFamily i j)) d := by
      have hh := translatedFamily_equigenerated hbase c
      have he : 2+c.degree = d := by omega
      exact he ▸ hh
    have hp := htest _ hgen (fun o' ho' =>
      (translatedFamily_linearQuotients_iff hbase c o').mpr
        (pairFamily_linearQuotients_of_not_final hij o' (fun hf =>
          hn ((finalPair_unique_card_three hcard hij hf hfinal) ▸ ho'))))
    exact pairFamily_not_polymatroidal hij (by omega)
      ((translatedFamily_polymatroidal_iff hbase c).mp hp)
  · rintro rfl B hB hL
    exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ o))

theorem degree_test_number_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) (F : Finset (VariableOrder V))
    (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) : F.card = 6 := by
  rw [(degree_tests_card_three_iff_univ hcard d hd F).mp hF,card_univ,variableOrder_card,hcard]
  norm_num

theorem empty_tests_of_small_degree {k : Type*} [CommSemiring k]
    (d : ℕ) (hd : d ≤ 1) : DegreeOrderTests k d (∅ : Set (VariableOrder V)) := by
  intro B hB _
  exact equigenerated_polymatroidal_of_degree_le_one hB hd

theorem empty_tests_of_small_dimension {k : Type*} [CommSemiring k]
    (hcard : Fintype.card V ≤ 1) : UniversalOrderTests k (∅ : Set (VariableOrder V)) := by
  intro B d hB _
  exact equigenerated_polymatroidal_of_card_le_one hB hcard

theorem degree_tests_card_two_iff_nonempty {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 2) (d : ℕ) (hd : 2 ≤ d) (F : Set (VariableOrder V)) :
    DegreeOrderTests k d F ↔ F.Nonempty := by
  constructor
  · intro htest
    by_contra hn
    obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (by omega : 2 ≤ Fintype.card V)
    apply purePair_not_polymatroidal hd hij
    exact htest _ (purePair_equigenerated d i j) (fun o ho => False.elim (hn ⟨o,ho⟩))
  · intro hne B hB hL
    obtain ⟨o,ho⟩ := hne
    exact one_order_suffices_card_two hB (by omega) o (hL o ho)

end Characterizations
