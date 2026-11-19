module
public import schur_tableau_bridge

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.Symmetric.Schur

/-- Padding a semistandard tableau with empty rows preserves row sorting. -/
theorem sortedLE_getD_of_isTableauRows {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (i : ℕ) : (rows.getD i []).SortedLE := by
  by_cases hi : i < rows.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hrows.sortedLE _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact List.sortedLE_nil

/-- The count of each entry in each row determines a semistandard tableau.
The nonempty-row convention is used to recover its number of rows. -/
theorem rows_eq_of_row_counts {rows other : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hother : other.IsTableauRows)
    (hcount : ∀ i a, (rows.getD i []).count a = (other.getD i []).count a) :
    rows = other := by
  have hrow (i : ℕ) : rows.getD i [] = other.getD i [] :=
    List.Perm.eq_of_sortedLE (sortedLE_getD_of_isTableauRows hrows i)
      (sortedLE_getD_of_isTableauRows hother i)
      (List.perm_iff_count.mpr (hcount i))
  have hlength : rows.length = other.length := by
    apply Nat.le_antisymm
    · by_contra h
      have hi : other.length < rows.length := Nat.lt_of_not_ge h
      have he := hrow other.length
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_default _ _ le_rfl] at he
      exact hrows.nil_notMem (he ▸ List.getElem_mem hi)
    · by_contra h
      have hi : rows.length < other.length := Nat.lt_of_not_ge h
      have he := hrow rows.length
      rw [List.getD_eq_default _ _ le_rfl, List.getD_eq_getElem _ _ hi] at he
      exact hother.nil_notMem (he.symm ▸ List.getElem_mem hi)
  apply List.ext_getElem hlength
  intro i hi hj
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hrow i

/-- Every entry in a padded row is an entry in the tableau. -/
theorem mem_flatten_of_mem_getD {α : Type*} {rows : List (List α)}
    {i : ℕ} {a : α} (ha : a ∈ rows.getD i []) : a ∈ rows.flatten := by
  by_cases hi : i < rows.length
  · rw [List.getD_eq_getElem _ _ hi] at ha
    exact List.mem_flatten.mpr ⟨_, List.getElem_mem hi, ha⟩
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)] at ha
    exact False.elim (List.not_mem_nil ha)

/-- For bounded tableaux, counts of labels in the finite alphabet suffice. -/
theorem evenTableau_eq_of_row_counts {n : ℕ} (T U : EvenSemistandardTableaux n)
    (hcount : ∀ (i : ℕ) (a : Fin n),
      (T.val.getD i []).count a.val = (U.val.getD i []).count a.val) : T = U := by
  apply Subtype.ext
  apply rows_eq_of_row_counts T.property.1 U.property.1
  intro i a
  by_cases ha : a < n
  · exact hcount i ⟨a, ha⟩
  · have hT : a ∉ T.val.getD i [] := fun h =>
      ha (T.property.2.2 a (mem_flatten_of_mem_getD h))
    have hU : a ∉ U.val.getD i [] := fun h =>
      ha (U.property.2.2 a (mem_flatten_of_mem_getD h))
    simp only [List.count_eq_zero.mpr hT, List.count_eq_zero.mpr hU]

/-- Finite row counts recover a tableau whenever all its rows have index
below `n`. Column strictness supplies these height bounds in applications. -/
theorem evenTableau_eq_of_finite_row_counts {n : ℕ} (T U : EvenSemistandardTableaux n)
    (hT : T.val.length ≤ n) (hU : U.val.length ≤ n)
    (hcount : ∀ (i a : Fin n),
      (T.val.getD i.val []).count a.val = (U.val.getD i.val []).count a.val) : T = U := by
  apply evenTableau_eq_of_row_counts T U
  intro i a
  by_cases hi : i < n
  · exact hcount ⟨i, hi⟩ a
  · rw [List.getD_eq_default _ _ (hT.trans (Nat.le_of_not_gt hi)),
      List.getD_eq_default _ _ (hU.trans (Nat.le_of_not_gt hi))]

end FourPapers.Symmetric.Schur

#print axioms FourPapers.Symmetric.Schur.evenTableau_eq_of_finite_row_counts
