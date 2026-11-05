module

public import higher_specht.verified.normal_form02

/- Generated ordinary proof stage. See audit/staged_specht_normal_form/NormalForm03/manifest.json. -/

@[expose] public section

section CanonicalSource20
/- Source: HigherSpecht/SemistandardKnuthNormalForm.lean -/



/-!
# The Knuth normal form for Mathlib semistandard tableaux

This file identifies the literal row word used by the Lascoux construction
with the row list used by Schensted insertion.  Consequently two such row
words in the same Knuth class have the same actual shape and every entry
agrees.  The result permits repeated letters and does not use a recording
tableau, standardization, or a count of tableaux.
-/

noncomputable section

open TauCeti

namespace HigherSpecht.Lascoux

variable {mu nu : YoungDiagram}

def semistandardRows (T : SemistandardYoungTableau mu) : List (List ℕ) :=
  (List.range (mu.colLen 0)).map (tableauRowWord T)

@[simp] theorem tableauRowWord_length (T : SemistandardYoungTableau mu) (r : ℕ) :
    (tableauRowWord T r).length = mu.rowLen r := by
  simp only [tableauRowWord, tableauRowSegment_length, Nat.sub_zero]

@[simp] theorem tableauRowWord_getElem (T : SemistandardYoungTableau mu)
    (r j : ℕ) (hj : j < (tableauRowWord T r).length) :
    (tableauRowWord T r)[j] = T r j := by
  simp only [tableauRowWord, tableauRowSegment, List.getElem_map,
    List.getElem_range', Nat.mul_one, Nat.one_mul, Nat.zero_add]

theorem tableauRowWord_sorted (T : SemistandardYoungTableau mu) (r : ℕ) :
    (tableauRowWord T r).SortedLE := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [tableauRowWord_getElem, tableauRowWord_getElem]
  exact T.row_weak hij (YoungDiagram.mem_iff_lt_rowLen.mpr
    (by simpa only [tableauRowWord_length] using hj))

theorem tableauRowWord_isRowAbove (T : SemistandardYoungTableau mu)
    {r s : ℕ} (hrs : r < s) :
    (tableauRowWord T r).IsRowAbove (tableauRowWord T s) := by
  refine ⟨by simpa only [tableauRowWord_length] using mu.rowLen_anti r s hrs.le, ?_⟩
  intro j hr hs
  rw [tableauRowWord_getElem, tableauRowWord_getElem]
  exact T.col_strict hrs (YoungDiagram.mem_iff_lt_rowLen.mpr
    (by simpa only [tableauRowWord_length] using hs))

@[simp] theorem semistandardRows_length (T : SemistandardYoungTableau mu) :
    (semistandardRows T).length = mu.colLen 0 := by simp [semistandardRows]

@[simp] theorem semistandardRows_getElem (T : SemistandardYoungTableau mu)
    (r : ℕ) (hr : r < (semistandardRows T).length) :
    (semistandardRows T)[r] = tableauRowWord T r := by
  simp only [semistandardRows, List.getElem_map, List.getElem_range]

theorem semistandardRows_isTableau (T : SemistandardYoungTableau mu) :
    (semistandardRows T).IsTableauRows := by
  refine ⟨?_, ?_, ?_⟩
  · intro hnil
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hnil
    have hr0 : (r, 0) ∈ mu := YoungDiagram.mem_iff_lt_colLen.mpr
      (List.mem_range.mp hr)
    have hp : 0 < mu.rowLen r := YoungDiagram.mem_iff_lt_rowLen.mp hr0
    have hz := congrArg List.length heq
    simp only [tableauRowWord_length, List.length_nil] at hz
    omega
  · intro row hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    exact tableauRowWord_sorted T r
  · rw [List.isChain_iff_getElem]
    intro r hr
    rw [semistandardRows_getElem, semistandardRows_getElem]
    exact tableauRowWord_isRowAbove T (Nat.lt_succ_self r)

theorem tableauWord_eq_rowWordRows (T : SemistandardYoungTableau mu) :
    tableauWord T = rowWordRows (semistandardRows T) := by
  simp only [tableauWord, descendingRows_eq_reverse_range, rowWordRows,
    semistandardRows, List.map_reverse, List.flatMap_def]

theorem semistandardRows_map_length (T : SemistandardYoungTableau mu) :
    (semistandardRows T).map List.length = mu.rowLens := by
  simp only [semistandardRows, List.map_map, YoungDiagram.rowLens,
    Function.comp_def, tableauRowWord_length]

theorem semistandardRows_getD (T : SemistandardYoungTableau mu) (r : ℕ) :
    (semistandardRows T).getD r [] = tableauRowWord T r := by
  by_cases hr : r < mu.colLen 0
  · have hr' : r < (semistandardRows T).length := by
      simpa only [semistandardRows_length] using hr
    rw [List.getD_eq_getElem (semistandardRows T) [] hr',
      semistandardRows_getElem]
  · have hlen : mu.rowLen r = 0 := by
      by_contra h
      have hp : 0 < mu.rowLen r := Nat.pos_of_ne_zero h
      have hc := YoungDiagram.mem_iff_lt_colLen.mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr hp : (r, 0) ∈ mu)
      exact hr hc
    have hr' : (semistandardRows T).length ≤ r := by
      simpa only [semistandardRows_length] using Nat.le_of_not_gt hr
    rw [List.getD_eq_default (semistandardRows T) [] hr']
    simp only [tableauRowWord, tableauRowSegment, hlen, Nat.sub_zero,
      List.range'_zero, List.map_nil]

theorem tableauRowWord_getD (T : SemistandardYoungTableau mu) (r j : ℕ) :
    (tableauRowWord T r).getD j 0 = T r j := by
  by_cases hj : j < mu.rowLen r
  · have hj' : j < (tableauRowWord T r).length := by
      simpa only [tableauRowWord_length] using hj
    rw [List.getD_eq_getElem (tableauRowWord T r) 0 hj',
      tableauRowWord_getElem]
  · have hj' : (tableauRowWord T r).length ≤ j := by
      simpa only [tableauRowWord_length] using Nat.le_of_not_gt hj
    rw [List.getD_eq_default (tableauRowWord T r) 0 hj',
      T.zeros (by simpa only [YoungDiagram.mem_iff_lt_rowLen] using hj)]

/-- Insertion reconstructs the literal semistandard tableau row word. -/
theorem insertionRows_tableauWord (T : SemistandardYoungTableau mu) :
    (tableauWord T).foldl (fun rows x => rowInsert x rows) [] = semistandardRows T := by
  rw [tableauWord_eq_rowWordRows]
  exact fold_rowInsert_rowWordRows _ (semistandardRows_isTableau T)

theorem semistandardRows_eq_of_knuth_tableauWord
    (T : SemistandardYoungTableau mu) (U : SemistandardYoungTableau nu)
    (h : KnuthEquivalent (tableauWord T) (tableauWord U)) :
    semistandardRows T = semistandardRows U := by
  have hi := h.insertionRows_eq
  rwa [insertionRows_tableauWord T, insertionRows_tableauWord U] at hi

/-- Equality of the original shapes, not merely equality of their sizes. -/
theorem shape_eq_of_knuth_tableauWord
    (T : SemistandardYoungTableau mu) (U : SemistandardYoungTableau nu)
    (h : KnuthEquivalent (tableauWord T) (tableauWord U)) : mu = nu := by
  have hrows := semistandardRows_eq_of_knuth_tableauWord T U h
  have hlengths := congrArg (List.map List.length) hrows
  rw [semistandardRows_map_length, semistandardRows_map_length] at hlengths
  exact YoungDiagram.equivListRowLens.injective (Subtype.ext hlengths)

theorem entries_eq_of_knuth_tableauWord
    (T : SemistandardYoungTableau mu) (U : SemistandardYoungTableau nu)
    (h : KnuthEquivalent (tableauWord T) (tableauWord U)) :
    ∀ r j, T r j = U r j := by
  intro r j
  have hrows := semistandardRows_eq_of_knuth_tableauWord T U h
  have he := congrArg (fun rows : List (List ℕ) => (rows.getD r []).getD j 0) hrows
  simpa only [semistandardRows_getD, tableauRowWord_getD] using he

/-- The actual semistandard Knuth normal form is unique, including its
shape.  `HEq` expresses equality across the two initially distinct shapes. -/
theorem semistandard_knuth_normal_form_unique
    (T : SemistandardYoungTableau mu) (U : SemistandardYoungTableau nu)
    (h : KnuthEquivalent (tableauWord T) (tableauWord U)) : mu = nu ∧ HEq T U := by
  have hshape := shape_eq_of_knuth_tableauWord T U h
  subst nu
  refine ⟨rfl, ?_⟩
  exact heq_of_eq (SemistandardYoungTableau.ext (entries_eq_of_knuth_tableauWord T U h))

theorem tableauWord_knuth_iff_eq (T U : SemistandardYoungTableau mu) :
    KnuthEquivalent (tableauWord T) (tableauWord U) ↔ T = U := by
  constructor
  · intro h
    exact SemistandardYoungTableau.ext (entries_eq_of_knuth_tableauWord T U h)
  · rintro rfl
    exact .refl _

end HigherSpecht.Lascoux
end
end CanonicalSource20
