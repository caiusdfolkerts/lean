module
public import matching_row_bump

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingInsertionCore imports loaded"
  progressOutput.flush

/-! Row insertion, paired insertion, and exact first-row carrier processing.
These components share the accepted row-bumping foundation and have no
commutative-algebra or standard-tableau connectivity dependencies. -/

/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.Schensted.Basic -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Schensted row insertion into a tableau

A semistandard tableau is recorded here by its list of rows, from top to bottom: every row is
nonempty and weakly increasing, and each row sits on top of the next one, being at least as long
and strictly smaller in every column (`List.IsTableauRows`).

Row insertion `TauCeti.rowInsert x T` inserts the letter `x` into the first row by
`TauCeti.rowBump`; the letter bumped out of that row is inserted into the second row, and so on,
until a letter is appended at the end of a row (possibly a new row at the bottom). This is
Schensted's insertion `T ← x`, the step iterated by the Robinson--Schensted--Knuth
correspondence. Its basic properties are:

* the result is again a tableau (`List.IsTableauRows.rowInsert`);
* it has the letters of `T` together with `x` (`TauCeti.flatten_rowInsert_perm`);
* its shape is that of `T` with one cell added, at the end of the row
  `TauCeti.rowInsertIndex x T` (`TauCeti.length_getD_rowInsert`), and that cell is a corner
  (`TauCeti.length_getD_succ_rowInsertIndex_lt`).

Reverse insertion `TauCeti.reverseRowInsert k T` removes the last entry of row `k` and moves it
up by `TauCeti.reverseRowBump`, row by row, ejecting a letter from the first row. It undoes
insertion (`TauCeti.reverseRowInsert_rowInsert`), and conversely, from a corner of a tableau it
produces a tableau and a letter whose insertion recovers the original tableau with the new cell
at that corner (`TauCeti.rowInsert_reverseRowInsert`, `List.IsTableauRows.reverseRowInsert`).
So insertion is a bijection between pairs of a tableau and a letter, and tableaux with a chosen
corner (`TauCeti.rowInsertEquiv`). Iterating it over the letters of a word, and recording the
new cells, is the Robinson--Schensted--Knuth correspondence.

## Main definitions

* `List.IsRowAbove`: one row can sit directly on top of another in a semistandard tableau.
* `List.IsTableauRows`: the rows of a semistandard tableau.
* `TauCeti.appendToRow`: append a letter at the end of a given row of a list of rows.
* `TauCeti.dropLastOfRow`: remove the last letter of a given row of a list of rows.
* `TauCeti.rowInsert`: Schensted row insertion of a letter into a tableau.
* `TauCeti.rowInsertIndex`: the row in which row insertion adds its new cell.
* `TauCeti.reverseRowInsert`: reverse row insertion from the end of a given row.
* `TauCeti.rowInsertEquiv`: row insertion as a bijection onto tableaux with a chosen corner.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Sections 1.1 and 4.1.
* B. E. Sagan, *The Symmetric Group*, 2nd ed., Springer GTM 203 (2001), Section 3.1.
-/

section
namespace List

variable {α : Type*}

/-- The row `upper` can sit directly on top of the row `lower` in a semistandard tableau:
`lower` is no longer than `upper`, and each entry of `lower` is strictly greater than the entry
of `upper` above it. -/
structure IsRowAbove [LT α] (upper lower : List α) : Prop where
  /-- The lower row is no longer than the upper row. -/
  length_le : lower.length ≤ upper.length
  /-- Each entry of the lower row is strictly greater than the entry above it. -/
  getElem_lt : ∀ (j : ℕ) (hu : j < upper.length) (hl : j < lower.length), upper[j] < lower[j]

/-- Any row can sit on top of the empty row. -/
@[simp]
theorem isRowAbove_nil [LT α] (upper : List α) : upper.IsRowAbove [] :=
  ⟨by simp, fun _ _ hl => absurd hl (Nat.not_lt_zero _)⟩

/-- Lengthening the upper row keeps it on top of the lower row. -/
theorem IsRowAbove.append_right [LT α] {upper lower : List α} (h : upper.IsRowAbove lower)
    (extra : List α) : (upper ++ extra).IsRowAbove lower := by
  refine ⟨by simpa using h.length_le.trans (Nat.le_add_right _ _), fun j hu hl => ?_⟩
  rw [getElem_append_left (hl.trans_le h.length_le)]
  exact h.getElem_lt j _ hl

/-- Lengthening the lower row by an entry greater than the entry above it keeps the upper row on
top of it. -/
theorem IsRowAbove.append_singleton [LT α] {upper lower : List α} (h : upper.IsRowAbove lower)
    {a : α} (hlen : lower.length < upper.length) (ha : upper[lower.length] < a) :
    upper.IsRowAbove (lower ++ [a]) := by
  refine ⟨by simpa using Nat.succ_le_of_lt hlen, fun j hu hl => ?_⟩
  simp only [length_append, length_singleton] at hl
  rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
  · rw [getElem_append_left hl]
    exact h.getElem_lt j hu hl
  · simpa using ha

/-- If one row sits above a second, and the second above a third, the first sits above the
third. -/
theorem IsRowAbove.trans [LT α] [IsTrans α (· < ·)] {upper middle lower : List α}
    (h₁ : upper.IsRowAbove middle) (h₂ : middle.IsRowAbove lower) : upper.IsRowAbove lower :=
  ⟨h₂.length_le.trans h₁.length_le, fun j hu hl => IsTrans.trans _ _ _
    (h₁.getElem_lt j hu (hl.trans_le h₂.length_le)) (h₂.getElem_lt j _ hl)⟩

instance [LT α] [IsTrans α (· < ·)] : IsTrans (List α) IsRowAbove :=
  ⟨fun _ _ _ => IsRowAbove.trans⟩

/-- The rows, listed from top to bottom, of a semistandard tableau: every row is nonempty and
weakly increasing, and every row sits on top of the next one in the sense of `List.IsRowAbove`.
So the row lengths weakly decrease and the columns strictly increase. -/
structure IsTableauRows [Preorder α] (rows : List (List α)) : Prop where
  /-- No row is empty. -/
  nil_notMem : [] ∉ rows
  /-- Every row is weakly increasing. -/
  sortedLE : ∀ row ∈ rows, row.SortedLE
  /-- Every row sits on top of the next one. -/
  isChain : rows.IsChain IsRowAbove

variable [Preorder α]

/-- The empty tableau. -/
@[simp]
theorem isTableauRows_nil : IsTableauRows ([] : List (List α)) :=
  ⟨by simp, by simp, .nil⟩

/-- A tableau is a nonempty weakly increasing first row on top of a tableau. -/
theorem isTableauRows_cons {row : List α} {rows : List (List α)} :
    IsTableauRows (row :: rows) ↔ row ≠ [] ∧ row.SortedLE ∧ row.IsRowAbove (rows.headD []) ∧
      IsTableauRows rows := by
  constructor
  · rintro ⟨hne, hs, hc⟩
    rw [isChain_cons] at hc
    refine ⟨fun h => hne (h ▸ mem_cons_self), hs _ mem_cons_self, ?_,
      ⟨fun h => hne (mem_cons_of_mem _ h), fun r hr => hs r (mem_cons_of_mem _ hr), hc.2⟩⟩
    cases rows with
    | nil => exact isRowAbove_nil row
    | cons lower rows => exact hc.1 lower rfl
  · rintro ⟨hne, hs, habove, hrows⟩
    refine ⟨?_, ?_, isChain_cons.mpr ⟨?_, hrows.isChain⟩⟩
    · intro h
      rcases mem_cons.mp h with h | h
      · exact hne h.symm
      · exact hrows.nil_notMem h
    · simpa using ⟨hs, hrows.sortedLE⟩
    · cases rows with
      | nil => simp
      | cons lower rows => simpa using habove

/-- Deleting the first row of a tableau leaves a tableau. -/
theorem IsTableauRows.tail {row : List α} {rows : List (List α)}
    (h : IsTableauRows (row :: rows)) : IsTableauRows rows :=
  (isTableauRows_cons.mp h).2.2.2

/-- The row lengths of a tableau form a weakly decreasing list. -/
theorem IsTableauRows.sortedGE_map_length {rows : List (List α)} (h : IsTableauRows rows) :
    (rows.map List.length).SortedGE :=
  (isChain_map_of_isChain List.length (fun _ _ habove => habove.length_le) h.isChain).sortedGE

/-- The row lengths of a tableau weakly decrease. Rows beyond the last one are read as empty. -/
theorem IsTableauRows.length_getD_succ_le {rows : List (List α)} (h : IsTableauRows rows)
    (i : ℕ) : (rows.getD (i + 1) []).length ≤ (rows.getD i []).length := by
  induction rows generalizing i with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨-, -, habove, hrows⟩ := isTableauRows_cons.mp h
    cases i with
    | zero =>
      cases rows with
      | nil => simp
      | cons lower rows => simpa using habove.length_le
    | succ i => simpa using ih hrows i

/-- Each row of a tableau sits on top of the next one. Rows beyond the last one are read as
empty. -/
theorem IsTableauRows.isRowAbove_getD {rows : List (List α)} (h : IsTableauRows rows) (i : ℕ) :
    (rows.getD i []).IsRowAbove (rows.getD (i + 1) []) := by
  induction rows generalizing i with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨-, -, habove, hrows⟩ := isTableauRows_cons.mp h
    cases i with
    | zero =>
      cases rows with
      | nil => simp
      | cons lower rows => simpa using habove
    | succ i => simpa using ih hrows i

/-- At a corner of the first row of a tableau, a first row with a single entry is the whole
tableau: the row below it is empty. -/
theorem IsTableauRows.eq_nil_of_dropLast_eq_nil {row : List α} {rows : List (List α)}
    (h : (row :: rows).IsTableauRows) (hk : (rows.getD 0 []).length < row.length)
    (hd : row.dropLast = []) : rows = [] := by
  obtain ⟨-, -, -, hrows⟩ := isTableauRows_cons.mp h
  cases rows with
  | nil => rfl
  | cons lower rows =>
    have h1 := congrArg length hd
    rw [length_dropLast, length_nil] at h1
    have := length_pos_iff.mpr (isTableauRows_cons.mp hrows).1
    simp at hk
    omega

/-- In a nonempty tableau whose largest entry is `a`, the highest row ending in `a` ends in a
corner: the row below it is strictly shorter. -/
theorem IsTableauRows.length_getD_succ_lt_of_getLast?_eq_some {rows : List (List α)}
    (h : rows.IsTableauRows) {a : α} (hmax : ∀ x ∈ rows.flatten, x ≤ a) {k : ℕ}
    (hk : (rows.getD k []).getLast? = some a) :
    (rows.getD (k + 1) []).length < (rows.getD k []).length := by
  obtain ⟨ys, hys⟩ := getLast?_eq_some_iff.mp hk
  by_contra hcon
  have hlen : ys.length < (rows.getD (k + 1) []).length := by
    rw [hys, length_append, length_singleton] at hcon
    omega
  have hlt := (h.isRowAbove_getD k).getElem_lt ys.length (by rw [hys]; simp) hlen
  have hx := hmax _ (mem_flatten_of_mem_getD (getElem_mem hlen))
  simp only [hys, getElem_append_right le_rfl, Nat.sub_self, getElem_singleton] at hlt
  exact absurd (hlt.trans_le hx) (lt_irrefl a)

end List

namespace List

variable {α : Type*} [PartialOrder α]

/-- In a tableau, the largest entry ends some row. -/
theorem IsTableauRows.exists_getLast?_getD_eq_some {rows : List (List α)} (h : rows.IsTableauRows)
    {a : α} (ha : a ∈ rows.flatten) (hmax : ∀ x ∈ rows.flatten, x ≤ a) :
    ∃ i, (rows.getD i []).getLast? = some a := by
  obtain ⟨row, hrow, har⟩ := mem_flatten.mp ha
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem hrow
  refine ⟨i, ?_⟩
  rw [getD_eq_getElem?_getD, getElem?_eq_getElem hi, Option.getD_some]
  obtain hnil | ⟨ys, z, hyz⟩ := rows[i].eq_nil_or_concat'
  · simp [hnil] at har
  -- The last entry `z` of the row is at least every entry of the row, `a` among them.
  have hle : ∀ x ∈ ys, x ≤ z := by
    have hs := h.sortedLE _ (getElem_mem hi)
    rw [hyz, sortedLE_iff_pairwise, pairwise_append] at hs
    exact fun x hx => hs.2.2 x hx z mem_cons_self
  have hza : z = a := le_antisymm (hmax z (mem_flatten.mpr ⟨_, getElem_mem hi, by simp [hyz]⟩)) (by
    rw [hyz, mem_append, mem_singleton] at har
    rcases har with har | rfl
    · exact hle a har
    · exact le_rfl)
  simp [hyz, hza]

end List

namespace TauCeti

open List

section RowOperations

variable {α : Type*}

/-! ### Appending a letter to a row -/

/-- Append the letter `a` at the end of row `k` of a list of rows. If `k` is at least the number
of rows, `a` starts a new last row. -/
def appendToRow (a : α) : ℕ → List (List α) → List (List α)
  | _, [] => [[a]]
  | 0, row :: rows => (row ++ [a]) :: rows
  | k + 1, row :: rows => row :: appendToRow a k rows

/-- Appending to a row of the empty list of rows starts a new row. -/
@[simp]
theorem appendToRow_nil (a : α) (k : ℕ) : appendToRow a k [] = [[a]] := by cases k <;> rfl

/-- Appending to row `0` appends the letter to the first row. -/
@[simp]
theorem appendToRow_zero_cons (a : α) (row : List α) (rows : List (List α)) :
    appendToRow a 0 (row :: rows) = (row ++ [a]) :: rows := (rfl)

/-- Appending to row `k + 1` appends to row `k` of the remaining rows. -/
@[simp]
theorem appendToRow_succ_cons (a : α) (k : ℕ) (row : List α) (rows : List (List α)) :
    appendToRow a (k + 1) (row :: rows) = row :: appendToRow a k rows := (rfl)

/-- **The rows of `TauCeti.appendToRow a k`**: row `k` gains the letter `a` at its end, and every
other row is unchanged. Rows beyond the last one are read as empty. -/
theorem getD_appendToRow (a : α) {k : ℕ} {rows : List (List α)} (hk : k ≤ rows.length) (i : ℕ) :
    (appendToRow a k rows).getD i [] = if i = k then rows.getD k [] ++ [a] else rows.getD i [] := by
  induction rows generalizing k i with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    cases i <;> simp [appendToRow]
  | cons row rows ih =>
    cases k with
    | zero => cases i <;> simp [appendToRow]
    | succ k =>
      cases i with
      | zero => simp [appendToRow]
      | succ i => simpa [appendToRow] using ih (by simpa using hk) i

/-- Appending to row `k` adds a new row exactly when `k` is the number of rows. -/
theorem length_appendToRow (a : α) {k : ℕ} {rows : List (List α)} (hk : k ≤ rows.length) :
    (appendToRow a k rows).length = max rows.length (k + 1) := by
  induction rows generalizing k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    simp [appendToRow]
  | cons row rows ih =>
    cases k with
    | zero => simp [appendToRow]
    | succ k =>
      simp only [appendToRow, length_cons, ih (by simpa using hk : k ≤ rows.length)]
      omega

/-- Appending to a row adds the letter to the entries. -/
theorem flatten_appendToRow_perm (a : α) (k : ℕ) (rows : List (List α)) :
    (appendToRow a k rows).flatten.Perm (rows.flatten ++ [a]) := by
  induction rows generalizing k with
  | nil => simp
  | cons row rows ih =>
    cases k with
    | zero =>
      simpa [appendToRow] using (perm_append_comm (l₁ := [a]) (l₂ := rows.flatten)).append_left row
    | succ k => simpa [appendToRow] using (ih k).append_left row

/-- Appending `a` to row `s` puts `a` in row `s`, when `a` is not already present. -/
@[simp]
theorem findIdx?_mem_appendToRow_self [DecidableEq α] {a : α} {s : ℕ} {rows : List (List α)}
    (ha : ∀ row ∈ rows, a ∉ row) (hs : s ≤ rows.length) :
    (appendToRow a s rows).findIdx? (fun row => a ∈ row) = some s := by
  induction rows generalizing s with
  | nil =>
    obtain rfl : s = 0 := by simpa using hs
    simp
  | cons row rows ih =>
    cases s with
    | zero => simp [findIdx?_cons]
    | succ s =>
      simp [findIdx?_cons, ha row mem_cons_self,
        ih (fun r hr => ha r (mem_cons_of_mem _ hr)) (by simpa using hs)]

/-- Appending `a` to a row does not move any other letter. -/
@[simp]
theorem findIdx?_mem_appendToRow_of_ne [DecidableEq α] {a b : α} (hab : b ≠ a) (s : ℕ)
    (rows : List (List α)) :
    (appendToRow a s rows).findIdx? (fun row => b ∈ row) =
      rows.findIdx? (fun row => b ∈ row) := by
  induction rows generalizing s with
  | nil => simp [findIdx?_cons, hab]
  | cons row rows ih =>
    cases s with
    | zero => simp [findIdx?_cons, hab]
    | succ s => simp [findIdx?_cons, ih]

/-- **Appending to a row preserves tableaux** when the new cell is a corner of the new shape and
its entry fits: it is at least every entry of its row, and greater than the entry above it. -/
theorem _root_.List.IsTableauRows.appendToRow [Preorder α] {rows : List (List α)}
    (h : rows.IsTableauRows) {a : α} {k : ℕ} (hk : k ≤ rows.length)
    (hle : ∀ x ∈ rows.getD k [], x ≤ a)
    (habove : ∀ i, k = i + 1 → ∃ hlen : (rows.getD k []).length < (rows.getD i []).length,
      (rows.getD i [])[(rows.getD k []).length] < a) :
    (appendToRow a k rows).IsTableauRows := by
  induction rows generalizing k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    simpa [TauCeti.appendToRow, isTableauRows_cons] using
      sortedLE_iff_pairwise.mpr (pairwise_singleton _ a)
  | cons row rows ih =>
    obtain ⟨hne, hs, hab, hrows⟩ := isTableauRows_cons.mp h
    cases k with
    | zero =>
      refine isTableauRows_cons.mpr ⟨by simp, ?_, hab.append_right _, hrows⟩
      exact sortedLE_iff_pairwise.mpr (pairwise_append.mpr ⟨sortedLE_iff_pairwise.mp hs,
        pairwise_singleton _ _, fun x hx y hy => by
          simpa [mem_singleton.mp hy] using hle x (by simpa using hx)⟩)
    | succ k =>
      refine isTableauRows_cons.mpr ⟨hne, hs, ?_, ih hrows (by simpa using hk)
        (by simpa using hle) fun i hi => by simpa using habove (i + 1) (by omega)⟩
      cases k with
      | zero =>
        obtain ⟨hlen, hlt⟩ := habove 0 rfl
        cases rows with
        | nil => simpa [TauCeti.appendToRow] using (isRowAbove_nil row).append_singleton hlen hlt
        | cons lower rows => simpa [TauCeti.appendToRow] using hab.append_singleton hlen hlt
      | succ k =>
        cases rows with
        | nil => simp at hk
        | cons lower rows => simpa [TauCeti.appendToRow] using hab

/-! ### Removing the last letter of a row -/

/-- Remove the last letter of row `k` of a list of rows, deleting the row if it becomes empty.
At a corner of a tableau this undoes `TauCeti.appendToRow`. -/
def dropLastOfRow : ℕ → List (List α) → List (List α)
  | _, [] => []
  | 0, row :: rows => if row.dropLast = [] then rows else row.dropLast :: rows
  | k + 1, row :: rows => row :: dropLastOfRow k rows

/-- Removing a letter from the empty list of rows does nothing. -/
@[simp]
theorem dropLastOfRow_nil (k : ℕ) : dropLastOfRow k ([] : List (List α)) = [] := by
  cases k <;> rfl

/-- Removing the last letter of row `0` drops the last letter of the first row, deleting that row
if it becomes empty. -/
@[simp]
theorem dropLastOfRow_zero_cons (row : List α) (rows : List (List α)) :
    dropLastOfRow 0 (row :: rows) = if row.dropLast = [] then rows else row.dropLast :: rows :=
  (rfl)

/-- Removing the last letter of row `k + 1` removes the last letter of row `k` of the remaining
rows. -/
@[simp]
theorem dropLastOfRow_succ_cons (k : ℕ) (row : List α) (rows : List (List α)) :
    dropLastOfRow (k + 1) (row :: rows) = row :: dropLastOfRow k rows := (rfl)

/-- Removing the letter just appended to a row of a list of nonempty rows recovers the rows. -/
@[simp]
theorem dropLastOfRow_appendToRow (a : α) {k : ℕ} {rows : List (List α)}
    (hne : [] ∉ rows) (hk : k ≤ rows.length) : dropLastOfRow k (appendToRow a k rows) = rows := by
  induction rows generalizing k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    simp [appendToRow]
  | cons row rows ih =>
    have hrow : row ≠ [] := fun h => hne (h ▸ mem_cons_self)
    cases k with
    | zero => simp [appendToRow, hrow]
    | succ k =>
      simpa [appendToRow, dropLastOfRow] using
        ih (fun h => hne (mem_cons_of_mem _ h)) (by simpa using hk)

/-- **The rows of `TauCeti.dropLastOfRow k`** at a corner of a tableau: row `k` loses its last
letter, and every other row is unchanged. Rows beyond the last one are read as empty. -/
theorem getD_dropLastOfRow [Preorder α] {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows) (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length)
    (i : ℕ) :
    (dropLastOfRow k rows).getD i [] =
      if i = k then (rows.getD k []).dropLast else rows.getD i [] := by
  induction rows generalizing k i with
  | nil => simp at hk
  | cons row rows ih =>
    cases k with
    | zero =>
      by_cases hd : row.dropLast = []
      · obtain rfl := h.eq_nil_of_dropLast_eq_nil (by simpa using hk) hd
        cases i <;> simp [dropLastOfRow, hd]
      · cases i <;> simp [dropLastOfRow, hd]
    | succ k =>
      cases i with
      | zero => simp [dropLastOfRow]
      | succ i => simpa [dropLastOfRow] using ih h.tail (by simpa using hk) i

/-- At a corner of a tableau, putting back the last letter of row `k` after removing it recovers
the tableau. -/
@[simp]
theorem appendToRow_dropLastOfRow [Preorder α] {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows) (hk : (rows[k + 1]?.getD []).length < (rows[k]?.getD []).length)
    {a : α} (ha : (rows[k]?.getD []).getLast? = some a) :
    appendToRow a k (dropLastOfRow k rows) = rows := by
  induction rows generalizing k with
  | nil => simp at ha
  | cons row rows ih =>
    cases k with
    | zero =>
      obtain ⟨ys, rfl⟩ := getLast?_eq_some_iff.mp (by simpa using ha)
      by_cases hd : ys = []
      · subst hd
        obtain rfl := h.eq_nil_of_dropLast_eq_nil (by simpa using hk) (by simp)
        simp [dropLastOfRow]
      · simp [dropLastOfRow, hd]
    | succ k =>
      simpa [appendToRow, dropLastOfRow] using ih h.tail (by simpa using hk) (by simpa using ha)

/-- **Removing a corner preserves tableaux**: deleting the last letter of a row that is longer than
the next one gives a tableau. -/
theorem _root_.List.IsTableauRows.dropLastOfRow [Preorder α] {k : ℕ}
    {rows : List (List α)} (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    (dropLastOfRow k rows).IsTableauRows := by
  induction rows generalizing k with
  | nil => simp at hk
  | cons row rows ih =>
    obtain ⟨hne, hs, hab, hrows⟩ := isTableauRows_cons.mp h
    cases k with
    | zero =>
      by_cases hd : row.dropLast = []
      · simpa [TauCeti.dropLastOfRow, hd] using hrows
      · simp only [TauCeti.dropLastOfRow, hd, ite_false]
        have hk' : (rows.headD []).length ≤ row.dropLast.length := by
          cases rows with
          | nil => simp
          | cons lower rows => simp at hk ⊢; omega
        refine isTableauRows_cons.mpr ⟨hd, sortedLE_iff_pairwise.mpr
          ((sortedLE_iff_pairwise.mp hs).sublist (dropLast_sublist _)), ⟨hk', fun j hu hl => ?_⟩,
          hrows⟩
        rw [getElem_dropLast]
        exact hab.getElem_lt j (by simp at hu; omega) hl
    | succ k =>
      refine isTableauRows_cons.mpr ⟨hne, hs, ?_, ih hrows (by simpa using hk)⟩
      cases k with
      | zero =>
        cases rows with
        | nil => simp [TauCeti.dropLastOfRow]
        | cons lower rows =>
          by_cases hd : lower.dropLast = []
          · obtain rfl := hrows.eq_nil_of_dropLast_eq_nil (by simpa using hk) hd
            simp [TauCeti.dropLastOfRow, hd]
          · simp only [TauCeti.dropLastOfRow, hd, ite_false, headD_cons]
            refine ⟨by rw [length_dropLast]; exact (Nat.sub_le _ _).trans hab.length_le,
              fun j hu hl => ?_⟩
            rw [getElem_dropLast]
            exact hab.getElem_lt j hu _
      | succ k =>
        cases rows with
        | nil => simp [TauCeti.dropLastOfRow]
        | cons lower rows => simpa [TauCeti.dropLastOfRow] using hab

end RowOperations

variable {α : Type*} [LinearOrder α]

/-! ### Row insertion -/

/-- **Schensted row insertion** `T ← x` of a letter `x` into a tableau given by its rows `T`:
insert `x` into the first row by `TauCeti.rowBump`, insert the bumped letter into the next row,
and so on, until a letter is appended at the end of a row, possibly a new last row. -/
def rowInsert (x : α) : List (List α) → List (List α)
  | [] => [[x]]
  | row :: rows => (rowBump x row).1 :: (rowBump x row).2.elim rows (rowInsert · rows)

/-- The index of the row in which `TauCeti.rowInsert x T` adds its new cell. -/
def rowInsertIndex (x : α) : List (List α) → ℕ
  | [] => 0
  | row :: rows => (rowBump x row).2.elim 0 (rowInsertIndex · rows + 1)

/-- Inserting into the empty tableau gives a one-cell tableau. -/
@[simp]
theorem rowInsert_nil (x : α) : rowInsert x [] = [[x]] := (rfl)

/-- Inserting into the empty tableau adds its cell in the first row. -/
@[simp]
theorem rowInsertIndex_nil (x : α) : rowInsertIndex x [] = 0 := (rfl)

/-- If nothing is bumped from the first row, insertion stops there. -/
theorem rowInsert_cons_of_eq_none {x : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = none) : rowInsert x (row :: rows) = (rowBump x row).1 :: rows := by
  simp [rowInsert, h]

/-- A letter bumped from the first row is inserted into the remaining rows. -/
theorem rowInsert_cons_of_eq_some {x y : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = some y) :
    rowInsert x (row :: rows) = (rowBump x row).1 :: rowInsert y rows := by
  simp [rowInsert, h]

/-- If nothing is bumped from the first row, the new cell is in the first row. -/
theorem rowInsertIndex_cons_of_eq_none {x : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = none) : rowInsertIndex x (row :: rows) = 0 := by
  simp [rowInsertIndex, h]

/-- If a letter is bumped from the first row, the new cell is where its insertion into the
remaining rows puts it. -/
theorem rowInsertIndex_cons_of_eq_some {x y : α} {row : List α} (rows : List (List α))
    (h : (rowBump x row).2 = some y) :
    rowInsertIndex x (row :: rows) = rowInsertIndex y rows + 1 := by
  simp [rowInsertIndex, h]

/-- The first row of `T ← x` is the first row of `T` (empty if `T` is) after the first bump. -/
theorem headD_rowInsert (x : α) (rows : List (List α)) :
    (rowInsert x rows).headD [] = (rowBump x (rows.headD [])).1 := by
  cases rows with
  | nil => simp
  | cons row rows => cases h : (rowBump x row).2 <;> simp [rowInsert, h]

/-- **Row insertion conserves the letters**: `T ← x` has the letters of `T` together with `x`. -/
theorem flatten_rowInsert_perm (x : α) (rows : List (List α)) :
    (rowInsert x rows).flatten.Perm (x :: rows.flatten) := by
  induction rows generalizing x with
  | nil => simp
  | cons row rows ih =>
    have hp := rowBump_perm x row
    cases h : (rowBump x row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows h, flatten_cons, flatten_cons, ← cons_append]
      exact Perm.append_right _ (by simpa [h] using hp)
    | some y =>
      rw [rowInsert_cons_of_eq_some rows h, flatten_cons, flatten_cons, ← cons_append]
      refine ((ih y).append_left _).trans ?_
      rw [h] at hp
      simpa using hp.append_right rows.flatten

/-- The new cell is in an existing row or in the row just below the last one. -/
theorem rowInsertIndex_le_length (x : α) (rows : List (List α)) :
    rowInsertIndex x rows ≤ rows.length := by
  induction rows generalizing x with
  | nil => simp
  | cons row rows ih =>
    cases h : (rowBump x row).2 with
    | none => simp [rowInsertIndex_cons_of_eq_none rows h]
    | some y => simpa [rowInsertIndex_cons_of_eq_some rows h] using ih y

/-- **The shape of `T ← x`**: the row `TauCeti.rowInsertIndex x T` gains one cell and every
other row keeps its length. Rows beyond the last one are read as empty. -/
theorem length_getD_rowInsert (x : α) (rows : List (List α)) (i : ℕ) :
    ((rowInsert x rows).getD i []).length =
      (rows.getD i []).length + if i = rowInsertIndex x rows then 1 else 0 := by
  induction rows generalizing x i with
  | nil => cases i <;> simp
  | cons row rows ih =>
    have hl := length_rowBump x row
    cases h : (rowBump x row).2 with
    | none =>
      rw [h] at hl
      rw [rowInsert_cons_of_eq_none rows h, rowInsertIndex_cons_of_eq_none rows h]
      cases i <;> simp_all
    | some y =>
      rw [h] at hl
      rw [rowInsert_cons_of_eq_some rows h, rowInsertIndex_cons_of_eq_some rows h]
      cases i with
      | zero => simp_all
      | succ i => simpa using ih y i

/-- `T ← x` has one more row than `T` exactly when the new cell starts a new row. -/
theorem length_rowInsert (x : α) (rows : List (List α)) :
    (rowInsert x rows).length = max rows.length (rowInsertIndex x rows + 1) := by
  induction rows generalizing x with
  | nil => simp
  | cons row rows ih =>
    cases h : (rowBump x row).2 with
    | none => simp [rowInsert_cons_of_eq_none rows h, rowInsertIndex_cons_of_eq_none rows h]
    | some y =>
      simp only [rowInsert_cons_of_eq_some rows h, rowInsertIndex_cons_of_eq_some rows h,
        length_cons, ih y]
      omega

/-- The row to which `TauCeti.rowInsert_appendToRow` moves a letter appended to row `s` of `T`
is a row of `T ← x` or the row just below its last one: it is `s + 1` if the new cell of `T ← x`
is in row `s`, and `s` otherwise. -/
theorem le_length_rowInsert (x : α) {s : ℕ} {rows : List (List α)} (hs : s ≤ rows.length) :
    (if rowInsertIndex x rows = s then s + 1 else s) ≤ (rowInsert x rows).length := by
  have hle := rowInsertIndex_le_length x rows
  rw [length_rowInsert]
  split_ifs <;> omega

/-- Inserting a letter at least as large as every entry of the first row appends it to the first
row. -/
theorem rowInsert_of_forall_le {k : α} {rows : List (List α)}
    (h : ∀ z ∈ rows.headD [], z ≤ k) : rowInsert k rows = appendToRow k 0 rows := by
  cases rows with
  | nil => simp
  | cons row rows =>
    rw [rowInsert_cons_of_eq_none rows (by simpa using h), rowBump_of_forall_le k row h]
    simp

/-- Inserting a letter at least as large as every entry of the first row adds its cell to the
first row. -/
theorem rowInsertIndex_of_forall_le {k : α} {rows : List (List α)}
    (h : ∀ z ∈ rows.headD [], z ≤ k) : rowInsertIndex k rows = 0 := by
  cases rows with
  | nil => simp
  | cons row rows => exact rowInsertIndex_cons_of_eq_none rows (by simpa using h)

/-- Insertion past a larger letter, computing both the new tableau and its new cell. -/
theorem rowInsert_appendToRow_and_rowInsertIndex_appendToRow {x k : α} {s : ℕ}
    {rows : List (List α)} (hx : x < k) (h : ∀ z ∈ rows.flatten, z < k) (hs : s ≤ rows.length) :
    rowInsert x (appendToRow k s rows) =
        appendToRow k (if rowInsertIndex x rows = s then s + 1 else s) (rowInsert x rows) ∧
      rowInsertIndex x (appendToRow k s rows) =
        if rowInsertIndex x rows = s then s + 1 else rowInsertIndex x rows := by
  induction rows generalizing x s with
  | nil =>
    obtain rfl : s = 0 := by simpa using hs
    have hb : (rowBump x [k]).2 = some k := by simp [hx]
    rw [appendToRow_nil, rowInsert_cons_of_eq_some [] hb, rowInsertIndex_cons_of_eq_some [] hb]
    simp [rowBump_cons_of_lt _ hx]
  | cons row rows ih =>
    have hrows : ∀ z ∈ rows.flatten, z < k := fun z hz => h z (by simp_all)
    cases s with
    | zero =>
      cases hb : (rowBump x row).2 with
      | none =>
        have hle : ∀ z ∈ row, z ≤ x := (rowBump_snd_eq_none_iff x row).mp hb
        have hbk : (rowBump x (row ++ [k])).2 = some k := by
          rw [rowBump_append x row [k] hle]
          simp [hx]
        have hk : ∀ z ∈ rows.headD [], z ≤ k := fun z hz =>
          (hrows z (by cases rows <;> simp_all)).le
        simp [rowInsert_cons_of_eq_some rows hbk, rowInsertIndex_cons_of_eq_some rows hbk,
          rowInsert_cons_of_eq_none rows hb, rowInsertIndex_cons_of_eq_none rows hb,
          rowInsert_of_forall_le hk, rowInsertIndex_of_forall_le hk, rowBump_append x row [k] hle,
          rowBump_of_forall_le x row hle, hx]
      | some y =>
        have hb' : (rowBump x (row ++ [k])).2 = some y := by
          rw [rowBump_append_of_snd_eq_some hb]
        simp [rowInsert_cons_of_eq_some rows hb', rowInsertIndex_cons_of_eq_some rows hb',
          rowInsert_cons_of_eq_some rows hb, rowInsertIndex_cons_of_eq_some rows hb,
          rowBump_append_of_snd_eq_some hb]
    | succ s =>
      cases hb : (rowBump x row).2 with
      | none =>
        simp [rowInsert_cons_of_eq_none _ hb, rowInsertIndex_cons_of_eq_none _ hb]
      | some y =>
        have hy : y < k := h y (mem_flatten_of_mem mem_cons_self (mem_of_rowBump_snd_eq_some hb))
        obtain ⟨ih₁, ih₂⟩ := ih hy hrows (by simpa using hs)
        simp only [appendToRow_succ_cons, rowInsert_cons_of_eq_some _ hb,
          rowInsertIndex_cons_of_eq_some _ hb, ih₁, ih₂]
        constructor <;> split_ifs <;> simp_all

/-- **Insertion past a larger letter.** Let `k` be strictly larger than `x` and than every entry
of `rows`, and append `k` to row `s`. Inserting `x` then gives the insertion of `x` into `rows`
with `k` appended to row `s`, unless the insertion of `x` into `rows` ends in row `s`: in that
case `x`'s bumping path displaces `k`, which moves to the end of row `s + 1`. -/
theorem rowInsert_appendToRow {x k : α} {s : ℕ} {rows : List (List α)} (hx : x < k)
    (h : ∀ z ∈ rows.flatten, z < k) (hs : s ≤ rows.length) :
    rowInsert x (appendToRow k s rows) =
      appendToRow k (if rowInsertIndex x rows = s then s + 1 else s) (rowInsert x rows) :=
  (rowInsert_appendToRow_and_rowInsertIndex_appendToRow hx h hs).1

/-- **The new cell of an insertion past a larger letter.** In the situation of
`TauCeti.rowInsert_appendToRow`, the new cell is in the same row as for the insertion of `x` into
`rows`, unless that row is `s`, in which case it is the cell of `k` at the end of row `s + 1`. -/
theorem rowInsertIndex_appendToRow {x k : α} {s : ℕ} {rows : List (List α)} (hx : x < k)
    (h : ∀ z ∈ rows.flatten, z < k) (hs : s ≤ rows.length) :
    rowInsertIndex x (appendToRow k s rows) =
      if rowInsertIndex x rows = s then s + 1 else rowInsertIndex x rows :=
  (rowInsert_appendToRow_and_rowInsertIndex_appendToRow hx h hs).2

/-! ### Insertion preserves tableaux -/

/-- The column step of row insertion: if `upper` sits on top of `lower` and inserting `x` into
`upper` bumps `y`, then the new upper row sits on top of the result of inserting `y` into
`lower`. The bumped letter lands weakly to the left of the column it left. -/
theorem isRowAbove_rowBump {x y : α} {upper lower : List α}
    (h : upper.IsRowAbove lower) (hbump : (rowBump x upper).2 = some y) :
    (rowBump x upper).1.IsRowAbove (rowBump y lower).1 := by
  obtain ⟨j, hj, hU', hUj, hpre, hxy⟩ :=
    exists_set_of_rowBump_snd_eq_some hbump
  rw [hU']
  cases hlow : (rowBump y lower).2 with
  | none =>
    have hle := (rowBump_snd_eq_none_iff y lower).mp hlow
    rw [rowBump_of_forall_le y lower hle]
    -- every entry of `lower` is at most `y`, so `lower` ends strictly before column `j`
    have hlen : lower.length ≤ j := by
      by_contra hcon
      have := h.getElem_lt j hj (by omega)
      exact absurd (hle _ (getElem_mem (by omega))) (not_le.mpr (hUj ▸ this))
    refine ⟨by simp; omega, fun c hu hl => ?_⟩
    simp only [length_append, length_cons, length_nil] at hl
    rw [getElem_set]
    by_cases hc : c < lower.length
    · rw [getElem_append_left hc, ite_eq_right (by omega)]
      exact h.getElem_lt c (by simpa using hu) hc
    · have hc' : c = lower.length := by omega
      subst hc'
      rw [getElem_append_right (by omega)]
      simp only [Nat.sub_self, getElem_cons_zero]
      split_ifs with hjc
      · exact hxy
      · exact (hpre _ (by omega)).trans_lt hxy
  | some w =>
    obtain ⟨j', hj', hL', _, hpre', hyw⟩ :=
      exists_set_of_rowBump_snd_eq_some hlow
    rw [hL']
    -- the first entry of `lower` exceeding `y` is weakly left of column `j`
    have hjj : j' ≤ j := by
      by_contra hcon
      have := h.getElem_lt j hj (by omega)
      exact absurd (hpre' j (by omega)) (not_le.mpr (hUj ▸ this))
    refine ⟨by simpa using h.length_le, fun c hu hl => ?_⟩
    simp only [List.length_set] at hu hl
    rw [getElem_set, getElem_set]
    split_ifs with h1 h2 h2
    · exact hxy
    · subst h1
      exact hxy.trans (hUj ▸ h.getElem_lt _ hj hl)
    · exact (hpre c (by omega)).trans_lt hxy
    · exact h.getElem_lt c hu hl

/-- **Row insertion preserves tableaux.** -/
theorem _root_.List.IsTableauRows.rowInsert {rows : List (List α)} (h : rows.IsTableauRows)
    (x : α) : (rowInsert x rows).IsTableauRows := by
  induction rows generalizing x with
  | nil => simp [isTableauRows_cons, sortedLE_nil]
  | cons row rows ih =>
    obtain ⟨hne, hs, habove, hrows⟩ := isTableauRows_cons.mp h
    have hs' := sortedLE_rowBump x hs
    have hne' : (rowBump x row).1 ≠ [] := by
      have := length_rowBump x row
      intro h0
      rw [h0] at this
      cases hb : (rowBump x row).2 <;> simp_all
    cases hb : (rowBump x row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows hb]
      refine isTableauRows_cons.mpr ⟨hne', hs', ?_, hrows⟩
      rw [rowBump_of_forall_le x row ((rowBump_snd_eq_none_iff x row).mp hb)]
      exact habove.append_right _
    | some y =>
      rw [rowInsert_cons_of_eq_some rows hb]
      refine isTableauRows_cons.mpr ⟨hne', hs', ?_, ih hrows y⟩
      rw [headD_rowInsert]
      exact isRowAbove_rowBump habove hb

/-- The row below the new cell of `T ← x` is strictly shorter than the row gaining the cell.
Only weakly decreasing original row lengths are needed. -/
theorem length_getD_succ_rowInsertIndex_lt {rows : List (List α)}
    (h : (rows.map List.length).SortedGE) (x : α) :
    ((rowInsert x rows).getD (rowInsertIndex x rows + 1) []).length <
      ((rowInsert x rows).getD (rowInsertIndex x rows) []).length := by
  rw [length_getD_rowInsert, length_getD_rowInsert, ite_eq_right (by omega), ite_eq_left rfl]
  simp only [Nat.add_zero]
  apply Nat.lt_succ_of_le
  by_cases hi : rowInsertIndex x rows + 1 < rows.length
  · have hj : rowInsertIndex x rows < rows.length := by omega
    rw [List.getD_eq_getElem rows [] hi, List.getD_eq_getElem rows [] hj]
    have hlen := h.getElem_ge_getElem_of_le (hi := by simpa using hi)
      (hj := by simpa using hj) (Nat.le_succ _)
    rw [List.getElem_map, List.getElem_map] at hlen
    exact hlen
  · rw [List.getD_eq_default rows [] (Nat.le_of_not_gt hi)]
    simp

/-- **A new cell below the first row sits under a longer row**: if `T ← x` adds its cell in row
`i + 1`, then row `i + 1` of `T` is strictly shorter than row `i`. -/
theorem length_getD_succ_lt_of_rowInsertIndex_eq_succ {rows : List (List α)}
    (h : rows.IsTableauRows) {x : α} {i : ℕ} (hi : rowInsertIndex x rows = i + 1) :
    (rows.getD (i + 1) []).length < (rows.getD i []).length := by
  have := (h.rowInsert x).length_getD_succ_le i
  rw [length_getD_rowInsert, length_getD_rowInsert, hi] at this
  split_ifs at this <;> omega

/-! ### Reverse insertion -/

/-- **Reverse row insertion** from the end of row `k`: remove the last entry of row `k`
(deleting the row if it becomes empty), insert it into row `k - 1` by
`TauCeti.reverseRowBump`, insert the letter returned into row `k - 2`, and so on up to the first
row. The second component is the letter returned by the first row, or `none` if some step
fails, which does not happen at a corner of a tableau. -/
def reverseRowInsert : ℕ → List (List α) → List (List α) × Option α
  | _, [] => ([], none)
  | 0, row :: rows => (if row.dropLast = [] then rows else row.dropLast :: rows, row.getLast?)
  | k + 1, row :: rows =>
    (reverseRowInsert k rows).2.elim (row :: (reverseRowInsert k rows).1, none) fun y =>
      ((reverseRowBump y row).1 :: (reverseRowInsert k rows).1, (reverseRowBump y row).2)

/-- Reverse insertion into the empty tableau fails. -/
@[simp]
theorem reverseRowInsert_nil (k : ℕ) : reverseRowInsert k ([] : List (List α)) = ([], none) := by
  cases k <;> rfl

/-- Reverse insertion from the end of the first row removes its last entry and returns it. -/
theorem reverseRowInsert_zero_cons (row : List α) (rows : List (List α)) :
    reverseRowInsert 0 (row :: rows) =
      (if row.dropLast = [] then rows else row.dropLast :: rows, row.getLast?) := (rfl)

/-- A letter returned by reverse insertion into the rows below the first is reverse bumped into
the first row. -/
theorem reverseRowInsert_succ_cons_of_eq_some {k : ℕ} {y : α} (row : List α)
    {rows : List (List α)} (h : (reverseRowInsert k rows).2 = some y) :
    reverseRowInsert (k + 1) (row :: rows) =
      ((reverseRowBump y row).1 :: (reverseRowInsert k rows).1, (reverseRowBump y row).2) := by
  simp [reverseRowInsert, h]

/-- If reverse insertion into the rows below the first fails, it fails. -/
theorem reverseRowInsert_succ_cons_of_eq_none {k : ℕ} (row : List α) {rows : List (List α)}
    (h : (reverseRowInsert k rows).2 = none) :
    reverseRowInsert (k + 1) (row :: rows) = (row :: (reverseRowInsert k rows).1, none) := by
  simp [reverseRowInsert, h]

/-- **Reverse insertion undoes insertion**: reverse inserting from the new cell of `T ← x`
recovers `T` and returns `x`. Only the rows of `T` being nonempty and weakly increasing is used. -/
theorem reverseRowInsert_rowInsert (x : α) {rows : List (List α)} (hne : [] ∉ rows)
    (hs : ∀ row ∈ rows, row.SortedLE) :
    reverseRowInsert (rowInsertIndex x rows) (rowInsert x rows) = (rows, some x) := by
  induction rows generalizing x with
  | nil => simp [reverseRowInsert_zero_cons]
  | cons row rows ih =>
    have hrow : row ≠ [] := fun h => hne (h ▸ mem_cons_self)
    cases hb : (rowBump x row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows hb, rowInsertIndex_cons_of_eq_none rows hb,
        rowBump_of_forall_le x row ((rowBump_snd_eq_none_iff x row).mp hb),
        reverseRowInsert_zero_cons]
      simp [hrow]
    | some y =>
      have ih' := ih y (fun h => hne (mem_cons_of_mem _ h))
        (fun r hr => hs r (mem_cons_of_mem _ hr))
      rw [rowInsert_cons_of_eq_some rows hb, rowInsertIndex_cons_of_eq_some rows hb,
        reverseRowInsert_succ_cons_of_eq_some _ (by rw [ih']), ih',
        reverseRowBump_rowBump_of_sortedLE x y (hs row mem_cons_self) hb]

/-- The column relation between an old row `L` and the row `L'` replacing it after reverse
insertion, when the letter `L[c]` was ejected from column `c`: `L'` is no longer, its entries
are no smaller, and from column `c` on they exceed the ejected letter. -/
structure ReverseStep (L L' : List α) (c : ℕ) (hc : c < L.length) : Prop where
  length_le : L'.length ≤ L.length
  getElem_le : ∀ (j : ℕ) (h₁ : j < L.length) (h₂ : j < L'.length), L[j] ≤ L'[j]
  getElem_lt : ∀ (j : ℕ) (h₂ : j < L'.length), c ≤ j → L[c] < L'[j]

/-- The column step of reverse insertion: if `U` sits on top of `L` and the letter `L[c]`
ejected from `L` reverse bumps `x` out of `U`, then the new upper row sits on top of the new
lower row, and the relation `ReverseStep` passes from `(L, L')` to the upper rows. -/
theorem reverseStep_reverseRowBump {U L L' : List α} {c : ℕ} {hc : c < L.length}
    (hUL : U.IsRowAbove L) (hstep : ReverseStep L L' c hc) :
    ∃ d, ∃ hd : d < U.length, (reverseRowBump L[c] U).2 = some U[d] ∧
      (reverseRowBump L[c] U).1.IsRowAbove L' ∧ ReverseStep U (reverseRowBump L[c] U).1 d hd := by
  -- column `c` of `U` holds an entry smaller than the incoming letter, so the bump succeeds
  have hcU : c < U.length := hc.trans_le hUL.length_le
  have hsome : (reverseRowBump L[c] U).2 ≠ none := by
    rw [ne_eq, reverseRowBump_snd_eq_none_iff]
    exact fun hall => absurd (hall _ (getElem_mem hcU)) (not_le.mpr (hUL.getElem_lt c hcU hc))
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hsome
  obtain ⟨d, hd, hU', hUd, hpost, hxy⟩ :=
    exists_set_of_reverseRowBump_snd_eq_some hx
  -- the replaced position is weakly right of column `c`
  have hcd : c ≤ d := by
    by_contra hcon
    exact absurd (hpost c hcU (by omega)) (not_le.mpr (hUL.getElem_lt c hcU hc))
  refine ⟨d, hd, by rw [hx, hUd], ?_, ?_⟩
  · rw [hU']
    refine ⟨by simpa using hstep.length_le.trans hUL.length_le, fun j hu hl => ?_⟩
    simp only [List.length_set] at hu
    rw [getElem_set]
    split_ifs with hdj
    · subst hdj
      exact hstep.getElem_lt d hl hcd
    · have hjL := hl.trans_le hstep.length_le
      exact (hUL.getElem_lt j hu hjL).trans_le (hstep.getElem_le j hjL hl)
  · rw [hU']
    refine ⟨by simp, fun j h₁ h₂ => ?_, fun j h₂ hdj => ?_⟩
    · rw [getElem_set]
      split_ifs with hdj
      · subst hdj
        exact hUd ▸ hxy.le
      · exact le_rfl
    · simp only [List.length_set] at h₂
      rw [getElem_set]
      split_ifs with hdj'
      · exact hUd ▸ hxy
      · exact hUd ▸ hxy.trans_le (hpost j h₂ (by omega))

/-- The invariant of reverse insertion from a corner: the letter returned was ejected from
some column `c` of the first row, the result is a tableau, and its first row satisfies
`ReverseStep`. Reinserting the returned letter recovers the tableau and the chosen corner. -/
theorem exists_reverseRowInsert_of_isTableauRows {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    ∃ c, ∃ hc : c < (rows.headD []).length,
      (reverseRowInsert k rows).2 = some (rows.headD [])[c] ∧
        (reverseRowInsert k rows).1.IsTableauRows ∧
        ReverseStep (rows.headD []) ((reverseRowInsert k rows).1.headD []) c hc ∧
        rowInsert (rows.headD [])[c] (reverseRowInsert k rows).1 = rows ∧
        rowInsertIndex (rows.headD [])[c] (reverseRowInsert k rows).1 = k := by
  induction rows generalizing k with
  | nil => simp at hk
  | cons row rows ih =>
    obtain ⟨hne, hs, habove, hrows⟩ := isTableauRows_cons.mp h
    simp only [headD_cons]
    cases k with
    | zero =>
      -- remove the last entry of the first row
      have hlen : 0 < row.length := length_pos_iff.mpr hne
      have hlast : row.dropLast ++ [row[row.length - 1]] = row := by
        simpa only [getLast_eq_getElem] using dropLast_concat_getLast hne
      have hle : ∀ z ∈ row.dropLast, z ≤ row[row.length - 1] := by
        have hs' := hs
        rw [← hlast, sortedLE_append] at hs'
        exact fun z hz => hs'.2.2 z hz _ mem_cons_self
      refine ⟨row.length - 1, by omega, ?_⟩
      by_cases hd : row.dropLast = []
      · -- a one-cell first row at a corner is the whole tableau
        obtain rfl := h.eq_nil_of_dropLast_eq_nil (by simpa using hk) hd
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [reverseRowInsert_zero_cons, getLast?_eq_getElem?]
        · simp [reverseRowInsert_zero_cons, hd]
        · simp only [reverseRowInsert_zero_cons, ite_eq_left hd, headD_nil]
          exact ⟨by simp, fun _ _ h₂ => absurd h₂ (by simp), fun _ h₂ _ => absurd h₂ (by simp)⟩
        · simpa [reverseRowInsert_zero_cons, hd] using congrArg (fun r => [r]) hlast
        · simp [reverseRowInsert_zero_cons, hd]
      · have hk' : (rows.headD []).length ≤ row.dropLast.length := by
          cases rows with
          | nil => simp
          | cons lower rows => simp at hk ⊢; omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [reverseRowInsert_zero_cons, getLast?_eq_getElem?]
        · rw [reverseRowInsert_zero_cons, ite_eq_right hd]
          refine isTableauRows_cons.mpr ⟨hd, sortedLE_iff_pairwise.mpr
            ((sortedLE_iff_pairwise.mp hs).sublist (dropLast_sublist _)), ⟨hk', fun j hu hl => ?_⟩,
            hrows⟩
          rw [getElem_dropLast]
          exact habove.getElem_lt j (by simp at hu; omega) hl
        · rw [reverseRowInsert_zero_cons, ite_eq_right hd]
          refine ⟨by simp, fun j h₁ h₂ => ?_, fun j h₂ hj => ?_⟩
          · simp [getElem_dropLast]
          · simp at h₂; omega
        · simp only [reverseRowInsert_zero_cons, ite_eq_right hd]
          rw [rowInsert_cons_of_eq_none rows ((rowBump_snd_eq_none_iff _ _).mpr hle),
            rowBump_of_forall_le _ _ hle, hlast]
        · simp only [reverseRowInsert_zero_cons, ite_eq_right hd]
          exact rowInsertIndex_cons_of_eq_none rows ((rowBump_snd_eq_none_iff _ _).mpr hle)
    | succ k =>
      obtain ⟨c, hc, hret, htab, hstep, hins, hidx⟩ := ih hrows (by simpa using hk)
      obtain ⟨d, hd, hx, hU, hstep'⟩ := reverseStep_reverseRowBump habove hstep
      -- Recover the first row by the local inverse, and the remaining rows by induction.
      have hb := rowBump_reverseRowBump_of_sortedLE _ _ hs hx
      rw [reverseRowInsert_succ_cons_of_eq_some row hret]
      refine ⟨d, hd, hx, isTableauRows_cons.mpr ⟨?_, ?_, hU, htab⟩, hstep', ?_, ?_⟩
      · intro h0
        have := length_reverseRowBump (rows.headD [])[c] row
        rw [h0, hx] at this
        simp only [length_nil, Option.toList_some, length_singleton, Nat.zero_add] at this
        exact hne (length_eq_zero_iff.mp (by omega))
      · exact sortedLE_reverseRowBump _ hs
      · rw [rowInsert_cons_of_eq_some _ (by rw [hb]), hb, hins]
      · rw [rowInsertIndex_cons_of_eq_some _ (by rw [hb]), hidx]

/-- **Reverse insertion preserves tableaux at corners**: reverse inserting from the end of a
row `k` of a tableau whose next row is strictly shorter yields a tableau. -/
theorem _root_.List.IsTableauRows.reverseRowInsert {k : ℕ} {rows : List (List α)}
    (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    (reverseRowInsert k rows).1.IsTableauRows := by
  obtain ⟨-, -, -, htab, -⟩ := exists_reverseRowInsert_of_isTableauRows h hk
  exact htab

/-- **Insertion undoes reverse insertion at a corner.** If row `k + 1` of a tableau `T` is
strictly shorter than row `k`, then reverse insertion from the end of row `k` returns a letter
`x` and a tableau `T'` such that `T' ← x` is `T`, with its new cell in row `k`. -/
theorem rowInsert_reverseRowInsert {k : ℕ} {rows : List (List α)} (h : rows.IsTableauRows)
    (hk : (rows.getD (k + 1) []).length < (rows.getD k []).length) :
    ∃ x, (reverseRowInsert k rows).2 = some x ∧
      rowInsert x (reverseRowInsert k rows).1 = rows ∧
        rowInsertIndex x (reverseRowInsert k rows).1 = k := by
  obtain ⟨c, hc, hret, -, -, hins, hidx⟩ := exists_reverseRowInsert_of_isTableauRows h hk
  exact ⟨_, hret, hins, hidx⟩

/-! ### Insertion as a bijection -/

/-- **Row insertion is a bijection** between pairs of a tableau and a letter, and pairs of a
tableau and a row `k` ending in a corner, that is, whose next row is strictly shorter. It sends
`(T, x)` to `T ← x` with the row of its new cell; the inverse is reverse row insertion. -/
def rowInsertEquiv :
    {rows : List (List α) // rows.IsTableauRows} × α ≃
      {p : List (List α) × ℕ //
        p.1.IsTableauRows ∧ (p.1.getD (p.2 + 1) []).length < (p.1.getD p.2 []).length} where
  toFun p := ⟨(rowInsert p.2 p.1.1, rowInsertIndex p.2 p.1.1), p.1.2.rowInsert p.2,
    length_getD_succ_rowInsertIndex_lt p.1.2.sortedGE_map_length p.2⟩
  invFun p := (⟨(reverseRowInsert p.1.2 p.1.1).1, p.2.1.reverseRowInsert p.2.2⟩,
    (reverseRowInsert p.1.2 p.1.1).2.get
      (Option.isSome_iff_exists.mpr ((rowInsert_reverseRowInsert p.2.1 p.2.2).imp fun _ h => h.1)))
  left_inv p := by
    have h := reverseRowInsert_rowInsert p.2 p.1.2.nil_notMem p.1.2.sortedLE
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [h]
    · simp [h]
  right_inv p := by
    obtain ⟨x, hx, hins, hidx⟩ := rowInsert_reverseRowInsert p.2.1 p.2.2
    refine Subtype.ext (Prod.ext ?_ ?_)
    · simpa [hx] using hins
    · simpa [hx] using hidx

/-- `rowInsertEquiv` sends `(T, x)` to `T ← x` with the row of its new cell. -/
@[simp]
theorem rowInsertEquiv_apply_coe (rows : {rows : List (List α) // rows.IsTableauRows}) (x : α) :
    (rowInsertEquiv (rows, x) : List (List α) × ℕ) =
      (rowInsert x rows.1, rowInsertIndex x rows.1) := (rfl)

/-- The tableau of `rowInsertEquiv.symm p` is the result of reverse row insertion. -/
@[simp]
theorem rowInsertEquiv_symm_apply_fst_coe
    (p : {p : List (List α) × ℕ //
      p.1.IsTableauRows ∧ (p.1.getD (p.2 + 1) []).length < (p.1.getD p.2 []).length}) :
    ((rowInsertEquiv.symm p).1 : List (List α)) = (reverseRowInsert p.1.2 p.1.1).1 := (rfl)

/-- The letter of `rowInsertEquiv.symm p` is the letter returned by reverse row insertion. -/
theorem some_rowInsertEquiv_symm_apply_snd
    (p : {p : List (List α) × ℕ //
      p.1.IsTableauRows ∧ (p.1.getD (p.2 + 1) []).length < (p.1.getD p.2 []).length}) :
    some (rowInsertEquiv.symm p).2 = (reverseRowInsert p.1.2 p.1.1).2 := by
  simp [rowInsertEquiv]

end TauCeti

end
end

run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingInsertionCore row-insertion component processed"
  progressOutput.flush
/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.Schensted.Bumping -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The row-insertion bumping lemma

If `x ≤ y`, inserting `x` and then `y` into a semistandard tableau places the second new
cell weakly above and strictly to the right of the first. If `y < x`, the second cell is
strictly below and weakly to the left. Thus the order of two incoming letters is detected
by either the rows or the columns of their new cells.

The column of the cell added by inserting `x` into `rows` is the original length of row
`rowInsertIndex x rows`. These comparisons ensure that a weakly increasing block of letters
adds cells in distinct columns. This is the horizontal-strip property needed for the
semistandard recording tableau in the matrix Robinson--Schensted--Knuth correspondence.

The row comparisons require less: weakly increasing rows suffice for the weak comparison,
and the strict comparison holds even without any tableau hypothesis. The descending column
comparison requires only weakly decreasing row lengths, with no ordering of the entries.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 4.1.
* B. E. Sagan, *The Symmetric Group*, second edition, Springer GTM 203 (2001), Section 3.2.
-/

section
namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

/-- Inserting weakly increasing letters successively ends weakly higher the second time.
Only weak increase within each row is needed. -/
theorem rowInsertIndex_le_of_le {rows : List (List α)}
    (hrows : ∀ row ∈ rows, row.SortedLE) {x y : α} (hxy : x ≤ y) :
    rowInsertIndex y (rowInsert x rows) ≤ rowInsertIndex x rows := by
  induction rows generalizing x y with
  | nil =>
    simp [rowInsertIndex_cons_of_eq_none []
      ((rowBump_snd_eq_none_iff y [x]).mpr (by simpa using hxy))]
  | cons row rows ih =>
    cases hx : (rowBump x row).2 with
    | none =>
      have hle := (rowBump_snd_eq_none_iff x row).mp hx
      have hy : (rowBump y (rowBump x row).1).2 = none := by
        rw [rowBump_of_forall_le x row hle]
        apply (rowBump_snd_eq_none_iff _ _).mpr
        intro z hz
        rcases mem_append.mp hz with hz | hz
        · exact (hle z hz).trans hxy
        · exact (mem_singleton.mp hz) ▸ hxy
      simp [rowInsert_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_none rows hy]
    | some a =>
      rw [rowInsert_cons_of_eq_some rows hx, rowInsertIndex_cons_of_eq_some rows hx]
      cases hy : (rowBump y (rowBump x row).1).2 with
      | none => simp [rowInsertIndex_cons_of_eq_none _ hy]
      | some b =>
        rw [rowInsertIndex_cons_of_eq_some _ hy]
        exact Nat.add_le_add_right (ih (fun r hr => hrows r (mem_cons_of_mem _ hr))
          (rowBump_bumped_le_of_le (hrows row mem_cons_self) hxy hx hy)) 1

/-- Inserting a strictly smaller letter successively ends strictly lower the second time.
This holds for arbitrary lists of rows. -/
theorem rowInsertIndex_lt_of_lt {rows : List (List α)} {x y : α} (hyx : y < x) :
    rowInsertIndex x rows < rowInsertIndex y (rowInsert x rows) := by
  induction rows generalizing x y with
  | nil =>
    rw [rowInsert_nil, rowInsertIndex_nil,
      rowInsertIndex_cons_of_eq_some (y := x) [] (by simp [rowBump_cons_of_lt [] hyx])]
    simp
  | cons row rows ih =>
    obtain ⟨b, hy, hbx⟩ := exists_rowBump_snd_eq_some_le_of_lt hyx row
    cases hx : (rowBump x row).2 with
    | none =>
      simp [rowInsert_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_none rows hx,
        rowInsertIndex_cons_of_eq_some rows hy]
    | some a =>
      rw [rowInsert_cons_of_eq_some rows hx, rowInsertIndex_cons_of_eq_some rows hx,
        rowInsertIndex_cons_of_eq_some _ hy]
      exact Nat.add_lt_add_right (ih (hbx.trans_lt (lt_of_rowBump_snd_eq_some hx))) 1

/-- For weakly increasing rows, the second insertion ends weakly higher exactly when the
second incoming letter is at least the first. Supply `hrows` explicitly when using this
characterization with `simp`: its discharger does not solve the universally quantified
row-sortedness premise. -/
theorem rowInsertIndex_le_iff {rows : List (List α)}
    (hrows : ∀ row ∈ rows, row.SortedLE) (x y : α) :
    rowInsertIndex y (rowInsert x rows) ≤ rowInsertIndex x rows ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    exact (not_lt_of_ge h) (rowInsertIndex_lt_of_lt (not_le.mp hxy))
  · exact rowInsertIndex_le_of_le hrows

/-- The second cell lies strictly to the right when the incoming letters weakly increase.
The column indices are the row lengths before the respective insertions. -/
theorem rowInsert_column_lt_of_le {rows : List (List α)} (hrows : rows.IsTableauRows)
    {x y : α} (hxy : x ≤ y) :
    (rows.getD (rowInsertIndex x rows) []).length <
      ((rowInsert x rows).getD (rowInsertIndex y (rowInsert x rows)) []).length := by
  have hrow := rowInsertIndex_le_of_le hrows.sortedLE hxy
  have hanti : Antitone fun i => ((rowInsert x rows).getD i []).length :=
    antitone_nat_of_succ_le (hrows.rowInsert x).length_getD_succ_le
  have hlen := hanti hrow
  dsimp only at hlen
  rw [length_getD_rowInsert, ite_eq_left rfl] at hlen
  omega

/-- The second cell lies weakly to the left when the second incoming letter is smaller.
The column indices are the row lengths before the respective insertions. Only weakly
decreasing row lengths are needed; the entries may be unsorted. -/
theorem rowInsert_column_le_of_lt {rows : List (List α)}
    (hshape : Antitone fun i => (rows.getD i []).length)
    {x y : α} (hyx : y < x) :
    ((rowInsert x rows).getD (rowInsertIndex y (rowInsert x rows)) []).length ≤
      (rows.getD (rowInsertIndex x rows) []).length := by
  have hrow := rowInsertIndex_lt_of_lt (rows := rows) hyx
  rw [length_getD_rowInsert, ite_eq_right (Ne.symm (Nat.ne_of_lt hrow)), Nat.add_zero]
  exact hshape hrow.le

/-- The second new cell lies strictly to the right exactly when the second incoming letter
is at least the first. This includes equal letters, which produce distinct columns. -/
@[simp]
theorem rowInsert_column_lt_iff {rows : List (List α)} (hrows : rows.IsTableauRows)
    (x y : α) :
    (rows[rowInsertIndex x rows]?.getD []).length <
      ((rowInsert x rows)[rowInsertIndex y (rowInsert x rows)]?.getD []).length ↔ x ≤ y := by
  simp only [← getD_eq_getElem?_getD]
  constructor
  · intro h
    by_contra hxy
    exact (not_lt_of_ge (rowInsert_column_le_of_lt
      (antitone_nat_of_succ_le hrows.length_getD_succ_le) (not_le.mp hxy))) h
  · exact rowInsert_column_lt_of_le hrows

end TauCeti

end
end

run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingInsertionCore bumping comparison component processed"
  progressOutput.flush
/- EXACT SOURCE FourPapers.Symmetric.PairedInsertion -/
section

set_option autoImplicit false

/-!
# The actual paired insertion algorithm

The construction here is the algorithm in Section 2 of the paper: insert the smaller
endpoint by ordinary, strict-bumping row insertion and append the larger endpoint
immediately to the right of the newly created box.  This is not ordinary RSK applied
to the symmetric exponent matrix.

The elementary statements below prove content and even-row preservation, the exact
first-row recursion, and semistandardness for insertion of a fresh largest endpoint.
The repeated-endpoint bijection and antidiagonal rank/Greene identities are separate
mathematical assertions; they are not included in the definition of this algorithm.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

/-- One paired-insertion step, including its bumping convention. -/
def pairInsert (a b : α) (rows : List (List α)) : List (List α) :=
  appendToRow b (rowInsertIndex a rows) (rowInsert a rows)

@[simp] theorem pairInsert_nil (a b : α) : pairInsert a b [] = [[a, b]] := rfl

/-- If no entry is bumped out of the first row, both new endpoints stay there. -/
theorem pairInsert_cons_of_none {a b : α} {row : List α} (rows : List (List α))
    (h : (rowBump a row).2 = none) :
    pairInsert a b (row :: rows) = ((rowBump a row).1 ++ [b]) :: rows := by
  simp [pairInsert, rowInsert_cons_of_eq_none rows h,
    rowInsertIndex_cons_of_eq_none rows h]

/-- A letter bumped from the first row becomes the smaller endpoint of the pair
inserted into the lower rows. -/
theorem pairInsert_cons_of_some {a b c : α} {row : List α} (rows : List (List α))
    (h : (rowBump a row).2 = some c) :
    pairInsert a b (row :: rows) = (rowBump a row).1 :: pairInsert c b rows := by
  simp [pairInsert, rowInsert_cons_of_eq_some rows h,
    rowInsertIndex_cons_of_eq_some rows h]

/-- All rows have even length, including the empty rows beyond the diagram.
The explicit witness is definitionally the natural-number predicate `Even`;
it keeps this insertion base independent of the separate parity library. -/
def EvenRows (rows : List (List α)) : Prop :=
  ∀ i, ∃ r : ℕ, (rows.getD i []).length = r + r

@[simp] theorem evenRows_nil : EvenRows ([] : List (List α)) := by
  intro i
  exact ⟨0, by simp⟩

/-- The two boxes of a paired step occur in precisely the same row. -/
theorem length_getD_pairInsert (a b : α) (rows : List (List α)) (i : ℕ) :
    ((pairInsert a b rows).getD i []).length =
      (rows.getD i []).length + if i = rowInsertIndex a rows then 2 else 0 := by
  have hk : rowInsertIndex a rows ≤ (rowInsert a rows).length :=
    by
      rw [length_rowInsert]
      exact (Nat.le_succ _).trans (le_max_right _ _)
  rw [pairInsert, getD_appendToRow b hk]
  split_ifs with hi
  · subst i
    rw [List.length_append, List.length_singleton, length_getD_rowInsert]
    simp only [ite_true]
  · rw [length_getD_rowInsert]
    simp only [if_neg hi, Nat.add_zero]

 theorem EvenRows.pairInsert {rows : List (List α)} (h : EvenRows rows) (a b : α) :
    EvenRows (pairInsert a b rows) := by
  intro i
  rw [length_getD_pairInsert]
  split_ifs
  · obtain ⟨r, hr⟩ := h i
    exact ⟨r + 1, by omega⟩
  · simpa using h i

/-- Paired insertion adds exactly the two endpoint occurrences, with multiplicity. -/
theorem flatten_pairInsert_perm (a b : α) (rows : List (List α)) :
    (pairInsert a b rows).flatten.Perm (a :: b :: rows.flatten) := by
  exact (flatten_appendToRow_perm b (rowInsertIndex a rows) (rowInsert a rows)).trans
    ((List.perm_append_singleton b _).trans
      (((flatten_rowInsert_perm a rows).cons b).trans (List.Perm.swap _ _ _)))

 theorem mem_flatten_pairInsert {a b x : α} {rows : List (List α)} :
    x ∈ (pairInsert a b rows).flatten ↔ x = a ∨ x = b ∨ x ∈ rows.flatten := by
  rw [(flatten_pairInsert_perm a b rows).mem_iff]
  simp

theorem mem_flatten_rowInsert {a x : α} {rows : List (List α)} :
    x ∈ (rowInsert a rows).flatten ↔ x = a ∨ x ∈ rows.flatten := by
  rw [(flatten_rowInsert_perm a rows).mem_iff]
  simp

/-- For a matching, each new larger endpoint is strictly larger than every earlier
endpoint.  Even row lengths then ensure that its appended box remains a corner. -/
theorem isTableauRows_pairInsert_fresh {a b : α} {rows : List (List α)}
    (hrows : rows.IsTableauRows) (heven : EvenRows rows)
    (hab : a < b) (hmax : ∀ x ∈ rows.flatten, x < b) :
    (pairInsert a b rows).IsTableauRows := by
  let k := rowInsertIndex a rows
  have hins := hrows.rowInsert a
  have hk : k ≤ (rowInsert a rows).length :=
    by
      rw [length_rowInsert]
      exact (Nat.le_succ _).trans (le_max_right _ _)
  have hlt (x : α) (hx : x ∈ (rowInsert a rows).flatten) : x < b := by
    rcases mem_flatten_rowInsert.mp hx with rfl | hx
    · exact hab
    · exact hmax x hx
  apply hins.appendToRow hk
  · intro x hx
    exact (hlt x (List.mem_flatten_of_mem_getD hx)).le
  · intro i hki
    have hne : i ≠ k := by omega
    have htop := hins.length_getD_succ_le i
    have hlenTop : ((rowInsert a rows).getD i []).length = (rows.getD i []).length := by
      rw [length_getD_rowInsert]
      simp only [show i ≠ rowInsertIndex a rows from hne, if_false, Nat.add_zero]
    have hlenBot : ((rowInsert a rows).getD k []).length = (rows.getD k []).length + 1 := by
      rw [length_getD_rowInsert]
      simp only [k, ite_true]
    have hlen : ((rowInsert a rows).getD k []).length <
        ((rowInsert a rows).getD i []).length := by
      rw [← hki] at htop
      rw [hlenTop, hlenBot] at htop ⊢
      obtain ⟨s, hs⟩ := heven i
      obtain ⟨t, ht⟩ := heven k
      omega
    exact ⟨hlen, hlt _ (List.mem_flatten_of_mem_getD (List.getElem_mem hlen))⟩

/-- Paired insertion in the order specified by a list of endpoint pairs. -/
def pairInsertList (pairs : List (α × α)) (rows : List (List α) := []) :
    List (List α) :=
  pairs.foldl (fun T p => pairInsert p.1 p.2 T) rows

@[simp] theorem pairInsertList_nil (rows : List (List α)) : pairInsertList [] rows = rows := rfl

@[simp] theorem pairInsertList_cons (p : α × α) (pairs : List (α × α))
    (rows : List (List α)) :
    pairInsertList (p :: pairs) rows = pairInsertList pairs (pairInsert p.1 p.2 rows) := rfl

 theorem pairInsertList_append (xs ys : List (α × α)) (rows : List (List α)) :
    pairInsertList (xs ++ ys) rows = pairInsertList ys (pairInsertList xs rows) := by
  exact List.foldl_append

 theorem EvenRows.pairInsertList {rows : List (List α)} (h : EvenRows rows)
    (pairs : List (α × α)) : EvenRows (pairInsertList pairs rows) := by
  induction pairs generalizing rows with
  | nil => exact h
  | cons p pairs ih => exact ih (h.pairInsert p.1 p.2)

/-- The list of endpoint occurrences of a list of edges. -/
def endpointWord (pairs : List (α × α)) : List α :=
  pairs.flatMap fun p => [p.1, p.2]

 theorem flatten_pairInsertList_perm (pairs : List (α × α)) (rows : List (List α)) :
    (pairInsertList pairs rows).flatten.Perm (endpointWord pairs ++ rows.flatten) := by
  induction pairs generalizing rows with
  | nil => simp [endpointWord]
  | cons p pairs ih =>
    apply (ih (pairInsert p.1 p.2 rows)).trans
    apply ((flatten_pairInsert_perm p.1 p.2 rows).append_left (endpointWord pairs)).trans
    simpa [endpointWord, List.append_assoc] using
      (List.perm_append_comm (l₁ := endpointWord pairs) (l₂ := [p.1, p.2])).append_right rows.flatten


end FourPapers.Symmetric

end

run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingInsertionCore paired-insertion component processed"
  progressOutput.flush
/- EXACT SOURCE FourPapers.Symmetric.MatchingInsertion -/
section

set_option autoImplicit false

/-!
# Reversing paired insertion at a fresh largest endpoint

On a matching, the larger endpoint of the final pair is the unique largest label.
Removing that endpoint identifies the exact row from which to perform reverse row
insertion. The following inverse statements concern the actual algorithm.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

/-- Remove the unique occurrence of a known largest endpoint and reverse the
insertion which created its neighboring box. -/
def reversePairInsert (b : α) (rows : List (List α)) : List (List α) × Option α :=
  let k := (rows.findIdx? fun row => b ∈ row).getD 0
  reverseRowInsert k (dropLastOfRow k rows)

/-- A fresh appended endpoint locates precisely the row created by row insertion. -/
theorem findIdx_pairInsert_fresh {a b : α} {rows : List (List α)}
    (hab : b ≠ a) (hb : b ∉ rows.flatten) :
    (pairInsert a b rows).findIdx? (fun row => b ∈ row) = some (rowInsertIndex a rows) := by
  have hnot : ∀ row ∈ rowInsert a rows, b ∉ row := by
    intro row hr hbr
    have hmem := (flatten_rowInsert_perm a rows).mem_iff.mp
      (List.mem_flatten.mpr ⟨row, hr, hbr⟩)
    simp only [List.mem_cons] at hmem
    exact hmem.elim hab hb
  have hk : rowInsertIndex a rows ≤ (rowInsert a rows).length := by
    rw [length_rowInsert]
    exact (Nat.le_succ _).trans (le_max_right _ _)
  exact findIdx?_mem_appendToRow_self hnot hk

/-- Exact reversal of a paired step at a fresh endpoint. -/
theorem reversePairInsert_pairInsert {a b : α} {rows : List (List α)}
    (hrows : rows.IsTableauRows) (hab : b ≠ a) (hb : b ∉ rows.flatten) :
    reversePairInsert b (pairInsert a b rows) = (rows, some a) := by
  have hk : rowInsertIndex a rows ≤ (rowInsert a rows).length := by
    rw [length_rowInsert]
    exact (Nat.le_succ _).trans (le_max_right _ _)
  rw [reversePairInsert, findIdx_pairInsert_fresh hab hb, Option.getD_some]
  rw [pairInsert, dropLastOfRow_appendToRow b (hrows.rowInsert a).nil_notMem hk]
  exact reverseRowInsert_rowInsert a hrows.nil_notMem hrows.sortedLE

/-- Two matching-insertion steps with the same fresh larger endpoint have the
same input if and only if their output tableaux agree. -/
theorem pairInsert_injective_fresh {a a' b : α} {rows rows' : List (List α)}
    (hrows : rows.IsTableauRows) (hrows' : rows'.IsTableauRows)
    (hab : b ≠ a) (hab' : b ≠ a') (hb : b ∉ rows.flatten) (hb' : b ∉ rows'.flatten)
    (h : pairInsert a b rows = pairInsert a' b rows') : a = a' ∧ rows = rows' := by
  have hrev := congrArg (reversePairInsert b) h
  rw [reversePairInsert_pairInsert hrows hab hb,
    reversePairInsert_pairInsert hrows' hab' hb'] at hrev
  exact ⟨Option.some.inj (congrArg Prod.snd hrev), congrArg Prod.fst hrev⟩

end FourPapers.Symmetric

end

run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingInsertionCore matching insertion component processed"
  progressOutput.flush
/- EXACT SOURCE FourPapers.Symmetric.FirstRowTransducer -/
section

set_option autoImplicit false

/-!
# Actual deletion of the first row by emitted pairs

This executable first-row process reads the same endpoint pairs as paired
insertion. Whenever a letter is bumped out of the first row, it emits that letter
paired with the current larger endpoint. The factorization theorem proves that
these emitted pairs produce exactly the lower rows, at every finite input prefix.
It does not assume or assert the still separate rank-statistic identities.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

/-- Process the top row and retain every actual pair sent to lower rows, in its
chronological order. -/
def firstRowProcess : List (α × α) → List α → List α × List (α × α)
  | [], row => (row, [])
  | (a, b) :: pairs, row =>
      let step := rowBump a row
      match step.2 with
      | none => firstRowProcess pairs (step.1 ++ [b])
      | some c =>
          let remaining := firstRowProcess pairs step.1
          (remaining.1, (c, b) :: remaining.2)

@[simp] theorem firstRowProcess_nil (row : List α) :
    firstRowProcess [] row = (row, []) := rfl

 theorem firstRowProcess_cons_none {a b : α} {pairs : List (α × α)} {row : List α}
    (h : (rowBump a row).2 = none) :
    firstRowProcess ((a, b) :: pairs) row =
      firstRowProcess pairs ((rowBump a row).1 ++ [b]) := by
  simp only [firstRowProcess, h]

 theorem firstRowProcess_cons_some {a b c : α} {pairs : List (α × α)} {row : List α}
    (h : (rowBump a row).2 = some c) :
    firstRowProcess ((a, b) :: pairs) row =
      ((firstRowProcess pairs (rowBump a row).1).1,
        (c, b) :: (firstRowProcess pairs (rowBump a row).1).2) := by
  simp only [firstRowProcess, h]

/-- The emitted pairs, rather than an assumed residual tableau, reconstruct
exactly all rows below the first. This holds for every finite word and every
initial list of rows. -/
theorem pairInsertList_firstRowProcess (pairs : List (α × α))
    (row : List α) (rows : List (List α)) :
    pairInsertList pairs (row :: rows) =
      (firstRowProcess pairs row).1 ::
        pairInsertList (firstRowProcess pairs row).2 rows := by
  induction pairs generalizing row rows with
  | nil => rfl
  | cons p pairs ih =>
    rcases p with ⟨a, b⟩
    rw [pairInsertList_cons]
    cases h : (rowBump a row).2 with
    | none =>
      rw [pairInsert_cons_of_none rows h, firstRowProcess_cons_none h]
      exact ih _ _
    | some c =>
      rw [pairInsert_cons_of_some rows h, firstRowProcess_cons_some h]
      simpa only [pairInsertList_cons] using ih (rowBump a row).1 (pairInsert c b rows)

/-- Starting from the empty tableau, actual first-row deletion equals paired
insertion of the emitted word. Empty words and empty residual tableaux are included. -/
theorem pairInsertList_tail (pairs : List (α × α)) :
    (pairInsertList pairs).tail = pairInsertList (firstRowProcess pairs []).2 := by
  cases pairs with
  | nil => rfl
  | cons p pairs =>
    rcases p with ⟨a, b⟩
    rw [pairInsertList_cons, pairInsert_nil, pairInsertList_firstRowProcess]
    simp only [List.tail_cons, firstRowProcess, rowBump_nil, List.singleton_append]

/-- The top row together with the emitted endpoints preserves the exact content
of the input, including multiplicity. -/
theorem firstRowProcess_content (pairs : List (α × α)) (row : List α) :
    ((firstRowProcess pairs row).1 ++ endpointWord (firstRowProcess pairs row).2).Perm
      (endpointWord pairs ++ row) := by
  have hfull := flatten_pairInsertList_perm pairs [row]
  rw [pairInsertList_firstRowProcess] at hfull
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hfull
  have hemitted := flatten_pairInsertList_perm (firstRowProcess pairs row).2 []
  simp only [List.flatten_nil, List.append_nil] at hemitted
  exact (hemitted.symm.append_left _).trans hfull

/-- Every endpoint prefix has the same exact deletion description. No relation
between a later prefix and an earlier one is silently assumed. -/
theorem pairedPrefixTableau_tail_word (pairs : List (α × α)) (q : α) :
    (pairInsertList (pairs.filter fun p => p.2 ≤ q)).tail =
      pairInsertList (firstRowProcess (pairs.filter fun p => p.2 ≤ q) []).2 :=
  pairInsertList_tail _

end FourPapers.Symmetric

end

run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingInsertionCore first-row transducer component processed"
  progressOutput.flush
/- EXACT SOURCE FourPapers.Symmetric.FirstRowMerge -/
section

set_option autoImplicit false

/-!
# Greedy matching in an actual first insertion row

For a fixed larger endpoint `b`, the increasing sequence of smaller endpoints is
matched greedily against the old first row. An old entry at most the current input
stays in the row; an old entry strictly above it is bumped and emitted. Once the
old row is exhausted, pairs of unmatched inputs emit `(b,b)`, and one unmatched
input leaves one `b` in the row. These are the mechanisms behind the min/parity
carrier formulas, proved here as identities of the actual insertion algorithm.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

/-- Entries already passed by every incoming lower endpoint remain untouched. -/
theorem firstRowProcess_passed_prefix (pairs : List (α × α)) (before row : List α)
    (hle : ∀ p ∈ pairs, ∀ z ∈ before, z ≤ p.1) :
    firstRowProcess pairs (before ++ row) =
      (before ++ (firstRowProcess pairs row).1, (firstRowProcess pairs row).2) := by
  induction pairs generalizing row with
  | nil => rfl
  | cons p pairs ih =>
    have hcur : ∀ z ∈ before, z ≤ p.1 := fun z hz => hle p (by simp) z hz
    have htail : ∀ q ∈ pairs, ∀ z ∈ before, z ≤ q.1 :=
      fun q hq z hz => hle q (List.mem_cons_of_mem _ hq) z hz
    have hb := rowBump_append p.1 before row hcur
    cases h : (rowBump p.1 row).2 with
    | none =>
      simp only [firstRowProcess, hb, h, List.append_assoc]
      exact ih _ htail
    | some c =>
      simp only [firstRowProcess, hb, h, ih _ htail]

/-- A current input below the old first entry consumes that old entry and emits
its pair. Later weakly larger inputs do not disturb the new first entry. -/
theorem firstRowProcess_match {a b c : α} (pairs : List (α × α)) (row : List α)
    (hac : a < c) (hfuture : ∀ p ∈ pairs, a ≤ p.1) :
    firstRowProcess ((a, b) :: pairs) (c :: row) =
      (a :: (firstRowProcess pairs row).1, (c, b) :: (firstRowProcess pairs row).2) := by
  have hp := firstRowProcess_passed_prefix pairs [a] row (by
    intro p hp z hz
    have hz' : z = a := List.mem_singleton.mp hz
    subst z
    exact hfuture p hp)
  simp only [List.singleton_append] at hp
  simp only [firstRowProcess, rowBump_cons_of_lt row hac, hp]

/-- Two unmatched lower endpoints consume one another's appended largest marker. -/
theorem firstRowProcess_empty_pair {a c b : α} (pairs : List (α × α))
    (hac : a ≤ c) (hcb : c < b) (hfuture : ∀ p ∈ pairs, c ≤ p.1) :
    firstRowProcess ((a, b) :: (c, b) :: pairs) [] =
      (a :: c :: (firstRowProcess pairs []).1, (b, b) :: (firstRowProcess pairs []).2) := by
  have hp := firstRowProcess_passed_prefix pairs [a, c] [] (by
    intro p hp z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hac.trans (hfuture p hp)
    · exact hfuture p hp)
  simp only [List.append_nil, List.cons_append, List.nil_append] at hp
  have hb : rowBump c [a, b] = ([a, c], some b) := by
    rw [rowBump_cons_of_le _ hac, rowBump_cons_of_lt _ hcb]
  simp only [firstRowProcess, rowBump_nil, List.singleton_append, hb, hp]

/-- The greedy first-row merge, including the unmatched-input parity rule. -/
def carrierMerge (b : α) (row incoming : List α) : List α × List (α × α) :=
  match row, incoming with
  | row, [] => (row, [])
  | [], [a] => ([a, b], [])
  | [], a :: c :: incoming =>
      let result := carrierMerge b [] incoming
      (a :: c :: result.1, (b, b) :: result.2)
  | c :: row, a :: incoming =>
      if a < c then
        let result := carrierMerge b row incoming
        (a :: result.1, (c, b) :: result.2)
      else
        let result := carrierMerge b row (a :: incoming)
        (c :: result.1, result.2)
termination_by row.length + incoming.length

decreasing_by all_goals simp_wf <;> omega

theorem firstRowProcess_eq_carrierMerge_aux (d : ℕ) :
    ∀ (b : α) (row incoming : List α), row.length + incoming.length = d →
      incoming.SortedLE → (∀ a ∈ incoming, a < b) →
      firstRowProcess (incoming.map fun a => (a, b)) row = carrierMerge b row incoming := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro b row incoming hlength hsorted hmax
    cases incoming with
    | nil => simp [firstRowProcess, carrierMerge]
    | cons a incoming =>
      have ha := (List.sortedLE_cons.mp hsorted).1
      have htail := (List.sortedLE_cons.mp hsorted).2
      cases row with
      | nil =>
        cases incoming with
        | nil => simp [firstRowProcess, carrierMerge, rowBump_nil]
        | cons c incoming =>
          have hci := (List.sortedLE_cons.mp htail).1
          have hsorted' := (List.sortedLE_cons.mp htail).2
          have hsize : ([] : List α).length + incoming.length < d := by
            simp only [List.length_nil, List.length_cons] at hlength ⊢
            omega
          have hrec := ih _ hsize b [] incoming rfl hsorted'
            (fun x hx => hmax x (by simp [hx]))
          simp only [List.map_cons]
          rw [firstRowProcess_empty_pair _ (ha c (by simp)) (hmax c (by simp)) (by
            intro p hp
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
            exact hci x hx)]
          simp only [carrierMerge, hrec]
      | cons c row =>
        by_cases hac : a < c
        · have hsize : row.length + incoming.length < d := by
            simp only [List.length_cons] at hlength
            omega
          have hrec := ih _ hsize b row incoming rfl htail
            (fun x hx => hmax x (List.mem_cons_of_mem _ hx))
          simp only [List.map_cons]
          rw [firstRowProcess_match _ row hac (by
            intro p hp
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
            exact ha x hx)]
          simp only [carrierMerge, hac, ite_true, hrec]
        · have hca : c ≤ a := le_of_not_gt hac
          have hsize : row.length + (a :: incoming).length < d := by
            simp only [List.length_cons] at hlength ⊢
            omega
          have hrec := ih _ hsize b row (a :: incoming) rfl hsorted hmax
          have hp := firstRowProcess_passed_prefix
            ((a :: incoming).map fun x => (x, b)) [c] row (by
              intro p hp z hz
              have hzc : z = c := List.mem_singleton.mp hz
              subst z
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hca
              · exact hca.trans (ha x hx))
          simpa only [List.singleton_append, carrierMerge, hac, ite_false, hrec] using hp

/-- The entire fixed-endpoint first-row process is the greedy merge, uniformly
for arbitrary row length, input length, and multiplicities. The strict bound on
incoming letters is separated from diagonal loop insertions. -/
theorem firstRowProcess_eq_carrierMerge (b : α) (row incoming : List α)
    (hsorted : incoming.SortedLE) (hmax : ∀ a ∈ incoming, a < b) :
    firstRowProcess (incoming.map fun a => (a, b)) row = carrierMerge b row incoming :=
  firstRowProcess_eq_carrierMerge_aux (row.length + incoming.length)
    b row incoming rfl hsorted hmax

end FourPapers.Symmetric

end

run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingInsertionCore first-row merge component processed"
  progressOutput.flush
/- EXACT SOURCE FourPapers.Symmetric.CarrierRowCounts -/
section

set_option autoImplicit false

/-!
# The min and parity carrier rules as actual row-processing identities

These formulas concern the executable paired-insertion first-row process. They
retain arbitrary input multiplicities. In the off-diagonal rule, every demanded
letter is strictly below the current carrier letter. The diagonal rule handles
all unmatched demands and all original loops in one exact identity.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

/-- Greedy absorption of a whole carrier block consumes exactly the smaller of
its multiplicity and the number of waiting demands. -/
theorem carrierMerge_replicate_prefix (b c : α) (p : ℕ)
    (row incoming : List α) (hlt : ∀ a ∈ incoming, a < c) :
    carrierMerge b (List.replicate p c ++ row) incoming =
      (incoming.take p ++
        (carrierMerge b (List.replicate (p - incoming.length) c ++ row)
          (incoming.drop p)).1,
       List.replicate (min p incoming.length) (c, b) ++
        (carrierMerge b (List.replicate (p - incoming.length) c ++ row)
          (incoming.drop p)).2) := by
  induction p generalizing incoming with
  | zero => simp
  | succ p ih =>
    cases incoming with
    | nil => simp [carrierMerge]
    | cons a incoming =>
      have hac := hlt a (by simp)
      have htail : ∀ z ∈ incoming, z < c :=
        fun z hz => hlt z (List.mem_cons_of_mem _ hz)
      have hsub : p + 1 - (incoming.length + 1) = p - incoming.length := by omega
      have hmin : min (p + 1) (incoming.length + 1) = min p incoming.length + 1 := by omega
      simp only [List.replicate_succ, List.cons_append, carrierMerge, hac, ite_true,
        ih incoming htail, List.take_succ_cons, List.drop_succ_cons, List.length_cons,
        hsub, hmin]

/-- The same min-rule for actual paired insertion. This is not a statement about
an independently postulated carrier model. -/
theorem firstRowProcess_offDiagonal_block (b c : α) (p : ℕ)
    (row incoming : List α) (hsorted : incoming.SortedLE)
    (hlt : ∀ a ∈ incoming, a < c) (hcb : c ≤ b) :
    firstRowProcess (incoming.map fun a => (a, b)) (List.replicate p c ++ row) =
      (incoming.take p ++
        (firstRowProcess ((incoming.drop p).map fun a => (a, b))
          (List.replicate (p - incoming.length) c ++ row)).1,
       List.replicate (min p incoming.length) (c, b) ++
        (firstRowProcess ((incoming.drop p).map fun a => (a, b))
          (List.replicate (p - incoming.length) c ++ row)).2) := by
  have hmax : ∀ a ∈ incoming, a < b := fun a ha => (hlt a ha).trans_le hcb
  have hdrop : ∀ a ∈ incoming.drop p, a < b :=
    fun a ha => hmax a (List.mem_of_mem_drop ha)
  rw [firstRowProcess_eq_carrierMerge b _ incoming hsorted hmax,
    firstRowProcess_eq_carrierMerge b _ (incoming.drop p) (hsorted.pairwise.drop (i := p)).sortedLE hdrop]
  exact carrierMerge_replicate_prefix b c p row incoming hlt

/-- A whole old carrier block is retained once all remaining input letters are
at least its label. -/
theorem carrierMerge_passed_replicate (b c : α) (p : ℕ) (row incoming : List α)
    (hle : ∀ a ∈ incoming, c ≤ a) :
    carrierMerge b (List.replicate p c ++ row) incoming =
      (List.replicate p c ++ (carrierMerge b row incoming).1,
        (carrierMerge b row incoming).2) := by
  induction p with
  | zero => simp
  | succ p ih =>
    cases incoming with
    | nil => simp [carrierMerge]
    | cons a incoming =>
      have hnot : ¬a < c := not_lt.mpr (hle a (by simp))
      simp only [List.replicate_succ, List.cons_append, carrierMerge, hnot, ite_false, ih]

/-- One complete alphabet step of the greedy merge. Only waiting demands below
`c` can consume its old copies; the remaining input, starting at `c`, cannot. -/
theorem carrierMerge_alphabet_step (b c : α) (p : ℕ)
    (row demands later : List α) (hlt : ∀ a ∈ demands, a < c)
    (hle : ∀ a ∈ later, c ≤ a) :
    carrierMerge b (List.replicate p c ++ row) (demands ++ later) =
      (demands.take p ++ List.replicate (p - demands.length) c ++
        (carrierMerge b row (demands.drop p ++ later)).1,
       List.replicate (min p demands.length) (c, b) ++
        (carrierMerge b row (demands.drop p ++ later)).2) := by
  induction p generalizing demands with
  | zero => simp
  | succ p ih =>
    cases demands with
    | nil => simpa using carrierMerge_passed_replicate b c (p + 1) row later hle
    | cons a demands =>
      have hac := hlt a (by simp)
      have htail : ∀ z ∈ demands, z < c :=
        fun z hz => hlt z (List.mem_cons_of_mem _ hz)
      have hsub : p + 1 - (demands.length + 1) = p - demands.length := by omega
      have hmin : min (p + 1) (demands.length + 1) = min p demands.length + 1 := by omega
      simp only [List.replicate_succ, List.cons_append, carrierMerge, hac, ite_true,
        ih demands htail, List.take_succ_cons, List.drop_succ_cons, List.length_cons,
        hsub, hmin]

/-- The exact one-letter scan recurrence of the actual row processor. This
identifies the emitted multiplicity, retained old copies, and the remaining input
word simultaneously, rather than proving only conservation of total weight. -/
theorem firstRowProcess_alphabet_step (b c : α) (p : ℕ)
    (row demands later : List α) (hsorted : (demands ++ later).SortedLE)
    (hmax : ∀ a ∈ demands ++ later, a < b)
    (hlt : ∀ a ∈ demands, a < c) (hle : ∀ a ∈ later, c ≤ a) :
    firstRowProcess ((demands ++ later).map fun a => (a, b))
      (List.replicate p c ++ row) =
      (demands.take p ++ List.replicate (p - demands.length) c ++
        (firstRowProcess ((demands.drop p ++ later).map fun a => (a, b)) row).1,
       List.replicate (min p demands.length) (c, b) ++
        (firstRowProcess ((demands.drop p ++ later).map fun a => (a, b)) row).2) := by
  have hs := List.sortedLE_append.mp hsorted
  have hsorted' : (demands.drop p ++ later).SortedLE := by
    exact List.sortedLE_append.mpr ⟨(hs.1.pairwise.drop (i := p)).sortedLE, hs.2.1,
      fun a ha z hz => hs.2.2 a (List.mem_of_mem_drop ha) z hz⟩
  have hmax' : ∀ a ∈ demands.drop p ++ later, a < b := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hmax a (List.mem_append_left _ (List.mem_of_mem_drop ha))
    · exact hmax a (List.mem_append_right _ ha)
  rw [firstRowProcess_eq_carrierMerge b _ _ hsorted hmax,
    firstRowProcess_eq_carrierMerge b _ _ hsorted' hmax']
  exact carrierMerge_alphabet_step b c p row demands later hlt hle

/-- The waiting-demand count after consuming old carriers and introducing new
copies of the current letter is precisely the second coordinate of (3.2). -/
theorem remaining_demand_length (demands : List α) (c : α) (p r : ℕ) :
    (demands.drop p ++ List.replicate r c).length =
      demands.length - min p demands.length + r := by
  simp only [List.length_append, List.length_drop, List.length_replicate]
  omega

theorem carrierMerge_empty_aux (d : ℕ) :
    ∀ (b : α) (incoming : List α), incoming.length = d →
      carrierMerge b [] incoming =
        (incoming ++ List.replicate (incoming.length % 2) b,
          List.replicate (incoming.length / 2) (b, b)) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro b incoming hlen
    cases incoming with
    | nil => simp [carrierMerge]
    | cons a incoming =>
      cases incoming with
      | nil => simp [carrierMerge]
      | cons c incoming =>
        have hsize : incoming.length < d := by
          simp only [List.length_cons] at hlen
          omega
        have hrec := ih incoming.length hsize b incoming rfl
        have hmod : (incoming.length + 1 + 1) % 2 = incoming.length % 2 := by omega
        have hdiv : (incoming.length + 1 + 1) / 2 = incoming.length / 2 + 1 := by omega
        simp only [carrierMerge, hrec, List.length_cons, hmod, hdiv,
          List.cons_append, List.replicate_succ]

/-- Once the old carriers are exhausted, two unmatched demands produce one
residual loop, while an odd demand leaves one largest-endpoint entry. -/
theorem carrierMerge_empty (b : α) (incoming : List α) :
    carrierMerge b [] incoming =
      (incoming ++ List.replicate (incoming.length % 2) b,
        List.replicate (incoming.length / 2) (b, b)) :=
  carrierMerge_empty_aux incoming.length b incoming rfl

/-- Every emitted lower endpoint comes from an old carrier or from the largest
marker `b`; an incoming lower endpoint itself is retained in the first row. -/
theorem carrierMerge_emitted_entries (b : α) (row incoming : List α) :
    ∀ p ∈ (carrierMerge b row incoming).2, p.2 = b ∧ (p.1 ∈ row ∨ p.1 = b) := by
  induction row generalizing incoming with
  | nil =>
    rw [carrierMerge_empty]
    intro p hp
    have hp' := List.eq_of_mem_replicate hp
    subst p
    exact ⟨rfl, Or.inr rfl⟩
  | cons c row ih =>
    cases incoming with
    | nil => simp [carrierMerge]
    | cons a incoming =>
      by_cases hac : a < c
      · simp only [carrierMerge, hac, ite_true]
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨rfl, Or.inl (by simp)⟩
        · obtain ⟨hpb, hprow | hpb'⟩ := ih incoming p hp
          · exact ⟨hpb, Or.inl (List.mem_cons_of_mem _ hprow)⟩
          · exact ⟨hpb, Or.inr hpb'⟩
      · simp only [carrierMerge, hac, ite_false]
        intro p hp
        obtain ⟨hpb, hprow | hpb'⟩ := ih (a :: incoming) p hp
        · exact ⟨hpb, Or.inl (List.mem_cons_of_mem _ hprow)⟩
        · exact ⟨hpb, Or.inr hpb'⟩

/-- With no old copy of `z` and with largest marker different from `z`, every
copy of `z` in the final row comes from an incoming copy, with its multiplicity. -/
theorem carrierMerge_count_of_not_mem (b z : α) (row incoming : List α)
    (hz : z ∉ row) (hzb : z ≠ b) :
    (carrierMerge b row incoming).1.count z = incoming.count z := by
  induction row generalizing incoming with
  | nil =>
    rw [carrierMerge_empty]
    simp [List.count_append, List.count_replicate, hzb, hzb.symm]
  | cons c row ih =>
    have hzc : z ≠ c := fun h => hz (by simp [h])
    have hzrow : z ∉ row := fun h => hz (List.mem_cons_of_mem _ h)
    cases incoming with
    | nil => simp [carrierMerge, List.count_eq_zero_of_not_mem hz]
    | cons a incoming =>
      by_cases hac : a < c
      · simp only [carrierMerge, hac, ite_true, List.count_cons, ih incoming hzrow]
      · simp [carrierMerge, hac, List.count_cons, ih (a :: incoming) hzrow, hzc, hzc.symm]

/-- Formula (3.2) at the level of actual insertion multiplicities. The third
coordinate is the exact emitted pair count, and the first is the exact retained
carrier count. Together with `remaining_demand_length`, all three coordinates
agree with the manuscript's min-rule for unrestricted natural multiplicities. -/
theorem firstRowProcess_offDiagonal_counts (b c : α) (p r : ℕ)
    (row demands later : List α)
    (hsorted : (demands ++ List.replicate r c ++ later).SortedLE)
    (hmax : ∀ a ∈ demands ++ List.replicate r c ++ later, a < b)
    (hlt : ∀ a ∈ demands, a < c) (hlater : ∀ a ∈ later, c < a)
    (hcrow : c ∉ row) (hcb : c < b) :
    let out := firstRowProcess
      ((demands ++ List.replicate r c ++ later).map fun a => (a, b))
      (List.replicate p c ++ row)
    out.1.count c = p - min p demands.length + r ∧
      out.2.count (c, b) = min p demands.length := by
  dsimp only
  rw [firstRowProcess_eq_carrierMerge b _ _ hsorted hmax]
  have hle : ∀ a ∈ List.replicate r c ++ later, c ≤ a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have hac : a = c := List.eq_of_mem_replicate ha
      exact hac.symm.le
    · exact (hlater a ha).le
  simp only [List.append_assoc]
  rw [carrierMerge_alphabet_step b c p row demands (List.replicate r c ++ later) hlt hle]
  let rest := demands.drop p ++ (List.replicate r c ++ later)
  have htake : c ∉ demands.take p := by
    intro h
    exact (lt_irrefl c) (hlt c (List.mem_of_mem_take h))
  have hdrop : c ∉ demands.drop p := by
    intro h
    exact (lt_irrefl c) (hlt c (List.mem_of_mem_drop h))
  have hlater' : c ∉ later := by
    intro h
    exact (lt_irrefl c) (hlater c h)
  have hrestcount : rest.count c = r := by
    simp [rest, List.count_append, List.count_eq_zero_of_not_mem hdrop,
      List.count_eq_zero_of_not_mem hlater']
  have hrowcount : (carrierMerge b row rest).1.count c = r :=
    (carrierMerge_count_of_not_mem b c row rest hcrow hcb.ne).trans hrestcount
  have hemit : (c, b) ∉ (carrierMerge b row rest).2 := by
    intro h
    obtain ⟨hb, hc | hc⟩ := carrierMerge_emitted_entries b row rest (c, b) h
    · exact hcrow hc
    · exact hcb.ne hc
  have hemitcount := List.count_eq_zero_of_not_mem hemit
  change (demands.take p ++ List.replicate (p - demands.length) c ++
      (carrierMerge b row rest).1).count c = p - min p demands.length + r ∧
    (List.replicate (min p demands.length) (c, b) ++
      (carrierMerge b row rest).2).count (c, b) = min p demands.length
  simp only [List.count_append, List.count_replicate_self,
    List.count_eq_zero_of_not_mem htake, Nat.zero_add]
  rw [hrowcount, hemitcount]
  constructor <;> omega

 theorem firstRowProcess_empty (b : α) (incoming : List α)
    (hsorted : incoming.SortedLE) (hmax : ∀ a ∈ incoming, a < b) :
    firstRowProcess (incoming.map fun a => (a, b)) [] =
      (incoming ++ List.replicate (incoming.length % 2) b,
        List.replicate (incoming.length / 2) (b, b)) := by
  rw [firstRowProcess_eq_carrierMerge b [] incoming hsorted hmax, carrierMerge_empty]

/-- Composition retains the chronological order of every emitted pair. -/
theorem firstRowProcess_append (xs ys : List (α × α)) (row : List α) :
    firstRowProcess (xs ++ ys) row =
      ((firstRowProcess ys (firstRowProcess xs row).1).1,
        (firstRowProcess xs row).2 ++ (firstRowProcess ys (firstRowProcess xs row).1).2) := by
  induction xs generalizing row with
  | nil => simp [firstRowProcess]
  | cons p xs ih =>
    rcases p with ⟨a, b⟩
    cases h : (rowBump a row).2 <;>
      simp only [List.cons_append, firstRowProcess, h, ih]

/-- Original loops append two largest entries each and emit no residual pair. -/
theorem firstRowProcess_loops (b : α) (r : ℕ) (row : List α)
    (hmax : ∀ a ∈ row, a ≤ b) :
    firstRowProcess (List.replicate r (b, b)) row =
      (row ++ List.replicate (2 * r) b, []) := by
  induction r generalizing row with
  | zero => simp [firstRowProcess]
  | succ r ih =>
    have hb := rowBump_of_forall_le b row hmax
    have hnone : (rowBump b row).2 = none := by rw [hb]
    rw [List.replicate_succ, firstRowProcess_cons_none hnone]
    simp only [hb]
    have hmax' : ∀ a ∈ (row ++ [b]) ++ [b], a ≤ b := by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | rfl) | rfl
      · exact hmax a ha
      · exact le_rfl
      · exact le_rfl
    rw [ih _ hmax']
    have htwo : 2 * (r + 1) = 2 + 2 * r := by omega
    rw [htwo, List.replicate_add]
    simp only [List.append_assoc, List.replicate_succ, List.replicate_zero,
      List.singleton_append, List.cons_append, List.nil_append]

/-- The exact diagonal carrier rule, with all waiting demands and all original
loops. The retained largest-endpoint multiplicity is `q % 2 + 2*r`, and the
emitted residual loop multiplicity is `q / 2`, where `q = incoming.length`. -/
theorem firstRowProcess_diagonal_block (b : α) (incoming : List α) (r : ℕ)
    (hsorted : incoming.SortedLE) (hmax : ∀ a ∈ incoming, a < b) :
    firstRowProcess ((incoming.map fun a => (a, b)) ++ List.replicate r (b, b)) [] =
      (incoming ++ List.replicate (incoming.length % 2 + 2 * r) b,
        List.replicate (incoming.length / 2) (b, b)) := by
  rw [firstRowProcess_append, firstRowProcess_empty b incoming hsorted hmax]
  have hrow : ∀ a ∈ incoming ++ List.replicate (incoming.length % 2) b, a ≤ b := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hmax a ha).le
    · have hab : a = b := List.eq_of_mem_replicate ha
      exact hab.le
  rw [firstRowProcess_loops b r _ hrow]
  simp only [List.append_nil, List.replicate_add, List.append_assoc]

end FourPapers.Symmetric

end

