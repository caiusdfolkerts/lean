module

public import higher_specht.verified.basis_foundation

/- Generated ordinary proof stage. See audit/staged_specht_basis/Basis01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/LascouxFirstLowering.lean -/



/-!
# The first shape-preserving Lascoux lowering step

If a semistandard tableau contains more zeros than ones, its rightmost zero
can be changed to a one. The resulting tableau has exactly the same shape and
the operation is injective: its changed cell is the first one in the first row.
The column inequality is derived from the actual content count, by injecting
all zero columns into one-cells if a one occurred below the changed cell.
-/

noncomputable section
open Finset
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

def zeroColumns (T : SemistandardYoungTableau mu) : Finset ℕ :=
  (range (mu.rowLen 0)).filter (fun j => T 0 j = 0)

def contentCells (T : SemistandardYoungTableau mu) (a : ℕ) : Finset (ℕ × ℕ) :=
  mu.cells.filter (fun c => T c.1 c.2 = a)

theorem mem_zeroColumns {T : SemistandardYoungTableau mu} {j : ℕ} :
    j ∈ zeroColumns T ↔ (0, j) ∈ mu ∧ T 0 j = 0 := by
  simp only [zeroColumns, mem_filter, mem_range, YoungDiagram.mem_iff_lt_rowLen]

theorem zero_cell_row {T : SemistandardYoungTableau mu} {i j : ℕ}
    (hc : (i, j) ∈ mu) (hz : T i j = 0) : i = 0 := by
  by_contra hi
  have h := T.col_strict (Nat.pos_of_ne_zero hi) hc
  omega

theorem contentCells_zero (T : SemistandardYoungTableau mu) :
    contentCells T 0 = (zeroColumns T).image (fun j => (0, j)) := by
  ext c
  rcases c with ⟨i, j⟩
  constructor
  · intro hc
    obtain ⟨hcm, hcz⟩ := mem_filter.mp hc
    have hi := zero_cell_row hcm hcz
    subst i
    exact mem_image.mpr ⟨j, mem_zeroColumns.mpr ⟨hcm, hcz⟩, rfl⟩
  · intro hc
    obtain ⟨l, hl, heq⟩ := mem_image.mp hc
    rw [← heq]
    exact mem_filter.mpr (mem_zeroColumns.mp hl)

theorem zeroColumns_card (T : SemistandardYoungTableau mu) :
    (zeroColumns T).card = (contentCells T 0).card := by
  rw [contentCells_zero, Finset.card_image_of_injective]
  intro i j hij
  exact congrArg Prod.snd hij

def FirstLoweringDomain (mu : YoungDiagram) :=
  {T : SemistandardYoungTableau mu // (contentCells T 1).card < (contentCells T 0).card}

theorem zeroColumns_nonempty (T : FirstLoweringDomain mu) : (zeroColumns T.val).Nonempty := by
  rw [← Finset.card_pos, zeroColumns_card]
  exact lt_of_le_of_lt (Nat.zero_le _) T.property

def lastZeroColumn (T : FirstLoweringDomain mu) : ℕ :=
  (zeroColumns T.val).max' (zeroColumns_nonempty T)

theorem lastZeroColumn_mem (T : FirstLoweringDomain mu) :
    lastZeroColumn T ∈ zeroColumns T.val := Finset.max'_mem _ _

theorem lastZeroColumn_cell (T : FirstLoweringDomain mu) :
    (0, lastZeroColumn T) ∈ mu := (mem_zeroColumns.mp (lastZeroColumn_mem T)).1

theorem lastZeroColumn_value (T : FirstLoweringDomain mu) :
    T.val 0 (lastZeroColumn T) = 0 := (mem_zeroColumns.mp (lastZeroColumn_mem T)).2

theorem zero_before_last (T : FirstLoweringDomain mu) {j : ℕ}
    (hj : j ≤ lastZeroColumn T) : T.val 0 j = 0 := by
  have h := T.val.row_weak_of_le hj (lastZeroColumn_cell T)
  rw [lastZeroColumn_value] at h
  omega

theorem positive_after_last (T : FirstLoweringDomain mu) {j : ℕ}
    (hj : lastZeroColumn T < j) (hc : (0, j) ∈ mu) : 0 < T.val 0 j := by
  by_contra h
  have hz : T.val 0 j = 0 := by omega
  have hmem := mem_zeroColumns.mpr ⟨hc, hz⟩
  have hle := Finset.le_max' (zeroColumns T.val) j hmem
  exact (Nat.not_lt_of_ge hle) hj

theorem greater_one_below_last (T : FirstLoweringDomain mu) {i : ℕ}
    (hi : 0 < i) (hc : (i, lastZeroColumn T) ∈ mu) : 1 < T.val i (lastZeroColumn T) := by
  have hpos := T.val.col_strict hi hc
  rw [lastZeroColumn_value] at hpos
  by_contra hnot
  have heq : T.val i (lastZeroColumn T) = 1 := by omega
  have hm (j : ℕ) (hj : j ∈ zeroColumns T.val) :
      (i, j) ∈ contentCells T.val 1 := by
    have hjle : j ≤ lastZeroColumn T := Finset.le_max' (zeroColumns T.val) j hj
    have hcell : (i, j) ∈ mu := mu.up_left_mem le_rfl hjle hc
    have hlo : 0 < T.val i j :=
      (Nat.zero_le (T.val 0 j)).trans_lt (T.val.col_strict hi hcell)
    have hhi : T.val i j ≤ 1 := (T.val.row_weak_of_le hjle hc).trans_eq heq
    have hvalue : T.val i j = 1 := le_antisymm hhi (Nat.succ_le_of_lt hlo)
    exact mem_filter.mpr ⟨hcell, hvalue⟩
  have hcard : (zeroColumns T.val).card ≤ (contentCells T.val 1).card :=
    Finset.card_le_card_of_injOn (fun j => (i, j)) hm (by
      intro a ha b hb hab
      exact congrArg Prod.snd hab)
  rw [zeroColumns_card] at hcard
  exact (Nat.not_lt_of_ge hcard) T.property

def firstLowering (T : FirstLoweringDomain mu) : SemistandardYoungTableau mu where
  entry i j := if i = 0 ∧ j = lastZeroColumn T then 1 else T.val i j
  row_weak' {i j k} hj hk := by
    by_cases hij : i = 0 ∧ j = lastZeroColumn T
    · obtain ⟨rfl, rfl⟩ := hij
      have hkn : k ≠ lastZeroColumn T := Nat.ne_of_gt hj
      simp only [true_and, if_pos rfl, hkn, if_false]
      exact Nat.succ_le_of_lt (positive_after_last T hj hk)
    · by_cases hik : i = 0 ∧ k = lastZeroColumn T
      · obtain ⟨rfl, rfl⟩ := hik
        have hz := zero_before_last T hj.le
        have hjne : j ≠ lastZeroColumn T := Nat.ne_of_lt hj
        simp [hjne, hz]
      · simp only [hij, hik, if_false]
        exact T.val.row_weak hj hk
  col_strict' {i k j} hik hkj := by
    by_cases hij : i = 0 ∧ j = lastZeroColumn T
    · obtain ⟨rfl, rfl⟩ := hij
      have hk : k ≠ 0 := Nat.ne_of_gt hik
      simp only [true_and, if_pos rfl, hk, false_and, if_false]
      exact greater_one_below_last T hik hkj
    · have hkj' : ¬ (k = 0 ∧ j = lastZeroColumn T) := by omega
      simp only [hij, hkj', if_false]
      exact T.val.col_strict hik hkj
  zeros' {i j} hc := by
    have hne : ¬ (i = 0 ∧ j = lastZeroColumn T) := by
      rintro ⟨rfl, rfl⟩
      exact hc (lastZeroColumn_cell T)
    simp only [hne, if_false]
    exact T.val.zeros hc

@[simp] theorem firstLowering_apply (T : FirstLoweringDomain mu) (i j : ℕ) :
    firstLowering T i j = if i = 0 ∧ j = lastZeroColumn T then 1 else T.val i j := rfl

theorem contentCells_firstLowering_zero (T : FirstLoweringDomain mu) :
    contentCells (firstLowering T) 0 =
      (contentCells T.val 0).erase (0, lastZeroColumn T) := by
  ext c
  by_cases hc : c = (0, lastZeroColumn T)
  · subst c
    simp [contentCells, firstLowering_apply, lastZeroColumn_cell, lastZeroColumn_value]
  · have hne : ¬ (c.1 = 0 ∧ c.2 = lastZeroColumn T) := by
      rintro ⟨h1, h2⟩
      exact hc (Prod.ext h1 h2)
    simp only [contentCells, mem_filter, mem_erase, firstLowering_apply,
      if_neg hne, ne_eq, hc, not_false_eq_true, true_and]

theorem contentCells_firstLowering_one (T : FirstLoweringDomain mu) :
    contentCells (firstLowering T) 1 =
      insert (0, lastZeroColumn T) (contentCells T.val 1) := by
  ext c
  by_cases hc : c = (0, lastZeroColumn T)
  · subst c
    simp [contentCells, firstLowering_apply, lastZeroColumn_cell, lastZeroColumn_value]
  · have hne : ¬ (c.1 = 0 ∧ c.2 = lastZeroColumn T) := by
      rintro ⟨h1, h2⟩
      exact hc (Prod.ext h1 h2)
    simp only [contentCells, mem_filter, mem_insert, firstLowering_apply,
      if_neg hne, hc, false_or]

theorem contentCells_firstLowering_other (T : FirstLoweringDomain mu) {a : ℕ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    contentCells (firstLowering T) a = contentCells T.val a := by
  ext c
  simp only [contentCells, mem_filter, firstLowering_apply]
  by_cases hc : c.1 = 0 ∧ c.2 = lastZeroColumn T
  · obtain ⟨h1, h2⟩ := hc
    simp only [h1, h2, and_self, if_true, lastZeroColumn_value, Ne.symm ha0,
      Ne.symm ha1]
  · simp only [hc, if_false]

theorem firstLowering_content_zero (T : FirstLoweringDomain mu) :
    (contentCells (firstLowering T) 0).card + 1 = (contentCells T.val 0).card := by
  rw [contentCells_firstLowering_zero, Finset.card_erase_add_one]
  exact mem_filter.mpr ⟨lastZeroColumn_cell T, lastZeroColumn_value T⟩

theorem firstLowering_content_one (T : FirstLoweringDomain mu) :
    (contentCells (firstLowering T) 1).card = (contentCells T.val 1).card + 1 := by
  rw [contentCells_firstLowering_one, Finset.card_insert_of_notMem]
  simp only [contentCells, mem_filter, lastZeroColumn_value, zero_ne_one, and_false,
    not_false_eq_true]

theorem firstLowering_injective : Function.Injective (firstLowering (mu := mu)) := by
  intro T U hTU
  have hj : lastZeroColumn T = lastZeroColumn U := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hv := congrArg (fun V : SemistandardYoungTableau mu => V 0 (lastZeroColumn T)) hTU
      have hz := zero_before_last U hlt.le
      have hbad : (1 : ℕ) = 0 := by
        simpa [firstLowering_apply, hlt.ne, hz] using hv
      exact Nat.one_ne_zero hbad
    · have hv := congrArg (fun V : SemistandardYoungTableau mu => V 0 (lastZeroColumn U)) hTU
      have hz := zero_before_last T hgt.le
      have hbad : (0 : ℕ) = 1 := by
        simpa [firstLowering_apply, hgt.ne, hz] using hv
      exact Nat.zero_ne_one hbad
  apply Subtype.ext
  ext i j
  by_cases hc : i = 0 ∧ j = lastZeroColumn T
  · obtain ⟨rfl, rfl⟩ := hc
    rw [lastZeroColumn_value, hj, lastZeroColumn_value]
  · have hc' : ¬ (i = 0 ∧ j = lastZeroColumn U) := by simpa only [hj] using hc
    have hv := congrArg (fun V : SemistandardYoungTableau mu => V i j) hTU
    simpa only [firstLowering_apply, hc, hc', if_false] using hv

end HigherSpecht.Lascoux
end
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/LascouxColumnSaturation.lean -/



/-!
# A maximally frequent letter occurs in every tableau column

Strict columns inject the cells occupied by one letter into the columns of
the shape.  Equality with the first-row width forces this injection to be
surjective.  The literal bottom-to-top row reading is also identified with
the actual finite cell count, so no separate content convention is assumed.
-/

noncomputable section

open Finset
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

def tableauCellReading (mu : YoungDiagram) : List (ℕ × ℕ) :=
  (descendingRows (mu.colLen 0)).flatMap
    (fun r => (List.range (mu.rowLen r)).map (fun j => (r, j)))

theorem tableauCellReading_nodup (mu : YoungDiagram) :
    (tableauCellReading mu).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro r hr
    exact List.nodup_range.map (fun i j h => congrArg Prod.snd h)
  · have hd : (descendingRows (mu.colLen 0)).Nodup := by
      rw [descendingRows_eq_reverse_range]
      exact List.nodup_reverse.mpr List.nodup_range
    apply hd.imp
    intro r s hrs c hc hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    obtain ⟨k, hk, hpair⟩ := List.mem_map.mp hd
    exact hrs (congrArg Prod.fst hpair).symm

theorem mem_tableauCellReading (mu : YoungDiagram) (c : ℕ × ℕ) :
    c ∈ tableauCellReading mu ↔ c ∈ mu := by
  rcases c with ⟨r, j⟩
  constructor
  · intro hc
    obtain ⟨s, hs, hcell⟩ := List.mem_flatMap.mp hc
    obtain ⟨k, hk, hp⟩ := List.mem_map.mp hcell
    have hr : s = r := congrArg Prod.fst hp
    have hj : k = j := congrArg Prod.snd hp
    subst s
    subst k
    exact YoungDiagram.mem_iff_lt_rowLen.mpr (List.mem_range.mp hk)
  · intro hc
    have hr : r < mu.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
      (mu.up_left_mem le_rfl (Nat.zero_le _) hc)
    exact List.mem_flatMap.mpr ⟨r, mem_descendingRows.mpr hr,
      List.mem_map.mpr ⟨j, List.mem_range.mpr (YoungDiagram.mem_iff_lt_rowLen.mp hc), rfl⟩⟩

theorem tableauCellReading_toFinset (mu : YoungDiagram) :
    (tableauCellReading mu).toFinset = mu.cells := by
  ext c
  simpa only [List.mem_toFinset, YoungDiagram.mem_cells] using mem_tableauCellReading mu c

theorem tableauWord_eq_map_cells (T : SemistandardYoungTableau mu) :
    tableauWord T = (tableauCellReading mu).map (fun c => T c.1 c.2) := by
  have hrow : tableauRowWord T =
      fun r => (List.range (mu.rowLen r)).map (T r) := by
    funext r
    simp only [tableauRowWord, tableauRowSegment, Nat.sub_zero, ← List.range_eq_range']
  simp only [tableauWord, hrow, tableauCellReading, List.map_flatMap,
    List.map_map, Function.comp_def]

/-- The literal row word has exactly the actual cell multiplicities. -/
theorem tableauWord_count_eq_contentCells (T : SemistandardYoungTableau mu) (a : ℕ) :
    (tableauWord T).count a = (contentCells T a).card := by
  rw [tableauWord_eq_map_cells]
  simp only [List.count_eq_countP, List.countP_map]
  have h := (tableauCellReading_nodup mu).card_eq_countP
    (P := fun c => T c.1 c.2 = a)
  rw [tableauCellReading_toFinset] at h
  simpa only [contentCells, Function.comp_def, Bool.beq_eq_decide_eq] using h.symm

theorem contentCells_column_injective (T : SemistandardYoungTableau mu) (a : ℕ) :
    Set.InjOn (Prod.snd : ℕ × ℕ → ℕ) (↑(contentCells T a)) := by
  intro c hc d hd hcol
  obtain ⟨hcm, hca⟩ := Finset.mem_filter.mp hc
  obtain ⟨hdm, hda⟩ := Finset.mem_filter.mp hd
  apply Prod.ext _ hcol
  rcases lt_trichotomy c.1 d.1 with hlt | heq | hgt
  · have h := T.col_strict hlt hdm
    have hca' : T c.1 d.2 = a := by simpa only [hcol] using hca
    rw [hca', hda] at h
    exact (lt_irrefl a h).elim
  · exact heq
  · have h := T.col_strict hgt hcm
    have hda' : T d.1 c.2 = a := by simpa only [hcol] using hda
    rw [hda', hca] at h
    exact (lt_irrefl a h).elim

theorem contentCells_columns_subset (T : SemistandardYoungTableau mu) (a : ℕ) :
    (contentCells T a).image Prod.snd ⊆ Finset.range (mu.rowLen 0) := by
  intro j hj
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hj
  have hcell := (Finset.mem_filter.mp hc).1
  exact Finset.mem_range.mpr (YoungDiagram.mem_iff_lt_rowLen.mp
    (mu.up_left_mem (Nat.zero_le _) le_rfl hcell))

/-- No letter can occur more often than the first-row width. -/
theorem contentCells_card_le_width (T : SemistandardYoungTableau mu) (a : ℕ) :
    (contentCells T a).card ≤ mu.rowLen 0 := by
  have h := Finset.card_le_card (contentCells_columns_subset T a)
  rwa [Finset.card_image_of_injOn (contentCells_column_injective T a), Finset.card_range] at h

theorem contentCells_columns_eq_range (T : SemistandardYoungTableau mu) (a : ℕ)
    (hcount : (contentCells T a).card = mu.rowLen 0) :
    (contentCells T a).image Prod.snd = Finset.range (mu.rowLen 0) := by
  apply Finset.eq_of_subset_of_card_le (contentCells_columns_subset T a)
  rw [Finset.card_image_of_injOn (contentCells_column_injective T a),
    Finset.card_range, hcount]

/-- At saturation, the letter occurs exactly once in every nonempty column. -/
theorem existsUnique_entry_in_each_column (T : SemistandardYoungTableau mu) (a : ℕ)
    (hcount : (contentCells T a).card = mu.rowLen 0)
    (j : ℕ) (hj : j < mu.rowLen 0) :
    ∃! r : ℕ, (r, j) ∈ mu ∧ T r j = a := by
  have hm : j ∈ (contentCells T a).image Prod.snd := by
    rw [contentCells_columns_eq_range T a hcount]
    exact Finset.mem_range.mpr hj
  obtain ⟨⟨r, s⟩, hcell, hs⟩ := Finset.mem_image.mp hm
  change s = j at hs
  subst s
  refine ⟨r, Finset.mem_filter.mp hcell, ?_⟩
  intro r' hr'
  have heq := contentCells_column_injective T a
    (Finset.mem_filter.mpr hr') hcell rfl
  exact congrArg Prod.fst heq

theorem existsUnique_entry_in_each_column_of_word_count
    (T : SemistandardYoungTableau mu) (a : ℕ)
    (hcount : (tableauWord T).count a = mu.rowLen 0)
    (j : ℕ) (hj : j < mu.rowLen 0) :
    ∃! r : ℕ, (r, j) ∈ mu ∧ T r j = a := by
  apply existsUnique_entry_in_each_column T a _ j hj
  rwa [tableauWord_count_eq_contentCells] at hcount

end HigherSpecht.Lascoux
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/LascouxSelectedCut.lean -/



/-!
# The selected row of an actual tableau lowering has a valid cut

The neighboring row is recovered from the literal descending row reading.
The changed position is computed from the genuine one-row lowering formula.
The matched-block argument then supplies the column inequality.  Thus the
final cut theorem has only the actual tableau and actual partial-operator
value as mathematical inputs.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram} {T : SemistandardYoungTableau mu} {v : ℕ} {output : List ℕ}

theorem SelectedLoweringRow.cut_bounds (R : SelectedLoweringRow T v output)
    (h : (listString v).lower (tableauWord T) = some output) :
    T.rowCountLt R.row v < T.rowCountLt R.row (v + 1) ∧
      T.rowCountLt (R.row + 1) (v + 2) < T.rowCountLt R.row (v + 1) := by
  have hlow : T.rowCountLt R.row v < T.rowCountLt R.row (v + 1) := by
    have hp := R.lower_pos
    dsimp only [rowLowerCount] at hp
    omega
  by_cases htop : R.row + 1 = mu.colLen 0
  · refine ⟨hlow, ?_⟩
    rw [T.rowCountLt_eq_zero_of_colLen_le (by omega) (v + 2)]
    omega
  · have hneighbor : R.row + 1 < mu.colLen 0 := by have := R.row_lt; omega
    obtain ⟨b, hb⟩ := R.before_neighbor hneighbor
    let p := b.flatMap (tableauRowWord T) ++ tableauRowBefore T v (R.row + 1) ++
      List.replicate (rowLowerCount T v (R.row + 1)) v
    let middle := tableauRowAfter T v (R.row + 1) ++ tableauRowBefore T v R.row
    let suffix := List.replicate (rowUpperCount T v R.row) (v + 1) ++
      tableauRowAfter T v R.row ++ R.after.flatMap (tableauRowWord T)
    have hm : NeutralSignature v middle :=
      (tableauRowAfter_neutral T v (R.row + 1)).append (tableauRowBefore_neutral T v R.row)
    have hword : tableauWord T =
        p ++ List.replicate (rowUpperCount T v (R.row + 1)) (v + 1) ++ middle ++
          List.replicate (rowLowerCount T v R.row) v ++ suffix := by
      rw [R.word_eq, hb]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [tableauRowWord_blocks T v (R.row + 1), tableauRowWord_blocks T v R.row]
      simp only [p, middle, suffix, List.append_assoc]
    let q := p ++ List.replicate (rowUpperCount T v (R.row + 1)) (v + 1) ++ middle ++
      List.replicate (rowLowerCount T v R.row - 1) v
    have hout : output = q ++ (v + 1) :: suffix := by
      rw [R.output_eq, hb]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [tableauRowWord_blocks T v (R.row + 1)]
      simp only [loweredTableauRowWord, q, p, middle, suffix,
        List.replicate_succ, List.append_assoc, List.cons_append]
    let i : Fin (rowLowerCount T v R.row) :=
      ⟨rowLowerCount T v R.row - 1, by have := R.lower_pos; omega⟩
    have hindex : p.length + rowUpperCount T v (R.row + 1) + middle.length + i.val =
        q.length := by
      simp only [q, i, List.length_append, List.length_replicate]
    have hget : output[p.length + rowUpperCount T v (R.row + 1) + middle.length + i.val]? =
        some (v + 1) := by
      rw [hindex, hout, List.getElem?_append_right (le_refl q.length), Nat.sub_self]
      rfl
    have hchanged : output[p.length + rowUpperCount T v (R.row + 1) +
        middle.length + i.val]? ≠ some v := by
      rw [hget]
      intro heq
      have := Option.some.inj heq
      omega
    exact lower_cut_bounds_of_changed_block T v R.row p middle suffix output hm
      (hword ▸ h) i hchanged

def tableauLoweringFromRow (R : SelectedLoweringRow T v output)
    (h : (listString v).lower (tableauWord T) = some output) : SemistandardYoungTableau mu :=
  lowerTableauAt T v R.row (R.cut_bounds h).1 (R.cut_bounds h).2

end HigherSpecht.Lascoux
end
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/LascouxTableauLowering.lean -/



/-!
# Genuine word lowering preserves the semistandard tableau shape

The selected row is obtained from the actual partial word operation.  Its
column bounds follow from matched-block protection, and the resulting recut
has precisely the output word.  The final existence statement has no assumed
shape-preservation or signature-validity premise.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

theorem recut_entry_eq_of_cut_eq (T : SemistandardYoungTableau mu) (v : ℕ)
    {cut : ℕ → ℕ} (hcut : T.IsCut v cut) (r : ℕ)
    (hr : cut r = T.rowCountLt r (v + 1)) (j : ℕ) :
    T.recut v cut hcut r j = T r j := by
  have h := congrArg (fun U : SemistandardYoungTableau mu => U r j)
    (T.recut_rowCountLt v)
  simpa only [SemistandardYoungTableau.recut_apply, hr] using h

theorem tableauRowBefore_recut (T : SemistandardYoungTableau mu) (v : ℕ)
    {cut : ℕ → ℕ} (hcut : T.IsCut v cut) (r : ℕ) :
    tableauRowBefore (T.recut v cut hcut) v r = tableauRowBefore T v r := by
  unfold tableauRowBefore
  rw [SemistandardYoungTableau.rowCountLt_recut_of_le hcut r le_rfl]
  unfold tableauRowSegment
  apply List.map_congr_left
  intro j hj
  obtain ⟨k, hk, hj⟩ := List.mem_range'.mp hj
  have hjcut : j < T.rowCountLt r v := by omega
  have hjlen := hjcut.trans_le (T.rowCountLt_le_rowLen r v)
  have hval := (T.lt_rowCountLt_iff (x := v) hjlen).mp hjcut
  apply SemistandardYoungTableau.recut_apply_of_not_inBlock hcut
  intro hb
  have hb' := (T.inBlock_def v r j).mp hb
  omega

theorem tableauRowAfter_recut (T : SemistandardYoungTableau mu) (v : ℕ)
    {cut : ℕ → ℕ} (hcut : T.IsCut v cut) (r : ℕ) :
    tableauRowAfter (T.recut v cut hcut) v r = tableauRowAfter T v r := by
  unfold tableauRowAfter
  rw [SemistandardYoungTableau.rowCountLt_recut_of_ge hcut r le_rfl]
  unfold tableauRowSegment
  apply List.map_congr_left
  intro j hj
  obtain ⟨k, hk, hj⟩ := List.mem_range'.mp hj
  have hbound := T.rowCountLt_le_rowLen r (v + 2)
  have hjcut : T.rowCountLt r (v + 2) ≤ j := by omega
  have hjlen : j < mu.rowLen r := by omega
  have hval := T.lt_rowCountLt_iff (x := v + 2) hjlen
  apply SemistandardYoungTableau.recut_apply_of_not_inBlock hcut
  intro hb
  have hb' := (T.inBlock_def v r j).mp hb
  omega

theorem tableauRowWord_lowerTableauAt (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hlow : T.rowCountLt r v < T.rowCountLt r (v + 1))
    (hnext : T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1)) :
    tableauRowWord (lowerTableauAt T v r hlow hnext) r = loweredTableauRowWord T v r := by
  let hcut := isCut_lowerTableauCut T v r hlow hnext
  have ha : (lowerTableauAt T v r hlow hnext).rowCountLt r v = T.rowCountLt r v :=
    SemistandardYoungTableau.rowCountLt_recut_of_le hcut r le_rfl
  have hb : (lowerTableauAt T v r hlow hnext).rowCountLt r (v + 2) =
      T.rowCountLt r (v + 2) :=
    SemistandardYoungTableau.rowCountLt_recut_of_ge hcut r le_rfl
  have hn : (lowerTableauAt T v r hlow hnext).rowCountLt r (v + 1) =
      T.rowCountLt r (v + 1) - 1 := by
    rw [lowerTableauAt_cut]
    simp only [lowerTableauCut, Function.update_self]
  have hL : rowLowerCount (lowerTableauAt T v r hlow hnext) v r =
      rowLowerCount T v r - 1 := by
    simp only [rowLowerCount, ha, hn]
    omega
  have hU : rowUpperCount (lowerTableauAt T v r hlow hnext) v r =
      rowUpperCount T v r + 1 := by
    simp only [rowUpperCount, hb, hn]
    have hle : T.rowCountLt r (v + 1) ≤ T.rowCountLt r (v + 2) :=
      T.rowCountLt_mono r (by omega)
    omega
  rw [tableauRowWord_blocks, hL, hU]
  change tableauRowBefore (T.recut v _ hcut) v r ++ _ ++ _ ++
    tableauRowAfter (T.recut v _ hcut) v r = _
  rw [tableauRowBefore_recut, tableauRowAfter_recut]
  rfl

theorem tableauRowWord_lowerTableauAt_other (T : SemistandardYoungTableau mu) (v r a : ℕ)
    (hlow : T.rowCountLt r v < T.rowCountLt r (v + 1))
    (hnext : T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1))
    (har : a ≠ r) :
    tableauRowWord (lowerTableauAt T v r hlow hnext) a = tableauRowWord T a := by
  unfold tableauRowWord tableauRowSegment
  apply List.map_congr_left
  intro j hj
  exact recut_entry_eq_of_cut_eq T v (isCut_lowerTableauCut T v r hlow hnext) a
    (by simp only [lowerTableauCut, Function.update_of_ne har]) j

theorem flatMap_tableauRowWord_lowerTableauAt (T : SemistandardYoungTableau mu)
    (v r : ℕ) (hlow : T.rowCountLt r v < T.rowCountLt r (v + 1))
    (hnext : T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1))
    (rows : List ℕ) (hrows : ∀ a ∈ rows, a ≠ r) :
    rows.flatMap (tableauRowWord (lowerTableauAt T v r hlow hnext)) =
      rows.flatMap (tableauRowWord T) := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
      simp only [List.flatMap_cons]
      rw [tableauRowWord_lowerTableauAt_other T v r a hlow hnext (hrows a (by simp)),
        ih (fun b hb => hrows b (by simp [hb]))]

theorem tableauLoweringFromRow_word {T : SemistandardYoungTableau mu} {v : ℕ} {output : List ℕ}
    (R : SelectedLoweringRow T v output)
    (h : (listString v).lower (tableauWord T) = some output) :
    tableauWord (tableauLoweringFromRow R h) = output := by
  rw [tableauWord, R.rows_eq, List.flatMap_append, List.flatMap_cons]
  change R.before.flatMap (tableauRowWord (lowerTableauAt T v R.row _ _)) ++
    (tableauRowWord (lowerTableauAt T v R.row _ _) R.row ++
      R.after.flatMap (tableauRowWord (lowerTableauAt T v R.row _ _))) = _
  have hb : ∀ a ∈ R.before, a ≠ R.row := by
    intro a ha
    exact (R.before_gt a ha).ne'
  have ha : ∀ a ∈ R.after, a ≠ R.row := by
    intro a ha
    rw [R.after_eq] at ha
    exact (mem_descendingRows.mp ha).ne
  rw [flatMap_tableauRowWord_lowerTableauAt T v R.row _ _ R.before hb,
    flatMap_tableauRowWord_lowerTableauAt T v R.row _ _ R.after ha,
    tableauRowWord_lowerTableauAt]
  simpa only [List.append_assoc] using R.output_eq.symm

/-- Actual crystal lowering of an actual semistandard row word has an actual
semistandard output of exactly the original shape. -/
theorem exists_tableau_of_word_lowering (T : SemistandardYoungTableau mu) (v : ℕ)
    {output : List ℕ} (h : (listString v).lower (tableauWord T) = some output) :
    ∃ U : SemistandardYoungTableau mu, tableauWord U = output := by
  obtain ⟨R⟩ := exists_selectedLoweringRow T v h
  exact ⟨tableauLoweringFromRow R h, tableauLoweringFromRow_word R h⟩

end HigherSpecht.Lascoux
end
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/LascouxTableauRaising.lean -/



/-!
# Genuine word raising preserves the semistandard tableau shape

The first changed upper letter is protected from a tight lower-row column
constraint by the same literal matched-block argument.  This supplies the
inverse operation on actual tableaux, without deriving it from a mere
cardinality comparison or from Bender--Knuth recutting.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

theorem SelectedRaisingRow.cut_bounds {T : SemistandardYoungTableau mu} {v : ℕ}
    {output : List ℕ} (R : SelectedRaisingRow T v output)
    (h : (listString v).raise (tableauWord T) = some output) :
    T.rowCountLt R.row (v + 1) < T.rowCountLt R.row (v + 2) ∧
      ∀ i, i + 1 = R.row → T.rowCountLt R.row (v + 1) < T.rowCountLt i v := by
  have hhigh : T.rowCountLt R.row (v + 1) < T.rowCountLt R.row (v + 2) := by
    have hp := R.upper_pos
    dsimp only [rowUpperCount] at hp
    omega
  refine ⟨hhigh, ?_⟩
  intro i hri
  have hafter : R.after = i :: descendingRows i := by
    rw [R.after_eq, ← hri]
    rfl
  let p := R.before.flatMap (tableauRowWord T) ++ tableauRowBefore T v R.row ++
    List.replicate (rowLowerCount T v R.row) v
  let middle := tableauRowAfter T v R.row ++ tableauRowBefore T v i
  let suffix := List.replicate (rowUpperCount T v i) (v + 1) ++
    tableauRowAfter T v i ++ (descendingRows i).flatMap (tableauRowWord T)
  have hm : NeutralSignature v middle :=
    (tableauRowAfter_neutral T v R.row).append (tableauRowBefore_neutral T v i)
  have hword : tableauWord T = p ++ List.replicate (rowUpperCount T v R.row) (v + 1) ++
      middle ++ List.replicate (rowLowerCount T v i) v ++ suffix := by
    rw [R.word_eq, hafter]
    simp only [List.flatMap_cons]
    rw [tableauRowWord_blocks T v R.row, tableauRowWord_blocks T v i]
    simp only [p, middle, suffix, List.append_assoc]
  let tail := List.replicate (rowUpperCount T v R.row - 1) (v + 1) ++
    middle ++ List.replicate (rowLowerCount T v i) v ++ suffix
  have hout : output = p ++ v :: tail := by
    have hrep : List.replicate (rowLowerCount T v R.row + 1) v =
        List.replicate (rowLowerCount T v R.row) v ++ [v] := by
      exact List.replicate_succ'
    rw [R.output_eq, hafter]
    simp only [List.flatMap_cons, raisedTableauRowWord]
    rw [tableauRowWord_blocks T v i, hrep]
    simp only [p, middle, suffix, tail, List.append_assoc, List.cons_append, List.nil_append]
  have hget : output[p.length]? = some v := by
    rw [hout, List.getElem?_append_right (le_refl p.length), Nat.sub_self]
    rfl
  have hchanged : output[p.length + 0]? ≠ some (v + 1) := by
    rw [Nat.add_zero, hget]
    intro heq
    have := Option.some.inj heq
    omega
  have hc := raise_column_bound_of_changed_block T v i p middle suffix output hm
    (by simpa only [hri] using (hword ▸ h))
    ⟨0, by simpa only [hri] using R.upper_pos⟩ hchanged
  simpa only [hri] using hc.2

def tableauRaisingFromRow {T : SemistandardYoungTableau mu} {v : ℕ} {output : List ℕ}
    (R : SelectedRaisingRow T v output)
    (h : (listString v).raise (tableauWord T) = some output) : SemistandardYoungTableau mu :=
  raiseTableauAt T v R.row (R.cut_bounds h).1 (R.cut_bounds h).2

theorem tableauRowWord_raiseTableauAt (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hhigh : T.rowCountLt r (v + 1) < T.rowCountLt r (v + 2))
    (hprev : ∀ i, i + 1 = r → T.rowCountLt r (v + 1) < T.rowCountLt i v) :
    tableauRowWord (raiseTableauAt T v r hhigh hprev) r = raisedTableauRowWord T v r := by
  let hcut := isCut_raiseTableauCut T v r hhigh hprev
  have ha : (raiseTableauAt T v r hhigh hprev).rowCountLt r v = T.rowCountLt r v :=
    SemistandardYoungTableau.rowCountLt_recut_of_le hcut r le_rfl
  have hb : (raiseTableauAt T v r hhigh hprev).rowCountLt r (v + 2) =
      T.rowCountLt r (v + 2) :=
    SemistandardYoungTableau.rowCountLt_recut_of_ge hcut r le_rfl
  have hn : (raiseTableauAt T v r hhigh hprev).rowCountLt r (v + 1) =
      T.rowCountLt r (v + 1) + 1 := by
    rw [raiseTableauAt_cut]
    simp only [raiseTableauCut, Function.update_self]
  have hL : rowLowerCount (raiseTableauAt T v r hhigh hprev) v r =
      rowLowerCount T v r + 1 := by
    simp only [rowLowerCount, ha, hn]
    have hle : T.rowCountLt r v ≤ T.rowCountLt r (v + 1) :=
      T.rowCountLt_mono r (by omega)
    omega
  have hU : rowUpperCount (raiseTableauAt T v r hhigh hprev) v r =
      rowUpperCount T v r - 1 := by
    simp only [rowUpperCount, hb, hn]
    omega
  rw [tableauRowWord_blocks, hL, hU]
  change tableauRowBefore (T.recut v _ hcut) v r ++ _ ++ _ ++
    tableauRowAfter (T.recut v _ hcut) v r = _
  rw [tableauRowBefore_recut, tableauRowAfter_recut]
  rfl

theorem tableauRowWord_raiseTableauAt_other (T : SemistandardYoungTableau mu) (v r a : ℕ)
    (hhigh : T.rowCountLt r (v + 1) < T.rowCountLt r (v + 2))
    (hprev : ∀ i, i + 1 = r → T.rowCountLt r (v + 1) < T.rowCountLt i v)
    (har : a ≠ r) :
    tableauRowWord (raiseTableauAt T v r hhigh hprev) a = tableauRowWord T a := by
  unfold tableauRowWord tableauRowSegment
  apply List.map_congr_left
  intro j hj
  exact recut_entry_eq_of_cut_eq T v (isCut_raiseTableauCut T v r hhigh hprev) a
    (by simp only [raiseTableauCut, Function.update_of_ne har]) j

theorem flatMap_tableauRowWord_raiseTableauAt (T : SemistandardYoungTableau mu)
    (v r : ℕ) (hhigh : T.rowCountLt r (v + 1) < T.rowCountLt r (v + 2))
    (hprev : ∀ i, i + 1 = r → T.rowCountLt r (v + 1) < T.rowCountLt i v)
    (rows : List ℕ) (hrows : ∀ a ∈ rows, a ≠ r) :
    rows.flatMap (tableauRowWord (raiseTableauAt T v r hhigh hprev)) =
      rows.flatMap (tableauRowWord T) := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
      simp only [List.flatMap_cons]
      rw [tableauRowWord_raiseTableauAt_other T v r a hhigh hprev (hrows a (by simp)),
        ih (fun b hb => hrows b (by simp [hb]))]

theorem tableauRaisingFromRow_word {T : SemistandardYoungTableau mu} {v : ℕ} {output : List ℕ}
    (R : SelectedRaisingRow T v output)
    (h : (listString v).raise (tableauWord T) = some output) :
    tableauWord (tableauRaisingFromRow R h) = output := by
  rw [tableauWord, R.rows_eq, List.flatMap_append, List.flatMap_cons]
  change R.before.flatMap (tableauRowWord (raiseTableauAt T v R.row _ _)) ++
    (tableauRowWord (raiseTableauAt T v R.row _ _) R.row ++
      R.after.flatMap (tableauRowWord (raiseTableauAt T v R.row _ _))) = _
  have hb : ∀ a ∈ R.before, a ≠ R.row := by
    intro a ha
    exact (R.before_gt a ha).ne'
  have ha : ∀ a ∈ R.after, a ≠ R.row := by
    intro a ha
    rw [R.after_eq] at ha
    exact (mem_descendingRows.mp ha).ne
  rw [flatMap_tableauRowWord_raiseTableauAt T v R.row _ _ R.before hb,
    flatMap_tableauRowWord_raiseTableauAt T v R.row _ _ R.after ha,
    tableauRowWord_raiseTableauAt]
  simpa only [List.append_assoc] using R.output_eq.symm

/-- Actual crystal raising has a semistandard output of exactly the original
shape whenever the literal partial word operator is defined. -/
theorem exists_tableau_of_word_raising (T : SemistandardYoungTableau mu) (v : ℕ)
    {output : List ℕ} (h : (listString v).raise (tableauWord T) = some output) :
    ∃ U : SemistandardYoungTableau mu, tableauWord U = output := by
  obtain ⟨R⟩ := exists_selectedRaisingRow T v h
  exact ⟨tableauRaisingFromRow R h, tableauRaisingFromRow_word R h⟩

end HigherSpecht.Lascoux
end
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/LascouxKnuthLowering.lean -/



/-!
# The actual partial lowering operator respects Knuth equivalence

The operator is checked on each elementary three-letter move with an
arbitrary suffix.  The signature formulas then extend the check to every
prefix, and induction on the literal Knuth relation handles compositions.
Absence of an operator value is retained explicitly; no total fallback is
introduced.  This is a supporting crystal lemma, not the catabolism image
or cardinality theorem.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def OptionKnuth : Option (List ℕ) → Option (List ℕ) → Prop
  | none, none => True
  | some u, some v => KnuthEquivalent u v
  | _, _ => False

namespace OptionKnuth

theorem refl (u : Option (List ℕ)) : OptionKnuth u u := by
  cases u with
  | none => trivial
  | some u => exact KnuthEquivalent.refl u

theorem symm {u v : Option (List ℕ)} (h : OptionKnuth u v) : OptionKnuth v u := by
  cases u <;> cases v
  · trivial
  · exact h.elim
  · exact h.elim
  · exact KnuthEquivalent.symm h

theorem trans {u v w : Option (List ℕ)} (huv : OptionKnuth u v)
    (hvw : OptionKnuth v w) : OptionKnuth u w := by
  cases u <;> cases v <;> cases w
  all_goals first | trivial | exact huv.elim | exact hvw.elim |
    exact KnuthEquivalent.trans huv hvw

theorem map_cons {u v : Option (List ℕ)} (h : OptionKnuth u v) (a : ℕ) :
    OptionKnuth (u.map (List.cons a)) (v.map (List.cons a)) := by
  cases u <;> cases v
  · trivial
  · exact h.elim
  · exact h.elim
  · exact KnuthEquivalent.cons h a

end OptionKnuth

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
/-- The left Knuth generator, with the entire suffix retained in the actual
signature computation.  The proof is a finite check of the three letters'
relations to `r` and `r+1`, with the suffix string length arbitrary. -/
theorem listString_lower_knuth_left_suffix (r a b c : ℕ)
    (hab : a < b) (hbc : b ≤ c) (suffix : List ℕ) :
    OptionKnuth ((listString r).lower ([b, a, c] ++ suffix))
      ((listString r).lower ([b, c, a] ++ suffix)) := by
  have hnone : (listString r).lower suffix = none ↔ (listString r).phi suffix = 0 :=
    (listString r).phi_zero_iff.symm
  cases hs : (listString r).lower suffix with
  | none =>
      have hp := hnone.mp hs
      simp only [List.cons_append, List.nil_append, listString_lower_cons,
        listString_phi_cons, letterString_lower, letterString_epsilon, letterString_phi, hs, hp]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
  | some v =>
      have hp : 0 < (listString r).phi suffix := by
        have h := (listString r).phi_lower hs
        omega
      simp only [List.cons_append, List.nil_append, listString_lower_cons,
        listString_phi_cons, letterString_lower, letterString_epsilon, letterString_phi, hs]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.left hab hbc).append_right v

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
/-- The right Knuth generator with an arbitrary suffix. -/
theorem listString_lower_knuth_right_suffix (r a b c : ℕ)
    (hab : a ≤ b) (hbc : b < c) (suffix : List ℕ) :
    OptionKnuth ((listString r).lower ([a, c, b] ++ suffix))
      ((listString r).lower ([c, a, b] ++ suffix)) := by
  have hnone : (listString r).lower suffix = none ↔ (listString r).phi suffix = 0 :=
    (listString r).phi_zero_iff.symm
  cases hs : (listString r).lower suffix with
  | none =>
      have hp := hnone.mp hs
      simp only [List.cons_append, List.nil_append, listString_lower_cons,
        listString_phi_cons, letterString_lower, letterString_epsilon, letterString_phi, hs, hp]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
  | some v =>
      have hp : 0 < (listString r).phi suffix := by
        have h := (listString r).phi_lower hs
        omega
      simp only [List.cons_append, List.nil_append, listString_lower_cons,
        listString_phi_cons, letterString_lower, letterString_epsilon, letterString_phi, hs]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right hab hbc).append_right v

theorem listString_lower_knuth_prefix (r : ℕ) (pre : List ℕ)
    {u v : List ℕ} (hknuth : KnuthEquivalent u v)
    (hlower : OptionKnuth ((listString r).lower u) ((listString r).lower v)) :
    OptionKnuth ((listString r).lower (pre ++ u))
      ((listString r).lower (pre ++ v)) := by
  induction pre with
  | nil => exact hlower
  | cons a pre ih =>
      have htail : KnuthEquivalent (pre ++ u) (pre ++ v) :=
        hknuth.append_left pre
      have hphi := (listString_signature_of_knuth r htail).2
      simp only [List.cons_append, listString_lower_cons, hphi]
      split_ifs with h
      · exact ih.map_cons a
      · cases (letterString r).lower a with
        | none => trivial
        | some b => exact htail.cons b

/-- Lowering is a genuine partial operation on Knuth classes. -/
theorem listString_lower_of_knuth_context (r : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) (pre suffix : List ℕ) :
    OptionKnuth ((listString r).lower (pre ++ u ++ suffix))
      ((listString r).lower (pre ++ v ++ suffix)) := by
  induction h generalizing pre suffix with
  | refl => exact OptionKnuth.refl _
  | symm h ih => exact (ih pre suffix).symm
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ pre suffix).trans (ih₂ pre suffix)
  | append l t h ih =>
      simpa only [List.append_assoc] using ih (pre ++ l) (t ++ suffix)
  | left hab hbc =>
      have hk := (KnuthEquivalent.left hab hbc).append_right suffix
      have hl := listString_lower_knuth_left_suffix r _ _ _ hab hbc suffix
      simpa only [List.append_assoc] using listString_lower_knuth_prefix r pre hk hl
  | right hab hbc =>
      have hk := (KnuthEquivalent.right hab hbc).append_right suffix
      have hl := listString_lower_knuth_right_suffix r _ _ _ hab hbc suffix
      simpa only [List.append_assoc] using listString_lower_knuth_prefix r pre hk hl

theorem listString_lower_of_knuth (r : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) :
    OptionKnuth ((listString r).lower u) ((listString r).lower v) := by
  simpa only [List.nil_append, List.append_nil] using
    listString_lower_of_knuth_context r h [] []

end HigherSpecht.Lascoux
end
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/LascouxKnuthRaising.lean -/



/-!
# The actual partial raising operator respects Knuth equivalence

This checks the inverse crystal operation on each literal Knuth generator,
including arbitrary contexts. Together with lowering and the exact signature
identities it supplies the reflection operation on Knuth classes. No statement
about the catabolizability image is inferred here.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
/-- The left Knuth generator, with the entire suffix retained in the actual
signature computation.  The proof is a finite check of the three letters'
relations to `r` and `r+1`, with the suffix string length arbitrary. -/
theorem listString_raise_knuth_left_suffix (r a b c : ℕ)
    (hab : a < b) (hbc : b ≤ c) (suffix : List ℕ) :
    OptionKnuth ((listString r).raise ([b, a, c] ++ suffix))
      ((listString r).raise ([b, c, a] ++ suffix)) := by
  have hnone : (listString r).raise suffix = none ↔ (listString r).epsilon suffix = 0 :=
    (listString r).epsilon_zero_iff.symm
  cases hs : (listString r).raise suffix with
  | none =>
      have hp := hnone.mp hs
      simp only [List.cons_append, List.nil_append, listString_raise_cons,
        listString_phi_cons, letterString_raise, letterString_epsilon, letterString_phi, hs, hp]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
  | some v =>
      have hp : 0 < (listString r).epsilon suffix := by
        have h := (listString r).epsilon_raise hs
        omega
      simp only [List.cons_append, List.nil_append, listString_raise_cons,
        listString_phi_cons, letterString_raise, letterString_epsilon, letterString_phi, hs]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.left hab hbc).append_right v

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
/-- The right Knuth generator with an arbitrary suffix. -/
theorem listString_raise_knuth_right_suffix (r a b c : ℕ)
    (hab : a ≤ b) (hbc : b < c) (suffix : List ℕ) :
    OptionKnuth ((listString r).raise ([a, c, b] ++ suffix))
      ((listString r).raise ([c, a, b] ++ suffix)) := by
  have hnone : (listString r).raise suffix = none ↔ (listString r).epsilon suffix = 0 :=
    (listString r).epsilon_zero_iff.symm
  cases hs : (listString r).raise suffix with
  | none =>
      have hp := hnone.mp hs
      simp only [List.cons_append, List.nil_append, listString_raise_cons,
        listString_phi_cons, letterString_raise, letterString_epsilon, letterString_phi, hs, hp]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
  | some v =>
      have hp : 0 < (listString r).epsilon suffix := by
        have h := (listString r).epsilon_raise hs
        omega
      simp only [List.cons_append, List.nil_append, listString_raise_cons,
        listString_phi_cons, letterString_raise, letterString_epsilon, letterString_phi, hs]
      split_ifs <;> simp only [Option.map_none, Option.map_some, OptionKnuth]
      all_goals subst_vars
      all_goals first
        | omega
        | exact KnuthEquivalent.refl _
        | exact (KnuthEquivalent.left (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).append_right suffix
        | exact (KnuthEquivalent.left (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right (by omega) (by omega)).symm.append_right suffix
        | exact (KnuthEquivalent.right hab hbc).append_right v

theorem listString_raise_knuth_prefix (r : ℕ) (pre : List ℕ)
    {u v : List ℕ} (hknuth : KnuthEquivalent u v)
    (hlower : OptionKnuth ((listString r).raise u) ((listString r).raise v)) :
    OptionKnuth ((listString r).raise (pre ++ u))
      ((listString r).raise (pre ++ v)) := by
  induction pre with
  | nil => exact hlower
  | cons a pre ih =>
      have htail : KnuthEquivalent (pre ++ u) (pre ++ v) :=
        hknuth.append_left pre
      have hphi := (listString_signature_of_knuth r htail).2
      simp only [List.cons_append, listString_raise_cons, hphi]
      split_ifs with h
      · exact ih.map_cons a
      · cases (letterString r).raise a with
        | none => trivial
        | some b => exact htail.cons b

/-- Raising is a genuine partial operation on Knuth classes. -/
theorem listString_raise_of_knuth_context (r : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) (pre suffix : List ℕ) :
    OptionKnuth ((listString r).raise (pre ++ u ++ suffix))
      ((listString r).raise (pre ++ v ++ suffix)) := by
  induction h generalizing pre suffix with
  | refl => exact OptionKnuth.refl _
  | symm h ih => exact (ih pre suffix).symm
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ pre suffix).trans (ih₂ pre suffix)
  | append l t h ih =>
      simpa only [List.append_assoc] using ih (pre ++ l) (t ++ suffix)
  | left hab hbc =>
      have hk := (KnuthEquivalent.left hab hbc).append_right suffix
      have hl := listString_raise_knuth_left_suffix r _ _ _ hab hbc suffix
      simpa only [List.append_assoc] using listString_raise_knuth_prefix r pre hk hl
  | right hab hbc =>
      have hk := (KnuthEquivalent.right hab hbc).append_right suffix
      have hl := listString_raise_knuth_right_suffix r _ _ _ hab hbc suffix
      simpa only [List.append_assoc] using listString_raise_knuth_prefix r pre hk hl

theorem listString_raise_of_knuth (r : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) :
    OptionKnuth ((listString r).raise u) ((listString r).raise v) := by
  simpa only [List.nil_append, List.append_nil] using
    listString_raise_of_knuth_context r h [] []

end HigherSpecht.Lascoux
end
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/LascouxContentSwaps.lean -/



/-!
# Explicit content transpositions made from crystal reflections

Every operator in this file is a finite composition of the actual signature
reflections.  In particular, swapping content is not implemented by replacing
the letters of the word.  These concrete equivalences let a repeated letter and
a missing letter be brought to positions zero and one before first lowering.
No braid relation, path independence, or catabolizability image statement is
assumed here.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def wordContent {n : ℕ} (u : Fin n → ℕ) (a : ℕ) : ℕ :=
  (List.ofFn u).count a

theorem wordReflection_content (r n a : ℕ) (u : Fin n → ℕ) :
    wordContent (wordReflection r n u) a =
      wordContent u (Equiv.swap r (r + 1) a) := by
  rw [wordContent, wordReflection_count]
  by_cases ha : a = r
  · subst a
    simp [wordContent]
  · by_cases hb : a = r + 1
    · subst a
      simp [wordContent, ha]
    · simp [wordContent, ha, hb, Equiv.swap_apply_of_ne_of_ne]

/-- The content transposition `(0,j)`, expressed by adjacent crystal
reflections.  The special first step avoids the degenerate conjugation at zero.
-/
def wordSwapZero (n : ℕ) : ℕ → ((Fin n → ℕ) ≃ (Fin n → ℕ))
  | 0 => Equiv.refl _
  | 1 => wordReflection 0 n
  | j + 2 => (wordReflection (j + 1) n).trans
      ((wordSwapZero n (j + 1)).trans (wordReflection (j + 1) n))

theorem wordSwapZero_content (n j a : ℕ) (u : Fin n → ℕ) :
    wordContent (wordSwapZero n j u) a =
      wordContent u (Equiv.swap 0 j a) := by
  induction j using Nat.twoStepInduction generalizing a u with
  | zero => simp [wordSwapZero]
  | one => simpa [wordSwapZero] using wordReflection_content 0 n a u
  | more j ih ih' =>
      simp only [wordSwapZero, Equiv.trans_apply]
      rw [wordReflection_content, ih', wordReflection_content]
      congr 1
      by_cases h0 : a = 0
      · subst a
        simp [Equiv.swap_apply_def]
      · by_cases h1 : a = j + 1
        · subst a
          simp [Equiv.swap_apply_def]
        · by_cases h2 : a = j + 2
          · subst a
            simp [Equiv.swap_apply_def]
          · simp [Equiv.swap_apply_def, h0, h1, h2,
              Ne.symm h0, Ne.symm h1, Ne.symm h2]

/-- A fixed reflection word realizing an arbitrary transposition of content.
The case distinction is part of the definition, so no choice of reduced word
or unproved Coxeter relation is involved. -/
def wordContentSwap (n i j : ℕ) : (Fin n → ℕ) ≃ (Fin n → ℕ) :=
  if i = j then Equiv.refl _
  else if i = 0 then wordSwapZero n j
  else if j = 0 then wordSwapZero n i
  else (wordSwapZero n i).trans ((wordSwapZero n j).trans (wordSwapZero n i))

theorem wordContentSwap_content (n i j a : ℕ) (u : Fin n → ℕ) :
    wordContent (wordContentSwap n i j u) a =
      wordContent u (Equiv.swap i j a) := by
  unfold wordContentSwap
  split_ifs with hij hi hj
  · subst j
    simp
  · subst i
    exact wordSwapZero_content n j a u
  · subst j
    simpa [Equiv.swap_comm] using wordSwapZero_content n i a u
  · simp only [Equiv.trans_apply]
    rw [wordSwapZero_content, wordSwapZero_content, wordSwapZero_content]
    congr 1
    by_cases h0 : a = 0
    · subst a
      simp [Equiv.swap_apply_def, hi, hj, hij,
        Ne.symm hi, Ne.symm hj, Ne.symm hij]
    · by_cases hai : a = i
      · subst a
        simp [Equiv.swap_apply_def, hi, hj, hij,
          Ne.symm hi, Ne.symm hj, Ne.symm hij]
      · by_cases haj : a = j
        · subst a
          simp [Equiv.swap_apply_def, hi, hj, hij,
            Ne.symm hi, Ne.symm hj, Ne.symm hij]
        · simp [Equiv.swap_apply_def, hi, hj, hij, h0, hai, haj,
            Ne.symm hi, Ne.symm hj, Ne.symm hij,
            Ne.symm h0, Ne.symm hai, Ne.symm haj]

/-- Bring distinct letters `i,j` to zero and one respectively.  This is a
concrete word equivalence built from the preceding actual reflections. -/
def wordBringPair (n i j : ℕ) : (Fin n → ℕ) ≃ (Fin n → ℕ) :=
  (wordContentSwap n 0 i).trans
    (wordContentSwap n 1 (Equiv.swap 0 i j))

def bringPairPermutation (i j : ℕ) : Equiv.Perm ℕ :=
  (Equiv.swap 0 i).trans (Equiv.swap 1 (Equiv.swap 0 i j))

theorem wordBringPair_content (n i j a : ℕ) (u : Fin n → ℕ) :
    wordContent (wordBringPair n i j u) a =
      wordContent u ((bringPairPermutation i j).symm a) := by
  simp only [wordBringPair, bringPairPermutation, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.symm_swap, wordContentSwap_content]

theorem bringPairPermutation_apply_left (i j : ℕ) (hij : i ≠ j) :
    bringPairPermutation i j i = 0 := by
  have hne : Equiv.swap 0 i j ≠ 0 := by
    intro h
    have h' := congrArg (Equiv.swap 0 i) h
    simp only [Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
    exact hij h'.symm
  simp only [bringPairPermutation, Equiv.trans_apply, Equiv.swap_apply_right]
  exact Equiv.swap_apply_of_ne_of_ne (by omega) (Ne.symm hne)

theorem bringPairPermutation_apply_right (i j : ℕ) :
    bringPairPermutation i j j = 1 := by
  simp [bringPairPermutation]

theorem wordBringPair_zero (n i j : ℕ) (hij : i ≠ j) (u : Fin n → ℕ) :
    wordContent (wordBringPair n i j u) 0 = wordContent u i := by
  rw [wordBringPair_content]
  congr 1
  exact (bringPairPermutation i j).symm_apply_eq.mpr
    (bringPairPermutation_apply_left i j hij).symm

theorem wordBringPair_one (n i j : ℕ) (u : Fin n → ℕ) :
    wordContent (wordBringPair n i j u) 1 = wordContent u j := by
  rw [wordBringPair_content]
  congr 1
  exact (bringPairPermutation i j).symm_apply_eq.mpr
    (bringPairPermutation_apply_right i j).symm

end HigherSpecht.Lascoux
end
end CanonicalSource7
