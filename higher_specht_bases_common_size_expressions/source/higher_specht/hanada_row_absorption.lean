module

public import higher_specht.hanada_row_insertion

@[expose] public section

/-!
# The sound one-row absorption comparison

Removing an entry from a sorted row and inserting a greater entry weakly
increases every order statistic.  Consequently every strict column lower
bound for the old row remains valid for the full replacement row.

This is the local absorption fact needed by the corrected upward-bumping
exchange.  It deliberately does not assert that a compacted neighboring
row satisfies an old column bound; that additional route invariant must be
proved separately.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem orderedInsert_eq_cons_of_le_all (a : α) (l : List α)
    (h : ∀ b ∈ l, a ≤ b) : List.orderedInsert (· ≤ ·) a l = a :: l := by
  cases l with
  | nil => simp only [List.orderedInsert_nil]
  | cons b l => exact List.orderedInsert_cons_of_le _ _ (h b (by simp))

/-- Increasing only the inserted entry increases every order statistic of
the sorted result, including in the presence of repeated values. -/
theorem orderedInsert_forall₂_mono {l : List α} (hl : l.Pairwise (· ≤ ·))
    {x y : α} (hxy : x ≤ y) :
    List.Forall₂ (· ≤ ·) (List.orderedInsert (· ≤ ·) x l)
      (List.orderedInsert (· ≤ ·) y l) := by
  induction l generalizing x y with
  | nil =>
      simpa only [List.orderedInsert_nil] using
        (List.Forall₂.cons hxy List.Forall₂.nil)
  | cons a l ih =>
      have hhead := (List.pairwise_cons.mp hl).1
      have htail := (List.pairwise_cons.mp hl).2
      by_cases hxa : x ≤ a
      · rw [List.orderedInsert_cons_of_le _ _ hxa]
        by_cases hya : y ≤ a
        · rw [List.orderedInsert_cons_of_le _ _ hya]
          exact List.Forall₂.cons hxy (List.forall₂_refl _)
        · rw [List.orderedInsert_of_not_le _ _ hya]
          apply List.Forall₂.cons hxa
          have h := ih htail (le_of_not_ge hya)
          rwa [orderedInsert_eq_cons_of_le_all a l hhead] at h
      · have hya : ¬ y ≤ a := fun h => hxa (hxy.trans h)
        rw [List.orderedInsert_of_not_le _ _ hxa, List.orderedInsert_of_not_le _ _ hya]
        exact List.Forall₂.cons le_rfl (ih htail hxy)

def sortedRowReplacement (l : List α) (old new : α) : List α :=
  List.orderedInsert (· ≤ ·) new (l.erase old)

theorem sortedRowReplacement_forall₂ {l : List α} (hl : l.Pairwise (· ≤ ·))
    {old new : α} (hold : old ∈ l) (hle : old ≤ new) :
    List.Forall₂ (· ≤ ·) l (sortedRowReplacement l old new) := by
  have herase : (l.erase old).Pairwise (· ≤ ·) := hl.sublist List.erase_sublist
  have h := orderedInsert_forall₂_mono herase hle
  rw [List.orderedInsert_erase old l hold hl] at h
  exact h

theorem sortedRowReplacement_length {l : List α} (hl : l.Pairwise (· ≤ ·))
    {old new : α} (hold : old ∈ l) (hle : old ≤ new) :
    (sortedRowReplacement l old new).length = l.length :=
  (sortedRowReplacement_forall₂ hl hold hle).length_eq.symm

theorem sortedRowReplacement_get {l : List α} (hl : l.Pairwise (· ≤ ·))
    {old new : α} (hold : old ∈ l) (hle : old ≤ new) (i : ℕ)
    (hi : i < l.length) (hi' : i < (sortedRowReplacement l old new).length) :
    l[i] ≤ (sortedRowReplacement l old new)[i] :=
  (sortedRowReplacement_forall₂ hl hold hle).get hi hi'

theorem RowsFit.mono_upper {lower old new : List α} (h : RowsFit lower old)
    (hle : List.Forall₂ (· ≤ ·) old new) : RowsFit lower new := by
  induction h generalizing new with
  | nil lower =>
      cases hle
      exact RowsFit.nil lower
  | cons hlt htail ih =>
      cases hle with
      | cons hle hrest => exact RowsFit.cons (hlt.trans_le hle) (ih hrest)

/-- The fully inserted replacement row is admissible against any lower row
already known to lie strictly below the original row. -/
theorem sortedRowReplacement_columnBound {lower upper : List α}
    (hu : upper.Pairwise (· ≤ ·)) (hcol : RowsFit lower upper)
    {old new : α} (hold : old ∈ upper) (hle : old ≤ new) :
    RowsFit lower (sortedRowReplacement upper old new) :=
  hcol.mono_upper (sortedRowReplacement_forall₂ hu hold hle)

theorem orderedInsert_lt_eq_le_of_sorted {l : List α} (hl : l.Pairwise (· ≤ ·))
    (x : α) : List.orderedInsert (· < ·) x l = List.orderedInsert (· ≤ ·) x l := by
  induction l with
  | nil => simp only [List.orderedInsert_nil]
  | cons a l ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
      by_cases hxa : x < a
      · simp only [List.orderedInsert_cons, if_pos hxa, if_pos hxa.le]
      · by_cases heq : x = a
        · subst x
          simp only [List.orderedInsert_cons, lt_self_iff_false, le_refl, if_false,
            if_true, ih htail, orderedInsert_eq_cons_of_le_all a l hhead]
        · have hle : ¬ x ≤ a := fun h => heq (le_antisymm h (le_of_not_gt hxa))
          simp only [List.orderedInsert_cons, if_neg hxa, if_neg hle, ih htail]

/-- Exact absorption by the literal bounded row-insertion routine.  Its
lower-row hypothesis is explicit; obtaining it at a multirow frontier is a
separate obligation. -/
theorem scheduleRowInsert_absorbs_deleted_entry {lower upper : List α}
    (hs : upper.Pairwise (· < ·)) (hfit : RowsFit lower upper)
    {old new : α} (hold : old ∈ upper) (hle : old ≤ new) :
    scheduleRowInsert lower (upper.erase old) new =
      (sortedRowReplacement upper old new, none) := by
  have herase : (upper.erase old).Pairwise (· < ·) :=
    hs.sublist List.erase_sublist
  have hweak := hs.imp (fun {_ _} h => h.le)
  have heraseWeak := herase.imp (fun {_ _} h => h.le)
  have h := scheduleRowInsert_eq_orderedInsert_of_fits lower (upper.erase old) new herase
    (by
      rw [orderedInsert_lt_eq_le_of_sorted heraseWeak]
      exact sortedRowReplacement_columnBound hweak hfit hold hle)
  simpa only [orderedInsert_lt_eq_le_of_sorted heraseWeak, sortedRowReplacement] using h

theorem sortedRowReplacement_eraseIdx {l : List α} (hl : l.Nodup)
    (i : Fin l.length) (x : α) :
    sortedRowReplacement l (l.get i) x =
      List.orderedInsert (· ≤ ·) x (l.eraseIdx i.val) := by
  rw [sortedRowReplacement, hl.erase_get i]

end HigherSpecht
