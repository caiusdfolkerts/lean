module

public import higher_specht.hanada_row_insertion

@[expose] public section

/-!
# Thresholds and relaxed barriers in the literal row insertion

An insertion whose input is at least a threshold leaves the entire prefix
below that threshold unchanged.  Whether a second insertion pops a smaller
entry depends only on that prefix.  Lowering existing barrier entries, or
extending the barrier, can only increase a popped entry or eliminate it.

These are statements about the actual recursive row routine.  They make no
assumption about a multirow endpoint, a partition count, or catabolizability.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

/-- The new barrier has no larger old entries and may have an extra suffix. -/
inductive LowerBarrierRelaxed : List α → List α → Prop
  | nil (lower : List α) : LowerBarrierRelaxed lower []
  | cons {new old : α} {newTail oldTail : List α} (hle : new ≤ old)
      (tail : LowerBarrierRelaxed newTail oldTail) :
      LowerBarrierRelaxed (new :: newTail) (old :: oldTail)

namespace LowerBarrierRelaxed

theorem length_le {new old : List α} (h : LowerBarrierRelaxed new old) :
    old.length ≤ new.length := by
  induction h with
  | nil => simp
  | cons _ _ ih => simpa only [List.length_cons] using Nat.succ_le_succ ih

theorem of_take {new old : List α} (hlen : old.length ≤ new.length)
    (h : List.Forall₂ (· ≤ ·) (new.take old.length) old) :
    LowerBarrierRelaxed new old := by
  induction old generalizing new with
  | nil => exact .nil new
  | cons x old ih =>
      cases new with
      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons y new =>
          have ht : List.Forall₂ (· ≤ ·) (y :: new.take old.length) (x :: old) := by
            simpa only [List.length_cons, List.take_succ_cons] using h
          cases ht with
          | cons hy hrest =>
              exact .cons hy (ih (by simp only [List.length_cons] at hlen; omega) hrest)

theorem trans {first second third : List α}
    (h₁ : LowerBarrierRelaxed first second) (h₂ : LowerBarrierRelaxed second third) :
    LowerBarrierRelaxed first third := by
  induction h₂ generalizing first with
  | nil => exact .nil first
  | cons hle htail ih =>
      cases h₁ with
      | cons hle' htail' => exact .cons (hle'.trans hle) (ih htail')

end LowerBarrierRelaxed

theorem RowsFit.relax_lower {new old upper : List α}
    (hrelax : LowerBarrierRelaxed new old) (hfit : RowsFit old upper) : RowsFit new upper := by
  induction hfit generalizing new with
  | nil => exact .nil new
  | cons hlt htail ih =>
      cases hrelax with
      | cons hle hrest => exact .cons (hle.trans_lt hlt) (ih hrest)

theorem scheduleRowInsert_lower_relaxed (lower upper : List α) (x : α) :
    LowerBarrierRelaxed (scheduleRowInsert lower upper x).1 upper :=
  LowerBarrierRelaxed.of_take (scheduleRowInsert_length_le lower upper x)
    (scheduleRowInsert_take_le lower upper x)

/-- Under a relaxed barrier, a surviving pop is no smaller than the old pop.
In particular an old absorption remains an absorption. -/
theorem scheduleRowInsert_pop_mono_barrier {new old : List α}
    (hrelax : LowerBarrierRelaxed new old) (upper : List α) (x y : α)
    (hy : (scheduleRowInsert new upper x).2 = some y) :
    ∃ z, (scheduleRowInsert old upper x).2 = some z ∧ z ≤ y := by
  induction hrelax generalizing upper x with
  | nil new =>
      exact ⟨x, rfl, scheduleRowInsert_pop_ge new upper x y hy⟩
  | @cons a b new old hab htail ih =>
      cases upper with
      | nil =>
          by_cases hb : b < x
          · have ha : a < x := hab.trans_lt hb
            simp [scheduleRowInsert, ha] at hy
          · exact ⟨x, by simp [scheduleRowInsert, hb],
              scheduleRowInsert_pop_ge _ _ _ _ hy⟩
      | cons u upper =>
          by_cases hx : x < u
          · by_cases hb : b < x
            · have ha : a < x := hab.trans_lt hb
              obtain ⟨z, hz, hzy⟩ := ih upper u
                (by simpa only [scheduleRowInsert, if_pos hx, if_pos ha] using hy)
              exact ⟨z, by simpa only [scheduleRowInsert, if_pos hx, if_pos hb] using hz, hzy⟩
            · exact ⟨x, by simp [scheduleRowInsert, hx, hb],
                scheduleRowInsert_pop_ge _ _ _ _ hy⟩
          · obtain ⟨z, hz, hzy⟩ := ih upper x
              (by simpa only [scheduleRowInsert, if_neg hx] using hy)
            exact ⟨z, by simpa only [scheduleRowInsert, if_neg hx] using hz, hzy⟩

theorem scheduleRowInsert_none_of_relaxed {new old : List α}
    (hrelax : LowerBarrierRelaxed new old) (upper : List α) (x : α)
    (h : (scheduleRowInsert old upper x).2 = none) :
    (scheduleRowInsert new upper x).2 = none := by
  cases hn : (scheduleRowInsert new upper x).2 with
  | none => rfl
  | some y =>
      obtain ⟨z, hz, hzy⟩ := scheduleRowInsert_pop_mono_barrier hrelax upper x y hn
      rw [h] at hz
      cases hz

def rowPrefixBelow (cutoff : α) (upper : List α) : List α :=
  upper.takeWhile fun x => decide (x < cutoff)

def popBelow (cutoff : α) : Option α → Option α
  | none => none
  | some x => if x < cutoff then some x else none

theorem popBelow_eq_none_of_input_ge (lower upper : List α) {cutoff x : α}
    (hx : cutoff ≤ x) : popBelow cutoff (scheduleRowInsert lower upper x).2 = none := by
  cases hp : (scheduleRowInsert lower upper x).2 with
  | none => rfl
  | some y =>
      have hy := hx.trans (scheduleRowInsert_pop_ge lower upper x y hp)
      simp only [popBelow, if_neg (not_lt.mpr hy)]

/-- Insertion of a large token cannot alter any smaller initial row entries.
No sortedness assumption is necessary for this exact prefix statement. -/
theorem rowPrefixBelow_scheduleRowInsert_of_le (lower upper : List α)
    {cutoff x : α} (hx : cutoff ≤ x) :
    rowPrefixBelow cutoff (scheduleRowInsert lower upper x).1 = rowPrefixBelow cutoff upper := by
  induction lower generalizing upper x with
  | nil => rfl
  | cons l lower ih =>
      cases upper with
      | nil =>
          by_cases hl : l < x <;>
            simp [scheduleRowInsert, hl, rowPrefixBelow, not_lt.mpr hx]
      | cons u upper =>
          by_cases hxu : x < u
          · have hu : ¬ u < cutoff := not_lt.mpr (hx.trans hxu.le)
            by_cases hl : l < x
            · simp [scheduleRowInsert, hxu, hl, rowPrefixBelow, not_lt.mpr hx, hu]
            · simp [scheduleRowInsert, hxu, hl]
          · simp only [scheduleRowInsert, if_neg hxu, rowPrefixBelow, List.takeWhile_cons]
            by_cases hu : u < cutoff
            · simpa [rowPrefixBelow, hu] using congrArg (List.cons u) (ih upper hx)
            · simp [hu]

/-- A pop below a fixed threshold depends only on the upper row's prefix
below that threshold.  Tokens at or above the threshold cannot later produce
a smaller pop. -/
theorem popBelow_scheduleRowInsert_prefix (lower upper : List α) (x cutoff : α) :
    popBelow cutoff (scheduleRowInsert lower upper x).2 =
      popBelow cutoff (scheduleRowInsert lower (rowPrefixBelow cutoff upper) x).2 := by
  induction upper generalizing lower x with
  | nil => rfl
  | cons u upper ih =>
      cases lower with
      | nil => rfl
      | cons l lower =>
          by_cases hu : u < cutoff
          · have hpre : rowPrefixBelow cutoff (u :: upper) = u :: rowPrefixBelow cutoff upper := by
              simp [rowPrefixBelow, hu]
            rw [hpre]
            by_cases hxu : x < u
            · by_cases hl : l < x
              · simpa only [scheduleRowInsert, if_pos hxu, if_pos hl] using ih lower u
              · simp only [scheduleRowInsert, if_pos hxu, if_neg hl]
            · simpa only [scheduleRowInsert, if_neg hxu] using ih lower x
          · have hpre : rowPrefixBelow cutoff (u :: upper) = [] := by
              simp [rowPrefixBelow, hu]
            rw [hpre]
            by_cases hx : cutoff ≤ x
            · rw [popBelow_eq_none_of_input_ge _ _ hx, popBelow_eq_none_of_input_ge _ _ hx]
            · have hxu : x < u := (lt_of_not_ge hx).trans_le (le_of_not_gt hu)
              by_cases hl : l < x
              · simp only [scheduleRowInsert, if_pos hxu, if_pos hl, popBelow]
                exact popBelow_eq_none_of_input_ge lower upper (le_of_not_gt hu)
              · simp only [scheduleRowInsert, if_pos hxu, if_neg hl]

theorem popBelow_scheduleRowInsert_eq_of_prefix {first second : List α}
    {cutoff : α} (hp : rowPrefixBelow cutoff first = rowPrefixBelow cutoff second)
    (lower : List α) (x : α) :
    popBelow cutoff (scheduleRowInsert lower first x).2 =
      popBelow cutoff (scheduleRowInsert lower second x).2 := by
  rw [popBelow_scheduleRowInsert_prefix lower first x cutoff,
    popBelow_scheduleRowInsert_prefix lower second x cutoff, hp]

/-- Pre-inserting an entry above the threshold leaves every subsequent
below-threshold pop unchanged when the lower barrier is fixed. -/
theorem popBelow_scheduleRowInsert_after_large (preLower lower upper : List α)
    (x z cutoff : α) (hz : cutoff ≤ z) :
    popBelow cutoff (scheduleRowInsert lower (scheduleRowInsert preLower upper z).1 x).2 =
      popBelow cutoff (scheduleRowInsert lower upper x).2 :=
  popBelow_scheduleRowInsert_eq_of_prefix
    (rowPrefixBelow_scheduleRowInsert_of_le preLower upper hz) lower x

/-- Combining a large pre-insertion and a relaxed lower barrier cannot create
a smaller pop that was absent from the original comparison. -/
theorem scheduleRowInsert_no_small_pop_after_large_and_relaxed
    {new old : List α} (hrelax : LowerBarrierRelaxed new old)
    (preLower upper : List α) (x z cutoff : α) (hz : cutoff ≤ z)
    (hsmall : popBelow cutoff (scheduleRowInsert old upper x).2 = none)
    {y : α} (hy : (scheduleRowInsert new (scheduleRowInsert preLower upper z).1 x).2 = some y) :
    cutoff ≤ y := by
  obtain ⟨p, hp, hpy⟩ := scheduleRowInsert_pop_mono_barrier hrelax
    (scheduleRowInsert preLower upper z).1 x y hy
  have hpre := popBelow_scheduleRowInsert_after_large preLower old upper x z cutoff hz
  rw [hp, hsmall] at hpre
  have hcp : cutoff ≤ p := by
    by_contra h
    have hpc : p < cutoff := lt_of_not_ge h
    simp only [popBelow, if_pos hpc] at hpre
    cases hpre
  exact hcp.trans hpy

end HigherSpecht
