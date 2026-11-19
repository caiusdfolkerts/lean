module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-!
# Literal row insertion with a lower-row barrier

The input moves right through a sorted row.  It may replace a larger entry
only when it is strictly larger than the entry directly below it.  A displaced
entry continues in the same row; the first obstruction is returned as the
popped entry.  This is the ordinary two-row operation, with no internal holes.

The lemmas here establish conservation, the direction of a popped entry, and
the exact no-pop criterion used by an absorption argument.  They do not assert
the missing multirow endpoint bound or the desired shuffle-dominance theorem.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

/-- Literal modified row insertion into a row with a finite lower barrier. -/
def scheduleRowInsert : List α → List α → α → List α × Option α
  | [], upper, x => (upper, some x)
  | l :: lower, [], x => if l < x then ([x], none) else ([], some x)
  | l :: lower, u :: upper, x =>
      if x < u then
        if l < x then
          let next := scheduleRowInsert lower upper u
          (x :: next.1, next.2)
        else (u :: upper, some x)
      else
        let next := scheduleRowInsert lower upper x
        (u :: next.1, next.2)

/-- Strict columns, with any unused suffix of the lower row allowed. -/
inductive RowsFit : List α → List α → Prop
  | nil (lower : List α) : RowsFit lower []
  | cons {l u : α} {lower upper : List α} (hlt : l < u)
      (tail : RowsFit lower upper) : RowsFit (l :: lower) (u :: upper)

namespace RowsFit

theorem length_le {lower upper : List α} (h : RowsFit lower upper) :
    upper.length ≤ lower.length := by
  induction h with
  | nil => simp
  | cons _ _ ih => simpa only [List.length_cons] using Nat.succ_le_succ ih

theorem cons_iff {l u : α} {lower upper : List α} :
    RowsFit (l :: lower) (u :: upper) ↔ l < u ∧ RowsFit lower upper := by
  constructor
  · intro h
    cases h with
    | cons hlt htail => exact ⟨hlt, htail⟩
  · rintro ⟨hlt, htail⟩
    exact .cons hlt htail

theorem not_nil_cons (u : α) (upper : List α) : ¬ RowsFit [] (u :: upper) := by
  intro h
  cases h

theorem of_getElem {lower upper : List α}
    (hlen : upper.length ≤ lower.length)
    (hlt : ∀ j (hj : j < upper.length), lower[j] < upper[j]) :
    RowsFit lower upper := by
  induction upper generalizing lower with
  | nil => exact RowsFit.nil _
  | cons u upper ih =>
      cases lower with
      | nil => simp at hlen
      | cons l lower =>
          have hhead : (l :: lower)[0] < (u :: upper)[0] := hlt 0 (by simp)
          refine RowsFit.cons (by simpa only [List.getElem_cons_zero] using hhead) ?_
          apply ih (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen)
          intro j hj
          have hju : j + 1 < (u :: upper).length := by
            simpa only [List.length_cons] using Nat.succ_lt_succ hj
          have hjl : j + 1 < (l :: lower).length := hju.trans_le hlen
          have htail : (l :: lower)[j + 1]'hjl < (u :: upper)[j + 1]'hju :=
            hlt (j + 1) hju
          simpa only [List.getElem_cons_succ] using htail

/-- Decreasing existing entries of the lower row, while keeping all of its
old positions, preserves strict columns above it. -/
theorem of_lower_take_le {oldLower newLower upper : List α}
    (hfit : RowsFit oldLower upper)
    (hle : List.Forall₂ (· ≤ ·) (newLower.take oldLower.length) oldLower) :
    RowsFit newLower upper := by
  induction hfit generalizing newLower with
  | nil => exact RowsFit.nil _
  | @cons l u lower upper hlu htail ih =>
      cases newLower with
      | nil => cases hle
      | cons v newLower =>
          simp only [List.length_cons, List.take_succ_cons] at hle
          cases hle with
          | cons hvl hrest => exact RowsFit.cons (hvl.trans_lt hlu) (ih hrest)

end RowsFit

theorem scheduleRowInsert_conservation (lower upper : List α) (x : α) :
    (x :: upper).Perm
      ((scheduleRowInsert lower upper x).1 ++
        (scheduleRowInsert lower upper x).2.toList) := by
  induction lower generalizing upper x with
  | nil =>
      simpa only [scheduleRowInsert, Option.toList_some] using
        (List.perm_append_singleton x upper).symm
  | cons l lower ih =>
      cases upper with
      | nil =>
          by_cases hl : l < x
          · simp [scheduleRowInsert, hl]
          · simp [scheduleRowInsert, hl]
      | cons u upper =>
          by_cases hx : x < u
          · by_cases hl : l < x
            · simpa only [scheduleRowInsert, hx, hl, if_true, List.cons_append] using
                (ih upper u).cons x
            · simpa only [scheduleRowInsert, hx, hl, if_true, if_false,
                Option.toList_some] using
                (List.perm_append_singleton x (u :: upper)).symm
          · have h := (List.Perm.swap u x upper).trans ((ih upper x).cons u)
            simpa only [scheduleRowInsert, hx, if_false, List.cons_append] using h

theorem scheduleRowInsert_pop_ge (lower upper : List α) (x y : α)
    (hy : (scheduleRowInsert lower upper x).2 = some y) : x ≤ y := by
  induction lower generalizing upper x with
  | nil =>
      have hxy : x = y := by simpa only [scheduleRowInsert, Option.some.injEq] using hy
      exact hxy.le
  | cons l lower ih =>
      cases upper with
      | nil =>
          by_cases hl : l < x
          · simp [scheduleRowInsert, hl] at hy
          · have hxy : x = y := by simpa [scheduleRowInsert, hl] using hy
            exact hxy.le
      | cons u upper =>
          by_cases hx : x < u
          · by_cases hl : l < x
            · exact hx.le.trans (ih upper u (by simpa [scheduleRowInsert, hx, hl] using hy))
            · have hxy : x = y := by simpa [scheduleRowInsert, hx, hl] using hy
              exact hxy.le
          · exact ih upper x (by simpa [scheduleRowInsert, hx] using hy)

theorem scheduleRowInsert_length (lower upper : List α) (x : α) :
    (scheduleRowInsert lower upper x).1.length +
        (scheduleRowInsert lower upper x).2.toList.length = upper.length + 1 := by
  have h := (scheduleRowInsert_conservation lower upper x).length_eq
  simpa only [List.length_cons, List.length_append] using h.symm

theorem scheduleRowInsert_length_le (lower upper : List α) (x : α) :
    upper.length ≤ (scheduleRowInsert lower upper x).1.length := by
  have h := scheduleRowInsert_length lower upper x
  cases hp : (scheduleRowInsert lower upper x).2 <;>
    simp only [hp, Option.toList_none, Option.toList_some,
      List.length_nil, List.length_cons, Nat.zero_add] at h <;> omega

theorem scheduleRowInsert_mem {lower upper : List α} {x z : α}
    (hz : z ∈ (scheduleRowInsert lower upper x).1) : z = x ∨ z ∈ upper := by
  have hout : z ∈ (scheduleRowInsert lower upper x).1 ++
      (scheduleRowInsert lower upper x).2.toList := List.mem_append.mpr (Or.inl hz)
  have hin := (scheduleRowInsert_conservation lower upper x).mem_iff.mpr hout
  simpa only [List.mem_cons] using hin

/-- Weak sorting is preserved even when the inserted value coincides with an
existing entry. Actual token applications have distinct second coordinates,
but the numerical comparison lemmas do not need that extra restriction. -/
theorem scheduleRowInsert_pairwise_le (lower upper : List α) (x : α)
    (hs : upper.Pairwise (· ≤ ·)) :
    (scheduleRowInsert lower upper x).1.Pairwise (· ≤ ·) := by
  induction lower generalizing upper x with
  | nil => exact hs
  | cons l lower ih =>
      cases upper with
      | nil =>
          by_cases hl : l < x <;> simp [scheduleRowInsert, hl]
      | cons u upper =>
          obtain ⟨hu, htail⟩ := List.pairwise_cons.mp hs
          by_cases hx : x < u
          · by_cases hl : l < x
            · simp only [scheduleRowInsert, hx, hl, if_true]
              apply List.pairwise_cons.mpr
              refine ⟨?_, ih upper u htail⟩
              intro z hz
              rcases scheduleRowInsert_mem hz with rfl | hz
              · exact hx.le
              · exact hx.le.trans (hu z hz)
            · simpa only [scheduleRowInsert, hx, hl, if_true, if_false] using
                List.pairwise_cons.mpr ⟨hu, htail⟩
          · simp only [scheduleRowInsert, hx, if_false]
            apply List.pairwise_cons.mpr
            refine ⟨?_, ih upper x htail⟩
            intro z hz
            rcases scheduleRowInsert_mem hz with rfl | hz
            · exact le_of_not_gt hx
            · exact hu z hz

/-- Existing positions only decrease; an appended final cell is deliberately
excluded from this comparison. This assertion concerns one insertion, not the
earlier compaction of a deleted cell. -/
theorem scheduleRowInsert_take_le (lower upper : List α) (x : α) :
    List.Forall₂ (· ≤ ·)
      ((scheduleRowInsert lower upper x).1.take upper.length) upper := by
  induction lower generalizing upper x with
  | nil =>
      simp only [scheduleRowInsert, List.take_length]
      exact List.forall₂_same.mpr (fun (a : α) _ => le_refl a)
  | cons l lower ih =>
      cases upper with
      | nil => simp
      | cons u upper =>
          by_cases hx : x < u
          · by_cases hl : l < x
            · simpa only [scheduleRowInsert, hx, hl, if_true, List.length_cons,
                List.take_succ_cons] using List.Forall₂.cons hx.le (ih upper u)
            · simp only [scheduleRowInsert, hx, hl, if_true, if_false, List.take_length]
              exact List.forall₂_same.mpr (fun (a : α) _ => le_refl a)
          · simpa only [scheduleRowInsert, hx, if_false, List.length_cons,
              List.take_succ_cons] using List.Forall₂.cons (le_refl u) (ih upper x)

/-- The operation preserves the literal column inequalities with its lower
row. Combined with `scheduleRowInsert_take_le`, this also preserves any fixed
row immediately above it. -/
theorem scheduleRowInsert_fits (lower upper : List α) (x : α)
    (hfit : RowsFit lower upper) :
    RowsFit lower (scheduleRowInsert lower upper x).1 := by
  induction lower generalizing upper x with
  | nil =>
      have hu : upper = [] := by
        cases upper with
        | nil => rfl
        | cons u upper => exact False.elim (RowsFit.not_nil_cons u upper hfit)
      subst upper
      exact RowsFit.nil []
  | cons l lower ih =>
      cases upper with
      | nil =>
          by_cases hl : l < x
          · simpa only [scheduleRowInsert, hl, if_true] using
              RowsFit.cons hl (RowsFit.nil lower)
          · simpa only [scheduleRowInsert, hl, if_false] using RowsFit.nil (l :: lower)
      | cons u upper =>
          obtain ⟨hlu, htail⟩ := RowsFit.cons_iff.mp hfit
          by_cases hx : x < u
          · by_cases hl : l < x
            · simpa only [scheduleRowInsert, hx, hl, if_true] using
                RowsFit.cons hl (ih upper u htail)
            · simpa only [scheduleRowInsert, hx, hl, if_true, if_false] using
                RowsFit.cons hlu htail
          · simpa only [scheduleRowInsert, hx, if_false] using
              RowsFit.cons hlu (ih upper x htail)

/-- If the complete sorted insertion fits the lower row, the literal algorithm
absorbs the input and returns exactly that sorted insertion, with no pop. -/
theorem scheduleRowInsert_eq_orderedInsert_of_fits (lower upper : List α) (x : α)
    (hs : upper.Pairwise (· < ·))
    (hfit : RowsFit lower (List.orderedInsert (· < ·) x upper)) :
    scheduleRowInsert lower upper x =
      (List.orderedInsert (· < ·) x upper, none) := by
  induction upper generalizing lower x with
  | nil =>
      simp only [List.orderedInsert_nil] at hfit ⊢
      cases lower with
      | nil => exact False.elim (RowsFit.not_nil_cons x [] hfit)
      | cons l lower =>
          have hl : l < x := (RowsFit.cons_iff.mp hfit).1
          simp only [scheduleRowInsert, hl, if_true]
  | cons u upper ih =>
      obtain ⟨hu, htail⟩ := List.pairwise_cons.mp hs
      cases lower with
      | nil =>
          have hlen := hfit.length_le
          simp only [List.orderedInsert_length, List.length_cons, List.length_nil] at hlen
          omega
      | cons l lower =>
          by_cases hx : x < u
          · rw [List.orderedInsert_cons_of_le (· < ·) upper hx] at hfit ⊢
            obtain ⟨hlx, hrest⟩ := RowsFit.cons_iff.mp hfit
            have hord : List.orderedInsert (· < ·) u upper = u :: upper := by
              cases upper with
              | nil => exact List.orderedInsert_nil (· < ·) u
              | cons v rest =>
                  exact List.orderedInsert_cons_of_le (· < ·) rest (hu v (by simp))
            have hnext := ih lower u htail (by simpa only [hord] using hrest)
            simp only [scheduleRowInsert, hx, hlx, if_true, hnext, hord]
          · rw [List.orderedInsert_of_not_le (· < ·) upper hx] at hfit ⊢
            obtain ⟨hlu, hrest⟩ := RowsFit.cons_iff.mp hfit
            have hnext := ih lower x htail hrest
            simp only [scheduleRowInsert, hx, if_false, hnext]

/-- A popped token can be advanced to the next row: when the incoming token
exceeds the first lower entry, the updated row is nonempty and its first entry
is at most the popped token. This is the elementary progress invariant for
upward propagation. -/
theorem scheduleRowInsert_head_le_pop {l x y : α} {lower upper : List α}
    (hlx : l < x)
    (hy : (scheduleRowInsert (l :: lower) upper x).2 = some y) :
    ∃ u rest, (scheduleRowInsert (l :: lower) upper x).1 = u :: rest ∧ u ≤ y := by
  cases upper with
  | nil => simp [scheduleRowInsert, hlx] at hy
  | cons u upper =>
      have hxy := scheduleRowInsert_pop_ge (l :: lower) (u :: upper) x y hy
      by_cases hx : x < u
      · refine ⟨x, (scheduleRowInsert lower upper u).1, ?_, hxy⟩
        simp only [scheduleRowInsert, hx, hlx, if_true]
      · refine ⟨u, (scheduleRowInsert lower upper x).1, ?_, (le_of_not_gt hx).trans hxy⟩
        simp only [scheduleRowInsert, hx, if_false]

end HigherSpecht
