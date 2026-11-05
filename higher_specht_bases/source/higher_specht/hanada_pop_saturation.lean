module

public import higher_specht.hanada_row_insertion
public import Mathlib.Data.List.Count

@[expose] public section

/-!
# Exact sublevel counts at a popped row entry

Strict columns give an injection from upper entries at most `t` to lower
entries strictly below `t`. When the literal row insertion pops `p`, these
two counts are equal. This local saturation statement uses weakly sorted
rows; it assumes neither a multirow endpoint bound nor shuffle dominance.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

def scheduleCountLT (row : List α) (t : α) : ℕ :=
  row.countP (fun z => decide (z < t))

def scheduleCountLE (row : List α) (t : α) : ℕ :=
  row.countP (fun z => decide (z ≤ t))

@[simp] theorem scheduleCountLT_nil (t : α) : scheduleCountLT [] t = 0 := rfl
@[simp] theorem scheduleCountLE_nil (t : α) : scheduleCountLE [] t = 0 := rfl

@[simp] theorem scheduleCountLT_cons (a : α) (row : List α) (t : α) :
    scheduleCountLT (a :: row) t = scheduleCountLT row t + if a < t then 1 else 0 := by
  simp [scheduleCountLT, List.countP_cons]

@[simp] theorem scheduleCountLE_cons (a : α) (row : List α) (t : α) :
    scheduleCountLE (a :: row) t = scheduleCountLE row t + if a ≤ t then 1 else 0 := by
  simp [scheduleCountLE, List.countP_cons]

theorem scheduleCountLT_eq_zero_of_forall (row : List α) (t : α)
    (h : ∀ a ∈ row, t ≤ a) : scheduleCountLT row t = 0 := by
  unfold scheduleCountLT
  apply List.countP_eq_zero.mpr
  intro a ha
  simpa only [decide_eq_true_eq] using not_lt.mpr (h a ha)

theorem scheduleCountLE_eq_zero_of_forall (row : List α) (t : α)
    (h : ∀ a ∈ row, t < a) : scheduleCountLE row t = 0 := by
  unfold scheduleCountLE
  apply List.countP_eq_zero.mpr
  intro a ha
  simpa only [decide_eq_true_eq] using not_le.mpr (h a ha)

theorem scheduleCountLT_eq_zero_of_le_head {a t : α} {row : List α}
    (hs : (a :: row).Pairwise (· ≤ ·)) (ht : t ≤ a) :
    scheduleCountLT (a :: row) t = 0 := by
  apply scheduleCountLT_eq_zero_of_forall
  intro b hb
  rcases List.mem_cons.mp hb with hba | hb
  · simpa only [hba] using ht
  · exact ht.trans ((List.pairwise_cons.mp hs).1 b hb)

theorem scheduleCountLE_eq_zero_of_lt_head {a t : α} {row : List α}
    (hs : (a :: row).Pairwise (· ≤ ·)) (ht : t < a) :
    scheduleCountLE (a :: row) t = 0 := by
  apply scheduleCountLE_eq_zero_of_forall
  intro b hb
  rcases List.mem_cons.mp hb with hba | hb
  · simpa only [hba] using ht
  · exact lt_of_lt_of_le ht ((List.pairwise_cons.mp hs).1 b hb)

theorem RowsFit.countLE_le_countLT {lower upper : List α}
    (hfit : RowsFit lower upper) (t : α) :
    scheduleCountLE upper t ≤ scheduleCountLT lower t := by
  induction hfit with
  | nil lower => simp
  | @cons l u lower upper hlu htail ih =>
      rw [scheduleCountLE_cons, scheduleCountLT_cons]
      by_cases hut : u ≤ t
      · have hlt : l < t := lt_of_lt_of_le hlu hut
        simpa only [if_pos hut, if_pos hlt] using Nat.add_le_add_right ih 1
      · simp only [if_neg hut, Nat.add_zero]
        exact ih.trans (Nat.le_add_right _ _)

/-- At the popped value the finite matching capacity of the lower row is
exactly saturated by the original upper row. -/
theorem scheduleRowInsert_pop_saturated (lower upper : List α) (x p : α)
    (hlower : lower.Pairwise (· ≤ ·)) (hupper : upper.Pairwise (· ≤ ·))
    (hfit : RowsFit lower upper)
    (hpop : (scheduleRowInsert lower upper x).2 = some p) :
    scheduleCountLE upper p = scheduleCountLT lower p := by
  induction lower generalizing upper x p with
  | nil =>
      cases upper with
      | nil => simp
      | cons u upper => exact False.elim (RowsFit.not_nil_cons u upper hfit)
  | cons l lower ih =>
      cases upper with
      | nil =>
          by_cases hlx : l < x
          · simp [scheduleRowInsert, hlx] at hpop
          · have hxp : x = p := by simpa [scheduleRowInsert, hlx] using hpop
            subst p
            simpa only [scheduleCountLE_nil] using
              (scheduleCountLT_eq_zero_of_le_head hlower (le_of_not_gt hlx)).symm
      | cons u upper =>
          obtain ⟨hlu, hfitTail⟩ := RowsFit.cons_iff.mp hfit
          have hls := (List.pairwise_cons.mp hlower).2
          have hus := (List.pairwise_cons.mp hupper).2
          by_cases hxu : x < u
          · by_cases hlx : l < x
            · have hrecPop : (scheduleRowInsert lower upper u).2 = some p := by
                simpa only [scheduleRowInsert, if_pos hxu, if_pos hlx] using hpop
              have hup : u ≤ p := scheduleRowInsert_pop_ge lower upper u p hrecPop
              have hlp : l < p := lt_of_lt_of_le hlu hup
              have hrec := ih upper u p hls hus hfitTail hrecPop
              simpa only [scheduleCountLE_cons, scheduleCountLT_cons,
                if_pos hup, if_pos hlp] using congrArg (fun z : ℕ => z + 1) hrec
            · have hxp : x = p := by simpa [scheduleRowInsert, hxu, hlx] using hpop
              subst p
              rw [scheduleCountLE_eq_zero_of_lt_head hupper hxu,
                scheduleCountLT_eq_zero_of_le_head hlower (le_of_not_gt hlx)]
          · have hrecPop : (scheduleRowInsert lower upper x).2 = some p := by
              simpa only [scheduleRowInsert, if_neg hxu] using hpop
            have hxp : x ≤ p := scheduleRowInsert_pop_ge lower upper x p hrecPop
            have hup : u ≤ p := (le_of_not_gt hxu).trans hxp
            have hlp : l < p := lt_of_lt_of_le hlu hup
            have hrec := ih upper x p hls hus hfitTail hrecPop
            simpa only [scheduleCountLE_cons, scheduleCountLT_cons,
              if_pos hup, if_pos hlp] using congrArg (fun z : ℕ => z + 1) hrec

end HigherSpecht
