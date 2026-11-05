module

public import higher_specht.verified.remaining01
public import tau_ceti.combinatorics.enumerative.partition.box_move
public import Mathlib.Data.Multiset.Pairwise
public import Mathlib.Data.Complex.Basic

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining02/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/HanadaEndpointDominance.lean -/



/-!
# Dominance from the actual bounded route endpoints

The j-th route begins at row j, so a relative endpoint at most d replaces
the cell deleted from row d+j by a cell in an earlier row.  The following
finite counting proof translates those exact endpoint data into all row
prefix inequalities.  Its application must supply the actual deletion
identity; no dominance assertion is included among its premises.
-/

namespace HigherSpecht

open Finset

def routeEndpointsBelow : List ℕ → ℕ → ℕ
  | [], _ => 0
  | e :: tail, r => (if e < r then 1 else 0) + routeEndpointsBelow tail (r - 1)

@[simp] theorem routeEndpointsBelow_zero (endpoints : List ℕ) :
    routeEndpointsBelow endpoints 0 = 0 := by
  induction endpoints with
  | nil => rfl
  | cons e endpoints ih => simp [routeEndpointsBelow, ih]

theorem sum_routeEndpointCount (endpoints : List ℕ) (r : ℕ) :
    (∑ j ∈ Finset.range r, routeEndpointCount endpoints j) = routeEndpointsBelow endpoints r := by
  induction endpoints generalizing r with
  | nil => simp [routeEndpointCount, routeEndpointsBelow]
  | cons e endpoints ih =>
      simp only [routeEndpointCount, Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_range]
      cases r with
      | zero => simp
      | succ r =>
          rw [Finset.sum_range_succ']
          simp only [if_pos rfl, if_true, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false,
            Nat.zero_add, Nat.add_zero, ih, routeEndpointsBelow, Nat.succ_sub_one]

theorem routeEndpointsBelow_lowerBound (endpoints : List ℕ) (d r : ℕ)
    (hbound : ∀ e ∈ endpoints, e ≤ d) :
    min endpoints.length (r - d) ≤ routeEndpointsBelow endpoints r := by
  induction endpoints generalizing r with
  | nil => simp [routeEndpointsBelow]
  | cons e endpoints ih =>
      have he := hbound e (by simp)
      have htail := ih (r - 1) (fun z hz => hbound z (List.mem_cons_of_mem e hz))
      cases r with
      | zero => simp
      | succ r =>
          by_cases hdr : d ≤ r
          · have her : e < r + 1 := by omega
            simp only [List.length_cons, routeEndpointsBelow, if_pos her, Nat.succ_sub_one] at *
            omega
          · have hz : r + 1 - d = 0 := by omega
            simp only [List.length_cons, hz, _root_.min_zero]
            exact Nat.zero_le _

def stackRowPrefix {α : Type*} (rows : List (List α)) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, (rows.getD j []).length

theorem ConsecutiveBumpRoutes.row_prefix {α : Type*} [LinearOrder α]
    {advance : α → α} {lower : List α} {rows result : List (List α)}
    {inputs : List α} {endpoints : List ℕ}
    (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints) (r : ℕ) :
    stackRowPrefix result r = stackRowPrefix rows r + routeEndpointsBelow endpoints r := by
  unfold stackRowPrefix
  simp_rw [h.row_lengths]
  rw [Finset.sum_add_distrib, sum_routeEndpointCount]

/-- If the initial stack is obtained by deleting one cell in each of m
consecutive rows starting at d, actual route endpoints bounded by d restore
all those prefix counts and can only increase them. -/
theorem ConsecutiveBumpRoutes.dominates_before_column_deletion
    {α : Type*} [LinearOrder α] {advance : α → α} {lower : List α}
    {before rows result : List (List α)} {inputs : List α} {endpoints : List ℕ}
    (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints)
    (d : ℕ) (hbound : ∀ e ∈ endpoints, e ≤ d)
    (hdelete : ∀ r, stackRowPrefix before r = stackRowPrefix rows r + min inputs.length (r - d)) :
    ∀ r, stackRowPrefix before r ≤ stackRowPrefix result r := by
  intro r
  rw [hdelete r, h.row_prefix r]
  apply Nat.add_le_add_left
  rw [← h.length_endpoints]
  exact routeEndpointsBelow_lowerBound endpoints d r hbound

end HigherSpecht
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/HanadaScheduledRows.lean -/



/-!
# Exact finite rows of a scheduled filling

The initial shuffle filling is converted to the literal finite row stack used
by the upward-route construction. The conversion preserves every row length,
the visit-height equation, strict row and column orders, and the complete
token content. It does not assert a greedy comparison or a count theorem.
-/

noncomputable section
open TauCeti
open scoped Classical

-- `List.mem_flatten_of_mem_getD` is supplied by `tau_ceti.data.list.get_d`.

namespace HigherSpecht

namespace ScheduleRowsValid

variable {α : Type*} [LinearOrder α] {height : α → ℕ}
  {r : ℕ} {rows : List (List α)}

theorem getD_sorted (h : ScheduleRowsValid height r rows) (j : ℕ) :
    (rows.getD j []).Pairwise (· ≤ ·) := by
  induction h generalizing j with
  | nil => simp
  | cons hs hh hc ht ih =>
      cases j with
      | zero => exact hs
      | succ j => exact ih j

theorem getD_height (h : ScheduleRowsValid height r rows) (j : ℕ) :
    ∀ x ∈ rows.getD j [], height x = r + j := by
  induction h generalizing j with
  | nil => simp
  | @cons r row tail hs hh hc ht ih =>
      cases j with
      | zero => simpa using hh
      | succ j => simpa only [List.getD_cons_succ, Nat.add_assoc,
          Nat.add_comm 1 j] using ih j

theorem getD_columns (h : ScheduleRowsValid height r rows) (j : ℕ) :
    RowsFit (rows.getD j []) (rows.getD (j + 1) []) := by
  induction h generalizing j with
  | nil => exact RowsFit.nil []
  | cons hs hh hc ht ih =>
      cases j with
      | zero => simpa only [List.getD_cons_zero, List.getD_cons_succ,
          List.headD_eq_getD] using hc
      | succ j => exact ih j

theorem mem_getD_of_height (h : ScheduleRowsValid height r rows)
    {x : α} (hx : x ∈ rows.flatten) {j : ℕ} (hheight : height x = r + j) :
    x ∈ rows.getD j [] := by
  obtain ⟨row, hrow, hxrow⟩ := List.mem_flatten.mp hx
  obtain ⟨k, hk, hroweq⟩ := List.mem_iff_getElem.mp hrow
  have hx' : x ∈ rows.getD k [] := by
    rw [List.getD_eq_getElem _ _ hk, hroweq]
    exact hxrow
  have hactual := h.getD_height k x hx'
  have hkj : k = j := Nat.add_left_cancel (hactual.symm.trans hheight)
  simpa only [hkj] using hx'

end ScheduleRowsValid

namespace ScheduledFilling

variable {n : ℕ} {a : Fin n → ℕ}

def rowCell (F : ScheduledFilling a) (r : ℕ) (j : Fin (F.shape.rowLen r)) :
    ↥F.shape.cells :=
  ⟨(r, j.val), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩

def row (F : ScheduledFilling a) (r : ℕ) : List (VisitTime n) :=
  List.ofFn (fun j : Fin (F.shape.rowLen r) => F.time (F.rowCell r j))

def rowsFrom (F : ScheduledFilling a) : ℕ → ℕ → List (List (VisitTime n))
  | _, 0 => []
  | r, k + 1 => F.row r :: F.rowsFrom (r + 1) k

def rows (F : ScheduledFilling a) : List (List (VisitTime n)) :=
  F.rowsFrom 0 (F.shape.colLen 0)

@[simp] theorem row_length (F : ScheduledFilling a) (r : ℕ) :
    (F.row r).length = F.shape.rowLen r := by simp [row]

@[simp] theorem row_get (F : ScheduledFilling a) (r : ℕ)
    (j : Fin (F.shape.rowLen r)) :
    (F.row r).get ⟨j.val, by simpa using j.isLt⟩ = F.time (F.rowCell r j) := by
  simp [row]

theorem row_pairwise_lt (F : ScheduledFilling a) (r : ℕ) :
    (F.row r).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  apply F.time_strict
  change (r, i.val) < (r, j.val)
  refine lt_iff_le_not_ge.mpr ⟨⟨le_refl r, hij.le⟩, ?_⟩
  intro h
  exact (not_le_of_gt hij) h.2

theorem row_height (F : ScheduledFilling a) (r : ℕ) :
    ∀ t ∈ F.row r, visitHeight a t = r := by
  intro t ht
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht
  have h := F.row_eq (F.rowCell r j)
  exact h.symm

theorem row_columns (F : ScheduledFilling a) (r : ℕ) :
    RowsFit (F.row r) (F.row (r + 1)) := by
  have hlen : (F.row (r + 1)).length ≤ (F.row r).length := by
    simpa only [row_length] using F.shape.rowLen_anti r (r + 1) (Nat.le_succ r)
  apply RowsFit.of_getElem hlen
  intro j hj
  have hj' : j < F.shape.rowLen (r + 1) := by simpa only [row_length] using hj
  have hjr : j < F.shape.rowLen r :=
    hj'.trans_le (F.shape.rowLen_anti r (r + 1) (Nat.le_succ r))
  have hc : F.time (F.rowCell r ⟨j, hjr⟩) <
      F.time (F.rowCell (r + 1) ⟨j, hj'⟩) := by
    apply F.time_strict
    change (r, j) < (r + 1, j)
    refine lt_iff_le_not_ge.mpr ⟨⟨Nat.le_succ r, le_refl j⟩, ?_⟩
    intro h
    have := h.1
    omega
  simpa [row] using hc

theorem rowsFrom_valid (F : ScheduledFilling a) (r k : ℕ) :
    ScheduleRowsValid (visitHeight a) r (F.rowsFrom r k) := by
  induction k generalizing r with
  | zero => exact .nil r
  | succ k ih =>
      refine .cons ((F.row_pairwise_lt r).imp (fun h => le_of_lt h))
        (F.row_height r) ?_ (ih (r + 1))
      cases k with
      | zero => exact RowsFit.nil _
      | succ k => exact F.row_columns r

theorem rows_valid (F : ScheduledFilling a) :
    ScheduleRowsValid (visitHeight a) 0 F.rows :=
  F.rowsFrom_valid 0 _

theorem rowsFrom_getD (F : ScheduledFilling a) (r k j : ℕ) :
    (F.rowsFrom r k).getD j [] = if j < k then F.row (r + j) else [] := by
  induction k generalizing r j with
  | zero => simp [rowsFrom]
  | succ k ih =>
      cases j with
      | zero => simp [rowsFrom]
      | succ j =>
          simpa only [rowsFrom, List.getD_cons_succ, Nat.succ_lt_succ_iff,
            Nat.add_succ, Nat.succ_add] using ih (r + 1) j

theorem rows_getD (F : ScheduledFilling a) (r : ℕ) :
    F.rows.getD r [] = F.row r := by
  rw [rows, rowsFrom_getD]
  by_cases hr : r < F.shape.colLen 0
  · simp [hr]
  · have hzero := YoungDiagram.rowLen_eq_zero_of_colLen_le
      (Nat.le_of_not_gt hr : F.shape.colLen 0 ≤ r)
    simp [hr, row, hzero]

@[simp] theorem rows_row_length (F : ScheduledFilling a) (r : ℕ) :
    (F.rows.getD r []).length = F.shape.rowLen r := by
  rw [rows_getD, row_length]

def rowTokens (F : ScheduledFilling a) (r : ℕ) : List (Fin n) :=
  (F.row r).map (fun t => (ofLex t).2)

theorem rowTokens_eq (F : ScheduledFilling a) (r : ℕ) :
    F.rowTokens r = List.ofFn (fun j => F.token (F.rowCell r j)) := by
  simp only [rowTokens, row, List.map_ofFn, Function.comp_def, time, visitTime, ofLex_toLex]

theorem rowTokens_nodup (F : ScheduledFilling a) (r : ℕ) :
    (F.rowTokens r).Nodup := by
  rw [rowTokens_eq, List.nodup_iff_pairwise_ne]
  apply List.pairwise_ofFn.mpr
  intro i j hij heq
  have hc := F.token.injective heq
  have hval : i.val = j.val := congrArg (fun c : ↥F.shape.cells => c.val.2) hc
  exact (ne_of_lt hij) (Fin.ext hval)

theorem mem_rowTokens_iff (F : ScheduledFilling a) (r : ℕ) (i : Fin n) :
    i ∈ F.rowTokens r ↔ (F.cell i).val.1 = r := by
  rw [rowTokens_eq, List.mem_ofFn]
  constructor
  · rintro ⟨j, hj⟩
    have hc : F.cell i = F.rowCell r j := by
      apply F.token.injective
      simpa only [token_cell] using hj.symm
    rw [hc]
    rfl
  · intro hr
    have hj : (F.cell i).val.2 < F.shape.rowLen r := by
      have hm := YoungDiagram.mem_iff_lt_rowLen.mp (F.cell i).property
      simpa only [hr] using hm
    refine ⟨⟨(F.cell i).val.2, hj⟩, ?_⟩
    have hc : F.rowCell r ⟨(F.cell i).val.2, hj⟩ = F.cell i := by
      apply Subtype.ext
      exact Prod.ext hr.symm rfl
    rw [hc, token_cell]

theorem mem_rowsFrom_tokens_iff (F : ScheduledFilling a) (r k : ℕ) (i : Fin n) :
    i ∈ (F.rowsFrom r k).flatten.map (fun t => (ofLex t).2) ↔
      r ≤ (F.cell i).val.1 ∧ (F.cell i).val.1 < r + k := by
  induction k generalizing r with
  | zero => simp [rowsFrom] <;> omega
  | succ k ih =>
      simp only [rowsFrom, List.flatten_cons, List.map_append, List.mem_append]
      change (i ∈ F.rowTokens r ∨
        i ∈ (F.rowsFrom (r + 1) k).flatten.map (fun t => (ofLex t).2)) ↔ _
      rw [mem_rowTokens_iff, ih]
      omega

theorem rowsFrom_tokens_nodup (F : ScheduledFilling a) (r k : ℕ) :
    ((F.rowsFrom r k).flatten.map (fun t => (ofLex t).2)).Nodup := by
  induction k generalizing r with
  | zero => simp [rowsFrom]
  | succ k ih =>
      simp only [rowsFrom, List.flatten_cons, List.map_append]
      apply List.nodup_append.mpr
      refine ⟨F.rowTokens_nodup r, ih (r + 1), ?_⟩
      intro i hi j hj heq
      subst j
      have hr := (F.mem_rowTokens_iff r i).mp hi
      have ht := (F.mem_rowsFrom_tokens_iff (r + 1) k i).mp hj
      omega

/-- Every original token appears exactly once, with its actual current visit.
This is a genuine content permutation, not merely an equality of cardinalities. -/
theorem rows_tokens_perm (F : ScheduledFilling a) :
    (F.rows.flatten.map (fun t => (ofLex t).2)).Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup (F.rowsFrom_tokens_nodup 0 _) (List.nodup_finRange n)).mpr
  intro i
  have hi : (F.cell i).val.1 < F.shape.colLen 0 :=
    (YoungDiagram.mem_iff_lt_colLen.mp (F.cell i).property).trans_le
      (F.shape.colLen_anti 0 (F.cell i).val.2 (Nat.zero_le _))
  have hm : i ∈ F.rows.flatten.map (fun t => (ofLex t).2) :=
    (F.mem_rowsFrom_tokens_iff 0 _ i).mpr ⟨Nat.zero_le _, by simpa using hi⟩
  exact iff_of_true hm (by simp)

/-- The geometric processed-cell invariant is exactly the sublevel count in
each literal row. This is the form retained by the greedy-run induction. -/
theorem row_countLT_of_isPrefix (F : ScheduledFilling a)
    {nu : YoungDiagram} {tau : VisitTime n} (hpre : F.IsPrefix nu tau) (r : ℕ) :
    scheduleCountLT (F.row r) tau = nu.rowLen r := by
  have hlen : nu.rowLen r ≤ F.shape.rowLen r :=
    YoungDiagram.rowLen_le_of_le hpre.1 r
  unfold scheduleCountLT row
  rw [List.ofFn_eq_map, List.countP_map]
  have hpred :
      (fun j : Fin (F.shape.rowLen r) => decide (F.time (F.rowCell r j) < tau)) =
        (fun j : Fin (F.shape.rowLen r) => decide (j.val < nu.rowLen r)) := by
    funext j
    have hiff : F.time (F.rowCell r j) < tau ↔ j.val < nu.rowLen r := by
      exact (hpre.2 (F.rowCell r j)).symm.trans YoungDiagram.mem_iff_lt_rowLen
    exact decide_eq_decide.mpr hiff
  change (List.finRange (F.shape.rowLen r)).countP
    (fun j => decide (F.time (F.rowCell r j) < tau)) = nu.rowLen r
  rw [hpred, ← (List.nodup_finRange (F.shape.rowLen r)).card_eq_countP]
  rw [List.toFinset_finRange, Fin.card_filter_val_lt, min_eq_right hlen]

theorem rows_countLT_of_isPrefix (F : ScheduledFilling a)
    {nu : YoungDiagram} {tau : VisitTime n} (hpre : F.IsPrefix nu tau) (r : ℕ) :
    scheduleCountLT (F.rows.getD r []) tau = nu.rowLen r := by
  rw [rows_getD]
  exact F.row_countLT_of_isPrefix hpre r

end ScheduledFilling
end HigherSpecht
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/HanadaBottomInsertion.lean -/



/-!
# The genuinely unbounded bottom row

Insertion into row zero has no lower-row barrier. It is ordinary sorted
insertion and always adds one cell. The sublevel-capacity argument proves
that a strictly larger input in the adjacent row is also absorbed. No
artificial finite barrier is substituted for the bottom row.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

def scheduleBottomInsert (row : List α) (x : α) : List α :=
  List.orderedInsert (· ≤ ·) x row

theorem scheduleBottomInsert_conservation (row : List α) (x : α) :
    (scheduleBottomInsert row x).Perm (x :: row) :=
  List.perm_orderedInsert (· ≤ ·) x row

@[simp] theorem scheduleBottomInsert_length (row : List α) (x : α) :
    (scheduleBottomInsert row x).length = row.length + 1 :=
  List.orderedInsert_length (· ≤ ·) row x

theorem scheduleBottomInsert_pairwise_le (row : List α) (x : α)
    (hs : row.Pairwise (· ≤ ·)) :
    (scheduleBottomInsert row x).Pairwise (· ≤ ·) :=
  hs.orderedInsert x row

/-- Dropping the first entry from a weakly sorted row can only raise its
remaining order statistics. This is an actual finite-list comparison. -/
theorem lowerBarrierRelaxed_cons_of_sorted {a : α} {row : List α}
    (hs : (a :: row).Pairwise (· ≤ ·)) : LowerBarrierRelaxed (a :: row) row := by
  induction row generalizing a with
  | nil => exact .nil [a]
  | cons b row ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
      exact .cons (hhead b (by simp)) (ih htail)

theorem scheduleBottomInsert_lower_relaxed (row : List α) (x : α)
    (hs : row.Pairwise (· ≤ ·)) :
    LowerBarrierRelaxed (scheduleBottomInsert row x) row := by
  induction row with
  | nil => exact .nil (scheduleBottomInsert [] x)
  | cons a row ih =>
      by_cases hxa : x ≤ a
      · change LowerBarrierRelaxed (List.orderedInsert (· ≤ ·) x (a :: row)) (a :: row)
        rw [List.orderedInsert_cons_of_le (· ≤ ·) row hxa]
        exact .cons hxa (lowerBarrierRelaxed_cons_of_sorted hs)
      · change LowerBarrierRelaxed (List.orderedInsert (· ≤ ·) x (a :: row)) (a :: row)
        rw [List.orderedInsert_of_not_le (· ≤ ·) row hxa]
        exact .cons le_rfl (ih (List.pairwise_cons.mp hs).2)

theorem scheduleBottomInsert_columns {lower upper : List α} (x : α)
    (hs : lower.Pairwise (· ≤ ·)) (hfit : RowsFit lower upper) :
    RowsFit (scheduleBottomInsert lower x) upper :=
  RowsFit.relax_lower (scheduleBottomInsert_lower_relaxed lower x hs) hfit

theorem scheduleCountLT_bottomInsert_gain (row : List α) (x t : α) (hxt : x < t) :
    scheduleCountLT (scheduleBottomInsert row x) t = scheduleCountLT row t + 1 := by
  have h := (scheduleBottomInsert_conservation row x).countP_eq
    (fun z => decide (z < t))
  simpa [scheduleCountLT, List.countP_cons, hxt] using h

/-- A strictly later visit inserted directly above the newly enlarged bottom
row is absorbed. This is the row-zero endpoint case of the exchange. -/
theorem scheduleBottomInsert_adjacent_none (lower upper : List α) (x y : α)
    (hlower : lower.Pairwise (· ≤ ·)) (hupper : upper.Pairwise (· ≤ ·))
    (hfit : RowsFit lower upper) (hxy : x < y) :
    (scheduleRowInsert (scheduleBottomInsert lower x) upper y).2 = none := by
  cases hpop : (scheduleRowInsert (scheduleBottomInsert lower x) upper y).2 with
  | none => rfl
  | some p =>
      have hyp := scheduleRowInsert_pop_ge (scheduleBottomInsert lower x) upper y p hpop
      have hgain := scheduleCountLT_bottomInsert_gain lower x p (hxy.trans_le hyp)
      have hcapacity := hfit.countLE_le_countLT p
      have hsaturated := scheduleRowInsert_pop_saturated
        (scheduleBottomInsert lower x) upper y p
        (scheduleBottomInsert_pairwise_le lower x hlower) hupper
        (scheduleBottomInsert_columns x hlower hfit) hpop
      omega

end HigherSpecht
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/HanadaColumnDeletion.lean -/



/-!
# Literal deletion of an upper column tail

The operation below removes the same indexed entry from every row at or
above a specified row.  Each row is compacted immediately.  Its validity,
removed tokens, exact prefix-length deficit, and sublevel counts are proved
from the actual row stack.  In particular, the numerical deletion identity
used by the endpoint argument is a conclusion of this operation.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

namespace RowsFit

theorem getElem_lt {lower upper : List α} (h : RowsFit lower upper)
    (j : ℕ) (hj : j < upper.length) : lower[j]'(hj.trans_le h.length_le) < upper[j] := by
  induction h generalizing j with
  | nil => simp at hj
  | cons hlt htail ih =>
      cases j with
      | zero => exact hlt
      | succ j => exact ih j (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hj)

theorem eraseIdx_both {lower upper : List α} (h : RowsFit lower upper) (c : ℕ) :
    RowsFit (lower.eraseIdx c) (upper.eraseIdx c) := by
  induction h generalizing c with
  | nil => exact .nil _
  | cons hlt htail ih =>
      cases c with
      | zero => exact htail
      | succ c => exact .cons hlt (ih c)

/-- Deleting only an upper entry preserves strict columns because a sorted
lower row is no larger than its own shifted tail. -/
theorem eraseIdx_upper {lower upper : List α} (h : RowsFit lower upper)
    (hlower : lower.Pairwise (· ≤ ·)) (c : ℕ) : RowsFit lower (upper.eraseIdx c) := by
  induction h generalizing c with
  | nil => exact .nil _
  | @cons l u lower upper hlt htail ih =>
      cases c with
      | zero =>
          exact RowsFit.relax_lower (lowerBarrierRelaxed_cons_of_sorted hlower) htail
      | succ c => exact .cons hlt (ih (List.pairwise_cons.mp hlower).2 c)

end RowsFit

def deletedColumn (rows : List (List α)) (c : ℕ) : List α :=
  rows.filterMap (fun row => row[c]?)

def eraseColumnAbove (c : ℕ) : ℕ → List (List α) → List (List α)
  | 0, rows => rows.map (fun row => row.eraseIdx c)
  | _ + 1, [] => []
  | start + 1, row :: tail => row :: eraseColumnAbove c start tail

def deletedColumnAbove (rows : List (List α)) (start c : ℕ) : List α :=
  deletedColumn (rows.drop start) c

@[simp] theorem eraseColumnAbove_zero (c : ℕ) (rows : List (List α)) :
    eraseColumnAbove c 0 rows = rows.map (fun row => row.eraseIdx c) := rfl

@[simp] theorem eraseColumnAbove_nil (c start : ℕ) :
    eraseColumnAbove c start ([] : List (List α)) = [] := by cases start <;> rfl

theorem eraseColumnAbove_getD (c start : ℕ) (rows : List (List α)) (j : ℕ) :
    (eraseColumnAbove c start rows).getD j [] =
      if start ≤ j then (rows.getD j []).eraseIdx c else rows.getD j [] := by
  induction start generalizing rows j with
  | zero =>
      simpa only [eraseColumnAbove, Nat.zero_le, if_pos, List.eraseIdx_nil] using
        (List.getD_map (l := rows) (d := ([] : List α)) (n := j) (fun row => row.eraseIdx c))
  | succ start ih =>
      cases rows with
      | nil => simp
      | cons row tail =>
          cases j with
          | zero => simp [eraseColumnAbove]
          | succ j =>
              simpa only [eraseColumnAbove, List.getD_cons_succ, Nat.succ_le_succ_iff] using
                ih tail j

theorem eraseColumnAbove_eq_take_drop (c start : ℕ) (rows : List (List α)) :
    eraseColumnAbove c start rows =
      rows.take start ++ (rows.drop start).map (fun row => row.eraseIdx c) := by
  induction start generalizing rows with
  | zero => simp [eraseColumnAbove]
  | succ start ih => cases rows <;> simp [eraseColumnAbove, ih]

namespace ScheduleRowsValid

variable {height : α → ℕ} {r : ℕ} {rows : List (List α)}

theorem map_eraseIdx (h : ScheduleRowsValid height r rows) (c : ℕ) :
    ScheduleRowsValid height r (rows.map (fun row => row.eraseIdx c)) := by
  induction h with
  | nil r => exact ScheduleRowsValid.nil (height := height) r
  | @cons r row tail hs hh hc ht ih =>
      refine .cons (hs.eraseIdx c) (fun x hx => hh x (List.mem_of_mem_eraseIdx hx)) ?_ ih
      cases tail with
      | nil => exact .nil _
      | cons upper rest => exact hc.eraseIdx_both c

theorem eraseColumnAbove (h : ScheduleRowsValid height r rows) (c start : ℕ) :
    ScheduleRowsValid height r (HigherSpecht.eraseColumnAbove c start rows) := by
  induction start generalizing r rows with
  | zero => exact h.map_eraseIdx c
  | succ start ih =>
      cases h with
      | nil => exact .nil r
      | @cons r row tail hs hh hc ht =>
          refine .cons hs hh ?_ (ih ht)
          cases start with
          | zero =>
              cases tail with
              | nil => exact .nil _
              | cons upper rest => exact hc.eraseIdx_upper hs c
          | succ start =>
              cases tail <;> simpa only [HigherSpecht.eraseColumnAbove, List.headD_cons,
                List.headD_nil] using hc

/-- Once the column has ended it cannot reappear in a later row. -/
theorem eraseColumn_eq_self_of_head_le (h : ScheduleRowsValid height r rows)
    (c : ℕ) (hc : (rows.headD []).length ≤ c) :
    rows.map (fun row => row.eraseIdx c) = rows ∧ deletedColumn rows c = [] := by
  induction h with
  | nil => simp [deletedColumn]
  | @cons r row tail hs hh hfit ht ih =>
      have hrow : row.length ≤ c := hc
      have htail : (tail.headD []).length ≤ c := hfit.length_le.trans hrow
      obtain ⟨he, hd⟩ := ih htail
      have hnone : row[c]? = none := List.getElem?_eq_none_iff.mpr hrow
      simp only [List.map_cons, List.eraseIdx_of_length_le hrow, he, deletedColumn,
        List.filterMap_cons, hnone, Option.map_none, List.nil_append]
      exact ⟨True.intro, hd⟩

theorem column_lt_of_mem {lower : List α} (h : ScheduleRowsValid height r rows)
    (hfit : RowsFit lower (rows.headD [])) {c : ℕ} {x y : α}
    (hx : lower[c]? = some x) (hy : y ∈ deletedColumn rows c) : x < y := by
  induction h generalizing lower x with
  | nil => simp [deletedColumn] at hy
  | @cons r row tail hs hh hc ht ih =>
      cases hz : row[c]? with
      | none =>
          have hlen : row.length ≤ c := List.getElem?_eq_none_iff.mp hz
          have hd := (ScheduleRowsValid.cons hs hh hc ht).eraseColumn_eq_self_of_head_le c hlen
          rw [hd.2] at hy
          simp at hy
      | some z =>
          obtain ⟨hcz, hczv⟩ := List.getElem?_eq_some_iff.mp hz
          obtain ⟨hcx, hcxv⟩ := List.getElem?_eq_some_iff.mp hx
          have hxz : x < z := by
            simpa only [List.headD_cons, hcxv, hczv] using hfit.getElem_lt c hcz
          have hy' : y = z ∨ y ∈ deletedColumn tail c := by
            simpa only [deletedColumn, List.filterMap_cons, hz, Option.map_some,
              List.mem_cons] using hy
          rcases hy' with rfl | hy'
          · exact hxz
          · exact hxz.trans (ih hc hz hy')

theorem deletedColumn_graded (h : ScheduleRowsValid height r rows) (c : ℕ) :
    GradedIncreasingInputs height r (deletedColumn rows c) := by
  induction h with
  | nil r => exact GradedIncreasingInputs.nil (height := height) r
  | @cons r row tail hs hh hc ht ih =>
      cases hx : row[c]? with
      | none =>
          have hlen : row.length ≤ c := List.getElem?_eq_none_iff.mp hx
          have hd := (ScheduleRowsValid.cons hs hh hc ht).eraseColumn_eq_self_of_head_le c hlen
          rw [hd.2]
          exact .nil r
      | some x =>
          have hxmem : x ∈ row := List.mem_of_getElem? hx
          rw [deletedColumn, List.filterMap_cons, hx]
          exact .cons (hh x hxmem) (fun y hy => ht.column_lt_of_mem hc hx hy) ih

end ScheduleRowsValid

@[simp] theorem stackRowPrefix_zero (rows : List (List α)) : stackRowPrefix rows 0 = 0 := by
  simp [stackRowPrefix]

@[simp] theorem stackRowPrefix_nil (r : ℕ) : stackRowPrefix ([] : List (List α)) r = 0 := by
  simp [stackRowPrefix]

theorem stackRowPrefix_cons_succ (row : List α) (rows : List (List α)) (r : ℕ) :
    stackRowPrefix (row :: rows) (r + 1) = row.length + stackRowPrefix rows r := by
  unfold stackRowPrefix
  rw [Finset.sum_range_succ']
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  exact Nat.add_comm _ _

/-- Removing a complete column subtracts exactly one entry from the first
`deletedColumn.length` rows and no entry thereafter. -/
theorem ScheduleRowsValid.stackRowPrefix_map_eraseIdx
    {height : α → ℕ} {r : ℕ} {rows : List (List α)}
    (h : ScheduleRowsValid height r rows) (c R : ℕ) :
    stackRowPrefix rows R = stackRowPrefix (rows.map (fun row => row.eraseIdx c)) R +
      min (deletedColumn rows c).length R := by
  induction h generalizing R with
  | nil => simp [deletedColumn]
  | @cons r row tail hs hh hc ht ih =>
      cases hx : row[c]? with
      | none =>
          have hlen : row.length ≤ c := List.getElem?_eq_none_iff.mp hx
          obtain ⟨he, hd⟩ :=
            (ScheduleRowsValid.cons hs hh hc ht).eraseColumn_eq_self_of_head_le c hlen
          simp only [he, hd, List.length_nil, Nat.zero_min, Nat.add_zero]
      | some x =>
          obtain ⟨hcx, hget⟩ := List.getElem?_eq_some_iff.mp hx
          have hlen := List.length_eraseIdx_add_one hcx
          cases R with
          | zero => simp
          | succ R =>
              rw [List.map_cons, stackRowPrefix_cons_succ, stackRowPrefix_cons_succ, ih]
              have hdel : deletedColumn (row :: tail) c = x :: deletedColumn tail c := by
                simp [deletedColumn, hx]
              rw [hdel, List.length_cons]
              omega

/-- The exact prefix deficit for the literal upper-column deletion. -/
theorem ScheduleRowsValid.stackRowPrefix_eraseColumnAbove
    {height : α → ℕ} {r : ℕ} {rows : List (List α)}
    (h : ScheduleRowsValid height r rows) (c start R : ℕ) :
    stackRowPrefix rows R = stackRowPrefix (HigherSpecht.eraseColumnAbove c start rows) R +
      min (deletedColumnAbove rows start c).length (R - start) := by
  induction start generalizing r rows R with
  | zero => simpa only [HigherSpecht.eraseColumnAbove_zero,
      deletedColumnAbove, List.drop_zero, Nat.sub_zero] using
      h.stackRowPrefix_map_eraseIdx c R
  | succ start ih =>
      cases h with
      | nil => simp [deletedColumnAbove, deletedColumn]
      | @cons r row tail hs hh hc ht =>
          cases R with
          | zero => simp
          | succ R =>
              simp only [HigherSpecht.eraseColumnAbove, stackRowPrefix_cons_succ,
                deletedColumnAbove, List.drop_succ_cons, Nat.add_sub_add_right]
              simpa only [deletedColumnAbove, Nat.add_assoc] using
                congrArg (fun v : ℕ => row.length + v) (ih ht R)

theorem deletedColumn_conservation (rows : List (List α)) (c : ℕ) :
    (deletedColumn rows c ++ (rows.map (fun row => row.eraseIdx c)).flatten).Perm rows.flatten := by
  induction rows with
  | nil => simp [deletedColumn]
  | cons row tail ih =>
      cases hx : row[c]? with
      | none =>
          have hlen : row.length ≤ c := List.getElem?_eq_none_iff.mp hx
          apply List.perm_iff_count.mpr
          intro y
          have ht := ih.count_eq y
          simp only [deletedColumn, List.filterMap_cons, hx, List.map_cons,
            List.flatten_cons, List.eraseIdx_of_length_le hlen, List.count_append] at *
          omega
      | some x =>
          obtain ⟨hc, hcx⟩ := List.getElem?_eq_some_iff.mp hx
          have hp : (x :: row.eraseIdx c).Perm row := by
            simpa only [hcx] using List.getElem_cons_eraseIdx_perm hc
          apply List.perm_iff_count.mpr
          intro y
          have hrow := hp.count_eq y
          have ht := ih.count_eq y
          simp only [deletedColumn, List.filterMap_cons, hx, List.map_cons,
            List.flatten_cons, List.count_append, List.count_cons, List.cons_append] at *
          omega

theorem deletedColumnAbove_conservation (rows : List (List α)) (start c : ℕ) :
    (deletedColumnAbove rows start c ++ (eraseColumnAbove c start rows).flatten).Perm
      rows.flatten := by
  induction start generalizing rows with
  | zero => exact deletedColumn_conservation rows c
  | succ start ih =>
      cases rows with
      | nil => simp [deletedColumnAbove, deletedColumn]
      | cons row tail =>
          apply List.perm_iff_count.mpr
          intro y
          have ht := (ih tail).count_eq y
          simp only [deletedColumnAbove, List.drop_succ_cons, eraseColumnAbove,
            List.flatten_cons, List.count_append] at *
          omega

theorem scheduleCountLE_eraseIdx_of_lt (row : List α) (c : ℕ) (cutoff x : α)
    (hx : row[c]? = some x) (hlt : cutoff < x) :
    scheduleCountLE (row.eraseIdx c) cutoff = scheduleCountLE row cutoff := by
  obtain ⟨hc, hcx⟩ := List.getElem?_eq_some_iff.mp hx
  have hp : (x :: row.eraseIdx c).Perm row := by
    simpa only [hcx] using List.getElem_cons_eraseIdx_perm hc
  have h := hp.countP_eq (fun z => decide (z ≤ cutoff))
  simpa [scheduleCountLE, List.countP_cons, not_le_of_gt hlt] using h

theorem eraseColumnAbove_processed_counts (rows : List (List α)) (start c : ℕ) (cutoff : α)
    (hremoved : ∀ z ∈ deletedColumnAbove rows start c, cutoff < z) (j : ℕ) :
    scheduleCountLE ((eraseColumnAbove c start rows).getD j []) cutoff =
      scheduleCountLE (rows.getD j []) cutoff := by
  induction start generalizing rows j with
  | zero =>
      induction rows generalizing j with
      | nil => simp
      | cons row tail ih =>
          have htail : ∀ z ∈ deletedColumnAbove tail 0 c, cutoff < z := by
            intro z hz
            apply hremoved z
            change z ∈ tail.filterMap (fun row => row[c]?) at hz
            change z ∈ (row :: tail).filterMap (fun row => row[c]?)
            obtain ⟨a, ha, haz⟩ := List.mem_filterMap.mp hz
            exact List.mem_filterMap.mpr ⟨a, List.mem_cons_of_mem row ha, haz⟩
          cases j with
          | zero =>
              cases hx : row[c]? with
              | none =>
                  have hlen : row.length ≤ c := List.getElem?_eq_none_iff.mp hx
                  simp [eraseColumnAbove, List.eraseIdx_of_length_le hlen]
              | some x =>
                  exact scheduleCountLE_eraseIdx_of_lt row c cutoff x hx (hremoved x (by
                    simp [deletedColumnAbove, deletedColumn, hx]))
          | succ j => exact ih htail j
  | succ start ih =>
      cases rows with
      | nil => simp
      | cons row tail =>
          cases j with
          | zero => rfl
          | succ j => exact ih tail hremoved j

end HigherSpecht
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/HanadaProcessedPrefixes.lean -/



/-!
# Literal preservation of already processed visits

This strengthens the numerical sublevel-count effects to equality of the
actual filtered rows.  Sorting is used only to identify a threshold prefix
with the corresponding filter.  The insertion and deletion proofs retain
the actual visit tokens.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem rowPrefixBelow_eq_filter (cutoff : α) {row : List α}
    (hs : row.Pairwise (· ≤ ·)) :
    rowPrefixBelow cutoff row = row.filter (fun z => decide (z < cutoff)) := by
  induction row with
  | nil => rfl
  | cons x row ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
      by_cases hx : x < cutoff
      · simp only [rowPrefixBelow, List.takeWhile_cons, List.filter_cons, hx, decide_true,
          if_pos rfl, if_true]
        exact congrArg (List.cons x) (ih htail)
      · have hempty : row.filter (fun z => decide (z < cutoff)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro z hz
          have hcz : cutoff ≤ z := (le_of_not_gt hx).trans (hhead z hz)
          simpa only [decide_eq_true_eq] using (not_lt.mpr hcz)
        simp [rowPrefixBelow, hx, hempty]

theorem ScheduleBumpRoute.processed_prefixes_of_le
    {advance : α → α} (hadvance : ∀ z, z < advance z)
    {lower : List α} {rows result : List (List α)} {x : α} {endpoint : ℕ}
    (h : ScheduleBumpRoute advance lower rows x result endpoint)
    (cutoff : α) (hcx : cutoff ≤ x) (j : ℕ) :
    rowPrefixBelow cutoff (result.getD j []) = rowPrefixBelow cutoff (rows.getD j []) := by
  induction h generalizing j with
  | top lower row x hs =>
      have hc := rowPrefixBelow_scheduleRowInsert_of_le lower [] hcx
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => rfl
  | stop lower upper row tail x hs =>
      have hc := rowPrefixBelow_scheduleRowInsert_of_le lower upper hcx
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => rfl
  | pass lower upper row tail result x p endpoint hs hn ih =>
      have hcp : cutoff ≤ advance p :=
        (hcx.trans (scheduleRowInsert_pop_ge lower upper x p (by rw [hs]))).trans
          (hadvance p).le
      have hc := rowPrefixBelow_scheduleRowInsert_of_le lower upper hcx
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => exact ih hcp j

theorem ConsecutiveBumpRoutes.processed_prefixes_of_le
    {advance : α → α} (hadvance : ∀ z, z < advance z)
    {lower : List α} {rows result : List (List α)} {inputs : List α} {endpoints : List ℕ}
    (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints)
    (cutoff : α) (hinputs : ∀ x ∈ inputs, cutoff ≤ x) (j : ℕ) :
    rowPrefixBelow cutoff (result.getD j []) = rowPrefixBelow cutoff (rows.getD j []) := by
  induction h generalizing j with
  | nil => rfl
  | cons lower row rows tail output x inputs endpoint endpoints first rest ih =>
      have hfirst := first.processed_prefixes_of_le hadvance cutoff (hinputs x (by simp))
      have hrest := ih (fun z hz => hinputs z (List.mem_cons_of_mem x hz))
      cases j with
      | zero => exact hfirst 0
      | succ j => exact (hrest j).trans (hfirst (j + 1))

theorem ConsecutiveBumpRoutes.processed_filters_of_le
    {advance : α → α} {height : α → ℕ}
    (hadvance : ∀ z, z < advance z) (hheight : ∀ z, height (advance z) = height z + 1)
    {lower : List α} {rows result : List (List α)} {inputs : List α} {endpoints : List ℕ}
    (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints)
    {r : ℕ} (hrows : ScheduleRowsValid height r rows)
    (hgraded : GradedIncreasingInputs height r inputs)
    (cutoff : α) (hinputs : ∀ x ∈ inputs, cutoff ≤ x) (j : ℕ) :
    (result.getD j []).filter (fun z => decide (z < cutoff)) =
      (rows.getD j []).filter (fun z => decide (z < cutoff)) := by
  rw [← rowPrefixBelow_eq_filter cutoff ((h.valid hheight hrows hgraded).getD_sorted j),
    ← rowPrefixBelow_eq_filter cutoff (hrows.getD_sorted j)]
  exact h.processed_prefixes_of_le hadvance cutoff hinputs j

theorem filter_eraseIdx_of_getElem?_not {β : Type*} (row : List β) (c : ℕ)
    (p : β → Bool) (x : β) (hx : row[c]? = some x) (hpx : p x = false) :
    (row.eraseIdx c).filter p = row.filter p := by
  induction row generalizing c with
  | nil => simp at hx
  | cons y row ih =>
      cases c with
      | zero =>
          have hxy : y = x := Option.some.inj hx
          simp [hxy, hpx]
      | succ c =>
          simpa only [List.eraseIdx_cons_succ, List.filter_cons, ih c hx] using
            (rfl : (if p y then y :: row.filter p else row.filter p) = _)

theorem eraseColumnAbove_processed_filters (rows : List (List α)) (start c : ℕ) (cutoff : α)
    (hremoved : ∀ z ∈ deletedColumnAbove rows start c, cutoff ≤ z) (j : ℕ) :
    ((eraseColumnAbove c start rows).getD j []).filter (fun z => decide (z < cutoff)) =
      (rows.getD j []).filter (fun z => decide (z < cutoff)) := by
  induction start generalizing rows j with
  | zero =>
      induction rows generalizing j with
      | nil => simp
      | cons row tail ih =>
          have htail : ∀ z ∈ deletedColumnAbove tail 0 c, cutoff ≤ z := by
            intro z hz
            apply hremoved z
            change z ∈ tail.filterMap (fun row => row[c]?) at hz
            change z ∈ (row :: tail).filterMap (fun row => row[c]?)
            obtain ⟨a, ha, haz⟩ := List.mem_filterMap.mp hz
            exact List.mem_filterMap.mpr ⟨a, List.mem_cons_of_mem row ha, haz⟩
          cases j with
          | zero =>
              cases hx : row[c]? with
              | none =>
                  have hlen : row.length ≤ c := List.getElem?_eq_none_iff.mp hx
                  simp [eraseColumnAbove, List.eraseIdx_of_length_le hlen]
              | some x =>
                  have hcx := hremoved x (by simp [deletedColumnAbove, deletedColumn, hx])
                  exact filter_eraseIdx_of_getElem?_not row c _ x hx (by
                    simp only [not_lt.mpr hcx, decide_false])
          | succ j => exact ih htail j
  | succ start ih =>
      cases rows with
      | nil => simp
      | cons row tail =>
          cases j with
          | zero => rfl
          | succ j => exact ih tail hremoved j

end HigherSpecht
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/HanadaShiftedColumn.lean -/



/-!
# Actual shifted column inputs and the first bounded route

All removed tokens are taken from the literal indexed column.  Subtracting
the same number of visits preserves their strict order on its proved domain
and moves their heights down by exactly that number.  The first route is
then constructed from the unchanged rows below the deletion frontier.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem ScheduleRowsValid.drop {height : α → ℕ} {r : ℕ} {rows : List (List α)}
    (h : ScheduleRowsValid height r rows) (k : ℕ) :
    ScheduleRowsValid height (r + k) (rows.drop k) := by
  induction k generalizing r rows with
  | zero => simpa using h
  | succ k ih =>
      cases h with
      | nil => exact .nil _
      | cons hs hh hc ht =>
          simpa only [List.drop_succ_cons, Nat.add_assoc, Nat.add_comm 1 k] using ih ht

theorem ScheduleRowsValid.frontierFits {height : α → ℕ} {r : ℕ}
    {rows : List (List α)} {lower : List α}
    (h : ScheduleRowsValid height r rows) (hfit : RowsFit lower (rows.headD [])) (d : ℕ) :
    RouteFrontierFits lower (rows.take d) (rows.getD d []) := by
  induction d generalizing r rows lower with
  | zero => simpa only [List.take_zero, List.headD_eq_getD, RouteFrontierFits] using hfit
  | succ d ih =>
      cases h with
      | nil => exact RowsFit.nil lower
      | cons hs hh hc ht => exact ih ht hc

theorem drop_eq_getD_cons_of_ne_nil (rows : List (List α)) (d : ℕ)
    (hne : rows.getD d [] ≠ []) :
    rows.drop d = rows.getD d [] :: rows.drop (d + 1) := by
  induction d generalizing rows with
  | zero => cases rows <;> simp_all
  | succ d ih =>
      cases rows with
      | nil => simp at hne
      | cons row tail =>
          simpa only [List.drop_succ_cons, List.getD_cons_succ] using ih tail hne

theorem eraseColumnAbove_eq_frontier (rows : List (List α)) (d c : ℕ)
    (hne : rows.getD d [] ≠ []) :
    eraseColumnAbove c d rows = rows.take d ++
      (rows.getD d []).eraseIdx c :: (rows.drop (d + 1)).map (fun row => row.eraseIdx c) := by
  rw [eraseColumnAbove_eq_take_drop, drop_eq_getD_cons_of_ne_nil rows d hne, List.map_cons]

theorem deletedColumnAbove_eq_frontier (rows : List (List α)) (d c : ℕ) {x : α}
    (hx : (rows.getD d [])[c]? = some x) :
    deletedColumnAbove rows d c = x :: deletedColumnAbove rows (d + 1) c := by
  have hne : rows.getD d [] ≠ [] := by
    intro h
    rw [h] at hx
    simp at hx
  unfold deletedColumnAbove
  rw [drop_eq_getD_cons_of_ne_nil rows d hne]
  simp only [deletedColumn, List.filterMap_cons, hx]

theorem eraseColumnAbove_add (rows : List (List α)) (c r d : ℕ) :
    eraseColumnAbove c (r + d) rows = rows.take r ++ eraseColumnAbove c d (rows.drop r) := by
  induction r generalizing rows with
  | zero => simp
  | succ r ih =>
      cases rows <;> simp [Nat.succ_add, eraseColumnAbove, ih]

theorem deletedColumnAbove_drop (rows : List (List α)) (r d c : ℕ) :
    deletedColumnAbove (rows.drop r) d c = deletedColumnAbove rows (r + d) c := by
  simp only [deletedColumnAbove, List.drop_drop, Nat.add_comm]

theorem pairwise_lt_of_pairwise_le_nodup {row : List α}
    (hs : row.Pairwise (· ≤ ·)) (hn : row.Nodup) : row.Pairwise (· < ·) := by
  exact (hs.and hn).imp (fun h => lt_of_le_of_ne h.1 h.2)

def retreatVisit {n : ℕ} (d : ℕ) (t : VisitTime n) : VisitTime n :=
  visitTime ((ofLex t).1 - d) (ofLex t).2

@[simp] theorem retreatVisit_position {n : ℕ} (d : ℕ) (t : VisitTime n) :
    (ofLex (retreatVisit d t)).2 = (ofLex t).2 := rfl

theorem retreatVisit_strictMonoOn {n : ℕ} (d : ℕ) {x y : VisitTime n}
    (hx : d ≤ (ofLex x).1) (hxy : x < y) : retreatVisit d x < retreatVisit d y := by
  rcases Prod.Lex.toLex_lt_toLex.mp hxy with h | ⟨h, hi⟩
  · change (ofLex x).1 < (ofLex y).1 at h
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl (by dsimp [retreatVisit, visitTime]; omega)
  · change (ofLex x).1 = (ofLex y).1 at h
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨by dsimp [retreatVisit, visitTime]; rw [h], hi⟩

theorem visitHeight_retreatVisit {n : ℕ} (a : Fin n → ℕ) (d : ℕ) (t : VisitTime n)
    (ht : d ≤ (ofLex t).1) : visitHeight a (retreatVisit d t) = visitHeight a t - d := by
  dsimp [visitHeight, retreatVisit, visitTime]
  omega

theorem advanceVisit_iterate {n : ℕ} (p k : ℕ) (i : Fin n) :
    advanceVisit^[k] (visitTime p i) = visitTime (p + k) i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem visit_round_le_of_le {n : ℕ} {x y : VisitTime n} (hxy : x ≤ y) :
    (ofLex x).1 ≤ (ofLex y).1 := by
  rcases Prod.Lex.toLex_le_toLex.mp hxy with h | ⟨h, hi⟩
  · exact h.le
  · exact h.le

theorem GradedIncreasingInputs.retreatVisit {n : ℕ} {a : Fin n → ℕ}
    {r : ℕ} {inputs : List (VisitTime n)}
    (h : GradedIncreasingInputs (visitHeight a) r inputs) (d : ℕ)
    (hvisits : ∀ t ∈ inputs, d ≤ (ofLex t).1) :
    GradedIncreasingInputs (visitHeight a) (r - d) (inputs.map (retreatVisit d)) := by
  induction h with
  | nil => exact .nil _
  | @cons r x tail hx hincr ht ih =>
      have hdx := hvisits x (by simp)
      have hdr : d ≤ r := by
        have h := hdx.trans (Nat.le_add_left (ofLex x).1 (a (ofLex x).2))
        change d ≤ visitHeight a x at h
        simpa only [hx] using h
      refine .cons (by rw [visitHeight_retreatVisit a d x hdx, hx]) ?_ ?_
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact retreatVisit_strictMonoOn d hdx (hincr z hz)
      · have htail := ih (fun t ht => hvisits t (List.mem_cons_of_mem x ht))
        convert htail using 1 <;> omega

/-- The actual column tail starts with the located token, and its shifted
tokens are strictly increasing at the consecutive intended target heights. -/
theorem shiftedColumn_inputs {n : ℕ} {a : Fin n → ℕ}
    {r : ℕ} {rows : List (List (VisitTime n))}
    (hrows : ScheduleRowsValid (visitHeight a) r rows)
    (d c p : ℕ) (i : Fin n)
    (hlocated : (rows.getD d [])[c]? = some (visitTime (p + d) i))
    (hr : r = a i + p) :
    ∃ tail,
      (deletedColumnAbove rows d c).map (retreatVisit d) = visitTime p i :: tail ∧
      GradedIncreasingInputs (visitHeight a) r (visitTime p i :: tail) ∧
      (∀ t ∈ deletedColumnAbove rows d c, visitTime p i ≤ t) ∧
      (∀ t ∈ deletedColumnAbove rows d c, d ≤ (ofLex t).1) := by
  have hcol := (hrows.drop d).deletedColumn_graded c
  change GradedIncreasingInputs (visitHeight a) (r + d) (deletedColumnAbove rows d c) at hcol
  have hfront := deletedColumnAbove_eq_frontier rows d c hlocated
  rw [hfront] at hcol
  cases hcol with
  | cons hh hincr htail =>
      have hmin : ∀ t ∈ deletedColumnAbove rows d c, visitTime (p + d) i ≤ t := by
        intro t ht
        rw [hfront] at ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact le_rfl
        · exact (hincr t ht).le
      have hvisits : ∀ t ∈ deletedColumnAbove rows d c, d ≤ (ofLex t).1 := by
        intro t ht
        exact (Nat.le_add_left d p).trans (visit_round_le_of_le (hmin t ht))
      have hgraded := ((hrows.drop d).deletedColumn_graded c).retreatVisit d hvisits
      have hmap : (deletedColumnAbove rows d c).map (retreatVisit d) = visitTime p i ::
          (deletedColumnAbove rows (d + 1) c).map (retreatVisit d) := by
        rw [hfront, List.map_cons]
        simp only [retreatVisit, visitTime, ofLex_toLex, Nat.add_sub_cancel]
      change GradedIncreasingInputs (visitHeight a) (r + d - d)
        ((deletedColumnAbove rows d c).map (retreatVisit d)) at hgraded
      rw [hmap] at hgraded
      refine ⟨_, hmap, ?_, ?_, hvisits⟩
      · simpa only [Nat.add_sub_cancel] using hgraded
      · intro t ht
        apply le_trans ?_ (hmin t ht)
        apply Prod.Lex.toLex_le_toLex.mpr
        by_cases hd : d = 0
        · exact Or.inr ⟨by omega, le_rfl⟩
        · exact Or.inl (by omega)

/-- Every token in a genuinely later column tail is strictly after the
current visit, before any shifting is performed. -/
theorem shiftedColumn_removed_later {n : ℕ} {a : Fin n → ℕ}
    {r : ℕ} {rows : List (List (VisitTime n))}
    (hrows : ScheduleRowsValid (visitHeight a) r rows)
    (d c p : ℕ) (i : Fin n) (hd : 0 < d)
    (hlocated : (rows.getD d [])[c]? = some (visitTime (p + d) i))
    (hr : r = a i + p) :
    ∀ t ∈ deletedColumnAbove rows d c, visitTime p i < t := by
  have hfront := deletedColumnAbove_eq_frontier rows d c hlocated
  have hcol := (hrows.drop d).deletedColumn_graded c
  change GradedIncreasingInputs (visitHeight a) (r + d) (deletedColumnAbove rows d c) at hcol
  rw [hfront] at hcol
  cases hcol with
  | cons hh hincr htail =>
      have hlt : visitTime p i < visitTime (p + d) i :=
        Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
      intro t ht
      rw [hfront] at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hlt
      · exact hlt.trans (hincr t ht)

theorem firstRoute_from_actual_column {n : ℕ} {a : Fin n → ℕ}
    {r : ℕ} {rows : List (List (VisitTime n))} {lower : List (VisitTime n)}
    (hrows : ScheduleRowsValid (visitHeight a) r rows)
    (hfit : RowsFit lower (rows.headD []))
    (d c p : ℕ) (i : Fin n)
    (hlocated : (rows.getD d [])[c]? = some (visitTime (p + d) i))
    (hnodup : (rows.getD d []).Nodup) :
    ∃ result endpoint,
      ScheduleBumpRoute advanceVisit lower (eraseColumnAbove c d rows) (visitTime p i)
        result endpoint ∧ endpoint ≤ d := by
  have hne : rows.getD d [] ≠ [] := by
    intro h
    rw [h] at hlocated
    simp at hlocated
  have hlen : d < rows.length := by
    by_contra h
    have he := List.getD_eq_default (l := rows) (d := ([] : List (VisitTime n)))
      (Nat.le_of_not_gt h)
    exact hne he
  obtain ⟨hc, hget⟩ := List.getElem?_eq_some_iff.mp hlocated
  have herase : (rows.getD d []).erase (visitTime (p + d) i) = (rows.getD d []).eraseIdx c := by
    simpa only [hget] using hnodup.erase_getElem c hc
  have hsorted := pairwise_lt_of_pairwise_le_nodup (hrows.getD_sorted d) hnodup
  have hreach : visitTime (p + d) i ≤ advanceVisit^[(rows.take d).length] (visitTime p i) := by
    rw [List.length_take, Nat.min_eq_left hlen.le, advanceVisit_iterate]
  obtain ⟨result, endpoint, hroute, hbound⟩ := ScheduleBumpRoute.exists_to_deleted_frontier
    advanceVisit advanceVisit_strictMono.monotone lower (rows.take d) (rows.getD d [])
      ((rows.drop (d + 1)).map (fun row => row.eraseIdx c))
      (visitTime (p + d) i) (visitTime p i) hsorted (List.mem_of_getElem? hlocated)
      (hrows.frontierFits hfit d) hreach
  refine ⟨result, endpoint, ?_, ?_⟩
  · have hrowsEq : rows.take d ++
        (rows.getD d []).erase (visitTime (p + d) i) ::
          (rows.drop (d + 1)).map (fun row => row.eraseIdx c) =
        eraseColumnAbove c d rows := by
      rw [herase, eraseColumnAbove_eq_frontier rows d c hne]
    exact Eq.mp (congrArg (fun rs =>
      ScheduleBumpRoute advanceVisit lower rs (visitTime p i) result endpoint) hrowsEq) hroute
  · exact hbound.trans (List.length_take_le _ _)

end HigherSpecht
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/HanadaQueueTimes.lean -/



/-!
# Visit times in the actual cyclic queue

All pending timestamps lie in one scan window. Consequently a scheduled
visit of a pending token that is strictly after the present front is at
least that token's actual queued visit. Rejection advances the same token
by exactly one visit. These statements concern the genuine sparse queue;
they do not insert fictitious dense scans or assume a completed filling.
-/

namespace HigherSpecht

def visitStamp {n : ℕ} (z : VisitTime n) : ℕ :=
  (ofLex z).1 * n + (ofLex z).2.val

@[simp] theorem visitStamp_visitTime {n : ℕ} (p : ℕ) (i : Fin n) :
    visitStamp (visitTime p i) = p * n + i.val := rfl

@[simp] theorem visitStamp_token {n : ℕ} (t : CyclingToken n) :
    visitStamp (visitTime t.round t.position) = t.stamp := rfl

theorem visitStamp_strictMono {n : ℕ} : StrictMono (visitStamp (n := n)) := by
  intro z w hzw
  change toLex (ofLex z) < toLex (ofLex w) at hzw
  rcases Prod.Lex.toLex_lt_toLex.mp hzw with hr | ⟨hr, hi⟩
  · have hmul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at hmul
    have hz := (ofLex z).2.isLt
    have hw := (ofLex w).2.isLt
    dsimp only [visitStamp]
    omega
  · dsimp only [visitStamp]
    rw [hr]
    exact Nat.add_lt_add_left hi _

theorem cyclingQueue_tail_front_lt {n : ℕ}
    {t u : CyclingToken n} {q : List (CyclingToken n)}
    (hq : CyclingQueueValid (t :: q)) (hu : u ∈ q) :
    visitTime t.round t.position < visitTime u.round u.position := by
  apply (visitStamp_strictMono (n := n)).lt_iff_lt.mp
  simpa only [visitStamp_token] using (List.pairwise_cons.mp hq.1).1 u hu

theorem cyclingQueue_after_front_lt {n : ℕ}
    {t u : CyclingToken n} {q : List (CyclingToken n)}
    (hq : CyclingQueueValid (t :: q)) (hu : u ∈ q ++ [t.bump]) :
    visitTime t.round t.position < visitTime u.round u.position := by
  rcases List.mem_append.mp hu with hu | hu
  · exact cyclingQueue_tail_front_lt hq hu
  · have hut : u = t.bump := List.mem_singleton.mp hu
    subst u
    apply (visitStamp_strictMono (n := n)).lt_iff_lt.mp
    simpa only [visitStamp_token] using t.stamp_lt_bump

/-- The queued visit of another pending token cannot lie strictly between
two successive possible visits of that token after the current front. -/
theorem cyclingQueue_visit_le_of_after_front {n : ℕ}
    {t u : CyclingToken n} {q : List (CyclingToken n)}
    (hq : CyclingQueueValid (t :: q)) (hu : u ∈ q) {z : VisitTime n}
    (hz : (ofLex z).2 = u.position)
    (htz : visitTime t.round t.position < z) :
    visitTime u.round u.position ≤ z := by
  have hwindow : u.stamp < t.stamp + n :=
    hq.2 t (by simp) u (by simp [hu])
  have hstamp := visitStamp_strictMono htz
  by_contra hle
  have hzu : z < visitTime u.round u.position := lt_of_not_ge hle
  change toLex (ofLex z) < toLex (u.round, u.position) at hzu
  have hr : (ofLex z).1 < u.round := by
    rcases Prod.Lex.toLex_lt_toLex.mp hzu with hr | ⟨hr, hi⟩
    · exact hr
    · rw [hz] at hi
      exact False.elim ((lt_irrefl u.position) hi)
  have hmul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hmul
  change t.stamp < (ofLex z).1 * n + (ofLex z).2.val at hstamp
  rw [hz] at hstamp
  dsimp only [CyclingToken.stamp] at hstamp hwindow
  omega

/-- A later visit of the same token is at least its once-bumped visit. -/
theorem cyclingToken_bump_visit_le_of_after {n : ℕ} (t : CyclingToken n)
    {z : VisitTime n} (hz : (ofLex z).2 = t.position)
    (htz : visitTime t.round t.position < z) :
    visitTime t.bump.round t.bump.position ≤ z := by
  change toLex (t.round, t.position) < toLex (ofLex z) at htz
  have hr : t.round + 1 ≤ (ofLex z).1 := by
    rcases Prod.Lex.toLex_lt_toLex.mp htz with hr | ⟨hr, hi⟩
    · exact Nat.succ_le_of_lt hr
    · rw [hz] at hi
      exact False.elim ((lt_irrefl t.position) hi)
  change toLex (t.round + 1, t.position) ≤ toLex (ofLex z)
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases hr.eq_or_lt with heq | hlt
  · exact Or.inr ⟨heq, by rw [hz]⟩
  · exact Or.inl hlt

/-- The same exact bound covers every entry of the queue after rejection. -/
theorem cyclingQueue_reject_visit_le_of_after_front {n : ℕ}
    {t u : CyclingToken n} {q : List (CyclingToken n)}
    (hq : CyclingQueueValid (t :: q)) (hu : u ∈ q ++ [t.bump])
    {z : VisitTime n} (hz : (ofLex z).2 = u.position)
    (htz : visitTime t.round t.position < z) :
    visitTime u.round u.position ≤ z := by
  rcases List.mem_append.mp hu with hu | hu
  · exact cyclingQueue_visit_le_of_after_front hq hu hz htz
  · have hut : u = t.bump := List.mem_singleton.mp hu
    subst u
    exact cyclingToken_bump_visit_le_of_after t hz htz

end HigherSpecht
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/HanadaGreedyInvariant.lean -/



/-!
# Processed-token invariant for the actual greedy cyclic queue

The row stack retains all original tokens once. Below the current visit its
token IDs are exactly the accepted IDs, and its row counts are exactly the
current Young diagram. The remaining entries are compared with the genuine
queue, not with an artificial dense scan.

This file supplies the invariant's initial and terminal facts and locates the
current pending token in the comparison rows. The exchange step must be
provided by the literal column deletion and upward routes; it is not included
as a hypothesis in a claimed catabolism or counting theorem.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def acceptedPositions {n : ℕ} (s : LabeledCatState n) : List (Fin n) :=
  s.accepted.map (fun z => z.1.position)

def processedPositions {n : ℕ} (rows : List (List (VisitTime n)))
    (cutoff : VisitTime n) : List (Fin n) :=
  (rows.flatten.filter (fun z => decide (z < cutoff))).map (fun z => (ofLex z).2)

theorem scheduleCountLT_le_countLE {α : Type*} [LinearOrder α]
    (row : List α) (t : α) : scheduleCountLT row t ≤ scheduleCountLE row t := by
  apply List.countP_mono_left
  intro z hz hzt
  simpa only [decide_eq_true_eq] using (show z < t from by simpa using hzt).le

theorem scheduleCountLT_lt_countLE_of_mem {α : Type*} [LinearOrder α]
    {row : List α} {t : α} (ht : t ∈ row) :
    scheduleCountLT row t < scheduleCountLE row t := by
  induction row with
  | nil => simp at ht
  | cons u row ih =>
      by_cases hu : u = t
      · subst u
        have hle := scheduleCountLT_le_countLE row t
        simp only [scheduleCountLT_cons, scheduleCountLE_cons, lt_self_iff_false,
          le_refl, if_false, if_true, Nat.add_zero]
        omega
      · have htrow : t ∈ row := (List.mem_cons.mp ht).resolve_left (Ne.symm hu)
        have htail := ih htrow
        by_cases hut : u < t
        · simp only [scheduleCountLT_cons, scheduleCountLE_cons,
            if_pos hut, if_pos hut.le]
          omega
        · have hnle : ¬ u ≤ t := fun h => hut (lt_of_le_of_ne h hu)
          simpa only [scheduleCountLT_cons, scheduleCountLE_cons,
            if_neg hut, if_neg hnle, Nat.add_zero] using htail

structure GreedyRowsInvariant {n : ℕ} (a : Fin n → ℕ)
    (initialShape : YoungDiagram) (s : LabeledCatState n) (cutoff : VisitTime n) where
  rows : List (List (VisitTime n))
  valid : ScheduleRowsValid (visitHeight a) 0 rows
  content : (rows.flatten.map (fun z => (ofLex z).2)).Perm (List.finRange n)
  processed : (processedPositions rows cutoff).Perm (acceptedPositions s)
  counts : ∀ r, scheduleCountLT (rows.getD r []) cutoff = s.shape.rowLen r
  dominance : ∀ k, (∑ r ∈ Finset.range k, initialShape.rowLen r) ≤ stackRowPrefix rows k

theorem LabeledInvariant.accepted_pending_disjoint {n : ℕ} {a : Fin n → ℕ}
    {s : LabeledCatState n} (hs : LabeledInvariant a s) {t : CyclingToken n}
    (ht : t ∈ s.pending) : t.position ∉ acceptedPositions s := by
  have hp : (acceptedPositions s ++ s.pending.map CyclingToken.position).Perm
      (List.finRange n) := by
    simpa only [acceptedPositions, List.map_map, Function.comp_def,
      initialCyclingQueue_positions] using hs.execution.positions
  have hn := hp.symm.nodup (List.nodup_finRange n)
  intro hi
  exact (List.nodup_append.mp hn).2.2 t.position hi t.position
    (List.mem_map.mpr ⟨t, ht, rfl⟩) rfl

namespace GreedyRowsInvariant

variable {n : ℕ} {a : Fin n → ℕ} {initialShape : YoungDiagram}
  {s : LabeledCatState n} {cutoff : VisitTime n}

theorem tokens_nodup (W : GreedyRowsInvariant a initialShape s cutoff) :
    (W.rows.flatten.map (fun z => (ofLex z).2)).Nodup :=
  W.content.symm.nodup (List.nodup_finRange n)

theorem entries_nodup (W : GreedyRowsInvariant a initialShape s cutoff) :
    W.rows.flatten.Nodup :=
  List.Nodup.of_map (fun z => (ofLex z).2) W.tokens_nodup

theorem pending_entry_not_lt (W : GreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) {t : CyclingToken n} (ht : t ∈ s.pending)
    {z : VisitTime n} (hz : z ∈ W.rows.flatten) (hid : (ofLex z).2 = t.position) :
    ¬ z < cutoff := by
  intro hzt
  have hm : t.position ∈ processedPositions W.rows cutoff := by
    exact List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨hz, by simpa using hzt⟩, hid⟩
  exact hs.accepted_pending_disjoint ht (W.processed.mem_iff.mp hm)

/-- The current pending token occurs in the actual comparison rows, at a row
no earlier than its current greedy insertion row. -/
theorem current_entry (W : GreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) {t : CyclingToken n} (ht : t ∈ s.pending)
    (hcutoff : cutoff = visitTime t.round t.position) :
    ∃ r z, z ∈ W.rows.getD r [] ∧ (ofLex z).2 = t.position ∧
      cutoff ≤ z ∧ tokenValue a t ≤ r := by
  have hm : t.position ∈ W.rows.flatten.map (fun z => (ofLex z).2) :=
    W.content.mem_iff.mpr (by simp)
  obtain ⟨z, hz, hid⟩ := List.mem_map.mp hm
  obtain ⟨row, hrow, hzrow⟩ := List.mem_flatten.mp hz
  obtain ⟨r, hr, hroweq⟩ := List.mem_iff_getElem.mp hrow
  have hz' : z ∈ W.rows.getD r [] := by
    rw [List.getD_eq_getElem _ _ hr, hroweq]
    exact hzrow
  have hge : cutoff ≤ z := le_of_not_gt (W.pending_entry_not_lt hs ht hz hid)
  have hheight := W.valid.getD_height r z hz'
  have hround : t.round ≤ (ofLex z).1 := by
    rw [hcutoff] at hge
    change toLex (t.round, t.position) ≤ toLex (ofLex z) at hge
    rcases Prod.Lex.toLex_le_toLex.mp hge with h | ⟨h, hi⟩
    · exact h.le
    · exact h.le
  refine ⟨r, z, hz', hid, hge, ?_⟩
  dsimp only [visitHeight] at hheight
  rw [hid, Nat.zero_add] at hheight
  rw [← hheight]
  exact Nat.add_le_add_left hround (a t.position)

/-- A rejected current visit cannot already occur in the comparison filling.
Otherwise strict-column capacity would make the corresponding row addable. -/
theorem current_absent_of_blocked (W : GreedyRowsInvariant a initialShape s cutoff)
    {t : CyclingToken n} (hcutoff : cutoff = visitTime t.round t.position)
    (hblocked : ¬ YoungDiagram.IsAddable s.shape
      (tokenValue a t, s.shape.rowLen (tokenValue a t))) : cutoff ∉ W.rows.flatten := by
  intro hmem
  obtain ⟨row, hrow, hcutrow⟩ := List.mem_flatten.mp hmem
  obtain ⟨r, hr, hroweq⟩ := List.mem_iff_getElem.mp hrow
  have hcutrow' : cutoff ∈ W.rows.getD r [] := by
    rw [List.getD_eq_getElem _ _ hr, hroweq]
    exact hcutrow
  have hheight := W.valid.getD_height r cutoff hcutrow'
  have hrval : r = tokenValue a t := by
    simpa only [hcutoff, visitHeight, visitTime, ofLex_toLex,
      tokenValue, Nat.zero_add] using hheight.symm
  have hrpos : r ≠ 0 := by
    intro hz
    apply hblocked
    rw [isAddable_rowEnd_iff]
    exact Or.inl (hrval.symm.trans hz)
  have hcolumns : RowsFit (W.rows.getD (r - 1) []) (W.rows.getD r []) := by
    have hc := W.valid.getD_columns (r - 1)
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hrpos)] using hc
  have hcapacity := hcolumns.countLE_le_countLT cutoff
  have hstrict := scheduleCountLT_lt_countLE_of_mem hcutrow'
  have hcurrent := W.counts r
  have hprevious := W.counts (r - 1)
  have hadd : s.shape.rowLen r < s.shape.rowLen (r - 1) := by omega
  apply hblocked
  rw [isAddable_rowEnd_iff]
  exact Or.inr (by simpa only [hrval] using hadd)

/-- At termination the complete token content forces every comparison entry
to have been processed. The exact per-row counts then identify the terminal
row lengths and transfer the maintained dominance. -/
theorem terminal_dominates (W : GreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) (hnil : s.pending = []) :
    Dominates s.shape initialShape := by
  have ha : (acceptedPositions s).Perm (List.finRange n) := by
    simpa only [acceptedPositions, List.map_map, Function.comp_def] using
      hs.complete_positions hnil
  have hprocessed := (W.processed.trans ha).length_eq
  have htotal := W.content.length_eq
  simp only [processedPositions, List.length_map, List.length_finRange] at hprocessed htotal
  have hfilter :
      (W.rows.flatten.filter (fun z => decide (z < cutoff))).length = W.rows.flatten.length :=
    hprocessed.trans htotal.symm
  have hall : ∀ z ∈ W.rows.flatten, z < cutoff := by
    simpa only [decide_eq_true_eq] using List.length_filter_eq_length_iff.mp hfilter
  have hrow (r : ℕ) : (W.rows.getD r []).length = s.shape.rowLen r := by
    rw [← W.counts r]
    symm
    apply List.countP_eq_length.mpr
    intro z hz
    simpa only [decide_eq_true_eq] using hall z (List.mem_flatten_of_mem_getD hz)
  intro k
  simpa only [stackRowPrefix, hrow] using W.dominance k

end GreedyRowsInvariant

theorem initial_visit_le {n : ℕ} (z : VisitTime (n + 1)) :
    visitTime 0 (0 : Fin (n + 1)) ≤ z := by
  apply le_of_not_gt
  intro h
  change toLex (ofLex z) < toLex (0, (0 : Fin (n + 1))) at h
  rcases Prod.Lex.toLex_lt_toLex.mp h with hp | ⟨hp, hi⟩
  · omega
  · exact (not_lt_of_ge (Fin.zero_le _)) hi

def ScheduledFilling.initialGreedyRows {n : ℕ} {a : Fin (n + 1) → ℕ}
    (F : ScheduledFilling a) :
    GreedyRowsInvariant a F.shape (labeledInitial (n + 1)) (visitTime 0 0) where
  rows := F.rows
  valid := F.rows_valid
  content := F.rows_tokens_perm
  processed := by
    have hf : F.rows.flatten.filter (fun z => decide (z < visitTime 0 0)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      simpa only [decide_eq_true_eq] using not_lt.mpr (initial_visit_le z)
    simp only [processedPositions, hf, List.map_nil, acceptedPositions,
      labeledInitial, List.Perm.refl]
  counts := by
    intro r
    have hz := scheduleCountLT_eq_zero_of_forall (F.rows.getD r []) (visitTime 0 0)
      (fun z _ => initial_visit_le z)
    simpa only [labeledInitial, YoungDiagram.rowLen_bot] using hz
  dominance := by
    intro k
    simp only [stackRowPrefix, F.rows_row_length]
    exact le_rfl

end HigherSpecht
end
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/HanadaClosedInvariant.lean -/



/-!
# Closing one actual visit and reopening at the next queued visit

Immediately after a step, processed entries are those at most the old visit.
The cyclic queue window proves that there is no unprocessed comparison entry
strictly before the new queue front. This transfers the closed invariant to
the open invariant used for the next actual step, including sparse queues.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def closedProcessedPositions {n : ℕ} (rows : List (List (VisitTime n)))
    (cutoff : VisitTime n) : List (Fin n) :=
  (rows.flatten.filter (fun z => decide (z ≤ cutoff))).map (fun z => (ofLex z).2)

structure ClosedGreedyRowsInvariant {n : ℕ} (a : Fin n → ℕ)
    (initialShape : YoungDiagram) (s : LabeledCatState n) (cutoff : VisitTime n) where
  rows : List (List (VisitTime n))
  valid : ScheduleRowsValid (visitHeight a) 0 rows
  content : (rows.flatten.map (fun z => (ofLex z).2)).Perm (List.finRange n)
  processed : (closedProcessedPositions rows cutoff).Perm (acceptedPositions s)
  counts : ∀ r, scheduleCountLE (rows.getD r []) cutoff = s.shape.rowLen r
  dominance : ∀ k, (∑ r ∈ Finset.range k, initialShape.rowLen r) ≤ stackRowPrefix rows k

theorem mem_filtered_tokenPositions_iff {n : ℕ} {entries : List (VisitTime n)}
    (hn : (entries.map (fun z => (ofLex z).2)).Nodup)
    (p : VisitTime n → Bool) {z : VisitTime n} (hz : z ∈ entries) :
    (ofLex z).2 ∈ (entries.filter p).map (fun w => (ofLex w).2) ↔ p z := by
  constructor
  · intro hm
    obtain ⟨w, hw, hid⟩ := List.mem_map.mp hm
    have hweq : w = z := List.inj_on_of_nodup_map hn (List.mem_filter.mp hw).1 hz hid
    simpa only [hweq] using (List.mem_filter.mp hw).2
  · intro hp
    exact List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨hz, hp⟩, rfl⟩

namespace ClosedGreedyRowsInvariant

variable {n : ℕ} {a : Fin n → ℕ} {initialShape : YoungDiagram}
  {s : LabeledCatState n} {cutoff : VisitTime n}

theorem tokens_nodup (W : ClosedGreedyRowsInvariant a initialShape s cutoff) :
    (W.rows.flatten.map (fun z => (ofLex z).2)).Nodup :=
  W.content.symm.nodup (List.nodup_finRange n)

theorem accepted_iff (W : ClosedGreedyRowsInvariant a initialShape s cutoff)
    {z : VisitTime n} (hz : z ∈ W.rows.flatten) :
    (ofLex z).2 ∈ acceptedPositions s ↔ z ≤ cutoff := by
  rw [← W.processed.mem_iff]
  exact (mem_filtered_tokenPositions_iff W.tokens_nodup
    (fun z => decide (z ≤ cutoff)) hz).trans (by simp)

theorem pending_of_gt (W : ClosedGreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) {z : VisitTime n} (hz : z ∈ W.rows.flatten)
    (hzt : cutoff < z) : ∃ u ∈ s.pending, (ofLex z).2 = u.position := by
  have hp : (acceptedPositions s ++ s.pending.map CyclingToken.position).Perm
      (List.finRange n) := by
    simpa only [acceptedPositions, List.map_map, Function.comp_def,
      initialCyclingQueue_positions] using hs.execution.positions
  have hm : (ofLex z).2 ∈ acceptedPositions s ++ s.pending.map CyclingToken.position :=
    hp.mem_iff.mpr (by simp)
  rcases List.mem_append.mp hm with hm | hm
  · exact False.elim ((not_le_of_gt hzt) ((W.accepted_iff hz).mp hm))
  · obtain ⟨u, hu, hid⟩ := List.mem_map.mp hm
    exact ⟨u, hu, hid.symm⟩

/-- The actual one-window queue arithmetic identifies the next open cutoff;
no dense scan or extra comparison hypothesis is introduced. -/
def reopen (W : ClosedGreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) {t u : CyclingToken n}
    {oldTail newTail : List (CyclingToken n)}
    (hcutoff : cutoff = visitTime t.round t.position)
    (hold : CyclingQueueValid (t :: oldTail))
    (hsubset : s.pending ⊆ oldTail ++ [t.bump])
    (hhead : s.pending = u :: newTail) :
    GreedyRowsInvariant a initialShape s (visitTime u.round u.position) := by
  have hu : u ∈ oldTail ++ [t.bump] := hsubset (by rw [hhead]; simp)
  have hnext : cutoff < visitTime u.round u.position := by
    rw [hcutoff]
    rcases List.mem_append.mp hu with hu | hu
    · have hstamp := (List.pairwise_cons.mp hold.1).1 u hu
      exact visitStamp_strictMono.lt_iff_lt.mp hstamp
    · have heq : u = t.bump := List.mem_singleton.mp hu
      subst u
      exact lt_advanceVisit (visitTime t.round t.position)
  have hnewQueue := (hs.execution.ordering (initialCyclingQueue_valid n)).1
  rw [hhead] at hnewQueue
  have hfront (v : CyclingToken n) (hv : v ∈ s.pending) :
      visitTime u.round u.position ≤ visitTime v.round v.position := by
    rw [hhead] at hv
    rcases List.mem_cons.mp hv with heq | hv
    · subst v
      exact le_rfl
    · exact (cyclingQueue_tail_front_lt hnewQueue hv).le
  have hiff (z : VisitTime n) (hz : z ∈ W.rows.flatten) :
      z < visitTime u.round u.position ↔ z ≤ cutoff := by
    constructor
    · intro hznext
      by_contra hn
      have hzt : cutoff < z := lt_of_not_ge hn
      obtain ⟨v, hv, hid⟩ := W.pending_of_gt hs hz hzt
      have hvz := cyclingQueue_reject_visit_le_of_after_front hold (hsubset hv) hid
        (by simpa only [hcutoff] using hzt)
      exact (not_le_of_gt hznext) ((hfront v hv).trans hvz)
    · intro hzt
      exact hzt.trans_lt hnext
  have hfilter (row : List (VisitTime n)) (hrow : ∀ z ∈ row, z ∈ W.rows.flatten) :
      row.filter (fun z => decide (z < visitTime u.round u.position)) =
        row.filter (fun z => decide (z ≤ cutoff)) := by
    apply List.filter_congr
    intro z hz
    exact decide_eq_decide.mpr (hiff z (hrow z hz))
  refine ⟨W.rows, W.valid, W.content, ?_, ?_, W.dominance⟩
  · simpa only [processedPositions, closedProcessedPositions,
      hfilter W.rows.flatten (fun _ h => h)] using W.processed
  · intro r
    have hf := hfilter (W.rows.getD r []) (fun _ hz => List.mem_flatten_of_mem_getD hz)
    simpa only [scheduleCountLT, scheduleCountLE, List.countP_eq_length_filter, hf] using W.counts r

theorem terminal_dominates (W : ClosedGreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) (hnil : s.pending = []) : Dominates s.shape initialShape := by
  have ha : (acceptedPositions s).Perm (List.finRange n) := by
    simpa only [acceptedPositions, List.map_map, Function.comp_def] using hs.complete_positions hnil
  have hprocessed := (W.processed.trans ha).length_eq
  have htotal := W.content.length_eq
  simp only [closedProcessedPositions, List.length_map, List.length_finRange] at hprocessed htotal
  have hfilter :
      (W.rows.flatten.filter (fun z => decide (z ≤ cutoff))).length = W.rows.flatten.length :=
    hprocessed.trans htotal.symm
  have hall : ∀ z ∈ W.rows.flatten, z ≤ cutoff := by
    simpa only [decide_eq_true_eq] using List.length_filter_eq_length_iff.mp hfilter
  have hrow (r : ℕ) : (W.rows.getD r []).length = s.shape.rowLen r := by
    rw [← W.counts r]
    symm
    apply List.countP_eq_length.mpr
    intro z hz
    simpa only [decide_eq_true_eq] using hall z (List.mem_flatten_of_mem_getD hz)
  intro k
  simpa only [stackRowPrefix, hrow] using W.dominance k

end ClosedGreedyRowsInvariant

theorem filter_le_eq_filter_lt_of_not_mem {α : Type*} [LinearOrder α]
    (row : List α) (cutoff : α) (hnot : cutoff ∉ row) :
    row.filter (fun z => decide (z ≤ cutoff)) = row.filter (fun z => decide (z < cutoff)) := by
  apply List.filter_congr
  intro z hz
  have hne : z ≠ cutoff := fun heq => hnot (heq ▸ hz)
  exact decide_eq_decide.mpr ⟨fun h => lt_of_le_of_ne h hne, fun h => h.le⟩

def GreedyRowsInvariant.close_rejected {n : ℕ} {a : Fin n → ℕ}
    {initialShape : YoungDiagram} {s : LabeledCatState n} {cutoff : VisitTime n}
    (W : GreedyRowsInvariant a initialShape s cutoff)
    {t : CyclingToken n} {q : List (CyclingToken n)}
    (hhead : s.pending = t :: q) (hcutoff : cutoff = visitTime t.round t.position)
    (hblocked : ¬ YoungDiagram.IsAddable s.shape
      (tokenValue a t, s.shape.rowLen (tokenValue a t))) :
    ClosedGreedyRowsInvariant a initialShape (labeledCatStep a s) cutoff := by
  have hnot := W.current_absent_of_blocked hcutoff hblocked
  have hshape : (labeledCatStep a s).shape = s.shape := by
    simp only [labeledCatStep, hhead, if_neg hblocked]
  have haccepted : (labeledCatStep a s).accepted = s.accepted := by
    simp only [labeledCatStep, hhead, if_neg hblocked]
  refine ⟨W.rows, W.valid, W.content, ?_, ?_, W.dominance⟩
  · simpa only [closedProcessedPositions, processedPositions, acceptedPositions,
      filter_le_eq_filter_lt_of_not_mem W.rows.flatten cutoff hnot, haccepted] using W.processed
  · intro r
    have hnotr : cutoff ∉ W.rows.getD r [] :=
      fun hm => hnot (List.mem_flatten_of_mem_getD hm)
    have hf := filter_le_eq_filter_lt_of_not_mem (W.rows.getD r []) cutoff hnotr
    simpa only [scheduleCountLT, scheduleCountLE, List.countP_eq_length_filter, hf,
      hshape] using W.counts r

end HigherSpecht
end
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/HanadaVisitUpdate.lean -/



/-!
# The exact acceptance interface for the greedy-row invariant

`GreedyVisitUpdate` records the concrete effects that the literal column
exchange and bump routes must establish. It is an intermediate certificate,
not a premise of a principal count or basis claim. The acceptance wrapper
below derives the new processed IDs from token uniqueness and the precise
row-count change, so a mere count cannot replace the actual token content.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

structure GreedyVisitUpdate {n : ℕ} (a : Fin n → ℕ)
    (oldRows : List (List (VisitTime n))) (cutoff : VisitTime n) (targetRow : ℕ) where
  result : List (List (VisitTime n))
  valid : ScheduleRowsValid (visitHeight a) 0 result
  content : (result.flatten.map (fun z => (ofLex z).2)).Perm
    (oldRows.flatten.map (fun z => (ofLex z).2))
  before : ∀ j,
    (result.getD j []).filter (fun z => decide (z < cutoff)) =
      (oldRows.getD j []).filter (fun z => decide (z < cutoff))
  processed : ∀ j, scheduleCountLE (result.getD j []) cutoff =
    scheduleCountLT (oldRows.getD j []) cutoff + if j = targetRow then 1 else 0
  dominance : ∀ k, stackRowPrefix oldRows k ≤ stackRowPrefix result k

theorem flatten_filter_eq_of_row_filters_eq {α : Type*}
    (p : α → Bool) (first second : List (List α))
    (h : ∀ j, (first.getD j []).filter p = (second.getD j []).filter p) :
    first.flatten.filter p = second.flatten.filter p := by
  induction first generalizing second with
  | nil =>
      symm
      apply List.filter_eq_nil_iff.mpr
      intro z hz hp
      obtain ⟨row, hrow, hzrow⟩ := List.mem_flatten.mp hz
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hrow
      have hf := h j
      rw [List.getD_eq_getElem _ _ hj, hjeq] at hf
      have hm : z ∈ row.filter p := List.mem_filter.mpr ⟨hzrow, hp⟩
      simpa only [List.getD_nil, List.filter_nil, ← hf, List.not_mem_nil] using hm
  | cons row rows ih =>
      cases second with
      | nil =>
          apply List.filter_eq_nil_iff.mpr
          intro z hz hp
          obtain ⟨r, hr, hzr⟩ := List.mem_flatten.mp hz
          obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hr
          have hf := h j
          rw [List.getD_eq_getElem _ _ hj, hjeq] at hf
          have hm : z ∈ r.filter p := List.mem_filter.mpr ⟨hzr, hp⟩
          simpa only [List.getD_nil, List.filter_nil, hf, List.not_mem_nil] using hm
      | cons other others =>
          simp only [List.flatten_cons, List.filter_append]
          have hfirst := h 0
          have htail (j : ℕ) := h (j + 1)
          rw [show row.filter p = other.filter p from hfirst,
            ih others (fun j => htail j)]

theorem filter_le_perm_cons_filter_lt {α : Type*} [LinearOrder α]
    (entries : List α) (cutoff : α) (hn : entries.Nodup) (hm : cutoff ∈ entries) :
    (entries.filter (fun z => decide (z ≤ cutoff))).Perm
      (cutoff :: entries.filter (fun z => decide (z < cutoff))) := by
  have hp := (List.perm_cons_erase hm).filter (fun z => decide (z ≤ cutoff))
  have htail : (entries.erase cutoff).filter (fun z => decide (z ≤ cutoff)) =
      entries.filter (fun z => decide (z < cutoff)) := by
    rw [filter_le_eq_filter_lt_of_not_mem _ cutoff hn.not_mem_erase,
      ← List.erase_filter]
    apply List.erase_eq_self_iff.mpr
    simp
  simpa only [List.filter_cons, le_refl, decide_true, Bool.coe_true, if_true,
    htail] using hp

theorem scheduleCountLE_eq_countLT_add_mem {α : Type*} [LinearOrder α]
    (entries : List α) (cutoff : α) (hn : entries.Nodup) :
    scheduleCountLE entries cutoff =
      scheduleCountLT entries cutoff + if cutoff ∈ entries then 1 else 0 := by
  by_cases hm : cutoff ∈ entries
  · have h := (filter_le_perm_cons_filter_lt entries cutoff hn hm).length_eq
    simpa only [scheduleCountLE, scheduleCountLT, List.countP_eq_length_filter,
      List.length_cons, if_pos hm] using h
  · simp only [scheduleCountLE, scheduleCountLT, List.countP_eq_length_filter,
      filter_le_eq_filter_lt_of_not_mem entries cutoff hm, if_neg hm, Nat.add_zero]

theorem nodup_getD_of_nodup_flatten {α : Type*} {rows : List (List α)}
    (hn : rows.flatten.Nodup) (j : ℕ) : (rows.getD j []).Nodup := by
  by_cases hj : j < rows.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hn.sublist (List.sublist_flatten_of_mem (List.getElem_mem hj))
  · simp [List.getD_eq_default, Nat.le_of_not_gt hj]

namespace GreedyVisitUpdate

variable {n : ℕ} {a : Fin n → ℕ} {oldRows : List (List (VisitTime n))}
  {cutoff : VisitTime n} {targetRow : ℕ}

/-- If the current token already has its current visit in the comparison
stack, acceptance changes only the processed cutoff; the rows stay literal. -/
def of_current_mem
    (hvalid : ScheduleRowsValid (visitHeight a) 0 oldRows)
    (hnodup : oldRows.flatten.Nodup) (hm : cutoff ∈ oldRows.flatten)
    (hheight : visitHeight a cutoff = targetRow) :
    GreedyVisitUpdate a oldRows cutoff targetRow where
  result := oldRows
  valid := hvalid
  content := List.Perm.refl _
  before := fun _ => rfl
  processed := by
    intro j
    rw [scheduleCountLE_eq_countLT_add_mem _ _ (nodup_getD_of_nodup_flatten hnodup j)]
    have hiff : cutoff ∈ oldRows.getD j [] ↔ j = targetRow := by
      constructor
      · intro hj
        have h := hvalid.getD_height j cutoff hj
        simpa only [Nat.zero_add, hheight] using h.symm
      · intro hj
        subst j
        exact hvalid.mem_getD_of_height hm (by simpa using hheight)
    simp only [hiff]
  dominance := fun _ => le_rfl

theorem current_mem (U : GreedyVisitUpdate a oldRows cutoff targetRow) :
    cutoff ∈ U.result.flatten := by
  have hlt : scheduleCountLT (U.result.getD targetRow []) cutoff =
      scheduleCountLT (oldRows.getD targetRow []) cutoff := by
    simp only [scheduleCountLT, List.countP_eq_length_filter, U.before targetRow]
  have hle := U.processed targetRow
  simp only [if_pos rfl, if_true] at hle
  by_contra hn
  have hnrow : cutoff ∉ U.result.getD targetRow [] :=
    fun h => hn (List.mem_flatten_of_mem_getD h)
  have hf := filter_le_eq_filter_lt_of_not_mem (U.result.getD targetRow []) cutoff hnrow
  have heq : scheduleCountLE (U.result.getD targetRow []) cutoff =
      scheduleCountLT (U.result.getD targetRow []) cutoff := by
    simp only [scheduleCountLE, scheduleCountLT, List.countP_eq_length_filter, hf]
  omega

theorem before_flatten (U : GreedyVisitUpdate a oldRows cutoff targetRow) :
    U.result.flatten.filter (fun z => decide (z < cutoff)) =
      oldRows.flatten.filter (fun z => decide (z < cutoff)) :=
  flatten_filter_eq_of_row_filters_eq _ _ _ U.before

end GreedyVisitUpdate

def GreedyRowsInvariant.close_accepted {n : ℕ} {a : Fin n → ℕ}
    {initialShape : YoungDiagram} {s : LabeledCatState n} {cutoff : VisitTime n}
    (W : GreedyRowsInvariant a initialShape s cutoff)
    {t : CyclingToken n} {q : List (CyclingToken n)}
    (hhead : s.pending = t :: q) (hcutoff : cutoff = visitTime t.round t.position)
    (hadd : YoungDiagram.IsAddable s.shape
      (tokenValue a t, s.shape.rowLen (tokenValue a t)))
    (U : GreedyVisitUpdate a W.rows cutoff (tokenValue a t)) :
    ClosedGreedyRowsInvariant a initialShape (labeledCatStep a s) cutoff := by
  have hcontent := U.content.trans W.content
  have hnodup : U.result.flatten.Nodup :=
    List.Nodup.of_map (fun z => (ofLex z).2)
      (hcontent.symm.nodup (List.nodup_finRange n))
  have hprocessed : (closedProcessedPositions U.result cutoff).Perm
      (acceptedPositions s ++ [t.position]) := by
    have hp := (filter_le_perm_cons_filter_lt U.result.flatten cutoff hnodup U.current_mem).map
      (fun z => (ofLex z).2)
    rw [U.before_flatten] at hp
    have hp' : (closedProcessedPositions U.result cutoff).Perm
        (t.position :: processedPositions W.rows cutoff) := by
      simpa only [closedProcessedPositions, processedPositions,
        List.map_cons, hcutoff, visitTime, ofLex_toLex] using hp
    exact hp'.trans ((W.processed.cons t.position).trans
      (List.perm_append_singleton t.position (acceptedPositions s)).symm)
  have haccepted : acceptedPositions (labeledCatStep a s) =
      acceptedPositions s ++ [t.position] := by
    simp only [labeledCatStep, hhead, if_pos hadd, acceptedPositions,
      List.map_append, List.map_cons, List.map_nil]
  refine ⟨U.result, U.valid, hcontent, ?_, ?_, ?_⟩
  · rw [haccepted]
    exact hprocessed
  · intro j
    rw [U.processed j, W.counts j]
    simp only [labeledCatStep, hhead, if_pos hadd]
    rw [hadd.rowLen_addCell]
    by_cases hj : j = tokenValue a t
    · simp [hj]
    · simp [hj, Ne.symm hj]
  · intro k
    exact (W.dominance k).trans (U.dominance k)

end HigherSpecht
end
end CanonicalSource9

section CanonicalSource10
/- Source: HigherSpecht/HanadaBoundedExchange.lean -/



/-!
# The actual column exchange above a lower row

The shifted inputs, the deletion deficit, the first absorbing frontier, and
every later bump route are constructed from the given finite rows.  The
capacity premise is the literal free space below the current visit; the
greedy acceptance wrapper obtains it from Young-diagram addability.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

structure BoundedColumnUpdate {n : ℕ} (a : Fin n → ℕ) (r : ℕ)
    (lower : List (VisitTime n)) (oldRows : List (List (VisitTime n)))
    (cutoff : VisitTime n) where
  result : List (List (VisitTime n))
  valid : ScheduleRowsValid (visitHeight a) r result
  fits : RowsFit lower (result.headD [])
  content : (result.flatten.map (fun z => (ofLex z).2)).Perm
    (oldRows.flatten.map (fun z => (ofLex z).2))
  before : ∀ j,
    (result.getD j []).filter (fun z => decide (z < cutoff)) =
      (oldRows.getD j []).filter (fun z => decide (z < cutoff))
  processed : ∀ j, scheduleCountLE (result.getD j []) cutoff =
    scheduleCountLT (oldRows.getD j []) cutoff + if j = 0 then 1 else 0
  dominance : ∀ k, stackRowPrefix oldRows k ≤ stackRowPrefix result k

theorem boundedVisitUpdate_of_later_column_nonempty {n : ℕ} {a : Fin n → ℕ}
    {r : ℕ} {rows : List (List (VisitTime n))} {lower : List (VisitTime n)}
    (hrows : ScheduleRowsValid (visitHeight a) r rows)
    (hn : rows.flatten.Nodup) (hlower : lower.Pairwise (· ≤ ·))
    (hfit : RowsFit lower (rows.headD []))
    (d c p : ℕ) (i : Fin n) (hd : 0 < d)
    (habsent : visitTime p i ∉ rows.flatten)
    (hcapacity : scheduleCountLT (rows.headD []) (visitTime p i) <
      scheduleCountLT lower (visitTime p i))
    (hlocated : (rows.getD d [])[c]? = some (visitTime (p + d) i))
    (hheight : r = a i + p) :
    Nonempty (BoundedColumnUpdate a r lower rows (visitTime p i)) := by
  let erased := eraseColumnAbove c d rows
  have herased : ScheduleRowsValid (visitHeight a) r erased := hrows.eraseColumnAbove c d
  have hhead : erased.headD [] = rows.headD [] := by
    change (eraseColumnAbove c d rows).headD [] = rows.headD []
    simp only [List.headD_eq_getD, eraseColumnAbove_getD,
      if_neg (by omega : ¬ d ≤ 0)]
  have hfitErased : RowsFit lower (erased.headD []) := by rw [hhead]; exact hfit
  obtain ⟨tail, hinputs, hgraded, hremoved, hvisits⟩ :=
    shiftedColumn_inputs hrows d c p i hlocated hheight
  have hremovedStrict := shiftedColumn_removed_later hrows d c p i hd hlocated hheight
  obtain ⟨firstResult, firstEndpoint, first, hfirstBound⟩ :=
    firstRoute_from_actual_column hrows hfit d c p i hlocated
      (nodup_getD_of_nodup_flatten hn d)
  obtain ⟨result, endpoints, hrun, hbound⟩ :=
    ConsecutiveBumpRoutes.exists_of_first_route advanceVisit_strictMono lt_advanceVisit
      (visitHeight_advanceVisit a) first herased hgraded
  have hbound' : ∀ e ∈ endpoints, e ≤ d := fun e he => (hbound e he).trans hfirstBound
  have hlater : ∀ y ∈ tail, visitTime p i < y := by
    cases hgraded with
    | cons hh hincr ht => exact hincr
  have hnothead : visitTime p i ∉ erased.headD [] := by
    rw [hhead, List.headD_eq_getD]
    exact fun hm => habsent (List.mem_flatten_of_mem_getD hm)
  have hpop : ∀ z,
      (scheduleRowInsert lower (erased.headD []) (visitTime p i)).2 = some z →
        visitTime p i < z := by
    apply scheduleRowInsert_pop_gt_of_capacity lower (erased.headD []) (visitTime p i)
      hlower herased.head_sorted hfitErased hnothead
    simpa only [hhead] using hcapacity
  refine ⟨⟨result, hrun.valid (visitHeight_advanceVisit a) herased hgraded,
    hrun.lower_fits hfitErased, ?_, ?_, ?_, ?_⟩⟩
  · let position : VisitTime n → Fin n := fun z => (ofLex z).2
    have hpositions : (visitTime p i :: tail).map position =
        (deletedColumnAbove rows d c).map position := by
      rw [← hinputs, List.map_map]
      rfl
    have hrunContent := ConsecutiveBumpRoutes.label_content
      (advance := advanceVisit) position (fun _ => rfl) hrun
    have hdeleteContent := (deletedColumnAbove_conservation rows d c).map position
    apply hrunContent.symm.trans
    simpa only [List.map_append, hpositions] using hdeleteContent
  · intro j
    have hrunBefore := hrun.processed_filters_of_le lt_advanceVisit (visitHeight_advanceVisit a)
      herased hgraded (visitTime p i) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact le_rfl
        · exact (hlater z hz).le) j
    exact hrunBefore.trans (eraseColumnAbove_processed_filters rows d c (visitTime p i)
      (fun z hz => (hremovedStrict z hz).le) j)
  · intro j
    rw [hrun.processed_counts_current lt_advanceVisit hlater hpop j]
    rw [eraseColumnAbove_processed_counts rows d c (visitTime p i) hremovedStrict j]
    rw [scheduleCountLE_eq_LT_of_not_mem (rows.getD j []) (visitTime p i)
      (fun hm => habsent (List.mem_flatten_of_mem_getD hm))]
  · apply hrun.dominates_before_column_deletion d hbound'
    intro R
    have heq := hrows.stackRowPrefix_eraseColumnAbove c d R
    have hlength : (visitTime p i :: tail).length = (deletedColumnAbove rows d c).length := by
      rw [← hinputs, List.length_map]
    simpa only [hlength] using heq

def boundedVisitUpdate_of_later_column {n : ℕ} {a : Fin n → ℕ}
    {r : ℕ} {rows : List (List (VisitTime n))} {lower : List (VisitTime n)}
    (hrows : ScheduleRowsValid (visitHeight a) r rows)
    (hn : rows.flatten.Nodup) (hlower : lower.Pairwise (· ≤ ·))
    (hfit : RowsFit lower (rows.headD []))
    (d c p : ℕ) (i : Fin n) (hd : 0 < d)
    (habsent : visitTime p i ∉ rows.flatten)
    (hcapacity : scheduleCountLT (rows.headD []) (visitTime p i) <
      scheduleCountLT lower (visitTime p i))
    (hlocated : (rows.getD d [])[c]? = some (visitTime (p + d) i))
    (hheight : r = a i + p) :
    BoundedColumnUpdate a r lower rows (visitTime p i) :=
  Classical.choice (boundedVisitUpdate_of_later_column_nonempty hrows hn hlower hfit
    d c p i hd habsent hcapacity hlocated hheight)

end HigherSpecht
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/HanadaExchangeReattach.lean -/



/-!
# Reattaching the unchanged rows below an actual exchange

The bounded exchange operates on the suffix starting at the current row.
These finite-list identities restore the unchanged pre and transport all
of its literal token, visit-filter, count, and dominance conclusions.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem getD_drop_add (rows : List (List α)) (r j : ℕ) :
    (rows.drop r).getD j [] = rows.getD (r + j) [] := by
  induction r generalizing rows with
  | zero => simp
  | succ r ih =>
      cases rows <;> simp [List.drop_succ_cons, Nat.succ_add, ih]

theorem getD_take_append (rows result : List (List α)) (r j : ℕ)
    (hr : r ≤ rows.length) :
    (rows.take r ++ result).getD j [] =
      if j < r then rows.getD j [] else result.getD (j - r) [] := by
  induction r generalizing rows j with
  | zero => simp
  | succ r ih =>
      cases rows with
      | nil => simp at hr
      | cons row tail =>
          cases j with
          | zero => simp
          | succ j =>
              simpa only [List.take_succ_cons, List.cons_append, List.getD_cons_succ,
                Nat.succ_lt_succ_iff, Nat.add_sub_add_right] using
                ih tail j (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hr)

theorem headD_take_append (rows result : List (List α)) (r : ℕ)
    (hr : 0 < r) (hlen : r ≤ rows.length) :
    (rows.take r ++ result).headD [] = rows.headD [] := by
  simpa only [List.headD_eq_getD, getD_take_append rows result r 0 hlen, if_pos hr]

theorem stackRowPrefix_append (pre suffix : List (List α)) (R : ℕ) :
    stackRowPrefix (pre ++ suffix) R =
      stackRowPrefix pre R + stackRowPrefix suffix (R - pre.length) := by
  induction pre generalizing R with
  | nil => simp
  | cons row pre ih =>
      cases R with
      | zero => simp
      | succ R =>
          simp only [List.cons_append, stackRowPrefix_cons_succ, List.length_cons,
            Nat.add_sub_add_right, ih]
          omega

theorem ScheduleRowsValid.replace_drop {height : α → ℕ} {start : ℕ}
    {rows result : List (List α)} (h : ScheduleRowsValid height start rows)
    (r : ℕ) (hr : r ≤ rows.length)
    (hnew : ScheduleRowsValid height (start + r) result)
    (hlink : r = 0 ∨ RowsFit (rows.getD (r - 1) []) (result.headD [])) :
    ScheduleRowsValid height start (rows.take r ++ result) := by
  induction r generalizing start rows with
  | zero => simpa using hnew
  | succ r ih =>
      cases h with
      | nil => simp at hr
      | @cons start row tail hs hh hc ht =>
          have hrt : r ≤ tail.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hr
          have hlink' : RowsFit ((row :: tail).getD r []) (result.headD []) := by
            simpa only [Nat.succ_sub_one] using hlink.resolve_left (by omega)
          cases r with
          | zero => exact .cons hs hh hlink' hnew
          | succ r =>
              have hnew' : ScheduleRowsValid height ((start + 1) + (r + 1)) result := by
                simpa only [Nat.add_assoc, Nat.add_comm 1 (r + 1)] using hnew
              have htail := ih ht hrt hnew' (Or.inr (by
                simpa only [List.getD_cons_succ, Nat.succ_sub_one] using hlink'))
              refine .cons hs hh ?_ htail
              exact (congrArg (RowsFit row)
                (headD_take_append tail result (r + 1) (by omega) hrt)).mpr hc

def BoundedColumnUpdate.reattach {n : ℕ} {a : Fin n → ℕ}
    {rows : List (List (VisitTime n))} {r : ℕ} {cutoff : VisitTime n}
    (hrows : ScheduleRowsValid (visitHeight a) 0 rows)
    (hr : 0 < r) (hlen : r ≤ rows.length) (habsent : cutoff ∉ rows.flatten)
    (U : BoundedColumnUpdate a r (rows.getD (r - 1) []) (rows.drop r) cutoff) :
    GreedyVisitUpdate a rows cutoff r := by
  refine ⟨rows.take r ++ U.result,
    hrows.replace_drop r hlen (by simpa only [Nat.zero_add] using U.valid) (Or.inr U.fits),
    ?_, ?_, ?_, ?_⟩
  · have h := U.content.append_left ((rows.take r).flatten.map (fun z => (ofLex z).2))
    simpa only [← List.map_append, ← List.flatten_append, List.take_append_drop] using h
  · intro j
    rw [getD_take_append rows U.result r j hlen]
    by_cases hj : j < r
    · simp only [if_pos hj]
    · simp only [if_neg hj]
      rw [U.before (j - r), getD_drop_add, Nat.add_sub_of_le (Nat.le_of_not_gt hj)]
  · intro j
    rw [getD_take_append rows U.result r j hlen]
    by_cases hj : j < r
    · simp only [if_pos hj, if_neg (ne_of_lt hj)]
      exact scheduleCountLE_eq_LT_of_not_mem (rows.getD j []) cutoff
        (fun hm => habsent (List.mem_flatten_of_mem_getD hm))
    · simp only [if_neg hj]
      rw [U.processed (j - r), getD_drop_add,
        Nat.add_sub_of_le (Nat.le_of_not_gt hj)]
      have heq : j - r = 0 ↔ j = r := by omega
      simp only [heq]
  · intro R
    have hlength : (rows.take r).length = r := by simp [List.length_take, Nat.min_eq_left hlen]
    have h := Nat.add_le_add_left (U.dominance (R - r)) (stackRowPrefix (rows.take r) R)
    have hleft := stackRowPrefix_append (rows.take r) (rows.drop r) R
    rw [List.take_append_drop, hlength] at hleft
    have hright := stackRowPrefix_append (rows.take r) U.result R
    rw [hlength] at hright
    rw [hleft, hright]
    exact h

end HigherSpecht
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/HanadaBottomExchange.lean -/



/-!
# The actual column exchange into row zero

The bottom row has no lower barrier. Its first insertion is ordinary sorted
insertion. Every remaining shifted column entry starts one row higher; the
adjacent-row absorption theorem constructs a first route with endpoint zero,
and the consecutive-route theorem keeps all subsequent relative endpoints
zero. Token content, processed prefixes, and all dominance inequalities are
derived from that execution and the literal column deletion.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem scheduleBottomInsert_filter_of_le (row : List α) (x cutoff : α)
    (hcx : cutoff ≤ x) :
    (scheduleBottomInsert row x).filter (fun z => decide (z < cutoff)) =
      row.filter (fun z => decide (z < cutoff)) := by
  induction row with
  | nil => simp [scheduleBottomInsert, not_lt.mpr hcx]
  | cons y row ih =>
      by_cases hxy : x ≤ y
      · simp only [scheduleBottomInsert,
          List.orderedInsert_cons_of_le (· ≤ ·) row hxy,
          List.filter_cons, not_lt.mpr hcx, decide_false, Bool.false_eq_true, if_false]
      · change (List.orderedInsert (· ≤ ·) x (y :: row)).filter _ = _
        rw [List.orderedInsert_of_not_le (· ≤ ·) row hxy]
        simpa only [List.filter_cons, scheduleBottomInsert] using
          congrArg (fun rest => if decide (y < cutoff) then y :: rest else rest) ih

theorem scheduleCountLE_bottomInsert_current (row : List α) (x : α) :
    scheduleCountLE (scheduleBottomInsert row x) x = scheduleCountLE row x + 1 := by
  have h := (scheduleBottomInsert_conservation row x).countP_eq
    (fun z => decide (z ≤ x))
  simpa [scheduleCountLE, List.countP_cons] using h

/-- The actual stack above a new bottom entry absorbs each successive
graded input in the row where that input starts. -/
theorem exists_bottom_tail_routes
    {advance : α → α} {height : α → ℕ}
    (hmono : StrictMono advance) (hadvance : ∀ z, z < advance z)
    (hheight : ∀ z, height (advance z) = height z + 1)
    {bottom : List α} {rows : List (List α)} {x : α} {inputs : List α}
    (hrows : ScheduleRowsValid height 0 (bottom :: rows))
    (hinputs : GradedIncreasingInputs height 0 (x :: inputs)) :
    ∃ result endpoints,
      ConsecutiveBumpRoutes advance (scheduleBottomInsert bottom x) rows inputs result endpoints ∧
        ∀ e ∈ endpoints, e ≤ 0 := by
  cases inputs with
  | nil => exact ⟨rows, [], .nil _ _, by simp⟩
  | cons y inputs =>
      have htailRows := hrows.tail_valid
      have hcolumns : RowsFit bottom (rows.headD []) := by
        cases hrows with
        | cons hs hh hc ht => exact hc
      have htailInputs : GradedIncreasingInputs height 1 (y :: inputs) := by
        cases hinputs with
        | cons hx hxy ht => exact ht
      have hxy : x < y := by
        cases hinputs with
        | cons hx hxy ht => exact hxy y (by simp)
      have hnone := scheduleBottomInsert_adjacent_none bottom (rows.headD []) x y
        hrows.head_sorted htailRows.head_sorted hcolumns hxy
      let next := (scheduleRowInsert (scheduleBottomInsert bottom x) (rows.headD []) y).1
      have hstep : scheduleRowInsert (scheduleBottomInsert bottom x) (rows.headD []) y =
          (next, none) := Prod.ext rfl hnone
      have first : ScheduleBumpRoute advance (scheduleBottomInsert bottom x) rows y
          (next :: rows.tail) 0 := by
        cases rows with
        | nil => exact .top _ _ _ hstep
        | cons upper tail => exact .stop _ _ _ _ _ hstep
      exact ConsecutiveBumpRoutes.exists_of_first_route hmono hadvance hheight
        first htailRows htailInputs

theorem nonempty_bottomVisitUpdate_of_later_column {n : ℕ} {a : Fin n → ℕ}
    {rows : List (List (VisitTime n))}
    (hrows : ScheduleRowsValid (visitHeight a) 0 rows)
    (hn : rows.flatten.Nodup) (d c p : ℕ) (i : Fin n) (hd : 0 < d)
    (habsent : visitTime p i ∉ rows.flatten)
    (hlocated : (rows.getD d [])[c]? = some (visitTime (p + d) i))
    (hheight : a i + p = 0) :
    Nonempty (GreedyVisitUpdate a rows (visitTime p i) 0) := by
  cases rows with
  | nil => simp at hlocated
  | cons bottom oldTail =>
      cases d with
      | zero => omega
      | succ d =>
          let erasedTail := eraseColumnAbove c d oldTail
          have herased : ScheduleRowsValid (visitHeight a) 0 (bottom :: erasedTail) :=
            hrows.eraseColumnAbove c (d + 1)
          have htailRows := herased.tail_valid
          obtain ⟨inputs, hinputs, hgraded, hremoved, hvisits⟩ :=
            shiftedColumn_inputs hrows (d + 1) c p i hlocated hheight.symm
          have hremovedStrict := shiftedColumn_removed_later hrows (d + 1) c p i
            (by omega) hlocated hheight.symm
          have hlater : ∀ y ∈ inputs, visitTime p i < y := by
            cases hgraded with
            | cons hx hxy ht => exact hxy
          have htailInputs : GradedIncreasingInputs (visitHeight a) 1 inputs := by
            cases hgraded with
            | cons hx hxy ht => exact ht
          obtain ⟨output, endpoints, hrun, hbound⟩ :=
            exists_bottom_tail_routes advanceVisit_strictMono lt_advanceVisit
              (visitHeight_advanceVisit a) herased hgraded
          let newBottom := scheduleBottomInsert bottom (visitTime p i)
          have hcolumns : RowsFit bottom (erasedTail.headD []) := by
            cases herased with
            | cons hs hh hc ht => exact hc
          have hvalid : ScheduleRowsValid (visitHeight a) 0 (newBottom :: output) := by
            refine .cons (scheduleBottomInsert_pairwise_le _ _ herased.head_sorted) ?_
              (hrun.lower_fits (scheduleBottomInsert_columns _ herased.head_sorted hcolumns))
              (hrun.valid (visitHeight_advanceVisit a) htailRows htailInputs)
            intro z hz
            have hz' : z ∈ visitTime p i :: bottom :=
              (scheduleBottomInsert_conservation bottom (visitTime p i)).mem_iff.mp hz
            rcases List.mem_cons.mp hz' with rfl | hz'
            · simpa only [visitHeight, visitTime, ofLex_toLex] using hheight
            · exact herased.head_height z hz'
          refine ⟨⟨newBottom :: output, hvalid, ?_, ?_, ?_, ?_⟩⟩
          · let position : VisitTime n → Fin n := fun z => (ofLex z).2
            have hpositions : (visitTime p i :: inputs).map position =
                (deletedColumnAbove (bottom :: oldTail) (d + 1) c).map position := by
              rw [← hinputs, List.map_map]
              rfl
            have hb := (scheduleBottomInsert_conservation bottom (visitTime p i)).map position
            have ht := ConsecutiveBumpRoutes.label_content
              (advance := advanceVisit) position (fun _ => rfl) hrun
            have hdel := (deletedColumnAbove_conservation (bottom :: oldTail) (d + 1) c).map position
            apply List.perm_iff_count.mpr
            intro z
            have hbz := hb.count_eq z
            have htz := ht.count_eq z
            have hdz := hdel.count_eq z
            have hiz := congrArg (fun l : List (Fin n) => l.count z) hpositions
            change ((newBottom :: output).flatten.map position).count z =
              ((bottom :: oldTail).flatten.map position).count z
            change ((deletedColumnAbove (bottom :: oldTail) (d + 1) c ++
              (bottom :: erasedTail).flatten).map position).count z =
              ((bottom :: oldTail).flatten.map position).count z at hdz
            simp only [List.map_cons, List.map_append, List.flatten_cons,
              List.count_append, List.count_cons] at hbz htz hdz hiz ⊢
            dsimp only [newBottom]
            omega
          · intro j
            cases j with
            | zero =>
                exact scheduleBottomInsert_filter_of_le bottom (visitTime p i) (visitTime p i) le_rfl
            | succ j =>
                have hfirst := hrun.processed_filters_of_le lt_advanceVisit
                  (visitHeight_advanceVisit a) htailRows htailInputs (visitTime p i)
                    (fun z hz => (hlater z hz).le) j
                have hsecond := eraseColumnAbove_processed_filters (bottom :: oldTail) (d + 1) c
                  (visitTime p i) (fun z hz => (hremovedStrict z hz).le) (j + 1)
                exact hfirst.trans hsecond
          · intro j
            cases j with
            | zero =>
                change scheduleCountLE newBottom (visitTime p i) =
                  scheduleCountLT bottom (visitTime p i) + 1
                rw [scheduleCountLE_bottomInsert_current,
                  scheduleCountLE_eq_LT_of_not_mem bottom (visitTime p i) (by
                    intro hm
                    exact habsent (List.mem_flatten.mpr ⟨bottom, by simp, hm⟩))]
            | succ j =>
                simp only [List.getD_cons_succ, Nat.succ_ne_zero, if_false, Nat.add_zero]
                rw [hrun.processed_counts_of_lt lt_advanceVisit (visitTime p i) hlater j]
                have hdel := eraseColumnAbove_processed_counts (bottom :: oldTail) (d + 1) c
                  (visitTime p i) hremovedStrict (j + 1)
                change scheduleCountLE (erasedTail.getD j []) (visitTime p i) =
                  scheduleCountLE (oldTail.getD j []) (visitTime p i) at hdel
                rw [hdel]
                exact scheduleCountLE_eq_LT_of_not_mem _ _ (fun hm =>
                  habsent (List.mem_flatten_of_mem_getD (i := j + 1) hm))
          · intro R
            cases R with
            | zero => simp
            | succ R =>
                have hdelete := hrows.stackRowPrefix_eraseColumnAbove c (d + 1) (R + 1)
                have hlength : (deletedColumnAbove (bottom :: oldTail) (d + 1) c).length =
                    inputs.length + 1 := by
                  have h := congrArg List.length hinputs
                  simpa only [List.length_map, List.length_cons] using h
                have hadded := routeEndpointsBelow_lowerBound endpoints 0 R hbound
                rw [Nat.sub_zero, hrun.length_endpoints] at hadded
                rw [hlength] at hdelete
                change stackRowPrefix (bottom :: oldTail) (R + 1) =
                  stackRowPrefix (bottom :: erasedTail) (R + 1) +
                    min (inputs.length + 1) (R + 1 - (d + 1)) at hdelete
                simp only [stackRowPrefix_cons_succ] at hdelete ⊢
                rw [hrun.row_prefix R]
                have hbottom : newBottom.length = bottom.length + 1 :=
                  scheduleBottomInsert_length bottom (visitTime p i)
                rw [hbottom]
                omega

/-- Data extracted only after the complete existence proposition has been proved. -/
def bottomVisitUpdate_of_later_column {n : ℕ} {a : Fin n → ℕ}
    {rows : List (List (VisitTime n))}
    (hrows : ScheduleRowsValid (visitHeight a) 0 rows)
    (hn : rows.flatten.Nodup) (d c p : ℕ) (i : Fin n) (hd : 0 < d)
    (habsent : visitTime p i ∉ rows.flatten)
    (hlocated : (rows.getD d [])[c]? = some (visitTime (p + d) i))
    (hheight : a i + p = 0) : GreedyVisitUpdate a rows (visitTime p i) 0 :=
  Classical.choice (nonempty_bottomVisitUpdate_of_later_column
    hrows hn d c p i hd habsent hlocated hheight)

end HigherSpecht
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/HanadaFullExchange.lean -/



/-!
# The complete acceptance exchange for the actual greedy state

The old visit and its column are recovered from the unique token occurrence
in the real comparison rows.  Addability supplies exactly the free strict
column capacity needed above row zero.  Every branch returns the concrete
update certificate proved by the literal operations; no exchange or
dominance hypothesis is added to the greedy-state interface.
-/

noncomputable section
open TauCeti
open scoped Classical

namespace HigherSpecht

theorem GreedyRowsInvariant.acceptance_update_nonempty {n : ℕ} {a : Fin n → ℕ}
    {initialShape : YoungDiagram} {s : LabeledCatState n} {cutoff : VisitTime n}
    (W : GreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) {t : CyclingToken n} {q : List (CyclingToken n)}
    (hhead : s.pending = t :: q) (hcutoff : cutoff = visitTime t.round t.position)
    (hadd : YoungDiagram.IsAddable s.shape
      (tokenValue a t, s.shape.rowLen (tokenValue a t))) :
    Nonempty (GreedyVisitUpdate a W.rows cutoff (tokenValue a t)) := by
  by_cases hmem : cutoff ∈ W.rows.flatten
  · exact ⟨GreedyVisitUpdate.of_current_mem W.valid W.entries_nodup hmem (by
      simp only [hcutoff, visitHeight, visitTime, ofLex_toLex, tokenValue])⟩
  · have ht : t ∈ s.pending := by rw [hhead]; exact List.mem_cons_self
    obtain ⟨oldRow, z, hz, hid, hge, hrowge⟩ := W.current_entry hs ht hcutoff
    let oldRound := (ofLex z).1
    let d := oldRound - t.round
    have hztime : z = visitTime oldRound t.position := by
      apply ofLex.injective
      exact Prod.ext rfl hid
    have hroundle : t.round ≤ oldRound := by
      rw [hcutoff, hztime] at hge
      exact visit_round_le_of_le hge
    have hround : t.round + d = oldRound := Nat.add_sub_of_le hroundle
    have hd : 0 < d := by
      by_contra h
      have heq : oldRound = t.round := by omega
      have hzt : z = cutoff := by rw [hztime, heq, hcutoff]
      apply hmem
      exact (congrArg (fun v => v ∈ W.rows.flatten) hzt).mp
        (List.mem_flatten_of_mem_getD hz)
    have holdheight := W.valid.getD_height oldRow z hz
    have holdrow : oldRow = tokenValue a t + d := by
      simp only [visitHeight, Nat.zero_add, hid] at holdheight
      dsimp only [tokenValue]
      change a t.position + oldRound = oldRow at holdheight
      omega
    obtain ⟨c, hc, hcz⟩ := List.mem_iff_getElem.mp hz
    have hlocated : (W.rows.getD (tokenValue a t + d) [])[c]? =
        some (visitTime (t.round + d) t.position) := by
      rw [← holdrow]
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨hc, ?_⟩
      rw [hcz, hztime, hround]
    have hlen : tokenValue a t ≤ W.rows.length := by
      have hne : W.rows.getD oldRow [] ≠ [] := by
        intro he
        exact List.not_mem_nil (he ▸ hz)
      have holdlen : oldRow < W.rows.length := by
        by_contra h
        exact hne (List.getD_eq_default W.rows [] (Nat.le_of_not_gt h))
      omega
    have hnotCurrent : visitTime t.round t.position ∉ W.rows.flatten := by
      simpa only [hcutoff] using hmem
    by_cases hrzero : tokenValue a t = 0
    · have hlocated0 : (W.rows.getD d [])[c]? =
          some (visitTime (t.round + d) t.position) := by
        simpa only [hrzero, Nat.zero_add] using hlocated
      have U := bottomVisitUpdate_of_later_column W.valid W.entries_nodup
        d c t.round t.position hd hnotCurrent hlocated0 (by simpa only [tokenValue] using hrzero)
      exact ⟨by simpa only [hcutoff, hrzero] using U⟩
    · have hrpos : 0 < tokenValue a t := Nat.pos_of_ne_zero hrzero
      let lower := W.rows.getD (tokenValue a t - 1) []
      let suffix := W.rows.drop (tokenValue a t)
      have hsuffix : ScheduleRowsValid (visitHeight a) (tokenValue a t) suffix := by
        simpa only [Nat.zero_add] using W.valid.drop (tokenValue a t)
      have hsuffixSub : List.Sublist suffix.flatten W.rows.flatten :=
        (List.drop_sublist (tokenValue a t) W.rows).flatten
      have hnsuffix : suffix.flatten.Nodup := W.entries_nodup.sublist hsuffixSub
      have habsentSuffix : visitTime t.round t.position ∉ suffix.flatten :=
        fun hm => hnotCurrent (hsuffixSub.mem hm)
      have hheadSuffix : suffix.headD [] = W.rows.getD (tokenValue a t) [] := by
        change (W.rows.drop (tokenValue a t)).headD [] = _
        rw [List.headD_eq_getD, getD_drop_add, Nat.add_zero]
      have hfit : RowsFit lower (suffix.headD []) := by
        rw [hheadSuffix]
        have h := W.valid.getD_columns (tokenValue a t - 1)
        simpa only [Nat.sub_add_cancel (Nat.one_le_of_lt hrpos)] using h
      have hstrict : s.shape.rowLen (tokenValue a t) <
          s.shape.rowLen (tokenValue a t - 1) := by
        have h := (isAddable_rowEnd_iff s.shape (tokenValue a t)).mp hadd
        exact h.resolve_left hrzero
      have hcapacity : scheduleCountLT (suffix.headD []) (visitTime t.round t.position) <
          scheduleCountLT lower (visitTime t.round t.position) := by
        rw [hheadSuffix]
        simpa only [lower, ← hcutoff, W.counts] using hstrict
      have hlocatedSuffix : (suffix.getD d [])[c]? =
          some (visitTime (t.round + d) t.position) := by
        simpa only [suffix, getD_drop_add] using hlocated
      let U := boundedVisitUpdate_of_later_column hsuffix hnsuffix
        (W.valid.getD_sorted (tokenValue a t - 1)) hfit d c t.round t.position hd
        habsentSuffix hcapacity hlocatedSuffix rfl
      have V := U.reattach W.valid hrpos hlen hnotCurrent
      exact ⟨by simpa only [hcutoff] using V⟩

def GreedyRowsInvariant.acceptance_update {n : ℕ} {a : Fin n → ℕ}
    {initialShape : YoungDiagram} {s : LabeledCatState n} {cutoff : VisitTime n}
    (W : GreedyRowsInvariant a initialShape s cutoff)
    (hs : LabeledInvariant a s) {t : CyclingToken n} {q : List (CyclingToken n)}
    (hhead : s.pending = t :: q) (hcutoff : cutoff = visitTime t.round t.position)
    (hadd : YoungDiagram.IsAddable s.shape
      (tokenValue a t, s.shape.rowLen (tokenValue a t))) :
    GreedyVisitUpdate a W.rows cutoff (tokenValue a t) :=
  Classical.choice (W.acceptance_update_nonempty hs hhead hcutoff hadd)

end HigherSpecht
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/HanadaShuffleExecution.lean -/



/-!
# The actual lazy execution of a shuffle of terminating words

Each original scan position has a color.  The global cyclic queue is shared,
but the decision to accept a token is made in its own color's Young diagram.
Each color projection consequently follows the original greedy algorithm.
Acceptance in a component is valid in the sum of the component row lengths.

The sum of the least remaining component execution lengths strictly decreases.
Thus all tokens are eventually accepted.  The final scheduled filling has
exactly the sum of the actual component output row lengths.  This supplies
the initial filling for Hanada's comparison argument; the separate greedy
comparison is not assumed or asserted here.
-/

noncomputable section
open TauCeti Finset Function
open scoped Classical

namespace HigherSpecht

variable {n : ℕ} {κ : Type*} [Fintype κ]

structure ShuffledCatState (n : ℕ) (κ : Type*) where
  globalState : LabeledCatState n
  localShape : κ → YoungDiagram

def shuffledInitial (n : ℕ) (κ : Type*) : ShuffledCatState n κ :=
  ⟨labeledInitial n, fun _ => ⊥⟩

def shuffledLocalState (a : Fin n → ℕ) (color : Fin n → κ)
    (s : ShuffledCatState n κ) (c : κ) : CatState :=
  ⟨((s.globalState.pending.filter fun t => decide (color t.position = c)).map
    (tokenValue a)).reverse, s.localShape c⟩

/-- The actual subword of scan positions of one color, in the paper's reading
order.  The reversal converts scan order to the word read from its right end. -/
def shuffledInputWord (a : Fin n → ℕ) (color : Fin n → κ) (c : κ) : List ℕ :=
  (shuffledLocalState a color (shuffledInitial n κ) c).word

theorem shuffledInputWord_eq (a : Fin n → ℕ) (color : Fin n → κ) (c : κ) :
    shuffledInputWord a color c =
      (((List.finRange n).filter fun i => decide (color i = c)).map a).reverse := by
  simp [shuffledInputWord, shuffledLocalState, shuffledInitial, labeledInitial,
    initialCyclingQueue, List.ofFn_eq_map, List.filter_map, List.map_map,
    Function.comp_def, tokenValue]

@[simp] theorem shuffledLocalState_initial (a : Fin n → ℕ) (color : Fin n → κ) (c : κ) :
    shuffledLocalState a color (shuffledInitial n κ) c =
      ⟨shuffledInputWord a color c, ⊥⟩ := rfl

def shuffledCatStep (a : Fin n → ℕ) (color : Fin n → κ)
    (s : ShuffledCatState n κ) : ShuffledCatState n κ :=
  match s.globalState.pending with
  | [] => s
  | t :: q =>
    let c := color t.position
    let r := tokenValue a t
    if YoungDiagram.IsAddable (s.localShape c) (r, (s.localShape c).rowLen r) then
      ⟨⟨q, s.globalState.shape.addCell (r, s.globalState.shape.rowLen r),
        s.globalState.accepted ++ [(t, (r, s.globalState.shape.rowLen r))]⟩,
        Function.update s.localShape c ((s.localShape c).addCell (r, (s.localShape c).rowLen r))⟩
    else
      ⟨⟨q ++ [t.bump], s.globalState.shape, s.globalState.accepted⟩, s.localShape⟩

def shuffledCatRun (a : Fin n → ℕ) (color : Fin n → κ) (N : ℕ)
    (s : ShuffledCatState n κ) : ShuffledCatState n κ :=
  (shuffledCatStep a color)^[N] s

theorem shuffledLocalState_step {a : Fin n → ℕ} {color : Fin n → κ}
    {s : ShuffledCatState n κ} {t : CyclingToken n} {q : List (CyclingToken n)}
    (hp : s.globalState.pending = t :: q) (c : κ) :
    shuffledLocalState a color (shuffledCatStep a color s) c =
      if c = color t.position then catStep (shuffledLocalState a color s c)
      else shuffledLocalState a color s c := by
  classical
  by_cases hc : c = color t.position
  · subst c
    simp only [if_pos rfl]
    unfold shuffledCatStep
    rw [hp]
    dsimp only
    split_ifs with hadd
    · simp only [shuffledLocalState, hp, List.filter_cons, decide_true, Bool.coe_true,
        if_true, List.map_cons, List.reverse_cons, Function.update_self]
      rw [catStep_append, if_pos hadd]
    · simp only [shuffledLocalState, hp, List.filter_cons, decide_true, Bool.coe_true,
        if_true, List.map_cons, List.reverse_cons, List.filter_append, List.filter_nil,
        CyclingToken.position_bump, List.map_append, List.map_nil, List.reverse_append,
        List.reverse_nil, List.nil_append, tokenValue_bump]
      rw [catStep_append, if_neg hadd]
      rfl
  · have hne : color t.position ≠ c := Ne.symm hc
    simp only [if_neg hc]
    unfold shuffledCatStep
    rw [hp]
    dsimp only
    split_ifs <;>
      simp [shuffledLocalState, hp, hc, hne, Function.update_of_ne,
        List.filter_append, CyclingToken.position_bump]

theorem shuffledLocalState_nonempty {a : Fin n → ℕ} {color : Fin n → κ}
    {s : ShuffledCatState n κ} {t : CyclingToken n} {q : List (CyclingToken n)}
    (hp : s.globalState.pending = t :: q) :
    (shuffledLocalState a color s (color t.position)).word ≠ [] := by
  simp [shuffledLocalState, hp]

def ShuffledRowSum (s : ShuffledCatState n κ) : Prop :=
  ∀ r, s.globalState.shape.rowLen r = ∑ c, (s.localShape c).rowLen r

theorem addable_of_component_addable {s : ShuffledCatState n κ} (hs : ShuffledRowSum s)
    {c : κ} {r : ℕ}
    (hadd : YoungDiagram.IsAddable (s.localShape c) (r, (s.localShape c).rowLen r)) :
    YoungDiagram.IsAddable s.globalState.shape (r, s.globalState.shape.rowLen r) := by
  rw [isAddable_rowEnd_iff] at hadd ⊢
  rcases hadd with hzero | hlt
  · exact Or.inl hzero
  · apply Or.inr
    rw [hs r, hs (r - 1)]
    exact Finset.sum_lt_sum
      (fun d _ => (s.localShape d).rowLen_anti _ _ (Nat.sub_le r 1))
      ⟨c, Finset.mem_univ c, hlt⟩

theorem shuffledCatStep_lazy {a : Fin n → ℕ} {color : Fin n → κ}
    {s : ShuffledCatState n κ} (hs : ShuffledRowSum s)
    (hnil : s.globalState.pending ≠ []) :
    LazyLabeledStep a s.globalState (shuffledCatStep a color s).globalState := by
  cases hp : s.globalState.pending with
  | nil => exact (hnil hp).elim
  | cons t q =>
      unfold shuffledCatStep
      rw [hp]
      dsimp only
      split_ifs with hadd
      · have hglobal := addable_of_component_addable hs hadd
        change LazyLabeledStep a
          ⟨s.globalState.pending, s.globalState.shape, s.globalState.accepted⟩ _
        rw [hp]
        exact LazyLabeledStep.accept t q s.globalState.shape s.globalState.accepted hglobal
      · change LazyLabeledStep a
          ⟨s.globalState.pending, s.globalState.shape, s.globalState.accepted⟩ _
        rw [hp]
        exact LazyLabeledStep.reject t q s.globalState.shape s.globalState.accepted

theorem shuffledRowSum_step {a : Fin n → ℕ} {color : Fin n → κ}
    {s : ShuffledCatState n κ} (hs : ShuffledRowSum s) :
    ShuffledRowSum (shuffledCatStep a color s) := by
  classical
  cases hp : s.globalState.pending with
  | nil => simpa only [shuffledCatStep, hp] using hs
  | cons t q =>
      unfold shuffledCatStep
      rw [hp]
      dsimp only
      split_ifs with hadd
      · have hglobal := addable_of_component_addable hs hadd
        intro j
        rw [hglobal.rowLen_addCell]
        have hsum :
            (∑ c, (Function.update s.localShape (color t.position)
              ((s.localShape (color t.position)).addCell
                (tokenValue a t, (s.localShape (color t.position)).rowLen (tokenValue a t))) c).rowLen j) =
            (∑ c, (s.localShape c).rowLen j) + if j = tokenValue a t then 1 else 0 := by
          have hfun : (fun c => (Function.update s.localShape (color t.position)
              ((s.localShape (color t.position)).addCell
                (tokenValue a t, (s.localShape (color t.position)).rowLen (tokenValue a t))) c).rowLen j) =
              Function.update (fun c => (s.localShape c).rowLen j) (color t.position)
                ((s.localShape (color t.position)).rowLen j +
                  if j = tokenValue a t then 1 else 0) := by
            funext c
            by_cases hc : c = color t.position
            · subst c
              simp only [Function.update_self, hadd.rowLen_addCell]
              by_cases hr : j = tokenValue a t
              · subst j
                simp
              · simp [hr, Ne.symm hr]
            · simp only [Function.update_of_ne hc]
          rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ _),
            Finset.sdiff_singleton_eq_erase]
          have hsplit := Finset.sum_erase_add (Finset.univ : Finset κ)
            (fun c => (s.localShape c).rowLen j) (Finset.mem_univ (color t.position))
          omega
        rw [hs j, hsum]
        by_cases hr : tokenValue a t = j
        · subst j
          simp
        · simp [hr, Ne.symm hr]
      · exact hs

/-- Least remaining length of an actual terminating component execution. -/
def catStateOutputSteps (s : CatState) (nu : YoungDiagram) (h : CatStateOutput s nu) : ℕ :=
  Nat.find h

theorem catStateOutputSteps_congr {s t : CatState} {nu : YoungDiagram}
    (heq : s = t) (hs : CatStateOutput s nu) (ht : CatStateOutput t nu) :
    catStateOutputSteps s nu hs = catStateOutputSteps t nu ht := by
  subst t
  rfl

theorem catStateOutputSteps_step_lt {s : CatState} {nu : YoungDiagram}
    (h : CatStateOutput s nu) (hstep : CatStateOutput (catStep s) nu)
    (hnil : s.word ≠ []) :
    catStateOutputSteps (catStep s) nu hstep < catStateOutputSteps s nu h := by
  have hs := Nat.find_spec h
  cases heq : Nat.find h with
  | zero =>
      rw [heq] at hs
      exact (hnil (congrArg CatState.word hs)).elim
  | succ k =>
      have hk : catRun k (catStep s) = ⟨[], nu⟩ := by
        rw [heq] at hs
        simpa only [catRun, Function.iterate_succ_apply] using hs
      exact (Nat.find_min' hstep hk).trans_lt (by
        change k < Nat.find h
        rw [heq]
        exact Nat.lt_succ_self k)

structure ShuffledInvariant (a : Fin n → ℕ) (color : Fin n → κ)
    (nu : κ → YoungDiagram) (s : ShuffledCatState n κ) : Prop where
  execution : LazyLabeledRun a (labeledInitial n) s.globalState
  rowSum : ShuffledRowSum s
  localOutput : ∀ c, CatStateOutput (shuffledLocalState a color s c) (nu c)

theorem shuffledInvariant_initial (a : Fin n → ℕ) (color : Fin n → κ)
    (nu : κ → YoungDiagram)
    (hout : ∀ c, CatWordOutput (shuffledInputWord a color c) (nu c)) :
    ShuffledInvariant a color nu (shuffledInitial n κ) := by
  refine ⟨LazyLabeledRun.refl, ?_, ?_⟩
  · intro r
    simp [ShuffledRowSum, shuffledInitial, labeledInitial]
  · intro c
    exact hout c

theorem ShuffledInvariant.step {a : Fin n → ℕ} {color : Fin n → κ}
    {nu : κ → YoungDiagram} {s : ShuffledCatState n κ}
    (hs : ShuffledInvariant a color nu s) :
    ShuffledInvariant a color nu (shuffledCatStep a color s) := by
  cases hp : s.globalState.pending with
  | nil => simpa only [shuffledCatStep, hp] using hs
  | cons t q =>
      refine ⟨hs.execution.tail (shuffledCatStep_lazy hs.rowSum (by simp [hp])),
        shuffledRowSum_step hs.rowSum, ?_⟩
      intro c
      rw [shuffledLocalState_step hp c]
      split_ifs with hc
      · exact (catStateOutput_iff_run _ _ 1).mp (hs.localOutput c)
      · exact hs.localOutput c

def shuffledPotential (a : Fin n → ℕ) (color : Fin n → κ)
    (nu : κ → YoungDiagram) (s : ShuffledCatState n κ)
    (hs : ShuffledInvariant a color nu s) : ℕ :=
  ∑ c, catStateOutputSteps (shuffledLocalState a color s c) (nu c) (hs.localOutput c)

theorem shuffledPotential_step_lt {a : Fin n → ℕ} {color : Fin n → κ}
    {nu : κ → YoungDiagram} {s : ShuffledCatState n κ}
    (hs : ShuffledInvariant a color nu s) (hnil : s.globalState.pending ≠ []) :
    shuffledPotential a color nu (shuffledCatStep a color s) hs.step <
      shuffledPotential a color nu s hs := by
  classical
  obtain ⟨t, q, hp⟩ := List.exists_cons_of_ne_nil hnil
  have hstrict : catStateOutputSteps
      (shuffledLocalState a color (shuffledCatStep a color s) (color t.position))
        (nu (color t.position)) (hs.step.localOutput _) <
      catStateOutputSteps (shuffledLocalState a color s (color t.position))
        (nu (color t.position)) (hs.localOutput _) := by
    have heq := shuffledLocalState_step (a := a) (color := color) hp (color t.position)
    simp only [if_pos rfl, if_true] at heq
    have hstep : CatStateOutput (catStep (shuffledLocalState a color s (color t.position)))
        (nu (color t.position)) :=
      (catStateOutput_iff_run _ _ 1).mp (hs.localOutput _)
    rw [catStateOutputSteps_congr heq _ hstep]
    exact catStateOutputSteps_step_lt _ _ (shuffledLocalState_nonempty (a := a) (color := color) hp)
  unfold shuffledPotential
  apply Finset.sum_lt_sum
  · intro c hc
    by_cases heq : c = color t.position
    · subst c
      exact hstrict.le
    · have hsame := shuffledLocalState_step (a := a) (color := color) hp c
      rw [if_neg heq] at hsame
      exact (catStateOutputSteps_congr hsame _ _).le
  · exact ⟨color t.position, Finset.mem_univ _, hstrict⟩

theorem shuffledCatRun_eventually_empty {a : Fin n → ℕ} {color : Fin n → κ}
    {nu : κ → YoungDiagram} {s : ShuffledCatState n κ}
    (hs : ShuffledInvariant a color nu s) :
    ∃ N, (shuffledCatRun a color N s).globalState.pending = [] ∧
      ShuffledInvariant a color nu (shuffledCatRun a color N s) := by
  have aux : ∀ m : ℕ, ∀ s : ShuffledCatState n κ,
      ∀ hs : ShuffledInvariant a color nu s,
      shuffledPotential a color nu s hs = m →
      ∃ N, (shuffledCatRun a color N s).globalState.pending = [] ∧
        ShuffledInvariant a color nu (shuffledCatRun a color N s) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro s hs hm
        by_cases hnil : s.globalState.pending = []
        · exact ⟨0, hnil, hs⟩
        · have hlt := shuffledPotential_step_lt hs hnil
          rw [hm] at hlt
          obtain ⟨N, hN, hI⟩ := ih _ hlt _ hs.step rfl
          refine ⟨N + 1, ?_⟩
          simpa only [shuffledCatRun, Function.iterate_succ_apply] using And.intro hN hI
  exact aux _ s hs rfl

/-- A shuffle of actual terminating component words has a complete lazy
scheduled filling whose row lengths are the componentwise sum of their
actual catabolism outputs.  No admissibility or comparison assumption is
needed in addition to those terminating local executions. -/
theorem exists_scheduledFilling_of_shuffle_outputs
    (a : Fin n → ℕ) (color : Fin n → κ) (nu : κ → YoungDiagram)
    (hout : ∀ c, CatWordOutput (shuffledInputWord a color c) (nu c)) :
    ∃ F : ScheduledFilling a, ∀ r, F.shape.rowLen r = ∑ c, (nu c).rowLen r := by
  obtain ⟨N, hnil, hI⟩ := shuffledCatRun_eventually_empty
    (shuffledInvariant_initial a color nu hout)
  let s := shuffledCatRun a color N (shuffledInitial n κ)
  obtain ⟨F, hF⟩ := exists_scheduledFilling_of_lazyRun hI.execution hnil
  have hlocal : ∀ c, s.localShape c = nu c := by
    intro c
    obtain ⟨k, hk⟩ := hI.localOutput c
    have hword : (shuffledLocalState a color s c).word = [] := by
      simp only [shuffledLocalState, show s.globalState.pending = [] from hnil,
        List.filter_nil, List.map_nil, List.reverse_nil]
    have hstate : shuffledLocalState a color s c = ⟨[], s.localShape c⟩ :=
      CatState.ext hword rfl
    rw [hstate, catRun_empty] at hk
    exact congrArg CatState.shape hk
  refine ⟨F, fun r => ?_⟩
  rw [hF, hI.rowSum r]
  exact Finset.sum_congr rfl (fun c _ => congrArg (fun d : YoungDiagram => d.rowLen r) (hlocal c))

/-- Among diagrams of a given cardinality, a column has the smallest row
prefix sums.  This is proved from the actual row lengths. -/
theorem min_card_le_rowPrefix (nu : YoungDiagram) (r : ℕ) :
    min r nu.card ≤ ∑ i ∈ Finset.range r, nu.rowLen i := by
  by_cases hr : r ≤ nu.colLen 0
  · have hones : r ≤ ∑ i ∈ Finset.range r, nu.rowLen i := by
      calc
        r = ∑ i ∈ Finset.range r, (1 : ℕ) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          have hic : i < nu.colLen 0 := (Finset.mem_range.mp hi).trans_le hr
          have hm : (i, 0) ∈ nu := YoungDiagram.mem_iff_lt_colLen.mpr hic
          exact YoungDiagram.mem_iff_lt_rowLen.mp hm
    exact (min_le_left _ _).trans hones
  · rw [← YoungDiagram.card_eq_sum_range_rowLen nu (Nat.le_of_not_ge hr)]
    exact min_le_right _ _

theorem rowPrefix_eq_sum_min_columns (lam : YoungDiagram) {m : ℕ}
    (hm : lam.rowLen 0 ≤ m) (r : ℕ) :
    (∑ i ∈ Finset.range r, lam.rowLen i) =
      ∑ j : Fin m, min r (lam.colLen j.val) := by
  rw [YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
  have hmaps : ∀ c ∈ lam.cells.filter (fun c => c.1 < r),
      c.2 ∈ Finset.range m := by
    intro c hc
    have hcell : c ∈ lam := (Finset.mem_filter.mp hc).1
    exact Finset.mem_range.mpr
      ((YoungDiagram.mem_iff_lt_rowLen.mp hcell).trans_le
        ((lam.rowLen_anti 0 c.1 c.1.zero_le).trans hm))
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) hmaps]
  simp_rw [YoungDiagram.card_filter_fst_lt_filter_snd_eq]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- In particular, shuffling words whose lengths cover the columns of `lam`
gives an actual scheduled filling dominating `lam`.  The further statement
that the greedy output dominates this scheduled filling remains separate. -/
theorem exists_scheduledFilling_dominating_of_column_shuffle
    {m : ℕ} (a : Fin n → ℕ) (color : Fin n → Fin m)
    (lam : YoungDiagram) (hm : lam.rowLen 0 ≤ m)
    (nu : Fin m → YoungDiagram)
    (hout : ∀ j, CatWordOutput (shuffledInputWord a color j) (nu j))
    (hsize : ∀ j, lam.colLen j.val ≤ (shuffledInputWord a color j).length) :
    ∃ F : ScheduledFilling a, Dominates F.shape lam := by
  obtain ⟨F, hF⟩ := exists_scheduledFilling_of_shuffle_outputs a color nu hout
  refine ⟨F, fun r => ?_⟩
  rw [rowPrefix_eq_sum_min_columns lam hm r]
  simp_rw [hF]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  have hcard : lam.colLen j.val ≤ (nu j).card := by
    rw [catWordOutput_card (hout j)]
    exact hsize j
  exact (min_le_min_left r hcard).trans (min_card_le_rowPrefix (nu j) r)

end HigherSpecht
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/HanadaGreedyDominance.lean -/



/-!
# Greedy cyclic insertion dominates every genuine scheduled filling

The proof follows the actual queue, including its sparse later rounds.  At
each visit the literal exchange supplies the acceptance update, rejection
keeps the comparison rows, and the cyclic-window lemma rebases the processed
cutoff at the next queue head.  The final theorem has no exchange, filling
preservation, or dominance premise beyond the defining scheduled filling.

Combining it with the independently constructed shuffle execution yields the
row-prefix comparison for actual terminating component outputs.  This is a
comparison theorem, not by itself the cardinality or basis theorem.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

theorem labeledCatRun_eq_of_pending_nil {n : ℕ} (a : Fin n → ℕ)
    {s : LabeledCatState n} (hs : s.pending = []) (N : ℕ) :
    labeledCatRun a N s = s := by
  apply Function.iterate_fixed
  simp only [labeledCatStep, hs]

theorem labeledCatStep_pending_subset {n : ℕ} (a : Fin n → ℕ)
    {s : LabeledCatState n} {t : CyclingToken n} {q : List (CyclingToken n)}
    (hhead : s.pending = t :: q) :
    (labeledCatStep a s).pending ⊆ q ++ [t.bump] := by
  unfold labeledCatStep
  rw [hhead]
  dsimp only
  split_ifs with hadd
  · exact List.subset_append_left q [t.bump]
  · exact List.Subset.refl _

/-- Induction on the actual finite run.  The acceptance update is derived
from the literal exchange, rather than supplied as an induction premise. -/
theorem GreedyRowsInvariant.run_terminal_dominates {n : ℕ} {a : Fin n → ℕ}
    {initialShape : YoungDiagram} (N : ℕ) :
    ∀ {s : LabeledCatState n} {cutoff : VisitTime n}
      (W : GreedyRowsInvariant a initialShape s cutoff)
      (hs : LabeledInvariant a s)
      {t : CyclingToken n} {q : List (CyclingToken n)},
      s.pending = t :: q → cutoff = visitTime t.round t.position →
      (labeledCatRun a N s).pending = [] →
      Dominates (labeledCatRun a N s).shape initialShape := by
  induction N with
  | zero =>
      intro s cutoff W hs t q hhead hcutoff hnil
      have : t :: q = [] := hhead.symm.trans hnil
      exact (List.cons_ne_nil _ _ this).elim
  | succ N ih =>
      intro s cutoff W hs t q hhead hcutoff hnil
      have hs' := labeledInvariant_step a hs
      have hqueue : CyclingQueueValid (t :: q) := by
        simpa only [hhead] using
          (hs.execution.ordering (initialCyclingQueue_valid n)).1
      let C : ClosedGreedyRowsInvariant a initialShape (labeledCatStep a s) cutoff :=
        if hadd : YoungDiagram.IsAddable s.shape
            (tokenValue a t, s.shape.rowLen (tokenValue a t)) then
          W.close_accepted hhead hcutoff hadd
            (W.acceptance_update hs hhead hcutoff hadd)
        else W.close_rejected hhead hcutoff hadd
      have hrun : labeledCatRun a (N + 1) s =
          labeledCatRun a N (labeledCatStep a s) := by
        exact Function.iterate_succ_apply _ _ _
      rw [hrun] at hnil ⊢
      cases hnext : (labeledCatStep a s).pending with
      | nil =>
          rw [labeledCatRun_eq_of_pending_nil a hnext N]
          exact C.terminal_dominates hs' hnext
      | cons u newTail =>
          let W' := C.reopen hs' hcutoff hqueue
            (labeledCatStep_pending_subset a hhead) hnext
          exact ih W' hs' hnext rfl hnil

/-- A scheduled filling on no tokens has no cells. -/
theorem ScheduledFilling.shape_eq_bot_of_zero {a : Fin 0 → ℕ}
    (F : ScheduledFilling a) : F.shape = ⊥ := by
  apply YoungDiagram.ext
  rw [YoungDiagram.cells_bot]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  exact Fin.elim0 (F.token ⟨c, hc⟩)

/-- Comparison with every genuine finite greedy run that terminates. -/
theorem ScheduledFilling.labeledRun_dominates {n : ℕ} {a : Fin n → ℕ}
    (F : ScheduledFilling a) (N : ℕ)
    (hnil : (labeledCatRun a N (labeledInitial n)).pending = []) :
    Dominates (labeledCatRun a N (labeledInitial n)).shape F.shape := by
  cases n with
  | zero =>
      rw [F.shape_eq_bot_of_zero]
      intro r
      simp only [YoungDiagram.rowLen_bot, Finset.sum_const_zero, Nat.zero_le]
  | succ n =>
      let t : CyclingToken (n + 1) := ⟨0, 0⟩
      let q : List (CyclingToken (n + 1)) :=
        List.ofFn (fun i : Fin n => (⟨i.succ, 0⟩ : CyclingToken (n + 1)))
      have hhead : (labeledInitial (n + 1)).pending = t :: q := by
        simp only [labeledInitial, initialCyclingQueue, List.ofFn_succ, t, q]
      exact GreedyRowsInvariant.run_terminal_dominates N F.initialGreedyRows
        (labeledInvariant_initial a) hhead rfl hnil

/-- The actual catabolism output dominates the given scheduled filling.
The output hypothesis is its literal terminating execution, not a surrogate
partition or a modified algorithm. -/
theorem catWordOutput_dominates_scheduledFilling {n : ℕ} {a : Fin n → ℕ}
    (F : ScheduledFilling a) {mu : YoungDiagram}
    (hout : CatWordOutput (List.ofFn a).reverse mu) : Dominates mu F.shape := by
  obtain ⟨N, hN⟩ := hout
  let s := labeledCatRun a N (labeledInitial n)
  have hforget : labeledForget a s = ⟨[], mu⟩ := by
    dsimp only [s]
    rw [labeledForget_run, labeledForget_initial]
    exact hN
  have hnil : s.pending = [] := by
    have hword := congrArg CatState.word hforget
    simpa only [labeledForget, List.reverse_eq_nil_iff, List.map_eq_nil_iff] using hword
  have hshape : s.shape = mu := congrArg CatState.shape hforget
  have hdom := F.labeledRun_dominates N hnil
  change Dominates s.shape F.shape at hdom
  rwa [hshape] at hdom

/-- Hanada's full shuffle comparison, stated directly as row-prefix sums.
All component shapes and the global shape are actual terminating outputs. -/
theorem catWordOutput_dominates_shuffle_outputs {n : ℕ} {κ : Type*} [Fintype κ]
    (a : Fin n → ℕ) (color : Fin n → κ) (nu : κ → YoungDiagram)
    (hout : ∀ c, CatWordOutput (shuffledInputWord a color c) (nu c))
    {mu : YoungDiagram} (hmu : CatWordOutput (List.ofFn a).reverse mu) :
    ∀ r, (∑ c, ∑ i ∈ Finset.range r, (nu c).rowLen i) ≤
      ∑ i ∈ Finset.range r, mu.rowLen i := by
  obtain ⟨F, hF⟩ := exists_scheduledFilling_of_shuffle_outputs a color nu hout
  have hdom := catWordOutput_dominates_scheduledFilling F hmu
  intro r
  have h := hdom r
  simp_rw [hF] at h
  calc
    (∑ c, ∑ i ∈ Finset.range r, (nu c).rowLen i) =
        ∑ i ∈ Finset.range r, ∑ c, (nu c).rowLen i := Finset.sum_comm
    _ ≤ ∑ i ∈ Finset.range r, mu.rowLen i := h

/-- The column-shuffle consequence used in the eligibility argument. -/
theorem catWordOutput_dominates_of_column_shuffle {n m : ℕ}
    (a : Fin n → ℕ) (color : Fin n → Fin m)
    (lam : YoungDiagram) (hm : lam.rowLen 0 ≤ m)
    (nu : Fin m → YoungDiagram)
    (hout : ∀ j, CatWordOutput (shuffledInputWord a color j) (nu j))
    (hsize : ∀ j, lam.colLen j.val ≤ (shuffledInputWord a color j).length)
    {mu : YoungDiagram} (hmu : CatWordOutput (List.ofFn a).reverse mu) :
    Dominates mu lam := by
  obtain ⟨F, hF⟩ := exists_scheduledFilling_dominating_of_column_shuffle
    a color lam hm nu hout hsize
  exact (catWordOutput_dominates_scheduledFilling F hmu).trans hF

end HigherSpecht
end
end CanonicalSource15

section CanonicalSource16
/- Source: HigherSpecht/HanadaCyclageDominance.lean -/



/-!
# Dominance under a decremented ordinary cyclic move

The input `A :: w`, with `A>0`, is replaced by `w ++ [A-1]`.
In scan order the last token becomes the first token and its visit number
increases by one.  Its row is unchanged and every absolute visit stamp
increases by exactly one.  Thus a genuine scheduled filling transports
without changing its shape.  The proved greedy comparison then gives the
dominance direction explicitly: the new output dominates the old one.

This lemma concerns literal labels and actual terminating executions.  The
separate cocharge calculation is needed to apply it to ordinary cyclage of
a standard word.
-/

noncomputable section
open TauCeti
open scoped Classical

namespace HigherSpecht

def rotateScanPosition (n : ℕ) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.lastCases 0 (fun i => i.succ)
  invFun := Fin.cases (Fin.last n) (fun i => i.castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem rotateScanPosition_last (n : ℕ) :
    rotateScanPosition n (Fin.last n) = 0 := by
  simp [rotateScanPosition]

@[simp] theorem rotateScanPosition_castSucc (n : ℕ) (i : Fin n) :
    rotateScanPosition n i.castSucc = i.succ := by
  simp [rotateScanPosition]

def rotateVisit {n : ℕ} (z : VisitTime (n + 1)) : VisitTime (n + 1) :=
  visitTime ((ofLex z).1 + if (ofLex z).2 = Fin.last n then 1 else 0)
    (rotateScanPosition n (ofLex z).2)

theorem visitStamp_rotateVisit {n : ℕ} (z : VisitTime (n + 1)) :
    visitStamp (rotateVisit z) = visitStamp z + 1 := by
  let p := (ofLex z).1
  let i := (ofLex z).2
  change visitStamp (visitTime (p + if i = Fin.last n then 1 else 0)
    (rotateScanPosition n i)) = p * (n + 1) + i.val + 1
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [if_pos rfl, if_true, rotateScanPosition_last, visitStamp_visitTime,
      Fin.val_zero, Fin.val_last, Nat.add_mul, one_mul]
    omega
  · have hne : j.castSucc ≠ Fin.last n := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      have hj := j.isLt
      omega
    simp only [if_neg hne, Nat.add_zero, rotateScanPosition_castSucc,
      visitStamp_visitTime, Fin.val_succ, Fin.val_castSucc]
    omega

theorem rotateVisit_strictMono {n : ℕ} : StrictMono (rotateVisit (n := n)) := by
  intro z w hzw
  apply (visitStamp_strictMono (n := n + 1)).lt_iff_lt.mp
  rw [visitStamp_rotateVisit, visitStamp_rotateVisit]
  exact Nat.add_lt_add_right (visitStamp_strictMono hzw) 1

/-- The literal scheduled filling after moving the last-read token to the
next scan's first position.  Its Young diagram is unchanged. -/
def ScheduledFilling.rotateDecrement {n : ℕ} {a : Fin n → ℕ} {A : ℕ}
    (F : ScheduledFilling (Fin.snoc a A)) (hA : 0 < A) :
    ScheduledFilling (Fin.cons (A - 1) a) where
  shape := F.shape
  token := F.token.trans (rotateScanPosition n)
  visit j :=
    let i := (rotateScanPosition n).symm j
    F.visit i + if i = Fin.last n then 1 else 0
  row_eq := by
    intro c
    have hid (i : Fin (n + 1)) :
        (Fin.cons (A - 1) a : Fin (n + 1) → ℕ) (rotateScanPosition n i) +
          (F.visit i + if i = Fin.last n then 1 else 0) =
        (Fin.snoc a A : Fin (n + 1) → ℕ) i + F.visit i := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [rotateScanPosition_last, Fin.cons_zero, Fin.snoc_last,
          if_pos rfl, if_true]
        omega
      · have hne : j.castSucc ≠ Fin.last n := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castSucc, Fin.val_last] at hv
          have hj := j.isLt
          omega
        simp only [rotateScanPosition_castSucc, Fin.cons_succ,
          Fin.snoc_castSucc, if_neg hne, Nat.add_zero]
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using
      (F.row_eq c).trans (hid (F.token c)).symm
  time_strict := by
    intro c d hcd
    have hh := rotateVisit_strictMono (F.time_strict c d hcd)
    change rotateVisit (visitTime (F.visit (F.token c)) (F.token c)) <
      rotateVisit (visitTime (F.visit (F.token d)) (F.token d)) at hh
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    change rotateVisit (visitTime (F.visit (F.token c)) (F.token c)) <
      rotateVisit (visitTime (F.visit (F.token d)) (F.token d))
    exact hh

@[simp] theorem ScheduledFilling.rotateDecrement_shape {n : ℕ}
    {a : Fin n → ℕ} {A : ℕ} (F : ScheduledFilling (Fin.snoc a A)) (hA : 0 < A) :
    (F.rotateDecrement hA).shape = F.shape := rfl

/-- A terminating one-color execution supplies its own actual scheduled
filling.  This is a specialization of the proved shuffle construction. -/
theorem exists_scheduledFilling_of_catWordOutput {n : ℕ} (a : Fin n → ℕ)
    {mu : YoungDiagram} (hout : CatWordOutput (List.ofFn a).reverse mu) :
    ∃ F : ScheduledFilling a, F.shape = mu := by
  have hlocal : ∀ c : Unit,
      CatWordOutput (shuffledInputWord a (fun _ => ()) c) mu := by
    intro c
    cases c
    simpa only [shuffledInputWord_eq, decide_true, List.filter_true,
      ← List.ofFn_eq_map] using hout
  obtain ⟨F, hF⟩ := exists_scheduledFilling_of_shuffle_outputs a
    (fun _ => ()) (fun _ : Unit => mu) hlocal
  refine ⟨F, ?_⟩
  have hrow : ∀ r, F.shape.rowLen r = mu.rowLen r := by
    intro r
    simpa using hF r
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨r, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hrow]

/-- The new output dominates the old output.  No equality of the two
outputs is asserted, and both hypotheses are actual executions. -/
theorem catWordOutput_rotate_decrement_dominates {A : ℕ} (hA : 0 < A)
    (w : List ℕ) {mu nu : YoungDiagram}
    (hold : CatWordOutput (A :: w) mu)
    (hnew : CatWordOutput (w ++ [A - 1]) nu) : Dominates nu mu := by
  let a : Fin w.length → ℕ := fun i => w.reverse.get (Fin.cast (List.length_reverse (as := w)).symm i)
  have ha : List.ofFn a = w.reverse := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_reverse]
    · intro i hi hi'
      simp only [List.getElem_ofFn, a, List.get_eq_getElem, Fin.cast_mk]
  have hscanOld : (List.ofFn (Fin.snoc a A)).reverse = A :: w := by
    simp only [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, ha, List.concat_eq_append,
      List.reverse_append, List.reverse_singleton, List.reverse_reverse,
      List.singleton_append]
  have hscanNew : (List.ofFn (Fin.cons (A - 1) a)).reverse = w ++ [A - 1] := by
    simp only [List.ofFn_cons, ha, List.reverse_cons, List.reverse_reverse]
  obtain ⟨F, hF⟩ := exists_scheduledFilling_of_catWordOutput (Fin.snoc a A)
    (hscanOld.symm ▸ hold)
  have hdom := catWordOutput_dominates_scheduledFilling (F.rotateDecrement hA)
    (hscanNew.symm ▸ hnew)
  simpa only [ScheduledFilling.rotateDecrement_shape, hF] using hdom

end HigherSpecht
end
end CanonicalSource16

section CanonicalSource17
/- Source: HigherSpecht/StandardCyclageCocharge.lean -/



/-!
# The exact cocharge change under ordinary rotation

For a permutation word beginning with a nonminimal letter `a`, moving `a`
to the end removes the inverse descent immediately before `a` and adds
the one immediately after it.  Their partial sums cancel except at `a`.
Consequently only that letter's cocharge label decreases, by exactly one.
The scheduled-filling transport then proves the forward dominance of the
actual catabolizability outputs.
-/

noncomputable section
open TauCeti

namespace HigherSpecht

theorem pair_sublist_singleton_false (a x y : ℕ) :
    ¬ [x, y].Sublist [a] := by
  intro h
  have hl := h.length_le
  simp only [List.length_cons, List.length_nil] at hl
  omega

theorem standardWord_tail_mem {n a j : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (hj : j < n) (hja : j ≠ a) : j ∈ w := by
  have hm : j ∈ a :: w := hw.mem_iff.mpr (List.mem_range.mpr hj)
  rcases List.mem_cons.mp hm with h | h
  · exact (hja h).elim
  · exact h

/-- The precise cancellation identity for the two adjacent inverse
descent indicators affected by the cyclic move. -/
theorem inverseDescent_rotate_balance {n a : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (j : ℕ) (hj : j + 1 < n) :
    (if [j + 1, j].Sublist (w ++ [a]) then (1 : ℕ) else 0) +
        (if j + 1 = a then 1 else 0) =
      (if [j + 1, j].Sublist (a :: w) then (1 : ℕ) else 0) +
        (if j = a then 1 else 0) := by
  have hnodup := hw.nodup_iff.mpr List.nodup_range
  have hnot : a ∉ w := (List.nodup_cons.mp hnodup).1
  have hold : [j + 1, j].Sublist (a :: w) ↔
      (j + 1 = a ∧ j ∈ w) ∨ [j + 1, j].Sublist w := by
    have h := pair_sublist_append_iff (a := j + 1) (b := j) [a] w
    simpa only [List.singleton_append, List.mem_singleton,
      pair_sublist_singleton_false, false_or] using h
  have hnew : [j + 1, j].Sublist (w ++ [a]) ↔
      [j + 1, j].Sublist w ∨ (j + 1 ∈ w ∧ j = a) := by
    have h := pair_sublist_append_iff (a := j + 1) (b := j) w [a]
    simpa only [List.mem_singleton, pair_sublist_singleton_false, or_false] using h
  by_cases hja : j = a
  · subst j
    have hm : a + 1 ∈ w := standardWord_tail_mem hw hj (by omega)
    have hp : ¬ [a + 1, a].Sublist w := not_pair_sublist_of_notMem_right hnot
    simp only [hold, hnew, hp, hm, Nat.add_one_ne_self, false_and,
      false_or, true_and, if_true, if_false]
  · by_cases hsucc : j + 1 = a
    · have hm : j ∈ w := standardWord_tail_mem hw (by omega) hja
      have hp : ¬ [j + 1, j].Sublist w := by
        apply not_pair_sublist_of_notMem_left
        simpa only [hsucc] using hnot
      have hold' : [j + 1, j].Sublist (a :: w) := hold.mpr (Or.inl ⟨hsucc, hm⟩)
      have hnew' : ¬ [j + 1, j].Sublist (w ++ [a]) := by
        intro hh
        rcases hnew.mp hh with hh | hh
        · exact hp hh
        · exact hja hh.2
      simp only [if_pos hold', if_neg hnew', if_pos hsucc, if_neg hja]
    · simp only [hold, hnew, hsucc, hja, false_and, and_false,
        false_or, or_false, if_false, Nat.add_zero]

theorem wordCochargeLabel_rotate_exact {n a : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (ha : 0 < a)
    (j : ℕ) (hj : j < n) :
    wordCochargeLabel (w ++ [a]) j + (if j = a then 1 else 0) =
      wordCochargeLabel (a :: w) j := by
  induction j with
  | zero => simp only [wordCochargeLabel_zero, if_neg (Nat.ne_of_gt ha).symm, Nat.add_zero]
  | succ j ih =>
      have hi := ih (by omega)
      have hb := inverseDescent_rotate_balance hw j hj
      rw [wordCochargeLabel_succ, wordCochargeLabel_succ]
      omega

theorem wordCochargeLabel_head_pos {n a : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (ha : 0 < a) :
    0 < wordCochargeLabel (a :: w) a := by
  have han : a < n := List.mem_range.mp (hw.subset (by simp))
  have h := wordCochargeLabel_rotate_exact hw ha a han
  simp only [if_pos rfl, if_true] at h
  omega

/-- This equality identifies every label, rather than merely its total
sum or the final partition. -/
theorem labelledWord_rotate_exact {n a : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (ha : 0 < a) :
    labelledWord (w ++ [a]) =
      w.map (wordCochargeLabel (a :: w)) ++ [wordCochargeLabel (a :: w) a - 1] := by
  have han : a < n := List.mem_range.mp (hw.subset (by simp))
  have hhead := wordCochargeLabel_rotate_exact hw ha a han
  simp only [if_pos rfl, if_true] at hhead
  have htail : w.map (wordCochargeLabel (w ++ [a])) =
      w.map (wordCochargeLabel (a :: w)) := by
    apply List.map_congr_left
    intro b hb
    have hbn : b < n := List.mem_range.mp (hw.subset (by simp [hb]))
    have hba : b ≠ a := by
      intro h
      subst b
      exact (List.nodup_cons.mp (hw.nodup_iff.mpr List.nodup_range)).1 hb
    have h := wordCochargeLabel_rotate_exact hw ha b hbn
    simpa only [if_neg hba, Nat.add_zero] using h
  simp only [labelledWord, List.map_append, List.map_cons, List.map_nil, htail]
  congr 2
  omega

/-- Actual catabolizability is monotone in this forward ordinary-cyclage
direction.  The reverse implication is not asserted. -/
theorem catWordOutput_standard_rotate_dominates {n a : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (ha : 0 < a)
    {mu nu : YoungDiagram}
    (hold : CatWordOutput (labelledWord (a :: w)) mu)
    (hnew : CatWordOutput (labelledWord (w ++ [a])) nu) : Dominates nu mu := by
  have hp := wordCochargeLabel_head_pos hw ha
  have ho : CatWordOutput
      (wordCochargeLabel (a :: w) a :: w.map (wordCochargeLabel (a :: w))) mu := by
    simpa only [labelledWord, List.map_cons] using hold
  rw [labelledWord_rotate_exact hw ha] at hnew
  exact catWordOutput_rotate_decrement_dominates hp _ ho hnew

def standardWordCocharge (w : List ℕ) : ℕ := (labelledWord w).sum

theorem wordCochargeLabel_le (w : List ℕ) (j : ℕ) :
    wordCochargeLabel w j ≤ j := by
  induction j with
  | zero => simpa only [wordCochargeLabel_zero] using (Nat.le_refl 0)
  | succ j ih =>
      rw [wordCochargeLabel_succ]
      split_ifs <;> omega

theorem sum_map_le_length_mul (w : List ℕ) (f : ℕ → ℕ) (M : ℕ)
    (h : ∀ a ∈ w, f a ≤ M) : (w.map f).sum ≤ w.length * M := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
        one_mul]
      omega

/-- A deliberately simple finite bound, used only as a terminating measure.
It does not replace any sharper cocharge or degree statement in the paper. -/
theorem standardWordCocharge_le_square {n : ℕ} {w : List ℕ}
    (hw : w.Perm (List.range n)) : standardWordCocharge w ≤ n * n := by
  have hlen : w.length = n := hw.length_eq.trans (List.length_range (n := n))
  have h := sum_map_le_length_mul w (wordCochargeLabel w) n (by
    intro a ha
    exact (wordCochargeLabel_le w a).trans
      (Nat.le_of_lt (List.mem_range.mp (hw.subset ha))))
  simpa only [standardWordCocharge, labelledWord, hlen] using h

theorem standardWordCocharge_knuth {n : ℕ} {u v : List ℕ}
    (h : KnuthEquivalent u v) (hu : u.Perm (List.range n)) :
    standardWordCocharge u = standardWordCocharge v := by
  have hh := h.labelledWord [] []
    (by simpa only [List.nil_append, List.append_nil] using hu)
  simp only [List.nil_append, List.append_nil] at hh
  exact hh.perm.sum_eq

/-- The predecessor has exactly one more unit of cocharge.  This makes
the deficit from the finite bound strictly decrease under the reverse
ordinary cycle, without asserting that its width decreases. -/
theorem standardWordCocharge_rotate {n a : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (ha : 0 < a) :
    standardWordCocharge (a :: w) = standardWordCocharge (w ++ [a]) + 1 := by
  have hp := wordCochargeLabel_head_pos hw ha
  rw [standardWordCocharge, standardWordCocharge, labelledWord_rotate_exact hw ha]
  simp only [labelledWord, List.map_cons, List.sum_cons, List.sum_append,
    List.sum_singleton, List.sum_nil, Nat.add_zero]
  omega

theorem standardWordCocharge_deficit_rotate_lt {n a : ℕ} {w : List ℕ}
    (hw : (a :: w).Perm (List.range n)) (ha : 0 < a) :
    n * n - standardWordCocharge (a :: w) <
      n * n - standardWordCocharge (w ++ [a]) := by
  have hsum := standardWordCocharge_rotate hw ha
  have hbound := standardWordCocharge_le_square hw
  omega

end HigherSpecht
end
end CanonicalSource17

section CanonicalSource18
/- Source: HigherSpecht/LascouxProgramCyclePotential.lean -/



/-!
# The genuine bounded cocharge potential after a crystal program

When a program ends in standard content, its output is an actual
permutation word.  Restricted-cycle transport therefore gives the exact
unit change of cocharge and the strict decrease of its bounded deficit.
The corresponding catabolizability comparison uses the actual terminating
cyclic-insertion outputs.  No width-decrease claim is used.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem standardContentWord_perm_range {N : ℕ}
    (u : WordOfContent N (standardContent N)) :
    (List.ofFn u.val).Perm (List.range N) := by
  apply List.perm_iff_count.mpr
  intro a
  change wordContent u.val a = (List.range N).count a
  rw [u.property]
  by_cases ha : a < N
  · rw [standardContent, if_pos ha]
    exact (List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr ha)).symm
  · rw [standardContent, if_neg ha]
    exact (List.count_eq_zero.mpr (by simpa only [List.mem_range] using ha)).symm

theorem CrystalProgram.restrictedCycle_cocharge {K N : ℕ} {c : ℕ → ℕ}
    (P : CrystalProgram K c (standardContent N)) {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (a m : ℕ) (u v : WordOfContent N c)
    (hu : List.ofFn u.val = a :: tableauWord T)
    (hv : List.ofFn v.val = tableauWord T ++ [a])
    (hbound : WordContentBound m (a :: tableauWord T))
    (heast : m ≤ rowInsertColumn a (semistandardRows T)) :
    standardWordCocharge (List.ofFn ((P.embedding N) u).val) =
      standardWordCocharge (List.ofFn ((P.embedding N) v).val) + 1 := by
  obtain ⟨b, U, hpu, hpv, _, _, _, hb0⟩ :=
    P.restrictedCycles N T a m u v hu hv hbound heast
  have hp := standardContentWord_perm_range ((P.embedding N) u)
  rw [hpu] at hp
  have h := standardWordCocharge_rotate hp (Nat.pos_of_ne_zero hb0)
  simpa only [← hpu, ← hpv] using h

theorem CrystalProgram.restrictedCycle_deficit_lt {K N : ℕ} {c : ℕ → ℕ}
    (P : CrystalProgram K c (standardContent N)) {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (a m : ℕ) (u v : WordOfContent N c)
    (hu : List.ofFn u.val = a :: tableauWord T)
    (hv : List.ofFn v.val = tableauWord T ++ [a])
    (hbound : WordContentBound m (a :: tableauWord T))
    (heast : m ≤ rowInsertColumn a (semistandardRows T)) :
    N * N - standardWordCocharge (List.ofFn ((P.embedding N) u).val) <
      N * N - standardWordCocharge (List.ofFn ((P.embedding N) v).val) := by
  have h := P.restrictedCycle_cocharge T a m u v hu hv hbound heast
  have hb := standardWordCocharge_le_square
    (standardContentWord_perm_range ((P.embedding N) u))
  omega

/-- Eligibility transfers from the predecessor back to the current word
in the exact direction needed by reverse-cycle induction. -/
theorem CrystalProgram.restrictedCycle_cat_dominates {K N : ℕ} {c : ℕ → ℕ}
    (P : CrystalProgram K c (standardContent N)) {mu eta theta : YoungDiagram}
    (T : SemistandardYoungTableau mu) (a m : ℕ) (u v : WordOfContent N c)
    (hu : List.ofFn u.val = a :: tableauWord T)
    (hv : List.ofFn v.val = tableauWord T ++ [a])
    (hbound : WordContentBound m (a :: tableauWord T))
    (heast : m ≤ rowInsertColumn a (semistandardRows T))
    (hpre : CatWordOutput (labelledWord (List.ofFn ((P.embedding N) u).val)) eta)
    (hcur : CatWordOutput (labelledWord (List.ofFn ((P.embedding N) v).val)) theta) :
    Dominates theta eta := by
  obtain ⟨b, U, hpu, hpv, _, _, _, hb0⟩ :=
    P.restrictedCycles N T a m u v hu hv hbound heast
  have hp := standardContentWord_perm_range ((P.embedding N) u)
  rw [hpu] at hp hpre
  rw [hpv] at hcur
  exact catWordOutput_standard_rotate_dominates hp (Nat.pos_of_ne_zero hb0) hpre hcur

end HigherSpecht.Lascoux
end
end CanonicalSource18

section CanonicalSource19
/- Source: HigherSpecht/LascouxImageCycleInduction.lean -/



/-!
# The bounded-cocharge induction for the image theorem

This is the cycle-induction component, with its saturated-width base
explicitly separated.  Every nonbase step uses an actual removable corner,
actual reverse row insertion, the actual finite crystal program, and the
proved unit change of standard cocharge.  In particular the width of the
predecessor is not assumed to decrease.  This intermediate theorem does
not by itself supply the saturated base or the final cardinality result.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem catOutput_labelled_knuth_iff {N : ℕ} {u v : List ℕ}
    (h : KnuthEquivalent u v) (hu : u.Perm (List.range N)) (nu : YoungDiagram) :
    CatWordOutput (labelledWord u) nu ↔ CatWordOutput (labelledWord v) nu := by
  have hl := h.labelledWord [] [] (by simpa only [List.nil_append, List.append_nil] using hu)
  simp only [List.nil_append, List.append_nil] at hl
  exact catWordOutput_knuth_iff hl nu

theorem exists_catOutput_labelled {N : ℕ} {w : List ℕ}
    (hw : w.Perm (List.range N)) :
    ∃ nu, CatWordOutput (labelledWord w) nu := by
  let sigma := permutationOfStandardWord w hw
  obtain ⟨nu, hnu⟩ := exists_catTableauOutput (rskPair N sigma).left
  refine ⟨nu, ?_⟩
  have h := (catWordOutput_labelledWord_rsk sigma nu).mpr hnu
  simpa only [sigma, permutationValueWord_permutationOfStandardWord] using h

/-- A genuine reverse-cycle induction.  The premise names only the
separate saturated base; no recurrence, cycle or image transport is
postulated in the induction step. -/
theorem CrystalProgram.image_dominance_of_saturated
    {K N : ℕ} {c : ℕ → ℕ} (P : CrystalProgram K c (standardContent N))
    (lam : YoungDiagram) (m : ℕ) (hc0 : c 0 = m) (hc : ∀ a, c a ≤ m)
    (hbase : ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
      (u : WordOfContent N c), List.ofFn u.val = tableauWord T → mu.rowLen 0 = m →
      ∀ nu, CatWordOutput (labelledWord (List.ofFn (P.embedding N u).val)) nu →
        Dominates nu lam) :
    ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
      (u : WordOfContent N c), List.ofFn u.val = tableauWord T →
      ∀ nu, CatWordOutput (labelledWord (List.ofFn (P.embedding N u).val)) nu →
        Dominates nu lam := by
  have aux : ∀ d : ℕ, ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
      (u : WordOfContent N c), List.ofFn u.val = tableauWord T →
      N * N - standardWordCocharge (List.ofFn (P.embedding N u).val) = d →
      ∀ nu, CatWordOutput (labelledWord (List.ofFn (P.embedding N u).val)) nu →
        Dominates nu lam := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro mu T u hu hd nu hnu
        have hmwidth : m ≤ mu.rowLen 0 := by
          have hzero := contentCells_card_le_width T 0
          rw [← tableauWord_count_eq_contentCells, ← hu] at hzero
          change wordContent u.val 0 ≤ mu.rowLen 0 at hzero
          simpa only [u.property, hc0] using hzero
        by_cases hwidth : mu.rowLen 0 = m
        · exact hbase T u hu hwidth nu hnu
        · have hwide : m < mu.rowLen 0 := by omega
          obtain ⟨rows, a, hrows, hins, heast, hknuth⟩ :=
            exists_tableau_eastCorner_pair T hwide
          let U := tableauOfRows rows hrows
          have hUword : tableauWord U = rowWordRows rows := tableauWord_tableauOfRows rows hrows
          have hkv : KnuthEquivalent (List.ofFn u.val) (tableauWord U ++ [a]) := by
            rw [hu, hUword]
            exact hknuth
          have hvlen : (tableauWord U ++ [a]).length = N := by
            simpa only [List.length_ofFn] using hkv.perm.length_eq.symm
          have hvcount : ∀ b, (tableauWord U ++ [a]).count b = c b := by
            intro b
            exact (hkv.perm.count_eq b).symm.trans (u.property b)
          let v := wordOfContentOfList N c (tableauWord U ++ [a]) hvlen hvcount
          have hv : List.ofFn v.val = tableauWord U ++ [a] :=
            wordOfContentOfList_word N c _ hvlen hvcount
          have hprelen : (a :: tableauWord U).length = N := by
            simpa only [List.length_cons, List.length_append, List.length_singleton,
              List.length_nil, Nat.zero_add] using hvlen
          have hprecount : ∀ b, (a :: tableauWord U).count b = c b := by
            intro b
            simpa only [List.count_cons, List.count_append, List.count_singleton,
              List.count_nil, Nat.zero_add, Nat.add_comm]
              using hvcount b
          let vpre := wordOfContentOfList N c (a :: tableauWord U) hprelen hprecount
          have hvpre : List.ofFn vpre.val = a :: tableauWord U :=
            wordOfContentOfList_word N c _ hprelen hprecount
          have hbound : WordContentBound m (a :: tableauWord U) := by
            intro b
            rw [hprecount]
            exact hc b
          have heast' : m ≤ rowInsertColumn a (semistandardRows U) := by
            rw [semistandardRows_tableauOfRows]
            exact heast
          let Tpre := insertionTableau (a :: tableauWord U)
          have hnormal : KnuthEquivalent (a :: tableauWord U) (tableauWord Tpre) :=
            knuth_insertionTableau _
          have hTprelen : (tableauWord Tpre).length = N := hnormal.perm.length_eq.symm.trans hprelen
          have hTprecount : ∀ b, (tableauWord Tpre).count b = c b := by
            intro b
            exact (hnormal.perm.count_eq b).symm.trans (hprecount b)
          let upre := wordOfContentOfList N c (tableauWord Tpre) hTprelen hTprecount
          have hupre : List.ofFn upre.val = tableauWord Tpre :=
            wordOfContentOfList_word N c _ hTprelen hTprecount
          have hcur : KnuthEquivalent (List.ofFn (P.embedding N u).val)
              (List.ofFn (P.embedding N v).val) := by
            apply ((P.properties N).knuth u v).mpr
            rw [hv]
            exact hkv
          have hpred : KnuthEquivalent (List.ofFn (P.embedding N vpre).val)
              (List.ofFn (P.embedding N upre).val) := by
            apply ((P.properties N).knuth vpre upre).mpr
            rw [hvpre, hupre]
            exact hnormal
          have hpotcur := standardWordCocharge_knuth hcur
            (standardContentWord_perm_range (P.embedding N u))
          have hpotpre := standardWordCocharge_knuth hpred
            (standardContentWord_perm_range (P.embedding N vpre))
          have hlt := P.restrictedCycle_deficit_lt U a m vpre v hvpre hv hbound heast'
          rw [hpotpre, ← hpotcur, hd] at hlt
          obtain ⟨theta, htheta⟩ := exists_catOutput_labelled
            (standardContentWord_perm_range (P.embedding N upre))
          have hthetaDom := ih _ hlt Tpre upre hupre rfl theta htheta
          have hthetaPre : CatWordOutput (labelledWord (List.ofFn (P.embedding N vpre).val)) theta :=
            (catOutput_labelled_knuth_iff hpred
              (standardContentWord_perm_range (P.embedding N vpre)) theta).mpr htheta
          have hnuCur : CatWordOutput (labelledWord (List.ofFn (P.embedding N v).val)) nu :=
            (catOutput_labelled_knuth_iff hcur
              (standardContentWord_perm_range (P.embedding N u)) nu).mp hnu
          exact (P.restrictedCycle_cat_dominates U a m vpre v hvpre hv hbound heast'
            hthetaPre hnuCur).trans hthetaDom
  intro mu T u hu nu hnu
  exact aux _ T u hu rfl nu hnu

end HigherSpecht.Lascoux
end
end CanonicalSource19

section CanonicalSource20
/- Source: HigherSpecht/LascouxPartitionImage.lean -/



/-!
# The actual partition-content balancing image lies in catabolizability

The outer induction removes the first row of the content partition.
At saturated width, the explicit sweep/neutral-tail/unsweep/shift/zero-row
program gives a genuine recursive output and path uniqueness identifies
it with the original program.  At larger width, actual reverse insertion
decreases the bounded standard-cocharge deficit.  Thus every program
endpoint used here has a complete source construction; no image theorem
is introduced as an assumption.

This is the fixed-content inclusion required by the later Griffin count.
It is distinct from the additional battery and boost reconstruction that
are needed for arbitrary `n >= |lambda|` and the full Griffin index set.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

theorem CrystalProgram.partition_image_dominates
    (lam : YoungDiagram) {K : ℕ}
    (P : CrystalProgram K lam.rowLen (standardContent lam.card))
    {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (u : WordOfContent lam.card lam.rowLen) (hu : List.ofFn u.val = tableauWord T)
    (nu : YoungDiagram)
    (hnu : CatWordOutput (labelledWord (List.ofFn (P.embedding lam.card u).val)) nu) :
    Dominates nu lam := by
  have aux : ∀ N : ℕ, ∀ lam : YoungDiagram, lam.card = N →
      ∀ K : ℕ, ∀ P : CrystalProgram K lam.rowLen (standardContent N),
      ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
        (u : WordOfContent N lam.rowLen), List.ofFn u.val = tableauWord T →
      ∀ nu, CatWordOutput (labelledWord (List.ofFn (P.embedding N u).val)) nu →
        Dominates nu lam := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro lam hcard K P
        by_cases hN : N = 0
        · intro T u hu nu hnu r
          have hz : ∀ i, lam.rowLen i = 0 := by
            intro i
            exact partitionContent_support lam i (by omega)
          simp only [hz, Finset.sum_const_zero]
          exact Nat.zero_le _
        · have hlam : 0 < lam.card := by omega
          let m := lam.rowLen 0
          have hm : 0 < m := partition_width_pos_of_card_pos lam hlam
          apply P.image_dominance_of_saturated lam m rfl
            (fun a => lam.rowLen_anti 0 a (Nat.zero_le a))
          intro mu T u hu hwidth nu hnu
          let M := (firstRowTail lam).card
          have hMlt : M < N := by
            exact (firstRowTail_card_lt lam hlam).trans_eq hcard
          have hNm : N = M + m := by
            exact hcard.symm.trans (firstRowTail_card_add_width lam).symm
          have hcard' : lam.card = M + m := hcard.trans hNm
          clear hcard
          subst N
          have hTcard : mu.card = M + m := by
            have hlen := congrArg List.length hu
            simpa only [List.length_ofFn, tableauWord_length] using hlen.symm
          have htailCard : (firstRowTail mu).card = M := by
            have h := firstRowTail_card_add_width mu
            rw [hwidth, hTcard] at h
            omega
          have hs : (contentCells T 0).card = mu.rowLen 0 := by
            rw [← tableauWord_count_eq_contentCells, ← hu]
            exact (u.property 0).trans hwidth.symm
          have hvlen : (tableauWord (firstRowTailPred T)).length = M := by
            rw [tableauWord_length, htailCard]
          have hvcount : ∀ a, (tableauWord (firstRowTailPred T)).count a =
              (firstRowTail lam).rowLen a := by
            intro a
            rw [tableauWord_count_eq_contentCells, firstRowTailPred_content T hs,
              ← tableauWord_count_eq_contentCells, ← hu, firstRowTail_rowLen]
            exact u.property (a + 1)
          let v := wordOfContentOfList M (firstRowTail lam).rowLen
            (tableauWord (firstRowTailPred T)) hvlen hvcount
          have hv : List.ofFn v.val = tableauWord (firstRowTailPred T) :=
            wordOfContentOfList_word M _ _ hvlen hvcount
          let Ptail := partitionBalancingProgram (firstRowTail lam)
          obtain ⟨Q, hQ⟩ := (Ptail.properties M).shape (firstRowTailPred T) v hv
          obtain ⟨theta, htheta⟩ := exists_catOutput_labelled
            (standardContentWord_perm_range (Ptail.embedding M v))
          have htailDom : Dominates theta (firstRowTail lam) :=
            ih M hMlt (firstRowTail lam) rfl M Ptail (firstRowTailPred T) v hv theta htheta
          have htailContent : firstContentTail M lam.rowLen = (firstRowTail lam).rowLen :=
            firstContentTail_partition lam
          let Ptail' := Ptail.castContents htailContent.symm rfl
          let v' := castContentWord htailContent.symm v
          have hv' : List.ofFn v'.val = tableauWord (firstRowTailPred T) := by
            rw [castContentWord_val]
            exact hv
          have hQ' : List.ofFn (Ptail'.embedding M v').val = tableauWord Q := by
            rw [CrystalProgram.embedding_castContents_word Ptail htailContent.symm rfl v v'
              (castContentWord_val htailContent.symm v).symm]
            exact hQ
          obtain ⟨R, hR⟩ := exists_saturated_standardProgram M m hm lam.rowLen rfl
            (partitionContent_tail_support lam) Ptail' T hs hwidth u hu v' hv' Q hQ'
          have hunique := crystal_balancing_unique_on_partition lam (standardContent (M + m))
          rw [hcard'] at hunique
          have heq : P.embedding (M + m) u = R.embedding (M + m) u :=
            hunique (P.embedding (M + m)) (R.embedding (M + m))
              (P.properties (M + m)) (R.properties (M + m)) T u hu
          rw [heq, hR] at hnu
          have hQperm : (tableauWord Q).Perm (List.range M) := by
            rw [← hQ]
            exact standardContentWord_perm_range (Ptail.embedding M v)
          have hthetaQ : CatWordOutput (labelledWord (tableauWord Q)) theta := by
            rw [← hQ]
            exact htheta
          have hrows := catWordOutput_glued_rows Q hQperm hm hwidth hnu hthetaQ
          exact dominates_of_glued_rows hrows htailDom
  exact aux lam.card lam rfl K P T u hu nu hnu

/-- The chosen balancing map is an actual injective word map, and every
semistandard row word in its literal partition content has an actual
terminating output dominating that partition. -/
theorem partitionBalancingProgram_image (lam : YoungDiagram)
    {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (u : WordOfContent lam.card lam.rowLen) (hu : List.ofFn u.val = tableauWord T) :
    ∃ nu, CatWordOutput
      (labelledWord (List.ofFn ((partitionBalancingProgram lam).embedding lam.card u).val)) nu ∧
        Dominates nu lam := by
  obtain ⟨nu, hnu⟩ := exists_catOutput_labelled
    (standardContentWord_perm_range ((partitionBalancingProgram lam).embedding lam.card u))
  exact ⟨nu, hnu, (partitionBalancingProgram lam).partition_image_dominates lam T u hu nu hnu⟩

/-- The fixed-content inclusion applies to every literal word.  Its
actual insertion tableau supplies the row-reading representative, and
the genuine program and cocharge maps preserve its Knuth class. -/
theorem CrystalProgram.partition_word_image_dominates
    (lam : YoungDiagram) {K : ℕ}
    (P : CrystalProgram K lam.rowLen (standardContent lam.card))
    (u : WordOfContent lam.card lam.rowLen) (nu : YoungDiagram)
    (hnu : CatWordOutput (labelledWord (List.ofFn (P.embedding lam.card u).val)) nu) :
    Dominates nu lam := by
  let T := insertionTableau (List.ofFn u.val)
  have hk : KnuthEquivalent (List.ofFn u.val) (tableauWord T) := knuth_insertionTableau _
  have hlen : (tableauWord T).length = lam.card := by
    simpa only [List.length_ofFn] using hk.perm.length_eq.symm
  have hcount : ∀ a, (tableauWord T).count a = lam.rowLen a := by
    intro a
    exact (hk.perm.count_eq a).symm.trans (u.property a)
  let v := wordOfContentOfList lam.card lam.rowLen (tableauWord T) hlen hcount
  have hv : List.ofFn v.val = tableauWord T := wordOfContentOfList_word _ _ _ hlen hcount
  have hmap : KnuthEquivalent (List.ofFn (P.embedding lam.card u).val)
      (List.ofFn (P.embedding lam.card v).val) := by
    apply ((P.properties lam.card).knuth u v).mpr
    rw [hv]
    exact hk
  have hvnu := (catOutput_labelled_knuth_iff hmap
    (standardContentWord_perm_range (P.embedding lam.card u)) nu).mp hnu
  exact P.partition_image_dominates lam T v hv nu hvnu

theorem partitionBalancingProgram_word_image (lam : YoungDiagram)
    (u : WordOfContent lam.card lam.rowLen) :
    ∃ nu, CatWordOutput
      (labelledWord (List.ofFn ((partitionBalancingProgram lam).embedding lam.card u).val)) nu ∧
        Dominates nu lam := by
  obtain ⟨nu, hnu⟩ := exists_catOutput_labelled
    (standardContentWord_perm_range ((partitionBalancingProgram lam).embedding lam.card u))
  exact ⟨nu, hnu, (partitionBalancingProgram lam).partition_word_image_dominates lam u nu hnu⟩

end HigherSpecht.Lascoux
end
end CanonicalSource20

section CanonicalSource21
/- Source: HigherSpecht/StandardCochargeInjectivity.lean -/



/-!
# A standard permutation is recovered from its literal cocharge word

Stable sorting recovers the original labels because cocharge is monotone
in the label and equal-cocharge labels occur in increasing positional
order.  We instantiate the already defined bounded-code inverse with
zero boosts.  This is the injectivity needed after discarding a battery
whose cocharge suffix is proved fixed.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

def zeroBoostCode {N : ℕ} (sigma : Equiv.Perm (Fin N)) : BoundedCochargeCode N (N + 1) where
  permutation := sigma
  boost := fun _ => 0
  boost_mono := fun _ _ _ => le_rfl
  bound i := by
    have h := wordCochargeLabel_le (permutationValueWord sigma) i.val
    change wordCochargeLabel (permutationValueWord sigma) i.val + 0 < N + 1
    omega

theorem decode_zeroBoostCode_word {N : ℕ} (sigma : Equiv.Perm (Fin N)) :
    List.ofFn (fun i => (decodeBoundedWord (zeroBoostCode sigma) i).val) =
      labelledWord (permutationValueWord sigma) := by
  simp only [decodeBoundedWord, zeroBoostCode, Nat.add_zero, labelledWord,
    permutationValueWord, List.map_ofFn, permutationCocharge, Function.comp_def]

theorem labelled_permutationWord_injective {N : ℕ}
    {sigma tau : Equiv.Perm (Fin N)}
    (h : labelledWord (permutationValueWord sigma) =
      labelledWord (permutationValueWord tau)) : sigma = tau := by
  have hd : decodeBoundedWord (zeroBoostCode sigma) =
      decodeBoundedWord (zeroBoostCode tau) := by
    have heq : List.ofFn (fun i => (decodeBoundedWord (zeroBoostCode sigma) i).val) =
        List.ofFn (fun i => (decodeBoundedWord (zeroBoostCode tau) i).val) := by
      rw [decode_zeroBoostCode_word, decode_zeroBoostCode_word]
      exact h
    have heq' := List.ofFn_inj.mp heq
    funext i
    exact Fin.ext (congrFun heq' i)
  have hc := congrArg encodeBoundedWord hd
  rw [encode_decode_boundedWord, encode_decode_boundedWord] at hc
  exact congrArg BoundedCochargeCode.permutation hc

theorem labelledWord_injective_of_standard {N : ℕ} {u v : List ℕ}
    (hu : u.Perm (List.range N)) (hv : v.Perm (List.range N))
    (h : labelledWord u = labelledWord v) : u = v := by
  let sigma := permutationOfStandardWord u hu
  let tau := permutationOfStandardWord v hv
  have hsigma := permutationValueWord_permutationOfStandardWord u hu
  have htau := permutationValueWord_permutationOfStandardWord v hv
  have hp : sigma = tau := labelled_permutationWord_injective (by
    rw [hsigma, htau]
    exact h)
  exact hsigma.symm.trans ((congrArg permutationValueWord hp).trans htau)

end HigherSpecht
end
end CanonicalSource21

section CanonicalSource22
/- Source: HigherSpecht/BatteryBalancedOutput.lean -/



/-!
# Actual balanced battery output and recovery from its device

The fixed-content embedding is applied to the concrete appended word.
Its output is a standard word whose actual catabolism dominates the
augmented partition. The tableau-suffix theorem and the literal first-pass
rigidity theorem force its entire battery cocharge suffix to be fixed.
Consequently the remaining device cocharge word recovers the full standard
output and hence the original input word.

Eligibility of the device for the Griffin index set is a separate column
stripping theorem; it is not assumed or built into these definitions.
-/

noncomputable section
open Finset
open scoped Classical

namespace HigherSpecht.Lascoux

def superstandardBatteryWord (h d : ℕ) : List ℕ :=
  (descendingRows h).flatMap (fun r => List.replicate d r)

theorem superstandardBatteryWord_length (h d : ℕ) :
    (superstandardBatteryWord h d).length = h * d := by
  induction h with
  | zero => simp [superstandardBatteryWord, descendingRows]
  | succ h ih =>
      simp only [superstandardBatteryWord, descendingRows, List.flatMap_cons,
        List.length_append, List.length_replicate, Nat.add_mul, one_mul] at ih ⊢
      omega

theorem battery_word_eq_superstandard {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d))
    (hT : ∀ r j, r < h → j < d → T r j = r) :
    tableauWord T = superstandardBatteryWord h d := by
  rw [← tableauWord_withHeight T h (batteryRectangle_height_le h d)]
  unfold superstandardBatteryWord
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r hr
  have hrh := mem_descendingRows.mp hr
  rw [batteryRowWord_eq_ofFn T ⟨r, hrh⟩]
  have heq : (fun j : Fin d => T r j) = fun _ => r := by
    funext j
    exact hT r j hrh j.isLt
  rw [heq, List.ofFn_const]

theorem cat_height_le_of_dominates {w : List ℕ} {nu rho : YoungDiagram}
    (hout : CatWordOutput w nu) (hcard : rho.card = w.length)
    (hdom : Dominates nu rho) {s : ℕ} (hheight : rho.colLen 0 ≤ s) :
    nu.colLen 0 ≤ s := by
  have hsum := hdom s
  rw [← YoungDiagram.card_eq_sum_range_rowLen rho hheight, hcard,
    ← catWordOutput_card hout, YoungDiagram.sum_range_rowLen_eq_card_filter_fst] at hsum
  have heq : (nu.cells.filter (fun c => c.1 < s)) = nu.cells :=
    eq_of_subset_of_card_le (filter_subset _ _) hsum
  by_contra h
  have hc : (s, 0) ∈ nu.cells :=
    YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge h)
  have hh : (s, 0) ∈ nu.cells.filter (fun c => c.1 < s) := by rwa [heq]
  exact (Nat.lt_irrefl s) (mem_filter.mp hh).2

def balancedBatteryWord {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    WordOfContent (batteryContentShape lam s (n - lam.card)).card
      (standardContent (batteryContentShape lam s (n - lam.card)).card) :=
  (partitionBalancingProgram (batteryContentShape lam s (n - lam.card))).embedding _
    (batteryInputWord u hs hheight)

def balancedBatteryList {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) : List ℕ :=
  List.ofFn (balancedBatteryWord u hs hheight).val

theorem balancedBatteryList_standard {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (balancedBatteryList u hs hheight).Perm
      (List.range (batteryContentShape lam s (n - lam.card)).card) :=
  standardContentWord_perm_range (balancedBatteryWord u hs hheight)

theorem balancedBatteryList_output {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ∃ nu, CatWordOutput (labelledWord (balancedBatteryList u hs hheight)) nu ∧
      Dominates nu (batteryContentShape lam s (n - lam.card)) ∧ nu.colLen 0 ≤ s := by
  obtain ⟨nu, hnu, hdom⟩ := partitionBalancingProgram_word_image
    (batteryContentShape lam s (n - lam.card)) (batteryInputWord u hs hheight)
  refine ⟨nu, hnu, hdom, ?_⟩
  apply cat_height_le_of_dominates hnu _ hdom (batteryContentShape_height_le _ _ _)
  simp only [labelledWord, List.length_map, List.length_ofFn]

theorem balancedBatteryList_suffix {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ∃ (pre : List ℕ) (T : SemistandardYoungTableau (batteryRectangle (s - 1) (n - lam.card))),
      pre.length = n ∧ balancedBatteryList u hs hheight = pre ++ tableauWord T := by
  obtain ⟨pre, T, hlen, hword⟩ :=
    (partitionBalancingProgram (batteryContentShape lam s (n - lam.card))).tableauSuffix
      _ (inputBattery u hheight) (contentWordNatList u) (batteryInputWord u hs hheight)
      (batteryInputWord_word u hs hheight)
  exact ⟨pre, T, hlen.trans (contentWordNatList_length u), hword⟩

theorem balancedBatteryList_labelled_suffix {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    labelledWord (balancedBatteryList u hs hheight) =
      (labelledWord (balancedBatteryList u hs hheight)).take n ++
        superstandardBatteryWord (s - 1) (n - lam.card) := by
  obtain ⟨pre, T, hlen, hword⟩ := balancedBatteryList_suffix u hs hheight
  have hperm : (pre ++ tableauWord T).Perm
      (List.range (batteryContentShape lam s (n - lam.card)).card) := by
    rw [← hword]
    exact balancedBatteryList_standard u hs hheight
  let C := suffixCochargeTableau T pre hperm
  let prefixCC := pre.map (wordCochargeLabel (pre ++ tableauWord T))
  have hcc : labelledWord (balancedBatteryList u hs hheight) = prefixCC ++ tableauWord C := by
    rw [hword]
    exact labelledWord_tableau_suffix T pre hperm
  obtain ⟨nu, hnu, hdom, hnuheight⟩ := balancedBatteryList_output u hs hheight
  have hheight' : nu.colLen 0 ≤ (s - 1) + 1 := by omega
  have hC : tableauWord C = superstandardBatteryWord (s - 1) (n - lam.card) := by
    apply battery_word_eq_superstandard C
    intro r j hr hj
    exact battery_superstandard_of_cat_height C prefixCC (hcc ▸ hnu) hheight' r j hr hj
  have hprefix : prefixCC.length = n := by simp only [prefixCC, List.length_map, hlen]
  rw [hcc, hC]
  rw [← hprefix, List.take_left]

theorem balancedBatteryList_labelled_bound {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    {a : ℕ} (ha : a ∈ labelledWord (balancedBatteryList u hs hheight)) : a < s := by
  obtain ⟨nu, hnu, hdom, hheight'⟩ := balancedBatteryList_output u hs hheight
  exact (catWordOutput_letter_lt_height hnu ha).trans_le hheight'

theorem balancedBatteryList_length_ge {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    n ≤ (batteryContentShape lam s (n - lam.card)).card := by
  rw [batteryContentShape_card_eq_inputLength u hs hheight]
  omega

def batteryDeviceWord {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) : Fin n → Fin s :=
  fun i =>
    let j := Fin.castLE (balancedBatteryList_length_ge u hs hheight) i
    ⟨wordCochargeLabel (balancedBatteryList u hs hheight)
      ((balancedBatteryWord u hs hheight).val j), by
      apply balancedBatteryList_labelled_bound u hs hheight
      exact List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩⟩

theorem batteryDeviceWord_list {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    List.ofFn (fun i => (batteryDeviceWord u hs hheight i).val) =
      (labelledWord (balancedBatteryList u hs hheight)).take n := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, labelledWord, List.length_map,
      balancedBatteryList, List.length_ofFn,
      min_eq_left (balancedBatteryList_length_ge u hs hheight)]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_take, labelledWord, List.getElem_map,
      balancedBatteryList, List.getElem_ofFn, batteryDeviceWord, Fin.castLE_mk]

theorem batteryDeviceWord_injective {n s : ℕ} {lam : YoungDiagram}
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Function.Injective (fun u : ContentWord n lam s => batteryDeviceWord u hs hheight) := by
  intro u v huv
  change batteryDeviceWord u hs hheight = batteryDeviceWord v hs hheight at huv
  have hprefix : (labelledWord (balancedBatteryList u hs hheight)).take n =
      (labelledWord (balancedBatteryList v hs hheight)).take n := by
    rw [← batteryDeviceWord_list u hs hheight, ← batteryDeviceWord_list v hs hheight, huv]
  have hlabels : labelledWord (balancedBatteryList u hs hheight) =
      labelledWord (balancedBatteryList v hs hheight) := by
    rw [balancedBatteryList_labelled_suffix u hs hheight,
      balancedBatteryList_labelled_suffix v hs hheight, hprefix]
  have hwords := labelledWord_injective_of_standard
    (balancedBatteryList_standard u hs hheight) (balancedBatteryList_standard v hs hheight) hlabels
  have hbalanced : balancedBatteryWord u hs hheight = balancedBatteryWord v hs hheight :=
    Subtype.ext (List.ofFn_inj.mp hwords)
  have hinput : batteryInputWord u hs hheight = batteryInputWord v hs hheight :=
    ((partitionBalancingProgram (batteryContentShape lam s (n - lam.card))).embedding _).injective
      hbalanced
  exact (batteryInputEmbedding n lam s hs hheight).injective hinput

/-- This is the actual bounded device word, before the separately proved
column-stripping argument establishes its Griffin eligibility. -/
def batteryDeviceEmbedding (n : ℕ) (lam : YoungDiagram) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ContentWord n lam s ↪ (Fin n → Fin s) where
  toFun u := batteryDeviceWord u hs hheight
  inj' := batteryDeviceWord_injective hs hheight

end HigherSpecht.Lascoux
end
end CanonicalSource22

section CanonicalSource23
/- Source: HigherSpecht/BatteryLabeledProvenance.lean -/



/-!
# Battery positions in the actual terminal insertion filling

The original row-major battery tokens are accepted during scan zero. The
accepted-record list is monotone during every later step, so extraction of
the terminal filling retains the exact token-to-cell assignments. The input
prefix condition is then calculated from the literal superstandard suffix.
-/

noncomputable section
open TauCeti Finset Function
open scoped Classical

namespace HigherSpecht

def rowMajorAccepted {n : ℕ} (d k : ℕ) (hk : k ≤ n) : List (AcceptedToken n) :=
  List.ofFn (fun i : Fin k =>
    ((⟨Fin.castLE hk i, 0⟩ : CyclingToken n), (i.val / d, i.val % d)))

def rowMajorState {n : ℕ} (d k : ℕ) (hk : k ≤ n) : LabeledCatState n :=
  ⟨(initialCyclingQueue n).drop k, rowMajorPrefix d k, rowMajorAccepted d k hk⟩

 theorem rowMajorAccepted_succ {n : ℕ} (d k : ℕ) (hk : k + 1 ≤ n) :
    rowMajorAccepted d (k + 1) hk =
      rowMajorAccepted d k (by omega) ++
        [((⟨⟨k, by omega⟩, 0⟩ : CyclingToken n), (k / d, k % d))] := by
  rw [rowMajorAccepted, List.ofFn_succ_last]
  rfl

 theorem rowMajorState_step {n : ℕ} (a : Fin n → ℕ) {d k : ℕ}
    (hd : 0 < d) (hk : k + 1 ≤ n)
    (ha : a ⟨k, by omega⟩ = k / d) :
    labeledCatStep a (rowMajorState d k (by omega)) = rowMajorState d (k + 1) hk := by
  have hq : (initialCyclingQueue n).drop k =
      (⟨⟨k, by omega⟩, 0⟩ : CyclingToken n) :: (initialCyclingQueue n).drop (k + 1) := by
    have hkl : k < (initialCyclingQueue n).length := by
      simp only [initialCyclingQueue, List.length_ofFn]
      omega
    simpa only [initialCyclingQueue, List.getElem_ofFn] using
      (List.drop_eq_getElem_cons (l := initialCyclingQueue n) hkl)
  change labeledCatStep a
    ⟨(initialCyclingQueue n).drop k, rowMajorPrefix d k, rowMajorAccepted d k (by omega)⟩ = _
  rw [hq]
  simp only [labeledCatStep, tokenValue, Nat.add_zero, ha, rowMajorPrefix_rowLen_next hd]
  rw [if_pos (rowMajorPrefix_next_addable hd k), rowMajorPrefix_addCell hd k]
  unfold rowMajorState
  congr 1
  exact (rowMajorAccepted_succ d k hk).symm

/-- All the specified initial tokens are accepted in order, with zero
rejections. This equality is about the executable labeled algorithm. -/
theorem labeledCatRun_rowMajorPrefix {n B d : ℕ} (a : Fin n → ℕ)
    (hd : 0 < d) (hB : B ≤ n)
    (ha : ∀ i : Fin B, a (Fin.castLE hB i) = i.val / d)
    (k : ℕ) (hk : k ≤ B) :
    labeledCatRun a k (labeledInitial n) = rowMajorState d k (hk.trans hB) := by
  induction k with
  | zero =>
      simp only [labeledCatRun, Function.iterate_zero, id_eq, rowMajorState,
        List.drop_zero, rowMajorPrefix_zero, rowMajorAccepted, List.ofFn_zero,
        labeledInitial]
  | succ k ih =>
      rw [labeledCatRun, Function.iterate_succ_apply']
      change labeledCatStep a (labeledCatRun a k (labeledInitial n)) = _
      rw [ih (by omega)]
      apply rowMajorState_step a hd (hk.trans hB)
      exact ha ⟨k, by omega⟩

 theorem labeledCatStep_accepted_subset {n : ℕ} (a : Fin n → ℕ)
    (s : LabeledCatState n) : s.accepted ⊆ (labeledCatStep a s).accepted := by
  rcases s with ⟨q, mu, acc⟩
  cases q with
  | nil => exact List.Subset.refl _
  | cons t q =>
      simp only [labeledCatStep]
      split_ifs
      · exact List.subset_append_left _ _
      · exact List.Subset.refl _

 theorem labeledCatRun_accepted_subset {n : ℕ} (a : Fin n → ℕ) (N : ℕ)
    (s : LabeledCatState n) : s.accepted ⊆ (labeledCatRun a N s).accepted := by
  induction N with
  | zero => exact List.Subset.refl _
  | succ N ih =>
      rw [labeledCatRun, Function.iterate_succ_apply']
      exact List.Subset.trans ih (labeledCatStep_accepted_subset a _)

 theorem labeledCatRun_add {n : ℕ} (a : Fin n → ℕ) (m k : ℕ)
    (s : LabeledCatState n) :
    labeledCatRun a (m + k) s = labeledCatRun a m (labeledCatRun a k s) :=
  Function.iterate_add_apply (labeledCatStep a) m k s

/-- The exact accepted token identities survive to the extracted terminal
scheduled filling, including their actual zero visit counts. -/
theorem exists_scheduledFilling_with_rowMajorPrefix {n B d : ℕ}
    (a : Fin n → ℕ) (hd : 0 < d) (hB : B ≤ n)
    (ha : ∀ i : Fin B, a (Fin.castLE hB i) = i.val / d)
    {mu : YoungDiagram} (hout : CatWordOutput (List.ofFn a).reverse mu) :
    ∃ F : ScheduledFilling a, F.shape = mu ∧
      ∀ i : Fin B,
        (F.token.symm (Fin.castLE hB i)).val = (i.val / d, i.val % d) ∧
        F.visit (Fin.castLE hB i) = 0 := by
  obtain ⟨N, hN⟩ := hout
  let s := labeledCatRun a (N + B) (labeledInitial n)
  have hforget : labeledForget a s = (⟨[], mu⟩ : CatState) := by
    dsimp only [s]
    rw [labeledForget_run, labeledForget_initial, Nat.add_comm N B,
      catRun_add, hN, catRun_empty]
  have hnil : s.pending = [] := by
    have hw := congrArg CatState.word hforget
    simpa only [labeledForget, List.reverse_eq_nil_iff, List.map_eq_nil_iff] using hw
  have hshape : s.shape = mu := congrArg CatState.shape hforget
  have hinv := (labeledCatRun_lazy a (N + B)).invariants
  let C : CompleteInsertion a := ⟨s, hinv.1, hnil⟩
  let F := C.scheduledFilling hinv.2
  refine ⟨F, hshape, ?_⟩
  intro i
  have hsub : rowMajorAccepted d B hB ⊆ s.accepted := by
    have hh := labeledCatRun_accepted_subset a N (labeledCatRun a B (labeledInitial n))
    rw [labeledCatRun_rowMajorPrefix a hd hB ha B le_rfl] at hh
    simpa only [s, labeledCatRun_add, labeledCatRun_rowMajorPrefix a hd hB ha B le_rfl,
      rowMajorState] using hh
  have hmem : ((⟨Fin.castLE hB i, 0⟩ : CyclingToken n), (i.val / d, i.val % d)) ∈
      s.accepted := hsub (List.mem_ofFn.mpr ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
  have ht : C.token j = (⟨Fin.castLE hB i, 0⟩ : CyclingToken n) := congrArg Prod.fst hj
  have hc : (C.cell j).val = (i.val / d, i.val % d) := congrArg Prod.snd hj
  have hp : (C.token j).position = Fin.castLE hB i := congrArg CyclingToken.position ht
  constructor
  · change (C.filling.symm (Fin.castLE hB i)).val = _
    rw [← hp, C.filling_symm_position]
    exact hc
  · change C.rejection (Fin.castLE hB i) = 0
    rw [← hp, C.rejection_position]
    exact congrArg CyclingToken.round ht

namespace Lascoux

/-- The reverse reading of the literal superstandard rectangle has label
`i / d` at its `i`th scanning position, including repeated row entries. -/
theorem superstandardBatteryWord_reverse (h d : ℕ) :
    (superstandardBatteryWord h d).reverse =
      List.ofFn (fun i : Fin (h * d) => i.val / d) := by
  by_cases hd : d = 0
  · subst d
    have hn : superstandardBatteryWord h 0 = [] := by
      apply List.eq_nil_iff_length_eq_zero.mpr
      rw [superstandardBatteryWord_length, Nat.mul_zero]
    simp only [hn, List.reverse_nil, Nat.mul_zero, List.ofFn_zero]
  · have hdp : 0 < d := Nat.pos_of_ne_zero hd
    induction h with
    | zero => simp [superstandardBatteryWord, descendingRows]
    | succ h ih =>
        rw [superstandardBatteryWord, descendingRows, List.flatMap_cons,
          List.reverse_append, List.reverse_replicate]
        change (superstandardBatteryWord h d).reverse ++ List.replicate d h = _
        rw [ih, Nat.succ_mul, List.ofFn_add]
        congr 1
        calc
          List.replicate d h = List.ofFn (fun _ : Fin d => h) := (List.ofFn_const d h).symm
          _ = List.ofFn (fun i : Fin d => (i.natAdd (h * d)).val / d) := by
            congr 1
            funext i
            change h = (h * d + i.val) / d
            rw [Nat.add_comm (h * d), Nat.add_mul_div_right _ _ hdp,
              Nat.div_eq_of_lt i.isLt, Nat.zero_add]

/-- This theorem derives the scan-prefix law from the supplied literal word
identity; it does not assume a separate placement property of the battery. -/
theorem exists_scheduledFilling_of_superstandard_suffix {M h d : ℕ}
    (w : Fin M → ℕ) (device : List ℕ)
    (hword : List.ofFn w = device ++ superstandardBatteryWord h d)
    {mu : YoungDiagram} (hout : CatWordOutput (List.ofFn w) mu) :
    ∃ F : ScheduledFilling (fun i => w (Fin.rev i)), F.shape = mu ∧
      ∀ (r j : ℕ) (hr : r < h) (hj : j < d),
        ∃ hi : r * d + j < M,
          (F.token.symm ⟨r * d + j, hi⟩).val = (r, j) ∧
          F.visit ⟨r * d + j, hi⟩ = 0 ∧
          w (Fin.rev ⟨r * d + j, hi⟩) = r := by
  have hlen := congrArg List.length hword
  simp only [List.length_ofFn, List.length_append, superstandardBatteryWord_length] at hlen
  have hB : h * d ≤ M := by omega
  by_cases hd : d = 0
  · obtain ⟨F, hF⟩ := exists_scheduledFilling_of_wordOutput hout
    refine ⟨F, hF, ?_⟩
    intro r j hr hj
    omega
  · let a : Fin M → ℕ := fun i => w (Fin.rev i)
    have hreading : List.ofFn a =
        List.ofFn (fun i : Fin (h * d) => i.val / d) ++ device.reverse := by
      have hh := congrArg List.reverse (ofFn_reverse_labels w)
      simp only [List.reverse_reverse] at hh
      change List.ofFn a = (List.ofFn w).reverse at hh
      rw [hh, hword, List.reverse_append, superstandardBatteryWord_reverse]
    have ha : ∀ i : Fin (h * d), a (Fin.castLE hB i) = i.val / d := by
      intro i
      have hh := congrArg (fun l : List ℕ => l[i.val]?) hreading
      rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt)] at hh
      have hcast : Fin.castLE hB i = ⟨i.val, i.isLt.trans_le hB⟩ := by
        apply Fin.ext
        exact Fin.coe_castLE hB i
      rw [hcast]
      simpa only [List.getElem?_ofFn, dif_pos (i.isLt.trans_le hB), dif_pos i.isLt,
        Option.some.injEq] using hh
    have houta : CatWordOutput (List.ofFn a).reverse mu := by
      rw [show (List.ofFn a).reverse = List.ofFn w from ofFn_reverse_labels w]
      exact hout
    obtain ⟨F, hF, hassign⟩ := exists_scheduledFilling_with_rowMajorPrefix
      a (Nat.pos_of_ne_zero hd) hB ha houta
    refine ⟨F, hF, ?_⟩
    intro r j hr hj
    have hkey : r * d + j < h * d := by
      have hm := Nat.mul_le_mul_right d (show r + 1 ≤ h by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    let i : Fin (h * d) := ⟨r * d + j, hkey⟩
    have hdiv : i.val / d = r := by
      change (r * d + j) / d = r
      rw [Nat.add_comm (r * d), Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero hd),
        Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : i.val % d = j := by
      change (r * d + j) % d = j
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
    refine ⟨hkey.trans_le hB, ?_, ?_, ?_⟩
    · have hh := (hassign i).1
      rw [hdiv, hmod] at hh
      simpa only [i, Fin.castLE_mk] using hh
    · exact (hassign i).2
    · exact (ha i).trans hdiv

end Lascoux
end HigherSpecht
end
end CanonicalSource23

section CanonicalSource24
/- Source: HigherSpecht/ProtectedColumnTransfers.lean -/



/-!
# Dominance transfers which preserve an initial battery rectangle

Both sequences are decreasing column heights. The target begins with `d`
columns of height `s`, while the current first `d` columns already contain
the protected `s-1` battery cells. We fill the first deficient column by
taking a cell from the first later return of the prefix-sum deficit to zero.
Its donor lies outside the protected prefix, is a removable corner, and
the move preserves every target prefix inequality. Repeating these literal
moves therefore never removes a protected cell.

This file proves the numerical transfer chain. The separate word-level
application must transport the actual cocharge witnesses along that chain.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace HigherSpecht

def columnPrefixSum (a : ℕ → ℕ) (r : ℕ) : ℕ := ∑ i ∈ range r, a i

@[simp] theorem columnPrefixSum_succ (a : ℕ → ℕ) (r : ℕ) :
    columnPrefixSum a (r + 1) = columnPrefixSum a r + a r := by
  exact sum_range_succ a r

def columnTransfer (a : ℕ → ℕ) (i j : ℕ) : ℕ → ℕ :=
  Function.update (Function.update a i (a i + 1)) j (a j - 1)

theorem columnTransfer_point_balance (a : ℕ → ℕ) {i j : ℕ}
    (hij : i ≠ j) (hj : 0 < a j) (k : ℕ) :
    columnTransfer a i j k + (if k = j then 1 else 0) =
      a k + (if k = i then 1 else 0) := by
  by_cases hki : k = i
  · subst k
    simp only [columnTransfer, Function.update_of_ne hij, Function.update_self,
      if_neg hij, if_pos rfl, if_true, Nat.add_zero]
  · by_cases hkj : k = j
    · subst k
      simp only [columnTransfer, Function.update_self, if_pos rfl, if_true, if_neg hki,
        Nat.add_zero]
      omega
    · simp only [columnTransfer, Function.update_of_ne hkj,
        Function.update_of_ne hki, if_neg hkj, if_neg hki]

theorem columnTransfer_prefix_balance (a : ℕ → ℕ) {i j : ℕ}
    (hij : i ≠ j) (hj : 0 < a j) (r : ℕ) :
    columnPrefixSum (columnTransfer a i j) r + (if j < r then 1 else 0) =
      columnPrefixSum a r + (if i < r then 1 else 0) := by
  have h := sum_congr rfl (fun k (_ : k ∈ range r) =>
    columnTransfer_point_balance a hij hj k)
  simpa only [sum_add_distrib, sum_ite_eq', mem_range, columnPrefixSum] using h

def deficientColumns (a : ℕ → ℕ) (d s : ℕ) : Finset ℕ :=
  (range d).filter (fun i => a i < s)

theorem deficientColumns_transfer (a : ℕ → ℕ) {d s i j : ℕ}
    (hi : i < d) (hj : d ≤ j) (hai : a i + 1 = s) :
    deficientColumns (columnTransfer a i j) d s = (deficientColumns a d s).erase i := by
  ext k
  simp only [deficientColumns, mem_filter, mem_range, mem_erase]
  by_cases hki : k = i
  · subst k
    simp only [columnTransfer, Function.update_of_ne (by omega : i ≠ j),
      Function.update_self, hai, Nat.lt_irrefl, and_false, ne_eq, not_true_eq_false,
      false_and]
  · by_cases hkd : k < d
    · have hkj : k ≠ j := by omega
      simp only [columnTransfer, Function.update_of_ne hkj, Function.update_of_ne hki,
        hkd, true_and, hki, ne_eq, not_false_eq_true]
    · simp only [hkd, false_and, and_false]

/-- A genuine transfer, with its protected recipient and unprotected
donor recorded. No dominance conclusion is included in the relation. -/
def ProtectedColumnStep (d s N : ℕ) (a a' : ℕ → ℕ) : Prop :=
  ∃ i j, i < d ∧ d ≤ j ∧ j < N ∧ a i + 1 = s ∧ 0 < a j ∧
    a j < s ∧ a' = columnTransfer a i j

theorem exists_protected_column_step {d s N : ℕ} (hdN : d ≤ N)
    (a b : ℕ → ℕ) (ha : Antitone a) (hb : Antitone b)
    (habove : ∀ k, a k ≤ s) (hprotected : ∀ k < d, s - 1 ≤ a k)
    (hfull : ∀ k < d, b k = s)
    (hzero : ∀ k, N ≤ k → a k = 0)
    (hmass : columnPrefixSum a N = columnPrefixSum b N)
    (hdom : ∀ r, columnPrefixSum a r ≤ columnPrefixSum b r)
    (hdef : (deficientColumns a d s).Nonempty) :
    ∃ a', ProtectedColumnStep d s N a a' ∧ Antitone a' ∧
      (∀ k, a' k ≤ s) ∧ (∀ k < d, s - 1 ≤ a' k) ∧
      (∀ k, N ≤ k → a' k = 0) ∧
      columnPrefixSum a' N = columnPrefixSum b N ∧
      (∀ r, columnPrefixSum a' r ≤ columnPrefixSum b r) ∧
      (deficientColumns a' d s).card < (deficientColumns a d s).card := by
  have hex : ∃ i, i < d ∧ a i < s := by
    obtain ⟨i, hi⟩ := hdef
    exact ⟨i, by simpa only [deficientColumns, mem_filter, mem_range] using hi⟩
  let i := Nat.find hex
  have hi : i < d ∧ a i < s := Nat.find_spec hex
  have hai : a i + 1 = s := by have := hprotected i hi.1; omega
  have hbefore : ∀ k < i, a k = s := by
    intro k hk
    have hk' : k < d := hk.trans hi.1
    have hn : ¬ a k < s := by
      intro hlt
      exact (Nat.not_le_of_lt hk) (Nat.find_min' hex ⟨hk', hlt⟩)
    exact le_antisymm (habove k) (Nat.le_of_not_gt hn)
  have hpref : columnPrefixSum a i = columnPrefixSum b i := by
    apply sum_congr rfl
    intro k hk
    have hki := mem_range.mp hk
    rw [hbefore k hki, hfull k (hki.trans hi.1)]
  have hreturn : ∃ r, i < r ∧ columnPrefixSum a r = columnPrefixSum b r :=
    ⟨N, hi.1.trans_le hdN, hmass⟩
  let r := Nat.find hreturn
  have hr : i < r ∧ columnPrefixSum a r = columnPrefixSum b r := Nat.find_spec hreturn
  have hrN : r ≤ N := Nat.find_min' hreturn ⟨hi.1.trans_le hdN, hmass⟩
  have hstrict : ∀ t, i < t → t < r →
      columnPrefixSum a t < columnPrefixSum b t := by
    intro t hit htr
    have hne : columnPrefixSum a t ≠ columnPrefixSum b t := by
      intro heq
      exact (Nat.not_le_of_lt htr) (Nat.find_min' hreturn ⟨hit, heq⟩)
    exact lt_of_le_of_ne (hdom t) hne
  have hir : i + 1 < r := by
    have hnot : r ≠ i + 1 := by
      intro heq
      have hh := hr.2
      rw [heq, columnPrefixSum_succ, columnPrefixSum_succ, hpref,
        hfull i hi.1] at hh
      omega
    omega
  let j := r - 1
  have hrj : r = j + 1 := by dsimp only [j]; omega
  have hij : i < j := by dsimp only [j]; omega
  have hjN : j < N := by dsimp only [j]; omega
  have hjexcess : b j < a j := by
    have hs := hstrict j hij (by omega)
    have he := hr.2
    rw [hrj, columnPrefixSum_succ, columnPrefixSum_succ] at he
    omega
  have hdj : d ≤ j := by
    by_contra h
    have hh := hfull j (Nat.lt_of_not_ge h)
    have hu := habove j
    omega
  have hjpos : 0 < a j := lt_of_le_of_lt (Nat.zero_le _) hjexcess
  have hjlt : a j < s := lt_of_le_of_lt (ha hij.le) hi.2
  have hjdrop : a (j + 1) < a j := by
    by_contra h
    have heqa : a (j + 1) = a j :=
      le_antisymm (ha (Nat.le_succ j)) (Nat.le_of_not_gt h)
    have hnb := hb (Nat.le_succ j)
    change b (j + 1) ≤ b j at hnb
    have hh := hdom (r + 1)
    rw [columnPrefixSum_succ, columnPrefixSum_succ, hr.2, hrj, heqa] at hh
    omega
  let a' := columnTransfer a i j
  have hat_i : a' i = s := by
    simp only [a', columnTransfer, Function.update_of_ne hij.ne,
      Function.update_self, hai]
  have hat_j : a' j = a j - 1 := by simp only [a', columnTransfer, Function.update_self]
  have hat_other : ∀ k, k ≠ i → k ≠ j → a' k = a k := by
    intro k hki hkj
    simp only [a', columnTransfer, Function.update_of_ne hkj, Function.update_of_ne hki]
  have ha' : Antitone a' := by
    intro p q hpq
    by_cases hpqe : p = q
    · subst p
      exact le_rfl
    have hpqlt : p < q := lt_of_le_of_ne hpq hpqe
    by_cases hqi : q = i
    · subst q
      rw [hat_i, hat_other p (by omega) (by omega), hbefore p hpqlt]
    · by_cases hqj : q = j
      · subst q
        rw [hat_j]
        by_cases hpi : p = i
        · subst p; rw [hat_i]; exact (Nat.sub_le _ _).trans (habove j)
        · rw [hat_other p hpi hpqe]
          exact (Nat.sub_le _ _).trans (ha hpq)
      · rw [hat_other q hqi hqj]
        by_cases hpi : p = i
        · subst p
          rw [hat_i]
          exact habove q
        · by_cases hpj : p = j
          · subst p
            rw [hat_j]
            have hle := ha (show j + 1 ≤ q by omega)
            omega
          · rw [hat_other p hpi hpj]
            exact ha hpq
  have hupper : ∀ k, a' k ≤ s := by
    intro k
    by_cases hki : k = i
    · subst k; rw [hat_i]
    · by_cases hkj : k = j
      · subst k; rw [hat_j]; exact (Nat.sub_le _ _).trans (habove j)
      · rw [hat_other k hki hkj]; exact habove k
  have hprotected' : ∀ k < d, s - 1 ≤ a' k := by
    intro k hk
    by_cases hki : k = i
    · subst k; rw [hat_i]; exact Nat.sub_le _ _
    · rw [hat_other k hki (by omega)]; exact hprotected k hk
  have hzero' : ∀ k, N ≤ k → a' k = 0 := by
    intro k hk
    rw [hat_other k (by omega) (by omega)]
    exact hzero k hk
  have hmass' : columnPrefixSum a' N = columnPrefixSum b N := by
    have hh := columnTransfer_prefix_balance a hij.ne hjpos N
    simp only [if_pos hjN, if_pos (hi.1.trans_le hdN)] at hh
    exact (Nat.add_right_cancel hh).trans hmass
  have hdom' : ∀ t, columnPrefixSum a' t ≤ columnPrefixSum b t := by
    intro t
    have hh := columnTransfer_prefix_balance a hij.ne hjpos t
    change columnPrefixSum a' t + _ = _ at hh
    by_cases hit : i < t
    · by_cases hjt : j < t
      · simp only [if_pos hit, if_pos hjt] at hh
        exact (Nat.add_right_cancel hh).le.trans (hdom t)
      · simp only [if_pos hit, if_neg hjt, Nat.add_zero] at hh
        have hs := hstrict t hit (by omega)
        omega
    · have hjt : ¬ j < t := by omega
      simp only [if_neg hit, if_neg hjt, Nat.add_zero] at hh
      exact hh.le.trans (hdom t)
  have hsmall : (deficientColumns a' d s).card < (deficientColumns a d s).card := by
    rw [deficientColumns_transfer a hi.1 hdj hai]
    exact card_erase_lt_of_mem (by
      simpa only [deficientColumns, mem_filter, mem_range] using hi)
  exact ⟨a', ⟨i, j, hi.1, hdj, hjN, hai, hjpos, hjlt, rfl⟩,
    ha', hupper, hprotected', hzero', hmass', hdom', hsmall⟩

/-- The complete protected-prefix filling phase is a finite chain of
literal transfers. Its donor never belongs to the protected prefix. -/
theorem exists_protected_column_fill {d s N : ℕ} (hdN : d ≤ N)
    (a b : ℕ → ℕ) (ha : Antitone a) (hb : Antitone b)
    (habove : ∀ k, a k ≤ s) (hprotected : ∀ k < d, s - 1 ≤ a k)
    (hfull : ∀ k < d, b k = s)
    (hzero : ∀ k, N ≤ k → a k = 0)
    (hmass : columnPrefixSum a N = columnPrefixSum b N)
    (hdom : ∀ r, columnPrefixSum a r ≤ columnPrefixSum b r) :
    ∃ a', Relation.ReflTransGen (ProtectedColumnStep d s N) a a' ∧
      Antitone a' ∧ (∀ k < d, a' k = s) ∧
      (∀ k, N ≤ k → a' k = 0) ∧
      columnPrefixSum a' N = columnPrefixSum b N ∧
      (∀ r, columnPrefixSum a' r ≤ columnPrefixSum b r) := by
  have aux : ∀ m : ℕ, ∀ a : ℕ → ℕ,
      (deficientColumns a d s).card = m → Antitone a →
      (∀ k, a k ≤ s) → (∀ k < d, s - 1 ≤ a k) →
      (∀ k, N ≤ k → a k = 0) →
      columnPrefixSum a N = columnPrefixSum b N →
      (∀ r, columnPrefixSum a r ≤ columnPrefixSum b r) →
      ∃ a', Relation.ReflTransGen (ProtectedColumnStep d s N) a a' ∧
        Antitone a' ∧ (∀ k < d, a' k = s) ∧
        (∀ k, N ≤ k → a' k = 0) ∧
        columnPrefixSum a' N = columnPrefixSum b N ∧
        (∀ r, columnPrefixSum a' r ≤ columnPrefixSum b r) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro a hcard ha habove hprotected hzero hmass hdom
        by_cases he : (deficientColumns a d s).Nonempty
        · obtain ⟨a₁, hstep, ha₁, hu₁, hp₁, hz₁, hm₁, hd₁, hlt⟩ :=
            exists_protected_column_step hdN a b ha hb habove hprotected hfull
              hzero hmass hdom he
          obtain ⟨a₂, hchain, ha₂, hf₂, hz₂, hm₂, hd₂⟩ :=
            ih (deficientColumns a₁ d s).card (hlt.trans_eq hcard) a₁ rfl
              ha₁ hu₁ hp₁ hz₁ hm₁ hd₁
          exact ⟨a₂, (Relation.ReflTransGen.single hstep).trans hchain,
            ha₂, hf₂, hz₂, hm₂, hd₂⟩
        · refine ⟨a, .refl, ha, ?_, hzero, hmass, hdom⟩
          intro k hk
          have hn : ¬ a k < s := by
            intro hlt
            exact he ⟨k, by simp only [deficientColumns, mem_filter, mem_range]; exact ⟨hk, hlt⟩⟩
          exact le_antisymm (habove k) (Nat.le_of_not_gt hn)
  exact aux _ a rfl ha habove hprotected hzero hmass hdom

end HigherSpecht
end
end CanonicalSource24

section CanonicalSource25
/- Source: HigherSpecht/BatteryContentColumns.lean -/



/-! The conjugate of the actual augmented partition consists of `d` columns
of height `s`, followed by the original columns of `lam`. -/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

theorem batteryContentShape_colLen (lam : YoungDiagram) (s d j : ℕ)
    (hheight : lam.colLen 0 ≤ s) :
    (batteryContentShape lam s d).colLen j =
      if j < d then s else lam.colLen (j - d) := by
  apply eq_of_forall_lt_iff
  intro r
  rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen,
    batteryContentShape_rowLen]
  by_cases hj : j < d
  · rw [if_pos hj]
    by_cases hr : r < s
    · rw [if_pos hr]
      exact ⟨fun _ => hr, fun _ => lt_of_lt_of_le hj (Nat.le_add_right d _)⟩
    · rw [if_neg hr]
      exact ⟨fun h => (Nat.not_lt_zero j h).elim, fun h => (hr h).elim⟩
  · rw [if_neg hj, ← YoungDiagram.mem_iff_lt_colLen,
      YoungDiagram.mem_iff_lt_rowLen]
    by_cases hr : r < s
    · rw [if_pos hr]
      omega
    · rw [if_neg hr]
      have hz : lam.rowLen r = 0 :=
        YoungDiagram.rowLen_eq_zero_of_colLen_le (hheight.trans (Nat.le_of_not_gt hr))
      simp only [hz, Nat.not_lt_zero]

theorem batteryContentShape_colLen_prefix (lam : YoungDiagram) (s d : ℕ)
    (hheight : lam.colLen 0 ≤ s) :
    columnPrefixSum (batteryContentShape lam s d).colLen d = d * s := by
  unfold columnPrefixSum
  have h : (∑ j ∈ range d, (batteryContentShape lam s d).colLen j) =
      ∑ _j ∈ range d, s := by
    apply sum_congr rfl
    intro j hj
    rw [batteryContentShape_colLen lam s d j hheight,
      if_pos (mem_range.mp hj)]
  rw [h]
  simp only [sum_const, card_range, smul_eq_mul]

theorem batteryContentShape_colLen_shift (lam : YoungDiagram) (s d r : ℕ)
    (hheight : lam.colLen 0 ≤ s) :
    (batteryContentShape lam s d).colLen (d + r) = lam.colLen r := by
  rw [batteryContentShape_colLen lam s d (d + r) hheight,
    if_neg (by omega : ¬ d + r < d), Nat.add_sub_cancel_left]

theorem batteryContentShape_columnPrefix_add (lam : YoungDiagram) (s d r : ℕ)
    (hheight : lam.colLen 0 ≤ s) :
    columnPrefixSum (batteryContentShape lam s d).colLen (d + r) =
      d * s + columnPrefixSum lam.colLen r := by
  rw [columnPrefixSum, sum_range_add]
  change columnPrefixSum (batteryContentShape lam s d).colLen d + _ = _
  rw [batteryContentShape_colLen_prefix lam s d hheight]
  congr 1
  apply sum_congr rfl
  intro j hj
  exact batteryContentShape_colLen_shift lam s d j hheight

end HigherSpecht.Lascoux
end
end CanonicalSource25

section CanonicalSource26
/- Source: HigherSpecht/CochargeColumnTransfer.lean -/



/-!
# Genuine two-column transfers for partition box moves

A cocharge word contains every value below any one of its letters. Therefore
the rightmost maximum of another word can be moved into it whenever an anchor
in the receiving word is at least that maximum. Repeating this literal move
gives every required transfer. If the higher maximum belongs to the shorter
word, grow that word to the new longer size and exchange the column names.
The final theorem has exactly the cardinality change in a partition box move.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

theorem exists_rightmost_selected_max {n : ℕ} (w : Fin n → ℕ)
    (C : Finset (Fin n)) (hC : C.Nonempty) :
    ∃ r ∈ C, (∀ i ∈ C, w i ≤ w r) ∧ (∀ i ∈ C, w i = w r → i ≤ r) := by
  obtain ⟨r, hr, hmax⟩ := C.exists_max_image (fun i => toLex (w i, i)) hC
  refine ⟨r, hr, ?_, ?_⟩
  · intro i hi
    rcases lt_or_eq_of_le (hmax i hi) with h | h
    · rcases Prod.Lex.toLex_lt_toLex.mp h with hval | ⟨hval, _⟩
      · exact hval.le
      · exact hval.le
    · exact (congrArg (fun z : ℕ ×ₗ Fin n => (ofLex z).1) h).le
  · intro i hi heq
    rcases lt_or_eq_of_le (hmax i hi) with h | h
    · rcases Prod.Lex.toLex_lt_toLex.mp h with hval | ⟨_, hpos⟩
      · omega
      · exact hpos.le
    · exact (congrArg (fun z : ℕ ×ₗ Fin n => (ofLex z).2) h).le

/-- Move exactly `k` donor positions into the column containing the specified
maximum anchor. Every intermediate move is an actual selected-word insertion
and a rightmost-maximum deletion. -/
theorem cochargeColumns_transfer_to_anchor {n : ℕ} (w : Fin n → ℕ)
    (A B : Finset (Fin n)) (p : Fin n) (hAB : Disjoint A B)
    (hA : IsCochargeWord (selectedWord w A))
    (hB : IsCochargeWord (selectedWord w B))
    (hp : p ∈ A) (hbound : ∀ i ∈ B, w i ≤ w p)
    (k : ℕ) (hk : k ≤ B.card) :
    ∃ A' B' : Finset (Fin n), Disjoint A' B' ∧ A' ∪ B' = A ∪ B ∧
      IsCochargeWord (selectedWord w A') ∧ IsCochargeWord (selectedWord w B') ∧
      A'.card = A.card + k ∧ B'.card + k = B.card := by
  induction k generalizing A B with
  | zero => exact ⟨A, B, hAB, rfl, hA, hB, by omega, by omega⟩
  | succ k ih =>
      have hBpos : B.Nonempty := card_pos.mp (by omega)
      obtain ⟨r, hr, hrmax, hright⟩ := exists_rightmost_selected_max w B hBpos
      have hrA : r ∉ A := fun h => disjoint_left.mp hAB h hr
      have hwp : w p ∈ selectedWord w A := (mem_selectedWord w A _).mpr ⟨p, hp, rfl⟩
      have hwra : w r ∈ selectedWord w A := hA.interval_mem hwp (hbound r hr)
      have hA1 : IsCochargeWord (selectedWord w (insert r A)) := hA.selected_insert r hwra
      have hB1 : IsCochargeWord (selectedWord w (B.erase r)) :=
        hB.selected_erase_rightmost_max r hrmax hright
      have hd : Disjoint (insert r A) (B.erase r) := by
        apply disjoint_left.mpr
        intro i hiA hiB
        obtain ⟨hir, hiB⟩ := mem_erase.mp hiB
        rcases mem_insert.mp hiA with rfl | hiA
        · exact hir rfl
        · exact disjoint_left.mp hAB hiA hiB
      have hu : insert r A ∪ B.erase r = A ∪ B := by
        ext i
        simp only [mem_union, mem_insert, mem_erase]
        constructor
        · rintro ((rfl | hiA) | ⟨_, hiB⟩)
          · exact Or.inr hr
          · exact Or.inl hiA
          · exact Or.inr hiB
        · intro hi
          by_cases hir : i = r
          · exact Or.inl (Or.inl hir)
          · rcases hi with hiA | hiB
            · exact Or.inl (Or.inr hiA)
            · exact Or.inr ⟨hir, hiB⟩
      have hcA : (insert r A).card = A.card + 1 := card_insert_of_notMem hrA
      have hcB : (B.erase r).card + 1 = B.card := card_erase_add_one hr
      obtain ⟨A', B', hdisj, hunion, hA', hB', hcardA', hcardB'⟩ :=
        ih (A := insert r A) (B := B.erase r) hd hA1 hB1
          (mem_insert_of_mem hp) (fun i hi => hbound i (mem_erase.mp hi).2)
          (by omega)
      exact ⟨A', B', hdisj, hunion.trans hu, hA', hB', by omega, by omega⟩

/-- Exact witness transfer for the genuine partition box move
`{a,b+1} → {a+1,b}`. The old columns may have repeated letters and unrelated
maximum values; only their actual cocharge-word property is assumed. -/
theorem cochargeColumns_boxMove {n : ℕ} (w : Fin n → ℕ)
    (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : IsCochargeWord (selectedWord w A))
    (hB : IsCochargeWord (selectedWord w B))
    (a b : ℕ) (hcardA : A.card = a) (hcardB : B.card = b + 1) (hba : b < a) :
    ∃ A' B' : Finset (Fin n), A' ∪ B' = A ∪ B ∧ Disjoint A' B' ∧
      IsCochargeWord (selectedWord w A') ∧ IsCochargeWord (selectedWord w B') ∧
      A'.card = a + 1 ∧ B'.card = b := by
  have hBpos : B.Nonempty := card_pos.mp (by omega)
  have hU : (A ∪ B).Nonempty := by
    obtain ⟨i, hi⟩ := hBpos
    exact ⟨i, mem_union_right A hi⟩
  obtain ⟨p, hp, hmax, _⟩ := exists_rightmost_selected_max w (A ∪ B) hU
  by_cases hpA : p ∈ A
  · obtain ⟨A', B', hd, hu, hA', hB', hcA, hcB⟩ :=
      cochargeColumns_transfer_to_anchor w A B p hAB hA hB hpA
        (fun i hi => hmax i (mem_union_right A hi)) 1 (by omega)
    exact ⟨A', B', hu, hd, hA', hB', by omega, by omega⟩
  · have hpB : p ∈ B := (mem_union.mp hp).resolve_left hpA
    obtain ⟨A', B', hd, hu, hA', hB', hcA, hcB⟩ :=
      cochargeColumns_transfer_to_anchor w B A p hAB.symm hB hA hpB
        (fun i hi => hmax i (mem_union_left B hi)) (a - b) (by omega)
    refine ⟨A', B', ?_, hd, hA', hB', by omega, by omega⟩
    exact hu.trans (union_comm B A)

end HigherSpecht
end
end CanonicalSource26

section CanonicalSource27
/- Source: HigherSpecht/ProtectedCochargeColumns.lean -/



/-!
# Literal cocharge witnesses along the protected transfer chain

A deficient battery column contains the complete alphabet `0,...,s-2`.
Every donor has fewer than `s` cells, so its rightmost maximum belongs to
that alphabet. Moving that actual position preserves both cocharge words
and every protected battery position. No exchange of the two column names
is used in this phase.
-/

noncomputable section
open Finset
open scoped Classical

namespace HigherSpecht

theorem IsCochargeWord.selected_value_lt_card {n : ℕ} {w : Fin n → ℕ}
    {C : Finset (Fin n)} (hC : IsCochargeWord (selectedWord w C))
    {t : Fin n} (ht : t ∈ C) : w t < C.card := by
  have hsub : range (w t + 1) ⊆ C.image w := by
    intro a ha
    have hw := hC.interval_mem ((mem_selectedWord w C _).mpr ⟨t, ht, rfl⟩)
      (Nat.le_of_lt_succ (mem_range.mp ha))
    obtain ⟨u, hu, hwu⟩ := (mem_selectedWord w C a).mp hw
    exact mem_image.mpr ⟨u, hu, hwu⟩
  have hh := (card_le_card hsub).trans (card_image_le : (C.image w).card ≤ C.card)
  rw [card_range] at hh
  omega

def transferredColumns {n N : ℕ} (C : Fin N → Finset (Fin n))
    (i j : Fin N) (t : Fin n) : Fin N → Finset (Fin n) :=
  Function.update (Function.update C i (insert t (C i))) j ((C j).erase t)

theorem transferredColumns_disjoint {n N : ℕ} {C : Fin N → Finset (Fin n)}
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    {i j : Fin N} (hij : i ≠ j) {t : Fin n} (ht : t ∈ C j) :
    Pairwise (fun k l => Disjoint (transferredColumns C i j t k)
      (transferredColumns C i j t l)) := by
  have hnot (k : Fin N) (hkj : k ≠ j) : t ∉ C k :=
    fun h => disjoint_left.mp (hC hkj) h ht
  intro k l hkl
  apply disjoint_left.mpr
  intro u huk hul
  by_cases hkj : k = j
  · subst k
    have huj : u ≠ t ∧ u ∈ C j := by
      simpa only [transferredColumns, Function.update_self, mem_erase] using huk
    by_cases hli : l = i
    · subst l
      have hul' : u = t ∨ u ∈ C i := by
        simpa only [transferredColumns, Function.update_of_ne hij,
          Function.update_self, mem_insert] using hul
      rcases hul' with heq | hui
      · exact huj.1 heq
      · exact disjoint_left.mp (hC hij) hui huj.2
    · have hlj : l ≠ j := Ne.symm hkl
      have hul' : u ∈ C l := by
        simpa only [transferredColumns, Function.update_of_ne hlj,
          Function.update_of_ne hli] using hul
      exact disjoint_left.mp (hC hkl) huj.2 hul'
  · by_cases hlj : l = j
    · subst l
      have hul' : u ≠ t ∧ u ∈ C j := by
        simpa only [transferredColumns, Function.update_self, mem_erase] using hul
      by_cases hki : k = i
      · subst k
        have huk' : u = t ∨ u ∈ C i := by
          simpa only [transferredColumns, Function.update_of_ne hij,
            Function.update_self, mem_insert] using huk
        rcases huk' with heq | hui
        · exact hul'.1 heq
        · exact disjoint_left.mp (hC hij) hui hul'.2
      · have huk' : u ∈ C k := by
          simpa only [transferredColumns, Function.update_of_ne hkj,
            Function.update_of_ne hki] using huk
        exact disjoint_left.mp (hC hkl) huk' hul'.2
    · by_cases hki : k = i
      · subst k
        have huk' : u = t ∨ u ∈ C i := by
          simpa only [transferredColumns, Function.update_of_ne hij,
            Function.update_self, mem_insert] using huk
        have hli : l ≠ i := Ne.symm hkl
        have hul' : u ∈ C l := by
          simpa only [transferredColumns, Function.update_of_ne hlj,
            Function.update_of_ne hli] using hul
        rcases huk' with rfl | hui
        · exact hnot l hlj hul'
        · exact disjoint_left.mp (hC hkl) hui hul'
      · by_cases hli : l = i
        · subst l
          have hul' : u = t ∨ u ∈ C i := by
            simpa only [transferredColumns, Function.update_of_ne hij,
              Function.update_self, mem_insert] using hul
          have huk' : u ∈ C k := by
            simpa only [transferredColumns, Function.update_of_ne hkj,
              Function.update_of_ne hki] using huk
          rcases hul' with rfl | hui
          · exact hnot k hkj huk'
          · exact disjoint_left.mp (hC hkl) huk' hui
        · have huk' : u ∈ C k := by
            simpa only [transferredColumns, Function.update_of_ne hkj,
              Function.update_of_ne hki] using huk
          have hul' : u ∈ C l := by
            simpa only [transferredColumns, Function.update_of_ne hlj,
              Function.update_of_ne hli] using hul
          exact disjoint_left.mp (hC hkl) huk' hul'

theorem transferredColumns_union {n N : ℕ} {C : Fin N → Finset (Fin n)}
    {i j : Fin N} (hij : i ≠ j) {t : Fin n} (ht : t ∈ C j) :
    univ.biUnion (transferredColumns C i j t) = univ.biUnion C := by
  ext u
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hkj : k = j
    · subst k
      exact ⟨j, (mem_erase.mp (by simpa only [transferredColumns, Function.update_self] using hk)).2⟩
    · by_cases hki : k = i
      · subst k
        have hh : u = t ∨ u ∈ C i := by
          simpa only [transferredColumns, Function.update_of_ne hij,
            Function.update_self, mem_insert] using hk
        rcases hh with rfl | hh
        · exact ⟨j, ht⟩
        · exact ⟨i, hh⟩
      · exact ⟨k, by simpa only [transferredColumns, Function.update_of_ne hkj,
          Function.update_of_ne hki] using hk⟩
  · rintro ⟨k, hk⟩
    by_cases hut : u = t
    · subst u
      refine ⟨i, ?_⟩
      simp only [transferredColumns, Function.update_of_ne hij, Function.update_self,
        mem_insert, true_or]
    · by_cases hkj : k = j
      · subst k
        exact ⟨j, by simpa only [transferredColumns, Function.update_self, mem_erase] using
          (And.intro hut hk)⟩
      · by_cases hki : k = i
        · subst k
          exact ⟨i, by simpa only [transferredColumns, Function.update_of_ne hij,
            Function.update_self] using mem_insert_of_mem hk⟩
        · exact ⟨k, by simpa only [transferredColumns, Function.update_of_ne hkj,
            Function.update_of_ne hki] using hk⟩

/-- One recorded numerical step is implemented on the actual selected
positions, retaining every protected battery set and the selected union. -/
theorem ColumnCochargeWitness.protected_step {n N d s : ℕ}
    {w : Fin n → ℕ} {a a' : ℕ → ℕ} (hdN : d ≤ N)
    (W : ColumnCochargeWitness w (fun j : Fin N => a j.val))
    (battery : Fin d → Finset (Fin n))
    (hkeep : ∀ k, battery k ⊆ W.columns (Fin.castLE hdN k))
    (halphabet : ∀ k (r : ℕ), r < s - 1 → ∃ t ∈ battery k, w t = r)
    (hstep : ProtectedColumnStep d s N a a') :
    ∃ V : ColumnCochargeWitness w (fun j : Fin N => a' j.val),
      (∀ k, battery k ⊆ V.columns (Fin.castLE hdN k)) ∧ V.selected = W.selected := by
  obtain ⟨i, j, hi, hdj, hjN, hai, haj, hajs, rfl⟩ := hstep
  let iN : Fin N := ⟨i, hi.trans_le hdN⟩
  let jN : Fin N := ⟨j, hjN⟩
  let iD : Fin d := ⟨i, hi⟩
  have hij : iN ≠ jN := fun h => by have := congrArg Fin.val h; dsimp [iN, jN] at this; omega
  have hpos : (W.columns jN).Nonempty := card_pos.mp (by rw [W.card_eq]; exact haj)
  obtain ⟨t, ht, hmax, hright⟩ := exists_rightmost_selected_max w (W.columns jN) hpos
  have htA : t ∉ W.columns iN := fun h => disjoint_left.mp (W.disjoint hij) h ht
  have hts : w t < s - 1 := by
    have hh := (W.admissible jN).selected_value_lt_card ht
    rw [W.card_eq] at hh
    dsimp only [jN] at hh
    omega
  obtain ⟨p, hp, hpt⟩ := halphabet iD (w t) hts
  have hptin : w t ∈ selectedWord w (W.columns iN) :=
    (mem_selectedWord w _ _).mpr ⟨p, hkeep iD hp, hpt⟩
  have hnewA := (W.admissible iN).selected_insert t hptin
  have hnewB := (W.admissible jN).selected_erase_rightmost_max t hmax hright
  let C := transferredColumns W.columns iN jN t
  have hcard : ∀ k : Fin N, (C k).card = columnTransfer a i j k.val := by
    intro k
    by_cases hkj : k = jN
    · subst k
      simp only [C, transferredColumns, Function.update_self, columnTransfer,
        jN, Function.update_self]
      rw [card_erase_of_mem ht, W.card_eq]
    · have hkj' : k.val ≠ j := fun h => hkj (Fin.ext h)
      by_cases hki : k = iN
      · subst k
        simp only [C, transferredColumns, Function.update_of_ne hij, Function.update_self,
          columnTransfer, iN, Function.update_of_ne (by omega : i ≠ j), Function.update_self]
        rw [card_insert_of_notMem htA, W.card_eq]
      · have hki' : k.val ≠ i := fun h => hki (Fin.ext h)
        simp only [C, transferredColumns, Function.update_of_ne hkj, Function.update_of_ne hki,
          columnTransfer, Function.update_of_ne hkj', Function.update_of_ne hki']
        exact W.card_eq k
  let V : ColumnCochargeWitness w (fun k : Fin N => columnTransfer a i j k.val) :=
    { columns := C
      disjoint := transferredColumns_disjoint W.disjoint hij ht
      card_eq := hcard
      admissible := by
        intro k
        by_cases hkj : k = jN
        · subst k
          simpa only [C, transferredColumns, Function.update_self] using hnewB
        · by_cases hki : k = iN
          · subst k
            simpa only [C, transferredColumns, Function.update_of_ne hij,
              Function.update_self] using hnewA
          · simpa only [C, transferredColumns, Function.update_of_ne hkj,
              Function.update_of_ne hki] using W.admissible k }
  refine ⟨V, ?_, transferredColumns_union hij ht⟩
  intro k u hu
  have hkj : Fin.castLE hdN k ≠ jN := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.coe_castLE, jN] at hh
    omega
  by_cases hki : Fin.castLE hdN k = iN
  · change u ∈ C (Fin.castLE hdN k)
    dsimp only [C]
    rw [transferredColumns, Function.update_of_ne hkj, Function.update_apply,
      if_pos hki]
    exact mem_insert_of_mem (by simpa only [← hki] using hkeep k hu)
  · change u ∈ C (Fin.castLE hdN k)
    dsimp only [C]
    rw [transferredColumns, Function.update_of_ne hkj, Function.update_of_ne hki]
    exact hkeep k hu

theorem ColumnCochargeWitness.protected_chain {n N d s : ℕ}
    {w : Fin n → ℕ} {a a' : ℕ → ℕ} (hdN : d ≤ N)
    (W : ColumnCochargeWitness w (fun j : Fin N => a j.val))
    (battery : Fin d → Finset (Fin n))
    (hkeep : ∀ k, battery k ⊆ W.columns (Fin.castLE hdN k))
    (halphabet : ∀ k (r : ℕ), r < s - 1 → ∃ t ∈ battery k, w t = r)
    (hchain : Relation.ReflTransGen (ProtectedColumnStep d s N) a a') :
    ∃ V : ColumnCochargeWitness w (fun j : Fin N => a' j.val),
      (∀ k, battery k ⊆ V.columns (Fin.castLE hdN k)) ∧ V.selected = W.selected := by
  induction hchain with
  | refl => exact ⟨W, hkeep, rfl⟩
  | tail hchain hstep ih =>
      obtain ⟨U, hU, hselected⟩ := ih
      obtain ⟨V, hV, hselected'⟩ := U.protected_step hdN battery hU halphabet hstep
      exact ⟨V, hV, hselected'.trans hselected⟩

end HigherSpecht
end
end CanonicalSource27

section CanonicalSource28
/- Source: HigherSpecht/CochargeColumnMajorization.lean -/



/-!
# Column cocharge witnesses under genuine partition dominance

A witness is a multiset of actual disjoint position sets, with its actual
cardinality multiset. A box move is realized by the proved two-word transfer.
The pinned partition theorem supplies the complete finite box-move chain;
conjugation converts the paper's row dominance into this column majorization.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

private instance cochargeDisjointSymm {n : ℕ} :
    Std.Symm (fun A B : Finset (Fin n) => Disjoint A B) :=
  ⟨fun _ _ h => h.symm⟩

private theorem multiset_disjoint_cons {n : ℕ} (A : Finset (Fin n))
    (C : Multiset (Finset (Fin n))) :
    (A ::ₘ C).Pairwise (fun X Y => Disjoint X Y) ↔
      (∀ B ∈ C, Disjoint A B) ∧ C.Pairwise (fun X Y => Disjoint X Y) := by
  refine Quotient.inductionOn' C ?_
  intro L
  simpa only [Multiset.quot_mk_to_coe, Multiset.cons_coe,
    Multiset.pairwise_coe_iff_pairwise, List.pairwise_cons, Multiset.mem_coe]

/-- Actual disjoint cocharge subwords with exactly the indicated positive
lengths. Neither dominance nor an output shape is part of this definition. -/
def CochargeRealizes {n : ℕ} (w : Fin n → ℕ) (parts : Multiset ℕ) : Prop :=
  ∃ C : Multiset (Finset (Fin n)),
    C.Pairwise (fun A B => Disjoint A B) ∧
    (∀ A ∈ C, IsCochargeWord (selectedWord w A) ∧ A.Nonempty) ∧
    C.map Finset.card = parts

private theorem boxMove_old_parts_le {k : ℕ} {nu mu : k.Partition}
    {a b : ℕ} (hba : b < a)
    (h : mu.parts + {a, b + 1} =
      nu.parts + ({a + 1, b} : Multiset ℕ).filter (· ≠ 0)) :
    ({a, b + 1} : Multiset ℕ) ≤ nu.parts := by
  apply Multiset.le_iff_count.mpr
  intro t
  have hc := congrArg (Multiset.count t) h
  by_cases hta : t = a
  · subst t
    have hne : a ≠ b := by omega
    have hne' : a ≠ a + 1 := by omega
    simp only [Multiset.count_add] at hc
    have hnew : Multiset.count a (({a + 1, b} : Multiset ℕ).filter (· ≠ 0)) = 0 := by
      simp [Multiset.count_filter, hne, hne']
    rw [hnew] at hc
    omega
  · by_cases htb : t = b + 1
    · subst t
      have hne : b + 1 ≠ a + 1 := by omega
      have hne' : b + 1 ≠ b := by omega
      simp only [Multiset.count_add] at hc
      have hnew : Multiset.count (b + 1) (({a + 1, b} : Multiset ℕ).filter (· ≠ 0)) = 0 := by
        simp [Multiset.count_filter, hne, hne', ne_of_lt hba]
      rw [hnew] at hc
      omega
    · simp [hta, htb]

/-- Every actual partition box move is implemented on the position sets. -/
theorem CochargeRealizes.boxMove {n k : ℕ} {w : Fin n → ℕ}
    {nu mu : k.Partition} (hreal : CochargeRealizes w nu.parts)
    (hmove : nu.IsBoxMove mu) : CochargeRealizes w mu.parts := by
  obtain ⟨a, b, hba, hparts⟩ := Nat.Partition.isBoxMove_iff.mp hmove
  obtain ⟨C, hpair, hvalid, hmap⟩ := hreal
  have hle := boxMove_old_parts_le hba hparts
  rw [← hmap] at hle
  obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.mp hle
  have hR' : C.map Finset.card = a ::ₘ (b + 1) ::ₘ R := by
    simpa only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add] using hR
  obtain ⟨A, hA, hcardA, hmapA⟩ := (Multiset.map_eq_cons Finset.card C ((b + 1) ::ₘ R) a).mpr hR'
  obtain ⟨B, hB, hcardB, hmapB⟩ :=
    (Multiset.map_eq_cons Finset.card (C.erase A) R (b + 1)).mpr hmapA
  let D := (C.erase A).erase B
  have hC : C = A ::ₘ B ::ₘ D := by
    calc
      C = A ::ₘ (C.erase A) := (Multiset.cons_erase hA).symm
      _ = _ := congrArg (Multiset.cons A) (Multiset.cons_erase hB).symm
  rw [hC, multiset_disjoint_cons, multiset_disjoint_cons] at hpair
  have hAB : Disjoint A B := hpair.1 B (Multiset.mem_cons_self _ _)
  have hAD : ∀ E ∈ D, Disjoint A E := fun E hE => hpair.1 E (Multiset.mem_cons_of_mem hE)
  have hBD : ∀ E ∈ D, Disjoint B E := hpair.2.1
  have hBmem : B ∈ C := Multiset.mem_of_mem_erase hB
  obtain ⟨A', B', hU, hd, hA', hB', hcA, hcB⟩ :=
    cochargeColumns_boxMove w A B hAB (hvalid A hA).1 (hvalid B hBmem).1
      a b hcardA hcardB hba
  have hnewD (E : Finset (Fin n)) (hE : E ∈ D) :
      Disjoint A' E ∧ Disjoint B' E := by
    have h := Finset.disjoint_union_left.mpr ⟨hAD E hE, hBD E hE⟩
    rw [← hU] at h
    exact Finset.disjoint_union_left.mp h
  have hDvalid : ∀ E ∈ D, IsCochargeWord (selectedWord w E) ∧ E.Nonempty := by
    intro E hE
    apply hvalid E
    rw [hC]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hE)
  have hApos : A'.Nonempty := card_pos.mp (by omega)
  let C' : Multiset (Finset (Fin n)) := if b = 0 then A' ::ₘ D else A' ::ₘ B' ::ₘ D
  have hCpair : C'.Pairwise (fun X Y => Disjoint X Y) := by
    dsimp only [C']
    by_cases hb : b = 0
    · rw [if_pos hb, multiset_disjoint_cons]
      exact ⟨fun E hE => (hnewD E hE).1, hpair.2.2⟩
    · rw [if_neg hb, multiset_disjoint_cons, multiset_disjoint_cons]
      refine ⟨?_, fun E hE => (hnewD E hE).2, hpair.2.2⟩
      intro E hE
      rcases Multiset.mem_cons.mp hE with rfl | hE
      · exact hd
      · exact (hnewD E hE).1
  have hCvalid : ∀ E ∈ C', IsCochargeWord (selectedWord w E) ∧ E.Nonempty := by
    intro E hE
    dsimp only [C'] at hE
    by_cases hb : b = 0
    · rw [if_pos hb, Multiset.mem_cons] at hE
      rcases hE with rfl | hE
      · exact ⟨hA', hApos⟩
      · exact hDvalid E hE
    · rw [if_neg hb, Multiset.mem_cons] at hE
      rcases hE with rfl | hE
      · exact ⟨hA', hApos⟩
      · rcases Multiset.mem_cons.mp hE with rfl | hE
        · exact ⟨hB', card_pos.mp (by omega)⟩
        · exact hDvalid E hE
  have hnewmap : C'.map Finset.card = R +
      ({a + 1, b} : Multiset ℕ).filter (· ≠ 0) := by
    change (if b = 0 then A' ::ₘ D else A' ::ₘ B' ::ₘ D).map Finset.card = _
    by_cases hb : b = 0 <;> simp [hb, Multiset.map_cons, hcA, hcB, hmapB,
      D, Multiset.insert_eq_cons, Multiset.filter_singleton, Multiset.singleton_add, add_comm] <;>
      exact (Multiset.singleton_add _ R).symm.trans (add_comm _ _)
  refine ⟨C', hCpair, hCvalid, ?_⟩
  have hcancel : C'.map Finset.card + {a, b + 1} = mu.parts + {a, b + 1} := by
    calc
      C'.map Finset.card + {a, b + 1} =
          (R + ({a + 1, b} : Multiset ℕ).filter (· ≠ 0)) + {a, b + 1} := by rw [hnewmap]
      _ = ({a, b + 1} + R) + ({a + 1, b} : Multiset ℕ).filter (· ≠ 0) := by ac_rfl
      _ = nu.parts + ({a + 1, b} : Multiset ℕ).filter (· ≠ 0) := by rw [← hR, hmap]
      _ = mu.parts + {a, b + 1} := hparts.symm
  exact add_right_cancel hcancel

/-- The complete finite box-move chain, not a reduction to an unproved move
or a new majorization premise on the paper's theorem. -/
theorem CochargeRealizes.of_dominates {n k : ℕ} {w : Fin n → ℕ}
    {nu mu : k.Partition} (hreal : CochargeRealizes w nu.parts)
    (hdom : mu.Dominates nu) : CochargeRealizes w mu.parts := by
  have hchain := Nat.Partition.dominates_iff_reflTransGen_isBoxMove.mp hdom
  clear hdom
  induction hchain with
  | refl => exact hreal
  | tail hchain hmove ih => exact ih.boxMove hmove

private theorem exists_list_with_card_map {n : ℕ}
    (C : Multiset (Finset (Fin n))) (sizes : List ℕ)
    (h : C.map Finset.card = sizes) :
    ∃ L : List (Finset (Fin n)), (L : Multiset (Finset (Fin n))) = C ∧
      L.map Finset.card = sizes := by
  induction sizes generalizing C with
  | nil =>
      have hC : C = 0 := Multiset.map_eq_zero.mp h
      exact ⟨[], hC.symm, rfl⟩
  | cons a sizes ih =>
      obtain ⟨A, hA, hcA, htail⟩ :=
        (Multiset.map_eq_cons Finset.card C (sizes : Multiset ℕ) a).mpr h
      obtain ⟨L, hL, hm⟩ := ih (C.erase A) htail
      refine ⟨A :: L, ?_, ?_⟩
      · change A ::ₘ (L : Multiset (Finset (Fin n))) = C
        rw [hL, Multiset.cons_erase hA]
      · simp only [List.map_cons, hcA, hm]

/-- Recover witnesses in the prescribed column order from the actual
multiset of lengths. This is an explicit enumeration, not a cardinal estimate. -/
theorem CochargeRealizes.orderedWitness {n m : ℕ} {w : Fin n → ℕ}
    {ell : Fin m → ℕ} (h : CochargeRealizes w (List.ofFn ell : Multiset ℕ)) :
    Nonempty (ColumnCochargeWitness w ell) := by
  obtain ⟨C, hp, hv, hm⟩ := h
  obtain ⟨L, hL, hmap⟩ := exists_list_with_card_map C (List.ofFn ell) hm
  have hlen : L.length = m := by
    have hh := congrArg List.length hmap
    simpa only [List.length_map, List.length_ofFn] using hh
  have hpair : L.Pairwise (fun A B => Disjoint A B) := by
    rw [← hL] at hp
    exact Multiset.pairwise_coe_iff_pairwise.mp hp
  let index (j : Fin m) : Fin L.length := ⟨j.val, by omega⟩
  refine ⟨{ columns := fun j => L.get (index j), disjoint := ?_, card_eq := ?_, admissible := ?_ }⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hpair.rel_get_of_lt (show index i < index j from hij)
    · exact (hpair.rel_get_of_lt (show index j < index i from hji)).symm
  · intro j
    have hjL : j.val < L.length := (index j).isLt
    have hh := congrArg (fun l : List ℕ => l[j.val]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hjL,
      Option.map_some, List.getElem?_ofFn, dif_pos j.isLt, Option.some.injEq] at hh
    change (L[j.val] : Finset (Fin n)).card = ell j
    exact hh
  · intro j
    apply (hv _ ?_).1
    rw [← hL]
    exact List.get_mem L (index j)

/-- A positive ordered column family gives its genuine cardinality multiset. -/
theorem ColumnCochargeWitness.realizes {n m : ℕ} {w : Fin n → ℕ}
    {ell : Fin m → ℕ} (W : ColumnCochargeWitness w ell) (hpos : ∀ j, 0 < ell j) :
    CochargeRealizes w (List.ofFn ell : Multiset ℕ) := by
  refine ⟨(List.ofFn W.columns : Multiset (Finset (Fin n))), ?_, ?_, ?_⟩
  · apply Multiset.pairwise_coe_iff_pairwise.mpr
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact W.disjoint hij.ne
  · intro A hA
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hA
    exact ⟨W.admissible j, card_pos.mp (by rw [W.card_eq]; exact hpos j)⟩
  · change ((List.ofFn W.columns).map Finset.card : Multiset ℕ) = _
    rw [List.map_ofFn]
    exact congrArg (fun f : Fin m → ℕ => (List.ofFn f : Multiset ℕ))
      (funext W.card_eq)

theorem ofFn_colLen_eq_transpose_rowLens (mu : YoungDiagram) :
    List.ofFn (fun j : Fin (mu.rowLen 0) => mu.colLen j.val) = mu.transpose.rowLens := by
  apply List.ext_getElem
  · simp [YoungDiagram.rowLens]
  · intro i hi hj
    simp [YoungDiagram.rowLens]

theorem diagram_dominates_toPartition {n : ℕ} {mu lam : YoungDiagram}
    (hmu : mu.card = n) (hlam : lam.card = n) (hdom : Dominates mu lam) :
    (mu.toPartition hmu).Dominates (lam.toPartition hlam) := by
  apply Nat.Partition.dominates_iff.mpr
  intro r
  rw [← YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    ← YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    YoungDiagram.ofPartition_toPartition, YoungDiagram.ofPartition_toPartition]
  rw [YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
  exact hdom r

/-- The full equal-size column-witness converse used for the actual augmented
Griffin word. The word, its output, dominance and size are literal; all missing
cocharge and redistribution claims are proved above. -/
theorem exists_columns_of_wordOutput_dominates {n : ℕ} {w : Fin n → ℕ}
    {mu lam : YoungDiagram} (houtput : CatWordOutput (List.ofFn w) mu)
    (hdom : Dominates mu lam) (hcard : lam.card = n) :
    Nonempty (ColumnCochargeWitness w
      (fun j : Fin (lam.rowLen 0) => lam.colLen j.val)) := by
  have hmu : mu.card = n := by simpa only [List.length_ofFn] using catWordOutput_card houtput
  obtain ⟨W⟩ := exists_columns_of_wordOutput houtput
  have hpos (j : Fin (mu.rowLen 0)) : 0 < mu.colLen j.val :=
    YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)
  have hreal : CochargeRealizes w (mu.toPartition hmu).conjugate.parts := by
    rw [Nat.Partition.conjugate_parts, YoungDiagram.ofPartition_toPartition,
      ← ofFn_colLen_eq_transpose_rowLens]
    exact W.realizes hpos
  have htarget := hreal.of_dominates (diagram_dominates_toPartition hmu hcard hdom).conjugate
  rw [Nat.Partition.conjugate_parts, YoungDiagram.ofPartition_toPartition,
    ← ofFn_colLen_eq_transpose_rowLens] at htarget
  exact htarget.orderedWitness

end HigherSpecht
end
end CanonicalSource28

section CanonicalSource29
/- Source: HigherSpecht/CochargeColumnRelocation.lean -/



/-!
# Relocating column witnesses into the first reading positions

This proves the finite exchange argument in Chou--Hanada, Proposition 4.4.
Among the actual column witnesses choose one with minimal sum of stable
reading ranks. If it misses an initial reading position, replace a globally
largest selected rank by that position. The literal rightmost-maximum lemma
preserves its column, while the rank sum strictly decreases. No counting or
catabolism-image theorem is used here.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def readingPrefix {n : ℕ} (rank : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    Finset (Fin n) :=
  univ.image (fun i : Fin k => rank.symm ⟨i.val, i.isLt.trans_le hk⟩)

@[simp] theorem mem_readingPrefix {n : ℕ} (rank : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n) (i : Fin n) :
    i ∈ readingPrefix rank k hk ↔ (rank i).val < k := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    simpa only [Equiv.apply_symm_apply] using j.isLt
  · intro hi
    refine mem_image.mpr ⟨⟨(rank i).val, hi⟩, mem_univ _, ?_⟩
    have heq : (⟨(rank i).val, hi.trans_le hk⟩ : Fin n) = rank i := Fin.ext rfl
    rw [heq, Equiv.symm_apply_apply]

@[simp] theorem readingPrefix_card {n : ℕ} (rank : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n) : (readingPrefix rank k hk).card = k := by
  unfold readingPrefix
  rw [card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin n => z.val) (rank.symm.injective hij)

theorem ColumnCochargeWitness.exists_readingPrefix {n m s : ℕ}
    (u : Fin n → Fin s) (ell : Fin m → ℕ) (k : ℕ)
    (hk : k ≤ n) (hsum : ∑ j, ell j = k)
    (W : ColumnCochargeWitness (fun i => (u i).val) ell) :
    ∃ V : ColumnCochargeWitness (fun i => (u i).val) ell,
      V.selected = readingPrefix (stablePositions u).symm k hk := by
  let rank := (stablePositions u).symm
  have hex : ∃ d : ℕ, ∃ V : ColumnCochargeWitness (fun i => (u i).val) ell,
      V.rankSum rank = d := ⟨W.rankSum rank, W, rfl⟩
  obtain ⟨V, hV⟩ := Nat.find_spec hex
  refine ⟨V, ?_⟩
  have hcard : V.selected.card = k := V.selected_card.trans hsum
  have hsub : V.selected ⊆ readingPrefix rank k hk := by
    by_contra hbad
    obtain ⟨outside, hout, houtP⟩ := Finset.not_subset.mp hbad
    have houtRank : k ≤ (rank outside).val := by
      exact Nat.le_of_not_gt (fun h => houtP ((mem_readingPrefix rank k hk outside).mpr h))
    obtain ⟨r, hr, hmaxRank⟩ := V.selected.exists_max_image (fun i => (rank i).val) ⟨outside, hout⟩
    have hrRank : k ≤ (rank r).val := houtRank.trans (hmaxRank outside hout)
    have hprefixNotSub : ¬ readingPrefix rank k hk ⊆ V.selected := by
      intro hPS
      have heq : readingPrefix rank k hk = V.selected :=
        Finset.eq_of_subset_of_card_le hPS (by rw [hcard, readingPrefix_card])
      have : outside ∈ readingPrefix rank k hk := heq.symm ▸ hout
      exact houtP this
    obtain ⟨t, htP, ht⟩ := Finset.not_subset.mp hprefixNotSub
    have htRank : (rank t).val < k := (mem_readingPrefix rank k hk t).mp htP
    obtain ⟨j, hrj⟩ := (V.mem_selected r).mp hr
    have hmax (i : Fin n) (hi : i ∈ V.columns j) : (u i).val ≤ (u r).val := by
      exact stableRank_value_le u (hmaxRank i (V.column_subset_selected j hi))
    have hright (i : Fin n) (hi : i ∈ V.columns j)
        (heq : (u i).val = (u r).val) : i ≤ r := by
      exact stableRank_position_le_of_value_eq u
        (hmaxRank i (V.column_subset_selected j hi)) heq
    have htrRank : rank t < rank r := by change (rank t).val < (rank r).val; omega
    have htval : (u t).val ≤ (u r).val := stableRank_value_le u htrRank.le
    have httie : (u t).val = (u r).val → t < r := by
      intro hval
      rcases (stableRank_lt_iff u t r).mp htrRank with hlt | ⟨_, hpos⟩
      · have : (u t).val < (u r).val := hlt
        omega
      · exact hpos
    let V' := V.exchange j r t hrj ht hmax hright htval httie
    have heq := V.exchange_rankSum j r t hrj ht hmax hright htval httie rank
    change V'.rankSum rank + (rank r).val = V.rankSum rank + (rank t).val at heq
    have hmin : Nat.find hex ≤ V'.rankSum rank := Nat.find_min' hex ⟨V', rfl⟩
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, readingPrefix_card])

/-- The first `k` boosts of the actual bounded-word code vanish after the
column witnesses have been relocated. -/
theorem ColumnCochargeWitness.prefix_boost_zero {n m s : ℕ}
    (u : Fin n → Fin s) (ell : Fin m → ℕ) (k : ℕ)
    (hk : k ≤ n) (hsum : ∑ j, ell j = k)
    (W : ColumnCochargeWitness (fun i => (u i).val) ell) :
    ∀ i : Fin n, i.val < k → stableBoost u i = 0 := by
  obtain ⟨V, hV⟩ := W.exists_readingPrefix u ell k hk hsum
  intro i hi
  have hmem : stablePositions u i ∈ V.selected := by
    rw [hV, mem_readingPrefix]
    simpa only [Equiv.symm_apply_apply] using hi
  simpa only [Equiv.symm_apply_apply] using
    stableBoost_eq_zero_of_selected_cochargeWord u V.selected_admissible
      (stablePositions u i) hmem

end HigherSpecht
end
end CanonicalSource29

section CanonicalSource30
/- Source: HigherSpecht/CochargeColumnRestriction.lean -/



/-!
# Restriction of actual column witnesses to their selected positions

An increasing enumeration keeps every repeated-letter position and preserves
the literal selected subwords. The full-cover version then applies the actual
shuffle execution theorem, with the reversal between word and scan order
proved explicitly.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

theorem selectedPositions_eq_sort {n : ℕ} (C : Finset (Fin n)) :
    (List.finRange n).filter (fun i => decide (i ∈ C)) = C.sort := by
  have hs := (List.Pairwise.filter (fun i => decide (i ∈ C))
    (List.sortedLT_finRange n).pairwise).sortedLT
  apply hs.eq_of_mem_iff C.sortedLT_sort
  intro i
  simp

theorem selectedWord_eq_sort {n : ℕ} (a : Fin n → ℕ) (C : Finset (Fin n)) :
    selectedWord a C = C.sort.map a := by
  rw [selectedWord, selectedPositions_eq_sort]

@[simp] theorem selectedWord_length {n : ℕ} (a : Fin n → ℕ) (C : Finset (Fin n)) :
    (selectedWord a C).length = C.card := by
  rw [selectedWord_eq_sort, List.length_map, Finset.length_sort]

theorem selectedWord_orderEmbedding {n k : ℕ} (a : Fin n → ℕ)
    (e : Fin k ↪o Fin n) (C : Finset (Fin n))
    (hC : ∀ i ∈ C, ∃ j, e j = i) :
    selectedWord (fun j => a (e j)) (univ.filter (fun j => e j ∈ C)) =
      selectedWord a C := by
  let L := (List.finRange k).filter (fun j => decide (e j ∈ C))
  have hsL : L.Pairwise (· < ·) :=
    List.Pairwise.filter _ (List.sortedLT_finRange k).pairwise
  have hsM : (L.map e).SortedLT := by
    apply List.Pairwise.sortedLT
    rw [List.pairwise_map]
    exact hsL.imp (fun h => e.strictMono h)
  have heq : L.map e = C.sort := by
    apply hsM.eq_of_mem_iff C.sortedLT_sort
    intro i
    simp only [List.mem_map, Finset.mem_sort]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa only [L, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using hj
    · intro hi
      obtain ⟨j, rfl⟩ := hC i hi
      exact ⟨j, by simp only [L, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq]; exact hi, rfl⟩
  change (((List.finRange k).filter (fun j => decide (j ∈ univ.filter (fun j => e j ∈ C)))).map
    (fun j => a (e j))) = _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change L.map (a ∘ e) = _
  rw [← List.map_map (f := e) (g := a), heq, ← selectedWord_eq_sort]

theorem card_orderEmbedding_preimage {n k : ℕ} (e : Fin k ↪o Fin n)
    (C : Finset (Fin n)) (hC : ∀ i ∈ C, ∃ j, e j = i) :
    (univ.filter (fun j => e j ∈ C)).card = C.card := by
  have himage : (univ.filter (fun j => e j ∈ C)).image e = C := by
    ext i
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      obtain ⟨j, rfl⟩ := hC i hi
      exact ⟨j, hi, rfl⟩
  calc
    (univ.filter (fun j => e j ∈ C)).card =
        ((univ.filter (fun j => e j ∈ C)).image e).card :=
      (card_image_of_injective _ e.injective).symm
    _ = C.card := congrArg Finset.card himage

def ColumnCochargeWitness.restrict {n m k : ℕ} {a : Fin n → ℕ}
    {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell)
    (hk : W.selected.card = k) :
    ColumnCochargeWitness (fun j => a (W.selected.orderEmbOfFin hk j)) ell where
  columns l := univ.filter (fun j => W.selected.orderEmbOfFin hk j ∈ W.columns l)
  disjoint := by
    intro l t hlt
    apply disjoint_left.mpr
    intro j hjl hjt
    exact disjoint_left.mp (W.disjoint hlt) (mem_filter.mp hjl).2 (mem_filter.mp hjt).2
  card_eq l := by
    rw [card_orderEmbedding_preimage, W.card_eq]
    intro i hi
    have him := W.column_subset_selected l hi
    change i ∈ (W.selected : Set (Fin n)) at him
    have hrange := W.selected.range_orderEmbOfFin hk
    rw [← hrange] at him
    exact him
  admissible l := by
    rw [selectedWord_orderEmbedding]
    · exact W.admissible l
    · intro i hi
      have him := W.column_subset_selected l hi
      change i ∈ (W.selected : Set (Fin n)) at him
      have hrange := W.selected.range_orderEmbOfFin hk
      rw [← hrange] at him
      exact him

theorem ColumnCochargeWitness.restrict_selected {n m k : ℕ} {a : Fin n → ℕ}
    {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell)
    (hk : W.selected.card = k) : (W.restrict hk).selected = univ := by
  apply eq_univ_of_forall
  intro i
  apply ((W.restrict hk).mem_selected i).mpr
  have hi := W.selected.orderEmbOfFin_mem hk i
  obtain ⟨j, hj⟩ := (W.mem_selected _).mp hi
  exact ⟨j, mem_filter.mpr ⟨mem_univ i, hj⟩⟩

theorem ColumnCochargeWitness.restrict_word {n m k : ℕ} {a : Fin n → ℕ}
    {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell)
    (hk : W.selected.card = k) :
    List.ofFn (fun j => a (W.selected.orderEmbOfFin hk j)) = selectedWord a W.selected := by
  rw [List.ofFn_eq_map]
  change (List.finRange k).map (a ∘ W.selected.orderEmbOfFin hk) = _
  rw [← List.map_map (f := W.selected.orderEmbOfFin hk) (g := a),
    W.selected.listMap_orderEmbOfFin_finRange hk,
    ← selectedWord_eq_sort]

theorem ofFn_reverse_positions {n : ℕ} {α : Type*} (a : Fin n → α) :
    (List.ofFn (fun i => a i.rev)).reverse = List.ofFn a := by
  conv_lhs => rw [List.ofFn_eq_map]
  change ((List.finRange n).map (a ∘ Fin.rev)).reverse = List.ofFn a
  rw [← List.map_map (f := Fin.rev) (g := a), ← List.finRange_reverse,
    List.map_reverse, List.reverse_reverse, ← List.ofFn_eq_map]

theorem shuffledInputWord_reverse_positions {n : ℕ} {κ : Type*} [Fintype κ]
    (a : Fin n → ℕ) (color : Fin n → κ) (j : κ) :
    shuffledInputWord (fun i => a i.rev) (fun i => color i.rev) j =
      selectedWord a (univ.filter (fun i => color i = j)) := by
  rw [shuffledInputWord_eq]
  have hm : (((List.finRange n).filter (fun i => decide (color i.rev = j))).map
      (fun i => a i.rev)) =
      (((List.finRange n).map Fin.rev).filter (fun i => decide (color i = j))).map a := by
    simp only [List.filter_map, List.map_map, Function.comp_def]
  rw [hm, ← List.finRange_reverse, List.filter_reverse, List.map_reverse,
    List.reverse_reverse]
  simp only [selectedWord, mem_filter, mem_univ, true_and]

theorem ColumnCochargeWitness.full_dominance {n m : ℕ} {a : Fin n → ℕ}
    (lam : YoungDiagram) (hm : lam.rowLen 0 ≤ m)
    (W : ColumnCochargeWitness a (fun j : Fin m => lam.colLen j.val))
    (hfull : W.selected = univ) {mu : YoungDiagram}
    (hout : CatWordOutput (List.ofFn a) mu) : Dominates mu lam := by
  have hex : ∀ i : Fin n, ∃ j : Fin m, i ∈ W.columns j := by
    intro i
    apply (W.mem_selected i).mp
    rw [hfull]
    exact mem_univ i
  choose color hcolor using hex
  have hcolor_iff (i : Fin n) (j : Fin m) : color i = j ↔ i ∈ W.columns j := by
    constructor
    · rintro rfl
      exact hcolor i
    · intro hij
      by_contra hne
      exact disjoint_left.mp (W.disjoint hne) (hcolor i) hij
  have hcols (j : Fin m) : univ.filter (fun i => color i = j) = W.columns j := by
    ext i
    simp only [mem_filter, mem_univ, true_and, hcolor_iff]
  have hwords (j : Fin m) :
      shuffledInputWord (fun i => a i.rev) (fun i => color i.rev) j =
        selectedWord a (W.columns j) := by
    rw [shuffledInputWord_reverse_positions]
    apply congrArg (selectedWord a)
    ext i
    simp only [mem_filter, mem_univ, true_and, hcolor_iff]
  have houtputs : ∀ j : Fin m, ∃ nu : YoungDiagram,
      CatWordOutput (shuffledInputWord (fun i => a i.rev) (fun i => color i.rev) j) nu := by
    intro j
    rw [hwords]
    exact exists_catWordOutput_of_admissible
      ((isCochargeWord_iff_admissible _).mp (W.admissible j))
  choose nu hnu using houtputs
  apply catWordOutput_dominates_of_column_shuffle (fun i => a i.rev)
    (fun i => color i.rev) lam hm nu hnu
  · intro j
    simpa only [hwords, selectedWord_length, W.card_eq] using le_refl (lam.colLen j.val)
  · simpa only [ofFn_reverse_positions] using hout

/-- The actual cyclic output of the union of the selected column words
dominates the prescribed diagram, even when other ambient positions exist. -/
theorem ColumnCochargeWitness.selected_dominance {n : ℕ} {a : Fin n → ℕ}
    (lam : YoungDiagram)
    (W : ColumnCochargeWitness a (fun j : Fin (lam.rowLen 0) => lam.colLen j.val))
    {mu : YoungDiagram} (hout : CatWordOutput (selectedWord a W.selected) mu) :
    Dominates mu lam := by
  apply (W.restrict rfl).full_dominance lam le_rfl (W.restrict_selected rfl)
  simpa only [W.restrict_word rfl] using hout

end HigherSpecht
end
end CanonicalSource30

section CanonicalSource31
/- Source: HigherSpecht/BatteryColumnStrip.lean -/



/-!
# Stripping the saturated protected battery columns

Every unprotected column consists of genuine device positions: otherwise it
would intersect a protected column at a battery position.  Restriction uses
the actual increasing device embedding, so selected word order is preserved.
After removing the common saturated prefix, the literal tail partition has
the required mass and is dominated by the prescribed column partition.
The already constructed box-move transfers then produce its actual witnesses.
-/

noncomputable section
open TauCeti Finset
open scoped Classical BigOperators

namespace HigherSpecht

def afterProtectedIndex {N d : ℕ} (hdN : d ≤ N) (j : Fin (N - d)) : Fin N :=
  ⟨d + j.val, by omega⟩

@[simp] theorem afterProtectedIndex_val {N d : ℕ} (hdN : d ≤ N)
    (j : Fin (N - d)) : (afterProtectedIndex hdN j).val = d + j.val := rfl

theorem afterProtectedIndex_injective {N d : ℕ} (hdN : d ≤ N) :
    Function.Injective (afterProtectedIndex hdN) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp only [afterProtectedIndex] at hh
  omega

theorem unprotectedColumn_in_device {M n N d : ℕ} {w : Fin M → ℕ}
    {a : ℕ → ℕ} (hdN : d ≤ N)
    (V : ColumnCochargeWitness w (fun j : Fin N => a j.val))
    (e : Fin n ↪o Fin M) (battery : Fin d → Finset (Fin M))
    (hkeep : ∀ j, battery j ⊆ V.columns (Fin.castLE hdN j))
    (hcover : ∀ t, (¬ ∃ i, e i = t) → ∃ j, t ∈ battery j)
    (j : Fin (N - d)) :
    ∀ t ∈ V.columns (afterProtectedIndex hdN j), ∃ i, e i = t := by
  intro t ht
  by_contra hn
  obtain ⟨k, hk⟩ := hcover t hn
  have hne : afterProtectedIndex hdN j ≠ Fin.castLE hdN k := by
    intro he
    have hh := congrArg Fin.val he
    simp only [afterProtectedIndex_val, Fin.coe_castLE] at hh
    have := k.isLt
    omega
  exact disjoint_left.mp (V.disjoint hne) ht (hkeep k hk)

def stripProtectedColumns {M n N d : ℕ} {w : Fin M → ℕ}
    {a : ℕ → ℕ} (hdN : d ≤ N)
    (V : ColumnCochargeWitness w (fun j : Fin N => a j.val))
    (e : Fin n ↪o Fin M) (battery : Fin d → Finset (Fin M))
    (hkeep : ∀ j, battery j ⊆ V.columns (Fin.castLE hdN j))
    (hcover : ∀ t, (¬ ∃ i, e i = t) → ∃ j, t ∈ battery j) :
    ColumnCochargeWitness (fun i => w (e i))
      (fun j : Fin (N - d) => a (d + j.val)) where
  columns j := univ.filter (fun i => e i ∈ V.columns (afterProtectedIndex hdN j))
  disjoint := by
    intro i j hij
    apply disjoint_left.mpr
    intro t hti htj
    exact disjoint_left.mp
      (V.disjoint (fun h => hij (afterProtectedIndex_injective hdN h)))
      (mem_filter.mp hti).2 (mem_filter.mp htj).2
  card_eq j := by
    rw [card_orderEmbedding_preimage e _
      (unprotectedColumn_in_device hdN V e battery hkeep hcover j), V.card_eq]
    rfl
  admissible j := by
    rw [selectedWord_orderEmbedding _ e _
      (unprotectedColumn_in_device hdN V e battery hkeep hcover j)]
    exact V.admissible _

def tailColumnShape (a : ℕ → ℕ) (N d : ℕ) (ha : Antitone a) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.ofFn (fun j : Fin (N - d) => a (d + j.val)))
    (List.sortedGE_ofFn_iff.mpr (by
      intro i j hij
      exact ha (Nat.add_le_add_left hij d)))

theorem tailColumnShape_rowLen_if (a : ℕ → ℕ) (N d r : ℕ) (ha : Antitone a) :
    (tailColumnShape a N d ha).rowLen r = if r < N - d then a (d + r) else 0 := by
  by_cases hr : r < N - d
  · rw [if_pos hr]
    exact (YoungDiagram.rowLen_ofRowLens
      (w := List.ofFn (fun j : Fin (N - d) => a (d + j.val)))
      (hw := List.sortedGE_ofFn_iff.mpr (by
        intro i j hij
        exact ha (Nat.add_le_add_left hij d)))
      ⟨r, by simpa only [List.length_ofFn] using hr⟩).trans
      (by simp only [Fin.getElem_fin, List.getElem_ofFn])
  · rw [if_neg hr]
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hc : (r, 0) ∈ tailColumnShape a N d ha :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hp
    obtain ⟨h, _⟩ := YoungDiagram.mem_ofRowLens.mp hc
    exact hr (by simpa only [List.length_ofFn] using h)

theorem tailColumnShape_rowLen (a : ℕ → ℕ) (N d r : ℕ) (ha : Antitone a)
    (hzero : ∀ j, N ≤ j → a j = 0) :
    (tailColumnShape a N d ha).rowLen r = a (d + r) := by
  rw [tailColumnShape_rowLen_if]
  split_ifs with hr
  · rfl
  · exact (hzero _ (by omega)).symm

theorem tailColumnShape_height_le (a : ℕ → ℕ) (N d : ℕ) (ha : Antitone a) :
    (tailColumnShape a N d ha).colLen 0 ≤ N - d := by
  by_contra h
  have hc : (N - d, 0) ∈ tailColumnShape a N d ha :=
    YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge h)
  have hp := YoungDiagram.mem_iff_lt_rowLen.mp hc
  simpa only [tailColumnShape_rowLen_if, lt_self_iff_false, if_false,
    Nat.lt_irrefl] using hp

theorem saturated_columnPrefix {a : ℕ → ℕ} {d s : ℕ}
    (hfull : ∀ j < d, a j = s) : columnPrefixSum a d = d * s := by
  unfold columnPrefixSum
  have he : (∑ j ∈ range d, a j) = ∑ _j ∈ range d, s :=
    sum_congr rfl (fun j hj => hfull j (mem_range.mp hj))
  rw [he]
  simp only [sum_const, card_range, smul_eq_mul]

theorem saturated_columnPrefix_add {a : ℕ → ℕ} {d s : ℕ}
    (hfull : ∀ j < d, a j = s) (r : ℕ) :
    columnPrefixSum a (d + r) = d * s + columnPrefixSum (fun j => a (d + j)) r := by
  rw [columnPrefixSum, sum_range_add]
  change columnPrefixSum a d + _ = _
  rw [saturated_columnPrefix hfull]
  rfl

theorem tailColumnShape_card {a : ℕ → ℕ} {N d s : ℕ} (hdN : d ≤ N)
    (ha : Antitone a) (hfull : ∀ j < d, a j = s)
    (hzero : ∀ j, N ≤ j → a j = 0) :
    (tailColumnShape a N d ha).card + d * s = columnPrefixSum a N := by
  have hsplit := saturated_columnPrefix_add hfull (N - d)
  have hd : d + (N - d) = N := Nat.add_sub_of_le hdN
  rw [hd] at hsplit
  rw [YoungDiagram.card_eq_sum_range_rowLen _ (tailColumnShape_height_le a N d ha)]
  simp_rw [tailColumnShape_rowLen a N d _ ha hzero]
  change columnPrefixSum (fun j => a (d + j)) (N - d) + d * s = _
  omega

theorem tailColumnShape_dominated {a : ℕ → ℕ} {N d s : ℕ}
    (lam : YoungDiagram) (hheight : lam.colLen 0 ≤ s)
    (ha : Antitone a) (hfull : ∀ j < d, a j = s)
    (hzero : ∀ j, N ≤ j → a j = 0)
    (hdom : ∀ r, columnPrefixSum a r ≤
      columnPrefixSum (Lascoux.batteryContentShape lam s d).colLen r) :
    Dominates lam.transpose (tailColumnShape a N d ha) := by
  intro r
  have hh := hdom (d + r)
  rw [saturated_columnPrefix_add hfull,
    Lascoux.batteryContentShape_columnPrefix_add lam s d r hheight] at hh
  have htail : columnPrefixSum (fun j => a (d + j)) r ≤ columnPrefixSum lam.colLen r := by
    omega
  simpa only [columnPrefixSum, tailColumnShape_rowLen a N d _ ha hzero,
    YoungDiagram.rowLen_transpose] using htail

theorem ofFn_rowLen_eq_rowLens (mu : YoungDiagram) :
    List.ofFn (fun j : Fin (mu.colLen 0) => mu.rowLen j.val) = mu.rowLens := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, YoungDiagram.length_rowLens]
  · intro i hi hj
    simp only [List.getElem_ofFn, YoungDiagram.get_rowLens]

/-- Discard only the empty tail columns. Every surviving column is an actual
restriction of the original selected positions. -/
def tailShapeWitness {n N d : ℕ} {w : Fin n → ℕ} {a : ℕ → ℕ}
    (ha : Antitone a) (hzero : ∀ j, N ≤ j → a j = 0)
    (W : ColumnCochargeWitness w (fun j : Fin (N - d) => a (d + j.val))) :
    ColumnCochargeWitness w (fun j : Fin ((tailColumnShape a N d ha).colLen 0) =>
      (tailColumnShape a N d ha).rowLen j.val) where
  columns j := W.columns (Fin.castLE (tailColumnShape_height_le a N d ha) j)
  disjoint := by
    intro i j hij
    exact W.disjoint (fun h => hij (Fin.ext (congrArg (fun z : Fin (N - d) => z.val) h)))
  card_eq j := by
    rw [W.card_eq, tailColumnShape_rowLen a N d j.val ha hzero]
    rfl
  admissible j := W.admissible _

/-- Actual device columns of the prescribed original partition after the
protected prefix has been filled. The shape and word transports are proved,
not supplied as extra witness or decomposition assumptions. -/
theorem exists_device_columns_after_protected_fill {M n N d s : ℕ}
    {w : Fin M → ℕ} (lam : YoungDiagram) (hdN : d ≤ N)
    (hheight : lam.colLen 0 ≤ s) (a : ℕ → ℕ) (ha : Antitone a)
    (hfull : ∀ j < d, a j = s) (hzero : ∀ j, N ≤ j → a j = 0)
    (hmass : columnPrefixSum a N = d * s + lam.card)
    (hdom : ∀ r, columnPrefixSum a r ≤
      columnPrefixSum (Lascoux.batteryContentShape lam s d).colLen r)
    (V : ColumnCochargeWitness w (fun j : Fin N => a j.val))
    (e : Fin n ↪o Fin M) (battery : Fin d → Finset (Fin M))
    (hkeep : ∀ j, battery j ⊆ V.columns (Fin.castLE hdN j))
    (hcover : ∀ t, (¬ ∃ i, e i = t) → ∃ j, t ∈ battery j) :
    Nonempty (ColumnCochargeWitness (fun i => w (e i))
      (fun j : Fin (lam.rowLen 0) => lam.colLen j.val)) := by
  let mu := tailColumnShape a N d ha
  have hmu : mu.card = lam.card := by
    have hh := tailColumnShape_card hdN ha hfull hzero
    rw [hmass] at hh
    change mu.card + d * s = d * s + lam.card at hh
    omega
  have hlam : lam.transpose.card = lam.card := by
    simp only [YoungDiagram.card_transpose]
  let W := stripProtectedColumns hdN V e battery hkeep hcover
  let U := tailShapeWitness ha hzero W
  have hpos (j : Fin (mu.colLen 0)) : 0 < mu.rowLen j.val :=
    YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr j.isLt)
  have hr : CochargeRealizes (fun i => w (e i)) (mu.toPartition hmu).parts := by
    rw [YoungDiagram.toPartition_parts, ← ofFn_rowLen_eq_rowLens]
    exact U.realizes hpos
  have hd : Dominates lam.transpose mu :=
    tailColumnShape_dominated lam hheight ha hfull hzero hdom
  have htarget := hr.of_dominates (diagram_dominates_toPartition hlam hmu hd)
  rw [YoungDiagram.toPartition_parts, ← ofFn_colLen_eq_transpose_rowLens] at htarget
  exact htarget.orderedWitness

end HigherSpecht
end
end CanonicalSource31

section CanonicalSource32
/- Source: HigherSpecht/BatteryProtectedColumns.lean -/



/-!
# The protected battery columns give actual device witnesses

This assembly uses the literal token locations of the initial rectangular
scan.  Its protected position sets are explicit images of row indices.
The entire numerical filling chain is implemented on actual cocharge
subwords, after which the unprotected columns are restricted to the device.
The terminal-scan provenance is supplied by its separate execution theorem.
-/

noncomputable section
open TauCeti Finset
open scoped Classical BigOperators

namespace HigherSpecht

def batteryPosition {h d M : ℕ} (hdM : h * d ≤ M) (r : Fin h) (j : Fin d) : Fin M :=
  Fin.rev ⟨r.val * d + j.val, by
    have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt r.isLt)
    rw [Nat.succ_mul] at h
    have := j.isLt
    omega⟩

@[simp] theorem batteryPosition_eq {h d M : ℕ} (hdM : h * d ≤ M)
    (r : Fin h) (j : Fin d) (hi : r.val * d + j.val < M) :
    batteryPosition hdM r j = Fin.rev ⟨r.val * d + j.val, hi⟩ := rfl

def batteryPositions {h d M : ℕ} (hdM : h * d ≤ M) (j : Fin d) : Finset (Fin M) :=
  univ.image (fun r : Fin h => batteryPosition hdM r j)

theorem batteryPosition_injective {h d M : ℕ} (hdM : h * d ≤ M) (j : Fin d) :
    Function.Injective (fun r : Fin h => batteryPosition hdM r j) := by
  intro r t hrt
  have hh := congrArg (fun x : Fin M => (Fin.rev x).val) hrt
  simp only [batteryPosition, Fin.rev_rev] at hh
  apply Fin.ext
  have hd := Nat.zero_lt_of_lt j.isLt
  exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_right_cancel hh)

theorem batteryPositions_card {h d M : ℕ} (hdM : h * d ≤ M) (j : Fin d) :
    (batteryPositions hdM j).card = h := by
  rw [batteryPositions, card_image_of_injective _ (batteryPosition_injective hdM j),
    card_univ, Fintype.card_fin]

def initialDeviceEmbedding {n M : ℕ} (hnM : n ≤ M) : Fin n ↪o Fin M where
  toFun := Fin.castLE hnM
  inj' := Fin.castLE_injective hnM
  map_rel_iff' := Iff.rfl

@[simp] theorem initialDeviceEmbedding_apply {n M : ℕ} (hnM : n ≤ M) (i : Fin n) :
    initialDeviceEmbedding hnM i = Fin.castLE hnM i := rfl

theorem batteryPositions_cover {n h d M : ℕ} (hM : M = n + h * d)
    (hdM : h * d ≤ M) (hnM : n ≤ M) (t : Fin M)
    (ht : ¬ ∃ i, initialDeviceEmbedding hnM i = t) :
    ∃ j : Fin d, t ∈ batteryPositions hdM j := by
  have hnt : n ≤ t.val := by
    by_contra h
    apply ht
    exact ⟨⟨t.val, Nat.lt_of_not_ge h⟩, Fin.ext rfl⟩
  let z := (Fin.rev t).val
  have hz : z < h * d := by
    dsimp only [z]
    simp only [Fin.val_rev]
    have := t.isLt
    omega
  have hd : 0 < d := by
    by_contra hzero
    have he : d = 0 := by omega
    simpa only [he, Nat.mul_zero, Nat.not_lt_zero] using hz
  let j : Fin d := ⟨z % d, Nat.mod_lt z hd⟩
  let r : Fin h := ⟨z / d, (Nat.div_lt_iff_lt_mul hd).mpr hz⟩
  refine ⟨j, mem_image.mpr ⟨r, mem_univ _, ?_⟩⟩
  apply Fin.rev_injective
  simp only [batteryPosition, Fin.rev_rev]
  apply Fin.ext
  dsimp only [r, j, z]
  exact Nat.div_add_mod' _ _

theorem columnPrefixSum_colLen_eq_card (mu : YoungDiagram) {N : ℕ}
    (hN : mu.rowLen 0 ≤ N) : columnPrefixSum mu.colLen N = mu.card := by
  have h := YoungDiagram.card_eq_sum_range_rowLen mu.transpose
    (N := N) (by simpa only [YoungDiagram.colLen_transpose] using hN)
  simpa only [YoungDiagram.card_transpose, YoungDiagram.rowLen_transpose,
    columnPrefixSum] using h.symm

theorem colLen_zero_of_width_le (mu : YoungDiagram) {j : ℕ}
    (hj : mu.rowLen 0 ≤ j) : mu.colLen j = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  have hc : (0, j) ∈ mu := YoungDiagram.mem_iff_lt_colLen.mpr hp
  exact (Nat.not_lt_of_ge hj) (YoungDiagram.mem_iff_lt_rowLen.mp hc)

theorem Dominates.columnPrefix_reverse {n : ℕ} {mu rho : YoungDiagram}
    (hmu : mu.card = n) (hrho : rho.card = n) (hdom : Dominates mu rho) (r : ℕ) :
    columnPrefixSum mu.colLen r ≤ columnPrefixSum rho.colLen r := by
  have hh := Nat.Partition.dominates_iff.mp
    (diagram_dominates_toPartition hmu hrho hdom).conjugate r
  rw [Nat.Partition.conjugate_parts_sort, Nat.Partition.conjugate_parts_sort,
    YoungDiagram.ofPartition_toPartition, YoungDiagram.ofPartition_toPartition,
    YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst] at hh
  simpa only [columnPrefixSum, YoungDiagram.rowLen_transpose] using hh

theorem ScheduledFilling.batteryPositions_subset {h d M : ℕ}
    {w : Fin M → ℕ} (hdM : h * d ≤ M)
    (F : ScheduledFilling (fun i => w (Fin.rev i)))
    (hcell : ∀ (r : Fin h) (j : Fin d),
      (F.token.symm (Fin.rev (batteryPosition hdM r j))).val = (r.val, j.val))
    (hdN : d ≤ F.shape.rowLen 0) (j : Fin d) :
    batteryPositions hdM j ⊆ F.columnCochargeWitness.columns (Fin.castLE hdN j) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := mem_image.mp ht
  let c := F.token.symm (Fin.rev (batteryPosition hdM r j))
  apply (mem_columnLabels F.wordEmbedding j.val _).mpr
  refine ⟨c, ?_, ?_⟩
  · exact congrArg Prod.snd (hcell r j)
  · simp only [ScheduledFilling.wordEmbedding_apply, c, Equiv.apply_symm_apply,
      Fin.rev_rev]

/-- The literal first rectangular scan, together with the actual output
dominance, suffices for all prescribed device columns.  Every transfer and
the final position restriction are constructed in the proof. -/
theorem ScheduledFilling.device_columns_of_battery {n d M s : ℕ}
    (lam : YoungDiagram) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hM : M = n + (s - 1) * d)
    (hrho : (Lascoux.batteryContentShape lam s d).card = M)
    {w : Fin M → ℕ} (F : ScheduledFilling (fun i => w (Fin.rev i)))
    (hdom : Dominates F.shape (Lascoux.batteryContentShape lam s d))
    (hFheight : F.shape.colLen 0 ≤ s)
    (hcell : ∀ (r : Fin (s - 1)) (j : Fin d),
      (F.token.symm (Fin.rev (batteryPosition (show (s - 1) * d ≤ M by omega) r j))).val =
        (r.val, j.val))
    (hlabel : ∀ (r : Fin (s - 1)) (j : Fin d),
      w (batteryPosition (show (s - 1) * d ≤ M by omega) r j) = r.val) :
    Nonempty (ColumnCochargeWitness
      (fun i : Fin n => w (initialDeviceEmbedding (show n ≤ M by omega) i))
      (fun j : Fin (lam.rowLen 0) => lam.colLen j.val)) := by
  let N := F.shape.rowLen 0
  let rho := Lascoux.batteryContentShape lam s d
  have hwidth : rho.rowLen 0 ≤ N := by
    have hh := hdom 1
    simpa only [sum_range_one] using hh
  have hdN : d ≤ N := by
    have he := Lascoux.batteryContentShape_rowLen lam s d 0
    rw [if_pos hs] at he
    change rho.rowLen 0 = _ at he
    omega
  have hFcard : F.shape.card = M := by
    have hh := Fintype.card_congr F.token
    simpa only [Fintype.card_coe, Fintype.card_fin, YoungDiagram.card] using hh
  have hzero : ∀ j, N ≤ j → F.shape.colLen j = 0 := by
    intro j hj
    exact colLen_zero_of_width_le F.shape hj
  have hprefix : ∀ r, columnPrefixSum F.shape.colLen r ≤ columnPrefixSum rho.colLen r :=
    Dominates.columnPrefix_reverse hFcard hrho hdom
  have hmass : columnPrefixSum F.shape.colLen N = columnPrefixSum rho.colLen N := by
    rw [columnPrefixSum_colLen_eq_card F.shape le_rfl,
      columnPrefixSum_colLen_eq_card rho hwidth, hFcard, hrho]
  let hdM : (s - 1) * d ≤ M := by omega
  let battery : Fin d → Finset (Fin M) := batteryPositions hdM
  let W := F.columnCochargeWitness
  have hkeep : ∀ j, battery j ⊆ W.columns (Fin.castLE hdN j) :=
    F.batteryPositions_subset hdM hcell hdN
  have hprotected : ∀ j < d, s - 1 ≤ F.shape.colLen j := by
    intro j hj
    have hh := card_le_card (hkeep ⟨j, hj⟩)
    rw [batteryPositions_card, W.card_eq] at hh
    exact hh
  have halphabet : ∀ j (r : ℕ), r < s - 1 → ∃ t ∈ battery j, w t = r := by
    intro j r hr
    refine ⟨batteryPosition hdM ⟨r, hr⟩ j, mem_image.mpr ⟨⟨r, hr⟩, mem_univ _, rfl⟩, ?_⟩
    exact hlabel ⟨r, hr⟩ j
  obtain ⟨a, hchain, ha, hfull, hz, hm, hmajor⟩ :=
    exists_protected_column_fill hdN F.shape.colLen rho.colLen
      (fun i j hij => F.shape.colLen_anti i j hij)
      (fun i j hij => rho.colLen_anti i j hij)
      (fun j => (F.shape.colLen_anti 0 j (Nat.zero_le j)).trans hFheight)
      hprotected (fun j hj => by
        rw [Lascoux.batteryContentShape_colLen lam s d j hheight, if_pos hj])
      hzero hmass hprefix
  obtain ⟨V, hV, hselected⟩ := W.protected_chain hdN battery hkeep halphabet hchain
  have hmass' : columnPrefixSum a N = d * s + lam.card := by
    rw [hm, columnPrefixSum_colLen_eq_card rho hwidth,
      Lascoux.batteryContentShape_card lam s d hheight]
    rw [Nat.mul_comm s d]
  exact exists_device_columns_after_protected_fill lam hdN hheight a ha hfull hz hmass'
    hmajor V (initialDeviceEmbedding (show n ≤ M by omega)) battery hV
    (batteryPositions_cover hM hdM (show n ≤ M by omega))

end HigherSpecht
end
end CanonicalSource32

section CanonicalSource33
/- Source: HigherSpecht/EligibleIndexCountWordRestriction.lean -/



/-!
# Exact bounded-word realization of every Griffin index

The unrestricted word standardization has already been constructed. Restricting
it to a nonempty partition imposes two literal conditions: the first `|lam|`
boosts vanish, and the actual first-label insertion tableau has the prescribed
catabolism dominance. The rectangle length is proved equivalent to the former
condition. This file is an exact index equivalence, not a proof that the number
of such words equals the staircase dimension.
-/

noncomputable section
open TauCeti
open scoped Classical

namespace HigherSpecht

theorem multiplier_height_iff_prefix_boost_zero (eta : YoungDiagram)
    {n k : ℕ} (hk : k ≤ n) (heta : eta.colLen 0 ≤ n) :
    eta.colLen 0 ≤ n - k ↔ ∀ i : Fin n, i.val < k → boostLabel eta n i = 0 := by
  constructor
  · intro hlen i hi
    exact boostLabel_eq_zero_on_prefix eta hk hlen i hi
  · intro hzero
    by_cases hk0 : k = 0
    · simpa only [hk0, Nat.sub_zero] using heta
    by_contra hlen
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let i : Fin n := ⟨k - 1, by omega⟩
    have hi : i.val < k := by dsimp [i]; omega
    have hz := hzero i hi
    have hc : (n - k, 0) ∈ eta :=
      YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge hlen)
    have hp : 0 < eta.rowLen (n - k) := YoungDiagram.mem_iff_lt_rowLen.mp hc
    have hind : n - 1 - i.val = n - k := by dsimp [i]; omega
    simp only [boostLabel, hind] at hz
    exact (Nat.ne_of_gt hp) hz

theorem partitionOfBoost_height_iff {n k : ℕ} (hk : k ≤ n)
    (b : Fin n → ℕ) (hb : Monotone b) :
    (partitionOfBoost b hb).colLen 0 ≤ n - k ↔ ∀ i : Fin n, i.val < k → b i = 0 := by
  rw [multiplier_height_iff_prefix_boost_zero _ hk (partitionOfBoost_height b hb)]
  simp only [boostLabel_partitionOfBoost]

def restrictedEmptyIndex {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) :=
  {i : GriffinIndex n ⊥ (by simp [YoungDiagram.card]) s //
    prefixEligible lam hk i.pair ∧ i.multiplier.colLen 0 ≤ n - lam.card}

def griffinRestrictedEmptyEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    GriffinIndex n lam hk s ≃ restrictedEmptyIndex lam hk s where
  toFun i :=
    ⟨{ pair := i.pair
       multiplier := i.multiplier
       eligible := prefixEligible_bot i.pair
       descents_lt := i.descents_lt
       multiplier_length := by
         simpa only [YoungDiagram.card, YoungDiagram.cells_bot, Finset.card_empty,
           Nat.sub_zero] using i.multiplier_length.trans (Nat.sub_le n lam.card)
       multiplier_width := i.multiplier_width }, i.eligible, i.multiplier_length⟩
  invFun i :=
    { pair := i.val.pair
      multiplier := i.val.multiplier
      eligible := i.property.1
      descents_lt := i.val.descents_lt
      multiplier_length := i.property.2
      multiplier_width := i.val.multiplier_width }
  left_inv i := by cases i; rfl
  right_inv i := by rcases i with ⟨i, hi⟩; cases i; rfl

def CochargeCodeEligible {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    {s : ℕ} (c : BoundedCochargeCode n s) : Prop :=
  prefixEligible lam hk (rskPair n c.permutation) ∧
    ∀ i : Fin n, i.val < lam.card → c.boost i = 0

def codeGriffinEmptyEquiv (n s : ℕ) (hs : 0 < s) :
    BoundedCochargeCode n s ≃ GriffinIndex n ⊥ (by simp [YoungDiagram.card]) s :=
  (codeRectangleEquiv n s hs).trans (rectangleGriffinEmptyEquiv n s)

@[simp] theorem codeGriffinEmptyEquiv_pair {n s : ℕ} (hs : 0 < s)
    (c : BoundedCochargeCode n s) :
    (codeGriffinEmptyEquiv n s hs c).pair = rskPair n c.permutation := rfl

@[simp] theorem codeGriffinEmptyEquiv_multiplier {n s : ℕ} (hs : 0 < s)
    (c : BoundedCochargeCode n s) :
    (codeGriffinEmptyEquiv n s hs c).multiplier = partitionOfBoost c.boost c.boost_mono := rfl

def eligibleCodeRestrictedEmptyEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) :
    {c : BoundedCochargeCode n s // CochargeCodeEligible lam hk c} ≃
      restrictedEmptyIndex lam hk s :=
  (codeGriffinEmptyEquiv n s hs).subtypeEquiv fun c => by
    simp only [CochargeCodeEligible, codeGriffinEmptyEquiv_pair,
      codeGriffinEmptyEquiv_multiplier, partitionOfBoost_height_iff hk]

def eligibleCodeGriffinEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) :
    {c : BoundedCochargeCode n s // CochargeCodeEligible lam hk c} ≃ GriffinIndex n lam hk s :=
  (eligibleCodeRestrictedEmptyEquiv n lam hk s hs).trans
    (griffinRestrictedEmptyEquiv n lam hk s).symm

/-- A literal bounded-word condition, expressed using the actual stable sorting
permutation and the actual first-label catabolism predicate. -/
def EligibleBoundedWord (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) :=
  {u : Fin n → Fin s // CochargeCodeEligible lam hk (encodeBoundedWord u)}

def eligibleBoundedWordCodeEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    EligibleBoundedWord n lam hk s ≃
      {c : BoundedCochargeCode n s // CochargeCodeEligible lam hk c} :=
  (boundedWordCochargeEquiv n s).subtypeEquiv (fun _ => Iff.rfl)

/-- Full parameter range and the exact manuscript index, with no counting or
eligibility theorem supplied as a premise. This merely realizes that index by
an explicitly specified subset of bounded words. -/
def eligibleBoundedWordGriffinEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) :
    EligibleBoundedWord n lam hk s ≃ GriffinIndex n lam hk s :=
  (eligibleBoundedWordCodeEquiv n lam hk s).trans
    (eligibleCodeGriffinEquiv n lam hk s hs)

theorem card_griffinIndex_eq_eligibleBoundedWords (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) :
    Nat.card (GriffinIndex n lam hk s) = Nat.card (EligibleBoundedWord n lam hk s) :=
  (Nat.card_congr (eligibleBoundedWordGriffinEquiv n lam hk s hs)).symm

end HigherSpecht
end
end CanonicalSource33

section CanonicalSource34
/- Source: HigherSpecht/CatPrefixTheorem.lean -/



/-!
# The manuscript's complete catabolizability restriction formula

The final assertions give every row-prefix sum and every individual row of
the actual cyclic output of the actual restricted tableau.  Their right-hand
sides are precisely retention of the first `k` boxes in row-superstandard
order.  The formula is obtained from the genuine smaller-word induction,
not by defining a replacement catabolizability statistic.
-/

noncomputable section

open TauCeti Finset Function

namespace HigherSpecht

theorem rowReadingCells_prefix_embedding {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (k : ℕ) :
    (rowReadingCells (prefixShape S k)).map (prefixCellsEmbedding S k) =
      (rowReadingCells mu).filter (fun c => (S c).val < k) := by
  let rel : ↥mu.cells → ↥mu.cells → Prop := fun c d =>
    d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 ≤ d.val.2)
  have hpL : ((rowReadingCells (prefixShape S k)).map (prefixCellsEmbedding S k)).Pairwise rel :=
    (pairwise_rowReadingCells (prefixShape S k)).map _ (fun _ _ h => h)
  have hpR : ((rowReadingCells mu).filter (fun c => (S c).val < k)).Pairwise rel :=
    (pairwise_rowReadingCells mu).filter _
  have hnL := (nodup_rowReadingCells (prefixShape S k)).map (prefixCellsEmbedding S k).injective
  have hnR := (nodup_rowReadingCells mu).filter (fun c => (S c).val < k)
  have hperm : ((rowReadingCells (prefixShape S k)).map (prefixCellsEmbedding S k)).Perm
      ((rowReadingCells mu).filter (fun c => (S c).val < k)) := by
    apply (List.perm_ext_iff_of_nodup hnL hnR).mpr
    intro c
    simp only [List.mem_map, List.mem_filter, mem_rowReadingCells, true_and]
    constructor
    · rintro ⟨d, rfl⟩
      apply decide_eq_true
      rw [prefixCellsEmbedding_apply]
      exact ((mem_prefixShape S k d.val).mp d.property).choose_spec
    · intro hc
      let d : ↥(prefixShape S k).cells :=
        ⟨c.val, (mem_prefixShape S k c.val).mpr
          ⟨c.property, by simpa only [decide_eq_true_eq] using hc⟩⟩
      exact ⟨d, Subtype.ext rfl⟩
  apply hperm.eq_of_pairwise _ hpL hpR
  intro c d _ _ hcd hdc
  apply Subtype.ext
  apply Prod.ext <;> rcases hcd with hcd | hcd <;> rcases hdc with hdc | hdc <;> omega

theorem tableauValueWord_prefix {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (k : ℕ) (hk : k ≤ mu.card) :
    tableauValueWord (prefixTableau S k hk) = (tableauValueWord S).filter (· < k) := by
  unfold tableauValueWord
  rw [List.filter_map]
  simp only [Function.comp_def]
  rw [← rowReadingCells_prefix_embedding S k, List.map_map]
  apply List.map_congr_left
  intro c hc
  exact prefixTableau_apply_val S k hk c

theorem standardWordCatShape_tableau {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    standardWordCatShape (tableauValueWord S) (tableauValueWord_perm S) =
      (columnInsertion S).state.shape := by
  have h := standardWordCatShape_output (tableauValueWord S) (tableauValueWord_perm S)
  rw [labelledWord_tableau] at h
  exact catWordOutput_unique h (columnInsertion_catTableauOutput S)

/-- Lemma 5.1, in its exact and complete row-prefix form. -/
theorem catabolizability_prefix_rowSums {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (k : ℕ) (hk : k ≤ mu.card) (r : ℕ) :
    rowPrefixSum (columnInsertion (prefixTableau S k hk)).state.shape r =
      min k (rowPrefixSum (columnInsertion S).state.shape r) := by
  have h := standardWordCatShape_prefix mu.card (tableauValueWord S) (tableauValueWord_perm S) k hk r
  have hprefixperm : (tableauValueWord (prefixTableau S k hk)).Perm (List.range k) := by
    rw [tableauValueWord_prefix]
    exact standardWord_filter_perm (tableauValueWord_perm S) hk
  have hshape := standardWordCatShape_congr
    (standardWord_filter_perm (tableauValueWord_perm S) hk) hprefixperm
    (tableauValueWord_prefix S k hk).symm
  rw [hshape, standardWordCatShape_tableau S] at h
  have hleft : standardWordCatShape (tableauValueWord (prefixTableau S k hk))
      hprefixperm =
      (columnInsertion (prefixTableau S k hk)).state.shape := by
    have h' := standardWordCatShape_tableau (prefixTableau S k hk)
    simpa only [prefixShape_card S k hk] using h'
  rwa [hleft] at h

theorem rowPrefixSum_succ (nu : YoungDiagram) (r : ℕ) :
    rowPrefixSum nu (r + 1) = rowPrefixSum nu r + nu.rowLen r := by
  exact Finset.sum_range_succ _ _

/-- Each output row is retained in full until the cutoff, then one remaining
row is shortened, and all later rows vanish. This is the paper's stated
row-superstandard truncation formula. -/
theorem catabolizability_prefix_rowLen {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (k : ℕ) (hk : k ≤ mu.card) (r : ℕ) :
    (columnInsertion (prefixTableau S k hk)).state.shape.rowLen r =
      min ((columnInsertion S).state.shape.rowLen r)
        (k - rowPrefixSum (columnInsertion S).state.shape r) := by
  have h0 := catabolizability_prefix_rowSums S k hk r
  have h1 := catabolizability_prefix_rowSums S k hk (r + 1)
  rw [rowPrefixSum_succ, rowPrefixSum_succ, h0] at h1
  omega

theorem rowPrefixSum_le_card (nu : YoungDiagram) (r : ℕ) : rowPrefixSum nu r ≤ nu.card := by
  rw [rowPrefixSum, YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Equal-size eligibility after restriction is equivalently dominance of
the original output over the smaller partition. -/
theorem catDominates_prefix_iff {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (lam : YoungDiagram) (hk : lam.card ≤ mu.card) :
    CatDominates (prefixTableau S lam.card hk) lam ↔
      Dominates (columnInsertion S).state.shape lam := by
  rw [← columnInsertion_dominates_iff]
  constructor
  · intro h r
    have hr := h r
    change rowPrefixSum lam r ≤ rowPrefixSum _ r at hr
    rw [catabolizability_prefix_rowSums] at hr
    exact hr.trans (min_le_right _ _)
  · intro h r
    change rowPrefixSum lam r ≤ rowPrefixSum _ r
    rw [catabolizability_prefix_rowSums]
    exact le_min (rowPrefixSum_le_card lam r) (h r)

end HigherSpecht
end
end CanonicalSource34

section CanonicalSource35
/- Source: HigherSpecht/GeneralizedDescentToGriffin.lean -/



/-!
# The actual inverse map from generalized descent words to Griffin indices

This is the inverse construction in Chou--Hanada, Proposition 4.4. Reading
order, the permutation, all boost entries, the multiplier rectangle, and the
first-label catabolism condition are the previously defined literal ones.
The result is an injection of the manuscript's words (written in unreversed
cocharge order) into its full index set. It contains no dimension or counting
premise and does not itself assert the missing battery count.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

theorem sum_fin_colLen (lam : YoungDiagram) :
    (∑ j : Fin (lam.rowLen 0), lam.colLen j.val) = lam.card := by
  rw [Fin.sum_univ_eq_sum_range]
  have h := YoungDiagram.card_eq_sum_range_rowLen lam.transpose
    (N := lam.rowLen 0) (by simpa only [YoungDiagram.colLen_transpose] using
      (le_refl (lam.rowLen 0)))
  simpa only [YoungDiagram.card_transpose, YoungDiagram.rowLen_transpose] using h.symm

def GeneralizedDescentWord (n : ℕ) (lam : YoungDiagram) (s : ℕ) :=
  {u : Fin n → Fin s // Nonempty
    (ColumnCochargeWitness (fun i => (u i).val)
      (fun j : Fin (lam.rowLen 0) => lam.colLen j.val))}

instance (n : ℕ) (lam : YoungDiagram) (s : ℕ) : Finite (GeneralizedDescentWord n lam s) :=
  inferInstanceAs (Finite {u : Fin n → Fin s // _})

theorem permutationValueWord_perm_range {n : ℕ} (sigma : Equiv.Perm (Fin n)) :
    (permutationValueWord sigma).Perm (List.range n) := by
  exact (rskPair_left_valueWord_knuth sigma).perm.trans
    (by simpa only [(rskPair n sigma).card_eq] using tableauValueWord_perm (rskPair n sigma).left)

theorem catWordOutput_labelledPrefix_rsk {n k : ℕ}
    (sigma : Equiv.Perm (Fin n)) (hk : k ≤ n) (nu : YoungDiagram) :
    CatWordOutput (labelledWord ((permutationValueWord sigma).filter (· < k))) nu ↔
      CatTableauOutput (prefixTableau (rskPair n sigma).left k
        (by simpa only [(rskPair n sigma).card_eq] using hk)) nu := by
  let P := rskPair n sigma
  have hkP : k ≤ P.shape.card := by simpa only [P.card_eq] using hk
  have hknuth := (rskPair_left_valueWord_knuth sigma).filter_lt k
  rw [← tableauValueWord_prefix P.left k hkP] at hknuth
  have hperm := standardWord_filter_perm (permutationValueWord_perm_range sigma) hk
  have hl := hknuth.labelledWord [] []
    (by simpa only [List.nil_append, List.append_nil] using hperm)
  simp only [List.nil_append, List.append_nil, labelledWord_tableau] at hl
  exact catWordOutput_knuth_iff hl nu

theorem labelledWord_stablePrefix_of_columns {n m s k : ℕ}
    (u : Fin n → Fin s) (ell : Fin m → ℕ) (hk : k ≤ n)
    (W : ColumnCochargeWitness (fun i => (u i).val) ell)
    (hW : W.selected = readingPrefix (stablePositions u).symm k hk) :
    labelledWord ((permutationValueWord (stablePositions u).symm).filter (· < k)) =
      selectedWord (fun i => (u i).val) W.selected := by
  rw [labelledWord_filter_lt]
  simp only [permutationValueWord, List.ofFn_eq_map, List.filter_map, List.map_map,
    Function.comp_def]
  rw [hW]
  unfold selectedWord
  simp only [mem_readingPrefix]
  apply List.map_congr_left
  intro i hi
  have him : i ∈ W.selected := by
    rw [hW, mem_readingPrefix]
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hi).2
  simpa only [positionCocharge, permutationCocharge, permutationValueWord,
    List.ofFn_eq_map] using
    positionCocharge_eq_of_selected_cochargeWord u W.selected_admissible i him

/-- The first-label eligibility and the first `|lam|` zero boosts both
follow from actual relocated column witnesses. -/
theorem encodeBoundedWord_eligible_of_columns {n s : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (u : Fin n → Fin s)
    (W : ColumnCochargeWitness (fun i => (u i).val)
      (fun j : Fin (lam.rowLen 0) => lam.colLen j.val)) :
    CochargeCodeEligible lam hk (encodeBoundedWord u) := by
  obtain ⟨V, hV⟩ := W.exists_readingPrefix u _ lam.card hk (sum_fin_colLen lam)
  obtain ⟨nu, hnu⟩ := exists_catWordOutput_of_admissible
    ((isCochargeWord_iff_admissible _).mp V.selected_admissible)
  have hdom := V.selected_dominance lam hnu
  have hlabel := labelledWord_stablePrefix_of_columns u _ hk V hV
  have hprefix : CatTableauOutput
      (prefixTableau (rskPair n (stablePositions u).symm).left lam.card
        (by simpa only [(rskPair n (stablePositions u).symm).card_eq] using hk)) nu := by
    apply (catWordOutput_labelledPrefix_rsk (stablePositions u).symm hk nu).mp
    rwa [hlabel]
  refine ⟨⟨nu, hprefix, hdom⟩, ?_⟩
  exact W.prefix_boost_zero u _ lam.card hk (sum_fin_colLen lam)

def generalizedDescentCodeEmbedding (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    GeneralizedDescentWord n lam s ↪
      {c : BoundedCochargeCode n s // CochargeCodeEligible lam hk c} where
  toFun u := ⟨encodeBoundedWord u.val,
    encodeBoundedWord_eligible_of_columns lam hk u.val (Classical.choice u.property)⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    apply (boundedWordCochargeEquiv n s).injective
    exact congrArg Subtype.val huv

/-- An actual injection into the exact, unrestricted manuscript index.
No additional prefix, count, rectangle, or catabolism condition is assumed. -/
def generalizedDescentGriffinEmbedding (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) :
    GeneralizedDescentWord n lam s ↪ GriffinIndex n lam hk s :=
  (generalizedDescentCodeEmbedding n lam hk s).trans
    (eligibleCodeGriffinEquiv n lam hk s hs).toEmbedding

theorem card_generalizedDescent_le_griffin (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) :
    Nat.card (GeneralizedDescentWord n lam s) ≤ Nat.card (GriffinIndex n lam hk s) :=
  Nat.card_le_card_of_injective (generalizedDescentGriffinEmbedding n lam hk s hs)
    (generalizedDescentGriffinEmbedding n lam hk s hs).injective

@[simp] theorem generalizedDescentCodeEmbedding_val (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (u : GeneralizedDescentWord n lam s) :
    (generalizedDescentCodeEmbedding n lam hk s u).val = encodeBoundedWord u.val := rfl

end HigherSpecht
end
end CanonicalSource35

section CanonicalSource36
/- Source: HigherSpecht/BatteryGriffinEmbedding.lean -/



/-!
# The actual battery injection into every Griffin index set

The concrete appended input is balanced by the proved fixed-content
embedding.  The literal battery suffix has fixed cocharge and hence makes
the device code injective. Its initial terminal columns retain all battery
positions. Actual protected transfers and column stripping give the
prescribed device witnesses, which the literal inverse boost construction
turns into the complete Griffin index, including both tableaux and multiplier.
No cardinality, catabolism, or battery-placement premise is added.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht.Lascoux

theorem batteryDeviceWord_has_columns {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Nonempty (ColumnCochargeWitness (fun i => (batteryDeviceWord u hs hheight i).val)
      (fun j : Fin (lam.rowLen 0) => lam.colLen j.val)) := by
  let d := n - lam.card
  let rho := batteryContentShape lam s d
  let M := rho.card
  let w : Fin M → ℕ := fun i => wordCochargeLabel (balancedBatteryList u hs hheight)
    ((balancedBatteryWord u hs hheight).val i)
  have hw : List.ofFn w = labelledWord (balancedBatteryList u hs hheight) := by
    change List.ofFn (fun i => wordCochargeLabel (balancedBatteryList u hs hheight)
      ((balancedBatteryWord u hs hheight).val i)) =
      (List.ofFn (balancedBatteryWord u hs hheight).val).map
        (wordCochargeLabel (balancedBatteryList u hs hheight))
    exact (List.map_ofFn (f := (balancedBatteryWord u hs hheight).val)
      (g := wordCochargeLabel (balancedBatteryList u hs hheight))).symm
  have hM : M = n + (s - 1) * d := batteryContentShape_card_eq_inputLength u hs hheight
  obtain ⟨nu, hout, hdom, hnuheight⟩ := balancedBatteryList_output u hs hheight
  have houtw : CatWordOutput (List.ofFn w) nu := by rwa [hw]
  have hword : List.ofFn w = (List.ofFn w).take n ++ superstandardBatteryWord (s - 1) d := by
    rw [hw]
    exact balancedBatteryList_labelled_suffix u hs hheight
  obtain ⟨F, hF, hposition⟩ :=
    exists_scheduledFilling_of_superstandard_suffix w ((List.ofFn w).take n) hword houtw
  have hW := F.device_columns_of_battery lam hs hheight hM (show rho.card = M from rfl)
    (by rwa [hF]) (by rwa [hF])
    (fun r j => by
      obtain ⟨hi, hcell, hvisit, hlabel⟩ := hposition r.val j.val r.isLt j.isLt
      rw [batteryPosition_eq _ r j hi, Fin.rev_rev]
      exact hcell)
    (fun r j => by
      obtain ⟨hi, hcell, hvisit, hlabel⟩ := hposition r.val j.val r.isLt j.isLt
      rw [batteryPosition_eq _ r j hi]
      exact hlabel)
  simpa only [w, batteryDeviceWord, initialDeviceEmbedding_apply] using hW

/-- The complete actual input-word injection, with the device eligibility
proved above from the genuine terminal insertion filling. -/
def batteryGeneralizedDescentEmbedding (n : ℕ) (lam : YoungDiagram) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ContentWord n lam s ↪ GeneralizedDescentWord n lam s where
  toFun u := ⟨batteryDeviceWord u hs hheight, batteryDeviceWord_has_columns u hs hheight⟩
  inj' := by
    intro u v huv
    exact batteryDeviceWord_injective hs hheight (congrArg Subtype.val huv)

def contentWordGriffinEmbedding (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ContentWord n lam s ↪ GriffinIndex n lam hk s :=
  (batteryGeneralizedDescentEmbedding n lam s hs hheight).trans
    (generalizedDescentGriffinEmbedding n lam hk s hs)

theorem card_contentWord_le_griffin (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Nat.card (ContentWord n lam s) ≤ Nat.card (GriffinIndex n lam hk s) :=
  Nat.card_le_card_of_injective (contentWordGriffinEmbedding n lam hk s hs hheight)
    (contentWordGriffinEmbedding n lam hk s hs hheight).injective

end HigherSpecht.Lascoux
end
end CanonicalSource36

section CanonicalSource37
/- Source: HigherSpecht/GriffinPrincipalBasis.lean -/



/-!
# The full prescribed Griffin basis

The reverse count is now supplied by the actual content-word battery
injection. The independent staircase basis supplies the dimension, and
the already established complete-copy independence supplies the other
cardinal inequality. The resulting basis is indexed by the manuscript's
literal full Griffin index and evaluates to its literal higher Specht family.

This source theorem is a candidate until the entire dependency closure has
passed Lean compilation and the separate statement/axiom audit.
-/

noncomputable section
open TauCeti Module

namespace HigherSpecht

theorem staircase_card_le_griffin_index (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Nat.card (GriffinStaircaseExponents n lam s) ≤ Nat.card (GriffinIndex n lam hk s) := by
  rw [card_staircase_eq_contentWords n lam s hs hheight]
  exact Lascoux.card_contentWord_le_griffin n lam hk s hs hheight

theorem griffin_index_card_eq_staircase (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Nat.card (GriffinIndex n lam hk s) = Nat.card (GriffinStaircaseExponents n lam s) :=
  le_antisymm (griffin_index_card_le_staircase n lam hk s hs hheight)
    (staircase_card_le_griffin_index n lam hk s hs hheight)

def griffinPrescribedBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Basis (GriffinIndex n lam hk s) K (GriffinRing K n lam s) :=
  griffinBasisOfReverseCardinality K n lam hk s hs hheight
    (staircase_card_le_griffin_index n lam hk s hs hheight)

@[simp] theorem griffinPrescribedBasis_apply (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (i : GriffinIndex n lam hk s) :
    griffinPrescribedBasis K n lam hk s hs hheight i = griffinFamily K n lam hk s i := by
  exact griffinBasisOfReverseCardinality_apply K n lam hk s hs hheight _ i

/-- Theorem 4.1, with every partition, admissible alphabet size, both
standard tableaux, and every multiplier in the exact prescribed rectangle. -/
theorem griffin_specifiedBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := K) (griffinFamily K n lam hk s) :=
  ⟨griffinPrescribedBasis K n lam hk s hs hheight,
    griffinPrescribedBasis_apply K n lam hk s hs hheight⟩

end HigherSpecht
end
end CanonicalSource37

section CanonicalSource38
/- Source: HigherSpecht/GradedStabilization.lean -/



/-!
# Exact stabilization below the power bound

The added generators `Xᵢ^s` have no coefficient in degree below `s`, as does
their entire ideal.  Projection to a homogeneous component therefore proves
that the finite and untruncated Griffin ideals agree in every such degree.
This is the actual ideal comparison needed in Section 6.1.
-/

noncomputable section

open Finset TauCeti MvPolynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n s d : ℕ} {μ : YoungDiagram}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem untruncatedIdeal_isHomogeneous (hn : μ.card ≤ n) :
    (untruncatedIdeal R n μ).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R) := by
  rw [← extendedElementaryIdeal_eq_untruncated μ hn]
  exact extendedElementaryIdeal_isHomogeneous μ

theorem powerIdeal_le_power_variableIdeal (n s : ℕ) :
    powerIdeal R n s ≤ MvPolynomial.idealOfVars (Fin n) R ^ s := by
  apply Ideal.span_le.mpr
  rintro f ⟨i, rfl⟩
  apply Ideal.pow_mem_pow
  exact Ideal.subset_span ⟨i, rfl⟩

theorem homogeneousComponent_powerIdeal_eq_zero {f : PolynomialRing n R}
    (hf : f ∈ powerIdeal R n s) (hd : d < s) :
    MvPolynomial.homogeneousComponent d f = 0 := by
  apply MvPolynomial.ext
  intro a
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  by_cases ha : a.degree = d
  · rw [if_pos ha]
    exact (MvPolynomial.mem_pow_idealOfVars_iff' s f).mp
      (powerIdeal_le_power_variableIdeal n s hf) a (ha ▸ hd)
  · rw [if_neg ha]

theorem homogeneous_mem_griffin_iff_untruncated (hn : μ.card ≤ n)
    {f : PolynomialRing n R} (hf : f.IsHomogeneous d) (hd : d < s) :
    f ∈ griffinIdeal R n μ s ↔ f ∈ untruncatedIdeal R n μ := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
    have hcomponent := congrArg (MvPolynomial.homogeneousComponent d) huv
    rw [map_add, homogeneousComponent_powerIdeal_eq_zero hv hd,
      add_zero, MvPolynomial.homogeneousComponent_eq_self hf] at hcomponent
    rw [← hcomponent]
    exact MvPolynomial.homogeneousComponent_mem_of_mem
      (untruncatedIdeal_isHomogeneous hn) hu d
  · intro h
    exact (show untruncatedIdeal R n μ ≤ griffinIdeal R n μ s from le_sup_left) h

/-- A relation among the actual degree-d representatives vanishes in the
untruncated ring exactly when it vanishes in any finite-s quotient with
`d < s`.  This is uniform in the coefficient ring. -/
theorem homogeneous_quotient_zero_iff (hn : μ.card ≤ n)
    {f : PolynomialRing n R} (hf : f.IsHomogeneous d) (hd : d < s) :
    Ideal.Quotient.mk (griffinIdeal R n μ s) f = 0 ↔
      Ideal.Quotient.mk (untruncatedIdeal R n μ) f = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  exact homogeneous_mem_griffin_iff_untruncated hn hf hd

end HigherSpecht
end
end CanonicalSource38

section CanonicalSource39
/- Source: HigherSpecht/UntruncatedIndependence.lean -/



/-!
# All untruncated higher Specht multiples are independent

Every finite subfamily fits in a genuine finite-s Griffin family.  Projection
from the untruncated quotient to that finite quotient preserves the literal
representatives, so the already established full finite-family independence
proves independence of the infinite untruncated family.  The argument includes
the empty partition and does not assume a count, spanning, or stabilization
theorem.
-/

noncomputable section

open TauCeti Module

namespace HigherSpecht

variable {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}

theorem untruncatedVectorIndex_ext {i j : UntruncatedVectorIndex n lam hk}
    (hpair : i.base.val = j.base.val) (heta : i.multiplier = j.multiplier) : i = j := by
  cases i
  cases j
  have hb := Subtype.ext hpair
  cases hb
  cases heta
  rfl

def finiteGriffinBound (t : Finset (UntruncatedVectorIndex n lam hk)) : ℕ :=
  max (lam.colLen 0) (t.sup fun i => descentNumber i.base.val.left + i.multiplier.rowLen 0 + 1) + 1

theorem finiteGriffinBound_pos (t : Finset (UntruncatedVectorIndex n lam hk)) :
    0 < finiteGriffinBound t := Nat.succ_pos _

theorem finiteGriffinBound_height (t : Finset (UntruncatedVectorIndex n lam hk)) :
    lam.colLen 0 ≤ finiteGriffinBound t :=
  (le_max_left _ _).trans (Nat.le_succ _)

theorem finiteGriffinBound_index (t : Finset (UntruncatedVectorIndex n lam hk)) (i : t) :
    descentNumber i.val.base.val.left < finiteGriffinBound t ∧
      i.val.multiplier.rowLen 0 ≤ finiteGriffinBound t - descentNumber i.val.base.val.left - 1 := by
  have h := Finset.le_sup (f := fun j : UntruncatedVectorIndex n lam hk =>
    descentNumber j.base.val.left + j.multiplier.rowLen 0 + 1) i.property
  have hm := le_max_right (lam.colLen 0)
    (t.sup fun j => descentNumber j.base.val.left + j.multiplier.rowLen 0 + 1)
  dsimp only [finiteGriffinBound]
  omega

def finiteUntruncatedToGriffin (t : Finset (UntruncatedVectorIndex n lam hk))
    (i : t) : GriffinIndex n lam hk (finiteGriffinBound t) where
  pair := i.val.base.val
  multiplier := i.val.multiplier
  eligible := i.val.base.property
  descents_lt := (finiteGriffinBound_index t i).1
  multiplier_length := i.val.multiplier_length
  multiplier_width := (finiteGriffinBound_index t i).2

theorem finiteUntruncatedToGriffin_injective (t : Finset (UntruncatedVectorIndex n lam hk)) :
    Function.Injective (finiteUntruncatedToGriffin t) := by
  intro i j h
  apply Subtype.ext
  apply untruncatedVectorIndex_ext
  · exact congrArg (fun z : GriffinIndex n lam hk (finiteGriffinBound t) => z.pair) h
  · exact congrArg (fun z : GriffinIndex n lam hk (finiteGriffinBound t) => z.multiplier) h

def untruncatedToGriffinProjection (K : Type*) [CommRing K] (n : ℕ)
    (lam : YoungDiagram) (s : ℕ) :
    UntruncatedRing K n lam →ₐ[K] GriffinRing K n lam s :=
  Ideal.Quotient.factorₐ K (show untruncatedIdeal K n lam ≤ griffinIdeal K n lam s from le_sup_left)

@[simp] theorem untruncatedToGriffinProjection_family (K : Type*) [CommRing K]
    (t : Finset (UntruncatedVectorIndex n lam hk)) (i : t) :
    untruncatedToGriffinProjection K n lam (finiteGriffinBound t)
      (untruncatedVectorFamily K n lam hk i.val) =
      griffinFamily K n lam hk (finiteGriffinBound t) (finiteUntruncatedToGriffin t i) := rfl

theorem untruncatedVectorFamily_linearIndependent_charZero (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    LinearIndependent K (untruncatedVectorFamily K n lam hk) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro t
  have h := (griffinFamily_linearIndependent_charZero K n lam hk (finiteGriffinBound t)
    (finiteGriffinBound_pos t) (finiteGriffinBound_height t)).comp
      (finiteUntruncatedToGriffin t) (finiteUntruncatedToGriffin_injective t)
  apply LinearIndependent.of_comp
    (untruncatedToGriffinProjection K n lam (finiteGriffinBound t)).toLinearMap
  simpa only [Function.comp_def, AlgHom.coe_toLinearMap, AlgHom.toLinearMap_apply,
    untruncatedToGriffinProjection_family] using h

end HigherSpecht
end
end CanonicalSource39

section CanonicalSource40
/- Source: HigherSpecht/ParameterAlgebra.lean -/



/-! The literal elementary-parameter algebra structure.  These definitions
and scalar-tower proofs are independent of higher-Specht independence,
spanning, or algebraic independence. -/

noncomputable section

open TauCeti MvPolynomial

namespace HigherSpecht

def elementaryParameterClasses (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) :
    Fin (n - lam.card) → UntruncatedRing K n lam :=
  fun j => Ideal.Quotient.mk (untruncatedIdeal K n lam)
    (MvPolynomial.esymm (Fin n) K (j.val + 1))

abbrev ElementaryParameterRing (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) :=
  MvPolynomial (Fin (n - lam.card)) K

noncomputable instance untruncatedParameterAlgebra (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    Algebra (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
  (MvPolynomial.aeval (elementaryParameterClasses K n lam)).toRingHom.toAlgebra

noncomputable instance untruncatedParameterScalarTower (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    IsScalarTower K (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
  IsScalarTower.of_algHom (MvPolynomial.aeval (elementaryParameterClasses K n lam))

@[simp] theorem untruncatedParameter_algebraMap (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) (p : ElementaryParameterRing K n lam) :
    algebraMap (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) p =
      MvPolynomial.aeval (elementaryParameterClasses K n lam) p := rfl

end HigherSpecht
end
end CanonicalSource40

section CanonicalSource41
/- Source: HigherSpecht/PartitionDifferences.lean -/



/-!
# Partitions of bounded length and monomials in elementary parameters

The partition with row lengths equal to successive tail sums of an exponent
vector has that vector as its consecutive row differences.  Thus the literal
`E_eta` factors are precisely monomials in the first elementary parameters.
-/

noncomputable section

open TauCeti Finset MvPolynomial

namespace HigherSpecht

def differenceTail {m : ℕ} (a : Fin m →₀ ℕ) (j : ℕ) : ℕ :=
  ∑ i : Fin m, if j ≤ i.val then a i else 0

theorem differenceTail_antitone {m : ℕ} (a : Fin m →₀ ℕ) : Antitone (differenceTail a) := by
  intro j k hjk
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> omega

theorem differenceTail_eq_zero {m : ℕ} (a : Fin m →₀ ℕ) {j : ℕ} (hj : m ≤ j) :
    differenceTail a j = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg (by have := i.isLt; omega)]

theorem differenceTail_succ {m : ℕ} (a : Fin m →₀ ℕ) (i : Fin m) :
    differenceTail a i.val = a i + differenceTail a (i.val + 1) := by
  have hterm (j : Fin m) : (if i.val ≤ j.val then a j else 0) =
      (if j = i then a j else 0) + (if i.val + 1 ≤ j.val then a j else 0) := by
    by_cases heq : j = i
    · subst j
      simp
    · have hne : j.val ≠ i.val := fun h => heq (Fin.ext h)
      split_ifs <;> omega
  simp only [differenceTail, hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

def partitionFromDifferences {m : ℕ} (a : Fin m →₀ ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.ofFn fun i : Fin m => differenceTail a i.val)
    (List.sortedGE_ofFn_iff.mpr fun i j hij => differenceTail_antitone a hij)

theorem partitionFromDifferences_height {m : ℕ} (a : Fin m →₀ ℕ) :
    (partitionFromDifferences a).colLen 0 ≤ m := by
  by_contra h
  have hc : (m, 0) ∈ partitionFromDifferences a :=
    YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge h)
  rw [partitionFromDifferences, YoungDiagram.mem_ofRowLens] at hc
  have hm : m < m := by simpa only [List.length_ofFn] using hc.1
  exact (Nat.lt_irrefl m) hm

theorem partitionFromDifferences_rowLen {m : ℕ} (a : Fin m →₀ ℕ) (j : ℕ) :
    (partitionFromDifferences a).rowLen j = differenceTail a j := by
  by_cases hj : j < m
  · have h := YoungDiagram.rowLen_ofRowLens
      (w := List.ofFn fun i : Fin m => differenceTail a i.val)
      (hw := List.sortedGE_ofFn_iff.mpr fun i l hil => differenceTail_antitone a hil)
      ⟨j, by simpa only [List.length_ofFn] using hj⟩
    simpa only [partitionFromDifferences, Fin.getElem_fin, List.getElem_ofFn] using h
  · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le
      ((partitionFromDifferences_height a).trans (le_of_not_gt hj)),
      differenceTail_eq_zero a (le_of_not_gt hj)]

theorem partitionFromDifferences_difference {m : ℕ} (a : Fin m →₀ ℕ) (i : Fin m) :
    (partitionFromDifferences a).rowLen i.val -
      (partitionFromDifferences a).rowLen (i.val + 1) = a i := by
  rw [partitionFromDifferences_rowLen, partitionFromDifferences_rowLen,
    differenceTail_succ]
  omega

theorem partitionFromDifferences_injective (m : ℕ) :
    Function.Injective (@partitionFromDifferences m) := by
  intro a b h
  ext i
  rw [← partitionFromDifferences_difference a i, ← partitionFromDifferences_difference b i, h]

def partitionDifferences (m : ℕ) (eta : YoungDiagram) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => eta.rowLen i.val - eta.rowLen (i.val + 1)

@[simp] theorem partitionDifferences_apply (m : ℕ) (eta : YoungDiagram) (i : Fin m) :
    partitionDifferences m eta i = eta.rowLen i.val - eta.rowLen (i.val + 1) := by
  rw [partitionDifferences, Finsupp.equivFunOnFinite_symm_apply_apply]

theorem differenceTail_partitionDifferences (m : ℕ) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ m) (j : ℕ) :
    differenceTail (partitionDifferences m eta) j = eta.rowLen j := by
  by_cases hj : j ≤ m
  · induction hj using Nat.decreasingInduction with
    | self => rw [differenceTail_eq_zero _ le_rfl, YoungDiagram.rowLen_eq_zero_of_colLen_le heta]
    | of_succ j hj ih =>
      rw [differenceTail_succ _ ⟨j, hj⟩, ih, partitionDifferences_apply]
      exact Nat.sub_add_cancel (eta.rowLen_anti j (j + 1) (Nat.le_succ j))
  · rw [differenceTail_eq_zero _ (by omega),
      YoungDiagram.rowLen_eq_zero_of_colLen_le (heta.trans (by omega))]

theorem partitionFromDifferences_partitionDifferences (m : ℕ) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ m) : partitionFromDifferences (partitionDifferences m eta) = eta := by
  apply YoungDiagram.rowLen_injective
  funext j
  rw [partitionFromDifferences_rowLen, differenceTail_partitionDifferences m eta heta]

def partitionDifferenceEquiv (m : ℕ) :
    {eta : YoungDiagram // eta.colLen 0 ≤ m} ≃ (Fin m →₀ ℕ) where
  toFun eta := partitionDifferences m eta.val
  invFun a := ⟨partitionFromDifferences a, partitionFromDifferences_height a⟩
  left_inv eta := Subtype.ext (partitionFromDifferences_partitionDifferences m eta.val eta.property)
  right_inv a := by ext i; rw [partitionDifferences_apply, partitionFromDifferences_difference]

theorem elementaryMultiplier_partitionFromDifferences {R : Type*} [CommRing R]
    (n m : ℕ) (a : Fin m →₀ ℕ) :
    elementaryMultiplier (R := R) n m (partitionFromDifferences a).rowLen =
      ∏ i : Fin m, MvPolynomial.esymm (Fin n) R (i.val + 1) ^ a i := by
  rw [elementaryMultiplier, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  rw [partitionFromDifferences_difference]

end HigherSpecht
end
end CanonicalSource41

section CanonicalSource42
/- Source: HigherSpecht/ElementaryParameters.lean -/



/-!
# Algebraic independence of the actual elementary parameters

The one-row higher Specht polynomial is exactly `n!`.  Its unrestricted
elementary multiples are a subfamily of the already proved untruncated
independent family.  The precise partition-difference correspondence converts
those multiples into all monomials in the images of `e_1,...,e_(n-k)`.  This
establishes the algebraic-independence assertion in Theorem 6.1 without using
the still separate spanning or index-count result.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

variable {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}

def oneRowParameterIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (a : Fin (n - lam.card) →₀ ℕ) : UntruncatedVectorIndex n lam hk where
  base := ⟨oneRowPair n, (oneRowGriffinIndex n lam hk 1 (Nat.zero_lt_succ 0)).eligible⟩
  multiplier := partitionFromDifferences a
  multiplier_length := partitionFromDifferences_height a

theorem oneRowParameterIndex_injective (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Function.Injective (oneRowParameterIndex n lam hk) := by
  intro a b h
  exact partitionFromDifferences_injective (n - lam.card)
    (congrArg (fun i : UntruncatedVectorIndex n lam hk => i.multiplier) h)

def elementaryParameterMonomial (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram)
    (a : Fin (n - lam.card) →₀ ℕ) : UntruncatedRing K n lam :=
  ∏ j : Fin (n - lam.card), elementaryParameterClasses K n lam j ^ a j

theorem oneRowParameterIndex_value (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (a : Fin (n - lam.card) →₀ ℕ) :
    untruncatedVectorFamily K n lam hk (oneRowParameterIndex n lam hk a) =
      (n.factorial : K) • elementaryParameterMonomial K n lam a := by
  simp only [untruncatedVectorFamily, oneRowParameterIndex, pairPolynomial_oneRow,
    elementaryMultiplier_partitionFromDifferences, map_mul, map_natCast,
    map_prod, map_pow, elementaryParameterMonomial, elementaryParameterClasses,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem elementaryParameterMonomial_linearIndependent (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    LinearIndependent K (elementaryParameterMonomial K n lam) := by
  have h := (untruncatedVectorFamily_linearIndependent_charZero K n lam hk).comp
    (oneRowParameterIndex n lam hk) (oneRowParameterIndex_injective n lam hk)
  apply LinearIndependent.of_comp
    ((n.factorial : K) • (LinearMap.id : UntruncatedRing K n lam →ₗ[K] UntruncatedRing K n lam))
  simpa only [Function.comp_def, oneRowParameterIndex_value,
    LinearMap.smul_apply, LinearMap.id_apply] using h

theorem aeval_elementaryParameters_monomial (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) (a : Fin (n - lam.card) →₀ ℕ) :
    MvPolynomial.aeval (elementaryParameterClasses K n lam) (MvPolynomial.monomial a (1 : K)) =
      elementaryParameterMonomial K n lam a := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_pow]
  rfl

/-- The algebraic-independence conclusion of Theorem 6.1, in its full
parameter range, including the empty partition. -/
theorem elementaryParameters_algebraicIndependent (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent K (elementaryParameterClasses K n lam) := by
  let B := MvPolynomial.basisMonomials (Fin (n - lam.card)) K
  have h := B.injective_constr_of_linearIndependent (R₂ := K)
    (elementaryParameterMonomial_linearIndependent K n lam hk)
  have heq : B.constr K (elementaryParameterMonomial K n lam) =
      (MvPolynomial.aeval (elementaryParameterClasses K n lam)).toLinearMap := by
    apply B.ext
    intro a
    rw [Basis.constr_basis]
    exact (aeval_elementaryParameters_monomial K n lam a).symm
  change Function.Injective (MvPolynomial.aeval (elementaryParameterClasses K n lam)).toLinearMap
  exact heq ▸ h

end HigherSpecht
end
end CanonicalSource42

section CanonicalSource43
/- Source: HigherSpecht/ParameterModule.lean -/



/-!
# The actual elementary-parameter module and independence over it

The polynomial parameter ring acts through evaluation at the actual elementary
classes.  Expanding its monomial basis gives exactly the unrestricted `E_eta`
family.  Consequently the prescribed unmultiplied higher Specht classes are
independent over this parameter ring.  The spanning conclusion of Theorem 6.1
still needs the separate full finite-index count.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

theorem linearIndependent_scalarRing_of_expansion
    {R A M ι κ : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module A M]
    [IsScalarTower R A M] [SMulCommClass R A M]
    (B : Basis κ R A) (v : ι → M)
    (hv : LinearIndependent R (fun z : ι × κ => B z.2 • v z.1)) :
    LinearIndependent A v := by
  classical
  let C := Finsupp.basis fun _ : ι => B
  let L := Finsupp.linearCombination A v
  have h := hv.comp (Equiv.sigmaEquivProd ι κ) (Equiv.sigmaEquivProd ι κ).injective
  have hC : LinearIndependent R (fun z : Σ _ : ι, κ => B z.2 • v z.1) := h
  have hinj := C.injective_constr_of_linearIndependent (R₂ := R) hC
  have heq : C.constr R (fun z : Σ _ : ι, κ => B z.2 • v z.1) = L.restrictScalars R := by
    apply C.ext
    intro z
    rw [Basis.constr_basis]
    simp only [C, Finsupp.coe_basis, L, LinearMap.restrictScalars_apply,
      Finsupp.linearCombination_single]
  change Function.Injective L
  have hrestrict : Function.Injective (L.restrictScalars R) := by
    rw [← heq]
    exact hinj
  exact hrestrict

def parameterVectorIndex {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (z : UntruncatedIndex n lam hk × (Fin (n - lam.card) →₀ ℕ)) :
    UntruncatedVectorIndex n lam hk where
  base := z.1
  multiplier := partitionFromDifferences z.2
  multiplier_length := partitionFromDifferences_height z.2

theorem parameterVectorIndex_injective {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n} :
    Function.Injective (parameterVectorIndex (n := n) (lam := lam) (hk := hk)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  apply Prod.ext
  · exact congrArg (fun x : UntruncatedVectorIndex n lam hk => x.base) h
  · exact partitionFromDifferences_injective (n - lam.card)
      (congrArg (fun x : UntruncatedVectorIndex n lam hk => x.multiplier) h)

theorem parameterVectorIndex_surjective {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n} :
    Function.Surjective (parameterVectorIndex (n := n) (lam := lam) (hk := hk)) := by
  intro i
  refine ⟨⟨i.base, partitionDifferences (n - lam.card) i.multiplier⟩, ?_⟩
  apply untruncatedVectorIndex_ext
  · rfl
  · exact partitionFromDifferences_partitionDifferences _ _ i.multiplier_length

def parameterVectorIndexEquiv (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (UntruncatedIndex n lam hk × (Fin (n - lam.card) →₀ ℕ)) ≃
      UntruncatedVectorIndex n lam hk :=
  Equiv.ofBijective parameterVectorIndex
    ⟨parameterVectorIndex_injective, parameterVectorIndex_surjective⟩

theorem parameter_monomial_smul (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : UntruncatedIndex n lam hk) (a : Fin (n - lam.card) →₀ ℕ) :
    (MvPolynomial.monomial a (1 : K) : ElementaryParameterRing K n lam) •
        untruncatedFamily K n lam hk i =
      untruncatedVectorFamily K n lam hk (parameterVectorIndex (i, a)) := by
  rw [Algebra.smul_def, untruncatedParameter_algebraMap,
    aeval_elementaryParameters_monomial]
  simp only [untruncatedFamily, untruncatedVectorFamily, parameterVectorIndex,
    elementaryMultiplier_partitionFromDifferences, elementaryParameterMonomial,
    elementaryParameterClasses, map_mul, map_prod, map_pow, mul_comm]

theorem untruncatedFamily_linearIndependent_parameters (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    LinearIndependent (ElementaryParameterRing K n lam) (untruncatedFamily K n lam hk) := by
  apply linearIndependent_scalarRing_of_expansion (MvPolynomial.basisMonomials (Fin (n - lam.card)) K)
  have h := (untruncatedVectorFamily_linearIndependent_charZero K n lam hk).comp
    parameterVectorIndex parameterVectorIndex_injective
  simpa only [MvPolynomial.coe_basisMonomials, parameter_monomial_smul,
    Function.comp_def] using h

end HigherSpecht
end
end CanonicalSource43

section CanonicalSource44
/- Source: HigherSpecht/UntruncatedSpanning.lean -/



/-!
# Degreewise lifting of the finite prescribed bases

This file supplies the actual homogeneous-component argument in Section 6.1.
The transfer theorem explicitly receives the finite prescribed bases; it is
not itself a proof of the unresolved nonempty-index count.  The empty-partition
application instantiates those bases with the bounded-word construction, so
that application has no counting or spanning premise.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

theorem homogeneousComponent_griffin_mem_untruncated
    {R : Type*} [CommRing R] {n s d : ℕ} {lam : YoungDiagram}
    (hk : lam.card ≤ n) {f : PolynomialRing n R}
    (hf : f ∈ griffinIdeal R n lam s) (hd : d < s) :
    homogeneousComponent d f ∈ untruncatedIdeal R n lam := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add, homogeneousComponent_powerIdeal_eq_zero hv hd, add_zero]
  exact MvPolynomial.homogeneousComponent_mem_of_mem
    (untruncatedIdeal_isHomogeneous hk) hu d

def forgetGriffinBound {n s : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (i : GriffinIndex n lam hk s) : UntruncatedVectorIndex n lam hk where
  base := ⟨i.pair, i.eligible⟩
  multiplier := i.multiplier
  multiplier_length := i.multiplier_length

@[simp] theorem forgetGriffinBound_family
    {R : Type*} [CommRing R] {n s : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (i : GriffinIndex n lam hk s) :
    Ideal.Quotient.mk (untruncatedIdeal R n lam) (griffinPolynomial i) =
      untruncatedVectorFamily R n lam hk (forgetGriffinBound i) := rfl

theorem homogeneous_class_mem_span_of_finite_basis
    {R : Type*} [CommRing R] {n d : ℕ} {lam : YoungDiagram} (hk : lam.card ≤ n)
    (s : ℕ) (hd : d < s)
    (b : Basis (GriffinIndex n lam hk s) R (GriffinRing R n lam s))
    (hb : ∀ i, b i = griffinFamily R n lam hk s i)
    {f : PolynomialRing n R} (hf : f.IsHomogeneous d) :
    Ideal.Quotient.mk (untruncatedIdeal R n lam) f ∈
      Submodule.span R (Set.range (untruncatedVectorFamily R n lam hk)) := by
  classical
  let q : PolynomialRing n R →ₐ[R] UntruncatedRing R n lam :=
    Ideal.Quotient.mkₐ R (untruncatedIdeal R n lam)
  let qf : PolynomialRing n R →ₐ[R] GriffinRing R n lam s :=
    Ideal.Quotient.mkₐ R (griffinIdeal R n lam s)
  let c := b.repr (qf f)
  let g : PolynomialRing n R := c.sum fun i a => a • griffinPolynomial i
  have hg : qf g = qf f := by
    change qf (∑ i ∈ c.support, c i • griffinPolynomial i) = qf f
    simp only [map_sum, map_smul]
    have heq : ∀ i, qf (griffinPolynomial i) = b i := fun i => (hb i).symm
    simp only [heq]
    exact b.linearCombination_repr (qf f)
  have hmem : f - g ∈ griffinIdeal R n lam s := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qf (f - g) = 0
    rw [map_sub, hg, sub_self]
  have hlow := homogeneousComponent_griffin_mem_untruncated hk hmem hd
  have hquot : q f = q (homogeneousComponent d g) := by
    apply sub_eq_zero.mp
    rw [← map_sub, ← homogeneousComponent_eq_self hf, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hlow
  change q f ∈ _
  rw [hquot]
  change q (homogeneousComponent d
    (∑ i ∈ c.support, c i • griffinPolynomial i)) ∈ _
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [homogeneousComponent_of_mem (griffinPolynomial_isHomogeneous i)]
  split_ifs with hdeg
  · exact Submodule.subset_span ⟨forgetGriffinBound i, rfl⟩
  · simpa only [map_zero] using (Submodule.zero_mem
      (Submodule.span R (Set.range (untruncatedVectorFamily R n lam hk))))

theorem untruncatedVectorFamily_spans_of_finite_bases
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s)) :
    ⊤ ≤ Submodule.span R (Set.range (untruncatedVectorFamily R n lam hk)) := by
  classical
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MvPolynomial.as_sum f, map_sum]
  apply Submodule.sum_mem
  intro a ha
  let s := a.degree + lam.colLen 0 + 1
  have hs : 0 < s := by dsimp [s]; omega
  have hheight : lam.colLen 0 ≤ s := by dsimp [s]; omega
  have hd : a.degree < s := by dsimp [s]; omega
  obtain ⟨b, hb⟩ := hb s hs hheight
  exact homogeneous_class_mem_span_of_finite_basis hk s hd b hb
    (MvPolynomial.isHomogeneous_monomial (f.coeff a) rfl)

def untruncatedVectorBasisOfFiniteBases
    (K : Type*) [Field K] [CharZero K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := K) (griffinFamily K n lam hk s)) :
    Basis (UntruncatedVectorIndex n lam hk) K (UntruncatedRing K n lam) :=
  Basis.mk (untruncatedVectorFamily_linearIndependent_charZero K n lam hk)
    (untruncatedVectorFamily_spans_of_finite_bases K n lam hk hb)

@[simp] theorem untruncatedVectorBasisOfFiniteBases_apply
    (K : Type*) [Field K] [CharZero K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := K) (griffinFamily K n lam hk s))
    (i : UntruncatedVectorIndex n lam hk) :
    untruncatedVectorBasisOfFiniteBases K n lam hk hb i =
      untruncatedVectorFamily K n lam hk i := Basis.mk_apply _ _ _

def untruncatedEmptyVectorBasis (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    Basis (UntruncatedVectorIndex n ⊥ (by simp [YoungDiagram.card])) K
      (UntruncatedRing K n ⊥) :=
  untruncatedVectorBasisOfFiniteBases K n ⊥ (by simp [YoungDiagram.card])
    (fun s hs _ => griffin_empty_specifiedBasis K n s hs)

@[simp] theorem untruncatedEmptyVectorBasis_apply
    (K : Type*) [Field K] [CharZero K] (n : ℕ)
    (i : UntruncatedVectorIndex n ⊥ (by simp [YoungDiagram.card])) :
    untruncatedEmptyVectorBasis K n i =
      untruncatedVectorFamily K n ⊥ (by simp [YoungDiagram.card]) i :=
  untruncatedVectorBasisOfFiniteBases_apply K n ⊥ _ _ i

end HigherSpecht
end
end CanonicalSource44

section CanonicalSource45
/- Source: HigherSpecht/ParameterBasis.lean -/



/-!
# From the genuine vector basis to the parameter-ring basis

The change of indices is the explicit partition-difference bijection, and the
scalar action is evaluation at the actual elementary classes.  The generic
transfer retains its finite-basis input visibly.  The final empty-partition
basis and its rank instantiate that input with the proved bounded-word basis.
-/

noncomputable section

open TauCeti Module

namespace HigherSpecht

theorem untruncatedFamily_spans_parameters_of_vector_span
    (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hspan : ⊤ ≤ Submodule.span K
      (Set.range (untruncatedVectorFamily K n lam hk))) :
    ⊤ ≤ Submodule.span (ElementaryParameterRing K n lam)
      (Set.range (untruncatedFamily K n lam hk)) := by
  classical
  let M := Submodule.span (ElementaryParameterRing K n lam)
    (Set.range (untruncatedFamily K n lam hk))
  have hle : Submodule.span K (Set.range (untruncatedVectorFamily K n lam hk)) ≤
      M.restrictScalars K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨⟨j, a⟩, rfl⟩ := parameterVectorIndex_surjective i
    rw [← parameter_monomial_smul]
    exact M.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  intro x hx
  exact hle (hspan hx)

def untruncatedParameterBasisOfFiniteBases
    (K : Type*) [Field K] [CharZero K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := K) (griffinFamily K n lam hk s)) :
    Basis (UntruncatedIndex n lam hk) (ElementaryParameterRing K n lam)
      (UntruncatedRing K n lam) :=
  Basis.mk (untruncatedFamily_linearIndependent_parameters K n lam hk)
    (untruncatedFamily_spans_parameters_of_vector_span K n lam hk
      (untruncatedVectorFamily_spans_of_finite_bases K n lam hk hb))

@[simp] theorem untruncatedParameterBasisOfFiniteBases_apply
    (K : Type*) [Field K] [CharZero K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := K) (griffinFamily K n lam hk s))
    (i : UntruncatedIndex n lam hk) :
    untruncatedParameterBasisOfFiniteBases K n lam hk hb i =
      untruncatedFamily K n lam hk i := Basis.mk_apply _ _ _

def untruncatedEmptyParameterBasis (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    Basis (UntruncatedIndex n ⊥ (by simp [YoungDiagram.card]))
      (ElementaryParameterRing K n ⊥) (UntruncatedRing K n ⊥) :=
  untruncatedParameterBasisOfFiniteBases K n ⊥ (by simp [YoungDiagram.card])
    (fun s hs _ => griffin_empty_specifiedBasis K n s hs)

@[simp] theorem untruncatedEmptyParameterBasis_apply
    (K : Type*) [Field K] [CharZero K] (n : ℕ)
    (i : UntruncatedIndex n ⊥ (by simp [YoungDiagram.card])) :
    untruncatedEmptyParameterBasis K n i =
      untruncatedFamily K n ⊥ (by simp [YoungDiagram.card]) i :=
  untruncatedParameterBasisOfFiniteBases_apply K n ⊥ _ _ i

def untruncatedEmptyIndexEquiv (n : ℕ) :
    UntruncatedIndex n ⊥ (by simp [YoungDiagram.card]) ≃ StandardPair n :=
  Equiv.subtypeUnivEquiv prefixEligible_bot

theorem card_untruncatedEmptyIndex (n : ℕ) :
    Nat.card (UntruncatedIndex n ⊥ (by simp [YoungDiagram.card])) = n.factorial := by
  rw [Nat.card_congr (untruncatedEmptyIndexEquiv n), Nat.card_eq_fintype_card]
  exact card_standardPair n

theorem untruncated_empty_finite_parameters
    (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    Module.Finite (ElementaryParameterRing K n ⊥) (UntruncatedRing K n ⊥) := by
  classical
  letI : Fintype (UntruncatedIndex n ⊥ (by simp [YoungDiagram.card])) := Fintype.ofFinite _
  exact Module.Finite.of_basis (untruncatedEmptyParameterBasis K n)

theorem untruncated_empty_parameter_rank
    (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    Module.finrank (ElementaryParameterRing K n ⊥) (UntruncatedRing K n ⊥) =
      n.factorial := by
  classical
  letI : Fintype (UntruncatedIndex n ⊥ (by simp [YoungDiagram.card])) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (untruncatedEmptyParameterBasis K n)]
  exact (Nat.card_eq_fintype_card).symm.trans (card_untruncatedEmptyIndex n)

end HigherSpecht
end
end CanonicalSource45

section CanonicalSource46
/- Source: HigherSpecht/SimultaneousStatements.lean -/



/-!
# The literal simultaneous harmonic-copy targets

These definitions retain the manuscript's actual common witnesses, including
the maximal permitted prefix, the factorial factor, the adjoint Young
operator, and the original polynomial differential action.  The two final
propositions are targets, not theorem declarations.  In particular neither
the unresolved prefix-catabolism restriction nor a dimension count is
silently added as a hypothesis of a claimed principal result.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module MvPolynomial

namespace HigherSpecht

def ordinaryHarmonics {n : ℕ} (I : Ideal (PolynomialRing n ℂ)) :
    Submodule ℂ (PolynomialRing n ℂ) where
  carrier := {p | ∀ f ∈ I, ordinaryAction f p = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq f hf
    rw [map_add, hp f hf, hq f hf, add_zero]
  smul_mem' := by
    intro c p hp f hf
    rw [map_smul, hp f hf, smul_zero]

theorem ordinaryHarmonics_eq_factorialTransport {n : ℕ}
    (I : Ideal (PolynomialRing n ℂ)) :
    ordinaryHarmonics I = (dividedHarmonics I).map
      (factorialTransport (σ := Fin n) (K := ℂ)).toLinearMap := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, rfl⟩ := (factorialTransport (σ := Fin n) (K := ℂ)).surjective p
    refine ⟨q, ?_, rfl⟩
    intro f hf
    apply (factorialTransport (σ := Fin n) (K := ℂ)).injective
    rw [map_zero, ← ordinaryAction_factorialTransport]
    exact hp f hf
  · rintro ⟨q, hq, rfl⟩ f hf
    change ordinaryAction f (factorialTransport q) = 0
    rw [ordinaryAction_factorialTransport, hq f hf, map_zero]

def adjointYoungApply {mu : YoungDiagram} (T : YoungTableau mu)
    (f : PolynomialRing mu.card ℂ) : PolynomialRing mu.card ℂ :=
  rowSymmetrize (rowSubgroup T) (columnAlternate (colSubgroup T) f)

def cyclicPolynomialCopy {n : ℕ} (h : PolynomialRing n ℂ) :
    Submodule ℂ (PolynomialRing n ℂ) :=
  Submodule.span ℂ (Set.range fun sigma : Equiv.Perm (Fin n) => MvPolynomial.rename sigma h)

/-- An actual injective intertwiner from the ordinary irreducible Young ideal.
The codomain is the genuine polynomial representation. -/
def IsSpechtPolynomialCopy {n : ℕ} (part : n.Partition)
    (W : Submodule ℂ (PolynomialRing n ℂ)) : Prop :=
  ∃ phi : (YoungIdealRepresentation (K := ℂ) part).IntertwiningMap
      (polynomialRepresentation ℂ n),
    Function.Injective phi ∧ LinearMap.range phi.toLinearMap = W

structure UnboundedHarmonicIndex (n : ℕ) where
  part : n.Partition
  left : StandardYoungTableau (YoungDiagram.ofPartition part)
  multiplier : YoungDiagram
  multiplier_length : multiplier.colLen 0 ≤ n

structure FiniteHarmonicIndex (n s : ℕ) extends UnboundedHarmonicIndex n where
  descents_lt : descentNumber left < s
  multiplier_width : multiplier.rowLen 0 ≤ s - descentNumber left - 1

def UnboundedHarmonicIndex.degree {n : ℕ} (i : UnboundedHarmonicIndex n) : ℕ :=
  cochargeDegree i.left + i.multiplier.card

def UnboundedHarmonicIndex.eligible {n : ℕ} (i : UnboundedHarmonicIndex n)
    (lam : YoungDiagram) (hk : lam.card ≤ n) : Prop :=
  i.multiplier.colLen 0 ≤ n - lam.card ∧
    CatDominates (prefixTableau i.left lam.card
      (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam

def maximalFinitePrefix {n s : ℕ} (i : FiniteHarmonicIndex n s) : ℕ :=
  min (n - i.multiplier.colLen 0)
    (∑ r ∈ Finset.range s, (columnInsertion i.left).state.shape.rowLen r)

theorem maximalFinitePrefix_le {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    maximalFinitePrefix i ≤ (YoungDiagram.ofPartition i.part).card := by
  rw [YoungDiagram.card_ofPartition]
  exact (min_le_left _ _).trans (Nat.sub_le _ _)

def finiteCommonHarmonicVector {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    PolynomialRing n ℂ :=
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)).toTableau
  let r := griffinWitnessRejection i.left T i.multiplier (maximalFinitePrefix i)
    (maximalFinitePrefix_le i) s
  let G := griffinApolarWitness i.left T (maximalFinitePrefix i) (maximalFinitePrefix_le i) s
  MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
    ((exponentFactorial r : ℂ)⁻¹ • adjointYoungApply T
      (ordinaryAction (MvPolynomial.monomial r (1 : ℂ)) G))

def finiteCommonHarmonicCopy {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    Submodule ℂ (PolynomialRing n ℂ) := cyclicPolynomialCopy (finiteCommonHarmonicVector i)

def maximalUntruncatedPrefix {n : ℕ} (i : UnboundedHarmonicIndex n) : ℕ :=
  n - i.multiplier.colLen 0

theorem maximalUntruncatedPrefix_le {n : ℕ} (i : UnboundedHarmonicIndex n) :
    maximalUntruncatedPrefix i ≤ (YoungDiagram.ofPartition i.part).card := by
  rw [YoungDiagram.card_ofPartition]
  exact Nat.sub_le _ _

def untruncatedCommonData {n : ℕ} (i : UnboundedHarmonicIndex n) :=
  let mu := YoungDiagram.ofPartition i.part
  let T := (StandardYoungTableau.rowSuperstandard mu).toTableau
  let k := maximalUntruncatedPrefix i
  let hk := maximalUntruncatedPrefix_le i
  let e := prefixAmbientEmbedding i.left T k hk
  let U := (insertionFilling (prefixTableau i.left k hk)
    (prefixTableau i.left k hk).toTableau).toEmbedding.trans e
  let b := transportedBoosted i.left T i.multiplier
  let outside : Fin mu.card →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun j => if j ∈ Set.range e then 0 else b j)
  let alpha := (insertionAlpha (prefixTableau i.left k hk)
    (prefixTableau i.left k hk).toTableau).mapDomain e + outside
  let G : PolynomialRing mu.card ℂ :=
    (∏ j ∈ Finset.range mu.card, columnAlternant U j) * MvPolynomial.monomial outside 1
  (T, alpha - b, G)

def untruncatedCommonHarmonicVector {n : ℕ} (i : UnboundedHarmonicIndex n) :
    PolynomialRing n ℂ :=
  let data := untruncatedCommonData i
  MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
    ((exponentFactorial data.2.1 : ℂ)⁻¹ • adjointYoungApply data.1
      (ordinaryAction (MvPolynomial.monomial data.2.1 (1 : ℂ)) data.2.2))

def untruncatedCommonHarmonicCopy {n : ℕ} (i : UnboundedHarmonicIndex n) :
    Submodule ℂ (PolynomialRing n ℂ) := cyclicPolynomialCopy (untruncatedCommonHarmonicVector i)

/-- The complete simultaneous-copy assertion of Theorem 5.2, including the
actual witnesses, their shapes/degrees, and every allowed ideal at once. -/
def FiniteSimultaneousHarmonicTarget : Prop :=
  ∀ n s : ℕ, 0 < n → 0 < s →
    (∀ i : FiniteHarmonicIndex n s,
      IsSpechtPolynomialCopy i.part (finiteCommonHarmonicCopy i) ∧
      finiteCommonHarmonicCopy i ≤ homogeneousSubmodule (Fin n) ℂ i.toUnboundedHarmonicIndex.degree) ∧
    iSupIndep (finiteCommonHarmonicCopy (n := n) (s := s)) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
      ordinaryHarmonics (griffinIdeal ℂ n lam s) =
        ⨆ i : {i : FiniteHarmonicIndex n s // i.toUnboundedHarmonicIndex.eligible lam hk},
          finiteCommonHarmonicCopy i.val

/-- The complete locally finite simultaneous-copy assertion of Theorem 6.6.
The empty-partition case is included in the quantified ideal equality. -/
def UntruncatedSimultaneousHarmonicTarget : Prop :=
  ∀ n : ℕ,
    (∀ i : UnboundedHarmonicIndex n,
      IsSpechtPolynomialCopy i.part (untruncatedCommonHarmonicCopy i) ∧
      untruncatedCommonHarmonicCopy i ≤ homogeneousSubmodule (Fin n) ℂ i.degree) ∧
    iSupIndep (untruncatedCommonHarmonicCopy (n := n)) ∧
    (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d}) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n),
      ordinaryHarmonics (untruncatedIdeal ℂ n lam) =
        ⨆ i : {i : UnboundedHarmonicIndex n // i.eligible lam hk},
          untruncatedCommonHarmonicCopy i.val

end HigherSpecht
end
end CanonicalSource46

section CanonicalSource47
/- Source: HigherSpecht/OrdinaryHarmonicCalculus.lean -/



/-!
# The ordinary differential action and its genuine harmonic submodules

These lemmas work with the action already identified with Mathlib partial
derivatives.  Differentiation, permutation, and the adjoint Young operator
preserve the appropriate actual annihilator; factorial-normalized column
witnesses are connected to that annihilator explicitly.
-/

noncomputable section

open MvPolynomial TauCeti Finset

namespace HigherSpecht

theorem ordinaryAction_mul_apply {sigma K : Type*} [Fintype sigma] [DecidableEq sigma]
    [Field K] [CharZero K] (f g p : MvPolynomial sigma K) :
    ordinaryAction (f * g) p = ordinaryAction f (ordinaryAction g p) := by
  rw [map_mul]
  rfl

theorem ordinaryAction_comm_apply {sigma K : Type*} [Fintype sigma] [DecidableEq sigma]
    [Field K] [CharZero K] (f g p : MvPolynomial sigma K) :
    ordinaryAction f (ordinaryAction g p) = ordinaryAction g (ordinaryAction f p) := by
  rw [← ordinaryAction_mul_apply, mul_comm, ordinaryAction_mul_apply]

theorem ordinaryAction_C_apply {sigma K : Type*} [Fintype sigma] [DecidableEq sigma]
    [Field K] [CharZero K] (c : K) (p : MvPolynomial sigma K) :
    ordinaryAction (MvPolynomial.C c) p = c • p := by
  rw [show MvPolynomial.C c = algebraMap K (MvPolynomial sigma K) c from rfl,
    AlgHom.commutes]
  rfl

theorem ordinaryAction_rename_equiv {sigma tau K : Type*}
    [Fintype sigma] [DecidableEq sigma] [Fintype tau] [DecidableEq tau]
    [Field K] [CharZero K] (e : sigma ≃ tau) (f p : MvPolynomial sigma K) :
    ordinaryAction (MvPolynomial.rename e f) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (ordinaryAction f p) := by
  induction f using MvPolynomial.induction_on generalizing p with
  | C c => simp only [rename_C, ordinaryAction_C_apply, map_smul]
  | add f g ihf ihg =>
    simp only [map_add, LinearMap.add_apply, ihf, ihg]
  | mul_X f i ih =>
    rw [map_mul, rename_X, ordinaryAction_mul_apply, ordinaryAction_mul_apply]
    simp only [ordinaryAction_X, Derivation.coeFn_coe,
      MvPolynomial.pderiv_rename e.injective, ih]

theorem ordinaryAction_mem_harmonics {n : ℕ} {I : Ideal (PolynomialRing n ℂ)}
    {p : PolynomialRing n ℂ} (hp : p ∈ ordinaryHarmonics I) (g : PolynomialRing n ℂ) :
    ordinaryAction g p ∈ ordinaryHarmonics I := by
  intro f hf
  rw [ordinaryAction_comm_apply, hp f hf, map_zero]

theorem ordinaryHarmonics_antitone {n : ℕ} :
    Antitone (ordinaryHarmonics : Ideal (PolynomialRing n ℂ) → Submodule ℂ (PolynomialRing n ℂ)) :=
  fun I J hIJ p hp f hf => hp f (hIJ hf)

theorem ordinaryHarmonics_rename_mem {n : ℕ} {I : Ideal (PolynomialRing n ℂ)}
    (hI : PermutationStable I) (e : Equiv.Perm (Fin n))
    {p : PolynomialRing n ℂ} (hp : p ∈ ordinaryHarmonics I) :
    MvPolynomial.rename e p ∈ ordinaryHarmonics I := by
  intro f hf
  have h := ordinaryAction_rename_equiv e (MvPolynomial.rename e.symm f) p
  rw [rename_rename, Equiv.self_comp_symm, rename_id_apply] at h
  rw [h, hp _ (hI e.symm f hf), map_zero]

def ordinaryHarmonicRepresentation {n : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hI : PermutationStable I) :
    Subrepresentation (polynomialRepresentation ℂ n) where
  toSubmodule := ordinaryHarmonics I
  apply_mem_toSubmodule e p hp := ordinaryHarmonics_rename_mem hI e hp

theorem rowSymmetrize_mem_ordinaryHarmonics {n : ℕ} {I : Ideal (PolynomialRing n ℂ)}
    (hI : PermutationStable I) (G : Subgroup (Equiv.Perm (Fin n)))
    {p : PolynomialRing n ℂ} (hp : p ∈ ordinaryHarmonics I) :
    rowSymmetrize G p ∈ ordinaryHarmonics I := by
  apply (ordinaryHarmonics I).sum_mem
  intro e he
  exact ordinaryHarmonics_rename_mem hI e.val hp

theorem columnAlternate_mem_ordinaryHarmonics {n : ℕ} {I : Ideal (PolynomialRing n ℂ)}
    (hI : PermutationStable I) (G : Subgroup (Equiv.Perm (Fin n)))
    {p : PolynomialRing n ℂ} (hp : p ∈ ordinaryHarmonics I) :
    columnAlternate G p ∈ ordinaryHarmonics I := by
  apply (ordinaryHarmonics I).sum_mem
  intro e he
  exact (ordinaryHarmonics I).smul_mem _ (ordinaryHarmonics_rename_mem hI e.val hp)

theorem adjointYoungApply_mem_ordinaryHarmonics {mu : YoungDiagram}
    {I : Ideal (PolynomialRing mu.card ℂ)} (hI : PermutationStable I)
    (T : TauCeti.YoungTableau mu) {p : PolynomialRing mu.card ℂ}
    (hp : p ∈ ordinaryHarmonics I) :
    adjointYoungApply T p ∈ ordinaryHarmonics I :=
  rowSymmetrize_mem_ordinaryHarmonics hI _ (columnAlternate_mem_ordinaryHarmonics hI _ hp)

theorem cyclicPolynomialCopy_le_ordinaryHarmonics {n : ℕ}
    {I : Ideal (PolynomialRing n ℂ)} (hI : PermutationStable I)
    {p : PolynomialRing n ℂ} (hp : p ∈ ordinaryHarmonics I) :
    cyclicPolynomialCopy p ≤ ordinaryHarmonics I := by
  apply Submodule.span_le.mpr
  rintro q ⟨e, rfl⟩
  exact ordinaryHarmonics_rename_mem hI e hp

theorem columnWitness_mem_ordinaryHarmonics {n : ℕ} {mu : YoungDiagram}
    (U : ↥mu.cells ↪ Fin n) (s : ℕ) {I : Ideal (PolynomialRing n ℂ)}
    (hU : columnWitness (R := ℂ) U s ∈ dividedHarmonics I) :
    columnWitness (R := ℂ) U s ∈ ordinaryHarmonics I := by
  intro f hf
  exact ordinaryAction_columnWitness_eq_zero_of_divided U s f (hU f hf)

theorem griffinApolarWitness_mem_ordinaryHarmonics {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (T : TauCeti.YoungTableau mu)
    (lam : YoungDiagram) (hk : lam.card ≤ mu.card) (s : ℕ)
    (hs : lam.colLen 0 ≤ s) (hs0 : 0 < s)
    (he : CatDominates (prefixTableau S lam.card hk) lam) :
    griffinApolarWitness (R := ℂ) S T lam.card hk s ∈
      ordinaryHarmonics (griffinIdeal ℂ mu.card lam s) :=
  columnWitness_mem_ordinaryHarmonics _ s
    (griffinApolarWitness_mem_harmonics S T lam hk s hs hs0 he)

end HigherSpecht
end
end CanonicalSource47

section CanonicalSource48
/- Source: HigherSpecht/CommonHarmonicMembership.lean -/



/-!
# The actual common finite witnesses annihilate every eligible ideal

The maximal prefix, its height cutoff, and every ideal inclusion are derived
from the complete restriction formula.  The ordinary derivative and adjoint
Young operator act on the literal manuscript witness.  No dimension count or
harmonic-decomposition premise appears in these membership theorems.
-/

noncomputable section

open TauCeti Finset MvPolynomial

namespace HigherSpecht

theorem ordinaryHarmonics_rename_finCongr {n m : ℕ} (h : n = m)
    (lam : YoungDiagram) (s : ℕ) {p : PolynomialRing n ℂ}
    (hp : p ∈ ordinaryHarmonics (griffinIdeal ℂ n lam s)) :
    MvPolynomial.rename (finCongr h) p ∈ ordinaryHarmonics (griffinIdeal ℂ m lam s) := by
  subst m
  simpa only [finCongr_refl, Equiv.coe_refl, rename_id_apply] using hp

theorem ordinaryUntruncatedHarmonics_rename_finCongr {n m : ℕ} (h : n = m)
    (lam : YoungDiagram) {p : PolynomialRing n ℂ}
    (hp : p ∈ ordinaryHarmonics (untruncatedIdeal ℂ n lam)) :
    MvPolynomial.rename (finCongr h) p ∈ ordinaryHarmonics (untruncatedIdeal ℂ m lam) := by
  subst m
  simpa only [finCongr_refl, Equiv.coe_refl, rename_id_apply] using hp

def finiteCommonPrefixShape {n s : ℕ} (i : FiniteHarmonicIndex n s) : YoungDiagram :=
  (columnInsertion (prefixTableau i.left (maximalFinitePrefix i) (maximalFinitePrefix_le i))).state.shape

theorem finiteCommonPrefixShape_card {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    (finiteCommonPrefixShape i).card = maximalFinitePrefix i :=
  prefixInsertionFilling_card i.left _ (maximalFinitePrefix_le i)

theorem finiteCommonPrefixShape_height {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    (finiteCommonPrefixShape i).colLen 0 ≤ s := by
  have hzero : (finiteCommonPrefixShape i).rowLen s = 0 := by
    rw [finiteCommonPrefixShape, catabolizability_prefix_rowLen]
    have hbound : maximalFinitePrefix i ≤ rowPrefixSum (columnInsertion i.left).state.shape s :=
      min_le_right _ _
    rw [Nat.sub_eq_zero_of_le hbound, _root_.min_zero]
  by_contra h
  have hc : (s, 0) ∈ (finiteCommonPrefixShape i).cells :=
    YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge h)
  have hpos := YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [hzero] at hpos
  exact Nat.not_lt_zero _ hpos

theorem maximalFinitePrefix_multiplier_length {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    i.multiplier.colLen 0 ≤ (YoungDiagram.ofPartition i.part).card - maximalFinitePrefix i := by
  have hk : maximalFinitePrefix i ≤ n - i.multiplier.colLen 0 := min_le_left _ _
  rw [YoungDiagram.card_ofPartition]
  have hlen := i.multiplier_length
  omega

theorem eligible_card_le_maximalFinitePrefix {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : lam.colLen 0 ≤ s)
    (he : i.toUnboundedHarmonicIndex.eligible lam hk) : lam.card ≤ maximalFinitePrefix i := by
  obtain ⟨hlen, hcat⟩ := he
  have hdom := (catDominates_prefix_iff i.left lam
    (by simpa only [YoungDiagram.card_ofPartition] using hk)).mp hcat
  have hsum := hdom s
  rw [← YoungDiagram.card_eq_sum_range_rowLen lam hs] at hsum
  apply le_min
  · omega
  · exact hsum

theorem finiteCommonPrefixShape_dominates {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : lam.colLen 0 ≤ s)
    (he : i.toUnboundedHarmonicIndex.eligible lam hk) :
    Dominates (finiteCommonPrefixShape i) lam := by
  have hcard := eligible_card_le_maximalFinitePrefix i lam hk hs he
  have hdom := (catDominates_prefix_iff i.left lam
    (by simpa only [YoungDiagram.card_ofPartition] using hk)).mp he.2
  intro r
  change rowPrefixSum lam r ≤ rowPrefixSum (finiteCommonPrefixShape i) r
  rw [finiteCommonPrefixShape, catabolizability_prefix_rowSums]
  exact le_min ((rowPrefixSum_le_card lam r).trans hcard) (hdom r)

theorem finiteCommonApolarWitness_mem_ordinaryHarmonics {n s : ℕ}
    (i : FiniteHarmonicIndex n s) (hs0 : 0 < s)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : lam.colLen 0 ≤ s)
    (he : i.toUnboundedHarmonicIndex.eligible lam hk) :
    griffinApolarWitness (R := ℂ) i.left
      (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)).toTableau
      (maximalFinitePrefix i) (maximalFinitePrefix_le i) s ∈
        ordinaryHarmonics (griffinIdeal ℂ (YoungDiagram.ofPartition i.part).card lam s) := by
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)).toTableau
  let U := ((insertionFilling (prefixTableau i.left (maximalFinitePrefix i)
      (maximalFinitePrefix_le i))
      (prefixTableau i.left (maximalFinitePrefix i) (maximalFinitePrefix_le i)).toTableau).toEmbedding).trans (prefixAmbientEmbedding i.left T (maximalFinitePrefix i)
          (maximalFinitePrefix_le i))
  have hU : columnWitness (R := ℂ) U s ∈
      ordinaryHarmonics (griffinIdeal ℂ (YoungDiagram.ofPartition i.part).card
        (finiteCommonPrefixShape i) s) :=
    columnWitness_mem_ordinaryHarmonics U s
      (columnWitness_mem_griffinHarmonics U hs0 (finiteCommonPrefixShape_height i))
  apply ordinaryHarmonics_antitone
    (griffinIdeal_le_of_dominates
      (by simpa only [YoungDiagram.card_ofPartition] using hk)
      (by rw [finiteCommonPrefixShape_card]; exact maximalFinitePrefix_le i)
      (finiteCommonPrefixShape_dominates i lam hk hs he)) hU

/-- Every literal common witness vector belongs to every harmonic space for
which its actual paper index is eligible. -/
theorem finiteCommonHarmonicVector_mem {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (hs0 : 0 < s) (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : lam.colLen 0 ≤ s)
    (he : i.toUnboundedHarmonicIndex.eligible lam hk) :
    finiteCommonHarmonicVector i ∈ ordinaryHarmonics (griffinIdeal ℂ n lam s) := by
  apply ordinaryHarmonics_rename_finCongr (YoungDiagram.card_ofPartition i.part) lam s
  apply (ordinaryHarmonics _).smul_mem
  apply adjointYoungApply_mem_ordinaryHarmonics (permutationStable_griffinIdeal lam s)
  exact ordinaryAction_mem_harmonics
    (finiteCommonApolarWitness_mem_ordinaryHarmonics i hs0 lam hk hs he) _

/-- The full cyclic copy has the required simultaneous membership. -/
theorem finiteCommonHarmonicCopy_le {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (hs0 : 0 < s) (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : lam.colLen 0 ≤ s)
    (he : i.toUnboundedHarmonicIndex.eligible lam hk) :
    finiteCommonHarmonicCopy i ≤ ordinaryHarmonics (griffinIdeal ℂ n lam s) :=
  cyclicPolynomialCopy_le_ordinaryHarmonics (permutationStable_griffinIdeal lam s)
    (finiteCommonHarmonicVector_mem i hs0 lam hk hs he)

end HigherSpecht
end
end CanonicalSource48

section CanonicalSource49
/- Source: HigherSpecht/SymmetrizerConvention.lean -/



/-!
# Justifying the column-after-row convention

Tau Ceti writes a Young symmetrizer as `a_T b_T`; the manuscript acts by
`b_T a_T`.  Inversion of group-algebra basis elements is an actual linear
anti-involution, fixing both subgroup sums.  Applying it to the verified
essential-idempotence identity gives the identity for the manuscript's
convention.  The resulting operator is then identified with `youngApply`.
-/

noncomputable section

open Finset TauCeti
open TauCeti.YoungTableau

namespace HigherSpecht

section Inversion

variable {R G : Type*} [CommRing R] [Group G]

def inverseGroupAlgebra : MonoidAlgebra R G ≃ₗ[R] MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainLinearEquiv R R (Equiv.inv G)

@[simp] theorem inverseGroupAlgebra_single (g : G) (r : R) :
    inverseGroupAlgebra (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
  simp only [inverseGroupAlgebra, MonoidAlgebra.mapDomainLinearEquiv_single, Equiv.inv_apply]

@[simp] theorem inverseGroupAlgebra_coeff (f : MonoidAlgebra R G) (g : G) :
    (inverseGroupAlgebra f).coeff g = f.coeff g⁻¹ := by
  simp only [inverseGroupAlgebra, MonoidAlgebra.coeff_mapDomainLinearEquiv,
    Finsupp.equivMapDomain_apply, Equiv.inv_symm, Equiv.inv_apply]

@[simp] theorem inverseGroupAlgebra_involutive (f : MonoidAlgebra R G) :
    inverseGroupAlgebra (inverseGroupAlgebra f) = f := by
  ext g
  simp

theorem inverseGroupAlgebra_mul (f g : MonoidAlgebra R G) :
    inverseGroupAlgebra (f * g) = inverseGroupAlgebra g * inverseGroupAlgebra f := by
  apply MonoidAlgebra.induction_on f
  · intro x
    apply MonoidAlgebra.induction_on g
    · intro y
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
        inverseGroupAlgebra_single, mul_inv_rev, one_mul]
    · intro u v hu hv
      simp only [mul_add, map_add, hu, hv, add_mul]
    · intro r u hu
      simp only [mul_smul_comm, map_smul, hu, smul_mul_assoc]
  · intro u v hu hv
    simp only [add_mul, map_add, hu, hv, mul_add]
  · intro r u hu
    simp only [smul_mul_assoc, map_smul, hu, mul_smul_comm]

end Inversion

variable {μ : YoungDiagram}

@[simp] theorem inverseGroupAlgebra_rowSymmetrizer (T : YoungTableau μ) :
    inverseGroupAlgebra (TauCeti.YoungTableau.rowSymmetrizer T) =
      TauCeti.YoungTableau.rowSymmetrizer T := by
  classical
  ext σ
  simp only [inverseGroupAlgebra_coeff, TauCeti.YoungTableau.rowSymmetrizer_coeff]
  exact ite_cond_congr (propext ((rowSubgroup T).inv_mem_iff))

@[simp] theorem inverseGroupAlgebra_columnAntisymmetrizer (T : YoungTableau μ) :
    inverseGroupAlgebra (columnAntisymmetrizer T) = columnAntisymmetrizer T := by
  classical
  ext σ
  simp only [inverseGroupAlgebra_coeff, columnAntisymmetrizer_coeff, Equiv.Perm.sign_inv]
  exact ite_cond_congr (propext ((colSubgroup T).inv_mem_iff))

def paperYoungSymmetrizer (T : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  columnAntisymmetrizer T * TauCeti.YoungTableau.rowSymmetrizer T

theorem paperYoungSymmetrizer_eq_inverse (T : YoungTableau μ) :
    paperYoungSymmetrizer T = inverseGroupAlgebra (youngSymmetrizer T) := by
  rw [youngSymmetrizer_def, inverseGroupAlgebra_mul,
    inverseGroupAlgebra_columnAntisymmetrizer, inverseGroupAlgebra_rowSymmetrizer]
  rfl

def youngScalar (T : YoungTableau μ) : ℚ :=
  (μ.card.factorial : ℚ) / (Module.finrank ℚ (spechtIdeal T) : ℚ)

theorem youngScalar_pos (T : YoungTableau μ) : 0 < youngScalar T := by
  apply div_pos
  · exact_mod_cast Nat.factorial_pos μ.card
  · exact_mod_cast finrank_spechtIdeal_pos T

theorem paperYoungSymmetrizer_sq (T : YoungTableau μ) :
    paperYoungSymmetrizer T * paperYoungSymmetrizer T =
      youngScalar T • paperYoungSymmetrizer T := by
  have h := congrArg inverseGroupAlgebra (youngSymmetrizer_sq T)
  rw [inverseGroupAlgebra_mul, map_smul] at h
  simpa only [← paperYoungSymmetrizer_eq_inverse, youngScalar] using h

theorem paperYoungSymmetrizer_ne_zero (T : YoungTableau μ) :
    paperYoungSymmetrizer T ≠ 0 := by
  rw [paperYoungSymmetrizer_eq_inverse]
  intro h
  apply youngSymmetrizer_ne_zero T
  apply inverseGroupAlgebra.injective
  simpa only [map_zero] using h

variable (R : Type*) [CommRing R] [Algebra ℚ R]

def paperYoungSymmetrizerOver (T : YoungTableau μ) :
    MonoidAlgebra R (Equiv.Perm (Fin μ.card)) :=
  MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ R) (paperYoungSymmetrizer T)

theorem paperYoungSymmetrizerOver_sq (T : YoungTableau μ) :
    paperYoungSymmetrizerOver R T * paperYoungSymmetrizerOver R T =
      algebraMap ℚ R (youngScalar T) • paperYoungSymmetrizerOver R T := by
  rw [algebraMap_smul, paperYoungSymmetrizerOver, ← map_mul,
    paperYoungSymmetrizer_sq, map_smul]

theorem asAlgebraHom_paperYoungSymmetrizer (T : YoungTableau μ)
    (f : PolynomialRing μ.card R) :
    (polynomialRepresentation R μ.card).asAlgebraHom (paperYoungSymmetrizerOver R T) f =
      youngApply T f := by
  classical
  simp only [paperYoungSymmetrizerOver, paperYoungSymmetrizer,
    columnAntisymmetrizer_def, TauCeti.YoungTableau.rowSymmetrizer_def,
    map_mul, map_sum, map_smul, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.mapAlgHom_single,
    Algebra.ofId_apply, map_one, Representation.asAlgebraHom_single,
    one_smul, polynomialRepresentation_apply]
  simp only [youngApply, columnAlternate, rowSymmetrize, map_sum,
    Finset.smul_sum, algebraMap_smul, map_intCast]
  rw [Finset.sum_comm]
  simp only [Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply,
    Representation.asAlgebraHom_single, one_smul, polynomialRepresentation_apply]

theorem youngApply_youngApply (T : YoungTableau μ) (f : PolynomialRing μ.card R) :
    youngApply T (youngApply T f) = algebraMap ℚ R (youngScalar T) • youngApply T f := by
  have h := congrArg (fun a : MonoidAlgebra R (Equiv.Perm (Fin μ.card)) =>
    (polynomialRepresentation R μ.card).asAlgebraHom a f) (paperYoungSymmetrizerOver_sq R T)
  simpa only [map_mul, Module.End.mul_apply, asAlgebraHom_paperYoungSymmetrizer,
    map_smul, LinearMap.smul_apply] using h

theorem rowSymmetrize_injective_on_youngApply_range [Nontrivial R]
    (T : YoungTableau μ) :
    Set.InjOn (rowSymmetrize (R := R) (rowSubgroup T)) (Set.range (youngApply (R := R) T)) := by
  rintro u ⟨f, rfl⟩ v ⟨g, rfl⟩ h
  have h' := congrArg (columnAlternate (R := R) (colSubgroup T)) h
  change youngApply T (youngApply T f) = youngApply T (youngApply T g) at h'
  rw [youngApply_youngApply, youngApply_youngApply] at h'
  have hκ : IsUnit (algebraMap ℚ R (youngScalar T)) :=
    (isUnit_iff_ne_zero.mpr (youngScalar_pos T).ne').map (algebraMap ℚ R)
  exact hκ.smul_left_cancel.mp h'

end HigherSpecht
end
end CanonicalSource49

section CanonicalSource50
/- Source: HigherSpecht/OrdinaryApolarPairing.lean -/



/-!
# The genuine ordinary apolar pairing and adjoint Young operator

The factorial derivative represents the exact shifted coefficient functional.
Group-algebra inversion is proved to be the adjoint operation for this
pairing.  Consequently the literal common harmonic vectors have the same
triangular coefficients as the actual witnesses, with explicit nonzero
factorial and Young scalars.
-/

noncomputable section

open MvPolynomial TauCeti TauCeti.YoungTableau Finset

namespace HigherSpecht

def ordinaryApolarFunctional {n : ℕ} (g : PolynomialRing n ℂ) :
    Module.Dual ℂ (PolynomialRing n ℂ) :=
  (MvPolynomial.lcoeff ℂ 0).comp ((LinearMap.applyₗ g).comp ordinaryAction.toLinearMap)

@[simp] theorem ordinaryApolarFunctional_apply {n : ℕ} (g f : PolynomialRing n ℂ) :
    ordinaryApolarFunctional g f = (ordinaryAction f g).coeff 0 := rfl

def ordinaryApolarRepresenter (n : ℕ) :
    PolynomialRing n ℂ →ₗ[ℂ] Module.Dual ℂ (PolynomialRing n ℂ) where
  toFun := ordinaryApolarFunctional
  map_add' g h := by ext f; simp [ordinaryApolarFunctional_apply]
  map_smul' c g := by ext f; simp [ordinaryApolarFunctional_apply]

theorem ordinaryAction_monomial_coeff {n : ℕ} (r a : Fin n →₀ ℕ) (p : PolynomialRing n ℂ) :
    (ordinaryAction (MvPolynomial.monomial r (1 : ℂ)) p).coeff a =
      p.coeff (a + r) * (exponentFactorial (a + r) : ℂ) / exponentFactorial a := by
  have h := ordinaryAction_factorialTransport (MvPolynomial.monomial r (1 : ℂ))
    ((factorialTransport (σ := Fin n) (K := ℂ)).symm p)
  rw [LinearEquiv.apply_symm_apply, dividedAction_monomial, one_smul] at h
  have hc := congrArg (fun q : PolynomialRing n ℂ => q.coeff a) h
  change (ordinaryAction (MvPolynomial.monomial r (1 : ℂ)) p).coeff a =
    (factorialNormalize (contractMonomial r (factorialDenormalize p))).coeff a at hc
  simpa only [coeff_factorialNormalize, coeff_contractMonomial, coeff_factorialDenormalize] using hc

def normalizedOrdinaryDerivative {n : ℕ} (r : Fin n →₀ ℕ) (g : PolynomialRing n ℂ) :
    PolynomialRing n ℂ :=
  (exponentFactorial r : ℂ)⁻¹ • ordinaryAction (MvPolynomial.monomial r (1 : ℂ)) g

theorem ordinaryApolar_normalizedDerivative {n : ℕ} (r : Fin n →₀ ℕ)
    (g f : PolynomialRing n ℂ) :
    ordinaryApolarFunctional (normalizedOrdinaryDerivative r g) f =
      (ordinaryAction f g).coeff r := by
  rw [ordinaryApolarFunctional_apply, normalizedOrdinaryDerivative, map_smul,
    MvPolynomial.coeff_smul, ordinaryAction_comm_apply, ordinaryAction_monomial_coeff]
  simp only [zero_add, exponentFactorial, Finsupp.zero_apply, Nat.factorial_zero,
    Finset.prod_const_one, Nat.cast_one, div_one, smul_eq_mul]
  have hfac := exponentFactorial_ne_zero (K := ℂ) r
  unfold exponentFactorial at hfac
  field_simp

theorem coeff_zero_rename_perm {n : ℕ} (e : Equiv.Perm (Fin n)) (p : PolynomialRing n ℂ) :
    (MvPolynomial.rename e p).coeff 0 = p.coeff 0 := by
  simpa only [Finsupp.mapDomain_zero] using
    MvPolynomial.coeff_rename_mapDomain e e.injective p 0

theorem ordinaryApolar_rename_adjoint {n : ℕ} (e : Equiv.Perm (Fin n))
    (f g : PolynomialRing n ℂ) :
    ordinaryApolarFunctional (MvPolynomial.rename e g) f =
      ordinaryApolarFunctional g (MvPolynomial.rename e.symm f) := by
  have h := ordinaryAction_rename_equiv e (MvPolynomial.rename e.symm f) g
  rw [rename_rename, Equiv.self_comp_symm, rename_id_apply] at h
  rw [ordinaryApolarFunctional_apply, h, coeff_zero_rename_perm]
  rfl

theorem ordinaryApolar_groupAlgebra_adjoint {n : ℕ}
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (f g : PolynomialRing n ℂ) :
    ordinaryApolarFunctional ((polynomialRepresentation ℂ n).asAlgebraHom a g) f =
      ordinaryApolarFunctional g
        ((polynomialRepresentation ℂ n).asAlgebraHom (inverseGroupAlgebra a) f) := by
  induction a using MonoidAlgebra.induction_on with
  | of e =>
    simpa only [MonoidAlgebra.of_apply, inverseGroupAlgebra_single,
      Representation.asAlgebraHom_single, one_smul, polynomialRepresentation_apply,
      Equiv.Perm.inv_def]
      using ordinaryApolar_rename_adjoint e f g
  | add a b iha ihb =>
    simp only [map_add, LinearMap.add_apply, ordinaryApolarFunctional_apply,
      MvPolynomial.coeff_add] at iha ihb ⊢
    rw [iha, ihb]
  | smul c a ih =>
    simp only [map_smul, LinearMap.smul_apply, ordinaryApolarFunctional_apply,
      MvPolynomial.coeff_smul, smul_eq_mul] at ih ⊢
    rw [ih]

theorem asAlgebraHom_youngSymmetrizer_adjoint {mu : YoungDiagram}
    (T : YoungTableau mu) (g : PolynomialRing mu.card ℂ) :
    (polynomialRepresentation ℂ mu.card).asAlgebraHom (youngSymmetrizerOver ℂ T) g =
      adjointYoungApply T g := by
  simp only [youngSymmetrizerOver_def, youngSymmetrizer_def,
    columnAntisymmetrizer_def, TauCeti.YoungTableau.rowSymmetrizer_def,
    map_mul, map_sum, map_smul, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.mapAlgHom_single,
    Algebra.ofId_apply, map_one, Representation.asAlgebraHom_single,
    one_smul, polynomialRepresentation_apply]
  simp only [adjointYoungApply, columnAlternate, rowSymmetrize, map_sum,
    map_smul, Finset.smul_sum, algebraMap_smul, map_intCast]
  rw [Finset.sum_comm]
  simp only [Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply,
    Representation.asAlgebraHom_single, one_smul, polynomialRepresentation_apply]

theorem inverseGroupAlgebra_youngSymmetrizerOver {mu : YoungDiagram} (T : YoungTableau mu) :
    inverseGroupAlgebra (youngSymmetrizerOver ℂ T) = paperYoungSymmetrizerOver ℂ T := by
  ext e
  simp only [inverseGroupAlgebra_coeff, youngSymmetrizerOver_coeff,
    paperYoungSymmetrizerOver, MonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply,
    paperYoungSymmetrizer_eq_inverse, inverseGroupAlgebra_coeff]

theorem ordinaryApolar_adjointYoung {mu : YoungDiagram} (T : YoungTableau mu)
    (f g : PolynomialRing mu.card ℂ) :
    ordinaryApolarFunctional (adjointYoungApply T g) f =
      ordinaryApolarFunctional g (youngApply T f) := by
  rw [← asAlgebraHom_youngSymmetrizer_adjoint,
    ordinaryApolar_groupAlgebra_adjoint, inverseGroupAlgebra_youngSymmetrizerOver,
    asAlgebraHom_paperYoungSymmetrizer]

theorem youngApply_mul_elementaryMultiplier {mu : YoungDiagram} (T : YoungTableau mu)
    (f : PolynomialRing mu.card ℂ) (m : ℕ) (eta : YoungDiagram) :
    youngApply T (f * elementaryMultiplier mu.card m eta.rowLen) =
      youngApply T f * elementaryMultiplier mu.card m eta.rowLen := by
  have hsym (e : Equiv.Perm (Fin mu.card)) :
      MvPolynomial.rename e (elementaryMultiplier (R := ℂ) mu.card m eta.rowLen) =
        elementaryMultiplier mu.card m eta.rowLen :=
    elementaryMultiplier_isSymmetric mu.card m eta.rowLen e
  simp only [youngApply, columnAlternate, rowSymmetrize, map_mul,
    hsym, ← Finset.sum_mul, map_sum, smul_mul_assoc]
  simp only [← smul_mul_assoc, ← Finset.sum_mul]

theorem ordinaryApolar_commonWitness_pairing {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (eta : YoungDiagram) (m : ℕ)
    (r : Fin mu.card →₀ ℕ) (G : PolynomialRing mu.card ℂ) :
    ordinaryApolarFunctional (adjointYoungApply T.toTableau (normalizedOrdinaryDerivative r G))
      (higherSpechtPolynomial S T * elementaryMultiplier mu.card m eta.rowLen) =
      algebraMap ℚ ℂ (youngScalar T.toTableau) *
        (ordinaryAction (higherSpechtPolynomial S T * elementaryMultiplier mu.card m eta.rowLen) G).coeff r := by
  rw [ordinaryApolar_adjointYoung, youngApply_mul_elementaryMultiplier,
    higherSpechtPolynomial, youngApply_youngApply, smul_mul_assoc, map_smul,
    smul_eq_mul, ordinaryApolar_normalizedDerivative]

end HigherSpecht
end
end CanonicalSource50

section CanonicalSource51
/- Source: HigherSpecht/CommonHarmonicIndependence.lean -/



/-!
# Independence of the literal common harmonic multiplicity vectors

The cut in the witness may vary with the index.  The original rearrangement
argument still gives the same triangular coefficient matrix, and the exact
ordinary-apolar adjoint identity transposes that matrix.  The diagonal scalar
is an explicit nonzero factorial ratio times the Young scalar.  No dimension
or spanning assertion is assumed here.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Finset MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem ordinaryAction_coefficientWitness_coeff {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a r : Fin n →₀ ℕ) (f : PolynomialRing n ℂ) :
    (ordinaryAction f (coefficientWitness G a)).coeff r =
      ((exponentFactorial a : ℂ) / exponentFactorial r) * witnessCoefficient G a r f := by
  exact ordinary_coefficient_eq_factorial_mul_contraction Finset.univ
    (fun e : G => permutedExponent a e.val) (fun e : G => coefficientSign e.val)
    (exponentFactorial a) (exponentFactorial_pos a)
    (fun e _ => exponentFactorial_permuted a e.val) f r

abbrev FixedFiniteHarmonicIndex (mu : YoungDiagram) (s : ℕ) :=
  FixedGriffinIndex mu ⊥ (by simp [YoungDiagram.card]) s

def fixedCommonCut {mu : YoungDiagram} {s : ℕ} (i : FixedFiniteHarmonicIndex mu s) : ℕ :=
  min (mu.card - i.multiplier.colLen 0)
    (∑ j ∈ Finset.range s, (columnInsertion i.left).state.shape.rowLen j)

theorem fixedCommonCut_le {mu : YoungDiagram} {s : ℕ} (i : FixedFiniteHarmonicIndex mu s) :
    fixedCommonCut i ≤ mu.card := (min_le_left _ _).trans (Nat.sub_le _ _)

theorem fixedCommonCut_multiplier_length {mu : YoungDiagram} {s : ℕ}
    (i : FixedFiniteHarmonicIndex mu s) : i.multiplier.colLen 0 ≤ mu.card - fixedCommonCut i := by
  have hk : fixedCommonCut i ≤ mu.card - i.multiplier.colLen 0 := min_le_left _ _
  have hi : i.multiplier.colLen 0 ≤ mu.card := by
    simpa [YoungDiagram.card] using i.multiplier_length
  omega

def fixedCommonWitnessFunctional {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    Module.Dual ℂ (PolynomialRing mu.card ℂ) :=
  griffinCoefficientFunctional i.left T.toTableau i.multiplier
    (fixedCommonCut i) (fixedCommonCut_le i) s

def fixedCommonHarmonicVector {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) : PolynomialRing mu.card ℂ :=
  adjointYoungApply T.toTableau (normalizedOrdinaryDerivative
    (griffinWitnessRejection i.left T.toTableau i.multiplier
      (fixedCommonCut i) (fixedCommonCut_le i) s)
    (griffinApolarWitness i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i) s))

def fixedCommonPairingScalar {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) : ℂ :=
  algebraMap ℚ ℂ (youngScalar T.toTableau) *
    ((exponentFactorial (griffinWitnessAlpha i.left T.toTableau
      (fixedCommonCut i) (fixedCommonCut_le i) s) : ℂ) /
      exponentFactorial (griffinWitnessRejection i.left T.toTableau i.multiplier
        (fixedCommonCut i) (fixedCommonCut_le i) s))

theorem fixedCommonPairingScalar_ne_zero {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    fixedCommonPairingScalar T i ≠ 0 := by
  apply mul_ne_zero
  · exact (map_ne_zero (algebraMap ℚ ℂ)).mpr (youngScalar_pos T.toTableau).ne'
  · exact div_ne_zero (exponentFactorial_ne_zero _) (exponentFactorial_ne_zero _)

theorem fixedCommonWitnessFunctional_offDiagonal {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i j : FixedFiniteHarmonicIndex mu s)
    (hne : i ≠ j) (hkey : fixedGriffinKey T j ≤ fixedGriffinKey T i) :
    fixedCommonWitnessFunctional T i (fixedGriffinPolynomial T j) = 0 := by
  rw [fixedCommonWitnessFunctional, griffinCoefficientFunctional_eq]
  apply witnessCoefficient_eq_zero_of_key_finiteRange
    (row := fun i => (rowIndex T.toTableau i : ℤ))
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier
      (fixedCommonCut i) (fixedCommonCut_le i) s
      (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (griffinWitnessGroup_preserves i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (fixedGriffinPolynomial T j)
    (boosted_higherSpecht_triangularSupport j.left T (Nat.sub_le _ _)
      j.multiplier j.multiplier_length)
    hkey (fun h => hne (fixedGriffinBoost_injective T h))
    (rowIndex_injective_on_intColumn T.toTableau)
    (transportedBoosted_intColumnMonovary i.left T.toTableau i.multiplier)
    (transportedBoosted_intColumnMonovary j.left T.toTableau j.multiplier)

theorem fixedCommonWitnessFunctional_diagonal {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    fixedCommonWitnessFunctional T i (fixedGriffinPolynomial T i) =
      ((rowFillingStabilizers T.toTableau (transportedCocharge i.left T.toTableau)).card : ℂ) *
      ((fixedWitnessPermutations
        (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
        (griffinWitnessRejection i.left T.toTableau i.multiplier
          (fixedCommonCut i) (fixedCommonCut_le i) s)
        (fun j => (colIndex T.toTableau j : ℤ))).card : ℂ) := by
  rw [fixedCommonWitnessFunctional, griffinCoefficientFunctional_eq]
  rw [witnessCoefficient_diagonal_finiteRange
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier
      (fixedCommonCut i) (fixedCommonCut_le i) s
      (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (griffinWitnessGroup_preserves i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (fixedGriffinPolynomial T i)
    (boosted_higherSpecht_triangularSupport i.left T (Nat.sub_le _ _)
      i.multiplier i.multiplier_length)]
  · rw [fixedGriffinPolynomial, lemma_4_2_distinguishedCoefficient i.left T
      (Nat.sub_le _ _) i.multiplier i.multiplier_length]
  · intro e he
    rw [← coeff_rename_perm, fixedGriffinPolynomial,
      boostedPolynomial_columnAlternating i.left T _ i.multiplier e
        (fun j => Int.ofNat_inj.mp (congrFun he j)), MvPolynomial.coeff_smul, smul_eq_mul]

theorem fixedCommonWitnessFunctional_diagonal_ne_zero {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    fixedCommonWitnessFunctional T i (fixedGriffinPolynomial T i) ≠ 0 := by
  rw [fixedCommonWitnessFunctional_diagonal]
  apply mul_ne_zero
  · exact_mod_cast (Finset.card_pos.mpr
      (rowFillingStabilizers_nonempty T.toTableau (transportedCocharge i.left T.toTableau))).ne'
  · exact_mod_cast (Finset.card_pos.mpr (fixedWitnessPermutations_nonempty
      (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
      (griffinWitnessRejection i.left T.toTableau i.multiplier
        (fixedCommonCut i) (fixedCommonCut_le i) s)
      (fun j => (colIndex T.toTableau j : ℤ)))).ne'

theorem ordinaryApolar_fixedCommonHarmonicVector {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i j : FixedFiniteHarmonicIndex mu s) :
    ordinaryApolarFunctional (fixedCommonHarmonicVector T i) (fixedGriffinPolynomial T j) =
      fixedCommonPairingScalar T i *
        fixedCommonWitnessFunctional T i (fixedGriffinPolynomial T j) := by
  rw [fixedCommonHarmonicVector, fixedGriffinPolynomial,
    ordinaryApolar_commonWitness_pairing, griffinApolarWitness_eq_coefficientWitness,
    ordinaryAction_coefficientWitness_coeff]
  rw [fixedCommonPairingScalar, fixedCommonWitnessFunctional, griffinCoefficientFunctional_eq]
  exact (mul_assoc _ _ _).symm

/-- The literal maximal-prefix common vectors are independent in their
actual ordinary polynomial space.  The key is reversed because adjoint
transport transposes the coefficient matrix. -/
theorem fixedCommonHarmonicVector_linearIndependent {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) :
    LinearIndependent ℂ (fixedCommonHarmonicVector (s := s) T) := by
  let L : FixedFiniteHarmonicIndex mu s → Module.Dual ℂ (PolynomialRing mu.card ℂ) :=
    fun i => (LinearMap.applyₗ (fixedGriffinPolynomial T i)).comp
      (ordinaryApolarRepresenter mu.card)
  apply linearIndependent_of_pairing_key
    (fun i => OrderDual.toDual (fixedGriffinKey T i)) L
  · intro i j hne hkey
    change ordinaryApolarFunctional (fixedCommonHarmonicVector T j) (fixedGriffinPolynomial T i) = 0
    rw [ordinaryApolar_fixedCommonHarmonicVector,
      fixedCommonWitnessFunctional_offDiagonal T j i hne.symm hkey, mul_zero]
  · intro i
    change ordinaryApolarFunctional (fixedCommonHarmonicVector T i) (fixedGriffinPolynomial T i) ≠ 0
    rw [ordinaryApolar_fixedCommonHarmonicVector]
    exact mul_ne_zero (fixedCommonPairingScalar_ne_zero T i)
      (fixedCommonWitnessFunctional_diagonal_ne_zero T i)

end HigherSpecht
end
end CanonicalSource51

section CanonicalSource52
/- Source: HigherSpecht/OutsideWitnessComparison.lean -/



/-!
# Exact factorial comparison when exterior witness powers are reduced

The finite witness and the untruncated witness have the same interior
alternant.  Their exterior exponents differ by a monomial fixed by the
column group.  Divided contraction first identifies the two actual
alternating polynomials.  The ordinary differentiation comparison then
follows from the already proved factorial conjugation, with an explicit
nonzero scalar.  This justifies comparison of the named common copies;
it does not replace either witness by a freely chosen vector.
-/

noncomputable section
open MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

theorem contractMonomial_coefficientWitness {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a d : Fin n →₀ ℕ)
    (hd : d ≤ a) (hfix : ∀ e : G, ∀ i, d (e.val i) = d i) :
    contractMonomial d (coefficientWitness (R := ℂ) G a) =
      coefficientWitness G (a - d) := by
  rw [coefficientWitness, map_sum, coefficientWitness]
  apply Finset.sum_congr rfl
  intro e he
  have hle : d ≤ permutedExponent a e.val := by
    intro i
    rw [permutedExponent_apply, ← hfix e i]
    exact hd (e.val i)
  have hsub : permutedExponent a e.val - d = permutedExponent (a - d) e.val := by
    ext i
    simp only [Finsupp.tsub_apply, permutedExponent_apply, hfix]
  rw [contractMonomial_monomial, if_pos hle, hsub]

theorem factorialNormalize_coefficientWitness {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n →₀ ℕ) :
    factorialNormalize (coefficientWitness (R := ℂ) G a) =
      (exponentFactorial a : ℂ)⁻¹ • coefficientWitness G a := by
  exact factorialNormalize_sum_of_common_factorial Finset.univ
    (fun e : G => permutedExponent a e.val) (fun e : G => coefficientSign e.val)
    (exponentFactorial a) (fun e _ => exponentFactorial_permuted a e.val)

theorem ordinaryAction_coefficientWitness_reduce_fixed {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a d : Fin n →₀ ℕ)
    (hd : d ≤ a) (hfix : ∀ e : G, ∀ i, d (e.val i) = d i) :
    ordinaryAction (MvPolynomial.monomial d (1 : ℂ)) (coefficientWitness G a) =
      ((exponentFactorial a : ℂ) / exponentFactorial (a - d)) •
        coefficientWitness G (a - d) := by
  have h := ordinaryAction_factorialTransport (MvPolynomial.monomial d (1 : ℂ))
    (coefficientWitness (R := ℂ) G a)
  change ordinaryAction (MvPolynomial.monomial d (1 : ℂ))
    (factorialNormalize (coefficientWitness G a)) =
      factorialNormalize (dividedAction (MvPolynomial.monomial d (1 : ℂ))
        (coefficientWitness G a)) at h
  rw [factorialNormalize_coefficientWitness, map_smul, dividedAction_monomial,
    LinearMap.smul_apply, one_smul, contractMonomial_coefficientWitness G a d hd hfix,
    factorialNormalize_coefficientWitness] at h
  have hmul := congrArg (fun p : PolynomialRing n ℂ => (exponentFactorial a : ℂ) • p) h
  simpa only [smul_smul, mul_inv_cancel₀ (exponentFactorial_ne_zero (K := ℂ) a), one_smul,
    div_eq_mul_inv] using hmul

def outsideWitnessComparisonScalar {n : ℕ} (a r d : Fin n →₀ ℕ) : ℂ :=
  ((exponentFactorial a : ℂ) / exponentFactorial (a - d)) *
    ((exponentFactorial r : ℂ) / exponentFactorial (r + d))

theorem outsideWitnessComparisonScalar_ne_zero {n : ℕ} (a r d : Fin n →₀ ℕ) :
    outsideWitnessComparisonScalar a r d ≠ 0 := by
  exact mul_ne_zero
    (div_ne_zero (exponentFactorial_ne_zero a) (exponentFactorial_ne_zero (a - d)))
    (div_ne_zero (exponentFactorial_ne_zero r) (exponentFactorial_ne_zero (r + d)))

/-- The literal ordinary normalized derivative of the finite witness is a
specified nonzero multiple of the derivative of its reduced exterior witness. -/
theorem normalizedOrdinaryDerivative_coefficientWitness_reduce_fixed {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a r d : Fin n →₀ ℕ)
    (hd : d ≤ a) (hfix : ∀ e : G, ∀ i, d (e.val i) = d i) :
    normalizedOrdinaryDerivative (r + d) (coefficientWitness G a) =
      outsideWitnessComparisonScalar a r d •
        normalizedOrdinaryDerivative r (coefficientWitness G (a - d)) := by
  have hmon : (MvPolynomial.monomial (r + d) (1 : ℂ) : PolynomialRing n ℂ) =
      MvPolynomial.monomial r 1 * MvPolynomial.monomial d 1 := by
    rw [MvPolynomial.monomial_mul]
    simp only [one_mul]
  rw [normalizedOrdinaryDerivative, hmon, ordinaryAction_mul_apply,
    ordinaryAction_coefficientWitness_reduce_fixed G a d hd hfix, map_smul]
  rw [normalizedOrdinaryDerivative, outsideWitnessComparisonScalar]
  simp only [smul_smul]
  congr 1
  have hr := exponentFactorial_ne_zero (K := ℂ) r
  field_simp
  <;> ring

theorem cyclicPolynomialCopy_smul {n : ℕ} {c : ℂ} (hc : c ≠ 0)
    (p : PolynomialRing n ℂ) : cyclicPolynomialCopy (c • p) = cyclicPolynomialCopy p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨e, rfl⟩
    change MvPolynomial.rename e (c • p) ∈ cyclicPolynomialCopy p
    rw [map_smul]
    exact (cyclicPolynomialCopy p).smul_mem c
      (Submodule.subset_span (Set.mem_range_self e))
  · apply Submodule.span_le.mpr
    rintro q ⟨e, rfl⟩
    change MvPolynomial.rename e p ∈ cyclicPolynomialCopy (c • p)
    have hmem : MvPolynomial.rename e (c • p) ∈ cyclicPolynomialCopy (c • p) :=
      Submodule.subset_span (Set.mem_range_self e)
    have h := (cyclicPolynomialCopy (c • p)).smul_mem c⁻¹ hmem
    simpa only [map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul] using h

end HigherSpecht
end
end CanonicalSource52

section CanonicalSource53
/- Source: HigherSpecht/UntruncatedWitnessComparison.lean -/



/-!
# The literal finite and untruncated prefix witnesses

The exterior exponent in the untruncated witness is the actual boosted
cocharge exponent.  The corresponding derivative has zero exterior order.
This file proves the exact nonzero-scalar comparison with every sufficiently
large finite witness at the same prefix.  The named untruncated polynomial
is retained throughout.
-/

noncomputable section
open MvPolynomial TauCeti TauCeti.YoungTableau Finset
open scoped Classical

namespace HigherSpecht

def exteriorPart {k n : ℕ} (e : Fin k ↪ Fin n) (b : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => if i ∈ Set.range e then 0 else b i

@[simp] theorem exteriorPart_inside {k n : ℕ} (e : Fin k ↪ Fin n)
    (b : Fin n →₀ ℕ) (i : Fin k) : exteriorPart e b (e i) = 0 := by
  simp [exteriorPart, Set.mem_range_self]

theorem exteriorPart_outside {k n : ℕ} (e : Fin k ↪ Fin n)
    (b : Fin n →₀ ℕ) {i : Fin n} (hi : i ∉ Set.range e) : exteriorPart e b i = b i := by
  rw [exteriorPart, Finsupp.equivFunOnFinite_symm_apply_apply, if_neg hi]

theorem coefficientWitness_partialFilling_fixed_exterior {k n : ℕ} {mu : YoungDiagram}
    (U : ↥mu.cells ≃ Fin k) (e : Fin k ↪ Fin n) (q : Fin n →₀ ℕ)
    (hq : ∀ i, q (e i) = 0) :
    coefficientWitness (R := ℂ)
      (embeddedPermutationGroup e (colorPermutationGroup (fullFillingColumn U)))
      ((fullFillingExponent U).mapDomain e + q) =
        (∏ j ∈ Finset.range n, columnAlternant (U.toEmbedding.trans e) j) *
          MvPolynomial.monomial q 1 := by
  rw [coefficientWitness_embedded e _ _ _ hq,
    coefficientWitness_fullFilling_eq_columnWitness U 1,
    columnWitness, outsidePower_equiv, mul_one, map_prod]
  simp_rw [rename_columnAlternant]
  congr 1
  have hkn : k ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  apply Finset.prod_subset (Finset.range_mono hkn)
  intro j hj hjnot
  exact columnAlternant_eq_one_of_width_le (U.toEmbedding.trans e)
    ((fullFilling_width_le U).trans (by simpa only [Finset.mem_range, not_lt] using hjnot))

variable {mu : YoungDiagram}

def untruncatedWitnessAlpha (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) : Fin mu.card →₀ ℕ :=
  (insertionAlpha (prefixTableau S k hk) (prefixTableau S k hk).toTableau).mapDomain
    (prefixAmbientEmbedding S T k hk) +
      exteriorPart (prefixAmbientEmbedding S T k hk) (transportedBoosted S T eta)

def untruncatedWitnessRejection (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) : Fin mu.card →₀ ℕ :=
  untruncatedWitnessAlpha S T eta k hk - transportedBoosted S T eta

def untruncatedApolarWitness (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) : PolynomialRing mu.card ℂ :=
  coefficientWitness (griffinWitnessGroup S T k hk) (untruncatedWitnessAlpha S T eta k hk)

@[simp] theorem untruncatedWitnessAlpha_inside (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card)
    (i : Fin (prefixShape S k).card) :
    untruncatedWitnessAlpha S T eta k hk (prefixAmbientEmbedding S T k hk i) =
      insertionAlpha (prefixTableau S k hk) (prefixTableau S k hk).toTableau i := by
  simp only [untruncatedWitnessAlpha, Finsupp.add_apply,
    Finsupp.mapDomain_apply_of_injective (prefixAmbientEmbedding S T k hk).injective,
    exteriorPart_inside, add_zero]

theorem untruncatedWitnessAlpha_outside (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card)
    {i : Fin mu.card} (hi : i ∉ Set.range (prefixAmbientEmbedding S T k hk)) :
    untruncatedWitnessAlpha S T eta k hk i = transportedBoosted S T eta i := by
  simp only [untruncatedWitnessAlpha, Finsupp.add_apply,
    Finsupp.mapDomain_of_notMem_range _ _ hi, exteriorPart_outside _ _ hi, zero_add]

theorem untruncatedApolarWitness_eq (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) :
    untruncatedApolarWitness S T eta k hk =
      (∏ j ∈ Finset.range mu.card, columnAlternant
        ((insertionFilling (prefixTableau S k hk) (prefixTableau S k hk).toTableau).toEmbedding.trans
          (prefixAmbientEmbedding S T k hk)) j) *
        MvPolynomial.monomial
          (exteriorPart (prefixAmbientEmbedding S T k hk) (transportedBoosted S T eta)) 1 := by
  exact coefficientWitness_partialFilling_fixed_exterior
    (insertionFilling (prefixTableau S k hk) (prefixTableau S k hk).toTableau)
    (prefixAmbientEmbedding S T k hk) _ (exteriorPart_inside _ _)

theorem boosted_le_untruncatedWitnessAlpha (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card)
    (hlen : eta.colLen 0 ≤ mu.card - k) :
    transportedBoosted S T eta ≤ untruncatedWitnessAlpha S T eta k hk := by
  intro i
  by_cases hi : i ∈ Set.range (prefixAmbientEmbedding S T k hk)
  · obtain ⟨j, rfl⟩ := hi
    rw [untruncatedWitnessAlpha_inside, prefixAmbientEmbedding_boost S T eta k hk hlen]
    have h := (insertion_rearrangementWitness
      (prefixTableau S k hk) (prefixTableau S k hk).toTableau).subtraction j
    dsimp only [intExponent] at h
    omega
  · rw [untruncatedWitnessAlpha_outside S T eta k hk hi]

theorem untruncatedWitnessAlpha_le_finite (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) (s : ℕ)
    (hdes : descentNumber S < s) (hwidth : eta.rowLen 0 ≤ s - descentNumber S - 1) :
    untruncatedWitnessAlpha S T eta k hk ≤ griffinWitnessAlpha S T k hk s := by
  intro i
  by_cases hi : i ∈ Set.range (prefixAmbientEmbedding S T k hk)
  · obtain ⟨j, rfl⟩ := hi
    rw [untruncatedWitnessAlpha_inside, griffinWitnessAlpha, embeddedWitnessAlpha_inside]
  · rw [untruncatedWitnessAlpha_outside S T eta k hk hi,
      griffinWitnessAlpha, embeddedWitnessAlpha_outside _ _ s i hi]
    exact Nat.le_pred_of_lt (boostedLabel_lt_bound S eta hdes hwidth (S (T.symm i)))

def witnessExteriorDifference (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) (s : ℕ) : Fin mu.card →₀ ℕ :=
  griffinWitnessAlpha S T k hk s - untruncatedWitnessAlpha S T eta k hk

theorem witnessExteriorDifference_fixed (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) (s : ℕ)
    (e : griffinWitnessGroup S T k hk) (i : Fin mu.card) :
    witnessExteriorDifference S T eta k hk s (e.val i) =
      witnessExteriorDifference S T eta k hk s i := by
  obtain ⟨sigma, hsigma, he⟩ := e.property
  have heq : e.val = sigma.viaEmbedding (prefixAmbientEmbedding S T k hk) := he.symm
  rw [heq]
  by_cases hi : i ∈ Set.range (prefixAmbientEmbedding S T k hk)
  · obtain ⟨j, rfl⟩ := hi
    rw [Equiv.Perm.viaEmbedding_apply]
    simp only [witnessExteriorDifference, Finsupp.tsub_apply, griffinWitnessAlpha,
      embeddedWitnessAlpha_inside, untruncatedWitnessAlpha_inside, Nat.sub_self]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hi]

theorem normalized_finiteWitness_eq_untruncated (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) (s : ℕ)
    (hlen : eta.colLen 0 ≤ mu.card - k) (hdes : descentNumber S < s)
    (hwidth : eta.rowLen 0 ≤ s - descentNumber S - 1) :
    normalizedOrdinaryDerivative (griffinWitnessRejection S T eta k hk s)
      (griffinApolarWitness S T k hk s) =
      outsideWitnessComparisonScalar (griffinWitnessAlpha S T k hk s)
        (untruncatedWitnessRejection S T eta k hk) (witnessExteriorDifference S T eta k hk s) •
          normalizedOrdinaryDerivative (untruncatedWitnessRejection S T eta k hk)
            (untruncatedApolarWitness S T eta k hk) := by
  have hsmall := boosted_le_untruncatedWitnessAlpha S T eta k hk hlen
  have hlarge := untruncatedWitnessAlpha_le_finite S T eta k hk s hdes hwidth
  have hd : witnessExteriorDifference S T eta k hk s ≤ griffinWitnessAlpha S T k hk s :=
    tsub_le_self
  have ha : griffinWitnessAlpha S T k hk s - witnessExteriorDifference S T eta k hk s =
      untruncatedWitnessAlpha S T eta k hk := by
    ext i
    have h := hlarge i
    simp only [witnessExteriorDifference, Finsupp.tsub_apply]
    omega
  have hr : griffinWitnessRejection S T eta k hk s =
      untruncatedWitnessRejection S T eta k hk + witnessExteriorDifference S T eta k hk s := by
    ext i
    have h := hlarge i
    have h' := hsmall i
    simp only [griffinWitnessRejection, untruncatedWitnessRejection,
      witnessExteriorDifference, Finsupp.tsub_apply, Finsupp.add_apply]
    omega
  rw [griffinApolarWitness_eq_coefficientWitness, hr,
    normalizedOrdinaryDerivative_coefficientWitness_reduce_fixed _ _ _ _ hd
      (witnessExteriorDifference_fixed S T eta k hk s), ha]
  rfl

end HigherSpecht
end
end CanonicalSource53

section CanonicalSource54
/- Source: HigherSpecht/CyclicYoungCopies.lean -/



/-!
# The full cyclic copies attached to actual Young-image vectors

The cyclic span is identified with the range of the genuine intertwiner from
the Young ideal.  Injectivity and simultaneous directness follow from the
verified Young tensor decomposition.  These are auxiliary representation
lemmas; their image-vector hypotheses must be instantiated by the actual
common polynomial witnesses.
-/

noncomputable section

open TauCeti Module

namespace HigherSpecht

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

def cyclicRepresentationSpan (rho : Representation K (Equiv.Perm (Fin n)) M) (v : M) :
    Submodule K M := Submodule.span K (Set.range fun g => rho g v)

theorem asAlgebraHom_mem_cyclicRepresentationSpan
    (rho : Representation K (Equiv.Perm (Fin n)) M) (v : M)
    (a : MonoidAlgebra K (Equiv.Perm (Fin n))) :
    rho.asAlgebraHom a v ∈ cyclicRepresentationSpan rho v := by
  apply MonoidAlgebra.induction_on a
  · intro g
    rw [Representation.asAlgebraHom_of]
    exact Submodule.subset_span (Set.mem_range_self g)
  · intro a b ha hb
    simpa only [map_add, LinearMap.add_apply] using
      (cyclicRepresentationSpan rho v).add_mem ha hb
  · intro c a ha
    simpa only [map_smul, LinearMap.smul_apply] using
      (cyclicRepresentationSpan rho v).smul_mem c ha

def intertwinerOfYoungImage (rho : Representation K (Equiv.Perm (Fin n)) M)
    (part : n.Partition) (v : YoungImage rho part) :
    (YoungIdealRepresentation (K := K) part).IntertwiningMap rho :=
  (youngHomImageEquiv rho part).symm v

theorem intertwinerOfYoungImage_generator
    (rho : Representation K (Equiv.Perm (Fin n)) M)
    (part : n.Partition) (v : YoungImage rho part) :
    intertwinerOfYoungImage rho part v (spanSingletonGenerator (part.youngSymmetrizer K)) = v := by
  exact Representation.spanSingletonHomEquivRange_symm_apply_generator rho _ _ v

theorem intertwinerOfYoungImage_smul_generator
    (rho : Representation K (Equiv.Perm (Fin n)) M)
    (part : n.Partition) (v : YoungImage rho part)
    (a : MonoidAlgebra K (Equiv.Perm (Fin n))) :
    intertwinerOfYoungImage rho part v (a • spanSingletonGenerator (part.youngSymmetrizer K)) =
      rho.asAlgebraHom a v := by
  exact Representation.spanSingletonHomEquivRange_symm_apply_smul_generator rho _ _ v a

theorem range_intertwinerOfYoungImage
    (rho : Representation K (Equiv.Perm (Fin n)) M)
    (part : n.Partition) (v : YoungImage rho part) :
    LinearMap.range (intertwinerOfYoungImage rho part v).toLinearMap =
      cyclicRepresentationSpan rho v := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨r, rfl⟩ := exists_smul_spanSingletonGenerator a
    rw [Representation.IntertwiningMap.toLinearMap_apply, intertwinerOfYoungImage_smul_generator]
    exact asAlgebraHom_mem_cyclicRepresentationSpan rho v r
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    refine ⟨(MonoidAlgebra.of K _ g) • spanSingletonGenerator (part.youngSymmetrizer K), ?_⟩
    rw [Representation.IntertwiningMap.toLinearMap_apply,
      intertwinerOfYoungImage_smul_generator, Representation.asAlgebraHom_of]

theorem intertwinerOfYoungImage_injective
    (rho : Representation K (Equiv.Perm (Fin n)) M)
    (part : n.Partition) (v : YoungImage rho part) (hv : v ≠ 0) :
    Function.Injective (intertwinerOfYoungImage rho part v) := by
  let b := Module.Free.chooseBasis K (YoungIdeal (K := K) part)
  have hsingleton : LinearIndependent K (fun _ : Unit => v) :=
    linearIndependent_unique_iff.mpr hv
  have h := independent_intertwiner_copies rho part b
    (fun _ : Unit => intertwinerOfYoungImage rho part v)
    (spanSingletonGenerator (part.youngSymmetrizer K)) b.linearIndependent
    (by simpa only [Function.comp_def, Submodule.subtype_apply,
      intertwinerOfYoungImage_generator] using
      hsingleton.map' (YoungImage rho part).subtype (Submodule.ker_subtype _))
  have hb : LinearIndependent K
      (fun j => intertwinerOfYoungImage rho part v (b j)) :=
    h.comp (fun j => (j, ())) (fun _ _ h => congrArg Prod.fst h)
  exact LinearMap.injective_of_linearIndependent b.span_eq hb

/-- Grouping an independent family into its actual spans preserves directness. -/
theorem linearIndependent_sigma_iSupIndep_span
    {I : Type*} {A : I → Type*} (v : ∀ i, A i → M)
    (hv : LinearIndependent K (fun z : Σ i, A i => v z.1 z.2)) :
    iSupIndep (fun i => Submodule.span K (Set.range (v i))) := by
  classical
  intro i
  let f : (Σ i, A i) → M := fun z => v z.1 z.2
  have hdisj : Disjoint {z : Σ i, A i | z.1 = i} {z : Σ i, A i | z.1 ≠ i} := by
    exact Set.disjoint_left.mpr (fun _ h hnot => hnot h)
  apply (hv.disjoint_span_image hdisj).mono
  · apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨i, a⟩, rfl, rfl⟩
  · apply iSup₂_le
    intro j hji
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨j, a⟩, hji, rfl⟩

set_option maxHeartbeats 800000 in
theorem intertwinerOfYoungImage_copies_iSupIndep
    (rho : Representation K (Equiv.Perm (Fin n)) M)
    {I : n.Partition → Type*} (v : ∀ part, I part → YoungImage rho part)
    (hv : ∀ part, LinearIndependent K (v part)) :
    iSupIndep (fun z : Σ part, I part => cyclicRepresentationSpan rho (v z.1 z.2)) := by
  classical
  let A (part : n.Partition) := Module.Free.ChooseBasisIndex K (YoungIdeal (K := K) part)
  let b (part : n.Partition) := Module.Free.chooseBasis K (YoungIdeal (K := K) part)
  let f (part : n.Partition) (i : I part) := intertwinerOfYoungImage rho part (v part i)
  have hgen (part : n.Partition) : LinearIndependent K
      (fun i : I part => f part i (spanSingletonGenerator (part.youngSymmetrizer K))) := by
    have hM : LinearIndependent K (fun i : I part => (v part i : M)) :=
      LinearIndependent.map' (R := K) (M := YoungImage rho part) (M' := M)
        (ι := I part) (v := v part) (hv part)
        (YoungImage rho part).subtype (Submodule.ker_subtype _)
    have he : (fun i : I part => f part i
        (spanSingletonGenerator (part.youngSymmetrizer K))) =
        (fun i : I part => (v part i : M)) := by
      funext i
      exact intertwinerOfYoungImage_generator rho part (v part i)
    exact Eq.mpr (congrArg (fun w : I part → M => LinearIndependent K w) he) hM
  have hf : LinearIndependent K
      (fun z : Σ part, A part × I part => f z.1 z.2.2 (b z.1 z.2.1)) :=
    independent_intertwiner_copies_all_shapes (K := K) (M := M) rho
      (A := A) (I := I) (fun part j => b part j) f
      (fun part => spanSingletonGenerator (part.youngSymmetrizer K))
      (fun part => (b part).linearIndependent) hgen
  let regroup : (Σ j : (Σ part, I part), A j.1) → (Σ part, A part × I part) :=
    fun z => ⟨z.1.1, z.2, z.1.2⟩
  have hregroup : Function.Injective regroup := by
    apply Function.LeftInverse.injective (g := fun z : Σ part, A part × I part =>
      (⟨⟨z.1, z.2.2⟩, z.2.1⟩ : Σ j : (Σ part, I part), A j.1))
    rintro ⟨⟨part, i⟩, a⟩
    rfl
  have hgroup : LinearIndependent K
      (fun z : Σ j : (Σ part, I part), A j.1 => f z.1.1 z.1.2 (b z.1.1 z.2)) :=
    LinearIndependent.comp (R := K) (M := M)
      (v := fun z : Σ part, A part × I part => f z.1 z.2.2 (b z.1 z.2.1))
      hf regroup hregroup
  have hs := linearIndependent_sigma_iSupIndep_span
    (fun (z : Σ part, I part) (a : A z.1) => f z.1 z.2 (b z.1 a)) hgroup
  convert hs using 1
  funext z
  rw [← range_intertwinerOfYoungImage]
  symm
  change Submodule.span K (Set.range ((f z.1 z.2).toLinearMap ∘ b z.1)) = _
  rw [Set.range_comp, ← Submodule.map_span, (b z.1).span_eq, Submodule.map_top]

end HigherSpecht
end
end CanonicalSource54

section CanonicalSource55
/- Source: HigherSpecht/PowerHarmonics.lean -/



/-!
# The actual finite ambient harmonic space

Annihilation by all coordinate powers is equivalent to the original
coefficientwise exponent bounds.  This supplies finite dimensionality for the
common-copy representation, without assuming a dimension theorem for a
Griffin quotient or its harmonic space.
-/

noncomputable section

open MvPolynomial Finset

namespace HigherSpecht

theorem dividedHarmonics_powerIdeal_eq_restrictDegree {R : Type*} [CommRing R]
    (n s : ℕ) (hs : 0 < s) :
    dividedHarmonics (powerIdeal R n s) = MvPolynomial.restrictDegree (Fin n) R (s - 1) := by
  apply Submodule.ext
  intro p
  constructor
  · intro hp
    apply (MvPolynomial.mem_restrictDegree (Fin n) p (s - 1)).mpr
    intro a ha i
    by_contra hn
    have hsi : s ≤ a i := by omega
    have hd : Finsupp.single i s ≤ a := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [Finsupp.single_eq_same] using hsi
      · simp only [Finsupp.single_eq_of_ne hji, Nat.zero_le]
    have hz := hp ((MvPolynomial.X i) ^ s) (Ideal.subset_span ⟨i, rfl⟩)
    rw [MvPolynomial.X_pow_eq_monomial, dividedAction_monomial, one_smul] at hz
    have hc := congrArg (fun q : PolynomialRing n R => q.coeff (a - Finsupp.single i s)) hz
    rw [coeff_contractMonomial, tsub_add_cancel_of_le hd, MvPolynomial.coeff_zero] at hc
    exact (MvPolynomial.mem_support_iff.mp ha) hc
  · intro hp
    apply (mem_dividedHarmonics_span_iff _ p).mpr
    rintro f ⟨i, rfl⟩
    change dividedAction ((MvPolynomial.X i) ^ s) p = 0
    rw [MvPolynomial.X_pow_eq_monomial, dividedAction_monomial, one_smul]
    apply MvPolynomial.ext
    intro r
    rw [coeff_contractMonomial, MvPolynomial.coeff_zero, Finsupp.zero_apply]
    by_contra hn
    have ha : r + Finsupp.single i s ∈ p.support := MvPolynomial.mem_support_iff.mpr hn
    have hbound := (MvPolynomial.mem_restrictDegree (Fin n) p (s - 1)).mp hp _ ha i
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hbound
    omega

theorem factorialNormalize_support {sigma K : Type*} [Fintype sigma] [DecidableEq sigma]
    [Field K] [CharZero K] (p : MvPolynomial sigma K) :
    (factorialNormalize p).support = p.support := by
  apply Finset.ext
  intro a
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff,
    coeff_factorialNormalize, div_ne_zero_iff]
  exact and_iff_left (exponentFactorial_ne_zero (K := K) a)

theorem factorialNormalize_mem_restrictDegree_iff {sigma K : Type*}
    [Fintype sigma] [DecidableEq sigma] [Field K] [CharZero K]
    (p : MvPolynomial sigma K) (d : ℕ) :
    factorialNormalize p ∈ MvPolynomial.restrictDegree sigma K d ↔
      p ∈ MvPolynomial.restrictDegree sigma K d := by
  rw [MvPolynomial.mem_restrictDegree, MvPolynomial.mem_restrictDegree, factorialNormalize_support]

theorem ordinaryHarmonics_powerIdeal_eq_restrictDegree (n s : ℕ) (hs : 0 < s) :
    ordinaryHarmonics (powerIdeal ℂ n s) = MvPolynomial.restrictDegree (Fin n) ℂ (s - 1) := by
  rw [ordinaryHarmonics_eq_factorialTransport, dividedHarmonics_powerIdeal_eq_restrictDegree n s hs]
  apply Submodule.ext
  intro p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (factorialNormalize_mem_restrictDegree_iff q (s - 1)).mpr hq
  · intro hp
    let q := (factorialTransport (σ := Fin n) (K := ℂ)).symm p
    have hq : factorialNormalize q = p :=
      (factorialTransport (σ := Fin n) (K := ℂ)).apply_symm_apply p
    exact ⟨q, (factorialNormalize_mem_restrictDegree_iff q (s - 1)).mp (hq.symm ▸ hp), hq⟩

theorem finiteDimensional_ordinaryPowerHarmonics (n s : ℕ) (hs : 0 < s) :
    FiniteDimensional ℂ (ordinaryHarmonics (powerIdeal ℂ n s)) := by
  rw [ordinaryHarmonics_powerIdeal_eq_restrictDegree n s hs]
  infer_instance

theorem finiteDimensional_ordinaryHarmonics_of_power_le {n s : ℕ}
    {I : Ideal (PolynomialRing n ℂ)} (hs : 0 < s) (hI : powerIdeal ℂ n s ≤ I) :
    FiniteDimensional ℂ (ordinaryHarmonics I) := by
  letI := finiteDimensional_ordinaryPowerHarmonics n s hs
  exact Module.Finite.of_injective (Submodule.inclusion (ordinaryHarmonics_antitone hI))
    (Submodule.inclusion_injective _)

theorem finiteDimensional_ordinaryGriffinHarmonics (n s : ℕ) (lam : YoungDiagram)
    (hs : 0 < s) : FiniteDimensional ℂ (ordinaryHarmonics (griffinIdeal ℂ n lam s)) :=
  finiteDimensional_ordinaryHarmonics_of_power_le hs le_sup_right

end HigherSpecht
end
end CanonicalSource55

section CanonicalSource56
/- Source: HigherSpecht/FiniteCommonSpechtCopies.lean -/



/-!
# The genuine finite common cyclic Specht copies

The multiplicity vectors are the exact maximal-prefix vectors defined for
Theorem 5.2.  Their ambient representation is the actual annihilator of the
empty-partition Griffin ideal.  The map from the ordinary Young ideal is
constructed from the actual Young-image vector, and its range is proved to be
the specified cyclic polynomial span.  Spanning the nonempty-partition
harmonic spaces is a separate remaining assertion.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau MvPolynomial Module
open scoped Classical

namespace HigherSpecht

theorem adjointYoungApply_smul {mu : YoungDiagram} (T : YoungTableau mu)
    (c : ℂ) (p : PolynomialRing mu.card ℂ) :
    adjointYoungApply T (c • p) = c • adjointYoungApply T p := by
  simp only [adjointYoungApply, rowSymmetrize, columnAlternate, map_sum, map_smul,
    Finset.smul_sum, smul_comm c]

def fixedFiniteToHarmonic {n s : ℕ} (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) : FiniteHarmonicIndex n s where
  part := part
  left := i.left
  multiplier := i.multiplier
  multiplier_length := by
    simpa [YoungDiagram.card_ofPartition, YoungDiagram.card] using i.multiplier_length
  descents_lt := i.descents_lt
  multiplier_width := i.multiplier_width

def finiteHarmonicToFixed {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    FixedFiniteHarmonicIndex (YoungDiagram.ofPartition i.part) s where
  left := i.left
  multiplier := i.multiplier
  eligible := prefixEligible_bot
    ⟨YoungDiagram.ofPartition i.part, rfl, i.left,
      StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)⟩
  descents_lt := i.descents_lt
  multiplier_length := by
    simpa [YoungDiagram.card_ofPartition, YoungDiagram.card] using i.multiplier_length
  multiplier_width := i.multiplier_width

def finiteHarmonicIndexEquiv (n s : ℕ) :
    FiniteHarmonicIndex n s ≃ Σ part : n.Partition,
      FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s where
  toFun i := ⟨i.part, finiteHarmonicToFixed i⟩
  invFun z := fixedFiniteToHarmonic z.1 z.2
  left_inv i := by cases i; rfl
  right_inv z := by rcases z with ⟨part, i⟩; cases i; rfl

theorem fixedCommonCut_toFinite {n s : ℕ} (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) :
    fixedCommonCut i = maximalFinitePrefix (fixedFiniteToHarmonic part i) := by
  simp only [fixedCommonCut, maximalFinitePrefix, fixedFiniteToHarmonic,
    YoungDiagram.card_ofPartition]

theorem finiteCommonHarmonicVector_toFixed {n s : ℕ} (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) :
    finiteCommonHarmonicVector (fixedFiniteToHarmonic part i) =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
        (fixedCommonHarmonicVector (StandardYoungTableau.rowSuperstandard _) i) := by
  simp only [finiteCommonHarmonicVector, fixedCommonHarmonicVector, fixedFiniteToHarmonic,
    normalizedOrdinaryDerivative, adjointYoungApply_smul, fixedCommonCut_toFinite] <;> rfl

theorem finiteHarmonicIndex_eligible_bot {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    i.toUnboundedHarmonicIndex.eligible ⊥ (by simp [YoungDiagram.card]) := by
  refine ⟨?_, ?_⟩
  · simpa [YoungDiagram.card] using i.multiplier_length
  · exact prefixEligible_bot
      ⟨YoungDiagram.ofPartition i.part, rfl, i.left,
        StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)⟩

def finiteCommonAmbient (n s : ℕ) : Subrepresentation (polynomialRepresentation ℂ n) :=
  ordinaryHarmonicRepresentation (griffinIdeal ℂ n ⊥ s) (permutationStable_griffinIdeal ⊥ s)

theorem finiteCommonAmbient_finiteDimensional (n s : ℕ) (hs : 0 < s) :
    FiniteDimensional ℂ (finiteCommonAmbient n s).toSubmodule :=
  finiteDimensional_ordinaryGriffinHarmonics n s ⊥ hs

def subrepresentationInclusion {K G M : Type*} [CommSemiring K] [Monoid G]
    [AddCommMonoid M] [Module K M] {rho : Representation K G M} (V : Subrepresentation rho) :
    V.toRepresentation.IntertwiningMap rho where
  toLinearMap := V.toSubmodule.subtype
  isIntertwining' g := by ext v; rfl

theorem polynomial_asAlgebraHom_domCongr_rename {n m : ℕ} (e : Fin n ≃ Fin m)
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (p : PolynomialRing n ℂ) :
    (polynomialRepresentation ℂ m).asAlgebraHom
      (MonoidAlgebra.domCongr ℂ ℂ e.permCongrHom a) (MvPolynomial.rename e p) =
        MvPolynomial.rename e ((polynomialRepresentation ℂ n).asAlgebraHom a p) := by
  apply MonoidAlgebra.induction_on a
  · intro g
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single,
      Representation.asAlgebraHom_single, one_smul, polynomialRepresentation_apply,
      MvPolynomial.rename_rename]
    apply congrArg (fun f : Fin n → Fin m => MvPolynomial.rename (R := ℂ) f p)
    funext i
    simp only [Function.comp_apply, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, ha, hb]
  · intro c a ha
    simp only [map_smul, LinearMap.smul_apply, ha]

def finiteCommonPreVector {n s : ℕ} (i : FiniteHarmonicIndex n s) : PolynomialRing n ℂ :=
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)).toTableau
  let r := griffinWitnessRejection i.left T i.multiplier (maximalFinitePrefix i)
    (maximalFinitePrefix_le i) s
  let G := griffinApolarWitness i.left T (maximalFinitePrefix i) (maximalFinitePrefix_le i) s
  MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (normalizedOrdinaryDerivative r G)

theorem finiteCommonPreVector_mem {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    finiteCommonPreVector i ∈ (finiteCommonAmbient n s).toSubmodule := by
  apply ordinaryHarmonics_rename_finCongr (YoungDiagram.card_ofPartition i.part) ⊥ s
  apply (ordinaryHarmonics _).smul_mem
  exact ordinaryAction_mem_harmonics
    (finiteCommonApolarWitness_mem_ordinaryHarmonics i hs ⊥
      (by simp [YoungDiagram.card]) (by simp) (finiteHarmonicIndex_eligible_bot i)) _

theorem finiteCommonHarmonicVector_mem_ambient {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (hs : 0 < s) : finiteCommonHarmonicVector i ∈ (finiteCommonAmbient n s).toSubmodule :=
  finiteCommonHarmonicVector_mem i hs ⊥ (by simp [YoungDiagram.card]) (by simp)
    (finiteHarmonicIndex_eligible_bot i)

theorem finiteCommonHarmonicVector_youngImage {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    (polynomialRepresentation ℂ n).asAlgebraHom (i.part.youngSymmetrizer ℂ)
      (finiteCommonPreVector i) = finiteCommonHarmonicVector i := by
  rw [Nat.Partition.youngSymmetrizer_def]
  simp only [finiteCommonPreVector, polynomial_asAlgebraHom_domCongr_rename,
    asAlgebraHom_youngSymmetrizer_adjoint, normalizedOrdinaryDerivative,
    adjointYoungApply_smul, finiteCommonHarmonicVector]

def finiteCommonYoungImage {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    YoungImage (finiteCommonAmbient n s).toRepresentation i.part :=
  ⟨⟨finiteCommonHarmonicVector i, finiteCommonHarmonicVector_mem_ambient i hs⟩,
    ⟨⟨finiteCommonPreVector i, finiteCommonPreVector_mem i hs⟩, by
      apply Subtype.ext
      exact ((subrepresentationInclusion (finiteCommonAmbient n s)).apply_asAlgebraHom
        (i.part.youngSymmetrizer ℂ) ⟨finiteCommonPreVector i, finiteCommonPreVector_mem i hs⟩).trans
        (finiteCommonHarmonicVector_youngImage i)⟩⟩

theorem finiteCommonYoungImage_linearIndependent {n s : ℕ} (part : n.Partition) (hs : 0 < s) :
    LinearIndependent (M := YoungImage (finiteCommonAmbient n s).toRepresentation part) ℂ
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
      (finiteCommonYoungImage (fixedFiniteToHarmonic part i) hs :
        YoungImage (finiteCommonAmbient n s).toRepresentation part)) := by
  let e := finCongr (YoungDiagram.card_ofPartition part)
  have h : LinearIndependent ℂ
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
        MvPolynomial.rename e
          (fixedCommonHarmonicVector
            (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)) i)) := by
    simpa only [Function.comp_def, AlgHom.coe_toLinearMap, AlgHom.toLinearMap_apply] using
      (fixedCommonHarmonicVector_linearIndependent (s := s)
        (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part))).map'
          (MvPolynomial.rename e).toLinearMap
            (LinearMap.ker_eq_bot.mpr (MvPolynomial.rename_injective e e.injective))
  apply LinearIndependent.of_comp ((finiteCommonAmbient n s).toSubmodule.subtype.comp
    (YoungImage (finiteCommonAmbient n s).toRepresentation part).subtype)
  change LinearIndependent ℂ
    (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
      finiteCommonHarmonicVector (fixedFiniteToHarmonic part i))
  have hfamily :
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
        finiteCommonHarmonicVector (fixedFiniteToHarmonic part i)) =
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
        MvPolynomial.rename e
          (fixedCommonHarmonicVector
            (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)) i)) := by
    funext i
    exact finiteCommonHarmonicVector_toFixed part i
  rw [hfamily]
  exact h

theorem finiteCommonYoungImage_ne_zero {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    finiteCommonYoungImage i hs ≠ 0 := by
  have h := (finiteCommonYoungImage_linearIndependent i.part hs).ne_zero (finiteHarmonicToFixed i)
  cases i
  exact h

theorem finiteCommonHarmonicCopy_eq_map_cyclic {n s : ℕ}
    (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    finiteCommonHarmonicCopy i =
      (cyclicRepresentationSpan (finiteCommonAmbient n s).toRepresentation
        (finiteCommonYoungImage i hs)).map (finiteCommonAmbient n s).toSubmodule.subtype := by
  rw [cyclicRepresentationSpan, Submodule.map_span, ← Set.range_comp]
  rfl

/-- Each exact manuscript vector generates a full ordinary Specht copy. -/
theorem finiteCommonHarmonicCopy_isSpecht {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    IsSpechtPolynomialCopy i.part (finiteCommonHarmonicCopy i) := by
  letI := finiteCommonAmbient_finiteDimensional n s hs
  let f := intertwinerOfYoungImage (finiteCommonAmbient n s).toRepresentation i.part
    (finiteCommonYoungImage i hs)
  let e := subrepresentationInclusion (finiteCommonAmbient n s)
  refine ⟨e.comp f, Subtype.val_injective.comp
    (intertwinerOfYoungImage_injective _ _ _ (finiteCommonYoungImage_ne_zero i hs)), ?_⟩
  rw [finiteCommonHarmonicCopy_eq_map_cyclic i hs, ← range_intertwinerOfYoungImage]
  exact LinearMap.range_comp f.toLinearMap e.toLinearMap

/-- The literal cyclic copies are independent simultaneously across all
standard tableaux, boosts, and shapes, without a dimension-count premise. -/
theorem finiteCommonHarmonicCopies_iSupIndep {n s : ℕ} (hs : 0 < s) :
    iSupIndep (finiteCommonHarmonicCopy (n := n) (s := s)) := by
  letI := finiteCommonAmbient_finiteDimensional n s hs
  have h := intertwinerOfYoungImage_copies_iSupIndep
    (finiteCommonAmbient n s).toRepresentation
    (fun part (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) =>
      (finiteCommonYoungImage (fixedFiniteToHarmonic part i) hs :
        YoungImage (finiteCommonAmbient n s).toRepresentation part))
    (fun part => finiteCommonYoungImage_linearIndependent part hs)
  have hm := LinearMap.iSupIndep_map (finiteCommonAmbient n s).toSubmodule.subtype
    Subtype.val_injective h
  have hc := hm.comp (finiteHarmonicIndexEquiv n s).injective
  convert hc using 1
  funext i
  change finiteCommonHarmonicCopy i =
    (cyclicRepresentationSpan (finiteCommonAmbient n s).toRepresentation
      (finiteCommonYoungImage
        (fixedFiniteToHarmonic (finiteHarmonicIndexEquiv n s i).1
          (finiteHarmonicIndexEquiv n s i).2) hs)).map
            (finiteCommonAmbient n s).toSubmodule.subtype
  rw [← finiteCommonHarmonicCopy_eq_map_cyclic]
  congr 1

end HigherSpecht
end
end CanonicalSource56

section CanonicalSource57
/- Source: HigherSpecht/CommonHarmonicDegrees.lean -/



/-!
# The actual degrees of the common harmonic copies

The degree is computed from the real support of the witness and the genuine
ordinary differential operator.  The rejection-vector identity is supplied by
the rearrangement construction; no external grading label is attached to a
polynomial independently of its coefficients.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

theorem degree_permutedExponent {n : ℕ} (a : Fin n →₀ ℕ) (e : Equiv.Perm (Fin n)) :
    (permutedExponent a e).degree = a.degree := by
  simp only [Finsupp.degree_eq_sum, permutedExponent_apply]
  exact Equiv.sum_comp e a

theorem coefficientWitness_isHomogeneous {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n →₀ ℕ) :
    (coefficientWitness (R := ℂ) G a).IsHomogeneous a.degree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  exact MvPolynomial.isHomogeneous_monomial _ (degree_permutedExponent a e.val)

theorem ordinaryAction_monomial_isHomogeneous {n d : ℕ} (r : Fin n →₀ ℕ)
    {p : PolynomialRing n ℂ} (hp : p.IsHomogeneous (d + r.degree)) :
    (ordinaryAction (MvPolynomial.monomial r (1 : ℂ)) p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a + r) ≠ 0 := by
    intro hz
    rw [ordinaryAction_monomial_coeff, hz, zero_mul, zero_div] at ha
    exact ha rfl
  have hdeg : (a + r).degree = d + r.degree := by
    by_contra h
    exact hcoeff (hp.coeff_eq_zero h)
  rw [map_add] at hdeg
  have ha' : a.degree = d := Nat.add_right_cancel hdeg
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using ha'

theorem normalizedOrdinaryDerivative_isHomogeneous {n d : ℕ}
    (r : Fin n →₀ ℕ) {p : PolynomialRing n ℂ} (hp : p.IsHomogeneous (d + r.degree)) :
    (normalizedOrdinaryDerivative r p).IsHomogeneous d :=
  (MvPolynomial.homogeneousSubmodule (Fin n) ℂ d).smul_mem _
    (ordinaryAction_monomial_isHomogeneous r hp)

theorem adjointYoungApply_isHomogeneous {mu : YoungDiagram} (T : YoungTableau mu)
    {p : PolynomialRing mu.card ℂ} {d : ℕ} (hp : p.IsHomogeneous d) :
    (adjointYoungApply T p).IsHomogeneous d :=
  rowSymmetrize_isHomogeneous _ (columnAlternate_isHomogeneous _ hp)

theorem degree_transportedBoosted {mu : YoungDiagram} (S T : StandardYoungTableau mu)
    (eta : YoungDiagram) (heta : eta.colLen 0 ≤ mu.card) :
    (transportedBoosted S T.toTableau eta).degree = cochargeDegree S + eta.card := by
  have hp : (higherSpechtPolynomial (R := ℂ) S T *
      elementaryMultiplier mu.card mu.card eta.rowLen).IsHomogeneous
        (cochargeDegree S + eta.card) :=
    (higherSpechtPolynomial_isHomogeneous S T).mul
      (elementaryMultiplier_isHomogeneous mu.card mu.card eta heta)
  have hc : (higherSpechtPolynomial (R := ℂ) S T *
      elementaryMultiplier mu.card mu.card eta.rowLen).coeff
        (transportedBoosted S T.toTableau eta) ≠ 0 := by
    rw [lemma_4_2_distinguishedCoefficient S T le_rfl eta heta]
    exact_mod_cast (Finset.card_pos.mpr
      (rowFillingStabilizers_nonempty T.toTableau (transportedCocharge S T.toTableau))).ne'
  by_contra hd
  exact hc (hp.coeff_eq_zero hd)

theorem fixedCommonHarmonicVector_isHomogeneous {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    (fixedCommonHarmonicVector T i).IsHomogeneous
      (cochargeDegree i.left + i.multiplier.card) := by
  let a := griffinWitnessAlpha i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i) s
  let r := griffinWitnessRejection i.left T.toTableau i.multiplier
    (fixedCommonCut i) (fixedCommonCut_le i) s
  let b := transportedBoosted i.left T.toTableau i.multiplier
  have hgeom := griffinWitness_rearrangement i.left T.toTableau i.multiplier
    (fixedCommonCut i) (fixedCommonCut_le i) s
    (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width
  have harb : a = r + b := by
    ext j
    have h := hgeom.subtraction j
    change (b j : ℤ) = (a j : ℤ) - (r j : ℤ) at h
    simp only [Finsupp.add_apply]
    omega
  have hlen : i.multiplier.colLen 0 ≤ mu.card := by
    simpa [YoungDiagram.card] using i.multiplier_length
  have had : a.degree = cochargeDegree i.left + i.multiplier.card + r.degree := by
    rw [harb, map_add, show b.degree = cochargeDegree i.left + i.multiplier.card from
      degree_transportedBoosted i.left T i.multiplier hlen]
    exact Nat.add_comm _ _
  apply adjointYoungApply_isHomogeneous
  apply normalizedOrdinaryDerivative_isHomogeneous
  rw [griffinApolarWitness_eq_coefficientWitness, ← had]
  exact coefficientWitness_isHomogeneous _ _

theorem finiteCommonHarmonicVector_isHomogeneous {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    (finiteCommonHarmonicVector i).IsHomogeneous i.toUnboundedHarmonicIndex.degree := by
  have h := (fixedCommonHarmonicVector_isHomogeneous
    (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part))
    (finiteHarmonicToFixed i)).rename_isHomogeneous
      (f := finCongr (YoungDiagram.card_ofPartition i.part))
  rw [← finiteCommonHarmonicVector_toFixed] at h
  have hi : fixedFiniteToHarmonic i.part (finiteHarmonicToFixed i) = i :=
    (finiteHarmonicIndexEquiv n s).left_inv i
  rw [hi] at h
  simpa only [finiteHarmonicToFixed, UnboundedHarmonicIndex.degree] using h

theorem cyclicPolynomialCopy_le_homogeneous {n d : ℕ} {p : PolynomialRing n ℂ}
    (hp : p.IsHomogeneous d) :
    cyclicPolynomialCopy p ≤ MvPolynomial.homogeneousSubmodule (Fin n) ℂ d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, rfl⟩
  exact hp.rename_isHomogeneous

/-- The full cyclic span has the precise cocharge-plus-partition degree. -/
theorem finiteCommonHarmonicCopy_le_homogeneous {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    finiteCommonHarmonicCopy i ≤
      MvPolynomial.homogeneousSubmodule (Fin n) ℂ i.toUnboundedHarmonicIndex.degree :=
  cyclicPolynomialCopy_le_homogeneous (finiteCommonHarmonicVector_isHomogeneous i)

end HigherSpecht
end
end CanonicalSource57

section CanonicalSource58
/- Source: HigherSpecht/OrdinaryHarmonicDuality.lean -/



/-!
# Exact quotient duality for ordinary harmonic polynomials

The inverse map is a finite sum of actual factorial-normalized monomials.
Coordinate-power relations bound its support.  Thus this proves the genuine
duality, including surjectivity, without assuming a dimension theorem or
replacing the annihilator by an abstract vector space of the desired size.
-/

noncomputable section

open MvPolynomial Finset Module
open scoped Classical

namespace HigherSpecht

theorem ordinaryApolar_monomial {n : ℕ} (p : PolynomialRing n ℂ) (a : Fin n →₀ ℕ) :
    ordinaryApolarFunctional p (MvPolynomial.monomial a 1) =
      p.coeff a * (exponentFactorial a : ℂ) := by
  rw [ordinaryApolarFunctional_apply, ordinaryAction_monomial_coeff]
  simp [exponentFactorial]

theorem ordinaryApolarRepresenter_injective (n : ℕ) :
    Function.Injective (ordinaryApolarRepresenter n) := by
  intro p q hpq
  ext a
  have h := DFunLike.congr_fun hpq (MvPolynomial.monomial a 1)
  change ordinaryApolarFunctional p (MvPolynomial.monomial a 1) =
    ordinaryApolarFunctional q (MvPolynomial.monomial a 1) at h
  rw [ordinaryApolar_monomial, ordinaryApolar_monomial] at h
  exact (mul_right_cancel₀ (exponentFactorial_ne_zero a)) h

theorem mem_ordinaryHarmonics_iff_apolar {n : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (p : PolynomialRing n ℂ) :
    p ∈ ordinaryHarmonics I ↔ ∀ f ∈ I, ordinaryApolarFunctional p f = 0 := by
  constructor
  · intro hp f hf
    rw [ordinaryApolarFunctional_apply, hp f hf, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  · intro hp f hf
    apply MvPolynomial.ext
    intro a
    have h := hp (MvPolynomial.monomial a 1 * f) (I.mul_mem_left _ hf)
    rw [ordinaryApolarFunctional_apply, ordinaryAction_mul_apply] at h
    change ordinaryApolarFunctional (ordinaryAction f p) (MvPolynomial.monomial a 1) = 0 at h
    rw [ordinaryApolar_monomial] at h
    exact (mul_eq_zero.mp h).resolve_right (exponentFactorial_ne_zero a)

def ordinaryHarmonicQuotientDual {n : ℕ} (I : Ideal (PolynomialRing n ℂ)) :
    ordinaryHarmonics I →ₗ[ℂ] Module.Dual ℂ (PolynomialRing n ℂ ⧸ I) where
  toFun p := (I.restrictScalars ℂ).liftQ (ordinaryApolarFunctional p.val)
    (fun f hf => (mem_ordinaryHarmonics_iff_apolar I p.val).mp p.property f hf)
  map_add' p q := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro f
    change ordinaryApolarFunctional (p.val + q.val) f =
      ordinaryApolarFunctional p.val f + ordinaryApolarFunctional q.val f
    simp only [ordinaryApolarFunctional_apply, map_add, MvPolynomial.coeff_add]
  map_smul' c p := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro f
    change ordinaryApolarFunctional (c • p.val) f = c • ordinaryApolarFunctional p.val f
    simp only [ordinaryApolarFunctional_apply, map_smul, MvPolynomial.coeff_smul]

@[simp] theorem ordinaryHarmonicQuotientDual_mk {n : ℕ}
    (I : Ideal (PolynomialRing n ℂ)) (p : ordinaryHarmonics I) (f : PolynomialRing n ℂ) :
    ordinaryHarmonicQuotientDual I p (Ideal.Quotient.mk I f) = ordinaryApolarFunctional p.val f := rfl

theorem ordinaryHarmonicQuotientDual_injective {n : ℕ} (I : Ideal (PolynomialRing n ℂ)) :
    Function.Injective (ordinaryHarmonicQuotientDual I) := by
  intro p q hpq
  apply Subtype.ext
  apply ordinaryApolarRepresenter_injective n
  apply LinearMap.ext
  intro f
  exact DFunLike.congr_fun hpq (Ideal.Quotient.mk I f)

abbrev BoxExponent (n s : ℕ) := {a : Fin n →₀ ℕ // ∀ i, a i < s}

instance finiteBoxExponent (n s : ℕ) : Finite (BoxExponent n s) := by
  apply Finite.of_injective (fun a : BoxExponent n s => fun i => (⟨a.val i, a.property i⟩ : Fin s))
  intro a b h
  apply Subtype.ext
  ext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance fintypeBoxExponent (n s : ℕ) : Fintype (BoxExponent n s) := Fintype.ofFinite _

def boundedApolarRepresentative {n : ℕ} (s : ℕ) (L : Module.Dual ℂ (PolynomialRing n ℂ)) :
    PolynomialRing n ℂ :=
  ∑ a : BoxExponent n s,
    MvPolynomial.monomial a.val (L (MvPolynomial.monomial a.val 1) / exponentFactorial a.val)

theorem boundedApolarRepresentative_coeff {n : ℕ} (s : ℕ)
    (L : Module.Dual ℂ (PolynomialRing n ℂ)) (a : Fin n →₀ ℕ) :
    (boundedApolarRepresentative s L).coeff a =
      if ∀ i, a i < s then L (MvPolynomial.monomial a 1) / exponentFactorial a else 0 := by
  rw [boundedApolarRepresentative, MvPolynomial.coeff_sum]
  split_ifs with ha
  · rw [Finset.sum_eq_single (⟨a, ha⟩ : BoxExponent n s)]
    · simp
    · intro b hb hba
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hba (Subtype.ext h)
    · simp
  · apply Finset.sum_eq_zero
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro h
    exact ha (h ▸ b.property)

theorem monomial_mem_of_large_coordinate {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) (a : Fin n →₀ ℕ) (i : Fin n) (hi : s ≤ a i) :
    MvPolynomial.monomial a (1 : ℂ) ∈ I := by
  have hle : Finsupp.single i s ≤ a := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using hi
    · simp only [Finsupp.single_eq_of_ne hji, Nat.zero_le]
  have hx : (MvPolynomial.X i : PolynomialRing n ℂ) ^ s ∈ I :=
    hpower (Ideal.subset_span ⟨i, rfl⟩)
  have h := I.mul_mem_left (MvPolynomial.monomial (a - Finsupp.single i s) 1) hx
  simpa only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    one_mul, tsub_add_cancel_of_le hle] using h

theorem boundedApolarRepresentative_pairing {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) (L : Module.Dual ℂ (PolynomialRing n ℂ))
    (hL : ∀ f ∈ I, L f = 0) (f : PolynomialRing n ℂ) :
    ordinaryApolarFunctional (boundedApolarRepresentative s L) f = L f := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | monomial a c =>
    have hm : (MvPolynomial.monomial a c : PolynomialRing n ℂ) = c • MvPolynomial.monomial a 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, map_smul, ordinaryApolar_monomial, boundedApolarRepresentative_coeff]
    congr 1
    split_ifs with ha
    · exact div_mul_cancel₀ _ (exponentFactorial_ne_zero a)
    · obtain ⟨i, hi⟩ := not_forall.mp ha
      rw [hL _ (monomial_mem_of_large_coordinate I hpower a i (le_of_not_gt hi)), zero_mul]

theorem ordinaryHarmonicQuotientDual_surjective {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) :
    Function.Surjective (ordinaryHarmonicQuotientDual I) := by
  intro L
  let Lp := L.comp (Ideal.Quotient.mkₐ ℂ I).toLinearMap
  have hLp : ∀ f ∈ I, Lp f = 0 := by
    intro f hf
    change L (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  let p := boundedApolarRepresentative s Lp
  have hp : p ∈ ordinaryHarmonics I := by
    apply (mem_ordinaryHarmonics_iff_apolar I p).mpr
    intro f hf
    rw [boundedApolarRepresentative_pairing I hpower Lp hLp, hLp f hf]
  refine ⟨⟨p, hp⟩, ?_⟩
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro f
  exact boundedApolarRepresentative_pairing I hpower Lp hLp f

/-- Genuine ordinary-apolar duality for every ideal containing the displayed
coordinate powers.  The bound is used only to make the explicit inverse finite. -/
def ordinaryHarmonicQuotientDualEquiv {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) :
    ordinaryHarmonics I ≃ₗ[ℂ] Module.Dual ℂ (PolynomialRing n ℂ ⧸ I) :=
  LinearEquiv.ofBijective (ordinaryHarmonicQuotientDual I)
    ⟨ordinaryHarmonicQuotientDual_injective I, ordinaryHarmonicQuotientDual_surjective I hpower⟩

theorem finrank_ordinaryGriffinHarmonics (n s : ℕ) (lam : YoungDiagram) :
    Module.finrank ℂ (ordinaryHarmonics (griffinIdeal ℂ n lam s)) =
      Module.finrank ℂ (GriffinRing ℂ n lam s) := by
  rw [(ordinaryHarmonicQuotientDualEquiv (griffinIdeal ℂ n lam s) le_sup_right).finrank_eq,
    Subspace.dual_finrank_eq]

end HigherSpecht
end
end CanonicalSource58

section CanonicalSource59
/- Source: HigherSpecht/CommonHarmonicAssembly.lean -/



/-!
# Exact assembly and the remaining nonempty counting obligation

The dimension of the actual eligible sum is proved to equal the cardinality
of the manuscript's full Griffin index, including all right tableaux.
Consequently a genuine specified quotient basis gives the full harmonic
equality.  That transfer is deliberately named `of_specifiedBasis`: the
nonempty count is not asserted by it.  The empty-partition equality below
instantiates the transfer with the actual bounded-word basis.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module
open scoped Classical

namespace HigherSpecht

instance finiteFiniteHarmonicIndex (n s : ℕ) : Finite (FiniteHarmonicIndex n s) :=
  Finite.of_injective (finiteHarmonicIndexEquiv n s) (finiteHarmonicIndexEquiv n s).injective

noncomputable instance fintypeFiniteHarmonicIndex (n s : ℕ) : Fintype (FiniteHarmonicIndex n s) :=
  Fintype.ofFinite _

abbrev EligibleFiniteHarmonicIndex (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :=
  {i : FiniteHarmonicIndex n s // i.toUnboundedHarmonicIndex.eligible lam hk}

abbrev EligibleHarmonicTableauIndex (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :=
  Σ i : EligibleFiniteHarmonicIndex n s lam hk,
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def eligibleHarmonicTableauPartitionEquiv (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    EligibleHarmonicTableauIndex n s lam hk ≃ PartitionGriffinVectorIndex n lam hk s where
  toFun z :=
    ⟨z.1.val.part, z.2,
      { left := z.1.val.left
        multiplier := z.1.val.multiplier
        eligible := z.1.property.2
        descents_lt := z.1.val.descents_lt
        multiplier_length := by
          simpa only [YoungDiagram.card_ofPartition] using z.1.property.1
        multiplier_width := z.1.val.multiplier_width }⟩
  invFun z := by
    let i : FiniteHarmonicIndex n s :=
      { part := z.1
        left := z.2.2.left
        multiplier := z.2.2.multiplier
        multiplier_length := by
          have h := z.2.2.multiplier_length.trans (Nat.sub_le _ _)
          simpa only [YoungDiagram.card_ofPartition] using h
        descents_lt := z.2.2.descents_lt
        multiplier_width := z.2.2.multiplier_width }
    exact ⟨⟨i,
      ⟨by simpa only [YoungDiagram.card_ofPartition] using z.2.2.multiplier_length,
        z.2.2.eligible⟩⟩, z.2.1⟩
  left_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; cases i; rfl
  right_inv z := by rcases z with ⟨part, T, i⟩; cases i; rfl

def eligibleHarmonicTableauEquiv (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    EligibleHarmonicTableauIndex n s lam hk ≃ GriffinIndex n lam hk s :=
  (eligibleHarmonicTableauPartitionEquiv n s lam hk).trans
    (partitionGriffinIndexEquiv n lam hk s)

theorem sum_standardCount_eligible_eq_card_griffin (n s : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    (∑ i : EligibleFiniteHarmonicIndex n s lam hk,
      standardCount (YoungDiagram.ofPartition i.val.part)) = Nat.card (GriffinIndex n lam hk s) := by
  rw [← Nat.card_congr (eligibleHarmonicTableauEquiv n s lam hk),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [standardCount_def]

theorem finrank_finiteCommonHarmonicCopy {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    Module.finrank ℂ (finiteCommonHarmonicCopy i) =
      standardCount (YoungDiagram.ofPartition i.part) := by
  obtain ⟨f, hf, hr⟩ := finiteCommonHarmonicCopy_isSpecht i hs
  rw [← hr, LinearMap.finrank_range_of_inj hf,
    Nat.Partition.finrank_span_youngSymmetrizer, TauCeti.finrank_spechtModule]

theorem finite_finiteCommonHarmonicCopy {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    Module.Finite ℂ (finiteCommonHarmonicCopy i) := by
  letI : Module.Finite ℂ (ordinaryHarmonics (griffinIdeal ℂ n ⊥ s)) :=
    finiteDimensional_ordinaryGriffinHarmonics n s ⊥ hs
  exact Module.Finite.of_injective
    (Submodule.inclusion (finiteCommonHarmonicCopy_le i hs ⊥
      (by simp [YoungDiagram.card]) (by simp) (finiteHarmonicIndex_eligible_bot i)))
    (Submodule.inclusion_injective _)

theorem finrank_iSup_of_independent {I : Type*} [Fintype I]
    {M : Type*} [AddCommGroup M] [Module ℂ M] (p : I → Submodule ℂ M)
    [∀ i, Module.Finite ℂ (p i)] (hp : iSupIndep p) :
    Module.finrank ℂ ↥(⨆ i, p i) = ∑ i, Module.finrank ℂ (p i) := by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj hp.dfinsupp_lsum_injective]
  change Module.finrank ℂ (DirectSum I (fun i => p i)) = _
  exact Module.finrank_directSum (R := ℂ) (fun i : I => p i)

def eligibleCommonHarmonicSum (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Submodule ℂ (PolynomialRing n ℂ) :=
  ⨆ i : EligibleFiniteHarmonicIndex n s lam hk, finiteCommonHarmonicCopy i.val

theorem eligibleCommonHarmonicSum_le (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    eligibleCommonHarmonicSum n s lam hk ≤ ordinaryHarmonics (griffinIdeal ℂ n lam s) := by
  apply iSup_le
  intro i
  exact finiteCommonHarmonicCopy_le i.val hs lam hk hheight i.property

theorem finrank_eligibleCommonHarmonicSum (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hs : 0 < s) :
    Module.finrank ℂ (eligibleCommonHarmonicSum n s lam hk) = Nat.card (GriffinIndex n lam hk s) := by
  letI : ∀ i : EligibleFiniteHarmonicIndex n s lam hk,
      Module.Finite ℂ (finiteCommonHarmonicCopy i.val) :=
    fun i => finite_finiteCommonHarmonicCopy i.val hs
  have hi := (finiteCommonHarmonicCopies_iSupIndep hs).comp
    (show Function.Injective (fun i : EligibleFiniteHarmonicIndex n s lam hk => i.val) from
      Subtype.val_injective)
  change iSupIndep (fun i : EligibleFiniteHarmonicIndex n s lam hk =>
    finiteCommonHarmonicCopy i.val) at hi
  rw [eligibleCommonHarmonicSum, finrank_iSup_of_independent _ hi]
  simp_rw [finrank_finiteCommonHarmonicCopy _ hs]
  exact sum_standardCount_eligible_eq_card_griffin n s lam hk

/-- Auxiliary assembly only: its displayed basis input is the genuine
remaining nonempty-partition spanning obligation. -/
theorem finiteCommonHarmonic_decomposition_of_specifiedBasis
    (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hb : IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    ordinaryHarmonics (griffinIdeal ℂ n lam s) = eligibleCommonHarmonicSum n s lam hk := by
  letI := finiteDimensional_ordinaryGriffinHarmonics n s lam hs
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (eligibleCommonHarmonicSum_le n s lam hk hs hheight)
  rw [finrank_eligibleCommonHarmonicSum n s lam hk hs, finrank_ordinaryGriffinHarmonics]
  obtain ⟨b, hb⟩ := hb
  rw [Module.finrank_eq_card_basis b, Nat.card_eq_fintype_card]

/-- The empty-partition case uses the actual bounded-word basis.  No count or
basis hypothesis remains here; it is still a specified special case of 5.2. -/
theorem finiteCommonHarmonic_decomposition_empty (n s : ℕ) (hs : 0 < s) :
    ordinaryHarmonics (griffinIdeal ℂ n ⊥ s) =
      eligibleCommonHarmonicSum n s ⊥ (by simp [YoungDiagram.card]) :=
  finiteCommonHarmonic_decomposition_of_specifiedBasis n s ⊥
    (by simp [YoungDiagram.card]) hs (by simp) (griffin_empty_specifiedBasis ℂ n s hs)

/-- All structural and membership assertions, with the still-unproved general
spanning equality deliberately absent from this auxiliary conjunction. -/
theorem finiteCommonHarmonic_structure (n s : ℕ) (hs : 0 < s) :
    (∀ i : FiniteHarmonicIndex n s,
      IsSpechtPolynomialCopy i.part (finiteCommonHarmonicCopy i) ∧
      finiteCommonHarmonicCopy i ≤ MvPolynomial.homogeneousSubmodule (Fin n) ℂ
        i.toUnboundedHarmonicIndex.degree) ∧
    iSupIndep (finiteCommonHarmonicCopy (n := n) (s := s)) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
      eligibleCommonHarmonicSum n s lam hk ≤ ordinaryHarmonics (griffinIdeal ℂ n lam s) :=
  ⟨fun i => ⟨finiteCommonHarmonicCopy_isSpecht i hs, finiteCommonHarmonicCopy_le_homogeneous i⟩,
    finiteCommonHarmonicCopies_iSupIndep hs,
    fun lam hk hheight => eligibleCommonHarmonicSum_le n s lam hk hs hheight⟩

end HigherSpecht
end
end CanonicalSource59

section CanonicalSource60
/- Source: HigherSpecht/CommonCopyStabilization.lean -/



/-!
# Stabilization of the manuscript's named common harmonic copies

Once the finite power bound contains the entire insertion diagram, its
maximal prefix is exactly the untruncated maximal prefix.  The two literal
vectors differ by the explicit nonzero factorial scalar already proved for
the exterior powers.  Thus their genuine cyclic polynomial submodules are
equal.  This also establishes all structural assertions of the untruncated
family without using a nonempty-partition spanning theorem.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

theorem columnInsertion_height_le_card {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (columnInsertion S).state.shape.colLen 0 ≤ mu.card := by
  exact (colLen_zero_le_card _).trans_eq (columnInsertion S).shape_card

theorem maximalFinitePrefix_eq_untruncated {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (hheight : (columnInsertion i.left).state.shape.colLen 0 ≤ s) :
    maximalFinitePrefix i = maximalUntruncatedPrefix i.toUnboundedHarmonicIndex := by
  rw [maximalFinitePrefix, ← YoungDiagram.card_eq_sum_range_rowLen _ hheight,
    (columnInsertion i.left).shape_card, YoungDiagram.card_ofPartition]
  exact min_eq_left (Nat.sub_le _ _)

theorem finiteCommonHarmonicVector_eq_normalized {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    finiteCommonHarmonicVector i =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
        (adjointYoungApply (StandardYoungTableau.rowSuperstandard _).toTableau
          (normalizedOrdinaryDerivative
            (griffinWitnessRejection i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              i.multiplier (maximalFinitePrefix i) (maximalFinitePrefix_le i) s)
            (griffinApolarWitness i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              (maximalFinitePrefix i) (maximalFinitePrefix_le i) s))) := by
  simp only [finiteCommonHarmonicVector, normalizedOrdinaryDerivative, adjointYoungApply_smul]

theorem untruncatedCommonHarmonicVector_eq_normalized {n : ℕ} (i : UnboundedHarmonicIndex n) :
    untruncatedCommonHarmonicVector i =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
        (adjointYoungApply (StandardYoungTableau.rowSuperstandard _).toTableau
          (normalizedOrdinaryDerivative
            (untruncatedWitnessRejection i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              i.multiplier (maximalUntruncatedPrefix i) (maximalUntruncatedPrefix_le i))
            (untruncatedApolarWitness i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              i.multiplier (maximalUntruncatedPrefix i) (maximalUntruncatedPrefix_le i)))) := by
  simp only [untruncatedCommonHarmonicVector, untruncatedCommonData,
    normalizedOrdinaryDerivative, adjointYoungApply_smul, untruncatedApolarWitness_eq,
    untruncatedWitnessRejection, untruncatedWitnessAlpha, exteriorPart]

def commonWitnessComparisonScalar {n s : ℕ} (i : FiniteHarmonicIndex n s) : ℂ :=
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)).toTableau
  let k := maximalUntruncatedPrefix i.toUnboundedHarmonicIndex
  let hk := maximalUntruncatedPrefix_le i.toUnboundedHarmonicIndex
  outsideWitnessComparisonScalar (griffinWitnessAlpha i.left T k hk s)
    (untruncatedWitnessRejection i.left T i.multiplier k hk)
    (witnessExteriorDifference i.left T i.multiplier k hk s)

theorem commonWitnessComparisonScalar_ne_zero {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    commonWitnessComparisonScalar i ≠ 0 := outsideWitnessComparisonScalar_ne_zero _ _ _

theorem finiteCommonHarmonicVector_eq_untruncated_smul {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (hheight : (columnInsertion i.left).state.shape.colLen 0 ≤ s) :
    finiteCommonHarmonicVector i = commonWitnessComparisonScalar i •
      untruncatedCommonHarmonicVector i.toUnboundedHarmonicIndex := by
  rw [finiteCommonHarmonicVector_eq_normalized, untruncatedCommonHarmonicVector_eq_normalized]
  have hprefix := maximalFinitePrefix_eq_untruncated i hheight
  simp_rw [hprefix]
  have hlen : i.multiplier.colLen 0 ≤ (YoungDiagram.ofPartition i.part).card -
      maximalUntruncatedPrefix i.toUnboundedHarmonicIndex := by
    have h := i.multiplier_length
    simp only [YoungDiagram.card_ofPartition, maximalUntruncatedPrefix]
    omega
  rw [normalized_finiteWitness_eq_untruncated _ _ _ _ _ s hlen i.descents_lt i.multiplier_width,
    adjointYoungApply_smul, map_smul]
  rfl

theorem finiteCommonHarmonicCopy_eq_untruncated {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (hheight : (columnInsertion i.left).state.shape.colLen 0 ≤ s) :
    finiteCommonHarmonicCopy i = untruncatedCommonHarmonicCopy i.toUnboundedHarmonicIndex := by
  rw [finiteCommonHarmonicCopy, finiteCommonHarmonicVector_eq_untruncated_smul i hheight,
    cyclicPolynomialCopy_smul (commonWitnessComparisonScalar_ne_zero i)]
  rfl

def commonCopyBound {n : ℕ} (i : UnboundedHarmonicIndex n) : ℕ :=
  n + descentNumber i.left + i.multiplier.rowLen 0 + 1

theorem commonCopyBound_pos {n : ℕ} (i : UnboundedHarmonicIndex n) : 0 < commonCopyBound i := by
  dsimp [commonCopyBound]
  omega

theorem commonCopyBound_conditions {n s : ℕ} (i : UnboundedHarmonicIndex n)
    (h : commonCopyBound i ≤ s) :
    n ≤ s ∧ descentNumber i.left < s ∧
      i.multiplier.rowLen 0 ≤ s - descentNumber i.left - 1 := by
  dsimp [commonCopyBound] at h
  omega

def UnboundedHarmonicIndex.finiteAt {n : ℕ} (i : UnboundedHarmonicIndex n)
    (s : ℕ) (h : commonCopyBound i ≤ s) : FiniteHarmonicIndex n s where
  toUnboundedHarmonicIndex := i
  descents_lt := (commonCopyBound_conditions i h).2.1
  multiplier_width := (commonCopyBound_conditions i h).2.2

@[simp] theorem UnboundedHarmonicIndex.finiteAt_forget {n : ℕ}
    (i : UnboundedHarmonicIndex n) (s : ℕ) (h : commonCopyBound i ≤ s) :
    (i.finiteAt s h).toUnboundedHarmonicIndex = i := rfl

theorem UnboundedHarmonicIndex.finiteAt_copy {n : ℕ}
    (i : UnboundedHarmonicIndex n) (s : ℕ) (h : commonCopyBound i ≤ s) :
    finiteCommonHarmonicCopy (i.finiteAt s h) = untruncatedCommonHarmonicCopy i := by
  apply finiteCommonHarmonicCopy_eq_untruncated
  have hc : (columnInsertion i.left).state.shape.colLen 0 ≤ n :=
    (columnInsertion_height_le_card i.left).trans_eq (YoungDiagram.card_ofPartition i.part)
  exact hc.trans (commonCopyBound_conditions i h).1

set_option maxHeartbeats 800000 in
theorem untruncatedCommonHarmonicCopy_isSpecht {n : ℕ} (i : UnboundedHarmonicIndex n) :
    IsSpechtPolynomialCopy i.part (untruncatedCommonHarmonicCopy i) := by
  have h := finiteCommonHarmonicCopy_isSpecht
    (i.finiteAt (commonCopyBound i) le_rfl) (commonCopyBound_pos i)
  rw [show (i.finiteAt (commonCopyBound i) le_rfl).part = i.part from rfl,
    i.finiteAt_copy (commonCopyBound i) le_rfl] at h
  exact h

theorem untruncatedCommonHarmonicCopy_le_homogeneous {n : ℕ}
    (i : UnboundedHarmonicIndex n) :
    untruncatedCommonHarmonicCopy i ≤ homogeneousSubmodule (Fin n) ℂ i.degree := by
  rw [← i.finiteAt_copy (commonCopyBound i) le_rfl]
  exact finiteCommonHarmonicCopy_le_homogeneous _

theorem untruncatedCommonHarmonicCopies_iSupIndep {n : ℕ} :
    iSupIndep (untruncatedCommonHarmonicCopy (n := n)) := by
  rw [iSupIndep_iff_supIndep]
  intro t
  let s := t.sup commonCopyBound + 1
  have hs : 0 < s := by dsimp [s]; omega
  have hb (i : t) : commonCopyBound i.val ≤ s :=
    (Finset.le_sup (f := commonCopyBound) i.property).trans (Nat.le_succ _)
  let f : t → FiniteHarmonicIndex n s := fun i => i.val.finiteAt s (hb i)
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact congrArg FiniteHarmonicIndex.toUnboundedHarmonicIndex h
  have hi := (finiteCommonHarmonicCopies_iSupIndep (n := n) hs).comp hf
  have heq : (fun i : t => finiteCommonHarmonicCopy (f i)) =
      (fun i : t => untruncatedCommonHarmonicCopy i.val) := by
    funext i
    exact i.val.finiteAt_copy s (hb i)
  change iSupIndep (fun i : t => finiteCommonHarmonicCopy (f i)) at hi
  rw [heq] at hi
  exact hi.supIndep

theorem descentNumber_le_card {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    descentNumber S ≤ mu.card :=
  (ascentCount_le _ _).trans (Nat.sub_le _ _)

def unboundedDegreeFiniteCode {n d : ℕ}
    (i : {i : UnboundedHarmonicIndex n // i.degree = d}) : FiniteHarmonicIndex n (n + d + 1) where
  toUnboundedHarmonicIndex := i.val
  descents_lt := by
    have h := descentNumber_le_card i.val.left
    rw [YoungDiagram.card_ofPartition] at h
    omega
  multiplier_width := by
    have hdes := descentNumber_le_card i.val.left
    rw [YoungDiagram.card_ofPartition] at hdes
    have hw := rowLen_zero_le_card i.val.multiplier
    have hd := i.property
    dsimp only [UnboundedHarmonicIndex.degree] at hd
    omega

theorem unboundedDegreeFiniteCode_injective (n d : ℕ) :
    Function.Injective (unboundedDegreeFiniteCode (n := n) (d := d)) := by
  intro i j h
  apply Subtype.ext
  exact congrArg FiniteHarmonicIndex.toUnboundedHarmonicIndex h

theorem finite_unboundedHarmonic_degree (n d : ℕ) :
    Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d} := by
  letI : Finite {i : UnboundedHarmonicIndex n // i.degree = d} :=
    Finite.of_injective unboundedDegreeFiniteCode (unboundedDegreeFiniteCode_injective n d)
  exact Set.toFinite _

theorem untruncatedCommonHarmonicCopy_le {n : ℕ} (i : UnboundedHarmonicIndex n)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (he : i.eligible lam hk) :
    untruncatedCommonHarmonicCopy i ≤ ordinaryHarmonics (untruncatedIdeal ℂ n lam) := by
  let s := max (commonCopyBound i) (lam.colLen 0) + 1
  have hb : commonCopyBound i ≤ s := (le_max_left _ _).trans (Nat.le_succ _)
  have hs : 0 < s := by dsimp [s]; omega
  have hheight : lam.colLen 0 ≤ s := (le_max_right _ _).trans (Nat.le_succ _)
  rw [← i.finiteAt_copy s hb]
  exact (finiteCommonHarmonicCopy_le (i.finiteAt s hb) hs lam hk hheight he).trans
    (ordinaryHarmonics_antitone le_sup_left)

end HigherSpecht
end
end CanonicalSource60

section CanonicalSource61
/- Source: HigherSpecht/UntruncatedCommonAssembly.lean -/



/-!
# Exact simultaneous harmonic assembly at arbitrary degree

Every polynomial lies in a genuine finite coordinate-power harmonic space.
At a sufficiently large power bound all named finite cyclic copies have
stabilized to the named untruncated copies.  This proves the untruncated
spanning equality from the actual finite prescribed bases, while retaining
the precise witnesses and all degrees.  The final assembly remains explicitly
conditional until the independent nonempty-index count supplies those bases.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem ordinaryHarmonics_sup {n : ℕ} (I J : Ideal (PolynomialRing n ℂ)) :
    ordinaryHarmonics (I ⊔ J) = ordinaryHarmonics I ⊓ ordinaryHarmonics J := by
  ext p
  constructor
  · intro hp
    exact ⟨ordinaryHarmonics_antitone le_sup_left hp,
      ordinaryHarmonics_antitone le_sup_right hp⟩
  · rintro ⟨hI, hJ⟩ f hf
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hf
    rw [map_add, LinearMap.add_apply, hI u hu, hJ v hv, add_zero]

theorem mem_ordinaryGriffinHarmonics_of_totalDegree {n s : ℕ} {lam : YoungDiagram}
    {p : PolynomialRing n ℂ} (hp : p ∈ ordinaryHarmonics (untruncatedIdeal ℂ n lam))
    (hd : p.totalDegree < s) : p ∈ ordinaryHarmonics (griffinIdeal ℂ n lam s) := by
  have hs : 0 < s := (Nat.zero_le p.totalDegree).trans_lt hd
  rw [griffinIdeal, ordinaryHarmonics_sup]
  refine ⟨hp, ?_⟩
  rw [ordinaryHarmonics_powerIdeal_eq_restrictDegree n s hs]
  apply MvPolynomial.restrictTotalDegree_le_restrictDegree (Fin n) ℂ (s - 1)
  exact (MvPolynomial.mem_restrictTotalDegree (Fin n) (s - 1) p).mpr (by omega)

def eligibleUntruncatedCommonHarmonicSum (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Submodule ℂ (PolynomialRing n ℂ) :=
  ⨆ i : {i : UnboundedHarmonicIndex n // i.eligible lam hk}, untruncatedCommonHarmonicCopy i.val

theorem eligibleUntruncatedCommonHarmonicSum_le (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    eligibleUntruncatedCommonHarmonicSum n lam hk ≤ ordinaryHarmonics (untruncatedIdeal ℂ n lam) := by
  apply iSup_le
  intro i
  exact untruncatedCommonHarmonicCopy_le i.val lam hk i.property

theorem finiteEligibleSum_le_untruncated {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hns : n ≤ s) :
    eligibleCommonHarmonicSum n s lam hk ≤ eligibleUntruncatedCommonHarmonicSum n lam hk := by
  apply iSup_le
  intro i
  have hheight : (columnInsertion i.val.left).state.shape.colLen 0 ≤ s := by
    have h : (columnInsertion i.val.left).state.shape.colLen 0 ≤ n :=
      (columnInsertion_height_le_card i.val.left).trans_eq
        (YoungDiagram.card_ofPartition i.val.part)
    exact h.trans hns
  rw [finiteCommonHarmonicCopy_eq_untruncated i.val hheight]
  exact le_iSup (fun j : {j : UnboundedHarmonicIndex n // j.eligible lam hk} =>
    untruncatedCommonHarmonicCopy j.val) ⟨i.val.toUnboundedHarmonicIndex, i.property⟩

/-- Exact transfer, with its remaining finite-basis dependency displayed. -/
theorem untruncatedCommonHarmonic_decomposition_of_finite_bases
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    ordinaryHarmonics (untruncatedIdeal ℂ n lam) =
      eligibleUntruncatedCommonHarmonicSum n lam hk := by
  apply le_antisymm
  · intro p hp
    let s := p.totalDegree + n + lam.colLen 0 + 1
    have hs : 0 < s := by dsimp [s]; omega
    have hheight : lam.colLen 0 ≤ s := by dsimp [s]; omega
    have hns : n ≤ s := by dsimp [s]; omega
    have hds : p.totalDegree < s := by dsimp [s]; omega
    have hfinite := mem_ordinaryGriffinHarmonics_of_totalDegree hp hds
    rw [finiteCommonHarmonic_decomposition_of_specifiedBasis n s lam hk hs hheight
      (hb s hs hheight)] at hfinite
    exact finiteEligibleSum_le_untruncated lam hk hns hfinite
  · exact eligibleUntruncatedCommonHarmonicSum_le n lam hk

theorem untruncatedCommonHarmonic_decomposition_empty (n : ℕ) :
    ordinaryHarmonics (untruncatedIdeal ℂ n ⊥) =
      eligibleUntruncatedCommonHarmonicSum n ⊥ (by simp [YoungDiagram.card]) :=
  untruncatedCommonHarmonic_decomposition_of_finite_bases n ⊥
    (by simp [YoungDiagram.card])
    (fun s hs _ => griffin_empty_specifiedBasis ℂ n s hs)

theorem untruncatedCommonHarmonic_structure (n : ℕ) :
    (∀ i : UnboundedHarmonicIndex n,
      IsSpechtPolynomialCopy i.part (untruncatedCommonHarmonicCopy i) ∧
      untruncatedCommonHarmonicCopy i ≤ homogeneousSubmodule (Fin n) ℂ i.degree) ∧
    iSupIndep (untruncatedCommonHarmonicCopy (n := n)) ∧
    (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d}) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n),
      eligibleUntruncatedCommonHarmonicSum n lam hk ≤
        ordinaryHarmonics (untruncatedIdeal ℂ n lam) :=
  ⟨fun i => ⟨untruncatedCommonHarmonicCopy_isSpecht i,
    untruncatedCommonHarmonicCopy_le_homogeneous i⟩,
    untruncatedCommonHarmonicCopies_iSupIndep, finite_unboundedHarmonic_degree n,
    fun lam hk => eligibleUntruncatedCommonHarmonicSum_le n lam hk⟩

theorem finite_simultaneous_target_of_specified_bases
    (hb : ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ),
      0 < s → lam.colLen 0 ≤ s → IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    FiniteSimultaneousHarmonicTarget := by
  intro n s hn hs
  obtain ⟨hshape, hind, hmem⟩ := finiteCommonHarmonic_structure n s hs
  refine ⟨hshape, hind, ?_⟩
  intro lam hk hheight
  exact finiteCommonHarmonic_decomposition_of_specifiedBasis n s lam hk hs hheight
    (hb n lam hk s hs hheight)

theorem untruncated_simultaneous_target_of_specified_bases
    (hb : ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ),
      0 < s → lam.colLen 0 ≤ s → IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    UntruncatedSimultaneousHarmonicTarget := by
  intro n
  obtain ⟨hshape, hind, hfinite, hmem⟩ := untruncatedCommonHarmonic_structure n
  refine ⟨hshape, hind, hfinite, ?_⟩
  intro lam hk
  exact untruncatedCommonHarmonic_decomposition_of_finite_bases n lam hk (hb n lam hk)

end HigherSpecht
end
end CanonicalSource61

section CanonicalSource62
/- Source: HigherSpecht/PrincipalBases.lean -/



/-!
# The prescribed bases and simultaneous harmonic endpoints

The finite count is supplied by the actual battery injection.  The general
degreewise and parameter-ring assemblies are instantiated with that result;
no counting or spanning premise is retained in these endpoints.  At full
prefix length, the literal prefix tableau is the original tableau.  The
Springer specialization therefore uses exactly the manuscript's index and
polynomial family, including the empty diagram.

These declarations remain source candidates until the complete dependency
closure passes compilation and the independent statement and axiom audits.
The numerical rank, Frobenius series, and commutative-algebra conclusions of
Theorem 6.1 are separate statements, not consequences asserted by a name here.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

theorem standardTableau_heq_of_shape_eq {mu nu : YoungDiagram}
    (hshape : mu = nu) (S : StandardYoungTableau mu) (T : StandardYoungTableau nu)
    (hentry : ∀ c : ↥mu.cells, (S c).val =
      (T ⟨c.val, by simpa only [hshape] using c.property⟩).val) : HEq S T := by
  subst nu
  apply heq_of_eq
  apply StandardYoungTableau.ext
  intro c
  exact Fin.ext (hentry c)

theorem catDominates_of_heq {mu nu : YoungDiagram}
    {S : StandardYoungTableau mu} {T : StandardYoungTableau nu}
    (hshape : mu = nu) (h : HEq S T) (lam : YoungDiagram) :
    CatDominates S lam ↔ CatDominates T lam := by
  subst nu
  cases eq_of_heq h
  rfl

theorem prefixTableau_full_heq {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    HEq (prefixTableau S mu.card le_rfl) S := by
  apply standardTableau_heq_of_shape_eq (prefixShape_full S)
  intro c
  exact prefixTableau_apply_val S mu.card le_rfl c

@[simp] theorem catDominates_prefixTableau_full {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (lam : YoungDiagram) :
    CatDominates (prefixTableau S mu.card le_rfl) lam ↔ CatDominates S lam :=
  catDominates_of_heq (prefixShape_full S) (prefixTableau_full_heq S) lam

@[simp] theorem prefixEligible_full (lam : YoungDiagram) (P : StandardPair lam.card) :
    prefixEligible lam le_rfl P ↔ CatDominates P.left lam := by
  have transport (k : ℕ) (hk : k ≤ P.shape.card) (he : k = P.shape.card) :
      CatDominates (prefixTableau P.left k hk) lam ↔ CatDominates P.left lam := by
    subst k
    exact catDominates_prefixTableau_full P.left lam
  exact transport lam.card P.card_eq.symm.le P.card_eq.symm

/-- The exact quantified basis assertion of Theorem 4.1. -/
theorem theorem_4_1 (K : Type*) [Field K] [CharZero K] : GriffinBasisTarget K := by
  intro n lam hk s hlam hheight
  exact griffin_specifiedBasis K n lam hk s
    ((height_pos_of_card_pos lam hlam).trans_le hheight) hheight

def untruncatedPrescribedVectorBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (UntruncatedVectorIndex n lam hk) K (UntruncatedRing K n lam) :=
  untruncatedVectorBasisOfFiniteBases K n lam hk
    (fun s hs hheight => griffin_specifiedBasis K n lam hk s hs hheight)

@[simp] theorem untruncatedPrescribedVectorBasis_apply
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : UntruncatedVectorIndex n lam hk) :
    untruncatedPrescribedVectorBasis K n lam hk i =
      untruncatedVectorFamily K n lam hk i :=
  untruncatedVectorBasisOfFiniteBases_apply K n lam hk _ i

theorem untruncated_vector_basis_target (K : Type*) [Field K] [CharZero K] :
    UntruncatedVectorBasisTarget K := by
  intro n lam hk
  exact ⟨untruncatedPrescribedVectorBasis K n lam hk,
    untruncatedPrescribedVectorBasis_apply K n lam hk⟩

theorem diagram_eq_bot_of_height_zero {eta : YoungDiagram} (h : eta.colLen 0 = 0) :
    eta = ⊥ := by
  apply le_antisymm
  · intro c hc
    have hc' := YoungDiagram.lt_colLen_zero_of_mem hc
    rw [h] at hc'
    exact (Nat.not_lt_zero _ hc').elim
  · exact bot_le

def springerUntruncatedVectorIndexEquiv (lam : YoungDiagram) :
    SpringerIndex lam ≃ UntruncatedVectorIndex lam.card lam le_rfl where
  toFun i :=
    { base := ⟨i.val, (prefixEligible_full lam i.val).mpr i.property⟩
      multiplier := ⊥
      multiplier_length := by simp }
  invFun i := ⟨i.base.val, (prefixEligible_full lam i.base.val).mp i.base.property⟩
  left_inv i := Subtype.ext rfl
  right_inv i := by
    apply untruncatedVectorIndex_ext
    · rfl
    · exact (diagram_eq_bot_of_height_zero (by
        have h := i.multiplier_length
        simpa only [Nat.sub_self, Nat.le_zero] using h)).symm

@[simp] theorem springerUntruncatedVectorIndexEquiv_family
    (K : Type*) [CommRing K] (lam : YoungDiagram) (i : SpringerIndex lam) :
    untruncatedVectorFamily K lam.card lam le_rfl
        (springerUntruncatedVectorIndexEquiv lam i) = springerFamily K lam i := by
  simp only [untruncatedVectorFamily, springerUntruncatedVectorIndexEquiv,
    Nat.sub_self, elementaryMultiplier, Finset.range_zero, Finset.prod_empty,
    mul_one, springerFamily, springerIdeal] <;> rfl

def springerPrescribedBasis (K : Type*) [Field K] [CharZero K] (lam : YoungDiagram) :
    Basis (SpringerIndex lam) K (SpringerRing K lam) :=
  (untruncatedPrescribedVectorBasis K lam.card lam le_rfl).reindex
    (springerUntruncatedVectorIndexEquiv lam).symm

@[simp] theorem springerPrescribedBasis_apply (K : Type*) [Field K] [CharZero K]
    (lam : YoungDiagram) (i : SpringerIndex lam) :
    springerPrescribedBasis K lam i = springerFamily K lam i := by
  change ((untruncatedPrescribedVectorBasis K lam.card lam le_rfl).reindex
    (springerUntruncatedVectorIndexEquiv lam).symm) i =
      (springerFamily K lam i : UntruncatedRing K lam.card lam)
  rw [Basis.reindex_apply, untruncatedPrescribedVectorBasis_apply]
  exact springerUntruncatedVectorIndexEquiv_family K lam i

/-- The original prescribed Springer family, with no prefix reformulation
left in its statement. -/
theorem springer_basis_target (K : Type*) [Field K] [CharZero K] :
    SpringerBasisTarget K := by
  intro lam
  exact ⟨springerPrescribedBasis K lam, springerPrescribedBasis_apply K lam⟩

def untruncatedPrescribedParameterBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (UntruncatedIndex n lam hk) (ElementaryParameterRing K n lam)
      (UntruncatedRing K n lam) :=
  untruncatedParameterBasisOfFiniteBases K n lam hk
    (fun s hs hheight => griffin_specifiedBasis K n lam hk s hs hheight)

@[simp] theorem untruncatedPrescribedParameterBasis_apply
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : UntruncatedIndex n lam hk) :
    untruncatedPrescribedParameterBasis K n lam hk i =
      untruncatedFamily K n lam hk i :=
  untruncatedParameterBasisOfFiniteBases_apply K n lam hk _ i

/-- The free-basis part of Theorem 6.1 over the actual elementary-parameter
action, not an arbitrary polynomial-ring module structure. -/
theorem untruncated_specified_parameter_basis
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing K n lam)
      (untruncatedFamily K n lam hk) :=
  ⟨untruncatedPrescribedParameterBasis K n lam hk,
    untruncatedPrescribedParameterBasis_apply K n lam hk⟩

theorem untruncated_finite_parameters (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Finite (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) := by
  classical
  letI : Fintype (UntruncatedIndex n lam hk) := Fintype.ofFinite _
  exact Module.Finite.of_basis (untruncatedPrescribedParameterBasis K n lam hk)

theorem untruncated_parameter_rank_eq_index (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.finrank (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) =
      Nat.card (UntruncatedIndex n lam hk) := by
  classical
  letI : Fintype (UntruncatedIndex n lam hk) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (untruncatedPrescribedParameterBasis K n lam hk)]
  exact Nat.card_eq_fintype_card.symm

/-- All the named common finite harmonic copies simultaneously, with their
actual adjoint-Young vectors, factorial factors, and full ideal equalities. -/
theorem theorem_5_2 : FiniteSimultaneousHarmonicTarget :=
  finite_simultaneous_target_of_specified_bases
    (fun n lam hk s hs hheight => griffin_specifiedBasis ℂ n lam hk s hs hheight)

/-- The exact locally finite untruncated common-copy decomposition. -/
theorem theorem_6_6 : UntruncatedSimultaneousHarmonicTarget :=
  untruncated_simultaneous_target_of_specified_bases
    (fun n lam hk s hs hheight => griffin_specifiedBasis ℂ n lam hk s hs hheight)

end HigherSpecht
end
end CanonicalSource62
