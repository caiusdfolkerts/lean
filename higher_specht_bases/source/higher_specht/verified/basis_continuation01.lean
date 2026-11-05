module

public import higher_specht.verified.basis_remainder01
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import tau_ceti.ring_theory.mv_polynomial.symmetric.alternant
public import tau_ceti.ring_theory.mv_polynomial.groebner.normal_form

/- Generated ordinary proof stage. See audit/staged_specht_basis32/BasisContinuation01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/ColumnRowInsertion.lean -/



/-!
# Inserting a complete next column

A decreasing column word inserts one new entry at the end of each participating
row.  The proof follows the actual bumping route, using the old row entries as
upper-bounded prefixes.  This is the combinatorial bridge used to compare
column and row readings; no equality of insertion tableaux is assumed.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

def appendColumn : List (List ℕ) → List ℕ → List (List ℕ)
  | rows, [] => rows
  | [], c :: cs => [c] :: appendColumn [] cs
  | row :: rows, c :: cs => (row ++ [c]) :: appendColumn rows cs

/-- Every existing entry in row `i` is at most the new entry in that row. -/
def ColumnDominates : List (List ℕ) → List ℕ → Prop
  | _, [] => True
  | [], _ :: _ => True
  | row :: rows, c :: cs => (∀ z ∈ row, z ≤ c) ∧ ColumnDominates rows cs

 theorem columnDominates_tail {rows : List (List ℕ)} {c : ℕ} {cs : List ℕ}
    (h : ColumnDominates rows (c :: cs)) (hs : (c :: cs).SortedLT) :
    ColumnDominates rows cs := by
  induction rows generalizing c cs with
  | nil => cases cs <;> trivial
  | cons row rows ih =>
    cases cs with
    | nil => trivial
    | cons d ds =>
      obtain ⟨hr, ht⟩ := h
      obtain ⟨hc, hcs⟩ := List.sortedLT_cons.mp hs
      exact ⟨fun z hz => (hr z hz).trans (hc d (by simp)).le, ih ht hcs⟩

 theorem rowInsert_appendColumn (rows : List (List ℕ)) (c : ℕ) (cs : List ℕ)
    (h : ColumnDominates rows (c :: cs)) (hs : (c :: cs).SortedLT) :
    rowInsert c (appendColumn rows cs) = appendColumn rows (c :: cs) := by
  induction cs generalizing rows c with
  | nil =>
    cases rows with
    | nil => simpa only [appendColumn] using rowInsert_nil c
    | cons row rows =>
      have hb := rowBump_of_forall_le c row h.1
      simp only [appendColumn]
      rw [rowInsert_cons_of_eq_none rows (by rw [hb]), hb]
  | cons d ds ih =>
    obtain ⟨hc, hds⟩ := List.sortedLT_cons.mp hs
    have hcd : c < d := hc d (by simp)
    cases rows with
    | nil =>
      have hb : rowBump c [d] = ([c], some d) := by
        exact rowBump_cons_of_lt [] hcd
      simp only [appendColumn]
      rw [rowInsert_cons_of_eq_some _ (by rw [hb]), hb]
      exact congrArg (List.cons [c]) (ih [] d (by trivial) hds)
    | cons row rows =>
      obtain ⟨hr, ht⟩ := h
      have hb : rowBump c (row ++ [d]) = (row ++ [c], some d) := by
        rw [rowBump_append c row [d] hr, rowBump_cons_of_lt [] hcd]
      simp only [appendColumn]
      rw [rowInsert_cons_of_eq_some _ (by rw [hb]), hb]
      exact congrArg (List.cons (row ++ [c])) (ih rows d ht hds)

 theorem fold_reverseColumn (rows : List (List ℕ)) (cs : List ℕ)
    (h : ColumnDominates rows cs) (hs : cs.SortedLT) :
    cs.reverse.foldl (fun rows x => rowInsert x rows) rows = appendColumn rows cs := by
  induction cs generalizing rows with
  | nil => rfl
  | cons c cs ih =>
    rw [List.reverse_cons, List.foldl_append]
    change rowInsert c (cs.reverse.foldl (fun rows x => rowInsert x rows) rows) = _
    rw [ih rows (columnDominates_tail h hs) (List.sortedLT_cons.mp hs).2]
    exact rowInsert_appendColumn rows c cs h hs

 theorem knuth_appendColumn (rows : List (List ℕ)) (cs : List ℕ)
    (hr : RowsSorted rows) (h : ColumnDominates rows cs) (hs : cs.SortedLT) :
    KnuthEquivalent (rowWordRows rows ++ cs.reverse) (rowWordRows (appendColumn rows cs)) := by
  rw [← fold_reverseColumn rows cs h hs]
  exact knuth_fold_rowInsert cs.reverse rows hr

 theorem length_appendColumn (rows : List (List ℕ)) (cs : List ℕ) :
    (appendColumn rows cs).length = max rows.length cs.length := by
  induction cs generalizing rows with
  | nil => simp [appendColumn]
  | cons c cs ih =>
    cases rows with
    | nil => simp [appendColumn, ih]
    | cons row rows => simp [appendColumn, ih, Nat.succ_max_succ]

 theorem getElem_appendColumn {rows : List (List ℕ)} {cs : List ℕ}
    (hlen : cs.length ≤ rows.length) (i : ℕ) (hi : i < rows.length) :
    (appendColumn rows cs)[i]'(by rw [length_appendColumn, max_eq_left hlen]; exact hi) =
      rows[i] ++ (if hc : i < cs.length then [cs[i]] else []) := by
  induction rows generalizing cs i with
  | nil => simp at hi
  | cons row rows ih =>
    cases cs with
    | nil => simp [appendColumn]
    | cons c cs =>
      cases i with
      | zero => simp [appendColumn]
      | succ i =>
        simpa only [appendColumn, List.getElem_cons_succ, List.length_cons,
          Nat.add_lt_add_iff_right] using ih (by simpa using hlen) i (by simpa using hi)

end HigherSpecht
end
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/CyclicScheduler.lean -/



/-!
# The actual cyclic scan schedule

A token carries its fixed position in the original right-to-left scan and
its number of previous rejections.  Rejection moves the token to the back
of the queue and increments that number.  Its timestamp `round*n+position`
therefore strictly increases through the execution.  This proves the scan
ordering used by Lemma 2.2 independently of any assumption about the final
insertion shape.
-/

noncomputable section

namespace HigherSpecht

structure CyclingToken (n : ℕ) where
  position : Fin n
  round : ℕ
  deriving DecidableEq

namespace CyclingToken

variable {n : ℕ}

def stamp (t : CyclingToken n) : ℕ := t.round * n + t.position.val

def bump (t : CyclingToken n) : CyclingToken n := ⟨t.position, t.round + 1⟩

@[simp] theorem position_bump (t : CyclingToken n) : t.bump.position = t.position := rfl

@[simp] theorem round_bump (t : CyclingToken n) : t.bump.round = t.round + 1 := rfl

@[simp] theorem stamp_bump (t : CyclingToken n) : t.bump.stamp = t.stamp + n := by
  simp only [stamp, bump, Nat.add_mul, one_mul]
  omega

theorem stamp_lt_bump (t : CyclingToken n) : t.stamp < t.bump.stamp := by
  rw [stamp_bump]
  have := t.position.isLt
  omega

theorem round_le_of_stamp_le {t u : CyclingToken n} (h : t.stamp ≤ u.stamp) : t.round ≤ u.round := by
  by_contra hn
  have hr : u.round + 1 ≤ t.round := by omega
  have hmul := Nat.mul_le_mul_right n hr
  have ht := t.position.isLt
  have hu := u.position.isLt
  dsimp only [stamp] at h
  rw [Nat.add_mul, one_mul] at hmul
  omega

theorem position_lt_of_stamp_lt_round_eq {t u : CyclingToken n}
    (h : t.stamp < u.stamp) (hr : t.round = u.round) : t.position < u.position := by
  dsimp only [stamp] at h
  rw [hr] at h
  exact Nat.lt_of_add_lt_add_left h

end CyclingToken

def CyclingQueueValid {n : ℕ} (q : List (CyclingToken n)) : Prop :=
  q.Pairwise (fun a b => a.stamp < b.stamp) ∧
    ∀ a ∈ q, ∀ b ∈ q, b.stamp < a.stamp + n

theorem cyclingQueueValid_tail {n : ℕ} {t : CyclingToken n} {q : List (CyclingToken n)}
    (h : CyclingQueueValid (t :: q)) : CyclingQueueValid q :=
  ⟨h.1.tail, fun a ha b hb => h.2 a (by simp [ha]) b (by simp [hb])⟩

theorem cyclingQueueValid_reject {n : ℕ} {t : CyclingToken n} {q : List (CyclingToken n)}
    (h : CyclingQueueValid (t :: q)) : CyclingQueueValid (q ++ [t.bump]) := by
  have htail := cyclingQueueValid_tail h
  have hhead := (List.pairwise_cons.mp h.1).1
  refine ⟨List.pairwise_append.mpr ⟨htail.1, by simp, ?_⟩, ?_⟩
  · intro a ha b hb
    have hb' : b = t.bump := by simpa only [List.mem_singleton] using hb
    subst b
    rw [CyclingToken.stamp_bump]
    exact h.2 t (by simp) a (by simp [ha])
  · intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp hb with hb | hb
      · exact htail.2 a ha b hb
      · have hb' : b = t.bump := by simpa only [List.mem_singleton] using hb
        subst b
        rw [CyclingToken.stamp_bump]
        exact Nat.add_lt_add_right (hhead a ha) n
    · have ha' : a = t.bump := by simpa only [List.mem_singleton] using ha
      subst a
      rcases List.mem_append.mp hb with hb | hb
      · have hb' := h.2 t (by simp) b (by simp [hb])
        rw [CyclingToken.stamp_bump]
        omega
      · have hb' : b = t.bump := by simpa only [List.mem_singleton] using hb
        subst b
        have := t.position.isLt
        omega

def initialCyclingQueue (n : ℕ) : List (CyclingToken n) := List.ofFn fun i => ⟨i, 0⟩

theorem initialCyclingQueue_valid (n : ℕ) : CyclingQueueValid (initialCyclingQueue n) := by
  constructor
  · rw [initialCyclingQueue, List.pairwise_ofFn]
    intro i j hij
    simpa only [CyclingToken.stamp, Nat.zero_mul, Nat.zero_add] using
      (Fin.lt_iff_val_lt_val.mp hij)
  · intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    simp only [CyclingToken.stamp, Nat.zero_mul, Nat.zero_add]
    have := j.isLt
    omega

@[simp] theorem initialCyclingQueue_positions (n : ℕ) :
    (initialCyclingQueue n).map CyclingToken.position = List.finRange n := by
  simp only [initialCyclingQueue, List.map_ofFn, Function.comp_def, List.finRange]

/-- These are exactly the two queue operations of cyclic insertion. -/
inductive CyclingExecution {n : ℕ} (initial : List (CyclingToken n)) :
    List (CyclingToken n) → List (CyclingToken n) → Prop
  | start : CyclingExecution initial [] initial
  | accept {accepted pending} (t : CyclingToken n)
      (h : CyclingExecution initial accepted (t :: pending)) :
      CyclingExecution initial (accepted ++ [t]) pending
  | reject {accepted pending} (t : CyclingToken n)
      (h : CyclingExecution initial accepted (t :: pending)) :
      CyclingExecution initial accepted (pending ++ [t.bump])

theorem CyclingExecution.positions {n : ℕ} {initial accepted pending : List (CyclingToken n)}
    (h : CyclingExecution initial accepted pending) :
    (accepted.map CyclingToken.position ++ pending.map CyclingToken.position).Perm
      (initial.map CyclingToken.position) := by
  induction h with
  | start => simp
  | accept t h ih =>
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append] using ih
  | @reject accepted pending t h ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, CyclingToken.position_bump]
    have hswap := (List.perm_append_comm (l₁ := pending.map CyclingToken.position)
      (l₂ := [t.position])).append_left (accepted.map CyclingToken.position)
    exact hswap.trans ih

theorem CyclingExecution.ordering {n : ℕ} {initial accepted pending : List (CyclingToken n)}
    (h : CyclingExecution initial accepted pending) (hinitial : CyclingQueueValid initial) :
    CyclingQueueValid pending ∧
      accepted.Pairwise (fun a b => a.stamp < b.stamp) ∧
      ∀ a ∈ accepted, ∀ b ∈ pending, a.stamp < b.stamp := by
  induction h with
  | start => exact ⟨hinitial, by simp, by simp⟩
  | accept t h ih =>
    obtain ⟨hq, ha, haq⟩ := ih
    refine ⟨cyclingQueueValid_tail hq, ?_, ?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨ha, by simp, ?_⟩
      intro a ha b hb
      have hb' : b = t := by simpa only [List.mem_singleton] using hb
      subst b
      exact haq a ha t (by simp)
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha | ha
      · exact haq a ha b (by simp [hb])
      · have ha' : a = t := by simpa only [List.mem_singleton] using ha
        subst a
        exact (List.pairwise_cons.mp hq.1).1 b hb
  | reject t h ih =>
    obtain ⟨hq, ha, haq⟩ := ih
    refine ⟨cyclingQueueValid_reject hq, ha, ?_⟩
    intro a ha b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact haq a ha b (by simp [hb])
    · have hb' : b = t.bump := by simpa only [List.mem_singleton] using hb
      subst b
      exact (haq a ha t (by simp)).trans t.stamp_lt_bump

theorem CyclingExecution.complete_positions {n : ℕ} {accepted : List (CyclingToken n)}
    (h : CyclingExecution (initialCyclingQueue n) accepted []) :
    (accepted.map CyclingToken.position).Perm (List.finRange n) := by
  simpa only [List.map_nil, List.append_nil, initialCyclingQueue_positions] using h.positions

end HigherSpecht
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/LabeledInsertion.lean -/



/-!
# Lifting catabolism insertion to the actual labeled witness

Forgetting the fixed scan positions in this execution gives exactly the
previously defined cyclic catabolism algorithm.  The accepted cells record
their genuine tokens and rejection counts.  The invariant proves that they
fill the current Young diagram once each and that insertion order increases
from bottom to top in a column.
-/

noncomputable section

open Finset TauCeti Function

namespace HigherSpecht

variable {n : ℕ}

abbrev AcceptedToken (n : ℕ) := CyclingToken n × (ℕ × ℕ)

structure LabeledCatState (n : ℕ) where
  pending : List (CyclingToken n)
  shape : YoungDiagram
  accepted : List (AcceptedToken n)

def tokenValue (a : Fin n → ℕ) (t : CyclingToken n) : ℕ := a t.position + t.round

@[simp] theorem tokenValue_bump (a : Fin n → ℕ) (t : CyclingToken n) :
    tokenValue a t.bump = tokenValue a t + 1 := by
  simp only [tokenValue, CyclingToken.position_bump, CyclingToken.round_bump, Nat.add_assoc]

def labeledForget (a : Fin n → ℕ) (s : LabeledCatState n) : CatState :=
  ⟨(s.pending.map (tokenValue a)).reverse, s.shape⟩

def labeledInitial (n : ℕ) : LabeledCatState n :=
  ⟨initialCyclingQueue n, ⊥, []⟩

def labeledCatStep (a : Fin n → ℕ) (s : LabeledCatState n) : LabeledCatState n :=
  match s.pending with
  | [] => s
  | t :: q =>
    let c := (tokenValue a t, s.shape.rowLen (tokenValue a t))
    if YoungDiagram.IsAddable s.shape c then
      ⟨q, s.shape.addCell c, s.accepted ++ [(t, c)]⟩
    else
      ⟨q ++ [t.bump], s.shape, s.accepted⟩

def labeledCatRun (a : Fin n → ℕ) (N : ℕ) (s : LabeledCatState n) : LabeledCatState n :=
  (labeledCatStep a)^[N] s

theorem labeledForget_initial (a : Fin n → ℕ) :
    labeledForget a (labeledInitial n) = ⟨(List.ofFn a).reverse, ⊥⟩ := by
  simp only [labeledForget, labeledInitial, initialCyclingQueue, List.map_ofFn,
    Function.comp_def, tokenValue, Nat.add_zero]

theorem labeledForget_step (a : Fin n → ℕ) (s : LabeledCatState n) :
    labeledForget a (labeledCatStep a s) = catStep (labeledForget a s) := by
  rcases s with ⟨pending, shape, accepted⟩
  cases pending with
  | nil => rfl
  | cons t q =>
    unfold labeledCatStep labeledForget catStep
    simp only [List.reverse_reverse, List.map_cons]
    split_ifs with h
    · rfl
    · simp only [List.map_append, List.map_cons, List.map_nil,
        List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, tokenValue_bump, List.singleton_append]

theorem labeledForget_run (a : Fin n → ℕ) (N : ℕ) (s : LabeledCatState n) :
    labeledForget a (labeledCatRun a N s) = catRun N (labeledForget a s) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [labeledCatRun, Function.iterate_succ_apply', labeledForget_step]
    change catStep (labeledForget a (labeledCatRun a N s)) = _
    rw [ih]
    exact (Function.iterate_succ_apply' catStep N (labeledForget a s)).symm

structure LabeledInvariant (a : Fin n → ℕ) (s : LabeledCatState n) : Prop where
  execution : CyclingExecution (initialCyclingQueue n) (s.accepted.map Prod.fst) s.pending
  cells : (s.accepted.map Prod.snd).toFinset = s.shape.cells
  distinctCells : (s.accepted.map Prod.snd).Nodup
  rowValue : ∀ z ∈ s.accepted, z.2.1 = tokenValue a z.1
  columnOrder : s.accepted.Pairwise (fun z w => z.2.2 = w.2.2 → z.2.1 < w.2.1)

theorem labeledInvariant_initial (a : Fin n → ℕ) : LabeledInvariant a (labeledInitial n) := by
  refine ⟨CyclingExecution.start, ?_, by simp [labeledInitial], by simp [labeledInitial],
    by simp [labeledInitial]⟩
  simp [labeledInitial, YoungDiagram.cells_bot]

theorem row_lt_new_cell_of_same_column {shape : YoungDiagram} {c d : ℕ × ℕ}
    (hc : YoungDiagram.IsAddable shape c) (hd : d ∈ shape) (hcol : d.2 = c.2) : d.1 < c.1 := by
  by_contra hn
  apply hc.notMem
  exact shape.up_left_mem (le_of_not_gt hn) (le_of_eq hcol.symm) hd

theorem labeledInvariant_step (a : Fin n → ℕ) {s : LabeledCatState n}
    (hs : LabeledInvariant a s) : LabeledInvariant a (labeledCatStep a s) := by
  rcases s with ⟨pending, shape, accepted⟩
  cases pending with
  | nil => exact hs
  | cons t q =>
    unfold labeledCatStep
    dsimp only
    split_ifs with hc
    · let c := (tokenValue a t, shape.rowLen (tokenValue a t))
      have hcmem : c ∉ (accepted.map Prod.snd).toFinset := by
        rw [hs.cells]
        exact hc.notMem
      have hcnotlist : c ∉ accepted.map Prod.snd := by
        simpa only [List.mem_toFinset] using hcmem
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.map_append, List.map_cons, List.map_nil] using
          CyclingExecution.accept t hs.execution
      · simp only [List.map_append, List.map_cons, List.map_nil, List.toFinset_append,
          List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
          Finset.union_singleton, hs.cells, hc.cells_addCell_eq_insert]
      · rw [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        refine ⟨hs.distinctCells, by simp, ?_⟩
        intro z hz w hw hzw
        have hw' : w = c := by simpa only [List.mem_singleton] using hw
        exact hcnotlist (hzw.trans hw' ▸ hz)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hs.rowValue z hz
        · have hz' : z = (t, c) := by simpa only [List.mem_singleton] using hz
          subst z
          rfl
      · apply List.pairwise_append.mpr
        refine ⟨hs.columnOrder, by simp, ?_⟩
        intro z hz w hw hcol
        have hw' : w = (t, c) := by simpa only [List.mem_singleton] using hw
        subst w
        apply row_lt_new_cell_of_same_column hc _ hcol
        change z.2 ∈ shape.cells
        have hcells : (accepted.map Prod.snd).toFinset = shape.cells := hs.cells
        rw [← hcells]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩)
    · refine ⟨CyclingExecution.reject t hs.execution, hs.cells, hs.distinctCells,
        hs.rowValue, hs.columnOrder⟩

theorem labeledInvariant_run (a : Fin n → ℕ) (N : ℕ) :
    LabeledInvariant a (labeledCatRun a N (labeledInitial n)) := by
  induction N with
  | zero => exact labeledInvariant_initial a
  | succ N ih =>
    rw [labeledCatRun, Function.iterate_succ_apply']
    exact labeledInvariant_step a ih

theorem exists_complete_labeled_insertion (a : Fin n → ℕ)
    (ha : CatAdmissible ⟨(List.ofFn a).reverse, ⊥⟩) :
    ∃ s : LabeledCatState n, LabeledInvariant a s ∧ s.pending = [] ∧
      CatWordOutput (List.ofFn a).reverse s.shape := by
  obtain ⟨N, hN⟩ := catRun_eventually_empty ha
  let s := labeledCatRun a N (labeledInitial n)
  have hs := labeledInvariant_run a N
  have hforget : labeledForget a s = catRun N ⟨(List.ofFn a).reverse, ⊥⟩ := by
    dsimp only [s]
    rw [labeledForget_run, labeledForget_initial]
  have hpending : s.pending = [] := by
    have h := congrArg CatState.word hforget
    rw [hN] at h
    simpa only [labeledForget, List.reverse_eq_nil_iff, List.map_eq_nil_iff] using h
  refine ⟨s, hs, hpending, N, ?_⟩
  rw [← hforget]
  simp only [labeledForget, hpending, List.map_nil, List.reverse_nil]

theorem LabeledInvariant.complete_positions {a : Fin n → ℕ} {s : LabeledCatState n}
    (hs : LabeledInvariant a s) (hpending : s.pending = []) :
    ((s.accepted.map Prod.fst).map CyclingToken.position).Perm (List.finRange n) := by
  apply CyclingExecution.complete_positions
  simpa only [hpending] using hs.execution

theorem LabeledInvariant.accepted_stamp_order {a : Fin n → ℕ} {s : LabeledCatState n}
    (hs : LabeledInvariant a s) :
    s.accepted.Pairwise (fun z w => z.1.stamp < w.1.stamp) := by
  simpa only [List.pairwise_map] using
    (hs.execution.ordering (initialCyclingQueue_valid n)).2.1

end HigherSpecht
end
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/Rearrangement.lean -/



/-!
# The norm and prefix inequalities behind the triangular pairing

The equality statements are included: a strict ordering of the witness
exponents forces a norm-preserving permutation to fix the rejection levels.
The largest-subset equality then forces preservation of every column prefix.
-/

noncomputable section

open Finset Equiv Function

namespace HigherSpecht

variable {ι : Type*} [Fintype ι]

def squareNorm (a : ι → ℤ) : ℤ := ∑ i, a i ^ 2

theorem squareNorm_sub (a b : ι → ℤ) :
    squareNorm (fun i => a i - b i) =
      squareNorm a + squareNorm b - 2 * ∑ i, a i * b i := by
  unfold squareNorm
  calc
    ∑ i, (a i - b i) ^ 2 = ∑ i, (a i ^ 2 + b i ^ 2 - 2 * (a i * b i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

@[simp] theorem squareNorm_comp_perm (a : ι → ℤ) (σ : Equiv.Perm ι) :
    squareNorm (a ∘ σ) = squareNorm a :=
  Equiv.sum_comp σ (fun i => a i ^ 2)

@[simp] theorem squareNorm_permuted (a : ι → ℤ) (σ : Equiv.Perm ι) :
    squareNorm (fun i => a (σ i)) = squareNorm a :=
  squareNorm_comp_perm a σ

/-- A permutation of a finite sequence that monovaries with the sequence
must leave its values unchanged. -/
theorem eq_of_monovary_perm {r : ι → ℤ} (σ : Equiv.Perm ι)
    (h : Monovary r (r ∘ σ)) : r ∘ σ = r := by
  have hle : (∑ i, r i * r (σ i)) ≤ ∑ i, r i * r i :=
    (monovary_self r).sum_mul_comp_perm_le_sum_mul
  have hge := h.sum_mul_comp_perm_le_sum_mul (σ := σ.symm)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hge
  have hinner : (∑ i, r i * r (σ i)) = ∑ i, r i * r i := le_antisymm hle hge
  have hsq : squareNorm (fun i => r i - r (σ i)) = 0 := by
    rw [squareNorm_sub, squareNorm_permuted]
    change squareNorm r + squareNorm r - 2 * (∑ i, r i * r (σ i)) = 0
    rw [hinner]
    simp only [squareNorm, pow_two]
    ring
  have hzero : ∀ i, (r i - r (σ i)) ^ 2 = 0 := by
    have hz := (Fintype.sum_eq_zero_iff_of_nonneg (fun i => sq_nonneg _)).mp hsq
    exact fun i => congrFun hz i
  funext i
  have hi := sq_eq_zero_iff.mp (hzero i)
  exact (sub_eq_zero.mp hi).symm

/-- Two sequences ordered by the same injective reference sequence monovary. -/
theorem monovary_of_common_injective {a r s : ι → ℤ}
    (ha : Function.Injective a) (har : Monovary a r) (has : Monovary a s) :
    Monovary r s := by
  intro i j hs
  have hij : i ≠ j := fun h => hs.ne (congrArg s h)
  have hlt : a i < a j := lt_of_le_of_ne (has hs) (fun h => hij (ha h))
  exact har.symm hlt

theorem squareNorm_sub_le_permuted {a r : ι → ℤ}
    (h : Monovary a r) (σ : Equiv.Perm ι) :
    squareNorm (fun i => a i - r i) ≤ squareNorm (fun i => a (σ i) - r i) := by
  have hi := h.sum_comp_perm_mul_le_sum_mul (σ := σ)
  rw [squareNorm_sub, squareNorm_sub, squareNorm_permuted]
  linarith

/-- Exact equality case for a strictly ordered witness column. -/
theorem squareNorm_sub_eq_permuted_iff {a r : ι → ℤ}
    (ha : Function.Injective a) (h : Monovary a r) (σ : Equiv.Perm ι) :
    squareNorm (fun i => a i - r i) = squareNorm (fun i => a (σ i) - r i) ↔
      r ∘ σ = r := by
  constructor
  · intro heq
    have hinner : (∑ i, a (σ i) * r i) = ∑ i, a i * r i := by
      rw [squareNorm_sub, squareNorm_sub, squareNorm_permuted] at heq
      linarith
    have hnew := (h.sum_comp_perm_mul_eq_sum_mul_iff (σ := σ)).mp hinner
    have hnew' : Monovary a (r ∘ σ.symm) := by
      simpa only [Function.comp_def, Equiv.apply_symm_apply] using hnew.comp_right σ.symm
    have hr := eq_of_monovary_perm σ.symm (monovary_of_common_injective ha h hnew')
    funext i
    have hi := congrFun hr (σ i)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hi.symm
  · intro hr
    have hfun : (fun i => a (σ i) - r i) = (fun i => a i - r i) ∘ σ := by
      funext i
      simp only [Function.comp_apply]
      rw [show r (σ i) = r i from congrFun hr i]
    rw [hfun, squareNorm_comp_perm]

def restrictedPermutation {κ : Type*} (c : ι → κ) (σ : Equiv.Perm ι)
    (hc : ∀ i, c (σ i) = c i) (j : κ) : Equiv.Perm {i // c i = j} :=
  σ.subtypePerm fun i => by rw [hc i]

@[simp] theorem restrictedPermutation_apply {κ : Type*} (c : ι → κ)
    (σ : Equiv.Perm ι) (hc : ∀ i, c (σ i) = c i) (j : κ)
    (i : {i // c i = j}) :
    (restrictedPermutation c σ hc j i).val = σ i.val := rfl

/-- Rearrangement can be applied separately to every witness column. -/
theorem block_squareNorm_sub_le_permuted {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ι → κ) {a r : ι → ℤ}
    (h : ∀ j, Monovary (fun i : {i // c i = j} => a i)
      (fun i : {i // c i = j} => r i))
    (σ : Equiv.Perm ι) (hc : ∀ i, c (σ i) = c i) :
    squareNorm (fun i => a i - r i) ≤ squareNorm (fun i => a (σ i) - r i) := by
  unfold squareNorm
  rw [← Fintype.sum_fiberwise c (fun i => (a i - r i) ^ 2),
    ← Fintype.sum_fiberwise c (fun i => (a (σ i) - r i) ^ 2)]
  apply Finset.sum_le_sum
  intro j hj
  exact squareNorm_sub_le_permuted (h j) (restrictedPermutation c σ hc j)

theorem block_squareNorm_sub_eq_permuted_iff {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ι → κ) {a r : ι → ℤ}
    (ha : ∀ j, Function.Injective (fun i : {i // c i = j} => a i))
    (h : ∀ j, Monovary (fun i : {i // c i = j} => a i)
      (fun i : {i // c i = j} => r i))
    (σ : Equiv.Perm ι) (hc : ∀ i, c (σ i) = c i) :
    squareNorm (fun i => a i - r i) = squareNorm (fun i => a (σ i) - r i) ↔
      r ∘ σ = r := by
  constructor
  · intro heq
    have hnonneg (j : κ) : 0 ≤
        (∑ i : {i // c i = j}, (a (σ i) - r i) ^ 2) -
          ∑ i : {i // c i = j}, (a i - r i) ^ 2 :=
      sub_nonneg.mpr (squareNorm_sub_le_permuted (h j)
        (restrictedPermutation c σ hc j))
    have hsum : (∑ j, ((∑ i : {i // c i = j}, (a (σ i) - r i) ^ 2) -
        ∑ i : {i // c i = j}, (a i - r i) ^ 2)) = 0 := by
      rw [Finset.sum_sub_distrib,
        Fintype.sum_fiberwise c (fun i => (a (σ i) - r i) ^ 2),
        Fintype.sum_fiberwise c (fun i => (a i - r i) ^ 2)]
      exact sub_eq_zero.mpr heq.symm
    have hz := (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    funext i
    have heqj : squareNorm (fun x : {x // c x = c i} => a x - r x) =
        squareNorm (fun x : {x // c x = c i} =>
          a (restrictedPermutation c σ hc (c i) x) - r x) :=
      (sub_eq_zero.mp (congrFun hz (c i))).symm
    have hr := (squareNorm_sub_eq_permuted_iff (ha (c i)) (h (c i))
      (restrictedPermutation c σ hc (c i))).mp heqj
    exact congrFun hr ⟨i, rfl⟩
  · intro hr
    have hfun : (fun i => a (σ i) - r i) = (fun i => a i - r i) ∘ σ := by
      funext i
      simp only [Function.comp_apply]
      rw [show r (σ i) = r i from congrFun hr i]
    rw [hfun, squareNorm_comp_perm]

/-- A set containing the largest values has maximal sum among its permuted
images.  The proof applies rearrangement to its zero-one indicator. -/
theorem sum_permuted_le_sum_of_largest [DecidableEq ι] (A : Finset ι)
    (b : ι → ℤ) (hmax : ∀ i ∈ A, ∀ j ∉ A, b j ≤ b i) (σ : Equiv.Perm ι) :
    (∑ i ∈ A, b (σ i)) ≤ ∑ i ∈ A, b i := by
  let mask : ι → ℤ := fun i => if i ∈ A then 1 else 0
  have hm : Monovary b mask := by
    intro i j hij
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
    · simp [mask, hi, hj] at hij
    · simp [mask, hi, hj] at hij
    · exact hmax j hj i hi
    · simp [mask, hi, hj] at hij
  have h := hm.sum_comp_perm_mul_le_sum_mul (σ := σ)
  simpa [mask, Finset.sum_ite_mem, mul_ite] using h

/-- With distinct values, equality in the largest-subset bound fixes the
subset, not just its cardinality. -/
theorem mem_largest_iff_of_sum_permuted_eq [DecidableEq ι] (A : Finset ι)
    (b : ι → ℤ) (hb : Function.Injective b)
    (hmax : ∀ i ∈ A, ∀ j ∉ A, b j ≤ b i) (σ : Equiv.Perm ι)
    (hs : (∑ i ∈ A, b (σ i)) = ∑ i ∈ A, b i) :
    ∀ i, σ i ∈ A ↔ i ∈ A := by
  let mask : ι → ℤ := fun i => if i ∈ A then 1 else 0
  have hm : Monovary b mask := by
    intro i j hij
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
    · simp [mask, hi, hj] at hij
    · simp [mask, hi, hj] at hij
    · exact hmax j hj i hi
    · simp [mask, hi, hj] at hij
  have hinner : (∑ i, b (σ i) * mask i) = ∑ i, b i * mask i := by
    simpa [mask, Finset.sum_ite_mem, mul_ite] using hs
  have heq : squareNorm (fun i => b i - mask i) =
      squareNorm (fun i => b (σ i) - mask i) := by
    rw [squareNorm_sub, squareNorm_sub, squareNorm_permuted, hinner]
  have hmask := (squareNorm_sub_eq_permuted_iff hb hm σ).mp heq
  intro i
  have hi := congrFun hmask i
  by_cases hsi : σ i ∈ A <;> by_cases hai : i ∈ A <;>
    simp_all [mask, Function.comp_apply]

theorem eq_of_block_monovary_perm {κ : Type*} (c : ι → κ)
    {b : ι → ℤ} (σ : Equiv.Perm ι) (hc : ∀ i, c (σ i) = c i)
    (h : ∀ j, Monovary (fun i : {i // c i = j} => b i)
      (fun i : {i // c i = j} => b (σ i))) : b ∘ σ = b := by
  classical
  funext i
  have heq := eq_of_monovary_perm (restrictedPermutation c σ hc (c i)) (h (c i))
  exact congrFun heq ⟨i, rfl⟩

end HigherSpecht
end
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/WitnessGeometry.lean -/



/-!
# The two rearrangements in the coefficient witness

The first rearrangement is within a column of the insertion witness.  Equality
fixes the rejection count.  Within such a tie block the original column index
has the reverse ordering, so a second rearrangement fixes that column index.
These are the actual finite inequalities used in Lemma 3.1, including their
equality conditions; no polynomial or basis assertion is an input here.
-/

noncomputable section

open Finset Equiv Function

namespace HigherSpecht

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq κ] [DecidableEq ν]

def columnWeight (c b : ι → ℤ) : ℤ := ∑ i, c i * b i

@[simp] theorem columnWeight_neg (c b : ι → ℤ) :
    columnWeight (fun i => -c i) b = -columnWeight c b := by
  simp [columnWeight, Finset.sum_neg_distrib]

theorem columnWeight_comp_perm (c b : ι → ℤ) (σ : Equiv.Perm ι)
    (hc : c ∘ σ = c) : columnWeight c (b ∘ σ) = columnWeight c b := by
  have hfun : (fun i => c i * b (σ i)) = (fun i => c i * b i) ∘ σ := by
    funext i
    simp only [Function.comp_apply]
    rw [show c (σ i) = c i from congrFun hc i]
  unfold columnWeight
  change (∑ i, c i * b (σ i)) = ∑ i, c i * b i
  rw [hfun]
  exact Equiv.sum_comp σ (fun i => c i * b i)

/-- The second rearrangement, expressed by a weighted column sum.  This sum is
equivalent to the sum of the negative prefix sums at a fixed total degree. -/
theorem block_columnWeight_le_permuted (v : ι → ν) {b c : ι → ℤ}
    (hbc : ∀ j, Monovary (fun i : {i // v i = j} => b i)
      (fun i : {i // v i = j} => -c i))
    (σ : Equiv.Perm ι) (hv : ∀ i, v (σ i) = v i) :
    columnWeight c b ≤ columnWeight c (b ∘ σ) := by
  have h := block_squareNorm_sub_le_permuted v (a := b) (r := fun i => -c i) hbc σ hv
  rw [squareNorm_sub, squareNorm_sub, squareNorm_permuted] at h
  have hleft : (∑ i, b i * -c i) = -columnWeight c b := by
    simp [columnWeight, mul_comm, Finset.sum_neg_distrib]
  have hright : (∑ i, b (σ i) * -c i) = -columnWeight c (b ∘ σ) := by
    simp [columnWeight, mul_comm, Finset.sum_neg_distrib, Function.comp_apply]
  rw [hleft, hright] at h
  linarith

theorem block_columnWeight_eq_permuted_iff (v : ι → ν) {b c : ι → ℤ}
    (hb : ∀ j, Function.Injective (fun i : {i // v i = j} => b i))
    (hbc : ∀ j, Monovary (fun i : {i // v i = j} => b i)
      (fun i : {i // v i = j} => -c i))
    (σ : Equiv.Perm ι) (hv : ∀ i, v (σ i) = v i) :
    columnWeight c b = columnWeight c (b ∘ σ) ↔ c ∘ σ = c := by
  constructor
  · intro hweight
    have heq : squareNorm (fun i => b i - -c i) =
        squareNorm (fun i => b (σ i) - -c i) := by
      rw [squareNorm_sub, squareNorm_sub, squareNorm_permuted]
      have hleft : (∑ i, b i * -c i) = -columnWeight c b := by
        simp [columnWeight, mul_comm, Finset.sum_neg_distrib]
      have hright : (∑ i, b (σ i) * -c i) = -columnWeight c (b ∘ σ) := by
        simp [columnWeight, mul_comm, Finset.sum_neg_distrib, Function.comp_apply]
      rw [hleft, hright, hweight]
    have hneg := (block_squareNorm_sub_eq_permuted_iff v (a := b) (r := fun i => -c i) hb hbc σ hv).mp heq
    funext i
    exact neg_injective (congrFun hneg i)
  · intro hc
    exact (columnWeight_comp_perm c b σ hc).symm

/-- Pure insertion-witness data.  The two block maps are, respectively, its
columns and its columns refined by a common rejection count. -/
structure RearrangementWitness (u : ι → κ) (v : ι → ν)
    (a r b c : ι → ℤ) : Prop where
  subtraction : ∀ i, b i = a i - r i
  columnDistinct : ∀ j, Function.Injective (fun i : {i // u i = j} => a i)
  columnMonovary : ∀ j, Monovary (fun i : {i // u i = j} => a i)
    (fun i : {i // u i = j} => r i)
  refinement : ∀ i j, v i = v j ↔ u i = u j ∧ r i = r j
  tiedMonovary : ∀ j, Monovary (fun i : {i // v i = j} => b i)
    (fun i : {i // v i = j} => -c i)

namespace RearrangementWitness

variable {u : ι → κ} {v : ι → ν} {a r b c : ι → ℤ}
  (h : RearrangementWitness u v a r b c)

include h

theorem tiedDistinct (j : ν) :
    Function.Injective (fun i : {i // v i = j} => b i) := by
  intro i l hbil
  change b i.val = b l.val at hbil
  have hvl : v i.val = v l.val := i.property.trans l.property.symm
  obtain ⟨hul, hrl⟩ := (h.refinement i.val l.val).mp hvl
  have hal : a i.val = a l.val := by
    rw [h.subtraction i, h.subtraction l, hrl] at hbil
    exact sub_left_injective hbil
  have hil : (⟨i.val, rfl⟩ : {x // u x = u i.val}) =
      ⟨l.val, hul.symm⟩ := h.columnDistinct (u i.val) hal
  exact Subtype.ext (congrArg (fun x : {x // u x = u i.val} => x.val) hil)

theorem norm_le (σ : Equiv.Perm ι) (hu : ∀ i, u (σ i) = u i) :
    squareNorm b ≤ squareNorm (fun i => a (σ i) - r i) := by
  have hb : b = fun i => a i - r i := funext h.subtraction
  rw [hb]
  exact block_squareNorm_sub_le_permuted u h.columnMonovary σ hu

theorem rejection_fixed_of_norm_eq (σ : Equiv.Perm ι)
    (hu : ∀ i, u (σ i) = u i)
    (heq : squareNorm b = squareNorm (fun i => a (σ i) - r i)) :
    r ∘ σ = r := by
  have hb : b = fun i => a i - r i := funext h.subtraction
  rw [hb] at heq
  exact (block_squareNorm_sub_eq_permuted_iff u h.columnDistinct
    h.columnMonovary σ hu).mp heq

theorem refined_fixed (σ : Equiv.Perm ι) (hu : ∀ i, u (σ i) = u i)
    (hr : r ∘ σ = r) : ∀ i, v (σ i) = v i := by
  intro i
  exact (h.refinement (σ i) i).mpr ⟨hu i, congrFun hr i⟩

theorem shifted_eq_permuted (σ : Equiv.Perm ι) (hr : r ∘ σ = r) :
    (fun i => a (σ i) - r i) = b ∘ σ := by
  funext i
  rw [Function.comp_apply, h.subtraction, show r (σ i) = r i from congrFun hr i]

theorem weight_le_of_norm_eq (σ : Equiv.Perm ι)
    (hu : ∀ i, u (σ i) = u i)
    (heq : squareNorm b = squareNorm (fun i => a (σ i) - r i)) :
    columnWeight c b ≤ columnWeight c (fun i => a (σ i) - r i) := by
  have hr := h.rejection_fixed_of_norm_eq σ hu heq
  rw [h.shifted_eq_permuted σ hr]
  exact block_columnWeight_le_permuted v h.tiedMonovary σ (h.refined_fixed σ hu hr)

theorem columns_fixed_of_norm_weight_eq (σ : Equiv.Perm ι)
    (hu : ∀ i, u (σ i) = u i)
    (hnorm : squareNorm b = squareNorm (fun i => a (σ i) - r i))
    (hweight : columnWeight c b = columnWeight c (fun i => a (σ i) - r i)) :
    c ∘ σ = c := by
  have hr := h.rejection_fixed_of_norm_eq σ hu hnorm
  rw [h.shifted_eq_permuted σ hr] at hweight
  exact (block_columnWeight_eq_permuted_iff v h.tiedDistinct h.tiedMonovary σ
    (h.refined_fixed σ hu hr)).mp hweight

end RearrangementWitness

omit [Fintype κ] [DecidableEq κ] in
/-- A column-sorted filling is the unique such filling in its column orbit.
The reference function can be the row number, which is injective in each
column of a tableau. -/
theorem eq_of_columnOrbit_of_sorted (c : ι → κ) (row : ι → ℤ)
    (hrow : ∀ j, Function.Injective (fun i : {i // c i = j} => row i))
    {b d : ι → ℤ}
    (hb : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => b i))
    (hd : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => d i))
    (σ : Equiv.Perm ι) (hc : ∀ i, c (σ i) = c i)
    (heq : b ∘ σ = d) : b = d := by
  classical
  have hmono (j : κ) : Monovary (fun i : {i // c i = j} => b i)
      (fun i : {i // c i = j} => b (σ i)) := by
    have h := monovary_of_common_injective (hrow j) (hb j) (hd j)
    simpa only [← heq, Function.comp_apply] using h
  exact (eq_of_block_monovary_perm c σ hc hmono).symm.trans heq

omit [Fintype κ] [DecidableEq κ] in
/-- The same conclusion when two sorted fillings have a common column-orbit
representative. -/
theorem eq_of_common_columnOrbit_of_sorted (c : ι → κ) (row : ι → ℤ)
    (hrow : ∀ j, Function.Injective (fun i : {i // c i = j} => row i))
    {b d : ι → ℤ}
    (hb : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => b i))
    (hd : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => d i))
    (σ ρ : Equiv.Perm ι) (hσ : ∀ i, c (σ i) = c i)
    (hρ : ∀ i, c (ρ i) = c i) (heq : b ∘ σ = d ∘ ρ) : b = d := by
  apply eq_of_columnOrbit_of_sorted c row hrow hb hd (σ * ρ.symm)
  · intro i
    simp only [Equiv.Perm.mul_apply]
    rw [hσ]
    exact (hρ (ρ.symm i)).symm.trans (congrArg c (Equiv.apply_symm_apply ρ i))
  · funext i
    have h := congrFun heq (ρ.symm i)
    simpa only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using h

/-- A norm/column-weight key.  At a fixed degree, its second coordinate is the
sum of the negative prefix sums, up to an additive constant.  It is sufficient
for coefficient triangularity because all prefix inequalities have one sign. -/
def normWeightKey (c b : ι → ℤ) : ℤ ×ₗ ℤ :=
  toLex (squareNorm b, columnWeight c b)

/-- A coefficient contribution below this key must come from the same
column-sorted filling.  This is the geometric part of triangularity, with
every supporting order and equality hypothesis exposed. -/
theorem contribution_same_filling
    {u : ι → κ} {v : ι → ν} {a r b d beta c : ι → ℤ}
    (hw : RearrangementWitness u v a r b c)
    (σ : Equiv.Perm ι) (hu : ∀ i, u (σ i) = u i)
    (hbeta : beta = fun i => a (σ i) - r i)
    (hnorm : squareNorm beta ≤ squareNorm d)
    (hweight : squareNorm beta = squareNorm d → columnWeight c beta ≤ columnWeight c d)
    (horbit : squareNorm beta = squareNorm d →
      columnWeight c beta = columnWeight c d →
      ∃ ρ : Equiv.Perm ι, c ∘ ρ = c ∧ beta = d ∘ ρ)
    (hkey : normWeightKey c d ≤ normWeightKey c b)
    (row : ι → ℤ)
    (hrow : ∀ j, Function.Injective (fun i : {i // c i = j} => row i))
    (hb : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => b i))
    (hd : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => d i)) : b = d := by
  have hk := Prod.Lex.toLex_le_toLex'.mp hkey
  have hnb : squareNorm b ≤ squareNorm beta := by
    rw [hbeta]
    exact hw.norm_le σ hu
  have hbd : squareNorm b = squareNorm d := le_antisymm (hnb.trans hnorm) hk.1
  have hnbe : squareNorm b = squareNorm beta := le_antisymm hnb (hnorm.trans hk.1)
  have hned : squareNorm beta = squareNorm d := hnbe.symm.trans hbd
  have hwb : columnWeight c b ≤ columnWeight c beta := by
    rw [hbeta] at hnbe ⊢
    exact hw.weight_le_of_norm_eq σ hu hnbe
  have hwd := hweight hned
  have hwdb : columnWeight c d ≤ columnWeight c b := hk.2 hbd.symm
  have hwbe : columnWeight c b = columnWeight c beta :=
    le_antisymm hwb (hwd.trans hwdb)
  have hwed : columnWeight c beta = columnWeight c d :=
    le_antisymm hwd (hwdb.trans hwb)
  have hcσ : c ∘ σ = c := by
    rw [hbeta] at hnbe hwbe
    exact hw.columns_fixed_of_norm_weight_eq σ hu hnbe hwbe
  have hr := hw.rejection_fixed_of_norm_eq σ hu (hbeta ▸ hnbe)
  have hbeta' : beta = b ∘ σ := hbeta.trans (hw.shifted_eq_permuted σ hr)
  obtain ⟨ρ, hcρ, hρ⟩ := horbit hned hwed
  exact eq_of_common_columnOrbit_of_sorted c row hrow hb hd σ ρ
    (fun i => congrFun hcσ i) (fun i => congrFun hcρ i) (hbeta'.symm.trans hρ)

end HigherSpecht
end
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/Apolar.lean -/



/-!
# Integral divided-power contraction and inverse systems

The underlying free module has symbols x^[a], represented here by the monomial
basis of `MvPolynomial`.  Multiplication in that polynomial type is used only
for the acting polynomial ring; contraction on the target is the explicitly
defined operation below.  In particular this does not identify ordinary
differentiation with contraction in positive characteristic.
-/

noncomputable section

open MvPolynomial

namespace HigherSpecht

variable {σ R : Type*} [CommRing R]

/-- Contraction by x^d on divided-power symbols. -/
def contractMonomial (d : σ →₀ ℕ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.basisMonomials σ R).constr R fun a =>
    if d ≤ a then MvPolynomial.monomial (a - d) 1 else 0

@[simp] theorem contractMonomial_monomial_one (d a : σ →₀ ℕ) :
    contractMonomial (R := R) d (MvPolynomial.monomial a 1) =
      if d ≤ a then MvPolynomial.monomial (a - d) 1 else 0 := by
  exact (MvPolynomial.basisMonomials σ R).constr_basis R _ a

theorem contractMonomial_monomial (d a : σ →₀ ℕ) (c : R) :
    contractMonomial d (MvPolynomial.monomial a c) =
      if d ≤ a then MvPolynomial.monomial (a - d) c else 0 := by
  classical
  have heq : MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [heq, map_smul, contractMonomial_monomial_one]
  split_ifs <;> simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one, smul_zero]

/-- The exact coefficient formula for contraction. -/
@[simp] theorem coeff_contractMonomial (d : σ →₀ ℕ) (p : MvPolynomial σ R)
    (r : σ →₀ ℕ) :
    (contractMonomial d p).coeff r = p.coeff (r + d) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial a c =>
    rw [contractMonomial_monomial]
    by_cases h : d ≤ a
    · rw [if_pos h]
      simp only [coeff_monomial, tsub_eq_iff_eq_add_of_le h]
    · rw [if_neg h]
      have hne : a ≠ r + d := by
        rintro rfl
        exact h le_add_self
      simp [coeff_monomial, hne]

@[simp] theorem contractMonomial_zero :
    contractMonomial (σ := σ) (R := R) 0 = LinearMap.id := by
  ext p r
  simp

theorem contractMonomial_add (a b : σ →₀ ℕ) :
    contractMonomial (R := R) (a + b) =
      (contractMonomial a).comp (contractMonomial b) := by
  ext p r
  simp [add_assoc, add_comm, add_left_comm]

theorem contractMonomial_comm (a b : σ →₀ ℕ) (p : MvPolynomial σ R) :
    contractMonomial a (contractMonomial b p) =
      contractMonomial b (contractMonomial a p) := by
  rw [← LinearMap.comp_apply, ← contractMonomial_add, add_comm,
    contractMonomial_add, LinearMap.comp_apply]

theorem contractMonomial_rename (e : Equiv.Perm σ) (d : σ →₀ ℕ)
    (p : MvPolynomial σ R) :
    contractMonomial (d.mapDomain e) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (contractMonomial d p) := by
  classical
  apply MvPolynomial.ext
  intro m
  obtain ⟨r, rfl⟩ := Finsupp.mapDomain_surjective e.surjective m
  rw [coeff_contractMonomial, ← Finsupp.mapDomain_add,
    MvPolynomial.coeff_rename_mapDomain e e.injective,
    MvPolynomial.coeff_rename_mapDomain e e.injective, coeff_contractMonomial]

def contractionMonoidHom : Multiplicative (σ →₀ ℕ) →*
    Module.End R (MvPolynomial σ R) where
  toFun a := contractMonomial a.toAdd
  map_one' := contractMonomial_zero
  map_mul' a b := contractMonomial_add a.toAdd b.toAdd

/-- The acting polynomial algebra, represented by divided-power contractions. -/
def dividedAction : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  AddMonoidAlgebra.lift R (Module.End R (MvPolynomial σ R)) (σ →₀ ℕ)
    contractionMonoidHom

@[simp] theorem dividedAction_monomial (d : σ →₀ ℕ) (c : R) :
    dividedAction (MvPolynomial.monomial d c) = c • contractMonomial d := by
  exact AddMonoidAlgebra.lift_single contractionMonoidHom d c

@[simp] theorem dividedAction_X (i : σ) :
    dividedAction (MvPolynomial.X i : MvPolynomial σ R) =
      contractMonomial (Finsupp.single i 1) := by
  simp only [MvPolynomial.X, dividedAction_monomial, one_smul]

theorem dividedAction_mul (f g p : MvPolynomial σ R) :
    dividedAction (f * g) p = dividedAction f (dividedAction g p) := by
  rw [map_mul, Module.End.mul_apply]

theorem dividedAction_comm (f g p : MvPolynomial σ R) :
    dividedAction f (dividedAction g p) = dividedAction g (dividedAction f p) := by
  rw [← dividedAction_mul, mul_comm, dividedAction_mul]

theorem dividedAction_rename (e : Equiv.Perm σ) (f p : MvPolynomial σ R) :
    dividedAction (MvPolynomial.rename e f) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (dividedAction f p) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial d c =>
    simp only [MvPolynomial.rename_monomial, dividedAction_monomial,
      LinearMap.smul_apply, contractMonomial_rename, map_smul]

/-- The inverse system of an ideal, with its actual contraction action. -/
def dividedHarmonics (I : Ideal (MvPolynomial σ R)) : Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ f ∈ I, dividedAction f p = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq f hf
    rw [map_add, hp f hf, hq f hf, add_zero]
  smul_mem' := by
    intro c p hp f hf
    rw [map_smul, hp f hf, smul_zero]

@[simp] theorem mem_dividedHarmonics {I : Ideal (MvPolynomial σ R)}
    {p : MvPolynomial σ R} :
    p ∈ dividedHarmonics I ↔ ∀ f ∈ I, dividedAction f p = 0 := Iff.rfl

theorem dividedHarmonics_antitone :
    Antitone (dividedHarmonics (σ := σ) (R := R)) := by
  intro I J h p hp f hf
  exact hp f (h hf)

theorem dividedAction_mem_dividedHarmonics {I : Ideal (MvPolynomial σ R)}
    {p : MvPolynomial σ R} (hp : p ∈ dividedHarmonics I) (g : MvPolynomial σ R) :
    dividedAction g p ∈ dividedHarmonics I := by
  intro f hf
  rw [dividedAction_comm, hp f hf, map_zero]

/-- Annihilation of a generating set implies annihilation of its generated
ideal; closure under polynomial multiples is proved using the actual action. -/
theorem mem_dividedHarmonics_span_iff (S : Set (MvPolynomial σ R))
    (p : MvPolynomial σ R) :
    p ∈ dividedHarmonics (Ideal.span S) ↔ ∀ f ∈ S, dividedAction f p = 0 := by
  constructor
  · intro h f hf
    exact h f (Ideal.subset_span hf)
  · intro h f hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact h f hf
    | zero => simp
    | add f g hf hg hfi hgi => simp [hfi, hgi]
    | smul f g hg hgi =>
      change dividedAction (f * g) p = 0
      rw [dividedAction_mul, hgi, map_zero]

/-- A shifted coefficient of the contraction against one genuine witness is
a linear functional on the acting polynomial ring. -/
def contractionCoefficient (w : MvPolynomial σ R) (r : σ →₀ ℕ) :
    Module.Dual R (MvPolynomial σ R) :=
  (MvPolynomial.lcoeff R r).comp
    ((LinearMap.applyₗ w).comp dividedAction.toLinearMap)

@[simp] theorem contractionCoefficient_apply (w f : MvPolynomial σ R) (r : σ →₀ ℕ) :
    contractionCoefficient w r f = (dividedAction f w).coeff r := rfl

theorem contractionCoefficient_kills_ideal {I : Ideal (MvPolynomial σ R)}
    {w : MvPolynomial σ R} (hw : w ∈ dividedHarmonics I) (r : σ →₀ ℕ) :
    I.restrictScalars R ≤ LinearMap.ker (contractionCoefficient w r) := by
  intro f hf
  change (dividedAction f w).coeff r = 0
  rw [hw f hf]
  rfl

@[simp] theorem contractionCoefficient_zero (r : σ →₀ ℕ) :
    contractionCoefficient (0 : MvPolynomial σ R) r = 0 := by
  ext f
  simp

theorem contractionCoefficient_add (u w : MvPolynomial σ R) (r : σ →₀ ℕ) :
    contractionCoefficient (u + w) r =
      contractionCoefficient u r + contractionCoefficient w r := by
  ext f
  simp

theorem contractionCoefficient_smul (c : R) (w : MvPolynomial σ R) (r : σ →₀ ℕ) :
    contractionCoefficient (c • w) r = c • contractionCoefficient w r := by
  ext f
  simp

theorem contractionCoefficient_sum {κ : Type*} (s : Finset κ)
    (w : κ → MvPolynomial σ R) (r : σ →₀ ℕ) :
    contractionCoefficient (∑ j ∈ s, w j) r = ∑ j ∈ s, contractionCoefficient (w j) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, contractionCoefficient_add, ih, Finset.sum_insert ha]

/-- A witness monomial represents an actual shifted coefficient functional;
if its exponent is too small the functional is zero. -/
theorem contractionCoefficient_monomial (a r : σ →₀ ℕ) (c : R) :
    contractionCoefficient (MvPolynomial.monomial a c) r =
      if r ≤ a then c • MvPolynomial.lcoeff R (a - r) else 0 := by
  classical
  apply (MvPolynomial.basisMonomials σ R).ext
  intro d
  change (dividedAction (MvPolynomial.monomial d 1)
    (MvPolynomial.monomial a c)).coeff r = _
  simp only [dividedAction_monomial, one_smul, coeff_contractMonomial,
    coeff_monomial]
  by_cases hr : r ≤ a
  · rw [if_pos hr]
    have heq : a = r + d ↔ d = a - r := by
      constructor
      · rintro rfl
        simp
      · rintro rfl
        exact (add_tsub_cancel_of_le hr).symm
    simp only [LinearMap.smul_apply, MvPolynomial.lcoeff_apply, coeff_monomial,
      smul_eq_mul, heq]
    split_ifs <;> simp_all
  · rw [if_neg hr, LinearMap.zero_apply]
    have heq : a ≠ r + d := by
      rintro rfl
      exact hr le_self_add
    simp [heq]

/-- The exact integral coefficient-pairing formula for an alternating
monomial witness.  No factorial division is present. -/
theorem contractionCoefficient_signed_sum {κ : Type*} (s : Finset κ)
    (a : κ → σ →₀ ℕ) (sign : κ → R) (r : σ →₀ ℕ) :
    contractionCoefficient (∑ j ∈ s, MvPolynomial.monomial (a j) (sign j)) r =
      ∑ j ∈ s, if r ≤ a j then sign j • MvPolynomial.lcoeff R (a j - r) else 0 := by
  rw [contractionCoefficient_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact contractionCoefficient_monomial (a j) r (sign j)

theorem dividedHarmonics_sup (I J : Ideal (MvPolynomial σ R)) :
    dividedHarmonics (I ⊔ J) = dividedHarmonics I ⊓ dividedHarmonics J := by
  ext p
  constructor
  · intro hp
    exact ⟨fun f hf => hp f (Submodule.mem_sup_left hf),
      fun f hf => hp f (Submodule.mem_sup_right hf)⟩
  · rintro ⟨hI, hJ⟩ f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
    simp [hI a ha, hJ b hb]

end HigherSpecht
end
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/AlternantContraction.lean -/



/-!
# Integral annihilation of a column alternant

Every positive elementary symmetric contraction annihilates the divided-power
staircase alternant.  The proof works over an arbitrary commutative ring: each
surviving lowered staircase repeats an exponent, so its determinant vanishes.
It does not divide by factorials, by two, or by a group order.
-/

noncomputable section

open MvPolynomial Finset Equiv

namespace HigherSpecht

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

def fullAlternation : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  ∑ e : Equiv.Perm σ, (((Equiv.Perm.sign e : ℤ) : R)) • (MvPolynomial.rename e).toLinearMap

theorem fullAlternation_apply (p : MvPolynomial σ R) :
    fullAlternation p = ∑ e : Equiv.Perm σ,
      (((Equiv.Perm.sign e : ℤ) : R)) • MvPolynomial.rename e p := by
  simp only [fullAlternation, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply]

theorem monomial_equivFun_eq_prod (a : σ → ℕ) :
    (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1 : MvPolynomial σ R) =
      ∏ i, X i ^ a i := by
  rw [MvPolynomial.prod_X_pow]
  have ha : Finsupp.equivFunOnFinite.symm a =
      Finsupp.indicator (Finset.univ : Finset σ) (fun i _ => a i) := by
    ext i
    simp only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.indicator_apply,
      Finset.mem_univ, dite_true]
  rw [ha]

theorem fullAlternation_monomial (a : σ →₀ ℕ) :
    fullAlternation (MvPolynomial.monomial a (1 : R)) = TauCeti.alternant σ R a := by
  have ha : a = Finsupp.equivFunOnFinite.symm (fun i => a i) := by ext i; rfl
  rw [ha, monomial_equivFun_eq_prod, fullAlternation_apply, TauCeti.alternant_eq_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [map_prod, map_pow, rename_X, Units.smul_def, Int.cast_smul_eq_zsmul,
    Finsupp.coe_equivFunOnFinite_symm]

theorem dividedAction_fullAlternation {f : MvPolynomial σ R} (hf : f.IsSymmetric)
    (p : MvPolynomial σ R) :
    dividedAction f (fullAlternation p) = fullAlternation (dividedAction f p) := by
  rw [fullAlternation_apply, fullAlternation_apply]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  have h := dividedAction_rename e f p
  rwa [hf e] at h

def subsetExponent (A : Finset σ) : σ →₀ ℕ :=
  Finsupp.indicator A fun _ _ => 1

@[simp] theorem subsetExponent_apply (A : Finset σ) (i : σ) :
    subsetExponent A i = if i ∈ A then 1 else 0 := by
  classical
  simp [subsetExponent, Finsupp.indicator_apply]

theorem prod_X_eq_monomial_subset (A : Finset σ) :
    (∏ i ∈ A, X i : MvPolynomial σ R) = monomial (subsetExponent A) 1 := by
  simpa only [pow_one, subsetExponent] using
    (MvPolynomial.prod_X_pow (R := R) (fun _ : σ => 1) A)

theorem dividedAction_esymm_monomial (d : ℕ) (a : σ →₀ ℕ) :
    dividedAction (MvPolynomial.esymm σ R d) (MvPolynomial.monomial a 1) =
      ∑ A ∈ (Finset.univ : Finset σ).powersetCard d,
        if subsetExponent A ≤ a then monomial (a - subsetExponent A) 1 else 0 := by
  simp only [MvPolynomial.esymm, map_sum, LinearMap.sum_apply,
    prod_X_eq_monomial_subset, dividedAction_monomial, one_smul,
    contractMonomial_monomial_one]

def staircaseExponent (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => i.val

@[simp] theorem staircaseExponent_apply (n : ℕ) (i : Fin n) :
    staircaseExponent n i = i.val := rfl

/-- If lowering a nonempty subset of a staircase is possible, its least
lowered position and the preceding position acquire the same exponent. -/
theorem lowered_staircase_not_injective {n : ℕ} (A : Finset (Fin n))
    (hA : A.Nonempty) (hle : subsetExponent A ≤ staircaseExponent n) :
    ¬ Function.Injective (fun i => (staircaseExponent n - subsetExponent A) i) := by
  let a := A.min' hA
  have ha : a ∈ A := A.min'_mem hA
  have hap : 0 < a.val := by
    have hi := hle a
    simp only [subsetExponent_apply, if_pos ha, staircaseExponent_apply] at hi
    omega
  let b : Fin n := ⟨a.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩
  have hba : b < a := by
    change a.val - 1 < a.val
    omega
  have hb : b ∉ A := by
    intro hb
    have hab := A.min'_le b hb
    exact (not_lt_of_ge hab) hba
  have heq : (staircaseExponent n - subsetExponent A) a =
      (staircaseExponent n - subsetExponent A) b := by
    simp only [Finsupp.tsub_apply, staircaseExponent_apply, subsetExponent_apply,
      if_pos ha, if_neg hb, Nat.sub_zero]
    rfl
  intro hinj
  exact hba.ne (hinj heq).symm

/-- The full elementary annihilation identity for a single column, over every
commutative coefficient ring and in every characteristic. -/
theorem elementary_contract_staircase_alternant (n d : ℕ) (hd : 0 < d) :
    dividedAction (MvPolynomial.esymm (Fin n) R d)
      (TauCeti.alternant (Fin n) R fun i => i.val) = 0 := by
  change dividedAction (MvPolynomial.esymm (Fin n) R d)
    (TauCeti.alternant (Fin n) R (staircaseExponent n)) = 0
  rw [← fullAlternation_monomial (staircaseExponent n)]
  rw [dividedAction_fullAlternation (MvPolynomial.esymm_isSymmetric _ _ _),
    dividedAction_esymm_monomial, map_sum]
  apply Finset.sum_eq_zero
  intro A hA
  by_cases hle : subsetExponent A ≤ staircaseExponent n
  · rw [if_pos hle, fullAlternation_monomial]
    apply TauCeti.alternant_eq_zero_of_not_injective
    apply lowered_staircase_not_injective A _ hle
    exact Finset.card_pos.mp (by simpa [(Finset.mem_powersetCard.mp hA).2] using hd)
  · rw [if_neg hle, map_zero]

theorem coeff_staircase_alternant_eq_zero_of_large {n : ℕ}
    (a : Fin n →₀ ℕ) (i : Fin n) (hi : n ≤ a i) :
    (TauCeti.alternant (Fin n) R fun j => j.val).coeff a = 0 := by
  rw [TauCeti.coeff_alternant]
  apply Finset.sum_eq_zero
  intro e he
  have h := (Finset.mem_filter.mp he).2
  have heq := congrFun h (e.symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at heq
  have hlt := (e.symm i).isLt
  omega

/-- Each exponent in a column of height `n` is strictly below `n`; hence every
contraction by a power at least `n` vanishes. -/
theorem power_contract_staircase_alternant {n s : ℕ} (hs : n ≤ s) (i : Fin n) :
    dividedAction ((X i : MvPolynomial (Fin n) R) ^ s)
      (TauCeti.alternant (Fin n) R fun j => j.val) = 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, dividedAction_monomial, one_smul]
  apply MvPolynomial.ext
  intro a
  rw [coeff_contractMonomial]
  change (TauCeti.alternant (Fin n) R fun j => j.val).coeff
    (a + Finsupp.single i s) = 0
  apply coeff_staircase_alternant_eq_zero_of_large _ i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  omega

end HigherSpecht
end
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/TensorContraction.lean -/



/-!
# Contraction on disjoint sets of variables

Divided-power contraction has no ordinary Leibniz rule.  The identities here
establish the precise replacement needed for the column witnesses: an operator
on one set of variables acts only on that factor of a product in disjoint
variables.  The coefficient ring is arbitrary.
-/

noncomputable section

open MvPolynomial

namespace HigherSpecht

variable {σ τ R : Type*} [CommRing R]

/-- Product of polynomials in disjoint sets of variables. -/
def tensorPolynomial (p : MvPolynomial σ R) (q : MvPolynomial τ R) :
    MvPolynomial (σ ⊕ τ) R :=
  MvPolynomial.rename Sum.inl p * MvPolynomial.rename Sum.inr q

@[simp] theorem tensorPolynomial_add_left (p p' : MvPolynomial σ R)
    (q : MvPolynomial τ R) :
    tensorPolynomial (p + p') q = tensorPolynomial p q + tensorPolynomial p' q := by
  simp [tensorPolynomial, add_mul]

@[simp] theorem tensorPolynomial_add_right (p : MvPolynomial σ R)
    (q q' : MvPolynomial τ R) :
    tensorPolynomial p (q + q') = tensorPolynomial p q + tensorPolynomial p q' := by
  simp [tensorPolynomial, mul_add]

@[simp] theorem tensorPolynomial_smul_left (c : R) (p : MvPolynomial σ R)
    (q : MvPolynomial τ R) :
    tensorPolynomial (c • p) q = c • tensorPolynomial p q := by
  simp [tensorPolynomial, smul_mul_assoc]

@[simp] theorem tensorPolynomial_smul_right (c : R) (p : MvPolynomial σ R)
    (q : MvPolynomial τ R) :
    tensorPolynomial p (c • q) = c • tensorPolynomial p q := by
  simp [tensorPolynomial, mul_smul_comm]

@[simp] theorem tensorPolynomial_zero_left (q : MvPolynomial τ R) :
    tensorPolynomial (0 : MvPolynomial σ R) q = 0 := by simp [tensorPolynomial]

@[simp] theorem tensorPolynomial_zero_right (p : MvPolynomial σ R) :
    tensorPolynomial p (0 : MvPolynomial τ R) = 0 := by simp [tensorPolynomial]

theorem tensorPolynomial_monomial (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c e : R) :
    tensorPolynomial (monomial a c) (monomial b e) =
      monomial (Finsupp.sumElim a b) (c * e) := by
  simp only [tensorPolynomial, rename_monomial, monomial_mul, Finsupp.sumElim_eq_add]

lemma sumElim_zero_le_iff (d a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    Finsupp.sumElim d 0 ≤ Finsupp.sumElim a b ↔ d ≤ a := by
  constructor
  · intro h i
    exact h (Sum.inl i)
  · intro h i
    cases i with
    | inl i => exact h i
    | inr i => exact Nat.zero_le _

lemma sumElim_sub_left (d a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    Finsupp.sumElim a b - Finsupp.sumElim d 0 = Finsupp.sumElim (a - d) b := by
  ext i
  cases i <;> simp [Finsupp.sumElim_apply]

/-- A divided-power monomial operator on the first group of variables leaves
the second factor unchanged. -/
theorem contractMonomial_tensor_left (d : σ →₀ ℕ)
    (p : MvPolynomial σ R) (q : MvPolynomial τ R) :
    contractMonomial (Finsupp.sumElim d 0) (tensorPolynomial p q) =
      tensorPolynomial (contractMonomial d p) q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p p' hp hp' => simp [hp, hp']
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | add q q' hq hq' => simp [hq, hq']
    | monomial b e =>
      rw [tensorPolynomial_monomial, contractMonomial_monomial,
        contractMonomial_monomial]
      simp only [sumElim_zero_le_iff, sumElim_sub_left]
      split_ifs <;> simp [tensorPolynomial_monomial]

/-- The corresponding identity for every polynomial operator. -/
theorem dividedAction_tensor_left (f p : MvPolynomial σ R) (q : MvPolynomial τ R) :
    dividedAction (MvPolynomial.rename Sum.inl f) (tensorPolynomial p q) =
      tensorPolynomial (dividedAction f p) q := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial d c =>
    have hd : Finsupp.mapDomain (Sum.inl : σ → σ ⊕ τ) d = Finsupp.sumElim d 0 := by
      simp [Finsupp.sumElim_eq_add]
    simp only [rename_monomial, dividedAction_monomial, LinearMap.smul_apply,
      hd, contractMonomial_tensor_left, tensorPolynomial_smul_left]

/-- Contraction transports through a bijection of variable sets. -/
theorem contractMonomial_rename_equiv (e : σ ≃ τ) (d : σ →₀ ℕ)
    (p : MvPolynomial σ R) :
    contractMonomial (d.mapDomain e) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (contractMonomial d p) := by
  classical
  apply MvPolynomial.ext
  intro m
  obtain ⟨r, rfl⟩ := Finsupp.mapDomain_surjective e.surjective m
  rw [coeff_contractMonomial, ← Finsupp.mapDomain_add,
    MvPolynomial.coeff_rename_mapDomain e e.injective,
    MvPolynomial.coeff_rename_mapDomain e e.injective, coeff_contractMonomial]

theorem dividedAction_rename_equiv (e : σ ≃ τ) (f p : MvPolynomial σ R) :
    dividedAction (MvPolynomial.rename e f) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (dividedAction f p) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial d c =>
    simp only [MvPolynomial.rename_monomial, dividedAction_monomial,
      LinearMap.smul_apply, contractMonomial_rename_equiv, map_smul]

theorem rename_tensorPolynomial_swap (p : MvPolynomial σ R) (q : MvPolynomial τ R) :
    MvPolynomial.rename (Equiv.sumComm σ τ) (tensorPolynomial p q) =
      tensorPolynomial q p := by
  simp only [tensorPolynomial, map_mul, MvPolynomial.rename_rename]
  exact mul_comm _ _

theorem dividedAction_tensor_right (f q : MvPolynomial τ R) (p : MvPolynomial σ R) :
    dividedAction (MvPolynomial.rename Sum.inr f) (tensorPolynomial p q) =
      tensorPolynomial p (dividedAction f q) := by
  have h := dividedAction_rename_equiv (Equiv.sumComm τ σ)
    (MvPolynomial.rename Sum.inl f) (tensorPolynomial q p)
  rw [dividedAction_tensor_left, rename_tensorPolynomial_swap,
    rename_tensorPolynomial_swap] at h
  simpa only [MvPolynomial.rename_rename, Function.comp_def, Equiv.sumComm_apply,
    Sum.swap_inl] using h

/-- A factorization on a subset and its complement gives the exact local
operator identity, without a division or characteristic restriction. -/
theorem dividedAction_disjoint_factor {κ : Type*} (C : κ → Prop) [DecidablePred C]
    (f p : MvPolynomial {i // C i} R) (q : MvPolynomial {i // ¬ C i} R) :
    dividedAction (MvPolynomial.rename Subtype.val f)
        (MvPolynomial.rename Subtype.val p * MvPolynomial.rename Subtype.val q) =
      MvPolynomial.rename Subtype.val (dividedAction f p) *
        MvPolynomial.rename Subtype.val q := by
  have h := dividedAction_rename_equiv (Equiv.sumCompl C)
    (MvPolynomial.rename Sum.inl f) (tensorPolynomial p q)
  rw [dividedAction_tensor_left] at h
  simpa only [tensorPolynomial, map_mul, MvPolynomial.rename_rename,
    Function.comp_def, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr] using h

/-- The factor-local action in arbitrary ambient variables. -/
theorem dividedAction_embedded_factor (e : σ ↪ τ)
    (f p : MvPolynomial σ R) (q : MvPolynomial τ R)
    (hq : ∀ i ∈ q.vars, i ∉ Set.range e) :
    dividedAction (MvPolynomial.rename e f) (MvPolynomial.rename e p * q) =
      MvPolynomial.rename e (dividedAction f p) * q := by
  classical
  let E : σ ≃ Set.range e := Equiv.ofInjective e e.injective
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q
    (Subtype.val : {i : τ // i ∉ Set.range e} → τ) Subtype.val_injective (by
      intro i hi
      exact ⟨⟨i, hq i hi⟩, rfl⟩)
  have h := dividedAction_disjoint_factor (fun i : τ => i ∈ Set.range e)
    (MvPolynomial.rename E f) (MvPolynomial.rename E p) q'
  rw [dividedAction_rename_equiv] at h
  simpa only [MvPolynomial.rename_rename, Function.comp_def, E,
    Equiv.ofInjective_apply, hq'] using h

/-- In particular, injective renaming preserves the actual contraction
operators on polynomials in those variables. -/
theorem dividedAction_rename_embedding (e : σ ↪ τ)
    (f p : MvPolynomial σ R) :
    dividedAction (MvPolynomial.rename e f) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (dividedAction f p) := by
  simpa using dividedAction_embedded_factor e f p (1 : MvPolynomial τ R)
    (by simp)

end HigherSpecht
end
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/ElementaryGenerating.lean -/



/-!
# Removing complete columns from elementary operators

If every positive elementary polynomial on each of several disjoint complete
blocks lies in an ideal, the generating product on their union is 1 modulo the
ideal.  The degree on the remaining variables gives the exact annihilation
bound used in Lemma 2.1.  This is an identity in a quotient polynomial ring,
valid integrally and over arbitrary commutative coefficient rings.
-/

noncomputable section

open Finset MvPolynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

def elementaryGenerating (Y : Finset (Fin n)) : Polynomial (PolynomialRing n R) :=
  ∏ i ∈ Y, (1 + Polynomial.C (MvPolynomial.X i) * Polynomial.X)

theorem elementaryGenerating_coeff (Y : Finset (Fin n)) (d : ℕ) :
    (elementaryGenerating (R := R) Y).coeff d = elementaryOn Y d := by
  classical
  rw [elementaryGenerating, Finset.prod_one_add, Polynomial.finsetSum_coeff]
  unfold elementaryOn
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  have hp : (∏ i ∈ A, (Polynomial.C (MvPolynomial.X i : PolynomialRing n R) *
      Polynomial.X)) = Polynomial.C (∏ i ∈ A, (MvPolynomial.X i : PolynomialRing n R)) *
        Polynomial.X ^ A.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]
  rw [hp, Polynomial.coeff_C_mul_X_pow]
  by_cases hcard : A.card = d
  · simp [hcard]
  · simp [hcard, Ne.symm hcard]

theorem elementaryGenerating_union (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    elementaryGenerating (R := R) (A ∪ B) =
      elementaryGenerating A * elementaryGenerating B := by
  exact Finset.prod_union hAB

theorem elementaryGenerating_biUnion {ι : Type*} (s : Finset ι)
    (C : ι → Finset (Fin n)) (hC : (s : Set ι).PairwiseDisjoint C) :
    elementaryGenerating (R := R) (s.biUnion C) = ∏ i ∈ s, elementaryGenerating (C i) := by
  exact Finset.prod_biUnion hC

theorem map_elementaryGenerating_eq_one
    (I : Ideal (PolynomialRing n R)) (C : Finset (Fin n))
    (hC : ∀ d : ℕ, 0 < d → elementaryOn C d ∈ I) :
    Polynomial.map (Ideal.Quotient.mk I) (elementaryGenerating C) = 1 := by
  ext d
  rw [Polynomial.coeff_map, elementaryGenerating_coeff]
  cases d with
  | zero => simp
  | succ d =>
    simpa only [Polynomial.coeff_one, Nat.succ_ne_zero, if_false] using
      Ideal.Quotient.eq_zero_iff_mem.mpr (hC _ (Nat.succ_pos _))

theorem map_elementaryGenerating_biUnion_eq_one
    (I : Ideal (PolynomialRing n R)) {ι : Type*} (s : Finset ι)
    (C : ι → Finset (Fin n)) (hC : (s : Set ι).PairwiseDisjoint C)
    (hmem : ∀ i ∈ s, ∀ d : ℕ, 0 < d → elementaryOn (C i) d ∈ I) :
    Polynomial.map (Ideal.Quotient.mk I) (elementaryGenerating (s.biUnion C)) = 1 := by
  rw [elementaryGenerating_biUnion s C hC, Polynomial.map_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact map_elementaryGenerating_eq_one I (C i) (hmem i hi)

/-- The exact degree bound after deleting complete blocks. -/
theorem elementaryOn_mem_of_disjoint_complete_blocks
    (I : Ideal (PolynomialRing n R)) {ι : Type*} (s : Finset ι)
    (C : ι → Finset (Fin n)) (hC : (s : Set ι).PairwiseDisjoint C)
    (hmem : ∀ i ∈ s, ∀ d : ℕ, 0 < d → elementaryOn (C i) d ∈ I)
    (Y : Finset (Fin n)) (hY : ∀ i ∈ s, C i ⊆ Y) {d : ℕ}
    (hd : Y.card - (∑ i ∈ s, (C i).card) < d) :
    elementaryOn Y d ∈ I := by
  classical
  let U := s.biUnion C
  have hUY : U ⊆ Y := Finset.biUnion_subset.mpr hY
  have hdisj : Disjoint U (Y \ U) := Finset.disjoint_sdiff
  have hunion : U ∪ (Y \ U) = Y := Finset.union_sdiff_of_subset hUY
  have hprod : Polynomial.map (Ideal.Quotient.mk I) (elementaryGenerating Y) =
      Polynomial.map (Ideal.Quotient.mk I) (elementaryGenerating (Y \ U)) := by
    conv_lhs => rw [← hunion, elementaryGenerating_union U (Y \ U) hdisj]
    rw [Polynomial.map_mul]
    rw [map_elementaryGenerating_biUnion_eq_one I s C hC hmem, one_mul]
  have hcoeff := congrArg (fun p : Polynomial (PolynomialRing n R ⧸ I) => p.coeff d) hprod
  simp only [Polynomial.coeff_map, elementaryGenerating_coeff] at hcoeff
  have hcard : (Y \ U).card < d := by
    rw [Finset.card_sdiff_of_subset hUY, show U.card = ∑ i ∈ s, (C i).card from
      Finset.card_biUnion hC]
    exact hd
  rw [elementaryOn_eq_zero_of_card_lt hcard, map_zero] at hcoeff
  exact Ideal.Quotient.eq_zero_iff_mem.mp hcoeff

variable {σ : Type*}

/-- The actual annihilator of a single divided-power polynomial is an ideal,
because the polynomial contraction operators commute. -/
def contractionAnnihilator (w : MvPolynomial σ R) : Ideal (MvPolynomial σ R) where
  carrier := {f | dividedAction f w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change dividedAction f w = 0 at hf
    change dividedAction g w = 0 at hg
    change dividedAction (f + g) w = 0
    simp [hf, hg]
  smul_mem' := by
    intro f g hg
    change dividedAction (f * g) w = 0
    rw [dividedAction_mul, hg, map_zero]

@[simp] theorem mem_contractionAnnihilator (w f : MvPolynomial σ R) :
    f ∈ contractionAnnihilator w ↔ dividedAction f w = 0 := Iff.rfl

theorem le_contractionAnnihilator_iff (I : Ideal (MvPolynomial σ R))
    (w : MvPolynomial σ R) : I ≤ contractionAnnihilator w ↔ w ∈ dividedHarmonics I := Iff.rfl

end HigherSpecht
end
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/CompleteColumns.lean -/



/-!
# The complete-column count in the annihilation bound

The labels of an injective filling are genuinely disjoint between columns.
Each incomplete column consumes a different label in the complement of Y.
Sorting these columns bounds their total size by the largest column lengths.
-/

noncomputable section

open Finset TauCeti

namespace HigherSpecht

lemma fin_val_le_strictMono (k : ℕ) {f : Fin k → ℕ} (hf : StrictMono f) (i : Fin k) :
    i.val ≤ f i := by
  have h := Finset.card_le_card_of_injOn f
    (s := Finset.Iio i) (t := Finset.range (f i))
    (fun j hj => Finset.mem_range.mpr (hf (Finset.mem_Iio.mp hj))) hf.injective.injOn
  simpa only [Fin.card_Iio, Finset.card_range] using h

/-- A nonincreasing sequence has its largest cardinality-bounded subsum in an
initial interval.  The index set can contain arbitrarily large indices. -/
theorem sum_antitone_finset_le_range (c : ℕ → ℕ) (hc : Antitone c)
    (s : Finset ℕ) {h : ℕ} (hs : s.card ≤ h) :
    ∑ j ∈ s, c j ≤ ∑ j ∈ Finset.range h, c j := by
  classical
  let e := s.orderEmbOfFin rfl
  calc
    ∑ j ∈ s, c j = ∑ i : Fin s.card, c (e i) := by
      conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl]
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ i : Fin s.card, c i.val := by
      apply Finset.sum_le_sum
      intro i hi
      exact hc (fin_val_le_strictMono _ e.strictMono i)
    _ = ∑ j ∈ Finset.range s.card, c j := Fin.sum_univ_eq_sum_range _ _
    _ ≤ ∑ j ∈ Finset.range h, c j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hs)
        (fun _ _ _ => Nat.zero_le _)

/-- No more than the number of missing labels of Y can be met by distinct
pairwise-disjoint blocks which are not wholly contained in Y. -/
theorem card_incomplete_blocks_le {n : ℕ} (s : Finset ℕ)
    (C : ℕ → Finset (Fin n)) (hC : (s : Set ℕ).PairwiseDisjoint C)
    (Y : Finset (Fin n)) :
    (s.filter fun j => ¬ C j ⊆ Y).card ≤ n - Y.card := by
  classical
  let D := s.filter fun j => ¬ C j ⊆ Y
  have hex : ∀ j : D, ∃ i : Fin n, i ∈ C j.val ∧ i ∉ Y := by
    intro j
    exact Finset.not_subset.mp (Finset.mem_filter.mp j.property).2
  choose f hf hfY using hex
  let g : D → ↥(Yᶜ) := fun j => ⟨f j, Finset.mem_compl.mpr (hfY j)⟩
  have hg : Function.Injective g := by
    intro j l heq
    apply Subtype.ext
    by_contra hne
    have hdisj := hC (Finset.mem_filter.mp j.property).1
      (Finset.mem_filter.mp l.property).1 hne
    have hval : f j = f l := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp hdisj (hval ▸ hf j) (hf l)
  have hcard := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin] using hcard

/-- The exact conjugate-tail bound, padded to n columns. -/
theorem complete_blocks_card_ge_conjugateTail {n : ℕ} (μ : YoungDiagram)
    (C : ℕ → Finset (Fin n))
    (hC : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint C)
    (hcard : ∀ j < n, (C j).card = μ.colLen j) (Y : Finset (Fin n)) :
    conjugateTail n μ Y.card ≤
      ∑ j ∈ (Finset.range n).filter (fun j => C j ⊆ Y), (C j).card := by
  classical
  let D := (Finset.range n).filter fun j => ¬ C j ⊆ Y
  have hD : D.card ≤ n - Y.card := card_incomplete_blocks_le _ C hC Y
  have hbad := sum_antitone_finset_le_range μ.colLen
    (fun i j hij => μ.colLen_anti i j hij) D hD
  have hsplit : (∑ j ∈ Finset.range n, μ.colLen j) =
      (∑ j ∈ (Finset.range n).filter (fun j => C j ⊆ Y), μ.colLen j) +
        ∑ j ∈ D, μ.colLen j := by
    symm
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hinterval : (∑ j ∈ Finset.range (n - Y.card), μ.colLen j) +
      conjugateTail n μ Y.card = ∑ j ∈ Finset.range n, μ.colLen j := by
    exact Finset.sum_range_add_sum_Ico _ (Nat.sub_le n Y.card)
  have hcomplete : (∑ j ∈ (Finset.range n).filter (fun j => C j ⊆ Y), (C j).card) =
      ∑ j ∈ (Finset.range n).filter (fun j => C j ⊆ Y), μ.colLen j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hcard j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  rw [hcomplete]
  omega

/-- A column's labels under an arbitrary injective filling of the diagram. -/
def columnLabels {n : ℕ} {μ : YoungDiagram} (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    Finset (Fin n) :=
  ((Finset.univ : Finset ↥μ.cells).filter fun c => c.val.2 = j).map U

@[simp] theorem mem_columnLabels {n : ℕ} {μ : YoungDiagram}
    (U : ↥μ.cells ↪ Fin n) (j : ℕ) (i : Fin n) :
    i ∈ columnLabels U j ↔ ∃ c : ↥μ.cells, c.val.2 = j ∧ U c = i := by
  simp [columnLabels]

/-- Cells in column j are indexed by their actual row, from zero up to its
height.  This does not require any ordering hypothesis on the filling. -/
def columnCellsEquiv (μ : YoungDiagram) (j : ℕ) :
    {c : ↥μ.cells // c.val.2 = j} ≃ Fin (μ.colLen j) where
  toFun c := ⟨c.val.val.1, by
    have hc := c.val.property
    simpa only [c.property] using YoungDiagram.mem_iff_lt_colLen.mp hc⟩
  invFun i := ⟨⟨(i.val, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩, rfl⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl c.property.symm
  right_inv i := Fin.ext rfl

theorem card_columnLabels {n : ℕ} {μ : YoungDiagram} (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    (columnLabels U j).card = μ.colLen j := by
  rw [columnLabels, Finset.card_map, ← Fintype.card_subtype]
  exact (Fintype.card_congr (columnCellsEquiv μ j)).trans (Fintype.card_fin _)

theorem columnLabels_pairwiseDisjoint {n : ℕ} {μ : YoungDiagram}
    (U : ↥μ.cells ↪ Fin n) : Set.PairwiseDisjoint Set.univ (columnLabels U) := by
  intro j hj l hl hne
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨c, hc, hci⟩ := (mem_columnLabels U j i).mp hi
  obtain ⟨d, hd, hdi⟩ := (mem_columnLabels U l i).mp hj
  have hcd : c = d := U.injective (hci.trans hdi.symm)
  exact hne (hc.symm.trans ((congrArg (fun c : ↥μ.cells => c.val.2) hcd).trans hd))

/-- The precise combinatorial inequality appearing in Lemma 2.1. -/
theorem columnLabels_complete_card_ge_tail {n : ℕ} {μ : YoungDiagram}
    (U : ↥μ.cells ↪ Fin n) (Y : Finset (Fin n)) :
    conjugateTail n μ Y.card ≤
      ∑ j ∈ (Finset.range n).filter (fun j => columnLabels U j ⊆ Y),
        (columnLabels U j).card := by
  apply complete_blocks_card_ge_conjugateTail μ (columnLabels U)
  · exact (columnLabels_pairwiseDisjoint U).subset (Set.subset_univ _)
  · intro j hj
    exact card_columnLabels U j

end HigherSpecht
end
end CanonicalSource9

section CanonicalSource10
/- Source: HigherSpecht/ColumnWitnesses.lean -/



/-!
# Actual injective-tableau witnesses

The witness is the product of the column alternants, embedded using the given
injective filling, and the specified outside powers.  Complete-column
annihilation is derived from the integral single-column identity and the
factor-local divided-power action, then combined with the conjugate-tail count.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {μ : YoungDiagram}

def columnEmbedding (U : ↥μ.cells ↪ Fin n) (j : ℕ) : Fin (μ.colLen j) ↪ Fin n where
  toFun i := U ⟨(i.val, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩
  inj' i l h := by
    have hi := congrArg (fun c : ↥μ.cells => c.val.1) (U.injective h)
    exact Fin.ext hi

theorem map_univ_columnEmbedding (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    (Finset.univ.map (columnEmbedding U j)) = columnLabels U j := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, mem_columnLabels]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨(r.val, j), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩, rfl, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    let r : Fin (μ.colLen j) := ⟨c.val.1, by
      rw [← hc]
      exact YoungDiagram.mem_iff_lt_colLen.mp c.property⟩
    refine ⟨r, ?_⟩
    apply congrArg U
    apply Subtype.ext
    exact Prod.ext rfl hc.symm

theorem range_columnEmbedding (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    Set.range (columnEmbedding U j) = ↑(columnLabels U j) := by
  rw [← map_univ_columnEmbedding]
  ext i
  simp

def columnAlternant (U : ↥μ.cells ↪ Fin n) (j : ℕ) : PolynomialRing n R :=
  MvPolynomial.rename (columnEmbedding U j)
    (TauCeti.alternant (Fin (μ.colLen j)) R fun i => i.val)

def fillingLabels (U : ↥μ.cells ↪ Fin n) : Finset (Fin n) := Finset.univ.map U

def outsidePower (U : ↥μ.cells ↪ Fin n) (s : ℕ) : PolynomialRing n R :=
  ∏ i ∈ (fillingLabels U)ᶜ, (MvPolynomial.X i) ^ (s - 1)

/-- The manuscript's column product with its outside exponents.  The use of
n padded columns is harmless because zero-height alternants are 1. -/
def columnWitness (U : ↥μ.cells ↪ Fin n) (s : ℕ) : PolynomialRing n R :=
  (∏ j ∈ Finset.range n, columnAlternant U j) * outsidePower U s

theorem rename_esymm_embedding {k : ℕ} (e : Fin k ↪ Fin n) (d : ℕ) :
    MvPolynomial.rename e (MvPolynomial.esymm (Fin k) R d) =
      elementaryOn (Finset.univ.map e) d := by
  classical
  simp only [MvPolynomial.esymm, elementaryOn, map_sum, map_prod, rename_X,
    Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro A hA
  change (∏ i ∈ A, (X (e i) : PolynomialRing n R)) = ∏ i ∈ A.map e, X i
  rw [Finset.prod_map]

theorem vars_columnAlternant_subset (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    (columnAlternant (R := R) U j).vars ⊆ columnLabels U j := by
  intro i hi
  obtain ⟨r, hr, rfl⟩ := MvPolynomial.mem_vars_rename _ _ hi
  rw [← map_univ_columnEmbedding]
  exact Finset.mem_map.mpr ⟨r, Finset.mem_univ _, rfl⟩

theorem columnLabels_subset_fillingLabels (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    columnLabels U j ⊆ fillingLabels U := by
  intro i hi
  obtain ⟨c, hc, rfl⟩ := (mem_columnLabels U j i).mp hi
  exact Finset.mem_map.mpr ⟨c, Finset.mem_univ _, rfl⟩

theorem vars_outsidePower_subset [Nontrivial R] (U : ↥μ.cells ↪ Fin n) (s : ℕ) :
    (outsidePower (R := R) U s).vars ⊆ (fillingLabels U)ᶜ := by
  intro i hi
  obtain ⟨l, hl, hil⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_prod _ hi)
  have h := MvPolynomial.vars_pow (X l : PolynomialRing n R) (s - 1) hil
  rw [MvPolynomial.vars_X, Finset.mem_singleton] at h
  exact h.symm ▸ hl

/-- Every positive elementary operator on a complete column annihilates the
entire witness, including all the other columns and outside powers. -/
theorem elementaryOn_column_contract_witness (U : ↥μ.cells ↪ Fin n) (s j d : ℕ)
    (hj : j < n) (hd : 0 < d) :
    dividedAction (elementaryOn (columnLabels U j) d)
      (columnWitness (R := R) U s) = 0 := by
  classical
  nontriviality R
  let q : PolynomialRing n R :=
    (∏ l ∈ (Finset.range n).erase j, columnAlternant U l) * outsidePower U s
  have hw : columnWitness (R := R) U s = columnAlternant U j * q := by
    unfold columnWitness q
    rw [← Finset.mul_prod_erase (Finset.range n) (columnAlternant U)
      (Finset.mem_range.mpr hj), mul_assoc]
  have hq : ∀ i ∈ q.vars, i ∉ Set.range (columnEmbedding U j) := by
    intro i hi
    rw [range_columnEmbedding]
    have hm := MvPolynomial.vars_mul _ _ hi
    rcases Finset.mem_union.mp hm with hi | hi
    · obtain ⟨l, hl, hil⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_prod _ hi)
      have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
      exact fun hij => Finset.disjoint_left.mp
        (columnLabels_pairwiseDisjoint U (Set.mem_univ j) (Set.mem_univ l) hlj.symm)
        hij (vars_columnAlternant_subset U l hil)
    · have hout := vars_outsidePower_subset U s hi
      exact fun hij => Finset.mem_compl.mp hout (columnLabels_subset_fillingLabels U j hij)
  have helem : elementaryOn (R := R) (columnLabels U j) d =
      MvPolynomial.rename (columnEmbedding U j)
        (MvPolynomial.esymm (Fin (μ.colLen j)) R d) := by
    rw [rename_esymm_embedding, map_univ_columnEmbedding]
  rw [hw, helem, columnAlternant, dividedAction_embedded_factor _ _ _ _ hq,
    elementary_contract_staircase_alternant _ _ hd, map_zero, zero_mul]

/-- The full elementary assertion of Lemma 2.1 over every commutative
coefficient ring, with the integer threshold exactly as printed. -/
theorem elementary_contract_columnWitness (U : ↥μ.cells ↪ Fin n) (s : ℕ)
    (Y : Finset (Fin n)) {d : ℕ} (hd : 0 < d)
    (hthreshold : (Y.card : ℤ) - (conjugateTail n μ Y.card : ℤ) < (d : ℤ)) :
    dividedAction (elementaryOn (R := R) Y d) (columnWitness U s) = 0 := by
  classical
  let J := (Finset.range n).filter fun j => columnLabels U j ⊆ Y
  have hC : (J : Set ℕ).PairwiseDisjoint (columnLabels U) :=
    (columnLabels_pairwiseDisjoint U).subset (Set.subset_univ _)
  have hmem : ∀ j ∈ J, ∀ e : ℕ, 0 < e →
      elementaryOn (R := R) (columnLabels U j) e ∈
        contractionAnnihilator (columnWitness U s) := by
    intro j hj e he
    exact elementaryOn_column_contract_witness U s j e
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) he
  have htail := columnLabels_complete_card_ge_tail U Y
  have hdegree : Y.card - (∑ j ∈ J, (columnLabels U j).card) < d := by
    dsimp [J] at *
    omega
  exact elementaryOn_mem_of_disjoint_complete_blocks
    (contractionAnnihilator (columnWitness U s)) J (columnLabels U) hC hmem Y
    (fun j hj => (Finset.mem_filter.mp hj).2) hdegree

/-- Inverse-system membership is proved for the actual ideal of all the
specified elementary generators. -/
theorem columnWitness_mem_untruncatedHarmonics (U : ↥μ.cells ↪ Fin n) (s : ℕ) :
    columnWitness (R := R) U s ∈ dividedHarmonics (untruncatedIdeal R n μ) := by
  rw [untruncatedIdeal, mem_dividedHarmonics_span_iff]
  rintro f ⟨Y, d, hd, hcard, hthreshold, rfl⟩
  exact elementary_contract_columnWitness U s Y hd hthreshold

lemma degreeOf_eq_zero_of_notMem_vars {p : PolynomialRing n R} {i : Fin n}
    (hi : i ∉ p.vars) : p.degreeOf i = 0 := by
  by_contra h
  exact hi (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)

theorem degreeOf_columnAlternant_le (U : ↥μ.cells ↪ Fin n) {s : ℕ}
    (hs : μ.colLen 0 ≤ s) (j : ℕ) (i : Fin n) :
    (columnAlternant (R := R) U j).degreeOf i ≤ s - 1 := by
  classical
  by_cases hi : i ∈ columnLabels U j
  · have hiRange : i ∈ Set.range (columnEmbedding U j) := by
      rw [range_columnEmbedding]
      exact hi
    obtain ⟨r, rfl⟩ := hiRange
    rw [columnAlternant, MvPolynomial.degreeOf_rename_of_injective
      (columnEmbedding U j).injective]
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro a ha
    have hn : (TauCeti.alternant (Fin (μ.colLen j)) R fun k => k.val).coeff a ≠ 0 :=
      MvPolynomial.mem_support_iff.mp ha
    have hal : a r < μ.colLen j := by
      by_contra h
      exact hn (coeff_staircase_alternant_eq_zero_of_large a r (Nat.le_of_not_gt h))
    have hj := (μ.colLen_anti 0 j (Nat.zero_le _)).trans hs
    omega
  · rw [degreeOf_eq_zero_of_notMem_vars (fun h => hi (vars_columnAlternant_subset U j h))]
    exact Nat.zero_le _

theorem degreeOf_outsidePower_le [Nontrivial R]
    (U : ↥μ.cells ↪ Fin n) (s : ℕ) (i : Fin n) :
    (outsidePower (R := R) U s).degreeOf i ≤ s - 1 := by
  classical
  calc
    (outsidePower (R := R) U s).degreeOf i ≤
        ∑ j ∈ (fillingLabels U)ᶜ, ((X j : PolynomialRing n R) ^ (s - 1)).degreeOf i :=
      MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ ∑ j : Fin n, ((X j : PolynomialRing n R) ^ (s - 1)).degreeOf i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = s - 1 := by
      rw [Finset.sum_eq_single i]
      · exact MvPolynomial.degreeOf_X_self_pow _ _
      · intro j hj hji
        exact MvPolynomial.degreeOf_X_pow_of_ne _ hji.symm
      · simp

/-- Every exponent of the actual witness is at most s-1. -/
theorem degreeOf_columnWitness_le [Nontrivial R]
    (U : ↥μ.cells ↪ Fin n) {s : ℕ} (hs : μ.colLen 0 ≤ s) (i : Fin n) :
    (columnWitness (R := R) U s).degreeOf i ≤ s - 1 := by
  classical
  have hprod := MvPolynomial.degreeOf_prod_le i (Finset.range n) (columnAlternant (R := R) U)
  have hmul := MvPolynomial.degreeOf_mul_le i
    (∏ j ∈ Finset.range n, columnAlternant (R := R) U j) (outsidePower U s)
  by_cases hex : ∃ j < n, i ∈ columnLabels U j
  · obtain ⟨j, hj, hij⟩ := hex
    have hout : (outsidePower (R := R) U s).degreeOf i = 0 := by
      apply degreeOf_eq_zero_of_notMem_vars
      intro hi
      exact Finset.mem_compl.mp (vars_outsidePower_subset U s hi)
        (columnLabels_subset_fillingLabels U j hij)
    have hsum : (∑ l ∈ Finset.range n, (columnAlternant (R := R) U l).degreeOf i) =
        (columnAlternant (R := R) U j).degreeOf i := by
      apply Finset.sum_eq_single j
      · intro l hl hlj
        apply degreeOf_eq_zero_of_notMem_vars
        intro hi
        exact Finset.disjoint_left.mp
          (columnLabels_pairwiseDisjoint U (Set.mem_univ j) (Set.mem_univ l) hlj.symm)
          hij (vars_columnAlternant_subset U l hi)
      · exact fun h => (h (Finset.mem_range.mpr hj)).elim
    rw [hsum] at hprod
    rw [hout, add_zero] at hmul
    exact hmul.trans (hprod.trans (degreeOf_columnAlternant_le U hs j i))
  · have hsum : (∑ l ∈ Finset.range n, (columnAlternant (R := R) U l).degreeOf i) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      apply degreeOf_eq_zero_of_notMem_vars
      intro hi
      exact hex ⟨l, Finset.mem_range.mp hl, vars_columnAlternant_subset U l hi⟩
    rw [hsum] at hprod
    have hzero := Nat.eq_zero_of_le_zero hprod
    rw [hzero, zero_add] at hmul
    exact hmul.trans (degreeOf_outsidePower_le U s i)

/-- The power assertion of Lemma 2.1, again for the genuine divided-power
witness over every commutative ring. -/
theorem power_contract_columnWitness (U : ↥μ.cells ↪ Fin n) {s : ℕ}
    (hs0 : 0 < s) (hs : μ.colLen 0 ≤ s) (i : Fin n) :
    dividedAction ((X i : PolynomialRing n R) ^ s) (columnWitness U s) = 0 := by
  classical
  nontriviality R
  rw [MvPolynomial.X_pow_eq_monomial, dividedAction_monomial, one_smul]
  apply MvPolynomial.ext
  intro a
  rw [coeff_contractMonomial]
  change (columnWitness (R := R) U s).coeff (a + Finsupp.single i s) = 0
  apply MvPolynomial.notMem_support_iff.mp
  apply MvPolynomial.notMem_support_of_degreeOf_lt i
  have hdeg := degreeOf_columnWitness_le (R := R) U hs i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  omega

/-- Lemma 2.1: all generators of the specified Griffin ideal annihilate the
column witness, with its full outside factors and the exact shape threshold. -/
theorem columnWitness_mem_griffinHarmonics (U : ↥μ.cells ↪ Fin n) {s : ℕ}
    (hs0 : 0 < s) (hs : μ.colLen 0 ≤ s) :
    columnWitness (R := R) U s ∈ dividedHarmonics (griffinIdeal R n μ s) := by
  rw [griffinIdeal, dividedHarmonics_sup]
  refine ⟨columnWitness_mem_untruncatedHarmonics U s, ?_⟩
  change columnWitness (R := R) U s ∈ dividedHarmonics (powerIdeal R n s)
  rw [powerIdeal]
  apply (mem_dividedHarmonics_span_iff _ _).mpr
  rintro f ⟨i, rfl⟩
  exact power_contract_columnWitness U hs0 hs i

end HigherSpecht
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/CompletedWitness.lean -/



/-!
# The filling and rejection counts from a complete insertion

The filling is extracted from the actual accepted-token list.  Thus its row
number is the original input plus the actual number of rejections.  The
cyclic scan invariant supplies precisely the two order properties required
for the coefficient rearrangement argument.
-/

noncomputable section

open Finset TauCeti Function

namespace HigherSpecht

variable {n : ℕ}

private theorem injective_get_map_of_nodup {α β : Type*} (l : List α) (f : α → β)
    (h : (l.map f).Nodup) : Function.Injective (fun i : Fin l.length => f (l.get i)) := by
  intro i j hij
  have heq : (l.map f).get ⟨i.val, by simpa using i.isLt⟩ =
      (l.map f).get ⟨j.val, by simpa using j.isLt⟩ := by
    simpa only [List.get_eq_getElem, List.getElem_map] using hij
  exact Fin.ext (congrArg (fun k : Fin (l.map f).length => k.val)
    (h.injective_get heq))

structure CompleteInsertion (a : Fin n → ℕ) where
  state : LabeledCatState n
  invariant : LabeledInvariant a state
  pending_nil : state.pending = []

namespace CompleteInsertion

variable {a : Fin n → ℕ} (C : CompleteInsertion a)

abbrev Index := Fin C.state.accepted.length

def token (i : C.Index) : CyclingToken n := (C.state.accepted.get i).1

def cell (i : C.Index) : ↥C.state.shape.cells :=
  ⟨(C.state.accepted.get i).2, by
    rw [← C.invariant.cells]
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨C.state.accepted.get i, List.get_mem _ _, rfl⟩)⟩

theorem position_bijective : Function.Bijective (fun i : C.Index => (C.token i).position) := by
  have hperm : (C.state.accepted.map (fun z => z.1.position)).Perm (List.finRange n) := by
    simpa only [List.map_map, Function.comp_def] using
      C.invariant.complete_positions C.pending_nil
  constructor
  · exact injective_get_map_of_nodup C.state.accepted (fun z => z.1.position)
      (hperm.nodup_iff.mpr (List.nodup_finRange n))
  · intro j
    have hj : j ∈ C.state.accepted.map (fun z => z.1.position) :=
      hperm.mem_iff.mpr (List.mem_finRange j)
    obtain ⟨z, hz, hzj⟩ := List.mem_map.mp hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
    refine ⟨i, ?_⟩
    change (C.state.accepted.get i).1.position = j
    rw [hi, hzj]

theorem cell_bijective : Function.Bijective C.cell := by
  constructor
  · intro i j hij
    apply injective_get_map_of_nodup C.state.accepted Prod.snd C.invariant.distinctCells
    exact congrArg Subtype.val hij
  · intro c
    have hc : c.val ∈ C.state.accepted.map Prod.snd := by
      apply List.mem_toFinset.mp
      rw [C.invariant.cells]
      exact c.property
    obtain ⟨z, hz, hzc⟩ := List.mem_map.mp hc
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
    refine ⟨i, Subtype.ext ?_⟩
    change (C.state.accepted.get i).2 = c.val
    rw [hi, hzc]

def positionEquiv : C.Index ≃ Fin n := Equiv.ofBijective _ C.position_bijective

def cellEquiv : C.Index ≃ ↥C.state.shape.cells := Equiv.ofBijective _ C.cell_bijective

/-- The actual accepted cell is filled by its original scan position. -/
def filling : ↥C.state.shape.cells ≃ Fin n := C.cellEquiv.symm.trans C.positionEquiv

def rejection (j : Fin n) : ℕ := (C.token (C.positionEquiv.symm j)).round

def row (j : Fin n) : ℕ := (C.filling.symm j).val.1

def column (j : Fin n) : ℕ := (C.filling.symm j).val.2

@[simp] theorem positionEquiv_apply (i : C.Index) : C.positionEquiv i = (C.token i).position := rfl

@[simp] theorem cellEquiv_apply (i : C.Index) : C.cellEquiv i = C.cell i := rfl

@[simp] theorem filling_cell (i : C.Index) : C.filling (C.cell i) = (C.token i).position := by
  change C.positionEquiv (C.cellEquiv.symm (C.cellEquiv i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem filling_symm_position (i : C.Index) :
    C.filling.symm (C.token i).position = C.cell i := by
  rw [← C.filling_cell]
  exact C.filling.symm_apply_apply _

@[simp] theorem rejection_position (i : C.Index) :
    C.rejection (C.token i).position = (C.token i).round := by
  change (C.token (C.positionEquiv.symm (C.positionEquiv i))).round = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem row_position (i : C.Index) :
    C.row (C.token i).position = (C.cell i).val.1 := by
  simp only [row, filling_symm_position]

@[simp] theorem column_position (i : C.Index) :
    C.column (C.token i).position = (C.cell i).val.2 := by
  simp only [column, filling_symm_position]

theorem row_eq_input_add_rejection (j : Fin n) : C.row j = a j + C.rejection j := by
  obtain ⟨i, rfl⟩ := C.position_bijective.surjective j
  rw [row_position, rejection_position]
  exact C.invariant.rowValue _ (List.get_mem _ _)

theorem stamp_strictMono : StrictMono (fun i : C.Index => (C.token i).stamp) := by
  intro i j hij
  exact C.invariant.accepted_stamp_order.rel_get_of_lt hij

theorem index_lt_of_same_column_row_lt {i j : C.Index}
    (hcol : (C.cell i).val.2 = (C.cell j).val.2)
    (hrow : (C.cell i).val.1 < (C.cell j).val.1) : i < j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hij
  · subst j
    exact (lt_irrefl _ hrow).elim
  · have hrev := C.invariant.columnOrder.rel_get_of_lt hij hcol.symm
    exact (lt_asymm hrow hrev).elim

theorem rejection_le_of_same_column_row_le {i j : Fin n}
    (hcol : C.column i = C.column j) (hrow : C.row i ≤ C.row j) :
    C.rejection i ≤ C.rejection j := by
  obtain ⟨l, rfl⟩ := C.position_bijective.surjective i
  obtain ⟨k, rfl⟩ := C.position_bijective.surjective j
  simp only [column_position, row_position] at hcol hrow
  rw [rejection_position, rejection_position]
  rcases eq_or_lt_of_le hrow with hrow | hrow
  · have hc : C.cell l = C.cell k := Subtype.ext (Prod.ext hrow hcol)
    have hlk := C.cell_bijective.injective hc
    subst k
    exact le_rfl
  · exact CyclingToken.round_le_of_stamp_le
      (C.stamp_strictMono (C.index_lt_of_same_column_row_lt hcol hrow)).le

theorem position_lt_of_same_column_row_lt_rejection_eq {i j : Fin n}
    (hcol : C.column i = C.column j) (hrow : C.row i < C.row j)
    (hr : C.rejection i = C.rejection j) : i < j := by
  obtain ⟨l, rfl⟩ := C.position_bijective.surjective i
  obtain ⟨k, rfl⟩ := C.position_bijective.surjective j
  simp only [column_position, row_position] at hcol hrow
  simp only [rejection_position] at hr
  exact CyclingToken.position_lt_of_stamp_lt_round_eq
    (C.stamp_strictMono (C.index_lt_of_same_column_row_lt hcol hrow)) hr

theorem row_column_injective : Function.Injective (fun i => (C.row i, C.column i)) := by
  intro i j hij
  apply C.filling.symm.injective
  apply Subtype.ext
  exact hij

theorem column_row_injective (k : ℕ) :
    Function.Injective (fun i : {i // C.column i = k} => (C.row i : ℤ)) := by
  intro i j hij
  change (C.row i : ℤ) = (C.row j : ℤ) at hij
  apply Subtype.ext
  apply C.row_column_injective
  have hrow : C.row i = C.row j := by exact_mod_cast hij
  exact Prod.ext hrow (i.property.trans j.property.symm)

theorem column_row_rejection_monovary (k : ℕ) :
    Monovary (fun i : {i // C.column i = k} => (C.row i : ℤ))
      (fun i : {i // C.column i = k} => (C.rejection i : ℤ)) := by
  apply Monovary.symm
  intro i j hij
  change (C.row i : ℤ) < (C.row j : ℤ) at hij
  change (C.rejection i : ℤ) ≤ (C.rejection j : ℤ)
  have hrow : C.row i ≤ C.row j := by exact_mod_cast hij.le
  exact_mod_cast C.rejection_le_of_same_column_row_le
    (i.property.trans j.property.symm) hrow

/-- If the original scan visits columns in decreasing order, the original
column number decreases up each common-rejection part of a witness column. -/
theorem tied_originalColumn_monovary (originalColumn : Fin n → ℕ)
    (hscan : Antitone originalColumn) (k : ℕ × ℕ) :
    Monovary
      (fun i : {i // (C.column i, C.rejection i) = k} => (a i : ℤ))
      (fun i : {i // (C.column i, C.rejection i) = k} => -(originalColumn i : ℤ)) := by
  apply Monovary.symm
  intro i j hij
  change (a i : ℤ) < (a j : ℤ) at hij
  have heq := i.property.trans j.property.symm
  have hcol : C.column i = C.column j := congrArg Prod.fst heq
  have hr : C.rejection i = C.rejection j := congrArg Prod.snd heq
  have hrow : C.row i < C.row j := by
    rw [C.row_eq_input_add_rejection, C.row_eq_input_add_rejection, hr]
    exact Nat.add_lt_add_right (by exact_mod_cast hij) _
  have hpos := C.position_lt_of_same_column_row_lt_rejection_eq hcol hrow hr
  exact neg_le_neg (by exact_mod_cast hscan hpos.le)

/-- The rearrangement witness is derived from a complete actual trace.  The
only reading-order premise is the explicit order of its original columns. -/
theorem rearrangementWitness (originalColumn : Fin n → ℕ)
    (hscan : Antitone originalColumn) :
    RearrangementWitness C.column (fun i => (C.column i, C.rejection i))
      (fun i => (C.row i : ℤ)) (fun i => (C.rejection i : ℤ))
      (fun i => (a i : ℤ)) (fun i => (originalColumn i : ℤ)) := by
  refine ⟨?_, C.column_row_injective, C.column_row_rejection_monovary, ?_,
    C.tied_originalColumn_monovary originalColumn hscan⟩
  · intro i
    have h : (C.row i : ℤ) = (a i : ℤ) + (C.rejection i : ℤ) := by
      exact_mod_cast C.row_eq_input_add_rejection i
    omega
  · intro i j
    simp only [Prod.mk.injEq, Nat.cast_inj]

theorem shape_card : C.state.shape.card = n := by
  have h := Fintype.card_congr C.filling
  simpa only [Fintype.card_coe, Fintype.card_fin] using h

end CompleteInsertion

theorem exists_completeInsertion (a : Fin n → ℕ)
    (ha : CatAdmissible ⟨(List.ofFn a).reverse, ⊥⟩) :
    ∃ C : CompleteInsertion a, CatWordOutput (List.ofFn a).reverse C.state.shape := by
  obtain ⟨s, hs, hnil, hout⟩ := exists_complete_labeled_insertion a ha
  exact ⟨⟨s, hs, hnil⟩, hout⟩

end HigherSpecht
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/RowColumnGeometry.lean -/



/-!
# Row permutations and the exact column-weight equality case

For a filling increasing across rows, a row permutation can only lower its
column-weighted exponent sum.  Equality fixes the filling.  Combining this
with column permutations proves the support condition of the manuscript's
triangularity argument for the actual column-after-row Young operator.
-/

noncomputable section

open Finset Function Equiv MvPolynomial TauCeti
open TauCeti.YoungTableau

namespace HigherSpecht

variable {ι κ : Type*} [Fintype ι]

/-- Fiberwise rearrangement does not require the set of fiber names to be
finite: only the names actually attained by the finite source are used. -/
theorem fiber_squareNorm_sub_le_permuted (c : ι → κ) {a r : ι → ℤ}
    (h : ∀ j, Monovary (fun i : {i // c i = j} => a i)
      (fun i : {i // c i = j} => r i))
    (σ : Equiv.Perm ι) (hc : ∀ i, c (σ i) = c i) :
    squareNorm (fun i => a i - r i) ≤ squareNorm (fun i => a (σ i) - r i) := by
  classical
  letI : Fintype (Set.range c) := (Set.finite_range c).fintype
  let c' : ι → Set.range c := fun i => ⟨c i, ⟨i, rfl⟩⟩
  apply block_squareNorm_sub_le_permuted c' (a := a) (r := r)
  · intro j
    exact (h j.val).comp_right
      (fun i : {i // c' i = j} => ⟨i.val, congrArg Subtype.val i.property⟩)
  · intro i
    exact Subtype.ext (hc i)

theorem fiber_squareNorm_sub_eq_permuted_iff (c : ι → κ) {a r : ι → ℤ}
    (ha : ∀ j, Function.Injective (fun i : {i // c i = j} => a i))
    (h : ∀ j, Monovary (fun i : {i // c i = j} => a i)
      (fun i : {i // c i = j} => r i))
    (σ : Equiv.Perm ι) (hc : ∀ i, c (σ i) = c i) :
    squareNorm (fun i => a i - r i) = squareNorm (fun i => a (σ i) - r i) ↔
      r ∘ σ = r := by
  classical
  letI : Fintype (Set.range c) := (Set.finite_range c).fintype
  let c' : ι → Set.range c := fun i => ⟨c i, ⟨i, rfl⟩⟩
  apply block_squareNorm_sub_eq_permuted_iff c' (a := a) (r := r)
  · intro j i l hil
    have heq : (⟨i.val, congrArg Subtype.val i.property⟩ : {i // c i = j.val}) =
        ⟨l.val, congrArg Subtype.val l.property⟩ := ha j.val hil
    exact Subtype.ext (congrArg (fun x : {i // c i = j.val} => x.val) heq)
  · intro j
    exact (h j.val).comp_right
      (fun i : {i // c' i = j} => ⟨i.val, congrArg Subtype.val i.property⟩)
  · intro i
    exact Subtype.ext (hc i)

theorem columnWeight_comp_left (c b : ι → ℤ) (σ : Equiv.Perm ι) :
    columnWeight (c ∘ σ) b = columnWeight c (b ∘ σ.symm) := by
  unfold columnWeight
  have h := Equiv.sum_comp σ (fun i => c i * b (σ.symm i))
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h

theorem columnWeight_rowPermutation_le (row : ι → κ) (c b : ι → ℤ)
    (h : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => b i))
    (ρ : Equiv.Perm ι) (hr : ∀ i, row (ρ i) = row i) :
    columnWeight c (b ∘ ρ) ≤ columnWeight c b := by
  have hr' : ∀ i, row (ρ.symm i) = row i := fun i =>
    (hr (ρ.symm i)).symm.trans (congrArg row (Equiv.apply_symm_apply ρ i))
  have hn := fiber_squareNorm_sub_le_permuted row h ρ.symm hr'
  rw [squareNorm_sub, squareNorm_sub, squareNorm_permuted] at hn
  change squareNorm c + squareNorm b - 2 * columnWeight c b ≤
    squareNorm c + squareNorm b - 2 * columnWeight (c ∘ ρ.symm) b at hn
  rw [columnWeight_comp_left, Equiv.symm_symm] at hn
  linarith

theorem columnWeight_rowPermutation_eq_iff (row : ι → κ) (c b : ι → ℤ)
    (hc : ∀ j, Function.Injective (fun i : {i // row i = j} => c i))
    (h : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => b i))
    (ρ : Equiv.Perm ι) (hr : ∀ i, row (ρ i) = row i) :
    columnWeight c (b ∘ ρ) = columnWeight c b ↔ b ∘ ρ = b := by
  constructor
  · intro heq
    have hr' : ∀ i, row (ρ.symm i) = row i := fun i =>
      (hr (ρ.symm i)).symm.trans (congrArg row (Equiv.apply_symm_apply ρ i))
    have hn : squareNorm (fun i => c i - b i) =
        squareNorm (fun i => c (ρ.symm i) - b i) := by
      rw [squareNorm_sub, squareNorm_sub, squareNorm_permuted]
      change squareNorm c + squareNorm b - 2 * columnWeight c b =
        squareNorm c + squareNorm b - 2 * columnWeight (c ∘ ρ.symm) b
      rw [columnWeight_comp_left, Equiv.symm_symm, heq]
    have hb := (fiber_squareNorm_sub_eq_permuted_iff row hc h ρ.symm hr').mp hn
    funext i
    have hi := congrFun hb (ρ i)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hi.symm
  · rintro hρ
    rw [hρ]

/-- A polynomial-side monomial is obtained first by a row permutation and
then by a column permutation.  The following statement uses the actual
permutation composition, including its exact equality case. -/
theorem rowColumn_weight_le (row : ι → κ) (c b : ι → ℤ)
    (h : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => b i))
    (ρ σ : Equiv.Perm ι) (hr : ∀ i, row (ρ i) = row i)
    (hcσ : c ∘ σ = c) :
    columnWeight c ((b ∘ ρ) ∘ σ) ≤ columnWeight c b := by
  rw [columnWeight_comp_perm c (b ∘ ρ) σ hcσ]
  exact columnWeight_rowPermutation_le row c b h ρ hr

theorem rowColumn_weight_eq_imp_columnOrbit (row : ι → κ) (c b : ι → ℤ)
    (hc : ∀ j, Function.Injective (fun i : {i // row i = j} => c i))
    (h : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => b i))
    (ρ σ : Equiv.Perm ι) (hr : ∀ i, row (ρ i) = row i)
    (hcσ : c ∘ σ = c)
    (heq : columnWeight c ((b ∘ ρ) ∘ σ) = columnWeight c b) :
    (b ∘ ρ) ∘ σ = b ∘ σ := by
  rw [columnWeight_comp_perm c (b ∘ ρ) σ hcσ] at heq
  rw [(columnWeight_rowPermutation_eq_iff row c b hc h ρ hr).mp heq]

theorem colIndex_injective_on_row {μ : YoungDiagram} (T : YoungTableau μ) (j : ℕ) :
    Function.Injective (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ)) := by
  intro i l heq
  change (colIndex T i : ℤ) = (colIndex T l : ℤ) at heq
  apply Subtype.ext
  apply rowIndex_colIndex_injective T
  have hcol : colIndex T i = colIndex T l := by exact_mod_cast heq
  exact Prod.ext (i.property.trans l.property.symm) hcol

theorem rowIndex_injective_on_column {μ : YoungDiagram} (T : YoungTableau μ) (j : ℕ) :
    Function.Injective (fun i : {i // colIndex T i = j} => (rowIndex T i : ℤ)) := by
  intro i l heq
  change (rowIndex T i : ℤ) = (rowIndex T l : ℤ) at heq
  apply Subtype.ext
  apply rowIndex_colIndex_injective T
  have hrow : rowIndex T i = rowIndex T l := by exact_mod_cast heq
  exact Prod.ext hrow (i.property.trans l.property.symm)

theorem transportedCocharge_rowMonovary {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (j : ℕ) :
    Monovary (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ))
      (fun i : {i // rowIndex T i = j} => (transportedCocharge S T i : ℤ)) := by
  apply Monovary.symm
  intro i l hil
  change (colIndex T i : ℤ) < (colIndex T l : ℤ) at hil
  have hcol : colIndex T i ≤ colIndex T l := by exact_mod_cast hil.le
  have hr : (T.symm i).val.1 = (T.symm l).val.1 := by
    simpa only [← rowIndex_def] using i.property.trans l.property.symm
  have hc : (T.symm i).val.2 ≤ (T.symm l).val.2 := by
    simpa only [← colIndex_def] using hcol
  change (cochargeFilling S (T.symm i) : ℤ) ≤ (cochargeFilling S (T.symm l) : ℤ)
  exact_mod_cast cochargeFilling_row_mono S hr hc

theorem transportedCocharge_columnDistinct {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (j : ℕ) :
    Function.Injective (fun i : {i // colIndex T i = j} => transportedCocharge S T i) := by
  intro i l hil
  apply Subtype.ext
  apply rowIndex_colIndex_injective T
  refine Prod.ext ?_ (i.property.trans l.property.symm)
  change rowIndex T i = rowIndex T l
  by_contra hrow
  rcases lt_or_gt_of_ne hrow with h | h
  · have hh := cochargeFilling_col_strict S (c := T.symm i) (d := T.symm l)
      (by simpa only [← colIndex_def] using i.property.trans l.property.symm)
      (by simpa only [← rowIndex_def] using h)
    exact (ne_of_lt hh) hil
  · have hh := cochargeFilling_col_strict S (c := T.symm l) (d := T.symm i)
      (by simpa only [← colIndex_def] using l.property.trans i.property.symm)
      (by simpa only [← rowIndex_def] using h)
    exact (ne_of_lt hh) hil.symm

theorem transportedCocharge_columnMonovary {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (j : ℕ) :
    Monovary (fun i : {i // colIndex T i = j} => (rowIndex T i : ℤ))
      (fun i : {i // colIndex T i = j} => (transportedCocharge S T i : ℤ)) := by
  apply Monovary.symm
  intro i l hil
  change (rowIndex T i : ℤ) < (rowIndex T l : ℤ) at hil
  have hrow : rowIndex T i < rowIndex T l := by exact_mod_cast hil
  have hc : (T.symm i).val.2 = (T.symm l).val.2 := by
    simpa only [← colIndex_def] using i.property.trans l.property.symm
  have hr : (T.symm i).val.1 < (T.symm l).val.1 := by
    simpa only [← rowIndex_def] using hrow
  change (cochargeFilling S (T.symm i) : ℤ) ≤ (cochargeFilling S (T.symm l) : ℤ)
  exact_mod_cast (cochargeFilling_col_strict S hc hr).le

end HigherSpecht
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/ColumnReadingInsertion.lean -/



/-!
# Column-reading cocharge and its genuine insertion witness

Columns are read left to right and, within a column, from top to bottom.
The cyclic scan uses the reverse of that reading.  The consecutive-entry
argument proves admissibility directly, so this construction does not
assume the equality of row- and column-reading catabolism outputs.
-/

noncomputable section

open Finset TauCeti TauCeti.YoungTableau Function

namespace HigherSpecht

def columnReadingCells (μ : YoungDiagram) : List ↥μ.cells :=
  μ.cells.attach.toList.mergeSort fun c d =>
    decide (c.val.2 < d.val.2 ∨ (c.val.2 = d.val.2 ∧ d.val.1 ≤ c.val.1))

def columnScanCells (μ : YoungDiagram) : List ↥μ.cells := (columnReadingCells μ).reverse

@[simp] theorem mem_columnReadingCells {μ : YoungDiagram} (c : ↥μ.cells) :
    c ∈ columnReadingCells μ := by simp [columnReadingCells]

@[simp] theorem mem_columnScanCells {μ : YoungDiagram} (c : ↥μ.cells) :
    c ∈ columnScanCells μ := by simp [columnScanCells]

@[simp] theorem length_columnReadingCells (μ : YoungDiagram) :
    (columnReadingCells μ).length = μ.card := by
  simp [columnReadingCells, YoungDiagram.card]

@[simp] theorem length_columnScanCells (μ : YoungDiagram) :
    (columnScanCells μ).length = μ.card := by simp [columnScanCells]

theorem nodup_columnReadingCells (μ : YoungDiagram) : (columnReadingCells μ).Nodup := by
  unfold columnReadingCells
  exact (List.mergeSort_perm _ _).nodup_iff.mpr μ.cells.attach.nodup_toList

theorem nodup_columnScanCells (μ : YoungDiagram) : (columnScanCells μ).Nodup := by
  simpa only [columnScanCells, List.nodup_reverse] using nodup_columnReadingCells μ

theorem pairwise_columnReadingCells (μ : YoungDiagram) :
    (columnReadingCells μ).Pairwise (fun c d =>
      c.val.2 < d.val.2 ∨ (c.val.2 = d.val.2 ∧ d.val.1 ≤ c.val.1)) := by
  unfold columnReadingCells
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun c d : ↥μ.cells =>
        decide (c.val.2 < d.val.2 ∨ (c.val.2 = d.val.2 ∧ d.val.1 ≤ c.val.1)))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      μ.cells.attach.toList)

def columnScanEquiv (μ : YoungDiagram) : Fin μ.card ≃ ↥μ.cells :=
  (finCongr (length_columnScanCells μ).symm).trans
    (List.Nodup.getEquivOfForallMemList (columnScanCells μ)
      (nodup_columnScanCells μ) (fun c => mem_columnScanCells c))

@[simp] theorem columnScanEquiv_apply (μ : YoungDiagram) (i : Fin μ.card) :
    columnScanEquiv μ i = (columnScanCells μ).get ⟨i.val, by simpa using i.isLt⟩ := rfl

theorem columnScan_column_antitone (μ : YoungDiagram) :
    Antitone (fun i : Fin μ.card => (columnScanEquiv μ i).val.2) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with hij | hij
  · subst j
    exact le_rfl
  · have hpair : (columnScanCells μ).Pairwise (fun c d =>
        d.val.2 < c.val.2 ∨ (d.val.2 = c.val.2 ∧ c.val.1 ≤ d.val.1)) := by
      exact (pairwise_columnReadingCells μ).reverse
    have h := hpair.rel_get_of_lt
      (a := ⟨i.val, by simpa using i.isLt⟩)
      (b := ⟨j.val, by simpa using j.isLt⟩) hij
    change (columnScanEquiv μ j).val.2 ≤ (columnScanEquiv μ i).val.2
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le

theorem consecutive_above_column_le {μ : YoungDiagram} (S : StandardYoungTableau μ)
    {i j : Fin μ.card} (hnext : j.val = i.val + 1)
    (hrow : rowIndex S.toTableau i < rowIndex S.toTableau j) :
    colIndex S.toTableau j ≤ colIndex S.toTableau i := by
  by_contra hn
  have hcol := lt_of_not_ge hn
  have hjmem : (rowIndex S.toTableau j, colIndex S.toTableau j) ∈ μ := by
    rw [rowIndex_def, colIndex_def]
    exact (S.toTableau.symm j).property
  let c : ↥μ.cells := ⟨(rowIndex S.toTableau i, colIndex S.toTableau j),
    μ.up_left_mem hrow.le le_rfl hjmem⟩
  have hic : i < S c := S.lt_of_colIndex_lt
    (by rw [rowIndex_standard_apply])
    (by simpa only [colIndex_standard_apply, c] using hcol)
  have hcj : S c < j := S.lt_of_rowIndex_lt
    (by rw [colIndex_standard_apply])
    (by simpa only [rowIndex_standard_apply, c] using hrow)
  have hic' : i.val < (S c).val := hic
  have hcj' : (S c).val < j.val := hcj
  omega

theorem pair_sublist_columnReadingCells {μ : YoungDiagram} {c d : ↥μ.cells}
    (hcol : c.val.2 ≤ d.val.2) (hrow : d.val.1 < c.val.1) :
    [c, d].Sublist (columnReadingCells μ) := by
  apply pair_sublist_of_pairwise (pairwise_columnReadingCells μ)
    (mem_columnReadingCells c) (mem_columnReadingCells d)
  · intro h
    have hh := congrArg (fun c : ↥μ.cells => c.val.1) h
    omega
  · intro h
    rcases h with h | ⟨_, h⟩ <;> omega

def columnCochargeWord {μ : YoungDiagram} (S : StandardYoungTableau μ) : List ℕ :=
  (columnReadingCells μ).map (cochargeFilling S)

def columnScanCocharge {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (i : Fin μ.card) : ℕ := cochargeFilling S (columnScanEquiv μ i)

theorem ofFn_columnScanCocharge {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    List.ofFn (columnScanCocharge S) = (columnCochargeWord S).reverse := by
  apply List.ext_getElem
  · simp [columnCochargeWord]
  · intro i hi hj
    simp only [List.getElem_ofFn, columnScanCocharge, columnScanEquiv_apply,
      List.get_eq_getElem, columnCochargeWord, ← List.map_reverse, columnScanCells,
      List.getElem_map]

/-- The same cocharge labels are admissible in the actual column reading. -/
theorem columnCochargeWord_admissible {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CatAdmissible ⟨columnCochargeWord S, ⊥⟩ := by
  intro a ha hap
  right
  obtain ⟨c, hc, hca⟩ := List.mem_map.mp ha
  have hac : a ≤ ascentCount (tableauRows S) (S c).val := le_of_eq hca.symm
  obtain ⟨i, hij, hic, hir⟩ := exists_ascent_at_level (tableauRows S) hap hac
  have hi : i < μ.card := hij.trans (S c).isLt
  have hi' : i + 1 < μ.card := by have := (S c).isLt; omega
  let x : Fin μ.card := ⟨i, hi⟩
  let y : Fin μ.card := ⟨i + 1, hi'⟩
  have hxy : rowIndex S.toTableau x < rowIndex S.toTableau y := by
    simpa only [tableauRows, dif_pos hi, dif_pos hi'] using hir
  have hcol := consecutive_above_column_le S (i := x) (j := y) rfl hxy
  have hpair := (pair_sublist_columnReadingCells
    (c := S.toTableau.symm y) (d := S.toTableau.symm x)
    (by simpa only [colIndex_def] using hcol)
    (by simpa only [rowIndex_def] using hxy)).map (cochargeFilling S)
  have hx : cochargeFilling S (S.toTableau.symm x) = a - 1 := by
    simpa only [cochargeFilling, standardTableau_apply_symm, cochargeLabel] using hic
  have hy : cochargeFilling S (S.toTableau.symm y) = a := by
    have hya : ascentCount (tableauRows S) (i + 1) = a := by
      rw [ascentCount_succ, if_pos hir, hic]
      omega
    simpa only [cochargeFilling, standardTableau_apply_symm, cochargeLabel, y] using hya
  simpa only [List.map_cons, List.map_nil, hx, hy, columnCochargeWord] using hpair

theorem columnScanCocharge_admissible {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CatAdmissible ⟨(List.ofFn (columnScanCocharge S)).reverse, ⊥⟩ := by
  rw [ofFn_columnScanCocharge, List.reverse_reverse]
  exact columnCochargeWord_admissible S

/-- The first terminating step of the actual unlabeled algorithm.  Only the
step number is selected: the labeled state below is the deterministic run,
not an arbitrary state satisfying its invariants. -/
def columnInsertionSteps {μ : YoungDiagram} (S : StandardYoungTableau μ) : ℕ := by
  classical
  exact Nat.find (catRun_eventually_empty (columnScanCocharge_admissible S))

theorem columnInsertionSteps_empty {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    (catRun (columnInsertionSteps S)
      ⟨(List.ofFn (columnScanCocharge S)).reverse, ⊥⟩).word = [] := by
  classical
  exact Nat.find_spec (catRun_eventually_empty (columnScanCocharge_admissible S))

theorem columnInsertion_pending_nil {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    (labeledCatRun (columnScanCocharge S) (columnInsertionSteps S)
      (labeledInitial μ.card)).pending = [] := by
  have hforget := labeledForget_run (columnScanCocharge S) (columnInsertionSteps S)
    (labeledInitial μ.card)
  rw [labeledForget_initial] at hforget
  have h := congrArg CatState.word hforget
  rw [columnInsertionSteps_empty S] at h
  simpa only [labeledForget, List.reverse_eq_nil_iff, List.map_eq_nil_iff] using h

/-- The completed column-reading witness retains the exact acceptance and
rejection decisions of `labeledCatStep`.  Its ordinary invariants are proved
from this execution and are the ones used by all subsequent pairings. -/
def columnInsertion {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CompleteInsertion (columnScanCocharge S) where
  state := labeledCatRun (columnScanCocharge S) (columnInsertionSteps S)
    (labeledInitial μ.card)
  invariant := labeledInvariant_run (columnScanCocharge S) (columnInsertionSteps S)
  pending_nil := columnInsertion_pending_nil S

/-- Literal correspondence with the deterministic labeled insertion run. -/
@[simp] theorem columnInsertion_state {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    (columnInsertion S).state =
      labeledCatRun (columnScanCocharge S) (columnInsertionSteps S)
        (labeledInitial μ.card) := rfl

/-- A deterministic insertion has only one completed labeled state.  In
particular, the polynomial witness is independent of how many idle steps
are taken after the queue becomes empty. -/
theorem labeledCatRun_complete_unique {n : ℕ} (a : Fin n → ℕ) (N M : ℕ)
    (hN : (labeledCatRun a N (labeledInitial n)).pending = [])
    (hM : (labeledCatRun a M (labeledInitial n)).pending = []) :
    labeledCatRun a N (labeledInitial n) = labeledCatRun a M (labeledInitial n) := by
  have hfixed {s : LabeledCatState n} (h : s.pending = []) : labeledCatStep a s = s := by
    simp only [labeledCatStep, h]
  have hNM : labeledCatRun a (M + N) (labeledInitial n) =
      labeledCatRun a N (labeledInitial n) := by
    rw [labeledCatRun, Function.iterate_add_apply]
    exact Function.iterate_fixed (hfixed hN) M
  have hMN : labeledCatRun a (N + M) (labeledInitial n) =
      labeledCatRun a M (labeledInitial n) := by
    rw [labeledCatRun, Function.iterate_add_apply]
    exact Function.iterate_fixed (hfixed hM) N
  exact hNM.symm.trans ((congrArg
    (fun k => labeledCatRun a k (labeledInitial n)) (Nat.add_comm M N)).trans hMN)

/-- Every completed execution of the manuscript's column-reading algorithm
has exactly this state, including its filling and rejection counts. -/
theorem columnInsertion_agrees_with_completed_run {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (N : ℕ)
    (hN : (labeledCatRun (columnScanCocharge S) N (labeledInitial μ.card)).pending = []) :
    (columnInsertion S).state =
      labeledCatRun (columnScanCocharge S) N (labeledInitial μ.card) := by
  exact labeledCatRun_complete_unique (columnScanCocharge S) (columnInsertionSteps S) N
    (columnInsertion_pending_nil S) hN

theorem columnInsertion_output {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CatWordOutput (columnCochargeWord S) (columnInsertion S).state.shape := by
  refine ⟨columnInsertionSteps S, ?_⟩
  have hforget : labeledForget (columnScanCocharge S) (columnInsertion S).state =
      catRun (columnInsertionSteps S) ⟨columnCochargeWord S, ⊥⟩ := by
    rw [columnInsertion_state, labeledForget_run, labeledForget_initial,
      ofFn_columnScanCocharge, List.reverse_reverse]
  rw [← hforget]
  simp only [labeledForget, (columnInsertion S).pending_nil, List.map_nil, List.reverse_nil]

theorem columnInsertion_rearrangementWitness {μ : YoungDiagram}
    (S : StandardYoungTableau μ) :
    RearrangementWitness (columnInsertion S).column
      (fun i => ((columnInsertion S).column i, (columnInsertion S).rejection i))
      (fun i => ((columnInsertion S).row i : ℤ))
      (fun i => ((columnInsertion S).rejection i : ℤ))
      (fun i => (columnScanCocharge S i : ℤ))
      (fun i => ((columnScanEquiv μ i).val.2 : ℤ)) :=
  (columnInsertion S).rearrangementWitness _ (columnScan_column_antitone μ)

end HigherSpecht
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/ReadingWords.lean -/



/-!
# Equality of row-reading and column-reading cyclic outputs

The proof constructs both reading words from the actual cells.  A complete
next column is inserted by the genuine Schensted bumping algorithm; elementary
Knuth transformations connect that insertion to its row word.  The local
cyclic invariance theorem then identifies the two catabolism outputs.
-/

noncomputable section

open Finset TauCeti Function

namespace HigherSpecht

def cellsInRow (μ : YoungDiagram) (r cut : ℕ) : List ↥μ.cells :=
  List.ofFn fun c : Fin (min cut (μ.rowLen r)) =>
    ⟨(r, c.val), YoungDiagram.mem_iff_lt_rowLen.mpr (lt_of_lt_of_le c.isLt (min_le_right _ _))⟩

def rowsOfCells (μ : YoungDiagram) (cut : ℕ) : List (List ↥μ.cells) :=
  List.ofFn fun r : Fin (μ.colLen 0) => cellsInRow μ r cut

def cellsInColumn (μ : YoungDiagram) (c : ℕ) : List ↥μ.cells :=
  List.ofFn fun r : Fin (μ.colLen c) =>
    ⟨(r.val, c), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩

def columnsOfCells (μ : YoungDiagram) (cut : ℕ) : List (List ↥μ.cells) :=
  List.ofFn fun c : Fin cut => (cellsInColumn μ c).reverse

 theorem mem_cellsInRow (μ : YoungDiagram) (r cut : ℕ) (c : ↥μ.cells) :
    c ∈ cellsInRow μ r cut ↔ c.val.1 = r ∧ c.val.2 < cut := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    have heq := congrArg Subtype.val hi
    exact ⟨(congrArg Prod.fst heq).symm,
      (congrArg Prod.snd heq).symm ▸ (lt_of_lt_of_le i.isLt (min_le_left _ _))⟩
  · rintro ⟨hr, hcut⟩
    apply List.mem_ofFn.mpr
    refine ⟨⟨c.val.2, lt_min hcut ?_⟩, ?_⟩
    · simpa only [hr] using YoungDiagram.mem_iff_lt_rowLen.mp c.property
    · exact Subtype.ext (Prod.ext hr.symm rfl)

 theorem mem_cellsInColumn (μ : YoungDiagram) (j : ℕ) (c : ↥μ.cells) :
    c ∈ cellsInColumn μ j ↔ c.val.2 = j := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact (congrArg (fun d : ↥μ.cells => d.val.2) hi).symm
  · intro hc
    apply List.mem_ofFn.mpr
    refine ⟨⟨c.val.1, ?_⟩, Subtype.ext (Prod.ext rfl hc.symm)⟩
    simpa only [hc] using YoungDiagram.mem_iff_lt_colLen.mp c.property

 theorem mem_rowsOfCells_flatten (μ : YoungDiagram) (cut : ℕ) (c : ↥μ.cells) :
    c ∈ (rowsOfCells μ cut).flatten ↔ c.val.2 < cut := by
  simp only [rowsOfCells, List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨row, ⟨r, rfl⟩, hc⟩
    exact ((mem_cellsInRow μ _ _ c).mp hc).2
  · intro hc
    let r : Fin (μ.colLen 0) := ⟨c.val.1, YoungDiagram.lt_colLen_zero_of_mem c.property⟩
    exact ⟨cellsInRow μ r cut, ⟨r, rfl⟩, (mem_cellsInRow μ _ _ c).mpr ⟨rfl, hc⟩⟩

 theorem mem_columnsOfCells_flatten (μ : YoungDiagram) (cut : ℕ) (c : ↥μ.cells) :
    c ∈ (columnsOfCells μ cut).flatten ↔ c.val.2 < cut := by
  simp only [columnsOfCells, List.mem_flatten, List.mem_ofFn, List.mem_reverse]
  constructor
  · rintro ⟨col, ⟨j, rfl⟩, hc⟩
    exact ((mem_cellsInColumn μ _ c).mp (List.mem_reverse.mp hc)) ▸ j.isLt
  · intro hc
    let j : Fin cut := ⟨c.val.2, hc⟩
    exact ⟨(cellsInColumn μ j).reverse, ⟨j, rfl⟩,
      List.mem_reverse.mpr ((mem_cellsInColumn μ _ c).mpr rfl)⟩

 theorem pairwise_rowExpansion (μ : YoungDiagram) (cut : ℕ) :
    ((rowsOfCells μ cut).reverse.flatten).Pairwise (fun c d =>
      d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 < d.val.2)) := by
  rw [List.pairwise_flatten]
  constructor
  · intro row hrow
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hrow)
    rw [cellsInRow, List.pairwise_ofFn]
    intro i j hij
    exact Or.inr ⟨rfl, hij⟩
  · rw [List.pairwise_reverse, rowsOfCells, List.pairwise_ofFn]
    intro i j hij c hc d hd
    have hc' := (mem_cellsInRow μ j cut c).mp hc
    have hd' := (mem_cellsInRow μ i cut d).mp hd
    exact Or.inl (by simpa only [hc'.1, hd'.1] using Fin.lt_iff_val_lt_val.mp hij)

 theorem pairwise_columnExpansion (μ : YoungDiagram) (cut : ℕ) :
    ((columnsOfCells μ cut).flatten).Pairwise (fun c d =>
      c.val.2 < d.val.2 ∨ (c.val.2 = d.val.2 ∧ d.val.1 < c.val.1)) := by
  rw [List.pairwise_flatten]
  constructor
  · intro col hcol
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hcol
    rw [List.pairwise_reverse, cellsInColumn, List.pairwise_ofFn]
    intro i k hik
    exact Or.inr ⟨rfl, hik⟩
  · rw [columnsOfCells, List.pairwise_ofFn]
    intro i j hij c hc d hd
    have hc' := (mem_cellsInColumn μ i c).mp (List.mem_reverse.mp hc)
    have hd' := (mem_cellsInColumn μ j d).mp (List.mem_reverse.mp hd)
    exact Or.inl (by simpa only [hc', hd'] using Fin.lt_iff_val_lt_val.mp hij)

@[simp] theorem mem_rowReadingCells {μ : YoungDiagram} (c : ↥μ.cells) :
    c ∈ rowReadingCells μ := by simp [rowReadingCells]

 theorem nodup_rowReadingCells (μ : YoungDiagram) : (rowReadingCells μ).Nodup := by
  unfold rowReadingCells
  exact (List.mergeSort_perm _ _).nodup_iff.mpr μ.cells.attach.nodup_toList

 theorem pairwise_rowReadingCells (μ : YoungDiagram) :
    (rowReadingCells μ).Pairwise (fun c d =>
      d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 ≤ d.val.2)) := by
  unfold rowReadingCells
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun c d : ↥μ.cells =>
        decide (d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 ≤ d.val.2)))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      μ.cells.attach.toList)

 theorem rowReadingCells_eq_expansion (μ : YoungDiagram) :
    rowReadingCells μ = (rowsOfCells μ (μ.rowLen 0)).reverse.flatten := by
  let rel : ↥μ.cells → ↥μ.cells → Prop := fun c d =>
    d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 ≤ d.val.2)
  have hleft : (rowReadingCells μ).Pairwise rel := pairwise_rowReadingCells μ
  have hright : ((rowsOfCells μ (μ.rowLen 0)).reverse.flatten).Pairwise rel := by
    apply (pairwise_rowExpansion μ (μ.rowLen 0)).imp
    intro c d h
    rcases h with h | ⟨hrow, hcol⟩
    · exact Or.inl h
    · exact Or.inr ⟨hrow, hcol.le⟩
  have hnodup : ((rowsOfCells μ (μ.rowLen 0)).reverse.flatten).Nodup :=
    (pairwise_rowExpansion μ (μ.rowLen 0)).imp (fun h heq => by subst heq; rcases h with h | h <;> omega)
  have hperm : (rowReadingCells μ).Perm (rowsOfCells μ (μ.rowLen 0)).reverse.flatten := by
    apply (List.perm_ext_iff_of_nodup (nodup_rowReadingCells μ) hnodup).mpr
    intro c
    have hc : c.val.2 < μ.rowLen 0 :=
      (YoungDiagram.mem_iff_lt_rowLen.mp c.property).trans_le
        (μ.rowLen_anti 0 c.val.1 (Nat.zero_le _))
    simp only [mem_rowReadingCells, List.mem_flatten, List.mem_reverse, true_iff]
    simpa only [List.mem_flatten] using (mem_rowsOfCells_flatten μ _ c).mpr hc
  apply hperm.eq_of_pairwise _ hleft hright
  intro c d _ _ hcd hdc
  apply Subtype.ext
  apply Prod.ext <;> rcases hcd with hcd | hcd <;> rcases hdc with hdc | hdc <;> omega

 theorem columnReadingCells_eq_expansion (μ : YoungDiagram) :
    columnReadingCells μ = (columnsOfCells μ (μ.rowLen 0)).flatten := by
  let rel : ↥μ.cells → ↥μ.cells → Prop := fun c d =>
    c.val.2 < d.val.2 ∨ (c.val.2 = d.val.2 ∧ d.val.1 ≤ c.val.1)
  have hleft : (columnReadingCells μ).Pairwise rel := pairwise_columnReadingCells μ
  have hright : ((columnsOfCells μ (μ.rowLen 0)).flatten).Pairwise rel := by
    apply (pairwise_columnExpansion μ (μ.rowLen 0)).imp
    intro c d h
    rcases h with h | ⟨hcol, hrow⟩
    · exact Or.inl h
    · exact Or.inr ⟨hcol, hrow.le⟩
  have hnodup : ((columnsOfCells μ (μ.rowLen 0)).flatten).Nodup :=
    (pairwise_columnExpansion μ (μ.rowLen 0)).imp
      (fun h heq => by subst heq; rcases h with h | h <;> omega)
  have hperm : (columnReadingCells μ).Perm (columnsOfCells μ (μ.rowLen 0)).flatten := by
    apply (List.perm_ext_iff_of_nodup (nodup_columnReadingCells μ) hnodup).mpr
    intro c
    have hc : c.val.2 < μ.rowLen 0 :=
      (YoungDiagram.mem_iff_lt_rowLen.mp c.property).trans_le
        (μ.rowLen_anti 0 c.val.1 (Nat.zero_le _))
    simp only [mem_columnReadingCells, mem_columnsOfCells_flatten, hc]
  apply hperm.eq_of_pairwise _ hleft hright
  intro c d _ _ hcd hdc
  apply Subtype.ext
  apply Prod.ext <;> rcases hcd with hcd | hcd <;> rcases hdc with hdc | hdc <;> omega

def fillingRows {μ : YoungDiagram} (f : ↥μ.cells → ℕ) (cut : ℕ) : List (List ℕ) :=
  (rowsOfCells μ cut).map (List.map f)

def fillingColumn {μ : YoungDiagram} (f : ↥μ.cells → ℕ) (j : ℕ) : List ℕ :=
  (cellsInColumn μ j).map f

def fillingColumnWord {μ : YoungDiagram} (f : ↥μ.cells → ℕ) (cut : ℕ) : List ℕ :=
  ((columnsOfCells μ cut).flatten).map f

 theorem fillingRows_sorted {μ : YoungDiagram} (f : ↥μ.cells → ℕ)
    (hf : ∀ c d, c.val.1 = d.val.1 → c.val.2 ≤ d.val.2 → f c ≤ f d)
    (cut : ℕ) : RowsSorted (fillingRows f cut) := by
  intro row hrow
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hcs
  rw [cellsInRow, List.map_ofFn]
  apply List.sortedLE_ofFn_iff.mpr
  intro i j hij
  exact hf _ _ rfl hij

 theorem fillingColumn_sorted {μ : YoungDiagram} (f : ↥μ.cells → ℕ)
    (hf : ∀ c d, c.val.2 = d.val.2 → c.val.1 < d.val.1 → f c < f d)
    (j : ℕ) : (fillingColumn f j).SortedLT := by
  rw [fillingColumn, cellsInColumn, List.map_ofFn]
  apply List.sortedLT_ofFn_iff.mpr
  intro i k hik
  exact hf _ _ rfl hik

 theorem fillingColumn_dominates {μ : YoungDiagram} (f : ↥μ.cells → ℕ)
    (hf : ∀ c d, c.val.1 = d.val.1 → c.val.2 ≤ d.val.2 → f c ≤ f d)
    (j : ℕ) : ColumnDominates (fillingRows f j) (fillingColumn f j) := by
  have hlen : μ.colLen j ≤ μ.colLen 0 := μ.colLen_anti 0 j (Nat.zero_le _)
  suffices h : ∀ (rows : List (List ℕ)) (col : List ℕ),
      (∀ i (hi : i < col.length), ∀ x ∈ rows.getD i [], x ≤ col[i]) →
      ColumnDominates rows col by
    apply h
    intro i hi x hx
    have hii : i < μ.colLen j := by simpa [fillingColumn, cellsInColumn] using hi
    have hi0 := hii.trans_le hlen
    simp only [fillingRows, rowsOfCells, List.map_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hi0, dite_true, Option.getD_some] at hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have hc' := (mem_cellsInRow μ i j c).mp hc
    simpa only [fillingColumn, cellsInColumn, List.map_ofFn, List.getElem_ofFn,
      Function.comp_def] using
      hf c ⟨(i, j), YoungDiagram.mem_iff_lt_colLen.mpr hii⟩ hc'.1 hc'.2.le
  intro rows col h
  induction col generalizing rows with
  | nil => cases rows <;> trivial
  | cons c cs ih =>
    cases rows with
    | nil => trivial
    | cons row rows =>
      refine ⟨?_, ih rows ?_⟩
      · intro x hx
        exact (h 0 (by simp) x (by simpa only [List.getD_cons_zero] using hx)).trans_eq
          (List.getElem_cons_zero c cs _)
      · intro i hi x hx
        exact (h (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi) x
          (by simpa only [List.getD_cons_succ] using hx)).trans_eq
            (List.getElem_cons_succ c cs i _)

 theorem fillingRows_appendColumn {μ : YoungDiagram} (f : ↥μ.cells → ℕ) (j : ℕ) :
    appendColumn (fillingRows f j) (fillingColumn f j) = fillingRows f (j + 1) := by
  have hrowsLength (cut : ℕ) : (fillingRows f cut).length = μ.colLen 0 := by
    simp only [fillingRows, rowsOfCells, List.length_map, List.length_ofFn]
  have hcolumnLength : (fillingColumn f j).length = μ.colLen j := by
    simp only [fillingColumn, cellsInColumn, List.length_map, List.length_ofFn]
  have hlen : (fillingColumn f j).length ≤ (fillingRows f j).length := by
    rw [hcolumnLength, hrowsLength]
    exact μ.colLen_anti 0 j (Nat.zero_le _)
  have hgetRow (cut r : ℕ) (hr : r < μ.colLen 0) :
      (fillingRows f cut)[r]'(by rw [hrowsLength]; exact hr) =
        (cellsInRow μ r cut).map f := by
    simp only [fillingRows, rowsOfCells, List.getElem_map, List.getElem_ofFn]
  have hgetColumn (r : ℕ) (hr : r < μ.colLen j) :
      (fillingColumn f j)[r]'(by rw [hcolumnLength]; exact hr) =
        f ⟨(r, j), YoungDiagram.mem_iff_lt_colLen.mpr hr⟩ := by
    simp only [fillingColumn, cellsInColumn, List.getElem_map, List.getElem_ofFn]
  apply List.ext_getElem
  · rw [length_appendColumn, max_eq_left hlen, hrowsLength, hrowsLength]
  · intro r hr hs
    have hrRows : r < (fillingRows f j).length := by
      simpa only [length_appendColumn, max_eq_left hlen] using hr
    have hr0 : r < μ.colLen 0 := by
      simpa only [hrowsLength] using hrRows
    rw [getElem_appendColumn hlen r hrRows, hgetRow j r hr0, hgetRow (j + 1) r hr0]
    by_cases hrj : r < μ.colLen j
    · have hjr : j < μ.rowLen r := YoungDiagram.mem_iff_lt_rowLen.mp
        (YoungDiagram.mem_iff_lt_colLen.mpr hrj)
      have hrcol : r < (fillingColumn f j).length := by rwa [hcolumnLength]
      rw [dif_pos hrcol, hgetColumn r hrj]
      simp only [cellsInRow, min_eq_left hjr.le,
        min_eq_left (Nat.succ_le_of_lt hjr), List.map_ofFn, Function.comp_def, Fin.val_cast]
      symm
      simpa only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last] using
        List.ofFn_succ' (fun c : Fin (j + 1) =>
          f ⟨(r, c.val), YoungDiagram.mem_iff_lt_rowLen.mpr
            (c.isLt.trans_le (Nat.succ_le_of_lt hjr))⟩)
    · have hjr : μ.rowLen r ≤ j := by
        by_contra h
        exact hrj (YoungDiagram.mem_iff_lt_colLen.mp
          (YoungDiagram.mem_iff_lt_rowLen.mpr (lt_of_not_ge h)))
      have hrcol : ¬ r < (fillingColumn f j).length := by rwa [hcolumnLength]
      simp only [dif_neg hrcol, List.append_nil, cellsInRow, min_eq_right hjr,
        min_eq_right (hjr.trans (Nat.le_succ j)), Fin.val_cast]

 theorem fillingColumnWord_succ {μ : YoungDiagram} (f : ↥μ.cells → ℕ) (j : ℕ) :
    fillingColumnWord f (j + 1) = fillingColumnWord f j ++ (fillingColumn f j).reverse := by
  simp only [fillingColumnWord, columnsOfCells, List.ofFn_succ', List.concat_eq_append,
    List.flatten_append, List.flatten_singleton, List.map_append, fillingColumn,
    List.map_reverse, Fin.val_castSucc, Fin.val_last]

 theorem filling_readings_knuth {μ : YoungDiagram} (f : ↥μ.cells → ℕ)
    (hrow : ∀ c d, c.val.1 = d.val.1 → c.val.2 ≤ d.val.2 → f c ≤ f d)
    (hcol : ∀ c d, c.val.2 = d.val.2 → c.val.1 < d.val.1 → f c < f d) :
    KnuthEquivalent ((columnReadingCells μ).map f) ((rowReadingCells μ).map f) := by
  have hcut : ∀ j, KnuthEquivalent (fillingColumnWord f j) (rowWordRows (fillingRows f j)) := by
    intro j
    induction j with
    | zero => simpa [fillingColumnWord, columnsOfCells, rowWordRows, fillingRows,
        rowsOfCells, cellsInRow] using KnuthEquivalent.refl []
    | succ j ih =>
      rw [fillingColumnWord_succ]
      refine (ih.append_right (fillingColumn f j).reverse).trans ?_
      rw [← fillingRows_appendColumn]
      exact knuth_appendColumn _ _
        (fillingRows_sorted f hrow j) (fillingColumn_dominates f hrow j)
        (fillingColumn_sorted f hcol j)
  rw [columnReadingCells_eq_expansion, rowReadingCells_eq_expansion]
  simpa only [fillingColumnWord, fillingRows, rowWordRows, List.map_reverse,
    List.map_flatten] using hcut (μ.rowLen 0)

 theorem cocharge_readings_knuth {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    KnuthEquivalent (columnCochargeWord S) (cochargeWord S) :=
  filling_readings_knuth (cochargeFilling S)
    (fun _ _ => cochargeFilling_row_mono S)
    (fun _ _ => cochargeFilling_col_strict S)

/-- The output of the actual column scan is exactly the paper's row-word
catabolizability output.  This closes the convention bridge needed by the
column-reading witness, rather than adding an insertion-shape hypothesis. -/
 theorem columnInsertion_catTableauOutput {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CatTableauOutput S (columnInsertion S).state.shape :=
  (catWordOutput_knuth_iff (cocharge_readings_knuth S) _).mp (columnInsertion_output S)

 theorem columnInsertion_dominates_iff {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (lam : YoungDiagram) : Dominates (columnInsertion S).state.shape lam ↔ CatDominates S lam := by
  constructor
  · intro h
    exact ⟨_, columnInsertion_catTableauOutput S, h⟩
  · rintro ⟨ν, hν, hdom⟩
    rwa [catTableauOutput_unique S (columnInsertion_catTableauOutput S) hν]

end HigherSpecht
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/EligibleIndexCountKnuth.lean -/



/-!
# The actual inverse-descent statistic under RSK

For a word with distinct letters, an elementary Knuth move exchanges two
nonconsecutive values. Thus it preserves the order of every pair `i,i+1`.
We combine this elementary invariant with the literal insertion normal form,
not with an assumed RSK statistic-preservation theorem.
-/

noncomputable section
open TauCeti Finset
open TauCeti.YoungTableau
open scoped Classical

namespace HigherSpecht

theorem KnuthEquivalent.perm {u v : List ℕ} (h : KnuthEquivalent u v) : u.Perm v := by
  induction h with
  | refl u => exact .refl _
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | append l r h ih => exact (ih.append_left l).append_right r
  | left hab hbc => exact (List.Perm.swap _ _ _).cons _
  | right hab hbc => exact List.Perm.swap _ _ _

def adjacentFilter (k : ℕ) (w : List ℕ) : List ℕ :=
  w.filter fun a => decide (a = k ∨ a = k + 1)

theorem adjacentFilter_swap {a c k : ℕ} (hgap : a + 1 < c) (w : List ℕ) :
    adjacentFilter k (a :: c :: w) = adjacentFilter k (c :: a :: w) := by
  by_cases ha : a = k ∨ a = k + 1 <;> by_cases hc : c = k ∨ c = k + 1
  · omega
  · simp [adjacentFilter, ha, hc]
  · simp [adjacentFilter, ha, hc]
  · simp [adjacentFilter, ha, hc]

theorem KnuthEquivalent.adjacentFilter_eq {u v : List ℕ}
    (h : KnuthEquivalent u v) (hu : u.Nodup) (k : ℕ) :
    adjacentFilter k u = adjacentFilter k v := by
  revert hu
  induction h with
  | refl u => intro hu; rfl
  | symm h ih => intro hu; exact (ih (h.perm.nodup_iff.mpr hu)).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hu
      exact (ih₁ hu).trans (ih₂ (h₁.perm.nodup_iff.mp hu))
  | @append u v l r h ih =>
      intro hu
      have hwhole : (l ++ (u ++ r)).Nodup := by
        simpa only [List.append_assoc] using hu
      have hu' : u.Nodup := hwhole.of_append_right.of_append_left
      simp only [adjacentFilter, List.filter_append]
      rw [show u.filter (fun a => decide (a = k ∨ a = k + 1)) =
          v.filter (fun a => decide (a = k ∨ a = k + 1)) from ih hu']
  | @left a b c hab hbc =>
      intro hu
      have hbcne : b ≠ c := by intro heq; subst c; simp at hu
      have hgap : a + 1 < c := by omega
      have heq : adjacentFilter k [a, c] = adjacentFilter k [c, a] :=
        adjacentFilter_swap hgap []
      simpa only [adjacentFilter, List.filter_cons] using congrArg
        (fun w : List ℕ => if decide (b = k ∨ b = k + 1) then b :: w else w) heq
  | @right a b c hab hbc =>
      intro hu
      have habne : a ≠ b := by intro heq; subst b; simp at hu
      exact adjacentFilter_swap (by omega) [b]

theorem pair_sublist_adjacentFilter (k : ℕ) (w : List ℕ) :
    [k + 1, k].Sublist (adjacentFilter k w) ↔ [k + 1, k].Sublist w := by
  constructor
  · intro h
    exact h.trans List.filter_sublist
  · intro h
    simpa [adjacentFilter] using h.filter (fun a => decide (a = k ∨ a = k + 1))

theorem KnuthEquivalent.inverseDescent_iff {u v : List ℕ}
    (h : KnuthEquivalent u v) (hu : u.Nodup) (k : ℕ) :
    [k + 1, k].Sublist u ↔ [k + 1, k].Sublist v := by
  rw [← pair_sublist_adjacentFilter k u, ← pair_sublist_adjacentFilter k v,
    h.adjacentFilter_eq hu k]

def wordCochargeLabel (w : List ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if [i + 1, i].Sublist w then 1 else 0

theorem KnuthEquivalent.wordCochargeLabel_eq {u v : List ℕ}
    (h : KnuthEquivalent u v) (hu : u.Nodup) (j : ℕ) :
    wordCochargeLabel u j = wordCochargeLabel v j := by
  unfold wordCochargeLabel
  apply Finset.sum_congr rfl
  intro i hi
  simp only [h.inverseDescent_iff hu i]

theorem rowBump_map_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : StrictMono f) (x : α) (row : List α) :
    rowBump (f x) (row.map f) =
      ((rowBump x row).1.map f, (rowBump x row).2.map f) := by
  induction row with
  | nil => simp only [List.map_nil, rowBump_nil, List.map_cons, Option.map_none]
  | cons y row ih =>
      by_cases hxy : x < y
      · simp only [List.map_cons, rowBump_cons_of_lt _ hxy,
          rowBump_cons_of_lt _ (hf hxy), Option.map_some]
      · have hfx : f y ≤ f x := hf.monotone (le_of_not_gt hxy)
        simp only [List.map_cons, rowBump_cons_of_le _ (le_of_not_gt hxy),
          rowBump_cons_of_le _ hfx, ih]

theorem rowInsert_map_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : StrictMono f) (x : α) (rows : List (List α)) :
    rowInsert (f x) (rows.map (List.map f)) = (rowInsert x rows).map (List.map f) := by
  induction rows generalizing x with
  | nil => simp only [List.map_nil, rowInsert_nil, List.map_cons]
  | cons row rows ih =>
      simp only [List.map_cons]
      cases h : (rowBump x row).2 with
      | none =>
          have hm : (rowBump (f x) (row.map f)).2 = none := by
            simp only [rowBump_map_strictMono hf, h, Option.map_none]
          rw [rowInsert_cons_of_eq_none _ hm, rowInsert_cons_of_eq_none _ h]
          simp only [List.map_cons, rowBump_map_strictMono hf]
      | some y =>
          have hm : (rowBump (f x) (row.map f)).2 = some (f y) := by
            simp only [rowBump_map_strictMono hf, h, Option.map_some]
          rw [rowInsert_cons_of_eq_some _ hm, rowInsert_cons_of_eq_some _ h]
          simp only [List.map_cons, rowBump_map_strictMono hf, ih]

theorem robinsonSchensted_fst_map_strictMono {α β : Type*}
    [LinearOrder α] [LinearOrder β] {f : α → β} (hf : StrictMono f) (w : List α) :
    (robinsonSchensted (w.map f)).1 = (robinsonSchensted w).1.map (List.map f) := by
  induction w using List.reverseRecOn with
  | nil => simp only [List.map_nil, robinsonSchensted_nil]
  | append_singleton w x ih =>
      simp only [List.map_append, List.map_cons, List.map_nil,
        robinsonSchensted_append_singleton, ih, rowInsert_map_strictMono hf]

theorem word_knuth_robinsonSchensted (w : List ℕ) :
    KnuthEquivalent w (rowWordRows (robinsonSchensted w).1) := by
  induction w using List.reverseRecOn with
  | nil => simpa only [robinsonSchensted_nil, rowWordRows, List.reverse_nil,
      List.flatten_nil] using KnuthEquivalent.refl []
  | append_singleton w x ih =>
      rw [robinsonSchensted_append_singleton]
      exact (ih.append_right [x]).trans (knuth_rowInsert _ x
        (isTableauRows_robinsonSchensted_fst w).sortedLE)

def tableauValueWord {μ : YoungDiagram} (S : StandardYoungTableau μ) : List ℕ :=
  (rowReadingCells μ).map (fun c => (S c).val)

theorem tableauValueWord_eq_rows {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    tableauValueWord S = rowWordRows (S.toRows.map (List.map Fin.val)) := by
  have hrows : fillingRows (fun c => (S c).val) (μ.rowLen 0) =
      S.toRows.map (List.map Fin.val) := by
    unfold fillingRows rowsOfCells
    rw [StandardYoungTableau.toRows_def]
    simp only [List.map_ofFn, Function.comp_def]
    congr 1
    funext r
    have hr : μ.rowLen r ≤ μ.rowLen 0 := μ.rowLen_anti 0 r (Nat.zero_le _)
    simp only [cellsInRow, min_eq_right hr, List.map_ofFn, Function.comp_def, Fin.val_cast]
  rw [tableauValueWord, rowReadingCells_eq_expansion]
  simpa only [rowWordRows, fillingRows, List.map_reverse, List.map_flatten] using
    congrArg rowWordRows hrows

theorem sublist_of_map_injective {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {u v : List α} (h : (u.map f).Sublist (v.map f)) : u.Sublist v := by
  obtain ⟨w, hw, heq⟩ := List.sublist_map_iff.mp h
  have huw : u = w := (List.map_injective_iff.mpr hf) heq
  simpa only [huw] using hw

theorem tableauValueWord_pair_iff {μ : YoungDiagram} (S : StandardYoungTableau μ)
    {i j : Fin μ.card} (hij : i < j) :
    [j.val, i.val].Sublist (tableauValueWord S) ↔
      rowIndex S.toTableau i < rowIndex S.toTableau j := by
  constructor
  · intro h
    have hc : [S.toTableau.symm j, S.toTableau.symm i].Sublist (rowReadingCells μ) := by
      have hf : Function.Injective (fun c : ↥μ.cells => (S c).val) := by
        intro c d hcd
        apply S.toTableau.injective
        simpa only [StandardYoungTableau.toTableau_apply] using Fin.ext hcd
      apply sublist_of_map_injective hf
      simpa only [List.map_cons, List.map_nil, standardTableau_apply_symm,
        tableauValueWord] using h
    have hr := (pairwise_rowReadingCells μ).forall_sublist hc
    have hr' : rowIndex S.toTableau i < rowIndex S.toTableau j ∨
      (rowIndex S.toTableau j = rowIndex S.toTableau i ∧
        colIndex S.toTableau j ≤ colIndex S.toTableau i) := by
      simpa only [rowIndex_def, colIndex_def] using hr
    rcases hr' with hr | ⟨heq, hcol⟩
    · exact hr
    · have hlt := (S.lt_iff_colIndex_lt heq.symm).mp hij
      exact (not_lt_of_ge hcol hlt).elim
  · intro hr
    have h := (pair_sublist_rowReadingCells (c := S.toTableau.symm j)
      (d := S.toTableau.symm i) (by simpa only [rowIndex_def] using hr)).map
        (fun c => (S c).val)
    simpa only [List.map_cons, List.map_nil, standardTableau_apply_symm, tableauValueWord] using h

theorem tableauValueWord_cochargeLabel {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (j : Fin μ.card) : wordCochargeLabel (tableauValueWord S) j.val = cochargeLabel S j := by
  unfold wordCochargeLabel cochargeLabel ascentCount
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i < j.val := Finset.mem_range.mp hi
  have hi0 : i < μ.card := hij.trans j.isLt
  have hi1 : i + 1 < μ.card := (Nat.succ_le_of_lt hij).trans_lt j.isLt
  have hd : [i + 1, i].Sublist (tableauValueWord S) ↔
      rowIndex S.toTableau ⟨i, hi0⟩ < rowIndex S.toTableau ⟨i + 1, hi1⟩ :=
    tableauValueWord_pair_iff S (i := ⟨i, hi0⟩) (j := ⟨i + 1, hi1⟩)
      (Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self i))
  simp only [hd, tableauRows, dif_pos hi0, dif_pos hi1]

def permutationValueWord {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn fun i => (σ i).val

theorem permutationValueWord_nodup {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permutationValueWord σ).Nodup := by
  apply List.pairwise_ofFn.mpr
  intro i j hij heq
  exact hij.ne (σ.injective (Fin.ext heq))

theorem rskPair_left_valueWord_knuth {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    KnuthEquivalent (permutationValueWord σ) (tableauValueWord (rskPair n σ).left) := by
  have hf : StrictMono (@Fin.val n) := fun _ _ h => Fin.lt_iff_val_lt_val.mp h
  rw [tableauValueWord_eq_rows, rskPair_left_rows,
    ← robinsonSchensted_fst_map_strictMono (f := @Fin.val n) hf (List.ofFn σ)]
  simpa only [permutationValueWord, List.map_ofFn, Function.comp_def] using
    word_knuth_robinsonSchensted ((List.ofFn σ).map Fin.val)

/-- RSK preserves the literal inverse-descent cocharge label at every label.
The finite cast only reconciles the insertion tableau's cardinality proof. -/
theorem rskPair_left_cochargeLabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    cochargeLabel (rskPair n σ).left ((finCongr (rskPair n σ).card_eq).symm j) =
      wordCochargeLabel (permutationValueWord σ) j.val := by
  rw [← tableauValueWord_cochargeLabel]
  exact ((rskPair_left_valueWord_knuth σ).wordCochargeLabel_eq
    (permutationValueWord_nodup σ) j.val).symm

theorem rskPair_left_descentNumber {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    descentNumber (rskPair n σ).left =
      wordCochargeLabel (permutationValueWord σ) (n - 1) := by
  by_cases hn : 0 < n
  · let j : Fin n := ⟨n - 1, by omega⟩
    have h := rskPair_left_cochargeLabel σ j
    unfold descentNumber
    rw [(rskPair n σ).card_eq]
    simpa only [cochargeLabel, finCongr_symm_apply_coe, j] using h
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hc : (rskPair n σ).shape.card = 0 := (rskPair n σ).card_eq.trans hn0
    simp [descentNumber, hc, ascentCount, hn0, wordCochargeLabel]

theorem rskPair_left_cochargeDegree {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    cochargeDegree (rskPair n σ).left =
      ∑ j : Fin n, wordCochargeLabel (permutationValueWord σ) j.val := by
  rw [cochargeDegree, ← Equiv.sum_comp (finCongr (rskPair n σ).card_eq).symm]
  exact Finset.sum_congr rfl (fun j _ => rskPair_left_cochargeLabel σ j)

end HigherSpecht
end
end CanonicalSource15

section CanonicalSource16
/- Source: HigherSpecht/EligibleIndexCountWords.lean -/



/-!
# Stable standardization of bounded words

Every finite word is sorted by value, breaking ties by its original position.
Subtracting inverse-descent cocharge along that order gives a nonnegative
increasing sequence. The inverse adds the cocharge labels back. This is the
literal unrestricted word argument needed for the empty-partition harmonic
decomposition. No all-partition catabolizability count follows from this file.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

theorem permutationValueWord_pair_iff {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j : Fin n) : [i.val, j.val].Sublist (permutationValueWord σ) ↔ σ.symm i < σ.symm j := by
  have hp : (List.ofFn σ).Pairwise (fun a b => σ.symm a < σ.symm b) := by
    apply List.pairwise_ofFn.mpr
    intro a b hab
    simpa only [Equiv.symm_apply_apply] using hab
  have hmap : permutationValueWord σ = (List.ofFn σ).map Fin.val := by
    simp only [permutationValueWord, List.map_ofFn, Function.comp_def]
  constructor
  · intro h
    rw [hmap] at h
    have hs : [i, j].Sublist (List.ofFn σ) :=
      sublist_of_map_injective Fin.val_injective (by simpa only [List.map_cons, List.map_nil] using h)
    exact hp.forall_sublist hs
  · intro hij
    have hi : i ∈ List.ofFn σ := List.mem_ofFn.mpr ⟨σ.symm i, σ.apply_symm_apply i⟩
    have hj : j ∈ List.ofFn σ := List.mem_ofFn.mpr ⟨σ.symm j, σ.apply_symm_apply j⟩
    have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
    have hs := pair_sublist_of_pairwise hp hi hj hne (not_lt.mpr hij.le)
    rw [hmap]
    simpa only [List.map_cons, List.map_nil] using hs.map Fin.val

@[simp] theorem wordCochargeLabel_zero (w : List ℕ) : wordCochargeLabel w 0 = 0 := by
  simp [wordCochargeLabel]

theorem wordCochargeLabel_succ (w : List ℕ) (j : ℕ) :
    wordCochargeLabel w (j + 1) = wordCochargeLabel w j +
      if [j + 1, j].Sublist w then 1 else 0 := by
  simp only [wordCochargeLabel, Finset.sum_range_succ]

theorem wordCochargeLabel_mono (w : List ℕ) : Monotone (wordCochargeLabel w) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [wordCochargeLabel_succ]
  exact Nat.le_add_right _ _

def permutationCocharge {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  wordCochargeLabel (permutationValueWord σ) i.val

theorem permutationCocharge_mono {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Monotone (permutationCocharge σ) := fun _ _ h => wordCochargeLabel_mono _ h

theorem permutationCocharge_succ {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    permutationCocharge σ i.succ = permutationCocharge σ i.castSucc +
      if σ.symm i.succ < σ.symm i.castSucc then 1 else 0 := by
  have hd : [i.val + 1, i.val].Sublist (permutationValueWord σ) ↔
      σ.symm i.succ < σ.symm i.castSucc := by
    simpa only [Fin.val_succ, Fin.val_castSucc] using
      permutationValueWord_pair_iff σ i.succ i.castSucc
  simp only [permutationCocharge, Fin.val_succ, Fin.val_castSucc,
    wordCochargeLabel_succ, hd]

def permutationReversePositions {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  if hk : k < n then n - 1 - (σ.symm ⟨k, hk⟩).val else 0

theorem permutationCocharge_eq_ascentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutationCocharge σ i = ascentCount (permutationReversePositions σ) i.val := by
  unfold permutationCocharge wordCochargeLabel ascentCount
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : j < n := (Finset.mem_range.mp hj).trans i.isLt
  have hj1 : j + 1 < n := (Nat.succ_le_of_lt (Finset.mem_range.mp hj)).trans_lt i.isLt
  have h0 := (σ.symm ⟨j, hj0⟩).isLt
  have h1 := (σ.symm ⟨j + 1, hj1⟩).isLt
  have hd : [j + 1, j].Sublist (permutationValueWord σ) ↔
      permutationReversePositions σ j < permutationReversePositions σ (j + 1) := by
    rw [permutationValueWord_pair_iff σ ⟨j + 1, hj1⟩ ⟨j, hj0⟩]
    simp only [Fin.lt_iff_val_lt_val, permutationReversePositions,
      dif_pos hj0, dif_pos hj1]
    omega
  simp only [hd]

theorem position_lt_of_cocharge_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i < j) (hcc : permutationCocharge σ i = permutationCocharge σ j) :
    σ.symm i < σ.symm j := by
  rw [permutationCocharge_eq_ascentCount, permutationCocharge_eq_ascentCount] at hcc
  have h := row_le_of_ascentCount_eq (permutationReversePositions σ) hij.le hcc
  simp only [permutationReversePositions, dif_pos i.isLt, dif_pos j.isLt, Fin.eta] at h
  have hi := (σ.symm i).isLt
  have hj := (σ.symm j).isLt
  have hne : (σ.symm i).val ≠ (σ.symm j).val := by
    intro heq
    exact hij.ne (σ.symm.injective (Fin.ext heq))
  change (σ.symm i).val < (σ.symm j).val
  omega

def StablePositions {n s : ℕ} (u : Fin n → Fin s) (p : Equiv.Perm (Fin n)) : Prop :=
  StrictMono (fun i => toLex (u (p i), p i))

theorem exists_stablePositions {n s : ℕ} (u : Fin n → Fin s) :
    ∃ p : Equiv.Perm (Fin n), StablePositions u p := by
  let f : ULift.{0} (Fin n) → Fin s ×ₗ Fin n := fun i => toLex (u i.down, i.down)
  have hf : Function.Injective f := by
    intro i j hij
    apply ULift.ext
    exact congrArg (fun x : Fin s ×ₗ Fin n => (ofLex x).2) hij
  let e := @Fintype.orderIsoFinOfCardEq (ULift.{0} (Fin n))
    (LinearOrder.lift' f hf) inferInstance n
    ((Fintype.card_ulift (Fin n)).trans (Fintype.card_fin n))
  refine ⟨e.toEquiv.trans Equiv.ulift, ?_⟩
  intro i j hij
  have hle : f (e i) ≤ f (e j) := e.map_rel_iff'.mpr hij.le
  have hnot : ¬ f (e j) ≤ f (e i) :=
    fun h => (not_le_of_gt hij) (e.map_rel_iff'.mp h)
  change f (e i) < f (e j)
  exact lt_iff_le_not_ge.mpr ⟨hle, hnot⟩

def stablePositions {n s : ℕ} (u : Fin n → Fin s) : Equiv.Perm (Fin n) :=
  Classical.choose (exists_stablePositions u)

theorem stablePositions_spec {n s : ℕ} (u : Fin n → Fin s) :
    StablePositions u (stablePositions u) := Classical.choose_spec (exists_stablePositions u)

theorem stablePositions_unique {n s : ℕ} {u : Fin n → Fin s}
    {p q : Equiv.Perm (Fin n)} (hp : StablePositions u p) (hq : StablePositions u q) : p = q := by
  have hm : StrictMono (p.trans q.symm) := by
    intro i j hij
    apply hq.lt_iff_lt.mp
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hp hij
  apply Equiv.ext
  intro i
  have h := hm.apply_eq (x := i)
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg q h

theorem stable_values_step {n s : ℕ} {u : Fin (n + 1) → Fin s}
    {p : Equiv.Perm (Fin (n + 1))} (hp : StablePositions u p) (i : Fin n) :
    (u (p i.castSucc)).val + (if p i.succ < p i.castSucc then 1 else 0) ≤
      (u (p i.succ)).val := by
  have h := Prod.Lex.toLex_lt_toLex.mp (hp i.castSucc_lt_succ)
  by_cases hd : p i.succ < p i.castSucc
  · rw [if_pos hd]
    rcases h with h | ⟨h, hpos⟩
    · exact Nat.succ_le_of_lt h
    · exact (lt_asymm hd hpos).elim
  · rw [if_neg hd, Nat.add_zero]
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg Fin.val h).le

theorem stable_cocharge_le_value {n s : ℕ} {u : Fin n → Fin s}
    {p : Equiv.Perm (Fin n)} (hp : StablePositions u p) (i : Fin n) :
    permutationCocharge p.symm i ≤ (u (p i)).val := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      refine Fin.induction ?_ (fun j ih => ?_) i
      · simp [permutationCocharge]
      · rw [permutationCocharge_succ]
        have h := stable_values_step hp j
        simp only [Equiv.symm_symm]
        exact (Nat.add_le_add_right ih _).trans h

def stableBoost {n s : ℕ} (u : Fin n → Fin s) (i : Fin n) : ℕ :=
  (u (stablePositions u i)).val - permutationCocharge (stablePositions u).symm i

theorem stableBoost_mono {n s : ℕ} (u : Fin n → Fin s) : Monotone (stableBoost u) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have hstep := stable_values_step (stablePositions_spec u) i
      have hcc := permutationCocharge_succ (stablePositions u).symm i
      have hle := stable_cocharge_le_value (stablePositions_spec u) i.castSucc
      have hle' := stable_cocharge_le_value (stablePositions_spec u) i.succ
      simp only [Equiv.symm_symm] at hcc
      unfold stableBoost
      omega

structure BoundedCochargeCode (n s : ℕ) where
  permutation : Equiv.Perm (Fin n)
  boost : Fin n → ℕ
  boost_mono : Monotone boost
  bound : ∀ i, permutationCocharge permutation i + boost i < s

def encodeBoundedWord {n s : ℕ} (u : Fin n → Fin s) : BoundedCochargeCode n s where
  permutation := (stablePositions u).symm
  boost := stableBoost u
  boost_mono := stableBoost_mono u
  bound i := by
    unfold stableBoost
    rw [Nat.add_sub_of_le (stable_cocharge_le_value (stablePositions_spec u) i)]
    exact (u _).isLt

def decodeBoundedWord {n s : ℕ} (c : BoundedCochargeCode n s) : Fin n → Fin s :=
  fun j => ⟨permutationCocharge c.permutation (c.permutation j) +
    c.boost (c.permutation j), c.bound _⟩

theorem decode_encode_boundedWord {n s : ℕ} (u : Fin n → Fin s) :
    decodeBoundedWord (encodeBoundedWord u) = u := by
  funext j
  apply Fin.ext
  change permutationCocharge (stablePositions u).symm ((stablePositions u).symm j) +
      stableBoost u ((stablePositions u).symm j) = (u j).val
  unfold stableBoost
  rw [Nat.add_sub_of_le (stable_cocharge_le_value (stablePositions_spec u) _),
    Equiv.apply_symm_apply]

theorem decoded_stablePositions {n s : ℕ} (c : BoundedCochargeCode n s) :
    StablePositions (decodeBoundedWord c) c.permutation.symm := by
  intro i j hij
  apply Prod.Lex.toLex_lt_toLex.mpr
  have hcc := permutationCocharge_mono c.permutation hij.le
  have hb := c.boost_mono hij.le
  have heval (i : Fin n) : (decodeBoundedWord c (c.permutation.symm i)).val =
      permutationCocharge c.permutation i + c.boost i := by
    simp only [decodeBoundedWord, Equiv.apply_symm_apply]
  by_cases heq : permutationCocharge c.permutation i + c.boost i =
      permutationCocharge c.permutation j + c.boost j
  · right
    refine ⟨Fin.ext (by simpa only [heval] using heq), ?_⟩
    exact position_lt_of_cocharge_eq c.permutation hij (by omega)
  · left
    change (decodeBoundedWord c (c.permutation.symm i)).val <
      (decodeBoundedWord c (c.permutation.symm j)).val
    rw [heval, heval]
    omega

theorem encode_decode_boundedWord {n s : ℕ} (c : BoundedCochargeCode n s) :
    encodeBoundedWord (decodeBoundedWord c) = c := by
  have hp : stablePositions (decodeBoundedWord c) = c.permutation.symm :=
    stablePositions_unique (stablePositions_spec _) (decoded_stablePositions c)
  have hb : stableBoost (decodeBoundedWord c) = c.boost := by
    funext i
    simp only [stableBoost, hp, Equiv.symm_symm, decodeBoundedWord,
      Equiv.apply_symm_apply, Nat.add_sub_cancel_left]
  cases c
  simp only [encodeBoundedWord, hp, Equiv.symm_symm, hb]

def boundedWordCochargeEquiv (n s : ℕ) : (Fin n → Fin s) ≃ BoundedCochargeCode n s where
  toFun := encodeBoundedWord
  invFun := decodeBoundedWord
  left_inv := decode_encode_boundedWord
  right_inv := encode_decode_boundedWord

theorem card_boundedCochargeCode (n s : ℕ) : Nat.card (BoundedCochargeCode n s) = s ^ n := by
  rw [← Nat.card_congr (boundedWordCochargeEquiv n s), Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_fin]

end HigherSpecht
end
end CanonicalSource16

section CanonicalSource17
/- Source: HigherSpecht/CatGreedyCocharge.lean -/



/-!
# Cocharge under the genuine first greedy rotation

The initial bottom-row interval is deleted and the two remaining word blocks
are exchanged.  The cocharge labels on the old upper block decrease by one;
those on the old bottom block remain unchanged.  All assertions below concern
the literal inverse-descent statistic on lists, with explicit support and
disjointness facts, and are independent of a catabolizability characterization.
-/

noncomputable section

open TauCeti Finset

namespace HigherSpecht

theorem pair_sublist_append_iff {a b : ℕ} (u v : List ℕ) :
    [a, b].Sublist (u ++ v) ↔
      [a, b].Sublist u ∨ (a ∈ u ∧ b ∈ v) ∨ [a, b].Sublist v := by
  induction u with
  | nil => simp
  | cons c u ih =>
    simp only [List.cons_append, List.sublist_cons_iff, List.cons.injEq,
      List.singleton_sublist, List.mem_append, List.mem_cons] at ih ⊢
    aesop

theorem not_pair_sublist_of_notMem_left {a b : ℕ} {w : List ℕ} (ha : a ∉ w) :
    ¬ [a, b].Sublist w := fun h => ha (h.subset (by simp))

theorem not_pair_sublist_of_notMem_right {a b : ℕ} {w : List ℕ} (hb : b ∉ w) :
    ¬ [a, b].Sublist w := fun h => hb (h.subset (by simp))

theorem reverse_pair_not_sublist_range (j m : ℕ) :
    ¬ [j + 1, j].Sublist (List.range m) := by
  intro h
  have hp := (@List.pairwise_lt_range m).forall_sublist h
  simpa using hp

theorem pair_sublist_remove_middle {a b : ℕ} (u middle v : List ℕ)
    (ha : a ∉ middle) (hb : b ∉ middle) :
    [a, b].Sublist (u ++ middle ++ v) ↔ [a, b].Sublist (u ++ v) := by
  simp only [pair_sublist_append_iff, List.mem_append]
  simp [ha, hb, not_pair_sublist_of_notMem_left ha]

theorem wordCochargeLabel_eq_zero_of_lowerBound {w : List ℕ} {m j : ℕ}
    (hw : ∀ a ∈ w, m ≤ a) (hj : j ≤ m) : wordCochargeLabel w j = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have him : i < m := (Finset.mem_range.mp hi).trans_le hj
  have hnot : i ∉ w := fun h => (not_lt_of_ge (hw i h)) him
  simp [not_pair_sublist_of_notMem_right hnot]

theorem wordCochargeLabel_initial_interval {upper bottom : List ℕ} {m j : ℕ}
    (hupper : ∀ a ∈ upper, m ≤ a) (hbottom : ∀ a ∈ bottom, m ≤ a)
    (hj : j < m) :
    wordCochargeLabel (upper ++ List.range m ++ bottom) j = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i < j := Finset.mem_range.mp hi
  have hiU : i ∉ upper := fun h => (not_lt_of_ge (hupper i h)) (by omega)
  have hiB : i ∉ bottom := fun h => (not_lt_of_ge (hbottom i h)) (by omega)
  have hi1U : i + 1 ∉ upper := fun h => (not_lt_of_ge (hupper (i + 1) h)) (by omega)
  have hnot : ¬ [i + 1, i].Sublist (upper ++ List.range m ++ bottom) := by
    simp only [pair_sublist_append_iff, List.mem_append]
    simp [hiU, hiB, hi1U, not_pair_sublist_of_notMem_right hiU,
      not_pair_sublist_of_notMem_right hiB, reverse_pair_not_sublist_range]
  have hnot' : ¬ [i + 1, i].Sublist (upper ++ (List.range m ++ bottom)) := by
    simpa only [List.append_assoc] using hnot
  simp [hnot']

theorem wordCochargeLabel_first_upper {upper bottom : List ℕ} {m : ℕ}
    (hm : 0 < m) (hupper : ∀ a ∈ upper, m ≤ a)
    (hbottom : ∀ a ∈ bottom, m ≤ a) (hmupper : m ∈ upper) :
    wordCochargeLabel (upper ++ List.range m ++ bottom) m = 1 := by
  have hzero := wordCochargeLabel_initial_interval hupper hbottom
    (j := m - 1) (by omega)
  have hpair : [m, m - 1].Sublist (upper ++ List.range m ++ bottom) := by
    apply (pair_sublist_append_iff (upper ++ List.range m) bottom).mpr
    apply Or.inl
    apply (pair_sublist_append_iff upper (List.range m)).mpr
    exact Or.inr (Or.inl ⟨hmupper, List.mem_range.mpr (by omega)⟩)
  have hs := wordCochargeLabel_succ (upper ++ List.range m ++ bottom) (m - 1)
  rw [Nat.sub_add_cancel hm, hzero, if_pos hpair, Nat.zero_add] at hs
  exact hs

theorem pair_sublist_swap_blocks_same {a b : ℕ} (upper bottom : List ℕ)
    (ha : a ∉ bottom) (hb : b ∉ bottom) :
    [a, b].Sublist (upper ++ bottom) ↔ [a, b].Sublist (bottom ++ upper) := by
  simp only [pair_sublist_append_iff]
  simp [ha, hb, not_pair_sublist_of_notMem_left ha]

theorem pair_sublist_swap_blocks_cross {a b : ℕ} (upper bottom : List ℕ)
    (haU : a ∈ upper) (haB : a ∉ bottom) (hbU : b ∉ upper) (hbB : b ∈ bottom) :
    [a, b].Sublist (upper ++ bottom) ∧ ¬ [a, b].Sublist (bottom ++ upper) := by
  simp only [pair_sublist_append_iff]
  simp [haU, haB, hbU, hbB, not_pair_sublist_of_notMem_right hbU,
    not_pair_sublist_of_notMem_left haB]

/-- The exact cocharge shift caused by deleting the first interval and
rotating the remaining bottom block before the upper block. -/
theorem wordCochargeLabel_greedy_rotation {upper bottom : List ℕ} {m n : ℕ}
    (hm : 0 < m) (hmn : m < n)
    (hupper : ∀ a ∈ upper, m ≤ a) (hbottom : ∀ a ∈ bottom, m ≤ a)
    (hdisjoint : ∀ a ∈ upper, a ∉ bottom)
    (hsupport : ∀ a, m ≤ a → a < n → a ∈ upper ∨ a ∈ bottom)
    (hmupper : m ∈ upper) {j : ℕ} (hmj : m ≤ j) (hjn : j < n) :
    wordCochargeLabel (upper ++ List.range m ++ bottom) j =
      wordCochargeLabel (bottom ++ upper) j + if j ∈ upper then 1 else 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmj
  revert hjn
  induction t with
  | zero =>
    intro hjn
    have hzero : wordCochargeLabel (bottom ++ upper) m = 0 :=
      wordCochargeLabel_eq_zero_of_lowerBound
        (fun a ha => (List.mem_append.mp ha).elim (hbottom a) (hupper a)) le_rfl
    simpa only [Nat.add_zero, wordCochargeLabel_first_upper hm hupper hbottom hmupper,
      hzero, if_pos hmupper, Nat.zero_add]
  | succ t ih =>
    intro hjn
    have ht : m + t < n := by omega
    have ih' := ih (by omega) ht
    have hjUorB := hsupport (m + t) (by omega) ht
    have hkUorB := hsupport (m + t + 1) (by omega) (by omega)
    have hjR : m + t ∉ List.range m := by simp
    have hkR : m + t + 1 ∉ List.range m := by
      simp only [List.mem_range]
      omega
    rw [show m + (t + 1) = m + t + 1 by omega,
      wordCochargeLabel_succ, wordCochargeLabel_succ, ih']
    simp only [pair_sublist_remove_middle upper (List.range m) bottom hkR hjR]
    by_cases hjU : m + t ∈ upper <;> by_cases hkU : m + t + 1 ∈ upper
    · have hjB := hdisjoint _ hjU
      have hkB := hdisjoint _ hkU
      simp only [pair_sublist_swap_blocks_same upper bottom hkB hjB,
        if_pos hjU, if_pos hkU]
      omega
    · have hjB := hdisjoint _ hjU
      have hkB : m + t + 1 ∈ bottom := hkUorB.resolve_left hkU
      have hp := pair_sublist_swap_blocks_cross bottom upper hkB hkU hjB hjU
      simp only [if_pos hjU, if_neg hkU, if_pos hp.1, if_neg hp.2]
    · have hjB : m + t ∈ bottom := hjUorB.resolve_left hjU
      have hkB := hdisjoint _ hkU
      have hp := pair_sublist_swap_blocks_cross upper bottom hkU hkB hjU hjB
      simp only [if_neg hjU, if_pos hkU, if_pos hp.1, if_neg hp.2]
    · have hsame := pair_sublist_swap_blocks_same bottom upper hkU hjU
      simp only [hsame.symm, if_neg hjU, if_neg hkU, Nat.add_zero]

/-- Lowering a word whose alphabet starts at `m` removes only absent inverse
descent tests. It does not alter the cocharge labels of its remaining letters. -/
theorem wordCochargeLabel_map_add (w : List ℕ) (m j : ℕ) :
    wordCochargeLabel (w.map (· + m)) (j + m) = wordCochargeLabel w j := by
  induction j with
  | zero =>
    simpa only [Nat.zero_add, wordCochargeLabel_zero] using
      wordCochargeLabel_eq_zero_of_lowerBound
        (w := w.map (· + m)) (m := m) (j := m)
        (by intro a ha; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; omega) le_rfl
  | succ j ih =>
    rw [show j + 1 + m = j + m + 1 by omega, wordCochargeLabel_succ,
      wordCochargeLabel_succ, ih]
    have heq : [j + m + 1, j + m].Sublist (w.map (· + m)) ↔
        [j + 1, j].Sublist w := by
      constructor
      · intro h
        exact sublist_of_map_injective (f := fun a : ℕ => a + m)
          (fun a b h => Nat.add_right_cancel h)
          (by simpa only [List.map_cons, List.map_nil, Nat.add_assoc, Nat.add_comm 1 m] using h)
      · intro h
        simpa only [List.map_cons, List.map_nil, Nat.add_assoc, Nat.add_comm 1 m] using
          h.map (· + m)
    simp only [heq]

end HigherSpecht
end
end CanonicalSource17

section CanonicalSource18
/- Source: HigherSpecht/StandardWordCocharge.lean -/



/-!
# Cocharge-labelled standard words and Schensted insertion

The conversion from a literal permutation word to a finite permutation keeps
every position.  A reversed pair forces a strict increase of its cocharge
labels, which is the strictness needed to transport ordinary Knuth moves to
the labelled words used by the cyclic insertion algorithm.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

def permutationOfStandardWord {n : ℕ} (w : List ℕ) (hw : w.Perm (List.range n)) :
    Equiv.Perm (Fin n) := by
  have hlen : w.length = n := by simpa only [List.length_range] using hw.length_eq
  let f : Fin n → Fin n := fun i =>
    ⟨w.get ⟨i.val, by simpa only [hlen] using i.isLt⟩,
      List.mem_range.mp (hw.subset (List.get_mem w _))⟩
  have hf : Injective f := by
    intro i j hij
    have hget := (hw.nodup_iff.mpr List.nodup_range).injective_get
      (congrArg Fin.val hij)
    exact Fin.ext (congrArg (fun z : Fin w.length => z.val) hget)
  exact Equiv.ofBijective f hf.bijective_of_finite

theorem permutationValueWord_permutationOfStandardWord {n : ℕ} (w : List ℕ)
    (hw : w.Perm (List.range n)) :
    permutationValueWord (permutationOfStandardWord w hw) = w := by
  have hlen : w.length = n := by simpa only [List.length_range] using hw.length_eq
  change List.ofFn (fun i : Fin n => w.get (Fin.cast hlen.symm i)) = w
  rw [← List.ofFn_congr hlen w.get, List.ofFn_get]

def labelledWord (w : List ℕ) : List ℕ := w.map (wordCochargeLabel w)

theorem labelledWord_tableau {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    labelledWord (tableauValueWord S) = cochargeWord S := by
  unfold labelledWord tableauValueWord cochargeWord
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact tableauValueWord_cochargeLabel S (S c)

theorem wordCochargeLabel_strict_of_reverse_pair {n a b : ℕ} {w : List ℕ}
    (hw : w.Perm (List.range n)) (hab : a < b) (hp : [b, a].Sublist w) :
    wordCochargeLabel w a < wordCochargeLabel w b := by
  have ha : a < n := List.mem_range.mp (hw.subset (hp.subset (by simp)))
  have hb : b < n := List.mem_range.mp (hw.subset (hp.subset (by simp)))
  let sigma := permutationOfStandardWord w hw
  have hsigma : permutationValueWord sigma = w :=
    permutationValueWord_permutationOfStandardWord w hw
  have hle := wordCochargeLabel_mono w hab.le
  by_contra hnot
  have heq : wordCochargeLabel w a = wordCochargeLabel w b := by omega
  have hcc : permutationCocharge sigma ⟨a, ha⟩ = permutationCocharge sigma ⟨b, hb⟩ := by
    simpa only [permutationCocharge, hsigma] using heq
  have hpos := position_lt_of_cocharge_eq sigma (show (⟨a, ha⟩ : Fin n) < ⟨b, hb⟩ from hab) hcc
  have hrev := (permutationValueWord_pair_iff sigma ⟨b, hb⟩ ⟨a, ha⟩).mp
    (by simpa only [hsigma] using hp)
  exact (lt_asymm hpos hrev).elim

theorem labelledWord_map_congr_of_knuth {u v : List ℕ}
    (h : KnuthEquivalent u v) (hu : u.Nodup) :
    v.map (wordCochargeLabel u) = labelledWord v := by
  apply List.map_congr_left
  intro a ha
  exact h.wordCochargeLabel_eq hu a

/-- Ordinary Knuth equivalence of permutation words induces genuine Knuth
equivalence of their cocharge-labelled words. The strict inequality in each
elementary relation is proved from the reversed value pair in that relation. -/
theorem KnuthEquivalent.labelledWord {u v : List ℕ} (h : KnuthEquivalent u v)
    (l r : List ℕ) {n : ℕ} (hu : (l ++ u ++ r).Perm (List.range n)) :
    KnuthEquivalent (labelledWord (l ++ u ++ r)) (labelledWord (l ++ v ++ r)) := by
  induction h generalizing l r with
  | refl u => exact .refl _
  | symm h ih =>
    exact (ih l r (((h.perm.append_left l).append_right r).trans hu)).symm
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ l r hu).trans (ih₂ l r
      (((h₁.perm.append_left l).append_right r).symm.trans hu))
  | append l' r' h ih =>
    simpa only [List.append_assoc] using ih (l ++ l') (r' ++ r)
      (by simpa only [List.append_assoc] using hu)
  | @left a b c hab hbc =>
    let w := l ++ [b, a, c] ++ r
    let d := wordCochargeLabel w
    have hp : [b, a].Sublist w := by
      have hp0 : [b, a].Sublist [b, a, c] := List.sublist_append_left [b, a] [c]
      exact List.sublist_append_of_sublist_left (List.sublist_append_of_sublist_right hp0)
    have hda : d a < d b := wordCochargeLabel_strict_of_reverse_pair hu hab hp
    have hdc : d b ≤ d c := wordCochargeLabel_mono w hbc
    have hmove := (KnuthEquivalent.left hda hdc).append
      (l.map d) (r.map d)
    have hwhole : KnuthEquivalent w (l ++ [b, c, a] ++ r) :=
      (KnuthEquivalent.left hab hbc).append l r
    have hn : w.Nodup := hu.nodup_iff.mpr List.nodup_range
    rw [← labelledWord_map_congr_of_knuth hwhole hn]
    simpa only [HigherSpecht.labelledWord, List.map_append, List.map_cons, List.map_nil,
      d, w] using hmove
  | @right a b c hab hbc =>
    let w := l ++ [a, c, b] ++ r
    let d := wordCochargeLabel w
    have hp : [c, b].Sublist w := by
      have hp0 : [c, b].Sublist [a, c, b] := (List.Sublist.refl [c, b]).cons a
      exact List.sublist_append_of_sublist_left (List.sublist_append_of_sublist_right hp0)
    have hda : d a ≤ d b := wordCochargeLabel_mono w hab
    have hdc : d b < d c := wordCochargeLabel_strict_of_reverse_pair hu hbc hp
    have hmove := (KnuthEquivalent.right hda hdc).append
      (l.map d) (r.map d)
    have hwhole : KnuthEquivalent w (l ++ [c, a, b] ++ r) :=
      (KnuthEquivalent.right hab hbc).append l r
    have hn : w.Nodup := hu.nodup_iff.mpr List.nodup_range
    rw [← labelledWord_map_congr_of_knuth hwhole hn]
    simpa only [HigherSpecht.labelledWord, List.map_append, List.map_cons, List.map_nil,
      d, w] using hmove

/-- The cocharge word of the actual Schensted insertion tableau has the same
cyclic output as the literal cocharge-labelled input word. -/
theorem catWordOutput_labelledWord_rsk {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (nu : YoungDiagram) :
    CatWordOutput (labelledWord (permutationValueWord sigma)) nu ↔
      CatTableauOutput (rskPair n sigma).left nu := by
  have hm : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  have hperm : (permutationValueWord sigma).Perm (List.range n) := by
    simpa only [permutationValueWord, List.ofFn_eq_map, List.map_map,
      Function.comp_def, hm] using sigma.map_finRange_perm.map Fin.val
  have hk := (rskPair_left_valueWord_knuth sigma).labelledWord [] []
    (by simpa only [List.nil_append, List.append_nil] using hperm)
  simp only [List.nil_append, List.append_nil, labelledWord_tableau] at hk
  exact catWordOutput_knuth_iff hk nu

end HigherSpecht
end
end CanonicalSource18

section CanonicalSource19
/- Source: HigherSpecht/LascouxCochargeCapacity.lean -/



/-!
# The actual cocharge filling and its first-row capacity

For a standard-content semistandard tableau, the cocharge labels of its
literal row word form another semistandard tableau of the same shape.
Entries in a higher-index row precede those above them in the reading;
column strictness therefore gives a reversed pair with strictly increasing
cocharge labels.  The ordinary column-count bound then limits the number
of zero labels by the first-row width.
-/

noncomputable section

namespace HigherSpecht.Lascoux

theorem descendingRows_pair_sublist {h r s : ℕ} (hrs : r < s) (hs : s < h) :
    [s, r].Sublist (descendingRows h) := by
  induction h with
  | zero => omega
  | succ h ih =>
      by_cases hsh : s = h
      · subst s
        change [h, r].Sublist (h :: descendingRows h)
        exact (List.singleton_sublist.mpr (mem_descendingRows.mpr hrs)).cons₂ h
      · have hsmall : s < h := by omega
        exact (ih hsmall).cons h

theorem tableauRowWord_entry_mem {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {r j : ℕ} (hcell : (r, j) ∈ mu) :
    T r j ∈ tableauRowWord T r := by
  have hj : j < (tableauRowWord T r).length := by
    rw [tableauRowWord_length]
    exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
  rw [← tableauRowWord_getElem T r j hj]
  exact List.getElem_mem hj

/-- The pair is a literal sublist in the paper's bottom-to-top row
reading, before any insertion or Knuth equivalence is applied. -/
theorem tableauWord_reverse_pair {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {r s j k : ℕ} (hrs : r < s)
    (hrj : (r, j) ∈ mu) (hsk : (s, k) ∈ mu) :
    [T s k, T r j].Sublist (tableauWord T) := by
  have hs : s < mu.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
    (mu.up_left_mem le_rfl (Nat.zero_le k) hsk)
  have hrows : (tableauRowWord T s ++ tableauRowWord T r).Sublist (tableauWord T) := by
    simpa only [tableauWord, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      (descendingRows_pair_sublist hrs hs).flatMap (tableauRowWord T)
  have hleft := List.singleton_sublist.mpr (tableauRowWord_entry_mem T hsk)
  have hright := List.singleton_sublist.mpr (tableauRowWord_entry_mem T hrj)
  exact (hleft.append hright).trans hrows

def cochargeTableau {mu : YoungDiagram} {M : ℕ}
    (T : SemistandardYoungTableau mu) (hw : (tableauWord T).Perm (List.range M)) :
    SemistandardYoungTableau mu where
  entry r j := wordCochargeLabel (tableauWord T) (T r j)
  row_weak' {r j k} hjk hcell :=
    wordCochargeLabel_mono (tableauWord T) (T.row_weak hjk hcell)
  col_strict' {r s j} hrs hcell :=
    wordCochargeLabel_strict_of_reverse_pair hw (T.col_strict hrs hcell)
      (tableauWord_reverse_pair T hrs (mu.up_left_mem hrs.le le_rfl hcell) hcell)
  zeros' {r j} hcell := by
    rw [T.zeros hcell, wordCochargeLabel_zero]

@[simp] theorem cochargeTableau_apply {mu : YoungDiagram} {M : ℕ}
    (T : SemistandardYoungTableau mu) (hw : (tableauWord T).Perm (List.range M))
    (r j : ℕ) :
    cochargeTableau T hw r j = wordCochargeLabel (tableauWord T) (T r j) := rfl

theorem cochargeTableau_word {mu : YoungDiagram} {M : ℕ}
    (T : SemistandardYoungTableau mu) (hw : (tableauWord T).Perm (List.range M)) :
    tableauWord (cochargeTableau T hw) = labelledWord (tableauWord T) := by
  rw [tableauWord_eq_map_cells (cochargeTableau T hw), labelledWord,
    tableauWord_eq_map_cells T, List.map_map]
  simp only [cochargeTableau_apply, tableauWord_eq_map_cells T, Function.comp_def]

/-- The capacity hypothesis needed by the actual greedy catabolism
step follows from the actual tableau, without a separate bound premise. -/
theorem labelledWord_zero_count_le_width {mu : YoungDiagram} {M : ℕ}
    (T : SemistandardYoungTableau mu) (hw : (tableauWord T).Perm (List.range M)) :
    (labelledWord (tableauWord T)).count 0 ≤ mu.rowLen 0 := by
  rw [← cochargeTableau_word T hw, tableauWord_count_eq_contentCells]
  exact contentCells_card_le_width (cochargeTableau T hw) 0

end HigherSpecht.Lascoux
end
end CanonicalSource19

section CanonicalSource20
/- Source: HigherSpecht/BatteryRectangle.lean -/



/-!
# The literal rectangular battery and its cocharge filling

The empty-width and empty-height cases use the actual empty Young diagram.
The cocharge filling is calculated from the complete standard word, whose
pre need not be a tableau word.  Its suffix has its original rectangular
shape, with strict columns proved from literal reversed value pairs.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def batteryRectangle (h d : ℕ) : YoungDiagram where
  cells := (Finset.range h).product (Finset.range d)
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_range] at hb ⊢
    exact ⟨hab.1.trans_lt hb.1, hab.2.trans_lt hb.2⟩

@[simp] theorem mem_batteryRectangle {h d r j : ℕ} :
    (r, j) ∈ batteryRectangle h d ↔ r < h ∧ j < d := by
  change (r, j) ∈ (Finset.range h).product (Finset.range d) ↔ _
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]

@[simp] theorem batteryRectangle_card (h d : ℕ) :
    (batteryRectangle h d).card = h * d := by
  simp only [YoungDiagram.card, batteryRectangle, Finset.product_eq_sprod,
    Finset.card_product, Finset.card_range]

theorem batteryRectangle_rowLen (h d r : ℕ) :
    (batteryRectangle h d).rowLen r = if r < h then d else 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_batteryRectangle]
  split_ifs with hr <;> simp only [hr, true_and, false_and, Nat.not_lt_zero]

theorem batteryRectangle_colLen (h d j : ℕ) :
    (batteryRectangle h d).colLen j = if j < d then h else 0 := by
  apply eq_of_forall_lt_iff
  intro r
  rw [← YoungDiagram.mem_iff_lt_colLen, mem_batteryRectangle]
  split_ifs with hj <;> simp only [hj, and_true, and_false, Nat.not_lt_zero]

theorem batteryRectangle_height_le (h d : ℕ) :
    (batteryRectangle h d).colLen 0 ≤ h := by
  rw [batteryRectangle_colLen]
  split_ifs <;> omega

theorem batteryRowWord_eq_ofFn {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d)) (r : Fin h) :
    tableauRowWord T r = List.ofFn (fun j : Fin d => T r j) := by
  apply List.ext_getElem
  · simp only [tableauRowWord_length, batteryRectangle_rowLen, r.isLt, if_true,
      List.length_ofFn]
  · intro j hj hj'
    rw [tableauRowWord_getElem, List.getElem_ofFn]

theorem batteryWord_eq_rows {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d)) :
    tableauWord T =
      (List.ofFn (fun r : Fin h => List.ofFn (fun j : Fin d => T r j))).reverse.flatten := by
  rw [← tableauWord_withHeight T h (batteryRectangle_height_le h d)]
  have hrows : (List.range h).map (tableauRowWord T) =
      List.ofFn (fun r : Fin h => List.ofFn (fun j : Fin d => T r j)) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_ofFn]
    · intro r hr hr'
      have hrh : r < h := by simpa only [List.length_ofFn] using hr'
      simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
        batteryRowWord_eq_ofFn T ⟨r, hrh⟩
  simpa only [descendingRows_eq_reverse_range, List.flatMap_def,
    List.map_reverse, hrows]

def suffixCochargeTableau {mu : YoungDiagram} {N : ℕ}
    (T : SemistandardYoungTableau mu) (pre : List ℕ)
    (hw : (pre ++ tableauWord T).Perm (List.range N)) :
    SemistandardYoungTableau mu where
  entry r j := wordCochargeLabel (pre ++ tableauWord T) (T r j)
  row_weak' {r j k} hjk hcell :=
    wordCochargeLabel_mono _ (T.row_weak hjk hcell)
  col_strict' {r s j} hrs hcell := by
    apply wordCochargeLabel_strict_of_reverse_pair hw (T.col_strict hrs hcell)
    exact (tableauWord_reverse_pair T hrs
      (mu.up_left_mem hrs.le le_rfl hcell) hcell).trans (List.sublist_append_right _ _)
  zeros' {r j} hcell := by
    rw [T.zeros hcell, wordCochargeLabel_zero]

@[simp] theorem suffixCochargeTableau_apply {mu : YoungDiagram} {N : ℕ}
    (T : SemistandardYoungTableau mu) (pre : List ℕ)
    (hw : (pre ++ tableauWord T).Perm (List.range N)) (r j : ℕ) :
    suffixCochargeTableau T pre hw r j =
      wordCochargeLabel (pre ++ tableauWord T) (T r j) := rfl

theorem labelledWord_tableau_suffix {mu : YoungDiagram} {N : ℕ}
    (T : SemistandardYoungTableau mu) (pre : List ℕ)
    (hw : (pre ++ tableauWord T).Perm (List.range N)) :
    labelledWord (pre ++ tableauWord T) =
      pre.map (wordCochargeLabel (pre ++ tableauWord T)) ++
        tableauWord (suffixCochargeTableau T pre hw) := by
  rw [labelledWord, List.map_append, tableauWord_eq_map_cells T,
    tableauWord_eq_map_cells (suffixCochargeTableau T pre hw), List.map_map]
  simp only [suffixCochargeTableau_apply, tableauWord_eq_map_cells T, Function.comp_def]

end HigherSpecht.Lascoux
end
end CanonicalSource20

section CanonicalSource21
/- Source: HigherSpecht/RowMajorPrefix.lean -/



/-!
# The literal row-major prefixes of a rectangle

The cell numbered `k` is `(k / d, k % d)`.  The next cell is genuinely
addable to the prefix Young diagram; no statement about the insertion
algorithm is included in the definition of this diagram.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def rowMajorPrefix (d k : ℕ) : YoungDiagram where
  cells := ((range (k + 1)).product (range d)).filter (fun c => c.1 * d + c.2 < k)
  isLowerSet := by
    intro a b hab hb
    simp only [mem_coe, mem_filter, Finset.product_eq_sprod, mem_product, mem_range] at hb ⊢
    refine ⟨⟨hab.1.trans_lt hb.1.1, hab.2.trans_lt hb.1.2⟩, ?_⟩
    exact (Nat.add_le_add (Nat.mul_le_mul_right d hab.1) hab.2).trans_lt hb.2

@[simp] theorem mem_rowMajorPrefix {d k r j : ℕ} :
    (r, j) ∈ rowMajorPrefix d k ↔ j < d ∧ r * d + j < k := by
  change ((r, j) ∈ ((range (k + 1)).product (range d)).filter
    (fun c => c.1 * d + c.2 < k)) ↔ _
  simp only [mem_filter, Finset.product_eq_sprod, mem_product, mem_range]
  constructor
  · rintro ⟨⟨_, hj⟩, hkey⟩
    exact ⟨hj, hkey⟩
  · rintro ⟨hj, hkey⟩
    have hd : 1 ≤ d := by omega
    have hrd : r ≤ r * d := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left r hd
    exact ⟨⟨by omega, hj⟩, hkey⟩

@[simp] theorem rowMajorPrefix_zero (d : ℕ) : rowMajorPrefix d 0 = ⊥ := by
  apply YoungDiagram.ext
  ext c
  rcases c with ⟨r, j⟩
  change (r, j) ∈ rowMajorPrefix d 0 ↔ (r, j) ∈ (⊥ : YoungDiagram)
  simp only [mem_rowMajorPrefix, Nat.not_lt_zero, and_false, YoungDiagram.notMem_bot]

 theorem rowMajorPrefix_rowLen_next {d : ℕ} (hd : 0 < d) (k : ℕ) :
    (rowMajorPrefix d k).rowLen (k / d) = k % d := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowMajorPrefix]
  have hmod := Nat.mod_lt k hd
  have hkey : k / d * d + k % d = k := by
    simpa only [Nat.mul_comm d (k / d)] using Nat.div_add_mod k d
  omega

 theorem rowMajorPrefix_next_addable {d : ℕ} (hd : 0 < d) (k : ℕ) :
    YoungDiagram.IsAddable (rowMajorPrefix d k) (k / d, k % d) := by
  rw [YoungDiagram.isAddable_iff_rowLen]
  refine ⟨(rowMajorPrefix_rowLen_next hd k).symm, ?_⟩
  intro r hr
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowMajorPrefix]
  refine ⟨Nat.mod_lt k hd, ?_⟩
  have hkey : k / d * d + k % d = k := by
    simpa only [Nat.mul_comm d (k / d)] using Nat.div_add_mod k d
  rw [hr, Nat.add_mul, Nat.one_mul] at hkey
  omega

 theorem rowMajorPrefix_addCell {d : ℕ} (hd : 0 < d) (k : ℕ) :
    (rowMajorPrefix d k).addCell (k / d, k % d) = rowMajorPrefix d (k + 1) := by
  apply YoungDiagram.ext
  rw [(rowMajorPrefix_next_addable hd k).cells_addCell_eq_insert]
  ext c
  rcases c with ⟨r, j⟩
  simp only [mem_insert]
  change ((r, j) = (k / d, k % d) ∨ (r, j) ∈ rowMajorPrefix d k) ↔
    (r, j) ∈ rowMajorPrefix d (k + 1)
  rw [mem_rowMajorPrefix, mem_rowMajorPrefix]
  constructor
  · rintro (heq | ⟨hj, hk⟩)
    · cases heq
      have hkey : k / d * d + k % d = k := by
        simpa only [Nat.mul_comm d (k / d)] using Nat.div_add_mod k d
      exact ⟨Nat.mod_lt k hd, by omega⟩
    · exact ⟨hj, by omega⟩
  · rintro ⟨hj, hk⟩
    by_cases hlt : r * d + j < k
    · exact Or.inr ⟨hj, hlt⟩
    · have he : r * d + j = k := by omega
      have hdiv : k / d = r := by
        rw [← he, Nat.add_comm (r * d) j, Nat.add_mul_div_right _ _ hd,
          Nat.div_eq_of_lt hj, Nat.zero_add]
      have hmod : k % d = j := by
        rw [← he, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
      exact Or.inl (Prod.ext hdiv.symm hmod.symm)

 theorem rowMajorPrefix_full (h d : ℕ) :
    rowMajorPrefix d (h * d) = Lascoux.batteryRectangle h d := by
  apply YoungDiagram.ext
  ext c
  rcases c with ⟨r, j⟩
  change (r, j) ∈ rowMajorPrefix d (h * d) ↔
    (r, j) ∈ Lascoux.batteryRectangle h d
  rw [mem_rowMajorPrefix, Lascoux.mem_batteryRectangle]
  constructor
  · rintro ⟨hj, hk⟩
    refine ⟨?_, hj⟩
    by_contra hn
    have hm := Nat.mul_le_mul_right d (Nat.le_of_not_gt hn)
    omega
  · rintro ⟨hr, hj⟩
    have hm' := Nat.mul_le_mul_right d (show r + 1 ≤ h by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm'
    exact ⟨hj, by omega⟩

end HigherSpecht
end
end CanonicalSource21

section CanonicalSource22
/- Source: HigherSpecht/HanadaScheduledFilling.lean -/



/-!
# The scheduled-filling invariant for Hanada's shuffle argument

An entry records its visit number and its original reading position.  Its
row is its initial cocharge label plus that visit number.  The accepted
Young diagram consists exactly of entries earlier than the present visit.

The rejection case below is proved directly: if the token were scheduled
at its present visit, all cells strictly below it would already be filled,
so it would be addable.  The early-insertion exchange is a separate missing
obligation.  This file asserts no shuffle-dominance or cardinality theorem.
-/

noncomputable section
open TauCeti Set
open scoped Classical

namespace HigherSpecht

abbrev VisitTime (n : ℕ) := ℕ ×ₗ Fin n

def visitTime {n : ℕ} (p : ℕ) (i : Fin n) : VisitTime n := toLex (p, i)

/-- The row/visit identity rules out equal visit pairs in different rows,
including when a route has displaced the same token more than once. -/
theorem visitTime_ne_of_row_ne {n : ℕ} (a : Fin n → ℕ)
    {p q r s : ℕ} {i j : Fin n}
    (hr : r = a i + p) (hs : s = a j + q) (hrs : r ≠ s) :
    visitTime p i ≠ visitTime q j := by
  intro h
  have hpq : (p, i) = (q, j) := congrArg ofLex h
  have hp : p = q := congrArg Prod.fst hpq
  have hij : i = j := congrArg Prod.snd hpq
  apply hrs
  rw [hr, hs, hp, hij]

/-- A weak comparison between visit pairs in distinct rows is automatically
strict. This supplies the strict-input premise of the adjacent-row routine
from the actual route's row identities. -/
theorem visitTime_lt_of_le_of_row_ne {n : ℕ} (a : Fin n → ℕ)
    {p q r s : ℕ} {i j : Fin n}
    (hr : r = a i + p) (hs : s = a j + q) (hrs : r ≠ s)
    (h : visitTime p i ≤ visitTime q j) : visitTime p i < visitTime q j :=
  lt_of_le_of_ne h (visitTime_ne_of_row_ne a hr hs hrs)

structure ScheduledFilling {n : ℕ} (initialLabel : Fin n → ℕ) where
  shape : YoungDiagram
  token : ↥shape.cells ≃ Fin n
  visit : Fin n → ℕ
  row_eq : ∀ c : ↥shape.cells, c.val.1 = initialLabel (token c) + visit (token c)
  time_strict : ∀ c d : ↥shape.cells, c.val < d.val →
    visitTime (visit (token c)) (token c) < visitTime (visit (token d)) (token d)

namespace ScheduledFilling

variable {n : ℕ} {a : Fin n → ℕ}

def cell (F : ScheduledFilling a) (i : Fin n) : ↥F.shape.cells := F.token.symm i

def time (F : ScheduledFilling a) (c : ↥F.shape.cells) : VisitTime n :=
  visitTime (F.visit (F.token c)) (F.token c)

@[simp] theorem token_cell (F : ScheduledFilling a) (i : Fin n) : F.token (F.cell i) = i :=
  F.token.apply_symm_apply i

@[simp] theorem cell_row (F : ScheduledFilling a) (i : Fin n) :
    (F.cell i).val.1 = a i + F.visit i := by
  simpa only [token_cell] using F.row_eq (F.cell i)

@[simp] theorem time_cell (F : ScheduledFilling a) (i : Fin n) :
    F.time (F.cell i) = visitTime (F.visit i) i := by simp only [time, token_cell]

/-- The exact processed-cell invariant before the current visit. -/
def IsPrefix (F : ScheduledFilling a) (nu : YoungDiagram) (tau : VisitTime n) : Prop :=
  nu ≤ F.shape ∧ ∀ c : ↥F.shape.cells, c.val ∈ nu ↔ F.time c < tau

theorem isAddable_of_time_eq (F : ScheduledFilling a) {nu : YoungDiagram}
    {tau : VisitTime n} (hpre : F.IsPrefix nu tau) {c : ↥F.shape.cells}
    (hc : F.time c = tau) : YoungDiagram.IsAddable nu c.val := by
  rw [YoungDiagram.isAddable_def]
  constructor
  · intro hmem
    have hlt := (hpre.2 c).mp hmem
    rw [hc] at hlt
    exact (lt_irrefl tau) hlt
  · intro d hdc
    have hd : d ∈ F.shape := F.shape.isLowerSet hdc.le c.property
    apply (hpre.2 ⟨d, hd⟩).2
    rw [← hc]
    exact F.time_strict ⟨d, hd⟩ c hdc

theorem isAddable_at_scheduled_visit (F : ScheduledFilling a) {nu : YoungDiagram}
    {p : ℕ} {i : Fin n} (hpre : F.IsPrefix nu (visitTime p i))
    (hi : F.visit i = p) :
    YoungDiagram.IsAddable nu (a i + p, nu.rowLen (a i + p)) := by
  have hadd := F.isAddable_of_time_eq hpre (c := F.cell i) (by
    rw [time_cell, hi])
  have hcell : (F.cell i).val = (a i + p, nu.rowLen (a i + p)) := by
    apply Prod.ext
    · rw [cell_row, hi]
    · rw [hadd.snd_eq_rowLen, cell_row, hi]
  rwa [hcell] at hadd

theorem visit_le_of_unread (F : ScheduledFilling a) {nu : YoungDiagram}
    {p : ℕ} {i : Fin n} (hpre : F.IsPrefix nu (visitTime p i))
    (hunread : (F.cell i).val ∉ nu) : p ≤ F.visit i := by
  by_contra h
  have hp : F.visit i < p := Nat.lt_of_not_ge h
  apply hunread
  apply (hpre.2 (F.cell i)).2
  rw [time_cell]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hp)

/-- The rejected token is scheduled in a strictly later row, so incrementing
its current label does not violate the existing filling constraint. -/
theorem row_strictly_after_rejected_visit (F : ScheduledFilling a) {nu : YoungDiagram}
    {p : ℕ} {i : Fin n} (hpre : F.IsPrefix nu (visitTime p i))
    (hunread : (F.cell i).val ∉ nu)
    (hblocked : ¬ YoungDiagram.IsAddable nu (a i + p, nu.rowLen (a i + p))) :
    a i + p + 1 ≤ (F.cell i).val.1 := by
  have hp := F.visit_le_of_unread hpre hunread
  have hne : F.visit i ≠ p := fun hi => hblocked (F.isAddable_at_scheduled_visit hpre hi)
  rw [cell_row]
  omega

/-- At a terminal state the accepted diagram is literally the entire filling;
its already established dominance then transfers to the output. -/
theorem terminal_shape_eq (F : ScheduledFilling a) {nu : YoungDiagram}
    (hsub : nu ≤ F.shape) (hfilled : ∀ i : Fin n, (F.cell i).val ∈ nu) : nu = F.shape := by
  apply le_antisymm hsub
  intro c hc
  have h := hfilled (F.token ⟨c, hc⟩)
  simpa only [cell, Equiv.symm_apply_apply] using h

theorem terminal_dominates (F : ScheduledFilling a) {nu lam : YoungDiagram}
    (hsub : nu ≤ F.shape) (hfilled : ∀ i : Fin n, (F.cell i).val ∈ nu)
    (hdom : Dominates F.shape lam) : Dominates nu lam := by
  rw [F.terminal_shape_eq hsub hfilled]
  exact hdom

end ScheduledFilling
end HigherSpecht
end
end CanonicalSource22

section CanonicalSource23
/- Source: HigherSpecht/LazyInsertion.lean -/



/-!
# Genuine lazy cyclic insertion and its scheduled filling

A lazy execution may reject an addable token.  Acceptance still requires
the actual Young-diagram addability condition.  Its fixed positions and
rejection counts are the same cyclic queue data as in the greedy algorithm.
The terminal filling constructed here is therefore an actual execution
witness.  No comparison between its shape and the greedy shape is asserted.
-/

noncomputable section
open TauCeti Function

namespace HigherSpecht

variable {n : ℕ}

inductive LazyLabeledStep (a : Fin n → ℕ) :
    LabeledCatState n → LabeledCatState n → Prop
  | accept (t : CyclingToken n) (q : List (CyclingToken n))
      (shape : YoungDiagram) (accepted : List (AcceptedToken n))
      (hadd : YoungDiagram.IsAddable shape
        (tokenValue a t, shape.rowLen (tokenValue a t))) :
      LazyLabeledStep a ⟨t :: q, shape, accepted⟩
        ⟨q, shape.addCell (tokenValue a t, shape.rowLen (tokenValue a t)),
          accepted ++ [(t, (tokenValue a t, shape.rowLen (tokenValue a t)))]⟩
  | reject (t : CyclingToken n) (q : List (CyclingToken n))
      (shape : YoungDiagram) (accepted : List (AcceptedToken n)) :
      LazyLabeledStep a ⟨t :: q, shape, accepted⟩
        ⟨q ++ [t.bump], shape, accepted⟩

inductive LazyLabeledRun (a : Fin n → ℕ) (start : LabeledCatState n) :
    LabeledCatState n → Prop
  | refl : LazyLabeledRun a start start
  | tail {s t} (h : LazyLabeledRun a start s) (hst : LazyLabeledStep a s t) :
      LazyLabeledRun a start t

/-- An accepted cell never lies weakly below an earlier accepted cell. -/
def LabeledLowerOrder (s : LabeledCatState n) : Prop :=
  s.accepted.Pairwise (fun z w => ¬ w.2 ≤ z.2)

theorem labeledLowerOrder_initial (n : ℕ) : LabeledLowerOrder (labeledInitial n) := by
  simp [LabeledLowerOrder, labeledInitial]

theorem LazyLabeledStep.invariant {a : Fin n → ℕ} {s t : LabeledCatState n}
    (hst : LazyLabeledStep a s t) (hs : LabeledInvariant a s) : LabeledInvariant a t := by
  cases hst with
  | accept tok q shape accepted hadd =>
      let c := (tokenValue a tok, shape.rowLen (tokenValue a tok))
      have hcells : (accepted.map Prod.snd).toFinset = shape.cells := hs.cells
      have hcnotlist : c ∉ accepted.map Prod.snd := by
        intro hc
        apply hadd.notMem
        change c ∈ shape.cells
        rw [← hcells]
        exact List.mem_toFinset.mpr hc
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.map_append, List.map_cons, List.map_nil] using
          CyclingExecution.accept tok hs.execution
      · change ((accepted ++ [(tok, c)]).map Prod.snd).toFinset = (shape.addCell c).cells
        simp only [List.map_append, List.map_cons, List.map_nil, List.toFinset_append,
          List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
          Finset.union_singleton, hcells, hadd.cells_addCell_eq_insert]
        exact hadd.cells_addCell_eq_insert.symm
      · rw [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        refine ⟨hs.distinctCells, by simp, ?_⟩
        intro x hx y hy hxy
        have hyc : y = c := by simpa only [List.mem_singleton] using hy
        exact hcnotlist ((hxy.trans hyc) ▸ hx)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hs.rowValue z hz
        · have hz' : z = (tok, c) := by simpa only [List.mem_singleton] using hz
          subst z
          rfl
      · apply List.pairwise_append.mpr
        refine ⟨hs.columnOrder, by simp, ?_⟩
        intro z hz w hw hcol
        have hw' : w = (tok, c) := by simpa only [List.mem_singleton] using hw
        subst w
        apply row_lt_new_cell_of_same_column hadd _ hcol
        change z.2 ∈ shape.cells
        rw [← hcells]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩)
  | reject tok q shape accepted =>
      exact ⟨CyclingExecution.reject tok hs.execution, hs.cells, hs.distinctCells,
        hs.rowValue, hs.columnOrder⟩

theorem LazyLabeledStep.lowerOrder {a : Fin n → ℕ} {s t : LabeledCatState n}
    (hst : LazyLabeledStep a s t) (hs : LabeledInvariant a s)
    (ho : LabeledLowerOrder s) : LabeledLowerOrder t := by
  cases hst with
  | accept tok q shape accepted hadd =>
      apply List.pairwise_append.mpr
      refine ⟨ho, by simp, ?_⟩
      intro z hz w hw hle
      have hw' : w = (tok, (tokenValue a tok, shape.rowLen (tokenValue a tok))) := by
        simpa only [List.mem_singleton] using hw
      subst w
      apply hadd.notMem
      apply shape.isLowerSet hle
      rw [← hs.cells]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩)
  | reject tok q shape accepted => exact ho

theorem LazyLabeledRun.invariants {a : Fin n → ℕ} {s : LabeledCatState n}
    (h : LazyLabeledRun a (labeledInitial n) s) :
    LabeledInvariant a s ∧ LabeledLowerOrder s := by
  induction h with
  | refl => exact ⟨labeledInvariant_initial a, labeledLowerOrder_initial n⟩
  | tail h hst ih => exact ⟨hst.invariant ih.1, hst.lowerOrder ih.1 ih.2⟩

theorem cyclingToken_visitTime_lt_of_stamp_lt {t u : CyclingToken n}
    (h : t.stamp < u.stamp) :
    visitTime t.round t.position < visitTime u.round u.position := by
  have hr := CyclingToken.round_le_of_stamp_le h.le
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases hr.eq_or_lt with heq | hlt
  · exact Or.inr ⟨heq, CyclingToken.position_lt_of_stamp_lt_round_eq h heq⟩
  · exact Or.inl hlt

namespace CompleteInsertion

variable {a : Fin n → ℕ} (C : CompleteInsertion a)

theorem index_lt_of_cell_lt (ho : LabeledLowerOrder C.state) {i j : C.Index}
    (hcell : (C.cell i).val < (C.cell j).val) : i < j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hij
  · subst j
    exact (lt_irrefl _ hcell).elim
  · exact (ho.rel_get_of_lt hij hcell.le).elim

/-- The scheduled tableau extracted from a complete lazy execution records
the actual rejection count of each original scan position. -/
def scheduledFilling (ho : LabeledLowerOrder C.state) : ScheduledFilling a where
  shape := C.state.shape
  token := C.filling
  visit := C.rejection
  row_eq := by
    intro c
    simpa only [row, Equiv.symm_apply_apply] using
      C.row_eq_input_add_rejection (C.filling c)
  time_strict := by
    intro c d hcd
    let i := C.cellEquiv.symm c
    let j := C.cellEquiv.symm d
    have hi : C.cell i = c := C.cellEquiv.apply_symm_apply c
    have hj : C.cell j = d := C.cellEquiv.apply_symm_apply d
    have hij : i < j := C.index_lt_of_cell_lt ho (by rw [hi, hj]; exact hcd)
    have htime := cyclingToken_visitTime_lt_of_stamp_lt (C.stamp_strictMono hij)
    rw [← hi, ← hj, filling_cell, filling_cell, rejection_position, rejection_position]
    exact htime

@[simp] theorem scheduledFilling_shape (ho : LabeledLowerOrder C.state) :
    (C.scheduledFilling ho).shape = C.state.shape := rfl

end CompleteInsertion

/-- Every actual terminal lazy execution supplies a scheduled filling with
exactly the terminal Young diagram, rather than an abstract shape premise. -/
theorem exists_scheduledFilling_of_lazyRun {a : Fin n → ℕ} {s : LabeledCatState n}
    (h : LazyLabeledRun a (labeledInitial n) s) (hnil : s.pending = []) :
    ∃ F : ScheduledFilling a, F.shape = s.shape := by
  have hi := h.invariants
  let C : CompleteInsertion a := ⟨s, hi.1, hnil⟩
  exact ⟨C.scheduledFilling hi.2, rfl⟩

end HigherSpecht
end
end CanonicalSource23

section CanonicalSource24
/- Source: HigherSpecht/CochargeWordOperations.lean -/



/-!
# The literal cocharge-word condition under a column exchange

The condition here is the empty-diagram admissibility invariant of the actual
cyclic insertion machine.  Its list formulation says that every positive
letter has an occurrence before its predecessor.  We prove the two elementary
operations used in Chou--Hanada, Lemma 2.13: insertion of a letter already in
the alphabet, and deletion of the rightmost maximum.  The indexed versions
retain the original positions of repeated letters.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def IsCochargeWord (w : List ℕ) : Prop :=
  ∀ a ∈ w, 0 < a → [a, a - 1].Sublist w

theorem isCochargeWord_iff_admissible (w : List ℕ) :
    IsCochargeWord w ↔ CatAdmissible ⟨w, ⊥⟩ := by
  simp only [IsCochargeWord, CatAdmissible, YoungDiagram.rowLen_bot,
    Nat.lt_irrefl, false_or]

theorem IsCochargeWord.interval_mem {w : List ℕ} (hw : IsCochargeWord w)
    {a b : ℕ} (ha : a ∈ w) (hba : b ≤ a) : b ∈ w := by
  exact admissible_interval_mem ((isCochargeWord_iff_admissible w).mp hw) ha b
    (by simp) hba

theorem IsCochargeWord.of_sublist {u v : List ℕ} (hu : IsCochargeWord u)
    (huv : u.Sublist v) (hletters : ∀ a ∈ v, a ∈ u) : IsCochargeWord v := by
  intro a ha hpos
  exact (hu a (hletters a ha) hpos).trans huv

/-- Positions are always listed in their original increasing order. -/
def selectedWord {n : ℕ} (a : Fin n → ℕ) (C : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter (fun i => decide (i ∈ C))).map a

@[simp] theorem mem_selectedWord {n : ℕ} (a : Fin n → ℕ)
    (C : Finset (Fin n)) (b : ℕ) :
    b ∈ selectedWord a C ↔ ∃ i ∈ C, a i = b := by
  simp only [selectedWord, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]

@[simp] theorem selectedWord_empty {n : ℕ} (a : Fin n → ℕ) :
    selectedWord a ∅ = [] := by simp [selectedWord]

@[simp] theorem selectedWord_univ {n : ℕ} (a : Fin n → ℕ) :
    selectedWord a univ = List.ofFn a := by
  simp only [selectedWord, mem_univ, decide_true, List.filter_true]
  exact List.ofFn_eq_map.symm

theorem selectedWord_sublist {n : ℕ} (a : Fin n → ℕ)
    {C D : Finset (Fin n)} (hCD : C ⊆ D) :
    (selectedWord a C).Sublist (selectedWord a D) := by
  have hfilter : ∀ L : List (Fin n),
      (L.filter (fun i => decide (i ∈ C))).Sublist
        (L.filter (fun i => decide (i ∈ D))) := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
        by_cases hiC : i ∈ C
        · have hiD := hCD hiC
          simpa [hiC, hiD] using ih.cons_cons i
        · by_cases hiD : i ∈ D
          · simpa [hiC, hiD] using ih.cons i
          · simpa [hiC, hiD] using ih
  exact (hfilter (List.finRange n)).map a

theorem pair_sublist_map_iff_exists {α : Type*} {w : List α}
    (f : α → ℕ) (a b : ℕ) :
    [a, b].Sublist (w.map f) ↔
      ∃ i j, [i, j].Sublist w ∧ f i = a ∧ f j = b := by
  constructor
  · intro h
    obtain ⟨v, hv, heq⟩ := List.sublist_map_iff.mp h
    cases v with
    | nil => simp at heq
    | cons i v =>
        cases v with
        | nil => simp at heq
        | cons j v =>
            cases v with
            | nil =>
                have hval : a = f i ∧ b = f j := by simpa using heq
                exact ⟨i, j, hv, hval.1.symm, hval.2.symm⟩
            | cons k v => simp at heq
  · rintro ⟨i, j, hij, rfl, rfl⟩
    simpa only [List.map_cons, List.map_nil] using hij.map f

theorem pair_sublist_selectedWord_iff {n : ℕ} (a : Fin n → ℕ)
    (C : Finset (Fin n)) (b c : ℕ) :
    [b, c].Sublist (selectedWord a C) ↔
      ∃ i ∈ C, ∃ j ∈ C, i < j ∧ a i = b ∧ a j = c := by
  let L := (List.finRange n).filter (fun i => decide (i ∈ C))
  have hs : L.Pairwise (· < ·) := by
    apply List.Pairwise.filter
    rw [← List.ofFn_id]
    exact List.pairwise_ofFn.mpr (fun _ _ h => h)
  have hmem (i : Fin n) : i ∈ L ↔ i ∈ C := by
    simp only [L, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  change [b, c].Sublist (L.map a) ↔ _
  rw [pair_sublist_map_iff_exists]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨i, (hmem i).mp (hij.subset (by simp)), j,
      (hmem j).mp (hij.subset (by simp)), hs.forall_sublist hij, hi, hj⟩
  · rintro ⟨i, hi, j, hj, hij, hbi, hcj⟩
    exact ⟨i, j, pair_sublist_of_pairwise hs ((hmem i).mpr hi)
      ((hmem j).mpr hj) hij.ne (not_lt.mpr hij.le), hbi, hcj⟩

theorem pair_sublist_ofFn_iff {n : ℕ} (a : Fin n → ℕ) (b c : ℕ) :
    [b, c].Sublist (List.ofFn a) ↔
      ∃ i j, i < j ∧ a i = b ∧ a j = c := by
  simpa only [selectedWord_univ, mem_univ, true_and, exists_prop] using
    pair_sublist_selectedWord_iff a univ b c

theorem IsCochargeWord.selected_insert {n : ℕ} {a : Fin n → ℕ}
    {C : Finset (Fin n)} (hC : IsCochargeWord (selectedWord a C))
    (i : Fin n) (hi : a i ∈ selectedWord a C) :
    IsCochargeWord (selectedWord a (insert i C)) := by
  apply hC.of_sublist (selectedWord_sublist a (subset_insert i C))
  intro b hb
  obtain ⟨j, hj, rfl⟩ := (mem_selectedWord a (insert i C) b).mp hb
  rcases mem_insert.mp hj with rfl | hj
  · exact hi
  · exact (mem_selectedWord a C _).mpr ⟨j, hj, rfl⟩

/-- Deleting the rightmost occurrence of the largest letter preserves the
actual predecessor-pair condition. Repeated maxima are handled by the
remaining earlier occurrence, rather than by deleting all maxima. -/
theorem IsCochargeWord.selected_erase_rightmost_max {n : ℕ} {a : Fin n → ℕ}
    {C : Finset (Fin n)} (hC : IsCochargeWord (selectedWord a C))
    (r : Fin n) (hmax : ∀ i ∈ C, a i ≤ a r)
    (hright : ∀ i ∈ C, a i = a r → i ≤ r) :
    IsCochargeWord (selectedWord a (C.erase r)) := by
  intro b hb hpos
  obtain ⟨i, hi, hbi⟩ := (mem_selectedWord a (C.erase r) b).mp hb
  obtain ⟨hin, hiC⟩ := mem_erase.mp hi
  have hbC : b ∈ selectedWord a C := (mem_selectedWord a C b).mpr ⟨i, hiC, hbi⟩
  obtain ⟨j, hj, k, hk, hjk, hjb, hkb⟩ :=
    (pair_sublist_selectedWord_iff a C b (b - 1)).mp (hC b hbC hpos)
  have hkne : k ≠ r := by
    intro heq
    have himax := hmax i hiC
    subst k
    omega
  apply (pair_sublist_selectedWord_iff a (C.erase r) b (b - 1)).mpr
  by_cases hjr : j = r
  · have hir : i < r := lt_of_le_of_ne (hright i hiC (hbi.trans (hjr ▸ hjb).symm)) hin
    exact ⟨i, hi, k, mem_erase.mpr ⟨hkne, hk⟩,
      hir.trans (hjr ▸ hjk), hbi, hkb⟩
  · exact ⟨j, mem_erase.mpr ⟨hjr, hj⟩, k, mem_erase.mpr ⟨hkne, hk⟩,
      hjk, hjb, hkb⟩

/-- The exact single-column exchange in the reading order. -/
theorem IsCochargeWord.selected_exchange {n : ℕ} {a : Fin n → ℕ}
    {C : Finset (Fin n)} (hC : IsCochargeWord (selectedWord a C))
    (r t : Fin n) (hr : r ∈ C)
    (hmax : ∀ i ∈ C, a i ≤ a r)
    (hright : ∀ i ∈ C, a i = a r → i ≤ r)
    (htval : a t ≤ a r) (httie : a t = a r → t < r) :
    IsCochargeWord (selectedWord a ((insert t C).erase r)) := by
  have hrval : a r ∈ selectedWord a C := (mem_selectedWord a C _).mpr ⟨r, hr, rfl⟩
  have htmem := hC.interval_mem hrval htval
  apply (hC.selected_insert t htmem).selected_erase_rightmost_max r
  · intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact htval
    · exact hmax i hi
  · intro i hi heq
    rcases mem_insert.mp hi with rfl | hi
    · exact (httie heq).le
    · exact hright i hi heq

end HigherSpecht
end
end CanonicalSource24

section CanonicalSource25
/- Source: HigherSpecht/CochargeWordStableSorting.lean -/



/-!
# Stable sorting recovers the labels of every cocharge subword

The stable permutation and the boost are the actual maps already used in the
bounded-word equivalence. Equal word values have equal cocharge labels because
both cocharge and boost are increasing in reading order. A predecessor-pair
witness forces a strict rise between consecutive values. Thus the labels on
an admissible selected word agree with its original values, with zero boost.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def positionCocharge {n s : ℕ} (u : Fin n → Fin s) (i : Fin n) : ℕ :=
  permutationCocharge (stablePositions u).symm ((stablePositions u).symm i)

theorem positionCocharge_le_value {n s : ℕ} (u : Fin n → Fin s) (i : Fin n) :
    positionCocharge u i ≤ (u i).val := by
  simpa only [positionCocharge, Equiv.apply_symm_apply] using
    stable_cocharge_le_value (stablePositions_spec u) ((stablePositions u).symm i)

theorem positionCocharge_add_boost {n s : ℕ} (u : Fin n → Fin s) (i : Fin n) :
    positionCocharge u i + stableBoost u ((stablePositions u).symm i) = (u i).val := by
  unfold positionCocharge stableBoost
  rw [Nat.add_sub_of_le (stable_cocharge_le_value (stablePositions_spec u) _),
    Equiv.apply_symm_apply]

theorem stableRank_lt_of_value_lt {n s : ℕ} (u : Fin n → Fin s)
    {i j : Fin n} (hij : u i < u j) :
    (stablePositions u).symm i < (stablePositions u).symm j := by
  apply (stablePositions_spec u).lt_iff_lt.mp
  simp only [Equiv.apply_symm_apply]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hij)

theorem stableRank_lt_iff {n s : ℕ} (u : Fin n → Fin s) (i j : Fin n) :
    (stablePositions u).symm i < (stablePositions u).symm j ↔
      u i < u j ∨ (u i = u j ∧ i < j) := by
  rw [← (stablePositions_spec u).lt_iff_lt]
  simp only [Equiv.apply_symm_apply, Prod.Lex.toLex_lt_toLex]

theorem stableRank_value_le {n s : ℕ} (u : Fin n → Fin s)
    {i j : Fin n} (hij : (stablePositions u).symm i ≤ (stablePositions u).symm j) :
    u i ≤ u j := by
  rcases lt_or_eq_of_le hij with h | h
  · rcases (stableRank_lt_iff u i j).mp h with hval | ⟨heq, _⟩
    · exact hval.le
    · exact heq.le
  · have heq := (stablePositions u).symm.injective h
    exact (congrArg u heq).le

theorem stableRank_position_le_of_value_eq {n s : ℕ} (u : Fin n → Fin s)
    {i j : Fin n} (hij : (stablePositions u).symm i ≤ (stablePositions u).symm j)
    (hval : (u i).val = (u j).val) : i ≤ j := by
  rcases lt_or_eq_of_le hij with h | h
  · rcases (stableRank_lt_iff u i j).mp h with hlt | ⟨_, hpos⟩
    · exact (lt_irrefl _ (by simpa only [Fin.lt_def, hval] using hlt)).elim
    · exact hpos.le
  · exact ((stablePositions u).symm.injective h).le

theorem positionCocharge_eq_of_value_eq {n s : ℕ} (u : Fin n → Fin s)
    {i j : Fin n} (hij : (u i).val = (u j).val) :
    positionCocharge u i = positionCocharge u j := by
  have hi := positionCocharge_add_boost u i
  have hj := positionCocharge_add_boost u j
  rcases le_total ((stablePositions u).symm i) ((stablePositions u).symm j) with h | h
  · have hcc := permutationCocharge_mono (stablePositions u).symm h
    have hb := stableBoost_mono u h
    change positionCocharge u i ≤ positionCocharge u j at hcc
    omega
  · have hcc := permutationCocharge_mono (stablePositions u).symm h
    have hb := stableBoost_mono u h
    change positionCocharge u j ≤ positionCocharge u i at hcc
    omega

theorem positionCocharge_lt_of_value_lt_reverse {n s : ℕ}
    (u : Fin n → Fin s) {i j : Fin n} (hval : u i < u j) (hpos : j < i) :
    positionCocharge u i < positionCocharge u j := by
  have hrank := stableRank_lt_of_value_lt u hval
  have hle := permutationCocharge_mono (stablePositions u).symm hrank.le
  change positionCocharge u i ≤ positionCocharge u j at hle
  apply lt_of_le_of_ne hle
  intro heq
  have hbad := position_lt_of_cocharge_eq (stablePositions u).symm hrank heq
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply] at hbad
  exact lt_asymm hpos hbad

/-- Any selected cocharge word retains its labels under the stable
standardization of the whole word, including other positions and values. -/
theorem positionCocharge_eq_of_selected_cochargeWord {n s : ℕ}
    (u : Fin n → Fin s) {C : Finset (Fin n)}
    (hC : IsCochargeWord (selectedWord (fun i => (u i).val) C))
    (i : Fin n) (hi : i ∈ C) : positionCocharge u i = (u i).val := by
  have hlevels : ∀ b : ℕ, ∀ j ∈ C, (u j).val = b → positionCocharge u j = b := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
        intro j hj hjb
        by_cases hb : b = 0
        · have hle := positionCocharge_le_value u j
          omega
        · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
          have hbmem : b ∈ selectedWord (fun i => (u i).val) C :=
            (mem_selectedWord _ C b).mpr ⟨j, hj, hjb⟩
          obtain ⟨r, hr, t, ht, hrt, hrb, htb⟩ :=
            (pair_sublist_selectedWord_iff (fun i => (u i).val) C b (b - 1)).mp
              (hC b hbmem hbpos)
          have htcc := ih (b - 1) (by omega) t ht htb
          have htrval : u t < u r := by change (u t).val < (u r).val; omega
          have hcc := positionCocharge_lt_of_value_lt_reverse u htrval hrt
          have heq := positionCocharge_eq_of_value_eq u (hrb.trans hjb.symm)
          have hle := positionCocharge_le_value u j
          omega
  exact hlevels (u i).val i hi rfl

theorem stableBoost_eq_zero_of_selected_cochargeWord {n s : ℕ}
    (u : Fin n → Fin s) {C : Finset (Fin n)}
    (hC : IsCochargeWord (selectedWord (fun i => (u i).val) C))
    (i : Fin n) (hi : i ∈ C) : stableBoost u ((stablePositions u).symm i) = 0 := by
  have hsum := positionCocharge_add_boost u i
  rw [positionCocharge_eq_of_selected_cochargeWord u hC i hi] at hsum
  omega

theorem positionCocharge_eq_of_cochargeWord {n s : ℕ} (u : Fin n → Fin s)
    (hu : IsCochargeWord (List.ofFn (fun i => (u i).val))) (i : Fin n) :
    positionCocharge u i = (u i).val := by
  exact positionCocharge_eq_of_selected_cochargeWord u
    (by simpa only [selectedWord_univ] using hu) i (mem_univ i)

/-- This equality identifies the predecessor-pair definition with actual
permutation cocharge, not an unrelated recognition predicate. -/
theorem labelledWord_stablePermutation_of_cochargeWord {n s : ℕ}
    (u : Fin n → Fin s)
    (hu : IsCochargeWord (List.ofFn (fun i => (u i).val))) :
    labelledWord (permutationValueWord (stablePositions u).symm) =
      List.ofFn (fun i => (u i).val) := by
  change (List.ofFn (fun i => ((stablePositions u).symm i).val)).map
    (wordCochargeLabel (permutationValueWord (stablePositions u).symm)) = _
  rw [List.map_ofFn]
  congr 1
  funext i
  exact positionCocharge_eq_of_cochargeWord u hu i

end HigherSpecht
end
end CanonicalSource25

section CanonicalSource26
/- Source: HigherSpecht/CochargeColumnWitness.lean -/



/-!
# Actual disjoint column cocharge witnesses

This is the literal ordered-set-partition data in the generalized descent-word
definition. Each column is a subword in the original position order, has its
prescribed number of positions, and satisfies the actual cocharge-word
condition. No catabolism dominance or cardinality is part of the definition.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

structure ColumnCochargeWitness {n m : ℕ} (a : Fin n → ℕ) (ell : Fin m → ℕ) where
  columns : Fin m → Finset (Fin n)
  disjoint : Pairwise (fun i j => Disjoint (columns i) (columns j))
  card_eq : ∀ j, (columns j).card = ell j
  admissible : ∀ j, IsCochargeWord (selectedWord a (columns j))

def ColumnCochargeWitness.selected {n m : ℕ} {a : Fin n → ℕ} {ell : Fin m → ℕ}
    (W : ColumnCochargeWitness a ell) : Finset (Fin n) :=
  univ.biUnion W.columns

@[simp] theorem ColumnCochargeWitness.mem_selected {n m : ℕ}
    {a : Fin n → ℕ} {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell) (i : Fin n) :
    i ∈ W.selected ↔ ∃ j, i ∈ W.columns j := by
  simp only [ColumnCochargeWitness.selected, mem_biUnion, mem_univ, true_and]

theorem ColumnCochargeWitness.column_subset_selected {n m : ℕ}
    {a : Fin n → ℕ} {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell) (j : Fin m) :
    W.columns j ⊆ W.selected := by
  intro i hi
  exact (W.mem_selected i).mpr ⟨j, hi⟩

theorem ColumnCochargeWitness.selected_card {n m : ℕ}
    {a : Fin n → ℕ} {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell) :
    W.selected.card = ∑ j, ell j := by
  rw [ColumnCochargeWitness.selected, card_biUnion]
  · simp_rw [W.card_eq]
  · intro i hi j hj hij
    exact W.disjoint hij

theorem ColumnCochargeWitness.selected_admissible {n m : ℕ}
    {a : Fin n → ℕ} {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell) :
    IsCochargeWord (selectedWord a W.selected) := by
  intro b hb hpos
  obtain ⟨i, hi, hbi⟩ := (mem_selectedWord a W.selected b).mp hb
  obtain ⟨j, hj⟩ := (W.mem_selected i).mp hi
  exact (W.admissible j b ((mem_selectedWord a (W.columns j) b).mpr ⟨i, hj, hbi⟩)
    hpos).trans (selectedWord_sublist a (W.column_subset_selected j))

def ColumnCochargeWitness.rankSum {n m : ℕ}
    {a : Fin n → ℕ} {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell)
    (rank : Equiv.Perm (Fin n)) : ℕ := ∑ j, ∑ i ∈ W.columns j, (rank i).val

/-- Replace one selected position by an unselected earlier reading position.
The hypotheses explicitly identify the rightmost maximum being removed. -/
def ColumnCochargeWitness.exchange {n m : ℕ}
    {a : Fin n → ℕ} {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell)
    (j : Fin m) (r t : Fin n) (hr : r ∈ W.columns j) (ht : t ∉ W.selected)
    (hmax : ∀ i ∈ W.columns j, a i ≤ a r)
    (hright : ∀ i ∈ W.columns j, a i = a r → i ≤ r)
    (htval : a t ≤ a r) (httie : a t = a r → t < r) :
    ColumnCochargeWitness a ell where
  columns := Function.update W.columns j ((insert t (W.columns j)).erase r)
  disjoint := by
    have hd (l : Fin m) (hl : l ≠ j) :
        Disjoint ((insert t (W.columns j)).erase r) (W.columns l) := by
      apply Finset.disjoint_left.mpr
      intro i hi hil
      rcases mem_insert.mp (mem_erase.mp hi).2 with rfl | hij
      · exact ht (W.column_subset_selected l hil)
      · exact Finset.disjoint_left.mp (W.disjoint hl.symm) hij hil
    intro l h hlh
    by_cases hlj : l = j
    · subst l
      have hhj : h ≠ j := Ne.symm hlh
      simpa only [Function.update_self, Function.update_of_ne hhj] using hd h hhj
    · by_cases hhj : h = j
      · subst h
        simpa only [Function.update_self, Function.update_of_ne hlj] using (hd l hlj).symm
      · simpa only [Function.update_of_ne hlj, Function.update_of_ne hhj] using W.disjoint hlh
  card_eq l := by
    by_cases hlj : l = j
    · subst l
      rw [Function.update_self]
      have htj : t ∉ W.columns j := fun h => ht (W.column_subset_selected j h)
      have hr' : r ∈ insert t (W.columns j) := mem_insert_of_mem hr
      rw [card_erase_of_mem hr', card_insert_of_notMem htj, Nat.add_sub_cancel,
        W.card_eq]
    · simpa only [Function.update_of_ne hlj] using W.card_eq l
  admissible l := by
    by_cases hlj : l = j
    · subst l
      rw [Function.update_self]
      exact (W.admissible j).selected_exchange r t hr hmax hright htval httie
    · simpa only [Function.update_of_ne hlj] using W.admissible l

theorem ColumnCochargeWitness.exchange_rankSum {n m : ℕ}
    {a : Fin n → ℕ} {ell : Fin m → ℕ} (W : ColumnCochargeWitness a ell)
    (j : Fin m) (r t : Fin n) (hr : r ∈ W.columns j) (ht : t ∉ W.selected)
    (hmax : ∀ i ∈ W.columns j, a i ≤ a r)
    (hright : ∀ i ∈ W.columns j, a i = a r → i ≤ r)
    (htval : a t ≤ a r) (httie : a t = a r → t < r)
    (rank : Equiv.Perm (Fin n)) :
    (W.exchange j r t hr ht hmax hright htval httie).rankSum rank + (rank r).val =
      W.rankSum rank + (rank t).val := by
  let V := W.exchange j r t hr ht hmax hright htval httie
  have htj : t ∉ W.columns j := fun h => ht (W.column_subset_selected j h)
  have hr' : r ∈ insert t (W.columns j) := mem_insert_of_mem hr
  have hcolumn := sum_erase_add (insert t (W.columns j)) (fun i => (rank i).val) hr'
  rw [sum_insert htj] at hcolumn
  have hrest : (∑ l ∈ (univ : Finset (Fin m)).erase j,
      ∑ i ∈ V.columns l, (rank i).val) =
      ∑ l ∈ (univ : Finset (Fin m)).erase j, ∑ i ∈ W.columns l, (rank i).val := by
    apply sum_congr rfl
    intro l hl
    have hlj := (mem_erase.mp hl).1
    simp only [V, ColumnCochargeWitness.exchange, Function.update_of_ne hlj]
  have hW := sum_erase_add (univ : Finset (Fin m))
    (fun l => ∑ i ∈ W.columns l, (rank i).val) (mem_univ j)
  have hV := sum_erase_add (univ : Finset (Fin m))
    (fun l => ∑ i ∈ V.columns l, (rank i).val) (mem_univ j)
  rw [hrest] at hV
  have hj : V.columns j = (insert t (W.columns j)).erase r := by
    simp only [V, ColumnCochargeWitness.exchange, Function.update_self]
  rw [hj] at hV
  change V.rankSum rank + (rank r).val = W.rankSum rank + (rank t).val
  unfold ColumnCochargeWitness.rankSum
  omega

end HigherSpecht
end
end CanonicalSource26

section CanonicalSource27
/- Source: HigherSpecht/CochargeScheduledColumns.lean -/



/-!
# Actual terminal columns are cocharge words

A first crossing of any positive initial label in a scheduled column occurs
between two consecutive rows in the same scan. The two tokens therefore have
opposite original-word positions and labels differing by one. This supplies
the literal predecessor-pair witness, including for repeated labels.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

namespace ScheduledFilling

variable {n : ℕ} {a : Fin n → ℕ}

def columnCell (F : ScheduledFilling a) (j : ℕ) (r : Fin (F.shape.colLen j)) :
    ↥F.shape.cells :=
  ⟨(r.val, j), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩

def wordEmbedding (F : ScheduledFilling a) : ↥F.shape.cells ↪ Fin n :=
  (F.token.trans Fin.revPerm).toEmbedding

@[simp] theorem wordEmbedding_apply (F : ScheduledFilling a) (c : ↥F.shape.cells) :
    F.wordEmbedding c = Fin.rev (F.token c) := rfl

/-- This is a statement about the actual selected subword, not an abstract
column alphabet or a permutation of its positions. -/
theorem column_cocharge {w : Fin n → ℕ}
    (F : ScheduledFilling (fun i => w (Fin.rev i))) (j : ℕ) :
    IsCochargeWord (selectedWord w (columnLabels F.wordEmbedding j)) := by
  intro b hb hbpos
  obtain ⟨i, hi, hbi⟩ := (mem_selectedWord w _ b).mp hb
  obtain ⟨c, hc, hci⟩ := (mem_columnLabels F.wordEmbedding j i).mp hi
  have hex : ∃ r : ℕ, ∃ hr : r < F.shape.colLen j,
      b ≤ w (Fin.rev (F.token (F.columnCell j ⟨r, hr⟩))) := by
    have hr : c.val.1 < F.shape.colLen j := by
      rw [← hc]
      exact YoungDiagram.mem_iff_lt_colLen.mp c.property
    refine ⟨c.val.1, hr, ?_⟩
    have heq : F.columnCell j ⟨c.val.1, hr⟩ = c := by
      apply Subtype.ext
      exact Prod.ext rfl hc.symm
    rw [heq]
    change b ≤ w (F.wordEmbedding c)
    rw [hci, hbi]
  let r := Nat.find hex
  obtain ⟨hr, hlabel⟩ := Nat.find_spec hex
  let d := F.columnCell j ⟨r, hr⟩
  have hrow : r = w (Fin.rev (F.token d)) + F.visit (F.token d) := F.row_eq d
  change b ≤ w (Fin.rev (F.token d)) at hlabel
  have hrpos : 0 < r := by omega
  have hp : r - 1 < F.shape.colLen j := by omega
  let c' := F.columnCell j ⟨r - 1, hp⟩
  have hrowp : r - 1 = w (Fin.rev (F.token c')) + F.visit (F.token c') := F.row_eq c'
  have hlabelp : w (Fin.rev (F.token c')) < b := by
    apply lt_of_not_ge
    intro hge
    exact Nat.find_min hex (show r - 1 < Nat.find hex by change r - 1 < r; omega) ⟨hp, hge⟩
  have hcell : c'.val < d.val := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨⟨by change r - 1 ≤ r; omega, le_rfl⟩, ?_⟩
    intro h
    have hbad : r ≤ r - 1 := h.1
    omega
  have ht := Prod.Lex.toLex_lt_toLex.mp (F.time_strict c' d hcell)
  have hround : F.visit (F.token c') = F.visit (F.token d) := by
    rcases ht with hlt | ⟨heq, _⟩
    · change F.visit (F.token c') < F.visit (F.token d) at hlt
      change b ≤ w (Fin.rev (F.token d)) at hlabel
      omega
    · exact heq
  have hpos : F.token c' < F.token d := by
    rcases ht with hlt | ⟨_, hlt⟩
    · omega
    · exact hlt
  have hdlabel : w (Fin.rev (F.token d)) = b := by
    change b ≤ w (Fin.rev (F.token d)) at hlabel
    omega
  have hclabel : w (Fin.rev (F.token c')) = b - 1 := by omega
  apply (pair_sublist_selectedWord_iff w (columnLabels F.wordEmbedding j) b (b - 1)).mpr
  refine ⟨Fin.rev (F.token d), ?_, Fin.rev (F.token c'), ?_,
    Fin.rev_lt_rev.mpr hpos, hdlabel, hclabel⟩
  · exact (mem_columnLabels F.wordEmbedding j _).mpr ⟨d, rfl, rfl⟩
  · exact (mem_columnLabels F.wordEmbedding j _).mpr ⟨c', rfl, rfl⟩

def columnCochargeWitness {w : Fin n → ℕ}
    (F : ScheduledFilling (fun i => w (Fin.rev i))) :
    ColumnCochargeWitness w (fun j : Fin (F.shape.rowLen 0) => F.shape.colLen j.val) where
  columns j := columnLabels F.wordEmbedding j.val
  disjoint := by
    intro i j hij
    exact columnLabels_pairwiseDisjoint F.wordEmbedding (Set.mem_univ _)
      (Set.mem_univ _) (fun h => hij (Fin.ext h))
  card_eq j := card_columnLabels F.wordEmbedding j.val
  admissible j := F.column_cocharge j.val

end ScheduledFilling

theorem LazyLabeledRun.greedy_step {n : ℕ} {a : Fin n → ℕ}
    {start s : LabeledCatState n} (h : LazyLabeledRun a start s) :
    LazyLabeledRun a start (labeledCatStep a s) := by
  rcases s with ⟨q, mu, accepted⟩
  cases q with
  | nil => exact h
  | cons t q =>
      dsimp only [labeledCatStep]
      split_ifs with hadd
      · exact h.tail (.accept t q mu accepted hadd)
      · exact h.tail (.reject t q mu accepted)

theorem labeledCatRun_lazy {n : ℕ} (a : Fin n → ℕ) (N : ℕ) :
    LazyLabeledRun a (labeledInitial n) (labeledCatRun a N (labeledInitial n)) := by
  induction N with
  | zero => exact .refl
  | succ N ih =>
      rw [labeledCatRun, Function.iterate_succ_apply']
      exact ih.greedy_step

theorem ofFn_reverse_labels {n : ℕ} (a : Fin n → ℕ) :
    (List.ofFn (fun i => a (Fin.rev i))).reverse = List.ofFn a := by
  apply List.ext_getElem
  · simp only [List.length_reverse, List.length_ofFn]
  · intro i hi hj
    simp only [List.length_reverse, List.length_ofFn] at hi hj
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.rev]
    omega

/-- Every genuine terminating word execution supplies the actual terminal
scheduled filling in the original positions. No admissibility premise is
added: termination here is precisely the supplied `CatWordOutput` proof. -/
theorem exists_scheduledFilling_of_wordOutput {n : ℕ} {w : Fin n → ℕ}
    {mu : YoungDiagram} (h : CatWordOutput (List.ofFn w) mu) :
    ∃ F : ScheduledFilling (fun i => w (Fin.rev i)), F.shape = mu := by
  obtain ⟨N, hN⟩ := h
  let a : Fin n → ℕ := fun i => w (Fin.rev i)
  let s := labeledCatRun a N (labeledInitial n)
  have hforget : labeledForget a s = (⟨[], mu⟩ : CatState) := by
    dsimp only [s, a]
    rw [labeledForget_run, labeledForget_initial, ofFn_reverse_labels]
    exact hN
  have hnil : s.pending = [] := by
    have hw := congrArg CatState.word hforget
    simpa only [labeledForget, List.reverse_eq_nil_iff, List.map_eq_nil_iff] using hw
  have hshape : s.shape = mu := congrArg CatState.shape hforget
  obtain ⟨F, hF⟩ := exists_scheduledFilling_of_lazyRun (labeledCatRun_lazy a N) hnil
  exact ⟨F, hF.trans hshape⟩

theorem exists_columns_of_wordOutput {n : ℕ} {w : Fin n → ℕ}
    {mu : YoungDiagram} (h : CatWordOutput (List.ofFn w) mu) :
    Nonempty (ColumnCochargeWitness w
      (fun j : Fin (mu.rowLen 0) => mu.colLen j.val)) := by
  obtain ⟨F, rfl⟩ := exists_scheduledFilling_of_wordOutput h
  exact ⟨F.columnCochargeWitness⟩

end HigherSpecht
end
end CanonicalSource27

section CanonicalSource28
/- Source: HigherSpecht/BatteryOmittedColors.lean -/



/-!
# Semistandard batteries obtained by omitting one color per column

A column contains the ordered alphabet with exactly its specified missing color
removed.  Missing colors decrease from left to right, so all rows weakly
increase.  The formulas include empty columns and the one-color alphabet.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

def omittedColorEntry (c r : ℕ) : ℕ := if r < c then r else r + 1

theorem omittedColorEntry_strictMono (c : ℕ) : StrictMono (omittedColorEntry c) := by
  intro r t hrt
  simp only [omittedColorEntry]
  split_ifs <;> omega

theorem omittedColorEntry_antitone_color (r : ℕ) :
    Antitone (fun c => omittedColorEntry c r) := by
  intro c e hce
  simp only [omittedColorEntry]
  split_ifs <;> omega

def omittedColorColumn {s : ℕ} (c : Fin s) : List ℕ :=
  List.ofFn (fun r : Fin (s - 1) => omittedColorEntry c.val r.val)

theorem omittedColorColumn_mem {s : ℕ} (c : Fin s) (a : ℕ) :
    a ∈ omittedColorColumn c ↔ a < s ∧ a ≠ c.val := by
  rw [omittedColorColumn, List.mem_ofFn]
  constructor
  · rintro ⟨r, rfl⟩
    have hr := r.isLt
    have hc := c.isLt
    simp only [omittedColorEntry]
    split_ifs <;> omega
  · rintro ⟨has, hac⟩
    by_cases haclt : a < c.val
    · refine ⟨⟨a, by have hc := c.isLt; omega⟩, ?_⟩
      simp only [omittedColorEntry, haclt, if_true]
    · have hca : c.val < a := by omega
      refine ⟨⟨a - 1, by omega⟩, ?_⟩
      have hnot : ¬ a - 1 < c.val := by omega
      simp only [omittedColorEntry, hnot, if_false]
      omega

theorem omittedColorColumn_nodup {s : ℕ} (c : Fin s) :
    (omittedColorColumn c).Nodup := by
  apply List.SortedLT.nodup
  apply List.sortedLT_ofFn_iff.mpr
  exact (omittedColorEntry_strictMono c.val).comp Fin.val_strictMono

theorem omittedColorColumn_count {s : ℕ} (c : Fin s) (a : ℕ) :
    (omittedColorColumn c).count a = if a < s ∧ a ≠ c.val then 1 else 0 := by
  by_cases ha : a < s ∧ a ≠ c.val
  · rw [if_pos ha]
    exact List.count_eq_one_of_mem (omittedColorColumn_nodup c)
      ((omittedColorColumn_mem c a).mpr ha)
  · rw [if_neg ha]
    exact List.count_eq_zero.mpr (fun h => ha ((omittedColorColumn_mem c a).mp h))

/-- Literal rectangular tableau whose columns each omit one specified color. -/
def omittedColorBattery {s d : ℕ} (missing : Fin d → Fin s)
    (hmissing : Antitone missing) :
    SemistandardYoungTableau (batteryRectangle (s - 1) d) where
  entry r j := if hr : r < s - 1 then
    if hj : j < d then omittedColorEntry (missing ⟨j, hj⟩).val r else 0 else 0
  row_weak' {r j k} hjk hcell := by
    have hm := mem_batteryRectangle.mp hcell
    have hjd : j < d := lt_trans hjk hm.2
    simp only [hm.1, hjd, hm.2, dif_pos]
    exact omittedColorEntry_antitone_color r
      (show (missing ⟨k, hm.2⟩).val ≤ (missing ⟨j, hjd⟩).val from
        hmissing (show (⟨j, hjd⟩ : Fin d) ≤ ⟨k, hm.2⟩ from hjk.le))
  col_strict' {r t j} hrt hcell := by
    have hm := mem_batteryRectangle.mp hcell
    have hrs : r < s - 1 := hrt.trans hm.1
    simp only [hrs, hm.1, hm.2, dif_pos]
    exact omittedColorEntry_strictMono _ hrt
  zeros' {r j} hcell := by
    have hm : ¬ (r < s - 1 ∧ j < d) := fun h => hcell (mem_batteryRectangle.mpr h)
    by_cases hr : r < s - 1
    · have hj : ¬ j < d := fun h => hm ⟨hr, h⟩
      simp only [dif_pos hr, dif_neg hj]
    · simp only [dif_neg hr]

@[simp] theorem omittedColorBattery_apply {s d : ℕ}
    (missing : Fin d → Fin s) (hmissing : Antitone missing)
    (r : Fin (s - 1)) (j : Fin d) :
    omittedColorBattery missing hmissing r j =
      omittedColorEntry (missing j).val r.val := by
  change (if hr : r.val < s - 1 then
    if hj : j.val < d then omittedColorEntry (missing ⟨j.val, hj⟩).val r.val
      else 0 else 0) = _
  simp only [dif_pos r.isLt, dif_pos j.isLt]

theorem list_count_ofFn_eq_sum {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = ∑ i : Fin n, if f i = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
      by_cases h : f 0 = a <;> simp [h, Nat.add_comm]

theorem omittedColorBattery_count {s d : ℕ}
    (missing : Fin d → Fin s) (hmissing : Antitone missing) (a : ℕ) :
    (tableauWord (omittedColorBattery missing hmissing)).count a =
      ∑ j : Fin d, if a < s ∧ a ≠ (missing j).val then 1 else 0 := by
  rw [batteryWord_eq_rows, List.count_flatten, List.map_reverse, List.sum_reverse]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]
  simp_rw [list_count_ofFn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← list_count_ofFn_eq_sum]
  simpa only [omittedColorBattery_apply, omittedColorColumn] using
    omittedColorColumn_count (missing j) a

theorem omittedColorBattery_count_add_missing {s d : ℕ}
    (missing : Fin d → Fin s) (hmissing : Antitone missing) (a : Fin s) :
    (tableauWord (omittedColorBattery missing hmissing)).count a.val +
      (List.ofFn missing).count a = d := by
  rw [omittedColorBattery_count, list_count_ofFn_eq_sum, ← Finset.sum_add_distrib]
  have hterm (j : Fin d) :
      (if a.val < s ∧ a.val ≠ (missing j).val then 1 else 0) +
        (if missing j = a then 1 else 0) = 1 := by
    by_cases h : missing j = a
    · simp [h, a.isLt]
    · have hn : a.val ≠ (missing j).val := fun he => h (Fin.ext he.symm)
      simp [h, hn, a.isLt]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem omittedColorBattery_count_eq_zero {s d : ℕ}
    (missing : Fin d → Fin s) (hmissing : Antitone missing) {a : ℕ} (ha : s ≤ a) :
    (tableauWord (omittedColorBattery missing hmissing)).count a = 0 := by
  rw [omittedColorBattery_count]
  simp only [Nat.not_lt_of_ge ha, false_and, if_false, Finset.sum_const_zero]

end HigherSpecht.Lascoux
end
end CanonicalSource28

section CanonicalSource29
/- Source: HigherSpecht/BoostedCocharge.lean -/



/-!
# The actual boosted cocharge fillings

The multiplier partition is padded with zeroes, and its parts are assigned in
reverse label order.  The boost is monotone in the standard label, preserves
strictness in columns, vanishes on the prescribed prefix, and obeys exactly
the rectangle bound in Theorem 4.1.  The resulting filling determines both
the standard tableau and the multiplier partition.
-/

noncomputable section

open Finset TauCeti
open TauCeti.YoungTableau

namespace HigherSpecht

variable {μ : YoungDiagram}

def boostLabel (eta : YoungDiagram) (n : ℕ) (i : Fin n) : ℕ :=
  eta.rowLen (n - 1 - i.val)

theorem boostLabel_mono (eta : YoungDiagram) (n : ℕ) : Monotone (boostLabel eta n) := by
  intro i j hij
  apply eta.rowLen_anti
  omega

def boostedLabel (S : StandardYoungTableau μ) (eta : YoungDiagram) (i : Fin μ.card) : ℕ :=
  cochargeLabel S i + boostLabel eta μ.card i

def boostedFilling (S : StandardYoungTableau μ) (eta : YoungDiagram) (c : ↥μ.cells) : ℕ :=
  boostedLabel S eta (S c)

def transportedBoosted (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) : Fin μ.card →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => boostedFilling S eta (T.symm i)

theorem boostedLabel_mono (S : StandardYoungTableau μ) (eta : YoungDiagram) :
    Monotone (boostedLabel S eta) :=
  (cochargeLabel_mono S).add (boostLabel_mono eta μ.card)

theorem cochargeLabel_eq_of_boostedLabel_eq (S : StandardYoungTableau μ)
    (eta : YoungDiagram) {i j : Fin μ.card} (hij : i ≤ j)
    (h : boostedLabel S eta i = boostedLabel S eta j) : cochargeLabel S i = cochargeLabel S j := by
  have hcc := cochargeLabel_mono S hij
  have hb := boostLabel_mono eta μ.card hij
  dsimp only [boostedLabel] at h
  omega

theorem row_le_of_boostedLabel_eq (S : StandardYoungTableau μ) (eta : YoungDiagram)
    {i j : Fin μ.card} (hij : i ≤ j) (h : boostedLabel S eta i = boostedLabel S eta j) :
    rowIndex S.toTableau j ≤ rowIndex S.toTableau i :=
  row_le_of_cochargeLabel_eq S hij (cochargeLabel_eq_of_boostedLabel_eq S eta hij h)

theorem boostedFilling_row_mono (S : StandardYoungTableau μ) (eta : YoungDiagram)
    {c d : ↥μ.cells} (hr : c.val.1 = d.val.1) (hc : c.val.2 ≤ d.val.2) :
    boostedFilling S eta c ≤ boostedFilling S eta d := by
  apply boostedLabel_mono
  rcases hc.eq_or_lt with h | h
  · have : c = d := Subtype.ext (Prod.ext hr h)
    simp [this]
  · exact (S.lt_of_colIndex_lt (by simpa only [rowIndex_standard_apply] using hr)
      (by simpa only [colIndex_standard_apply] using h)).le

theorem boostedFilling_col_strict (S : StandardYoungTableau μ) (eta : YoungDiagram)
    {c d : ↥μ.cells} (hc : c.val.2 = d.val.2) (hr : c.val.1 < d.val.1) :
    boostedFilling S eta c < boostedFilling S eta d := by
  have hlabel : S c < S d := S.lt_of_rowIndex_lt
    (by simpa only [colIndex_standard_apply] using hc)
    (by simpa only [rowIndex_standard_apply] using hr)
  exact add_lt_add_of_lt_of_le (cochargeFilling_col_strict S hc hr)
    (boostLabel_mono eta μ.card hlabel.le)

theorem boostLabel_eq_zero_on_prefix (eta : YoungDiagram) {n k : ℕ}
    (hk : k ≤ n) (hlen : eta.colLen 0 ≤ n - k) (i : Fin n) (hi : i.val < k) :
    boostLabel eta n i = 0 := by
  apply YoungDiagram.rowLen_eq_zero_of_colLen_le
  have := i.isLt
  omega

theorem boostedLabel_eq_on_prefix (S : StandardYoungTableau μ) (eta : YoungDiagram)
    {k : ℕ} (hk : k ≤ μ.card) (hlen : eta.colLen 0 ≤ μ.card - k)
    (i : Fin μ.card) (hi : i.val < k) : boostedLabel S eta i = cochargeLabel S i := by
  rw [boostedLabel, boostLabel_eq_zero_on_prefix eta hk hlen i hi, add_zero]

theorem boostedLabel_lt_bound (S : StandardYoungTableau μ) (eta : YoungDiagram)
    {s : ℕ} (hdes : descentNumber S < s)
    (hwidth : eta.rowLen 0 ≤ s - descentNumber S - 1) (i : Fin μ.card) :
    boostedLabel S eta i < s := by
  have hcc := cochargeLabel_le_descentNumber S i
  have hb := eta.rowLen_anti 0 (μ.card - 1 - i.val) (Nat.zero_le _)
  dsimp only [boostedLabel, boostLabel]
  omega

/-- The actual boosted filling recovers its standardization; this does not
assume a separate inverse or an unstated uniqueness of boosted words. -/
theorem tableau_eq_of_boostedFilling_eq (S T : StandardYoungTableau μ)
    (eta theta : YoungDiagram) (hfill : boostedFilling S eta = boostedFilling T theta) : S = T := by
  let σ : Equiv.Perm (Fin μ.card) := S.toTableau.symm.trans T.toTableau
  have hσ (i : Fin μ.card) : σ i = T (S.toTableau.symm i) := rfl
  have hr (i : Fin μ.card) : rowIndex T.toTableau (σ i) = rowIndex S.toTableau i := by
    rw [hσ, rowIndex_standard_apply, rowIndex_def]
  have hc (i : Fin μ.card) : colIndex T.toTableau (σ i) = colIndex S.toTableau i := by
    rw [hσ, colIndex_standard_apply, colIndex_def]
  have ha (i : Fin μ.card) : boostedLabel S eta i = boostedLabel T theta (σ i) := by
    have h := congrFun hfill (S.toTableau.symm i)
    simpa only [boostedFilling, standardTableau_apply_symm, ← hσ] using h
  have hmono : StrictMono σ := by
    intro i j hij
    by_contra hnot
    have hji : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hnot)
      (fun h => hij.ne (σ.injective h.symm))
    have hs := boostedLabel_mono S eta hij.le
    have ht := boostedLabel_mono T theta hji.le
    have heq : boostedLabel S eta i = boostedLabel S eta j := by
      rw [← ha, ← ha] at ht
      omega
    have hrs := row_le_of_boostedLabel_eq S eta hij.le heq
    have hrt := row_le_of_boostedLabel_eq T theta hji.le (by rw [← ha, ← ha, heq])
    rw [hr, hr] at hrt
    have hre : rowIndex S.toTableau i = rowIndex S.toTableau j := le_antisymm hrt hrs
    have hcs := (S.lt_iff_colIndex_lt hre).mp hij
    have hct := (T.lt_iff_colIndex_lt (by rw [hr, hr, hre])).mp hji
    rw [hc, hc] at hct
    exact (not_lt_of_ge hcs.le) hct
  apply StandardYoungTableau.ext
  intro c
  have hi := hmono.apply_eq (x := S c)
  simpa only [hσ, standardTableau_symm_apply] using hi.symm

theorem partition_eq_of_boostedFilling_eq (S : StandardYoungTableau μ)
    {eta theta : YoungDiagram} (heta : eta.colLen 0 ≤ μ.card) (htheta : theta.colLen 0 ≤ μ.card)
    (hfill : boostedFilling S eta = boostedFilling S theta) : eta = theta := by
  have hrow (j : ℕ) : eta.rowLen j = theta.rowLen j := by
    by_cases hj : j < μ.card
    · let i : Fin μ.card := ⟨μ.card - 1 - j, by omega⟩
      have h := congrFun hfill (S.toTableau.symm i)
      simp only [boostedFilling, standardTableau_apply_symm, boostedLabel, boostLabel] at h
      have hindex : μ.card - 1 - i.val = j := by dsimp [i]; omega
      rw [hindex] at h
      exact Nat.add_left_cancel h
    · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (heta.trans (le_of_not_gt hj)),
        YoungDiagram.rowLen_eq_zero_of_colLen_le (htheta.trans (le_of_not_gt hj))]
  ext c
  rcases c with ⟨r, j⟩
  change (r, j) ∈ eta ↔ (r, j) ∈ theta
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, hrow]

theorem boostedFilling_injective (μ : YoungDiagram) :
    Function.Injective (fun x : StandardYoungTableau μ × {eta : YoungDiagram | eta.colLen 0 ≤ μ.card} =>
      boostedFilling x.1 x.2.val) := by
  rintro ⟨S, eta⟩ ⟨T, theta⟩ h
  have hST := tableau_eq_of_boostedFilling_eq S T eta.val theta.val h
  subst T
  have heta := partition_eq_of_boostedFilling_eq S eta.property theta.property h
  exact Prod.ext rfl (Subtype.ext heta)

end HigherSpecht
end
end CanonicalSource29

section CanonicalSource30
/- Source: HigherSpecht/ContractionLeading.lean -/



/-!
# Leading divided-power witnesses and integral monomial independence

A monic witness with leading exponent a supplies a monic contracted witness
for every exponent below a coordinatewise.  The resulting coefficient
functionals prove independence of the actual monomial classes.  Combining
this independence with genuine monic division closes the usual dimension
step without assuming a characteristic-zero dimension theorem.
-/

noncomputable section

open MvPolynomial Finset
open scoped MonomialOrder

namespace HigherSpecht

variable {σ R : Type*} [CommRing R]

theorem contractMonomial_mem_dividedHarmonics {I : Ideal (MvPolynomial σ R)}
    {w : MvPolynomial σ R} (hw : w ∈ dividedHarmonics I) (d : σ →₀ ℕ) :
    contractMonomial d w ∈ dividedHarmonics I := by
  simpa only [dividedAction_monomial, one_smul] using
    dividedAction_mem_dividedHarmonics hw (MvPolynomial.monomial d 1)

theorem degree_contractMonomial (m : MonomialOrder σ) {w : MvPolynomial σ R}
    (hw : w ≠ 0) (d : σ →₀ ℕ) (hd : d ≤ m.degree w) :
    m.degree (contractMonomial d w) = m.degree w - d := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply m.degree_le_iff.mpr
    intro beta hbeta
    have hcoeff : w.coeff (beta + d) ≠ 0 := by
      simpa only [MvPolynomial.mem_support_iff, coeff_contractMonomial] using hbeta
    have hle := m.le_degree (MvPolynomial.mem_support_iff.mpr hcoeff)
    rw [← tsub_add_cancel_of_le hd] at hle
    simpa only [map_add, add_le_add_iff_right] using hle
  · apply m.le_degree
    rw [MvPolynomial.mem_support_iff, coeff_contractMonomial, tsub_add_cancel_of_le hd]
    exact m.coeff_degree_ne_zero_iff.mpr hw

theorem leadingCoeff_contractMonomial (m : MonomialOrder σ) {w : MvPolynomial σ R}
    (hw : w ≠ 0) (d : σ →₀ ℕ) (hd : d ≤ m.degree w) :
    m.leadingCoeff (contractMonomial d w) = m.leadingCoeff w := by
  rw [MonomialOrder.leadingCoeff, degree_contractMonomial m hw d hd,
    coeff_contractMonomial, tsub_add_cancel_of_le hd]
  rfl

theorem monic_contractMonomial [Nontrivial R] (m : MonomialOrder σ)
    {w : MvPolynomial σ R} (hw : m.Monic w) (d : σ →₀ ℕ) (hd : d ≤ m.degree w) :
    m.Monic (contractMonomial d w) := by
  rw [MonomialOrder.Monic, leadingCoeff_contractMonomial m hw.ne_zero d hd]
  exact hw

/-- No finite-dimensional hypothesis is needed.  Each chosen leader is a
genuine harmonic polynomial, and its lower terms determine a triangular
coefficient pairing. -/
theorem linearIndependent_quotient_monomials_of_monic_harmonics
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R)) (C : Set (σ →₀ ℕ))
    (hC : ∀ c ∈ C, ∃ w : MvPolynomial σ R,
      w ∈ dividedHarmonics I ∧ m.degree w = c ∧ m.Monic w) :
    LinearIndependent R (fun c : C => Ideal.Quotient.mk I (MvPolynomial.monomial c.val 1)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a hsum i hi
  by_contra hai
  let S := s.filter fun j => a j ≠ 0
  have hS : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun j => m.toSyn j.val) hS
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  obtain ⟨w, hw, hdeg, hmonic⟩ := hC j.val j.property
  let N := I.restrictScalars R
  let L : Module.Dual R (MvPolynomial σ R ⧸ I) :=
    N.liftQ (contractionCoefficient w 0) (contractionCoefficient_kills_ideal hw 0)
  have heq := congrArg L hsum
  have hL (c : C) : L (Ideal.Quotient.mk I (MvPolynomial.monomial c.val 1)) = w.coeff c.val := by
    change (dividedAction (MvPolynomial.monomial c.val 1) w).coeff 0 = _
    simp only [dividedAction_monomial, one_smul, coeff_contractMonomial, zero_add]
  simp only [map_sum, map_smul, smul_eq_mul, hL, map_zero] at heq
  have hdiag : w.coeff j.val = 1 := by
    rw [← hdeg]
    exact hmonic
  have hsingle : (∑ l ∈ s, a l * w.coeff l.val) = a j := by
    rw [Finset.sum_eq_single j]
    · rw [hdiag, mul_one]
    · intro l hls hlj
      by_cases hal : a l = 0
      · simp only [hal, zero_mul]
      · have hle := hmin l (Finset.mem_filter.mpr ⟨hls, hal⟩)
        have hne : m.toSyn j.val ≠ m.toSyn l.val := by
          intro he
          exact hlj (Subtype.ext (m.toSyn.injective he).symm)
        have hlt : m.degree w ≺[m] l.val := by
          rw [hdeg]
          exact lt_of_le_of_ne hle hne
        rw [m.coeff_eq_zero_of_lt hlt, mul_zero]
    · exact fun hn => (hn hjs).elim
  rw [hsingle] at heq
  exact haj heq

/-- A downward staircase of monic harmonic leaders gives independent
monomial classes over every nontrivial coefficient ring. -/
theorem linearIndependent_below_harmonic_leaders [Nontrivial R]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (A : Set (MvPolynomial σ R))
    (hA : ∀ w ∈ A, w ∈ dividedHarmonics I ∧ m.Monic w) :
    LinearIndependent R (fun c : {c : σ →₀ ℕ | ∃ w ∈ A, c ≤ m.degree w} =>
      Ideal.Quotient.mk I (MvPolynomial.monomial c.val 1)) := by
  apply linearIndependent_quotient_monomials_of_monic_harmonics m I
  rintro c ⟨w, hw, hc⟩
  obtain ⟨hH, hM⟩ := hA w hw
  have hd : m.degree w - c ≤ m.degree w := tsub_le_self
  refine ⟨contractMonomial (m.degree w - c) w,
    contractMonomial_mem_dividedHarmonics hH _, ?_, monic_contractMonomial m hM _ hd⟩
  rw [degree_contractMonomial m hM.ne_zero _ hd, tsub_tsub_cancel_of_le hc]

/-- Division plus independently proved monomial independence is sufficient
to verify a Gröbner basis.  In particular this does not insert a dimension
formula as an extra premise. -/
theorem isGroebnerBasis_of_independent_remainder_monomials
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R)) (G : Set (MvPolynomial σ R))
    (hGI : G ⊆ I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hlin : LinearIndependent R (fun c : {c : σ →₀ ℕ | ∀ g ∈ G, g ≠ 0 → ¬ m.degree g ≤ c} =>
      Ideal.Quotient.mk I (MvPolynomial.monomial c.val 1))) :
    m.IsGroebnerBasis G I := by
  let C : Set (σ →₀ ℕ) := {c | ∀ g ∈ G, g ≠ 0 → ¬ m.degree g ≤ c}
  let q : restrictSupport R C →ₗ[R] MvPolynomial σ R ⧸ I :=
    (Ideal.Quotient.mkₐ R I).toLinearMap.comp (restrictSupport R C).subtype
  have hq : Function.Injective q := by
    apply LinearMap.injective_of_linearIndependent (basisRestrictSupport R C).span_eq
    have hcomp : q ∘ (basisRestrictSupport R C) = fun c : C =>
        Ideal.Quotient.mk I (MvPolynomial.monomial c.val 1) := by
      funext c
      change Ideal.Quotient.mk I (basisRestrictSupport R C c : MvPolynomial σ R) = _
      rw [MvPolynomial.basisRestrictSupport_apply_coe]
    rw [hcomp]
    exact hlin
  apply MonomialOrder.isGroebnerBasis_iff_isRemainder_zero.mpr
  refine ⟨hGI, ?_⟩
  intro f hf
  obtain ⟨r, hr⟩ := MonomialOrder.exists_isRemainder hG f
  have hrC : r ∈ restrictSupport R C := by
    apply (mem_restrictSupport_iff R).mpr
    intro c hc
    intro g hg hg0
    exact hr.not_degree_le hc hg hg0
  have hrI : r ∈ I := by
    have hs : f - r ∈ I := Ideal.span_le.mpr hGI hr.sub_mem_span
    simpa only [sub_sub_cancel] using I.sub_mem hf hs
  have hr0 : r = 0 := by
    have heq : q ⟨r, hrC⟩ = q 0 := by
      change Ideal.Quotient.mk I r = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hrI
    exact congrArg Subtype.val (hq heq)
  simpa only [hr0] using hr

end HigherSpecht
end
end CanonicalSource30

section CanonicalSource31
/- Source: HigherSpecht/GroebnerLifts.lean -/



/-!
# Integral elementary-generator lifts in Yu's Gröbner recursion

The recursion temporarily allows a partition with one more cell than the
number of variables.  Its ideal must then include the degree-zero elementary
generator.  `extendedElementaryIdeal` implements that actual extension and
is proved equal to the manuscript's ideal in its stated parameter range.
The lifting lemma is proved in the integral polynomial ring itself, not only
after extension to a characteristic-zero field.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

def columnTail (μ : YoungDiagram) (h : ℕ) : ℕ :=
  (μ.cells.filter fun c => h ≤ c.2).card

@[simp] theorem columnTail_zero (μ : YoungDiagram) : columnTail μ 0 = μ.card := by
  simp [columnTail, YoungDiagram.card]

theorem columnTail_succ (μ : YoungDiagram) (h : ℕ) :
    columnTail μ h = μ.colLen h + columnTail μ (h + 1) := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := μ.cells.filter fun c => h ≤ c.2) (fun c => c.2 = h)
  have hcol : ((μ.cells.filter fun c => h ≤ c.2).filter fun c => c.2 = h) = μ.col h := by
    apply Finset.ext
    intro c
    constructor
    · intro hc
      obtain ⟨hc', heq⟩ := Finset.mem_filter.mp hc
      obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hc'
      exact YoungDiagram.mem_col_iff.mpr ⟨(YoungDiagram.mem_cells _).mp hmem, heq⟩
    · intro hc
      obtain ⟨hmem, heq⟩ := YoungDiagram.mem_col_iff.mp hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨(YoungDiagram.mem_cells _).mpr hmem, le_of_eq heq.symm⟩, heq⟩
  have htail : ((μ.cells.filter fun c => h ≤ c.2).filter fun c => ¬ c.2 = h) =
      μ.cells.filter fun c => h + 1 ≤ c.2 := by
    ext c
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hc, hle⟩, hne⟩
      exact ⟨hc, by omega⟩
    · rintro ⟨hc, hlt⟩
      exact ⟨⟨hc, by omega⟩, by omega⟩
  rw [hcol, htail, ← μ.colLen_eq_card] at hpart
  exact hpart.symm

theorem columnTail_eq_zero_of_width_le (μ : YoungDiagram) {h : ℕ}
    (hh : μ.rowLen 0 ≤ h) : columnTail μ h = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hcμ, hcol⟩ := Finset.mem_filter.mp hc
  have hlt := YoungDiagram.mem_iff_lt_rowLen.mp hcμ
  have hrow := μ.rowLen_anti 0 c.1 (Nat.zero_le _)
  omega

theorem columnTail_add_prefix (μ : YoungDiagram) (h : ℕ) :
    columnTail μ h + ∑ j ∈ Finset.range h, μ.colLen j = μ.card := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ]
    rw [columnTail_succ μ h] at ih
    omega

theorem columnTail_eq_sum_Ico (μ : YoungDiagram) {h n : ℕ}
    (hh : h ≤ n) (hn : μ.rowLen 0 ≤ n) :
    columnTail μ h = ∑ j ∈ Finset.Ico h n, μ.colLen j := by
  have h1 := columnTail_add_prefix μ h
  have h2 := columnTail_add_prefix μ n
  rw [columnTail_eq_zero_of_width_le μ hn, zero_add] at h2
  have hsplit := Finset.sum_range_add_sum_Ico μ.colLen hh
  omega

theorem rowLen_zero_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.card := by
  rw [μ.rowLen_eq_card, YoungDiagram.card]
  exact Finset.card_le_card (by intro c hc; exact (YoungDiagram.mem_row_iff.mp hc).1)

theorem columnTail_eq_conjugateTail {n m : ℕ} (μ : YoungDiagram) (hn : μ.card ≤ n) :
    columnTail μ (n - m) = conjugateTail n μ m := by
  exact columnTail_eq_sum_Ico μ (Nat.sub_le _ _) ((rowLen_zero_le_card μ).trans hn)

theorem conjugateTail_le_card {n : ℕ} (μ : YoungDiagram) (hn : μ.card ≤ n)
    (Y : Finset (Fin n)) : conjugateTail n μ Y.card ≤ Y.card := by
  classical
  let U : ↥μ.cells ↪ Fin n := (Fintype.equivFin ↥μ.cells).toEmbedding.trans
    (Fin.castLEEmb (by simpa only [Fintype.card_coe, YoungDiagram.card] using hn))
  let J := (Finset.range n).filter fun j => columnLabels U j ⊆ Y
  have hJ : (↑J : Set ℕ).PairwiseDisjoint (columnLabels U) :=
    (columnLabels_pairwiseDisjoint U).subset (Set.subset_univ _)
  calc
    conjugateTail n μ Y.card ≤ ∑ j ∈ J, (columnLabels U j).card :=
      columnLabels_complete_card_ge_tail U Y
    _ = (J.biUnion (columnLabels U)).card := (Finset.card_biUnion hJ).symm
    _ ≤ Y.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun j hj =>
      (Finset.mem_filter.mp hj).2)

theorem columnTail_erase {μ : YoungDiagram} {c : ℕ × ℕ}
    (hc : YoungDiagram.IsCorner μ c) (h : ℕ) :
    columnTail (μ.erase c) h = if h ≤ c.2 then columnTail μ h - 1 else columnTail μ h := by
  rw [columnTail, hc.cells_erase, Finset.filter_erase, Finset.card_erase_eq_ite]
  simp only [Finset.mem_filter, YoungDiagram.mem_cells, hc.mem, true_and, columnTail]

theorem columnTail_pos_of_corner {μ : YoungDiagram} {c : ℕ × ℕ}
    (hc : YoungDiagram.IsCorner μ c) {h : ℕ} (hh : h ≤ c.2) : 0 < columnTail μ h := by
  exact Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc.mem, hh⟩⟩

variable {R : Type*} [CommRing R]

/-- The standard extension needed by the recursion.  Unlike the principal
range, degree zero is allowed precisely when the numerical threshold says so. -/
def extendedElementaryIdeal (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :
    Ideal (PolynomialRing n R) :=
  Ideal.span {p | ∃ (Y : Finset (Fin n)) (d : ℕ), d ≤ Y.card ∧
    (Y.card : ℤ) - (columnTail μ (n - Y.card) : ℤ) < d ∧ p = elementaryOn Y d}

theorem elementaryOn_mem_extended {n : ℕ} {μ : YoungDiagram}
    (Y : Finset (Fin n)) (d : ℕ)
    (hd : (Y.card : ℤ) - (columnTail μ (n - Y.card) : ℤ) < d) :
    elementaryOn (R := R) Y d ∈ extendedElementaryIdeal R n μ := by
  by_cases hm : d ≤ Y.card
  · exact Ideal.subset_span ⟨Y, d, hm, hd, rfl⟩
  · rw [elementaryOn_eq_zero_of_card_lt (Nat.lt_of_not_ge hm)]
    exact Ideal.zero_mem _

theorem extendedElementaryIdeal_eq_untruncated {n : ℕ} (μ : YoungDiagram)
    (hn : μ.card ≤ n) : extendedElementaryIdeal R n μ = untruncatedIdeal R n μ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hth, rfl⟩
    rw [columnTail_eq_conjugateTail μ hn] at hth
    have htail := conjugateTail_le_card μ hn Y
    apply elementaryOn_mem_untruncatedIdeal Y (by omega) hd hth
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hcard, hth, rfl⟩
    exact elementaryOn_mem_extended Y d (by rwa [columnTail_eq_conjugateTail μ hn])

theorem extendedElementaryIdeal_eq_top_of_card_gt {n : ℕ} (μ : YoungDiagram)
    (hn : n < μ.card) : extendedElementaryIdeal R n μ = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := elementaryOn_mem_extended (R := R) (μ := μ) (Finset.univ : Finset (Fin n)) 0
    (by simpa only [Finset.card_univ, Fintype.card_fin, Nat.sub_self, columnTail_zero] using
      (show (n : ℤ) - (μ.card : ℤ) < (0 : ℕ) by omega))
  simpa only [elementaryOn_zero] using h

theorem elementaryOn_insert_succ {n : ℕ} (Y : Finset (Fin n)) {i : Fin n}
    (hi : i ∉ Y) (d : ℕ) :
    elementaryOn (R := R) (insert i Y) (d + 1) =
      elementaryOn Y (d + 1) + MvPolynomial.X i * elementaryOn Y d := by
  have hprod : elementaryGenerating (R := R) (insert i Y) = elementaryGenerating Y +
      Polynomial.C (MvPolynomial.X i) * (elementaryGenerating Y * Polynomial.X) := by
    rw [elementaryGenerating, Finset.prod_insert hi]
    change (1 + Polynomial.C (MvPolynomial.X i) * Polynomial.X) * elementaryGenerating Y = _
    ring
  have hcoeff := congrArg (fun p : Polynomial (PolynomialRing n R) => p.coeff (d + 1)) hprod
  simpa only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X,
    elementaryGenerating_coeff] using hcoeff

/-- The telescoping part of Yu's lift, proved by induction inside an
arbitrary ideal over an arbitrary commutative coefficient ring. -/
theorem pow_mul_elementaryOn_mem_of_insert {n : ℕ} (I : Ideal (PolynomialRing n R))
    (Y : Finset (Fin n)) {i : Fin n} (hi : i ∉ Y) (a d : ℕ)
    (hinsert : ∀ e : ℕ, d < e → elementaryOn (insert i Y) e ∈ I)
    (hend : elementaryOn Y (d + a) ∈ I) :
    MvPolynomial.X i ^ a * elementaryOn Y d ∈ I := by
  induction a generalizing d with
  | zero => simpa using hend
  | succ a ih =>
    have hlast : elementaryOn Y ((d + 1) + a) ∈ I := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
    have hrec := ih (d + 1) (fun e he => hinsert e (by omega)) hlast
    have hfirst := I.mul_mem_left (MvPolynomial.X i ^ a) (hinsert (d + 1) (by omega))
    have heq : (MvPolynomial.X i : PolynomialRing n R) ^ (a + 1) * elementaryOn Y d =
        MvPolynomial.X i ^ a * elementaryOn (insert i Y) (d + 1) -
          MvPolynomial.X i ^ a * elementaryOn Y (d + 1) := by
      rw [elementaryOn_insert_succ Y hi, pow_succ]
      ring
    rw [heq]
    exact I.sub_mem hfirst hrec

/-- The second branch of the actual integral generator lift.  The height
bound is exactly the one obtained by erasing a corner to the left of the
cut in the conjugate tail. -/
theorem yu_generator_lift_left {n : ℕ} (μ : YoungDiagram) (Y : Finset (Fin (n + 1)))
    {i : Fin (n + 1)} (hi : i ∉ Y) (a d : ℕ)
    (ha : μ.colLen (n - Y.card) ≤ a)
    (hd : (Y.card : ℤ) - (columnTail μ (n - Y.card) : ℤ) < d) :
    MvPolynomial.X i ^ a * elementaryOn (R := R) Y d ∈
      extendedElementaryIdeal R (n + 1) μ := by
  have hm : Y.card ≤ n := by
    have hh := Finset.card_insert_of_notMem hi
    have hh' := Finset.card_le_univ (insert i Y)
    simp only [Fintype.card_fin, hh] at hh'
    omega
  apply pow_mul_elementaryOn_mem_of_insert _ Y hi a d
  · intro e he
    apply elementaryOn_mem_extended
    rw [Finset.card_insert_of_notMem hi]
    have heq : n + 1 - (Y.card + 1) = n - Y.card := by omega
    rw [heq]
    omega
  · apply elementaryOn_mem_extended
    have ht := columnTail_succ μ (n - Y.card)
    have heq : n + 1 - Y.card = n - Y.card + 1 := by omega
    rw [heq]
    omega

def yuGeneratorLift {n : ℕ} (μ : YoungDiagram) (c : Option (ℕ × ℕ))
    (Y : Finset (Fin (n + 1))) (i : Fin (n + 1)) (d : ℕ) : PolynomialRing (n + 1) R :=
  match c with
  | none => MvPolynomial.X i ^ μ.colLen 0 * elementaryOn Y d
  | some cell => MvPolynomial.X i ^ μ.colLen (cell.2 + 1) *
      elementaryOn (if n - Y.card ≤ cell.2 then insert i Y else Y) d

/-- Yu's Lemma 4.2, including the zero-degree generators in the transient
oversized partition case, as genuine ideal membership over every ring. -/
theorem yu_generator_lift_mem {n : ℕ} (μ : YoungDiagram) (c : Option (ℕ × ℕ))
    (hc : ∀ cell, c = some cell → YoungDiagram.IsCorner μ cell)
    (Y : Finset (Fin (n + 1))) {i : Fin (n + 1)} (hi : i ∉ Y) (d : ℕ)
    (hd : (Y.card : ℤ) - (columnTail (match c with | none => μ | some cell => μ.erase cell)
      (n - Y.card) : ℤ) < d) :
    yuGeneratorLift (R := R) μ c Y i d ∈ extendedElementaryIdeal R (n + 1) μ := by
  cases c with
  | none =>
    exact yu_generator_lift_left μ Y hi _ d (μ.colLen_anti 0 _ (Nat.zero_le _)) hd
  | some c =>
    have hc' := hc c rfl
    dsimp only at hd
    rw [columnTail_erase hc'] at hd
    by_cases hcut : n - Y.card ≤ c.2
    · rw [if_pos hcut] at hd
      simp only [yuGeneratorLift, if_pos hcut]
      apply Ideal.mul_mem_left
      apply elementaryOn_mem_extended
      rw [Finset.card_insert_of_notMem hi]
      have hpos := columnTail_pos_of_corner hc' hcut
      have heq : n + 1 - (Y.card + 1) = n - Y.card := by omega
      rw [heq]
      omega
    · rw [if_neg hcut] at hd
      simp only [yuGeneratorLift, if_neg hcut]
      exact yu_generator_lift_left μ Y hi _ d
        (μ.colLen_anti (c.2 + 1) _ (by omega)) hd

end HigherSpecht
end
end CanonicalSource31
