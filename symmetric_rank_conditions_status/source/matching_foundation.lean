module
public import matching_insertion_core
public import matching_median_audit
public import Aesop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Logic.Relation
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SplitIfs

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 1000
run_cmd do
  let progressOutput ← IO.getStdout
  progressOutput.putStrLn "MatchingFoundation imports loaded"
  progressOutput.flush

/-! Combinatorial foundation for the symmetric-rank formalization.

This module combines the matching bijection and descent theorem, Young-diagram
and standard-tableau geometry, dual connectivity, literal monomial coordinates,
exact carrier arithmetic, ordinary Knuth equivalence, and tableau duality.
It deliberately has no dependency on polynomial ideals or SymmetricLocal.
Recovered mathematical proof bodies are retained; the final axiom audit is
performed once on the resulting theorem dependency graph.
-/

/- SOURCE COMPONENT MatchingBijectionCore -/

/- EXACT SOURCE FourPapers.Symmetric.MatchingBijection -/
section

set_option autoImplicit false

/-!
# The matching part of the paired-insertion bijection

A matching is represented without losing its incidences: its pairs have distinct
endpoint occurrences, smaller endpoint first, and increasing larger endpoints.
The target consists of genuine semistandard tableaux with distinct entries and even
row lengths. This is the fixed-point-free part of column Beissinger insertion.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

/-- The lightweight insertion-base predicate is exactly Mathlib's parity
predicate, with no change to the meaning of an even-row tableau. -/
theorem evenRows_iff_nat_even (rows : List (List α)) :
    EvenRows rows ↔ ∀ i, Even ((rows.getD i []).length) := Iff.rfl

 theorem endpointWord_append (xs ys : List (α × α)) :
    endpointWord (xs ++ ys) = endpointWord xs ++ endpointWord ys := by
  simp [endpointWord]

 theorem mem_endpointWord {w : List (α × α)} {x : α} :
    x ∈ endpointWord w ↔ ∃ p ∈ w, x = p.1 ∨ x = p.2 := by
  simp [endpointWord]

/-- An ordered list containing every edge of a matching exactly once. -/
structure MatchingWord (w : List (α × α)) : Prop where
  lower_lt_upper : ∀ p ∈ w, p.1 < p.2
  ordered : w.Pairwise (fun p q => p.2 < q.2)
  distinct : (endpointWord w).Nodup

@[simp] theorem matchingWord_nil : MatchingWord ([] : List (α × α)) := by
  constructor <;> simp [endpointWord]

 theorem MatchingWord.prefix {w v : List (α × α)} (h : MatchingWord (w ++ v)) :
    MatchingWord w := by
  refine ⟨fun p hp => h.lower_lt_upper p (List.mem_append_left _ hp),
    (List.pairwise_append.mp h.ordered).1, ?_⟩
  have hd := h.distinct
  rw [endpointWord_append] at hd
  exact (List.nodup_append.mp hd).1

 theorem MatchingWord.before_last {w : List (α × α)} {p : α × α}
    (h : MatchingWord (w ++ [p])) : ∀ x ∈ endpointWord w, x < p.2 := by
  intro x hx
  obtain ⟨q, hq, rfl | rfl⟩ := mem_endpointWord.mp hx
  · exact (h.lower_lt_upper q (List.mem_append_left _ hq)).trans
      ((List.pairwise_append.mp h.ordered).2.2 q hq p (by simp))
  · exact (List.pairwise_append.mp h.ordered).2.2 q hq p (by simp)

/-- The output on every matching is a semistandard tableau. -/
theorem MatchingWord.isTableauRows {w : List (α × α)} (h : MatchingWord w) :
    (pairInsertList w).IsTableauRows := by
  induction w using List.reverseRecOn with
  | nil => exact List.isTableauRows_nil
  | append_singleton w p ih =>
    have hw : MatchingWord w := h.prefix
    rw [pairInsertList_append]
    change (pairInsert p.1 p.2 (pairInsertList w)).IsTableauRows
    apply isTableauRows_pairInsert_fresh (ih hw) (evenRows_nil.pairInsertList w)
      (h.lower_lt_upper p (by simp))
    intro x hx
    have hc := (flatten_pairInsertList_perm w []).mem_iff.mp hx
    exact h.before_last x (by simpa using hc)

 theorem MatchingWord.output_distinct {w : List (α × α)} (h : MatchingWord w) :
    (pairInsertList w).flatten.Nodup := by
  apply (flatten_pairInsertList_perm w []).nodup_iff.mpr
  simpa using h.distinct

/-- Every nonempty even-row standard tableau can be reversed by one genuine paired
step, deleting exactly two endpoint occurrences. -/
theorem exists_reverse_paired_step {rows : List (List α)} (hrows : rows.IsTableauRows)
    (heven : EvenRows rows) (hnd : rows.flatten.Nodup) (hne : rows.flatten ≠ []) :
    ∃ (a b : α) (previous : List (List α)),
      previous.IsTableauRows ∧ EvenRows previous ∧ previous.flatten.Nodup ∧
      a < b ∧ (∀ x ∈ previous.flatten, x < b) ∧
      pairInsert a b previous = rows ∧
      previous.flatten.length + 2 = rows.flatten.length := by
  classical
  let S := rows.flatten.toFinset
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  let b := S.max' hS
  have hb : b ∈ rows.flatten := by
    exact List.mem_toFinset.mp (Finset.max'_mem S hS)
  have hmax : ∀ x ∈ rows.flatten, x ≤ b := by
    intro x hx
    exact Finset.le_max' S x (List.mem_toFinset.mpr hx)
  obtain ⟨k, hlast⟩ := hrows.exists_getLast?_getD_eq_some hb hmax
  have hcorner := hrows.length_getD_succ_lt_of_getLast?_eq_some hmax hlast
  let middle := dropLastOfRow k rows
  have hm : middle.IsTableauRows := hrows.dropLastOfRow hcorner
  have hlenMiddle (i : ℕ) : (middle.getD i []).length =
      if i = k then (rows.getD k []).length - 1 else (rows.getD i []).length := by
    dsimp only [middle]
    rw [getD_dropLastOfRow hrows hcorner]
    split_ifs <;> simp only [List.length_dropLast]
  have hmcorner : (middle.getD (k + 1) []).length < (middle.getD k []).length := by
    rw [hlenMiddle, hlenMiddle]
    simp only [Nat.add_one_ne_self, if_false, if_true]
    obtain ⟨s, hs⟩ := heven k
    obtain ⟨t, ht⟩ := heven (k + 1)
    omega
  obtain ⟨a, ha, hins, hindex⟩ := rowInsert_reverseRowInsert hm hmcorner
  let previous := (reverseRowInsert k middle).1
  have hp : previous.IsTableauRows := hm.reverseRowInsert hmcorner
  have hpaired : pairInsert a b previous = rows := by
    rw [pairInsert, hindex, hins]
    exact appendToRow_dropLastOfRow hrows hcorner hlast
  have hplen (i : ℕ) := length_getD_rowInsert a previous i
  rw [hins, hindex] at hplen
  have hpeven : EvenRows previous := by
    intro i
    have hlen := hplen i
    rw [hlenMiddle] at hlen
    obtain ⟨s, hs⟩ := heven i
    by_cases hik : i = k
    · subst i
      simp only [if_true] at hlen
      have htwo : 2 ≤ (rows.getD k []).length := by omega
      refine ⟨s - 1, ?_⟩
      omega
    · simp only [if_neg hik, Nat.add_zero] at hlen
      exact ⟨s, by omega⟩
  have hcontent : rows.flatten.Perm (a :: b :: previous.flatten) := by
    rw [← hpaired]
    exact flatten_pairInsert_perm a b previous
  have hnd' := hnd.perm hcontent
  have hnp : previous.flatten.Nodup := hnd'.of_cons.of_cons
  have habne : a ≠ b := by
    intro hab
    exact (List.nodup_cons.mp hnd').1 (by simp [hab])
  have hab : a < b := lt_of_le_of_ne
    (hmax a (hcontent.mem_iff.mpr (by simp))) habne
  have hpmax : ∀ x ∈ previous.flatten, x < b := by
    intro x hx
    apply lt_of_le_of_ne (hmax x (hcontent.mem_iff.mpr (by simp [hx])))
    intro hxb
    exact (List.nodup_cons.mp hnd'.of_cons).1 (hxb ▸ hx)
  refine ⟨a, b, previous, hp, hpeven, hnp, hab, hpmax, hpaired, ?_⟩
  have := hcontent.length_eq
  simp only [List.length_cons] at this
  omega

theorem exists_matchingWord_aux (d : ℕ) :
    ∀ rows : List (List α), rows.flatten.length = d →
      rows.IsTableauRows → EvenRows rows → rows.flatten.Nodup →
      ∃ w : List (α × α), MatchingWord w ∧ pairInsertList w = rows := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro rows hlen hrows heven hnd
    by_cases hnil : rows.flatten = []
    · have hrnil : rows = [] := by
        cases rows with
        | nil => rfl
        | cons row rows =>
          have hr : row = [] := (List.append_eq_nil_iff.mp hnil).1
          exact False.elim (hrows.nil_notMem (by simp [hr]))
      subst rows
      exact ⟨[], matchingWord_nil, rfl⟩
    · obtain ⟨a, b, previous, hp, hpeven, hpnd, hab, hpmax, hpaired, hsize⟩ :=
        exists_reverse_paired_step hrows heven hnd hnil
      have hd : previous.flatten.length < d := by omega
      obtain ⟨w, hw, hwrows⟩ := ih previous.flatten.length hd previous rfl hp hpeven hpnd
      have hout : pairInsertList (w ++ [(a, b)]) = rows := by
        rw [pairInsertList_append, hwrows]
        exact hpaired
      refine ⟨w ++ [(a, b)], ?_, hout⟩
      constructor
      · intro p hp'
        rcases List.mem_append.mp hp' with hp' | hp'
        · exact hw.lower_lt_upper p hp'
        · have hp'' := List.mem_singleton.mp hp'
          subst p
          exact hab
      · apply List.pairwise_append.mpr
        refine ⟨hw.ordered, by simp, ?_⟩
        intro p hp' q hq
        have hq' : q = (a, b) := List.mem_singleton.mp hq
        subst q
        apply hpmax p.2
        rw [← hwrows]
        apply (flatten_pairInsertList_perm w []).mem_iff.mpr
        simp only [List.flatten_nil, List.append_nil]
        exact mem_endpointWord.mpr ⟨p, hp', Or.inr rfl⟩
      · have hc := (flatten_pairInsertList_perm (w ++ [(a, b)]) [])
        rw [hout] at hc
        simpa using hnd.perm hc

/-- Surjectivity onto all standard tableaux with even row lengths, over every
linearly ordered alphabet and without a bound on the number of matching edges. -/
theorem exists_matchingWord {rows : List (List α)} (hrows : rows.IsTableauRows)
    (heven : EvenRows rows) (hnd : rows.flatten.Nodup) :
    ∃ w : List (α × α), MatchingWord w ∧ pairInsertList w = rows :=
  exists_matchingWord_aux rows.flatten.length rows rfl hrows heven hnd

/-- Each input edge contributes exactly two tableau entries. -/
theorem endpointWord_length (w : List (α × α)) : (endpointWord w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      simp only [endpointWord, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil] at ih ⊢
      omega

 theorem pairInsertList_flatten_length (w : List (α × α)) :
    (pairInsertList w).flatten.length = 2 * w.length := by
  have h := (flatten_pairInsertList_perm w []).length_eq
  simpa only [List.flatten_nil, List.append_nil, endpointWord_length] using h

@[simp] theorem pairInsertList_append_singleton (w : List (α × α)) (p : α × α) :
    pairInsertList (w ++ [p]) = pairInsert p.1 p.2 (pairInsertList w) := by
  rw [pairInsertList_append]
  rfl

 theorem MatchingWord.tableau_le_last {w : List (α × α)} {p : α × α}
    (h : MatchingWord (w ++ [p])) :
    ∀ x ∈ (pairInsertList (w ++ [p])).flatten, x ≤ p.2 := by
  intro x hx
  have hx' := (flatten_pairInsertList_perm (w ++ [p]) []).mem_iff.mp hx
  simp only [List.flatten_nil, List.append_nil, endpointWord_append] at hx'
  rcases List.mem_append.mp hx' with hx' | hx'
  · exact (h.before_last x hx').le
  · have hp : p.1 < p.2 := h.lower_lt_upper p (by simp)
    simp only [endpointWord, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact hp.le
    · exact le_rfl

theorem last_endpoint_mem (w : List (α × α)) (p : α × α) :
    p.2 ∈ (pairInsertList (w ++ [p])).flatten := by
  apply (flatten_pairInsertList_perm (w ++ [p]) []).mem_iff.mpr
  simp only [List.flatten_nil, List.append_nil]
  exact mem_endpointWord.mpr ⟨p, by simp, Or.inr rfl⟩

/-- Paired insertion is injective on every finite matching, not merely on a
bounded collection of matchings. -/
theorem pairInsertList_injOn_matching :
    Set.InjOn (fun w : List (α × α) => pairInsertList w) {w | MatchingWord w} := by
  intro w hw v hv heq
  change pairInsertList w = pairInsertList v at heq
  induction w using List.reverseRecOn generalizing v with
  | nil =>
    have hl := pairInsertList_flatten_length v
    rw [← heq] at hl
    have hv0 : v.length = 0 := by simpa using hl.symm
    exact (List.length_eq_zero_iff.mp hv0).symm
  | append_singleton w p ih =>
    obtain rfl | ⟨v, q, rfl⟩ := v.eq_nil_or_concat'
    · have hl := pairInsertList_flatten_length (w ++ [p])
      rw [heq] at hl
      simp only [pairInsertList, List.foldl_nil, List.flatten_nil, List.length_nil,
        List.length_append, List.length_singleton] at hl
      omega
    rcases p with ⟨a, b⟩
    rcases q with ⟨a', b'⟩
    have hbb' : b ≤ b' := hv.tableau_le_last b (by
      rw [← heq]
      exact last_endpoint_mem w (a, b))
    have hb'b : b' ≤ b := hw.tableau_le_last b' (by
      rw [heq]
      exact last_endpoint_mem v (a', b'))
    have hb : b = b' := le_antisymm hbb' hb'b
    subst b'
    have hw' : MatchingWord w := hw.prefix
    have hv' : MatchingWord v := hv.prefix
    have hba : b ≠ a := (hw.lower_lt_upper (a, b) (by simp)).ne.symm
    have hba' : b ≠ a' := (hv.lower_lt_upper (a', b) (by simp)).ne.symm
    have hbnot : b ∉ (pairInsertList w).flatten := by
      intro hx
      have hc := (flatten_pairInsertList_perm w []).mem_iff.mp hx
      exact (lt_irrefl b) (hw.before_last b (by simpa using hc))
    have hbnot' : b ∉ (pairInsertList v).flatten := by
      intro hx
      have hc := (flatten_pairInsertList_perm v []).mem_iff.mp hx
      exact (lt_irrefl b) (hv.before_last b (by simpa using hc))
    rw [pairInsertList_append_singleton, pairInsertList_append_singleton] at heq
    obtain ⟨ha, hprev⟩ := pairInsert_injective_fresh hw'.isTableauRows hv'.isTableauRows
      hba hba' hbnot hbnot' heq
    have hwv : w = v := ih hw' hv' hprev
    subst v
    subst a'
    rfl

/-- The complete matching/standard-even-tableau bijection, with explicit source
and target properties. -/
noncomputable def matchingTableauEquiv :
    {w : List (α × α) // MatchingWord w} ≃
      {rows : List (List α) // rows.IsTableauRows ∧ EvenRows rows ∧ rows.flatten.Nodup} :=
  Equiv.ofBijective
    (fun w => ⟨pairInsertList w.val, w.property.isTableauRows,
      evenRows_nil.pairInsertList _, w.property.output_distinct⟩)
    ⟨by
      intro w v h
      apply Subtype.ext
      exact pairInsertList_injOn_matching w.property v.property (congrArg Subtype.val h),
      by
      intro rows
      obtain ⟨w, hw, hrows⟩ := exists_matchingWord rows.property.1 rows.property.2.1
        rows.property.2.2
      exact ⟨⟨w, hw⟩, Subtype.ext hrows⟩⟩

end FourPapers.Symmetric

end

/- EXACT SOURCE FourPapers.Symmetric.InsertionDescents -/
section

set_option autoImplicit false

/-!
# Consecutive-label descents under row insertion

This file supplies the ordinary row-insertion part of the descent rule needed for
the matching correspondence. A descent is defined by the actual positions of the
two labels, rather than by a purported matching statistic.
-/

open TauCeti

namespace FourPapers.Symmetric

/-- The label `y` lies in a strictly lower row than `x`. The recursive definition
also works for lists of rows before proving their tableau properties. -/
def RowDescends {α : Type*} [DecidableEq α] (x y : α) : List (List α) → Prop
  | [] => False
  | row :: rows => (x ∈ row ∧ y ∈ rows.flatten) ∨
      (x ∉ row ∧ y ∉ row ∧ RowDescends x y rows)

@[simp] theorem rowDescends_nil {α : Type*} [DecidableEq α] (x y : α) :
    ¬RowDescends x y [] := id

@[simp] theorem rowDescends_cons {α : Type*} [DecidableEq α]
    (x y : α) (row : List α) (rows : List (List α)) :
    RowDescends x y (row :: rows) ↔ (x ∈ row ∧ y ∈ rows.flatten) ∨
      (x ∉ row ∧ y ∉ row ∧ RowDescends x y rows) := Iff.rfl

 theorem RowDescends.mem_left {α : Type*} [DecidableEq α] {x y : α}
    {rows : List (List α)} (h : RowDescends x y rows) : x ∈ rows.flatten := by
  induction rows with
  | nil => exact False.elim h
  | cons row rows ih =>
    rcases h with h | h
    · exact List.mem_append_left _ h.1
    · exact List.mem_append_right _ (ih h.2.2)

 theorem RowDescends.mem_right {α : Type*} [DecidableEq α] {x y : α}
    {rows : List (List α)} (h : RowDescends x y rows) : y ∈ rows.flatten := by
  induction rows with
  | nil => exact False.elim h
  | cons row rows ih =>
    rcases h with h | h
    · exact List.mem_append_right _ h.2
    · exact List.mem_append_right _ (ih h.2.2)

 theorem not_rowDescends_of_mem_head {α : Type*} [DecidableEq α] {x y : α}
    {row : List α} {rows : List (List α)} (hnd : (row :: rows).flatten.Nodup)
    (hy : y ∈ row) : ¬RowDescends x y (row :: rows) := by
  have hn : y ∉ rows.flatten := by
    exact fun hyt => (List.nodup_append.mp hnd).2.2 y hy y hyt rfl
  simp only [rowDescends_cons, hy, hn, and_false, false_or, not_true_eq_false, false_and]
  exact not_false

theorem rowBump_mem_some {α : Type*} [LinearOrder α] {a c z : α} {row : List α}
    (hnd : row.Nodup) (h : (rowBump a row).2 = some c) :
    z ∈ (rowBump a row).1 ↔ z = a ∨ z ∈ row ∧ z ≠ c := by
  obtain ⟨before, after, hr, hout, hbefore, hac⟩ :=
    (rowBump_eq_some_iff a c row (rowBump a row).1).mp (Prod.ext rfl h)
  have hc1 : c ∉ before := by
    intro hc
    exact (not_le_of_gt hac) (hbefore c hc)
  have hc2 : c ∉ after := by
    rw [hr, List.nodup_append] at hnd
    exact (List.nodup_cons.mp hnd.2.1).1
  rw [hout, hr]
  by_cases hzc : z = c
  · subst z
    simp [hc1, hc2, (ne_of_lt hac).symm]
  · simp only [List.mem_append, List.mem_cons, hzc, false_or, ne_eq,
      not_false_eq_true, and_true]
    tauto

theorem mem_rowInsert {α : Type*} [LinearOrder α] {a z : α}
    {rows : List (List α)} :
    z ∈ (rowInsert a rows).flatten ↔ z = a ∨ z ∈ rows.flatten := by
  rw [(flatten_rowInsert_perm a rows).mem_iff]
  simp

theorem rowInsert_nodup {α : Type*} [LinearOrder α] {a : α}
    {rows : List (List α)} (hnd : rows.flatten.Nodup) (ha : a ∉ rows.flatten) :
    (rowInsert a rows).flatten.Nodup :=
  (flatten_rowInsert_perm a rows).nodup_iff.mpr (List.nodup_cons.mpr ⟨ha, hnd⟩)

/-- Inserting a new letter puts that letter in the first row. -/
theorem mem_head_rowInsert {α : Type*} [LinearOrder α] (a : α) (rows : List (List α)) :
    a ∈ (rowInsert a rows).headD [] := by
  cases rows with
  | nil => simp
  | cons row rows =>
    rw [headD_rowInsert]
    have hmem := (rowBump_perm a row).mem_iff.mpr (by simp : a ∈ a :: row)
    rw [List.mem_append] at hmem
    rcases hmem with hm | hm
    · exact hm
    · cases h : (rowBump a row).2 with
      | none => simp [h] at hm
      | some c =>
        have hac := lt_of_rowBump_snd_eq_some h
        simp only [h, Option.toList_some, List.mem_singleton] at hm
        exact False.elim ((ne_of_lt hac) hm)

/-- A newly inserted label cannot be below an old label in the resulting tableau. -/
theorem not_rowDescends_rowInsert_new_right {α : Type*} [LinearOrder α] (x a : α)
    {rows : List (List α)} (hnd : rows.flatten.Nodup) (ha : a ∉ rows.flatten) :
    ¬RowDescends x a (rowInsert a rows) := by
  have hn := rowInsert_nodup hnd ha
  have hm := mem_head_rowInsert a rows
  cases he : rowInsert a rows with
  | nil => simp [he]
  | cons row rows =>
    rw [he] at hn hm
    exact not_rowDescends_of_mem_head hn hm

/-- If a row contains `k+1`, inserting `k` bumps exactly that letter. -/
theorem rowBump_consecutive {k : ℕ} {row : List ℕ} (hs : row.SortedLE)
    (hk : k + 1 ∈ row) : (rowBump k row).2 = some (k + 1) := by
  cases h : (rowBump k row).2 with
  | none =>
    have hle := (rowBump_snd_eq_none_iff k row).mp h (k + 1) hk
    omega
  | some c =>
    obtain ⟨before, after, hr, hout, hbefore, hkc⟩ :=
      (rowBump_eq_some_iff k c row (rowBump k row).1).mp (Prod.ext rfl h)
    have hc : c ≤ k + 1 := by
      rw [hr, List.mem_append, List.mem_cons] at hk
      rcases hk with hk | hk | hk
      · have := hbefore (k + 1) hk
        omega
      · omega
      · rw [hr, List.sortedLE_append] at hs
        exact (List.sortedLE_cons.mp hs.2.1).1 _ hk
    have heq : c = k + 1 := by omega
    simpa [heq] using h

/-- Inserting the predecessor of an existing label creates its descent. -/
theorem rowDescends_rowInsert_new_left {k : ℕ} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hnd : rows.flatten.Nodup)
    (hk : k ∉ rows.flatten) (hs : k + 1 ∈ rows.flatten) :
    RowDescends k (k + 1) (rowInsert k rows) := by
  cases rows with
  | nil => simp at hs
  | cons row rows =>
    have ht := hrows.tail
    rcases List.mem_append.mp hs with hs | hs
    · have hb := rowBump_consecutive (hrows.sortedLE _ (by simp)) hs
      rw [rowInsert_cons_of_eq_some rows hb, rowDescends_cons]
      refine Or.inl ⟨?_, ?_⟩
      · exact (rowBump_mem_some (List.nodup_append.mp hnd).1 hb).mpr (Or.inl rfl)
      · exact mem_rowInsert.mpr (Or.inl rfl)
    · cases hb : (rowBump k row).2 with
      | none =>
        rw [rowInsert_cons_of_eq_none rows hb, rowDescends_cons]
        refine Or.inl ⟨?_, hs⟩
        have hm := (rowBump_perm k row).mem_iff.mpr (by simp : k ∈ k :: row)
        simpa [hb] using hm
      | some c =>
        rw [rowInsert_cons_of_eq_some rows hb, rowDescends_cons]
        exact Or.inl ⟨(rowBump_mem_some (List.nodup_append.mp hnd).1 hb).mpr (Or.inl rfl),
          mem_rowInsert.mpr (Or.inr hs)⟩

/-- A bump of `k+1` cannot jump over an existing `k`, unless the incoming letter
is precisely `k`. -/
theorem predecessor_not_mem_of_bump {a k : ℕ} {row : List ℕ}
    (hs : row.SortedLE) (ha : a ≠ k) (hb : (rowBump a row).2 = some (k + 1)) :
    k ∉ row := by
  obtain ⟨before, after, hr, hout, hbefore, hak⟩ :=
    (rowBump_eq_some_iff a (k + 1) row (rowBump a row).1).mp (Prod.ext rfl hb)
  intro hk
  rw [hr, List.mem_append, List.mem_cons] at hk
  rcases hk with hk | hk | hk
  · have := hbefore k hk
    omega
  · omega
  · rw [hr, List.sortedLE_append] at hs
    have := (List.sortedLE_cons.mp hs.2.1).1 _ hk
    omega

/-- Ordinary row insertion preserves descents between two consecutive old labels.
No tableau size bound is imposed. -/
theorem rowDescends_rowInsert_iff {a k : ℕ} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hnd : rows.flatten.Nodup)
    (ha : a ∉ rows.flatten) (hak : a ≠ k) (hak' : a ≠ k + 1)
    (hx : k ∈ rows.flatten) (hy : k + 1 ∈ rows.flatten) :
    RowDescends k (k + 1) (rowInsert a rows) ↔ RowDescends k (k + 1) rows := by
  induction rows generalizing a with
  | nil => simp at hx
  | cons row rows ih =>
    have hndR := (List.nodup_append.mp hnd).1
    have hndT := (List.nodup_append.mp hnd).2.1
    have hdis := (List.nodup_append.mp hnd).2.2
    have hsR := hrows.sortedLE row (by simp)
    have ht := hrows.tail
    cases hb : (rowBump a row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows hb,
        rowBump_of_forall_le a row ((rowBump_snd_eq_none_iff a row).mp hb)]
      simp only [rowDescends_cons, List.mem_append, List.mem_singleton,
        hak.symm, hak'.symm, or_false]
    | some c =>
      have hcR := mem_of_rowBump_snd_eq_some hb
      have hcT : c ∉ rows.flatten := fun hc => hdis c hcR c hc rfl
      have hxR : k ∈ (rowBump a row).1 ↔ k ∈ row ∧ k ≠ c := by
        simpa only [hak.symm, false_or] using rowBump_mem_some (z := k) hndR hb
      have hyR : k + 1 ∈ (rowBump a row).1 ↔ k + 1 ∈ row ∧ k + 1 ≠ c := by
        simpa only [hak'.symm, false_or] using rowBump_mem_some (z := k + 1) hndR hb
      rw [rowInsert_cons_of_eq_some rows hb]
      by_cases hcx : c = k
      · subst c
        by_cases hyr : k + 1 ∈ row
        · have hyt : k + 1 ∉ rows.flatten := fun hy => hdis _ hyr _ hy rfl
          simp [rowDescends_cons, hxR, hyR, hcR, hyr, mem_rowInsert, hyt]
        · have hyt : k + 1 ∈ rows.flatten := (List.mem_append.mp hy).resolve_left hyr
          have hdesc := rowDescends_rowInsert_new_left ht hndT hcT hyt
          simp [rowDescends_cons, hxR, hyR, hcR, hyr, hyt, hdesc]
      · by_cases hcy : c = k + 1
        · subst c
          have hxr : k ∉ row := predecessor_not_mem_of_bump hsR hak hb
          have hdesc := not_rowDescends_rowInsert_new_right k (k + 1) hndT hcT
          simp [rowDescends_cons, hxR, hyR, hxr, hcR, mem_rowInsert, hcT, hdesc]
        · have hxR' : (k ∈ (rowBump a row).1) ↔ k ∈ row := by
            simpa [Ne.symm hcx] using hxR
          have hyR' : (k + 1 ∈ (rowBump a row).1) ↔ k + 1 ∈ row := by
            simpa [Ne.symm hcy] using hyR
          have hxT : (k ∈ (rowInsert c rows).flatten) ↔ k ∈ rows.flatten := by
            simpa only [mem_rowInsert, Ne.symm hcx, false_or]
          have hyT : (k + 1 ∈ (rowInsert c rows).flatten) ↔ k + 1 ∈ rows.flatten := by
            simpa only [mem_rowInsert, Ne.symm hcy, false_or]
          by_cases hxr : k ∈ row
          · simp only [rowDescends_cons, hxR', hyR', hyT, hxr,
              true_and, not_true_eq_false, false_and, or_false]
          · by_cases hyr : k + 1 ∈ row
            · simp only [rowDescends_cons, hxR', hyR', hyT, hyr,
                not_true_eq_false, false_and, and_false, or_false]
            · have hxt : k ∈ rows.flatten := (List.mem_append.mp hx).resolve_left hxr
              have hyt : k + 1 ∈ rows.flatten := (List.mem_append.mp hy).resolve_left hyr
              have hind := ih ht hndT hcT hcx hcy hxt hyt
              simpa only [rowDescends_cons, hxR', hyR', hyT, hxr, hyr,
                false_and, false_or, not_false_eq_true, true_and] using hind

end FourPapers.Symmetric

end

/- EXACT SOURCE FourPapers.Symmetric.RowPositions -/
section

set_option autoImplicit false

/-!
# Actual row positions in paired insertion

The descent predicate is related to the genuine row indices found in the tableau.
In particular, the comparison for two successively processed largest endpoints is
proved from the row-bumping lemma, without appealing to a matching statistic.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

 theorem mem_flatten_of_findIdx?_eq_some {rows : List (List α)} {x : α} {i : ℕ}
    (h : rows.findIdx? (fun row => x ∈ row) = some i) : x ∈ rows.flatten := by
  obtain ⟨hi, hx, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact List.mem_flatten.mpr ⟨rows[i], List.getElem_mem hi, by simpa using hx⟩

 theorem rowDescends_iff_of_findIdx? {rows : List (List α)} {x y : α} {i j : ℕ}
    (hnd : rows.flatten.Nodup)
    (hx : rows.findIdx? (fun row => x ∈ row) = some i)
    (hy : rows.findIdx? (fun row => y ∈ row) = some j) :
    RowDescends x y rows ↔ i < j := by
  induction rows generalizing i j with
  | nil => simp at hx
  | cons row rows ih =>
    have hndT := (List.nodup_append.mp hnd).2.1
    have hdis := (List.nodup_append.mp hnd).2.2
    by_cases hxr : x ∈ row
    · have hi : i = 0 := by simpa [List.findIdx?_cons, hxr] using hx.symm
      subst i
      by_cases hyr : y ∈ row
      · have hj : j = 0 := by simpa [List.findIdx?_cons, hyr] using hy.symm
        subst j
        have hyt : y ∉ rows.flatten := fun hy => hdis y hyr y hy rfl
        simp only [rowDescends_cons, hxr, hyr, hyt, and_false, not_true_eq_false,
          false_and, or_self, lt_self_iff_false]
      · cases hfy : rows.findIdx? (fun r => y ∈ r) with
        | none => simp [List.findIdx?_cons, hyr, hfy] at hy
        | some q =>
          have hj : j = q + 1 := by
            simpa [List.findIdx?_cons, hyr, hfy] using hy.symm
          subst j
          have hyt := mem_flatten_of_findIdx?_eq_some hfy
          simp [rowDescends_cons, hxr, hyr, hyt]
    · by_cases hyr : y ∈ row
      · have hj : j = 0 := by simpa [List.findIdx?_cons, hyr] using hy.symm
        subst j
        simp [rowDescends_cons, hxr, hyr]
      · cases hfx : rows.findIdx? (fun r => x ∈ r) with
        | none => simp [List.findIdx?_cons, hxr, hfx] at hx
        | some p =>
          have hi : i = p + 1 := by
            simpa [List.findIdx?_cons, hxr, hfx] using hx.symm
          subst i
          cases hfy : rows.findIdx? (fun r => y ∈ r) with
          | none => simp [List.findIdx?_cons, hyr, hfy] at hy
          | some q =>
            have hj : j = q + 1 := by
              simpa [List.findIdx?_cons, hyr, hfy] using hy.symm
            subst j
            simpa [rowDescends_cons, hxr, hyr] using ih hndT hfx hfy

 theorem exists_findIdx?_mem {rows : List (List α)} {x : α} (hx : x ∈ rows.flatten) :
    ∃ i, rows.findIdx? (fun row => x ∈ row) = some i := by
  cases h : rows.findIdx? (fun row => x ∈ row) with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have hn := List.findIdx?_eq_none_iff.mp h
    obtain ⟨row, hr, hx⟩ := List.mem_flatten.mp hx
    have := hn row hr
    simpa [hx] using this

 theorem nodup_appendToRow {rows : List (List α)} {b : α} (k : ℕ)
    (hnd : rows.flatten.Nodup) (hb : b ∉ rows.flatten) :
    (appendToRow b k rows).flatten.Nodup := by
  apply (flatten_appendToRow_perm b k rows).nodup_iff.mpr
  refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
  intro a ha c hc heq
  have hcb : c = b := List.mem_singleton.mp hc
  exact hb (hcb ▸ heq ▸ ha)

/-- Appending a distinct fresh label leaves the relative rows of old labels
unchanged. -/
theorem rowDescends_appendToRow_iff {rows : List (List α)} {b x y : α} (k : ℕ)
    (hnd : rows.flatten.Nodup) (hb : b ∉ rows.flatten)
    (hx : x ∈ rows.flatten) (hy : y ∈ rows.flatten) :
    RowDescends x y (appendToRow b k rows) ↔ RowDescends x y rows := by
  have hxb : x ≠ b := by rintro rfl; exact hb hx
  have hyb : y ≠ b := by rintro rfl; exact hb hy
  obtain ⟨i, hi⟩ := exists_findIdx?_mem hx
  obtain ⟨j, hj⟩ := exists_findIdx?_mem hy
  have hi' := hi
  have hj' := hj
  rw [← findIdx?_mem_appendToRow_of_ne hxb k rows] at hi'
  rw [← findIdx?_mem_appendToRow_of_ne hyb k rows] at hj'
  rw [rowDescends_iff_of_findIdx? (nodup_appendToRow k hnd hb) hi' hj',
    rowDescends_iff_of_findIdx? hnd hi hj]

/-- Fresh paired insertion preserves descents of two old consecutive labels. -/
theorem rowDescends_pairInsert_old_iff {rows : List (List ℕ)} {a b k : ℕ}
    (hrows : rows.IsTableauRows) (hnd : rows.flatten.Nodup)
    (ha : a ∉ rows.flatten) (hb : b ∉ rows.flatten) (hab : a ≠ b)
    (hx : k ∈ rows.flatten) (hy : k + 1 ∈ rows.flatten) :
    RowDescends k (k + 1) (pairInsert a b rows) ↔ RowDescends k (k + 1) rows := by
  have hak : a ≠ k := by rintro rfl; exact ha hx
  have hak' : a ≠ k + 1 := by rintro rfl; exact ha hy
  have hb' : b ∉ (rowInsert a rows).flatten := by
    simp only [mem_rowInsert, not_or]
    exact ⟨hab.symm, hb⟩
  rw [pairInsert, rowDescends_appendToRow_iff _ (rowInsert_nodup hnd ha) hb'
    (mem_rowInsert.mpr (Or.inr hx)) (mem_rowInsert.mpr (Or.inr hy)),
    rowDescends_rowInsert_iff hrows hnd ha hak hak' hx hy]

/-- Exact descent comparison between the two new largest endpoints. This is the
last-pair case in the Beissinger matching descent rule. -/
theorem rowDescends_pairInsert_two_largest {rows : List (List α)} {a c b d : α}
    (hrows : rows.IsTableauRows) (hnd : rows.flatten.Nodup)
    (ha : a ∉ rows.flatten) (hc : c ∉ rows.flatten) (hac : a ≠ c)
    (hab : a < b) (hcb : c < b) (hbd : b < d)
    (hmax : ∀ x ∈ rows.flatten, x < b) :
    RowDescends b d (pairInsert c d (pairInsert a b rows)) ↔ c < a := by
  let middle := rowInsert a rows
  let previous := rowInsert c middle
  let s := rowInsertIndex a rows
  let t := rowInsertIndex c middle
  have hs : s ≤ middle.length := by
    dsimp [s, middle]
    rw [length_rowInsert]
    exact (Nat.le_succ _).trans (le_max_right _ _)
  have hmmax : ∀ x ∈ middle.flatten, x < b := by
    intro x hx
    rcases mem_rowInsert.mp hx with rfl | hx
    · exact hab
    · exact hmax x hx
  have hpmax : ∀ x ∈ previous.flatten, x < b := by
    intro x hx
    rcases mem_rowInsert.mp hx with rfl | hx
    · exact hcb
    · exact hmmax x hx
  have hc' : c ∉ middle.flatten := by
    simp only [middle, mem_rowInsert, not_or]
    exact ⟨hac.symm, hc⟩
  have hndP := rowInsert_nodup (rowInsert_nodup hnd ha) hc'
  have hrew : pairInsert c d (pairInsert a b rows) =
      appendToRow d (if t = s then s + 1 else t)
        (appendToRow b (if t = s then s + 1 else s) previous) := by
    unfold pairInsert
    rw [rowInsert_appendToRow hcb hmmax hs,
      rowInsertIndex_appendToRow hcb hmmax hs]
  have hrowb : (if t = s then s + 1 else s) ≤ previous.length :=
    le_length_rowInsert c hs
  have hbP : b ∉ previous.flatten := by intro hb; exact (lt_irrefl b) (hpmax b hb)
  have hdP : d ∉ previous.flatten := by
    intro hd
    exact (not_lt_of_ge hbd.le) (hpmax d hd)
  have hndB := nodup_appendToRow (if t = s then s + 1 else s) hndP hbP
  have hdB : d ∉ (appendToRow b (if t = s then s + 1 else s) previous).flatten := by
    rw [(flatten_appendToRow_perm _ _ _).mem_iff]
    simp [hdP, (ne_of_lt hbd).symm]
  have hind : (if t = s then s + 1 else t) ≤
      (appendToRow b (if t = s then s + 1 else s) previous).length := by
    rw [length_appendToRow _ hrowb]
    have ht : t ≤ previous.length := by
      dsimp [t, previous]
      rw [length_rowInsert]
      exact (Nat.le_succ _).trans (le_max_right _ _)
    split_ifs <;> omega
  have hfb : (appendToRow b (if t = s then s + 1 else s) previous).findIdx?
      (fun row => b ∈ row) = some (if t = s then s + 1 else s) := by
    apply findIdx?_mem_appendToRow_self _ hrowb
    intro row hr hbr
    exact hbP (List.mem_flatten.mpr ⟨row, hr, hbr⟩)
  have hfd : (appendToRow d (if t = s then s + 1 else t)
      (appendToRow b (if t = s then s + 1 else s) previous)).findIdx?
      (fun row => d ∈ row) = some (if t = s then s + 1 else t) := by
    apply findIdx?_mem_appendToRow_self _ hind
    intro row hr hdr
    exact hdB (List.mem_flatten.mpr ⟨row, hr, hdr⟩)
  rw [hrew, rowDescends_iff_of_findIdx? (nodup_appendToRow _ hndB hdB)
    (by simpa only [findIdx?_mem_appendToRow_of_ne (ne_of_lt hbd)] using hfb) hfd]
  have hcmp : t ≤ s ↔ a ≤ c := rowInsertIndex_le_iff hrows.sortedLE a c
  by_cases hts : t = s
  · simp only [hts, if_pos rfl, lt_self_iff_false, false_iff]
    have : a ≤ c := hcmp.mp (by omega)
    exact not_lt_of_ge this
  · simp only [if_neg hts]
    simpa only [not_le] using not_congr hcmp

end FourPapers.Symmetric

end

/- EXACT SOURCE FourPapers.Symmetric.MatchingDescents -/
section

set_option autoImplicit false

/-!
# The consecutive-label descent rule for actual paired insertion

Matching partners are the endpoints of an edge in the input matching itself.
This file compares them with the positions of consecutive labels in the tableau.
-/

open TauCeti

namespace FourPapers.Symmetric

variable {α : Type*} [LinearOrder α]

/-- Two labels are partners exactly when their unordered edge occurs in the
matching word. -/
def Partners (w : List (α × α)) (x y : α) : Prop := (x, y) ∈ w ∨ (y, x) ∈ w

 theorem Partners.symm {w : List (α × α)} {x y : α} (h : Partners w x y) :
    Partners w y x := Or.symm h

 theorem Partners.mem_left {w : List (α × α)} {x y : α} (h : Partners w x y) :
    x ∈ endpointWord w := by
  rcases h with h | h
  · exact mem_endpointWord.mpr ⟨(x, y), h, Or.inl rfl⟩
  · exact mem_endpointWord.mpr ⟨(y, x), h, Or.inr rfl⟩

 theorem Partners.mem_right {w : List (α × α)} {x y : α} (h : Partners w x y) :
    y ∈ endpointWord w := h.symm.mem_left

@[simp] theorem partners_append (v w : List (α × α)) (x y : α) :
    Partners (v ++ w) x y ↔ Partners v x y ∨ Partners w x y := by
  simp only [Partners, List.mem_append]
  tauto

@[simp] theorem partners_singleton (p : α × α) (x y : α) :
    Partners [p] x y ↔ (x = p.1 ∧ y = p.2) ∨ (x = p.2 ∧ y = p.1) := by
  simp [Partners, Prod.ext_iff, and_comm]

 theorem MatchingWord.last_fresh {w : List (α × α)} {a b : α}
    (h : MatchingWord (w ++ [(a, b)])) :
    a ∉ endpointWord w ∧ b ∉ endpointWord w := by
  have hd := h.distinct
  rw [endpointWord_append] at hd
  have hdis := (List.nodup_append.mp hd).2.2
  constructor
  · intro ha
    exact hdis a ha a (by simp [endpointWord]) rfl
  · intro hb
    exact hdis b hb b (by simp [endpointWord]) rfl

 theorem MatchingWord.eq_append_of_max {w : List (α × α)} {x y : α}
    (h : MatchingWord w) (hp : Partners w x y)
    (hmax : ∀ z ∈ endpointWord w, z ≤ x) :
    ∃ v, w = v ++ [(y, x)] := by
  have hyx : (y, x) ∈ w := by
    rcases hp with hp | hp
    · have hlt := h.lower_lt_upper (x, y) hp
      exact False.elim ((not_lt_of_ge (hmax y (Partners.mem_right (Or.inl hp)))) hlt)
    · exact hp
  obtain ⟨v, u, hw⟩ := List.mem_iff_append.mp hyx
  have hu : u = [] := by
    cases u with
    | nil => rfl
    | cons p u =>
      have hord := h.ordered
      rw [hw, List.pairwise_append, List.pairwise_cons] at hord
      have hlt : x < p.2 := hord.2.1.1 p (by simp)
      have hmem : p.2 ∈ endpointWord w := mem_endpointWord.mpr
        ⟨p, by simp [hw], Or.inr rfl⟩
      exact False.elim ((not_lt_of_ge (hmax p.2 hmem)) hlt)
  exact ⟨v, by simpa [hu] using hw⟩

 theorem nodup_pairInsert {rows : List (List α)} {a b : α}
    (hnd : rows.flatten.Nodup) (ha : a ∉ rows.flatten) (hb : b ∉ rows.flatten)
    (hab : a ≠ b) : (pairInsert a b rows).flatten.Nodup := by
  apply (flatten_pairInsert_perm a b rows).nodup_iff.mpr
  simp only [List.nodup_cons, List.mem_cons, not_or]
  exact ⟨⟨hab, ha⟩, hb, hnd⟩

 theorem not_rowDescends_pairInsert_of_index_zero {rows : List (List α)} {a b x : α}
    (hnd : rows.flatten.Nodup) (ha : a ∉ rows.flatten) (hb : b ∉ rows.flatten)
    (hab : a ≠ b) (hindex : rowInsertIndex a rows = 0) :
    ¬RowDescends x b (pairInsert a b rows) := by
  intro hd
  obtain ⟨i, hi⟩ := exists_findIdx?_mem hd.mem_left
  have hbpos := findIdx_pairInsert_fresh hab.symm hb
  rw [hindex] at hbpos
  have hh := (rowDescends_iff_of_findIdx? (nodup_pairInsert hnd ha hb hab) hi hbpos).mp hd
  omega

 theorem rowDescends_pairInsert_new_left {rows : List (List ℕ)} {b k : ℕ}
    (hrows : rows.IsTableauRows) (hnd : rows.flatten.Nodup)
    (hk : k ∉ rows.flatten) (hb : b ∉ rows.flatten) (hkb : k ≠ b)
    (hy : k + 1 ∈ rows.flatten) :
    RowDescends k (k + 1) (pairInsert k b rows) := by
  have hb' : b ∉ (rowInsert k rows).flatten := by
    simp only [mem_rowInsert, not_or]
    exact ⟨hkb.symm, hb⟩
  rw [pairInsert, rowDescends_appendToRow_iff _ (rowInsert_nodup hnd hk) hb'
    (mem_rowInsert.mpr (Or.inl rfl)) (mem_rowInsert.mpr (Or.inr hy))]
  exact rowDescends_rowInsert_new_left hrows hnd hk hy

 theorem not_rowDescends_pairInsert_new_right {rows : List (List ℕ)} {b k : ℕ}
    (hnd : rows.flatten.Nodup) (hk : k + 1 ∉ rows.flatten)
    (hb : b ∉ rows.flatten) (hkb : k + 1 ≠ b)
    (hx : k ∈ rows.flatten) :
    ¬RowDescends k (k + 1) (pairInsert (k + 1) b rows) := by
  have hb' : b ∉ (rowInsert (k + 1) rows).flatten := by
    simp only [mem_rowInsert, not_or]
    exact ⟨hkb.symm, hb⟩
  rw [pairInsert, rowDescends_appendToRow_iff _ (rowInsert_nodup hnd hk) hb'
    (mem_rowInsert.mpr (Or.inr hx)) (mem_rowInsert.mpr (Or.inl rfl))]
  exact not_rowDescends_rowInsert_new_right k (k + 1) hnd hk

/-- The full consecutive-label descent formula for every finite matching. The
right side refers to the actual partners, and the left side to the actual output
of paired insertion. -/
theorem MatchingWord.descent {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {k p q : ℕ} (hp : Partners w k p) (hq : Partners w (k + 1) q) :
    RowDescends k (k + 1) (pairInsertList w) ↔ q < p ∧ p ≠ k + 1 := by
  induction w using List.reverseRecOn generalizing k p q with
  | nil => simp [Partners] at hp
  | append_singleton w edge ih =>
    obtain ⟨a, b⟩ := edge
    have hw0 : MatchingWord w := hw.prefix
    have hab : a < b := hw.lower_lt_upper (a, b) (by simp)
    have hfresh := hw.last_fresh
    have hcontent : ∀ x, x ∈ (pairInsertList w).flatten ↔ x ∈ endpointWord w := by
      intro x
      simpa only [List.flatten_nil, List.append_nil] using (flatten_pairInsertList_perm w []).mem_iff (a := x)
    have ha : a ∉ (pairInsertList w).flatten := by
      intro h
      exact hfresh.1 ((hcontent a).mp h)
    have hb : b ∉ (pairInsertList w).flatten := by
      intro h
      exact hfresh.2 ((hcontent b).mp h)
    rw [pairInsertList_append_singleton]
    rcases (partners_append w [(a, b)] k p).mp hp with hpold | hpnew
    · rcases (partners_append w [(a, b)] (k + 1) q).mp hq with hqold | hqnew
      · have hx := (hcontent k).mpr hpold.mem_left
        have hy := (hcontent (k + 1)).mpr hqold.mem_left
        exact (rowDescends_pairInsert_old_iff hw0.isTableauRows hw0.output_distinct
          ha hb hab.ne hx hy).trans (ih hw0 hpold hqold)
      · rcases (partners_singleton (a, b) (k + 1) q).mp hqnew with hqnew | hqnew
        · obtain ⟨hka, hqb⟩ := hqnew
          dsimp only [Prod.fst, Prod.snd] at hka hqb
          subst a
          subst q
          have hx := (hcontent k).mpr hpold.mem_left
          have hn := not_rowDescends_pairInsert_new_right hw0.output_distinct ha hb hab.ne hx
          have hpb : p < b := hw.before_last p hpold.mem_right
          constructor
          · intro hd
            exact False.elim (hn hd)
          · intro h
            exact False.elim ((not_lt_of_ge hpb.le) h.1)
        · obtain ⟨hkb, hqa⟩ := hqnew
          dsimp only [Prod.fst, Prod.snd] at hkb hqa
          subst b
          subst q
          have hmax : ∀ z ∈ endpointWord w, z ≤ k := by
            intro z hz
            have := hw.before_last z hz
            omega
          obtain ⟨v, rfl⟩ := hw0.eq_append_of_max hpold hmax
          have hv : MatchingWord v := hw0.prefix
          have hvcontent : ∀ x, x ∈ (pairInsertList v).flatten ↔ x ∈ endpointWord v := by
            intro x
            simpa only [List.flatten_nil, List.append_nil] using (flatten_pairInsertList_perm v []).mem_iff (a := x)
          have hpv : p ∉ (pairInsertList v).flatten := by
            intro h
            exact hw0.last_fresh.1 ((hvcontent p).mp h)
          have hav : a ∉ (pairInsertList v).flatten := by
            intro h
            apply hfresh.1
            rw [endpointWord_append]
            exact List.mem_append_left _ ((hvcontent a).mp h)
          have hpa : p ≠ a := by
            intro h
            apply hfresh.1
            exact h ▸ hpold.mem_right
          have hpk : p < k := hw0.lower_lt_upper (p, k) (by simp)
          have hak : a < k := by
            have hane : a ≠ k := by
              intro h
              exact hfresh.1 (h.symm ▸ hpold.mem_left)
            omega
          have hvmax : ∀ z ∈ (pairInsertList v).flatten, z < k := by
            intro z hz
            exact hw0.before_last z ((hvcontent z).mp hz)
          rw [pairInsertList_append_singleton]
          have hiff := rowDescends_pairInsert_two_largest hv.isTableauRows hv.output_distinct
            hpv hav hpa hpk hak (Nat.lt_succ_self k) hvmax
          have hpne : p ≠ k + 1 := by omega
          rw [show (p ≠ k + 1) = True from propext (iff_true_intro hpne), and_true]
          exact hiff
    · rcases (partners_append w [(a, b)] (k + 1) q).mp hq with hqold | hqnew
      · rcases (partners_singleton (a, b) k p).mp hpnew with hpnew | hpnew
        · obtain ⟨hka, hpb⟩ := hpnew
          dsimp only [Prod.fst, Prod.snd] at hka hpb
          subst a
          subst p
          have hy := (hcontent (k + 1)).mpr hqold.mem_left
          have hd := rowDescends_pairInsert_new_left hw0.isTableauRows hw0.output_distinct
            ha hb hab.ne hy
          have hqb : q < b := hw.before_last q hqold.mem_right
          have hbk : b ≠ k + 1 := by
            intro h
            exact hfresh.2 (h.symm ▸ hqold.mem_left)
          exact iff_of_true hd ⟨hqb, hbk⟩
        · obtain ⟨hkb, hpa⟩ := hpnew
          have hlt := hw.before_last (k + 1) hqold.mem_left
          omega
      · have hpn := (partners_singleton (a, b) k p).mp hpnew
        have hqn := (partners_singleton (a, b) (k + 1) q).mp hqnew
        have heq : a = k ∧ b = k + 1 ∧ p = k + 1 ∧ q = k := by
          rcases hpn with hpn | hpn <;> rcases hqn with hqn | hqn <;> omega
        obtain ⟨haeq, hbeq, hpeq, hqeq⟩ := heq
        subst a
        subst b
        subst p
        subst q
        have hindex : rowInsertIndex k (pairInsertList w) = 0 := by
          apply rowInsertIndex_of_forall_le
          intro z hz
          have hz' : z ∈ (pairInsertList w).flatten := by
            cases he : pairInsertList w with
            | nil => simpa [he] using hz
            | cons row rows => exact List.mem_append_left _ (by simpa [he] using hz)
          have := hw.before_last z ((hcontent z).mp hz')
          omega
        have hn := not_rowDescends_pairInsert_of_index_zero hw0.output_distinct
          ha hb hab.ne hindex (x := k)
        simp [hn]

end FourPapers.Symmetric

end

/- SOURCE COMPONENT MatchingPartners -/

/-! The partner relation of a finite matching and transport by label permutations. -/
namespace FourPapers.Symmetric

/-- Conjugation of the actual matching relation by a bijection of labels.
The words remain in their canonical increasing-upper-endpoint order. -/
def ConjugatesPartners (f : ℕ ≃ ℕ) (w v : List (ℕ × ℕ)) : Prop :=
  ∀ x y, Partners v (f x) (f y) ↔ Partners w x y

theorem mem_endpointWord_iff_exists_partner (w : List (ℕ × ℕ)) (x : ℕ) :
    x ∈ endpointWord w ↔ ∃ y, Partners w x y := by
  constructor
  · intro hx
    obtain ⟨p,hp,rfl | rfl⟩ := mem_endpointWord.mp hx
    · exact ⟨p.2,Or.inl hp⟩
    · exact ⟨p.1,Or.inr hp⟩
  · rintro ⟨y,h⟩
    exact h.mem_left

theorem ConjugatesPartners.endpoint {f : ℕ ≃ ℕ} {w v : List (ℕ × ℕ)}
    (h : ConjugatesPartners f w v) (x : ℕ) :
    f x ∈ endpointWord v ↔ x ∈ endpointWord w := by
  rw [mem_endpointWord_iff_exists_partner,mem_endpointWord_iff_exists_partner]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨f.symm y,(h x (f.symm y)).mp (by simpa using hy)⟩
  · rintro ⟨y,hy⟩
    exact ⟨f y,(h x y).mpr hy⟩

theorem conjugatesPartners_refl (w : List (ℕ × ℕ)) :
    ConjugatesPartners (Equiv.refl _) w w := by
  intro x y
  rfl

theorem partners_perm {w v : List (ℕ × ℕ)} (h : w.Perm v) (x y : ℕ) :
    Partners w x y ↔ Partners v x y := by
  simp only [Partners,h.mem_iff]

theorem ConjugatesPartners.of_perm {f : ℕ ≃ ℕ} {w v u : List (ℕ × ℕ)}
    (h : ConjugatesPartners f w v) (hperm : u.Perm v) :
    ConjugatesPartners f w u := by
  intro x y
  exact (partners_perm hperm (f x) (f y)).trans (h x y)

theorem MatchingWord.edge_eq_of_common_endpoint {w : List (ℕ × ℕ)}
    (hw : MatchingWord w) {p q : ℕ × ℕ} (hp : p ∈ w) (hq : q ∈ w)
    {x : ℕ} (hxp : x = p.1 ∨ x = p.2) (hxq : x = q.1 ∨ x = q.2) : p = q := by
  by_contra hpq
  have hn : (w.flatMap (fun p => [p.1,p.2])).Nodup := hw.distinct
  have hd := (List.nodup_flatMap.mp hn).2
  letI : Std.Symm (fun p q : ℕ × ℕ => List.Disjoint [p.1,p.2] [q.1,q.2]) :=
    ⟨fun _ _ h => h.symm⟩
  have hdis : List.Disjoint [p.1,p.2] [q.1,q.2] := hd.forall hp hq hpq
  exact (List.disjoint_left.mp hdis) (by simpa using hxp) (by simpa using hxq)

theorem MatchingWord.partner_unique {w : List (ℕ × ℕ)}
    (hw : MatchingWord w) {x y z : ℕ} (hy : Partners w x y) (hz : Partners w x z) :
    y = z := by
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact congrArg Prod.snd (hw.edge_eq_of_common_endpoint hy hz (Or.inl rfl) (Or.inl rfl))
  · have heq := hw.edge_eq_of_common_endpoint hy hz (Or.inl rfl) (Or.inr rfl)
    have h₁ := congrArg Prod.fst heq
    have h₂ := congrArg Prod.snd heq
    exact h₂.trans h₁
  · have heq := hw.edge_eq_of_common_endpoint hy hz (Or.inr rfl) (Or.inl rfl)
    have h₁ := congrArg Prod.fst heq
    have h₂ := congrArg Prod.snd heq
    exact h₁.trans h₂
  · exact congrArg Prod.fst (hw.edge_eq_of_common_endpoint hy hz (Or.inr rfl) (Or.inr rfl))

theorem MatchingWord.partner_ne {w : List (ℕ × ℕ)}
    (hw : MatchingWord w) {x y : ℕ} (h : Partners w x y) : x ≠ y := by
  intro hxy
  subst y
  rcases h with h | h
  all_goals exact (lt_irrefl x) (hw.lower_lt_upper _ h)


end FourPapers.Symmetric

/- SOURCE COMPONENT MatchingYoungGeometry -/

/- Two pure diagram lemmas recovered from the algebraic checkpoint. Names are
qualified to avoid duplicating the original declarations when the algebra bridge
is imported. The statements and proof bodies are unchanged. -/
namespace YoungDiagram
@[simp]
theorem matching_rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact notMem_bot (i, 0) (mem_iff_lt_rowLen.mpr hpos)

@[simp]
theorem matching_getD_rowLens (μ : YoungDiagram) (i : ℕ) :
    μ.rowLens[i]?.getD 0 = μ.rowLen i := by
  rw [← List.getD_eq_getElem?_getD]
  by_cases hi : i < μ.rowLens.length
  · rw [List.getD_eq_getElem _ _ hi, get_rowLens]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    symm
    apply Nat.eq_zero_of_not_pos
    intro hpos
    apply hi
    rw [length_rowLens, ← mem_iff_lt_colLen, mem_iff_lt_rowLen]
    exact hpos

end YoungDiagram

/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.Diagram -/
section
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting the cells of a Young diagram by rows

Mathlib's `YoungDiagram.rowLens` records the lengths of the rows of a Young diagram.  This file
counts the cells of a diagram row by row: the first `k` row lengths sum to the number of cells
lying in the first `k` rows, whether those lengths are summed as
`∑ i ∈ Finset.range k, μ.rowLen i` or as `(μ.rowLens.take k).sum`.  Read as a multiset, the row
lengths are the lengths of the rows `i < μ.colLen 0` (`YoungDiagram.coe_rowLens`), so sums and
counts over them are sums and counts over rows (`YoungDiagram.sum_map_coe_rowLens`,
`YoungDiagram.card_filter_coe_rowLens`).  Since
the rows exhaust the cells, the row lengths also determine the diagram
(`YoungDiagram.rowLen_injective`).  Cutting the same count column by column,
`YoungDiagram.card_filter_fst_lt_filter_snd_eq` counts the cells of the first `k` rows
lying in a fixed column; summing that count over the columns gives the counting core
`YoungDiagram.card_filter_le_sum_take_rowLens`, which bounds the elements of row less than `k` in
a finite type labelled by a row and injected into the cells, no two of them sharing both a row and
a column, by the cells of the first `k` rows.  The same row-by-row reading applies to any property
of the cells, not only to counting them all: `YoungDiagram.card_filter_cells` counts the cells
satisfying a predicate one row at a time, and `YoungDiagram.prod_cells_eq_prod_range` reads a
product over the cells the same way.

The partial sums are the shape of every dominance statement about partitions, since dominance
compares partial sums of decreasingly sorted parts, and the sorted parts of a partition are the
row lengths of its Young diagram.

Reading the rows also describes containment: one diagram is contained in another exactly when
each of its rows is shorter (`YoungDiagram.le_iff_forall_rowLen_le`), from which a diagram
has only finitely many sub-diagrams (`YoungDiagram.finite_Iic`).  Columns are monotone in
containment as well (`YoungDiagram.colLen_le_of_le`).

The file closes with the two degenerate shapes, at the bottom and at the top of the dominance
order.  A diagram with at most one column has its cells described one row at a time by
`YoungDiagram.mem_iff_of_rowLen_le_one` and counted by
`YoungDiagram.card_eq_colLen_of_rowLen_le_one`; a diagram with at most one row is described
by `YoungDiagram.mem_iff_of_colLen_le_one` and counted by
`YoungDiagram.card_eq_rowLen_of_colLen_le_one`.

Finally, `YoungDiagram.cellContent` is the *content* `j - i` of the cell `(i, j)`, its column index
minus its row index; transposition negates it (`YoungDiagram.cellContent_swap`).
-/

section
namespace YoungDiagram

theorem sum_list_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A row past the last one of a Young diagram is empty. -/
theorem rowLen_eq_zero_of_colLen_le {μ : YoungDiagram} {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  exact absurd (_root_.YoungDiagram.mem_iff_lt_colLen.mp
    (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))) (Nat.not_lt.mpr hi)

/-- The row of a cell is one of the rows of the diagram. -/
theorem lt_colLen_zero_of_mem {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ) :
    i < μ.colLen 0 :=
  _root_.YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) h)

/- YoungDiagram.matching_rowLen_bot is supplied above. -/

/-- The empty Young diagram has no cells, so every column of it is empty. -/
@[simp]
theorem colLen_bot (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 :=
  Nat.eq_zero_of_not_pos fun h =>
    _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)

/-- A Young diagram is determined by its row lengths. -/
theorem rowLen_injective : Function.Injective _root_.YoungDiagram.rowLen := by
  intro μ ν h
  apply _root_.YoungDiagram.ext
  apply Finset.ext
  intro c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells,
    _root_.YoungDiagram.mem_iff_lt_rowLen, _root_.YoungDiagram.mem_iff_lt_rowLen, congrFun h i]

/- YoungDiagram.matching_getD_rowLens is supplied above. -/

/-- Merge-sorting the row lengths of a Young diagram recovers them: they are already
decreasing. This is stated for `List.mergeSort` in the shape `simp` produces from
`Multiset.sort` on a coerced list (via `Multiset.coe_sort` and `ge_iff_le`), making it the
`simp` normal form for sorted row-length expressions; the public statement is
`TauCeti.YoungDiagram.sort_coe_rowLens`. -/
@[simp]
theorem mergeSort_rowLens (μ : YoungDiagram) :
    μ.rowLens.mergeSort (fun a b => decide (b ≤ a)) = μ.rowLens :=
  List.mergeSort_eq_self _ μ.rowLens_sorted.pairwise

/-- Sorting the row lengths of a Young diagram, as a multiset, recovers the row lengths: they
are already decreasing. -/
theorem sort_coe_rowLens (μ : YoungDiagram) :
    (↑μ.rowLens : Multiset ℕ).sort (· ≥ ·) = μ.rowLens := by
  rw [Multiset.coe_sort]
  exact mergeSort_rowLens μ

/-- The row lengths of a Young diagram, as a multiset, are the lengths of the rows above the
end of its first column. -/
theorem coe_rowLens (μ : YoungDiagram) :
    (μ.rowLens : Multiset ℕ) = (Finset.range (μ.colLen 0)).val.map μ.rowLen := by
  rw [rowLens, ← Multiset.map_coe, Finset.range_val, Multiset.coe_range]

/-- A sum over the row lengths of a Young diagram, as a multiset, is a sum over its rows. -/
theorem sum_map_coe_rowLens {M : Type*} [AddCommMonoid M] (μ : YoungDiagram) (g : ℕ → M) :
    ((μ.rowLens : Multiset ℕ).map g).sum = ∑ i ∈ Finset.range (μ.colLen 0), g (μ.rowLen i) := by
  rw [coe_rowLens, Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def]

/-- The row lengths of a Young diagram satisfying a predicate are counted by the rows whose
length satisfies it. -/
theorem card_filter_coe_rowLens (μ : YoungDiagram) (p : ℕ → Prop) [DecidablePred p] :
    ((μ.rowLens : Multiset ℕ).filter p).card =
      ((Finset.range (μ.colLen 0)).filter fun i => p (μ.rowLen i)).card := by
  rw [coe_rowLens, Multiset.filter_map, Multiset.card_map, ← Finset.filter_val, Finset.card_val]
  rfl

/-- The first `k` row lengths of a Young diagram count its cells in the first `k` rows. -/
theorem sum_range_rowLen_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    ∑ i ∈ Finset.range k, μ.rowLen i = (μ.cells.filter fun c => c.1 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => c.1 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => c.1 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, μ.rowLen i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [μ.rowLen_eq_card]
      congr 1
      ext c
      have hik : i < k := Finset.mem_range.mp hi
      simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells,
        _root_.YoungDiagram.mem_row_iff]
      aesop

/-- The cells of a Young diagram, counted over any range of rows that contains all of them.  This
is `YoungDiagram.sum_rowLens_eq_card` with the range of summation chosen by hand instead of being
the exact number of rows `μ.colLen 0`. -/
theorem card_eq_sum_range_rowLen (μ : _root_.YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    μ.card = ∑ i ∈ Finset.range N, μ.rowLen i := by
  rw [sum_range_rowLen_eq_card_filter_fst]
  refine (congrArg Finset.card (Finset.filter_true_of_mem fun c hc => ?_)).symm
  exact lt_of_lt_of_le ((_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
    (μ.colLen_anti 0 c.snd c.snd.zero_le)) hN

/-- **The cells of a Young diagram carrying a given property, counted row by row.**  The range of
summation is any range of rows containing all of them, as in
`YoungDiagram.card_eq_sum_range_rowLen`; a row past the last one contributes nothing, being
empty. -/
theorem card_filter_cells (μ : _root_.YoungDiagram) (p : ℕ × ℕ → Prop) [DecidablePred p] {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    (μ.cells.filter p).card
      = ∑ i ∈ Finset.range N, ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).card := by
  have hcells : μ.cells.filter p
      = (Finset.range N).biUnion fun i =>
          ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).image fun j => (i, j) := by
    ext c
    obtain ⟨i, j⟩ := c
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      _root_.YoungDiagram.mem_cells, Prod.mk.injEq]
    constructor
    · rintro ⟨hij, hp⟩
      refine ⟨i, lt_of_lt_of_le (lt_of_lt_of_le (_root_.YoungDiagram.mem_iff_lt_colLen.mp hij)
        (μ.colLen_anti 0 j j.zero_le)) hN, j, ⟨?_, hp⟩, rfl, rfl⟩
      exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp hij
    · rintro ⟨i', -, j', ⟨hj', hp⟩, rfl, rfl⟩
      exact ⟨_root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj', hp⟩
  rw [hcells, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ =>
      Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
  · intro y _ z _ hyz
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    rintro c ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact hyz (congrArg Prod.fst hj').symm

/-- **A product over the cells of a Young diagram, read row by row.**  The cells are fibred over
their row index by `Prod.fst`, and the fibre of `i` is the row `YoungDiagram.row μ i`, which is
`{i} ×ˢ Finset.range (μ.rowLen i)`.  The range of rows is any range containing all of them, as in
`YoungDiagram.card_eq_sum_range_rowLen`; a row past the last one contributes an empty product. -/
theorem prod_cells_eq_prod_range {M : Type*} [CommMonoid M] (μ : _root_.YoungDiagram) {N : ℕ}
    (hN : μ.colLen 0 ≤ N) (f : ℕ × ℕ → M) :
    ∏ c ∈ μ.cells, f c = ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range (μ.rowLen i), f (i, j) := by
  have hmaps : ∀ c ∈ μ.cells, c.1 ∈ Finset.range N := by
    rintro ⟨a, b⟩ hc
    exact Finset.mem_range.mpr ((_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
      ((μ.colLen_anti 0 b b.zero_le).trans hN))
  rw [← Finset.prod_fiberwise_of_maps_to hmaps f]
  refine Finset.prod_congr rfl fun i _ => ?_
  -- the fibre of `i` is `YoungDiagram.row`, defined as exactly this filter
  rw [← _root_.YoungDiagram.row, _root_.YoungDiagram.row_eq_prod, Finset.prod_product,
    Finset.prod_singleton]

/-- The first `k` entries of `YoungDiagram.rowLens` count the cells in the first `k` rows.  This
is `YoungDiagram.sum_range_rowLen_eq_card_filter_fst` with the truncation taken on the
list of row lengths, the form in which partial sums enter the dominance order on partitions. -/
theorem sum_take_rowLens_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.take k).sum = (μ.cells.filter fun c => c.1 < k).card := by
  rw [_root_.YoungDiagram.rowLens, ← List.map_take, List.take_range, sum_list_range,
    ← sum_range_rowLen_eq_card_filter_fst]
  have hsub : Finset.range (min k (μ.colLen 0)) ⊆ Finset.range k := fun i hi =>
    Finset.mem_range.mpr (lt_min_iff.mp (Finset.mem_range.mp hi)).1
  refine Finset.sum_subset hsub fun i hi hi' => ?_
  exact rowLen_eq_zero_of_colLen_le
    (by simpa [lt_min_iff, Finset.mem_range.mp hi] using Finset.mem_range.not.mp hi')

/-- The cells of a Young diagram lying in a fixed column and in one of the first `k` rows are the
top `min k (colLen j)` cells of that column. -/
theorem card_filter_fst_lt_filter_snd_eq (lam : YoungDiagram) (k j : ℕ) :
    (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j).card
      = min k (lam.colLen j) := by
  have himg : (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j)
      = (Finset.range (min k (lam.colLen j))).image fun i => (i, j) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, lt_min_iff,
      _root_.YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨hc, hk⟩, hj⟩
      refine ⟨c.1, ⟨hk, ?_⟩, ?_⟩
      · exact _root_.YoungDiagram.mem_iff_lt_colLen.mp (hj ▸ hc)
      · rw [← hj]
    · rintro ⟨i, ⟨hik, hicol⟩, rfl⟩
      exact ⟨⟨_root_.YoungDiagram.mem_iff_lt_colLen.mpr hicol, hik⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h, Finset.card_range]

/-- **The counting core of the dominance lemma.** Let the elements of a finite type `α` be
labelled by a *row* `r a : ℕ` and placed in the cells of a Young diagram `lam` by an injection
`f`, in such a way that the row of an element together with the column of its cell determines
the element.  Then the elements of row less than `k` are no more numerous than the cells of `lam`
in its first `k` rows.

The hypothesis `hcol` is the condition that elements sharing a row occupy pairwise distinct
columns; it is what bounds by `k` the number of elements landing in any one column. -/
theorem card_filter_le_sum_take_rowLens {α : Type*} [Fintype α] (lam : YoungDiagram)
    (r : α → ℕ) (f : α → ℕ × ℕ) (hmem : ∀ a, f a ∈ lam.cells) (hinj : Function.Injective f)
    (hcol : ∀ a b, r a = r b → (f a).2 = (f b).2 → a = b) (k : ℕ) :
    (Finset.univ.filter fun a => r a < k).card ≤ (lam.rowLens.take k).sum := by
  classical
  rw [sum_take_rowLens_eq_card_filter_fst]
  -- Every column index in sight is smaller than the length of the top row.
  have hlt : ∀ c ∈ lam.cells, c.2 ∈ Finset.range (lam.rowLen 0) := by
    intro c hc
    refine Finset.mem_range.mpr (lt_of_lt_of_le ?_ (lam.rowLen_anti 0 c.1 c.1.zero_le))
    exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp ((_root_.YoungDiagram.mem_cells c).mp hc)
  -- Split both sides into their columns.
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => (f a).2)
      (t := Finset.range (lam.rowLen 0)) fun a _ => hlt _ (hmem a),
    Finset.card_eq_sum_card_fiberwise (f := fun c : ℕ × ℕ => c.2)
      (t := Finset.range (lam.rowLen 0)) fun c hc =>
      hlt c (Finset.mem_filter.mp hc).1]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [card_filter_fst_lt_filter_snd_eq lam k j]
  have hfib : ∀ a ∈ ((Finset.univ.filter fun a => r a < k).filter fun a => (f a).2 = j : Finset α),
      r a < k ∧ (f a).2 = j := by
    intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  -- In a fixed column, the elements are separated by their rows, and they fit in the column.
  refine le_min (le_of_le_of_eq ?_ (Finset.card_range k))
    (le_of_le_of_eq ?_ lam.colLen_eq_card.symm)
  · refine Finset.card_le_card_of_injOn r (fun a ha => ?_) fun a ha b hb hab => ?_
    · exact Finset.mem_range.mpr (hfib a ha).1
    · exact hcol a b hab (((hfib a ha).2).trans (hfib b hb).2.symm)
  · refine Finset.card_le_card_of_injOn f (fun a ha => ?_) hinj.injOn
    exact _root_.YoungDiagram.mem_col_iff.mpr
      ⟨(_root_.YoungDiagram.mem_cells _).mp (hmem a), (hfib a ha).2⟩

/-- A row of a sub-diagram is no longer than the corresponding row. -/
theorem rowLen_le_of_le {μ ν : YoungDiagram} (h : ν ≤ μ) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i := by
  rcases Nat.eq_zero_or_pos (ν.rowLen i) with h0 | h0
  · omega
  · have hmem : ((i, ν.rowLen i - 1) : ℕ × ℕ) ∈ ν :=
      _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h hmem)
    omega

/-- A Young diagram is contained in another as soon as each of its rows is shorter. -/
theorem le_of_forall_rowLen_le {μ ν : YoungDiagram} (h : ∀ i, ν.rowLen i ≤ μ.rowLen i) : ν ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (h i))

/-- Containment of Young diagrams is containment of rows. -/
theorem le_iff_forall_rowLen_le {μ ν : YoungDiagram} : ν ≤ μ ↔ ∀ i, ν.rowLen i ≤ μ.rowLen i :=
  ⟨fun h => rowLen_le_of_le h, le_of_forall_rowLen_le⟩

/-- A column of a sub-diagram is no longer than the corresponding column. -/
theorem colLen_le_of_le {μ ν : YoungDiagram} (h : ν ≤ μ) (j : ℕ) : ν.colLen j ≤ μ.colLen j := by
  rw [← _root_.YoungDiagram.rowLen_transpose, ← _root_.YoungDiagram.rowLen_transpose]
  exact rowLen_le_of_le (_root_.YoungDiagram.transpose_mono h) j

/-- A row of a Young diagram is at least as long as any initial segment of cells it contains. -/
theorem le_rowLen_of_forall_mem {ν : YoungDiagram} {i k : ℕ}
    (h : ∀ j < k, ((i, j) : ℕ × ℕ) ∈ ν) : k ≤ ν.rowLen i := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h (k - 1) (by omega))
    omega

/-- A Young diagram has finitely many sub-diagrams, each being determined by its set of cells. -/
theorem finite_Iic (μ : YoungDiagram) : (Set.Iic μ).Finite := by
  have hinj : Set.InjOn _root_.YoungDiagram.cells (Set.Iic μ) :=
    fun _ _ _ _ h => _root_.YoungDiagram.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (μ.cells.powerset : Finset (Finset (ℕ × ℕ))).finite_toSet ?_
  rintro s ⟨ξ, hξ, rfl⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun c hc => Set.mem_Iic.mp hξ hc)

/-- **The cells of a Young diagram with at most one column.**  Every row is then either empty or
the single cell in column `0`, so a cell is a cell of the first column, and the diagram reaches
exactly as far down as that column does. -/
theorem mem_iff_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) {i j : ℕ} :
    (i, j) ∈ μ ↔ i < μ.colLen 0 ∧ j = 0 := by
  grind [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_iff_lt_colLen,
    _root_.YoungDiagram.mem_iff_lt_rowLen, μ.rowLen_anti 0 i (Nat.zero_le _)]

/-- The cells of a Young diagram with at most one column are exactly the cells `(i, 0)` with
`i < μ.colLen 0`: the whole of its first column, and nothing else. -/
theorem cells_eq_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    μ.cells = Finset.range (μ.colLen 0) ×ˢ {0} := by
  ext ⟨i, j⟩
  simp [_root_.YoungDiagram.mem_cells, mem_iff_of_rowLen_le_one h, eq_comm]

/-- A Young diagram with at most one column has one cell in each of its `μ.colLen 0` rows. -/
theorem card_eq_colLen_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    μ.card = μ.colLen 0 := by
  simp [_root_.YoungDiagram.card, cells_eq_of_rowLen_le_one h]

/-- **The cells of a Young diagram with at most one row.**  Every column is then either empty or
the single cell in row `0`, so a cell is a cell of the first row, and the diagram reaches exactly
as far right as that row does. -/
theorem mem_iff_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) {i j : ℕ} :
    (i, j) ∈ μ ↔ i = 0 ∧ j < μ.rowLen 0 := by
  grind [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_iff_lt_colLen,
    _root_.YoungDiagram.mem_iff_lt_rowLen, μ.colLen_anti 0 j (Nat.zero_le _)]

/-- The cells of a Young diagram with at most one row are exactly the cells `(0, j)` with
`j < μ.rowLen 0`: the whole of its first row, and nothing else. -/
theorem cells_eq_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.cells = {0} ×ˢ Finset.range (μ.rowLen 0) := by
  ext ⟨i, j⟩
  simp [_root_.YoungDiagram.mem_cells, mem_iff_of_colLen_le_one h, eq_comm, and_comm]

/-- A Young diagram with at most one row has one cell in each of its `μ.rowLen 0` columns. -/
theorem card_eq_rowLen_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.card = μ.rowLen 0 := by
  simp [_root_.YoungDiagram.card, cells_eq_of_colLen_le_one h]

/-- The **content** of the cell `(i, j)`: its column index minus its row index, `j - i`. -/
def cellContent (c : ℕ × ℕ) : ℤ := c.2 - c.1

theorem cellContent_def (c : ℕ × ℕ) : cellContent c = c.2 - c.1 := (rfl)

@[simp]
theorem cellContent_mk (i j : ℕ) : cellContent (i, j) = j - i := (rfl)

@[simp]
theorem cellContent_swap (c : ℕ × ℕ) : cellContent c.swap = -cellContent c := by
  simp [cellContent_def]

end YoungDiagram


end

/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.Corner -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Corners of a Young diagram

A *corner* of a Young diagram `μ` is a cell of `μ` with neither the cell to its right nor the cell
below it in `μ`.  Equivalently, the corners are the maximal cells of `μ`
(`YoungDiagram.IsCorner.eq_of_le`): they are exactly the cells `c` for which removing `c`
alone leaves a set of cells that is still a Young diagram.  So they index the ways of building `μ`
one cell at a time, and hence the recursions that count standard Young tableaux.  The corners are
also exactly the cells of hook length `1`, which is
`YoungDiagram.isCorner_iff_hookLength_eq_one` in
`TauCeti.Combinatorics.Young.HookLength.Basic`, downstream of this file.

Deletion is `YoungDiagram.erase`.  It is defined without any hypothesis on the cell — it
removes the whole principal upper set of `c`, that is `c` together with every cell weakly below and
to the right of it — so that it can be summed over the corners of `μ` with no dependent index.  At a
corner, and only at a cell of `μ` that is a corner, nothing but `c` itself is removed
(`YoungDiagram.IsCorner.cells_erase`), and at a cell outside `μ` nothing is removed at all.

## Main definitions

* `YoungDiagram.IsCorner`: the predicate cutting out the corners of a diagram.
* `YoungDiagram.corners`: the corners of a diagram, as a `Finset`.
* `YoungDiagram.erase`: the diagram with the principal upper set of a cell removed.

## Main results

* `YoungDiagram.IsCorner.cells_erase`: erasing a corner deletes exactly that cell, and
  `YoungDiagram.IsCorner.card_erase`: it drops the number of cells by one.
* `YoungDiagram.exists_isCorner`: a nonempty Young diagram has a corner, so the corner
  recursions are not vacuous.
* `YoungDiagram.IsCorner.eq_of_fst_eq`: the corners of a diagram sit in distinct rows, and
  `YoungDiagram.IsCorner.fst_lt_colLen_zero`: those rows are rows of the diagram.
* `YoungDiagram.corners_transpose` and `YoungDiagram.erase_transpose`: corners and
  deletion commute with transposition.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10, where the corner recursion for
  standard Young tableaux is the starting point of the hook-length formula.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose `hookLengthFormula` milestone is proved by induction along the corners of `μ`.
-/

section
namespace YoungDiagram

variable {μ : YoungDiagram} {c d : ℕ × ℕ} {i j : ℕ}

/-! ### Corners -/

/-- A **corner** of a Young diagram: a cell of `μ` with neither the cell to its right nor the cell
below it in `μ`.  These are exactly the maximal cells of `μ`
(`YoungDiagram.IsCorner.eq_of_le`), equivalently the cells whose removal on its own leaves a
set of cells that is still a Young diagram. -/
def IsCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ

/-- The defining conjunction of `YoungDiagram.IsCorner`, for introducing and eliminating the
predicate. -/
theorem isCorner_def (μ : YoungDiagram) (c : ℕ × ℕ) :
    IsCorner μ c ↔ c ∈ μ ∧ (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ :=
  Iff.rfl

instance instDecidableIsCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Decidable (IsCorner μ c) :=
  decidable_of_iff _ (isCorner_def μ c).symm

namespace IsCorner

theorem mem (h : IsCorner μ c) : c ∈ μ := h.1

theorem right_notMem (h : IsCorner μ c) : (c.1, c.2 + 1) ∉ μ := h.2.1

theorem below_notMem (h : IsCorner μ c) : (c.1 + 1, c.2) ∉ μ := h.2.2

/-- A corner is a maximal cell: the only cell of `μ` weakly below and to the right of a corner is
the corner itself. -/
theorem eq_of_le (h : IsCorner μ c) (hd : d ∈ μ) (hcd : c ≤ d) : d = c := by
  obtain ⟨hc1, hc2⟩ := hcd
  have h1 : c.1 = d.1 := by
    refine le_antisymm hc1 (le_of_not_gt fun hlt => h.below_notMem ?_)
    exact μ.up_left_mem hlt hc2 hd
  have h2 : c.2 = d.2 := by
    refine le_antisymm hc2 (le_of_not_gt fun hlt => h.right_notMem ?_)
    exact μ.up_left_mem hc1 hlt hd
  exact Prod.ext h1.symm h2.symm

theorem le_iff (h : IsCorner μ c) (hd : d ∈ μ) : c ≤ d ↔ d = c :=
  ⟨h.eq_of_le hd, fun hdc => hdc ▸ le_rfl⟩

end IsCorner

/-- The corners of a Young diagram, as a finite set of cells. -/
def corners (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.filter (IsCorner μ)

@[simp]
theorem mem_corners : c ∈ corners μ ↔ IsCorner μ c := by
  simp only [corners, Finset.mem_filter, _root_.YoungDiagram.mem_cells, and_iff_right_iff_imp]
  exact fun h => h.mem

theorem corners_subset_cells (μ : YoungDiagram) : corners μ ⊆ μ.cells :=
  Finset.filter_subset _ _

/-- **A nonempty Young diagram has a corner**: a cell maximizing `i + j` has neither the cell to its
right nor the cell below it in the diagram. -/
theorem exists_isCorner (hμ : 0 < μ.card) : ∃ c, IsCorner μ c := by
  obtain ⟨c, hc, hmax⟩ :=
    μ.cells.exists_max_image (fun d => d.1 + d.2) (Finset.card_pos.mp hμ)
  refine ⟨c, hc, fun hmem => ?_, fun hmem => ?_⟩
  · have h := hmax _ hmem
    omega
  · have h := hmax _ hmem
    omega

theorem corners_nonempty (hμ : 0 < μ.card) : (corners μ).Nonempty := by
  obtain ⟨c, hc⟩ := exists_isCorner hμ
  exact ⟨c, mem_corners.mpr hc⟩

/-! ### Deleting a corner -/

/-- The Young diagram obtained from `μ` by deleting the cell `c` together with every cell weakly
below and to the right of it.

The definition is total, so that it can be summed over the corners of `μ` without a dependent index.
It is `Finset.erase` on cells exactly at a corner (`YoungDiagram.IsCorner.cells_erase`), and
it leaves `μ` unchanged at a cell outside `μ`
(`YoungDiagram.erase_eq_self_of_notMem`); at a cell of `μ` that is not a corner it deletes
the entire principal upper set of `c` in `μ`, which is the price of totality. -/
def erase (μ : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram where
  cells := μ.cells.filter fun d => ¬ c ≤ d
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨μ.isLowerSet hba (Finset.mem_coe.mpr ha.1), fun hc => ha.2 (hc.trans hba)⟩

@[simp]
theorem mem_erase : d ∈ erase μ c ↔ d ∈ μ ∧ ¬ c ≤ d :=
  Finset.mem_filter

theorem mem_of_mem_erase (h : d ∈ erase μ c) : d ∈ μ :=
  (mem_erase.mp h).1

theorem erase_le (μ : YoungDiagram) (c : ℕ × ℕ) : erase μ c ≤ μ :=
  Finset.filter_subset _ _

@[simp]
theorem erase_eq_self_of_notMem (h : c ∉ μ) : erase μ c = μ := by
  apply _root_.YoungDiagram.ext
  apply Finset.ext
  intro d
  change d ∈ erase μ c ↔ d ∈ μ
  refine ⟨fun hd => mem_of_mem_erase hd, fun hd => mem_erase.mpr ⟨hd, fun hcd => h ?_⟩⟩
  exact μ.isLowerSet hcd hd

namespace IsCorner

theorem mem_erase_iff (h : IsCorner μ c) : d ∈ erase μ c ↔ d ∈ μ ∧ d ≠ c := by
  rw [YoungDiagram.mem_erase]
  exact and_congr_right fun hd => not_congr (h.le_iff hd)

@[simp]
theorem cells_erase (h : IsCorner μ c) : (erase μ c).cells = μ.cells.erase c := by
  ext d
  simp only [Finset.mem_erase, _root_.YoungDiagram.mem_cells, h.mem_erase_iff]
  tauto

theorem notMem_erase (h : IsCorner μ c) : c ∉ erase μ c := fun hc =>
  (h.mem_erase_iff.mp hc).2 rfl

/-- Erasing a corner drops the number of cells by exactly one. -/
@[simp]
theorem card_erase (h : IsCorner μ c) : (erase μ c).card + 1 = μ.card := by
  rw [YoungDiagram.card, h.cells_erase, Finset.card_erase_of_mem h.mem]
  exact Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨c, h.mem⟩)

theorem card_pos (h : IsCorner μ c) : 0 < μ.card :=
  Finset.card_pos.mpr ⟨c, h.mem⟩

/-! ### Rows and columns after erasure -/

/-- Erasing a corner erases that cell from every row finset. Only its own row contains it. -/
@[simp]
theorem row_erase (h : IsCorner μ c) : (erase μ c).row i = (μ.row i).erase c := by
  ext d
  simp only [mem_row_iff, h.mem_erase_iff, Finset.mem_erase]
  tauto

/-- Erasing a corner erases that cell from every column finset. Only its own column contains it. -/
@[simp]
theorem col_erase (h : IsCorner μ c) : (erase μ c).col j = (μ.col j).erase c := by
  ext d
  simp only [mem_col_iff, h.mem_erase_iff, Finset.mem_erase]
  tauto

/-- Erasing a corner shortens its row by one and leaves every other row unchanged. -/
@[simp]
theorem rowLen_erase (h : IsCorner μ c) :
    (erase μ c).rowLen i = if c.1 = i then μ.rowLen i - 1 else μ.rowLen i := by
  rw [(erase μ c).rowLen_eq_card, h.row_erase, Finset.card_erase_eq_ite,
    μ.rowLen_eq_card]
  simp only [mem_row_iff, h.mem, true_and]

/-- Erasing a corner shortens its column by one and leaves every other column unchanged. -/
@[simp]
theorem colLen_erase (h : IsCorner μ c) :
    (erase μ c).colLen j = if c.2 = j then μ.colLen j - 1 else μ.colLen j := by
  rw [(erase μ c).colLen_eq_card, h.col_erase, Finset.card_erase_eq_ite,
    μ.colLen_eq_card]
  simp only [mem_col_iff, h.mem, true_and]

/-- A corner is the final cell of its row. -/
theorem rowLen_eq_snd_add_one (h : IsCorner μ c) : μ.rowLen c.1 = c.2 + 1 := by
  have hmem := _root_.YoungDiagram.mem_iff_lt_rowLen.mp h.mem
  have hright := h.right_notMem
  rw [_root_.YoungDiagram.mem_iff_lt_rowLen] at hright
  omega

/-- A corner is the final cell of its column. -/
theorem colLen_eq_fst_add_one (h : IsCorner μ c) : μ.colLen c.2 = c.1 + 1 := by
  have hmem := _root_.YoungDiagram.mem_iff_lt_colLen.mp h.mem
  have hbelow := h.below_notMem
  rw [_root_.YoungDiagram.mem_iff_lt_colLen] at hbelow
  omega

/-- A corner is the final cell of its row, so it is determined by the row it lies in: the corners
of a diagram sit in distinct rows. -/
theorem eq_of_fst_eq (hc : IsCorner μ c) (hd : IsCorner μ d) (h : c.1 = d.1) : c = d := by
  have hcr := hc.rowLen_eq_snd_add_one
  have hdr := hd.rowLen_eq_snd_add_one
  rw [h] at hcr
  exact Prod.ext h (by omega)

/-- The row of a corner is one of the rows of the diagram. -/
theorem fst_lt_colLen_zero (h : IsCorner μ c) : c.1 < μ.colLen 0 :=
  _root_.YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le c.2) h.mem)

end IsCorner

/-! ### Transposition -/

@[simp]
theorem isCorner_transpose : IsCorner μ.transpose c ↔ IsCorner μ c.swap := by
  simp only [isCorner_def, _root_.YoungDiagram.mem_transpose, Prod.swap_prod_mk, Prod.fst_swap,
    Prod.snd_swap]
  tauto

@[simp]
theorem corners_transpose (μ : YoungDiagram) :
    corners μ.transpose = (corners μ).image Prod.swap := by
  ext ⟨i, j⟩
  simp [corners, isCorner_transpose]

@[simp]
theorem erase_transpose (μ : YoungDiagram) (c : ℕ × ℕ) :
    erase μ.transpose c = (erase μ c.swap).transpose := by
  refine SetLike.ext fun d => ?_
  rw [mem_erase, _root_.YoungDiagram.mem_transpose, _root_.YoungDiagram.mem_transpose, mem_erase]
  exact and_congr_right fun _ =>
    not_congr ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

end YoungDiagram

end
end

/- EXACT SOURCE FourPapers.Symmetric.DualCornerGeometry -/
section

set_option autoImplicit false

/-!
# Corner geometry for elementary dual-equivalence connectivity

The argument is uniform in the shape. After removing two different corners of a
Young diagram, a remaining removable corner lies between them in bottom-to-top
row-reading order. This supplies the three largest labels in the induction that
connects different largest-label corner fibers.
-/

namespace FourPapers.Symmetric

/-- Bottom-to-top, and left-to-right within each row, as used in ordinary
row-reading words and elementary dual equivalence. -/
def RowReadBefore (c d : ℕ × ℕ) : Prop :=
  d.1 < c.1 ∨ c.1 = d.1 ∧ c.2 < d.2

 theorem rowReadBefore_irrefl (c : ℕ × ℕ) : ¬RowReadBefore c c := by
  simp [RowReadBefore]

 theorem rowReadBefore_trans {a b c : ℕ × ℕ}
    (hab : RowReadBefore a b) (hbc : RowReadBefore b c) : RowReadBefore a c := by
  rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
  · exact Or.inl (hbc.trans hab)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨hab.trans hbc, hab'.trans hbc'⟩

 theorem exists_corner_above {μ : YoungDiagram} {z : ℕ × ℕ} (hz : z ∈ μ) :
    ∃ e, z ≤ e ∧ YoungDiagram.IsCorner μ e := by
  classical
  let S := μ.cells.filter (fun e => z ≤ e)
  have hS : S.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨hz, le_rfl⟩⟩
  obtain ⟨e, he, hmax⟩ := S.exists_max_image (fun d => d.1 + d.2) hS
  have he' := Finset.mem_filter.mp he
  refine ⟨e, he'.2, he'.1, ?_, ?_⟩
  · intro hr
    have hrS : (e.1, e.2 + 1) ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨hr, he'.2.1, he'.2.2.trans (Nat.le_succ _)⟩
    have := hmax _ hrS
    omega
  · intro hb
    have hbS : (e.1 + 1, e.2) ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨hb, he'.2.1.trans (Nat.le_succ _), he'.2.2⟩
    have := hmax _ hbS
    omega

 theorem corner_survives_erase {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hc : YoungDiagram.IsCorner μ c) (hd : YoungDiagram.IsCorner μ d) (hdc : d ≠ c) :
    YoungDiagram.IsCorner (YoungDiagram.erase μ c) d := by
  exact ⟨hc.mem_erase_iff.mpr ⟨hd.mem, hdc⟩,
    fun h => hd.right_notMem (YoungDiagram.mem_of_mem_erase h),
    fun h => hd.below_notMem (YoungDiagram.mem_of_mem_erase h)⟩

 theorem corner_col_reverse_of_row_lt {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hc : YoungDiagram.IsCorner μ c) (hd : YoungDiagram.IsCorner μ d) (hrow : c.1 < d.1) :
    d.2 < c.2 := by
  apply lt_of_not_ge
  intro hcol
  have heq := hc.eq_of_le hd.mem ⟨hrow.le, hcol⟩
  have := congrArg Prod.fst heq
  omega

/-- The removable-corner witness needed to join any two different corner fibers.
No bound is imposed on the size, height, or width of the Young diagram. -/
theorem exists_corner_between {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hc : YoungDiagram.IsCorner μ c) (hd : YoungDiagram.IsCorner μ d) (hrow : c.1 < d.1) :
    ∃ e, YoungDiagram.IsCorner (YoungDiagram.erase (YoungDiagram.erase μ c) d) e ∧
      RowReadBefore d e ∧ RowReadBefore e c := by
  have hcol : d.2 < c.2 := corner_col_reverse_of_row_lt hc hd hrow
  have hdc : d ≠ c := by intro h; have := congrArg Prod.fst h; omega
  have hd' := corner_survives_erase hc hd hdc
  let z : ℕ × ℕ := (d.1 - 1, d.2)
  have hzmem : z ∈ μ := μ.up_left_mem (Nat.sub_le _ _) le_rfl hd.mem
  have hzc : z ≠ c := by intro h; have := congrArg Prod.snd h; dsimp [z] at this; omega
  have hzd : z ≠ d := by intro h; have := congrArg Prod.fst h; dsimp [z] at this; omega
  have hz : z ∈ YoungDiagram.erase (YoungDiagram.erase μ c) d :=
    hd'.mem_erase_iff.mpr ⟨hc.mem_erase_iff.mpr ⟨hzmem, hzc⟩, hzd⟩
  obtain ⟨e, hze, he⟩ := exists_corner_above hz
  have hemem : e ∈ μ := YoungDiagram.mem_of_mem_erase
    (YoungDiagram.mem_of_mem_erase he.mem)
  have hed : e ≠ d := (hd'.mem_erase_iff.mp he.mem).2
  have hec : e ≠ c := (hc.mem_erase_iff.mp
    (YoungDiagram.mem_of_mem_erase he.mem)).2
  have herow : e.1 < d.1 := by
    apply lt_of_not_ge
    intro h
    exact hed (hd.eq_of_le hemem ⟨h, hze.2⟩)
  have hlow : c.1 ≤ e.1 := by have := hze.1; dsimp [z] at this; omega
  refine ⟨e, he, Or.inl herow, ?_⟩
  rcases hlow.eq_or_lt with heq | hlt
  · refine Or.inr ⟨heq.symm, ?_⟩
    apply lt_of_not_ge
    intro h
    exact hec (hc.eq_of_le hemem ⟨heq.le, h⟩)
  · exact Or.inl hlt

end FourPapers.Symmetric

end

end -- closing MatchingYoungGeometry source-file anonymous section

/- SOURCE COMPONENT MatchingStandardTableaux -/

/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.Tableau -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- The pigeonhole principle for the labels of a column.

/-!
# Young tableaux

A `μ`-tableau is a bijective filling `t : ↥μ.cells ≃ Fin μ.card` of the cells of a Young diagram
`μ` by the labels `Fin μ.card`.  This file defines `YoungTableau`, the row and the column of a
label, and identifies the labels lying in a given row, respectively column, with the cells of that
row, respectively column, of `μ`; counting those labels recovers the row lengths of `μ`
(`YoungTableau.card_filter_rowIndex_eq`) and their partial sums
(`YoungTableau.card_filter_rowIndex_lt`), and the column lengths
(`YoungTableau.card_filter_colIndex_eq`). The latter gives the pigeonhole lemma
`YoungTableau.exists_ne_and_apply_eq_of_lt_colLen`: a filling by fewer values than the length of a
column repeats a value on that column. On top of that it proves the counting lemma
`YoungTableau.colIndex_lt_rowLen_of_injective`: if the row of a label together with the column of
its image under a permutation `u` of the labels determine the label, then that pair of indices is
again a cell of `μ`.  A second counting lemma,
`YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt`, bounds a filling of the labels that is
injective on columns: it takes small values no more often than the row index does, the row filling
`YoungTableau.rowFilling` being the extreme case.  It also defines `YoungTableau.relabel`, the
transitive action of the permutations of the labels on the tableaux of a fixed shape, which is how
two tableaux of the same shape are compared.

Note that `YoungTableau μ` is an abbreviation, so that the whole `Equiv` API applies to a tableau
directly.  As a consequence dot notation on a tableau resolves in the `Equiv` namespace, and the
declarations below are to be spelled out, as in `YoungTableau.rowIndex t`.

A `μ`-tableau is not required to be row- or column-increasing.  The strictly row- and
column-increasing ones are `TauCeti.StandardYoungTableau`, whose `toTableau` field is a `μ`-tableau
in the present sense; Mathlib's `SemistandardYoungTableau` is a different notion again, a filling
of `μ` by natural numbers that is weakly increasing along each row and strictly increasing down
each column (represented as a function `ℕ → ℕ → ℕ` vanishing outside `μ`), with no bijectivity
requirement.  The three notions are kept distinct.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 0.
-/

section
namespace TauCeti

/-- A `μ`-tableau: a bijective filling of the cells of the Young diagram `μ` by the labels
`Fin μ.card`. -/
abbrev YoungTableau (μ : YoungDiagram) : Type := ↥μ.cells ≃ Fin μ.card

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The row of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def rowIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

/-- The column of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def colIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

/-- The row of a label is the first coordinate of the cell carrying it.  This is not a `simp`
lemma: `rowIndex` is the normal form, and `rowIndex_apply` computes it on a label presented as
the value of `t`. -/
theorem rowIndex_def (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex t k = (t.symm k : ℕ × ℕ).1 := by
  rw [rowIndex]

/-- The column of a label is the second coordinate of the cell carrying it.  As for
`rowIndex_def`, this is not a `simp` lemma. -/
theorem colIndex_def (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex t k = (t.symm k : ℕ × ℕ).2 := by
  rw [colIndex]

@[simp]
theorem rowIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    rowIndex t (t c) = (c : ℕ × ℕ).1 := by
  rw [rowIndex_def, Equiv.symm_apply_apply]

@[simp]
theorem colIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    colIndex t (t c) = (c : ℕ × ℕ).2 := by
  rw [colIndex_def, Equiv.symm_apply_apply]

/-- A cell of a Young diagram is determined by its row together with its column, so a label of a
tableau is determined by its row and its column. -/
theorem rowIndex_colIndex_injective (t : YoungTableau μ) :
    Function.Injective fun k => (rowIndex t k, colIndex t k) := by
  intro k l h
  simp only [rowIndex_def, colIndex_def, Prod.mk.injEq] at h
  exact t.symm.injective (Subtype.ext (Prod.ext h.1 h.2))

/-- The labels lying in row `i` of a `μ`-tableau are the cells of the `i`-th row of `μ`. -/
def rowFiberEquiv (t : YoungTableau μ) (i : ℕ) :
    {k : Fin μ.card // rowIndex t k = i} ≃ ↥(μ.row i) :=
  -- the two predicates are given explicitly: inferring them from `Iff.rfl` would state the source
  -- subtype through the unfolding of `rowIndex` rather than through `rowIndex` itself
  (Equiv.subtypeEquiv (p := fun k => rowIndex t k = i) (q := fun c : ↥μ.cells => (↑c : ℕ × ℕ).1 = i)
      t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.1 = i).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]

/-- The labels lying in column `j` of a `μ`-tableau are the cells of the `j`-th column of `μ`. -/
def colFiberEquiv (t : YoungTableau μ) (j : ℕ) :
    {k : Fin μ.card // colIndex t k = j} ≃ ↥(μ.col j) :=
  -- as for `rowFiberEquiv`, the two predicates are given explicitly
  (Equiv.subtypeEquiv (p := fun k => colIndex t k = j) (q := fun c : ↥μ.cells => (↑c : ℕ × ℕ).2 = j)
      t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.2 = j).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_col_iff, YoungDiagram.mem_cells]

-- This and `colFiberEquiv_apply_coe` are the defining equations of the two fiber equivalences: in
-- each chain only the leading `Equiv.subtypeEquiv` moves the underlying cell, by applying `t.symm`,
-- while `Equiv.subtypeSubtypeEquivSubtypeInter` and `Equiv.subtypeEquivRight` change only the
-- predicate, so the two sides differ by subtype coercions alone and hold by `rfl`.  The definitions
-- are deliberately not `@[expose]`d, so the pre-bump `simp [rowFiberEquiv]` has nothing to unfold;
-- the parentheses in `(rfl)` keep the definitional step inside this module, leaving these lemmas
-- and the `_symm_apply_coe` pair below as the whole interface for importers.
@[simp]
theorem rowFiberEquiv_apply_coe (t : YoungTableau μ) (i : ℕ)
    (k : {k : Fin μ.card // rowIndex t k = i}) :
    (rowFiberEquiv t i k : ℕ × ℕ) = (t.symm k.1 : ℕ × ℕ) := (rfl)

@[simp]
theorem colFiberEquiv_apply_coe (t : YoungTableau μ) (j : ℕ)
    (k : {k : Fin μ.card // colIndex t k = j}) :
    (colFiberEquiv t j k : ℕ × ℕ) = (t.symm k.1 : ℕ × ℕ) := (rfl)

/-- The label attached to a cell of row `i` is the label of that cell in the tableau. -/
@[simp]
theorem rowFiberEquiv_symm_apply_coe (t : YoungTableau μ) (i : ℕ) (c : ↥(μ.row i)) :
    ((rowFiberEquiv t i).symm c : Fin μ.card) =
      t ⟨(c : ℕ × ℕ), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_row_iff.mp c.2).1⟩ := by
  apply t.symm.injective
  rw [Equiv.symm_apply_apply]
  refine Subtype.ext ?_
  rw [← rowFiberEquiv_apply_coe, Equiv.apply_symm_apply]

/-- The label attached to a cell of column `j` is the label of that cell in the tableau. -/
@[simp]
theorem colFiberEquiv_symm_apply_coe (t : YoungTableau μ) (j : ℕ) (c : ↥(μ.col j)) :
    ((colFiberEquiv t j).symm c : Fin μ.card) =
      t ⟨(c : ℕ × ℕ), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_col_iff.mp c.2).1⟩ := by
  apply t.symm.injective
  rw [Equiv.symm_apply_apply]
  refine Subtype.ext ?_
  rw [← colFiberEquiv_apply_coe, Equiv.apply_symm_apply]

/-! ## Cells and labels -/

/-- The row and the column of a label are the coordinates of a cell of `μ`. -/
theorem rowIndex_colIndex_mem (t : YoungTableau μ) (x : Fin μ.card) :
    (rowIndex t x, colIndex t x) ∈ μ := by
  rw [rowIndex_def, colIndex_def]
  simp

/-- A label lies in a column strictly to the left of the end of its row. -/
theorem colIndex_lt_rowLen (t : YoungTableau μ) (x : Fin μ.card) :
    colIndex t x < μ.rowLen (rowIndex t x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (rowIndex_colIndex_mem t x)

/-- **The row of a label is below the number of rows.** The label lies in its own column, which is
no longer than the zeroth one. -/
theorem rowIndex_lt_colLen_zero (t : YoungTableau μ) (x : Fin μ.card) :
    rowIndex t x < μ.colLen 0 :=
  (YoungDiagram.mem_iff_lt_colLen.mp (rowIndex_colIndex_mem t x)).trans_le
    (μ.colLen_anti 0 _ (Nat.zero_le _))

/-- Every cell of `μ` carries a label. -/
theorem exists_rowIndex_colIndex (t : YoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    ∃ x, rowIndex t x = i ∧ colIndex t x = j :=
  ⟨t ⟨(i, j), (YoungDiagram.mem_cells _).mpr h⟩, by simp, by simp⟩

/-- Row `i` of a `μ`-tableau carries `μ.rowLen i` labels. -/
theorem card_filter_rowIndex_eq (t : YoungTableau μ) (i : ℕ) :
    (Finset.univ.filter fun y => rowIndex t y = i).card = μ.rowLen i := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rowFiberEquiv t i), Fintype.card_coe]
  exact (YoungDiagram.rowLen_eq_card μ).symm

/-- Column `j` of a `μ`-tableau carries `μ.colLen j` labels. -/
theorem card_filter_colIndex_eq (t : YoungTableau μ) (j : ℕ) :
    (Finset.univ.filter fun y => colIndex t y = j).card = μ.colLen j := by
  rw [← Fintype.card_subtype, Fintype.card_congr (colFiberEquiv t j), Fintype.card_coe]
  exact (YoungDiagram.colLen_eq_card μ).symm

/-- A filling with fewer values than the length of column `j` repeats a value on that column:
two distinct labels of the column have the same image. -/
theorem exists_ne_and_apply_eq_of_lt_colLen (t : YoungTableau μ) {α : Type*} [Fintype α]
    {j : ℕ} (hn : Fintype.card α < μ.colLen j) (p : Fin μ.card → α) :
    ∃ a b : Fin μ.card, colIndex t a = j ∧ colIndex t b = j ∧ a ≠ b ∧ p a = p b := by
  classical
  have hcard : Fintype.card {ℓ : Fin μ.card // colIndex t ℓ = j} = μ.colLen j := by
    rw [Fintype.card_subtype]
    exact card_filter_colIndex_eq t j
  obtain ⟨a, b, hab, hpab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun ℓ : {ℓ : Fin μ.card // colIndex t ℓ = j} => p ℓ)
      (by rw [hcard]; exact hn)
  exact ⟨a, b, a.2, b.2, fun h => hab (Subtype.ext h), hpab⟩

/-- The labels of a tableau lying in one of its first `k` rows are as many as the cells of the
shape in its first `k` rows. -/
theorem card_filter_rowIndex_lt (t : YoungTableau μ) (k : ℕ) :
    (Finset.univ.filter fun x => rowIndex t x < k).card = (μ.rowLens.take k).sum := by
  classical
  rw [YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  refine Finset.card_bij (fun x _ => ((t.symm x : ↥μ.cells) : ℕ × ℕ)) (fun x hx => ?_)
    (fun x _ y _ h => t.symm.injective (Subtype.ext h)) fun c hc => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, rowIndex_def] at hx
    exact Finset.mem_filter.mpr ⟨(t.symm x).2, hx⟩
  · rw [Finset.mem_filter] at hc
    refine ⟨t ⟨c, hc.1⟩, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, rowIndex_apply] using hc.2
    · rw [Equiv.symm_apply_apply]

/-! ## The counting lemma -/

/-- **Row `i` meets the first `k` columns in exactly `min (μ.rowLen i) k` labels.** -/
theorem card_filter_colIndex_lt_and_rowIndex_eq (t : YoungTableau μ) (i k : ℕ) :
    (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card
      = min (μ.rowLen i) k := by
  have hinj : Set.InjOn (colIndex t)
      ↑(Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact rowIndex_colIndex_injective t (Prod.ext (ha.2.trans hb.2.symm) hab)
  have himg : (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).image
      (colIndex t) = (Finset.range (μ.rowLen i)).filter fun j => j < k := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy2 ▸ colIndex_lt_rowLen t y, hy1⟩
    · rintro ⟨hj1, hj2⟩
      obtain ⟨y, hy1, hy2⟩ :=
        exists_rowIndex_colIndex t (YoungDiagram.mem_iff_lt_rowLen.mpr hj1)
      exact ⟨y, ⟨hy2 ▸ hj2, hy1⟩, hy2⟩
  have hrange : ((Finset.range (μ.rowLen i)).filter fun j => j < k)
      = Finset.range (min (μ.rowLen i) k) := by
    ext j
    simp
  rw [← Finset.card_image_of_injOn hinj, himg, hrange, Finset.card_range]

/-- **Row `i` meets the first `k` columns of the `u`-image in at most `min (μ.rowLen i) k`
labels**, when the row of a label together with the column of its `u`-image determines the label.
Only injectivity of that pairing is used, so `u` need not be a permutation. -/
theorem card_filter_colIndex_comp_lt_and_rowIndex_eq_le (t : YoungTableau μ)
    {u : Fin μ.card → Fin μ.card}
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (i k : ℕ) :
    (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
      ≤ min (μ.rowLen i) k := by
  refine le_min ?_ ?_
  · rw [← card_filter_rowIndex_eq t i]
    refine Finset.card_le_card fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  · have hinj : Set.InjOn (fun y => colIndex t (u y))
        ↑(Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hu (Prod.ext (ha.2.trans hb.2.symm) hab)
    calc (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
        = ((Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).image
            fun y => colIndex t (u y)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range k).card := by
            refine Finset.card_le_card fun j hj => ?_
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            obtain ⟨y, ⟨hy1, _⟩, rfl⟩ := hj
            exact Finset.mem_range.mpr hy1
      _ = k := Finset.card_range k

/-- **Summed over the rows, the labels whose `u`-image lies in the first `k` columns number
`∑ᵢ min (μ.rowLen i) k`.** No injectivity hypothesis is needed. -/
theorem sum_card_filter_colIndex_comp_lt_and_rowIndex_eq (t : YoungTableau μ)
    (u : Equiv.Perm (Fin μ.card)) (k : ℕ) :
    ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
        (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ, min (μ.rowLen i) k := by
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ Finset.image (rowIndex t) Finset.univ :=
    fun y => Finset.mem_image_of_mem _ (Finset.mem_univ y)
  have h1 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
          (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t)
      (t := Finset.image (rowIndex t) Finset.univ) fun y _ => hmemS y]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
  have h2 : (Finset.univ.filter fun y => colIndex t y < k).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
          (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t)
      (t := Finset.image (rowIndex t) Finset.univ) fun y _ => hmemS y]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
  have h3 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
      = (Finset.univ.filter fun y => colIndex t y < k).card :=
    Finset.card_equiv u fun i => by simp
  rw [← h1, h3, h2]
  exact Finset.sum_congr rfl fun i _ => card_filter_colIndex_lt_and_rowIndex_eq t i k

/-- **The counting lemma for rows and columns along a permutation.**  If the row of a label
together with the column of its `u`-image determine the label, then that pair is again a cell of
`μ`.

Both halves of the count are over the rows of `μ`: the labels whose `u`-image lies in one of the
first `k` columns number `∑ᵢ min (μ.rowLen i) k`, while row `i` can contribute at most
`min (μ.rowLen i) k` of them.  Upper bounds that add up to the total are equalities, and the case
`k = μ.rowLen i` of the resulting equality is the statement. -/
theorem colIndex_lt_rowLen_of_injective (t : YoungTableau μ) (u : Equiv.Perm (Fin μ.card))
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (x : Fin μ.card) :
    colIndex t (u x) < μ.rowLen (rowIndex t x) := by
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ Finset.image (rowIndex t) Finset.univ :=
    fun y => Finset.mem_image_of_mem _ (Finset.mem_univ y)
  -- The row-wise upper bounds add up to the total, so each is an equality.
  have hi := (Finset.sum_eq_sum_iff_of_le fun i _ =>
      card_filter_colIndex_comp_lt_and_rowIndex_eq_le t hu i (μ.rowLen (rowIndex t x))).mp
    (sum_card_filter_colIndex_comp_lt_and_rowIndex_eq t u (μ.rowLen (rowIndex t x)))
    (rowIndex t x) (hmemS x)
  rw [min_self] at hi
  -- a subset of the row with the same cardinality is the whole row
  have hsub : (Finset.univ.filter fun y =>
        colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x)
      ⊆ Finset.univ.filter fun y => rowIndex t y = rowIndex t x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  have hEq := Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (by rw [card_filter_rowIndex_eq t (rowIndex t x), hi]))
  have hx : x ∈ Finset.univ.filter fun y =>
      colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x := by
    rw [hEq]
    simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.1

/-! ## Fillings injective on columns

A filling `p : Fin μ.card → ℕ` of the labels of a `μ`-tableau is *injective on columns* when the
value `p x` together with the column of `x` determines `x`.  The counting lemma
`TauCeti.YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt` is that such a filling takes
small values no more often than the row index does: for every `m`, at most as many labels satisfy
`p x < m` as satisfy `rowIndex t x < m`.  The row index is itself injective on columns
(`TauCeti.YoungTableau.rowIndex_colIndex_injective`), so the bound is sharp.

Reading the labels as the cells carrying them, the filling plays the role of a row function and
the tableau that of an injection into the cells, so the lemma is the counting core
`YoungDiagram.card_filter_le_sum_take_rowLens` with the right-hand side counted back by
`TauCeti.YoungTableau.card_filter_rowIndex_lt`.
-/

/-- **A filling injective on columns takes small values no more often than the row index does.**
For every `m`, at most as many labels of a `μ`-tableau satisfy `p x < m` as lie in one of the
first `m` rows.

As `m` varies, this gives the dominance bound on the content of such a filling: the content is
dominated by the sequence of row lengths of `μ`, which is the content of the row index itself. -/
theorem card_filter_lt_le_card_filter_rowIndex_lt (t : YoungTableau μ) {p : Fin μ.card → ℕ}
    (hp : Function.Injective fun x => (p x, colIndex t x)) (m : ℕ) :
    (Finset.univ.filter fun x => p x < m).card ≤
      (Finset.univ.filter fun x => rowIndex t x < m).card := by
  rw [card_filter_rowIndex_lt]
  refine YoungDiagram.card_filter_le_sum_take_rowLens μ p
    (fun x => ((t.symm x : ↥μ.cells) : ℕ × ℕ)) (fun x => (t.symm x).2)
    (fun x y hxy => t.symm.injective (Subtype.ext hxy)) (fun x y hv hc => ?_) m
  exact hp (Prod.ext hv (by simpa only [colIndex_def] using hc))

/-! ## The row filling -/

variable {n : ℕ}

/-- **The row filling** of a `μ`-tableau whose shape has at most `n` rows: the row index of a
label, read as an element of `Fin n`.  It is injective on the columns of `t`
(`TauCeti.YoungTableau.rowIndex_colIndex_injective`), and the extreme case of the counting lemma
above: its content is the sequence of row lengths of `μ`. -/
def rowFilling (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) (x : Fin μ.card) : Fin n :=
  ⟨rowIndex t x, (rowIndex_lt_colLen_zero t x).trans_le hn⟩

@[simp]
theorem val_rowFilling (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) (x : Fin μ.card) :
    (rowFilling t hn x : ℕ) = rowIndex t x :=
  (rfl)

@[simp]
theorem rowFilling_eq_iff (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) (x : Fin μ.card)
    (j : Fin n) : rowFilling t hn x = j ↔ rowIndex t x = (j : ℕ) := by
  rw [Fin.ext_iff, val_rowFilling]

/-! ## Relabeling -/

/-- The tableau `t` with its labels permuted by `σ`: the cell that `t` labels `k` is labelled
`σ k` by `relabel σ t`.

Relabeling is the left action of `Equiv.Perm (Fin μ.card)` on `YoungTableau μ` recorded by
`relabel_one` and `relabel_relabel`, and it is transitive by `exists_relabel_eq`.  It is not
registered as a `MulAction` instance because `YoungTableau μ` is an abbreviation for a type of
equivalences, so such an instance would fire on equivalences at large, far outside the tableaux
it is meant for. -/
def relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) : YoungTableau μ :=
  t.trans σ

@[simp]
theorem relabel_apply (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (c : ↥μ.cells) :
    relabel σ t c = σ (t c) :=
  (rfl)

@[simp]
theorem relabel_symm_apply (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    (relabel σ t).symm k = t.symm (σ⁻¹ k) := by
  rw [relabel, Equiv.symm_trans_apply, Equiv.Perm.inv_def]

/-- Relabeling by `σ` moves the label `k` to the row that `t` gives to `σ⁻¹ k`. -/
@[simp]
theorem rowIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex (relabel σ t) k = rowIndex t (σ⁻¹ k) := by
  rw [rowIndex_def, rowIndex_def, relabel_symm_apply]

/-- Relabeling by `σ` moves the label `k` to the column that `t` gives to `σ⁻¹ k`. -/
@[simp]
theorem colIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex (relabel σ t) k = colIndex t (σ⁻¹ k) := by
  rw [colIndex_def, colIndex_def, relabel_symm_apply]

@[simp]
theorem relabel_one (t : YoungTableau μ) : relabel 1 t = t := by
  rw [relabel, Equiv.Perm.one_def, Equiv.trans_refl]

@[simp]
theorem relabel_relabel (σ τ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    relabel σ (relabel τ t) = relabel (σ * τ) t := by
  rw [relabel, relabel, relabel, Equiv.trans_assoc, Equiv.Perm.mul_def]

/-- The permutation of the labels carrying the tableau `t` to the tableau `t'` of the same
shape. -/
def relabelPerm (t t' : YoungTableau μ) : Equiv.Perm (Fin μ.card) :=
  t.symm.trans t'

/-- The permutation carrying `t` to `t'` sends the label `k` to the label that `t'` gives to the
cell that `t` labels `k`. -/
@[simp]
theorem relabelPerm_apply (t t' : YoungTableau μ) (k : Fin μ.card) :
    relabelPerm t t' k = t' (t.symm k) := by
  rw [relabelPerm, Equiv.trans_apply]

@[simp]
theorem relabel_relabelPerm (t t' : YoungTableau μ) : relabel (relabelPerm t t') t = t' := by
  rw [relabel, relabelPerm, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

/-- Any two tableaux of the same shape differ by a relabeling. -/
theorem exists_relabel_eq (t t' : YoungTableau μ) : ∃ σ, relabel σ t = t' :=
  ⟨relabelPerm t t', relabel_relabelPerm t t'⟩

/-- Every Young diagram carries a tableau: enumerating its cells is one.

This is a theorem rather than a `Nonempty` instance because `YoungTableau μ` is an abbreviation
for a type of equivalences, so an instance would fire on equivalences at large. -/
theorem nonempty (μ : YoungDiagram) : Nonempty (YoungTableau μ) :=
  ⟨μ.cells.equivFin⟩

end YoungTableau

end TauCeti

end
end

/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.StandardTableau.Basic -/
section
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Standard Young tableaux

A standard Young tableau of shape `μ` is a bijective labeling of the cells of `μ` by
`Fin μ.card` that increases strictly from left to right and from top to bottom. This file
defines standard Young tableaux, their finite cardinality `standardCount`, and transposition. Its
underlying labeling is the existing `YoungTableau μ` type, so the general tableau API applies
without converting between parallel representations.

The labels start at zero, following the `Fin μ.card` convention in the Schur--Weyl roadmap.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 0.
* Mathlib's `Mathlib.Combinatorics.Young.YoungDiagram`, for Young diagrams and their
  transposition.
-/

section
namespace TauCeti

/-- A standard Young tableau of shape `μ` is a bijective labeling of its cells by
`Fin μ.card`, strictly increasing along rows and columns. -/
structure StandardYoungTableau (μ : YoungDiagram) where
  /-- The underlying Young tableau. -/
  toTableau : YoungTableau μ
  /-- Labels increase strictly from left to right. -/
  row_strict' : ∀ {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ),
    toTableau ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < toTableau ⟨(i, j₂), hcell⟩
  /-- Labels increase strictly from top to bottom. -/
  col_strict' : ∀ {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ),
    toTableau ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < toTableau ⟨(i₂, j), hcell⟩

namespace StandardYoungTableau

instance instFunLike {μ : YoungDiagram} :
    FunLike (StandardYoungTableau μ) ↥μ.cells (Fin μ.card) where
  coe T := T.toTableau
  coe_injective T U h := by
    cases T with
    | mk e _ _ =>
      cases U with
      | mk e' _ _ =>
        congr
        exact Equiv.ext fun c => congrFun h c

/-- The underlying function of a standard Young tableau is its underlying tableau. -/
@[simp]
theorem coe_toTableau {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    ⇑T.toTableau = T :=
  rfl

/-- Evaluating the underlying tableau agrees with evaluating the standard tableau. -/
@[simp]
theorem toTableau_apply {μ : YoungDiagram} (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    T.toTableau c = T c :=
  rfl

/-- Two standard Young tableaux are equal when all of their entries agree. -/
@[ext]
theorem ext {μ : YoungDiagram} {T U : StandardYoungTableau μ} (h : ∀ c, T c = U c) : T = U :=
  DFunLike.ext T U h

/-- The entries of a standard Young tableau form a bijection. -/
theorem bijective {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    Function.Bijective T :=
  T.toTableau.bijective

/-- The entries of a standard Young tableau are injective. -/
theorem injective {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    Function.Injective T :=
  T.toTableau.injective

/-- Every label occurs in a standard Young tableau. -/
theorem surjective {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    Function.Surjective T :=
  T.toTableau.surjective

/-- Entries of a standard Young tableau increase strictly from left to right. -/
theorem row_strict {μ : YoungDiagram} (T : StandardYoungTableau μ)
    {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ) :
    T ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < T ⟨(i, j₂), hcell⟩ :=
  T.row_strict' h hcell

/-- Entries of a standard Young tableau increase strictly from top to bottom. -/
theorem col_strict {μ : YoungDiagram} (T : StandardYoungTableau μ)
    {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ) :
    T ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < T ⟨(i₂, j), hcell⟩ :=
  T.col_strict' h hcell

def transposeCellEquiv (μ : YoungDiagram) : ↥μ.transpose.cells ≃ ↥μ.cells :=
  (Equiv.prodComm ℕ ℕ).subtypeEquiv fun _ => YoungDiagram.mem_transpose

-- These are the two defining equations of `transposeCellEquiv`, in the shape
-- `@[simps apply symm_apply]` would generate: `Equiv.subtypeEquiv` applies `Equiv.prodComm` to the
-- underlying pair in each direction, so both sides differ only by the subtype coercion and hold by
-- `rfl`.  They are needed because Mathlib's own `Equiv.subtypeEquiv_apply` and
-- `Equiv.subtypeEquiv_symm` no longer fire on this equivalence: the subtype here is `↥μ.cells`, the
-- `Finset` coercion to a sort, which `simp` no longer sees through to `Subtype _` after the bump.
@[simp]
theorem transposeCellEquiv_apply (μ : YoungDiagram) (c : ↥μ.transpose.cells) :
    transposeCellEquiv μ c = ⟨c.1.swap, YoungDiagram.mem_transpose.mp c.2⟩ :=
  rfl

@[simp]
theorem transposeCellEquiv_symm_apply (μ : YoungDiagram) (c : ↥μ.cells) :
    (transposeCellEquiv μ).symm c =
      ⟨c.1.swap, YoungDiagram.mem_transpose.mpr c.2⟩ :=
  rfl

/-- Transpose a standard Young tableau by swapping its rows and columns while preserving its
labels. -/
def transpose {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    StandardYoungTableau μ.transpose where
  toTableau :=
    (transposeCellEquiv μ).trans
      (T.toTableau.trans (finCongr (YoungDiagram.card_transpose μ).symm))
  row_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv_apply, Prod.swap, finCongr,
      Equiv.coe_fn_mk, Fin.cast_lt_cast, toTableau_apply] using
      T.col_strict h (YoungDiagram.mem_transpose.mp hcell)
  col_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv_apply, Prod.swap, finCongr,
      Equiv.coe_fn_mk, Fin.cast_lt_cast, toTableau_apply] using
      T.row_strict h (YoungDiagram.mem_transpose.mp hcell)

/-- Transposition preserves the numeric label of each cell. -/
@[simp]
theorem transpose_apply_val {μ : YoungDiagram} (T : StandardYoungTableau μ)
    (c : ↥μ.transpose.cells) : (T.transpose c).val =
      (T ⟨c.1.swap, YoungDiagram.mem_transpose.mp c.2⟩).val :=
  calc
    (T.transpose c).val = (T.transpose.toTableau c).val :=
      congrArg Fin.val (toTableau_apply T.transpose c).symm
    _ = (T ⟨c.1.swap, YoungDiagram.mem_transpose.mp c.2⟩).val := by
      simp only [transpose, Equiv.trans_apply, transposeCellEquiv_apply,
        finCongr, Equiv.coe_fn_mk, Fin.val_cast, toTableau_apply]

def untranspose {μ : YoungDiagram} (T : StandardYoungTableau μ.transpose) :
    StandardYoungTableau μ where
  toTableau :=
    (transposeCellEquiv μ).symm.trans
      (T.toTableau.trans (finCongr (YoungDiagram.card_transpose μ)))
  row_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv_symm_apply, Prod.swap, finCongr,
      Equiv.coe_fn_mk, Fin.cast_lt_cast, toTableau_apply] using
      T.col_strict h (YoungDiagram.mem_transpose.mpr hcell)
  col_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv_symm_apply, Prod.swap, finCongr,
      Equiv.coe_fn_mk, Fin.cast_lt_cast, toTableau_apply] using
      T.row_strict h (YoungDiagram.mem_transpose.mpr hcell)

theorem untranspose_apply_val {μ : YoungDiagram}
    (T : StandardYoungTableau μ.transpose) (c : ↥μ.cells) : (untranspose T c).val =
      (T ⟨c.1.swap, YoungDiagram.mem_transpose.mpr c.2⟩).val :=
  calc
    (untranspose T c).val = ((untranspose T).toTableau c).val :=
      congrArg Fin.val (toTableau_apply (untranspose T) c).symm
    _ = (T ⟨c.1.swap, YoungDiagram.mem_transpose.mpr c.2⟩).val := by
      simp only [untranspose, Equiv.trans_apply, transposeCellEquiv_symm_apply,
        finCongr, Equiv.coe_fn_mk, Fin.val_cast, toTableau_apply]

/-- Transposition is an equivalence between standard Young tableaux of conjugate shapes. -/
def transposeEquiv (μ : YoungDiagram) :
    StandardYoungTableau μ ≃ StandardYoungTableau μ.transpose where
  toFun := transpose
  invFun := untranspose
  left_inv T := by
    apply DFunLike.ext
    intro c
    apply Fin.ext
    simp only [untranspose_apply_val, transpose_apply_val, Prod.swap_swap]
  right_inv T := by
    apply DFunLike.ext
    intro c
    apply Fin.ext
    simp only [transpose_apply_val, untranspose_apply_val, Prod.swap_swap]

/-- The forward map of `transposeEquiv` is tableau transposition. -/
@[simp]
theorem transposeEquiv_apply {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    transposeEquiv μ T = T.transpose :=
  by simp [transposeEquiv]

/-- The inverse transpose equivalence swaps cells while preserving their numeric labels. -/
@[simp]
theorem transposeEquiv_symm_apply_val {μ : YoungDiagram}
    (T : StandardYoungTableau μ.transpose) (c : ↥μ.cells) : (((transposeEquiv μ).symm T) c).val =
      (T ⟨c.1.swap, YoungDiagram.mem_transpose.mpr c.2⟩).val :=
  untranspose_apply_val T c

/-- Standard Young tableaux of a fixed shape form a finite type. -/
noncomputable instance instFintype (μ : YoungDiagram) :
    Fintype (StandardYoungTableau μ) :=
  FunLike.fintype (StandardYoungTableau μ)

end StandardYoungTableau

/-- The number of standard Young tableaux of shape `μ`. -/
noncomputable def standardCount (μ : YoungDiagram) : ℕ :=
  Fintype.card (StandardYoungTableau μ)

/-- The number of standard Young tableaux is the cardinality of their finite type. -/
theorem standardCount_def (μ : YoungDiagram) :
    standardCount μ = Fintype.card (StandardYoungTableau μ) :=
  by simp only [standardCount]

/-- Transposing a Young diagram does not change its number of standard Young tableaux. -/
@[simp]
theorem standardCount_transpose (μ : YoungDiagram) :
    standardCount μ.transpose = standardCount μ :=
  Fintype.card_congr (StandardYoungTableau.transposeEquiv μ).symm

end TauCeti

end
end

/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.StandardTableau.Corner -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The corner recursion for standard Young tableaux

The largest label of a standard Young tableau of shape `μ` sits at a corner of `μ`
(`TauCeti.StandardYoungTableau.isCorner_maxCell`), and deleting that cell leaves a standard Young
tableau of the smaller shape.  This is a bijection, and summing it over the corners gives the
**corner recursion**

`standardCount μ = ∑ c ∈ corners μ, standardCount (erase μ c)`

for a nonempty diagram `μ` (`TauCeti.standardCount_eq_sum_corners`).  It is the recursion the
hook-length formula is proved by, and the one that makes `standardCount` computable from the shape
alone.

The bijection is stated fibrewise, as an equivalence between the tableaux whose largest label sits
at a *given* corner `c` and the tableaux of shape `erase μ c`, so that no type in this file depends
on a tableau and no transport along an equality of shapes is needed; that is why
`TauCeti.StandardYoungTableau.restrict` takes the corner and the equation naming it as parameters
rather than reading them off its argument.

## Main definitions

* `TauCeti.StandardYoungTableau.maxCell`: the cell carrying the largest label.
* `TauCeti.StandardYoungTableau.restrict`: delete the corner carrying the largest label.
* `TauCeti.StandardYoungTableau.extend`: the inverse, labelling a corner with the largest label.
* `TauCeti.StandardYoungTableau.cornerFiberEquiv`: the two as an equivalence.

## Main results

* `TauCeti.StandardYoungTableau.isCorner_maxCell`: the largest label of a standard Young tableau
  sits at a corner.
* `TauCeti.standardCount_eq_sum_corners`: the corner recursion.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10, where the corner recursion opens
  the proof of the hook-length formula.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose `hookLengthFormula` milestone is the induction this recursion drives.
-/

section
namespace TauCeti

namespace StandardYoungTableau

variable {μ : YoungDiagram} {c : ℕ × ℕ}

/-! ### The cell carrying the largest label -/

/-- The cell of a standard Young tableau of a nonempty shape that carries the largest label,
`μ.card - 1`. -/
def maxCell (hμ : 0 < μ.card) (T : StandardYoungTableau μ) : ℕ × ℕ :=
  (T.toTableau.symm ⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩ : ↥μ.cells)

theorem maxCell_mem (hμ : 0 < μ.card) (T : StandardYoungTableau μ) : maxCell hμ T ∈ μ :=
  (T.toTableau.symm ⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩).2

/-- The label at `TauCeti.StandardYoungTableau.maxCell` is the largest one. -/
theorem apply_maxCell (hμ : 0 < μ.card) (T : StandardYoungTableau μ) :
    (T ⟨maxCell hμ T, maxCell_mem hμ T⟩).val + 1 = μ.card := by
  have h : T ⟨maxCell hμ T, maxCell_mem hμ T⟩ = ⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩ :=
    T.toTableau.apply_symm_apply _
  have hval : (⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩ : Fin μ.card).val = μ.card - 1 := rfl
  rw [h]
  omega

/-- **The largest label of a standard Young tableau sits at a corner.**  Neither the cell to its
right nor the cell below it can be in the diagram, since either would carry a strictly larger
label. -/
theorem isCorner_maxCell (hμ : 0 < μ.card) (T : StandardYoungTableau μ) :
    YoungDiagram.IsCorner μ (maxCell hμ T) := by
  have hmax := apply_maxCell hμ T
  refine (YoungDiagram.isCorner_def μ _).mpr ⟨maxCell_mem hμ T, fun hmem => ?_, fun hmem => ?_⟩
  · have hlt : (T ⟨maxCell hμ T, maxCell_mem hμ T⟩).val
        < (T ⟨((maxCell hμ T).1, (maxCell hμ T).2 + 1), hmem⟩).val :=
      T.row_strict (Nat.lt_succ_self _) hmem
    have := (T ⟨((maxCell hμ T).1, (maxCell hμ T).2 + 1), hmem⟩).isLt
    omega
  · have hlt : (T ⟨maxCell hμ T, maxCell_mem hμ T⟩).val
        < (T ⟨((maxCell hμ T).1 + 1, (maxCell hμ T).2), hmem⟩).val :=
      T.col_strict (Nat.lt_succ_self _) hmem
    have := (T ⟨((maxCell hμ T).1 + 1, (maxCell hμ T).2), hmem⟩).isLt
    omega

/-- A cell carries the largest label exactly when it is the cell
`TauCeti.StandardYoungTableau.maxCell`. -/
theorem maxCell_eq_iff (hμ : 0 < μ.card) (T : StandardYoungTableau μ) (hc : c ∈ μ) :
    maxCell hμ T = c ↔ (T ⟨c, hc⟩).val + 1 = μ.card := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact apply_maxCell hμ T
  · have hval : T ⟨c, hc⟩ = T ⟨maxCell hμ T, maxCell_mem hμ T⟩ :=
      Fin.ext (by have := apply_maxCell hμ T; omega)
    have hcm : c = maxCell hμ T := congrArg Subtype.val (T.injective hval)
    exact hcm.symm

/-! ### Deleting the corner carrying the largest label -/

theorem restrict_lt (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) (d : ↥(YoungDiagram.erase μ c).cells) :
    (T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val < (YoungDiagram.erase μ c).card := by
  have hd : d.1 ∈ μ := YoungDiagram.mem_of_mem_erase d.2
  have hcard := hc.card_erase
  have hlt := (T ⟨d.1, hd⟩).isLt
  rcases Nat.lt_or_ge (T ⟨d.1, hd⟩).val (YoungDiagram.erase μ c).card with h | h
  · exact h
  · have hval : T ⟨d.1, hd⟩ = T ⟨c, hc.mem⟩ := Fin.ext (by omega)
    have hdc : d.1 = c := congrArg Subtype.val (T.injective hval)
    exact absurd hdc (hc.mem_erase_iff.mp d.2).2

def restrictFun (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) :
    ↥(YoungDiagram.erase μ c).cells → Fin (YoungDiagram.erase μ c).card :=
  fun d => ⟨(T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val, restrict_lt hc T hT d⟩

theorem restrictFun_bijective (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau μ) (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) :
    Function.Bijective (restrictFun hc T hT) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun d e h => ?_, by simp⟩
  have hv : (T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val
      = (T ⟨e.1, YoungDiagram.mem_of_mem_erase e.2⟩).val := by
    have hval := congrArg Fin.val h
    exact hval
  refine Subtype.ext ?_
  simpa using T.injective (Fin.ext hv)

/-- **Deleting the corner carrying the largest label** from a standard Young tableau.  The corner
`c` and the fact that it carries the largest label are parameters rather than being read off `T`,
so that the shape of the result does not depend on `T`. -/
noncomputable def restrict (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) :
    StandardYoungTableau (YoungDiagram.erase μ c) where
  toTableau := Equiv.ofBijective _ (restrictFun_bijective hc T hT)
  row_strict' h hcell := T.row_strict h (YoungDiagram.mem_of_mem_erase hcell)
  col_strict' h hcell := T.col_strict h (YoungDiagram.mem_of_mem_erase hcell)

@[simp]
theorem restrict_apply_val (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) (d : ↥(YoungDiagram.erase μ c).cells) :
    (restrict hc T hT d).val = (T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val :=
  (rfl)

/-! ### Labelling a corner with the largest label -/

theorem extend_lt (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥(YoungDiagram.erase μ c).cells) :
    (T d).val < μ.card := by
  have := (T d).isLt
  have := hc.card_erase
  omega

def extendFun (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) : ↥μ.cells → Fin μ.card :=
  fun d =>
    if h : d.1 = c then ⟨μ.card - 1, Nat.sub_lt hc.card_pos Nat.one_pos⟩
    else ⟨(T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, h⟩⟩).val, extend_lt hc T _⟩

theorem extendFun_apply_of_eq (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 = c) :
    (extendFun hc T d).val = μ.card - 1 := by
  simp only [extendFun, dite_eq_left h]

theorem extendFun_apply_of_ne (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 ≠ c) :
    (extendFun hc T d).val = (T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, h⟩⟩).val := by
  simp only [extendFun, dite_eq_right h]

theorem extendFun_bijective (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    Function.Bijective (extendFun hc T) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun d e h => ?_, by simp⟩
  have hval := congrArg Fin.val h
  have hcard := hc.card_erase
  by_cases hd : d.1 = c <;> by_cases he : e.1 = c
  · exact Subtype.ext (hd.trans he.symm)
  · rw [extendFun_apply_of_eq hc T d hd, extendFun_apply_of_ne hc T e he] at hval
    have := (T ⟨e.1, hc.mem_erase_iff.mpr ⟨e.2, he⟩⟩).isLt
    omega
  · rw [extendFun_apply_of_ne hc T d hd, extendFun_apply_of_eq hc T e he] at hval
    have := (T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, hd⟩⟩).isLt
    omega
  · rw [extendFun_apply_of_ne hc T d hd, extendFun_apply_of_ne hc T e he] at hval
    have h' : T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, hd⟩⟩
        = T ⟨e.1, hc.mem_erase_iff.mpr ⟨e.2, he⟩⟩ := Fin.ext hval
    refine Subtype.ext ?_
    simpa using T.injective h'

theorem extendFun_row (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) {i j₁ j₂ : ℕ} (h : j₁ < j₂)
    (hcell : (i, j₂) ∈ μ) :
    (extendFun hc T ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩).val
      < (extendFun hc T ⟨(i, j₂), hcell⟩).val := by
  have hcard := hc.card_erase
  by_cases h2 : ((i, j₂) : ℕ × ℕ) = c
  · have h1 : ((i, j₁) : ℕ × ℕ) ≠ c := by
      rw [← h2]
      exact fun hh => absurd (congrArg Prod.snd hh) (by omega)
    rw [extendFun_apply_of_eq hc T ⟨(i, j₂), hcell⟩ h2,
      extendFun_apply_of_ne hc T ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ h1]
    have := (T ⟨(i, j₁), hc.mem_erase_iff.mpr ⟨μ.up_left_mem le_rfl h.le hcell, h1⟩⟩).isLt
    omega
  · have h1 : ((i, j₁) : ℕ × ℕ) ≠ c := fun hh => hc.right_notMem (by
      rw [← hh]
      exact μ.up_left_mem le_rfl h hcell)
    rw [extendFun_apply_of_ne hc T ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ h1,
      extendFun_apply_of_ne hc T ⟨(i, j₂), hcell⟩ h2]
    exact T.row_strict h (hc.mem_erase_iff.mpr ⟨hcell, h2⟩)

theorem extendFun_col (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) {i₁ i₂ j : ℕ} (h : i₁ < i₂)
    (hcell : (i₂, j) ∈ μ) :
    (extendFun hc T ⟨(i₁, j), μ.up_left_mem h.le le_rfl hcell⟩).val
      < (extendFun hc T ⟨(i₂, j), hcell⟩).val := by
  have hcard := hc.card_erase
  by_cases h2 : ((i₂, j) : ℕ × ℕ) = c
  · have h1 : ((i₁, j) : ℕ × ℕ) ≠ c := by
      rw [← h2]
      exact fun hh => absurd (congrArg Prod.fst hh) (by omega)
    rw [extendFun_apply_of_eq hc T ⟨(i₂, j), hcell⟩ h2,
      extendFun_apply_of_ne hc T ⟨(i₁, j), μ.up_left_mem h.le le_rfl hcell⟩ h1]
    have := (T ⟨(i₁, j), hc.mem_erase_iff.mpr ⟨μ.up_left_mem h.le le_rfl hcell, h1⟩⟩).isLt
    omega
  · have h1 : ((i₁, j) : ℕ × ℕ) ≠ c := fun hh => hc.below_notMem (by
      rw [← hh]
      exact μ.up_left_mem h le_rfl hcell)
    rw [extendFun_apply_of_ne hc T ⟨(i₁, j), μ.up_left_mem h.le le_rfl hcell⟩ h1,
      extendFun_apply_of_ne hc T ⟨(i₂, j), hcell⟩ h2]
    exact T.col_strict h (hc.mem_erase_iff.mpr ⟨hcell, h2⟩)

/-- **Restoring a deleted corner**: extend a standard Young tableau of shape `erase μ c` to one of
shape `μ` by giving the corner `c` the largest label. -/
noncomputable def extend (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) : StandardYoungTableau μ where
  toTableau := Equiv.ofBijective _ (extendFun_bijective hc T)
  row_strict' h hcell := extendFun_row hc T h hcell
  col_strict' h hcell := extendFun_col hc T h hcell

@[simp]
theorem extend_apply_val_of_eq (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 = c) :
    (extend hc T d).val = μ.card - 1 :=
  extendFun_apply_of_eq hc T d h

@[simp]
theorem extend_apply_val_of_ne (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 ≠ c) :
    (extend hc T d).val = (T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, h⟩⟩).val :=
  extendFun_apply_of_ne hc T d h

/-- The extended tableau does carry its largest label at the restored corner, so it lies in the
fibre that `TauCeti.StandardYoungTableau.restrict` is defined on.

This is deliberately not a `simp` lemma: `TauCeti.StandardYoungTableau.extend_apply_val_of_eq`
rewrites its left-hand side to `μ.card - 1 + 1`, so its statement is not in simp-normal form. -/
theorem extend_apply_self (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    ((extend hc T) ⟨c, hc.mem⟩).val + 1 = μ.card := by
  rw [extend_apply_val_of_eq hc T ⟨c, hc.mem⟩ rfl]
  have := hc.card_pos
  omega

@[simp]
theorem restrict_extend (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    restrict hc (extend hc T) (extend_apply_self hc T) = T := by
  refine DFunLike.ext _ _ fun d => Fin.ext ?_
  rw [restrict_apply_val, extend_apply_val_of_ne hc T _ (hc.mem_erase_iff.mp d.2).2]

@[simp]
theorem extend_restrict (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) : extend hc (restrict hc T hT) = T := by
  refine DFunLike.ext _ _ fun d => Fin.ext ?_
  by_cases h : d.1 = c
  · have hd : d = ⟨c, hc.mem⟩ := Subtype.ext h
    rw [extend_apply_val_of_eq hc _ d h, hd]
    omega
  · rw [extend_apply_val_of_ne hc _ d h, restrict_apply_val]

/-- **The corner bijection**: the standard Young tableaux of shape `μ` whose largest label sits at
the corner `c` are the standard Young tableaux of shape `erase μ c`. -/
noncomputable def cornerFiberEquiv (hc : YoungDiagram.IsCorner μ c) :
    {T : StandardYoungTableau μ // (T ⟨c, hc.mem⟩).val + 1 = μ.card} ≃
      StandardYoungTableau (YoungDiagram.erase μ c) where
  toFun T := restrict hc T.1 T.2
  invFun T := ⟨extend hc T, extend_apply_self hc T⟩
  left_inv T := Subtype.ext (extend_restrict hc T.1 T.2)
  right_inv T := restrict_extend hc T

private noncomputable def maxCorner (hμ : 0 < μ.card) (T : StandardYoungTableau μ) :
    {c : ℕ × ℕ // c ∈ YoungDiagram.corners μ} :=
  ⟨maxCell hμ T, YoungDiagram.mem_corners.mpr (isCorner_maxCell hμ T)⟩

end StandardYoungTableau

/-- **The corner recursion for standard Young tableaux**: the standard Young tableaux of a nonempty
shape `μ` are counted by their corners, a tableau being recorded by the corner carrying its largest
label together with what is left after deleting that corner. -/
theorem standardCount_eq_sum_corners {μ : YoungDiagram} (hμ : 0 < μ.card) :
    standardCount μ = ∑ c ∈ YoungDiagram.corners μ, standardCount (YoungDiagram.erase μ c) := by
  classical
  have key : ∀ c : {c : ℕ × ℕ // c ∈ YoungDiagram.corners μ},
      Fintype.card {T : StandardYoungTableau μ // StandardYoungTableau.maxCorner hμ T = c}
        = standardCount (YoungDiagram.erase μ c.1) := by
    intro c
    have hc : YoungDiagram.IsCorner μ c.1 := YoungDiagram.mem_corners.mp c.2
    have e : {T : StandardYoungTableau μ // StandardYoungTableau.maxCorner hμ T = c} ≃
        StandardYoungTableau (YoungDiagram.erase μ c.1) :=
      (Equiv.subtypeEquivRight fun T => by
        rw [Subtype.ext_iff]
        exact StandardYoungTableau.maxCell_eq_iff hμ T hc.mem).trans
        (StandardYoungTableau.cornerFiberEquiv hc)
    rw [standardCount_def, Fintype.card_congr e]
  rw [standardCount_def, ← Fintype.card_congr
      (Equiv.sigmaFiberEquiv (StandardYoungTableau.maxCorner hμ)),
    Fintype.card_sigma, ← Finset.sum_coe_sort (YoungDiagram.corners μ)]
  exact Finset.sum_congr rfl fun c _ => key c

end TauCeti

end
end

/- EXACT SOURCE FourPapers.Symmetric.Vendor.Combinatorics.Young.StandardTableau.Reading -/
section
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Reading order, the superstandard tableaux, and the shapes with a unique standard tableau

Numbering the cells of a Young diagram `μ` in *reading order* -- left to right along the first
row, then left to right along the second, and so on -- labels the cell `(i, j)` by
`YoungDiagram.readingIndex μ (i, j) = μ.rowLen 0 + ⋯ + μ.rowLen (i - 1) + j`.  Reading
order increases along rows and down columns, so this labelling is a standard Young tableau, the
**row-superstandard tableau** `TauCeti.StandardYoungTableau.rowSuperstandard μ`; in particular
`TauCeti.standardCount μ`, the number `f^μ` of standard Young tableaux, is never zero.

Numbering the cells column by column instead gives a second standard Young tableau
`TauCeti.StandardYoungTableau.colSuperstandard μ`, the transpose of the row-superstandard tableau
of the transposed diagram.  The two disagree as soon as `μ` has a cell outside its first row *and*
a cell outside its first column, while a diagram with at most one row, or with at most one column
-- the empty diagram included -- has only one standard Young tableau at all.  So `f^μ = 1` holds
exactly for the diagrams with at most one row and those with at most one column.

## Main definitions

* `YoungDiagram.readingIndex`: the position of a cell in reading order.
* `TauCeti.StandardYoungTableau.rowSuperstandard`: the tableau numbering the cells row by row.
* `TauCeti.StandardYoungTableau.colSuperstandard`: the tableau numbering the cells column by
  column.

## Main results

* `TauCeti.standardCount_pos`: every Young diagram has a standard Young tableau.
* `TauCeti.standardCount_eq_one_iff`: a Young diagram has exactly one standard Young tableau
  precisely when it has at most one row or at most one column, the empty diagram included.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 0 and 5.
-/

section
open scoped Nat

namespace YoungDiagram

variable {μ : YoungDiagram}

/-- The position of the coordinate pair `c` in reading order: the number of cells of `μ` lying in
rows above `c.1`, plus the column index `c.2`.  This is defined for an arbitrary pair, but it
numbers `μ` in reading order only on the cells of `μ`. -/
def readingIndex (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (∑ i ∈ Finset.range c.1, μ.rowLen i) + c.2

/-- The reading index of a coordinate pair is the sum of the lengths of the rows of `μ` above it,
plus its column index. -/
theorem readingIndex_def (μ : YoungDiagram) (c : ℕ × ℕ) :
    readingIndex μ c = (∑ i ∈ Finset.range c.1, μ.rowLen i) + c.2 := by
  rw [readingIndex]

/-- In row `0` the reading index is the column index; for a cell of the first row of `μ` this says
that it is numbered by its column index. -/
@[simp]
theorem readingIndex_zero (μ : YoungDiagram) (j : ℕ) : readingIndex μ (0, j) = j := by
  simp [readingIndex]

/-- The reading index of `(1, 0)` is the length of the first row of `μ`; when `μ` has a second row,
`(1, 0)` is its first cell. -/
@[simp]
theorem readingIndex_one_zero (μ : YoungDiagram) : readingIndex μ (1, 0) = μ.rowLen 0 := by
  simp [readingIndex]

/-- The first `k` row lengths count the cells in the first `k` rows, so the reading index of a
cell of `μ` is smaller than the number of cells of `μ`. -/
theorem readingIndex_lt_card {c : ℕ × ℕ} (hc : c ∈ μ) : readingIndex μ c < μ.card := by
  have hsucc : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ μ.card := by
    rw [sum_range_rowLen_eq_card_filter_fst]
    exact Finset.card_filter_le _ _
  rw [Finset.sum_range_succ] at hsucc
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex]
  omega

/-- Reading order runs down the rows: a cell in an earlier row has the smaller reading index. -/
theorem readingIndex_lt_readingIndex_of_fst_lt {c d : ℕ × ℕ} (hc : c ∈ μ) (h : c.1 < d.1) :
    readingIndex μ c < readingIndex μ d := by
  have hsub : Finset.range (c.1 + 1) ⊆ Finset.range d.1 := by
    rw [Finset.range_subset_range]
    omega
  have hmono : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ ∑ i ∈ Finset.range d.1, μ.rowLen i :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_range_succ] at hmono
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex, readingIndex]
  omega

/-- Reading order runs along each row: within a row, a cell in an earlier column has the smaller
reading index. -/
theorem readingIndex_lt_readingIndex_of_snd_lt {c d : ℕ × ℕ} (hrow : c.1 = d.1) (h : c.2 < d.2) :
    readingIndex μ c < readingIndex μ d := by
  rw [readingIndex, readingIndex, hrow]
  omega

/-- Distinct cells of `μ` have distinct reading indices. -/
theorem eq_of_readingIndex_eq {c d : ℕ × ℕ} (hc : c ∈ μ) (hd : d ∈ μ)
    (h : readingIndex μ c = readingIndex μ d) : c = d := by
  rcases lt_trichotomy c.1 d.1 with hfst | hfst | hfst
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hc hfst).ne
  · rcases lt_trichotomy c.2 d.2 with hsnd | hsnd | hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst hsnd).ne
    · exact Prod.ext hfst hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst.symm hsnd).ne'
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hd hfst).ne'

end YoungDiagram

namespace TauCeti

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- The **row-superstandard tableau** of `μ`: the standard Young tableau numbering the cells of
`μ` in reading order, left to right along the first row, then left to right along the second, and
so on.  This is the tableau at which the classical-groups roadmap fixes the Young symmetrizer
`c_λ`. -/
noncomputable def rowSuperstandard (μ : YoungDiagram) : StandardYoungTableau μ where
  toTableau :=
    Equiv.ofBijective
      (fun c => ⟨YoungDiagram.readingIndex μ c.1, YoungDiagram.readingIndex_lt_card c.2⟩)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun c d hcd =>
          Subtype.ext (YoungDiagram.eq_of_readingIndex_eq c.2 d.2 (congrArg Fin.val hcd)),
          by simp⟩)
  row_strict' := fun {i j₁ j₂} h _ =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt
      (μ := μ) (c := (i, j₁)) (d := (i, j₂)) rfl h)
  col_strict' := fun {i₁ i₂ j} h hcell =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
      (c := (i₁, j)) (d := (i₂, j)) (μ.up_left_mem h.le (le_refl j) hcell) h)

/-- The row-superstandard tableau labels a cell by its reading index. -/
@[simp]
theorem rowSuperstandard_apply_val (μ : YoungDiagram) (c : ↥μ.cells) :
    (rowSuperstandard μ c).val = YoungDiagram.readingIndex μ c.1 := by
  -- `rowSuperstandard` is not `@[expose]`d, so its body is reached through its equation lemma
  -- rather than by definitional unfolding.
  rw [rowSuperstandard]
  rfl

/-- The **column-superstandard tableau** of `μ`: the standard Young tableau numbering the cells of
`μ` top to bottom down the first column, then top to bottom down the second, and so on.  It is the
transpose of the row-superstandard tableau of the transposed diagram. -/
noncomputable def colSuperstandard (μ : YoungDiagram) : StandardYoungTableau μ :=
  (transposeEquiv μ).symm (rowSuperstandard μ.transpose)

/-- The column-superstandard tableau labels a cell by the reading index of the transposed cell in
the transposed diagram. -/
@[simp]
theorem colSuperstandard_apply_val (μ : YoungDiagram) (c : ↥μ.cells) :
    (colSuperstandard μ c).val = YoungDiagram.readingIndex μ.transpose c.1.swap := by
  rw [colSuperstandard, transposeEquiv_symm_apply_val, rowSuperstandard_apply_val]

/-- Transposing the column-superstandard tableau of `μ` gives the row-superstandard tableau of the
transposed diagram: this is the defining property of `colSuperstandard`. -/
@[simp]
theorem transpose_colSuperstandard (μ : YoungDiagram) :
    (colSuperstandard μ).transpose = rowSuperstandard μ.transpose := by
  rw [colSuperstandard, ← transposeEquiv_apply, Equiv.apply_symm_apply]

/-- Every Young diagram carries a standard Young tableau. -/
instance instNonempty (μ : YoungDiagram) : Nonempty (StandardYoungTableau μ) :=
  ⟨rowSuperstandard μ⟩

/-! ### Diagrams with a unique standard Young tableau -/

/-- A diagram with at most one row has all of its cells in that row. -/
theorem fst_eq_zero_of_colLen_le_one (h : μ.colLen 0 ≤ 1) {c : ℕ × ℕ} (hc : c ∈ μ) :
    c.1 = 0 := by
  have h₀ : (c.1, 0) ∈ μ := μ.up_left_mem (le_refl _) (Nat.zero_le _) hc
  have := _root_.YoungDiagram.mem_iff_lt_colLen.mp h₀
  omega

/-- A diagram with at most one row admits only the row-superstandard tableau: a standard Young
tableau on a single row labels the cells in increasing order of column index. -/
theorem eq_rowSuperstandard_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (T : StandardYoungTableau μ) :
    T = rowSuperstandard μ := by
  have hcard : μ.card = μ.rowLen 0 := YoungDiagram.card_eq_rowLen_of_colLen_le_one h
  have hmem : ∀ k : Fin μ.card, ((0, (k : ℕ)) : ℕ × ℕ) ∈ μ := fun k =>
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (hcard ▸ k.isLt)
  have hid : (fun k : Fin μ.card => T ⟨(0, (k : ℕ)), hmem k⟩) = id :=
    StrictMono.eq_id fun k l hkl => T.row_strict (Fin.lt_def.mp hkl) (hmem l)
  refine ext fun c => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := c
  have hmemij : ((i, j) : ℕ × ℕ) ∈ μ := hij
  have hi : i = 0 := fst_eq_zero_of_colLen_le_one h hmemij
  subst hi
  have hlt : j < μ.card := hcard ▸ _root_.YoungDiagram.mem_iff_lt_rowLen.mp hmemij
  refine Fin.ext ?_
  rw [rowSuperstandard_apply_val, YoungDiagram.readingIndex_zero]
  exact congrArg Fin.val (congrFun hid ⟨j, hlt⟩)

/-- A diagram with at most one row has at most one standard Young tableau. -/
theorem subsingleton_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    Subsingleton (StandardYoungTableau μ) :=
  ⟨fun T U =>
    (eq_rowSuperstandard_of_colLen_le_one h T).trans
      (eq_rowSuperstandard_of_colLen_le_one h U).symm⟩

/-- A diagram with at most one column has at most one standard Young tableau. -/
theorem subsingleton_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) :
    Subsingleton (StandardYoungTableau μ) :=
  (transposeEquiv μ).subsingleton_congr.mpr (subsingleton_of_colLen_le_one (by simpa using h))

/-- If `μ` has a cell outside its first row and a cell outside its first column, then the
row-superstandard and the column-superstandard tableaux differ: reading by rows labels the cell
`(0, 1)` by `1`, while reading by columns labels it by the length of the first column. -/
theorem rowSuperstandard_ne_colSuperstandard (hrow : 1 < μ.rowLen 0) (hcol : 1 < μ.colLen 0) :
    rowSuperstandard μ ≠ colSuperstandard μ := by
  have hmem : ((0, 1) : ℕ × ℕ) ∈ μ := _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hrow
  intro heq
  have hval := congrArg Fin.val (DFunLike.congr_fun heq ⟨(0, 1), hmem⟩)
  rw [rowSuperstandard_apply_val, colSuperstandard_apply_val, YoungDiagram.readingIndex_zero,
    Prod.swap_prod_mk, YoungDiagram.readingIndex_one_zero,
    _root_.YoungDiagram.rowLen_transpose] at hval
  omega

end StandardYoungTableau

/-! ### Counting standard Young tableaux of extreme shapes -/

/-- **Every Young diagram has a standard Young tableau**, namely the row-superstandard one. -/
theorem standardCount_pos (μ : YoungDiagram) : 0 < standardCount μ := by
  rw [standardCount_def]
  exact Fintype.card_pos

/-- The number of standard Young tableaux of a given shape is never zero. -/
@[simp]
theorem standardCount_ne_zero (μ : YoungDiagram) : standardCount μ ≠ 0 :=
  (standardCount_pos μ).ne'

/-- A Young diagram with at most one row has exactly one standard Young tableau. -/
theorem standardCount_eq_one_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    standardCount μ = 1 := by
  have := StandardYoungTableau.subsingleton_of_colLen_le_one h
  rw [standardCount_def]
  exact Fintype.card_eq_one_iff.mpr
    ⟨StandardYoungTableau.rowSuperstandard μ, fun T => Subsingleton.elim _ _⟩

/-- A Young diagram with at most one column has exactly one standard Young tableau. -/
theorem standardCount_eq_one_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    standardCount μ = 1 := by
  rw [← standardCount_transpose]
  exact standardCount_eq_one_of_colLen_le_one (by simpa using h)

/-- A Young diagram with a cell outside its first row and a cell outside its first column has at
least two standard Young tableaux. -/
theorem one_lt_standardCount {μ : YoungDiagram} (hrow : 1 < μ.rowLen 0) (hcol : 1 < μ.colLen 0) :
    1 < standardCount μ := by
  rw [standardCount_def]
  exact Fintype.one_lt_card_iff_nontrivial.mpr
    ⟨StandardYoungTableau.rowSuperstandard μ, StandardYoungTableau.colSuperstandard μ,
      StandardYoungTableau.rowSuperstandard_ne_colSuperstandard hrow hcol⟩

/-- **The shapes with a unique standard Young tableau** are exactly the diagrams with at most one
row and those with at most one column; the empty diagram, which satisfies both hypotheses, is one
of them. -/
@[simp]
theorem standardCount_eq_one_iff {μ : YoungDiagram} :
    standardCount μ = 1 ↔ μ.rowLen 0 ≤ 1 ∨ μ.colLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h =>
    h.elim standardCount_eq_one_of_rowLen_le_one standardCount_eq_one_of_colLen_le_one⟩
  by_contra hcon
  have hrow : 1 < μ.rowLen 0 := by
    by_contra hrow
    exact hcon (Or.inl (by omega))
  have hcol : 1 < μ.colLen 0 := by
    by_contra hcol
    exact hcon (Or.inr (by omega))
  exact absurd h (one_lt_standardCount hrow hcol).ne'

end TauCeti

end
end

/- SOURCE COMPONENT MatchingConnectivity -/

/- EXACT SOURCE FourPapers.Symmetric.DualConnectivity -/
section

set_option autoImplicit false

/-!
# Elementary dual-equivalence connectivity of standard tableaux

The relation below is the usual elementary dual-equivalence swap: two consecutive
labels are swapped precisely when the adjacent third label lies between their
cells in the bottom-to-top row-reading word. Both endpoints are genuine standard
Young tableaux. Connectivity is proved by induction through largest-label corners.
-/

noncomputable section

open TauCeti
open TauCeti.StandardYoungTableau

namespace FourPapers.Symmetric

variable {μ : YoungDiagram}

/-- Numeric entries on actual cells, extended by zero outside the shape only to
avoid transport between the types of cells of a shape and of its corner deletion. -/
def tableauEntry (T : StandardYoungTableau μ) (c : ℕ × ℕ) : ℕ :=
  if h : c ∈ μ then (T ⟨c, h⟩).val else 0

@[simp] theorem tableauEntry_of_mem (T : StandardYoungTableau μ) {c : ℕ × ℕ}
    (hc : c ∈ μ) : tableauEntry T c = (T ⟨c, hc⟩).val := by
  simp only [tableauEntry, dif_pos hc]

 theorem tableauEntry_injective (T : StandardYoungTableau μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (h : tableauEntry T c = tableauEntry T d) : c = d := by
  rw [tableauEntry_of_mem T hc, tableauEntry_of_mem T hd] at h
  exact congrArg Subtype.val (T.injective (Fin.ext h))

 theorem tableauEntry_ext {T U : StandardYoungTableau μ}
    (h : ∀ c ∈ μ, tableauEntry T c = tableauEntry U c) : T = U := by
  apply StandardYoungTableau.ext
  intro c
  apply Fin.ext
  simpa only [tableauEntry_of_mem _ c.2] using h c c.2

/-- Strictly between two cells in the row-reading word. -/
def RowReadBetween (a e b : ℕ × ℕ) : Prop :=
  (RowReadBefore a e ∧ RowReadBefore e b) ∨
    (RowReadBefore b e ∧ RowReadBefore e a)

/-- An elementary dual-equivalence edge, written directly in terms of the three
consecutive numeric labels and their actual cells. -/
def DualMove (T U : StandardYoungTableau μ) : Prop :=
  ∃ a b e : ℕ × ℕ, a ∈ μ ∧ b ∈ μ ∧ e ∈ μ ∧
    tableauEntry T a + 1 = tableauEntry T b ∧
    (tableauEntry T e + 1 = tableauEntry T a ∨
      tableauEntry T b + 1 = tableauEntry T e) ∧
    RowReadBetween a e b ∧
    ∀ x ∈ μ, tableauEntry U x =
      if x = a then tableauEntry T b else if x = b then tableauEntry T a
      else tableauEntry T x

/-- A finite sequence of elementary dual-equivalence edges, allowing reverse
traversal. Identity moves do not change this equivalence relation. -/
def DualEquivalent (T U : StandardYoungTableau μ) : Prop := Relation.EqvGen DualMove T U

 theorem tableauEntry_extend {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) {d : ℕ × ℕ}
    (hd : d ∈ YoungDiagram.erase μ c) :
    tableauEntry (extend hc T) d = tableauEntry T d := by
  rw [tableauEntry_of_mem _ (YoungDiagram.mem_of_mem_erase hd), tableauEntry_of_mem _ hd,
    extend_apply_val_of_ne hc T _ (hc.mem_erase_iff.mp hd).2]

 theorem tableauEntry_extend_corner {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    tableauEntry (extend hc T) c + 1 = μ.card := by
  rw [tableauEntry_of_mem _ hc.mem]
  exact extend_apply_self hc T

 theorem DualMove.extend {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    {T U : StandardYoungTableau (YoungDiagram.erase μ c)} (h : DualMove T U) :
    DualMove (extend hc T) (extend hc U) := by
  obtain ⟨a, b, e, ha, hb, he, hab, hadj, hbetween, hswap⟩ := h
  refine ⟨a, b, e, YoungDiagram.mem_of_mem_erase ha,
    YoungDiagram.mem_of_mem_erase hb, YoungDiagram.mem_of_mem_erase he, ?_, ?_, hbetween, ?_⟩
  · simpa only [tableauEntry_extend hc T ha, tableauEntry_extend hc T hb] using hab
  · simpa only [tableauEntry_extend hc T ha, tableauEntry_extend hc T hb,
      tableauEntry_extend hc T he] using hadj
  · intro x hx
    have hac : a ≠ c := (hc.mem_erase_iff.mp ha).2
    have hbc : b ≠ c := (hc.mem_erase_iff.mp hb).2
    by_cases hxc : x = c
    · subst x
      simp only [hac.symm, hbc.symm, if_false]
      have ht := tableauEntry_extend_corner hc T
      have hu := tableauEntry_extend_corner hc U
      omega
    · have hx' := hc.mem_erase_iff.mpr ⟨hx, hxc⟩
      simpa only [tableauEntry_extend hc U hx', tableauEntry_extend hc T ha,
        tableauEntry_extend hc T hb, tableauEntry_extend hc T hx'] using hswap x hx'

 theorem DualEquivalent.extend {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    {T U : StandardYoungTableau (YoungDiagram.erase μ c)} (h : DualEquivalent T U) :
    DualEquivalent (extend hc T) (extend hc U) := by
  induction h with
  | rel T U h => exact Relation.EqvGen.rel _ _ (DualMove.extend hc h)
  | refl T => exact Relation.EqvGen.refl _
  | symm T U h ih => exact Relation.EqvGen.symm _ _ ih
  | trans T U V h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem swap_last_two_lt (T : StandardYoungTableau μ)
    (c d : ↥μ.cells) (hc : YoungDiagram.IsCorner μ c.val)
    (hd : YoungDiagram.IsCorner μ d.val)
    (hC : (T c).val + 1 = μ.card) (hD : (T d).val + 2 = μ.card)
    (x y : ↥μ.cells) (hxy : x.val ≤ y.val) (hne : x ≠ y) (hlt : T x < T y) :
    T (Equiv.swap c d x) < T (Equiv.swap c d y) := by
  classical
  have hxc : x ≠ c := by
    intro h
    subst x
    have := hc.eq_of_le y.2 hxy
    exact hne (Subtype.ext this.symm)
  have hxd : x ≠ d := by
    intro h
    subst x
    have := hd.eq_of_le y.2 hxy
    exact hne (Subtype.ext this.symm)
  have hsmall : (T x).val < (T d).val := by
    have hxb := (T x).isLt
    have hxc' : (T x).val ≠ (T c).val := by
      intro h
      exact hxc (T.injective (Fin.ext h))
    have hxd' : (T x).val ≠ (T d).val := by
      intro h
      exact hxd (T.injective (Fin.ext h))
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hxc hxd]
  by_cases hyc : y = c
  · subst y
    simpa only [Equiv.swap_apply_left, Fin.lt_def] using hsmall
  · by_cases hyd : y = d
    · subst y
      rw [Equiv.swap_apply_right]
      change (T x).val < (T c).val
      omega
    · simpa only [Equiv.swap_apply_of_ne_of_ne hyc hyd] using hlt

/-- Exchanging the two largest labels in different removable corners preserves
standardness. -/
def swapLastTwoCorners (T : StandardYoungTableau μ) (c d : ↥μ.cells)
    (hc : YoungDiagram.IsCorner μ c.val) (hd : YoungDiagram.IsCorner μ d.val)
    (hC : (T c).val + 1 = μ.card) (hD : (T d).val + 2 = μ.card) :
    StandardYoungTableau μ where
  toTableau := (Equiv.swap c d).trans T.toTableau
  row_strict' := by
    intro i j₁ j₂ hj hcell
    change T (Equiv.swap c d ⟨(i, j₁), _⟩) < T (Equiv.swap c d ⟨(i, j₂), hcell⟩)
    apply swap_last_two_lt T c d hc hd hC hD
      ⟨(i, j₁), μ.up_left_mem le_rfl hj.le hcell⟩ ⟨(i, j₂), hcell⟩
      ⟨le_rfl, hj.le⟩ _ (T.row_strict hj hcell)
    intro h
    have heq := congrArg (fun x : ↥μ.cells => x.val.2) h
    change j₁ = j₂ at heq
    omega
  col_strict' := by
    intro i₁ i₂ j hi hcell
    change T (Equiv.swap c d ⟨(i₁, j), _⟩) < T (Equiv.swap c d ⟨(i₂, j), hcell⟩)
    apply swap_last_two_lt T c d hc hd hC hD
      ⟨(i₁, j), μ.up_left_mem hi.le le_rfl hcell⟩ ⟨(i₂, j), hcell⟩
      ⟨hi.le, le_rfl⟩ _ (T.col_strict hi hcell)
    intro h
    have heq := congrArg (fun x : ↥μ.cells => x.val.1) h
    change i₁ = i₂ at heq
    omega

 theorem tableauEntry_swapLastTwo (T : StandardYoungTableau μ) (c d : ↥μ.cells)
    (hc : YoungDiagram.IsCorner μ c.val) (hd : YoungDiagram.IsCorner μ d.val)
    (hC : (T c).val + 1 = μ.card) (hD : (T d).val + 2 = μ.card)
    {x : ℕ × ℕ} (hx : x ∈ μ) :
    tableauEntry (swapLastTwoCorners T c d hc hd hC hD) x =
      if x = c.val then tableauEntry T d.val else
        if x = d.val then tableauEntry T c.val else tableauEntry T x := by
  classical
  rw [tableauEntry_of_mem _ hx]
  change (T (Equiv.swap c d ⟨x, hx⟩)).val = _
  by_cases hxc : x = c.val
  · have heq : (⟨x, hx⟩ : ↥μ.cells) = c := Subtype.ext hxc
    simp only [heq, Equiv.swap_apply_left, hxc, if_true,
      tableauEntry_of_mem T d.2]
  · by_cases hxd : x = d.val
    · have heq : (⟨x, hx⟩ : ↥μ.cells) = d := Subtype.ext hxd
      simp only [heq, Equiv.swap_apply_right, if_neg hxc, if_pos hxd,
        tableauEntry_of_mem T c.2]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hxc (congrArg Subtype.val h))
        (fun h => hxd (congrArg Subtype.val h))]
      simp only [if_neg hxc, if_neg hxd, tableauEntry_of_mem T hx]

/-- A single elementary dual-equivalence edge joins suitable tableaux whose
largest entries lie in either of two prescribed different corners. -/
theorem exists_dual_corner_bridge {c d : ℕ × ℕ}
    (hc : YoungDiagram.IsCorner μ c) (hd : YoungDiagram.IsCorner μ d) (hrow : c.1 < d.1) :
    ∃ T U : StandardYoungTableau μ,
      tableauEntry T c + 1 = μ.card ∧ tableauEntry U d + 1 = μ.card ∧ DualMove T U := by
  have hdc : d ≠ c := by intro h; have := congrArg Prod.fst h; omega
  have hd' := corner_survives_erase hc hd hdc
  obtain ⟨e, he, hde, hec⟩ := exists_corner_between hc hd hrow
  let ν := YoungDiagram.erase (YoungDiagram.erase μ c) d
  let S : StandardYoungTableau ν := extend he (rowSuperstandard (YoungDiagram.erase ν e))
  let R : StandardYoungTableau (YoungDiagram.erase μ c) := extend hd' S
  let T : StandardYoungTableau μ := extend hc R
  have hTc : tableauEntry T c + 1 = μ.card := tableauEntry_extend_corner hc R
  have hTd : tableauEntry T d + 2 = μ.card := by
    rw [show tableauEntry T d = tableauEntry R d from tableauEntry_extend hc R hd'.mem]
    have ht := tableauEntry_extend_corner hd' S
    change tableauEntry R d + 1 = (YoungDiagram.erase μ c).card at ht
    have hcsize := hc.card_erase
    omega
  have heμc := YoungDiagram.mem_of_mem_erase he.mem
  have heμ := YoungDiagram.mem_of_mem_erase heμc
  have hTe : tableauEntry T e + 3 = μ.card := by
    rw [show tableauEntry T e = tableauEntry R e from tableauEntry_extend hc R heμc,
      show tableauEntry R e = tableauEntry S e from tableauEntry_extend hd' S he.mem]
    have ht := tableauEntry_extend_corner he (rowSuperstandard (YoungDiagram.erase ν e))
    have hcsize := hc.card_erase
    have hdsize := hd'.card_erase
    change tableauEntry S e + 1 = ν.card at ht
    dsimp only [ν] at ht
    omega
  let C : ↥μ.cells := ⟨c, hc.mem⟩
  let D : ↥μ.cells := ⟨d, hd.mem⟩
  have hC : (T C).val + 1 = μ.card := by simpa only [tableauEntry_of_mem T hc.mem] using hTc
  have hD : (T D).val + 2 = μ.card := by simpa only [tableauEntry_of_mem T hd.mem] using hTd
  let U := swapLastTwoCorners T C D hc hd hC hD
  have hU (x : ℕ × ℕ) (hx : x ∈ μ) : tableauEntry U x =
      if x = c then tableauEntry T d else if x = d then tableauEntry T c
      else tableauEntry T x := tableauEntry_swapLastTwo T C D hc hd hC hD hx
  have hUd : tableauEntry U d + 1 = μ.card := by
    rw [hU d hd.mem]
    simp only [if_neg hdc, if_pos rfl]
    exact hTc
  refine ⟨T, U, hTc, hUd, d, c, e, hd.mem, hc.mem, heμ, ?_, ?_, Or.inl ⟨hde, hec⟩, ?_⟩
  · omega
  · exact Or.inl (by omega)
  · intro x hx
    rw [hU x hx]
    by_cases hxc : x = c
    · subst x
      simp [hdc, hdc.symm]
    · by_cases hxd : x = d
      · subst x
        simp [hdc, hdc.symm]
      · simp [hxc, hxd]

theorem dualConnected_of_card (n : ℕ) :
    ∀ μ : YoungDiagram, μ.card = n → ∀ T U : StandardYoungTableau μ, DualEquivalent T U := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro μ hcard T U
    by_cases hn : μ.card = 0
    · have hTU : T = U := by
        apply StandardYoungTableau.ext
        intro c
        have := (T c).isLt
        omega
      subst U
      exact Relation.EqvGen.refl T
    · have hpos : 0 < μ.card := Nat.pos_of_ne_zero hn
      let c := maxCell hpos T
      let d := maxCell hpos U
      have hc : YoungDiagram.IsCorner μ c := isCorner_maxCell hpos T
      have hd : YoungDiagram.IsCorner μ d := isCorner_maxCell hpos U
      have hTc : tableauEntry T c + 1 = μ.card := by
        rw [tableauEntry_of_mem T hc.mem]
        exact apply_maxCell hpos T
      have hUd : tableauEntry U d + 1 = μ.card := by
        rw [tableauEntry_of_mem U hd.mem]
        exact apply_maxCell hpos U
      have fiber {e : ℕ × ℕ} (he : YoungDiagram.IsCorner μ e)
          {V W : StandardYoungTableau μ}
          (hV : tableauEntry V e + 1 = μ.card) (hW : tableauEntry W e + 1 = μ.card) :
          DualEquivalent V W := by
        have hV' : (V ⟨e, he.mem⟩).val + 1 = μ.card := by
          simpa only [tableauEntry_of_mem V he.mem] using hV
        have hW' : (W ⟨e, he.mem⟩).val + 1 = μ.card := by
          simpa only [tableauEntry_of_mem W he.mem] using hW
        have hlt : (YoungDiagram.erase μ e).card < n := by
          have := he.card_erase
          omega
        have hpath := ih _ hlt (YoungDiagram.erase μ e) rfl
          (restrict he V hV') (restrict he W hW')
        have hpath' := DualEquivalent.extend he hpath
        simpa only [extend_restrict] using hpath'
      by_cases hcd : c = d
      · exact fiber hc hTc (by simpa only [← hcd] using hUd)
      · have hrowne : c.1 ≠ d.1 := fun h => hcd (hc.eq_of_fst_eq hd h)
        rcases lt_or_gt_of_ne hrowne with hrow | hrow
        · obtain ⟨V, W, hVc, hWd, hVW⟩ := exists_dual_corner_bridge hc hd hrow
          exact Relation.EqvGen.trans _ _ _ (fiber hc hTc hVc)
            (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hVW) (fiber hd hWd hUd))
        · obtain ⟨V, W, hVd, hWc, hVW⟩ := exists_dual_corner_bridge hd hc hrow
          exact Relation.EqvGen.trans _ _ _ (fiber hc hTc hWc)
            (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _
              (Relation.EqvGen.rel _ _ hVW)) (fiber hd hVd hUd))

/-- Every pair of standard Young tableaux of the same shape is connected by a
finite sequence of elementary dual-equivalence moves, for every finite shape. -/
theorem standardTableaux_dual_connected (T U : StandardYoungTableau μ) : DualEquivalent T U :=
  dualConnected_of_card μ.card μ rfl T U

end FourPapers.Symmetric

end
end

/- SOURCE COMPONENT MatchingMonomials -/

namespace FourPapers.Symmetric

/-- Independent symmetric coordinates, ordered by larger then smaller endpoint.
This is definitionally equal to the algebraic `Entry` coordinate type. -/
abbrev MatchingEntry (n : ℕ) := {p : Fin n ×ₗ Fin n // p.2 ≤ p.1}

/-- The original monomial is processed by increasing `(larger, smaller)` endpoints,
with every exponent retained as an exact multiplicity. -/
noncomputable def monomialPairs {n : ℕ} (m : MatchingEntry n →₀ ℕ) : List (Fin n × Fin n) :=
  (m.toMultiset.sort (· ≤ ·)).map fun e => (e.val.2, e.val.1)

/-- The paper's tableau algorithm, without assuming its theorem in its definition. -/
noncomputable def pairedTableau {n : ℕ} (m : MatchingEntry n →₀ ℕ) : List (List (Fin n)) :=
  pairInsertList (monomialPairs m)

 theorem pairedTableau_evenRows {n : ℕ} (m : MatchingEntry n →₀ ℕ) : EvenRows (pairedTableau m) :=
  evenRows_nil.pairInsertList _

 theorem pairedTableau_content {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    (pairedTableau m).flatten.Perm (endpointWord (monomialPairs m)) := by
  simpa [pairedTableau] using flatten_pairInsertList_perm (monomialPairs m) []

end FourPapers.Symmetric

/- SOURCE COMPONENT MatchingCarrierArithmetic -/

/- EXACT SOURCE FourPapers.Symmetric.CarrierArithmetic -/
section

set_option autoImplicit false

/-!
# Exact arithmetic of symmetric row-deletion carriers

These are the unbounded natural-number operations (3.2) and (3.3), not a finite table
of evaluations. The involutions are valid for all carrier multiplicities and all entry
multiplicities. They preserve the endpoint weights used in the Hilbert-series comparison.
-/

namespace FourPapers.Symmetric

/-- The off-diagonal operation on the two carriers and the entry multiplicity. -/
def offDiagonalCarrier (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let s := min x.1 x.2.1
  (x.1 - s + x.2.2, x.2.1 - s + x.2.2, s)

/-- The diagonal operation pairs the unused carrier demands in twos. -/
def diagonalCarrier (x : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 % 2 + 2 * x.2, x.1 / 2)

/-- Every off-diagonal carrier update is exactly invertible by the same formula. -/
theorem offDiagonalCarrier_involutive : Function.Involutive offDiagonalCarrier := by
  rintro ⟨p, q, r⟩
  apply Prod.ext
  · dsimp [offDiagonalCarrier]
    omega
  · apply Prod.ext <;> dsimp [offDiagonalCarrier] <;> omega

/-- Every diagonal carrier update is exactly invertible by the same formula. -/
theorem diagonalCarrier_involutive : Function.Involutive diagonalCarrier := by
  rintro ⟨p, q⟩
  apply Prod.ext <;> dsimp [diagonalCarrier] <;> omega

/-- An off-diagonal update preserves the first endpoint degree. -/
theorem offDiagonalCarrier_weight_left (x : ℕ × ℕ × ℕ) :
    (offDiagonalCarrier x).1 + (offDiagonalCarrier x).2.2 = x.1 + x.2.2 := by
  dsimp [offDiagonalCarrier]
  omega

/-- An off-diagonal update preserves the second endpoint degree. -/
theorem offDiagonalCarrier_weight_right (x : ℕ × ℕ × ℕ) :
    (offDiagonalCarrier x).2.1 + (offDiagonalCarrier x).2.2 = x.2.1 + x.2.2 := by
  dsimp [offDiagonalCarrier]
  omega

/-- A diagonal update preserves the endpoint degree, counting a loop twice. -/
theorem diagonalCarrier_weight (x : ℕ × ℕ) :
    (diagonalCarrier x).1 + 2 * (diagonalCarrier x).2 = x.1 + 2 * x.2 := by
  dsimp [diagonalCarrier]
  omega

/-- The off-diagonal carrier operation packaged as a genuine bijection. -/
def offDiagonalCarrierEquiv : (ℕ × ℕ × ℕ) ≃ (ℕ × ℕ × ℕ) :=
  ⟨offDiagonalCarrier, offDiagonalCarrier, offDiagonalCarrier_involutive,
    offDiagonalCarrier_involutive⟩

/-- The diagonal carrier operation packaged as a genuine bijection. -/
def diagonalCarrierEquiv : (ℕ × ℕ) ≃ (ℕ × ℕ) :=
  ⟨diagonalCarrier, diagonalCarrier, diagonalCarrier_involutive,
    diagonalCarrier_involutive⟩

end FourPapers.Symmetric

end

/- EXACT SOURCE FourPapers.Symmetric.ExactCarriers -/
section

set_option autoImplicit false

/-!
# The carrier bijection on the actual symmetric monomial coordinates

The coordinates are precisely the carriers `bᵢ` and the independent symmetric entries.
They are processed by increasing `(larger endpoint, smaller endpoint)`, with each diagonal
last in its endpoint stage. This proves the bijection portion of Lemma 3.2 on unbounded
exponents. Its tableau and northwest-rank preservation are additional assertions.
-/

namespace FourPapers.Symmetric

/-- The exact independent symmetric exponents, together with the carrier exponents. -/
abbrev ExactCarrierState (n : ℕ) := (Fin n → ℕ) × (MatchingEntry n → ℕ)

/-- Apply (3.2) at one independent entry. -/
def exactOffDiagonal {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n) :
    ExactCarrierState n :=
  let q := offDiagonalCarrier (s.1 e.val.2, s.1 e.val.1, s.2 e)
  (Function.update (Function.update s.1 e.val.2 q.1) e.val.1 q.2.1,
    Function.update s.2 e q.2.2)

/-- Apply (3.3) at one independent entry. Used only on the diagonal in the sequence. -/
def exactDiagonal {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n) : ExactCarrierState n :=
  let q := diagonalCarrier (s.1 e.val.2, s.2 e)
  (Function.update s.1 e.val.2 q.1, Function.update s.2 e q.2)

theorem exactOffDiagonal_involutive {n : ℕ} (e : MatchingEntry n) (he : e.val.2 ≠ e.val.1) :
    Function.Involutive (exactOffDiagonal e) := by
  intro s
  have h := offDiagonalCarrier_involutive (s.1 e.val.2, s.1 e.val.1, s.2 e)
  apply Prod.ext
  · funext k
    by_cases hki : k = e.val.2
    · subst k
      simpa [exactOffDiagonal, he, he.symm] using congrArg Prod.fst h
    · by_cases hkj : k = e.val.1
      · subst k
        simpa [exactOffDiagonal, he, he.symm] using congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) h
      · simp [exactOffDiagonal, hki, hkj]
  · funext p
    by_cases hp : p = e
    · subst p
      simpa [exactOffDiagonal, he, he.symm] using congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) h
    · simp [exactOffDiagonal, hp]

theorem exactDiagonal_involutive {n : ℕ} (e : MatchingEntry n) :
    Function.Involutive (exactDiagonal e) := by
  intro s
  have h := diagonalCarrier_involutive (s.1 e.val.2, s.2 e)
  apply Prod.ext
  · funext k
    by_cases hk : k = e.val.2
    · subst k
      simpa [exactDiagonal] using congrArg Prod.fst h
    · simp [exactDiagonal, hk]
  · funext p
    by_cases hp : p = e
    · subst p
      simpa [exactDiagonal] using congrArg Prod.snd h
    · simp [exactDiagonal, hp]

/-- Use exactly the diagonal or off-diagonal formula appropriate to this coordinate. -/
def exactCarrierStep {n : ℕ} (e : MatchingEntry n) : ExactCarrierState n ≃ ExactCarrierState n :=
  if he : e.val.2 = e.val.1 then
    ⟨exactDiagonal e, exactDiagonal e,
      exactDiagonal_involutive e, exactDiagonal_involutive e⟩
  else
    ⟨exactOffDiagonal e, exactOffDiagonal e,
      exactOffDiagonal_involutive e he, exactOffDiagonal_involutive e he⟩

/-- The paper's endpoint order, including the diagonal after all smaller lower endpoints. -/
def orderedCarrierEntries (n : ℕ) : List (MatchingEntry n) :=
  (Finset.univ : Finset (MatchingEntry n)).sort (· ≤ ·)

/-- Compose the explicitly invertible steps in their listed order. -/
def exactCarrierSequence {n : ℕ} : List (MatchingEntry n) → ExactCarrierState n ≃ ExactCarrierState n
  | [] => Equiv.refl _
  | e :: es => (exactCarrierStep e).trans (exactCarrierSequence es)

/-- The full row-deletion carrier arithmetic on the precise coordinate set. -/
def exactCarrierEquiv (n : ℕ) : ExactCarrierState n ≃ ExactCarrierState n :=
  exactCarrierSequence (orderedCarrierEntries n)

/-- The required exponent-set bijection `m ↔ (c,N)`, with free natural carriers and
arbitrary symmetric residual monomials. No lower-triangular surplus variables occur. -/
noncomputable def monomialCarrierEquiv (n : ℕ) :
    ((Fin n ⊕ MatchingEntry n) →₀ ℕ) ≃ (Fin n → ℕ) × (MatchingEntry n →₀ ℕ) :=
  Finsupp.equivFunOnFinite.trans
    ((Equiv.sumArrowEquivProdArrow (Fin n) (MatchingEntry n) ℕ).trans
      ((exactCarrierEquiv n).trans
        (Equiv.prodCongr (Equiv.refl _) Finsupp.equivFunOnFinite.symm)))

theorem monomialCarrierEquiv_bijective (n : ℕ) :
    Function.Bijective (monomialCarrierEquiv n) := (monomialCarrierEquiv n).bijective

/-- Endpoint degree with the first vertex assigned degree zero: each carrier contributes
once at its endpoint and each symmetric entry contributes once at each endpoint. -/
def carrierEndpointWeight {n : ℕ} (s : ExactCarrierState n) (k : Fin n) : ℕ :=
  s.1 k + ∑ e : MatchingEntry n, s.2 e *
    ((if e.val.2 = k then 1 else 0) + (if e.val.1 = k then 1 else 0))

theorem weightedSum_update {α : Type*} [Fintype α] [DecidableEq α]
    (f w : α → ℕ) (a : α) (v : ℕ) :
    (∑ b, Function.update f a v b * w b) =
      (∑ b ∈ Finset.univ.erase a, f b * w b) + v * w a := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  rw [Function.update_of_ne (Finset.mem_erase.mp hb).1]

theorem exactOffDiagonal_preserves_weight {n : ℕ} (e : MatchingEntry n)
    (he : e.val.2 ≠ e.val.1) (s : ExactCarrierState n) (k : Fin n) :
    carrierEndpointWeight (exactOffDiagonal e s) k = carrierEndpointWeight s k := by
  classical
  let w : MatchingEntry n → ℕ := fun d =>
    (if d.val.2 = k then 1 else 0) + (if d.val.1 = k then 1 else 0)
  let q := offDiagonalCarrier (s.1 e.val.2, s.1 e.val.1, s.2 e)
  change (Function.update (Function.update s.1 e.val.2 q.1) e.val.1 q.2.1) k +
      (∑ d, Function.update s.2 e q.2.2 d * w d) = s.1 k + ∑ d, s.2 d * w d
  rw [weightedSum_update]
  rw [← Finset.sum_erase_add _ (fun d => s.2 d * w d) (Finset.mem_univ e)]
  by_cases hk : k = e.val.2
  · subst k
    simp only [Function.update_self, Function.update_of_ne he, w, if_true,
      if_neg he.symm, add_zero, mul_one]
    have h := offDiagonalCarrier_weight_left (s.1 e.val.2, s.1 e.val.1, s.2 e)
    dsimp only [q] at *
    omega
  · by_cases hk' : k = e.val.1
    · subst k
      simp only [Function.update_self, w, if_neg he, if_true, zero_add, mul_one]
      have h := offDiagonalCarrier_weight_right (s.1 e.val.2, s.1 e.val.1, s.2 e)
      dsimp only [q] at *
      omega
    · simp [Function.update_of_ne hk, Function.update_of_ne hk', w, Ne.symm hk, Ne.symm hk']

theorem exactDiagonal_preserves_weight {n : ℕ} (e : MatchingEntry n)
    (he : e.val.2 = e.val.1) (s : ExactCarrierState n) (k : Fin n) :
    carrierEndpointWeight (exactDiagonal e s) k = carrierEndpointWeight s k := by
  classical
  let w : MatchingEntry n → ℕ := fun d =>
    (if d.val.2 = k then 1 else 0) + (if d.val.1 = k then 1 else 0)
  let q := diagonalCarrier (s.1 e.val.2, s.2 e)
  change (Function.update s.1 e.val.2 q.1) k +
      (∑ d, Function.update s.2 e q.2 d * w d) = s.1 k + ∑ d, s.2 d * w d
  rw [weightedSum_update]
  rw [← Finset.sum_erase_add _ (fun d => s.2 d * w d) (Finset.mem_univ e)]
  by_cases hk : k = e.val.2
  · subst k
    simp only [Function.update_self, w, if_true, if_pos he.symm, one_add_one_eq_two]
    have h := diagonalCarrier_weight (s.1 e.val.2, s.2 e)
    dsimp only [q] at *
    omega
  · have hk' : e.val.1 ≠ k := by simpa [← he] using Ne.symm hk
    simp [Function.update_of_ne hk, w, Ne.symm hk, hk']

theorem exactCarrierStep_preserves_weight {n : ℕ} (e : MatchingEntry n)
    (s : ExactCarrierState n) (k : Fin n) :
    carrierEndpointWeight (exactCarrierStep e s) k = carrierEndpointWeight s k := by
  unfold exactCarrierStep
  split_ifs with he
  · exact exactDiagonal_preserves_weight e he s k
  · exact exactOffDiagonal_preserves_weight e he s k

/-- Every stage preserves the endpoint grading, hence so does the complete bijection. -/
theorem exactCarrierSequence_preserves_weight {n : ℕ} (es : List (MatchingEntry n))
    (s : ExactCarrierState n) (k : Fin n) :
    carrierEndpointWeight (exactCarrierSequence es s) k = carrierEndpointWeight s k := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    change carrierEndpointWeight (exactCarrierSequence es (exactCarrierStep e s)) k = _
    rw [ih, exactCarrierStep_preserves_weight]

theorem exactCarrierEquiv_preserves_weight (n : ℕ) (s : ExactCarrierState n) (k : Fin n) :
    carrierEndpointWeight (exactCarrierEquiv n s) k = carrierEndpointWeight s k :=
  exactCarrierSequence_preserves_weight (orderedCarrierEntries n) s k

/-- The weight statement directly on the input monomial and output pair `(c,N)`. -/
theorem monomialCarrierEquiv_preserves_weight (n : ℕ)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) (k : Fin n) :
    (monomialCarrierEquiv n m).1 k +
        (∑ e : MatchingEntry n, (monomialCarrierEquiv n m).2 e *
          ((if e.val.2 = k then 1 else 0) + (if e.val.1 = k then 1 else 0))) =
      m (.inl k) + ∑ e : MatchingEntry n, m (.inr e) *
        ((if e.val.2 = k then 1 else 0) + (if e.val.1 = k then 1 else 0)) := by
  change carrierEndpointWeight
    (exactCarrierEquiv n ((fun i => m (.inl i)), (fun e => m (.inr e)))) k =
      carrierEndpointWeight ((fun i => m (.inl i)), (fun e => m (.inr e))) k
  exact exactCarrierEquiv_preserves_weight n _ k

end FourPapers.Symmetric

end

/- SOURCE COMPONENT MatchingKnuthCore -/

/- EXACT SOURCE SLICE HigherSpecht.CatMoveInvariance: KnuthEquivalent -/
namespace HigherSpecht
/-- A literal Knuth replacement of a natural-number word. -/
inductive KnuthEquivalent : List ℕ → List ℕ → Prop
  | refl (u) : KnuthEquivalent u u
  | symm {u v} : KnuthEquivalent u v → KnuthEquivalent v u
  | trans {u v w} : KnuthEquivalent u v → KnuthEquivalent v w → KnuthEquivalent u w
  | append {u v} (l r) : KnuthEquivalent u v → KnuthEquivalent (l ++ u ++ r) (l ++ v ++ r)
  | left {a b c : ℕ} : a < b → b ≤ c → KnuthEquivalent [b, a, c] [b, c, a]
  | right {a b c : ℕ} : a ≤ b → b < c → KnuthEquivalent [a, c, b] [c, a, b]


end HigherSpecht

/- EXACT RECOVERED SOURCE HigherSpecht.KnuthRowInsertion -/
section
section
/-!
# Knuth reduction of row insertion

Only the elementary three-letter relations are used.  The result connects the
literal word to the row word of its actual insertion tableau, including repeated
letters.  The rows need only be weakly increasing; empty padded rows are allowed.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

namespace KnuthEquivalent

 theorem append_left {u v : List ℕ} (h : KnuthEquivalent u v) (l : List ℕ) :
    KnuthEquivalent (l ++ u) (l ++ v) := by
  simpa only [List.append_nil] using h.append l []

 theorem append_right {u v : List ℕ} (h : KnuthEquivalent u v) (r : List ℕ) :
    KnuthEquivalent (u ++ r) (v ++ r) := by
  simpa only [List.nil_append] using h.append [] r

 theorem cons {u v : List ℕ} (h : KnuthEquivalent u v) (a : ℕ) :
    KnuthEquivalent (a :: u) (a :: v) := by
  simpa only [List.singleton_append] using h.append_left [a]

end KnuthEquivalent

/-- Slide a small final letter leftward through a weakly increasing suffix,
using the fixed preceding letter as the Knuth mediator. -/
theorem knuth_slideSmall (after : List ℕ) (b x : ℕ)
    (hs : after.SortedLE) (hb : ∀ z ∈ after, b ≤ z) (hxb : x < b) :
    KnuthEquivalent ([b] ++ after ++ [x]) ([b, x] ++ after) := by
  induction after generalizing b with
  | nil => exact .refl _
  | cons y after ih =>
    obtain ⟨hy, hs⟩ := List.sortedLE_cons.mp hs
    have hby : b ≤ y := hb y (by simp)
    have htail := (ih y hs hy (hxb.trans_le hby)).cons b
    have hmove := (KnuthEquivalent.left hxb hby).symm.append_right after
    refine KnuthEquivalent.trans (v := ([b, y, x] ++ after)) ?_ ?_
    · simpa only [List.cons_append, List.nil_append] using htail
    · simpa only [List.cons_append, List.nil_append] using hmove

/-- Slide a bumped larger letter to the left of the unchanged row prefix. -/
theorem knuth_slideLarge (before : List ℕ) (x b : ℕ)
    (hs : before.SortedLE) (hb : ∀ z ∈ before, z ≤ x) (hxb : x < b) :
    KnuthEquivalent (before ++ [b, x]) ([b] ++ before ++ [x]) := by
  induction before using List.reverseRecOn generalizing x with
  | nil => exact .refl _
  | append_singleton before a ih =>
    obtain ⟨hbefore, _, hcross⟩ := List.sortedLE_append.mp hs
    have hax : a ≤ x := hb a (by simp)
    have hpref : ∀ z ∈ before, z ≤ a := by
      intro z hz
      exact hcross z hz a (by simp)
    have hfirst := (KnuthEquivalent.right hax hxb).append_left before
    have hsecond := (ih a hbefore hpref (hax.trans_lt hxb)).append_right [x]
    refine KnuthEquivalent.trans (v := (before ++ [b, a, x])) ?_ ?_
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hfirst
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsecond

 theorem knuth_rowBump_some (row : List ℕ) (x y : ℕ) (hs : row.SortedLE)
    (hy : (rowBump x row).2 = some y) :
    KnuthEquivalent (row ++ [x]) (y :: (rowBump x row).1) := by
  obtain ⟨before, after, hr, hout, hbefore, hxy⟩ :=
    (rowBump_eq_some_iff x y row (rowBump x row).1).mp (Prod.ext rfl hy)
  rw [hr, List.sortedLE_append, List.sortedLE_cons] at hs
  have hfirst := (knuth_slideSmall after y x hs.2.1.2 hs.2.1.1 hxy).append_left before
  have hsecond := (knuth_slideLarge before x y hs.1 hbefore hxy).append_right after
  rw [hout, hr]
  refine KnuthEquivalent.trans (v := (before ++ [y, x] ++ after)) ?_ ?_
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hfirst
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsecond

/-- Rows are listed in increasing row coordinate; the row word reads them in
reverse order and reads each individual row from left to right. -/
def rowWordRows (rows : List (List ℕ)) : List ℕ := rows.reverse.flatten

@[simp] theorem rowWordRows_nil : rowWordRows [] = [] := rfl

@[simp] theorem rowWordRows_cons (row : List ℕ) (rows : List (List ℕ)) :
    rowWordRows (row :: rows) = rowWordRows rows ++ row := by
  simp [rowWordRows]

def RowsSorted (rows : List (List ℕ)) : Prop := ∀ row ∈ rows, row.SortedLE

 theorem rowsSorted_rowInsert (x : ℕ) {rows : List (List ℕ)} (h : RowsSorted rows) :
    RowsSorted (rowInsert x rows) := by
  induction rows generalizing x with
  | nil => simp [rowInsert_nil, RowsSorted, List.sortedLE_cons, List.sortedLE_nil]
  | cons row rows ih =>
    have hr : row.SortedLE := h row (by simp)
    have ht : RowsSorted rows := fun r hr => h r (by simp [hr])
    cases hs : (rowBump x row).2 with
    | none =>
      rw [rowInsert_cons_of_eq_none rows hs]
      intro r hrmem
      rcases List.mem_cons.mp hrmem with rfl | hrmem
      · exact sortedLE_rowBump x hr
      · exact ht r hrmem
    | some y =>
      rw [rowInsert_cons_of_eq_some rows hs]
      intro r hrmem
      rcases List.mem_cons.mp hrmem with rfl | hrmem
      · exact sortedLE_rowBump x hr
      · exact ih y ht r hrmem

 theorem knuth_rowInsert (rows : List (List ℕ)) (x : ℕ) (h : RowsSorted rows) :
    KnuthEquivalent (rowWordRows rows ++ [x]) (rowWordRows (rowInsert x rows)) := by
  induction rows generalizing x with
  | nil => simpa only [rowInsert_nil, rowWordRows_cons, rowWordRows_nil, List.nil_append, List.append_nil] using KnuthEquivalent.refl [x]
  | cons row rows ih =>
    have hr : row.SortedLE := h row (by simp)
    have ht : RowsSorted rows := fun r hr => h r (by simp [hr])
    cases hs : (rowBump x row).2 with
    | none =>
      have hb := rowBump_of_forall_le x row ((rowBump_snd_eq_none_iff x row).mp hs)
      rw [rowInsert_cons_of_eq_none rows hs, rowWordRows_cons, rowWordRows_cons, hb]
      simpa only [List.append_assoc] using KnuthEquivalent.refl (rowWordRows rows ++ row ++ [x])
    | some y =>
      rw [rowInsert_cons_of_eq_some rows hs, rowWordRows_cons, rowWordRows_cons]
      have hfirst := (knuth_rowBump_some row x y hr hs).append_left (rowWordRows rows)
      have hsecond := (ih y ht).append_right (rowBump x row).1
      refine KnuthEquivalent.trans (v := (rowWordRows rows ++ [y] ++ (rowBump x row).1)) ?_ ?_
      · simpa only [List.append_assoc, List.singleton_append] using hfirst
      · simpa only [List.append_assoc, List.singleton_append] using hsecond

 theorem rowsSorted_fold_rowInsert (w : List ℕ) {rows : List (List ℕ)}
    (h : RowsSorted rows) : RowsSorted (w.foldl (fun rows x => rowInsert x rows) rows) := by
  induction w generalizing rows with
  | nil => exact h
  | cons x w ih => exact ih (rowsSorted_rowInsert x h)

 theorem knuth_fold_rowInsert (w : List ℕ) (rows : List (List ℕ)) (h : RowsSorted rows) :
    KnuthEquivalent (rowWordRows rows ++ w)
      (rowWordRows (w.foldl (fun rows x => rowInsert x rows) rows)) := by
  induction w generalizing rows with
  | nil => simpa using KnuthEquivalent.refl (rowWordRows rows)
  | cons x w ih =>
    have hfirst := (knuth_rowInsert rows x h).append_right w
    have hsecond := ih (rowInsert x rows) (rowsSorted_rowInsert x h)
    refine KnuthEquivalent.trans ?_ hsecond
    simpa only [List.append_assoc, List.singleton_append] using hfirst

end HigherSpecht

end
end
end

/- EXACT RECOVERED SOURCE HigherSpecht.KnuthRowTransducer -/
section
section
/-!
# A row-insertion transducer preserves the literal Knuth relations

`rowBumpWord` records both the final first row and, in chronological order,
the letters actually bumped into the remaining rows.  Each elementary
Knuth relation gives the same first row and Knuth-equivalent bumped words.
The proof includes equal letters and every possible absent bump.
-/

noncomputable section

open TauCeti

namespace HigherSpecht

def rowBumpWord (row : List ℕ) (word : List ℕ) : List ℕ × List ℕ :=
  (List.rec (motive := fun _ => List ℕ → List ℕ × List ℕ)
    (fun row => (row, []))
    (fun x _ ih row =>
      let first := rowBump x row
      let rest := ih first.1
      (rest.1, first.2.toList ++ rest.2)) word) row

@[simp] theorem rowBumpWord_nil (row : List ℕ) : rowBumpWord row [] = (row, []) := rfl

@[simp] theorem rowBumpWord_cons (row : List ℕ) (x : ℕ) (w : List ℕ) :
    rowBumpWord row (x :: w) =
      ((rowBumpWord (rowBump x row).1 w).1,
        (rowBump x row).2.toList ++ (rowBumpWord (rowBump x row).1 w).2) := rfl

theorem rowBump_fst_lowerBound {row : List ℕ} {a x : ℕ}
    (ha : ∀ z ∈ row, a ≤ z) (hx : a ≤ x) :
    ∀ z ∈ (rowBump x row).1, a ≤ z := by
  intro z hz
  have hm := (rowBump_perm x row).mem_iff.mp (List.mem_append_left _ hz)
  rcases List.mem_cons.mp hm with rfl | hz
  · exact hx
  · exact ha z hz

theorem rowBump_fst_upperBound {row : List ℕ} {a x : ℕ}
    (ha : ∀ z ∈ row, z ≤ a) (hx : x ≤ a) :
    ∀ z ∈ (rowBump x row).1, z ≤ a := by
  intro z hz
  have hm := (rowBump_perm x row).mem_iff.mp (List.mem_append_left _ hz)
  rcases List.mem_cons.mp hm with rfl | hz
  · exact hx
  · exact ha z hz

theorem rowBump_snd_none_of_le_of_none {row : List ℕ} {x y : ℕ}
    (hxy : x ≤ y) (hx : (rowBump x row).2 = none) :
    (rowBump y (rowBump x row).1).2 = none := by
  apply (rowBump_snd_eq_none_iff y _).mpr
  exact rowBump_fst_upperBound
    (fun z hz => ((rowBump_snd_eq_none_iff x row).mp hx z hz).trans hxy) hxy

/-- A first entry no greater than any input is passed unchanged. -/
theorem rowBumpWord_cons_of_le_all (p : ℕ) (row w : List ℕ)
    (hp : ∀ x ∈ w, p ≤ x) :
    rowBumpWord (p :: row) w =
      (p :: (rowBumpWord row w).1, (rowBumpWord row w).2) := by
  induction w generalizing row with
  | nil => rfl
  | cons x w ih =>
      have hpx := hp x (by simp)
      have htail : ∀ y ∈ w, p ≤ y := fun y hy => hp y (by simp [hy])
      simp only [rowBumpWord_cons, rowBump_cons_of_le _ hpx,
        ih _ htail]

theorem rowBumpWord_sorted (row w : List ℕ) (hrow : row.SortedLE) :
    (rowBumpWord row w).1.SortedLE := by
  induction w generalizing row with
  | nil => exact hrow
  | cons x w ih => exact ih _ (sortedLE_rowBump x hrow)

theorem rowBumpWord_bumped_length_le (row w : List ℕ) :
    (rowBumpWord row w).2.length ≤ w.length := by
  induction w generalizing row with
  | nil => simp
  | cons x w ih =>
      have h := ih (rowBump x row).1
      cases hb : (rowBump x row).2 <;>
        simp only [rowBumpWord_cons, List.length_append, hb, Option.toList_none,
          Option.toList_some, List.length_nil, List.length_singleton,
          List.length_cons] <;> omega

theorem rowBumpWord_empty_bumped_length_lt {w : List ℕ} (hw : w ≠ []) :
    (rowBumpWord [] w).2.length < w.length := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons x w =>
      have h := rowBumpWord_bumped_length_le [x] w
      simpa only [rowBumpWord_cons, rowBump_nil, Option.toList_none,
        List.nil_append, List.length_cons] using Nat.lt_succ_of_le h

theorem rowBumpWord_append (row u v : List ℕ) :
    rowBumpWord row (u ++ v) =
      ((rowBumpWord (rowBumpWord row u).1 v).1,
        (rowBumpWord row u).2 ++ (rowBumpWord (rowBumpWord row u).1 v).2) := by
  induction u generalizing row with
  | nil => simp
  | cons x u ih =>
      simp only [List.cons_append, rowBumpWord_cons, ih, List.append_assoc]

/-- The first elementary relation, with its strict and weak inequalities
in exactly the convention used in `KnuthEquivalent.left`. -/
theorem rowBumpWord_knuth_left (row : List ℕ) (hrow : row.SortedLE)
    {a b c : ℕ} (hab : a < b) (hbc : b ≤ c) :
    (rowBumpWord row [b, a, c]).1 = (rowBumpWord row [b, c, a]).1 ∧
      KnuthEquivalent (rowBumpWord row [b, a, c]).2
        (rowBumpWord row [b, c, a]).2 := by
  induction row with
  | nil =>
      have hac : a ≤ c := (hab.trans_le hbc).le
      simp only [rowBumpWord_cons, rowBumpWord_nil, rowBump_nil,
        rowBump_cons_of_lt _ hab, rowBump_cons_of_le _ hbc,
        rowBump_cons_of_le _ hac, Option.toList_none, Option.toList_some,
        List.nil_append, List.append_nil, List.cons_append]
      exact ⟨by trivial, .refl _⟩
  | cons p row ih =>
      obtain ⟨hprow, hs⟩ := List.sortedLE_cons.mp hrow
      by_cases hpa : p ≤ a
      · have h1 : ∀ x ∈ [b, a, c], p ≤ x := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact hpa.trans hab.le
          · exact hpa
          · exact hpa.trans (hab.trans_le hbc).le
        have h2 : ∀ x ∈ [b, c, a], p ≤ x := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact hpa.trans hab.le
          · exact hpa.trans (hab.trans_le hbc).le
          · exact hpa
        rw [rowBumpWord_cons_of_le_all p row _ h1,
          rowBumpWord_cons_of_le_all p row _ h2]
        exact ⟨congrArg (List.cons p) (ih hs).1, (ih hs).2⟩
      · have hap : a < p := lt_of_not_ge hpa
        by_cases hpb : p ≤ b
        · have hpc : p ≤ c := hpb.trans hbc
          have hac : a ≤ c := (hab.trans_le hbc).le
          simp only [rowBumpWord_cons, rowBumpWord_nil,
            rowBump_cons_of_le _ hpb, rowBump_cons_of_lt _ hap,
            rowBump_cons_of_le _ hpc, rowBump_cons_of_le _ hac,
            Option.toList_some, List.append_nil, List.nil_append,
            List.cons_append]
          refine ⟨by trivial, ?_⟩
          cases hb : (rowBump b row).2 with
          | none =>
              have hc := rowBump_snd_none_of_le_of_none hbc hb
              simp only [hb, hc, Option.toList_none, List.nil_append, List.append_nil]
              exact .refl _
          | some q =>
              cases hc : (rowBump c (rowBump b row).1).2 with
              | none =>
                  simp only [hb, hc, Option.toList_some, Option.toList_none,
                    List.nil_append, List.append_nil, List.cons_append]
                  exact .refl _
              | some r =>
                  have hpq : p < q := hpb.trans_lt (lt_of_rowBump_snd_eq_some hb)
                  have hqr : q ≤ r := rowBump_bumped_le_of_le hs hbc hb hc
                  simpa only [hb, hc, Option.toList_some, List.nil_append,
                    List.append_nil, List.cons_append] using KnuthEquivalent.left hpq hqr
        · have hbp : b < p := lt_of_not_ge hpb
          have hac : a ≤ c := (hab.trans_le hbc).le
          simp only [rowBumpWord_cons, rowBumpWord_nil,
            rowBump_cons_of_lt _ hbp, rowBump_cons_of_lt _ hab,
            rowBump_cons_of_le _ hbc, rowBump_cons_of_le _ hac,
            Option.toList_some, List.append_nil, List.nil_append,
            List.cons_append]
          refine ⟨by trivial, ?_⟩
          cases hc : (rowBump c row).2 with
          | none =>
              simp only [hc, Option.toList_none, List.nil_append, List.append_nil]
              exact .refl _
          | some q =>
              have hpq : p ≤ q := hprow q (mem_of_rowBump_snd_eq_some hc)
              simpa only [hc, Option.toList_some, List.nil_append,
                List.append_nil, List.cons_append] using KnuthEquivalent.left hbp hpq

/-- The second elementary relation.  When all three inputs precede the
first old entry, its outgoing relation changes from right to left; this
case is included explicitly rather than assuming a uniform bump order. -/
theorem rowBumpWord_knuth_right (row : List ℕ) (hrow : row.SortedLE)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b < c) :
    (rowBumpWord row [a, c, b]).1 = (rowBumpWord row [c, a, b]).1 ∧
      KnuthEquivalent (rowBumpWord row [a, c, b]).2
        (rowBumpWord row [c, a, b]).2 := by
  have hac : a < c := hab.trans_lt hbc
  induction row with
  | nil =>
      simp only [rowBumpWord_cons, rowBumpWord_nil, rowBump_nil,
        rowBump_cons_of_lt _ hac, rowBump_cons_of_lt _ hbc,
        rowBump_cons_of_le _ hac.le, rowBump_cons_of_le _ hab,
        Option.toList_none, Option.toList_some, List.nil_append,
        List.append_nil, List.cons_append]
      exact ⟨by trivial, .refl _⟩
  | cons p row ih =>
      obtain ⟨hprow, hs⟩ := List.sortedLE_cons.mp hrow
      by_cases hpa : p ≤ a
      · have h1 : ∀ x ∈ [a, c, b], p ≤ x := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact hpa
          · exact hpa.trans hac.le
          · exact hpa.trans hab
        have h2 : ∀ x ∈ [c, a, b], p ≤ x := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact hpa.trans hac.le
          · exact hpa
          · exact hpa.trans hab
        rw [rowBumpWord_cons_of_le_all p row _ h1,
          rowBumpWord_cons_of_le_all p row _ h2]
        exact ⟨congrArg (List.cons p) (ih hs).1, (ih hs).2⟩
      · have hap : a < p := lt_of_not_ge hpa
        by_cases hpc : p ≤ c
        · obtain ⟨q, hq, hqc⟩ := exists_rowBump_snd_eq_some_le_of_lt hbc row
          have hpq : p ≤ q := rowBump_fst_lowerBound hprow hpc q
            (mem_of_rowBump_snd_eq_some hq)
          simp only [rowBumpWord_cons, rowBumpWord_nil,
            rowBump_cons_of_lt _ hap, rowBump_cons_of_le _ hpc,
            rowBump_cons_of_le _ hac.le, rowBump_cons_of_le _ hab,
            Option.toList_some, List.append_nil, List.nil_append,
            List.cons_append, hq]
          refine ⟨by trivial, ?_⟩
          cases hc : (rowBump c row).2 with
          | none =>
              simp only [hc, Option.toList_none, Option.toList_some,
                List.nil_append, List.append_nil, List.cons_append]
              exact .refl _
          | some r =>
              have hqr : q < r := hqc.trans_lt (lt_of_rowBump_snd_eq_some hc)
              simpa only [hc, Option.toList_some, List.nil_append,
                List.append_nil, List.cons_append] using KnuthEquivalent.right hpq hqr
        · have hcp : c < p := lt_of_not_ge hpc
          cases row with
          | nil =>
              simp only [rowBumpWord_cons, rowBumpWord_nil, rowBump_nil,
                rowBump_cons_of_lt _ hap, rowBump_cons_of_lt _ hcp,
                rowBump_cons_of_lt _ hac, rowBump_cons_of_lt _ hbc,
                rowBump_cons_of_le _ hac.le, rowBump_cons_of_le _ hab,
                Option.toList_none, Option.toList_some, List.nil_append,
                List.append_nil, List.cons_append]
              exact ⟨by trivial, .refl _⟩
          | cons q row =>
              have hpq : p ≤ q := hprow q (by simp)
              have hcq : c < q := hcp.trans_le hpq
              have hbq : b < q := hbc.trans hcq
              simp only [rowBumpWord_cons, rowBumpWord_nil,
                rowBump_cons_of_lt _ hap, rowBump_cons_of_lt _ hcp,
                rowBump_cons_of_lt _ hac, rowBump_cons_of_lt _ hbc,
                rowBump_cons_of_lt _ hcq, rowBump_cons_of_lt _ hbq,
                rowBump_cons_of_le _ hac.le, rowBump_cons_of_le _ hab,
                Option.toList_some, List.nil_append, List.append_nil,
                List.cons_append]
              exact ⟨by trivial, (KnuthEquivalent.left hcp hpq).symm⟩

/-- Arbitrary Knuth transformations commute with the one-row transducer,
including arbitrary word prefixes and suffixes. -/
theorem KnuthEquivalent.rowBumpWord {u v : List ℕ} (h : KnuthEquivalent u v)
    (row : List ℕ) (hrow : row.SortedLE) :
    (HigherSpecht.rowBumpWord row u).1 = (HigherSpecht.rowBumpWord row v).1 ∧
      KnuthEquivalent (HigherSpecht.rowBumpWord row u).2 (HigherSpecht.rowBumpWord row v).2 := by
  induction h generalizing row with
  | refl u => exact ⟨by trivial, .refl _⟩
  | symm h ih => exact ⟨(ih row hrow).1.symm, (ih row hrow).2.symm⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ⟨(ih₁ row hrow).1.trans (ih₂ row hrow).1,
        (ih₁ row hrow).2.trans (ih₂ row hrow).2⟩
  | @append u v l r h ih =>
      obtain ⟨heq, hknuth⟩ := ih (HigherSpecht.rowBumpWord row l).1 (rowBumpWord_sorted row l hrow)
      simp only [rowBumpWord_append]
      rw [heq]
      refine ⟨by trivial, ?_⟩
      simpa only [List.append_assoc] using hknuth.append (HigherSpecht.rowBumpWord row l).2
        (HigherSpecht.rowBumpWord (HigherSpecht.rowBumpWord (HigherSpecht.rowBumpWord row l).1 v).1 r).2
  | left hab hbc => exact rowBumpWord_knuth_left row hrow hab hbc
  | right hab hbc => exact rowBumpWord_knuth_right row hrow hab hbc

end HigherSpecht

end
end
end

/- EXACT RECOVERED SOURCE HigherSpecht.KnuthInsertionInvariant -/
section
section
/-!
# Actual Schensted insertion is invariant under Knuth equivalence

One row is removed from the existing tableau at every recursive step.
When no row exists, the bumped word is strictly shorter than a nonempty
input word.  The well-founded measure is therefore the number of existing
rows plus the input length.  No uniqueness or insertion-tableau premise is
used to prove this invariance.
-/

noncomputable section

open TauCeti

namespace HigherSpecht

theorem knuthEquivalent_length {u v : List ℕ} (h : KnuthEquivalent u v) :
    u.length = v.length := by
  induction h with
  | refl u => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | append l r h ih => simp only [List.length_append, ih]
  | left hab hbc => rfl
  | right hab hbc => rfl

/-- Iterated insertion through an existing first row is exactly the
one-row transducer followed by insertion of its actual outgoing word. -/
theorem fold_rowInsert_cons (w row : List ℕ) (rows : List (List ℕ)) :
    w.foldl (fun rows x => rowInsert x rows) (row :: rows) =
      (rowBumpWord row w).1 ::
        (rowBumpWord row w).2.foldl (fun rows x => rowInsert x rows) rows := by
  induction w generalizing row rows with
  | nil => rfl
  | cons x w ih =>
      cases hb : (rowBump x row).2 with
      | none =>
          rw [List.foldl_cons, rowInsert_cons_of_eq_none rows hb, ih]
          simp only [rowBumpWord_cons, hb, Option.toList_none, List.nil_append]
      | some y =>
          rw [List.foldl_cons, rowInsert_cons_of_eq_some rows hb, ih]
          simp only [rowBumpWord_cons, hb, Option.toList_some,
            List.singleton_append, List.foldl_cons]

/-- For a nonempty word the first row created from the empty tableau is
the transducer's nonempty output, and the rest is its bumped word. -/
theorem fold_rowInsert_nil_of_ne_nil (w : List ℕ) (hw : w ≠ []) :
    w.foldl (fun rows x => rowInsert x rows) [] =
      (rowBumpWord [] w).1 ::
        (rowBumpWord [] w).2.foldl (fun rows x => rowInsert x rows) [] := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons x w =>
      rw [List.foldl_cons, rowInsert_nil]
      change w.foldl (fun rows x => rowInsert x rows) ([x] :: []) = _
      rw [fold_rowInsert_cons]
      simp only [rowBumpWord_cons, rowBump_nil, Option.toList_none, List.nil_append]

/-- All actual insertion operators for Knuth-equivalent words agree on
every list of sorted rows.  In particular they agree on each semistandard
tableau and on the empty tableau. -/
theorem KnuthEquivalent.fold_rowInsert_eq {u v : List ℕ} (h : KnuthEquivalent u v)
    (rows : List (List ℕ)) (hrows : RowsSorted rows) :
    u.foldl (fun rows x => rowInsert x rows) rows =
      v.foldl (fun rows x => rowInsert x rows) rows := by
  cases rows with
  | nil =>
      by_cases hu : u = []
      · have hv : v = [] := List.length_eq_zero_iff.mp (by
          simpa only [hu, List.length_nil] using (knuthEquivalent_length h).symm)
        simp only [hu, hv]
      · have hv : v ≠ [] := by
          intro hv
          apply hu
          apply List.length_eq_zero_iff.mp
          simpa only [hv, List.length_nil] using knuthEquivalent_length h
        obtain ⟨heq, hk⟩ := h.rowBumpWord [] List.sortedLE_nil
        have hlt := rowBumpWord_empty_bumped_length_lt hu
        rw [fold_rowInsert_nil_of_ne_nil u hu, fold_rowInsert_nil_of_ne_nil v hv, heq]
        congr 1
        exact hk.fold_rowInsert_eq [] (by simp [RowsSorted])
  | cons row rows =>
      have hr : row.SortedLE := hrows row (by simp)
      have hs : RowsSorted rows := fun r hr => hrows r (by simp [hr])
      obtain ⟨heq, hk⟩ := h.rowBumpWord row hr
      have hle := rowBumpWord_bumped_length_le row u
      rw [fold_rowInsert_cons, fold_rowInsert_cons, heq]
      congr 1
      exact hk.fold_rowInsert_eq rows hs
termination_by rows.length + u.length
decreasing_by
  all_goals simp_all only [List.length_nil, List.length_cons]
  all_goals omega

theorem KnuthEquivalent.insertionRows_eq {u v : List ℕ} (h : KnuthEquivalent u v) :
    u.foldl (fun rows x => rowInsert x rows) [] =
      v.foldl (fun rows x => rowInsert x rows) [] :=
  h.fold_rowInsert_eq [] (by simp [RowsSorted])

end HigherSpecht

end
end
end

/- EXACT RECOVERED SOURCE HigherSpecht.KnuthTableauReconstruction -/
section
section
/-!
# Reconstruction of a semistandard tableau from its row word

Inserting a sorted upper row into the row immediately below it replaces
that row by the upper row and bumps every old entry in its original order.
Iterating this identity proves reconstruction for the literal bottom-to-top
row word.  Combined with insertion invariance, it proves uniqueness of
the semistandard representative of every Knuth class.
-/

noncomputable section

open TauCeti

namespace HigherSpecht

set_option backward.isDefEq.respectTransparency false in
theorem rowBumpWord_of_isRowAbove (upper lower : List ℕ)
    (hs : upper.SortedLE) (habove : upper.IsRowAbove lower) :
    rowBumpWord lower upper = (upper, lower) := by
  induction upper generalizing lower with
  | nil =>
      have hl : lower = [] := List.length_eq_zero_iff.mp (by
        have h := habove.length_le
        simpa only [List.length_nil, Nat.le_zero] using h)
      subst lower
      rfl
  | cons a upper ih =>
      obtain ⟨ha, hu⟩ := List.sortedLE_cons.mp hs
      cases lower with
      | nil =>
          rw [rowBumpWord_cons, rowBump_nil,
            rowBumpWord_cons_of_le_all a [] upper ha,
            ih [] hu (List.isRowAbove_nil upper)]
          rfl
      | cons b lower =>
          have hab : a < b := habove.getElem_lt 0 (by simp) (by simp)
          have htail : upper.IsRowAbove lower := by
            refine ⟨by simpa only [List.length_cons, Nat.succ_le_succ_iff] using
              habove.length_le, ?_⟩
            intro j hu' hl'
            have h := habove.getElem_lt (j + 1)
              (by simp only [List.length_cons]; omega)
              (by simp only [List.length_cons]; omega)
            change upper[j] < lower[j] at h
            exact h
          rw [rowBumpWord_cons, rowBump_cons_of_lt lower hab,
            rowBumpWord_cons_of_le_all a lower upper ha, ih lower hu htail]
          rfl

/-- A sorted nonempty row above an actual tableau is recovered as its new
first row by ordinary Schensted insertion of that row's entries. -/
theorem fold_rowInsert_rowAbove (upper : List ℕ) (rows : List (List ℕ))
    (hu : upper ≠ []) (hs : upper.SortedLE) (hrows : rows.IsTableauRows)
    (habove : upper.IsRowAbove (rows.headD [])) :
    upper.foldl (fun rows x => rowInsert x rows) rows = upper :: rows := by
  induction rows generalizing upper with
  | nil =>
      rw [fold_rowInsert_nil_of_ne_nil upper hu,
        rowBumpWord_of_isRowAbove upper [] hs (List.isRowAbove_nil upper)]
      rfl
  | cons lower rows ih =>
      obtain ⟨hl, hls, hla, htail⟩ := List.isTableauRows_cons.mp hrows
      rw [fold_rowInsert_cons, rowBumpWord_of_isRowAbove upper lower hs habove]
      exact congrArg (List.cons upper) (ih lower hl hls htail hla)

theorem fold_rowInsert_rowWordRows (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) :
    (rowWordRows rows).foldl (fun rows x => rowInsert x rows) [] = rows := by
  induction rows with
  | nil => rfl
  | cons upper rows ih =>
      obtain ⟨hu, hs, habove, htail⟩ := List.isTableauRows_cons.mp hrows
      rw [rowWordRows_cons, List.foldl_append, ih htail]
      exact fold_rowInsert_rowAbove upper rows hu hs htail habove

/-- Genuine semistandard Knuth normal-form uniqueness, including repeated
letters and arbitrary finite shapes. -/
theorem tableauRows_eq_of_knuth_rowWord
    {rows rows' : List (List ℕ)} (hrows : rows.IsTableauRows)
    (hrows' : rows'.IsTableauRows)
    (h : KnuthEquivalent (rowWordRows rows) (rowWordRows rows')) : rows = rows' := by
  have hi := h.insertionRows_eq
  rwa [fold_rowInsert_rowWordRows rows hrows,
    fold_rowInsert_rowWordRows rows' hrows'] at hi

theorem knuth_rowWordRows_iff_eq
    {rows rows' : List (List ℕ)} (hrows : rows.IsTableauRows)
    (hrows' : rows'.IsTableauRows) :
    KnuthEquivalent (rowWordRows rows) (rowWordRows rows') ↔ rows = rows' := by
  constructor
  · exact tableauRows_eq_of_knuth_rowWord hrows hrows'
  · rintro rfl
    exact .refl _

end HigherSpecht

end
end
end

/- SOURCE COMPONENT MatchingMedianSelector -/

namespace FourPapers.Symmetric

instance instDecidableStrictMedian (x y z : ℕ) : Decidable (StrictMedian x y z) := by
  unfold StrictMedian
  infer_instance

/-- The paper's median rule: selector one swaps the first two distinguished
labels; selector two swaps the last two. -/
def matchingMedianSelector (k p q r : ℕ) : Fin 3 :=
  let a := modifiedPartner k k p
  let b := modifiedPartner k (k+1) q
  let c := modifiedPartner k (k+2) r
  if StrictMedian a b c then 0
  else if StrictMedian a c b then 1 else 2

theorem matchingMedianSelector_zero_of_fixed {k p q r : ℕ}
    (hp : p ≠ k) (hq : q ≠ k+1) (hr : r ≠ k+2)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h01 : p = k+1 ↔ q = k) (h02 : p = k+2 ↔ r = k)
    (h12 : q = k+2 ↔ r = k+1)
    (hfixed : (q < p ∧ p ≠ k+1) ↔ (r < q ∧ q ≠ k+2)) :
    matchingMedianSelector k p q r = 0 := by
  have ht : MatchingTriple k p q r := ⟨hp,hq,hr,h01,h02,h12,hpq,hpr,hqr⟩
  have hm := (matching_middle_median_iff ht).mpr hfixed
  simp only [matchingMedianSelector,hm,ite_true]

theorem matching_modified_partners_distinct {k p q r : ℕ}
    (h : MatchingTriple k p q r) :
    modifiedPartner k k p ≠ modifiedPartner k (k+1) q ∧
    modifiedPartner k k p ≠ modifiedPartner k (k+2) r ∧
    modifiedPartner k (k+1) q ≠ modifiedPartner k (k+2) r := by
  have hpq := h.ab_ne
  have hpr := h.ac_ne
  have hqr := h.bc_ne
  unfold modifiedPartner
  split_ifs <;> omega

@[simp] theorem matchingMedianSelector_eq_zero_iff (k p q r : ℕ) :
    matchingMedianSelector k p q r = 0 ↔
      StrictMedian (modifiedPartner k k p) (modifiedPartner k (k+1) q)
        (modifiedPartner k (k+2) r) := by
  dsimp only [matchingMedianSelector]
  split_ifs <;> simp_all

@[simp] theorem matchingMedianSelector_eq_one_iff (k p q r : ℕ) :
    matchingMedianSelector k p q r = 1 ↔
      StrictMedian (modifiedPartner k k p) (modifiedPartner k (k+2) r)
        (modifiedPartner k (k+1) q) := by
  dsimp only [matchingMedianSelector]
  split_ifs <;> simp_all [StrictMedian] <;> omega

 theorem matchingMedianSelector_eq_two_iff {k p q r : ℕ}
    (h : MatchingTriple k p q r) :
    matchingMedianSelector k p q r = 2 ↔
      StrictMedian (modifiedPartner k (k+1) q) (modifiedPartner k k p)
        (modifiedPartner k (k+2) r) := by
  obtain ⟨hab,hac,hbc⟩ := matching_modified_partners_distinct h
  dsimp only [matchingMedianSelector]
  split_ifs <;> simp_all [StrictMedian] <;> omega

end FourPapers.Symmetric

/- SOURCE COMPONENT SymmetricDual -/

/- COMPLETE SOURCE COMPONENT DualWordKnuth -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 1000

/-!
# Dual moves respect ordinary Knuth equivalence

Only the three consecutive distinguished labels are retained by `tripleFootprint`.
All other letters and both surrounding contexts remain arbitrary.  The finite
lemma below classifies the possible orders of these three labels; it imposes no
bound on a word, alphabet, tableau, matching or monomial.
-/

namespace FourPapers.Symmetric
open HigherSpecht

/-- Keep the three consecutive labels, with their positions and order. -/
def tripleTag (k x : ℕ) : Option (Fin 3) :=
  if x = k then some 0 else if x = k + 1 then some 1
  else if x = k + 2 then some 2 else none

def tripleFootprint (k : ℕ) (w : List ℕ) : List (Fin 3) := w.filterMap (tripleTag k)

def dualSelector (w : List (Fin 3)) : Fin 3 :=
  if w = [0, 2, 1] ∨ w = [1, 2, 0] then 1
  else if w = [1, 0, 2] ∨ w = [2, 0, 1] then 2 else 0

def dualLetter (k : ℕ) (s : Fin 3) : ℕ ≃ ℕ :=
  if s = 1 then Equiv.swap k (k + 1)
  else if s = 2 then Equiv.swap (k + 1) (k + 2) else Equiv.refl _

def dualWord (k : ℕ) (w : List ℕ) : List ℕ :=
  w.map (dualLetter k (dualSelector (tripleFootprint k w)))

theorem tripleTag_eq_some_iff (k x : ℕ) (d : Fin 3) :
    tripleTag k x = some d ↔ x = k + d.val := by
  fin_cases d <;> simp only [tripleTag, Fin.val_zero, Fin.val_one, Fin.val_ofNat]
  all_goals split_ifs <;> simp_all <;> omega

theorem tripleTag_eq_none_iff (k x : ℕ) :
    tripleTag k x = none ↔ x ≠ k ∧ x ≠ k + 1 ∧ x ≠ k + 2 := by
  unfold tripleTag
  split_ifs <;> simp_all

theorem tripleFootprint_nodup {k : ℕ} {w : List ℕ} (h : w.Nodup) :
    (tripleFootprint k w).Nodup := by
  apply List.Nodup.filterMap (f := tripleTag k) _ h
  intro a b d ha hb
  have ha' := (tripleTag_eq_some_iff k a d).mp (Option.mem_def.mp ha)
  have hb' := (tripleTag_eq_some_iff k b d).mp (Option.mem_def.mp hb)
  omega

theorem mem_tripleFootprint (k : ℕ) (w : List ℕ) (d : Fin 3) :
    d ∈ tripleFootprint k w ↔ k + d.val ∈ w := by
  simp only [tripleFootprint, List.mem_filterMap, tripleTag_eq_some_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro h; exact ⟨_, h, rfl⟩

theorem tripleFootprint_perm {k : ℕ} {w : List ℕ} (hn : w.Nodup)
    (hm : ∀ d : Fin 3, k + d.val ∈ w) :
    (tripleFootprint k w).Perm [0, 1, 2] := by
  apply (List.perm_ext_iff_of_nodup (tripleFootprint_nodup hn) (by decide)).mpr
  intro d
  rw [mem_tripleFootprint]
  have h := hm d
  fin_cases d <;> simp_all

/-- Every possible nonrepeating footprint, including incomplete contexts. -/
def shortTripleWord (i : Fin 16) : List (Fin 3) :=
  match i.val with
  | 0 => [] | 1 => [0] | 2 => [1] | 3 => [2]
  | 4 => [0,1] | 5 => [0,2] | 6 => [1,0] | 7 => [1,2]
  | 8 => [2,0] | 9 => [2,1]
  | 10 => [0,1,2] | 11 => [0,2,1] | 12 => [1,0,2]
  | 13 => [1,2,0] | 14 => [2,0,1] | _ => [2,1,0]

theorem exists_shortTripleWord (w : List (Fin 3)) (hn : w.Nodup) :
    ∃ i, shortTripleWord i = w := by
  have hl : w.length ≤ 3 := by simpa using hn.length_le_card
  cases w with
  | nil => exact ⟨0, rfl⟩
  | cons a w =>
    cases w with
    | nil => fin_cases a <;> first | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
    | cons b w =>
      cases w with
      | nil =>
        fin_cases a <;> fin_cases b <;> simp_all only [List.nodup_cons, List.mem_singleton, not_true_eq_false, false_and]
        all_goals first | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩ | exact ⟨9, rfl⟩
      | cons c w =>
        have hw : w = [] := List.length_eq_zero_iff.mp (by
          simp only [List.length_cons] at hl
          omega)
        subst w
        fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
        all_goals first | exact ⟨10, rfl⟩ | exact ⟨11, rfl⟩ | exact ⟨12, rfl⟩ | exact ⟨13, rfl⟩ | exact ⟨14, rfl⟩ | exact ⟨15, rfl⟩

def tripleAdmissible (a b c : Option (Fin 3)) : Prop :=
  (a.toList ++ b.toList ++ c.toList).Pairwise (· < ·) ∧
    (a ≠ none → c ≠ none → b ≠ none)

instance (a b c : Option (Fin 3)) : Decidable (tripleAdmissible a b c) := inferInstanceAs
  (Decidable ((a.toList ++ b.toList ++ c.toList).Pairwise (· < ·) ∧
    (a ≠ none → c ≠ none → b ≠ none)))

def safeTripleSwap (s : Fin 3) (a b c : Option (Fin 3)) : Prop :=
  (s = 1 → ¬(some 0 ∈ [a,b,c] ∧ some 1 ∈ [a,b,c])) ∧
  (s = 2 → ¬(some 1 ∈ [a,b,c] ∧ some 2 ∈ [a,b,c]))

instance (s : Fin 3) (a b c : Option (Fin 3)) : Decidable (safeTripleSwap s a b c) :=
  inferInstanceAs (Decidable ((s = 1 → ¬(some 0 ∈ [a,b,c] ∧ some 1 ∈ [a,b,c])) ∧
    (s = 2 → ¬(some 1 ∈ [a,b,c] ∧ some 2 ∈ [a,b,c]))))

/-- The complete local order-pattern classification for each Knuth relation.
`decide` constructs an ordinary kernel-checked proof over the finite three-letter
state space; the later lifting lemma restores arbitrary contexts and labels. -/
theorem dualSelector_knuth_patterns :
    ∀ (left : Bool) (l r : Fin 16) (a b c : Option (Fin 3)),
      tripleAdmissible a b c →
      let p := shortTripleWord l
      let q := shortTripleWord r
      let u := if left then [b,a,c] else [a,c,b]
      let v := if left then [b,c,a] else [c,a,b]
      (p ++ u.filterMap id ++ q).Perm [0,1,2] →
      (dualSelector (p ++ u.filterMap id ++ q) = dualSelector (p ++ v.filterMap id ++ q) ∧
        safeTripleSwap (dualSelector (p ++ u.filterMap id ++ q)) a b c) ∨
      (a = some 0 ∧ b = some 1 ∧ c = some 2 ∧ p = [] ∧ q = []) := by
  intro left l r
  cases left <;> fin_cases l <;> fin_cases r <;> decide +kernel

theorem tripleAdmissible_tags {k a b c : ℕ} (hab : a < b) (hbc : b < c) :
    tripleAdmissible (tripleTag k a) (tripleTag k b) (tripleTag k c) := by
  constructor
  · have hp : ([a,b,c] : List ℕ).Pairwise (· < ·) := by simp [hab, hbc, hab.trans hbc]
    have h := hp.filterMap (tripleTag k) (fun x y hxy d hd e he => by
      have hx := (tripleTag_eq_some_iff k x d).mp hd
      have hy := (tripleTag_eq_some_iff k y e).mp he
      change d.val < e.val
      omega)
    cases ha : tripleTag k a <;> cases hb : tripleTag k b <;> cases hc : tripleTag k c <;>
      simpa [ha,hb,hc] using h
  · intro ha hc hb
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp ha
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hc
    have hx := (tripleTag_eq_some_iff k a d).mp hd
    have hy := (tripleTag_eq_some_iff k c e).mp he
    have hb' := (tripleTag_eq_none_iff k b).mp hb
    have := d.isLt
    have := e.isLt
    omega

theorem dualLetter_eq_self_of_none {k x : ℕ} (s : Fin 3)
    (h : tripleTag k x = none) : dualLetter k s x = x := by
  obtain ⟨h0,h1,h2⟩ := (tripleTag_eq_none_iff k x).mp h
  unfold dualLetter
  split_ifs <;> simp [Equiv.swap_apply_of_ne_of_ne, h0, h1, h2]

theorem map_dualLetter_eq_self {k : ℕ} {w : List ℕ}
    (h : tripleFootprint k w = []) (s : Fin 3) : w.map (dualLetter k s) = w := by
  calc
    w.map (dualLetter k s) = w.map id := by
      apply List.map_congr_left
      intro x hx
      exact dualLetter_eq_self_of_none s (List.forall_none_of_filterMap_eq_nil h x hx)
    _ = w := List.map_id w

/-- A swap can reverse only its two adjacent labels. -/

theorem swap_adjacent_lt {p x y : ℕ} (hxy : x < y)
    (h : ¬(x = p ∧ y = p + 1)) :
    Equiv.swap p (p + 1) x < Equiv.swap p (p + 1) y := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

theorem dualLetter_triple_lt {k a b c : ℕ} {s : Fin 3}
    (hab : a < b) (hbc : b < c)
    (hs : safeTripleSwap s (tripleTag k a) (tripleTag k b) (tripleTag k c)) :
    dualLetter k s a < dualLetter k s b ∧ dualLetter k s b < dualLetter k s c := by
  unfold dualLetter
  split_ifs with h1 h2
  · have h := hs.1 h1
    constructor <;> apply swap_adjacent_lt (by omega)
    all_goals rintro ⟨ha,hb⟩; apply h; simp [ha,hb,tripleTag,Nat.add_assoc]
  · have h := hs.2 h2
    constructor <;> apply swap_adjacent_lt (by omega)
    all_goals rintro ⟨ha,hb⟩; apply h; simp [ha,hb,tripleTag,Nat.add_assoc]
  · exact ⟨hab,hbc⟩

/-- Prefixes or suffixes containing none of the three labels commute with a dual move. -/
theorem dualWord_append_outside {k : ℕ} (w v : List ℕ)
    (h : tripleFootprint k v = []) : dualWord k (w ++ v) = dualWord k w ++ v := by
  change v.filterMap (tripleTag k) = [] at h
  simp only [dualWord, tripleFootprint, List.filterMap_append, h, List.append_nil,
    List.map_append]
  rw [map_dualLetter_eq_self h]

@[simp] theorem tripleFootprint_append (k : ℕ) (u v : List ℕ) :
    tripleFootprint k (u ++ v) = tripleFootprint k u ++ tripleFootprint k v :=
  List.filterMap_append

@[simp] theorem tripleTag_self (k : ℕ) : tripleTag k k = some 0 := by simp [tripleTag]
@[simp] theorem tripleTag_succ (k : ℕ) : tripleTag k (k+1) = some 1 := by simp [tripleTag]
@[simp] theorem tripleTag_add_two (k : ℕ) : tripleTag k (k+2) = some 2 := by simp [tripleTag]

def knuthBefore (left : Bool) (a b c : ℕ) : List ℕ :=
  if left then [b,a,c] else [a,c,b]

def knuthAfter (left : Bool) (a b c : ℕ) : List ℕ :=
  if left then [b,c,a] else [c,a,b]

theorem knuthTriple (left : Bool) {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    KnuthEquivalent (knuthBefore left a b c) (knuthAfter left a b c) := by
  cases left
  · exact .right hab.le hbc
  · exact .left hab hbc.le

/-- Dual equivalence commutes with either elementary Knuth move, with arbitrary
surrounding words and arbitrary values of the other letters. -/
theorem dualWord_knuth_step (left : Bool) (k a b c : ℕ) (l r : List ℕ)
    (hab : a < b) (hbc : b < c)
    (hn : (l ++ knuthBefore left a b c ++ r).Nodup)
    (hm : ∀ d : Fin 3, k + d.val ∈ l ++ knuthBefore left a b c ++ r) :
    KnuthEquivalent (dualWord k (l ++ knuthBefore left a b c ++ r))
      (dualWord k (l ++ knuthAfter left a b c ++ r)) := by
  have hln := (List.nodup_append.mp (List.nodup_append.mp hn).1).1
  have hrn := (List.nodup_append.mp hn).2.1
  obtain ⟨li,hli⟩ := exists_shortTripleWord _ (tripleFootprint_nodup (k := k) hln)
  obtain ⟨ri,hri⟩ := exists_shortTripleWord _ (tripleFootprint_nodup (k := k) hrn)
  have hp := tripleFootprint_perm hn hm
  have hfU : tripleFootprint k (l ++ knuthBefore left a b c ++ r) =
      tripleFootprint k l ++
        (if left then [tripleTag k b,tripleTag k a,tripleTag k c]
          else [tripleTag k a,tripleTag k c,tripleTag k b]).filterMap id ++
        tripleFootprint k r := by
    cases left <;> simp only [knuthBefore, Bool.false_eq_true, if_false, if_true,
      tripleFootprint_append] <;> rfl
  have hfV : tripleFootprint k (l ++ knuthAfter left a b c ++ r) =
      tripleFootprint k l ++
        (if left then [tripleTag k b,tripleTag k c,tripleTag k a]
          else [tripleTag k c,tripleTag k a,tripleTag k b]).filterMap id ++
        tripleFootprint k r := by
    cases left <;> simp only [knuthAfter, Bool.false_eq_true, if_false, if_true,
      tripleFootprint_append] <;> rfl
  have hclass := dualSelector_knuth_patterns left li ri
    (tripleTag k a) (tripleTag k b) (tripleTag k c) (tripleAdmissible_tags hab hbc)
  dsimp only at hclass
  rw [hli,hri,←hfU,←hfV] at hclass
  rcases hclass hp with hs | hex
  · have hi := dualLetter_triple_lt hab hbc hs.2
    unfold dualWord
    rw [← hs.1]
    cases left
    · simpa only [knuthBefore,knuthAfter,Bool.false_eq_true,if_false,List.map_append,
        List.map_cons,List.map_nil] using
        (KnuthEquivalent.right hi.1.le hi.2).append
          (l.map (dualLetter k (dualSelector (tripleFootprint k (l ++ knuthBefore false a b c ++ r)))))
          (r.map (dualLetter k (dualSelector (tripleFootprint k (l ++ knuthBefore false a b c ++ r)))))
    · simpa only [knuthBefore,knuthAfter,if_true,List.map_append,List.map_cons,List.map_nil] using
        (KnuthEquivalent.left hi.1 hi.2.le).append
          (l.map (dualLetter k (dualSelector (tripleFootprint k (l ++ knuthBefore true a b c ++ r)))))
          (r.map (dualLetter k (dualSelector (tripleFootprint k (l ++ knuthBefore true a b c ++ r)))))
  · obtain ⟨ha,hb,hc,hl,hr⟩ := hex
    have ha' : a = k := by simpa using (tripleTag_eq_some_iff k a 0).mp ha
    have hb' : b = k+1 := by simpa using (tripleTag_eq_some_iff k b 1).mp hb
    have hc' : c = k+2 := by simpa using (tripleTag_eq_some_iff k c 2).mp hc
    subst a; subst b; subst c
    have hl1 := map_dualLetter_eq_self hl (1 : Fin 3)
    have hl2 := map_dualLetter_eq_self hl (2 : Fin 3)
    have hr1 := map_dualLetter_eq_self hr (1 : Fin 3)
    have hr2 := map_dualLetter_eq_self hr (2 : Fin 3)
    have h01 : k < k+1 := by omega
    have h12 : k+1 < k+2 := by omega
    unfold dualWord
    rw [hfU,hfV,hl,hr]
    simp only [List.nil_append,List.append_nil,tripleTag_self,tripleTag_succ,
      tripleTag_add_two]
    cases left
    · change KnuthEquivalent
        ((l ++ [k,k+2,k+1] ++ r).map (dualLetter k 1))
        ((l ++ [k+2,k,k+1] ++ r).map (dualLetter k 2))
      simp only [List.map_append,hl1,hr1,hl2,hr2]
      have h := (KnuthEquivalent.left h01 h12.le).symm.append l r
      simpa [dualLetter,Equiv.swap_apply_def,Nat.add_assoc] using h
    · change KnuthEquivalent
        ((l ++ [k+1,k,k+2] ++ r).map (dualLetter k 2))
        ((l ++ [k+1,k+2,k] ++ r).map (dualLetter k 1))
      simp only [List.map_append,hl1,hr1,hl2,hr2]
      have h := (KnuthEquivalent.right h01.le h12).symm.append l r
      simpa [dualLetter,Equiv.swap_apply_def,Nat.add_assoc] using h

/-- Knuth equivalence preserves every letter occurrence. -/
theorem knuthEquivalent_perm {u v : List ℕ} (h : KnuthEquivalent u v) : u.Perm v := by
  induction h with
  | refl u => exact .refl _
  | symm h ih => exact ih.symm
  | trans h g ih ih' => exact ih.trans ih'
  | append l r h ih => exact (ih.append_left l).append_right r
  | left hab hbc => exact (List.Perm.swap _ _ []).cons _
  | right hab hbc => exact List.Perm.swap _ _ [_]

/-- The three-label dual transformation respects an arbitrary finite sequence of
Knuth transformations, including transformations inside unbounded contexts. -/
theorem dualWord_knuthEquivalent_context {k : ℕ} {u v : List ℕ}
    (h : KnuthEquivalent u v) :
    ∀ l r : List ℕ, (l ++ u ++ r).Nodup →
      (∀ d : Fin 3, k + d.val ∈ l ++ u ++ r) →
      KnuthEquivalent (dualWord k (l ++ u ++ r)) (dualWord k (l ++ v ++ r)) := by
  induction h with
  | refl u => intro l r hn hm; exact .refl _
  | @symm u v h ih =>
    intro l r hn hm
    have hp := ((knuthEquivalent_perm h).append_left l).append_right r
    exact (ih l r (hp.symm.nodup hn) (fun d => hp.mem_iff.mpr (hm d))).symm
  | @trans u v w h g ih ih' =>
    intro l r hn hm
    have hp := ((knuthEquivalent_perm h).append_left l).append_right r
    exact (ih l r hn hm).trans
      (ih' l r (hp.nodup hn) (fun d => hp.mem_iff.mp (hm d)))
  | @append u v p q h ih =>
    intro l r hn hm
    have hn' : ((l ++ p) ++ u ++ (q ++ r)).Nodup := by
      simpa only [List.append_assoc] using hn
    have hm' : ∀ d : Fin 3, k + d.val ∈ (l ++ p) ++ u ++ (q ++ r) := by
      simpa only [List.append_assoc] using hm
    simpa only [List.append_assoc] using ih (l ++ p) (q ++ r) hn' hm'
  | @left a b c hab hbc =>
    intro l r hn hm
    have hn' := (List.nodup_append.mp (List.nodup_append.mp hn).1).2.1
    have hne : b ≠ c := by
      intro heq
      exact (List.nodup_cons.mp hn').1 (by simp [heq])
    exact dualWord_knuth_step true k a b c l r hab (lt_of_le_of_ne hbc hne) hn hm
  | @right a b c hab hbc =>
    intro l r hn hm
    have hn' := (List.nodup_append.mp (List.nodup_append.mp hn).1).2.1
    have hne : a ≠ b := by
      intro heq
      exact (List.nodup_cons.mp hn').1 (by simp [heq])
    exact dualWord_knuth_step false k a b c l r (lt_of_le_of_ne hab hne) hbc hn hm

theorem dualWord_knuthEquivalent {k : ℕ} {u v : List ℕ}
    (h : KnuthEquivalent u v) (hn : u.Nodup) (hm : ∀ d : Fin 3, k + d.val ∈ u) :
    KnuthEquivalent (dualWord k u) (dualWord k v) := by
  simpa only [List.nil_append,List.append_nil] using
    dualWord_knuthEquivalent_context h [] [] (by simpa) (by simpa)

/-- Consequently the actual Schensted insertion tableaux of the two transformed
words agree. This is derived from the checked insertion-invariance theorem. -/
theorem insertionRows_dualWord_eq {k : ℕ} {u v : List ℕ}
    (h : KnuthEquivalent u v) (hn : u.Nodup) (hm : ∀ d : Fin 3, k + d.val ∈ u) :
    (dualWord k u).foldl (fun rows x => TauCeti.rowInsert x rows) [] =
      (dualWord k v).foldl (fun rows x => TauCeti.rowInsert x rows) [] :=
  (dualWord_knuthEquivalent h hn hm).insertionRows_eq

end FourPapers.Symmetric


/- COMPLETE SOURCE COMPONENT DualTableau -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

/- SOURCE TauCeti/Combinatorics/Young/Schensted/Shape.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The shape of a list of tableau rows

A list of rows satisfying `List.IsTableauRows` has weakly decreasing positive row lengths, so it
determines a Young diagram `List.tableauShape`. Its row lengths are the lengths of the rows
(`List.rowLens_tableauShape`) and its number of cells is the number of entries
(`List.card_tableauShape`).
-/

namespace List

/-- The Young diagram whose row lengths are the lengths of a semistandard list of tableau rows. -/
def tableauShape {α : Type*} [Preorder α]
    (rows : List (List α)) (hrows : rows.IsTableauRows) : YoungDiagram :=
  YoungDiagram.ofRowLens (rows.map length) hrows.sortedGE_map_length

/-- The row lengths of the shape inferred from tableau rows are the lengths of those rows. -/
@[simp]
theorem rowLens_tableauShape {α : Type*} [Preorder α]
    (rows : List (List α)) (hrows : rows.IsTableauRows) :
    (tableauShape rows hrows).rowLens = rows.map length := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro k hk
  obtain ⟨row, hrow, rfl⟩ := mem_map.mp hk
  exact List.length_pos_iff.mpr fun hnil => hrows.nil_notMem (hnil ▸ hrow)

/-- The number of cells in the shape inferred from tableau rows is the length of their
flattening. -/
@[simp]
theorem card_tableauShape {α : Type*} [Preorder α]
    (rows : List (List α)) (hrows : rows.IsTableauRows) :
    (tableauShape rows hrows).card = rows.flatten.length := by
  rw [← YoungDiagram.sum_rowLens_eq_card, rowLens_tableauShape, length_flatten]

end List


/- SOURCE TauCeti/Combinatorics/Young/StandardTableau/Rows.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Standard tableaux as lists of rows

`StandardYoungTableau.toRows` lists the entries of a standard tableau from left to right in each
row, with the rows ordered from top to bottom. These rows satisfy `List.IsTableauRows`, have the
prescribed shape, and contain every label exactly once. Conversely, these three properties
characterize the lists arising from standard tableaux, giving `StandardYoungTableau.rowsEquiv`.

This connects bijective cell labelings with the list representation used by Schensted insertion.
In particular, an insertion tableau containing each label once can be read as a standard tableau
without changing its entries or its shape. Empty shapes are included.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Sections 1.1 and 4.1.
* B. E. Sagan, *The Symmetric Group*, second edition, Springer GTM 203 (2001), Section 3.1.
-/

namespace TauCeti.StandardYoungTableau

open List

variable {μ : YoungDiagram}

/-- The rows of a standard tableau, listed from top to bottom and left to right. -/
def toRows (T : StandardYoungTableau μ) : List (List (Fin μ.card)) :=
  ofFn fun i : Fin (μ.colLen 0) => ofFn fun j : Fin (μ.rowLen i) =>
    T ⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩

/-- The row representation enumerates each row in increasing column order. -/
theorem toRows_def (T : StandardYoungTableau μ) :
    T.toRows = ofFn fun i : Fin (μ.colLen 0) => ofFn fun j : Fin (μ.rowLen i) =>
      T ⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩ := (rfl)

/-- The number of rows is the height of the first column. -/
@[simp]
theorem length_toRows (T : StandardYoungTableau μ) : T.toRows.length = μ.colLen 0 := by
  simp [toRows]

/-- The row lengths of a standard tableau agree with its shape. -/
@[simp]
theorem map_length_toRows (T : StandardYoungTableau μ) : T.toRows.map length = μ.rowLens := by
  simp [toRows, YoungDiagram.rowLens, ← ofFn_getElem_eq_map]

/-- Reading a row in its natural column order recovers its entries. -/
@[simp]
theorem getElem_toRows (T : StandardYoungTableau μ) (i : ℕ) (hi : i < T.toRows.length) :
    T.toRows[i] = ofFn fun j : Fin (μ.rowLen i) =>
      T ⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩ := by
  simp [toRows]

/-- Reading a row beyond the shape gives length zero; otherwise it has the shape's row length. -/
@[simp]
theorem length_getD_getElem?_toRows (T : StandardYoungTableau μ) (i : ℕ) :
    (T.toRows[i]?.getD []).length = μ.rowLen i := by
  rw [← getD_eq_getElem?_getD, ← getD_map T.toRows [] length, map_length_toRows]
  exact YoungDiagram.matching_getD_rowLens μ i

/-- Looking up the coordinates of a cell in the row representation recovers its label. -/
@[simp]
theorem getElem?_getD_getElem?_toRows (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    (T.toRows[c.1.1]?.getD [])[c.1.2]? = some (T c) := by
  have hi : c.1.1 < T.toRows.length := by simpa using μ.lt_colLen_zero_of_mem c.2
  have hj : c.1.2 < μ.rowLen c.1.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.2
  rw [getElem?_eq_getElem hi]
  simp [hj]

/-- A standard tableau's row representation is a semistandard tableau. -/
theorem isTableauRows_toRows (T : StandardYoungTableau μ) : T.toRows.IsTableauRows := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [toRows, mem_ofFn]
    rintro ⟨i, hi⟩
    have hpos : 0 < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)
    have := congrArg length hi
    simp only [length_ofFn, length_nil] at this
    omega
  · simp only [toRows, forall_mem_ofFn_iff]
    intro i
    apply sortedLE_iff_pairwise.mpr
    apply pairwise_ofFn.mpr
    intro j k hjk
    exact (T.row_strict (Fin.lt_def.mp hjk)
      (YoungDiagram.mem_iff_lt_rowLen.mpr k.isLt)).le
  · apply Pairwise.isChain
    simp only [toRows, pairwise_ofFn]
    intro i k hik
    refine ⟨by simpa using μ.rowLen_anti i k (Fin.le_def.mp hik.le), ?_⟩
    intro j hu hl
    simp only [length_ofFn] at hu hl
    simpa using T.col_strict (Fin.lt_def.mp hik) (YoungDiagram.mem_iff_lt_rowLen.mpr hl)

/-- The rows contain each label exactly once. -/
theorem flatten_toRows_perm (T : StandardYoungTableau μ) :
    T.toRows.flatten.Perm (finRange μ.card) := by
  have hmem (x : Fin μ.card) : x ∈ T.toRows.flatten := by
    obtain ⟨c, rfl⟩ := T.surjective x
    have hj : c.1.2 < μ.rowLen c.1.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.2
    simp only [toRows, mem_flatten, mem_ofFn]
    refine ⟨_, ⟨⟨c.1.1, μ.lt_colLen_zero_of_mem c.2⟩, rfl⟩, ?_⟩
    exact mem_ofFn.mpr ⟨⟨c.1.2, hj⟩, rfl⟩
  have hlen : T.toRows.flatten.length = μ.card := by
    rw [length_flatten, map_length_toRows, YoungDiagram.sum_rowLens_eq_card]
  exact ((subperm_of_subset (nodup_finRange μ.card) (fun x _ => hmem x)).perm_of_length_le
    (by simp [hlen])).symm

/-- The first row of the row representation containing a label is the row of that label. -/
@[simp]
theorem findIdx?_mem_toRows (T : StandardYoungTableau μ) (l : Fin μ.card) :
    T.toRows.findIdx? (fun row => l ∈ row) = some (YoungTableau.rowIndex T.toTableau l) := by
  obtain ⟨c, rfl⟩ := T.surjective l
  have hmem (i : ℕ) (hi : i < T.toRows.length) : T c ∈ T.toRows[i] ↔ i = c.1.1 := by
    rw [getElem_toRows, mem_ofFn]
    constructor
    · rintro ⟨j, hj⟩
      exact congrArg (fun d : ↥μ.cells => d.1.1) (T.injective hj)
    · rintro rfl
      exact ⟨⟨c.1.2, YoungDiagram.mem_iff_lt_rowLen.mp c.2⟩, rfl⟩
  have hlt : c.1.1 < T.toRows.length := by simpa using μ.lt_colLen_zero_of_mem c.2
  rw [findIdx?_eq_some_iff_getElem, show YoungTableau.rowIndex T.toTableau (T c) = c.1.1 from
    YoungTableau.rowIndex_apply T.toTableau c]
  exact ⟨hlt, by simpa using (hmem _ hlt).mpr rfl,
    fun j hj => by
      rw [decide_eq_true_iff, hmem j (hj.trans hlt)]
      omega⟩

/-- The row representation determines a standard tableau. -/
theorem toRows_injective : Function.Injective (toRows (μ := μ)) := by
  intro T U h
  apply ext
  intro c
  have heq := congrArg (fun rows => (rows[c.1.1]?.getD [])[c.1.2]?) h
  simpa only [getElem?_getD_getElem?_toRows T c, getElem?_getD_getElem?_toRows U c,
    Option.some.injEq] using heq

/-! ### Decoding a list of rows -/

section ofRows

variable {rows : List (List (Fin μ.card))}

/-- A list of rows of shape `μ` has a row for the row of every cell of `μ`. -/
theorem lt_length_of_mem (hshape : rows.map length = μ.rowLens) {i j : ℕ}
    (h : (i, j) ∈ μ) : i < rows.length := by
  simpa [← length_map (f := length), hshape] using μ.lt_colLen_zero_of_mem h

/-- In a list of rows of shape `μ`, each row has the length of the corresponding row of `μ`. -/
theorem length_getElem_of_map_length (hshape : rows.map length = μ.rowLens) {i : ℕ}
    (hi : i < rows.length) : rows[i].length = μ.rowLen i := by
  rw [← YoungDiagram.matching_getD_rowLens, ← hshape, ← getD_eq_getElem?_getD, getD_eq_getElem _ _ (by simpa using hi),
    getElem_map]

/-- In a list of rows of shape `μ`, the row of a cell of `μ` is long enough to hold it. -/
theorem lt_length_getElem_of_mem (hshape : rows.map length = μ.rowLens) {i j : ℕ}
    (h : (i, j) ∈ μ) : j < (rows[i]'(lt_length_of_mem hshape h)).length := by
  rw [length_getElem_of_map_length hshape]
  exact YoungDiagram.mem_iff_lt_rowLen.mp h

/-- The cell labeling read off a list of rows of shape `μ`. -/
def ofRowsFun (hshape : rows.map length = μ.rowLens) (c : ↥μ.cells) : Fin μ.card :=
  (rows[c.1.1]'(lt_length_of_mem hshape c.2))[c.1.2]'(lt_length_getElem_of_mem hshape c.2)

/-- Full content makes the cell labeling surjective. -/
theorem ofRowsFun_surjective (hshape : rows.map length = μ.rowLens)
    (hcontent : rows.flatten.Perm (finRange μ.card)) : Function.Surjective (ofRowsFun hshape) := by
  intro x
  obtain ⟨row, hr, hx⟩ := mem_flatten.mp (hcontent.symm.subset (mem_finRange x))
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem hr
  obtain ⟨j, hj, rfl⟩ := getElem_of_mem hx
  rw [length_getElem_of_map_length hshape hi] at hj
  exact ⟨⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr hj⟩, rfl⟩

/-- The content condition excludes repeated labels, strengthening weak row order. -/
theorem ofRowsFun_row_strict (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) (hcontent : rows.flatten.Perm (finRange μ.card))
    {i j k : ℕ} (hjk : j < k) (hcell : (i, k) ∈ μ) :
    ofRowsFun hshape ⟨(i, j), μ.up_left_mem le_rfl hjk.le hcell⟩ <
      ofRowsFun hshape ⟨(i, k), hcell⟩ := by
  have hi := lt_length_of_mem hshape hcell
  have hsorted := (htab.sortedLE _ (getElem_mem hi)).sortedLT_of_nodup
    ((nodup_flatten.mp (hcontent.nodup_iff.mpr (nodup_finRange _))).1 _ (getElem_mem hi))
  exact hsorted.strictMono_get
    (a := ⟨j, hjk.trans (lt_length_getElem_of_mem hshape hcell)⟩)
    (b := ⟨k, lt_length_getElem_of_mem hshape hcell⟩) hjk

/-- Transitivity of `IsRowAbove` compares any two rows, not just adjacent rows. -/
theorem ofRowsFun_col_strict (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) {i k j : ℕ} (hik : i < k) (hcell : (k, j) ∈ μ) :
    ofRowsFun hshape ⟨(i, j), μ.up_left_mem hik.le le_rfl hcell⟩ <
      ofRowsFun hshape ⟨(k, j), hcell⟩ := by
  have hk := lt_length_of_mem hshape hcell
  have hj := lt_length_getElem_of_mem hshape hcell
  have habove := (pairwise_iff_getElem.mp htab.isChain.pairwise) i k (hik.trans hk) hk hik
  exact habove.getElem_lt j (hj.trans_le habove.length_le) hj

/-- The standard tableau whose rows are a semistandard list of rows of shape `μ` containing
every label exactly once. -/
noncomputable def ofRows (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) (hcontent : rows.flatten.Perm (finRange μ.card)) :
    StandardYoungTableau μ where
  toTableau := Equiv.ofBijective (ofRowsFun hshape)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨ofRowsFun_surjective hshape hcontent, by simp⟩)
  row_strict' := ofRowsFun_row_strict htab hshape hcontent
  col_strict' := ofRowsFun_col_strict htab hshape

/-- Enumerating the decoded cells recovers each original row entry. -/
theorem toRows_ofRows (htab : rows.IsTableauRows)
    (hshape : rows.map length = μ.rowLens) (hcontent : rows.flatten.Perm (finRange μ.card)) :
    (ofRows htab hshape hcontent).toRows = rows := by
  have hlen : rows.length = μ.colLen 0 := by simpa using congrArg length hshape
  refine ext_getElem (by simp [hlen]) fun i hi hi' => ?_
  rw [getElem_toRows]
  exact ext_getElem (by simp [length_getElem_of_map_length hshape hi']) fun j _ _ => by
    rw [List.getElem_ofFn]
    rfl

end ofRows

/-- A list of rows comes from a standard tableau exactly when it is a semistandard tableau
of the given shape containing each label exactly once. -/
theorem exists_toRows_eq_iff {rows : List (List (Fin μ.card))} :
    (∃ T : StandardYoungTableau μ, T.toRows = rows) ↔
      rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
        rows.flatten.Perm (finRange μ.card) := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.isTableauRows_toRows, T.map_length_toRows, T.flatten_toRows_perm⟩
  · rintro ⟨htab, hshape, hcontent⟩
    exact ⟨ofRows htab hshape hcontent, toRows_ofRows htab hshape hcontent⟩

/-- Standard tableaux of shape `μ` correspond to semistandard lists of rows of that shape
containing every label exactly once. -/
noncomputable def rowsEquiv (μ : YoungDiagram) :
    StandardYoungTableau μ ≃ {rows : List (List (Fin μ.card)) //
      rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
        rows.flatten.Perm (finRange μ.card)} :=
  Equiv.ofBijective
    (fun T => ⟨T.toRows, exists_toRows_eq_iff.mp ⟨T, rfl⟩⟩)
    ⟨fun _ _ h => toRows_injective (congrArg Subtype.val h), fun rows =>
      (exists_toRows_eq_iff.mpr rows.2).imp fun _ h => Subtype.ext h⟩

/-- The forward row equivalence lists the entries of the tableau by rows. -/
@[simp]
theorem rowsEquiv_apply_coe (T : StandardYoungTableau μ) :
    (rowsEquiv μ T : List (List (Fin μ.card))) = T.toRows := (rfl)

/-- Decoding a valid row list and reading it back recovers that list. -/
@[simp]
theorem toRows_rowsEquiv_symm (rows : {rows : List (List (Fin μ.card)) //
    rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
      rows.flatten.Perm (finRange μ.card)}) :
    ((rowsEquiv μ).symm rows).toRows = rows.val :=
  congrArg Subtype.val ((rowsEquiv μ).apply_symm_apply rows)

/-- The tableau decoded from a valid row list labels each cell by the entry in its row and
column. -/
@[simp]
theorem rowsEquiv_symm_apply (rows : {rows : List (List (Fin μ.card)) //
    rows.IsTableauRows ∧ rows.map length = μ.rowLens ∧
      rows.flatten.Perm (finRange μ.card)}) (c : ↥μ.cells) :
    (rowsEquiv μ).symm rows c = (rows.val[c.1.1]'(by
      simpa [← length_map (f := length), rows.2.2.1] using μ.lt_colLen_zero_of_mem c.2))[c.1.2]'(by
      rw [← getElem_map length, getElem_of_eq rows.2.2.1, YoungDiagram.get_rowLens]
      · exact YoungDiagram.mem_iff_lt_rowLen.mp c.2
      · simpa [rows.2.2.1] using μ.lt_colLen_zero_of_mem c.2) := by
  have key (rs : List (List (Fin μ.card))) (h : ((rowsEquiv μ).symm rows).toRows = rs) h₁ h₂ :
      (rowsEquiv μ).symm rows c = (rs[c.1.1]'h₁)[c.1.2]'h₂ := by
    subst h
    simp only [getElem_toRows, List.getElem_ofFn]
  exact key _ (toRows_rowsEquiv_symm rows) _ _

end TauCeti.StandardYoungTableau

noncomputable section
open Finset TauCeti Function
namespace HigherSpecht

/- SOURCE HigherSpecht.Catabolism:rowReadingCells -/
/-- Top-to-bottom, left-to-right row reading in the paper's French convention.
The row coordinate itself is still the standard zero-based Young-diagram
coordinate, so larger row coordinates are read first. -/
def rowReadingCells (μ : YoungDiagram) : List ↥μ.cells :=
  μ.cells.attach.toList.mergeSort fun c d =>
    decide (d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 ≤ d.val.2))



/- SOURCE HigherSpecht.ReadingWords:rowSlice0 -/
def cellsInRow (μ : YoungDiagram) (r cut : ℕ) : List ↥μ.cells :=
  List.ofFn fun c : Fin (min cut (μ.rowLen r)) =>
    ⟨(r, c.val), YoungDiagram.mem_iff_lt_rowLen.mpr (lt_of_lt_of_le c.isLt (min_le_right _ _))⟩

def rowsOfCells (μ : YoungDiagram) (cut : ℕ) : List (List ↥μ.cells) :=
  List.ofFn fun r : Fin (μ.colLen 0) => cellsInRow μ r cut



/- SOURCE HigherSpecht.ReadingWords:rowSlice1 -/
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



/- SOURCE HigherSpecht.ReadingWords:rowSlice2 -/
 theorem mem_rowsOfCells_flatten (μ : YoungDiagram) (cut : ℕ) (c : ↥μ.cells) :
    c ∈ (rowsOfCells μ cut).flatten ↔ c.val.2 < cut := by
  simp only [rowsOfCells, List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨row, ⟨r, rfl⟩, hc⟩
    exact ((mem_cellsInRow μ _ _ c).mp hc).2
  · intro hc
    let r : Fin (μ.colLen 0) := ⟨c.val.1, YoungDiagram.lt_colLen_zero_of_mem c.property⟩
    exact ⟨cellsInRow μ r cut, ⟨r, rfl⟩, (mem_cellsInRow μ _ _ c).mpr ⟨rfl, hc⟩⟩



/- SOURCE HigherSpecht.ReadingWords:rowSlice3 -/
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



/- SOURCE HigherSpecht.ReadingWords:rowSlice4 -/
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



/- SOURCE HigherSpecht.ReadingWords:rowSlice5 -/
def fillingRows {μ : YoungDiagram} (f : ↥μ.cells → ℕ) (cut : ℕ) : List (List ℕ) :=
  (rowsOfCells μ cut).map (List.map f)



/- SOURCE HigherSpecht.EligibleIndexCountKnuth:tableauValueWord -/
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



/- SOURCE HigherSpecht.CatTermination:pair_sublist_of_pairwise -/
lemma pair_sublist_of_pairwise {α : Type*} {rel : α → α → Prop} {w : List α}
    (hw : w.Pairwise rel) {a b : α} (ha : a ∈ w) (hb : b ∈ w)
    (hne : a ≠ b) (hba : ¬ rel b a) : [a, b].Sublist w := by
  induction w with
  | nil => simp at ha
  | cons c w ih =>
    obtain ⟨hc, htail⟩ := List.pairwise_cons.mp hw
    rcases List.mem_cons.mp ha with hac | haw
    · subst c
      have hb' : b ∈ w := (List.mem_cons.mp hb).resolve_left hne.symm
      exact (List.singleton_sublist.mpr hb').cons_cons a
    · rcases List.mem_cons.mp hb with hbc | hbw
      · subst c
        exact (hba (hc _ haw)).elim
      · exact (ih htail haw hbw).cons c

end HigherSpecht
end

/- SOURCE FourPapers.Symmetric.DualTableauGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FourPapers.Symmetric
open TauCeti TauCeti.StandardYoungTableau

variable {μ : YoungDiagram}

theorem tableauEntry_row_lt (T : StandardYoungTableau μ) {i j l : ℕ}
    (hjl : j < l) (hc : (i,l) ∈ μ) :
    tableauEntry T (i,j) < tableauEntry T (i,l) := by
  rw [tableauEntry_of_mem T (μ.up_left_mem le_rfl hjl.le hc),tableauEntry_of_mem T hc]
  exact T.row_strict hjl hc

theorem tableauEntry_col_lt (T : StandardYoungTableau μ) {i j l : ℕ}
    (hij : i < j) (hc : (j,l) ∈ μ) :
    tableauEntry T (i,l) < tableauEntry T (j,l) := by
  rw [tableauEntry_of_mem T (μ.up_left_mem hij.le le_rfl hc),tableauEntry_of_mem T hc]
  exact T.col_strict hij hc

/-- A standard tableau is order preserving on its Young-diagram cells. -/
theorem tableauEntry_mono (T : StandardYoungTableau μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (hcd : c ≤ d) : tableauEntry T c ≤ tableauEntry T d := by
  have hm : (c.1,d.2) ∈ μ := μ.up_left_mem hcd.1 le_rfl hd
  have hrow : tableauEntry T c ≤ tableauEntry T (c.1,d.2) := by
    rcases hcd.2.eq_or_lt with h | h
    · rw [← h]
    · exact (tableauEntry_row_lt T h hm).le
  have hcol : tableauEntry T (c.1,d.2) ≤ tableauEntry T d := by
    rcases hcd.1.eq_or_lt with h | h
    · rw [h]
    · exact (tableauEntry_col_lt T h hd).le
  exact hrow.trans hcol

theorem tableauEntry_strict (T : StandardYoungTableau μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (hcd : c ≤ d) (hne : c ≠ d) :
    tableauEntry T c < tableauEntry T d :=
  lt_of_le_of_ne (tableauEntry_mono T hc hd hcd)
    (fun h => hne (tableauEntry_injective T hc hd h))

/-- Comparable cells carrying consecutive labels are adjacent cells. -/
theorem adjacent_cells_of_entry_succ (T : StandardYoungTableau μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (hcd : c ≤ d)
    (hlabel : tableauEntry T c + 1 = tableauEntry T d) :
    d = (c.1+1,c.2) ∨ d = (c.1,c.2+1) := by
  by_cases hr : c.1 < d.1
  · let e : ℕ × ℕ := (c.1+1,c.2)
    have he : e ∈ μ := μ.up_left_mem (by omega) hcd.2 hd
    have hce : tableauEntry T c < tableauEntry T e :=
      tableauEntry_col_lt T (Nat.lt_succ_self _) he
    have hed : tableauEntry T e ≤ tableauEntry T d :=
      tableauEntry_mono T he hd ⟨by dsimp [e]; omega,hcd.2⟩
    have hv : tableauEntry T e = tableauEntry T d := by omega
    exact Or.inl (tableauEntry_injective T he hd hv).symm
  · have hr' : c.1 = d.1 := by have := hcd.1; omega
    have hs : c.2 < d.2 := by
      by_contra h
      have heq : c = d := Prod.ext hr' (by have := hcd.2; omega)
      subst d
      omega
    let e : ℕ × ℕ := (c.1,c.2+1)
    have he : e ∈ μ := μ.up_left_mem hcd.1 (by omega) hd
    have hce : tableauEntry T c < tableauEntry T e :=
      tableauEntry_row_lt T (Nat.lt_succ_self _) he
    have hed : tableauEntry T e ≤ tableauEntry T d :=
      tableauEntry_mono T he hd ⟨hcd.1,by dsimp [e]; omega⟩
    have hv : tableauEntry T e = tableauEntry T d := by omega
    exact Or.inr (tableauEntry_injective T he hd hv).symm

/-- The third adjacent label between the other two in row-reading order prevents
those two cells from being comparable. This is the geometric reason a dual move
preserves standardness. -/
theorem dual_between_incomparable (T : StandardYoungTableau μ) {c d e : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (he : e ∈ μ)
    (hlabel : tableauEntry T c + 1 = tableauEntry T d)
    (hadj : tableauEntry T e + 1 = tableauEntry T c ∨
      tableauEntry T d + 1 = tableauEntry T e)
    (hbetween : RowReadBetween c e d) : ¬c ≤ d ∧ ¬d ≤ c := by
  constructor
  · intro hcd
    rcases adjacent_cells_of_entry_succ T hc hd hcd hlabel with hv | hh
    · have hepos : e.1 = c.1 ∧ e.2 < c.2 ∨ e.1 = c.1+1 ∧ c.2 < e.2 := by
        rcases hbetween with h | h
        all_goals rcases h.1 with h1 | ⟨h1,h1'⟩ <;>
          rcases h.2 with h2 | ⟨h2,h2'⟩ <;> simp only [hv,Prod.fst,Prod.snd] at * <;> omega
      rcases hepos with ⟨her,hecol⟩ | ⟨her,hecol⟩
      · let z : ℕ × ℕ := (c.1+1,e.2)
        have hz : z ∈ μ := μ.up_left_mem (by simp [hv,z]) (by simpa [hv] using hecol.le) hd
        have hez : tableauEntry T e < tableauEntry T z := by
          rw [show e = (c.1,e.2) from Prod.ext her rfl]
          exact tableauEntry_col_lt T (Nat.lt_succ_self _) hz
        have hzd : tableauEntry T z < tableauEntry T d := by
          rw [hv]
          exact tableauEntry_row_lt T hecol (by simpa only [←hv] using hd)
        have heq : tableauEntry T z = tableauEntry T c := by rcases hadj with h | h <;> omega
        have heq' := tableauEntry_injective T hz hc heq
        have hrow := congrArg Prod.fst heq'
        dsimp [z] at hrow
        omega
      · let z : ℕ × ℕ := (c.1,e.2)
        have hz : z ∈ μ := μ.up_left_mem (by omega) le_rfl he
        have hcz : tableauEntry T c < tableauEntry T z := tableauEntry_row_lt T hecol hz
        have hze : tableauEntry T z < tableauEntry T e := by
          have he' : (c.1+1,e.2) ∈ μ := by
            change (e.1,e.2) ∈ μ at he
            rwa [her] at he
          calc
            tableauEntry T z < tableauEntry T (c.1+1,e.2) :=
              tableauEntry_col_lt T (Nat.lt_succ_self _) he'
            _ = tableauEntry T e := congrArg (tableauEntry T) (show e = (c.1+1,e.2) from Prod.ext her rfl).symm
        have heq : tableauEntry T z = tableauEntry T d := by rcases hadj with h | h <;> omega
        have heq' := tableauEntry_injective T hz hd heq
        have hrow := congrArg Prod.fst heq'
        dsimp [z] at hrow
        simp only [hv,Prod.fst] at hrow
        omega
    · rcases hbetween with h | h
      all_goals rcases h.1 with h1 | ⟨h1,h1'⟩ <;>
        rcases h.2 with h2 | ⟨h2,h2'⟩ <;> simp only [hh,Prod.fst,Prod.snd] at * <;> omega
  · intro hdc
    have h := tableauEntry_mono T hd hc hdc
    omega

/-- Swapping the two consecutive labels in incomparable cells preserves every
strict comparison that is required by a tableau. -/
theorem swap_consecutive_cells_lt (T : StandardYoungTableau μ) (c d : ↥μ.cells)
    (hlabel : (T c).val+1 = (T d).val) (hinc : ¬c.val ≤ d.val)
    (x y : ↥μ.cells) (hxy : x.val ≤ y.val) (hlt : T x < T y) :
    T (Equiv.swap c d x) < T (Equiv.swap c d y) := by
  classical
  let f : ↥μ.cells → ℕ := fun z => (T z).val
  have hf : Function.Injective f := fun x y h => T.injective (Fin.ext h)
  change f (Equiv.swap c d x) < f (Equiv.swap c d y)
  rw [← hf.swap_apply c d x,← hf.swap_apply c d y]
  change f c + 1 = f d at hlabel
  rw [←hlabel]
  apply swap_adjacent_lt hlt
  rintro ⟨hx,hy⟩
  have hxc := hf hx
  have hyd := hf (hy.trans hlabel)
  subst x; subst y
  exact hinc hxy

/-- The actual cell swap used by elementary dual equivalence. -/
def swapConsecutiveCells (T : StandardYoungTableau μ) (c d : ↥μ.cells)
    (hlabel : (T c).val+1 = (T d).val) (hinc : ¬c.val ≤ d.val) :
    StandardYoungTableau μ where
  toTableau := (Equiv.swap c d).trans T.toTableau
  row_strict' := by
    intro i j l hjl hc
    change T (Equiv.swap c d ⟨(i,j),_⟩) < T (Equiv.swap c d ⟨(i,l),hc⟩)
    exact swap_consecutive_cells_lt T c d hlabel hinc _ _ ⟨le_rfl,hjl.le⟩
      (T.row_strict hjl hc)
  col_strict' := by
    intro i j l hij hc
    change T (Equiv.swap c d ⟨(i,l),_⟩) < T (Equiv.swap c d ⟨(j,l),hc⟩)
    exact swap_consecutive_cells_lt T c d hlabel hinc _ _ ⟨hij.le,le_rfl⟩
      (T.col_strict hij hc)

end FourPapers.Symmetric


/- SOURCE FourPapers.Symmetric.DualTableauAction -/
/- Actual cell and row-word realization of the dual word operation. -/
namespace FourPapers.Symmetric
open TauCeti HigherSpecht
variable {μ : YoungDiagram}

 theorem rowReadingCells_strict (μ : YoungDiagram) :
    (rowReadingCells μ).Pairwise (fun c d => RowReadBefore c.val d.val) := by
  rw [rowReadingCells_eq_expansion]
  exact pairwise_rowExpansion μ (μ.rowLen 0)

 theorem rowReadBefore_iff_pair_sublist (c d : ↥μ.cells) :
    RowReadBefore c.val d.val ↔ [c,d].Sublist (rowReadingCells μ) := by
  constructor
  · intro h
    apply pair_sublist_of_pairwise (rowReadingCells_strict μ)
      (mem_rowReadingCells c) (mem_rowReadingCells d)
    · intro heq; subst d; exact rowReadBefore_irrefl c.val h
    · intro hdc
      exact rowReadBefore_irrefl c.val (rowReadBefore_trans h hdc)
  · intro h
    exact (List.pairwise_pair (R := fun c d : ↥μ.cells => RowReadBefore c.val d.val)).mp
      ((rowReadingCells_strict μ).sublist h)

 theorem tableauValueWord_nodup (T : StandardYoungTableau μ) :
    (tableauValueWord T).Nodup := by
  exact (nodup_rowReadingCells μ).map (fun c d h => T.injective (Fin.ext h))

 theorem mem_tableauValueWord (T : StandardYoungTableau μ) (x : Fin μ.card) :
    x.val ∈ tableauValueWord T := by
  refine List.mem_map.mpr ⟨T.toTableau.symm x,mem_rowReadingCells _,?_⟩
  change (T.toTableau (T.toTableau.symm x)).val = x.val
  rw [Equiv.apply_symm_apply]

 theorem tableauValueWord_pair_iff_cells (T : StandardYoungTableau μ) (c d : ↥μ.cells) :
    [(T c).val,(T d).val].Sublist (tableauValueWord T) ↔
      RowReadBefore c.val d.val := by
  constructor
  · intro h
    apply (rowReadBefore_iff_pair_sublist c d).mpr
    apply sublist_of_map_injective (fun c d h => T.injective (Fin.ext h))
    exact h
  · intro h
    exact ((rowReadBefore_iff_pair_sublist c d).mp h).map (fun c => (T c).val)

 theorem map_filterMap_sublist_of_partialInverse {α β : Type*}
    (f : α → Option β) (g : β → α) (h : ∀ x y, f x = some y → g y = x)
    (w : List α) : ((w.filterMap f).map g).Sublist w := by
  induction w with
  | nil => exact List.Sublist.refl _
  | cons x w ih =>
    cases hx : f x with
    | none => simpa only [List.filterMap_cons,hx,List.map_nil,List.nil_append] using ih.cons x
    | some y => simpa only [List.filterMap_cons,hx,List.map_cons,h x y hx] using ih.cons_cons x

 theorem tripleFootprint_lift_sublist (k : ℕ) (w : List ℕ) :
    ((tripleFootprint k w).map (fun d => k+d.val)).Sublist w := by
  apply map_filterMap_sublist_of_partialInverse
  intro x y h
  exact ((tripleTag_eq_some_iff k x y).mp h).symm

 theorem tripleFootprint_pair_lift {k : ℕ} {w : List ℕ} {d e : Fin 3}
    (h : [d,e].Sublist (tripleFootprint k w)) :
    [k+d.val,k+e.val].Sublist w :=
  (h.map (fun d : Fin 3 => k+d.val)).trans (tripleFootprint_lift_sublist k w)

 theorem dualSelector_eq_one_iff (w : List (Fin 3)) :
    dualSelector w = 1 ↔ w = [0,2,1] ∨ w = [1,2,0] := by
  unfold dualSelector
  split_ifs <;> simp_all

 theorem dualSelector_eq_two_iff (w : List (Fin 3)) :
    dualSelector w = 2 ↔ w = [1,0,2] ∨ w = [2,0,1] := by
  by_cases h1 : w = [0,2,1] ∨ w = [1,2,0]
  · rcases h1 with rfl | rfl <;> decide
  · unfold dualSelector
    rw [if_neg h1]
    split_ifs <;> simp_all

 def tripleCell (T : StandardYoungTableau μ) (k : ℕ) (hk : k+2 < μ.card)
    (d : Fin 3) : ↥μ.cells :=
  T.toTableau.symm ⟨k+d.val,by have := d.isLt; omega⟩

 @[simp] theorem tripleCell_label (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card) (d : Fin 3) : (T (tripleCell T k hk d)).val = k+d.val := by
  change (T.toTableau (T.toTableau.symm _)).val = _
  rw [Equiv.apply_symm_apply]

 theorem tripleCell_before (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card) {d e : Fin 3}
    (h : [d,e].Sublist (tripleFootprint k (tableauValueWord T))) :
    RowReadBefore (tripleCell T k hk d).val (tripleCell T k hk e).val := by
  apply (tableauValueWord_pair_iff_cells T _ _).mp
  simpa only [tripleCell_label] using tripleFootprint_pair_lift h

 theorem selector_one_between (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card)
    (hs : dualSelector (tripleFootprint k (tableauValueWord T)) = 1) :
    RowReadBetween (tripleCell T k hk 0).val (tripleCell T k hk 2).val
      (tripleCell T k hk 1).val := by
  rcases (dualSelector_eq_one_iff _).mp hs with h | h
  · exact Or.inl ⟨tripleCell_before T k hk (by rw [h]; decide),
      tripleCell_before T k hk (by rw [h]; decide)⟩
  · exact Or.inr ⟨tripleCell_before T k hk (by rw [h]; decide),
      tripleCell_before T k hk (by rw [h]; decide)⟩

 theorem selector_two_between (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card)
    (hs : dualSelector (tripleFootprint k (tableauValueWord T)) = 2) :
    RowReadBetween (tripleCell T k hk 1).val (tripleCell T k hk 0).val
      (tripleCell T k hk 2).val := by
  rcases (dualSelector_eq_two_iff _).mp hs with h | h
  · exact Or.inl ⟨tripleCell_before T k hk (by rw [h]; decide),
      tripleCell_before T k hk (by rw [h]; decide)⟩
  · exact Or.inr ⟨tripleCell_before T k hk (by rw [h]; decide),
      tripleCell_before T k hk (by rw [h]; decide)⟩

 theorem tableauEntry_tripleCell_label (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card) (d : Fin 3) :
    tableauEntry T (tripleCell T k hk d).val = k+d.val := by
  rw [tableauEntry_of_mem T (tripleCell T k hk d).property]
  exact tripleCell_label T k hk d

 theorem selector_one_incomparable (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card)
    (hs : dualSelector (tripleFootprint k (tableauValueWord T)) = 1) :
    ¬ (tripleCell T k hk 0).val ≤ (tripleCell T k hk 1).val := by
  apply (dual_between_incomparable T
    (c := (tripleCell T k hk 0).val) (d := (tripleCell T k hk 1).val)
    (e := (tripleCell T k hk 2).val) (tripleCell T k hk 0).property
    (tripleCell T k hk 1).property (tripleCell T k hk 2).property
    (by simp [tableauEntry_tripleCell_label, Fin.val_two, Nat.add_assoc])
    (Or.inr (by simp [tableauEntry_tripleCell_label, Fin.val_two, Nat.add_assoc]))
    (selector_one_between T k hk hs)).1

 theorem selector_two_incomparable (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card)
    (hs : dualSelector (tripleFootprint k (tableauValueWord T)) = 2) :
    ¬ (tripleCell T k hk 1).val ≤ (tripleCell T k hk 2).val := by
  apply (dual_between_incomparable T
    (c := (tripleCell T k hk 1).val) (d := (tripleCell T k hk 2).val)
    (e := (tripleCell T k hk 0).val) (tripleCell T k hk 1).property
    (tripleCell T k hk 2).property (tripleCell T k hk 0).property
    (by simp [tableauEntry_tripleCell_label, Fin.val_two, Nat.add_assoc])
    (Or.inl (by simp [tableauEntry_tripleCell_label, Fin.val_two, Nat.add_assoc]))
    (selector_two_between T k hk hs)).1

 noncomputable def dualTableau (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card) : StandardYoungTableau μ :=
  if h1 : dualSelector (tripleFootprint k (tableauValueWord T)) = 1 then
    swapConsecutiveCells T (tripleCell T k hk 0) (tripleCell T k hk 1)
      (by simp only [tripleCell_label]; rfl) (selector_one_incomparable T k hk h1)
  else if h2 : dualSelector (tripleFootprint k (tableauValueWord T)) = 2 then
    swapConsecutiveCells T (tripleCell T k hk 1) (tripleCell T k hk 2)
      (by simp only [tripleCell_label]; omega) (selector_two_incomparable T k hk h2)
  else T

 theorem swapConsecutiveCells_apply_val (T : StandardYoungTableau μ) (c d x : ↥μ.cells)
    (hlabel : (T c).val+1 = (T d).val) (hinc : ¬ c.val ≤ d.val) :
    ((swapConsecutiveCells T c d hlabel hinc) x).val =
      Equiv.swap (T c).val (T d).val (T x).val := by
  classical
  let f : ↥μ.cells → ℕ := fun c => (T c).val
  have hf : Function.Injective f := fun c d h => T.injective (Fin.ext h)
  change f (Equiv.swap c d x) = Equiv.swap (f c) (f d) (f x)
  exact (hf.swap_apply c d x).symm

 theorem dualTableau_apply_val (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card) (x : ↥μ.cells) :
    (dualTableau T k hk x).val =
      dualLetter k (dualSelector (tripleFootprint k (tableauValueWord T))) (T x).val := by
  unfold dualTableau dualLetter
  split_ifs <;> simp only [swapConsecutiveCells_apply_val,tripleCell_label,
    Fin.val_zero,Fin.val_one,Fin.val_two,Fin.val_ofNat,Nat.add_zero,Equiv.refl_apply]

 theorem tableauValueWord_dualTableau (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k+2 < μ.card) : tableauValueWord (dualTableau T k hk) =
      dualWord k (tableauValueWord T) := by
  unfold tableauValueWord dualWord
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact dualTableau_apply_val T k hk c

end FourPapers.Symmetric



/- COMPLETE SOURCE COMPONENT StrictDualTableau -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
/- Injective semistandard fillings with arbitrary natural-number labels.
This permits gaps in the label set during actual matching insertion. -/
namespace FourPapers.Symmetric
open TauCeti

structure StrictCellFilling (μ : YoungDiagram) where
  entry : ↥μ.cells → ℕ
  injective : Function.Injective entry
  row_strict : ∀ {i j l : ℕ} (hjl : j < l) (hc : (i,l) ∈ μ),
    entry ⟨(i,j),μ.up_left_mem le_rfl hjl.le hc⟩ < entry ⟨(i,l),hc⟩
  col_strict : ∀ {i j l : ℕ} (hij : i < j) (hc : (j,l) ∈ μ),
    entry ⟨(i,l),μ.up_left_mem hij.le le_rfl hc⟩ < entry ⟨(j,l),hc⟩

instance {μ : YoungDiagram} : CoeFun (StrictCellFilling μ) (fun _ => ↥μ.cells → ℕ) :=
  ⟨StrictCellFilling.entry⟩

variable {μ : YoungDiagram}

def strictEntry (T : StrictCellFilling μ) (c : ℕ × ℕ) : ℕ :=
  if hc : c ∈ μ then T ⟨c,hc⟩ else 0

@[simp] theorem strictEntry_of_mem (T : StrictCellFilling μ) {c : ℕ × ℕ}
    (hc : c ∈ μ) : strictEntry T c = T ⟨c,hc⟩ := by
  simp only [strictEntry,dif_pos hc]

 theorem strictEntry_injective (T : StrictCellFilling μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (h : strictEntry T c = strictEntry T d) : c = d := by
  rw [strictEntry_of_mem T hc,strictEntry_of_mem T hd] at h
  exact congrArg Subtype.val (T.injective h)

end FourPapers.Symmetric

namespace FourPapers.Symmetric
open TauCeti
variable {μ : YoungDiagram}
theorem strictEntry_row_lt (T : StrictCellFilling μ) {i j l : ℕ}
    (hjl : j < l) (hc : (i,l) ∈ μ) :
    strictEntry T (i,j) < strictEntry T (i,l) := by
  rw [strictEntry_of_mem T (μ.up_left_mem le_rfl hjl.le hc),strictEntry_of_mem T hc]
  exact T.row_strict hjl hc

theorem strictEntry_col_lt (T : StrictCellFilling μ) {i j l : ℕ}
    (hij : i < j) (hc : (j,l) ∈ μ) :
    strictEntry T (i,l) < strictEntry T (j,l) := by
  rw [strictEntry_of_mem T (μ.up_left_mem hij.le le_rfl hc),strictEntry_of_mem T hc]
  exact T.col_strict hij hc

/-- A standard tableau is order preserving on its Young-diagram cells. -/
theorem strictEntry_mono (T : StrictCellFilling μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (hcd : c ≤ d) : strictEntry T c ≤ strictEntry T d := by
  have hm : (c.1,d.2) ∈ μ := μ.up_left_mem hcd.1 le_rfl hd
  have hrow : strictEntry T c ≤ strictEntry T (c.1,d.2) := by
    rcases hcd.2.eq_or_lt with h | h
    · rw [← h]
    · exact (strictEntry_row_lt T h hm).le
  have hcol : strictEntry T (c.1,d.2) ≤ strictEntry T d := by
    rcases hcd.1.eq_or_lt with h | h
    · rw [h]
    · exact (strictEntry_col_lt T h hd).le
  exact hrow.trans hcol

theorem strictEntry_strict (T : StrictCellFilling μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (hcd : c ≤ d) (hne : c ≠ d) :
    strictEntry T c < strictEntry T d :=
  lt_of_le_of_ne (strictEntry_mono T hc hd hcd)
    (fun h => hne (strictEntry_injective T hc hd h))

/-- Comparable cells carrying consecutive labels are adjacent cells. -/
theorem adjacent_strict_cells_of_entry_succ (T : StrictCellFilling μ) {c d : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (hcd : c ≤ d)
    (hlabel : strictEntry T c + 1 = strictEntry T d) :
    d = (c.1+1,c.2) ∨ d = (c.1,c.2+1) := by
  by_cases hr : c.1 < d.1
  · let e : ℕ × ℕ := (c.1+1,c.2)
    have he : e ∈ μ := μ.up_left_mem (by omega) hcd.2 hd
    have hce : strictEntry T c < strictEntry T e :=
      strictEntry_col_lt T (Nat.lt_succ_self _) he
    have hed : strictEntry T e ≤ strictEntry T d :=
      strictEntry_mono T he hd ⟨by dsimp [e]; omega,hcd.2⟩
    have hv : strictEntry T e = strictEntry T d := by omega
    exact Or.inl (strictEntry_injective T he hd hv).symm
  · have hr' : c.1 = d.1 := by have := hcd.1; omega
    have hs : c.2 < d.2 := by
      by_contra h
      have heq : c = d := Prod.ext hr' (by have := hcd.2; omega)
      subst d
      omega
    let e : ℕ × ℕ := (c.1,c.2+1)
    have he : e ∈ μ := μ.up_left_mem hcd.1 (by omega) hd
    have hce : strictEntry T c < strictEntry T e :=
      strictEntry_row_lt T (Nat.lt_succ_self _) he
    have hed : strictEntry T e ≤ strictEntry T d :=
      strictEntry_mono T he hd ⟨hcd.1,by dsimp [e]; omega⟩
    have hv : strictEntry T e = strictEntry T d := by omega
    exact Or.inr (strictEntry_injective T he hd hv).symm

/-- The third adjacent label between the other two in row-reading order prevents
those two cells from being comparable. This is the geometric reason a dual move
preserves standardness. -/
theorem strict_dual_between_incomparable (T : StrictCellFilling μ) {c d e : ℕ × ℕ}
    (hc : c ∈ μ) (hd : d ∈ μ) (he : e ∈ μ)
    (hlabel : strictEntry T c + 1 = strictEntry T d)
    (hadj : strictEntry T e + 1 = strictEntry T c ∨
      strictEntry T d + 1 = strictEntry T e)
    (hbetween : RowReadBetween c e d) : ¬c ≤ d ∧ ¬d ≤ c := by
  constructor
  · intro hcd
    rcases adjacent_strict_cells_of_entry_succ T hc hd hcd hlabel with hv | hh
    · have hepos : e.1 = c.1 ∧ e.2 < c.2 ∨ e.1 = c.1+1 ∧ c.2 < e.2 := by
        rcases hbetween with h | h
        all_goals rcases h.1 with h1 | ⟨h1,h1'⟩ <;>
          rcases h.2 with h2 | ⟨h2,h2'⟩ <;> simp only [hv,Prod.fst,Prod.snd] at * <;> omega
      rcases hepos with ⟨her,hecol⟩ | ⟨her,hecol⟩
      · let z : ℕ × ℕ := (c.1+1,e.2)
        have hz : z ∈ μ := μ.up_left_mem (by simp [hv,z]) (by simpa [hv] using hecol.le) hd
        have hez : strictEntry T e < strictEntry T z := by
          rw [show e = (c.1,e.2) from Prod.ext her rfl]
          exact strictEntry_col_lt T (Nat.lt_succ_self _) hz
        have hzd : strictEntry T z < strictEntry T d := by
          rw [hv]
          exact strictEntry_row_lt T hecol (by simpa only [←hv] using hd)
        have heq : strictEntry T z = strictEntry T c := by rcases hadj with h | h <;> omega
        have heq' := strictEntry_injective T hz hc heq
        have hrow := congrArg Prod.fst heq'
        dsimp [z] at hrow
        omega
      · let z : ℕ × ℕ := (c.1,e.2)
        have hz : z ∈ μ := μ.up_left_mem (by omega) le_rfl he
        have hcz : strictEntry T c < strictEntry T z := strictEntry_row_lt T hecol hz
        have hze : strictEntry T z < strictEntry T e := by
          have he' : (c.1+1,e.2) ∈ μ := by
            change (e.1,e.2) ∈ μ at he
            rwa [her] at he
          calc
            strictEntry T z < strictEntry T (c.1+1,e.2) :=
              strictEntry_col_lt T (Nat.lt_succ_self _) he'
            _ = strictEntry T e := congrArg (strictEntry T) (show e = (c.1+1,e.2) from Prod.ext her rfl).symm
        have heq : strictEntry T z = strictEntry T d := by rcases hadj with h | h <;> omega
        have heq' := strictEntry_injective T hz hd heq
        have hrow := congrArg Prod.fst heq'
        dsimp [z] at hrow
        simp only [hv,Prod.fst] at hrow
        omega
    · rcases hbetween with h | h
      all_goals rcases h.1 with h1 | ⟨h1,h1'⟩ <;>
        rcases h.2 with h2 | ⟨h2,h2'⟩ <;> simp only [hh,Prod.fst,Prod.snd] at * <;> omega
  · intro hdc
    have h := strictEntry_mono T hd hc hdc
    omega

/-- Swapping the two consecutive labels in incomparable cells preserves every
strict comparison that is required by a tableau. -/
theorem swap_strict_consecutive_cells_lt (T : StrictCellFilling μ) (c d : ↥μ.cells)
    (hlabel : T c+1 = T d) (hinc : ¬c.val ≤ d.val)
    (x y : ↥μ.cells) (hxy : x.val ≤ y.val) (hlt : T x < T y) :
    T (Equiv.swap c d x) < T (Equiv.swap c d y) := by
  classical
  let f : ↥μ.cells → ℕ := fun z => T z
  have hf : Function.Injective f := fun x y h => T.injective h
  change f (Equiv.swap c d x) < f (Equiv.swap c d y)
  rw [← hf.swap_apply c d x,← hf.swap_apply c d y]
  change f c + 1 = f d at hlabel
  rw [←hlabel]
  apply swap_adjacent_lt hlt
  rintro ⟨hx,hy⟩
  have hxc := hf hx
  have hyd := hf (hy.trans hlabel)
  subst x; subst y
  exact hinc hxy


/-- Swapping consecutive labels in incomparable cells, retaining arbitrary gaps. -/
def swapStrictConsecutive (T : StrictCellFilling μ) (c d : ↥μ.cells)
    (hlabel : T c+1 = T d) (hinc : ¬c.val ≤ d.val) : StrictCellFilling μ where
  entry x := T (Equiv.swap c d x)
  injective := T.injective.comp (Equiv.swap c d).injective
  row_strict := by
    intro i j l hjl hc
    exact swap_strict_consecutive_cells_lt T c d hlabel hinc _ _ ⟨le_rfl,hjl.le⟩
      (T.row_strict hjl hc)
  col_strict := by
    intro i j l hij hc
    exact swap_strict_consecutive_cells_lt T c d hlabel hinc _ _ ⟨hij.le,le_rfl⟩
      (T.col_strict hij hc)

 theorem swapStrictConsecutive_apply (T : StrictCellFilling μ) (c d x : ↥μ.cells)
    (hlabel : T c+1 = T d) (hinc : ¬c.val ≤ d.val) :
    swapStrictConsecutive T c d hlabel hinc x = Equiv.swap (T c) (T d) (T x) :=
  (T.injective.swap_apply c d x).symm

end FourPapers.Symmetric
namespace FourPapers.Symmetric
open TauCeti HigherSpecht
variable {μ : YoungDiagram}

 theorem rows_cell_row_bound {rows : List (List ℕ)}
    (hshape : rows.map List.length = μ.rowLens) {c : ℕ × ℕ} (hc : c ∈ μ) :
    c.1 < rows.length := by
  simpa [← List.length_map (f := List.length),hshape] using μ.lt_colLen_zero_of_mem hc

 theorem rows_cell_length {rows : List (List ℕ)}
    (hshape : rows.map List.length = μ.rowLens) {i : ℕ} (hi : i < rows.length) :
    rows[i].length = μ.rowLen i := by
  rw [← YoungDiagram.matching_getD_rowLens,←hshape,←List.getD_eq_getElem?_getD,
    List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]

 theorem rows_cell_col_bound {rows : List (List ℕ)}
    (hshape : rows.map List.length = μ.rowLens) {c : ℕ × ℕ} (hc : c ∈ μ) :
    c.2 < (rows[c.1]'(rows_cell_row_bound hshape hc)).length := by
  rw [rows_cell_length hshape]
  exact YoungDiagram.mem_iff_lt_rowLen.mp hc

 def rowsCellEntry {rows : List (List ℕ)} (hshape : rows.map List.length = μ.rowLens)
    (c : ↥μ.cells) : ℕ :=
    (rows[c.val.1]'(rows_cell_row_bound hshape c.property))[c.val.2]'
      (rows_cell_col_bound hshape c.property)

 theorem rowsCellEntry_injective {rows : List (List ℕ)}
    (hshape : rows.map List.length = μ.rowLens) (hn : rows.flatten.Nodup) :
    Function.Injective (rowsCellEntry hshape) := by
  intro c d h
  change (rows[c.val.1]'(rows_cell_row_bound hshape c.property))[c.val.2]'(rows_cell_col_bound hshape c.property) =
    (rows[d.val.1]'(rows_cell_row_bound hshape d.property))[d.val.2]'(rows_cell_col_bound hshape d.property) at h
  have hc := rows_cell_row_bound hshape c.property
  have hd := rows_cell_row_bound hshape d.property
  have hc' := rows_cell_col_bound hshape c.property
  have hd' := rows_cell_col_bound hshape d.property
  have hparts := List.nodup_flatten.mp hn
  have hr : c.val.1 = d.val.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hdis := hparts.2.rel_getElem_of_lt hc hd hlt
      exact hdis (List.getElem_mem hc') (h.symm ▸ List.getElem_mem hd')
    · have hdis := hparts.2.rel_getElem_of_lt hd hc hgt
      exact hdis (List.getElem_mem hd') (h ▸ List.getElem_mem hc')
  have hcol : c.val.2 = d.val.2 := by
    apply (hparts.1 _ (List.getElem_mem hc)).eq_of_getElem_eq hc'
      (by simpa only [hr] using hd')
    simpa only [rowsCellEntry,hr] using h
  exact Subtype.ext (Prod.ext hr hcol)

 def strictFillingOfRows {rows : List (List ℕ)} (hrows : rows.IsTableauRows)
    (hshape : rows.map List.length = μ.rowLens) (hn : rows.flatten.Nodup) :
    StrictCellFilling μ where
  entry := rowsCellEntry hshape
  injective := rowsCellEntry_injective hshape hn
  row_strict := by
    intro i j l hjl hc
    have hi := rows_cell_row_bound hshape hc
    have hsorted := (hrows.sortedLE _ (List.getElem_mem hi)).sortedLT_of_nodup
      ((List.nodup_flatten.mp hn).1 _ (List.getElem_mem hi))
    exact hsorted.strictMono_get
      (a := ⟨j,hjl.trans (rows_cell_col_bound hshape hc)⟩)
      (b := ⟨l,rows_cell_col_bound hshape hc⟩) hjl
  col_strict := by
    intro i j l hij hc
    have hj := rows_cell_row_bound hshape hc
    have hl := rows_cell_col_bound hshape hc
    have habove := (List.pairwise_iff_getElem.mp hrows.isChain.pairwise)
      i j (hij.trans hj) hj hij
    exact habove.getElem_lt l (hl.trans_le habove.length_le) hl

 def strictFillingRows (T : StrictCellFilling μ) : List (List ℕ) :=
   fillingRows T (μ.rowLen 0)

 theorem strictFillingRows_eq_ofRows {rows : List (List ℕ)} (hrows : rows.IsTableauRows)
    (hshape : rows.map List.length = μ.rowLens) (hn : rows.flatten.Nodup) :
    strictFillingRows (strictFillingOfRows hrows hshape hn) = rows := by
  have hlen : rows.length = μ.colLen 0 := by simpa using congrArg List.length hshape
  unfold strictFillingRows fillingRows rowsOfCells
  rw [List.map_ofFn]
  refine List.ext_getElem (by simp [hlen]) fun i hi hi' => ?_
  simp only [List.getElem_ofFn,Function.comp_def,cellsInRow,List.map_ofFn]
  have hr : μ.rowLen i ≤ μ.rowLen 0 := μ.rowLen_anti 0 i (Nat.zero_le _)
  simp only [min_eq_right hr]
  refine List.ext_getElem (by simp [rows_cell_length hshape hi']) fun j hj hj' => ?_
  rw [List.getElem_ofFn]
  rfl

 theorem strictFillingRows_isTableau (T : StrictCellFilling μ) :
    (strictFillingRows T).IsTableauRows := by
  unfold strictFillingRows fillingRows rowsOfCells
  simp only [List.map_ofFn,Function.comp_def]
  refine ⟨?_,?_,?_⟩
  · simp only [List.mem_ofFn]
    rintro ⟨i,hi⟩
    have hpos : 0 < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)
    have hlen := congrArg List.length hi
    simp only [cellsInRow,List.length_map,List.length_ofFn,List.length_nil] at hlen
    have hr : μ.rowLen i ≤ μ.rowLen 0 := μ.rowLen_anti 0 i (Nat.zero_le _)
    omega
  · simp only [List.forall_mem_ofFn_iff]
    intro i
    simp only [cellsInRow,List.map_ofFn]
    apply List.sortedLE_iff_pairwise.mpr
    apply List.pairwise_ofFn.mpr
    intro j l hjl
    exact (T.row_strict hjl
      (YoungDiagram.mem_iff_lt_rowLen.mpr (l.isLt.trans_le (min_le_right _ _)))).le
  · apply List.Pairwise.isChain
    rw [List.pairwise_ofFn]
    intro i j hij
    have hi : μ.rowLen i ≤ μ.rowLen 0 := μ.rowLen_anti 0 i (Nat.zero_le _)
    have hj : μ.rowLen j ≤ μ.rowLen 0 := μ.rowLen_anti 0 j (Nat.zero_le _)
    simp only [cellsInRow,min_eq_right hi,min_eq_right hj,List.map_ofFn]
    refine ⟨by simpa using μ.rowLen_anti i j hij.le,?_⟩
    intro l hu hl
    simp only [List.length_ofFn] at hu hl
    simpa using T.col_strict hij (YoungDiagram.mem_iff_lt_rowLen.mpr hl)

 noncomputable def strictValueWord (T : StrictCellFilling μ) : List ℕ :=
   (rowReadingCells μ).map T

 theorem strictValueWord_eq_rows (T : StrictCellFilling μ) :
    strictValueWord T = rowWordRows (strictFillingRows T) := by
  simp only [strictValueWord,rowReadingCells_eq_expansion,rowWordRows,
    strictFillingRows,fillingRows,List.map_reverse,List.map_flatten]

 theorem strictValueWord_pair_iff_cells (T : StrictCellFilling μ) (c d : ↥μ.cells) :
    [T c,T d].Sublist (strictValueWord T) ↔ RowReadBefore c.val d.val := by
  constructor
  · intro h
    apply (rowReadBefore_iff_pair_sublist c d).mpr
    exact sublist_of_map_injective T.injective h
  · intro h
    exact ((rowReadBefore_iff_pair_sublist c d).mp h).map T

 theorem strictValueWord_nodup (T : StrictCellFilling μ) :
    (strictValueWord T).Nodup := (nodup_rowReadingCells μ).map T.injective

 theorem strictFillingRows_injective : Function.Injective (strictFillingRows (μ := μ)) := by
  intro T U h
  have hw : strictValueWord T = strictValueWord U := by
    rw [strictValueWord_eq_rows,strictValueWord_eq_rows,h]
  have he : T.entry = U.entry := funext fun c => List.map_inj_left.mp hw c (mem_rowReadingCells c)
  cases T; cases U; cases he; rfl

end FourPapers.Symmetric

namespace FourPapers.Symmetric
open TauCeti HigherSpecht
variable {μ : YoungDiagram}

 noncomputable def strictTripleCell (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) (d : Fin 3) : ↥μ.cells :=
  Classical.choose (List.mem_map.mp (hm d))

 @[simp] theorem strictTripleCell_label (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) (d : Fin 3) :
    T (strictTripleCell T k hm d) = k+d.val :=
  (Classical.choose_spec (List.mem_map.mp (hm d))).2

 theorem strictTripleCell_before (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) {d e : Fin 3}
    (h : [d,e].Sublist (tripleFootprint k (strictValueWord T))) :
    RowReadBefore (strictTripleCell T k hm d).val (strictTripleCell T k hm e).val := by
  apply (strictValueWord_pair_iff_cells T _ _).mp
  simpa only [strictTripleCell_label] using tripleFootprint_pair_lift h

 theorem strict_selector_one_between (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T)
    (hs : dualSelector (tripleFootprint k (strictValueWord T)) = 1) :
    RowReadBetween (strictTripleCell T k hm 0).val (strictTripleCell T k hm 2).val
      (strictTripleCell T k hm 1).val := by
  rcases (dualSelector_eq_one_iff _).mp hs with h | h
  · exact Or.inl ⟨strictTripleCell_before T k hm (by rw [h]; decide),
      strictTripleCell_before T k hm (by rw [h]; decide)⟩
  · exact Or.inr ⟨strictTripleCell_before T k hm (by rw [h]; decide),
      strictTripleCell_before T k hm (by rw [h]; decide)⟩

 theorem strict_selector_two_between (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T)
    (hs : dualSelector (tripleFootprint k (strictValueWord T)) = 2) :
    RowReadBetween (strictTripleCell T k hm 1).val (strictTripleCell T k hm 0).val
      (strictTripleCell T k hm 2).val := by
  rcases (dualSelector_eq_two_iff _).mp hs with h | h
  · exact Or.inl ⟨strictTripleCell_before T k hm (by rw [h]; decide),
      strictTripleCell_before T k hm (by rw [h]; decide)⟩
  · exact Or.inr ⟨strictTripleCell_before T k hm (by rw [h]; decide),
      strictTripleCell_before T k hm (by rw [h]; decide)⟩

 theorem strictEntry_strictTripleCell_label (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) (d : Fin 3) :
    strictEntry T (strictTripleCell T k hm d).val = k+d.val := by
  rw [strictEntry_of_mem T (strictTripleCell T k hm d).property]
  exact strictTripleCell_label T k hm d

 theorem strict_selector_one_incomparable (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T)
    (hs : dualSelector (tripleFootprint k (strictValueWord T)) = 1) :
    ¬ (strictTripleCell T k hm 0).val ≤ (strictTripleCell T k hm 1).val := by
  exact (strict_dual_between_incomparable T
    (c := (strictTripleCell T k hm 0).val) (d := (strictTripleCell T k hm 1).val)
    (e := (strictTripleCell T k hm 2).val) (strictTripleCell T k hm 0).property
    (strictTripleCell T k hm 1).property (strictTripleCell T k hm 2).property
    (by simp [strictEntry_strictTripleCell_label, Fin.val_two, Nat.add_assoc])
    (Or.inr (by simp [strictEntry_strictTripleCell_label, Fin.val_two, Nat.add_assoc]))
    (strict_selector_one_between T k hm hs)).1

 theorem strict_selector_two_incomparable (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T)
    (hs : dualSelector (tripleFootprint k (strictValueWord T)) = 2) :
    ¬ (strictTripleCell T k hm 1).val ≤ (strictTripleCell T k hm 2).val := by
  exact (strict_dual_between_incomparable T
    (c := (strictTripleCell T k hm 1).val) (d := (strictTripleCell T k hm 2).val)
    (e := (strictTripleCell T k hm 0).val) (strictTripleCell T k hm 1).property
    (strictTripleCell T k hm 2).property (strictTripleCell T k hm 0).property
    (by simp [strictEntry_strictTripleCell_label, Fin.val_two, Nat.add_assoc])
    (Or.inl (by simp [strictEntry_strictTripleCell_label, Fin.val_two, Nat.add_assoc]))
    (strict_selector_two_between T k hm hs)).1

 noncomputable def dualStrictFilling (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) : StrictCellFilling μ :=
  if h1 : dualSelector (tripleFootprint k (strictValueWord T)) = 1 then
    swapStrictConsecutive T (strictTripleCell T k hm 0) (strictTripleCell T k hm 1)
      (by simp only [strictTripleCell_label]; rfl) (strict_selector_one_incomparable T k hm h1)
  else if h2 : dualSelector (tripleFootprint k (strictValueWord T)) = 2 then
    swapStrictConsecutive T (strictTripleCell T k hm 1) (strictTripleCell T k hm 2)
      (by simp only [strictTripleCell_label]; omega) (strict_selector_two_incomparable T k hm h2)
  else T

 theorem dualStrictFilling_apply (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) (x : ↥μ.cells) :
    dualStrictFilling T k hm x =
      dualLetter k (dualSelector (tripleFootprint k (strictValueWord T))) (T x) := by
  unfold dualStrictFilling dualLetter
  split_ifs <;> simp only [swapStrictConsecutive_apply,strictTripleCell_label,
    Fin.val_zero,Fin.val_one,Fin.val_two,Fin.val_ofNat,Nat.add_zero,Equiv.refl_apply]

 theorem strictValueWord_dual (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) :
    strictValueWord (dualStrictFilling T k hm) = dualWord k (strictValueWord T) := by
  unfold strictValueWord dualWord
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact dualStrictFilling_apply T k hm c

 def dualRows (k : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  rows.map (List.map (dualLetter k (dualSelector (tripleFootprint k (rowWordRows rows)))))

 theorem rowWordRows_dualRows (k : ℕ) (rows : List (List ℕ)) :
    rowWordRows (dualRows k rows) = dualWord k (rowWordRows rows) := by
  simp only [rowWordRows,dualRows,dualWord,List.map_reverse,List.map_flatten]

 theorem strictFillingRows_dual (T : StrictCellFilling μ) (k : ℕ)
    (hm : ∀ d : Fin 3, k+d.val ∈ strictValueWord T) :
    strictFillingRows (dualStrictFilling T k hm) = dualRows k (strictFillingRows T) := by
  unfold dualRows
  rw [← strictValueWord_eq_rows]
  unfold strictFillingRows fillingRows
  rw [List.map_map]
  apply List.map_congr_left
  intro row hr
  simp only [Function.comp_apply,List.map_map]
  apply List.map_congr_left
  intro c hc
  exact dualStrictFilling_apply T k hm c

 theorem dualRows_isTableau {k : ℕ} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hn : rows.flatten.Nodup)
    (hm : ∀ d : Fin 3, k+d.val ∈ rowWordRows rows) : (dualRows k rows).IsTableauRows := by
  let μ := List.tableauShape rows hrows
  let T : StrictCellFilling μ := strictFillingOfRows hrows
    (List.rowLens_tableauShape rows hrows).symm hn
  have ht : strictFillingRows T = rows := strictFillingRows_eq_ofRows hrows _ hn
  have hm' : ∀ d : Fin 3, k+d.val ∈ strictValueWord T := by
    simpa only [strictValueWord_eq_rows,ht] using hm
  have h := strictFillingRows_isTableau (dualStrictFilling T k hm')
  simpa only [strictFillingRows_dual,ht] using h

 @[simp] theorem length_dualRows (k : ℕ) (rows : List (List ℕ)) :
    (dualRows k rows).length = rows.length := List.length_map _

 @[simp] theorem map_length_dualRows (k : ℕ) (rows : List (List ℕ)) :
    (dualRows k rows).map List.length = rows.map List.length := by
  simp only [dualRows,List.map_map,Function.comp_def,List.length_map]

 theorem mem_rowWordRows_iff (x : ℕ) (rows : List (List ℕ)) :
    x ∈ rowWordRows rows ↔ x ∈ rows.flatten := by
  simp only [rowWordRows,List.mem_flatten,List.mem_reverse]

 theorem rowWordRows_nodup_iff (rows : List (List ℕ)) :
    (rowWordRows rows).Nodup ↔ rows.flatten.Nodup := by
  exact (List.reverse_perm rows).flatten.nodup_iff

end FourPapers.Symmetric

namespace FourPapers.Symmetric
open TauCeti HigherSpecht

/-- Elementary dual equivalence commutes with ordinary insertion of every letter
outside its distinguished triple. The other labels may have arbitrary gaps. -/
theorem dualRows_rowInsert {k a : ℕ} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hn : rows.flatten.Nodup) (ha : a ∉ rows.flatten)
    (hm : ∀ d : Fin 3, k+d.val ∈ rowWordRows rows) (hout : tripleTag k a = none) :
    rowInsert a (dualRows k rows) = dualRows k (rowInsert a rows) := by
  have hD := dualRows_isTableau hrows hn hm
  have hrows' := hrows.rowInsert a
  have hn' := rowInsert_nodup hn ha
  have hm' : ∀ d : Fin 3, k+d.val ∈ rowWordRows (rowInsert a rows) := by
    intro d
    rw [mem_rowWordRows_iff,mem_rowInsert]
    exact Or.inr ((mem_rowWordRows_iff _ _).mp (hm d))
  apply tableauRows_eq_of_knuth_rowWord (hD.rowInsert a)
    (dualRows_isTableau hrows' hn' hm')
  have hbefore : (rowWordRows rows ++ [a]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(rowWordRows_nodup_iff rows).mpr hn,by simp,?_⟩
    intro x hx y hy hxy
    have hy' : y = a := by simpa using hy
    exact ha ((mem_rowWordRows_iff _ _).mp (hxy.trans hy' ▸ hx))
  have hmove := dualWord_knuthEquivalent (knuth_rowInsert rows a hrows.sortedLE)
    hbefore (fun d => List.mem_append_left _ (hm d))
  have ha' : tripleFootprint k [a] = [] := by simp [tripleFootprint,hout]
  rw [dualWord_append_outside _ _ ha',←rowWordRows_dualRows,
    ←rowWordRows_dualRows] at hmove
  exact (knuth_rowInsert (dualRows k rows) a hD.sortedLE).symm.trans hmove

 theorem length_getD_dualRows (k : ℕ) (rows : List (List ℕ)) (i : ℕ) :
    ((dualRows k rows).getD i []).length = (rows.getD i []).length := by
  simpa only [dualRows,List.map_nil,List.length_map] using
    congrArg List.length (List.getD_map rows []
      (List.map (dualLetter k (dualSelector (tripleFootprint k (rowWordRows rows))))) (n := i))

 theorem dualRows_rowInsertIndex {k a : ℕ} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hn : rows.flatten.Nodup) (ha : a ∉ rows.flatten)
    (hm : ∀ d : Fin 3, k+d.val ∈ rowWordRows rows) (hout : tripleTag k a = none) :
    rowInsertIndex a (dualRows k rows) = rowInsertIndex a rows := by
  have h := congrArg (fun T : List (List ℕ) =>
    (T.getD (rowInsertIndex a rows) []).length) (dualRows_rowInsert hrows hn ha hm hout)
  rw [length_getD_rowInsert,length_getD_dualRows,length_getD_dualRows,
    length_getD_rowInsert,if_pos rfl] at h
  split_ifs at h with hi
  · exact hi.symm
  · omega

 theorem map_appendToRow {α β : Type*} (f : α → β) (a : α) (i : ℕ)
    (rows : List (List α)) :
    (appendToRow a i rows).map (List.map f) =
      appendToRow (f a) i (rows.map (List.map f)) := by
  induction rows generalizing i with
  | nil => simp
  | cons row rows ih => cases i <;> simp [ih]

 theorem tripleFootprint_appendToRow {k a : ℕ} (hout : tripleTag k a = none)
    (i : ℕ) (rows : List (List ℕ)) :
    tripleFootprint k (rowWordRows (appendToRow a i rows)) =
      tripleFootprint k (rowWordRows rows) := by
  induction rows generalizing i with
  | nil => simp [rowWordRows,tripleFootprint,hout]
  | cons row rows ih =>
    cases i with
    | zero => simp [rowWordRows_cons,tripleFootprint,hout]
    | succ i => simp only [appendToRow_succ_cons,rowWordRows_cons,
        tripleFootprint_append,ih]

 theorem dualRows_appendToRow {k a : ℕ} (hout : tripleTag k a = none)
    (i : ℕ) (rows : List (List ℕ)) :
    dualRows k (appendToRow a i rows) = appendToRow a i (dualRows k rows) := by
  unfold dualRows
  rw [tripleFootprint_appendToRow hout,map_appendToRow,dualLetter_eq_self_of_none _ hout]

/-- The genuine paired insertion operation commutes with the actual dual action
when both new endpoints are outside the distinguished triple. This is the
arbitrary-label form of the column-Beissinger commuting step. -/
theorem dualRows_pairInsert {k a b : ℕ} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hn : rows.flatten.Nodup) (ha : a ∉ rows.flatten)
    (hm : ∀ d : Fin 3, k+d.val ∈ rowWordRows rows)
    (haout : tripleTag k a = none) (hbout : tripleTag k b = none) :
    pairInsert a b (dualRows k rows) = dualRows k (pairInsert a b rows) := by
  unfold pairInsert
  rw [dualRows_appendToRow hbout,dualRows_rowInsertIndex hrows hn ha hm haout,
    dualRows_rowInsert hrows hn ha hm haout]

end FourPapers.Symmetric

namespace FourPapers.Symmetric
open TauCeti HigherSpecht

 theorem isTableauRows_fold_rowInsert (w : List ℕ) {rows : List (List ℕ)}
    (h : rows.IsTableauRows) :
    (w.foldl (fun rows x => rowInsert x rows) rows).IsTableauRows := by
  induction w generalizing rows with
  | nil => exact h
  | cons x w ih => exact ih (h.rowInsert x)

 theorem word_knuth_insertionRows (w : List ℕ) :
    KnuthEquivalent w (rowWordRows (w.foldl (fun rows x => rowInsert x rows) [])) := by
  simpa only [rowWordRows_nil,List.nil_append] using knuth_fold_rowInsert w [] (by simp [RowsSorted])

/-- Full ordinary insertion intertwines the word dual operation and the actual
cell dual operation, for arbitrary distinct natural-number labels. -/
 theorem dualRows_insertionRows {k : ℕ} {w : List ℕ} (hn : w.Nodup)
    (hm : ∀ d : Fin 3, k+d.val ∈ w) :
    (dualWord k w).foldl (fun rows x => rowInsert x rows) [] =
      dualRows k (w.foldl (fun rows x => rowInsert x rows) []) := by
  let T := w.foldl (fun rows x => rowInsert x rows) []
  have hT : T.IsTableauRows := isTableauRows_fold_rowInsert w List.isTableauRows_nil
  have hword : KnuthEquivalent w (rowWordRows T) := word_knuth_insertionRows w
  have hp := knuthEquivalent_perm hword
  have hnT : T.flatten.Nodup := (rowWordRows_nodup_iff T).mp (hp.nodup hn)
  have hmT : ∀ d : Fin 3, k+d.val ∈ rowWordRows T := fun d => hp.mem_iff.mp (hm d)
  have hdual := (dualWord_knuthEquivalent hword hn hm).insertionRows_eq
  rw [←rowWordRows_dualRows,fold_rowInsert_rowWordRows _ (dualRows_isTableau hT hnT hmT)] at hdual
  exact hdual

/-- Inserting a missing member of the distinguished triple can be handled by
appending it to the reading word before applying the word dual move. -/
 theorem dualRows_rowInsert_from_word {k a : ℕ} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hn : rows.flatten.Nodup) (ha : a ∉ rows.flatten)
    (hm : ∀ d : Fin 3, k+d.val ∈ rowWordRows rows ++ [a]) :
    (dualWord k (rowWordRows rows ++ [a])).foldl (fun rows x => rowInsert x rows) [] =
      dualRows k (rowInsert a rows) := by
  have hnodup : (rowWordRows rows ++ [a]).Nodup := by
    refine List.nodup_append.mpr ⟨(rowWordRows_nodup_iff rows).mpr hn,by simp,?_⟩
    intro x hx y hy hxy
    have hy' : y = a := by simpa using hy
    exact ha ((mem_rowWordRows_iff _ _).mp (hxy.trans hy' ▸ hx))
  have h := dualRows_insertionRows hnodup hm
  simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,
    fold_rowInsert_rowWordRows rows hrows] using h

end FourPapers.Symmetric

