module

public import higher_specht.hanada_row_sorting
public import tau_ceti.combinatorics.young.standard_tableau.order
public import Mathlib.Order.Preorder.Finite
public import tau_ceti.combinatorics.young.addable
public import tau_ceti.combinatorics.young.schensted.basic
public import tau_ceti.combinatorics.young.bender_knuth

/- Generated ordinary proof stage. See audit/staged_specht_normal_form/NormalForm01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/Cocharge.lean -/



/-!
# Cocharge with the manuscript's French convention

Rows are indexed from zero at the bottom.  A rise of the row index between
consecutive labels is precisely an inverse descent of the top-to-bottom row
word.  Labels are represented by `Fin μ.card`, hence are one less than the
printed labels.  No cyclic insertion or basis theorem is built into the
definition.
-/

noncomputable section

open Finset TauCeti
open TauCeti.YoungTableau

namespace HigherSpecht

@[simp] theorem rowIndex_standard_apply {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (c : ↥μ.cells) : rowIndex S.toTableau (S c) = c.val.1 := by
  rw [← StandardYoungTableau.toTableau_apply, rowIndex_apply]

@[simp] theorem colIndex_standard_apply {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (c : ↥μ.cells) : colIndex S.toTableau (S c) = c.val.2 := by
  rw [← StandardYoungTableau.toTableau_apply, colIndex_apply]

@[simp] theorem standardTableau_apply_symm {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (i : Fin μ.card) : S (S.toTableau.symm i) = i := by
  rw [← StandardYoungTableau.toTableau_apply, Equiv.apply_symm_apply]

@[simp] theorem standardTableau_symm_apply {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (c : ↥μ.cells) : S.toTableau.symm (S c) = c := by
  rw [← StandardYoungTableau.toTableau_apply, Equiv.symm_apply_apply]

/-- Count the strict rises of a row-index sequence before position `j`. -/
def ascentCount (r : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if r i < r (i + 1) then 1 else 0

@[simp] theorem ascentCount_zero (r : ℕ → ℕ) : ascentCount r 0 = 0 := by
  simp [ascentCount]

theorem ascentCount_succ (r : ℕ → ℕ) (j : ℕ) :
    ascentCount r (j + 1) = ascentCount r j +
      if r j < r (j + 1) then 1 else 0 := by
  simp only [ascentCount, Finset.sum_range_succ]

theorem ascentCount_mono (r : ℕ → ℕ) : Monotone (ascentCount r) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [ascentCount_succ]
  exact Nat.le_add_right _ _

theorem ascentCount_le (r : ℕ → ℕ) (j : ℕ) : ascentCount r j ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ascentCount_succ]
    split_ifs <;> omega

/-- If the endpoint row rises, some consecutive row index rises between the
two endpoints.  This also records the strict cocharge consequence. -/
theorem ascentCount_lt_of_row_lt (r : ℕ → ℕ) {i j : ℕ}
    (hij : i ≤ j) (hr : r i < r j) : ascentCount r i < ascentCount r j := by
  revert hr
  induction j, hij using Nat.le_induction with
  | base => exact fun h => (lt_irrefl _ h).elim
  | succ j hij ih =>
    intro hr
    by_cases hstep : r j < r (j + 1)
    · rw [ascentCount_succ, if_pos hstep]
      exact Nat.lt_succ_of_le (ascentCount_mono r hij)
    · have hprev : r i < r j := hr.trans_le (Nat.le_of_not_gt hstep)
      exact (ih hprev).trans_le (ascentCount_mono r (Nat.le_succ j))

theorem row_le_of_ascentCount_eq (r : ℕ → ℕ) {i j : ℕ}
    (hij : i ≤ j) (hc : ascentCount r i = ascentCount r j) : r j ≤ r i := by
  by_contra h
  have := ascentCount_lt_of_row_lt r hij (Nat.lt_of_not_ge h)
  omega

/-- Extend the label-to-row function by zero outside the finite label range.
Only indices strictly below `μ.card` enter cocharge labels. -/
def tableauRows {μ : YoungDiagram} (S : StandardYoungTableau μ) (i : ℕ) : ℕ :=
  if h : i < μ.card then rowIndex S.toTableau ⟨i, h⟩ else 0

@[simp] theorem tableauRows_fin {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (i : Fin μ.card) : tableauRows S i = rowIndex S.toTableau i := by
  simp [tableauRows, i.isLt]

/-- The cocharge label of a printed entry (with the printed entry shifted by one). -/
def cochargeLabel {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (i : Fin μ.card) : ℕ := ascentCount (tableauRows S) i.val

/-- The cocharge filling on the cells, before assigning variable labels through T. -/
def cochargeFilling {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (c : ↥μ.cells) : ℕ := cochargeLabel S (S c)

def cochargeDegree {μ : YoungDiagram} (S : StandardYoungTableau μ) : ℕ :=
  ∑ i : Fin μ.card, cochargeLabel S i

def descentNumber {μ : YoungDiagram} (S : StandardYoungTableau μ) : ℕ :=
  ascentCount (tableauRows S) (μ.card - 1)

theorem cochargeLabel_mono {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    Monotone (cochargeLabel S) := by
  intro i j hij
  exact ascentCount_mono _ hij

theorem cochargeLabel_le_label {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (i : Fin μ.card) : cochargeLabel S i ≤ i.val := ascentCount_le _ _

theorem cochargeLabel_le_descentNumber {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (i : Fin μ.card) :
    cochargeLabel S i ≤ descentNumber S := by
  apply ascentCount_mono
  have := i.isLt
  omega

theorem cochargeLabel_strict_of_row_lt {μ : YoungDiagram}
    (S : StandardYoungTableau μ) {i j : Fin μ.card} (hij : i ≤ j)
    (hr : rowIndex S.toTableau i < rowIndex S.toTableau j) :
    cochargeLabel S i < cochargeLabel S j := by
  exact ascentCount_lt_of_row_lt _ hij (by simpa only [tableauRows_fin] using hr)

theorem row_le_of_cochargeLabel_eq {μ : YoungDiagram}
    (S : StandardYoungTableau μ) {i j : Fin μ.card} (hij : i ≤ j)
    (hc : cochargeLabel S i = cochargeLabel S j) :
    rowIndex S.toTableau j ≤ rowIndex S.toTableau i := by
  simpa only [tableauRows_fin] using row_le_of_ascentCount_eq
    (tableauRows S) hij hc

theorem cochargeFilling_row_mono {μ : YoungDiagram}
    (S : StandardYoungTableau μ) {c d : ↥μ.cells}
    (hr : c.val.1 = d.val.1) (hc : c.val.2 ≤ d.val.2) :
    cochargeFilling S c ≤ cochargeFilling S d := by
  apply cochargeLabel_mono
  rcases hc.eq_or_lt with h | h
  · have : c = d := Subtype.ext (Prod.ext hr h)
    simp [this]
  · exact (S.lt_of_colIndex_lt (by simpa only [rowIndex_standard_apply] using hr)
      (by simpa only [colIndex_standard_apply] using h)).le

theorem cochargeFilling_col_strict {μ : YoungDiagram}
    (S : StandardYoungTableau μ) {c d : ↥μ.cells}
    (hc : c.val.2 = d.val.2) (hr : c.val.1 < d.val.1) :
    cochargeFilling S c < cochargeFilling S d := by
  have hlabel : S c < S d := S.lt_of_rowIndex_lt
    (by simpa only [colIndex_standard_apply] using hc)
    (by simpa only [rowIndex_standard_apply] using hr)
  exact cochargeLabel_strict_of_row_lt S hlabel.le
    (by simpa only [rowIndex_standard_apply] using hr)

/-- Standardizing the cocharge filling recovers the original tableau.  The
proof uses the two reading orders directly: equal cocharge reverses row order,
while within a row the standard labels increase with columns. -/
theorem cochargeFilling_injective (μ : YoungDiagram) :
    Function.Injective (@cochargeFilling μ) := by
  intro S T hfill
  let σ : Equiv.Perm (Fin μ.card) := S.toTableau.symm.trans T.toTableau
  have hσ (i : Fin μ.card) : σ i = T (S.toTableau.symm i) := rfl
  have hr (i : Fin μ.card) : rowIndex T.toTableau (σ i) = rowIndex S.toTableau i := by
    rw [hσ, rowIndex_standard_apply, rowIndex_def]
  have hc (i : Fin μ.card) : colIndex T.toTableau (σ i) = colIndex S.toTableau i := by
    rw [hσ, colIndex_standard_apply, colIndex_def]
  have ha (i : Fin μ.card) : cochargeLabel S i = cochargeLabel T (σ i) := by
    have h := congrFun hfill (S.toTableau.symm i)
    simpa only [cochargeFilling, standardTableau_apply_symm, ← hσ] using h
  have hmono : StrictMono σ := by
    intro i j hij
    by_contra hnot
    have hji : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hnot)
      (fun h => hij.ne (σ.injective h.symm))
    have hs := cochargeLabel_mono S hij.le
    have ht := cochargeLabel_mono T hji.le
    have heq : cochargeLabel S i = cochargeLabel S j := by
      rw [← ha, ← ha] at ht
      omega
    have hrs := row_le_of_cochargeLabel_eq S hij.le heq
    have hrt := row_le_of_cochargeLabel_eq T hji.le (by rw [← ha, ← ha, heq])
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

end HigherSpecht
end
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/Catabolism.lean -/



/-!
# The actual cyclic insertion algorithm for catabolizability

This is Blasiak's Algorithm 3.1: present the rightmost cocharge letter, insert
it into its numbered row when that row end is addable, and otherwise increase
the letter and move it to the left.  Outputs are represented by a terminating
execution relation.  No fallback partition is assigned to a nonterminating
input, and termination on cocharge words is a separate mathematical obligation.
-/

noncomputable section

open Finset TauCeti Function

namespace HigherSpecht

/-- Top-to-bottom, left-to-right row reading in the paper's French convention.
The row coordinate itself is still the standard zero-based Young-diagram
coordinate, so larger row coordinates are read first. -/
def rowReadingCells (μ : YoungDiagram) : List ↥μ.cells :=
  μ.cells.attach.toList.mergeSort fun c d =>
    decide (d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 ≤ d.val.2))

def cochargeWord {μ : YoungDiagram} (S : StandardYoungTableau μ) : List ℕ :=
  (rowReadingCells μ).map (cochargeFilling S)

@[simp] theorem length_cochargeWord {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    (cochargeWord S).length = μ.card := by
  simp [cochargeWord, rowReadingCells, YoungDiagram.card]

structure CatState where
  word : List ℕ
  shape : YoungDiagram

@[ext] theorem CatState.ext {s t : CatState} (hw : s.word = t.word)
    (hsh : s.shape = t.shape) : s = t := by
  cases s
  cases t
  simp_all

def catStep (s : CatState) : CatState :=
  match s.word.reverse with
  | [] => s
  | a :: rest =>
    if YoungDiagram.IsAddable s.shape (a, s.shape.rowLen a) then
      ⟨rest.reverse, s.shape.addCell (a, s.shape.rowLen a)⟩
    else
      ⟨(a + 1) :: rest.reverse, s.shape⟩

def catRun (steps : ℕ) (s : CatState) : CatState := catStep^[steps] s

@[simp] theorem catStep_empty (μ : YoungDiagram) : catStep ⟨[], μ⟩ = ⟨[], μ⟩ := rfl

@[simp] theorem catRun_empty (N : ℕ) (μ : YoungDiagram) :
    catRun N ⟨[], μ⟩ = ⟨[], μ⟩ := by
  exact Function.iterate_fixed (catStep_empty μ) N

@[simp] theorem catRun_zero (s : CatState) : catRun 0 s = s := rfl

theorem catRun_add (m n : ℕ) (s : CatState) :
    catRun (m + n) s = catRun m (catRun n s) := by
  exact Function.iterate_add_apply catStep m n s

/-- Every step preserves the number of uninserted letters plus the number of
already inserted cells, whether the step inserts or corotates. -/
theorem catStep_mass (s : CatState) :
    (catStep s).word.length + (catStep s).shape.card = s.word.length + s.shape.card := by
  cases hword : s.word.reverse with
  | nil => simp only [catStep, hword]
  | cons a rest =>
    have hlen : s.word.length = rest.length + 1 := by
      have h := congrArg List.length hword
      simpa only [List.length_reverse, List.length_cons] using h
    by_cases ha : YoungDiagram.IsAddable s.shape (a, s.shape.rowLen a)
    · simp only [catStep, hword, if_pos ha, List.length_reverse, ha.card_addCell]
      omega
    · simp only [catStep, hword, if_neg ha, List.length_cons, List.length_reverse]
      omega

theorem catRun_mass (N : ℕ) (s : CatState) :
    (catRun N s).word.length + (catRun N s).shape.card =
      s.word.length + s.shape.card := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show N + 1 = 1 + N by omega, catRun_add]
    change (catStep (catRun N s)).word.length + (catStep (catRun N s)).shape.card = _
    rw [catStep_mass, ih]

/-- A genuine terminating output of cyclic insertion. -/
def CatWordOutput (word : List ℕ) (μ : YoungDiagram) : Prop :=
  ∃ N, catRun N ⟨word, ⊥⟩ = ⟨[], μ⟩

def CatTableauOutput {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (ν : YoungDiagram) : Prop := CatWordOutput (cochargeWord S) ν

theorem catWordOutput_unique {word : List ℕ} {μ ν : YoungDiagram}
    (hμ : CatWordOutput word μ) (hν : CatWordOutput word ν) : μ = ν := by
  obtain ⟨m, hm⟩ := hμ
  obtain ⟨n, hn⟩ := hν
  have hmn : catRun (m + n) ⟨word, ⊥⟩ = ⟨[], μ⟩ := by
    rw [Nat.add_comm m n, catRun_add, hm, catRun_empty]
  have hnm : catRun (m + n) ⟨word, ⊥⟩ = ⟨[], ν⟩ := by
    rw [catRun_add, hn, catRun_empty]
  exact congrArg CatState.shape (hmn.symm.trans hnm)

theorem catWordOutput_card {word : List ℕ} {μ : YoungDiagram}
    (h : CatWordOutput word μ) : μ.card = word.length := by
  obtain ⟨N, hN⟩ := h
  have hm := catRun_mass N (⟨word, ⊥⟩ : CatState)
  simpa only [hN, List.length_nil, zero_add, YoungDiagram.card, YoungDiagram.cells_bot,
    Finset.card_empty, Nat.add_zero] using hm

theorem catTableauOutput_card {μ ν : YoungDiagram} (S : StandardYoungTableau μ)
    (h : CatTableauOutput S ν) : ν.card = μ.card := by
  simpa only [length_cochargeWord] using catWordOutput_card h

theorem catTableauOutput_unique {μ ν θ : YoungDiagram} (S : StandardYoungTableau μ)
    (hν : CatTableauOutput S ν) (hθ : CatTableauOutput S θ) : ν = θ :=
  catWordOutput_unique hν hθ

/-- Dominance of row-prefix sums, allowing the two diagrams to have different
sizes as in the manuscript's simultaneous-ideal statements. -/
def Dominates (ν μ : YoungDiagram) : Prop :=
  ∀ r : ℕ, (∑ i ∈ Finset.range r, μ.rowLen i) ≤ ∑ i ∈ Finset.range r, ν.rowLen i

theorem dominates_refl (μ : YoungDiagram) : Dominates μ μ := fun _ => le_rfl

theorem Dominates.trans {μ ν θ : YoungDiagram}
    (hμν : Dominates μ ν) (hνθ : Dominates ν θ) : Dominates μ θ :=
  fun r => (hνθ r).trans (hμν r)

/-- The eligibility relation stated directly in terms of the actual terminating
insertion algorithm.  Its comparison with the recursive catabolism definition
is kept separate from all basis assertions. -/
def CatDominates {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (lam : YoungDiagram) : Prop :=
  ∃ ν, CatTableauOutput S ν ∧ Dominates ν lam

end HigherSpecht
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/CatTermination.lean -/



/-!
# Termination of the actual cyclic insertion algorithm

The invariant records the cocharge-word condition on the pending letters and
the already inserted row-constant tableau.  A positive pending letter has an
earlier occurrence followed by its predecessor, unless that predecessor
already occurs in the inserted diagram.  This invariant bounds every label by
the conserved mass.  Every nonterminal step either inserts one letter or
increases the total label sum, giving an explicit decreasing natural measure.
-/

noncomputable section

open Finset TauCeti

namespace HigherSpecht

lemma pair_sublist_cons_iff {α : Type*} (a b c : α) (w : List α) :
    [a, b].Sublist (c :: w) ↔ [a, b].Sublist w ∨ (a = c ∧ b ∈ w) := by
  rw [List.sublist_cons_iff]
  simp only [List.cons.injEq, List.singleton_sublist]
  aesop

lemma pair_sublist_append_singleton_iff {α : Type*} (a b c : α) (w : List α) :
    [a, b].Sublist (w ++ [c]) ↔ [a, b].Sublist w ∨ (a ∈ w ∧ b = c) := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.cons_append, pair_sublist_cons_iff, ih, pair_sublist_cons_iff]
    simp only [List.mem_append, List.mem_singleton, List.mem_cons]
    aesop

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

/-- The pending-word form of the cocharge invariant. -/
def CatAdmissible (s : CatState) : Prop :=
  ∀ a ∈ s.word, 0 < a → 0 < s.shape.rowLen (a - 1) ∨
    [a, a - 1].Sublist s.word

lemma not_addable_row_facts (μ : YoungDiagram) {a : ℕ}
    (ha : ¬ YoungDiagram.IsAddable μ (a, μ.rowLen a)) :
    0 < a ∧ μ.rowLen (a - 1) = μ.rowLen a := by
  have hap : 0 < a := by
    by_contra h
    have ha0 : a = 0 := by omega
    subst a
    apply ha
    rw [YoungDiagram.isAddable_iff_rowLen]
    exact ⟨rfl, fun i hi => by omega⟩
  have hnlt : ¬ μ.rowLen a < μ.rowLen (a - 1) := by
    intro hlt
    apply ha
    rw [YoungDiagram.isAddable_iff_rowLen]
    refine ⟨rfl, ?_⟩
    intro i hi
    have hieq : i = a - 1 := by omega
    simpa only [hieq] using hlt
  have hle := μ.rowLen_anti (a - 1) a (Nat.sub_le _ _)
  exact ⟨hap, by omega⟩

lemma admissible_accept {w : List ℕ} {μ : YoungDiagram} {a : ℕ}
    (hs : CatAdmissible ⟨w ++ [a], μ⟩)
    (ha : YoungDiagram.IsAddable μ (a, μ.rowLen a)) :
    CatAdmissible ⟨w, μ.addCell (a, μ.rowLen a)⟩ := by
  intro b hb hbp
  rcases hs b (List.mem_append.mpr (Or.inl hb)) hbp with hrow | hword
  · left
    rw [ha.rowLen_addCell]
    split_ifs <;> omega
  · rcases (pair_sublist_append_singleton_iff _ _ _ _).mp hword with hword | ⟨hb', heq⟩
    · exact Or.inr hword
    · left
      rw [ha.rowLen_addCell, if_pos heq.symm]
      exact Nat.succ_pos _

lemma admissible_reject {w : List ℕ} {μ : YoungDiagram} {a : ℕ}
    (hs : CatAdmissible ⟨w ++ [a], μ⟩)
    (ha : ¬ YoungDiagram.IsAddable μ (a, μ.rowLen a)) :
    CatAdmissible ⟨(a + 1) :: w, μ⟩ := by
  have hfacts := not_addable_row_facts μ ha
  have hamem : μ.rowLen a = 0 → a ∈ w := by
    intro hzero
    have h := hs a (by simp) hfacts.1
    rcases h with hrow | hword
    · rw [hfacts.2, hzero] at hrow
      omega
    · rcases (pair_sublist_append_singleton_iff _ _ _ _).mp hword with hword | ⟨_, hbad⟩
      · exact hword.subset (by simp)
      · omega
  intro b hb hbp
  rcases List.mem_cons.mp hb with rfl | hb
  · by_cases hrow : 0 < μ.rowLen a
    · exact Or.inl (by simpa using hrow)
    · right
      simpa only [Nat.add_sub_cancel] using
        (List.singleton_sublist.mpr (hamem (Nat.eq_zero_of_not_pos hrow))).cons_cons (a + 1)
  · rcases hs b (List.mem_append.mpr (Or.inl hb)) hbp with hrow | hword
    · exact Or.inl hrow
    · rcases (pair_sublist_append_singleton_iff _ _ _ _).mp hword with hword | ⟨_, heq⟩
      · exact Or.inr (hword.cons (a + 1))
      · by_cases hrow : 0 < μ.rowLen a
        · exact Or.inl (heq.symm ▸ hrow)
        · have hbeq : b = a + 1 := by omega
          subst b
          right
          simpa only [Nat.add_sub_cancel] using
            (List.singleton_sublist.mpr (hamem (Nat.eq_zero_of_not_pos hrow))).cons_cons (a + 1)

theorem catStep_admissible {s : CatState} (hs : CatAdmissible s) :
    CatAdmissible (catStep s) := by
  cases hword : s.word.reverse with
  | nil => simpa only [catStep, hword] using hs
  | cons a rest =>
    have hw : s.word = rest.reverse ++ [a] := by
      have h := congrArg List.reverse hword
      simpa only [List.reverse_reverse, List.reverse_cons] using h
    have hs' : CatAdmissible ⟨rest.reverse ++ [a], s.shape⟩ := hw ▸ hs
    simp only [catStep, hword]
    split_ifs with ha
    · exact admissible_accept hs' ha
    · exact admissible_reject hs' ha

def catMass (s : CatState) : ℕ := s.word.length + s.shape.card

def rowDegree (μ : YoungDiagram) : ℕ := ∑ c ∈ μ.cells, c.1

def catDegree (s : CatState) : ℕ := s.word.sum + rowDegree s.shape

lemma colLen_zero_le_card (μ : YoungDiagram) : μ.colLen 0 ≤ μ.card := by
  rw [μ.colLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma admissible_interval_mem {s : CatState} (hs : CatAdmissible s)
    {a : ℕ} (ha : a ∈ s.word) :
    ∀ b, s.shape.colLen 0 ≤ b → b ≤ a → b ∈ s.word := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b hb hba
    rcases hba.eq_or_lt with rfl | hba
    · exact ha
    · have hap : 0 < a := by omega
      rcases hs a ha hap with hrow | hword
      · have hz := YoungDiagram.rowLen_eq_zero_of_colLen_le
          (μ := s.shape) (i := a - 1) (by omega)
        omega
      · have hprev : a - 1 ∈ s.word := hword.subset (by simp)
        exact ih (a - 1) (by omega) hprev b hb (by omega)

/-- Every pending letter is bounded by the conserved number of letters and
cells.  No assertion is made for arbitrary non-cocharge input words. -/
theorem admissible_label_lt_mass {s : CatState} (hs : CatAdmissible s)
    {a : ℕ} (ha : a ∈ s.word) : a < catMass s := by
  by_cases hsmall : a < s.shape.colLen 0
  · have hh := colLen_zero_le_card s.shape
    dsimp [catMass]
    omega
  · have hsub : Finset.Icc (s.shape.colLen 0) a ⊆ s.word.toFinset := by
      intro b hb
      exact List.mem_toFinset.mpr (admissible_interval_mem hs ha b
        (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2)
    have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le s.word)
    rw [Nat.card_Icc] at hc
    have hh := colLen_zero_le_card s.shape
    dsimp [catMass]
    omega

theorem catDegree_le_mass_bound {s : CatState} (hs : CatAdmissible s) :
    catDegree s ≤ catMass s * (catMass s - 1) := by
  have hw : s.word.sum ≤ s.word.length * (catMass s - 1) := by
    have hbound : ∀ w : List ℕ, (∀ a ∈ w, a ≤ catMass s - 1) →
        w.sum ≤ w.length * (catMass s - 1) := by
      intro w
      induction w with
      | nil => simp
      | cons a w ih =>
          intro h
          have ha := h a (by simp)
          have ht := ih (fun b hb => h b (by simp [hb]))
          simpa only [List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm] using
            Nat.add_le_add ha ht
    exact hbound s.word (fun a ha => by have := admissible_label_lt_mass hs ha; omega)
  have hr : rowDegree s.shape ≤ s.shape.card * (catMass s - 1) := by
    calc
      rowDegree s.shape ≤ ∑ c ∈ s.shape.cells, (catMass s - 1) := by
        apply Finset.sum_le_sum
        intro c hc
        have hrow := YoungDiagram.lt_colLen_zero_of_mem hc
        have hh := colLen_zero_le_card s.shape
        dsimp [catMass]
        omega
      _ = s.shape.card * (catMass s - 1) := by simp [YoungDiagram.card]
  change s.word.sum + rowDegree s.shape ≤
    (s.word.length + s.shape.card) * (catMass s - 1)
  calc
    s.word.sum + rowDegree s.shape ≤
        s.word.length * (catMass s - 1) + s.shape.card * (catMass s - 1) :=
      Nat.add_le_add hw hr
    _ = (s.word.length + s.shape.card) * (catMass s - 1) :=
      (Nat.add_mul _ _ _).symm

lemma rowDegree_addCell {μ : YoungDiagram} {c : ℕ × ℕ}
    (hc : YoungDiagram.IsAddable μ c) :
    rowDegree (μ.addCell c) = rowDegree μ + c.1 := by
  rw [rowDegree, hc.cells_addCell_eq_insert, Finset.sum_insert (by simpa using hc.notMem)]
  exact Nat.add_comm _ _

theorem catStep_progress (s : CatState) (hs : s.word ≠ []) :
    catDegree (catStep s) + s.word.length =
      catDegree s + (catStep s).word.length + 1 := by
  cases hword : s.word.reverse with
  | nil =>
    have : s.word = [] := by simpa using congrArg List.reverse hword
    exact (hs this).elim
  | cons a rest =>
    have hw : s.word = rest.reverse ++ [a] := by
      simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse hword
    simp only [catStep, hword]
    split_ifs with ha
    · simp only [catDegree, List.length_reverse, rowDegree_addCell ha]
      rw [hw]
      simp only [List.sum_append, List.sum_cons, List.sum_nil, List.length_append,
        List.length_reverse, List.length_singleton, Nat.add_zero]
      omega
    · simp only [catDegree, List.sum_cons, List.length_cons, List.length_reverse]
      rw [hw]
      simp only [List.sum_append, List.sum_cons, List.sum_nil, List.length_append,
        List.length_reverse, List.length_singleton, Nat.add_zero]
      omega

def catPotential (s : CatState) : ℕ :=
  catMass s * (catMass s - 1) - catDegree s + s.word.length

theorem catPotential_step_lt {s : CatState} (hs : CatAdmissible s) (hnil : s.word ≠ []) :
    catPotential (catStep s) < catPotential s := by
  have hmass : catMass (catStep s) = catMass s := catStep_mass s
  have hbound := catDegree_le_mass_bound hs
  have hbound' := catDegree_le_mass_bound (catStep_admissible hs)
  have hprogress := catStep_progress s hnil
  unfold catPotential
  rw [hmass] at hbound' ⊢
  omega

/-- Termination for every word satisfying the genuine cocharge invariant. -/
theorem catRun_eventually_empty {s : CatState} (hs : CatAdmissible s) :
    ∃ N : ℕ, (catRun N s).word = [] := by
  have aux : ∀ k : ℕ, ∀ s : CatState, catPotential s = k → CatAdmissible s →
      ∃ N : ℕ, (catRun N s).word = [] := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s hk hs
      by_cases hnil : s.word = []
      · exact ⟨0, hnil⟩
      · have hlt : catPotential (catStep s) < k := hk ▸ catPotential_step_lt hs hnil
        obtain ⟨N, hN⟩ := ih _ hlt (catStep s) rfl (catStep_admissible hs)
        refine ⟨N + 1, ?_⟩
        rw [catRun_add]
        exact hN
  exact aux _ s rfl hs

theorem exists_catWordOutput_of_admissible {w : List ℕ}
    (hw : CatAdmissible ⟨w, ⊥⟩) : ∃ μ : YoungDiagram, CatWordOutput w μ := by
  obtain ⟨N, hN⟩ := catRun_eventually_empty hw
  exact ⟨(catRun N ⟨w, ⊥⟩).shape, N, CatState.ext hN rfl⟩

/-- A positive cocharge value is entered at a genuine inverse descent. -/
lemma exists_ascent_at_level (r : ℕ → ℕ) {j a : ℕ} (ha : 0 < a)
    (hlevel : a ≤ ascentCount r j) :
    ∃ i < j, ascentCount r i = a - 1 ∧ r i < r (i + 1) := by
  induction j with
  | zero => simp at hlevel; omega
  | succ j ih =>
    by_cases hj : a ≤ ascentCount r j
    · obtain ⟨i, hi, hc, hr⟩ := ih hj
      exact ⟨i, by omega, hc, hr⟩
    · rw [ascentCount_succ] at hlevel
      by_cases hr : r j < r (j + 1)
      · rw [if_pos hr] at hlevel
        exact ⟨j, Nat.lt_succ_self _, by omega, hr⟩
      · rw [if_neg hr] at hlevel
        omega

lemma pair_sublist_rowReadingCells {μ : YoungDiagram} {c d : ↥μ.cells}
    (hrow : d.val.1 < c.val.1) : [c, d].Sublist (rowReadingCells μ) := by
  let rel : ↥μ.cells → ↥μ.cells → Prop := fun a b =>
    b.val.1 < a.val.1 ∨ (a.val.1 = b.val.1 ∧ a.val.2 ≤ b.val.2)
  have hpair : (rowReadingCells μ).Pairwise rel := by
    unfold rowReadingCells
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b : ↥μ.cells => decide (rel a b))
        (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; dsimp [rel] at *; omega)
        (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; dsimp [rel]; omega)
        μ.cells.attach.toList)
  have hc : c ∈ rowReadingCells μ := by simp [rowReadingCells]
  have hd : d ∈ rowReadingCells μ := by simp [rowReadingCells]
  apply pair_sublist_of_pairwise hpair hc hd
  · intro h
    have h' := congrArg (fun c : ↥μ.cells => c.val.1) h
    omega
  · dsimp [rel]
    omega

/-- The row-reading cocharge word satisfies the invariant, proved directly
from successive cocharge labels and the actual sorted row reading. -/
theorem cochargeWord_admissible {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CatAdmissible ⟨cochargeWord S, ⊥⟩ := by
  intro a ha hap
  right
  obtain ⟨c, hc, hca⟩ := List.mem_map.mp ha
  have hac : a ≤ ascentCount (tableauRows S) (S c).val := by
    exact le_of_eq hca.symm
  obtain ⟨i, hij, hic, hir⟩ := exists_ascent_at_level (tableauRows S) hap hac
  have hi : i < μ.card := hij.trans (S c).isLt
  have hi' : i + 1 < μ.card := by have := (S c).isLt; omega
  let x : Fin μ.card := ⟨i, hi⟩
  let y : Fin μ.card := ⟨i + 1, hi'⟩
  have hxy : (S.toTableau.symm x).val.1 < (S.toTableau.symm y).val.1 := by
    simpa only [tableauRows, dif_pos hi, dif_pos hi', TauCeti.YoungTableau.rowIndex_def,
      x, y] using hir
  have hpair := (pair_sublist_rowReadingCells hxy).map (cochargeFilling S)
  have hx : cochargeFilling S (S.toTableau.symm x) = a - 1 := by
    simpa only [cochargeFilling, standardTableau_apply_symm, cochargeLabel, x] using hic
  have hy : cochargeFilling S (S.toTableau.symm y) = a := by
    rw [cochargeFilling, standardTableau_apply_symm]
    change ascentCount (tableauRows S) (i + 1) = a
    rw [ascentCount_succ, if_pos hir, hic]
    omega
  simpa only [List.map_cons, List.map_nil, hx, hy, cochargeWord] using hpair

/-- The actual cyclic algorithm terminates on every standard tableau's
cocharge word, with no fallback output or termination assumption. -/
theorem exists_catTableauOutput {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    ∃ ν : YoungDiagram, CatTableauOutput S ν :=
  exists_catWordOutput_of_admissible (cochargeWord_admissible S)

end HigherSpecht
end
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/CatLocalMoves.lean -/



/-!
# Local confluence calculations for cyclic catabolism

The auxiliary row-function machine is conjugate to the actual Young-diagram
machine.  It lets the two critical Knuth calculations be checked with ordinary
natural-number arithmetic.  A row function is never used as a replacement for
the actual output partition: injectivity of the encoding transfers every
calculation back to the original algorithm.
-/

noncomputable section

open Finset TauCeti Function

namespace HigherSpecht

abbrev RawCatState := List ℕ × (ℕ → ℕ)

def rawCanInsert (r : ℕ → ℕ) (a : ℕ) : Prop := a = 0 ∨ r a < r (a - 1)

instance (r : ℕ → ℕ) (a : ℕ) : Decidable (rawCanInsert r a) := inferInstanceAs
  (Decidable (a = 0 ∨ r a < r (a - 1)))

def rawCatPresent (w : List ℕ) (r : ℕ → ℕ) (a : ℕ) : RawCatState :=
  if rawCanInsert r a then (w, Function.update r a (r a + 1))
  else ((a + 1) :: w, r)

def rawCatStep (s : RawCatState) : RawCatState :=
  match s.1.reverse with
  | [] => s
  | a :: rest => rawCatPresent rest.reverse s.2 a

def rawCatRun (N : ℕ) : RawCatState → RawCatState := rawCatStep^[N]

def catEncoding (s : CatState) : RawCatState := (s.word, s.shape.rowLen)

theorem catEncoding_injective : Function.Injective catEncoding := by
  intro s t h
  apply CatState.ext (congrArg Prod.fst h)
  exact YoungDiagram.rowLen_injective (congrArg Prod.snd h)

theorem isAddable_rowEnd_iff (μ : YoungDiagram) (a : ℕ) :
    YoungDiagram.IsAddable μ (a, μ.rowLen a) ↔ rawCanInsert μ.rowLen a := by
  rw [YoungDiagram.isAddable_iff_rowLen]
  simp only [true_and, rawCanInsert]
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (h (a - 1) (by omega))
  · rintro (rfl | h) i hi
    · omega
    · simpa only [show a - 1 = i by omega] using h

theorem rowLen_addRow_eq_update {μ : YoungDiagram} {a : ℕ}
    (ha : YoungDiagram.IsAddable μ (a, μ.rowLen a)) :
    (μ.addCell (a, μ.rowLen a)).rowLen =
      Function.update μ.rowLen a (μ.rowLen a + 1) := by
  funext i
  rw [ha.rowLen_addCell]
  by_cases h : a = i
  · subst i
    simp
  · simp [Function.update_of_ne (Ne.symm h), h]

@[simp] theorem catStep_append (w : List ℕ) (μ : YoungDiagram) (a : ℕ) :
    catStep ⟨w ++ [a], μ⟩ =
      if YoungDiagram.IsAddable μ (a, μ.rowLen a) then
        ⟨w, μ.addCell (a, μ.rowLen a)⟩ else ⟨(a + 1) :: w, μ⟩ := by
  simp only [catStep, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.reverse_reverse]

@[simp] theorem rawCatStep_append (w : List ℕ) (r : ℕ → ℕ) (a : ℕ) :
    rawCatStep (w ++ [a], r) = rawCatPresent w r a := by
  simp only [rawCatStep, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.reverse_reverse]

theorem catEncoding_step (s : CatState) :
    catEncoding (catStep s) = rawCatStep (catEncoding s) := by
  obtain ⟨w, μ⟩ := s
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [catStep_append]
    change catEncoding _ = rawCatStep (w ++ [a], μ.rowLen)
    rw [rawCatStep_append, rawCatPresent]
    by_cases ha : YoungDiagram.IsAddable μ (a, μ.rowLen a)
    · rw [if_pos ha, if_pos ((isAddable_rowEnd_iff μ a).mp ha)]
      exact Prod.ext rfl (rowLen_addRow_eq_update ha)
    · rw [if_neg ha, if_neg (fun h => ha ((isAddable_rowEnd_iff μ a).mpr h))]
      rfl

theorem catEncoding_run (N : ℕ) (s : CatState) :
    catEncoding (catRun N s) = rawCatRun N (catEncoding s) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [catRun, rawCatRun, Function.iterate_succ_apply'] at ih ⊢
    rw [catEncoding_step, ih]

@[simp] theorem rawCatRun_two (s : RawCatState) :
    rawCatRun 2 s = rawCatStep (rawCatStep s) := rfl

@[simp] theorem rawCatRun_three (s : RawCatState) :
    rawCatRun 3 s = rawCatStep (rawCatStep (rawCatStep s)) := rfl

theorem rawCatPresent_append (w tail : List ℕ) (r : ℕ → ℕ) (a : ℕ) :
    rawCatPresent (w ++ tail) r a =
      ((rawCatPresent w r a).1 ++ tail, (rawCatPresent w r a).2) := by
  unfold rawCatPresent
  split_ifs <;> rfl

theorem rawCatRun_two_append (w : List ℕ) (r : ℕ → ℕ) (a b : ℕ) :
    rawCatRun 2 (w ++ [a, b], r) =
      rawCatPresent (rawCatPresent w r b).1 (rawCatPresent w r b).2 a := by
  rw [rawCatRun_two,
    show w ++ [a, b] = (w ++ [a]) ++ [b] by simp,
    rawCatStep_append, rawCatPresent_append]
  exact rawCatStep_append _ _ _

theorem rawCatRun_three_append (w : List ℕ) (r : ℕ → ℕ) (a b c : ℕ) :
    rawCatRun 3 (w ++ [a, b, c], r) =
      rawCatPresent
        (rawCatPresent (rawCatPresent w r c).1 (rawCatPresent w r c).2 b).1
        (rawCatPresent (rawCatPresent w r c).1 (rawCatPresent w r c).2 b).2 a := by
  rw [rawCatRun_three,
    show w ++ [a, b, c] = (w ++ [a, b]) ++ [c] by simp,
    rawCatStep_append, rawCatPresent_append]
  exact rawCatRun_two_append _ _ _ _

/-- The distant-row move is exactly Blasiak's catabolism transformation. -/
def FarLetters (a b : ℕ) : Prop := a + 1 < b ∨ b + 1 < a

theorem FarLetters.symm {a b : ℕ} (h : FarLetters a b) : FarLetters b a :=
  Or.symm h

theorem FarLetters.increment {a b : ℕ} (h : FarLetters a b) :
    FarLetters (a + 1) (b + 1) := by
  rcases h with h | h <;> unfold FarLetters <;> omega

theorem rawCanInsert_update_far (r : ℕ → ℕ) {a b : ℕ} (h : FarLetters a b) :
    rawCanInsert (Function.update r a (r a + 1)) b ↔ rawCanInsert r b := by
  have hab : b ≠ a := by rcases h with h | h <;> omega
  by_cases hb : b = 0
  · simp [rawCanInsert, hb]
  · have hba : b - 1 ≠ a := by rcases h with h | h <;> omega
    simp [rawCanInsert, Function.update_of_ne hab, Function.update_of_ne hba]

/-- After presenting two distant letters, either the states agree or both
letters were rejected and the same distant move has migrated to the front. -/
theorem rawCat_far_two (w : List ℕ) (r : ℕ → ℕ) {a b : ℕ}
    (hab : FarLetters a b) :
    (rawCatRun 2 (w ++ [a, b], r) = rawCatRun 2 (w ++ [b, a], r)) ∨
      (rawCatRun 2 (w ++ [a, b], r) = ([a + 1, b + 1] ++ w, r) ∧
       rawCatRun 2 (w ++ [b, a], r) = ([b + 1, a + 1] ++ w, r)) := by
  have hne : a ≠ b := by rcases hab with h | h <;> omega
  by_cases ha : rawCanInsert r a <;> by_cases hb : rawCanInsert r b
  · left
    simp only [rawCatRun_two_append, rawCatPresent,
      if_pos ha, if_pos hb]
    rw [if_pos ((rawCanInsert_update_far r hab.symm).mpr ha),
      if_pos ((rawCanInsert_update_far r hab).mpr hb)]
    apply Prod.ext
    · rfl
    · funext i
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        simp_all [Function.update_apply]
  · left
    simp only [rawCatRun_two_append, rawCatPresent,
      if_pos ha, if_neg hb]
    rw [if_neg (fun h => hb ((rawCanInsert_update_far r hab).mp h))]
  · left
    simp only [rawCatRun_two_append, rawCatPresent,
      if_neg ha, if_pos hb]
    rw [if_neg (fun h => ha ((rawCanInsert_update_far r hab.symm).mp h))]
  · right
    constructor <;>
      simp only [rawCatRun_two_append, rawCatPresent, if_neg ha, if_neg hb,
        List.cons_append, List.nil_append]

set_option maxHeartbeats 1500000 in
/-- The first adjacent-value Knuth move.  The exceptional branch is itself the
same move, with every value increased by one. -/
theorem rawCat_knuth_left_three (w : List ℕ) (r : ℕ → ℕ) (a : ℕ)
    (hanti : Antitone r) :
    rawCatRun 3 (w ++ [a + 1, a, a + 1], r) =
        rawCatRun 3 (w ++ [a + 1, a + 1, a], r) ∨
      (rawCatRun 3 (w ++ [a + 1, a, a + 1], r) =
          ([a + 2, a + 1, a + 2] ++ w, r) ∧
       rawCatRun 3 (w ++ [a + 1, a + 1, a], r) =
          ([a + 2, a + 2, a + 1] ++ w, r)) := by
  have hab : r (a + 1) ≤ r a := hanti (Nat.le_succ a)
  have hpa : r a ≤ r (a - 1) := hanti (Nat.sub_le a 1)
  have hnext : r (a + 1) < r a + 1 := by omega
  have hne : a + 1 ≠ a := by omega
  have hpred : a - 1 ≠ a + 1 := by omega
  have hpred_self : (a - 1 = a) ↔ a = 0 := by omega
  by_cases ha : rawCanInsert r a
  · left
    have hha : a = 0 ∨ r a < r (a - 1) := ha
    by_cases hz : a = 0 <;> by_cases hb : r (a + 1) < r a
    all_goals
      rw [rawCatRun_three_append, rawCatRun_three_append]
      apply Prod.ext
      · simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
      · funext i
        by_cases hi : i = a <;> by_cases hi' : i = a + 1 <;>
          simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
  · by_cases hb : rawCanInsert r (a + 1)
    · left
      have hha : ¬(a = 0 ∨ r a < r (a - 1)) := ha
      have hhb : r (a + 1) < r a := by
        rcases hb with h | h
        · omega
        · simpa only [Nat.add_sub_cancel] using h
      have hz : a ≠ 0 := fun h => ha (Or.inl h)
      by_cases htwice : r (a + 1) + 1 < r a
      all_goals
        rw [rawCatRun_three_append, rawCatRun_three_append]
        apply Prod.ext
        · simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
        · funext i
          by_cases hi : i = a <;> by_cases hi' : i = a + 1 <;>
            simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
    · right
      constructor <;>
        simp only [rawCatRun_three_append, rawCatPresent, if_neg ha, if_neg hb,
          List.cons_append, List.nil_append, Nat.add_assoc]

set_option maxHeartbeats 1500000 in
/-- The second adjacent-value Knuth move. -/
theorem rawCat_knuth_right_three (w : List ℕ) (r : ℕ → ℕ) (a : ℕ)
    (hanti : Antitone r) :
    rawCatRun 3 (w ++ [a, a + 1, a], r) =
        rawCatRun 3 (w ++ [a + 1, a, a], r) ∨
      (rawCatRun 3 (w ++ [a, a + 1, a], r) =
          ([a + 1, a + 2, a + 1] ++ w, r) ∧
       rawCatRun 3 (w ++ [a + 1, a, a], r) =
          ([a + 2, a + 1, a + 1] ++ w, r)) := by
  have hab : r (a + 1) ≤ r a := hanti (Nat.le_succ a)
  have hpa : r a ≤ r (a - 1) := hanti (Nat.sub_le a 1)
  have hnext : r (a + 1) < r a + 1 := by omega
  have hnext' : r (a + 1) < r a + 1 + 1 := by omega
  have hne : a + 1 ≠ a := by omega
  have hpred : a - 1 ≠ a + 1 := by omega
  have hpred_self : (a - 1 = a) ↔ a = 0 := by omega
  by_cases ha : rawCanInsert r a
  · left
    have hha : a = 0 ∨ r a < r (a - 1) := ha
    by_cases hz : a = 0 <;> by_cases htwice : r a + 1 < r (a - 1)
    all_goals
      rw [rawCatRun_three_append, rawCatRun_three_append]
      apply Prod.ext
      · simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
      · funext i
        by_cases hi : i = a <;> by_cases hi' : i = a + 1 <;>
          simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
  · by_cases hb : rawCanInsert r (a + 1)
    · left
      have hha : ¬(a = 0 ∨ r a < r (a - 1)) := ha
      have hhb : r (a + 1) < r a := by
        rcases hb with h | h
        · omega
        · simpa only [Nat.add_sub_cancel] using h
      have hz : a ≠ 0 := fun h => ha (Or.inl h)
      rw [rawCatRun_three_append, rawCatRun_three_append]
      apply Prod.ext
      · simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
      · funext i
        by_cases hi : i = a <;> by_cases hi' : i = a + 1 <;>
          simp_all [rawCatPresent, rawCanInsert, Function.update_apply, -not_lt, -not_le, -Nat.not_lt, -Nat.not_le]
    · right
      constructor <;>
        simp only [rawCatRun_three_append, rawCatPresent, if_neg ha, if_neg hb,
          List.cons_append, List.nil_append, Nat.add_assoc]

end HigherSpecht
end
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/CatMoveInvariance.lean -/



/-!
# Termination-preserving local moves

The proof inducts on a genuine terminating execution.  It does not assign an
output to arbitrary words, nor use termination as an extra hypothesis in the
final cocharge application.  A delayed local move either disappears when its
letters are presented or returns, incremented, at the front of the queue.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

def CatStateOutput (s : CatState) (ν : YoungDiagram) : Prop :=
  ∃ N, catRun N s = ⟨[], ν⟩

theorem catStateOutput_iff_run (s : CatState) (ν : YoungDiagram) (k : ℕ) :
    CatStateOutput s ν ↔ CatStateOutput (catRun k s) ν := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [← catRun_add, Nat.add_comm, catRun_add, hN, catRun_empty]
  · rintro ⟨N, hN⟩
    exact ⟨N + k, (catRun_add N k s).trans hN⟩

theorem catStep_length_lower (s : CatState) :
    s.word.length ≤ (catStep s).word.length + 1 := by
  obtain ⟨w, μ⟩ := s
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rw [catStep_append]
    split_ifs <;> simp <;> omega

theorem catRun_length_lower (N : ℕ) (s : CatState) :
    s.word.length ≤ (catRun N s).word.length + N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep := catStep_length_lower (catRun N s)
    have hrun : catRun (N + 1) s = catStep (catRun N s) := by
      rw [Nat.add_comm N 1, catRun_add]
      rfl
    rw [hrun]
    omega

/-- A finite set of local word rules whose nontrivial delayed branch is a
corotation of the entire rule.  The structure is purely algorithmic and its
actual instance is constructed below from the three local calculations. -/
structure CatWindowRules where
  rel : List ℕ → List ℕ → Prop
  symm : ∀ {u v}, rel u v → rel v u
  nonempty : ∀ {u v}, rel u v → 0 < u.length
  length_eq : ∀ {u v}, rel u v → u.length = v.length
  advance : ∀ {u v}, rel u v → ∀ (l : List ℕ) (μ : YoungDiagram),
    catRun u.length ⟨l ++ u, μ⟩ = catRun u.length ⟨l ++ v, μ⟩ ∨
      ∃ u' v', rel u' v' ∧
        catRun u.length ⟨l ++ u, μ⟩ = ⟨u' ++ l, μ⟩ ∧
        catRun u.length ⟨l ++ v, μ⟩ = ⟨v' ++ l, μ⟩

/-- Local-rule invariance, in arbitrary left and right contexts and from an
arbitrary existing partition.  Only the left execution is assumed terminating;
the proof constructs a terminating right execution with the same output. -/
theorem CatWindowRules.output_of_move (rules : CatWindowRules) (N : ℕ) :
    ∀ (l r u v : List ℕ) (μ ν : YoungDiagram), rules.rel u v →
      catRun N ⟨l ++ u ++ r, μ⟩ = ⟨[], ν⟩ →
      CatStateOutput ⟨l ++ v ++ r, μ⟩ ν := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro l r u v μ ν huv hN
    have hlen := catRun_length_lower N (⟨l ++ u ++ r, μ⟩ : CatState)
    rw [hN] at hlen
    simp only [List.length_append, List.length_nil, Nat.zero_add] at hlen
    have hup := rules.nonempty huv
    induction r using List.reverseRecOn with
    | nil =>
      simp only [List.append_nil] at hN ⊢
      have hkN : u.length ≤ N := by omega
      have hklt : N - u.length < N := by omega
      have htail : catRun (N - u.length) (catRun u.length ⟨l ++ u, μ⟩) =
          ⟨[], ν⟩ := by
        rw [← catRun_add, Nat.sub_add_cancel hkN]
        exact hN
      rcases rules.advance huv l μ with heq | ⟨u', v', huv', hu', hv'⟩
      · apply (catStateOutput_iff_run ⟨l ++ v, μ⟩ ν u.length).mpr
        exact ⟨N - u.length, heq ▸ htail⟩
      · rw [hu'] at htail
        have hout := ih (N - u.length) hklt [] l u' v' μ ν huv'
          (by simpa using htail)
        apply (catStateOutput_iff_run ⟨l ++ v, μ⟩ ν u.length).mpr
        simpa only [hv', List.nil_append] using hout
    | append_singleton r a ihr =>
      have hNp : 0 < N := by omega
      have hstep : catRun (N - 1) (catStep ⟨(l ++ u ++ r) ++ [a], μ⟩) =
          ⟨[], ν⟩ := by
        change catRun (N - 1) (catRun 1 ⟨(l ++ u ++ r) ++ [a], μ⟩) = _
        rw [← catRun_add, Nat.sub_add_cancel hNp]
        simpa only [List.append_assoc] using hN
      have htarget : CatStateOutput (catStep ⟨(l ++ v ++ r) ++ [a], μ⟩) ν := by
        rw [catStep_append] at hstep ⊢
        by_cases ha : YoungDiagram.IsAddable μ (a, μ.rowLen a)
        · rw [if_pos ha] at hstep ⊢
          exact ih (N - 1) (by omega) l r u v
            (μ.addCell (a, μ.rowLen a)) ν huv hstep
        · rw [if_neg ha] at hstep ⊢
          simpa only [List.cons_append] using ih (N - 1) (by omega)
            ((a + 1) :: l) r u v μ ν huv hstep
      have hout := (catStateOutput_iff_run
        (⟨(l ++ v ++ r) ++ [a], μ⟩ : CatState) ν 1).mpr htarget
      simpa only [List.append_assoc] using hout

theorem CatWindowRules.output_iff (rules : CatWindowRules)
    {u v : List ℕ} (huv : rules.rel u v) (l r : List ℕ) (μ ν : YoungDiagram) :
    CatStateOutput ⟨l ++ u ++ r, μ⟩ ν ↔ CatStateOutput ⟨l ++ v ++ r, μ⟩ ν := by
  constructor
  · rintro ⟨N, hN⟩
    exact rules.output_of_move N l r u v μ ν huv hN
  · rintro ⟨N, hN⟩
    exact rules.output_of_move N l r v u μ ν (rules.symm huv) hN

inductive CatPrimitive : List ℕ → List ℕ → Prop
  | far {a b : ℕ} : FarLetters a b → CatPrimitive [a, b] [b, a]
  | left (a : ℕ) : CatPrimitive [a + 1, a, a + 1] [a + 1, a + 1, a]
  | right (a : ℕ) : CatPrimitive [a, a + 1, a] [a + 1, a, a]
  | symm {u v : List ℕ} : CatPrimitive u v → CatPrimitive v u

theorem CatPrimitive.nonempty {u v : List ℕ} (h : CatPrimitive u v) :
    0 < u.length ∧ u.length = v.length := by
  induction h with
  | far h => simp
  | left a => simp
  | right a => simp
  | symm h ih => exact ⟨by omega, ih.2.symm⟩

theorem CatPrimitive.advance {u v : List ℕ} (h : CatPrimitive u v)
    (l : List ℕ) (μ : YoungDiagram) :
    catRun u.length ⟨l ++ u, μ⟩ = catRun u.length ⟨l ++ v, μ⟩ ∨
      ∃ u' v', CatPrimitive u' v' ∧
        catRun u.length ⟨l ++ u, μ⟩ = ⟨u' ++ l, μ⟩ ∧
        catRun u.length ⟨l ++ v, μ⟩ = ⟨v' ++ l, μ⟩ := by
  induction h with
  | @far a b hab =>
    rcases rawCat_far_two l μ.rowLen hab with heq | ⟨hl, hr⟩
    · left
      apply catEncoding_injective
      rw [catEncoding_run, catEncoding_run]
      exact heq
    · right
      refine ⟨[a + 1, b + 1], [b + 1, a + 1], .far hab.increment, ?_, ?_⟩
      · apply catEncoding_injective
        rw [catEncoding_run]
        exact hl
      · apply catEncoding_injective
        rw [catEncoding_run]
        exact hr
  | left a =>
    rcases rawCat_knuth_left_three l μ.rowLen a (fun _ _ h => μ.rowLen_anti _ _ h) with
      heq | ⟨hl, hr⟩
    · left
      apply catEncoding_injective
      rw [catEncoding_run, catEncoding_run]
      exact heq
    · right
      refine ⟨[a + 2, a + 1, a + 2], [a + 2, a + 2, a + 1], ?_, ?_, ?_⟩
      · simpa only [Nat.add_assoc] using CatPrimitive.left (a + 1)
      · apply catEncoding_injective
        rw [catEncoding_run]
        exact hl
      · apply catEncoding_injective
        rw [catEncoding_run]
        exact hr
  | right a =>
    rcases rawCat_knuth_right_three l μ.rowLen a (fun _ _ h => μ.rowLen_anti _ _ h) with
      heq | ⟨hl, hr⟩
    · left
      apply catEncoding_injective
      rw [catEncoding_run, catEncoding_run]
      exact heq
    · right
      refine ⟨[a + 1, a + 2, a + 1], [a + 2, a + 1, a + 1], ?_, ?_, ?_⟩
      · simpa only [Nat.add_assoc] using CatPrimitive.right (a + 1)
      · apply catEncoding_injective
        rw [catEncoding_run]
        exact hl
      · apply catEncoding_injective
        rw [catEncoding_run]
        exact hr
  | symm h ih =>
    have hlen := h.nonempty.2
    rw [← hlen]
    rcases ih with heq | ⟨u', v', h', hu', hv'⟩
    · exact Or.inl heq.symm
    · exact Or.inr ⟨v', u', .symm h', hv', hu'⟩

def catWindowRules : CatWindowRules where
  rel := CatPrimitive
  symm := CatPrimitive.symm
  nonempty h := h.nonempty.1
  length_eq h := h.nonempty.2
  advance h := h.advance

/-- A literal Knuth replacement of a natural-number word. -/
inductive KnuthEquivalent : List ℕ → List ℕ → Prop
  | refl (u) : KnuthEquivalent u u
  | symm {u v} : KnuthEquivalent u v → KnuthEquivalent v u
  | trans {u v w} : KnuthEquivalent u v → KnuthEquivalent v w → KnuthEquivalent u w
  | append {u v} (l r) : KnuthEquivalent u v → KnuthEquivalent (l ++ u ++ r) (l ++ v ++ r)
  | left {a b c : ℕ} : a < b → b ≤ c → KnuthEquivalent [b, a, c] [b, c, a]
  | right {a b c : ℕ} : a ≤ b → b < c → KnuthEquivalent [a, c, b] [c, a, b]

/-- All Knuth transformations preserve the actual terminating cyclic output. -/
theorem catStateOutput_knuth_iff {u v : List ℕ} (h : KnuthEquivalent u v)
    (l r : List ℕ) (μ ν : YoungDiagram) :
    CatStateOutput ⟨l ++ u ++ r, μ⟩ ν ↔ CatStateOutput ⟨l ++ v ++ r, μ⟩ ν := by
  induction h generalizing l r with
  | refl u => rfl
  | symm h ih => exact (ih l r).symm
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ l r).trans (ih₂ l r)
  | append l' r' h ih =>
    simpa only [List.append_assoc] using ih (l ++ l') (r' ++ r)
  | @left a b c hab hbc =>
    by_cases hac : a + 1 < c
    · have hfar := catWindowRules.output_iff (CatPrimitive.far (Or.inl hac))
        (l ++ [b]) r μ ν
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hfar
    · have hca : c = a + 1 := by omega
      have hba : b = a + 1 := by omega
      subst b
      subst c
      exact catWindowRules.output_iff (CatPrimitive.left a) l r μ ν
  | @right a b c hab hbc =>
    by_cases hac : a + 1 < c
    · have hfar := catWindowRules.output_iff (CatPrimitive.far (Or.inl hac))
        l ([b] ++ r) μ ν
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hfar
    · have hca : c = a + 1 := by omega
      have hba : b = a := by omega
      subst b
      subst c
      exact catWindowRules.output_iff (CatPrimitive.right a) l r μ ν

theorem catWordOutput_knuth_iff {u v : List ℕ} (h : KnuthEquivalent u v)
    (ν : YoungDiagram) : CatWordOutput u ν ↔ CatWordOutput v ν := by
  simpa only [CatWordOutput, CatStateOutput, List.nil_append, List.append_nil] using
    catStateOutput_knuth_iff h [] [] ⊥ ν

end HigherSpecht
end
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/KnuthRowInsertion.lean -/



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
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/KnuthRowTransducer.lean -/



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

def rowBumpWord (row : List ℕ) : List ℕ → List ℕ × List ℕ
  | [] => (row, [])
  | x :: w =>
      let first := rowBump x row
      let rest := rowBumpWord first.1 w
      (rest.1, first.2.toList ++ rest.2)

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
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/KnuthInsertionInvariant.lean -/



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
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/KnuthTableauReconstruction.lean -/



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
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/LascouxTableauCuts.lean -/



/-!
# Single-cell crystal cuts inside an actual semistandard tableau

The pinned `recut` construction supplies the complete row and column
inequalities.  Decreasing the `v`/`v+1` cut in row `r` is permitted precisely
when the cut is strictly above the two relevant lower bounds; increasing it
uses the two upper bounds.  The signature-selection argument must discharge
these bounds before this construction is applied to a crystal operator.

These are genuine tableaux of the original shape.  The Bender--Knuth involution
is not identified with the signature reflection anywhere in this file.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

def lowerTableauCut (T : SemistandardYoungTableau mu) (v r : ℕ) : ℕ → ℕ :=
  Function.update (fun i => T.rowCountLt i (v + 1)) r
    (T.rowCountLt r (v + 1) - 1)

def raiseTableauCut (T : SemistandardYoungTableau mu) (v r : ℕ) : ℕ → ℕ :=
  Function.update (fun i => T.rowCountLt i (v + 1)) r
    (T.rowCountLt r (v + 1) + 1)

theorem isCut_lowerTableauCut (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hlow : T.rowCountLt r v < T.rowCountLt r (v + 1))
    (hnext : T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1)) :
    T.IsCut v (lowerTableauCut T v r) where
  le_cut i := by
    by_cases hi : i = r
    · subst i
      simp only [lowerTableauCut, Function.update_self]
      omega
    · simpa only [lowerTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).le_cut i
  cut_le i := by
    by_cases hi : i = r
    · subst i
      simp only [lowerTableauCut, Function.update_self]
      exact (Nat.sub_le _ _).trans ((T.isCut_rowCountLt v).cut_le r)
    · simpa only [lowerTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).cut_le i
  succ_le_cut i := by
    by_cases hi : i = r
    · subst i
      simp only [lowerTableauCut, Function.update_self]
      omega
    · simpa only [lowerTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).succ_le_cut i
  cut_succ_le i := by
    by_cases hi : i + 1 = r
    · simp only [lowerTableauCut, hi, Function.update_self]
      have h := (T.isCut_rowCountLt v).cut_succ_le i
      rw [hi] at h
      exact (Nat.sub_le _ _).trans h
    · simpa only [lowerTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).cut_succ_le i

theorem isCut_raiseTableauCut (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hhigh : T.rowCountLt r (v + 1) < T.rowCountLt r (v + 2))
    (hprev : ∀ i, i + 1 = r → T.rowCountLt r (v + 1) < T.rowCountLt i v) :
    T.IsCut v (raiseTableauCut T v r) where
  le_cut i := by
    by_cases hi : i = r
    · subst i
      simp only [raiseTableauCut, Function.update_self]
      exact ((T.isCut_rowCountLt v).le_cut r).trans (Nat.le_succ _)
    · simpa only [raiseTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).le_cut i
  cut_le i := by
    by_cases hi : i = r
    · subst i
      simp only [raiseTableauCut, Function.update_self]
      exact hhigh
    · simpa only [raiseTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).cut_le i
  succ_le_cut i := by
    by_cases hi : i = r
    · subst i
      simp only [raiseTableauCut, Function.update_self]
      exact ((T.isCut_rowCountLt v).succ_le_cut r).trans (Nat.le_succ _)
    · simpa only [raiseTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).succ_le_cut i
  cut_succ_le i := by
    by_cases hi : i + 1 = r
    · simp only [raiseTableauCut, hi, Function.update_self]
      exact hprev i hi
    · simpa only [raiseTableauCut, Function.update_of_ne hi] using
        (T.isCut_rowCountLt v).cut_succ_le i

def lowerTableauAt (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hlow : T.rowCountLt r v < T.rowCountLt r (v + 1))
    (hnext : T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1)) :
    SemistandardYoungTableau mu :=
  T.recut v (lowerTableauCut T v r) (isCut_lowerTableauCut T v r hlow hnext)

def raiseTableauAt (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hhigh : T.rowCountLt r (v + 1) < T.rowCountLt r (v + 2))
    (hprev : ∀ i, i + 1 = r → T.rowCountLt r (v + 1) < T.rowCountLt i v) :
    SemistandardYoungTableau mu :=
  T.recut v (raiseTableauCut T v r) (isCut_raiseTableauCut T v r hhigh hprev)

theorem lowerTableauAt_cut (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hlow : T.rowCountLt r v < T.rowCountLt r (v + 1))
    (hnext : T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1)) (i : ℕ) :
    (lowerTableauAt T v r hlow hnext).rowCountLt i (v + 1) =
      lowerTableauCut T v r i :=
  SemistandardYoungTableau.rowCountLt_recut_succ
    (isCut_lowerTableauCut T v r hlow hnext) i

theorem raiseTableauAt_cut (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hhigh : T.rowCountLt r (v + 1) < T.rowCountLt r (v + 2))
    (hprev : ∀ i, i + 1 = r → T.rowCountLt r (v + 1) < T.rowCountLt i v) (i : ℕ) :
    (raiseTableauAt T v r hhigh hprev).rowCountLt i (v + 1) =
      raiseTableauCut T v r i :=
  SemistandardYoungTableau.rowCountLt_recut_succ
    (isCut_raiseTableauCut T v r hhigh hprev) i

theorem lowerTableauAt_other_letter (T : SemistandardYoungTableau mu) (v r x : ℕ)
    (hlow : T.rowCountLt r v < T.rowCountLt r (v + 1))
    (hnext : T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1))
    (hx : x ≠ v) (hx' : x ≠ v + 1) :
    (lowerTableauAt T v r hlow hnext).content x = T.content x :=
  SemistandardYoungTableau.content_recut_of_ne
    (isCut_lowerTableauCut T v r hlow hnext) hx hx'

theorem raiseTableauAt_other_letter (T : SemistandardYoungTableau mu) (v r x : ℕ)
    (hhigh : T.rowCountLt r (v + 1) < T.rowCountLt r (v + 2))
    (hprev : ∀ i, i + 1 = r → T.rowCountLt r (v + 1) < T.rowCountLt i v)
    (hx : x ≠ v) (hx' : x ≠ v + 1) :
    (raiseTableauAt T v r hhigh hprev).content x = T.content x :=
  SemistandardYoungTableau.content_recut_of_ne
    (isCut_raiseTableauCut T v r hhigh hprev) hx hx'

end HigherSpecht.Lascoux
end
end CanonicalSource9
