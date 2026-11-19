module
public import combinatorics_verification.part001
@[expose] public section

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingPrefixHeight\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingPrefixHeight"

/- Begin source MatchingPrefixHeight.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric
open TauCeti TauCeti.StandardYoungTableau

variable {μ : YoungDiagram}

theorem tableauNatRows_flatten_nodup (T : StandardYoungTableau μ) :
    (tableauNatRows T).flatten.Nodup := by
  unfold tableauNatRows
  rw [←List.map_flatten]
  exact ((T.flatten_toRows_perm).nodup_iff.mpr (List.nodup_finRange μ.card)).map
    (fun a b h => Fin.ext h)

theorem findIdx_tableauNatRows (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    (tableauNatRows T).findIdx? (fun row => (T c).val ∈ row) = some c.val.1 := by
  have hm (row : List (Fin μ.card)) : (T c).val ∈ row.map Fin.val ↔ T c ∈ row := by
    constructor
    · intro h
      obtain ⟨x,hx,hx'⟩ := List.mem_map.mp h
      have heq : x = T c := Fin.ext hx'
      exact heq ▸ hx
    · intro h
      exact List.mem_map.mpr ⟨T c,h,rfl⟩
  have hrow : YoungTableau.rowIndex T.toTableau (T c) = c.val.1 :=
    YoungTableau.rowIndex_apply T.toTableau c
  simpa only [tableauNatRows,List.findIdx?_map,Function.comp_def,hm,hrow]
    using T.findIdx?_mem_toRows (T c)

theorem rowDescends_tableauNatRows_iff (T : StandardYoungTableau μ) (c d : ↥μ.cells) :
    RowDescends (T c).val (T d).val (tableauNatRows T) ↔ c.val.1 < d.val.1 :=
  rowDescends_iff_of_findIdx? (tableauNatRows_flatten_nodup T)
    (findIdx_tableauNatRows T c) (findIdx_tableauNatRows T d)

theorem matching_endpoint_of_lt {T : StandardYoungTableau μ} {w : List (ℕ × ℕ)}
    (hT : pairInsertList w = tableauNatRows T) {x : ℕ} (hx : x < μ.card) :
    x ∈ endpointWord w := by
  rw [←mem_rowWordRows_pairInsertList,hT]
  exact mem_rowWordRows_tableauNatRows T hx

def PrefixExtension.cell {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) (S : StandardYoungTableau E.shape) (i : Fin q) :
    ↥E.shape.cells := S.toTableau.symm ⟨i.val,by rw [E.card]; exact i.isLt⟩

theorem PrefixExtension.cell_label {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) (S : StandardYoungTableau E.shape) (i : Fin q) :
    (S (E.cell S i)).val = i.val := by
  change (S.toTableau (S.toTableau.symm _)).val = _
  rw [Equiv.apply_symm_apply]

def PrefixExtension.fullCell {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) (c : ↥E.shape.cells) : ↥μ.cells :=
  ⟨c.val,E.shape_le c.property⟩

theorem PrefixExtension.fullCell_label {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) (S : StandardYoungTableau E.shape) (c : ↥E.shape.cells) :
    ((E.extend S) (E.fullCell c)).val = (S c).val := by
  have hh := E.inside S c.val c.property
  simpa only [tableauEntry_of_mem _ (E.shape_le c.property),
    tableauEntry_of_mem _ c.property,PrefixExtension.fullCell] using hh

theorem PrefixExtension.rowDescends_iff {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) (S : StandardYoungTableau E.shape) (i j : Fin q) :
    RowDescends i.val j.val (tableauNatRows (E.extend S)) ↔
      (E.cell S i).val.1 < (E.cell S j).val.1 := by
  have hi := E.fullCell_label S (E.cell S i)
  have hj := E.fullCell_label S (E.cell S j)
  rw [E.cell_label S i] at hi
  rw [E.cell_label S j] at hj
  have hh := rowDescends_tableauNatRows_iff (E.extend S)
    (E.fullCell (E.cell S i)) (E.fullCell (E.cell S j))
  rw [hi,hj] at hh
  exact hh

theorem colSuperstandard_firstColumn (ν : YoungDiagram) (i : ℕ)
    (hi : i < ν.colLen 0) :
    (colSuperstandard ν ⟨(i,0),YoungDiagram.mem_iff_lt_colLen.mpr hi⟩).val = i := by
  simp only [colSuperstandard_apply_val,Prod.swap,YoungDiagram.readingIndex_zero]

theorem PrefixExtension.column_chain {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    (hT : pairInsertList w = tableauNatRows (E.extend (colSuperstandard E.shape))) :
    MatchingChains.IsChain (partnerMap w) (Finset.range (E.shape.colLen 0)) ∧
      ∀ i ∈ Finset.range (E.shape.colLen 0), i < q := by
  let S := colSuperstandard E.shape
  let U := E.extend S
  have hlabel (i : ℕ) (hi : i < E.shape.colLen 0) :
      (U (E.fullCell ⟨(i,0),YoungDiagram.mem_iff_lt_colLen.mpr hi⟩)).val = i := by
    rw [E.fullCell_label]
    exact colSuperstandard_firstColumn E.shape i hi
  have hm : ∀ i < E.shape.colLen 0, i ∈ endpointWord w := by
    intro i hi
    apply matching_endpoint_of_lt hT
    have hh := (U (E.fullCell ⟨(i,0),YoungDiagram.mem_iff_lt_colLen.mpr hi⟩)).isLt
    simpa only [hlabel i hi] using hh
  have hd : ∀ i, i + 1 < E.shape.colLen 0 →
      RowDescends i (i + 1) (pairInsertList w) := by
    intro i hi
    have hi' : i < E.shape.colLen 0 := by omega
    rw [hT]
    have hh := (rowDescends_tableauNatRows_iff U
      (E.fullCell ⟨(i,0),YoungDiagram.mem_iff_lt_colLen.mpr hi'⟩)
      (E.fullCell ⟨(i+1,0),YoungDiagram.mem_iff_lt_colLen.mpr hi⟩)).mpr
      (by change i < i + 1; omega)
    simpa only [hlabel i hi',hlabel (i+1) hi] using hh
  refine ⟨hw.prefix_chain_of_descents _ hm hd,?_⟩
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hh := (S ⟨(i,0),YoungDiagram.mem_iff_lt_colLen.mpr hi'⟩).isLt
  have hentry : (S ⟨(i,0),YoungDiagram.mem_iff_lt_colLen.mpr hi'⟩).val = i :=
    colSuperstandard_firstColumn E.shape i hi'
  rw [hentry] at hh
  exact hh.trans_eq E.card

theorem rowSuperstandard_row_between (ν : YoungDiagram) (a b c : ↥ν.cells)
    (hab : a.val.1 = b.val.1)
    (hac : (rowSuperstandard ν a).val ≤ (rowSuperstandard ν c).val)
    (hcb : (rowSuperstandard ν c).val ≤ (rowSuperstandard ν b).val) :
    c.val.1 = a.val.1 := by
  simp only [rowSuperstandard_apply_val] at hac hcb
  rcases lt_trichotomy c.val.1 a.val.1 with h | h | h
  · have hh := YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
        (d := a.val) c.property h
    omega
  · exact h
  · have hh := YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
        (d := c.val) b.property (by omega : b.val.1 < c.val.1)
    omega

theorem PrefixExtension.row_chain_card_le {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    (hT : pairInsertList w = tableauNatRows (E.extend (rowSuperstandard E.shape)))
    {C : Finset ℕ} (hC : MatchingChains.IsChain (partnerMap w) C)
    (hrows : ∀ i ∈ C, i < q) : C.card ≤ E.shape.colLen 0 := by
  classical
  let S := rowSuperstandard E.shape
  let row (i : ℕ) (hi : i < q) : ℕ := (E.cell S ⟨i,hi⟩).val.1
  have hlt (i : ℕ) (hi : i < q) : row i hi < E.shape.colLen 0 :=
    E.shape.lt_colLen_zero_of_mem (E.cell S ⟨i,hi⟩).property
  have hneq : ∀ (i : ℕ) (hi : i ∈ C) (j : ℕ) (hj : j ∈ C),
      i < j → row i (hrows i hi) ≠ row j (hrows j hj) := by
    intro i hi j hj hij heq
    have hiq := hrows i hi
    have hjq := hrows j hj
    have hbetween (k : ℕ) (hik : i ≤ k) (hkj : k ≤ j) :
        row k (by omega) = row i hiq := by
      apply rowSuperstandard_row_between E.shape
        (E.cell S ⟨i,hiq⟩) (E.cell S ⟨j,hjq⟩) (E.cell S ⟨k,by omega⟩) heq
      · simpa only [←show S = rowSuperstandard E.shape from rfl,E.cell_label] using hik
      · simpa only [←show S = rowSuperstandard E.shape from rfl,E.cell_label] using hkj
    have hm : ∀ k, i ≤ k → k ≤ j → k ∈ endpointWord w := by
      intro k hik hkj
      apply matching_endpoint_of_lt hT
      have hc := E.fullCell_label S (E.cell S ⟨k,by omega⟩)
      rw [E.cell_label] at hc
      change ((E.extend S) (E.fullCell (E.cell S ⟨k,by omega⟩))).val = k at hc
      have hh := ((E.extend S) (E.fullCell (E.cell S ⟨k,by omega⟩))).isLt
      rw [hc] at hh
      exact hh
    have hd : ∀ k, i ≤ k → k < j → ¬RowDescends k (k+1) (pairInsertList w) := by
      intro k hik hkj
      rw [hT]
      have hiff := E.rowDescends_iff S ⟨k,by omega⟩ ⟨k+1,by omega⟩
      change (RowDescends k (k+1) (tableauNatRows (E.extend S)) ↔
        row k _ < row (k+1) _) at hiff
      rw [hiff,hbetween k hik (by omega),hbetween (k+1) (by omega) (by omega)]
      exact lt_irrefl _
    have hsub : ({i,j} : Finset ℕ) ⊆ C := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hi
      · have he := Finset.mem_singleton.mp hk
        exact he.symm ▸ hj
    have hcard := hw.chain_card_le_one_of_no_descents hm hd (hC.mono hsub) (by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · omega
      · have he := Finset.mem_singleton.mp hk
        omega)
    have he : i = j := (Finset.card_le_one.mp hcard) i (by simp) j (by simp)
    omega
  let f : {i // i ∈ C} → Fin (E.shape.colLen 0) :=
    fun i => ⟨row i.val (hrows i.val i.property),hlt i.val (hrows i.val i.property)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hrow := congrArg Fin.val hij
    apply Subtype.ext
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact False.elim (hneq i.val i.property j.val j.property h hrow)
    · exact h
    · exact False.elim (hneq j.val j.property i.val i.property h hrow.symm)
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Prefix-height identity for every standard matching, in the exact attained
maximum form: there is a chain of the prefix height and every chain is no longer.
`PrefixExtension.mem_shape_iff` identifies the height with the original tableau's
subdiagram of labels below `q`. -/
theorem MatchingWord.prefix_height {T : StandardYoungTableau μ} {q : ℕ}
    {w : List (ℕ × ℕ)} (hw : MatchingWord w) (hT : pairInsertList w = tableauNatRows T)
    (hq : q ≤ μ.card) (E : PrefixExtension T q) :
    (∃ C : Finset ℕ, MatchingChains.IsChain (partnerMap w) C ∧
      C.card = E.shape.colLen 0 ∧ ∀ i ∈ C, i < q) ∧
    (∀ C : Finset ℕ, MatchingChains.IsChain (partnerMap w) C →
      (∀ i ∈ C, i < q) → C.card ≤ E.shape.colLen 0) := by
  constructor
  · obtain ⟨v,hv,hvT,hprefix,_⟩ := E.lift_matching hq (colSuperstandard E.shape) hw hT
    obtain ⟨hchain,hrows⟩ := E.column_chain hv hvT
    exact (hprefix (E.shape.colLen 0)).mpr
      ⟨Finset.range (E.shape.colLen 0),hchain,Finset.card_range _,hrows⟩
  · intro C hC hrows
    obtain ⟨v,hv,hvT,hprefix,_⟩ := E.lift_matching hq (rowSuperstandard E.shape) hw hT
    obtain ⟨D,hD,hcard,hDrows⟩ := (hprefix C.card).mp ⟨C,hC,rfl,hrows⟩
    have hbound := E.row_chain_card_le hv hvT hD hDrows
    omega

end FourPapers.Symmetric
end
/- End source MatchingPrefixHeight.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingNestedBlocks\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingNestedBlocks"

/- Begin source MatchingNestedBlocks.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourPapers.Symmetric
open TauCeti

/-- Append two columns to the first `h` rows, creating rows when needed. -/
def appendColumnPair (a b : ℕ) : ℕ → List (List ℕ) → List (List ℕ)
  | 0, rows => rows
  | h + 1, [] => [a,b] :: appendColumnPair (a+1) (b+1) h []
  | h + 1, row :: rows => (row ++ [a,b]) :: appendColumnPair (a+1) (b+1) h rows

/-- A nested block in increasing-upper-endpoint order. In the matching block
used in Section 2.2, `b = a+h`. -/
def nestedWord (a b : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | h + 1 => nestedWord (a+1) b h ++ [(a,b+h)]

theorem pairInsert_appendColumnPair (a b h : ℕ) (rows : List (List ℕ))
    (hsmall : ∀ x ∈ rows.flatten, x ≤ a) :
    pairInsert a (b+h) (appendColumnPair (a+1) b h rows) =
      appendColumnPair a b (h+1) rows := by
  induction h generalizing a b rows with
  | zero =>
    cases rows with
    | nil => simp only [appendColumnPair,pairInsert_nil,Nat.add_zero]
    | cons row rows =>
      have hr : ∀ x ∈ row, x ≤ a := fun x hx => hsmall x (List.mem_append_left _ hx)
      have hbump := rowBump_of_forall_le a row hr
      rw [appendColumnPair,pairInsert_cons_of_none rows (by rw [hbump]),hbump]
      simp only [appendColumnPair,Prod.fst,Nat.add_zero,List.append_assoc,List.singleton_append]
  | succ h ih =>
    cases rows with
    | nil =>
      have hbump : rowBump a [a+1,b] = ([a,b],some (a+1)) := by
        rw [rowBump_cons_of_lt [b] (by omega)]
      rw [appendColumnPair,pairInsert_cons_of_some _ (by rw [hbump]),hbump]
      simp only [Prod.fst]
      have hh := ih (a+1) (b+1) [] (by simp)
      have hnum : b + (h+1) = (b+1)+h := by omega
      rewrite [hnum,hh]
      rfl
    | cons row rows =>
      have hr : ∀ x ∈ row, x ≤ a := fun x hx => hsmall x (List.mem_append_left _ hx)
      have ht : ∀ x ∈ rows.flatten, x ≤ a+1 := by
        intro x hx
        have := hsmall x (List.mem_append_right _ hx)
        omega
      have hbump : rowBump a (row ++ [a+1,b]) = (row ++ [a,b],some (a+1)) := by
        rw [rowBump_append a row [a+1,b] hr,rowBump_cons_of_lt [b] (by omega)]
      rw [appendColumnPair,pairInsert_cons_of_some _ (by rw [hbump]),hbump]
      simp only [Prod.fst]
      have hnum : b + (h+1) = (b+1)+h := by omega
      rewrite [hnum,ih (a+1) (b+1) rows ht]
      rfl

/-- Exact unbounded insertion calculation for a nested block, including its
interaction with every previously inserted smaller label. -/
theorem pairInsertList_nestedWord (a b h : ℕ) (rows : List (List ℕ))
    (hsmall : ∀ x ∈ rows.flatten, x ≤ a) :
    pairInsertList (nestedWord a b h) rows = appendColumnPair a b h rows := by
  induction h generalizing a rows with
  | zero => rfl
  | succ h ih =>
    rw [nestedWord,pairInsertList_append,pairInsertList_cons,pairInsertList_nil,
      ih (a+1) rows (by intro x hx; have := hsmall x hx; omega)]
    exact pairInsert_appendColumnPair a b h rows hsmall

theorem mem_nestedWord_iff (a b h : ℕ) (p : ℕ × ℕ) :
    p ∈ nestedWord a b h ↔ ∃ i < h, p = (a + h - 1 - i,b+i) := by
  induction h generalizing a with
  | zero => simp [nestedWord]
  | succ h ih =>
    rw [nestedWord,List.mem_append,ih,List.mem_singleton]
    constructor
    · rintro (⟨i,hi,rfl⟩ | rfl)
      · refine ⟨i,by omega,?_⟩
        congr 1
        omega
      · exact ⟨h,by omega,by congr 1 <;> omega⟩
    · rintro ⟨i,hi,rfl⟩
      by_cases hie : i = h
      · right
        subst i
        congr 1
        omega
      · left
        refine ⟨i,by omega,?_⟩
        congr 1
        omega

theorem nestedWord_length (a b h : ℕ) : (nestedWord a b h).length = h := by
  induction h generalizing a with
  | zero => rfl
  | succ h ih => simp only [nestedWord,List.length_append,List.length_singleton,ih]

theorem nestedWord_endpoint_bounds {a b h x : ℕ} (hab : a+h ≤ b)
    (hx : x ∈ endpointWord (nestedWord a b h)) :
    (a ≤ x ∧ x < a+h) ∨ (b ≤ x ∧ x < b+h) := by
  obtain ⟨p,hp,hx⟩ := mem_endpointWord.mp hx
  obtain ⟨i,hi,rfl⟩ := (mem_nestedWord_iff a b h p).mp hp
  rcases hx with hx | hx
  · left; simp only [Prod.fst] at hx; omega
  · right; simp only [Prod.snd] at hx; omega

theorem matchingWord_nestedWord (a b h : ℕ) (hab : a+h ≤ b) :
    MatchingWord (nestedWord a b h) := by
  induction h generalizing a with
  | zero => exact matchingWord_nil
  | succ h ih =>
    have hab' : a+1+h ≤ b := by omega
    have hw := ih (a+1) hab'
    constructor
    · intro p hp
      obtain ⟨i,hi,rfl⟩ := (mem_nestedWord_iff a b (h+1) p).mp hp
      simp only [Prod.fst,Prod.snd]
      omega
    · rw [nestedWord,List.pairwise_append]
      refine ⟨hw.ordered,by simp,?_⟩
      intro p hp q hq
      have hq' := List.mem_singleton.mp hq
      subst q
      obtain ⟨i,hi,rfl⟩ := (mem_nestedWord_iff (a+1) b h p).mp hp
      simp only [Prod.snd]
      omega
    · rw [nestedWord,endpointWord_append]
      apply List.Nodup.append hw.distinct
      · change ([a,b+h] : List ℕ).Nodup
        apply List.nodup_cons.mpr
        refine ⟨?_,List.nodup_singleton _⟩
        intro hm
        have he : a = b+h := List.mem_singleton.mp hm
        omega
      · intro x hx hx'
        have hbnd := nestedWord_endpoint_bounds hab' hx
        change x ∈ [a,b+h] at hx'
        rcases List.mem_cons.mp hx' with he | hm
        · omega
        · have he : x = b+h := List.mem_singleton.mp hm
          omega

theorem partnerMap_nestedWord_lower (a h i : ℕ) (hi : i < h) :
    partnerMap (nestedWord a (a+h) h) (a+i) = a+2*h-1-i := by
  have hw := matchingWord_nestedWord a (a+h) h le_rfl
  apply hw.partnerMap_eq
  left
  apply (mem_nestedWord_iff a (a+h) h _).mpr
  refine ⟨h-1-i,by omega,?_⟩
  apply Prod.ext <;> simp only [Prod.fst,Prod.snd] <;> omega

/-- All nested edges form one admissible chain when oriented from the lower
half of their block. Its cardinality is exactly the number of edges. -/
theorem nestedWord_lower_chain (a h : ℕ) :
    MatchingChains.IsChain (partnerMap (nestedWord a (a+h) h)) (Finset.Ico a (a+h)) := by
  constructor
  · intro r hr s hs hrs
    obtain ⟨har,hrh⟩ := Finset.mem_Ico.mp hr
    obtain ⟨has,hsh⟩ := Finset.mem_Ico.mp hs
    have hir : r-a < h := by omega
    have his : s-a < h := by omega
    have hpr := partnerMap_nestedWord_lower a h (r-a) hir
    have hps := partnerMap_nestedWord_lower a h (s-a) his
    have hrr : a+(r-a) = r := by omega
    have hss : a+(s-a) = s := by omega
    rw [hrr] at hpr
    rw [hss] at hps
    omega
  · intro r hr hbad
    obtain ⟨har,hrh⟩ := Finset.mem_Ico.mp hr
    have hp := partnerMap_nestedWord_lower a h (r-a) (by omega)
    have hrr : a+(r-a) = r := by omega
    rw [hrr] at hp
    have hb := (Finset.mem_Ico.mp hbad).2
    omega

theorem nestedWord_endpoint_interval {a h x : ℕ}
    (hx : x ∈ endpointWord (nestedWord a (a+h) h)) : a ≤ x ∧ x < a+2*h := by
  have hh := nestedWord_endpoint_bounds (a := a) (b := a+h) le_rfl hx
  omega

theorem nestedWord_chain_card_le {a h : ℕ} {C : Finset ℕ}
    (hC : MatchingChains.IsChain (partnerMap (nestedWord a (a+h) h)) C) :
    C.card ≤ h := by
  have hw := matchingWord_nestedWord a (a+h) h le_rfl
  have hs : MatchingChains.endpoints (partnerMap (nestedWord a (a+h) h)) C ⊆
      Finset.Ico a (a+2*h) := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact Finset.mem_Ico.mpr (nestedWord_endpoint_interval (hC.rows_mem_endpoints hr))
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_Ico.mpr (nestedWord_endpoint_interval
        (partnerMap_spec (hC.rows_mem_endpoints hs)).mem_right)
  have hle := Finset.card_le_card hs
  rw [(MatchingChains.oneUse_iff_endpoints_card hw.partnerMap_involutive C).mp hC.oneUse,
    Nat.card_Ico] at hle
  omega

/-- Every single nested block has the exact chain maximum predicted by its
two-column rectangle, for every block size including zero. -/
theorem nestedWord_chain_maximum (a h : ℕ) :
    (∃ C : Finset ℕ, MatchingChains.IsChain (partnerMap (nestedWord a (a+h) h)) C ∧
      C.card = h) ∧
    (∀ C : Finset ℕ, MatchingChains.IsChain (partnerMap (nestedWord a (a+h) h)) C →
      C.card ≤ h) := by
  refine ⟨⟨Finset.Ico a (a+h),nestedWord_lower_chain a h,?_⟩,?_⟩
  · rw [Nat.card_Ico]
    omega
  · intro C hC
    exact nestedWord_chain_card_le hC

/-- Successive disjoint nested blocks, with every endpoint in a later block
larger than every endpoint in an earlier block. -/
def nestedBlocks (s : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | h :: hs => nestedWord s (s+h) h ++ nestedBlocks (s+2*h) hs

theorem nestedBlocks_endpoint_bounds {s x : ℕ} {hs : List ℕ}
    (hx : x ∈ endpointWord (nestedBlocks s hs)) : s ≤ x ∧ x < s+2*hs.sum := by
  induction hs generalizing s with
  | nil => simp [nestedBlocks,endpointWord] at hx
  | cons h hs ih =>
    rw [nestedBlocks,endpointWord_append,List.mem_append] at hx
    simp only [List.sum_cons]
    rcases hx with hx | hx
    · have hh := nestedWord_endpoint_interval hx
      omega
    · have hh := ih hx
      omega

theorem nestedBlocks_matching (s : ℕ) (hs : List ℕ) : MatchingWord (nestedBlocks s hs) := by
  induction hs generalizing s with
  | nil => exact matchingWord_nil
  | cons h hs ih =>
    have hw := matchingWord_nestedWord s (s+h) h le_rfl
    have hv := ih (s+2*h)
    constructor
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hw.lower_lt_upper p hp
      · exact hv.lower_lt_upper p hp
    · rw [nestedBlocks,List.pairwise_append]
      refine ⟨hw.ordered,hv.ordered,?_⟩
      intro p hp q hq
      have hp' : p.2 ∈ endpointWord (nestedWord s (s+h) h) :=
        mem_endpointWord.mpr ⟨p,hp,Or.inr rfl⟩
      have hq' : q.2 ∈ endpointWord (nestedBlocks (s+2*h) hs) :=
        mem_endpointWord.mpr ⟨q,hq,Or.inr rfl⟩
      have hpb := nestedWord_endpoint_interval hp'
      have hqb := nestedBlocks_endpoint_bounds hq'
      omega
    · rw [nestedBlocks,endpointWord_append]
      apply List.Nodup.append hw.distinct hv.distinct
      intro x hx hx'
      have hxb := nestedWord_endpoint_interval hx
      have hxb' := nestedBlocks_endpoint_bounds hx'
      omega

theorem nestedBlocks_length (s : ℕ) (hs : List ℕ) : (nestedBlocks s hs).length = hs.sum := by
  induction hs generalizing s with
  | nil => rfl
  | cons h hs ih => simp only [nestedBlocks,List.length_append,nestedWord_length,ih,List.sum_cons]

theorem Partners.of_sublist {w v : List (ℕ × ℕ)} (hsub : w.Sublist v)
    {x y : ℕ} (h : Partners w x y) : Partners v x y := by
  rcases h with h | h
  · exact Or.inl (hsub.subset h)
  · exact Or.inr (hsub.subset h)

theorem MatchingWord.partnerMap_of_sublist {w v : List (ℕ × ℕ)}
    (hv : MatchingWord v) (hsub : w.Sublist v) {x : ℕ} (hx : x ∈ endpointWord w) :
    partnerMap v x = partnerMap w x :=
  hv.partnerMap_eq ((partnerMap_spec hx).of_sublist hsub)

def nestedBlocksRows (s : ℕ) : List ℕ → List (List ℕ) → List (List ℕ)
  | [], rows => rows
  | h :: hs, rows => nestedBlocksRows (s+2*h) hs (appendColumnPair s (s+h) h rows)

theorem pairInsertList_nestedBlocks (s : ℕ) (hs : List ℕ) (rows : List (List ℕ))
    (hsmall : ∀ x ∈ rows.flatten, x < s) :
    pairInsertList (nestedBlocks s hs) rows = nestedBlocksRows s hs rows := by
  induction hs generalizing s rows with
  | nil => rfl
  | cons h hs ih =>
    have hb : ∀ x ∈ (appendColumnPair s (s+h) h rows).flatten, x < s+2*h := by
      intro x hx
      rw [←pairInsertList_nestedWord s (s+h) h rows (fun z hz => (hsmall z hz).le)] at hx
      have hm := (flatten_pairInsertList_perm (nestedWord s (s+h) h) rows).mem_iff.mp hx
      rcases List.mem_append.mp hm with hm | hm
      · exact (nestedWord_endpoint_interval hm).2
      · have hh := hsmall x hm
        omega
    rewrite [nestedBlocks,pairInsertList_append,pairInsertList_nestedWord s (s+h) h rows
      (fun z hz => (hsmall z hz).le),ih _ _ hb]
    rfl

/-- The word of a particular block occurs literally as a sublist of the full
canonical matching word, at the offset determined by the preceding block sizes. -/
theorem nestedWord_sublist_nestedBlocks (s : ℕ) (hs : List ℕ) (i : ℕ) :
    (nestedWord (s+2*(hs.take i).sum)
      (s+2*(hs.take i).sum+hs.getD i 0) (hs.getD i 0)).Sublist (nestedBlocks s hs) := by
  induction hs generalizing s i with
  | nil => simp [nestedWord,nestedBlocks]
  | cons h hs ih =>
    cases i with
    | zero =>
      simp only [List.take_zero,List.sum_nil,Nat.mul_zero,Nat.add_zero,List.getD_cons_zero]
      exact List.sublist_append_left _ _
    | succ i =>
      have hh := ih (s+2*h) i
      have heq : s+2*(h+(hs.take i).sum) = s+2*h+2*(hs.take i).sum := by omega
      simp only [List.take_succ_cons,List.sum_cons,List.getD_cons_succ,heq]
      exact hh.trans (List.sublist_append_right _ _)

end FourPapers.Symmetric
end
/- End source MatchingNestedBlocks.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingPackingBounds\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingPackingBounds"

/- Begin source MatchingPackingBounds.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false

namespace FourPapers.Symmetric.MatchingChains

/-- Among sets of a fixed cardinality, the initial interval maximizes the sum
of a nonnegative decreasing sequence. No support bound is required. -/
theorem antitone_sum_finset_le_range_card (H : ℕ → ℕ) (hH : Antitone H)
    (S : Finset ℕ) :
    (∑ i ∈ S, H i) ≤ ∑ i ∈ Finset.range S.card, H i := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases he : S = ∅
  · subst S
    simp
  have hn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  let m := S.max' hn
  have hm : m ∈ S := Finset.max'_mem S hn
  have hsub : S ⊆ Finset.range (m + 1) := by
    intro i hi
    apply Finset.mem_range.mpr
    have hh : i ≤ m := Finset.le_max' S i hi
    omega
  have hbound : S.card ≤ m + 1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hc : (S.erase m).card + 1 = S.card := Finset.card_erase_add_one hm
  have hcm : (S.erase m).card ≤ m := by omega
  have hi := ih (S.erase m) (Finset.erase_ssubset hm)
  calc
    (∑ i ∈ S, H i) = (∑ i ∈ S.erase m, H i) + H m :=
      (Finset.sum_erase_add S H hm).symm
    _ ≤ (∑ i ∈ Finset.range (S.erase m).card, H i) + H (S.erase m).card :=
      Nat.add_le_add hi (hH hcm)
    _ = ∑ i ∈ Finset.range S.card, H i := by
      rw [←hc,Finset.sum_range_succ]

/-- The top `k` terms bound the sum over any set of at most `k` indices. -/
theorem antitone_sum_finset_le_range (H : ℕ → ℕ) (hH : Antitone H)
    (S : Finset ℕ) (k : ℕ) (hk : S.card ≤ k) :
    (∑ i ∈ S, H i) ≤ ∑ i ∈ Finset.range k, H i :=
  (antitone_sum_finset_le_range_card H hH S).trans
    (Finset.sum_le_sum_of_subset (Finset.range_mono hk))

end FourPapers.Symmetric.MatchingChains
end
/- End source MatchingPackingBounds.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingNestedPacking\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingNestedPacking"

/- Begin source MatchingNestedPacking.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric
open scoped BigOperators

theorem sum_take_succ_getD (hs : List ℕ) (i : ℕ) :
    (hs.take (i+1)).sum = (hs.take i).sum + hs.getD i 0 := by
  induction hs generalizing i with
  | nil => simp
  | cons h hs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons,List.sum_cons,List.getD_cons_succ,ih]
      omega

def blockStart (s : ℕ) (hs : List ℕ) (i : ℕ) : ℕ := s+2*(hs.take i).sum

theorem blockStart_succ (s : ℕ) (hs : List ℕ) (i : ℕ) :
    blockStart s hs (i+1) = blockStart s hs i + 2*hs.getD i 0 := by
  unfold blockStart
  rw [sum_take_succ_getD]
  omega

theorem blockStart_zero (s : ℕ) (hs : List ℕ) : blockStart s hs 0 = s := by
  simp [blockStart]

theorem blockStart_cons_succ (s h : ℕ) (hs : List ℕ) (i : ℕ) :
    blockStart s (h::hs) (i+1) = blockStart (s+2*h) hs i := by
  simp only [blockStart,List.take_succ_cons,List.sum_cons]
  omega

theorem blockStart_monotone (s : ℕ) (hs : List ℕ) : Monotone (blockStart s hs) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [blockStart_succ]
  omega

def InNestedBlock (s : ℕ) (hs : List ℕ) (i x : ℕ) : Prop :=
  blockStart s hs i ≤ x ∧ x < blockStart s hs (i+1)

theorem InNestedBlock.order {s i j x y : ℕ} {hs : List ℕ}
    (hi : InNestedBlock s hs i x) (hj : InNestedBlock s hs j y) (hij : i < j) : x < y := by
  have hb := blockStart_monotone s hs (by omega : i+1 ≤ j)
  exact hi.2.trans_le (hb.trans hj.1)

theorem InNestedBlock.unique {s i j x : ℕ} {hs : List ℕ}
    (hi : InNestedBlock s hs i x) (hj : InNestedBlock s hs j x) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim ((lt_irrefl x) (hi.order hj h))
  · exact h
  · exact False.elim ((lt_irrefl x) (hj.order hi h))

theorem nestedBlocks_partners_block {s x y : ℕ} {hs : List ℕ}
    (h : Partners (nestedBlocks s hs) x y) :
    ∃ i < hs.length, InNestedBlock s hs i x ∧ InNestedBlock s hs i y := by
  induction hs generalizing s with
  | nil => simp [nestedBlocks,Partners] at h
  | cons a hs ih =>
    rw [nestedBlocks,partners_append] at h
    rcases h with h | h
    · refine ⟨0,by simp,?_,?_⟩
      · have hx := nestedWord_endpoint_interval h.mem_left
        simpa only [InNestedBlock,blockStart_zero,blockStart_cons_succ] using hx
      · have hy := nestedWord_endpoint_interval h.mem_right
        simpa only [InNestedBlock,blockStart_zero,blockStart_cons_succ] using hy
    · obtain ⟨i,hi,hx,hy⟩ := ih h
      refine ⟨i+1,by simp only [List.length_cons]; omega,?_,?_⟩
      · simpa only [InNestedBlock,blockStart_cons_succ] using hx
      · simpa only [InNestedBlock,blockStart_cons_succ] using hy

/-- Every nonempty admissible chain belongs to one block. The proof uses the
actual partner relation: both coordinates increase between different blocks. -/
theorem nestedBlocks_chain_block {s : ℕ} {hs : List ℕ} {C : Finset ℕ}
    (hC : MatchingChains.IsChain (partnerMap (nestedBlocks s hs)) C) (hne : C.Nonempty) :
    ∃ i < hs.length, ∀ r ∈ C,
      InNestedBlock s hs i r ∧ InNestedBlock s hs i (partnerMap (nestedBlocks s hs) r) := by
  obtain ⟨r,hr⟩ := hne
  obtain ⟨i,hi,hri,hyi⟩ := nestedBlocks_partners_block
    (partnerMap_spec (hC.rows_mem_endpoints hr))
  refine ⟨i,hi,?_⟩
  intro t ht
  obtain ⟨j,hj,htj,hyj⟩ := nestedBlocks_partners_block
    (partnerMap_spec (hC.rows_mem_endpoints ht))
  have heq : i = j := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have hrt := hri.order htj hij
      have hyrt := hyi.order hyj hij
      have hh := hC.decreasing r hr t ht hrt
      omega
    · exact hij
    · have htr := htj.order hri hji
      have hytr := hyj.order hyi hji
      have hh := hC.decreasing t ht r hr htr
      omega
  exact heq.symm ▸ ⟨htj,hyj⟩

theorem nestedBlocks_lower_chain (s : ℕ) (hs : List ℕ) (i : ℕ) :
    MatchingChains.IsChain (partnerMap (nestedBlocks s hs))
      (Finset.Ico (blockStart s hs i) (blockStart s hs i + hs.getD i 0)) := by
  let a := blockStart s hs i
  let h := hs.getD i 0
  have hC := nestedWord_lower_chain a h
  apply hC.congr_on
  intro r hr
  exact ((nestedBlocks_matching s hs).partnerMap_of_sublist
    (nestedWord_sublist_nestedBlocks s hs i) (hC.rows_mem_endpoints hr)).symm

theorem nestedBlocks_lower_endpoints {s i x : ℕ} {hs : List ℕ}
    (hx : x ∈ MatchingChains.endpoints (partnerMap (nestedBlocks s hs))
      (Finset.Ico (blockStart s hs i) (blockStart s hs i+hs.getD i 0))) :
    InNestedBlock s hs i x := by
  let a := blockStart s hs i
  let h := hs.getD i 0
  have hC := nestedWord_lower_chain a h
  have heq (r : ℕ) (hr : r ∈ Finset.Ico a (a+h)) :
      partnerMap (nestedBlocks s hs) r = partnerMap (nestedWord a (a+h) h) r :=
    (nestedBlocks_matching s hs).partnerMap_of_sublist
      (nestedWord_sublist_nestedBlocks s hs i) (hC.rows_mem_endpoints hr)
  have hb : a ≤ x ∧ x < a+2*h := by
    rcases Finset.mem_union.mp hx with hx | hx
    · have hh := Finset.mem_Ico.mp hx
      omega
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
      rw [heq r hr]
      exact nestedWord_endpoint_interval (partnerMap_spec (hC.rows_mem_endpoints hr)).mem_right
  simpa only [InNestedBlock,blockStart_succ] using hb

def nestedBlocksPacking (s : ℕ) (hs : List ℕ) (k : ℕ) : Fin k → Finset ℕ :=
  fun i => Finset.Ico (blockStart s hs i.val) (blockStart s hs i.val+hs.getD i.val 0)

theorem nestedBlocksPacking_isPacking (s : ℕ) (hs : List ℕ) (k : ℕ) :
    MatchingChains.IsPacking (partnerMap (nestedBlocks s hs)) (nestedBlocksPacking s hs k) := by
  constructor
  · intro i
    exact nestedBlocks_lower_chain s hs i.val
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have heq := (nestedBlocks_lower_endpoints hx).unique (nestedBlocks_lower_endpoints hx')
    exact hij (Fin.ext heq)

theorem nestedBlocksPacking_size (s : ℕ) (hs : List ℕ) (k : ℕ) :
    MatchingChains.packingSize (nestedBlocksPacking s hs k) =
      ∑ i ∈ Finset.range k, hs.getD i 0 := by
  unfold MatchingChains.packingSize nestedBlocksPacking
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left]
  exact Fin.sum_univ_eq_sum_range (fun i => hs.getD i 0) k

/-- The exact global upper bound: each color lies in one block, the colors
assigned to a block cannot use more edges than that block contains, and at most
one block per nonempty color is charged to the decreasing list of block sizes. -/
theorem nestedBlocks_packing_bound {κ : Type*} [Fintype κ]
    (s : ℕ) (hs : List ℕ) (hH : Antitone (fun i => hs.getD i 0))
    {P : κ → Finset ℕ} (hP : MatchingChains.IsPacking (partnerMap (nestedBlocks s hs)) P) :
    MatchingChains.packingSize P ≤ ∑ i ∈ Finset.range (Fintype.card κ), hs.getD i 0 := by
  classical
  let y := partnerMap (nestedBlocks s hs)
  have hy : Function.Involutive y := (nestedBlocks_matching s hs).partnerMap_involutive
  let assign (c : κ) : ℕ := if h : (P c).Nonempty then
    (nestedBlocks_chain_block (hP.chain c) h).choose else 0
  let K : Finset κ := Finset.univ.filter fun c => (P c).Nonempty
  let S : Finset ℕ := K.image assign
  have hassign (c : κ) (hc : c ∈ K) :
      ∀ r ∈ P c, InNestedBlock s hs (assign c) r ∧ InNestedBlock s hs (assign c) (y r) := by
    have hn : (P c).Nonempty := (Finset.mem_filter.mp hc).2
    simpa only [assign,dif_pos hn] using
      (nestedBlocks_chain_block (hP.chain c) hn).choose_spec.2
  have hends (c : κ) (hc : c ∈ K) (x : ℕ)
      (hx : x ∈ MatchingChains.endpoints y (P c)) : InNestedBlock s hs (assign c) x := by
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (hassign c hc x hx).1
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
      exact (hassign c hc r hr).2
  have hsize : (∑ c ∈ K, (P c).card) = MatchingChains.packingSize P := by
    unfold MatchingChains.packingSize
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro c hc hnc
    have hn : ¬(P c).Nonempty := by
      intro hh
      exact hnc (Finset.mem_filter.mpr ⟨hc,hh⟩)
    have hz : P c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hz,Finset.card_empty]
  have hS : S.card ≤ Fintype.card κ := by
    have hh := Finset.card_image_le (s := K) (f := assign)
    have hk := Finset.card_le_card (Finset.filter_subset (s := (Finset.univ : Finset κ))
      (p := fun c => (P c).Nonempty))
    rw [Finset.card_univ] at hk
    exact hh.trans hk
  have hblock (i : ℕ) : (∑ c ∈ K with assign c = i, (P c).card) ≤ hs.getD i 0 := by
    let A := K.filter fun c => assign c = i
    have hd : ((A : Finset κ) : Set κ).PairwiseDisjoint
        (fun c => MatchingChains.endpoints y (P c)) := by
      intro c hc d hd hcd
      exact hP.disjoint c d hcd
    have hcard := Finset.card_biUnion hd
    have hsub : A.biUnion (fun c => MatchingChains.endpoints y (P c)) ⊆
        Finset.Ico (blockStart s hs i) (blockStart s hs (i+1)) := by
      intro x hx
      obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hcK,hci⟩ := Finset.mem_filter.mp hc
      have hh := hends c hcK x hx
      rw [hci] at hh
      exact Finset.mem_Ico.mpr hh
    have hle := Finset.card_le_card hsub
    rw [hcard,Nat.card_Ico,blockStart_succ,Nat.add_sub_cancel_left] at hle
    have he : (∑ c ∈ A, (MatchingChains.endpoints y (P c)).card) =
        2 * ∑ c ∈ A, (P c).card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      exact (MatchingChains.oneUse_iff_endpoints_card hy (P c)).mp (hP.chain c).oneUse
    rw [he] at hle
    change (∑ c ∈ A, (P c).card) ≤ hs.getD i 0
    omega
  calc
    MatchingChains.packingSize P = ∑ c ∈ K, (P c).card := hsize.symm
    _ = ∑ i ∈ S, ∑ c ∈ K with assign c = i, (P c).card := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro c hc
      exact Finset.mem_image_of_mem assign hc
    _ ≤ ∑ i ∈ S, hs.getD i 0 := Finset.sum_le_sum (fun i hi => hblock i)
    _ ≤ ∑ i ∈ Finset.range (Fintype.card κ), hs.getD i 0 :=
      MatchingChains.antitone_sum_finset_le_range _ hH S (Fintype.card κ) hS

/-- All global packing numbers of the canonical disjoint nested matching,
with every number of colors and every block size allowed. -/
theorem nestedBlocks_packing_maximum (s : ℕ) (hs : List ℕ)
    (hH : Antitone (fun i => hs.getD i 0)) (k : ℕ) :
    (∃ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap (nestedBlocks s hs)) P ∧
      MatchingChains.packingSize P = ∑ i ∈ Finset.range k, hs.getD i 0) ∧
    (∀ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap (nestedBlocks s hs)) P →
      MatchingChains.packingSize P ≤ ∑ i ∈ Finset.range k, hs.getD i 0) := by
  refine ⟨⟨nestedBlocksPacking s hs k,nestedBlocksPacking_isPacking s hs k,
    nestedBlocksPacking_size s hs k⟩,?_⟩
  intro P hP
  simpa only [Fintype.card_fin] using nestedBlocks_packing_bound s hs hH hP

end FourPapers.Symmetric
end
/- End source MatchingNestedPacking.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingNestedShape\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingNestedShape"

/- Begin source MatchingNestedShape.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric
open TauCeti HigherSpecht

variable {μ : YoungDiagram}

/-- A strict filling by labels in the exact range of the shape is a standard
tableau. Bijectivity follows from injectivity and the equal finite cardinalities. -/
noncomputable def StrictCellFilling.toStandard (T : StrictCellFilling μ)
    (hbound : ∀ c, T c < μ.card) : StandardYoungTableau μ where
  toTableau := Equiv.ofBijective (fun c => (⟨T c,hbound c⟩ : Fin μ.card))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun c d h => T.injective (congrArg Fin.val h),by simp⟩)
  row_strict' := fun h hc => T.row_strict h hc
  col_strict' := fun h hc => T.col_strict h hc

theorem StrictCellFilling.toStandard_apply_val (T : StrictCellFilling μ)
    (hbound : ∀ c, T c < μ.card) (c : ↥μ.cells) :
    (T.toStandard hbound c).val = T c := rfl

theorem strictFillingRows_eq_ofFn (T : StrictCellFilling μ) :
    strictFillingRows T = List.ofFn (fun i : Fin (μ.colLen 0) =>
      List.ofFn fun j : Fin (μ.rowLen i.val) =>
        T ⟨(i.val,j.val),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩) := by
  unfold strictFillingRows fillingRows rowsOfCells
  rw [List.map_ofFn]
  congr 1
  funext i
  have hr : μ.rowLen i.val ≤ μ.rowLen 0 := μ.rowLen_anti 0 i.val (Nat.zero_le _)
  simp only [Function.comp_def,cellsInRow,List.map_ofFn,min_eq_right hr,Fin.val_cast]

theorem StrictCellFilling.tableauNatRows_toStandard (T : StrictCellFilling μ)
    (hbound : ∀ c, T c < μ.card) :
    tableauNatRows (T.toStandard hbound) = strictFillingRows T := by
  rw [strictFillingRows_eq_ofFn]
  simp only [tableauNatRows,StandardYoungTableau.toRows_def,List.map_ofFn,
    Function.comp_def,StrictCellFilling.toStandard_apply_val]

/-- Conversion of an actual distinct-entry tableau to the standard-tableau
interface used by connectivity, with equality of the full row lists. -/
theorem exists_tableauNatRows_of_bounds {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hshape : rows.map List.length = μ.rowLens)
    (hn : rows.flatten.Nodup) (hbound : ∀ x ∈ rows.flatten, x < μ.card) :
    ∃ T : StandardYoungTableau μ, tableauNatRows T = rows := by
  let S := strictFillingOfRows hrows hshape hn
  have hb : ∀ c : ↥μ.cells, S c < μ.card := by
    intro c
    apply hbound
    have hr := rows_cell_row_bound hshape c.property
    exact List.mem_flatten.mpr ⟨rows[c.val.1]'hr,List.getElem_mem hr,
      List.getElem_mem (rows_cell_col_bound hshape c.property)⟩
  refine ⟨S.toStandard hb,?_⟩
  rw [S.tableauNatRows_toStandard hb]
  exact strictFillingRows_eq_ofRows hrows hshape hn

theorem length_getD_appendColumnPair (a b h : ℕ) (rows : List (List ℕ)) (i : ℕ) :
    ((appendColumnPair a b h rows).getD i []).length =
      (rows.getD i []).length + if i < h then 2 else 0 := by
  induction h generalizing a b rows i with
  | zero => simp only [appendColumnPair,Nat.not_lt_zero,if_false,Nat.add_zero]
  | succ h ih =>
    cases rows with
    | nil =>
      cases i with
      | zero => simp [appendColumnPair]
      | succ i => simpa only [appendColumnPair,List.getD_cons_succ,List.getD_nil,
          List.length_nil,Nat.succ_lt_succ_iff] using ih (a+1) (b+1) [] i
    | cons row rows =>
      cases i with
      | zero => simp [appendColumnPair]
      | succ i =>
        simpa only [appendColumnPair,List.getD_cons_succ,Nat.succ_lt_succ_iff] using
          (ih (a+1) (b+1) rows i)

theorem length_getD_nestedBlocksRows (s : ℕ) (hs : List ℕ)
    (rows : List (List ℕ)) (i : ℕ) :
    ((nestedBlocksRows s hs rows).getD i []).length =
      (rows.getD i []).length + 2 * (hs.filter (fun h => i < h)).length := by
  induction hs generalizing s rows with
  | nil => simp [nestedBlocksRows]
  | cons h hs ih =>
    rw [nestedBlocksRows,ih,length_getD_appendColumnPair]
    by_cases hi : i < h <;> simp [List.filter_cons, hi] <;> omega

theorem length_getD_pairInsertList_nestedBlocks (s : ℕ) (hs : List ℕ) (i : ℕ) :
    ((pairInsertList (nestedBlocks s hs)).getD i []).length =
      2 * (hs.filter (fun h => i < h)).length := by
  rw [pairInsertList_nestedBlocks s hs [] (by simp),length_getD_nestedBlocksRows]
  simp

def columnPairHeights (ν : YoungDiagram) : List ℕ :=
  (List.range (ν.rowLen 0 / 2)).map (fun i => ν.colLen (2*i))

theorem columnPairHeights_getD (ν : YoungDiagram) (i : ℕ) :
    (columnPairHeights ν).getD i 0 =
      if i < ν.rowLen 0 / 2 then ν.colLen (2*i) else 0 := by
  by_cases hi : i < ν.rowLen 0 / 2
  · rw [if_pos hi,List.getD_eq_getElem _ _ (by simpa [columnPairHeights] using hi)]
    simp only [columnPairHeights,List.getElem_map,List.getElem_range]
  · rw [if_neg hi,List.getD_eq_default]
    simpa only [columnPairHeights,List.length_map,List.length_range] using Nat.le_of_not_gt hi

theorem columnPairHeights_antitone (ν : YoungDiagram) :
    Antitone (fun i => (columnPairHeights ν).getD i 0) := by
  intro i j hij
  change (columnPairHeights ν).getD j 0 ≤ (columnPairHeights ν).getD i 0
  rw [columnPairHeights_getD,columnPairHeights_getD]
  by_cases hj : j < ν.rowLen 0 / 2
  · rw [if_pos hj,if_pos (by omega)]
    exact ν.colLen_anti (2*i) (2*j) (by omega)
  · rw [if_neg hj]
    exact Nat.zero_le _

theorem length_filter_range_lt (n k : ℕ) :
    ((List.range n).filter (fun i => i < k)).length = min n k := by
  have hn := (List.nodup_range (n := n)).filter (fun i => i < k)
  have hr : (List.range n).toFinset = Finset.range n := by
    ext i
    simp only [List.mem_toFinset,List.mem_range,Finset.mem_range]
  rw [←List.toFinset_card_of_nodup hn,List.toFinset_filter,hr]
  have he : (Finset.range n).filter (fun i => decide (i < k)) = Finset.range (min n k) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,decide_eq_true_eq,lt_min_iff]
  rw [he,Finset.card_range]

theorem columnPairHeights_filter_length (ν : YoungDiagram)
    (hEven : ∀ i, Even (ν.rowLen i)) (r : ℕ) :
    ((columnPairHeights ν).filter (fun h => r < h)).length = ν.rowLen r / 2 := by
  have hp (i : ℕ) : (r < ν.colLen (2*i)) ↔ i < ν.rowLen r / 2 := by
    have hc : (r < ν.colLen (2*i)) ↔ 2*i < ν.rowLen r :=
      YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
    rw [hc]
    obtain ⟨a,ha⟩ := hEven r
    omega
  unfold columnPairHeights
  rw [List.filter_map,List.length_map]
  simp only [Function.comp_def]
  simp_rw [hp]
  rw [length_filter_range_lt,min_eq_right]
  have hh := ν.rowLen_anti 0 r (Nat.zero_le _)
  omega

theorem rowLen_tableauShape_eq_length_getD {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (r : ℕ) :
    (List.tableauShape rows hrows).rowLen r = (rows.getD r []).length := by
  symm
  rw [←List.getD_map rows [] List.length,←List.rowLens_tableauShape rows hrows]
  simpa only [List.getD_eq_getElem?_getD,List.length_nil] using
    YoungDiagram.matching_getD_rowLens (List.tableauShape rows hrows) r

/-- The canonical nested matching has the exact prescribed even row lengths.
The assertion is about the actual output of paired insertion. -/
theorem nestedBlocks_tableauShape (ν : YoungDiagram)
    (hEven : ∀ i, Even (ν.rowLen i)) :
    List.tableauShape (pairInsertList (nestedBlocks 0 (columnPairHeights ν)))
      (nestedBlocks_matching 0 (columnPairHeights ν)).isTableauRows = ν := by
  apply YoungDiagram.rowLen_injective
  funext r
  rw [rowLen_tableauShape_eq_length_getD,length_getD_pairInsertList_nestedBlocks,
    columnPairHeights_filter_length ν hEven r]
  obtain ⟨a,ha⟩ := hEven r
  omega

theorem exists_standard_nestedBlocks (ν : YoungDiagram)
    (hEven : ∀ i, Even (ν.rowLen i)) :
    ∃ U : StandardYoungTableau ν,
      pairInsertList (nestedBlocks 0 (columnPairHeights ν)) = tableauNatRows U := by
  let w := nestedBlocks 0 (columnPairHeights ν)
  have hw : MatchingWord w := nestedBlocks_matching 0 (columnPairHeights ν)
  have hshape : (pairInsertList w).map List.length = ν.rowLens := by
    rw [←List.rowLens_tableauShape (pairInsertList w) hw.isTableauRows,
      nestedBlocks_tableauShape ν hEven]
  have hcard : ν.card = 2*(columnPairHeights ν).sum := by
    have h1 := List.card_tableauShape (pairInsertList w) hw.isTableauRows
    rw [nestedBlocks_tableauShape ν hEven,pairInsertList_flatten_length,
      nestedBlocks_length] at h1
    exact h1
  have hbound : ∀ x ∈ (pairInsertList w).flatten, x < ν.card := by
    intro x hx
    have hm := (flatten_pairInsertList_perm w []).mem_iff.mp hx
    have hm' : x ∈ endpointWord w := by simpa only [List.flatten_nil,List.append_nil] using hm
    have hh := (nestedBlocks_endpoint_bounds hm').2
    rw [hcard]
    simpa only [Nat.zero_add] using hh
  obtain ⟨U,hU⟩ := exists_tableauNatRows_of_bounds hw.isTableauRows hshape hw.output_distinct hbound
  exact ⟨U,hU.symm⟩

theorem map_length_tableauNatRows (T : StandardYoungTableau μ) :
    (tableauNatRows T).map List.length = μ.rowLens := by
  simpa only [tableauNatRows,List.map_map,Function.comp_def,List.length_map] using
    T.map_length_toRows

theorem length_getD_of_map_length {rows : List (List ℕ)}
    (hshape : rows.map List.length = μ.rowLens) (r : ℕ) :
    (rows.getD r []).length = μ.rowLen r := by
  rw [←List.getD_map rows [] List.length,hshape]
  simpa only [List.getD_eq_getElem?_getD,List.length_nil] using YoungDiagram.matching_getD_rowLens μ r

theorem MatchingWord.even_tableau_shape {T : StandardYoungTableau μ}
    {w : List (ℕ × ℕ)} (hT : pairInsertList w = tableauNatRows T) :
    ∀ r, Even (μ.rowLen r) := by
  have he : ∀ r, Even (((pairInsertList w).getD r []).length) :=
    (evenRows_iff_nat_even (pairInsertList w)).mp (evenRows_nil.pairInsertList w)
  have hshape : (pairInsertList w).map List.length = μ.rowLens := by
    rw [hT,map_length_tableauNatRows]
  intro r
  simpa only [length_getD_of_map_length hshape r] using he r

/-- The full-shape packing assertion for every standard matching. The right
side counts the first `k` pairs of columns in the actual paired-insertion shape.
The even-row hypothesis is derived from insertion, not supplied as an assumption. -/
theorem MatchingWord.packing_shape {T : StandardYoungTableau μ}
    {w : List (ℕ × ℕ)} (hw : MatchingWord w) (hT : pairInsertList w = tableauNatRows T)
    (k : ℕ) :
    (∃ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P ∧
      MatchingChains.packingSize P =
        ∑ i ∈ Finset.range k, (columnPairHeights μ).getD i 0) ∧
    (∀ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P →
      MatchingChains.packingSize P ≤
        ∑ i ∈ Finset.range k, (columnPairHeights μ).getD i 0) := by
  have hEven := MatchingWord.even_tableau_shape hT
  obtain ⟨U,hU⟩ := exists_standard_nestedBlocks μ hEven
  have hprof := matching_packing_equivalent_of_same_tableau_shape hw
    (nestedBlocks_matching 0 (columnPairHeights μ)) hT hU
  obtain ⟨⟨P,hP,hsize⟩,hbound⟩ := nestedBlocks_packing_maximum 0 (columnPairHeights μ)
    (columnPairHeights_antitone μ) k
  constructor
  · exact (hprof (Fin k) _).mpr ⟨P,hP,hsize⟩
  · intro Q hQ
    obtain ⟨R,hR,hRsize⟩ := (hprof (Fin k) (MatchingChains.packingSize Q)).mp ⟨Q,hQ,rfl⟩
    have hh := hbound R hR
    omega

theorem columnPairHeights_getD_eq_colLen (ν : YoungDiagram)
    (hEven : ∀ i, Even (ν.rowLen i)) (j : ℕ) :
    (columnPairHeights ν).getD j 0 = ν.colLen (2*j) := by
  rw [columnPairHeights_getD]
  split_ifs with hj
  · rfl
  · symm
    apply Nat.eq_zero_of_not_pos
    intro hc
    have hm : (0,2*j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr hc
    have hw := YoungDiagram.mem_iff_lt_rowLen.mp hm
    obtain ⟨a,ha⟩ := hEven 0
    omega

theorem colLen_eq_card_filter_rows (ν : YoungDiagram) (j : ℕ) :
    ν.colLen j = ((Finset.univ : Finset (Fin (ν.colLen 0))).filter
      (fun r => j < ν.rowLen r.val)).card := by
  rw [YoungDiagram.colLen_eq_card]
  apply Finset.card_bij (fun p hp =>
    (⟨p.1,ν.lt_colLen_zero_of_mem (YoungDiagram.mem_col_iff.mp hp).1⟩ : Fin (ν.colLen 0)))
  · intro p hp
    obtain ⟨hpν,hpj⟩ := YoungDiagram.mem_col_iff.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hh := YoungDiagram.mem_iff_lt_rowLen.mp hpν
    simpa only [hpj] using hh
  · intro p hp q hq hpq
    apply Prod.ext
    · exact congrArg Fin.val hpq
    · exact (YoungDiagram.mem_col_iff.mp hp).2.trans (YoungDiagram.mem_col_iff.mp hq).2.symm
  · intro r hr
    refine ⟨(r.val,j),?_,?_⟩
    · apply YoungDiagram.mk_mem_col_iff.mpr
      exact YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_filter.mp hr).2
    · apply Fin.ext
      rfl

theorem sum_range_ite_lt_matching (k n : ℕ) :
    (∑ i ∈ Finset.range k, if i < n then 1 else 0) = min k n := by
  rw [Finset.sum_boole]
  have he : ((Finset.range k).filter (fun i => i < n)) = Finset.range (min k n) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,lt_min_iff]
  simp only [he,Finset.card_range,Nat.cast_id]

/-- Double counting proves the equivalence with the paper's row formula
`Σᵢ min(k,μᵢ)` when the actual tableau has row lengths `2μᵢ`. -/
theorem sum_columnPairHeights_eq_sum_min_half_rows (ν : YoungDiagram)
    (hEven : ∀ i, Even (ν.rowLen i)) (k : ℕ) :
    (∑ j ∈ Finset.range k, (columnPairHeights ν).getD j 0) =
      ∑ r : Fin (ν.colLen 0), min k (ν.rowLen r.val / 2) := by
  simp_rw [columnPairHeights_getD_eq_colLen ν hEven,colLen_eq_card_filter_rows]
  have hterm (j : ℕ) :
      ((Finset.univ : Finset (Fin (ν.colLen 0))).filter (fun r => 2*j < ν.rowLen r.val)).card =
        ∑ r : Fin (ν.colLen 0), if j < ν.rowLen r.val / 2 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    have he : (2*j < ν.rowLen r.val) ↔ j < ν.rowLen r.val / 2 := by
      obtain ⟨a,ha⟩ := hEven r.val
      omega
    simp only [he]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact sum_range_ite_lt_matching k (ν.rowLen r.val / 2)

theorem MatchingWord.packing_shape_row_formula {T : StandardYoungTableau μ}
    {w : List (ℕ × ℕ)} (hw : MatchingWord w) (hT : pairInsertList w = tableauNatRows T)
    (k : ℕ) :
    (∃ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P ∧
      MatchingChains.packingSize P = ∑ r : Fin (μ.colLen 0), min k (μ.rowLen r.val / 2)) ∧
    (∀ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P →
      MatchingChains.packingSize P ≤ ∑ r : Fin (μ.colLen 0), min k (μ.rowLen r.val / 2)) := by
  simpa only [sum_columnPairHeights_eq_sum_min_half_rows μ
    (MatchingWord.even_tableau_shape hT) k] using hw.packing_shape hT k

end FourPapers.Symmetric
end
/- End source MatchingNestedShape.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingDirectStatistics\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingDirectStatistics"

/- Begin source MatchingDirectStatistics.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric
open TauCeti

variable {μ : YoungDiagram}

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.prefix_height_definition\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.prefix_height_definition"

/-- Actual nonempty-row count after keeping entries strictly below the cutoff. -/
def rowsPrefixHeight (rows : List (List ℕ)) (q : ℕ) : ℕ :=
  (rows.filter fun row => (row.filter fun x => x < q) ≠ []).length

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.tableau_row_definition\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.tableau_row_definition"

def tableauNatRow (T : StandardYoungTableau μ) (i : Fin (μ.colLen 0)) : List ℕ :=
  List.ofFn fun j : Fin (μ.rowLen i.val) =>
    (T ⟨(i.val,j.val),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩).val

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.rows_ofFn\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.rows_ofFn"

theorem tableauNatRows_eq_ofFn (T : StandardYoungTableau μ) :
    tableauNatRows T = List.ofFn (tableauNatRow T) := by
  simp only [tableauNatRows,StandardYoungTableau.toRows_def,List.map_ofFn,
    tableauNatRow,Function.comp_def]
  rfl

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.row_has_prefix\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.row_has_prefix"

theorem PrefixExtension.row_has_prefix {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) (i : Fin (μ.colLen 0)) :
    ((tableauNatRow T i).filter fun x => x < q) ≠ [] ↔ i.val < E.shape.colLen 0 := by
  constructor
  · intro hne
    by_contra hi
    apply hne
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    have hnot : ¬(T ⟨(i.val,j.val),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩).val < q := by
      intro hsmall
      have hc : (i.val,j.val) ∈ E.shape := (E.mem_shape_iff _).mpr
        ⟨YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt,by
          simpa only [tableauEntry_of_mem _ (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)] using hsmall⟩
      exact hi (E.shape.lt_colLen_zero_of_mem hc)
    simpa only [decide_eq_true_eq] using hnot
  · intro hi heq
    have hc : (i.val,0) ∈ E.shape := YoungDiagram.mem_iff_lt_colLen.mpr hi
    have hcμ : (i.val,0) ∈ μ := E.shape_le hc
    have hsmall := ((E.mem_shape_iff _).mp hc).2
    have hj : 0 < μ.rowLen i.val := YoungDiagram.mem_iff_lt_rowLen.mp hcμ
    have hm : tableauEntry T (i.val,0) ∈ tableauNatRow T i := by
      apply List.mem_ofFn.mpr
      refine ⟨⟨0,hj⟩,?_⟩
      rw [tableauEntry_of_mem T hcμ]
    have hm' : tableauEntry T (i.val,0) ∈
        ((tableauNatRow T i).filter fun x => x < q) :=
      List.mem_filter.mpr ⟨hm,by simpa only [decide_eq_true_eq] using hsmall⟩
    rw [heq] at hm'
    exact List.not_mem_nil hm'

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.filter_length\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.filter_length"

theorem length_filter_eq_sum_indicator {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) :
    (l.filter fun x => p x).length = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : p x <;> simp [hx,ih,Nat.add_comm]

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.finRange_values\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.finRange_values"

theorem matching_finRange_values (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_finRange,List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range,Fin.val_cast]

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.prefix_height_identity\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.prefix_height_identity"

theorem PrefixExtension.height_eq_rowsPrefixHeight {T : StandardYoungTableau μ} {q : ℕ}
    (E : PrefixExtension T q) : E.shape.colLen 0 = rowsPrefixHeight (tableauNatRows T) q := by
  have hle : E.shape.colLen 0 ≤ μ.colLen 0 := by
    by_contra hh
    have hc : (μ.colLen 0,0) ∈ E.shape := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hx := YoungDiagram.mem_iff_lt_colLen.mp (E.shape_le hc)
    omega
  symm
  unfold rowsPrefixHeight
  rw [tableauNatRows_eq_ofFn,List.ofFn_eq_map,List.filter_map,List.length_map]
  simp only [Function.comp_def]
  calc
    _ = ((List.finRange (μ.colLen 0)).filter
        (fun x : Fin (μ.colLen 0) => decide (x.val < E.shape.colLen 0))).length := by
      apply congrArg List.length
      apply List.filter_congr
      intro i hi
      exact decide_eq_decide.mpr (E.row_has_prefix i)
    _ = ((List.range (μ.colLen 0)).filter
        (fun x => decide (x < E.shape.colLen 0))).length := by
      simp only [←matching_finRange_values (μ.colLen 0), List.filter_map,
        List.length_map, Function.comp_def]
    _ = E.shape.colLen 0 := by
      rw [length_filter_range_lt, min_eq_right hle]

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.dense_standard_tableau\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.dense_standard_tableau"

/-- A finite matching with precisely the labels `0,...,N-1` is represented by an
actual standard tableau of the shape obtained from its insertion rows. -/
theorem MatchingWord.exists_standard_of_dense {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    (N : ℕ) (hDense : ∀ x : ℕ, x ∈ endpointWord w ↔ x < N) :
    ∃ (ν : YoungDiagram) (T : StandardYoungTableau ν),
      ν.card = N ∧ pairInsertList w = tableauNatRows T := by
  let ν := List.tableauShape (pairInsertList w) hw.isTableauRows
  have hp : (endpointWord w).Perm (List.range N) := by
    apply (List.perm_ext_iff_of_nodup hw.distinct (show (List.range N).Nodup from List.nodup_range)).mpr
    intro x
    simpa only [List.mem_range] using hDense x
  have hcard : ν.card = N := by
    rw [List.card_tableauShape]
    have hlen := (flatten_pairInsertList_perm w []).length_eq
    have hpend := hp.length_eq
    simp only [List.flatten_nil,List.append_nil,List.length_range] at hlen hpend
    omega
  have hshape : (pairInsertList w).map List.length = ν.rowLens :=
    (List.rowLens_tableauShape _ _).symm
  have hbound : ∀ x ∈ (pairInsertList w).flatten, x < ν.card := by
    intro x hx
    rw [hcard]
    apply (hDense x).mp
    have hm := (flatten_pairInsertList_perm w []).mem_iff.mp hx
    simpa only [List.flatten_nil,List.append_nil] using hm
  obtain ⟨T,hT⟩ := exists_tableauNatRows_of_bounds hw.isTableauRows hshape hw.output_distinct hbound
  exact ⟨ν,T,hcard,hT.symm⟩

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.direct_prefix_height\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.direct_prefix_height"

/-- Direct prefix-height theorem on the actual matching insertion rows. Every
shape and prefix extension used in the proof has been eliminated from its hypotheses. -/
theorem MatchingWord.prefix_height_direct {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    (N : ℕ) (hDense : ∀ x : ℕ, x ∈ endpointWord w ↔ x < N) (q : ℕ) (hq : q ≤ N) :
    (∃ C : Finset ℕ, MatchingChains.IsChain (partnerMap w) C ∧
      C.card = rowsPrefixHeight (pairInsertList w) q ∧ ∀ i ∈ C, i < q) ∧
    (∀ C : Finset ℕ, MatchingChains.IsChain (partnerMap w) C →
      (∀ i ∈ C, i < q) → C.card ≤ rowsPrefixHeight (pairInsertList w) q) := by
  obtain ⟨ν,T,hcard,hT⟩ := hw.exists_standard_of_dense N hDense
  have hq' : q ≤ ν.card := by omega
  obtain ⟨E⟩ := prefixExtension_exists T q hq'
  have hh := hw.prefix_height hT hq' E
  simpa only [E.height_eq_rowsPrefixHeight,←hT] using hh

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.half_row_sum\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.half_row_sum"

theorem sum_min_half_rows_tableauNatRows (T : StandardYoungTableau μ) (k : ℕ) :
    ((tableauNatRows T).map (fun row => min k (row.length/2))).sum =
      ∑ r : Fin (μ.colLen 0), min k (μ.rowLen r.val/2) := by
  rw [tableauNatRows_eq_ofFn,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [tableauNatRow,List.length_ofFn,Function.comp_def]

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL MatchingDirectStatistics.direct_packing_shape\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL MatchingDirectStatistics.direct_packing_shape"

/-- Direct full-shape theorem on the actual matching insertion rows, for every
number of colors. The right side is exactly the paper's sum over half-row lengths. -/
theorem MatchingWord.packing_shape_direct {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    (N : ℕ) (hDense : ∀ x : ℕ, x ∈ endpointWord w ↔ x < N) (k : ℕ) :
    (∃ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P ∧
      MatchingChains.packingSize P =
        ((pairInsertList w).map (fun row => min k (row.length/2))).sum) ∧
    (∀ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P →
      MatchingChains.packingSize P ≤
        ((pairInsertList w).map (fun row => min k (row.length/2))).sum) := by
  obtain ⟨ν,T,hcard,hT⟩ := hw.exists_standard_of_dense N hDense
  have hh := hw.packing_shape_row_formula hT k
  simpa only [←sum_min_half_rows_tableauNatRows T k,←hT] using hh

end FourPapers.Symmetric
end
/- End source MatchingDirectStatistics.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingCollapse\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingCollapse"

/- Begin source MatchingCollapse.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Collapsing standardized endpoint labels

The map from the labels of an inflated matching to its original vertices is
weakly increasing. The extra hypothesis needed to commute it with insertion
is expressed by the positions of equal fibers in the actual tableau: larger
standardized labels in one fiber occur in weakly higher rows.

These lemmas concern the row algorithm itself; no insertion statistic is built
into their definitions.
-/

namespace FourPapers.Symmetric
open TauCeti

/-- In different rows, labels in the same collapsed fiber rise as they increase. -/
def FibersRise (f : ℕ → ℕ) (rows : List (List ℕ)) : Prop :=
  rows.Pairwise fun upper lower =>
    ∀ x ∈ upper, ∀ y ∈ lower, f x = f y → y < x

theorem not_rowDescends_trans {rows : List (List ℕ)}
    (hn : rows.flatten.Nodup) {x y z : ℕ}
    (hx : x ∈ rows.flatten) (hy : y ∈ rows.flatten) (hz : z ∈ rows.flatten)
    (hxy : ¬RowDescends x y rows) (hyz : ¬RowDescends y z rows) :
    ¬RowDescends x z rows := by
  obtain ⟨i, hi⟩ := exists_findIdx?_mem hx
  obtain ⟨j, hj⟩ := exists_findIdx?_mem hy
  obtain ⟨k, hk⟩ := exists_findIdx?_mem hz
  rw [rowDescends_iff_of_findIdx? hn hi hj] at hxy
  rw [rowDescends_iff_of_findIdx? hn hj hk] at hyz
  rw [rowDescends_iff_of_findIdx? hn hi hk]
  omega

/-- Adjacent non-descents control all pairs in a filled interval of labels. -/
theorem not_rowDescends_of_adjacent {rows : List (List ℕ)}
    (hn : rows.flatten.Nodup) (x y : ℕ) (hxy : x ≤ y)
    (hm : ∀ k, x ≤ k → k ≤ y → k ∈ rows.flatten)
    (hd : ∀ k, x ≤ k → k < y → ¬RowDescends k (k + 1) rows) :
    ¬RowDescends x y rows := by
  induction y generalizing x with
  | zero =>
    have hx : x = 0 := by omega
    subst x
    obtain ⟨i, hi⟩ := exists_findIdx?_mem (hm 0 le_rfl le_rfl)
    rw [rowDescends_iff_of_findIdx? hn hi hi]
    omega
  | succ y ih =>
    by_cases he : x = y + 1
    · subst x
      obtain ⟨i, hi⟩ := exists_findIdx?_mem (hm (y + 1) le_rfl le_rfl)
      rw [rowDescends_iff_of_findIdx? hn hi hi]
      omega
    have hxy' : x ≤ y := by omega
    have hfirst : ¬RowDescends x y rows :=
      ih x hxy' (fun k hk hky => hm k hk (by omega))
        (fun k hk hky => hd k hk (by omega))
    exact not_rowDescends_trans hn (hm x le_rfl hxy)
      (hm y hxy' (by omega)) (hm (y + 1) hxy le_rfl)
      hfirst (hd y hxy' (by omega))

theorem FibersRise.tail {f : ℕ → ℕ} {row : List ℕ} {rows : List (List ℕ)}
    (h : FibersRise f (row :: rows)) : FibersRise f rows :=
  (List.pairwise_cons.mp h).2

theorem FibersRise.lower_lt {f : ℕ → ℕ} {row : List ℕ} {rows : List (List ℕ)}
    (h : FibersRise f (row :: rows)) {x y : ℕ}
    (hx : x ∈ row) (hy : y ∈ rows.flatten) (heq : f x = f y) : y < x := by
  obtain ⟨lower, hlower, hy⟩ := List.mem_flatten.mp hy
  exact (List.pairwise_cons.mp h).1 lower hlower x hx y hy heq

/-- Absence of descents throughout a fiber gives the geometric order needed
for collapsing that fiber. Repeated original labels are allowed. -/
theorem fibersRise_of_no_fiber_descents {f : ℕ → ℕ} {rows : List (List ℕ)}
    (hn : rows.flatten.Nodup)
    (hd : ∀ x y, x < y → f x = f y → ¬RowDescends x y rows) :
    FibersRise f rows := by
  induction rows with
  | nil => exact List.Pairwise.nil
  | cons row rows ih =>
    have hparts := List.nodup_append.mp hn
    have hdis := hparts.2.2
    apply List.pairwise_cons.mpr
    constructor
    · intro lower hlower x hx y hy hxy
      have hyt : y ∈ rows.flatten := List.mem_flatten.mpr ⟨lower, hlower, hy⟩
      have hne : x ≠ y := fun he => hdis x hx y hyt he
      by_contra hnot
      have hlt : x < y := by omega
      exact hd x y hlt hxy (Or.inl ⟨hx, hyt⟩)
    · apply ih hparts.2.1
      intro x y hxy heq hdesc
      have hxr : x ∉ row := fun hx => hdis x hx x hdesc.mem_left rfl
      have hyr : y ∉ row := fun hy => hdis y hy y hdesc.mem_right rfl
      exact hd x y hxy heq (Or.inr ⟨hxr, hyr, hdesc⟩)

/-- The adjacent descent rule is enough for canonical inflation: the labels
already present in each vertex block form an interval. -/
theorem fibersRise_of_no_adjacent_descents {f : ℕ → ℕ} (hf : Monotone f)
    {rows : List (List ℕ)} (hn : rows.flatten.Nodup)
    (hfilled : ∀ x ∈ rows.flatten, ∀ y ∈ rows.flatten,
      f x = f y → ∀ k, x ≤ k → k ≤ y → k ∈ rows.flatten)
    (hd : ∀ k, k ∈ rows.flatten → k + 1 ∈ rows.flatten →
      f k = f (k + 1) → ¬RowDescends k (k + 1) rows) :
    FibersRise f rows := by
  apply fibersRise_of_no_fiber_descents hn
  intro x y hxy heq hdesc
  have hm := hfilled x hdesc.mem_left y hdesc.mem_right heq
  apply not_rowDescends_of_adjacent hn x y hxy.le hm _ hdesc
  intro k hxk hky
  have hfxk : f x ≤ f k := hf hxk
  have hkk : f k ≤ f (k + 1) := hf (by omega)
  have hky' : f (k + 1) ≤ f y := hf (by omega)
  have hfeq : f k = f (k + 1) := by omega
  exact hd k (hm k hxk hky.le) (hm (k + 1) (by omega) (by omega)) hfeq

/-- A row-bumping step commutes with a weakly increasing collapse when every
old label in the new label's fiber is smaller than it. -/
theorem rowBump_map_of_fiber_fresh {f : ℕ → ℕ} (hf : Monotone f)
    {a : ℕ} {row : List ℕ}
    (ha : ∀ b ∈ row, f a = f b → b < a) :
    rowBump (f a) (row.map f) =
      ((rowBump a row).1.map f, (rowBump a row).2.map f) := by
  induction row with
  | nil => rfl
  | cons b row ih =>
    have hb := ha b (List.mem_cons_self)
    have ht : ∀ c ∈ row, f a = f c → c < a :=
      fun c hc => ha c (List.mem_cons_of_mem b hc)
    have hcmp : f a < f b ↔ a < b := by
      constructor
      · intro h
        by_contra hnot
        exact (not_lt_of_ge (hf (by omega))) h
      · intro h
        have hle := hf h.le
        have hne : f a ≠ f b := by
          intro he
          have := hb he
          omega
        exact lt_of_le_of_ne hle hne
    simp only [List.map_cons, rowBump_cons, hcmp]
    split_ifs <;> simp only [List.map_cons, Option.map_some, ih ht]

/-- A bump carries the same-fiber freshness condition into the next row.
Consequently collapse preserves the full bumping route and its final row. -/
theorem rowInsert_map_of_fibersRise {f : ℕ → ℕ} (hf : Monotone f)
    {a : ℕ} {rows : List (List ℕ)} (hrows : FibersRise f rows)
    (ha : ∀ b ∈ rows.flatten, f a = f b → b < a) :
    rowInsert (f a) (rows.map (List.map f)) = (rowInsert a rows).map (List.map f) ∧
      rowInsertIndex (f a) (rows.map (List.map f)) = rowInsertIndex a rows := by
  induction rows generalizing a with
  | nil => simp
  | cons row rows ih =>
    have hfirst : ∀ b ∈ row, f a = f b → b < a :=
      fun b hb => ha b (List.mem_append_left _ hb)
    have hmap := rowBump_map_of_fiber_fresh hf hfirst
    cases hb : (rowBump a row).2 with
    | none =>
      have hbn : (rowBump (f a) (row.map f)).2 = none := by rw [hmap, hb]; rfl
      constructor <;> simp only [List.map_cons, rowInsert_cons_of_eq_none rows hb,
        rowInsert_cons_of_eq_none _ hbn, rowInsertIndex_cons_of_eq_none rows hb,
        rowInsertIndex_cons_of_eq_none _ hbn, hmap]
    | some b =>
      have hbs : (rowBump (f a) (row.map f)).2 = some (f b) := by rw [hmap, hb]; rfl
      have hbmem : b ∈ row := mem_of_rowBump_snd_eq_some hb
      have hfresh : ∀ c ∈ rows.flatten, f b = f c → c < b :=
        fun c hc he => hrows.lower_lt hbmem hc he
      obtain ⟨hins, hindex⟩ := ih hrows.tail hfresh
      constructor <;> simp only [List.map_cons, rowInsert_cons_of_eq_some rows hb,
        rowInsert_cons_of_eq_some _ hbs, rowInsertIndex_cons_of_eq_some rows hb,
        rowInsertIndex_cons_of_eq_some _ hbs, hmap, hins, hindex]

/-- The appended partner occupies the same cell before and after collapse. -/
theorem pairInsert_map_of_fibersRise {f : ℕ → ℕ} (hf : Monotone f)
    {a b : ℕ} {rows : List (List ℕ)} (hrows : FibersRise f rows)
    (ha : ∀ c ∈ rows.flatten, f a = f c → c < a) :
    pairInsert (f a) (f b) (rows.map (List.map f)) =
      (pairInsert a b rows).map (List.map f) := by
  obtain ⟨hins, hindex⟩ := rowInsert_map_of_fibersRise hf hrows ha
  unfold pairInsert
  rw [hins, hindex, map_appendToRow]

/-- Collapse commutes with every stage of paired insertion when standardized
copies are introduced chronologically within their fibers. The hypotheses
refer only to the order of labels in the prefix tableaux and to freshness. -/
theorem pairInsertList_map_of_prefix_fibers {f : ℕ → ℕ} (hf : Monotone f)
    (pairs : List (ℕ × ℕ)) (rows : List (List ℕ))
    (hprefix : ∀ pre post, pairs = pre ++ post → FibersRise f (pairInsertList pre rows))
    (hfresh : ∀ pre a b post, pairs = pre ++ (a, b) :: post →
      ∀ c ∈ (pairInsertList pre rows).flatten, f a = f c → c < a) :
    pairInsertList (pairs.map fun p => (f p.1, f p.2)) (rows.map (List.map f)) =
      (pairInsertList pairs rows).map (List.map f) := by
  induction pairs generalizing rows with
  | nil => rfl
  | cons p pairs ih =>
    have hrow : FibersRise f rows := by
      simpa using hprefix [] (p :: pairs) rfl
    have hnew : ∀ c ∈ rows.flatten, f p.1 = f c → c < p.1 := by
      simpa using hfresh [] p.1 p.2 pairs rfl
    have hprefix' : ∀ pre post, pairs = pre ++ post →
        FibersRise f (pairInsertList pre (pairInsert p.1 p.2 rows)) := by
      intro pre post he
      have hh := hprefix (p :: pre) post (by simp [he])
      simpa only [pairInsertList_cons] using hh
    have hfresh' : ∀ pre a b post, pairs = pre ++ (a, b) :: post →
        ∀ c ∈ (pairInsertList pre (pairInsert p.1 p.2 rows)).flatten,
          f a = f c → c < a := by
      intro pre a b post he
      have hh := hfresh (p :: pre) a b post (by simp [he])
      simpa only [pairInsertList_cons] using hh
    simpa only [List.map_cons, pairInsertList_cons,
      pairInsert_map_of_fibersRise hf hrow hnew] using
        ih (pairInsert p.1 p.2 rows) hprefix' hfresh'

theorem isRowAbove_map_of_fibersRise {f : ℕ → ℕ} (hf : Monotone f)
    {upper lower : List ℕ} (h : upper.IsRowAbove lower)
    (hrise : ∀ x ∈ upper, ∀ y ∈ lower, f x = f y → y < x) :
    (upper.map f).IsRowAbove (lower.map f) := by
  refine ⟨by simpa using h.length_le, ?_⟩
  intro j hu hl
  have hu' : j < upper.length := by simpa using hu
  have hl' : j < lower.length := by simpa using hl
  simp only [List.getElem_map]
  have hlt := h.getElem_lt j hu' hl'
  have hle := hf hlt.le
  have hne : f upper[j] ≠ f lower[j] := by
    intro he
    have := hrise _ (List.getElem_mem hu') _ (List.getElem_mem hl') he
    omega
  exact lt_of_le_of_ne hle hne

/-- Collapse yields a semistandard tableau when each fiber rises in the
standardized tableau. Column strictness is proved, rather than assumed. -/
theorem isTableauRows_map_of_fibersRise {f : ℕ → ℕ} (hf : Monotone f)
    {rows : List (List ℕ)} (htab : rows.IsTableauRows) (hrise : FibersRise f rows) :
    (rows.map (List.map f)).IsTableauRows := by
  induction rows with
  | nil => exact List.isTableauRows_nil
  | cons row rows ih =>
    obtain ⟨hne, hsort, habove, htail⟩ := List.isTableauRows_cons.mp htab
    apply List.isTableauRows_cons.mpr
    refine ⟨by simpa using hne, ?_, ?_, ih htail hrise.tail⟩
    · apply List.sortedLE_iff_pairwise.mpr
      rw [List.pairwise_map]
      exact hsort.pairwise.imp (fun h => hf h)
    · cases rows with
      | nil => exact List.isRowAbove_nil _
      | cons lower rows =>
        exact isRowAbove_map_of_fibersRise hf habove
          ((List.pairwise_cons.mp hrise).1 lower (List.mem_cons_self))

end FourPapers.Symmetric
end
/- End source MatchingCollapse.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN CanonicalInflation\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN CanonicalInflation"

/- Begin source CanonicalInflation.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Canonical inflation of repeated endpoints

Each occurrence of an edge has two distinct incidences, even for a loop.
Incidences are ordered first by their original vertex and then by their
chronological position in the ordered edge word. Ranking this order produces
a genuine matching. The collapse map remembers the original vertices.
-/

namespace FourPapers.Symmetric
namespace Inflation

structure Incidence (w : List (ℕ × ℕ)) where
  edge : Fin w.length
  upper : Bool
  deriving DecidableEq

def incidenceEquiv (w : List (ℕ × ℕ)) : Incidence w ≃ Fin w.length × Bool where
  toFun o := (o.edge, o.upper)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance (w : List (ℕ × ℕ)) : Fintype (Incidence w) :=
  Fintype.ofEquiv (Fin w.length × Bool) (incidenceEquiv w).symm

theorem card_incidence (w : List (ℕ × ℕ)) :
    Fintype.card (Incidence w) = 2 * w.length := by
  rw [Fintype.card_congr (incidenceEquiv w)]
  simp [Nat.mul_comm]

def vertex {w : List (ℕ × ℕ)} (o : Incidence w) : ℕ :=
  if o.upper then w[o.edge].2 else w[o.edge].1

def chronology {w : List (ℕ × ℕ)} (o : Incidence w) : ℕ :=
  2 * o.edge.val + if o.upper then 1 else 0

def key {w : List (ℕ × ℕ)} (o : Incidence w) : ℕ ×ₗ ℕ :=
  toLex (vertex o, chronology o)

theorem chronology_injective {w : List (ℕ × ℕ)} :
    Function.Injective (chronology (w := w)) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ he
  cases s <;> cases t <;> simp [chronology] at he
  all_goals try omega
  all_goals
    have hij : i = j := Fin.ext (by omega)
    subst j
    rfl

theorem key_injective {w : List (ℕ × ℕ)} : Function.Injective (key (w := w)) := by
  intro x y h
  exact chronology_injective (congrArg (fun p : ℕ ×ₗ ℕ => p.2) h)

instance (w : List (ℕ × ℕ)) : LinearOrder (Incidence w) :=
  LinearOrder.lift' key key_injective

noncomputable def orderedIncidences (w : List (ℕ × ℕ)) :
    Fin (Fintype.card (Incidence w)) ≃o Incidence w :=
  Fintype.orderIsoFinOfCardEq (Incidence w) rfl

noncomputable def label {w : List (ℕ × ℕ)} (o : Incidence w) :
    Fin (Fintype.card (Incidence w)) := (orderedIncidences w).symm o

theorem label_injective {w : List (ℕ × ℕ)} :
    Function.Injective (fun o : Incidence w => (label o).val) :=
  Fin.val_injective.comp (orderedIncidences w).symm.injective

theorem label_lt_iff {w : List (ℕ × ℕ)} (x y : Incidence w) :
    (label x).val < (label y).val ↔
      vertex x < vertex y ∨ vertex x = vertex y ∧ chronology x < chronology y := by
  change (orderedIncidences w).symm x < (orderedIncidences w).symm y ↔ _
  rw [OrderIso.lt_iff_lt]
  change key x < key y ↔ _
  exact Prod.Lex.toLex_lt_toLex

theorem label_le_iff {w : List (ℕ × ℕ)} (x y : Incidence w) :
    (label x).val ≤ (label y).val ↔
      vertex x < vertex y ∨ vertex x = vertex y ∧ chronology x ≤ chronology y := by
  change (orderedIncidences w).symm x ≤ (orderedIncidences w).symm y ↔ _
  rw [OrderIso.le_iff_le]
  change key x ≤ key y ↔ _
  exact Prod.Lex.toLex_le_toLex

def partner {w : List (ℕ × ℕ)} (o : Incidence w) : Incidence w :=
  ⟨o.edge, !o.upper⟩

theorem partner_involutive {w : List (ℕ × ℕ)} :
    Function.Involutive (partner (w := w)) := by
  rintro ⟨i,s⟩
  cases s <;> rfl

noncomputable def inflatedPair (w : List (ℕ × ℕ)) (i : Fin w.length) : ℕ × ℕ :=
  ((label (⟨i,false⟩ : Incidence w)).val, (label (⟨i,true⟩ : Incidence w)).val)

noncomputable def inflate (w : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.ofFn (inflatedPair w)

def endpointSup (w : List (ℕ × ℕ)) : ℕ := (endpointWord w).toFinset.sup id

theorem vertex_mem_endpoints {w : List (ℕ × ℕ)} (o : Incidence w) :
    vertex o ∈ endpointWord w := by
  apply mem_endpointWord.mpr
  refine ⟨w[o.edge], List.getElem_mem o.edge.isLt, ?_⟩
  cases h : o.upper <;> simp [vertex, h]

theorem vertex_le_endpointSup {w : List (ℕ × ℕ)} (o : Incidence w) :
    vertex o ≤ endpointSup w := by
  exact Finset.le_sup (f := id) (List.mem_toFinset.mpr (vertex_mem_endpoints o))

/-- Outside the finite inflated alphabet, extend collapse constantly by its
largest original endpoint. This makes collapse monotone on all natural numbers. -/
noncomputable def collapse (w : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  if hk : k < Fintype.card (Incidence w) then
    vertex (orderedIncidences w ⟨k,hk⟩)
  else endpointSup w

@[simp] theorem collapse_label {w : List (ℕ × ℕ)} (o : Incidence w) :
    collapse w (label o).val = vertex o := by
  unfold collapse
  rw [dif_pos (label o).isLt]
  change vertex ((orderedIncidences w) ((orderedIncidences w).symm o)) = vertex o
  exact congrArg vertex ((orderedIncidences w).apply_symm_apply o)

@[simp] theorem label_orderedIncidences (w : List (ℕ × ℕ))
    (k : Fin (Fintype.card (Incidence w))) :
    label (orderedIncidences w k) = k :=
  (orderedIncidences w).symm_apply_apply k

theorem collapse_monotone (w : List (ℕ × ℕ)) : Monotone (collapse w) := by
  intro x y hxy
  by_cases hy : y < Fintype.card (Incidence w)
  · have hx : x < Fintype.card (Incidence w) := hxy.trans_lt hy
    simp only [collapse, dif_pos hx, dif_pos hy]
    have hlabels : (label (orderedIncidences w ⟨x,hx⟩)).val ≤
        (label (orderedIncidences w ⟨y,hy⟩)).val := by simpa using hxy
    rcases (label_le_iff _ _).mp hlabels with h | ⟨h,_⟩
    · exact h.le
    · exact h.le
  · by_cases hx : x < Fintype.card (Incidence w)
    · simpa only [collapse, dif_pos hx, dif_neg hy] using
        vertex_le_endpointSup (orderedIncidences w ⟨x,hx⟩)
    · simp only [collapse, dif_neg hx, dif_neg hy, le_refl]

/-- The exact ordering used for the factors of a symmetric monomial. -/
structure OrderedPairs (w : List (ℕ × ℕ)) : Prop where
  lower_le_upper : ∀ p ∈ w, p.1 ≤ p.2
  ordered : w.Pairwise fun p q => p.2 < q.2 ∨ p.2 = q.2 ∧ p.1 ≤ q.1

theorem OrderedPairs.upper_mono {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    (i j : Fin w.length) (hij : i < j) : w[i].2 ≤ w[j].2 := by
  have h := (List.pairwise_iff_getElem.mp hw.ordered) i.val j.val i.isLt j.isLt hij
  rcases h with h | ⟨h,_⟩
  · exact h.le
  · exact h.le

theorem OrderedPairs.inflatedPair_lt {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    (i : Fin w.length) : (inflatedPair w i).1 < (inflatedPair w i).2 := by
  apply (label_lt_iff _ _).mpr
  have h := hw.lower_le_upper _ (List.getElem_mem i.isLt)
  by_cases he : w[i].1 = w[i].2
  · exact Or.inr ⟨by simpa [vertex] using he, by simp [chronology]⟩
  · exact Or.inl (by simpa [vertex] using lt_of_le_of_ne h he)

theorem OrderedPairs.inflated_upper_strict {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    {i j : Fin w.length} (hij : i < j) :
    (inflatedPair w i).2 < (inflatedPair w j).2 := by
  apply (label_lt_iff _ _).mpr
  have h := hw.upper_mono i j hij
  by_cases he : w[i].2 = w[j].2
  · refine Or.inr ⟨by simpa [vertex] using he, ?_⟩
    simp only [chronology, if_true]
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hij (by decide)) 1
  · exact Or.inl (by simpa [vertex] using lt_of_le_of_ne h he)

theorem inflated_endpoints_nodup (w : List (ℕ × ℕ)) :
    (endpointWord (inflate w)).Nodup := by
  classical
  unfold endpointWord inflate
  apply List.nodup_flatMap.mpr
  constructor
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    have hne : (inflatedPair w i).1 ≠ (inflatedPair w i).2 := by
      intro he
      have hh := congrArg Incidence.upper (label_injective he)
      cases hh
    simp [hne]
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    apply List.disjoint_left.mpr
    intro x hx hy
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy
    all_goals
      have he : i = j := congrArg Incidence.edge (label_injective hy)
      exact (ne_of_lt hij) he

/-- Canonical inflation is a matching of distinct endpoint occurrences,
including arbitrary parallel edges and loops in the original word. -/
theorem OrderedPairs.matching_inflate {w : List (ℕ × ℕ)} (hw : OrderedPairs w) :
    MatchingWord (inflate w) := by
  refine ⟨?_, ?_, inflated_endpoints_nodup w⟩
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hw.inflatedPair_lt i
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hw.inflated_upper_strict hij

@[simp] theorem collapse_inflatedPair (w : List (ℕ × ℕ)) (i : Fin w.length) :
    (collapse w (inflatedPair w i).1, collapse w (inflatedPair w i).2) = w[i] := by
  simp [inflatedPair, vertex]

/-- Collapse recovers the original ordered word, with every edge occurrence. -/
theorem collapse_inflate (w : List (ℕ × ℕ)) :
    (inflate w).map (fun p => (collapse w p.1, collapse w p.2)) = w := by
  apply List.ext_getElem
  · simp [inflate]
  · intro i hi hi'
    simp only [List.getElem_map, inflate, List.getElem_ofFn, collapse_inflatedPair]
    rfl

theorem chronology_lt_of_edge_lt {w : List (ℕ × ℕ)} {x y : Incidence w}
    (h : x.edge < y.edge) : chronology x < chronology y := by
  cases hx : x.upper <;> cases hy : y.upper <;> simp [chronology, hx, hy]
  all_goals omega

theorem edge_le_of_chronology_le {w : List (ℕ × ℕ)} {x y : Incidence w}
    (h : chronology x ≤ chronology y) : x.edge ≤ y.edge := by
  cases hx : x.upper <;> cases hy : y.upper <;> simp [chronology, hx, hy] at h
  all_goals omega

/-- Among incidences at one original vertex, partners from different edge
occurrences increase in the inflated order. -/
theorem OrderedPairs.partner_label_lt {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    {x y : Incidence w} (hij : x.edge < y.edge) (hvertex : vertex x = vertex y) :
    (label (partner x)).val < (label (partner y)).val := by
  have hp := hw.lower_le_upper _ (List.getElem_mem x.edge.isLt)
  have hq := hw.lower_le_upper _ (List.getElem_mem y.edge.isLt)
  have ho := (List.pairwise_iff_getElem.mp hw.ordered)
    x.edge.val y.edge.val x.edge.isLt y.edge.isLt hij
  have hv : vertex (partner x) ≤ vertex (partner y) := by
    cases hx : x.upper <;> cases hy : y.upper <;>
      simp [vertex, partner, hx, hy] at hvertex ⊢ <;> omega
  apply (label_lt_iff _ _).mpr
  by_cases he : vertex (partner x) = vertex (partner y)
  · exact Or.inr ⟨he, chronology_lt_of_edge_lt hij⟩
  · exact Or.inl (lt_of_le_of_ne hv he)

/-- The only inverted pair of partners inside an original vertex block is
the two incidences of a single loop. This is the exact one-use exception. -/
theorem OrderedPairs.partner_label_lt_or_paired {w : List (ℕ × ℕ)}
    (hw : OrderedPairs w) {x y : Incidence w}
    (hxy : (label x).val < (label y).val) (hvertex : vertex x = vertex y) :
    (label (partner x)).val < (label (partner y)).val ∨ partner x = y := by
  have hc : chronology x < chronology y := by
    rcases (label_lt_iff x y).mp hxy with h | ⟨_,h⟩
    · omega
    · exact h
  have he : x.edge ≤ y.edge := edge_le_of_chronology_le hc.le
  by_cases hij : x.edge = y.edge
  · right
    rcases x with ⟨i,s⟩
    rcases y with ⟨j,t⟩
    simp only at hij
    subst j
    cases s <;> cases t <;> simp [chronology] at hc
    rfl
  · exact Or.inl (hw.partner_label_lt (lt_of_le_of_ne he hij) hvertex)

@[simp] theorem length_inflate (w : List (ℕ × ℕ)) : (inflate w).length = w.length := by
  simp [inflate]

@[simp] theorem getElem_inflate (w : List (ℕ × ℕ)) (i : ℕ)
    (hi : i < (inflate w).length) :
    (inflate w)[i] = inflatedPair w ⟨i, by simpa using hi⟩ := by
  simp [inflate]

noncomputable def «prefix» (w : List (ℕ × ℕ)) (q : ℕ) : List (ℕ × ℕ) :=
  (inflate w).take q

@[simp] theorem prefix_length (w : List (ℕ × ℕ)) : «prefix» w w.length = inflate w := by
  exact List.take_of_length_le (by simp)

theorem inflatedPair_mem_prefix {w : List (ℕ × ℕ)} {q : ℕ}
    (i : Fin w.length) (hi : i.val < q) : inflatedPair w i ∈ «prefix» w q := by
  have hit : i.val < («prefix» w q).length := by
    simpa [«prefix», List.length_take] using (lt_min hi i.isLt)
  simpa [«prefix»] using List.getElem_mem hit

/-- A prefix contains precisely both incidences of every processed edge. -/
theorem mem_endpoints_prefix_iff {w : List (ℕ × ℕ)} {q x : ℕ} :
    x ∈ endpointWord («prefix» w q) ↔
      ∃ o : Incidence w, o.edge.val < q ∧ (label o).val = x := by
  constructor
  · intro hx
    obtain ⟨p,hp,hx⟩ := mem_endpointWord.mp hx
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hp
    have hiq : i < q := by
      have := hi
      simp only [«prefix», List.length_take, length_inflate] at this
      omega
    have hiw : i < w.length := by
      have := hi
      simp only [«prefix», List.length_take, length_inflate] at this
      omega
    simp only [«prefix», List.getElem_take, getElem_inflate, inflatedPair] at hx
    rcases hx with hx | hx
    · exact ⟨⟨⟨i,hiw⟩,false⟩, hiq, hx.symm⟩
    · exact ⟨⟨⟨i,hiw⟩,true⟩, hiq, hx.symm⟩
  · rintro ⟨⟨i,s⟩,hi,rfl⟩
    apply mem_endpointWord.mpr
    refine ⟨inflatedPair w i, inflatedPair_mem_prefix i hi, ?_⟩
    cases s <;> simp [inflatedPair]

theorem partners_prefix {w : List (ℕ × ℕ)} {q : ℕ}
    (o : Incidence w) (ho : o.edge.val < q) :
    Partners («prefix» w q) (label o).val (label (partner o)).val := by
  rcases o with ⟨i,s⟩
  have hp := inflatedPair_mem_prefix i ho
  cases s
  · exact Or.inl (by simpa [inflatedPair, partner] using hp)
  · exact Or.inr (by simpa [inflatedPair, partner] using hp)

theorem OrderedPairs.matching_prefix {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    (q : ℕ) : MatchingWord («prefix» w q) := by
  have h := hw.matching_inflate
  rw [← List.take_append_drop q (inflate w)] at h
  exact h.prefix

/-- Processed labels occupy an initial interval in each original vertex block. -/
theorem prefix_fiber_filled {w : List (ℕ × ℕ)} {q x y : ℕ}
    (hx : x ∈ endpointWord («prefix» w q)) (hy : y ∈ endpointWord («prefix» w q))
    (hxy : collapse w x = collapse w y) (k : ℕ) (hxk : x ≤ k) (hky : k ≤ y) :
    k ∈ endpointWord («prefix» w q) := by
  obtain ⟨oy, hoy, hly⟩ := mem_endpoints_prefix_iff.mp hy
  have hyN : y < Fintype.card (Incidence w) := hly ▸ (label oy).isLt
  have hkN : k < Fintype.card (Incidence w) := hky.trans_lt hyN
  let ok : Incidence w := orderedIncidences w ⟨k,hkN⟩
  have hlk : (label ok).val = k := by simp [ok]
  have hfxk := collapse_monotone w hxk
  have hfky := collapse_monotone w hky
  have hfk : collapse w k = collapse w y := by omega
  have hv : vertex ok = vertex oy := by
    simpa only [← hlk, ← hly, collapse_label] using hfk
  have hlabels : (label ok).val ≤ (label oy).val := by simpa [hlk, hly] using hky
  have hchrono : chronology ok ≤ chronology oy := by
    rcases (label_le_iff ok oy).mp hlabels with h | ⟨_,h⟩
    · omega
    · exact h
  have hedge := edge_le_of_chronology_le hchrono
  apply mem_endpoints_prefix_iff.mpr
  exact ⟨ok, lt_of_le_of_lt hedge hoy, hlk⟩

/-- No tableau descent lies inside an original vertex block. The exception
for the two ends of one matching edge is handled by the actual descent rule. -/
theorem OrderedPairs.prefix_no_fiber_descent {w : List (ℕ × ℕ)}
    (hw : OrderedPairs w) (q k : ℕ)
    (hk : k ∈ endpointWord («prefix» w q))
    (hk' : k + 1 ∈ endpointWord («prefix» w q))
    (heq : collapse w k = collapse w (k + 1)) :
    ¬RowDescends k (k + 1) (pairInsertList («prefix» w q)) := by
  obtain ⟨x,hx,hlx⟩ := mem_endpoints_prefix_iff.mp hk
  obtain ⟨y,hy,hly⟩ := mem_endpoints_prefix_iff.mp hk'
  have hp : Partners («prefix» w q) k (label (partner x)).val := by
    simpa only [hlx] using partners_prefix x hx
  have hq : Partners («prefix» w q) (k + 1) (label (partner y)).val := by
    simpa only [hly] using partners_prefix y hy
  rw [(hw.matching_prefix q).descent hp hq]
  have hv : vertex x = vertex y := by
    calc
      vertex x = collapse w k := by rw [←hlx,collapse_label]
      _ = collapse w (k+1) := heq
      _ = vertex y := by rw [←hly,collapse_label]
  have hlt : (label x).val < (label y).val := by omega
  rcases hw.partner_label_lt_or_paired hlt hv with h | h
  · omega
  · simp only [h, hly, ne_eq, not_true_eq_false, and_false, not_false_eq_true]

theorem OrderedPairs.prefix_fibersRise {w : List (ℕ × ℕ)}
    (hw : OrderedPairs w) (q : ℕ) :
    FibersRise (collapse w) (pairInsertList («prefix» w q)) := by
  have hm := hw.matching_prefix q
  have hcontent : (pairInsertList («prefix» w q)).flatten.Perm (endpointWord («prefix» w q)) := by
    simpa using flatten_pairInsertList_perm («prefix» w q) []
  apply fibersRise_of_no_adjacent_descents (collapse_monotone w) hm.output_distinct
  · intro x hx y hy heq k hxk hky
    exact hcontent.mem_iff.mpr
      (prefix_fiber_filled (hcontent.mem_iff.mp hx) (hcontent.mem_iff.mp hy) heq k hxk hky)
  · intro k hk hk' heq
    exact hw.prefix_no_fiber_descent q k
      (hcontent.mem_iff.mp hk) (hcontent.mem_iff.mp hk') heq

/-- A newly processed lower endpoint is larger than every earlier occurrence
in its original vertex fiber. -/
theorem prefix_new_fiber_fresh {w : List (ℕ × ℕ)} (i : Fin w.length)
    {c : ℕ} (hc : c ∈ endpointWord («prefix» w i.val))
    (heq : collapse w (inflatedPair w i).1 = collapse w c) :
    c < (inflatedPair w i).1 := by
  obtain ⟨o,ho,hlo⟩ := mem_endpoints_prefix_iff.mp hc
  let a : Incidence w := ⟨i,false⟩
  have hv : vertex o = vertex a := by
    simpa only [inflatedPair, ← hlo, collapse_label, a] using heq.symm
  have hlt : (label o).val < (label a).val :=
    (label_lt_iff o a).mpr (Or.inr ⟨hv, chronology_lt_of_edge_lt ho⟩)
  simpa only [hlo, inflatedPair, a] using hlt

/-- Canonical inflation commutes with the exact paired insertion algorithm,
including every occurrence of a repeated edge and both incidences of a loop. -/
theorem OrderedPairs.insertion_collapse {w : List (ℕ × ℕ)} (hw : OrderedPairs w) :
    pairInsertList w =
      (pairInsertList (inflate w)).map (List.map (collapse w)) := by
  have hprefix : ∀ pre post, inflate w = pre ++ post →
      FibersRise (collapse w) (pairInsertList pre []) := by
    intro pre post he
    have hpre : pre = «prefix» w pre.length := by simp [«prefix», he]
    rw [hpre]
    exact hw.prefix_fibersRise pre.length
  have hfresh : ∀ pre a b post, inflate w = pre ++ (a,b) :: post →
      ∀ c ∈ (pairInsertList pre []).flatten, collapse w a = collapse w c → c < a := by
    intro pre a b post he c hc heq
    have hpre : pre = «prefix» w pre.length := by simp [«prefix», he]
    have hi : pre.length < w.length := by
      have hlen := congrArg List.length he
      simp only [length_inflate, List.length_append, List.length_cons] at hlen
      omega
    let i : Fin w.length := ⟨pre.length,hi⟩
    have hpair : inflatedPair w i = (a,b) := by
      have hget : (inflate w)[pre.length]'(by simpa using hi) = (a,b) := by simp [he]
      simpa [i] using hget
    have hc' : c ∈ endpointWord pre := by
      simpa using (flatten_pairInsertList_perm pre []).mem_iff.mp hc
    have hcf : c ∈ endpointWord («prefix» w i.val) := by simpa [i, ← hpre] using hc'
    have hce : collapse w (inflatedPair w i).1 = collapse w c := by simpa [hpair] using heq
    simpa only [hpair] using prefix_new_fiber_fresh i hcf hce
  have h := pairInsertList_map_of_prefix_fibers (collapse_monotone w)
    (inflate w) [] hprefix hfresh
  simpa only [collapse_inflate, List.map_nil] using h

/-- Paired insertion is semistandard for every ordered symmetric edge word.
The matching case is extended to arbitrary multiplicities by proved collapse. -/
theorem OrderedPairs.isTableauRows {w : List (ℕ × ℕ)} (hw : OrderedPairs w) :
    (pairInsertList w).IsTableauRows := by
  rw [hw.insertion_collapse]
  apply isTableauRows_map_of_fibersRise (collapse_monotone w)
    hw.matching_inflate.isTableauRows
  simpa only [prefix_length] using hw.prefix_fibersRise w.length

end Inflation
end FourPapers.Symmetric
end
/- End source CanonicalInflation.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingFiberOrder\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingFiberOrder"

/- Begin source MatchingFiberOrder.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourPapers.Symmetric
open Inflation

/-- The exact matching condition for merging consecutive standardized labels
into one vertex. A paired edge is the sole permitted partner-order exception. -/
def FiberCompatible (f : ℕ → ℕ) (w : List (ℕ × ℕ)) : Prop :=
  ∀ x ∈ endpointWord w, ∀ y ∈ endpointWord w, x < y → f x = f y →
    partnerMap w x < partnerMap w y ∨ partnerMap w x = y

theorem MatchingWord.fiberCompatible_of_no_descents {w : List (ℕ × ℕ)}
    (hw : MatchingWord w) {f : ℕ → ℕ} (hf : Monotone f)
    (hfilled : ∀ x ∈ endpointWord w, ∀ y ∈ endpointWord w,
      ∀ k, x ≤ k → k ≤ y → k ∈ endpointWord w)
    (hd : ∀ k, k ∈ endpointWord w → k+1 ∈ endpointWord w →
      f k = f (k+1) → ¬RowDescends k (k+1) (pairInsertList w)) :
    FiberCompatible f w := by
  intro x hx y hy hxy heq
  have hn : MatchingChains.NoDescents (partnerMap w) x y := by
    intro k hxk hky
    have hk := hfilled x hx y hy k hxk hky.le
    have hk' := hfilled x hx y hy (k+1) (by omega) (by omega)
    have hfk : f k = f (k+1) := by
      have hx' := hf hxk
      have hy' := hf (show k+1 ≤ y by omega)
      have hkk := hf (show k ≤ k+1 by omega)
      omega
    have hnot := hd k hk hk' hfk
    rw [hw.descent_partnerMap hk hk'] at hnot
    by_cases hp : partnerMap w k = k+1
    · exact Or.inr hp
    · left
      have hne : partnerMap w k ≠ partnerMap w (k+1) := by
        intro he
        have hh := hw.partnerMap_involutive.injective he
        omega
      omega
  rcases hn.inversion hw.partnerMap_involutive le_rfl le_rfl hxy with h | ⟨_,h⟩
  · exact Or.inl h
  · exact Or.inr h

def collapsePairs (f : ℕ → ℕ) (w : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  w.map (fun p => (f p.1,f p.2))

theorem card_incidence_collapsePairs (f : ℕ → ℕ) (w : List (ℕ × ℕ)) :
    Fintype.card (Incidence (collapsePairs f w)) = Fintype.card (Incidence w) := by
  calc
    Fintype.card (Incidence (collapsePairs f w)) = 2 * (collapsePairs f w).length :=
      card_incidence (collapsePairs f w)
    _ = 2 * w.length := by rw [collapsePairs,List.length_map]
    _ = Fintype.card (Incidence w) := (card_incidence w).symm

theorem MatchingWord.collapsePairs_ordered {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {f : ℕ → ℕ} (hf : Monotone f) (hcompat : FiberCompatible f w) :
    OrderedPairs (collapsePairs f w) := by
  constructor
  · intro p hp
    change p ∈ w.map (fun a => (f a.1,f a.2)) at hp
    obtain ⟨a,ha,hap⟩ := List.mem_map.mp hp
    subst p
    exact hf (hw.lower_lt_upper a ha).le
  · rw [collapsePairs,List.pairwise_map]
    apply hw.ordered.imp_of_mem
    intro p q hp hq hpq
    have hle := hf hpq.le
    by_cases he : f p.2 = f q.2
    · right
      refine ⟨he,?_⟩
      have hp' : p.2 ∈ endpointWord w := mem_endpointWord.mpr ⟨p,hp,Or.inr rfl⟩
      have hq' : q.2 ∈ endpointWord w := mem_endpointWord.mpr ⟨q,hq,Or.inr rfl⟩
      have hm := hcompat p.2 hp' q.2 hq' hpq he
      rw [hw.partnerMap_eq (Or.inr hp),hw.partnerMap_eq (Or.inr hq)] at hm
      rcases hm with hm | hm
      · exact hf hm.le
      · have hpl := hw.lower_lt_upper p hp
        omega
    · exact Or.inl (lt_of_le_of_ne hle he)

theorem MatchingWord.vertex_injective {w : List (ℕ × ℕ)} (hw : MatchingWord w) :
    Function.Injective (vertex (w := w)) := by
  intro x y he
  have hp : w[x.edge] = w[y.edge] := by
    apply hw.edge_eq_of_common_endpoint (List.getElem_mem x.edge.isLt)
      (List.getElem_mem y.edge.isLt) (x := vertex x)
    · cases h : x.upper <;> simp [vertex,h]
    · rw [he]
      cases h : y.upper <;> simp [vertex,h]
  have hupper : w[x.edge.val].2 = w[y.edge.val].2 := by
    simpa only [Fin.getElem_fin] using congrArg Prod.snd hp
  have hedge : x.edge = y.edge := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh := (List.pairwise_iff_getElem.mp hw.ordered)
        x.edge.val y.edge.val x.edge.isLt y.edge.isLt hlt
      exact (ne_of_lt hh) hupper
    · have hh := (List.pairwise_iff_getElem.mp hw.ordered)
        y.edge.val x.edge.val y.edge.isLt x.edge.isLt hgt
      exact (ne_of_lt hh) hupper.symm
  rcases x with ⟨i,s⟩
  rcases y with ⟨j,t⟩
  simp only at hedge
  subst j
  have hp' := hw.lower_lt_upper _ (List.getElem_mem i.isLt)
  cases s <;> cases t <;> simp [vertex] at he
  all_goals first | rfl | omega

theorem MatchingWord.partnerMap_vertex {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    (o : Incidence w) : partnerMap w (vertex o) = vertex (partner o) := by
  apply hw.partnerMap_eq
  cases h : o.upper
  · simp only [vertex,partner,h,Bool.not_false,Bool.false_eq_true,
      eq_self_iff_true,if_false,if_true]
    exact Or.inl (List.getElem_mem o.edge.isLt)
  · simp only [vertex,partner,h,Bool.not_true,Bool.false_eq_true,
      eq_self_iff_true,if_false,if_true]
    exact Or.inr (List.getElem_mem o.edge.isLt)

theorem MatchingWord.edge_lt_of_upper_lt {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {i j : Fin w.length} (h : w[i].2 < w[j].2) : i < j := by
  by_contra hn
  by_cases he : i = j
  · subst j
    exact (lt_irrefl _) h
  · have hj : j < i := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
    have hh := (List.pairwise_iff_getElem.mp hw.ordered)
      j.val i.val j.isLt i.isLt hj
    exact (not_lt_of_ge hh.le) h

theorem MatchingWord.vertex_max_partner {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    (o : Incidence w) : max (vertex o) (vertex (partner o)) = w[o.edge].2 := by
  have h := (hw.lower_lt_upper _ (List.getElem_mem o.edge.isLt)).le
  cases hupper : o.upper <;> simp [vertex,partner,hupper,max_eq_right h,max_eq_left h]

/-- The same-fiber order of matching labels agrees with chronological incidence
order. This is the converse to the canonical-inflation partner-order lemma. -/
theorem MatchingWord.chronology_lt_of_fiber_vertex_lt {w : List (ℕ × ℕ)}
    (hw : MatchingWord w) {f : ℕ → ℕ} (hcompat : FiberCompatible f w)
    {x y : Incidence w} (hxy : vertex x < vertex y) (hfxy : f (vertex x) = f (vertex y)) :
    chronology x < chronology y := by
  have hp := hcompat _ (vertex_mem_endpoints x) _ (vertex_mem_endpoints y) hxy hfxy
  rw [hw.partnerMap_vertex,hw.partnerMap_vertex] at hp
  rcases hp with hp | hp
  · have hmax : max (vertex x) (vertex (partner x)) <
        max (vertex y) (vertex (partner y)) := by omega
    rw [hw.vertex_max_partner,hw.vertex_max_partner] at hmax
    exact chronology_lt_of_edge_lt (hw.edge_lt_of_upper_lt hmax)
  · have hpair : partner x = y := hw.vertex_injective hp
    subst y
    cases hu : x.upper <;> simp [vertex,partner,hu] at hxy ⊢
    · simp [chronology,partner,hu]
    · have h := hw.lower_lt_upper _ (List.getElem_mem x.edge.isLt)
      omega

def sourceIncidence (f : ℕ → ℕ) (w : List (ℕ × ℕ))
    (o : Incidence (collapsePairs f w)) : Incidence w :=
  ⟨⟨o.edge.val,by simpa only [collapsePairs,List.length_map] using o.edge.isLt⟩,o.upper⟩

theorem sourceIncidence_injective (f : ℕ → ℕ) (w : List (ℕ × ℕ)) :
    Function.Injective (sourceIncidence f w) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  have he : i = j := Fin.ext (congrArg (fun o => o.edge.val) h)
  have hs : s = t := congrArg Incidence.upper h
  subst j
  subst t
  rfl

@[simp] theorem vertex_sourceIncidence (f : ℕ → ℕ) (w : List (ℕ × ℕ))
    (o : Incidence (collapsePairs f w)) :
    vertex o = f (vertex (sourceIncidence f w o)) := by
  cases h : o.upper <;> simp [vertex,collapsePairs,sourceIncidence,h]

@[simp] theorem chronology_sourceIncidence (f : ℕ → ℕ) (w : List (ℕ × ℕ))
    (o : Incidence (collapsePairs f w)) : chronology (sourceIncidence f w o) = chronology o := rfl

theorem MatchingWord.sourceVertex_strictMono {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {f : ℕ → ℕ} (hf : Monotone f) (hcompat : FiberCompatible f w) :
    StrictMono (fun o : Incidence (collapsePairs f w) => vertex (sourceIncidence f w o)) := by
  intro x y hxy
  have hk : key x < key y := hxy
  rcases Prod.Lex.lt_iff.mp hk with hv | ⟨hv,hchron⟩
  · change vertex x < vertex y at hv
    rw [vertex_sourceIncidence,vertex_sourceIncidence] at hv
    by_contra hn
    exact (not_lt_of_ge (hf (le_of_not_gt hn))) hv
  · change vertex x = vertex y at hv
    change chronology x < chronology y at hchron
    rw [vertex_sourceIncidence,vertex_sourceIncidence] at hv
    by_contra hn
    have hne : vertex (sourceIncidence f w x) ≠ vertex (sourceIncidence f w y) := by
      intro he
      have hsource := hw.vertex_injective he
      have heq := sourceIncidence_injective f w hsource
      subst y
      exact (lt_irrefl _) hxy
    have hrev : vertex (sourceIncidence f w y) < vertex (sourceIncidence f w x) :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
    have hc := hw.chronology_lt_of_fiber_vertex_lt hcompat hrev hv.symm
    rw [chronology_sourceIncidence,chronology_sourceIncidence] at hc
    omega

noncomputable def sourceLabel {w : List (ℕ × ℕ)} (f : ℕ → ℕ)
    (hDense : ∀ x, x ∈ endpointWord w ↔ x < Fintype.card (Incidence w))
    (o : Incidence (collapsePairs f w)) : Fin (Fintype.card (Incidence (collapsePairs f w))) :=
  ⟨vertex (sourceIncidence f w o),by
    have h := (hDense _).mp (vertex_mem_endpoints (sourceIncidence f w o))
    exact h.trans_eq (card_incidence_collapsePairs f w).symm⟩

theorem sourceLabel_surjective {w : List (ℕ × ℕ)} (f : ℕ → ℕ)
    (hDense : ∀ x, x ∈ endpointWord w ↔ x < Fintype.card (Incidence w)) :
    Function.Surjective (sourceLabel f hDense) := by
  intro a
  have ham : a.val ∈ endpointWord w := (hDense _).mpr
    (a.isLt.trans_eq (card_incidence_collapsePairs f w))
  obtain ⟨p,hp,ha | ha⟩ := mem_endpointWord.mp ham
  · obtain ⟨i,hi,hp⟩ := List.getElem_of_mem hp
    refine ⟨⟨⟨i,by simpa only [collapsePairs,List.length_map] using hi⟩,false⟩,?_⟩
    apply Fin.ext
    simp only [sourceLabel,sourceIncidence,vertex,Bool.false_eq_true,if_false]
    exact (congrArg Prod.fst hp).trans ha.symm
  · obtain ⟨i,hi,hp⟩ := List.getElem_of_mem hp
    refine ⟨⟨⟨i,by simpa only [collapsePairs,List.length_map] using hi⟩,true⟩,?_⟩
    apply Fin.ext
    simp only [sourceLabel,sourceIncidence,vertex,eq_self_iff_true,if_true]
    exact (congrArg Prod.snd hp).trans ha.symm

/-- Canonical inflation assigns exactly the original dense matching labels,
provided the matching has the proved same-fiber partner order. -/
theorem MatchingWord.label_collapsePairs {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {f : ℕ → ℕ} (hf : Monotone f) (hcompat : FiberCompatible f w)
    (hDense : ∀ x, x ∈ endpointWord w ↔ x < Fintype.card (Incidence w))
    (o : Incidence (collapsePairs f w)) :
    (label o).val = vertex (sourceIncidence f w o) := by
  let g := sourceLabel f hDense
  have hg : StrictMono g := hw.sourceVertex_strictMono hf hcompat
  let e : Incidence (collapsePairs f w) ≃o
      Fin (Fintype.card (Incidence (collapsePairs f w))) :=
    OrderIso.ofSurjective (OrderEmbedding.ofStrictMono g hg) (sourceLabel_surjective f hDense)
  have he : (orderedIncidences (collapsePairs f w)).symm = e := Subsingleton.elim _ _
  have hh := congrArg (fun e => (e o).val) he
  exact hh

theorem MatchingWord.inflate_collapsePairs {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {f : ℕ → ℕ} (hf : Monotone f) (hcompat : FiberCompatible f w)
    (hDense : ∀ x, x ∈ endpointWord w ↔ x < Fintype.card (Incidence w)) :
    inflate (collapsePairs f w) = w := by
  apply List.ext_getElem
  · simp only [length_inflate,collapsePairs,List.length_map]
  · intro i hi hi'
    rw [getElem_inflate]
    apply Prod.ext
    · exact hw.label_collapsePairs hf hcompat hDense
        (⟨⟨i,by simpa only [length_inflate] using hi⟩,false⟩ :
          Incidence (collapsePairs f w))
    · exact hw.label_collapsePairs hf hcompat hDense
        (⟨⟨i,by simpa only [length_inflate] using hi⟩,true⟩ :
          Incidence (collapsePairs f w))

theorem MatchingWord.collapse_collapsePairs {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {f : ℕ → ℕ} (hf : Monotone f) (hcompat : FiberCompatible f w)
    (hDense : ∀ x, x ∈ endpointWord w ↔ x < Fintype.card (Incidence w))
    {x : ℕ} (hx : x ∈ endpointWord w) : collapse (collapsePairs f w) x = f x := by
  let a : Fin (Fintype.card (Incidence (collapsePairs f w))) :=
    ⟨x,((hDense x).mp hx).trans_eq (card_incidence_collapsePairs f w).symm⟩
  obtain ⟨o,ho⟩ := sourceLabel_surjective f hDense a
  have ho' : vertex (sourceIncidence f w o) = x := congrArg Fin.val ho
  have hlabel : (label o).val = x := (hw.label_collapsePairs hf hcompat hDense o).trans ho'
  calc
    collapse (collapsePairs f w) x = collapse (collapsePairs f w) (label o).val :=
      congrArg (collapse (collapsePairs f w)) hlabel.symm
    _ = vertex o := collapse_label o
    _ = f (vertex (sourceIncidence f w o)) := vertex_sourceIncidence f w o
    _ = f x := congrArg f ho'

/-- Collapse is valid for every dense matching satisfying the intrinsic fiber
condition. It is therefore available for inverses obtained from standard tableaux. -/
theorem MatchingWord.insertion_collapsePairs {w : List (ℕ × ℕ)} (hw : MatchingWord w)
    {f : ℕ → ℕ} (hf : Monotone f) (hcompat : FiberCompatible f w)
    (hDense : ∀ x, x ∈ endpointWord w ↔ x < Fintype.card (Incidence w)) :
    pairInsertList (collapsePairs f w) = (pairInsertList w).map (List.map f) := by
  rw [(hw.collapsePairs_ordered hf hcompat).insertion_collapse,
    hw.inflate_collapsePairs hf hcompat hDense]
  apply List.map_congr_left
  intro row hrow
  apply List.map_congr_left
  intro x hx
  apply hw.collapse_collapsePairs hf hcompat hDense
  have hm : x ∈ (pairInsertList w).flatten := List.mem_flatten.mpr ⟨row,hrow,hx⟩
  simpa only [List.flatten_nil,List.append_nil] using
    (flatten_pairInsertList_perm w []).mem_iff.mp hm

end FourPapers.Symmetric
end
/- End source MatchingFiberOrder.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN SemistandardStandardization\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN SemistandardStandardization"

/- Begin source SemistandardStandardization.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric
open TauCeti

/-- A semistandard filling of a fixed Young diagram by natural labels. -/
structure WeakCellFilling (μ : YoungDiagram) where
  entry : ↥μ.cells → ℕ
  row_mono : ∀ {i j l : ℕ} (hjl : j < l) (hc : (i,l) ∈ μ),
    entry ⟨(i,j),μ.up_left_mem le_rfl hjl.le hc⟩ ≤ entry ⟨(i,l),hc⟩
  col_strict : ∀ {i j l : ℕ} (hij : i < j) (hc : (j,l) ∈ μ),
    entry ⟨(i,l),μ.up_left_mem hij.le le_rfl hc⟩ < entry ⟨(j,l),hc⟩

instance {μ : YoungDiagram} : CoeFun (WeakCellFilling μ) (fun _ => ↥μ.cells → ℕ) :=
  ⟨WeakCellFilling.entry⟩

namespace WeakCellFilling
variable {μ : YoungDiagram}

/-- Equal entries are read from lower rows to upper rows, and from left to
right within one row. This is the standardization appropriate to row insertion. -/
def cellKey (T : WeakCellFilling μ) (c : ↥μ.cells) : ℕ ×ₗ (ℕᵒᵈ ×ₗ ℕ) :=
  toLex (T c,toLex (OrderDual.toDual c.val.1,c.val.2))

theorem cellKey_injective (T : WeakCellFilling μ) : Function.Injective T.cellKey := by
  intro c d h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : ℕ ×ₗ (ℕᵒᵈ ×ₗ ℕ) => OrderDual.ofDual p.2.1) h
  · exact congrArg (fun p : ℕ ×ₗ (ℕᵒᵈ ×ₗ ℕ) => p.2.2) h

structure OrderedCell (T : WeakCellFilling μ) where
  cell : ↥μ.cells
  deriving DecidableEq

def orderedCellEquiv (T : WeakCellFilling μ) : OrderedCell T ≃ ↥μ.cells where
  toFun c := c.cell
  invFun c := ⟨c⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance (T : WeakCellFilling μ) : Fintype (OrderedCell T) :=
  Fintype.ofEquiv ↥μ.cells T.orderedCellEquiv.symm

instance (T : WeakCellFilling μ) : LinearOrder (OrderedCell T) :=
  LinearOrder.lift' (fun c => T.cellKey c.cell)
    (fun _ _ h => congrArg OrderedCell.mk (T.cellKey_injective h))

theorem card_orderedCell (T : WeakCellFilling μ) : Fintype.card (OrderedCell T) = μ.card := by
  rw [Fintype.card_congr T.orderedCellEquiv]
  simp

noncomputable def orderedCells (T : WeakCellFilling μ) : Fin μ.card ≃o OrderedCell T :=
  Fintype.orderIsoFinOfCardEq (OrderedCell T) T.card_orderedCell

noncomputable def label (T : WeakCellFilling μ) (c : ↥μ.cells) : Fin μ.card :=
  T.orderedCells.symm ⟨c⟩

theorem label_lt_iff (T : WeakCellFilling μ) (c d : ↥μ.cells) :
    T.label c < T.label d ↔
      T c < T d ∨ T c = T d ∧
        (d.val.1 < c.val.1 ∨ c.val.1 = d.val.1 ∧ c.val.2 < d.val.2) := by
  change T.orderedCells.symm ⟨c⟩ < T.orderedCells.symm ⟨d⟩ ↔ _
  rw [OrderIso.lt_iff_lt]
  change T.cellKey c < T.cellKey d ↔ _
  simp only [cellKey,Prod.Lex.toLex_lt_toLex]
  rfl

theorem label_le_entry (T : WeakCellFilling μ) {c d : ↥μ.cells}
    (h : T.label c ≤ T.label d) : T c ≤ T d := by
  rcases lt_or_eq_of_le h with h | h
  · rcases (T.label_lt_iff c d).mp h with h | ⟨h,_⟩
    · exact h.le
    · exact h.le
  · have hh : c = d := by
      have hh := T.orderedCells.symm.injective h
      exact congrArg OrderedCell.cell hh
    exact hh ▸ le_rfl

noncomputable def standard (T : WeakCellFilling μ) : StandardYoungTableau μ where
  toTableau := T.orderedCellEquiv.symm.trans T.orderedCells.toEquiv.symm
  row_strict' := by
    intro i j l hjl hc
    apply (T.label_lt_iff _ _).mpr
    have hle := T.row_mono hjl hc
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,Or.inr ⟨rfl,hjl⟩⟩
  col_strict' := by
    intro i j l hij hc
    exact (T.label_lt_iff _ _).mpr (Or.inl (T.col_strict hij hc))

theorem standard_apply (T : WeakCellFilling μ) (c : ↥μ.cells) :
    T.standard c = T.label c := rfl

def entrySup (T : WeakCellFilling μ) : ℕ := Finset.univ.sup T.entry

theorem entry_le_sup (T : WeakCellFilling μ) (c : ↥μ.cells) : T c ≤ T.entrySup :=
  Finset.le_sup (f := T.entry) (Finset.mem_univ c)

noncomputable def collapse (T : WeakCellFilling μ) (k : ℕ) : ℕ :=
  if hk : k < μ.card then T (T.orderedCells ⟨k,hk⟩).cell else T.entrySup

@[simp] theorem collapse_label (T : WeakCellFilling μ) (c : ↥μ.cells) :
    T.collapse (T.label c).val = T c := by
  unfold collapse
  rw [dif_pos (T.label c).isLt]
  change T (T.orderedCells (T.orderedCells.symm ⟨c⟩)).cell = T c
  exact congrArg (fun o : T.OrderedCell => T o.cell) (T.orderedCells.apply_symm_apply ⟨c⟩)

theorem collapse_monotone (T : WeakCellFilling μ) : Monotone T.collapse := by
  intro x y hxy
  by_cases hy : y < μ.card
  · have hx : x < μ.card := hxy.trans_lt hy
    simp only [collapse,dif_pos hx,dif_pos hy]
    apply T.label_le_entry
    change T.orderedCells.symm (T.orderedCells ⟨x,hx⟩) ≤
      T.orderedCells.symm (T.orderedCells ⟨y,hy⟩)
    simpa only [OrderIso.symm_apply_apply, Fin.mk_le_mk] using hxy
  · by_cases hx : x < μ.card
    · simpa only [collapse,dif_pos hx,dif_neg hy] using
        T.entry_le_sup (T.orderedCells ⟨x,hx⟩).cell
    · simp only [collapse,dif_neg hx,dif_neg hy,le_refl]

def rows (T : WeakCellFilling μ) : List (List ℕ) :=
  List.ofFn fun i : Fin (μ.colLen 0) =>
    List.ofFn fun j : Fin (μ.rowLen i.val) =>
      T ⟨(i.val,j.val),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩

theorem collapse_standard_rows (T : WeakCellFilling μ) :
    (tableauNatRows T.standard).map (List.map T.collapse) = T.rows := by
  simp only [tableauNatRows,StandardYoungTableau.toRows_def,List.map_ofFn,
    List.map_map,Function.comp_def,standard_apply,collapse_label,rows]

theorem no_fiber_descents (T : WeakCellFilling μ) (x y : Fin μ.card)
    (hxy : x < y) (heq : T.collapse x.val = T.collapse y.val) :
    ¬RowDescends x.val y.val (tableauNatRows T.standard) := by
  let c := T.standard.toTableau.symm x
  let d := T.standard.toTableau.symm y
  have hc : T.label c = x := T.standard.toTableau.apply_symm_apply x
  have hd : T.label d = y := T.standard.toTableau.apply_symm_apply y
  have hentries : T c = T d := by
    rw [←T.collapse_label c,←T.collapse_label d,hc,hd]
    exact heq
  have hlabels : T.label c < T.label d := by simpa only [hc,hd] using hxy
  have hrows : d.val.1 ≤ c.val.1 := by
    rcases (T.label_lt_iff c d).mp hlabels with h | ⟨_,h | ⟨h,_⟩⟩
    · omega
    · exact h.le
    · omega
  have hdesc := rowDescends_tableauNatRows_iff T.standard c d
  rw [standard_apply,standard_apply,hc,hd] at hdesc
  exact fun hh => (not_lt_of_ge hrows) (hdesc.mp hh)

end WeakCellFilling

def weakFillingOfRows {μ : YoungDiagram} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hshape : rows.map List.length = μ.rowLens) :
    WeakCellFilling μ where
  entry := rowsCellEntry hshape
  row_mono := by
    intro i j l hjl hc
    have hi := rows_cell_row_bound hshape hc
    exact (hrows.sortedLE _ (List.getElem_mem hi)).monotone_get
      (a := ⟨j,hjl.trans (rows_cell_col_bound hshape hc)⟩)
      (b := ⟨l,rows_cell_col_bound hshape hc⟩) hjl.le
  col_strict := by
    intro i j l hij hc
    have hj := rows_cell_row_bound hshape hc
    have hl := rows_cell_col_bound hshape hc
    have habove := (List.pairwise_iff_getElem.mp hrows.isChain.pairwise)
      i j (hij.trans hj) hj hij
    exact habove.getElem_lt l (hl.trans_le habove.length_le) hl

theorem weakFillingOfRows_rows {μ : YoungDiagram} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hshape : rows.map List.length = μ.rowLens) :
    (weakFillingOfRows hrows hshape).rows = rows := by
  have hlen : rows.length = μ.colLen 0 := by simpa using congrArg List.length hshape
  refine List.ext_getElem (by simp [WeakCellFilling.rows,hlen]) fun i hi hi' => ?_
  simp only [WeakCellFilling.rows,List.getElem_ofFn]
  refine List.ext_getElem (by simp [rows_cell_length hshape hi']) fun j hj hj' => ?_
  rewrite [List.getElem_ofFn]
  rfl

theorem FibersRise.lt_of_rowDescends {f : ℕ → ℕ} {rows : List (List ℕ)}
    (h : FibersRise f rows) {x y : ℕ} (hd : RowDescends x y rows)
    (he : f x = f y) : y < x := by
  induction rows with
  | nil => exact False.elim hd
  | cons row rows ih =>
    rcases hd with hd | hd
    · exact h.lower_lt hd.1 hd.2 he
    · exact ih h.tail hd.2.2

theorem WeakCellFilling.entry_of_rows_eq {μ : YoungDiagram} (T : WeakCellFilling μ)
    (S : StandardYoungTableau μ) (f : ℕ → ℕ)
    (hrows : (tableauNatRows S).map (List.map f) = T.rows) (c : ↥μ.cells) :
    T c = f (S c).val := by
  have hi : c.val.1 < μ.colLen 0 := μ.lt_colLen_zero_of_mem c.property
  have hj : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
  have h := congrArg (fun rs : List (List ℕ) => (rs.getD c.val.1 []).getD c.val.2 0) hrows
  simp only [tableauNatRows_eq_ofFn,tableauNatRow,WeakCellFilling.rows,List.map_ofFn,
    Function.comp_def,List.getD_eq_getElem,List.length_ofFn,hi,hj,List.getElem_ofFn] at h
  exact h.symm

/-- The original values and the same-fiber row order uniquely determine a
dense standardization. This rules out a choice-dependent inverse. -/
theorem WeakCellFilling.standard_unique {μ : YoungDiagram} (T : WeakCellFilling μ)
    (S : StandardYoungTableau μ) {f : ℕ → ℕ} (hf : Monotone f)
    (hentry : ∀ c : ↥μ.cells, T c = f (S c).val)
    (hFibers : FibersRise f (tableauNatRows S)) : S = T.standard := by
  let g : T.OrderedCell → Fin μ.card := fun c => S c.cell
  have hg : StrictMono g := by
    intro c d hcd
    have hk : T.cellKey c.cell < T.cellKey d.cell := hcd
    change toLex (T c.cell,toLex (OrderDual.toDual c.cell.val.1,c.cell.val.2)) <
      toLex (T d.cell,toLex (OrderDual.toDual d.cell.val.1,d.cell.val.2)) at hk
    rcases Prod.Lex.toLex_lt_toLex.mp hk with hv | ⟨he,hkey⟩
    · have hvalue : f (S c.cell).val < f (S d.cell).val := by simpa only [hentry] using hv
      by_contra hn
      exact (not_lt_of_ge (hf (le_of_not_gt hn))) hvalue
    · rcases Prod.Lex.toLex_lt_toLex.mp hkey with hrow | ⟨hrow,hcol⟩
      · have hrow' : d.cell.val.1 < c.cell.val.1 := hrow
        have hdesc := (rowDescends_tableauNatRows_iff S d.cell c.cell).mpr hrow'
        have hfe : f (S d.cell).val = f (S c.cell).val := by
          rw [←hentry,←hentry]
          exact he.symm
        exact hFibers.lt_of_rowDescends hdesc hfe
      · have hrow' : c.cell.val.1 = d.cell.val.1 := hrow
        have h := S.row_strict hcol d.cell.property
        have hc : (⟨(d.cell.val.1,c.cell.val.2),
            μ.up_left_mem le_rfl hcol.le d.cell.property⟩ : ↥μ.cells) = c.cell :=
          Subtype.ext (Prod.ext hrow'.symm rfl)
        change S c.cell < S d.cell
        simpa only [hc] using h
  have hsurj : Function.Surjective g := by
    intro a
    obtain ⟨c,hc⟩ := S.surjective a
    exact ⟨⟨c⟩,hc⟩
  let e : T.OrderedCell ≃o Fin μ.card :=
    OrderIso.ofSurjective (OrderEmbedding.ofStrictMono g hg) hsurj
  have he : e = T.orderedCells.symm := Subsingleton.elim _ _
  apply StandardYoungTableau.ext
  intro c
  exact congrArg (fun e => e ⟨c⟩) he

theorem WeakCellFilling.standard_unique_of_rows {μ : YoungDiagram}
    (T : WeakCellFilling μ) (S : StandardYoungTableau μ) {f : ℕ → ℕ}
    (hf : Monotone f) (hrows : (tableauNatRows S).map (List.map f) = T.rows)
    (hFibers : FibersRise f (tableauNatRows S)) : S = T.standard :=
  T.standard_unique S hf (T.entry_of_rows_eq S f hrows) hFibers

end FourPapers.Symmetric
end
/- End source SemistandardStandardization.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingCarrierArithmetic\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingCarrierArithmetic"

/- Begin source MatchingCarrierArithmetic.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

/-!
# Compatibility import for MatchingCarrierArithmetic

The exact accepted aggregate supplies this original API. The full earlier
source, source hashes, and declaration-provider map are preserved in
`recovery/matching_aggregate_reuse_20261102/`. No mathematical statement is
replaced by an assumption. The aggregate retains original license notices.
-/
end
/- End source MatchingCarrierArithmetic.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingCarrierProcess\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingCarrierProcess"

/- Begin source MatchingCarrierProcess.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

/-!
# Compatibility import for MatchingCarrierProcess

The exact accepted aggregate supplies this original API. The full earlier
source, source hashes, and declaration-provider map are preserved in
`recovery/matching_aggregate_reuse_20261102/`. No mathematical statement is
replaced by an assumption. The aggregate retains original license notices.
-/
end
/- End source MatchingCarrierProcess.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN CarrierDeletion\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN CarrierDeletion"

/- Begin source CarrierDeletion.lean; exact hash recorded in audit/combinatorics_sources.json -/
section


set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Whole endpoint stages of first-row deletion

This file connects the paper's min/parity carrier arithmetic to the actual
paired-insertion row processor.  Every multiplicity is an arbitrary natural
number, and the alphabet and endpoint word are unbounded.
-/

namespace FourPapers.Symmetric

open TauCeti

variable {α : Type*} [LinearOrder α]

/-- One alphabet block: its label, its old carrier count, and its incoming count. -/
abbrev CarrierBlock (α : Type*) := α × ℕ × ℕ

/-- The old first row, written in blocks of equal letters. -/
def carrierOldRow : List (CarrierBlock α) → List α
  | [] => []
  | (c, p, _) :: blocks => List.replicate p c ++ carrierOldRow blocks

/-- Incoming lower endpoints, written in the same alphabet order. -/
def carrierIncoming : List (CarrierBlock α) → List α
  | [] => []
  | (c, _, r) :: blocks => List.replicate r c ++ carrierIncoming blocks

/-- Strict ordering of the distinct alphabet blocks. -/
def OrderedCarrierBlocks (blocks : List (CarrierBlock α)) : Prop :=
  blocks.Pairwise (fun x y => x.1 < y.1)

/-- The residual pairs produced by the numerical min/parity rules in one stage.
The last term records all residual loops, so the diagonal rule is included. -/
def stageEmissions (b : α) : List (CarrierBlock α) → ℕ → List (α × α)
  | [], q => List.replicate (q / 2) (b, b)
  | (c, p, r) :: blocks, q =>
      List.replicate (min p q) (c, b) ++
        stageEmissions b blocks (q - min p q + r)

/-- Carrier counts left at the previously visited alphabet letters. -/
def stageRetained : List (CarrierBlock α) → ℕ → List (α × ℕ)
  | [], _ => []
  | (c, p, r) :: blocks, q =>
      (c, p - min p q + r) :: stageRetained blocks (q - min p q + r)

/-- The retained counts, read as the actual weakly increasing first row. -/
def stageRetainedWord : List (CarrierBlock α) → ℕ → List α
  | [], _ => []
  | (c, p, r) :: blocks, q =>
      List.replicate (p - min p q + r) c ++
        stageRetainedWord blocks (q - min p q + r)

/-- Demands remaining when the scan reaches the diagonal. -/
def stageDemand : List (CarrierBlock α) → ℕ → ℕ
  | [], q => q
  | (_, p, r) :: blocks, q => stageDemand blocks (q - min p q + r)

theorem mem_carrierOldRow {blocks : List (CarrierBlock α)} {a : α}
    (ha : a ∈ carrierOldRow blocks) : ∃ d ∈ blocks, a = d.1 := by
  induction blocks with
  | nil => simp [carrierOldRow] at ha
  | cons d blocks ih =>
    rcases d with ⟨c, p, r⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨(c, p, r), by simp, List.eq_of_mem_replicate ha⟩
    · obtain ⟨d, hd, h⟩ := ih ha
      exact ⟨d, List.mem_cons_of_mem _ hd, h⟩

theorem mem_carrierIncoming {blocks : List (CarrierBlock α)} {a : α}
    (ha : a ∈ carrierIncoming blocks) : ∃ d ∈ blocks, a = d.1 := by
  induction blocks with
  | nil => simp [carrierIncoming] at ha
  | cons d blocks ih =>
    rcases d with ⟨c, p, r⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨(c, p, r), by simp, List.eq_of_mem_replicate ha⟩
    · obtain ⟨d, hd, h⟩ := ih ha
      exact ⟨d, List.mem_cons_of_mem _ hd, h⟩

/-- The numerical scan emits exactly the pairs emitted by the actual greedy row
merge. The demands need only lie below the current alphabet; their multiplicity
and all subsequent block multiplicities are unrestricted. -/
theorem carrierMerge_stageEmissions (b : α) (blocks : List (CarrierBlock α))
    (demands : List α) (hblocks : OrderedCarrierBlocks blocks)
    (hbelow : ∀ a ∈ demands, ∀ d ∈ blocks, a < d.1) :
    (carrierMerge b (carrierOldRow blocks)
      (demands ++ carrierIncoming blocks)).2 = stageEmissions b blocks demands.length := by
  induction blocks generalizing demands with
  | nil => simp [carrierOldRow, carrierIncoming, carrierMerge_empty, stageEmissions]
  | cons d blocks ih =>
    rcases d with ⟨c, p, r⟩
    have hord := List.pairwise_cons.mp hblocks
    have hlt : ∀ a ∈ demands, a < c := fun a ha => hbelow a ha (c,p,r) (by simp)
    have hle : ∀ a ∈ List.replicate r c ++ carrierIncoming blocks, c ≤ a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact (List.eq_of_mem_replicate ha).symm.le
      · obtain ⟨d, hd, rfl⟩ := mem_carrierIncoming ha
        exact (hord.1 d hd).le
    have hnew : ∀ a ∈ demands.drop p ++ List.replicate r c,
        ∀ d ∈ blocks, a < d.1 := by
      intro a ha d hd
      rcases List.mem_append.mp ha with ha | ha
      · exact hbelow a (List.mem_of_mem_drop ha) d (List.mem_cons_of_mem _ hd)
      · have hac := List.eq_of_mem_replicate ha
        subst a
        exact hord.1 d hd
    have hrec := ih (demands.drop p ++ List.replicate r c) hord.2 hnew
    have hlen : (demands.drop p ++ List.replicate r c).length =
        demands.length - min p demands.length + r := remaining_demand_length demands c p r
    simp only [carrierOldRow, carrierIncoming]
    rw [carrierMerge_alphabet_step b c p (carrierOldRow blocks) demands
      (List.replicate r c ++ carrierIncoming blocks) hlt hle]
    simp only [← List.append_assoc] at hrec ⊢
    rw [hrec, hlen]
    rfl

/-- The part of the greedy merge already passed by the scan has exactly the
retained multiplicity specified by the off-diagonal carrier rule. -/
theorem carrierMerge_passed_word (demands : List α) (c : α) (p r : ℕ) :
    demands.take p ++ List.replicate (p - demands.length) c ++
      (demands.drop p ++ List.replicate r c) =
    demands ++ List.replicate (p - min p demands.length + r) c := by
  by_cases hp : p ≤ demands.length
  · have hsub : p - demands.length = 0 := Nat.sub_eq_zero_of_le hp
    simp only [hsub, Nat.min_eq_left hp, Nat.sub_self, Nat.zero_add,
      List.replicate_zero, List.append_nil]
    rw [← List.append_assoc, List.take_append_drop]
  · have hp' : demands.length ≤ p := le_of_lt (Nat.lt_of_not_ge hp)
    rw [List.take_of_length_le hp', List.drop_eq_nil_of_le hp']
    simp only [List.nil_append, Nat.min_eq_right hp']
    rw [List.replicate_add, List.append_assoc]

/-- In addition to the emitted pairs, the complete resulting first row agrees
with the numerical carrier scan. This records every retained letter, including
the final parity bit at the current largest endpoint. -/
theorem carrierMerge_stageRow (b : α) (blocks : List (CarrierBlock α))
    (demands : List α) (hblocks : OrderedCarrierBlocks blocks)
    (hbelow : ∀ a ∈ demands, ∀ d ∈ blocks, a < d.1) :
    (carrierMerge b (carrierOldRow blocks)
      (demands ++ carrierIncoming blocks)).1 =
    demands ++ stageRetainedWord blocks demands.length ++
      List.replicate (stageDemand blocks demands.length % 2) b := by
  induction blocks generalizing demands with
  | nil => simp [carrierOldRow, carrierIncoming, carrierMerge_empty,
      stageRetainedWord, stageDemand]
  | cons d blocks ih =>
    rcases d with ⟨c, p, r⟩
    have hord := List.pairwise_cons.mp hblocks
    have hlt : ∀ a ∈ demands, a < c := fun a ha => hbelow a ha (c,p,r) (by simp)
    have hle : ∀ a ∈ List.replicate r c ++ carrierIncoming blocks, c ≤ a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact (List.eq_of_mem_replicate ha).symm.le
      · obtain ⟨d, hd, rfl⟩ := mem_carrierIncoming ha
        exact (hord.1 d hd).le
    have hnew : ∀ a ∈ demands.drop p ++ List.replicate r c,
        ∀ d ∈ blocks, a < d.1 := by
      intro a ha d hd
      rcases List.mem_append.mp ha with ha | ha
      · exact hbelow a (List.mem_of_mem_drop ha) d (List.mem_cons_of_mem _ hd)
      · have hac := List.eq_of_mem_replicate ha
        subst a
        exact hord.1 d hd
    have hrec := ih (demands.drop p ++ List.replicate r c) hord.2 hnew
    have hlen : (demands.drop p ++ List.replicate r c).length =
        demands.length - min p demands.length + r := remaining_demand_length demands c p r
    simp only [carrierOldRow, carrierIncoming]
    rw [carrierMerge_alphabet_step b c p (carrierOldRow blocks) demands
      (List.replicate r c ++ carrierIncoming blocks) hlt hle]
    simp only [List.append_assoc] at hrec
    rw [hrec, hlen]
    simpa only [stageRetainedWord, stageDemand, List.append_assoc] using
      congrArg (fun z : List α => z ++
        stageRetainedWord blocks (demands.length - min p demands.length + r) ++
        List.replicate (stageDemand blocks
          (demands.length - min p demands.length + r) % 2) b)
        (carrierMerge_passed_word demands c p r)

theorem carrierIncoming_sorted (blocks : List (CarrierBlock α))
    (hblocks : OrderedCarrierBlocks blocks) : (carrierIncoming blocks).SortedLE := by
  induction blocks with
  | nil => exact List.sortedLE_nil
  | cons d blocks ih =>
    rcases d with ⟨c, p, r⟩
    have hord := List.pairwise_cons.mp hblocks
    apply List.sortedLE_append.mpr
    refine ⟨List.sortedLE_replicate r, ih hord.2, ?_⟩
    intro a ha z hz
    have hac : a = c := List.eq_of_mem_replicate ha
    obtain ⟨e, he, hze⟩ := mem_carrierIncoming hz
    simpa [hac, hze] using (hord.1 e he).le

/-- Every entry of the processed first row comes from an input endpoint or the
old row. This is extracted from the checked content permutation, with no tableau
assumption. -/
theorem firstRowProcess_row_le (b : α) (pairs : List (α × α)) (row : List α)
    (hpairs : ∀ p ∈ pairs, p.1 ≤ b ∧ p.2 ≤ b)
    (hrow : ∀ a ∈ row, a ≤ b) :
    ∀ a ∈ (firstRowProcess pairs row).1, a ≤ b := by
  intro a ha
  have hperm := firstRowProcess_content pairs row
  have hmem : a ∈ endpointWord pairs ++ row :=
    hperm.mem_iff.mp (List.mem_append_left _ ha)
  rcases List.mem_append.mp hmem with hmem | hmem
  · obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact (hpairs p hp).1
    · exact (hpairs p hp).2
  · exact hrow a hmem

/-- The full off-diagonal scan, followed by any number of original loops,
produces exactly the numerical stage emissions. In particular, the incoming
original loops do not silently become residual loops. -/
theorem firstRowProcess_stageEmissions (b : α) (blocks : List (CarrierBlock α))
    (demands : List α) (loops : ℕ)
    (hblocks : OrderedCarrierBlocks blocks) (hsorted : demands.SortedLE)
    (hbelow : ∀ a ∈ demands, ∀ d ∈ blocks, a < d.1)
    (hmax : ∀ d ∈ blocks, d.1 < b) (hdmax : ∀ a ∈ demands, a < b) :
    (firstRowProcess
      (((demands ++ carrierIncoming blocks).map fun a => (a, b)) ++
        List.replicate loops (b, b)) (carrierOldRow blocks)).2 =
      stageEmissions b blocks demands.length := by
  let incoming := demands ++ carrierIncoming blocks
  have hisorted : incoming.SortedLE := by
    apply List.sortedLE_append.mpr
    refine ⟨hsorted, carrierIncoming_sorted blocks hblocks, ?_⟩
    intro a ha z hz
    obtain ⟨d, hd, rfl⟩ := mem_carrierIncoming hz
    exact (hbelow a ha d hd).le
  have himax : ∀ a ∈ incoming, a < b := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hdmax a ha
    · obtain ⟨d, hd, rfl⟩ := mem_carrierIncoming ha
      exact hmax d hd
  have hrowmax : ∀ a ∈ carrierOldRow blocks, a ≤ b := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := mem_carrierOldRow ha
    exact (hmax d hd).le
  have hprocessed : ∀ a ∈
      (firstRowProcess (incoming.map fun a => (a, b)) (carrierOldRow blocks)).1,
      a ≤ b := by
    apply firstRowProcess_row_le b _ _ _ hrowmax
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact ⟨(himax a ha).le, le_rfl⟩
  change (firstRowProcess ((incoming.map fun a => (a, b)) ++
    List.replicate loops (b, b)) (carrierOldRow blocks)).2 = _
  rw [firstRowProcess_append, firstRowProcess_loops b loops _ hprocessed]
  simp only [List.append_nil]
  rw [firstRowProcess_eq_carrierMerge b _ incoming hisorted himax]
  exact carrierMerge_stageEmissions b blocks demands hblocks hbelow

/-- The complete endpoint-stage identity, including every retained count and
every residual pair, for arbitrary natural multiplicities. -/
theorem firstRowProcess_stage (b : α) (blocks : List (CarrierBlock α))
    (demands : List α) (loops : ℕ)
    (hblocks : OrderedCarrierBlocks blocks) (hsorted : demands.SortedLE)
    (hbelow : ∀ a ∈ demands, ∀ d ∈ blocks, a < d.1)
    (hmax : ∀ d ∈ blocks, d.1 < b) (hdmax : ∀ a ∈ demands, a < b) :
    firstRowProcess
      (((demands ++ carrierIncoming blocks).map fun a => (a, b)) ++
        List.replicate loops (b, b)) (carrierOldRow blocks) =
      (demands ++ stageRetainedWord blocks demands.length ++
        List.replicate (stageDemand blocks demands.length % 2 + 2 * loops) b,
        stageEmissions b blocks demands.length) := by
  let incoming := demands ++ carrierIncoming blocks
  have hisorted : incoming.SortedLE := by
    apply List.sortedLE_append.mpr
    refine ⟨hsorted, carrierIncoming_sorted blocks hblocks, ?_⟩
    intro a ha z hz
    obtain ⟨d, hd, rfl⟩ := mem_carrierIncoming hz
    exact (hbelow a ha d hd).le
  have himax : ∀ a ∈ incoming, a < b := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hdmax a ha
    · obtain ⟨d, hd, rfl⟩ := mem_carrierIncoming ha
      exact hmax d hd
  have hrowmax : ∀ a ∈ carrierOldRow blocks, a ≤ b := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := mem_carrierOldRow ha
    exact (hmax d hd).le
  have hprocessed : ∀ a ∈
      (firstRowProcess (incoming.map fun a => (a, b)) (carrierOldRow blocks)).1,
      a ≤ b := by
    apply firstRowProcess_row_le b _ _ _ hrowmax
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact ⟨(himax a ha).le, le_rfl⟩
  change firstRowProcess ((incoming.map fun a => (a, b)) ++
    List.replicate loops (b, b)) (carrierOldRow blocks) = _
  rw [firstRowProcess_append, firstRowProcess_loops b loops _ hprocessed]
  simp only [List.append_nil]
  rw [firstRowProcess_eq_carrierMerge b _ incoming hisorted himax]
  change ((carrierMerge b (carrierOldRow blocks)
      (demands ++ carrierIncoming blocks)).1 ++ List.replicate (2 * loops) b,
    (carrierMerge b (carrierOldRow blocks)
      (demands ++ carrierIncoming blocks)).2) = _
  rw [carrierMerge_stageRow b blocks demands hblocks hbelow,
    carrierMerge_stageEmissions b blocks demands hblocks hbelow,
    List.replicate_add]
  simp only [List.append_assoc]

/-- The lower rows after one entire endpoint stage are obtained by inserting
the precisely counted residual pairs. This is an equality of actual tableaux,
not merely a conservation law for the carrier counts. -/
theorem pairInsertList_stage_tail (b : α) (blocks : List (CarrierBlock α))
    (demands : List α) (loops : ℕ) (lowerRows : List (List α))
    (hblocks : OrderedCarrierBlocks blocks) (hsorted : demands.SortedLE)
    (hbelow : ∀ a ∈ demands, ∀ d ∈ blocks, a < d.1)
    (hmax : ∀ d ∈ blocks, d.1 < b) (hdmax : ∀ a ∈ demands, a < b) :
    (pairInsertList
      (((demands ++ carrierIncoming blocks).map fun a => (a, b)) ++
        List.replicate loops (b, b)) (carrierOldRow blocks :: lowerRows)).tail =
      pairInsertList (stageEmissions b blocks demands.length) lowerRows := by
  rw [pairInsertList_firstRowProcess, List.tail_cons]
  rw [firstRowProcess_stageEmissions b blocks demands loops
    hblocks hsorted hbelow hmax hdmax]

end FourPapers.Symmetric
end
/- End source CarrierDeletion.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN CarrierArithmeticStage\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN CarrierArithmeticStage"

/- Begin source CarrierArithmeticStage.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric
open TauCeti

theorem exactCarrierStep_diag {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n)
    (he : e.val.2 = e.val.1) : exactCarrierStep e s = exactDiagonal e s := by
  simp only [exactCarrierStep,dif_pos he] <;> rfl

theorem exactCarrierStep_off {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n)
    (he : e.val.2 ≠ e.val.1) : exactCarrierStep e s = exactOffDiagonal e s := by
  simp only [exactCarrierStep,dif_neg he] <;> rfl

theorem exactCarrierStep_fst_fixed {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n)
    (k : Fin n) (hk₁ : k ≠ e.val.1) (hk₂ : k ≠ e.val.2) :
    (exactCarrierStep e s).1 k = s.1 k := by
  by_cases he : e.val.2 = e.val.1
  · rw [exactCarrierStep_diag e s he]
    simp [exactDiagonal,hk₂]
  · rw [exactCarrierStep_off e s he]
    simp [exactOffDiagonal,hk₁,hk₂]

theorem exactCarrierStep_snd_fixed {n : ℕ} (e f : MatchingEntry n) (s : ExactCarrierState n)
    (hef : f ≠ e) : (exactCarrierStep e s).2 f = s.2 f := by
  by_cases he : e.val.2 = e.val.1
  · rw [exactCarrierStep_diag e s he]
    simp [exactDiagonal,hef]
  · rw [exactCarrierStep_off e s he]
    simp [exactOffDiagonal,hef]

theorem exactCarrierSequence_fst_fixed {n : ℕ} (es : List (MatchingEntry n))
    (s : ExactCarrierState n) (k : Fin n)
    (hk : ∀ e ∈ es, k ≠ e.val.1 ∧ k ≠ e.val.2) :
    (exactCarrierSequence es s).1 k = s.1 k := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    rw [exactCarrierSequence,Equiv.trans_apply,ih _ (fun f hf => hk f (List.mem_cons_of_mem _ hf))]
    exact exactCarrierStep_fst_fixed e s k (hk e (by simp)).1 (hk e (by simp)).2

theorem exactCarrierSequence_snd_fixed {n : ℕ} (es : List (MatchingEntry n))
    (s : ExactCarrierState n) (f : MatchingEntry n) (hf : f ∉ es) :
    (exactCarrierSequence es s).2 f = s.2 f := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    have hfe : f ≠ e := fun hh => hf (List.mem_cons.mpr (Or.inl hh))
    have hft : f ∉ es := fun hh => hf (List.mem_cons_of_mem _ hh)
    rw [exactCarrierSequence,Equiv.trans_apply,ih _ hft]
    exact exactCarrierStep_snd_fixed e f s hfe

theorem exactOffDiagonal_lower {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n)
    (he : e.val.2 ≠ e.val.1) :
    (exactOffDiagonal e s).1 e.val.2 =
      s.1 e.val.2 - min (s.1 e.val.2) (s.1 e.val.1) + s.2 e := by
  simp [exactOffDiagonal,offDiagonalCarrier,he]

theorem exactOffDiagonal_upper {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n) :
    (exactOffDiagonal e s).1 e.val.1 =
      s.1 e.val.1 - min (s.1 e.val.2) (s.1 e.val.1) + s.2 e := by
  simp [exactOffDiagonal,offDiagonalCarrier]

theorem exactOffDiagonal_entry {n : ℕ} (e : MatchingEntry n) (s : ExactCarrierState n) :
    (exactOffDiagonal e s).2 e = min (s.1 e.val.2) (s.1 e.val.1) := by
  simp [exactOffDiagonal,offDiagonalCarrier]

def carrierBlocksOfEntries {n : ℕ} (es : List (MatchingEntry n)) (s : ExactCarrierState n) :
    List (CarrierBlock ℕ) := es.map fun e => (e.val.2.val+1,s.1 e.val.2,s.2 e)

def carrierLettersOfEntries {n : ℕ} (es : List (MatchingEntry n)) (s : ExactCarrierState n) :
    List ℕ := es.flatMap fun e => List.replicate (s.1 e.val.2) (e.val.2.val+1)

def carrierPairsOfEntries {n : ℕ} (j : Fin n)
    (es : List (MatchingEntry n)) (s : ExactCarrierState n) : List (ℕ × ℕ) :=
  es.flatMap fun e => List.replicate (s.2 e) (e.val.2.val+1,j.val+1)

theorem carrierOldRow_blocksOfEntries {n : ℕ} (es : List (MatchingEntry n))
    (s : ExactCarrierState n) :
    carrierOldRow (carrierBlocksOfEntries es s) = carrierLettersOfEntries es s := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [carrierBlocksOfEntries,List.map_cons,carrierOldRow,
      carrierLettersOfEntries,List.flatMap_cons] using congrArg (List.replicate (s.1 e.val.2)
        (e.val.2.val+1) ++ ·) ih

theorem carrierBlocksOfEntries_step_tail {n : ℕ} {j : Fin n}
    {e : MatchingEntry n} {es : List (MatchingEntry n)}
    (hej : e.val.1 = j) (helt : e.val.2 < j)
    (ht : ∀ f ∈ es, f.val.1 = j ∧ e.val.2 < f.val.2 ∧ f.val.2 < j)
    (s : ExactCarrierState n) :
    carrierBlocksOfEntries es (exactCarrierStep e s) = carrierBlocksOfEntries es s := by
  apply List.map_congr_left
  intro f hf
  have hfacts := ht f hf
  have hf₁ : f.val.2 ≠ e.val.1 := by rw [hej]; exact hfacts.2.2.ne
  have hf₂ : f.val.2 ≠ e.val.2 := hfacts.2.1.ne'
  have hfe : f ≠ e := by intro hh; subst f; exact (lt_irrefl _) hfacts.2.1
  rw [exactCarrierStep_fst_fixed e s f.val.2 hf₁ hf₂,exactCarrierStep_snd_fixed e f s hfe]

/-- The finite function updates at one upper endpoint agree exactly with the
min-count scan of the first row. This statement includes all carrier counts and
every emitted multiplicity, without a bound on any exponent. -/
theorem exactOffStage_spec {n : ℕ} (j : Fin n) (es : List (MatchingEntry n))
    (horder : es.Pairwise (fun e f => e.val.2 < f.val.2))
    (hstage : ∀ e ∈ es, e.val.1 = j ∧ e.val.2 < j)
    (s : ExactCarrierState n) :
    (exactCarrierSequence es s).1 j = stageDemand (carrierBlocksOfEntries es s) (s.1 j) ∧
    carrierLettersOfEntries es (exactCarrierSequence es s) =
      stageRetainedWord (carrierBlocksOfEntries es s) (s.1 j) ∧
    carrierPairsOfEntries j es (exactCarrierSequence es s) ++
      List.replicate ((exactCarrierSequence es s).1 j / 2) (j.val+1,j.val+1) =
      stageEmissions (j.val+1) (carrierBlocksOfEntries es s) (s.1 j) := by
  induction es generalizing s with
  | nil => simp [exactCarrierSequence,carrierBlocksOfEntries,carrierLettersOfEntries,
      carrierPairsOfEntries,stageDemand,stageRetainedWord,stageEmissions]
  | cons e es ih =>
    obtain ⟨heorder,horder⟩ := List.pairwise_cons.mp horder
    obtain ⟨hej,helt⟩ := hstage e (by simp)
    have hst : ∀ f ∈ es, f.val.1 = j ∧ f.val.2 < j :=
      fun f hf => hstage f (List.mem_cons_of_mem _ hf)
    have ht : ∀ f ∈ es, f.val.1 = j ∧ e.val.2 < f.val.2 ∧ f.val.2 < j :=
      fun f hf => ⟨(hst f hf).1,heorder f hf,(hst f hf).2⟩
    let u := exactCarrierStep e s
    have he : e.val.2 ≠ e.val.1 := by rw [hej]; exact helt.ne
    have huj : u.1 j = s.1 j - min (s.1 e.val.2) (s.1 j) + s.2 e := by
      dsimp only [u]
      rw [exactCarrierStep_off e s he,←hej,exactOffDiagonal_upper,hej]
    have hul : u.1 e.val.2 = s.1 e.val.2 - min (s.1 e.val.2) (s.1 j) + s.2 e := by
      dsimp only [u]
      rw [exactCarrierStep_off e s he,exactOffDiagonal_lower e s he,hej]
    have hue : u.2 e = min (s.1 e.val.2) (s.1 j) := by
      dsimp only [u]
      rw [exactCarrierStep_off e s he,exactOffDiagonal_entry,hej]
    have hblocks : carrierBlocksOfEntries es u = carrierBlocksOfEntries es s :=
      carrierBlocksOfEntries_step_tail hej helt ht s
    have hfixlower : (exactCarrierSequence es u).1 e.val.2 = u.1 e.val.2 := by
      apply exactCarrierSequence_fst_fixed
      intro f hf
      exact ⟨by rw [(hst f hf).1]; exact helt.ne,(heorder f hf).ne⟩
    have heNot : e ∉ es := by
      intro hh
      exact (lt_irrefl _) (heorder e hh)
    have hfixentry := exactCarrierSequence_snd_fixed es u e heNot
    obtain ⟨hq,hret,hemit⟩ := ih horder hst u
    rw [hblocks,huj] at hq hret hemit
    have hseq : exactCarrierSequence (e::es) s = exactCarrierSequence es u := rfl
    rw [hseq]
    refine ⟨?_,?_,?_⟩
    · simpa only [carrierBlocksOfEntries,List.map_cons,stageDemand] using hq
    · change
        List.replicate ((exactCarrierSequence es u).1 e.val.2) (e.val.2.val+1) ++
          carrierLettersOfEntries es (exactCarrierSequence es u) =
        List.replicate (s.1 e.val.2 - min (s.1 e.val.2) (s.1 j) + s.2 e)
            (e.val.2.val+1) ++
          stageRetainedWord (carrierBlocksOfEntries es s)
            (s.1 j - min (s.1 e.val.2) (s.1 j) + s.2 e)
      rw [hfixlower,hul,hret]
    · change
        (List.replicate ((exactCarrierSequence es u).2 e) (e.val.2.val+1,j.val+1) ++
          carrierPairsOfEntries j es (exactCarrierSequence es u)) ++
            List.replicate ((exactCarrierSequence es u).1 j / 2) (j.val+1,j.val+1) =
        List.replicate (min (s.1 e.val.2) (s.1 j)) (e.val.2.val+1,j.val+1) ++
          stageEmissions (j.val+1) (carrierBlocksOfEntries es s)
            (s.1 j - min (s.1 e.val.2) (s.1 j) + s.2 e)
      rw [List.append_assoc,hfixentry,hue,hemit]

theorem exactCarrierSequence_append_apply {n : ℕ}
    (es fs : List (MatchingEntry n)) (s : ExactCarrierState n) :
    exactCarrierSequence (es++fs) s = exactCarrierSequence fs (exactCarrierSequence es s) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [List.cons_append,exactCarrierSequence,Equiv.trans_apply]
    exact ih _

def carrierDiagonalEntry {n : ℕ} (j : Fin n) : MatchingEntry n := ⟨(j,j),le_rfl⟩

def carrierInputStage {n : ℕ} (j : Fin n) (es : List (MatchingEntry n))
    (s : ExactCarrierState n) : List (ℕ × ℕ) :=
  List.replicate (s.1 j) (0,j.val+1) ++ carrierPairsOfEntries j es s ++
    List.replicate (s.2 (carrierDiagonalEntry j)) (j.val+1,j.val+1)

def carrierResidualStage {n : ℕ} (j : Fin n) (es : List (MatchingEntry n))
    (s : ExactCarrierState n) : List (ℕ × ℕ) :=
  carrierPairsOfEntries j es s ++
    List.replicate (s.2 (carrierDiagonalEntry j)) (j.val+1,j.val+1)

theorem carrierIncoming_blocksOfEntries {n : ℕ} (j : Fin n)
    (es : List (MatchingEntry n)) (s : ExactCarrierState n) :
    (carrierIncoming (carrierBlocksOfEntries es s)).map (fun a => (a,j.val+1)) =
      carrierPairsOfEntries j es s := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change
      ((List.replicate (s.2 e) (e.val.2.val+1) ++
        carrierIncoming (carrierBlocksOfEntries es s)).map (fun a => (a,j.val+1))) =
      List.replicate (s.2 e) (e.val.2.val+1,j.val+1) ++ carrierPairsOfEntries j es s
    rw [List.map_append,List.map_replicate,ih]

/-- The final diagonal operation gives exactly the retained endpoint count and
the emitted loop multiplicity in the actual first-row stage. -/
theorem exactCarrierStage_spec {n : ℕ} (j : Fin n) (es : List (MatchingEntry n))
    (horder : es.Pairwise (fun e f => e.val.2 < f.val.2))
    (hstage : ∀ e ∈ es, e.val.1 = j ∧ e.val.2 < j)
    (s : ExactCarrierState n) :
    let t := exactCarrierSequence (es++[carrierDiagonalEntry j]) s
    t.1 j = stageDemand (carrierBlocksOfEntries es s) (s.1 j) % 2 +
      2*s.2 (carrierDiagonalEntry j) ∧
    carrierLettersOfEntries es t = stageRetainedWord (carrierBlocksOfEntries es s) (s.1 j) ∧
    carrierResidualStage j es t = stageEmissions (j.val+1) (carrierBlocksOfEntries es s) (s.1 j) := by
  let u := exactCarrierSequence es s
  let d := carrierDiagonalEntry j
  let t := exactCarrierStep d u
  have hdNot : d ∉ es := by
    intro hd
    have hh := (hstage d hd).2
    exact (lt_irrefl j) hh
  have hud : u.2 d = s.2 d := exactCarrierSequence_snd_fixed es s d hdNot
  have ht : t = exactDiagonal d u := exactCarrierStep_diag d u rfl
  have htj : t.1 j = u.1 j % 2 + 2*u.2 d := by
    rw [ht]
    simp [exactDiagonal,diagonalCarrier,d,carrierDiagonalEntry]
  have htd : t.2 d = u.1 j / 2 := by
    rw [ht]
    simp [exactDiagonal,diagonalCarrier,d,carrierDiagonalEntry]
  have hletters : carrierLettersOfEntries es t = carrierLettersOfEntries es u := by
    apply List.flatMap_congr
    intro e he
    have hne : e.val.2 ≠ j := (hstage e he).2.ne
    rw [ht]
    simp [exactDiagonal,d,carrierDiagonalEntry,hne]
  have hpairs : carrierPairsOfEntries j es t = carrierPairsOfEntries j es u := by
    apply List.flatMap_congr
    intro e he
    have hne : e ≠ d := by intro hh; exact hdNot (hh ▸ he)
    rw [exactCarrierStep_snd_fixed d e u hne]
  obtain ⟨hq,hret,hemit⟩ := exactOffStage_spec j es horder hstage s
  have hseq : exactCarrierSequence (es++[d]) s = t := by
    rewrite [exactCarrierSequence_append_apply]
    rfl
  change (exactCarrierSequence (es++[d]) s).1 j = _ ∧ _ ∧ _
  rw [hseq]
  refine ⟨?_,hletters.trans hret,?_⟩
  · rw [htj,hud,hq]
  · unfold carrierResidualStage
    rw [hpairs,htd]
    exact hemit

theorem orderedCarrierBlocks_of_entries {n : ℕ} (es : List (MatchingEntry n))
    (horder : es.Pairwise (fun e f => e.val.2 < f.val.2)) (s : ExactCarrierState n) :
    OrderedCarrierBlocks (carrierBlocksOfEntries es s) := by
  apply horder.map
  intro e f h
  change e.val.2.val+1 < f.val.2.val+1
  have hh : e.val.2.val < f.val.2.val := h
  omega

/-- One whole endpoint stage of the exact carrier equivalence is the actual
first-row processor. Old copies of label zero are retained and the new carrier
demands add their own copies. Every other count is precisely the updated state. -/
theorem firstRowProcess_exactCarrierStage {n : ℕ} (j : Fin n)
    (es : List (MatchingEntry n))
    (horder : es.Pairwise (fun e f => e.val.2 < f.val.2))
    (hstage : ∀ e ∈ es, e.val.1 = j ∧ e.val.2 < j)
    (s : ExactCarrierState n) (z : ℕ) :
    let t := exactCarrierSequence (es++[carrierDiagonalEntry j]) s
    firstRowProcess (carrierInputStage j es s)
      (List.replicate z 0 ++ carrierLettersOfEntries es s) =
      (List.replicate (z+s.1 j) 0 ++ carrierLettersOfEntries es t ++
        List.replicate (t.1 j) (j.val+1), carrierResidualStage j es t) := by
  let B := carrierBlocksOfEntries es s
  let demands := List.replicate (s.1 j) 0
  let loops := s.2 (carrierDiagonalEntry j)
  have hbelow : ∀ a ∈ demands, ∀ d ∈ B, a < d.1 := by
    intro a ha d hd
    have ha0 : a = 0 := List.eq_of_mem_replicate ha
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
    simp only [ha0,Prod.fst]
    omega
  have hmax : ∀ d ∈ B, d.1 < j.val+1 := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
    have hh : e.val.2.val < j.val := (hstage e he).2
    simp only [Prod.fst]
    omega
  have hdmax : ∀ a ∈ demands, a < j.val+1 := by
    intro a ha
    have ha0 := List.eq_of_mem_replicate ha
    omega
  have hinput : (((demands ++ carrierIncoming B).map fun a => (a,j.val+1)) ++
      List.replicate loops (j.val+1,j.val+1)) = carrierInputStage j es s := by
    rewrite [List.map_append,List.map_replicate,carrierIncoming_blocksOfEntries]
    rfl
  have hprocess := firstRowProcess_stage (j.val+1) B demands loops
    (orderedCarrierBlocks_of_entries es horder s) (List.sortedLE_replicate _)
    hbelow hmax hdmax
  rw [hinput,carrierOldRow_blocksOfEntries] at hprocess
  have hprefix := firstRowProcess_passed_prefix (carrierInputStage j es s)
    (List.replicate z 0) (carrierLettersOfEntries es s) (by
      intro p hp a ha
      have ha0 := List.eq_of_mem_replicate ha
      omega)
  rw [hprocess] at hprefix
  obtain ⟨hq,hret,hemit⟩ := exactCarrierStage_spec j es horder hstage s
  simp only [B,demands,loops,List.length_replicate,Prod.fst,Prod.snd] at hprefix
  rw [←hret,←hq,←hemit] at hprefix
  simpa only [demands,←List.append_assoc,←List.replicate_add] using hprefix

/-- The tableau-tail form of the same exact stage identity, ready for induction
over all upper endpoints in the canonical carrier sequence. -/
theorem pairInsertList_exactCarrierStage {n : ℕ} (j : Fin n)
    (es : List (MatchingEntry n))
    (horder : es.Pairwise (fun e f => e.val.2 < f.val.2))
    (hstage : ∀ e ∈ es, e.val.1 = j ∧ e.val.2 < j)
    (s : ExactCarrierState n) (z : ℕ) (lowerRows : List (List ℕ)) :
    let t := exactCarrierSequence (es++[carrierDiagonalEntry j]) s
    pairInsertList (carrierInputStage j es s)
      ((List.replicate z 0 ++ carrierLettersOfEntries es s)::lowerRows) =
      (List.replicate (z+s.1 j) 0 ++ carrierLettersOfEntries es t ++
        List.replicate (t.1 j) (j.val+1)) ::
        pairInsertList (carrierResidualStage j es t) lowerRows := by
  rw [pairInsertList_firstRowProcess,firstRowProcess_exactCarrierStage j es horder hstage]

end FourPapers.Symmetric
end
/- End source CarrierArithmeticStage.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN CarrierEndpointOrder\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN CarrierEndpointOrder"

/- Begin source CarrierEndpointOrder.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric

def carrierLowerIndex {n : ℕ} (j : Fin n) (i : Fin j.val) : Fin n :=
  ⟨i.val,i.isLt.trans j.isLt⟩

def carrierOffEntry {n : ℕ} (j : Fin n) (i : Fin j.val) : MatchingEntry n :=
  ⟨(j,carrierLowerIndex j i),by change i.val ≤ j.val; exact i.isLt.le⟩

def carrierOffEntries {n : ℕ} (j : Fin n) : List (MatchingEntry n) :=
  List.ofFn (carrierOffEntry j)

def carrierFullStage {n : ℕ} (j : Fin n) : List (MatchingEntry n) :=
  carrierOffEntries j ++ [carrierDiagonalEntry j]

theorem mem_carrierOffEntries {n : ℕ} (j : Fin n) (e : MatchingEntry n) :
    e ∈ carrierOffEntries j ↔ e.val.1 = j ∧ e.val.2 < j := by
  constructor
  · intro he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact ⟨rfl,i.isLt⟩
  · rintro ⟨hej,helt⟩
    apply List.mem_ofFn.mpr
    refine ⟨⟨e.val.2.val,helt⟩,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hej.symm
    · apply Fin.ext
      rfl

theorem mem_carrierFullStage {n : ℕ} (j : Fin n) (e : MatchingEntry n) :
    e ∈ carrierFullStage j ↔ e.val.1 = j := by
  rw [carrierFullStage,List.mem_append,mem_carrierOffEntries,List.mem_singleton]
  constructor
  · rintro (h | rfl)
    · exact h.1
    · rfl
  · intro hej
    by_cases he : e.val.2 = j
    · right
      apply Subtype.ext
      exact Prod.ext hej he
    · left
      refine ⟨hej,?_⟩
      have hle : e.val.2 ≤ j := by simpa only [hej] using e.property
      exact lt_of_le_of_ne hle he

theorem carrierOffEntries_ordered {n : ℕ} (j : Fin n) :
    (carrierOffEntries j).Pairwise (fun e f => e.val.2 < f.val.2) := by
  rw [carrierOffEntries,List.pairwise_ofFn]
  intro a b hab
  exact hab

theorem carrierOffEntries_stage {n : ℕ} (j : Fin n) :
    ∀ e ∈ carrierOffEntries j, e.val.1 = j ∧ e.val.2 < j :=
  fun e he => (mem_carrierOffEntries j e).mp he

theorem carrierFullStage_sorted {n : ℕ} (j : Fin n) : (carrierFullStage j).SortedLT := by
  apply List.Pairwise.sortedLT
  rw [carrierFullStage,List.pairwise_append]
  refine ⟨?_,by simp,?_⟩
  · apply (carrierOffEntries_ordered j).imp_of_mem
    intro e f he hf hlt
    have hej := (mem_carrierOffEntries j e).mp he
    have hfj := (mem_carrierOffEntries j f).mp hf
    apply Prod.Lex.lt_iff.mpr
    exact Or.inr ⟨hej.1.trans hfj.1.symm,hlt⟩
  · intro e he f hf
    have hf' := List.mem_singleton.mp hf
    subst f
    obtain ⟨hej,helt⟩ := (mem_carrierOffEntries j e).mp he
    apply Prod.Lex.lt_iff.mpr
    exact Or.inr ⟨hej,helt⟩

def carrierEntriesBefore (n q : ℕ) : List (MatchingEntry n) :=
  ((List.finRange n).take q).flatMap carrierFullStage

theorem mem_carrierEntriesBefore {n q : ℕ} (e : MatchingEntry n) :
    e ∈ carrierEntriesBefore n q ↔ e.val.1.val < q := by
  unfold carrierEntriesBefore
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨j,hj,he⟩
    have hej := (mem_carrierFullStage j e).mp he
    have htake : j.val < q := by
      obtain ⟨i,hi,hij⟩ := List.getElem_of_mem hj
      have hilen : i < min q n := by simpa only [List.length_take,List.length_finRange] using hi
      have hvalue : j.val = i := by
        have hh := congrArg Fin.val hij
        simpa only [List.getElem_take,List.getElem_finRange,Fin.val_cast] using hh.symm
      omega
    simpa only [hej] using htake
  · intro he
    refine ⟨e.val.1,?_,(mem_carrierFullStage _ _).mpr rfl⟩
    have hi : e.val.1.val < ((List.finRange n).take q).length := by
      simp only [List.length_take,List.length_finRange,lt_min_iff]
      exact ⟨he,e.val.1.isLt⟩
    have hh := List.getElem_mem hi
    simpa only [List.getElem_take,List.getElem_finRange,Fin.cast_mk,Fin.eta] using hh

theorem carrierEntriesBefore_sorted (n q : ℕ) : (carrierEntriesBefore n q).SortedLT := by
  apply List.Pairwise.sortedLT
  apply List.pairwise_flatMap.mpr
  refine ⟨fun j hj => (carrierFullStage_sorted j).pairwise,?_⟩
  apply ((List.sortedLT_finRange n).pairwise.take (i := q)).imp
  intro j k hjk e he f hf
  have hej := (mem_carrierFullStage j e).mp he
  have hfk := (mem_carrierFullStage k f).mp hf
  apply Prod.Lex.lt_iff.mpr
  exact Or.inl (by
    change e.val.1 < f.val.1
    simpa only [hej,hfk] using hjk)

/-- The endpoint-stage enumeration is exactly the already defined sorted carrier
entry list. Thus the global first-row argument acts on `exactCarrierEquiv`. -/
theorem carrierEntriesBefore_full (n : ℕ) : carrierEntriesBefore n n = orderedCarrierEntries n := by
  symm
  apply (Finset.univ.sortedLT_sort).eq_of_mem_iff (carrierEntriesBefore_sorted n n)
  intro e
  simp only [Finset.mem_sort,Finset.mem_univ,true_iff,mem_carrierEntriesBefore]
  exact e.val.1.isLt

theorem carrierEntriesBefore_succ {n q : ℕ} (hq : q < n) :
    carrierEntriesBefore n (q+1) = carrierEntriesBefore n q ++ carrierFullStage ⟨q,hq⟩ := by
  unfold carrierEntriesBefore
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using hq),
    List.flatMap_append,List.flatMap_singleton,List.getElem_finRange]
  simp only [Fin.cast_mk]

theorem exactCarrierBefore_fst_future {n q : ℕ} (s : ExactCarrierState n)
    (j : Fin n) (hqj : q ≤ j.val) :
    (exactCarrierSequence (carrierEntriesBefore n q) s).1 j = s.1 j := by
  apply exactCarrierSequence_fst_fixed
  intro e he
  have heu := (mem_carrierEntriesBefore e).mp he
  have hel : e.val.2.val ≤ e.val.1.val := e.property
  constructor
  · intro hh; have := congrArg Fin.val hh; omega
  · intro hh; have := congrArg Fin.val hh; omega

theorem exactCarrierBefore_snd_future {n q : ℕ} (s : ExactCarrierState n)
    (e : MatchingEntry n) (hqe : q ≤ e.val.1.val) :
    (exactCarrierSequence (carrierEntriesBefore n q) s).2 e = s.2 e := by
  apply exactCarrierSequence_snd_fixed
  intro he
  have := (mem_carrierEntriesBefore e).mp he
  omega

theorem exactCarrierStage_snd_past {n : ℕ} (j : Fin n) (s : ExactCarrierState n)
    (e : MatchingEntry n) (hej : e.val.1 < j) :
    (exactCarrierSequence (carrierFullStage j) s).2 e = s.2 e := by
  apply exactCarrierSequence_snd_fixed
  intro he
  have hh := (mem_carrierFullStage j e).mp he
  exact hej.ne hh

end FourPapers.Symmetric
end
/- End source CarrierEndpointOrder.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN CarrierGlobalDeletion\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN CarrierGlobalDeletion"

/- Begin source CarrierGlobalDeletion.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace FourPapers.Symmetric

def carrierStateBefore {n : ℕ} (q : ℕ) (s : ExactCarrierState n) : ExactCarrierState n :=
  exactCarrierSequence (carrierEntriesBefore n q) s

def carrierInputPrefix {n : ℕ} (q : ℕ) (s : ExactCarrierState n) : List (ℕ × ℕ) :=
  ((List.finRange n).take q).flatMap fun j => carrierInputStage j (carrierOffEntries j) s

def carrierResidualPrefix {n : ℕ} (q : ℕ) (s : ExactCarrierState n) : List (ℕ × ℕ) :=
  ((List.finRange n).take q).flatMap fun j => carrierResidualStage j (carrierOffEntries j) s

def carrierLettersBefore {n : ℕ} (q : ℕ) (s : ExactCarrierState n) : List ℕ :=
  ((List.finRange n).take q).flatMap fun i => List.replicate (s.1 i) (i.val+1)

def carrierZerosBefore {n : ℕ} (q : ℕ) (s : ExactCarrierState n) : ℕ :=
  (((List.finRange n).take q).map s.1).sum

theorem finRange_take_succ {n q : ℕ} (hq : q < n) :
    (List.finRange n).take (q+1) = (List.finRange n).take q ++ [⟨q,hq⟩] := by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using hq)]
  simp only [List.getElem_finRange,Fin.cast_mk]

theorem carrierStateBefore_succ {n q : ℕ} (hq : q < n) (s : ExactCarrierState n) :
    carrierStateBefore (q+1) s =
      exactCarrierSequence (carrierFullStage ⟨q,hq⟩) (carrierStateBefore q s) := by
  rewrite [carrierStateBefore,carrierEntriesBefore_succ hq,exactCarrierSequence_append_apply]
  rfl

theorem carrierStateBefore_full (n : ℕ) (s : ExactCarrierState n) :
    carrierStateBefore n s = exactCarrierEquiv n s := by
  rewrite [carrierStateBefore,carrierEntriesBefore_full]
  rfl

theorem carrierInputPrefix_succ {n q : ℕ} (hq : q < n) (s : ExactCarrierState n) :
    carrierInputPrefix (q+1) s = carrierInputPrefix q s ++
      carrierInputStage ⟨q,hq⟩ (carrierOffEntries ⟨q,hq⟩) s := by
  simp only [carrierInputPrefix,finRange_take_succ hq,List.flatMap_append,List.flatMap_singleton]

theorem carrierResidualPrefix_succ {n q : ℕ} (hq : q < n) (s : ExactCarrierState n) :
    carrierResidualPrefix (q+1) s = carrierResidualPrefix q s ++
      carrierResidualStage ⟨q,hq⟩ (carrierOffEntries ⟨q,hq⟩) s := by
  simp only [carrierResidualPrefix,finRange_take_succ hq,List.flatMap_append,List.flatMap_singleton]

theorem carrierLettersBefore_succ {n q : ℕ} (hq : q < n) (s : ExactCarrierState n) :
    carrierLettersBefore (q+1) s = carrierLettersBefore q s ++
      List.replicate (s.1 ⟨q,hq⟩) (q+1) := by
  simp only [carrierLettersBefore,finRange_take_succ hq,List.flatMap_append,List.flatMap_singleton]

theorem carrierZerosBefore_succ {n q : ℕ} (hq : q < n) (s : ExactCarrierState n) :
    carrierZerosBefore (q+1) s = carrierZerosBefore q s + s.1 ⟨q,hq⟩ := by
  simp only [carrierZerosBefore,finRange_take_succ hq,List.map_append,List.map_singleton,
    List.sum_append,List.sum_singleton]

theorem carrierLowerIndices_eq_take {n : ℕ} (j : Fin n) :
    List.ofFn (carrierLowerIndex j) = (List.finRange n).take j.val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,List.length_finRange,min_eq_left j.isLt.le]
  · intro i hi hi'
    simp only [List.getElem_ofFn,List.getElem_take,List.getElem_finRange]
    apply Fin.ext
    rfl

theorem carrierLetters_stage_eq {n : ℕ} (j : Fin n) (s : ExactCarrierState n) :
    carrierLettersOfEntries (carrierOffEntries j) s = carrierLettersBefore j.val s := by
  have hindices : (carrierOffEntries j).map (fun e => e.val.2) =
      (List.finRange n).take j.val := by
    rw [carrierOffEntries,List.map_ofFn]
    exact carrierLowerIndices_eq_take j
  rewrite [carrierLettersBefore,←hindices,List.flatMap_map]
  rfl

theorem carrierInputStage_before {n : ℕ} (j : Fin n) (s : ExactCarrierState n) :
    carrierInputStage j (carrierOffEntries j) (carrierStateBefore j.val s) =
      carrierInputStage j (carrierOffEntries j) s := by
  have hq := exactCarrierBefore_fst_future s j le_rfl
  change (carrierStateBefore j.val s).1 j = s.1 j at hq
  have he (e : MatchingEntry n) (hej : e.val.1 = j) :
      (carrierStateBefore j.val s).2 e = s.2 e := by
    apply exactCarrierBefore_snd_future
    rw [hej]
  unfold carrierInputStage
  rw [hq,he (carrierDiagonalEntry j) rfl]
  congr 2
  apply List.flatMap_congr
  intro e he'
  rw [he e ((mem_carrierOffEntries j e).mp he').1]

theorem carrierResidualStage_congr {n : ℕ} (j : Fin n) (s t : ExactCarrierState n)
    (he : ∀ e : MatchingEntry n, e.val.1 = j → s.2 e = t.2 e) :
    carrierResidualStage j (carrierOffEntries j) s =
      carrierResidualStage j (carrierOffEntries j) t := by
  unfold carrierResidualStage
  rw [he (carrierDiagonalEntry j) rfl]
  congr 1
  apply List.flatMap_congr
  intro e he'
  rw [he e ((mem_carrierOffEntries j e).mp he').1]

theorem carrierResidualPrefix_congr {n q : ℕ} (s t : ExactCarrierState n)
    (he : ∀ e : MatchingEntry n, e.val.1.val < q → s.2 e = t.2 e) :
    carrierResidualPrefix q s = carrierResidualPrefix q t := by
  apply List.flatMap_congr
  intro j hj
  have hd : carrierDiagonalEntry j ∈ carrierEntriesBefore n q := by
    apply List.mem_flatMap.mpr
    exact ⟨j,hj,(mem_carrierFullStage j _).mpr rfl⟩
  have hqj : j.val < q := (mem_carrierEntriesBefore _).mp hd
  apply carrierResidualStage_congr
  intro e hej
  exact he e (by simpa only [hej] using hqj)

theorem carrierResidualPrefix_past_step {n q : ℕ} (hq : q < n) (s : ExactCarrierState n) :
    carrierResidualPrefix q (carrierStateBefore (q+1) s) =
      carrierResidualPrefix q (carrierStateBefore q s) := by
  apply carrierResidualPrefix_congr
  intro e he
  rw [carrierStateBefore_succ hq]
  exact exactCarrierStage_snd_past ⟨q,hq⟩ _ e he

/-- Complete first-row invariant after each endpoint stage. The state is the
actual finite-function carrier transformation, and both words are the canonical
endpoint-stage words with their original multiplicities. -/
theorem firstRowProcess_carrierPrefix {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (s : ExactCarrierState n) :
    firstRowProcess (carrierInputPrefix q s) [] =
      (List.replicate (carrierZerosBefore q s) 0 ++
        carrierLettersBefore q (carrierStateBefore q s),
        carrierResidualPrefix q (carrierStateBefore q s)) := by
  induction q with
  | zero => simp [carrierInputPrefix,carrierZerosBefore,carrierLettersBefore,
      carrierResidualPrefix,firstRowProcess]
  | succ q ih =>
    have hqn : q < n := by omega
    let j : Fin n := ⟨q,hqn⟩
    let u := carrierStateBefore q s
    let t := carrierStateBefore (q+1) s
    have hstate : exactCarrierSequence (carrierOffEntries j ++ [carrierDiagonalEntry j]) u = t :=
      (carrierStateBefore_succ hqn s).symm
    have hinput : carrierInputStage j (carrierOffEntries j) u =
        carrierInputStage j (carrierOffEntries j) s := carrierInputStage_before j s
    have hqcarrier : u.1 j = s.1 j := exactCarrierBefore_fst_future s j le_rfl
    have hstage := firstRowProcess_exactCarrierStage j (carrierOffEntries j)
      (carrierOffEntries_ordered j) (carrierOffEntries_stage j) u (carrierZerosBefore q s)
    dsimp only at hstage
    rw [hstate,hinput,carrierLetters_stage_eq,carrierLetters_stage_eq,hqcarrier] at hstage
    rw [carrierInputPrefix_succ hqn,firstRowProcess_append,ih (by omega)]
    simp only [Prod.fst,Prod.snd]
    rw [hstage]
    simp only [Prod.fst,Prod.snd]
    rw [carrierZerosBefore_succ hqn,carrierLettersBefore_succ hqn,
      carrierResidualPrefix_succ hqn,carrierResidualPrefix_past_step hqn]
    simp only [List.append_assoc,j,t]

/-- At every endpoint stage, the tableau of the exact residual monomial is
obtained by deleting the first row of the actual input tableau. -/
theorem pairInsertList_carrierPrefix_tail {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (s : ExactCarrierState n) :
    (pairInsertList (carrierInputPrefix q s)).tail =
      pairInsertList (carrierResidualPrefix q (carrierStateBefore q s)) := by
  rw [pairInsertList_tail,firstRowProcess_carrierPrefix q hq]

theorem pairInsertList_exactCarrierEquiv_tail (n : ℕ) (s : ExactCarrierState n) :
    (pairInsertList (carrierInputPrefix n s)).tail =
      pairInsertList (carrierResidualPrefix n (exactCarrierEquiv n s)) := by
  simpa only [carrierStateBefore_full] using pairInsertList_carrierPrefix_tail n le_rfl s

theorem carrierStateBefore_snd_stable {n : ℕ} (s : ExactCarrierState n) (r : ℕ) :
    r ≤ n → ∀ q ≤ r, ∀ e : MatchingEntry n, e.val.1.val < q →
      (carrierStateBefore r s).2 e = (carrierStateBefore q s).2 e := by
  induction r with
  | zero =>
    intro hr q hq e he
    omega
  | succ r ih =>
    intro hr q hq e he
    by_cases hqr : q = r+1
    · subst q
      rfl
    · have hqr' : q ≤ r := by omega
      have hrn : r < n := by omega
      rw [carrierStateBefore_succ hrn,
        exactCarrierStage_snd_past ⟨r,hrn⟩ _ e (by change e.val.1.val < r; omega)]
      exact ih (by omega) q hqr' e he

theorem carrierResidualPrefix_final {n : ℕ} (q : ℕ) (hq : q ≤ n) (s : ExactCarrierState n) :
    carrierResidualPrefix q (exactCarrierEquiv n s) =
      carrierResidualPrefix q (carrierStateBefore q s) := by
  apply carrierResidualPrefix_congr
  intro e he
  rw [←carrierStateBefore_full]
  exact carrierStateBefore_snd_stable s n le_rfl q hq e he

/-- The stage residual can be read from the final carrier-equivalence output,
because later endpoint stages never alter an earlier residual exponent. -/
theorem pairInsertList_exactCarrierEquiv_prefix_tail {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (s : ExactCarrierState n) :
    (pairInsertList (carrierInputPrefix q s)).tail =
      pairInsertList (carrierResidualPrefix q (exactCarrierEquiv n s)) := by
  rw [carrierResidualPrefix_final q hq]
  exact pairInsertList_carrierPrefix_tail q hq s

end FourPapers.Symmetric
end
/- End source CarrierGlobalDeletion.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MonomialSerialization\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MonomialSerialization"

/- Begin source MonomialSerialization.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourPapers.Symmetric

/-- Expand a coordinate list with its exact natural multiplicities. -/
def expandCoordinates {α : Type*} (m : α → ℕ) (es : List α) : List α :=
  es.flatMap (fun e => List.replicate (m e) e)

theorem count_expandCoordinates {α : Type*} [DecidableEq α]
    (m : α → ℕ) (es : List α) (hn : es.Nodup) (a : α) :
    (expandCoordinates m es).count a = if a ∈ es then m a else 0 := by
  induction es with
  | nil => simp [expandCoordinates]
  | cons b es ih =>
    have hb := List.nodup_cons.mp hn
    have hi := ih hb.2
    change (es.flatMap (fun e => List.replicate (m e) e)).count a = _ at hi
    rw [expandCoordinates,List.flatMap_cons,List.count_append,hi]
    by_cases hab : a = b
    · subst a
      simp [hb.1]
    · simp [List.count_replicate,hab,Ne.symm hab]

theorem pairwise_expandCoordinates {α : Type*} [Preorder α]
    (m : α → ℕ) {es : List α} (hs : es.Pairwise (· ≤ ·)) :
    (expandCoordinates m es).Pairwise (· ≤ ·) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro a ha
    exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · apply hs.imp
    intro a b hab x hx y hy
    have hx' := (List.mem_replicate.mp hx).2
    have hy' := (List.mem_replicate.mp hy).2
    subst x
    subst y
    exact hab

/-- Canonical sorted serialization is uniquely determined by coordinate order
and multiplicities. Coordinates of multiplicity zero may be present or absent. -/
theorem sort_toMultiset_eq_expand {α : Type*} [LinearOrder α]
    (m : α →₀ ℕ) (es : List α) (hs : es.Pairwise (· ≤ ·))
    (hn : es.Nodup) (hcover : ∀ a ∈ m.support, a ∈ es) :
    m.toMultiset.sort (· ≤ ·) = expandCoordinates m es := by
  have hp : (m.toMultiset.sort (· ≤ ·)).Perm (expandCoordinates m es) := by
    apply List.perm_iff_count.mpr
    intro a
    have hc : (m.toMultiset.sort (· ≤ ·)).count a = m a := by
      rw [← Multiset.coe_count]
      rw [Multiset.sort_eq,Finsupp.count_toMultiset]
    rw [hc,count_expandCoordinates m es hn]
    by_cases ha : a ∈ es
    · simp only [if_pos ha]
    · rw [if_neg ha]
      apply Finsupp.notMem_support_iff.mp
      intro ham
      exact ha (hcover a ham)
  exact hp.eq_of_pairwise' (Multiset.pairwise_sort _ _)
    (pairwise_expandCoordinates m hs)

theorem sort_toMultiset_eq_univ_expand {α : Type*} [LinearOrder α] [Fintype α]
    (m : α →₀ ℕ) :
    m.toMultiset.sort (· ≤ ·) =
      expandCoordinates m ((Finset.univ : Finset α).sort (· ≤ ·)) := by
  apply sort_toMultiset_eq_expand m _ (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _)
  intro a ha
  simp only [Finset.mem_sort,Finset.mem_univ]

theorem carrierResidualStage_eq_expand {n : ℕ} (j : Fin n) (s : ExactCarrierState n) :
    carrierResidualStage j (carrierOffEntries j) s =
      (carrierFullStage j).flatMap (fun e =>
        List.replicate (s.2 e) (e.val.2.val+1,e.val.1.val+1)) := by
  unfold carrierResidualStage carrierFullStage carrierPairsOfEntries
  rw [List.flatMap_append,List.flatMap_singleton]
  congr 1
  apply List.flatMap_congr
  intro e he
  rw [((mem_carrierOffEntries j e).mp he).1]

theorem carrierResidualPrefix_eq_expand {n q : ℕ} (s : ExactCarrierState n) :
    carrierResidualPrefix q s =
      (carrierEntriesBefore n q).flatMap (fun e =>
        List.replicate (s.2 e) (e.val.2.val+1,e.val.1.val+1)) := by
  simp only [carrierResidualPrefix,carrierEntriesBefore,List.flatMap_assoc]
  apply List.flatMap_congr
  intro j hj
  exact carrierResidualStage_eq_expand j s

/-- The residual stage word is the canonical monomial word on the smaller
matrix, with every vertex shifted by one to retain the original labels. -/
theorem carrierResidualPrefix_full_eq_monomialPairs {n : ℕ} (s : ExactCarrierState n) :
    carrierResidualPrefix n s =
      (monomialPairs (Finsupp.equivFunOnFinite.symm s.2)).map
        (fun p => (p.1.val+1,p.2.val+1)) := by
  rw [carrierResidualPrefix_eq_expand,carrierEntriesBefore_full]
  simp only [monomialPairs,sort_toMultiset_eq_univ_expand,expandCoordinates,
    List.map_flatMap,List.map_replicate,List.map_map,Function.comp_def] <;> rfl

/-- Restricting the endpoint stages is exactly filtering the final canonical
word by its larger endpoint. This includes the empty prefix. -/
theorem carrierResidualPrefix_eq_filter {n : ℕ} (q : ℕ) (s : ExactCarrierState n) :
    carrierResidualPrefix q s =
      (carrierResidualPrefix n s).filter (fun p => p.2 ≤ q) := by
  have he : carrierEntriesBefore n q =
      (carrierEntriesBefore n n).filter (fun e => e.val.1.val < q) := by
    apply (carrierEntriesBefore_sorted n q).eq_of_mem_iff
      ((List.Pairwise.filter _ (carrierEntriesBefore_sorted n n).pairwise).sortedLT)
    intro e
    simp only [List.mem_filter,mem_carrierEntriesBefore,decide_eq_true_eq]
    exact ⟨fun h => ⟨e.val.1.isLt,h⟩,fun h => h.2⟩
  rw [carrierResidualPrefix_eq_expand,carrierResidualPrefix_eq_expand,he]
  have hf (es : List (MatchingEntry n)) :
      (es.filter (fun e => e.val.1.val < q)).flatMap
          (fun e => List.replicate (s.2 e) (e.val.2.val+1,e.val.1.val+1)) =
        (es.flatMap (fun e => List.replicate (s.2 e)
          (e.val.2.val+1,e.val.1.val+1))).filter (fun p => p.2 ≤ q) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      by_cases hq : e.val.1.val < q
      · simp [hq,ih,List.filter_replicate,Nat.succ_le_iff]
      · simp [hq,ih,List.filter_replicate,Nat.succ_le_iff]
  exact hf _

end FourPapers.Symmetric
end
/- End source MonomialSerialization.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MatchingMonomials\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MatchingMonomials"

/- Begin source MatchingMonomials.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

/-!
# Compatibility import for MatchingMonomials

The exact accepted aggregate supplies this original API. The full earlier
source, source hashes, and declaration-provider map are preserved in
`recovery/matching_aggregate_reuse_20261102/`. No mathematical statement is
replaced by an assumption. The aggregate retains original license notices.
-/
end
/- End source MatchingMonomials.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MonomialSemistandard\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MonomialSemistandard"

/- Begin source MonomialSemistandard.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FourPapers.Symmetric

/-- The original finite-alphabet edge word, with its labels viewed as natural
numbers. This changes no factors or multiplicities. -/
noncomputable def natMonomialPairs {n : ℕ} (m : MatchingEntry n →₀ ℕ) : List (ℕ × ℕ) :=
  (monomialPairs m).map fun p => (p.1.val,p.2.val)

theorem natMonomialPairs_ordered {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    Inflation.OrderedPairs (natMonomialPairs m) := by
  constructor
  · intro p hp
    simp only [natMonomialPairs,monomialPairs,List.map_map,List.mem_map,
      Function.comp_apply] at hp
    obtain ⟨e,he,rfl⟩ := hp
    exact e.property
  · simp only [natMonomialPairs,monomialPairs,List.map_map,List.pairwise_map,
      Function.comp_apply]
    apply (Multiset.pairwise_sort m.toMultiset (· ≤ ·)).imp
    intro e f hef
    change e.val ≤ f.val at hef
    rcases Prod.Lex.le_iff.mp hef with h | ⟨h,h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨congrArg Fin.val h,h'⟩

/-- Semistandardness in Theorem 2.1 for every symmetric monomial, all matrix
sizes, and unrestricted multiplicities. The theorem refers to the original
paired-insertion algorithm on `Fin n`. -/
theorem pairedTableau_isTableauRows {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    (pairedTableau m).IsTableauRows := by
  have hf : StrictMono (fun x : Fin n => x.val) := fun _ _ h => h
  apply (isTableauRows_map_iff_strictMono _ hf (pairedTableau m)).mp
  have hmap : pairInsertList (natMonomialPairs m) =
      (pairedTableau m).map (List.map (fun x : Fin n => x.val)) := by
    simpa only [natMonomialPairs,pairedTableau,List.map_nil] using
      pairInsertList_map_strictMono (fun x : Fin n => x.val) hf (monomialPairs m) []
  rw [←hmap]
  exact (natMonomialPairs_ordered m).isTableauRows

theorem Inflation.OrderedPairs.filter {w : List (ℕ × ℕ)}
    (hw : Inflation.OrderedPairs w) (p : ℕ × ℕ → Bool) :
    Inflation.OrderedPairs (w.filter p) := by
  constructor
  · intro x hx
    exact hw.lower_le_upper x (List.mem_filter.mp hx).1
  · exact hw.ordered.filter p

end FourPapers.Symmetric
end
/- End source MonomialSemistandard.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN SemistandardSurjectivity\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN SemistandardSurjectivity"

/- Begin source SemistandardSurjectivity.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric
open TauCeti Inflation

theorem tableauNatRows_isTableau {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    (tableauNatRows T).IsTableauRows := by
  apply (isTableauRows_map_iff_strictMono (fun x : Fin μ.card => x.val)
    (fun _ _ h => h) T.toRows).mpr
  exact T.isTableauRows_toRows

theorem mem_flatten_tableauNatRows_iff {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (x : ℕ) :
    x ∈ (tableauNatRows T).flatten ↔ x < μ.card := by
  constructor
  · intro hx
    rw [tableauNatRows,←List.map_flatten] at hx
    obtain ⟨a,ha,hax⟩ := List.mem_map.mp hx
    exact hax ▸ a.isLt
  · intro hx
    rw [tableauNatRows,←List.map_flatten]
    apply List.mem_map.mpr
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    apply T.flatten_toRows_perm.mem_iff.mpr
    exact List.mem_finRange _

theorem length_flatten_tableauNatRows {μ : YoungDiagram}
    (T : StandardYoungTableau μ) : (tableauNatRows T).flatten.length = μ.card := by
  rw [tableauNatRows,←List.map_flatten,List.length_map]
  simpa only [List.length_finRange] using T.flatten_toRows_perm.length_eq

theorem evenRows_iff_map {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (rows : List (List α)) :
    EvenRows (rows.map (List.map f)) ↔ EvenRows rows := by
  unfold EvenRows
  have he (i : ℕ) : ((rows.map (List.map f)).getD i []).length = (rows.getD i []).length := by
    simpa only [List.map_nil,List.length_map] using
      congrArg List.length (List.getD_map rows [] (List.map f) (n := i))
  simp only [he]

/-- Every even-row semistandard tableau is the output of the original paired
algorithm on an ordered word, including repeated entries and loops. -/
theorem exists_orderedPairs_of_evenTableau {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (heven : EvenRows rows) :
    ∃ w : List (ℕ × ℕ), OrderedPairs w ∧ pairInsertList w = rows := by
  let μ := List.tableauShape rows hrows
  have hshape : rows.map List.length = μ.rowLens := (List.rowLens_tableauShape rows hrows).symm
  let T := weakFillingOfRows hrows hshape
  let S := T.standard
  have hcollapse : (tableauNatRows S).map (List.map T.collapse) = rows :=
    T.collapse_standard_rows.trans (weakFillingOfRows_rows hrows hshape)
  have hseven : EvenRows (tableauNatRows S) := by
    apply (evenRows_iff_map T.collapse (tableauNatRows S)).mp
    rw [hcollapse]
    exact heven
  obtain ⟨w,hw,hT⟩ := exists_matchingWord (tableauNatRows_isTableau S) hseven
    (tableauNatRows_flatten_nodup S)
  have hcard : Fintype.card (Incidence w) = μ.card := by
    rw [card_incidence,←pairInsertList_flatten_length,hT,length_flatten_tableauNatRows]
  have hdense : ∀ x, x ∈ endpointWord w ↔ x < Fintype.card (Incidence w) := by
    intro x
    rw [hcard,←mem_flatten_tableauNatRows_iff S x,←hT]
    simpa only [List.flatten_nil,List.append_nil] using
      (flatten_pairInsertList_perm w []).mem_iff.symm
  have hfilled : ∀ x ∈ endpointWord w, ∀ y ∈ endpointWord w,
      ∀ k, x ≤ k → k ≤ y → k ∈ endpointWord w := by
    intro x hx y hy k hxk hky
    exact (hdense k).mpr (hky.trans_lt ((hdense y).mp hy))
  have hdesc : ∀ k, k ∈ endpointWord w → k+1 ∈ endpointWord w →
      T.collapse k = T.collapse (k+1) → ¬RowDescends k (k+1) (pairInsertList w) := by
    intro k hk hk' heq
    have hkN : k < μ.card := by simpa only [hcard] using (hdense k).mp hk
    have hkN' : k+1 < μ.card := by simpa only [hcard] using (hdense (k+1)).mp hk'
    rw [hT]
    exact T.no_fiber_descents ⟨k,hkN⟩ ⟨k+1,hkN'⟩ (by change k < k+1; omega) heq
  have hcompat := hw.fiberCompatible_of_no_descents T.collapse_monotone hfilled hdesc
  refine ⟨collapsePairs T.collapse w,hw.collapsePairs_ordered T.collapse_monotone hcompat,?_⟩
  rw [hw.insertion_collapsePairs T.collapse_monotone hcompat hdense,hT,hcollapse]

def finiteWordEntries {n : ℕ} (w : List (ℕ × ℕ)) (hw : OrderedPairs w)
    (hb : ∀ p ∈ w, p.2 < n) : List (MatchingEntry n) :=
  w.attach.map fun p =>
    ⟨toLex (⟨p.val.2,hb p.val p.property⟩,
      ⟨p.val.1,(hw.lower_le_upper p.val p.property).trans_lt (hb p.val p.property)⟩),
      hw.lower_le_upper p.val p.property⟩

theorem finiteWordEntries_pairwise {n : ℕ} (w : List (ℕ × ℕ)) (hw : OrderedPairs w)
    (hb : ∀ p ∈ w, p.2 < n) :
    (finiteWordEntries w hw hb).Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hiw : i < w.length := by simpa only [finiteWordEntries,List.length_map,List.length_attach] using hi
  have hjw : j < w.length := by simpa only [finiteWordEntries,List.length_map,List.length_attach] using hj
  have h := (List.pairwise_iff_getElem.mp hw.ordered) i j hiw hjw hij
  simp only [finiteWordEntries,List.getElem_map,List.getElem_attach]
  apply Prod.Lex.le_iff.mpr
  rcases h with h | ⟨h,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨Fin.ext h,h'⟩

theorem finiteWordEntries_natPairs {n : ℕ} (w : List (ℕ × ℕ)) (hw : OrderedPairs w)
    (hb : ∀ p ∈ w, p.2 < n) :
    (finiteWordEntries w hw hb).map (fun e => (e.val.2.val,e.val.1.val)) = w := by
  simp only [finiteWordEntries,List.map_map,Function.comp_def]
  exact List.attach_map_subtype_val w

noncomputable def monomialOfOrderedPairs {n : ℕ} (w : List (ℕ × ℕ)) (hw : OrderedPairs w)
    (hb : ∀ p ∈ w, p.2 < n) : MatchingEntry n →₀ ℕ :=
  (↑(finiteWordEntries w hw hb) : Multiset (MatchingEntry n)).toFinsupp

theorem natMonomialPairs_monomialOfOrderedPairs {n : ℕ} (w : List (ℕ × ℕ))
    (hw : OrderedPairs w) (hb : ∀ p ∈ w, p.2 < n) :
    natMonomialPairs (monomialOfOrderedPairs w hw hb) = w := by
  simp only [natMonomialPairs,monomialPairs,monomialOfOrderedPairs,
    Multiset.toFinsupp_toMultiset,Multiset.coe_sort]
  rw [List.mergeSort_eq_self (· ≤ ·) (finiteWordEntries_pairwise w hw hb),List.map_map]
  exact finiteWordEntries_natPairs w hw hb

/-- Surjectivity for the precise finite matrix alphabet, with no restriction on
degree, number of rows, repeated entries, or diagonal variables. -/
theorem exists_monomial_of_evenTableau {n : ℕ} {rows : List (List (Fin n))}
    (hrows : rows.IsTableauRows) (heven : EvenRows rows) :
    ∃ m : MatchingEntry n →₀ ℕ, pairedTableau m = rows := by
  let numeric := rows.map (List.map (fun x : Fin n => x.val))
  have hf : StrictMono (fun x : Fin n => x.val) := fun _ _ h => h
  have ht : numeric.IsTableauRows :=
    (isTableauRows_map_iff_strictMono _ hf rows).mpr hrows
  have he : EvenRows numeric := (evenRows_iff_map _ rows).mpr heven
  obtain ⟨w,hw,hout⟩ := exists_orderedPairs_of_evenTableau ht he
  have hb : ∀ p ∈ w, p.2 < n := by
    intro p hp
    have hm : p.2 ∈ (pairInsertList w).flatten := by
      apply (flatten_pairInsertList_perm w []).mem_iff.mpr
      simpa only [List.flatten_nil,List.append_nil] using
        (mem_endpointWord.mpr ⟨p,hp,Or.inr rfl⟩)
    rw [hout] at hm
    simp only [numeric,←List.map_flatten,List.mem_map] at hm
    obtain ⟨x,hx,hxp⟩ := hm
    exact hxp ▸ x.isLt
  let m := monomialOfOrderedPairs w hw hb
  refine ⟨m,?_⟩
  have hmap : (pairedTableau m).map (List.map (fun x : Fin n => x.val)) = numeric := by
    unfold pairedTableau
    rw [←pairInsertList_map_strictMono (fun x : Fin n => x.val) hf (monomialPairs m) []]
    change pairInsertList (natMonomialPairs m) = numeric
    dsimp only [m]
    rw [natMonomialPairs_monomialOfOrderedPairs]
    exact hout
  apply Fin.val_injective.list_map.list_map
  exact hmap

end FourPapers.Symmetric
end
/- End source SemistandardSurjectivity.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN InflationChains\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN InflationChains"

/- Begin source InflationChains.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Chains before and after canonical inflation

Selected incidences remember the actual occurrence of each original edge.
Thus parallel copies can be used separately, whereas the two orientations of
one occurrence cannot both be used. Collapse preserves strict row and column
inequalities by the matching one-use condition.
-/

namespace FourPapers.Symmetric.Inflation
open MatchingChains

theorem partners_inflate {w : List (ℕ × ℕ)} (o : Incidence w) :
    Partners (inflate w) (label o).val (label (partner o)).val := by
  simpa only [prefix_length] using partners_prefix o o.edge.isLt

theorem OrderedPairs.partnerMap_label {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    (o : Incidence w) :
    partnerMap (inflate w) (label o).val = (label (partner o)).val :=
  hw.matching_inflate.partnerMap_eq (partners_inflate o)

theorem mem_endpoints_inflate_iff {w : List (ℕ × ℕ)} {x : ℕ} :
    x ∈ endpointWord (inflate w) ↔ x < Fintype.card (Incidence w) := by
  constructor
  · intro hx
    have hp : x ∈ endpointWord («prefix» w w.length) := by simpa only [prefix_length] using hx
    obtain ⟨o,_,hlo⟩ := mem_endpoints_prefix_iff.mp hp
    exact hlo ▸ (label o).isLt
  · intro hx
    let o := orderedIncidences w ⟨x,hx⟩
    have hl : (label o).val = x := by simp [o]
    have hp : x ∈ endpointWord («prefix» w w.length) :=
      mem_endpoints_prefix_iff.mpr ⟨o,o.edge.isLt,hl⟩
    simpa only [prefix_length] using hp

/-- A matching chain has at most one row in any original vertex block.
The alternative would either contradict decreasing partners or use an edge
twice. This is the strictness assertion in Section 2.3. -/
theorem OrderedPairs.chain_collapse_strict {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    {C : Finset ℕ} (hC : IsChain (partnerMap (inflate w)) C)
    {r s : ℕ} (hr : r ∈ C) (hs : s ∈ C) (hrs : r < s) :
    collapse w r < collapse w s := by
  have hrN := mem_endpoints_inflate_iff.mp (hC.rows_mem_endpoints hr)
  have hsN := mem_endpoints_inflate_iff.mp (hC.rows_mem_endpoints hs)
  let x := orderedIncidences w ⟨r,hrN⟩
  let y := orderedIncidences w ⟨s,hsN⟩
  have hlx : (label x).val = r := by simp [x]
  have hly : (label y).val = s := by simp [y]
  have hle := collapse_monotone w hrs.le
  apply lt_of_le_of_ne hle
  intro he
  have hv : vertex x = vertex y := by
    simpa only [← hlx, ← hly, collapse_label] using he
  have hlabels : (label x).val < (label y).val := by omega
  rcases hw.partner_label_lt_or_paired hlabels hv with hp | hp
  · have hdec := hC.decreasing r hr s hs hrs
    have hpr : partnerMap (inflate w) r = (label (partner x)).val := by
      simpa only [hlx] using hw.partnerMap_label x
    have hps : partnerMap (inflate w) s = (label (partner y)).val := by
      simpa only [hly] using hw.partnerMap_label y
    rw [hpr,hps] at hdec
    omega
  · have hpr : partnerMap (inflate w) r = s := by
      simpa only [hlx,hp,hly] using hw.partnerMap_label x
    exact hC.oneUse r hr (hpr.symm ▸ hs)

/-- A folded chain chooses actual edge occurrences, with increasing original
rows and decreasing original columns. The final field prohibits using the
other orientation of the same occurrence. -/
structure IsOccurrenceChain {w : List (ℕ × ℕ)} (C : Finset (Incidence w)) : Prop where
  increasing : ∀ x ∈ C, ∀ y ∈ C, x < y → vertex x < vertex y
  decreasing : ∀ x ∈ C, ∀ y ∈ C, x < y → vertex (partner y) < vertex (partner x)
  oneUse : ∀ x ∈ C, partner x ∉ C

noncomputable def labelSet {w : List (ℕ × ℕ)} (C : Finset (Incidence w)) : Finset ℕ :=
  C.image fun o => (label o).val

theorem labelSet_card {w : List (ℕ × ℕ)} (C : Finset (Incidence w)) :
    (labelSet C).card = C.card := Finset.card_image_of_injective _ label_injective

theorem label_strictMono {w : List (ℕ × ℕ)} :
    StrictMono (fun o : Incidence w => (label o).val) :=
  fun _ _ h => (orderedIncidences w).symm.strictMono h

/-- Inflation and collapse give exactly the same admissible chains, retaining
their number of selected edge occurrences. -/
theorem OrderedPairs.chain_labelSet_iff {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    (C : Finset (Incidence w)) :
    IsChain (partnerMap (inflate w)) (labelSet C) ↔ IsOccurrenceChain C := by
  classical
  constructor
  · intro hC
    refine ⟨?_,?_,?_⟩
    · intro x hx y hy hxy
      have h := hw.chain_collapse_strict hC
        (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy)
        (label_strictMono hxy)
      simpa only [collapse_label] using h
    · intro x hx y hy hxy
      have hT := hC.transpose hw.matching_inflate.partnerMap_involutive
      have hx' : partnerMap (inflate w) (label x).val ∈
          (labelSet C).image (partnerMap (inflate w)) :=
        Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hx)
      have hy' : partnerMap (inflate w) (label y).val ∈
          (labelSet C).image (partnerMap (inflate w)) :=
        Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy)
      have hdec := hC.decreasing (label x).val (Finset.mem_image_of_mem _ hx)
        (label y).val (Finset.mem_image_of_mem _ hy) (label_strictMono hxy)
      have h := hw.chain_collapse_strict hT hy' hx' hdec
      simpa only [hw.partnerMap_label, collapse_label] using h
    · intro x hx hbad
      apply hC.oneUse (label x).val (Finset.mem_image_of_mem _ hx)
      rw [hw.partnerMap_label]
      exact Finset.mem_image_of_mem _ hbad
  · intro hC
    constructor
    · intro r hr s hs hrs
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hs
      have hxy : x < y := label_strictMono.lt_iff_lt.mp hrs
      rw [hw.partnerMap_label,hw.partnerMap_label]
      exact (label_lt_iff _ _).mpr (Or.inl (hC.decreasing x hx y hy hxy))
    · intro r hr hbad
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
      rw [hw.partnerMap_label] at hbad
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hbad
      have he' : y = partner x := label_injective he
      exact hC.oneUse x hx (he' ▸ hy)

theorem same_edge_eq_or_partner {w : List (ℕ × ℕ)} {x y : Incidence w}
    (he : x.edge = y.edge) : x = y ∨ partner x = y := by
  rcases x with ⟨i,s⟩
  rcases y with ⟨j,t⟩
  simp only at he
  subst j
  cases s <;> cases t <;> simp [partner]

/-- One-use means that distinct selected incidences belong to distinct edge
occurrences, even when several occurrences have the same two original vertices. -/
theorem IsOccurrenceChain.edge_injective {w : List (ℕ × ℕ)}
    {C : Finset (Incidence w)} (hC : IsOccurrenceChain C) :
    Set.InjOn Incidence.edge (↑C : Set (Incidence w)) := by
  intro x hx y hy he
  rcases same_edge_eq_or_partner he with h | h
  · exact h
  · exact False.elim (hC.oneUse x hx (h.symm ▸ hy))

noncomputable def occurrenceSet (w : List (ℕ × ℕ)) (C : Finset ℕ) : Finset (Incidence w) :=
  Finset.univ.filter fun o => (label o).val ∈ C

@[simp] theorem mem_occurrenceSet {w : List (ℕ × ℕ)} {C : Finset ℕ}
    (o : Incidence w) : o ∈ occurrenceSet w C ↔ (label o).val ∈ C := by
  classical
  simp [occurrenceSet]

@[simp] theorem occurrenceSet_labelSet {w : List (ℕ × ℕ)} (C : Finset (Incidence w)) :
    occurrenceSet w (labelSet C) = C := by
  classical
  ext o
  simp only [mem_occurrenceSet, labelSet, Finset.mem_image]
  constructor
  · rintro ⟨p,hp,he⟩
    exact label_injective he ▸ hp
  · intro ho
    exact ⟨o,ho,rfl⟩

theorem labelSet_occurrenceSet {w : List (ℕ × ℕ)} (C : Finset ℕ)
    (hC : ∀ r ∈ C, r < Fintype.card (Incidence w)) :
    labelSet (occurrenceSet w C) = C := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp hr
    exact (mem_occurrenceSet o).mp ho
  · intro hr
    let o := orderedIncidences w ⟨r,hC r hr⟩
    have hl : (label o).val = r := by simp [o]
    exact Finset.mem_image.mpr ⟨o,(mem_occurrenceSet o).mpr (hl.symm ▸ hr),hl⟩

theorem OrderedPairs.chain_occurrenceSet {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    {C : Finset ℕ} (hC : IsChain (partnerMap (inflate w)) C) :
    IsOccurrenceChain (occurrenceSet w C) := by
  apply (hw.chain_labelSet_iff _).mp
  rw [labelSet_occurrenceSet C
    (fun r hr => mem_endpoints_inflate_iff.mp (hC.rows_mem_endpoints hr))]
  exact hC

theorem occurrenceSet_card_of_chain {w : List (ℕ × ℕ)}
    {C : Finset ℕ} (hC : IsChain (partnerMap (inflate w)) C) :
    (occurrenceSet w C).card = C.card := by
  rw [← labelSet_card, labelSet_occurrenceSet C
    (fun r hr => mem_endpoints_inflate_iff.mp (hC.rows_mem_endpoints hr))]

noncomputable def occurrenceEndpoints {w : List (ℕ × ℕ)}
    (C : Finset (Incidence w)) : Finset (Incidence w) := C ∪ C.image partner

theorem OrderedPairs.endpoints_labelSet {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    (C : Finset (Incidence w)) :
    endpoints (partnerMap (inflate w)) (labelSet C) = labelSet (occurrenceEndpoints C) := by
  classical
  simp only [endpoints, labelSet, occurrenceEndpoints, Finset.image_union, Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro o ho
  exact hw.partnerMap_label o

/-- Distinct colors use distinct original edge occurrences, represented by
their two incidence positions. -/
structure IsOccurrencePacking {w : List (ℕ × ℕ)} {κ : Type*}
    (P : κ → Finset (Incidence w)) : Prop where
  chain : ∀ c, IsOccurrenceChain (P c)
  disjoint : ∀ c d, c ≠ d → Disjoint (occurrenceEndpoints (P c)) (occurrenceEndpoints (P d))

theorem OrderedPairs.packing_labelSet_iff {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    {κ : Type*} (P : κ → Finset (Incidence w)) :
    IsPacking (partnerMap (inflate w)) (fun c => labelSet (P c)) ↔ IsOccurrencePacking P := by
  classical
  constructor
  · intro hP
    constructor
    · intro c
      exact (hw.chain_labelSet_iff _).mp (hP.chain c)
    · intro c d hcd
      have hh := hP.disjoint c d hcd
      rw [hw.endpoints_labelSet,hw.endpoints_labelSet] at hh
      exact (Finset.disjoint_image label_injective).mp hh
  · intro hP
    constructor
    · intro c
      exact (hw.chain_labelSet_iff _).mpr (hP.chain c)
    · intro c d hcd
      rw [hw.endpoints_labelSet,hw.endpoints_labelSet]
      exact (Finset.disjoint_image label_injective).mpr (hP.disjoint c d hcd)

theorem OrderedPairs.packing_occurrenceSet {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    {κ : Type*} {P : κ → Finset ℕ} (hP : IsPacking (partnerMap (inflate w)) P) :
    IsOccurrencePacking (fun c => occurrenceSet w (P c)) := by
  apply (hw.packing_labelSet_iff _).mp
  have hsets : (fun c => labelSet (occurrenceSet w (P c))) = P := by
    funext c
    exact labelSet_occurrenceSet (P c)
      (fun r hr => mem_endpoints_inflate_iff.mp ((hP.chain c).rows_mem_endpoints hr))
  rw [hsets]
  exact hP

/-- The transfer applies simultaneously to every color and preserves the full
number of covered edge occurrences. There is no degree or color bound. -/
theorem packing_occurrenceSet_size {w : List (ℕ × ℕ)} {κ : Type*} [Fintype κ]
    {P : κ → Finset ℕ} (hP : IsPacking (partnerMap (inflate w)) P) :
    (∑ c, (occurrenceSet w (P c)).card) = ∑ c, (P c).card := by
  apply Finset.sum_congr rfl
  intro c hc
  exact occurrenceSet_card_of_chain (hP.chain c)

theorem packing_labelSet_size {w : List (ℕ × ℕ)} {κ : Type*} [Fintype κ]
    (P : κ → Finset (Incidence w)) :
    (∑ c, (labelSet (P c)).card) = ∑ c, (P c).card := by
  simp only [labelSet_card]

end FourPapers.Symmetric.Inflation
end
/- End source InflationChains.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN SemistandardBijection\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN SemistandardBijection"

/- Begin source SemistandardBijection.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace FourPapers.Symmetric
open TauCeti Inflation

theorem Inflation.OrderedPairs.exists_standardization {w : List (ℕ × ℕ)} (hw : OrderedPairs w)
    {μ : YoungDiagram} (hshape : (pairInsertList w).map List.length = μ.rowLens) :
    ∃ S : StandardYoungTableau μ,
      pairInsertList (inflate w) = tableauNatRows S ∧
      (tableauNatRows S).map (List.map (collapse w)) = pairInsertList w ∧
      FibersRise (collapse w) (tableauNatRows S) := by
  have hshape' : (pairInsertList (inflate w)).map List.length = μ.rowLens := by
    rw [hw.insertion_collapse,List.map_map] at hshape
    simpa only [Function.comp_def,List.length_map] using hshape
  have hcard : Fintype.card (Incidence w) = μ.card := by
    rw [card_incidence,←pairInsertList_flatten_length,List.length_flatten,hshape,
      YoungDiagram.sum_rowLens_eq_card]
  have hb : ∀ x ∈ (pairInsertList (inflate w)).flatten, x < μ.card := by
    intro x hx
    have hm : x ∈ endpointWord (inflate w) := by
      simpa only [List.flatten_nil,List.append_nil] using
        (flatten_pairInsertList_perm (inflate w) []).mem_iff.mp hx
    rw [←hcard]
    exact mem_endpoints_inflate_iff.mp hm
  obtain ⟨S,hS⟩ := exists_tableauNatRows_of_bounds hw.matching_inflate.isTableauRows
    hshape' hw.matching_inflate.output_distinct hb
  refine ⟨S,hS.symm,?_,?_⟩
  · rw [hS]
    exact hw.insertion_collapse.symm
  · have h := hw.prefix_fibersRise w.length
    simpa only [prefix_length,hS] using h

/-- Paired insertion is injective on all canonically ordered symmetric words,
with arbitrary repeated endpoints. The proof uses unique standardization and
the actual matching bijection. -/
theorem pairInsertList_injOn_orderedPairs :
    Set.InjOn (fun w : List (ℕ × ℕ) => pairInsertList w) {w | OrderedPairs w} := by
  intro w hw v hv heq
  change pairInsertList w = pairInsertList v at heq
  let rows := pairInsertList w
  have hrows : rows.IsTableauRows := hw.isTableauRows
  let μ := List.tableauShape rows hrows
  have hshape : rows.map List.length = μ.rowLens := (List.rowLens_tableauShape rows hrows).symm
  obtain ⟨S,hS,hSw,hSFibers⟩ := hw.exists_standardization hshape
  obtain ⟨U,hU,hUv,hUFibers⟩ := hv.exists_standardization (by rw [←heq]; exact hshape)
  let T := weakFillingOfRows hrows hshape
  have hTrows : T.rows = rows := weakFillingOfRows_rows hrows hshape
  have hSw' : (tableauNatRows S).map (List.map (collapse w)) = T.rows :=
    hSw.trans hTrows.symm
  have hUv' : (tableauNatRows U).map (List.map (collapse v)) = T.rows :=
    hUv.trans (heq.symm.trans hTrows.symm)
  have hSstd : S = T.standard :=
    T.standard_unique_of_rows S (collapse_monotone w) hSw' hSFibers
  have hUstd : U = T.standard :=
    T.standard_unique_of_rows U (collapse_monotone v) hUv' hUFibers
  have hSU : S = U := hSstd.trans hUstd.symm
  have hinflate : inflate w = inflate v :=
    pairInsertList_injOn_matching hw.matching_inflate hv.matching_inflate
      (hS.trans ((congrArg tableauNatRows hSU).trans hU.symm))
  have hcell (c : ↥μ.cells) : collapse w (S c).val = collapse v (S c).val := by
    have h₁ := T.entry_of_rows_eq S (collapse w) hSw' c
    have h₂ := T.entry_of_rows_eq U (collapse v) hUv' c
    rw [←hSU] at h₂
    exact h₁.symm.trans h₂
  have hvalues (x : ℕ) (hx : x ∈ endpointWord (inflate w)) : collapse w x = collapse v x := by
    have hxt : x ∈ (tableauNatRows S).flatten := by
      rw [←hS]
      apply (flatten_pairInsertList_perm (inflate w) []).mem_iff.mpr
      simpa only [List.flatten_nil,List.append_nil] using hx
    have hxN := (mem_flatten_tableauNatRows_iff S x).mp hxt
    obtain ⟨c,hc⟩ := S.surjective ⟨x,hxN⟩
    simpa only [hc] using hcell c
  calc
    w = (inflate w).map (fun p => (collapse w p.1,collapse w p.2)) :=
      (collapse_inflate w).symm
    _ = (inflate w).map (fun p => (collapse v p.1,collapse v p.2)) := by
      apply List.map_congr_left
      intro p hp
      rw [hvalues p.1 (mem_endpointWord.mpr ⟨p,hp,Or.inl rfl⟩),
        hvalues p.2 (mem_endpointWord.mpr ⟨p,hp,Or.inr rfl⟩)]
    _ = v := by rw [hinflate,collapse_inflate]

theorem natMonomialPairs_injective {n : ℕ} :
    Function.Injective (natMonomialPairs (n := n)) := by
  intro m m' heq
  have hf : Function.Injective (fun e : MatchingEntry n => (e.val.2.val,e.val.1.val)) := by
    intro e f h
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.snd h)) (Fin.ext (congrArg Prod.fst h))
  have hlist : m.toMultiset.sort (· ≤ ·) = m'.toMultiset.sort (· ≤ ·) :=
    hf.list_map (by
      simpa only [natMonomialPairs,monomialPairs,List.map_map,Function.comp_def] using heq)
  have hm := congrArg (fun l : List (MatchingEntry n) => (↑l : Multiset (MatchingEntry n))) hlist
  simp only [Multiset.sort_eq] at hm
  have hh := congrArg Multiset.toFinsupp hm
  simpa only [Finsupp.toMultiset_toFinsupp] using hh

theorem pairInsertList_natMonomialPairs {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    pairInsertList (natMonomialPairs m) =
      (pairedTableau m).map (List.map (fun x : Fin n => x.val)) := by
  have hf : StrictMono (fun x : Fin n => x.val) := fun _ _ h => h
  simpa only [natMonomialPairs,pairedTableau,List.map_nil] using
    pairInsertList_map_strictMono (fun x : Fin n => x.val) hf (monomialPairs m) []

/-- Injectivity in Theorem 2.1 for the precise finite-alphabet monomial map. -/
theorem pairedTableau_injective {n : ℕ} : Function.Injective (pairedTableau (n := n)) := by
  intro m m' h
  apply natMonomialPairs_injective
  apply pairInsertList_injOn_orderedPairs (natMonomialPairs_ordered m) (natMonomialPairs_ordered m')
  change pairInsertList (natMonomialPairs m) = pairInsertList (natMonomialPairs m')
  rw [pairInsertList_natMonomialPairs,pairInsertList_natMonomialPairs,h]

/-- The complete monomial/even-row semistandard-tableau bijection of Theorem
2.1. The source is the original independent symmetric exponent space and the
forward map is the paper's paired insertion, not a chosen equivalent encoding. -/
noncomputable def pairedTableauEquiv (n : ℕ) :
    (MatchingEntry n →₀ ℕ) ≃
      {rows : List (List (Fin n)) // rows.IsTableauRows ∧ EvenRows rows} :=
  Equiv.ofBijective
    (fun m => ⟨pairedTableau m,pairedTableau_isTableauRows m,pairedTableau_evenRows m⟩)
    ⟨by
      intro m m' h
      exact pairedTableau_injective (congrArg Subtype.val h),
      by
      intro rows
      obtain ⟨m,hm⟩ := exists_monomial_of_evenTableau rows.property.1 rows.property.2
      exact ⟨m,Subtype.ext hm⟩⟩

@[simp] theorem pairedTableauEquiv_apply (n : ℕ) (m : MatchingEntry n →₀ ℕ) :
    (pairedTableauEquiv n m).val = pairedTableau m := rfl

end FourPapers.Symmetric
end
/- End source SemistandardBijection.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN CarrierMonomialSerialization\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN CarrierMonomialSerialization"

/- Begin source CarrierMonomialSerialization.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric

/-- The original independent coordinates other than the pivot. This is the
same coordinate map as `Pivot.pivotEntry (some v)` in the algebra modules. -/
def matchingPivotNonzero {n : ℕ} : Fin n ⊕ MatchingEntry n → MatchingEntry (n+1)
  | .inl i =>
      ⟨toLex (i.succ,0),show (0 : Fin (n+1)) ≤ i.succ from Fin.zero_le _⟩
  | .inr e =>
      ⟨toLex (e.val.1.succ,e.val.2.succ),
        show e.val.2.succ ≤ e.val.1.succ from Fin.succ_le_succ_iff.mpr e.property⟩

theorem matchingPivotNonzero_injective {n : ℕ} :
    Function.Injective (matchingPivotNonzero (n := n)) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have h := congrArg (fun e : MatchingEntry (n+1) => e.val.1) hab
      change i.succ = j.succ at h
      exact congrArg Sum.inl (Fin.succ_injective n h)
    | inr e =>
      have h := congrArg (fun e : MatchingEntry (n+1) => e.val.2) hab
      change (0 : Fin (n+1)) = e.val.2.succ at h
      exact (Fin.succ_ne_zero e.val.2 h.symm).elim
  | inr e =>
    cases b with
    | inl j =>
      have h := congrArg (fun e : MatchingEntry (n+1) => e.val.2) hab
      change e.val.2.succ = (0 : Fin (n+1)) at h
      exact (Fin.succ_ne_zero e.val.2 h).elim
    | inr f =>
      have h₁ := congrArg (fun e : MatchingEntry (n+1) => e.val.1) hab
      have h₂ := congrArg (fun e : MatchingEntry (n+1) => e.val.2) hab
      change e.val.1.succ = f.val.1.succ at h₁
      change e.val.2.succ = f.val.2.succ at h₂
      exact congrArg Sum.inr (Subtype.ext
        (Prod.ext (Fin.succ_injective n h₁) (Fin.succ_injective n h₂)))

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL CarrierMonomialSerialization.lift_exponent\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL CarrierMonomialSerialization.lift_exponent"

noncomputable def matchingLiftPivotExponent {n : ℕ} (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    MatchingEntry (n+1) →₀ ℕ := m.mapDomain matchingPivotNonzero

@[simp] theorem matchingLiftPivotExponent_apply {n : ℕ}
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) (v : Fin n ⊕ MatchingEntry n) :
    matchingLiftPivotExponent m (matchingPivotNonzero v) = m v :=
  Finsupp.mapDomain_apply_of_injective matchingPivotNonzero_injective m v

def carrierStateOfMonomial {n : ℕ} (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    ExactCarrierState n := (fun i => m (.inl i),fun e => m (.inr e))

def carrierInputCoordinates {n : ℕ} (q : ℕ) : List (Fin n ⊕ MatchingEntry n) :=
  ((List.finRange n).take q).flatMap fun j =>
    Sum.inl j :: (carrierFullStage j).map Sum.inr

theorem carrierInputCoordinates_upper {n : ℕ} (j : Fin n)
    (v : Fin n ⊕ MatchingEntry n)
    (hv : v ∈ Sum.inl j :: (carrierFullStage j).map Sum.inr) :
    (matchingPivotNonzero v).val.1 = j.succ := by
  rcases List.mem_cons.mp hv with rfl | hv
  · rfl
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
    change e.val.1.succ = j.succ
    exact congrArg Fin.succ ((mem_carrierFullStage j e).mp he)

theorem carrierInputCoordinates_mem {n : ℕ} (q : ℕ)
    (v : Fin n ⊕ MatchingEntry n) :
    v ∈ carrierInputCoordinates q ↔
      match v with | .inl i => i.val < q | .inr e => e.val.1.val < q := by
  unfold carrierInputCoordinates
  cases v with
  | inl i =>
    simp only [List.mem_flatMap,List.mem_cons,List.mem_map,Sum.inl.injEq,
      Sum.inr_ne_inl,Sum.inl_ne_inr,false_and,and_false,exists_false,or_false,exists_eq_right]
    have hm := mem_carrierEntriesBefore (carrierDiagonalEntry i) (q := q)
    simpa only [carrierEntriesBefore,List.mem_flatMap,mem_carrierFullStage,
      carrierDiagonalEntry,exists_eq_right] using hm
  | inr e =>
    simp only [List.mem_flatMap,List.mem_cons,List.mem_map,Sum.inl_ne_inr,Sum.inr_ne_inl,
      Sum.inr.injEq,false_or,exists_eq_right,mem_carrierFullStage,exists_eq_right]
    have hm := mem_carrierEntriesBefore e (q := q)
    simpa only [carrierEntriesBefore,List.mem_flatMap,mem_carrierFullStage,
      exists_eq_right] using hm

theorem matchingPivotNonzero_inr_strictMono {n : ℕ} :
    StrictMono (fun e : MatchingEntry n => matchingPivotNonzero (Sum.inr e)) := by
  intro e f hef
  change e.val < f.val at hef
  change toLex (e.val.1.succ,e.val.2.succ) < toLex (f.val.1.succ,f.val.2.succ)
  rcases Prod.Lex.lt_iff.mp hef with h | ⟨h,h'⟩
  · exact Prod.Lex.lt_iff.mpr (Or.inl (Fin.succ_lt_succ_iff.mpr h))
  · exact Prod.Lex.lt_iff.mpr (Or.inr ⟨congrArg Fin.succ h,
      Fin.succ_lt_succ_iff.mpr h'⟩)

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL CarrierMonomialSerialization.sorted_coordinates\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL CarrierMonomialSerialization.sorted_coordinates"

theorem carrierInputCoordinates_sorted {n : ℕ} (q : ℕ) :
    ((carrierInputCoordinates (n := n) q).map matchingPivotNonzero).SortedLT := by
  apply List.Pairwise.sortedLT
  rw [carrierInputCoordinates,List.map_flatMap]
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro j hj
    rw [List.map_cons,List.pairwise_cons]
    constructor
    · intro e he
      simp only [List.mem_map] at he
      obtain ⟨v,⟨f,hf,rfl⟩,rfl⟩ := he
      have hjf := (mem_carrierFullStage j f).mp hf
      apply Prod.Lex.lt_iff.mpr
      exact Or.inr ⟨congrArg Fin.succ hjf.symm,by simp [matchingPivotNonzero]⟩
    · rw [List.map_map,List.pairwise_map]
      apply (carrierFullStage_sorted j).pairwise.imp
      intro a b hab
      exact matchingPivotNonzero_inr_strictMono hab
  · apply ((List.sortedLT_finRange n).pairwise.take (i := q)).imp
    intro j k hjk e he f hf
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hf
    apply Prod.Lex.lt_iff.mpr
    apply Or.inl
    change (matchingPivotNonzero v).val.1 < (matchingPivotNonzero w).val.1
    rw [carrierInputCoordinates_upper j v hv,carrierInputCoordinates_upper k w hw]
    exact Fin.succ_lt_succ_iff.mpr hjk

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL CarrierMonomialSerialization.coordinate_expansion\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL CarrierMonomialSerialization.coordinate_expansion"

theorem carrierInputPrefix_eq_coordinateExpansion {n : ℕ} (q : ℕ)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    carrierInputPrefix q (carrierStateOfMonomial m) =
      (carrierInputCoordinates q).flatMap (fun v =>
        List.replicate (m v)
          ((matchingPivotNonzero v).val.2.val,(matchingPivotNonzero v).val.1.val)) := by
  unfold carrierInputPrefix carrierInputCoordinates
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro j hj
  simp only [carrierInputStage,carrierStateOfMonomial,List.flatMap_cons,List.flatMap_map,
    matchingPivotNonzero,Fin.val_succ,Fin.val_zero]
  rw [carrierFullStage,List.flatMap_append,List.flatMap_singleton]
  simp only [carrierDiagonalEntry]
  rw [List.append_assoc]
  congr 1
  congr 1
  unfold carrierPairsOfEntries
  apply List.flatMap_congr
  intro e he
  rewrite [((mem_carrierOffEntries j e).mp he).1]
  rfl

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL CarrierMonomialSerialization.full_serialization\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL CarrierMonomialSerialization.full_serialization"

/-- Serialization of the original input monomial, with precisely zero exponent
at the pivot coordinate and arbitrary exponents at all remaining coordinates. -/
theorem carrierInputPrefix_full_eq_natMonomialPairs {n : ℕ}
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    carrierInputPrefix n (carrierStateOfMonomial m) =
      natMonomialPairs (matchingLiftPivotExponent m) := by
  let es := (carrierInputCoordinates (n := n) n).map matchingPivotNonzero
  have hs := carrierInputCoordinates_sorted (n := n) n
  have hcover : ∀ e ∈ (matchingLiftPivotExponent m).support, e ∈ es := by
    intro e he
    obtain ⟨v,rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero
      (Finsupp.mem_support_iff.mp he)
    apply List.mem_map.mpr
    refine ⟨v,?_,rfl⟩
    apply (carrierInputCoordinates_mem n v).mpr
    cases v with
    | inl i => exact i.isLt
    | inr e => exact e.val.1.isLt
  have hsort := sort_toMultiset_eq_expand (matchingLiftPivotExponent m) es
    hs.sortedLE.pairwise hs.nodup hcover
  rw [carrierInputPrefix_eq_coordinateExpansion]
  simp only [natMonomialPairs,monomialPairs,hsort,expandCoordinates,es,
    List.flatMap_map,List.map_flatMap,List.map_replicate,List.map_map,
    Function.comp_def,matchingLiftPivotExponent_apply]

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL CarrierMonomialSerialization.prefix_filter\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL CarrierMonomialSerialization.prefix_filter"

theorem carrierInputPrefix_eq_filter {n : ℕ} (q : ℕ) (s : ExactCarrierState n) :
    carrierInputPrefix q s = (carrierInputPrefix n s).filter (fun p => p.2 ≤ q) := by
  have he : (List.finRange n).take q =
      (List.finRange n).filter (fun j => j.val < q) := by
    apply ((List.sortedLT_finRange n).pairwise.take (i := q)).sortedLT.eq_of_mem_iff
      ((List.Pairwise.filter _ (List.sortedLT_finRange n).pairwise).sortedLT)
    intro j
    have hm := carrierInputCoordinates_mem (n := n) q (Sum.inl j)
    have ht : j ∈ (List.finRange n).take q ↔ j.val < q := by
      simpa only [carrierInputCoordinates,List.mem_flatMap,List.mem_cons,List.mem_map,
        Sum.inl.injEq,Sum.inr_ne_inl,Sum.inl_ne_inr,false_and,and_false,
        exists_false,or_false,exists_eq_right,exists_eq_right'] using hm
    simp only [ht,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  have hf (js : List (Fin n)) :
      (js.filter (fun j => j.val < q)).flatMap
          (fun j => carrierInputStage j (carrierOffEntries j) s) =
        (js.flatMap (fun j => carrierInputStage j (carrierOffEntries j) s)).filter
          (fun p => p.2 ≤ q) := by
    induction js with
    | nil => rfl
    | cons j js ih =>
      have hstage : (carrierInputStage j (carrierOffEntries j) s).filter
          (fun p => p.2 ≤ q) =
          if j.val < q then carrierInputStage j (carrierOffEntries j) s else [] := by
        unfold carrierInputStage carrierPairsOfEntries
        simp only [List.filter_append,List.filter_flatMap,List.filter_replicate,
          Nat.succ_le_iff]
        by_cases hj : j.val < q <;> simp [hj]
      by_cases hj : j.val < q <;>
        simp [List.filter_cons,hj,hstage,ih,List.filter_append]
  have hfull : (List.finRange n).take n = List.finRange n := by
    simpa only [List.length_finRange] using (List.take_length (l := List.finRange n))
  simp only [carrierInputPrefix,hfull]
  rw [he]
  exact hf _

theorem carrierInputPrefix_eq_natMonomialPairs_filter {n : ℕ} (q : ℕ)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    carrierInputPrefix q (carrierStateOfMonomial m) =
      (natMonomialPairs (matchingLiftPivotExponent m)).filter (fun p => p.2 ≤ q) := by
  rw [carrierInputPrefix_eq_filter,carrierInputPrefix_full_eq_natMonomialPairs]

theorem carrierResidualPrefix_eq_natMonomialPairs_filter {n : ℕ} (q : ℕ)
    (s : ExactCarrierState n) :
    carrierResidualPrefix q s =
      ((natMonomialPairs (Finsupp.equivFunOnFinite.symm s.2)).filter
        (fun p => p.2 < q)).map (fun p => (p.1+1,p.2+1)) := by
  rw [carrierResidualPrefix_eq_filter,carrierResidualPrefix_full_eq_monomialPairs,
    List.filter_map]
  simp only [natMonomialPairs,List.map_map,List.filter_map,Function.comp_def,
    Nat.succ_le_iff]

theorem monomialCarrierEquiv_snd_eq {n : ℕ}
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    (monomialCarrierEquiv n m).2 =
      Finsupp.equivFunOnFinite.symm (exactCarrierEquiv n (carrierStateOfMonomial m)).2 := rfl

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL CarrierMonomialSerialization.tableau_tail\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL CarrierMonomialSerialization.tableau_tail"

/-- The exact monomial carrier equivalence deletes the first tableau row.
Both sides use the original sorted monomial serialization; the successor map
merely restores the labels of the residual matrix inside the original matrix. -/
theorem monomialCarrierEquiv_tableau_tail {n : ℕ}
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    (pairInsertList (natMonomialPairs (matchingLiftPivotExponent m))).tail =
      (pairInsertList (natMonomialPairs (monomialCarrierEquiv n m).2)).map
        (List.map Nat.succ) := by
  rw [←carrierInputPrefix_full_eq_natMonomialPairs,pairInsertList_exactCarrierEquiv_tail,
    carrierResidualPrefix_full_eq_monomialPairs,monomialCarrierEquiv_snd_eq]
  have hf : StrictMono Nat.succ := fun a b hab => Nat.succ_lt_succ hab
  simpa only [natMonomialPairs,List.map_map,Function.comp_def,Nat.succ_eq_add_one,
    List.map_nil] using
    pairInsertList_map_strictMono Nat.succ hf
      (natMonomialPairs (Finsupp.equivFunOnFinite.symm
        (exactCarrierEquiv n (carrierStateOfMonomial m)).2)) []

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_DECL CarrierMonomialSerialization.tableau_prefix_tail\n") (fun _ => pure ())
  logInfo "CANONICAL_DECL CarrierMonomialSerialization.tableau_prefix_tail"

/-- The row-deletion identity holds at every endpoint prefix, using the final
residual monomial supplied by the bijection. -/
theorem monomialCarrierEquiv_tableau_prefix_tail {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    (pairInsertList ((natMonomialPairs (matchingLiftPivotExponent m)).filter
      (fun p => p.2 ≤ q))).tail =
      (pairInsertList ((natMonomialPairs (monomialCarrierEquiv n m).2).filter
        (fun p => p.2 < q))).map (List.map Nat.succ) := by
  rw [←carrierInputPrefix_eq_natMonomialPairs_filter,
    pairInsertList_exactCarrierEquiv_prefix_tail q hq,
    carrierResidualPrefix_eq_natMonomialPairs_filter,monomialCarrierEquiv_snd_eq]
  have hf : StrictMono Nat.succ := fun a b hab => Nat.succ_lt_succ hab
  simpa only [Nat.succ_eq_add_one,List.map_nil] using
    pairInsertList_map_strictMono Nat.succ hf
      ((natMonomialPairs (Finsupp.equivFunOnFinite.symm
        (exactCarrierEquiv n (carrierStateOfMonomial m)).2)).filter (fun p => p.2 < q)) []

end FourPapers.Symmetric
end
/- End source CarrierMonomialSerialization.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN CarrierTableauRecurrence\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN CarrierTableauRecurrence"

/- Begin source CarrierTableauRecurrence.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FourPapers.Symmetric

theorem row_has_prefix_of_isRowAbove {upper lower : List ℕ}
    (h : upper.IsRowAbove lower) (q : ℕ)
    (hlower : (lower.filter (fun x => x < q)) ≠ []) :
    (upper.filter (fun x => x < q)) ≠ [] := by
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hlower
  obtain ⟨hx,hxq⟩ := List.mem_filter.mp hx
  have hxq' : x < q := by simpa only [decide_eq_true_eq] using hxq
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem hx
  have hju : j < upper.length := hj.trans_le h.length_le
  have huq : upper[j] < q := (h.getElem_lt j hju hj).trans (he.symm ▸ hxq')
  intro hnil
  have hm : upper[j] ∈ upper.filter (fun x => x < q) :=
    List.mem_filter.mpr ⟨List.getElem_mem hju,by simpa only [decide_eq_true_eq] using huq⟩
  rw [hnil] at hm
  exact List.not_mem_nil hm

/-- Removing the first row of a semistandard tableau reduces every prefix
height by one, with natural subtraction handling an empty prefix. -/
theorem rowsPrefixHeight_tail {rows : List (List ℕ)} (hrows : rows.IsTableauRows)
    (q : ℕ) : rowsPrefixHeight rows.tail q = rowsPrefixHeight rows q - 1 := by
  cases rows with
  | nil => simp [rowsPrefixHeight]
  | cons row rows =>
    change (rows.filter (fun r => (r.filter (fun x => x < q)) ≠ [])).length =
      ((row::rows).filter (fun r => (r.filter (fun x => x < q)) ≠ [])).length - 1
    by_cases hrow : (row.filter (fun x => x < q)) ≠ []
    · rw [List.filter_cons_of_pos
        (p := fun r : List ℕ => decide ((r.filter (fun x => x < q)) ≠ []))
        (by simpa only [decide_eq_true_eq] using hrow),List.length_cons]
      omega
    · have htail : rows.filter (fun r => (r.filter (fun x => x < q)) ≠ []) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro r hr hsmall
        have hsmall' : (r.filter (fun x => x < q)) ≠ [] := by
          simpa only [decide_eq_true_eq] using hsmall
        have habove : row.IsRowAbove r := (List.pairwise_cons.mp hrows.isChain.pairwise).1 r hr
        exact hrow (row_has_prefix_of_isRowAbove habove q hsmall')
      rw [List.filter_cons_of_neg
        (p := fun r : List ℕ => decide ((r.filter (fun x => x < q)) ≠ []))
        (by simpa only [decide_eq_true_eq] using hrow),htail]
      rfl

theorem rowsPrefixHeight_map_succ (rows : List (List ℕ)) (q : ℕ) :
    rowsPrefixHeight (rows.map (List.map Nat.succ)) (q+1) = rowsPrefixHeight rows q := by
  have hn (l : List ℕ) : l.map Nat.succ ≠ [] ↔ l ≠ [] :=
    not_congr (List.map_eq_nil_iff (f := Nat.succ) (l := l))
  simp only [rowsPrefixHeight,List.filter_map,List.length_map,Function.comp_def,
    Nat.succ_lt_succ_iff,hn]

/-- The exact row-count recurrence required by the northwest rank bounds,
at every endpoint stage of the original monomial carrier bijection. -/
theorem monomialCarrierEquiv_prefix_height {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) (i : ℕ) :
    rowsPrefixHeight
      (pairInsertList ((natMonomialPairs (monomialCarrierEquiv n m).2).filter
        (fun p => p.2 < q))) i =
      rowsPrefixHeight
        (pairInsertList ((natMonomialPairs (matchingLiftPivotExponent m)).filter
          (fun p => p.2 ≤ q))) (i+1) - 1 := by
  have ht := ((natMonomialPairs_ordered (matchingLiftPivotExponent m)).filter
    (fun p => p.2 ≤ q)).isTableauRows
  rw [←rowsPrefixHeight_tail ht,
    monomialCarrierEquiv_tableau_prefix_tail q hq,rowsPrefixHeight_map_succ]

theorem monomialCarrierEquiv_height {n : ℕ}
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) (i : ℕ) :
    rowsPrefixHeight (pairInsertList (natMonomialPairs (monomialCarrierEquiv n m).2)) i =
      rowsPrefixHeight (pairInsertList (natMonomialPairs (matchingLiftPivotExponent m)))
        (i+1) - 1 := by
  have ht := (natMonomialPairs_ordered (matchingLiftPivotExponent m)).isTableauRows
  rw [←rowsPrefixHeight_tail ht,monomialCarrierEquiv_tableau_tail,
    rowsPrefixHeight_map_succ]

/-- Row lengths, and hence half-row lengths, shift exactly by one under the
actual carrier bijection. No shape statistic is substituted for the algorithm. -/
theorem monomialCarrierEquiv_halfShape_tail {n : ℕ}
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    ((pairInsertList (natMonomialPairs (matchingLiftPivotExponent m))).map
      (fun row => row.length / 2)).tail =
      (pairInsertList (natMonomialPairs (monomialCarrierEquiv n m).2)).map
        (fun row => row.length / 2) := by
  rw [←List.map_tail,monomialCarrierEquiv_tableau_tail,List.map_map]
  simp only [Function.comp_def,List.length_map]

theorem monomialCarrierEquiv_halfShape_prefix_tail {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    ((pairInsertList ((natMonomialPairs (matchingLiftPivotExponent m)).filter
      (fun p => p.2 ≤ q))).map (fun row => row.length / 2)).tail =
      (pairInsertList ((natMonomialPairs (monomialCarrierEquiv n m).2).filter
        (fun p => p.2 < q))).map (fun row => row.length / 2) := by
  rw [←List.map_tail,monomialCarrierEquiv_tableau_prefix_tail q hq,List.map_map]
  simp only [Function.comp_def,List.length_map]

end FourPapers.Symmetric
end
/- End source CarrierTableauRecurrence.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN OccurrenceSelection\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN OccurrenceSelection"

/- Begin source OccurrenceSelection.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Selecting distinct occurrences from exponent inequalities

The index types remember occurrences, not merely their labels.  Consequently
the injection below cannot use one occurrence twice, including when two
different requested factors have the same label.
-/

namespace FourPapers.Symmetric

variable {α ι κ : Type*} [DecidableEq α] [Fintype ι] [Fintype κ]

noncomputable def occurrenceExponent (f : ι → α) : α →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

theorem occurrenceExponent_apply (f : ι → α) (a : α) :
    occurrenceExponent f a = Fintype.card {i // f i = a} := by
  classical
  simp only [occurrenceExponent, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Fintype.card_subtype, Finset.card_filter]

/-- Fiberwise cardinal inequalities can be realized by one global injection
which preserves every label. -/
theorem exists_embedding_of_fiber_card_le (f : ι → α) (g : κ → α)
    (h : ∀ a, Fintype.card {i // f i = a} ≤ Fintype.card {j // g j = a}) :
    ∃ e : ι ↪ κ, ∀ i, g (e i) = f i := by
  classical
  let E : ∀ a, {i // f i = a} ↪ {j // g j = a} :=
    fun a => Classical.choice (Function.Embedding.nonempty_of_card_le (h a))
  let e : ι → κ := fun i => (E (f i) ⟨i,rfl⟩).val
  have he (i : ι) : g (e i) = f i := (E (f i) ⟨i,rfl⟩).property
  have hinj : Function.Injective e := by
    intro i j hij
    have hlabel : f i = f j := (he i).symm.trans ((congrArg g hij).trans (he j))
    have hcast (a : α) (ha : f j = a) : (E a ⟨j,ha⟩).val = e j := by
      subst a
      rfl
    have hE : E (f i) ⟨i,rfl⟩ = E (f i) ⟨j,hlabel.symm⟩ := by
      apply Subtype.ext
      exact hij.trans (hcast (f i) hlabel.symm).symm
    exact congrArg Subtype.val ((E (f i)).injective hE)
  exact ⟨⟨e,hinj⟩,he⟩

/-- A monomial-divisibility inequality is exactly the possibility of choosing
distinct occurrences of all the requested factors. -/
theorem occurrenceExponent_le_iff (f : ι → α) (g : κ → α) :
    occurrenceExponent f ≤ occurrenceExponent g ↔
      ∃ e : ι ↪ κ, ∀ i, g (e i) = f i := by
  classical
  constructor
  · intro h
    apply exists_embedding_of_fiber_card_le f g
    intro a
    simpa only [← occurrenceExponent_apply] using h a
  · rintro ⟨e,he⟩ a
    rw [occurrenceExponent_apply, occurrenceExponent_apply]
    let ef : {i // f i = a} ↪ {j // g j = a} :=
      ⟨fun i => ⟨e i.val, (he i.val).trans i.property⟩,
        fun i j hij => Subtype.ext (e.injective (congrArg Subtype.val hij))⟩
    exact Fintype.card_le_of_embedding ef

theorem occurrenceExponent_comp_embedding_le (g : κ → α) (e : ι ↪ κ) :
    occurrenceExponent (g ∘ e) ≤ occurrenceExponent g :=
  (occurrenceExponent_le_iff _ _).mpr ⟨e,fun _ => rfl⟩

theorem mapDomain_occurrenceExponent {β : Type*} (f : ι → α) (g : α → β) :
    (occurrenceExponent f).mapDomain g = occurrenceExponent (g ∘ f) := by
  classical
  simp only [occurrenceExponent, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single, Function.comp_apply]

theorem toFinsupp_map {β : Type*} [DecidableEq β] (l : Multiset α) (f : α → β) :
    (l.map f).toFinsupp = l.toFinsupp.mapDomain f := by
  rw [← Finsupp.toMultiset_toFinsupp (l.toFinsupp.mapDomain f),
    ← Finsupp.toMultiset_map, Multiset.toFinsupp_toMultiset]

theorem occurrenceExponent_list (l : List α) :
    occurrenceExponent l.get = (l : Multiset α).toFinsupp := by
  classical
  induction l with
  | nil => simp [occurrenceExponent]
  | cons a l ih =>
    have hcons : ((a :: l : List α) : Multiset α) = {a} + (l : Multiset α) := rfl
    simp only [occurrenceExponent, List.length_cons, Fin.sum_univ_succ,
      List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
      List.getElem_cons_zero, List.getElem_cons_succ, hcons,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    simpa only [occurrenceExponent, List.get_eq_getElem] using
      congrArg (fun z => Finsupp.single a 1 + z) ih

theorem occurrenceExponent_list_comp {β : Type*} [DecidableEq β]
    (l : List α) (g : α → β) :
    occurrenceExponent (g ∘ l.get) = ((l.map g : List β) : Multiset β).toFinsupp := by
  rw [← mapDomain_occurrenceExponent, occurrenceExponent_list]
  simpa only [Multiset.map_coe] using (toFinsupp_map (l : Multiset α) g).symm

end FourPapers.Symmetric
end
/- End source OccurrenceSelection.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN FoldedOccurrences\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN FoldedOccurrences"

/- Begin source FoldedOccurrences.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Folded divisibility and occurrence chains

This module relates the literal product of symmetric coordinates to the
occurrence-sensitive chains used by matching insertion.  It includes loops
and arbitrary multiplicities.
-/

namespace FourPapers.Symmetric.Inflation

def natFold (a b : ℕ) : ℕ × ℕ := (max a b, min a b)

theorem natFold_comm (a b : ℕ) : natFold a b = natFold b a := by
  simp only [natFold, max_comm, min_comm]

theorem natFold_eq_iff (a b c d : ℕ) :
    natFold a b = natFold c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have hmax := congrArg Prod.fst h
    have hmin := congrArg Prod.snd h
    change max a b = max c d at hmax
    change min a b = min c d at hmin
    omega
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact natFold_comm _ _

noncomputable def wordExponent (w : List (ℕ × ℕ)) : (ℕ × ℕ) →₀ ℕ :=
  occurrenceExponent (fun i : Fin w.length => natFold w[i].1 w[i].2)

theorem natFold_vertex_partner {w : List (ℕ × ℕ)} (o : Incidence w) :
    natFold (vertex o) (vertex (partner o)) = natFold w[o.edge].1 w[o.edge].2 := by
  cases h : o.upper <;> simp only [vertex, partner, h, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, if_false, if_true]
  exact natFold_comm _ _

theorem exists_incidence_of_fold_eq {w : List (ℕ × ℕ)} (i : Fin w.length)
    (a b : ℕ) (h : natFold a b = natFold w[i].1 w[i].2) :
    ∃ o : Incidence w, o.edge = i ∧ vertex o = a ∧ vertex (partner o) = b := by
  rcases (natFold_eq_iff _ _ _ _).mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact ⟨⟨i,false⟩,rfl,ha.symm,hb.symm⟩
  · exact ⟨⟨i,true⟩,rfl,ha.symm,hb.symm⟩

/-- The requested ordered pairs can be realized by distinct original edge
occurrences precisely when their folded product divides the original word. -/
theorem occurrenceExponent_fold_le_iff {ι : Type*} [Fintype ι]
    (w : List (ℕ × ℕ)) (a b : ι → ℕ) :
    occurrenceExponent (fun i => natFold (a i) (b i)) ≤ wordExponent w ↔
      ∃ e : ι → Incidence w, Function.Injective (fun i => (e i).edge) ∧
        (∀ i, vertex (e i) = a i) ∧ (∀ i, vertex (partner (e i)) = b i) := by
  classical
  constructor
  · intro h
    obtain ⟨j,hj⟩ := (occurrenceExponent_le_iff _ _).mp h
    choose e he hva hvb using fun i => exists_incidence_of_fold_eq (j i) (a i) (b i) (hj i).symm
    refine ⟨e,?_,hva,hvb⟩
    intro i k hik
    apply j.injective
    simpa only [he] using hik
  · rintro ⟨e,hinj,ha,hb⟩
    apply (occurrenceExponent_le_iff _ _).mpr
    refine ⟨⟨fun i => (e i).edge,hinj⟩,?_⟩
    intro i
    change natFold w[(e i).edge].1 w[(e i).edge].2 = natFold (a i) (b i)
    simpa only [ha,hb] using (natFold_vertex_partner (e i)).symm

theorem chain_of_parametrization {w : List (ℕ × ℕ)} {t : ℕ}
    (e : Fin t → Incidence w)
    (hinj : Function.Injective (fun p => (e p).edge))
    (ha : StrictMono (fun p => vertex (e p)))
    (hb : StrictAnti (fun p => vertex (partner (e p)))) :
    IsOccurrenceChain (Finset.univ.image e) := by
  classical
  constructor
  · intro x hx y hy hxy
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
    have hpq : p < q := by
      by_contra hnot
      rcases lt_or_eq_of_le (le_of_not_gt hnot) with hqp | hqp
      · have hv := ha hqp
        have hl := (label_lt_iff (e q) (e p)).mpr (Or.inl hv)
        have hl' := label_strictMono hxy
        exact (not_lt_of_ge hl.le) hl'
      · subst q
        exact lt_irrefl _ hxy
    exact ha hpq
  · intro x hx y hy hxy
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
    have hpq : p < q := by
      by_contra hnot
      rcases lt_or_eq_of_le (le_of_not_gt hnot) with hqp | hqp
      · have hv := ha hqp
        have hl := (label_lt_iff (e q) (e p)).mpr (Or.inl hv)
        have hl' := label_strictMono hxy
        exact (not_lt_of_ge hl.le) hl'
      · subst q
        exact lt_irrefl _ hxy
    exact hb hpq
  · intro x hx hbad
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,_,he⟩ := Finset.mem_image.mp hbad
    have hedge := congrArg (fun z : Incidence w => z.edge) he
    change (e q).edge = (e p).edge at hedge
    have hpq : q = p := hinj hedge
    subst q
    have he' := congrArg Incidence.upper he
    change (e p).upper = !(e p).upper at he'
    cases hu : (e p).upper <;> simp [hu] at he'

/-- Exact rectangular antidiagonal existence in occurrence form. Both sides
use arbitrary, strictly increasing rows and strictly decreasing columns. -/
theorem exists_antidiagonal_iff_occurrence_chain (w : List (ℕ × ℕ)) (i j t : ℕ) :
    (∃ a b : Fin t → ℕ, StrictMono a ∧ StrictAnti b ∧
      (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧
      occurrenceExponent (fun p => natFold (a p) (b p)) ≤ wordExponent w) ↔
    ∃ C : Finset (Incidence w), IsOccurrenceChain C ∧ C.card = t ∧
      (∀ o ∈ C, vertex o ≤ i) ∧ (∀ o ∈ C, vertex (partner o) ≤ j) := by
  classical
  constructor
  · rintro ⟨a,b,ha,hb,hai,hbj,hm⟩
    obtain ⟨e,he,hea,heb⟩ := (occurrenceExponent_fold_le_iff w a b).mp hm
    have hei : Function.Injective e := fun p q hpq => he (congrArg Incidence.edge hpq)
    refine ⟨Finset.univ.image e,chain_of_parametrization e he ?_ ?_,?_,?_,?_⟩
    · simpa only [hea] using ha
    · simpa only [heb] using hb
    · simp only [Finset.card_image_of_injective _ hei, Finset.card_univ, Fintype.card_fin]
    · intro o ho
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ho
      simpa only [hea] using hai p
    · intro o ho
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ho
      simpa only [heb] using hbj p
  · rintro ⟨C,hC,hcard,hi,hj⟩
    let e : Fin t ↪o Incidence w := C.orderEmbOfFin hcard
    have hem (p : Fin t) : e p ∈ C := C.orderEmbOfFin_mem hcard p
    refine ⟨fun p => vertex (e p),fun p => vertex (partner (e p)),?_,?_,
      fun p => hi _ (hem p),fun p => hj _ (hem p),?_⟩
    · intro p q hpq
      exact hC.increasing _ (hem p) _ (hem q) (e.strictMono hpq)
    · intro p q hpq
      exact hC.decreasing _ (hem p) _ (hem q) (e.strictMono hpq)
    · apply (occurrenceExponent_fold_le_iff w _ _).mpr
      refine ⟨e,?_,fun _ => rfl,fun _ => rfl⟩
      intro p q hpq
      exact e.injective (hC.edge_injective (hem p) (hem q) hpq)

theorem mem_occurrenceEndpoints_edge {w : List (ℕ × ℕ)}
    {C : Finset (Incidence w)} {z : Incidence w} (hz : z ∈ occurrenceEndpoints C) :
    ∃ o ∈ C, o.edge = z.edge := by
  classical
  rcases Finset.mem_union.mp hz with h | h
  · exact ⟨z,h,rfl⟩
  · obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp h
    exact ⟨o,ho,rfl⟩

theorem IsOccurrencePacking.color_eq_of_edge_eq {w : List (ℕ × ℕ)} {κ : Type*}
    {P : κ → Finset (Incidence w)} (hP : IsOccurrencePacking P)
    {c d : κ} {o p : Incidence w} (ho : o ∈ P c) (hp : p ∈ P d)
    (he : o.edge = p.edge) : c = d := by
  classical
  by_contra hcd
  have hdis := Finset.disjoint_left.mp (hP.disjoint c d hcd)
  rcases same_edge_eq_or_partner he with h | h
  · exact hdis (Finset.mem_union_left _ (h ▸ ho)) (Finset.mem_union_left _ hp)
  · exact hdis
      (Finset.mem_union_right _ (h ▸ Finset.mem_image_of_mem partner ho))
      (Finset.mem_union_left _ hp)

/-- Arbitrarily many antidiagonals share a single occurrence budget. This is
the exact product-divisibility condition, with no restriction on their sizes. -/
theorem exists_packed_antidiagonals_iff_occurrence_packing
    (w : List (ℕ × ℕ)) {κ : Type*} [Fintype κ] (s : κ → ℕ) :
    (∃ a b : ∀ c, Fin (s c) → ℕ,
      (∀ c, StrictMono (a c)) ∧ (∀ c, StrictAnti (b c)) ∧
      occurrenceExponent (fun p : Σ c, Fin (s c) => natFold (a p.1 p.2) (b p.1 p.2)) ≤
        wordExponent w) ↔
    ∃ P : κ → Finset (Incidence w), IsOccurrencePacking P ∧ ∀ c, (P c).card = s c := by
  classical
  constructor
  · rintro ⟨a,b,ha,hb,hm⟩
    obtain ⟨e,he,hea,heb⟩ :=
      (occurrenceExponent_fold_le_iff w
        (fun p : Σ c, Fin (s c) => a p.1 p.2)
        (fun p : Σ c, Fin (s c) => b p.1 p.2)).mp hm
    let P : κ → Finset (Incidence w) := fun c => Finset.univ.image (fun p => e ⟨c,p⟩)
    have hei (c : κ) : Function.Injective (fun p : Fin (s c) => (e ⟨c,p⟩).edge) := by
      intro p q hpq
      have hv := congrArg (fun z : Σ d, Fin (s d) => z.2.val) (he hpq)
      exact Fin.ext hv
    have hem (c : κ) : Function.Injective (fun p : Fin (s c) => e ⟨c,p⟩) :=
      fun p q hpq => hei c (congrArg Incidence.edge hpq)
    refine ⟨P,⟨?_,?_⟩,?_⟩
    · intro c
      apply chain_of_parametrization _ (hei c)
      · simpa only [hea] using ha c
      · simpa only [heb] using hb c
    · intro c d hcd
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨o,ho,hoz⟩ := mem_occurrenceEndpoints_edge hz
      obtain ⟨p,hp,hpz⟩ := mem_occurrenceEndpoints_edge hz'
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ho
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
      exact hcd (congrArg Sigma.fst (he (hoz.trans hpz.symm)))
    · intro c
      simp only [P, Finset.card_image_of_injective _ (hem c),
        Finset.card_univ, Fintype.card_fin]
  · rintro ⟨P,hP,hsize⟩
    let E : ∀ c, Fin (s c) ↪o Incidence w := fun c => (P c).orderEmbOfFin (hsize c)
    have hE (c : κ) (p : Fin (s c)) : E c p ∈ P c :=
      (P c).orderEmbOfFin_mem (hsize c) p
    let e : (Σ c, Fin (s c)) → Incidence w := fun p => E p.1 p.2
    have hei : Function.Injective (fun p => (e p).edge) := by
      rintro ⟨c,i⟩ ⟨d,j⟩ he
      have hcd : c = d := hP.color_eq_of_edge_eq (hE c i) (hE d j) he
      subst d
      have hij : i = j := (E c).injective ((hP.chain c).edge_injective (hE c i) (hE c j) he)
      subst j
      rfl
    refine ⟨fun c p => vertex (E c p),fun c p => vertex (partner (E c p)),?_,?_,?_⟩
    · intro c p q hpq
      exact (hP.chain c).increasing _ (hE c p) _ (hE c q) ((E c).strictMono hpq)
    · intro c p q hpq
      exact (hP.chain c).decreasing _ (hE c p) _ (hE c q) ((E c).strictMono hpq)
    · exact (occurrenceExponent_fold_le_iff w _ _).mpr ⟨e,hei,fun _ => rfl,fun _ => rfl⟩

end FourPapers.Symmetric.Inflation
end
/- End source FoldedOccurrences.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MonomialFoldedWords\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MonomialFoldedWords"

/- Begin source MonomialFoldedWords.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FourPapers.Symmetric
open Inflation

/-- Forget only the ambient finite bound on an independent symmetric
coordinate; its two ordered endpoints remain unchanged. -/
def entryNat {n : ℕ} (e : MatchingEntry n) : ℕ × ℕ := (e.val.1.val,e.val.2.val)

theorem entryNat_injective {n : ℕ} : Function.Injective (entryNat (n := n)) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact Fin.ext (congrArg Prod.snd h)

/-- The same folding map as the algebraic coordinate definition, available
without importing polynomial algebra. Their equality is definitional. -/
def matchingFold {n : ℕ} (i j : Fin n) : MatchingEntry n :=
  ⟨toLex (max i j,min i j),min_le_max⟩

theorem entryNat_matchingFold {n : ℕ} (i j : Fin n) :
    entryNat (matchingFold i j) = natFold i.val j.val := by
  change ((max i j).val, (min i j).val) = (max i.val j.val, min i.val j.val)
  rw [Fin.val_max, Fin.val_min]

theorem wordExponent_eq_toFinsupp (w : List (ℕ × ℕ)) :
    wordExponent w = ((w.map (fun p => natFold p.1 p.2) : List (ℕ × ℕ)) :
      Multiset (ℕ × ℕ)).toFinsupp := by
  simpa only [wordExponent, Function.comp_def, List.get_eq_getElem, Fin.getElem_fin] using
    occurrenceExponent_list_comp w (fun p => natFold p.1 p.2)

/-- The sorted edge word contains precisely the original exponent vector.
In particular no occurrence is lost at loops or repeated coordinates. -/
theorem wordExponent_natMonomialPairs {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    wordExponent (natMonomialPairs m) = m.mapDomain entryNat := by
  classical
  rw [wordExponent_eq_toFinsupp]
  have hmap : (natMonomialPairs m).map (fun p => natFold p.1 p.2) =
      (m.toMultiset.sort (· ≤ ·)).map entryNat := by
    simp only [natMonomialPairs,monomialPairs,List.map_map,Function.comp_apply]
    apply List.map_congr_left
    intro e he
    have h : e.val.2.val ≤ e.val.1.val := e.property
    change natFold e.val.2.val e.val.1.val = (e.val.1.val, e.val.2.val)
    simp only [natFold,max_eq_right h,min_eq_left h]
  rw [hmap,← Multiset.map_coe,Multiset.sort_eq,Finsupp.toMultiset_map,
    Finsupp.toMultiset_toFinsupp]

theorem natMonomialPairs_vertex_lt {n : ℕ} (m : MatchingEntry n →₀ ℕ)
    (o : Incidence (natMonomialPairs m)) : vertex o < n := by
  have hm := vertex_mem_endpoints o
  rcases mem_endpointWord.mp hm with ⟨p,hp,he⟩
  simp only [natMonomialPairs,monomialPairs,List.map_map,List.mem_map,
    Function.comp_apply] at hp
  obtain ⟨e,he',rfl⟩ := hp
  rcases he with h | h
  · rw [h]
    exact e.val.2.isLt
  · rw [h]
    exact e.val.1.isLt

noncomputable def matchingAntidiagonalExponent {n t : ℕ}
    (a b : Fin t ↪o Fin n) : MatchingEntry n →₀ ℕ :=
  ∑ p : Fin t, Finsupp.single (matchingFold (a p) (b p.rev)) 1

theorem mapDomain_matchingAntidiagonalExponent {n t : ℕ}
    (a b : Fin t ↪o Fin n) :
    (matchingAntidiagonalExponent a b).mapDomain entryNat =
      occurrenceExponent (fun p => natFold (a p).val (b p.rev).val) := by
  simp only [matchingAntidiagonalExponent,occurrenceExponent,
    Finsupp.mapDomain_finsetSum,Finsupp.mapDomain_single,entryNat_matchingFold]

/-- Literal folded antidiagonal divisibility is equivalent to the natural
endpoint occurrence formulation, before any insertion statistic is invoked. -/
theorem matchingAntidiagonal_le_iff {n t : ℕ} (m : MatchingEntry n →₀ ℕ)
    (a b : Fin t ↪o Fin n) :
    matchingAntidiagonalExponent a b ≤ m ↔
      occurrenceExponent (fun p => natFold (a p).val (b p.rev).val) ≤
        wordExponent (natMonomialPairs m) := by
  rw [wordExponent_natMonomialPairs,← mapDomain_matchingAntidiagonalExponent,
    Finsupp.mapDomain_le_mapDomain_iff_le entryNat_injective]

/-- Exact finite-alphabet rectangular chain correspondence. This remains
valid for all monomials and for every permitted rectangle, without a degree
bound or an assumption that coordinates occur only once. -/
theorem matchingAntidiagonal_exists_iff {n t : ℕ} (m : MatchingEntry n →₀ ℕ)
    (i j : Fin n) :
    (∃ a b : Fin t ↪o Fin n, (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧
      matchingAntidiagonalExponent a b ≤ m) ↔
    ∃ C : Finset (Incidence (natMonomialPairs m)), IsOccurrenceChain C ∧ C.card = t ∧
      (∀ o ∈ C, vertex o ≤ i.val) ∧ (∀ o ∈ C, vertex (partner o) ≤ j.val) := by
  rw [← exists_antidiagonal_iff_occurrence_chain]
  constructor
  · rintro ⟨a,b,hai,hbj,hm⟩
    refine ⟨fun p => (a p).val,fun p => (b p.rev).val,?_,?_,
      fun p => hai p,fun p => hbj p.rev,(matchingAntidiagonal_le_iff m a b).mp hm⟩
    · exact fun p q hpq => a.strictMono hpq
    · exact fun p q hpq => b.strictMono (Fin.rev_lt_rev.mpr hpq)
  · rintro ⟨a,b,ha,hb,hai,hbj,hm⟩
    let A : Fin t ↪o Fin n := OrderEmbedding.ofStrictMono
      (fun p => ⟨a p,(hai p).trans_lt i.isLt⟩) ha
    let B : Fin t ↪o Fin n := OrderEmbedding.ofStrictMono
      (fun p => ⟨b p.rev,(hbj p.rev).trans_lt j.isLt⟩)
      (fun p q hpq => hb (Fin.rev_lt_rev.mpr hpq))
    refine ⟨A,B,(fun p => hai p),(fun p => hbj p.rev),?_⟩
    apply (matchingAntidiagonal_le_iff m A B).mpr
    change occurrenceExponent (fun p => natFold (a p) (b p.rev.rev)) ≤ _
    simpa only [Fin.rev_rev] using hm

theorem mapDomain_sum_matchingAntidiagonalExponent {n : ℕ} {κ : Type*} [Fintype κ]
    (s : κ → ℕ) (a b : ∀ c, Fin (s c) ↪o Fin n) :
    (∑ c, matchingAntidiagonalExponent (a c) (b c)).mapDomain entryNat =
      occurrenceExponent (fun p : Σ c, Fin (s c) =>
        natFold (a p.1 p.2).val (b p.1 p.2.rev).val) := by
  rw [Finsupp.mapDomain_finsetSum]
  simp only [mapDomain_matchingAntidiagonalExponent,occurrenceExponent]
  exact (Fintype.sum_sigma (fun p : Σ c, Fin (s c) =>
    Finsupp.single (natFold (a p.1 p.2).val (b p.1 p.2.rev).val) (1 : ℕ))).symm

theorem matchingPacking_exists_iff {n : ℕ} (m : MatchingEntry n →₀ ℕ)
    {κ : Type*} [Fintype κ] (s : κ → ℕ) :
    (∃ a b : ∀ c, Fin (s c) ↪o Fin n,
      (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m) ↔
    ∃ P : κ → Finset (Incidence (natMonomialPairs m)),
      IsOccurrencePacking P ∧ ∀ c, (P c).card = s c := by
  classical
  constructor
  · rintro ⟨a,b,hm⟩
    apply (exists_packed_antidiagonals_iff_occurrence_packing _ s).mp
    refine ⟨fun c p => (a c p).val,fun c p => (b c p.rev).val,
      (fun c p q hpq => (a c).strictMono hpq),
      (fun c p q hpq => (b c).strictMono (Fin.rev_lt_rev.mpr hpq)),?_⟩
    rw [wordExponent_natMonomialPairs,← mapDomain_sum_matchingAntidiagonalExponent,
      Finsupp.mapDomain_le_mapDomain_iff_le entryNat_injective]
    exact hm
  · intro hP
    obtain ⟨a,b,ha,hb,hm⟩ :=
      (exists_packed_antidiagonals_iff_occurrence_packing _ s).mpr hP
    obtain ⟨e,he,hea,heb⟩ := (occurrenceExponent_fold_le_iff _ _ _).mp hm
    have haN (c : κ) (p : Fin (s c)) : a c p < n := by
      simpa only [hea] using natMonomialPairs_vertex_lt m (e ⟨c,p⟩)
    have hbN (c : κ) (p : Fin (s c)) : b c p < n := by
      simpa only [heb] using natMonomialPairs_vertex_lt m (partner (e ⟨c,p⟩))
    let A : ∀ c, Fin (s c) ↪o Fin n := fun c =>
      OrderEmbedding.ofStrictMono (fun p => ⟨a c p,haN c p⟩) (ha c)
    let B : ∀ c, Fin (s c) ↪o Fin n := fun c =>
      OrderEmbedding.ofStrictMono (fun p => ⟨b c p.rev,hbN c p.rev⟩)
        (fun p q hpq => hb c (Fin.rev_lt_rev.mpr hpq))
    refine ⟨A,B,?_⟩
    apply (Finsupp.mapDomain_le_mapDomain_iff_le entryNat_injective _ _).mp
    rw [mapDomain_sum_matchingAntidiagonalExponent,← wordExponent_natMonomialPairs]
    change occurrenceExponent (fun p : Σ c, Fin (s c) =>
      natFold (a p.1 p.2) (b p.1 p.2.rev.rev)) ≤ _
    simpa only [Fin.rev_rev] using hm

end FourPapers.Symmetric
end
/- End source MonomialFoldedWords.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MonomialPackingStatistics\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MonomialPackingStatistics"

/- Begin source MonomialPackingStatistics.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourPapers.Symmetric
open Inflation MatchingChains

theorem map_rowLengths_insertion_collapse {w : List (ℕ × ℕ)} (hw : OrderedPairs w) :
    (pairInsertList w).map List.length = (pairInsertList (inflate w)).map List.length := by
  rw [hw.insertion_collapse,List.map_map]
  simp only [Function.comp_def,List.length_map]

theorem sum_min_half_rows_inflate {w : List (ℕ × ℕ)} (hw : OrderedPairs w) (k : ℕ) :
    ((pairInsertList w).map (fun row => min k (row.length/2))).sum =
      ((pairInsertList (inflate w)).map (fun row => min k (row.length/2))).sum := by
  rw [hw.insertion_collapse,List.map_map]
  simp only [Function.comp_def,List.length_map]

/-- Full matching Greene formula transferred to arbitrary repeated edge
words, with exact multiplicities and arbitrary numbers of chains. -/
theorem Inflation.OrderedPairs.occurrencePacking_shape {w : List (ℕ × ℕ)}
    (hw : OrderedPairs w) (k : ℕ) :
    (∃ P : Fin k → Finset (Incidence w), IsOccurrencePacking P ∧
      (∑ c, (P c).card) = ((pairInsertList w).map (fun row => min k (row.length/2))).sum) ∧
    (∀ P : Fin k → Finset (Incidence w), IsOccurrencePacking P →
      (∑ c, (P c).card) ≤ ((pairInsertList w).map (fun row => min k (row.length/2))).sum) := by
  have hh := hw.matching_inflate.packing_shape_direct (Fintype.card (Incidence w))
    (fun x => mem_endpoints_inflate_iff) k
  rw [sum_min_half_rows_inflate hw k]
  constructor
  · obtain ⟨P,hP,he⟩ := hh.1
    refine ⟨fun c => occurrenceSet w (P c),hw.packing_occurrenceSet hP,?_⟩
    rw [packing_occurrenceSet_size hP]
    exact he
  · intro P hP
    have h := hh.2 (fun c => labelSet (P c)) ((hw.packing_labelSet_iff P).mpr hP)
    simpa only [packingSize,labelSet_card] using h

theorem sum_min_half_rows_natMonomialPairs {n : ℕ} (m : MatchingEntry n →₀ ℕ) (k : ℕ) :
    ((pairInsertList (natMonomialPairs m)).map (fun row => min k (row.length/2))).sum =
      ((pairedTableau m).map (fun row => min k (row.length/2))).sum := by
  have hf : StrictMono (fun x : Fin n => x.val) := fun _ _ h => h
  have h := pairInsertList_map_strictMono (fun x : Fin n => x.val) hf (monomialPairs m) []
  simp only [List.map_nil] at h
  change ((pairInsertList ((monomialPairs m).map (fun p => (p.1.val,p.2.val))) []).map
    (fun row => min k (row.length/2))).sum = _
  rw [h]
  simp only [List.map_map,Function.comp_def,List.length_map,pairedTableau,List.map_nil]

/-- The full antidiagonal-product maximum in Theorem 2.1, expressed as an
attaining product and a bound on every product. All factors are actual folded
antidiagonals in the original finite alphabet. -/
theorem monomialPacking_shape {n : ℕ} (m : MatchingEntry n →₀ ℕ) (k : ℕ) :
    (∃ (s : Fin k → ℕ) (a b : ∀ c, Fin (s c) ↪o Fin n),
      (∑ c, s c) = ((pairedTableau m).map (fun row => min k (row.length/2))).sum ∧
      (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m) ∧
    (∀ (s : Fin k → ℕ) (a b : ∀ c, Fin (s c) ↪o Fin n),
      (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m →
      (∑ c, s c) ≤ ((pairedTableau m).map (fun row => min k (row.length/2))).sum) := by
  have hh := (natMonomialPairs_ordered m).occurrencePacking_shape k
  rw [sum_min_half_rows_natMonomialPairs] at hh
  constructor
  · obtain ⟨P,hP,he⟩ := hh.1
    obtain ⟨a,b,hm⟩ := (matchingPacking_exists_iff m (fun c => (P c).card)).mpr
      ⟨P,hP,fun _ => rfl⟩
    exact ⟨fun c => (P c).card,a,b,he,hm⟩
  · intro s a b hm
    obtain ⟨P,hP,hs⟩ := (matchingPacking_exists_iff m s).mp ⟨a,b,hm⟩
    simpa only [hs] using hh.2 P hP

end FourPapers.Symmetric
end
/- End source MonomialPackingStatistics.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MonomialPrefixStatistics\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MonomialPrefixStatistics"

/- Begin source MonomialPrefixStatistics.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourPapers.Symmetric
open Inflation MatchingChains

theorem mem_finset_iff_lt_card_of_lower (S : Finset ℕ)
    (hS : ∀ a ∈ S, ∀ b ≤ a, b ∈ S) (a : ℕ) : a ∈ S ↔ a < S.card := by
  constructor
  · intro ha
    have hsub : Finset.range (a+1) ⊆ S := by
      intro b hb
      exact hS a ha b (by have := Finset.mem_range.mp hb; omega)
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_range] at hh
    omega
  · intro ha
    by_contra hn
    have hsub : S ⊆ Finset.range a := by
      intro b hb
      apply Finset.mem_range.mpr
      by_contra hnot
      exact hn (hS b hb a (by omega))
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_range] at hh
    omega

noncomputable def inflationCutoff (w : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  ((Finset.range (Fintype.card (Incidence w))).filter fun r => collapse w r ≤ i).card

theorem inflationCutoff_le (w : List (ℕ × ℕ)) (i : ℕ) :
    inflationCutoff w i ≤ Fintype.card (Incidence w) := by
  simpa only [inflationCutoff,Finset.card_range] using
    Finset.card_filter_le (Finset.range (Fintype.card (Incidence w))) (fun r => collapse w r ≤ i)

theorem lt_inflationCutoff_iff {w : List (ℕ × ℕ)} {r i : ℕ}
    (hr : r < Fintype.card (Incidence w)) :
    r < inflationCutoff w i ↔ collapse w r ≤ i := by
  classical
  let S := (Finset.range (Fintype.card (Incidence w))).filter fun r => collapse w r ≤ i
  have hS : ∀ a ∈ S, ∀ b ≤ a, b ∈ S := by
    intro a ha b hba
    obtain ⟨haN,hai⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (hba.trans_lt (Finset.mem_range.mp haN)),
      (collapse_monotone w hba).trans hai⟩
  have hh := (mem_finset_iff_lt_card_of_lower S hS r).symm
  simpa only [S,inflationCutoff,Finset.mem_filter,Finset.mem_range,and_iff_right hr] using hh

theorem label_lt_inflationCutoff_iff {w : List (ℕ × ℕ)} (o : Incidence w) (i : ℕ) :
    (label o).val < inflationCutoff w i ↔ vertex o ≤ i := by
  simpa only [collapse_label] using lt_inflationCutoff_iff (label o).isLt

theorem rowsPrefixHeight_collapse {w : List (ℕ × ℕ)} (rows : List (List ℕ)) (i : ℕ)
    (hbound : ∀ x ∈ rows.flatten, x < Fintype.card (Incidence w)) :
    rowsPrefixHeight (rows.map (List.map (collapse w))) (i+1) =
      rowsPrefixHeight rows (inflationCutoff w i) := by
  unfold rowsPrefixHeight
  rw [List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro row hr
  have hinner : row.filter (fun x => collapse w x < i+1) =
      row.filter (fun x => x < inflationCutoff w i) := by
    apply List.filter_congr
    intro x hx
    have hxN := hbound x (List.mem_flatten.mpr ⟨row,hr,hx⟩)
    have he := lt_inflationCutoff_iff (i := i) hxN
    have he' : (collapse w x < i+1) ↔ x < inflationCutoff w i := by omega
    exact decide_eq_decide.mpr he'
  have hn (l : List ℕ) : l.map (collapse w) ≠ [] ↔ l ≠ [] :=
    not_congr (List.map_eq_nil_iff (f := collapse w) (l := l))
  simp only [Function.comp_def,List.filter_map,hn,hinner]

theorem Inflation.OrderedPairs.prefixHeight_inflate {w : List (ℕ × ℕ)}
    (hw : OrderedPairs w) (i : ℕ) :
    rowsPrefixHeight (pairInsertList w) (i+1) =
      rowsPrefixHeight (pairInsertList (inflate w)) (inflationCutoff w i) := by
  rw [hw.insertion_collapse]
  apply rowsPrefixHeight_collapse
  intro x hx
  apply mem_endpoints_inflate_iff.mp
  simpa using (flatten_pairInsertList_perm (inflate w) []).mem_iff.mp hx

/-- The rectangular-chain statistic after an endpoint stage, before
translating its remaining column bound. -/
theorem Inflation.OrderedPairs.occurrencePrefix_height {w : List (ℕ × ℕ)}
    (hw : OrderedPairs w) (i : ℕ) :
    (∃ C : Finset (Incidence w), IsOccurrenceChain C ∧
      C.card = rowsPrefixHeight (pairInsertList w) (i+1) ∧ ∀ o ∈ C, vertex o ≤ i) ∧
    (∀ C : Finset (Incidence w), IsOccurrenceChain C →
      (∀ o ∈ C, vertex o ≤ i) → C.card ≤ rowsPrefixHeight (pairInsertList w) (i+1)) := by
  have hh := hw.matching_inflate.prefix_height_direct (Fintype.card (Incidence w))
    (fun x => mem_endpoints_inflate_iff) (inflationCutoff w i) (inflationCutoff_le w i)
  rw [hw.prefixHeight_inflate i]
  constructor
  · obtain ⟨C,hC,hcard,hrows⟩ := hh.1
    refine ⟨occurrenceSet w C,hw.chain_occurrenceSet hC,?_,?_⟩
    · rw [occurrenceSet_card_of_chain hC]
      exact hcard
    · intro o ho
      exact (label_lt_inflationCutoff_iff o i).mp (hrows _ ((mem_occurrenceSet o).mp ho))
  · intro C hC hi
    have hbound := hh.2 (labelSet C) ((hw.chain_labelSet_iff C).mpr hC) (by
      intro r hr
      obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp hr
      exact (label_lt_inflationCutoff_iff o i).mpr (hi o ho))
    simpa only [labelSet_card] using hbound

end FourPapers.Symmetric
end
/- End source MonomialPrefixStatistics.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MonomialRectangularStatistics\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MonomialRectangularStatistics"

/- Begin source MonomialRectangularStatistics.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourPapers.Symmetric
open Inflation

theorem toMultiset_filter_matching {α : Type*} [DecidableEq α]
    (m : α →₀ ℕ) (p : α → Prop) [DecidablePred p] :
    (m.filter p).toMultiset = m.toMultiset.filter p := by
  apply Multiset.ext.mpr
  intro a
  simp only [Finsupp.count_toMultiset,Finsupp.filter_apply,Multiset.count_filter]

theorem sort_filter_matching {α : Type*} [LinearOrder α]
    (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).sort (· ≤ ·) = (s.sort (· ≤ ·)).filter (fun a => p a) := by
  have hp : ((s.filter p).sort (· ≤ ·)).Perm
      ((s.sort (· ≤ ·)).filter (fun a => p a)) := by
    apply Multiset.coe_eq_coe.mp
    simp only [Multiset.sort_eq,← Multiset.filter_coe,Multiset.sort_eq]
  exact hp.eq_of_pairwise' (Multiset.pairwise_sort _ _) ((Multiset.pairwise_sort _ _).filter _)

def prefixMonomial {n : ℕ} (m : MatchingEntry n →₀ ℕ) (j : Fin n) :
    MatchingEntry n →₀ ℕ := m.filter (fun e => e.val.1 ≤ j)

theorem monomialPairs_prefixMonomial {n : ℕ} (m : MatchingEntry n →₀ ℕ) (j : Fin n) :
    monomialPairs (prefixMonomial m j) = (monomialPairs m).filter (fun p => p.2 ≤ j) := by
  simp only [monomialPairs,prefixMonomial,toMultiset_filter_matching,sort_filter_matching,
    List.filter_map,Function.comp_def]

theorem matchingAntidiagonal_le_prefix_iff {n t : ℕ} (m : MatchingEntry n →₀ ℕ)
    (j : Fin n) (a b : Fin t ↪o Fin n)
    (ha : ∀ p, a p ≤ j) (hb : ∀ p, b p ≤ j) :
    matchingAntidiagonalExponent a b ≤ prefixMonomial m j ↔
      matchingAntidiagonalExponent a b ≤ m := by
  constructor
  · intro h e
    apply (h e).trans
    simp only [prefixMonomial,Finsupp.filter_apply]
    split_ifs <;> omega
  · intro h e
    by_cases he : e.val.1 ≤ j
    · simpa only [prefixMonomial,Finsupp.filter_apply,if_pos he] using h e
    · rw [prefixMonomial,Finsupp.filter_apply,if_neg he]
      apply le_of_eq
      simp only [matchingAntidiagonalExponent,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro p hp
      have hne : matchingFold (a p) (b p.rev) ≠ e := by
        intro heq
        apply he
        rw [← heq]
        exact max_le (ha p) (hb p.rev)
      simp only [Finsupp.single_apply,if_neg hne]

theorem prefixMonomial_vertex_le {n : ℕ} (m : MatchingEntry n →₀ ℕ) (j : Fin n)
    (o : Incidence (natMonomialPairs (prefixMonomial m j))) : vertex o ≤ j.val := by
  have hm := vertex_mem_endpoints o
  rcases mem_endpointWord.mp hm with ⟨p,hp,he⟩
  simp only [natMonomialPairs,monomialPairs,List.map_map,List.mem_map,
    Function.comp_apply] at hp
  obtain ⟨e,he',rfl⟩ := hp
  have hs : e ∈ (prefixMonomial m j).support :=
    (Finsupp.mem_toMultiset _ _).mp ((Multiset.mem_sort _).mp he')
  have hbound : e.val.1 ≤ j := (Finset.mem_filter.mp hs).2
  rcases he with h | h
  · rw [h]
    exact e.property.trans hbound
  · rw [h]
    exact hbound

theorem rowsPrefixHeight_map_fin {n : ℕ} (rows : List (List (Fin n))) (i : Fin n) :
    rowsPrefixHeight (rows.map (List.map (fun x : Fin n => x.val))) (i.val+1) =
      (rows.filter (fun row => (row.filter (fun x => x ≤ i)) ≠ [])).length := by
  have hn (l : List (Fin n)) :
      l.map (fun x : Fin n => x.val) ≠ [] ↔ l ≠ [] :=
    not_congr (List.map_eq_nil_iff (f := fun x : Fin n => x.val) (l := l))
  simp only [rowsPrefixHeight,List.filter_map,List.length_map,hn,
    Function.comp_def,Nat.lt_succ_iff,← Fin.le_def]

theorem rowsPrefixHeight_natMonomialPairs_prefix {n : ℕ}
    (m : MatchingEntry n →₀ ℕ) (i j : Fin n) :
    rowsPrefixHeight (pairInsertList (natMonomialPairs (prefixMonomial m j))) (i.val+1) =
      ((pairInsertList ((monomialPairs m).filter (fun p => p.2 ≤ j))).filter
        (fun row => (row.filter (fun x => x ≤ i)) ≠ [])).length := by
  have hf : StrictMono (fun x : Fin n => x.val) := fun _ _ h => h
  have h := pairInsertList_map_strictMono (fun x : Fin n => x.val) hf
    (monomialPairs (prefixMonomial m j)) []
  simp only [List.map_nil] at h
  change rowsPrefixHeight (pairInsertList
    ((monomialPairs (prefixMonomial m j)).map (fun p => (p.1.val,p.2.val))) []) _ = _
  rw [h]
  simp only [List.map_nil,rowsPrefixHeight_map_fin,monomialPairs_prefixMonomial]

/-- Full northwest rank formula of Theorem 2.1, in an attained-maximum form.
The original endpoint-stage tableau and literal folded antidiagonal divisors
occur in the statement; no statistic is defined through the asserted equality. -/
theorem monomialRectangular_shape {n : ℕ} (m : MatchingEntry n →₀ ℕ)
    (i j : Fin n) (hij : i ≤ j) :
    let H := ((pairInsertList ((monomialPairs m).filter (fun p => p.2 ≤ j))).filter
      (fun row => (row.filter (fun x => x ≤ i)) ≠ [])).length
    (∃ a b : Fin H ↪o Fin n, (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧
      matchingAntidiagonalExponent a b ≤ m) ∧
    (∀ (t : ℕ) (a b : Fin t ↪o Fin n), (∀ p, a p ≤ i) → (∀ p, b p ≤ j) →
      matchingAntidiagonalExponent a b ≤ m → t ≤ H) := by
  dsimp only
  have hh := (natMonomialPairs_ordered (prefixMonomial m j)).occurrencePrefix_height i.val
  rw [rowsPrefixHeight_natMonomialPairs_prefix] at hh
  constructor
  · obtain ⟨C,hC,hcard,hi⟩ := hh.1
    obtain ⟨a,b,ha,hb,hm⟩ := (matchingAntidiagonal_exists_iff (prefixMonomial m j) i j).mpr
      ⟨C,hC,hcard,hi,fun o ho => prefixMonomial_vertex_le m j (partner o)⟩
    exact ⟨a,b,ha,hb,(matchingAntidiagonal_le_prefix_iff m j a b
      (fun p => (ha p).trans hij) hb).mp hm⟩
  · intro t a b ha hb hm
    have hm' := (matchingAntidiagonal_le_prefix_iff m j a b
      (fun p => (ha p).trans hij) hb).mpr hm
    obtain ⟨C,hC,hcard,hi,hj⟩ := (matchingAntidiagonal_exists_iff (prefixMonomial m j) i j).mp
      ⟨a,b,ha,hb,hm'⟩
    rw [← hcard]
    exact hh.2 C hC hi

end FourPapers.Symmetric
end
/- End source MonomialRectangularStatistics.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN HalfShapeScores\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN HalfShapeScores"

/- Begin source HalfShapeScores.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FourPapers.Symmetric

def rowPackingScore (μ : List ℕ) (k : ℕ) : ℕ := (μ.map (min k)).sum

def rowTailScore (μ : List ℕ) (r : ℕ) : ℕ := (μ.drop r).sum

theorem rowPackingScore_le_sum (μ : List ℕ) (k : ℕ) : rowPackingScore μ k ≤ μ.sum := by
  induction μ with
  | nil => rfl
  | cons a μ ih =>
    simp only [rowPackingScore,List.map_cons,List.sum_cons] at *
    exact Nat.add_le_add (min_le_right _ _) ih

theorem rowPackingScore_le_prefix_add_tail (μ : List ℕ) (k r : ℕ) :
    rowPackingScore μ k ≤ r*k + rowTailScore μ r := by
  induction r generalizing μ with
  | zero => simpa only [rowTailScore,List.drop_zero,Nat.zero_mul,Nat.zero_add] using
      rowPackingScore_le_sum μ k
  | succ r ih =>
    cases μ with
    | nil => simp [rowPackingScore,rowTailScore]
    | cons a μ =>
      have h := ih μ
      simp only [rowPackingScore,List.map_cons,List.sum_cons,rowTailScore,List.drop_succ_cons,
        Nat.succ_mul] at *
      have ha := min_le_left k a
      omega

theorem sortedGE_getD_le_head (a : ℕ) (μ : List ℕ) (h : (a::μ).SortedGE) (r : ℕ) :
    μ.getD r 0 ≤ a := by
  obtain ⟨ha,hμ⟩ := List.sortedGE_cons.mp h
  by_cases hr : r < μ.length
  · rw [List.getD_eq_getElem _ _ hr]
    exact ha _ (List.getElem_mem hr)
  · rw [List.getD_eq_default μ 0 (Nat.le_of_not_gt hr)]
    exact Nat.zero_le _

theorem rowPackingScore_at_head (a : ℕ) (μ : List ℕ) (h : (a::μ).SortedGE) :
    rowPackingScore (a::μ) a = (a::μ).sum := by
  unfold rowPackingScore
  have hm : (a::μ).map (min a) = (a::μ).map id := by
    apply List.map_congr_left
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_self _
    · exact min_eq_right ((List.sortedGE_cons.mp h).1 x hx)
  rw [hm,List.map_id]

/-- The column cutoff given by the next half-row length attains the tail
formula. The statement also covers cutoffs beyond the last row. -/
theorem rowPackingScore_at_getD (μ : List ℕ) (hμ : μ.SortedGE) (r : ℕ) :
    rowPackingScore μ (μ.getD r 0) = r*(μ.getD r 0) + rowTailScore μ r := by
  induction r generalizing μ with
  | zero =>
    cases μ with
    | nil => simp [rowPackingScore,rowTailScore]
    | cons a μ => simpa only [List.getD_cons_zero,Nat.zero_mul,Nat.zero_add,
        rowTailScore,List.drop_zero] using rowPackingScore_at_head a μ hμ
  | succ r ih =>
    cases μ with
    | nil => simp [rowPackingScore,rowTailScore]
    | cons a μ =>
      have htail := (List.sortedGE_cons.mp hμ).2
      have hk := sortedGE_getD_le_head a μ hμ r
      have ht := ih μ htail
      simp only [List.getD_cons_succ,rowPackingScore,List.map_cons,List.sum_cons,
        min_eq_left hk,rowTailScore,List.drop_succ_cons,Nat.succ_mul] at *
      omega

/-- Equation (5.1), without introducing a bounded surrogate maximum. Every
natural number k satisfies the bound, and the displayed k attains equality. -/
theorem rowTailScore_is_max (μ : List ℕ) (hμ : μ.SortedGE) (r : ℕ) :
    (∀ k : ℕ, rowPackingScore μ k - k*r ≤ rowTailScore μ r) ∧
    rowPackingScore μ (μ.getD r 0) - (μ.getD r 0)*r = rowTailScore μ r := by
  constructor
  · intro k
    have h := rowPackingScore_le_prefix_add_tail μ k r
    rw [Nat.mul_comm r k] at h
    omega
  · rw [rowPackingScore_at_getD μ hμ r,Nat.mul_comm r (μ.getD r 0)]
    omega

theorem _root_.List.IsTableauRows.halfLengths_sorted {α : Type*} [Preorder α]
    {rows : List (List α)} (hrows : rows.IsTableauRows) :
    (rows.map (fun row => row.length/2)).SortedGE := by
  have h := hrows.sortedGE_map_length.pairwise
  have hdiv := h.imp (fun {a b} hab => Nat.div_le_div_right (c := 2) hab)
  have hh := (List.pairwise_map.mpr hdiv).sortedGE
  simpa only [List.map_map,Function.comp_def] using hh

theorem pairedTableau_halfLengths_sorted {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    ((pairedTableau m).map (fun row => row.length/2)).SortedGE :=
  (pairedTableau_isTableauRows m).halfLengths_sorted

/-- A bounded family of nonnegative integer budgets realizes every smaller
total exactly. This is the allocation step in Lemma 5.1. -/
theorem exists_fin_budget_sum {k : ℕ} (a : Fin k → ℕ) (s : ℕ)
    (hs : s ≤ ∑ i, a i) :
    ∃ c : Fin k → ℕ, (∀ i, c i ≤ a i) ∧ (∑ i, c i) = s := by
  induction k generalizing s with
  | zero =>
    have hs0 : s = 0 := by simpa using hs
    exact ⟨Fin.elim0,(fun i => Fin.elim0 i),by simp [hs0]⟩
  | succ k ih =>
    let c₀ := min s (a 0)
    have hrem : s-c₀ ≤ ∑ i : Fin k, a i.succ := by
      rw [Fin.sum_univ_succ] at hs
      dsimp only [c₀]
      omega
    obtain ⟨c,hc,hcs⟩ := ih (fun i => a i.succ) (s-c₀) hrem
    refine ⟨Fin.cases c₀ c,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact min_le_right _ _
      · exact hc j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero,Fin.cases_succ,hcs]
      dsimp only [c₀]
      omega

theorem sum_sub_le_sum_tsub {k : ℕ} (a : Fin k → ℕ) (r : ℕ) :
    (∑ i, a i) - k*r ≤ ∑ i, (a i-r) := by
  have hh : (∑ i, a i) ≤ ∑ i, ((a i-r)+r) := by
    apply Finset.sum_le_sum
    intro i hi
    omega
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul] at hh
  omega

end FourPapers.Symmetric
end
/- End source HalfShapeScores.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN OccurrenceScores\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN OccurrenceScores"

/- Begin source OccurrenceScores.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace FourPapers.Symmetric.Inflation

theorem IsOccurrenceChain.mono {w : List (ℕ × ℕ)} {C D : Finset (Incidence w)}
    (hC : IsOccurrenceChain C) (hD : D ⊆ C) : IsOccurrenceChain D := by
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy hxy
    exact hC.increasing x (hD hx) y (hD hy) hxy
  · intro x hx y hy hxy
    exact hC.decreasing x (hD hx) y (hD hy) hxy
  · intro x hx hbad
    exact hC.oneUse x (hD hx) (hD hbad)

theorem occurrenceEndpoints_mono {w : List (ℕ × ℕ)} {C D : Finset (Incidence w)}
    (h : C ⊆ D) : occurrenceEndpoints C ⊆ occurrenceEndpoints D := by
  classical
  intro o ho
  rcases Finset.mem_union.mp ho with h₁ | h₁
  · exact Finset.mem_union_left _ (h h₁)
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h₁
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem partner (h hp))

theorem IsOccurrencePacking.restrict {w : List (ℕ × ℕ)} {κ ι : Type*}
    {P : κ → Finset (Incidence w)} (hP : IsOccurrencePacking P)
    (e : ι ↪ κ) (Q : ι → Finset (Incidence w)) (hQ : ∀ i, Q i ⊆ P (e i)) :
    IsOccurrencePacking Q := by
  refine ⟨fun i => (hP.chain (e i)).mono (hQ i),?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact Finset.disjoint_left.mp (hP.disjoint (e i) (e j) (fun he => hij (e.injective he)))
    (occurrenceEndpoints_mono (hQ i) hz) (occurrenceEndpoints_mono (hQ j) hz')

def HasOccurrenceScore (w : List (ℕ × ℕ)) (t s : ℕ) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Finset (Incidence w)), IsOccurrencePacking P ∧
    (∀ c, t ≤ (P c).card) ∧ (∑ c, ((P c).card-t+1)) = s

/-- Discard zero budgets and trim the remaining chains to precisely the
allocated scores. The construction preserves the global one-use condition. -/
theorem HasOccurrenceScore.of_packing {w : List (ℕ × ℕ)} {k t s : ℕ}
    (ht : 0 < t) (P : Fin k → Finset (Incidence w)) (hP : IsOccurrencePacking P)
    (hs : s ≤ ∑ c, ((P c).card-(t-1))) : HasOccurrenceScore w t s := by
  classical
  obtain ⟨c,hc,hcs⟩ := exists_fin_budget_sum (fun i => (P i).card-(t-1)) s hs
  let I := {i : Fin k // 0 < c i}
  have hsize (i : I) : (t-1)+c i.val ≤ (P i.val).card := by
    have hi := i.property
    have hci := hc i.val
    omega
  choose Q hQ hcard using fun i : I => Finset.exists_subset_card_eq (hsize i)
  have hPack : IsOccurrencePacking Q :=
    hP.restrict (Function.Embedding.subtype (fun i => 0 < c i)) Q hQ
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hscore (i : I) : (Q i).card-t+1 = c i.val := by
    rw [hcard]
    have hi := i.property
    omega
  have hzero : (∑ i : {i : Fin k // ¬0<c i}, c i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hp := i.property
    omega
  have hsum : (∑ i : I, c i.val) = s := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => 0<c i) c
    simpa only [hzero,Nat.add_zero,hcs] using hh
  refine ⟨Fintype.card I,fun j => Q (e j),?_,?_,?_⟩
  · exact hPack.restrict e.toEmbedding (fun j => Q (e j)) (fun _ => le_rfl)
  · intro j
    rw [hcard]
    have hi := (e j).property
    omega
  · simp only [hscore]
    rw [Equiv.sum_comp e (fun i : I => c i.val)]
    exact hsum

/-- Lemma 5.1 in occurrence form: exact symbolic score, with arbitrary
multiplicities and no restriction on the number or size of input factors. -/
theorem OrderedPairs.occurrenceScore_iff_tail {w : List (ℕ × ℕ)}
    (hw : OrderedPairs w) (t s : ℕ) (ht : 0 < t) :
    HasOccurrenceScore w t s ↔
      s ≤ rowTailScore ((pairInsertList w).map (fun row => row.length/2)) (t-1) := by
  let μ := (pairInsertList w).map (fun row => row.length/2)
  have hμ : μ.SortedGE := hw.isTableauRows.halfLengths_sorted
  have hshape (k : ℕ) :
      ((pairInsertList w).map (fun row => min k (row.length/2))).sum = rowPackingScore μ k := by
    simp only [rowPackingScore,μ,List.map_map,Function.comp_def]
  constructor
  · rintro ⟨k,P,hP,htP,hs⟩
    have hupper := (hw.occurrencePacking_shape k).2 P hP
    rw [hshape] at hupper
    have htail := rowPackingScore_le_prefix_add_tail μ k (t-1)
    have hsum : s+k*(t-1) = ∑ i, (P i).card := by
      rw [← hs]
      have hk : k*(t-1) = ∑ _i : Fin k, (t-1) := by simp
      rw [hk,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hh := htP i
      omega
    rw [Nat.mul_comm (t-1) k] at htail
    change s ≤ rowTailScore μ (t-1)
    omega
  · intro hs
    let k := μ.getD (t-1) 0
    obtain ⟨P,hP,hPsize⟩ := (hw.occurrencePacking_shape k).1
    rw [hshape,rowPackingScore_at_getD μ hμ (t-1)] at hPsize
    have hbudget := sum_sub_le_sum_tsub (fun i => (P i).card) (t-1)
    apply HasOccurrenceScore.of_packing ht P hP
    change s ≤ rowTailScore μ (t-1) at hs
    have htail : rowTailScore μ (t-1) ≤ ∑ i, ((P i).card-(t-1)) := by
      rw [hPsize] at hbudget
      dsimp only [k] at *
      rw [Nat.mul_comm (t-1) (μ.getD (t-1) 0)] at hbudget
      simpa only [Nat.add_sub_cancel_left] using hbudget
    exact hs.trans htail

end FourPapers.Symmetric.Inflation
end
/- End source OccurrenceScores.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "CANONICAL_BEGIN MonomialSymbolicStatistics\n") (fun _ => pure ())
  logInfo "CANONICAL_BEGIN MonomialSymbolicStatistics"

/- Begin source MonomialSymbolicStatistics.lean; exact hash recorded in audit/combinatorics_sources.json -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourPapers.Symmetric
open Inflation

theorem halfLengths_natMonomialPairs {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    (pairInsertList (natMonomialPairs m)).map (fun row => row.length/2) =
      (pairedTableau m).map (fun row => row.length/2) := by
  have hf : StrictMono (fun x : Fin n => x.val) := fun _ _ h => h
  have h := pairInsertList_map_strictMono (fun x : Fin n => x.val) hf (monomialPairs m) []
  simp only [List.map_nil] at h
  change (pairInsertList ((monomialPairs m).map (fun p => (p.1.val,p.2.val))) []).map
    (fun row => row.length/2) = _
  rw [h]
  simp only [List.map_map,Function.comp_def,List.length_map,pairedTableau,List.map_nil]

theorem occurrenceScore_natMonomialPairs_iff {n : ℕ}
    (m : MatchingEntry n →₀ ℕ) (t s : ℕ) :
    HasOccurrenceScore (natMonomialPairs m) t s ↔
      ∃ (k : ℕ) (sizes : Fin k → ℕ) (a b : ∀ c, Fin (sizes c) ↪o Fin n),
        (∀ c, t ≤ sizes c) ∧ (∑ c, (sizes c-t+1)) = s ∧
        (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m := by
  constructor
  · rintro ⟨k,P,hP,ht,hs⟩
    obtain ⟨a,b,hm⟩ := (matchingPacking_exists_iff m (fun c => (P c).card)).mpr
      ⟨P,hP,fun _ => rfl⟩
    exact ⟨k,fun c => (P c).card,a,b,ht,hs,hm⟩
  · rintro ⟨k,sizes,a,b,ht,hs,hm⟩
    obtain ⟨P,hP,hsize⟩ := (matchingPacking_exists_iff m sizes).mp ⟨a,b,hm⟩
    exact ⟨k,P,hP,(fun c => by simpa only [hsize] using ht c),
      by simpa only [hsize] using hs⟩

/-- Exact symbolic-score criterion for the original finite-alphabet folded
antidiagonals, including all integers s and every positive threshold t. -/
theorem monomialSymbolic_shape {n : ℕ} (m : MatchingEntry n →₀ ℕ)
    (t s : ℕ) (ht : 0 < t) :
    (∃ (k : ℕ) (sizes : Fin k → ℕ) (a b : ∀ c, Fin (sizes c) ↪o Fin n),
      (∀ c, t ≤ sizes c) ∧ (∑ c, (sizes c-t+1)) = s ∧
      (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m) ↔
    s ≤ rowTailScore ((pairedTableau m).map (fun row => row.length/2)) (t-1) := by
  rw [← occurrenceScore_natMonomialPairs_iff]
  have hh := (natMonomialPairs_ordered m).occurrenceScore_iff_tail t s ht
  simpa only [halfLengths_natMonomialPairs] using hh

end FourPapers.Symmetric
end
/- End source MonomialSymbolicStatistics.lean -/

/- One read-only audit of the full checked environment. -/
/-!
# Closed statement and trust audit for the combinatorial core

Every example below restates its complete type outside all source-local sections.
The carrier equalities refer to the actual arithmetic bijection; the monomial
statistics use literal folded-antidiagonal exponent inequalities.
-/
noncomputable section
open FourPapers.Symmetric TauCeti
open scoped BigOperators

example {w : List (ℕ × ℕ)} (hw : MatchingWord w) (N : ℕ)
    (hDense : ∀ x : ℕ, x ∈ endpointWord w ↔ x < N) (q : ℕ) (hq : q ≤ N) :
    (∃ C : Finset ℕ, MatchingChains.IsChain (partnerMap w) C ∧
      C.card = rowsPrefixHeight (pairInsertList w) q ∧ ∀ i ∈ C, i < q) ∧
    (∀ C : Finset ℕ, MatchingChains.IsChain (partnerMap w) C →
      (∀ i ∈ C, i < q) → C.card ≤ rowsPrefixHeight (pairInsertList w) q) :=
  hw.prefix_height_direct N hDense q hq

example {w : List (ℕ × ℕ)} (hw : MatchingWord w) (N : ℕ)
    (hDense : ∀ x : ℕ, x ∈ endpointWord w ↔ x < N) (k : ℕ) :
    (∃ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P ∧
      MatchingChains.packingSize P =
        ((pairInsertList w).map (fun row => min k (row.length / 2))).sum) ∧
    (∀ P : Fin k → Finset ℕ, MatchingChains.IsPacking (partnerMap w) P →
      MatchingChains.packingSize P ≤
        ((pairInsertList w).map (fun row => min k (row.length / 2))).sum) :=
  hw.packing_shape_direct N hDense k

example (n : ℕ) :
    (MatchingEntry n →₀ ℕ) ≃
      {rows : List (List (Fin n)) // rows.IsTableauRows ∧ EvenRows rows} :=
  pairedTableauEquiv n

example (n : ℕ) (m : MatchingEntry n →₀ ℕ) :
    (pairedTableauEquiv n m).val = pairedTableau m :=
  pairedTableauEquiv_apply n m

example {n : ℕ} : Function.Injective (pairedTableau (n := n)) :=
  pairedTableau_injective

example {n : ℕ} {rows : List (List (Fin n))}
    (hrows : rows.IsTableauRows) (heven : EvenRows rows) :
    ∃ m : MatchingEntry n →₀ ℕ, pairedTableau m = rows :=
  exists_monomial_of_evenTableau hrows heven

example {n : ℕ} (m : MatchingEntry n →₀ ℕ) :
    (pairedTableau m).flatten.Perm (endpointWord (monomialPairs m)) :=
  pairedTableau_content m

example (n : ℕ) :
    ((Fin n ⊕ MatchingEntry n) →₀ ℕ) ≃
      (Fin n → ℕ) × (MatchingEntry n →₀ ℕ) :=
  monomialCarrierEquiv n

example {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    (pairInsertList ((natMonomialPairs (matchingLiftPivotExponent m)).filter
      (fun p => p.2 ≤ q))).tail =
      (pairInsertList ((natMonomialPairs (monomialCarrierEquiv n m).2).filter
        (fun p => p.2 < q))).map (List.map Nat.succ) :=
  monomialCarrierEquiv_tableau_prefix_tail q hq m

example {n : ℕ} (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    (pairInsertList (natMonomialPairs (matchingLiftPivotExponent m))).tail =
      (pairInsertList (natMonomialPairs (monomialCarrierEquiv n m).2)).map
        (List.map Nat.succ) :=
  monomialCarrierEquiv_tableau_tail m

example {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) (i : ℕ) :
    rowsPrefixHeight
      (pairInsertList ((natMonomialPairs (monomialCarrierEquiv n m).2).filter
        (fun p => p.2 < q))) i =
      rowsPrefixHeight
        (pairInsertList ((natMonomialPairs (matchingLiftPivotExponent m)).filter
          (fun p => p.2 ≤ q))) (i + 1) - 1 :=
  monomialCarrierEquiv_prefix_height q hq m i

example {n : ℕ} (q : ℕ) (hq : q ≤ n)
    (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) :
    ((pairInsertList ((natMonomialPairs (matchingLiftPivotExponent m)).filter
      (fun p => p.2 ≤ q))).map (fun row => row.length / 2)).tail =
      (pairInsertList ((natMonomialPairs (monomialCarrierEquiv n m).2).filter
        (fun p => p.2 < q))).map (fun row => row.length / 2) :=
  monomialCarrierEquiv_halfShape_prefix_tail q hq m

example (n : ℕ) (m : (Fin n ⊕ MatchingEntry n) →₀ ℕ) (k : Fin n) :
    (monomialCarrierEquiv n m).1 k +
        (∑ e : MatchingEntry n, (monomialCarrierEquiv n m).2 e *
          ((if e.val.2 = k then 1 else 0) + (if e.val.1 = k then 1 else 0))) =
      m (.inl k) + ∑ e : MatchingEntry n, m (.inr e) *
        ((if e.val.2 = k then 1 else 0) + (if e.val.1 = k then 1 else 0)) :=
  monomialCarrierEquiv_preserves_weight n m k

example {n : ℕ} (m : MatchingEntry n →₀ ℕ) (k : ℕ) :
    (∃ (s : Fin k → ℕ) (a b : ∀ c, Fin (s c) ↪o Fin n),
      (∑ c, s c) = ((pairedTableau m).map (fun row => min k (row.length / 2))).sum ∧
      (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m) ∧
    (∀ (s : Fin k → ℕ) (a b : ∀ c, Fin (s c) ↪o Fin n),
      (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m →
      (∑ c, s c) ≤ ((pairedTableau m).map (fun row => min k (row.length / 2))).sum) :=
  monomialPacking_shape m k

example {n : ℕ} (m : MatchingEntry n →₀ ℕ) (i j : Fin n) (hij : i ≤ j) :
    let H := ((pairInsertList ((monomialPairs m).filter (fun p => p.2 ≤ j))).filter
      (fun row => (row.filter (fun x => x ≤ i)) ≠ [])).length
    (∃ a b : Fin H ↪o Fin n, (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧
      matchingAntidiagonalExponent a b ≤ m) ∧
    (∀ (t : ℕ) (a b : Fin t ↪o Fin n), (∀ p, a p ≤ i) → (∀ p, b p ≤ j) →
      matchingAntidiagonalExponent a b ≤ m → t ≤ H) :=
  monomialRectangular_shape m i j hij

example {n : ℕ} (m : MatchingEntry n →₀ ℕ) (t s : ℕ) (ht : 0 < t) :
    (∃ (k : ℕ) (sizes : Fin k → ℕ) (a b : ∀ c, Fin (sizes c) ↪o Fin n),
      (∀ c, t ≤ sizes c) ∧ (∑ c, (sizes c - t + 1)) = s ∧
      (∑ c, matchingAntidiagonalExponent (a c) (b c)) ≤ m) ↔
    s ≤ rowTailScore ((pairedTableau m).map (fun row => row.length / 2)) (t - 1) :=
  monomialSymbolic_shape m t s ht
end

#print axioms FourPapers.Symmetric.MatchingWord.prefix_height_direct
#print axioms FourPapers.Symmetric.MatchingWord.packing_shape_direct
#print axioms FourPapers.Symmetric.pairedTableauEquiv
#print axioms FourPapers.Symmetric.pairedTableauEquiv_apply
#print axioms FourPapers.Symmetric.pairedTableau_injective
#print axioms FourPapers.Symmetric.exists_monomial_of_evenTableau
#print axioms FourPapers.Symmetric.pairedTableau_content
#print axioms FourPapers.Symmetric.monomialCarrierEquiv
#print axioms FourPapers.Symmetric.monomialCarrierEquiv_bijective
#print axioms FourPapers.Symmetric.monomialCarrierEquiv_tableau_prefix_tail
#print axioms FourPapers.Symmetric.monomialCarrierEquiv_tableau_tail
#print axioms FourPapers.Symmetric.monomialCarrierEquiv_prefix_height
#print axioms FourPapers.Symmetric.monomialCarrierEquiv_halfShape_prefix_tail
#print axioms FourPapers.Symmetric.monomialCarrierEquiv_halfShape_tail
#print axioms FourPapers.Symmetric.monomialCarrierEquiv_preserves_weight
#print axioms FourPapers.Symmetric.monomialPacking_shape
#print axioms FourPapers.Symmetric.monomialRectangular_shape
#print axioms FourPapers.Symmetric.monomialSymbolic_shape

set_option maxHeartbeats 8000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let roots : Array Name := #[
    "FourPapers.Symmetric.MatchingWord.prefix_height_direct".toName,
    "FourPapers.Symmetric.MatchingWord.packing_shape_direct".toName,
    "FourPapers.Symmetric.pairedTableauEquiv".toName,
    "FourPapers.Symmetric.pairedTableauEquiv_apply".toName,
    "FourPapers.Symmetric.pairedTableau_injective".toName,
    "FourPapers.Symmetric.exists_monomial_of_evenTableau".toName,
    "FourPapers.Symmetric.pairedTableau_content".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv_bijective".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv_tableau_prefix_tail".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv_tableau_tail".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv_prefix_height".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv_halfShape_prefix_tail".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv_halfShape_tail".toName,
    "FourPapers.Symmetric.monomialCarrierEquiv_preserves_weight".toName,
    "FourPapers.Symmetric.monomialPacking_shape".toName,
    "FourPapers.Symmetric.monomialRectangular_shape".toName,
    "FourPapers.Symmetric.monomialSymbolic_shape".toName]
  let mut runtimeOnly : Array Name := #[]
  let mut auditedImports : NameSet := {}
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved local axiom: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe declaration: {name}"
      match env.find? name.getPrefix with
      | some parent =>
        if parent.isUnsafe || parent.isPartial || parent.isAxiom then
          throwError "Unsafe runtime companion lacks safe defining declaration: {name}"
      | none => throwError "Unrecognized runtime companion: {name}"
      runtimeOnly := runtimeOnly.push name
    else
      for dep in ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]) do
        if let some info := env.find? dep then
          if info.isUnsafe || info.isPartial then
            throwError "Unsafe proof dependency {dep} in safe declaration {name}"
          if info.isAxiom && !auditedImports.contains dep then
            -- Exported theorems may have axiom-shaped public declarations. Stock Lean's
            -- exportedAxiomsExt stores their checked, transitive axiom dependencies.
            -- collectAxioms uses that metadata rather than misclassifying proof stubs.
            let deps ← collectAxioms dep
            for ax in deps do
              if !allowed.contains ax then
                throwError "Unapproved imported axiom {ax}, reached through {dep} in {name}"
            auditedImports := auditedImports.insert dep
  let mut rootAxioms : Array Json := #[]
  for root in roots do
    unless env.contains root do
      throwError "Required final theorem is unavailable: {root}"
    let axioms ← collectAxioms root
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Unapproved transitive axiom in {root}: {ax}"
    rootAxioms := rootAxioms.push <| Json.mkObj [
      ("theorem", toJson root.toString), ("axioms", toJson (axioms.map Name.toString))]
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  for root in roots do
    names := names.insert root
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    Json.arr #[toJson (index name), toJson (ci.type.getUsedConstants.map index),
      toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map index),
      toJson ((ctors ci).map index), toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index)),
    ("root_axioms", Json.arr rootAxioms),
    ("compiler_runtime_only", toJson (runtimeOnly.map Name.toString))]
  liftIO <| tryCatch (IO.FS.createDirAll ".lake/reports/audit") (fun _ => pure ())
  liftIO <| tryCatch (IO.FS.writeFile ".lake/reports/audit/combinatorics_dependency_graph.json" (Json.compress graph)) (fun _ => pure ())
  logInfo m!"COMBINATORICS_AUDIT_OK {constants.size} local declarations; {roots.size} verification roots; only propext, Classical.choice, Quot.sound; no authored axioms or unsafe proof dependencies."

