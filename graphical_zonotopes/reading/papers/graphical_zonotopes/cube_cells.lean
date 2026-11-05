module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.FinCases
public import Aesop
public import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset

/-- A Boolean cube cell fixes a set of coordinates and assigns one to a
subset of those coordinates. The other coordinates are free. -/
structure Cell (I : Type*) where
  fixed : Finset I
  ones : Finset I
  ones_subset : ones⊆fixed
  deriving DecidableEq

variable {I : Type*} [Fintype I] [DecidableEq I]

def Cell.assignment (C : Cell I) : Finset C.fixed :=
  univ.filter (fun i => i.1∈C.ones)

def Cell.pull (C : Cell I) (Y : Finset I) : Finset C.fixed :=
  univ.filter (fun i => i.1∈Y)

def Cell.Matches (C : Cell I) (Y : Finset I) : Prop := C.pull Y=C.assignment

instance (C : Cell I) (Y : Finset I) : Decidable (C.Matches Y) :=
  inferInstanceAs (Decidable (C.pull Y=C.assignment))
@[simp] theorem Cell.mem_assignment (C : Cell I) (i : C.fixed) :
    i∈C.assignment ↔ i.1∈C.ones := by simp [Cell.assignment]
@[simp] theorem Cell.mem_pull (C : Cell I) (Y : Finset I) (i : C.fixed) :
    i∈C.pull Y ↔ i.1∈Y := by simp [Cell.pull]

theorem Cell.matches_iff (C : Cell I) {Y : Finset I} :
    C.Matches Y ↔ ∀ i∈C.fixed,(i∈Y ↔ i∈C.ones) := by
  constructor
  · intro h i hi
    have hh:=Finset.ext_iff.mp h (⟨i,hi⟩ : C.fixed)
    simpa using hh
  · intro h
    apply Finset.ext
    intro i
    simpa using h i.1 i.2

theorem Cell.matches_ones (C : Cell I) : C.Matches C.ones := by
  apply C.matches_iff.mpr
  intro i hi
  rfl


/-- Splitting a cell on a previously free coordinate preserves its cube
and gives two disjoint nonempty subcells. -/
def Cell.splitZero (C : Cell I) (i : I) : Cell I where
  fixed:=insert i C.fixed
  ones:=C.ones
  ones_subset:=C.ones_subset.trans (subset_insert i C.fixed)

def Cell.splitOne (C : Cell I) (i : I) : Cell I where
  fixed:=insert i C.fixed
  ones:=insert i C.ones
  ones_subset:=insert_subset_insert i C.ones_subset

theorem Cell.matches_splitZero (C : Cell I) (i : I) (hi : i∉C.fixed) (Y : Finset I) :
    (C.splitZero i).Matches Y ↔ C.Matches Y ∧ i∉Y := by
  have hio : i∉C.ones:=fun h => hi (C.ones_subset h)
  constructor
  · intro h
    have hh:=(C.splitZero i).matches_iff.mp h
    refine ⟨C.matches_iff.mpr (fun j hj => hh j (mem_insert_of_mem hj)),?_⟩
    have he:=hh i (mem_insert_self i C.fixed)
    exact fun hy => hio (he.mp hy)
  · rintro ⟨h,hY⟩
    apply (C.splitZero i).matches_iff.mpr
    intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · simp [Cell.splitZero,hY,hio]
    · exact C.matches_iff.mp h j hj

theorem Cell.matches_splitOne (C : Cell I) (i : I) (hi : i∉C.fixed) (Y : Finset I) :
    (C.splitOne i).Matches Y ↔ C.Matches Y ∧ i∈Y := by
  constructor
  · intro h
    have hh:=(C.splitOne i).matches_iff.mp h
    refine ⟨C.matches_iff.mpr ?_,?_⟩
    · intro j hj
      have hji : j≠i:=fun he => hi (he ▸ hj)
      simpa [Cell.splitOne,hji] using hh j (mem_insert_of_mem hj)
    · exact (hh i (mem_insert_self i C.fixed)).mpr (mem_insert_self i C.ones)
  · rintro ⟨h,hY⟩
    apply (C.splitOne i).matches_iff.mpr
    intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · simp [Cell.splitOne,hY]
    · have hji : j≠i:=fun he => hi (he ▸ hj)
      simpa [Cell.splitOne,hji] using C.matches_iff.mp h j hj

theorem Cell.splitZero_ne (C : Cell I) (i : I) (hi : i∉C.fixed) : C.splitZero i≠C := by
  intro h
  have he:=congrArg Cell.fixed h
  exact hi (he ▸ mem_insert_self i C.fixed)

theorem Cell.splitOne_ne (C : Cell I) (i : I) (hi : i∉C.fixed) : C.splitOne i≠C := by
  intro h
  have he:=congrArg Cell.fixed h
  exact hi (he ▸ mem_insert_self i C.fixed)

theorem Cell.split_ne (C : Cell I) (i : I) (hi : i∉C.fixed) : C.splitZero i≠C.splitOne i := by
  intro h
  have he:=congrArg Cell.ones h
  have hm : i∈C.ones := he.symm ▸ mem_insert_self i C.ones
  exact hi (C.ones_subset hm)

def Cell.root : Cell I where
  fixed:=∅
  ones:=∅
  ones_subset:=Subset.rfl

@[simp] theorem Cell.root_matches (Y : Finset I) : (Cell.root (I:=I)).Matches Y := by
  apply (Cell.matches_iff Cell.root).mpr
  simp [Cell.root]

namespace CubePartition

def Valid (F : Finset (Cell I)) : Prop := ∀ Y : Finset I,∃! C,C∈F ∧ C.Matches Y

def UsesZero (F : Finset (Cell I)) (A : Finset I) : Prop :=
  ∀ i∈A,∃ C∈F,i∈C.fixed ∧ i∉C.ones

theorem Valid.unique {F : Finset (Cell I)} (hF : Valid F) {Y : Finset I}
    {C D : Cell I} (hC : C∈F) (hD : D∈F) (hCY : C.Matches Y) (hDY : D.Matches Y) : C=D := by
  obtain ⟨E,hE,hu⟩:=hF Y
  exact (hu C ⟨hC,hCY⟩).trans (hu D ⟨hD,hDY⟩).symm

theorem root_valid : Valid ({Cell.root} : Finset (Cell I)) := by
  intro Y
  refine ⟨Cell.root,⟨mem_singleton_self _,Cell.root_matches Y⟩,?_⟩
  intro C hC
  exact mem_singleton.mp hC.1

def refine (F : Finset (Cell I)) (C : Cell I) (i : I) : Finset (Cell I) :=
  insert (C.splitZero i) (insert (C.splitOne i) (F.erase C))

theorem Valid.splitZero_not_mem {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : C.splitZero i∉F := by
  intro hz
  have hm:=(C.matches_splitZero i hi (C.splitZero i).ones).mp (C.splitZero i).matches_ones
  exact C.splitZero_ne i hi (hF.unique hz hC (C.splitZero i).matches_ones hm.1)

theorem Valid.splitOne_not_mem {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : C.splitOne i∉F := by
  intro hz
  have hm:=(C.matches_splitOne i hi (C.splitOne i).ones).mp (C.splitOne i).matches_ones
  exact C.splitOne_ne i hi (hF.unique hz hC (C.splitOne i).matches_ones hm.1)

theorem Valid.refine_card {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) :
    (refine F C i).card=F.card+1 := by
  have h0:=hF.splitZero_not_mem hC i hi
  have h1:=hF.splitOne_not_mem hC i hi
  have h01:=C.split_ne i hi
  have h0e : C.splitZero i∉F.erase C := fun h => h0 (mem_of_mem_erase h)
  have h1e : C.splitOne i∉F.erase C := fun h => h1 (mem_of_mem_erase h)
  have h0i : C.splitZero i∉insert (C.splitOne i) (F.erase C) := by simp [h01,h0e]
  rw [refine,card_insert_of_notMem h0i,card_insert_of_notMem h1e,card_erase_of_mem hC]
  have hp:=card_pos.mpr ⟨C,hC⟩
  omega

theorem Valid.refine_valid {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : Valid (refine F C i) := by
  intro Y
  have hparent {D : Cell I} (hD : D∈refine F C i) (hDY : D.Matches Y) :
      D=C.splitZero i ∨ D=C.splitOne i ∨ (D∈F ∧ D≠C) := by
    simp only [refine,mem_insert,mem_erase] at hD
    rcases hD with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
  obtain ⟨D,hD,huniq⟩:=hF Y
  by_cases hDC : D=C
  · subst D
    by_cases hY : i∈Y
    · refine ⟨C.splitOne i,⟨by simp [refine],(C.matches_splitOne i hi Y).mpr ⟨hD.2,hY⟩⟩,?_⟩
      intro E hE
      rcases hparent hE.1 hE.2 with h|h|h
      · subst E
        exact False.elim (((C.matches_splitZero i hi Y).mp hE.2).2 hY)
      · exact h
      · exact False.elim (h.2 (huniq E ⟨h.1,hE.2⟩))
    · refine ⟨C.splitZero i,⟨by simp [refine],(C.matches_splitZero i hi Y).mpr ⟨hD.2,hY⟩⟩,?_⟩
      intro E hE
      rcases hparent hE.1 hE.2 with h|h|h
      · exact h
      · subst E
        exact False.elim (hY ((C.matches_splitOne i hi Y).mp hE.2).2)
      · exact False.elim (h.2 (huniq E ⟨h.1,hE.2⟩))
  · refine ⟨D,⟨by simp [refine,hDC,hD.1],hD.2⟩,?_⟩
    intro E hE
    rcases hparent hE.1 hE.2 with h|h|h
    · subst E
      have hm:=(C.matches_splitZero i hi Y).mp hE.2
      exact False.elim (hDC (huniq C ⟨hC,hm.1⟩).symm)
    · subst E
      have hm:=(C.matches_splitOne i hi Y).mp hE.2
      exact False.elim (hDC (huniq C ⟨hC,hm.1⟩).symm)
    · exact huniq E ⟨h.1,hE.2⟩

theorem UsesZero.refine {F : Finset (Cell I)} {A : Finset I} (hF : UsesZero F A)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : UsesZero (refine F C i) (insert i A) := by
  intro j hj
  rcases mem_insert.mp hj with hji|hj
  · subst j
    refine ⟨C.splitZero i,by simp [CubePartition.refine],by simp [Cell.splitZero],?_⟩
    exact fun h => hi (C.ones_subset h)
  · obtain ⟨D,hD,hjD,hj0⟩:=hF j hj
    by_cases hDC : D=C
    · subst D
      exact ⟨C.splitZero i,by simp [CubePartition.refine],mem_insert_of_mem hjD,hj0⟩
    · exact ⟨D,by simp [CubePartition.refine,hDC,hD],hjD,hj0⟩


/-- Distinct cells of a partition have distinct canonical vertices. -/
theorem Valid.ones_injective {F : Finset (Cell I)} (hF : Valid F) :
    Set.InjOn Cell.ones (F : Set (Cell I)) := by
  intro C hC D hD hCD
  apply hF.unique hC hD C.matches_ones
  simpa only [hCD] using D.matches_ones

theorem Valid.card_le {F : Finset (Cell I)} (hF : Valid F) :
    F.card≤2^Fintype.card I := by
  have hh:=card_le_card (subset_univ (F.image Cell.ones))
  rw [card_image_of_injOn hF.ones_injective] at hh
  simpa using hh

/-- Unless every cell is a point, some cell can still be split. -/
theorem Valid.exists_free {F : Finset (Cell I)} (hF : Valid F)
    (hlt : F.card<2^Fintype.card I) : ∃ C∈F,∃ i : I,i∉C.fixed := by
  by_contra h
  have hfixed : ∀ C∈F,∀ i : I,i∈C.fixed := by
    intro C hC i
    by_contra hi
    exact h ⟨C,hC,i,hi⟩
  have hcover : (univ : Finset (Finset I))⊆F.image Cell.ones := by
    intro Y hY
    obtain ⟨C,hC,hunique⟩:=hF Y
    have he : C.ones=Y := by
      ext i
      exact (C.matches_iff.mp hC.2 i (hfixed C hC.1 i)).symm
    exact mem_image.mpr ⟨C,hC.1,he⟩
  have hh:=(card_le_card hcover).trans (card_image_le)
  have hh' : 2^Fintype.card I≤F.card := by simpa using hh
  exact (Nat.not_le_of_lt hlt) hh'

theorem Valid.fixed_nonempty {F : Finset (Cell I)} (hF : Valid F)
    (hcard : 2≤F.card) {C : Cell I} (hC : C∈F) : C.fixed.Nonempty := by
  by_contra h
  have hf : C.fixed=∅:=not_nonempty_iff_eq_empty.mp h
  have hsub : F⊆{C} := by
    intro D hD
    apply mem_singleton.mpr
    apply hF.unique hD hC D.matches_ones
    apply C.matches_iff.mpr
    simp [hf]
  have hh:=card_le_card hsub
  simp only [card_singleton] at hh
  omega

/-- A chain of coordinate splits supplies a partition with one more cell
than coordinates split. It uses a zero assignment in every such coordinate. -/
theorem exists_chain (A : Finset I) :
    ∃ F : Finset (Cell I),Valid F ∧ F.card=A.card+1 ∧ UsesZero F A ∧
      ∀ C∈F,C.fixed⊆A := by
  induction A using Finset.induction_on with
  | empty =>
      refine ⟨{Cell.root},root_valid,by simp,?_,?_⟩
      · intro i hi
        simp at hi
      · intro C hC
        have he:=mem_singleton.mp hC
        subst C
        exact Subset.rfl
  | @insert i A hi ih =>
      obtain ⟨F,hF,hcard,huses,hfixed⟩:=ih
      obtain ⟨C,hC,huniq⟩:=hF ∅
      have hif : i∉C.fixed:=fun hh => hi (hfixed C hC.1 hh)
      refine ⟨refine F C i,hF.refine_valid hC.1 i hif,?_,huses.refine hC.1 i hif,?_⟩
      · rw [hF.refine_card hC.1 i hif,hcard,card_insert_of_notMem hi]
      · intro D hD
        simp only [refine,mem_insert,mem_erase] at hD
        rcases hD with rfl|rfl|hD
        · exact insert_subset_insert i (hfixed C hC.1)
        · exact insert_subset_insert i (hfixed C hC.1)
        · exact (hfixed D hD.2).trans (subset_insert i A)

/-- Every cardinality between the coordinate chain and the point partition
is attained by successive splits. The zero-assignment condition survives. -/
theorem exists_card (k : ℕ) (hlo : Fintype.card I+1≤k)
    (hhi : k≤2^Fintype.card I) :
    ∃ F : Finset (Cell I),Valid F ∧ F.card=k ∧ UsesZero F univ := by
  have hstep : ∀ n,Fintype.card I+1≤n → n≤2^Fintype.card I →
      ∃ F : Finset (Cell I),Valid F ∧ F.card=n ∧ UsesZero F univ := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base =>
        intro htop
        obtain ⟨F,hF,hcard,huses,hfixed⟩:=exists_chain (univ : Finset I)
        exact ⟨F,hF,by simpa using hcard,huses⟩
    | succ n hn ih =>
        intro htop
        obtain ⟨F,hF,hcard,huses⟩:=ih (by omega)
        have hlt : F.card<2^Fintype.card I:=by omega
        obtain ⟨C,hC,i,hi⟩:=hF.exists_free hlt
        refine ⟨refine F C i,hF.refine_valid hC i hi,?_,?_⟩
        · rw [hF.refine_card hC i hi,hcard]
        · simpa only [insert_eq_of_mem (mem_univ i)] using huses.refine hC i hi
  exact hstep k hlo hhi

/-- The partition required for the intermediate range of Theorem 8.7. -/
theorem exists_proper_card [Nonempty I] (k : ℕ) (hlo : Fintype.card I+1≤k)
    (hhi : k≤2^Fintype.card I) :
    ∃ F : Finset (Cell I),Valid F ∧ F.card=k ∧ UsesZero F univ ∧
      ∀ C∈F,C.fixed.Nonempty := by
  obtain ⟨F,hF,hcard,huses⟩:=exists_card k hlo hhi
  have hpos:=Fintype.card_pos (α:=I)
  refine ⟨F,hF,hcard,huses,?_⟩
  intro C hC
  exact hF.fixed_nonempty (by omega) hC

end CubePartition

end GraphicalZonotopes.TwoHub
