module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.PowersetCard
import Lean.Elab.Tactic.Omega

/-!
# The exact indexing of singleton and pair states

A selected exterior monomial records two subsets, one in each half of the
paired basis.  Its singly occupied pairs form two disjoint sets; the doubly
occupied pairs form a subset of their complement.  The equivalence below
retains every monomial, and its degree identity retains the original exterior
degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenSingletons

variable {ι : Type*} [DecidableEq ι]

abbrev SingletonState (ι : Type*) :=
  {AB : Finset ι × Finset ι // Disjoint AB.1 AB.2}

abbrev Available (S : SingletonState ι) := {i : ι // i ∉ S.val.1 ∪ S.val.2}

abbrev PairedState (ι : Type*) [DecidableEq ι] :=
  (S : SingletonState ι) × Finset (Available S)

instance [Fintype ι] : Fintype (SingletonState ι) := Fintype.ofFinite _
instance [Fintype ι] : Fintype (PairedState ι) := Fintype.ofFinite _

def pairSupport (S : SingletonState ι) (P : Finset (Available S)) : Finset ι :=
  P.map (Function.Embedding.subtype _)

theorem pairSupport_not_mem (S : SingletonState ι) (P : Finset (Available S))
    {i : ι} (hi : i ∈ pairSupport S P) : i ∉ S.val.1 ∪ S.val.2 :=
  P.property_of_mem_map_subtype hi

theorem pairSupport_disjoint_left (S : SingletonState ι) (P : Finset (Available S)) :
    Disjoint S.val.1 (pairSupport S P) := by
  apply Finset.disjoint_left.mpr
  intro i hi hP
  exact pairSupport_not_mem S P hP (Finset.mem_union_left _ hi)

theorem pairSupport_disjoint_right (S : SingletonState ι) (P : Finset (Available S)) :
    Disjoint S.val.2 (pairSupport S P) := by
  apply Finset.disjoint_left.mpr
  intro i hi hP
  exact pairSupport_not_mem S P hP (Finset.mem_union_right _ hi)

def selection (T : PairedState ι) : Finset ι × Finset ι :=
  (T.1.val.1 ∪ pairSupport T.1 T.2, T.1.val.2 ∪ pairSupport T.1 T.2)

theorem selection_sdiff_left (T : PairedState ι) :
    (selection T).1 \ (selection T).2 = T.1.val.1 := by
  ext i
  simp only [selection, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hA | hP, hn⟩
    · exact hA
    · exact False.elim (hn (Or.inr hP))
  · intro hA
    refine ⟨Or.inl hA, ?_⟩
    rintro (hB | hP)
    · exact Finset.disjoint_left.mp T.1.property hA hB
    · exact Finset.disjoint_left.mp (pairSupport_disjoint_left T.1 T.2) hA hP

theorem selection_sdiff_right (T : PairedState ι) :
    (selection T).2 \ (selection T).1 = T.1.val.2 := by
  ext i
  simp only [selection, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hB | hP, hn⟩
    · exact hB
    · exact False.elim (hn (Or.inr hP))
  · intro hB
    refine ⟨Or.inl hB, ?_⟩
    rintro (hA | hP)
    · exact Finset.disjoint_left.mp T.1.property hA hB
    · exact Finset.disjoint_left.mp (pairSupport_disjoint_right T.1 T.2) hB hP

theorem selection_inter (T : PairedState ι) :
    (selection T).1 ∩ (selection T).2 = pairSupport T.1 T.2 := by
  ext i
  simp only [selection, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hA | hP, hB | hP'⟩
    · exact False.elim (Finset.disjoint_left.mp T.1.property hA hB)
    · exact hP'
    · exact hP
    · exact hP
  · intro hP
    exact ⟨Or.inr hP, Or.inr hP⟩

theorem selection_injective : Function.Injective (selection (ι := ι)) := by
  rintro ⟨S, P⟩ ⟨T, Q⟩ h
  have hS : S = T := by
    apply Subtype.ext
    apply Prod.ext
    · simpa only [selection_sdiff_left] using
        congrArg (fun AB : Finset ι × Finset ι => AB.1 \ AB.2) h
    · simpa only [selection_sdiff_right] using
        congrArg (fun AB : Finset ι × Finset ι => AB.2 \ AB.1) h
  subst T
  have hP : pairSupport S P = pairSupport S Q := by
    simpa only [selection_inter] using
      congrArg (fun AB : Finset ι × Finset ι => AB.1 ∩ AB.2) h
  have he : P = Q := Finset.map_injective (Function.Embedding.subtype _) hP
  subst Q
  rfl

theorem selection_surjective : Function.Surjective (selection (ι := ι)) := by
  rintro ⟨A, B⟩
  have hdisjoint : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  let S : SingletonState ι := ⟨(A \ B, B \ A), hdisjoint⟩
  have hAvail : ∀ i ∈ A ∩ B, i ∉ S.val.1 ∪ S.val.2 := by
    intro i hi hs
    obtain ⟨hA, hB⟩ := Finset.mem_inter.mp hi
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (Finset.mem_sdiff.mp hs).2 hB
    · exact (Finset.mem_sdiff.mp hs).2 hA
  let P : Finset (Available S) := (A ∩ B).subtype (fun i => i ∉ S.val.1 ∪ S.val.2)
  have hP : pairSupport S P = A ∩ B := Finset.subtype_map_of_mem hAvail
  refine ⟨⟨S, P⟩, ?_⟩
  apply Prod.ext
  · change (A \ B) ∪ pairSupport S P = A
    rw [hP]
    ext i
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]
  · change (B \ A) ∪ pairSupport S P = B
    rw [hP]
    ext i
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]

def selectionEquiv : PairedState ι ≃ Finset ι × Finset ι :=
  Equiv.ofBijective selection ⟨selection_injective, selection_surjective⟩

def supportEquiv : PairedState ι ≃ Finset (ι ⊕ ι) :=
  selectionEquiv.trans Finset.sumEquiv.toEquiv.symm

@[simp] theorem supportEquiv_apply (T : PairedState ι) :
    supportEquiv T = (selection T).1.disjSum (selection T).2 := rfl

def singletonDegree (S : SingletonState ι) : ℕ := S.val.1.card + S.val.2.card

def degree (T : PairedState ι) : ℕ := singletonDegree T.1 + 2 * T.2.card

theorem support_card (T : PairedState ι) : (supportEquiv T).card = degree T := by
  rw [supportEquiv_apply, Finset.card_disjSum]
  change (T.1.val.1 ∪ pairSupport T.1 T.2).card +
    (T.1.val.2 ∪ pairSupport T.1 T.2).card = _
  rw [Finset.card_union_of_disjoint (pairSupport_disjoint_left T.1 T.2),
    Finset.card_union_of_disjoint (pairSupport_disjoint_right T.1 T.2)]
  simp only [pairSupport, Finset.card_map, degree, singletonDegree]
  omega

abbrev DegreeState (ι : Type*) [DecidableEq ι] (s : ℕ) :=
  {T : PairedState ι // degree T = s}

instance [Fintype ι] (s : ℕ) : Fintype (DegreeState ι s) := Fintype.ofFinite _

def degreeSupportEquiv (s : ℕ) : DegreeState ι s ≃ Set.powersetCard (ι ⊕ ι) s where
  toFun T := ⟨supportEquiv T.val, (support_card T.val).trans T.property⟩
  invFun S := ⟨supportEquiv.symm S.val, by
    rw [← support_card, Equiv.apply_symm_apply]
    exact S.property⟩
  left_inv T := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv S := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

end PaperVerification.AlternatingForms.EvenSingletons
