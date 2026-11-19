module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Sorting rows preserves a strict column matching

If every element of an upper row is matched injectively to a strictly smaller
element in a lower row, sorting both rows leaves each upper entry strictly
larger than the entry directly below it. The proof is a finite pigeonhole
argument on initial segments. This is the row-sorting step in Hanada's
scheduled-filling construction; no catabolizability or counting assertion is
assumed here.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

/-- The first `j+1` indices cannot all inject into the first `j` indices. -/
theorem exists_initial_index_le_matching {m n : ℕ}
    (matching : Fin n ↪ Fin m) (hnm : n ≤ m) (j : Fin n) :
    ∃ i : Fin n, i ≤ j ∧ Fin.castLE hnm j ≤ matching i := by
  by_contra h
  let initial : Fin (j.val + 1) → Fin n :=
    Fin.castLE (Nat.succ_le_of_lt j.isLt)
  have hinitial : Function.Injective initial :=
    Fin.castLE_injective _
  have hsmall (i : Fin (j.val + 1)) : (matching (initial i)).val < j.val := by
    have hij : initial i ≤ j := by
      change i.val ≤ j.val
      exact Nat.le_of_lt_succ i.isLt
    have hlt' : matching (initial i) < Fin.castLE hnm j := by
      apply lt_of_not_ge
      intro hji
      exact h ⟨initial i, hij, hji⟩
    exact hlt'
  let smaller : Fin (j.val + 1) → Fin j.val :=
    fun i => ⟨(matching (initial i)).val, hsmall i⟩
  have hsmaller : Function.Injective smaller := by
    intro i k hik
    apply hinitial
    apply matching.injective
    apply Fin.ext
    exact congrArg (fun z : Fin j.val => z.val) hik
  have hcard := Fintype.card_le_of_injective smaller hsmaller
  have himpossible : j.val + 1 ≤ j.val := by
    simpa only [Fintype.card_fin] using hcard
  exact Nat.not_succ_le_self j.val himpossible

/-- Strict comparison of sorted sequences follows from any injective strict
matching; the matching itself need not preserve order. -/
theorem sorted_lt_of_injective_matching {m n : ℕ}
    (lower : Fin m ↪o α) (upper : Fin n ↪o α)
    (matching : Fin n ↪ Fin m)
    (hlt : ∀ i, lower (matching i) < upper i)
    (hnm : n ≤ m) (j : Fin n) :
    lower (Fin.castLE hnm j) < upper j := by
  obtain ⟨i, hij, hji⟩ := exists_initial_index_le_matching matching hnm j
  exact lt_of_le_of_lt (lower.monotone hji)
    (lt_of_lt_of_le (hlt i) (upper.monotone hij))

/-- The non-strict comparison used when replacing a deleted row entry by a
larger entry. -/
theorem sorted_le_of_injective_matching {m n : ℕ}
    (lower : Fin m ↪o α) (upper : Fin n ↪o α)
    (matching : Fin n ↪ Fin m)
    (hle : ∀ i, lower (matching i) ≤ upper i)
    (hnm : n ≤ m) (j : Fin n) :
    lower (Fin.castLE hnm j) ≤ upper j := by
  obtain ⟨i, hij, hji⟩ := exists_initial_index_le_matching matching hnm j
  exact (lower.monotone hji).trans ((hle i).trans (upper.monotone hij))

omit [LinearOrder α] in
/-- An injective matching implies the required inequality of row lengths. -/
theorem row_card_le_of_matching (lower upper : Finset α)
    (matching : ↥upper ↪ ↥lower) : upper.card ≤ lower.card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective matching matching.injective

/-- Sorting two finite rows preserves strict columns whenever the original
columns give an injective matching to smaller entries in the lower row. -/
theorem orderEmbOfFin_lt_of_injective_matching (lower upper : Finset α)
    (matching : ↥upper ↪ ↥lower)
    (hlt : ∀ b : ↥upper, (matching b).val < b.val) (j : Fin upper.card) :
    lower.orderEmbOfFin rfl
        (Fin.castLE (row_card_le_of_matching lower upper matching) j) <
      upper.orderEmbOfFin rfl j := by
  let indexedMatching : Fin upper.card ↪ Fin lower.card :=
    (upper.orderIsoOfFin rfl).toEquiv.toEmbedding.trans
      (matching.trans (lower.orderIsoOfFin rfl).symm.toEquiv.toEmbedding)
  have hindexed (i : Fin upper.card) :
      lower.orderEmbOfFin rfl (indexedMatching i) < upper.orderEmbOfFin rfl i := by
    change
      (((lower.orderIsoOfFin rfl)
        ((lower.orderIsoOfFin rfl).symm (matching ((upper.orderIsoOfFin rfl) i)))) : α) <
      (((upper.orderIsoOfFin rfl) i) : α)
    rw [OrderIso.apply_symm_apply]
    exact hlt ((upper.orderIsoOfFin rfl) i)
  exact sorted_lt_of_injective_matching (lower.orderEmbOfFin rfl)
    (upper.orderEmbOfFin rfl) indexedMatching hindexed
    (row_card_le_of_matching lower upper matching) j

/-- Non-strict order-statistic comparison for finite rows. -/
theorem orderEmbOfFin_le_of_injective_matching (lower upper : Finset α)
    (matching : ↥upper ↪ ↥lower)
    (hle : ∀ b : ↥upper, (matching b).val ≤ b.val) (j : Fin upper.card) :
    lower.orderEmbOfFin rfl
        (Fin.castLE (row_card_le_of_matching lower upper matching) j) ≤
      upper.orderEmbOfFin rfl j := by
  let indexedMatching : Fin upper.card ↪ Fin lower.card :=
    (upper.orderIsoOfFin rfl).toEquiv.toEmbedding.trans
      (matching.trans (lower.orderIsoOfFin rfl).symm.toEquiv.toEmbedding)
  have hindexed (i : Fin upper.card) :
      lower.orderEmbOfFin rfl (indexedMatching i) ≤ upper.orderEmbOfFin rfl i := by
    change
      (((lower.orderIsoOfFin rfl)
        ((lower.orderIsoOfFin rfl).symm (matching ((upper.orderIsoOfFin rfl) i)))) : α) ≤
      (((upper.orderIsoOfFin rfl) i) : α)
    rw [OrderIso.apply_symm_apply]
    exact hle ((upper.orderIsoOfFin rfl) i)
  exact sorted_le_of_injective_matching (lower.orderEmbOfFin rfl)
    (upper.orderEmbOfFin rfl) indexedMatching hindexed
    (row_card_le_of_matching lower upper matching) j

end HigherSpecht
