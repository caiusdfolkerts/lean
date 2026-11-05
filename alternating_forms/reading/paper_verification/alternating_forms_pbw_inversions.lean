module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Lean.Elab.Tactic.Omega

/-!
# The finite secondary filtration for commutative PBW words

The number counted here is the literal number of out-of-order pairs of
letters. Replacing a subword by a permutation preserves every crossing
pair involving its context. Hence replacing a nonnormal subword by its
increasing rearrangement strictly lowers this number in every context.
This handles the commutative sorting steps that leave the monomial
exponent unchanged.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.PBWWords

variable {α : Type*} (R : α → α → Prop)

def badPairs : List α → ℕ
  | [] => 0
  | a::L => L.countP (fun b ↦ decide (¬R a b))+badPairs L

def crossing (L M : List α) : ℕ :=
  (L.map (fun a ↦ M.countP (fun b ↦ decide (¬R a b)))).sum

@[simp] theorem badPairs_nil : badPairs R ([] : List α)=0 := rfl
@[simp] theorem badPairs_cons (a : α) (L : List α) :
    badPairs R (a::L)=L.countP (fun b ↦ decide (¬R a b))+badPairs R L := rfl

@[simp] theorem crossing_nil (M : List α) : crossing R [] M=0 := rfl
@[simp] theorem crossing_cons (a : α) (L M : List α) :
    crossing R (a::L) M=M.countP (fun b ↦ decide (¬R a b))+crossing R L M := rfl

theorem crossing_append_left (L M N : List α) :
    crossing R (L++M) N=crossing R L N+crossing R M N := by
  simp only [crossing,List.map_append,List.sum_append]

theorem crossing_append_right (L M N : List α) :
    crossing R L (M++N)=crossing R L M+crossing R L N := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [crossing_cons,List.countP_append,ih]
    omega

theorem badPairs_append (L M : List α) :
    badPairs R (L++M)=badPairs R L+badPairs R M+crossing R L M := by
  induction L with
  | nil => simp only [List.nil_append,badPairs_nil,crossing_nil,Nat.zero_add,Nat.add_zero]
  | cons a L ih =>
    simp only [List.cons_append,badPairs_cons,List.countP_append,crossing_cons,ih]
    omega

theorem badPairs_eq_zero_iff (L : List α) :
    badPairs R L=0 ↔ L.Pairwise R := by
  classical
  induction L with
  | nil => exact ⟨fun _ ↦ List.Pairwise.nil,fun _ ↦ rfl⟩
  | cons a L ih =>
    rw [badPairs_cons,Nat.add_eq_zero,ih,List.pairwise_cons]
    constructor
    · rintro ⟨h,hL⟩
      refine ⟨?_,hL⟩
      intro b hb
      have he := List.countP_eq_zero.mp h b hb
      simpa only [Bool.not_eq_true,decide_eq_false_iff_not,not_not] using he
    · rintro ⟨h,hL⟩
      refine ⟨List.countP_eq_zero.mpr ?_,hL⟩
      intro b hb
      simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
      exact h b hb

theorem crossing_perm_left {L M : List α} (h : L.Perm M) (N : List α) :
    crossing R L N=crossing R M N :=
  (h.map (fun a ↦ N.countP (fun b ↦ decide (¬R a b)))).sum_eq

theorem crossing_perm_right (L : List α) {M N : List α} (h : M.Perm N) :
    crossing R L M=crossing R L N := by
  unfold crossing
  congr 1
  apply List.map_congr_left
  intro a ha
  exact List.Perm.countP_eq _ h

theorem badPairs_context_balance (P Q L M : List α) (h : L.Perm M) :
    badPairs R (P++L++Q)+badPairs R M=
      badPairs R (P++M++Q)+badPairs R L := by
  simp only [badPairs_append,crossing_append_left,
    crossing_perm_left R h Q,crossing_perm_right R P h]
  omega

/-- Strict decrease is retained inside every surrounding bar word. -/
theorem badPairs_context_decrease (P Q L M : List α) (h : L.Perm M)
    (hL : ¬L.Pairwise R) (hM : M.Pairwise R) :
    badPairs R (P++M++Q)<badPairs R (P++L++Q) := by
  have hpos : 0<badPairs R L := Nat.pos_of_ne_zero
    (fun hz ↦ hL ((badPairs_eq_zero_iff R L).mp hz))
  have hz := (badPairs_eq_zero_iff R M).mpr hM
  have he := badPairs_context_balance R P Q L M h
  omega

end PaperVerification.AlternatingForms.PBWWords

