module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Lean.Elab.Tactic.Omega
@[expose] public section
/-! # The binary affine code in the Barnes–Wall construction

All code membership is literal membership in RM(1,3), the evaluations of affine
functions on F₂³.  Finite identities are proved by the kernel's ordinary decision
procedure, without `native_decide` or externally trusted computation.  These are
supporting finite algebra lemmas, not finite tests of the lattice theorem.
-/

namespace PaperVerification.ColdSpots

open scoped BigOperators

set_option maxRecDepth 65536
set_option maxHeartbeats 0

abbrev Binary := ZMod 2
abbrev AffineCoefficients3 := Fin 4 → Binary
abbrev LinearCoefficients3 := Fin 3 → Binary
abbrev BinaryWord8 := Fin 8 → Binary

@[simp] theorem binary_two_eq_zero : (2 : Binary) = 0 := by decide

@[simp] theorem binary_four_eq_zero : (4 : Binary) = 0 := by decide

@[simp] theorem binary_one_val : (1 : Binary).val = 1 := by decide

/-- Binary expansion of the coordinate index, with the last coordinate paired. -/
def binaryDigit (i : Fin 8) (j : Fin 3) : Binary := ((i.val / 2 ^ j.val) % 2 : ℕ)

/-- Evaluation of a literal affine function on F₂³. -/
def affineWord3 (a : AffineCoefficients3) : BinaryWord8 :=
  fun i => a 3 + ∑ j : Fin 3, a j.castSucc * binaryDigit i j

def linearWord3 (a : LinearCoefficients3) : BinaryWord8 :=
  fun i => ∑ j : Fin 3, a j * binaryDigit i j

/-- The first-order Reed–Muller code RM(1,3). -/
def InRM3 (c : BinaryWord8) : Prop := ∃ a : AffineCoefficients3, c = affineWord3 a

instance (c : BinaryWord8) : Decidable (InRM3 c) := by
  unfold InRM3
  infer_instance

/-- The four independent equations defining the same affine code in pair order. -/
def PairCodeCondition (c : BinaryWord8) : Prop :=
  c 0 + c 1 = c 2 + c 3 ∧ c 0 + c 1 = c 4 + c 5 ∧
  c 0 + c 1 = c 6 + c 7 ∧ c 0 + c 2 + c 4 + c 6 = 0

instance (c : BinaryWord8) : Decidable (PairCodeCondition c) := by
  unfold PairCodeCondition
  infer_instance

theorem inRM3_iff_pairCondition : ∀ c : BinaryWord8, InRM3 c ↔ PairCodeCondition c := by
  decide

theorem affineWord3_injective : Function.Injective affineWord3 := by decide

theorem linearWord3_injective : Function.Injective linearWord3 := by decide

theorem linearWord3_zero_coordinate (a : LinearCoefficients3) : linearWord3 a 0 = 0 := by
  simp [linearWord3, binaryDigit]

theorem linearWord3_mem (a : LinearCoefficients3) : InRM3 (linearWord3 a) := by
  refine ⟨Fin.snoc a 0, ?_⟩
  funext i
  unfold linearWord3 affineWord3
  rw [show (3 : Fin 4) = Fin.last 3 by decide]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, zero_add]

theorem inRM3_zero : InRM3 (fun _ => 0) := by
  refine ⟨fun _ => 0, ?_⟩
  funext i
  simp only [affineWord3, zero_mul, Finset.sum_const_zero, add_zero]

theorem inRM3_one : InRM3 (fun _ => 1) := by
  exact (inRM3_iff_pairCondition _).mpr (by decide)

theorem inRM3_add {c d : BinaryWord8} (hc : InRM3 c) (hd : InRM3 d) :
    InRM3 (fun i => c i + d i) := by
  rcases hc with ⟨a, rfl⟩
  rcases hd with ⟨b, rfl⟩
  refine ⟨a + b, ?_⟩
  funext i
  simp only [affineWord3, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem inRM3_neg {c : BinaryWord8} (hc : InRM3 c) : InRM3 (fun i => -c i) := by
  rcases hc with ⟨a, rfl⟩
  refine ⟨-a, ?_⟩
  funext i
  simp only [affineWord3, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

theorem inRM3_sub {c d : BinaryWord8} (hc : InRM3 c) (hd : InRM3 d) :
    InRM3 (fun i => c i - d i) := by
  simpa only [sub_eq_add_neg] using inRM3_add hc (inRM3_neg hd)

def binaryWeight (c : BinaryWord8) : ℕ := (Finset.univ.filter fun i => c i = 1).card

/-- The exact weight enumerator support of RM(1,3). -/
theorem inRM3_weight : ∀ c : BinaryWord8, InRM3 c →
    binaryWeight c = 0 ∨ binaryWeight c = 4 ∨ binaryWeight c = 8 := by decide

theorem inRM3_even_weight {c : BinaryWord8} (hc : InRM3 c) : Even (binaryWeight c) := by
  rcases inRM3_weight c hc with h | h | h <;> rw [h] <;> decide

theorem inRM3_weight_div_four {c : BinaryWord8} (hc : InRM3 c) : 4 ∣ binaryWeight c := by
  rcases inRM3_weight c hc with h | h | h <;> rw [h] <;> decide

/-- The complementary-pair representatives used for M/E8. -/
theorem inRM3_linear_or_complement : ∀ c : BinaryWord8, InRM3 c →
    ∃ a : LinearCoefficients3, c = linearWord3 a ∨ c = fun i => 1 + linearWord3 a i := by
  decide

theorem linearWord3_weight : ∀ a : LinearCoefficients3,
    binaryWeight (linearWord3 a) = 0 ∨ binaryWeight (linearWord3 a) = 4 := by decide

/-- The code's binary sum agrees with the parity of its number of ones. -/
theorem binary_sum_eq_weight : ∀ c : BinaryWord8,
    (∑ i, c i) = (binaryWeight c : Binary) := by decide

theorem binary_weight_le (c : BinaryWord8) : binaryWeight c ≤ 8 := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem binary_weight_zero_iff : ∀ c : BinaryWord8,
    binaryWeight c = 0 ↔ ∀ i, c i = 0 := by decide

theorem binary_weight_eight_iff : ∀ c : BinaryWord8,
    binaryWeight c = 8 ↔ ∀ i, c i = 1 := by decide

/-- Distances between an eligible four-half word and the code are exactly 2,4,6. -/
theorem eligible_word_difference_weights {c d : BinaryWord8}
    (hc : binaryWeight c = 4) (hnc : ¬InRM3 c) (hd : InRM3 d) :
      binaryWeight (fun i => c i - d i) = 2 ∨
      binaryWeight (fun i => c i - d i) = 4 ∨
      binaryWeight (fun i => c i - d i) = 6 := by
  let e : BinaryWord8 := fun i => c i - d i
  have he : Even (binaryWeight e) := by
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [← binary_sum_eq_weight]
    change (∑ i, (c i - d i)) = 0
    rw [Finset.sum_sub_distrib, binary_sum_eq_weight, binary_sum_eq_weight, hc]
    have hed := ZMod.natCast_eq_zero_iff_even.mpr (inRM3_even_weight hd)
    simpa only [hed, sub_zero, Nat.cast_ofNat] using binary_four_eq_zero
  have hn0 : binaryWeight e ≠ 0 := by
    intro h
    have he0 := (binary_weight_zero_iff e).mp h
    have hcd : c = d := by funext i; exact sub_eq_zero.mp (he0 i)
    exact hnc (hcd.symm ▸ hd)
  have hn8 : binaryWeight e ≠ 8 := by
    intro h
    have he1 := (binary_weight_eight_iff e).mp h
    have hcd : c = fun i => d i + 1 := by
      funext i
      have hi : c i - d i = 1 := he1 i
      linear_combination hi
    rw [hcd] at hnc
    exact hnc (inRM3_add hd inRM3_one)
  obtain ⟨k, hk⟩ := he
  have hle := binary_weight_le e
  change binaryWeight e = 2 ∨ binaryWeight e = 4 ∨ binaryWeight e = 6
  omega

theorem binary_eq_zero_or_one : ∀ c : Binary, c = 0 ∨ c = 1 := by decide

theorem binary_val_zero_or_one (c : Binary) : c.val = 0 ∨ c.val = 1 := by
  have h := c.val_lt
  omega

theorem binary_val_cast (c : Binary) : ((c.val : ℤ) : Binary) = c := by
  simp

theorem sum_binary_val (c : BinaryWord8) :
    (∑ i, (c i).val) = binaryWeight c := by
  unfold binaryWeight
  have hi (i : Fin 8) : (c i).val = if c i = 1 then 1 else 0 := by
    rcases binary_eq_zero_or_one (c i) with h | h <;> norm_num [h]
  simp only [hi]
  simp

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.inRM3_iff_pairCondition
#print axioms PaperVerification.ColdSpots.eligible_word_difference_weights
