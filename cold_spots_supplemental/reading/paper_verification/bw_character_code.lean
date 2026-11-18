module

public import PaperVerification.BWCode
public import Mathlib.Tactic.SimpRw

@[expose] public section

/-! # The finite character calculation for the 120 Barnes–Wall classes

Every finite statement is an exact theorem of the indicated binary vector spaces.
The real-coordinate classification is proved separately before this count is
applied; these are not numerical tests of the Gaussian theorem.
-/

namespace PaperVerification.ColdSpots

open scoped BigOperators

-- These kernel decisions range over the same complete binary-word space as
-- BWCode, with additional character and quotient parameters.
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The even binary word supported at the origin and one further binary point. -/
def pairWord (j : Fin 8) : BinaryWord8 :=
  fun i => (if i = 0 then 1 else 0) + (if i = j then 1 else 0)

theorem pairWord_zero : pairWord 0 = 0 := by
  decide

theorem pairWord_weight : ∀ j : Fin 8, binaryWeight (pairWord j) = if j = 0 then 0 else 2 := by decide

theorem pairWord_even (j : Fin 8) : Even (binaryWeight (pairWord j)) := by
  rw [pairWord_weight]
  split_ifs <;> decide

/-- The eight exact classes of the even binary code modulo RM(1,3). -/
theorem even_word_coset_representatives : ∀ c : BinaryWord8, Even (binaryWeight c) →
    ∃! j : Fin 8, InRM3 (fun i => c i - pairWord j i) := by
  unfold ExistsUnique
  simp_rw [inRM3_iff_pairCondition]
  decide +kernel

theorem pairWord_coset_distinct : ∀ j k : Fin 8,
    InRM3 (fun i => pairWord j i - pairWord k i) ↔ j = k := by
  simp_rw [inRM3_iff_pairCondition]
  decide

theorem pairWord_coset_nonzero : ∀ j : Fin 8, InRM3 (pairWord j) ↔ j = 0 := by
  simp_rw [inRM3_iff_pairCondition]
  decide

/-- Self-orthogonality of the binary affine code, including constant words. -/
theorem rm3_even_intersection : ∀ a b : AffineCoefficients3,
    Even ((Finset.univ.filter fun i => affineWord3 a i = 1 ∧ affineWord3 b i = 1).card) := by decide +kernel

theorem linearWord3_add (a b : LinearCoefficients3) :
    linearWord3 (a + b) = fun i => linearWord3 a i + linearWord3 b i := by
  funext i
  simp only [linearWord3, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem binary_val_add_carry : ∀ a b : Binary,
    (a.val : ℤ) + b.val = ((a + b).val : ℤ) +
      2 * (if a = 1 ∧ b = 1 then 1 else 0 : ℤ) := by decide

theorem pairWord_linear_intersection : ∀ j : Fin 8, ∀ a : LinearCoefficients3,
    (∑ i, (if pairWord j i = 1 ∧ linearWord3 a i = 1 then 1 else 0 : ℤ)) =
      ((linearWord3 a j).val : ℤ) := by decide

theorem pairWord_linear_difference_weights : ∀ j : Fin 8, j ≠ 0 → ∀ a : LinearCoefficients3,
    (linearWord3 a j = 0 → binaryWeight (fun i => pairWord j i - linearWord3 a i) = 2 ∨
      binaryWeight (fun i => pairWord j i - linearWord3 a i) = 6) ∧
    (linearWord3 a j = 1 → binaryWeight (fun i => pairWord j i - linearWord3 a i) = 4) := by decide

abbrev BWCharacter := {p : Fin 8 × Binary // p ≠ (0, 0)}
abbrev BWCharacterDomain := LinearCoefficients3 × Binary

def bwCharacterEval (χ : BWCharacter) (q : BWCharacterDomain) : Binary :=
  linearWord3 q.1 χ.val.1 + χ.val.2 * q.2

theorem bwCharacterEval_add (χ : BWCharacter) (q r : BWCharacterDomain) :
    bwCharacterEval χ (q + r) = bwCharacterEval χ q + bwCharacterEval χ r := by
  simp only [bwCharacterEval, Prod.fst_add, Prod.snd_add, linearWord3_add, mul_add]
  ring

theorem bwCharacterEval_zero (χ : BWCharacter) : bwCharacterEval χ 0 = 0 := by
  simp [bwCharacterEval, linearWord3]

theorem bwCharacterEval_sub (χ : BWCharacter) (q r : BWCharacterDomain) :
    bwCharacterEval χ (q - r) = bwCharacterEval χ q - bwCharacterEval χ r := by
  have h := bwCharacterEval_add χ (q - r) r
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem bwCharacter_nonzero : ∀ χ : BWCharacter, ∃ q : BWCharacterDomain, bwCharacterEval χ q = 1 := by
  decide

/-- Distinct affine near-coset hyperplanes intersect; equal ones are disjoint
exactly when their two phase values differ. -/
theorem bwCharacter_complement_iff : ∀ χ ψ : BWCharacter, ∀ b c : Binary,
    (∀ q : BWCharacterDomain, bwCharacterEval χ q ≠ b ∨ bwCharacterEval ψ q ≠ c) ↔
      χ = ψ ∧ b ≠ c := by decide +kernel

theorem card_bwCharacter : Fintype.card BWCharacter = 15 := by decide

theorem card_bwCharacter_odd_fibre : ∀ χ : BWCharacter,
    Fintype.card {q : BWCharacterDomain // bwCharacterEval χ q = 1} = 8 := by decide

abbrev BWHoleIndex := {p : BWCharacter × BWCharacterDomain // bwCharacterEval p.1 p.2 = 1}

theorem card_bwHoleIndex : Fintype.card BWHoleIndex = 120 := by decide

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.even_word_coset_representatives
#print axioms PaperVerification.ColdSpots.bwCharacter_complement_iff
#print axioms PaperVerification.ColdSpots.card_bwHoleIndex
