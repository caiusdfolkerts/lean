module

public import PaperVerification.BWCharacterCode
public import PaperVerification.BWEligibility

@[expose] public section

/-! # Binary addition in the actual quotient M/E8

The carry vectors are exhibited as even-sum integer vectors, proving rather than
assuming the vector-space addition of equation (27).  The resulting profile
translation rule is an equality of actual nearest-lattice distances.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def binaryCarry (a b : Binary) : ℤ := if a = 1 ∧ b = 1 then 1 else 0

theorem linear_carry_sum_even : ∀ a b : LinearCoefficients3,
    Even (∑ i, binaryCarry (linearWord3 a i) (linearWord3 b i)) := by decide

theorem halfWord_add_carry (c d : BinaryWord8) :
    halfWord c + halfWord d = intVec (fun i => binaryCarry (c i) (d i)) +
      halfWord (fun i => c i + d i) := by
  funext i
  have hi := binary_val_add_carry (c i) (d i)
  change ((c i).val : ℤ) + (d i).val = ((c i + d i).val : ℤ) +
    2 * binaryCarry (c i) (d i) at hi
  have hr : ((c i).val : ℝ) + ((d i).val : ℝ) = ((c i + d i).val : ℝ) +
      2 * (binaryCarry (c i) (d i) : ℝ) := by exact_mod_cast hi
  change ((c i).val : ℝ) / 2 + ((d i).val : ℝ) / 2 =
    (binaryCarry (c i) (d i) : ℝ) + ((c i + d i).val : ℝ) / 2
  linarith

theorem bitUnit_add_carry (ε η : Binary) : bitUnit ε + bitUnit η = bitUnit (ε + η) +
    (fun i => if i = 0 then 2 * binaryCarry ε η else 0) := by
  funext i
  by_cases hi : i = 0
  · simpa only [Pi.add_apply, bitUnit, if_pos hi, binaryCarry] using binary_val_add_carry ε η
  · simp [bitUnit, hi]

def bwRepresentativeCarry (q r : BWQuotient) : Fin 8 → ℤ :=
  (fun i => binaryCarry (linearWord3 q.1 i) (linearWord3 r.1 i)) +
    (fun i => if i = 0 then 2 * binaryCarry q.2 r.2 else 0)

theorem bwRepresentativeCarry_even (q r : BWQuotient) : Even (∑ i, bwRepresentativeCarry q r i) := by
  have h := (linear_carry_sum_even q.1 r.1).add (even_two.mul_right (binaryCarry q.2 r.2))
  simpa [bwRepresentativeCarry, Finset.sum_add_distrib] using h

theorem bwRepresentative_add_carry (q r : BWQuotient) :
    bwRepresentative q + bwRepresentative r = intVec (bwRepresentativeCarry q r) + bwRepresentative (q + r) := by
  calc
    _ = (halfWord (linearWord3 q.1) + halfWord (linearWord3 r.1)) +
        intVec (bitUnit q.2 + bitUnit r.2) := by
      rw [intVec_add]
      unfold bwRepresentative
      abel
    _ = (intVec (fun i => binaryCarry (linearWord3 q.1 i) (linearWord3 r.1 i)) +
        halfWord (fun i => linearWord3 q.1 i + linearWord3 r.1 i)) +
        intVec (bitUnit (q.2 + r.2) + (fun i => if i = 0 then 2 * binaryCarry q.2 r.2 else 0)) := by
      rw [halfWord_add_carry, bitUnit_add_carry]
    _ = _ := by
      rw [intVec_add]
      unfold bwRepresentativeCarry bwRepresentative
      rw [intVec_add, Prod.fst_add, Prod.snd_add, linearWord3_add]
      change _ = _ + (halfWord (fun i => linearWord3 q.1 i + linearWord3 r.1 i) +
        intVec (bitUnit (q.2 + r.2)))
      abel

theorem bwRepresentative_add_mod_e8 (q r : BWQuotient) :
    bwRepresentative q + bwRepresentative r - bwRepresentative (q + r) ∈ dPlusSet 8 := by
  rw [bwRepresentative_add_carry, add_sub_cancel_right]
  exact ⟨bwRepresentativeCarry q r, bwRepresentativeCarry_even q r, Or.inl rfl⟩

theorem bwRepresentative_sub_mod_e8 (q r : BWQuotient) :
    bwRepresentative q - bwRepresentative r - bwRepresentative (q - r) ∈ dPlusSet 8 := by
  have h := dPlusSet_neg (by decide : Even 8) (bwRepresentative_add_mod_e8 (q - r) r)
  rw [sub_add_cancel] at h
  convert h using 1 <;> abel

theorem bwDepthProfile_translate_representative (x : Fin 8 → ℝ) (r q : BWQuotient) :
    bwDepthProfile (x + bwRepresentative r) q = bwDepthProfile x (q - r) := by
  let u := bwRepresentative q - bwRepresentative r - bwRepresentative (q - r)
  have hu : u ∈ dPlusSet 8 := bwRepresentative_sub_mod_e8 q r
  have he : x + bwRepresentative r - bwRepresentative q =
      (x - bwRepresentative (q - r)) - u := by dsimp [u]; abel
  unfold bwDepthProfile
  rw [he]
  change squaredDepth (dPlusAddSubgroup 8 (by decide) : Set (Fin 8 → ℝ))
      ((x - bwRepresentative (q - r)) - u) =
    squaredDepth (dPlusAddSubgroup 8 (by decide) : Set (Fin 8 → ℝ))
      (x - bwRepresentative (q - r))
  exact squaredDepth_sub_of_subgroup (dPlusAddSubgroup 8 (by decide)) _ _ hu

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwRepresentative_add_mod_e8
#print axioms PaperVerification.ColdSpots.bwDepthProfile_translate_representative
