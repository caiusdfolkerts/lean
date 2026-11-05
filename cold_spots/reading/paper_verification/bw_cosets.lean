module
public import PaperVerification.BWCoordinates
public import PaperVerification.LatticeE8Families
public import Mathlib.Logic.Equiv.Set
@[expose] public section
/-! # The sixteen actual E8 cosets in M

The representatives are exactly equation (27): half of a homogeneous affine
word, followed by the optional first-coordinate unit vector.  Coverage and
uniqueness are proved on real lattice points, giving a bijection usable for
both infinite Gaussian sums and exact distances.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def halfWord (c : BinaryWord8) : Fin 8 → ℝ := fun i => ((c i).val : ℝ) / 2

theorem halfWord_apply_of_eq_zero {c : BinaryWord8} {i : Fin 8} (h : c i = 0) :
    halfWord c i = 0 := by
  change ((c i).val : ℝ) / 2 = 0
  rw [h, ZMod.val_zero]
  norm_num

theorem halfWord_apply_of_eq_one {c : BinaryWord8} {i : Fin 8} (h : c i = 1) :
    halfWord c i = 1 / 2 := by
  change ((c i).val : ℝ) / 2 = 1 / 2
  rw [h, show (1 : Binary).val = 1 by decide]
  norm_num

def bitUnit (ε : Binary) : Fin 8 → ℤ := fun i => if i = 0 then ε.val else 0

abbrev BWQuotient := LinearCoefficients3 × Binary

def bwRepresentative (q : BWQuotient) : Fin 8 → ℝ :=
  halfWord (linearWord3 q.1) + intVec (bitUnit q.2)

theorem card_bwQuotient : Fintype.card BWQuotient = 16 := by
  norm_num [BWQuotient, LinearCoefficients3, Binary, Fintype.card_fun]

theorem sum_bitUnit (ε : Binary) : (∑ i, bitUnit ε i) = (ε.val : ℤ) := by
  simp [bitUnit]

theorem halfWord_mem_bwM {c : BinaryWord8} (hc : InRM3 c) : halfWord c ∈ bwMSet := by
  refine ⟨fun i => (c i).val, ?_, rfl⟩
  simpa only [binary_val_cast] using hc

theorem bwRepresentative_mem (q : BWQuotient) : bwRepresentative q ∈ bwMSet :=
  bwMSet_add (halfWord_mem_bwM (linearWord3_mem q.1)) (intVec_mem_bwM (bitUnit q.2))

theorem bwMSet_iff_integer_halfCode (x : Fin 8 → ℝ) :
    x ∈ bwMSet ↔ ∃ m : Fin 8 → ℤ, ∃ c : BinaryWord8,
      InRM3 c ∧ x = intVec m + halfWord c := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    let c : BinaryWord8 := fun i => (w i : Binary)
    let m : Fin 8 → ℤ := fun i => (w i - (c i).val) / 2
    have hi (i : Fin 8) : 2 * m i = w i - (c i).val := by
      apply Int.mul_ediv_cancel'
      apply even_iff_two_dvd.mp
      apply ZMod.intCast_eq_zero_iff_even.mp
      simp only [Int.cast_sub, binary_val_cast, c, sub_self]
    refine ⟨m, c, hw, ?_⟩
    funext i
    change (w i : ℝ) / 2 = (m i : ℝ) + ((c i).val : ℝ) / 2
    have h : 2 * (m i : ℝ) = (w i : ℝ) - ((c i).val : ℝ) := by exact_mod_cast hi i
    linarith
  · rintro ⟨m, c, hc, rfl⟩
    exact bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM hc)

theorem halfWord_complement (c : BinaryWord8) :
    halfWord (fun i => 1 + c i) = fun i => 1 / 2 - halfWord c i := by
  funext i
  change (((1 + c i).val : ℝ) / 2) = 1 / 2 - ((c i).val : ℝ) / 2
  rcases binary_eq_zero_or_one (c i) with h | h
  · rw [h, add_zero, show (1 : Binary).val = 1 by decide, ZMod.val_zero]
    norm_num
  · rw [h, show (1 + 1 : Binary) = 0 by decide, ZMod.val_zero,
      show (1 : Binary).val = 1 by decide]
    norm_num

theorem intVec_mem_dPlus_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℤ) :
    intVec z ∈ dPlusSet n ↔ Even (∑ i, z i) := by
  constructor
  · rintro ⟨w, hw, he | he⟩
    · have hzw := intVec_injective n he
      simpa only [hzw] using hw
    · have hi := congrFun he ⟨0, hn⟩
      exact (integer_ne_half_shift (z ⟨0, hn⟩) (w ⟨0, hn⟩) hi).elim
  · intro hz
    exact ⟨z, hz, Or.inl rfl⟩

theorem even_sum_sub_parity_bit (m : Fin 8 → ℤ) :
    Even ((∑ i, m i) - (((∑ i, m i : ℤ) : Binary).val : ℤ)) := by
  apply ZMod.intCast_eq_zero_iff_even.mp
  simp only [Int.cast_sub, binary_val_cast, sub_self]

/-- Every actual M point belongs to one of the sixteen displayed cosets. -/
theorem bw_coset_coverage {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) :
    ∃ q : BWQuotient, ∃ l ∈ dPlusSet 8, x = l + bwRepresentative q := by
  rcases (bwMSet_iff_integer_halfCode x).mp hx with ⟨m, c, hc, rfl⟩
  obtain ⟨a, hc | hc⟩ := inRM3_linear_or_complement c hc
  · subst c
    let ε : Binary := (∑ i, m i : ℤ)
    let z := m - bitUnit ε
    have hz : Even (∑ i, z i) := by
      simpa only [z, Pi.sub_apply, Finset.sum_sub_distrib, sum_bitUnit, ε] using
        even_sum_sub_parity_bit m
    refine ⟨(a, ε), intVec z, ⟨z, hz, Or.inl rfl⟩, ?_⟩
    funext i
    simp only [bwRepresentative, Pi.add_apply, intVec, z, Pi.sub_apply, Int.cast_sub]
    ring
  · rw [hc, halfWord_complement]
    let ε : Binary := (∑ i, m i : ℤ)
    let u : Fin 8 → ℤ := fun i => (linearWord3 a i).val
    let z : Fin 8 → ℤ := fun i => m i - u i - bitUnit ε i
    have hu : Even (∑ i, u i) := by
      have h := (Int.even_coe_nat _).mpr (inRM3_even_weight (linearWord3_mem a))
      simpa only [u, ← Nat.cast_sum, sum_binary_val] using h
    have hz : Even (∑ i, z i) := by
      have hm := (even_sum_sub_parity_bit m).sub hu
      have heq : (∑ i, z i) = ((∑ i, m i) - (ε.val : ℤ)) - ∑ i, u i := by
        simp only [z, Finset.sum_sub_distrib, sum_bitUnit]
        ring
      rw [heq]
      exact hm
    refine ⟨(a, ε), (fun i => (z i : ℝ) + 1 / 2), ⟨z, hz, Or.inr rfl⟩, ?_⟩
    funext i
    simp only [bwRepresentative, Pi.add_apply, intVec, z, u, Int.cast_sub, halfWord,
      Int.cast_natCast]
    ring

/-- Distinct displayed representatives never differ by an E8 vector. -/
theorem bwRepresentative_mod_e8_injective {q r : BWQuotient}
    (h : bwRepresentative q - bwRepresentative r ∈ dPlusSet 8) : q = r := by
  rcases h with ⟨z, hz, he | he⟩
  · have hword : linearWord3 q.1 = linearWord3 r.1 := by
      funext i
      have hi := congrFun he i
      change ((linearWord3 q.1 i).val : ℝ) / 2 + (bitUnit q.2 i : ℝ) -
        (((linearWord3 r.1 i).val : ℝ) / 2 + (bitUnit r.2 i : ℝ)) = (z i : ℝ) at hi
      have hint : ((linearWord3 q.1 i).val : ℤ) - (linearWord3 r.1 i).val +
          2 * (bitUnit q.2 i - bitUnit r.2 i) = 2 * z i := by
        exact_mod_cast (show ((linearWord3 q.1 i).val : ℝ) - (linearWord3 r.1 i).val +
          2 * ((bitUnit q.2 i : ℝ) - (bitUnit r.2 i : ℝ)) = 2 * (z i : ℝ) by linarith)
      have hb := congrArg (fun k : ℤ => (k : Binary)) hint
      have hsub : linearWord3 q.1 i - linearWord3 r.1 i = 0 := by simpa using hb
      exact sub_eq_zero.mp hsub
    have ha : q.1 = r.1 := linearWord3_injective hword
    have hz' : intVec (bitUnit q.2 - bitUnit r.2) ∈ dPlusSet 8 := by
      have heq : bwRepresentative q - bwRepresentative r = intVec (bitUnit q.2 - bitUnit r.2) := by
        funext i
        simp only [bwRepresentative, Pi.sub_apply, Pi.add_apply, hword, intVec, Int.cast_sub]
        ring
      rw [heq] at he
      rw [he]
      exact ⟨z, hz, Or.inl rfl⟩
    have hp := (intVec_mem_dPlus_iff (by decide : 0 < 8) _).mp hz'
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_bitUnit] at hp
    have hb := hp.intCast_zmod_two
    have heps : q.2 = r.2 := sub_eq_zero.mp (by simpa only [Int.cast_sub, binary_val_cast] using hb)
    exact Prod.ext ha heps
  · have hi := congrFun he 0
    have he0 : (((q.2.val : ℤ) - (r.2.val : ℤ) : ℤ) : ℝ) =
        (z 0 : ℝ) + 1 / 2 := by
      simpa [bwRepresentative, halfWord, linearWord3_zero_coordinate,
        intVec, bitUnit] using hi
    exact (integer_ne_half_shift ((q.2.val : ℤ) - r.2.val) (z 0) he0).elim

def bwCosetMap (v : BWQuotient × dPlusSet 8) : bwMSet :=
  ⟨v.2.val + bwRepresentative v.1, bwMSet_add (dPlusSet_subset_bwM v.2.property)
    (bwRepresentative_mem v.1)⟩

theorem bwCosetMap_bijective : Function.Bijective bwCosetMap := by
  constructor
  · rintro ⟨q, l⟩ ⟨r, k⟩ he
    have hv := congrArg Subtype.val he
    change l.val + bwRepresentative q = k.val + bwRepresentative r at hv
    have hd : bwRepresentative q - bwRepresentative r = k.val - l.val := by
      funext i
      have hi := congrFun hv i
      change l.val i + bwRepresentative q i = k.val i + bwRepresentative r i at hi
      change bwRepresentative q i - bwRepresentative r i = k.val i - l.val i
      linarith
    have hq : q = r := bwRepresentative_mod_e8_injective
      (hd.symm ▸ dPlusSet_sub (by decide : Even 8) k.property l.property)
    subst r
    have hl : l = k := Subtype.ext (add_right_cancel hv)
    cases hl
    rfl
  · intro x
    obtain ⟨q, l, hl, hx⟩ := bw_coset_coverage x.property
    exact ⟨(q, ⟨l, hl⟩), Subtype.ext hx.symm⟩

def bwCosetEquiv : BWQuotient × dPlusSet 8 ≃ bwMSet :=
  Equiv.ofBijective bwCosetMap bwCosetMap_bijective

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwCosetMap_bijective
#print axioms PaperVerification.ColdSpots.bw_coset_coverage
