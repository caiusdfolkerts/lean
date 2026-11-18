module

public import PaperVerification.BWHoles

@[expose] public section
/-! # Identification with the literal RM(1,4) Barnes–Wall construction

The diagonal point set is proved equal to D₁₆ + ½ RM(1,4).  The four-dimensional
code is defined by evaluations of affine binary functions; its Plotkin form is
made explicit, rather than postulated as a lattice identification.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev AffineCoefficients4 := AffineCoefficients3 × Binary
abbrev BinaryWord16 := Fin 16 → Binary

def affineWord4 (a : AffineCoefficients4) : BinaryWord16 :=
  Fin.append (affineWord3 a.1) (fun i => affineWord3 a.1 i + a.2)

/-- The same codeword evaluated in the four binary coordinate digits. -/
def affineValue4 (a : AffineCoefficients4) (i : Fin 16) : Binary :=
  a.1 3 + (∑ j : Fin 3, a.1 j.castSucc * (((i.val / 2 ^ j.val) % 2 : ℕ) : Binary)) +
    a.2 * (((i.val / 8) % 2 : ℕ) : Binary)

set_option maxRecDepth 65536 in
theorem affineWord4_eq_evaluation : ∀ a : AffineCoefficients4, ∀ i : Fin 16,
    affineWord4 a i = affineValue4 a i := by decide

def InRM4 (c : BinaryWord16) : Prop := ∃ a : AffineCoefficients4, c = affineWord4 a

def halfWord16 (c : BinaryWord16) : Fin 16 → ℝ := fun i => ((c i).val : ℝ) / 2

@[simp] theorem halfWord16_zero : halfWord16 (0 : BinaryWord16) = 0 := by
  funext i
  simp only [halfWord16, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, zero_div]

/-- The literal Construction-D point set in the paper. -/
def bwRMConstruction : Set (Fin 16 → ℝ) :=
  {x | ∃ z : Fin 16 → ℤ, Even (∑ i, z i) ∧ ∃ c : BinaryWord16,
    InRM4 c ∧ x = intVec z + halfWord16 c}

theorem inRM4_plotkin (c : BinaryWord16) :
    InRM4 c ↔ ∃ u : BinaryWord8, InRM3 u ∧ ∃ η : Binary,
      c = Fin.append u (fun i => u i + η) := by
  constructor
  · rintro ⟨⟨a, η⟩, rfl⟩
    exact ⟨affineWord3 a, ⟨a, rfl⟩, η, rfl⟩
  · rintro ⟨u, ⟨a, rfl⟩, η, rfl⟩
    exact ⟨(a, η), rfl⟩

theorem sum_halfWord (c : BinaryWord8) : (∑ i, halfWord c i) = (binaryWeight c : ℝ) / 2 := by
  simp only [halfWord, ← Finset.sum_div, ← Nat.cast_sum, sum_binary_val]

theorem halfWord_even_integerSum {c : BinaryWord8} (hc : InRM3 c) :
    ∃ k : ℤ, Even k ∧ (∑ i, halfWord c i) = (k : ℝ) := by
  rw [sum_halfWord]
  rcases inRM3_weight c hc with h | h | h
  · exact ⟨0, by decide, by norm_num [h]⟩
  · exact ⟨2, by decide, by norm_num [h]⟩
  · exact ⟨4, by decide, by norm_num [h]⟩

theorem e8_even_integerSum {x : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) :
    ∃ k : ℤ, Even k ∧ (∑ i, x i) = (k : ℝ) := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · exact ⟨∑ i, z i, hz, by simp [intVec]⟩
  · exact ⟨(∑ i, z i) + 4, hz.add (by decide), by norm_num [Finset.sum_add_distrib]⟩

theorem bwGamma_append_iff (x y : Fin 8 → ℝ) :
    Fin.append x y ∈ bwGammaSet ↔ x ∈ bwMSet ∧ y ∈ bwMSet ∧ x - y ∈ dPlusSet 8 := by
  constructor
  · rintro ⟨q, l, hl, k, hk, h⟩
    have hx : x = l + bwRepresentative q := by
      simpa only [bwLeft_append] using congrArg bwLeft h
    have hy : y = k + bwRepresentative q := by
      simpa only [bwRight_append] using congrArg bwRight h
    refine ⟨hx.symm ▸ bwMSet_add (dPlusSet_subset_bwM hl) (bwRepresentative_mem q),
      hy.symm ▸ bwMSet_add (dPlusSet_subset_bwM hk) (bwRepresentative_mem q), ?_⟩
    have heq : x - y = l - k := by rw [hx, hy]; abel
    rw [heq]
    exact dPlusSet_sub (by decide : Even 8) hl hk
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨q, l, hl, rfl⟩ := bw_coset_coverage hx
    obtain ⟨r, k, hk, rfl⟩ := bw_coset_coverage hy
    have hrep : bwRepresentative q - bwRepresentative r ∈ dPlusSet 8 := by
      have h := dPlusSet_sub (by decide : Even 8) hxy
        (dPlusSet_sub (by decide : Even 8) hl hk)
      convert h using 1 <;> abel
    have hqr := bwRepresentative_mod_e8_injective hrep
    subst r
    exact ⟨q, l, hl, k, hk, rfl⟩

theorem halfWord_difference_e8_words {m k : Fin 8 → ℤ} {c d : BinaryWord8}
    (h : (intVec m + halfWord c) - (intVec k + halfWord d) ∈ dPlusSet 8) :
    c = d ∨ d = fun i => c i + 1 := by
  rcases h with ⟨z, hz, he | he⟩
  · left
    funext i
    have hi := congrFun he i
    change (m i : ℝ) + ((c i).val : ℝ) / 2 -
      ((k i : ℝ) + ((d i).val : ℝ) / 2) = (z i : ℝ) at hi
    have hint : 2 * (m i - k i - z i) + ((c i).val : ℤ) - (d i).val = 0 := by
      exact_mod_cast (show 2 * ((m i : ℝ) - (k i : ℝ) - (z i : ℝ)) +
        ((c i).val : ℝ) - ((d i).val : ℝ) = 0 by linarith)
    have hb := congrArg (fun a : ℤ => (a : Binary)) hint
    exact sub_eq_zero.mp (by simpa using hb)
  · right
    funext i
    have hi := congrFun he i
    change (m i : ℝ) + ((c i).val : ℝ) / 2 -
      ((k i : ℝ) + ((d i).val : ℝ) / 2) = (z i : ℝ) + 1 / 2 at hi
    have hint : 2 * (m i - k i - z i) + ((c i).val : ℤ) - (d i).val = 1 := by
      exact_mod_cast (show 2 * ((m i : ℝ) - (k i : ℝ) - (z i : ℝ)) +
        ((c i).val : ℝ) - ((d i).val : ℝ) = 1 by linarith)
    have hb := congrArg (fun a : ℤ => (a : Binary)) hint
    have heq : c i - d i = 1 := by simpa using hb
    have hneg : (-1 : Binary) = 1 := by decide
    calc
      d i = c i - 1 := by linear_combination -heq
      _ = c i + 1 := by rw [sub_eq_add_neg, hneg]

theorem integerPart_even_total {m k : Fin 8 → ℤ} {c d : BinaryWord8}
    (hc : InRM3 c) (hd : InRM3 d)
    (h : (intVec m + halfWord c) - (intVec k + halfWord d) ∈ dPlusSet 8) :
    Even ((∑ i, m i) + ∑ i, k i) := by
  obtain ⟨a, ha, hca⟩ := halfWord_even_integerSum hc
  obtain ⟨b, hb, hdb⟩ := halfWord_even_integerSum hd
  obtain ⟨v, hv, hvsum⟩ := e8_even_integerSum h
  have heq : (∑ i, m i) - (∑ i, k i) = v - a + b := by
    have hre : ((∑ i, m i : ℤ) : ℝ) + (a : ℝ) -
        (((∑ i, k i : ℤ) : ℝ) + (b : ℝ)) = (v : ℝ) := by
      simpa only [Pi.sub_apply, Pi.add_apply, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, intVec, ← Int.cast_sum, hca, hdb] using hvsum
    exact_mod_cast (show ((∑ i, m i : ℤ) : ℝ) - ((∑ i, k i : ℤ) : ℝ) =
      (v : ℝ) - (a : ℝ) + (b : ℝ) by linarith)
  apply Int.even_add.mpr
  apply Int.even_sub.mp
  rw [heq]
  exact (hv.sub ha).add hb

theorem int_halfCode_difference_mem_e8 {m k : Fin 8 → ℤ} {c : BinaryWord8}
    (hc : InRM3 c) (η : Binary) (hp : Even ((∑ i, m i) + ∑ i, k i)) :
    (intVec m + halfWord c) - (intVec k + halfWord (fun i => c i + η)) ∈ dPlusSet 8 := by
  have hmk : Even ((∑ i, m i) - ∑ i, k i) := Int.even_sub.mpr (Int.even_add.mp hp)
  rcases binary_eq_zero_or_one η with hη | hη
  · subst η
    have heq : (intVec m + halfWord c) - (intVec k + halfWord (fun i => c i + 0)) =
        intVec (m - k) := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, halfWord, add_zero, intVec, Int.cast_sub]
      ring
    rw [heq]
    apply (intVec_mem_dPlus_iff (by decide : 0 < 8) _).mpr
    simpa only [Pi.sub_apply, Finset.sum_sub_distrib] using hmk
  · subst η
    have hcompl : halfWord (fun i => c i + 1) = fun i => 1 / 2 - halfWord c i := by
      simpa only [add_comm] using halfWord_complement c
    rw [hcompl]
    let z : Fin 8 → ℤ := fun i => m i - k i + (c i).val - 1
    have hcEven : Even ((binaryWeight c : ℕ) : ℤ) := (Int.even_coe_nat _).mpr (inRM3_even_weight hc)
    have hz : Even (∑ i, z i) := by
      simpa only [z, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Nat.cast_sum,
        sum_binary_val, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_ofNat] using
          (hmk.add hcEven).sub (by decide : Even (8 : ℤ))
    refine ⟨z, hz, Or.inr ?_⟩
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, intVec, halfWord, z,
      Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
    ring

/-- The exact lattice identity in Section 7.1, retaining its actual RM code meaning. -/
theorem bwGammaSet_eq_RMConstruction : bwGammaSet = bwRMConstruction := by
  ext z
  rw [← append_bw_blocks z]
  constructor
  · intro hz
    obtain ⟨hx, hy, hxy⟩ := (bwGamma_append_iff _ _).mp hz
    obtain ⟨m, c, hc, hm⟩ := (bwMSet_iff_integer_halfCode _).mp hx
    obtain ⟨k, d, hd, hk⟩ := (bwMSet_iff_integer_halfCode _).mp hy
    rw [hm, hk] at hxy ⊢
    have hp := integerPart_even_total hc hd hxy
    have hcd := halfWord_difference_e8_words hxy
    refine ⟨Fin.append m k, ?_, Fin.append c d, ?_, ?_⟩
    · simpa only [Fin.sum_univ_add (a := 8) (b := 8),
        Fin.append_left, Fin.append_right] using hp
    · apply (inRM4_plotkin _).mpr
      rcases hcd with hcd | hcd
      · exact ⟨c, hc, 0, by rw [← hcd]; simp⟩
      · exact ⟨c, hc, 1, by rw [hcd]⟩
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, intVec, halfWord, halfWord16,
          Pi.add_apply]
  · rintro ⟨w, hw, c, hc, hz⟩
    obtain ⟨u, hu, η, rfl⟩ := (inRM4_plotkin c).mp hc
    let m : Fin 8 → ℤ := fun i => w (Fin.castAdd 8 i)
    let k : Fin 8 → ℤ := fun i => w (Fin.natAdd 8 i)
    have hx : bwLeft z = intVec m + halfWord u := by
      funext i
      have h := congrFun hz (Fin.castAdd 8 i)
      simpa only [Fin.append_left, Pi.add_apply, intVec, halfWord, halfWord16, m] using h
    have hy : bwRight z = intVec k + halfWord (fun i => u i + η) := by
      funext i
      have h := congrFun hz (Fin.natAdd 8 i)
      simpa only [Fin.append_right, Pi.add_apply, intVec, halfWord, halfWord16, k] using h
    have hp : Even ((∑ i, m i) + ∑ i, k i) := by
      simpa only [Fin.sum_univ_add (a := 8) (b := 8), m, k] using hw
    apply (bwGamma_append_iff _ _).mpr
    rw [hx, hy]
    refine ⟨bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM hu), ?_,
      int_halfCode_difference_mem_e8 hu η hp⟩
    apply bwMSet_add (intVec_mem_bwM k) (halfWord_mem_bwM ?_)
    rcases binary_eq_zero_or_one η with h | h
    · simpa only [h, add_zero] using hu
    · simpa only [h] using inRM3_add hu inRM3_one

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.affineWord4_eq_evaluation
#print axioms PaperVerification.ColdSpots.bwGammaSet_eq_RMConstruction
