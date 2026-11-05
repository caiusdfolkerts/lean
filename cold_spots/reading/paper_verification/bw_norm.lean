module

public import PaperVerification.BWNormalized

@[expose] public section

/-! # Exact Barnes–Wall minimal-norm normalization

The finite-code construction has minimum squared norm two before scaling, and
four after √2 scaling.  Both the lower bound and a literal attaining vector are
proved in ordinary Euclidean coordinates.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def binaryWeight16 (c : BinaryWord16) : ℕ := (Finset.univ.filter fun i => c i = 1).card

/-- Hamming weight is the sum of the ordinary zero-or-one representatives. -/
theorem sum_binary_val16 (c : BinaryWord16) :
    (∑ i, (c i).val) = binaryWeight16 c := by
  unfold binaryWeight16
  have hi (i : Fin 16) : (c i).val = if c i = 1 then 1 else 0 := by
    rcases binary_eq_zero_or_one (c i) with h | h
    · simp only [h, ZMod.val_zero, zero_ne_one, ite_false]
    · simp only [h, binary_one_val, ite_true]
  simp only [hi]
  simp

/-- Splitting the sixteen coordinates into the two actual blocks preserves
the complete Hamming weight, for arbitrary binary words. -/
theorem binaryWeight16_append (c d : BinaryWord8) :
    binaryWeight16 (Fin.append c d) = binaryWeight c + binaryWeight d := by
  rw [← sum_binary_val16, Fin.sum_univ_add (a := 8) (b := 8)]
  simp only [Fin.append_left, Fin.append_right, sum_binary_val]

/-- Each bit and its complement contribute exactly one to the weight. -/
theorem binaryWeight_add_complement (c : BinaryWord8) :
    binaryWeight c + binaryWeight (fun i => c i + 1) = 8 := by
  have h11 : (1 : Binary) + 1 = 0 := by decide
  have hi (i : Fin 8) : (c i).val + (c i + 1).val = 1 := by
    rcases binary_eq_zero_or_one (c i) with h | h
    · simp only [h, ZMod.val_zero, zero_add, binary_one_val]
    · simp only [h, h11, binary_one_val, ZMod.val_zero, add_zero]
  calc
    binaryWeight c + binaryWeight (fun i => c i + 1) =
        (∑ i, (c i).val) + ∑ i, (c i + 1).val := by
      rw [sum_binary_val c, sum_binary_val (fun i => c i + 1)]
    _ = ∑ i, ((c i).val + (c i + 1).val) :=
      (Finset.sum_add_distrib).symm
    _ = 8 := by
      simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_ofNat]

/-- The four-dimensional affine code has the same exact weight support,
proved structurally from its two-block form rather than by enumerating
the entire family of affine coefficient functions. -/
theorem affineWord4_weight : ∀ a : AffineCoefficients4,
    binaryWeight16 (affineWord4 a) = 0 ∨ binaryWeight16 (affineWord4 a) = 8 ∨
      binaryWeight16 (affineWord4 a) = 16 := by
  rintro ⟨a, η⟩
  rcases binary_eq_zero_or_one η with hη | hη
  · subst η
    have h := inRM3_weight (affineWord3 a) ⟨a, rfl⟩
    have hw : binaryWeight (affineWord3 a) + binaryWeight (affineWord3 a) = 0 ∨
        binaryWeight (affineWord3 a) + binaryWeight (affineWord3 a) = 8 ∨
        binaryWeight (affineWord3 a) + binaryWeight (affineWord3 a) = 16 := by omega
    simpa only [affineWord4, add_zero, binaryWeight16_append] using hw
  · subst η
    right
    left
    change binaryWeight16
      (Fin.append (affineWord3 a) (fun i => affineWord3 a i + 1)) = 8
    rw [binaryWeight16_append]
    exact binaryWeight_add_complement (affineWord3 a)

theorem inRM4_weight {c : BinaryWord16} (hc : InRM4 c) :
    binaryWeight16 c = 0 ∨ binaryWeight16 c = 8 ∨ binaryWeight16 c = 16 := by
  rcases hc with ⟨a, rfl⟩
  exact affineWord4_weight a

theorem inRM4_zero : InRM4 (fun _ => 0) := by
  exact ⟨(0, 0), by decide⟩

theorem binaryWeight16_zero_iff (c : BinaryWord16) : binaryWeight16 c = 0 ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext i
    rcases binary_eq_zero_or_one (c i) with hc | hc
    · exact hc
    · have hpos : 0 < binaryWeight16 c := Finset.card_pos.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
      omega
  · intro h
    simp [binaryWeight16, h]

theorem binary_square_eq_self : ∀ a : Binary, a ^ 2 = a := by decide

theorem even_integer_sqSum {n : ℕ} (z : Fin n → ℤ) (hz : Even (∑ i, z i)) :
    Even (∑ i, z i ^ 2) := by
  apply ZMod.intCast_eq_zero_iff_even.mp
  rw [Int.cast_sum]
  simp_rw [Int.cast_pow, binary_square_eq_self]
  rw [← Int.cast_sum]
  exact hz.intCast_zmod_two

/-- Nonzero vectors of D_n have Euclidean squared norm at least two. -/
theorem dSet_sqNorm_lower {n : ℕ} (z : Fin n → ℤ) (hz : Even (∑ i, z i))
    (hne : intVec z ≠ 0) : 2 ≤ sqDist (intVec z) 0 := by
  have hzne : z ≠ 0 := by
    intro h
    apply hne
    funext i
    simp only [h, intVec, Pi.zero_apply, Int.cast_zero]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hzne (funext h)
  have hs : 0 < (∑ i, z i ^ 2) := Finset.sum_pos'
    (fun j _ => sq_nonneg (z j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  obtain ⟨k, hk⟩ := even_integer_sqSum z hz
  have hl : 2 ≤ (∑ i, z i ^ 2) := by omega
  have hr : (2 : ℝ) ≤ ((∑ i, z i ^ 2 : ℤ) : ℝ) := by exact_mod_cast hl
  simpa only [sqDist, intVec, Pi.zero_apply, sub_zero, Int.cast_sum, Int.cast_pow] using hr

theorem half_integer_sqNorm_lower (z : ℤ) : (1 / 4 : ℝ) ≤ ((z : ℝ) + 1 / 2) ^ 2 := by
  have hz : z ≤ -1 ∨ 0 ≤ z := by omega
  rcases hz with hz | hz
  · have h : (z : ℝ) ≤ -1 := by exact_mod_cast hz
    nlinarith [sq_nonneg ((z : ℝ) + 1)]
  · have h : (0 : ℝ) ≤ z := by exact_mod_cast hz
    nlinarith [sq_nonneg (z : ℝ)]

theorem integer_halfCode_sqNorm_lower (z : Fin 16 → ℤ) (c : BinaryWord16) :
    (binaryWeight16 c : ℝ) / 4 ≤ sqDist (intVec z + halfWord16 c) 0 := by
  classical
  have hi (i : Fin 16) : (if c i = 1 then 1 / 4 else 0 : ℝ) ≤
      ((z i : ℝ) + ((c i).val : ℝ) / 2) ^ 2 := by
    rcases binary_eq_zero_or_one (c i) with hc | hc
    · simp only [hc, zero_ne_one, if_false, ZMod.val_zero, Nat.cast_zero, zero_div, add_zero]
      exact sq_nonneg _
    · simpa only [hc, if_pos rfl, ite_true, binary_one_val, Nat.cast_one] using
        half_integer_sqNorm_lower (z i)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 16))) (fun i _ => hi i)
  simpa [binaryWeight16, Finset.sum_ite, sqDist, intVec, halfWord16,
    div_eq_mul_inv] using h

/-- The exact unscaled minimum norm of the point set Γ=D16+½RM(1,4). -/
theorem bwGamma_sqNorm_lower {x : Fin 16 → ℝ} (hx : x ∈ bwGammaSet) (hne : x ≠ 0) :
    2 ≤ sqDist x 0 := by
  rw [bwGammaSet_eq_RMConstruction] at hx
  rcases hx with ⟨z, hz, c, hc, rfl⟩
  rcases inRM4_weight hc with h0 | h8 | h16
  · have hc0 := (binaryWeight16_zero_iff c).mp h0
    have heq : intVec z + halfWord16 c = intVec z := by
      rw [hc0, halfWord16_zero, add_zero]
    rw [heq] at hne ⊢
    exact dSet_sqNorm_lower z hz hne
  · have h := integer_halfCode_sqNorm_lower z c
    norm_num [h8] at h
    exact h
  · have h := integer_halfCode_sqNorm_lower z c
    norm_num [h16] at h
    linarith

def bwNormWitnessInt : Fin 16 → ℤ := fun i => if i = 0 then 1 else if i = 1 then -1 else 0

theorem bwNormWitness_even : Even (∑ i, bwNormWitnessInt i) := by
  norm_num [bwNormWitnessInt, Fin.sum_univ_succ]

theorem bwNormWitness_mem : intVec bwNormWitnessInt ∈ bwGammaSet := by
  rw [bwGammaSet_eq_RMConstruction]
  exact ⟨bwNormWitnessInt, bwNormWitness_even, 0, inRM4_zero,
    by simp only [halfWord16_zero, add_zero]⟩

theorem bwNormWitness_sqNorm : sqDist (intVec bwNormWitnessInt) 0 = 2 := by
  have h : (∑ i, bwNormWitnessInt i ^ 2 : ℤ) = 2 := by decide
  have hr : ((∑ i, bwNormWitnessInt i ^ 2 : ℤ) : ℝ) = 2 := by exact_mod_cast h
  simpa only [sqDist, intVec, Pi.zero_apply, sub_zero, Int.cast_sum, Int.cast_pow] using hr

/-- Minimal squared norm four in the normalization used throughout the manuscript. -/
theorem bw16_minimal_squared_norm :
    (∀ x ∈ bw16Set, x ≠ 0 → 4 ≤ sqDist x 0) ∧
      ∃ x ∈ bw16Set, x ≠ 0 ∧ sqDist x 0 = 4 := by
  constructor
  · intro x hx hne
    rw [bw16Set_eq_scaledGamma] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyne : y ≠ 0 := by
      intro h
      apply hne
      funext i
      simp only [scaleVec, h, Pi.zero_apply, mul_zero]
    have h := bwGamma_sqNorm_lower hy hyne
    have heq : (0 : Fin 16 → ℝ) = scaleVec (Real.sqrt 2) 0 := by
      funext i
      simp only [scaleVec, Pi.zero_apply, mul_zero]
    rw [heq, sqDist_scaleVec, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  · refine ⟨scaleVec (Real.sqrt 2) (intVec bwNormWitnessInt), ?_, ?_, ?_⟩
    · rw [bw16Set_eq_scaledGamma]
      exact ⟨intVec bwNormWitnessInt, bwNormWitness_mem, rfl⟩
    · intro hzero
      have hx := congrArg (fun x => sqDist x 0) hzero
      have hnorm : sqDist (scaleVec (Real.sqrt 2) (intVec bwNormWitnessInt)) 0 = 4 := by
        have heq : (0 : Fin 16 → ℝ) = scaleVec (Real.sqrt 2) 0 := by
          funext i
          simp only [scaleVec, Pi.zero_apply, mul_zero]
        rw [heq, sqDist_scaleVec, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), bwNormWitness_sqNorm]
        norm_num
      rw [hnorm] at hx
      norm_num [sqDist] at hx
    · have heq : (0 : Fin 16 → ℝ) = scaleVec (Real.sqrt 2) 0 := by
        funext i
        simp only [scaleVec, Pi.zero_apply, mul_zero]
      rw [heq, sqDist_scaleVec, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), bwNormWitness_sqNorm]
      norm_num

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bw16_minimal_squared_norm
