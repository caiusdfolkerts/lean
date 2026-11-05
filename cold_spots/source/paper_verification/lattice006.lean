module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.SimpRw
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import paper_verification.lattice002
public import paper_verification.lattice003
public import paper_verification.lattice004
public import paper_verification.lattice005

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.BWNorm
section Source_BWNorm

-- original header: module

-- original header: public import PaperVerification.BWNormalized

-- original header: @[expose] public section

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
end
end Source_BWNorm
-- END ORIGINAL PaperVerification.BWNorm


-- BEGIN ORIGINAL PaperVerification.BWThetaFormula
section Source_BWThetaFormula

-- original header: module

-- original header: public import PaperVerification.BWNormalized

-- original header: @[expose] public section
/-! # The printed Barnes–Wall minimum value

The value is computed at the explicit complementary quarter-coordinate witness.
The calculation uses the already proved actual Gaussian profile identity and
retains the sixteen cosets, so no separate unverified theta identity is needed.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

/-- The parity character is exactly the integer power printed in the paper. -/
theorem paritySign_eq_neg_one_zpow (z : ℤ) : paritySign z = (-1 : ℝ) ^ z := by
  exact (neg_one_zpow_eq_ite (α := ℝ) (n := z)).symm

/-- Literal correspondence with the alternating theta series of Section 2. -/
theorem alternatingGaussian_eq_literal (α t : ℝ) :
    alternatingGaussian α t =
      ∑' z : ℤ, (-1 : ℝ) ^ z * Real.exp (-α * ((z : ℝ) - t) ^ 2) := by
  unfold alternatingGaussian
  apply tsum_congr
  intro z
  rw [paritySign_eq_neg_one_zpow]

theorem paritySign_eq_of_even_iff {a b : ℤ} (h : Even a ↔ Even b) : paritySign a = paritySign b := by
  unfold paritySign
  by_cases ha : Even a
  · simp [ha, h.mp ha]
  · simp [ha, show ¬Even b from fun hb => ha (h.mpr hb)]

theorem paritySign_sq (a : ℤ) : paritySign a ^ 2 = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

/-- The exact two-valued theta profile of every integral-sum quarter vector. -/
theorem gaussian_quarter_integerSum {α : ℝ} (hα : 0 < α) {x : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    setGaussian (dPlusSet 8) α x = gaussian α (1 / 4) ^ 8 +
      paritySign (∑ i, roundedInt x i) * alternatingGaussian α (1 / 4) ^ 8 := by
  have hr := (quarterGrid_iff_folded x).mp hx
  have hp := paritySign_eq_of_even_iff (quarter_parities_equiv hx hs)
  rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα, dPlusGaussian_signed_fold hα]
  have hA : foldedAProduct α x = gaussian α (1 / 4) ^ 8 := by simp [foldedAProduct, hr]
  have hC : foldedCProduct α x = gaussian α (1 / 4) ^ 8 := by
    have he : (1 / 4 : ℝ) - 1 / 2 = -(1 / 4 : ℝ) := by ring
    simp only [foldedCProduct, hr, he, gaussian_even, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hB : foldedBProduct α x = alternatingGaussian α (1 / 4) ^ 8 := by simp [foldedBProduct, hr]
  have hD : foldedDProduct α x = alternatingGaussian α (1 / 4) ^ 8 := by
    have he : (1 / 4 : ℝ) - 1 / 2 = -(1 / 4 : ℝ) := by ring
    simp only [foldedDProduct, hr, he, alternatingGaussian_even, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hA, hB, hC, hD, ← hp]
  ring

theorem quarter_unit_profile_product {α : ℝ} (hα : 0 < α) {x : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    setGaussian (dPlusSet 8) α (x + e8FirstVector) * setGaussian (dPlusSet 8) α x =
      gaussian α (1 / 4) ^ 16 - alternatingGaussian α (1 / 4) ^ 16 := by
  have hg : -e8FirstVector ∈ bwMSet := bwMSet_neg e8FirstVector_mem_bwM
  have hx' : QuarterGrid8 (x + e8FirstVector) := by
    simpa only [sub_neg_eq_add] using quarterGrid_sub_bwM hx hg
  have hs' : IntegerSum8 (x + e8FirstVector) := by
    simpa only [sub_neg_eq_add] using integerSum_sub hs (bwM_integerSum hg)
  rw [gaussian_quarter_integerSum hα hx' hs', gaussian_quarter_integerSum hα hx hs]
  have hsum : (∑ i, roundedInt (x + e8FirstVector) i) = (∑ i, roundedInt x i) + 1 := by
    rw [e8FirstVector_eq_intVec, roundedInt_add_intVec]
    simp [Finset.sum_add_distrib, sum_bitUnit]
  rw [hsum, paritySign_add_one]
  have hp := paritySign_sq (∑ i, roundedInt x i)
  calc
    _ = gaussian α (1 / 4) ^ 16 - paritySign (∑ i, roundedInt x i) ^ 2 *
        alternatingGaussian α (1 / 4) ^ 16 := by ring
    _ = _ := by rw [hp, one_mul]

/-- Equation (28), exactly in its printed scalar notation. -/
theorem bwGammaMinimum_eq_quarter {α : ℝ} (hα : 0 < α) :
    bwGammaMinimum α = 16 * (gaussian α (1 / 4) ^ 16 - alternatingGaussian α (1 / 4) ^ 16) := by
  rw [← setGaussian_bwGamma_witness hα, setGaussian_bwGamma_eq_sum_profiles hα]
  have hq (q : BWQuotient) :
      bwThetaProfile α (bwQuarterPoint + e8FirstVector) q * bwThetaProfile α bwQuarterPoint q =
      gaussian α (1 / 4) ^ 16 - alternatingGaussian α (1 / 4) ^ 16 := by
    have hg := bwRepresentative_mem q
    have h := quarter_unit_profile_product hα (quarterGrid_sub_bwM bwQuarterPoint_quarterGrid hg)
      (integerSum_sub bwQuarterPoint_integerSum (bwM_integerSum hg))
    have heq : bwQuarterPoint - bwRepresentative q + e8FirstVector =
        bwQuarterPoint + e8FirstVector - bwRepresentative q := by abel
    simpa only [bwThetaProfile, heq] using h
  simp only [hq, Finset.sum_const, Finset.card_univ, card_bwQuotient, nsmul_eq_mul, Nat.cast_ofNat]

/-- The paper's attained minimum in the usual BW16 normalization. -/
theorem bw16_gaussian_minimum_literal {α : ℝ} (hα : 0 < α) :
    (∀ z : Fin 16 → ℝ,
      16 * (gaussian (2 * α) (1 / 4) ^ 16 - alternatingGaussian (2 * α) (1 / 4) ^ 16) ≤
        setGaussian bw16Set α z) ∧
      ∃ z, setGaussian bw16Set α z =
        16 * (gaussian (2 * α) (1 / 4) ^ 16 - alternatingGaussian (2 * α) (1 / 4) ^ 16) := by
  simpa only [bwGammaMinimum_eq_quarter (by positivity : 0 < 2 * α)] using bw16_gaussian_minimum hα

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwGammaMinimum_eq_quarter
#print axioms PaperVerification.ColdSpots.bw16_gaussian_minimum_literal
#print axioms PaperVerification.ColdSpots.alternatingGaussian_eq_literal
end
end Source_BWThetaFormula
-- END ORIGINAL PaperVerification.BWThetaFormula


-- BEGIN ORIGINAL PaperVerification.BWCharacterCode
section Source_BWCharacterCode

-- original header: module

-- original header: public import PaperVerification.BWCode
-- original header: public import Mathlib.Tactic.SimpRw

-- original header: @[expose] public section

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
end Source_BWCharacterCode
-- END ORIGINAL PaperVerification.BWCharacterCode


-- BEGIN ORIGINAL PaperVerification.BWQuotientGroup
section Source_BWQuotientGroup

-- original header: module

-- original header: public import PaperVerification.BWCharacterCode
-- original header: public import PaperVerification.BWEligibility

-- original header: @[expose] public section

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
end
end Source_BWQuotientGroup
-- END ORIGINAL PaperVerification.BWQuotientGroup


-- BEGIN ORIGINAL PaperVerification.BWCanonical
section Source_BWCanonical

-- original header: module

-- original header: public import PaperVerification.BWQuotientGroup
-- original header: public import PaperVerification.BWHoles


-- original header: @[expose] public section
/-! # Actual representatives of the fifteen eligible M-hole classes

The binary characters below describe exact distances from real points to the
sixteen E8 cosets.  This supplies the geometric bridge needed before counting
Barnes–Wall deep holes modulo translation.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def bwCanonicalHole (χ : BWCharacter) : Fin 8 → ℝ :=
  if χ.val.2 = 0 then halfWord (pairWord χ.val.1)
  else bwQuarterPoint - halfWord (pairWord χ.val.1)

def bwNearFar (b : Binary) : ℝ := if b = 0 then 1 / 2 else 1

theorem bwNearFar_ge (b : Binary) : (1 / 2 : ℝ) ≤ bwNearFar b := by
  unfold bwNearFar
  split_ifs <;> norm_num

theorem bwNearFar_eq_one_iff (b : Binary) : bwNearFar b = 1 ↔ b = 1 := by
  rcases binary_eq_zero_or_one b with h | h <;> norm_num [bwNearFar, h]

theorem bwNearFar_eq_half_iff (b : Binary) : bwNearFar b = 1 / 2 ↔ b = 0 := by
  rcases binary_eq_zero_or_one b with h | h <;> norm_num [bwNearFar, h]

theorem quarter_depth_by_parity {x : Fin 8 → ℝ} (hx : QuarterGrid8 x)
    (hs : IntegerSum8 x) :
    squaredDepth (dPlusSet 8) x = if Even (∑ i, roundedInt x i) then 1 / 2 else 1 := by
  have hp := quarter_parities_equiv hx hs
  have hd := squaredDepth_dPlus_of_constant x 0 (1 / 4) ((quarterGrid_iff_folded x).mp hx)
  by_cases he : Even (∑ i, roundedInt x i)
  · norm_num [he, hp.mp he] at hd ⊢
    exact hd
  · have he' : ¬Even (∑ i, halfRoundedInt x i) := fun h => he (hp.mpr h)
    norm_num [he, he'] at hd ⊢
    exact hd

theorem round_quarter_sub_binary (a b : Binary) :
    round (1 / 4 - (a.val : ℝ) / 2 - (b.val : ℝ) / 2) = -binaryCarry a b := by
  rcases binary_eq_zero_or_one a with ha | ha <;>
    rcases binary_eq_zero_or_one b with hb | hb
  all_goals
    rw [ha, hb]
    simp only [binary_one_val, ZMod.val_zero, Nat.cast_one, Nat.cast_zero]
    norm_num [binaryCarry, round_eq_iff]

theorem roundedInt_quarter_sub_words (c d : BinaryWord8) :
    roundedInt (bwQuarterPoint - halfWord c - halfWord d) =
      fun i => -binaryCarry (c i) (d i) := by
  funext i
  exact round_quarter_sub_binary (c i) (d i)

theorem sum_roundedInt_quarter_pair (j : Fin 8) (q : BWQuotient) :
    (∑ i, roundedInt (bwQuarterPoint - halfWord (pairWord j) - bwRepresentative q) i) =
      -((linearWord3 q.1 j).val : ℤ) - (q.2.val : ℤ) := by
  have heq : bwQuarterPoint - halfWord (pairWord j) - bwRepresentative q =
      (bwQuarterPoint - halfWord (pairWord j) - halfWord (linearWord3 q.1)) +
        intVec (-bitUnit q.2) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, bwRepresentative, intVec, Int.cast_neg]
    ring
  rw [heq, roundedInt_add_intVec, roundedInt_quarter_sub_words]
  simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    sum_bitUnit, binaryCarry, pairWord_linear_intersection]
  ring

theorem quarter_pair_grid (j : Fin 8) :
    QuarterGrid8 (bwQuarterPoint - halfWord (pairWord j)) := by
  intro i
  refine ⟨-((pairWord j i).val : ℤ), ?_⟩
  simp only [Pi.sub_apply, bwQuarterPoint, halfWord, Int.cast_neg, Int.cast_natCast]
  ring

theorem quarter_pair_integerSum (j : Fin 8) :
    IntegerSum8 (bwQuarterPoint - halfWord (pairWord j)) := by
  obtain ⟨k, hk⟩ := pairWord_even j
  refine ⟨2 - (k : ℤ), ?_⟩
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, bwQuarterPoint, halfWord,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_binary_val, hk]
  push_cast
  ring

theorem canonical_quarter_profile (j : Fin 8) (q : BWQuotient) :
    bwDepthProfile (bwQuarterPoint - halfWord (pairWord j)) q =
      bwNearFar (linearWord3 q.1 j + q.2) := by
  unfold bwDepthProfile
  rw [quarter_depth_by_parity
    (quarterGrid_sub_bwM (quarter_pair_grid j) (bwRepresentative_mem q))
    (integerSum_sub (quarter_pair_integerSum j) (bwM_integerSum (bwRepresentative_mem q))),
    sum_roundedInt_quarter_pair]
  have he : Even (-((linearWord3 q.1 j).val : ℤ) - (q.2.val : ℤ)) ↔
      linearWord3 q.1 j + q.2 = 0 := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simp only [Int.cast_sub, Int.cast_neg, binary_val_cast]
    rw [sub_eq_add_neg, ← neg_add, neg_eq_zero]
  simp only [he, bwNearFar]

theorem canonical_half_profile (j : Fin 8) (hj : j ≠ 0) (q : BWQuotient) :
    bwDepthProfile (halfWord (pairWord j)) q = bwNearFar (linearWord3 q.1 j) := by
  obtain ⟨m, hm⟩ := halfWord_sub_representation (pairWord j) (linearWord3 q.1)
  have heq : halfWord (pairWord j) - bwRepresentative q =
      intVec (m - bitUnit q.2) + halfWord (fun i => pairWord j i - linearWord3 q.1 i) := by
    unfold bwRepresentative
    rw [sub_add_eq_sub_sub, hm]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, intVec, Int.cast_sub]
    ring
  have hw := pairWord_linear_difference_weights j hj q.1
  unfold bwDepthProfile
  rw [heq]
  rcases binary_eq_zero_or_one (linearWord3 q.1 j) with h | h
  · rcases hw.1 h with hwt | hwt
    all_goals
      rw [halfWord_depth _ _ (by rw [hwt]; norm_num) (by rw [hwt]; norm_num)]
      norm_num [hwt, bwNearFar, h]
  · have hwt := hw.2 h
    rw [halfWord_depth _ _ (by rw [hwt]; norm_num) (by rw [hwt]; norm_num)]
    norm_num [hwt, bwNearFar, h]

/-- Every entry is an exact nearest-coset squared distance. -/
theorem bwCanonicalHole_profile (χ : BWCharacter) (q : BWQuotient) :
    bwDepthProfile (bwCanonicalHole χ) q = bwNearFar (bwCharacterEval χ q) := by
  rcases binary_eq_zero_or_one χ.val.2 with h | h
  · have hj : χ.val.1 ≠ 0 := by
      intro hj
      exact χ.property (Prod.ext hj h)
    simpa only [bwCanonicalHole, h, if_pos rfl, ite_true, bwCharacterEval,
      zero_mul, add_zero] using
      canonical_half_profile χ.val.1 hj q
  · simpa only [bwCanonicalHole, h, one_ne_zero, if_false, bwCharacterEval, one_mul] using
      canonical_quarter_profile χ.val.1 q

theorem bwCanonicalHole_eligible (χ : BWCharacter) : BWEligible (bwCanonicalHole χ) := by
  constructor
  · apply le_antisymm (squaredDepth_bwM_le _)
    obtain ⟨q, hq, _⟩ := exists_min_bwDepthProfile (bwCanonicalHole χ)
    rw [← hq, bwCanonicalHole_profile]
    exact bwNearFar_ge _
  · obtain ⟨q, hq⟩ := bwCharacter_nonzero χ
    refine ⟨q, ?_⟩
    rw [bwCanonicalHole_profile, hq]
    norm_num [bwNearFar]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwCanonicalHole_profile
#print axioms PaperVerification.ColdSpots.bwCanonicalHole_eligible
end
end Source_BWCanonical
-- END ORIGINAL PaperVerification.BWCanonical


-- BEGIN ORIGINAL PaperVerification.BWEligibleClasses
section Source_BWEligibleClasses

-- original header: module

-- original header: public import PaperVerification.BWCanonical


-- original header: @[expose] public section
/-! # Exact classification modulo M of every eligible real point

All coordinates and translations in this file are real vectors in the displayed
Reed–Muller lattice.  The finite binary quotient is used only after proving its
connection to these vectors in both directions.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem halfWord_sub_mem_bwM_iff (c d : BinaryWord8) :
    halfWord c - halfWord d ∈ bwMSet ↔ InRM3 (fun i => c i - d i) := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have hi (i : Fin 8) : w i = ((c i).val : ℤ) - (d i).val := by
      have h := congrFun heq i
      change ((c i).val : ℝ) / 2 - ((d i).val : ℝ) / 2 = (w i : ℝ) / 2 at h
      exact_mod_cast (show (w i : ℝ) = ((c i).val : ℝ) - ((d i).val : ℝ) by linarith)
    convert hw using 1
    funext i
    rw [hi i]
    simp only [Int.cast_sub, binary_val_cast]
  · intro hc
    obtain ⟨m, hm⟩ := halfWord_sub_representation c d
    rw [hm]
    exact bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM hc)

theorem quarterGrid_integer_normalForm {x : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    ∃ m : Fin 8 → ℤ, ∃ c : BinaryWord8, Even (binaryWeight c) ∧
      x = intVec m + bwQuarterPoint - halfWord c := by
  choose w hw using hx
  let c : BinaryWord8 := fun i => (w i : Binary)
  let m : Fin 8 → ℤ := fun i => (w i + (c i).val) / 2
  have hi (i : Fin 8) : 2 * m i = w i + (c i).val := by
    apply Int.mul_ediv_cancel'
    apply even_iff_two_dvd.mp
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_add, binary_val_cast, c]
    exact (show ∀ a : Binary, a + a = 0 by decide) _
  have heq : x = intVec m + bwQuarterPoint - halfWord c := by
    funext i
    change x i = (m i : ℝ) + 1 / 4 - ((c i).val : ℝ) / 2
    have h : 2 * (m i : ℝ) = (w i : ℝ) + ((c i).val : ℝ) := by exact_mod_cast hi i
    rw [hw i]
    linarith
  obtain ⟨k, hk⟩ := hs
  have hsum : (k : ℝ) = ((∑ i, m i : ℤ) : ℝ) + 2 - (binaryWeight c : ℝ) / 2 := by
    rw [← hk, heq]
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      intVec, bwQuarterPoint, halfWord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Int.cast_sum, ← Finset.sum_div, ← Nat.cast_sum, sum_binary_val]
    ring
  have hcast : (binaryWeight c : ℤ) = 2 * ((∑ i, m i) + 2 - k) := by
    exact_mod_cast (show (binaryWeight c : ℝ) =
      2 * (((∑ i, m i : ℤ) : ℝ) + 2 - k) by linarith)
  have heven : Even (binaryWeight c : ℤ) := by
    rw [hcast]
    exact even_two.mul_right _
  exact ⟨m, c, (Int.even_coe_nat _).mp heven, heq⟩

theorem e8_eligible_has_canonical_class {x : Fin 8 → ℝ}
    (hx : E8FoldedHole x) (hM : squaredDepth bwMSet x = 1 / 2) :
    ∃ χ : BWCharacter, x - bwCanonicalHole χ ∈ bwMSet := by
  have hxM : x ∉ bwMSet := by
    intro hxM
    have h := squaredDepth_zero_of_mem hxM
    linarith
  rcases hx with ⟨hr, hp⟩ | ⟨hr, hp⟩ | hb | ⟨hr, hp, hq⟩
  · have heq : x = intVec (roundedInt x) := by
      funext i
      exact sub_eq_zero.mp (abs_eq_zero.mp (hr i))
    exact (hxM (heq.symm ▸ intVec_mem_bwM (roundedInt x))).elim
  · have heq : x = fun i => (halfRoundedInt x i : ℝ) + 1 / 2 := by
      funext i
      have h := abs_sub_halfRoundedInt x i
      rw [hr i, sub_self] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp h)
    have hm : x ∈ bwMSet := by
      rw [heq]
      refine ⟨fun i => 2 * halfRoundedInt x i + 1, ?_, ?_⟩
      · simpa using (inRM3_one : InRM3 (fun _ : Fin 8 => (1 : Binary)))
      · funext i
        push_cast
        ring
    exact (hxM hm).elim
  · have hgrid := (balancedHalfGrid_iff_paperHalfGrid (by decide : Even 8) x).mp hb
    obtain ⟨m, c, rfl⟩ := halfGrid_integer_halfWord hgrid.1
    have hc4 : binaryWeight c = 4 := by
      have hcount := hgrid.2
      norm_num [nonintegerCount_integer_halfWord] at hcount
      exact hcount
    have hnc : ¬InRM3 c := fun hc => hxM (bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM hc))
    obtain ⟨j, hj, _⟩ := even_word_coset_representatives c (by rw [hc4]; decide)
    have hj0 : j ≠ 0 := by
      intro h
      apply hnc
      simpa only [h, pairWord_zero, Pi.zero_apply, sub_zero] using hj
    let χ : BWCharacter := ⟨(j, 0), fun h => hj0 (congrArg Prod.fst h)⟩
    refine ⟨χ, ?_⟩
    have hm := bwMSet_add (intVec_mem_bwM m) ((halfWord_sub_mem_bwM_iff c (pairWord j)).mpr hj)
    simpa only [bwCanonicalHole, χ, if_pos rfl, ite_true, add_sub_assoc] using hm
  · obtain ⟨m, c, hc, heq⟩ := quarterGrid_integer_normalForm
      ((quarterGrid_iff_folded x).mpr hr) (quarter_integerSum_of_both_odd hr hp hq)
    obtain ⟨j, hj, _⟩ := even_word_coset_representatives c hc
    let χ : BWCharacter := ⟨(j, 1), by intro h; have := congrArg Prod.snd h; simpa using this⟩
    refine ⟨χ, ?_⟩
    have hm := bwMAddSubgroup.sub_mem (intVec_mem_bwM m)
      ((halfWord_sub_mem_bwM_iff c (pairWord j)).mpr hj)
    have he : x - bwCanonicalHole χ = intVec m - (halfWord c - halfWord (pairWord j)) := by
      rw [heq]
      simp only [bwCanonicalHole, χ, one_ne_zero, if_false]
      abel
    rw [he]
    exact hm

theorem bwEligible_has_canonical_class {x : Fin 8 → ℝ} (hx : BWEligible x) :
    ∃ χ : BWCharacter, x - bwCanonicalHole χ ∈ bwMSet := by
  obtain ⟨q, hq⟩ := hx.2
  have hh : E8FoldedHole (x - bwRepresentative q) := (squaredDepth_E8_eq_one_iff _).mp hq
  have hM : squaredDepth bwMSet (x - bwRepresentative q) = 1 / 2 := by
    change squaredDepth (bwMAddSubgroup : Set (Fin 8 → ℝ))
      (x - bwRepresentative q) = 1 / 2
    rw [squaredDepth_sub_of_subgroup bwMAddSubgroup _ _ (bwRepresentative_mem q)]
    exact hx.1
  obtain ⟨χ, hχ⟩ := e8_eligible_has_canonical_class hh hM
  refine ⟨χ, ?_⟩
  have h := bwMSet_add hχ (bwRepresentative_mem q)
  convert h using 1 <;> abel

theorem halfIntegerGrid_sub {x y : Fin 8 → ℝ}
    (hx : HalfIntegerGrid x) (hy : HalfIntegerGrid y) : HalfIntegerGrid (x - y) := by
  intro i
  obtain ⟨m, hm⟩ := hx i
  obtain ⟨n, hn⟩ := hy i
  refine ⟨m - n, ?_⟩
  simp only [Pi.sub_apply, hm, hn, Int.cast_sub]
  ring

theorem halfWord_halfIntegerGrid (c : BinaryWord8) : HalfIntegerGrid (halfWord c) := by
  intro i
  exact ⟨((c i).val : ℤ), by simp only [halfWord, Int.cast_natCast]⟩

theorem bwM_halfIntegerGrid {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) : HalfIntegerGrid x := by
  rcases hx with ⟨w, hw, rfl⟩
  exact fun i => ⟨w i, rfl⟩

theorem quarterGrid_not_halfIntegerGrid {x : Fin 8 → ℝ} (hx : QuarterGrid8 x) :
    ¬HalfIntegerGrid x := by
  intro h
  obtain ⟨m, hm⟩ := hx 0
  obtain ⟨n, hn⟩ := h 0
  have hr : 2 * (n : ℝ) = 2 * (m : ℝ) + 1 := by linarith
  have hi : 2 * n = 2 * m + 1 := by exact_mod_cast hr
  omega

/-- Distinct nonzero characters give different actual translation classes. -/
theorem bwCanonicalHole_sub_mem_iff (χ ψ : BWCharacter) :
    bwCanonicalHole χ - bwCanonicalHole ψ ∈ bwMSet ↔ χ = ψ := by
  constructor
  · intro h
    rcases binary_eq_zero_or_one χ.val.2 with hc | hc <;>
      rcases binary_eq_zero_or_one ψ.val.2 with hp | hp
    · have hm : halfWord (pairWord χ.val.1) - halfWord (pairWord ψ.val.1) ∈ bwMSet := by
        simpa only [bwCanonicalHole, hc, hp, if_pos rfl, ite_true] using h
      have hj := (pairWord_coset_distinct _ _).mp ((halfWord_sub_mem_bwM_iff _ _).mp hm)
      apply Subtype.ext
      exact Prod.ext hj (hc.trans hp.symm)
    · have hm : halfWord (pairWord χ.val.1) -
          (bwQuarterPoint - halfWord (pairWord ψ.val.1)) ∈ bwMSet := by
        simpa only [bwCanonicalHole, hc, hp, if_pos rfl, ite_true, one_ne_zero, if_false] using h
      have hg := halfIntegerGrid_sub (halfWord_halfIntegerGrid (pairWord χ.val.1))
        (bwM_halfIntegerGrid hm)
      have he : halfWord (pairWord χ.val.1) - (halfWord (pairWord χ.val.1) -
          (bwQuarterPoint - halfWord (pairWord ψ.val.1))) =
          bwQuarterPoint - halfWord (pairWord ψ.val.1) := by abel
      rw [he] at hg
      exact (quarterGrid_not_halfIntegerGrid (quarter_pair_grid _) hg).elim
    · have hm : halfWord (pairWord ψ.val.1) -
          (bwQuarterPoint - halfWord (pairWord χ.val.1)) ∈ bwMSet := by
        have hh := bwMSet_neg h
        simpa only [bwCanonicalHole, hc, hp, if_pos rfl, ite_true, one_ne_zero, if_false,
          neg_sub] using hh
      have hg := halfIntegerGrid_sub (halfWord_halfIntegerGrid (pairWord ψ.val.1))
        (bwM_halfIntegerGrid hm)
      have he : halfWord (pairWord ψ.val.1) - (halfWord (pairWord ψ.val.1) -
          (bwQuarterPoint - halfWord (pairWord χ.val.1))) =
          bwQuarterPoint - halfWord (pairWord χ.val.1) := by abel
      rw [he] at hg
      exact (quarterGrid_not_halfIntegerGrid (quarter_pair_grid _) hg).elim
    · have hm : halfWord (pairWord ψ.val.1) - halfWord (pairWord χ.val.1) ∈ bwMSet := by
        have he : bwCanonicalHole χ - bwCanonicalHole ψ =
            halfWord (pairWord ψ.val.1) - halfWord (pairWord χ.val.1) := by
          simp only [bwCanonicalHole, hc, hp, one_ne_zero, if_false]
          abel
        rwa [he] at h
      have hj := (pairWord_coset_distinct _ _).mp ((halfWord_sub_mem_bwM_iff _ _).mp hm)
      apply Subtype.ext
      exact Prod.ext hj.symm (hc.trans hp.symm)
  · rintro rfl
    simpa only [sub_self] using bwMSet_zero

theorem bwEligible_unique_canonical_class {x : Fin 8 → ℝ} (hx : BWEligible x) :
    ∃! χ : BWCharacter, x - bwCanonicalHole χ ∈ bwMSet := by
  obtain ⟨χ, hχ⟩ := bwEligible_has_canonical_class hx
  refine ⟨χ, hχ, ?_⟩
  intro ψ hψ
  apply (bwCanonicalHole_sub_mem_iff ψ χ).mp
  have h := bwMAddSubgroup.sub_mem hχ hψ
  change (x - bwCanonicalHole χ) - (x - bwCanonicalHole ψ) ∈ bwMSet at h
  convert h using 1 <;> abel

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwEligible_unique_canonical_class
end
end Source_BWEligibleClasses
-- END ORIGINAL PaperVerification.BWEligibleClasses


-- BEGIN ORIGINAL PaperVerification.LatticeTranslationClasses
section Source_LatticeTranslationClasses

-- original header: module

-- original header: public import PaperVerification.LatticeTranslations
-- original header: public import Mathlib.GroupTheory.QuotientGroup.Basic
-- original header: public import Mathlib.SetTheory.Cardinal.Finite


-- original header: @[expose] public section
/-! # Translation classes of actual deep holes

The quotient is taken in the ambient real additive group by the actual lattice
subgroup, and then restricted to classes containing a deepest point.
-/

noncomputable section

namespace PaperVerification.ColdSpots

def DeepTranslationClasses {n : ℕ} (L : AddSubgroup (Fin n → ℝ)) :=
  {C : (Fin n → ℝ) ⧸ L // ∃ x : Fin n → ℝ, IsDeepHole (L : Set _) x ∧
    (x : (Fin n → ℝ) ⧸ L) = C}

end PaperVerification.ColdSpots
end
end Source_LatticeTranslationClasses
-- END ORIGINAL PaperVerification.LatticeTranslationClasses


-- BEGIN ORIGINAL PaperVerification.BWTranslationClasses
section Source_BWTranslationClasses

-- original header: module

-- original header: public import PaperVerification.BWEligibleClasses
-- original header: public import PaperVerification.BWConstruction
-- original header: public import PaperVerification.BWNormalized
-- original header: public import PaperVerification.BWNorm
-- original header: public import PaperVerification.LatticeTranslationClasses
-- original header: public import Mathlib.GroupTheory.QuotientGroup.Basic
-- original header: public import Mathlib.SetTheory.Cardinal.Finite


-- original header: @[expose] public section
/-! # The exact 120 Barnes–Wall translation classes

This file constructs the quotient of actual deep holes by actual lattice
translations and proves its equivalence with 120 explicit character/phase
indices.  Both completeness and distinctness are proved in real coordinates.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem bwGamma_mem_iff (z : Fin 16 → ℝ) :
    z ∈ bwGammaSet ↔ bwLeft z ∈ bwMSet ∧ bwRight z ∈ bwMSet ∧
      bwLeft z - bwRight z ∈ dPlusSet 8 := by
  simpa only [append_bw_blocks] using bwGamma_append_iff (bwLeft z) (bwRight z)

def bwGammaAddSubgroup : AddSubgroup (Fin 16 → ℝ) where
  carrier := bwGammaSet
  zero_mem' := by
    apply (bwGamma_mem_iff 0).mpr
    have hleft : bwLeft (0 : Fin 16 → ℝ) = 0 := by
      funext i
      rfl
    have hright : bwRight (0 : Fin 16 → ℝ) = 0 := by
      funext i
      rfl
    rw [hleft, hright, sub_self]
    exact
      (show (0 : Fin 8 → ℝ) ∈ bwMSet ∧ (0 : Fin 8 → ℝ) ∈ bwMSet ∧
        (0 : Fin 8 → ℝ) ∈ dPlusSet 8 from ⟨bwMSet_zero, bwMSet_zero, zero_mem_dPlusSet 8⟩)
  add_mem' := by
    intro z w hz hw
    obtain ⟨hz₁, hz₂, hz₃⟩ := (bwGamma_mem_iff z).mp hz
    obtain ⟨hw₁, hw₂, hw₃⟩ := (bwGamma_mem_iff w).mp hw
    apply (bwGamma_mem_iff (z + w)).mpr
    refine ⟨bwMSet_add hz₁ hw₁, bwMSet_add hz₂ hw₂, ?_⟩
    have he : bwLeft (z + w) - bwRight (z + w) =
        (bwLeft z - bwRight z) + (bwLeft w - bwRight w) := by
      funext i
      simp only [bwLeft, bwRight, Pi.add_apply, Pi.sub_apply]
      ring
    rw [he]
    exact dPlusSet_add (by decide : Even 8) hz₃ hw₃
  neg_mem' := by
    intro z hz
    obtain ⟨hz₁, hz₂, hz₃⟩ := (bwGamma_mem_iff z).mp hz
    apply (bwGamma_mem_iff (-z)).mpr
    refine ⟨bwMSet_neg hz₁, bwMSet_neg hz₂, ?_⟩
    have he : bwLeft (-z) - bwRight (-z) = -(bwLeft z - bwRight z) := by
      funext i
      simp only [bwLeft, bwRight, Pi.neg_apply, Pi.sub_apply]
      ring
    rw [he]
    exact dPlusSet_neg (by decide : Even 8) hz₃

theorem bwCanonical_pair_gluing_iff (χ ψ : BWCharacter) (q : BWQuotient) :
    BWGluingCondition (bwCanonicalHole χ) (bwCanonicalHole ψ + bwRepresentative q) ↔
      χ = ψ ∧ bwCharacterEval χ q = 1 := by
  have hχ := (bwCanonicalHole_eligible χ).1
  have hψ : squaredDepth bwMSet (bwCanonicalHole ψ + bwRepresentative q) = 1 / 2 := by
    change squaredDepth (bwMAddSubgroup : Set (Fin 8 → ℝ))
      (bwCanonicalHole ψ + bwRepresentative q) = 1 / 2
    rw [squaredDepth_add_of_subgroup bwMAddSubgroup _ _ (bwRepresentative_mem q)]
    exact (bwCanonicalHole_eligible ψ).1
  have hlocal (r : BWQuotient) :
      (bwDepthProfile (bwCanonicalHole χ) r = 1 ∨
        bwDepthProfile (bwCanonicalHole ψ + bwRepresentative q) r = 1) ↔
      (bwCharacterEval χ r ≠ 0 ∨ bwCharacterEval ψ r ≠ bwCharacterEval ψ q) := by
    rw [bwCanonicalHole_profile, bwDepthProfile_translate_representative,
      bwCanonicalHole_profile, bwNearFar_eq_one_iff, bwNearFar_eq_one_iff,
      bwCharacterEval_sub]
    exact (show ∀ a b c : Binary, (a = 1 ∨ b - c = 1) ↔ (a ≠ 0 ∨ b ≠ c) by decide) _ _ _
  unfold BWGluingCondition
  rw [hχ, hψ]
  simp only [true_and]
  simp_rw [hlocal]
  rw [bwCharacter_complement_iff]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (binary_eq_zero_or_one _).resolve_left (Ne.symm h)⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by simpa [h]⟩

theorem bwCanonical_pair_depth_iff (χ ψ : BWCharacter) (q : BWQuotient) :
    squaredDepth bwGammaSet (Fin.append (bwCanonicalHole χ)
      (bwCanonicalHole ψ + bwRepresentative q)) = 3 / 2 ↔
        χ = ψ ∧ bwCharacterEval χ q = 1 := by
  rw [squaredDepth_bwGamma_eq_iff, bwCanonical_pair_gluing_iff]

def bwCanonicalDeepHole (p : BWHoleIndex) : Fin 16 → ℝ :=
  Fin.append (bwCanonicalHole p.val.1) (bwCanonicalHole p.val.1 + bwRepresentative p.val.2)

theorem bwCanonicalDeepHole_deep (p : BWHoleIndex) : IsDeepHole bwGammaSet (bwCanonicalDeepHole p) := by
  apply (isDeepHole_bwGamma_iff_depth _).mpr
  exact (bwCanonical_pair_depth_iff _ _ _).mpr ⟨rfl, p.property⟩

/-- Every real deep hole belongs to one of the displayed 120 actual cosets. -/
theorem bwDeepHole_coset_coverage {z : Fin 16 → ℝ} (hz : IsDeepHole bwGammaSet z) :
    ∃ p : BWHoleIndex, z - bwCanonicalDeepHole p ∈ bwGammaSet := by
  let x := bwLeft z
  let y := bwRight z
  have hd : squaredDepth bwGammaSet (Fin.append x y) = 3 / 2 := by
    simpa only [x, y, append_bw_blocks] using (isDeepHole_bwGamma_iff_depth z).mp hz
  obtain ⟨hx, hy⟩ := bwGamma_deep_eligible hd
  obtain ⟨χ, hχ⟩ := bwEligible_has_canonical_class hx
  obtain ⟨ψ, hψ⟩ := bwEligible_has_canonical_class hy
  let s := x - bwCanonicalHole χ
  let t := y - bwCanonicalHole ψ
  obtain ⟨q, l, hl, hq⟩ := bw_coset_coverage (bwMAddSubgroup.sub_mem hψ hχ)
  let z₀ := Fin.append (bwCanonicalHole χ) (bwCanonicalHole ψ + bwRepresentative q)
  have htranslate : z - z₀ ∈ bwGammaSet := by
    apply (bwGamma_mem_iff _).mpr
    have hleft : bwLeft (z - z₀) = s := by
      funext i
      simp only [bwLeft, z₀, s, x, Pi.sub_apply, Fin.append_left]
    have hright : bwRight (z - z₀) = t - bwRepresentative q := by
      funext i
      simp only [bwRight, z₀, t, y, Pi.sub_apply, Pi.add_apply, Fin.append_right]
      ring
    rw [hleft, hright]
    refine ⟨hχ, bwMAddSubgroup.sub_mem hψ (bwRepresentative_mem q), ?_⟩
    have he : s - (t - bwRepresentative q) = -l := by
      change t - s = l + bwRepresentative q at hq
      rw [show s - (t - bwRepresentative q) = -(t - s) + bwRepresentative q by abel, hq]
      abel
    rw [he]
    exact dPlusSet_neg (by decide : Even 8) hl
  have hd₀ : squaredDepth bwGammaSet z₀ = 3 / 2 := by
    have h := squaredDepth_sub_of_subgroup bwGammaAddSubgroup z (z - z₀) htranslate
    rw [sub_sub_cancel] at h
    exact h.trans ((isDeepHole_bwGamma_iff_depth z).mp hz)
  obtain ⟨heq, hphase⟩ := (bwCanonical_pair_depth_iff χ ψ q).mp hd₀
  subst ψ
  exact ⟨⟨(χ, q), hphase⟩, htranslate⟩

/-- No two of the 120 representatives differ by a lattice vector. -/
theorem bwCanonicalDeepHole_distinct (p r : BWHoleIndex) :
    bwCanonicalDeepHole p - bwCanonicalDeepHole r ∈ bwGammaSet ↔ p = r := by
  constructor
  · intro h
    obtain ⟨hleft, _, hdiff⟩ := (bwGamma_mem_iff _).mp h
    have hc : p.val.1 = r.val.1 := by
      apply (bwCanonicalHole_sub_mem_iff _ _).mp
      have he : bwLeft (bwCanonicalDeepHole p - bwCanonicalDeepHole r) =
          bwCanonicalHole p.val.1 - bwCanonicalHole r.val.1 := by
        funext i
        simp only [bwLeft, bwCanonicalDeepHole, Pi.sub_apply, Fin.append_left]
      simpa only [he] using hleft
    have hq : bwRepresentative r.val.2 - bwRepresentative p.val.2 ∈ dPlusSet 8 := by
      have he : bwLeft (bwCanonicalDeepHole p - bwCanonicalDeepHole r) -
          bwRight (bwCanonicalDeepHole p - bwCanonicalDeepHole r) =
          bwRepresentative r.val.2 - bwRepresentative p.val.2 := by
        funext i
        simp only [bwLeft, bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply,
          Fin.append_left, Fin.append_right, hc]
        ring
      rwa [he] at hdiff
    have hqr := bwRepresentative_mod_e8_injective hq
    exact Subtype.ext (Prod.ext hc hqr.symm)
  · rintro rfl
    rw [sub_self]
    change (0 : Fin 16 → ℝ) ∈ bwGammaAddSubgroup
    exact bwGammaAddSubgroup.zero_mem

theorem bwDeepHole_coset_iff (z : Fin 16 → ℝ) :
    IsDeepHole bwGammaSet z ↔ ∃ p : BWHoleIndex, z - bwCanonicalDeepHole p ∈ bwGammaSet := by
  constructor
  · exact bwDeepHole_coset_coverage
  · rintro ⟨p, hp⟩
    apply (isDeepHole_bwGamma_iff_depth z).mpr
    have h := squaredDepth_add_of_subgroup bwGammaAddSubgroup
      (bwCanonicalDeepHole p) (z - bwCanonicalDeepHole p) hp
    rw [add_sub_cancel] at h
    exact h.trans ((isDeepHole_bwGamma_iff_depth _).mp (bwCanonicalDeepHole_deep p))

def bwDeepClassMap (p : BWHoleIndex) : DeepTranslationClasses bwGammaAddSubgroup :=
  ⟨(bwCanonicalDeepHole p : (Fin 16 → ℝ) ⧸ bwGammaAddSubgroup),
    bwCanonicalDeepHole p, bwCanonicalDeepHole_deep p, rfl⟩

theorem bwDeepClassMap_bijective : Function.Bijective bwDeepClassMap := by
  constructor
  · intro p r h
    apply (bwCanonicalDeepHole_distinct p r).mp
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, z, hz, hC⟩
    obtain ⟨p, hp⟩ := bwDeepHole_coset_coverage hz
    refine ⟨p, Subtype.ext ?_⟩
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hp).symm.trans hC

def bwDeepClassEquiv : BWHoleIndex ≃ DeepTranslationClasses bwGammaAddSubgroup :=
  Equiv.ofBijective bwDeepClassMap bwDeepClassMap_bijective

/-- Exactly 120 translation classes, in the actual unscaled lattice quotient. -/
theorem bwGamma_deep_translation_class_count :
    Nat.card (DeepTranslationClasses bwGammaAddSubgroup) = 120 := by
  rw [← Nat.card_congr bwDeepClassEquiv, Nat.card_eq_fintype_card, card_bwHoleIndex]

def scaleVecAddHom {n : ℕ} (c : ℝ) : (Fin n → ℝ) →+ (Fin n → ℝ) where
  toFun := scaleVec c
  map_zero' := by funext i; simp [scaleVec]
  map_add' := by intro x y; funext i; simp [scaleVec, mul_add]

def bw16AddSubgroup : AddSubgroup (Fin 16 → ℝ) :=
  bwGammaAddSubgroup.map (scaleVecAddHom (Real.sqrt 2))

theorem bw16AddSubgroup_coe : (bw16AddSubgroup : Set (Fin 16 → ℝ)) = bw16Set := by
  rw [bw16Set_eq_scaledGamma]
  rfl

theorem scaled_difference_mem_bw16 (x y : Fin 16 → ℝ) :
    scaleVec (Real.sqrt 2) x - scaleVec (Real.sqrt 2) y ∈ bw16Set ↔ x - y ∈ bwGammaSet := by
  rw [bw16Set_eq_scaledGamma]
  have he : scaleVec (Real.sqrt 2) x - scaleVec (Real.sqrt 2) y =
      scaleVec (Real.sqrt 2) (x - y) := by
    funext i
    simp only [scaleVec, Pi.sub_apply, mul_sub]
  rw [he]
  constructor
  · rintro ⟨z, hz, h⟩
    exact scaleVec_injective (Real.sqrt 2) sqrt_two_ne_zero h ▸ hz
  · intro h
    exact ⟨x - y, h, rfl⟩

def bw16CanonicalDeepHole (p : BWHoleIndex) : Fin 16 → ℝ :=
  scaleVec (Real.sqrt 2) (bwCanonicalDeepHole p)

theorem bw16CanonicalDeepHole_deep (p : BWHoleIndex) :
    IsDeepHole bw16Set (bw16CanonicalDeepHole p) := by
  rw [bw16Set_eq_scaledGamma]
  exact (isDeepHole_scaled_iff (Real.sqrt 2) sqrt_two_ne_zero bwGammaSet bwGamma_nonempty _).mpr
    (bwCanonicalDeepHole_deep p)

theorem bw16DeepHole_coset_coverage {z : Fin 16 → ℝ} (hz : IsDeepHole bw16Set z) :
    ∃ p : BWHoleIndex, z - bw16CanonicalDeepHole p ∈ bw16Set := by
  let y := scaleVec (Real.sqrt 2)⁻¹ z
  have he : scaleVec (Real.sqrt 2) y = z := scaleVec_inv (Real.sqrt 2) sqrt_two_ne_zero z
  have hy : IsDeepHole bwGammaSet y := by
    apply (isDeepHole_scaled_iff (Real.sqrt 2) sqrt_two_ne_zero bwGammaSet bwGamma_nonempty y).mp
    rw [he, ← bw16Set_eq_scaledGamma]
    exact hz
  obtain ⟨p, hp⟩ := bwDeepHole_coset_coverage hy
  refine ⟨p, ?_⟩
  rw [← he]
  exact (scaled_difference_mem_bw16 y (bwCanonicalDeepHole p)).mpr hp

theorem bw16CanonicalDeepHole_distinct (p r : BWHoleIndex) :
    bw16CanonicalDeepHole p - bw16CanonicalDeepHole r ∈ bw16Set ↔ p = r := by
  rw [bw16CanonicalDeepHole, bw16CanonicalDeepHole, scaled_difference_mem_bw16,
    bwCanonicalDeepHole_distinct]

def bw16DeepClassMap (p : BWHoleIndex) : DeepTranslationClasses bw16AddSubgroup :=
  ⟨(bw16CanonicalDeepHole p : (Fin 16 → ℝ) ⧸ bw16AddSubgroup), bw16CanonicalDeepHole p,
    by rw [bw16AddSubgroup_coe]; exact bw16CanonicalDeepHole_deep p, rfl⟩

theorem bw16DeepClassMap_bijective : Function.Bijective bw16DeepClassMap := by
  constructor
  · intro p r h
    apply (bw16CanonicalDeepHole_distinct p r).mp
    rw [← bw16AddSubgroup_coe]
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, z, hz, hC⟩
    rw [bw16AddSubgroup_coe] at hz
    obtain ⟨p, hp⟩ := bw16DeepHole_coset_coverage hz
    refine ⟨p, Subtype.ext ?_⟩
    rw [← bw16AddSubgroup_coe] at hp
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hp).symm.trans hC

def bw16DeepClassEquiv : BWHoleIndex ≃ DeepTranslationClasses bw16AddSubgroup :=
  Equiv.ofBijective bw16DeepClassMap bw16DeepClassMap_bijective

/-- The literal Barnes–Wall normalization has exactly 120 classes as well. -/
theorem bw16_deep_translation_class_count :
    Nat.card (DeepTranslationClasses bw16AddSubgroup) = 120 := by
  rw [← Nat.card_congr bw16DeepClassEquiv, Nat.card_eq_fintype_card, card_bwHoleIndex]

/-! ## The literal union over all E8 roots in §7.5 -/

/-- A root of the actual E8 lattice, with its ordinary Euclidean squared norm. -/
def IsE8Root (r : Fin 8 → ℝ) : Prop := r ∈ dPlusSet 8 ∧ sqDist r 0 = 2

/-- The integer exponent of the paper's character.  Its integrality is proved
below, so taking the floor does not alter `2 * ⟨r,g⟩` on its stated domain. -/
def bwRootExponent (r g : Fin 8 → ℝ) : ℤ := ⌊2 * ∑ i, r i * g i⌋

def bwRootCharacter (r g : Fin 8 → ℝ) : ℝ := (-1 : ℝ) ^ bwRootExponent r g

theorem bwRootCharacter_eq_of_exponent (r g : Fin 8 → ℝ) (k : ℤ)
    (hk : (k : ℝ) = 2 * ∑ i, r i * g i) :
    bwRootCharacter r g = (-1 : ℝ) ^ k := by
  simp only [bwRootCharacter, bwRootExponent, ← hk, Int.floor_intCast]

def bwRootNumerator (χ : BWCharacter) (i : Fin 8) : ℤ :=
  if χ.val.2 = 0 then 2 * ((pairWord χ.val.1 i).val : ℤ)
  else 1 - 2 * ((pairWord χ.val.1 i).val : ℤ)

private def bwRootIntegerPart (χ : BWCharacter) (i : Fin 8) : ℤ :=
  if χ.val.2 = 0 then (pairWord χ.val.1 i).val else -((pairWord χ.val.1 i).val : ℤ)

private def bwRepresentativeNumerator (q : BWQuotient) (i : Fin 8) : ℤ :=
  ((linearWord3 q.1 i).val : ℤ) + 2 * bitUnit q.2 i

private def bwCanonicalPairExponent (χ : BWCharacter) (q : BWQuotient) : ℤ :=
  (∑ i, bwRootNumerator χ i * bwRepresentativeNumerator q i) / 2

set_option maxRecDepth 65536 in
/-- Exact finite integer arithmetic, subsequently related to all real lattice
points.  These finite calculations do not replace the geometric classification. -/
private theorem bwRoot_integer_arithmetic : ∀ χ : BWCharacter,
    Even (∑ i, bwRootIntegerPart χ i) ∧ (∑ i, bwRootNumerator χ i ^ 2) = 8 ∧
    ∀ q : BWQuotient,
      (∑ i, bwRootNumerator χ i * bwRepresentativeNumerator q i) =
        2 * bwCanonicalPairExponent χ q ∧
      (bwCanonicalPairExponent χ q : Binary) = bwCharacterEval χ q := by decide

def bwCanonicalRoot (χ : BWCharacter) : Fin 8 → ℝ :=
  fun i => (bwRootNumerator χ i : ℝ) / 2

theorem bwCanonicalRoot_half (χ : BWCharacter) :
    (fun i => bwCanonicalRoot χ i / 2) = bwCanonicalHole χ := by
  funext i
  by_cases h : χ.val.2 = 0 <;>
    simp only [bwCanonicalRoot, bwRootNumerator, bwCanonicalHole, h, if_true,
      if_false, halfWord, Pi.sub_apply, bwQuarterPoint, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, Int.cast_sub, Int.cast_one] <;> ring

theorem bwCanonicalRoot_isRoot (χ : BWCharacter) : IsE8Root (bwCanonicalRoot χ) := by
  refine ⟨⟨bwRootIntegerPart χ, (bwRoot_integer_arithmetic χ).1, ?_⟩, ?_⟩
  · by_cases h : χ.val.2 = 0
    · left
      funext i
      simp [bwCanonicalRoot, bwRootNumerator, bwRootIntegerPart, intVec, h]
    · right
      funext i
      simp only [bwCanonicalRoot, bwRootNumerator, bwRootIntegerPart, h, if_false,
        Int.cast_sub, Int.cast_one, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_neg]
      ring
  · calc
      sqDist (bwCanonicalRoot χ) 0 = ((∑ i, bwRootNumerator χ i ^ 2 : ℤ) : ℝ) / 4 := by
        simp only [sqDist, Pi.zero_apply, sub_zero, bwCanonicalRoot, Int.cast_sum,
          Int.cast_pow, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 := by rw [(bwRoot_integer_arithmetic χ).2.1]; norm_num

private theorem e8_sqNorm_even {x : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) :
    ∃ k : ℤ, Even k ∧ sqDist x 0 = (k : ℝ) := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · exact ⟨∑ i, z i ^ 2, even_integer_sqSum z hz, by simp [sqDist, intVec]⟩
  · refine ⟨(∑ i, z i ^ 2) + (∑ i, z i) + 2,
      ((even_integer_sqSum z hz).add hz).add (by decide), ?_⟩
    have hi (i : Fin 8) : ((z i : ℝ) + 1 / 2) ^ 2 = (z i : ℝ) ^ 2 + z i + 1 / 4 := by ring
    simp only [sqDist, Pi.zero_apply, sub_zero, hi, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_pow,
      Int.cast_ofNat]
    ring

private theorem e8_pairing_even {x y : Fin 8 → ℝ}
    (hx : x ∈ dPlusSet 8) (hy : y ∈ dPlusSet 8) :
    ∃ k : ℤ, Even k ∧ 2 * ∑ i, x i * y i = (k : ℝ) := by
  obtain ⟨a, ha, hxa⟩ := e8_sqNorm_even hx
  obtain ⟨b, hb, hyb⟩ := e8_sqNorm_even hy
  obtain ⟨c, hc, hzc⟩ := e8_sqNorm_even (dPlusSet_sub (by decide : Even 8) hx hy)
  refine ⟨a + b - c, (ha.add hb).sub hc, ?_⟩
  have he : sqDist (x - y) 0 = sqDist x 0 + sqDist y 0 - 2 * ∑ i, x i * y i := by
    simp only [sqDist, Pi.sub_apply, Pi.zero_apply, sub_zero, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  push_cast
  linarith

set_option maxRecDepth 65536 in
private theorem bwM_pairing_even {x y : Fin 8 → ℝ}
    (hx : x ∈ bwMSet) (hy : y ∈ bwMSet) :
    ∃ k : ℤ, Even k ∧ 4 * ∑ i, x i * y i = (k : ℝ) := by
  rcases hx with ⟨u, ⟨a, ha⟩, rfl⟩
  rcases hy with ⟨v, ⟨b, hb⟩, rfl⟩
  refine ⟨∑ i, u i * v i, ?_, ?_⟩
  · apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sum, Int.cast_mul]
    have hu (i) : (u i : Binary) = affineWord3 a i := congrFun ha i
    have hv (i) : (v i : Binary) = affineWord3 b i := congrFun hb i
    simp_rw [hu, hv]
    exact (show ∀ a b : AffineCoefficients3,
      (∑ i, affineWord3 a i * affineWord3 b i) = 0 by decide) a b
  · simp only [Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Every actual E8 root half belongs to one of the fifteen classes; no
restriction to selected root representatives is made. -/
theorem e8Root_half_has_canonical_class {r : Fin 8 → ℝ} (hr : IsE8Root r) :
    ∃ χ : BWCharacter, (fun i => r i / 2) - bwCanonicalHole χ ∈ bwMSet := by
  let x : Fin 8 → ℝ := fun i => r i / 2
  change ∃ χ : BWCharacter, x - bwCanonicalHole χ ∈ bwMSet
  have hnorm : sqDist x 0 = 1 / 2 := by
    have h : sqDist x 0 = sqDist r 0 / 4 := by
      simp only [sqDist, Pi.zero_apply, sub_zero, Finset.sum_div, x]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h, hr.2]
    norm_num
  have hnot : x ∉ bwMSet := by
    intro hx
    have hmem : Fin.append x x ∈ bwGammaSet := (bwGamma_append_iff x x).mpr
      ⟨hx, hx, by simpa only [sub_self] using zero_mem_dPlusSet 8⟩
    have hd : sqDist (Fin.append x x) 0 = 1 := by
      rw [show (0 : Fin 16 → ℝ) = Fin.append (0 : Fin 8 → ℝ) (0 : Fin 8 → ℝ) by
        funext i
        refine Fin.addCases
          (motive := fun k : Fin (8 + 8) =>
            (0 : ℝ) = Fin.append (0 : Fin 8 → ℝ) (0 : Fin 8 → ℝ) k)
          (fun j : Fin 8 => ?_) (fun j : Fin 8 => ?_) i <;>
          simp only [Fin.append_left, Fin.append_right, Pi.zero_apply],
        sqDist_append, hnorm]
      norm_num
    have hne : Fin.append x x ≠ 0 := by
      intro h
      rw [h] at hd
      norm_num [sqDist] at hd
    have := bwGamma_sqNorm_lower hmem hne
    linarith
  have hsum : IntegerSum8 x := by
    obtain ⟨k, ⟨a, ha⟩, hk⟩ := e8_even_integerSum hr.1
    refine ⟨a, ?_⟩
    change (∑ i, r i / 2) = (a : ℝ)
    rw [← Finset.sum_div, hk, ha]
    push_cast
    ring
  rcases hr.1 with ⟨z, hz, he | he⟩
  · have hg : HalfIntegerGrid x := fun i => ⟨z i, by simp [x, he, intVec]⟩
    obtain ⟨m, c, hc⟩ := halfGrid_integer_halfWord hg
    obtain ⟨k, hk⟩ := hsum
    have hw : (binaryWeight c : ℤ) = 2 * (k - ∑ i, m i) := by
      have hs : (k : ℝ) = ((∑ i, m i : ℤ) : ℝ) + (binaryWeight c : ℝ) / 2 := by
        rw [← hk, hc]
        simp only [Pi.add_apply, Finset.sum_add_distrib, intVec, ← Int.cast_sum,
          sum_halfWord]
      exact_mod_cast (show (binaryWeight c : ℝ) =
        2 * ((k : ℝ) - ((∑ i, m i : ℤ) : ℝ)) by linarith)
    have heven : Even (binaryWeight c) := by
      apply (Int.even_coe_nat _).mp
      rw [hw]
      exact even_two.mul_right _
    obtain ⟨j, hj, _⟩ := even_word_coset_representatives c heven
    have hj0 : j ≠ 0 := by
      intro hj0
      apply hnot
      rw [hc]
      exact bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM (by
        simpa only [hj0, pairWord_zero, Pi.zero_apply, sub_zero] using hj))
    let χ : BWCharacter := ⟨(j, 0), fun h => hj0 (congrArg Prod.fst h)⟩
    refine ⟨χ, ?_⟩
    rw [hc]
    simpa only [bwCanonicalHole, χ, if_pos rfl, ite_true, add_sub_assoc] using
      bwMSet_add (intVec_mem_bwM m) ((halfWord_sub_mem_bwM_iff c (pairWord j)).mpr hj)
  · have hg : QuarterGrid8 x := by
      intro i
      refine ⟨z i, ?_⟩
      simp only [x, he]
      ring
    obtain ⟨m, c, hce, hc⟩ := quarterGrid_integer_normalForm hg hsum
    obtain ⟨j, hj, _⟩ := even_word_coset_representatives c hce
    let χ : BWCharacter := ⟨(j, 1), by intro h; have := congrArg Prod.snd h; simpa using this⟩
    refine ⟨χ, ?_⟩
    have h := bwMAddSubgroup.sub_mem (intVec_mem_bwM m)
      ((halfWord_sub_mem_bwM_iff c (pairWord j)).mpr hj)
    change intVec m - (halfWord c - halfWord (pairWord j)) ∈ bwMSet at h
    convert h using 1
    rw [hc]
    simp only [bwCanonicalHole, χ, one_ne_zero, if_false]
    abel

private theorem bwCanonicalRoot_pairing (χ : BWCharacter) (q : BWQuotient) :
    2 * ∑ i, bwCanonicalRoot χ i * bwRepresentative q i =
      (bwCanonicalPairExponent χ q : ℝ) := by
  have hv (i) : (bwRepresentativeNumerator q i : ℝ) = 2 * bwRepresentative q i := by
    simp only [bwRepresentativeNumerator, bwRepresentative, Pi.add_apply, halfWord,
      intVec, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  calc
    _ = ((∑ i, bwRootNumerator χ i * bwRepresentativeNumerator q i : ℤ) : ℝ) / 2 := by
      simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div, Finset.mul_sum, hv,
        bwCanonicalRoot]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [((bwRoot_integer_arithmetic χ).2.2 q).1]
      push_cast
      ring

/-- The literal pairing gives precisely the binary quotient character, for an
arbitrary actual root and arbitrary vector of M. -/
theorem bwRootExponent_mod_two {r g : Fin 8 → ℝ} (hr : IsE8Root r)
    (hg : g ∈ bwMSet) (χ : BWCharacter)
    (hχ : (fun i => r i / 2) - bwCanonicalHole χ ∈ bwMSet)
    (q : BWQuotient) (hq : g - bwRepresentative q ∈ dPlusSet 8) :
    (bwRootExponent r g : ℝ) = 2 * ∑ i, r i * g i ∧
      (bwRootExponent r g : Binary) = bwCharacterEval χ q := by
  let m := (fun i => r i / 2) - bwCanonicalHole χ
  obtain ⟨a, ha, hea⟩ := e8_pairing_even (bwCanonicalRoot_isRoot χ).1 hq
  obtain ⟨b, hb, heb⟩ := bwM_pairing_even hχ hg
  change 4 * ∑ i, m i * g i = (b : ℝ) at heb
  let k : ℤ := a + bwCanonicalPairExponent χ q + b
  have he : 2 * ∑ i, r i * g i = (k : ℝ) := by
    have hi (i) : r i = bwCanonicalRoot χ i + 2 * m i := by
      have h := congrFun (bwCanonicalRoot_half χ) i
      dsimp [m]
      change bwCanonicalRoot χ i / 2 = bwCanonicalHole χ i at h
      linarith
    have hid : 2 * ∑ i, r i * g i =
        (2 * ∑ i, bwCanonicalRoot χ i * (g - bwRepresentative q) i) +
        (2 * ∑ i, bwCanonicalRoot χ i * bwRepresentative q i) +
        (4 * ∑ i, m i * g i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Pi.sub_apply, hi]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hid, hea, bwCanonicalRoot_pairing, heb]
    simp only [k, Int.cast_add]
  have hk : bwRootExponent r g = k := by simp only [bwRootExponent, he, Int.floor_intCast]
  refine ⟨by rw [hk]; exact he.symm, ?_⟩
  rw [hk]
  simp only [k, Int.cast_add, ha.intCast_zmod_two, hb.intCast_zmod_two, zero_add, add_zero]
  exact ((bwRoot_integer_arithmetic χ).2.2 q).2

theorem bwRootExponent_integral {r g : Fin 8 → ℝ} (hr : IsE8Root r) (hg : g ∈ bwMSet) :
    (bwRootExponent r g : ℝ) = 2 * ∑ i, r i * g i := by
  obtain ⟨χ, hχ⟩ := e8Root_half_has_canonical_class hr
  obtain ⟨q, l, hl, he⟩ := bw_coset_coverage hg
  exact (bwRootExponent_mod_two hr hg χ hχ q (by rw [he, add_sub_cancel_right]; exact hl)).1

theorem bwRootExponent_eq_euclidean_pairing {r g : Fin 8 → ℝ}
    (hr : IsE8Root r) (hg : g ∈ bwMSet) :
    (bwRootExponent r g : ℝ) = 2 *
      inner ℝ (WithLp.toLp 2 r : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 g) := by
  rw [bwRootExponent_integral hr hg]
  simp [EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]

theorem bwRootCharacter_eq_neg_one_iff {r g : Fin 8 → ℝ} (hr : IsE8Root r)
    (hg : g ∈ bwMSet) (χ : BWCharacter)
    (hχ : (fun i => r i / 2) - bwCanonicalHole χ ∈ bwMSet)
    (q : BWQuotient) (hq : g - bwRepresentative q ∈ dPlusSet 8) :
    bwRootCharacter r g = -1 ↔ bwCharacterEval χ q = 1 := by
  have h := (bwRootExponent_mod_two hr hg χ hχ q hq).2
  have he : Even (bwRootExponent r g) ↔ bwCharacterEval χ q = 0 := by
    rw [← ZMod.intCast_eq_zero_iff_even, h]
  simp only [bwRootCharacter, neg_one_zpow_eq_ite, he]
  rcases binary_eq_zero_or_one (bwCharacterEval χ q) with h0 | h0 <;> norm_num [h0]

/-- The complete union in §7.5, indexed by every actual E8 root and using the
literal character `(-1)^(2⟨r,t-s⟩)`. -/
theorem bwGamma_deepHole_iff_root_union (x y : Fin 8 → ℝ) :
    IsDeepHole bwGammaSet (Fin.append x y) ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧
        x = (fun i => r i / 2) + s ∧ y = (fun i => r i / 2) + t ∧
        bwRootCharacter r (t - s) = -1 := by
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := bwDeepHole_coset_coverage hz
    obtain ⟨hs, ht, hd⟩ := (bwGamma_mem_iff _).mp hp
    let s := x - bwCanonicalHole p.val.1
    let t := y - bwCanonicalHole p.val.1
    have hs' : s ∈ bwMSet := by
      have hleft : bwLeft (Fin.append x y - bwCanonicalDeepHole p) = s := by
        funext i
        simp only [bwLeft, bwCanonicalDeepHole, Pi.sub_apply, Fin.append_left, s]
      simpa only [hleft] using hs
    have ht' : t - bwRepresentative p.val.2 ∈ bwMSet := by
      convert ht using 1
      funext i
      simp only [bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply, Fin.append_right, t]
      ring
    have htM : t ∈ bwMSet := by
      simpa only [sub_add_cancel] using bwMSet_add ht' (bwRepresentative_mem p.val.2)
    have hq : (t - s) - bwRepresentative p.val.2 ∈ dPlusSet 8 := by
      convert dPlusSet_neg (by decide : Even 8) hd using 1
      funext i
      simp only [bwLeft, bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply,
        Pi.neg_apply, Fin.append_left, Fin.append_right, s, t]
      ring
    refine ⟨bwCanonicalRoot p.val.1, bwCanonicalRoot_isRoot _, s, t, hs', htM, ?_, ?_, ?_⟩
    · rw [bwCanonicalRoot_half]; dsimp [s]; abel
    · rw [bwCanonicalRoot_half]; dsimp [t]; abel
    · apply (bwRootCharacter_eq_neg_one_iff (bwCanonicalRoot_isRoot _)
        (bwMAddSubgroup.sub_mem htM hs') p.val.1 ?_ p.val.2 hq).mpr p.property
      rw [bwCanonicalRoot_half, sub_self]
      exact bwMSet_zero
  · rintro ⟨r, hr, s, t, hs, ht, hx, hy, hphase⟩
    obtain ⟨χ, hχ⟩ := e8Root_half_has_canonical_class hr
    obtain ⟨q, l, hl, he⟩ := bw_coset_coverage (bwMAddSubgroup.sub_mem ht hs)
    have hq : (t - s) - bwRepresentative q ∈ dPlusSet 8 := by
      rw [he, add_sub_cancel_right]
      exact hl
    have hp := (bwRootCharacter_eq_neg_one_iff hr (bwMAddSubgroup.sub_mem ht hs)
      χ hχ q hq).mp hphase
    apply (bwDeepHole_coset_iff _).mpr
    refine ⟨⟨(χ, q), hp⟩, (bwGamma_mem_iff _).mpr ?_⟩
    constructor
    · convert bwMSet_add hχ hs using 1
      funext i
      simp only [bwLeft, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply, Fin.append_left, hx]
      ring
    constructor
    · have hm : ((fun i => r i / 2) - bwCanonicalHole χ + t) - bwRepresentative q ∈ bwMSet :=
        bwMAddSubgroup.sub_mem (bwMSet_add hχ ht) (bwRepresentative_mem q)
      convert hm using 1
      funext i
      simp only [bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply, Fin.append_right, hy]
      ring
    · convert dPlusSet_neg (by decide : Even 8) hq using 1
      funext i
      simp only [bwLeft, bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply,
        Pi.neg_apply, Fin.append_left, Fin.append_right, hx, hy]
      ring

theorem bwGamma_gaussian_equality_iff_root_union {α : ℝ} (hα : 0 < α) (x y : Fin 8 → ℝ) :
    setGaussian bwGammaSet α (Fin.append x y) = bwGammaMinimum α ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧
        x = (fun i => r i / 2) + s ∧ y = (fun i => r i / 2) + t ∧
        bwRootCharacter r (t - s) = -1 := by
  rw [← isColdSpot_bwGamma_iff_value hα, coldSpot_bwGamma_iff_deepHole hα,
    bwGamma_deepHole_iff_root_union]

/-- The identical full equality locus after the paper's √2 normalization. -/
theorem bw16_coldSpot_iff_root_union {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bw16Set α z ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  let w := scaleVec (Real.sqrt 2)⁻¹ z
  have hw : scaleVec (Real.sqrt 2) w = z := scaleVec_inv _ sqrt_two_ne_zero z
  have hdeep : IsColdSpot bw16Set α z ↔ IsDeepHole bwGammaSet w := by
    rw [coldSpot_bw16_iff_deepHole hα, ← hw, bw16Set_eq_scaledGamma,
      isDeepHole_scaled_iff _ sqrt_two_ne_zero _ bwGamma_nonempty]
  rw [hdeep, ← append_bw_blocks w, bwGamma_deepHole_iff_root_union]
  constructor
  · rintro ⟨r, hr, s, t, hs, ht, hx, hy, hp⟩
    refine ⟨r, hr, s, t, hs, ht, hp, ?_⟩
    rw [← hx, ← hy, append_bw_blocks, hw]
  · rintro ⟨r, hr, s, t, hs, ht, hp, hz⟩
    have he : w = Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t) :=
      scaleVec_injective _ sqrt_two_ne_zero (hw.trans hz)
    exact ⟨r, hr, s, t, hs, ht, by rw [he, bwLeft_append],
      by rw [he, bwRight_append], hp⟩

theorem bw16_deepHole_iff_root_union (z : Fin 16 → ℝ) :
    IsDeepHole bw16Set z ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  rw [← coldSpot_bw16_iff_deepHole (α := 1) (by norm_num),
    bw16_coldSpot_iff_root_union (by norm_num)]

theorem bw16_gaussian_equality_iff_root_union {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    setGaussian bw16Set α z = bwGammaMinimum (2 * α) ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  have hv : IsColdSpot bw16Set α z ↔ setGaussian bw16Set α z = bwGammaMinimum (2 * α) := by
    obtain ⟨hmin, w, hw⟩ := bw16_gaussian_minimum hα
    constructor
    · intro h
      have hz := h w
      rw [hw] at hz
      exact le_antisymm hz (hmin z)
    · intro hz y
      rw [hz]
      exact hmin y
  rw [← hv, bw16_coldSpot_iff_root_union hα]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwDeepHole_coset_iff
#print axioms PaperVerification.ColdSpots.bwGamma_deep_translation_class_count
#print axioms PaperVerification.ColdSpots.bw16_deep_translation_class_count
#print axioms PaperVerification.ColdSpots.bwRootExponent_integral
#print axioms PaperVerification.ColdSpots.bwGamma_deepHole_iff_root_union
#print axioms PaperVerification.ColdSpots.bwGamma_gaussian_equality_iff_root_union
#print axioms PaperVerification.ColdSpots.bw16_coldSpot_iff_root_union
#print axioms PaperVerification.ColdSpots.bw16_deepHole_iff_root_union
#print axioms PaperVerification.ColdSpots.bw16_gaussian_equality_iff_root_union
end
end Source_BWTranslationClasses
-- END ORIGINAL PaperVerification.BWTranslationClasses


-- BEGIN ORIGINAL PaperVerification.DnTranslationClasses
section Source_DnTranslationClasses

-- original header: module

-- original header: public import PaperVerification.LatticeTranslationClasses
-- original header: public import PaperVerification.BWCode
-- original header: public import Mathlib.Data.Finset.Powerset
-- original header: public import Mathlib.Data.Fintype.Powerset


-- original header: @[expose] public section
/-! # The binomial number of D_n^+ deep-hole translation classes

The representatives normalize the first coordinate to be integral and retain
one integer-parity bit.  Complementation identifies the two choices of half
coordinates.  The final quotient count is therefore exactly binomial(n,n/2),
with no restriction beyond even n>8.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

abbrev DnHoleIndex (n : ℕ) := {S : Finset (Fin n) // S.card = n / 2}

theorem card_dnHoleIndex (n : ℕ) : Fintype.card (DnHoleIndex n) = n.choose (n / 2) := by
  let e : DnHoleIndex n ≃ ((Finset.univ : Finset (Fin n)).powersetCard (n / 2)) :=
    { toFun := fun S => ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
      invFun := fun S => ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Finset.card_powersetCard]

def dnHalfSet (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 / 2 else 0

def dnUnit (hn : 0 < n) (ε : Binary) : Fin n → ℤ :=
  fun i => if i = ⟨0, hn⟩ then ε.val else 0

theorem sum_dnUnit (hn : 0 < n) (ε : Binary) : (∑ i, dnUnit hn ε i) = (ε.val : ℤ) := by
  simp [dnUnit]

def dnNormalizedSet (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if (⟨0, hn⟩ : Fin n) ∈ S then Sᶜ else S

def dnSetPhase (hn : 0 < n) (S : Finset (Fin n)) : Binary :=
  if (⟨0, hn⟩ : Fin n) ∈ S then 1 else 0

def dnClassPoint (hn : 0 < n) (S : DnHoleIndex n) : Fin n → ℝ :=
  dnHalfSet (dnNormalizedSet hn S.val) + intVec (dnUnit hn (dnSetPhase hn S.val))

theorem dnNormalizedSet_zero_not_mem (hn : 0 < n) (S : Finset (Fin n)) :
    (⟨0, hn⟩ : Fin n) ∉ dnNormalizedSet hn S := by
  classical
  unfold dnNormalizedSet
  split_ifs with h <;> simp [h]

theorem even_half_identity (heven : Even n) : n = n / 2 + n / 2 := by
  obtain ⟨k, hk⟩ := heven
  omega

theorem dnNormalizedSet_card (hn : 0 < n) (heven : Even n) (S : DnHoleIndex n) :
    (dnNormalizedSet hn S.val).card = n / 2 := by
  classical
  unfold dnNormalizedSet
  split_ifs
  · rw [Finset.card_compl, Fintype.card_fin, S.property]
    have := even_half_identity heven
    omega
  · exact S.property

theorem foldedRadius_halfSet_int (S : Finset (Fin n)) (m : Fin n → ℤ) (i : Fin n) :
    foldedRadius (dnHalfSet S + intVec m) i = if i ∈ S then 1 / 2 else 0 := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    apply (foldedRadius_eq_half_iff _ i).mpr
    exact ⟨m i, by simp [dnHalfSet, intVec, hi, add_comm]⟩
  · rw [if_neg hi]
    apply (foldedRadius_eq_zero_iff _ i).mpr
    exact ⟨m i, by simp [dnHalfSet, intVec, hi]⟩

theorem dnClassPoint_balanced (hn : 0 < n) (heven : Even n) (S : DnHoleIndex n) :
    BalancedHalfGrid (dnClassPoint hn S) := by
  classical
  constructor
  · intro i
    rw [dnClassPoint, foldedRadius_halfSet_int]
    split_ifs <;> simp
  · have hsum : (∑ i, foldedRadius (dnClassPoint hn S) i) =
        ((dnNormalizedSet hn S.val).card : ℝ) / 2 := by
      simp [dnClassPoint, foldedRadius_halfSet_int, Finset.sum_ite, div_eq_mul_inv]
    rw [hsum, dnNormalizedSet_card hn heven S]
    have hcast : (n : ℝ) = ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast even_half_identity heven
    linarith

theorem dnClassPoint_deep (hn : 8 < n) (heven : Even n) (S : DnHoleIndex n) :
    IsDeepHole (dPlusSet n) (dnClassPoint (by omega) S) := by
  apply (isDeepHole_dPlus_iff_depth hn.le heven _).mpr
  exact squaredDepth_dPlus_of_balanced hn.le (dnClassPoint_balanced (by omega) heven S)

theorem dnHalfGrid_normalForm {x : Fin n → ℝ} (hx : HalfIntegerGrid x) :
    ∃ m : Fin n → ℤ, ∃ S : Finset (Fin n), x = dnHalfSet S + intVec m := by
  classical
  choose w hw using hx
  let c : Fin n → Binary := fun i => (w i : Binary)
  let m : Fin n → ℤ := fun i => (w i - (c i).val) / 2
  let S : Finset (Fin n) := Finset.univ.filter (fun i => c i = 1)
  have hi (i : Fin n) : 2 * m i = w i - (c i).val := by
    apply Int.mul_ediv_cancel'
    apply even_iff_two_dvd.mp
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sub, binary_val_cast, c, sub_self]
  refine ⟨m, S, ?_⟩
  funext i
  have h : 2 * (m i : ℝ) = (w i : ℝ) - ((c i).val : ℝ) := by exact_mod_cast hi i
  rw [hw i]
  rcases binary_eq_zero_or_one (c i) with hc | hc
  all_goals
    rw [hc] at h
    simp only [binary_one_val, ZMod.val_zero, Nat.cast_one, Nat.cast_zero] at h
    simp [dnHalfSet, S, intVec, hc]
    linarith

theorem nonintegerCount_halfSet_int (S : Finset (Fin n)) (m : Fin n → ℤ) :
    nonintegerCount (dnHalfSet S + intVec m) = S.card := by
  classical
  unfold nonintegerCount
  have he : (Finset.univ.filter fun i => ¬∃ k : ℤ, (dnHalfSet S + intVec m) i = (k : ℝ)) = S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← foldedRadius_eq_zero_iff,
      foldedRadius_halfSet_int]
    by_cases hi : i ∈ S <;> simp [hi]
  rw [he]

theorem dnNormalized_data_injective (hn : 0 < n) {S T : Finset (Fin n)}
    (hset : dnNormalizedSet hn S = dnNormalizedSet hn T)
    (hphase : dnSetPhase hn S = dnSetPhase hn T) : S = T := by
  classical
  by_cases hs : (⟨0, hn⟩ : Fin n) ∈ S <;> by_cases ht : (⟨0, hn⟩ : Fin n) ∈ T
  · have h : Sᶜ = Tᶜ := by simpa only [dnNormalizedSet, if_pos hs, if_pos ht] using hset
    simpa using congrArg (fun U : Finset (Fin n) => Uᶜ) h
  · norm_num [dnSetPhase, hs, ht] at hphase
  · norm_num [dnSetPhase, hs, ht] at hphase
  · simpa only [dnNormalizedSet, if_neg hs, if_neg ht] using hset

theorem dnHalfSet_integer_difference {S T : Finset (Fin n)} {m : Fin n → ℤ}
    (h : dnHalfSet S - dnHalfSet T = intVec m) : S = T := by
  classical
  ext i
  have hi := congrFun h i
  change (if i ∈ S then 1 / 2 else 0) - (if i ∈ T then 1 / 2 else 0) = (m i : ℝ) at hi
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T
  · simp [hs, ht]
  · have he : (m i : ℝ) = (0 : ℝ) + 1 / 2 := by norm_num [hs, ht] at hi ⊢; linarith
    exact (integer_ne_half_shift (m i) 0 (by simpa only [Int.cast_zero] using he)).elim
  · have he : (m i : ℝ) = (-1 : ℝ) + 1 / 2 := by norm_num [hs, ht] at hi ⊢; linarith
    exact (integer_ne_half_shift (m i) (-1)
      (by simpa only [Int.cast_neg, Int.cast_one] using he)).elim
  · simp [hs, ht]

theorem dnClassPoint_distinct (hn : 0 < n) (S T : DnHoleIndex n) :
    dnClassPoint hn S - dnClassPoint hn T ∈ dPlusSet n ↔ S = T := by
  classical
  constructor
  · rintro ⟨z, hz, h | h⟩
    · have hset : dnNormalizedSet hn S.val = dnNormalizedSet hn T.val := by
        apply dnHalfSet_integer_difference (m := z - dnUnit hn (dnSetPhase hn S.val) + dnUnit hn (dnSetPhase hn T.val))
        have he := h
        funext i
        have hi := congrFun he i
        simp only [dnClassPoint, Pi.sub_apply, Pi.add_apply, intVec, Int.cast_add, Int.cast_sub] at hi ⊢
        linarith
      have heq : z = dnUnit hn (dnSetPhase hn S.val) - dnUnit hn (dnSetPhase hn T.val) := by
        apply intVec_injective n
        rw [← h]
        funext i
        simp only [dnClassPoint, Pi.sub_apply, Pi.add_apply, intVec, Int.cast_sub, hset]
        ring
      simp only [heq, Pi.sub_apply, Finset.sum_sub_distrib, sum_dnUnit] at hz
      have hphase : dnSetPhase hn S.val = dnSetPhase hn T.val := by
        have hh := ZMod.intCast_eq_zero_iff_even.mpr hz
        simpa only [Int.cast_sub, binary_val_cast, sub_eq_zero] using hh
      exact Subtype.ext (dnNormalized_data_injective hn hset hphase)
    · have hi := congrFun h ⟨0, hn⟩
      have hs := dnNormalizedSet_zero_not_mem hn S.val
      have ht := dnNormalizedSet_zero_not_mem hn T.val
      simp only [dnClassPoint, Pi.sub_apply, Pi.add_apply, dnHalfSet, if_neg hs, if_neg ht,
        zero_add, intVec, dnUnit, if_pos rfl, ite_true] at hi
      apply False.elim
      apply integer_ne_half_shift
        (((dnSetPhase hn S.val).val : ℤ) - (dnSetPhase hn T.val).val) (z ⟨0, hn⟩)
      simpa only [Int.cast_sub, Int.cast_natCast] using hi
  · rintro rfl
    simpa only [sub_self] using zero_mem_dPlusSet n

def dnIndexOfNormalized (hn : 0 < n) (heven : Even n) (S : Finset (Fin n))
    (hS : S.card = n / 2) (ε : Binary) : DnHoleIndex n :=
  if ε = 0 then ⟨S, hS⟩ else ⟨Sᶜ, by
    rw [Finset.card_compl, Fintype.card_fin, hS]
    have := even_half_identity heven
    omega⟩

theorem dnIndexOfNormalized_point (hn : 0 < n) (heven : Even n) (S : Finset (Fin n))
    (hS : S.card = n / 2) (hzero : (⟨0, hn⟩ : Fin n) ∉ S) (ε : Binary) :
    dnClassPoint hn (dnIndexOfNormalized hn heven S hS ε) = dnHalfSet S + intVec (dnUnit hn ε) := by
  classical
  rcases binary_eq_zero_or_one ε with h | h <;>
    simp [dnIndexOfNormalized, dnClassPoint, dnNormalizedSet, dnSetPhase, hzero, h]

theorem dnDeepHole_coset_coverage (hn : 8 < n) (heven : Even n)
    {x : Fin n → ℝ} (hx : IsDeepHole (dPlusSet n) x) :
    ∃ S : DnHoleIndex n, x - dnClassPoint (by omega) S ∈ dPlusSet n := by
  classical
  have hgrid := (isDeepHole_dPlus_iff_paperHalfGrid hn heven x).mp hx
  obtain ⟨m, S, rfl⟩ := dnHalfGrid_normalForm hgrid.1
  have hS : S.card = n / 2 := by
    simpa only [nonintegerCount_halfSet_int] using hgrid.2
  let hn0 : 0 < n := by omega
  by_cases hs : (⟨0, hn0⟩ : Fin n) ∈ S
  · let z : Fin n → ℤ := fun i => m i + (if i ∈ S then 1 else 0) - 1
    let ε : Binary := (∑ i, z i : ℤ)
    have hSc : (Sᶜ).card = n / 2 := by
      rw [Finset.card_compl, Fintype.card_fin, hS]
      have := even_half_identity heven
      omega
    refine ⟨dnIndexOfNormalized hn0 heven Sᶜ hSc ε, ?_⟩
    rw [dnIndexOfNormalized_point hn0 heven Sᶜ hSc (by simpa using hs)]
    refine ⟨z - dnUnit hn0 ε, ?_, Or.inr ?_⟩
    · apply ZMod.intCast_eq_zero_iff_even.mp
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_dnUnit, Int.cast_sub, binary_val_cast, ε, sub_self]
    · funext i
      by_cases hi : i ∈ S <;>
        simp [dnHalfSet, intVec, z, hi] <;> ring
  · let ε : Binary := (∑ i, m i : ℤ)
    refine ⟨dnIndexOfNormalized hn0 heven S hS ε, ?_⟩
    rw [dnIndexOfNormalized_point hn0 heven S hS hs]
    refine ⟨m - dnUnit hn0 ε, ?_, Or.inl ?_⟩
    · apply ZMod.intCast_eq_zero_iff_even.mp
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_dnUnit, Int.cast_sub, binary_val_cast, ε, sub_self]
    · funext i
      simp only [Pi.add_apply, Pi.sub_apply, intVec, Int.cast_sub]
      ring

def dnDeepClassMap (hn : 8 < n) (heven : Even n) (S : DnHoleIndex n) :
    DeepTranslationClasses (dPlusAddSubgroup n heven) :=
  ⟨(dnClassPoint (by omega) S : (Fin n → ℝ) ⧸ dPlusAddSubgroup n heven),
    dnClassPoint (by omega) S, dnClassPoint_deep hn heven S, rfl⟩

theorem dnDeepClassMap_bijective (hn : 8 < n) (heven : Even n) :
    Function.Bijective (dnDeepClassMap hn heven) := by
  constructor
  · intro S T h
    apply (dnClassPoint_distinct (by omega) S T).mp
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, x, hx, hC⟩
    obtain ⟨S, hS⟩ := dnDeepHole_coset_coverage hn heven hx
    refine ⟨S, Subtype.ext ?_⟩
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hS).symm.trans hC

def dnDeepClassEquiv (hn : 8 < n) (heven : Even n) :
    DnHoleIndex n ≃ DeepTranslationClasses (dPlusAddSubgroup n heven) :=
  Equiv.ofBijective (dnDeepClassMap hn heven) (dnDeepClassMap_bijective hn heven)

/-- The full symbolic binomial count for every even n>8. -/
theorem dPlus_deep_translation_class_count (hn : 8 < n) (heven : Even n) :
    Nat.card (DeepTranslationClasses (dPlusAddSubgroup n heven)) = n.choose (n / 2) := by
  rw [← Nat.card_congr (dnDeepClassEquiv hn heven), Nat.card_eq_fintype_card, card_dnHoleIndex]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.dPlus_deep_translation_class_count
end
end Source_DnTranslationClasses
-- END ORIGINAL PaperVerification.DnTranslationClasses


-- BEGIN ORIGINAL PaperVerification.LatticeMetricMeaning
section Source_LatticeMetricMeaning

-- original header: module

-- original header: public import PaperVerification.LatticeDefs
-- original header: public import PaperVerification.DnGaussian
-- original header: public import Mathlib.Topology.MetricSpace.HausdorffDistance
-- original header: public import Mathlib.Analysis.SpecialFunctions.Sqrt


-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

variable {n : ℕ}

def euclideanRealization (L : Set (Fin n → ℝ)) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun x : Fin n → ℝ ↦ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))) '' L

theorem sqDist_eq_euclidean_dist_sq (x y : Fin n → ℝ) :
    sqDist x y=dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)^2 := by
  rw [sqDist_eq_euclidean_norm_sq,dist_eq_norm]

def euclideanRealizationEquiv (L : Set (Fin n → ℝ)) : L ≃ euclideanRealization L :=
  Equiv.ofBijective (fun x ↦ ⟨(WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin n)),
    x.val,x.property,rfl⟩) ⟨by
      intro x y h
      apply Subtype.ext
      have he := congrArg (fun p : euclideanRealization L ↦ WithLp.ofLp p.val) h
      exact he,by
      rintro ⟨y,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩⟩

theorem setGaussian_eq_euclidean (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) :
    setGaussian L α x = ∑' v : euclideanRealization L,
      Real.exp (-α*dist v.val (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))^2) := by
  rw [← (euclideanRealizationEquiv L).tsum_eq]
  apply tsum_congr
  intro v
  exact congrArg (fun t : ℝ ↦ Real.exp (-α*t)) (sqDist_eq_euclidean_dist_sq v.val x)

theorem isColdSpot_iff_euclidean (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) :
    IsColdSpot L α x ↔ ∀ y : EuclideanSpace ℝ (Fin n),
      (∑' v : euclideanRealization L,
        Real.exp (-α*dist v.val (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))^2)) ≤
      ∑' v : euclideanRealization L, Real.exp (-α*dist v.val y^2) := by
  constructor
  · intro h y
    have hy := h (WithLp.ofLp y)
    simpa only [setGaussian_eq_euclidean,WithLp.toLp_ofLp] using hy
  · intro h y
    have hy := h (WithLp.toLp 2 y)
    simpa only [setGaussian_eq_euclidean] using hy

/-- The working infimum of squared distances is exactly the square of the
ordinary metric distance to the actual Euclidean lattice set. -/
theorem squaredDepth_eq_infDist_sq (L : Set (Fin n → ℝ)) (hL : L.Nonempty) (x : Fin n → ℝ) :
    squaredDepth L x=
      Metric.infDist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (euclideanRealization L)^2 := by
  let d := Metric.infDist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (euclideanRealization L)
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have hD := squaredDepth_nonneg L hL x
  apply le_antisymm
  · have hs : Real.sqrt (squaredDepth L x) ≤ d := by
      apply (Metric.le_infDist (hL.image _)).mpr
      rintro y ⟨z,hz,rfl⟩
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mp
      rw [Real.sq_sqrt hD,← sqDist_eq_euclidean_dist_sq]
      exact squaredDepth_le x hz
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rw [Real.sq_sqrt hD] at hsq
    exact hsq
  · apply le_csInf (hL.image _)
    rintro r ⟨z,hz,rfl⟩
    change d^2 ≤ sqDist x z
    rw [sqDist_eq_euclidean_dist_sq]
    exact pow_le_pow_left₀ hd
      (Metric.infDist_le_dist_of_mem (show (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))∈
        euclideanRealization L from ⟨z,hz,rfl⟩)) 2

/-- In particular the formal `IsDeepHole` predicate has exactly its ordinary
Euclidean metric meaning; all ambient points are quantified. -/
theorem isDeepHole_iff_metric (L : Set (Fin n → ℝ)) (hL : L.Nonempty) (x : Fin n → ℝ) :
    IsDeepHole L x ↔ ∀ y : EuclideanSpace ℝ (Fin n),
      Metric.infDist y (euclideanRealization L) ≤
        Metric.infDist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (euclideanRealization L) := by
  constructor
  · intro h y
    have hy := h (WithLp.ofLp y)
    rw [squaredDepth_eq_infDist_sq L hL,squaredDepth_eq_infDist_sq L hL] at hy
    simpa only [WithLp.toLp_ofLp] using
      (sq_le_sq₀ (Metric.infDist_nonneg) (Metric.infDist_nonneg)).mp hy
  · intro h y
    rw [squaredDepth_eq_infDist_sq L hL,squaredDepth_eq_infDist_sq L hL]
    exact pow_le_pow_left₀ (Metric.infDist_nonneg) (h (WithLp.toLp 2 y)) 2

end PaperVerification.ColdSpots
end
end Source_LatticeMetricMeaning
-- END ORIGINAL PaperVerification.LatticeMetricMeaning


-- BEGIN ORIGINAL PaperVerification.E7MetricMeaning
section Source_E7MetricMeaning

-- original header: module

-- original header: public import PaperVerification.E7Theorems
-- original header: public import PaperVerification.LatticeMetricMeaning
-- original header: public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem coordinateInner_eq_euclidean_inner (x y : Fin 8 → ℝ) :
    coordinateInner x y=inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 y) := by
  simp [coordinateInner,EuclideanSpace.inner_toLp_toLp,dotProduct,mul_comm]

/-- `project8` is orthogonal projection for the Euclidean inner product,
independently of the default norm on an unbundled coordinate function type. -/
theorem project8_residual_orthogonal (x : Fin 8 → ℝ) (y : zeroSumSpace) :
    inner ℝ (WithLp.toLp 2 (x-(project8 x).val) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 y.val)=0 := by
  rw [← coordinateInner_eq_euclidean_inner]
  unfold coordinateInner
  simp only [Pi.sub_apply,project8_apply,sub_sub_cancel,← Finset.mul_sum,
    zeroSumSpace_sum,mul_zero]

theorem e7DualSet_euclidean_meaning (y : zeroSumSpace) : y ∈ e7DualSet ↔
    ∀ x ∈ e7Set, ∃ k : ℤ,
      inner ℝ (WithLp.toLp 2 y.val : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 x.val)=(k:ℝ) := by
  simp only [e7DualSet,Set.mem_setOf_eq,coordinateInner_eq_euclidean_inner]

def e7AmbientLattice : Set (Fin 8 → ℝ) := Subtype.val '' e7ProjectedSet

/-- The projected lattice and its ambient image have exactly the same points,
with no multiplicities introduced by the coordinate inclusion. -/
def e7AmbientLatticeEquiv : e7ProjectedSet ≃ e7AmbientLattice :=
  Equiv.ofBijective (fun y ↦ ⟨y.val.val, y.val, y.property, rfl⟩) ⟨by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : e7AmbientLattice ↦ v.val) h, by
    rintro ⟨v, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩⟩

theorem e7AmbientLattice_eq_dual_image :
    e7AmbientLattice = Subtype.val '' e7DualSet := by
  rw [e7DualSet_eq_projected]
  rfl

theorem e7Gaussian_eq_ambient (α : ℝ) (x : zeroSumSpace) :
    e7Gaussian α x = setGaussian e7AmbientLattice α x.val := by
  exact e7AmbientLatticeEquiv.tsum_eq
    (fun v : e7AmbientLattice ↦ Real.exp (-α * sqDist v.val x.val))

/-- The Gaussian in the principal E7 statement is the literal Gaussian sum
for the Euclidean realization of the integral dual lattice. -/
theorem e7Gaussian_eq_euclidean (α : ℝ) (x : zeroSumSpace) :
    e7Gaussian α x = ∑' v : euclideanRealization e7AmbientLattice,
      Real.exp (-α * dist v.val
        (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8)) ^ 2) := by
  rw [e7Gaussian_eq_ambient, setGaussian_eq_euclidean]

theorem isE7ColdSpot_iff_euclidean (α : ℝ) (x : zeroSumSpace) :
    IsE7ColdSpot α x ↔ ∀ y : EuclideanSpace ℝ (Fin 8), (∑ i, y i) = 0 →
      (∑' v : euclideanRealization e7AmbientLattice,
        Real.exp (-α * dist v.val
          (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8)) ^ 2)) ≤
        ∑' v : euclideanRealization e7AmbientLattice,
          Real.exp (-α * dist v.val y ^ 2) := by
  constructor
  · intro h y hy
    let z : zeroSumSpace := ⟨WithLp.ofLp y, hy⟩
    have hz := h z
    simpa only [e7Gaussian_eq_euclidean, z, WithLp.toLp_ofLp] using hz
  · intro h y
    have hy := h (WithLp.toLp 2 y.val) y.property
    simpa only [e7Gaussian_eq_euclidean] using hy

theorem e7SquaredDepth_eq_ambient (x : zeroSumSpace) :
    e7SquaredDepth x=squaredDepth e7AmbientLattice x.val := by
  unfold e7SquaredDepth squaredDepth e7AmbientLattice
  rw [Set.image_image]

theorem e7SquaredDepth_metric_meaning (x : zeroSumSpace) :
    e7SquaredDepth x=Metric.infDist (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8))
      (euclideanRealization e7AmbientLattice)^2 := by
  rw [e7SquaredDepth_eq_ambient]
  exact squaredDepth_eq_infDist_sq e7AmbientLattice
    (e7Projected_nonempty.image (fun y : zeroSumSpace ↦ y.val)) x.val

theorem isE7DeepHole_metric_meaning (x : zeroSumSpace) : IsE7DeepHole x ↔
    ∀ y : EuclideanSpace ℝ (Fin 8), (∑ i,y i)=0 →
      Metric.infDist y (euclideanRealization e7AmbientLattice) ≤
        Metric.infDist (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8))
          (euclideanRealization e7AmbientLattice) := by
  constructor
  · intro h y hy
    let z : zeroSumSpace := ⟨WithLp.ofLp y,hy⟩
    have hd := h z
    rw [e7SquaredDepth_metric_meaning,e7SquaredDepth_metric_meaning] at hd
    exact (sq_le_sq₀ Metric.infDist_nonneg Metric.infDist_nonneg).mp hd
  · intro h y
    rw [e7SquaredDepth_metric_meaning,e7SquaredDepth_metric_meaning]
    exact pow_le_pow_left₀ Metric.infDist_nonneg
      (h (WithLp.toLp 2 y.val) y.property) 2

def coordinateSumLinear : (Fin 8 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i,x i
  map_add' := by intro x y; simp [Finset.sum_add_distrib]
  map_smul' := by intro a x; simp [← Finset.mul_sum]

theorem coordinateSumLinear_surjective : Function.Surjective coordinateSumLinear := by
  intro c
  exact ⟨Pi.single 0 c,by simp [coordinateSumLinear,Pi.single_apply]⟩

theorem zeroSumSpace_finrank : Module.finrank ℝ zeroSumSpace=7 := by
  have hk : LinearMap.ker coordinateSumLinear=zeroSumSpace := rfl
  have hr : LinearMap.range coordinateSumLinear=⊤ :=
    LinearMap.range_eq_top.mpr coordinateSumLinear_surjective
  have h := LinearMap.finrank_range_add_finrank_ker coordinateSumLinear
  rw [hk,hr] at h
  norm_num at h
  omega

end PaperVerification.ColdSpots
end
end Source_E7MetricMeaning
-- END ORIGINAL PaperVerification.E7MetricMeaning


-- BEGIN ORIGINAL PaperVerification.E8IntegralBasis
section Source_E8IntegralBasis

-- original header: module

-- original header: public import PaperVerification.LatticeTranslations
-- original header: public import Mathlib.Tactic.Module


-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e8SimpleRoot : Fin 8 → (Fin 8 → ℝ) :=
  ![![1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,1/2],
    ![1,1,0,0,0,0,0,0],![-1,1,0,0,0,0,0,0],
    ![0,-1,1,0,0,0,0,0],![0,0,-1,1,0,0,0,0],
    ![0,0,0,-1,1,0,0,0],![0,0,0,0,-1,1,0,0],![0,0,0,0,0,-1,1,0]]

def e8RootSum (t : Fin 8 → ℝ) : Fin 8 → ℝ := ∑ i, t i • e8SimpleRoot i

def e8RootCoordinates (x : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![2*x 7,(∑ i, x i)/2+2*x 7,(∑ i, x i)/2+3*x 7-x 0,
    x 2+x 3+x 4+x 5+x 6+5*x 7,x 3+x 4+x 5+x 6+4*x 7,
    x 4+x 5+x 6+3*x 7,x 5+x 6+2*x 7,x 6+x 7]

theorem e8RootCoordinates_sum (t : Fin 8 → ℝ) : e8RootCoordinates (e8RootSum t)=t := by
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8RootSum,e8SimpleRoot,Fin.sum_univ_succ] <;> ring

theorem e8RootSum_coordinates (x : Fin 8 → ℝ) : e8RootSum (e8RootCoordinates x)=x := by
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8RootSum,e8SimpleRoot,Fin.sum_univ_succ] <;> ring

theorem e8RootSum_injective : Function.Injective e8RootSum :=
  Function.LeftInverse.injective e8RootCoordinates_sum

theorem e8SimpleRoot_mem (i : Fin 8) : e8SimpleRoot i ∈ dPlusSet 8 := by
  fin_cases i
  · refine ⟨![0,-1,-1,-1,-1,-1,-1,0],by decide,Or.inr ?_⟩
    ext j
    fin_cases j <;> norm_num [e8SimpleRoot]
  all_goals solve
    | refine ⟨![1,1,0,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![-1,1,0,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,-1,1,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,-1,1,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,0,-1,1,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,0,0,-1,1,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,0,0,0,-1,1,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]

theorem e8RootSum_int_mem (t : Fin 8 → ℤ) : e8RootSum (fun i ↦ (t i:ℝ)) ∈ dPlusSet 8 := by
  let L := dPlusAddSubgroup 8 (by decide)
  have h : (∑ i, t i • e8SimpleRoot i) ∈ L :=
    L.sum_mem (fun i hi ↦ L.zsmul_mem (e8SimpleRoot_mem i) (t i))
  change (∑ i, t i • e8SimpleRoot i) ∈ dPlusSet 8 at h
  simpa only [e8RootSum, Int.cast_smul_eq_zsmul] using h

def e8IntCoordinates (m : Fin 8 → ℤ) (k : ℤ) : Fin 8 → ℤ :=
  ![2*m 7,k+2*m 7,k+3*m 7-m 0,
    m 2+m 3+m 4+m 5+m 6+5*m 7,m 3+m 4+m 5+m 6+4*m 7,
    m 4+m 5+m 6+3*m 7,m 5+m 6+2*m 7,m 6+m 7]

def e8HalfCoordinates : Fin 8 → ℤ := ![1,3,3,5,4,3,2,1]

theorem e8RootCoordinates_int (m : Fin 8 → ℤ) (k : ℤ) (hk : ∑ i,m i=k+k) :
    e8RootCoordinates (intVec m)=fun i ↦ (e8IntCoordinates m k i:ℝ) := by
  have hsum : (∑ i,(m i:ℝ))=(k:ℝ)+k := by exact_mod_cast hk
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8IntCoordinates,intVec,hsum] <;> ring

theorem e8RootCoordinates_half (m : Fin 8 → ℤ) (k : ℤ) (hk : ∑ i,m i=k+k) :
    e8RootCoordinates (fun i ↦ (m i:ℝ)+1/2)=
      fun i ↦ ((e8IntCoordinates m k i+e8HalfCoordinates i:ℤ):ℝ) := by
  have hsum : (∑ i,(m i:ℝ))=(k:ℝ)+k := by exact_mod_cast hk
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8IntCoordinates,e8HalfCoordinates,
    Finset.sum_add_distrib,hsum] <;> ring

/-- An explicit integral basis for the actual coordinate E₈ lattice. -/
theorem e8_mem_iff_integer_root_coordinates (x : Fin 8 → ℝ) :
    x ∈ dPlusSet 8 ↔ ∃ t : Fin 8 → ℤ, x=e8RootSum (fun i ↦ (t i:ℝ)) := by
  constructor
  · rintro ⟨m,⟨k,hk⟩,rfl|rfl⟩
    · refine ⟨e8IntCoordinates m k,?_⟩
      rw [← e8RootCoordinates_int m k hk,e8RootSum_coordinates]
    · refine ⟨fun i ↦ e8IntCoordinates m k i+e8HalfCoordinates i,?_⟩
      rw [← e8RootCoordinates_half m k hk,e8RootSum_coordinates]
  · rintro ⟨t,rfl⟩
    exact e8RootSum_int_mem t

def e8IntegralQ (t : Fin 8 → ℤ) : ℤ :=
  (∑ i,t i^2)-t 0*t 2-t 2*t 3-t 1*t 3-t 3*t 4-t 4*t 5-t 5*t 6-t 6*t 7

theorem e8RootSum_norm (t : Fin 8 → ℤ) :
    sqDist (e8RootSum (fun i ↦ (t i:ℝ))) 0=2*(e8IntegralQ t:ℝ) := by
  simp [sqDist,e8RootSum,e8SimpleRoot,e8IntegralQ,Fin.sum_univ_succ]
  ring

theorem e8RootSum_add (a b : Fin 8 → ℝ) : e8RootSum (a+b)=e8RootSum a+e8RootSum b := by
  simp [e8RootSum,add_smul,Finset.sum_add_distrib]

theorem e8RootSum_sub (a b : Fin 8 → ℝ) : e8RootSum (a-b)=e8RootSum a-e8RootSum b := by
  simp [e8RootSum,sub_smul,Finset.sum_sub_distrib]

theorem e8RootSum_smul (c : ℝ) (a : Fin 8 → ℝ) : e8RootSum (c•a)=c•e8RootSum a := by
  simp [e8RootSum,smul_smul,Finset.smul_sum]

end PaperVerification.ColdSpots
end
end Source_E8IntegralBasis
-- END ORIGINAL PaperVerification.E8IntegralBasis


-- Kernel-environment audit: every mathematical source body precedes this command.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let entries := kenv.constants.foldStage2
    (fun rows name ci => rows.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let kind : ConstantInfo → String := fun ci => match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut failures : Array Json := #[]
  for (name, ci) in entries do
    if ci.isUnsafe then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unsafe_declaration", toJson true)])
    let deps := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    let mut dependencyRows : Array Json := #[]
    for dep in deps do
      match kenv.find? dep with
      | none =>
        failures := failures.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("missing_dependency", toJson dep.toString)])
      | some info =>
        let origin := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx]!.toString
          | none => env.mainModule.toString
        dependencyRows := dependencyRows.push (Json.mkObj [
          ("name", toJson dep.toString), ("kind", toJson (kind info)),
          ("module", toJson origin)])
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun ax => !allowed.contains ax)
    if !bad.isEmpty then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unapproved_axioms", toJson (bad.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("type", toJson (toString ci.type)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice006.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
