module

public import PaperVerification.BWQuotientGroup
public import PaperVerification.BWHoles


@[expose] public section
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
