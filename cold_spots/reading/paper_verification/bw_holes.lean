module
public import PaperVerification.BWEligibility
@[expose] public section
/-! # The full Barnes–Wall deep-hole equality criterion

An explicit real point attains squared depth 3/2.  The proof then identifies all
points attaining it with exactly the same coset condition as sharp Gaussian
 gluing.  The argument applies to every point of R¹⁶.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def bwQuarterPoint : Fin 8 → ℝ := fun _ => 1 / 4

def BWGluingCondition (x y : Fin 8 → ℝ) : Prop :=
  squaredDepth bwMSet x = 1 / 2 ∧ squaredDepth bwMSet y = 1 / 2 ∧
    ∀ q : BWQuotient, bwDepthProfile x q = 1 ∨ bwDepthProfile y q = 1

theorem e8FirstVector_eq_intVec : e8FirstVector = intVec (bitUnit 1) := by
  funext i
  simp [e8FirstVector, intVec, bitUnit]

theorem e8FirstVector_mem_bwM : e8FirstVector ∈ bwMSet := by
  rw [e8FirstVector_eq_intVec]
  exact intVec_mem_bwM _

theorem roundedInt_add_intVec {n : ℕ} (x : Fin n → ℝ) (m : Fin n → ℤ) :
    roundedInt (x + intVec m) = roundedInt x + m := by
  funext i
  simp only [roundedInt, Pi.add_apply, intVec, round_add_intCast]

theorem quarter_hole_or_unit_translate {x : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    E8FoldedHole x ∨ E8FoldedHole (x + e8FirstVector) := by
  have hp := quarter_parities_equiv hx hs
  by_cases he : Even (∑ i, roundedInt x i)
  · right
    have hg : -e8FirstVector ∈ bwMSet := bwMSet_neg e8FirstVector_mem_bwM
    have hx' : QuarterGrid8 (x + e8FirstVector) := by
      simpa only [sub_neg_eq_add] using quarterGrid_sub_bwM hx hg
    have hs' : IntegerSum8 (x + e8FirstVector) := by
      simpa only [sub_neg_eq_add] using integerSum_sub hs (bwM_integerSum hg)
    have hne : ¬Even (∑ i, roundedInt (x + e8FirstVector) i) := by
      rw [e8FirstVector_eq_intVec, roundedInt_add_intVec]
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_bitUnit, ZMod.val_one, Nat.cast_one]
      simpa only [Int.even_add_one, not_not] using he
    exact Or.inr (Or.inr (Or.inr ⟨(quarterGrid_iff_folded _).mp hx', hne,
      fun h => hne ((quarter_parities_equiv hx' hs').mpr h)⟩))
  · left
    exact Or.inr (Or.inr (Or.inr ⟨(quarterGrid_iff_folded _).mp hx, he,
      fun h => he (hp.mpr h)⟩))

theorem bwQuarterPoint_quarterGrid : QuarterGrid8 bwQuarterPoint := by
  intro i
  exact ⟨0, by norm_num [bwQuarterPoint]⟩

theorem bwQuarterPoint_integerSum : IntegerSum8 bwQuarterPoint := by
  exact ⟨2, by norm_num [bwQuarterPoint]⟩

/-- Every half-integer coordinate is at least one quarter from the witness. -/
theorem quarter_half_integer_sq_lower (k : ℤ) :
    (1 / 16 : ℝ) ≤ (1 / 4 - (k : ℝ) / 2) ^ 2 := by
  have hk : k ≤ 0 ∨ 1 ≤ k := by omega
  rcases hk with hk | hk
  · have h : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    nlinarith [sq_nonneg ((k : ℝ) / 2)]
  · have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hs := sq_nonneg (((k : ℝ) - 1) / 2)
    nlinarith

theorem squaredDepth_bwM_quarter : squaredDepth bwMSet bwQuarterPoint = 1 / 2 := by
  apply le_antisymm (squaredDepth_bwM_le _)
  apply le_csInf ((show bwMSet.Nonempty from ⟨0, bwMSet_zero⟩).image (fun z => sqDist bwQuarterPoint z))
  rintro r ⟨z, ⟨w, hw, rfl⟩, rfl⟩
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8)))
    (fun i _ => quarter_half_integer_sq_lower (w i))
  norm_num [sqDist, bwQuarterPoint] at h ⊢
  exact h

theorem squaredDepth_bwM_quarter_unit :
    squaredDepth bwMSet (bwQuarterPoint + e8FirstVector) = 1 / 2 := by
  change squaredDepth (bwMAddSubgroup : Set (Fin 8 → ℝ))
    (bwQuarterPoint + e8FirstVector) = 1 / 2
  rw [squaredDepth_add_of_subgroup bwMAddSubgroup _ _ e8FirstVector_mem_bwM]
  exact squaredDepth_bwM_quarter

/-- The two witness profiles complement one another in every quotient coset. -/
theorem bw_witness_gluing : BWGluingCondition (bwQuarterPoint + e8FirstVector) bwQuarterPoint := by
  refine ⟨squaredDepth_bwM_quarter_unit, squaredDepth_bwM_quarter, ?_⟩
  intro q
  have hqM := bwRepresentative_mem q
  have h := quarter_hole_or_unit_translate (quarterGrid_sub_bwM bwQuarterPoint_quarterGrid hqM)
    (integerSum_sub bwQuarterPoint_integerSum (bwM_integerSum hqM))
  have heq : bwQuarterPoint - bwRepresentative q + e8FirstVector =
      bwQuarterPoint + e8FirstVector - bwRepresentative q := by abel
  rcases h with h | h
  · right
    exact (squaredDepth_E8_eq_one_iff _).mpr h
  · left
    rw [heq] at h
    exact (squaredDepth_E8_eq_one_iff _).mpr h

/-- The gluing equality condition always gives a deepest point. -/
theorem squaredDepth_bwGamma_of_gluing {x y : Fin 8 → ℝ} (h : BWGluingCondition x y) :
    squaredDepth bwGammaSet (Fin.append x y) = 3 / 2 := by
  apply le_antisymm (squaredDepth_bwGamma_le _)
  apply (le_squaredDepth_bwGamma_iff x y _).mpr
  intro q
  have hx := squaredDepth_bwM_le_profile x q
  have hy := squaredDepth_bwM_le_profile y q
  rw [h.1] at hx
  rw [h.2.1] at hy
  rcases h.2.2 q with he | he <;> rw [he] <;> linarith

theorem squaredDepth_bwGamma_witness :
    squaredDepth bwGammaSet (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint) = 3 / 2 :=
  squaredDepth_bwGamma_of_gluing bw_witness_gluing

/-- Equality in the radius estimate forces both marginal blocks to be M-deep. -/
theorem bwGamma_deep_marginals {x y : Fin 8 → ℝ}
    (h : squaredDepth bwGammaSet (Fin.append x y) = 3 / 2) :
    squaredDepth bwMSet x = 1 / 2 ∧ squaredDepth bwMSet y = 1 / 2 := by
  obtain ⟨q, hq, _⟩ := exists_min_bwDepthProfile x
  obtain ⟨r, hr, _⟩ := exists_min_bwDepthProfile y
  have hqsum := squaredDepth_bwGamma_le_profile x y q
  have hrsum := squaredDepth_bwGamma_le_profile x y r
  rw [h, hq] at hqsum
  rw [h, hr] at hrsum
  constructor
  · linarith [squaredDepth_bwM_le x, bwDepthProfile_le_one y q]
  · linarith [squaredDepth_bwM_le y, bwDepthProfile_le_one x r]

/-- Every deepest block is eligible; this is deduced rather than imposed. -/
theorem bwGamma_deep_eligible {x y : Fin 8 → ℝ}
    (h : squaredDepth bwGammaSet (Fin.append x y) = 3 / 2) : BWEligible x ∧ BWEligible y := by
  obtain ⟨hx, hy⟩ := bwGamma_deep_marginals h
  obtain ⟨q, hq, _⟩ := exists_min_bwDepthProfile x
  obtain ⟨r, hr, _⟩ := exists_min_bwDepthProfile y
  have hqsum := squaredDepth_bwGamma_le_profile x y q
  have hrsum := squaredDepth_bwGamma_le_profile x y r
  rw [h, hq, hx] at hqsum
  rw [h, hr, hy] at hrsum
  refine ⟨⟨hx, r, ?_⟩, ⟨hy, q, ?_⟩⟩
  · linarith [bwDepthProfile_le_one x r]
  · linarith [bwDepthProfile_le_one y q]

/-- Complete radius equality, for all real points, in exactly the gluing form. -/
theorem squaredDepth_bwGamma_eq_iff (x y : Fin 8 → ℝ) :
    squaredDepth bwGammaSet (Fin.append x y) = 3 / 2 ↔ BWGluingCondition x y := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := bwGamma_deep_eligible h
    refine ⟨hx.1, hy.1, ?_⟩
    intro q
    have hs := squaredDepth_bwGamma_le_profile x y q
    rw [h] at hs
    rcases bwEligible_profile_two_depths hx q with hqx | hqx
    · rcases bwEligible_profile_two_depths hy q with hqy | hqy
      · rw [hqx, hqy] at hs
        norm_num at hs
      · exact Or.inr hqy
    · exact Or.inl hqx
  · exact squaredDepth_bwGamma_of_gluing

theorem isDeepHole_bwGamma_iff_depth (z : Fin 16 → ℝ) :
    IsDeepHole bwGammaSet z ↔ squaredDepth bwGammaSet z = 3 / 2 := by
  constructor
  · intro h
    have hbound := h (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint)
    rw [squaredDepth_bwGamma_witness] at hbound
    exact le_antisymm (squaredDepth_bwGamma_le z) hbound
  · intro hz y
    rw [hz]
    exact squaredDepth_bwGamma_le y

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.squaredDepth_bwGamma_eq_iff
#print axioms PaperVerification.ColdSpots.squaredDepth_bwGamma_witness
