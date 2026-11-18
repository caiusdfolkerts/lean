module
public import PaperVerification.BWGluing
@[expose] public section
/-! # Complete geometric eligibility for Barnes–Wall gluing

The full real-coordinate argument uses the complete E8 hole classification.
Every eligible M-hole has E8-coset squared distances only one half and one.
This is enough for the equality theorem; no orbit enumeration is needed.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def IntegerSum8 (x : Fin 8 → ℝ) : Prop := ∃ k : ℤ, (∑ i, x i) = (k : ℝ)
def QuarterGrid8 (x : Fin 8 → ℝ) : Prop := ∀ i, ∃ k : ℤ, x i = (k : ℝ) / 2 + 1 / 4

theorem squaredDepth_sub_of_subgroup {n : ℕ} (L : AddSubgroup (Fin n → ℝ))
    (x g : Fin n → ℝ) (hg : g ∈ L) : squaredDepth (L : Set _) (x - g) = squaredDepth (L : Set _) x := by
  simpa only [sub_eq_add_neg] using squaredDepth_add_of_subgroup L x (-g) (L.neg_mem hg)

theorem squaredDepth_zero_of_mem {n : ℕ} {L : Set (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ L) :
    squaredDepth L x = 0 := by
  apply le_antisymm
  · simpa [sqDist] using squaredDepth_le x hx
  · exact squaredDepth_nonneg L ⟨x, hx⟩ x

theorem bwM_integerSum {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) : IntegerSum8 x := by
  rcases hx with ⟨w, hw, rfl⟩
  have he : Even (∑ i, w i) := by
    apply ZMod.intCast_eq_zero_iff_even.mp
    rw [Int.cast_sum, binary_sum_eq_weight]
    exact (inRM3_even_weight hw).natCast_zmod_two
  obtain ⟨k, hk⟩ := he
  refine ⟨k, ?_⟩
  rw [← Finset.sum_div, ← Int.cast_sum, hk]
  push_cast
  ring

theorem integerSum_sub {x y : Fin 8 → ℝ} (hx : IntegerSum8 x) (hy : IntegerSum8 y) :
    IntegerSum8 (x - y) := by
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha, hb, Int.cast_sub]

theorem quarterGrid_iff_folded (x : Fin 8 → ℝ) :
    QuarterGrid8 x ↔ ∀ i, foldedRadius x i = 1 / 4 := by
  constructor
  · intro hx i
    obtain ⟨k, hk⟩ := hx i
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · have hi : x i = (m : ℝ) + 1 / 4 := by rw [hk, hm]; push_cast; ring
      have hr : round (1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
      have hxround : round (x i) = m := by
        rw [hi, round_intCast_add, hr, add_zero]
      change |x i - (round (x i) : ℝ)| = 1 / 4
      rw [hxround, hi, add_sub_cancel_left]
      norm_num
    · have hi : x i = ((m + 1 : ℤ) : ℝ) - 1 / 4 := by rw [hk, hm]; push_cast; ring
      have hr : round (-1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
      have hi' : x i = ((m + 1 : ℤ) : ℝ) + (-1 / 4 : ℝ) := by linarith
      have hxround : round (x i) = m + 1 := by
        rw [hi', round_intCast_add, hr, add_zero]
      change |x i - (round (x i) : ℝ)| = 1 / 4
      rw [hxround, hi', add_sub_cancel_left]
      norm_num
  · intro hx i
    have hi := hx i
    unfold foldedRadius at hi
    by_cases h : 0 ≤ x i - (roundedInt x i : ℝ)
    · rw [abs_of_nonneg h] at hi
      refine ⟨2 * roundedInt x i, ?_⟩
      push_cast
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)] at hi
      refine ⟨2 * roundedInt x i - 1, ?_⟩
      push_cast
      linarith

theorem quarterGrid_sub_bwM {x g : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hg : g ∈ bwMSet) : QuarterGrid8 (x - g) := by
  rcases hg with ⟨w, hw, rfl⟩
  intro i
  obtain ⟨k, hk⟩ := hx i
  refine ⟨k - w i, ?_⟩
  simp only [Pi.sub_apply, hk, Int.cast_sub]
  ring

/-- The two nearest integer parities of a quarter vector are linked to its sum. -/
theorem quarter_coordinate_sum_identity {x : Fin 8 → ℝ}
    (hx : ∀ i, foldedRadius x i = 1 / 4) :
    2 * (∑ i, x i) = ((∑ i, roundedInt x i) : ℝ) +
      ((∑ i, halfRoundedInt x i) : ℝ) + 4 := by
  have hi (i : Fin 8) : 2 * x i = (roundedInt x i : ℝ) + (halfRoundedInt x i : ℝ) + 1 / 2 := by
    have hr := hx i
    unfold foldedRadius at hr
    by_cases h : 0 ≤ x i - (roundedInt x i : ℝ)
    · rw [abs_of_nonneg h] at hr
      simp only [halfRoundedInt, if_pos h, add_zero]
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)] at hr
      simp only [halfRoundedInt, if_neg h, Int.cast_add, Int.cast_neg, Int.cast_one]
      linarith
  calc
    _ = ∑ i, 2 * x i := Finset.mul_sum ..
    _ = ∑ i, ((roundedInt x i : ℝ) + (halfRoundedInt x i : ℝ) + 1 / 2) :=
      Finset.sum_congr rfl (fun i _ => hi i)
    _ = _ := by norm_num [Finset.sum_add_distrib]

theorem quarter_integerSum_of_both_odd {x : Fin 8 → ℝ}
    (hx : ∀ i, foldedRadius x i = 1 / 4)
    (hi : ¬Even (∑ i, roundedInt x i)) (hh : ¬Even (∑ i, halfRoundedInt x i)) : IntegerSum8 x := by
  have he : Even ((∑ i, roundedInt x i) + (∑ i, halfRoundedInt x i) + 4) :=
    ((Int.not_even_iff_odd.mp hi).add_odd (Int.not_even_iff_odd.mp hh)).add (by decide)
  obtain ⟨k, hk⟩ := he
  refine ⟨k, ?_⟩
  have hs := quarter_coordinate_sum_identity hx
  have hcast : ((∑ i, roundedInt x i) : ℝ) + ((∑ i, halfRoundedInt x i) : ℝ) + 4 =
      (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
  linarith

theorem quarter_parities_equiv {x : Fin 8 → ℝ} (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    Even (∑ i, roundedInt x i) ↔ Even (∑ i, halfRoundedInt x i) := by
  have hr := (quarterGrid_iff_folded x).mp hx
  rcases hs with ⟨k, hk⟩
  have hsum : 2 * k = (∑ i, roundedInt x i) + (∑ i, halfRoundedInt x i) + 4 := by
    exact_mod_cast (show 2 * (k : ℝ) = ((∑ i, roundedInt x i) : ℝ) +
      ((∑ i, halfRoundedInt x i) : ℝ) + 4 by rw [← hk]; exact quarter_coordinate_sum_identity hr)
  have h : Even ((∑ i, roundedInt x i) + (∑ i, halfRoundedInt x i)) := by
    have he : Even (2 * k - 4) := (even_two.mul_right k).sub (by decide)
    convert he using 1 <;> omega
  exact Int.even_add.mp h

theorem quarter_two_depths {x : Fin 8 → ℝ} (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    squaredDepth (dPlusSet 8) x = 1 / 2 ∨ squaredDepth (dPlusSet 8) x = 1 := by
  have hr := (quarterGrid_iff_folded x).mp hx
  have hp := quarter_parities_equiv hx hs
  have hd := squaredDepth_dPlus_of_constant x 0 (1 / 4) hr
  by_cases he : Even (∑ i, roundedInt x i)
  · left
    norm_num [he, hp.mp he] at hd
    exact hd
  · right
    have he' : ¬Even (∑ i, halfRoundedInt x i) := fun h => he (hp.mpr h)
    norm_num [he, he'] at hd
    exact hd

theorem foldedRadius_integer_halfWord (m : Fin 8 → ℤ) (c : BinaryWord8) (i : Fin 8) :
    foldedRadius (intVec m + halfWord c) i = (halfWord c) i := by
  rcases binary_eq_zero_or_one (c i) with h | h
  · have hc := halfWord_apply_of_eq_zero h
    have hx : (intVec m + halfWord c) i = (m i : ℝ) := by
      simp only [Pi.add_apply, intVec, hc, add_zero]
    have hr := (foldedRadius_eq_zero_iff _ i).mpr ⟨m i, hx⟩
    simpa only [hc] using hr
  · have hc := halfWord_apply_of_eq_one h
    have hx : (intVec m + halfWord c) i = (m i : ℝ) + 1 / 2 := by
      simp only [Pi.add_apply, intVec, hc]
    have hr := (foldedRadius_eq_half_iff _ i).mpr ⟨m i, hx⟩
    simpa only [hc] using hr

theorem nonintegerCount_integer_halfWord (m : Fin 8 → ℤ) (c : BinaryWord8) :
    nonintegerCount (intVec m + halfWord c) = binaryWeight c := by
  classical
  unfold nonintegerCount binaryWeight
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← foldedRadius_eq_zero_iff, foldedRadius_integer_halfWord]
  rcases binary_eq_zero_or_one (c i) with h | h
  · norm_num [halfWord_apply_of_eq_zero h, h]
  · norm_num [halfWord_apply_of_eq_one h, h]

/-- Every point of the full half-grid has an actual integer part and binary word. -/
theorem halfGrid_integer_halfWord {x : Fin 8 → ℝ} (hx : HalfIntegerGrid x) :
    ∃ m : Fin 8 → ℤ, ∃ c : BinaryWord8, x = intVec m + halfWord c := by
  choose w hw using hx
  let c : BinaryWord8 := fun i => (w i : Binary)
  let m : Fin 8 → ℤ := fun i => (w i - (c i).val) / 2
  have hi (i : Fin 8) : 2 * m i = w i - (c i).val := by
    apply Int.mul_ediv_cancel'
    apply even_iff_two_dvd.mp
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sub, binary_val_cast, c, sub_self]
  refine ⟨m, c, ?_⟩
  funext i
  change x i = (m i : ℝ) + ((c i).val : ℝ) / 2
  rw [hw i]
  have h : 2 * (m i : ℝ) = (w i : ℝ) - ((c i).val : ℝ) := by exact_mod_cast hi i
  linarith

theorem halfWord_sub_representation (c d : BinaryWord8) :
    ∃ m : Fin 8 → ℤ, halfWord c - halfWord d = intVec m + halfWord (fun i => c i - d i) := by
  let e : BinaryWord8 := fun i => c i - d i
  let m : Fin 8 → ℤ := fun i => ((c i).val - (d i).val - (e i).val : ℤ) / 2
  have hi (i : Fin 8) : 2 * m i = ((c i).val - (d i).val - (e i).val : ℤ) := by
    apply Int.mul_ediv_cancel'
    apply even_iff_two_dvd.mp
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sub, binary_val_cast, e, sub_self]
  refine ⟨m, ?_⟩
  funext i
  change ((c i).val : ℝ) / 2 - ((d i).val : ℝ) / 2 = (m i : ℝ) + ((e i).val : ℝ) / 2
  have h : 2 * (m i : ℝ) = ((c i).val : ℝ) - ((d i).val : ℝ) - ((e i).val : ℝ) := by exact_mod_cast hi i
  linarith

theorem halfWord_depth (m : Fin 8 → ℤ) (c : BinaryWord8)
    (hc0 : 0 < binaryWeight c) (hc8 : binaryWeight c < 8) :
    squaredDepth (dPlusSet 8) (intVec m + halfWord c) =
      min ((binaryWeight c : ℝ) / 4) ((8 - (binaryWeight c : ℝ)) / 4) := by
  classical
  have h0 : ∃ i, c i = 0 := by
    by_contra h
    push_neg at h
    have hh : ∀ i, c i = 1 := fun i => (binary_eq_zero_or_one _).resolve_left (h i)
    have hw := (binary_weight_eight_iff c).mpr hh
    omega
  have h1 : ∃ i, c i = 1 := by
    by_contra h
    push_neg at h
    have hh : ∀ i, c i = 0 := fun i => (binary_eq_zero_or_one _).resolve_right (h i)
    have hw := (binary_weight_zero_iff c).mpr hh
    omega
  obtain ⟨lo, hlo⟩ := h0
  obtain ⟨hi, hhi⟩ := h1
  have hr0 : foldedRadius (intVec m + halfWord c) lo = 0 := by
    rw [foldedRadius_integer_halfWord]
    exact halfWord_apply_of_eq_zero hlo
  have hr1 : foldedRadius (intVec m + halfWord c) hi = 1 / 2 := by
    rw [foldedRadius_integer_halfWord]
    exact halfWord_apply_of_eq_one hhi
  have hd := squaredDepth_dPlus_eq (intVec m + halfWord c) lo hi
    (fun i => by rw [hr0]; exact foldedRadius_nonneg _ i)
    (fun i => by rw [hr1]; exact foldedRadius_le_half _ i)
  have hbase : integerBaseCost (intVec m + halfWord c) = (binaryWeight c : ℝ) / 4 := by
    have hs (i : Fin 8) : (foldedRadius (intVec m + halfWord c) i) ^ 2 =
        if c i = 1 then 1 / 4 else 0 := by
      rw [foldedRadius_integer_halfWord]
      rcases binary_eq_zero_or_one (c i) with h | h
      · norm_num [halfWord_apply_of_eq_zero h, h]
      · norm_num [halfWord_apply_of_eq_one h, h]
    simp only [integerBaseCost, hs]
    simp [Finset.sum_ite, binaryWeight, div_eq_mul_inv]
  have hsum : (∑ i, foldedRadius (intVec m + halfWord c) i) = (binaryWeight c : ℝ) / 2 := by
    rw [folded_sum_eq_nonintegerCount]
    · rw [nonintegerCount_integer_halfWord]
    · intro i
      rw [foldedRadius_integer_halfWord]
      rcases binary_eq_zero_or_one (c i) with h | h
      · norm_num [halfWord_apply_of_eq_zero h, h]
      · norm_num [halfWord_apply_of_eq_one h, h]
  rw [integerRepairCost, halfRepairCost, hr0, hr1] at hd
  norm_num at hd
  rw [hbase, halfBaseCost_eq, hbase, hsum] at hd
  convert hd using 1 <;> congr 1 <;> ring

theorem balanced_outside_bwM_translates_two_depths {x g : Fin 8 → ℝ}
    (hx : BalancedHalfGrid x) (hxM : x ∉ bwMSet) (hg : g ∈ bwMSet) :
    squaredDepth (dPlusSet 8) (x - g) = 1 / 2 ∨ squaredDepth (dPlusSet 8) (x - g) = 1 := by
  have hgrid := (balancedHalfGrid_iff_paperHalfGrid (by decide : Even 8) x).mp hx
  obtain ⟨m, c, rfl⟩ := halfGrid_integer_halfWord hgrid.1
  have hc : binaryWeight c = 4 := by
    have hcount := hgrid.2
    norm_num [nonintegerCount_integer_halfWord] at hcount
    exact hcount
  have hnc : ¬InRM3 c := fun h => hxM (bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM h))
  obtain ⟨k, d, hd, rfl⟩ := (bwMSet_iff_integer_halfCode g).mp hg
  obtain ⟨a, ha⟩ := halfWord_sub_representation c d
  have heq : (intVec m + halfWord c) - (intVec k + halfWord d) =
      intVec (m - k + a) + halfWord (fun i => c i - d i) := by
    have hsplit : (intVec m + halfWord c) - (intVec k + halfWord d) =
        intVec (m - k) + (halfWord c - halfWord d) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, intVec, Int.cast_sub]
      ring
    rw [hsplit, ha, ← add_assoc, ← intVec_add]
  rw [heq]
  rcases eligible_word_difference_weights hc hnc hd with hw | hw | hw
  all_goals
    have hv := halfWord_depth (m - k + a) (fun i => c i - d i)
      (by rw [hw]; norm_num) (by rw [hw]; norm_num)
  · left
    norm_num [hw] at hv
    exact hv
  · right
    norm_num [hw] at hv
    exact hv
  · left
    norm_num [hw] at hv
    exact hv

/-- All translates of an eligible E8 hole have one of the two exact depths. -/
theorem e8_hole_bwMdeep_translates_two_depths {x g : Fin 8 → ℝ}
    (hx : E8FoldedHole x) (hM : squaredDepth bwMSet x = 1 / 2) (hg : g ∈ bwMSet) :
    squaredDepth (dPlusSet 8) (x - g) = 1 / 2 ∨ squaredDepth (dPlusSet 8) (x - g) = 1 := by
  have hxM : x ∉ bwMSet := by
    intro hxM
    have hzero := squaredDepth_zero_of_mem hxM
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
  · exact balanced_outside_bwM_translates_two_depths hb hxM hg
  · exact quarter_two_depths (quarterGrid_sub_bwM ((quarterGrid_iff_folded x).mpr hr) hg)
      (integerSum_sub (quarter_integerSum_of_both_odd hr hp hq) (bwM_integerSum hg))

def BWEligible (x : Fin 8 → ℝ) : Prop :=
  squaredDepth bwMSet x = 1 / 2 ∧ ∃ q : BWQuotient, bwDepthProfile x q = 1

theorem bwEligible_profile_two_depths {x : Fin 8 → ℝ} (hx : BWEligible x) (q : BWQuotient) :
    bwDepthProfile x q = 1 / 2 ∨ bwDepthProfile x q = 1 := by
  obtain ⟨q₀, hq₀⟩ := hx.2
  have hh : E8FoldedHole (x - bwRepresentative q₀) :=
    (squaredDepth_E8_eq_one_iff _).mp hq₀
  have hM : squaredDepth bwMSet (x - bwRepresentative q₀) = 1 / 2 := by
    change squaredDepth (bwMAddSubgroup : Set (Fin 8 → ℝ))
      (x - bwRepresentative q₀) = 1 / 2
    rw [squaredDepth_sub_of_subgroup bwMAddSubgroup x (bwRepresentative q₀) (bwRepresentative_mem q₀)]
    exact hx.1
  have hg : bwRepresentative q - bwRepresentative q₀ ∈ bwMSet :=
    bwMAddSubgroup.sub_mem (bwRepresentative_mem q) (bwRepresentative_mem q₀)
  have h := e8_hole_bwMdeep_translates_two_depths hh hM hg
  have heq : x - bwRepresentative q₀ - (bwRepresentative q - bwRepresentative q₀) =
      x - bwRepresentative q := by abel
  simpa only [heq, bwDepthProfile] using h

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e8_hole_bwMdeep_translates_two_depths
#print axioms PaperVerification.ColdSpots.bwEligible_profile_two_depths
