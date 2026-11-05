module

public import PaperVerification.E8BinaryClasses
public import PaperVerification.BWEligibility


@[expose] public section
/-! # The 135 actual E8 deep-hole classes

Every real deep hole doubles to an E8 point.  Its coordinates in the explicit
integral root basis determine a nonzero isotropic binary vector.  Conversely
every such vector is a deepest half-lattice point.  This identifies the actual
translation quotient, rather than just counting a finite surrogate.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem e8_deep_double_mem {x : Fin 8 → ℝ} (hx : IsDeepHole (dPlusSet 8) x) :
    (fun i => 2 * x i) ∈ dPlusSet 8 := by
  rcases (isDeepHole_E8_iff x).mp hx with ⟨hr, hp⟩ | ⟨hr, hp⟩ | hb | ⟨hr, hp, hq⟩
  · refine ⟨fun i => 2 * roundedInt x i, ?_, Or.inl ?_⟩
    · rw [← Finset.mul_sum]
      exact even_two.mul_right _
    · funext i
      have hi : x i = (roundedInt x i : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp (hr i))
      simp [intVec, hi]
  · refine ⟨fun i => 2 * halfRoundedInt x i + 1, ?_, Or.inl ?_⟩
    · have he : Even (2 * (∑ i, halfRoundedInt x i) + 8) :=
        (even_two.mul_right _).add (by decide)
      simpa [Finset.sum_add_distrib, ← Finset.mul_sum] using he
    · funext i
      have hi := abs_sub_halfRoundedInt x i
      rw [hr i, sub_self] at hi
      have he : x i = (halfRoundedInt x i : ℝ) + 1 / 2 := sub_eq_zero.mp (abs_eq_zero.mp hi)
      simp [intVec, he]
      ring
  · have hgrid := (balancedHalfGrid_iff_paperHalfGrid (by decide : Even 8) x).mp hb
    obtain ⟨m, c, rfl⟩ := halfGrid_integer_halfWord hgrid.1
    have hc4 : binaryWeight c = 4 := by
      have hcount := hgrid.2
      norm_num [nonintegerCount_integer_halfWord] at hcount
      exact hcount
    refine ⟨fun i => 2 * m i + (c i).val, ?_, Or.inl ?_⟩
    · have he : Even (2 * (∑ i, m i) + 4) := (even_two.mul_right _).add (by decide)
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum,
        sum_binary_val, hc4, Nat.cast_ofNat] using he
    · funext i
      simp only [Pi.add_apply, intVec, halfWord, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast]
      ring
  · refine ⟨roundedInt x + halfRoundedInt x, ?_, Or.inr ?_⟩
    · simpa only [Pi.add_apply, Finset.sum_add_distrib] using
        (Int.not_even_iff_odd.mp hp).add_odd (Int.not_even_iff_odd.mp hq)
    · funext i
      have hri := hr i
      unfold foldedRadius at hri
      by_cases hs : 0 ≤ x i - (roundedInt x i : ℝ)
      · rw [abs_of_nonneg hs] at hri
        simp only [Pi.add_apply, halfRoundedInt, if_pos hs, add_zero, Int.cast_add]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hs)] at hri
        simp only [Pi.add_apply, halfRoundedInt, if_neg hs, Int.cast_add,
          Int.cast_neg, Int.cast_one]
        linarith

theorem e8_halfRoot_coordinates_of_deep {x : Fin 8 → ℝ} (hx : IsDeepHole (dPlusSet 8) x) :
    ∃ t : Fin 8 → ℤ, x = e8HalfRootSum t := by
  obtain ⟨t, ht⟩ := (e8_mem_iff_integer_root_coordinates _).mp (e8_deep_double_mem hx)
  refine ⟨t, ?_⟩
  have he := e8HalfRootSum_double t
  funext i
  have h₁ := congrFun ht i
  have h₂ := congrFun he i
  linarith

theorem e8_deep_halfRoot_binary {t : Fin 8 → ℤ} (hx : IsDeepHole (dPlusSet 8) (e8HalfRootSum t)) :
    e8BinaryQ (fun i => (t i : Binary)) = 0 ∧ (fun i => (t i : Binary)) ≠ 0 := by
  have hdepth : squaredDepth (dPlusSet 8) (e8HalfRootSum t) = 1 :=
    (squaredDepth_E8_eq_one_iff _).mpr ((isDeepHole_E8_iff _).mp hx)
  constructor
  · obtain ⟨y, hy, hdist⟩ := exists_nearest_dPlus (by decide : 0 < 8) (e8HalfRootSum t)
    obtain ⟨k, rfl⟩ := (e8_mem_iff_integer_root_coordinates y).mp hy
    let u : Fin 8 → ℤ := t - fun i => 2 * k i
    have hd : sqDist (e8HalfRootSum t) (e8RootSum (fun i => (k i : ℝ))) =
        (e8IntegralQ u : ℝ) / 2 := by
      rw [← e8HalfRootSum_two k, ← sqDist_sub_zero, ← e8HalfRootSum_sub, e8HalfRootSum_norm]
    have hQ : e8IntegralQ u = 2 := by
      rw [hd, hdepth] at hdist
      exact_mod_cast (show (e8IntegralQ u : ℝ) = 2 by linarith)
    have hu : (fun i => (u i : Binary)) = fun i => (t i : Binary) := by
      funext i
      simp [u]
    have hcast := congrArg (fun z : ℤ => (z : Binary)) hQ
    rw [e8IntegralQ_cast, hu] at hcast
    simpa using hcast
  · intro hzero
    have hmem : e8HalfRootSum t ∈ dPlusSet 8 := by
      apply (e8HalfRootSum_mem_iff t).mpr
      intro i
      apply ZMod.intCast_eq_zero_iff_even.mp
      exact congrFun hzero i
    have hz := squaredDepth_zero_of_mem hmem
    linarith

def e8DeepClassMap (c : E8HoleIndex) : DeepTranslationClasses (dPlusAddSubgroup 8 (by decide)) :=
  ⟨(e8ClassPoint c.val : (Fin 8 → ℝ) ⧸ dPlusAddSubgroup 8 (by decide)),
    e8ClassPoint c.val, e8ClassPoint_deep c, rfl⟩

theorem e8DeepClassMap_bijective : Function.Bijective e8DeepClassMap := by
  constructor
  · intro c d h
    apply Subtype.ext
    apply (e8ClassPoint_sub_mem_iff c.val d.val).mp
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, x, hx, hC⟩
    obtain ⟨t, rfl⟩ := e8_halfRoot_coordinates_of_deep hx
    let c : E8HoleIndex := ⟨fun i => (t i : Binary), e8_deep_halfRoot_binary hx⟩
    refine ⟨c, Subtype.ext ?_⟩
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr (e8HalfRootSum_class t)).symm.trans hC

def e8DeepClassEquiv : E8HoleIndex ≃ DeepTranslationClasses (dPlusAddSubgroup 8 (by decide)) :=
  Equiv.ofBijective e8DeepClassMap e8DeepClassMap_bijective

theorem e8_deep_translation_class_count :
    Nat.card (DeepTranslationClasses (dPlusAddSubgroup 8 (by decide))) = 135 := by
  rw [← Nat.card_congr e8DeepClassEquiv, Nat.card_eq_fintype_card, card_e8HoleIndex]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e8_deep_translation_class_count
