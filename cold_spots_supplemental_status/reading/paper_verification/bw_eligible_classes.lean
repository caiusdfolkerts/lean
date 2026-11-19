module

public import PaperVerification.BWCanonical


@[expose] public section
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
