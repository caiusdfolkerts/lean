module

public import VolumePolynomials.BerwaldMoments

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The sharp second-moment inequality for bounded concave functions

All moments are uniform Lebesgue averages over the actual convex domain.
No regularity at its boundary, strict positivity of the function, or
attainment of its supremum is assumed.
-/

open Set MeasureTheory Module

namespace VolumePolynomials

open BerwaldComparison BerwaldLevelSets BerwaldMoments

def berwaldConstant (k : ℕ) : ℝ := 2 * (k + 1 : ℝ) / (k + 2 : ℝ)

def uniformAverage {E : Type*} [MeasurableSpace E] [MeasureSpace E]
    (Z : Set E) (f : E → ℝ) : ℝ := (∫ x in Z, f x) / volume.real Z

/-- The scalar assertion of Lemma 6.1, in arbitrary positive finite
dimension. The positive volume assumption specifies the uniform averaging
operation already required in the paper's notation. -/
theorem sharp_berwald_second_moment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : 0 < finrank ℝ E) {Z : Set E} (hZ : IsCompact Z)
    (hvol : 0 < volume.real Z) {f : E → ℝ} (hf : ConcaveOn ℝ Z f)
    (hn : ∀ x ∈ Z, 0 ≤ f x) (hb : BddAbove (f '' Z)) :
    uniformAverage Z (fun x => f x ^ 2) ≤
      berwaldConstant (finrank ℝ E) * uniformAverage Z f ^ 2 := by
  first
  | have hne : Z.Nonempty := by
      first
      | by_contra h
        have hz : Z = ∅ := not_nonempty_iff_eq_empty.mp h
        simpa only [hz, measureReal_empty, lt_self_iff_false] using hvol
    let M : ℝ := sSup (f '' Z)
    have hM0 : 0 ≤ M := by
      first
      | obtain ⟨x, hx⟩ := hne
        exact (hn x hx).trans (le_csSup hb ⟨x, hx, rfl⟩)
    by_cases hM : M = 0
    · have hzero : ∀ x ∈ Z, f x = 0 := by
        first
        | intro x hx
          apply le_antisymm _ (hn x hx)
          have hfx : f x ≤ M := le_csSup hb ⟨x, hx, rfl⟩
          simpa only [hM] using hfx
      have hi : (∫ x in Z, f x) = 0 := by
        first
        | calc
            (∫ x in Z, f x) = ∫ x in Z, (0 : ℝ) :=
              setIntegral_congr_fun hZ.measurableSet hzero
            _ = 0 := integral_zero _ _
      have hi2 : (∫ x in Z, f x ^ 2) = 0 := by
        first
        | calc
            (∫ x in Z, f x ^ 2) = ∫ x in Z, (0 : ℝ) := by
              apply setIntegral_congr_fun hZ.measurableSet
              intro x hx
              change f x ^ 2 = 0
              rw [hzero x hx, zero_pow (by decide : 2 ≠ 0)]
            _ = 0 := integral_zero _ _
      simp only [uniformAverage, hi, hi2, zero_div, zero_pow (by decide : 2 ≠ 0),
        mul_zero, le_refl]
    · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
      have hconc := rootTail_concave_nonnegative hdim.ne' hZ hne hvol hf
      have hpow : ∀ t ∈ Ico 0 M, clippedTail Z f t = rootTail Z f t ^ finrank ℝ E := by
        first
        | intro t ht
          rw [clippedTail, if_pos ht.2, rootTail_pow hdim.ne', tail]
      have hz : ∀ t, M ≤ t → clippedTail Z f t = 0 := by
        first
        | intro t ht
          exact if_neg (not_lt.mpr ht)
      have hbound := sharp_moment_bound hdim hMpos
        (rootTail Z f) (clippedTail Z f) hconc (rootTail_zero hvol hn)
        (fun t _ => rootTail_nonnegative Z f t) hpow hz
        (fun a _ => clippedTail_integrableOn hZ f 0 a)
        (fun _ ha => clippedTail_first_moment_integrableOn hZ f ha)
      have hfirst : uniformAverage Z f = ∫ t in Icc 0 M, clippedTail Z f t := by
        first
        | simpa only [uniformAverage, Nat.zero_add, pow_one, Nat.cast_zero,
            zero_add, pow_zero, one_mul] using
            moment_identity_bounded hZ hf hn hb (a := M) le_rfl 0
      have hsecond : uniformAverage Z (fun x => f x ^ 2) =
          2 * ∫ t in Icc 0 M, t * clippedTail Z f t := by
        first
        | simpa only [uniformAverage, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two,
            pow_one] using moment_identity_bounded hZ hf hn hb (a := M) le_rfl 1
      rw [hsecond, hfirst]
      exact hbound

end VolumePolynomials
