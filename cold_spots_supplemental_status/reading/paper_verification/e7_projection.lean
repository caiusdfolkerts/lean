module
public import PaperVerification.E7Coordinates
public import PaperVerification.GaussianExtrema
public import PaperVerification.LatticeGeometry
public import Mathlib.Algebra.Ring.Int.Parity
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e7Gaussian (α : ℝ) (x : zeroSumSpace) : ℝ :=
  ∑' y : e7ProjectedSet, Real.exp (-α * sqDist y.val.val x.val)

def e7SquaredDepth (x : zeroSumSpace) : ℝ :=
  sInf ((fun y : zeroSumSpace ↦ sqDist x.val y.val) '' e7ProjectedSet)

def IsE7ColdSpot (α : ℝ) (x : zeroSumSpace) : Prop :=
  ∀ y : zeroSumSpace, e7Gaussian α x ≤ e7Gaussian α y

def IsE7DeepHole (x : zeroSumSpace) : Prop :=
  ∀ y : zeroSumSpace, e7SquaredDepth y ≤ e7SquaredDepth x

def e7Slice (x : zeroSumSpace) : Fin 8 → ℝ := fun i ↦ x i + 1 / 8

def e7FibreOffset (y : e7ProjectedSet) : ℝ := (∑ i, (e7Lift y i : ℝ)) / 4

lemma e7FibreOffset_half_integer (y : e7ProjectedSet) :
    ∃ l : ℤ, e7FibreOffset y = (l : ℝ) / 2 := by
  obtain ⟨l, hl⟩ := e7Lift_even y
  refine ⟨l, ?_⟩
  unfold e7FibreOffset
  have hc : (∑ i, (e7Lift y i : ℝ)) = (l : ℝ) + l := by exact_mod_cast hl
  rw [hc]
  ring

theorem sqDist_e8Fibre_slice (y : e7ProjectedSet) (k : ℤ) (x : zeroSumSpace) :
    sqDist (e8FibreMap (y, k)).val (e7Slice x) =
      sqDist y.val.val x.val + 2 * ((k : ℝ) + e7FibreOffset y - 1 / 4) ^ 2 := by
  have hy (i : Fin 8) : (e7Lift y i : ℝ) =
      y.val i + e7FibreOffset y / 2 := by
    have h := congrFun (congrArg Subtype.val (e7Lift_projects y)) i
    simp only [project8_apply, intVec] at h
    unfold e7FibreOffset
    linarith
  have hsum : (∑ i, (y.val i - x i)) = 0 := by
    rw [Finset.sum_sub_distrib, zeroSumSpace_sum, zeroSumSpace_sum, sub_self]
  unfold sqDist e8FibreMap e7Slice
  simp only [hy]
  have hterm (i : Fin 8) :
      (y.val i + e7FibreOffset y / 2 + (k : ℝ) / 2 - (x i + 1 / 8)) ^ 2 =
        (y.val i - x i) ^ 2 +
        (y.val i - x i) * ((k : ℝ) + e7FibreOffset y - 1 / 4) +
        ((k : ℝ) + e7FibreOffset y - 1 / 4) ^ 2 / 4 := by ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma gaussian_quarter_half_integer_shift (α : ℝ) (l : ℤ) :
    gaussian α (1 / 4 - (l : ℝ) / 2) = gaussian α (1 / 4) := by
  rcases Int.even_or_odd l with ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [hq]
    push_cast
    rw [show (1 / 4 : ℝ) - ((q : ℝ) + q) / 2 = 1 / 4 + (-q : ℤ) by
      push_cast; ring, gaussian_int_period]
  · rw [hq]
    push_cast
    rw [show (1 / 4 : ℝ) - (2 * (q : ℝ) + 1) / 2 = -(1 / 4) + (-q : ℤ) by
      push_cast; ring, gaussian_int_period, gaussian_even]

lemma hasSum_e8_fibre {α : ℝ} (hα : 0 < α) (y : e7ProjectedSet) (x : zeroSumSpace) :
    HasSum (fun k : ℤ ↦ Real.exp (-α * sqDist (e8FibreMap (y, k)).val (e7Slice x)))
      (gaussian (2 * α) (1 / 4) * Real.exp (-α * sqDist y.val.val x.val)) := by
  have h2 : 0 < 2 * α := by positivity
  obtain ⟨l, hl⟩ := e7FibreOffset_half_integer y
  have h := (hasSum_gaussian h2 (1 / 4 - e7FibreOffset y)).mul_right
    (Real.exp (-α * sqDist y.val.val x.val))
  rw [hl, gaussian_quarter_half_integer_shift] at h
  convert h using 1
  funext k
  rw [sqDist_e8Fibre_slice, hl, ← Real.exp_add]
  congr 1
  ring

theorem summable_setGaussian_dPlus {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    Summable (fun z : dPlusSet n ↦ Real.exp (-α * sqDist z.val x)) := by
  let f : dPlusSet n → ℝ := fun z ↦ Real.exp (-α * sqDist z.val x)
  have hl : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inl z)))
      (dGaussian α x) := (summable_dGaussian hα x).hasSum
  have hr : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inr z)))
      (dGaussian α (fun i ↦ x i - 1 / 2)) := by
    change HasSum (fun z : EvenTuple n ↦
      Real.exp (-α * sqDist (fun i ↦ (z.val i : ℝ) + 1 / 2) x)) _
    simp only [sqDist_half_shift]
    exact (summable_dGaussian hα _).hasSum
  exact (((dPlusTagEquiv hn).hasSum_iff (f := f)).mp (hl.sum hr)).summable

/-- Equation (25): exact factorization of convergent Gaussian sums. -/
theorem e8_slice_gaussian_factorization {α : ℝ} (hα : 0 < α) (x : zeroSumSpace) :
    setGaussian (dPlusSet 8) α (e7Slice x) =
      gaussian (2 * α) (1 / 4) * e7Gaussian α x := by
  have hs := summable_setGaussian_dPlus (by decide : 0 < 8) hα (e7Slice x)
  have hsum := (e8FibreEquiv.hasSum_iff
    (f := fun z : dPlusSet 8 ↦ Real.exp (-α * sqDist z.val (e7Slice x)))).mpr hs.hasSum
  have houter := hsum.prod_fiberwise (fun y ↦ hasSum_e8_fibre hα y x)
  have heq := houter.tsum_eq
  rw [tsum_mul_left] at heq
  exact heq.symm

theorem summable_e7Gaussian {α : ℝ} (hα : 0 < α) (x : zeroSumSpace) :
    Summable (fun y : e7ProjectedSet ↦ Real.exp (-α * sqDist y.val.val x.val)) := by
  have hs := summable_setGaussian_dPlus (by decide : 0 < 8) hα (e7Slice x)
  have hsum := (e8FibreEquiv.hasSum_iff
    (f := fun z : dPlusSet 8 ↦ Real.exp (-α * sqDist z.val (e7Slice x)))).mpr hs.hasSum
  have houter := (hsum.prod_fiberwise (fun y ↦ hasSum_e8_fibre hα y x)).summable
  exact (summable_mul_left_iff (gaussian_pos (show 0 < 2 * α by positivity) _).ne').mp houter

lemma half_integer_quarter_distance_lower (k l : ℤ) :
    (1 / 8 : ℝ) ≤ 2 * ((k : ℝ) + (l : ℝ) / 2 - 1 / 4) ^ 2 := by
  rcases le_or_gt (2 * k + l) 0 with h | h
  · have hr : (2 : ℝ) * k + l ≤ 0 := by exact_mod_cast h
    have ht : (k : ℝ) + (l : ℝ) / 2 - 1 / 4 ≤ -(1 / 4 : ℝ) := by linarith
    nlinarith [sq_nonneg ((k : ℝ) + (l : ℝ) / 2)]
  · have hr : (1 : ℝ) ≤ 2 * k + l := by exact_mod_cast (show (1 : ℤ) ≤ 2 * k + l by omega)
    have ht : (1 / 4 : ℝ) ≤ (k : ℝ) + (l : ℝ) / 2 - 1 / 4 := by linarith
    nlinarith [sq_nonneg ((k : ℝ) + (l : ℝ) / 2 - 1 / 2)]

lemma exists_half_integer_quarter_distance_eq (l : ℤ) :
    ∃ k : ℤ, 2 * ((k : ℝ) + (l : ℝ) / 2 - 1 / 4) ^ 2 = 1 / 8 := by
  rcases Int.even_or_odd l with ⟨q, hq⟩ | ⟨q, hq⟩
  · refine ⟨-q, ?_⟩
    rw [hq]
    push_cast
    ring
  · refine ⟨-q, ?_⟩
    rw [hq]
    push_cast
    ring

lemma e7Projected_nonempty : e7ProjectedSet.Nonempty :=
  ⟨project8 (intVec 0), ⟨0, by simp, rfl⟩⟩

lemma e7SquaredDepth_le (x : zeroSumSpace) {y : zeroSumSpace} (hy : y ∈ e7ProjectedSet) :
    e7SquaredDepth x ≤ sqDist x.val y.val :=
  csInf_le ⟨0, by rintro r ⟨z, hz, rfl⟩; exact sqDist_nonneg _ _⟩ ⟨y, hy, rfl⟩

/-- The squared-distance identity is proved directly, independently of a
large-parameter asymptotic argument. -/
theorem e8_slice_depth_factorization (x : zeroSumSpace) :
    squaredDepth (dPlusSet 8) (e7Slice x) = e7SquaredDepth x + 1 / 8 := by
  apply le_antisymm
  · have hle : squaredDepth (dPlusSet 8) (e7Slice x) - 1 / 8 ≤ e7SquaredDepth x := by
      apply le_csInf (e7Projected_nonempty.image _)
      rintro d ⟨y, hy, rfl⟩
      let y' : e7ProjectedSet := ⟨y, hy⟩
      obtain ⟨l, hl⟩ := e7FibreOffset_half_integer y'
      obtain ⟨k, hk⟩ := exists_half_integer_quarter_distance_eq l
      have h := squaredDepth_le (e7Slice x) (e8FibreMap (y', k)).property
      rw [sqDist_comm, sqDist_e8Fibre_slice, hl, hk, sqDist_comm] at h
      linarith
    linarith
  · apply le_csInf ((dPlusSet_nonempty 8).image _)
    rintro d ⟨v, hv, rfl⟩
    obtain ⟨⟨y, k⟩, heq⟩ := e8FibreMap_bijective.surjective ⟨v, hv⟩
    have heqv := congrArg Subtype.val heq
    change (e8FibreMap (y, k)).val = v at heqv
    change e7SquaredDepth x + 1 / 8 ≤ sqDist (e7Slice x) v
    rw [← heqv, sqDist_comm, sqDist_e8Fibre_slice]
    obtain ⟨l, hl⟩ := e7FibreOffset_half_integer y
    have hbase := e7SquaredDepth_le x y.property
    rw [sqDist_comm] at hbase
    rw [hl]
    linarith [half_integer_quarter_distance_lower k l]

theorem e7SquaredDepth_le_seven_eighths (x : zeroSumSpace) : e7SquaredDepth x ≤ 7 / 8 := by
  have h := squaredDepth_dPlus_le (n := 8) (by decide) (e7Slice x)
  rw [e8_slice_depth_factorization] at h
  norm_num at h
  linarith

end PaperVerification.ColdSpots
