module
public import VolumePolynomials.RationalInterpolation
public import VolumePolynomials.VolumeLipschitz
public import Mathlib.Tactic.GCongr

@[expose] public section

set_option autoImplicit false

/-!
# A rational modulus for all ordinary coefficients

The coefficient map is controlled by the literal Hausdorff distances of the
input bodies. The constants are explicit rational expressions in the dimension,
number of bodies, box radius, and rational interpolation data. No effective
modulus is inferred merely from qualitative compactness or continuity.
-/

open Set Finset MeasureTheory Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

section Geometry

theorem exists_near_weightedSum {n d : ℕ} (K L : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {ε : ℝ}
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) {x : Space d}
    (hx : x ∈ weightedSum K t) :
    ∃ y ∈ weightedSum L t, dist x y ≤ ε * ∑ i, t i := by
  first
  | classical
    obtain ⟨a, ha, hax⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    have hpoints : ∀ i, ∃ p ∈ K i, t i • p = a i := by
      first
      | intro i
        exact Set.mem_smul_set.mp (ha i)
    choose p hp hpa using hpoints
    choose q hq hdist using fun i =>
      (L i).isCompact.exists_infDist_eq_dist (L i).nonempty (p i)
    have hpq : ∀ i, dist (p i) (q i) ≤ ε := by
      first
      | intro i
        rw [← hdist i]
        exact (infDist_le_hausdorffDist_of_mem (hp i)
          ConvexBody.hausdorffEDist_ne_top).trans (hKL i)
    have hpx : ∑ i, t i • p i = x := by
      first
      | simpa only [hpa] using hax
    refine ⟨∑ i, t i • q i, (mem_sum_body _ _).mpr
      ⟨fun i => t i • q i, fun i => ⟨q i, hq i, rfl⟩, rfl⟩, ?_⟩
    rw [← hpx, dist_eq_norm, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖t i • p i - t i • q i‖ := norm_sum_le _ _
      _ = ∑ i, t i * dist (p i) (q i) := by
        first
        | apply Finset.sum_congr rfl
          intro i _
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (ht i), dist_eq_norm]
      _ ≤ ∑ i, t i * ε := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hpq i) (ht i)
      _ = ε * ∑ i, t i := by rw [← Finset.sum_mul, mul_comm]

theorem dist_weightedSum_le {n d : ℕ} (K L : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {ε : ℝ} (hε : 0 ≤ ε)
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) :
    dist (weightedSum K t) (weightedSum L t) ≤ ε * ∑ i, t i := by
  first
  | change hausdorffDist (weightedSum K t : Set (Space d))
      (weightedSum L t : Set (Space d)) ≤ _
    exact hausdorffDist_le_of_mem_dist (mul_nonneg hε (Finset.sum_nonneg fun i _ => ht i))
      (fun _ hx => exists_near_weightedSum K L t ht hKL hx)
      (fun _ hy => exists_near_weightedSum L K t ht
        (fun i => by simpa only [dist_comm] using hKL i) hy)

theorem weightedSum_subset_box {n d : ℕ} (K : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {R : ℝ}
    (hK : ∀ i, (K i : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R)) :
    (weightedSum K t : Set (Space d)) ⊆
      Icc (fun _ => -(R * ∑ i, t i)) (fun _ => R * ∑ i, t i) := by
  first
  | intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    have hpoints : ∀ i, ∃ p ∈ K i, t i • p = a i := by
      first
      | intro i
        exact Set.mem_smul_set.mp (ha i)
    choose p hp hpa using hpoints
    have hupper (j : Fin d) : (∑ i, a i) j ≤ R * ∑ i, t i := by
      first
      | simp only [Finset.sum_apply, ← hpa, Pi.smul_apply, smul_eq_mul]
        calc
          _ ≤ ∑ i, t i * R := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ((hK i (hp i)).2 j) (ht i)
          _ = R * ∑ i, t i := by rw [← Finset.sum_mul, mul_comm]
    have hlower (j : Fin d) : -(R * ∑ i, t i) ≤ (∑ i, a i) j := by
      first
      | simp only [Finset.sum_apply, ← hpa, Pi.smul_apply, smul_eq_mul]
        calc
          _ = ∑ i, t i * -R := by rw [← Finset.sum_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ((hK i (hp i)).1 j) (ht i)
    exact ⟨hlower, hupper⟩

end Geometry

/-- One strict rational bound for the sum of every interpolation weight vector. -/
def interpolationWeightBound (n d : ℕ) : ℚ :=
  1 + ∑ j : Fin (interpolationSize n d), ∑ i : Fin n, interpolationWeight j i

theorem interpolationWeightBound_pos (n d : ℕ) : 0 < interpolationWeightBound n d := by
  first
  | exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
        (interpolationWeight_pos j i).le)

theorem interpolationWeight_sum_le {n d : ℕ} (j : Fin (interpolationSize n d)) :
    (∑ i : Fin n, interpolationWeight j i) ≤ interpolationWeightBound n d := by
  first
  | apply (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun i _ => (interpolationWeight_pos k i).le)
      (Finset.mem_univ j)).trans
    exact le_add_of_nonneg_left zero_le_one

/-- Entirely rational coefficient-modulus constant for bodies in `[-R,R]^d`. -/
def coefficientModulus (n d : ℕ) (R : ℚ) : ℚ :=
  coefficientExtractionBound n d * interpolationWeightBound n d *
    (2 * R * interpolationWeightBound n d + 2) ^ d

/-- Uniform coefficient control, including lower-dimensional bodies. The only
smallness restriction is on the approximation error, not on the geometry. -/
theorem Realizes.coefficient_sub_le_of_dist_le {n d : ℕ}
    {K L : Fin n → Body d} {c c' : Coefficients n d}
    (hc : Realizes K c) (hc' : Realizes L c') (R : ℚ) (hR : 0 ≤ R)
    (hK : ∀ i, (K i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    (hL : ∀ i, (L i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε * (interpolationWeightBound n d : ℝ) ≤ 1)
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) (α : MultiIndex n d) :
    |c α - c' α| ≤ ε * (coefficientModulus n d R : ℝ) := by
  first
  | let T : ℝ := interpolationWeightBound n d
    have hT : 0 < T := by
      first
      | dsimp [T]
        exact_mod_cast interpolationWeightBound_pos n d
    have hR' : 0 ≤ (R : ℝ) := by exact_mod_cast hR
    have hη : 0 ≤ ε * T * (2 * (R : ℝ) * T + 2) ^ d := by positivity
    have hsamples : ∀ j : Fin (interpolationSize n d),
        |evaluate c (fun i => (interpolationWeight j i : ℝ)) -
          evaluate c' (fun i => (interpolationWeight j i : ℝ))| ≤
            ε * T * (2 * (R : ℝ) * T + 2) ^ d := by
      first
      | intro j
        let t : Fin n → ℝ := fun i => interpolationWeight j i
        have ht : ∀ i, 0 ≤ t i := by
          intro i
          dsimp [t]
          exact_mod_cast (interpolationWeight_pos j i).le
        have hsum : ∑ i, t i ≤ T := by
          dsimp [t, T]
          exact_mod_cast interpolationWeight_sum_le j
        have hbox : ∀ P : Fin n → Body d,
            (∀ i, (P i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) →
            (weightedSum P t : Set (Space d)) ⊆
              Icc (fun _ => -((R : ℝ) * T)) (fun _ => (R : ℝ) * T) := by
          intro P hP x hx
          obtain ⟨hlo, hhi⟩ := weightedSum_subset_box P t ht hP hx
          have hbound := mul_le_mul_of_nonneg_left hsum hR'
          exact ⟨fun k => (neg_le_neg hbound).trans (hlo k),
            fun k => (hhi k).trans hbound⟩
        rw [hc _ ht, hc' _ ht]
        simpa only [volumeFunction, mul_assoc] using
          abs_bodyVolume_sub_le_of_dist_le (weightedSum K t) (weightedSum L t)
          (mul_nonneg hR' hT.le) (mul_nonneg hε hT.le) hsmall
          (hbox K hK) (hbox L hL)
          ((dist_weightedSum_le K L t ht hε hKL).trans
            (mul_le_mul_of_nonneg_left hsum hε))
    have h := abs_coefficient_sub_le_of_samples c c' hη hsamples α
    convert h using 1
    simp only [coefficientModulus, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_ofNat]
    dsimp [T]
    ring

end VolumePolynomials
