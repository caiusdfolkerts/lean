module

public import VolumePolynomials.SimplexCoordinates
public import VolumePolynomials.BodyContinuity
public import VolumePolynomials.RealizationCone
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Axis simplices and their literal coordinate sections

The defining body is a linear image of the coordinate simplex, hence the
convex hull of the origin and the listed axis vertices. Positive axis
lengths give an exact linear-inequality description, including a zero
dilation parameter. This is the geometric input to Appendix A.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

def diagonalMap {n : ℕ} (lam : Fin n → ℝ) : Space n →L[ℝ] Space n where
  toFun x i := lam i * x i
  map_add' x y := by ext i; simp only [Pi.add_apply, mul_add]
  map_smul' r x := by
    ext i
    change lam i * (r * x i) = r * (lam i * x i)
    ring
  cont := continuous_pi (fun i => continuous_const.mul (continuous_apply i))

@[simp] theorem diagonalMap_apply {n : ℕ} (lam : Fin n → ℝ) (x : Space n) (i : Fin n) :
    diagonalMap lam x i = lam i * x i := rfl

def axisBody {n : ℕ} (lam : Fin n → ℝ) : Body n :=
  mapBody (diagonalMap lam) (body n)

theorem zero_mem_axisBody {n : ℕ} (lam : Fin n → ℝ) :
    (0 : Space n) ∈ axisBody lam :=
  ⟨0, zero_mem_simplex n, map_zero _⟩

theorem axisBody_finiteHull {n : ℕ} (lam : Fin n → ℝ) :
    PolytopeGeometry.IsFiniteHull (axisBody lam : Set (Space n)) :=
  (simplex_finiteHull n).linear_image (diagonalMap lam).toLinearMap

theorem axisBody_one (n : ℕ) : axisBody (fun _ : Fin n => 1) = body n := by
  first
  | apply ConvexBody.ext
    change diagonalMap (fun _ : Fin n => (1 : ℝ)) '' simplex n = simplex n
    have heq : (diagonalMap (fun _ : Fin n => (1 : ℝ)) : Space n → Space n) = id := by
      first
      | funext x i
        simp [diagonalMap]
    rw [heq, Set.image_id]

theorem axisBody_scalar {n : ℕ} (lam : Fin n → ℝ) (r : ℝ) :
    axisBody (fun i => r * lam i) = r • axisBody lam := by
  first
  | apply ConvexBody.ext
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨diagonalMap lam y, ⟨y, hy, rfl⟩, ?_⟩
      ext i
      simp [diagonalMap, mul_assoc]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      ext i
      simp [diagonalMap, mul_assoc]

theorem mem_axisBody_iff {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) (x : Space n) :
    x ∈ axisBody lam ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i / lam i ≤ 1 := by
  first
  | constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun i => mul_nonneg (hlam i).le (hy.1 i), ?_⟩
      have heq (i : Fin n) : diagonalMap lam y i / lam i = y i := by
        first
        | dsimp only [diagonalMap]
          exact mul_div_cancel_left₀ _ (hlam i).ne'
      simpa only [heq] using hy.2
    · rintro ⟨hx, hs⟩
      refine ⟨fun i => x i / lam i,
        ⟨fun i => div_nonneg (hx i) (hlam i).le, hs⟩, ?_⟩
      ext i
      exact mul_div_cancel₀ _ (hlam i).ne'

theorem mem_smul_axisBody_iff {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) (x : Space n) :
    x ∈ t • axisBody lam ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i / lam i ≤ t := by
  first
  | constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' := (mem_axisBody_iff hlam y).mp hy
      refine ⟨fun i => mul_nonneg ht (hy'.1 i), ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, ← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left hy'.2 ht).trans_eq (mul_one t)
    · rintro ⟨hx, hs⟩
      by_cases ht0 : t = 0
      · have hx0 : x = 0 := by
          first
          | ext i
            change x i = 0
            have hsum : x i / lam i ≤ ∑ j, x j / lam j :=
              Finset.single_le_sum (fun j _ => div_nonneg (hx j) (hlam j).le)
                (Finset.mem_univ i)
            have hdiv : x i / lam i ≤ 0 := hsum.trans (ht0 ▸ hs)
            exact le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ (hlam i)).mp hdiv) (hx i)
        rw [ht0, hx0, body_zero_smul]
        rfl
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        refine ⟨t⁻¹ • x, (mem_axisBody_iff hlam _).mpr ⟨?_, ?_⟩, ?_⟩
        · intro i
          exact mul_nonneg (inv_nonneg.mpr ht) (hx i)
        · simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, ← Finset.mul_sum]
          rw [← div_eq_inv_mul]
          exact (div_le_one htpos).mpr hs
        · change t • (t⁻¹ • x) = x
          rw [smul_smul, mul_inv_cancel₀ ht0, one_smul]

theorem coordinate_nonnegative {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) {x : Space n}
    (hx : x ∈ t • axisBody lam) (i : Fin n) : 0 ≤ x i :=
  ((mem_smul_axisBody_iff hlam ht x).mp hx).1 i

theorem coordinate_upper_bound {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) {x : Space n}
    (hx : x ∈ t • axisBody lam) (i : Fin n) : x i ≤ t * lam i := by
  first
  | have hx' := (mem_smul_axisBody_iff hlam ht x).mp hx
    have h : x i / lam i ≤ t :=
      (Finset.single_le_sum (fun j _ => div_nonneg (hx'.1 j) (hlam j).le)
        (Finset.mem_univ i)).trans hx'.2
    exact (div_le_iff₀ (hlam i)).mp h

/-- A section at the first coordinate, before any Minkowski summation. -/
theorem section_smul_axisBody {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) {t z : ℝ} (ht : 0 ≤ t)
    (hz0 : 0 ≤ z) (hzt : z ≤ t * lam 0) :
    {x : Space n | Fin.cons z x ∈ t • axisBody lam} =
      (t - z / lam 0) • (axisBody (Fin.tail lam) : Set (Space n)) := by
  first
  | have hr : 0 ≤ t - z / lam 0 :=
      sub_nonneg.mpr ((div_le_iff₀ (hlam 0)).mpr hzt)
    ext x
    rw [Set.mem_setOf_eq, mem_smul_axisBody_iff hlam ht,
      show x ∈ (t - z / lam 0) • (axisBody (Fin.tail lam) : Set (Space n)) ↔
        x ∈ (t - z / lam 0) • axisBody (Fin.tail lam) from Iff.rfl,
      mem_smul_axisBody_iff (lam := Fin.tail lam) (fun i => hlam i.succ) hr x]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ,
      Fin.tail_def]
    constructor
    · rintro ⟨⟨_, hx⟩, hs⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hs⟩
      exact ⟨⟨hz0, hx⟩, by linarith⟩

theorem scaled_simplex_subset_axisBody {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {r : ℝ} (hr : 0 ≤ r) (hle : ∀ i, r ≤ lam i) :
    r • body n ≤ axisBody lam := by
  first
  | rintro _ ⟨x, hx, rfl⟩
    apply (mem_axisBody_iff hlam _).mpr
    refine ⟨fun i => mul_nonneg hr (hx.1 i), ?_⟩
    apply (Finset.sum_le_sum (fun i _ => ?_)).trans hx.2
    change r * x i / lam i ≤ x i
    apply (div_le_iff₀ (hlam i)).mpr
    nlinarith [mul_le_mul_of_nonneg_right (hle i) (hx.1 i)]

theorem diagonal_dist_le {n : ℕ} (lam mu : Fin n → ℝ)
    {x : Space n} (hx : x ∈ simplex n) :
    dist (diagonalMap lam x) (diagonalMap mu x) ≤ dist lam mu := by
  first
  | apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    have hxi := (simplex_subset_unit_box n hx).2 i
    have habs : |x i| ≤ 1 := by rwa [abs_of_nonneg (hx.1 i)]
    calc
      dist (diagonalMap lam x i) (diagonalMap mu x i) =
          |lam i - mu i| * |x i| := by
        first
        | rw [Real.dist_eq]
          change |lam i * x i - mu i * x i| = |lam i - mu i| * |x i|
          rw [← sub_mul, abs_mul]
      _ ≤ |lam i - mu i| := by
        first
        | simpa only [mul_one] using mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ ≤ dist lam mu := by simpa only [Real.dist_eq] using dist_le_pi_dist lam mu i

theorem axisBody_dist_le {n : ℕ} (lam mu : Fin n → ℝ) :
    dist (axisBody lam) (axisBody mu) ≤ dist lam mu := by
  first
  | rw [← ConvexBody.hausdorffDist_coe]
    apply Metric.hausdorffDist_le_of_mem_dist dist_nonneg
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨diagonalMap mu x, ⟨x, hx, rfl⟩, diagonal_dist_le lam mu hx⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨diagonalMap lam x, ⟨x, hx, rfl⟩, by
        simpa only [dist_comm mu lam] using diagonal_dist_le mu lam hx⟩

theorem continuous_axisBody (n : ℕ) : Continuous (axisBody (n := n)) := by
  first
  | have h : LipschitzWith 1 (axisBody (n := n)) :=
      LipschitzWith.of_dist_le_mul (fun lam mu => by
        simpa only [NNReal.coe_one, one_mul] using axisBody_dist_le lam mu)
    exact h.continuous

end VolumePolynomials.AxisSimplex
