module

public import VolumePolynomials.Definitions
public import VolumePolynomials.FinitePolytope
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.FunProp

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Coordinate simplices and their affine height

The simplex is the actual subset of coordinate space with nonnegative
coordinates and coordinate sum at most one. Its description as a finite
convex hull is proved explicitly. The affine height is the missing
barycentric coordinate, so its positive superlevel sets are homothetic
copies of the simplex.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.SimplexCoordinates

def simplex (n : ℕ) : Set (Space n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def height {n : ℕ} (x : Space n) : ℝ := 1 - ∑ i, x i

theorem zero_mem_simplex (n : ℕ) : (0 : Space n) ∈ simplex n := by
  first
  | simp [simplex]

theorem coordinate_mem_simplex {n : ℕ} (i : Fin n) :
    (Pi.single i 1 : Space n) ∈ simplex n := by
  first
  | classical
    constructor
    · intro j
      by_cases hji : j = i <;> simp [Pi.single_apply, hji]
    · simp

theorem simplex_convex (n : ℕ) : Convex ℝ (simplex n) := by
  first
  | intro x hx y hy a b ha hb hab
    constructor
    · intro i
      exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      calc
        a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
            (mul_le_mul_of_nonneg_left hy.2 hb)
        _ = 1 := by simpa only [mul_one] using hab

theorem simplex_closed (n : ℕ) : IsClosed (simplex n) := by
  first
  | have heq : simplex n =
        (⋂ i, {x : Space n | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
      first
      | ext x
        simp [simplex]
    rw [heq]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

theorem simplex_subset_unit_box (n : ℕ) :
    simplex n ⊆ Icc (0 : Space n) (fun _ => 1) := by
  first
  | intro x hx
    exact ⟨hx.1, fun i => (Finset.single_le_sum (fun j _ => hx.1 j)
      (Finset.mem_univ i)).trans hx.2⟩

theorem simplex_compact (n : ℕ) : IsCompact (simplex n) :=
  isCompact_Icc.of_isClosed_subset (simplex_closed n) (simplex_subset_unit_box n)

def body (n : ℕ) : Body n :=
  ⟨simplex n, simplex_convex n, simplex_compact n, ⟨0, zero_mem_simplex n⟩⟩

theorem height_nonnegative {n : ℕ} {x : Space n} (hx : x ∈ simplex n) :
    0 ≤ height x := sub_nonneg.mpr hx.2

theorem height_le_one {n : ℕ} {x : Space n} (hx : x ∈ simplex n) :
    height x ≤ 1 := by
  first
  | unfold height
    exact sub_le_self _ (Finset.sum_nonneg (fun i _ => hx.1 i))

theorem continuous_height (n : ℕ) : Continuous (height : Space n → ℝ) := by
  first
  | unfold height
    fun_prop

def vertex (n : ℕ) : Fin (n + 1) → Space n :=
  Fin.cons 0 (fun i => Pi.single i 1)

theorem vertex_mem_simplex (n : ℕ) (i : Fin (n + 1)) : vertex n i ∈ simplex n := by
  first
  | cases i using Fin.cases with
    | zero => exact zero_mem_simplex n
    | succ i => exact coordinate_mem_simplex i

theorem simplex_eq_convexHull (n : ℕ) :
    simplex n = convexHull ℝ (Set.range (vertex n)) := by
  first
  | apply le_antisymm
    · intro x hx
      let w : Fin (n + 1) → ℝ := Fin.cons (height x) x
      apply mem_convexHull_of_exists_fintype w (vertex n)
      · intro i
        cases i using Fin.cases with
        | zero => exact height_nonnegative hx
        | succ i => exact hx.1 i
      · simp [w, Fin.sum_univ_succ, height]
      · intro i
        exact Set.mem_range_self i
      · ext j
        simp [w, vertex, Fin.sum_univ_succ, Finset.sum_apply, Pi.single_apply]
    · exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact vertex_mem_simplex n i)
        (simplex_convex n)

theorem simplex_finiteHull (n : ℕ) : PolytopeGeometry.IsFiniteHull (simplex n) :=
  ⟨range (vertex n), Set.finite_range _, simplex_eq_convexHull n⟩

/-- A fixed open box lies in the simplex; this proves positive ambient
volume without assuming a simplex-volume formula. -/
theorem simplex_volume_pos (n : ℕ) : 0 < volume.real (simplex n) := by
  first
  | let c : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
    have hc : 0 < c := by dsimp [c]; positivity
    have hsub : Icc (0 : Space n) (fun _ => c) ⊆ simplex n := by
      first
      | intro x hx
        refine ⟨hx.1, ?_⟩
        calc
          ∑ i, x i ≤ ∑ _ : Fin n, c := Finset.sum_le_sum (fun i _ => hx.2 i)
          _ = (n : ℝ) * c := by simp
          _ ≤ 1 := by
            dsimp [c]
            have hden : (0 : ℝ) < n + 1 := by positivity
            rw [Nat.cast_add, Nat.cast_one, ← div_eq_mul_inv]
            exact (div_le_one hden).mpr (by linarith)
    have hbox : 0 < volume.real (Icc (0 : Space n) (fun _ => c)) := by
      first
      | rw [measureReal_def, Real.volume_Icc_pi_toReal (a := (0 : Space n))
          (b := fun _ => c) (fun _ => hc.le)]
        simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        exact pow_pos hc _
    exact hbox.trans_le (measureReal_mono hsub (simplex_compact n).measure_ne_top)

theorem superlevel_eq_smul {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    {x : Space n | x ∈ simplex n ∧ t ≤ height x} = (1 - t) • simplex n := by
  first
  | have hr : 0 < 1 - t := sub_pos.mpr ht1
    ext x
    constructor
    · rintro ⟨hx, hxt⟩
      refine ⟨(1 - t)⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
      · intro i
        exact mul_nonneg (inv_nonneg.mpr hr.le) (hx.1 i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [← div_eq_inv_mul]
        apply (div_le_one hr).mpr
        dsimp only [height] at hxt
        linarith
      · change (1 - t) • ((1 - t)⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · rintro ⟨y, hy, rfl⟩
      have hsum : ∑ i, ((1 - t) • y) i = (1 - t) * ∑ i, y i := by
        first
        | simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      have hbound : (1 - t) * ∑ i, y i ≤ 1 - t := by
        first
        | simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 hr.le
      refine ⟨⟨fun i => mul_nonneg hr.le (hy.1 i), ?_⟩, ?_⟩
      · rw [hsum]
        linarith
      · unfold height
        rw [hsum]
        linarith

theorem superlevel_empty {n : ℕ} {t : ℝ} (ht : 1 < t) :
    {x : Space n | x ∈ simplex n ∧ t ≤ height x} = ∅ := by
  first
  | apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxt⟩
    exact (not_le_of_gt ht) (hxt.trans (height_le_one hx))

theorem superlevel_volume {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x} =
      (1 - t) ^ n * volume.real (simplex n) := by
  first
  | rw [superlevel_eq_smul ht0 ht1, measureReal_def,
      Measure.addHaar_smul_of_nonneg volume (sub_nonneg.mpr ht1.le),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr ht1.le) _)]
    simp only [Space, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, measureReal_def]

end VolumePolynomials.SimplexCoordinates
