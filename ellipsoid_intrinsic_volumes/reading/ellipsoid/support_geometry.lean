module

public import Ellipsoid.Semiaxes
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Pointwise InnerProductSpace RealInnerProductSpace

namespace EllipsoidVerification

def axisLinear {n : ℕ} (a : Fin n → ℝ) : Space n →ₗ[ℝ] Space n where
  toFun := axisMap a
  map_add' x y := by ext i; simp [axisMap]; ring
  map_smul' r x := by ext i; simp [axisMap]; ring

def axisCLM {n : ℕ} (a : Fin n → ℝ) : Space n →L[ℝ] Space n :=
  (axisLinear a).toContinuousLinearMap

@[simp] theorem axisCLM_apply {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    axisCLM a x = axisMap a x := rfl

@[simp] theorem axisMap_zero {n : ℕ} (a : Fin n → ℝ) : axisMap a 0 = 0 := by
  exact (axisLinear a).map_zero

@[simp] theorem axisMap_smul {n : ℕ} (a : Fin n → ℝ) (r : ℝ) (x : Space n) :
    axisMap a (r • x) = r • axisMap a x := (axisLinear a).map_smul r x

theorem axisMap_injective {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, a i ≠ 0) :
    Function.Injective (axisMap a) := by
  intro x y h
  ext i
  exact mul_left_cancel₀ (ha i) (congrArg (fun z : Space n => z i) h)

theorem axisMap_ne_zero {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, a i ≠ 0)
    {x : Space n} (hx : x ≠ 0) : axisMap a x ≠ 0 := by
  intro h
  apply hx
  apply axisMap_injective ha
  simpa using h

theorem axisMap_inner {n : ℕ} (a : Fin n → ℝ) (x y : Space n) :
    ⟪x, axisMap a y⟫_ℝ = ⟪axisMap a x, y⟫_ℝ := by
  simp only [PiLp.inner_apply, Real.inner_apply, axisMap, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def axisBody {n : ℕ} (a : Fin n → ℝ) : Set (Space n) :=
  axisMap a '' Metric.closedBall 0 1

def axisSupport {n : ℕ} (a : Fin n → ℝ) (x : Space n) : ℝ := ‖axisMap a x‖

def supportPoint {n : ℕ} (a : Fin n → ℝ) (x : Space n) : Space n :=
  axisMap a ((axisSupport a x)⁻¹ • axisMap a x)

theorem axisSupport_pos {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {x : Space n} (hx : x ≠ 0) : 0 < axisSupport a x :=
  norm_pos_iff.mpr (axisMap_ne_zero (fun i => (ha i).ne') hx)

@[simp] theorem axisSupport_zero {n : ℕ} (a : Fin n → ℝ) : axisSupport a 0 = 0 := by
  simp [axisSupport]

@[simp] theorem supportPoint_zero {n : ℕ} (a : Fin n → ℝ) : supportPoint a 0 = 0 := by
  simp [supportPoint]

@[fun_prop] theorem continuous_axisSupport {n : ℕ} (a : Fin n → ℝ) :
    Continuous (axisSupport a) := (continuous_axisMap a).norm

theorem axisSupport_smul {n : ℕ} (a : Fin n → ℝ) (r : ℝ) (x : Space n) :
    axisSupport a (r • x) = |r| * axisSupport a x := by
  simp [axisSupport, norm_smul, Real.norm_eq_abs]

theorem supportPoint_mem_axisBody {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    supportPoint a x ∈ axisBody a := by
  refine ⟨(axisSupport a x)⁻¹ • axisMap a x, ?_, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg (axisMap a x)), axisSupport]
  by_cases h : ‖axisMap a x‖ = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem inner_le_axisSupport {n : ℕ} (a : Fin n → ℝ) (x : Space n)
    {y : Space n} (hy : y ∈ axisBody a) : ⟪x, y⟫_ℝ ≤ axisSupport a x := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [axisMap_inner]
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  exact (real_inner_le_norm _ _).trans (by
    simpa [axisSupport] using mul_le_mul_of_nonneg_left hz' (norm_nonneg (axisMap a x)))

theorem inner_supportPoint {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    ⟪x, supportPoint a x⟫_ℝ = axisSupport a x := by
  rw [supportPoint, axisMap_inner, inner_smul_right, real_inner_self_eq_norm_sq]
  dsimp [axisSupport]
  by_cases h : ‖axisMap a x‖ = 0
  · simp [h]
  · field_simp

theorem convex_axisBody {n : ℕ} (a : Fin n → ℝ) : Convex ℝ (axisBody a) :=
  (convex_closedBall (0 : Space n) 1).linear_image (axisLinear a)

theorem zero_mem_axisBody {n : ℕ} (a : Fin n → ℝ) : (0 : Space n) ∈ axisBody a := by
  exact ⟨0, by simp, axisMap_zero a⟩

def normalOffset {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) : Space n :=
  ‖x‖ • supportPoint a x + t • x

@[simp] theorem normalOffset_zero {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    normalOffset a t 0 = 0 := by simp [normalOffset]

theorem inner_normalOffset_self {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    ⟪x, normalOffset a t x⟫_ℝ =
      ‖x‖ * (axisSupport a x + t * ‖x‖) := by
  rw [normalOffset, inner_add_right, inner_smul_right, inner_smul_right,
    inner_supportPoint, real_inner_self_eq_norm_sq]
  ring

theorem inner_normalOffset_le {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (x y : Space n) :
    ⟪x, normalOffset a t y⟫_ℝ ≤ ‖y‖ * (axisSupport a x + t * ‖x‖) := by
  have hsup := inner_le_axisSupport a x (supportPoint_mem_axisBody a y)
  have hinner := real_inner_le_norm x y
  rw [normalOffset, inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hsup (norm_nonneg y),
    mul_le_mul_of_nonneg_left hinner ht]

theorem normalOffset_ne_zero {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) {x : Space n} (hx : x ≠ 0) : normalOffset a t x ≠ 0 := by
  intro h
  have hp : 0 < ‖x‖ * (axisSupport a x + t * ‖x‖) :=
    mul_pos (norm_pos_iff.mpr hx)
      (add_pos_of_pos_of_nonneg (axisSupport_pos ha hx) (mul_nonneg ht (norm_nonneg x)))
  rw [← inner_normalOffset_self, h, inner_zero_right] at hp
  exact lt_irrefl _ hp

theorem normalOffset_norm_eq_of_eq {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) {x y : Space n}
    (h : normalOffset a t x = normalOffset a t y) : ‖x‖ = ‖y‖ := by
  suffices hle : ∀ x y : Space n, normalOffset a t x = normalOffset a t y → ‖x‖ ≤ ‖y‖ from
    le_antisymm (hle x y h) (hle y x h.symm)
  intro x y hxy
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : 0 < axisSupport a x + t * ‖x‖ :=
      add_pos_of_pos_of_nonneg (axisSupport_pos ha hx) (mul_nonneg ht (norm_nonneg x))
    have hh := inner_normalOffset_le a ht x y
    rw [← hxy, inner_normalOffset_self] at hh
    exact le_of_mul_le_mul_right hh hpos

theorem normalOffset_injective {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) : Function.Injective (normalOffset a t) := by
  intro x y h
  have hnorm := normalOffset_norm_eq_of_eq ha ht h
  by_cases hx : x = 0
  · rw [hx]
    symm
    apply norm_eq_zero.mp
    simpa [hx] using hnorm.symm
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : y ≠ 0 := by
    intro hy
    exact hr.ne' (by simpa [hy] using hnorm)
  have hxS := axisSupport_pos ha hx
  have hyS := axisSupport_pos ha hy
  have hsup := inner_le_axisSupport a x (supportPoint_mem_axisBody a y)
  have hxy := real_inner_le_norm x y
  rw [← hnorm] at hxy
  have heq := congrArg (fun z : Space n => ⟪x, z⟫_ℝ) h
  rw [inner_normalOffset_self, normalOffset, inner_add_right, inner_smul_right,
    inner_smul_right, ← hnorm] at heq
  have hs : ⟪x, supportPoint a y⟫_ℝ = axisSupport a x := by
    have hn := mul_nonneg ht (sub_nonneg.mpr hxy)
    nlinarith
  have hcs : ⟪axisMap a x, axisMap a y⟫_ℝ = axisSupport a x * axisSupport a y := by
    rw [supportPoint, axisMap_inner, inner_smul_right] at hs
    field_simp [hyS.ne'] at hs
    nlinarith
  have hcol := (inner_eq_norm_mul_iff_real).1 hcs
  have hcol' : axisSupport a y • x = axisSupport a x • y := by
    apply axisMap_injective (fun i => (ha i).ne')
    simpa only [axisMap_smul, axisSupport] using hcol
  have hnormcol := congrArg norm hcol'
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hyS.le,
    Real.norm_of_nonneg hxS.le, ← hnorm] at hnormcol
  have hS : axisSupport a y = axisSupport a x := mul_right_cancel₀ hr.ne' hnormcol
  rw [hS] at hcol'
  ext i
  exact mul_left_cancel₀ hxS.ne' (congrArg (fun z : Space n => z i) hcol')

theorem normalOffset_mem_parallelBody {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {x : Space n} (hx : x ∈ Metric.closedBall 0 1) :
    normalOffset a t x ∈ parallelBody (axisBody a) t := by
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  have hfirst : ‖x‖ • supportPoint a x ∈ axisBody a :=
    (convex_axisBody a).smul_mem_of_zero_mem (zero_mem_axisBody a)
      (supportPoint_mem_axisBody a x) ⟨norm_nonneg x, hx'⟩
  have hsecond : t • x ∈ Metric.closedBall (0 : Space n) t := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht]
    exact mul_le_of_le_one_right ht hx'
  exact ⟨_, hfirst, _, hsecond, rfl⟩

end EllipsoidVerification
