module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# The nearest-point step in the lattice-covering argument

This module proves the geometric part of Lemma 4.1. The existence of a
balancing inner product for every point of the matroid base polytope is a
separate analytic theorem, not an assumption silently discharged here.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators InnerProductSpace

/-- A centered zonotope with half-widths `c i / 2` in directions `v i`. -/
def CenteredZonotope {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E]
    (v : ι → E) (c : ι → ℝ) : Set E :=
  {y | ∃ t : ι → ℝ, (∀ i, |t i| ≤ c i / 2) ∧ ∑ i, t i • v i = y}

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every Euclidean nearest-point error satisfies all neighboring-point inequalities. -/
theorem nearest_error_inner_bound (Γ : AddSubgroup E) (x z : E)
    (hz : z ∈ Γ) (hnearest : ∀ y ∈ Γ, ‖x - z‖ ≤ ‖x - y‖)
    (v : E) (hv : v ∈ Γ) :
    |⟪v, x - z⟫_ℝ| ≤ ‖v‖ ^ 2 / 2 := by
  have hminus : ‖x - z‖ ≤ ‖(x - z) - v‖ := by
    have h := hnearest (z + v) (Γ.add_mem hz hv)
    convert h using 1 <;> congr 1 <;> abel
  have hplus : ‖x - z‖ ≤ ‖(x - z) + v‖ := by
    have h := hnearest (z - v) (Γ.sub_mem hz hv)
    convert h using 1 <;> congr 1 <;> abel
  have hminus2 : ‖x - z‖ ^ 2 ≤ ‖(x - z) - v‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hminus
  have hplus2 : ‖x - z‖ ^ 2 ≤ ‖(x - z) + v‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hplus
  rw [norm_sub_sq_real (x - z) v] at hminus2
  rw [norm_add_sq_real (x - z) v] at hplus2
  rw [real_inner_comm (x - z) v]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A weighted tight frame gives a covering zonotope for every closed additive
subgroup containing its vectors, in a proper real inner-product space.

Applied after the log-determinant balancing step, this is exactly the
nearest-lattice-point argument in Lemma 4.1. No lattice-covering conclusion
is included among the hypotheses.
-/
theorem balanced_frame_covering [ProperSpace E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (v : ι → E) (hv : ∀ i, v i ∈ Γ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hframe : ∀ y : E, ∑ i, (w i * ⟪v i, y⟫_ℝ) • v i = y)
    (x : E) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (fun i => w i * ‖v i‖ ^ 2) := by
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist ⟨0, Γ.zero_mem⟩ x
  have hnearest : ∀ y ∈ Γ, ‖x - z‖ ≤ ‖x - y‖ := by
    intro y hy
    rw [← dist_eq_norm, ← dist_eq_norm, ← hdist]
    exact Metric.infDist_le_dist_of_mem hy
  refine ⟨z, hz, fun i => w i * ⟪v i, x - z⟫_ℝ, ?_, hframe (x - z)⟩
  intro i
  have h := nearest_error_inner_bound Γ x z hz hnearest (v i) (hv i)
  rw [abs_mul, abs_of_nonneg (hw i)]
  have hmul := mul_le_mul_of_nonneg_left h (hw i)
  nlinarith

/-- The quadratic norm-square determined by a real continuous linear operator. -/
def quadraticValue (T : E →L[ℝ] E) (x : E) : ℝ := ⟪x, T x⟫_ℝ

lemma quadraticValue_continuous (T : E →L[ℝ] E) : Continuous (quadraticValue T) :=
  continuous_id.inner T.continuous

lemma quadraticValue_smul (T : E →L[ℝ] E) (x : E) (a : ℝ) :
    quadraticValue T (a • x) = a ^ 2 * quadraticValue T x := by
  simp only [quadraticValue, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Positive definite quadratic forms have a uniform norm-square lower bound. -/
theorem quadraticValue_lower_bound [FiniteDimensional ℝ E] [Nontrivial E]
    (T : E →L[ℝ] E) (hpos : ∀ x ≠ 0, 0 < quadraticValue T x) :
    ∃ ε > 0, ∀ x, ε * ‖x‖ ^ 2 ≤ quadraticValue T x := by
  have hsne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMinOn hsne
      (quadraticValue_continuous T).continuousOn
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hunorm
  refine ⟨quadraticValue T u, hpos u hu0, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, quadraticValue]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
  have h : quadraticValue T u ≤ quadraticValue T (‖x‖⁻¹ • x) := hmin hxunit
  rw [quadraticValue_smul] at h
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
  simpa [mul_assoc, mul_comm, mul_left_comm, ← mul_pow, hnorm.ne'] using hmul

/-- A positive definite quadratic distance attains its minimum on every closed
additive subgroup. Discreteness and full rank are not needed for this step. -/
theorem exists_quadratic_nearest [FiniteDimensional ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (T : E →L[ℝ] E) (hpos : ∀ x ≠ 0, 0 < quadraticValue T x) (x : E) :
    ∃ z ∈ Γ, ∀ y ∈ Γ, quadraticValue T (x - z) ≤ quadraticValue T (x - y) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    refine ⟨0, Γ.zero_mem, ?_⟩
    intro y _
    exact le_of_eq (congrArg (fun z => quadraticValue T (x - z)) (Subsingleton.elim 0 y))
  letI := hE
  obtain ⟨ε, hε, hbound⟩ := quadraticValue_lower_bound T hpos
  have hnorm : Filter.Tendsto (fun y : E => ‖x - y‖) (Filter.cocompact E)
      Filter.atTop := by
    simpa only [Function.comp_def, ← Metric.cobounded_eq_cocompact] using
      tendsto_norm_cobounded_atTop.comp (tendsto_const_sub_cobounded x)
  have hpow : Filter.Tendsto (fun y : E => ‖x - y‖ ^ 2) (Filter.cocompact E)
      Filter.atTop := (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnorm
  have hlim : Filter.Tendsto (fun y : E => quadraticValue T (x - y))
      (Filter.cocompact E) Filter.atTop :=
    Filter.tendsto_atTop_mono (fun y => hbound (x - y))
      (Filter.Tendsto.const_mul_atTop hε hpow)
  have hcont : Continuous (fun y : E => quadraticValue T (x - y)) :=
    (quadraticValue_continuous T).comp (continuous_const.sub continuous_id)
  have hev : ∀ᶠ y in Filter.cocompact E,
      quadraticValue T (x - 0) ≤ quadraticValue T (x - y) :=
    hlim.eventually (Filter.eventually_ge_atTop _)
  obtain ⟨z, hz, hmin⟩ := hcont.continuousOn.exists_isMinOn' hclosed Γ.zero_mem
    (hev.filter_mono inf_le_left)
  exact ⟨z, hz, fun y hy => hmin hy⟩

/-- Symmetric quadratic expansion. -/
lemma quadraticValue_add (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ) (a b : E) :
    quadraticValue T (a + b) =
      quadraticValue T a + 2 * ⟪b, T a⟫_ℝ + quadraticValue T b := by
  simp only [quadraticValue, map_add, inner_add_left, inner_add_right]
  rw [hsym a b]
  ring

lemma quadraticValue_sub (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ) (a b : E) :
    quadraticValue T (a - b) =
      quadraticValue T a - 2 * ⟪b, T a⟫_ℝ + quadraticValue T b := by
  simp only [quadraticValue, map_sub, inner_sub_left, inner_sub_right]
  rw [hsym a b]
  ring

/-- The full ellipsoidal nearest-point step used in Lemma 4.1. -/
theorem ellipsoidal_frame_covering [FiniteDimensional ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ)
    (hpos : ∀ x ≠ 0, 0 < quadraticValue T x)
    (v : ι → E) (hv : ∀ i, v i ∈ Γ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hframe : ∀ y : E, ∑ i, (w i * ⟪v i, T y⟫_ℝ) • v i = y)
    (x : E) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (fun i => w i * quadraticValue T (v i)) := by
  obtain ⟨z, hz, hnearest⟩ := exists_quadratic_nearest Γ hclosed T hpos x
  refine ⟨z, hz, fun i => w i * ⟪v i, T (x - z)⟫_ℝ, ?_, hframe (x - z)⟩
  intro i
  have hminus : quadraticValue T (x - z) ≤ quadraticValue T ((x - z) - v i) := by
    have h := hnearest (z + v i) (Γ.add_mem hz (hv i))
    convert h using 1 <;> congr 1 <;> abel
  have hplus : quadraticValue T (x - z) ≤ quadraticValue T ((x - z) + v i) := by
    have h := hnearest (z - v i) (Γ.sub_mem hz (hv i))
    convert h using 1 <;> congr 1 <;> abel
  rw [quadraticValue_sub T hsym (x - z) (v i)] at hminus
  rw [quadraticValue_add T hsym (x - z) (v i)] at hplus
  have habs : |⟪v i, T (x - z)⟫_ℝ| ≤ quadraticValue T (v i) / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg (hw i)]
  have hmul := mul_le_mul_of_nonneg_left habs (hw i)
  nlinarith

end PaperVerification.Toric
