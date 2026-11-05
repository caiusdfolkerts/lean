module
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Finite exponential balancing

An analytic ingredient of the determinant-minimization argument in the toric
lattice-covering lemma. A finite spanning configuration with a strictly positive
zero relation admits an exponential reweighting with zero barycenter.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators InnerProductSpace
open Filter Topology

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sum of positive parts of the configuration's directional inner products. -/
def positivePartSum (v : ι → E) (x : E) : ℝ := ∑ i, max ⟪v i, x⟫_ℝ 0

lemma positivePartSum_nonneg (v : ι → E) (x : E) : 0 ≤ positivePartSum v x :=
  Finset.sum_nonneg (fun i _ => le_max_right _ _)

lemma positivePartSum_continuous (v : ι → E) : Continuous (positivePartSum v) := by
  unfold positivePartSum
  exact continuous_finset_sum _ (fun i _ =>
    (continuous_const.inner continuous_id).max continuous_const)

lemma positivePartSum_smul (v : ι → E) (x : E) {a : ℝ} (ha : 0 ≤ a) :
    positivePartSum v (a • x) = a * positivePartSum v x := by
  simp only [positivePartSum, real_inner_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_zero] using (mul_max_of_nonneg ⟪v i, x⟫_ℝ 0 ha).symm

/-- A positive zero relation rules out a nonzero direction having all inner products nonpositive. -/
lemma positivePartSum_pos (v : ι → E)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    {x : E} (hx : x ≠ 0) : 0 < positivePartSum v x := by
  have hnonneg := positivePartSum_nonneg v x
  by_contra hnot
  have hsum : positivePartSum v x = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hmaxzero : (fun i => max ⟪v i, x⟫_ℝ 0) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg (fun i => le_max_right ⟪v i, x⟫_ℝ 0)).mp hsum
  have hmax : ∀ i, max ⟪v i, x⟫_ℝ 0 = 0 := fun i => congrFun hmaxzero i
  have hnonpos : ∀ i, ⟪v i, x⟫_ℝ ≤ 0 := fun i =>
    (le_max_left _ _).trans (hmax i).le
  have hweighted : ∑ i, p i * ⟪v i, x⟫_ℝ = 0 := by
    have h := congrArg (fun y : E => ⟪y, x⟫_ℝ) hzero
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h
  have htermzero : (fun i => p i * ⟪v i, x⟫_ℝ) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonpos
      (fun i => mul_nonpos_of_nonneg_of_nonpos (hp i).le (hnonpos i))).mp hweighted
  have hterm : ∀ i, p i * ⟪v i, x⟫_ℝ = 0 := fun i => congrFun htermzero i
  have hinner : ∀ i, ⟪v i, x⟫_ℝ = 0 := fun i =>
    (mul_eq_zero.mp (hterm i)).resolve_left (hp i).ne'
  have hspaninner : ∀ y ∈ Submodule.span ℝ (Set.range v), ⟪y, x⟫_ℝ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hinner i
    | zero => simp
    | add y z hy hz hy' hz' => simp [inner_add_left, hy', hz']
    | smul a y hy hy' => simp [real_inner_smul_left, hy']
  have hxspan : x ∈ Submodule.span ℝ (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  have hself := hspaninner x hxspan
  exact hx ((inner_self_eq_zero (𝕜 := ℝ)).mp hself)

/-- Uniform linear growth of the positive-part support function. -/
lemma positivePartSum_lower_bound [FiniteDimensional ℝ E] [Nontrivial E]
    (v : ι → E) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0) :
    ∃ ε > 0, ∀ x : E, ε * ‖x‖ ≤ positivePartSum v x := by
  have hsne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMinOn hsne
      (positivePartSum_continuous v).continuousOn
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hunorm
  refine ⟨positivePartSum v u, positivePartSum_pos v hspan p hp hzero hu0, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, positivePartSum]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
  have h : positivePartSum v u ≤ positivePartSum v (‖x‖⁻¹ • x) := hmin hxunit
  rw [positivePartSum_smul v x (inv_nonneg.mpr hnorm.le)] at h
  have hmul := mul_le_mul_of_nonneg_right h hnorm.le
  simpa [mul_assoc, mul_comm, mul_left_comm, hnorm.ne'] using hmul

/-- A finite positive exponential sum. -/
def exponentialSum (v : ι → E) (d : ι → ℝ) (x : E) : ℝ :=
  ∑ i, d i * Real.exp ⟪v i, x⟫_ℝ

lemma exponentialSum_continuous (v : ι → E) (d : ι → ℝ) :
    Continuous (exponentialSum v d) := by
  unfold exponentialSum
  exact continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_const.inner continuous_id).rexp)

/-- The balancing theorem for a configuration spanning its ambient real inner-product space. -/
theorem finite_exponential_balance [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    exact ⟨0, Subsingleton.elim _ _⟩
  letI := hE
  obtain ⟨ε, hε, hbound⟩ := positivePartSum_lower_bound v hspan p hp hzero
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min d
  have hcoeff : 0 < d i₀ * ε := mul_pos (hd i₀) hε
  have hlower : ∀ x, d i₀ * ε * ‖x‖ ≤ exponentialSum v d x := by
    intro x
    calc
      d i₀ * ε * ‖x‖ ≤ d i₀ * positivePartSum v x := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound x) (hd i₀).le
      _ = ∑ i, d i₀ * max ⟪v i, x⟫_ℝ 0 := by rw [positivePartSum, Finset.mul_sum]
      _ ≤ exponentialSum v d x := by
        apply Finset.sum_le_sum
        intro i _
        have he : max ⟪v i, x⟫_ℝ 0 ≤ Real.exp ⟪v i, x⟫_ℝ := by
          refine max_le ?_ (Real.exp_pos _).le
          linarith [Real.add_one_le_exp ⟪v i, x⟫_ℝ]
        exact mul_le_mul (hi₀ i) he (le_max_right _ _) (hd i).le
  have hlim : Tendsto (exponentialSum v d) (cocompact E) atTop :=
    tendsto_atTop_mono hlower
      (Tendsto.const_mul_atTop hcoeff tendsto_norm_cocompact_atTop)
  obtain ⟨x, hxmin⟩ := (exponentialSum_continuous v d).exists_forall_le hlim
  let g : E := ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i
  have hlocal : IsLocalMin (fun t : ℝ => exponentialSum v d (x + t • g)) 0 := by
    exact Filter.Eventually.of_forall (fun t => by simpa using hxmin (x + t • g))
  have hpath : HasDerivAt (fun t : ℝ => x + t • g) g 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add x
  have hderiv : HasDerivAt (fun t : ℝ => exponentialSum v d (x + t • g))
      ⟪g, g⟫_ℝ 0 := by
    have hi (i : ι) : HasDerivAt
        (fun t : ℝ => d i * Real.exp ⟪v i, x + t • g⟫_ℝ)
        ((d i * Real.exp ⟪v i, x⟫_ℝ) * ⟪v i, g⟫_ℝ) 0 := by
      have hi' : HasDerivAt (fun t : ℝ => ⟪v i, x + t • g⟫_ℝ) ⟪v i, g⟫_ℝ 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (v i)).inner ℝ hpath
      simpa [mul_assoc] using hi'.exp.const_mul (d i)
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    simpa only [exponentialSum, g, sum_inner, real_inner_smul_left] using hs
  refine ⟨x, ?_⟩
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hlocal.hasDerivAt_eq_zero hderiv)

/-- The same balancing theorem in the span of the configuration. This removes
any unnecessary full-dimensionality assumption on the ambient space. -/
theorem finite_exponential_balance_in_span [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i = 0 := by
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hv : ∀ i, v i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let vW : ι → W := fun i => ⟨v i, hv i⟩
  have hspan : Submodule.span ℝ (Set.range vW) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff W hv).mpr rfl
  have hzeroW : ∑ i, p i • vW i = 0 := by
    apply Subtype.ext
    simpa [vW] using hzero
  obtain ⟨x, hx⟩ := finite_exponential_balance vW hspan p hp hzeroW d hd
  refine ⟨x, ?_⟩
  have h := congrArg (fun z : W => (z : E)) hx
  simpa [vW] using h

/-- A strictly positive convex combination is the barycenter of a suitable
exponential reweighting with any prescribed positive base coefficients.

This is the finite-dimensional analytic step behind the log-determinant
argument: the points will be the incidence vectors of all vector-space bases. -/
theorem finite_exponential_barycenter [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E) (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) •
      (v i - ∑ j, p j • v j) = 0 := by
  let c : E := ∑ j, p j • v j
  have hzero : ∑ i, p i • (v i - c) = 0 := by
    simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hpsum, c]
  obtain ⟨x, hx⟩ := finite_exponential_balance_in_span
    (fun i => v i - c) p hp hzero d hd
  refine ⟨x, ?_⟩
  have h := congrArg (fun z : E => Real.exp ⟪c, x⟫_ℝ • z) hx
  rw [smul_zero, Finset.smul_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, inner_sub_left]
  congr 1
  calc
    d i * Real.exp ⟪v i, x⟫_ℝ =
        d i * (Real.exp ⟪c, x⟫_ℝ *
          Real.exp (⟪v i, x⟫_ℝ - ⟪c, x⟫_ℝ)) := by
            rw [← Real.exp_add]
            congr 2
            ring
    _ = _ := by ring

end PaperVerification.Toric
