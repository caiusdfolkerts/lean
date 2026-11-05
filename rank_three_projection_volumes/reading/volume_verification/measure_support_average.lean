module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped Topology

namespace VolumeVerification.MeasureSupportAverage

section CompactTarget
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A continuous nonnegative function whose integral is zero vanishes on the
actual topological support of the measure. -/
theorem zero_on_support_of_integral_zero (ν : Measure X) [IsFiniteMeasure ν]
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) (hzero : (∫ x, f x ∂ν) = 0) :
    ∀ x ∈ ν.support, f x = 0 := by
  have hae : (fun x => f x) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg hf
      ((BoundedContinuousFunction.mkOfCompact f).integrable ν)).mp hzero
  have hclosed : IsClosed {x : X | f x = 0} :=
    isClosed_eq f.continuous continuous_const
  exact Measure.support_subset_of_isClosed hclosed hae

/-- Continuous nonnegative test functions detect inclusion of actual measure
supports. This does not assume absolute continuity of the two measures. -/
theorem support_subset_of_nonnegative_integral_zero
    (ν η : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (hzero : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂η) = 0 → (∫ x, f x ∂ν) = 0) :
    ν.support ⊆ η.support := by
  intro x hx
  by_contra hη
  obtain ⟨U, hUnhds, hUzero⟩ := Measure.notMem_support_iff_exists.mp hη
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hUnhds
  have hballzero : η (ball x r) = 0 := measure_mono_null hball hUzero
  let f : C(X, ℝ) :=
    ⟨fun y => max 0 (r - dist y x),
      continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))⟩
  have hf : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hfae : (fun y => f y) =ᵐ[η] 0 := by
    filter_upwards [compl_mem_ae_iff.mpr hballzero] with y hy
    have hdist : r ≤ dist y x := by
      simpa only [mem_compl_iff, mem_ball, not_lt] using hy
    exact max_eq_left (sub_nonpos.mpr hdist)
  have hfη : (∫ y, f y ∂η) = 0 := by
    rw [integral_congr_ae hfae]
    exact integral_zero X ℝ
  have hfx := zero_on_support_of_integral_zero ν f hf (hzero f hf hfη) x hx
  have hpos : f x = r := by simp [f, max_eq_right hr.le]
  rw [hpos] at hfx
  exact hr.ne' hfx

/-- A dense vector lattice of continuous functions that contains the constants
contains exact nonnegative local tests. Uniform approximation is followed by a
lattice truncation, so the resulting function is exactly zero off the prescribed
neighborhood, rather than merely small there. -/
theorem exists_nonnegative_local_test
    (D : Submodule ℝ C(X, ℝ)) (hdense : Dense (D : Set C(X, ℝ)))
    (hone : (1 : C(X, ℝ)) ∈ D)
    (hsup : ∀ {f g : C(X, ℝ)}, f ∈ D → g ∈ D → f ⊔ g ∈ D)
    (x : X) (U : Set X) (hU : U ∈ 𝓝 x) :
    ∃ g : C(X, ℝ), g ∈ D ∧ (∀ y, 0 ≤ g y) ∧ 0 < g x ∧
      ∀ y, y ∉ U → g y = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let f : C(X, ℝ) :=
    ⟨fun y => max 0 (r - dist y x),
      continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))⟩
  obtain ⟨g, hgD, hfg⟩ := Metric.mem_closure_iff.mp (hdense f) (r / 4) (by linarith)
  have happ (y : X) : |f y - g y| < r / 4 := by
    exact (ContinuousMap.dist_apply_le_dist (f := f) (g := g) y).trans_lt hfg
  let q : C(X, ℝ) := (g - (r / 4) • 1) ⊔ 0
  have hqD : q ∈ D := hsup (D.sub_mem hgD (D.smul_mem _ hone)) D.zero_mem
  refine ⟨q, hqD, ?_, ?_, ?_⟩
  · intro y
    exact le_max_right _ _
  · have hx : f x = r := by simp [f, max_eq_right hr.le]
    have hgx : 0 < g x - r / 4 := by
      have h := (abs_lt.mp (happ x)).2
      rw [hx] at h
      linarith
    have hq : q x = max (g x - r / 4) 0 := by simp [q]
    rw [hq]
    exact hgx.trans_le (le_max_left _ _)
  · intro y hy
    have hdist : r ≤ dist y x := by
      by_contra hn
      exact hy (hball (by simpa only [mem_ball] using lt_of_not_ge hn))
    have hfy : f y = 0 := max_eq_left (sub_nonpos.mpr hdist)
    have hgy : g y ≤ r / 4 := by
      have h := (abs_lt.mp (happ y)).1
      rw [hfy] at h
      linarith
    simp [q, max_eq_right (sub_nonpos.mpr hgy)]

/-- For support inclusion it suffices to test a dense lattice such as the
differences of genuine support functions. -/
theorem support_subset_of_dense_lattice_integral_zero
    (D : Submodule ℝ C(X, ℝ)) (hdense : Dense (D : Set C(X, ℝ)))
    (hone : (1 : C(X, ℝ)) ∈ D)
    (hsup : ∀ {f g : C(X, ℝ)}, f ∈ D → g ∈ D → f ⊔ g ∈ D)
    (ν η : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (hzero : ∀ f : C(X, ℝ), f ∈ D → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂η) = 0 → (∫ x, f x ∂ν) = 0) :
    ν.support ⊆ η.support := by
  intro x hx
  by_contra hη
  obtain ⟨U, hU, hUzero⟩ := Measure.notMem_support_iff_exists.mp hη
  obtain ⟨g, hgD, hg, hgx, hgout⟩ :=
    exists_nonnegative_local_test D hdense hone hsup x U hU
  have hgae : (fun y => g y) =ᵐ[η] 0 := by
    filter_upwards [compl_mem_ae_iff.mpr hUzero] with y hy
    exact hgout y hy
  have hgη : (∫ y, g y ∂η) = 0 := by
    rw [integral_congr_ae hgae]
    exact integral_zero X ℝ
  have hgν : (∫ y, g y ∂ν) = 0 := hzero g hgD hg hgη
  have hxzero := zero_on_support_of_integral_zero ν g hg hgν x hx
  exact hgx.ne' hxzero

end CompactTarget

section Average
variable {T X : Type*} [TopologicalSpace T]
  [MeasurableSpace T] [BorelSpace T]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Every member of a weakly continuous family of finite positive measures is
supported on the support of its average, provided the parameter measure charges
every nonempty open set. The average is specified by its continuous integrals;
no unsupported pointwise domination of mixed area measures is used. -/
theorem support_family_subset_average_support
    (ρ : Measure T) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (ν : T → Measure X) [∀ t, IsFiniteMeasure (ν t)]
    (η : Measure X) [IsFiniteMeasure η]
    (hcontinuous : ∀ f : C(X, ℝ), Continuous (fun t => ∫ x, f x ∂ν t))
    (hintegrable : ∀ f : C(X, ℝ), Integrable (fun t => ∫ x, f x ∂ν t) ρ)
    (haverage : ∀ f : C(X, ℝ),
      (∫ t, (∫ x, f x ∂ν t) ∂ρ) = ∫ x, f x ∂η) :
    ∀ t, (ν t).support ⊆ η.support := by
  intro t
  apply support_subset_of_nonnegative_integral_zero
  intro f hf hfη
  let F : C(T, ℝ) := ⟨fun s => ∫ x, f x ∂ν s, hcontinuous f⟩
  have hF : ∀ s, 0 ≤ F s := fun s => integral_nonneg hf
  have hFzero : (∫ s, F s ∂ρ) = 0 := (haverage f).trans hfη
  have hae : (fun s => F s) =ᵐ[ρ] 0 :=
    (integral_eq_zero_iff_of_nonneg hF (hintegrable f)).mp hFzero
  have heq : (fun s => F s) = 0 :=
    Measure.eq_of_ae_eq (μ := ρ) hae F.continuous continuous_const
  exact congrFun heq t

/-- Support inclusion for an average need only be established on a dense
vector lattice of test functions. In the mixed-volume application these are
differences of support functions; their parameter integrals are continuous
directly by continuity of genuine mixed volumes. -/
theorem support_family_subset_of_dense_lattice_average
    (D : Submodule ℝ C(X, ℝ)) (hdense : Dense (D : Set C(X, ℝ)))
    (hone : (1 : C(X, ℝ)) ∈ D)
    (hsup : ∀ {f g : C(X, ℝ)}, f ∈ D → g ∈ D → f ⊔ g ∈ D)
    (ρ : Measure T) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (ν : T → Measure X) [∀ t, IsFiniteMeasure (ν t)]
    (η : Measure X) [IsFiniteMeasure η] (c : ℝ)
    (hcontinuous : ∀ f : C(X, ℝ), f ∈ D → Continuous (fun t => ∫ x, f x ∂ν t))
    (hintegrable : ∀ f : C(X, ℝ), f ∈ D → Integrable (fun t => ∫ x, f x ∂ν t) ρ)
    (haverage : ∀ f : C(X, ℝ), f ∈ D →
      (∫ t, (∫ x, f x ∂ν t) ∂ρ) = c * ∫ x, f x ∂η) :
    ∀ t, (ν t).support ⊆ η.support := by
  intro t
  apply support_subset_of_dense_lattice_integral_zero D hdense hone hsup
  intro f hfD hf hfη
  let F : C(T, ℝ) := ⟨fun s => ∫ x, f x ∂ν s, hcontinuous f hfD⟩
  have hF : ∀ s, 0 ≤ F s := fun s => integral_nonneg hf
  have hFzero : (∫ s, F s ∂ρ) = 0 := by
    change (∫ s, (∫ x, f x ∂ν s) ∂ρ) = 0
    rw [haverage f hfD, hfη, mul_zero]
  have hae : (fun s => F s) =ᵐ[ρ] 0 :=
    (integral_eq_zero_iff_of_nonneg hF (hintegrable f hfD)).mp hFzero
  have heq : (fun s => F s) = 0 :=
    Measure.eq_of_ae_eq (μ := ρ) hae F.continuous continuous_const
  exact congrFun heq t

end Average
end VolumeVerification.MeasureSupportAverage
