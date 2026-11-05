module

public import development.analytic_rigidity
public import development.compactification
public import development.finite_obstruction
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

#assert_standard_axioms VolumeVerification.ProjectionMeasureReduction.impossible_measure_data

/- Source module: VolumeVerification.MeasureSupportAverage. SHA256: 87c09867d8ba256cb40b1cdb6b38fd3e6ce8d8f1cfd46644f8c6daee9ca3a91f -/
section DevelopmentSource0








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
end
end
end DevelopmentSource0

/- Source module: Projection.ConvexHullRigidity. SHA256: 6effd5f1f277e4657580e3fdef8129392bdea67d490b4a4fc38f74674c446226 -/
section DevelopmentSource1






@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- For actual support functions, equality of one reference pairing for the
convex hull propagates to every mixed-area support. This is an amplification
theorem: the reference pairing equality remains explicit and must be obtained
separately. Neither weak nor strong AF rigidity is assumed in its proof.

The proof uses the actual convex hull `D = conv(A ∪ B)`. Its quadratic
valuation identity and AF show that the nonnegative support difference
`h_D - h_A` has zero integral against every marked mixed area measure. -/
theorem support_equality_of_hull_reference_pairing {d : ℕ}
    (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A B H : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a)
    (hHH : 0 < mixedVolume μ (Fin.cons H (Fin.cons H K)))
    (hreference :
      mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons H K)) =
        mixedVolume μ (Fin.cons A (Fin.cons H K))) :
    ∀ T : ConvexBody E, ∀ u ∈ (mixedAreaMeasure μ (Fin.cons T K) hdim).support,
      supportContinuous A u = supportContinuous B u := by
  let D := joinBody A B
  let q : ConvexBody E → ConvexBody E → ℝ :=
    fun X Y => mixedVolume μ (Fin.cons X (Fin.cons Y K))
  have hsymm (X Y : ConvexBody E) : q X Y = q Y X :=
    PolyhedralSupport.mixedVolume_cons_cons_swap μ X Y K
  have hmono : a ≤ q D A := by
    rw [← hAA]
    exact mixedVolume_mono_first_all μ (Fin.cons A K) hdim A D
      (le_joinBody_left A B)
  have hDAall : ∀ T, q D T = q A T :=
    VolumeVerification.AFPairingEquality.hull_pairings_of_weak_equality
      q hsymm
      (fun X Y T => PolyhedralSupport.mixedVolume_cons_add μ X Y (Fin.cons T K))
      (fun r hr X T => PolyhedralSupport.mixedVolume_cons_smul μ X (Fin.cons T K) hr)
      (fun X Y => mixedVolume_alexandrovFenchel μ hdim K X Y)
      A B D H a ha hAA hAB hBB (mixedVolume_joinBody_identity μ K A B)
      hmono hHH hreference
  have hABall : ∀ T, q A T = q B T :=
    mixedVolume_equal_pairings_of_AF_equality μ hdim K A B a ha hAA hAB hBB
  have hDBall (T : ConvexBody E) : q D T = q B T := (hDAall T).trans (hABall T)
  have zero_on_marked_support (C T : ConvexBody E) (hC : C ≤ D)
      (hpair : q D T = q C T) :
      ∀ u ∈ (mixedAreaMeasure μ (Fin.cons T K) hdim).support,
        supportContinuous D u - supportContinuous C u = 0 := by
    apply VolumeVerification.MeasureSupportAverage.zero_on_support_of_integral_zero
      (mixedAreaMeasure μ (Fin.cons T K) hdim)
      (supportContinuous D - supportContinuous C)
      (fun u => sub_nonneg.mpr (supportContinuous_mono hC u))
    change (∫ u, supportContinuous D u - supportContinuous C u
      ∂mixedAreaMeasure μ (Fin.cons T K) hdim) = 0
    have hDint : Integrable (fun u => supportContinuous D u)
        (mixedAreaMeasure μ (Fin.cons T K) hdim) :=
      (BoundedContinuousFunction.mkOfCompact (supportContinuous D)).integrable _
    have hCint : Integrable (fun u => supportContinuous C u)
        (mixedAreaMeasure μ (Fin.cons T K) hdim) :=
      (BoundedContinuousFunction.mkOfCompact (supportContinuous C)).integrable _
    have hpair' : mixedVolume μ (Fin.cons D (Fin.cons T K)) =
        mixedVolume μ (Fin.cons C (Fin.cons T K)) := hpair
    rw [integral_sub hDint hCint,
      mixedAreaMeasure_integral, mixedAreaMeasure_integral, hpair', sub_self]
  intro T u hu
  have hA := zero_on_marked_support A T (le_joinBody_left A B) (hDAall T) u hu
  have hB := zero_on_marked_support B T (le_joinBody_right A B) (hDBall T) u hu
  linarith

/-- The usual weak-to-strong formulation is an immediate consequence of the
reference-pairing version. Weak equality is required only on the actual
area-measure support of one reference body with positive self-pairing. -/
theorem support_equality_of_weak_area_equality {d : ℕ}
    (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A B H : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a)
    (hHH : 0 < mixedVolume μ (Fin.cons H (Fin.cons H K)))
    (hweak : ∀ u ∈ (mixedAreaMeasure μ (Fin.cons H K) hdim).support,
      supportContinuous A u = supportContinuous B u) :
    ∀ T : ConvexBody E, ∀ u ∈ (mixedAreaMeasure μ (Fin.cons T K) hdim).support,
      supportContinuous A u = supportContinuous B u := by
  apply support_equality_of_hull_reference_pairing μ K hdim A B H a ha
    hAA hAB hBB hHH
  have hi : (∫ u, supportContinuous (joinBody A B) u
      ∂mixedAreaMeasure μ (Fin.cons H K) hdim) =
    ∫ u, supportContinuous A u ∂mixedAreaMeasure μ (Fin.cons H K) hdim := by
    apply integral_congr_ae
    filter_upwards [Measure.support_mem_ae
      (μ := mixedAreaMeasure μ (Fin.cons H K) hdim)] with u hu
    have h := hweak u hu
    rw [supportContinuous_join, ContinuousMap.sup_apply, ← h, max_self]
  rw [mixedAreaMeasure_integral, mixedAreaMeasure_integral] at hi
  exact mul_left_cancel₀ (ne_of_gt
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg (d + 1)) zero_lt_one)) hi

end RankThreeProjection
end
end
end DevelopmentSource1

/- Source module: Projection.SegmentSupport. SHA256: 270a1beac99ea14450dabca077b86832eee4499012710e8f1207a5efc4f0cafa -/
section DevelopmentSource2





@[expose] public section
set_option autoImplicit false
noncomputable section

namespace RankThreeProjection
open VolumePolynomials
open scoped BigOperators Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The support function of the actual centered segment, with the paper's
half-length normalization. -/
@[simp] theorem supportContinuous_centeredSegment (v : E) (u : NormalSphere E) :
    supportContinuous (centeredSegment v) u = |u.val v| / 2 := by
  exact OAI.Paper092.SupportGeometry.support_centered_segment v u.val

theorem supportContinuous_smul_real (A : ConvexBody E) {r : ℝ} (hr : 0 ≤ r)
    (u : NormalSphere E) :
    supportContinuous (r • A) u = r * supportContinuous A u :=
  Support.smul_body A u.val hr

theorem supportContinuous_sum {ι : Type*} (s : Finset ι) (A : ι → ConvexBody E)
    (u : NormalSphere E) :
    supportContinuous (∑ i ∈ s, A i) u = ∑ i ∈ s, supportContinuous (A i) u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, supportContinuous_zero, ContinuousMap.zero_apply]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, supportContinuous_add,
        ContinuousMap.add_apply, ih]

/-- The support function of a genuine Minkowski sum of marked segments. -/
theorem supportContinuous_weighted_segments {ι : Type*} [Fintype ι]
    (U : ι → E) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (u : NormalSphere E) :
    supportContinuous (∑ i, x i • centeredSegment (U i)) u =
      (1 / 2 : ℝ) * ∑ i, x i * |u.val (U i)| := by
  rw [supportContinuous_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [supportContinuous_smul_real _ (hx i), supportContinuous_centeredSegment]
  ring

end RankThreeProjection
end
end
end DevelopmentSource2

/- Source module: Projection.RepeatedSegment. SHA256: 2ff4a19cb3c004a556e0570a03833c73a5fd22897f9d75dd388eadc16503bcf6 -/
section DevelopmentSource3





@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem centeredSegment_zero : centeredSegment (0 : E) = 0 := by
  apply ConvexBody.ext
  change segment ℝ (-(1 / 2 : ℝ) • (0 : E)) ((1 / 2 : ℝ) • (0 : E)) = {0}
  simp

section Measure
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem mixedVolume_zero_first {d : ℕ} (K : Fin d → ConvexBody E) :
    mixedVolume volume (Fin.cons (0 : ConvexBody E) K) = 0 := by
  simpa only [Fin.update_cons_zero] using
    mixedVolume_zero_arg volume (Fin.cons (0 : ConvexBody E) K) 0

/-- A repeated segment contributes zero to actual mixed volume.  The proof
sends its direction to the first coordinate and uses interval-fiber extrusion;
it does not define the diagonal of a matrix to be zero. -/
theorem mixedVolume_repeated_segment_zero {d : ℕ}
    (K : Fin d → ConvexBody E) (v : E) :
    mixedVolume volume
      (Fin.cons (centeredSegment v) (Fin.cons (centeredSegment v) K)) = 0 := by
  by_cases hv : v = 0
  · subst v
    rw [centeredSegment_zero, mixedVolume_zero_first]
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  let l : E →L[ℝ] ℝ := f.toContinuousLinearMap
  have hl : l v = 1 := hf
  let F := LinearMap.ker l.toLinearMap
  letI : MeasureSpace F := ⟨Measure.addHaar⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure F) := by
    change Measure.IsAddHaarMeasure (Measure.addHaar : Measure F)
    infer_instance
  let T : E ≃L[ℝ] ℝ × F := LinearFrame.continuousEquiv l v hl
  have hTv : T v = (1, 0) := by
    apply Prod.ext
    · exact hl
    · apply Subtype.ext
      change v - l v • v = 0
      simp only [hl, one_smul, sub_self]
  let K' : Fin d → ConvexBody (ℝ × F) :=
    fun i => mapBody T.toContinuousLinearMap (K i)
  have hmap :
      (fun i => mapBody T.toContinuousLinearMap
        ((Fin.cons (centeredSegment v) (Fin.cons (centeredSegment v) K) :
          Fin (d + 2) → ConvexBody E) i)) =
      Fin.cons (centeredSegment (1, (0 : F)))
        (Fin.cons (centeredSegment (1, (0 : F))) K') := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, map_centeredSegment,
        ContinuousLinearEquiv.coe_coe, hTv]
    · refine Fin.cases ?_ (fun k => rfl) j
      simp only [Fin.cons_succ, Fin.cons_zero, map_centeredSegment,
        ContinuousLinearEquiv.coe_coe, hTv]
  have hz : mixedVolume volume
      (Fin.cons (centeredSegment (1, (0 : F)))
        (Fin.cons (centeredSegment (1, (0 : F))) K')) = 0 := by
    have he := mixedVolume_centered_axis
      (Fin.cons (centeredSegment (1, (0 : F))) K')
    have hp :
        (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ F)
          ((Fin.cons (centeredSegment (1, (0 : F))) K' :
            Fin (d + 1) → ConvexBody (ℝ × F)) i)) =
        Fin.cons (0 : ConvexBody F)
          (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ F) (K' i)) := by
      funext i
      refine Fin.cases ?_ (fun j => rfl) i
      simp only [Fin.cons_zero, map_centeredSegment]
      change centeredSegment (0 : F) = 0
      exact centeredSegment_zero
    rw [hp, mixedVolume_zero_first] at he
    exact (mul_eq_zero.mp he).resolve_left (by positivity)
  rw [mixedVolume_eq_frameFactor_mul volume volume T, hmap, hz, mul_zero]

end Measure
end RankThreeProjection
end
end
end DevelopmentSource3

/- Source module: Projection.HyperplaneObstruction. SHA256: 184550bb656d24f674923e3d20b52a8a5418a582f20a21d5690fbefad7e9b054 -/
section DevelopmentSource4






@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators Matrix

namespace RankThreeProjection
open VolumePolynomials

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Measure
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The actual complementary mixed-volume matrix, with the paper's factor
`dim(E) * (dim(E)-1)` when `dim(E)=d+2`. -/
def complementaryMixedMatrix {d : ℕ} (K : ConvexBody E) (U : ι → E) :
    Matrix ι ι ℝ := fun i j =>
  (d + 2 : ℝ) * (d + 1 : ℝ) * mixedVolume volume
    (Fin.cons (centeredSegment (U i))
      (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)))

@[simp] theorem complementaryMixedMatrix_diagonal {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (i : ι) :
    complementaryMixedMatrix (d := d) K U i i = 0 := by
  rw [complementaryMixedMatrix, mixedVolume_repeated_segment_zero, mul_zero]

theorem complementaryMixedMatrix_symmetric {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (i j : ι) :
    complementaryMixedMatrix (d := d) K U i j =
      complementaryMixedMatrix (d := d) K U j i := by
  unfold complementaryMixedMatrix
  congr 1
  have he := mixedVolume_reindex volume
    (Fin.cons (centeredSegment (U i))
      (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)))
    (Equiv.swap (0 : Fin (d + 2)) 1)
  change mixedVolume volume
    ((Matrix.vecCons (centeredSegment (U i))
      (Matrix.vecCons (centeredSegment (U j)) (fun _ : Fin d => K))) ∘
        Equiv.swap 0 1) = _ at he
  rw [Matrix.cons_cons_comp_swap_zero_one] at he
  exact he.symm

theorem complementaryMixedMatrix_translate {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (v : E) :
    complementaryMixedMatrix (d := d) (translateBody v K) U =
      complementaryMixedMatrix (d := d) K U := by
  funext i j
  unfold complementaryMixedMatrix
  congr 1
  have he := mixedVolume_translate volume
    (Fin.cons (centeredSegment (U i))
      (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)))
    (Fin.cons 0 (Fin.cons 0 (fun _ : Fin d => v)))
  convert he using 1
  congr 1
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp only [Fin.cons_zero, translateBody_zero]
  · refine Fin.cases ?_ (fun m => rfl) l
    simp only [Fin.cons_succ, Fin.cons_zero, translateBody_zero]

section Frame
variable [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)]

theorem complementaryMixedMatrix_frame {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (T : E ≃L[ℝ] F) (i j : ι) :
    complementaryMixedMatrix (d := d) K U i j =
      (mixedVolumeFrameFactor volume volume T : ℝ) *
        complementaryMixedMatrix (d := d) (mapBody T.toContinuousLinearMap K)
          (fun i => T (U i)) i j := by
  unfold complementaryMixedMatrix
  rw [mixedVolume_eq_frameFactor_mul volume volume T]
  have he :
      (fun k : Fin (d + 2) => mapBody T.toContinuousLinearMap
        ((Fin.cons (centeredSegment (U i))
          (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)) :
            Fin (d + 2) → ConvexBody E) k)) =
      (Fin.cons (centeredSegment (T (U i)))
        (Fin.cons (centeredSegment (T (U j)))
          (fun _ : Fin d => mapBody T.toContinuousLinearMap K)) :
            Fin (d + 2) → ConvexBody F) := by
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · exact map_centeredSegment _ _
    · refine Fin.cases ?_ (fun m => rfl) l
      exact map_centeredSegment _ _
  rw [he]
  ring

end Frame

/-- A body annihilated by a nonzero functional maps to its actual projection
in the kernel factor. This is set equality, including degenerate bodies. -/
theorem mapBody_frame_eq_embed (K : ConvexBody E)
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (hK : ∀ x ∈ (K : Set E), l x = 0) :
    mapBody (LinearFrame.continuousEquiv l v hv).toContinuousLinearMap K =
      embedHyperplane (mapBody
        ((ContinuousLinearMap.snd ℝ ℝ (LinearMap.ker l.toLinearMap)).comp
          (LinearFrame.continuousEquiv l v hv).toContinuousLinearMap) K) := by
  apply ConvexBody.ext
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(LinearFrame.continuousEquiv l v hv x).2, ⟨x, hx, rfl⟩, ?_⟩
    apply Prod.ext
    · exact (hK x hx).symm
    · rfl
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    apply Prod.ext
    · exact hK x hx
    · rfl

/-- Lemma 5.1's weighted inequalities in every actual hyperplane frame.
The frame's positive Haar factor is retained explicitly during the proof. -/
theorem complementaryMixedMatrix_hyperplane_weighted_triangles
    {d : ℕ} (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (U : ι → E) (l : E →L[ℝ] ℝ) (hl : l ≠ 0)
    (hK : ∀ x ∈ (K : Set E), l x = 0) (i j k : ι) :
    complementaryMixedMatrix (d := d) K U i j * |l (U k)| ≤
      complementaryMixedMatrix (d := d) K U i k * |l (U j)| +
        complementaryMixedMatrix (d := d) K U j k * |l (U i)| := by
  obtain ⟨v, hv⟩ := LinearFrame.exists_unit_value l hl
  let F := LinearMap.ker l.toLinearMap
  letI : MeasureSpace F := ⟨Measure.addHaar⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure F) := by
    change Measure.IsAddHaarMeasure (Measure.addHaar : Measure F)
    infer_instance
  have hF : finrank ℝ F = d + 1 := by
    change finrank ℝ (LinearMap.ker l.toLinearMap) = d + 1
    have he := LinearFrame.finrank_kernel_add_one l v hv
    rw [hdim] at he
    omega
  letI : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  let T : E ≃L[ℝ] ℝ × F := LinearFrame.continuousEquiv l v hv
  let L : ConvexBody F := mapBody
    ((ContinuousLinearMap.snd ℝ ℝ F).comp T.toContinuousLinearMap) K
  let N := segmentMixedVolumeSeminorm volume (fun _ : Fin d => L) hF
  let J : ℝ := mixedVolumeFrameFactor volume volume T
  have hJ : 0 ≤ J := NNReal.coe_nonneg _
  have he (a b : ι) : complementaryMixedMatrix (d := d) K U a b =
      J * N (l (U a) • (T (U b)).2 - l (U b) • (T (U a)).2) := by
    rw [complementaryMixedMatrix_frame K U T,
      mapBody_frame_eq_embed K l v hv hK]
    rw [complementaryMixedMatrix, ← hyperplanePair]
    change J * ((d + 2 : ℝ) * (d + 1 : ℝ) *
      hyperplanePair (d := d) L (T (U a)) (T (U b))) = _
    rw [hyperplanePair_eq_seminorm L hF]
    rfl
  simp_rw [he]
  have ht := seminorm_weighted_triangle N (fun a => l (U a))
    (fun a => (T (U a)).2) i j k
  nlinarith [mul_le_mul_of_nonneg_left ht hJ]

/-- If every mark is tangent to the containing hyperplane, every entry of
the actual complementary mixed-volume matrix vanishes. -/
theorem complementaryMixedMatrix_eq_zero_of_tangent
    {d : ℕ} (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (U : ι → E) (l : E →L[ℝ] ℝ) (hl : l ≠ 0)
    (hK : ∀ x ∈ (K : Set E), l x = 0) (hU : ∀ i, l (U i) = 0) :
    complementaryMixedMatrix (d := d) K U = 0 := by
  obtain ⟨v, hv⟩ := LinearFrame.exists_unit_value l hl
  let F := LinearMap.ker l.toLinearMap
  letI : MeasureSpace F := ⟨Measure.addHaar⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure F) := by
    change Measure.IsAddHaarMeasure (Measure.addHaar : Measure F)
    infer_instance
  let T : E ≃L[ℝ] ℝ × F := LinearFrame.continuousEquiv l v hv
  let L : ConvexBody F := mapBody
    ((ContinuousLinearMap.snd ℝ ℝ F).comp T.toContinuousLinearMap) K
  funext i j
  rw [complementaryMixedMatrix_frame K U T,
    mapBody_frame_eq_embed K l v hv hK]
  unfold complementaryMixedMatrix
  rw [← hyperplanePair]
  have hz : hyperplanePair (d := d) L (T (U i)) (T (U j)) = 0 := by
    have hframe (k : ι) : T (U k) = (l (U k), (T (U k)).2) :=
      Prod.ext (LinearFrame.continuousEquiv_fst l v hv (U k)) rfl
    rw [hframe i, hframe j, hU i, hU j]
    have hf := hyperplanePair_formula (d := d) L
      (l (U i)) (l (U j)) (T (U i)).2 (T (U j)).2
    rw [hU i, hU j, zero_smul, zero_smul, sub_self, centeredSegment_zero,
      mixedVolume_zero_first] at hf
    exact (mul_eq_zero.mp hf).resolve_left (by positivity)
  rw [hz]
  simp

/-- A rank-at-most-three positive hollow matrix on at least five marks cannot
be represented by an actual body in any linear hyperplane. -/
theorem hyperplane_representation_impossible {n d : ℕ} (hn : 5 ≤ n)
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2) (U : Fin n → E)
    (l : E →L[ℝ] ℝ) (hl : l ≠ 0) (hK : ∀ x ∈ (K : Set E), l x = 0)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank ≤ 3) : False := by
  let x : Fin n → ℝ := fun i => |l (U i)|
  have hx : ∀ i, 0 ≤ x i := fun i => abs_nonneg _
  have hne : x ≠ 0 := by
    intro hx0
    have hU : ∀ i, l (U i) = 0 := by
      intro i
      exact abs_eq_zero.mp (congrFun hx0 i)
    have hzero := complementaryMixedMatrix_eq_zero_of_tangent K hdim U l hl hK hU
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
    have hp := hpos i j hij
    rw [hzero] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  apply VolumePapers.RankThree.no_nonnegative_weighted_triangles hn
    (complementaryMixedMatrix (d := d) K U)
    (complementaryMixedMatrix_diagonal K U)
    (complementaryMixedMatrix_symmetric K U) hpos hrank x hx hne
  intro i j k _ _ _
  exact complementaryMixedMatrix_hyperplane_weighted_triangles K hdim U l hl hK i j k

/-- Every lower-dimensional body can be translated into the kernel of an
actual nonzero continuous functional. -/
theorem exists_translate_annihilator (K : ConvexBody E)
    (hdim : finrank ℝ (affineSpan ℝ (K : Set E)).direction < finrank ℝ E) :
    ∃ (p : E) (l : E →L[ℝ] ℝ), l ≠ 0 ∧
      ∀ x ∈ ((translateBody (-p) K : ConvexBody E) : Set E), l x = 0 := by
  let V := (affineSpan ℝ (K : Set E)).direction
  have hV : V < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hdim' : finrank ℝ V < finrank ℝ E := hdim
    rw [he, finrank_top] at hdim'
    exact (lt_irrefl _) hdim'
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hV inferInstance
  obtain ⟨p, hp⟩ := K.nonempty
  let l : E →L[ℝ] ℝ := f.toContinuousLinearMap
  refine ⟨p, l, ?_, ?_⟩
  · intro hl
    apply hf
    ext x
    exact congrArg (fun g : E →L[ℝ] ℝ => g x) hl
  · intro x hx
    change x ∈ (translateBody (-p) K : Set E) at hx
    rw [coe_translateBody] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hv : y - p ∈ V := by
      simpa only [vsub_eq_sub] using
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ (K : Set E) hy)
          (subset_affineSpan ℝ (K : Set E) hp)
    have hz : f (y - p) ∈ V.map f := ⟨y - p, hv, rfl⟩
    rw [hmap, Submodule.mem_bot] at hz
    simpa only [l, LinearMap.coe_toContinuousLinearMap', vadd_eq_add,
      neg_add_eq_sub] using hz

/-- The hyperplane obstruction applies to every non-full-dimensional body,
not just to a chosen coordinate hyperplane or to bodies of codimension one. -/
theorem nonfull_representation_impossible {n d : ℕ} (hn : 5 ≤ n)
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2) (U : Fin n → E)
    (hK : finrank ℝ (affineSpan ℝ (K : Set E)).direction < finrank ℝ E)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank ≤ 3) : False := by
  obtain ⟨p, l, hl, hzero⟩ := exists_translate_annihilator K hK
  apply hyperplane_representation_impossible hn (translateBody (-p) K) hdim U l hl hzero
  · simpa only [complementaryMixedMatrix_translate] using hpos
  · simpa only [complementaryMixedMatrix_translate] using hrank

end Measure
end RankThreeProjection
end
end
end DevelopmentSource4

/- Source module: Projection.FullDimensionalReduction. SHA256: 58c930d7651975151f8a8e83d1c80b178f7f047f5bf131f35f5c1bc067292cfb -/
section DevelopmentSource5







@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped BigOperators Pointwise Matrix

namespace RankThreeProjection
open VolumePolynomials

/-!
This file proves the finite-measure reduction underlying Proposition 4.2.
`SegmentAreaRigidity` is an explicit hypothesis of this intermediate reduction.
The source in `Rigidity.FullDimensional` supplies it for full-dimensional repeated
bodies, and `Main` uses that proof in the unconditional principal statements.
It is neither an axiom nor included in any definition of convex bodies, mixed
volume, or the realization locus. The project's build and endpoint audit
reports record the verification status.
-/

/-- The precise equality-rigidity consequence needed by the polygon argument.
All measures and support functions in this proposition are the actual ones
constructed from convex bodies. `Rigidity.FullDimensional` supplies this
proposition for full-dimensional `K`. See the project's build and endpoint
audit reports for the verification status of the complete development. -/
def SegmentAreaRigidity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {d : ℕ} (K : ConvexBody E) (hdim : finrank ℝ E = d + 2) : Prop :=
  ∀ (A C : ConvexBody E) (a : ℝ), 0 < a →
    mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a →
    mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a →
    mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a →
    ∃ t : E, ∀ v : E,
      ∀ᵐ u ∂mixedAreaMeasure volume
        (Fin.cons (centeredSegment v) (fun _ : Fin d => K)) hdim,
        supportContinuous A u - supportContinuous C u = u.val t

section Coordinates
variable {n : ℕ}

def normalCoordinates (u : NormalSphere (Space n)) : Space n :=
  fun i => u.val (Pi.single i 1)

theorem continuous_normalCoordinates : Continuous (normalCoordinates (n := n)) := by
  apply continuous_pi
  intro i
  change Continuous (fun u : NormalSphere (Space n) => u.val (Pi.single i 1))
  fun_prop

theorem normal_evaluation_coordinates (u : NormalSphere (Space n)) (v : Space n) :
    u.val v = ∑ i, v i * normalCoordinates u i := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Space n) := by
    ext j
    simp [Pi.single_apply]
  calc
    u.val v = ∑ i, u.val (v i • (Pi.single i 1 : Space n)) := by
      rw [← map_sum]
      exact congrArg u.val hv
    _ = ∑ i, v i * normalCoordinates u i := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [normalCoordinates, smul_eq_mul] using
        (map_smul u.val (v i) (Pi.single i 1 : Space n))

theorem mark_coordinate_identity (U : Fin n → Space n)
    (j : Fin n) (u : NormalSphere (Space n)) :
    VolumeVerification.EdgeMoments.coordinate U normalCoordinates j u = u.val (U j) := by
  exact (normal_evaluation_coordinates u (U j)).symm

end Coordinates

section Reduction
variable {n d : ℕ} [NeZero n]
  (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)

/-- The paper's actual normalized mixed area measures. -/
def markedAreaMeasure (v : Space n) : Measure (NormalSphere (Space n)) :=
  ENNReal.ofReal ((d + 1 : ℝ) / 2) •
    mixedAreaMeasure volume (Fin.cons (centeredSegment v) (fun _ : Fin d => K)) hdim

instance markedAreaMeasure_finite (v : Space n) : IsFiniteMeasure (markedAreaMeasure K hdim v) := by
  unfold markedAreaMeasure
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem markedAreaMeasure_pairing (u v : Space n) :
    (∫ x, |x.val v| ∂markedAreaMeasure K hdim u) =
      (d + 2 : ℝ) * (d + 1 : ℝ) * mixedVolume volume
        (Fin.cons (centeredSegment u)
          (Fin.cons (centeredSegment v) (fun _ : Fin d => K))) := by
  have he : (fun x : NormalSphere (Space n) => |x.val v|) =
      fun x => 2 * supportContinuous (centeredSegment v) x := by
    funext x
    rw [supportContinuous_centeredSegment]
    ring
  rw [he, markedAreaMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), integral_const_mul,
    mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap volume (centeredSegment v) (centeredSegment u)]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem markedAreaMeasure_centered (u v : Space n) :
    (∫ x, x.val v ∂markedAreaMeasure K hdim u) = 0 := by
  rw [markedAreaMeasure, integral_smul_measure, mixedAreaMeasure_centered, smul_zero]

theorem markedAreaMeasure_kernel_relation
    (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (w : Fin n → ℝ) (hw : complementaryMixedMatrix (d := d) K U *ᵥ w = 0)
    (s : Set (NormalSphere (Space n))) :
    ∑ i, w i * (markedAreaMeasure K hdim (U i)).real s = 0 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by
    have hn : n = d + 2 := by simpa only [Space,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
    omega)
  have he := mixedAreaMeasure_kernel_relation volume (fun _ : Fin d => K) hdim
    (fun i => centeredSegment (U i)) (complementaryMixedMatrix (d := d) K U)
    ((d + 2 : ℝ) * (d + 1 : ℝ)) (by positivity)
    (fun _ _ => rfl) (complementaryMixedMatrix_symmetric K U)
    (complementaryMixedMatrix_diagonal K U) hpos w hw s
  simp only [markedAreaMeasure, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (d + 1 : ℝ) / 2)]
  calc
    _ = ((d + 1 : ℝ) / 2) *
        ∑ i, w i * (mixedAreaMeasure volume
          (Fin.cons (centeredSegment (U i)) (fun _ : Fin d => K)) hdim).real s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [he, mul_zero]

theorem markedAreaMeasure_kernel_rigidity
    (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hR : SegmentAreaRigidity K hdim)
    (w : Fin n → ℝ) (hw : complementaryMixedMatrix (d := d) K U *ᵥ w = 0) :
    ∃ l : Fin n → ℝ, ∀ i,
      ∀ᵐ u ∂markedAreaMeasure K hdim (U i),
        (∑ j, w j * |u.val (U j)|) = ∑ j, l j * normalCoordinates u j := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by
    have hn : n = d + 2 := by simpa only [Space,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
    omega)
  by_cases hw0 : w = 0
  · subst w
    exact ⟨0, fun _ => Filter.Eventually.of_forall (fun _ => by simp)⟩
  let x := VolumeVerification.PositiveHollowKernel.positivePart w
  let y := VolumeVerification.PositiveHollowKernel.negativePart w
  have hx : ∀ i, 0 ≤ x i := fun i => le_max_right _ _
  have hy : ∀ i, 0 ≤ y i := fun i => le_max_right _ _
  obtain ⟨a, ha, hAA, hAC, hCC⟩ :=
    mixedVolume_kernel_zonotopes_equal_positive volume (fun _ : Fin d => K)
      (fun i => centeredSegment (U i)) (complementaryMixedMatrix (d := d) K U)
      ((d + 2 : ℝ) * (d + 1 : ℝ)) (by positivity) (fun _ _ => rfl)
      (complementaryMixedMatrix_symmetric K U) (complementaryMixedMatrix_diagonal K U)
      hpos w hw hw0
  obtain ⟨t, ht⟩ := hR
    (∑ i, x i • centeredSegment (U i)) (∑ i, y i • centeredSegment (U i))
    a ha hAA hAC hCC
  refine ⟨fun j => 2 * t j, ?_⟩
  intro i
  have hae := Measure.ae_smul_measure (ht (U i)) (ENNReal.ofReal ((d + 1 : ℝ) / 2))
  filter_upwards [hae] with u hu
  rw [supportContinuous_weighted_segments U x hx,
    supportContinuous_weighted_segments U y hy] at hu
  have hparts : ∀ j, w j = x j - y j := by
    intro j
    exact (congrFun
      (VolumeVerification.PositiveHollowKernel.positivePart_sub_negativePart w) j).symm
  have hs : (∑ j, w j * |u.val (U j)|) =
      (∑ j, x j * |u.val (U j)|) - ∑ j, y j * |u.val (U j)| := by
    simp_rw [hparts, sub_mul, Finset.sum_sub_distrib]
  rw [normal_evaluation_coordinates] at hu
  rw [hs]
  have he : (∑ j, 2 * t j * normalCoordinates u j) =
      2 * ∑ j, t j * normalCoordinates u j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

/-- All area-measure and polygonal steps of Proposition 4.2, with the sole
remaining geometric rigidity obligation visible in the theorem type. -/
theorem full_dimensional_obstruction_from_segment_rigidity
    (hn : 5 ≤ n) (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank = 3)
    (hR : SegmentAreaRigidity K hdim) : False := by
  apply VolumeVerification.ProjectionMeasureReduction.impossible_measure_data hn
    (complementaryMixedMatrix (d := d) K U) U
    (complementaryMixedMatrix_symmetric K U) (complementaryMixedMatrix_diagonal K U)
    hpos hrank (fun i => markedAreaMeasure K hdim (U i))
    normalCoordinates continuous_normalCoordinates
  · intro i j
    simp only [mark_coordinate_identity]
    exact (markedAreaMeasure_pairing K hdim (U i) (U j)).symm
  · intro i j
    exact markedAreaMeasure_centered K hdim (U i) (Pi.single j 1)
  · intro w hw s _hs
    exact markedAreaMeasure_kernel_relation K hdim U hpos w hw s
  · intro w hw
    simpa only [mark_coordinate_identity] using
      markedAreaMeasure_kernel_rigidity K hdim U hpos hR w hw

end Reduction
end RankThreeProjection
end
end
end DevelopmentSource5

/- Source module: Projection.Rigidity.WeakHullTransfer. SHA256: 9146c2fe039de34e9ea45b7e24e512283327a4d52ccdcb50330ecb7b439283b1 -/
section DevelopmentSource6






/-!
# Transporting the weak hull conclusion and recovering segment rigidity

The analytic work can be carried out in Euclidean coordinates. This file
transports its scalar mixed-volume conclusion through the actual positive
Haar conversion factor, then applies the convex-hull amplification in the
original normed space. No unit spheres or area measures in different norms
are identified.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection.Rigidity
open VolumePolynomials

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The precise weak conclusion needed from the analytic argument. It refers
only to actual convex hulls, translations, and actual mixed volumes. -/
def WeakHullReference {d : ℕ} (K : ConvexBody E) : Prop :=
  ∀ (A C : ConvexBody E) (a : ℝ), 0 < a →
    mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a →
    mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a →
    mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a →
    ∃ t : E,
      mixedVolume μ (Fin.cons (joinBody A (translateBody t C))
        (Fin.cons K (fun _ : Fin d => K))) =
      mixedVolume μ (Fin.cons A (Fin.cons K (fun _ : Fin d => K)))

theorem mixedVolume_pair_translate_background {d : ℕ}
    (K A C : ConvexBody E) (p : E) :
    mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => translateBody p K))) =
      mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) := by
  have h := mixedVolume_translate μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K)))
    (Fin.cons 0 (Fin.cons 0 (fun _ : Fin d => p)))
  convert h using 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => rfl) j) i <;>
    simp only [Fin.cons_zero, Fin.cons_succ, translateBody_zero]

theorem mixedVolume_translate_head {d : ℕ}
    (H : Fin d → ConvexBody E) (A : ConvexBody E) (p : E) :
    mixedVolume μ (Fin.cons (translateBody p A) H) =
      mixedVolume μ (Fin.cons A H) := by
  have h := mixedVolume_translate μ (Fin.cons A H) (Fin.cons p (fun _ => 0))
  convert h using 1
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => by simp only [Fin.cons_succ, translateBody_zero]) i

theorem mixedVolume_translate_second {d : ℕ}
    (H : Fin d → ConvexBody E) (A C : ConvexBody E) (p : E) :
    mixedVolume μ (Fin.cons A (Fin.cons (translateBody p C) H)) =
      mixedVolume μ (Fin.cons A (Fin.cons C H)) := by
  rw [PolyhedralSupport.mixedVolume_cons_cons_swap,
    mixedVolume_translate_head,
    PolyhedralSupport.mixedVolume_cons_cons_swap]

theorem supportContinuous_translate (p : E) (A : ConvexBody E)
    (u : NormalSphere E) :
    supportContinuous (translateBody p A) u = u.val p + supportContinuous A u := by
  rw [translateBody, supportContinuous_add, ContinuousMap.add_apply,
    supportContinuous_point]

theorem translateBody_join (p : E) (A C : ConvexBody E) :
    translateBody p (joinBody A C) = joinBody (translateBody p A) (translateBody p C) := by
  apply supportContinuous_injective
  ext u
  simp only [supportContinuous_translate, supportContinuous_join, ContinuousMap.sup_apply]
  exact add_max _ _ _

/-- It is enough for the analytic comparison to treat bodies containing the
origin. Arbitrary comparison bodies are translated, and the final translation
is adjusted exactly. -/
theorem weakHullReference_of_origin_comparisons {d : ℕ} (K : ConvexBody E)
    (h : ∀ (A C : ConvexBody E), (0 : E) ∈ A → (0 : E) ∈ C →
      ∀ (a : ℝ), 0 < a →
      mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a →
      mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a →
      mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a →
      ∃ t : E,
        mixedVolume μ (Fin.cons (joinBody A (translateBody t C))
          (Fin.cons K (fun _ : Fin d => K))) =
        mixedVolume μ (Fin.cons A (Fin.cons K (fun _ : Fin d => K)))) :
    WeakHullReference μ (d := d) K := by
  intro A C a ha hAA hAC hCC
  obtain ⟨p, hp⟩ := A.nonempty
  obtain ⟨q, hq⟩ := C.nonempty
  let A₀ := translateBody (-p) A
  let C₀ := translateBody (-q) C
  have hA₀ : (0 : E) ∈ A₀ := zero_mem_translateBody_neg hp
  have hC₀ : (0 : E) ∈ C₀ := zero_mem_translateBody_neg hq
  obtain ⟨v, hv⟩ := h A₀ C₀ hA₀ hC₀ a ha
    (by simpa only [A₀, mixedVolume_translate_head, mixedVolume_translate_second] using hAA)
    (by simpa only [A₀, C₀, mixedVolume_translate_head, mixedVolume_translate_second] using hAC)
    (by simpa only [C₀, mixedVolume_translate_head, mixedVolume_translate_second] using hCC)
  refine ⟨p + v - q, ?_⟩
  have he : translateBody p (joinBody A₀ (translateBody v C₀)) =
      joinBody A (translateBody (p + v - q) C) := by
    rw [translateBody_join]
    simp only [A₀, C₀, translateBody_translate, add_neg_cancel, translateBody_zero,
      sub_eq_add_neg, add_assoc]
  rw [← he, mixedVolume_translate_head, hv, mixedVolume_translate_head]

theorem zero_mem_interior_translateBody_neg (K : ConvexBody E) (p : E)
    (hp : p ∈ interior (K : Set E)) :
    (0 : E) ∈ interior ((translateBody (-p) K : ConvexBody E) : Set E) := by
  apply mem_interior_iff_mem_nhds.mpr
  rw [coe_translateBody]
  have hzero : (0 : E) ∈ (-p) +ᵥ interior (K : Set E) :=
    ⟨p, hp, by simp⟩
  apply Filter.mem_of_superset ((isOpen_interior.vadd (-p)).mem_nhds hzero)
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, interior_subset hy, rfl⟩

/-- Translating the repeated body changes none of the weak conclusion. -/
theorem weakHullReference_of_translate {d : ℕ} (K : ConvexBody E) (p : E)
    (h : WeakHullReference μ (d := d) (translateBody p K)) :
    WeakHullReference μ (d := d) K := by
  intro A C a ha hAA hAC hCC
  obtain ⟨t, ht⟩ := h A C a ha
    (by simpa only [mixedVolume_pair_translate_background] using hAA)
    (by simpa only [mixedVolume_pair_translate_background] using hAC)
    (by simpa only [mixedVolume_pair_translate_background] using hCC)
  refine ⟨t, ?_⟩
  rw [mixedVolume_translate_second, mixedVolume_translate_second,
    mixedVolume_pair_translate_background, mixedVolume_pair_translate_background] at ht
  exact ht

end Algebra

section Frame
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  (ν : Measure F) [Measure.IsAddHaarMeasure ν]

theorem mapBody_join (T : E →L[ℝ] F) (A C : ConvexBody E) :
    mapBody T (joinBody A C) = joinBody (mapBody T A) (mapBody T C) := by
  apply ConvexBody.ext
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, c, hc, r, s, hr, hs, hrs, rfl⟩ := mem_convexJoin.mp hx
    apply mem_convexJoin.mpr
    exact ⟨T a, ⟨a, ha, rfl⟩, T c, ⟨c, hc, rfl⟩, r, s,
      hr, hs, hrs, by simp only [map_add, map_smul]⟩
  · intro hy
    obtain ⟨a, ⟨x, hx, rfl⟩, c, ⟨z, hz, rfl⟩, r, s, hr, hs, hrs, rfl⟩ :=
      mem_convexJoin.mp hy
    refine ⟨r • x + s • z, ?_, by simp only [map_add, map_smul]⟩
    exact mem_convexJoin.mpr ⟨x, hx, z, hz, r, s, hr, hs, hrs, rfl⟩

theorem mixedVolume_pair_frame {d : ℕ} (T : E ≃L[ℝ] F) (K A C : ConvexBody E) :
    mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) =
      (mixedVolumeFrameFactor μ ν T : ℝ) *
        mixedVolume ν (Fin.cons (mapBody T.toContinuousLinearMap A)
          (Fin.cons (mapBody T.toContinuousLinearMap C)
            (fun _ : Fin d => mapBody T.toContinuousLinearMap K))) := by
  have h := mixedVolume_eq_frameFactor_mul μ ν T
    (Fin.cons A (Fin.cons C (fun _ : Fin d => K)))
  convert h using 1
  congr 2
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

/-- Norm-independent transfer of the actual weak pairing conclusion. -/
theorem weakHullReference_of_frame {d : ℕ}
    (T : E ≃L[ℝ] F) (K : ConvexBody E)
    (h : WeakHullReference ν (d := d) (mapBody T.toContinuousLinearMap K)) :
    WeakHullReference μ (d := d) K := by
  intro A C a ha hAA hAC hCC
  let factor : ℝ := mixedVolumeFrameFactor μ ν T
  have hf : 0 < factor := NNReal.coe_pos.mpr (mixedVolumeFrameFactor_pos μ ν T)
  have heq (X Y : ConvexBody E)
      (hXY : mixedVolume μ (Fin.cons X (Fin.cons Y (fun _ : Fin d => K))) = a) :
      mixedVolume ν (Fin.cons (mapBody T.toContinuousLinearMap X)
        (Fin.cons (mapBody T.toContinuousLinearMap Y)
          (fun _ : Fin d => mapBody T.toContinuousLinearMap K))) = a / factor := by
    apply (eq_div_iff hf.ne').mpr
    rw [mul_comm]
    exact (mixedVolume_pair_frame μ ν T K X Y).symm.trans hXY
  obtain ⟨v, hv⟩ := h (mapBody T.toContinuousLinearMap A)
    (mapBody T.toContinuousLinearMap C) (a / factor) (div_pos ha hf)
    (heq A A hAA) (heq A C hAC) (heq C C hCC)
  refine ⟨T.symm v, ?_⟩
  rw [mixedVolume_pair_frame μ ν T K,
    mixedVolume_pair_frame μ ν T K, mapBody_join, mapBody_translate]
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    using congrArg (fun x : ℝ => factor * x) hv

end Frame

section Strong
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The weak scalar pairing theorem suffices for exactly the strong segment
area statement used in Proposition 4.2. -/
theorem segmentAreaRigidity_of_weakHullReference {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : 0 < volume.real (K : Set E))
    (hweak : WeakHullReference volume (d := d) K) :
    SegmentAreaRigidity K hdim := by
  intro A C a ha hAA hAC hCC
  obtain ⟨t, ht⟩ := hweak A C a ha hAA hAC hCC
  have hAC' : mixedVolume volume
      (Fin.cons A (Fin.cons (translateBody t C) (fun _ : Fin d => K))) = a := by
    rw [mixedVolume_translate_second]
    exact hAC
  have hCC' : mixedVolume volume
      (Fin.cons (translateBody t C)
        (Fin.cons (translateBody t C) (fun _ : Fin d => K))) = a := by
    rw [mixedVolume_translate_head, mixedVolume_translate_second]
    exact hCC
  have hKK : 0 < mixedVolume volume
      (Fin.cons K (Fin.cons K (fun _ : Fin d => K))) := by
    simpa only [MultilinearDiagonal.cons_const, mixedVolume_diagonal volume hdim] using hK
  have hstrong := support_equality_of_hull_reference_pairing volume
    (fun _ : Fin d => K) hdim A (translateBody t C) K a ha hAA hAC' hCC' hKK ht
  refine ⟨t, ?_⟩
  intro v
  filter_upwards [Measure.support_mem_ae
    (μ := mixedAreaMeasure volume (Fin.cons (centeredSegment v) (fun _ : Fin d => K)) hdim)]
    with u hu
  have he := hstrong (centeredSegment v) u hu
  rw [translateBody, supportContinuous_add, ContinuousMap.add_apply,
    supportContinuous_point] at he
  linarith

/-- Interior supplies the required positive actual volume. -/
theorem segmentAreaRigidity_of_weakHullReference_of_interior {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : (interior (K : Set E)).Nonempty)
    (hweak : WeakHullReference volume (d := d) K) :
    SegmentAreaRigidity K hdim := by
  apply segmentAreaRigidity_of_weakHullReference K hdim _ hweak
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume hK).ne' K.isCompact.measure_lt_top.ne

end Strong
end RankThreeProjection.Rigidity

end
end
end DevelopmentSource6

/- Source module: Projection.ComplementaryCompactification. SHA256: 1d91f2fc6a3af528563caa2daeee2dba3f2dc6d7704c4540d0715f67041f86a7 -/
section DevelopmentSource7





@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators Topology

namespace RankThreeProjection
open VolumePolynomials

def firstDeleted {n : ℕ} (I : Deleted n 2) : Fin n :=
  I.val.orderEmbOfFin I.property 0

def secondDeleted {n : ℕ} (I : Deleted n 2) : Fin n :=
  I.val.orderEmbOfFin I.property 1

theorem firstDeleted_ne_secondDeleted {n : ℕ} (I : Deleted n 2) :
    firstDeleted I ≠ secondDeleted I := by
  intro h
  have he := (I.val.orderEmbOfFin I.property).injective h
  exact (by decide : (0 : Fin 2) ≠ 1) he

theorem deleted_pair {n : ℕ} (I : Deleted n 2) :
    I.val = {firstDeleted I, secondDeleted I} := by
  apply Finset.coe_injective
  rw [← I.val.range_orderEmbOfFin I.property]
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [firstDeleted, secondDeleted]
  · intro hi
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Extract the two-coordinate-deletion tuple from a symmetric hollow array. -/
def tupleOfArray {n : ℕ} (P : Array n) : Deleted n 2 → ℝ :=
  fun I => P (firstDeleted I) (secondDeleted I)

/-- Fill both symmetric entries from each two-element deletion set. -/
def arrayOfTuple {n : ℕ} (p : Deleted n 2 → ℝ) : Array n := fun i j =>
  if h : i = j then 0 else p ⟨{i, j}, by simp [h]⟩

theorem arrayOfTuple_tupleOfArray {n : ℕ} (P : Array n)
    (hdiag : ∀ i, P i i = 0) (hsym : ∀ i j, P i j = P j i) :
    arrayOfTuple (tupleOfArray P) = P := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [arrayOfTuple, hdiag]
  let I : Deleted n 2 := ⟨{i, j}, by simp [hij]⟩
  have ha : firstDeleted I = i ∨ firstDeleted I = j := by
    simpa only [firstDeleted, I, Finset.mem_insert, Finset.mem_singleton] using
      I.val.orderEmbOfFin_mem I.property (0 : Fin 2)
  have hb : secondDeleted I = i ∨ secondDeleted I = j := by
    simpa only [secondDeleted, I, Finset.mem_insert, Finset.mem_singleton] using
      I.val.orderEmbOfFin_mem I.property (1 : Fin 2)
  have hab := firstDeleted_ne_secondDeleted I
  change (if h : i = j then 0 else
    P (firstDeleted ⟨{i, j}, by simp [h]⟩)
      (secondDeleted ⟨{i, j}, by simp [h]⟩)) = P i j
  rw [dif_neg hij]
  change P (firstDeleted I) (secondDeleted I) = P i j
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · rw [ha, hb]
  · rw [ha, hb, hsym j i]
  · exact (hab (ha.trans hb.symm)).elim

theorem tupleOfArray_projectionArray {n : ℕ} (K : Body n) :
    tupleOfArray (projectionArray K) = allProjectionArray (k := 2) K := by
  funext I
  simp only [tupleOfArray, projectionArray,
    if_neg (firstDeleted_ne_secondDeleted I), allProjectionArray]
  rw [← deleted_pair I]

theorem arrayOfTuple_allProjectionArray {n : ℕ} (K : Body n) :
    arrayOfTuple (allProjectionArray (k := 2) K) = projectionArray K := by
  rw [← tupleOfArray_projectionArray]
  exact arrayOfTuple_tupleOfArray _ (projectionArray_diagonal K) (projectionArray_symmetric K)

theorem continuous_tupleOfArray {n : ℕ} : Continuous (tupleOfArray (n := n)) := by
  apply continuous_pi
  intro I
  exact (continuous_apply (secondDeleted I)).comp (continuous_apply (firstDeleted I))

theorem continuous_arrayOfTuple {n : ℕ} : Continuous (arrayOfTuple (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simpa only [arrayOfTuple, dif_pos hij] using
      (continuous_const : Continuous (fun _ : Deleted n 2 → ℝ => (0 : ℝ)))
  · simpa only [arrayOfTuple, dif_neg hij] using
      (continuous_apply (⟨{i, j}, by simp [hij]⟩ : Deleted n 2))

theorem factorial_ratio_two {n : ℕ} (hn : 2 ≤ n) :
    (n.factorial : ℝ) / ((n - 2).factorial : ℝ) =
      (n - 2 + 2 : ℕ) * (n - 2 + 1 : ℕ) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  field_simp
  ring

theorem markedTuple_pair_volume {n : ℕ} (K : Body n) (U : Fin n → Space n)
    (I : Deleted n 2) :
    mixedVolume volume (markedTuple K U I) =
      mixedVolume volume
        (Fin.cons (centeredSegment (U (firstDeleted I)))
          (Fin.cons (centeredSegment (U (secondDeleted I)))
            (fun _ : Fin (n - 2) => K))) := by
  let T : Fin (n - 2 + 2) → Body n :=
    Fin.cons (centeredSegment (U (firstDeleted I)))
      (Fin.cons (centeredSegment (U (secondDeleted I))) (fun _ : Fin (n - 2) => K))
  have he : (fun i => T (rotateMarkedIndices (n - 2) 2 i)) = markedTuple K U I := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [rotateMarkedIndices_body]
      have hj : tailIndex 2 j = j.succ.succ := by apply Fin.ext; simp
      simp only [hj, T, Fin.cons_succ, markedTuple, Fin.append_left]
    · intro j
      rw [rotateMarkedIndices_segment]
      fin_cases j
      · simp only [markedTuple, Fin.append_right]
        change T (headIndex (n - 2) (0 : Fin 2)) =
          centeredSegment (U (firstDeleted I))
        have hj : headIndex (n - 2) (0 : Fin 2) = 0 := by apply Fin.ext; rfl
        rw [hj]
        exact Fin.cons_zero _ _
      · simp only [markedTuple, Fin.append_right]
        change T (headIndex (n - 2) (1 : Fin 2)) =
          centeredSegment (U (secondDeleted I))
        have hj : headIndex (n - 2) (1 : Fin 2) = 1 := by apply Fin.ext; rfl
        rw [hj]
        simp only [T, Fin.cons_one, Fin.cons_zero]
  rw [← he]
  exact mixedVolume_reindex volume T (rotateMarkedIndices (n - 2) 2)

theorem tupleOfArray_complementaryMixedMatrix {n : ℕ} (hn : 2 ≤ n)
    (K : Body n) (U : Fin n → Space n) :
    tupleOfArray (complementaryMixedMatrix (d := n - 2) K U) =
      allMarkedArray (k := 2) K U := by
  funext I
  simp only [tupleOfArray, complementaryMixedMatrix, allMarkedArray,
    markedTuple_pair_volume, factorial_ratio_two hn, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one]

theorem arrayOfTuple_allMarkedArray {n : ℕ} (hn : 2 ≤ n)
    (K : Body n) (U : Fin n → Space n) :
    arrayOfTuple (allMarkedArray (k := 2) K U) =
      complementaryMixedMatrix (d := n - 2) K U := by
  rw [← tupleOfArray_complementaryMixedMatrix hn]
  exact arrayOfTuple_tupleOfArray _
    (complementaryMixedMatrix_diagonal K U) (complementaryMixedMatrix_symmetric K U)

theorem closedProjectionLocus_hollow_symmetric {n : ℕ} {P : Array n}
    (hP : P ∈ closedProjectionLocus n) :
    (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i) := by
  constructor
  · intro i
    have hclosed : IsClosed {Q : Array n | Q i i = 0} :=
      isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const
    apply (hclosed.closure_subset_iff (s := projectionLocus n)).mpr ?_ hP
    rintro Q ⟨K, rfl⟩
    exact projectionArray_diagonal K i
  · intro i j
    have hclosed : IsClosed {Q : Array n | Q i j = Q j i} :=
      isClosed_eq ((continuous_apply j).comp (continuous_apply i))
        ((continuous_apply i).comp (continuous_apply j))
    apply (hclosed.closure_subset_iff (s := projectionLocus n)).mpr ?_ hP
    rintro Q ⟨K, rfl⟩
    exact projectionArray_symmetric K i j

/-- The exact matrix form of Theorem 3.1 for complementary projections.
The matrix on the right is defined by actual mixed volumes even on its
diagonal; its hollowness was proved by repeated-segment extrusion. -/
theorem complementary_compactification {n : ℕ} (hn : 3 ≤ n) (P : Array n) :
    P ∈ closedProjectionLocus n ↔
      ∃ (K : Body n) (U : Fin n → Space n),
        n - 1 ≤ bodyDimension K ∧ complementaryMixedMatrix (d := n - 2) K U = P := by
  constructor
  · intro hP
    have ht : tupleOfArray P ∈ closure (allProjectionLocus n 2) := by
      have h := mem_closure_image continuous_tupleOfArray.continuousAt hP
      apply closure_mono (t := allProjectionLocus n 2) ?_ h
      rintro _ ⟨Q, ⟨K, rfl⟩, rfl⟩
      exact ⟨K, (tupleOfArray_projectionArray K).symm⟩
    obtain ⟨K, U, hdim, he⟩ :=
      (theorem31_with_dimension (by omega) (by omega) (tupleOfArray P)).mp ht
    obtain ⟨hdiag, hsym⟩ := closedProjectionLocus_hollow_symmetric hP
    refine ⟨K, U, ?_, ?_⟩
    · simpa only [show n - 2 + 1 = n - 1 by omega] using hdim
    · have hh := congrArg arrayOfTuple he
      rw [arrayOfTuple_allMarkedArray (by omega),
        arrayOfTuple_tupleOfArray P hdiag hsym] at hh
      exact hh
  · rintro ⟨K, U, _hdim, rfl⟩
    have ht : allMarkedArray (k := 2) K U ∈ closure (allProjectionLocus n 2) :=
      (theorem31 (by omega) (by omega) _).mpr ⟨K, U, rfl⟩
    have h := mem_closure_image continuous_arrayOfTuple.continuousAt ht
    rw [arrayOfTuple_allMarkedArray (by omega)] at h
    apply closure_mono (t := projectionLocus n) ?_ h
    rintro _ ⟨p, ⟨L, rfl⟩, rfl⟩
    exact ⟨L, (arrayOfTuple_allProjectionArray L).symm⟩

end RankThreeProjection
end
end
end DevelopmentSource7

/- Source module: Projection.BodyDimension. SHA256: c339981f9984d739773014c458ade99306a3a0554a9553df1269dc9b2dd41729 -/
section DevelopmentSource8






/-!
# Actual affine dimension and ambient interior

These statements connect the affine-span definition used in the
compactification theorem to the nonempty-interior hypothesis required by the
full-dimensional obstruction. Nonemptiness comes from the actual convex body;
no additional dimension or interior predicate is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Module

namespace RankThreeProjection

/-- For an actual nonempty compact convex body, full affine dimension is
equivalent to nonempty ambient interior. -/
theorem affineSpan_direction_finrank_eq_iff_interior_nonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : ConvexBody E) :
    finrank ℝ (affineSpan ℝ (K : Set E)).direction = finrank ℝ E ↔
      (interior (K : Set E)).Nonempty := by
  have hspan : ((affineSpan ℝ (K : Set E)) : Set E).Nonempty :=
    K.nonempty.mono (subset_affineSpan ℝ (K : Set E))
  calc
    finrank ℝ (affineSpan ℝ (K : Set E)).direction = finrank ℝ E ↔
        (affineSpan ℝ (K : Set E)).direction = ⊤ :=
      Submodule.eq_top_iff_finrank_eq.symm
    _ ↔ affineSpan ℝ (K : Set E) = ⊤ :=
      AffineSubspace.direction_eq_top_iff_of_nonempty hspan
    _ ↔ (interior (K : Set E)).Nonempty :=
      K.convex.interior_nonempty_iff_affineSpan_eq_top.symm

/-- The affine dimension cannot exceed the actual coordinate-space dimension. -/
theorem bodyDimension_le {n : ℕ} (K : Body n) : bodyDimension K ≤ n := by
  have h := Submodule.finrank_le (affineSpan ℝ (K : Set (Space n))).direction
  simpa only [bodyDimension, Space, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using h

/-- The exact bridge from the compactification's dimension to the interior
hypothesis of the full-dimensional branch. -/
theorem bodyDimension_eq_iff_interior_nonempty {n : ℕ} (K : Body n) :
    bodyDimension K = n ↔ (interior (K : Set (Space n))).Nonempty := by
  simpa only [bodyDimension, Space, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using
      affineSpan_direction_finrank_eq_iff_interior_nonempty K

/-- Its complementary form supplies precisely the dimension deficit used to
translate a body into the kernel of a nonzero continuous linear functional. -/
theorem bodyDimension_lt_iff_interior_empty {n : ℕ} (K : Body n) :
    bodyDimension K < n ↔ interior (K : Set (Space n)) = ∅ := by
  constructor
  · intro hdim
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hfull
    exact (ne_of_lt hdim) ((bodyDimension_eq_iff_interior_nonempty K).mpr hfull)
  · intro hempty
    apply lt_of_le_of_ne (bodyDimension_le K)
    intro hdim
    have hfull := (bodyDimension_eq_iff_interior_nonempty K).mp hdim
    rw [hempty] at hfull
    exact Set.not_nonempty_empty hfull

end RankThreeProjection
end
end
end DevelopmentSource8

/- Source module: VolumeVerification.RankThreeExamples. SHA256: cae512bbf5620b3b2c9ff12bc60e56d03b922e28ab394f7710f5ba5d59209433 -/
section DevelopmentSource9


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace VolumeVerification.RankThreeExamples

/-- Squared distances between distinct points on a line give positive hollow
rank-three matrices in every size at least three. Circle factorization then
provides the equivalent weighted circle representation used in the paper. -/
def squaredIndexMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((i.val : ℝ) - (j.val : ℝ)) ^ 2

theorem squaredIndexMatrix_diagonal (n : ℕ) (i : Fin n) :
    squaredIndexMatrix n i i = 0 := by simp [squaredIndexMatrix]

theorem squaredIndexMatrix_symmetric (n : ℕ) (i j : Fin n) :
    squaredIndexMatrix n i j = squaredIndexMatrix n j i := by
  unfold squaredIndexMatrix
  ring

theorem squaredIndexMatrix_positive (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    0 < squaredIndexMatrix n i j := by
  apply sq_pos_of_ne_zero
  intro hz
  apply hij
  apply Fin.ext
  exact_mod_cast sub_eq_zero.mp hz

theorem squaredIndexMatrix_rank_le (n : ℕ) : (squaredIndexMatrix n).rank ≤ 3 := by
  let L : Matrix (Fin n) (Fin 3) ℝ :=
    fun i => ![1, (i.val : ℝ), (i.val : ℝ)^2]
  let R : Matrix (Fin 3) (Fin n) ℝ :=
    fun k j => ![(j.val : ℝ)^2, -2 * (j.val : ℝ), 1] k
  have he : squaredIndexMatrix n = L * R := by
    ext i j
    change ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = ∑ k : Fin 3, L i k * R k j
    simp [Fin.sum_univ_succ, L, R]
    ring
  rw [he]
  exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_width L)

theorem squaredIndexMatrix_rank (n : ℕ) (hn : 3 ≤ n) :
    (squaredIndexMatrix n).rank = 3 := by
  let f : Fin 3 → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  have hm : (squaredIndexMatrix n).submatrix f f =
      (!![0,1,4; 1,0,1; 4,1,0] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.submatrix, squaredIndexMatrix, f]
  have hd : ((squaredIndexMatrix n).submatrix f f).det ≠ 0 := by
    rw [hm]
    norm_num [Matrix.det_fin_three]
  have hr := Matrix.rank_of_det_ne_zero hd
  have hle := Matrix.rank_submatrix_le (squaredIndexMatrix n) f f
  have hup := squaredIndexMatrix_rank_le n
  norm_num only [Fintype.card_fin] at hr
  omega

/-- The exact five-by-five example printed after Theorem 1.1. -/
def hexagonFive : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,3,4,3;
     1,0,1,3,4;
     3,1,0,1,3;
     4,3,1,0,1;
     3,4,3,1,0]

def hexagonB : Fin 5 → ℝ := ![2,1,-1,-2,-1]
def hexagonC : Fin 5 → ℝ := ![0,1,1,0,-1]

theorem hexagonFive_factorization (i j : Fin 5) :
    hexagonFive i j =
      2 - hexagonB i * hexagonB j / 2 - 3 * hexagonC i * hexagonC j / 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [hexagonFive, hexagonB, hexagonC]

theorem hexagonFive_diagonal (i : Fin 5) : hexagonFive i i = 0 := by
  fin_cases i <;> norm_num [hexagonFive]

theorem hexagonFive_symmetric (i j : Fin 5) : hexagonFive i j = hexagonFive j i := by
  fin_cases i <;> fin_cases j <;> norm_num [hexagonFive]

theorem hexagonFive_positive (i j : Fin 5) (hij : i ≠ j) : 0 < hexagonFive i j := by
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | norm_num [hexagonFive]

theorem hexagonFive_rank : hexagonFive.rank = 3 := by
  let L : Matrix (Fin 5) (Fin 3) ℝ := fun i => ![1, hexagonB i, hexagonC i]
  let R : Matrix (Fin 3) (Fin 5) ℝ :=
    fun k j => ![2, -hexagonB j / 2, -3 * hexagonC j / 2] k
  have he : hexagonFive = L * R := by
    ext i j
    rw [hexagonFive_factorization]
    change 2 - hexagonB i * hexagonB j / 2 - 3 * hexagonC i * hexagonC j / 2 =
      ∑ k : Fin 3, L i k * R k j
    simp [Fin.sum_univ_succ, L, R]
    ring
  have hup : hexagonFive.rank ≤ 3 := by
    rw [he]
    exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_width L)
  let f : Fin 3 → Fin 5 := fun i => ⟨i.val, by omega⟩
  have hm : hexagonFive.submatrix f f =
      (!![0,1,3; 1,0,1; 3,1,0] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.submatrix, hexagonFive, f]
  have hd : (hexagonFive.submatrix f f).det ≠ 0 := by
    rw [hm]
    norm_num [Matrix.det_fin_three]
  have hr := Matrix.rank_of_det_ne_zero hd
  have hle := Matrix.rank_submatrix_le hexagonFive f f
  norm_num only [Fintype.card_fin] at hr
  omega

theorem hexagonFive_signature :
    _root_.sigPos hexagonFive.toQuadraticForm' = 1 ∧
      _root_.sigNeg hexagonFive.toQuadraticForm' = 2 ∧
      Module.finrank ℝ hexagonFive.toQuadraticForm'.radical = 2 := by
  simpa using MatrixInertia.positive_hollow_rank_three_signature hexagonFive
    hexagonFive_symmetric hexagonFive_diagonal hexagonFive_positive hexagonFive_rank
    (0 : Fin 5) 1 2 (by decide) (by decide) (by decide)

end VolumeVerification.RankThreeExamples

end
end
end DevelopmentSource9

/- Source module: Projection.ClosureObstruction. SHA256: 67afb72333559ea27f9b4f46726eea079d23e339d3ef2061e625e4950a747804 -/
section DevelopmentSource10








/-!
# Conditional assembly with the rigidity obligation displayed

This file assembles the geometric branches under an explicit rigidity
interface. `Rigidity.FullDimensional` supplies that interface, and `Main`
states the unconditional Theorem 1.1. This intermediate file alone does not
establish the principal theorem. Verification of the complete chain is recorded
in the project's build and endpoint-audit reports.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Module Filter
open scoped Matrix Topology

namespace RankThreeProjection
open VolumeVerification.MatrixInertia

section
variable {n : ℕ} [NeZero n]

/-- The repeated-body equality theorem, restricted to precisely the actual
coordinate-space bodies needed in the final argument. Its proof is supplied by
`Rigidity.FullDimensional`, and `Main` discharges it in the principal statements. -/
def FullDimensionalRigidity : Prop :=
  ∀ (K : Body n) (d : ℕ) (hdim : finrank ℝ (Space n) = d + 2),
    (interior (K : Set (Space n))).Nonempty → SegmentAreaRigidity K hdim

/-- The two dimension branches and the exact compactification imply closure
exclusion once the remaining geometric rigidity theorem has been supplied. -/
theorem rank_three_exclusion_of_rigidity (hn : 5 ≤ n)
    (hR : FullDimensionalRigidity (n := n))
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ closedProjectionLocus n := by
  intro hclosure
  obtain ⟨K,U,_hdimension,hrep⟩ :=
    (complementary_compactification (by omega) P).mp hclosure
  have hdim : finrank ℝ (Space n) = (n - 2) + 2 := by
    simp only [Space, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hpositive : ∀ i j, i ≠ j →
      0 < complementaryMixedMatrix (d := n - 2) K U i j := by
    simpa only [hrep] using hP.2.2
  have hrank' : (complementaryMixedMatrix (d := n - 2) K U).rank = 3 := by
    simpa only [hrep] using hrank
  by_cases hfull : (interior (K : Set (Space n))).Nonempty
  · exact full_dimensional_obstruction_from_segment_rigidity K hdim hn U
      hpositive hrank' (hR K (n - 2) hdim hfull)
  · apply nonfull_representation_impossible hn K hdim U ?_ hpositive hrank'.le
    have hbody : bodyDimension K < n :=
      (bodyDimension_lt_iff_interior_empty K).mpr
        (Set.not_nonempty_iff_eq_empty.mp hfull)
    simpa only [bodyDimension, Space, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using hbody

/-- The inertia assertion itself uses no geometric rigidity hypothesis. -/
theorem rank_three_signature (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    sigPos P.toQuadraticForm' = 1 ∧
      sigNeg P.toQuadraticForm' = 2 ∧
      finrank ℝ P.toQuadraticForm'.radical = n - 3 := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; simp [i₀, i₁] at this
  have h02 : i₀ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₀, i₂] at this
  have h12 : i₁ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₁, i₂] at this
  simpa only [Fintype.card_fin] using positive_hollow_rank_three_signature
    P hP.2.1 hP.1 hP.2.2 hrank i₀ i₁ i₂ h01 h02 h12

/-- Assembly of all conclusions, still conditional on the one named
geometric obligation. This conditional statement is not a verification of
the paper's unconditional principal theorem. -/
theorem theorem11_from_rigidity (hn : 5 ≤ n)
    (hR : FullDimensionalRigidity (n := n))
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ closedProjectionLocus n ∧
      (sigPos P.toQuadraticForm' = 1 ∧
        sigNeg P.toQuadraticForm' = 2 ∧
        finrank ℝ P.toQuadraticForm'.radical = n - 3) ∧
      ∃ a : Fin n → ℝ,
        (∀ i, 0 < a i) ∧
        Tendsto (strictPerturb P a) (𝓝 0) (𝓝 P) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
          PositiveHollowSymmetric (strictPerturb P a ε) ∧
          StrictLorentzian (strictPerturb P a ε) ∧
          strictPerturb P a ε ∉ closedProjectionLocus n) ∧
        (∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
          ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
            Q.val ∉ closedProjectionLocus n) := by
  have hout := rank_three_exclusion_of_rigidity hn hR P hP hrank
  exact ⟨hout, rank_three_signature hn P hP hrank,
    rank_three_strict_family hn P hP hrank hout⟩

/-- The relative-open family is nonempty in every dimension at least five,
once the remaining geometric rigidity theorem has been supplied. -/
theorem exists_open_counterexamples_from_rigidity (hn : 5 ≤ n)
    (hR : FullDimensionalRigidity (n := n)) :
    ∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
      ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
        Q.val ∉ closedProjectionLocus n := by
  let P := VolumeVerification.RankThreeExamples.squaredIndexMatrix n
  have hP : PositiveHollowSymmetric P :=
    ⟨VolumeVerification.RankThreeExamples.squaredIndexMatrix_diagonal n,
      VolumeVerification.RankThreeExamples.squaredIndexMatrix_symmetric n,
      VolumeVerification.RankThreeExamples.squaredIndexMatrix_positive n⟩
  have hrank : P.rank = 3 :=
    VolumeVerification.RankThreeExamples.squaredIndexMatrix_rank n (by omega)
  obtain ⟨a, _ha, _hlim, _hsmall, hopen⟩ :=
    rank_three_strict_family hn P hP hrank
      (rank_three_exclusion_of_rigidity hn hR P hP hrank)
  exact hopen

end
end RankThreeProjection

end
end
end DevelopmentSource10

/- Source module: Projection.Rigidity.FullDimensional. SHA256: 14fad8afe58345f82cef94c0b53e350c3602f49683e756d9cc65e15eb52abf28 -/
section DevelopmentSource11






/-!
# Full-dimensional equality rigidity in the original coordinate model

The analytic theorem is proved in Euclidean coordinates. Only its actual
scalar mixed-volume conclusion is transported to the coordinate maximum-norm
space. The positive Haar conversion factor is explicit in the transfer
theorem. Strong support equality is then deduced for the original area
measures. No normal spheres or norms are silently identified.

The project's build and endpoint-audit reports record verification of this
source and its complete dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace RankThreeProjection
open VolumePolynomials Rigidity

/-- The actual weak hull conclusion for every full-dimensional coordinate
body. Neither interior of comparison bodies nor genericity of marked vectors
is required. -/
theorem weakHullReference_of_nonempty_interior {n d : ℕ}
    (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)
    (hK : (interior (K : Set (Space n))).Nonempty) :
    WeakHullReference volume (d := d) K := by
  have hn : n = d + 2 := by
    simpa only [Space, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
  subst n
  obtain ⟨p, hp⟩ := hK
  let K₀ : Body (d + 2) := translateBody (-p) K
  have hK₀ : (0 : Space (d + 2)) ∈ interior (K₀ : Set (Space (d + 2))) :=
    zero_mem_interior_translateBody_neg K p hp
  let T : Space (d + 2) ≃L[ℝ] OAI.PettyProjection.Space (d + 2) :=
    (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
  let L : ConvexBody (OAI.PettyProjection.Space (d + 2)) :=
    mapBody T.toContinuousLinearMap K₀
  have hL : (0 : OAI.PettyProjection.Space (d + 2)) ∈
      interior (L : Set (OAI.PettyProjection.Space (d + 2))) := by
    change (0 : OAI.PettyProjection.Space (d + 2)) ∈
      interior (T.toHomeomorph '' (K₀ : Set (Space (d + 2))))
    rw [← T.toHomeomorph.image_interior]
    exact ⟨0, hK₀, map_zero T⟩
  have hweakL : WeakHullReference volume (d := d) L := by
    apply weakHullReference_of_origin_comparisons volume L
    intro A C hA hC a ha hAA hAC hCC
    exact OAI.PettyProjection.euclidean_origin_weak_hull L A C hL hA hC
      a ha hAA hAC hCC
  have hweakK₀ : WeakHullReference volume (d := d) K₀ :=
    weakHullReference_of_frame volume volume T K₀ hweakL
  exact weakHullReference_of_translate volume K (-p) hweakK₀

/-- Full-dimensional segment-area rigidity, with the complete analytic and
convex-hull proof chain supplied. The only body hypothesis is actual nonempty
interior of the repeated body. -/
theorem segmentAreaRigidity_of_nonempty_interior {n d : ℕ} [NeZero n]
    (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)
    (hK : (interior (K : Set (Space n))).Nonempty) :
    SegmentAreaRigidity K hdim :=
  segmentAreaRigidity_of_weakHullReference_of_interior K hdim hK
    (weakHullReference_of_nonempty_interior K hdim hK)

theorem fullDimensionalRigidity (n : ℕ) [NeZero n] :
    FullDimensionalRigidity (n := n) := by
  intro K d hdim hK
  exact segmentAreaRigidity_of_nonempty_interior K hdim hK

/-- Proposition 4.2 for the actual marked mixed-volume array. Full
dimensionality is the only geometric assumption on the repeated body, and
the marked vectors are arbitrary. The equality-rigidity theorem is supplied
by the complete proof chain rather than retained as a hypothesis. -/
theorem full_dimensional_obstruction {n d : ℕ} (hn : 5 ≤ n)
    (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)
    (hK : (interior (K : Set (Space n))).Nonempty)
    (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank = 3) : False := by
  letI : NeZero n := ⟨by omega⟩
  exact full_dimensional_obstruction_from_segment_rigidity K hdim hn U hpos hrank
    (segmentAreaRigidity_of_nonempty_interior K hdim hK)

end RankThreeProjection
end
end
end DevelopmentSource11

/- Source module: Projection.Main. SHA256: 35046d9cc32b4c7e515244390556701dd154ac3e9b2598d524513047b0caabf2 -/
section DevelopmentSource12







/-!
# Principal statements of the projection-volume paper

The statements below retain the paper's unrestricted dimensions, positive
off-diagonal entries, actual matrix rank and inertia, actual coordinate
projection volumes, and topological closure. No rigidity proposition occurs
as an additional theorem hypothesis.

The project's status file, complete build log, and signature/axiom audit record
the verification evidence. The presence of these source statements alone is
not a certificate of mechanical verification.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Module Filter
open scoped Matrix Topology

namespace RankThreeProjection
open VolumeVerification.MatrixInertia

/-- The actual strict counterexamples, as a subset of the ordinary matrix
space. This set is used to state the paper's limit conclusion directly. -/
def strictCounterexampleLocus (n : ℕ) : Set (Array n) :=
  {Q | PositiveHollowSymmetric Q ∧ StrictLorentzian Q ∧
    Q ∉ closedProjectionLocus n}

/-- The exclusion conclusion of Theorem 1.1, for every n≥5. -/
theorem rank_three_projection_exclusion {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ closedProjectionLocus n := by
  letI : NeZero n := ⟨by omega⟩
  exact rank_three_exclusion_of_rigidity hn (fullDimensionalRigidity n) P hP hrank

/-- Theorem 1.1, including inertia, strict perturbations converging to each
rank-three matrix, and a nonempty relative-open family of strict counterexamples. -/
theorem theorem11 {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ closedProjectionLocus n ∧
      (sigPos P.toQuadraticForm' = 1 ∧
        sigNeg P.toQuadraticForm' = 2 ∧
        finrank ℝ P.toQuadraticForm'.radical = n - 3) ∧
      ∃ a : Fin n → ℝ,
        (∀ i, 0 < a i) ∧
        Tendsto (strictPerturb P a) (𝓝 0) (𝓝 P) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
          PositiveHollowSymmetric (strictPerturb P a ε) ∧
          StrictLorentzian (strictPerturb P a ε) ∧
          strictPerturb P a ε ∉ closedProjectionLocus n) ∧
        (∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
          ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
            Q.val ∉ closedProjectionLocus n) := by
  letI : NeZero n := ⟨by omega⟩
  exact theorem11_from_rigidity hn (fullDimensionalRigidity n) P hP hrank

/-- The limit assertion of Theorem 1.1 in its direct topological form.
This formally derives closure membership from the positive-parameter
perturbation family, rather than leaving that passage informal. -/
theorem rank_three_limit_strict_counterexamples {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∈ closure (strictCounterexampleLocus n) := by
  obtain ⟨a, _ha, hlim, ⟨δ, hδ, hsmall⟩, _hopen⟩ :=
    (theorem11 hn P hP hrank).2.2
  apply mem_closure_of_tendsto
    (hlim.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  have hδ' : Iio δ ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hδ'] with ε hε hεδ
  exact hsmall ε hε hεδ

/-- The nonempty open counterexample family exists in every dimension n≥5,
without taking the existence of a rank-three example as a hypothesis. -/
theorem exists_open_counterexamples {n : ℕ} (hn : 5 ≤ n) :
    ∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
      ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
        Q.val ∉ closedProjectionLocus n := by
  letI : NeZero n := ⟨by omega⟩
  exact exists_open_counterexamples_from_rigidity hn (fullDimensionalRigidity n)

/-- Theorem 1.1 with canonical Euclidean bodies and Euclidean projection
volume throughout. The exact coordinate-model equivalence has been proved,
including equality of realization loci, rather than assumed informally. -/
theorem theorem11_euclidean {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ euclideanClosedProjectionLocus n ∧
      (sigPos P.toQuadraticForm' = 1 ∧
        sigNeg P.toQuadraticForm' = 2 ∧
        finrank ℝ P.toQuadraticForm'.radical = n - 3) ∧
      ∃ a : Fin n → ℝ,
        (∀ i, 0 < a i) ∧
        Tendsto (strictPerturb P a) (𝓝 0) (𝓝 P) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
          PositiveHollowSymmetric (strictPerturb P a ε) ∧
          StrictLorentzian (strictPerturb P a ε) ∧
          strictPerturb P a ε ∉ euclideanClosedProjectionLocus n) ∧
        (∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
          ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
            Q.val ∉ euclideanClosedProjectionLocus n) := by
  simpa only [euclideanClosedProjectionLocus_eq] using theorem11 hn P hP hrank

end RankThreeProjection
end
end
end DevelopmentSource12

#check @RankThreeProjection.theorem11
#print axioms RankThreeProjection.theorem11
#check @RankThreeProjection.theorem11_euclidean
#print axioms RankThreeProjection.theorem11_euclidean
#check @RankThreeProjection.theorem31
#print axioms RankThreeProjection.theorem31
#check @RankThreeProjection.theorem31_with_dimension
#print axioms RankThreeProjection.theorem31_with_dimension
#check @RankThreeProjection.theorem31_renormalize_dimension
#print axioms RankThreeProjection.theorem31_renormalize_dimension
#check @RankThreeProjection.theorem31_euclidean
#print axioms RankThreeProjection.theorem31_euclidean
#check @RankThreeProjection.theorem31_euclidean_closure
#print axioms RankThreeProjection.theorem31_euclidean_closure
#check @RankThreeProjection.theorem31_euclidean_renormalize_dimension
#print axioms RankThreeProjection.theorem31_euclidean_renormalize_dimension
#check @RankThreeProjection.rank_three_projection_exclusion
#print axioms RankThreeProjection.rank_three_projection_exclusion
#check @RankThreeProjection.rank_three_limit_strict_counterexamples
#print axioms RankThreeProjection.rank_three_limit_strict_counterexamples
#check @RankThreeProjection.exists_open_counterexamples
#print axioms RankThreeProjection.exists_open_counterexamples
#check @RankThreeProjection.full_dimensional_obstruction
#print axioms RankThreeProjection.full_dimensional_obstruction
#check @VolumePapers.RankThree.no_nonnegative_weighted_triangles
#print axioms VolumePapers.RankThree.no_nonnegative_weighted_triangles
#check @RankThreeProjection.signature_iff_diagonal_sign_counts
#print axioms RankThreeProjection.signature_iff_diagonal_sign_counts
#assert_standard_axioms RankThreeProjection.theorem11
#assert_standard_axioms RankThreeProjection.theorem11_euclidean
#assert_standard_axioms RankThreeProjection.theorem31
#assert_standard_axioms RankThreeProjection.theorem31_with_dimension
#assert_standard_axioms RankThreeProjection.theorem31_renormalize_dimension
#assert_standard_axioms RankThreeProjection.theorem31_euclidean
#assert_standard_axioms RankThreeProjection.theorem31_euclidean_closure
#assert_standard_axioms RankThreeProjection.theorem31_euclidean_renormalize_dimension
#assert_standard_axioms RankThreeProjection.rank_three_projection_exclusion
#assert_standard_axioms RankThreeProjection.rank_three_limit_strict_counterexamples
#assert_standard_axioms RankThreeProjection.exists_open_counterexamples
#assert_standard_axioms RankThreeProjection.full_dimensional_obstruction
#assert_standard_axioms VolumePapers.RankThree.no_nonnegative_weighted_triangles
#assert_standard_axioms RankThreeProjection.signature_iff_diagonal_sign_counts
#export_checked_module_dependencies ".lake/reports/verification/Combined.dependencies.json"
