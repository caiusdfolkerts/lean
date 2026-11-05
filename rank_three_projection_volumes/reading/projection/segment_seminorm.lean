module
public import Projection.Extrusion
public import VolumePolynomials.ProjectionMonotonicity
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Tactic.Module
@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The actual segment mixed-volume seminorm

The seminorm used in Lemma 5.1 follows directly from Minkowski additivity,
monotonicity, and the inclusion `S_(u+v) ⊆ S_u + S_v`.  No Cauchy projection
formula is assumed.  The extrusion identity identifying the complementary
projection array with this seminorm remains a separate geometric theorem.
-/
namespace RankThreeProjection
open Set MeasureTheory Module VolumePolynomials
open scoped Pointwise BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smul_segmentBody (r : ℝ) (a b : E) :
    r • segmentBody a b = segmentBody (r • a) (r • b) := by
  apply ConvexBody.ext
  change (fun x : E => r • x) '' segment ℝ a b = segment ℝ (r • a) (r • b)
  exact image_segment ℝ (r • (LinearMap.id : E →ₗ[ℝ] E)).toAffineMap a b

theorem centeredSegment_smul (r : ℝ) (v : E) :
    centeredSegment (r • v) = r • centeredSegment v := by
  unfold centeredSegment
  rw [smul_segmentBody]
  congr 1 <;> simp only [smul_smul, mul_comm]

theorem centeredSegment_neg (v : E) :
    centeredSegment (-v) = centeredSegment v := by
  apply ConvexBody.ext
  change segment ℝ (-(1 / 2 : ℝ) • (-v)) ((1 / 2 : ℝ) • (-v)) =
    segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)
  simpa only [smul_neg, neg_smul, neg_neg] using
    segment_symm ℝ ((1 / 2 : ℝ) • v) (-((1 / 2 : ℝ) • v))

theorem centeredSegment_abs_smul (r : ℝ) (v : E) :
    centeredSegment (r • v) = |r| • centeredSegment v := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, centeredSegment_smul]
  · rw [abs_of_nonpos hr, ← centeredSegment_smul]
    simp only [neg_smul, centeredSegment_neg]

theorem centeredSegment_add_le (u v : E) :
    centeredSegment (u + v) ≤ centeredSegment u + centeredSegment v := by
  change segment ℝ (-(1 / 2 : ℝ) • (u + v)) ((1 / 2 : ℝ) • (u + v)) ⊆
    ((centeredSegment u + centeredSegment v : ConvexBody E) : Set E)
  apply (centeredSegment u + centeredSegment v).convex.segment_subset
  · rw [smul_add]
    exact Set.add_mem_add
      (left_mem_segment ℝ (-(1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • u))
      (left_mem_segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v))
  · rw [smul_add]
    exact Set.add_mem_add
      (right_mem_segment ℝ (-(1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • u))
      (right_mem_segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v))

section MixedVolume
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- `dim(E) * V(S_v, K₁, …, K_(dim(E)-1))` as a genuine Mathlib seminorm.
The background bodies are arbitrary compact convex bodies. -/
def segmentMixedVolumeSeminorm {n : ℕ} (K : Fin n → ConvexBody E)
    (hdim : finrank ℝ E = n + 1) : Seminorm ℝ E := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  refine Seminorm.of
    (fun v => (n + 1 : ℝ) * mixedVolume μ (Fin.cons (centeredSegment v) K)) ?_ ?_
  · intro u v
    have h := mixedVolume_mono_first_all μ K hdim _ _ (centeredSegment_add_le u v)
    have hadd : mixedVolume μ (Fin.cons (centeredSegment u + centeredSegment v) K) =
        mixedVolume μ (Fin.cons (centeredSegment u) K) +
          mixedVolume μ (Fin.cons (centeredSegment v) K) := by
      simpa only [Fin.update_cons_zero] using
        mixedVolume_add μ (Fin.cons (centeredSegment u) K) 0
          (centeredSegment u) (centeredSegment v)
    rw [hadd] at h
    simpa only [mul_add] using
      mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n + 1 : ℝ))
  · intro r v
    rw [centeredSegment_abs_smul]
    have hsmul : mixedVolume μ (Fin.cons (|r| • centeredSegment v) K) =
        |r| * mixedVolume μ (Fin.cons (centeredSegment v) K) := by
      simpa only [Fin.update_cons_zero] using
        mixedVolume_smul μ (Fin.cons (centeredSegment v) K) 0
          (centeredSegment v) (abs_nonneg r)
    rw [hsmul, Real.norm_eq_abs]
    ring

@[simp] theorem segmentMixedVolumeSeminorm_apply {n : ℕ}
    (K : Fin n → ConvexBody E) (hdim : finrank ℝ E = n + 1) (v : E) :
    segmentMixedVolumeSeminorm μ K hdim v =
      (n + 1 : ℝ) * mixedVolume μ (Fin.cons (centeredSegment v) K) := rfl

end MixedVolume

/-- The vector identity behind the hyperplane weighted triangle inequalities.
It holds for every seminorm and all labels, with no nonzero-weight assumption. -/
theorem seminorm_weighted_triangle {ι : Type*}
    (N : Seminorm ℝ E) (α : ι → ℝ) (b : ι → E) (i j k : ι) :
    N (α i • b j - α j • b i) * |α k| ≤
      N (α i • b k - α k • b i) * |α j| +
        N (α j • b k - α k • b j) * |α i| := by
  have he : α k • (α i • b j - α j • b i) =
      α j • (α i • b k - α k • b i) -
        α i • (α j • b k - α k • b j) := by module
  have h := map_sub_le_add N
    (α j • (α i • b k - α k • b i))
    (α i • (α j • b k - α k • b j))
  rw [← he, map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul] at h
  simpa only [Real.norm_eq_abs, mul_comm] using h

end RankThreeProjection
