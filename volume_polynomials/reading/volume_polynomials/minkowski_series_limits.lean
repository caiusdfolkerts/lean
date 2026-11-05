module

public import VolumePolynomials.MinkowskiSeries
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology Pointwise
open Set Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def prefixPoint (u : ℕ → E) (N : ℕ) (t : SegmentChoice) : E :=
  ∑ n ∈ Finset.range N, (t n : ℝ) • u n

def prefixSeries (u : ℕ → E) (N : ℕ) : Set E := Set.range (prefixPoint u N)

theorem prefixPoint_continuous (u : ℕ → E) (N : ℕ) : Continuous (prefixPoint u N) := by
  first
  | apply continuous_finsetSum
    intro n hn
    exact ((continuous_apply n).subtype_val).smul continuous_const

theorem prefixSeries_isCompact (u : ℕ → E) (N : ℕ) : IsCompact (prefixSeries u N) :=
  isCompact_range (prefixPoint_continuous u N)

theorem zero_mem_prefixSeries (u : ℕ → E) (N : ℕ) : (0 : E) ∈ prefixSeries u N := by
  first
  | refine ⟨fun _ => ⟨0, by constructor <;> norm_num⟩, ?_⟩
    simp [prefixPoint]

theorem prefixSeries_convex (u : ℕ → E) (N : ℕ) : Convex ℝ (prefixSeries u N) := by
  first
  | intro x hx y hy a b ha hb hab
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    let w : SegmentChoice := fun n =>
      ⟨a * (s n : ℝ) + b * (t n : ℝ), by
        change a • (s n : ℝ) + b • (t n : ℝ) ∈ Icc (- (1/2 : ℝ)) (1/2 : ℝ)
        exact (convex_Icc (𝕜 := ℝ) (- (1/2 : ℝ)) (1/2 : ℝ))
          (s n).property (t n).property ha hb hab⟩
    refine ⟨w, ?_⟩
    simp [prefixPoint, w, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

def prefixBody (u : ℕ → E) (N : ℕ) : ConvexBody E where
  carrier := prefixSeries u N
  convex' := prefixSeries_convex u N
  isCompact' := prefixSeries_isCompact u N
  nonempty' := ⟨0, zero_mem_prefixSeries u N⟩

def truncatedChoice (N : ℕ) (t : SegmentChoice) : SegmentChoice :=
  fun n => if n < N then t n else ⟨0, by constructor <;> norm_num⟩

theorem seriesPoint_truncated (u : ℕ → E) (N : ℕ) (t : SegmentChoice) :
    seriesPoint u (truncatedChoice N t) = prefixPoint u N t := by
  first
  | unfold seriesPoint
    rw [tsum_eq_sum (s := Finset.range N) (by
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [truncatedChoice, hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [truncatedChoice, Finset.mem_range.mp hn]

theorem prefixSeries_subset (u : ℕ → E) (N : ℕ) : prefixSeries u N ⊆ segmentSeries u := by
  first
  | rintro x ⟨t, rfl⟩
    exact ⟨truncatedChoice N t, seriesPoint_truncated u N t⟩

theorem prefixPoint_succ (u : ℕ → E) (N : ℕ) (t : SegmentChoice) :
    prefixPoint u (N + 1) t = prefixPoint u N t + (t N : ℝ) • u N := by
  first
  | exact Finset.sum_range_succ _ _

theorem prefixPoint_update (u : ℕ → E) (N : ℕ) (t : SegmentChoice)
    (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    prefixPoint u N (Function.update t N a) = prefixPoint u N t := by
  first
  | classical
    apply Finset.sum_congr rfl
    intro n hn
    rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hn))]

theorem prefixSeries_zero (u : ℕ → E) : prefixSeries u 0 = {0} := by
  first
  | ext x
    constructor
    · rintro ⟨t, rfl⟩
      simp [prefixPoint]
    · intro hx
      have hxzero : x = 0 := Set.mem_singleton_iff.mp hx
      rw [hxzero]
      exact zero_mem_prefixSeries u 0

theorem prefixSeries_succ (u : ℕ → E) (N : ℕ) :
    prefixSeries u (N + 1) = prefixSeries u N + centeredSegment (u N) := by
  first
  | classical
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact Set.mem_add.mpr ⟨prefixPoint u N t, ⟨t, rfl⟩, (t N : ℝ) • u N,
        ⟨t N, rfl⟩, (prefixPoint_succ u N t).symm⟩
    · intro hx
      obtain ⟨y, ⟨t, rfl⟩, z, ⟨a, rfl⟩, rfl⟩ := Set.mem_add.mp hx
      refine ⟨Function.update t N a, ?_⟩
      rw [prefixPoint_succ, prefixPoint_update]
      simp

def seriesTailBound (u : ℕ → E) (N : ℕ) : ℝ :=
  (1/2 : ℝ) * ∑' k, ‖u (k + N)‖

theorem seriesTailBound_nonneg (u : ℕ → E) (N : ℕ) : 0 ≤ seriesTailBound u N := by
  first
  | apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun _ => norm_nonneg _)

theorem seriesTailBound_tendsto (u : ℕ → E) : Tendsto (seriesTailBound u) atTop (𝓝 0) := by
  first
  | change Tendsto (fun N => (1/2 : ℝ) * ∑' k, ‖u (k + N)‖) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_sum_nat_add (fun n => ‖u n‖)).const_mul (1/2 : ℝ)

theorem seriesPoint_sub_prefix (u : ℕ → E) (hu : Summable fun n => ‖u n‖)
    (N : ℕ) (t : SegmentChoice) :
    seriesPoint u t - prefixPoint u N t = ∑' k, (t (k + N) : ℝ) • u (k + N) := by
  first
  | have hs := (series_summable u hu t).sum_add_tsum_nat_add N
    unfold seriesPoint prefixPoint
    rw [← hs]
    simp

theorem seriesPoint_dist_prefix_le (u : ℕ → E) (hu : Summable fun n => ‖u n‖)
    (N : ℕ) (t : SegmentChoice) :
    dist (seriesPoint u t) (prefixPoint u N t) ≤ seriesTailBound u N := by
  first
  | rw [dist_eq_norm, seriesPoint_sub_prefix u hu N t]
    have htail : Summable (fun k => ‖u (k + N)‖) := (summable_nat_add_iff N).mpr hu
    have hbound := tsum_of_norm_bounded (htail.mul_left (1/2)).hasSum
      (fun k => series_term_norm_le u t (k + N))
    simpa only [tsum_mul_left, seriesTailBound] using hbound

/-- Quantitative Hausdorff convergence, for the actual compact convex finite and infinite sums. -/
theorem prefixBody_dist_le (u : ℕ → E) (hu : Summable fun n => ‖u n‖) (N : ℕ) :
    dist (prefixBody u N) (segmentSeriesBody u hu) ≤ seriesTailBound u N := by
  first
  | change hausdorffDist (prefixSeries u N) (segmentSeries u) ≤ seriesTailBound u N
    apply hausdorffDist_le_of_mem_dist (seriesTailBound_nonneg u N)
    · intro x hx
      exact ⟨x, prefixSeries_subset u N hx, by simpa using seriesTailBound_nonneg u N⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨prefixPoint u N t, ⟨t, rfl⟩, seriesPoint_dist_prefix_le u hu N t⟩

theorem prefixBody_tendsto (u : ℕ → E) (hu : Summable fun n => ‖u n‖) :
    Tendsto (prefixBody u) atTop (𝓝 (segmentSeriesBody u hu)) := by
  first
  | apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (prefixBody_dist_le u hu) (seriesTailBound_tendsto u)

end VolumePolynomials
