module

public import VolumePolynomials.MinkowskiSeries
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

/-! Explicit nontrivial exposed segments in an infinite Minkowski series. -/

namespace VolumePolynomials

open scoped Topology
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A coefficient choice maximizing a fixed linear functional, one segment at a time. -/
noncomputable def maximizingChoice (l : E →L[ℝ] ℝ) (u : ℕ → E) : SegmentChoice := by
  first
  | classical
    exact fun n => if 0 ≤ l (u n) then ⟨1/2, by constructor <;> norm_num⟩
      else ⟨-(1/2), by constructor <;> norm_num⟩

theorem maximizingChoice_term (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (t : SegmentChoice) (n : ℕ) :
    l ((t n : ℝ) • u n) ≤ l ((maximizingChoice l u n : ℝ) • u n) := by
  first
  | classical
    simp only [map_smul, smul_eq_mul]
    by_cases h : 0 ≤ l (u n)
    · simp only [maximizingChoice, if_pos h]
      exact mul_le_mul_of_nonneg_right (t n).property.2 h
    · simp only [maximizingChoice, if_neg h]
      exact mul_le_mul_of_nonpos_right (t n).property.1 (le_of_not_ge h)

theorem maximizingChoice_maximal (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) {x : E} (hx : x ∈ segmentSeries u) :
    l x ≤ l (seriesPoint u (maximizingChoice l u)) := by
  first
  | obtain ⟨t, rfl⟩ := hx
    rw [seriesPoint, seriesPoint, l.map_tsum (series_summable u hu t),
      l.map_tsum (series_summable u hu (maximizingChoice l u))]
    exact Summable.tsum_le_tsum (maximizingChoice_term l u t)
      (l.summable (series_summable u hu t))
      (l.summable (series_summable u hu (maximizingChoice l u)))

theorem seriesPoint_update_sub (u : ℕ → E) (hu : Summable fun n => ‖u n‖)
    (t : SegmentChoice) (j : ℕ) (a b : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    seriesPoint u (Function.update t j a) - seriesPoint u (Function.update t j b) =
      ((a : ℝ) - (b : ℝ)) • u j := by
  first
  | classical
    rw [seriesPoint, seriesPoint, ← Summable.tsum_sub
      (series_summable u hu (Function.update t j a))
      (series_summable u hu (Function.update t j b))]
    rw [tsum_eq_single j]
    · simp [sub_smul]
    · intro n hn
      simp [Function.update_of_ne hn]

theorem maximizingChoice_update_value (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    l (seriesPoint u (Function.update (maximizingChoice l u) j a)) =
      l (seriesPoint u (maximizingChoice l u)) := by
  first
  | classical
    rw [seriesPoint, seriesPoint,
      l.map_tsum (series_summable u hu (Function.update (maximizingChoice l u) j a)),
      l.map_tsum (series_summable u hu (maximizingChoice l u))]
    apply tsum_congr
    intro n
    by_cases hn : n = j
    · subst n
      simp [map_smul, hj]
    · simp [Function.update_of_ne hn]

theorem maximizingChoice_update_mem_exposed (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    seriesPoint u (Function.update (maximizingChoice l u) j a) ∈
      l.toExposed (segmentSeries u) := by
  first
  | constructor
    · exact ⟨Function.update (maximizingChoice l u) j a, rfl⟩
    · intro y hy
      rw [maximizingChoice_update_value l u hu j hj a]
      exact maximizingChoice_maximal l u hu hy

/-- A maximizer of a functional having a positive direction cannot be an interior point. -/
theorem exposed_mem_frontier (l : E →L[ℝ] ℝ) (s : Set E) (v : E)
    (hv : 0 < l v) {x : E} (hx : x ∈ l.toExposed s) : x ∈ frontier s := by
  first
  | rw [mem_frontier_iff_notMem_interior hx.1]
    intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    have hvne : v ≠ 0 := by intro h; simpa [h] using hv
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    let t : ℝ := ε / (2 * ‖v‖)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hvnorm)
    have hdist : dist (x + t • v) x < ε := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖v‖ = ε / 2 := by
        dsimp [t]
        field_simp [hvnorm.ne'] <;> ring
      rw [heq]
      linarith
    have hmem : x + t • v ∈ s := hball hdist
    have hle := hx.2 (x + t • v) hmem
    rw [map_add, map_smul, smul_eq_mul] at hle
    have : 0 < t * l v := mul_pos ht hv
    linarith

/-- The whole translated j-th centered segment is exposed, not just its endpoints. -/
theorem translated_segment_mem_exposed (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0) :
    ∃ a : E, ∀ t : ℝ, -(1/2 : ℝ) ≤ t → t ≤ 1/2 →
      a + t • u j ∈ l.toExposed (segmentSeries u) := by
  first
  | classical
    let z : Icc (- (1/2 : ℝ)) (1/2 : ℝ) := ⟨0, by constructor <;> norm_num⟩
    let a := seriesPoint u (Function.update (maximizingChoice l u) j z)
    refine ⟨a, ?_⟩
    intro t htlo hthi
    let q : Icc (- (1/2 : ℝ)) (1/2 : ℝ) := ⟨t, htlo, hthi⟩
    have heq := seriesPoint_update_sub u hu (maximizingChoice l u) j q z
    have heq' : seriesPoint u (Function.update (maximizingChoice l u) j q) = a + t • u j := by
      dsimp [a, q, z] at *
      simpa [sub_eq_iff_eq_add, add_comm] using heq
    rw [← heq']
    exact maximizingChoice_update_mem_exposed l u hu j hj q

theorem translated_segment_mem_frontier (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (v : E) (hv : 0 < l v) :
    ∃ a : E, ∀ t : ℝ, -(1/2 : ℝ) ≤ t → t ≤ 1/2 →
      a + t • u j ∈ frontier (segmentSeries u) := by
  first
  | obtain ⟨a, ha⟩ := translated_segment_mem_exposed l u hu j hj
    exact ⟨a, fun t htlo hthi => exposed_mem_frontier l _ v hv (ha t htlo hthi)⟩

/-- At a maximizing point, every coefficient whose direction has nonzero support value is
forced to its unique maximizing endpoint. -/
theorem maximizingChoice_unique_coordinate (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (t : SegmentChoice)
    (ht : l (seriesPoint u t) = l (seriesPoint u (maximizingChoice l u)))
    (n : ℕ) (hn : l (u n) ≠ 0) : t n = maximizingChoice l u n := by
  first
  | let f : ℕ → ℝ := fun k => l ((maximizingChoice l u k : ℝ) • u k) - l ((t k : ℝ) • u k)
    have hf : Summable f :=
      (l.summable (series_summable u hu (maximizingChoice l u))).sub
        (l.summable (series_summable u hu t))
    have hfnonneg (k : ℕ) : 0 ≤ f k := sub_nonneg.mpr (maximizingChoice_term l u t k)
    have hsum : ∑' k, f k = 0 := by
      rw [Summable.tsum_sub
        (l.summable (series_summable u hu (maximizingChoice l u)))
        (l.summable (series_summable u hu t)),
        ← l.map_tsum (series_summable u hu (maximizingChoice l u)),
        ← l.map_tsum (series_summable u hu t)]
      exact sub_eq_zero.mpr ht.symm
    have hle := hf.le_tsum n (fun k _ => hfnonneg k)
    rw [hsum] at hle
    have heq : f n = 0 := le_antisymm hle (hfnonneg n)
    dsimp [f] at heq
    simp only [map_smul, smul_eq_mul] at heq
    apply Subtype.ext
    exact (mul_right_cancel₀ hn (sub_eq_zero.mp heq)).symm

/-- If just one generating direction is perpendicular to the normal, its whole centered
segment, translated by the endpoint sum, is exactly the exposed face. -/
theorem exposed_face_eq_centered_segment (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (hnonzero : ∀ n, n ≠ j → l (u n) ≠ 0) :
    ∃ a : E, l.toExposed (segmentSeries u) =
      {x | ∃ t : Icc (- (1/2 : ℝ)) (1/2 : ℝ), x = a + (t : ℝ) • u j} := by
  first
  | classical
    let z : Icc (- (1/2 : ℝ)) (1/2 : ℝ) := ⟨0, by constructor <;> norm_num⟩
    let a := seriesPoint u (Function.update (maximizingChoice l u) j z)
    have heq (t : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
        seriesPoint u (Function.update (maximizingChoice l u) j t) = a + (t : ℝ) • u j := by
      have h := seriesPoint_update_sub u hu (maximizingChoice l u) j t z
      dsimp [a, z] at *
      simpa [sub_eq_iff_eq_add, add_comm] using h
    refine ⟨a, Set.ext fun x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨t, rfl⟩ := hx.1
      have hval : l (seriesPoint u t) = l (seriesPoint u (maximizingChoice l u)) :=
        (maximizingChoice_maximal l u hu ⟨t, rfl⟩).antisymm
          (hx.2 _ ⟨maximizingChoice l u, rfl⟩)
      have ht : t = Function.update (maximizingChoice l u) j (t j) := by
        funext n
        by_cases hn : n = j
        · subst n
          simp
        · rw [Function.update_of_ne hn]
          exact maximizingChoice_unique_coordinate l u hu t hval n (hnonzero n hn)
      refine ⟨t j, ?_⟩
      conv_lhs => rw [ht]
      exact heq (t j)
    · rintro ⟨t, rfl⟩
      rw [← heq t]
      exact maximizingChoice_update_mem_exposed l u hu j hj t

end VolumePolynomials
