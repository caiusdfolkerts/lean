module

public import mixed_volume.general.indexed_series

/-! Support functions of actual indexed segment bodies, with exact finite
Minkowski combinations. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.SeriesSupport

open VolumePolynomials VolumePolynomials.BodySupport Set
open scoped Pointwise BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ext (K L : ConvexBody E)
    (h : ∀ l : E →L[ℝ] ℝ, support K l = support L l) : K = L := by
  exact ConvexBody.ext (OAI.Paper092.SupportGeometry.eq_of_support_eq
    K.isCompact K.nonempty K.convex L.isCompact L.nonempty L.convex h)

theorem support_add (K L : ConvexBody E) (l : E →L[ℝ] ℝ) :
    support (K + L) l = support K l + support L l :=
  OAI.Paper092.SupportGeometry.support_add K.isCompact K.nonempty L.isCompact L.nonempty l

theorem support_smul (K : ConvexBody E) (l : E →L[ℝ] ℝ) {r : ℝ} (hr : 0 ≤ r) :
    support (r • K) l = r * support K l :=
  OAI.Paper092.SupportGeometry.support_smul (K : Set E) l hr

@[simp] theorem support_point (p : E) (l : E →L[ℝ] ℝ) :
    support (pointBody p) l = l p := by
  simp only [BodySupport.support, coe_pointBody, Set.image_singleton, csSup_singleton]

@[simp] theorem support_zero (l : E →L[ℝ] ℝ) : support (0 : ConvexBody E) l = 0 := by
  change support (pointBody 0) l = 0
  rw [support_point, map_zero]

theorem support_translate (K : ConvexBody E) (p : E) (l : E →L[ℝ] ℝ) :
    support (translateBody p K) l = l p + support K l := by
  rw [translateBody, support_add, support_point]

theorem support_sum {κ : Type*} (q : Finset κ) (K : κ → ConvexBody E) (l : E →L[ℝ] ℝ) :
    support (∑ j ∈ q, K j) l = ∑ j ∈ q, support (K j) l := by
  classical
  induction q using Finset.induction_on with
  | empty => simp
  | @insert j q hj ih => simp only [Finset.sum_insert hj, support_add, ih]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem support_map (K : ConvexBody E) (f : E →L[ℝ] F) (l : F →L[ℝ] ℝ) :
    support (mapBody f K) l = support K (l.comp f) := by
  dsimp [BodySupport.support]
  rw [Set.image_image]
  rfl

variable {ι : Type*} [DecidableEq ι] [CompleteSpace E]

open IndexedSeries

theorem summable_abs_image (l : E →L[ℝ] ℝ) (u : ι → E)
    (hu : Summable fun i => ‖u i‖) : Summable fun i => |l (u i)| := by
  simpa only [Real.norm_eq_abs] using IndexedSeries.summable_norm_linear_image l u hu

theorem maximizing_value (l : E →L[ℝ] ℝ) (u : ι → E)
    (hu : Summable fun i => ‖u i‖) :
    l (IndexedSeries.seriesPoint u (IndexedSeries.maximizingChoice l u)) = (1 / 2 : ℝ) * ∑' i, |l (u i)| := by
  rw [IndexedSeries.seriesPoint, l.map_tsum (IndexedSeries.series_summable u hu (IndexedSeries.maximizingChoice l u)), ← tsum_mul_left]
  apply tsum_congr
  intro i
  simp only [map_smul, smul_eq_mul, IndexedSeries.maximizingChoice]
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

theorem support_series (l : E →L[ℝ] ℝ) (u : ι → E)
    (hu : Summable fun i => ‖u i‖) :
    support (IndexedSeries.segmentSeriesBody u hu) l = (1 / 2 : ℝ) * ∑' i, |l (u i)| := by
  rw [← maximizing_value l u hu]
  apply le_antisymm
  · exact BodySupport.support_le _ _ (fun x hx => IndexedSeries.maximizingChoice_maximal l u hu hx)
  · exact BodySupport.le_support _ _ ⟨IndexedSeries.maximizingChoice l u, rfl⟩

theorem support_weighted (l : E →L[ℝ] ℝ) (g : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hcs : Summable fun i => ‖c i • g i‖) :
    support (IndexedSeries.segmentSeriesBody (fun i => c i • g i) hcs) l =
      ∑' i, c i * ((1 / 2 : ℝ) * |l (g i)|) := by
  rw [support_series, ← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hc i)]
  ring

theorem weighted_support_summable (l : E →L[ℝ] ℝ) (g : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hcs : Summable fun i => ‖c i • g i‖) :
    Summable fun i => c i * ((1 / 2 : ℝ) * |l (g i)|) := by
  have h := (summable_abs_image l (fun i => c i • g i) hcs).mul_left (1 / 2 : ℝ)
  convert h using 1
  ext i
  rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hc i)]
  ring

theorem weighted_combination {κ : Type*} [Fintype κ]
    (g : ι → E) (c : κ → ι → ℝ) (p : κ → ℝ)
    (hc : ∀ j i, 0 ≤ c j i) (hp : ∀ j, 0 ≤ p j)
    (hcs : ∀ j, Summable fun i => ‖c j i • g i‖)
    (hsum : Summable fun i => ‖(∑ j, p j * c j i) • g i‖) :
    (∑ j, p j • IndexedSeries.segmentSeriesBody (fun i => c j i • g i) (hcs j)) =
      IndexedSeries.segmentSeriesBody (fun i => (∑ j, p j * c j i) • g i) hsum := by
  apply ext
  intro l
  rw [support_sum, support_weighted l g _
    (fun i => Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (hc j i)))]
  simp_rw [support_smul _ _ (hp _), support_weighted _ _ _ (hc _) (hcs _)]
  have ht (j : κ) : Summable fun i => p j * (c j i * ((1 / 2 : ℝ) * |l (g i)|)) :=
    (weighted_support_summable l g (c j) (hc j) (hcs j)).mul_left (p j)
  have hcomm := (hasSum_sum (s := (Finset.univ : Finset κ)) (fun j _ => (ht j).hasSum)).tsum_eq
  calc
    (∑ j, p j * ∑' i, c j i * ((1 / 2 : ℝ) * |l (g i)|)) =
        ∑ j, ∑' i, p j * (c j i * ((1 / 2 : ℝ) * |l (g i)|)) := by
          simp only [tsum_mul_left]
    _ = ∑' i, ∑ j, p j * (c j i * ((1 / 2 : ℝ) * |l (g i)|)) := hcomm.symm
    _ = ∑' i, (∑ j, p j * c j i) * ((1 / 2 : ℝ) * |l (g i)|) := by
      apply tsum_congr
      intro i
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end MixedVolume.SeriesSupport

end
