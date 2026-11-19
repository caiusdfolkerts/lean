module

public import VolumePolynomials.MinkowskiSeries
public import VolumePolynomials.BodyOperations

@[expose] public section
noncomputable section

open Set

namespace VolumePolynomials

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem summable_norm_linear_image (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) : Summable (fun n => ‖f (u n)‖) := by
  first
  | apply (hu.mul_left ‖f‖).of_norm_bounded
    intro n
    rw [norm_norm]
    exact f.le_opNorm (u n)

theorem map_seriesPoint (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) (t : SegmentChoice) :
    f (seriesPoint u t) = seriesPoint (fun n => f (u n)) t := by
  first
  | rw [seriesPoint, f.map_tsum (series_summable u hu t)]
    simp only [map_smul, seriesPoint]

theorem image_segmentSeries (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) :
    f '' segmentSeries u = segmentSeries (fun n => f (u n)) := by
  first
  | ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (map_seriesPoint f u hu t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨seriesPoint u t, ⟨t, rfl⟩, map_seriesPoint f u hu t⟩

theorem map_segmentSeriesBody (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) :
    mapBody f (segmentSeriesBody u hu) =
      segmentSeriesBody (fun n => f (u n)) (summable_norm_linear_image f u hu) := by
  first
  | apply ConvexBody.ext
    exact image_segmentSeries f u hu

def oneTermSequence (v : E) (n : ℕ) : E := if n = 0 then v else 0

theorem oneTermSequence_summable (v : E) :
    Summable (fun n => ‖oneTermSequence v n‖) := by
  first
  | simpa only [oneTermSequence, apply_ite, norm_zero] using
      (hasSum_ite_eq (0 : ℕ) ‖v‖).summable

theorem seriesPoint_oneTermSequence (v : E) (t : SegmentChoice) :
    seriesPoint (oneTermSequence v) t = (t 0 : ℝ) • v := by
  first
  | simp [seriesPoint, oneTermSequence, smul_ite]

theorem segmentSeries_oneTermSequence (v : E) :
    segmentSeries (oneTermSequence v) = centeredSegment v := by
  first
  | ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t 0, seriesPoint_oneTermSequence v t⟩
    · rintro ⟨a, rfl⟩
      exact ⟨fun _ => a, seriesPoint_oneTermSequence v (fun _ => a)⟩

end VolumePolynomials
