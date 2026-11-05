module

public import VolumePolynomials.ShapeTuple
public import VolumePolynomials.HolonomySeries
public import VolumePolynomials.MinkowskiSeriesMaps
public import VolumePolynomials.ZonoidRealization3

@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

/-- The three plane embeddings with the transport coordinates built in. -/
def placedA : Plane →L[ℝ] ThreeSpace := embedXY
def placedB : Plane →L[ℝ] ThreeSpace := embedXZ.comp transport01.toContinuousLinearMap
def placedC : Plane →L[ℝ] ThreeSpace :=
  embedYZ.comp (transport12.toContinuousLinearMap.comp transport01.toContinuousLinearMap)

/-- The nine bodies in the constructive half of Theorem 1.2. -/
def canonicalTuple (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) : Fin 9 → Body 3 :=
  ![centeredBody (axis 0), centeredBody (axis 1), centeredBody (axis 2),
    centeredBody directionV, centeredBody directionW, centeredBody directionZ,
    mapBody placedA (forcedBody lam hlam₀ hlam₁),
    mapBody placedB (forcedBody lam hlam₀ hlam₁),
    mapBody placedC (forcedBody lam hlam₀ hlam₁)]

/-- All nine entries have honest summable segment representations. -/
def canonicalGenerators (lam : ℝ) : Fin 9 → ℕ → ThreeSpace :=
  ![oneTermSequence (axis 0), oneTermSequence (axis 1), oneTermSequence (axis 2),
    oneTermSequence directionV, oneTermSequence directionW, oneTermSequence directionZ,
    fun n => placedA (weightedOrbit lam n),
    fun n => placedB (weightedOrbit lam n),
    fun n => placedC (weightedOrbit lam n)]

theorem canonicalGenerators_summable (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (i : Fin 9) : Summable (fun n => ‖canonicalGenerators lam i n‖) := by
  first
  | fin_cases i
    · exact oneTermSequence_summable (axis 0)
    · exact oneTermSequence_summable (axis 1)
    · exact oneTermSequence_summable (axis 2)
    · exact oneTermSequence_summable directionV
    · exact oneTermSequence_summable directionW
    · exact oneTermSequence_summable directionZ
    · exact summable_norm_linear_image placedA (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact summable_norm_linear_image placedB (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact summable_norm_linear_image placedC (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)

theorem segmentSeriesBody_oneTermSequence (v : ThreeSpace) :
    segmentSeriesBody (oneTermSequence v) (oneTermSequence_summable v) = centeredBody v := by
  first
  | apply ConvexBody.ext
    change segmentSeries (oneTermSequence v) = (centeredBody v : Set ThreeSpace)
    rw [segmentSeries_oneTermSequence, centeredSegment_eq_image, centeredBody_carrier]

theorem canonicalTuple_eq_series (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    canonicalTuple lam hlam₀ hlam₁ =
      fun i => segmentSeriesBody (canonicalGenerators lam i)
        (canonicalGenerators_summable lam hlam₀ hlam₁ i) := by
  first
  | funext i
    fin_cases i
    · exact (segmentSeriesBody_oneTermSequence (axis 0)).symm
    · exact (segmentSeriesBody_oneTermSequence (axis 1)).symm
    · exact (segmentSeriesBody_oneTermSequence (axis 2)).symm
    · exact (segmentSeriesBody_oneTermSequence directionV).symm
    · exact (segmentSeriesBody_oneTermSequence directionW).symm
    · exact (segmentSeriesBody_oneTermSequence directionZ).symm
    · exact map_segmentSeriesBody placedA (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact map_segmentSeriesBody placedB (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact map_segmentSeriesBody placedC (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)

/-- Full genuine cubic polynomial existence for the nine-body construction,
with all nonnegative real weights and all 165 cubic coefficient coordinates. -/
theorem canonicalTuple_realizes (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    ∃ c : Coefficients 9 3, Realizes (canonicalTuple lam hlam₀ hlam₁) c := by
  first
  | rw [canonicalTuple_eq_series]
    exact summable_segment_series_realizes (canonicalGenerators lam)
      (canonicalGenerators_summable lam hlam₀ hlam₁)

theorem canonicalTuple_calibrated (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    IsCalibratedTuple (canonicalTuple lam hlam₀ hlam₁) := by
  first
  | constructor
    · intro i
      fin_cases i <;> rfl
    · exact ⟨0, zero_mem_segmentSeries (weightedOrbit lam), map_zero placedA⟩
    · exact ⟨0, zero_mem_segmentSeries (weightedOrbit lam), map_zero placedB⟩
    · exact ⟨0, zero_mem_segmentSeries (weightedOrbit lam), map_zero placedC⟩
    · rintro x ⟨p, hp, rfl⟩
      rfl
    · rintro x ⟨p, hp, rfl⟩
      rfl
    · rintro x ⟨p, hp, rfl⟩
      rfl


end VolumePolynomials.Holonomy
