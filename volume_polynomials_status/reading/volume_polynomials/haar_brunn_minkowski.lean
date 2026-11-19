module

public import VolumePolynomials.LinearFrame
public import VolumePolynomials.BodyOperations
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic

@[expose] public section
set_option autoImplicit false

/-! # Brunn--Minkowski for the specified Haar measure in any finite normed space

An actual continuous linear coordinate equivalence transports the theorem to
Euclidean space. The positive Haar normalization factor is carried through
the dimension root explicitly.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem haar_brunn_minkowski (hdim : finrank ℝ E ≠ 0)
    (A B : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * μ.real (A : Set E) ^ ((finrank ℝ E : ℝ)⁻¹) +
      b * μ.real (B : Set E) ^ ((finrank ℝ E : ℝ)⁻¹) ≤
      μ.real (a • A + b • B : ConvexBody E) ^ ((finrank ℝ E : ℝ)⁻¹) := by
  first
  | letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := inferInstanceAs (Measure.IsAddHaarMeasure μ)
    let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    let C := mapBody T.toContinuousLinearMap A
    let D := mapBody T.toContinuousLinearMap B
    let c : ℝ := LinearFrame.volumeFactor T
    have hc : 0 ≤ c := NNReal.coe_nonneg _
    have hscale (K : ConvexBody E) :
        μ.real (K : Set E) = c * volume.real (mapBody T.toContinuousLinearMap K :
          Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) := by
      first
      | rw [coe_mapBody, ContinuousLinearEquiv.coe_coe]
        exact LinearFrame.realVolume_eq_factor_mul_image T (K : Set E)
    have hfin : volume (a • (C : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) + b • (D : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) ≠ ⊤ := by
      simpa only [ConvexBody.coe_add, ConvexBody.coe_smul] using
        (a • C + b • D).isCompact.measure_ne_top
    have h := TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le
      (E := EuclideanSpace ℝ (Fin (finrank ℝ E))) (by simpa using hdim)
      C.nonempty C.isCompact.measurableSet.nullMeasurableSet
      D.nonempty D.isCompact.measurableSet.nullMeasurableSet ha hb hfin
    have h' : a * volume.real (C : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ^ ((finrank ℝ E : ℝ)⁻¹) +
        b * volume.real (D : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ^ ((finrank ℝ E : ℝ)⁻¹) ≤
        volume.real ((a • C + b • D : ConvexBody _) :
          Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ^ ((finrank ℝ E : ℝ)⁻¹) := by
      simpa only [finrank_euclideanSpace_fin, ConvexBody.coe_add, ConvexBody.coe_smul] using h
    rw [hscale A, hscale B, hscale (a • A + b • B), mapBody_add,
      mapBody_smul, mapBody_smul]
    simp only [Real.mul_rpow hc measureReal_nonneg]
    have hmul := mul_le_mul_of_nonneg_left h' (Real.rpow_nonneg hc ((finrank ℝ E : ℝ)⁻¹))
    convert hmul using 1 <;> simp only [C, D] <;> ring

end VolumePolynomials
