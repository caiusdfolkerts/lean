module

public import VolumePolynomials.MixedVolume
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

set_option autoImplicit false

/-! # Exact transport of actual mixed volume through measure-preserving frames -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators NNReal

namespace VolumePolynomials

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  (ν : Measure F) [Measure.IsAddHaarMeasure ν]

theorem measureReal_image_measurePreserving (T : E ≃L[ℝ] F)
    (hT : MeasurePreserving T μ ν) (S : Set E) : ν.real (T '' S) = μ.real S := by
  first
  | have h := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' S)
    rw [Set.preimage_image_eq S T.injective] at h
    exact congrArg ENNReal.toReal h.symm

theorem volumePolynomial_map_measurePreserving {n : ℕ}
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T μ ν) (K : Fin n → ConvexBody E) :
    volumePolynomial ν (fun i => mapBody T.toContinuousLinearMap (K i)) = volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • mapBody T.toContinuousLinearMap (K i)) =
        mapBody T.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody T.toContinuousLinearMap (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul T.toContinuousLinearMap (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom T.toContinuousLinearMap) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    exact (measureReal_image_measurePreserving μ ν T hT _).symm

theorem mixedVolume_map_measurePreserving {n : ℕ}
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T μ ν) (K : Fin n → ConvexBody E) :
    mixedVolume ν (fun i => mapBody T.toContinuousLinearMap (K i)) = mixedVolume μ K := by
  first
  | simp only [mixedVolume, volumePolynomial_map_measurePreserving μ ν T hT K]

/-- The actual Haar conversion factor; it is positive and is not supplied as
an unverified Jacobian hypothesis. -/
def mixedVolumeFrameFactor (T : E ≃L[ℝ] F) : ℝ≥0 :=
  Measure.addHaarScalarFactor (μ.map T) ν

theorem mixedVolumeFrameFactor_pos (T : E ≃L[ℝ] F) :
    0 < mixedVolumeFrameFactor μ ν T :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem measureReal_eq_frameFactor_mul_image (T : E ≃L[ℝ] F) (S : Set E) :
    μ.real S = (mixedVolumeFrameFactor μ ν T : ℝ) * ν.real (T '' S) := by
  first
  | have hm : (μ.map T) (T '' S) = μ S := by
      first
      | change (μ.map T.toHomeomorph) (T.toHomeomorph '' S) = μ S
        rw [T.toHomeomorph.measurableEmbedding.map_apply,
          Set.preimage_image_eq S T.toHomeomorph.injective]
    have hs : μ.map T = mixedVolumeFrameFactor μ ν T • ν :=
      Measure.isAddLeftInvariant_eq_smul _ _
    have he := congrArg ENNReal.toReal hm.symm
    rw [hs, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul] at he
    simpa only [ENNReal.coe_toReal, measureReal_def] using he

theorem volumePolynomial_eq_frameFactor_mul {n : ℕ}
    (T : E ≃L[ℝ] F) (K : Fin n → ConvexBody E) :
    volumePolynomial μ K = MvPolynomial.C (mixedVolumeFrameFactor μ ν T : ℝ) *
      volumePolynomial ν (fun i => mapBody T.toContinuousLinearMap (K i)) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [map_mul, MvPolynomial.eval_C, volumePolynomial_eval ν _ t ht]
    have hsum : (∑ i, t i • mapBody T.toContinuousLinearMap (K i)) =
        mapBody T.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody T.toContinuousLinearMap (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul T.toContinuousLinearMap (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom T.toContinuousLinearMap) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    exact (measureReal_eq_frameFactor_mul_image μ ν T _).symm

theorem mixedVolume_eq_frameFactor_mul {n : ℕ}
    (T : E ≃L[ℝ] F) (K : Fin n → ConvexBody E) :
    mixedVolume μ K = (mixedVolumeFrameFactor μ ν T : ℝ) *
      mixedVolume ν (fun i => mapBody T.toContinuousLinearMap (K i)) := by
  first
  | rw [mixedVolume, volumePolynomial_eq_frameFactor_mul μ ν T K, MvPolynomial.coeff_C_mul,
      mixedVolume]
    ring

theorem volumePolynomial_map_linear {n : ℕ} (L : E →L[ℝ] E) (K : Fin n → ConvexBody E) :
    volumePolynomial μ (fun i => mapBody L (K i)) =
      MvPolynomial.C |LinearMap.det L.toLinearMap| * volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [map_mul, MvPolynomial.eval_C, volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • mapBody L (K i)) = mapBody L (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody L (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul L (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom L) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    have h := congrArg ENNReal.toReal (Measure.addHaar_image_linearMap μ L.toLinearMap
      ((∑ i, t i • K i : ConvexBody E) : Set E))
    simpa only [coe_mapBody, ContinuousLinearMap.coe_coe, measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h.symm

/-- Full determinant transport, including singular linear maps. -/
theorem mixedVolume_map_linear {n : ℕ} (L : E →L[ℝ] E) (K : Fin n → ConvexBody E) :
    mixedVolume μ (fun i => mapBody L (K i)) =
      |LinearMap.det L.toLinearMap| * mixedVolume μ K := by
  first
  | rw [mixedVolume, volumePolynomial_map_linear μ L K, MvPolynomial.coeff_C_mul, mixedVolume]
    ring

end VolumePolynomials
