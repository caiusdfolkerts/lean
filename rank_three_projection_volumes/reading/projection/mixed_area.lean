module

public import Projection.SupportDensity
public import VolumePolynomials.ProjectionMonotonicity

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped NNReal Pointwise

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance normalSphereMeasurableSpace : MeasurableSpace (NormalSphere E) :=
  borel (NormalSphere E)

instance normalSphereBorelSpace : BorelSpace (NormalSphere E) := ⟨rfl⟩

variable [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The first mixed-volume slot, with the usual area-measure normalization. -/
def mixedFirstLinear {d : ℕ} (K : Fin d → ConvexBody E) : ConvexBody E →ₗ[ℝ≥0] ℝ :=
  (d + 1 : ℝ≥0) •
    (mixedVolumeMultilinear μ (d + 1)).toLinearMap (Fin.cons 0 K) 0

@[simp] theorem mixedFirstLinear_apply {d : ℕ} (K : Fin d → ConvexBody E) (A : ConvexBody E) :
    mixedFirstLinear μ K A = (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K) := by
  have ht : Function.update
      (Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) 0 A =
      (Fin.cons A K : Fin (d + 1) → ConvexBody E) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  simp only [mixedFirstLinear, LinearMap.smul_apply, MultilinearMap.toLinearMap_apply,
    mixedVolumeMultilinear_apply, ht]
  rfl

theorem mixedFirstLinear_monotone {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (A B : ConvexBody E)
    (hAB : supportLinear A ≤ supportLinear B) :
    mixedFirstLinear μ K A ≤ mixedFirstLinear μ K B := by
  rw [mixedFirstLinear_apply, mixedFirstLinear_apply]
  exact mul_le_mul_of_nonneg_left
    (mixedVolume_mono_first_all μ K hdim A B (le_of_supportContinuous_le hAB))
    (by positivity)

/-- Existence of the actual mixed area measure, proved from monotonicity,
support functions, Hahn–Banach, and Riesz representation. -/
theorem exists_mixedAreaMeasure {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) :
    ∃ ν : Measure (NormalSphere E), IsFiniteMeasure ν ∧
      ∀ A : ConvexBody E,
        (∫ u, supportContinuous A u ∂ν) =
          (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K) := by
  obtain ⟨ν, hν, hrep⟩ := PositiveRepresentation.exists_representing_measure
    (supportLinear (E := E)) (mixedFirstLinear μ K)
    (mixedFirstLinear_monotone μ K hdim) unitBall supportContinuous_unitBall
  refine ⟨ν, hν, ?_⟩
  intro A
  exact (hrep A).trans (mixedFirstLinear_apply μ K A)

/-- The unique positive mixed area measure of the background tuple. -/
def mixedAreaMeasure {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) : Measure (NormalSphere E) :=
  (exists_mixedAreaMeasure μ K hdim).choose

instance mixedAreaMeasure_finite {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) : IsFiniteMeasure (mixedAreaMeasure μ K hdim) :=
  (exists_mixedAreaMeasure μ K hdim).choose_spec.1

theorem mixedAreaMeasure_integral {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (A : ConvexBody E) :
    (∫ u, supportContinuous A u ∂mixedAreaMeasure μ K hdim) =
      (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K) :=
  (exists_mixedAreaMeasure μ K hdim).choose_spec.2 A

theorem mixedAreaMeasure_unique {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (ν : Measure (NormalSphere E)) [IsFiniteMeasure ν]
    (hν : ∀ A : ConvexBody E, (∫ u, supportContinuous A u ∂ν) =
      (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K)) :
    ν = mixedAreaMeasure μ K hdim := by
  apply measure_eq_of_support_integrals
  intro A
  exact (hν A).trans (mixedAreaMeasure_integral μ K hdim A).symm

theorem mixedVolume_point_first {d : ℕ} (K : Fin d → ConvexBody E) (v : E) :
    mixedVolume μ (Fin.cons (pointBody v) K) = 0 := by
  have ht : (fun i : Fin (d + 1) => translateBody
      ((Fin.cons v (fun _ : Fin d => 0) : Fin (d + 1) → E) i)
      ((Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) i)) =
      (Fin.cons (pointBody v) K : Fin (d + 1) → ConvexBody E) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      apply ConvexBody.ext
      ext x
      simp [coe_translateBody, ConvexBody.coe_zero, pointBody, Set.mem_vadd_set,
        vadd_eq_add, eq_comm]
    · simp only [Fin.cons_succ, translateBody_zero]
  have htrans := mixedVolume_translate μ (Fin.cons (0 : ConvexBody E) K)
    (Fin.cons v (fun _ : Fin d => 0))
  rw [ht] at htrans
  have hz := mixedVolume_zero_arg μ (Fin.cons (0 : ConvexBody E) K) 0
  have hu : Function.update
      (Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) 0 0 =
      (Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [hu] at hz
  exact htrans.trans hz

/-- Every linear first moment of the mixed area measure vanishes. -/
theorem mixedAreaMeasure_centered {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (v : E) :
    (∫ u, u.val v ∂mixedAreaMeasure μ K hdim) = 0 := by
  have h := mixedAreaMeasure_integral μ K hdim (pointBody v)
  simpa only [supportContinuous_point, mixedVolume_point_first, mul_zero] using h

end RankThreeProjection
