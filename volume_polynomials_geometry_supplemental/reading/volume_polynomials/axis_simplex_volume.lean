module

public import VolumePolynomials.AxisSimplexSections
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Actual volume recurrence for ordered axis simplices

The coordinate splitting is the measure-preserving equivalence already
proved for product Lebesgue measure. Fubini and the exact section identities
give the recurrence in Appendix A, including zero Minkowski coefficients.
The axis lengths are strictly positive here; the final polynomial identity
extends to nonnegative lengths by Hausdorff continuity.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

theorem firstSection_measurable {n : ℕ} (K : Body (n + 1)) (z : ℝ) :
    MeasurableSet (firstSection K z) := by
  first
  | have hc : Continuous (fun x : Space n => (Fin.cons z x : Space (n + 1))) := by
      first
      | apply continuous_pi
        intro i
        cases i using Fin.cases with
        | zero => exact continuous_const
        | succ i => exact continuous_apply i
    exact K.isCompact.measurableSet.preimage hc.measurable

/-- Both the integrability assertion and the equality concern the actual
Lebesgue volumes of the coordinate sections. -/
theorem firstSection_fubini {n : ℕ} (K : Body (n + 1)) :
    Integrable (fun z : ℝ => volume.real (firstSection K z)) ∧
      bodyVolume K = ∫ z : ℝ, volume.real (firstSection K z) := by
  first
  | let e : ℝ × Space n ≃ᵐ Space (n + 1) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have he : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
    have he_apply (z : ℝ) (x : Space n) : e (z, x) = (Fin.cons z x : Space (n + 1)) := by
      first
      | change Fin.insertNth 0 z x = (Fin.cons z x : Space (n + 1))
        exact Fin.insertNth_zero' z x
    let f : Space (n + 1) → ℝ := (K : Set (Space (n + 1))).indicator (fun _ => 1)
    have hf : Integrable f :=
      (integrableOn_const K.isCompact.measure_ne_top).integrable_indicator
        K.isCompact.measurableSet
    have hfe : Integrable (f ∘ e) ((volume : Measure ℝ).prod (volume : Measure (Space n))) := by
      first
      | simpa only [← Measure.volume_eq_prod] using he.integrable_comp_of_integrable hf
    have hinner (z : ℝ) : (∫ x : Space n, f (e (z, x))) =
        volume.real (firstSection K z) := by
      first
      | simp only [he_apply]
        change (∫ x : Space n, (firstSection K z).indicator (fun _ => (1 : ℝ)) x) = _
        rw [integral_indicator (firstSection_measurable K z), setIntegral_const]
        simp only [smul_eq_mul, mul_one]
    have htotal : (∫ x : Space (n + 1), f x) = bodyVolume K := by
      first
      | rw [integral_indicator K.isCompact.measurableSet, setIntegral_const]
        simp only [smul_eq_mul, mul_one, bodyVolume]
    constructor
    · simpa only [Function.comp_apply, hinner] using hfe.integral_prod_left
    · have hp := integral_prod (f ∘ e) hfe
      rw [← Measure.volume_eq_prod] at hp
      simpa only [Function.comp_apply, he.integral_comp' f, htotal, hinner] using hp

theorem integral_upper_section_power (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (t s : ℝ) :
    (∫ z in t..t + s * lam, (s - (z - t) / lam) ^ n) =
      lam * s ^ (n + 1) / (n + 1) := by
  first
  | have hshift := intervalIntegral.integral_comp_sub_right
      (fun w : ℝ => (s - w / lam) ^ n) t (a := t) (b := t + s * lam)
    simp only [sub_self, add_sub_cancel_left] at hshift
    rw [hshift, intervalIntegral.integral_comp_sub_div (fun w : ℝ => w ^ n) hlam.ne' s]
    have hcancel : s * lam / lam = s := mul_div_cancel_right₀ s hlam.ne'
    rw [hcancel, zero_div, sub_zero, sub_self, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, smul_eq_mul]
    ring

/-- The recurrence obtained from the actual sections, with the shortest
axis listed first. -/
theorem volume_sum_recurrence {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body (n + 1) + s • axisBody lam) =
      (∫ u in 0..t, bodyVolume (u • body n + s • axisBody (Fin.tail lam))) +
        lam 0 * s ^ (n + 1) / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
  first
  | let K : Body (n + 1) := t • body (n + 1) + s • axisBody lam
    let f : ℝ → ℝ := fun z => volume.real (firstSection K z)
    have hf : Integrable f := (firstSection_fubini K).1
    have htop : t ≤ t + s * lam 0 := le_add_of_nonneg_right (mul_nonneg hs (hlam 0).le)
    have hsupport : ∀ z, z ∉ Icc (0 : ℝ) (t + s * lam 0) → f z = 0 := by
      first
      | intro z hz
        dsimp only [f, K]
        rw [firstSection_sum_empty hlam ht hs hz, measureReal_empty]
    have hwhole : bodyVolume K = ∫ z in 0..t + s * lam 0, f z := by
      first
      | rw [(firstSection_fubini K).2]
        change (∫ z, f z) = _
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,
          integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (ht.trans htop)]
    have hlower : (∫ z in 0..t, f z) =
        ∫ u in 0..t, bodyVolume (u • body n + s • axisBody (Fin.tail lam)) := by
      first
      | calc
          (∫ z in 0..t, f z) = ∫ z in 0..t,
              bodyVolume ((t - z) • body n + s • axisBody (Fin.tail lam)) := by
            apply intervalIntegral.integral_congr_Ioo_of_le ht
            intro z hz
            dsimp only [f, K]
            rw [firstSection_sum_lower hlam hmin ht hs hz.1.le hz.2.le]
            rfl
          _ = _ := by
            simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left
              (fun u : ℝ => bodyVolume (u • body n + s • axisBody (Fin.tail lam)))
              t (a := 0) (b := t)
    have hupper : (∫ z in t..t + s * lam 0, f z) =
        lam 0 * s ^ (n + 1) / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
      first
      | calc
          (∫ z in t..t + s * lam 0, f z) =
              ∫ z in t..t + s * lam 0,
                (s - (z - t) / lam 0) ^ n * bodyVolume (axisBody (Fin.tail lam)) := by
            apply intervalIntegral.integral_congr_Ioo_of_le htop
            intro z hz
            dsimp only [f, K]
            rw [firstSection_sum_upper hlam hmin ht hs hz.1.le hz.2.le]
            change bodyVolume ((s - (z - t) / lam 0) • axisBody (Fin.tail lam)) = _
            apply bodyVolume_smul
            apply sub_nonneg.mpr
            apply (div_le_iff₀ (hlam 0)).mpr
            linarith [hz.2]
          _ = _ := by rw [intervalIntegral.integral_mul_const, integral_upper_section_power n (hlam 0)]
    change bodyVolume K = _
    rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (a := 0) (b := t))
      (hf.intervalIntegrable (a := t) (b := t + s * lam 0)), hlower, hupper]

theorem simplex_volume_zero : bodyVolume (body 0) = 1 := by
  first
  | have heq : simplex 0 = Icc (0 : Space 0) (fun _ => 1) := by
      first
      | ext x
        simp [simplex, Pi.le_def]
    change volume.real (simplex 0) = 1
    rw [heq]
    simp [measureReal_def, Real.volume_Icc_pi]

theorem simplex_volume (n : ℕ) : bodyVolume (body n) = 1 / (n.factorial : ℝ) := by
  first
  | induction n with
    | zero => simpa only [Nat.factorial_zero, Nat.cast_one, div_one] using simplex_volume_zero
    | succ n ih =>
        have hrec := volume_sum_recurrence (fun _ : Fin (n + 1) => zero_lt_one)
          (fun _ => le_rfl) (t := 1) (s := 0) zero_le_one le_rfl
        simp only [one_smul, body_zero_smul, add_zero,
          zero_pow (Nat.succ_ne_zero n), mul_zero, zero_div, zero_mul] at hrec
        rw [hrec]
        have hfn : (∫ u in (0 : ℝ)..1, bodyVolume (u • body n)) =
            ∫ u in (0 : ℝ)..1, u ^ n * bodyVolume (body n) := by
          first
          | apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
            intro u hu
            exact bodyVolume_smul _ hu.1.le
        rw [hfn, intervalIntegral.integral_mul_const, integral_pow, ih,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, one_div, ← mul_inv]

theorem det_diagonalMap {n : ℕ} (lam : Fin n → ℝ) :
    LinearMap.det (diagonalMap lam).toLinearMap = ∏ i, lam i := by
  first
  | rw [← LinearMap.det_toMatrix']
    have hm : LinearMap.toMatrix' (diagonalMap lam).toLinearMap = Matrix.diagonal lam := by
      first
      | ext i j
        simp [LinearMap.toMatrix'_apply, diagonalMap, Matrix.diagonal_apply, Pi.single_apply]
    rw [hm, Matrix.det_diagonal]

theorem axisBody_volume {n : ℕ} (lam : Fin n → ℝ) :
    bodyVolume (axisBody lam) = |∏ i, lam i| / (n.factorial : ℝ) := by
  first
  | rw [axisBody, bodyVolume_map, det_diagonalMap, simplex_volume]
    ring

end VolumePolynomials.AxisSimplex
