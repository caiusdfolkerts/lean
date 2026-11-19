module

public import VolumePolynomials.PlanarFiberAverage
public import VolumePolynomials.HigherLiftCoordinates
public import VolumePolynomials.FiberVolume
public import Mathlib.Tactic.LinearCombination

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # Extracting the seven coefficients after actual fiber averaging

The input is the literal Fubini identity furnished by `CoordinateFiberData`.
Every fiber integral is justified. The mean body preserves widths and the
actual triple mixed-volume functional, while Berwald supplies its area
bound. Exact polynomial interpolation then recovers all six repeated
coefficients and the triple coefficient, retaining the common positive
Jacobian times projection-volume factor.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarCorner PlanarEdges ConvexFibers

def horizontalWidthFunctional : MinkowskiFunctional Plane :=
  MinkowskiFunctional.width (ContinuousLinearMap.fst ℝ ℝ ℝ)

def verticalWidthFunctional : MinkowskiFunctional Plane :=
  MinkowskiFunctional.width (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem horizontalWidthFunctional_apply (A : ConvexBody Plane) :
    horizontalWidthFunctional A = width A := by
  first
  | exact (image_length_eq_support A (ContinuousLinearMap.fst ℝ ℝ ℝ)).symm

@[simp] theorem verticalWidthFunctional_apply (A : ConvexBody Plane) :
    verticalWidthFunctional A = height A := by
  first
  | exact (image_length_eq_support A (ContinuousLinearMap.snd ℝ ℝ ℝ)).symm

def sevenTermValue (a : Fin 7 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  t 0 ^ 2 * t 1 * a 0 + t 0 ^ 2 * t 2 * a 1 +
  t 0 * t 1 ^ 2 * a 2 + t 1 ^ 2 * t 2 * a 3 +
  t 0 * t 2 ^ 2 * a 4 + t 1 * t 2 ^ 2 * a 5 + t 0 * t 1 * t 2 * a 6

/-- Exact linear independence of all seven monomials, for arbitrary real
coefficients. The rational interpolation identities are proved in the
kernel; this is a polynomial identity theorem, not a numerical test of a
geometric statement. -/
theorem sevenTermValue_injective {a b : Fin 7 → ℝ}
    (h : ∀ t : Fin 3 → ℝ, (∀ i, 0 < t i) → sevenTermValue a t = sevenTermValue b t) :
    a = b := by
  first
  | have h111 := h ![1, 1, 1] (by intro i; fin_cases i <;> norm_num)
    have h112 := h ![1, 1, 2] (by intro i; fin_cases i <;> norm_num)
    have h113 := h ![1, 1, 3] (by intro i; fin_cases i <;> norm_num)
    have h121 := h ![1, 2, 1] (by intro i; fin_cases i <;> norm_num)
    have h122 := h ![1, 2, 2] (by intro i; fin_cases i <;> norm_num)
    have h123 := h ![1, 2, 3] (by intro i; fin_cases i <;> norm_num)
    have h131 := h ![1, 3, 1] (by intro i; fin_cases i <;> norm_num)
    norm_num [sevenTermValue] at h111 h112 h113 h121 h122 h123 h131
    funext i
    fin_cases i
    · change a 0 = b 0
      linear_combination 6 * h111 - 6 * h112 + 2 * h113 -
        (3 / 2) * h121 + (3 / 2) * h122 - (1 / 2) * h123
    · change a 1 = b 1
      linear_combination 2 * h111 + 2 * h112 - h113 -
        (5 / 2) * h121 - h122 + (1 / 2) * h123 + h131
    · change a 2 = b 2
      linear_combination -3 * h111 + 3 * h112 - h113 +
        (3 / 2) * h121 - (3 / 2) * h122 + (1 / 2) * h123
    · change a 3 = b 3
      linear_combination (7 / 2) * h111 - 3 * h112 + h113 -
        (5 / 2) * h121 + (3 / 2) * h122 - (1 / 2) * h123 + (1 / 2) * h131
    · change a 4 = b 4
      linear_combination h111 - 2 * h112 + h113 - (1 / 2) * h121 + h122 - (1 / 2) * h123
    · change a 5 = b 5
      linear_combination -(1 / 2) * h111 + h112 - (1 / 2) * h113 +
        (1 / 2) * h121 - h122 + (1 / 2) * h123
    · change a 6 = b 6
      linear_combination -8 * h111 + 5 * h112 - (3 / 2) * h113 +
        5 * h121 - (1 / 2) * h122 - (3 / 2) * h131

def averagedCoefficients (A B C : ConvexBody Plane) (τ : ℝ) : Fin 7 → ℝ :=
  ![τ * height B, τ * height C,
    volume.real (B : Set Plane) * width A, volume.real (B : Set Plane) * width C,
    volume.real (C : Set Plane) * height A, volume.real (C : Set Plane) * width B,
    6 * triple A B C]

theorem fiber_area_integrable {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    IntegrableOn (fun y => volume.real (fiberBody F y : Set Plane)) (projection F) := by
  first
  | apply (FiberVolume.integrable_fiber_realVolume F).integrableOn.congr_fun
      (hs := (projection_compact F).measurableSet)
    intro y hy
    change volume.real (fiberSet F y) = volume.real (fiberBody F y : Set Plane)
    rw [coe_fiberBody F hy]

theorem mean_fiber_area_nonnegative {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    0 ≤ uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)) := by
  first
  | unfold uniformAverage
    exact div_nonneg (integral_nonneg (fun _ => measureReal_nonneg)) measureReal_nonneg

/-- The complete integrated cubic, with its actual mean area. Neither
fiber measurability nor integrability is an extra hypothesis. -/
theorem averaged_coordinate_volume {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) (A B C : ConvexBody Plane)
    (hvol : 0 < volume.real (projection F))
    (hA : ∀ φ : MinkowskiFunctional Plane,
      φ A = uniformAverage (projection F) (fun y => φ (fiberBody F y)))
    (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∫ y in projection F, coordinateVolume (fiberBody F y) B C t) =
      volume.real (projection F) * sevenTermValue
        (averagedCoefficients A B C
          (uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)))) t := by
  first
  | let τ := uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane))
    let a₂ := t 0 ^ 2 * t 1 * height B + t 0 ^ 2 * t 2 * height C
    let aw := t 0 * t 1 ^ 2 * volume.real (B : Set Plane)
    let ah := t 0 * t 2 ^ 2 * volume.real (C : Set Plane)
    let a₀ := t 1 ^ 2 * t 2 * (volume.real (B : Set Plane) * width C) +
      t 1 * t 2 ^ 2 * (volume.real (C : Set Plane) * width B)
    let a₃ := t 0 * t 1 * t 2
    have heval (y : VolumePolynomials.Space k) :
        coordinateVolume (fiberBody F y) B C t =
          a₂ * volume.real (fiberBody F y : Set Plane) +
            aw * width (fiberBody F y) + ah * height (fiberBody F y) +
            a₀ + a₃ * (6 * triple (fiberBody F y) B C) := by
      first
      | rw [coordinate_volume_formula _ _ _ t ht]
        dsimp only [a₂, aw, ah, a₀, a₃]
        ring
    have ha := fiber_area_integrable F
    have hw : IntegrableOn (fun y => width (fiberBody F y)) (projection F) := by
      first
      | simpa only [horizontalWidthFunctional_apply] using
          fiber_functional_integrable F horizontalWidthFunctional
    have hh : IntegrableOn (fun y => height (fiberBody F y)) (projection F) := by
      first
      | simpa only [verticalWidthFunctional_apply] using
          fiber_functional_integrable F verticalWidthFunctional
    have hv : IntegrableOn (fun y => 6 * triple (fiberBody F y) B C) (projection F) :=
      fiber_functional_integrable F (tripleFunctional B C)
    have hc : IntegrableOn (fun _ : VolumePolynomials.Space k => a₀) (projection F) :=
      integrableOn_const (projection_compact F).measure_ne_top
    have hmean (φ : MinkowskiFunctional Plane) :
        (∫ y in projection F, φ (fiberBody F y)) = volume.real (projection F) * φ A := by
      first
      | have h := hA φ
        rw [uniformAverage, eq_div_iff hvol.ne'] at h
        exact h.symm.trans (mul_comm _ _)
    have harea : (∫ y in projection F, volume.real (fiberBody F y : Set Plane)) =
        volume.real (projection F) * τ := by
      first
      | dsimp only [τ, uniformAverage]
        field_simp [hvol.ne']
    have hwidth : (∫ y in projection F, width (fiberBody F y)) =
        volume.real (projection F) * width A := by
      first
      | simpa only [horizontalWidthFunctional_apply] using hmean horizontalWidthFunctional
    have hheight : (∫ y in projection F, height (fiberBody F y)) =
        volume.real (projection F) * height A := by
      first
      | simpa only [verticalWidthFunctional_apply] using hmean verticalWidthFunctional
    have htriple : (∫ y in projection F, 6 * triple (fiberBody F y) B C) =
        volume.real (projection F) * (6 * triple A B C) := hmean (tripleFunctional B C)
    calc
      _ = ∫ y in projection F,
          a₂ * volume.real (fiberBody F y : Set Plane) +
            aw * width (fiberBody F y) + ah * height (fiberBody F y) +
            a₀ + a₃ * (6 * triple (fiberBody F y) B C) := by
        first
        | apply setIntegral_congr_fun (projection_compact F).measurableSet
          exact fun y _ => heval y
      _ = a₂ * (∫ y in projection F, volume.real (fiberBody F y : Set Plane)) +
          aw * (∫ y in projection F, width (fiberBody F y)) +
          ah * (∫ y in projection F, height (fiberBody F y)) +
          volume.real (projection F) * a₀ +
          a₃ * (∫ y in projection F, 6 * triple (fiberBody F y) B C) := by
        first
        | have h12 : IntegrableOn (fun y => a₂ * volume.real (fiberBody F y : Set Plane) +
              aw * width (fiberBody F y)) (projection F) := by
            exact Integrable.fun_add (ha.const_mul a₂) (hw.const_mul aw)
          have h123 : IntegrableOn (fun y => a₂ * volume.real (fiberBody F y : Set Plane) +
              aw * width (fiberBody F y) + ah * height (fiberBody F y)) (projection F) := by
            exact Integrable.fun_add h12 (hh.const_mul ah)
          have h1234 : IntegrableOn (fun y => a₂ * volume.real (fiberBody F y : Set Plane) +
              aw * width (fiberBody F y) + ah * height (fiberBody F y) + a₀) (projection F) := by
            exact Integrable.fun_add h123 hc
          rw [integral_add h1234 (hv.const_mul a₃), integral_add h123 hc,
            integral_add h12 (hh.const_mul ah), integral_add (ha.const_mul a₂) (hw.const_mul aw),
            integral_const_mul, integral_const_mul, integral_const_mul,
            integral_const_mul, setIntegral_const]
          rfl
      _ = _ := by
        first
        | rw [harea, hwidth, hheight, htriple]
          dsimp only [a₂, aw, ah, a₀, a₃, τ, sevenTermValue, averagedCoefficients, Matrix.cons_val]
          ring

end VolumePolynomials.PlanarInteraction

namespace VolumePolynomials.HigherLift

open PlanarExtrusion PlanarInteraction ConvexFibers

theorem CoordinateFiberData.exists_repeatedCoefficientData {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) :
    ∃ R : RepeatedCoefficientData α s z (correction k),
      (∀ φ : MinkowskiFunctional Plane,
        φ R.A = uniformAverage (projection D.F) (fun y => φ (fiberBody D.F y))) ∧
      (k = 0 → volume.real (R.A : Set Plane) = R.τ / correction k) := by
  first
  | obtain ⟨A, hA, harea, hzero⟩ := planar_average_coordinates k D.F D.projection_pos
    let τ := uniformAverage (projection D.F) (fun y => volume.real (fiberBody D.F y : Set Plane))
    let M := D.J * volume.real (projection D.F)
    have heq : (fun j : Fin 7 => M * averagedCoefficients A D.B D.C τ j) =
        ![3 * (correction k * α), 3 * (correction k * α), 3, 3, 3 * s, 3, 6 * z] := by
      first
      | apply sevenTermValue_injective
        intro t ht
        have h := D.integral_identity t ht
        rw [averaged_coordinate_volume D.F A D.B D.C D.projection_pos hA t
          (fun i => (ht i).le)] at h
        calc
          _ = D.J * (volume.real (projection D.F) *
              sevenTermValue (averagedCoefficients A D.B D.C τ) t) := by
            first
            | dsimp only [sevenTermValue, M]
              ring
          _ = CubicSlice.value (correction k * α) s z t := h
          _ = _ := by
            first
            | dsimp only [CubicSlice.value, sevenTermValue, Matrix.cons_val]
              ring
    have hcoeff (j : Fin 7) := congrFun heq j
    let R : RepeatedCoefficientData α s z (correction k) := {
      A := A
      B := D.B
      C := D.C
      M := M
      τ := τ
      M_pos := mul_pos D.J_pos D.projection_pos
      τ_nonneg := mean_fiber_area_nonnegative D.F
      AAB := by simpa [averagedCoefficients, mul_assoc] using hcoeff 0
      AAC := by simpa [averagedCoefficients, mul_assoc] using hcoeff 1
      BBA := by simpa [averagedCoefficients, mul_assoc] using hcoeff 2
      BBC := by simpa [averagedCoefficients, mul_assoc] using hcoeff 3
      CCA := by simpa [averagedCoefficients, mul_assoc] using hcoeff 4
      CCB := by simpa [averagedCoefficients, mul_assoc] using hcoeff 5
      area_lower := by simpa only [correction, berwaldConstant] using harea
      ABC := by simpa only [averagedCoefficients, Matrix.cons_val] using hcoeff 6 }
    refine ⟨R, hA, ?_⟩
    intro hk
    change volume.real (A : Set Plane) = τ / correction k
    rw [hzero hk]
    subst k
    norm_num [correction, τ]

def CoordinateFiberData.repeatedCoefficientData {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) : RepeatedCoefficientData α s z (correction k) :=
  Classical.choose D.exists_repeatedCoefficientData

theorem CoordinateFiberData.repeatedCoefficientData_average {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (φ : MinkowskiFunctional Plane) :
    φ D.repeatedCoefficientData.A =
      uniformAverage (projection D.F) (fun y => φ (fiberBody D.F y)) :=
  (Classical.choose_spec D.exists_repeatedCoefficientData).1 φ

theorem CoordinateFiberData.repeatedCoefficientData_area_zero {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (hk : k = 0) :
    volume.real (D.repeatedCoefficientData.A : Set Plane) =
      D.repeatedCoefficientData.τ / correction k :=
  (Classical.choose_spec D.exists_repeatedCoefficientData).2 hk

def CoordinateFiberData.normalize {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (hα : 0 < α) : NormalizedPlanarData α s z :=
  D.repeatedCoefficientData.normalize hα (by unfold correction; positivity)

theorem CoordinateFiberData.normalize_area_zero {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (hα : 0 < α) (hk : k = 0) :
    volume.real ((D.normalize hα).A : Set Plane) = α * (D.normalize hα).T :=
  D.repeatedCoefficientData.normalize_area_eq hα (by unfold correction; positivity)
    (D.repeatedCoefficientData_area_zero hk)

end VolumePolynomials.HigherLift
