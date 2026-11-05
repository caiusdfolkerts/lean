module

public import VolumePolynomials.BodyFrames
public import VolumePolynomials.ProjectionCoordinates
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.Holonomy

/-- The usual oriented determinant of three column vectors. -/
def determinant3 (v w z : ThreeSpace) : ℝ :=
  v 0 * (w 1 * z 2 - w 2 * z 1) -
    v 1 * (w 0 * z 2 - w 2 * z 0) +
    v 2 * (w 0 * z 1 - w 1 * z 0)

theorem frameColumnMap_toMatrix_apply (v : Fin 3 → ThreeSpace) (i j : Fin 3) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (frameColumnMap v).toLinearMap i j = v j i := by
  first
  | simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    exact congrFun (frameColumnMap_basis v j) i

theorem frameColumnMap_det_three (v w z : ThreeSpace) :
    LinearMap.det (frameColumnMap ![v, w, z]).toLinearMap = determinant3 v w z := by
  first
  | rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)), Matrix.det_fin_three]
    simp only [frameColumnMap_toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, determinant3]
    ring

/-- This determinant identity is for actual Lebesgue volume of actual segments. -/
theorem volume_three_origin_segments (v w z : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 w + segmentBody 0 z) =
      |determinant3 v w z| := by
  first
  | have h := bodyVolume_sum_origin_segments ![v, w, z]
    rw [frameColumnMap_det_three] at h
    simpa [Fin.sum_univ_three] using h

theorem volume_coordinate_test₁ (v : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 (Pi.single 1 1) +
      segmentBody 0 (Pi.single 2 1)) = |v 0| := by
  first
  | rw [volume_three_origin_segments]
    simp [determinant3, Pi.single_apply]

theorem volume_coordinate_test₂ (v : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 (Pi.single 0 1) +
      segmentBody 0 (Pi.single 2 1)) = |v 1| := by
  first
  | rw [volume_three_origin_segments]
    simp [determinant3, Pi.single_apply]

theorem volume_coordinate_test₃ (v : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 (Pi.single 0 1) +
      segmentBody 0 (Pi.single 1 1)) = |v 2| := by
  first
  | rw [volume_three_origin_segments]
    simp [determinant3, Pi.single_apply]

theorem determinant3_of_zero_coordinates (v w z : ThreeSpace)
    (hv : v 0 = 0) (hw : w 2 = 0) :
    determinant3 v w z =
      -(w 0) * v 1 * z 2 + w 0 * v 2 * z 1 - z 0 * v 2 * w 1 := by
  first
  | simp only [determinant3, hv, hw]
    ring

theorem calibrated_determinant : |determinant3 directionV directionW directionZ| =
    (4 / 3 : ℝ) := by
  first
  | norm_num [determinant3, directionV, directionW, directionZ]

private theorem sign_mul_self (s : ThreeSpace) (hs : ∀ i, |s i| = 1) (i : Fin 3) :
    s i * s i = 1 := by
  first
  | nlinarith [sq_abs (s i), hs i]

/-- Coordinate reflections as a genuine continuous linear equivalence. -/
def coordinateReflection (s : ThreeSpace) (hs : ∀ i, |s i| = 1) : ThreeSpace ≃L[ℝ] ThreeSpace where
  toFun x i := s i * x i
  invFun x i := s i * x i
  left_inv x := by
    first
    | funext i
      change s i * (s i * x i) = x i
      rw [← mul_assoc, sign_mul_self s hs, one_mul]
  right_inv x := by
    first
    | funext i
      change s i * (s i * x i) = x i
      rw [← mul_assoc, sign_mul_self s hs, one_mul]
  map_add' x y := by funext i; dsimp; ring
  map_smul' c x := by funext i; dsimp; ring
  continuous_toFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i))
  continuous_invFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i))

@[simp] theorem coordinateReflection_apply (s : ThreeSpace) (hs : ∀ i, |s i| = 1)
    (x : ThreeSpace) (i : Fin 3) : coordinateReflection s hs x i = s i * x i := rfl

theorem coordinateReflection_basis (s : ThreeSpace) (hs : ∀ i, |s i| = 1) (i : Fin 3) :
    coordinateReflection s hs (Pi.single i 1) = s i • (Pi.single i 1 : ThreeSpace) := by
  first
  | funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Pi.single_apply, hj, Ne.symm hj]

theorem coordinateReflection_abs_det (s : ThreeSpace) (hs : ∀ i, |s i| = 1) :
    |LinearMap.det (coordinateReflection s hs).toLinearMap| = 1 := by
  first
  | have hm : LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
        (coordinateReflection s hs).toLinearMap = Matrix.diagonal s := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [LinearMap.toMatrix_apply, Pi.basisFun_apply]
      · simp [LinearMap.toMatrix_apply, Pi.basisFun_apply, Matrix.diagonal_apply,
          Pi.single_apply, hij, Ne.symm hij]
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)), hm, Matrix.det_diagonal,
      Finset.abs_prod]
    simp [hs]

/-- The determinant calibration provides one common volume-preserving reflection
and independent orientations of the three oblique segment vectors. -/
theorem calibrate_vectors (v w z : ThreeSpace)
    (hv₀ : v 0 = 0) (hv₁ : |v 1| = 1) (hv₂ : |v 2| = 1)
    (hw₀ : |w 0| = 1) (hw₁ : |w 1| = 1) (hw₂ : w 2 = 0)
    (hz₀ : |z 0| = 1) (hz₁ : |z 1| = (2 / 3 : ℝ)) (hz₂ : |z 2| = 1)
    (hdet : |determinant3 v w z| = (4 / 3 : ℝ)) :
    ∃ g : ThreeSpace ≃L[ℝ] ThreeSpace,
      |LinearMap.det g.toLinearMap| = 1 ∧
      (∀ i : Fin 3, ∃ s : ℝ, |s| = 1 ∧
        g (Pi.single i 1) = s • (Pi.single i 1 : ThreeSpace)) ∧
      ∃ rv rw rz : ℝ, |rv| = 1 ∧ |rw| = 1 ∧ |rz| = 1 ∧
        g (rv • v) = directionV ∧ g (rw • w) = directionW ∧ g (rz • z) = directionZ := by
  first
  | rw [determinant3_of_zero_coordinates v w z hv₀ hw₂] at hdet
    obtain ⟨s₁, s₃, rv, rw, rz, hs₁, hs₃, hrv, hrw, hrz,
        hV₁, hV₂, hW₀, hW₁, hZ₀, hZ₁, hZ₂⟩ :=
      calibration_signs (v 1) (v 2) (w 0) (w 1) (z 0) (z 1) (z 2)
        hv₁ hv₂ hw₀ hw₁ hz₀ hz₁ hz₂ hdet
    let s : ThreeSpace := ![s₁, 1, s₃]
    have hs : ∀ i, |s i| = 1 := by
      intro i
      fin_cases i <;> simp [s, hs₁, hs₃]
    refine ⟨coordinateReflection s hs, coordinateReflection_abs_det s hs,
      fun i => ⟨s i, hs i, coordinateReflection_basis s hs i⟩,
      rv, rw, rz, hrv, hrw, hrz, ?_, ?_, ?_⟩
    · funext i
      change s i * (rv * v i) = directionV i
      fin_cases i
      · simp [s, directionV, hv₀]
      · simpa [s, directionV] using hV₁
      · simpa [s, directionV, mul_comm, mul_left_comm, mul_assoc] using hV₂
    · funext i
      change s i * (rw * w i) = directionW i
      fin_cases i
      · simpa [s, directionW, mul_comm, mul_left_comm, mul_assoc] using hW₀
      · simpa [s, directionW] using hW₁
      · simp [s, directionW, hw₂]
    · funext i
      change s i * (rz * z i) = directionZ i
      fin_cases i
      · simpa [s, directionZ, mul_comm, mul_left_comm, mul_assoc] using hZ₀
      · simpa [s, directionZ] using hZ₁
      · simpa [s, directionZ, mul_comm, mul_left_comm, mul_assoc] using hZ₂


end VolumePolynomials.Holonomy
