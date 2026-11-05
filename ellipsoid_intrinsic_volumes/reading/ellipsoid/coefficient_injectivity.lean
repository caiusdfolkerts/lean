module

public import Ellipsoid.CoefficientDerivative
public import Ellipsoid.RectangleUnivalence
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

noncomputable section

open Set Matrix Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def internalCoefficientInclusion (m : ℕ) : (Fin m → ℝ) →L[ℝ] Coefficients (m + 1) :=
  ContinuousLinearMap.pi fun j =>
    if h0 : j.val = 0 then 0 else if hn : j.val = m + 1 then 0 else
      ContinuousLinearMap.proj ⟨j.val - 1, by omega⟩

theorem fixedEndpoints_eq_affine (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    fixedEndpoints m e0 en x = fixedEndpoints m e0 en 0 + internalCoefficientInclusion m x := by
  funext j
  simp only [fixedEndpoints, internalCoefficientInclusion,
    ContinuousLinearMap.pi_apply, Pi.add_apply]
  split_ifs <;> simp

theorem internalCoefficientInclusion_single (m : ℕ) (q : Fin m) :
    internalCoefficientInclusion m (Pi.single q 1) =
      Pi.single (⟨q.val + 1, by omega⟩ : Fin (m + 2)) 1 := by
  let q' : Fin (m + 1 + 1) := ⟨q.val + 1, by omega⟩
  change _ = (Pi.single q' 1 : Coefficients (m + 1))
  funext j
  simp only [internalCoefficientInclusion, ContinuousLinearMap.pi_apply]
  by_cases h0 : j.val = 0
  · have hne : j ≠ q' := by
      intro h
      have hh : j.val = q.val + 1 := congrArg Fin.val h
      omega
    simp only [dif_pos h0, ContinuousLinearMap.zero_apply, Pi.single_eq_of_ne hne]
  by_cases hn : j.val = m + 1
  · have hne : j ≠ q' := by
      intro h
      have hh : j.val = q.val + 1 := congrArg Fin.val h
      have hq := q.isLt
      omega
    simp only [dif_neg h0, dif_pos hn, ContinuousLinearMap.zero_apply,
      Pi.single_eq_of_ne hne]
  simp only [dif_neg h0, dif_neg hn, ContinuousLinearMap.proj_apply]
  let j' : Fin m := ⟨j.val - 1, by have hj := j.isLt; omega⟩
  change (Pi.single q 1 : Fin m → ℝ) j' =
    (Pi.single q' 1 : Coefficients (m + 1)) j
  by_cases hj : j = q'
  · have hp : j' = q := by
      apply Fin.ext
      have hh : j.val = q.val + 1 := congrArg Fin.val hj
      change j.val - 1 = q.val
      omega
    rw [hp, hj]
    simp
  · have hp : j' ≠ q := by
      intro h
      have hh : j.val - 1 = q.val := congrArg Fin.val h
      apply hj
      apply Fin.ext
      change j.val = q.val + 1
      omega
    simp only [Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hj]

theorem hasFDerivAt_fixedEndpoints (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    HasFDerivAt (fixedEndpoints m e0 en) (internalCoefficientInclusion m) x := by
  have h : HasFDerivAt
      (fun y => fixedEndpoints m e0 en 0 + internalCoefficientInclusion m y)
      (internalCoefficientInclusion m) x :=
    ((internalCoefficientInclusion m).hasFDerivAt (x := x)).const_add
      (fixedEndpoints m e0 en 0)
  simpa only [← fixedEndpoints_eq_affine] using h

@[fun_prop] theorem continuous_fixedEndpoints (m : ℕ) (e0 en : ℝ) :
    Continuous (fixedEndpoints m e0 en) := by
  have h : Continuous
      (fun y => fixedEndpoints m e0 en 0 + internalCoefficientInclusion m y) :=
    continuous_const.add (internalCoefficientInclusion m).continuous
  simpa only [← fixedEndpoints_eq_affine] using h

def fixedCoefficientJacobian (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := coefficientJacobian (fixedEndpoints m e0 en x)

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_coefficientMap {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    HasFDerivAt (coefficientMap m e0 en)
      (matrixDerivative (fixedCoefficientJacobian m e0 en x)) x := by
  let e := fixedEndpoints m e0 en x
  have he : coefficientAdmissible e := fixedEndpoints_admissible h0 hn hx
  have hU := (isOpen_positiveCoefficientDomain (m + 1)).mem_nhds
    (admissible_mem_positiveCoefficientDomain he)
  let L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := ContinuousLinearMap.pi fun k =>
    (fderiv ℝ (fun z : Coefficients (m + 1) => coefficientTransform z (k.val + 1)) e).comp
      (internalCoefficientInclusion m)
  have hL : HasFDerivAt (coefficientMap m e0 en) L x := by
    apply hasFDerivAt_pi.mpr
    intro k
    have hf := ((contDiffOn_coefficientTransform (k := k.val + 1) (by omega) (by omega)).contDiffAt hU
      |>.differentiableAt (by simp)).hasFDerivAt
    exact hf.comp x (hasFDerivAt_fixedEndpoints m e0 en x)
  have heq : L = matrixDerivative (fixedCoefficientJacobian m e0 en x) := by
    apply ContinuousLinearMap.ext
    intro u
    have hu := pi_eq_sum_univ' u
    rw [hu]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    funext k
    have hleft : L (Pi.single q 1) k = coefficientJacobian e k q := by
      change (fderiv ℝ (fun z : Coefficients (m + 1) =>
        coefficientTransform z (k.val + 1)) e)
          (internalCoefficientInclusion m (Pi.single q 1)) = _
      rw [internalCoefficientInclusion_single]
      exact fderiv_coefficientTransform_single he k q
    have hright : matrixDerivative (fixedCoefficientJacobian m e0 en x)
        (Pi.single q 1) k = coefficientJacobian e k q := by
      change ((show Matrix (Fin m) (Fin m) ℝ from coefficientJacobian e) *ᵥ
        (Pi.single q 1 : Fin m → ℝ)) k = _
      exact congrFun (Matrix.mulVec_single_one
        (show Matrix (Fin m) (Fin m) ℝ from coefficientJacobian e) q) k
    exact hleft.trans hright.symm
  simpa only [heq] using hL

theorem fixedCoefficientJacobian_diagonallyStable {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    DiagonallyStable (fixedCoefficientJacobian m e0 en x) := by
  have he := fixedEndpoints_admissible h0 hn hx
  refine ⟨jacobianRescaling (fixedEndpoints m e0 en x), jacobianRescaling_pos he, ?_⟩
  rw [fixedCoefficientJacobian, coefficientJacobian_eq_balancedJacobian he]
  exact symmetricPart_balancedJacobian_posDef (by omega) he

/-- The injectivity clause of Theorem 2.1 on the entire closed orthant.
The endpoints are fixed positive numbers; internal coefficients can vanish. -/
theorem coefficientMap_injOn_nonnegative {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Set.InjOn (coefficientMap m e0 en) {x : Fin m → ℝ | 0 ≤ x} := by
  intro x hx y hy hxy
  let b : Fin m → ℝ := fun i => max (x i) (y i)
  have hx' : x ∈ Icc 0 b := ⟨hx, fun i => le_max_left _ _⟩
  have hy' : y ∈ Icc 0 b := ⟨hy, fun i => le_max_right _ _⟩
  exact injOn_rectangle_of_diagonal_stability
    (fun z hz => hasFDerivAt_coefficientMap h0 hn hz.1)
    (fun z hz => fixedCoefficientJacobian_diagonallyStable h0 hn hz.1) hx' hy' hxy

theorem coefficientMap_principalJacobianPositive {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    principalJacobianPositive (fixedCoefficientJacobian m e0 en x) :=
  coefficientJacobian_principal_minors_pos (by omega) (fixedEndpoints_admissible h0 hn hx)

end EllipsoidVerification
