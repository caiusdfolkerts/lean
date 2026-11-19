module

public import ToricPower.BasicPolytope

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators

namespace ToricPower

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def adjugateRow (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) :
    Matrix ι (Fin n) ℤ := C * (basicMatrix C I).adjugate

def residualNumerator (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι)
    (h : ι → ℤ) (j : ι) : ℤ :=
  (basicMatrix C I).det *
    ((∑ k, adjugateRow C I j k * h (I k)) - (basicMatrix C I).det * h j)

def realResidual (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι)
    (h : ι → ℝ) (j : ι) : ℝ :=
  ((basicMatrix C I).det : ℝ) *
    ((∑ k, (adjugateRow C I j k : ℝ) * h (I k)) -
      ((basicMatrix C I).det : ℝ) * h j)

def residualBudget (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) (j : ι) : ℤ :=
  |(basicMatrix C I).det| *
    (|(basicMatrix C I).det| + ∑ k, |adjugateRow C I j k|)

/-- A finite integer expression depending only on the constraint matrix. -/
def affineThresholdCoefficient (C : Matrix ι (Fin n) ℤ) : ℤ :=
  1 + ∑ I : Fin n → ι, ∑ j, residualBudget C I j

lemma residualBudget_nonneg (C : Matrix ι (Fin n) ℤ)
    (I : Fin n → ι) (j : ι) : 0 ≤ residualBudget C I j := by
  unfold residualBudget
  positivity

lemma affineThresholdCoefficient_pos (C : Matrix ι (Fin n) ℤ) :
    0 < affineThresholdCoefficient C := by
  unfold affineThresholdCoefficient
  have hs : 0 ≤ ∑ I : Fin n → ι, ∑ j, residualBudget C I j :=
    Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun j _ =>
      residualBudget_nonneg C I j
  omega

lemma residualBudget_le_threshold (C : Matrix ι (Fin n) ℤ)
    (I : Fin n → ι) (j : ι) :
    residualBudget C I j ≤ affineThresholdCoefficient C := by
  have hj : residualBudget C I j ≤ ∑ k, residualBudget C I k :=
    Finset.single_le_sum (fun k _ => residualBudget_nonneg C I k)
      (Finset.mem_univ j)
  have hI : (∑ k, residualBudget C I k) ≤
      ∑ J : Fin n → ι, ∑ k, residualBudget C J k :=
    Finset.single_le_sum
      (fun J _ => Finset.sum_nonneg fun k _ => residualBudget_nonneg C J k)
      (Finset.mem_univ I)
  unfold affineThresholdCoefficient
  omega

lemma abs_residualNumerator_le (C : Matrix ι (Fin n) ℤ)
    (I : Fin n → ι) (e : ι → ℤ) (j : ι)
    (B : ℤ) (hB : 0 ≤ B) (he : ∀ k, |e k| ≤ B) :
    |residualNumerator C I e j| ≤ B * residualBudget C I j := by
  have hs : |∑ k, adjugateRow C I j k * e (I k)| ≤
      B * ∑ k, |adjugateRow C I j k| := by
    calc
      |∑ k, adjugateRow C I j k * e (I k)| ≤
          ∑ k, |adjugateRow C I j k * e (I k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |adjugateRow C I j k| * B := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (he (I k)) (abs_nonneg _)
      _ = B * ∑ k, |adjugateRow C I j k| := by
        rw [← Finset.sum_mul, mul_comm]
  have hj : |(basicMatrix C I).det * e j| ≤ |(basicMatrix C I).det| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
  calc
    |residualNumerator C I e j| =
        |(basicMatrix C I).det| *
          |(∑ k, adjugateRow C I j k * e (I k)) -
            (basicMatrix C I).det * e j| := by rw [residualNumerator, abs_mul]
    _ ≤ |(basicMatrix C I).det| *
        (|∑ k, adjugateRow C I j k * e (I k)| +
          |(basicMatrix C I).det * e j|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
    _ ≤ |(basicMatrix C I).det| *
        (B * (∑ k, |adjugateRow C I j k|) + |(basicMatrix C I).det| * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hs hj) (abs_nonneg _)
    _ = B * residualBudget C I j := by unfold residualBudget; ring

lemma basicSolution_det_smul (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ)
    (I : Fin n → ι) (hI : (basicMatrix C I).det ≠ 0) :
    ((basicMatrix C I).det : ℝ) • basicSolution C h I =
      (realMatrix (basicMatrix C I)).adjugate *ᵥ (fun k => h (I k)) := by
  have hd : ((basicMatrix C I).det : ℝ) ≠ 0 := by exact_mod_cast hI
  rw [basicSolution, smul_smul, mul_inv_cancel₀ hd, one_smul]

lemma realResidual_eq (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ)
    (I : Fin n → ι) (hI : (basicMatrix C I).det ≠ 0) (j : ι) :
    (((basicMatrix C I).det : ℝ) ^ 2) *
      (matrixRows (C.map (Int.castRingHom ℝ)) j (basicSolution C h I) - h j) =
        realResidual C I h j := by
  have hv := congrArg (fun x => C.map (Int.castRingHom ℝ) *ᵥ x)
    (basicSolution_det_smul C h I hI)
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← realMatrix_adjugate] at hv
  have hm : C.map (Int.castRingHom ℝ) * realMatrix (basicMatrix C I).adjugate =
      (adjugateRow C I).map (Int.castRingHom ℝ) := by
    ext a k
    simp [adjugateRow, realMatrix, Matrix.mul_apply]
  rw [hm] at hv
  have hj := congrFun hv j
  change ((basicMatrix C I).det : ℝ) *
    matrixRows (C.map (Int.castRingHom ℝ)) j (basicSolution C h I) =
      ∑ k, (adjugateRow C I j k : ℝ) * h (I k) at hj
  unfold realResidual
  rw [← hj]
  ring

lemma realResidual_affine (C : Matrix ι (Fin n) ℤ)
    (d e : ι → ℤ) (I : Fin n → ι) (j : ι) (t : ℝ) :
    realResidual C I (fun k => t * (d k : ℝ) + e k) j =
      (residualNumerator C I d j : ℝ) * t + residualNumerator C I e j := by
  have hs : (∑ k, (adjugateRow C I j k : ℝ) *
      (t * (d (I k) : ℝ) + e (I k))) =
      t * (∑ k, (adjugateRow C I j k : ℝ) * d (I k)) +
        ∑ k, (adjugateRow C I j k : ℝ) * e (I k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [realResidual, residualNumerator, Int.cast_mul, Int.cast_sub, Int.cast_sum]
  rw [hs]
  ring

lemma basicSolution_feasible_iff_residual (C : Matrix ι (Fin n) ℤ)
    (h : ι → ℝ) (I : Fin n → ι) (hI : (basicMatrix C I).det ≠ 0) :
    basicSolution C h I ∈ NormalProjective.halfspaceRegion
      (matrixRows (C.map (Int.castRingHom ℝ))) h ↔
        ∀ j, realResidual C I h j ≤ 0 := by
  have hd : ((basicMatrix C I).det : ℝ) ≠ 0 := by exact_mod_cast hI
  have hp : 0 < ((basicMatrix C I).det : ℝ) ^ 2 := sq_pos_of_ne_zero hd
  constructor
  · intro h j
    rw [← realResidual_eq C _ I hI j]
    exact mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr (h j))
  · intro h j
    have hj := h j
    rw [← realResidual_eq C _ I hI j] at hj
    nlinarith

/-- Every basic-vertex feasibility test stabilizes at a bound independent of the
slope vector. In the toric application this vector encodes the unrestricted raw
coefficient vector. No finite coefficient-box restriction is used. -/
theorem affine_basic_feasibility_stable (C : Matrix ι (Fin n) ℤ)
    (d e : ι → ℤ) (B : ℤ) (hB : 0 ≤ B) (he : ∀ j, |e j| ≤ B)
    (t u : ℝ)
    (ht : (B * affineThresholdCoefficient C : ℝ) < t)
    (hu : (B * affineThresholdCoefficient C : ℝ) < u) :
    feasibleBases C (fun j => t * (d j : ℝ) + e j) =
      feasibleBases C (fun j => u * (d j : ℝ) + e j) := by
  ext I
  by_cases hI : (basicMatrix C I).det = 0
  · simp [feasibleBases, hI]
  · simp only [feasibleBases, Set.mem_setOf_eq]
    rw [basicSolution_feasible_iff_residual C _ I hI,
      basicSolution_feasible_iff_residual C _ I hI]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro j
    rw [realResidual_affine, realResidual_affine]
    have hb : |residualNumerator C I e j| ≤ B * affineThresholdCoefficient C :=
      (abs_residualNumerator_le C I e j B hB he).trans
        (mul_le_mul_of_nonneg_left (residualBudget_le_threshold C I j) hB)
    have hbr : (|residualNumerator C I e j| : ℝ) ≤
        (B * affineThresholdCoefficient C : ℝ) := by exact_mod_cast hb
    exact integer_affine_sign_stable _ _ t u (hbr.trans_lt ht) (hbr.trans_lt hu)

end ToricPower
