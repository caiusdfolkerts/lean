module

public import wishart.verified.core05
public import tau_ceti.probability.distributions.wishart.inverse.basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import tau_ceti.analysis.matrix.orthogonal_rows
public import tau_ceti.linear_algebra.matrix.rank

/- Generated ordinary proof stage. See audit/staged_compact_inverseassociation/InverseAssociation01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/InverseRegressionAlgebra.lean -/



/-!
# The affine inverse-regression identity

This is the matrix identity behind (16).  The inverse of the existing Wishart
regression matrix, after exchanging its two coordinate blocks, is an affine
congruence in the inverse Schur complement.  The other coefficients depend only
on the independent pivot and Gaussian variables.  No density or conditional
distribution is asserted in this algebraic file.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Classical MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

def inverseRegressionBlock {q m : ℕ}
    (S : Matrix (Fin q) (Fin q) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin q) (Fin m) ℝ) :
    Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ :=
  Matrix.fromBlocks S (S * H) (Hᵀ * S) (R + Hᵀ * S * H)

theorem inverseRegressionBlock_eq_affine {q m : ℕ}
    (S : Matrix (Fin q) (Fin q) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin q) (Fin m) ℝ) :
    inverseRegressionBlock S R H = Matrix.fromBlocks 0 0 0 R +
      (Matrix.fromCols 1 H)ᵀ * S * Matrix.fromCols 1 H := by
  rw [Matrix.transpose_fromCols, Matrix.transpose_one, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols]
  simp only [inverseRegressionBlock, Matrix.one_mul, Matrix.mul_one,
    Matrix.fromBlocks_add, zero_add]

theorem inverseRegressionBlock_isHermitian {q m : ℕ}
    {S : Matrix (Fin q) (Fin q) ℝ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.IsHermitian) (hR : R.IsHermitian)
    (H : Matrix (Fin q) (Fin m) ℝ) :
    (inverseRegressionBlock S R H).IsHermitian := by
  have hSt : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.eq
  apply Matrix.IsHermitian.fromBlocks hS
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, hSt]
  · exact hR.add (by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.isHermitian_conjTranspose_mul_mul H hS)

/-- The matrix in (16), in the original `Fin (q+m)` coordinates. -/
def inverseRegressionAffine {q m : ℕ}
    (S : SymmetricMatrix q) (R : SymmetricMatrix m)
    (H : Matrix (Fin q) (Fin m) ℝ) : SymmetricMatrix (q + m) :=
  ⟨(inverseRegressionBlock (S : Matrix (Fin q) (Fin q) ℝ)
      (R : Matrix (Fin m) (Fin m) ℝ) H).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    ((inverseRegressionBlock_isHermitian (selfAdjoint.isHermitian_coe S)
      (selfAdjoint.isHermitian_coe R) H).submatrix _).isSelfAdjoint⟩

@[fun_prop] theorem measurable_inverseRegressionAffine {q m : ℕ} :
    Measurable (fun x : SymmetricMatrix q ×
      (SymmetricMatrix m × Matrix (Fin q) (Fin m) ℝ) =>
        inverseRegressionAffine x.1 x.2.1 x.2.2) := by
  apply Measurable.subtype_mk
  unfold inverseRegressionBlock
  fun_prop

theorem inverseRegressionAffine_selected {q m : ℕ}
    (S : SymmetricMatrix q) (R : SymmetricMatrix m)
    (H : Matrix (Fin q) (Fin m) ℝ) :
    ((inverseRegressionAffine S R H : SymmetricMatrix (q + m)) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
      (Fin.castAdd m) (Fin.castAdd m) = (S : Matrix (Fin q) (Fin q) ℝ) := by
  ext i j
  simp [inverseRegressionAffine, inverseRegressionBlock, Matrix.submatrix_apply]

/-- The affine regression map preserves the Loewner order, without any
positivity assumption on its fixed residual coefficient. -/
theorem inverseRegressionAffine_mono {q m : ℕ}
    (S T : SymmetricMatrix q) (R : SymmetricMatrix m)
    (H : Matrix (Fin q) (Fin m) ℝ)
    (hST : ((T : Matrix (Fin q) (Fin q) ℝ) - S).PosSemidef) :
    (((inverseRegressionAffine T R H : SymmetricMatrix (q + m)) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ) -
      (inverseRegressionAffine S R H : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)).PosSemidef := by
  have h := hST.conjTranspose_mul_mul_same
    (Matrix.fromCols (1 : Matrix (Fin q) (Fin q) ℝ) H)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have heq : inverseRegressionBlock T R H - inverseRegressionBlock S R H =
      (Matrix.fromCols 1 H)ᵀ * ((T : Matrix (Fin q) (Fin q) ℝ) -
        (S : Matrix (Fin q) (Fin q) ℝ)) *
        Matrix.fromCols 1 H := by
    rw [inverseRegressionBlock_eq_affine, inverseRegressionBlock_eq_affine,
      add_sub_add_left_eq_sub, Matrix.mul_sub, Matrix.sub_mul]
  have heq' : ((inverseRegressionAffine T R H : SymmetricMatrix (q + m)) :
      Matrix (Fin (q + m)) (Fin (q + m)) ℝ) -
      (inverseRegressionAffine S R H : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) =
      ((Matrix.fromCols 1 H)ᵀ * ((T : Matrix (Fin q) (Fin q) ℝ) -
        (S : Matrix (Fin q) (Fin q) ℝ)) * Matrix.fromCols 1 H).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    exact congrFun (congrFun heq (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  rw [heq']
  exact h.submatrix finSumFinEquiv.symm

theorem inverseRegressionBlock_posDef {q m : ℕ}
    {S : Matrix (Fin q) (Fin q) ℝ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.PosDef) (hR : R.PosDef) (H : Matrix (Fin q) (Fin m) ℝ) :
    (inverseRegressionBlock S R H).PosDef := by
  letI := Matrix.invertibleOfIsUnitDet S hS.det_pos.ne'.isUnit
  have hSt : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hcross : (S * H)ᴴ = Hᵀ * S := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hSt]
  have hcancel : Hᵀ * S * S⁻¹ * (S * H) = Hᵀ * S * H := by
    rw [Matrix.mul_assoc Hᵀ S S⁻¹, Matrix.mul_nonsing_inv S hS.det_pos.ne'.isUnit,
      Matrix.mul_one, ← Matrix.mul_assoc]
  have hpsd : (inverseRegressionBlock S R H).PosSemidef := by
    unfold inverseRegressionBlock
    rw [← hcross, Matrix.PosDef.fromBlocks₁₁ _ _ hS, hcross, hcancel,
      add_sub_cancel_right]
    exact hR.posSemidef
  apply hpsd.posDef_iff_det_ne_zero.mpr
  rw [inverseRegressionBlock, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    hcancel, add_sub_cancel_right]
  exact mul_ne_zero hS.det_pos.ne' hR.det_pos.ne'

theorem inverseRegressionAffine_posDef {q m : ℕ}
    {S : SymmetricMatrix q} {R : SymmetricMatrix m}
    (hS : (S : Matrix (Fin q) (Fin q) ℝ).PosDef)
    (hR : (R : Matrix (Fin m) (Fin m) ℝ).PosDef)
    (H : Matrix (Fin q) (Fin m) ℝ) :
    (inverseRegressionAffine S R H : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosDef :=
  (inverseRegressionBlock_posDef hS hR H).submatrix finSumFinEquiv.symm.injective

theorem regressionBlockMatrix_factorization {m q : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin q) (Fin m) ℝ)
    (W : Matrix (Fin q) (Fin q) ℝ) :
    regressionBlockMatrix R G W =
      Matrix.fromBlocks R 0 G 1 * Matrix.fromBlocks 1 0 0 W *
        (Matrix.fromBlocks R 0 G 1)ᵀ := by
  simp only [regressionBlockMatrix, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]

theorem inverse_regression_factor {m q : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin q) (Fin m) ℝ)
    (hR : R.det ≠ 0) :
    (Matrix.fromBlocks R 0 G (1 : Matrix (Fin q) (Fin q) ℝ))⁻¹ =
      Matrix.fromBlocks R⁻¹ 0 (-G * R⁻¹) 1 := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_nonsing_inv _ hR.isUnit, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
    add_zero, zero_add, add_neg_cancel, Matrix.fromBlocks_one]

theorem inverse_block_diagonal {m q : ℕ}
    (W : Matrix (Fin q) (Fin q) ℝ) (hW : W.det ≠ 0) :
    (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) 0 0 W)⁻¹ =
      Matrix.fromBlocks 1 0 0 W⁻¹ := by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv _ hW.isUnit,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.fromBlocks_one]

/-- Exact block inverse, with the Schur-complement coordinates moved first. -/
theorem regressionBlockMatrix_inverse_swap {m q : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin q) (Fin m) ℝ)
    (W : Matrix (Fin q) (Fin q) ℝ) (hR : R.det ≠ 0) (hW : W.det ≠ 0) :
    ((regressionBlockMatrix R G W)⁻¹).submatrix
      (Equiv.sumComm (Fin q) (Fin m)) (Equiv.sumComm (Fin q) (Fin m)) =
      inverseRegressionBlock W⁻¹ (R⁻¹ᵀ * R⁻¹) (-G * R⁻¹) := by
  rw [regressionBlockMatrix_factorization, Matrix.mul_inv_rev,
    Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
    inverse_regression_factor R G hR, inverse_block_diagonal W hW]
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero,
    Equiv.sumComm_apply, Matrix.fromBlocks_submatrix_sum_swap_sum_swap, inverseRegressionBlock,
    Matrix.mul_assoc]

def swapBlockEquiv (q m : ℕ) : Fin (q + m) ≃ Fin (m + q) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin q) (Fin m)).trans finSumFinEquiv)

def swappedSymmetricInv {m q : ℕ} (X : SymmetricMatrix (m + q)) :
    SymmetricMatrix (q + m) :=
  ⟨((X : Matrix (Fin (m + q)) (Fin (m + q)) ℝ)⁻¹).submatrix
      (swapBlockEquiv q m) (swapBlockEquiv q m),
    ((selfAdjoint.isHermitian_coe X).inv.submatrix _).isSelfAdjoint⟩

@[fun_prop] theorem measurable_swappedSymmetricInv {m q : ℕ} :
    Measurable (@swappedSymmetricInv m q) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hm : Measurable (fun X : SymmetricMatrix (m + q) =>
      (symmetricInv X : Matrix (Fin (m + q)) (Fin (m + q)) ℝ)
        (swapBlockEquiv q m i) (swapBlockEquiv q m j)) :=
    (measurable_pi_apply (swapBlockEquiv q m j)).comp
      ((measurable_pi_apply (swapBlockEquiv q m i)).comp measurable_symmetricInv.subtype_val)
  have heq : (fun X : SymmetricMatrix (m + q) =>
      ((X : Matrix (Fin (m + q)) (Fin (m + q)) ℝ)⁻¹)
        (swapBlockEquiv q m i) (swapBlockEquiv q m j)) =
      (fun X : SymmetricMatrix (m + q) =>
        (symmetricInv X : Matrix (Fin (m + q)) (Fin (m + q)) ℝ)
          (swapBlockEquiv q m i) (swapBlockEquiv q m j)) := by
    funext X
    rw [coe_symmetricInv]
  change Measurable (fun X : SymmetricMatrix (m + q) =>
    ((X : Matrix (Fin (m + q)) (Fin (m + q)) ℝ)⁻¹)
      (swapBlockEquiv q m i) (swapBlockEquiv q m j))
  rw [heq]
  exact hm

def inverseRegressionCoefficient {m q : ℕ}
    (V : SymmetricMatrix m) (G : Fin m → EuclideanSpace ℝ (Fin q)) :
    Matrix (Fin q) (Fin m) ℝ :=
  -Matrix.of (fun i j => G j i) * (CFC.sqrt (V : Matrix (Fin m) (Fin m) ℝ))⁻¹

@[fun_prop] theorem measurable_inverseRegressionCoefficient {m q : ℕ} :
    Measurable (fun x : SymmetricMatrix m × (Fin m → EuclideanSpace ℝ (Fin q)) =>
      inverseRegressionCoefficient x.1 x.2) := by
  unfold inverseRegressionCoefficient
  fun_prop

/-- Inversion of the actual zero-cross-scale Wishart reconstruction is exactly
the affine inverse-Wishart reconstruction.  Both hypotheses hold almost surely
under the independent Wishart source law. -/
theorem swapped_inverse_regressionReconstruction {m q : ℕ}
    (x : RegressionData m q)
    (hV : (x.1 : Matrix (Fin m) (Fin m) ℝ).PosDef)
    (hW : (x.2.2 : Matrix (Fin q) (Fin q) ℝ).PosDef) :
    swappedSymmetricInv (regressionReconstruction (0 : Matrix (Fin m) (Fin q) ℝ) x) =
      inverseRegressionAffine (symmetricInv x.2.2) (symmetricInv x.1)
        (inverseRegressionCoefficient x.1 x.2.1) := by
  let R := CFC.sqrt (x.1 : Matrix (Fin m) (Fin m) ℝ)
  have hRR : R * Rᵀ = (x.1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self _ hV.posSemidef.nonneg
  have hR : R.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hRR
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hh
    exact hV.det_pos.ne' hh.symm
  have hres : R⁻¹ᵀ * R⁻¹ = (x.1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ := by
    rw [← hRR, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  have hblock := regressionBlockMatrix_inverse_swap R
    (Matrix.of (fun i j => x.2.1 j i)) (x.2.2 : Matrix (Fin q) (Fin q) ℝ)
    hR hW.det_pos.ne'
  rw [hres] at hblock
  have hsource := regressionReconstruction_submatrix
    (0 : Matrix (Fin m) (Fin q) ℝ) x
  simp only [Matrix.transpose_zero, Matrix.zero_mul, zero_add] at hsource
  have hinv := congrArg (fun M : Matrix (Fin m ⊕ Fin q) (Fin m ⊕ Fin q) ℝ =>
    M⁻¹.submatrix (Equiv.sumComm (Fin q) (Fin m))
      (Equiv.sumComm (Fin q) (Fin m))) hsource
  rw [Matrix.inv_submatrix_equiv, hblock] at hinv
  apply Subtype.ext
  ext i j
  simpa only [swappedSymmetricInv, inverseRegressionAffine, inverseRegressionCoefficient,
    coe_symmetricInv, swapBlockEquiv, Matrix.submatrix_apply,
    Equiv.trans_apply, Equiv.apply_symm_apply, R] using congrArg
      (fun M : Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ =>
        M (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) hinv

end Wishart
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/InverseRegressionLaw.lean -/



/-!
# Independent affine regression for the actual inverse-Wishart law

The selected inverse Schur complement is independent of the pivot and Gaussian
matrix.  The full law is obtained by inverting the already proved real-shape
Wishart regression law.  This proves the complete joint representation needed
in Theorem 6.1, including the zero-dimensional complementary-block case.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Classical MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

abbrev InverseRegressionNoise (q m : ℕ) :=
  SymmetricMatrix m × (Fin m → EuclideanSpace ℝ (Fin q))

def inverseRegressionNoiseMeasure (β : ℝ) (q m : ℕ) :
    Measure (InverseRegressionNoise q m) :=
  (nonsingularWishartMeasure β (1 : Matrix (Fin m) (Fin m) ℝ)).prod
    (Measure.pi fun _ : Fin m =>
      ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) 1)

def inverseRegressionSource (β : ℝ) (q m : ℕ) :
    Measure (SymmetricMatrix q × InverseRegressionNoise q m) :=
  (inverseWishartMeasure (β - m) (1 : Matrix (Fin q) (Fin q) ℝ)).prod
    (inverseRegressionNoiseMeasure β q m)

theorem inverseRegressionNoiseMeasure_isProbability {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    IsProbabilityMeasure (inverseRegressionNoiseMeasure β q m) := by
  have hm : (m : ℝ) - 1 < β := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    push_cast at hβ
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hm
  unfold inverseRegressionNoiseMeasure
  infer_instance

theorem inverseRegressionSource_isProbability {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    IsProbabilityMeasure (inverseRegressionSource β q m) := by
  have hq : (q : ℝ) - 1 < β - m := by
    push_cast at hβ
    linarith
  letI := isProbabilityMeasure_inverseWishartMeasure
    (S := (1 : Matrix (Fin q) (Fin q) ℝ)) Matrix.PosDef.one hq
  letI := inverseRegressionNoiseMeasure_isProbability hβ
  unfold inverseRegressionSource
  infer_instance

def inverseRegressionSourceTransform {m q : ℕ} (x : RegressionData m q) :
    SymmetricMatrix q × InverseRegressionNoise q m :=
  (symmetricInv x.2.2, (x.1, x.2.1))

@[fun_prop] theorem measurable_inverseRegressionSourceTransform {m q : ℕ} :
    Measurable (@inverseRegressionSourceTransform m q) := by
  unfold inverseRegressionSourceTransform
  fun_prop

theorem measurePreserving_inverseRegressionSourceTransform
    {β : ℝ} {q m : ℕ} (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    MeasurePreserving inverseRegressionSourceTransform
      (regressionDataMeasure β m q 1) (inverseRegressionSource β q m) := by
  have hq : (q : ℝ) - 1 < β - m := by
    push_cast at hβ
    linarith
  have hm : (m : ℝ) - 1 < β := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    push_cast at hβ
    linarith
  let V := nonsingularWishartMeasure β (1 : Matrix (Fin m) (Fin m) ℝ)
  let G := Measure.pi fun _ : Fin m =>
    ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin q))
      (1 : Matrix (Fin q) (Fin q) ℝ)
  let W := nonsingularWishartMeasure (β - m) (1 : Matrix (Fin q) (Fin q) ℝ)
  letI : IsProbabilityMeasure V :=
    isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hm
  letI : IsProbabilityMeasure W :=
    isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hq
  have hinv : MeasurePreserving symmetricInv W
      (inverseWishartMeasure (β - m) (1 : Matrix (Fin q) (Fin q) ℝ)) := by
    refine ⟨measurable_symmetricInv, ?_⟩
    simp only [inverseWishartMeasure_def, inv_one, W]
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc V G W)
  have hswap := (Measure.measurePreserving_swap (μ := V.prod G) (ν := W)).comp hassoc
  exact (hinv.prod (MeasurePreserving.id (V.prod G))).comp hswap

def inverseRegressionReconstruction {q m : ℕ}
    (x : SymmetricMatrix q × InverseRegressionNoise q m) : SymmetricMatrix (q + m) :=
  inverseRegressionAffine x.1 (symmetricInv x.2.1)
    (inverseRegressionCoefficient x.2.1 x.2.2)

@[fun_prop] theorem measurable_inverseRegressionReconstruction {q m : ℕ} :
    Measurable (@inverseRegressionReconstruction q m) := by
  unfold inverseRegressionReconstruction
  exact measurable_inverseRegressionAffine.comp
    (measurable_fst.prodMk
      ((measurable_symmetricInv.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_inverseRegressionCoefficient.comp measurable_snd)))

theorem inverseRegressionReconstruction_selected {q m : ℕ}
    (x : SymmetricMatrix q × InverseRegressionNoise q m) :
    principalSymmetricBlock (Fin.castAdd m) (inverseRegressionReconstruction x) = x.1 := by
  apply Subtype.ext
  exact inverseRegressionAffine_selected _ _ _

theorem inverseRegressionReconstruction_mono {q m : ℕ}
    (x : InverseRegressionNoise q m) (S T : SymmetricMatrix q)
    (hST : ((T : Matrix (Fin q) (Fin q) ℝ) - S).PosSemidef) :
    (((inverseRegressionReconstruction (T, x) : SymmetricMatrix (q + m)) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ) -
      (inverseRegressionReconstruction (S, x) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ)).PosSemidef :=
  inverseRegressionAffine_mono S T _ _ hST

theorem map_swappedSymmetricInv_identityWishart {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    (nonsingularWishartMeasure β
      (1 : Matrix (Fin (m + q)) (Fin (m + q)) ℝ)).map swappedSymmetricInv =
      inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have hm : ((m + q : ℕ) : ℝ) - 1 < β := by
    simpa only [Nat.add_comm] using hβ
  have hfun : @swappedSymmetricInv m q =
      symmetricInv ∘ principalSymmetricBlock (swapBlockEquiv q m) := by
    funext X
    apply Subtype.ext
    simpa only [swappedSymmetricInv, Function.comp_apply, coe_symmetricInv,
      principalSymmetricBlock] using
      (Matrix.inv_submatrix_equiv (X : Matrix (Fin (m + q)) (Fin (m + q)) ℝ)
        (swapBlockEquiv q m) (swapBlockEquiv q m)).symm
  rw [hfun, ← Measure.map_map measurable_symmetricInv
      (measurable_principalSymmetricBlock _),
    map_principalSymmetricBlock_nonsingularWishartMeasure _
      (swapBlockEquiv q m).injective Matrix.PosDef.one hm,
    Matrix.submatrix_one_equiv, inverseWishartMeasure_def, inv_one]

/-- Actual independent affine inverse-Wishart regression.  The selected law is
`IW_q(β-m,I)` and the independent noise is the literal product of `W_m(β,I)`
and an `m` by `q` standard Gaussian array.  The displayed reconstruction uses
`R=V⁻¹` and `H=-Gᵀ sqrt(V)⁻¹`; hence it is precisely the affine map (16).
The entire full-matrix law is identified, not only a selected marginal. -/
theorem map_inverseRegressionReconstruction {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    (inverseRegressionSource β q m).map inverseRegressionReconstruction =
      inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have hm : ((m + q : ℕ) : ℝ) - 1 < β := by
    simpa only [Nat.add_comm] using hβ
  have hV : ∀ᵐ x ∂regressionDataMeasure β m q 1,
      (x.1 : Matrix (Fin m) (Fin m) ℝ).PosDef :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_posDef_nonsingularWishartMeasure β (1 : Matrix (Fin m) (Fin m) ℝ))
  have hW : ∀ᵐ x ∂regressionDataMeasure β m q 1,
      (x.2.2 : Matrix (Fin q) (Fin q) ℝ).PosDef :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_snd.ae
        (ae_posDef_nonsingularWishartMeasure (β - m)
          (1 : Matrix (Fin q) (Fin q) ℝ)))
  rw [← (measurePreserving_inverseRegressionSourceTransform hβ).map_eq,
    Measure.map_map measurable_inverseRegressionReconstruction
      measurable_inverseRegressionSourceTransform]
  have hae : inverseRegressionReconstruction ∘ inverseRegressionSourceTransform =ᵐ[
      regressionDataMeasure β m q 1]
      swappedSymmetricInv ∘ regressionReconstruction
        (0 : Matrix (Fin m) (Fin q) ℝ) := by
    filter_upwards [hV, hW] with x hxV hxW
    exact (swapped_inverse_regressionReconstruction x hxV hxW).symm
  rw [Measure.map_congr hae,
    ← Measure.map_map measurable_swappedSymmetricInv
      (measurable_regressionReconstruction 0),
    map_regressionReconstruction hm 0 Matrix.PosDef.one]
  have hscale : regressionScale (0 : Matrix (Fin m) (Fin q) ℝ) 1 = 1 := by
    simp [regressionScale, Matrix.fromBlocks_one]
  rw [hscale]
  exact map_swappedSymmetricInv_identityWishart hβ

theorem map_selectedBlock_identityInverseWishart {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    (inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)).map
      (principalSymmetricBlock (Fin.castAdd m)) =
      inverseWishartMeasure (β - m) (1 : Matrix (Fin q) (Fin q) ℝ) := by
  letI := inverseRegressionNoiseMeasure_isProbability hβ
  rw [← map_inverseRegressionReconstruction hβ,
    Measure.map_map (measurable_principalSymmetricBlock _)
      measurable_inverseRegressionReconstruction]
  have hfun : principalSymmetricBlock (Fin.castAdd m) ∘
      (@inverseRegressionReconstruction q m) =
        (Prod.fst : SymmetricMatrix q × InverseRegressionNoise q m → SymmetricMatrix q) := by
    funext x
    exact inverseRegressionReconstruction_selected x
  rw [hfun, inverseRegressionSource, Measure.map_fst_prod, measure_univ, one_smul]

end Wishart
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/AntitoneChamberAssociation.lean -/



open scoped Classical ENNReal

/-!
# Common antitone tests on an associated chamber law

The inverse-Wishart application also uses two decreasing spectral functions.
For bounded tests the change `f ↦ M - f` preserves covariance and makes each
test increasing. Monotone truncation then permits arbitrary nonnegative tests,
including infinite expectations. The final theorem applies this closure argument
to the actual chamber law from Lemma 2.1.
-/

open MeasureTheory Filter
open scoped Topology

namespace WishartVerification

section BoundedComplements

variable {Ω : Type*} [MeasurableSpace Ω] [Preorder Ω]

/-- Bounded common antitone tests satisfy association whenever the same law
associates every nonnegative increasing measurable pair on `s`. This is a
closure lemma; the final chamber theorem supplies its association premise from
the already proved continuous FKG theorem. -/
theorem bounded_antitone_association_of_nonnegative_association
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hinc : ∀ F G : Ω → ℝ, Measurable F → Measurable G →
      (∀ x, 0 ≤ F x) → (∀ x, 0 ≤ G x) → MonotoneOn F s → MonotoneOn G s →
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ) * (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (F x * G x) ∂μ)
    (f g : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfM : ∀ x, f x ≤ M) (hgM : ∀ x, g x ≤ M)
    (hfa : AntitoneOn f s) (hga : AntitoneOn g s) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  let F : Ω → ℝ := fun x ↦ M - f x
  let G : Ω → ℝ := fun x ↦ M - g x
  have hFm : Measurable F := measurable_const.sub hfm
  have hGm : Measurable G := measurable_const.sub hgm
  have hF0 (x) : 0 ≤ F x := sub_nonneg.mpr (hfM x)
  have hG0 (x) : 0 ≤ G x := sub_nonneg.mpr (hgM x)
  have hFM (x) : F x ≤ M := sub_le_self M (hf0 x)
  have hGM (x) : G x ≤ M := sub_le_self M (hg0 x)
  have hFi : MonotoneOn F s := fun x hx y hy hxy ↦ sub_le_sub_left (hfa hx hy hxy) M
  have hGi : MonotoneOn G s := fun x hx y hy hxy ↦ sub_le_sub_left (hga hx hy hxy) M
  have hfi := integrable_of_nonneg_bounded μ f M hfm hf0 hfM
  have hgi := integrable_of_nonneg_bounded μ g M hgm hg0 hgM
  have hfgi := integrable_of_nonneg_bounded μ (fun x ↦ f x * g x) (M * M)
    (hfm.mul hgm) (fun x ↦ mul_nonneg (hf0 x) (hg0 x))
    (fun x ↦ mul_le_mul (hfM x) (hgM x) (hg0 x) hM)
  have hFI := integrable_of_nonneg_bounded μ F M hFm hF0 hFM
  have hGI := integrable_of_nonneg_bounded μ G M hGm hG0 hGM
  have hFGI := integrable_of_nonneg_bounded μ (fun x ↦ F x * G x) (M * M)
    (hFm.mul hGm) (fun x ↦ mul_nonneg (hF0 x) (hG0 x))
    (fun x ↦ mul_le_mul (hFM x) (hGM x) (hG0 x) hM)
  have hcomp := integral_mul_le_of_lintegral_mul_le μ F G hF0 hG0 hFI hGI hFGI
    (hinc F G hFm hGm hF0 hG0 hFi hGi)
  have hid := covariance_kernel_identity hfi hgi hfgi
  have hidcomp := covariance_kernel_identity hFI hGI hFGI
  have hkernel (x y : Ω) :
      (F x - F y) * (G x - G y) = (f x - f y) * (g x - g y) := by
    dsimp [F, G]
    ring
  simp_rw [hkernel] at hidcomp
  rw [hid] at hidcomp
  linarith

end BoundedComplements

variable {ι : Type*} [Fintype ι]

/-- Common antitone association with extended nonnegative expectations, obtained
from increasing association through bounded complements and monotone caps. -/
theorem antitone_association_of_nonnegative_association
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (s : Set (ι → ℝ))
    (hinc : ∀ F G : (ι → ℝ) → ℝ, Measurable F → Measurable G →
      (∀ x, 0 ≤ F x) → (∀ x, 0 ≤ G x) → MonotoneOn F s → MonotoneOn G s →
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ) * (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (F x * G x) ∂μ)
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfa : AntitoneOn f s) (hga : AntitoneOn g s) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ := by
  let A (n : ℕ) := ∫⁻ x, ENNReal.ofReal (testCap n f x) ∂μ
  let B (n : ℕ) := ∫⁻ x, ENNReal.ofReal (testCap n g x) ∂μ
  have hAm (n : ℕ) : Measurable (testCap n f) := hfm.min measurable_const
  have hBm (n : ℕ) : Measurable (testCap n g) := hgm.min measurable_const
  have hAsup : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ⨆ n, A n :=
    lintegral_ofReal_eq_iSup_of_monotone μ _ _ hAm (testCap_mono_index f)
      (testCap_tendsto f)
  have hBsup : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ⨆ n, B n :=
    lintegral_ofReal_eq_iSup_of_monotone μ _ _ hBm (testCap_mono_index g)
      (testCap_tendsto g)
  have hAn : Monotone A := fun n m hnm ↦ lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (testCap_mono_index f x hnm)
  have hBn : Monotone B := fun n m hnm ↦ lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (testCap_mono_index g x hnm)
  have hfinite (n : ℕ) : A n * B n ≤ ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ := by
    let M : ℝ := (n : ℝ) + 1
    have hM : 0 ≤ M := by positivity
    have hfn0 := testCap_nonneg n f hf0
    have hgn0 := testCap_nonneg n g hg0
    have hfnM (x) : testCap n f x ≤ M := min_le_right _ _
    have hgnM (x) : testCap n g x ≤ M := min_le_right _ _
    have hfni := integrable_of_nonneg_bounded μ (testCap n f) M (hAm n) hfn0 hfnM
    have hgni := integrable_of_nonneg_bounded μ (testCap n g) M (hBm n) hgn0 hgnM
    have hfgni := integrable_of_nonneg_bounded μ
      (fun x ↦ testCap n f x * testCap n g x) (M * M)
      ((hAm n).mul (hBm n)) (fun x ↦ mul_nonneg (hfn0 x) (hgn0 x))
      (fun x ↦ mul_le_mul (hfnM x) (hgnM x) (hgn0 x) hM)
    have hreal := bounded_antitone_association_of_nonnegative_association μ s hinc
      (testCap n f) (testCap n g) M hM (hAm n) (hBm n) hfn0 hgn0 hfnM hgnM
      (fun x hx y hy hxy ↦ min_le_min_right _ (hfa hx hy hxy))
      (fun x hx y hy hxy ↦ min_le_min_right _ (hga hx hy hxy))
    have hcap : A n * B n ≤
        ∫⁻ x, ENNReal.ofReal (testCap n f x * testCap n g x) ∂μ := by
      dsimp [A, B]
      rw [← ofReal_integral_eq_lintegral_ofReal hfni (ae_of_all _ hfn0),
        ← ofReal_integral_eq_lintegral_ofReal hgni (ae_of_all _ hgn0),
        ← ofReal_integral_eq_lintegral_ofReal hfgni
          (ae_of_all _ fun x ↦ mul_nonneg (hfn0 x) (hgn0 x)),
        ← ENNReal.ofReal_mul (integral_nonneg hfn0)]
      exact ENNReal.ofReal_le_ofReal hreal
    exact hcap.trans (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
      (mul_le_mul (min_le_left _ _) (min_le_left _ _) (hgn0 x) (hf0 x)))
  rw [hAsup, hBsup, ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply iSup_le
  intro n
  apply iSup_le
  intro m
  exact (mul_le_mul' (hAn (le_max_left n m)) (hBn (le_max_right n m))).trans
    (hfinite (max n m))

variable [LinearOrder ι]

set_option maxHeartbeats 800000 in
/-- The common-decreasing version of the actual Lemma 2.1 chamber law. No
association assumption or finite-moment hypothesis is added. -/
theorem lemma_2_1_antitone_association
    (s : Set ℝ) (hs : MeasurableSet s) (w : ι → ℝ → ℝ)
    (β : ℝ) (hβ : 0 < β) (hwm : ∀ i, Measurable (w i))
    (hw0 : ∀ i t, 0 ≤ w i t)
    (hZ0 : (∫⁻ x : ι → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ 0)
    (hZtop : (∫⁻ x : ι → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ ∞)
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfa : AntitoneOn f (orderedChamber s)) (hga : AntitoneOn g (orderedChamber s)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂normalizedWeight volume (chamberWeight s w β)) *
        (∫⁻ x, ENNReal.ofReal (g x) ∂normalizedWeight volume (chamberWeight s w β)) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂normalizedWeight volume (chamberWeight s w β) := by
  letI := normalizedWeight_probability volume (chamberWeight s w β) hZ0 hZtop
  refine antitone_association_of_nonnegative_association (ι := ι)
    (normalizedWeight volume (chamberWeight s w β)) (orderedChamber s)
    ?_ f g hfm hgm hf0 hg0 hfa hga
  intro F G hFm hGm hF0 hG0 hFi hGi
  exact lemma_2_1_association (ι := ι) s hs w β hβ hwm hw0 hZ0 hZtop
    F G hFm hGm hF0 hG0 hFi hGi

end WishartVerification
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/InverseSpectralLaw.lean -/



/-!
# The inverse-Wishart spectral law by reciprocal reversal

Inversion sends an ascending positive spectrum to its reversed reciprocals.
The whole inverse-Wishart matrix law is the image of the already verified
Wishart Haar--Laguerre representation.  This exact transformation avoids a
second eigenvalue change-of-variables theorem.  The reversal reverses the
coordinate order, so common increasing and common decreasing association are
interchanged, with no change in the class of spectral tests.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart.Spectral

def reciprocalReverse {p : ℕ} (lam : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (lam (Fin.rev i))⁻¹

@[fun_prop] theorem measurable_reciprocalReverse {p : ℕ} :
    Measurable (@reciprocalReverse p) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (Fin.rev i)).inv

theorem reciprocalReverse_involutive {p : ℕ} :
    Function.Involutive (@reciprocalReverse p) := by
  intro lam
  funext i
  simp [reciprocalReverse]

theorem reciprocalReverse_mem_chamber {p : ℕ} {lam : Fin p → ℝ}
    (hlam : lam ∈ positiveChamber p) :
    reciprocalReverse lam ∈ positiveChamber p := by
  constructor
  · intro i j hij
    exact (inv_lt_inv₀ (hlam.2 (Fin.rev i)) (hlam.2 (Fin.rev j))).mpr
      (hlam.1 (Fin.rev_lt_rev.mpr hij))
  · intro i
    exact inv_pos.mpr (hlam.2 (Fin.rev i))

theorem reciprocalReverse_antitoneOn {p : ℕ} :
    AntitoneOn (@reciprocalReverse p) (positiveChamber p) := by
  intro x hx y hy hxy i
  exact (inv_le_inv₀ (hy.2 (Fin.rev i)) (hx.2 (Fin.rev i))).mpr (hxy (Fin.rev i))

theorem symmetricInv_conjugate {p : ℕ} (O : Orth p) (S : Sym p) :
    symmetricInv (conjugate O S) = conjugate O (symmetricInv S) := by
  have hOinv : (O : Matrix (Fin p) (Fin p) ℝ)⁻¹ =
      (O : Matrix (Fin p) (Fin p) ℝ)ᵀ :=
    Matrix.inv_eq_right_inv (orth_mul_transpose O)
  apply Subtype.ext
  simp only [coe_symmetricInv, conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, hOinv,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem symmetricInv_diagonalSym {p : ℕ} (lam : Fin p → ℝ)
    (hlam : ∀ i, lam i ≠ 0) :
    symmetricInv (diagonalSym lam) = diagonalSym (fun i => (lam i)⁻¹) := by
  apply Subtype.ext
  rw [coe_symmetricInv]
  change (Matrix.diagonal lam)⁻¹ = Matrix.diagonal (fun i ↦ (lam i)⁻¹)
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_inv_cancel₀ (hlam _), Matrix.diagonal_one]

def inverseSpectralMatrix {p : ℕ} (lam : Fin p → ℝ) (O : Orth p) : Sym p :=
  symmetricInv (conjugate O (diagonalSym lam))

@[fun_prop] theorem measurable_inverseSpectralMatrix {p : ℕ} :
    Measurable (fun z : (Fin p → ℝ) × Orth p => inverseSpectralMatrix z.1 z.2) := by
  unfold inverseSpectralMatrix
  exact measurable_symmetricInv.comp ((continuous_conjugate p).measurable.comp
    (measurable_snd.prodMk ((continuous_diagonalSym p).measurable.comp measurable_fst)))

theorem inverseSpectralMatrix_eq_reversed {p : ℕ}
    (lam : Fin p → ℝ) (O : Orth p) (hlam : ∀ i, lam i ≠ 0) :
    inverseSpectralMatrix lam O =
      conjugate (O * permutationOrth Fin.revPerm) (diagonalSym (reciprocalReverse lam)) := by
  rw [inverseSpectralMatrix, symmetricInv_conjugate, symmetricInv_diagonalSym lam hlam,
    conjugate_mul, conjugate_permutation_diagonal]
  congr 2
  funext i
  simp [reciprocalReverse]

theorem ascendingSpectrum_inverseSpectralMatrix {p : ℕ}
    (lam : Fin p → ℝ) (O : Orth p) (hlam : lam ∈ positiveChamber p) :
    ascendingSpectrum (inverseSpectralMatrix lam O) = reciprocalReverse lam := by
  rw [inverseSpectralMatrix_eq_reversed lam O (fun i ↦ (hlam.2 i).ne')]
  exact ascendingSpectrum_conjugate_diagonal _ _ (reciprocalReverse_mem_chamber hlam).1

theorem inverseSpectralMatrix_posDef {p : ℕ}
    (lam : Fin p → ℝ) (O : Orth p) (hlam : lam ∈ positiveChamber p) :
    (inverseSpectralMatrix lam O : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  have hD : (Matrix.diagonal lam).PosDef := Matrix.PosDef.diagonal hlam.2
  have hO : Function.Injective
      (O : Matrix (Fin p) (Fin p) ℝ).vecMul :=
    Matrix.vecMul_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.UnitaryGroup.det_isUnit O))
  have hc := hD.mul_mul_conjTranspose_same hO
  simpa only [inverseSpectralMatrix, conjugate,
    Matrix.coe_symmetricCongruenceLinearMap_apply, coe_symmetricInv,
    Matrix.conjTranspose_eq_transpose_of_trivial, diagonalSym] using hc.inv

/-- Fixed-frame inverse spectral matrices are antitone in every positive
eigenvalue coordinate.  This is the Loewner order used by affine regression. -/
theorem inverseSpectralMatrix_antitone {p : ℕ}
    (x y : Fin p → ℝ) (O : Orth p)
    (hx : x ∈ positiveChamber p) (hy : y ∈ positiveChamber p) (hxy : x ≤ y) :
    (((inverseSpectralMatrix x O : Sym p) : Matrix (Fin p) (Fin p) ℝ) -
      (inverseSpectralMatrix y O : Matrix (Fin p) (Fin p) ℝ)).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (x i)⁻¹ - (y i)⁻¹)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr
      ((inv_le_inv₀ (hy.2 i) (hx.2 i)).mpr (hxy i))
  have hh := hd.mul_mul_conjTranspose_same (O : Matrix (Fin p) (Fin p) ℝ)
  rw [inverseSpectralMatrix, inverseSpectralMatrix, symmetricInv_conjugate,
    symmetricInv_conjugate, symmetricInv_diagonalSym x (fun i ↦ (hx.2 i).ne'),
    symmetricInv_diagonalSym y (fun i ↦ (hy.2 i).ne')]
  simpa only [
    conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply, diagonalSym,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.diagonal_sub,
    Matrix.mul_sub, Matrix.sub_mul, Pi.sub_apply] using hh

/-- Exact product-source representation of the identity-scale inverse-Wishart
law. The spectral source remains the actual normalized Wishart chamber law;
reciprocal reversal above proves its exact relation to ordered inverse spectra. -/
theorem inverseWishart_laguerre_haar_representation {p : ℕ} {β : ℝ}
    (hβ : (p : ℝ) - 1 < β) :
    ((WishartVerification.normalizedWeight volume (wishartEigenDensity p β)).prod
      (haarProb (Orth p))).map (fun z => inverseSpectralMatrix z.1 z.2) =
      inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have hm : Measurable (fun z : (Fin p → ℝ) × Orth p =>
      conjugate z.2 (diagonalSym z.1)) := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      ((continuous_conjugate p).measurable.comp
        (measurable_snd.prodMk ((continuous_diagonalSym p).measurable.comp measurable_fst)))
  rw [inverseWishartMeasure_def, inv_one,
    ← wishart_laguerre_haar_representation hβ,
    Measure.map_map measurable_symmetricInv hm]
  rfl

theorem inverseIdentityEigenLaw_eq_map_reciprocalReverse {p : ℕ} {β : ℝ}
    (hβ : (p : ℝ) - 1 < β) :
    (inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ)).map ascendingSpectrum =
      (WishartVerification.normalizedWeight volume (wishartEigenDensity p β)).map
        reciprocalReverse := by
  rw [← inverseWishart_laguerre_haar_representation hβ,
    Measure.map_map (continuous_ascendingSpectrum p).measurable
      measurable_inverseSpectralMatrix]
  have hae : (fun z : (Fin p → ℝ) × Orth p =>
      ascendingSpectrum (inverseSpectralMatrix z.1 z.2)) =ᵐ[
        (WishartVerification.normalizedWeight volume (wishartEigenDensity p β)).prod
          (haarProb (Orth p))] reciprocalReverse ∘ Prod.fst := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_laguerreLaw_mem_chamber hβ)] with z hz
    exact ascendingSpectrum_inverseSpectralMatrix _ _ hz
  change Measure.map (fun z : (Fin p → ℝ) × Orth p ↦
      ascendingSpectrum (inverseSpectralMatrix z.1 z.2))
      ((WishartVerification.normalizedWeight volume (wishartEigenDensity p β)).prod
        (haarProb (Orth p))) = _
  rw [Measure.map_congr hae,
    ← Measure.map_map measurable_reciprocalReverse measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

end Wishart.Spectral
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/CompressionNormalization.lean -/



/-!
# Exact normalization of an arbitrary full-rank compression

For a positive scale Sigma and a full-column-rank matrix B, an invertible
ambient factor A is constructed with A Aᵀ=Sigma and
Bᵀ A=sqrt(Bᵀ Sigma B) E, where E selects the first q coordinates.
Consequently the normalized selected compression is exactly the leading
principal block, including its entire spectrum. No assumption of coordinate
alignment, disjointness, or an integer Wishart degree is introduced.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def compressionScale {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ := Bᵀ * Sigma * B

theorem compressionScale_posDef {p q : ℕ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) :
    (compressionScale Sigma B).PosDef := by
  have hBt : Bᵀ.rank = q := by rw [Matrix.rank_transpose, hB]
  simpa only [compressionScale, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose] using
    hSigma.mul_mul_conjTranspose_same
      ((Matrix.rank_eq_card_iff_vecMul_injective Bᵀ).1 (by simpa using hBt))

/-- Data of the constructed normalization, with its algebraic identities.
The existence theorem below proves these fields from positive scale and full
column rank; they are not assumptions on the input compression. -/
structure CompressionNormalization {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) where
  q_le : q ≤ p
  ambient : Matrix (Fin p) (Fin p) ℝ
  det_ambient_ne_zero : ambient.det ≠ 0
  ambient_gram : ambient * ambientᵀ = Sigma
  selected : Bᵀ * ambient = CFC.sqrt (compressionScale Sigma B) *
    (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE q_le) id

theorem nonempty_compressionNormalization {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) :
    Nonempty (CompressionNormalization Sigma B) := by
  have hBt : Bᵀ.rank = q := by rw [Matrix.rank_transpose, hB]
  have hqp : q ≤ p := hBt ▸ Bᵀ.rank_le_width
  have hG := compressionScale_posDef hSigma B hB
  obtain ⟨R, hR⟩ := hSigma.exists_generalLinearGroup_mul_transpose_eq
  let Rm : Matrix (Fin p) (Fin p) ℝ := R
  let T := CFC.sqrt (compressionScale Sigma B)
  have hT : T * Tᵀ = compressionScale Sigma B := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self _ hG.posSemidef.nonneg
  have hTdet : T.det ≠ 0 := sqrt_det_ne_zero_of_posDef hG
  have hGram : T * Tᵀ = (Bᵀ * Rm) * (Bᵀ * Rm)ᵀ := by
    rw [hT, Matrix.transpose_mul, Matrix.transpose_transpose]
    change Bᵀ * Sigma * B = Bᵀ * Rm * (Rmᵀ * B)
    rw [← hR]
    simp only [Rm, Matrix.mul_assoc]
  obtain ⟨Q, hQ, hfactor⟩ :=
    Matrix.exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE (Bᵀ * Rm) hqp hTdet hGram
  have hQt : Qᵀ * Q = 1 := mul_eq_one_comm.mp hQ
  let A := Rm * Qᵀ
  have hAgram : A * Aᵀ = Sigma := by
    dsimp only [A]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Rm * Qᵀ * (Q * Rmᵀ) = Rm * (Qᵀ * Q) * Rmᵀ := by
        simp only [Matrix.mul_assoc]
      _ = Sigma := by rw [hQt, Matrix.mul_one]; exact hR
  have hAdet : A.det ≠ 0 := by
    intro hzero
    have hdet := congrArg Matrix.det hAgram
    rw [Matrix.det_mul, hzero, zero_mul] at hdet
    exact hSigma.det_pos.ne' hdet.symm
  refine ⟨⟨hqp, A, hAdet, hAgram, ?_⟩⟩
  let E := (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id
  have hEQ : E * Q = Q.submatrix (Fin.castLE hqp) id := by
    have hrefl : (⇑(Equiv.refl (Fin p)).symm : Fin p → Fin p) = id := rfl
    simpa only [E, Equiv.coe_refl, hrefl, Function.id_comp] using
      Matrix.one_submatrix_mul (Fin.castLE hqp) (Equiv.refl (Fin p)) Q
  change Bᵀ * (Rm * Qᵀ) = T * E
  rw [← Matrix.mul_assoc, hfactor, ← hEQ]
  calc
    T * (E * Q) * Qᵀ = T * (E * (Q * Qᵀ)) := by simp only [Matrix.mul_assoc]
    _ = T * E := by rw [hQ, Matrix.mul_one]

def compressionNormalization {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) :
    CompressionNormalization Sigma B := Classical.choice (nonempty_compressionNormalization hSigma B hB)

def normalizedCompressionRows {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) : Matrix (Fin q) (Fin p) ℝ :=
  (CFC.sqrt (compressionScale Sigma B))⁻¹ * Bᵀ

def normalizedCompression {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) : SymmetricMatrix p → SymmetricMatrix q :=
  Matrix.symmetricCongruenceLinearMap (normalizedCompressionRows Sigma B)

@[fun_prop] theorem measurable_normalizedCompression {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) :
    Measurable (normalizedCompression Sigma B) :=
  (LinearMap.continuous_of_finiteDimensional _).measurable

theorem normalizedCompressionRows_scale {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) :
    normalizedCompressionRows Sigma B * Sigma * (normalizedCompressionRows Sigma B)ᵀ = 1 := by
  have hG := compressionScale_posDef hSigma B hB
  have hInv := (inverseSqrt_properties hG).2.1
  simpa only [normalizedCompressionRows, Matrix.transpose_mul,
    Matrix.transpose_transpose, compressionScale, Matrix.mul_assoc] using hInv

theorem normalizedCompressionRows_ambient {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) :
    normalizedCompressionRows Sigma B * N.ambient =
      (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le) id := by
  rw [normalizedCompressionRows, Matrix.mul_assoc, N.selected, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (sqrt_det_ne_zero_of_posDef (compressionScale_posDef hSigma B hB))), Matrix.one_mul]

/-- Every normalized compression becomes an orthonormal row map after any
ambient whitening factor, not merely the specially selected compression. -/
theorem normalizedCompressionRows_ambient_gram {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * Aᵀ = Sigma) :
    (normalizedCompressionRows Sigma B * A) * (normalizedCompressionRows Sigma B * A)ᵀ = 1 := by
  rw [Matrix.transpose_mul]
  calc
    normalizedCompressionRows Sigma B * A * (Aᵀ * (normalizedCompressionRows Sigma B)ᵀ) =
        normalizedCompressionRows Sigma B * (A * Aᵀ) * (normalizedCompressionRows Sigma B)ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, normalizedCompressionRows_scale hSigma B hB]

/-- The selected normalized matrix is literally the leading principal
matrix. Hence every spectral test, without any invariance hypothesis, is
transported to the same leading-block spectral test. -/
theorem normalizedCompression_congruence {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) (Y : SymmetricMatrix p) :
    normalizedCompression Sigma B (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
      principalSymmetricBlock (Fin.castLE N.q_le) Y := by
  unfold normalizedCompression
  rw [← LinearMap.comp_apply, ← Matrix.symmetricCongruenceLinearMap_mul,
    normalizedCompressionRows_ambient hSigma B hB N,
    ← principalSymmetricBlock_eq_congruence]

theorem normalizedCompression_congruence_sum {q m : ℕ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin (q + m)) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) (Y : SymmetricMatrix (q + m)) :
    normalizedCompression Sigma B (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
      principalSymmetricBlock (Fin.castAdd m) Y := by
  rw [normalizedCompression_congruence hSigma B hB N]
  have heq : Fin.castLE N.q_le = Fin.castAdd m := by
    funext i
    apply Fin.ext
    rfl
  rw [heq]

theorem normalizedCompression_congruence_full {p : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.rank = p)
    (N : CompressionNormalization Sigma B) (Y : SymmetricMatrix p) :
    normalizedCompression Sigma B (Matrix.symmetricCongruenceLinearMap N.ambient Y) = Y := by
  rw [normalizedCompression_congruence hSigma B hB N]
  apply Subtype.ext
  ext i j
  rfl

theorem map_compressionNormalization {p q : ℕ} (n : ℝ)
    {Sigma : Matrix (Fin p) (Fin p) ℝ} {B : Matrix (Fin p) (Fin q) ℝ}
    (N : CompressionNormalization Sigma B) :
    (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.symmetricCongruenceLinearMap N.ambient) =
      nonsingularWishartMeasure n Sigma := by
  rw [map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero n 1
    N.det_ambient_ne_zero, Matrix.mul_one, N.ambient_gram]

theorem compressionNormalization_shifted_matrix {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) (c : ℝ) (Y : SymmetricMatrix p) :
    Bᵀ * (Matrix.symmetricCongruenceLinearMap N.ambient Y : Matrix (Fin p) (Fin p) ℝ) * B +
        c • compressionScale Sigma B =
      CFC.sqrt (compressionScale Sigma B) *
        ((Y : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le) (Fin.castLE N.q_le) +
          c • (1 : Matrix (Fin q) (Fin q) ℝ)) * (CFC.sqrt (compressionScale Sigma B))ᵀ := by
  let T := CFC.sqrt (compressionScale Sigma B)
  let E := (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le) id
  have hT : T * Tᵀ = compressionScale Sigma B := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self _ (compressionScale_posDef hSigma B hB).posSemidef.nonneg
  have hEY : E * (Y : Matrix (Fin p) (Fin p) ℝ) * Eᵀ =
      (Y : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le) (Fin.castLE N.q_le) := by
    simp only [E, Matrix.transpose_submatrix, Matrix.transpose_one,
      Matrix.submatrix_one_mul_mul_submatrix_one]
  have hmain : Bᵀ * (N.ambient * (Y : Matrix (Fin p) (Fin p) ℝ) * N.ambientᵀ) * B =
      (Bᵀ * N.ambient) * (Y : Matrix (Fin p) (Fin p) ℝ) * (Bᵀ * N.ambient)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply, hmain, N.selected]
  change (T * E) * (Y : Matrix (Fin p) (Fin p) ℝ) * (T * E)ᵀ + c • compressionScale Sigma B =
    T * ((Y : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le) (Fin.castLE N.q_le) +
      c • (1 : Matrix (Fin q) (Fin q) ℝ)) * Tᵀ
  rw [Matrix.transpose_mul]
  calc
    T * E * (Y : Matrix (Fin p) (Fin p) ℝ) * (Eᵀ * Tᵀ) + c • compressionScale Sigma B =
        T * E * (Y : Matrix (Fin p) (Fin p) ℝ) * (Eᵀ * Tᵀ) + c • (T * Tᵀ) := by rw [hT]
    _ =
        T * (E * (Y : Matrix (Fin p) (Fin p) ℝ) * Eᵀ + c • 1) * Tᵀ := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hEY]

theorem compressionNormalization_shifted_det {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) (c : ℝ) (Y : SymmetricMatrix p) :
    (Bᵀ * (Matrix.symmetricCongruenceLinearMap N.ambient Y : Matrix (Fin p) (Fin p) ℝ) * B +
      c • compressionScale Sigma B).det =
      (compressionScale Sigma B).det *
        ((Y : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le) (Fin.castLE N.q_le) +
          c • (1 : Matrix (Fin q) (Fin q) ℝ)).det := by
  have hTdet : (CFC.sqrt (compressionScale Sigma B)).det *
      (CFC.sqrt (compressionScale Sigma B)).det = (compressionScale Sigma B).det := by
    simpa only [Matrix.det_mul] using congrArg Matrix.det
      (CFC.sqrt_mul_sqrt_self (compressionScale Sigma B)
        (compressionScale_posDef hSigma B hB).posSemidef.nonneg)
  rw [compressionNormalization_shifted_matrix hSigma B hB N c Y,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc
    _ = ((CFC.sqrt (compressionScale Sigma B)).det *
        (CFC.sqrt (compressionScale Sigma B)).det) *
        ((Y : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le) (Fin.castLE N.q_le) +
          c • (1 : Matrix (Fin q) (Fin q) ℝ)).det := by ring
    _ = _ := by rw [hTdet]

theorem unnormalize_normalizedCompression {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (Y : SymmetricMatrix p) :
    Matrix.symmetricCongruenceLinearMap (CFC.sqrt (compressionScale Omega B))
      (normalizedCompression Omega B Y) = Matrix.symmetricCongruenceLinearMap Bᵀ Y := by
  unfold normalizedCompression normalizedCompressionRows
  rw [← LinearMap.comp_apply, ← Matrix.symmetricCongruenceLinearMap_mul,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (sqrt_det_ne_zero_of_posDef (compressionScale_posDef hOmega B hB))),
    Matrix.one_mul]

theorem normalizedCompression_posDef {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    {Y : SymmetricMatrix p} (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    (normalizedCompression Omega B Y : Matrix (Fin k) (Fin k) ℝ).PosDef := by
  let R := (CFC.sqrt (compressionScale Omega B))⁻¹
  have hR : IsUnit R := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [show R.det = (CFC.sqrt (compressionScale Omega B)).det⁻¹ by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']]
    exact (inv_ne_zero (sqrt_det_ne_zero_of_posDef (compressionScale_posDef hOmega B hB))).isUnit
  have h := (compressionScale_posDef hY B hB).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit hR)
  simpa only [R, compressionScale, normalizedCompression, normalizedCompressionRows,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h

end Wishart
end
end CanonicalSource4

section CanonicalSource5
/- Source: Wishart/LoewnerSpectralTests.lean -/



/-!
# Ordered spectral tests and Loewner comparison

The monotonicity hypothesis is imposed only on ordered positive spectra,
including repeated eigenvalues.  Thus the comparison does not silently assume
simple spectra at the deterministic matrices used inside a conditional law.
-/

open Matrix MeasureTheory
open scoped Classical MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart.Spectral

def positiveOrderedSpectrum (p : ℕ) : Set (Fin p → ℝ) :=
  {lam | Monotone lam ∧ ∀ i, 0 < lam i}

theorem positiveChamber_subset_positiveOrderedSpectrum (p : ℕ) :
    positiveChamber p ⊆ positiveOrderedSpectrum p :=
  fun _ h => ⟨h.1.monotone, h.2⟩

theorem ascendingSpectrum_mem_positiveOrderedSpectrum {p : ℕ}
    (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    ascendingSpectrum S ∈ positiveOrderedSpectrum p := by
  refine ⟨monotone_ascendingSpectrum S, fun i => ?_⟩
  simpa only [ascendingSpectrum, coordinateSpectrum, Function.comp_apply] using
    hS.eigenvalues_pos (ascendingIndexEquiv p i)

/-- Every ordered eigenvalue is increasing in Loewner order.  This is derived
from the proved Courant--Fischer comparison of quadratic forms. -/
theorem ascendingSpectrum_mono_of_posSemidef {p : ℕ} (S T : Sym p)
    (hST : ((T : Matrix (Fin p) (Fin p) ℝ) - S).PosSemidef) :
    ascendingSpectrum S ≤ ascendingSpectrum T := by
  intro i
  rw [ascendingSpectrum_eq_eigenvalues₀, ascendingSpectrum_eq_eigenvalues₀]
  simp only [Matrix.IsHermitian.eigenvalues₀]
  apply LinearMap.IsSymmetric.eigenvalue_mono
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (selfAdjoint.isHermitian_coe S))
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (selfAdjoint.isHermitian_coe T))
    finrank_euclideanSpace
  intro x
  have h := hST.dotProduct_mulVec_nonneg (fun j => x j)
  simp only [Matrix.sub_mulVec, dotProduct_sub, star_trivial] at h
  change (fun j => x j) ⬝ᵥ ((S : Matrix (Fin p) (Fin p) ℝ) *ᵥ fun j => x j) ≤
    (fun j => x j) ⬝ᵥ ((T : Matrix (Fin p) (Fin p) ℝ) *ᵥ fun j => x j)
  exact sub_nonneg.mp h

theorem orthonormalRows_vecMul_injective {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (hC : C * Cᵀ = 1) :
    Function.Injective C.vecMul := by
  intro x y hxy
  have h := congrArg (fun z => z ᵥ* Cᵀ) hxy
  simpa only [Matrix.vecMul_vecMul, hC, Matrix.vecMul_one] using h

def compressionSpectralTest {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (Φ : (Fin k → ℝ) → ℝ) (X : Sym p) : ℝ :=
  Φ (ascendingSpectrum (Matrix.symmetricCongruenceLinearMap C X))

@[fun_prop] theorem measurable_compressionSpectralTest {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (Φ : (Fin k → ℝ) → ℝ) (hΦ : Measurable Φ) :
    Measurable (compressionSpectralTest C Φ) :=
  hΦ.comp ((continuous_ascendingSpectrum k).measurable.comp
    (LinearMap.continuous_of_finiteDimensional _).measurable)

theorem compression_posDef_of_orthonormalRows {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (hC : C * Cᵀ = 1)
    (X : Sym p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    ((Matrix.symmetricCongruenceLinearMap C X : Sym k) : Matrix (Fin k) (Fin k) ℝ).PosDef := by
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    hX.mul_mul_conjTranspose_same (orthonormalRows_vecMul_injective C hC)

theorem compression_difference_posSemidef {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (X Y : Sym p)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    (((Matrix.symmetricCongruenceLinearMap C Y : Sym k) : Matrix (Fin k) (Fin k) ℝ) -
      (Matrix.symmetricCongruenceLinearMap C X : Matrix (Fin k) (Fin k) ℝ)).PosSemidef := by
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul] using
    hXY.mul_mul_conjTranspose_same C

theorem compressionSpectralTest_mono {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (hC : C * Cᵀ = 1)
    (Φ : (Fin k → ℝ) → ℝ) (hΦ : MonotoneOn Φ (positiveOrderedSpectrum k))
    (X Y : Sym p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef)
    (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    compressionSpectralTest C Φ X ≤ compressionSpectralTest C Φ Y := by
  apply hΦ
  · exact ascendingSpectrum_mem_positiveOrderedSpectrum _
      (compression_posDef_of_orthonormalRows C hC X hX)
  · exact ascendingSpectrum_mem_positiveOrderedSpectrum _
      (compression_posDef_of_orthonormalRows C hC Y hY)
  · exact ascendingSpectrum_mono_of_posSemidef _ _
      (compression_difference_posSemidef C X Y hXY)

theorem compressionSpectralTest_antitone {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (hC : C * Cᵀ = 1)
    (Φ : (Fin k → ℝ) → ℝ) (hΦ : AntitoneOn Φ (positiveOrderedSpectrum k))
    (X Y : Sym p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef)
    (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    compressionSpectralTest C Φ Y ≤ compressionSpectralTest C Φ X := by
  apply hΦ
  · exact ascendingSpectrum_mem_positiveOrderedSpectrum _
      (compression_posDef_of_orthonormalRows C hC X hX)
  · exact ascendingSpectrum_mem_positiveOrderedSpectrum _
      (compression_posDef_of_orthonormalRows C hC Y hY)
  · exact ascendingSpectrum_mono_of_posSemidef _ _
      (compression_difference_posSemidef C X Y hXY)

end Wishart.Spectral
end
end CanonicalSource5

section CanonicalSource6
/- Source: Wishart/InverseSpectralRegression.lean -/



/-!
# Actual spectral regression and bounded conditional tests

All averages in this file are integrals over the displayed independent Haar
and Gaussian/Wishart source.  Bounded tests are used here so that conditional
integrability holds at every positive chamber point.  The later monotone-limit
step removes boundedness; no conditional finiteness assumption is retained in
Theorem 6.1.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

open Spectral

def LoewnerIncreasing {p : ℕ} (g : SymmetricMatrix p → ℝ) : Prop :=
  ∀ X Y : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosDef →
    (Y : Matrix (Fin p) (Fin p) ℝ).PosDef →
    ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef → g X ≤ g Y

def LoewnerDecreasing {p : ℕ} (g : SymmetricMatrix p → ℝ) : Prop :=
  ∀ X Y : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosDef →
    (Y : Matrix (Fin p) (Fin p) ℝ).PosDef →
    ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef → g Y ≤ g X

def inverseFrameNoiseMeasure (β : ℝ) (q m : ℕ) :
    Measure (Orth q × InverseRegressionNoise q m) :=
  (haarProb (Orth q)).prod (inverseRegressionNoiseMeasure β q m)

theorem inverseFrameNoiseMeasure_isProbability {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    IsProbabilityMeasure (inverseFrameNoiseMeasure β q m) := by
  letI := inverseRegressionNoiseMeasure_isProbability hβ
  unfold inverseFrameNoiseMeasure
  infer_instance

def inverseSpectralRegressionSource (β : ℝ) (q m : ℕ) :
    Measure ((Fin q → ℝ) × (Orth q × InverseRegressionNoise q m)) :=
  (normalizedWeight volume (wishartEigenDensity q (β - m))).prod
    (inverseFrameNoiseMeasure β q m)

def inverseSpectralDataTransform {q m : ℕ}
    (z : (Fin q → ℝ) × (Orth q × InverseRegressionNoise q m)) :
    SymmetricMatrix q × InverseRegressionNoise q m :=
  (inverseSpectralMatrix z.1 z.2.1, z.2.2)

@[fun_prop] theorem measurable_inverseSpectralDataTransform {q m : ℕ} :
    Measurable (@inverseSpectralDataTransform q m) := by
  unfold inverseSpectralDataTransform
  exact (measurable_inverseSpectralMatrix.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)

theorem measurePreserving_inverseSpectralDataTransform {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    MeasurePreserving inverseSpectralDataTransform
      (inverseSpectralRegressionSource β q m) (inverseRegressionSource β q m) := by
  have hq : (q : ℝ) - 1 < β - m := by
    push_cast at hβ
    linarith
  letI := laguerreLaw_isProbability hq
  letI := inverseRegressionNoiseMeasure_isProbability hβ
  have hspec : MeasurePreserving
      (fun z : (Fin q → ℝ) × Orth q => inverseSpectralMatrix z.1 z.2)
      ((normalizedWeight volume (wishartEigenDensity q (β - m))).prod
        (haarProb (Orth q)))
      (inverseWishartMeasure (β - m) (1 : Matrix (Fin q) (Fin q) ℝ)) :=
    ⟨measurable_inverseSpectralMatrix, inverseWishart_laguerre_haar_representation hq⟩
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc
      (normalizedWeight volume (wishartEigenDensity q (β - m)))
      (haarProb (Orth q)) (inverseRegressionNoiseMeasure β q m))
  exact (hspec.prod (MeasurePreserving.id _)).comp hassoc

def inverseSpectralRegressionMatrix {q m : ℕ}
    (z : (Fin q → ℝ) × (Orth q × InverseRegressionNoise q m)) : SymmetricMatrix (q + m) :=
  inverseRegressionReconstruction (inverseSpectralDataTransform z)

@[fun_prop] theorem measurable_inverseSpectralRegressionMatrix {q m : ℕ} :
    Measurable (@inverseSpectralRegressionMatrix q m) :=
  measurable_inverseRegressionReconstruction.comp measurable_inverseSpectralDataTransform

theorem map_inverseSpectralRegressionMatrix {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β) :
    (inverseSpectralRegressionSource β q m).map inverseSpectralRegressionMatrix =
      inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  change (inverseSpectralRegressionSource β q m).map
    (inverseRegressionReconstruction ∘ inverseSpectralDataTransform) = _
  rw [← Measure.map_map measurable_inverseRegressionReconstruction
      measurable_inverseSpectralDataTransform,
    (measurePreserving_inverseSpectralDataTransform hβ).map_eq,
    map_inverseRegressionReconstruction hβ]

theorem inverseSpectralRegressionMatrix_selected {q m : ℕ}
    (z : (Fin q → ℝ) × (Orth q × InverseRegressionNoise q m)) :
    principalSymmetricBlock (Fin.castAdd m) (inverseSpectralRegressionMatrix z) =
      inverseSpectralMatrix z.1 z.2.1 :=
  inverseRegressionReconstruction_selected _

theorem ae_inverseFrameNoise_posDef (β : ℝ) (q m : ℕ) :
    ∀ᵐ u ∂inverseFrameNoiseMeasure β q m,
      (u.2.1 : Matrix (Fin m) (Fin m) ℝ).PosDef :=
  Measure.quasiMeasurePreserving_snd.ae
    (Measure.quasiMeasurePreserving_fst.ae
      (ae_posDef_nonsingularWishartMeasure β (1 : Matrix (Fin m) (Fin m) ℝ)))

theorem inverseSpectralRegressionMatrix_posDef {q m : ℕ}
    (lam : Fin q → ℝ) (u : Orth q × InverseRegressionNoise q m)
    (hlam : lam ∈ positiveChamber q)
    (hu : (u.2.1 : Matrix (Fin m) (Fin m) ℝ).PosDef) :
    (inverseSpectralRegressionMatrix (lam, u) :
      Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosDef := by
  apply inverseRegressionAffine_posDef
    (inverseSpectralMatrix_posDef lam u.1 hlam)
  simpa only [inverseSpectralDataTransform, coe_symmetricInv] using hu.inv

theorem inverseSpectralRegressionMatrix_antitone {q m : ℕ}
    (x y : Fin q → ℝ) (u : Orth q × InverseRegressionNoise q m)
    (hx : x ∈ positiveChamber q) (hy : y ∈ positiveChamber q) (hxy : x ≤ y) :
    (((inverseSpectralRegressionMatrix (x, u) : SymmetricMatrix (q + m)) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ) -
      (inverseSpectralRegressionMatrix (y, u) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ)).PosSemidef :=
  inverseRegressionReconstruction_mono u.2 _ _
    (inverseSpectralMatrix_antitone x y u.1 hx hy hxy)

def inverseSpectralAverage {q m : ℕ} (β : ℝ) (g : SymmetricMatrix (q + m) → ℝ) :
    (Fin q → ℝ) → ℝ :=
  parameterAverageOn (inverseFrameNoiseMeasure β q m) (positiveChamber q)
    (fun z => g (inverseSpectralRegressionMatrix z))

@[fun_prop] theorem measurable_inverseSpectralAverage {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    Measurable (inverseSpectralAverage β g) := by
  letI := inverseFrameNoiseMeasure_isProbability hβ
  exact parameterAverageOn_measurable _ _ (orderedChamber_measurable _ measurableSet_Ioi)
    _ (hg.comp measurable_inverseSpectralRegressionMatrix)

theorem inverseSpectralAverage_nonneg {q m : ℕ} (β : ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : ∀ X, 0 ≤ g X) (lam : Fin q → ℝ) :
    0 ≤ inverseSpectralAverage β g lam :=
  parameterAverageOn_nonneg _ _ _ (fun _ _ _ => hg _) lam

theorem inverseSpectralAverage_le {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g)
    (hg0 : ∀ X, 0 ≤ g X) {N : ℝ} (hN : 0 ≤ N) (hgN : ∀ X, g X ≤ N)
    (lam : Fin q → ℝ) : inverseSpectralAverage β g lam ≤ N := by
  letI := inverseFrameNoiseMeasure_isProbability hβ
  by_cases hlam : lam ∈ positiveChamber q
  · rw [inverseSpectralAverage, parameterAverageOn_of_mem _ _ _ hlam]
    have hgi := integrable_of_nonneg_bounded (inverseFrameNoiseMeasure β q m)
      (fun u => g (inverseSpectralRegressionMatrix (lam, u))) N
      ((hg.comp measurable_inverseSpectralRegressionMatrix).comp measurable_prodMk_left)
      (fun _ => hg0 _) (fun _ => hgN _)
    simpa only [parameterAverage, integral_const, probReal_univ, one_smul] using
      integral_mono hgi (integrable_const N) (fun u => hgN _)
  · simpa only [inverseSpectralAverage, parameterAverageOn_of_not_mem _ _ _ hlam] using hN

theorem inverseSpectralAverage_antitone_of_increasing {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g)
    (hg0 : ∀ X, 0 ≤ g X) {N : ℝ} (hgN : ∀ X, g X ≤ N)
    (hmono : LoewnerIncreasing g) :
    AntitoneOn (inverseSpectralAverage β g) (positiveChamber q) := by
  letI := inverseFrameNoiseMeasure_isProbability hβ
  intro x hx y hy hxy
  rw [inverseSpectralAverage, parameterAverageOn_of_mem _ _ _ hx,
    parameterAverageOn_of_mem _ _ _ hy]
  apply integral_mono_ae
  · exact integrable_of_nonneg_bounded _ _ N
      ((hg.comp measurable_inverseSpectralRegressionMatrix).comp measurable_prodMk_left)
      (fun _ => hg0 _) (fun _ => hgN _)
  · exact integrable_of_nonneg_bounded _ _ N
      ((hg.comp measurable_inverseSpectralRegressionMatrix).comp measurable_prodMk_left)
      (fun _ => hg0 _) (fun _ => hgN _)
  · filter_upwards [ae_inverseFrameNoise_posDef β q m] with u hu
    exact hmono _ _ (inverseSpectralRegressionMatrix_posDef y u hy hu)
      (inverseSpectralRegressionMatrix_posDef x u hx hu)
      (inverseSpectralRegressionMatrix_antitone x y u hx hy hxy)

theorem inverseSpectralAverage_monotone_of_decreasing {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g)
    (hg0 : ∀ X, 0 ≤ g X) {N : ℝ} (hgN : ∀ X, g X ≤ N)
    (hmono : LoewnerDecreasing g) :
    MonotoneOn (inverseSpectralAverage β g) (positiveChamber q) := by
  letI := inverseFrameNoiseMeasure_isProbability hβ
  intro x hx y hy hxy
  rw [inverseSpectralAverage, parameterAverageOn_of_mem _ _ _ hx,
    parameterAverageOn_of_mem _ _ _ hy]
  apply integral_mono_ae
  · exact integrable_of_nonneg_bounded _ _ N
      ((hg.comp measurable_inverseSpectralRegressionMatrix).comp measurable_prodMk_left)
      (fun _ => hg0 _) (fun _ => hgN _)
  · exact integrable_of_nonneg_bounded _ _ N
      ((hg.comp measurable_inverseSpectralRegressionMatrix).comp measurable_prodMk_left)
      (fun _ => hg0 _) (fun _ => hgN _)
  · filter_upwards [ae_inverseFrameNoise_posDef β q m] with u hu
    exact hmono _ _ (inverseSpectralRegressionMatrix_posDef y u hy hu)
      (inverseSpectralRegressionMatrix_posDef x u hx hu)
      (inverseSpectralRegressionMatrix_antitone x y u hx hy hxy)

end Wishart
end
end CanonicalSource6

section CanonicalSource7
/- Source: Wishart/InverseBoundedAssociation.lean -/



/-!
# The selected inverse-Wishart split for bounded spectral tests

The conditional factor is the actual affine-regression average.  Both directions
of spectral monotonicity are covered.  All three moments are identified with
their original inverse-Wishart expectations before applying chamber association.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

open Spectral

def selectedSpectralTest {q m : ℕ} (Φ : (Fin q → ℝ) → ℝ)
    (X : SymmetricMatrix (q + m)) : ℝ :=
  Φ (ascendingSpectrum (principalSymmetricBlock (Fin.castAdd m) X))

@[fun_prop] theorem measurable_selectedSpectralTest {q m : ℕ}
    {Φ : (Fin q → ℝ) → ℝ} (hΦ : Measurable Φ) :
    Measurable (@selectedSpectralTest q m Φ) :=
  hΦ.comp ((continuous_ascendingSpectrum q).measurable.comp
    (measurable_principalSymmetricBlock _))

theorem inverse_bounded_spectral_moments {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    {Φ : (Fin q → ℝ) → ℝ} {g : SymmetricMatrix (q + m) → ℝ}
    (hΦ : Measurable Φ) (hg : Measurable g)
    (hΦ0 : ∀ x, 0 ≤ Φ x) (hg0 : ∀ X, 0 ≤ g X)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hΦM : ∀ x, Φ x ≤ M) (hgN : ∀ X, g X ≤ N) :
    (∫ X, g X ∂inverseWishartMeasure β
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) =
        ∫ lam, inverseSpectralAverage β g lam
          ∂normalizedWeight volume (wishartEigenDensity q (β - m)) ∧
    (∫ X, selectedSpectralTest Φ X ∂inverseWishartMeasure β
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) =
        ∫ lam, Φ (reciprocalReverse lam)
          ∂normalizedWeight volume (wishartEigenDensity q (β - m)) ∧
    (∫ X, selectedSpectralTest Φ X * g X ∂inverseWishartMeasure β
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) =
        ∫ lam, Φ (reciprocalReverse lam) * inverseSpectralAverage β g lam
          ∂normalizedWeight volume (wishartEigenDensity q (β - m)) := by
  have hq : (q : ℝ) - 1 < β - m := by
    push_cast at hβ
    linarith
  let μ := normalizedWeight volume (wishartEigenDensity q (β - m))
  let ν := inverseFrameNoiseMeasure β q m
  letI : IsProbabilityMeasure μ := laguerreLaw_isProbability hq
  letI : IsProbabilityMeasure ν := inverseFrameNoiseMeasure_isProbability hβ
  let H : (Fin q → ℝ) × (Orth q × InverseRegressionNoise q m) → ℝ :=
    fun z => g (inverseSpectralRegressionMatrix z)
  let f : (Fin q → ℝ) → ℝ := fun lam => Φ (reciprocalReverse lam)
  have hHm : Measurable H := hg.comp measurable_inverseSpectralRegressionMatrix
  have hfm : Measurable f := hΦ.comp measurable_reciprocalReverse
  have hHi : Integrable H (μ.prod ν) :=
    integrable_of_nonneg_bounded _ _ N hHm (fun _ => hg0 _) (fun _ => hgN _)
  have hfi : Integrable (fun z : (Fin q → ℝ) × (Orth q × InverseRegressionNoise q m) =>
      f z.1) (μ.prod ν) :=
    integrable_of_nonneg_bounded _ _ M (hfm.comp measurable_fst)
      (fun _ => hΦ0 _) (fun _ => hΦM _)
  have hfHi : Integrable (fun z => f z.1 * H z) (μ.prod ν) :=
    integrable_of_nonneg_bounded _ _ (M * N) ((hfm.comp measurable_fst).mul hHm)
      (fun _ => mul_nonneg (hΦ0 _) (hg0 _))
      (fun _ => mul_le_mul (hΦM _) (hgN _) (hg0 _) hM)
  have hchamber : ∀ᵐ lam ∂μ, lam ∈ positiveChamber q := ae_laguerreLaw_mem_chamber hq
  have hsel : (fun z : (Fin q → ℝ) × (Orth q × InverseRegressionNoise q m) =>
      selectedSpectralTest Φ (inverseSpectralRegressionMatrix z)) =ᵐ[μ.prod ν]
        (fun z => f z.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hchamber] with z hz
    rw [selectedSpectralTest, inverseSpectralRegressionMatrix_selected,
      ascendingSpectrum_inverseSpectralMatrix _ _ hz]
  have hmap := map_inverseSpectralRegressionMatrix hβ
  constructor
  · rw [← hmap, integral_map_of_stronglyMeasurable
      measurable_inverseSpectralRegressionMatrix hg.stronglyMeasurable]
    exact (integral_parameterAverageOn μ ν _ hchamber H hHi).symm
  constructor
  · rw [← hmap, integral_map_of_stronglyMeasurable
      measurable_inverseSpectralRegressionMatrix
      (measurable_selectedSpectralTest hΦ).stronglyMeasurable]
    change (∫ z, selectedSpectralTest Φ (inverseSpectralRegressionMatrix z)
      ∂μ.prod ν) = _
    rw [integral_congr_ae hsel]
    rw [integral_prod _ hfi]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  · have hprodmeas : Measurable (fun X : SymmetricMatrix (q + m) =>
        selectedSpectralTest Φ X * g X) :=
      (measurable_selectedSpectralTest hΦ).mul hg
    rw [← hmap, integral_map_of_stronglyMeasurable
      measurable_inverseSpectralRegressionMatrix
      hprodmeas.stronglyMeasurable]
    have hjoint : (fun z : (Fin q → ℝ) × (Orth q × InverseRegressionNoise q m) =>
        selectedSpectralTest Φ (inverseSpectralRegressionMatrix z) *
          g (inverseSpectralRegressionMatrix z)) =ᵐ[μ.prod ν]
            (fun z => f z.1 * H z) := hsel.mul (ae_of_all _ fun _ => rfl)
    change (∫ z, selectedSpectralTest Φ (inverseSpectralRegressionMatrix z) *
      g (inverseSpectralRegressionMatrix z) ∂μ.prod ν) = _
    rw [integral_congr_ae hjoint]
    exact (integral_mul_parameterAverageOn μ ν _ hchamber f H hfHi).symm

/-- The exact selected split for bounded nonnegative tests, in either common
direction.  There is no overlap, rank, or additional degree restriction. -/
theorem inverseWishart_selected_split_bounded {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    {Φ : (Fin q → ℝ) → ℝ} {g : SymmetricMatrix (q + m) → ℝ}
    (hΦ : Measurable Φ) (hg : Measurable g)
    (hΦ0 : ∀ x, 0 ≤ Φ x) (hg0 : ∀ X, 0 ≤ g X)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hΦM : ∀ x, Φ x ≤ M) (hgN : ∀ X, g X ≤ N)
    (hdir : (MonotoneOn Φ (positiveOrderedSpectrum q) ∧ LoewnerIncreasing g) ∨
      (AntitoneOn Φ (positiveOrderedSpectrum q) ∧ LoewnerDecreasing g)) :
    (∫ X, selectedSpectralTest Φ X ∂inverseWishartMeasure β
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, g X ∂inverseWishartMeasure β
        (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, selectedSpectralTest Φ X * g X ∂inverseWishartMeasure β
        (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have hq : (q : ℝ) - 1 < β - m := by
    push_cast at hβ
    linarith
  let μ := normalizedWeight volume (wishartEigenDensity q (β - m))
  letI : IsProbabilityMeasure μ := laguerreLaw_isProbability hq
  let f : (Fin q → ℝ) → ℝ := fun lam => Φ (reciprocalReverse lam)
  let F := inverseSpectralAverage β g
  have hfm : Measurable f := hΦ.comp measurable_reciprocalReverse
  have hFm : Measurable F := measurable_inverseSpectralAverage hβ hg
  have hf0 : ∀ x, 0 ≤ f x := fun _ => hΦ0 _
  have hF0 : ∀ x, 0 ≤ F x := inverseSpectralAverage_nonneg β hg0
  have hFbound : ∀ x, F x ≤ N := inverseSpectralAverage_le hβ hg hg0 hN hgN
  have hfi : Integrable f μ := integrable_of_nonneg_bounded _ _ M hfm hf0 (fun _ => hΦM _)
  have hFi : Integrable F μ := integrable_of_nonneg_bounded _ _ N hFm hF0 hFbound
  have hfFi : Integrable (fun x => f x * F x) μ :=
    integrable_of_nonneg_bounded _ _ (M * N) (hfm.mul hFm)
      (fun x => mul_nonneg (hf0 x) (hF0 x))
      (fun x => mul_le_mul (hΦM _) (hFbound x) (hF0 x) hM)
  obtain ⟨hZ0, hZtop, _⟩ := identityEigenLaw_normalized_density hq
  have hassoc : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (f x * F x) ∂μ := by
    rcases hdir with ⟨hφmono, hgmono⟩ | ⟨hφanti, hganti⟩
    · have hfa : AntitoneOn f (positiveChamber q) := by
        intro x hx y hy hxy
        exact hφmono
          (positiveChamber_subset_positiveOrderedSpectrum q (reciprocalReverse_mem_chamber hy))
          (positiveChamber_subset_positiveOrderedSpectrum q (reciprocalReverse_mem_chamber hx))
          (reciprocalReverse_antitoneOn hx hy hxy)
      exact lemma_2_1_antitone_association (Set.Ioi 0) measurableSet_Ioi
        (fun _ => laguerreWeight q (β - m)) 1 (by norm_num)
        (fun _ => measurable_laguerreWeight _ _) (fun _ => laguerreWeight_nonneg _ _)
        hZ0 hZtop f F hfm hFm hf0 hF0 hfa
        (inverseSpectralAverage_antitone_of_increasing hβ hg hg0 hgN hgmono)
    · have hfi' : MonotoneOn f (positiveChamber q) := by
        intro x hx y hy hxy
        exact hφanti
          (positiveChamber_subset_positiveOrderedSpectrum q (reciprocalReverse_mem_chamber hy))
          (positiveChamber_subset_positiveOrderedSpectrum q (reciprocalReverse_mem_chamber hx))
          (reciprocalReverse_antitoneOn hx hy hxy)
      exact lemma_2_1_association (Set.Ioi 0) measurableSet_Ioi
        (fun _ => laguerreWeight q (β - m)) 1 (by norm_num)
        (fun _ => measurable_laguerreWeight _ _) (fun _ => laguerreWeight_nonneg _ _)
        hZ0 hZtop f F hfm hFm hf0 hF0 hfi'
        (inverseSpectralAverage_monotone_of_decreasing hβ hg hg0 hgN hganti)
  have hreal := integral_mul_le_of_lintegral_mul_le μ f F hf0 hF0 hfi hFi hfFi hassoc
  obtain ⟨hremaining, hselected, hjoint⟩ :=
    inverse_bounded_spectral_moments hβ hΦ hg hΦ0 hg0 hM hN hΦM hgN
  rw [hselected, hremaining, hjoint]
  exact hreal

end Wishart
end
end CanonicalSource7

section CanonicalSource8
/- Source: Wishart/NonnegativeTruncation.lean -/



/-! # Bounded truncation and monotone convergence for nonnegative products -/

noncomputable section
open MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace WishartVerification

def nonnegativeTruncation {Ω : Type*} (n : ℕ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  min (f x) ((n : ℝ) + 1)

theorem nonnegativeTruncation_nonneg {Ω : Type*} (n : ℕ) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : Ω) : 0 ≤ nonnegativeTruncation n f x :=
  le_min (hf x) (by positivity)

theorem nonnegativeTruncation_mono_index {Ω : Type*} (f : Ω → ℝ) (x : Ω) :
    Monotone (fun n => nonnegativeTruncation n f x) := by
  intro n m hnm
  exact min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem nonnegativeTruncation_tendsto {Ω : Type*} (f : Ω → ℝ) (x : Ω) :
    Tendsto (fun n => nonnegativeTruncation n f x) atTop (𝓝 (f x)) := by
  have hev : ∀ᶠ n : ℕ in atTop, f x ≤ (n : ℝ) + 1 :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (f x))).mono fun n hn => hn.trans (by linarith)
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => (min_eq_left hn).symm)

theorem lintegral_association_of_truncated_integral_association
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hcap : ∀ n : ℕ,
      (∫ x, nonnegativeTruncation n f x ∂μ) *
        (∫ x, nonnegativeTruncation n g x ∂μ) ≤
      ∫ x, nonnegativeTruncation n f x * nonnegativeTruncation n g x ∂μ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ := by
  let A (n : ℕ) := ∫⁻ x, ENNReal.ofReal (nonnegativeTruncation n f x) ∂μ
  let B (n : ℕ) := ∫⁻ x, ENNReal.ofReal (nonnegativeTruncation n g x) ∂μ
  have hAsup := lintegral_ofReal_eq_iSup_of_monotone μ
    (fun n => nonnegativeTruncation n f) f (fun _ => hfm.min measurable_const)
    (nonnegativeTruncation_mono_index f) (nonnegativeTruncation_tendsto f)
  have hBsup := lintegral_ofReal_eq_iSup_of_monotone μ
    (fun n => nonnegativeTruncation n g) g (fun _ => hgm.min measurable_const)
    (nonnegativeTruncation_mono_index g) (nonnegativeTruncation_tendsto g)
  have hAn : Monotone A := fun n m hnm => lintegral_mono fun x =>
    ENNReal.ofReal_le_ofReal (nonnegativeTruncation_mono_index f x hnm)
  have hBn : Monotone B := fun n m hnm => lintegral_mono fun x =>
    ENNReal.ofReal_le_ofReal (nonnegativeTruncation_mono_index g x hnm)
  have hfinite (n : ℕ) : A n * B n ≤ ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ := by
    let M : ℝ := (n : ℝ) + 1
    have hM : 0 ≤ M := by positivity
    have hfn0 := nonnegativeTruncation_nonneg n f hf0
    have hgn0 := nonnegativeTruncation_nonneg n g hg0
    have hfnI := integrable_of_nonneg_bounded μ (nonnegativeTruncation n f) M
      (hfm.min measurable_const) hfn0 (fun _ => min_le_right _ _)
    have hgnI := integrable_of_nonneg_bounded μ (nonnegativeTruncation n g) M
      (hgm.min measurable_const) hgn0 (fun _ => min_le_right _ _)
    have hfgI := integrable_of_nonneg_bounded μ
      (fun x => nonnegativeTruncation n f x * nonnegativeTruncation n g x) (M * M)
      ((hfm.min measurable_const).mul (hgm.min measurable_const))
      (fun x => mul_nonneg (hfn0 x) (hgn0 x))
      (fun x => mul_le_mul (min_le_right _ _) (min_le_right _ _) (hgn0 x) hM)
    have hc : A n * B n ≤
        ∫⁻ x, ENNReal.ofReal (nonnegativeTruncation n f x * nonnegativeTruncation n g x) ∂μ := by
      dsimp [A, B]
      rw [← ofReal_integral_eq_lintegral_ofReal hfnI (ae_of_all _ hfn0),
        ← ofReal_integral_eq_lintegral_ofReal hgnI (ae_of_all _ hgn0),
        ← ofReal_integral_eq_lintegral_ofReal hfgI
          (ae_of_all _ fun x => mul_nonneg (hfn0 x) (hgn0 x)),
        ← ENNReal.ofReal_mul (integral_nonneg hfn0)]
      exact ENNReal.ofReal_le_ofReal (hcap n)
    exact hc.trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (mul_le_mul (min_le_left _ _) (min_le_left _ _) (hgn0 x) (hf0 x)))
  rw [hAsup, hBsup, ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply iSup_le
  intro n
  apply iSup_le
  intro m
  exact (mul_le_mul' (hAn (le_max_left n m)) (hBn (le_max_right n m))).trans
    (hfinite (max n m))

end WishartVerification
end
end CanonicalSource8

section CanonicalSource9
/- Source: Wishart/InverseTruncation.lean -/



/-!
# Removal of boundedness in inverse-Wishart association

The passage uses nonnegative extended integrals.  It therefore neither assumes
finite conditional expectations at every conditioning value nor loses cases
where a marginal or product expectation is infinite.  Finite real expectations
are recovered only after the extended inequality has been established.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification Filter
open scoped Classical ENNReal Topology MatrixOrder Matrix.Norms.L2Operator

noncomputable section



namespace Wishart

open Spectral

/-- Full nonnegative selected association.  All expectations are extended,
and there are no conditional finiteness or growth assumptions. -/
theorem inverseWishart_selected_split_lintegral {β : ℝ} {q m : ℕ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    {Φ : (Fin q → ℝ) → ℝ} {g : SymmetricMatrix (q + m) → ℝ}
    (hΦ : Measurable Φ) (hg : Measurable g)
    (hΦ0 : ∀ x, 0 ≤ Φ x) (hg0 : ∀ X, 0 ≤ g X)
    (hdir : (MonotoneOn Φ (positiveOrderedSpectrum q) ∧ LoewnerIncreasing g) ∨
      (AntitoneOn Φ (positiveOrderedSpectrum q) ∧ LoewnerDecreasing g)) :
    (∫⁻ X, ENNReal.ofReal (selectedSpectralTest Φ X) ∂inverseWishartMeasure β
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫⁻ X, ENNReal.ofReal (g X) ∂inverseWishartMeasure β
        (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫⁻ X, ENNReal.ofReal (selectedSpectralTest Φ X * g X) ∂inverseWishartMeasure β
        (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  letI := isProbabilityMeasure_inverseWishartMeasure
    (S := (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) Matrix.PosDef.one hβ
  apply lintegral_association_of_truncated_integral_association _
    (selectedSpectralTest Φ) g (measurable_selectedSpectralTest hΦ) hg
    (fun _ => hΦ0 _) hg0
  intro n
  let M : ℝ := (n : ℝ) + 1
  have hM : 0 ≤ M := by positivity
  have hcapdir :
      (MonotoneOn (nonnegativeTruncation n Φ) (positiveOrderedSpectrum q) ∧
        LoewnerIncreasing (nonnegativeTruncation n g)) ∨
      (AntitoneOn (nonnegativeTruncation n Φ) (positiveOrderedSpectrum q) ∧
        LoewnerDecreasing (nonnegativeTruncation n g)) := by
    rcases hdir with ⟨hp, hg'⟩ | ⟨hp, hg'⟩
    · exact Or.inl ⟨fun _ hx _ hy hxy => min_le_min_right _ (hp hx hy hxy),
        fun X Y hX hY hXY => min_le_min_right _ (hg' X Y hX hY hXY)⟩
    · exact Or.inr ⟨fun _ hx _ hy hxy => min_le_min_right _ (hp hx hy hxy),
        fun X Y hX hY hXY => min_le_min_right _ (hg' X Y hX hY hXY)⟩
  exact inverseWishart_selected_split_bounded hβ
    (hΦ.min measurable_const) (hg.min measurable_const)
    (nonnegativeTruncation_nonneg n Φ hΦ0) (nonnegativeTruncation_nonneg n g hg0)
    hM hM (fun _ => min_le_right _ _) (fun _ => min_le_right _ _) hcapdir

end Wishart
end
end CanonicalSource9

section CanonicalSource10
/- Source: Wishart/InverseCompressionAssembly.lean -/



/-!
# Arbitrary inverse-Wishart compressions

Each factor is the literal function of the ordered eigenvalues of
`(sqrt (Bᵀ Ω B))⁻¹ (Bᵀ Y B) (sqrt (Bᵀ Ω B))⁻¹`.
The chosen selected compression is normalized by an invertible ambient
congruence. Every other compression remains an arbitrary orthonormal row map;
overlap is unrestricted. Extended selected splits are proved without any
moment assumptions.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

open Spectral

def inverseCompressionFactor {p k : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ)
    (Φ : (Fin k → ℝ) → ℝ) (X : SymmetricMatrix p) : ℝ :=
  Φ (ascendingSpectrum (normalizedCompression Omega B X))

def inverseCompressionProduct {p d : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) (J : Finset (Fin d))
    (X : SymmetricMatrix p) : ℝ :=
  ∏ i ∈ J, inverseCompressionFactor Omega (B i) (Φ i) X

def inverseCompressionMoment {p d : ℕ} (β : ℝ)
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) (J : Finset (Fin d)) : ℝ :=
  ∫ X, inverseCompressionProduct Omega k B Φ J X ∂inverseWishartMeasure β Omega

def inverseCompressionExtendedMoment {p d : ℕ} (β : ℝ)
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) (J : Finset (Fin d)) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (inverseCompressionProduct Omega k B Φ J X)
    ∂inverseWishartMeasure β Omega

def CommonSpectralMonotonicity {d : ℕ} (k : Fin d → ℕ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) : Prop :=
  (∀ i, MonotoneOn (Φ i) (positiveOrderedSpectrum (k i))) ∨
    (∀ i, AntitoneOn (Φ i) (positiveOrderedSpectrum (k i)))

@[fun_prop] theorem measurable_inverseCompressionFactor {p k : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ)
    {Φ : (Fin k → ℝ) → ℝ} (hΦ : Measurable Φ) :
    Measurable (inverseCompressionFactor Omega B Φ) :=
  hΦ.comp ((continuous_ascendingSpectrum k).measurable.comp
    (measurable_normalizedCompression Omega B))

@[fun_prop] theorem measurable_inverseCompressionProduct {p d : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    {Φ : ∀ i, (Fin (k i) → ℝ) → ℝ} (hΦ : ∀ i, Measurable (Φ i))
    (J : Finset (Fin d)) : Measurable (inverseCompressionProduct Omega k B Φ J) :=
  Finset.measurable_prod _ fun i _ => measurable_inverseCompressionFactor Omega (B i) (hΦ i)

theorem inverseCompressionProduct_nonneg {p d : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    {Φ : ∀ i, (Fin (k i) → ℝ) → ℝ} (hΦ : ∀ i x, 0 ≤ Φ i x)
    (J : Finset (Fin d)) (X : SymmetricMatrix p) :
    0 ≤ inverseCompressionProduct Omega k B Φ J X :=
  Finset.prod_nonneg fun i _ => hΦ i _

@[simp] theorem inverseCompressionProduct_singleton {p d : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) (j : Fin d) (X : SymmetricMatrix p) :
    inverseCompressionProduct Omega k B Φ {j} X =
      inverseCompressionFactor Omega (B j) (Φ j) X := by
  simp [inverseCompressionProduct]

theorem inverseCompressionProduct_split {p d : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) (J : Finset (Fin d)) (j : Fin d)
    (hj : j ∈ J) (X : SymmetricMatrix p) :
    inverseCompressionProduct Omega k B Φ J X =
      inverseCompressionFactor Omega (B j) (Φ j) X *
        inverseCompressionProduct Omega k B Φ (J.erase j) X :=
  (Finset.mul_prod_erase J (fun i => inverseCompressionFactor Omega (B i) (Φ i) X) hj).symm

theorem map_symmetricCongruenceLinearMap_inverseWishartMeasure_of_det_ne_zero
    {p : ℕ} (β : ℝ) (Omega : Matrix (Fin p) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.det ≠ 0) :
    (inverseWishartMeasure β Omega).map (Matrix.symmetricCongruenceLinearMap A) =
      inverseWishartMeasure β (A * Omega * Aᵀ) := by
  let U : Matrix.GeneralLinearGroup (Fin p) ℝ := Matrix.nonsingInvUnit A hA.isUnit
  have hcoe : (U : Matrix (Fin p) (Fin p) ℝ) = A := rfl
  have hfun : (Matrix.GeneralLinearGroup.symmetricCongruence U :
      SymmetricMatrix p → SymmetricMatrix p) = Matrix.symmetricCongruenceLinearMap A := by
    funext X
    apply Subtype.ext
    rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply,
      Matrix.coe_symmetricCongruenceLinearMap_apply, hcoe]
  simpa only [hfun, hcoe] using map_symmetricCongruence_inverseWishartMeasure β Omega U

theorem map_inverseCompressionNormalization {p q : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} {B : Matrix (Fin p) (Fin q) ℝ}
    (N : CompressionNormalization Omega B) :
    (inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ)).map
      (Matrix.symmetricCongruenceLinearMap N.ambient) = inverseWishartMeasure β Omega := by
  rw [map_symmetricCongruenceLinearMap_inverseWishartMeasure_of_det_ne_zero β 1
    N.ambient N.det_ambient_ne_zero, Matrix.mul_one, N.ambient_gram]

theorem inverseCompressionFactor_ambient {p k : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ)
    (Φ : (Fin k → ℝ) → ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (Y : SymmetricMatrix p) :
    inverseCompressionFactor Omega B Φ (Matrix.symmetricCongruenceLinearMap A Y) =
      compressionSpectralTest (normalizedCompressionRows Omega B * A) Φ Y := by
  unfold inverseCompressionFactor normalizedCompression compressionSpectralTest
  rw [Matrix.symmetricCongruenceLinearMap_mul, LinearMap.comp_apply]

/-- Every selected subproduct split for arbitrary full-column-rank, possibly
overlapping compressions.  This extended-integral version has no finite-moment
assumptions at all. -/
theorem inverseCompression_selected_split_lintegral {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hΦm : ∀ i, Measurable (Φ i)) (hΦ0 : ∀ i x, 0 ≤ Φ i x)
    (hdir : CommonSpectralMonotonicity k Φ)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    inverseCompressionExtendedMoment β Omega k B Φ {j} *
      inverseCompressionExtendedMoment β Omega k B Φ (J.erase j) ≤
        inverseCompressionExtendedMoment β Omega k B Φ J := by
  have hqp : k j ≤ p := by rw [← hB j]; exact (B j).rank_le_height
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  let N := compressionNormalization hOmega (B j) (hB j)
  let C (i : Fin d) := normalizedCompressionRows Omega (B i) * N.ambient
  have hC (i : Fin d) : C i * (C i)ᵀ = 1 :=
    normalizedCompressionRows_ambient_gram hOmega (B i) (hB i) N.ambient N.ambient_gram
  let g : SymmetricMatrix (k j + m) → ℝ :=
    fun Y => ∏ i ∈ J.erase j, compressionSpectralTest (C i) (Φ i) Y
  have hgm : Measurable g := Finset.measurable_prod _ fun i _ =>
    measurable_compressionSpectralTest (C i) (Φ i) (hΦm i)
  have hg0 (Y) : 0 ≤ g Y := Finset.prod_nonneg fun i _ => hΦ0 i _
  have hselected (Y : SymmetricMatrix (k j + m)) :
      inverseCompressionFactor Omega (B j) (Φ j)
        (Matrix.symmetricCongruenceLinearMap N.ambient Y) = selectedSpectralTest (Φ j) Y := by
    unfold inverseCompressionFactor selectedSpectralTest
    rw [normalizedCompression_congruence_sum hOmega (B j) (hB j) N]
  have hremaining (Y : SymmetricMatrix (k j + m)) :
      inverseCompressionProduct Omega k B Φ (J.erase j)
        (Matrix.symmetricCongruenceLinearMap N.ambient Y) = g Y := by
    unfold inverseCompressionProduct g
    apply Finset.prod_congr rfl
    intro i hi
    exact inverseCompressionFactor_ambient Omega (B i) (Φ i) N.ambient Y
  have hjoint (Y : SymmetricMatrix (k j + m)) :
      inverseCompressionProduct Omega k B Φ J
        (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
        selectedSpectralTest (Φ j) Y * g Y := by
    rw [inverseCompressionProduct_split _ _ _ _ J j hj, hselected, hremaining]
  have hdir' : (MonotoneOn (Φ j) (positiveOrderedSpectrum (k j)) ∧ LoewnerIncreasing g) ∨
      (AntitoneOn (Φ j) (positiveOrderedSpectrum (k j)) ∧ LoewnerDecreasing g) := by
    rcases hdir with hinc | hdec
    · refine Or.inl ⟨hinc j, ?_⟩
      intro X Y hX hY hXY
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hΦ0 i _
      · intro i hi
        exact compressionSpectralTest_mono (C i) (hC i) (Φ i) (hinc i) X Y hX hY hXY
    · refine Or.inr ⟨hdec j, ?_⟩
      intro X Y hX hY hXY
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hΦ0 i _
      · intro i hi
        exact compressionSpectralTest_antitone (C i) (hC i) (Φ i) (hdec i) X Y hX hY hXY
  have hsplit := inverseWishart_selected_split_lintegral hβ (hΦm j) hgm (hΦ0 j) hg0 hdir'
  have hAmeas : Measurable (Matrix.symmetricCongruenceLinearMap N.ambient) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  unfold inverseCompressionExtendedMoment
  rw [← map_inverseCompressionNormalization β N]
  rw [lintegral_map ((measurable_inverseCompressionProduct Omega k B hΦm {j}).ennreal_ofReal)
      hAmeas,
    lintegral_map ((measurable_inverseCompressionProduct Omega k B hΦm (J.erase j)).ennreal_ofReal)
      hAmeas,
    lintegral_map ((measurable_inverseCompressionProduct Omega k B hΦm J).ennreal_ofReal) hAmeas]
  simp only [inverseCompressionProduct_singleton, hselected, hremaining, hjoint]
  exact hsplit

end Wishart
end
end CanonicalSource10

section CanonicalSource11
/- Source: Wishart/InverseTheorem.lean -/



/-!
# Theorem 6.1: the complete inverse-Wishart spectral inequalities

The extended version has no moment hypotheses.  The real-expectation version
requires exactly the displayed joint moment, the displayed complementary
moments, and the individual moments to be finite.  No integrability of other
subproducts or conditional moments is assumed.  All ranks, all overlaps, every
real admissible degree, and both common monotonicity directions are retained.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

open Spectral

theorem ennreal_product_singletons_le {ι : Type*} [DecidableEq ι]
    (M : Finset ι → ℝ≥0∞) (hempty : M ∅ = 1)
    (hsplit : ∀ J i, i ∈ J → M {i} * M (J.erase i) ≤ M J) (J : Finset ι) :
    (∏ i ∈ J, M {i}) ≤ M J := by
  induction J using Finset.induction_on with
  | empty => simp [hempty]
  | @insert i J hi ih =>
      rw [Finset.prod_insert hi]
      have hs := hsplit (insert i J) i (Finset.mem_insert_self i J)
      rw [Finset.erase_insert hi] at hs
      exact (mul_le_mul' le_rfl ih).trans hs

theorem inverseCompression_product_lintegral {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hΦm : ∀ i, Measurable (Φ i)) (hΦ0 : ∀ i x, 0 ≤ Φ i x)
    (hdir : CommonSpectralMonotonicity k Φ) (J : Finset (Fin d)) :
    (∏ i ∈ J, inverseCompressionExtendedMoment β Omega k B Φ {i}) ≤
      inverseCompressionExtendedMoment β Omega k B Φ J := by
  letI := isProbabilityMeasure_inverseWishartMeasure hOmega hβ
  apply ennreal_product_singletons_le
    (inverseCompressionExtendedMoment β Omega k B Φ)
  · simp [inverseCompressionExtendedMoment, inverseCompressionProduct]
  · exact inverseCompression_selected_split_lintegral hOmega hβ k B hB Φ hΦm hΦ0 hdir

theorem inverseCompressionExtendedMoment_eq_ofReal {p d : ℕ} (β : ℝ)
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) (hΦ0 : ∀ i x, 0 ≤ Φ i x)
    (J : Finset (Fin d))
    (hI : Integrable (inverseCompressionProduct Omega k B Φ J) (inverseWishartMeasure β Omega)) :
    inverseCompressionExtendedMoment β Omega k B Φ J =
      ENNReal.ofReal (inverseCompressionMoment β Omega k B Φ J) :=
  (ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ (inverseCompressionProduct_nonneg Omega k B hΦ0 J))).symm

theorem inverseCompressionMoment_nonneg {p d : ℕ} (β : ℝ)
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ) (hΦ0 : ∀ i x, 0 ≤ Φ i x)
    (J : Finset (Fin d)) : 0 ≤ inverseCompressionMoment β Omega k B Φ J :=
  integral_nonneg (inverseCompressionProduct_nonneg Omega k B hΦ0 J)

theorem inverseCompression_selected_split {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hΦm : ∀ i, Measurable (Φ i)) (hΦ0 : ∀ i x, 0 ≤ Φ i x)
    (hdir : CommonSpectralMonotonicity k Φ)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J)
    (hIsel : Integrable (inverseCompressionProduct Omega k B Φ {j})
      (inverseWishartMeasure β Omega))
    (hIrem : Integrable (inverseCompressionProduct Omega k B Φ (J.erase j))
      (inverseWishartMeasure β Omega))
    (hIall : Integrable (inverseCompressionProduct Omega k B Φ J)
      (inverseWishartMeasure β Omega)) :
    inverseCompressionMoment β Omega k B Φ {j} *
      inverseCompressionMoment β Omega k B Φ (J.erase j) ≤
        inverseCompressionMoment β Omega k B Φ J := by
  have h := inverseCompression_selected_split_lintegral hOmega hβ k B hB Φ hΦm hΦ0 hdir J j hj
  rw [inverseCompressionExtendedMoment_eq_ofReal β Omega k B Φ hΦ0 {j} hIsel,
    inverseCompressionExtendedMoment_eq_ofReal β Omega k B Φ hΦ0 (J.erase j) hIrem,
    inverseCompressionExtendedMoment_eq_ofReal β Omega k B Φ hΦ0 J hIall,
    ← ENNReal.ofReal_mul (inverseCompressionMoment_nonneg β Omega k B Φ hΦ0 {j})] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (inverseCompressionMoment_nonneg β Omega k B Φ hΦ0 J)).mp h

theorem inverseCompression_product {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hΦm : ∀ i, Measurable (Φ i)) (hΦ0 : ∀ i x, 0 ≤ Φ i x)
    (hdir : CommonSpectralMonotonicity k Φ) (J : Finset (Fin d))
    (hIsingle : ∀ i ∈ J, Integrable (inverseCompressionProduct Omega k B Φ {i})
      (inverseWishartMeasure β Omega))
    (hIall : Integrable (inverseCompressionProduct Omega k B Φ J)
      (inverseWishartMeasure β Omega)) :
    (∏ i ∈ J, inverseCompressionMoment β Omega k B Φ {i}) ≤
      inverseCompressionMoment β Omega k B Φ J := by
  have h := inverseCompression_product_lintegral hOmega hβ k B hB Φ hΦm hΦ0 hdir J
  rw [inverseCompressionExtendedMoment_eq_ofReal β Omega k B Φ hΦ0 J hIall] at h
  have hprod : (∏ i ∈ J, inverseCompressionExtendedMoment β Omega k B Φ {i}) =
      ENNReal.ofReal (∏ i ∈ J, inverseCompressionMoment β Omega k B Φ {i}) := by
    rw [ENNReal.ofReal_prod_of_nonneg
      (fun i _ => inverseCompressionMoment_nonneg β Omega k B Φ hΦ0 {i})]
    apply Finset.prod_congr rfl
    intro i hi
    exact inverseCompressionExtendedMoment_eq_ofReal β Omega k B Φ hΦ0 {i} (hIsingle i hi)
  rw [hprod] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (inverseCompressionMoment_nonneg β Omega k B Φ hΦ0 J)).mp h

/-- Exact statement of Theorem 6.1. `hIsingle`, `hIremaining`, and `hIjoint`
are precisely the finite real moments displayed in the manuscript's chain.
The underlying extended inequalities above have no integrability assumptions.
In particular no positive-power, disjointness, or rank-threshold restriction
has been introduced for the measurable spectral functions. -/
theorem theorem_6_1 {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (Φ : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hΦm : ∀ i, Measurable (Φ i)) (hΦ0 : ∀ i x, 0 ≤ Φ i x)
    (hdir : CommonSpectralMonotonicity k Φ)
    (hIsingle : ∀ i, Integrable (inverseCompressionFactor Omega (B i) (Φ i))
      (inverseWishartMeasure β Omega))
    (hIremaining : ∀ j, Integrable (inverseCompressionProduct Omega k B Φ (Finset.univ.erase j))
      (inverseWishartMeasure β Omega))
    (hIjoint : Integrable (inverseCompressionProduct Omega k B Φ Finset.univ)
      (inverseWishartMeasure β Omega)) :
    (∏ i, inverseCompressionMoment β Omega k B Φ {i}) ≤
      inverseCompressionMoment β Omega k B Φ Finset.univ ∧
    ∀ j : Fin d,
      (∏ i, inverseCompressionMoment β Omega k B Φ {i}) ≤
        inverseCompressionMoment β Omega k B Φ {j} *
          inverseCompressionMoment β Omega k B Φ (Finset.univ.erase j) ∧
      inverseCompressionMoment β Omega k B Φ {j} *
          inverseCompressionMoment β Omega k B Φ (Finset.univ.erase j) ≤
        inverseCompressionMoment β Omega k B Φ Finset.univ := by
  have hIsing (i : Fin d) : Integrable (inverseCompressionProduct Omega k B Φ {i})
      (inverseWishartMeasure β Omega) := by
    have hfun : inverseCompressionProduct Omega k B Φ {i} =
        inverseCompressionFactor Omega (B i) (Φ i) := by
      funext X
      exact inverseCompressionProduct_singleton Omega k B Φ i X
    rw [hfun]
    exact hIsingle i
  constructor
  · exact inverseCompression_product hOmega hβ k B hB Φ hΦm hΦ0 hdir Finset.univ
      (fun i _ => hIsing i) hIjoint
  intro j
  constructor
  · have hrem := inverseCompression_product hOmega hβ k B hB Φ hΦm hΦ0 hdir
      (Finset.univ.erase j) (fun i _ => hIsing i) (hIremaining j)
    have hmul := mul_le_mul_of_nonneg_left hrem
      (inverseCompressionMoment_nonneg β Omega k B Φ hΦ0 {j})
    rw [Finset.mul_prod_erase Finset.univ
      (fun i => inverseCompressionMoment β Omega k B Φ {i}) (Finset.mem_univ j)] at hmul
    exact hmul
  · exact inverseCompression_selected_split hOmega hβ k B hB Φ hΦm hΦ0 hdir
      Finset.univ j (Finset.mem_univ j) (hIsing j) (hIremaining j) hIjoint

end Wishart
end
end CanonicalSource11

section CanonicalSource12
/- Source: Wishart/SpectralDomainExtension.lean -/



/-!
# Tests defined only on the positive ordered spectrum

The inverse-Wishart comparison accepts a Borel function on the actual spectral
domain. Zero extension to the ambient coordinate space is measurable, preserves
both monotonicity directions on that domain, and agrees with the original test
at every positive-definite compression. All integral and integrability transfers
below use the proved positive-definite support of the actual inverse-Wishart law.
-/

noncomputable section
open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.Spectral

abbrev PositiveSpectrum (p : ℕ) := {lam : Fin p → ℝ // lam ∈ positiveOrderedSpectrum p}

theorem measurableSet_positiveOrderedSpectrum (p : ℕ) :
    MeasurableSet (positiveOrderedSpectrum p) := by
  have heq : positiveOrderedSpectrum p =
      (⋂ i : Fin p, ⋂ j : Fin p, ⋂ (_h : i ≤ j), {lam | lam i ≤ lam j}) ∩
        (⋂ i : Fin p, {lam | (0 : ℝ) < lam i}) := by
    ext lam
    simp only [positiveOrderedSpectrum, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter, Monotone]
  rw [heq]
  exact (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply i)
      (measurable_pi_apply j)).inter
    (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i))

def spectralZeroExtension {p : ℕ} {E : Type*} [Zero E]
    (f : PositiveSpectrum p → E) (lam : Fin p → ℝ) : E :=
  if h : lam ∈ positiveOrderedSpectrum p then f ⟨lam, h⟩ else 0

@[simp] theorem spectralZeroExtension_coe {p : ℕ} {E : Type*} [Zero E]
    (f : PositiveSpectrum p → E) (lam : PositiveSpectrum p) :
    spectralZeroExtension f lam.val = f lam := by
  simp only [spectralZeroExtension, dif_pos lam.property]

theorem spectralZeroExtension_of_mem {p : ℕ} {E : Type*} [Zero E]
    (f : PositiveSpectrum p → E) (lam : Fin p → ℝ)
    (hlam : lam ∈ positiveOrderedSpectrum p) :
    spectralZeroExtension f lam = f ⟨lam, hlam⟩ := by
  simp only [spectralZeroExtension, dif_pos hlam]

theorem measurable_spectralZeroExtension {p : ℕ} {E : Type*}
    [Zero E] [MeasurableSpace E] {f : PositiveSpectrum p → E} (hf : Measurable f) :
    Measurable (spectralZeroExtension f) :=
  hf.dite measurable_const (measurableSet_positiveOrderedSpectrum p)

theorem spectralZeroExtension_nonneg {p : ℕ} {E : Type*} [Zero E] [Preorder E]
    {f : PositiveSpectrum p → E} (hf : ∀ x, 0 ≤ f x) (lam : Fin p → ℝ) :
    0 ≤ spectralZeroExtension f lam := by
  unfold spectralZeroExtension
  split_ifs with h
  · exact hf ⟨lam, h⟩
  · exact le_rfl

theorem monotone_spectralZeroExtension_iff {p : ℕ} {E : Type*} [Zero E] [Preorder E]
    (f : PositiveSpectrum p → E) :
    MonotoneOn (spectralZeroExtension f) (positiveOrderedSpectrum p) ↔ Monotone f := by
  constructor
  · intro h x y hxy
    simpa only [spectralZeroExtension_coe] using h x.property y.property hxy
  · intro h x hx y hy hxy
    rw [spectralZeroExtension_of_mem f x hx, spectralZeroExtension_of_mem f y hy]
    exact h (show (⟨x, hx⟩ : PositiveSpectrum p) ≤ ⟨y, hy⟩ from hxy)

theorem antitone_spectralZeroExtension_iff {p : ℕ} {E : Type*} [Zero E] [Preorder E]
    (f : PositiveSpectrum p → E) :
    AntitoneOn (spectralZeroExtension f) (positiveOrderedSpectrum p) ↔ Antitone f := by
  constructor
  · intro h x y hxy
    simpa only [spectralZeroExtension_coe] using h x.property y.property hxy
  · intro h x hx y hy hxy
    rw [spectralZeroExtension_of_mem f x hx, spectralZeroExtension_of_mem f y hy]
    exact h (show (⟨x, hx⟩ : PositiveSpectrum p) ≤ ⟨y, hy⟩ from hxy)

theorem spectral_restriction_extension {p : ℕ} {E : Type*} [Zero E]
    (f : PositiveSpectrum p → E) :
    (fun lam : PositiveSpectrum p => spectralZeroExtension f lam.val) = f := by
  funext lam
  exact spectralZeroExtension_coe f lam

theorem spectral_extension_restriction_eqOn {p : ℕ} {E : Type*} [Zero E]
    (f : (Fin p → ℝ) → E) :
    Set.EqOn (spectralZeroExtension (fun lam : PositiveSpectrum p => f lam.val))
      f (positiveOrderedSpectrum p) := by
  intro lam hlam
  exact spectralZeroExtension_of_mem _ lam hlam

end Wishart.Spectral

namespace Wishart

open Spectral

/-- The original domain-valued test at an actual positive compression; its
arbitrary value off the positive matrix cone is fixed to zero. -/
def domainInverseCompressionFactor {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (f : PositiveSpectrum k → ℝ) (Y : SymmetricMatrix p) : ℝ :=
  if hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef then
    f ⟨ascendingSpectrum (normalizedCompression Omega B Y),
      ascendingSpectrum_mem_positiveOrderedSpectrum _ (normalizedCompression_posDef hOmega B hB hY)⟩
  else 0

theorem inverseCompressionFactor_zeroExtension_eq {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (f : PositiveSpectrum k → ℝ) (Y : SymmetricMatrix p)
    (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    inverseCompressionFactor Omega B (spectralZeroExtension f) Y =
      domainInverseCompressionFactor hOmega B hB f Y := by
  rw [domainInverseCompressionFactor, dif_pos hY]
  exact spectralZeroExtension_of_mem f _
    (ascendingSpectrum_mem_positiveOrderedSpectrum _ (normalizedCompression_posDef hOmega B hB hY))

theorem inverseCompressionFactor_zeroExtension_ae {p k : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (f : PositiveSpectrum k → ℝ) :
    inverseCompressionFactor Omega B (spectralZeroExtension f) =ᵐ[inverseWishartMeasure β Omega]
      domainInverseCompressionFactor hOmega B hB f := by
  filter_upwards [ae_posDef_inverseWishartMeasure β Omega] with Y hY
  exact inverseCompressionFactor_zeroExtension_eq hOmega B hB f Y hY

theorem aemeasurable_domainInverseCompressionFactor {p k : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    {f : PositiveSpectrum k → ℝ} (hf : Measurable f) :
    AEMeasurable (domainInverseCompressionFactor hOmega B hB f)
      (inverseWishartMeasure β Omega) :=
  (measurable_inverseCompressionFactor Omega B
    (measurable_spectralZeroExtension hf)).aemeasurable.congr
      (inverseCompressionFactor_zeroExtension_ae β hOmega B hB f)

def domainInverseCompressionProduct {p d : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : ∀ i, PositiveSpectrum (k i) → ℝ)
    (J : Finset (Fin d)) (Y : SymmetricMatrix p) : ℝ :=
  ∏ i ∈ J, domainInverseCompressionFactor hOmega (B i) (hB i) (f i) Y

theorem inverseCompressionProduct_zeroExtension_ae {p d : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : ∀ i, PositiveSpectrum (k i) → ℝ)
    (J : Finset (Fin d)) :
    inverseCompressionProduct Omega k B (fun i => spectralZeroExtension (f i)) J
      =ᵐ[inverseWishartMeasure β Omega] domainInverseCompressionProduct hOmega k B hB f J := by
  filter_upwards [ae_posDef_inverseWishartMeasure β Omega] with Y hY
  apply Finset.prod_congr rfl
  intro i hi
  exact inverseCompressionFactor_zeroExtension_eq hOmega (B i) (hB i) (f i) Y hY

theorem inverseCompressionProduct_zeroExtension_integrable_iff {p d : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : ∀ i, PositiveSpectrum (k i) → ℝ)
    (J : Finset (Fin d)) :
    Integrable (inverseCompressionProduct Omega k B (fun i => spectralZeroExtension (f i)) J)
        (inverseWishartMeasure β Omega) ↔
      Integrable (domainInverseCompressionProduct hOmega k B hB f J)
        (inverseWishartMeasure β Omega) :=
  integrable_congr (inverseCompressionProduct_zeroExtension_ae β hOmega k B hB f J)

theorem inverseCompressionProduct_zeroExtension_integral {p d : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : ∀ i, PositiveSpectrum (k i) → ℝ)
    (J : Finset (Fin d)) :
    inverseCompressionMoment β Omega k B (fun i => spectralZeroExtension (f i)) J =
      ∫ Y, domainInverseCompressionProduct hOmega k B hB f J Y ∂inverseWishartMeasure β Omega :=
  integral_congr_ae (inverseCompressionProduct_zeroExtension_ae β hOmega k B hB f J)

theorem inverseCompressionProduct_zeroExtension_lintegral {p d : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : ∀ i, PositiveSpectrum (k i) → ℝ)
    (J : Finset (Fin d)) :
    inverseCompressionExtendedMoment β Omega k B (fun i => spectralZeroExtension (f i)) J =
      ∫⁻ Y, ENNReal.ofReal (domainInverseCompressionProduct hOmega k B hB f J Y)
        ∂inverseWishartMeasure β Omega := by
  apply lintegral_congr_ae
  filter_upwards [inverseCompressionProduct_zeroExtension_ae β hOmega k B hB f J] with Y hY
  exact congrArg ENNReal.ofReal hY

/-- The full finite-expectation chain of Theorem6.1 for functions whose domain
is literally only the ordered positive spectrum. No extension hypothesis is
imposed on the user-supplied functions. -/
theorem theorem_6_1_on_positiveOrderedSpectrum {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (f : ∀ i, PositiveSpectrum (k i) → ℝ)
    (hfm : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hdir : (∀ i, Monotone (f i)) ∨ (∀ i, Antitone (f i)))
    (hIsingle : ∀ i, Integrable (domainInverseCompressionFactor hOmega (B i) (hB i) (f i))
      (inverseWishartMeasure β Omega))
    (hIremaining : ∀ j, Integrable
      (domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j))
      (inverseWishartMeasure β Omega))
    (hIjoint : Integrable (domainInverseCompressionProduct hOmega k B hB f Finset.univ)
      (inverseWishartMeasure β Omega)) :
    (∏ i, ∫ Y, domainInverseCompressionProduct hOmega k B hB f {i} Y
        ∂inverseWishartMeasure β Omega) ≤
      (∫ Y, domainInverseCompressionProduct hOmega k B hB f Finset.univ Y
        ∂inverseWishartMeasure β Omega) ∧
    ∀ j : Fin d,
      (∏ i, ∫ Y, domainInverseCompressionProduct hOmega k B hB f {i} Y
          ∂inverseWishartMeasure β Omega) ≤
        (∫ Y, domainInverseCompressionProduct hOmega k B hB f {j} Y
          ∂inverseWishartMeasure β Omega) *
        (∫ Y, domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j) Y
          ∂inverseWishartMeasure β Omega) ∧
      (∫ Y, domainInverseCompressionProduct hOmega k B hB f {j} Y
          ∂inverseWishartMeasure β Omega) *
        (∫ Y, domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j) Y
          ∂inverseWishartMeasure β Omega) ≤
        (∫ Y, domainInverseCompressionProduct hOmega k B hB f Finset.univ Y
          ∂inverseWishartMeasure β Omega) := by
  have hcommon : CommonSpectralMonotonicity k (fun i => spectralZeroExtension (f i)) := by
    rcases hdir with hinc | hdec
    · exact Or.inl fun i => (monotone_spectralZeroExtension_iff (f i)).2 (hinc i)
    · exact Or.inr fun i => (antitone_spectralZeroExtension_iff (f i)).2 (hdec i)
  have hsing (i : Fin d) : Integrable
      (inverseCompressionFactor Omega (B i) (spectralZeroExtension (f i)))
      (inverseWishartMeasure β Omega) :=
    (integrable_congr (inverseCompressionFactor_zeroExtension_ae β hOmega
      (B i) (hB i) (f i))).2 (hIsingle i)
  have hmain := theorem_6_1 hOmega hβ k B hB (fun i => spectralZeroExtension (f i))
    (fun i => measurable_spectralZeroExtension (hfm i))
    (fun i => spectralZeroExtension_nonneg (hf0 i)) hcommon hsing
    (fun j => (inverseCompressionProduct_zeroExtension_integrable_iff β hOmega k B hB f
      (Finset.univ.erase j)).2 (hIremaining j))
    ((inverseCompressionProduct_zeroExtension_integrable_iff β hOmega k B hB f
      Finset.univ).2 hIjoint)
  simpa only [inverseCompressionProduct_zeroExtension_integral β hOmega k B hB f] using hmain

end Wishart
end
end CanonicalSource12
