module

public import wishart.verified.real_remainder11

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder12/manifest.json. -/

@[expose] public section

section CanonicalSource110
/- Source: Wishart/SingularRegressionRows.lean -/



/-!
# Selected blocks and individual mean rows in singular spectral regression

These are pointwise identities for the actual source of
`map_singularSpectralRegressionModel`. They expose the selected positive
spectrum and the precise dependence of each data row on one eigenvalue.
-/

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open Wishart.Spectral
open scoped Classical ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

theorem rectangularDiagonalFactor_gram (n p : ℕ) (lam : Fin (min n p) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    (rectangularDiagonalFactor n p lam)ᵀ * rectangularDiagonalFactor n p lam =
      (initialRows (min_le_right n p))ᵀ * Matrix.diagonal lam *
        initialRows (min_le_right n p) := by
  let D : Matrix (Fin (min n p)) (Fin (min n p)) ℝ :=
    Matrix.diagonal (fun i => Real.sqrt (lam i))
  have hDD : D * D = Matrix.diagonal lam := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hlam i)
  unfold rectangularDiagonalFactor
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose]
  calc
    (initialRows (min_le_right n p))ᵀ *
        (D * initialRows (min_le_left n p)) *
          ((initialRows (min_le_left n p))ᵀ * D * initialRows (min_le_right n p)) =
        (initialRows (min_le_right n p))ᵀ * D *
          (initialRows (min_le_left n p) * (initialRows (min_le_left n p))ᵀ) * D *
            initialRows (min_le_right n p) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [initialRows_mul_transpose, Matrix.mul_one]
      rw [Matrix.mul_assoc _ D D, hDD]

theorem matrixGram_singularSpectralFactor (n q : ℕ) (lam : Fin (min n q) → ℝ)
    (O : Orth q) (hlam : ∀ i, 0 ≤ lam i) :
    matrixGram (singularSpectralFactor n q lam O) = positiveGramSpectralMatrix n q lam O := by
  apply Subtype.ext
  simp only [singularSpectralFactor, coe_matrixGram, Matrix.transpose_mul,
    Matrix.transpose_transpose, positiveGramSpectralMatrix, conjugate,
    Matrix.coe_symmetricCongruenceLinearMap_apply, coe_paddedSym, diagonalSym]
  calc
    (O : Matrix (Fin q) (Fin q) ℝ) * (rectangularDiagonalFactor n q lam)ᵀ *
        (rectangularDiagonalFactor n q lam * (O : Matrix (Fin q) (Fin q) ℝ)ᵀ) =
        (O : Matrix (Fin q) (Fin q) ℝ) *
          ((rectangularDiagonalFactor n q lam)ᵀ * rectangularDiagonalFactor n q lam) *
            (O : Matrix (Fin q) (Fin q) ℝ)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [rectangularDiagonalFactor_gram n q lam hlam]

theorem singularSpectralRegressionModel_selected {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (lam : Fin (min n q) → ℝ) (O : Orth q) (G : Matrix (Fin n) (Fin m) ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    regressionSelectedBlock (singularSpectralRegressionModel K C (lam, O, G)) =
      positiveGramSpectralMatrix n q lam O := by
  unfold singularSpectralRegressionModel
  rw [rawGaussianRegressionGram_selected, matrixGram_singularSpectralFactor n q lam O hlam]

theorem ae_singularSpectralRegressionModel_selected {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    ∀ᵐ z ∂singularRegressionSource n q m,
      regressionSelectedBlock (singularSpectralRegressionModel K C z) =
        positiveGramSpectralMatrix n q z.1 z.2.1 := by
  have hae := (measurePreserving_fst : MeasurePreserving Prod.fst
    (singularRegressionSource n q m) (positiveGramEigenLaw n q)).quasiMeasurePreserving.ae
      (ae_positiveGramEigenLaw_mem_chamber n q)
  filter_upwards [hae] with z hz
  exact singularSpectralRegressionModel_selected K C z.1 z.2.1 z.2.2 (fun i => (hz.2 i).le)

/-- The selected matrix and full matrix have their actual joint Gram law. -/
theorem map_singularSpectralRegressionJoint {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) :
    (singularRegressionSource n q m).map
      (fun z => (positiveGramSpectralMatrix n q z.1 z.2.1,
        singularSpectralRegressionModel K C z)) =
      (wishartGramMeasure n (regressionScale K C)).map
        (fun X => (regressionSelectedBlock X, X)) := by
  rw [← map_singularSpectralRegressionModel (n := n) K hC,
    Measure.map_map (by fun_prop) (measurable_singularSpectralRegressionModel K C)]
  apply Measure.map_congr
  filter_upwards [ae_singularSpectralRegressionModel_selected (n := n) K C] with z hz
  exact Prod.ext hz.symm rfl

theorem rawGaussianRegressionData_transpose {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin n) (Fin m) ℝ) :
    (rawGaussianRegressionData K C (A, G))ᵀ =
      regressionMeanInjection K * Aᵀ + regressionNoiseInjection q m * CFC.sqrt C * Gᵀ := by
  apply Matrix.submatrix_injective finSumFinEquiv.surjective Function.surjective_id
  dsimp only
  rw [← Matrix.transpose_submatrix, rawGaussianRegressionData_submatrix,
    Matrix.transpose_fromCols, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_mul, matrix_sqrt_transpose, Matrix.submatrix_add,
    Pi.add_apply, Pi.add_apply,
    Matrix.submatrix_mul _ _ finSumFinEquiv id id Function.bijective_id,
    Matrix.submatrix_mul _ _ finSumFinEquiv id id Function.bijective_id,
    Matrix.submatrix_mul _ _ finSumFinEquiv id id Function.bijective_id,
    regressionMeanInjection_submatrix, regressionNoiseInjection_submatrix]
  simp only [Matrix.submatrix_id_id, Matrix.fromRows_mul, Matrix.one_mul,
    Matrix.zero_mul, Matrix.mul_assoc]
  ext i j
  cases i <;> simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.add_apply, Matrix.zero_apply, add_zero]

def singularMeanMatrix (n : ℕ) {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Orth q) (lam : Fin (min n q) → ℝ) :
    Matrix (Fin (q + m)) (Fin n) ℝ :=
  regressionMeanInjection K * (singularSpectralFactor n q lam O)ᵀ

def singularNoiseFactor {q m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (q + m)) (Fin m) ℝ := regressionNoiseInjection q m * CFC.sqrt C

theorem singularMeanMatrix_eq (n : ℕ) {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Orth q) (lam : Fin (min n q) → ℝ) :
    singularMeanMatrix n K O lam =
      ((regressionMeanInjection K * (O : Matrix (Fin q) (Fin q) ℝ)).submatrix id
        (Fin.castLE (min_le_right n q))) *
          Matrix.diagonal (fun i => Real.sqrt (lam i)) * initialRows (min_le_left n q) := by
  unfold singularMeanMatrix singularSpectralFactor rectangularDiagonalFactor
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  have hsel := Matrix.mul_submatrix_one (Equiv.refl (Fin q))
    (Fin.castLE (min_le_right n q))
    (regressionMeanInjection K * (O : Matrix (Fin q) (Fin q) ℝ))
  have hrefl : (⇑(Equiv.refl (Fin q)).symm : Fin q → Fin q) = id := rfl
  simpa only [initialRows, Matrix.transpose_submatrix, Matrix.transpose_one,
    Equiv.coe_refl, hrefl, Function.id_comp, Matrix.mul_assoc] using
      congrArg (fun M => M * Matrix.diagonal (fun i => Real.sqrt (lam i)) *
        initialRows (min_le_left n q)) hsel

theorem mul_initialRows_apply {r n k : ℕ} (h : r ≤ n)
    (M : Matrix (Fin k) (Fin r) ℝ) (i : Fin k) (j : Fin n) :
    (M * initialRows h) i j = if hj : (j : ℕ) < r then M i ⟨j, hj⟩ else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : (j : ℕ) < r
  · rw [dif_pos hj]
    rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin r)]
    · simp only [initialRows, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
        show Fin.castLE h (⟨j, hj⟩ : Fin r) = j from Fin.ext rfl, ite_true, mul_one]
    · intro a ha hne
      have hne' : Fin.castLE h a ≠ j := by
        intro he
        apply hne
        exact Fin.ext (show (a : ℕ) = (j : ℕ) from congrArg Fin.val he)
      simp only [initialRows, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
        if_neg hne', mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [dif_neg hj]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : Fin.castLE h a ≠ j := by
      intro he
      apply hj
      simpa only [← congrArg Fin.val he, Fin.coe_castLE] using a.isLt
    simp only [initialRows, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
      if_neg hne, mul_zero]

def singularRegressionDirection (n : ℕ) {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Orth q) (a : Fin (min n q)) :
    EuclideanSpace ℝ (Fin (q + m)) :=
  WithLp.toLp 2 (fun i => (regressionMeanInjection K *
    (O : Matrix (Fin q) (Fin q) ℝ)) i (Fin.castLE (min_le_right n q) a))

/-- One positive eigenvalue changes exactly one mean row; all remaining rows
beyond the positive rank have zero mean. -/
theorem singularMeanMatrix_apply (n : ℕ) {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Orth q) (lam : Fin (min n q) → ℝ)
    (i : Fin (q + m)) (a : Fin n) :
    singularMeanMatrix n K O lam i a =
      if ha : (a : ℕ) < min n q then
        Real.sqrt (lam ⟨a, ha⟩) * singularRegressionDirection n K O ⟨a, ha⟩ i else 0 := by
  rw [singularMeanMatrix_eq, mul_initialRows_apply]
  split_ifs with ha
  · rw [Matrix.mul_diagonal]
    simp only [Matrix.submatrix_apply, id_eq, singularRegressionDirection, PiLp.toLp_apply,
      mul_comm]
  · rfl

theorem singularSpectralRegressionModel_eq_shiftedRows {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (lam : Fin (min n q) → ℝ) (O : Orth q) (G : Matrix (Fin n) (Fin m) ℝ) :
    singularSpectralRegressionModel K C (lam, O, G) =
      wishartGram (fun a : Fin n => WithLp.toLp 2 (fun i =>
        singularMeanMatrix n K O lam i a +
          (singularNoiseFactor C * Gᵀ) i a)) := by
  rw [singularSpectralRegressionModel, rawGaussianRegressionGram_eq_matrixGram,
    matrixGram_eq_wishartGram]
  congr 1
  funext a
  apply PiLp.ext
  intro i
  have h := congrArg (fun M : Matrix (Fin (q + m)) (Fin n) ℝ => M i a)
    (rawGaussianRegressionData_transpose K C (singularSpectralFactor n q lam O) G)
  exact h

theorem measurePreserving_gaussianMatrixRows_linear {n m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) :
    MeasurePreserving
      (fun G : Matrix (Fin n) (Fin m) ℝ => fun a : Fin n =>
        L.toEuclideanLin (WithLp.toLp 2 (G a)))
      (gaussianMatrixMeasure n m)
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 (L * Lᵀ)) := by
  have hstd : MeasurePreserving (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1)
      (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [PiLp.zero_apply] using
      (multivariateGaussian_one_eq_map_pi (0 : EuclideanSpace ℝ (Fin m))).symm
  have hL : MeasurePreserving L.toEuclideanLin
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1)
      (multivariateGaussian 0 (L * Lᵀ)) := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    simpa only [map_zero, add_zero, Matrix.mul_one] using
      map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        Matrix.PosSemidef.one L 0
  exact measurePreserving_pi _ _ (fun _ : Fin n => hL.comp hstd)

end Wishart
end
end CanonicalSource110

section CanonicalSource111
/- Source: Wishart/SingularRowGrouping.lean -/



/-!
# Grouping the zero mean rows into an independent Gram background

For each fixed selected eigenframe, the actual integer regression source is
exactly a family of `min n q` shifted Gaussian rows and an independent
`Gram(n - min n q)` background with the same (possibly singular) covariance.
No distributional or radial comparison hypothesis occurs in the bridge.
-/

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open Wishart.Spectral
open scoped Classical ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

def rowSplitIndex (n r : ℕ) (h : r ≤ n) : Fin r ⊕ Fin (n - r) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp] theorem rowSplitIndex_inl (n r : ℕ) (h : r ≤ n) (a : Fin r) :
    rowSplitIndex n r h (.inl a) = Fin.castLE h a := by
  apply Fin.ext
  rfl

@[simp] theorem rowSplitIndex_val_inr (n r : ℕ) (h : r ≤ n) (a : Fin (n - r)) :
    ((rowSplitIndex n r h (.inr a) : Fin n) : ℕ) = r + a := rfl

def splitRowsGramData {n r p : ℕ} (h : r ≤ n)
    (Z : Fin n → EuclideanSpace ℝ (Fin p)) : RegressionNoise r p :=
  (fun a => Z (Fin.castLE h a),
    wishartGram (fun a : Fin (n - r) => Z (rowSplitIndex n r h (.inr a))))

theorem measurePreserving_splitRowsGramData {n r p : ℕ} (h : r ≤ n)
    (C : Matrix (Fin p) (Fin p) ℝ) :
    MeasurePreserving (splitRowsGramData (p := p) h)
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 C)
      (gaussianResidualMeasure r C (wishartGramMeasure (n - r) C)) := by
  let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  have hindex := measurePreserving_piCongrLeft
    (fun _ : Fin n => γ) (rowSplitIndex n r h)
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin r ⊕ Fin (n - r) => γ)
  have hgram : MeasurePreserving (wishartGram (p := p) (ι := Fin (n - r)))
      (Measure.pi fun _ : Fin (n - r) => γ) (wishartGramMeasure (n - r) C) :=
    ⟨measurable_wishartGram, (wishartGramMeasure_eq_map_pi (n - r) C).symm⟩
  have hmap := ((MeasurePreserving.id (Measure.pi fun _ : Fin r => γ)).prod hgram).comp
    (hsplit.comp hindex.symm)
  change MeasurePreserving
    (fun Z : Fin n → EuclideanSpace ℝ (Fin p) =>
      ((fun a : Fin r => Z (rowSplitIndex n r h (.inl a))),
       wishartGram (fun a : Fin (n - r) => Z (rowSplitIndex n r h (.inr a)))))
    (Measure.pi fun _ : Fin n => γ)
    ((Measure.pi fun _ : Fin r => γ).prod (wishartGramMeasure (n - r) C)) at hmap
  change MeasurePreserving
    (fun Z : Fin n → EuclideanSpace ℝ (Fin p) =>
      ((fun a : Fin r => Z (Fin.castLE h a)),
       wishartGram (fun a : Fin (n - r) => Z (rowSplitIndex n r h (.inr a)))))
    (Measure.pi fun _ : Fin n => γ)
    ((Measure.pi fun _ : Fin r => γ).prod (wishartGramMeasure (n - r) C))
  simpa only [rowSplitIndex_inl] using hmap

theorem wishartGram_splitRows {n r p : ℕ} (h : r ≤ n)
    (Z : Fin n → EuclideanSpace ℝ (Fin p)) :
    wishartGram Z = wishartGram (fun a : Fin r => Z (Fin.castLE h a)) +
      wishartGram (fun a : Fin (n - r) => Z (rowSplitIndex n r h (.inr a))) := by
  apply Subtype.ext
  simp only [coe_wishartGram, Submodule.coe_add]
  rw [← Equiv.sum_comp (rowSplitIndex n r h)
    (fun a : Fin n => Matrix.vecMulVec (Z a).ofLp (Z a).ofLp), Fintype.sum_sum_type]
  simp only [rowSplitIndex_inl]

theorem wishartGram_shiftedRows {r p : ℕ}
    (v : Fin r → EuclideanSpace ℝ (Fin p)) (lam : Fin r → ℝ)
    (Z : Fin r → EuclideanSpace ℝ (Fin p)) :
    wishartGram (fun a => Z a + Real.sqrt (lam a) • v a) = rowBackground v lam Z := by
  apply Subtype.ext
  ext i j
  simp only [coe_wishartGram, coe_rowBackground, Matrix.sum_apply, Matrix.vecMulVec_apply,
    WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

def singularNoiseCovariance {q m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (q + m)) (Fin (q + m)) ℝ :=
  singularNoiseFactor (q := q) C * (singularNoiseFactor (q := q) C)ᵀ

theorem singularNoiseCovariance_posSemidef {q m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ) : (singularNoiseCovariance (q := q) C).PosSemidef := by
  simpa only [singularNoiseCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (singularNoiseFactor (q := q) C)

def singularGroupedNoiseData (n : ℕ) {q m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin m) ℝ) :
    RegressionNoise (min n q) (q + m) :=
  splitRowsGramData (min_le_left n q)
    (fun a => (singularNoiseFactor (q := q) C).toEuclideanLin (WithLp.toLp 2 (G a)))

theorem measurePreserving_singularGroupedNoiseData (n q : ℕ) {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ) :
    MeasurePreserving (singularGroupedNoiseData (q := q) n C)
      (gaussianMatrixMeasure n m)
      (gaussianResidualMeasure (min n q) (singularNoiseCovariance (q := q) C)
        (wishartGramMeasure (n - min n q) (singularNoiseCovariance (q := q) C))) :=
  (measurePreserving_splitRowsGramData (min_le_left n q)
    (singularNoiseCovariance (q := q) C)).comp
      (measurePreserving_gaussianMatrixRows_linear (n := n) (singularNoiseFactor (q := q) C))

/-- Pointwise grouping for every real eigenvalue parameter; positivity is
needed by the spectral law, but not by this algebraic identity. -/
theorem singularSpectralRegressionModel_eq_groupedRows {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (lam : Fin (min n q) → ℝ) (O : Orth q) (G : Matrix (Fin n) (Fin m) ℝ) :
    singularSpectralRegressionModel K C (lam, O, G) =
      shiftedRowsSym (singularRegressionDirection n K O) lam
        (singularGroupedNoiseData (q := q) n C G) := by
  let r := min n q
  let L := singularNoiseFactor (q := q) C
  let Z : Fin n → EuclideanSpace ℝ (Fin (q + m)) :=
    fun a => L.toEuclideanLin (WithLp.toLp 2 (G a))
  let Y : Fin n → EuclideanSpace ℝ (Fin (q + m)) :=
    fun a => WithLp.toLp 2 (fun i => singularMeanMatrix n K O lam i a + (L * Gᵀ) i a)
  have hnoise (a : Fin n) (i : Fin (q + m)) : Z a i = (L * Gᵀ) i a := by
    simp only [Z, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.transpose_apply, PiLp.toLp_apply]
  have hfirst : (fun a : Fin r => Y (Fin.castLE (min_le_left n q) a)) =
      fun a => Z (Fin.castLE (min_le_left n q) a) +
        Real.sqrt (lam a) • singularRegressionDirection n K O a := by
    funext a
    apply PiLp.ext
    intro i
    change singularMeanMatrix n K O lam i (Fin.castLE (min_le_left n q) a) +
      (L * Gᵀ) i (Fin.castLE (min_le_left n q) a) = _
    rw [singularMeanMatrix_apply]
    have ha : (a : ℕ) < min n q := a.isLt
    simp only [Fin.coe_castLE, dif_pos ha, Fin.eta, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, hnoise, add_comm]
  have htail : (fun a : Fin (n - r) => Y (rowSplitIndex n r (min_le_left n q) (.inr a))) =
      fun a => Z (rowSplitIndex n r (min_le_left n q) (.inr a)) := by
    funext a
    apply PiLp.ext
    intro i
    change singularMeanMatrix n K O lam i (rowSplitIndex n r (min_le_left n q) (.inr a)) +
      (L * Gᵀ) i (rowSplitIndex n r (min_le_left n q) (.inr a)) = _
    rw [singularMeanMatrix_apply]
    have hnot : ¬ ((rowSplitIndex n r (min_le_left n q) (.inr a) : Fin n) : ℕ) < min n q := by
      rw [rowSplitIndex_val_inr]
      exact not_lt.mpr (Nat.le_add_right _ _)
    rw [dif_neg hnot, zero_add, hnoise]
  rw [singularSpectralRegressionModel_eq_shiftedRows]
  change wishartGram Y = _
  rw [wishartGram_splitRows (min_le_left n q), hfirst, htail, wishartGram_shiftedRows]
  change rowBackground (singularRegressionDirection n K O) lam
      (fun a => Z (Fin.castLE (min_le_left n q) a)) +
      wishartGram (fun a : Fin (n - r) => Z (rowSplitIndex n r (min_le_left n q) (.inr a))) =
    wishartGram (fun a : Fin (n - r) => Z (rowSplitIndex n r (min_le_left n q) (.inr a))) +
      rowBackground (singularRegressionDirection n K O) lam
        (fun a => Z (Fin.castLE (min_le_left n q) a))
  exact add_comm _ _

/-- Exact fixed-frame distributional bridge to the Gaussian/Gram radial
source used by the integer Stein identity. -/
theorem map_singularSpectralRegressionModel_groupedNoise {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (lam : Fin (min n q) → ℝ) (O : Orth q) :
    (gaussianMatrixMeasure n m).map
      (fun G => singularSpectralRegressionModel K C (lam, O, G)) =
      (gaussianResidualMeasure (min n q) (singularNoiseCovariance (q := q) C)
        (wishartGramMeasure (n - min n q) (singularNoiseCovariance (q := q) C))).map
          (shiftedRowsSym (singularRegressionDirection n K O) lam) := by
  rw [← (measurePreserving_singularGroupedNoiseData n q C).map_eq,
    Measure.map_map (measurable_shiftedRowsSym _ _)
      (measurePreserving_singularGroupedNoiseData n q C).measurable]
  congr 1
  funext G
  exact singularSpectralRegressionModel_eq_groupedRows K C lam O G

theorem integral_singularSpectralRegressionModel_groupedNoise {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (lam : Fin (min n q) → ℝ) (O : Orth q)
    {f : Sym (q + m) → ℝ} (hf : Measurable f) :
    (∫ G, f (singularSpectralRegressionModel K C (lam, O, G)) ∂gaussianMatrixMeasure n m) =
      ∫ x, f (shiftedRowsSym (singularRegressionDirection n K O) lam x)
        ∂gaussianResidualMeasure (min n q) (singularNoiseCovariance (q := q) C)
          (wishartGramMeasure (n - min n q) (singularNoiseCovariance (q := q) C)) := by
  have hmodel : Measurable (fun G : Matrix (Fin n) (Fin m) ℝ =>
      singularSpectralRegressionModel K C (lam, O, G)) :=
    (measurable_singularSpectralRegressionModel K C).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [← integral_map hmodel.aemeasurable hf.aestronglyMeasurable,
    map_singularSpectralRegressionModel_groupedNoise,
    integral_map (measurable_shiftedRowsSym _ _).aemeasurable hf.aestronglyMeasurable]

end Wishart
end
end CanonicalSource111

section CanonicalSource112
/- Source: Wishart/SteinConvolution.lean -/



/-! # Addition of independent laws with a linear Stein identity

This is an internal closure lemma.  Its input identities are proved for the
actual row laws in `GramStein`; they are not hypotheses of a principal result.
-/

noncomputable section

open MeasureTheory

namespace WishartVerification

/-- Evaluating a temperate derivative along temperate inputs preserves temperate growth. -/
theorem hasTemperateGrowth_fderiv_apply {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {g : E → ℝ} {V B : D → E}
    (hg : g.HasTemperateGrowth) (hV : V.HasTemperateGrowth) (hB : B.HasTemperateGrowth) :
    (fun z => fderiv ℝ g (V z) (B z)).HasTemperateGrowth := by
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
    (ContinuousLinearMap.apply ℝ (E' := E) ℝ).bilinear_hasTemperateGrowth hB
      ((hasTemperateGrowth_fderiv hg).comp hV)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def LinearSteinIdentity (μ : Measure E) (B : E →L[ℝ] E) (c : E →L[ℝ] ℝ)
    (a : ℝ) : Prop :=
  ∀ (g : E → ℝ), g.HasTemperateGrowth → ∀ T : E,
    (∫ X, fderiv ℝ g (X + T) (B X) ∂μ) =
      ∫ X, (c X - a) * g (X + T) ∂μ

set_option backward.isDefEq.respectTransparency false in
theorem hasTemperateGrowth_linearSteinDerivative (B : E →L[ℝ] E) (T : E)
    {g : E → ℝ} (hg : g.HasTemperateGrowth) :
    (fun X => fderiv ℝ g (X + T) (B X)).HasTemperateGrowth := by
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, Pi.add_def, id_eq] using
    (ContinuousLinearMap.apply ℝ (E' := E) ℝ).bilinear_hasTemperateGrowth B.hasTemperateGrowth
      ((hasTemperateGrowth_fderiv hg).comp
        (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const T)))

set_option backward.isDefEq.respectTransparency false in
theorem hasTemperateGrowth_linearSteinScore (c : E →L[ℝ] ℝ) (a : ℝ) (T : E)
    {g : E → ℝ} (hg : g.HasTemperateGrowth) :
    (fun X => (c X - a) * g (X + T)).HasTemperateGrowth := by
  simpa only [Function.comp_def, Pi.sub_def, Pi.mul_def, Pi.add_def, id_eq] using
    (c.hasTemperateGrowth.sub (Function.HasTemperateGrowth.const a)).mul
      (hg.comp (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const T)))

theorem linearSteinIdentity_dirac_zero (B : E →L[ℝ] E) (c : E →L[ℝ] ℝ) :
    LinearSteinIdentity (Measure.dirac 0) B c 0 := by
  intro g hg T
  simp only [integral_dirac, map_zero, zero_add, sub_zero, zero_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Independent addition adds the scalar terms in the two Stein identities. -/
theorem linearSteinIdentity_conv {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasAllFiniteMoments (fun X : E => ‖X‖) μ)
    (hν : HasAllFiniteMoments (fun X : E => ‖X‖) ν)
    (B : E →L[ℝ] E) (c : E →L[ℝ] ℝ) (a b : ℝ)
    (hμs : LinearSteinIdentity μ B c a) (hνs : LinearSteinIdentity ν B c b) :
    LinearSteinIdentity (μ ∗ ν) B c (a + b) := by
  intro g hg T
  let μp := μ.prod ν
  let V : E × E → E := fun z => z.1 + z.2 + T
  let L₁ : E × E → ℝ := fun z => fderiv ℝ g (V z) (B z.1)
  let L₂ : E × E → ℝ := fun z => fderiv ℝ g (V z) (B z.2)
  let R₁ : E × E → ℝ := fun z => (c z.1 - a) * g (V z)
  let R₂ : E × E → ℝ := fun z => (c z.2 - b) * g (V z)
  have hp : HasAllFiniteMoments (fun z : E × E => ‖z‖) μp :=
    allFiniteNormMoments_prod hμ hν
  have hfst := (ContinuousLinearMap.fst ℝ E E).hasTemperateGrowth
  have hsnd := (ContinuousLinearMap.snd ℝ E E).hasTemperateGrowth
  have hV : V.HasTemperateGrowth := (hfst.add hsnd).add
    (Function.HasTemperateGrowth.const T)
  have hd := (hasTemperateGrowth_fderiv hg).comp hV
  have hgf := hg.comp hV
  have hL₁ : Integrable L₁ μp := by
    apply integrable_temperate_of_allNormMoments hp
    simpa only [L₁, Function.comp_def, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.coe_fst'] using
      (ContinuousLinearMap.apply ℝ (E' := E) ℝ).bilinear_hasTemperateGrowth
        (B.hasTemperateGrowth.comp hfst) hd
  have hL₂ : Integrable L₂ μp := by
    apply integrable_temperate_of_allNormMoments hp
    simpa only [L₂, Function.comp_def, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.coe_snd'] using
      (ContinuousLinearMap.apply ℝ (E' := E) ℝ).bilinear_hasTemperateGrowth
        (B.hasTemperateGrowth.comp hsnd) hd
  have hR₁ : Integrable R₁ μp := by
    apply integrable_temperate_of_allNormMoments hp
    simpa only [R₁, Function.comp_def, Pi.sub_def, Pi.mul_def,
      ContinuousLinearMap.coe_fst'] using
      ((c.hasTemperateGrowth.comp hfst).sub (Function.HasTemperateGrowth.const a)).mul hgf
  have hR₂ : Integrable R₂ μp := by
    apply integrable_temperate_of_allNormMoments hp
    simpa only [R₂, Function.comp_def, Pi.sub_def, Pi.mul_def,
      ContinuousLinearMap.coe_snd'] using
      ((c.hasTemperateGrowth.comp hsnd).sub (Function.HasTemperateGrowth.const b)).mul hgf
  have heq₁ : (∫ z, L₁ z ∂μp) = ∫ z, R₁ z ∂μp := by
    rw [integral_prod_symm _ hL₁, integral_prod_symm _ hR₁]
    apply integral_congr_ae
    filter_upwards with Y
    simpa only [L₁, R₁, V, add_assoc] using hμs g hg (Y + T)
  have heq₂ : (∫ z, L₂ z ∂μp) = ∫ z, R₂ z ∂μp := by
    rw [integral_prod _ hL₂, integral_prod _ hR₂]
    apply integral_congr_ae
    filter_upwards with X
    simpa only [L₂, R₂, V, add_assoc, add_comm, add_left_comm] using hνs g hg (X + T)
  have hleft := (hasTemperateGrowth_linearSteinDerivative B T hg).1.continuous
  have hright := (hasTemperateGrowth_linearSteinScore c (a + b) T hg).1.continuous
  rw [Measure.conv,
    integral_map (by fun_prop) hleft.aestronglyMeasurable,
    integral_map (by fun_prop) hright.aestronglyMeasurable]
  calc
    (∫ z : E × E, fderiv ℝ g (z.1 + z.2 + T) (B (z.1 + z.2)) ∂μ.prod ν) =
        ∫ z, L₁ z + L₂ z ∂μp := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [map_add, L₁, L₂, V]
    _ = (∫ z, L₁ z ∂μp) + ∫ z, L₂ z ∂μp := integral_add hL₁ hL₂
    _ = (∫ z, R₁ z ∂μp) + ∫ z, R₂ z ∂μp := by rw [heq₁, heq₂]
    _ = ∫ z, R₁ z + R₂ z ∂μp := (integral_add hR₁ hR₂).symm
    _ = ∫ z : E × E, (c (z.1 + z.2) - (a + b)) * g (z.1 + z.2 + T) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [R₁, R₂, V, map_add]
      ring

end WishartVerification
end
end CanonicalSource112

section CanonicalSource113
/- Source: Wishart/GramStein.lean -/



/-!
# Stein identities for Gaussian Gram measures, including singular degrees

The single-row identity comes from Gaussian integration by parts applied to
an actual linear-weighted test.  Adding independent Gaussian rows supplies the
integer-degree identity without using a nonexistent density on the ambient
positive definite cone.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace WishartVerification

variable {p : ℕ}

theorem allFiniteMoments_gram_norm (n : ℕ) (C : Matrix (Fin p) (Fin p) ℝ) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p => ‖X‖) (wishartGramMeasure n C) := by
  intro q hq
  simpa only [ENNReal.coe_toNNReal hq] using
    (memLp_id_wishartGramMeasure C n q.toNNReal).norm

@[simp] theorem symmetricMatrixAction_rankOne (z u : EuclideanSpace ℝ (Fin p)) :
    symmetricMatrixAction (rankOneSymmetric z) u = ⟪u, z⟫ • z := by
  apply PiLp.ext
  intro i
  simp only [symmetricMatrixAction_apply, coe_rankOneSymmetric, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, PiLp.smul_apply,
    smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem wishartGram_fin_one (z : Fin 1 → EuclideanSpace ℝ (Fin p)) :
    wishartGram z = rankOneSymmetric (z 0) := by
  apply Subtype.ext
  simp only [coe_wishartGram, Fin.sum_univ_one, coe_rankOneSymmetric]

theorem map_rankOneSymmetric_gaussian (C : Matrix (Fin p) (Fin p) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C).map rankOneSymmetric =
      wishartGramMeasure 1 C := by
  have hmap := (measurePreserving_eval
    (fun _ : Fin 1 => multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C) 0).map_eq
  rw [← hmap, Measure.map_map
    hasTemperateGrowth_rankOneSymmetric.1.continuous.measurable (by fun_prop),
    wishartGramMeasure_eq_map_pi]
  congr 1
  funext z
  exact (wishartGram_fin_one z).symm

theorem map_gram_add_gaussian_rankOne (n : ℕ) (C : Matrix (Fin p) (Fin p) ℝ) :
    ((wishartGramMeasure n C).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)).map
        (fun z => z.1 + rankOneSymmetric z.2) = wishartGramMeasure (n + 1) C := by
  rw [← wishartGramMeasure_conv_wishartGramMeasure n 1 C,
    ← map_rankOneSymmetric_gaussian C, Measure.conv]
  have hm : Measurable (rankOneSymmetric : EuclideanSpace ℝ (Fin p) → SymmetricMatrix p) :=
    hasTemperateGrowth_rankOneSymmetric.1.continuous.measurable
  have hp := Measure.map_prod_map (wishartGramMeasure n C)
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C) measurable_id hm
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A single Gaussian row, with an arbitrary fixed symmetric offset. -/
theorem gaussian_rankOne_stein {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (T : SymmetricMatrix p) (u v : EuclideanSpace ℝ (Fin p)) :
    (∫ z, ⟪u, z⟫ * fderiv ℝ g (T + rankOneSymmetric z)
      (symmetricRankDirection v z) ∂multivariateGaussian 0 C) =
    ∫ z, (⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫ - ⟪u, v⟫) *
      g (T + rankOneSymmetric z) ∂multivariateGaussian 0 C := by
  let V : EuclideanSpace ℝ (Fin p) → SymmetricMatrix p := fun z => T + rankOneSymmetric z
  let f : EuclideanSpace ℝ (Fin p) → ℝ := fun z => ⟪u, z⟫ * g (V z)
  let L : EuclideanSpace ℝ (Fin p) → ℝ := fun z =>
    ⟪u, z⟫ * fderiv ℝ g (V z) (symmetricRankDirection v z)
  let G : EuclideanSpace ℝ (Fin p) → ℝ := fun z =>
    (⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫) * g (V z)
  have hV : V.HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const T).add hasTemperateGrowth_rankOneSymmetric
  have hgf : (fun z => g (V z)).HasTemperateGrowth := hg.comp hV
  have hf : f.HasTemperateGrowth := (innerSL ℝ u).hasTemperateGrowth.mul hgf
  have hL : L.HasTemperateGrowth := by
    simpa only [L, Pi.mul_def, innerSL_apply_apply] using
      (innerSL ℝ u).hasTemperateGrowth.mul
        (hasTemperateGrowth_fderiv_apply hg hV (symmetricRankDirection v).hasTemperateGrowth)
  have hG : G.HasTemperateGrowth := by
    simpa only [G, Function.comp_def, Pi.mul_def, innerSL_apply_apply,
      LinearMap.coe_toContinuousLinearMap'] using
      (((innerSL ℝ v).hasTemperateGrowth.comp
        C⁻¹.toEuclideanLin.toContinuousLinearMap.hasTemperateGrowth).mul
          (innerSL ℝ u).hasTemperateGrowth).mul hgf
  have hμ := allFiniteMoments_gaussian_norm (μ := multivariateGaussian 0 C)
  have hLi := integrable_temperate_of_allNormMoments hμ hL
  have hGi := integrable_temperate_of_allNormMoments hμ hG
  have hfi := integrable_temperate_of_allNormMoments hμ hgf
  have hd (z : EuclideanSpace ℝ (Fin p)) :
      fderiv ℝ f z v = ⟪u, v⟫ * g (V z) + L z := by
    have hderiv := ((innerSL ℝ u).hasFDerivAt.mul
      ((hg.1.differentiable (by simp) (V z)).hasFDerivAt.comp z
        ((hasFDerivAt_rankOneSymmetric z).const_add T))).fderiv
    have heval := congrArg (fun A : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ => A v) hderiv
    simpa only [f, V, L, Function.comp_def, Pi.mul_def, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, symmetricRankDirection_comm,
      mul_comm, add_comm] using heval
  have hs := gaussian_stein_temperate hC hf v
  simp_rw [hd] at hs
  have hGi' : (∫ z, ⟪v, C⁻¹.toEuclideanLin z⟫ * f z ∂multivariateGaussian 0 C) =
      ∫ z, G z ∂multivariateGaussian 0 C := by
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [f, G]
    ring
  rw [hGi', integral_add (hfi.const_mul ⟪u, v⟫) hLi, integral_const_mul] at hs
  change (∫ z, L z ∂multivariateGaussian 0 C) = _
  have heq : (fun z => (⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫ - ⟪u, v⟫) *
      g (T + rankOneSymmetric z)) = (fun z => G z - ⟪u, v⟫ * g (V z)) := by
    funext z
    dsimp only [G, V]
    ring
  rw [heq, integral_sub hGi (hfi.const_mul ⟪u, v⟫), integral_const_mul]
  linarith

def gramSteinDirection (u v : EuclideanSpace ℝ (Fin p)) :
    SymmetricMatrix p →L[ℝ] SymmetricMatrix p :=
  (symmetricRankDirection v).comp (symmetricMatrixAction.flip u)

def gramSteinScore (C : Matrix (Fin p) (Fin p) ℝ)
    (u v : EuclideanSpace ℝ (Fin p)) : SymmetricMatrix p →L[ℝ] ℝ :=
  (innerSL ℝ u).comp (symmetricMatrixAction.flip (C⁻¹.toEuclideanLin v))

@[simp] theorem gramSteinDirection_apply (u v : EuclideanSpace ℝ (Fin p))
    (W : SymmetricMatrix p) :
    gramSteinDirection u v W = symmetricRankDirection v (symmetricMatrixAction W u) := rfl

@[simp] theorem gramSteinScore_apply (C : Matrix (Fin p) (Fin p) ℝ)
    (u v : EuclideanSpace ℝ (Fin p)) (W : SymmetricMatrix p) :
    gramSteinScore C u v W = ⟪u, symmetricMatrixAction W (C⁻¹.toEuclideanLin v)⟫ := rfl

theorem gramSteinDirection_rankOne (u v z : EuclideanSpace ℝ (Fin p)) :
    gramSteinDirection u v (rankOneSymmetric z) = ⟪u, z⟫ • symmetricRankDirection v z := by
  rw [gramSteinDirection_apply, symmetricMatrixAction_rankOne, map_smul]

theorem gramSteinScore_rankOne {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    (u v z : EuclideanSpace ℝ (Fin p)) :
    gramSteinScore C u v (rankOneSymmetric z) = ⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫ := by
  rw [gramSteinScore_apply, symmetricMatrixAction_rankOne, real_inner_smul_right]
  rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr hC.inv.isHermitian) v z]

theorem linearSteinIdentity_gram_one {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    (u v : EuclideanSpace ℝ (Fin p)) :
    LinearSteinIdentity (wishartGramMeasure 1 C)
      (gramSteinDirection u v) (gramSteinScore C u v) ⟪u, v⟫ := by
  intro g hg T
  have hleft := (hasTemperateGrowth_linearSteinDerivative (gramSteinDirection u v) T hg).1.continuous
  have hright := (hasTemperateGrowth_linearSteinScore (gramSteinScore C u v) ⟪u, v⟫ T hg).1.continuous
  rw [← map_rankOneSymmetric_gaussian C,
    integral_map hasTemperateGrowth_rankOneSymmetric.1.continuous.measurable.aemeasurable
      hleft.aestronglyMeasurable,
    integral_map hasTemperateGrowth_rankOneSymmetric.1.continuous.measurable.aemeasurable
      hright.aestronglyMeasurable]
  simpa only [gramSteinDirection_rankOne, gramSteinScore_rankOne hC,
    map_smul, smul_eq_mul, add_comm] using gaussian_rankOne_stein hC hg T u v

/-- The genuine Gram law has the linear Stein identity at every natural
degree, including degrees below the ambient dimension and degree zero. -/
theorem linearSteinIdentity_gram (n : ℕ) {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) (u v : EuclideanSpace ℝ (Fin p)) :
    LinearSteinIdentity (wishartGramMeasure n C)
      (gramSteinDirection u v) (gramSteinScore C u v) ((n : ℝ) * ⟪u, v⟫) := by
  induction n with
  | zero =>
      simpa only [wishartGramMeasure_zero, Nat.cast_zero, zero_mul] using
        linearSteinIdentity_dirac_zero (gramSteinDirection u v) (gramSteinScore C u v)
  | succ n ih =>
      have h := linearSteinIdentity_conv (allFiniteMoments_gram_norm n C)
        (allFiniteMoments_gram_norm 1 C) (gramSteinDirection u v) (gramSteinScore C u v)
        ((n : ℝ) * ⟪u, v⟫) ⟪u, v⟫ ih (linearSteinIdentity_gram_one hC u v)
      rw [wishartGramMeasure_conv_wishartGramMeasure] at h
      have ha : ((n + 1 : ℕ) : ℝ) * ⟪u, v⟫ = (n : ℝ) * ⟪u, v⟫ + ⟪u, v⟫ := by
        push_cast
        ring
      simpa only [Nat.succ_eq_add_one, ha] using h

theorem gram_stein_translate (n : ℕ) {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (T : SymmetricMatrix p) (u v : EuclideanSpace ℝ (Fin p)) :
    (∫ W, fderiv ℝ g (W + T)
      (symmetricRankDirection v (symmetricMatrixAction W u)) ∂wishartGramMeasure n C) =
      ∫ W, (⟪u, symmetricMatrixAction W (C⁻¹.toEuclideanLin v)⟫ -
        (n : ℝ) * ⟪u, v⟫) * g (W + T) ∂wishartGramMeasure n C :=
  linearSteinIdentity_gram n hC u v g hg T

end WishartVerification
end
end CanonicalSource113

section CanonicalSource114
/- Source: Wishart/GramWeightedRadialStein.lean -/



/-!
# Weighted radial identity for every natural Gram degree

The background law is the actual Gaussian Gram measure, including singular
and zero degrees. The identity is supplied by Gaussian integration by parts
and independent-row convolution in `GramStein`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix
open scoped RealInnerProductSpace

namespace WishartVerification

variable {p : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem weighted_radial_gram_stein {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    (n : ℕ)
    {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (u v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    r * (∫ Y : RadialInputSpace p,
      ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ *
        g (radialInput v r Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) =
    (n : ℝ) * (∫ Y : RadialInputSpace p, ⟪u, Y.2 + r • v⟫ * g (radialInput v r Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) := by
  let μW := wishartGramMeasure n C
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  let w : RadialInputSpace p → EuclideanSpace ℝ (Fin p) := fun Y => Y.2 + r • v
  let V : RadialInputSpace p → SymmetricMatrix p := radialInput v r
  let L : RadialInputSpace p → ℝ := fun Y =>
    fderiv ℝ g (V Y) (symmetricRankDirection (w Y) (symmetricMatrixAction Y.1 u))
  let G : RadialInputSpace p → ℝ := fun Y =>
    ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin Y.2)⟫ * g (V Y)
  let Q : RadialInputSpace p → ℝ := fun Y =>
    ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ * g (V Y)
  let R : RadialInputSpace p → ℝ := fun Y => ⟪u, w Y⟫ * g (V Y)
  let S : RadialInputSpace p → ℝ := fun Y =>
    (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin (w Y))⟫ - (n : ℝ) * ⟪u, w Y⟫) * g (V Y)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C) allFiniteMoments_gaussian_norm
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hZ := (ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hw : w.HasTemperateGrowth := hZ.add (Function.HasTemperateGrowth.const (r • v))
  have hV : V.HasTemperateGrowth := hW.add (hasTemperateGrowth_rankOneSymmetric.comp hw)
  have hgV := hg.comp hV
  have hCi := (LinearMap.toContinuousLinearMap C⁻¹.toEuclideanLin).hasTemperateGrowth
  have hinner := (innerSL ℝ u).hasTemperateGrowth
  have hWu := symmetricMatrixAction.bilinear_hasTemperateGrowth hW (Function.HasTemperateGrowth.const u)
  have hH : (fun Y : RadialInputSpace p =>
      symmetricRankDirection (w Y) (symmetricMatrixAction Y.1 u)).HasTemperateGrowth := by
    simpa only [symmetricRankDirection, ContinuousLinearMap.smul_apply,
      Pi.smul_def, Pi.smul_apply, ContinuousLinearMap.coe_fst', two_smul,
      ContinuousLinearMap.add_apply] using
      (Function.HasTemperateGrowth.const (2 : ℝ)).fun_smul
        (symmetricOuterCLM.bilinear_hasTemperateGrowth hw hWu)
  have hLt : L.HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hH
      ((hasTemperateGrowth_fderiv hg).comp hV)
  have hGt : G.HasTemperateGrowth :=
    (hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW (hCi.comp hZ))).mul hgV
  have hQt : Q.HasTemperateGrowth :=
    (hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
      (Function.HasTemperateGrowth.const _))).mul hgV
  have hRt : R.HasTemperateGrowth := (hinner.comp hw).mul hgV
  have hSt : S.HasTemperateGrowth :=
    ((hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW (hCi.comp hw))).sub
      ((Function.HasTemperateGrowth.const (n : ℝ)).mul (hinner.comp hw))).mul hgV
  have hLint : Integrable L μ := integrable_temperate_of_allNormMoments hμ hLt
  have hGint : Integrable G μ := integrable_temperate_of_allNormMoments hμ hGt
  have hQint : Integrable Q μ := integrable_temperate_of_allNormMoments hμ hQt
  have hRint : Integrable R μ := integrable_temperate_of_allNormMoments hμ hRt
  have hSint : Integrable S μ := integrable_temperate_of_allNormMoments hμ hSt
  have hWishart (z : EuclideanSpace ℝ (Fin p)) :
      (∫ W, L (W, z) ∂μW) = ∫ W, S (W, z) ∂μW := by
    let wz := z + r • v
    simpa only [L, S, w, V, radialInput, wz] using
      gram_stein_translate n hC hg (rankOneSymmetric wz) u wz
  have hGaussian (W : SymmetricMatrix p) :
      (∫ z, G (W, z) ∂μZ) = ∫ z, L (W, z) ∂μZ := by
    have hshift : (fun z : EuclideanSpace ℝ (Fin p) => z + r • v).HasTemperateGrowth :=
      Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const _)
    have htest : (fun z : EuclideanSpace ℝ (Fin p) =>
        g (W + rankOneSymmetric (z + r • v))).HasTemperateGrowth :=
      hg.comp ((Function.HasTemperateGrowth.const W).add (hasTemperateGrowth_rankOneSymmetric.comp hshift))
    have hid := gaussian_stein_temperate hC htest (symmetricMatrixAction W u)
    have hd (z h : EuclideanSpace ℝ (Fin p)) :
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin p) => g (W + rankOneSymmetric (z + r • v))) z h =
          fderiv ℝ g (W + rankOneSymmetric (z + r • v))
            (symmetricRankDirection (z + r • v) h) := by
      have hin := (hasFDerivAt_rankOneSymmetric (z + r • v)).comp z
        ((hasFDerivAt_id z).add_const (r • v))
      have hderiv := ((hg.1.differentiable (by simp) _).hasFDerivAt.comp z (hin.const_add W)).fderiv
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using congrArg (fun J => J h) hderiv
    simpa only [hd, inner_symmetricMatrixAction, L, G, w, V, radialInput] using hid
  have hSG : (∫ Y, S Y ∂μ) = ∫ Y, G Y ∂μ := by
    rw [integral_prod_symm S hSint, integral_prod G hGint]
    calc
      (∫ z, ∫ W, S (W, z) ∂μW ∂μZ) = ∫ z, ∫ W, L (W, z) ∂μW ∂μZ :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => (hWishart z).symm)
      _ = ∫ Y, L Y ∂μ := (integral_prod_symm L hLint).symm
      _ = ∫ W, ∫ z, L (W, z) ∂μZ ∂μW := integral_prod L hLint
      _ = ∫ W, ∫ z, G (W, z) ∂μZ ∂μW :=
        integral_congr_ae (Filter.Eventually.of_forall fun W => (hGaussian W).symm)
  have hsplit : S = fun Y => G Y + r * Q Y - (n : ℝ) * R Y := by
    funext Y
    simp only [S, G, Q, R, w, map_add, map_smul, inner_add_right, real_inner_smul_right]
    ring
  rw [hsplit] at hSG
  have hsumInt : Integrable (fun Y => G Y + r * Q Y) μ := by
    simpa only [Pi.add_def] using hGint.add (hQint.const_mul r)
  rw [integral_sub hsumInt (hRint.const_mul (n : ℝ)),
    integral_add hGint (hQint.const_mul r), integral_const_mul, integral_const_mul] at hSG
  change r * (∫ Y, Q Y ∂μ) = (n : ℝ) * (∫ Y, R Y ∂μ)
  linarith

end WishartVerification
end
end CanonicalSource114

section CanonicalSource115
/- Source: Wishart/GramRadialSteinIdentity.lean -/



/-! # The radial generator identity for singular integer Gram laws

This version uses the actual Gaussian Gram law at every natural degree.
The calculus helpers are common to both versions; the law-specific Stein
input is the proved Gaussian-row identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix
open scoped RealInnerProductSpace BigOperators
namespace WishartVerification
variable {p : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem radial_gram_stein {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    (n : ℕ)
    {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (u v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (∫ Y : RadialInputSpace p,
      fderiv ℝ g (radialInput v r Y)
        (symmetricRankDirection v (symmetricMatrixAction Y.1 u))
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) =
    ∫ Y : RadialInputSpace p,
      (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ - (n : ℝ) * ⟪u, v⟫) *
        g (radialInput v r Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C) := by
  let μW := wishartGramMeasure n C
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C) allFiniteMoments_gaussian_norm
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hV := hasTemperateGrowth_radialInput_slice v r
  have hWu := symmetricMatrixAction.bilinear_hasTemperateGrowth hW
    (Function.HasTemperateGrowth.const u)
  have hH := (symmetricRankDirection v).hasTemperateGrowth.comp hWu
  have hL : Integrable (fun Y : RadialInputSpace p =>
      fderiv ℝ g (radialInput v r Y)
        (symmetricRankDirection v (symmetricMatrixAction Y.1 u))) μ := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.coe_fst'] using
      integrable_temperate_of_allNormMoments hμ
        ((ContinuousLinearMap.apply ℝ (E' := SymmetricMatrix p) ℝ).bilinear_hasTemperateGrowth hH
          ((hasTemperateGrowth_fderiv hg).comp hV))
  have hscore := ((innerSL ℝ u).hasTemperateGrowth.comp
    (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
      (Function.HasTemperateGrowth.const (C⁻¹.toEuclideanLin v)))).sub
        (Function.HasTemperateGrowth.const ((n : ℝ) * ⟪u, v⟫))
  have hR : Integrable (fun Y : RadialInputSpace p =>
      (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ - (n : ℝ) * ⟪u, v⟫) *
        g (radialInput v r Y)) μ := by
    simpa only [Function.comp_def, Pi.sub_def, Pi.mul_def,
      ContinuousLinearMap.coe_fst', innerSL_apply_apply] using
      integrable_temperate_of_allNormMoments hμ (hscore.mul (hg.comp hV))
  rw [integral_prod_symm _ hL, integral_prod_symm _ hR]
  apply integral_congr_ae
  filter_upwards with z
  simpa only [radialInput] using
    gram_stein_translate n hC hg (rankOneSymmetric (z + r • v)) u v


set_option backward.isDefEq.respectTransparency false in
theorem radial_gram_generator_identity {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    (n : ℕ)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    r * (∫ Y : RadialInputSpace p, symmetricRadialGenerator ((n : ℝ) + 1) v f (radialInput v r Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) =
    r * (∫ Y : RadialInputSpace p, radialSecondIntegrand f v r Y
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) +
    (n : ℝ) * (∫ Y : RadialInputSpace p, radialFirstIntegrand f v r Y
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) := by
  let μ := (wishartGramMeasure n C).prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
  let V := radialInput v r
  let gi := radialDerivativeTest f v
  let L : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    fderiv ℝ (gi i) (V Y)
      (symmetricRankDirection v (symmetricMatrixAction Y.1 (coordinateVector i)))
  let Q : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    ⟪coordinateVector i, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ * gi i (V Y)
  let R : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    (Y.2 + r • v) i * gi i (V Y)
  let B : RadialInputSpace p → ℝ := fun Y => fderiv ℝ f (V Y) (rankOneSymmetric v)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C) allFiniteMoments_gaussian_norm
  have hV := hasTemperateGrowth_radialInput_slice v r
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hZ := (ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hgi (i : Fin p) := hasTemperateGrowth_radialDerivativeTest hf v i
  have hgint (i : Fin p) : Integrable (fun Y => gi i (V Y)) μ :=
    integrable_temperate_of_allNormMoments hμ ((hgi i).comp hV)
  have hLint (i : Fin p) : Integrable (L i) μ := by
    exact integrable_temperate_of_allNormMoments hμ
      ((ContinuousLinearMap.apply ℝ (E' := SymmetricMatrix p) ℝ).bilinear_hasTemperateGrowth
        ((symmetricRankDirection v).hasTemperateGrowth.comp
          (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
            (Function.HasTemperateGrowth.const (coordinateVector i))))
        ((hasTemperateGrowth_fderiv (hgi i)).comp hV))
  have hQint (i : Fin p) : Integrable (Q i) μ :=
    integrable_temperate_of_allNormMoments hμ
      (((innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
        (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
          (Function.HasTemperateGrowth.const (C⁻¹.toEuclideanLin v)))).mul ((hgi i).comp hV))
  have hRint (i : Fin p) : Integrable (R i) μ := by
    have ht := ((innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
      (hZ.add (Function.HasTemperateGrowth.const (r • v)))).mul ((hgi i).comp hV)
    simpa only [Function.comp_def, Pi.add_def, Pi.mul_def,
      ContinuousLinearMap.coe_snd', innerSL_apply_apply, coordinate_inner, R, gi, V] using
      integrable_temperate_of_allNormMoments hμ ht
  have hBint : Integrable B μ := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, B, V] using
      integrable_temperate_of_allNormMoments hμ
        ((ContinuousLinearMap.apply ℝ ℝ (rankOneSymmetric v)).hasTemperateGrowth.comp
          ((hasTemperateGrowth_fderiv hf).comp hV))
  have hsecond : Integrable (radialSecondIntegrand f v r) μ :=
    integrable_temperate_of_allNormMoments hμ
      ((hasTemperateGrowth_radialSecondIntegrand hf v).comp
        (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const r)
          Function.HasTemperateGrowth.id))
  have hWi (i : Fin p) :
      (∫ Y, L i Y ∂μ) = (∫ Y, Q i Y ∂μ) - (n : ℝ) * v i * (∫ Y, gi i (V Y) ∂μ) := by
    have h := radial_gram_stein hC n (hgi i) (coordinateVector i) v r
    simp only [sub_mul, coordinate_inner] at h
    have hQint' : Integrable (fun Y : RadialInputSpace p =>
        (symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)) i * gi i (V Y)) μ := by
      simpa only [Q, coordinate_inner] using hQint i
    change (∫ Y, L i Y ∂μ) = ∫ Y,
      (symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)) i * gi i (V Y) -
        (n : ℝ) * v i * gi i (V Y) ∂μ at h
    rw [integral_sub hQint' ((hgint i).const_mul ((n : ℝ) * v i)), integral_const_mul] at h
    simpa only [Q, coordinate_inner] using h
  have hRi (i : Fin p) : r * (∫ Y, Q i Y ∂μ) = (n : ℝ) * (∫ Y, R i Y ∂μ) := by
    simpa only [Q, R, gi, V, μ, coordinate_inner] using
      weighted_radial_gram_stein hC n (hgi i) (coordinateVector i) v r
  have hLi (i : Fin p) :
      r * (∫ Y, L i Y ∂μ) + r * (n : ℝ) * v i * (∫ Y, gi i (V Y) ∂μ) =
        (n : ℝ) * (∫ Y, R i Y ∂μ) := by
    rw [hWi]
    nlinarith [hRi i]
  have hsum := congrArg (fun a : Fin p → ℝ => ∑ i, a i) (funext hLi)
  have hLpoint (Y : RadialInputSpace p) :
      (∑ i, L i Y) = radialCovarianceContraction f (V Y) v
        (Y.1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [radialCovarianceContraction_eq_directional_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (symmetricSecondDerivative_eq hf _ _ _).symm
  have hRpoint (Y : RadialInputSpace p) :
      (∑ i, R i Y) = radialFirstIntegrand f v r Y :=
    (radialFirstIntegrand_eq_coordinate_sum f v r Y).symm
  have hBpoint (Y : RadialInputSpace p) :
      (∑ i, v i * gi i (V Y)) = 2 * B Y := sum_radialDerivativeTest f v (V Y)
  have hLsum : (∑ i, ∫ Y, L i Y ∂μ) =
      ∫ Y, radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ) ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hLint i)]
    exact integral_congr_ae (Filter.Eventually.of_forall hLpoint)
  have hRsum : (∑ i, ∫ Y, R i Y ∂μ) = ∫ Y, radialFirstIntegrand f v r Y ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hRint i)]
    exact integral_congr_ae (Filter.Eventually.of_forall hRpoint)
  have hBsum : (∑ i, v i * (∫ Y, gi i (V Y) ∂μ)) = 2 * (∫ Y, B Y ∂μ) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hgint i).const_mul (v i))]
    rw [integral_congr_ae (Filter.Eventually.of_forall hBpoint), integral_const_mul]
  have hcovint : Integrable (fun Y =>
      radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) μ := by
    exact (integrable_finsetSum _ (fun i _ => hLint i)).congr
      (Filter.Eventually.of_forall hLpoint)
  have hgen :
      (∫ Y, symmetricRadialGenerator ((n : ℝ) + 1) v f (V Y) ∂μ) =
        (∫ Y, radialSecondIntegrand f v r Y ∂μ) +
        (∫ Y, radialCovarianceContraction f (V Y) v
          (Y.1 : Matrix (Fin p) (Fin p) ℝ) ∂μ) +
        2 * (n : ℝ) * (∫ Y, B Y ∂μ) := by
    simp_rw [V, symmetricRadialGenerator_decomposition]
    have hsumInt : Integrable (fun Y => radialSecondIntegrand f v r Y +
        radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) μ := by
      simpa only [Pi.add_def] using hsecond.add hcovint
    change (∫ Y, (radialSecondIntegrand f v r Y +
        radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) +
        2 * ((n : ℝ) + 1 - 1) * B Y ∂μ) = _
    rw [integral_add hsumInt (hBint.const_mul (2 * ((n : ℝ) + 1 - 1))),
      integral_add hsecond hcovint, integral_const_mul]
    ring
  change r * (∫ Y, symmetricRadialGenerator ((n : ℝ) + 1) v f (V Y) ∂μ) = _
  rw [hgen]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum
  rw [hLsum, hRsum] at hsum
  have hBsum' : (∑ i, v i * ∫ Y, gi i (V Y) ∂μ) = 2 * ∫ Y, B Y ∂μ := hBsum
  rw [hBsum'] at hsum
  nlinarith


end WishartVerification
end
end CanonicalSource115

section CanonicalSource116
/- Source: Wishart/GramRadialMeanMonotonicity.lean -/



/-! # Radial monotonicity for every natural Gram degree

The degree is not restricted by the ambient dimension. This file first proves
the result for positive definite covariance; covariance-degenerate limits are
treated separately using coupled Gaussian rows.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set Topology Matrix
namespace WishartVerification
variable {p : ℕ}

theorem radialGramExpectation_even {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    (n : ℕ)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (∫ Y : RadialInputSpace p, f (radialInput v (-r) Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) =
    ∫ Y : RadialInputSpace p, f (radialInput v r Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C) := by
  let μW := wishartGramMeasure n C
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C) allFiniteMoments_gaussian_norm
  have hint (s : ℝ) : Integrable (fun Y => f (radialInput v s Y)) μ :=
    integrable_temperate_of_allNormMoments hμ (hf.comp (hasTemperateGrowth_radialInput_slice v s))
  rw [integral_prod _ (hint (-r)), integral_prod _ (hint r)]
  apply integral_congr_ae
  filter_upwards with W
  have hneg : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin p) => -z) μZ μZ :=
    ⟨by fun_prop, map_neg_centered_multivariateGaussian hC.posSemidef⟩
  have h := hneg.integral_comp (MeasurableEquiv.neg _).measurableEmbedding
    (fun z => f (W + rankOneSymmetric (z + r • v)))
  change (∫ z, f (W + rankOneSymmetric (z + (-r) • v)) ∂μZ) =
    ∫ z, f (W + rankOneSymmetric (z + r • v)) ∂μZ
  calc
    (∫ z, f (W + rankOneSymmetric (z + (-r) • v)) ∂μZ) =
        ∫ z, f (W + rankOneSymmetric (-z + r • v)) ∂μZ := by
      apply integral_congr_ae
      filter_upwards with z
      have he : -z + r • v = -(z + (-r) • v) := by module
      rw [he, rankOneSymmetric_neg]
    _ = _ := h

theorem ae_radialGramInput_posSemidef (n : ℕ) (C : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    ∀ᵐ Y : RadialInputSpace p
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C),
      (radialInput v r Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  have hW : ∀ᵐ Y : RadialInputSpace p
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C),
      (Y.1 : Matrix (Fin p) (Fin p) ℝ).PosSemidef :=
    Measure.quasiMeasurePreserving_fst.ae (ae_posSemidef_wishartGramMeasure n C)
  filter_upwards [hW] with Y hY
  exact hY.add (rankOneSymmetric_posSemidef (Y.2 + r • v))

/-- Polynomial-growth smooth tests with nonnegative radial generator have a
nondecreasing expectation under the genuine integer Gaussian Gram law. -/
theorem monotoneOn_radialGramExpectation_of_generator_nonneg
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    (n : ℕ)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p))
    (hgenerator : ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
      0 ≤ symmetricRadialGenerator ((n : ℝ) + 1) v f X) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p, f (radialInput v (Real.sqrt t) Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  let μ := (wishartGramMeasure n C).prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
  let J : ℝ → ℝ := fun r => ∫ Y, f (radialInput v r Y) ∂μ
  let J₁ : ℝ → ℝ := fun r => ∫ Y, radialFirstIntegrand f v r Y ∂μ
  let J₂ : ℝ → ℝ := fun r => ∫ Y, radialSecondIntegrand f v r Y ∂μ
  let F : ℝ → ℝ := fun t => J (Real.sqrt t)
  let D : ℝ → ℝ := fun t => J₁ (Real.sqrt t) / (2 * Real.sqrt t)
  let D₂ : ℝ → ℝ := fun t =>
    (J₂ (Real.sqrt t) - J₁ (Real.sqrt t) / Real.sqrt t) / (4 * t)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C) allFiniteMoments_gaussian_norm
  have hJ (r : ℝ) : HasDerivAt J (J₁ r) r := hasDerivAt_radialExpectation hμ hf v r
  have hJ₁ (r : ℝ) : HasDerivAt J₁ (J₂ r) r := hasDerivAt_radialFirstExpectation hμ hf v r
  have heven (r : ℝ) : J (-r) = J r := radialGramExpectation_even hC n hf v r
  have hN : 0 < (n : ℝ) + 1 := by positivity
  apply Wishart.monotoneOn_of_radial_operator_nonneg_of_derivative_limit
    (N := (n : ℝ) + 1) (D := D) (D₂ := D₂) (L := J₂ 0 / 2) hN
  · exact ((continuous_iff_continuousAt.mpr fun r => (hJ r).continuousAt).comp
      Real.continuous_sqrt).continuousOn
  · intro t ht
    exact Wishart.hasDerivAt_sqrt_profile ht (hJ (Real.sqrt t))
  · intro t ht
    exact hasDerivAt_sqrt_profile_derivative ht (hJ₁ (Real.sqrt t))
  · exact Wishart.tendsto_sqrt_derivative_quotient
      (Wishart.hasDerivAt_even_zero heven (hJ 0)) (hJ₁ 0)
  · intro t ht
    have hrad := radial_gram_generator_identity hC n hf v (Real.sqrt t)
    have hnonneg : 0 ≤ ∫ Y, symmetricRadialGenerator ((n : ℝ) + 1) v f
        (radialInput v (Real.sqrt t) Y) ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_radialGramInput_posSemidef n C v (Real.sqrt t)] with Y hY
      exact hgenerator _ hY
    have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hmain : 0 ≤ J₂ (Real.sqrt t) + (n : ℝ) * J₁ (Real.sqrt t) / Real.sqrt t := by
      apply nonneg_of_mul_nonneg_right (a := Real.sqrt t)
      · convert mul_nonneg hr.le hnonneg using 1
        rw [hrad]
        dsimp [J₁, J₂]
        field_simp
        ring
      · exact hr
    dsimp [D, D₂]
    convert hmain using 1
    field_simp
    ring


end WishartVerification
end
end CanonicalSource116

section CanonicalSource117
/- Source: Wishart/GramCovarianceLimit.lean -/



/-!
# Covariance-degenerate limits for the actual Gaussian Gram law

A single fixed standard Gaussian source in twice the ambient dimension is
mapped by `[sqrt C, δ I]`. Its covariance is exactly `C + δ² I`, including at
`δ = 0`. The matrix and vector transports are polynomial in `δ`. The proved
parameter-integral theorem therefore supplies an integrable polynomial
majorant and continuity of every smooth temperate expectation at zero.
The direction of the noncentral shift is arbitrary; it need not belong to
the range of the limiting covariance.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set Topology
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace WishartVerification

variable {p r : ℕ}

def rectangularCongruenceCLM (A : Matrix (Fin p) (Fin r) ℝ) :
    SymmetricMatrix r →L[ℝ] SymmetricMatrix p :=
  LinearMap.toContinuousLinearMap (Matrix.symmetricCongruenceLinearMap A)

def rectangularCongruenceCrossCLM (A B : Matrix (Fin p) (Fin r) ℝ) :
    SymmetricMatrix r →L[ℝ] SymmetricMatrix p :=
  rectangularCongruenceCLM (A + B) - rectangularCongruenceCLM A -
    rectangularCongruenceCLM B

@[simp] theorem rectangularCongruenceCLM_apply
    (A : Matrix (Fin p) (Fin r) ℝ) (W : SymmetricMatrix r) :
    rectangularCongruenceCLM A W = Matrix.symmetricCongruenceLinearMap A W := rfl

theorem rectangular_congruence_affine_parameter
    (A B : Matrix (Fin p) (Fin r) ℝ) (δ : ℝ) (W : SymmetricMatrix r) :
    Matrix.symmetricCongruenceLinearMap (A + δ • B) W =
      rectangularCongruenceCLM A W + δ • rectangularCongruenceCrossCLM A B W +
        δ ^ 2 • rectangularCongruenceCLM B W := by
  apply Subtype.ext
  simp only [rectangularCongruenceCrossCLM, ContinuousLinearMap.sub_apply,
    rectangularCongruenceCLM_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul, pow_two]
  abel

def rectangularRadialNoiseTransport (A B : Matrix (Fin p) (Fin r) ℝ)
    (δ : ℝ) (Y : RadialInputSpace r) : RadialInputSpace p :=
  (Matrix.symmetricCongruenceLinearMap (A + δ • B) Y.1,
    (A + δ • B).toEuclideanLin Y.2)

theorem hasTemperateGrowth_rectangularRadialNoiseTransport
    (A B : Matrix (Fin p) (Fin r) ℝ) :
    (fun z : ℝ × RadialInputSpace r =>
      rectangularRadialNoiseTransport A B z.1 z.2).HasTemperateGrowth := by
  have ht := (ContinuousLinearMap.fst ℝ ℝ (RadialInputSpace r)).hasTemperateGrowth
  have hW := ((ContinuousLinearMap.fst ℝ (SymmetricMatrix r) (EuclideanSpace ℝ (Fin r))).comp
    (ContinuousLinearMap.snd ℝ ℝ (RadialInputSpace r))).hasTemperateGrowth
  have hz := ((ContinuousLinearMap.snd ℝ (SymmetricMatrix r) (EuclideanSpace ℝ (Fin r))).comp
    (ContinuousLinearMap.snd ℝ ℝ (RadialInputSpace r))).hasTemperateGrowth
  have hfirst := ((rectangularCongruenceCLM A).hasTemperateGrowth.comp hW).add
    (ht.smul ((rectangularCongruenceCrossCLM A B).hasTemperateGrowth.comp hW))
  have hfirst' := hfirst.add
    ((ht.pow 2).smul ((rectangularCongruenceCLM B).hasTemperateGrowth.comp hW))
  have hsecond := (A.toEuclideanLin.toContinuousLinearMap.hasTemperateGrowth.comp hz).add
    (ht.smul (B.toEuclideanLin.toContinuousLinearMap.hasTemperateGrowth.comp hz))
  have h := hasTemperateGrowth_prodMk hfirst' hsecond
  have heq : (fun z : ℝ × RadialInputSpace r =>
      (rectangularCongruenceCLM A z.2.1 +
        z.1 • rectangularCongruenceCrossCLM A B z.2.1 +
        z.1 ^ 2 • rectangularCongruenceCLM B z.2.1,
       A.toEuclideanLin z.2.2 + z.1 • B.toEuclideanLin z.2.2)) =
      (fun z => rectangularRadialNoiseTransport A B z.1 z.2) := by
    funext z
    apply Prod.ext
    · exact (rectangular_congruence_affine_parameter A B z.1 z.2.1).symm
    · simp only [rectangularRadialNoiseTransport, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply]
  change ((fun z : ℝ × RadialInputSpace r =>
      (rectangularCongruenceCLM A z.2.1 +
        z.1 • rectangularCongruenceCrossCLM A B z.2.1 +
        z.1 ^ 2 • rectangularCongruenceCLM B z.2.1,
       A.toEuclideanLin z.2.2 + z.1 • B.toEuclideanLin z.2.2))).HasTemperateGrowth at h
  rw [heq] at h
  exact h

theorem map_rectangularRadialNoiseTransport (n : ℕ)
    (A B : Matrix (Fin p) (Fin r) ℝ) (δ : ℝ) :
    ((wishartGramMeasure n (1 : Matrix (Fin r) (Fin r) ℝ)).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) 1)).map
        (rectangularRadialNoiseTransport A B δ) =
      (wishartGramMeasure n ((A + δ • B) * (A + δ • B)ᵀ)).prod
        (multivariateGaussian 0 ((A + δ • B) * (A + δ • B)ᵀ)) := by
  let T := A + δ • B
  have hgaussian : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) 1).map
      T.toEuclideanLin = multivariateGaussian 0 (T * Tᵀ) := by
    simpa only [map_zero, add_zero, Matrix.mul_one] using
      map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin r))
        Matrix.PosSemidef.one T 0
  have hgram : (wishartGramMeasure n (1 : Matrix (Fin r) (Fin r) ℝ)).map
      (Matrix.symmetricCongruenceLinearMap T) = wishartGramMeasure n (T * Tᵀ) := by
    simpa only [Matrix.mul_one] using
      map_symmetricCongruenceLinearMap_wishartGramMeasure n T Matrix.PosSemidef.one
  change Measure.map (Prod.map (Matrix.symmetricCongruenceLinearMap T) T.toEuclideanLin) _ = _
  rw [← Measure.map_prod_map _ _ (LinearMap.continuous_of_finiteDimensional _).measurable
    (LinearMap.continuous_of_finiteDimensional T.toEuclideanLin).measurable, hgram, hgaussian]

def covarianceRegularizationBase (C : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin (p + p)) ℝ :=
  (Matrix.fromCols (CFC.sqrt C) 0).submatrix id finSumFinEquiv.symm

def covarianceRegularizationNoise (p : ℕ) : Matrix (Fin p) (Fin (p + p)) ℝ :=
  (Matrix.fromCols 0 1).submatrix id finSumFinEquiv.symm

theorem covarianceRegularization_covariance
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) (δ : ℝ) :
    (covarianceRegularizationBase C + δ • covarianceRegularizationNoise p) *
      (covarianceRegularizationBase C + δ • covarianceRegularizationNoise p)ᵀ =
        C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have hsqrt : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian.eq
  simp only [covarianceRegularizationBase, covarianceRegularizationNoise,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows,
    Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.submatrix_id_id,
    hsqrt, CFC.sqrt_mul_sqrt_self C hC.nonneg, smul_zero, pow_two]

theorem covarianceRegularization_posDef
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef := by
  have h := (Matrix.PosDef.one.smul (sq_pos_of_pos hδ)).add_posSemidef hC
  simpa only [add_comm] using h

/-- Covariance regularization preserves the genuine expectation and is
continuous at zero. All domination is derived from joint temperate growth. -/
theorem continuous_radialGram_covarianceRegularization
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) (n : ℕ)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Continuous (fun δ : ℝ => ∫ Y : RadialInputSpace p, f (radialInput v s Y)
      ∂(wishartGramMeasure n (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))).prod
        (multivariateGaussian 0 (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)))) := by
  let A := covarianceRegularizationBase C
  let B := covarianceRegularizationNoise p
  let μ := (wishartGramMeasure n (1 : Matrix (Fin (p + p)) (Fin (p + p)) ℝ)).prod
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin (p + p))) 1)
  let F : ℝ × RadialInputSpace (p + p) → ℝ := fun z =>
    f (radialInput v s (rectangularRadialNoiseTransport A B z.1 z.2))
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace (p + p) => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_gram_norm n 1) allFiniteMoments_gaussian_norm
  have hF : F.HasTemperateGrowth := hf.comp
    ((hasTemperateGrowth_radialInput_slice v s).comp
      (hasTemperateGrowth_rectangularRadialNoiseTransport A B))
  have heq (δ : ℝ) : (∫ Y, F (δ, Y) ∂μ) =
      ∫ Y : RadialInputSpace p, f (radialInput v s Y)
        ∂(wishartGramMeasure n (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))).prod
          (multivariateGaussian 0 (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))) := by
    have hmap := map_rectangularRadialNoiseTransport n A B δ
    rw [covarianceRegularization_covariance hC] at hmap
    have hm : Measurable (rectangularRadialNoiseTransport A B δ) :=
      ((hasTemperateGrowth_rectangularRadialNoiseTransport A B).1.continuous.comp
        (by fun_prop : Continuous (fun Y : RadialInputSpace (p + p) => (δ, Y)))).measurable
    have hi := integral_map (μ := μ) hm.aemeasurable
      (hf.1.continuous.comp (hasTemperateGrowth_radialInput_slice v s).1.continuous).aestronglyMeasurable
    rw [hmap] at hi
    exact hi.symm
  have hcont : Continuous (fun δ : ℝ => ∫ Y, F (δ, Y) ∂μ) :=
    continuous_iff_continuousAt.mpr fun δ => (hasDerivAt_integral_temperate hμ hF δ).continuousAt
  exact hcont.congr heq

/-- The integer-degree radial theorem for every positive semidefinite
covariance, including singular covariance and arbitrary noncentral direction. -/
theorem monotoneOn_radialGramExpectation_of_generator_nonneg_posSemidef
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    (n : ℕ) {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p))
    (hgenerator : ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
      0 ≤ symmetricRadialGenerator ((n : ℝ) + 1) v f X) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p, f (radialInput v (Real.sqrt t) Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  intro s hs t ht hst
  let δ (l : ℕ) : ℝ := 1 / ((l : ℝ) + 1)
  have hδ : ∀ l, 0 < δ l := fun l => by dsimp [δ]; positivity
  have hlim : Tendsto δ atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hscont := continuous_radialGram_covarianceRegularization hC n hf v (Real.sqrt s)
  have htcont := continuous_radialGram_covarianceRegularization hC n hf v (Real.sqrt t)
  have hsconv := hscont.continuousAt.tendsto.comp hlim
  have htconv := htcont.continuousAt.tendsto.comp hlim
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_smul, add_zero] at hsconv htconv
  exact le_of_tendsto_of_tendsto hsconv htconv (Filter.Eventually.of_forall fun l =>
    monotoneOn_radialGramExpectation_of_generator_nonneg
      (covarianceRegularization_posDef hC (hδ l)) n hf v hgenerator hs ht hst)

end WishartVerification
end
end CanonicalSource117

section CanonicalSource118
/- Source: Wishart/GramFiniteOuterComparison.lean -/



/-!
# Finite determinant outer approximations under integer Gram noise

All limits are taken under the actual Gram/Gaussian product measure.  The
internal smooth-comparison input is instantiated from the proved radial
identity, including the separate covariance-degenerate limit.  The finite
approximations are valid at singular matrices; no positive-domain limit is
used to prescribe an outer function's value at a zero determinant.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set Topology Matrix
open scoped BigOperators ENNReal Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem monotoneOn_radialGram_affineMaximumProduct_of_smoothComparison
    (n : ℕ) (C : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (hcomparison : ∀ (f : SymmetricMatrix p → ℝ), f.HasTemperateGrowth →
      (∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
        0 ≤ symmetricRadialGenerator ((n : ℝ) + 1) v f X) →
      MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p,
        f (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0))
    {ε : ℝ} (hε : 0 < ε) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j) (hsize : ∀ i, k i ≤ n) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p,
      affineMaximumProduct ε k B M a b (radialInput v (Real.sqrt t) Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  have hN (i : κ) : min (k i : ℝ) (p : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have hi : min (k i : ℝ) (p : ℝ) ≤ (n : ℝ) :=
      (min_le_left _ _).trans (Nat.cast_le.mpr (hsize i))
    linarith
  have hm (l : ℕ) := hcomparison
    (regularizedPowerMeanProduct ε ((l : ℝ) + 1) k B M a b)
    (hasTemperateGrowth_regularizedPowerMeanProduct hε (by positivity) k B M a b ha)
    (fun X hX => regularizedPowerMeanProduct_generator_nonneg hε (by positivity)
      k B M a b hB ha hX hN v)
  have hμ := allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C)
    (allFiniteMoments_gaussian_norm (μ := multivariateGaussian 0 C))
  have hlimit (r : ℝ) := regularizedPowerMeanProduct_integral_tendsto hε k B M a b hB
    (radialInput v r) (ae_radialGramInput_posSemidef n C v r)
    (monomialMoments_of_temperate_matrix hμ
      (hasTemperateGrowth_radialInput_slice v r) ε k B M a b ha)
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlimit (Real.sqrt s)) (hlimit (Real.sqrt t))
    (Filter.Eventually.of_forall fun l => hm l hs ht hst)

theorem monotoneOn_radialGram_finiteOuterProduct_of_smoothComparison
    (n : ℕ) (C : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (hcomparison : ∀ (f : SymmetricMatrix p → ℝ), f.HasTemperateGrowth →
      (∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
        0 ≤ symmetricRadialGenerator ((n : ℝ) + 1) v f X) →
      MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p,
        f (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0))
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j) (hsize : ∀ i, k i ≤ n) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p,
      affineMaximumProduct 0 k B M a b (radialInput v (Real.sqrt t) Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  have hμ := allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C)
    (allFiniteMoments_gaussian_norm (μ := multivariateGaussian 0 C))
  have hlimit (r : ℝ) := affineMaximumProduct_regularization_integral_tendsto hμ
    (hasTemperateGrowth_radialInput_slice v r) (ae_radialGramInput_posSemidef n C v r)
    k B M a b hB ha
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlimit (Real.sqrt s)) (hlimit (Real.sqrt t))
    (Filter.Eventually.of_forall fun l =>
      monotoneOn_radialGram_affineMaximumProduct_of_smoothComparison n C v hcomparison
        (determinantRegularization_pos l) k B M a b hB ha hsize hs ht hst)

/-- Positive-definite covariance is already supplied by the actual integer
radial identity. No lower bound relating n to the ambient dimension remains. -/
theorem monotoneOn_radialGram_finiteOuterProduct
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef) (n : ℕ)
    (v : EuclideanSpace ℝ (Fin p)) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j) (hsize : ∀ i, k i ≤ n) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p,
      affineMaximumProduct 0 k B M a b (radialInput v (Real.sqrt t) Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0) :=
  monotoneOn_radialGram_finiteOuterProduct_of_smoothComparison n C v
    (fun _ hf hg => monotoneOn_radialGramExpectation_of_generator_nonneg hC n hf v hg)
    k B M a b hB ha hsize

/-- The finite approximation comparison for every covariance, including a
singular Schur complement in the conditional Gaussian model. -/
theorem monotoneOn_radialGram_finiteOuterProduct_posSemidef
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) (n : ℕ)
    (v : EuclideanSpace ℝ (Fin p)) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j) (hsize : ∀ i, k i ≤ n) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p,
      affineMaximumProduct 0 k B M a b (radialInput v (Real.sqrt t) Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) (Ici 0) :=
  monotoneOn_radialGram_finiteOuterProduct_of_smoothComparison n C v
    (fun _ hf hg =>
      monotoneOn_radialGramExpectation_of_generator_nonneg_posSemidef hC n hf v hg)
    k B M a b hB ha hsize

end WishartVerification
end
end CanonicalSource118

section CanonicalSource119
/- Source: Wishart/GramOuterRegressionMonotonicity.lean -/



/-!
# Conditional determinant comparison for singular Gram noise

One shifted Gaussian row is separated from the others. The background has
exactly the stated natural number of Gram rows, including zero. All other
shifted rows become a fixed positive semidefinite offset. The covariance may
be singular, and no mean direction is required to lie in its range.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem monotoneOn_gramShiftedRows_finiteOuter_coordinate
    {q p : ℕ} (d : ℕ) {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, k i ≤ d)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) (c : Fin q) :
    MonotoneOn (fun t : ℝ => ∫ x,
      affineMaximumProduct 0 k B M a b (shiftedRowsSym v (Function.update lam c t) x)
        ∂gaussianResidualMeasure q C (wishartGramMeasure d C)) (Set.Ici 0) := by
  cases q with
  | zero => exact Fin.elim0 c
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
    let μ := Measure.pi (fun _ : Fin q => γ)
    let ρ := (wishartGramMeasure d C).prod γ
    let A (z : Fin q → EuclideanSpace ℝ (Fin p)) :=
      rowBackground (v ∘ c.succAbove) (lam ∘ c.succAbove) z
    let F (t : ℝ) (y : (Fin q → EuclideanSpace ℝ (Fin p)) × RadialInputSpace p) :=
      affineMaximumProduct 0 k B M a b (A y.1 + radialInput (v c) (Real.sqrt t) y.2)
    have hsplit := measurePreserving_separateRegressionRow C (wishartGramMeasure d C) c
    have hFmeas (t : ℝ) : Measurable (F t) := by
      apply (continuous_affineMaximumProduct 0 k B M a b ha).measurable.comp
      apply Measurable.add
      · exact (measurable_rowBackground _ _).comp measurable_fst
      · exact ((hasTemperateGrowth_radialInput_slice (v c) (Real.sqrt t)).1.continuous.measurable).comp
          measurable_snd
    have hFcomp (t : ℝ) : F t ∘ separateRegressionRow c =
        (fun x => affineMaximumProduct 0 k B M a b
          (shiftedRowsSym v (Function.update lam c t) x)) := by
      funext x
      dsimp only [F, A, Function.comp_apply]
      rw [shiftedRowsSym_separate]
    have hFi (t : ℝ) : Integrable (F t) (μ.prod ρ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hFmeas t).aestronglyMeasurable
        hsplit.measurable.aemeasurable).mpr
      rw [hFcomp]
      apply HasAllFiniteMoments.integrable
      apply allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
      intro i j
      simpa only [coe_shiftedRowsSym] using
        allFiniteMoments_shiftedRowsGram_entry C (allFiniteMoments_gram_entry d C)
          v (Function.update lam c t) i j
    have heq (t : ℝ) :
        (∫ x, affineMaximumProduct 0 k B M a b
          (shiftedRowsSym v (Function.update lam c t) x)
          ∂gaussianResidualMeasure (q + 1) C (wishartGramMeasure d C)) =
        ∫ z, ∫ Y, F t (z, Y) ∂ρ ∂μ := by
      rw [← integral_prod _ (hFi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hFmeas t).aestronglyMeasurable]
      exact congrArg (fun f => ∫ x, f x
        ∂gaussianResidualMeasure (q + 1) C (wishartGramMeasure d C)) (hFcomp t).symm
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hFi s).integral_prod_left (hFi t).integral_prod_left
    apply Filter.Eventually.of_forall
    intro z
    have hBz : ∀ i,
        (B i + (M i)ᵀ * (A z : Matrix (Fin p) (Fin p) ℝ) * M i).PosSemidef := by
      intro i
      apply (hB i).add
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (rowBackground_posSemidef _ _ z).conjTranspose_mul_mul_same (M i)
    simpa only [F, affineMaximumProduct_add_offset] using
      monotoneOn_radialGram_finiteOuterProduct_posSemidef hC d (v c) k
        (fun i => B i + (M i)ᵀ * (A z : Matrix (Fin p) (Fin p) ℝ) * M i)
        M a b hBz ha hsize hs ht hst

theorem monotoneOn_gramShiftedRows_finiteOuter
    {q p : ℕ} (d : ℕ) {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, k i ≤ d) (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      affineMaximumProduct 0 k B M a b (shiftedRowsSym v lam x)
        ∂gaussianResidualMeasure q C (wishartGramMeasure d C))
      (Set.Ici (0 : Fin q → ℝ)) :=
  monotoneOn_nonnegative_pi_of_update _ fun lam c =>
    monotoneOn_gramShiftedRows_finiteOuter_coordinate d hC k B M a b hB ha hsize v lam c

end Wishart
end
end CanonicalSource119
