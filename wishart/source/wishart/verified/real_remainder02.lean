module

public import wishart.verified.real_remainder01

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder02/manifest.json. -/

@[expose] public section

section CanonicalSource10
/- Source: Wishart/CompressionRankBound.lean -/



/-!
# The smaller-dimension trace bound

The sandwich `sqrt V * A * sqrt V` is positive semidefinite and satisfies
`B - B² ≥ 0`. Its eigenvalues consequently lie in `[0,1]`. This gives the
ambient-dimension bound, which is combined with the compression-dimension
bound without any additional nonsingularity assumption on `V`.
-/

noncomputable section

open Matrix Filter Topology
open scoped MatrixOrder RealInnerProductSpace BigOperators

namespace WishartVerification

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

theorem eigenvalue_le_one_of_square_contraction {B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBB : (B - B * B).PosSemidef) (i : n) :
    hB.isHermitian.eigenvalues i ≤ 1 := by
  let w : EuclideanSpace ℝ n := hB.isHermitian.eigenvectorBasis i
  have hw : (fun j => w j) ⬝ᵥ (fun j => w j) = 1 := by
    calc
      _ = ⟪w, w⟫ := by simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      _ = 1 := by simp [w, real_inner_self_eq_norm_sq]
  have he : B *ᵥ (fun j => w j) = hB.isHermitian.eigenvalues i • (fun j => w j) :=
    hB.isHermitian.mulVec_eigenvectorBasis i
  have h := hBB.dotProduct_mulVec_nonneg (fun j => w j)
  simp only [star_trivial, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    he, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hw] at h
  have hlambda := hB.eigenvalues_nonneg i
  nlinarith

theorem trace_le_card_of_square_contraction {B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBB : (B - B * B).PosSemidef) :
    B.trace ≤ Fintype.card n := by
  rw [hB.isHermitian.trace_eq_sum_eigenvalues]
  calc
    _ ≤ ∑ _i : n, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => eigenvalue_le_one_of_square_contraction hB hBB i)
    _ = _ := by simp

theorem compressed_trace_le_ambient_card {Q : Matrix k k ℝ}
    (hQ : Q.PosDef) (M : Matrix n k ℝ) {V : Matrix n n ℝ}
    (hV : V.PosSemidef) (hQT : (Q - Mᵀ * V * M).PosSemidef) :
    Matrix.trace ((M * Q⁻¹ * Mᵀ) * V) ≤ Fintype.card n := by
  let A := M * Q⁻¹ * Mᵀ
  let R := CFC.sqrt V
  let B := R * A * R
  have hA : A.PosSemidef := compressed_inverse_posSemidef hQ M
  have hR : R.PosSemidef := Matrix.LE.le.posSemidef (CFC.sqrt_nonneg V)
  have hRR : R * R = V := CFC.sqrt_mul_sqrt_self V hV.nonneg
  have hB : B.PosSemidef := by
    simpa only [hR.isHermitian.eq] using hA.mul_mul_conjTranspose_same R
  have hcontract : (A - A * V * A).PosSemidef :=
    compressed_inverse_contraction hQ M V hQT
  have hBB : (B - B * B).PosSemidef := by
    have h := hcontract.mul_mul_conjTranspose_same R
    rw [hR.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul] at h
    have hsquare : B * B = R * (A * V * A) * R := by
      calc
        B * B = R * A * (R * R) * A * R := by
          dsimp [B]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hRR]; simp only [Matrix.mul_assoc]
    simpa only [hsquare] using h
  have htrace := trace_le_card_of_square_contraction hB hBB
  simpa only [B, R, hV.trace_sqrt_mul_mul_sqrt] using htrace

theorem compressed_trace_le_min_card {Q : Matrix k k ℝ}
    (hQ : Q.PosDef) (M : Matrix n k ℝ) {V : Matrix n n ℝ}
    (hV : V.PosSemidef) (hQT : (Q - Mᵀ * V * M).PosSemidef) :
    Matrix.trace ((M * Q⁻¹ * Mᵀ) * V) ≤
      min (Fintype.card k : ℝ) (Fintype.card n : ℝ) :=
  le_min (compressed_trace_le_card hQ M V hQT)
    (compressed_trace_le_ambient_card hQ M hV hQT)

variable {p : ℕ}

theorem symmetricDirectionalGenerator_compressionLog_nonneg_min
    {ε : ℝ} (hε : 0 < ε) {B : Matrix k k ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {N : ℝ} (hN : min (Fintype.card k : ℝ) (p : ℝ) + 1 ≤ N)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricDirectionalGenerator N v (compressionLog ε B M) X := by
  have hQ := regularizedCompression_posDef hε hB M hX
  let A := M * (regularizedCompression ε B M X)⁻¹ * Mᵀ
  have hA : A.PosSemidef := compressed_inverse_posSemidef hQ M
  have hQT : (regularizedCompression ε B M X -
      Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M).PosSemidef := by
    have he : regularizedCompression ε B M X -
        Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M = B + ε • 1 := by
      dsimp [regularizedCompression, compressionCLM_apply]
      abel
    rw [he]
    exact hB.add (Matrix.PosSemidef.one.smul hε.le)
  have hcontract := compressed_inverse_contraction hQ M _ hQT
  have htrace : Matrix.trace (A * (X : Matrix (Fin p) (Fin p) ℝ)) ≤
      min (Fintype.card k : ℝ) (p : ℝ) := by
    simpa only [Fintype.card_fin] using compressed_trace_le_min_card hQ M hX hQT
  have hbound := logarithmic_generator_lower_bound hA hcontract htrace N (fun i => v i)
  rw [symmetricDirectionalGenerator_compressionLog ε B M hQ N v]
  apply le_trans _ hbound
  apply mul_nonneg
  · have : 0 ≤ N - min (Fintype.card k : ℝ) (p : ℝ) - 1 := by linarith
    positivity
  · simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (fun i => v i)

/-- The full smaller-dimension version used after reducing a singular
covariance and a transverse mean to an ambient space of dimension `r+1`. -/
theorem regularizedCompressionProduct_generator_nonneg_min {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    {N : ℝ} (hN : ∀ i, min ((D i).size : ℝ) (p : ℝ) + 1 ≤ N)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricRadialGenerator N v (regularizedCompressionProduct ε D) X := by
  let f : ι → SymmetricMatrix p → ℝ := fun i => compressionLog ε (D i).offset (D i).linear
  have hunit (i : ι) : IsUnit (regularizedCompression ε (D i).offset (D i).linear X).det :=
    isUnit_iff_ne_zero.mpr (regularizedCompression_posDef hε (hB i) (D i).linear hX).det_pos.ne'
  have hf := compressionLogSum_differentiable_near ε D hunit
  have hD (i : ι) (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (f i) Y H) X :=
    (hasFDerivAt_compressionLog_direction ε (D i).offset (D i).linear (hunit i) H).differentiableAt
  have hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (compressionLogSum ε D) Y := by
    filter_upwards [hf] with Y hY
    exact DifferentiableAt.fun_sum (fun i _ => (hY i).const_mul (D i).exponent)
  have hgD (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (compressionLogSum ε D) Y H) X := by
    have heq : (fun Y => fderiv ℝ (compressionLogSum ε D) Y H) =ᶠ[𝓝 X]
        (fun Y => ∑ i, (D i).exponent * fderiv ℝ (f i) Y H) :=
      hf.mono fun Y hY => fderiv_linear_combination_apply _ f hY H
    exact heq.differentiableAt_iff.mpr
      (DifferentiableAt.fun_sum (fun i _ => (hD i H).const_mul (D i).exponent))
  rw [symmetricRadialGenerator_eq_directional
    (hasTemperateGrowth_regularizedCompressionProduct hε D),
    symmetricDirectionalGenerator_congr
      (regularizedCompressionProduct_eventually_exp hε D hB hX),
    symmetricDirectionalGenerator_exp hg hgD]
  apply mul_nonneg (Real.exp_pos _).le
  apply add_nonneg _ (symmetricCarreDuChamp_nonneg _ hX v)
  change 0 ≤ symmetricDirectionalGenerator N v (fun Y => ∑ i, (D i).exponent * f i Y) X
  rw [symmetricDirectionalGenerator_linear_combination _ f hf hD]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hη i)
    (symmetricDirectionalGenerator_compressionLog_nonneg_min hε (hB i) (D i).linear hX
      (by simpa using hN i) v)

end WishartVerification
end
end CanonicalSource10

section CanonicalSource11
/- Source: Wishart/ScalarRadialCompression.lean -/



/-!
# Unregularized determinant products in transverse regression

The regularization limit is justified by an explicit common polynomial
envelope on the actual Gaussian/Wishart noise source.  Thus the result concerns
ordinary determinant powers, including singular compressed matrices.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Filter Set Topology
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem hasTemperateGrowth_scalar_regularized_det {r : ℕ}
    {k : Type*} [Fintype k] [DecidableEq k]
    (B : Matrix k k ℝ) (M : Matrix (Fin (1 + r)) k ℝ) (s : ℝ) :
    (fun y : ℝ × ScalarRegressionNoise r =>
      (regularizedCompression y.1 B M (scalarRadialMatrix s y.2)).det).HasTemperateGrowth := by
  let F : ℝ × RadialInputSpace (1 + r) → ℝ := fun y =>
    (regularizedCompression y.1 B M (radialInput (scalarTransverseAxis r) s y.2)).det
  let G : ℝ × ScalarRegressionNoise r → ℝ × RadialInputSpace (1 + r) :=
    fun y => (y.1, scalarRadialDataCLM r y.2)
  have hF : F.HasTemperateGrowth :=
    hasTemperateGrowth_radial_regularized_det (p := 1 + r) B M
      (scalarTransverseAxis r) s
  have hG : G.HasTemperateGrowth := hasTemperateGrowth_scalarRadialDataParameter r
  have hcomp : (F ∘ G).HasTemperateGrowth := hF.comp hG
  have heq : F ∘ G = (fun y : ℝ × ScalarRegressionNoise r =>
      (regularizedCompression y.1 B M (scalarRadialMatrix s y.2)).det) := by
    funext y
    rfl
  rw [heq] at hcomp
  exact hcomp

theorem scalar_regularized_product_integral_tendsto {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {ι : Type*} [Fintype ι]
    (D : ι → CompressionData (1 + r))
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent) (s : ℝ) :
    Tendsto (fun n => ∫ x : ScalarRegressionNoise r,
      regularizedCompressionProduct (determinantRegularization n) D (scalarRadialMatrix s x)
        ∂scalarRegressionNoiseMeasure N r) atTop
      (𝓝 (∫ x : ScalarRegressionNoise r, compressionProduct D (scalarRadialMatrix s x)
        ∂scalarRegressionNoiseMeasure N r)) := by
  classical
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  let μ := scalarRegressionNoiseMeasure N r
  have hμ := allFiniteNormMoments_scalarRegressionNoise hN
  have hpoly (i : ι) := norm_temperate_uniform_parameter
    (hasTemperateGrowth_scalar_regularized_det (D i).offset (D i).linear s) 0
  choose k A hA hbound using hpoly
  let bound : ScalarRegressionNoise r → ℝ := fun x =>
    ∏ i, (A i * (1 + ‖x‖) ^ k i) ^ (D i).exponent
  have hb : Integrable bound μ := by
    apply HasAllFiniteMoments.integrable
    apply HasAllFiniteMoments.finset_prod
    intro i hi
    have hpow := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).rpow
      (show 0 ≤ (k i : ℝ) by positivity)
    have hAi : HasAllFiniteMoments
        (fun x : ScalarRegressionNoise r => A i * (1 + ‖x‖) ^ k i) μ := by
      simpa only [Real.rpow_natCast] using hpow.const_mul (A i)
    exact hAi.rpow (hη i)
  refine tendsto_integral_of_dominated_convergence bound ?_ hb ?_ ?_
  · intro n
    exact ((hasTemperateGrowth_regularizedCompressionProduct (determinantRegularization_pos n) D).comp
      ((hasTemperateGrowth_scalarRadialMatrix r).comp
        (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
          Function.HasTemperateGrowth.id))).1.continuous.aestronglyMeasurable
  · intro n
    filter_upwards [ae_scalarRadialMatrix_posSemidef N s] with x hx
    unfold regularizedCompressionProduct bound
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      rw [smoothRegularizedDetPower_eq (determinantRegularization_pos n)
        (D i).exponent (hB i) (D i).linear hx]
      have hd : 0 ≤ (regularizedCompression (determinantRegularization n)
          (D i).offset (D i).linear (scalarRadialMatrix s x)).det :=
        (regularizedCompression_posDef (determinantRegularization_pos n)
          (hB i) (D i).linear hx).det_pos.le
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hd _)]
      apply Real.rpow_le_rpow hd _ (hη i)
      have heps : determinantRegularization n ∈ Icc ((0 : ℝ) - 1) (0 + 1) :=
        ⟨by linarith [determinantRegularization_pos n],
          by simpa using determinantRegularization_le_one n⟩
      simpa only [Real.norm_of_nonneg hd] using hbound i _ heps x
  · filter_upwards [ae_scalarRadialMatrix_posSemidef N s] with x hx
    exact tendsto_regularizedCompressionProduct D hB hη hx

/-- The determinant-product comparison in the transverse source. The finite
compression family and every real exponent are unrestricted apart from the
displayed generator size bound. -/
theorem monotoneOn_scalarRadial_compressionProduct {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {ι : Type*} [Fintype ι]
    (D : ι → CompressionData (1 + r))
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, ((D i).size : ℝ) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ x : ScalarRegressionNoise r,
      compressionProduct D (scalarRadialMatrix (Real.sqrt t) x)
        ∂scalarRegressionNoiseMeasure N r) (Ici 0) := by
  intro s hs t ht hst
  have hmono (n : ℕ) := monotoneOn_scalarRadialProfile_of_generator_nonneg hN
    (hasTemperateGrowth_regularizedCompressionProduct (determinantRegularization_pos n) D)
    (fun X hX => regularizedCompressionProduct_generator_nonneg (determinantRegularization_pos n)
      D hB hη hsize hX (scalarTransverseAxis r))
  exact le_of_tendsto_of_tendsto
    (scalar_regularized_product_integral_tendsto hN D hB hη (Real.sqrt s))
    (scalar_regularized_product_integral_tendsto hN D hB hη (Real.sqrt t))
    (Filter.Eventually.of_forall fun n => hmono n hs ht hst)

/-- The rank-refined transverse comparison. The effective conditional matrix
has dimension r+1, so large compressions require only that dimension rather
than their number of columns. This is the min(k_i,r+1) bound of Lemma 3.1. -/
theorem monotoneOn_scalarRadial_compressionProduct_min {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {ι : Type*} [Fintype ι]
    (D : ι → CompressionData (1 + r))
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((D i).size : ℝ) (((1 + r : ℕ) : ℝ)) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ x : ScalarRegressionNoise r,
      compressionProduct D (scalarRadialMatrix (Real.sqrt t) x)
        ∂scalarRegressionNoiseMeasure N r) (Ici 0) := by
  intro s hs t ht hst
  have hmono (n : ℕ) := monotoneOn_scalarRadialProfile_of_generator_nonneg hN
    (hasTemperateGrowth_regularizedCompressionProduct (determinantRegularization_pos n) D)
    (fun X hX => regularizedCompressionProduct_generator_nonneg_min
      (determinantRegularization_pos n) D hB hη hsize hX (scalarTransverseAxis r))
  exact le_of_tendsto_of_tendsto
    (scalar_regularized_product_integral_tendsto hN D hB hη (Real.sqrt s))
    (scalar_regularized_product_integral_tendsto hN D hB hη (Real.sqrt t))
    (Filter.Eventually.of_forall fun n => hmono n hs ht hst)

end Wishart
end
end CanonicalSource11

section CanonicalSource12
/- Source: Wishart/TransverseCompressionTransport.lean -/



/-!
# Rectangular transport of the real-shape radial comparison

The rectangular map has first column v and remaining columns L. It need not
be injective. The source remains the genuine independent standard Gaussian
and W_r(N−1,I) pair; singular ambient covariance is represented by its actual
linear image, without applying a nonsingular density to a singular scale.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def radialLiftMatrix {p r : ℕ} (v : EuclideanSpace ℝ (Fin p))
    (L : Matrix (Fin p) (Fin r) ℝ) : Matrix (Fin p) (Fin (1 + r)) ℝ :=
  (Matrix.fromCols (Matrix.of (fun i (_ : Fin 1) => v i)) L).submatrix
    (Equiv.refl (Fin p)) finSumFinEquiv.symm

@[simp] theorem radialLiftMatrix_castAdd {p r : ℕ}
    (v : EuclideanSpace ℝ (Fin p)) (L : Matrix (Fin p) (Fin r) ℝ)
    (i : Fin p) (a : Fin 1) : radialLiftMatrix v L i (Fin.castAdd r a) = v i := by
  simp [radialLiftMatrix]

@[simp] theorem radialLiftMatrix_natAdd {p r : ℕ}
    (v : EuclideanSpace ℝ (Fin p)) (L : Matrix (Fin p) (Fin r) ℝ)
    (i : Fin p) (a : Fin r) : radialLiftMatrix v L i (Fin.natAdd 1 a) = L i a := by
  simp [radialLiftMatrix]

theorem radialLiftMatrix_noise {p r : ℕ}
    (v : EuclideanSpace ℝ (Fin p)) (L : Matrix (Fin p) (Fin r) ℝ) :
    radialLiftMatrix v L * scalarNoiseMatrix r = L := by
  simp only [radialLiftMatrix, scalarNoiseMatrix, Matrix.submatrix_mul_equiv,
    Matrix.fromCols_mul_fromRows, Matrix.mul_zero, Matrix.mul_one, zero_add,
    Equiv.coe_refl, Matrix.submatrix_id_id]

theorem radialLiftMatrix_axis {p r : ℕ}
    (v : EuclideanSpace ℝ (Fin p)) (L : Matrix (Fin p) (Fin r) ℝ) :
    (radialLiftMatrix v L).toEuclideanLin (scalarTransverseAxis r) = v := by
  rw [scalarTransverseAxis_eq_coordinate]
  apply PiLp.ext
  intro i
  simp [Matrix.toLpLin_apply, coordinateVector, Matrix.mulVec_single_one, Matrix.col_apply]

theorem symmetricCongruence_rankOne {p r : ℕ}
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin r)) :
    Matrix.symmetricCongruenceLinearMap L (rankOneSymmetric v) =
      rankOneSymmetric (L.toEuclideanLin v) := by
  apply Subtype.ext
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply, coe_rankOneSymmetric, coe_rankOneSymmetric,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  rfl

def linearRadialInput {p r : ℕ} (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : ScalarRegressionNoise r) :
    SymmetricMatrix p :=
  Matrix.symmetricCongruenceLinearMap L x.2 +
    rankOneSymmetric (L.toEuclideanLin x.1 + s • v)

@[fun_prop] theorem measurable_linearRadialInput {p r : ℕ}
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Measurable (linearRadialInput L v s) := by
  exact ((LinearMap.continuous_of_finiteDimensional
    (Matrix.symmetricCongruenceLinearMap L)).measurable.comp measurable_snd).add
    ((hasTemperateGrowth_rankOneSymmetric (p := p)).1.continuous.measurable.comp
      (((L.toEuclideanLin.toContinuousLinearMap).continuous.measurable.comp measurable_fst).add
        measurable_const))

/-- The complete conditional matrix is a literal rectangular congruence of
the scalar-regression matrix. Both residual and rank-one terms agree. -/
theorem radialLiftMatrix_scalarRadialMatrix {p r : ℕ}
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (x : ScalarRegressionNoise r) :
    Matrix.symmetricCongruenceLinearMap (radialLiftMatrix v L) (scalarRadialMatrix s x) =
      linearRadialInput L v s x := by
  simp only [scalarRadialMatrix, radialInput, scalarRadialDataCLM_apply, map_add,
    symmetricCongruence_rankOne, map_smul, radialLiftMatrix_axis]
  rw [← LinearMap.comp_apply, ← Matrix.symmetricCongruenceLinearMap_mul, radialLiftMatrix_noise]
  have hlin : (radialLiftMatrix v L).toEuclideanLin
      ((scalarNoiseMatrix r).toEuclideanLin x.1) = L.toEuclideanLin x.1 := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, radialLiftMatrix_noise]
  rw [hlin]
  rfl

def pullbackCompressionData {p r : ℕ} {ι : Type*}
    (D : ι → CompressionData p) (L : Matrix (Fin p) (Fin r) ℝ) :
    ι → CompressionData r :=
  fun i => ⟨(D i).size, (D i).offset, Lᵀ * (D i).linear, (D i).exponent⟩

theorem compressionProduct_congruence {p r : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → CompressionData p) (L : Matrix (Fin p) (Fin r) ℝ)
    (X : SymmetricMatrix r) :
    compressionProduct D (Matrix.symmetricCongruenceLinearMap L X) =
      compressionProduct (pullbackCompressionData D L) X := by
  apply Finset.prod_congr rfl
  intro i hi
  change ((D i).offset + (D i).linearᵀ *
      (Matrix.symmetricCongruenceLinearMap L X : Matrix (Fin p) (Fin p) ℝ) *
        (D i).linear).det ^ (D i).exponent =
    ((D i).offset + (Lᵀ * (D i).linear)ᵀ *
      (X : Matrix (Fin r) (Fin r) ℝ) * (Lᵀ * (D i).linear)).det ^ (D i).exponent
  simp only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Real-shape mean-shift monotonicity after an arbitrary rectangular linear
image. This is the required rank-r covariance representation, including mean
directions outside the covariance range. -/
theorem monotoneOn_linearRadial_compressionProduct {p r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) {ι : Type*} [Fintype ι]
    (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((D i).size : ℝ) (((1 + r : ℕ) : ℝ)) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ x : ScalarRegressionNoise r,
      compressionProduct D (linearRadialInput L v (Real.sqrt t) x)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  have heq (t : ℝ) (x : ScalarRegressionNoise r) :
      compressionProduct D (linearRadialInput L v (Real.sqrt t) x) =
        compressionProduct (pullbackCompressionData D (radialLiftMatrix v L))
          (scalarRadialMatrix (Real.sqrt t) x) := by
    rw [← radialLiftMatrix_scalarRadialMatrix, compressionProduct_congruence]
  simpa only [heq] using
    monotoneOn_scalarRadial_compressionProduct_min hN
      (pullbackCompressionData D (radialLiftMatrix v L)) hB hη hsize

end Wishart
end
end CanonicalSource12

section CanonicalSource13
/- Source: Wishart/FullSpectralRegression.lean -/



/-!
# Full conditional Wishart matrices in spectral coordinates

The conditional matrix, including its cross block, is an embedded residual
plus a Gram matrix with one shifted Gaussian vector per selected eigenvalue.
The mean vectors have a selected component, whereas the Gaussian covariance
is supported on the complement. This retains all information needed for
arbitrary, possibly overlapping, compressions of the full matrix.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def gaussianRowsLinearMap {q m p : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (z : Fin q → EuclideanSpace ℝ (Fin m)) : Fin q → EuclideanSpace ℝ (Fin p) :=
  fun a => L.toEuclideanLin (z a)

@[fun_prop] theorem measurable_gaussianRowsLinearMap {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) :
    Measurable (gaussianRowsLinearMap (q := q) L) := by
  unfold gaussianRowsLinearMap
  fun_prop

theorem gaussianRowMatrix_linearMap {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) (z : Fin q → EuclideanSpace ℝ (Fin m)) :
    gaussianRowMatrix (gaussianRowsLinearMap L z) = L * gaussianRowMatrix z := by
  ext i a
  simp only [gaussianRowMatrix, gaussianRowsLinearMap, Matrix.of_apply,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]

def regressionNoiseLinearMap {q m p : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (x : RegressionNoise q m) : RegressionNoise q p :=
  (gaussianRowsLinearMap L x.1, Matrix.symmetricCongruenceLinearMap L x.2)

@[fun_prop] theorem measurable_regressionNoiseLinearMap {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) :
    Measurable (regressionNoiseLinearMap (q := q) L) := by
  exact ((measurable_gaussianRowsLinearMap L).comp measurable_fst).prodMk
    ((LinearMap.continuous_of_finiteDimensional _).measurable.comp measurable_snd)

theorem regressionNoiseLinearMap_comp {q m p r : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin m) (Fin r) ℝ)
    (x : RegressionNoise q r) :
    regressionNoiseLinearMap L (regressionNoiseLinearMap R x) =
      regressionNoiseLinearMap (L * R) x := by
  apply Prod.ext
  · funext a
    exact congrArg (fun T => T (x.1 a)) (Matrix.toLpLin_mul_same (p := 2) L R).symm
  · exact congrArg (fun T => T x.2) (Matrix.symmetricCongruenceLinearMap_mul L R).symm

theorem regressionNoiseLinearMap_rotation {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (x : RegressionNoise q m) :
    regressionNoiseLinearMap L (regressionNoiseRotation O x) =
      regressionNoiseRotation O (regressionNoiseLinearMap L x) := by
  apply Prod.ext
  · have hmat : gaussianRowMatrix
        (gaussianRowsLinearMap L (gaussianRowRotation O x.1)) =
        gaussianRowMatrix (gaussianRowRotation O (gaussianRowsLinearMap L x.1)) := by
      simp only [gaussianRowMatrix_linearMap, gaussianRowRotation_matrix, Matrix.mul_assoc]
    funext a
    apply PiLp.ext
    intro i
    exact congrArg (fun M : Matrix (Fin p) (Fin q) ℝ => M i a) hmat
  · rfl

theorem measurePreserving_regressionNoiseLinearMap {q m : ℕ} (n : ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.det ≠ 0) :
    MeasurePreserving (regressionNoiseLinearMap (q := q) R)
      (regressionNoiseMeasure n q m 1)
      (regressionNoiseMeasure n q m (R * Rᵀ)) := by
  have hGaussian : MeasurePreserving R.toEuclideanLin
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (R * Rᵀ)) := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    simpa only [map_zero, add_zero, Matrix.mul_one] using
      map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        Matrix.PosSemidef.one R 0
  have hRows := measurePreserving_pi
    (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1)
    (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (R * Rᵀ))
    (fun _ => hGaussian)
  have hResidual : MeasurePreserving (Matrix.symmetricCongruenceLinearMap R)
      (nonsingularWishartMeasure (n - q) (1 : Matrix (Fin m) (Fin m) ℝ))
      (nonsingularWishartMeasure (n - q) (R * Rᵀ)) := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    simpa only [Matrix.mul_one] using
      map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero
        (n - q) 1 hR
  exact hRows.prod hResidual

def linearRegressionGramWithMean {q m p : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (L : Matrix (Fin p) (Fin m) ℝ)
    (x : RegressionNoise q m) : SymmetricMatrix p :=
  regressionGramWithMean M (regressionNoiseLinearMap L x)

@[fun_prop] theorem measurable_linearRegressionGramWithMean {q m p : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (L : Matrix (Fin p) (Fin m) ℝ) :
    Measurable (linearRegressionGramWithMean M L) :=
  (measurable_regressionGramWithMean M).comp (measurable_regressionNoiseLinearMap L)

@[simp] theorem coe_linearRegressionGramWithMean {q m p : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (L : Matrix (Fin p) (Fin m) ℝ)
    (x : RegressionNoise q m) :
    (linearRegressionGramWithMean M L x : Matrix (Fin p) (Fin p) ℝ) =
      (M + L * gaussianRowMatrix x.1) * (M + L * gaussianRowMatrix x.1)ᵀ +
        L * (x.2 : Matrix (Fin m) (Fin m) ℝ) * Lᵀ := by
  simp only [linearRegressionGramWithMean, regressionGramWithMean,
    regressionNoiseLinearMap, gaussianRowMatrix_linearMap,
    Matrix.coe_symmetricCongruenceLinearMap_apply]

theorem linearRegressionGramWithMean_rotation {q m p : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (L : Matrix (Fin p) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) (hO : O * Oᵀ = 1)
    (x : RegressionNoise q m) :
    linearRegressionGramWithMean (M * Oᵀ) L (regressionNoiseRotation O x) =
      linearRegressionGramWithMean M L x := by
  unfold linearRegressionGramWithMean
  rw [regressionNoiseLinearMap_rotation]
  exact regressionGramWithMean_rotation M O hO _

def regressionMeanInjection {q m : ℕ} (K : Matrix (Fin q) (Fin m) ℝ) :
    Matrix (Fin (q + m)) (Fin q) ℝ :=
  (Matrix.fromRows (1 : Matrix (Fin q) (Fin q) ℝ) Kᵀ).submatrix
    finSumFinEquiv.symm (Equiv.refl (Fin q))

def regressionNoiseInjection (q m : ℕ) : Matrix (Fin (q + m)) (Fin m) ℝ :=
  (Matrix.fromRows (0 : Matrix (Fin q) (Fin m) ℝ) 1).submatrix
    finSumFinEquiv.symm (Equiv.refl (Fin m))

@[simp] theorem regressionMeanInjection_submatrix {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) :
    (regressionMeanInjection K).submatrix finSumFinEquiv id = Matrix.fromRows 1 Kᵀ := by
  ext i j
  simp [regressionMeanInjection]

@[simp] theorem regressionNoiseInjection_submatrix (q m : ℕ) :
    (regressionNoiseInjection q m).submatrix finSumFinEquiv id =
      Matrix.fromRows (0 : Matrix (Fin q) (Fin m) ℝ) 1 := by
  ext i j
  simp [regressionNoiseInjection]

theorem regressionReconstruction_eq_linearGram {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (S : SymmetricMatrix q) (x : RegressionNoise q m) :
    regressionReconstruction K (S, x) =
      linearRegressionGramWithMean
        (regressionMeanInjection K * CFC.sqrt (S : Matrix (Fin q) (Fin q) ℝ))
        (regressionNoiseInjection q m) x := by
  apply Subtype.ext
  apply Matrix.submatrix_injective finSumFinEquiv.surjective finSumFinEquiv.surjective
  change (regressionReconstruction K (S, x) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
    finSumFinEquiv finSumFinEquiv = _
  rw [regressionReconstruction_submatrix, coe_linearRegressionGramWithMean]
  let A := CFC.sqrt (S : Matrix (Fin q) (Fin q) ℝ)
  let G := gaussianRowMatrix x.1
  let J := regressionNoiseInjection q m
  have hY : (regressionMeanInjection K * A + J * G).submatrix finSumFinEquiv id =
      Matrix.fromRows A (Kᵀ * A + G) := by
    rw [Matrix.submatrix_add]
    change (regressionMeanInjection K * A).submatrix finSumFinEquiv id +
      (J * G).submatrix finSumFinEquiv id = _
    rw [Matrix.submatrix_mul _ _ finSumFinEquiv id id Function.bijective_id,
      Matrix.submatrix_mul _ _ finSumFinEquiv id id Function.bijective_id]
    simp only [regressionMeanInjection_submatrix, J, regressionNoiseInjection_submatrix,
      Matrix.submatrix_id_id, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
    ext (i | i) j <;> simp
  have hW : (J * (x.2 : Matrix (Fin m) (Fin m) ℝ) * Jᵀ).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (0 : Matrix (Fin q) (Fin q) ℝ) 0 0
        (x.2 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [Matrix.submatrix_mul _ _ finSumFinEquiv id finSumFinEquiv Function.bijective_id,
      Matrix.submatrix_mul _ _ finSumFinEquiv id id Function.bijective_id,
      ← Matrix.transpose_submatrix]
    simp only [J, regressionNoiseInjection_submatrix, Matrix.submatrix_id_id,
      Matrix.transpose_fromRows, Matrix.transpose_zero, Matrix.transpose_one]
    rw [Matrix.fromRows_mul, Matrix.zero_mul, Matrix.one_mul,
      Matrix.fromRows_mul_fromCols]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one]
  change regressionBlockMatrix A (Kᵀ * A + G) x.2 =
    ((regressionMeanInjection K * A + J * G) *
      (regressionMeanInjection K * A + J * G)ᵀ +
      J * (x.2 : Matrix (Fin m) (Fin m) ℝ) * Jᵀ).submatrix
        finSumFinEquiv finSumFinEquiv
  rw [Matrix.submatrix_add]
  change regressionBlockMatrix A (Kᵀ * A + G) x.2 =
    ((regressionMeanInjection K * A + J * G) *
      (regressionMeanInjection K * A + J * G)ᵀ).submatrix
        finSumFinEquiv finSumFinEquiv +
    (J * (x.2 : Matrix (Fin m) (Fin m) ℝ) * Jᵀ).submatrix
      finSumFinEquiv finSumFinEquiv
  rw [Matrix.submatrix_mul _ _ finSumFinEquiv id finSumFinEquiv Function.bijective_id,
    ← Matrix.transpose_submatrix, hY, hW,
    Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add]
  simp only [regressionBlockMatrix, add_zero]

def fullSpectralRegressionMean {q m : ℕ} (K : Matrix (Fin q) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) (lam : Fin q → ℝ) :
    Matrix (Fin (q + m)) (Fin q) ℝ :=
  regressionMeanInjection K * O * Matrix.diagonal (fun a => Real.sqrt (lam a))

theorem fullSpectralRegressionMean_apply {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (i : Fin (q + m)) (a : Fin q) :
    fullSpectralRegressionMean K O lam i a =
      Real.sqrt (lam a) * (regressionMeanInjection K * O) i a := by
  rw [fullSpectralRegressionMean, Matrix.mul_diagonal]
  ring

@[fun_prop] theorem measurable_fullSpectralRegressionMean {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) :
    Measurable (fun x : (Fin q → ℝ) × Matrix (Fin q) (Fin q) ℝ =>
      fullSpectralRegressionMean K x.2 x.1) := by
  apply Matrix.measurable_iff.mpr
  intro i a
  simp only [fullSpectralRegressionMean_apply, Matrix.mul_apply]
  fun_prop

def fullSpectralRegressionModel {q m : ℕ} (K : Matrix (Fin q) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) (lam : Fin q → ℝ) :
    RegressionNoise q m → SymmetricMatrix (q + m) :=
  linearRegressionGramWithMean (fullSpectralRegressionMean K O lam)
    (regressionNoiseInjection q m)

@[fun_prop] theorem measurable_fullSpectralRegressionModel {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ) (lam : Fin q → ℝ) :
    Measurable (fullSpectralRegressionModel K O lam) :=
  measurable_linearRegressionGramWithMean _ _

/-- The law of the entire conditional matrix agrees with the embedded
spectral-row model. Thus this identity also transports overlapping minors. -/
theorem map_fullRegression_spectral {q m : ℕ} (n : ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (hO : O * Oᵀ = 1) (lam : Fin q → ℝ) (hlam : ∀ a, 0 ≤ lam a)
    (S : SymmetricMatrix q)
    (hS : (S : Matrix (Fin q) (Fin q) ℝ) = O * Matrix.diagonal lam * Oᵀ) :
    (regressionNoiseMeasure n q m C).map (fun x => regressionReconstruction K (S, x)) =
      (regressionNoiseMeasure n q m C).map (fullSpectralRegressionModel K O lam) := by
  simp_rw [regressionReconstruction_eq_linearGram]
  have hmean : regressionMeanInjection K * CFC.sqrt (S : Matrix (Fin q) (Fin q) ℝ) =
      fullSpectralRegressionMean K O lam * Oᵀ := by
    rw [hS, sqrt_spectral_matrix O hO lam hlam]
    simp only [fullSpectralRegressionMean, Matrix.mul_assoc]
  rw [hmean]
  have hrotate := measurePreserving_regressionNoiseRotation (m := m) n hC O hO
  conv_lhs => rw [← hrotate.map_eq]
  rw [Measure.map_map (measurable_linearRegressionGramWithMean _ _) hrotate.measurable]
  congr 1
  funext x
  exact linearRegressionGramWithMean_rotation _ _ O hO x

theorem fullSpectralRegressionModel_linearMap {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) (lam : Fin q → ℝ) (x : RegressionNoise q m) :
    fullSpectralRegressionModel K O lam (regressionNoiseLinearMap R x) =
      linearRegressionGramWithMean (fullSpectralRegressionMean K O lam)
        (regressionNoiseInjection q m * R) x := by
  unfold fullSpectralRegressionModel linearRegressionGramWithMean
  rw [regressionNoiseLinearMap_comp]

/-- Covariance whitening is performed only in the genuine m-dimensional
residual law; the full ambient image may have singular covariance. -/
theorem map_fullSpectralRegressionModel_sqrt {q m : ℕ} (n : ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) :
    (regressionNoiseMeasure n q m C).map (fullSpectralRegressionModel K O lam) =
      (regressionNoiseMeasure n q m 1).map
        (linearRegressionGramWithMean (fullSpectralRegressionMean K O lam)
          (regressionNoiseInjection q m * CFC.sqrt C)) := by
  have hroot : CFC.sqrt C * (CFC.sqrt C)ᵀ = C := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg
  have hdet : (CFC.sqrt C).det ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det hroot
    rw [Matrix.det_mul, hzero, zero_mul] at h
    exact hC.det_pos.ne' h.symm
  have hpush := (measurePreserving_regressionNoiseLinearMap (q := q) n (CFC.sqrt C) hdet).map_eq
  rw [hroot] at hpush
  rw [← hpush, Measure.map_map
    (measurable_fullSpectralRegressionModel K O lam) (measurable_regressionNoiseLinearMap _)]
  congr 1
  funext x
  exact fullSpectralRegressionModel_linearMap K _ O lam x

end Wishart
end
end CanonicalSource13

section CanonicalSource14
/- Source: Wishart/OverlapRegressionMonotonicity.lean -/



/-!
# Conditional monotonicity for arbitrary overlapping compressions

The source is a genuine residual Wishart law in dimension m, together with
independent m-dimensional standard Gaussian rows. An arbitrary rectangular
map embeds the noise in the full ambient space. The means need not belong
to its range. Separating a single row invokes the transverse radial theorem,
with the exact bound min(compression rank,m+1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def linearShiftedRowsSym {q m p : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ)
    (x : RegressionNoise q m) : SymmetricMatrix p :=
  Matrix.symmetricCongruenceLinearMap L x.2 +
    rowBackground v lam (gaussianRowsLinearMap L x.1)

@[fun_prop] theorem measurable_linearShiftedRowsSym {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) (v : Fin q → EuclideanSpace ℝ (Fin p))
    (lam : Fin q → ℝ) : Measurable (linearShiftedRowsSym L v lam) := by
  apply Measurable.add
  · exact (LinearMap.continuous_of_finiteDimensional _).measurable.comp measurable_snd
  · exact (measurable_rowBackground v lam).comp
      ((measurable_gaussianRowsLinearMap L).comp measurable_fst)

theorem linearShiftedRowsSym_posSemidef {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) (v : Fin q → EuclideanSpace ℝ (Fin p))
    (lam : Fin q → ℝ) (x : RegressionNoise q m)
    (hW : (x.2 : Matrix (Fin m) (Fin m) ℝ).PosSemidef) :
    (linearShiftedRowsSym L v lam x : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.add _ (rowBackground_posSemidef v lam _)
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hW.mul_mul_conjTranspose_same L

set_option maxHeartbeats 1000000 in
theorem allFiniteMoments_linearShiftedRowsSym_entry
    {q m p : ℕ} {ν : Measure (SymmetricMatrix m)} [IsProbabilityMeasure ν]
    (C : Matrix (Fin m) (Fin m) ℝ)
    (hν : ∀ i j : Fin m, HasAllFiniteMoments
      (fun W : SymmetricMatrix m => (W : Matrix (Fin m) (Fin m) ℝ) i j) ν)
    (L : Matrix (Fin p) (Fin m) ℝ) (v : Fin q → EuclideanSpace ℝ (Fin p))
    (lam : Fin q → ℝ) (i j : Fin p) :
    HasAllFiniteMoments (fun x =>
      (linearShiftedRowsSym L v lam x : Matrix (Fin p) (Fin p) ℝ) i j)
      (gaussianResidualMeasure q C ν) := by
  have hz (a : Fin q) (b : Fin m) : HasAllFiniteMoments
      (fun x : RegressionNoise q m => x.1 a b) (gaussianResidualMeasure q C ν) :=
    (allFiniteMoments_gaussian_coordinate 0 C b).comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin q =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C) a).comp measurePreserving_fst)
  have hLz (a : Fin q) (b : Fin p) : HasAllFiniteMoments
      (fun x : RegressionNoise q m => L.toEuclideanLin (x.1 a) b)
      (gaussianResidualMeasure q C ν) := by
    simpa only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using
      HasAllFiniteMoments.finset_sum (μ := gaussianResidualMeasure q C ν)
        Finset.univ (fun (k : Fin m) (x : RegressionNoise q m) => L b k * x.1 a k)
        (fun k _ => (hz a k).const_mul (L b k))
  have hW (a b : Fin m) : HasAllFiniteMoments
      (fun x : RegressionNoise q m => (x.2 : Matrix (Fin m) (Fin m) ℝ) a b)
      (gaussianResidualMeasure q C ν) :=
    (hν a b).comp_measurePreserving measurePreserving_snd
  have hLW : HasAllFiniteMoments (fun x : RegressionNoise q m =>
      (L * (x.2 : Matrix (Fin m) (Fin m) ℝ) * Lᵀ) i j)
      (gaussianResidualMeasure q C ν) :=
    HasAllFiniteMoments.matrix_right_mul_entry _ Lᵀ
      (fun a b => HasAllFiniteMoments.matrix_left_mul_entry _ L hW a b) i j
  have hy (a : Fin q) (b : Fin p) : HasAllFiniteMoments
      (fun x : RegressionNoise q m =>
        L.toEuclideanLin (x.1 a) b + Real.sqrt (lam a) * v a b)
      (gaussianResidualMeasure q C ν) :=
    (hLz a b).add (HasAllFiniteMoments.const _)
  simpa only [linearShiftedRowsSym, Submodule.coe_add,
    Matrix.coe_symmetricCongruenceLinearMap_apply, coe_rowBackground,
    gaussianRowsLinearMap, Matrix.add_apply, Matrix.sum_apply, Matrix.vecMulVec_apply] using
    hLW.add (HasAllFiniteMoments.finset_sum (μ := gaussianResidualMeasure q C ν) Finset.univ
      (fun (a : Fin q) (x : RegressionNoise q m) =>
        (L.toEuclideanLin (x.1 a) i + Real.sqrt (lam a) * v a i) *
        (L.toEuclideanLin (x.1 a) j + Real.sqrt (lam a) * v a j))
      (fun a _ => (hy a i).mul (hy a j)))

def separateScalarRegressionRow {q m : ℕ} (a : Fin (q + 1))
    (x : RegressionNoise (q + 1) m) :
    (Fin q → EuclideanSpace ℝ (Fin m)) × ScalarRegressionNoise m :=
  (fun j => x.1 (a.succAbove j), (x.1 a, x.2))

theorem measurePreserving_separateScalarRegressionRow {q m : ℕ}
    (ν : ℝ) (a : Fin (q + 1)) :
    MeasurePreserving (separateScalarRegressionRow (m := m) a)
      (gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1))
      ((Measure.pi (fun _ : Fin q =>
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1)).prod
        (scalarRegressionNoiseMeasure (ν + 1) m)) := by
  let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1
  let μ := Measure.pi (fun _ : Fin q => γ)
  let ρ := nonsingularWishartMeasure ν (1 : Matrix (Fin m) (Fin m) ℝ)
  have hswap : MeasurePreserving Prod.swap (ρ.prod γ) (γ.prod ρ) :=
    Measure.measurePreserving_swap
  have h := ((MeasurePreserving.id μ).prod hswap).comp
    (measurePreserving_separateRegressionRow (1 : Matrix (Fin m) (Fin m) ℝ) ρ a)
  have hf : Prod.map id Prod.swap ∘ separateRegressionRow (m := m) a =
      separateScalarRegressionRow (m := m) a := by
    funext x
    rfl
  rw [hf] at h
  simpa only [μ, γ, ρ, scalarRegressionNoiseMeasure, add_sub_cancel_right] using h

theorem linearShiftedRowsSym_separate {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ)
    (v : Fin (q + 1) → EuclideanSpace ℝ (Fin p)) (lam : Fin (q + 1) → ℝ)
    (a : Fin (q + 1)) (t : ℝ) (x : RegressionNoise (q + 1) m) :
    linearShiftedRowsSym L v (Function.update lam a t) x =
      rowBackground (v ∘ a.succAbove) (lam ∘ a.succAbove)
        (gaussianRowsLinearMap L (separateScalarRegressionRow a x).1) +
      linearRadialInput L (v a) (Real.sqrt t) (separateScalarRegressionRow a x).2 := by
  unfold linearShiftedRowsSym rowBackground
  rw [Fin.sum_univ_succAbove _ a]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne _ _),
    separateScalarRegressionRow, Function.comp_apply, linearRadialInput,
    gaussianRowsLinearMap]
  abel

theorem monotoneOn_linearShiftedRows_compressionProduct_coordinate
    {q m p : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((D i).size : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ ν + 1)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) (a : Fin q) :
    MonotoneOn (fun t : ℝ => ∫ x,
      compressionProduct D (linearShiftedRowsSym L v (Function.update lam a t) x)
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)) (Set.Ici 0) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  cases q with
  | zero => exact Fin.elim0 a
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1
    let μ := Measure.pi (fun _ : Fin q => γ)
    let ρ := scalarRegressionNoiseMeasure (ν + 1) m
    let B (z : Fin q → EuclideanSpace ℝ (Fin m)) :=
      rowBackground (v ∘ a.succAbove) (lam ∘ a.succAbove) (gaussianRowsLinearMap L z)
    let F (t : ℝ) (y : (Fin q → EuclideanSpace ℝ (Fin m)) × ScalarRegressionNoise m) :=
      compressionProduct D (B y.1 + linearRadialInput L (v a) (Real.sqrt t) y.2)
    have hsplit := measurePreserving_separateScalarRegressionRow (m := m) ν a
    have hFmeas (t : ℝ) : Measurable (F t) := by
      apply (measurable_compressionProduct D).comp
      apply Measurable.add
      · exact ((measurable_rowBackground _ _).comp
          (measurable_gaussianRowsLinearMap L)).comp measurable_fst
      · exact (measurable_linearRadialInput L (v a) (Real.sqrt t)).comp measurable_snd
    have hFcomp (t : ℝ) : F t ∘ separateScalarRegressionRow a =
        (fun x => compressionProduct D (linearShiftedRowsSym L v (Function.update lam a t) x)) := by
      funext x
      dsimp only [F, B, Function.comp_apply]
      rw [linearShiftedRowsSym_separate]
    have hFi (t : ℝ) : Integrable (F t) (μ.prod ρ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hFmeas t).aestronglyMeasurable
        hsplit.measurable.aemeasurable).mpr
      rw [hFcomp]
      apply HasAllFiniteMoments.integrable
      apply allFiniteMoments_compressionProduct_of_entries D hη
      exact allFiniteMoments_linearShiftedRowsSym_entry 1
        (fun i j => allFiniteMoments_wishart_entry (α := ν)
          (Sigma := (1 : Matrix (Fin m) (Fin m) ℝ)) i j)
        L v (Function.update lam a t)
    have heq (t : ℝ) :
        (∫ x, compressionProduct D (linearShiftedRowsSym L v (Function.update lam a t) x)
          ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) =
        ∫ z, ∫ Y, F t (z, Y) ∂ρ ∂μ := by
      rw [← integral_prod _ (hFi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hFmeas t).aestronglyMeasurable]
      exact congrArg (fun f => ∫ x, f x
        ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) (hFcomp t).symm
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hFi s).integral_prod_left (hFi t).integral_prod_left
    apply Filter.Eventually.of_forall
    intro z
    have hBz : ∀ i, ((addCompressionOffset D (B z)) i).offset.PosSemidef := by
      intro i
      apply (hB i).add
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (rowBackground_posSemidef _ _ (gaussianRowsLinearMap L z)).conjTranspose_mul_mul_same
          (D i).linear
    have hN : (m : ℝ) < ν + 1 := by linarith
    simpa only [F, compressionProduct_add] using
      monotoneOn_linearRadial_compressionProduct hN L (v a)
        (addCompressionOffset D (B z)) hBz hη hsize hs ht hst

theorem monotoneOn_linearShiftedRows_compressionProduct
    {q m p : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((D i).size : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ ν + 1)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      compressionProduct D (linearShiftedRowsSym L v lam x)
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))
      (Set.Ici (0 : Fin q → ℝ)) :=
  monotoneOn_nonnegative_pi_of_update _ fun lam a =>
    monotoneOn_linearShiftedRows_compressionProduct_coordinate hν L D hB hη hsize v lam a

def fullSpectralRegressionDirections {q m : ℕ} (K : Matrix (Fin q) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) : Fin q → EuclideanSpace ℝ (Fin (q + m)) :=
  fun a => WithLp.toLp 2 (fun i => (regressionMeanInjection K * O) i a)

theorem fullSpectralGram_eq_linearShiftedRows {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (L : Matrix (Fin (q + m)) (Fin m) ℝ)
    (x : RegressionNoise q m) :
    linearRegressionGramWithMean (fullSpectralRegressionMean K O lam) L x =
      linearShiftedRowsSym L (fullSpectralRegressionDirections K O) lam x := by
  apply Subtype.ext
  ext i j
  simp only [coe_linearRegressionGramWithMean, linearShiftedRowsSym, Submodule.coe_add,
    Matrix.coe_symmetricCongruenceLinearMap_apply, coe_rowBackground, gaussianRowsLinearMap,
    fullSpectralRegressionDirections, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, gaussianRowMatrix,
    Matrix.of_apply, PiLp.toLp_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  simp only [fullSpectralRegressionMean_apply, Matrix.mul_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

def fullSpectralConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix (q + m) → ℝ) (lam : Fin q → ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  ∫ x, g (fullSpectralRegressionModel K O lam x) ∂regressionNoiseMeasure n q m C

theorem fullSpectralConditionalMoment_standardNoise {q m : ℕ} (n : ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ) (lam : Fin q → ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    fullSpectralConditionalMoment n C K g lam O =
      ∫ x, g (linearShiftedRowsSym (regressionNoiseInjection q m * CFC.sqrt C)
        (fullSpectralRegressionDirections K O) lam x) ∂regressionNoiseMeasure n q m 1 := by
  unfold fullSpectralConditionalMoment
  have hlaw := map_fullSpectralRegressionModel_sqrt n hC K O lam
  rw [← integral_map (measurable_fullSpectralRegressionModel K O lam).aemeasurable
      hg.aestronglyMeasurable, hlaw,
    integral_map (measurable_linearRegressionGramWithMean _ _).aemeasurable
      hg.aestronglyMeasurable]
  simp only [fullSpectralConditionalMoment, fullSpectralGram_eq_linearShiftedRows]

/-- Exact conditional comparison for all overlapping compression products.
The rank bound is equivalent to alpha >= min(q+k,p+1), with p=q+m. -/
theorem monotoneOn_fullSpectralConditionalMoment_compressionProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData (q + m))
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((D i).size : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ n - q + 1) :
    MonotoneOn (fun lam => fullSpectralConditionalMoment n C K (compressionProduct D) lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  simp_rw [fullSpectralConditionalMoment_standardNoise n hC K O _
    (measurable_compressionProduct D)]
  exact monotoneOn_linearShiftedRows_compressionProduct hν
    (regressionNoiseInjection q m * CFC.sqrt C) D hB hη hsize
      (fullSpectralRegressionDirections K O)

end Wishart
end
end CanonicalSource14

section CanonicalSource15
/- Source: Wishart/FullRegressionMoments.lean -/



/-!
# Conditional moments of full-matrix observables

The remaining observable may depend on every entry of the original matrix.
In particular no disjointness is imposed on the compressed determinants.
The conditional moments are integrals over the actual independent regression
source, and their integrability is transported from the original Wishart law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def fullRegressionConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix (q + m) → ℝ) (S : SymmetricMatrix q) : ℝ :=
  ∫ x, g (regressionReconstruction K (S, x)) ∂regressionNoiseMeasure n q m C

@[fun_prop] theorem measurable_fullRegressionConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    Measurable (fullRegressionConditionalMoment n C K g) :=
  (hg.comp (measurable_regressionReconstruction K)).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_fullRegression_joint_source {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {g : SymmetricMatrix (q + m) → ℝ}
    (hjoint : Integrable
      (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) * g X)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun x : RegressionData q m => h x.1 * g (regressionReconstruction K x))
      ((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
        (regressionNoiseMeasure n q m C)) := by
  have hsource := (integrable_regressionReconstruction_iff hn K hC
    hjoint.aestronglyMeasurable).mp hjoint
  apply hsource.congr
  filter_upwards [ae_regressionReconstruction_selected n K C] with x hx
  have hselected : principalSymmetricBlock (Fin.castAdd m) (regressionReconstruction K x) =
      x.1 := Subtype.ext hx
  rw [hselected]

theorem integral_fullRegression_selected_mul {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {g : SymmetricMatrix (q + m) → ℝ}
    (hjoint : Integrable
      (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) * g X)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X) * g X
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ S, h S * fullRegressionConditionalMoment n C K g S
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ) := by
  rw [integral_regressionReconstruction hn K hC hjoint.aestronglyMeasurable]
  have hae : (fun x : RegressionData q m =>
      h (principalSymmetricBlock (Fin.castAdd m) (regressionReconstruction K x)) *
        g (regressionReconstruction K x)) =ᵐ[regressionDataMeasure n q m C]
      (fun x => h x.1 * g (regressionReconstruction K x)) := by
    filter_upwards [ae_regressionReconstruction_selected n K C] with x hx
    rw [show principalSymmetricBlock (Fin.castAdd m) (regressionReconstruction K x) = x.1
      from Subtype.ext hx]
  rw [integral_congr_ae hae]
  change (∫ x : RegressionData q m, h x.1 * g (regressionReconstruction K x)
    ∂((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
      (regressionNoiseMeasure n q m C))) = _
  rw [integral_prod _ (integrable_fullRegression_joint_source hn K hC hjoint)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun S => integral_const_mul (h S) _

theorem integrable_selected_mul_fullRegressionConditionalMoment {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {g : SymmetricMatrix (q + m) → ℝ}
    (hjoint : Integrable
      (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) * g X)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun S => h S * fullRegressionConditionalMoment n C K g S)
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  apply (integrable_fullRegression_joint_source hn K hC hjoint).integral_prod_left.congr
  exact Filter.Eventually.of_forall fun S => integral_const_mul (h S) _

theorem integrable_fullRegressionConditionalMoment {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix (q + m) → ℝ}
    (hg : Integrable g (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fullRegressionConditionalMoment n C K g)
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  simpa only [one_mul] using
    integrable_selected_mul_fullRegressionConditionalMoment hn K hC
      (h := fun _ => 1) (g := g) (by simpa only [one_mul] using hg)

theorem integral_fullRegression {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix (q + m) → ℝ}
    (hg : Integrable g (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, g X ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ S, fullRegressionConditionalMoment n C K g S
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ) := by
  simpa only [one_mul] using integral_fullRegression_selected_mul hn K hC
    (h := fun _ => 1) (g := g) (by simpa only [one_mul] using hg)

set_option maxHeartbeats 1200000 in
@[fun_prop] theorem measurable_fullSpectralConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    Measurable (Function.uncurry (fullSpectralConditionalMoment n C K g)) := by
  have hmodel : Measurable (fun y :
      (((Fin q → ℝ) × Matrix (Fin q) (Fin q) ℝ) × RegressionNoise q m) =>
        fullSpectralRegressionModel K y.1.2 y.1.1 y.2) := by
    exact measurable_regressionGramWithMean_uncurry.comp
      (((measurable_fullSpectralRegressionMean K).comp measurable_fst).prodMk
        ((measurable_regressionNoiseLinearMap (regressionNoiseInjection q m)).comp measurable_snd))
  exact (hg.comp hmodel).stronglyMeasurable.integral_prod_right'.measurable

theorem fullRegressionConditionalMoment_eq_spectral {q m : ℕ} (n : ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (hO : O * Oᵀ = 1) (lam : Fin q → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (S : SymmetricMatrix q)
    (hS : (S : Matrix (Fin q) (Fin q) ℝ) = O * Matrix.diagonal lam * Oᵀ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    fullRegressionConditionalMoment n C K g S = fullSpectralConditionalMoment n C K g lam O := by
  have hmap := map_fullRegression_spectral n hC K O hO lam hlam S hS
  have hi := congrArg (fun μ : Measure (SymmetricMatrix (q + m)) => ∫ T, g T ∂μ) hmap
  have hm : Measurable (fun x : RegressionNoise q m => regressionReconstruction K (S, x)) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_regressionReconstruction K).comp
        (measurable_const.prodMk (measurable_id : Measurable (id : RegressionNoise q m → _)))
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_map (measurable_fullSpectralRegressionModel K O lam).aemeasurable
      hg.aestronglyMeasurable] at hi
  exact hi

theorem integrable_sq_fullRegressionConditionalMoment {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hgi : Integrable g (nonsingularWishartMeasure n (regressionScale K C)))
    (hg2i : Integrable (fun X => g X ^ 2)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun S => fullRegressionConditionalMoment n C K g S ^ 2)
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  have hsource := integrable_fullRegression_joint_source hn K hC
    (h := fun _ => 1) (g := g) (by simpa only [one_mul] using hgi)
  have hsource2 := integrable_fullRegression_joint_source hn K hC
    (h := fun _ => 1) (g := fun X => g X ^ 2) (by simpa only [one_mul] using hg2i)
  exact parameterAverage_sq_integrable _ _
    (fun x : RegressionData q m => g (regressionReconstruction K x))
    (hgm.comp (measurable_regressionReconstruction K))
    (by simpa only [one_mul] using hsource)
    (by simpa only [one_mul] using hsource2)

end Wishart
end
end CanonicalSource15

section CanonicalSource16
/- Source: Wishart/FullSpectralRegressionMoments.lean -/



/-!
# Haar moment identities for arbitrary full-matrix observables

The selected test is any function with the displayed spectral expression.
The remaining test may use overlapping compressions. All three moments and
the needed integrability assertions follow from the exact Wishart, regression,
and Laguerre–Haar laws; these laws are not hypotheses of the final identities.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def haarFullRegressionIntegrand {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix (q + m) → ℝ) (x : (Fin q → ℝ) × Spectral.Orth q) : ℝ :=
  fullSpectralConditionalMoment n C K g x.1 ↑x.2

set_option maxHeartbeats 800000 in
@[fun_prop] theorem measurable_haarFullRegressionIntegrand {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    Measurable (haarFullRegressionIntegrand n C K g) := by
  have hcoe : Measurable (fun O : Spectral.Orth q =>
      (O : Matrix (Fin q) (Fin q) ℝ)) := measurable_subtype_coe
  have hm : Measurable (fun x : (Fin q → ℝ) × Spectral.Orth q =>
      (x.1, (x.2 : Matrix (Fin q) (Fin q) ℝ))) :=
    measurable_fst.prodMk (hcoe.comp measurable_snd)
  have hf : Measurable (Function.uncurry (fullSpectralConditionalMoment n C K g)) :=
    measurable_fullSpectralConditionalMoment n C K hg
  change Measurable (Function.uncurry (fullSpectralConditionalMoment n C K g) ∘
    (fun x : (Fin q → ℝ) × Spectral.Orth q =>
      (x.1, (x.2 : Matrix (Fin q) (Fin q) ℝ))))
  exact hf.comp hm

def fullRegressionSpectralAverage {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix (q + m) → ℝ) : (Fin q → ℝ) → ℝ :=
  parameterAverageOn (haarProb (Spectral.Orth q))
    (Spectral.positiveChamber q) (haarFullRegressionIntegrand n C K g)

@[fun_prop] theorem measurable_fullRegressionSpectralAverage {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    Measurable (fullRegressionSpectralAverage n C K g) :=
  parameterAverageOn_measurable _ _ (orderedChamber_measurable _ measurableSet_Ioi) _
    (measurable_haarFullRegressionIntegrand n C K hg)

theorem fullRegressionSpectralAverage_eq {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix (q + m) → ℝ) {lam : Fin q → ℝ}
    (hlam : lam ∈ Spectral.positiveChamber q) :
    fullRegressionSpectralAverage n C K g lam =
      ∫ O : Spectral.Orth q, fullSpectralConditionalMoment n C K g lam ↑O
        ∂haarProb (Spectral.Orth q) := parameterAverageOn_of_mem _ _ _ hlam

theorem ae_fullRegressionConditionalMoment_spectral {q m : ℕ} {n : ℝ}
    (hn : (q : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    (fun x => fullRegressionConditionalMoment n C K g (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))]
      haarFullRegressionIntegrand n C K g := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (Spectral.ae_laguerreLaw_mem_chamber hn)] with x hx
  exact fullRegressionConditionalMoment_eq_spectral n hC K ↑x.2
    (Spectral.orth_mul_transpose x.2) x.1 (fun i => (hx.2 i).le)
    (regressionSpectralMatrix x) (Matrix.coe_symmetricCongruenceLinearMap_apply _ _) hg

theorem integrable_haarFullRegressionIntegrand {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hgi : Integrable g (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (haarFullRegressionIntegrand n C K g)
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  exact ((measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable
    (integrable_fullRegressionConditionalMoment hn K hC hgi)).congr
      (ae_fullRegressionConditionalMoment_spectral hnq hC.posSemidef K hgm)

theorem integrable_selected_mul_haarFullRegressionIntegrand {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {f : (Fin q → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ Spectral.positiveChamber q, ∀ O : Spectral.Orth q,
      h (regressionSpectralMatrix (lam, O)) = f lam)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hjoint : Integrable (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) * g X)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun x => f x.1 * haarFullRegressionIntegrand n C K g x)
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  apply ((measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable
    (integrable_selected_mul_fullRegressionConditionalMoment hn K hC hjoint)).congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (Spectral.ae_laguerreLaw_mem_chamber hnq),
    ae_fullRegressionConditionalMoment_spectral hnq hC.posSemidef K hgm] with x hx hy
  exact congrArg₂ (· * ·) (hspectral x.1 hx x.2) hy

theorem integral_fullRegression_selected_spectral {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} (hh : Measurable h) {f : (Fin q → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ Spectral.positiveChamber q, ∀ O : Spectral.Orth q,
      h (regressionSpectralMatrix (lam, O)) = f lam) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, f lam ∂regressionEigenLaw q n := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  rw [integral_regression_selected hn K hC hh,
    integral_regressionSpectralMatrix hnq hh.aestronglyMeasurable]
  have heq : (fun x => h (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))] (fun x => f x.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (Spectral.ae_laguerreLaw_mem_chamber hnq)] with x hx
    exact hspectral x.1 hx x.2
  rw [integral_congr_ae heq, integral_fun_fst]
  simp only [probReal_univ, one_smul]

theorem integral_fullRegression_joint_spectral {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {f : (Fin q → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ Spectral.positiveChamber q, ∀ O : Spectral.Orth q,
      h (regressionSpectralMatrix (lam, O)) = f lam)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hjoint : Integrable (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) * g X)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X) * g X
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, f lam * fullRegressionSpectralAverage n C K g lam ∂regressionEigenLaw q n := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  have hcond := integrable_selected_mul_fullRegressionConditionalMoment hn K hC hjoint
  rw [integral_fullRegression_selected_mul hn K hC hjoint,
    integral_regressionSpectralMatrix hnq hcond.aestronglyMeasurable]
  have heq : (fun x => h (regressionSpectralMatrix x) *
      fullRegressionConditionalMoment n C K g (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))]
      (fun x => f x.1 * haarFullRegressionIntegrand n C K g x) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (Spectral.ae_laguerreLaw_mem_chamber hnq),
      ae_fullRegressionConditionalMoment_spectral hnq hC.posSemidef K hgm] with x hx hy
    exact congrArg₂ (· * ·) (hspectral x.1 hx x.2) hy
  rw [integral_congr_ae heq]
  exact (integral_mul_parameterAverageOn _ _ _
    (Spectral.ae_laguerreLaw_mem_chamber hnq) _ _
    (integrable_selected_mul_haarFullRegressionIntegrand hn K hC hspectral hgm hjoint)).symm

theorem integral_fullRegression_remaining_spectral {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hgi : Integrable g (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, g X ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, fullRegressionSpectralAverage n C K g lam ∂regressionEigenLaw q n := by
  simpa only [one_mul] using integral_fullRegression_joint_spectral hn K hC
    (h := fun _ => 1) (f := fun _ => 1) (fun _ _ _ => rfl) hgm
      (by simpa only [one_mul] using hgi)

theorem integrable_fullRegressionSpectralAverage {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hgi : Integrable g (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fullRegressionSpectralAverage n C K g) (regressionEigenLaw q n) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  exact parameterAverageOn_integrable _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hnq) _
    (integrable_haarFullRegressionIntegrand hn K hC hgm hgi)

theorem integrable_selected_mul_fullRegressionSpectralAverage {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {f : (Fin q → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ Spectral.positiveChamber q, ∀ O : Spectral.Orth q,
      h (regressionSpectralMatrix (lam, O)) = f lam)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hjoint : Integrable (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) * g X)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun lam => f lam * fullRegressionSpectralAverage n C K g lam)
      (regressionEigenLaw q n) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  exact mul_parameterAverageOn_integrable _ _ _
    (Spectral.ae_laguerreLaw_mem_chamber hnq) _ _
    (integrable_selected_mul_haarFullRegressionIntegrand hn K hC hspectral hgm hjoint)

theorem memLp_fullRegressionSpectralAverage_two {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hgi : Integrable g (nonsingularWishartMeasure n (regressionScale K C)))
    (hg2i : Integrable (fun X => g X ^ 2)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    MemLp (fullRegressionSpectralAverage n C K g) 2 (regressionEigenLaw q n) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  have hsq := (measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable
    (integrable_sq_fullRegressionConditionalMoment hn K hC hgm hgi hg2i)
  have hsq' : Integrable (fun x => haarFullRegressionIntegrand n C K g x ^ 2)
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) :=
    hsq.congr ((ae_fullRegressionConditionalMoment_spectral hnq hC.posSemidef K hgm).fun_comp
      (fun r : ℝ => r ^ 2))
  exact parameterAverageOn_memLp_two _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hnq) _
    (measurable_haarFullRegressionIntegrand n C K hgm)
    (integrable_haarFullRegressionIntegrand hn K hC hgm hgi) hsq'

theorem fullSpectralConditionalMoment_compressionProduct_nonneg {q m : ℕ}
    (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) {ι : Type*} [Fintype ι]
    (D : ι → CompressionData (q + m)) (hB : ∀ i, (D i).offset.PosSemidef)
    (lam : Fin q → ℝ) :
    0 ≤ fullSpectralConditionalMoment n C K (compressionProduct D) lam O := by
  apply integral_nonneg_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure (n - q) C)] with x hx
  apply compressionProduct_nonneg D hB
  apply regressionGramWithMean_posSemidef
  simpa only [regressionNoiseLinearMap, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    hx.posSemidef.mul_mul_conjTranspose_same (regressionNoiseInjection q m)

theorem fullRegressionSpectralAverage_compressionProduct_nonneg {q m : ℕ}
    (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData (q + m))
    (hB : ∀ i, (D i).offset.PosSemidef) (lam : Fin q → ℝ) :
    0 ≤ fullRegressionSpectralAverage n C K (compressionProduct D) lam := by
  unfold fullRegressionSpectralAverage
  apply parameterAverageOn_nonneg
  intro lam' _ O
  exact fullSpectralConditionalMoment_compressionProduct_nonneg n C K ↑O D hB lam'

set_option maxHeartbeats 1000000 in
theorem allFiniteMoments_haarFullRegressionModel_entry
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (lam : Fin q → ℝ) :
    ∀ i j : Fin (q + m), HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        (fullSpectralRegressionModel K ↑y.1 lam y.2 :
          Matrix (Fin (q + m)) (Fin (q + m)) ℝ) i j)
      ((haarProb (Spectral.Orth q)).prod (regressionNoiseMeasure n q m C)) := by
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  let μ := (haarProb (Spectral.Orth q)).prod (regressionNoiseMeasure n q m C)
  let J := regressionNoiseInjection q m
  have hmean (i : Fin (q + m)) (a : Fin q) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        fullSpectralRegressionMean K ↑y.1 lam i a) μ := by
    have hm : HasAllFiniteMoments (fun O : Spectral.Orth q =>
        fullSpectralRegressionMean K ↑O lam i a) (haarProb (Spectral.Orth q)) := by
      apply allFiniteMoments_continuous_compact
      unfold fullSpectralRegressionMean
      fun_prop
    exact hm.comp_measurePreserving
      (measurePreserving_fst (μ := haarProb (Spectral.Orth q))
        (ν := regressionNoiseMeasure n q m C))
  have hz (i : Fin m) (a : Fin q) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m => y.2.1 a i) μ :=
    (allFiniteMoments_gaussian_coordinate 0 C i).comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin q =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C) a).comp
        (measurePreserving_fst.comp measurePreserving_snd))
  have hJz (i : Fin (q + m)) (a : Fin q) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m => (J * gaussianRowMatrix y.2.1) i a) μ :=
    HasAllFiniteMoments.matrix_left_mul_entry _ J hz i a
  have hW (i j : Fin m) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        (y.2.2 : Matrix (Fin m) (Fin m) ℝ) i j) μ :=
    (allFiniteMoments_wishart_entry (α := n - q) (Sigma := C) i j).comp_measurePreserving
      (measurePreserving_snd.comp measurePreserving_snd)
  have hJW (i j : Fin (q + m)) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        (J * (y.2.2 : Matrix (Fin m) (Fin m) ℝ) * Jᵀ) i j) μ :=
    HasAllFiniteMoments.matrix_right_mul_entry _ Jᵀ
      (fun i j => HasAllFiniteMoments.matrix_left_mul_entry _ J hW i j) i j
  have hentry (i j : Fin (q + m)) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        (fullSpectralRegressionModel K ↑y.1 lam y.2 :
          Matrix (Fin (q + m)) (Fin (q + m)) ℝ) i j) μ := by
    have hsum := HasAllFiniteMoments.finset_sum (μ := μ) Finset.univ
      (fun (a : Fin q) (y : Spectral.Orth q × RegressionNoise q m) =>
        (fullSpectralRegressionMean K ↑y.1 lam i a + (J * gaussianRowMatrix y.2.1) i a) *
        (fullSpectralRegressionMean K ↑y.1 lam j a + (J * gaussianRowMatrix y.2.1) j a))
      (fun a _ => ((hmean i a).add (hJz i a)).mul ((hmean j a).add (hJz j a)))
    simpa only [fullSpectralRegressionModel, coe_linearRegressionGramWithMean,
      Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] using hsum.add (hJW i j)
  exact hentry

theorem integrable_haar_fullSpectralConditionalMoment_compressionProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData (q + m))
    (hη : ∀ i, 0 ≤ (D i).exponent) (lam : Fin q → ℝ) :
    Integrable (fun O : Spectral.Orth q =>
      fullSpectralConditionalMoment n C K (compressionProduct D) lam ↑O)
      (haarProb (Spectral.Orth q)) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  exact (allFiniteMoments_compressionProduct_of_entries D hη _
    (allFiniteMoments_haarFullRegressionModel_entry hn hC K lam)).integrable.integral_prod_left

theorem monotoneOn_fullRegressionSpectralAverage_compressionProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData (q + m))
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((D i).size : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ n - q + 1) :
    MonotoneOn (fullRegressionSpectralAverage n C K (compressionProduct D))
      (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_fullSpectralConditionalMoment_compressionProduct hn hC K D hη lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_fullSpectralConditionalMoment_compressionProduct hn hC K ↑O D hB hη hsize
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

end Wishart
end
end CanonicalSource16

section CanonicalSource17
/- Source: Wishart/GaussianDeterminantMonotonicity.lean -/



/-!
# Weak Gaussian determinant comparison on the full semidefinite range

The background and covariance are both allowed to be singular. Tests need
only be increasing on the nonnegative support, and finite expectations are
the only analytic hypotheses in the comparison. Rectangular Gaussian images
are transported through their exact law, without an injectivity condition.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace WishartVerification

theorem integral_le_of_cdf_le_on_support {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hsμ : ∀ᵐ x ∂μ, x ∈ s) (hsν : ∀ᵐ x ∂ν, x ∈ s)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (horder : ∀ x, cdf ν x ≤ cdf μ x) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν := by
  let π := μ.quantileCoupling ν
  have hπ := μ.isCoupling_quantileCoupling ν
  have hfst : ∀ᵐ z ∂π, z.1 ∈ s :=
    hπ.measurePreserving_fst.quasiMeasurePreserving.ae hsμ
  have hsnd : ∀ᵐ z ∂π, z.2 ∈ s :=
    hπ.measurePreserving_snd.quasiMeasurePreserving.ae hsν
  have hfg : (fun z : ℝ × ℝ => f z.1) ≤ᵐ[π] fun z => f z.2 := by
    filter_upwards [μ.ae_fst_le_snd_quantileCoupling ν horder, hfst, hsnd]
      with z hz hzfst hzsnd
    exact hf hzfst hzsnd hz
  have hle := integral_mono_ae (hπ.integrable_comp_fst hμ)
    (hπ.integrable_comp_snd hν) hfg
  simpa only [hπ.integral_comp_fst hμ.aestronglyMeasurable,
    hπ.integral_comp_snd hν.aestronglyMeasurable] using hle

theorem integral_gaussian_rankOneDeterminant_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B C : Matrix ι ι ℝ} (hB : B.PosSemidef) (hC : C.PosSemidef)
    (v : EuclideanSpace ℝ ι) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : MonotoneOn f (Set.Ici 0)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hsi : Integrable (fun z => f (rankOneDeterminant B v s z)) (multivariateGaussian 0 C))
    (hti : Integrable (fun z => f (rankOneDeterminant B v t z)) (multivariateGaussian 0 C)) :
    (∫ z, f (rankOneDeterminant B v s z) ∂multivariateGaussian 0 C) ≤
      ∫ z, f (rankOneDeterminant B v t z) ∂multivariateGaussian 0 C := by
  let law (r : ℝ) := (multivariateGaussian 0 C).map (rankOneDeterminant B v r)
  letI (r : ℝ) : IsProbabilityMeasure (law r) := by infer_instance
  have hsupport (r : ℝ) : ∀ᵐ x ∂law r, x ∈ Set.Ici 0 := by
    change ∀ᵐ x ∂(multivariateGaussian 0 C).map (rankOneDeterminant B v r), 0 ≤ x
    rw [ae_map_iff (measurable_rankOneDeterminant B v r).aemeasurable measurableSet_Ici]
    exact Filter.Eventually.of_forall (rankOneDeterminant_nonneg hB v r)
  have hsi' : Integrable f (law s) :=
    (integrable_map_measure hfm.aestronglyMeasurable
      (measurable_rankOneDeterminant B v s).aemeasurable).mpr hsi
  have hti' : Integrable f (law t) :=
    (integrable_map_measure hfm.aestronglyMeasurable
      (measurable_rankOneDeterminant B v t).aemeasurable).mpr hti
  have hle := integral_le_of_cdf_le_on_support hf (hsupport s) (hsupport t) hsi' hti'
    (cdf_gaussian_shift_determinant_antitone hB hC v hs hst)
  have heq (r : ℝ) : (∫ x, f x ∂law r) =
      ∫ z, f (rankOneDeterminant B v r z) ∂multivariateGaussian 0 C :=
    integral_map (measurable_rankOneDeterminant B v r).aemeasurable hfm.aestronglyMeasurable
  rw [heq s, heq t] at hle
  exact hle

theorem integral_gaussian_rankOneDeterminant_rpow_monotoneOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B C : Matrix ι ι ℝ} (hB : B.PosSemidef) (hC : C.PosSemidef)
    (v : EuclideanSpace ℝ ι) {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (fun t : ℝ => ∫ z, rankOneDeterminant B v t z ^ η
      ∂multivariateGaussian 0 C) (Set.Ici 0) := by
  intro s hs t ht hst
  apply integral_gaussian_rankOneDeterminant_le hB hC v (measurable_id.pow_const _)
    (fun a ha b hb hab => Real.rpow_le_rpow ha hab hη) hs hst
  · exact integrable_gaussian_rankOneDeterminant_rpow 0 B C v s hη
  · exact integrable_gaussian_rankOneDeterminant_rpow 0 B C v t hη

theorem measurePreserving_rectangularStandardGaussian {m k : ℕ}
    (L : Matrix (Fin k) (Fin m) ℝ) :
    MeasurePreserving L.toEuclideanLin
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (L * Lᵀ)) := by
  refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
  simpa only [map_zero, add_zero, Matrix.mul_one] using
    map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
      Matrix.PosSemidef.one L 0

theorem integral_rectangularGaussian_rankOneDeterminant_le {m k : ℕ}
    {B : Matrix (Fin k) (Fin k) ℝ} (hB : B.PosSemidef)
    (L : Matrix (Fin k) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin k))
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hsi : Integrable (fun z => f (rankOneDeterminant B v s (L.toEuclideanLin z)))
      (multivariateGaussian 0 1))
    (hti : Integrable (fun z => f (rankOneDeterminant B v t (L.toEuclideanLin z)))
      (multivariateGaussian 0 1)) :
    (∫ z, f (rankOneDeterminant B v s (L.toEuclideanLin z)) ∂multivariateGaussian 0 1) ≤
      ∫ z, f (rankOneDeterminant B v t (L.toEuclideanLin z)) ∂multivariateGaussian 0 1 := by
  have hmap := measurePreserving_rectangularStandardGaussian L
  have hC : (L * Lᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose L
  have hmeas (r : ℝ) : Measurable (fun z => f (rankOneDeterminant B v r z)) :=
    hfm.comp (measurable_rankOneDeterminant B v r)
  have heq (r : ℝ) :
      (∫ z, f (rankOneDeterminant B v r z) ∂multivariateGaussian 0 (L * Lᵀ)) =
        ∫ z, f (rankOneDeterminant B v r (L.toEuclideanLin z)) ∂multivariateGaussian 0 1 := by
    rw [← hmap.map_eq, integral_map hmap.measurable.aemeasurable (hmeas r).aestronglyMeasurable]
  rw [← heq s, ← heq t]
  apply integral_gaussian_rankOneDeterminant_le hB hC v hfm hf hs hst
  · rw [← hmap.map_eq]
    exact (integrable_map_measure (hmeas s).aestronglyMeasurable hmap.measurable.aemeasurable).mpr hsi
  · rw [← hmap.map_eq]
    exact (integrable_map_measure (hmeas t).aestronglyMeasurable hmap.measurable.aemeasurable).mpr hti

end WishartVerification
end
end CanonicalSource17

section CanonicalSource18
/- Source: Wishart/OverlapSingleDeterminant.lean -/



/-!
# A single overlapping determinant has no additional shape restriction

After fixing the residual matrix and all other Gaussian rows, compression
leaves a positive semidefinite background and one Gaussian rank-one update.
The Gaussian comparison therefore handles arbitrary increasing outer tests,
including when either the background or the projected covariance is singular.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def compressedDeterminant {p k : ℕ} (E : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin p) (Fin k) ℝ) (X : SymmetricMatrix p) : ℝ :=
  (E + Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M).det

@[fun_prop] theorem measurable_compressedDeterminant {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (M : Matrix (Fin p) (Fin k) ℝ) :
    Measurable (compressedDeterminant E M) := by
  unfold compressedDeterminant
  fun_prop

theorem compressedDeterminant_nonneg {p k : ℕ}
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ compressedDeterminant E M X := by
  apply Matrix.PosSemidef.det_nonneg
  apply hE.add
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hX.conjTranspose_mul_mul_same M

theorem linearShiftedRowsSym_split {q m p : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ)
    (v : Fin (q + 1) → EuclideanSpace ℝ (Fin p)) (lam : Fin (q + 1) → ℝ)
    (a : Fin (q + 1)) (t : ℝ) (x : RegressionNoise (q + 1) m) :
    linearShiftedRowsSym L v (Function.update lam a t) x =
      linearShiftedRowsSym L (v ∘ a.succAbove) (lam ∘ a.succAbove)
        (splitRegressionRow a x).1 +
      rankOneSymmetric (L.toEuclideanLin (x.1 a) + Real.sqrt t • v a) := by
  unfold linearShiftedRowsSym rowBackground
  rw [Fin.sum_univ_succAbove _ a]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne _ _),
    splitRegressionRow, Function.comp_apply, gaussianRowsLinearMap]
  abel

theorem compressedDeterminant_add_gaussianRankOne {p m k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (M : Matrix (Fin p) (Fin k) ℝ)
    (B : SymmetricMatrix p) (L : Matrix (Fin p) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (t : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    compressedDeterminant E M (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt t • v)) =
      rankOneDeterminant (E + Mᵀ * (B : Matrix (Fin p) (Fin p) ℝ) * M)
        (Mᵀ.toEuclideanLin v) t ((Mᵀ * L).toEuclideanLin z) := by
  have hRank := congrArg (fun X : SymmetricMatrix k => (X : Matrix (Fin k) (Fin k) ℝ))
    (symmetricCongruence_rankOne Mᵀ (L.toEuclideanLin z + Real.sqrt t • v))
  simp only [Matrix.coe_symmetricCongruenceLinearMap_apply, coe_rankOneSymmetric,
    Matrix.transpose_transpose] at hRank
  have hlin : Mᵀ.toEuclideanLin (L.toEuclideanLin z + Real.sqrt t • v) =
      (Mᵀ * L).toEuclideanLin z + Real.sqrt t • Mᵀ.toEuclideanLin v := by
    rw [map_add, map_smul, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  simp only [compressedDeterminant, Submodule.coe_add, Matrix.mul_add,
    Matrix.add_mul, coe_rankOneSymmetric, hRank, hlin, rankOneDeterminant, add_assoc]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem monotoneOn_linearShiftedRows_compressedDet_coordinate_of_integrable
    {q m p k : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) (a : Fin q)
    (hint : ∀ t : ℝ, Integrable
      (fun x => f (compressedDeterminant E M (linearShiftedRowsSym L v (Function.update lam a t) x)))
      (gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))) :
    MonotoneOn (fun t : ℝ => ∫ x,
      f (compressedDeterminant E M (linearShiftedRowsSym L v (Function.update lam a t) x))
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)) (Set.Ici 0) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  cases q with
  | zero => exact Fin.elim0 a
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1
    let μ : Measure (RegressionNoise q m) :=
      gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)
    let B : RegressionNoise q m → SymmetricMatrix p :=
      linearShiftedRowsSym L (v ∘ a.succAbove) (lam ∘ a.succAbove)
    let A (y : RegressionNoise q m) := E + Mᵀ * (B y : Matrix (Fin p) (Fin p) ℝ) * M
    let F (t : ℝ) (y : RegressionNoise q m × EuclideanSpace ℝ (Fin m)) : ℝ :=
      f (rankOneDeterminant (A y.1) (Mᵀ.toEuclideanLin (v a)) t ((Mᵀ * L).toEuclideanLin y.2))
    have hsplit := measurePreserving_splitRegressionRow (1 : Matrix (Fin m) (Fin m) ℝ)
      (nonsingularWishartMeasure ν 1) a
    have hBm : Measurable B := measurable_linearShiftedRowsSym L _ _
    have hAm : Measurable A := by
      dsimp only [A]
      fun_prop
    have hFmeas (t : ℝ) : Measurable (F t) := by
      apply hfm.comp
      dsimp only [F, rankOneDeterminant]
      fun_prop
    have hFcomp (t : ℝ) : F t ∘ splitRegressionRow a =
        (fun x => f (compressedDeterminant E M
          (linearShiftedRowsSym L v (Function.update lam a t) x))) := by
      funext x
      dsimp only [F, A, B, Function.comp_apply]
      rw [linearShiftedRowsSym_split, compressedDeterminant_add_gaussianRankOne]
      rw [show (splitRegressionRow a x).2 = x.1 a from rfl]
    have hFi (t : ℝ) : Integrable (F t) (μ.prod γ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hFmeas t).aestronglyMeasurable hsplit.measurable.aemeasurable).mpr
      rw [hFcomp]
      exact hint t
    have heq (t : ℝ) :
        (∫ x, f (compressedDeterminant E M (linearShiftedRowsSym L v (Function.update lam a t) x))
          ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) =
        ∫ y, ∫ z, F t (y, z) ∂γ ∂μ := by
      rw [← integral_prod _ (hFi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hFmeas t).aestronglyMeasurable]
      exact congrArg (fun g => ∫ x, g x
        ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) (hFcomp t).symm
    have hA : ∀ᵐ y ∂μ, (A y).PosSemidef := by
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_posDef_nonsingularWishartMeasure ν (1 : Matrix (Fin m) (Fin m) ℝ))] with y hy
      apply hE.add
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (linearShiftedRowsSym_posSemidef L _ _ y hy.posSemidef).conjTranspose_mul_mul_same M
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hFi s).integral_prod_left (hFi t).integral_prod_left
    filter_upwards [hA, (hFi s).prod_right_ae, (hFi t).prod_right_ae] with y hy hys hyt
    exact integral_rectangularGaussian_rankOneDeterminant_le hy (Mᵀ * L)
      (Mᵀ.toEuclideanLin (v a)) hfm hf hs hst hys hyt

theorem allFiniteMoments_linearShiftedRows_compressedDet
    {q m p k : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ) (E : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin p) (Fin k) ℝ)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) :
    HasAllFiniteMoments (fun x => compressedDeterminant E M (linearShiftedRowsSym L v lam x))
      (gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  apply HasAllFiniteMoments.det
  intro i j
  apply (HasAllFiniteMoments.const (E i j)).add
  exact HasAllFiniteMoments.matrix_right_mul_entry _ M
    (fun a b => HasAllFiniteMoments.matrix_left_mul_entry _ Mᵀ
      (allFiniteMoments_linearShiftedRowsSym_entry 1
        (fun i j => allFiniteMoments_wishart_entry (α := ν)
          (Sigma := (1 : Matrix (Fin m) (Fin m) ℝ)) i j) L v lam) a b) i j

theorem monotoneOn_linearShiftedRows_compressedDet_rpow
    {q m p k : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) {η : ℝ} (hη : 0 ≤ η)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      compressedDeterminant E M (linearShiftedRowsSym L v lam x) ^ η
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))
      (Set.Ici (0 : Fin q → ℝ)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  apply monotoneOn_nonnegative_pi_of_update
  intro lam a
  apply monotoneOn_linearShiftedRows_compressedDet_coordinate_of_integrable hν L hE M
    (measurable_id.pow_const _) (fun x hx y hy hxy => Real.rpow_le_rpow hx hxy hη) v lam a
  intro t
  exact ((allFiniteMoments_linearShiftedRows_compressedDet hν L E M v
    (Function.update lam a t)).rpow hη).integrable

theorem integrable_linearShiftedRows_compressedDet_bounded
    {q m p k : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (A : ℝ)
    (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ A)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) :
    Integrable (fun x => f (compressedDeterminant E M (linearShiftedRowsSym L v lam x)))
      (gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  apply (integrable_const A).mono'
    ((hfm.comp (measurable_compressedDeterminant E M)).comp
      (measurable_linearShiftedRowsSym L v lam)).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure ν (1 : Matrix (Fin m) (Fin m) ℝ))] with x hx
  exact hbound _ (compressedDeterminant_nonneg hE M
    (linearShiftedRowsSym_posSemidef L v lam x hx.posSemidef))

theorem monotoneOn_linearShiftedRows_compressedDet_bounded
    {q m p k : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (A : ℝ) (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ A)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      f (compressedDeterminant E M (linearShiftedRowsSym L v lam x))
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))
      (Set.Ici (0 : Fin q → ℝ)) := by
  apply monotoneOn_nonnegative_pi_of_update
  intro lam a
  apply monotoneOn_linearShiftedRows_compressedDet_coordinate_of_integrable
    hν L hE M hfm hf v lam a
  intro t
  exact integrable_linearShiftedRows_compressedDet_bounded hν L hE M hfm A hbound v _

theorem monotoneOn_fullSpectralConditionalMoment_singleDet_rpow
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ) {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (fun lam => fullSpectralConditionalMoment n C K
      (fun X => compressedDeterminant E M X ^ η) lam O) (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by push_cast at hn; linarith
  intro lam hlam lam' hlam' hle
  dsimp only
  rw [fullSpectralConditionalMoment_standardNoise n hC K O lam
    ((measurable_compressedDeterminant E M).pow_const η),
    fullSpectralConditionalMoment_standardNoise n hC K O lam'
      ((measurable_compressedDeterminant E M).pow_const η)]
  exact monotoneOn_linearShiftedRows_compressedDet_rpow hν
    (regressionNoiseInjection q m * CFC.sqrt C) hE M hη (fullSpectralRegressionDirections K O)
      hlam hlam' hle

theorem monotoneOn_fullSpectralConditionalMoment_singleDet_bounded
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (A : ℝ) (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ A) :
    MonotoneOn (fun lam => fullSpectralConditionalMoment n C K
      (fun X => f (compressedDeterminant E M X)) lam O) (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by push_cast at hn; linarith
  intro lam hlam lam' hlam' hle
  dsimp only
  change fullSpectralConditionalMoment n C K (f ∘ compressedDeterminant E M) lam O ≤
    fullSpectralConditionalMoment n C K (f ∘ compressedDeterminant E M) lam' O
  rw [fullSpectralConditionalMoment_standardNoise n hC K O lam
    (hfm.comp (measurable_compressedDeterminant E M)),
    fullSpectralConditionalMoment_standardNoise n hC K O lam'
      (hfm.comp (measurable_compressedDeterminant E M))]
  exact monotoneOn_linearShiftedRows_compressedDet_bounded hν
    (regressionNoiseInjection q m * CFC.sqrt C) hE M hfm hf A hbound
      (fullSpectralRegressionDirections K O) hlam hlam' hle

def singleDetCompressionData {p k : ℕ} (E : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin p) (Fin k) ℝ) (η : ℝ) : Unit → CompressionData p :=
  fun _ => ⟨k, E, M, η⟩

set_option backward.isDefEq.respectTransparency false in
theorem compressionProduct_singleDet {p k : ℕ} (E : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin p) (Fin k) ℝ) (η : ℝ) (X : SymmetricMatrix p) :
    compressionProduct (singleDetCompressionData E M η) X =
      compressedDeterminant E M X ^ η := by
  simp only [compressionProduct, Fintype.prod_unique, singleDetCompressionData, compressedDeterminant]

theorem monotoneOn_fullRegressionSpectralAverage_singleDet_rpow
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ) {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (fullRegressionSpectralAverage n C K
      (fun X => compressedDeterminant E M X ^ η)) (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    have hf : compressionProduct (singleDetCompressionData E M η) =
        (fun X => compressedDeterminant E M X ^ η) :=
      funext (compressionProduct_singleDet E M η)
    simpa only [haarFullRegressionIntegrand, hf] using
      integrable_haar_fullSpectralConditionalMoment_compressionProduct hn hC K
        (singleDetCompressionData E M η) (fun _ => hη) lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_fullSpectralConditionalMoment_singleDet_rpow hn hC K ↑O hE M hη
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

theorem fullSpectralRegressionModel_posSemidef {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (x : RegressionNoise q m)
    (hW : (x.2 : Matrix (Fin m) (Fin m) ℝ).PosSemidef) :
    (fullSpectralRegressionModel K O lam x : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef := by
  apply regressionGramWithMean_posSemidef
  simpa only [regressionNoiseLinearMap, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    hW.mul_mul_conjTranspose_same (regressionNoiseInjection q m)

theorem norm_fullSpectralConditionalMoment_singleDet_le
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ)
    {f : ℝ → ℝ} (A : ℝ) (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ A)
    (lam : Fin q → ℝ) :
    ‖fullSpectralConditionalMoment n C K (fun X => f (compressedDeterminant E M X)) lam O‖ ≤ A := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  have hb : ∀ᵐ x ∂regressionNoiseMeasure n q m C,
      ‖f (compressedDeterminant E M (fullSpectralRegressionModel K O lam x))‖ ≤ A := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_posDef_nonsingularWishartMeasure (n - q) C)] with x hx
    exact hbound _ (compressedDeterminant_nonneg hE M
      (fullSpectralRegressionModel_posSemidef K O lam x hx.posSemidef))
  simpa only [fullSpectralConditionalMoment, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

theorem integrable_haar_fullSpectralConditionalMoment_singleDet_bounded
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (A : ℝ)
    (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ A) (lam : Fin q → ℝ) :
    Integrable (fun O : Spectral.Orth q => fullSpectralConditionalMoment n C K
      (fun X => f (compressedDeterminant E M X)) lam ↑O) (haarProb (Spectral.Orth q)) := by
  apply (integrable_const A).mono'
  · exact ((measurable_fullSpectralConditionalMoment n C K
      (hfm.comp (measurable_compressedDeterminant E M))).comp
        (measurable_const.prodMk measurable_subtype_coe)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun O =>
      norm_fullSpectralConditionalMoment_singleDet_le hn hC K ↑O hE M A hbound lam

theorem monotoneOn_fullRegressionSpectralAverage_singleDet_bounded
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (A : ℝ) (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ A) :
    MonotoneOn (fullRegressionSpectralAverage n C K
      (fun X => f (compressedDeterminant E M X))) (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_fullSpectralConditionalMoment_singleDet_bounded hn hC K hE M hfm A hbound lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_fullSpectralConditionalMoment_singleDet_bounded hn hC K ↑O hE M hfm hf A hbound
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

theorem fullRegressionSpectralAverage_singleDet_nonneg
    {q m k : ℕ} (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ)
    {f : ℝ → ℝ} (hf0 : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ f t) (lam : Fin q → ℝ) :
    0 ≤ fullRegressionSpectralAverage n C K (fun X => f (compressedDeterminant E M X)) lam := by
  apply parameterAverageOn_nonneg _ _ _ _ lam
  intro lam hlam O
  apply integral_nonneg_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure (n - q) C)] with x hx
  exact hf0 _ (compressedDeterminant_nonneg hE M
    (fullSpectralRegressionModel_posSemidef K ↑O lam x hx.posSemidef))

end Wishart
end
end CanonicalSource18

section CanonicalSource19
/- Source: Wishart/LoewnerCompressionProducts.lean -/



/-!
# Loewner monotonicity of nonnegative compression determinant products

The determinant comparison is obtained from the ordered eigenvalue comparison
and the product formula, including singular matrices. Positive semidefinite
offsets and arbitrary rectangular compressions preserve that comparison.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem det_eq_prod_ascendingSpectrum {p : ℕ} (X : SymmetricMatrix p) :
    (X : Matrix (Fin p) (Fin p) ℝ).det = ∏ i, Spectral.ascendingSpectrum X i := by
  obtain ⟨O, hO⟩ := Spectral.exists_conjugate_diagonal_ascendingSpectrum X
  calc
    (X : Matrix (Fin p) (Fin p) ℝ).det =
        (Spectral.conjugate O (Spectral.diagonalSym (Spectral.ascendingSpectrum X)) :
          Matrix (Fin p) (Fin p) ℝ).det := congrArg (fun Z : SymmetricMatrix p =>
            (Z : Matrix (Fin p) (Fin p) ℝ).det) hO.symm
    _ = _ := by rw [Spectral.det_conjugate]; exact Matrix.det_diagonal

theorem det_le_of_posSemidef_sub {p : ℕ} (X Y : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    (X : Matrix (Fin p) (Fin p) ℝ).det ≤ (Y : Matrix (Fin p) (Fin p) ℝ).det := by
  rw [det_eq_prod_ascendingSpectrum, det_eq_prod_ascendingSpectrum]
  apply Finset.prod_le_prod₀
  · intro i hi
    simpa only [Spectral.ascendingSpectrum, Spectral.coordinateSpectrum, Function.comp_apply] using
      hX.eigenvalues_nonneg (Spectral.ascendingIndexEquiv p i)
  · intro i hi
    exact Spectral.ascendingSpectrum_mono_of_posSemidef X Y hXY i

def affineCompressionSym {p k : ℕ} (E : Matrix (Fin k) (Fin k) ℝ)
    (hE : E.IsHermitian) (M : Matrix (Fin p) (Fin k) ℝ) (X : SymmetricMatrix p) :
    SymmetricMatrix k :=
  ⟨E, Matrix.isHermitian_iff_isSelfAdjoint.mp hE⟩ + Matrix.symmetricCongruenceLinearMap Mᵀ X

@[simp] theorem coe_affineCompressionSym {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (hE : E.IsHermitian)
    (M : Matrix (Fin p) (Fin k) ℝ) (X : SymmetricMatrix p) :
    (affineCompressionSym E hE M X : Matrix (Fin k) (Fin k) ℝ) =
      E + Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M := by
  simp only [affineCompressionSym, Submodule.coe_add,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_transpose]

theorem compressedDeterminant_mono {p k : ℕ}
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) (X Y : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    compressedDeterminant E M X ≤ compressedDeterminant E M Y := by
  have hAX : (affineCompressionSym E hE.isHermitian M X :
      Matrix (Fin k) (Fin k) ℝ).PosSemidef := by
    rw [coe_affineCompressionSym]
    apply hE.add
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hX.conjTranspose_mul_mul_same M
  have hdiff : ((affineCompressionSym E hE.isHermitian M Y :
      Matrix (Fin k) (Fin k) ℝ) - affineCompressionSym E hE.isHermitian M X).PosSemidef := by
    simp only [coe_affineCompressionSym, add_sub_add_left_eq_sub]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul] using
      hXY.conjTranspose_mul_mul_same M
  simpa only [coe_affineCompressionSym, compressedDeterminant] using
    det_le_of_posSemidef_sub (affineCompressionSym E hE.isHermitian M X)
      (affineCompressionSym E hE.isHermitian M Y) hAX hdiff

theorem compressionProduct_loewner_mono {p : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (X Y : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    compressionProduct D X ≤ compressionProduct D Y := by
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Real.rpow_nonneg (compressedDeterminant_nonneg (hB i) (D i).linear hX) _
  · intro i hi
    exact Real.rpow_le_rpow (compressedDeterminant_nonneg (hB i) (D i).linear hX)
      (compressedDeterminant_mono (hB i) (D i).linear X Y hX hXY) (hη i)

theorem allFiniteMoments_wishart_compressionProduct
    {p : ℕ} {n : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hη : ∀ i, 0 ≤ (D i).exponent) :
    HasAllFiniteMoments (compressionProduct D) (nonsingularWishartMeasure n Sigma) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  exact allFiniteMoments_compressionProduct_of_entries D hη id
    (fun i j => allFiniteMoments_wishart_entry i j)

theorem spectralMatrix_posSemidef {p : ℕ} (O : Spectral.Orth p)
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    (regressionSpectralMatrix (lam, O) : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  simpa only [regressionSpectralMatrix, Spectral.conjugate,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Spectral.diagonalSym,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosSemidef.diagonal hlam).mul_mul_conjTranspose_same (O : Matrix (Fin p) (Fin p) ℝ)

theorem spectralMatrix_difference_posSemidef {p : ℕ} (O : Spectral.Orth p)
    (lam lam' : Fin p → ℝ) (hle : lam ≤ lam') :
    ((regressionSpectralMatrix (lam', O) : Matrix (Fin p) (Fin p) ℝ) -
      regressionSpectralMatrix (lam, O)).PosSemidef := by
  have hdiag : Matrix.diagonal (fun i => lam' i - lam i) =
      Matrix.diagonal lam' - Matrix.diagonal lam := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  have h := (Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hle i))).mul_mul_conjTranspose_same
    (O : Matrix (Fin p) (Fin p) ℝ)
  simpa only [hdiag, regressionSpectralMatrix, Spectral.conjugate,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Spectral.diagonalSym,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul] using h

end Wishart
end
end CanonicalSource19
