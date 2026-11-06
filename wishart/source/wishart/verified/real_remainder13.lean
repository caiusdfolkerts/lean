module

public import wishart.verified.real_remainder12

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

section CanonicalSource120
/- Source: Wishart/GramSingleDeterminant.lean -/



/-!
# Unrestricted single determinant comparison for integer Gaussian Gram noise

Both the residual Gram degree and the covariance may be singular. A selected
Gaussian row is separated by its exact product law. A compressed determinant
then becomes a positive semidefinite quadratic form in that row, so its proved
Gaussian stochastic comparison imposes no dimension or degree restriction.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace WishartVerification

theorem integral_linearGaussian_rankOneDeterminant_le {p k : ℕ}
    {B : Matrix (Fin k) (Fin k) ℝ} (hB : B.PosSemidef)
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    (L : Matrix (Fin k) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin k))
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hsi : Integrable (fun z => f (rankOneDeterminant B v s (L.toEuclideanLin z)))
      (multivariateGaussian 0 C))
    (hti : Integrable (fun z => f (rankOneDeterminant B v t (L.toEuclideanLin z)))
      (multivariateGaussian 0 C)) :
    (∫ z, f (rankOneDeterminant B v s (L.toEuclideanLin z)) ∂multivariateGaussian 0 C) ≤
      ∫ z, f (rankOneDeterminant B v t (L.toEuclideanLin z)) ∂multivariateGaussian 0 C := by
  have hmap : MeasurePreserving L.toEuclideanLin
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (L * C * Lᵀ)) := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    simpa only [map_zero, add_zero] using map_affine_multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin p)) hC L 0
  have hLC : (L * C * Lᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hC.mul_mul_conjTranspose_same L
  have hmeas (r : ℝ) : Measurable (fun z => f (rankOneDeterminant B v r z)) :=
    hfm.comp (measurable_rankOneDeterminant B v r)
  have heq (r : ℝ) :
      (∫ z, f (rankOneDeterminant B v r z) ∂multivariateGaussian 0 (L * C * Lᵀ)) =
        ∫ z, f (rankOneDeterminant B v r (L.toEuclideanLin z)) ∂multivariateGaussian 0 C := by
    rw [← hmap.map_eq, integral_map hmap.measurable.aemeasurable (hmeas r).aestronglyMeasurable]
  rw [← heq s, ← heq t]
  apply integral_gaussian_rankOneDeterminant_le hB hLC v hfm hf hs hst
  · rw [← hmap.map_eq]
    exact (integrable_map_measure (hmeas s).aestronglyMeasurable hmap.measurable.aemeasurable).mpr hsi
  · rw [← hmap.map_eq]
    exact (integrable_map_measure (hmeas t).aestronglyMeasurable hmap.measurable.aemeasurable).mpr hti

end WishartVerification

namespace Wishart

theorem shiftedRowsSym_split {q p : ℕ}
    (v : Fin (q + 1) → EuclideanSpace ℝ (Fin p)) (lam : Fin (q + 1) → ℝ)
    (a : Fin (q + 1)) (t : ℝ) (x : RegressionNoise (q + 1) p) :
    shiftedRowsSym v (Function.update lam a t) x =
      shiftedRowsSym (v ∘ a.succAbove) (lam ∘ a.succAbove) (splitRegressionRow a x).1 +
        rankOneSymmetric (x.1 a + Real.sqrt t • v a) := by
  apply Subtype.ext
  simpa only [coe_shiftedRowsSym, Submodule.coe_add, coe_rankOneSymmetric] using
    shiftedRowsGram_split v lam a t x

theorem compressedDeterminant_add_rankOne {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (M : Matrix (Fin p) (Fin k) ℝ)
    (B : SymmetricMatrix p) (v : EuclideanSpace ℝ (Fin p))
    (t : ℝ) (z : EuclideanSpace ℝ (Fin p)) :
    compressedDeterminant E M (B + rankOneSymmetric (z + Real.sqrt t • v)) =
      rankOneDeterminant (E + Mᵀ * (B : Matrix (Fin p) (Fin p) ℝ) * M)
        (Mᵀ.toEuclideanLin v) t (Mᵀ.toEuclideanLin z) := by
  simpa only [Matrix.toLpLin_one, LinearMap.id_apply, Matrix.mul_one] using
    compressedDeterminant_add_gaussianRankOne E M B (1 : Matrix (Fin p) (Fin p) ℝ) v t z

theorem shiftedRowsSym_posSemidef {q p : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ)
    (x : RegressionNoise q p) (hW : (x.2 : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (shiftedRowsSym v lam x : Matrix (Fin p) (Fin p) ℝ).PosSemidef :=
  hW.add (rowBackground_posSemidef v lam x.1)

/-- A single determinant under any independent PSD residual law. Its finite
integrability hypotheses are discharged below for the actual Gram law. -/
theorem monotoneOn_shiftedRows_compressedDet_coordinate_of_integrable
    {q p k : ℕ} {ν : Measure (SymmetricMatrix p)} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ W : SymmetricMatrix p ∂ν, (W : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) (a : Fin q)
    (hint : ∀ t : ℝ, Integrable
      (fun x => f (compressedDeterminant E M (shiftedRowsSym v (Function.update lam a t) x)))
      (gaussianResidualMeasure q C ν)) :
    MonotoneOn (fun t : ℝ => ∫ x,
      f (compressedDeterminant E M (shiftedRowsSym v (Function.update lam a t) x))
        ∂gaussianResidualMeasure q C ν) (Set.Ici 0) := by
  cases q with
  | zero => exact Fin.elim0 a
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
    let μ : Measure (RegressionNoise q p) := gaussianResidualMeasure q C ν
    let B : RegressionNoise q p → SymmetricMatrix p :=
      shiftedRowsSym (v ∘ a.succAbove) (lam ∘ a.succAbove)
    let A (y : RegressionNoise q p) := E + Mᵀ * (B y : Matrix (Fin p) (Fin p) ℝ) * M
    let F (t : ℝ) (y : RegressionNoise q p × EuclideanSpace ℝ (Fin p)) : ℝ :=
      f (rankOneDeterminant (A y.1) (Mᵀ.toEuclideanLin (v a)) t (Mᵀ.toEuclideanLin y.2))
    have hsplit := measurePreserving_splitRegressionRow C ν a
    have hFmeas (t : ℝ) : Measurable (F t) := by
      apply hfm.comp
      dsimp only [F, A, B, rankOneDeterminant]
      fun_prop
    have hFcomp (t : ℝ) : F t ∘ splitRegressionRow a =
        (fun x => f (compressedDeterminant E M
          (shiftedRowsSym v (Function.update lam a t) x))) := by
      funext x
      dsimp only [F, A, B, Function.comp_apply]
      rw [shiftedRowsSym_split, compressedDeterminant_add_rankOne]
      rfl
    have hFi (t : ℝ) : Integrable (F t) (μ.prod γ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hFmeas t).aestronglyMeasurable hsplit.measurable.aemeasurable).mpr
      rw [hFcomp]
      exact hint t
    have heq (t : ℝ) :
        (∫ x, f (compressedDeterminant E M (shiftedRowsSym v (Function.update lam a t) x))
          ∂gaussianResidualMeasure (q + 1) C ν) = ∫ y, ∫ z, F t (y, z) ∂γ ∂μ := by
      rw [← integral_prod _ (hFi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hFmeas t).aestronglyMeasurable]
      exact congrArg (fun g => ∫ x, g x ∂gaussianResidualMeasure (q + 1) C ν) (hFcomp t).symm
    have hA : ∀ᵐ y ∂μ, (A y).PosSemidef := by
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae hν] with y hy
      apply hE.add
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (shiftedRowsSym_posSemidef _ _ y hy).conjTranspose_mul_mul_same M
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hFi s).integral_prod_left (hFi t).integral_prod_left
    filter_upwards [hA, (hFi s).prod_right_ae, (hFi t).prod_right_ae] with y hy hys hyt
    exact integral_linearGaussian_rankOneDeterminant_le hy hC Mᵀ
      (Mᵀ.toEuclideanLin (v a)) hfm hf hs hst hys hyt

theorem allFiniteMoments_gramShiftedRows_compressedDet {q p k : ℕ} (d : ℕ)
    (C : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin p) (Fin k) ℝ)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) :
    HasAllFiniteMoments (fun x => compressedDeterminant E M (shiftedRowsSym v lam x))
      (gaussianResidualMeasure q C (wishartGramMeasure d C)) := by
  apply HasAllFiniteMoments.det
  intro i j
  apply (HasAllFiniteMoments.const (E i j)).add
  apply HasAllFiniteMoments.matrix_right_mul_entry _ M
  intro a b
  apply HasAllFiniteMoments.matrix_left_mul_entry _ Mᵀ
  intro u w
  simpa only [coe_shiftedRowsSym] using
    allFiniteMoments_shiftedRowsGram_entry C (allFiniteMoments_gram_entry d C) v lam u w

theorem monotoneOn_gramShiftedRows_compressedDet_bounded {q p k : ℕ}
    (d : ℕ) {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (A : ℝ) (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ A)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      f (compressedDeterminant E M (shiftedRowsSym v lam x))
        ∂gaussianResidualMeasure q C (wishartGramMeasure d C))
      (Set.Ici (0 : Fin q → ℝ)) := by
  apply monotoneOn_nonnegative_pi_of_update
  intro lam a
  apply monotoneOn_shiftedRows_compressedDet_coordinate_of_integrable
    (ae_posSemidef_wishartGramMeasure d C) hC hE M hfm hf v lam a
  intro t
  apply (integrable_const A).mono'
    ((hfm.comp (measurable_compressedDeterminant E M)).comp
      (measurable_shiftedRowsSym v (Function.update lam a t))).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posSemidef_wishartGramMeasure d C)] with x hx
  exact hbound _ (compressedDeterminant_nonneg hE M (shiftedRowsSym_posSemidef _ _ x hx))

theorem monotoneOn_gramShiftedRows_compressedDet_finiteMaximum {q p k : ℕ}
    (d : ℕ) {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      finiteMaximum (fun j => Real.exp (b j) *
        compressedDeterminant E M (shiftedRowsSym v lam x) ^ a j)
          ∂gaussianResidualMeasure q C (wishartGramMeasure d C))
      (Set.Ici (0 : Fin q → ℝ)) := by
  apply monotoneOn_nonnegative_pi_of_update
  intro lam c
  apply monotoneOn_shiftedRows_compressedDet_coordinate_of_integrable
    (ae_posSemidef_wishartGramMeasure d C) hC hE M
    (measurable_finiteMaximum _ fun j => measurable_const.mul (measurable_id.pow_const (a j)))
    (fun x hx y hy hxy => finiteMaximum_mono
      (x := fun j => Real.exp (b j) * x ^ a j)
      (y := fun j => Real.exp (b j) * y ^ a j) fun j =>
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy (ha j)) (Real.exp_pos _).le) v lam c
  intro t
  exact (hasAllFiniteMoments_finiteMaximum _ fun j =>
    ((allFiniteMoments_gramShiftedRows_compressedDet d C E M v
      (Function.update lam c t)).rpow (ha j)).const_mul (Real.exp (b j))).integrable

/-- The exact one-factor finite-outer representation used by the general
geometric outer-function limit. No compression rank bound is present. -/
theorem monotoneOn_gramShiftedRows_single_finiteOuter {q p k : ℕ}
    (d : ℕ) {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      affineMaximumProduct 0 (fun _ : Unit => k) (fun _ => E) (fun _ => M)
        (fun _ => a) (fun _ => b) (shiftedRowsSym v lam x)
          ∂gaussianResidualMeasure q C (wishartGramMeasure d C))
      (Set.Ici (0 : Fin q → ℝ)) := by
  simpa only [affineMaximumProduct, Fintype.prod_unique, regularizedCompression,
    compressionCLM_apply, zero_smul, add_zero, compressedDeterminant] using
    monotoneOn_gramShiftedRows_compressedDet_finiteMaximum d hC hE M a b ha v

end Wishart
end
end CanonicalSource120

section CanonicalSource121
/- Source: Wishart/SingularRegressionMoments.lean -/



/-!
# Exact spectral moment identities for every integer Gram law

The spectral parameter has the actual positive Laguerre law, and the remaining
source consists of an independent full Haar frame and Gaussian entries. The
three expectation identities are pushforward and Fubini identities for that
source. They do not posit a conditional expectation or a spectral density.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification Wishart.Spectral
open scoped Classical ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def singularRegressionFrameNoise (n q m : ℕ) :
    Measure (Orth q × Matrix (Fin n) (Fin m) ℝ) :=
  (haarProb (Orth q)).prod (gaussianMatrixMeasure n m)

instance singularRegressionFrameNoise_isProbability (n q m : ℕ) :
    IsProbabilityMeasure (singularRegressionFrameNoise n q m) := by
  unfold singularRegressionFrameNoise
  infer_instance

def singularRegressionSpectralAverage {q m : ℕ} (n : ℕ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix (q + m) → ℝ) : (Fin (min n q) → ℝ) → ℝ :=
  parameterAverageOn (singularRegressionFrameNoise n q m)
    (positiveChamber (min n q)) (fun z => g (singularSpectralRegressionModel K C z))

@[fun_prop] theorem measurable_singularRegressionSpectralAverage {q m : ℕ} (n : ℕ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix (q + m) → ℝ} (hg : Measurable g) :
    Measurable (singularRegressionSpectralAverage n C K g) :=
  parameterAverageOn_measurable _ _ (orderedChamber_measurable _ measurableSet_Ioi) _
    (hg.comp (measurable_singularSpectralRegressionModel K C))

theorem singularRegressionSpectralAverage_eq {q m : ℕ} (n : ℕ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix (q + m) → ℝ) {lam : Fin (min n q) → ℝ}
    (hlam : lam ∈ positiveChamber (min n q)) :
    singularRegressionSpectralAverage n C K g lam =
      ∫ u, g (singularSpectralRegressionModel K C (lam, u))
        ∂singularRegressionFrameNoise n q m :=
  parameterAverageOn_of_mem _ _ _ hlam

theorem measurePreserving_singularSpectralRegressionModel {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) :
    MeasurePreserving (singularSpectralRegressionModel (n := n) K C)
      (singularRegressionSource n q m) (wishartGramMeasure n (regressionScale K C)) :=
  ⟨measurable_singularSpectralRegressionModel K C, map_singularSpectralRegressionModel K hC⟩

theorem ae_singularRegression_selected_spectral {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    {h : SymmetricMatrix q → ℝ} {f : (Fin (min n q) → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ positiveChamber (min n q), ∀ O : Orth q,
      h (positiveGramSpectralMatrix n q lam O) = f lam) :
    (fun z => h (regressionSelectedBlock (singularSpectralRegressionModel K C z))) =ᵐ[
      singularRegressionSource n q m] (fun z => f z.1) := by
  letI := positiveGramEigenLaw_isProbability n q
  have hch := (Measure.quasiMeasurePreserving_fst (μ := positiveGramEigenLaw n q)
    (ν := singularRegressionFrameNoise n q m)).ae (ae_positiveGramEigenLaw_mem_chamber n q)
  filter_upwards [ae_singularSpectralRegressionModel_selected (n := n) K C, hch] with z hz hzc
  rw [hz]
  exact hspectral z.1 hzc z.2.1

theorem integrable_singularRegressionSource {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {g : SymmetricMatrix (q + m) → ℝ}
    (hgi : Integrable g (wishartGramMeasure n (regressionScale K C))) :
    Integrable (fun z => g (singularSpectralRegressionModel K C z))
      (singularRegressionSource n q m) :=
  (measurePreserving_singularSpectralRegressionModel K hC).integrable_comp_of_integrable hgi

theorem integral_singularRegression_selected_spectral {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {h : SymmetricMatrix q → ℝ} (hh : Measurable h)
    {f : (Fin (min n q) → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ positiveChamber (min n q), ∀ O : Orth q,
      h (positiveGramSpectralMatrix n q lam O) = f lam) :
    (∫ X, h (regressionSelectedBlock X) ∂wishartGramMeasure n (regressionScale K C)) =
      ∫ lam, f lam ∂positiveGramEigenLaw n q := by
  letI := positiveGramEigenLaw_isProbability n q
  rw [← map_singularSpectralRegressionModel (n := n) K hC,
    integral_map (measurable_singularSpectralRegressionModel K C).aemeasurable
      (show Measurable (fun X : SymmetricMatrix (q + m) => h (regressionSelectedBlock X)) from hh.comp (by fun_prop)).aestronglyMeasurable,
    integral_congr_ae (ae_singularRegression_selected_spectral K C hspectral)]
  change (∫ z, f z.1 ∂(positiveGramEigenLaw n q).prod
    (singularRegressionFrameNoise n q m)) = _
  simp only [integral_fun_fst, probReal_univ, one_smul]

theorem integrable_singularRegression_selected_source {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {h : SymmetricMatrix q → ℝ}
    {f : (Fin (min n q) → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ positiveChamber (min n q), ∀ O : Orth q,
      h (positiveGramSpectralMatrix n q lam O) = f lam)
    (hhi : Integrable (fun X => h (regressionSelectedBlock X))
      (wishartGramMeasure n (regressionScale K C))) :
    Integrable f (positiveGramEigenLaw n q) := by
  letI := positiveGramEigenLaw_isProbability n q
  have hi := (integrable_singularRegressionSource K hC hhi).congr
    (ae_singularRegression_selected_spectral K C hspectral)
  have hi' := hi.integral_prod_left
  simpa only [integral_const, probReal_univ, one_smul] using hi'

theorem integrable_singularRegression_joint_source {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {h : SymmetricMatrix q → ℝ}
    {f : (Fin (min n q) → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ positiveChamber (min n q), ∀ O : Orth q,
      h (positiveGramSpectralMatrix n q lam O) = f lam)
    {g : SymmetricMatrix (q + m) → ℝ}
    (hjoint : Integrable (fun X => h (regressionSelectedBlock X) * g X)
      (wishartGramMeasure n (regressionScale K C))) :
    Integrable (fun z => f z.1 * g (singularSpectralRegressionModel K C z))
      (singularRegressionSource n q m) := by
  apply (integrable_singularRegressionSource K hC hjoint).congr
  exact (ae_singularRegression_selected_spectral K C hspectral).mono fun z hz =>
    congrArg (fun r => r * g (singularSpectralRegressionModel K C z)) hz

theorem integral_singularRegression_joint_spectral {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {h : SymmetricMatrix q → ℝ} (hh : Measurable h)
    {f : (Fin (min n q) → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ positiveChamber (min n q), ∀ O : Orth q,
      h (positiveGramSpectralMatrix n q lam O) = f lam)
    {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hjoint : Integrable (fun X => h (regressionSelectedBlock X) * g X)
      (wishartGramMeasure n (regressionScale K C))) :
    (∫ X, h (regressionSelectedBlock X) * g X ∂wishartGramMeasure n (regressionScale K C)) =
      ∫ lam, f lam * singularRegressionSpectralAverage n C K g lam ∂positiveGramEigenLaw n q := by
  letI := positiveGramEigenLaw_isProbability n q
  rw [← map_singularSpectralRegressionModel (n := n) K hC,
    integral_map (measurable_singularSpectralRegressionModel K C).aemeasurable
      (show Measurable (fun X : SymmetricMatrix (q + m) => h (regressionSelectedBlock X) * g X) from (hh.comp (by fun_prop)).mul hgm).aestronglyMeasurable]
  have heq := (ae_singularRegression_selected_spectral K C hspectral).mono fun z hz =>
    congrArg (fun r => r * g (singularSpectralRegressionModel K C z)) hz
  rw [integral_congr_ae heq]
  exact (integral_mul_parameterAverageOn _ _ _ (ae_positiveGramEigenLaw_mem_chamber n q) _ _
    (integrable_singularRegression_joint_source K hC hspectral hjoint)).symm

theorem integral_singularRegression_remaining_spectral {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {g : SymmetricMatrix (q + m) → ℝ} (hgm : Measurable g)
    (hgi : Integrable g (wishartGramMeasure n (regressionScale K C))) :
    (∫ X, g X ∂wishartGramMeasure n (regressionScale K C)) =
      ∫ lam, singularRegressionSpectralAverage n C K g lam ∂positiveGramEigenLaw n q := by
  simpa only [one_mul] using integral_singularRegression_joint_spectral K hC
    (h := fun _ => 1) measurable_const (f := fun _ => 1) (fun _ _ _ => rfl) hgm
    (by simpa only [one_mul] using hgi)

theorem integrable_singularRegressionSpectralAverage {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {g : SymmetricMatrix (q + m) → ℝ}
    (hgi : Integrable g (wishartGramMeasure n (regressionScale K C))) :
    Integrable (singularRegressionSpectralAverage n C K g) (positiveGramEigenLaw n q) := by
  letI := positiveGramEigenLaw_isProbability n q
  exact parameterAverageOn_integrable _ _ _ (ae_positiveGramEigenLaw_mem_chamber n q) _
    (integrable_singularRegressionSource K hC hgi)

theorem integrable_selected_mul_singularRegressionSpectralAverage {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) {h : SymmetricMatrix q → ℝ}
    {f : (Fin (min n q) → ℝ) → ℝ}
    (hspectral : ∀ lam ∈ positiveChamber (min n q), ∀ O : Orth q,
      h (positiveGramSpectralMatrix n q lam O) = f lam)
    {g : SymmetricMatrix (q + m) → ℝ}
    (hjoint : Integrable (fun X => h (regressionSelectedBlock X) * g X)
      (wishartGramMeasure n (regressionScale K C))) :
    Integrable (fun lam => f lam * singularRegressionSpectralAverage n C K g lam)
      (positiveGramEigenLaw n q) := by
  letI := positiveGramEigenLaw_isProbability n q
  exact mul_parameterAverageOn_integrable _ _ _ (ae_positiveGramEigenLaw_mem_chamber n q) _ _
    (integrable_singularRegression_joint_source K hC hspectral hjoint)

/-- Every Gaussian matrix coordinate has all finite moments under the literal
product of its independent normal entries. -/
theorem allFiniteMoments_gaussianMatrix_entry {n p : ℕ} (i : Fin n) (j : Fin p) :
    HasAllFiniteMoments (fun G : Matrix (Fin n) (Fin p) ℝ => G i j)
      (gaussianMatrixMeasure n p) := by
  have h : HasAllFiniteMoments (fun x : ℝ => x) (gaussianReal 0 1) :=
    fun r hr => memLp_id_gaussianReal' r hr
  exact h.comp_measurePreserving
    ((measurePreserving_eval (fun _ : Fin p => gaussianReal 0 1) j).comp
      (measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) i))

set_option maxHeartbeats 1000000 in
theorem allFiniteMoments_singularRegressionFrameNoise_entry {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (lam : Fin (min n q) → ℝ) :
    ∀ i j : Fin (q + m), HasAllFiniteMoments
      (fun u : Orth q × Matrix (Fin n) (Fin m) ℝ =>
        (singularSpectralRegressionModel K C (lam, u) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) i j)
      (singularRegressionFrameNoise n q m) := by
  let μ := singularRegressionFrameNoise n q m
  let L := singularNoiseFactor (q := q) C
  have hmean (i : Fin (q + m)) (a : Fin n) : HasAllFiniteMoments
      (fun u : Orth q × Matrix (Fin n) (Fin m) ℝ => singularMeanMatrix n K u.1 lam i a) μ := by
    have hm : HasAllFiniteMoments (fun O : Orth q => singularMeanMatrix n K O lam i a)
        (haarProb (Orth q)) := by
      apply allFiniteMoments_continuous_compact
      unfold singularMeanMatrix singularSpectralFactor
      fun_prop
    exact hm.comp_measurePreserving measurePreserving_fst
  have hG (a : Fin n) (j : Fin m) : HasAllFiniteMoments
      (fun u : Orth q × Matrix (Fin n) (Fin m) ℝ => u.2 a j) μ :=
    (allFiniteMoments_gaussianMatrix_entry a j).comp_measurePreserving measurePreserving_snd
  have hLG (i : Fin (q + m)) (a : Fin n) : HasAllFiniteMoments
      (fun u : Orth q × Matrix (Fin n) (Fin m) ℝ => (L * u.2ᵀ) i a) μ :=
    HasAllFiniteMoments.matrix_left_mul_entry _ L (fun j a => hG a j) i a
  intro i j
  have h := HasAllFiniteMoments.finset_sum (μ := μ) Finset.univ
    (fun (a : Fin n) (u : Orth q × Matrix (Fin n) (Fin m) ℝ) =>
      (singularMeanMatrix n K u.1 lam i a + (L * u.2ᵀ) i a) *
        (singularMeanMatrix n K u.1 lam j a + (L * u.2ᵀ) j a))
    (fun a _ => ((hmean i a).add (hLG i a)).mul ((hmean j a).add (hLG j a)))
  convert h using 1
  funext u
  rcases u with ⟨O, G⟩
  rw [singularSpectralRegressionModel_eq_shiftedRows]
  simp only [coe_wishartGram, Matrix.sum_apply,
    Matrix.vecMulVec_apply, PiLp.toLp_apply, L]

end Wishart
end
end CanonicalSource121

section CanonicalSource122
/- Source: Wishart/PaddedSpectralDeterminants.lean -/



/-!
# Shifted determinant tests on a positive spectrum with zero eigenvalues

The zero eigenvalues are retained by an actual padded symmetric matrix. The
extension outside the positive chamber clamps the positive eigenvalues to zero;
it is measurable, nonnegative, and monotone and agrees with the literal matrix
factor everywhere on the source law. No positive determinant is asserted for
an unshifted rank-deficient matrix.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification Wishart.Spectral
open scoped Classical BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem paddedSym_diagonal_posSemidef {r p : ℕ} (h : r ≤ p)
    (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    (paddedSym h (diagonalSym lam) : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  simpa only [coe_paddedSym, diagonalSym, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosSemidef.diagonal hlam).conjTranspose_mul_mul_same (initialRows h)

theorem paddedSym_diagonal_difference_posSemidef {r p : ℕ} (h : r ≤ p)
    (lam lam' : Fin r → ℝ) (hle : lam ≤ lam') :
    ((paddedSym h (diagonalSym lam') : Matrix (Fin p) (Fin p) ℝ) -
      paddedSym h (diagonalSym lam)).PosSemidef := by
  have hd : Matrix.diagonal (fun i => lam' i - lam i) =
      Matrix.diagonal lam' - Matrix.diagonal lam := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  have hp := paddedSym_diagonal_posSemidef h (fun i => lam' i - lam i)
    (fun i => sub_nonneg.mpr (hle i))
  simpa only [coe_paddedSym, diagonalSym, hd, Matrix.mul_sub, Matrix.sub_mul] using hp

theorem shiftedMatrixDetPower_conjugate {p : ℕ} (O : Orth p)
    (c η : ℝ) (X : SymmetricMatrix p) :
    shiftedMatrixDetPower c η (conjugate O X) = shiftedMatrixDetPower c η X := by
  let S : SymmetricMatrix p := X + c • diagonalSym (fun _ => (1 : ℝ))
  have hconj : (conjugate O X : Matrix (Fin p) (Fin p) ℝ) + c • 1 =
      (conjugate O S : Matrix (Fin p) (Fin p) ℝ) := by
    simp only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
      S, Submodule.coe_add, Submodule.coe_smul, diagonalSym, Matrix.diagonal_one,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, orth_mul_transpose]
  unfold shiftedMatrixDetPower
  rw [hconj, det_conjugate]
  simp only [S, Submodule.coe_add, Submodule.coe_smul, diagonalSym, Matrix.diagonal_one]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem finiteShiftedDetTest_conjugate {p : ℕ} (O : Orth p)
    (c : ℝ) (a b : ι → ℝ) (X : SymmetricMatrix p) :
    finiteShiftedDetTest c a b (conjugate O X) = finiteShiftedDetTest c a b X := by
  unfold finiteShiftedDetTest
  congr 1
  funext j
  rw [shiftedMatrixDetPower_conjugate]

theorem finiteShiftedDetTest_nonneg_on_psd {p : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (X : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ finiteShiftedDetTest c a b X := by
  apply finiteMaximum_nonneg
  intro j
  exact mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg ((hX.add (Matrix.PosSemidef.one.smul hc)).det_nonneg) _)

theorem finiteShiftedDetTest_loewner_mono {p : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (X Y : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    finiteShiftedDetTest c a b X ≤ finiteShiftedDetTest c a b Y := by
  have hdet := compressedDeterminant_mono (Matrix.PosSemidef.one.smul hc)
    (1 : Matrix (Fin p) (Fin p) ℝ) X Y hX hXY
  simp only [compressedDeterminant, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one, add_comm] at hdet
  apply finiteMaximum_mono
    (x := fun j => Real.exp (b j) * shiftedMatrixDetPower c (a j) X)
    (y := fun j => Real.exp (b j) * shiftedMatrixDetPower c (a j) Y)
  intro j
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact Real.rpow_le_rpow (hX.add (Matrix.PosSemidef.one.smul hc)).det_nonneg hdet (ha j)

def paddedNonnegativeSpectrum (n p : ℕ) (lam : Fin (min n p) → ℝ) : SymmetricMatrix p :=
  paddedSym (min_le_right n p) (diagonalSym (fun i => max (lam i) 0))

@[fun_prop] theorem continuous_paddedNonnegativeSpectrum (n p : ℕ) :
    Continuous (paddedNonnegativeSpectrum n p) :=
  (continuous_paddedSym _).comp ((continuous_diagonalSym _).comp (by fun_prop))

theorem paddedNonnegativeSpectrum_posSemidef (n p : ℕ) (lam : Fin (min n p) → ℝ) :
    (paddedNonnegativeSpectrum n p lam : Matrix (Fin p) (Fin p) ℝ).PosSemidef :=
  paddedSym_diagonal_posSemidef _ _ (fun i => le_max_right _ _)

def paddedShiftedFiniteTest (n p : ℕ) (c : ℝ) (a b : ι → ℝ)
    (lam : Fin (min n p) → ℝ) : ℝ :=
  finiteShiftedDetTest c a b (paddedNonnegativeSpectrum n p lam)

@[fun_prop] theorem measurable_paddedShiftedFiniteTest (n p : ℕ) (c : ℝ) (a b : ι → ℝ) :
    Measurable (paddedShiftedFiniteTest n p c a b) :=
  (measurable_finiteShiftedDetTest p c a b).comp
    (continuous_paddedNonnegativeSpectrum n p).measurable

theorem paddedShiftedFiniteTest_nonneg (n p : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (lam : Fin (min n p) → ℝ) :
    0 ≤ paddedShiftedFiniteTest n p c a b lam :=
  finiteShiftedDetTest_nonneg_on_psd hc a b _ (paddedNonnegativeSpectrum_posSemidef n p lam)

theorem paddedShiftedFiniteTest_monotone (n p : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    Monotone (paddedShiftedFiniteTest n p c a b) := by
  intro lam lam' hle
  apply finiteShiftedDetTest_loewner_mono hc a b ha _ _
    (paddedNonnegativeSpectrum_posSemidef n p lam)
  exact paddedSym_diagonal_difference_posSemidef _ _ _
    (fun i => max_le_max (hle i) le_rfl)

theorem finiteShiftedDetTest_positiveGramSpectralMatrix (n p : ℕ) (c : ℝ)
    (a b : ι → ℝ) (lam : Fin (min n p) → ℝ)
    (hlam : lam ∈ positiveChamber (min n p)) (O : Orth p) :
    finiteShiftedDetTest c a b (positiveGramSpectralMatrix n p lam O) =
      paddedShiftedFiniteTest n p c a b lam := by
  rw [positiveGramSpectralMatrix, finiteShiftedDetTest_conjugate]
  have heq : (fun i => max (lam i) 0) = lam := funext fun i => max_eq_left (hlam.2 i).le
  simp only [paddedShiftedFiniteTest, paddedNonnegativeSpectrum, heq]

theorem allFiniteMoments_finiteShiftedDetTest_gram {p : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) (a b : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j) :
    HasAllFiniteMoments (finiteShiftedDetTest (q := p) c a b) (wishartGramMeasure n Sigma) := by
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  apply HasAllFiniteMoments.const_mul
  change HasAllFiniteMoments (fun X : SymmetricMatrix p =>
    ((X : Matrix (Fin p) (Fin p) ℝ) + c • 1).det ^ a j) (wishartGramMeasure n Sigma)
  have h := (allFiniteMoments_gram_affine_compression_det n Sigma
    (c • (1 : Matrix (Fin p) (Fin p) ℝ)) (1 : Matrix (Fin p) (Fin p) ℝ)).rpow (ha j)
  simpa only [shiftedMatrixDetPower, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one, add_comm] using h

end Wishart
end
end CanonicalSource122

section CanonicalSource123
/- Source: Wishart/GramSelectedFiniteTests.lean -/



/-!
# Association on the exact positive spectrum of an integer Gram matrix

The selected finite determinant test is a function of the positive spectrum
with the exact zero eigenvalues padded back in. Its three expectation
identities are proved from the actual singular regression source. The only
internal comparison input is the remaining conditional monotonicity, supplied
by the Gaussian-row comparison in the final applications.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open WishartVerification Wishart.Spectral
open scoped Classical BigOperators Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem singularSpectralRegressionModel_posSemidef {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (z : (Fin (min n q) → ℝ) × (Orth q × Matrix (Fin n) (Fin m) ℝ)) :
    (singularSpectralRegressionModel K C z : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef := by
  rw [singularSpectralRegressionModel, rawGaussianRegressionGram_eq_matrixGram, coe_matrixGram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (rawGaussianRegressionData K C
      (singularSpectralFactor n q z.1 z.2.1, z.2.2))

theorem singularRegressionSpectralAverage_finiteOuter_nonneg {q m : ℕ}
    (n : ℕ) (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (lam : Fin (min n q) → ℝ) :
    0 ≤ singularRegressionSpectralAverage n C K (affineMaximumProduct 0 k B M a b) lam :=
  parameterAverageOn_nonneg _ _ _ (fun lam _ u =>
    affineMaximumProduct_zero_nonneg k B M a b hB
      (singularSpectralRegressionModel_posSemidef K C (lam, u))) lam

theorem allFiniteMoments_selected_finiteShiftedDetTest_gram {q m : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) (c : ℝ)
    (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    HasAllFiniteMoments (fun X : SymmetricMatrix (q + m) =>
      finiteShiftedDetTest c a b (regressionSelectedBlock X)) (wishartGramMeasure n Sigma) := by
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  apply HasAllFiniteMoments.const_mul
  apply HasAllFiniteMoments.rpow _ (ha j)
  apply HasAllFiniteMoments.det
  intro u v
  change HasAllFiniteMoments
    (fun X : SymmetricMatrix (q + m) =>
      (X : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) (Fin.castAdd m u) (Fin.castAdd m v) +
        (c • (1 : Matrix (Fin q) (Fin q) ℝ)) u v) (wishartGramMeasure n Sigma)
  exact (allFiniteMoments_gram_entry n Sigma _ _).add (HasAllFiniteMoments.const _)

theorem gram_identity_leading_finiteOuter_split_of_spectral_monotone
    {q m : ℕ} (n : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hmono : MonotoneOn
      (singularRegressionSpectralAverage n (1 : Matrix (Fin m) (Fin m) ℝ)
        (0 : Matrix (Fin q) (Fin m) ℝ) (affineMaximumProduct 0 k B M a b))
      (positiveChamber (min n q))) :
    (∫ X, finiteShiftedDetTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X)
      ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, finiteShiftedDetTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X) *
        affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  let K : Matrix (Fin q) (Fin m) ℝ := 0
  let C : Matrix (Fin m) (Fin m) ℝ := 1
  have hC : C.PosSemidef := Matrix.PosSemidef.one
  have hScale : regressionScale K C = 1 := regressionScale_zero_one q m
  have hshape : ((min n q : ℕ) : ℝ) - 1 < (max n q : ℕ) := by
    have hle : ((min n q : ℕ) : ℝ) ≤ (max n q : ℕ) := by
      exact_mod_cast (min_le_max : min n q ≤ max n q)
    linarith
  letI := positiveGramEigenLaw_isProbability n q
  have hselected := allFiniteMoments_selected_finiteShiftedDetTest_gram n
    (regressionScale K C) c a₀ b₀ ha₀
  have hremaining := allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
    (fun X : SymmetricMatrix (q + m) => X)
    (allFiniteMoments_gram_entry n (regressionScale K C))
  have hjoint := (hselected.mul hremaining).integrable
  have hspectral := finiteShiftedDetTest_positiveGramSpectralMatrix n q c a₀ b₀
  have hgm := (continuous_affineMaximumProduct 0 k B M a b ha).measurable
  rw [← hScale]
  change (∫ X, finiteShiftedDetTest c a₀ b₀ (regressionSelectedBlock X)
      ∂wishartGramMeasure n (regressionScale K C)) *
      (∫ X, affineMaximumProduct 0 k B M a b X ∂wishartGramMeasure n (regressionScale K C)) ≤
      ∫ X, finiteShiftedDetTest c a₀ b₀ (regressionSelectedBlock X) *
        affineMaximumProduct 0 k B M a b X ∂wishartGramMeasure n (regressionScale K C)
  rw [integral_singularRegression_selected_spectral K hC
      (measurable_finiteShiftedDetTest q c a₀ b₀) hspectral,
    integral_singularRegression_remaining_spectral K hC hgm hremaining.integrable,
    integral_singularRegression_joint_spectral K hC
      (measurable_finiteShiftedDetTest q c a₀ b₀) hspectral hgm hjoint]
  exact integral_laguerre_mul_ge hshape
    (measurable_paddedShiftedFiniteTest n q c a₀ b₀)
    (measurable_singularRegressionSpectralAverage n C K hgm)
    (paddedShiftedFiniteTest_nonneg n q hc a₀ b₀)
    (singularRegressionSpectralAverage_finiteOuter_nonneg n C K k B M a b hB)
    ((paddedShiftedFiniteTest_monotone n q hc a₀ b₀ ha₀).monotoneOn _)
    hmono
    (integrable_singularRegression_selected_source K hC hspectral hselected.integrable)
    (integrable_singularRegressionSpectralAverage K hC hremaining.integrable)
    (integrable_selected_mul_singularRegressionSpectralAverage K hC hspectral hjoint)

end Wishart
end
end CanonicalSource123

section CanonicalSource124
/- Source: Wishart/GramOuterNormalization.lean -/



/-! # Covariance normalization for the actual integer Gaussian Gram law -/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem map_gram_compressionNormalization {p q : ℕ} (n : ℕ)
    {Sigma : Matrix (Fin p) (Fin p) ℝ} {B : Matrix (Fin p) (Fin q) ℝ}
    (N : CompressionNormalization Sigma B) :
    (wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.symmetricCongruenceLinearMap N.ambient) = wishartGramMeasure n Sigma := by
  rw [map_symmetricCongruenceLinearMap_wishartGramMeasure n N.ambient Matrix.PosSemidef.one,
    Matrix.mul_one, N.ambient_gram]

theorem gram_compression_finiteOuter_split_of_whitened_split {q m : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin (q + m)) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hidentity :
      let N := compressionNormalization hSigma Q hQ
      let b₀' := fun j => b₀ j + Real.log (compressionScale Sigma Q).det * a₀ j
      let M' := fun i => N.ambientᵀ * M i
      (∫ X, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) X)
        ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
        (∫ X, affineMaximumProduct 0 k B M' a b X
          ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
        ∫ X, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) X) *
          affineMaximumProduct 0 k B M' a b X
          ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂wishartGramMeasure n Sigma) *
      (∫ X, affineMaximumProduct 0 k B M a b X ∂wishartGramMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n Sigma := by
  let N := compressionNormalization hSigma Q hQ
  let b₀' : ι → ℝ := fun j => b₀ j + Real.log (compressionScale Sigma Q).det * a₀ j
  let M' := fun i => N.ambientᵀ * M i
  have htransform (f : SymmetricMatrix (q + m) → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂wishartGramMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [← map_gram_compressionNormalization n N,
      integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
        hf.aestronglyMeasurable]
  have hs (Y : SymmetricMatrix (q + m))
      (hY : (Y : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef) :
      finiteCompressionDetTest Sigma Q c a₀ b₀ (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
        finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) Y) :=
    compressionNormalization_finiteOuter hSigma Q hQ N hc a₀ b₀ Y hY
  have hselected :
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂wishartGramMeasure n Sigma) =
        ∫ Y, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) Y)
          ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform _ (measurable_finiteCompressionDetTest Sigma Q c a₀ b₀)]
    apply integral_congr_ae
    exact (ae_posSemidef_wishartGramMeasure n 1).mono hs
  have hremaining :
      (∫ X, affineMaximumProduct 0 k B M a b X ∂wishartGramMeasure n Sigma) =
        ∫ Y, affineMaximumProduct 0 k B M' a b Y
          ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform _ (continuous_affineMaximumProduct 0 k B M a b ha).measurable]
    simp only [affineMaximumProduct_congruence, M']
  have hjoint :
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n Sigma) =
        ∫ Y, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) Y) *
          affineMaximumProduct 0 k B M' a b Y
          ∂wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform (fun X => finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X) ((measurable_finiteCompressionDetTest Sigma Q c a₀ b₀).mul
      (continuous_affineMaximumProduct 0 k B M a b ha).measurable)]
    apply integral_congr_ae
    filter_upwards [ae_posSemidef_wishartGramMeasure n
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)] with Y hY
    rw [hs Y hY, affineMaximumProduct_congruence]
  rw [hselected, hremaining, hjoint]
  exact hidentity


end Wishart
end
end CanonicalSource124

section CanonicalSource125
/- Source: Wishart/GramSpectralComparison.lean -/



/-!
# Singular conditional comparisons averaged over the actual Haar frame

The fixed-frame comparison is transferred by the proved Gaussian-row grouping
identity. Both integrations are against the concrete source measures. Thus the
spectral association step uses the true conditional moment, including when the
selected block is singular or the residual Gram degree is zero.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification Wishart.Spectral
open scoped Classical BigOperators Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

theorem monotoneOn_singularRegressionSpectralAverage_of_groupedNoise
    {q m : ℕ} (n : ℕ) (C : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ) (g : SymmetricMatrix (q + m) → ℝ)
    (hg : Measurable g)
    (hgi : ∀ lam, Integrable (fun u => g (singularSpectralRegressionModel K C (lam, u)))
      (singularRegressionFrameNoise n q m))
    (hmono : ∀ O : Orth q, MonotoneOn (fun lam : Fin (min n q) → ℝ =>
      ∫ x, g (shiftedRowsSym (singularRegressionDirection n K O) lam x)
        ∂gaussianResidualMeasure (min n q) (singularNoiseCovariance (q := q) C)
          (wishartGramMeasure (n - min n q) (singularNoiseCovariance (q := q) C)))
      (Set.Ici (0 : Fin (min n q) → ℝ))) :
    MonotoneOn (singularRegressionSpectralAverage n C K g) (positiveChamber (min n q)) := by
  intro lam hlam lam' hlam' hle
  rw [singularRegressionSpectralAverage_eq n C K g hlam,
    singularRegressionSpectralAverage_eq n C K g hlam']
  change (∫ u, g (singularSpectralRegressionModel K C (lam, u))
      ∂(haarProb (Orth q)).prod (gaussianMatrixMeasure n m)) ≤
      ∫ u, g (singularSpectralRegressionModel K C (lam', u))
        ∂(haarProb (Orth q)).prod (gaussianMatrixMeasure n m)
  rw [integral_prod _ (hgi lam), integral_prod _ (hgi lam')]
  apply integral_mono_ae (hgi lam).integral_prod_left (hgi lam').integral_prod_left
  apply Filter.Eventually.of_forall
  intro O
  dsimp only
  rw [integral_singularSpectralRegressionModel_groupedNoise K C lam O hg,
    integral_singularSpectralRegressionModel_groupedNoise K C lam' O hg]
  exact hmono O (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem monotoneOn_singularRegressionSpectralAverage_finiteOuter
    {q m : ℕ} (n : ℕ) (C : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, k i ≤ n - min n q) :
    MonotoneOn (singularRegressionSpectralAverage n C K (affineMaximumProduct 0 k B M a b))
      (positiveChamber (min n q)) := by
  apply monotoneOn_singularRegressionSpectralAverage_of_groupedNoise n C K _
    (continuous_affineMaximumProduct 0 k B M a b ha).measurable
  · intro lam
    exact (allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha _
      (allFiniteMoments_singularRegressionFrameNoise_entry K C lam)).integrable
  · intro O
    exact monotoneOn_gramShiftedRows_finiteOuter (n - min n q)
      (singularNoiseCovariance_posSemidef C) k B M a b hB ha hsize
      (singularRegressionDirection n K O)

theorem monotoneOn_singularRegressionSpectralAverage_singleFiniteOuter
    {q m k : ℕ} (n : ℕ) (C : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MonotoneOn (singularRegressionSpectralAverage n C K
      (affineMaximumProduct 0 (fun _ : Unit => k) (fun _ => E) (fun _ => M)
        (fun _ => a) (fun _ => b))) (positiveChamber (min n q)) := by
  apply monotoneOn_singularRegressionSpectralAverage_of_groupedNoise n C K _
    (continuous_affineMaximumProduct 0 _ _ _ _ _ (fun _ => ha)).measurable
  · intro lam
    exact (allFiniteMoments_affineMaximumProduct_of_entries 0 _ _ _ _ _ (fun _ => ha) _
      (allFiniteMoments_singularRegressionFrameNoise_entry K C lam)).integrable
  · intro O
    exact monotoneOn_gramShiftedRows_single_finiteOuter (n - min n q)
      (singularNoiseCovariance_posSemidef C) hE M a b ha
      (singularRegressionDirection n K O)

theorem gram_compression_finiteOuter_selected_split {p q : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, q + k i ≤ n) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂wishartGramMeasure n Sigma) *
      (∫ X, affineMaximumProduct 0 k B M a b X ∂wishartGramMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n Sigma := by
  have hqp : q ≤ p := (compressionNormalization hSigma Q hQ).q_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  apply gram_compression_finiteOuter_split_of_whitened_split n hSigma Q hQ hc
    a₀ b₀ ha₀ k B M a b hB ha
  apply gram_identity_leading_finiteOuter_split_of_spectral_monotone n hc _ _ ha₀
    k B _ a b hB ha
  apply monotoneOn_singularRegressionSpectralAverage_finiteOuter n 1 0 k B _ a b hB ha
  intro i
  have hi := hsize i
  have hm := min_le_right n q
  have hn := min_le_left n q
  omega

theorem gram_compression_finiteOuter_pair {p q k : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    (a₀ b₀ a b : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j) (ha : ∀ j, 0 ≤ a j)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef) (M : Matrix (Fin p) (Fin k) ℝ) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂wishartGramMeasure n Sigma) *
      (∫ X, finiteMonomialTest a b (compressedDeterminant E M X)
        ∂wishartGramMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X *
        finiteMonomialTest a b (compressedDeterminant E M X) ∂wishartGramMeasure n Sigma := by
  have hqp : q ≤ p := (compressionNormalization hSigma Q hQ).q_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  have h := gram_compression_finiteOuter_split_of_whitened_split n hSigma Q hQ hc
    a₀ b₀ ha₀ (fun _ : Unit => k) (fun _ => E) (fun _ => M) (fun _ => a) (fun _ => b)
    (fun _ => hE) (fun _ => ha) (by
      apply gram_identity_leading_finiteOuter_split_of_spectral_monotone n hc _ _ ha₀
        (fun _ : Unit => k) (fun _ => E) _ (fun _ => a) (fun _ => b)
        (fun _ => hE) (fun _ => ha)
      exact monotoneOn_singularRegressionSpectralAverage_singleFiniteOuter n 1 0 hE
        ((compressionNormalization hSigma Q hQ).ambientᵀ * M) a b ha)
  simpa only [affineMaximumProduct_unit] using h

end Wishart
end
end CanonicalSource125

section CanonicalSource126
/- Source: Wishart/GramFullRankFiniteComparison.lean -/



/-!
# Full-rank factors under every integer Gram law

A full-rank factor is spectral in the entire whitened matrix. Padding the
positive eigenvalues by zeros preserves Loewner order, so every remaining
finite determinant test increases with that spectrum. Actual positive-spectrum
association supplies the split, without a sample-size or overlap restriction.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open WishartVerification Wishart.Spectral
open scoped Classical BigOperators Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

theorem positiveGramSpectralMatrix_posSemidef (n p : ℕ)
    (lam : Fin (min n p) → ℝ) (O : Orth p) (hlam : ∀ i, 0 ≤ lam i) :
    (positiveGramSpectralMatrix n p lam O : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  simpa only [positiveGramSpectralMatrix, conjugate,
    Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (paddedSym_diagonal_posSemidef (min_le_right n p) lam hlam).mul_mul_conjTranspose_same
      (O : Matrix (Fin p) (Fin p) ℝ)

theorem positiveGramSpectralMatrix_difference_posSemidef (n p : ℕ)
    (lam lam' : Fin (min n p) → ℝ) (O : Orth p) (hle : lam ≤ lam') :
    ((positiveGramSpectralMatrix n p lam' O : Matrix (Fin p) (Fin p) ℝ) -
      positiveGramSpectralMatrix n p lam O).PosSemidef := by
  have h := (paddedSym_diagonal_difference_posSemidef (min_le_right n p) lam lam' hle).mul_mul_conjTranspose_same (O : Matrix (Fin p) (Fin p) ℝ)
  simpa only [positiveGramSpectralMatrix, conjugate,
    Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul] using h

theorem singularSpectralRegressionModel_zero_tail {n p : ℕ}
    (lam : Fin (min n p) → ℝ) (O : Orth p) (G : Matrix (Fin n) (Fin 0) ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    singularSpectralRegressionModel (0 : Matrix (Fin p) (Fin 0) ℝ)
        (1 : Matrix (Fin 0) (Fin 0) ℝ) (lam, O, G) = positiveGramSpectralMatrix n p lam O := by
  have h := singularSpectralRegressionModel_selected
    (0 : Matrix (Fin p) (Fin 0) ℝ) (1 : Matrix (Fin 0) (Fin 0) ℝ) lam O G hlam
  have hblock (X : SymmetricMatrix p) : regressionSelectedBlock (m := 0) X = X := by
    apply Subtype.ext
    ext i j
    rfl
  simpa only [Nat.add_zero, hblock] using h

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem monotoneOn_singularRegressionSpectralAverage_finiteOuter_fullRank
    {p : ℕ} (n : ℕ)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j) :
    MonotoneOn (singularRegressionSpectralAverage n (1 : Matrix (Fin 0) (Fin 0) ℝ)
      (0 : Matrix (Fin p) (Fin 0) ℝ) (affineMaximumProduct 0 k B M a b))
      (positiveChamber (min n p)) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact (allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha _
      (allFiniteMoments_singularRegressionFrameNoise_entry (q := p) (m := 0) 0 1 lam)).integrable
  · intro lam hlam lam' hlam' hle
    apply Filter.Eventually.of_forall
    intro u
    rw [singularSpectralRegressionModel_zero_tail lam u.1 u.2 (fun i => (hlam.2 i).le),
      singularSpectralRegressionModel_zero_tail lam' u.1 u.2 (fun i => (hlam'.2 i).le)]
    exact affineMaximumProduct_loewner_mono k B M a b hB ha _ _
      (positiveGramSpectralMatrix_posSemidef n p lam u.1 (fun i => (hlam.2 i).le))
      (positiveGramSpectralMatrix_difference_posSemidef n p lam lam' u.1 hle)

theorem gram_fullRank_finiteOuter_split_identity {p : ℕ} (n : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, finiteShiftedDetTest c a₀ b₀ X
      ∂wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) *
      (∫ X, affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) ≤
      ∫ X, finiteShiftedDetTest c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have hblock (X : SymmetricMatrix p) : principalSymmetricBlock (Fin.castAdd 0) X = X := by
    apply Subtype.ext
    ext i j
    rfl
  simpa only [Nat.add_zero, hblock] using
    gram_identity_leading_finiteOuter_split_of_spectral_monotone (q := p) (m := 0) n hc
      a₀ b₀ ha₀ k B M a b hB ha
      (monotoneOn_singularRegressionSpectralAverage_finiteOuter_fullRank n k B M a b hB ha)

theorem gram_fullRank_finiteOuter_split {p : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.rank = p) (hc : 0 ≤ c)
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂wishartGramMeasure n Sigma) *
      (∫ X, affineMaximumProduct 0 k B M a b X ∂wishartGramMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂wishartGramMeasure n Sigma := by
  apply gram_compression_finiteOuter_split_of_whitened_split (m := 0) n hSigma Q hQ hc
    a₀ b₀ ha₀ k B M a b hB ha
  have hblock (X : SymmetricMatrix p) : principalSymmetricBlock (Fin.castAdd 0) X = X := by
    apply Subtype.ext
    ext i j
    rfl
  simpa only [Nat.add_zero, hblock] using gram_fullRank_finiteOuter_split_identity n hc a₀
    (fun j => b₀ j + Real.log (compressionScale Sigma Q).det * a₀ j) ha₀ k B
    (fun i => (compressionNormalization hSigma Q hQ).ambientᵀ * M i) a b hB ha

end Wishart
end
end CanonicalSource126

section CanonicalSource127
/- Source: Wishart/GramGeometricFullRankSplit.lean -/



/-! # The unrestricted full-rank split in Corollary 5.4 -/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

/-- Every full-rank factor in Corollary 5.4 splits for every natural sample size.
The remaining family may overlap arbitrarily, and all expectations may be
infinite. -/
theorem gram_compression_geometric_fullRank_split {p : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.rank = p) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricOuterOnNonnegative f₀) (hf : ∀ i, GeometricOuterOnNonnegative (f i)) :
    (∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X))
      ∂wishartGramMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X) *
        ∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma := by
  apply gram_compression_boundary_split_of_finite n hSigma Q hQ hc k M hM d hd f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  exact gram_fullRank_finiteOuter_split n hSigma Q hQ hc a₀ b₀ ha₀ k
    (fun i => d i • compressionScale Sigma (M i)) M a b
    (fun i => (compressionScale_posDef hSigma (M i) (hM i)).posSemidef.smul (hd i)) ha

end Wishart
end
end CanonicalSource127

section CanonicalSource128
/- Source: Wishart/GramGeometricSplits.lean -/



/-! # Exact geometric splits for singular integer Gram laws -/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

/-- The selected-factor assertion of Corollary 5.4 under its exact uncapped sample-size
threshold, for the full stated class of geometrically log-convex functions.
There is no integrability or polynomial-growth assumption on those functions. -/
theorem gram_compression_geometric_selected_split {p q : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricOuterOnNonnegative f₀) (hf : ∀ i, GeometricOuterOnNonnegative (f i))
    (hsize : ∀ i, q + k i ≤ n) :
    (∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X))
      ∂wishartGramMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X) *
        ∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma := by
  apply gram_compression_boundary_split_of_finite n hSigma Q hQ hc k M hM d hd f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  exact gram_compression_finiteOuter_selected_split n hSigma Q hQ hc a₀ b₀ ha₀ k
    (fun i => d i • compressionScale Sigma (M i)) M a b
    (fun i => (compressionScale_posDef hSigma (M i) (hM i)).posSemidef.smul (hd i))
    ha hsize


theorem gram_compression_geometric_pair {p q k : ℕ} (n : ℕ) {c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (f g : ℝ → ℝ) (hf : GeometricOuterOnNonnegative f) (hg : GeometricOuterOnNonnegative g) :
    (∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X))
      ∂wishartGramMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (g (shiftedCompressionDeterminant Sigma M d X))
        ∂wishartGramMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X) *
        g (shiftedCompressionDeterminant Sigma M d X))
        ∂wishartGramMeasure n Sigma := by
  have h := gram_compression_boundary_split_of_finite n hSigma Q hQ hc
    (fun _ : Unit => k) (fun _ => M) (fun _ => hM) (fun _ => d) (fun _ => hd)
    f (fun _ => g) hf (fun _ => hg) (by
      intro l a₀ b₀ a b ha₀ ha
      have hpair := gram_compression_finiteOuter_pair n hSigma Q hQ hc
        a₀ b₀ (a ()) (b ()) ha₀ (ha ())
        ((compressionScale_posDef hSigma M hM).posSemidef.smul hd) M
      simpa only [affineMaximumProduct, Fintype.prod_unique, regularizedCompression,
        compressionCLM_apply, zero_smul, add_zero, finiteMonomialTest, compressedDeterminant]
        using hpair)
  simpa only [Fintype.prod_unique] using h


end Wishart
end
end CanonicalSource128

section CanonicalSource129
/- Source: Wishart/GramGeometricProducts.lean -/



/-!
# The complete integer Gram product assembly (Corollary 5.4)

Every measure is the actual Gaussian Gram law. The retained ranks discard
almost-sure constants and full-rank factors. The remaining ordered threshold is
uncapped: with at least three factors, it is the largest plus the third largest
rank. The final pair and every full-rank factor split without any degree bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart
namespace GramGeometricCompressionFamily
variable {p : ℕ} {ι : Type*} [DecidableEq ι]
variable (F : GramGeometricCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)

theorem moment_selected_split (n : ℕ)
    (hSigma : Sigma.PosDef)
    (J : Finset ι) (i : ι) (hi : i ∈ J)
    (hsize : ∀ j ∈ J.erase i,
      F.size i + F.size j ≤ n) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have h := gram_compression_geometric_selected_split n hSigma
    (F.matrix i) (F.full_rank i) (F.shift_nonneg i)
    (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
    (fun j => F.shift j) (fun j => F.shift_nonneg j)
    (F.outer i) (fun j => F.outer j) (F.boundary i) (fun j => F.boundary j)
    (fun j => hsize j j.property)
  change (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂wishartGramMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
        ∂wishartGramMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X *
        ∏ j : J.erase i, F.factor Sigma (j : ι) X) ∂wishartGramMeasure n Sigma at h
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  have hprod (X : SymmetricMatrix p) :
      (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
        F.subproduct Sigma (J.erase i) X :=
    Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
  simp_rw [hprod] at h
  simpa only [moment] using h

theorem moment_full_rank_split (n : ℕ)
    (hSigma : Sigma.PosDef)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hfull : F.size i = p) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have hsplit (q : ℕ) (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hqp : q = p) :
      (∫⁻ X, ENNReal.ofReal (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X))
        ∂wishartGramMeasure n Sigma) * F.moment Sigma n (J.erase i) ≤
        ∫⁻ X, ENNReal.ofReal (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X) *
          F.subproduct Sigma (J.erase i) X) ∂wishartGramMeasure n Sigma := by
    subst q
    have h := gram_compression_geometric_fullRank_split n hSigma Q hQ (F.shift_nonneg i)
      (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
      (fun j => F.shift j) (fun j => F.shift_nonneg j)
      (F.outer i) (fun j => F.outer j) (F.boundary i) (fun j => F.boundary j)
    change (∫⁻ X, ENNReal.ofReal
        (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X))
        ∂wishartGramMeasure n Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
          ∂wishartGramMeasure n Sigma) ≤
        ∫⁻ X, ENNReal.ofReal
          (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X) *
            ∏ j : J.erase i, F.factor Sigma (j : ι) X)
          ∂wishartGramMeasure n Sigma at h
    have hprod (X : SymmetricMatrix p) :
        (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
          F.subproduct Sigma (J.erase i) X :=
      Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
    simp_rw [hprod] at h
    simpa only [moment] using h
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  exact hsplit (F.size i) (F.matrix i) (F.full_rank i) hfull

theorem moment_pair_split (n : ℕ)
    (hSigma : Sigma.PosDef)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hsmall : J.card ≤ 2) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have hcard : (J.erase i).card ≤ 1 := by rw [Finset.card_erase_of_mem hi]; omega
  by_cases hrest : J.erase i = ∅
  · have hJ : J = {i} := by
      have h := Finset.insert_erase hi
      rw [hrest, Finset.insert_empty] at h
      exact h.symm
    rw [hrest, hJ, F.moment_empty Sigma n, mul_one]
  · have hcard' : (J.erase i).card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hrest)
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard'
    have h := gram_compression_geometric_pair n hSigma
      (F.matrix i) (F.full_rank i) (F.matrix j) (F.full_rank j)
      (F.shift_nonneg i) (F.shift_nonneg j)
      (F.outer i) (F.outer j) (F.boundary i) (F.boundary j)
    rw [F.moment_singleton, F.moment_split Sigma n J i hi, hj, F.moment_singleton]
    simpa only [factor, subproduct, Finset.prod_singleton] using h

theorem moment_split_outside_activeProper [Fintype ι] (n : ℕ)
    (hSigma : Sigma.PosDef)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hinactive : i ∉ F.activeProper Sigma n) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  by_cases hc : F.AEConstantFactor Sigma n i
  · exact (F.moment_constant_split Sigma n hSigma.posSemidef J i hi hc).le
  have hfull : F.size i = p := by
    have hle := F.size_le i
    by_contra hne
    have hklt : F.size i < p := lt_of_le_of_ne hle hne
    exact hinactive (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hklt, hc⟩)
  exact F.moment_full_rank_split Sigma n hSigma J i hi hfull

/-- A reusable form permits any retained set containing every nonconstant proper
factor. Its outside-set hypothesis concerns only actual almost-sure constancy or
matrix rank; it is not an unproved analytic comparison. -/
theorem product_moments_le_of_rank_test (n : ℕ)
    (hSigma : Sigma.PosDef)
    (A : Finset ι) (houtside : ∀ i, i ∉ A → F.size i = p ∨ F.AEConstantFactor Sigma n i)
    (hsize : gramOrderedRankThreshold F.size A n) (J : Finset ι) :
    (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
  apply extended_product_singletons_le_by_gram_rank (F.moment Sigma n) F.size A n
    (F.moment_empty Sigma n) (fun _ => bot_le) _
    (F.moment_pair_split Sigma n hSigma)
    (fun S i hi _ hs => F.moment_selected_split Sigma n hSigma S i hi hs)
    ((gramOrderedRankThreshold_iff F.size A n).mp hsize) J
  intro S i hi hiA
  rcases houtside i hiA with hfull | hc
  · exact F.moment_full_rank_split Sigma n hSigma S i hi hfull
  · exact (F.moment_constant_split Sigma n hSigma.posSemidef S i hi hc).le

/-- The full product assertion of Corollary 5.4 for the entire geometric outer
class, with exactly the sorted largest-plus-third-largest retained-rank test. -/
theorem product_moments_le [Fintype ι] (n : ℕ)
    (hSigma : Sigma.PosDef)
    (hsize : gramOrderedRankThreshold F.size (F.activeProper Sigma n) n) (J : Finset ι) :
    (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
  apply extended_product_singletons_le_by_gram_rank (F.moment Sigma n) F.size
    (F.activeProper Sigma n) n (F.moment_empty Sigma n) (fun _ => bot_le)
    (F.moment_split_outside_activeProper Sigma n hSigma)
    (F.moment_pair_split Sigma n hSigma)
    (fun S i hi _ hs => F.moment_selected_split Sigma n hSigma S i hi hs)
    ((gramOrderedRankThreshold_iff F.size (F.activeProper Sigma n) n).mp hsize) J

theorem product_integrals_le_integral_product [Fintype ι] (n : ℕ)
    (hSigma : Sigma.PosDef)
    (hsize : gramOrderedRankThreshold F.size (F.activeProper Sigma n) n) :
    (∏ i, ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂wishartGramMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i, F.factor Sigma i X) ∂wishartGramMeasure n Sigma := by
  simpa only [moment_singleton, moment, subproduct, Finset.prod_singleton] using
    F.product_moments_le Sigma n hSigma hsize Finset.univ


end GramGeometricCompressionFamily
end Wishart
end
end CanonicalSource129
