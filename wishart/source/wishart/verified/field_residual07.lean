module

public import wishart.verified.field_residual06
public import Mathlib.Analysis.Matrix.PosDef

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

section CanonicalSource60
/- Source: Wishart/FieldIntegerConditionalMonotonicity.lean -/



/-!
# Conditional monotonicity for the actual integer Schur source

The residual matrix has the genuine `(n-p)`-row Gaussian Gram law. Its
positive-semidefinite support holds even when the residual is singular or
has zero rows. The same Gaussian rotation and unrestricted row comparison
therefore apply throughout the integer parameter range. The actual source
map theorem separately carries `p ≤ n`; conditional monotonicity itself
needs only the displayed concrete product measure.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral
variable {p q : ℕ}

theorem integerSpectralSchur_conditional_integral (n : ℕ)
    (f : Hermitian (p + q) → ℝ≥0∞) (hf : Measurable f)
    (lam : Fin p → ℝ) (hlam : ∀ a, 0 ≤ lam a) :
    (∫⁻ z, f (spectralSchurBuild (lam,z)) ∂integerSchurNoiseLaw n p q) =
      ∫⁻ U, ∫⁻ W, ∫⁻ Z,
        f (trailingBackground ℂ W + spectralSchurGram ℂ U lam Z)
        ∂matrixGaussian ℂ p q
        ∂gramMeasure (n - p) (1 : Matrix (Fin q) (Fin q) ℂ)
        ∂TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)) := by
  have hmeas : Measurable (fun z : SchurNoise p q => f (spectralSchurBuild (lam,z))) :=
    hf.comp (measurable_spectralSchurBuild.comp (measurable_const.prodMk measurable_id))
  rw [integerSchurNoiseLaw, lintegral_prod _ hmeas.aemeasurable]
  apply lintegral_congr
  intro U
  have hUW : Measurable (fun z : Matrix (Fin p) (Fin q) ℂ × Hermitian q =>
      f (schurInput (unitaryConjugate ℂ U (Wishart.FieldCharts.diagonalHermitian ℂ lam)) z.2 z.1)) :=
    hf.comp (measurable_schurInput.comp (measurable_const.prodMk measurable_id))
  simp only [spectralSchurBuild]
  rw [lintegral_prod_symm _ hUW.aemeasurable]
  apply lintegral_congr
  intro W
  have hZ : Measurable (fun Z : Matrix (Fin p) (Fin q) ℂ =>
      f (schurInput (unitaryConjugate ℂ U (Wishart.FieldCharts.diagonalHermitian ℂ lam)) W Z)) :=
    hf.comp (measurable_schurInput.comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hrot := matrixGaussian_map_unitary_left (p := p) (q := q) ℂ
    (by simp [Complex.finrank_real_complex]) Complex.reLm complex_re_star_mul U
  conv_lhs => rw [← hrot, lintegral_map hZ (by fun_prop)]
  apply lintegral_congr
  intro Z
  exact congrArg f (schurInput_unitary_diagonal U lam hlam W Z)

theorem monotone_integerSpectralSchur_conditional_product (n : ℕ) {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin p → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) (spectralSchurBuild (lam,z))))
      ∂integerSchurNoiseLaw n p q) (Ici 0) := by
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℂ (B i))).measurable
  intro x hx y hy hxy
  change (∫⁻ z, f (spectralSchurBuild (x,z)) ∂integerSchurNoiseLaw n p q) ≤
    ∫⁻ z, f (spectralSchurBuild (y,z)) ∂integerSchurNoiseLaw n p q
  rw [integerSpectralSchur_conditional_integral n f hf x hx,
    integerSpectralSchur_conditional_integral n f hf y hy]
  apply lintegral_mono
  intro U
  apply lintegral_mono_ae
  filter_upwards [gramMeasure_ae_posSemidef (n - p) (1 : Matrix (Fin q) (Fin q) ℂ)] with W hW
  exact monotone_spectralSchur_average U W hW k B Q hQ h hc hm L hx hy hxy

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral
variable {p q : ℕ}

theorem integerSpectralSchur_conditional_integral (n : ℕ)
    (f : Hermitian (p + q) → ℝ≥0∞) (hf : Measurable f)
    (lam : Fin p → ℝ) (hlam : ∀ a, 0 ≤ lam a) :
    (∫⁻ z, f (spectralSchurBuild (lam,z)) ∂integerSchurNoiseLaw n p q) =
      ∫⁻ U, ∫⁻ W, ∫⁻ Z,
        f (trailingBackground ℍ[ℝ] W + spectralSchurGram ℍ[ℝ] U lam Z)
        ∂matrixGaussian ℍ[ℝ] p q
        ∂gramMeasure (n - p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])
        ∂TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) := by
  have hmeas : Measurable (fun z : SchurNoise p q => f (spectralSchurBuild (lam,z))) :=
    hf.comp (measurable_spectralSchurBuild.comp (measurable_const.prodMk measurable_id))
  rw [integerSchurNoiseLaw, lintegral_prod _ hmeas.aemeasurable]
  apply lintegral_congr
  intro U
  have hUW : Measurable (fun z : Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q =>
      f (schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) z.2 z.1)) :=
    hf.comp (measurable_schurInput.comp (measurable_const.prodMk measurable_id))
  simp only [spectralSchurBuild]
  rw [lintegral_prod_symm _ hUW.aemeasurable]
  apply lintegral_congr
  intro W
  have hZ : Measurable (fun Z : Matrix (Fin p) (Fin q) ℍ[ℝ] =>
      f (schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) W Z)) :=
    hf.comp (measurable_schurInput.comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hrot := matrixGaussian_map_unitary_left (p := p) (q := q) ℍ[ℝ]
    (by simp [Quaternion.finrank_eq_four]) (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul U
  conv_lhs => rw [← hrot, lintegral_map hZ (by fun_prop)]
  apply lintegral_congr
  intro Z
  exact congrArg f (schurInput_unitary_diagonal U lam hlam W Z)

theorem monotone_integerSpectralSchur_conditional_product (n : ℕ) {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin p → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) (spectralSchurBuild (lam,z))))
      ∂integerSchurNoiseLaw n p q) (Ici 0) := by
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℍ[ℝ] (B i))).measurable
  intro x hx y hy hxy
  change (∫⁻ z, f (spectralSchurBuild (x,z)) ∂integerSchurNoiseLaw n p q) ≤
    ∫⁻ z, f (spectralSchurBuild (y,z)) ∂integerSchurNoiseLaw n p q
  rw [integerSpectralSchur_conditional_integral n f hf x hx,
    integerSpectralSchur_conditional_integral n f hf y hy]
  apply lintegral_mono
  intro U
  apply lintegral_mono_ae
  filter_upwards [gramMeasure_ae_posSemidef (n - p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])] with W hW
  exact monotone_spectralSchur_average U W hW k B Q hQ h hc hm L hx hy hxy

end Wishart.QuaternionMatrix
end
end CanonicalSource60

section CanonicalSource61
/- Source: Wishart/FieldGramLeadingComparison.lean -/



/-!
# Integer Gram comparison in every rank regime

The selected spectrum has its exact zero multiplicity.  Its positive part is
an actual nonsingular dual Gram spectrum with the interchanged dimensions.
The joint representation of the whole matrix, and the conditional row
monotonicity, are proved from the Gaussian law in the imported modules.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral WishartVerification
variable {p q : ℕ}

theorem gram_leading_finite_comparison_of_rows_le {n : ℕ}
    (hnp : n ≤ p) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℂ (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
  have hn : (n : ℝ) - 1 < (p : ℝ) := by
    have hnp' : (n : ℝ) ≤ p := by exact_mod_cast hnp
    linarith
  letI := identityEigenLaw_isProbability hn
  letI := singularSchurNoiseLaw_probability n p q
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  let φ : (Fin n → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal
    (sortedFaceMonomialApprox hc₀ hm₀ L₀
      (fun a => singularPaddedSpectrum hnp lam (Fin.rev a) + c))
  have hf : Measurable f := by
    apply (continuous_complexFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply Measurable.add
    · apply Measurable.subtype_mk
      fun_prop
    · exact measurable_const
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℂ (B i))).measurable
  have hφ : Measurable φ := by
    apply (continuous_sortedFaceMonomialApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply measurable_pi_iff.mpr
    intro a
    exact (((measurable_pi_apply (Fin.rev a)).comp (continuous_singularPaddedSpectrum hnp).measurable).add measurable_const)
  apply selected_split_of_conditional_association
    (gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ))
    (identityEigenLaw n (p : ℝ)) (singularSchurNoiseLaw n p q) (chamber n)
    (ae_identityEigenLaw_mem_chamber hn) (singularSchurBuild hnp)
    (measurable_singularSchurBuild hnp) (singular_schur_gram_law hnp) f g hf hg φ hφ
  · intro lam hlam z
    dsimp only [f, φ, singularSchurBuild]
    have hlead : Wishart.FieldHermitian.leadingBlock ℂ
        (singularSchurGram ℂ hnp z.1 lam z.2) =
          unitaryConjugate ℂ z.1 (Wishart.FieldCharts.diagonalHermitian ℂ
            (singularPaddedSpectrum hnp lam)) := by
      apply Subtype.ext
      simpa only [Wishart.FieldHermitian.leadingBlock, unitaryConjugate,
        singularSchurGram, singularLeadingFactor, Wishart.FieldCharts.diagonalHermitian,
        realDiagonal, horizontalJoin, Algebra.algebraMap_eq_smul_one] using
          (congrArg Subtype.val (leadingBlock_singularSchurGram ℂ hnp z.1 lam
            (fun a => (hlam.2 a).le) z.2))
    rw [hlead]
    have hpad0 := singularPaddedSpectrum_nonneg hnp (fun a => (hlam.2 a).le)
    have hpadm := singularPaddedSpectrum_monotone hnp hlam.1.monotone (fun a => (hlam.2 a).le)
    have hpos := Wishart.FieldSpectral.identityShift_posSemidef (unitaryConjugate ℂ z.1 (Wishart.FieldCharts.diagonalHermitian ℂ (singularPaddedSpectrum hnp lam)))
      (posSemidef_unitary_diagonal z.1 (singularPaddedSpectrum hnp lam) hpad0) hc0
    rw [complexFaceApprox_eq_sorted hc₀ hm₀ L₀ _ hpos,
      Wishart.FieldSpectral.orderedValues_identityShift, orderedValues_unitary_diagonal z.1 _ hpadm]
    rfl
  · exact identityEigenLaw_association hn
  · intro x hx y hy hxy
    apply ENNReal.ofReal_le_ofReal
    apply sortedFaceMonomialApprox_mono hc₀ hm₀ L₀
    · intro a
      exact add_nonneg (singularPaddedSpectrum_nonneg hnp (fun i => (hx.2 i).le) (Fin.rev a)) hc0
    · intro a
      simpa only [add_comm] using
        add_le_add_right (singularPaddedSpectrum_mono_parameter hnp hxy (Fin.rev a)) c
  · intro x hx y hy hxy
    exact monotone_singularSchur_conditional_product hnp k B Q hQ h hc hm L
      (fun a => (hx.2 a).le) (fun a => (hy.2 a).le) hxy

theorem gram_leading_finite_comparison_of_columns_le {n : ℕ}
    (hpn : p ≤ n) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℂ (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
  have hpα : (p : ℝ) - 1 < (n : ℝ) := by
    have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
    linarith
  letI := identityEigenLaw_isProbability hpα
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  let φ : (Fin p → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal
    (sortedFaceMonomialApprox hc₀ hm₀ L₀ (fun a => lam (Fin.rev a) + c))
  have hf : Measurable f := by
    apply (continuous_complexFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply Measurable.add
    · apply Measurable.subtype_mk
      fun_prop
    · exact measurable_const
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℂ (B i))).measurable
  have hφ : Measurable φ := by
    apply (continuous_sortedFaceMonomialApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    fun_prop
  apply selected_split_of_conditional_association
    (gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ))
    (identityEigenLaw p (n : ℝ)) (integerSchurNoiseLaw n p q) (chamber p)
    (ae_identityEigenLaw_mem_chamber hpα) spectralSchurBuild measurable_spectralSchurBuild
    (integerSpectralSchurBuild_law hpn) f g hf hg φ hφ
  · intro lam hlam z
    dsimp only [f, φ]
    rw [leadingBlock_spectralSchurBuild]
    have hpos := Wishart.FieldSpectral.identityShift_posSemidef
      (unitaryConjugate ℂ z.1 (Wishart.FieldCharts.diagonalHermitian ℂ lam))
      (posSemidef_unitary_diagonal z.1 lam (fun a => (hlam.2 a).le)) hc0
    rw [complexFaceApprox_eq_sorted hc₀ hm₀ L₀ _ hpos,
      Wishart.FieldSpectral.orderedValues_identityShift, orderedValues_unitary_diagonal z.1 lam hlam.1.monotone]
    rfl
  · exact identityEigenLaw_association hpα
  · intro x hx y hy hxy
    apply ENNReal.ofReal_le_ofReal
    apply sortedFaceMonomialApprox_mono hc₀ hm₀ L₀
    · intro a
      exact add_nonneg (hx.2 (Fin.rev a)).le hc0
    · intro a
      simpa only [add_comm] using add_le_add_right (hxy (Fin.rev a)) c
  · intro x hx y hy hxy
    exact monotone_integerSpectralSchur_conditional_product n k B Q hQ h hc hm L
      (fun a => (hx.2 a).le) (fun a => (hy.2 a).le) hxy


theorem gram_leading_finite_comparison (n : ℕ) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℂ (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
  rcases le_total p n with hpn | hnp
  · exact gram_leading_finite_comparison_of_columns_le hpn c hc0 h₀ hc₀ hm₀ L₀ k B Q hQ h hc hm L
  · exact gram_leading_finite_comparison_of_rows_le hnp c hc0 h₀ hc₀ hm₀ L₀ k B Q hQ h hc hm L

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral WishartVerification
variable {p q : ℕ}

theorem gram_leading_finite_comparison_of_rows_le {n : ℕ}
    (hnp : n ≤ p) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
  have hn : (n : ℝ) - 1 < (p : ℝ) := by
    have hnp' : (n : ℝ) ≤ p := by exact_mod_cast hnp
    linarith
  letI := identityEigenLaw_isProbability hn
  letI := singularSchurNoiseLaw_probability n p q
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  let φ : (Fin n → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal
    (sortedFaceMonomialApprox hc₀ hm₀ L₀
      (fun a => singularPaddedSpectrum hnp lam (Fin.rev a) + c))
  have hf : Measurable f := by
    apply (continuous_quaternionFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply Measurable.add
    · apply Measurable.subtype_mk
      fun_prop
    · exact measurable_const
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℍ[ℝ] (B i))).measurable
  have hφ : Measurable φ := by
    apply (continuous_sortedFaceMonomialApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply measurable_pi_iff.mpr
    intro a
    exact (((measurable_pi_apply (Fin.rev a)).comp (continuous_singularPaddedSpectrum hnp).measurable).add measurable_const)
  apply selected_split_of_conditional_association
    (gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]))
    (identityEigenLaw n (p : ℝ)) (singularSchurNoiseLaw n p q) (chamber n)
    (ae_identityEigenLaw_mem_chamber hn) (singularSchurBuild hnp)
    (measurable_singularSchurBuild hnp) (singular_schur_gram_law hnp) f g hf hg φ hφ
  · intro lam hlam z
    dsimp only [f, φ, singularSchurBuild]
    have hlead : Wishart.FieldHermitian.leadingBlock ℍ[ℝ]
        (singularSchurGram ℍ[ℝ] hnp z.1 lam z.2) =
          unitaryConjugate ℍ[ℝ] z.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ]
            (singularPaddedSpectrum hnp lam)) := by
      apply Subtype.ext
      simpa only [Wishart.FieldHermitian.leadingBlock, unitaryConjugate,
        singularSchurGram, singularLeadingFactor, Wishart.FieldCharts.diagonalHermitian,
        realDiagonal, horizontalJoin, Algebra.algebraMap_eq_smul_one] using
          (congrArg Subtype.val (leadingBlock_singularSchurGram ℍ[ℝ] hnp z.1 lam
            (fun a => (hlam.2 a).le) z.2))
    rw [hlead]
    have hpad0 := singularPaddedSpectrum_nonneg hnp (fun a => (hlam.2 a).le)
    have hpadm := singularPaddedSpectrum_monotone hnp hlam.1.monotone (fun a => (hlam.2 a).le)
    have hpos := identityShift_posSemidef (unitaryConjugate ℍ[ℝ] z.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] (singularPaddedSpectrum hnp lam)))
      (posSemidef_unitary_diagonal z.1 (singularPaddedSpectrum hnp lam) hpad0) hc0
    rw [quaternionFaceApprox_eq_sorted hc₀ hm₀ L₀ _ hpos,
      orderedValues_identityShift, orderedValues_unitary_diagonal z.1 _ hpadm]
    rfl
  · exact identityEigenLaw_association hn
  · intro x hx y hy hxy
    apply ENNReal.ofReal_le_ofReal
    apply sortedFaceMonomialApprox_mono hc₀ hm₀ L₀
    · intro a
      exact add_nonneg (singularPaddedSpectrum_nonneg hnp (fun i => (hx.2 i).le) (Fin.rev a)) hc0
    · intro a
      exact add_le_add (singularPaddedSpectrum_mono_parameter hnp hxy (Fin.rev a)) le_rfl
  · intro x hx y hy hxy
    exact monotone_singularSchur_conditional_product hnp k B Q hQ h hc hm L
      (fun a => (hx.2 a).le) (fun a => (hy.2 a).le) hxy

theorem gram_leading_finite_comparison_of_columns_le {n : ℕ}
    (hpn : p ≤ n) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
  have hpα : (p : ℝ) - 1 < (n : ℝ) := by
    have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
    linarith
  letI := identityEigenLaw_isProbability hpα
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  let φ : (Fin p → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal
    (sortedFaceMonomialApprox hc₀ hm₀ L₀ (fun a => lam (Fin.rev a) + c))
  have hf : Measurable f := by
    apply (continuous_quaternionFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply Measurable.add
    · apply Measurable.subtype_mk
      fun_prop
    · exact measurable_const
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℍ[ℝ] (B i))).measurable
  have hφ : Measurable φ := by
    apply (continuous_sortedFaceMonomialApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    fun_prop
  apply selected_split_of_conditional_association
    (gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]))
    (identityEigenLaw p (n : ℝ)) (integerSchurNoiseLaw n p q) (chamber p)
    (ae_identityEigenLaw_mem_chamber hpα) spectralSchurBuild measurable_spectralSchurBuild
    (integerSpectralSchurBuild_law hpn) f g hf hg φ hφ
  · intro lam hlam z
    dsimp only [f, φ]
    rw [leadingBlock_spectralSchurBuild]
    have hpos := identityShift_posSemidef
      (unitaryConjugate ℍ[ℝ] z.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam))
      (posSemidef_unitary_diagonal z.1 lam (fun a => (hlam.2 a).le)) hc0
    rw [quaternionFaceApprox_eq_sorted hc₀ hm₀ L₀ _ hpos,
      orderedValues_identityShift, orderedValues_unitary_diagonal z.1 lam hlam.1.monotone]
    rfl
  · exact identityEigenLaw_association hpα
  · intro x hx y hy hxy
    apply ENNReal.ofReal_le_ofReal
    apply sortedFaceMonomialApprox_mono hc₀ hm₀ L₀
    · intro a
      exact add_nonneg (hx.2 (Fin.rev a)).le hc0
    · intro a
      exact add_le_add (hxy (Fin.rev a)) le_rfl
  · intro x hx y hy hxy
    exact monotone_integerSpectralSchur_conditional_product n k B Q hQ h hc hm L
      (fun a => (hx.2 a).le) (fun a => (hy.2 a).le) hxy


theorem gram_leading_finite_comparison (n : ℕ) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure n (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
  rcases le_total p n with hpn | hnp
  · exact gram_leading_finite_comparison_of_columns_le hpn c hc0 h₀ hc₀ hm₀ L₀ k B Q hQ h hc hm L
  · exact gram_leading_finite_comparison_of_rows_le hnp c hc0 h₀ hc₀ hm₀ L₀ k B Q hQ h hc hm L

end Wishart.QuaternionMatrix

end
end CanonicalSource61

section CanonicalSource62
/- Source: Wishart/FieldGramArbitraryComparison.lean -/



/-!
# Integer Gram comparisons for arbitrary orthonormal selected frames

The source measure is the actual integer Gaussian Gram law, at every number
of rows. The proof transports its independently established conditional
comparison; no nonsingular-density substitution is made in a singular case.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral

theorem gram_orthonormal_selected_finite_comparison {p q : ℕ} (N : ℕ) {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin (p + q)) (Fin p) ℂ) (hB₀ : B₀ᴴ * B₀ = 1)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (compress ℂ B₀ X) c))
      ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
      ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (compress ℂ B₀ X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
      ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
  obtain ⟨U, hU⟩ := Wishart.FieldSpectral.exists_unitary_extension (Nat.le_add_right p q) B₀ hB₀
  have hcast : (Fin.castLE (Nat.le_add_right p q) : Fin p → Fin (p + q)) =
      Fin.castAdd q := by funext i; rfl
  rw [hcast] at hU
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (compress ℂ B₀ X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  have hf : Measurable f :=
    (continuous_complexFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      (((continuous_compress ℂ B₀).add continuous_const).measurable)
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      ((continuous_const.add (continuous_compress ℂ (B i))).measurable)
  have hmap := gramMeasure_map_unitary (n := N) U
  have hUm : Measurable (unitaryConjugate ℂ U) := by
    apply Measurable.subtype_mk
    fun_prop
  have hint (t : Hermitian (p + q) → ℝ≥0∞) (ht : Measurable t) :
      (∫⁻ X, t X ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) =
      ∫⁻ X, t (unitaryConjugate ℂ U X)
        ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
    conv_lhs => rw [← hmap, lintegral_map ht hUm]
  change (∫⁻ X, f X ∂_) * (∫⁻ X, g X ∂_) ≤ ∫⁻ X, f X * g X ∂_
  rw [hint f hf, hint g hg, hint (fun X => f X * g X) (hf.mul hg)]
  have hselected (X : Hermitian (p + q)) :
      compress ℂ B₀ (unitaryConjugate ℂ U X) =
        Wishart.FieldHermitian.leadingBlock ℂ X := by
    simpa only [compress, unitaryConjugate, Wishart.FieldHermitian.leadingBlock] using
      (compress_completed_frame ℂ U B₀ hU X)
  have hother (i : ι) (X : Hermitian (p + q)) :
      compress ℂ (B i) (unitaryConjugate ℂ U X) =
        compress ℂ ((star U : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) * B i) X := by
    apply Subtype.ext
    simp only [compress, unitaryConjugate, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [f, g, hselected, hother]
  exact gram_leading_finite_comparison N c hc0 h₀ hc₀ hm₀ L₀
    k (fun i => (star U : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) * B i) Q hQ h hc hm L

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral

theorem gram_orthonormal_selected_finite_comparison {p q : ℕ} (N : ℕ) {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin (p + q)) (Fin p) ℍ[ℝ]) (hB₀ : B₀ᴴ * B₀ = 1)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (compress ℍ[ℝ] B₀ X) c))
      ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (compress ℍ[ℝ] B₀ X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
      ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
  obtain ⟨U, hU⟩ := exists_unitary_extension (p + q) p (Nat.le_add_right p q) B₀ hB₀
  have hcast : (Fin.castLE (Nat.le_add_right p q) : Fin p → Fin (p + q)) =
      Fin.castAdd q := by funext i; rfl
  rw [hcast] at hU
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (compress ℍ[ℝ] B₀ X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  have hf : Measurable f :=
    (continuous_quaternionFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      (((continuous_compress ℍ[ℝ] B₀).add continuous_const).measurable)
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      ((continuous_const.add (continuous_compress ℍ[ℝ] (B i))).measurable)
  have hmap := gramMeasure_map_unitary (n := N) U
  have hUm : Measurable (unitaryConjugate ℍ[ℝ] U) := by
    apply Measurable.subtype_mk
    fun_prop
  have hint (t : Hermitian (p + q) → ℝ≥0∞) (ht : Measurable t) :
      (∫⁻ X, t X ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) =
      ∫⁻ X, t (unitaryConjugate ℍ[ℝ] U X)
        ∂gramMeasure N (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
    conv_lhs => rw [← hmap, lintegral_map ht hUm]
  change (∫⁻ X, f X ∂_) * (∫⁻ X, g X ∂_) ≤ ∫⁻ X, f X * g X ∂_
  rw [hint f hf, hint g hg, hint (fun X => f X * g X) (hf.mul hg)]
  have hselected (X : Hermitian (p + q)) :
      compress ℍ[ℝ] B₀ (unitaryConjugate ℍ[ℝ] U X) =
        Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X := by
    simpa only [compress, unitaryConjugate, Wishart.FieldHermitian.leadingBlock] using
      (compress_completed_frame ℍ[ℝ] U B₀ hU X)
  have hother (i : ι) (X : Hermitian (p + q)) :
      compress ℍ[ℝ] (B i) (unitaryConjugate ℍ[ℝ] U X) =
        compress ℍ[ℝ] (star U.val * B i) X := by
    apply Subtype.ext
    simp only [compress, unitaryConjugate, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [f, g, hselected, hother]
  exact gram_leading_finite_comparison N c hc0 h₀ hc₀ hm₀ L₀
    k (fun i => star U.val * B i) Q hQ h hc hm L

end Wishart.QuaternionMatrix
end
end CanonicalSource62

section CanonicalSource63
/- Source: Wishart/FieldGramComparison.lean -/



/-!
# Integer Gram comparison at arbitrary positive covariance

The source measure is the actual integer Gaussian Gram law, at every number
of rows. The proof transports its independently established conditional
comparison; no nonsingular-density substitution is made in a singular case.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.Spectral

theorem gram_selected_finite_comparison {m k₀ : ℕ} (N : ℕ) (Sigma : Matrix (Fin m) (Fin m) ℂ) (hSigma : Sigma.PosDef)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℂ) (hB₀ : Function.Injective B₀.mulVec)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c)) ∂gramMeasure N Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
      (Q i + normalizedCompression (B i) Sigma X)) ∂gramMeasure N Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + normalizedCompression (B i) Sigma X)) ∂gramMeasure N Sigma := by
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := B₀.mulVecLin) hB₀
  have hk : k₀ ≤ m := by simpa using hdim
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  let f : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c))
  let g : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + normalizedCompression (B i) Sigma X))
  have hcomp {k : ℕ} (D : Matrix (Fin (k₀ + q)) (Fin k) ℂ) :
      Continuous (normalizedCompression D Sigma) := by
    apply Continuous.subtype_mk
    fun_prop
  have hf : Measurable f :=
    (continuous_complexFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      ((hcomp B₀).add continuous_const).measurable
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (hcomp (B i))).measurable
  have hT : Measurable (Wishart.FieldHermitian.congruence ℂ (CFC.sqrt Sigma)) := by
    apply Measurable.subtype_mk
    fun_prop
  have hlaw := gramMeasure_covariance_law N Sigma
  change (∫⁻ X, f X ∂gramMeasure N Sigma) * (∫⁻ X, g X ∂gramMeasure N Sigma) ≤
    ∫⁻ X, f X * g X ∂gramMeasure N Sigma
  rw [hlaw, lintegral_map hf hT, lintegral_map hg hT, lintegral_map (f := fun X => f X * g X) (hf.mul hg) hT]
  have hfinite := gram_orthonormal_selected_finite_comparison N
    (whitenedColumns Sigma B₀) (whitenedColumns_gram hSigma hB₀)
    c hc0 h₀ hc₀ hm₀ L₀ k (fun i => whitenedColumns Sigma (B i)) Q hQ h hc hm L
  simpa only [f, g, normalizedCompression_whiten hSigma, compress] using hfinite

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.Spectral

theorem gram_selected_finite_comparison {m k₀ : ℕ} (N : ℕ) (Sigma : Matrix (Fin m) (Fin m) ℍ[ℝ]) (hSigma : PosDef Sigma)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℍ[ℝ]) (hB₀ : FullColumnRank B₀)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (normalizedCompression B₀ Sigma X) c)) ∂gramMeasure N Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
      (Q i + normalizedCompression (B i) Sigma X)) ∂gramMeasure N Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (normalizedCompression B₀ Sigma X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + normalizedCompression (B i) Sigma X)) ∂gramMeasure N Sigma := by
  have hk : k₀ ≤ m := by simpa using hB₀.card_le
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  let f : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (normalizedCompression B₀ Sigma X) c))
  let g : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + normalizedCompression (B i) Sigma X))
  have hcomp {k : ℕ} (D : Matrix (Fin (k₀ + q)) (Fin k) ℍ[ℝ]) :
      Continuous (normalizedCompression D Sigma) := by
    apply Continuous.subtype_mk
    fun_prop
  have hf : Measurable f :=
    (continuous_quaternionFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      ((hcomp B₀).add continuous_const).measurable
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (hcomp (B i))).measurable
  have hT : Measurable (Wishart.FieldHermitian.congruence ℍ[ℝ] (sqrt Sigma)) := by
    apply Measurable.subtype_mk
    fun_prop
  have hlaw := gramMeasure_covariance_law N Sigma
  change (∫⁻ X, f X ∂gramMeasure N Sigma) * (∫⁻ X, g X ∂gramMeasure N Sigma) ≤
    ∫⁻ X, f X * g X ∂gramMeasure N Sigma
  rw [hlaw, lintegral_map hf hT, lintegral_map hg hT, lintegral_map (f := fun X => f X * g X) (hf.mul hg) hT]
  have hfinite := gram_orthonormal_selected_finite_comparison N
    (whitenedColumns Sigma B₀) (whitenedColumns_gram hSigma hB₀)
    c hc0 h₀ hc₀ hm₀ L₀ k (fun i => whitenedColumns Sigma (B i)) Q hQ h hc hm L
  simpa only [f, g, normalizedCompression_whiten hSigma, compress] using hfinite

end Wishart.QuaternionMatrix
end
end CanonicalSource63

section CanonicalSource64
/- Source: Wishart/FieldGramBoundary.lean -/




/-!
# Integer Gram comparison for full spectral boundary profiles

The source measure is the actual integer Gaussian Gram law, at every number
of rows. The proof transports its independently established conditional
comparison; no nonsingular-density substitution is made in a singular case.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.Spectral

theorem gram_selected_boundary_comparison {m k₀ : ℕ} (N : ℕ) (Sigma : Matrix (Fin m) (Fin m) ℂ) (hSigma : Sigma.PosDef)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℂ) (hB₀ : Function.Injective B₀.mulVec)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀)
    (hm₀ : Monotone h₀) (hs₀ : SymmetricProfile h₀)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i))
    (hs : ∀ i, SymmetricProfile (h i)) :
    (∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c))))
      ∂gramMeasure N Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, spectralBoundaryValue (h i) (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Q i + normalizedCompression (B i) Sigma X))))
      ∂gramMeasure N Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c))) *
      ∏ i, spectralBoundaryValue (h i) (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Q i + normalizedCompression (B i) Sigma X)))) ∂gramMeasure N Sigma := by
  let μ := gramMeasure N Sigma
  let A₀ : Hermitian m → Hermitian k₀ := fun X => Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c
  let A : ∀ i, Hermitian m → Hermitian (k i) := fun i X => Q i + normalizedCompression (B i) Sigma X
  have hAm₀ : Measurable A₀ := ((continuous_normalizedCompression B₀ Sigma).add continuous_const).measurable
  have hAm (i : ι) : Measurable (A i) :=
    (continuous_const.add (continuous_normalizedCompression (B i) Sigma)).measurable
  have hA₀ : ∀ᵐ X ∂μ, (A₀ X : Matrix (Fin k₀) (Fin k₀) ℂ).PosSemidef := by
    filter_upwards [gramMeasure_ae_posSemidef N Sigma] with X hX
    exact Wishart.FieldSpectral.identityShift_posSemidef _ (normalizedCompression_posSemidef B₀ Sigma X hX) hc0
  have hA : ∀ᵐ X ∂μ, ∀ i, (A i X : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef := by
    filter_upwards [gramMeasure_ae_posSemidef N Sigma] with X hX i
    exact (hQ i).add (normalizedCompression_posSemidef (B i) Sigma X hX)
  apply complex_spectral_boundary_selected_split μ k₀ k A₀ A hAm₀ hAm hA₀ hA h₀ h hc₀ hc hm₀ hm hs₀ hs
  intro n
  have hh := gram_selected_finite_comparison N Sigma hSigma B₀ hB₀ c hc0
    h₀ hc₀ hm₀ n k B Q hQ h hc hm (fun _ => n)
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ n (A₀ X)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) n (A i X)) ∂μ := hh
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hA₀] with X hX
      exact (ENNReal.ofReal_mul (complexFaceApprox_nonneg hc₀ hm₀ n (A₀ X) hX)).symm

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.Spectral

theorem gram_selected_boundary_comparison {m k₀ : ℕ} (N : ℕ) (Sigma : Matrix (Fin m) (Fin m) ℍ[ℝ]) (hSigma : PosDef Sigma)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℍ[ℝ]) (hB₀ : FullColumnRank B₀)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀)
    (hm₀ : Monotone h₀) (hs₀ : SymmetricProfile h₀)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i))
    (hs : ∀ i, SymmetricProfile (h i)) :
    (∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (orderedValues (identityShift (normalizedCompression B₀ Sigma X) c)))
      ∂gramMeasure N Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, spectralBoundaryValue (h i) (orderedValues (Q i + normalizedCompression (B i) Sigma X)))
      ∂gramMeasure N Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (orderedValues (identityShift (normalizedCompression B₀ Sigma X) c)) *
      ∏ i, spectralBoundaryValue (h i) (orderedValues (Q i + normalizedCompression (B i) Sigma X))) ∂gramMeasure N Sigma := by
  let μ := gramMeasure N Sigma
  let A₀ : Hermitian m → Hermitian k₀ := fun X => identityShift (normalizedCompression B₀ Sigma X) c
  let A : ∀ i, Hermitian m → Hermitian (k i) := fun i X => Q i + normalizedCompression (B i) Sigma X
  have hAm₀ : Measurable A₀ := ((continuous_normalizedCompression B₀ Sigma).add continuous_const).measurable
  have hAm (i : ι) : Measurable (A i) :=
    (continuous_const.add (continuous_normalizedCompression (B i) Sigma)).measurable
  have hA₀ : ∀ᵐ X ∂μ, PosSemidef (A₀ X).val := by
    filter_upwards [gramMeasure_ae_posSemidef N Sigma] with X hX
    exact identityShift_posSemidef _ (normalizedCompression_posSemidef B₀ Sigma X hX) hc0
  have hA : ∀ᵐ X ∂μ, ∀ i, PosSemidef (A i X).val := by
    filter_upwards [gramMeasure_ae_posSemidef N Sigma] with X hX i
    exact (hQ i).add (normalizedCompression_posSemidef (B i) Sigma X hX)
  apply quaternion_spectral_boundary_selected_split μ k₀ k A₀ A hAm₀ hAm hA₀ hA h₀ h hc₀ hc hm₀ hm hs₀ hs
  intro n
  have hh := gram_selected_finite_comparison N Sigma hSigma B₀ hB₀ c hc0
    h₀ hc₀ hm₀ n k B Q hQ h hc hm (fun _ => n)
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ n (A₀ X)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) n (A i X)) ∂μ := hh
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hA₀] with X hX
      exact (ENNReal.ofReal_mul (quaternionFaceApprox_nonneg hc₀ hm₀ n (A₀ X) hX)).symm

end Wishart.QuaternionMatrix
end
end CanonicalSource64

section CanonicalSource65
/- Source: Wishart/FieldGramProducts.lean -/



/-!
# The full integer Gram selected-product assertions

The source measure is the actual integer Gaussian Gram law, at every number
of rows. The proof transports its independently established conditional
comparison; no nonsingular-density substitution is made in a singular case.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
namespace Wishart

namespace ComplexSpectralFamily
variable {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gram_selected_product_comparison (N : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (F : ComplexSpectralFamily p ι) :
    ExtendedSelectedProductComparison (ComplexMatrix.gramMeasure N Sigma) (F.factor Sigma) := by
  apply extendedSelectedProductComparison_of_splits
  intro J j hj
  have h := ComplexMatrix.gram_selected_boundary_comparison N Sigma hSigma
    (F.matrix j) (F.full_rank j) (F.shift j) (F.shift_nonneg j)
    (F.profile j) (F.convex j) (F.increasing j) (F.symmetric j)
    (fun i : J.erase j => F.size i)
    (fun i : J.erase j => F.matrix i)
    (fun i : J.erase j => F.shift i •
      (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (F.size i)))
    (fun i => (Matrix.PosDef.one.posSemidef.smul (F.shift_nonneg i)))
    (fun i : J.erase j => F.profile i)
    (fun i => F.convex i) (fun i => F.increasing i) (fun i => F.symmetric i)
  have hselected (i : ι) (X : ComplexMatrix.Hermitian p) :
      Spectral.spectralBoundaryValue (F.profile i) (FieldSpectral.orderedValues
        (WishartVerification.hermitian_matrix_coe
          (FieldSpectral.identityShift (ComplexMatrix.normalizedCompression (F.matrix i) Sigma X)
            (F.shift i)))) = F.factor Sigma i X := rfl
  have hother (i : ι) (X : ComplexMatrix.Hermitian p) :
      Spectral.spectralBoundaryValue (F.profile i) (FieldSpectral.orderedValues
        (WishartVerification.hermitian_matrix_coe
          (F.shift i • (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (F.size i)) +
            ComplexMatrix.normalizedCompression (F.matrix i) Sigma X))) = F.factor Sigma i X := by
    exact congrArg (fun Y : ComplexMatrix.Hermitian (F.size i) =>
      Spectral.spectralBoundaryValue (F.profile i)
        (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe Y)))
      (add_comm _ _)
  have hp (X : ComplexMatrix.Hermitian p) :
      (∏ i : J.erase j, F.factor Sigma i X) = ∏ i ∈ J.erase j, F.factor Sigma i X :=
    Finset.prod_coe_sort (J.erase j) (fun i => F.factor Sigma i X)
  have hs :
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma j X) ∂ComplexMatrix.gramMeasure N Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, F.factor Sigma i X)
          ∂ComplexMatrix.gramMeasure N Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma j X * ∏ i ∈ J.erase j, F.factor Sigma i X)
        ∂ComplexMatrix.gramMeasure N Sigma := by
    simp_rw [← hp]
    simpa only [hselected, hother] using h
  convert hs using 1
  apply congrArg (fun t : ComplexMatrix.Hermitian p → ℝ≥0∞ => ∫⁻ X, t X ∂ComplexMatrix.gramMeasure N Sigma)
  funext X
  rw [Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hj]

end ComplexSpectralFamily

namespace QuaternionSpectralFamily
variable {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gram_selected_product_comparison (N : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (F : QuaternionSpectralFamily p ι) :
    ExtendedSelectedProductComparison (QuaternionMatrix.gramMeasure N Sigma) (F.factor Sigma) := by
  apply extendedSelectedProductComparison_of_splits
  intro J j hj
  have h := QuaternionMatrix.gram_selected_boundary_comparison N Sigma hSigma
    (F.matrix j) (F.full_rank j) (F.shift j) (F.shift_nonneg j)
    (F.profile j) (F.convex j) (F.increasing j) (F.symmetric j)
    (fun i : J.erase j => F.size i)
    (fun i : J.erase j => F.matrix i)
    (fun i : J.erase j => F.shift i •
      (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (F.size i)))
    (fun i => (QuaternionMatrix.posDef_one.posSemidef.smul (F.shift_nonneg i)))
    (fun i : J.erase j => F.profile i)
    (fun i => F.convex i) (fun i => F.increasing i) (fun i => F.symmetric i)
  have hp (X : QuaternionMatrix.Hermitian p) :
      (∏ i : J.erase j, F.factor Sigma i X) = ∏ i ∈ J.erase j, F.factor Sigma i X :=
    Finset.prod_coe_sort (J.erase j) (fun i => F.factor Sigma i X)
  have hs :
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma j X) ∂QuaternionMatrix.gramMeasure N Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, F.factor Sigma i X)
          ∂QuaternionMatrix.gramMeasure N Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma j X * ∏ i ∈ J.erase j, F.factor Sigma i X)
        ∂QuaternionMatrix.gramMeasure N Sigma := by
    simp_rw [← hp]
    simpa only [factor, shiftedCompression, QuaternionMatrix.identityShift, add_comm] using h
  convert hs using 1
  apply congrArg (fun t : QuaternionMatrix.Hermitian p → ℝ≥0∞ => ∫⁻ X, t X ∂QuaternionMatrix.gramMeasure N Sigma)
  funext X
  rw [Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hj]

end QuaternionSpectralFamily

end Wishart
end
end CanonicalSource65

section CanonicalSource66
/- Source: Wishart/FieldTraceExponential.lean -/



/-!
# Finite exponential trace moments of the literal field densities

Multiplication by exp(trace/2) in the complex case, or exp(trace) in the
quaternion case, changes covariance I to 2I. The exact density identity reduces
the desired finite integral to the already proved positive finite normalizer.
This holds at every admissible real shape, including noninteger shapes.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder Ring ENNReal

namespace Wishart.ComplexMatrix
variable {p : ℕ}

theorem inv_two_smul_one :
    ((2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℂ))⁻¹ =
      (1 / 2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℂ) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul]
  norm_num

theorem trace_half_smul_one_mul (X : Matrix (Fin p) (Fin p) ℂ) :
    (((1 / 2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℂ)) * X).trace.re =
      (1 / 2 : ℝ) * X.trace.re := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
  change Complex.reLm ((1 / 2 : ℝ) • X.trace) = _
  rw [map_smul, smul_eq_mul]
  rfl

theorem wishartWeight_trace_tilt (α : ℝ) (X : Hermitian p) :
    wishartWeight α (1 : Matrix (Fin p) (Fin p) ℂ) X *
      ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * (X : Matrix (Fin p) (Fin p) ℂ).trace.re)) =
    wishartWeight α ((2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℂ)) X := by
  by_cases hX : (X : Matrix (Fin p) (Fin p) ℂ).PosDef
  · rw [wishartWeight, if_pos hX, wishartWeight, if_pos hX, inv_one,
      Matrix.one_mul, inv_two_smul_one, trace_half_smul_one_mul,
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (realDeterminant_pos hX).le _)
        (Real.exp_pos _).le), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  · simp only [wishartWeight, if_neg hX, zero_mul]

theorem finite_exponential_trace_standard {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    (∫⁻ X, ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) *
      (X : Matrix (Fin p) (Fin p) ℂ).trace.re))
      ∂wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)) < ⊤ := by
  have hfirst := finiteDensity_wishart_standard p hα
  have hsecond := (finiteDensity_wishart_and_covariance_law hα
    (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 2))).1
  have hmeas : Measurable (fun X : Hermitian p => ENNReal.ofReal
      (Real.exp ((1 / 2 : ℝ) * (X : Matrix (Fin p) (Fin p) ℂ).trace.re))) := by fun_prop
  rw [wishartMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_wishartWeight α 1) hmeas]
  simp_rw [Pi.mul_apply, wishartWeight_trace_tilt]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hfirst.positive) hsecond.finite

theorem trace_allFiniteMoments_standard {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    WishartVerification.HasAllFiniteMoments
      (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℂ).trace.re)
      (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)) := by
  letI := wishart_standard_probability p hα
  apply WishartVerification.allFiniteMoments_of_positive_exponential (by fun_prop) _
    (by norm_num : (0 : ℝ) < 1 / 2) (finite_exponential_trace_standard hα)
  filter_upwards [wishart_ae_posDef α (1 : Matrix (Fin p) (Fin p) ℂ)] with X hX
  change (0 : ℝ) ≤ RCLike.re (X : Matrix (Fin p) (Fin p) ℂ).trace
  rw [Wishart.FieldSpectral.trace_eq_sum_orderedValues hX.isHermitian]
  exact Finset.sum_nonneg fun i _ => (Wishart.FieldSpectral.orderedValues_pos hX i).le

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
variable {p : ℕ}

theorem ringInverse_two_smul_one :
    ((2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]))⁻¹ʳ =
      (1 / 2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  let u : (Matrix (Fin p) (Fin p) ℍ[ℝ])ˣ :=
    ⟨(2 : ℝ) • 1, (1 / 2 : ℝ) • 1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul]
      norm_num, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul]
      norm_num⟩
  exact Ring.inverse_unit u

theorem trace_half_smul_one_mul (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    (((1 / 2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])) * X).trace.re =
      (1 / 2 : ℝ) * X.trace.re := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) ((1 / 2 : ℝ) • X.trace) = _
  rw [map_smul, smul_eq_mul]
  rfl

theorem wishartWeight_trace_tilt (α : ℝ) (X : Hermitian p) :
    wishartWeight α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) X *
      ENNReal.ofReal (Real.exp ((X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re)) =
    wishartWeight α ((2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])) X := by
  by_cases hX : PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])
  · rw [wishartWeight, if_pos hX, wishartWeight, if_pos hX, Ring.inverse_one,
      Matrix.one_mul, ringInverse_two_smul_one, trace_half_smul_one_mul,
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (positiveDeterminant_nonneg _) _)
        (Real.exp_pos _).le), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  · simp only [wishartWeight, if_neg hX, zero_mul]

theorem finite_exponential_trace_standard {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    (∫⁻ X, ENNReal.ofReal (Real.exp
      ((X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re))
      ∂wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])) < ⊤ := by
  have hfirst := finiteDensity_wishart_standard p hα
  have hsecond := (finiteDensity_wishart_and_covariance_law hα
    (posDef_one.smul (by norm_num : (0 : ℝ) < 2))).1
  have hmeas : Measurable (fun X : Hermitian p => ENNReal.ofReal
      (Real.exp ((X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re))) :=
    (Quaternion.continuous_re.measurable.comp (by fun_prop)).exp.ennreal_ofReal
  rw [wishartMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_wishartWeight α 1) hmeas]
  simp_rw [Pi.mul_apply, wishartWeight_trace_tilt]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hfirst.positive) hsecond.finite

theorem trace_allFiniteMoments_standard {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    WishartVerification.HasAllFiniteMoments
      (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re)
      (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])) := by
  letI := wishart_standard_probability p hα
  apply WishartVerification.allFiniteMoments_of_positive_exponential
    (f := fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re)
    (Quaternion.continuous_re.measurable.comp (by fun_prop)) _
    (by norm_num : (0 : ℝ) < 1) (by simpa only [one_mul] using finite_exponential_trace_standard hα)
  filter_upwards [wishart_ae_posDef α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])] with X hX
  let D := orderedEigenDecomposition (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) hX.isHermitian
  rw [D.trace_eq_sum]
  exact Finset.sum_nonneg fun i _ => D.values_nonneg hX.posSemidef i

end Wishart.QuaternionMatrix
end
end CanonicalSource66

section CanonicalSource67
/- Source: Wishart/FieldGramTraceMoments.lean -/



/-!
# Every finite trace moment of the actual integer Gaussian Gram laws

The trace is exactly a finite sum of squared row norms. Each row is the
specified real Gaussian pushforward, including singular covariance factors.
The argument applies to every sample size and does not use a density for the
resulting Gram matrix.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open WishartVerification Wishart.FieldDensity

variable (F : Type*) [NormedRing F]
  [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage7_1 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


theorem realTrace_rowsGram {n p : ℕ} (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2) (z : Fin n → Row F p) :
    realTrace F re (rowsGram F z).val = ∑ a, ‖z a‖ ^ 2 := by
  rw [rowsGram, realTrace_matrixGram F re hstar]
  simp only [rectangularNormSquare, rowsMatrix, Matrix.of_apply, PiLp.norm_sq_eq_of_L2]

theorem rowNormSquares_allFiniteMoments {r p n : ℕ} (R : Matrix (Fin r) (Fin p) F) :
    HasAllFiniteMoments (fun z : Fin n → Row F p => ∑ a, ‖z a‖ ^ 2)
      (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F R)) := by
  apply HasAllFiniteMoments.finset_sum
  intro a ha
  have hn : HasAllFiniteMoments (fun z : Fin n → Row F p => ‖z a‖)
      (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F R)) :=
    (norm_allFiniteMoments F R).comp_measurePreserving (measurePreserving_eval _ a)
  simpa only [Real.rpow_two] using hn.rpow (show (0 : ℝ) ≤ 2 by norm_num)

theorem realTrace_gramWithFactor_allFiniteMoments {r p : ℕ} (n : ℕ)
    (R : Matrix (Fin r) (Fin p) F) (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2) :
    HasAllFiniteMoments (fun X : Hermitian F p => realTrace F re X.val)
      (gramWithFactor F n R) := by
  have hT : MeasurePreserving (rowsGram F : (Fin n → Row F p) → Hermitian F p)
      (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F R)) (gramWithFactor F n R) :=
    ⟨(continuous_rowsGram F n p).measurable, rfl⟩
  have hm : Measurable (fun X : Hermitian F p => realTrace F re X.val) := by
    unfold realTrace
    apply Finset.measurable_sum
    intro i hi
    exact re.continuous_of_finiteDimensional.measurable.comp
      ((measurable_pi_apply i).comp ((measurable_pi_apply i).comp measurable_subtype_coe))
  apply HasAllFiniteMoments.of_comp_measurePreserving hT hm
  have h := rowNormSquares_allFiniteMoments (n := n) F R
  apply h.congr_ae
  exact Filter.Eventually.of_forall fun z => (realTrace_rowsGram F re hstar z).symm

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open Wishart.FieldGaussian

theorem trace_gram_allFiniteMoments {p : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    WishartVerification.HasAllFiniteMoments
      (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℂ).trace.re)
      (gramMeasure n Sigma) := by
  simpa only [complex_realTrace_eq, gramMeasure] using
    realTrace_gramWithFactor_allFiniteMoments ℂ n (CFC.sqrt Sigma) Complex.reLm complex_re_star_mul

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian

theorem trace_gram_allFiniteMoments {p : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    WishartVerification.HasAllFiniteMoments
      (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re)
      (gramMeasure n Sigma) := by
  simpa only [quaternion_realTrace_eq, gramMeasure] using
    realTrace_gramWithFactor_allFiniteMoments ℍ[ℝ] n (sqrt Sigma) (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
      quaternion_re_star_mul

end Wishart.QuaternionMatrix
end
end CanonicalSource67

section CanonicalSource68
/- Source: Wishart/FieldCompressionTraceBounds.lean -/



/-!
# Trace and determinant envelopes for arbitrary compressions

The compression matrices need not have full column rank.  The estimates use
the actual complex determinant and the actual positive quaternion determinant,
including singular matrices and zero-dimensional compressions.  The complex
constant is the squared Frobenius norm.  The quaternion constant is twice that
quantity, obtained by the faithful complex representation; sharpness of the
constant is unnecessary for the moment applications.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion ComplexOrder BigOperators

namespace Wishart.FieldSpectral

variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem realTrace_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    0 ≤ RCLike.re A.trace :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

theorem eigenvalue_le_realTrace {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i : n) :
    hA.isHermitian.eigenvalues i ≤ RCLike.re A.trace := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [map_sum, RCLike.ofReal_re]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- Every PSD matrix is bounded in the Loewner order by its real trace times
the identity.  This also holds in dimension zero. -/
theorem realTrace_identity_sub_posSemidef {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) :
    (RCLike.re A.trace • (1 : Matrix n n 𝕜) - A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let d : n → 𝕜 := fun i => ((RCLike.re A.trace - hA.isHermitian.eigenvalues i : ℝ) : 𝕜)
  have hd : (Matrix.diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : 𝕜) ≤ ((RCLike.re A.trace - hA.isHermitian.eigenvalues i : ℝ) : 𝕜)
    exact_mod_cast sub_nonneg.mpr (eigenvalue_le_realTrace hA i)
  have heq : Matrix.diagonal d = RCLike.re A.trace • (1 : Matrix n n 𝕜) -
      Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    funext i
    simp [d, Algebra.smul_def]
  have hspec : A = (U : Matrix n n 𝕜) *
      Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) *
      (U : Matrix n n 𝕜)ᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem
  have hunit : (U : Matrix n n 𝕜) * (U : Matrix n n 𝕜)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  have h := hd.mul_mul_conjTranspose_same (U : Matrix n n 𝕜)
  rw [heq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hunit, ← hspec] at h
  exact h

/-- The squared Frobenius norm, expressed as an actual Gram trace. -/
def compressionTraceConstant (B : Matrix n m 𝕜) : ℝ := RCLike.re (Bᴴ * B).trace

theorem compressionTraceConstant_nonneg (B : Matrix n m 𝕜) :
    0 ≤ compressionTraceConstant B :=
  realTrace_nonneg (Matrix.posSemidef_conjTranspose_mul_self B)

theorem compressionTraceConstant_eq_sum (B : Matrix n m 𝕜) :
    compressionTraceConstant B = ∑ j, ∑ i, ‖B i j‖ ^ 2 := by
  simp only [compressionTraceConstant, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum]
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [RCLike.star_def, ← RCLike.ofReal_pow, RCLike.ofReal_re] using
    congrArg RCLike.re (RCLike.conj_mul (B i j))

theorem realTrace_compression_le {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (B : Matrix n m 𝕜) :
    RCLike.re (Bᴴ * A * B).trace ≤ compressionTraceConstant B * RCLike.re A.trace := by
  have h := realTrace_nonneg
    ((realTrace_identity_sub_posSemidef hA).conjTranspose_mul_mul_same B)
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, map_sub, RCLike.smul_re] at h
  simpa only [compressionTraceConstant, mul_comm] using sub_nonneg.mp h

theorem realTrace_compression_add_le {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (B : Matrix n m 𝕜) (D : Matrix m m 𝕜) :
    RCLike.re (Bᴴ * A * B + D).trace ≤
      compressionTraceConstant B * RCLike.re A.trace + RCLike.re D.trace := by
  simpa only [Matrix.trace_add, map_add, add_comm] using
    add_le_add_right (realTrace_compression_le hA B) (RCLike.re D.trace)

end Wishart.FieldSpectral

namespace Wishart.ComplexMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem realDeterminant_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ realDeterminant A :=
  (RCLike.nonneg_iff.mp hA.det_nonneg).1

theorem realDeterminant_le_trace_pow {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    realDeterminant A ≤ A.trace.re ^ Fintype.card n := by
  rw [realDeterminant_eq_prod_eigenvalues hA.isHermitian]
  calc
    _ ≤ ∏ _i : n, A.trace.re := Finset.prod_le_prod₀
      (fun i _ => hA.eigenvalues_nonneg i)
      (fun i _ => Wishart.FieldSpectral.eigenvalue_le_realTrace hA i)
    _ = _ := by simp

variable {p k : ℕ}

theorem compression_determinant_bounds
    {X : Matrix (Fin p) (Fin p) ℂ} (hX : X.PosSemidef)
    (B : Matrix (Fin p) (Fin k) ℂ)
    {D : Matrix (Fin k) (Fin k) ℂ} (hD : D.PosSemidef) :
    0 ≤ realDeterminant (Bᴴ * X * B + D) ∧
      realDeterminant (Bᴴ * X * B + D) ≤ (Bᴴ * X * B + D).trace.re ^ k := by
  have h := (hX.conjTranspose_mul_mul_same B).add hD
  exact ⟨realDeterminant_nonneg h, by simpa using realDeterminant_le_trace_pow h⟩

theorem compression_determinant_le_trace_envelope
    {X : Matrix (Fin p) (Fin p) ℂ} (hX : X.PosSemidef)
    (B : Matrix (Fin p) (Fin k) ℂ)
    {D : Matrix (Fin k) (Fin k) ℂ} (hD : D.PosSemidef) :
    realDeterminant (Bᴴ * X * B + D) ≤
      (FieldSpectral.compressionTraceConstant B * X.trace.re + D.trace.re) ^ k := by
  refine (compression_determinant_bounds hX B hD).2.trans ?_
  exact pow_le_pow_left₀
    (FieldSpectral.realTrace_nonneg ((hX.conjTranspose_mul_mul_same B).add hD))
    (FieldSpectral.realTrace_compression_add_le hX B D) k

theorem shifted_compression_determinant_bounds
    {X : Matrix (Fin p) (Fin p) ℂ} (hX : X.PosSemidef)
    (B : Matrix (Fin p) (Fin k) ℂ)
    {C : Matrix (Fin k) (Fin k) ℂ} (hC : C.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ realDeterminant (Bᴴ * X * B + c • C) ∧
      realDeterminant (Bᴴ * X * B + c • C) ≤ (Bᴴ * X * B + c • C).trace.re ^ k :=
  compression_determinant_bounds hX B (hC.smul hc)

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem realTrace_nonneg {A : Matrix n n ℍ[ℝ]} (hA : PosSemidef A) :
    0 ≤ A.trace.re := by
  have h := FieldSpectral.realTrace_nonneg hA
  rw [trace_complexRepresentation] at h
  change 0 ≤ 2 * A.trace.re at h
  linarith

/-- A finite compression constant obtained from the faithful complex
representation.  It equals twice the real trace of the quaternion Gram matrix. -/
def compressionTraceConstant (B : Matrix n m ℍ[ℝ]) : ℝ :=
  FieldSpectral.compressionTraceConstant (complexRepresentation B)

theorem compressionTraceConstant_nonneg (B : Matrix n m ℍ[ℝ]) :
    0 ≤ compressionTraceConstant B :=
  FieldSpectral.compressionTraceConstant_nonneg _

theorem compressionTraceConstant_eq_gram (B : Matrix n m ℍ[ℝ]) :
    compressionTraceConstant B = 2 * (Bᴴ * B).trace.re := by
  unfold compressionTraceConstant FieldSpectral.compressionTraceConstant
  rw [← complexRepresentation_conjTranspose, ← complexRepresentation_mul,
    trace_complexRepresentation]
  rfl

theorem realTrace_compression_le {A : Matrix n n ℍ[ℝ]} (hA : PosSemidef A)
    (B : Matrix n m ℍ[ℝ]) :
    (Bᴴ * A * B).trace.re ≤ compressionTraceConstant B * A.trace.re := by
  have h := FieldSpectral.realTrace_compression_le hA (complexRepresentation B)
  rw [← complexRepresentation_congruence, trace_complexRepresentation,
    trace_complexRepresentation] at h
  change 2 * (Bᴴ * A * B).trace.re ≤ compressionTraceConstant B * (2 * A.trace.re) at h
  linarith

theorem realTrace_compression_add_le {A : Matrix n n ℍ[ℝ]} (hA : PosSemidef A)
    (B : Matrix n m ℍ[ℝ]) (D : Matrix m m ℍ[ℝ]) :
    (Bᴴ * A * B + D).trace.re ≤
      compressionTraceConstant B * A.trace.re + D.trace.re := by
  have h := add_le_add_right (realTrace_compression_le hA B) D.trace.re
  simpa only [Matrix.trace_add, Quaternion.re_add, add_comm] using h

variable {p k : ℕ}

theorem positiveDeterminant_le_trace_pow {A : Matrix (Fin k) (Fin k) ℍ[ℝ]}
    (hA : PosSemidef A) : positiveDeterminant A ≤ A.trace.re ^ k := by
  let D := orderedEigenDecomposition A hA.isHermitian
  rw [D.positiveDeterminant_eq_prod hA]
  have hvalue (i : Fin k) : D.values i ≤ A.trace.re := by
    rw [D.trace_eq_sum]
    exact Finset.single_le_sum (fun j _ => D.values_nonneg hA j) (Finset.mem_univ i)
  calc
    _ ≤ ∏ _i : Fin k, A.trace.re := Finset.prod_le_prod₀
      (fun i _ => D.values_nonneg hA i) (fun i _ => hvalue i)
    _ = _ := by simp

theorem compression_determinant_bounds
    {X : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hX : PosSemidef X)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    {D : Matrix (Fin k) (Fin k) ℍ[ℝ]} (hD : PosSemidef D) :
    0 ≤ positiveDeterminant (Bᴴ * X * B + D) ∧
      positiveDeterminant (Bᴴ * X * B + D) ≤ (Bᴴ * X * B + D).trace.re ^ k := by
  exact ⟨positiveDeterminant_nonneg _,
    positiveDeterminant_le_trace_pow ((hX.congruence B).add hD)⟩

theorem compression_determinant_le_trace_envelope
    {X : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hX : PosSemidef X)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    {D : Matrix (Fin k) (Fin k) ℍ[ℝ]} (hD : PosSemidef D) :
    positiveDeterminant (Bᴴ * X * B + D) ≤
      (compressionTraceConstant B * X.trace.re + D.trace.re) ^ k := by
  refine (compression_determinant_bounds hX B hD).2.trans ?_
  exact pow_le_pow_left₀ (realTrace_nonneg ((hX.congruence B).add hD))
    (realTrace_compression_add_le hX B D) k

theorem shifted_compression_determinant_bounds
    {X : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hX : PosSemidef X)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    {C : Matrix (Fin k) (Fin k) ℍ[ℝ]} (hC : PosSemidef C)
    {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ positiveDeterminant (Bᴴ * X * B + c • C) ∧
      positiveDeterminant (Bᴴ * X * B + c • C) ≤ (Bᴴ * X * B + c • C).trace.re ^ k :=
  compression_determinant_bounds hX B (hC.smul hc)

end Wishart.QuaternionMatrix
end
end CanonicalSource68

section CanonicalSource69
/- Source: Wishart/FieldFinitePowers.lean -/



/-!
# Finite nonnegative determinant powers for both actual field laws

The density branch obtains every trace moment from the proved exponential
trace tilt and transports it by actual covariance congruence. The integer
branch uses the exact Gaussian row sum. Determinant powers are bounded by
trace polynomials; Holder closure handles any finite family and arbitrary
overlap without additional integrability hypotheses.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.ComplexMatrix
open WishartVerification

theorem trace_allFiniteMoments {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {Sigma : Matrix (Fin p) (Fin p) ℂ} (hSigma : Sigma.PosDef) :
    HasAllFiniteMoments (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℂ).trace.re)
      (wishartMeasure α Sigma) := by
  letI := wishart_standard_probability p hα
  let T := Wishart.FieldHermitian.congruence ℂ (CFC.sqrt Sigma)
  have hT : Measurable T := by
    apply Measurable.subtype_mk
    fun_prop
  have hpres : MeasurePreserving T
      (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)) (wishartMeasure α Sigma) :=
    ⟨hT, (finiteDensity_wishart_and_covariance_law hα hSigma).2.symm⟩
  have htr : Measurable (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℂ).trace.re) := by
    fun_prop
  apply HasAllFiniteMoments.of_comp_measurePreserving hpres htr
  apply allFiniteMoments_of_nonnegative_bound (htr.comp hT)
  · filter_upwards [wishart_ae_posDef α (1 : Matrix (Fin p) (Fin p) ℂ)] with X hX
    exact Wishart.FieldSpectral.realTrace_nonneg (hX.posSemidef.conjTranspose_mul_mul_same (CFC.sqrt Sigma))
  · filter_upwards [wishart_ae_posDef α (1 : Matrix (Fin p) (Fin p) ℂ)] with X hX
    exact Wishart.FieldSpectral.realTrace_compression_le hX.posSemidef (CFC.sqrt Sigma)
  · exact (trace_allFiniteMoments_standard hα).const_mul
      (Wishart.FieldSpectral.compressionTraceConstant (CFC.sqrt Sigma))

theorem finite_compression_determinant_powers_of_trace {p : ℕ}
    (μ : Measure (Hermitian p)) [IsFiniteMeasure μ]
    (hPSD : ∀ᵐ (X : Hermitian p) ∂μ, (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef)
    (htrace : HasAllFiniteMoments
      (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℂ).trace.re) μ)
    {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (D : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) (hD : ∀ i, (D i).PosSemidef)
    (ν : ι → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    (∫⁻ X, ENNReal.ofReal (∏ i,
      realDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B i + D i) ^ ν i) ∂μ) < ⊤ := by
  let f (i : ι) (X : Hermitian p) :=
    realDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B i + D i)
  have hfm (i : ι) : Measurable (f i) := continuous_realDeterminant.measurable.comp (by fun_prop)
  have hf0 (i : ι) : ∀ᵐ X ∂μ, 0 ≤ f i X := by
    filter_upwards [hPSD] with X hX
    exact (compression_determinant_bounds hX (B i) (hD i)).1
  have hf (i : ι) : HasAllFiniteMoments (f i) μ := by
    let C := Wishart.FieldSpectral.compressionTraceConstant (B i)
    have hh := ((htrace.const_mul C).add
      (HasAllFiniteMoments.const (D i).trace.re)).rpow
        (show (0 : ℝ) ≤ (k i : ℝ) by positivity)
    have henv : HasAllFiniteMoments (fun X : Hermitian p =>
        (C * (X : Matrix (Fin p) (Fin p) ℂ).trace.re + (D i).trace.re) ^ k i) μ := by
      simpa only [Real.rpow_natCast] using hh
    apply allFiniteMoments_of_nonnegative_bound (hfm i) (hf0 i) _ henv
    filter_upwards [hPSD] with X hX
    exact compression_determinant_le_trace_envelope hX (B i) (hD i)
  have hprod : Integrable (fun X => ∏ i, f i X ^ ν i) μ :=
    (HasAllFiniteMoments.finset_prod Finset.univ
      (fun i X => f i X ^ ν i) (fun i _ => (hf i).rpow (hν i))).integrable
  apply lt_top_iff_ne_top.mpr
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hprod.aestronglyMeasurable _).mpr hprod
  filter_upwards [hPSD] with X hX
  exact Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg ((compression_determinant_bounds hX (B i) (hD i)).1) _

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open WishartVerification

theorem trace_allFiniteMoments {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hSigma : PosDef Sigma) :
    HasAllFiniteMoments (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re)
      (wishartMeasure α Sigma) := by
  letI := wishart_standard_probability p hα
  let T := Wishart.FieldHermitian.congruence ℍ[ℝ] (sqrt Sigma)
  have hT : Measurable T := by
    apply Measurable.subtype_mk
    fun_prop
  have hpres : MeasurePreserving T
      (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])) (wishartMeasure α Sigma) :=
    ⟨hT, (finiteDensity_wishart_and_covariance_law hα hSigma).2.symm⟩
  have htr : Measurable (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re) :=
    Quaternion.continuous_re.measurable.comp (by fun_prop)
  apply HasAllFiniteMoments.of_comp_measurePreserving hpres htr
  apply allFiniteMoments_of_nonnegative_bound (htr.comp hT)
  · filter_upwards [wishart_ae_posDef α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])] with X hX
    exact Wishart.QuaternionMatrix.realTrace_nonneg (hX.posSemidef.congruence (sqrt Sigma))
  · filter_upwards [wishart_ae_posDef α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])] with X hX
    exact Wishart.QuaternionMatrix.realTrace_compression_le hX.posSemidef (sqrt Sigma)
  · exact (trace_allFiniteMoments_standard hα).const_mul
      (Wishart.QuaternionMatrix.compressionTraceConstant (sqrt Sigma))

theorem finite_compression_determinant_powers_of_trace {p : ℕ}
    (μ : Measure (Hermitian p)) [IsFiniteMeasure μ]
    (hPSD : ∀ᵐ (X : Hermitian p) ∂μ, PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (htrace : HasAllFiniteMoments
      (fun X : Hermitian p => (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re) μ)
    {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (D : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) (hD : ∀ i, PosSemidef (D i))
    (ν : ι → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    (∫⁻ X, ENNReal.ofReal (∏ i,
      positiveDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i + D i) ^ ν i) ∂μ) < ⊤ := by
  let f (i : ι) (X : Hermitian p) :=
    positiveDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i + D i)
  have hfm (i : ι) : Measurable (f i) := continuous_positiveDeterminant.measurable.comp (by fun_prop)
  have hf0 (i : ι) : ∀ᵐ X ∂μ, 0 ≤ f i X := by
    filter_upwards [hPSD] with X hX
    exact (compression_determinant_bounds hX (B i) (hD i)).1
  have hf (i : ι) : HasAllFiniteMoments (f i) μ := by
    let C := Wishart.QuaternionMatrix.compressionTraceConstant (B i)
    have hh := ((htrace.const_mul C).add
      (HasAllFiniteMoments.const (D i).trace.re)).rpow
        (show (0 : ℝ) ≤ (k i : ℝ) by positivity)
    have henv : HasAllFiniteMoments (fun X : Hermitian p =>
        (C * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re + (D i).trace.re) ^ k i) μ := by
      simpa only [Real.rpow_natCast] using hh
    apply allFiniteMoments_of_nonnegative_bound (hfm i) (hf0 i) _ henv
    filter_upwards [hPSD] with X hX
    exact compression_determinant_le_trace_envelope hX (B i) (hD i)
  have hprod : Integrable (fun X => ∏ i, f i X ^ ν i) μ :=
    (HasAllFiniteMoments.finset_prod Finset.univ
      (fun i X => f i X ^ ν i) (fun i _ => (hf i).rpow (hν i))).integrable
  apply lt_top_iff_ne_top.mpr
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hprod.aestronglyMeasurable _).mpr hprod
  filter_upwards [hPSD] with X hX
  exact Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg ((compression_determinant_bounds hX (B i) (hD i)).1) _

end Wishart.QuaternionMatrix

namespace Wishart

theorem theorem_7_1_complex_finite_powers : TheoremSevenOneComplexFinitePowers := by
  intro p ι _ _ Sigma hSigma k B hB c ν hc hν μ hlaw
  let D := fun i => c i • ComplexMatrix.compressionCovariance (B i) Sigma
  have hD (i : ι) : (D i).PosSemidef :=
    (hSigma.posSemidef.conjTranspose_mul_mul_same (B i)).smul (hc i)
  rcases hlaw with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · letI := ComplexMatrix.wishart_probability hα hSigma
    apply ComplexMatrix.finite_compression_determinant_powers_of_trace _ _
      (ComplexMatrix.trace_allFiniteMoments hα hSigma) k B D hD ν hν
    exact (ComplexMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
  · exact ComplexMatrix.finite_compression_determinant_powers_of_trace _
      (ComplexMatrix.gramMeasure_ae_posSemidef n Sigma) (ComplexMatrix.trace_gram_allFiniteMoments n Sigma)
      k B D hD ν hν

theorem theorem_7_1_quaternion_finite_powers : TheoremSevenOneQuaternionFinitePowers := by
  intro p ι _ _ Sigma hSigma k B hB c ν hc hν μ hlaw
  let D := fun i => c i • QuaternionMatrix.compressionCovariance (B i) Sigma
  have hD (i : ι) : QuaternionMatrix.PosSemidef (D i) :=
    (hSigma.posSemidef.congruence (B i)).smul (hc i)
  rcases hlaw with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · letI := QuaternionMatrix.wishart_probability hα hSigma
    apply QuaternionMatrix.finite_compression_determinant_powers_of_trace _ _
      (QuaternionMatrix.trace_allFiniteMoments hα hSigma) k B D hD ν hν
    exact (QuaternionMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
  · exact QuaternionMatrix.finite_compression_determinant_powers_of_trace _
      (QuaternionMatrix.gramMeasure_ae_posSemidef n Sigma) (QuaternionMatrix.trace_gram_allFiniteMoments n Sigma)
      k B D hD ν hν

end Wishart
end
end CanonicalSource69
