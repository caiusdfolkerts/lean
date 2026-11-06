module

public import wishart.verified.real_remainder09
public import tau_ceti.probability.distributions.wishart.agreement

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder10/manifest.json. -/

@[expose] public section

section CanonicalSource90
/- Source: Wishart/SpectralSelectedTests.lean -/



/-! # Selected spectral tests and unrestricted full-rank splitting -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Filter Topology Matrix
open scoped Classical BigOperators Matrix.Norms.Operator

namespace Wishart.Spectral

open WishartVerification

def identitySymmetric (p : ℕ) : Sym p :=
  ⟨1, Matrix.isHermitian_one.isSelfAdjoint⟩

def shiftSymmetric {p : ℕ} (c : ℝ) (X : Sym p) : Sym p :=
  X + c • identitySymmetric p

@[simp] theorem coe_shiftSymmetric {p : ℕ} (c : ℝ) (X : Sym p) :
    (shiftSymmetric c X : Matrix (Fin p) (Fin p) ℝ) =
      (X : Matrix (Fin p) (Fin p) ℝ) + c • 1 := rfl

theorem shiftSymmetric_posSemidef {p : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {X : Sym p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (shiftSymmetric c X : Matrix (Fin p) (Fin p) ℝ).PosSemidef :=
  hX.add (Matrix.PosSemidef.one.smul hc)

theorem shiftSymmetric_posDef {p : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {X : Sym p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    (shiftSymmetric c X : Matrix (Fin p) (Fin p) ℝ).PosDef :=
  hX.add_posSemidef (Matrix.PosSemidef.one.smul hc)

theorem conjugate_shiftSymmetric {p : ℕ} (O : Orth p) (c : ℝ) (X : Sym p) :
    conjugate O (shiftSymmetric c X) = shiftSymmetric c (conjugate O X) := by
  apply Subtype.ext
  simp only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
    coe_shiftSymmetric, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, orth_mul_transpose]

theorem descendingSpectrum_conjugate {p : ℕ} (O : Orth p) (X : Sym p) :
    descendingSpectrum (conjugate O X) = descendingSpectrum X := by
  funext i
  simp only [descendingSpectrum, Function.comp_apply, ascendingSpectrum_conjugate]

theorem spectralPlaneMonomial_conjugate {p : ℕ}
    (O : Orth p) (a : Fin p → ℝ) (b : ℝ) (X : Sym p) :
    spectralPlaneMonomial a b (conjugate O X) = spectralPlaneMonomial a b X := by
  simp only [spectralPlaneMonomial, leadingEigenvalueProduct, descendingSpectrum_conjugate]

theorem spectralPlaneMonomial_loewner {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (X Y : Sym p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    spectralPlaneMonomial a b X ≤ spectralPlaneMonomial a b Y := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.prod_le_prod₀
  · intro j hj
    exact Real.rpow_nonneg (leadingEigenvalueProduct_nonneg _ hX) _
  · intro j hj
    apply Real.rpow_le_rpow (leadingEigenvalueProduct_nonneg _ hX) _ (slopeDrop_nonneg ha hmono j)
    exact Finset.prod_le_prod₀ (fun i _ => descendingSpectrum_nonneg hX _)
      (fun i _ => ascendingSpectrum_mono_of_posSemidef X Y hXY _)

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem affineSpectralPlaneTest_nonneg {p : ℕ}
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    {X : Sym p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X :=
  Finset.prod_nonneg fun i _ => finiteMaximum_nonneg fun j =>
    spectralPlaneMonomial_nonneg _ _ (affineCompressionSym_posSemidef (hE i) (M i) hX)

theorem affineSpectralPlaneTest_loewner {p : ℕ}
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (X Y : Sym p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y - X : Sym p) : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X ≤
      affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b Y := by
  apply Finset.prod_le_prod₀
  · intro i hi
    exact finiteMaximum_nonneg fun j =>
      spectralPlaneMonomial_nonneg _ _ (affineCompressionSym_posSemidef (hE i) (M i) hX)
  · intro i hi
    apply finiteMaximum_mono
    intro j
    apply spectralPlaneMonomial_loewner _ _ (ha i j) (hmono i j) _ _
      (affineCompressionSym_posSemidef (hE i) (M i) hX)
    simp only [coe_affineCompressionSym, add_sub_add_left_eq_sub]
    simpa only [Submodule.coe_sub, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_sub, Matrix.sub_mul] using hXY.conjTranspose_mul_mul_same (M i)

def selectedSpectralPlaneTest {q : ℕ} (c : ℝ) (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (X : Sym q) : ℝ := finiteMaximum (fun j => spectralPlaneMonomial (a j) (b j) (shiftSymmetric c X))

def selectedSpectrumPlaneTest {q : ℕ} (c : ℝ) (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (lam : Fin q → ℝ) : ℝ :=
  (positiveChamber q).indicator (fun x => selectedSpectralPlaneTest c a b (diagonalSym x)) lam

theorem continuous_selectedSpectralPlaneTest {q : ℕ} (c : ℝ)
    (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (ha : ∀ j l, 0 ≤ a j l) (hmono : ∀ j, Antitone (a j)) :
    Continuous (selectedSpectralPlaneTest c a b) := by
  apply continuous_finiteMaximum
  intro j
  exact (continuous_spectralPlaneMonomial _ _ (ha j) (hmono j)).comp
    (continuous_id.add continuous_const)

theorem measurable_selectedSpectrumPlaneTest {q : ℕ} (c : ℝ)
    (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (ha : ∀ j l, 0 ≤ a j l) (hmono : ∀ j, Antitone (a j)) :
    Measurable (selectedSpectrumPlaneTest c a b) :=
  ((continuous_selectedSpectralPlaneTest c a b ha hmono).measurable.comp
    (continuous_diagonalSym q).measurable).indicator
      (orderedChamber_measurable _ measurableSet_Ioi)

theorem selectedSpectrumPlaneTest_nonneg {q : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (a : ι → Fin q → ℝ) (b : ι → ℝ) (lam : Fin q → ℝ) :
    0 ≤ selectedSpectrumPlaneTest c a b lam := by
  by_cases hlam : lam ∈ positiveChamber q
  · rw [selectedSpectrumPlaneTest, Set.indicator_of_mem hlam]
    apply finiteMaximum_nonneg
    intro j
    exact spectralPlaneMonomial_nonneg _ _
      (shiftSymmetric_posSemidef hc (Matrix.posSemidef_diagonal_iff.mpr fun i => (hlam.2 i).le))
  · simp only [selectedSpectrumPlaneTest, Set.indicator_of_notMem hlam, le_refl]

theorem selectedSpectralPlaneTest_spectral {q : ℕ} (c : ℝ)
    (a : ι → Fin q → ℝ) (b : ι → ℝ) (lam : Fin q → ℝ)
    (hlam : lam ∈ positiveChamber q) (O : Orth q) :
    selectedSpectralPlaneTest c a b (regressionSpectralMatrix (lam, O)) =
      selectedSpectrumPlaneTest c a b lam := by
  rw [selectedSpectrumPlaneTest, Set.indicator_of_mem hlam]
  unfold selectedSpectralPlaneTest
  simp only [regressionSpectralMatrix, ← conjugate_shiftSymmetric, spectralPlaneMonomial_conjugate]

theorem selectedSpectrumPlaneTest_monotone {q : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (ha : ∀ j l, 0 ≤ a j l) (hmono : ∀ j, Antitone (a j)) :
    MonotoneOn (selectedSpectrumPlaneTest c a b) (positiveChamber q) := by
  intro lam hlam lam' hlam' hle
  simp only [selectedSpectrumPlaneTest, Set.indicator_of_mem hlam,
    Set.indicator_of_mem hlam']
  apply finiteMaximum_mono
  intro j
  apply spectralPlaneMonomial_loewner _ _ (ha j) (hmono j) _ _
    (shiftSymmetric_posSemidef hc (Matrix.posSemidef_diagonal_iff.mpr fun i => (hlam.2 i).le))
  simp only [coe_shiftSymmetric, add_sub_add_right_eq_sub]
  change (Matrix.diagonal lam' - Matrix.diagonal lam).PosSemidef
  rw [Matrix.diagonal_sub]
  exact Matrix.posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr (hle i)

theorem matrixTestAllMoments_selectedSpectralPlaneTest {q : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (ha : ∀ j l, 0 ≤ a j l) (hmono : ∀ j, Antitone (a j)) :
    MatrixTestAllMoments (selectedSpectralPlaneTest c a b) := by
  intro Ω _ μ _ X hXm hX hentries
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  apply allFiniteMoments_spectralPlaneMonomial _ _ (ha j) (hmono j)
  · exact hXm.add measurable_const
  · exact hX.mono fun z hz => shiftSymmetric_posSemidef hc hz
  · intro u v
    exact (hentries u v).add (HasAllFiniteMoments.const ((c • (1 : Matrix (Fin q) (Fin q) ℝ)) u v))

end Wishart.Spectral

namespace Wishart

open WishartVerification Spectral

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem identity_leading_spectralPlane_split
    {q m : ℕ} {n c : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n) (hc : 0 ≤ c)
    (a₀ : ι → Fin q → ℝ) (b₀ : ι → ℝ)
    (ha₀ : ∀ j l, 0 ≤ a₀ j l) (hmono₀ : ∀ j, Antitone (a₀ j))
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef) (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (hsize : ∀ i, min (k i : ℝ) ((1 + m : ℕ) : ℝ) + 1 ≤ n - q + 1) :
    (∫ X, selectedSpectralPlaneTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n 1) *
      (∫ X, affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
        ∂nonsingularWishartMeasure n 1) ≤
      ∫ X, selectedSpectralPlaneTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X) *
        affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
          ∂nonsingularWishartMeasure n 1 := by
  have h := regression_test_split_of_spectral_monotone hn
    (0 : Matrix (Fin q) (Fin m) ℝ) Matrix.PosDef.one
    (continuous_selectedSpectralPlaneTest c a₀ b₀ ha₀ hmono₀).measurable
    (MatrixTestAllMoments.wishart
      (matrixTestAllMoments_selectedSpectralPlaneTest hc a₀ b₀ ha₀ hmono₀) n 1)
    (measurable_selectedSpectrumPlaneTest c a₀ b₀ ha₀ hmono₀)
    (selectedSpectrumPlaneTest_nonneg hc a₀ b₀)
    (selectedSpectrumPlaneTest_monotone hc a₀ b₀ ha₀ hmono₀)
    (selectedSpectralPlaneTest_spectral c a₀ b₀)
    (continuous_affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b ha hmono).measurable
    (matrixTestAllMoments_affineSpectralPlaneTest k E hE M a b ha hmono)
    (fun X hX => affineSpectralPlaneTest_nonneg k E hE M a b hX)
    (monotoneOn_fullRegressionSpectralAverage_affineSpectralPlaneTest hn Matrix.PosDef.one 0
      k E hE M a b ha hmono hsize)
  simpa only [regressionScale_zero_one] using h

theorem identity_fullRank_spectralPlane_split
    {p : ℕ} {n c : ℝ} (hn : (p : ℝ) - 1 < n) (hc : 0 ≤ c)
    (a₀ : ι → Fin p → ℝ) (b₀ : ι → ℝ)
    (ha₀ : ∀ j l, 0 ≤ a₀ j l) (hmono₀ : ∀ j, Antitone (a₀ j))
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) :
    (∫ X, selectedSpectralPlaneTest c a₀ b₀ X ∂nonsingularWishartMeasure n 1) *
      (∫ X, affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
        ∂nonsingularWishartMeasure n 1) ≤
      ∫ X, selectedSpectralPlaneTest c a₀ b₀ X *
        affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
          ∂nonsingularWishartMeasure n 1 := by
  exact wholeMatrix_test_split hn
    (continuous_selectedSpectralPlaneTest c a₀ b₀ ha₀ hmono₀).measurable
    (MatrixTestAllMoments.wishart
      (matrixTestAllMoments_selectedSpectralPlaneTest hc a₀ b₀ ha₀ hmono₀) n 1)
    (measurable_selectedSpectrumPlaneTest c a₀ b₀ ha₀ hmono₀)
    (selectedSpectrumPlaneTest_nonneg hc a₀ b₀)
    (selectedSpectrumPlaneTest_monotone hc a₀ b₀ ha₀ hmono₀)
    (selectedSpectralPlaneTest_spectral c a₀ b₀)
    (continuous_affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b ha hmono).measurable
    (matrixTestAllMoments_affineSpectralPlaneTest k E hE M a b ha hmono)
    (fun X hX => affineSpectralPlaneTest_nonneg k E hE M a b hX)
    (affineSpectralPlaneTest_loewner k E hE M a b ha hmono)

end Wishart
end
end CanonicalSource90

section CanonicalSource91
/- Source: Wishart/SpectralNormalization.lean -/



/-!
# Exact covariance normalization for logarithmic spectral comparisons

The selected normalized compression becomes the literal leading block of an
identity-scale Wishart matrix. All other affine compressions are transported by
the same congruence. The rank condition is the manuscript's condition (10).
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Classical BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart.Spectral

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem affineCompressionSym_congruence {p r k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (hE : E.IsHermitian)
    (M : Matrix (Fin p) (Fin k) ℝ) (A : Matrix (Fin p) (Fin r) ℝ) (X : Sym r) :
    affineCompressionSym E hE M (Matrix.symmetricCongruenceLinearMap A X) =
      affineCompressionSym E hE (Aᵀ * M) X := by
  apply Subtype.ext
  simp only [coe_affineCompressionSym, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem affineSpectralPlaneTest_congruence {p r : ℕ}
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).IsHermitian) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (A : Matrix (Fin p) (Fin r) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ) (X : Sym r) :
    affineSpectralPlaneTest k E hE M a b (Matrix.symmetricCongruenceLinearMap A X) =
      affineSpectralPlaneTest k E hE (fun i => Aᵀ * M i) a b X := by
  simp only [affineSpectralPlaneTest, affineCompressionSym_congruence]

def normalizedSpectralPlaneTest {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (a : ι → Fin q → ℝ) (b : ι → ℝ) (X : Sym p) : ℝ :=
  selectedSpectralPlaneTest c a b (normalizedCompression Sigma B X)

theorem measurable_normalizedSpectralPlaneTest {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (ha : ∀ j l, 0 ≤ a j l) (hmono : ∀ j, Antitone (a j)) :
    Measurable (normalizedSpectralPlaneTest Sigma B c a b) :=
  (continuous_selectedSpectralPlaneTest c a b ha hmono).measurable.comp
    (measurable_normalizedCompression Sigma B)

theorem normalizedSpectralPlaneTest_congruence_sum {q m : ℕ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin (q + m)) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) (c : ℝ)
    (a : ι → Fin q → ℝ) (b : ι → ℝ) (X : Sym (q + m)) :
    normalizedSpectralPlaneTest Sigma B c a b (Matrix.symmetricCongruenceLinearMap N.ambient X) =
      selectedSpectralPlaneTest c a b (principalSymmetricBlock (Fin.castAdd m) X) := by
  unfold normalizedSpectralPlaneTest
  rw [normalizedCompression_congruence_sum hSigma B hB N X]

end Wishart.Spectral

namespace Wishart

open Spectral

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem normalizedSpectralPlane_split_of_identity {q m : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin (q + m)) (Fin q) ℝ) (hB : B.rank = q)
    (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (ha : ∀ j l, 0 ≤ a j l) (hmono : ∀ j, Antitone (a j))
    {F : SymmetricMatrix (q + m) → ℝ} (hFm : Measurable F)
    (hidentity :
      (∫ X, selectedSpectralPlaneTest c a b (principalSymmetricBlock (Fin.castAdd m) X)
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
        (∫ X, F (Matrix.symmetricCongruenceLinearMap (compressionNormalization hSigma B hB).ambient X)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
        ∫ X, selectedSpectralPlaneTest c a b (principalSymmetricBlock (Fin.castAdd m) X) *
          F (Matrix.symmetricCongruenceLinearMap (compressionNormalization hSigma B hB).ambient X)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) :
    (∫ X, normalizedSpectralPlaneTest Sigma B c a b X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, F X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, normalizedSpectralPlaneTest Sigma B c a b X * F X
        ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma B hB
  have hpush := map_compressionNormalization n N
  have htransform (f : SymmetricMatrix (q + m) → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [← hpush, integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hf.aestronglyMeasurable]
  have hprod := htransform _
    ((measurable_normalizedSpectralPlaneTest Sigma B c a b ha hmono).mul hFm)
  simp only [Pi.mul_apply] at hprod
  rw [htransform _ (measurable_normalizedSpectralPlaneTest Sigma B c a b ha hmono),
    htransform _ hFm, hprod]
  simpa only [normalizedSpectralPlaneTest_congruence_sum hSigma B hB N] using hidentity

/-- Exact proper selected-factor comparison for finite spectral supporting
planes. The final logarithmic profile is recovered by monotone convergence. -/
theorem normalizedSpectralPlane_selected_split {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (hc : 0 ≤ c)
    (a₀ : ι → Fin q → ℝ) (b₀ : ι → ℝ)
    (ha₀ : ∀ j l, 0 ≤ a₀ j l) (hmono₀ : ∀ j, Antitone (a₀ j))
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (hsize : ∀ i, min ((q : ℝ) + k i) ((p : ℝ) + 1) ≤ n) :
    (∫ X, normalizedSpectralPlaneTest Sigma B c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, normalizedSpectralPlaneTest Sigma B c a₀ b₀ X *
        affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
          ∂nonsingularWishartMeasure n Sigma := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (compressionNormalization hSigma B hB).q_le
  apply normalizedSpectralPlane_split_of_identity hSigma B hB a₀ b₀ ha₀ hmono₀
    (continuous_affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b ha hmono).measurable
  simp only [affineSpectralPlaneTest_congruence]
  apply identity_leading_spectralPlane_split hn hc a₀ b₀ ha₀ hmono₀ k E hE _ a b ha hmono
  intro i
  have harith : (((q + m : ℕ) : ℝ)) + 1 = (q : ℝ) + (((1 + m : ℕ) : ℝ)) := by
    push_cast
    ring
  have hi := hsize i
  rw [harith, min_add_add_left] at hi
  linarith

/-- Every full-rank selected spectral factor splits throughout the real-shape
nonsingular range; no extra degree bound is used. -/
theorem normalizedSpectralPlane_fullRank_split {p : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.rank = p) (hc : 0 ≤ c)
    (a₀ : ι → Fin p → ℝ) (b₀ : ι → ℝ)
    (ha₀ : ∀ j l, 0 ≤ a₀ j l) (hmono₀ : ∀ j, Antitone (a₀ j))
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) :
    (∫ X, normalizedSpectralPlaneTest Sigma B c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, normalizedSpectralPlaneTest Sigma B c a₀ b₀ X *
        affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b X
          ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma B hB
  have hpush := map_compressionNormalization n N
  have htransform (f : SymmetricMatrix p → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [← hpush, integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hf.aestronglyMeasurable]
  have hprod := htransform _
    ((measurable_normalizedSpectralPlaneTest Sigma B c a₀ b₀ ha₀ hmono₀).mul
      (continuous_affineSpectralPlaneTest k E (fun i => (hE i).isHermitian)
        M a b ha hmono).measurable)
  simp only [Pi.mul_apply] at hprod
  rw [htransform _ (measurable_normalizedSpectralPlaneTest Sigma B c a₀ b₀ ha₀ hmono₀),
    htransform _ (continuous_affineSpectralPlaneTest k E
      (fun i => (hE i).isHermitian) M a b ha hmono).measurable, hprod]
  simpa only [normalizedSpectralPlaneTest, normalizedCompression_congruence_full hSigma B hB N,
    affineSpectralPlaneTest_congruence] using
    identity_fullRank_spectralPlane_split hn hc a₀ b₀ ha₀ hmono₀ k E hE
      (fun i => N.ambientᵀ * M i) a b ha hmono

end Wishart
end
end CanonicalSource91

section CanonicalSource92
/- Source: Wishart/SpectralFunctionLimit.lean -/



/-!
# The full finite convex logarithmic spectral class

The limit is taken in extended nonnegative integrals. The matrix inputs are
positive definite almost everywhere, exactly as they are for full-column-rank
compressions of the nonsingular Wishart law. No assertion about logarithms on
singular boundary faces is used in this passage.
-/

noncomputable section

open MeasureTheory Filter Topology Set Matrix
open scoped Classical BigOperators ENNReal

namespace Wishart.Spectral

open WishartVerification

def FiniteConvexIncreasingSymmetric {k : ℕ} (h : (Fin k → ℝ) → ℝ) : Prop :=
  ConvexOn ℝ Set.univ h ∧ Monotone h ∧ SymmetricProfile h

def logSpectralFactor {k : ℕ} (h : (Fin k → ℝ) → ℝ) (S : Sym k) : ℝ :=
  Real.exp (h (fun i => Real.log (descendingSpectrum S i)))

theorem continuous_convexProfile {k : ℕ} {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ Set.univ h) : Continuous h := by
  simpa only [interior_univ, continuousOn_univ] using hc.continuousOn_interior

theorem measurable_logSpectralFactor {k : ℕ} {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ Set.univ h) : Measurable (logSpectralFactor h) := by
  apply Real.measurable_exp.comp
  apply (continuous_convexProfile hc).measurable.comp
  exact measurable_pi_lambda fun i => Real.measurable_log.comp
    ((measurable_pi_apply i).comp (continuous_descendingSpectrum k).measurable)

theorem logSpectralFactor_eq_ascending {k : ℕ}
    {h : (Fin k → ℝ) → ℝ} (hsym : SymmetricProfile h) (S : Sym k) :
    logSpectralFactor h S = Real.exp (h (fun i => Real.log (ascendingSpectrum S i))) := by
  unfold logSpectralFactor
  congr 1
  exact hsym Fin.revPerm (fun i => Real.log (ascendingSpectrum S i))

theorem antitone_log_descendingSpectrum {k : ℕ} {S : Sym k}
    (hS : (S : Matrix (Fin k) (Fin k) ℝ).PosDef) :
    Antitone (fun i => Real.log (descendingSpectrum S i)) := by
  intro i j hij
  exact Real.log_le_log (descendingSpectrum_pos hS j) (antitone_descendingSpectrum S hij)

theorem spectralPlaneMaximum_nat_eq_exp {k : ℕ}
    (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ) (n : ℕ)
    {S : Sym k} (hS : (S : Matrix (Fin k) (Fin k) ℝ).PosDef) :
    finiteMaximum (fun j : Fin (n + 1) => spectralPlaneMonomial (a j) (b j) S) =
      Real.exp (coordinatePartialMaximum a b n (fun i => Real.log (descendingSpectrum S i))) := by
  apply le_antisymm
  · apply finiteMaximum_le
    intro j
    rw [spectralPlaneMonomial_eq_exp _ _ hS]
    apply Real.exp_le_exp.mpr
    exact Finset.le_sup'
      (fun l => coordinatePlane (a l) (b l) (fun i => Real.log (descendingSpectrum S i)))
      (Finset.mem_range.mpr j.isLt)
  · obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup'
      (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
      (fun j => coordinatePlane (a j) (b j) (fun i => Real.log (descendingSpectrum S i)))
    let jf : Fin (n + 1) := ⟨j, Finset.mem_range.mp hj⟩
    change Real.exp ((Finset.range (n + 1)).sup' _ _) ≤ _
    rw [hmax]
    calc
      _ = spectralPlaneMonomial (a jf) (b jf) S :=
        (spectralPlaneMonomial_eq_exp _ _ hS).symm
      _ ≤ _ := le_finiteMaximum
        (fun l : Fin (n + 1) => spectralPlaneMonomial (a l) (b l) S) jf

variable {κ : Type*} [Fintype κ] (k : κ → ℕ)

def logSpectralProduct (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (S : ∀ i, Sym (k i)) : ℝ := ∏ i, logSpectralFactor (h i) (S i)

def supportingSpectralProduct (a : ∀ i, ℕ → Fin (k i) → ℝ) (b : κ → ℕ → ℝ)
    (n : ℕ) (S : ∀ i, Sym (k i)) : ℝ :=
  spectralPlaneMaximumProduct k (fun i (j : Fin (n + 1)) => a i j)
    (fun i (j : Fin (n + 1)) => b i j) S

theorem supportingSpectralProduct_eq
    (a : ∀ i, ℕ → Fin (k i) → ℝ) (b : κ → ℕ → ℝ) (n : ℕ)
    {S : ∀ i, Sym (k i)} (hS : ∀ i, (S i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef) :
    supportingSpectralProduct k a b n S = ∏ i,
      Real.exp (coordinatePartialMaximum (a i) (b i) n
        (fun j => Real.log (descendingSpectrum (S i) j))) := by
  unfold supportingSpectralProduct spectralPlaneMaximumProduct
  exact Finset.prod_congr rfl fun i hi => spectralPlaneMaximum_nat_eq_exp _ _ n (hS i)

theorem supportingSpectralProduct_mono_index
    (a : ∀ i, ℕ → Fin (k i) → ℝ) (b : κ → ℕ → ℝ)
    {S : ∀ i, Sym (k i)} (hS : ∀ i, (S i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef) :
    Monotone (fun n => supportingSpectralProduct k a b n S) := by
  intro n m hnm
  change supportingSpectralProduct k a b n S ≤ supportingSpectralProduct k a b m S
  rw [supportingSpectralProduct_eq k a b n hS, supportingSpectralProduct_eq k a b m hS]
  exact Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le)
    (fun i _ => Real.exp_le_exp.mpr (coordinatePartialMaximum_monotone_index _ _ _ hnm))

theorem supportingSpectralProduct_tendsto
    (a : ∀ i, ℕ → Fin (k i) → ℝ) (b : κ → ℕ → ℝ)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hle : ∀ i n x, coordinatePlane (a i n) (b i n) x ≤ h i x)
    (hsup : ∀ i x, Antitone x → (⨆ n, coordinatePlane (a i n) (b i n) x) = h i x)
    {S : ∀ i, Sym (k i)} (hS : ∀ i, (S i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef) :
    Tendsto (fun n => supportingSpectralProduct k a b n S) atTop
      (𝓝 (logSpectralProduct k h S)) := by
  simp only [supportingSpectralProduct_eq k a b _ hS, logSpectralProduct, logSpectralFactor]
  apply tendsto_finsetProd
  intro i hi
  exact Real.continuous_exp.continuousAt.tendsto.comp
    (coordinatePartialMaximum_tendsto (hle i)
      (hsup i _ (antitone_log_descendingSpectrum (hS i))))

theorem supportingSpectralProduct_lintegral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ∀ i, ℕ → Fin (k i) → ℝ) (b : κ → ℕ → ℝ)
    (ha : ∀ i n j, 0 ≤ a i n j) (hanti : ∀ i n, Antitone (a i n))
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hle : ∀ i n x, coordinatePlane (a i n) (b i n) x ≤ h i x)
    (hsup : ∀ i x, Antitone x → (⨆ n, coordinatePlane (a i n) (b i n) x) = h i x)
    (Z : Ω → ∀ i, Sym (k i)) (hZm : Measurable Z)
    (hZ : ∀ᵐ z ∂μ, ∀ i, (Z z i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (supportingSpectralProduct k a b n (Z z)) ∂μ)
      atTop (𝓝 (∫⁻ z, ENNReal.ofReal (logSpectralProduct k h (Z z)) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact ((continuous_spectralPlaneMaximumProduct k
      (fun i (j : Fin (n + 1)) => a i j) (fun i (j : Fin (n + 1)) => b i j)
      (fun i j l => ha i j l) (fun i j => hanti i j)).measurable.comp hZm).ennreal_ofReal.aemeasurable
  · filter_upwards [hZ] with z hz
    intro n m hnm
    exact ENNReal.ofReal_le_ofReal (supportingSpectralProduct_mono_index k a b hz hnm)
  · filter_upwards [hZ] with z hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (supportingSpectralProduct_tendsto k a b h hle hsup hz)

/-- This limit theorem preserves the complete finite, convex, symmetric,
coordinatewise increasing profile class and allows infinite expectations.
Applications establish the finite comparisons using the actual conditional
Wishart regression theorem, rather than leaving that premise unproved. -/
theorem log_spectral_comparison_of_finite_comparisons
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    (Z : Ω → ∀ i, Sym (k i)) (Y : Ξ → ∀ i, Sym (k i))
    (hZm : Measurable Z) (hYm : Measurable Y)
    (hZ : ∀ᵐ z ∂μ, ∀ i, (Z z i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef)
    (hY : ∀ᵐ y ∂ν, ∀ i, (Y y i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef)
    (hfinite : ∀ n : ℕ, ∀ a : ∀ i, Fin (n + 1) → Fin (k i) → ℝ,
      ∀ b : κ → Fin (n + 1) → ℝ,
      (∀ i j l, 0 ≤ a i j l) → (∀ i j, Antitone (a i j)) →
      (∫⁻ z, ENNReal.ofReal (spectralPlaneMaximumProduct k a b (Z z)) ∂μ) ≤
        ∫⁻ y, ENNReal.ofReal (spectralPlaneMaximumProduct k a b (Y y)) ∂ν)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i)) :
    (∫⁻ z, ENNReal.ofReal (logSpectralProduct k h (Z z)) ∂μ) ≤
      ∫⁻ y, ENNReal.ofReal (logSpectralProduct k h (Y y)) ∂ν := by
  choose a b ha hanti hle hsup using fun i =>
    exists_sorted_coordinate_minorants (hh i).1 (hh i).2.1 (hh i).2.2
  exact le_of_tendsto_of_tendsto
    (supportingSpectralProduct_lintegral_tendsto k μ a b ha hanti h hle hsup Z hZm hZ)
    (supportingSpectralProduct_lintegral_tendsto k ν a b ha hanti h hle hsup Y hYm hY)
    (Filter.Eventually.of_forall fun n => hfinite n
      (fun i j => a i j) (fun i j => b i j) (fun i j l => ha i j l) (fun i j => hanti i j))

end Wishart.Spectral
end
end CanonicalSource92

section CanonicalSource93
/- Source: Wishart/SpectralExpectationLimits.lean -/



/-!
# Extended expectations of logarithmic spectral factors

The product of the two marginal expectations is represented on independent
copies. Both sides then pass by monotone convergence, including infinite
expectations. All logarithms are evaluated on positive definite matrices almost
everywhere; singular-boundary values play no role.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Classical BigOperators ENNReal

namespace Wishart.Spectral

open WishartVerification

/-- A limit lemma whose finite-test premise is discharged in the subsequent
actual-law theorem. It does not assert a Wishart comparison by assumption. -/
theorem log_spectral_selected_split_of_finite_splits
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) [SFinite μ] (q : ℕ) (k : κ → ℕ)
    (Z₀ : Ω → Sym q) (Z : Ω → ∀ i, Sym (k i))
    (hZ₀m : Measurable Z₀) (hZm : Measurable Z)
    (hZ₀ : ∀ᵐ z ∂μ, (Z₀ z : Matrix (Fin q) (Fin q) ℝ).PosDef)
    (hZ : ∀ᵐ z ∂μ, ∀ i, (Z z i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef)
    (hfinite : ∀ n : ℕ, ∀ a₀ : Fin (n + 1) → Fin q → ℝ,
      ∀ b₀ : Fin (n + 1) → ℝ, ∀ a : ∀ i, Fin (n + 1) → Fin (k i) → ℝ,
      ∀ b : κ → Fin (n + 1) → ℝ,
      (∀ j l, 0 ≤ a₀ j l) → (∀ j, Antitone (a₀ j)) →
      (∀ i j l, 0 ≤ a i j l) → (∀ i j, Antitone (a i j)) →
      (∫⁻ z, ENNReal.ofReal (finiteMaximum (fun j => spectralPlaneMonomial (a₀ j) (b₀ j) (Z₀ z))) ∂μ) *
        (∫⁻ z, ENNReal.ofReal (spectralPlaneMaximumProduct k a b (Z z)) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (finiteMaximum (fun j => spectralPlaneMonomial (a₀ j) (b₀ j) (Z₀ z)) *
          spectralPlaneMaximumProduct k a b (Z z)) ∂μ)
    (h₀ : (Fin q → ℝ) → ℝ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hh₀ : FiniteConvexIncreasingSymmetric h₀)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i)) :
    (∫⁻ z, ENNReal.ofReal (logSpectralFactor h₀ (Z₀ z)) ∂μ) *
      (∫⁻ z, ENNReal.ofReal (logSpectralProduct k h (Z z)) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (logSpectralFactor h₀ (Z₀ z) * logSpectralProduct k h (Z z)) ∂μ := by
  let dim : Option κ → ℕ := fun i => i.elim q k
  let left : Ω × Ω → ∀ i, Sym (dim i) := fun z i =>
    match i with
    | none => Z₀ z.1
    | some j => Z z.2 j
  let right : Ω → ∀ i, Sym (dim i) := fun z i =>
    match i with
    | none => Z₀ z
    | some j => Z z j
  let profiles : ∀ i, (Fin (dim i) → ℝ) → ℝ := fun i =>
    match i with
    | none => h₀
    | some j => h j
  have hlm : Measurable left := by
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | none => exact hZ₀m.comp measurable_fst
    | some i => exact ((measurable_pi_iff.mp hZm) i).comp measurable_snd
  have hrm : Measurable right := by
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | none => exact hZ₀m
    | some i => exact (measurable_pi_iff.mp hZm) i
  have hlpos : ∀ᵐ z ∂μ.prod μ, ∀ i,
      (left z i : Matrix (Fin (dim i)) (Fin (dim i)) ℝ).PosDef := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hZ₀,
      Measure.quasiMeasurePreserving_snd.ae hZ] with z hz₀ hz i
    cases i with
    | none => exact hz₀
    | some i => exact hz i
  have hrpos : ∀ᵐ z ∂μ, ∀ i,
      (right z i : Matrix (Fin (dim i)) (Fin (dim i)) ℝ).PosDef := by
    filter_upwards [hZ₀, hZ] with z hz₀ hz i
    cases i with
    | none => exact hz₀
    | some i => exact hz i
  have hprofiles : ∀ i, FiniteConvexIncreasingSymmetric (profiles i) := by
    intro i
    cases i with
    | none => exact hh₀
    | some i => exact hh i
  have hcompare := log_spectral_comparison_of_finite_comparisons dim
    (μ.prod μ) μ left right hlm hrm hlpos hrpos (by
      intro n a b ha hanti
      dsimp only [dim, Option.elim] at a ha hanti ⊢
      have hselm : Measurable (fun z => finiteMaximum
          (fun j : Fin (n + 1) => spectralPlaneMonomial (a none j) (b none j) (Z₀ z))) :=
        (continuous_finiteMaximum fun j =>
          continuous_spectralPlaneMonomial _ _ (ha none j) (hanti none j)).measurable.comp hZ₀m
      have hrestm : Measurable (fun z => spectralPlaneMaximumProduct k
          (fun i j => a (some i) j) (fun i j => b (some i) j) (Z z)) :=
        (continuous_spectralPlaneMaximumProduct k _ _
          (fun i j l => ha (some i) j l) (fun i j => hanti (some i) j)).measurable.comp hZm
      have hsel0 : ∀ᵐ z ∂μ, 0 ≤ finiteMaximum
          (fun j : Fin (n + 1) => spectralPlaneMonomial (a none j) (b none j) (Z₀ z)) :=
        hZ₀.mono fun z hz => finiteMaximum_nonneg fun j =>
          spectralPlaneMonomial_nonneg _ _ hz.posSemidef
      have hind := lintegral_independent_real_product (μ := μ) (ν := μ) hselm.aemeasurable hrestm.aemeasurable hsel0
      dsimp only [dim, spectralPlaneMaximumProduct] at hind ⊢
      simp only [Fintype.prod_option, left, right]
      rw [hind]
      exact hfinite n (a none) (b none) (fun i j => a (some i) j)
        (fun i j => b (some i) j) (ha none) (hanti none)
        (fun i j l => ha (some i) j l) (fun i j => hanti (some i) j)) profiles hprofiles
  have hselm : Measurable (fun z => logSpectralFactor h₀ (Z₀ z)) :=
    (measurable_logSpectralFactor hh₀.1).comp hZ₀m
  have hrestm : Measurable (fun z => logSpectralProduct k h (Z z)) := by
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_logSpectralFactor (hh i).1).comp ((measurable_pi_iff.mp hZm) i)
  have hind := lintegral_independent_real_product (μ := μ) (ν := μ) hselm.aemeasurable hrestm.aemeasurable
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
  dsimp only [dim, logSpectralProduct] at hind hcompare
  simp only [Fintype.prod_option, profiles, left, right] at hcompare
  dsimp only [Option.elim] at hcompare
  rw [hind] at hcompare
  exact hcompare

end Wishart.Spectral
end
end CanonicalSource93

section CanonicalSource94
/- Source: Wishart/SpectralLogSplits.lean -/



/-!
# Actual Wishart splits for the full logarithmic spectral class

All final profiles are finite convex symmetric coordinatewise increasing
functions on the entire logarithmic coordinate space. Expectations are extended
nonnegative integrals, and no moment bound is imposed on the final profiles.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart.Spectral

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

def normalizedShiftedMatrix {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (X : Sym p) : Sym q := shiftSymmetric c (normalizedCompression Sigma B X)

theorem measurable_normalizedShiftedMatrix {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) (c : ℝ) :
    Measurable (normalizedShiftedMatrix Sigma B c) :=
  (measurable_normalizedCompression Sigma B).add measurable_const

theorem normalizedShiftedMatrix_posDef {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) {c : ℝ} (hc : 0 ≤ c)
    {X : Sym p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    (normalizedShiftedMatrix Sigma B c X : Matrix (Fin q) (Fin q) ℝ).PosDef :=
  shiftSymmetric_posDef hc (normalizedCompression_posDef hSigma B hB hX)

theorem normalizedShiftedMatrix_eq_affine {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) (c : ℝ)
    (X : Sym p) :
    normalizedShiftedMatrix Sigma B c X =
      affineCompressionSym (c • (1 : Matrix (Fin q) (Fin q) ℝ))
        (Matrix.isHermitian_one.smul (IsSelfAdjoint.all c)) (normalizedCompressionRows Sigma B)ᵀ X := by
  apply Subtype.ext
  simp only [normalizedShiftedMatrix, coe_shiftSymmetric, coe_affineCompressionSym,
    normalizedCompression, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_transpose, add_comm]

def normalizedLogSpectralFactor {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (h : (Fin q → ℝ) → ℝ) (X : Sym p) : ℝ :=
  logSpectralFactor h (normalizedShiftedMatrix Sigma B c X)

theorem measurable_normalizedLogSpectralFactor {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) {h : (Fin q → ℝ) → ℝ} (hh : FiniteConvexIncreasingSymmetric h) :
    Measurable (normalizedLogSpectralFactor Sigma B c h) :=
  (measurable_logSpectralFactor hh.1).comp (measurable_normalizedShiftedMatrix Sigma B c)

theorem normalizedSpectralPlaneTest_matrixTestAllMoments {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (a : ι → Fin q → ℝ) (b : ι → ℝ)
    (ha : ∀ j l, 0 ≤ a j l) (hmono : ∀ j, Antitone (a j)) :
    MatrixTestAllMoments (normalizedSpectralPlaneTest Sigma B c a b) := by
  intro Ω _ μ _ X hXm hX hentries
  simpa only [affineSpectralPlaneTest, spectralPlaneMaximumProduct, Fintype.prod_unique,
    normalizedSpectralPlaneTest, selectedSpectralPlaneTest,
    ← normalizedShiftedMatrix_eq_affine, normalizedShiftedMatrix] using
    matrixTestAllMoments_affineSpectralPlaneTest (fun _ : Unit => q)
      (fun _ => c • (1 : Matrix (Fin q) (Fin q) ℝ))
      (fun _ => Matrix.PosSemidef.one.smul hc)
      (fun _ => (normalizedCompressionRows Sigma B)ᵀ)
      (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hmono) hXm hX hentries

def normalizedSpectralPlaneProduct {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (k : κ → ℕ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (d : κ → ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ) (X : Sym p) : ℝ :=
  spectralPlaneMaximumProduct k a b (fun i => normalizedShiftedMatrix Sigma (M i) (d i) X)

theorem normalizedSpectralPlaneProduct_eq_affine {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (k : κ → ℕ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (d : κ → ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ) (X : Sym p) :
    normalizedSpectralPlaneProduct Sigma k M d a b X =
      affineSpectralPlaneTest k (fun i => d i • (1 : Matrix (Fin (k i)) (Fin (k i)) ℝ))
        (fun i => Matrix.isHermitian_one.smul (IsSelfAdjoint.all (d i)))
        (fun i => (normalizedCompressionRows Sigma (M i))ᵀ) a b X := by
  simp only [normalizedSpectralPlaneProduct, affineSpectralPlaneTest,
    normalizedShiftedMatrix_eq_affine]

theorem normalizedSpectralPlaneProduct_matrixTestAllMoments {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (k : κ → ℕ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) :
    MatrixTestAllMoments (normalizedSpectralPlaneProduct Sigma k M d a b) := by
  intro Ω _ μ _ X hXm hX hentries
  simpa only [normalizedSpectralPlaneProduct_eq_affine] using
    matrixTestAllMoments_affineSpectralPlaneTest k
      (fun i => d i • (1 : Matrix (Fin (k i)) (Fin (k i)) ℝ))
      (fun i => Matrix.PosSemidef.one.smul (hd i))
      (fun i => (normalizedCompressionRows Sigma (M i))ᵀ) a b ha hmono hXm hX hentries

end Wishart.Spectral

namespace Wishart

open Spectral

/-- Internal limit bridge: every finite comparison is supplied below by the
actual normalized Wishart comparison, with its proved finite moments. -/
theorem normalizedLogSpectral_split_of_finite {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h₀ : (Fin q → ℝ) → ℝ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hh₀ : FiniteConvexIncreasingSymmetric h₀) (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i))
    (hfinite : ∀ l : ℕ, ∀ a₀ : Fin (l + 1) → Fin q → ℝ,
      ∀ b₀ : Fin (l + 1) → ℝ, ∀ a : ∀ i, Fin (l + 1) → Fin (k i) → ℝ,
      ∀ b : κ → Fin (l + 1) → ℝ,
      (∀ j s, 0 ≤ a₀ j s) → (∀ j, Antitone (a₀ j)) →
      (∀ i j s, 0 ≤ a i j s) → (∀ i j, Antitone (a i j)) →
      (∫ X, normalizedSpectralPlaneTest Sigma B c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
        (∫ X, normalizedSpectralPlaneProduct Sigma k M d a b X ∂nonsingularWishartMeasure n Sigma) ≤
        ∫ X, normalizedSpectralPlaneTest Sigma B c a₀ b₀ X *
          normalizedSpectralPlaneProduct Sigma k M d a b X ∂nonsingularWishartMeasure n Sigma) :
    (∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma B c h₀ X)
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, normalizedLogSpectralFactor Sigma (M i) (d i) (h i) X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma B c h₀ X *
        ∏ i, normalizedLogSpectralFactor Sigma (M i) (d i) (h i) X)
        ∂nonsingularWishartMeasure n Sigma := by
  let μ := nonsingularWishartMeasure n Sigma
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  have h₀pos : ∀ᵐ X ∂μ,
      (normalizedShiftedMatrix Sigma B c X : Matrix (Fin q) (Fin q) ℝ).PosDef :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      normalizedShiftedMatrix_posDef hSigma B hB hc hX
  have hpos : ∀ᵐ X ∂μ, ∀ i,
      (normalizedShiftedMatrix Sigma (M i) (d i) X : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosDef :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX i =>
      normalizedShiftedMatrix_posDef hSigma (M i) (hM i) (hd i) hX
  apply log_spectral_selected_split_of_finite_splits μ q k
    (normalizedShiftedMatrix Sigma B c)
    (fun X i => normalizedShiftedMatrix Sigma (M i) (d i) X)
    (measurable_normalizedShiftedMatrix Sigma B c)
    (measurable_pi_iff.mpr fun i => measurable_normalizedShiftedMatrix Sigma (M i) (d i))
    h₀pos hpos _ h₀ h hh₀ hh
  intro l a₀ b₀ a b ha₀ hanti₀ ha hanti
  let selected := normalizedSpectralPlaneTest Sigma B c a₀ b₀
  let remaining := normalizedSpectralPlaneProduct Sigma k M d a b
  have hsM : HasAllFiniteMoments selected μ :=
    MatrixTestAllMoments.wishart
      (normalizedSpectralPlaneTest_matrixTestAllMoments Sigma B hc a₀ b₀ ha₀ hanti₀) n Sigma
  have hrM : HasAllFiniteMoments remaining μ :=
    MatrixTestAllMoments.wishart
      (normalizedSpectralPlaneProduct_matrixTestAllMoments Sigma k M d hd a b ha hanti) n Sigma
  have hs0 : ∀ᵐ X ∂μ, 0 ≤ selected X := h₀pos.mono fun X hX =>
    finiteMaximum_nonneg fun j => spectralPlaneMonomial_nonneg _ _ hX.posSemidef
  have hr0 : ∀ᵐ X ∂μ, 0 ≤ remaining X := hpos.mono fun X hX =>
    Finset.prod_nonneg fun i hi => finiteMaximum_nonneg fun j =>
      spectralPlaneMonomial_nonneg _ _ (hX i).posSemidef
  have hcompare := ENNReal.ofReal_le_ofReal (hfinite l a₀ b₀ a b ha₀ hanti₀ ha hanti)
  rw [ENNReal.ofReal_mul (integral_nonneg_of_ae hs0),
    ofReal_integral_eq_lintegral_ofReal hsM.integrable hs0,
    ofReal_integral_eq_lintegral_ofReal hrM.integrable hr0,
    ofReal_integral_eq_lintegral_ofReal (hsM.mul hrM).integrable
      (by filter_upwards [hs0, hr0] with X hs hr; exact mul_nonneg hs hr)] at hcompare
  exact hcompare

/-- The selected-factor assertion of Theorem 5.3 at the exact individual form
of condition (10), for all real admissible Wishart shapes and the full profile
class. The inequality is meaningful even when some expectations are infinite. -/
theorem normalizedLogSpectral_selected_split {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h₀ : (Fin q → ℝ) → ℝ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hh₀ : FiniteConvexIncreasingSymmetric h₀) (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i))
    (hsize : ∀ i, min ((q : ℝ) + k i) ((p : ℝ) + 1) ≤ n) :
    (∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma B c h₀ X)
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, normalizedLogSpectralFactor Sigma (M i) (d i) (h i) X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma B c h₀ X *
        ∏ i, normalizedLogSpectralFactor Sigma (M i) (d i) (h i) X)
        ∂nonsingularWishartMeasure n Sigma := by
  apply normalizedLogSpectral_split_of_finite hSigma hn B hB hc k M hM d hd h₀ h hh₀ hh
  intro l a₀ b₀ a b ha₀ hanti₀ ha hanti
  simpa only [normalizedSpectralPlaneProduct_eq_affine] using
    normalizedSpectralPlane_selected_split hSigma hn B hB hc a₀ b₀ ha₀ hanti₀ k
      (fun i => d i • (1 : Matrix (Fin (k i)) (Fin (k i)) ℝ))
      (fun i => Matrix.PosSemidef.one.smul (hd i))
      (fun i => (normalizedCompressionRows Sigma (M i))ᵀ) a b ha hanti hsize

/-- Full-rank selected spectral factors split with no additional shape bound. -/
theorem normalizedLogSpectral_fullRank_split {p : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.rank = p) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h₀ : (Fin p → ℝ) → ℝ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hh₀ : FiniteConvexIncreasingSymmetric h₀) (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i)) :
    (∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma B c h₀ X)
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, normalizedLogSpectralFactor Sigma (M i) (d i) (h i) X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma B c h₀ X *
        ∏ i, normalizedLogSpectralFactor Sigma (M i) (d i) (h i) X)
        ∂nonsingularWishartMeasure n Sigma := by
  apply normalizedLogSpectral_split_of_finite hSigma hn B hB hc k M hM d hd h₀ h hh₀ hh
  intro l a₀ b₀ a b ha₀ hanti₀ ha hanti
  simpa only [normalizedSpectralPlaneProduct_eq_affine] using
    normalizedSpectralPlane_fullRank_split hSigma hn B hB hc a₀ b₀ ha₀ hanti₀ k
      (fun i => d i • (1 : Matrix (Fin (k i)) (Fin (k i)) ℝ))
      (fun i => Matrix.PosSemidef.one.smul (hd i))
      (fun i => (normalizedCompressionRows Sigma (M i))ᵀ) a b ha hanti

end Wishart
end
end CanonicalSource94

section CanonicalSource95
/- Source: Wishart/RankPairIteration.lean -/



/-! # The largest-two-ranks condition for logarithmic spectral factors

This iteration never uses an unrestricted two-factor comparison. Its threshold
is exactly the pairwise rank bound, which is equivalent to the manuscript's
largest-plus-second-largest condition after discarding inactive factors.
-/

noncomputable section

open scoped Classical ENNReal BigOperators

namespace WishartVerification.MomentAssembly

variable {ι : Type*} [DecidableEq ι]

def rankPairThreshold (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, i ≠ j → min ((rank i : ℝ) + rank j) ((p : ℝ) + 1) ≤ n

theorem extended_product_singletons_le_by_pair_rank (m : Finset ι → ℝ≥0∞)
    (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ)
    (hempty : m ∅ = 1)
    (houtside : ∀ J i, i ∈ J → i ∉ A → m {i} * m (J.erase i) ≤ m J)
    (hrank : ∀ J i, i ∈ J → J ⊆ A →
      (∀ j ∈ J.erase i, min ((rank i : ℝ) + rank j) ((p : ℝ) + 1) ≤ n) →
      m {i} * m (J.erase i) ≤ m J)
    (hthreshold : rankPairThreshold rank A p n) (J : Finset ι) :
    (∏ i ∈ J, m {i}) ≤ m J := by
  apply extended_product_singletons_le_of_exists_split m hempty (fun _ => bot_le) _ J
  intro S hS
  by_cases hout : ∃ i ∈ S, i ∉ A
  · obtain ⟨i, hi, hiA⟩ := hout
    exact ⟨i, hi, houtside S i hi hiA⟩
  have hSA : S ⊆ A := by
    intro i hi
    by_contra hiA
    exact hout ⟨i, hi, hiA⟩
  obtain ⟨i, hi⟩ := hS
  refine ⟨i, hi, hrank S i hi hSA ?_⟩
  intro j hj
  exact hthreshold i (hSA hi) j (hSA (Finset.mem_of_mem_erase hj))
    (Finset.ne_of_mem_erase hj).symm

theorem rankPairThreshold_of_card_le_one (rank : ι → ℕ) (A : Finset ι)
    (p : ℕ) (n : ℝ) (hA : A.card ≤ 1) : rankPairThreshold rank A p n := by
  intro i hi j hj hij
  have heq := Finset.card_le_one.mp hA i hi j hj
  exact (hij heq).elim

theorem rankPairThreshold_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (rank : ι → ℕ) (A : Finset ι) (e : κ ≃ A) (p : ℕ) (n : ℝ) :
    rankPairThreshold rank A p n ↔
      rankPairThreshold (fun i => rank (e i)) Finset.univ p n := by
  constructor
  · intro h i hi j hj hij
    exact h (e i) (e i).property (e j) (e j).property
      (fun heq => hij (e.injective (Subtype.ext heq)))
  · intro h i hi j hj hij
    have hne : e.symm ⟨i, hi⟩ ≠ e.symm ⟨j, hj⟩ := by
      intro heq
      exact hij (congrArg Subtype.val (e.symm.injective heq))
    simpa only [Equiv.apply_symm_apply] using
      h (e.symm ⟨i, hi⟩) (Finset.mem_univ _) (e.symm ⟨j, hj⟩) (Finset.mem_univ _) hne

theorem rankPairThreshold_iff_largest_second {d : ℕ} (hd : 2 ≤ d)
    (rank : Fin d → ℕ) (hsorted : Antitone rank) (p : ℕ) (n : ℝ) :
    rankPairThreshold rank Finset.univ p n ↔
      min ((rank ⟨0, by omega⟩ : ℝ) + rank ⟨1, by omega⟩) ((p : ℝ) + 1) ≤ n := by
  constructor
  · intro h
    exact h ⟨0, by omega⟩ (Finset.mem_univ _) ⟨1, by omega⟩ (Finset.mem_univ _) (by
      intro heq
      have hv := congrArg Fin.val heq
      change (0 : ℕ) = 1 at hv
      omega)
  · intro h i hi j hj hij
    have hijv : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    have hindices : 1 ≤ i.val ∨ 1 ≤ j.val := by omega
    have hi0 : (rank i : ℝ) ≤ rank ⟨0, by omega⟩ := Nat.cast_le.mpr (hsorted (Nat.zero_le _))
    have hj0 : (rank j : ℝ) ≤ rank ⟨0, by omega⟩ := Nat.cast_le.mpr (hsorted (Nat.zero_le _))
    have hsum : (rank i : ℝ) + rank j ≤
        (rank ⟨0, by omega⟩ : ℝ) + rank ⟨1, by omega⟩ := by
      rcases hindices with hi | hj
      · have hi1 : (rank i : ℝ) ≤ rank ⟨1, by omega⟩ := Nat.cast_le.mpr (hsorted hi)
        linarith
      · have hj1 : (rank j : ℝ) ≤ rank ⟨1, by omega⟩ := Nat.cast_le.mpr (hsorted hj)
        linarith
    exact (min_le_min_right _ hsum).trans h

def orderedPairRankThreshold (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) : Prop :=
  ∀ h : 2 ≤ Fintype.card A,
    min ((descendingRanks rank A ⟨0, by omega⟩ : ℝ) +
      descendingRanks rank A ⟨1, by omega⟩) ((p : ℝ) + 1) ≤ n

theorem orderedPairRankThreshold_iff (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) :
    orderedPairRankThreshold rank A p n ↔ rankPairThreshold rank A p n := by
  rw [rankPairThreshold_equiv rank A (descendingRankEquiv rank A) p n]
  change orderedPairRankThreshold rank A p n ↔
    rankPairThreshold (descendingRanks rank A) Finset.univ p n
  by_cases hd : 2 ≤ Fintype.card A
  · rw [rankPairThreshold_iff_largest_second hd _ (antitone_descendingRanks rank A)]
    exact ⟨fun h => h hd, fun h _ => h⟩
  · constructor
    · intro h
      apply rankPairThreshold_of_card_le_one
      simpa only [Finset.card_univ, Fintype.card_fin] using (show Fintype.card A ≤ 1 by omega)
    · intro h hcard
      exact (hd hcard).elim

end WishartVerification.MomentAssembly
end
end CanonicalSource95

section CanonicalSource96
/- Source: Wishart/GeometricConstantFactors.lean -/



/-!
# Almost-sure and pointwise constancy of geometric compression factors

For every admissible nonsingular Wishart law, the null sets on the positive
definite cone agree exactly with restricted symmetric Lebesgue null sets.
The cone is open, symmetric Lebesgue measure gives positive mass to nonempty
open sets, and geometric compression factors are continuous there. Thus the
constant factors discarded from the rank test are exactly the almost surely
constant factors of the actual law.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

theorem ae_nonsingularWishart_iff_ae_restrict_posDef {p : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (hn : (p : ℝ) - 1 < n) (P : SymmetricMatrix p → Prop) :
    (∀ᵐ X ∂nonsingularWishartMeasure n Sigma, P X) ↔
      ∀ᵐ X ∂(symmetricLebesgue p).restrict
        {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef}, P X := by
  rw [nonsingularWishartMeasure_of_posDef hSigma hn,
    ae_withDensity_iff_ae_restrict (measurable_nonsingularWishartPDF n Sigma)]
  have hset : {X : SymmetricMatrix p | nonsingularWishartPDF n Sigma X ≠ 0} =
      {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
    ext X
    exact (pos_iff_ne_zero).symm.trans (nonsingularWishartPDF_pos_iff hSigma hn)
  rw [hset]

/-- Equality almost surely under the actual nonsingular Wishart law extends
to every positive definite matrix for functions continuous on that cone. -/
theorem eqOn_posDef_of_ae_eq_nonsingularWishart {p : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (hn : (p : ℝ) - 1 < n) {f g : SymmetricMatrix p → ℝ}
    (hf : ContinuousOn f {X | (X : Matrix (Fin p) (Fin p) ℝ).PosDef})
    (hg : ContinuousOn g {X | (X : Matrix (Fin p) (Fin p) ℝ).PosDef})
    (hfg : f =ᵐ[nonsingularWishartMeasure n Sigma] g) :
    Set.EqOn f g {X | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  have hae := (ae_nonsingularWishart_iff_ae_restrict_posDef hSigma hn
    (fun X ↦ f X = g X)).mp hfg
  exact Measure.eqOn_open_of_ae_eq hae (isOpen_setOfPred_posDefMatrix p) hf hg

namespace GeometricCompressionFamily

variable {p : ℕ} {ι : Type*} [DecidableEq ι]
variable (F : GeometricCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)

theorem continuousOn_factor_posDef (hSigma : Sigma.PosDef) (i : ι) :
    ContinuousOn (F.factor Sigma i)
      {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  have hd : Continuous (shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i)) := by
    unfold shiftedCompressionDeterminant
    fun_prop
  apply (F.geometric i).continuousOn.comp hd.continuousOn
  intro X hX
  exact shiftedCompressionDeterminant_pos hSigma (F.matrix i) (F.full_rank i)
    (F.shift_nonneg i) hX

theorem factor_ae_eq_const_iff {n : ℝ} (hSigma : Sigma.PosDef)
    (hn : (p : ℝ) - 1 < n) (i : ι) (c : ℝ) :
    (∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c) ↔
      ∀ X : SymmetricMatrix p,
        (X : Matrix (Fin p) (Fin p) ℝ).PosDef → F.factor Sigma i X = c := by
  constructor
  · intro h
    exact eqOn_posDef_of_ae_eq_nonsingularWishart hSigma hn
      (F.continuousOn_factor_posDef Sigma hSigma i) continuousOn_const h
  · intro h
    exact (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX ↦ h X hX

/-- The actual rank-test predicate agrees with almost-sure constancy; the
equivalence requires no moment bound. -/
theorem constantFactor_iff_ae_constant {n : ℝ} (hSigma : Sigma.PosDef)
    (hn : (p : ℝ) - 1 < n) (i : ι) :
    F.ConstantFactor Sigma i ↔
      ∃ c : ℝ, ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c := by
  unfold ConstantFactor
  exact exists_congr (fun c ↦ (F.factor_ae_eq_const_iff Sigma hSigma hn i c).symm)

theorem activeProper_eq_filter_not_ae_constant [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n) :
    F.activeProper Sigma = Finset.univ.filter (fun i ↦ F.size i < p ∧
      ¬ ∃ c : ℝ, ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c) := by
  ext i
  simp only [activeProper, Finset.mem_filter, Finset.mem_univ, true_and,
    F.constantFactor_iff_ae_constant Sigma hSigma hn i]

end GeometricCompressionFamily

end Wishart
end
end CanonicalSource96

section CanonicalSource97
/- Source: Wishart/LogSpectralProducts.lean -/



/-!
# The logarithmic spectral product inequality (Theorem 5.3)

Each factor is exp(h(log λ(S+cI))) for a finite convex symmetric coordinatewise
increasing h and the literal covariance-normalized compression S. The rank
condition is largest-plus-second-largest after removing almost surely constant
and full-rank factors. All expectations are extended nonnegative integrals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

open Spectral

structure LogSpectralCompressionFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  profile : ∀ i, (Fin (size i) → ℝ) → ℝ
  profile_class : ∀ i, FiniteConvexIncreasingSymmetric (profile i)

namespace LogSpectralCompressionFamily

variable {p : ℕ} {ι : Type*} [DecidableEq ι]
variable (F : LogSpectralCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)

def factor (i : ι) (X : SymmetricMatrix p) : ℝ :=
  normalizedLogSpectralFactor Sigma (F.matrix i) (F.shift i) (F.profile i) X

def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, F.factor Sigma i X

def moment (n : ℝ) (J : Finset ι) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma

def ConstantFactor (i : ι) : Prop :=
  ∃ c : ℝ, ∀ X : SymmetricMatrix p,
    (X : Matrix (Fin p) (Fin p) ℝ).PosDef → F.factor Sigma i X = c

def activeProper [Fintype ι] : Finset ι :=
  Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)

theorem size_le (i : ι) : F.size i ≤ p := by
  rw [← F.full_rank i]
  exact (F.matrix i).rank_le_height

/-- Literal manuscript factor, with ascending eigenvalues. Symmetry of the
profile proves equivalence to the descending enumeration used in the proof. -/
theorem factor_eq_raw (i : ι) (X : SymmetricMatrix p) :
    F.factor Sigma i X = Real.exp (F.profile i (fun j => Real.log
      (ascendingSpectrum (normalizedCompression Sigma (F.matrix i) X +
        F.shift i • identitySymmetric (F.size i)) j))) :=
  logSpectralFactor_eq_ascending (F.profile_class i).2.2 _

theorem factor_pos (i : ι) (X : SymmetricMatrix p) : 0 < F.factor Sigma i X :=
  Real.exp_pos _

theorem measurable_factor (i : ι) : Measurable (F.factor Sigma i) :=
  measurable_normalizedLogSpectralFactor Sigma (F.matrix i) (F.shift i) (F.profile_class i)

theorem measurable_subproduct (J : Finset ι) : Measurable (F.subproduct Sigma J) :=
  Finset.measurable_prod J (fun i _ => F.measurable_factor Sigma i)

theorem continuousOn_factor_posDef (hSigma : Sigma.PosDef) (i : ι) :
    ContinuousOn (F.factor Sigma i)
      {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  intro X hX
  apply Real.continuous_exp.continuousAt.comp_continuousWithinAt
  apply (continuous_convexProfile (F.profile_class i).1).continuousAt.comp_continuousWithinAt
  apply continuousWithinAt_pi.mpr
  intro j
  have hpos := descendingSpectrum_pos
    (normalizedShiftedMatrix_posDef hSigma (F.matrix i) (F.full_rank i) (F.shift_nonneg i) hX) j
  have hnorm : Continuous (normalizedShiftedMatrix Sigma (F.matrix i) (F.shift i)) := by
    unfold normalizedShiftedMatrix normalizedCompression shiftSymmetric
    exact (LinearMap.continuous_of_finiteDimensional _).add continuous_const
  have hcoord : ContinuousWithinAt
      (fun Y : SymmetricMatrix p => descendingSpectrum
        (normalizedShiftedMatrix Sigma (F.matrix i) (F.shift i) Y) j)
      {Y : SymmetricMatrix p | (Y : Matrix (Fin p) (Fin p) ℝ).PosDef} X :=
    ((continuous_apply j).comp
      ((continuous_descendingSpectrum _).comp hnorm)).continuousAt.continuousWithinAt
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun Y : SymmetricMatrix p => descendingSpectrum
      (normalizedShiftedMatrix Sigma (F.matrix i) (F.shift i) Y) j)
    (x := X) (Real.continuousAt_log (ne_of_gt hpos)) hcoord

theorem constantFactor_iff_ae_constant {n : ℝ} (hSigma : Sigma.PosDef)
    (hn : (p : ℝ) - 1 < n) (i : ι) :
    F.ConstantFactor Sigma i ↔
      ∃ c : ℝ, ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX => hc X hX⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, eqOn_posDef_of_ae_eq_nonsingularWishart hSigma hn
      (F.continuousOn_factor_posDef Sigma hSigma i) continuousOn_const hc⟩

@[simp] theorem moment_singleton (n : ℝ) (i : ι) :
    F.moment Sigma n {i} =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma := by
  simp only [moment, subproduct, Finset.prod_singleton]

theorem moment_empty {n : ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n) :
    F.moment Sigma n ∅ = 1 := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  simp only [moment, subproduct, Finset.prod_empty, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]

theorem moment_split (n : ℝ) (J : Finset ι) (i : ι) (hi : i ∈ J) :
    F.moment Sigma n J =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X * F.subproduct Sigma (J.erase i) X)
        ∂nonsingularWishartMeasure n Sigma := by
  apply lintegral_congr_ae
  filter_upwards with X
  congr 1
  exact (Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hi).symm

theorem moment_constant_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hconst : F.ConstantFactor Sigma i) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) = F.moment Sigma n J := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  obtain ⟨c, hc⟩ := hconst
  have hcpos : 0 < c := by
    rw [← hc ⟨Sigma, hSigma.isHermitian.isSelfAdjoint⟩ hSigma]
    exact F.factor_pos Sigma i _
  have hcae : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX => hc X hX
  have hsingle : F.moment Sigma n {i} = ENNReal.ofReal c := by
    rw [F.moment_singleton]
    calc
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) =
          ∫⁻ _X, ENNReal.ofReal c ∂nonsingularWishartMeasure n Sigma :=
        lintegral_congr_ae (hcae.mono fun X hX => congrArg ENNReal.ofReal hX)
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  rw [hsingle, F.moment_split Sigma n J i hi]
  calc
    ENNReal.ofReal c * F.moment Sigma n (J.erase i) =
        ∫⁻ X, ENNReal.ofReal c * ENNReal.ofReal (F.subproduct Sigma (J.erase i) X)
          ∂nonsingularWishartMeasure n Sigma :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hcae] with X hX
      rw [hX, ENNReal.ofReal_mul hcpos.le]

theorem moment_selected_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J)
    (hdegree : ∀ j ∈ J.erase i, min ((F.size i : ℝ) + F.size j) ((p : ℝ) + 1) ≤ n) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have h := normalizedLogSpectral_selected_split hSigma hn
    (F.matrix i) (F.full_rank i) (F.shift_nonneg i)
    (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
    (fun j => F.shift j) (fun j => F.shift_nonneg j)
    (F.profile i) (fun j => F.profile j) (F.profile_class i) (fun j => F.profile_class j)
    (fun j => hdegree j j.property)
  change (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X *
        ∏ j : J.erase i, F.factor Sigma (j : ι) X) ∂nonsingularWishartMeasure n Sigma at h
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  have hprod (X : SymmetricMatrix p) :
      (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
        F.subproduct Sigma (J.erase i) X :=
    Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
  simp_rw [hprod] at h
  simpa only [moment] using h

theorem moment_full_rank_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hfull : F.size i = p) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have hsplit (q : ℕ) (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q)
      (h : (Fin q → ℝ) → ℝ) (hh : FiniteConvexIncreasingSymmetric h) (hqp : q = p) :
      (∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma Q (F.shift i) h X)
        ∂nonsingularWishartMeasure n Sigma) * F.moment Sigma n (J.erase i) ≤
        ∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma Q (F.shift i) h X *
          F.subproduct Sigma (J.erase i) X) ∂nonsingularWishartMeasure n Sigma := by
    subst q
    have hs := normalizedLogSpectral_fullRank_split hSigma hn Q hQ (F.shift_nonneg i)
      (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
      (fun j => F.shift j) (fun j => F.shift_nonneg j)
      h (fun j => F.profile j) hh (fun j => F.profile_class j)
    change (∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma Q (F.shift i) h X)
        ∂nonsingularWishartMeasure n Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
          ∂nonsingularWishartMeasure n Sigma) ≤
        ∫⁻ X, ENNReal.ofReal (normalizedLogSpectralFactor Sigma Q (F.shift i) h X *
          ∏ j : J.erase i, F.factor Sigma (j : ι) X) ∂nonsingularWishartMeasure n Sigma at hs
    have hprod (X : SymmetricMatrix p) :
        (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
          F.subproduct Sigma (J.erase i) X :=
      Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
    simp_rw [hprod] at hs
    simpa only [moment] using hs
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  exact hsplit (F.size i) (F.matrix i) (F.full_rank i) (F.profile i) (F.profile_class i) hfull

theorem moment_split_outside_activeProper [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hinactive : i ∉ F.activeProper Sigma) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  by_cases hc : F.ConstantFactor Sigma i
  · exact (F.moment_constant_split Sigma hSigma hn J i hi hc).le
  have hfull : F.size i = p := by
    have hle := F.size_le i
    by_contra hne
    have hklt : F.size i < p := lt_of_le_of_ne hle hne
    exact hinactive (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hklt, hc⟩)
  exact F.moment_full_rank_split Sigma hSigma hn J i hi hfull

/-- Full product comparison under the exact retained largest-two-rank condition.
It is vacuous for at most one retained factor. -/
theorem product_moments_le [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hsize : orderedPairRankThreshold F.size (F.activeProper Sigma) p n) (J : Finset ι) :
    (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
  apply extended_product_singletons_le_by_pair_rank (F.moment Sigma n) F.size
    (F.activeProper Sigma) p n (F.moment_empty Sigma hSigma hn)
    (F.moment_split_outside_activeProper Sigma hSigma hn)
  · intro S i hi hSA hdegree
    exact F.moment_selected_split Sigma hSigma hn S i hi hdegree
  · exact (orderedPairRankThreshold_iff _ _ _ _).mp hsize

/-- Theorem 5.3, with literal logarithmic eigenvalue factors and nonnegative
extended expectations. No radial, spectral-law, approximation, or integrability
premise remains in this statement. -/
theorem theorem_5_3 [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hsize : orderedPairRankThreshold F.size (F.activeProper Sigma) p n) :
    (∏ i, ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i, F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma := by
  simpa only [moment_singleton, moment, subproduct, Finset.prod_singleton] using
    F.product_moments_le Sigma hSigma hn hsize Finset.univ

end LogSpectralCompressionFamily

end Wishart
end
end CanonicalSource97

section CanonicalSource98
/- Source: Wishart/SingularGramSupport.lean -/



/-!
# Determinant support and moments for singular Gaussian Gram laws

The measure is the pushforward of the actual independent Gaussian rows, at
every natural sample size.  No density-defined Wishart law is used below its
admissible shape range.  The support dichotomy identifies precisely the zero
determinants that must be removed before positive-domain outer approximations.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem measurePreserving_gramCompression {p k : ℕ} (n : ℕ)
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosSemidef)
    (B : Matrix (Fin p) (Fin k) ℝ) :
    MeasurePreserving (Matrix.symmetricCongruenceLinearMap Bᵀ)
      (wishartGramMeasure n Sigma) (wishartGramMeasure n (compressionScale Sigma B)) := by
  refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
  simpa only [compressionScale, Matrix.transpose_transpose] using
    map_symmetricCongruenceLinearMap_wishartGramMeasure n Bᵀ hSigma

theorem ae_posDef_gramCompression {p k n : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (hkn : k ≤ n) :
    ∀ᵐ X : SymmetricMatrix p ∂wishartGramMeasure n Sigma,
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).PosDef := by
  have hmap := measurePreserving_gramCompression n hSigma.posSemidef B
  have h := hmap.quasiMeasurePreserving.ae
    (ae_posDef_wishartGramMeasure (compressionScale_posDef hSigma B hB) hkn)
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_transpose] using h

theorem ae_det_gramCompression_eq_zero {p k n : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosSemidef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hnk : n < k) :
    ∀ᵐ X : SymmetricMatrix p ∂wishartGramMeasure n Sigma,
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det = 0 := by
  have hmap := measurePreserving_gramCompression n hSigma B
  have hrank := hmap.quasiMeasurePreserving.ae
    (ae_rank_le_wishartGramMeasure n (compressionScale Sigma B))
  filter_upwards [hrank] with X hX
  simp only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_transpose] at hX
  by_contra hdet
  have heq := Matrix.rank_of_det_ne_zero hdet
  have hle : k ≤ n := by
    simpa only [Fintype.card_fin, heq] using hX.trans (min_le_left _ _)
  exact (not_le_of_gt hnk) hle

theorem ae_shiftedCompressionDeterminant_pos_gram {p k n : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    {c : ℝ} (hc : 0 ≤ c) (hpositive : 0 < c ∨ k ≤ n) :
    ∀ᵐ X ∂wishartGramMeasure n Sigma,
      0 < shiftedCompressionDeterminant Sigma B c X := by
  rcases hpositive with hcpos | hkn
  · filter_upwards [ae_posSemidef_wishartGramMeasure n Sigma] with X hX
    have hcomp : (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hX.conjTranspose_mul_mul_same B
    have hshift := ((compressionScale_posDef hSigma B hB).smul hcpos).add_posSemidef hcomp
    simpa only [shiftedCompressionDeterminant, add_comm] using hshift.det_pos
  · filter_upwards [ae_posDef_gramCompression hSigma B hB hkn] with X hX
    exact (hX.add_posSemidef
      ((compressionScale_posDef hSigma B hB).posSemidef.smul hc)).det_pos

/-- The event of a zero determinant is deterministic: it occurs precisely for
an unshifted compression whose rank exceeds the number of Gaussian rows. -/
theorem ae_shiftedCompressionDeterminant_zero_iff_gram {p k n : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    {c : ℝ} (hc : 0 ≤ c) :
    ∀ᵐ X ∂wishartGramMeasure n Sigma,
      shiftedCompressionDeterminant Sigma B c X = 0 ↔ c = 0 ∧ n < k := by
  by_cases hbad : c = 0 ∧ n < k
  · filter_upwards [ae_det_gramCompression_eq_zero hSigma.posSemidef B hbad.2]
      with X hX
    simp only [shiftedCompressionDeterminant, hbad.1, zero_smul, add_zero, hX,
      true_iff, hbad, and_self]
  · have hpositive : 0 < c ∨ k ≤ n := by
      by_cases hc0 : c = 0
      · exact Or.inr (le_of_not_gt (fun hnk => hbad ⟨hc0, hnk⟩))
      · exact Or.inl (lt_of_le_of_ne hc (Ne.symm hc0))
    filter_upwards [ae_shiftedCompressionDeterminant_pos_gram hSigma B hB hc hpositive]
      with X hX
    exact iff_of_false hX.ne' hbad

theorem ae_outer_unshifted_gram_eq_const {p k n : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosSemidef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hnk : n < k) (f : ℝ → ℝ) :
    ∀ᵐ X ∂wishartGramMeasure n Sigma,
      f (shiftedCompressionDeterminant Sigma B 0 X) = f 0 := by
  filter_upwards [ae_det_gramCompression_eq_zero hSigma B hnk] with X hX
  simp only [shiftedCompressionDeterminant, zero_smul, add_zero, hX]

theorem allFiniteMoments_gram_entry {p : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      (X : Matrix (Fin p) (Fin p) ℝ) i j) (wishartGramMeasure n Sigma) := by
  intro q hq
  simpa only [ENNReal.coe_toNNReal hq] using
    memLp_coe_apply_wishartGramMeasure Sigma n i j q.toNNReal

theorem allFiniteMoments_gram_affine_compression_det {p k : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin p) (Fin k) ℝ) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      (E + Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det)
      (wishartGramMeasure n Sigma) := by
  apply HasAllFiniteMoments.det
  intro i j
  apply HasAllFiniteMoments.add (HasAllFiniteMoments.const (E i j))
  exact HasAllFiniteMoments.matrix_right_mul_entry _ B
    (fun a b => HasAllFiniteMoments.matrix_left_mul_entry _ Bᵀ
      (allFiniteMoments_gram_entry n Sigma) a b) i j

/-- The moment-finiteness assertion of Corollary 5.4, at every natural row
count, for arbitrary overlapping compressions and all nonnegative powers. -/
theorem allFiniteMoments_gram_determinant_product {p : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      ∏ i, (E i + (B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det ^ a i)
      (wishartGramMeasure n Sigma) := by
  exact HasAllFiniteMoments.finset_prod Finset.univ _ fun i _ =>
    (allFiniteMoments_gram_affine_compression_det n Sigma (E i) (B i)).rpow (ha i)

end Wishart
end
end CanonicalSource98

section CanonicalSource99
/- Source: Wishart/GeometricBoundary.lean -/



/-!
# The finite boundary extension in Corollary 5.4

The value at zero is the finite nonnegative right limit stipulated in the
paper.  The positive-domain supporting-monomial approximation is later augmented
by a constant supporting monomial when necessary to recover this value.
-/

noncomputable section

open Filter Set Topology MeasureTheory

namespace WishartVerification

structure GeometricOuterOnNonnegative (f : ℝ → ℝ) : Prop where
  geometric : GeometricallyLogConvex f
  zero_nonneg : 0 ≤ f 0
  continuous_zero : ContinuousWithinAt f (Ici 0) 0

theorem GeometricOuterOnNonnegative.nonneg {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  rcases hx.eq_or_lt with hzero | hpos
  · simpa only [← hzero] using hf.zero_nonneg
  · exact (hf.geometric.positive x hpos).le

theorem GeometricOuterOnNonnegative.zero_le_value {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) {y : ℝ} (hy : 0 < y) : f 0 ≤ f y := by
  have hlim : Tendsto f (𝓝[Ioi 0] 0) (𝓝 (f 0)) :=
    hf.continuous_zero.mono Ioi_subset_Ici_self
  apply le_of_tendsto hlim
  have hnear : ∀ᶠ x in 𝓝[Ioi 0] (0 : ℝ), x < y :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hy)
  filter_upwards [self_mem_nhdsWithin, hnear] with x hx hxy
  exact hf.geometric.monotoneOn hx hy hxy.le

theorem GeometricOuterOnNonnegative.monotoneOn {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) : MonotoneOn f (Ici 0) := by
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · subst x
    rcases hy.eq_or_lt with hy0 | hypos
    · simpa only [← hy0] using (le_rfl : f 0 ≤ f 0)
    · exact hf.zero_le_value hypos
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    exact hf.geometric.monotoneOn hxpos (hxpos.trans_le hxy) hxy

theorem GeometricOuterOnNonnegative.continuousOn {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) : ContinuousOn f (Ici 0) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact hf.continuous_zero
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    exact ((hf.geometric.continuousOn x hxpos).continuousAt
      (Ioi_mem_nhds hxpos)).continuousWithinAt

def nonnegativeOuterExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ici (0 : ℝ)).piecewise f (fun _ => 0)

theorem measurable_nonnegativeOuterExtension {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) : Measurable (nonnegativeOuterExtension f) :=
  hf.continuousOn.measurable_piecewise continuous_const.continuousOn measurableSet_Ici

theorem nonnegativeOuterExtension_eq {f : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) :
    nonnegativeOuterExtension f x = f x := Set.piecewise_eq_of_mem _ _ _ hx

theorem aemeasurable_geometric_outer_comp_nonnegative
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) {d : Ω → ℝ}
    (hd : Measurable d) (hpos : ∀ᵐ z ∂μ, 0 ≤ d z) :
    AEMeasurable (fun z => f (d z)) μ := by
  apply ((measurable_nonnegativeOuterExtension hf).comp hd).aemeasurable.congr
  exact hpos.mono fun z hz => nonnegativeOuterExtension_eq hz

end WishartVerification
end
end CanonicalSource99
