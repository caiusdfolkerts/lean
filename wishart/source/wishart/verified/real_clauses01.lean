module

public import wishart.verified.real_all

/- Real Section 5 supplement, including empty principal blocks.
   Source provenance: verification/recovery-patches.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/MonotoneCompressionPair.lean -/



/-!
# The unrestricted monotone two-factor assertion of Theorem 5.1

The outer functions are only required to be nonnegative and nondecreasing on
the positive half-line. Their values elsewhere are irrelevant. A zero extension
is automatically measurable and nondecreasing, bounded caps give the comparison,
and monotone convergence removes the caps. The real-expectation theorem assumes
exactly the three relevant moments to be finite.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace WishartVerification

def positiveMonotoneExtension (f : ℝ → ℝ) : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator f

theorem positiveMonotoneExtension_eq {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    positiveMonotoneExtension f t = f t := Set.indicator_of_mem ht _

theorem positiveMonotoneExtension_nonneg {f : ℝ → ℝ}
    (hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) (t : ℝ) :
    0 ≤ positiveMonotoneExtension f t := Set.indicator_nonneg hf0 t

theorem monotone_positiveMonotoneExtension {f : ℝ → ℝ}
    (hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) (hf : MonotoneOn f (Set.Ioi 0)) :
    Monotone (positiveMonotoneExtension f) := by
  intro x y hxy
  by_cases hx : 0 < x
  · have hy : 0 < y := hx.trans_le hxy
    rw [positiveMonotoneExtension_eq hx, positiveMonotoneExtension_eq hy]
    exact hf hx hy hxy
  · rw [positiveMonotoneExtension, Set.indicator_of_notMem hx]
    exact positiveMonotoneExtension_nonneg hf0 y

theorem measurable_positiveMonotoneExtension {f : ℝ → ℝ}
    (hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) (hf : MonotoneOn f (Set.Ioi 0)) :
    Measurable (positiveMonotoneExtension f) := (monotone_positiveMonotoneExtension hf0 hf).measurable

end WishartVerification

namespace Wishart

theorem compression_monotone_pair_lintegral_global {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (f g : ℝ → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    (hfmono : MonotoneOn f (Set.Ici 0)) (hgmono : MonotoneOn g (Set.Ici 0)) :
    (∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (g (shiftedCompressionDeterminant Sigma M d X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X) *
        g (shiftedCompressionDeterminant Sigma M d X)) ∂nonsingularWishartMeasure n Sigma := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  apply lintegral_association_of_truncated_integral_association
    (nonsingularWishartMeasure n Sigma)
    (fun X => f (shiftedCompressionDeterminant Sigma Q c X))
    (fun X => g (shiftedCompressionDeterminant Sigma M d X))
    (hfm.comp (measurable_shiftedCompressionDeterminant Sigma Q c))
    (hgm.comp (measurable_shiftedCompressionDeterminant Sigma M d))
    (fun X => hf0 _) (fun X => hg0 _)
  intro l
  let A : ℝ := (l : ℝ) + 1
  have hA : 0 ≤ A := by positivity
  have hfn : ∀ t, 0 ≤ nonnegativeTruncation l f t := nonnegativeTruncation_nonneg l f hf0
  have hgn : ∀ t, 0 ≤ nonnegativeTruncation l g t := nonnegativeTruncation_nonneg l g hg0
  exact compression_monotone_pair_bounded hSigma hn Q hQ M hM hc hd
    (nonnegativeTruncation l f) (nonnegativeTruncation l g)
    (hfm.min measurable_const) (hgm.min measurable_const) hfn hgn
    (fun x hx y hy hxy => min_le_min_right _ (hfmono hx hy hxy))
    (fun x hx y hy hxy => min_le_min_right _ (hgmono hx hy hxy)) A A hA hA
    (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hfn t)]; exact min_le_right _ _)
    (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hgn t)]; exact min_le_right _ _)

/-- The stronger extended-expectation form of the two-factor assertion.
Only the positive-domain values and monotonicity of the outer functions enter.
All ranks, overlaps, and admissible real degrees are allowed. -/
theorem compression_monotone_pair_lintegral {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (f g : ℝ → ℝ)
    (hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) (hg0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t)
    (hfmono : MonotoneOn f (Set.Ioi 0)) (hgmono : MonotoneOn g (Set.Ioi 0)) :
    (∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (g (shiftedCompressionDeterminant Sigma M d X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X) *
        g (shiftedCompressionDeterminant Sigma M d X)) ∂nonsingularWishartMeasure n Sigma := by
  let F := positiveMonotoneExtension f
  let G := positiveMonotoneExtension g
  have h := compression_monotone_pair_lintegral_global hSigma hn Q hQ M hM hc hd F G
    (measurable_positiveMonotoneExtension hf0 hfmono)
    (measurable_positiveMonotoneExtension hg0 hgmono)
    (positiveMonotoneExtension_nonneg hf0) (positiveMonotoneExtension_nonneg hg0)
    ((monotone_positiveMonotoneExtension hf0 hfmono).monotoneOn _)
    ((monotone_positiveMonotoneExtension hg0 hgmono).monotoneOn _)
  have heq : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma,
      F (shiftedCompressionDeterminant Sigma Q c X) = f (shiftedCompressionDeterminant Sigma Q c X) ∧
      G (shiftedCompressionDeterminant Sigma M d X) = g (shiftedCompressionDeterminant Sigma M d X) := by
    filter_upwards [ae_posDef_nonsingularWishartMeasure n Sigma] with X hX
    exact ⟨positiveMonotoneExtension_eq (shiftedCompressionDeterminant_pos hSigma Q hQ hc hX),
      positiveMonotoneExtension_eq (shiftedCompressionDeterminant_pos hSigma M hM hd hX)⟩
  have hsel := lintegral_congr_ae (heq.mono fun X hX => congrArg ENNReal.ofReal hX.1)
  have hrem := lintegral_congr_ae (heq.mono fun X hX => congrArg ENNReal.ofReal hX.2)
  have hjoint := lintegral_congr_ae (heq.mono fun X hX =>
    congrArg ENNReal.ofReal (congrArg₂ (· * ·) hX.1 hX.2))
  rwa [hsel, hrem, hjoint] at h

/-- The final sentence of Theorem 5.1, for arbitrary nonnegative
nondecreasing outer functions and exactly the displayed finite moments. -/
theorem theorem_5_1_monotone_pair {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (f g : ℝ → ℝ)
    (hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) (hg0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t)
    (hfmono : MonotoneOn f (Set.Ioi 0)) (hgmono : MonotoneOn g (Set.Ioi 0))
    (hIf : Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X))
      (nonsingularWishartMeasure n Sigma))
    (hIg : Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X))
      (nonsingularWishartMeasure n Sigma))
    (hIjoint : Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) *
      g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma)) :
    (∫ X, f (shiftedCompressionDeterminant Sigma Q c X) ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, g (shiftedCompressionDeterminant Sigma M d X) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, f (shiftedCompressionDeterminant Sigma Q c X) *
        g (shiftedCompressionDeterminant Sigma M d X) ∂nonsingularWishartMeasure n Sigma := by
  have hfnn : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma,
      0 ≤ f (shiftedCompressionDeterminant Sigma Q c X) :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      hf0 _ (shiftedCompressionDeterminant_pos hSigma Q hQ hc hX)
  have hgnn : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma,
      0 ≤ g (shiftedCompressionDeterminant Sigma M d X) :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      hg0 _ (shiftedCompressionDeterminant_pos hSigma M hM hd hX)
  have hprodnn := (hfnn.and hgnn).mono fun X hX => mul_nonneg hX.1 hX.2
  have h := compression_monotone_pair_lintegral hSigma hn Q hQ M hM hc hd f g hf0 hg0 hfmono hgmono
  rw [← ofReal_integral_eq_lintegral_ofReal hIf hfnn,
    ← ofReal_integral_eq_lintegral_ofReal hIg hgnn,
    ← ofReal_integral_eq_lintegral_ofReal hIjoint hprodnn,
    ← ENNReal.ofReal_mul (integral_nonneg_of_ae hfnn)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hprodnn)).mp h

end Wishart
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/GaugeMonotonePair.lean -/



/-!
# Arbitrary increasing outer functions for a pair of convex spectral gauges

Bounded tests follow directly from Gaussian Anderson comparison, exact regression,
and Laguerre association. Monotone caps then remove boundedness in nonnegative
extended integrals. Geometric log convexity is not required for a pair.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator ENNReal

namespace WishartVerification

theorem matrixTestAllMoments_of_bounded {p : ℕ} {F : SymmetricMatrix p → ℝ}
    (hFm : Measurable F) (A : ℝ) (hbound : ∀ X, ‖F X‖ ≤ A) : MatrixTestAllMoments F := by
  intro Ω _ μ _ X hXm _ _ u hu
  exact ((HasAllFiniteMoments.const (μ := μ) A) u hu).mono'
    (hFm.comp hXm).aestronglyMeasurable (Filter.Eventually.of_forall fun z => hbound (X z))

end WishartVerification

namespace Wishart

theorem monotoneOn_fullRegressionSpectralAverage_gauge_bounded
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (G : GaugeCompression (q + m))
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (A : ℝ) (hbound : ∀ x ∈ Set.Ici (0 : ℝ), ‖f x‖ ≤ A) :
    MonotoneOn (fullRegressionSpectralAverage n C K (fun X => f (G.value X)))
      (Spectral.positiveChamber q) := by
  have hFM : MatrixTestAllMoments (fun X => f (G.value X)) :=
    matrixTestAllMoments_of_bounded (hfm.comp G.measurable_value) A
      (fun X => hbound _ (G.value_nonneg X))
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  have hconditional (O : Matrix (Fin q) (Fin q) ℝ) :
      MonotoneOn (fun lam => fullSpectralConditionalMoment n C K (fun X => f (G.value X)) lam O)
        (Set.Ici (0 : Fin q → ℝ)) := by
    let L := regressionNoiseInjection q m * CFC.sqrt C
    let v := fullSpectralRegressionDirections K O
    have hmono : MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
        f (G.value (linearShiftedRowsSym L v lam x))
          ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure (n - q) 1))
        (Set.Ici (0 : Fin q → ℝ)) := by
      apply monotoneOn_nonnegative_pi_of_update
      intro lam u
      apply monotoneOn_linearShiftedRows_gauge_coordinate_of_integrable hν L G hfm hf v lam u
      intro t
      apply (integrable_const A).mono'
        ((hfm.comp G.measurable_value).comp
          (measurable_linearShiftedRowsSym L v (Function.update lam u t))).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => hbound _ (G.value_nonneg _)
    intro lam hlam lam' hlam' hle
    dsimp only
    rw [fullSpectralConditionalMoment_standardNoise n hC K O lam (g := fun X => f (G.value X))
        (hfm.comp G.measurable_value),
      fullSpectralConditionalMoment_standardNoise n hC K O lam' (g := fun X => f (G.value X))
        (hfm.comp G.measurable_value)]
    exact hmono hlam hlam' hle
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_fullSpectralConditionalMoment_test hn hC K hFM lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O => hconditional ↑O
      (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

theorem shiftedGaugeValue_diagonal_monotone {q : ℕ} (Φ : SpectralGauge q)
    {c : ℝ} (hc : 0 ≤ c) :
    MonotoneOn (fun lam => shiftedGaugeValue Φ c (Spectral.diagonalSym lam))
      (Spectral.positiveChamber q) := by
  intro lam hlam lam' hlam' hle
  have hX : (Spectral.diagonalSym lam : Matrix (Fin q) (Fin q) ℝ).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => (hlam.2 i).le
  have hY : (Spectral.diagonalSym lam' : Matrix (Fin q) (Fin q) ℝ).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => (hlam'.2 i).le
  have hXY : ((Spectral.diagonalSym lam' - Spectral.diagonalSym lam : SymmetricMatrix q) :
      Matrix (Fin q) (Fin q) ℝ).PosSemidef := by
    change (Matrix.diagonal lam' - Matrix.diagonal lam).PosSemidef
    rw [Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr (hle i)
  simpa only [shiftedGaugeValue_identity] using
    (identityGaugeCompression Φ c hc).value_loewner _ _ hX hY hXY

theorem identity_leading_gauge_bounded_pair
    {q m : ℕ} {n c : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (Φ : SpectralGauge q) (hc : 0 ≤ c) (G : GaugeCompression (q + m))
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MonotoneOn f (Set.Ici 0)) (hg : MonotoneOn g (Set.Ici 0))
    (hf0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ f x) (hg0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ g x)
    (A B : ℝ) (hfA : ∀ x ∈ Set.Ici (0 : ℝ), ‖f x‖ ≤ A)
    (hgB : ∀ x ∈ Set.Ici (0 : ℝ), ‖g x‖ ≤ B) :
    (∫ X, f (shiftedGaugeValue Φ c (principalSymmetricBlock (Fin.castAdd m) X))
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, g (G.value X) ∂nonsingularWishartMeasure n 1) ≤
      ∫ X, f (shiftedGaugeValue Φ c (principalSymmetricBlock (Fin.castAdd m) X)) * g (G.value X)
        ∂nonsingularWishartMeasure n 1 := by
  have hh : Measurable (fun S => f (shiftedGaugeValue Φ c S)) :=
    hfm.comp (measurable_shiftedGaugeValue Φ c)
  have hHM : HasAllFiniteMoments (fun S => f (shiftedGaugeValue Φ c S))
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) :=
    MatrixTestAllMoments.wishart
      (matrixTestAllMoments_of_bounded hh A (fun S => hfA _ (Φ.value_nonneg _))) n 1
  have hm : Measurable (fun lam : Fin q → ℝ => f (shiftedGaugeValue Φ c (Spectral.diagonalSym lam))) :=
    hh.comp (by apply Measurable.subtype_mk; fun_prop)
  have hs : ∀ lam ∈ Spectral.positiveChamber q, ∀ O : Spectral.Orth q,
      f (shiftedGaugeValue Φ c (regressionSpectralMatrix (lam, O))) =
        f (shiftedGaugeValue Φ c (Spectral.diagonalSym lam)) := by
    intro lam hlam O
    rw [shiftedGaugeValue_spectral Φ hc lam (fun i => (hlam.2 i).le) O]
  have h := regression_test_split_of_spectral_monotone hn (0 : Matrix (Fin q) (Fin m) ℝ)
    Matrix.PosDef.one hh hHM hm (fun lam => hf0 _ (Φ.value_nonneg _))
    (fun lam hlam lam' hlam' hle => hf (Φ.value_nonneg _) (Φ.value_nonneg _)
      (shiftedGaugeValue_diagonal_monotone Φ hc hlam hlam' hle)) hs
    (hgm.comp G.measurable_value)
    (matrixTestAllMoments_of_bounded (hgm.comp G.measurable_value) B
      (fun X => hgB _ (G.value_nonneg X)))
    (fun X _ => hg0 _ (G.value_nonneg X))
    (monotoneOn_fullRegressionSpectralAverage_gauge_bounded hn Matrix.PosDef.one 0 G hgm hg B hgB)
  simpa only [regressionScale_zero_one, Function.comp_def] using h

theorem normalizedGauge_bounded_pair {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    (M : Matrix (Fin p) (Fin k) ℝ) (Ψ : SpectralGauge k) (hd : 0 ≤ d)
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MonotoneOn f (Set.Ici 0)) (hg : MonotoneOn g (Set.Ici 0))
    (hf0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ f x) (hg0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ g x)
    (A B : ℝ) (hfA : ∀ x ∈ Set.Ici (0 : ℝ), ‖f x‖ ≤ A)
    (hgB : ∀ x ∈ Set.Ici (0 : ℝ), ‖g x‖ ≤ B) :
    (∫ X, f (normalizedGaugeValue Sigma Q Φ c X) ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, g (normalizedGaugeValue Sigma M Ψ d X) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, f (normalizedGaugeValue Sigma Q Φ c X) * g (normalizedGaugeValue Sigma M Ψ d X)
        ∂nonsingularWishartMeasure n Sigma := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (compressionNormalization hSigma Q hQ).q_le
  let N := compressionNormalization hSigma Q hQ
  let G := normalizedGaugeCompression Sigma M Ψ d hd
  have hpush := map_compressionNormalization n N
  have htransform (h : SymmetricMatrix (q + m) → ℝ) (hh : Measurable h) :
      (∫ X, h X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, h (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [← hpush, integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hh.aestronglyMeasurable]
  have hselm := hfm.comp (measurable_normalizedGaugeValue Sigma Q Φ c)
  have hremm := hgm.comp (measurable_normalizedGaugeValue Sigma M Ψ d)
  rw [htransform (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) hselm,
    htransform (fun X => g (normalizedGaugeValue Sigma M Ψ d X)) hremm,
    htransform (fun X => f (normalizedGaugeValue Sigma Q Φ c X) *
      g (normalizedGaugeValue Sigma M Ψ d X)) (hselm.mul hremm)]
  have h := identity_leading_gauge_bounded_pair hn Φ hc (G.pullback N.ambient)
    hfm hgm hf hg hf0 hg0 A B hfA hgB
  simpa only [GaugeCompression.value_pullback, G, normalizedGaugeCompression_value,
    normalizedGaugeValue, normalizedCompression_congruence_sum hSigma Q hQ N] using h

/-- The manuscript's arbitrary nonnegative nondecreasing pair clause. The proof
actually permits extended expectations; its finite-real-moment specialization
is obtained by the standard integral/lintegral correspondence. -/
theorem normalizedGauge_monotone_pair {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    (M : Matrix (Fin p) (Fin k) ℝ) (Ψ : SpectralGauge k) (hd : 0 ≤ d)
    {f g : ℝ → ℝ} (hf : MonotoneOn f (Set.Ici 0)) (hg : MonotoneOn g (Set.Ici 0))
    (hf0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ f x) (hg0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ g x) :
    (∫⁻ X, ENNReal.ofReal (f (normalizedGaugeValue Sigma Q Φ c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (g (normalizedGaugeValue Sigma M Ψ d X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f (normalizedGaugeValue Sigma Q Φ c X) *
        g (normalizedGaugeValue Sigma M Ψ d X)) ∂nonsingularWishartMeasure n Sigma := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  let f' : ℝ → ℝ := fun x => f (max 0 x)
  let g' : ℝ → ℝ := fun x => g (max 0 x)
  have hf' : Monotone f' := fun x y hxy => hf (le_max_left _ _) (le_max_left _ _)
    (max_le_max_left 0 hxy)
  have hg' : Monotone g' := fun x y hxy => hg (le_max_left _ _) (le_max_left _ _)
    (max_le_max_left 0 hxy)
  have hfm : Measurable (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) := by
    simpa only [f', Function.comp_def, max_eq_right (normalizedGaugeValue_nonneg Sigma Q Φ c _)] using
      hf'.measurable.comp (measurable_normalizedGaugeValue Sigma Q Φ c)
  have hgm : Measurable (fun X => g (normalizedGaugeValue Sigma M Ψ d X)) := by
    simpa only [g', Function.comp_def, max_eq_right (normalizedGaugeValue_nonneg Sigma M Ψ d _)] using
      hg'.measurable.comp (measurable_normalizedGaugeValue Sigma M Ψ d)
  apply lintegral_association_of_truncated_integral_association
    (nonsingularWishartMeasure n Sigma) _ _ hfm hgm
    (fun X => hf0 _ (normalizedGaugeValue_nonneg Sigma Q Φ c X))
    (fun X => hg0 _ (normalizedGaugeValue_nonneg Sigma M Ψ d X))
  intro l
  let fc := nonnegativeTruncation l f'
  let gc := nonnegativeTruncation l g'
  have hfc0 (x : ℝ) : 0 ≤ fc x :=
    nonnegativeTruncation_nonneg l f' (fun x => hf0 _ (le_max_left _ _)) x
  have hgc0 (x : ℝ) : 0 ≤ gc x :=
    nonnegativeTruncation_nonneg l g' (fun x => hg0 _ (le_max_left _ _)) x
  have h := normalizedGauge_bounded_pair hSigma hn Q hQ Φ hc M Ψ hd
    (hf'.measurable.min measurable_const) (hg'.measurable.min measurable_const)
    (fun x _ y _ hxy => min_le_min_right _ (hf' hxy))
    (fun x _ y _ hxy => min_le_min_right _ (hg' hxy))
    (fun x _ => hfc0 x) (fun x _ => hgc0 x) ((l : ℝ) + 1) ((l : ℝ) + 1)
    (fun x _ => by
      change ‖fc x‖ ≤ (l : ℝ) + 1
      rw [Real.norm_of_nonneg (hfc0 x)]
      exact min_le_right _ _)
    (fun x _ => by
      change ‖gc x‖ ≤ (l : ℝ) + 1
      rw [Real.norm_of_nonneg (hgc0 x)]
      exact min_le_right _ _)
  simpa only [fc, gc, nonnegativeTruncation, f', g',
    max_eq_right (normalizedGaugeValue_nonneg Sigma Q Φ c _),
    max_eq_right (normalizedGaugeValue_nonneg Sigma M Ψ d _)] using h

/-- Finite-real-expectation form of the arbitrary nondecreasing outer-function
pair assertion, with precisely the three relevant integrability hypotheses. -/
theorem normalizedGauge_monotone_pair_integral {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    (M : Matrix (Fin p) (Fin k) ℝ) (Ψ : SpectralGauge k) (hd : 0 ≤ d)
    {f g : ℝ → ℝ} (hf : MonotoneOn f (Set.Ici 0)) (hg : MonotoneOn g (Set.Ici 0))
    (hf0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ f x) (hg0 : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ g x)
    (hfi : Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X))
      (nonsingularWishartMeasure n Sigma))
    (hgi : Integrable (fun X => g (normalizedGaugeValue Sigma M Ψ d X))
      (nonsingularWishartMeasure n Sigma))
    (hfgi : Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X) *
      g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma)) :
    (∫ X, f (normalizedGaugeValue Sigma Q Φ c X) ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, g (normalizedGaugeValue Sigma M Ψ d X) ∂nonsingularWishartMeasure n Sigma) ≤
        ∫ X, f (normalizedGaugeValue Sigma Q Φ c X) *
          g (normalizedGaugeValue Sigma M Ψ d X) ∂nonsingularWishartMeasure n Sigma :=
  integral_mul_le_of_lintegral_mul_le _ _ _
    (fun X => hf0 _ (normalizedGaugeValue_nonneg Sigma Q Φ c X))
    (fun X => hg0 _ (normalizedGaugeValue_nonneg Sigma M Ψ d X)) hfi hgi hfgi
    (normalizedGauge_monotone_pair hSigma hn Q hQ Φ hc M Ψ hd hf hg hf0 hg0)

end Wishart
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/GaugePrincipalSplits.lean -/



/-!
# Every disjoint principal gauge split in the full real-shape range

The blocks may be any pairwise disjoint nonempty coordinate sets; covering the
ambient coordinates is unnecessary. A selected block omits two coordinates
whenever two other blocks exist. This proves the row threshold from the given
nonsingular shape condition, rather than adding it as a hypothesis.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability WishartVerification
open WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem disjoint_principal_selected_gauge_rank_bound {p d : ℕ} {n : ℝ}
    (hn : (p : ℝ) - 1 < n) (I : Fin d → Finset (Fin p))
    (hI : ∀ i, (I i).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hd : 3 ≤ d) (i : Fin d) : (Fintype.card (I i) : ℝ) + 1 ≤ n := by
  obtain ⟨j, _, hji⟩ := Finset.exists_mem_ne
    (s := (Finset.univ : Finset (Fin d))) (by simpa using (show 1 < d by omega)) i
  obtain ⟨k, hki, hkj⟩ := exists_third_block_index hd i j hji.symm
  obtain ⟨a, hak⟩ := hI k
  have hai : a ∉ I i := fun hai => Finset.disjoint_left.mp (hdisjoint hki) hak hai
  have haj : a ∉ I j := fun haj => Finset.disjoint_left.mp (hdisjoint hkj) hak haj
  have ha : a ∉ I i ∪ I j := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hai, haj⟩
  have hcard := Finset.card_le_card (Finset.subset_univ (insert a (I i ∪ I j)))
  have hnat : (I i).card + (I j).card + 1 ≤ p := by
    simpa only [Finset.card_insert_of_notMem ha,
      Finset.card_union_of_disjoint (hdisjoint hji.symm), Finset.card_univ, Fintype.card_fin] using hcard
  have hjpos : 0 < (I j).card := Finset.card_pos.mpr (hI j)
  have hi : (I i).card + 2 ≤ p := by omega
  have hireal : (Fintype.card (I i) : ℝ) + 2 ≤ p := by
    rw [Fintype.card_coe]
    exact_mod_cast hi
  linarith

/-- The actual normalized principal matrix, with the covariance inverse square
root on both sides, in an arbitrary fixed enumeration of the coordinate set. -/
def normalizedPrincipalGaugeMatrix {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Finset (Fin p)) (X : SymmetricMatrix p) : SymmetricMatrix (Fintype.card I) :=
  Matrix.symmetricCongruenceLinearMap
    (CFC.sqrt (Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I)))⁻¹
      (principalSetMatrix I X)

theorem compressionScale_principalSelection {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) :
    compressionScale Sigma (principalSelectionMatrix I) =
      Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I) := by
  simp only [compressionScale, principalSelectionMatrix, Matrix.transpose_submatrix,
    Matrix.transpose_one, Matrix.submatrix_one_mul_mul_submatrix_one]

theorem normalizedCompression_principalSelection {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) (X : SymmetricMatrix p) :
    normalizedCompression Sigma (principalSelectionMatrix I) X =
      normalizedPrincipalGaugeMatrix Sigma I X := by
  unfold normalizedCompression normalizedCompressionRows
  rw [compressionScale_principalSelection, Matrix.symmetricCongruenceLinearMap_mul,
    LinearMap.comp_apply]
  simp only [principalSelectionMatrix, Matrix.transpose_submatrix, Matrix.transpose_one,
    normalizedPrincipalGaugeMatrix, principalSetMatrix, principalSymmetricBlock_eq_congruence]

def principalGaugeFamily {p d : ℕ} (I : Fin d → Finset (Fin p))
    (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) : GeometricGaugeFamily p (Fin d) where
  size i := Fintype.card (I i)
  matrix i := principalSelectionMatrix (I i)
  full_rank i := principalSelectionMatrix_rank (I i)
  gauge := Φ
  shift := c
  shift_nonneg := hc
  outer := f
  geometric := hf

def principalGaugeFactor {p d : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Fin d → Finset (Fin p)) (Φ : ∀ i, SpectralGauge (Fintype.card (I i)))
    (c : Fin d → ℝ) (f : Fin d → ℝ → ℝ) (i : Fin d) (X : SymmetricMatrix p) : ℝ :=
  f i (Φ i (normalizedPrincipalGaugeMatrix Sigma (I i) X +
    c i • SpectralGauge.identitySymmetric (Fintype.card (I i))))

theorem principalGaugeFamily_factor_eq {p d : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p))
    (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (i : Fin d)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (principalGaugeFamily I Φ c hc f hf).factor Sigma i X =
      principalGaugeFactor Sigma I Φ c f i X := by
  rw [GeometricGaugeFamily.factor_eq_raw _ _ i hX]
  simp only [principalGaugeFamily, normalizedCompression_principalSelection, principalGaugeFactor]
  rfl

theorem principalGaugeFamily_moment_eq {p d : ℕ} (n : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p))
    (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d)) :
    (principalGaugeFamily I Φ c hc f hf).moment Sigma n J =
      ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, principalGaugeFactor Sigma I Φ c f i X)
        ∂nonsingularWishartMeasure n Sigma := by
  apply lintegral_congr_ae
  filter_upwards [ae_posDef_nonsingularWishartMeasure n Sigma] with X hX
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact principalGaugeFamily_factor_eq Sigma I Φ c hc f hf i hX.posSemidef

theorem principalGaugeFamily_selected_split {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d))
    (i : Fin d) (hi : i ∈ J) :
    (principalGaugeFamily I Φ c hc f hf).moment Sigma n {i} *
      (principalGaugeFamily I Φ c hc f hf).moment Sigma n (J.erase i) ≤
        (principalGaugeFamily I Φ c hc f hf).moment Sigma n J := by
  let F := principalGaugeFamily I Φ c hc f hf
  by_cases hsmall : J.card ≤ 2
  · exact F.moment_pair_split Sigma hSigma hn J i hi hsmall
  · have hJd : J.card ≤ d := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ J)
    exact F.moment_selected_split Sigma hSigma hn J i hi
      (disjoint_principal_selected_gauge_rank_bound hn I hI hdisjoint (by omega) i)

/-- Every selected split in the disjoint-principal clause of Theorem 5.2,
with literal covariance-normalized gauge factors and extended expectations. -/
theorem theorem_5_2_disjoint_principal_selected_split {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d))
    (i : Fin d) (hi : i ∈ J) :
    (∫⁻ X, ENNReal.ofReal (principalGaugeFactor Sigma I Φ c f i X)
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j ∈ J.erase i, principalGaugeFactor Sigma I Φ c f j X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ j ∈ J, principalGaugeFactor Sigma I Φ c f j X)
        ∂nonsingularWishartMeasure n Sigma := by
  have h := principalGaugeFamily_selected_split hSigma hn I hI hdisjoint Φ c hc f hf J i hi
  simpa only [principalGaugeFamily_moment_eq, Finset.prod_singleton] using h

/-- Full disjoint-principal gauge product inequality, with no extra condition
on the number or dimensions of the blocks. -/
theorem theorem_5_2_disjoint_principal_product {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (principalGaugeFactor Sigma I Φ c f i X)
      ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, principalGaugeFactor Sigma I Φ c f i X)
        ∂nonsingularWishartMeasure n Sigma := by
  let F := principalGaugeFamily I Φ c hc f hf
  have h : (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
    apply extended_product_singletons_le_of_exists_split (F.moment Sigma n)
      (F.moment_empty Sigma hSigma hn) (fun _ => bot_le) _ J
    intro S hS
    obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, principalGaugeFamily_selected_split hSigma hn I hI hdisjoint Φ c hc f hf S i hi⟩
  simpa only [F, principalGaugeFamily_moment_eq, Finset.prod_singleton] using h

end Wishart
end
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/GaugeStatementCorrespondence.lean -/



/-!
# Exact constancy and outer-function domains in Theorem 5.2

The rank test discards precisely the almost surely constant factors.  The
arbitrary monotone pair assertion uses outer functions only on the positive
half-line, because the actual normalized gauge arguments are positive under
every admissible nonsingular Wishart law.  Their values at zero and on the
negative half-line impose no extra hypothesis.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem continuousOn_normalizedGaugeValue_posDef {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c) :
    ContinuousOn (normalizedGaugeValue Sigma B Φ c)
      {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  let G : SymmetricMatrix p → SymmetricMatrix q := fun X =>
    normalizedCompression Sigma B X + c • SpectralGauge.identitySymmetric q
  have hG : Continuous G := by
    unfold G normalizedCompression
    exact (LinearMap.continuous_of_finiteDimensional _).add continuous_const
  have hcone : Set.MapsTo G
      {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef}
      (positiveSemidefiniteCone q) := by
    intro X hX
    apply Matrix.PosSemidef.add _ (Matrix.PosSemidef.one.smul hc)
    simpa only [normalizedCompression, Matrix.coe_symmetricCongruenceLinearMap_apply,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.posSemidef.mul_mul_conjTranspose_same (normalizedCompressionRows Sigma B)
  apply (Φ.continuousOn.comp hG.continuousOn hcone).congr
  intro X hX
  exact normalizedGaugeValue_eq_raw Sigma B Φ hc hX.posSemidef

namespace GeometricGaugeFamily

variable {p : ℕ} {ι : Type*} [DecidableEq ι]
variable (F : GeometricGaugeFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)

theorem continuousOn_factor_posDef (hSigma : Sigma.PosDef) (i : ι) :
    ContinuousOn (F.factor Sigma i)
      {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  apply (F.geometric i).continuousOn.comp
    (continuousOn_normalizedGaugeValue_posDef Sigma (F.matrix i) (F.gauge i)
      (F.shift_nonneg i))
  intro X hX
  exact normalizedGaugeValue_pos hSigma (F.matrix i) (F.full_rank i)
    (F.gauge i) (F.shift_nonneg i) hX

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

theorem activeProper_eq_filter_not_ae_constant [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n) :
    F.activeProper Sigma = Finset.univ.filter (fun i => F.size i < p ∧
      ¬ ∃ c : ℝ, ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c) := by
  ext i
  simp only [activeProper, Finset.mem_filter, Finset.mem_univ, true_and,
    F.constantFactor_iff_ae_constant Sigma hSigma hn i]

end GeometricGaugeFamily

/-- The unrestricted pair assertion needs no condition on an unused value
of either outer function at zero.  Both compressions retain their full ranks. -/
theorem normalizedGauge_positive_monotone_pair {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k) (Ψ : SpectralGauge k) (hd : 0 ≤ d)
    (f g : ℝ → ℝ) (hf : MonotoneOn f (Set.Ioi 0)) (hg : MonotoneOn g (Set.Ioi 0))
    (hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) (hg0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t) :
    (∫⁻ X, ENNReal.ofReal (f (normalizedGaugeValue Sigma Q Φ c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (g (normalizedGaugeValue Sigma M Ψ d X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f (normalizedGaugeValue Sigma Q Φ c X) *
        g (normalizedGaugeValue Sigma M Ψ d X)) ∂nonsingularWishartMeasure n Sigma := by
  let f' := positiveMonotoneExtension f
  let g' := positiveMonotoneExtension g
  have h := normalizedGauge_monotone_pair hSigma hn Q hQ Φ hc M Ψ hd
    ((monotone_positiveMonotoneExtension hf0 hf).monotoneOn _)
    ((monotone_positiveMonotoneExtension hg0 hg).monotoneOn _)
    (fun t _ => positiveMonotoneExtension_nonneg hf0 t)
    (fun t _ => positiveMonotoneExtension_nonneg hg0 t)
  have heq : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma,
      f' (normalizedGaugeValue Sigma Q Φ c X) = f (normalizedGaugeValue Sigma Q Φ c X) ∧
      g' (normalizedGaugeValue Sigma M Ψ d X) = g (normalizedGaugeValue Sigma M Ψ d X) := by
    filter_upwards [ae_posDef_nonsingularWishartMeasure n Sigma] with X hX
    exact ⟨positiveMonotoneExtension_eq (normalizedGaugeValue_pos hSigma Q hQ Φ hc hX),
      positiveMonotoneExtension_eq (normalizedGaugeValue_pos hSigma M hM Ψ hd hX)⟩
  have hsel := lintegral_congr_ae (heq.mono fun X hX => congrArg ENNReal.ofReal hX.1)
  have hrem := lintegral_congr_ae (heq.mono fun X hX => congrArg ENNReal.ofReal hX.2)
  have hjoint := lintegral_congr_ae (heq.mono fun X hX =>
    congrArg ENNReal.ofReal (congrArg₂ (· * ·) hX.1 hX.2))
  rwa [hsel, hrem, hjoint] at h

theorem theorem_5_2_monotone_pair {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k) (Ψ : SpectralGauge k) (hd : 0 ≤ d)
    (f g : ℝ → ℝ) (hf : MonotoneOn f (Set.Ioi 0)) (hg : MonotoneOn g (Set.Ioi 0))
    (hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) (hg0 : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t)
    (hIf : Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X))
      (nonsingularWishartMeasure n Sigma))
    (hIg : Integrable (fun X => g (normalizedGaugeValue Sigma M Ψ d X))
      (nonsingularWishartMeasure n Sigma))
    (hIjoint : Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X) *
      g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma)) :
    (∫ X, f (normalizedGaugeValue Sigma Q Φ c X) ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, g (normalizedGaugeValue Sigma M Ψ d X) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, f (normalizedGaugeValue Sigma Q Φ c X) *
        g (normalizedGaugeValue Sigma M Ψ d X) ∂nonsingularWishartMeasure n Sigma := by
  have hfnn : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma,
      0 ≤ f (normalizedGaugeValue Sigma Q Φ c X) :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      hf0 _ (normalizedGaugeValue_pos hSigma Q hQ Φ hc hX)
  have hgnn : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma,
      0 ≤ g (normalizedGaugeValue Sigma M Ψ d X) :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      hg0 _ (normalizedGaugeValue_pos hSigma M hM Ψ hd hX)
  have hprodnn := (hfnn.and hgnn).mono fun X hX => mul_nonneg hX.1 hX.2
  have h := normalizedGauge_positive_monotone_pair hSigma hn Q hQ Φ hc M hM Ψ hd
    f g hf hg hf0 hg0
  rw [← ofReal_integral_eq_lintegral_ofReal hIf hfnn,
    ← ofReal_integral_eq_lintegral_ofReal hIg hgnn,
    ← ofReal_integral_eq_lintegral_ofReal hIjoint hprodnn,
    ← ENNReal.ofReal_mul (integral_nonneg_of_ae hfnn)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hprodnn)).mp h

end Wishart
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/SectionFivePrincipalSplits.lean -/



/-!
# The disjoint-principal clauses of Theorems 5.1 and 5.3

All factors are the literal shifted principal determinants or the literal
covariance-normalized principal logarithmic spectral tests.  The rank bounds
are consequences of actual disjoint nonempty coordinate sets.  In the
logarithmic spectral case, a third original block remains available to bound
the final pair even after earlier factors have been split away.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open WishartVerification.MomentAssembly Wishart.Spectral
open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem disjoint_principal_pair_card_le {p d : ℕ}
    (I : Fin d → Finset (Fin p))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (i j : Fin d) (hij : i ≠ j) :
    Fintype.card (I i) + Fintype.card (I j) ≤ p := by
  have h := Finset.card_le_card (Finset.subset_univ (I i ∪ I j))
  simpa only [Fintype.card_coe, Finset.card_union_of_disjoint (hdisjoint hij),
    Finset.card_univ, Fintype.card_fin] using h

theorem disjoint_principal_pair_rank_bound_of_three {p d : ℕ} {n : ℝ}
    (hn : (p : ℝ) - 1 < n) (I : Fin d → Finset (Fin p))
    (hI : ∀ i, (I i).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hd : 3 ≤ d) (i j : Fin d) (hij : i ≠ j) :
    min ((Fintype.card (I i) : ℝ) + Fintype.card (I j)) ((p : ℝ) + 1) ≤ n := by
  obtain ⟨k, hki, hkj⟩ := exists_third_block_index hd i j hij
  obtain ⟨a, hak⟩ := hI k
  have hai : a ∉ I i := fun hai => Finset.disjoint_left.mp (hdisjoint hki) hak hai
  have haj : a ∉ I j := fun haj => Finset.disjoint_left.mp (hdisjoint hkj) hak haj
  have ha : a ∉ I i ∪ I j := by simp only [Finset.mem_union, not_or]; exact ⟨hai, haj⟩
  have hcard := Finset.card_le_card (Finset.subset_univ (insert a (I i ∪ I j)))
  have hnat : Fintype.card (I i) + Fintype.card (I j) + 1 ≤ p := by
    simpa only [Fintype.card_coe, Finset.card_insert_of_notMem ha,
      Finset.card_union_of_disjoint (hdisjoint hij), Finset.card_univ, Fintype.card_fin] using hcard
  have hreal : (Fintype.card (I i) : ℝ) + Fintype.card (I j) + 1 ≤ p := by
    exact_mod_cast hnat
  exact (min_le_left _ _).trans (by linarith)

def principalShiftedDeterminant {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Finset (Fin p)) (c : ℝ) (X : SymmetricMatrix p) : ℝ :=
  ((X : Matrix (Fin p) (Fin p) ℝ).submatrix (principalSetCoordinates I) (principalSetCoordinates I) +
    c • Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I)).det

theorem shiftedCompressionDeterminant_principalSelection {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) (c : ℝ) (X : SymmetricMatrix p) :
    shiftedCompressionDeterminant Sigma (principalSelectionMatrix I) c X =
      principalShiftedDeterminant Sigma I c X := by
  unfold shiftedCompressionDeterminant principalShiftedDeterminant
  rw [compressionScale_principalSelection]
  simp only [principalSelectionMatrix, Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.submatrix_one_mul_mul_submatrix_one]

def principalGeometricFamily {p d : ℕ} (I : Fin d → Finset (Fin p))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) : GeometricCompressionFamily p (Fin d) where
  size i := Fintype.card (I i)
  matrix i := principalSelectionMatrix (I i)
  full_rank i := principalSelectionMatrix_rank (I i)
  shift := c
  shift_nonneg := hc
  outer := f
  geometric := hf

theorem principalGeometricFamily_factor_eq {p d : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (i : Fin d) (X : SymmetricMatrix p) :
    (principalGeometricFamily I c hc f hf).factor Sigma i X =
      f i (principalShiftedDeterminant Sigma (I i) (c i) X) := by
  simp only [GeometricCompressionFamily.factor, principalGeometricFamily,
    shiftedCompressionDeterminant_principalSelection]

theorem principalGeometricFamily_moment_eq {p d : ℕ} (n : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d)) :
    (principalGeometricFamily I c hc f hf).moment Sigma n J =
      ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, f i (principalShiftedDeterminant Sigma (I i) (c i) X))
        ∂nonsingularWishartMeasure n Sigma := by
  simp only [GeometricCompressionFamily.moment, GeometricCompressionFamily.subproduct,
    principalGeometricFamily_factor_eq]

theorem principalGeometricFamily_selected_split {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d))
    (i : Fin d) (hi : i ∈ J) :
    (principalGeometricFamily I c hc f hf).moment Sigma n {i} *
      (principalGeometricFamily I c hc f hf).moment Sigma n (J.erase i) ≤
        (principalGeometricFamily I c hc f hf).moment Sigma n J := by
  let F := principalGeometricFamily I c hc f hf
  by_cases hsmall : J.card ≤ 2
  · exact F.moment_pair_split Sigma hSigma hn J i hi hsmall
  · have hJd : J.card ≤ d := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ J)
    apply F.moment_selected_split Sigma hSigma hn J i hi
    intro j hj
    exact disjoint_principal_pair_rank_bound_of_three hn I hI hdisjoint (by omega) i j
      (Finset.ne_of_mem_erase hj).symm

theorem theorem_5_1_disjoint_principal_selected_split {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d))
    (i : Fin d) (hi : i ∈ J) :
    (∫⁻ X, ENNReal.ofReal (f i (principalShiftedDeterminant Sigma (I i) (c i) X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j ∈ J.erase i,
        f j (principalShiftedDeterminant Sigma (I j) (c j) X)) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ j ∈ J,
        f j (principalShiftedDeterminant Sigma (I j) (c j) X)) ∂nonsingularWishartMeasure n Sigma := by
  simpa only [principalGeometricFamily_moment_eq, Finset.prod_singleton] using
    principalGeometricFamily_selected_split hSigma hn I hI hdisjoint c hc f hf J i hi

theorem theorem_5_1_disjoint_principal_product {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (f i (principalShiftedDeterminant Sigma (I i) (c i) X))
      ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i ∈ J,
        f i (principalShiftedDeterminant Sigma (I i) (c i) X)) ∂nonsingularWishartMeasure n Sigma := by
  let F := principalGeometricFamily I c hc f hf
  have h : (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
    apply extended_product_singletons_le_of_exists_split (F.moment Sigma n)
      (F.moment_empty Sigma hSigma hn) (fun _ => bot_le) _ J
    intro S hS
    obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, principalGeometricFamily_selected_split hSigma hn I hI hdisjoint c hc f hf S i hi⟩
  simpa only [F, principalGeometricFamily_moment_eq, Finset.prod_singleton] using h

def principalLogSpectralFamily {p d : ℕ} (I : Fin d → Finset (Fin p))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i)) : LogSpectralCompressionFamily p (Fin d) where
  size i := Fintype.card (I i)
  matrix i := principalSelectionMatrix (I i)
  full_rank i := principalSelectionMatrix_rank (I i)
  shift := c
  shift_nonneg := hc
  profile := h
  profile_class := hh

def principalLogSpectralFactor {p d : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Fin d → Finset (Fin p)) (c : Fin d → ℝ)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ) (i : Fin d) (X : SymmetricMatrix p) : ℝ :=
  Real.exp (h i (fun j => Real.log (ascendingSpectrum
    (normalizedPrincipalGaugeMatrix Sigma (I i) X +
      c i • Spectral.identitySymmetric (Fintype.card (I i))) j)))

theorem principalLogSpectralFamily_factor_eq {p d : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i)) (i : Fin d) (X : SymmetricMatrix p) :
    (principalLogSpectralFamily I c hc h hh).factor Sigma i X =
      principalLogSpectralFactor Sigma I c h i X := by
  rw [LogSpectralCompressionFamily.factor_eq_raw]
  simp only [principalLogSpectralFamily, normalizedCompression_principalSelection,
    principalLogSpectralFactor]
  rfl

theorem principalLogSpectralFamily_moment_eq {p d : ℕ} (n : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i)) (J : Finset (Fin d)) :
    (principalLogSpectralFamily I c hc h hh).moment Sigma n J =
      ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, principalLogSpectralFactor Sigma I c h i X)
        ∂nonsingularWishartMeasure n Sigma := by
  simp only [LogSpectralCompressionFamily.moment, LogSpectralCompressionFamily.subproduct,
    principalLogSpectralFamily_factor_eq]

/-- A third original nonempty disjoint block supplies the missing ambient
coordinate even at the final two-factor split. Alternatively n≥p covers
every pair of disjoint blocks, including a two-block partition. -/
theorem principalLogSpectralFamily_selected_split {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hrange : 3 ≤ d ∨ (p : ℝ) ≤ n)
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i))
    (J : Finset (Fin d)) (i : Fin d) (hi : i ∈ J) :
    (principalLogSpectralFamily I c hc h hh).moment Sigma n {i} *
      (principalLogSpectralFamily I c hc h hh).moment Sigma n (J.erase i) ≤
        (principalLogSpectralFamily I c hc h hh).moment Sigma n J := by
  apply LogSpectralCompressionFamily.moment_selected_split _ Sigma hSigma hn J i hi
  intro j hj
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  rcases hrange with hd | hp
  · exact disjoint_principal_pair_rank_bound_of_three hn I hI hdisjoint hd i j hij
  · have hnat := disjoint_principal_pair_card_le I hdisjoint i j hij
    have hreal : (Fintype.card (I i) : ℝ) + Fintype.card (I j) ≤ p := by exact_mod_cast hnat
    exact (min_le_left _ _).trans (hreal.trans hp)

theorem theorem_5_3_disjoint_principal_selected_split {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hrange : 3 ≤ d ∨ (p : ℝ) ≤ n)
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i))
    (J : Finset (Fin d)) (i : Fin d) (hi : i ∈ J) :
    (∫⁻ X, ENNReal.ofReal (principalLogSpectralFactor Sigma I c h i X)
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j ∈ J.erase i, principalLogSpectralFactor Sigma I c h j X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ j ∈ J, principalLogSpectralFactor Sigma I c h j X)
        ∂nonsingularWishartMeasure n Sigma := by
  simpa only [principalLogSpectralFamily_moment_eq, Finset.prod_singleton] using
    principalLogSpectralFamily_selected_split hSigma hn I hI hdisjoint hrange c hc h hh J i hi

theorem theorem_5_3_disjoint_principal_product {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p)) (hI : ∀ i, (I i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hrange : 3 ≤ d ∨ (p : ℝ) ≤ n)
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ)
    (hh : ∀ i, FiniteConvexIncreasingSymmetric (h i)) (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (principalLogSpectralFactor Sigma I c h i X)
      ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, principalLogSpectralFactor Sigma I c h i X)
        ∂nonsingularWishartMeasure n Sigma := by
  let F := principalLogSpectralFamily I c hc h hh
  have hprod : (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
    apply extended_product_singletons_le_of_exists_split (F.moment Sigma n)
      (F.moment_empty Sigma hSigma hn) (fun _ => bot_le) _ J
    intro S hS
    obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, principalLogSpectralFamily_selected_split hSigma hn I hI hdisjoint hrange c hc h hh S i hi⟩
  simpa only [F, principalLogSpectralFamily_moment_eq, Finset.prod_singleton] using hprod

end Wishart
end
end CanonicalSource4

section CanonicalSource7
/- Source: Wishart/SectionFiveEmptyBlocks.lean -/



/-!
# Empty principal determinant blocks in Theorem 5.1

An empty principal block has determinant one, even after the proportional
shift. Its outer factor is therefore an actual constant. Removing such a
factor uses the exact constant-moment identity, with no division or finiteness
assumption on the remaining extended expectations.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

@[simp] theorem principalShiftedDeterminant_empty {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) (X : SymmetricMatrix p) :
    principalShiftedDeterminant Sigma ∅ c X = 1 := by
  unfold principalShiftedDeterminant
  haveI : IsEmpty (Fin (Fintype.card (∅ : Finset (Fin p)))) := by
    rw [Fintype.card_coe, Finset.card_empty]
    infer_instance
  exact Matrix.det_isEmpty

theorem principalGeometricFamily_constantFactor_of_empty {p d : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (i : Fin d) (hI : I i = ∅) :
    (principalGeometricFamily I c hc f hf).ConstantFactor Sigma i := by
  refine ⟨f i 1, fun X _ => ?_⟩
  rw [principalGeometricFamily_factor_eq, hI, principalShiftedDeterminant_empty]

/-- Every selected disjoint-principal split, permitting empty original blocks.
The induction removes literal empty-block constants before using the genuine
two-factor comparison or the three-nonempty-block dimension bound. -/
theorem principalGeometricFamily_selected_split_allow_empty {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d))
    (i : Fin d) (hi : i ∈ J) :
    (principalGeometricFamily I c hc f hf).moment Sigma n {i} *
      (principalGeometricFamily I c hc f hf).moment Sigma n (J.erase i) ≤
        (principalGeometricFamily I c hc f hf).moment Sigma n J := by
  let F := principalGeometricFamily I c hc f hf
  change F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J
  revert i
  refine Finset.strongInductionOn J ?_
  intro S ih i hi
  by_cases hiempty : I i = ∅
  · exact (F.moment_constant_split Sigma hSigma hn S i hi
      (principalGeometricFamily_constantFactor_of_empty Sigma I c hc f hf i hiempty)).le
  by_cases hempty : ∃ j ∈ S, I j = ∅
  · obtain ⟨j, hj, hjempty⟩ := hempty
    have hij : i ≠ j := by
      intro heq
      subst j
      exact hiempty hjempty
    have hi' : i ∈ S.erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
    have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    have hconst : F.ConstantFactor Sigma j :=
      principalGeometricFamily_constantFactor_of_empty Sigma I c hc f hf j hjempty
    have hsplit := ih (S.erase j) (Finset.erase_ssubset hj) i hi'
    calc
      F.moment Sigma n {i} * F.moment Sigma n (S.erase i) =
          F.moment Sigma n {i} *
            (F.moment Sigma n {j} * F.moment Sigma n ((S.erase i).erase j)) :=
        congrArg (fun z => F.moment Sigma n {i} * z)
          (F.moment_constant_split Sigma hSigma hn (S.erase i) j hj' hconst).symm
      _ = F.moment Sigma n {j} *
          (F.moment Sigma n {i} * F.moment Sigma n ((S.erase i).erase j)) := by ac_rfl
      _ = F.moment Sigma n {j} *
          (F.moment Sigma n {i} * F.moment Sigma n ((S.erase j).erase i)) := by
        rw [Finset.erase_right_comm]
      _ ≤ F.moment Sigma n {j} * F.moment Sigma n (S.erase j) :=
        mul_le_mul_right hsplit _
      _ = F.moment Sigma n S := F.moment_constant_split Sigma hSigma hn S j hj hconst
  · have hnonempty : ∀ j ∈ S, (I j).Nonempty := by
      intro j hj
      by_contra hne
      exact hempty ⟨j, hj, Finset.not_nonempty_iff_eq_empty.mp hne⟩
    by_cases hsmall : S.card ≤ 2
    · exact F.moment_pair_split Sigma hSigma hn S i hi hsmall
    · apply F.moment_selected_split Sigma hSigma hn S i hi
      intro j hj
      change min ((Fintype.card (I i) : ℝ) + Fintype.card (I j)) ((p : ℝ) + 1) ≤ n
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have hrest : 1 < (S.erase i).card := by
        rw [Finset.card_erase_of_mem hi]
        omega
      obtain ⟨k, hk, hkj⟩ := Finset.exists_mem_ne (s := S.erase i) hrest j
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      obtain ⟨a, hak⟩ := hnonempty k (Finset.mem_of_mem_erase hk)
      have hai : a ∉ I i := fun hai => Finset.disjoint_left.mp (hdisjoint hki) hak hai
      have haj : a ∉ I j := fun haj => Finset.disjoint_left.mp (hdisjoint hkj) hak haj
      have ha : a ∉ I i ∪ I j := by
        simp only [Finset.mem_union, not_or]
        exact ⟨hai, haj⟩
      have hcard := Finset.card_le_card (Finset.subset_univ (insert a (I i ∪ I j)))
      have hnat : (I i).card + (I j).card + 1 ≤ p := by
        simpa only [Finset.card_insert_of_notMem ha,
          Finset.card_union_of_disjoint (hdisjoint hij), Finset.card_univ,
          Fintype.card_fin] using hcard
      have hreal : (Fintype.card (I i) : ℝ) + Fintype.card (I j) + 1 ≤ p := by
        simp only [Fintype.card_coe]
        exact_mod_cast hnat
      exact (min_le_left _ _).trans (by linarith)

theorem theorem_5_1_disjoint_principal_selected_split_allow_empty {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d))
    (i : Fin d) (hi : i ∈ J) :
    (∫⁻ X, ENNReal.ofReal (f i (principalShiftedDeterminant Sigma (I i) (c i) X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j ∈ J.erase i,
        f j (principalShiftedDeterminant Sigma (I j) (c j) X)) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ j ∈ J,
        f j (principalShiftedDeterminant Sigma (I j) (c j) X)) ∂nonsingularWishartMeasure n Sigma := by
  simpa only [principalGeometricFamily_moment_eq, Finset.prod_singleton] using
    principalGeometricFamily_selected_split_allow_empty hSigma hn I hdisjoint c hc f hf J i hi

theorem theorem_5_1_disjoint_principal_product_allow_empty {p d : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (I : Fin d → Finset (Fin p))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (f i (principalShiftedDeterminant Sigma (I i) (c i) X))
      ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i ∈ J,
        f i (principalShiftedDeterminant Sigma (I i) (c i) X)) ∂nonsingularWishartMeasure n Sigma := by
  let F := principalGeometricFamily I c hc f hf
  have h : (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
    apply extended_product_singletons_le_of_exists_split (F.moment Sigma n)
      (F.moment_empty Sigma hSigma hn) (fun _ => bot_le) _ J
    intro S hS
    obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, principalGeometricFamily_selected_split_allow_empty
      hSigma hn I hdisjoint c hc f hf S i hi⟩
  simpa only [F, principalGeometricFamily_moment_eq, Finset.prod_singleton] using h

end Wishart
end
end CanonicalSource7

section CanonicalSource5
/- Source: Wishart/SectionFiveStatements.lean -/



/-!
# Complete statement targets for the real Section 5 results

The targets retain selected splits, the exact retained-rank product tests,
all exceptional full-rank and two-factor clauses, the stronger principal-block
ranges, the arbitrary monotone pair assertions, and the singular Gram moment
claim.  Every expectation below is an integral of an actual function under
the literal density-defined or independent-Gaussian-row law.

These proposition definitions are statement targets.  Their proof constants
are supplied separately in `SectionFiveTheorems` and require ordinary checking
and the same final body/axiom audit as every principal result.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open WishartVerification.MomentAssembly Wishart.Spectral
open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def selectedExtendedBound {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (J : Finset ι) (i : ι) : Prop :=
  (∫⁻ X, ENNReal.ofReal (f i X) ∂μ) *
    (∫⁻ X, ENNReal.ofReal (∏ j ∈ J.erase i, f j X) ∂μ) ≤
      ∫⁻ X, ENNReal.ofReal (∏ j ∈ J, f j X) ∂μ

def productExtendedBound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (J : Finset ι) : Prop :=
  (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (f i X) ∂μ) ≤
    ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, f i X) ∂μ

def realPairBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) : Prop :=
  (∫ X, f X ∂μ) * (∫ X, g X ∂μ) ≤ ∫ X, f X * g X ∂μ

/-- The literal maximum in (10). The empty remaining product is handled by
the separate trivial-small-family clause whenever that clause applies. -/
def selectedCompressionRankBound {ι : Type*} [DecidableEq ι]
    (rank : ι → ℕ) (J : Finset ι) (i : ι) (p : ℕ) (n : ℝ) : Prop :=
  min ((rank i : ℝ) + (J.erase i).sup rank) ((p : ℝ) + 1) ≤ n

theorem selectedCompressionRankBound_each {ι : Type*} [DecidableEq ι]
    {rank : ι → ℕ} {J : Finset ι} {i : ι} {p : ℕ} {n : ℝ}
    (h : selectedCompressionRankBound rank J i p n) {j : ι} (hj : j ∈ J.erase i) :
    min ((rank i : ℝ) + rank j) ((p : ℝ) + 1) ≤ n := by
  change min ((rank i : ℝ) + (J.erase i).sup rank) ((p : ℝ) + 1) ≤ n at h
  have hsup : (rank j : ℝ) ≤ ((J.erase i).sup rank : ℕ) :=
    Nat.cast_le.mpr (Finset.le_sup hj)
  exact (min_le_min_right _ (add_le_add_right hsup (rank i : ℝ))).trans h

/-- This checks the equivalence of the implementation's individual bounds
with the displayed maximum when another factor remains. -/
theorem selectedCompressionRankBound_iff_each {ι : Type*} [DecidableEq ι]
    (rank : ι → ℕ) (J : Finset ι) (i : ι) (p : ℕ) (n : ℝ)
    (hne : (J.erase i).Nonempty) :
    selectedCompressionRankBound rank J i p n ↔
      ∀ j ∈ J.erase i, min ((rank i : ℝ) + rank j) ((p : ℝ) + 1) ≤ n := by
  constructor
  · intro h j hj
    exact selectedCompressionRankBound_each h hj
  · intro h
    obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup (J.erase i) hne rank
    unfold selectedCompressionRankBound
    rw [hmax]
    exact h j hj

structure DeterminantCompressionConclusion {p d : ℕ}
    (F : GeometricCompressionFamily p (Fin d))
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (n : ℝ) : Prop where
  selected : ∀ J : Finset (Fin d), ∀ i ∈ J,
    (F.size i = p ∨ J.card ≤ 2 ∨ selectedCompressionRankBound F.size J i p n) →
      selectedExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J i
  product : orderedRankThreshold F.size (F.activeProper Sigma) p n →
    ∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J
  constants : ∀ i, F.ConstantFactor Sigma i ↔
    ∃ c : ℝ, ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c

structure GaugeCompressionConclusion {p d : ℕ}
    (F : GeometricGaugeFamily p (Fin d))
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (n : ℝ) : Prop where
  selected : ∀ J : Finset (Fin d), ∀ i ∈ J,
    (F.size i = p ∨ J.card ≤ 2 ∨ (F.size i : ℝ) + 1 ≤ n) →
      selectedExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J i
  product : orderedGaugeRankThreshold F.size (F.activeProper Sigma) n →
    ∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J
  constants : ∀ i, F.ConstantFactor Sigma i ↔
    ∃ c : ℝ, ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c

structure LogSpectralCompressionConclusion {p d : ℕ}
    (F : LogSpectralCompressionFamily p (Fin d))
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (n : ℝ) : Prop where
  selected : ∀ J : Finset (Fin d), ∀ i ∈ J,
    (F.size i = p ∨ selectedCompressionRankBound F.size J i p n) →
      selectedExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J i
  product : orderedPairRankThreshold F.size (F.activeProper Sigma) p n →
    ∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J
  constants : ∀ i, F.ConstantFactor Sigma i ↔
    ∃ c : ℝ, ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c

def Theorem51GeometricTarget : Prop :=
  ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (F : GeometricCompressionFamily p (Fin d)),
    Sigma.PosDef → (p : ℝ) - 1 < n → DeterminantCompressionConclusion F Sigma n

def Theorem52GeometricTarget : Prop :=
  ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (F : GeometricGaugeFamily p (Fin d)),
    Sigma.PosDef → (p : ℝ) - 1 < n → GaugeCompressionConclusion F Sigma n

def Theorem53SpectralTarget : Prop :=
  ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (F : LogSpectralCompressionFamily p (Fin d)),
    Sigma.PosDef → (p : ℝ) - 1 < n → LogSpectralCompressionConclusion F Sigma n

def Theorem51MonotonePairTarget : Prop :=
  ∀ (p q k : ℕ) (n c d : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (Q : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin k) ℝ) (f g : ℝ → ℝ),
    Sigma.PosDef → (p : ℝ) - 1 < n → Q.rank = q → M.rank = k → 0 ≤ c → 0 ≤ d →
    (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) → (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t) →
    MonotoneOn f (Set.Ioi 0) → MonotoneOn g (Set.Ioi 0) →
    Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X))
      (nonsingularWishartMeasure n Sigma) →
    Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X))
      (nonsingularWishartMeasure n Sigma) →
    Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) *
      g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma) →
    realPairBound (nonsingularWishartMeasure n Sigma)
      (fun X => f (shiftedCompressionDeterminant Sigma Q c X))
      (fun X => g (shiftedCompressionDeterminant Sigma M d X))

def Theorem52MonotonePairTarget : Prop :=
  ∀ (p q k : ℕ) (n c d : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (Q : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin k) ℝ)
    (Φ : SpectralGauge q) (Ψ : SpectralGauge k) (f g : ℝ → ℝ),
    Sigma.PosDef → (p : ℝ) - 1 < n → Q.rank = q → M.rank = k → 0 ≤ c → 0 ≤ d →
    (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) → (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t) →
    MonotoneOn f (Set.Ioi 0) → MonotoneOn g (Set.Ioi 0) →
    Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X))
      (nonsingularWishartMeasure n Sigma) →
    Integrable (fun X => g (normalizedGaugeValue Sigma M Ψ d X))
      (nonsingularWishartMeasure n Sigma) →
    Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X) *
      g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma) →
    realPairBound (nonsingularWishartMeasure n Sigma)
      (fun X => f (normalizedGaugeValue Sigma Q Φ c X))
      (fun X => g (normalizedGaugeValue Sigma M Ψ d X))

def Theorem51PrincipalTarget : Prop :=
  ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Fin d → Finset (Fin p)) (c : Fin d → ℝ) (f : Fin d → ℝ → ℝ),
    Sigma.PosDef → (p : ℝ) - 1 < n →
    Pairwise (fun i j => Disjoint (I i) (I j)) → (∀ i, 0 ≤ c i) →
    (∀ i, GeometricallyLogConvex (f i)) →
    (∀ J, ∀ i ∈ J, selectedExtendedBound (nonsingularWishartMeasure n Sigma)
      (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J i) ∧
    (∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma)
      (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J)

def Theorem52PrincipalTarget : Prop :=
  ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Fin d → Finset (Fin p)) (Φ : ∀ i, SpectralGauge (Fintype.card (I i)))
    (c : Fin d → ℝ) (f : Fin d → ℝ → ℝ),
    Sigma.PosDef → (p : ℝ) - 1 < n → (∀ i, (I i).Nonempty) →
    Pairwise (fun i j => Disjoint (I i) (I j)) → (∀ i, 0 ≤ c i) →
    (∀ i, GeometricallyLogConvex (f i)) →
    (∀ J, ∀ i ∈ J, selectedExtendedBound (nonsingularWishartMeasure n Sigma)
      (principalGaugeFactor Sigma I Φ c f) J i) ∧
    (∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma)
      (principalGaugeFactor Sigma I Φ c f) J)

def Theorem53PrincipalTarget : Prop :=
  ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Fin d → Finset (Fin p)) (c : Fin d → ℝ)
    (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ),
    Sigma.PosDef → (p : ℝ) - 1 < n → (∀ i, (I i).Nonempty) →
    Pairwise (fun i j => Disjoint (I i) (I j)) → (3 ≤ d ∨ (p : ℝ) ≤ n) →
    (∀ i, 0 ≤ c i) → (∀ i, FiniteConvexIncreasingSymmetric (h i)) →
    (∀ J, ∀ i ∈ J, selectedExtendedBound (nonsingularWishartMeasure n Sigma)
      (principalLogSpectralFactor Sigma I c h) J i) ∧
    (∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma)
      (principalLogSpectralFactor Sigma I c h) J)

def Corollary54ProductTarget : Prop :=
  ∀ (p d n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (F : GramGeometricCompressionFamily p (Fin d)),
    1 ≤ n → Sigma.PosDef → gramOrderedRankThreshold F.size (F.activeProper Sigma n) n →
    ∀ J, productExtendedBound (wishartGramMeasure n Sigma) (F.factor Sigma) J

def Corollary54MonotonePairTarget : Prop :=
  ∀ (p q k n : ℕ) (c d : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (Q : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin k) ℝ) (f g : ℝ → ℝ),
    1 ≤ n → Sigma.PosDef → Q.rank = q → M.rank = k → 0 ≤ c → 0 ≤ d →
    (∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ f t) → (∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ g t) →
    MonotoneOn f (Set.Ici 0) → MonotoneOn g (Set.Ici 0) →
    Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X))
      (wishartGramMeasure n Sigma) →
    Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X))
      (wishartGramMeasure n Sigma) →
    Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) *
      g (shiftedCompressionDeterminant Sigma M d X)) (wishartGramMeasure n Sigma) →
    realPairBound (wishartGramMeasure n Sigma)
      (fun X => f (shiftedCompressionDeterminant Sigma Q c X))
      (fun X => g (shiftedCompressionDeterminant Sigma M d X))

def Corollary54PowerTarget : Prop :=
  ∀ (p d n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ),
    1 ≤ n → Sigma.PosDef → (∀ i, (B i).rank = k i) →
    (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) → HasAllFiniteMoments
      (fun X : SymmetricMatrix p => ∏ i, shiftedCompressionDeterminant Sigma (B i) (c i) X ^ ν i)
      (wishartGramMeasure n Sigma)

/-- The complete central assertions of Section 5, including every separate
pair and principal-block clause. None is an assumption of another field. -/
structure RealSectionFiveTarget : Prop where
  determinant : Theorem51GeometricTarget
  determinantPair : Theorem51MonotonePairTarget
  determinantPrincipal : Theorem51PrincipalTarget
  gauge : Theorem52GeometricTarget
  gaugePair : Theorem52MonotonePairTarget
  gaugePrincipal : Theorem52PrincipalTarget
  logarithmicSpectral : Theorem53SpectralTarget
  logarithmicSpectralPrincipal : Theorem53PrincipalTarget
  singularGram : Corollary54ProductTarget
  singularGramPair : Corollary54MonotonePairTarget
  singularGramPowers : Corollary54PowerTarget

end Wishart
end
end CanonicalSource5

section CanonicalSource6
/- Source: Wishart/SectionFiveTheorems.lean -/



/-!
# Complete real Section 5 theorem assembly

All clauses are instantiated from the actual laws and proved analytic
comparisons.  This module introduces no comparison, spectral-law, growth,
integrability, or constant-factor premise beyond the literal target statements.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open WishartVerification.MomentAssembly Wishart.Spectral
open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem theorem_5_1_geometric_target : Theorem51GeometricTarget := by
  intro p d n Sigma F hSigma hn
  refine ⟨?_, ?_, fun i => F.constantFactor_iff_ae_constant Sigma hSigma hn i⟩
  · intro J i hi hrange
    have h : F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
      rcases hrange with hfull | hsmall | hrank
      · exact F.moment_full_rank_split Sigma hSigma hn J i hi hfull
      · exact F.moment_pair_split Sigma hSigma hn J i hi hsmall
      · exact F.moment_selected_split Sigma hSigma hn J i hi
          (fun j hj => selectedCompressionRankBound_each hrank hj)
    simpa only [selectedExtendedBound, GeometricCompressionFamily.moment,
      GeometricCompressionFamily.subproduct, Finset.prod_singleton] using h
  · intro hrank J
    simpa only [productExtendedBound, GeometricCompressionFamily.moment,
      GeometricCompressionFamily.subproduct, Finset.prod_singleton] using
      F.product_moments_le Sigma hSigma hn hrank J

theorem theorem_5_2_geometric_target : Theorem52GeometricTarget := by
  intro p d n Sigma F hSigma hn
  refine ⟨?_, ?_, fun i => F.constantFactor_iff_ae_constant Sigma hSigma hn i⟩
  · intro J i hi hrange
    have h : F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
      rcases hrange with hfull | hsmall | hrank
      · exact F.moment_full_rank_split Sigma hSigma hn J i hi hfull
      · exact F.moment_pair_split Sigma hSigma hn J i hi hsmall
      · exact F.moment_selected_split Sigma hSigma hn J i hi hrank
    simpa only [selectedExtendedBound, GeometricGaugeFamily.moment,
      GeometricGaugeFamily.subproduct, Finset.prod_singleton] using h
  · intro hrank J
    simpa only [productExtendedBound, GeometricGaugeFamily.moment,
      GeometricGaugeFamily.subproduct, Finset.prod_singleton] using
      F.product_moments_le Sigma hSigma hn hrank J

theorem theorem_5_3_spectral_target : Theorem53SpectralTarget := by
  intro p d n Sigma F hSigma hn
  refine ⟨?_, ?_, fun i => F.constantFactor_iff_ae_constant Sigma hSigma hn i⟩
  · intro J i hi hrange
    have h : F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
      rcases hrange with hfull | hrank
      · exact F.moment_full_rank_split Sigma hSigma hn J i hi hfull
      · exact F.moment_selected_split Sigma hSigma hn J i hi
          (fun j hj => selectedCompressionRankBound_each hrank hj)
    simpa only [selectedExtendedBound, LogSpectralCompressionFamily.moment,
      LogSpectralCompressionFamily.subproduct, Finset.prod_singleton] using h
  · intro hrank J
    simpa only [productExtendedBound, LogSpectralCompressionFamily.moment,
      LogSpectralCompressionFamily.subproduct, Finset.prod_singleton] using
      F.product_moments_le Sigma hSigma hn hrank J

theorem theorem_5_1_monotone_pair_target : Theorem51MonotonePairTarget := by
  intro p q k n c d Sigma Q M f g hSigma hn hQ hM hc hd hf0 hg0 hf hg hIf hIg hIjoint
  exact theorem_5_1_monotone_pair hSigma hn Q hQ M hM hc hd f g hf0 hg0 hf hg hIf hIg hIjoint

theorem theorem_5_2_monotone_pair_target : Theorem52MonotonePairTarget := by
  intro p q k n c d Sigma Q M Φ Ψ f g hSigma hn hQ hM hc hd hf0 hg0 hf hg hIf hIg hIjoint
  exact theorem_5_2_monotone_pair hSigma hn Q hQ Φ hc M hM Ψ hd f g hf hg hf0 hg0 hIf hIg hIjoint

theorem theorem_5_1_principal_target : Theorem51PrincipalTarget := by
  intro p d n Sigma I c f hSigma hn hdisjoint hc hf
  exact ⟨fun J i hi => theorem_5_1_disjoint_principal_selected_split_allow_empty
      hSigma hn I hdisjoint c hc f hf J i hi,
    fun J => theorem_5_1_disjoint_principal_product_allow_empty
      hSigma hn I hdisjoint c hc f hf J⟩

theorem theorem_5_2_principal_target : Theorem52PrincipalTarget := by
  intro p d n Sigma I Φ c f hSigma hn hI hdisjoint hc hf
  exact ⟨fun J i hi => theorem_5_2_disjoint_principal_selected_split
      hSigma hn I hI hdisjoint Φ c hc f hf J i hi,
    fun J => theorem_5_2_disjoint_principal_product hSigma hn I hI hdisjoint Φ c hc f hf J⟩

theorem theorem_5_3_principal_target : Theorem53PrincipalTarget := by
  intro p d n Sigma I c h hSigma hn hI hdisjoint hrange hc hh
  exact ⟨fun J i hi => theorem_5_3_disjoint_principal_selected_split
      hSigma hn I hI hdisjoint hrange c hc h hh J i hi,
    fun J => theorem_5_3_disjoint_principal_product hSigma hn I hI hdisjoint hrange c hc h hh J⟩

theorem corollary_5_4_product_target : Corollary54ProductTarget := by
  intro p d n Sigma F hn hSigma hrank J
  simpa only [productExtendedBound, GramGeometricCompressionFamily.moment,
    GramGeometricCompressionFamily.subproduct, Finset.prod_singleton] using
    F.product_moments_le Sigma n hSigma hrank J

theorem corollary_5_4_monotone_pair_target : Corollary54MonotonePairTarget := by
  intro p q k n c d Sigma Q M f g hn hSigma hQ hM hc hd hf0 hg0 hf hg hIf hIg hIjoint
  exact corollary_5_4_monotone_pair n hSigma Q hQ M hM hc hd f g hf0 hg0 hf hg hIf hIg hIjoint

theorem corollary_5_4_power_target : Corollary54PowerTarget := by
  intro p d n Sigma k B c ν hn hSigma hB hc hν
  exact corollary_5_4_power_moments n Sigma k B c ν hν

theorem theorem_5_1_complete :
    Theorem51GeometricTarget ∧ Theorem51MonotonePairTarget ∧ Theorem51PrincipalTarget :=
  ⟨theorem_5_1_geometric_target, theorem_5_1_monotone_pair_target, theorem_5_1_principal_target⟩

theorem theorem_5_2_complete :
    Theorem52GeometricTarget ∧ Theorem52MonotonePairTarget ∧ Theorem52PrincipalTarget :=
  ⟨theorem_5_2_geometric_target, theorem_5_2_monotone_pair_target, theorem_5_2_principal_target⟩

theorem theorem_5_3_complete : Theorem53SpectralTarget ∧ Theorem53PrincipalTarget :=
  ⟨theorem_5_3_spectral_target, theorem_5_3_principal_target⟩

theorem corollary_5_4_complete :
    Corollary54ProductTarget ∧ Corollary54MonotonePairTarget ∧ Corollary54PowerTarget :=
  ⟨corollary_5_4_product_target, corollary_5_4_monotone_pair_target, corollary_5_4_power_target⟩

theorem real_section_five : RealSectionFiveTarget where
  determinant := theorem_5_1_geometric_target
  determinantPair := theorem_5_1_monotone_pair_target
  determinantPrincipal := theorem_5_1_principal_target
  gauge := theorem_5_2_geometric_target
  gaugePair := theorem_5_2_monotone_pair_target
  gaugePrincipal := theorem_5_2_principal_target
  logarithmicSpectral := theorem_5_3_spectral_target
  logarithmicSpectralPrincipal := theorem_5_3_principal_target
  singularGram := corollary_5_4_product_target
  singularGramPair := corollary_5_4_monotone_pair_target
  singularGramPowers := corollary_5_4_power_target

end Wishart
end
end CanonicalSource6
