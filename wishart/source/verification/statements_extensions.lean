module

public import wishart.verified.real_tail01

@[expose] public section

noncomputable section
open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification Wishart Wishart.Spectral
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace WishartAudit

/- Literal independently reviewed paper targets. No theorem-type reflection is used. -/

def ProportionalShiftStatement : Prop :=
  ∀ {p d : ℕ} (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i),
    (∀ J, Integrable (shiftedMomentIntegrand Sigma P c ν J)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧
    ∀ j : Fin d,
      shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j) ≤
        shiftedMoment α Sigma P c ν Finset.univ ∧
      (∏ i : Fin d, shiftedMoment α Sigma P c ν {i}) ≤
        shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j)

theorem proportional_shift_exact : ProportionalShiftStatement :=
  @WishartVerification.proportional_shift_product_inequalities

def ExponentMonotonicityStatement : Prop :=
  ∀ {p d : ℕ} (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i),
    MonotoneOn (shiftedMomentRatio α Sigma P c) (Set.Ici (0 : Fin d → ℝ)) ∧
    ∀ (ν : Fin d → ℝ), (∀ i, 0 ≤ ν i) → ∀ j : Fin d,
      IncreasingExpectationLE (orderedChamber (Set.Ioi 0))
        ((shiftedTiltLaw α Sigma P c ν {j}).map (selectedEigenvalues Sigma P j))
        ((shiftedTiltLaw α Sigma P c ν Finset.univ).map (selectedEigenvalues Sigma P j))

theorem exponent_monotonicity_exact : ExponentMonotonicityStatement :=
  @WishartVerification.proposition_4_1

def InverseAssociationStatement : Prop :=
  ∀ {p d : ℕ} {β : ℝ}
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
      (inverseWishartMeasure β Omega)),
    (∏ i, inverseCompressionMoment β Omega k B Φ {i}) ≤
      inverseCompressionMoment β Omega k B Φ Finset.univ ∧
    ∀ j : Fin d,
      (∏ i, inverseCompressionMoment β Omega k B Φ {i}) ≤
        inverseCompressionMoment β Omega k B Φ {j} *
          inverseCompressionMoment β Omega k B Φ (Finset.univ.erase j) ∧
      inverseCompressionMoment β Omega k B Φ {j} *
          inverseCompressionMoment β Omega k B Φ (Finset.univ.erase j) ≤
        inverseCompressionMoment β Omega k B Φ Finset.univ

theorem inverse_association_exact : InverseAssociationStatement := @Wishart.theorem_6_1

def InverseDomainAssociationStatement : Prop :=
  ∀ {p d : ℕ} {β : ℝ}
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
      (inverseWishartMeasure β Omega)),
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
          ∂inverseWishartMeasure β Omega)

theorem inverse_domain_association_exact : InverseDomainAssociationStatement :=
  @Wishart.theorem_6_1_on_positiveOrderedSpectrum

end WishartAudit
