module
public import WishartLiteralPrimitivesSourceBridge
public import wishart_main
public import WishartValuePreservation
import all wishart.verified.real_remainder07
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
@[expose] public section
noncomputable section
namespace Wishart.SpectralGauge
attribute [local instance] gaugeSymmetricSeminormedAddCommGroup gaugeSymmetricInnerProductSpace
/-- Whole-record specification of the actual source gauge seminorm. -/
theorem gaugeSeminormed_value {k : ℕ} :
    @gaugeSymmetricSeminormedAddCommGroup k =
      (TauCeti.symmetricMatrixNormedAddCommGroup k).toSeminormedAddCommGroup := by rfl
/-- Whole-record specification of the actual source gauge inner product. -/
theorem gaugeInner_value {k : ℕ} :
    @gaugeSymmetricInnerProductSpace k = TauCeti.symmetricMatrixInnerProductSpace k := by rfl
end Wishart.SpectralGauge

#print equations Wishart.QuaternionMatrix.complexRepresentation
#print equations Wishart.QuaternionMatrix.positiveDeterminant
#print equations Wishart.QuaternionMatrix.sqrt
#print equations Wishart.QuaternionMatrix.PosDef
#print equations Wishart.QuaternionSpectralFamily.shiftedCompression
#print equations Wishart.QuaternionMatrix.normalizedCompression
#print equations Wishart.QuaternionMatrix.flatHermitian
#print equations Wishart.QuaternionMatrix.flatRepresentation
#print equations Wishart.matrixBetaIIMeasure
#print equations Wishart.matrixBetaIIPDF
#print equations Wishart.matrixBetaIIPDFReal
#print equations Wishart.matrixBetaIIConstant
#print equations Wishart.inverseDeterminantMoment
#print equations Wishart.Corollary54PowerTarget
#print equations Wishart.Corollary54MonotonePairTarget
#print equations Wishart.Corollary54ProductTarget
#print equations Wishart.GramGeometricCompressionFamily.activeProper
#print equations Wishart.GramGeometricCompressionFamily.AEConstantFactor
#print equations Wishart.Theorem52PrincipalTarget
#print equations Wishart.Theorem52MonotonePairTarget
#print equations Wishart.Theorem51PrincipalTarget
#print equations Wishart.Theorem51MonotonePairTarget
#print equations WishartVerification.shiftedTiltLaw
#print equations WishartVerification.shiftedMomentRatio
#print equations WishartVerification.shiftedMoment
#print equations WishartVerification.PrincipalTheorem
#print equations WishartVerification.principalMoment

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification WishartVerification.MomentAssembly Wishart.Spectral
open scoped RealInnerProductSpace Quaternion BigOperators
namespace WishartVerification section open scoped BigOperators Matrix
theorem principalMoment_formula {p d:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (ν:Fin d → ℝ) (J:Finset (Fin d)) : principalMoment α Sigma P ν J = (∫ X,principalMomentIntegrand P ν J X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma) := by rfl
end end WishartVerification
namespace WishartVerification section open scoped BigOperators Matrix
theorem PrincipalTheorem_formula : PrincipalTheorem  = (∀ (p d:ℕ) (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (ν:Fin d → ℝ),0 < p → 0 < d → (p:ℝ) - 1 < α → Sigma.PosDef → (∀ i,0 ≤ ν i) → (∀ J:Finset (Fin d),Integrable (principalMomentIntegrand P ν J) (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧ (∀ j:Fin d,principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (Finset.univ.erase j) ≤ principalMoment α Sigma P ν Finset.univ ∧ (∏ i:Fin d,principalMoment α Sigma P ν {i}) ≤ principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (Finset.univ.erase j)) ∧ ((principalMoment α Sigma P ν Finset.univ=∏ i:Fin d,principalMoment α Sigma P ν {i}) ↔ independentActiveScaleBlocks Sigma P ν)) := by rfl
end end WishartVerification
namespace WishartVerification section open scoped Classical variable {p d:ℕ}
theorem shiftedMoment_formula (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (c ν:Fin d → ℝ) (J:Finset (Fin d)) : shiftedMoment α Sigma P c ν J = (∫ X,shiftedMomentIntegrand Sigma P c ν J X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma) := by rfl
end end WishartVerification
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem inverseDeterminantMoment_formula {p d:ℕ} (β:ℝ) (Omega:Matrix (Fin p) (Fin p) ℝ) (k:Fin d → ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (c ν:Fin d → ℝ) (J:Finset (Fin d)) : inverseDeterminantMoment β Omega k B c ν J = (∫ Y,inverseDeterminantProduct Omega k B c ν J Y ∂inverseWishartMeasure β Omega) := by rfl
end end Wishart
namespace Wishart.GramGeometricCompressionFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p:ℕ} {ι:Type*} [DecidableEq ι] variable (F:GramGeometricCompressionFamily p ι) (Sigma:Matrix (Fin p) (Fin p) ℝ)
omit [DecidableEq ι] in
theorem AEConstantFactor_formula (n:ℕ) (i:ι) : AEConstantFactor F Sigma n i = (∃ c:ℝ,∀ᵐ X ∂wishartGramMeasure n Sigma,F.factor Sigma i X=c) := by rfl
end end Wishart.GramGeometricCompressionFamily
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem matrixBetaIIMeasure_formula {p:ℕ} (α β:ℝ) (Omega:Matrix (Fin p) (Fin p) ℝ) : matrixBetaIIMeasure α β Omega = ((symmetricLebesgue p).withDensity (matrixBetaIIPDF α β Omega)) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Theorem51MonotonePairTarget_formula : Theorem51MonotonePairTarget  = (∀ (p q k:ℕ) (n c d:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (Q:Matrix (Fin p) (Fin q) ℝ) (M:Matrix (Fin p) (Fin k) ℝ) (f g:ℝ → ℝ),Sigma.PosDef → (p:ℝ) - 1 < n → Q.rank=q → M.rank=k → 0 ≤ c → 0 ≤ d → (∀ t ∈ Set.Ioi (0:ℝ),0 ≤ f t) → (∀ t ∈ Set.Ioi (0:ℝ),0 ≤ g t) → MonotoneOn f (Set.Ioi 0) → MonotoneOn g (Set.Ioi 0) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) * g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma) → realPairBound (nonsingularWishartMeasure n Sigma) (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (fun X => g (shiftedCompressionDeterminant Sigma M d X))) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Theorem52MonotonePairTarget_formula : Theorem52MonotonePairTarget  = (∀ (p q k:ℕ) (n c d:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (Q:Matrix (Fin p) (Fin q) ℝ) (M:Matrix (Fin p) (Fin k) ℝ) (Φ:SpectralGauge q) (Ψ:SpectralGauge k) (f g:ℝ → ℝ),Sigma.PosDef → (p:ℝ) - 1 < n → Q.rank=q → M.rank=k → 0 ≤ c → 0 ≤ d → (∀ t ∈ Set.Ioi (0:ℝ),0 ≤ f t) → (∀ t ∈ Set.Ioi (0:ℝ),0 ≤ g t) → MonotoneOn f (Set.Ioi 0) → MonotoneOn g (Set.Ioi 0) → Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X) * g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma) → realPairBound (nonsingularWishartMeasure n Sigma) (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) (fun X => g (normalizedGaugeValue Sigma M Ψ d X))) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Theorem51PrincipalTarget_formula : Theorem51PrincipalTarget  = (∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d → Finset (Fin p)) (c:Fin d → ℝ) (f:Fin d → ℝ → ℝ),Sigma.PosDef → (p:ℝ) - 1 < n → Pairwise (fun i j => Disjoint (I i) (I j)) → (∀ i,0 ≤ c i) → (∀ i,GeometricallyLogConvex (f i)) → (∀ J,∀ i ∈ J,selectedExtendedBound (nonsingularWishartMeasure n Sigma) (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J i) ∧ (∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J)) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Theorem52PrincipalTarget_formula : Theorem52PrincipalTarget  = (∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d → Finset (Fin p)) (Φ:∀ i,SpectralGauge (Fintype.card (I i))) (c:Fin d → ℝ) (f:Fin d → ℝ → ℝ),Sigma.PosDef → (p:ℝ) - 1 < n → (∀ i,(I i).Nonempty) → Pairwise (fun i j => Disjoint (I i) (I j)) → (∀ i,0 ≤ c i) → (∀ i,GeometricallyLogConvex (f i)) → (∀ J,∀ i ∈ J,selectedExtendedBound (nonsingularWishartMeasure n Sigma) (principalGaugeFactor Sigma I Φ c f) J i) ∧ (∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (principalGaugeFactor Sigma I Φ c f) J)) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Corollary54ProductTarget_formula : Corollary54ProductTarget  = (∀ (p d n:ℕ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (F:GramGeometricCompressionFamily p (Fin d)),1 ≤ n → Sigma.PosDef → gramOrderedRankThreshold F.size (F.activeProper Sigma n) n → ∀ J,productExtendedBound (wishartGramMeasure n Sigma) (F.factor Sigma) J) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Corollary54MonotonePairTarget_formula : Corollary54MonotonePairTarget  = (∀ (p q k n:ℕ) (c d:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (Q:Matrix (Fin p) (Fin q) ℝ) (M:Matrix (Fin p) (Fin k) ℝ) (f g:ℝ → ℝ),1 ≤ n → Sigma.PosDef → Q.rank=q → M.rank=k → 0 ≤ c → 0 ≤ d → (∀ t ∈ Set.Ici (0:ℝ),0 ≤ f t) → (∀ t ∈ Set.Ici (0:ℝ),0 ≤ g t) → MonotoneOn f (Set.Ici 0) → MonotoneOn g (Set.Ici 0) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (wishartGramMeasure n Sigma) → Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X)) (wishartGramMeasure n Sigma) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) * g (shiftedCompressionDeterminant Sigma M d X)) (wishartGramMeasure n Sigma) → realPairBound (wishartGramMeasure n Sigma) (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (fun X => g (shiftedCompressionDeterminant Sigma M d X))) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Corollary54PowerTarget_formula : Corollary54PowerTarget  = (∀ (p d n:ℕ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (k:Fin d → ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (c ν:Fin d → ℝ),1 ≤ n → Sigma.PosDef → (∀ i,(B i).rank=k i) → (∀ i,0 ≤ c i) → (∀ i,0 ≤ ν i) → HasAllFiniteMoments (fun X:SymmetricMatrix p => ∏ i,shiftedCompressionDeterminant Sigma (B i) (c i) X ^ ν i) (wishartGramMeasure n Sigma)) := by rfl
end end Wishart

namespace Wishart.Spectral section open scoped ENNReal
theorem coordinateSpectrum_formula {p:ℕ} (S:Sym p) : coordinateSpectrum S = ((selfAdjoint.isHermitian_coe S).eigenvalues) := by rfl
end end Wishart.Spectral
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
theorem normalizedCompression_formula {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin q) ℝ) : normalizedCompression Sigma B = (Matrix.symmetricCongruenceLinearMap (normalizedCompressionRows Sigma B)) := by rfl
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
theorem Theorem53PrincipalTarget_formula : Theorem53PrincipalTarget = (∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d → Finset (Fin p)) (c:Fin d → ℝ) (h:∀ i,(Fin (Fintype.card (I i)) → ℝ) → ℝ),Sigma.PosDef → (p:ℝ) - 1 < n → (∀ i,(I i).Nonempty) → Pairwise (fun i j => Disjoint (I i) (I j)) → (3 ≤ d ∨ (p:ℝ) ≤ n) → (∀ i,0 ≤ c i) → (∀ i,FiniteConvexIncreasingSymmetric (h i)) → (∀ J,∀ i ∈ J,selectedExtendedBound (nonsingularWishartMeasure n Sigma) (principalLogSpectralFactor Sigma I c h) J i) ∧ (∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (principalLogSpectralFactor Sigma I c h) J)) := by rfl
end end Wishart

#print equations Wishart.SpectralGauge.supportSet
#print equations Wishart.normalizedSelectedMatrix
section
attribute [local instance 4100] Matrix.instStarModule
theorem TauCeti.symmetricMatrixContinuousENorm_formula (p : ℕ) :
    TauCeti.symmetricMatrixContinuousENorm p = ESeminormedAddMonoid.toContinuousENorm := by
  rfl
end
