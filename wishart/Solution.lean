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
