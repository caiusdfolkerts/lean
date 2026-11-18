module
public import Mathlib
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Analysis.Calculus.FDeriv.Det
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic
public import TauCeti.Analysis.Matrix.Eigenvalues
public import TauCeti.Analysis.Matrix.FunctionalCalculus
public import TauCeti.LinearAlgebra.Matrix.Alternating
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Moments
public import TauCeti.Probability.Distributions.NoncentralChiSquared.StochasticOrder
public import TauCeti.Probability.Distributions.Wishart.Agreement
public import TauCeti.Probability.Distributions.Wishart.Inverse.Measurability
public import TauCeti.Probability.Distributions.Wishart.Inverse.Moments
public import TauCeti.Probability.Distributions.Wishart.LowDimension
public import TauCeti.Probability.Distributions.Wishart.Marginal
public import TauCeti.Probability.Distributions.Wishart.Moments
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric
public import TauCeti.Topology.Algebra.UnitaryGroup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
namespace Wishart.Spectral end Wishart.Spectral
namespace WishartVerification.MomentAssembly end WishartVerification.MomentAssembly
namespace WishartVerification end WishartVerification
open Filter Function Matrix MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Set.powersetCard TauCeti TauCeti.Probability Topology Wishart.Spectral WishartVerification WishartVerification.MomentAssembly
open scoped Quaternion BigOperators
namespace Wishart.QuaternionMatrix
/-- Real scalar multiplication commutes with quaternion conjugation. -/
instance quaternionRealStarModule : StarModule ℝ ℍ[ℝ] where
  star_smul r q := by
    simpa only [star_trivial] using Quaternion.star_smul r q
/-- The ordinary Borel measurable structure on real quaternion space. -/
instance quaternionMeasurableSpace : MeasurableSpace ℍ[ℝ] := borel _
instance quaternionBorelSpace : BorelSpace ℍ[ℝ] := ⟨rfl⟩
end Wishart.QuaternionMatrix
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
/-- Exact source definition of SymmetricMatrix. -/
abbrev SymmetricMatrix (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- Exact source definition of principalSymmetricBlock. -/
def principalSymmetricBlock {p q : ℕ} (f : Fin q → Fin p) (X : SymmetricMatrix p) : SymmetricMatrix q := ⟨(X : Matrix (Fin p) (Fin p) ℝ).submatrix f f, Matrix.isHermitian_iff_isSelfAdjoint.mp ((Matrix.isHermitian_iff_isSelfAdjoint.mpr X.property).submatrix f)⟩
/-- Exact source definition of blockDiagonalMatrix. -/
def blockDiagonalMatrix {q m : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ := (Matrix.fromBlocks A 0 0 C).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
/-- Exact source definition of leadingScale. -/
def leadingScale (q m : ℕ) (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) : Matrix (Fin q) (Fin q) ℝ := S.submatrix (Fin.castAdd m) (Fin.castAdd m)
/-- Exact source definition of selectedInverseRoot. -/
def selectedInverseRoot (q m : ℕ) (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) : Matrix (Fin q) (Fin q) ℝ := (CFC.sqrt (leadingScale q m S))⁻¹
/-- Exact source definition of selectedWhitening. -/
def selectedWhitening (q m : ℕ) (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ := blockDiagonalMatrix (selectedInverseRoot q m S) (1 : Matrix (Fin m) (Fin m) ℝ)
end end Wishart
namespace WishartVerification section open scoped BigOperators Matrix
/-- Exact source definition of SymmetricMatrix. -/
abbrev SymmetricMatrix (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- A partition into labelled nonempty principal blocks. -/
structure PrincipalPartition (p d : ℕ) where
  block : Fin d → Finset (Fin p)
  nonempty : ∀ i, (block i).Nonempty
  unique_block : ∀ x : Fin p, ∃! i : Fin d, x ∈ block i
/-- Exact source definition of principalMinor. -/
def principalMinor {p : ℕ} (I : Finset (Fin p)) (X : SymmetricMatrix p) : ℝ := ((X : Matrix (Fin p) (Fin p) ℝ).submatrix (fun i : I => (i : Fin p)) (fun i : I => (i : Fin p))).det
/-- Exact source definition of principalMomentIntegrand. -/
def principalMomentIntegrand {p d : ℕ} (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d)) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, (principalMinor (P.block i) X) ^ (ν i)
/-- Exact source definition of principalMoment. -/
def principalMoment {p d : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d)) : ℝ := ∫ X, principalMomentIntegrand P ν J X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma
/-- Exact source definition of independentActiveScaleBlocks. -/
def independentActiveScaleBlocks {p d : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (ν : Fin d → ℝ) : Prop := ∀ i j : Fin d, i ≠ j → 0 < ν i → 0 < ν j → ∀ a ∈ P.block i, ∀ b ∈ P.block j, Sigma a b = 0
/-- The whole content of manuscript Theorem 1.1: arbitrary real shape in its full nonsingular range, all nonnegative real exponents, all selected splits, joint integrability, and the exact equality characterization. -/
def PrincipalTheorem : Prop := ∀ (p d : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (ν : Fin d → ℝ), 0 < p → 0 < d → (p : ℝ) - 1 < α → Sigma.PosDef → (∀ i, 0 ≤ ν i) → (∀ J : Finset (Fin d), Integrable (principalMomentIntegrand P ν J) (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧ (∀ j : Fin d, principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (Finset.univ.erase j) ≤ principalMoment α Sigma P ν Finset.univ ∧ (∏ i : Fin d, principalMoment α Sigma P ν {i}) ≤ principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (Finset.univ.erase j)) ∧ ((principalMoment α Sigma P ν Finset.univ = ∏ i : Fin d, principalMoment α Sigma P ν {i}) ↔ independentActiveScaleBlocks Sigma P ν)
end end WishartVerification
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
/-- Exact source definition of selectedDimension. -/
abbrev selectedDimension {p : ℕ} (I : Finset (Fin p)) : ℕ := Fintype.card I
/-- Exact source definition of complementDimension. -/
abbrev complementDimension {p : ℕ} (I : Finset (Fin p)) : ℕ := Fintype.card {a : Fin p // a ∉ I}
/-- Exact source definition of selectedCoordinatesEquiv. -/
def selectedCoordinatesEquiv {p : ℕ} (I : Finset (Fin p)) : Fin (selectedDimension I + complementDimension I) ≃ Fin p := finSumFinEquiv.symm.trans ((Equiv.sumCongr (Fintype.equivFin I).symm (Fintype.equivFin {a : Fin p // a ∉ I}).symm).trans (Equiv.sumCompl (fun a : Fin p => a ∈ I)))
/-- Exact source definition of normalizedSelectedMatrix. -/
def normalizedSelectedMatrix {p : ℕ} (I : Finset (Fin p)) (S : Matrix (Fin p) (Fin p) ℝ) (X : SymmetricMatrix p) : SymmetricMatrix (selectedDimension I + complementDimension I) := Matrix.symmetricCongruenceLinearMap (selectedWhitening (selectedDimension I) (complementDimension I) (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I))) (principalSymmetricBlock (selectedCoordinatesEquiv I) X)
end end Wishart
namespace WishartVerification section open scoped ENNReal variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
/-- Exact source definition of HasAllFiniteMoments. -/
def HasAllFiniteMoments (f : Ω → ℝ) (μ : Measure Ω) : Prop := ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ
end end WishartVerification
namespace WishartVerification section open scoped Classical Matrix variable {p d : ℕ}
/-- Exact source definition of selectedRank. -/
abbrev selectedRank (P : PrincipalPartition p d) (j : Fin d) : ℕ := Wishart.selectedDimension (P.block j)
/-- Exact source definition of remainingRank. -/
abbrev remainingRank (P : PrincipalPartition p d) (j : Fin d) : ℕ := Wishart.complementDimension (P.block j)
/-- Exact source definition of normalizedPrincipalMatrix. -/
abbrev normalizedPrincipalMatrix (P : PrincipalPartition p d) (Sigma : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) := Wishart.normalizedSelectedMatrix (P.block j) Sigma
end end WishartVerification
namespace Wishart.Spectral section open scoped ENNReal
/-- Exact source definition of Sym. -/
abbrev Sym (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- Exact source definition of coordinateSpectrum. -/
noncomputable def coordinateSpectrum {p : ℕ} (S : Sym p) : Fin p → ℝ := (selfAdjoint.isHermitian_coe S).eigenvalues
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical
/-- Exact source definition of ascendingIndexEquiv. -/
noncomputable def ascendingIndexEquiv (p : ℕ) : Equiv.Perm (Fin p) := Fin.revPerm.trans ((finCongr (Fintype.card_fin p).symm).trans (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p)))))
/-- Exact source definition of ascendingSpectrum. -/
noncomputable def ascendingSpectrum {p : ℕ} (S : Sym p) : Fin p → ℝ := coordinateSpectrum S ∘ ascendingIndexEquiv p
end end Wishart.Spectral
namespace WishartVerification section open scoped Classical ENNReal variable {ι : Type*} [Fintype ι] [LinearOrder ι]
/-- Exact source definition of orderedChamber. -/
def orderedChamber (s : Set ℝ) : Set (ι → ℝ) := {x | StrictMono x ∧ ∀ i, x i ∈ s}
end end WishartVerification
namespace WishartVerification section open scoped Classical ENNReal variable {ι : Type*} [Fintype ι] [LinearOrder ι] variable {Ω : Type*} [MeasurableSpace Ω]
/-- Normalizing a nonnegative real density by its nonnegative integral. -/
noncomputable def normalizedWeight (μ : Measure Ω) (w : Ω → ℝ) : Measure Ω := (∫⁻ x, ENNReal.ofReal (w x) ∂μ)⁻¹ • μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
end end WishartVerification
namespace WishartVerification section open scoped Classical variable {p d : ℕ}
/-- Exact source definition of principalSetCoordinates. -/
def principalSetCoordinates (I : Finset (Fin p)) : Fin (Fintype.card I) → Fin p := fun a ↦ ((Fintype.equivFin I).symm a : Fin p)
/-- Exact source definition of principalSetMatrix. -/
def principalSetMatrix (I : Finset (Fin p)) : SymmetricMatrix p → SymmetricMatrix (Fintype.card I) := Wishart.principalSymmetricBlock (principalSetCoordinates I)
/-- Theorem 1.1, with all original quantifiers and parameter ranges, joint moment finiteness, every selected split, the product lower bound, and the exact active-block equality characterization. -/
theorem theorem_1_1 : PrincipalTheorem := by sorry
end end WishartVerification
namespace WishartVerification section open scoped Classical ENNReal variable {Ω : Type*} [MeasurableSpace Ω]
/-- Comparison against every bounded Borel increasing real-valued test. The order restriction is only on the common support set. -/
def IncreasingExpectationLE [Preorder Ω] (s : Set Ω) (μ ν : Measure Ω) : Prop := ∀ f : Ω → ℝ, Measurable f → MonotoneOn f s → (∃ M : ℝ, ∀ x, |f x| ≤ M) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν
end end WishartVerification
namespace WishartVerification section open scoped Classical variable {p d : ℕ}
/-- Exact source definition of shiftedPrincipalMinor. -/
def shiftedPrincipalMinor (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) (c : ℝ) (X : SymmetricMatrix p) : ℝ := (((X : Matrix (Fin p) (Fin p) ℝ).submatrix (fun i : I ↦ (i : Fin p)) (fun i : I ↦ (i : Fin p))) + c • Sigma.submatrix (fun i : I ↦ (i : Fin p)) (fun i : I ↦ (i : Fin p))).det
/-- Exact source definition of shiftedMomentIntegrand. -/
def shiftedMomentIntegrand (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, shiftedPrincipalMinor Sigma (P.block i) (c i) X ^ ν i
/-- Exact source definition of shiftedMoment. -/
def shiftedMoment (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) : ℝ := ∫ X, shiftedMomentIntegrand Sigma P c ν J X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma
/-- Exact source definition of shiftedMomentRatio. -/
def shiftedMomentRatio (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (c ν : Fin d → ℝ) : ℝ := shiftedMoment α Sigma P c ν Finset.univ / ∏ i : Fin d, shiftedMoment α Sigma P c ν {i}
/-- Exact source definition of shiftedTiltLaw. -/
def shiftedTiltLaw (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) : Measure (SymmetricMatrix p) := normalizedWeight (TauCeti.Probability.nonsingularWishartMeasure α Sigma) (shiftedMomentIntegrand Sigma P c ν J)
/-- Exact source definition of selectedEigenvalues. -/
def selectedEigenvalues (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d) (j : Fin d) (X : SymmetricMatrix p) : Fin (selectedRank P j) → ℝ := Wishart.Spectral.ascendingSpectrum (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j)) (normalizedPrincipalMatrix P Sigma j X))
end end WishartVerification
namespace WishartVerification section open scoped Classical Matrix variable {p d : ℕ}
/-- Section 4.1: both inequalities with arbitrary proportional nonnegative shifts, with the original real shape and all nonnegative real powers. -/
theorem proportional_shift_product_inequalities (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) : (∀ J, Integrable (shiftedMomentIntegrand Sigma P c ν J) (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧ ∀ j : Fin d, shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j) ≤ shiftedMoment α Sigma P c ν Finset.univ ∧ (∏ i : Fin d, shiftedMoment α Sigma P c ν {i}) ≤ shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j) := by sorry
end end WishartVerification
namespace WishartVerification section open scoped Classical variable {p d : ℕ}
/-- Proposition 4.1 in full: the normalized determinant-product ratio is increasing in every exponent, and the full determinant tilt stochastically dominates the single-factor tilt on the entire ordered selected spectrum. -/
theorem proposition_4_1 (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) : MonotoneOn (shiftedMomentRatio α Sigma P c) (Set.Ici (0 : Fin d → ℝ)) ∧ ∀ (ν : Fin d → ℝ), (∀ i, 0 ≤ ν i) → ∀ j : Fin d, IncreasingExpectationLE (orderedChamber (Set.Ioi 0)) ((shiftedTiltLaw α Sigma P c ν {j}).map (selectedEigenvalues Sigma P j)) ((shiftedTiltLaw α Sigma P c ν Finset.univ).map (selectedEigenvalues Sigma P j)) := by sorry
end end WishartVerification
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
/-- Exact source definition of compressionScale. -/
def compressionScale {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ := Bᵀ * Sigma * B
/-- Exact source definition of normalizedCompressionRows. -/
def normalizedCompressionRows {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) : Matrix (Fin q) (Fin p) ℝ := (CFC.sqrt (compressionScale Sigma B))⁻¹ * Bᵀ
/-- Exact source definition of normalizedCompression. -/
def normalizedCompression {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) : SymmetricMatrix p → SymmetricMatrix q := Matrix.symmetricCongruenceLinearMap (normalizedCompressionRows Sigma B)
/-- Exact source definition of normalizedCompression_posDef. -/
theorem normalizedCompression_posDef {p k : ℕ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) {Y : SymmetricMatrix p} (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef) : (normalizedCompression Omega B Y : Matrix (Fin k) (Fin k) ℝ).PosDef := by sorry
end end Wishart
namespace Wishart.Spectral section open scoped Classical MatrixOrder Matrix.Norms.L2Operator
/-- Exact source definition of positiveOrderedSpectrum. -/
def positiveOrderedSpectrum (p : ℕ) : Set (Fin p → ℝ) := {lam | Monotone lam ∧ ∀ i, 0 < lam i}
/-- Exact source definition of ascendingSpectrum_mem_positiveOrderedSpectrum. -/
theorem ascendingSpectrum_mem_positiveOrderedSpectrum {p : ℕ} (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) : ascendingSpectrum S ∈ positiveOrderedSpectrum p := by sorry
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- Exact source definition of PositiveSpectrum. -/
abbrev PositiveSpectrum (p : ℕ) := {lam : Fin p → ℝ // lam ∈ positiveOrderedSpectrum p}
end end Wishart.Spectral
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The original domain-valued test at an actual positive compression; its arbitrary value off the positive matrix cone is fixed to zero. -/
def domainInverseCompressionFactor {p k : ℕ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (f : PositiveSpectrum k → ℝ) (Y : SymmetricMatrix p) : ℝ := if hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef then f ⟨ascendingSpectrum (normalizedCompression Omega B Y), ascendingSpectrum_mem_positiveOrderedSpectrum _ (normalizedCompression_posDef hOmega B hB hY)⟩ else 0
/-- Exact source definition of domainInverseCompressionProduct. -/
def domainInverseCompressionProduct {p d : ℕ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i) (f : ∀ i, PositiveSpectrum (k i) → ℝ) (J : Finset (Fin d)) (Y : SymmetricMatrix p) : ℝ := ∏ i ∈ J, domainInverseCompressionFactor hOmega (B i) (hB i) (f i) Y
/-- The full finite-expectation chain of Theorem6.1 for functions whose domain is literally only the ordered positive spectrum. No extension hypothesis is imposed on the user-supplied functions. -/
theorem theorem_6_1_on_positiveOrderedSpectrum {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i) (f : ∀ i, PositiveSpectrum (k i) → ℝ) (hfm : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x) (hdir : (∀ i, Monotone (f i)) ∨ (∀ i, Antitone (f i))) (hIsingle : ∀ i, Integrable (domainInverseCompressionFactor hOmega (B i) (hB i) (f i)) (inverseWishartMeasure β Omega)) (hIremaining : ∀ j, Integrable (domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j)) (inverseWishartMeasure β Omega)) (hIjoint : Integrable (domainInverseCompressionProduct hOmega k B hB f Finset.univ) (inverseWishartMeasure β Omega)) : (∏ i, ∫ Y, domainInverseCompressionProduct hOmega k B hB f {i} Y ∂inverseWishartMeasure β Omega) ≤ (∫ Y, domainInverseCompressionProduct hOmega k B hB f Finset.univ Y ∂inverseWishartMeasure β Omega) ∧ ∀ j : Fin d, (∏ i, ∫ Y, domainInverseCompressionProduct hOmega k B hB f {i} Y ∂inverseWishartMeasure β Omega) ≤ (∫ Y, domainInverseCompressionProduct hOmega k B hB f {j} Y ∂inverseWishartMeasure β Omega) * (∫ Y, domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j) Y ∂inverseWishartMeasure β Omega) ∧ (∫ Y, domainInverseCompressionProduct hOmega k B hB f {j} Y ∂inverseWishartMeasure β Omega) * (∫ Y, domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j) Y ∂inverseWishartMeasure β Omega) ≤ (∫ Y, domainInverseCompressionProduct hOmega k B hB f Finset.univ Y ∂inverseWishartMeasure β Omega) := by sorry
/-- Exact source definition of inverseCompressionDeterminant. -/
def inverseCompressionDeterminant {p k : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ) (c : ℝ) (Y : SymmetricMatrix p) : ℝ := (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B + c • compressionScale S B).det
/-- Exact source definition of inverseDeterminantProduct. -/
def inverseDeterminantProduct {p d : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ) (J : Finset (Fin d)) (Y : SymmetricMatrix p) : ℝ := ∏ i ∈ J, inverseCompressionDeterminant S (B i) (c i) Y ^ ν i
/-- Exact source definition of inverseDeterminantMoment. -/
def inverseDeterminantMoment {p d : ℕ} (β : ℝ) (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ) (J : Finset (Fin d)) : ℝ := ∫ Y, inverseDeterminantProduct Omega k B c ν J Y ∂inverseWishartMeasure β Omega
end end Wishart
namespace WishartVerification section open scoped BigOperators variable {ι : Type*} [Fintype ι] [Nonempty ι]
/-- Exact source definition of finiteMaximum. -/
def finiteMaximum (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x
end end WishartVerification
namespace WishartVerification section 
/-- The paper's condition on a positive outer function, on its actual domain `(0,∞)`. Values at nonpositive arguments do not enter this definition. -/
structure GeometricallyLogConvex (f : ℝ → ℝ) : Prop where
  positive : ∀ x, 0 < x → 0 < f x
  convex_log : ConvexOn ℝ Set.univ (fun s => Real.log (f (Real.exp s)))
  monotone_log : Monotone (fun s => Real.log (f (Real.exp s)))
end end WishartVerification
namespace Wishart.QuaternionMatrix section open scoped Matrix Quaternion BigOperators Classical ComplexOrder
/-- Exact source definition of Hermitian. -/
abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℍ[ℝ])
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Matrix Quaternion BigOperators Classical ComplexOrder variable {m n k : Type*}
/-- The standard real-algebra representation, with each quaternion replaced by its two-by-two complex matrix. This also applies to rectangular matrices. -/
def complexRepresentation (A : Matrix m n ℍ[ℝ]) : Matrix (m × Fin 2) (n × Fin 2) ℂ := Matrix.comp m n (Fin 2) (Fin 2) ℂ (A.map Quaternion.toComplexMatrix)
/-- Exact source definition of isHermitian_complexRepresentation_iff. -/
theorem isHermitian_complexRepresentation_iff (A : Matrix n n ℍ[ℝ]) : (complexRepresentation A).IsHermitian ↔ A.IsHermitian := by sorry
/-- Positive definiteness on the quaternion Hermitian space. -/
def PosDef [Fintype n] (A : Matrix n n ℍ[ℝ]) : Prop := (complexRepresentation A).PosDef
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Matrix Quaternion ComplexOrder BigOperators Classical Ring variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The positive square root of the complex determinant. All uses as a quaternion determinant carry an explicit positive-semidefinite hypothesis. -/
def positiveDeterminant (A : Matrix n n ℍ[ℝ]) : ℝ := Real.sqrt (complexRepresentation A).det.re
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring variable {n : Type*} [Fintype n] [DecidableEq n]
/-- A continuous linear left inverse of the faithful representation, defined on the entire complex ambient space. -/
def representationLeftInverse :
    Matrix (n × Fin 2) (n × Fin 2) ℂ →ₗ[ℝ] Matrix n n ℍ[ℝ] where
  toFun A := Matrix.of fun i j =>
    ⟨(A (i,0) (j,0)).re, (A (i,0) (j,0)).im,
      -(A (i,1) (j,0)).re, (A (i,1) (j,0)).im⟩
  map_add' A B := by ext i j <;> simp [add_comm]
  map_smul' r A := by ext i j <;> simp [QuaternionAlgebra.smul_mk]
/-- Exact source definition of sqrt. -/
def sqrt (A : Matrix n n ℍ[ℝ]) : Matrix n n ℍ[ℝ] := representationLeftInverse (CFC.sqrt (complexRepresentation A))
end end Wishart.QuaternionMatrix
namespace Wishart.ComplexMatrix section open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace BigOperators Classical variable {n : Type*} [Fintype n] [DecidableEq n]
/-- Exact source definition of realDeterminant. -/
def realDeterminant (A : Matrix n n ℂ) : ℝ := A.det.re
end end Wishart.ComplexMatrix
namespace Wishart.FieldGaussian section open scoped Classical Matrix BigOperators Quaternion ENNReal variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [SMulCommClass ℝ F F] [IsScalarTower ℝ F F] [MeasurableSpace F] [BorelSpace F]
/-- Exact source definition of Row. -/
abbrev Row (m : ℕ) := PiLp 2 (fun _ : Fin m => F)
/-- Right multiplication by a genuinely arbitrary rectangular field matrix, viewed as a real continuous linear map. -/
def rowFactorLinearMap {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) :
    Row F r →ₗ[ℝ] Row F m where
  toFun z := WithLp.toLp 2 fun j => ∑ i, z i * R i j
  map_add' x y := by
    ext j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext j
    simp [smul_mul_assoc, Finset.smul_sum]
/-- Exact source definition of rowFactorCLM. -/
def rowFactorCLM {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) : Row F r →L[ℝ] Row F m := (rowFactorLinearMap F R).toContinuousLinearMap
/-- Exact source definition of standardDeviation. -/
def standardDeviation : ℝ := (Real.sqrt (Module.finrank ℝ F))⁻¹
/-- Exact source definition of normalizedRowFactorCLM. -/
def normalizedRowFactorCLM {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) : Row F r →L[ℝ] Row F m := standardDeviation F • rowFactorCLM F R
/-- The actual centered field Gaussian row with rectangular covariance factor `R`; for an identity factor each real component has variance `1 / dim ℝ F`. -/
def gaussianRowWithFactor {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) : Measure (Row F m) := (stdGaussian (Row F r)).map (normalizedRowFactorCLM F R)
end end Wishart.FieldGaussian
namespace Wishart.FieldGaussian section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [SMulCommClass ℝ F F] [IsScalarTower ℝ F F] [StarModule ℝ F] [MeasurableSpace F] [BorelSpace F]
/-- Exact source definition of Hermitian. -/
abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) F)
/-- Exact source definition of rowsMatrix. -/
def rowsMatrix {n p : ℕ} (z : Fin n → Row F p) : Matrix (Fin n) (Fin p) F := Matrix.of fun i j => z i j
/-- Exact source definition of rowsGram. -/
def rowsGram {n p : ℕ} (z : Fin n → Row F p) : Hermitian F p := ⟨(rowsMatrix F z)ᴴ * rowsMatrix F z, (Matrix.isHermitian_conjTranspose_mul_self (rowsMatrix F z)).isSelfAdjoint⟩
/-- Exact source definition of gramWithFactor. -/
def gramWithFactor {r p : ℕ} (n : ℕ) (R : Matrix (Fin r) (Fin p) F) : Measure (Hermitian F p) := (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F R)).map (rowsGram F)
end end Wishart.FieldGaussian
namespace Wishart.ComplexMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal
/-- Exact source definition of Hermitian. -/
abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)
/-- Exact source definition of hermitianLebesgue. -/
def hermitianLebesgue (p : ℕ) : Measure (Hermitian p) := (Module.finBasis ℝ (Hermitian p)).addHaar
/-- The unnormalized literal complex density (b = 2). -/
def wishartWeight {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ) (X : Hermitian p) : ℝ≥0∞ := if (X : Matrix (Fin p) (Fin p) ℂ).PosDef then ENNReal.ofReal (realDeterminant (X : Matrix (Fin p) (Fin p) ℂ) ^ (α - p) * Real.exp (-((Sigma⁻¹ * (X : Matrix (Fin p) (Fin p) ℂ)).trace).re)) else 0
/-- Exact source definition of wishartNormalizer. -/
def wishartNormalizer {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ) : ℝ≥0∞ := ∫⁻ X, wishartWeight α Sigma X ∂hermitianLebesgue p
/-- Exact source definition of wishartMeasure. -/
def wishartMeasure {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ) : Measure (Hermitian p) := (wishartNormalizer α Sigma)⁻¹ • (hermitianLebesgue p).withDensity (wishartWeight α Sigma)
/-- The genuine n-row field Gaussian Gram law, including singular sample sizes. -/
def gramMeasure {p : ℕ} (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℂ) : Measure (Hermitian p) := Wishart.FieldGaussian.gramWithFactor ℂ n (CFC.sqrt Sigma)
/-- Exact source definition of compressionCovariance. -/
def compressionCovariance {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℂ) (Sigma : Matrix (Fin p) (Fin p) ℂ) : Matrix (Fin k) (Fin k) ℂ := Bᴴ * Sigma * B
/-- The exact standardized compression. The congruence form makes the total function Hermitian even outside its intended positive-definite parameters. -/
def normalizedCompression {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℂ) (Sigma : Matrix (Fin p) (Fin p) ℂ) (X : Hermitian p) : Hermitian k :=
  let R := B * (CFC.sqrt (compressionCovariance B Sigma))⁻¹
  ⟨Rᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * R,
    (Matrix.isHermitian_conjTranspose_mul_mul R
      (show IsSelfAdjoint (X : Matrix (Fin p) (Fin p) ℂ) from X.property).isHermitian).isSelfAdjoint⟩
end end Wishart.ComplexMatrix
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal open scoped Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false in
local instance matrixBorelSpace (p q : ℕ) : BorelSpace (Matrix (Fin p) (Fin q) ℍ[ℝ]) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → ℍ[ℝ]))
set_option backward.isDefEq.respectTransparency false in
local instance hermitianBorelSpace (p : ℕ) : BorelSpace (Hermitian p) :=
  inferInstanceAs (BorelSpace {X : Matrix (Fin p) (Fin p) ℍ[ℝ] // X ∈ selfAdjoint.submodule ℝ _})
set_option backward.isDefEq.respectTransparency false in
/-- Exact source definition of hermitianLebesgue. -/
def hermitianLebesgue (p : ℕ) : Measure (Hermitian p) := (Module.finBasis ℝ (Hermitian p)).addHaar
/-- The unnormalized literal quaternion density (b = 4). -/
def wishartWeight {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (X : Hermitian p) : ℝ≥0∞ := if PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) then ENNReal.ofReal (positiveDeterminant (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (α - p + 1) - 1) * Real.exp (-2 * ((Sigma⁻¹ʳ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ])).trace).re)) else 0
/-- Exact source definition of wishartNormalizer. -/
def wishartNormalizer {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : ℝ≥0∞ := ∫⁻ X, wishartWeight α Sigma X ∂hermitianLebesgue p
/-- Exact source definition of wishartMeasure. -/
def wishartMeasure {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : Measure (Hermitian p) := (wishartNormalizer α Sigma)⁻¹ • (hermitianLebesgue p).withDensity (wishartWeight α Sigma)
/-- Exact source definition of gramMeasure. -/
def gramMeasure {p : ℕ} (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : Measure (Hermitian p) := Wishart.FieldGaussian.gramWithFactor ℍ[ℝ] n (sqrt Sigma)
/-- Exact source definition of compressionCovariance. -/
def compressionCovariance {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : Matrix (Fin k) (Fin k) ℍ[ℝ] := Bᴴ * Sigma * B
/-- Exact source definition of normalizedCompression. -/
def normalizedCompression {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (X : Hermitian p) : Hermitian k :=
  let R := B * (sqrt (compressionCovariance B Sigma))⁻¹ʳ
  ⟨Rᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * R,
    (Matrix.isHermitian_conjTranspose_mul_mul R
      (show IsSelfAdjoint (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) from X.property).isHermitian).isSelfAdjoint⟩
end end Wishart.QuaternionMatrix
namespace WishartVerification section 
/-- Exact source definition of hermitian_matrix_coe. -/
theorem hermitian_matrix_coe {F ι : Type*} [AddCommGroup F] [Module ℝ F] [StarAddMonoid F] [StarModule ℝ F] (X : selfAdjoint.submodule ℝ (Matrix ι ι F)) : (X : Matrix ι ι F).IsHermitian := by sorry
end end WishartVerification
namespace Wishart section open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Exact source definition of shiftedCompressionDeterminant. -/
def shiftedCompressionDeterminant {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ) (c : ℝ) (X : SymmetricMatrix p) : ℝ := (Qᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * Q + c • compressionScale Sigma Q).det
end end Wishart
namespace WishartVerification.MomentAssembly section open scoped Classical variable {ι : Type*} [DecidableEq ι]
/-- Exact source definition of descendingRankEquiv. -/
def descendingRankEquiv (rank : ι → ℕ) (A : Finset ι) : Fin (Fintype.card A) ≃ A := (Tuple.sortDesc (fun i => rank ((Fintype.equivFin A).symm i))).trans (Fintype.equivFin A).symm
/-- Exact source definition of descendingRanks. -/
def descendingRanks (rank : ι → ℕ) (A : Finset ι) : Fin (Fintype.card A) → ℕ := fun i => rank (descendingRankEquiv rank A i)
/-- The condition is vacuous when at most two active proper factors remain; otherwise it reads precisely `n ≥ min(k_(1)+k_(3), p+1)` in descending order. -/
def orderedRankThreshold (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) : Prop :=
  ∀ h : 3 ≤ Fintype.card A,
    min ((descendingRanks rank A ⟨0, by omega⟩ : ℝ) +
      descendingRanks rank A ⟨2, by omega⟩) ((p : ℝ) + 1) ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Exact source definition of GeometricCompressionFamily. -/
structure GeometricCompressionFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  outer : ι → ℝ → ℝ
  geometric : ∀ i, GeometricallyLogConvex (outer i)
end end Wishart
namespace Wishart.GeometricCompressionFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p : ℕ} {ι : Type*} [DecidableEq ι] variable (F : GeometricCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)
/-- Exact source definition of factor. -/
def factor (i : ι) (X : SymmetricMatrix p) : ℝ := F.outer i (shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i) X)
/-- Exact source definition of subproduct. -/
def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, F.factor Sigma i X
/-- Exact source definition of moment. -/
def moment (n : ℝ) (J : Finset ι) : ℝ≥0∞ := ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma
/-- Constancy is tested on the entire positive definite cone, the actual support of the nonsingular law. It is not a premise about an unknown conditional moment. -/
def ConstantFactor (i : ι) : Prop := ∃ c : ℝ, ∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosDef → F.factor Sigma i X = c
/-- Exact source definition of activeProper. -/
def activeProper [Fintype ι] : Finset ι := Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)
end end Wishart.GeometricCompressionFamily
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.Operator ENNReal
/-- Exact source definition of positiveSemidefiniteCone. -/
def positiveSemidefiniteCone (k : ℕ) : Set (SymmetricMatrix k) := {X | (X : Matrix (Fin k) (Fin k) ℝ).PosSemidef}
/-- A nonzero continuous convex homogeneous Loewner-increasing orthogonally invariant function on the positive semidefinite cone, precisely as defined in the manuscript. -/
structure SpectralGauge (k : ℕ) where
  toFun : SymmetricMatrix k → ℝ
  nonnegative : ∀ X ∈ positiveSemidefiniteCone k, 0 ≤ toFun X
  nonzero : ∃ X ∈ positiveSemidefiniteCone k, toFun X ≠ 0
  continuousOn : ContinuousOn toFun (positiveSemidefiniteCone k)
  convexOn : ConvexOn ℝ (positiveSemidefiniteCone k) toFun
  homogeneous : ∀ (a : ℝ), 0 ≤ a → ∀ X ∈ positiveSemidefiniteCone k,
    toFun (a • X) = a * toFun X
  loewner : ∀ X ∈ positiveSemidefiniteCone k, ∀ Y ∈ positiveSemidefiniteCone k,
    ((Y - X : SymmetricMatrix k) : Matrix (Fin k) (Fin k) ℝ).PosSemidef →
      toFun X ≤ toFun Y
  orthogonalInvariant : ∀ (U : Matrix.orthogonalGroup (Fin k) ℝ)
    (X : SymmetricMatrix k), X ∈ positiveSemidefiniteCone k →
    toFun (Matrix.symmetricCongruenceLinearMap (U : Matrix (Fin k) (Fin k) ℝ) X) =
      toFun X
instance {k : ℕ} : CoeFun (SpectralGauge k) (fun _ => SymmetricMatrix k → ℝ) := ⟨SpectralGauge.toFun⟩
end end Wishart
namespace Wishart.SpectralGauge section open scoped Matrix MatrixOrder Matrix.Norms.Operator RealInnerProductSpace InnerProductSpace variable {k : ℕ} (Φ : SpectralGauge k)
/-- Exact source definition of identitySymmetric. -/
def identitySymmetric (k : ℕ) : SymmetricMatrix k := ⟨1, Matrix.isHermitian_one.isSelfAdjoint⟩
/-- The canonical compact set of all positive linear trace minorants. -/
def supportSet : Set (SymmetricMatrix k) := {H | (H : Matrix (Fin k) (Fin k) ℝ).PosSemidef ∧ ∀ X ∈ positiveSemidefiniteCone k, ⟪H, X⟫_ℝ ≤ Φ X}
/-- A single countable family of positive trace minorants recovers the gauge at every PSD input. This supplies finite maxima for subsequent regularization. -/
theorem exists_countable_positive_support : ∃ H : ℕ → SymmetricMatrix k, (∀ n, H n ∈ Φ.supportSet) ∧ ∀ X ∈ positiveSemidefiniteCone k, (⨆ n, ⟪H n, X⟫_ℝ) = Φ X := by sorry
end end Wishart.SpectralGauge
namespace Wishart.SpectralGauge section open scoped Matrix MatrixOrder Matrix.Norms.Operator variable {k : ℕ} (Φ : SpectralGauge k)
/-- A measurable extension used only to express random variables on the whole ambient measurable space. It equals the original gauge at every PSD matrix. -/
def value (X : SymmetricMatrix k) : ℝ := (positiveSemidefiniteCone k).indicator Φ X
end end Wishart.SpectralGauge
namespace Wishart.SpectralGauge section open scoped Matrix MatrixOrder Matrix.Norms.Operator RealInnerProductSpace variable {k : ℕ} (Φ : SpectralGauge k)
/-- Exact source definition of supportSequence. -/
def supportSequence : ℕ → SymmetricMatrix k := Classical.choose Φ.exists_countable_positive_support
/-- Exact source definition of supportMaximum. -/
def supportMaximum (n : ℕ) (X : SymmetricMatrix k) : ℝ := finiteMaximum (fun l : Fin (n + 1) => ⟪Φ.supportSequence l, X⟫)
end end Wishart.SpectralGauge
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.Operator
/-- Exact source definition of shiftedGaugeValue. -/
def shiftedGaugeValue {q : ℕ} (Φ : SpectralGauge q) (c : ℝ) (S : SymmetricMatrix q) : ℝ := Φ.value (S + c • SpectralGauge.identitySymmetric q)
/-- Exact source definition of normalizedGaugeValue. -/
def normalizedGaugeValue {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) (Φ : SpectralGauge q) (c : ℝ) (X : SymmetricMatrix p) : ℝ := shiftedGaugeValue Φ c (normalizedCompression Sigma B X)
end end Wishart
namespace WishartVerification.MomentAssembly section open scoped Classical ENNReal BigOperators variable {ι : Type*} [DecidableEq ι]
/-- Exact source definition of orderedGaugeRankThreshold. -/
def orderedGaugeRankThreshold (rank : ι → ℕ) (A : Finset ι) (n : ℝ) : Prop :=
  ∀ h : 3 ≤ Fintype.card A, (descendingRanks rank A ⟨2, by omega⟩ : ℝ) + 1 ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Exact source definition of GeometricGaugeFamily. -/
structure GeometricGaugeFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  gauge : ∀ i, SpectralGauge (size i)
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  outer : ι → ℝ → ℝ
  geometric : ∀ i, GeometricallyLogConvex (outer i)
end end Wishart
namespace Wishart.GeometricGaugeFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p : ℕ} {ι : Type*} [DecidableEq ι] variable (F : GeometricGaugeFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)
/-- Exact source definition of factor. -/
def factor (i : ι) (X : SymmetricMatrix p) : ℝ := F.outer i (normalizedGaugeValue Sigma (F.matrix i) (F.gauge i) (F.shift i) X)
/-- Exact source definition of subproduct. -/
def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, F.factor Sigma i X
/-- Exact source definition of moment. -/
def moment (n : ℝ) (J : Finset ι) : ℝ≥0∞ := ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma
/-- Exact source definition of ConstantFactor. -/
def ConstantFactor (i : ι) : Prop := ∃ c : ℝ, ∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosDef → F.factor Sigma i X = c
/-- Exact source definition of activeProper. -/
def activeProper [Fintype ι] : Finset ι := Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)
end end Wishart.GeometricGaugeFamily
namespace Wishart.Spectral section open scoped Classical
/-- Exact source definition of SymmetricProfile. -/
def SymmetricProfile {k : ℕ} (h : (Fin k → ℝ) → ℝ) : Prop := ∀ (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ), h (x ∘ σ) = h x
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical Matrix.Norms.Operator
/-- The manuscript's decreasing eigenvalue enumeration. -/
noncomputable def descendingSpectrum {p : ℕ} (S : Sym p) : Fin p → ℝ := ascendingSpectrum S ∘ Fin.rev
end end Wishart.Spectral
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder variable {m n : Type*} [Fintype m] [Fintype n]
/-- Exact source definition of FullColumnRank. -/
def FullColumnRank (B : Matrix m n ℍ[ℝ]) : Prop := Function.Injective B.mulVec
end end Wishart.QuaternionMatrix
namespace Wishart.FieldSpectral section open scoped Classical ComplexOrder Matrix.Norms.L2Operator variable {𝕜 : Type*} [RCLike 𝕜]
/-- Exact source definition of orderedValues. -/
def orderedValues {p : ℕ} {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.IsHermitian) : Fin p → ℝ := fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin p).symm i)
/-- Exact source definition of Hermitian. -/
abbrev Hermitian (𝕜 : Type*) [RCLike 𝕜] (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)
end end Wishart.FieldSpectral
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator open scoped Matrix.Norms.Frobenius
/-- Flatten the two scalar coordinates in the actual complex representation. -/
def flatRepresentation {p j : ℕ} (A : Matrix (Fin p) (Fin j) ℍ[ℝ]) : Matrix (Fin (p * 2)) (Fin (j * 2)) ℂ := (complexRepresentation A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
/-- Exact source definition of flatHermitian. -/
def flatHermitian {p : ℕ} (A : Hermitian p) : Wishart.FieldSpectral.Hermitian ℂ (p * 2) := ⟨flatRepresentation (A : Matrix (Fin p) (Fin p) ℍ[ℝ]), (((isHermitian_complexRepresentation_iff _).mpr (WishartVerification.hermitian_matrix_coe A)).submatrix finProdFinEquiv.symm).eq⟩
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder Matrix.Norms.L2Operator open scoped Matrix.Norms.Frobenius
/-- Exact source definition of doubledIndex. -/
def doubledIndex {p : ℕ} (i : Fin p) : Fin (p * 2) := finProdFinEquiv (i, 0)
/-- Exact source definition of orderedValues. -/
def orderedValues {p : ℕ} (A : Hermitian p) : Fin p → ℝ := fun i => Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (flatHermitian A)) (doubledIndex i)
end end Wishart.QuaternionMatrix
namespace Wishart.Spectral section open scoped Classical BigOperators variable {k : ℕ}
/-- Exact source definition of spectralRegularization. -/
def spectralRegularization (h : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (t : ℝ) : ℝ := Real.exp (h (fun i => Real.log (x i + Real.exp t)))
/-- Exact source definition of spectralBoundaryValue. -/
def spectralBoundaryValue (h : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ := ⨅ t : ℝ, spectralRegularization h x t
end end Wishart.Spectral
namespace Wishart section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal
/-- Both inequalities in the selected-factor chain, with extended expectations. Using nonnegative extended multiplication also fixes the paper's zero-factor convention: `0 * ∞ = 0`. -/
def ExtendedSelectedProductComparison {E ι : Type*} [MeasurableSpace E] [DecidableEq ι] (μ : Measure E) (f : ι → E → ℝ) : Prop := ∀ (J : Finset ι) (j : ι), j ∈ J → (∫⁻ X, ENNReal.ofReal (f j X) ∂μ) * (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, f i X) ∂μ) ≤ ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, f i X) ∂μ ∧ (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (f i X) ∂μ) ≤ (∫⁻ X, ENNReal.ofReal (f j X) ∂μ) * (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, f i X) ∂μ)
/-- Exact source definition of ComplexSpectralFamily. -/
structure ComplexSpectralFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℂ
  full_rank : ∀ i, Function.Injective (matrix i).mulVec
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  profile : ∀ i, (Fin (size i) → ℝ) → ℝ
  convex : ∀ i, ConvexOn ℝ univ (profile i)
  increasing : ∀ i, Monotone (profile i)
  symmetric : ∀ i, Spectral.SymmetricProfile (profile i)
/-- Exact source definition of QuaternionSpectralFamily. -/
structure QuaternionSpectralFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℍ[ℝ]
  full_rank : ∀ i, QuaternionMatrix.FullColumnRank (matrix i)
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  profile : ∀ i, (Fin (size i) → ℝ) → ℝ
  convex : ∀ i, ConvexOn ℝ univ (profile i)
  increasing : ∀ i, Monotone (profile i)
  symmetric : ∀ i, Spectral.SymmetricProfile (profile i)
end end Wishart
namespace Wishart.ComplexSpectralFamily section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal variable {p : ℕ} {ι : Type*} (F : ComplexSpectralFamily p ι)
/-- Exact source definition of shiftedCompression. -/
def shiftedCompression (Sigma : Matrix (Fin p) (Fin p) ℂ) (i : ι) (X : ComplexMatrix.Hermitian p) : ComplexMatrix.Hermitian (F.size i) := ComplexMatrix.normalizedCompression (F.matrix i) Sigma X + F.shift i • (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (F.size i))
/-- Exact source definition of factor. -/
def factor (Sigma : Matrix (Fin p) (Fin p) ℂ) (i : ι) (X : ComplexMatrix.Hermitian p) : ℝ := Spectral.spectralBoundaryValue (F.profile i) (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (F.shiftedCompression Sigma i X)))
end end Wishart.ComplexSpectralFamily
namespace Wishart.QuaternionSpectralFamily section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal variable {p : ℕ} {ι : Type*} (F : QuaternionSpectralFamily p ι)
/-- Exact source definition of shiftedCompression. -/
def shiftedCompression (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (i : ι) (X : QuaternionMatrix.Hermitian p) : QuaternionMatrix.Hermitian (F.size i) := QuaternionMatrix.normalizedCompression (F.matrix i) Sigma X + F.shift i • (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (F.size i))
/-- Exact source definition of factor. -/
def factor (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (i : ι) (X : QuaternionMatrix.Hermitian p) : ℝ := Spectral.spectralBoundaryValue (F.profile i) (QuaternionMatrix.orderedValues (F.shiftedCompression Sigma i X))
end end Wishart.QuaternionSpectralFamily
namespace Wishart section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal
/-- The two allowed actual complex laws; the real-shape normalization must still be established, rather than built into this predicate as an assumption. -/
def IsSectionSevenComplexLaw {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℂ) (μ : Measure (ComplexMatrix.Hermitian p)) : Prop := (∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = ComplexMatrix.wishartMeasure α Sigma) ∨ (∃ n : ℕ, 1 ≤ n ∧ μ = ComplexMatrix.gramMeasure n Sigma)
/-- Exact source definition of IsSectionSevenQuaternionLaw. -/
def IsSectionSevenQuaternionLaw {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (μ : Measure (QuaternionMatrix.Hermitian p)) : Prop := (∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = QuaternionMatrix.wishartMeasure α Sigma) ∨ (∃ n : ℕ, 1 ≤ n ∧ μ = QuaternionMatrix.gramMeasure n Sigma)
/-- This is a required conclusion in the final Section 7 package. It prevents the normalization convention `∞⁻¹ = 0` from making a malformed density law produce a vacuous zero-measure comparison. -/
def SectionSevenComplexNormalization : Prop := ∀ (p : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ), (p : ℝ) - 1 < α → Sigma.PosDef → 0 < ComplexMatrix.wishartNormalizer α Sigma ∧ ComplexMatrix.wishartNormalizer α Sigma < ⊤ ∧ IsProbabilityMeasure (ComplexMatrix.wishartMeasure α Sigma)
/-- Exact source definition of SectionSevenQuaternionNormalization. -/
def SectionSevenQuaternionNormalization : Prop := ∀ (p : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]), (p : ℝ) - 1 < α → QuaternionMatrix.PosDef Sigma → 0 < QuaternionMatrix.wishartNormalizer α Sigma ∧ QuaternionMatrix.wishartNormalizer α Sigma < ⊤ ∧ IsProbabilityMeasure (QuaternionMatrix.wishartMeasure α Sigma)
/-- Full complex principal target: all admissible real shapes and all positive integer sample sizes, all finite families and all full-column-rank overlaps. -/
def TheoremSevenOneComplex : Prop := ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Sigma : Matrix (Fin p) (Fin p) ℂ), Sigma.PosDef → ∀ (F : ComplexSpectralFamily p ι) (μ : Measure (ComplexMatrix.Hermitian p)), IsSectionSevenComplexLaw Sigma μ → ExtendedSelectedProductComparison μ (F.factor Sigma)
/-- Exact source definition of TheoremSevenOneQuaternion. -/
def TheoremSevenOneQuaternion : Prop := ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]), QuaternionMatrix.PosDef Sigma → ∀ (F : QuaternionSpectralFamily p ι) (μ : Measure (QuaternionMatrix.Hermitian p)), IsSectionSevenQuaternionLaw Sigma μ → ExtendedSelectedProductComparison μ (F.factor Sigma)
/-- The finite determinant-power assertion is a separate part of 7.1; it is not silently inferred from the extended comparison. -/
def TheoremSevenOneComplexFinitePowers : Prop := ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Sigma : Matrix (Fin p) (Fin p) ℂ), Sigma.PosDef → ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ), (∀ i, Function.Injective (B i).mulVec) → ∀ (c ν : ι → ℝ), (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) → ∀ μ : Measure (ComplexMatrix.Hermitian p), IsSectionSevenComplexLaw Sigma μ → (∫⁻ X, ENNReal.ofReal (∏ i, ComplexMatrix.realDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B i + c i • ComplexMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂μ) < ⊤
/-- Exact source definition of TheoremSevenOneQuaternionFinitePowers. -/
def TheoremSevenOneQuaternionFinitePowers : Prop := ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]), QuaternionMatrix.PosDef Sigma → ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ]), (∀ i, QuaternionMatrix.FullColumnRank (B i)) → ∀ (c ν : ι → ℝ), (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) → ∀ μ : Measure (QuaternionMatrix.Hermitian p), IsSectionSevenQuaternionLaw Sigma μ → (∫⁻ X, ENNReal.ofReal (∏ i, QuaternionMatrix.positiveDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i + c i • QuaternionMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂μ) < ⊤
/-- The required combined Section 7 target, including law nonvacuity and finite moments. Defining this proposition does not assert it. -/
def TheoremSevenOne : Prop := SectionSevenComplexNormalization ∧ SectionSevenQuaternionNormalization ∧ TheoremSevenOneComplex ∧ TheoremSevenOneQuaternion ∧ TheoremSevenOneComplexFinitePowers ∧ TheoremSevenOneQuaternionFinitePowers
end end Wishart
namespace Wishart.Spectral section open scoped Classical BigOperators Matrix.Norms.Operator
/-- Exact source definition of identitySymmetric. -/
def identitySymmetric (p : ℕ) : Sym p := ⟨1, Matrix.isHermitian_one.isSelfAdjoint⟩
/-- Exact source definition of shiftSymmetric. -/
def shiftSymmetric {p : ℕ} (c : ℝ) (X : Sym p) : Sym p := X + c • identitySymmetric p
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical BigOperators ENNReal
/-- Exact source definition of FiniteConvexIncreasingSymmetric. -/
def FiniteConvexIncreasingSymmetric {k : ℕ} (h : (Fin k → ℝ) → ℝ) : Prop := ConvexOn ℝ Set.univ h ∧ Monotone h ∧ SymmetricProfile h
/-- Exact source definition of logSpectralFactor. -/
def logSpectralFactor {k : ℕ} (h : (Fin k → ℝ) → ℝ) (S : Sym k) : ℝ := Real.exp (h (fun i => Real.log (descendingSpectrum S i)))
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
/-- Exact source definition of normalizedShiftedMatrix. -/
def normalizedShiftedMatrix {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) (c : ℝ) (X : Sym p) : Sym q := shiftSymmetric c (normalizedCompression Sigma B X)
/-- Exact source definition of normalizedLogSpectralFactor. -/
def normalizedLogSpectralFactor {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) (c : ℝ) (h : (Fin q → ℝ) → ℝ) (X : Sym p) : ℝ := logSpectralFactor h (normalizedShiftedMatrix Sigma B c X)
end end Wishart.Spectral
namespace WishartVerification.MomentAssembly section open scoped Classical ENNReal BigOperators variable {ι : Type*} [DecidableEq ι]
/-- Exact source definition of orderedPairRankThreshold. -/
def orderedPairRankThreshold (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) : Prop :=
  ∀ h : 2 ≤ Fintype.card A,
    min ((descendingRanks rank A ⟨0, by omega⟩ : ℝ) +
      descendingRanks rank A ⟨1, by omega⟩) ((p : ℝ) + 1) ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Exact source definition of LogSpectralCompressionFamily. -/
structure LogSpectralCompressionFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  profile : ∀ i, (Fin (size i) → ℝ) → ℝ
  profile_class : ∀ i, FiniteConvexIncreasingSymmetric (profile i)
end end Wishart
namespace Wishart.LogSpectralCompressionFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p : ℕ} {ι : Type*} [DecidableEq ι] variable (F : LogSpectralCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)
/-- Exact source definition of factor. -/
def factor (i : ι) (X : SymmetricMatrix p) : ℝ := normalizedLogSpectralFactor Sigma (F.matrix i) (F.shift i) (F.profile i) X
/-- Exact source definition of subproduct. -/
def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, F.factor Sigma i X
/-- Exact source definition of moment. -/
def moment (n : ℝ) (J : Finset ι) : ℝ≥0∞ := ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma
/-- Exact source definition of ConstantFactor. -/
def ConstantFactor (i : ι) : Prop := ∃ c : ℝ, ∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosDef → F.factor Sigma i X = c
/-- Exact source definition of activeProper. -/
def activeProper [Fintype ι] : Finset ι := Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)
end end Wishart.LogSpectralCompressionFamily
namespace WishartVerification section 
/-- Exact source definition of GeometricOuterOnNonnegative. -/
structure GeometricOuterOnNonnegative (f : ℝ → ℝ) : Prop where
  geometric : GeometricallyLogConvex f
  zero_nonneg : 0 ≤ f 0
  continuous_zero : ContinuousWithinAt f (Ici 0) 0
end end WishartVerification
namespace WishartVerification.MomentAssembly section open scoped Classical ENNReal BigOperators variable {ι : Type*} [DecidableEq ι]
/-- The condition is vacuous when at most two active proper factors remain; otherwise it reads precisely `n ≥ k_(1)+k_(3)` in descending order. -/
def gramOrderedRankThreshold (rank : ι → ℕ) (A : Finset ι) (n : ℕ) : Prop :=
  ∀ h : 3 ≤ Fintype.card A,
    descendingRanks rank A ⟨0, by omega⟩ +
      descendingRanks rank A ⟨2, by omega⟩ ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Exact source definition of GramGeometricCompressionFamily. -/
structure GramGeometricCompressionFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  outer : ι → ℝ → ℝ
  boundary : ∀ i, GeometricOuterOnNonnegative (outer i)
end end Wishart
namespace Wishart.GramGeometricCompressionFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p : ℕ} {ι : Type*} [DecidableEq ι] variable (F : GramGeometricCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)
/-- Exact source definition of factor. -/
def factor (i : ι) (X : SymmetricMatrix p) : ℝ := F.outer i (shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i) X)
/-- Exact source definition of subproduct. -/
def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, F.factor Sigma i X
/-- Exact source definition of moment. -/
def moment (n : ℕ) (J : Finset ι) : ℝ≥0∞ := ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂wishartGramMeasure n Sigma
/-- Exact source definition of AEConstantFactor. -/
def AEConstantFactor (n : ℕ) (i : ι) : Prop := ∃ c : ℝ, ∀ᵐ X ∂wishartGramMeasure n Sigma, F.factor Sigma i X = c
/-- Exact source definition of activeProper. -/
def activeProper [Fintype ι] (n : ℕ) : Finset ι := Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.AEConstantFactor Sigma n i)
end end Wishart.GramGeometricCompressionFamily
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- Exact source definition of matrixBetaIIConstant. -/
def matrixBetaIIConstant {p : ℕ} (α β : ℝ) (Omega : Matrix (Fin p) (Fin p) ℝ) : ℝ := multivariateGamma p ((α + β) / 2) / (multivariateGamma p (α / 2) * multivariateGamma p (β / 2)) * Omega.det ^ (β / 2)
/-- Exact source definition of matrixBetaIIPDFReal. -/
def matrixBetaIIPDFReal {p : ℕ} (α β : ℝ) (Omega : Matrix (Fin p) (Fin p) ℝ) (X : SymmetricMatrix p) : ℝ := if (X : Matrix (Fin p) (Fin p) ℝ).PosDef then matrixBetaIIConstant α β Omega * (X : Matrix (Fin p) (Fin p) ℝ).det ^ ((α - p - 1) / 2) * (Omega + (X : Matrix (Fin p) (Fin p) ℝ)).det ^ (-((α + β) / 2)) else 0
/-- Exact source definition of matrixBetaIIPDF. -/
def matrixBetaIIPDF {p : ℕ} (α β : ℝ) (Omega : Matrix (Fin p) (Fin p) ℝ) (X : SymmetricMatrix p) : ℝ≥0∞ := ENNReal.ofReal (matrixBetaIIPDFReal α β Omega X)
/-- The beta-II law is defined by the paper's density, not by an assumed hierarchy. Equality to the hierarchy is proved in the next module. -/
def matrixBetaIIMeasure {p : ℕ} (α β : ℝ) (Omega : Matrix (Fin p) (Fin p) ℝ) : Measure (SymmetricMatrix p) := (symmetricLebesgue p).withDensity (matrixBetaIIPDF α β Omega)
/-- Exact source definition of compressionDeterminantProduct. -/
def compressionDeterminantProduct {p d : ℕ} (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (ν : Fin d → ℝ) (J : Finset (Fin d)) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det ^ ν i
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The actual normalized principal matrix, with the covariance inverse square root on both sides, in an arbitrary fixed enumeration of the coordinate set. -/
def normalizedPrincipalGaugeMatrix {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) (X : SymmetricMatrix p) : SymmetricMatrix (Fintype.card I) := Matrix.symmetricCongruenceLinearMap (CFC.sqrt (Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I)))⁻¹ (principalSetMatrix I X)
/-- Exact source definition of principalGaugeFactor. -/
def principalGaugeFactor {p d : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p)) (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ) (f : Fin d → ℝ → ℝ) (i : Fin d) (X : SymmetricMatrix p) : ℝ := f i (Φ i (normalizedPrincipalGaugeMatrix Sigma (I i) X + c i • SpectralGauge.identitySymmetric (Fintype.card (I i))))
/-- Exact source definition of principalShiftedDeterminant. -/
def principalShiftedDeterminant {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) (c : ℝ) (X : SymmetricMatrix p) : ℝ := ((X : Matrix (Fin p) (Fin p) ℝ).submatrix (principalSetCoordinates I) (principalSetCoordinates I) + c • Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I)).det
/-- Exact source definition of principalLogSpectralFactor. -/
def principalLogSpectralFactor {p d : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p)) (c : Fin d → ℝ) (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ) (i : Fin d) (X : SymmetricMatrix p) : ℝ := Real.exp (h i (fun j => Real.log (ascendingSpectrum (normalizedPrincipalGaugeMatrix Sigma (I i) X + c i • Spectral.identitySymmetric (Fintype.card (I i))) j)))
/-- Exact source definition of selectedExtendedBound. -/
def selectedExtendedBound {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (μ : Measure Ω) (f : ι → Ω → ℝ) (J : Finset ι) (i : ι) : Prop := (∫⁻ X, ENNReal.ofReal (f i X) ∂μ) * (∫⁻ X, ENNReal.ofReal (∏ j ∈ J.erase i, f j X) ∂μ) ≤ ∫⁻ X, ENNReal.ofReal (∏ j ∈ J, f j X) ∂μ
/-- Exact source definition of productExtendedBound. -/
def productExtendedBound {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : ι → Ω → ℝ) (J : Finset ι) : Prop := (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (f i X) ∂μ) ≤ ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, f i X) ∂μ
/-- Exact source definition of realPairBound. -/
def realPairBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) : Prop := (∫ X, f X ∂μ) * (∫ X, g X ∂μ) ≤ ∫ X, f X * g X ∂μ
/-- The literal maximum in (10). The empty remaining product is handled by the separate trivial-small-family clause whenever that clause applies. -/
def selectedCompressionRankBound {ι : Type*} [DecidableEq ι] (rank : ι → ℕ) (J : Finset ι) (i : ι) (p : ℕ) (n : ℝ) : Prop := min ((rank i : ℝ) + (J.erase i).sup rank) ((p : ℝ) + 1) ≤ n
/-- Exact source definition of DeterminantCompressionConclusion. -/
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
/-- Exact source definition of GaugeCompressionConclusion. -/
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
/-- Exact source definition of LogSpectralCompressionConclusion. -/
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
/-- Exact source definition of Theorem51GeometricTarget. -/
def Theorem51GeometricTarget : Prop := ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (F : GeometricCompressionFamily p (Fin d)), Sigma.PosDef → (p : ℝ) - 1 < n → DeterminantCompressionConclusion F Sigma n
/-- Exact source definition of Theorem52GeometricTarget. -/
def Theorem52GeometricTarget : Prop := ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (F : GeometricGaugeFamily p (Fin d)), Sigma.PosDef → (p : ℝ) - 1 < n → GaugeCompressionConclusion F Sigma n
/-- Exact source definition of Theorem53SpectralTarget. -/
def Theorem53SpectralTarget : Prop := ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (F : LogSpectralCompressionFamily p (Fin d)), Sigma.PosDef → (p : ℝ) - 1 < n → LogSpectralCompressionConclusion F Sigma n
/-- Exact source definition of Theorem51MonotonePairTarget. -/
def Theorem51MonotonePairTarget : Prop := ∀ (p q k : ℕ) (n c d : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin k) ℝ) (f g : ℝ → ℝ), Sigma.PosDef → (p : ℝ) - 1 < n → Q.rank = q → M.rank = k → 0 ≤ c → 0 ≤ d → (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) → (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t) → MonotoneOn f (Set.Ioi 0) → MonotoneOn g (Set.Ioi 0) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) * g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma) → realPairBound (nonsingularWishartMeasure n Sigma) (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (fun X => g (shiftedCompressionDeterminant Sigma M d X))
/-- Exact source definition of Theorem52MonotonePairTarget. -/
def Theorem52MonotonePairTarget : Prop := ∀ (p q k : ℕ) (n c d : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin k) ℝ) (Φ : SpectralGauge q) (Ψ : SpectralGauge k) (f g : ℝ → ℝ), Sigma.PosDef → (p : ℝ) - 1 < n → Q.rank = q → M.rank = k → 0 ≤ c → 0 ≤ d → (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t) → (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t) → MonotoneOn f (Set.Ioi 0) → MonotoneOn g (Set.Ioi 0) → Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma) → Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X) * g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma) → realPairBound (nonsingularWishartMeasure n Sigma) (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) (fun X => g (normalizedGaugeValue Sigma M Ψ d X))
/-- Exact source definition of Theorem51PrincipalTarget. -/
def Theorem51PrincipalTarget : Prop := ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p)) (c : Fin d → ℝ) (f : Fin d → ℝ → ℝ), Sigma.PosDef → (p : ℝ) - 1 < n → Pairwise (fun i j => Disjoint (I i) (I j)) → (∀ i, 0 ≤ c i) → (∀ i, GeometricallyLogConvex (f i)) → (∀ J, ∀ i ∈ J, selectedExtendedBound (nonsingularWishartMeasure n Sigma) (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J i) ∧ (∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma) (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J)
/-- Exact source definition of Theorem52PrincipalTarget. -/
def Theorem52PrincipalTarget : Prop := ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p)) (Φ : ∀ i, SpectralGauge (Fintype.card (I i))) (c : Fin d → ℝ) (f : Fin d → ℝ → ℝ), Sigma.PosDef → (p : ℝ) - 1 < n → (∀ i, (I i).Nonempty) → Pairwise (fun i j => Disjoint (I i) (I j)) → (∀ i, 0 ≤ c i) → (∀ i, GeometricallyLogConvex (f i)) → (∀ J, ∀ i ∈ J, selectedExtendedBound (nonsingularWishartMeasure n Sigma) (principalGaugeFactor Sigma I Φ c f) J i) ∧ (∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma) (principalGaugeFactor Sigma I Φ c f) J)
/-- Exact source definition of Theorem53PrincipalTarget. -/
def Theorem53PrincipalTarget : Prop := ∀ (p d : ℕ) (n : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Fin d → Finset (Fin p)) (c : Fin d → ℝ) (h : ∀ i, (Fin (Fintype.card (I i)) → ℝ) → ℝ), Sigma.PosDef → (p : ℝ) - 1 < n → (∀ i, (I i).Nonempty) → Pairwise (fun i j => Disjoint (I i) (I j)) → (3 ≤ d ∨ (p : ℝ) ≤ n) → (∀ i, 0 ≤ c i) → (∀ i, FiniteConvexIncreasingSymmetric (h i)) → (∀ J, ∀ i ∈ J, selectedExtendedBound (nonsingularWishartMeasure n Sigma) (principalLogSpectralFactor Sigma I c h) J i) ∧ (∀ J, productExtendedBound (nonsingularWishartMeasure n Sigma) (principalLogSpectralFactor Sigma I c h) J)
/-- Exact source definition of Corollary54ProductTarget. -/
def Corollary54ProductTarget : Prop := ∀ (p d n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (F : GramGeometricCompressionFamily p (Fin d)), 1 ≤ n → Sigma.PosDef → gramOrderedRankThreshold F.size (F.activeProper Sigma n) n → ∀ J, productExtendedBound (wishartGramMeasure n Sigma) (F.factor Sigma) J
/-- Exact source definition of Corollary54MonotonePairTarget. -/
def Corollary54MonotonePairTarget : Prop := ∀ (p q k n : ℕ) (c d : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin k) ℝ) (f g : ℝ → ℝ), 1 ≤ n → Sigma.PosDef → Q.rank = q → M.rank = k → 0 ≤ c → 0 ≤ d → (∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ f t) → (∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ g t) → MonotoneOn f (Set.Ici 0) → MonotoneOn g (Set.Ici 0) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (wishartGramMeasure n Sigma) → Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X)) (wishartGramMeasure n Sigma) → Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) * g (shiftedCompressionDeterminant Sigma M d X)) (wishartGramMeasure n Sigma) → realPairBound (wishartGramMeasure n Sigma) (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (fun X => g (shiftedCompressionDeterminant Sigma M d X))
/-- Exact source definition of Corollary54PowerTarget. -/
def Corollary54PowerTarget : Prop := ∀ (p d n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ), 1 ≤ n → Sigma.PosDef → (∀ i, (B i).rank = k i) → (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) → HasAllFiniteMoments (fun X : SymmetricMatrix p => ∏ i, shiftedCompressionDeterminant Sigma (B i) (c i) X ^ ν i) (wishartGramMeasure n Sigma)
/-- Exact source definition of theorem_5_1_complete. -/
theorem theorem_5_1_complete : Theorem51GeometricTarget ∧ Theorem51MonotonePairTarget ∧ Theorem51PrincipalTarget := by sorry
/-- Exact source definition of theorem_5_2_complete. -/
theorem theorem_5_2_complete : Theorem52GeometricTarget ∧ Theorem52MonotonePairTarget ∧ Theorem52PrincipalTarget := by sorry
/-- Exact source definition of theorem_5_3_complete. -/
theorem theorem_5_3_complete : Theorem53SpectralTarget ∧ Theorem53PrincipalTarget := by sorry
/-- Exact source definition of corollary_5_4_complete. -/
theorem corollary_5_4_complete : Corollary54ProductTarget ∧ Corollary54MonotonePairTarget ∧ Corollary54PowerTarget := by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal Matrix
/-- The exact criterion under the convention permitting zero-column full column rank matrices. No positive-rank hypothesis is imposed. -/
theorem corollary_6_2_finite_moment_iff_positive_ranks {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) : Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ) (inverseWishartMeasure β Omega) ↔ 2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i), ν i) < β - p + 1 := by sorry
/-- The full common-sign product inequalities also retain zero-column compressions, with the exact positive-rank sum in the finite-moment range. -/
theorem corollary_6_2_positive_ranks {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hrange : ((∀ i, 0 ≤ ν i) ∧ 2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i), ν i) < β - p + 1) ∨ (∀ i, ν i ≤ 0)) : (∀ J : Finset (Fin d), Integrable (inverseDeterminantProduct Omega k B c ν J) (inverseWishartMeasure β Omega)) ∧ (∏ i, inverseDeterminantMoment β Omega k B c ν {i}) ≤ inverseDeterminantMoment β Omega k B c ν Finset.univ ∧ ∀ j : Fin d, (∏ i, inverseDeterminantMoment β Omega k B c ν {i}) ≤ inverseDeterminantMoment β Omega k B c ν {j} * inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ∧ inverseDeterminantMoment β Omega k B c ν {j} * inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ≤ inverseDeterminantMoment β Omega k B c ν Finset.univ := by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The marginal gamma formula on the full corrected finite-moment range. For a zero-column compression the determinant and both multivariate gamma factors equal one, so no condition on the real exponent is needed. -/
theorem corollary_6_2_gamma_moment_effective_rank {p k : ℕ} {β r : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (hr : k = 0 ∨ 2 * r < β - p + 1) : (∫ Y : SymmetricMatrix p, (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r ∂inverseWishartMeasure β Omega) = (compressionScale Omega B).det ^ r * (2 : ℝ) ^ (-(k : ℝ) * r) * (multivariateGamma k ((β - p + k) / 2 - r) / multivariateGamma k ((β - p + k) / 2)) := by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal Matrix
/-- Exact source definition of theorem_6_3_finite_moment_iff_positive_ranks. -/
theorem theorem_6_3_finite_moment_iff_positive_ranks {p d : ℕ} {α β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i) (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) : Integrable (compressionDeterminantProduct k B ν Finset.univ) (matrixBetaIIMeasure α β Omega) ↔ 2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i), ν i) < β - p + 1 := by sorry
/-- The printed beta-II gamma formula on the corrected all-rank domain. Positive ranks retain exactly the printed nonnegative moment range; rank zero permits every real exponent and both gamma ratios reduce to one. -/
theorem theorem_6_3_gamma_moment_effective_rank {p k : ℕ} {α β r : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (hr : k = 0 ∨ (0 ≤ r ∧ 2 * r < β - p + 1)) : (∫ X : SymmetricMatrix p, (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r ∂matrixBetaIIMeasure α β Omega) = (compressionScale Omega B).det ^ r * (multivariateGamma k (α / 2 + r) / multivariateGamma k (α / 2)) * (multivariateGamma k ((β - p + k) / 2 - r) / multivariateGamma k ((β - p + k) / 2)) := by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The exact beta-II product statement with the retained factors defined by their actual almost-sure behavior under the density (19). -/
theorem theorem_6_3_ae_constant_rank {p d : ℕ} {α β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef) (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i) (f : Fin d → ℝ → ℝ) (hf : ∀ i, GeometricallyLogConvex (f i)) (hsize : orderedRankThreshold k (Finset.univ.filter (fun i ↦ k i < p ∧ ¬ ∃ c : ℝ, ∀ᵐ X : SymmetricMatrix p ∂matrixBetaIIMeasure α β Omega, f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det = c)) p α) (J : Finset (Fin d)) : (∏ i ∈ J, ∫⁻ X : SymmetricMatrix p, ENNReal.ofReal (f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det) ∂matrixBetaIIMeasure α β Omega) ≤ ∫⁻ X : SymmetricMatrix p, ENNReal.ofReal (∏ i ∈ J, f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det) ∂matrixBetaIIMeasure α β Omega := by sorry
end end Wishart
namespace Wishart section open scoped Classical Quaternion ENNReal
/-- The full Section 7 target, with both literal laws, both fields, nonvacuous normalization, the selected-factor chains, and finite powers. -/
theorem theorem_7_1 : TheoremSevenOne := by sorry
end end Wishart
