/-
Copyright (c) 2026 Caius Folkerts. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This audit adapts the checked audit accompanying deformed_coinvariants in
caiusdfolkerts/lean, including its exact type serializer derived from
sublattice_resolutions. The mathematical source and the fixed endpoint
selections are specific to Wishart. This module is audit infrastructure, not a provider of
mathematical axioms or theorem statements.
-/
module
public import WishartSourceContext

/- BEGIN GENERATED LOCAL IMPORTS -/
import all WishartCommonProofWitnesses
import all WishartSourceContext
import all WishartValuePreservation
import all WishartLiteralPrimitives
import all WishartLiteralPrimitivesSourceBridge
import all TauCeti.Algebra.Module.Equiv.Basic
import all TauCeti.Algebra.Order.Field.Basic
import all TauCeti.Algebra.Quaternion.ComplexMatrix
import all TauCeti.Algebra.Quaternion.NormForm
import all TauCeti.Algebra.Ring.Invertible
import all TauCeti.Analysis.Analytic.OfScalars
import all TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import all TauCeti.Analysis.Calculus.ContDiff.Translation
import all TauCeti.Analysis.Calculus.Deriv.Second
import all TauCeti.Analysis.Calculus.DerivativeTest
import all TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import all TauCeti.Analysis.Calculus.FDeriv.Det
import all TauCeti.Analysis.Calculus.FDeriv.Prod
import all TauCeti.Analysis.Calculus.Gradient
import all TauCeti.Analysis.Calculus.LineDeriv.Basic
import all TauCeti.Analysis.Calculus.ParametricIntegral
import all TauCeti.Analysis.Calculus.SecondDerivative
import all TauCeti.Analysis.Calculus.TaylorIntegral
import all TauCeti.Analysis.Distribution.DuBoisReymond
import all TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import all TauCeti.Analysis.InnerProductSpace.BasisSpan
import all TauCeti.Analysis.InnerProductSpace.CompleteSquare
import all TauCeti.Analysis.InnerProductSpace.CourantFischer
import all TauCeti.Analysis.InnerProductSpace.Euclidean.Space
import all TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import all TauCeti.Analysis.InnerProductSpace.Harmonic.Ball
import all TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation
import all TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import all TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import all TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Converse
import all TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic
import all TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import all TauCeti.Analysis.InnerProductSpace.Laplacian.BarrierMaximizer
import all TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import all TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison
import all TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple
import all TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma
import all TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr
import all TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple
import all TauCeti.Analysis.InnerProductSpace.Laplacian.MaximumPrinciple
import all TauCeti.Analysis.InnerProductSpace.Laplacian.ParametricIntegral
import all TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple
import all TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import all TauCeti.Analysis.InnerProductSpace.NormPow
import all TauCeti.Analysis.InnerProductSpace.PointSpectrum
import all TauCeti.Analysis.InnerProductSpace.Spectrum
import all TauCeti.Analysis.InnerProductSpace.Symmetric.FunctionalCalculus
import all TauCeti.Analysis.Matrix.Eigenvalues
import all TauCeti.Analysis.Matrix.EntrywiseOpNorm
import all TauCeti.Analysis.Matrix.EuclideanLin
import all TauCeti.Analysis.Matrix.Frobenius
import all TauCeti.Analysis.Matrix.FunctionalCalculus
import all TauCeti.Analysis.Matrix.L2OpNorm
import all TauCeti.Analysis.Matrix.LDL
import all TauCeti.Analysis.Matrix.MeasurableSpace
import all TauCeti.Analysis.Matrix.OrthogonalRows
import all TauCeti.Analysis.Matrix.PosDef
import all TauCeti.Analysis.Matrix.PosSemidef.Basic
import all TauCeti.Analysis.Matrix.Spectrum
import all TauCeti.Analysis.Matrix.Sqrt
import all TauCeti.Analysis.Normed.Lp.PiLp
import all TauCeti.Analysis.Normed.Module.Ball
import all TauCeti.Analysis.Normed.Module.RCLike.Real
import all TauCeti.Analysis.Normed.Operator.Basic
import all TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
import all TauCeti.Analysis.PDE.GreenFunction.Ball
import all TauCeti.Analysis.PDE.GreenFunction.BoundaryConcentration
import all TauCeti.Analysis.PDE.PoissonIntegral.Ball
import all TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import all TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import all TauCeti.Analysis.SpecialFunctions.Erf
import all TauCeti.Analysis.SpecialFunctions.Gamma
import all TauCeti.Analysis.SpecialFunctions.IncompleteGamma
import all TauCeti.Analysis.SpecialFunctions.Log.SumLogOneSub
import all TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
import all TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Cholesky
import all TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Divergence
import all TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral
import all TauCeti.Analysis.SpecialFunctions.Pow.Real
import all TauCeti.Analysis.SpecificLimits.SqLeMulDoubling
import all TauCeti.Combinatorics.Enumerative.Partition.Basic
import all TauCeti.Combinatorics.Enumerative.Partition.Conjugate
import all TauCeti.Combinatorics.Enumerative.Partition.Dominance
import all TauCeti.Combinatorics.Young.BenderKnuth
import all TauCeti.Combinatorics.Young.Diagram
import all TauCeti.Combinatorics.Young.Kostka
import all TauCeti.Combinatorics.Young.Partitions
import all TauCeti.Combinatorics.Young.SemistandardTableau
import all TauCeti.Data.Fin.Tuple.Sort
import all TauCeti.Data.List.Lex
import all TauCeti.LinearAlgebra.Dimension.Submodule
import all TauCeti.LinearAlgebra.Eigenspace.Anticommute
import all TauCeti.LinearAlgebra.Matrix.Alternating
import all TauCeti.LinearAlgebra.Matrix.BlockSucc
import all TauCeti.LinearAlgebra.Matrix.Cholesky.Basic
import all TauCeti.LinearAlgebra.Matrix.Cholesky.Coordinates
import all TauCeti.LinearAlgebra.Matrix.Cholesky.Equiv
import all TauCeti.LinearAlgebra.Matrix.Cholesky.Jacobian
import all TauCeti.LinearAlgebra.Matrix.Cholesky.Topology
import all TauCeti.LinearAlgebra.Matrix.Congruence
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialUnitary
import all TauCeti.LinearAlgebra.Matrix.InvSub
import all TauCeti.LinearAlgebra.Matrix.MvPolynomial
import all TauCeti.LinearAlgebra.Matrix.PosSemidef
import all TauCeti.LinearAlgebra.Matrix.Rank
import all TauCeti.LinearAlgebra.Matrix.Rank.Closed
import all TauCeti.LinearAlgebra.Matrix.Trace.Basic
import all TauCeti.LinearAlgebra.Matrix.Triangular
import all TauCeti.LinearAlgebra.UnitaryGroup
import all TauCeti.MeasureTheory.Constructions.HaarToSphere
import all TauCeti.MeasureTheory.Constructions.Pi
import all TauCeti.MeasureTheory.Function.L1Space.Integrable
import all TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import all TauCeti.MeasureTheory.Function.Monotone
import all TauCeti.MeasureTheory.Group.Integral
import all TauCeti.MeasureTheory.Group.Measure
import all TauCeti.MeasureTheory.Integral.OddSymmetric
import all TauCeti.MeasureTheory.Integral.Pi
import all TauCeti.MeasureTheory.Integral.SubMeanValue
import all TauCeti.MeasureTheory.Measure.Dirac
import all TauCeti.MeasureTheory.Measure.Haar.OfBasis
import all TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import all TauCeti.MeasureTheory.Measure.Measurability
import all TauCeti.MeasureTheory.Measure.Mod0MeasureIso
import all TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
import all TauCeti.MeasureTheory.Measure.PiWithDensity
import all TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map
import all TauCeti.MeasureTheory.Measure.Prod
import all TauCeti.MeasureTheory.Measure.ProductKernel
import all TauCeti.MeasureTheory.Measure.Real
import all TauCeti.MeasureTheory.Measure.Support
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Determinant
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Integrable
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Inv
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef
import all TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank
import all TauCeti.MeasureTheory.Measure.WithDensity
import all TauCeti.MeasureTheory.OptimalTransport.Compactness
import all TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
import all TauCeti.MeasureTheory.OptimalTransport.Coupling
import all TauCeti.MeasureTheory.OptimalTransport.Existence.Basic
import all TauCeti.MeasureTheory.OptimalTransport.Gluing
import all TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic
import all TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import all TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile.Basic
import all TauCeti.Probability.Cdf
import all TauCeti.Probability.Cdf.Density
import all TauCeti.Probability.Density
import all TauCeti.Probability.Distributions.ChiSquared.Basic
import all TauCeti.Probability.Distributions.ChiSquared.Support
import all TauCeti.Probability.Distributions.Dirac
import all TauCeti.Probability.Distributions.Gamma.Basic
import all TauCeti.Probability.Distributions.Gamma.Cdf
import all TauCeti.Probability.Distributions.Gamma.CharFun
import all TauCeti.Probability.Distributions.Gamma.Measurability
import all TauCeti.Probability.Distributions.Gamma.PDF
import all TauCeti.Probability.Distributions.Gamma.Sqrt
import all TauCeti.Probability.Distributions.Gamma.Support
import all TauCeti.Probability.Distributions.Gaussian.Affine
import all TauCeti.Probability.Distributions.Gaussian.Basic
import all TauCeti.Probability.Distributions.Gaussian.Cdf
import all TauCeti.Probability.Distributions.Gaussian.ChiSquared
import all TauCeti.Probability.Distributions.Gaussian.Density
import all TauCeti.Probability.Distributions.Gaussian.Multivariate
import all TauCeti.Probability.Distributions.Gaussian.Pi
import all TauCeti.Probability.Distributions.Gaussian.QuadraticForm
import all TauCeti.Probability.Distributions.InverseGamma.Basic
import all TauCeti.Probability.Distributions.InverseGamma.Moments
import all TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
import all TauCeti.Probability.Distributions.NoncentralChiSquared.Convolution
import all TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian
import all TauCeti.Probability.Distributions.NoncentralChiSquared.Moments
import all TauCeti.Probability.Distributions.NoncentralChiSquared.StochasticOrder
import all TauCeti.Probability.Distributions.NoncentralChiSquared.Transforms
import all TauCeti.Probability.Distributions.Poisson.Basic
import all TauCeti.Probability.Distributions.Poisson.Measurability
import all TauCeti.Probability.Distributions.Wishart.Agreement
import all TauCeti.Probability.Distributions.Wishart.Bartlett
import all TauCeti.Probability.Distributions.Wishart.Basic
import all TauCeti.Probability.Distributions.Wishart.CharFun
import all TauCeti.Probability.Distributions.Wishart.Congruence
import all TauCeti.Probability.Distributions.Wishart.Inverse.Basic
import all TauCeti.Probability.Distributions.Wishart.Inverse.Measurability
import all TauCeti.Probability.Distributions.Wishart.Inverse.Moments
import all TauCeti.Probability.Distributions.Wishart.LowDimension
import all TauCeti.Probability.Distributions.Wishart.Marginal
import all TauCeti.Probability.Distributions.Wishart.Moments
import all TauCeti.Probability.Distributions.Wishart.Nonsingular
import all TauCeti.Probability.Distributions.Wishart.Transforms
import all TauCeti.Probability.GeneratingFunction
import all TauCeti.Probability.Kernel.Composition.MeasureCompProd
import all TauCeti.Probability.Kernel.Disintegration.Countable
import all TauCeti.Probability.Moments.Basic
import all TauCeti.Probability.Moments.ComplexMGF
import all TauCeti.Probability.Moments.Covariance
import all TauCeti.Probability.Moments.Determinacy
import all TauCeti.Probability.Moments.IntegrableExpMul
import all TauCeti.Probability.Moments.Pi
import all TauCeti.Probability.Quantile
import all TauCeti.Probability.StochasticOrder
import all TauCeti.RepresentationTheory.Compact.Haar
import all TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import all TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric
import all TauCeti.Topology.Algebra.MvPolynomial.ZeroLocus
import all TauCeti.Topology.Algebra.Star.Unitary
import all TauCeti.Topology.Algebra.UnitaryGroup
import all TauCeti.Topology.Compactness.Normed
import all TauCeti.Topology.EMetricSpace.Rpow
import all TauCeti.Topology.Instances.Matrix
import all TauCeti.Topology.Order.Compact
import all TauCeti.Topology.Semicontinuity.Approximation
import all verification.statements_beta_ii
import all verification.statements_beta_ii_moments
import all verification.statements_extensions
import all verification.statements_field
import all verification.statements_inverse
import all verification.statements_overlap
import all verification.statements_principal
import all verification.statements_radial_c2
import all verification.statements_radial_partition
import all verification.statements_row_logsubharmonic
import all wishart.field_foundation_verified
import all wishart.verified
import all wishart.verified.core01
import all wishart.verified.core02
import all wishart.verified.core03
import all wishart.verified.core04
import all wishart.verified.core05
import all wishart.verified.extended_log_submean
import all wishart.verified.field_analytic01
import all wishart.verified.field_analytic_union
import all wishart.verified.field_common_base
import all wishart.verified.field_example_finite_moments
import all wishart.verified.field_foundation01
import all wishart.verified.field_frontier01
import all wishart.verified.field_frontier02
import all wishart.verified.field_frontier03
import all wishart.verified.field_residual01
import all wishart.verified.field_residual02
import all wishart.verified.field_residual03
import all wishart.verified.field_residual04
import all wishart.verified.field_residual05
import all wishart.verified.field_residual06
import all wishart.verified.field_residual07
import all wishart.verified.field_residual08
import all wishart.verified.field_residual09
import all wishart.verified.field_row_logsubharmonic
import all wishart.verified.field_spectral_moments
import all wishart.verified.finite_order_congruence
import all wishart.verified.finite_order_covariance
import all wishart.verified.finite_order_extension
import all wishart.verified.finite_order_gram
import all wishart.verified.finite_order_growth
import all wishart.verified.finite_order_integral
import all wishart.verified.finite_order_radial_calculus
import all wishart.verified.finite_order_stein
import all wishart.verified.integer_radial_c2
import all wishart.verified.inverse_association01
import all wishart.verified.lemma_3_1_integer
import all wishart.verified.lemma_3_1_real
import all wishart.verified.lemma_3_3
import all wishart.verified.overlap_obstruction
import all wishart.verified.proportionate_shifts01
import all wishart.verified.radial_conclusion
import all wishart.verified.radial_expectation_c2
import all wishart.verified.radial_mean_c2
import all wishart.verified.real_all
import all wishart.verified.real_beta_ii01
import all wishart.verified.real_beta_ii02
import all wishart.verified.real_clauses01
import all wishart.verified.real_core_extensions
import all wishart.verified.real_correspondence01
import all wishart.verified.real_radial_c2
import all wishart.verified.real_remainder01
import all wishart.verified.real_remainder02
import all wishart.verified.real_remainder03
import all wishart.verified.real_remainder04
import all wishart.verified.real_remainder05
import all wishart.verified.real_remainder06
import all wishart.verified.real_remainder07
import all wishart.verified.real_remainder08
import all wishart.verified.real_remainder09
import all wishart.verified.real_remainder10
import all wishart.verified.real_remainder11
import all wishart.verified.real_remainder12
import all wishart.verified.real_remainder13
import all wishart.verified.real_remainder14
import all wishart.verified.real_remainder15
import all wishart.verified.real_tail01
import all wishart.verified.scalar_radial_c2
import all wishart.verified.shared_extended_limits01
import all wishart.verified.spectral_example_moments
import all wishart.verified.spectral_profile_closure
import all wishart_main
/- END GENERATED LOCAL IMPORTS -/
import Lean
import all Lean.Util.CollectAxioms

/-!
# Checked kernel audit of the complete Wishart development

The generated imports and ownership list are the local source dependency closure
of all Wishart theorem and literal statement modules, including the
vendored TauCeti modules. Local ownership is determined by imported module
indices and module declaration tables, not declaration namespace spelling.

Every selected local constant is read from the checked kernel environment. The
audit rejects local axioms and unapproved transitive axioms, requires the selected
paper endpoints to be actual theorem declarations with proof bodies, and rejects
unsafe or partial declarations on their traversable dependency paths. Imported
library bodies that are not exposed remain an explicit axiom-summary boundary.

Selected theorem types are exported as lossless expression DAGs. The JSON is
parsed, decoded and compared structurally with the checked type before the audit
can write .lake/reports/audit/kernel-dependencies.json. This checks the imported
environment and does not replace rebuilding the mathematical sources.
-/

set_option stderrAsMessages false

namespace WishartAudit.Kernel

namespace ExactType

open Lean

def formatVersion : String := "lean-expr-dag-v1"

def nameToJson : Name → Json
  | .anonymous => .arr #[.str "anonymous"]
  | .str p s => .arr #[.str "str", nameToJson p, .str s]
  | .num p n => .arr #[.str "num", nameToJson p, toJson n]

partial def nameFromJson (j : Json) : Except String Name := do
  match (← j.getArr?).toList with
  | [.str "anonymous"] => return .anonymous
  | [.str "str", p, s] => return .str (← nameFromJson p) (← s.getStr?)
  | [.str "num", p, n] => return .num (← nameFromJson p) (← n.getNat?)
  | _ => throw "Invalid exact Name constructor or arity"

def binderToJson : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

def binderFromJson : Json → Except String BinderInfo
  | .str "default" => .ok .default
  | .str "implicit" => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit" => .ok .instImplicit
  | _ => .error "Invalid BinderInfo constructor"

def literalToJson : Literal → Json
  | .natVal n => .arr #[.str "natVal", toJson n]
  | .strVal s => .arr #[.str "strVal", .str s]

def literalFromJson (j : Json) : Except String Literal := do
  match (← j.getArr?).toList with
  | [.str "natVal", n] => return .natVal (← n.getNat?)
  | [.str "strVal", s] => return .strVal (← s.getStr?)
  | _ => throw "Invalid Literal constructor or arity"

private structure EncodeState where
  exprMemo : ExprStructMap Nat := {}
  levelMemo : Std.HashMap Level Nat := {}
  expressions : Array Json := #[]
  levels : Array Json := #[]

private abbrev EncodeM := StateT EncodeState (Except String)

private partial def internLevel (u : Level) : EncodeM Nat := do
  if let some id := (← get).levelMemo[u]? then
    return id
  let row ← match u with
    | .zero => pure <| Json.arr #[.str "zero"]
    | .succ v => do
      let v ← internLevel v
      pure <| Json.arr #[.str "succ", toJson v]
    | .max v w => do
      let v ← internLevel v
      let w ← internLevel w
      pure <| Json.arr #[.str "max", toJson v, toJson w]
    | .imax v w => do
      let v ← internLevel v
      let w ← internLevel w
      pure <| Json.arr #[.str "imax", toJson v, toJson w]
    | .param n => pure <| Json.arr #[.str "param", nameToJson n]
    | .mvar _ => throw "Universe metavariable in a checked type export"
  let s ← get
  let id := s.levels.size
  set { s with levels := s.levels.push row, levelMemo := s.levelMemo.insert u id }
  return id

private partial def internExpr (e : Expr) : EncodeM Nat := do
  if let some id := (← get).exprMemo[ExprStructEq.mk e]? then
    return id
  let row ← match e with
    | .bvar i => pure <| Json.arr #[.str "bvar", toJson i]
    | .fvar _ => throw "Free variable in a checked type export"
    | .mvar _ => throw "Expression metavariable in a checked type export"
    | .sort u => do
      let u ← internLevel u
      pure <| Json.arr #[.str "sort", toJson u]
    | .const n us => do
      let us ← us.toArray.mapM internLevel
      pure <| Json.arr #[.str "const", nameToJson n, .arr (us.map toJson)]
    | .app f a => do
      let f ← internExpr f
      let a ← internExpr a
      pure <| Json.arr #[.str "app", toJson f, toJson a]
    | .lam n t b bi => do
      let t ← internExpr t
      let b ← internExpr b
      pure <| Json.arr #[.str "lam", nameToJson n, toJson t, toJson b, binderToJson bi]
    | .forallE n t b bi => do
      let t ← internExpr t
      let b ← internExpr b
      pure <| Json.arr #[.str "forallE", nameToJson n, toJson t, toJson b, binderToJson bi]
    | .letE n t v b nd => do
      let t ← internExpr t
      let v ← internExpr v
      let b ← internExpr b
      pure <| Json.arr #[.str "letE", nameToJson n, toJson t, toJson v, toJson b, .bool nd]
    | .lit l => pure <| Json.arr #[.str "lit", literalToJson l]
    | .mdata _ _ => throw "Metadata is forbidden in an exact checked-type DAG export"
    | .proj n i b => do
      let b ← internExpr b
      pure <| Json.arr #[.str "proj", nameToJson n, toJson i, toJson b]
  let s ← get
  let id := s.expressions.size
  set { s with expressions := s.expressions.push row, exprMemo := s.exprMemo.insert (ExprStructEq.mk e) id }
  return id

private def requireClosed (e : Expr) : Except String Unit := do
  if e.hasFVar then throw "A checked declaration type contains a free variable"
  if e.hasMVar then throw "A checked declaration type contains a metavariable"
  if e.hasLooseBVars then throw "A checked declaration type contains an unbound de Bruijn variable"

private def priorRef {α : Type} (values : Array α) (j : Json) : Except String (Nat × α) := do
  let id ← j.getNat?
  match values[id]? with
  | some value => return (id, value)
  | none => throw s!"DAG reference {id} is not strictly before node {values.size}"

private structure LevelNode where
  value : Level
  references : Array Nat := #[]

private def decodeLevelNode (prev : Array Level) (j : Json) : Except String LevelNode := do
  match (← j.getArr?).toList with
  | [.str "zero"] => return { value := .zero }
  | [.str "succ", u] =>
    let (i, u) ← priorRef prev u
    return { value := .succ u, references := #[i] }
  | [.str "max", u, v] =>
    let (i, u) ← priorRef prev u
    let (k, v) ← priorRef prev v
    return { value := .max u v, references := #[i, k] }
  | [.str "imax", u, v] =>
    let (i, u) ← priorRef prev u
    let (k, v) ← priorRef prev v
    return { value := .imax u v, references := #[i, k] }
  | [.str "param", n] => return { value := .param (← nameFromJson n) }
  | [.str "mvar", _] => throw "Universe metavariables are forbidden in a checked type DAG"
  | _ => throw "Invalid Level constructor or arity"

private structure ExprNode where
  value : Expr
  exprRefs : Array Nat := #[]
  levelRefs : Array Nat := #[]

private def decodeExprNode (prev : Array Expr) (levels : Array Level) (j : Json) :
    Except String ExprNode := do
  match (← j.getArr?).toList with
  | [.str "bvar", i] => return { value := .bvar (← i.getNat?) }
  | [.str "fvar", _] => throw "Free variables are forbidden in a checked type DAG"
  | [.str "mvar", _] => throw "Metavariables are forbidden in a checked type DAG"
  | [.str "sort", u] =>
    let (i, u) ← priorRef levels u
    return { value := .sort u, levelRefs := #[i] }
  | [.str "const", n, us] =>
    let us ← (← us.getArr?).mapM (priorRef levels)
    return { value := .const (← nameFromJson n) (us.toList.map Prod.snd), levelRefs := us.map Prod.fst }
  | [.str "app", f, a] =>
    let (i, f) ← priorRef prev f
    let (k, a) ← priorRef prev a
    return { value := .app f a, exprRefs := #[i, k] }
  | [.str "lam", n, t, b, bi] =>
    let (i, t) ← priorRef prev t
    let (k, b) ← priorRef prev b
    return { value := .lam (← nameFromJson n) t b (← binderFromJson bi), exprRefs := #[i, k] }
  | [.str "forallE", n, t, b, bi] =>
    let (i, t) ← priorRef prev t
    let (k, b) ← priorRef prev b
    return { value := .forallE (← nameFromJson n) t b (← binderFromJson bi), exprRefs := #[i, k] }
  | [.str "letE", n, t, v, b, nd] =>
    let (i, t) ← priorRef prev t
    let (k, v) ← priorRef prev v
    let (l, b) ← priorRef prev b
    return { value := .letE (← nameFromJson n) t v b (← nd.getBool?), exprRefs := #[i, k, l] }
  | [.str "lit", l] => return { value := .lit (← literalFromJson l) }
  | [.str "mdata", _, _] => throw "Metadata is forbidden in an exact checked-type DAG"
  | [.str "proj", n, i, b] =>
    let (k, b) ← priorRef prev b
    return { value := .proj (← nameFromJson n) (← i.getNat?) b, exprRefs := #[k] }
  | _ => throw "Invalid Expr constructor or arity"

structure DecodedType where
  declarationName : Name
  levelParameters : List Name
  type : Expr
  expressionNodes : Nat
  levelNodes : Nat

/-- Decode and validate a strictly postorder, closed, entirely reachable type DAG. -/
def decodeType (j : Json) : Except String DecodedType := do
  unless (← (← j.getObjVal? "format").getStr?) == formatVersion do
    throw "Unsupported type DAG format"
  let declarationName ← nameFromJson (← j.getObjVal? "declaration_name")
  let levelParameters ← (← (← j.getObjVal? "level_parameters").getArr?).toList.mapM nameFromJson
  let levelRows ← (← j.getObjVal? "levels").getArr?
  let exprRows ← (← j.getObjVal? "expressions").getArr?
  let mut levels : Array Level := #[]
  let mut usedLevels : Array Bool := Array.replicate levelRows.size false
  for row in levelRows do
    let node ← decodeLevelNode levels row
    for i in node.references do
      usedLevels := usedLevels.set! i true
    levels := levels.push node.value
  let mut expressions : Array Expr := #[]
  let mut usedExprs : Array Bool := Array.replicate exprRows.size false
  for row in exprRows do
    let node ← decodeExprNode expressions levels row
    for i in node.exprRefs do
      usedExprs := usedExprs.set! i true
    for i in node.levelRefs do
      usedLevels := usedLevels.set! i true
    expressions := expressions.push node.value
  let root ← (← j.getObjVal? "root").getNat?
  let some type := expressions[root]? | throw "Missing type DAG root"
  unless root + 1 == expressions.size do
    throw "A postorder type DAG must have its root last"
  -- Every non-root node must be referenced. With strictly backward references,
  -- this is equivalent to reachability from the unique last/root node.
  for i in [:usedExprs.size] do
    if i != root && !usedExprs[i]! then
      throw s!"Unreachable expression node {i}"
  -- Every level must lead, through strictly backward universe references,
  -- to a use in a reachable expression node.
  for i in [:usedLevels.size] do
    unless usedLevels[i]! do throw s!"Unreachable universe node {i}"
  requireClosed type
  return { declarationName, levelParameters, type, expressionNodes := expressions.size, levelNodes := levels.size }

/--
Export the actual checked type. `complete` is added only after JSON byte
serialization, reparsing, closed/postorder/reachability validation, and an exact
`Expr.equal` comparison. This is neither alpha-equivalence nor definitional equality.
-/
def encodeCheckedType (declName : Name) (levelParams : List Name) (type : Expr) :
    Except String Json := do
  requireClosed type
  let (root, state) ← (internExpr type).run {}
  let payload := Json.mkObj [
    ("format", .str formatVersion),
    ("declaration_name", nameToJson declName),
    ("level_parameters", .arr (levelParams.toArray.map nameToJson)),
    ("levels", .arr state.levels),
    ("expressions", .arr state.expressions),
    ("root", toJson root)]
  let serialized := payload.compress
  let parsed ← Json.parse serialized
  let decoded ← decodeType parsed
  unless decoded.declarationName == declName do
    throw "Exact declaration Name round-trip failed"
  unless decoded.levelParameters == levelParams do
    throw "Exact universe-parameter Name/order round-trip failed"
  unless Expr.equal decoded.type type do
    throw "Exact structural Expr round-trip failed"
  return Json.mkObj [
    ("format", .str formatVersion),
    ("complete", .bool true),
    ("roundtrip_check", .str "Json.compress -> Json.parse -> decodeType -> Expr.equal"),
    ("expression_nodes", toJson state.expressions.size),
    ("level_nodes", toJson state.levels.size),
    ("metadata_nodes", toJson (0 : Nat)),
    ("metadata_policy", .str "reject-all"),
    ("serialized_payload_bytes", toJson serialized.toUTF8.size),
    ("payload", parsed)]

end ExactType


set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  if (← getOptions).getBool "debug.skipKernelTC".toName false then
    throwError "The kernel audit requires debug.skipKernelTC=false"
  let outputDirectory : System.FilePath := ".lake/reports/audit"
  let outputPath := outputDirectory / "kernel-dependencies.json"
  -- A failed audit must not leave a previous success at its output path.
  if ← liftIO outputPath.pathExists then
    liftIO <| IO.FS.removeFile outputPath
  -- BEGIN GENERATED OWNED MODULES
  let projectModules : Array Name := #[
    `WishartCommonProofWitnesses,
    `WishartSourceContext,
    `WishartValuePreservation,
    `WishartLiteralPrimitives,
    `WishartLiteralPrimitivesSourceBridge,

    `TauCeti.Algebra.Module.Equiv.Basic,
    `TauCeti.Algebra.Order.Field.Basic,
    `TauCeti.Algebra.Quaternion.ComplexMatrix,
    `TauCeti.Algebra.Quaternion.NormForm,
    `TauCeti.Algebra.Ring.Invertible,
    `TauCeti.Analysis.Analytic.OfScalars,
    `TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity,
    `TauCeti.Analysis.Calculus.ContDiff.Translation,
    `TauCeti.Analysis.Calculus.Deriv.Second,
    `TauCeti.Analysis.Calculus.DerivativeTest,
    `TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap,
    `TauCeti.Analysis.Calculus.FDeriv.Det,
    `TauCeti.Analysis.Calculus.FDeriv.Prod,
    `TauCeti.Analysis.Calculus.Gradient,
    `TauCeti.Analysis.Calculus.LineDeriv.Basic,
    `TauCeti.Analysis.Calculus.ParametricIntegral,
    `TauCeti.Analysis.Calculus.SecondDerivative,
    `TauCeti.Analysis.Calculus.TaylorIntegral,
    `TauCeti.Analysis.Distribution.DuBoisReymond,
    `TauCeti.Analysis.Distribution.TestFunction.LineDeriv,
    `TauCeti.Analysis.InnerProductSpace.BasisSpan,
    `TauCeti.Analysis.InnerProductSpace.CompleteSquare,
    `TauCeti.Analysis.InnerProductSpace.CourantFischer,
    `TauCeti.Analysis.InnerProductSpace.Euclidean.Space,
    `TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho,
    `TauCeti.Analysis.InnerProductSpace.Harmonic.Ball,
    `TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation,
    `TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry,
    `TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic,
    `TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Converse,
    `TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic,
    `TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.BarrierMaximizer,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.Basic,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.MaximumPrinciple,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.ParametricIntegral,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple,
    `TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple,
    `TauCeti.Analysis.InnerProductSpace.NormPow,
    `TauCeti.Analysis.InnerProductSpace.PointSpectrum,
    `TauCeti.Analysis.InnerProductSpace.Spectrum,
    `TauCeti.Analysis.InnerProductSpace.Symmetric.FunctionalCalculus,
    `TauCeti.Analysis.Matrix.Eigenvalues,
    `TauCeti.Analysis.Matrix.EntrywiseOpNorm,
    `TauCeti.Analysis.Matrix.EuclideanLin,
    `TauCeti.Analysis.Matrix.Frobenius,
    `TauCeti.Analysis.Matrix.FunctionalCalculus,
    `TauCeti.Analysis.Matrix.L2OpNorm,
    `TauCeti.Analysis.Matrix.LDL,
    `TauCeti.Analysis.Matrix.MeasurableSpace,
    `TauCeti.Analysis.Matrix.OrthogonalRows,
    `TauCeti.Analysis.Matrix.PosDef,
    `TauCeti.Analysis.Matrix.PosSemidef.Basic,
    `TauCeti.Analysis.Matrix.Spectrum,
    `TauCeti.Analysis.Matrix.Sqrt,
    `TauCeti.Analysis.Normed.Lp.PiLp,
    `TauCeti.Analysis.Normed.Module.Ball,
    `TauCeti.Analysis.Normed.Module.RCLike.Real,
    `TauCeti.Analysis.Normed.Operator.Basic,
    `TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic,
    `TauCeti.Analysis.PDE.GreenFunction.Ball,
    `TauCeti.Analysis.PDE.GreenFunction.BoundaryConcentration,
    `TauCeti.Analysis.PDE.PoissonIntegral.Ball,
    `TauCeti.Analysis.Sobolev.WeakDeriv.Basic,
    `TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian,
    `TauCeti.Analysis.SpecialFunctions.Erf,
    `TauCeti.Analysis.SpecialFunctions.Gamma,
    `TauCeti.Analysis.SpecialFunctions.IncompleteGamma,
    `TauCeti.Analysis.SpecialFunctions.Log.SumLogOneSub,
    `TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic,
    `TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Cholesky,
    `TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Divergence,
    `TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral,
    `TauCeti.Analysis.SpecialFunctions.Pow.Real,
    `TauCeti.Analysis.SpecificLimits.SqLeMulDoubling,
    `TauCeti.Combinatorics.Enumerative.Partition.Basic,
    `TauCeti.Combinatorics.Enumerative.Partition.Conjugate,
    `TauCeti.Combinatorics.Enumerative.Partition.Dominance,
    `TauCeti.Combinatorics.Young.BenderKnuth,
    `TauCeti.Combinatorics.Young.Diagram,
    `TauCeti.Combinatorics.Young.Kostka,
    `TauCeti.Combinatorics.Young.Partitions,
    `TauCeti.Combinatorics.Young.SemistandardTableau,
    `TauCeti.Data.Fin.Tuple.Sort,
    `TauCeti.Data.List.Lex,
    `TauCeti.LinearAlgebra.Dimension.Submodule,
    `TauCeti.LinearAlgebra.Eigenspace.Anticommute,
    `TauCeti.LinearAlgebra.Matrix.Alternating,
    `TauCeti.LinearAlgebra.Matrix.BlockSucc,
    `TauCeti.LinearAlgebra.Matrix.Cholesky.Basic,
    `TauCeti.LinearAlgebra.Matrix.Cholesky.Coordinates,
    `TauCeti.LinearAlgebra.Matrix.Cholesky.Equiv,
    `TauCeti.LinearAlgebra.Matrix.Cholesky.Jacobian,
    `TauCeti.LinearAlgebra.Matrix.Cholesky.Topology,
    `TauCeti.LinearAlgebra.Matrix.Congruence,
    `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialUnitary,
    `TauCeti.LinearAlgebra.Matrix.InvSub,
    `TauCeti.LinearAlgebra.Matrix.MvPolynomial,
    `TauCeti.LinearAlgebra.Matrix.PosSemidef,
    `TauCeti.LinearAlgebra.Matrix.Rank,
    `TauCeti.LinearAlgebra.Matrix.Rank.Closed,
    `TauCeti.LinearAlgebra.Matrix.Trace.Basic,
    `TauCeti.LinearAlgebra.Matrix.Triangular,
    `TauCeti.LinearAlgebra.UnitaryGroup,
    `TauCeti.MeasureTheory.Constructions.HaarToSphere,
    `TauCeti.MeasureTheory.Constructions.Pi,
    `TauCeti.MeasureTheory.Function.L1Space.Integrable,
    `TauCeti.MeasureTheory.Function.Lp.LIntegralRpow,
    `TauCeti.MeasureTheory.Function.Monotone,
    `TauCeti.MeasureTheory.Group.Integral,
    `TauCeti.MeasureTheory.Group.Measure,
    `TauCeti.MeasureTheory.Integral.OddSymmetric,
    `TauCeti.MeasureTheory.Integral.Pi,
    `TauCeti.MeasureTheory.Integral.SubMeanValue,
    `TauCeti.MeasureTheory.Measure.Dirac,
    `TauCeti.MeasureTheory.Measure.Haar.OfBasis,
    `TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral,
    `TauCeti.MeasureTheory.Measure.Measurability,
    `TauCeti.MeasureTheory.Measure.Mod0MeasureIso,
    `TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus,
    `TauCeti.MeasureTheory.Measure.PiWithDensity,
    `TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map,
    `TauCeti.MeasureTheory.Measure.Prod,
    `TauCeti.MeasureTheory.Measure.ProductKernel,
    `TauCeti.MeasureTheory.Measure.Real,
    `TauCeti.MeasureTheory.Measure.Support,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Determinant,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Integrable,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Inv,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef,
    `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank,
    `TauCeti.MeasureTheory.Measure.WithDensity,
    `TauCeti.MeasureTheory.OptimalTransport.Compactness,
    `TauCeti.MeasureTheory.OptimalTransport.Cost.Basic,
    `TauCeti.MeasureTheory.OptimalTransport.Coupling,
    `TauCeti.MeasureTheory.OptimalTransport.Existence.Basic,
    `TauCeti.MeasureTheory.OptimalTransport.Gluing,
    `TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic,
    `TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic,
    `TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile.Basic,
    `TauCeti.Probability.Cdf,
    `TauCeti.Probability.Cdf.Density,
    `TauCeti.Probability.Density,
    `TauCeti.Probability.Distributions.ChiSquared.Basic,
    `TauCeti.Probability.Distributions.ChiSquared.Support,
    `TauCeti.Probability.Distributions.Dirac,
    `TauCeti.Probability.Distributions.Gamma.Basic,
    `TauCeti.Probability.Distributions.Gamma.Cdf,
    `TauCeti.Probability.Distributions.Gamma.CharFun,
    `TauCeti.Probability.Distributions.Gamma.Measurability,
    `TauCeti.Probability.Distributions.Gamma.PDF,
    `TauCeti.Probability.Distributions.Gamma.Sqrt,
    `TauCeti.Probability.Distributions.Gamma.Support,
    `TauCeti.Probability.Distributions.Gaussian.Affine,
    `TauCeti.Probability.Distributions.Gaussian.Basic,
    `TauCeti.Probability.Distributions.Gaussian.Cdf,
    `TauCeti.Probability.Distributions.Gaussian.ChiSquared,
    `TauCeti.Probability.Distributions.Gaussian.Density,
    `TauCeti.Probability.Distributions.Gaussian.Multivariate,
    `TauCeti.Probability.Distributions.Gaussian.Pi,
    `TauCeti.Probability.Distributions.Gaussian.QuadraticForm,
    `TauCeti.Probability.Distributions.InverseGamma.Basic,
    `TauCeti.Probability.Distributions.InverseGamma.Moments,
    `TauCeti.Probability.Distributions.NoncentralChiSquared.Basic,
    `TauCeti.Probability.Distributions.NoncentralChiSquared.Convolution,
    `TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian,
    `TauCeti.Probability.Distributions.NoncentralChiSquared.Moments,
    `TauCeti.Probability.Distributions.NoncentralChiSquared.StochasticOrder,
    `TauCeti.Probability.Distributions.NoncentralChiSquared.Transforms,
    `TauCeti.Probability.Distributions.Poisson.Basic,
    `TauCeti.Probability.Distributions.Poisson.Measurability,
    `TauCeti.Probability.Distributions.Wishart.Agreement,
    `TauCeti.Probability.Distributions.Wishart.Bartlett,
    `TauCeti.Probability.Distributions.Wishart.Basic,
    `TauCeti.Probability.Distributions.Wishart.CharFun,
    `TauCeti.Probability.Distributions.Wishart.Congruence,
    `TauCeti.Probability.Distributions.Wishart.Inverse.Basic,
    `TauCeti.Probability.Distributions.Wishart.Inverse.Measurability,
    `TauCeti.Probability.Distributions.Wishart.Inverse.Moments,
    `TauCeti.Probability.Distributions.Wishart.LowDimension,
    `TauCeti.Probability.Distributions.Wishart.Marginal,
    `TauCeti.Probability.Distributions.Wishart.Moments,
    `TauCeti.Probability.Distributions.Wishart.Nonsingular,
    `TauCeti.Probability.Distributions.Wishart.Transforms,
    `TauCeti.Probability.GeneratingFunction,
    `TauCeti.Probability.Kernel.Composition.MeasureCompProd,
    `TauCeti.Probability.Kernel.Disintegration.Countable,
    `TauCeti.Probability.Moments.Basic,
    `TauCeti.Probability.Moments.ComplexMGF,
    `TauCeti.Probability.Moments.Covariance,
    `TauCeti.Probability.Moments.Determinacy,
    `TauCeti.Probability.Moments.IntegrableExpMul,
    `TauCeti.Probability.Moments.Pi,
    `TauCeti.Probability.Quantile,
    `TauCeti.Probability.StochasticOrder,
    `TauCeti.RepresentationTheory.Compact.Haar,
    `TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic,
    `TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric,
    `TauCeti.Topology.Algebra.MvPolynomial.ZeroLocus,
    `TauCeti.Topology.Algebra.Star.Unitary,
    `TauCeti.Topology.Algebra.UnitaryGroup,
    `TauCeti.Topology.Compactness.Normed,
    `TauCeti.Topology.EMetricSpace.Rpow,
    `TauCeti.Topology.Instances.Matrix,
    `TauCeti.Topology.Order.Compact,
    `TauCeti.Topology.Semicontinuity.Approximation,
    `verification.statements_beta_ii,
    `verification.statements_beta_ii_moments,
    `verification.statements_extensions,
    `verification.statements_field,
    `verification.statements_inverse,
    `verification.statements_overlap,
    `verification.statements_principal,
    `verification.statements_radial_c2,
    `verification.statements_radial_partition,
    `verification.statements_row_logsubharmonic,
    `wishart.field_foundation_verified,
    `wishart.verified,
    `wishart.verified.core01,
    `wishart.verified.core02,
    `wishart.verified.core03,
    `wishart.verified.core04,
    `wishart.verified.core05,
    `wishart.verified.extended_log_submean,
    `wishart.verified.field_analytic01,
    `wishart.verified.field_analytic_union,
    `wishart.verified.field_common_base,
    `wishart.verified.field_example_finite_moments,
    `wishart.verified.field_foundation01,
    `wishart.verified.field_frontier01,
    `wishart.verified.field_frontier02,
    `wishart.verified.field_frontier03,
    `wishart.verified.field_residual01,
    `wishart.verified.field_residual02,
    `wishart.verified.field_residual03,
    `wishart.verified.field_residual04,
    `wishart.verified.field_residual05,
    `wishart.verified.field_residual06,
    `wishart.verified.field_residual07,
    `wishart.verified.field_residual08,
    `wishart.verified.field_residual09,
    `wishart.verified.field_row_logsubharmonic,
    `wishart.verified.field_spectral_moments,
    `wishart.verified.finite_order_congruence,
    `wishart.verified.finite_order_covariance,
    `wishart.verified.finite_order_extension,
    `wishart.verified.finite_order_gram,
    `wishart.verified.finite_order_growth,
    `wishart.verified.finite_order_integral,
    `wishart.verified.finite_order_radial_calculus,
    `wishart.verified.finite_order_stein,
    `wishart.verified.integer_radial_c2,
    `wishart.verified.inverse_association01,
    `wishart.verified.lemma_3_1_integer,
    `wishart.verified.lemma_3_1_real,
    `wishart.verified.lemma_3_3,
    `wishart.verified.overlap_obstruction,
    `wishart.verified.proportionate_shifts01,
    `wishart.verified.radial_conclusion,
    `wishart.verified.radial_expectation_c2,
    `wishart.verified.radial_mean_c2,
    `wishart.verified.real_all,
    `wishart.verified.real_beta_ii01,
    `wishart.verified.real_beta_ii02,
    `wishart.verified.real_clauses01,
    `wishart.verified.real_core_extensions,
    `wishart.verified.real_correspondence01,
    `wishart.verified.real_radial_c2,
    `wishart.verified.real_remainder01,
    `wishart.verified.real_remainder02,
    `wishart.verified.real_remainder03,
    `wishart.verified.real_remainder04,
    `wishart.verified.real_remainder05,
    `wishart.verified.real_remainder06,
    `wishart.verified.real_remainder07,
    `wishart.verified.real_remainder08,
    `wishart.verified.real_remainder09,
    `wishart.verified.real_remainder10,
    `wishart.verified.real_remainder11,
    `wishart.verified.real_remainder12,
    `wishart.verified.real_remainder13,
    `wishart.verified.real_remainder14,
    `wishart.verified.real_remainder15,
    `wishart.verified.real_tail01,
    `wishart.verified.scalar_radial_c2,
    `wishart.verified.shared_extended_limits01,
    `wishart.verified.spectral_example_moments,
    `wishart.verified.spectral_profile_closure,
    `wishart_main]
  -- END GENERATED OWNED MODULES
  -- BEGIN SELECTED THEOREM ROOTS
  let roots : Array (String × Name × Name) := #[
    ("WishartVerification.theorem_1_1", `WishartVerification.theorem_1_1, `wishart.verified.core05),
    ("WishartVerification.theorem_1_1_of_hasLaw", `WishartVerification.theorem_1_1_of_hasLaw, `wishart.verified.real_correspondence01),
    ("WishartVerification.proportional_shift_product_inequalities", `WishartVerification.proportional_shift_product_inequalities, `wishart.verified.proportionate_shifts01),
    ("WishartVerification.proposition_4_1", `WishartVerification.proposition_4_1, `wishart.verified.proportionate_shifts01),
    ("WishartVerification.proposition_4_1_exponent_monotonicity", `WishartVerification.proposition_4_1_exponent_monotonicity, `wishart.verified.proportionate_shifts01),
    ("WishartVerification.proposition_4_1_stochastic_domination", `WishartVerification.proposition_4_1_stochastic_domination, `wishart.verified.proportionate_shifts01),
    ("Wishart.theorem_5_1_complete", `Wishart.theorem_5_1_complete, `wishart.verified.real_clauses01),
    ("Wishart.theorem_5_2_complete", `Wishart.theorem_5_2_complete, `wishart.verified.real_clauses01),
    ("Wishart.theorem_5_3_complete", `Wishart.theorem_5_3_complete, `wishart.verified.real_clauses01),
    ("Wishart.corollary_5_4_complete", `Wishart.corollary_5_4_complete, `wishart.verified.real_clauses01),
    ("Wishart.real_section_five", `Wishart.real_section_five, `wishart.verified.real_clauses01),
    ("Wishart.theorem_6_1", `Wishart.theorem_6_1, `wishart.verified.inverse_association01),
    ("Wishart.theorem_6_1_on_positiveOrderedSpectrum", `Wishart.theorem_6_1_on_positiveOrderedSpectrum, `wishart.verified.inverse_association01),
    ("Wishart.corollary_6_2", `Wishart.corollary_6_2, `wishart.verified.real_remainder03),
    ("Wishart.corollary_6_2_finite_moment_iff", `Wishart.corollary_6_2_finite_moment_iff, `wishart.verified.real_remainder03),
    ("Wishart.corollary_6_2_positive_ranks", `Wishart.corollary_6_2_positive_ranks, `wishart.verified.real_tail01),
    ("Wishart.corollary_6_2_finite_moment_iff_positive_ranks", `Wishart.corollary_6_2_finite_moment_iff_positive_ranks, `wishart.verified.real_tail01),
    ("Wishart.corollary_6_2_gamma_moment_effective_rank", `Wishart.corollary_6_2_gamma_moment_effective_rank, `wishart.verified.real_tail01),
    ("Wishart.Audit.inverse_rank_zero_moment_threshold_edge_case", `Wishart.Audit.inverse_rank_zero_moment_threshold_edge_case, `wishart.verified.real_tail01),
    ("Wishart.theorem_6_3", `Wishart.theorem_6_3, `wishart.verified.real_beta_ii02),
    ("Wishart.theorem_6_3_ae_constant_rank", `Wishart.theorem_6_3_ae_constant_rank, `wishart.verified.real_tail01),
    ("Wishart.theorem_6_3_disjoint_principal_blocks_allow_empty", `Wishart.theorem_6_3_disjoint_principal_blocks_allow_empty, `wishart.verified.real_tail01),
    ("Wishart.theorem_6_3_finite_moment_iff_positive_ranks", `Wishart.theorem_6_3_finite_moment_iff_positive_ranks, `wishart.verified.real_tail01),
    ("Wishart.theorem_6_3_gamma_moment_effective_rank", `Wishart.theorem_6_3_gamma_moment_effective_rank, `wishart.verified.real_tail01),
    ("Wishart.theorem_7_1", `Wishart.theorem_7_1, `wishart.verified.field_residual08),
    ("Wishart.theorem_7_1_complex", `Wishart.theorem_7_1_complex, `wishart.verified.field_residual08),
    ("Wishart.theorem_7_1_quaternion", `Wishart.theorem_7_1_quaternion, `wishart.verified.field_residual08),
    ("Wishart.theorem_7_1_complex_normalization", `Wishart.theorem_7_1_complex_normalization, `wishart.verified.field_residual02),
    ("Wishart.theorem_7_1_quaternion_normalization", `Wishart.theorem_7_1_quaternion_normalization, `wishart.verified.field_residual02),
    ("Wishart.theorem_7_1_complex_finite_powers", `Wishart.theorem_7_1_complex_finite_powers, `wishart.verified.field_residual07),
    ("Wishart.theorem_7_1_quaternion_finite_powers", `Wishart.theorem_7_1_quaternion_finite_powers, `wishart.verified.field_residual07),
    ("WishartAudit.principal_exact", `WishartAudit.principal_exact, `verification.statements_principal),
    ("WishartAudit.proportional_shift_exact", `WishartAudit.proportional_shift_exact, `verification.statements_extensions),
    ("WishartAudit.exponent_monotonicity_exact", `WishartAudit.exponent_monotonicity_exact, `verification.statements_extensions),
    ("WishartAudit.inverse_association_exact", `WishartAudit.inverse_association_exact, `verification.statements_extensions),
    ("WishartAudit.inverse_domain_association_exact", `WishartAudit.inverse_domain_association_exact, `verification.statements_extensions),
    ("WishartAudit.inverse_determinant_product_exact", `WishartAudit.inverse_determinant_product_exact, `verification.statements_inverse),
    ("WishartAudit.inverse_determinant_moment_exact", `WishartAudit.inverse_determinant_moment_exact, `verification.statements_inverse),
    ("WishartAudit.inverse_determinant_gamma_exact", `WishartAudit.inverse_determinant_gamma_exact, `verification.statements_inverse),
    ("WishartAudit.inverse_all_rank_moment_exact", `WishartAudit.inverse_all_rank_moment_exact, `verification.statements_inverse),
    ("WishartAudit.inverse_all_rank_gamma_exact", `WishartAudit.inverse_all_rank_gamma_exact, `verification.statements_inverse),
    ("FieldSevenOneAudit.complex_positive_value", `FieldSevenOneAudit.complex_positive_value, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_positive_value", `FieldSevenOneAudit.quaternion_positive_value, `verification.statements_field),
    ("FieldSevenOneAudit.complex_matrix_boundary", `FieldSevenOneAudit.complex_matrix_boundary, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_matrix_boundary", `FieldSevenOneAudit.quaternion_matrix_boundary, `verification.statements_field),
    ("FieldSevenOneAudit.complex_whitening_formula", `FieldSevenOneAudit.complex_whitening_formula, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_whitening_formula", `FieldSevenOneAudit.quaternion_whitening_formula, `verification.statements_field),
    ("FieldSevenOneAudit.complex_determinant_eigenvalues", `FieldSevenOneAudit.complex_determinant_eigenvalues, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_determinant_eigenvalues", `FieldSevenOneAudit.quaternion_determinant_eigenvalues, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_positive_cone", `FieldSevenOneAudit.quaternion_positive_cone, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_strict_positive_cone", `FieldSevenOneAudit.quaternion_strict_positive_cone, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_full_column_rank", `FieldSevenOneAudit.quaternion_full_column_rank, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_rank_complex_representation", `FieldSevenOneAudit.quaternion_rank_complex_representation, `verification.statements_field),
    ("FieldSevenOneAudit.complex_component_law", `FieldSevenOneAudit.complex_component_law, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_component_law", `FieldSevenOneAudit.quaternion_component_law, `verification.statements_field),
    ("FieldSevenOneAudit.complex_covariance_factor", `FieldSevenOneAudit.complex_covariance_factor, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_covariance_factor", `FieldSevenOneAudit.quaternion_covariance_factor, `verification.statements_field),
    ("FieldSevenOneAudit.complex_gram_image", `FieldSevenOneAudit.complex_gram_image, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_gram_image", `FieldSevenOneAudit.quaternion_gram_image, `verification.statements_field),
    ("FieldSevenOneAudit.complexDensity20_eq_weight", `FieldSevenOneAudit.complexDensity20_eq_weight, `verification.statements_field),
    ("FieldSevenOneAudit.quaternionDensity20_eq_weight", `FieldSevenOneAudit.quaternionDensity20_eq_weight, `verification.statements_field),
    ("FieldSevenOneAudit.complex_density_20", `FieldSevenOneAudit.complex_density_20, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_density_20", `FieldSevenOneAudit.quaternion_density_20, `verification.statements_field),
    ("FieldSevenOneAudit.complex_selected_chain", `FieldSevenOneAudit.complex_selected_chain, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_selected_chain", `FieldSevenOneAudit.quaternion_selected_chain, `verification.statements_field),
    ("FieldSevenOneAudit.complex_finite_powers", `FieldSevenOneAudit.complex_finite_powers, `verification.statements_field),
    ("FieldSevenOneAudit.quaternion_finite_powers", `FieldSevenOneAudit.quaternion_finite_powers, `verification.statements_field),
    ("Wishart.theorem_7_1_complex_of_hasLaw", `Wishart.theorem_7_1_complex_of_hasLaw, `wishart.verified.field_residual08),
    ("Wishart.theorem_7_1_quaternion_of_hasLaw", `Wishart.theorem_7_1_quaternion_of_hasLaw, `wishart.verified.field_residual08),
    ("Wishart.theorem_7_1_complex_finite_powers_of_hasLaw", `Wishart.theorem_7_1_complex_finite_powers_of_hasLaw, `wishart.verified.field_residual08),
    ("Wishart.theorem_7_1_quaternion_finite_powers_of_hasLaw", `Wishart.theorem_7_1_quaternion_finite_powers_of_hasLaw, `wishart.verified.field_residual08),
    ("Wishart.ExtendedSelectedProductComparison.of_zero_or_aeEq", `Wishart.ExtendedSelectedProductComparison.of_zero_or_aeEq, `wishart.verified.field_residual08),
    ("Wishart.complex_unnormalizedDeterminantPower_comparison", `Wishart.complex_unnormalizedDeterminantPower_comparison, `wishart.verified.field_residual09),
    ("Wishart.quaternion_unnormalizedDeterminantPower_comparison", `Wishart.quaternion_unnormalizedDeterminantPower_comparison, `wishart.verified.field_residual09),
    ("Wishart.complex_geometricDeterminant_comparison", `Wishart.complex_geometricDeterminant_comparison, `wishart.verified.field_residual09),
    ("Wishart.quaternion_geometricDeterminant_comparison", `Wishart.quaternion_geometricDeterminant_comparison, `wishart.verified.field_residual09),
    ("WishartVerification.Audit.betaII_density_eighteen_normalized", `WishartVerification.Audit.betaII_density_eighteen_normalized, `verification.statements_beta_ii),
    ("WishartVerification.Audit.betaII_density_positive_exactly_on_cone", `WishartVerification.Audit.betaII_density_positive_exactly_on_cone, `verification.statements_beta_ii),
    ("WishartVerification.Audit.betaII_ae_constant_iff_on_positive_cone", `WishartVerification.Audit.betaII_ae_constant_iff_on_positive_cone, `verification.statements_beta_ii),
    ("WishartVerification.Audit.betaII_rank_condition_exact", `WishartVerification.Audit.betaII_rank_condition_exact, `verification.statements_beta_ii),
    ("WishartVerification.Audit.betaII_actual_hierarchy_and_independent_congruence", `WishartVerification.Audit.betaII_actual_hierarchy_and_independent_congruence, `verification.statements_beta_ii),
    ("WishartVerification.Audit.betaII_product_complete_ae_rank", `WishartVerification.Audit.betaII_product_complete_ae_rank, `verification.statements_beta_ii),
    ("WishartVerification.Audit.betaII_disjoint_principal_blocks_all_shapes", `WishartVerification.Audit.betaII_disjoint_principal_blocks_all_shapes, `verification.statements_beta_ii),
    ("WishartVerification.Audit.betaII_joint_moment_exact_positive_rank_sum", `WishartVerification.Audit.betaII_joint_moment_exact_positive_rank_sum, `verification.statements_beta_ii_moments),
    ("WishartVerification.Audit.betaII_joint_lintegral_finite_iff_positive_rank_sum", `WishartVerification.Audit.betaII_joint_lintegral_finite_iff_positive_rank_sum, `verification.statements_beta_ii_moments),
    ("WishartVerification.Audit.betaII_joint_moment_exact_nonempty_compressions", `WishartVerification.Audit.betaII_joint_moment_exact_nonempty_compressions, `verification.statements_beta_ii_moments),
    ("WishartVerification.Audit.betaII_gamma_moment_all_ranks", `WishartVerification.Audit.betaII_gamma_moment_all_ranks, `verification.statements_beta_ii_moments),
    ("WishartVerification.Audit.betaII_zero_column_moment_every_real_exponent", `WishartVerification.Audit.betaII_zero_column_moment_every_real_exponent, `verification.statements_beta_ii_moments),
    ("WishartVerification.Audit.betaII_rank_zero_moment_threshold_edge_case", `WishartVerification.Audit.betaII_rank_zero_moment_threshold_edge_case, `verification.statements_beta_ii_moments),
    ("Wishart.lintegral_compression_det_rpow_matrixBetaII_factorization", `Wishart.lintegral_compression_det_rpow_matrixBetaII_factorization, `wishart.verified.real_beta_ii02),
    ("Wishart.integrable_inverse_product_of_matrixBetaII_product", `Wishart.integrable_inverse_product_of_matrixBetaII_product, `wishart.verified.real_beta_ii02),
    ("Wishart.complex_unitarilyInvariantNorm_power_comparison", `Wishart.complex_unitarilyInvariantNorm_power_comparison, `wishart.verified.field_residual08),
    ("Wishart.quaternion_unitarilyInvariantNorm_power_comparison", `Wishart.quaternion_unitarilyInvariantNorm_power_comparison, `wishart.verified.field_residual08),
    ("Wishart.complex_polynomialPower_comparison", `Wishart.complex_polynomialPower_comparison, `wishart.verified.field_residual09),
    ("Wishart.quaternion_polynomialPower_comparison", `Wishart.quaternion_polynomialPower_comparison, `wishart.verified.field_residual09),
    ("Wishart.complex_elementaryPower_comparison", `Wishart.complex_elementaryPower_comparison, `wishart.verified.field_residual09),
    ("Wishart.quaternion_elementaryPower_comparison", `Wishart.quaternion_elementaryPower_comparison, `wishart.verified.field_residual09),
    ("Wishart.complex_schurPositivePower_comparison", `Wishart.complex_schurPositivePower_comparison, `wishart.verified.field_residual09),
    ("Wishart.quaternion_schurPositivePower_comparison", `Wishart.quaternion_schurPositivePower_comparison, `wishart.verified.field_residual09),
    ("Wishart.complex_tracePower_comparison", `Wishart.complex_tracePower_comparison, `wishart.verified.field_residual09),
    ("Wishart.quaternion_tracePower_comparison", `Wishart.quaternion_tracePower_comparison, `wishart.verified.field_residual09),
    ("Wishart.Spectral.productProfile_properties", `Wishart.Spectral.productProfile_properties, `wishart.verified.spectral_profile_closure),
    ("Wishart.Spectral.spectralBoundaryValue_productProfile", `Wishart.Spectral.spectralBoundaryValue_productProfile, `wishart.verified.spectral_profile_closure),
    ("Wishart.Spectral.nonnegativeSumProfile_properties", `Wishart.Spectral.nonnegativeSumProfile_properties, `wishart.verified.spectral_profile_closure),
    ("Wishart.Spectral.spectralBoundaryValue_nonnegativeSumProfile", `Wishart.Spectral.spectralBoundaryValue_nonnegativeSumProfile, `wishart.verified.spectral_profile_closure),
    ("Wishart.Spectral.nonnegativeSum_zero_or_profile", `Wishart.Spectral.nonnegativeSum_zero_or_profile, `wishart.verified.spectral_profile_closure),
    ("Wishart.Spectral.outerCompositionProfile_properties", `Wishart.Spectral.outerCompositionProfile_properties, `wishart.verified.spectral_profile_closure),
    ("Wishart.Spectral.spectralBoundaryValue_outerCompositionProfile", `Wishart.Spectral.spectralBoundaryValue_outerCompositionProfile, `wishart.verified.spectral_profile_closure),
    ("WishartVerification.HasAllFiniteMoments.polynomial_eval", `WishartVerification.HasAllFiniteMoments.polynomial_eval, `wishart.verified.spectral_example_moments),
    ("WishartVerification.HasAllFiniteMoments.finite_lintegral_product", `WishartVerification.HasAllFiniteMoments.finite_lintegral_product, `wishart.verified.spectral_example_moments),
    ("Wishart.Spectral.SymmetricAbsoluteNorm.sqrt_value_le_sum_sqrt", `Wishart.Spectral.SymmetricAbsoluteNorm.sqrt_value_le_sum_sqrt, `wishart.verified.spectral_example_moments),
    ("Wishart.Spectral.SymmetricAbsoluteNorm.sqrt_value_allFiniteMoments", `Wishart.Spectral.SymmetricAbsoluteNorm.sqrt_value_allFiniteMoments, `wishart.verified.spectral_example_moments),
    ("Wishart.ComplexMatrix.shiftedCompression_eigenvalue_allFiniteMoments_of_trace", `Wishart.ComplexMatrix.shiftedCompression_eigenvalue_allFiniteMoments_of_trace, `wishart.verified.field_spectral_moments),
    ("Wishart.QuaternionMatrix.orderedValues_le_realTrace", `Wishart.QuaternionMatrix.orderedValues_le_realTrace, `wishart.verified.field_spectral_moments),
    ("Wishart.QuaternionMatrix.shiftedCompression_eigenvalue_allFiniteMoments_of_trace", `Wishart.QuaternionMatrix.shiftedCompression_eigenvalue_allFiniteMoments_of_trace, `wishart.verified.field_spectral_moments),
    ("Wishart.IsSectionSevenComplexLaw.isProbability", `Wishart.IsSectionSevenComplexLaw.isProbability, `wishart.verified.field_spectral_moments),
    ("Wishart.IsSectionSevenQuaternionLaw.isProbability", `Wishart.IsSectionSevenQuaternionLaw.isProbability, `wishart.verified.field_spectral_moments),
    ("Wishart.IsSectionSevenComplexLaw.trace_allFiniteMoments", `Wishart.IsSectionSevenComplexLaw.trace_allFiniteMoments, `wishart.verified.field_spectral_moments),
    ("Wishart.IsSectionSevenQuaternionLaw.trace_allFiniteMoments", `Wishart.IsSectionSevenQuaternionLaw.trace_allFiniteMoments, `wishart.verified.field_spectral_moments),
    ("Wishart.complex_shifted_eigenvalue_allFiniteMoments", `Wishart.complex_shifted_eigenvalue_allFiniteMoments, `wishart.verified.field_spectral_moments),
    ("Wishart.quaternion_shifted_eigenvalue_allFiniteMoments", `Wishart.quaternion_shifted_eigenvalue_allFiniteMoments, `wishart.verified.field_spectral_moments),
    ("Wishart.complex_polynomialPower_allFiniteMoments", `Wishart.complex_polynomialPower_allFiniteMoments, `wishart.verified.field_example_finite_moments),
    ("Wishart.complex_tracePower_allFiniteMoments", `Wishart.complex_tracePower_allFiniteMoments, `wishart.verified.field_example_finite_moments),
    ("Wishart.complex_unitarilyInvariantNorm_power_allFiniteMoments", `Wishart.complex_unitarilyInvariantNorm_power_allFiniteMoments, `wishart.verified.field_example_finite_moments),
    ("Wishart.quaternion_polynomialPower_allFiniteMoments", `Wishart.quaternion_polynomialPower_allFiniteMoments, `wishart.verified.field_example_finite_moments),
    ("Wishart.quaternion_tracePower_allFiniteMoments", `Wishart.quaternion_tracePower_allFiniteMoments, `wishart.verified.field_example_finite_moments),
    ("Wishart.quaternion_unitarilyInvariantNorm_power_allFiniteMoments", `Wishart.quaternion_unitarilyInvariantNorm_power_allFiniteMoments, `wishart.verified.field_example_finite_moments),
    ("Wishart.complex_polynomialPowers_finite_joint_moment", `Wishart.complex_polynomialPowers_finite_joint_moment, `wishart.verified.field_example_finite_moments),
    ("Wishart.complex_tracePowers_finite_joint_moment", `Wishart.complex_tracePowers_finite_joint_moment, `wishart.verified.field_example_finite_moments),
    ("Wishart.complex_unitarilyInvariantNormPowers_finite_joint_moment", `Wishart.complex_unitarilyInvariantNormPowers_finite_joint_moment, `wishart.verified.field_example_finite_moments),
    ("Wishart.quaternion_polynomialPowers_finite_joint_moment", `Wishart.quaternion_polynomialPowers_finite_joint_moment, `wishart.verified.field_example_finite_moments),
    ("Wishart.quaternion_tracePowers_finite_joint_moment", `Wishart.quaternion_tracePowers_finite_joint_moment, `wishart.verified.field_example_finite_moments),
    ("Wishart.quaternion_unitarilyInvariantNormPowers_finite_joint_moment", `Wishart.quaternion_unitarilyInvariantNormPowers_finite_joint_moment, `wishart.verified.field_example_finite_moments),
    ("Wishart.OverlapObstruction.covariance_rank_one_overlap", `Wishart.OverlapObstruction.covariance_rank_one_overlap, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.covariance_rank_one_overlap_neg", `Wishart.OverlapObstruction.covariance_rank_one_overlap_neg, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.covariance_rank_one_overlap_three_halves", `Wishart.OverlapObstruction.covariance_rank_one_overlap_three_halves, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.covariance_rank_one_overlap_three_halves_neg", `Wishart.OverlapObstruction.covariance_rank_one_overlap_three_halves_neg, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.isProbabilityMeasure_coordinateMeasure", `Wishart.OverlapObstruction.isProbabilityMeasure_coordinateMeasure, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.bartlett_realizes_wishart", `Wishart.OverlapObstruction.bartlett_realizes_wishart, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integrable_monomial", `Wishart.OverlapObstruction.integrable_monomial, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integral_monomial", `Wishart.OverlapObstruction.integral_monomial, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.continuous_selectedQuadratic", `Wishart.OverlapObstruction.continuous_selectedQuadratic, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.continuous_shiftedQuadratic", `Wishart.OverlapObstruction.continuous_shiftedQuadratic, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.continuous_overlapProduct", `Wishart.OverlapObstruction.continuous_overlapProduct, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integrable_selectedQuadratic", `Wishart.OverlapObstruction.integrable_selectedQuadratic, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integrable_overlapProduct", `Wishart.OverlapObstruction.integrable_overlapProduct, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integrable_selected_overlapProduct", `Wishart.OverlapObstruction.integrable_selected_overlapProduct, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integral_selectedQuadratic", `Wishart.OverlapObstruction.integral_selectedQuadratic, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integral_overlapProduct", `Wishart.OverlapObstruction.integral_overlapProduct, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.integral_selected_overlapProduct", `Wishart.OverlapObstruction.integral_selected_overlapProduct, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.rank_one_overlap_split_fails", `Wishart.OverlapObstruction.rank_one_overlap_split_fails, `wishart.verified.overlap_obstruction),
    ("Wishart.OverlapObstruction.conditional_mean_rank_one_overlap_bartlett", `Wishart.OverlapObstruction.conditional_mean_rank_one_overlap_bartlett, `wishart.verified.overlap_obstruction),
    ("WishartAudit.overlap_covariance_exact", `WishartAudit.overlap_covariance_exact, `verification.statements_overlap),
    ("WishartAudit.overlap_covariance_negative_exact", `WishartAudit.overlap_covariance_negative_exact, `verification.statements_overlap),
    ("WishartVerification.lemma_2_1_association", `WishartVerification.lemma_2_1_association, `wishart.verified.core03),
    ("WishartVerification.lemma_2_1_strict_association", `WishartVerification.lemma_2_1_strict_association, `wishart.verified.core04),
    ("Wishart.map_regressionJointReconstruction", `Wishart.map_regressionJointReconstruction, `wishart.verified.core01),
    ("WishartVerification.cdf_gaussian_shift_determinant_antitone", `WishartVerification.cdf_gaussian_shift_determinant_antitone, `wishart.verified.core02),
    ("WishartVerification.integral_gaussian_rankOneDeterminant_rpow_strictMono", `WishartVerification.integral_gaussian_rankOneDeterminant_rpow_strictMono, `wishart.verified.core02),
    ("Wishart.FiniteOrder.lemma_3_1_integer", `Wishart.FiniteOrder.lemma_3_1_integer, `wishart.verified.lemma_3_1_integer),
    ("Wishart.FiniteOrder.lemma_3_1_real", `Wishart.FiniteOrder.lemma_3_1_real, `wishart.verified.lemma_3_1_real),
    ("WishartAudit.lemma_3_1_integer_literal", `WishartAudit.lemma_3_1_integer_literal, `verification.statements_radial_c2),
    ("WishartAudit.lemma_3_1_real_literal", `WishartAudit.lemma_3_1_real_literal, `verification.statements_radial_c2),
    ("WishartAudit.hessian_polynomial_bound_iff_bilinear_bound", `WishartAudit.hessian_polynomial_bound_iff_bilinear_bound, `verification.statements_radial_c2),
    ("Wishart.FieldGaussian.complex_row_logsubharmonic_product", `Wishart.FieldGaussian.complex_row_logsubharmonic_product, `wishart.verified.field_row_logsubharmonic),
    ("Wishart.FieldGaussian.quaternion_row_logsubharmonic_product", `Wishart.FieldGaussian.quaternion_row_logsubharmonic_product, `wishart.verified.field_row_logsubharmonic),
    ("WishartAudit.lemma_7_2_complex_literal", `WishartAudit.lemma_7_2_complex_literal, `verification.statements_row_logsubharmonic),
    ("WishartAudit.lemma_7_2_quaternion_literal", `WishartAudit.lemma_7_2_quaternion_literal, `verification.statements_row_logsubharmonic),
    ("WishartVerification.ExtendedLogSubmean.positive_truncation", `WishartVerification.ExtendedLogSubmean.positive_truncation, `wishart.verified.extended_log_submean),
    ("WishartVerification.ExtendedLogSubmean.finset_prod_ballSubmean", `WishartVerification.ExtendedLogSubmean.finset_prod_ballSubmean, `wishart.verified.extended_log_submean),
    ("WishartVerification.lemma_3_3", `WishartVerification.lemma_3_3, `wishart.verified.lemma_3_3),
    ("WishartVerification.strictMonoOn_radial_full_determinant", `WishartVerification.strictMonoOn_radial_full_determinant, `wishart.verified.lemma_3_3),
    ("WishartAudit.lemma_3_3_literal", `WishartAudit.lemma_3_3_literal, `verification.statements_radial_partition),
    ("WishartAudit.lemma_3_3_single_block_strict_literal", `WishartAudit.lemma_3_3_single_block_strict_literal, `verification.statements_radial_partition),
    ("Wishart.map_regressionReconstruction", `Wishart.map_regressionReconstruction, `wishart.verified.core01)]
  -- END SELECTED THEOREM ROOTS
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName,
    "Quot.sound".toName]
  let moduleNames := env.header.moduleNames
  let selectedModules : NameSet :=
    projectModules.foldl (fun names name => names.insert name) {}
  unless selectedModules.size == projectModules.size do
    throwError "Duplicate module in the generated ownership list"
  let moduleOf := fun name =>
    match env.getModuleIdxFor? name with
    | some i => moduleNames[i.toNat]!
    | none => env.mainModule
  -- A changed mathematical import graph must regenerate the explicit list.
  for moduleName in moduleNames do
    let localPrefix := moduleName.toString.startsWith "Wishart" ||
      moduleName.toString.startsWith "wishart." ||
      moduleName == `wishart_main ||
      moduleName.toString.startsWith "TauCeti." ||
      moduleName.toString.startsWith "verification.statements_"
    if localPrefix && !selectedModules.contains moduleName then
      throwError "Local import absent from generated audit closure: {moduleName}"
  for moduleName in projectModules do
    unless moduleNames.contains moduleName do
      throwError "Expected local module was not imported: {moduleName}"
  let checked := env.checked.get
  let mut constants : Array (Name × ConstantInfo) := #[]
  let mut declaredIn : NameMap (Array Name) := {}
  let mut loadedProjectModules : Array Name := #[]
  for i in [:moduleNames.size] do
    let moduleName := moduleNames[i]!
    if selectedModules.contains moduleName then
      unless env.header.modules[i]!.importAll do
        throwError "Local module requires import all to expose its kernel bodies: {moduleName}"
      loadedProjectModules := loadedProjectModules.push moduleName
      let moduleData := env.header.moduleData[i]!
      unless moduleData.constNames.size == moduleData.constants.size do
        throwError "Inconsistent imported constant arrays in {moduleName}"
      for name in moduleData.constNames, stored in moduleData.constants do
        let some ci := checked.find? name |
          throwError "Local declaration absent from checked environment: {name}"
        -- Compatible duplicate entries may occur in generated equation lemmas.
        -- Accept them only when their complete ConstantInfo agrees.
        unless ci == stored do
          throwError "Imported local body differs from resolved checked body: {name} in {moduleName}"
        let entries := (declaredIn.find? name).getD #[]
        declaredIn := declaredIn.insert name (entries.push moduleName)
        if entries.isEmpty then
          constants := constants.push (name, ci)
  if constants.isEmpty then
    throwError "No local declarations were selected for the kernel audit"
  unless loadedProjectModules.size == projectModules.size do
    throwError "The audit did not load every selected local module"
  constants := constants.qsort (fun a b => Name.lt a.1 b.1)
  let projectInfo : NameMap ConstantInfo :=
    constants.foldl (fun result pair => result.insert pair.1 pair.2) {}
  let isProject := fun name => projectInfo.contains name
  let kindOf := fun ci : ConstantInfo => match ci with
    | .axiomInfo _ => "axiom"
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "definition"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  liftIO <| IO.eprintln
    s!"KERNEL_AUDIT_PHASE: {constants.size} checked declarations; {projectModules.size} local modules"
  -- Recompute local axiom dependencies from checked types and values. At the
  -- external-library boundary, use Lean's exported axiom summaries; this is
  -- necessary when an imported library theorem deliberately hides its body.
  let axiomState := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let findExternalAxioms := fun (e : Environment) (name : Name) =>
    if isProject name then none else axiomState.find? e name
  let localAxiomLists := CollectAxioms.runM env do
    constants.mapM fun (name, _) =>
      CollectAxioms.collectAndGet findExternalAxioms name
  let mut nodes : Array Json := #[]
  let mut leaves : NameSet := {}
  let mut localTheorems : Nat := 0
  for (name, ci) in constants, axioms in localAxiomLists do
    if ci.isAxiom then
      throwError "Local axiom is forbidden: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
      throwError "Local declaration has an open checked type: {name}"
    if let some value := ci.value? (allowOpaque := true) then
      if value.hasMVar || value.hasFVar || value.hasLooseBVars then
        throwError "Local declaration has an open checked body: {name}"
    if let .thmInfo _ := ci then
      localTheorems := localTheorems + 1
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} in local declaration {name}"
    let dependencies := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    if dependencies.contains "sorryAx".toName then
      throwError "Local declaration contains sorryAx: {name}"
    for dependency in dependencies do
      unless isProject dependency do
        leaves := leaves.insert dependency
      unless (checked.find? dependency).isSome ||
          (axiomState.find? env dependency).isSome do
        throwError "Dependency has neither checked information nor an imported axiom summary: {dependency}"
    let ranges ← findDeclarationRangesCore? name
    nodes := nodes.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("indexed_module", toJson (moduleOf name).toString),
      ("declared_in_modules", toJson (((declaredIn.find? name).getD #[]).map Name.toString)),
      ("source_start_line", toJson (ranges.map (fun r => r.range.pos.line))),
      ("source_end_line", toJson (ranges.map (fun r => r.range.endPos.line))),
      ("declaration_kind", toJson (kindOf ci)),
      ("body_available", toJson (ci.hasValue (allowOpaque := true))),
      ("is_unsafe", toJson ci.isUnsafe),
      ("is_partial", toJson ci.isPartial),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
      ("dependencies", toJson (dependencies.map Name.toString))]
  if localTheorems == 0 then
    throwError "No local theorems were checked"
  let mut rootInfo : Array Json := #[]
  for (paperResult, name, expectedModule) in roots do
    let some ci := projectInfo.find? name |
      throwError "Selected theorem is absent from the checked local declarations: {name}"
    unless ((declaredIn.find? name).getD #[]).contains expectedModule do
      throwError "Selected theorem is not declared in its expected module: {name} in {expectedModule}"
    -- In particular, an opaque statement or an imported axiom-shaped stub
    -- cannot satisfy the requirement for a principal mathematical theorem.
    let proof ← match ci with
      | .thmInfo value => pure value.value
      | _ => throwError "Selected endpoint is not an actual checked theorem with a proof: {name}"
    if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars then
      throwError "Selected theorem has an open proof: {name}"
    let axioms := CollectAxioms.runM env <|
      CollectAxioms.collectAndGet findExternalAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} in selected theorem {name}"
    let ty ← liftTermElabM <| PrettyPrinter.ppExpr ci.type
    let exactType ← match ExactType.encodeCheckedType ci.name ci.levelParams ci.type with
      | .ok data => pure data
      | .error message => throwError "Lossless checked-type export failed for {name}: {message}"
    rootInfo := rootInfo.push <| Json.mkObj [
      ("paper_result", toJson paperResult),
      ("name", toJson name.toString),
      ("module", toJson (moduleOf name).toString),
      ("declaration_kind", toJson "theorem"),
      ("proof_body_present", toJson true),
      ("type_readable", toJson ty.pretty),
      ("type_kernel", exactType),
      ("universe_parameters", toJson (ci.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString))]
    liftIO <| IO.eprintln s!"KERNEL_AUDIT_PHASE: checked theorem and exact type: {name}"
  -- Traverse actual checked types and available values, including available
  -- imported-library bodies. Hidden external bodies are recorded as summary
  -- boundaries, not described as traversed or independently rechecked here.
  let mut pending := roots.map (fun (_, name, _) => name)
  let mut reachable : NameSet := {}
  let mut externalNodes : Array Json := #[]
  let mut summaryBoundaries : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless reachable.contains name do
      reachable := reachable.insert name
      if name == "sorryAx".toName then
        throwError "Selected theorem dependency path reaches sorryAx"
      match checked.find? name with
      | none =>
        let some axioms := axiomState.find? env name |
          throwError "Selected dependency has no checked information or axiom summary: {name}"
        if isProject name then
          throwError "Local dependency has no checked body: {name}"
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unapproved boundary axiom {ax} in selected dependency {name}"
        summaryBoundaries := summaryBoundaries.insert name
        externalNodes := externalNodes.push <| Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson (moduleOf name).toString),
          ("body_available", toJson false),
          ("inspection", toJson "exported axiom summary only")]
      | some ci =>
        if ci.isUnsafe || ci.isPartial then
          throwError "Unsafe or partial declaration on a selected kernel dependency path: {name}"
        let dependencies := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
        for dependency in dependencies do
          pending := pending.push dependency
        if ci.isAxiom && !allowed.contains name then
          unless (axiomState.find? env name).isSome do
            throwError "Opaque imported boundary lacks an exported axiom summary: {name}"
          summaryBoundaries := summaryBoundaries.insert name
        unless isProject name do
          externalNodes := externalNodes.push <| Json.mkObj [
            ("name", toJson name.toString),
            ("module", toJson (moduleOf name).toString),
            ("declaration_kind", toJson (kindOf ci)),
            ("body_available", toJson (ci.hasValue (allowOpaque := true))),
            ("is_unsafe", toJson ci.isUnsafe),
            ("is_partial", toJson ci.isPartial),
            ("dependencies", toJson (dependencies.map Name.toString))]
  let mut leafInfo : Array Json := #[]
  for name in (leaves ++ summaryBoundaries).toArray.qsort Name.lt do
    unless (checked.find? name).isSome || (axiomState.find? env name).isSome do
      throwError "Imported boundary dependency is unavailable: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} in imported boundary dependency {name}"
    leafInfo := leafInfo.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson (moduleOf name).toString),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
      ("on_selected_dependency_path", toJson (reachable.contains name)),
      ("hidden_body_boundary", toJson (summaryBoundaries.contains name))]
  let runtimeOnly := constants.filterMap fun (name, ci) =>
    if ci.isUnsafe || ci.isPartial then some <| Json.mkObj [
      ("name", toJson name.toString),
      ("is_unsafe", toJson ci.isUnsafe),
      ("is_partial", toJson ci.isPartial),
      ("reachable_from_selected_theorems", toJson (reachable.contains name))]
    else none
  let graph := Json.mkObj [
    ("format", toJson "wishart-kernel-audit-v1"),
    ("lean_version", toJson Lean.versionString),
    ("audit_module", toJson env.mainModule.toString),
    ("kernel_checking_enabled_for_audit", toJson true),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("local_axiom_analysis", toJson
      "Traversed checked local types and bodies; used Lean exported axiom summaries at external-library boundaries."),
    ("dependency_path_analysis", toJson
      "Rejected unsafe and partial constants on selected paths through checked types and available values; recorded hidden imported bodies as summary boundaries."),
    ("type_export_format", toJson ExactType.formatVersion),
    ("project_modules", toJson (projectModules.qsort Name.lt |>.map Name.toString)),
    ("project_declaration_count", toJson constants.size),
    ("project_theorem_count", toJson localTheorems),
    ("selected_dependency_count", toJson reachable.size),
    ("roots", Json.arr rootInfo),
    ("local_declarations", Json.arr nodes),
    ("unreachable_local_runtime_implementations", Json.arr runtimeOnly),
    ("reachable_external_declarations", Json.arr
      (externalNodes.qsort (fun a b => a.compress < b.compress))),
    ("imported_boundary_dependencies", Json.arr leafInfo),
    ("hidden_body_boundaries", toJson
      (summaryBoundaries.toArray.qsort Name.lt |>.map Name.toString))]
  -- Validation above is mandatory; JSON persistence is optional in read-only builds.
  let reportPersisted ← liftIO do
    try
      IO.FS.createDirAll outputDirectory
      let temporaryPath := outputDirectory / "kernel-dependencies.json.tmp"
      IO.FS.writeFile temporaryPath (graph.pretty ++ "\n")
      IO.FS.rename temporaryPath outputPath
      pure true
    catch _ => pure false
  logInfo m!"Optional kernel audit report persisted: {reportPersisted}"
  logInfo m!"KERNEL_AUDIT_OK {constants.size} local declarations; {localTheorems} theorems; {roots.size} roots; {projectModules.size} local modules; {reachable.size} inspected dependency nodes"

end WishartAudit.Kernel

