module

public import volume_polynomials.assembly_part03

/- Candidate source-preserving assembly. This file is not a verification report. -/
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FinCases
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic.Abel
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Data.Nat.Find
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Data.List.Range
public import Mathlib.Order.Filter.Finite
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Matrix
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Data.List.SignVariations
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Geometry.Convex.Cone.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Relation
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.Setoid.Partition
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Order.Fin.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.Multiset.UnionInter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Sym.Basic
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Tactic.GCongr
public import Mathlib.FieldTheory.IsRealClosed.Real
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Ring.Ordering.Basic
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Order.Zorn
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.Tactic.ByContra
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Definability
public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.ModelTheory.Order
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Tactic.Choose
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.NumberTheory.Niven
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Sublists
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Logic.Encodable.Pi
public meta import Lean.Elab.Command
public meta import Lean.AddDecl
public meta import Lean.Data.Json
public meta import Lean.Util.FoldConsts
public meta import Lean.Meta.Tactic.AuxLemma
meta import all Lean.Meta.Match.Match
public meta import Lean.Util.CollectAxioms
public meta import Lean.Meta.Basic
public meta import Lean.Meta.RecExt
public meta import Lean.Compiler.Old

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  try
    IO.FS.createDirAll ".lake/reports/audit"
  catch _ =>
    IO.eprintln "Optional audit report output skipped in this environment."


set_option Elab.async false


set_option Elab.async false

/- BEGIN SOURCE: VolumePolynomials/PlanarFiberAverage.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # Minkowski averaging in the literal product coordinates

`Plane` and `Space k` have the sup norm. We transport both factors through
the actual measure-preserving `WithLp 2` equivalences before applying the
inner-product averaging theorem. Thus all areas and uniform averages below
retain their original product-Lebesgue meaning. The zero-dimensional base
is treated separately by its actual Dirac volume.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

namespace MinkowskiFunctional

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def comp_mapBody (φ : MinkowskiFunctional F) (L : E →L[ℝ] F) :
    MinkowskiFunctional E where
  toFun K := φ (mapBody L K)
  continuous_toFun := φ.continuous_toFun.comp (continuous_mapBody L)
  monotone h := φ.monotone (Set.image_mono h)
  map_add K M := by rw [mapBody_add, φ.map_add]
  map_nonneg_smul r hr K := by rw [mapBody_smul, φ.map_nonneg_smul r hr]

@[simp] theorem comp_mapBody_apply (φ : MinkowskiFunctional F) (L : E →L[ℝ] F)
    (K : ConvexBody E) : φ.comp_mapBody L K = φ (mapBody L K) := rfl

end MinkowskiFunctional

theorem mapBody_equiv_symm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E ≃L[ℝ] F) (K : ConvexBody E) :
    mapBody T.symm.toContinuousLinearMap (mapBody T.toContinuousLinearMap K) = K := by
  first
  | apply ConvexBody.ext
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      have hyx : y = x := by
        change T.symm (T y) = x at hxy
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hxy
      exact hyx ▸ hy
    · intro hx
      exact ⟨T x, ⟨x, hx, rfl⟩, T.symm_apply_apply x⟩

theorem uniformAverage_image_measurePreserving {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T) (Z : Set E) (f : F → ℝ) :
    uniformAverage (T '' Z) f = uniformAverage Z (fun x => f (T x)) := by
  first
  | have hmeasure := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' Z)
    rw [Set.preimage_image_eq Z T.injective] at hmeasure
    have hreal : volume.real (T '' Z) = volume.real Z :=
      congrArg ENNReal.toReal hmeasure.symm
    rw [uniformAverage, uniformAverage,
      hT.setIntegral_image_emb T.toHomeomorph.measurableEmbedding f Z, hreal]

namespace ConvexFibers

section Equivalences

variable {E E' U U' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup U'] [NormedSpace ℝ U']

theorem projection_map_prodEquiv (T : E ≃L[ℝ] E') (S : U ≃L[ℝ] U')
    (F : ConvexBody (E × U)) :
    projection (mapBody (T.prodCongr S).toContinuousLinearMap F) = S '' projection F := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hpy⟩
      exact ⟨p.2, ⟨p, hp, rfl⟩, hpy⟩
    · rintro ⟨u, ⟨p, hp, hpu⟩, huy⟩
      exact ⟨(T p.1, S p.2), ⟨p, hp, rfl⟩, (congrArg S hpu).trans huy⟩

theorem fiberBody_map_prodEquiv (T : E ≃L[ℝ] E') (S : U ≃L[ℝ] U')
    (F : ConvexBody (E × U)) {y : U} (hy : y ∈ projection F) :
    fiberBody (mapBody (T.prodCongr S).toContinuousLinearMap F) (S y) =
      mapBody T.toContinuousLinearMap (fiberBody F y) := by
  first
  | have hy' : S y ∈ projection (mapBody (T.prodCongr S).toContinuousLinearMap F) := by
      first
      | rw [projection_map_prodEquiv]
        exact Set.mem_image_of_mem S hy
    apply ConvexBody.ext
    rw [coe_fiberBody _ hy', coe_mapBody, coe_fiberBody _ hy]
    ext x
    constructor
    · rintro ⟨⟨u, z⟩, huz, h⟩
      have hzy : z = y := S.injective (congrArg Prod.snd h)
      subst z
      exact ⟨u, huz, congrArg Prod.fst h⟩
    · rintro ⟨u, huy, hux⟩
      exact ⟨(u, y), huy, Prod.ext hux rfl⟩

end Equivalences

end ConvexFibers

namespace PlanarInteraction

open PlanarExtrusion ConvexFibers MinkowskiAverages

abbrev InnerPlane := WithLp 2 Plane
abbrev InnerBase (k : ℕ) := EuclideanSpace ℝ (Fin k)

def planeToInner : Plane ≃L[ℝ] InnerPlane :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm

def baseToInner (k : ℕ) : VolumePolynomials.Space k ≃L[ℝ] InnerBase k :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm

theorem planeToInner_preserving : MeasurePreserving planeToInner :=
  WithLp.volume_preserving_toLp ℝ ℝ

theorem baseToInner_preserving (k : ℕ) : MeasurePreserving (baseToInner k) :=
  PiLp.volume_preserving_toLp (Fin k)

def innerTotal {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    ConvexBody (InnerPlane × InnerBase k) :=
  mapBody (planeToInner.prodCongr (baseToInner k)).toContinuousLinearMap F

theorem innerTotal_projection {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    projection (innerTotal F) = baseToInner k '' projection F :=
  projection_map_prodEquiv planeToInner (baseToInner k) F

theorem innerTotal_fiber {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k))
    {y : VolumePolynomials.Space k} (hy : y ∈ projection F) :
    fiberBody (innerTotal F) (baseToInner k y) =
      mapBody planeToInner.toContinuousLinearMap (fiberBody F y) :=
  fiberBody_map_prodEquiv planeToInner (baseToInner k) F hy

theorem innerTotal_area {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k))
    {y : VolumePolynomials.Space k} (hy : y ∈ projection F) :
    volume.real (fiberBody (innerTotal F) (baseToInner k y) : Set InnerPlane) =
      volume.real (fiberBody F y : Set Plane) := by
  first
  | rw [innerTotal_fiber F hy]
    exact measureReal_image_measurePreserving volume volume planeToInner
      planeToInner_preserving _

theorem fiber_functional_integrable {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) (φ : MinkowskiFunctional Plane) :
    IntegrableOn (fun y => φ (fiberBody F y)) (projection F) := by
  first
  | obtain ⟨R, hR⟩ := fibers_uniformly_bounded (innerTotal F)
    let ψ := φ.comp_mapBody planeToInner.symm.toContinuousLinearMap
    have h := functional_fiber_integrable (projection_compact (innerTotal F))
      (fiberBody_concave (innerTotal F)) hR ψ
    rw [innerTotal_projection] at h
    have hi := ((baseToInner_preserving k).integrableOn_image
      (baseToInner k).toHomeomorph.measurableEmbedding).mp h
    apply hi.congr_fun _ (projection_compact F).measurableSet
    intro y hy
    change φ (mapBody planeToInner.symm.toContinuousLinearMap
      (fiberBody (innerTotal F) (baseToInner k y))) = φ (fiberBody F y)
    rw [innerTotal_fiber F hy, mapBody_equiv_symm]

theorem projection_zero_base (F : ConvexBody (Plane × VolumePolynomials.Space 0)) :
    projection F = Set.univ := by
  first
  | apply Set.eq_univ_of_forall
    intro y
    obtain ⟨p, hp⟩ := F.nonempty
    refine ⟨p, hp, ?_⟩
    funext i
    exact Fin.elim0 i

theorem uniformAverage_zero_base (F : ConvexBody (Plane × VolumePolynomials.Space 0))
    (f : VolumePolynomials.Space 0 → ℝ) : uniformAverage (projection F) f = f 0 := by
  first
  | rw [projection_zero_base, uniformAverage, Measure.restrict_univ,
      Measure.volume_pi_eq_dirac (0 : VolumePolynomials.Space 0)]
    simp only [integral_dirac, measureReal_def, Measure.dirac_apply_of_mem (Set.mem_univ _),
      ENNReal.toReal_one, div_one]

/-- Lemma 6.1 in the literal coordinate spaces, including the exact
zero-dimensional case. The base dimension is unrestricted. -/
theorem planar_average_coordinates (k : ℕ)
    (F : ConvexBody (Plane × VolumePolynomials.Space k))
    (hvol : 0 < volume.real (projection F)) :
    ∃ A : ConvexBody Plane,
      (∀ φ : MinkowskiFunctional Plane,
        φ A = uniformAverage (projection F) (fun y => φ (fiberBody F y))) ∧
      uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)) /
        berwaldConstant k ≤ volume.real (A : Set Plane) ∧
      (k = 0 → volume.real (A : Set Plane) =
        uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane))) := by
  first
  | by_cases hk : k = 0
    · subst k
      refine ⟨fiberBody F 0, ?_, ?_, ?_⟩
      · intro φ
        rw [uniformAverage_zero_base]
      · rw [uniformAverage_zero_base]
        norm_num [berwaldConstant]
      · intro _
        rw [uniformAverage_zero_base]
    have hbase : 0 < finrank ℝ (InnerBase k) := by
      first
      | simpa only [InnerBase, finrank_euclideanSpace, Fintype.card_fin] using Nat.pos_of_ne_zero hk
    have hdim : finrank ℝ InnerPlane = 2 := by
      first
      | rw [(WithLp.linearEquiv 2 ℝ Plane).finrank_eq]
        exact PlanarCorner.plane_finrank
    have hvol' : 0 < volume.real (projection (innerTotal F)) := by
      first
      | rw [innerTotal_projection,
          measureReal_image_measurePreserving volume volume (baseToInner k) (baseToInner_preserving k)]
        exact hvol
    obtain ⟨A', hA', harea⟩ := planar_average_area hdim hbase (innerTotal F) hvol'
    let A := mapBody planeToInner.symm.toContinuousLinearMap A'
    have hAreaA : volume.real (A : Set Plane) = volume.real (A' : Set InnerPlane) :=
      measureReal_image_measurePreserving volume volume planeToInner.symm
        (MeasurePreserving.symm planeToInner.toHomeomorph.toMeasurableEquiv planeToInner_preserving) _
    have hmean : uniformAverage (projection (innerTotal F))
        (fun y => volume.real (fiberBody (innerTotal F) y : Set InnerPlane)) =
        uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)) := by
      first
      | rw [innerTotal_projection, uniformAverage_image_measurePreserving
          (baseToInner k) (baseToInner_preserving k)]
        unfold uniformAverage
        congr 1
        apply setIntegral_congr_fun (projection_compact F).measurableSet
        exact fun y hy => innerTotal_area F hy
    refine ⟨A, ?_, ?_, fun he => (hk he).elim⟩
    · intro φ
      have h := hA' (φ.comp_mapBody planeToInner.symm.toContinuousLinearMap)
      change φ A = uniformAverage (projection (innerTotal F))
        (fun y => φ (mapBody planeToInner.symm.toContinuousLinearMap (fiberBody (innerTotal F) y))) at h
      rw [innerTotal_projection, uniformAverage_image_measurePreserving
        (baseToInner k) (baseToInner_preserving k)] at h
      refine h.trans ?_
      unfold uniformAverage
      congr 1
      apply setIntegral_congr_fun (projection_compact F).measurableSet
      intro y hy
      change φ (mapBody planeToInner.symm.toContinuousLinearMap
        (fiberBody (innerTotal F) (baseToInner k y))) = φ (fiberBody F y)
      rw [innerTotal_fiber F hy, mapBody_equiv_symm]
    · rw [hAreaA]
      rw [hmean] at harea
      simpa only [InnerBase, finrank_euclideanSpace, Fintype.card_fin,
        div_eq_mul_inv, mul_comm] using harea

end PlanarInteraction
end VolumePolynomials
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarFiberAverage.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarNormalization.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Normalizing the six repeated coefficients

The scalar `M` is the actual positive factor from the coordinate Jacobian
and the volume of the quotient projection. The six equations retain that
factor. One diagonal map normalizes all three bodies simultaneously, and
its determinant gives the exact transformation of the triple mixed volume.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges

def diagonalSpace (l a c : ℝ) : Space →L[ℝ] Space :=
  (l • ContinuousLinearMap.id ℝ ℝ).prodMap (diagonalLinear a c)

@[simp] theorem diagonalSpace_apply (l a c : ℝ) (p : Space) :
    diagonalSpace l a c p = (l * p.1, (a * p.2.1, c * p.2.2)) := by
  first
  | change (l * p.1, diagonalLinear a c p.2) = _
    rw [diagonalLinear_apply]

@[simp] theorem diagonalSpace_det (l a c : ℝ) :
    LinearMap.det (diagonalSpace l a c).toLinearMap = l * (a * c) := by
  first
  | change LinearMap.det ((l • LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
      (diagonalLinear a c).toLinearMap) = _
    rw [LinearMap.det_prodMap, diagonalLinear_det]
    simp

theorem diagonalSpace_XY (l a c : ℝ) (A : ConvexBody Plane) :
    mapBody (diagonalSpace l a c) (mapBody embedXY A) =
      mapBody embedXY (mapBody (diagonalLinear a c) A) := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    congr 1
    funext p
    simp only [Function.comp_apply, diagonalSpace_apply, diagonalLinear_apply, embedXY]
    simp

theorem diagonalSpace_YZ (l a c : ℝ) (B : ConvexBody Plane) :
    mapBody (diagonalSpace l a c) (mapBody embedYZ B) =
      mapBody embedYZ (mapBody (diagonalLinear c l) B) := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    congr 1
    funext p
    simp only [Function.comp_apply, diagonalSpace_apply, diagonalLinear_apply, embedYZ]
    simp

theorem diagonalSpace_XZ (l a c : ℝ) (C : ConvexBody Plane) :
    mapBody (diagonalSpace l a c) (mapBody embedXZ C) =
      mapBody embedXZ (mapBody (diagonalLinear a l) C) := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    congr 1
    funext p
    simp only [Function.comp_apply, diagonalSpace_apply, diagonalLinear_apply, embedXZ]
    simp

/-- Determinant transport for the three distinct coordinate planes,
including singular diagonal maps. -/
theorem triple_diagonal (l a c : ℝ) (A B C : ConvexBody Plane) :
    triple (mapBody (diagonalLinear a c) A)
      (mapBody (diagonalLinear c l) B) (mapBody (diagonalLinear a l) C) =
      |l * (a * c)| * triple A B C := by
  first
  | have h := mixedVolume_map_linear volume (diagonalSpace l a c)
      ![mapBody embedXY A, mapBody embedYZ B, mapBody embedXZ C]
    have heq : (fun i : Fin 3 => mapBody (diagonalSpace l a c)
        (![mapBody embedXY A, mapBody embedYZ B, mapBody embedXZ C] i)) =
        ![mapBody embedXY (mapBody (diagonalLinear a c) A),
          mapBody embedYZ (mapBody (diagonalLinear c l) B),
          mapBody embedXZ (mapBody (diagonalLinear a l) C)] := by
      first
      | funext i
        fin_cases i
        · exact diagonalSpace_XY l a c A
        · exact diagonalSpace_YZ l a c B
        · exact diagonalSpace_XZ l a c C
    simpa only [heq, diagonalSpace_det, triple, mixed3] using h

def normalizeA (a c : ℝ) (A : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear a⁻¹ c⁻¹) A

def normalizeB (c l : ℝ) (B : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear c⁻¹ l⁻¹) B

def normalizeC (a l : ℝ) (C : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear a⁻¹ l⁻¹) C

/-- These are literal coefficient equalities, with no abstract mixed-volume
operation. In the lifted case `τ` is the mean fiber area and `κ = cₖ`.
In the cubic case `τ = area A` and `κ = 1`. -/
structure RepeatedCoefficientData (α s z κ : ℝ) where
  A : ConvexBody Plane
  B : ConvexBody Plane
  C : ConvexBody Plane
  M : ℝ
  τ : ℝ
  M_pos : 0 < M
  τ_nonneg : 0 ≤ τ
  AAB : M * τ * height B = 3 * κ * α
  AAC : M * τ * height C = 3 * κ * α
  BBA : M * volume.real (B : Set Plane) * width A = 3
  BBC : M * volume.real (B : Set Plane) * width C = 3
  CCA : M * volume.real (C : Set Plane) * height A = 3 * s
  CCB : M * volume.real (C : Set Plane) * width B = 3
  area_lower : τ / κ ≤ volume.real (A : Set Plane)
  ABC : M * (6 * triple A B C) = 6 * z

structure NormalizedPlanarData (α s z : ℝ) where
  A : ConvexBody Plane
  B : ConvexBody Plane
  C : ConvexBody Plane
  T : ℝ
  T_pos : 0 < T
  A_width : width A = 1
  A_height : height A = s
  A_area : α * T ≤ volume.real (A : Set Plane)
  B_width : width B = 1
  B_height : height B = 1
  C_width : width C = 1
  C_height : height C = 1
  B_area : volume.real (B : Set Plane) = T
  C_area : volume.real (C : Set Plane) = T
  triple_value : 6 * triple A B C = 2 * T * z

theorem RepeatedCoefficientData.positive_factors {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    0 < width D.A ∧ 0 < width D.B ∧ 0 < height D.B ∧ 0 < D.τ := by
  first
  | have ha : 0 < width D.A := by
      first
      | by_contra! h
        have hz : width D.A = 0 := le_antisymm h measureReal_nonneg
        have he := D.BBA
        rw [hz, mul_zero] at he
        norm_num at he
    have hc : 0 < width D.B := by
      first
      | by_contra! h
        have hz : width D.B = 0 := le_antisymm h measureReal_nonneg
        have he := D.CCB
        rw [hz, mul_zero] at he
        norm_num at he
    have hτ : 0 < D.τ := by
      first
      | by_contra! h
        have hz : D.τ = 0 := le_antisymm h D.τ_nonneg
        have he := D.AAB
        rw [hz, mul_zero, zero_mul] at he
        have : 0 < 3 * κ * α := by positivity
        linarith
    have hl : 0 < height D.B := by
      first
      | by_contra! h
        have hz : height D.B = 0 := le_antisymm h measureReal_nonneg
        have he := D.AAB
        rw [hz, mul_zero] at he
        have : 0 < 3 * κ * α := by positivity
        linarith
    exact ⟨ha, hc, hl, hτ⟩

theorem RepeatedCoefficientData.width_relations {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    height D.C = height D.B ∧ width D.C = width D.A ∧ height D.A = s * width D.B := by
  first
  | obtain ⟨ha, hc, hl, hτ⟩ := D.positive_factors hα hκ
    have hB : D.M * volume.real (D.B : Set Plane) ≠ 0 := by
      first
      | intro h
        have he := D.BBA
        rw [h, zero_mul] at he
        norm_num at he
    have hC : D.M * volume.real (D.C : Set Plane) ≠ 0 := by
      first
      | intro h
        have he := D.CCB
        rw [h, zero_mul] at he
        norm_num at he
    refine ⟨mul_left_cancel₀ (mul_ne_zero D.M_pos.ne' hτ.ne')
      (D.AAC.trans D.AAB.symm), mul_left_cancel₀ hB (D.BBC.trans D.BBA.symm), ?_⟩
    apply mul_left_cancel₀ hC
    calc
      _ = 3 * s := D.CCA
      _ = s * (D.M * volume.real (D.C : Set Plane) * width D.B) := by rw [D.CCB]; ring
      _ = _ := by ring

def normalizationScale {α s z κ : ℝ} (D : RepeatedCoefficientData α s z κ) : ℝ :=
  3 / (D.M * width D.A * width D.B * height D.B)

theorem normalizationScale_pos {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    0 < normalizationScale D := by
  first
  | obtain ⟨ha, hc, hl, _⟩ := D.positive_factors hα hκ
    exact div_pos (by norm_num) (mul_pos (mul_pos (mul_pos D.M_pos ha) hc) hl)

theorem RepeatedCoefficientData.normalized_area_identities {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    volume.real (normalizeB (width D.B) (height D.B) D.B : Set Plane) = normalizationScale D ∧
    volume.real (normalizeC (width D.A) (height D.B) D.C : Set Plane) = normalizationScale D ∧
    D.τ / κ / (width D.A * width D.B) = α * normalizationScale D := by
  first
  | obtain ⟨ha, hc, hl, hτ⟩ := D.positive_factors hα hκ
    have hBa := D.BBA
    have hCb := D.CCB
    have hAa := D.AAB
    constructor
    · rw [normalizeB, area_mapBody, diagonalLinear_det,
        abs_of_pos (mul_pos (inv_pos.mpr hc) (inv_pos.mpr hl))]
      unfold normalizationScale
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne']
      nlinarith [congrArg (fun x : ℝ => x * height D.B * width D.B) hBa]
    constructor
    · rw [normalizeC, area_mapBody, diagonalLinear_det,
        abs_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hl))]
      unfold normalizationScale
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne']
      nlinarith [congrArg (fun x : ℝ => x * height D.B * width D.A) hCb]
    · unfold normalizationScale
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne', hκ.ne']
      nlinarith [congrArg (fun x : ℝ => x * width D.A * width D.B) hAa]

/-- The same diagonal normalization proves the cubic statement and the
averaged higher-dimensional statement, without discarding its Jacobian. -/
def RepeatedCoefficientData.normalize {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    NormalizedPlanarData α s z := by
  first
  | obtain ⟨ha, hc, hl, hτ⟩ := D.positive_factors hα hκ
    obtain ⟨hf, he, hb⟩ := D.width_relations hα hκ
    obtain ⟨hBa, hCa, hAa⟩ := D.normalized_area_identities hα hκ
    refine ⟨normalizeA (width D.A) (width D.B) D.A,
      normalizeB (width D.B) (height D.B) D.B,
      normalizeC (width D.A) (height D.B) D.C,
      normalizationScale D, normalizationScale_pos D hα hκ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hBa, hCa, ?_⟩
    · rw [normalizeA, width_map_diagonal, abs_of_pos (inv_pos.mpr ha), inv_mul_cancel₀ ha.ne']
    · rw [normalizeA, height_map_diagonal, abs_of_pos (inv_pos.mpr hc), hb]
      field_simp [hc.ne']
    · rw [normalizeA, area_mapBody, diagonalLinear_det,
        abs_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hc)), ← hAa]
      have h := div_le_div_of_nonneg_right D.area_lower (mul_pos ha hc).le
      simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h
    · rw [normalizeB, width_map_diagonal, abs_of_pos (inv_pos.mpr hc), inv_mul_cancel₀ hc.ne']
    · rw [normalizeB, height_map_diagonal, abs_of_pos (inv_pos.mpr hl), inv_mul_cancel₀ hl.ne']
    · rw [normalizeC, width_map_diagonal, abs_of_pos (inv_pos.mpr ha), he, inv_mul_cancel₀ ha.ne']
    · rw [normalizeC, height_map_diagonal, abs_of_pos (inv_pos.mpr hl), hf, inv_mul_cancel₀ hl.ne']
    · rw [normalizeA, normalizeB, normalizeC, triple_diagonal,
        abs_of_pos (mul_pos (inv_pos.mpr hl) (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hc)))]
      unfold normalizationScale
      have habc := D.ABC
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne']
      nlinarith [congrArg (fun x : ℝ => x * width D.A * width D.B * height D.B) habc]

theorem RepeatedCoefficientData.normalize_area_eq {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ)
    (harea : volume.real (D.A : Set Plane) = D.τ / κ) :
    volume.real ((D.normalize hα hκ).A : Set Plane) = α * (D.normalize hα hκ).T := by
  first
  | obtain ⟨ha, hc, hl, _⟩ := D.positive_factors hα hκ
    change volume.real (normalizeA (width D.A) (width D.B) D.A : Set Plane) =
      α * normalizationScale D
    rw [normalizeA, area_mapBody, diagonalLinear_det,
      abs_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hc)), harea,
      ← (D.normalized_area_identities hα hκ).2.2]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarNormalization.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarCubicVolume.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The complete seven-term volume polynomial in the coordinate planes,
and the converse direction of Proposition 3.1 with an actual common dilation. -/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges

theorem repeated_XY_XY_YZ (A B : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedXY A) (mapBody embedYZ B) =
      volume.real (A : Set Plane) * height B := by
  first
  | let A' := mapBody embedXY A
    let B' := mapBody embedYZ B
    have h := cubic_volume_expansion B' A' (by norm_num : (0 : ℝ) ≤ 1)
    have hv := volume_XY_YZ A B
    have hr := repeated_XY_YZ A B
    rw [show volume.real (A' : Set Space) = 0 from volume_embedXY A,
      show volume.real (B' : Set Space) = 0 from volume_embedYZ B] at h
    simp only [ConvexBody.coe_add, ConvexBody.coe_smul, one_smul, one_pow,
      mul_one, mul_zero, add_zero, zero_add] at h
    have hBAA : mixed3 B' A' A' = mixed3 A' A' B' := by
      first
      | rw [mixed3_swap_first B' A' A', mixed3_swap_last A' B' A']
    have hBBA : mixed3 B' B' A' = mixed3 A' B' B' := by
      first
      | rw [mixed3_swap_last B' B' A', mixed3_swap_first B' A' B']
    rw [hBAA, hBBA] at h
    change volume.real (A' + B' : Set Space) = _ at hv
    change 3 * mixed3 A' B' B' = _ at hr
    change 3 * mixed3 A' A' B' = _
    linarith

theorem repeated_XY_XY_XZ (A C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedXY A) (mapBody embedXZ C) =
      volume.real (A : Set Plane) * height C := by
  first
  | let A' := mapBody embedXY A
    let C' := mapBody embedXZ C
    have h := cubic_volume_expansion C' A' (by norm_num : (0 : ℝ) ≤ 1)
    have hv := volume_XY_XZ A C
    have hr := repeated_XY_XZ A C
    rw [show volume.real (A' : Set Space) = 0 from volume_embedXY A,
      show volume.real (C' : Set Space) = 0 from volume_embedXZ C] at h
    simp only [ConvexBody.coe_add, ConvexBody.coe_smul, one_smul, one_pow,
      mul_one, mul_zero, add_zero, zero_add] at h
    have hCAA : mixed3 C' A' A' = mixed3 A' A' C' := by
      first
      | rw [mixed3_swap_first C' A' A', mixed3_swap_last A' C' A']
    have hCCA : mixed3 C' C' A' = mixed3 A' C' C' := by
      first
      | rw [mixed3_swap_last C' C' A', mixed3_swap_first C' A' C']
    rw [hCAA, hCCA] at h
    change volume.real (A' + C' : Set Space) = _ at hv
    change 3 * mixed3 A' C' C' = _ at hr
    change 3 * mixed3 A' A' C' = _
    linarith

theorem reframeX_YZ (B : ConvexBody Plane) :
    mapBody reframeX.toContinuousLinearMap (mapBody embedYZ B) = mapBody embedXY B := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    rfl

theorem reframeX_XZ (C : ConvexBody Plane) :
    mapBody reframeX.toContinuousLinearMap (mapBody embedXZ C) = mapBody embedYZ (swapBody C) := by
  first
  | apply ConvexBody.ext
    simp only [swapBody, coe_mapBody, Set.image_image]
    rfl

theorem swapBody_height (C : ConvexBody Plane) : height (swapBody C) = width C := by
  first
  | change volume.real (PlanarExtrusion.projection (swapBody C : Set Plane)) = width C
    rw [swapBody_projection]
    rfl

theorem repeated_YZ_YZ_XZ (B C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXZ C) =
      volume.real (B : Set Plane) * width C := by
  first
  | have h := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXZ C)
    rw [reframeX_YZ, reframeX_XZ] at h
    rw [← h, repeated_XY_XY_YZ, swapBody_height]

theorem repeated_YZ_XZ_XZ (B C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedYZ B) (mapBody embedXZ C) (mapBody embedXZ C) =
      volume.real (C : Set Plane) * width B := by
  first
  | have h := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedYZ B) (mapBody embedXZ C) (mapBody embedXZ C)
    rw [reframeX_YZ, reframeX_XZ] at h
    rw [← h, repeated_XY_YZ, swapBody_area]

def coordinateVolume (A B C : ConvexBody Plane) (t : Fin 3 → ℝ) : ℝ :=
  volume.real (t 0 • mapBody embedXY A + t 1 • mapBody embedYZ B +
    t 2 • mapBody embedXZ C : Set Space)

/-- Every coefficient is expressed in literal area, width, or mixed volume. -/
theorem coordinate_volume_formula (A B C : ConvexBody Plane)
    (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    coordinateVolume A B C t =
      t 0 ^ 2 * t 1 * (volume.real (A : Set Plane) * height B) +
      t 0 ^ 2 * t 2 * (volume.real (A : Set Plane) * height C) +
      t 0 * t 1 ^ 2 * (volume.real (B : Set Plane) * width A) +
      t 1 ^ 2 * t 2 * (volume.real (B : Set Plane) * width C) +
      t 0 * t 2 ^ 2 * (volume.real (C : Set Plane) * height A) +
      t 1 * t 2 ^ 2 * (volume.real (C : Set Plane) * width B) +
      t 0 * t 1 * t 2 * (6 * triple A B C) := by
  first
  | have h := trivariate_volume_formula_planar volume space_finrank
      (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      (volume_embedXY A) (volume_embedYZ B) (volume_embedXZ C) (ht 0) (ht 1) (ht 2)
    have hBAA : mixed3 (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXY A) =
        mixed3 (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedYZ B) := by
      first
      | rw [mixed3_swap_last (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXY A),
          mixed3_swap_first (mapBody embedYZ B) (mapBody embedXY A)]
    have hCAA : mixed3 (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedXY A) =
        mixed3 (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedXZ C) := by
      first
      | rw [mixed3_swap_last (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedXY A),
          mixed3_swap_first (mapBody embedXZ C) (mapBody embedXY A)]
    have hCCB : mixed3 (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedYZ B) =
        mixed3 (mapBody embedYZ B) (mapBody embedXZ C) (mapBody embedXZ C) := by
      first
      | rw [mixed3_swap_last (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedYZ B),
          mixed3_swap_first (mapBody embedXZ C) (mapBody embedYZ B)]
    change coordinateVolume A B C t = _ at h
    change mixed3 _ _ _ = _ at hBAA hCAA hCCB
    simp only [show mixedVolume3 (volume : Measure Space) = mixed3 from rfl] at h
    rw [hBAA, hCAA, hCCB] at h
    rw [h]
    have h1 := repeated_XY_XY_YZ A B
    have h2 := repeated_XY_XY_XZ A C
    have h3 := repeated_XY_YZ A B
    have h4 := repeated_YZ_YZ_XZ B C
    have h5 := repeated_XY_XZ A C
    have h6 := repeated_YZ_XZ_XZ B C
    dsimp only [triple]
    linear_combination t 0 ^ 2 * t 1 * h1 + t 0 ^ 2 * t 2 * h2 +
      t 0 * t 1 ^ 2 * h3 + t 1 ^ 2 * t 2 * h4 +
      t 0 * t 2 ^ 2 * h5 + t 1 * t 2 ^ 2 * h6

def coordinateEquiv : VolumePolynomials.Space 3 ≃L[ℝ] Space :=
  (Holonomy.coordinateExtract 0).toContinuousLinearEquiv

theorem coordinateEquiv_measurePreserving : MeasurePreserving coordinateEquiv :=
  Holonomy.coordinateExtract_measurePreserving 0

def cubicTuple (A B C : ConvexBody Plane) : Fin 3 → Body 3 :=
  fun i => mapBody coordinateEquiv.symm.toContinuousLinearMap
    (![mapBody embedXY A, mapBody embedYZ B, mapBody embedXZ C] i)

theorem volumeFunction_cubicTuple (A B C : ConvexBody Plane)
    (t : Fin 3 → ℝ) :
    volumeFunction (cubicTuple A B C) t = coordinateVolume A B C t := by
  first
  | have hsum : weightedSum (cubicTuple A B C) t =
        mapBody coordinateEquiv.symm.toContinuousLinearMap
          (t 0 • mapBody embedXY A + t 1 • mapBody embedYZ B + t 2 • mapBody embedXZ C) := by
      first
      | simp only [weightedSum, cubicTuple, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          mapBody_add, mapBody_smul]
    rw [volumeFunction, hsum]
    exact measureReal_image_measurePreserving volume volume coordinateEquiv.symm
      (MeasurePreserving.symm coordinateEquiv.toHomeomorph.toMeasurableEquiv
        coordinateEquiv_measurePreserving) _

theorem normalized_coordinate_volume {α s z : ℝ} (D : NormalizedPlanarData α s z)
    (harea : volume.real (D.A : Set Plane) = α * D.T)
    (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    coordinateVolume D.A D.B D.C t = D.T / 3 * CubicSlice.value α s z t := by
  first
  | rw [coordinate_volume_formula _ _ _ t ht, harea, D.B_area, D.C_area,
      D.A_width, D.A_height, D.B_width, D.B_height, D.C_width, D.C_height, D.triple_value]
    dsimp only [CubicSlice.value]
    ring

theorem normalized_cubic_realizes {α s z : ℝ} (D : NormalizedPlanarData α s z)
    (harea : volume.real (D.A : Set Plane) = α * D.T) :
    Realizes (cubicTuple D.A D.B D.C) ((D.T / 3) • CubicSlice.coefficients α s z) := by
  first
  | intro t ht
    rw [evaluate_smul, CubicSlice.evaluate_coefficients, volumeFunction_cubicTuple,
      normalized_coordinate_volume D harea t ht]

def cubicDilation {α s z : ℝ} (D : NormalizedPlanarData α s z) : ℝ :=
  (3 / D.T) ^ ((3 : ℝ)⁻¹)

theorem normalized_mem_volumeLocus {α s z : ℝ} (D : NormalizedPlanarData α s z)
    (harea : volume.real (D.A : Set Plane) = α * D.T) :
    CubicSlice.coefficients α s z ∈ VolumeLocus 3 3 := by
  first
  | have hbase : 0 ≤ 3 / D.T := (div_pos (by norm_num) D.T_pos).le
    have hr : 0 ≤ cubicDilation D := Real.rpow_nonneg hbase _
    have hp : cubicDilation D ^ 3 = 3 / D.T :=
      Real.rpow_inv_natCast_pow hbase (by decide)
    have h := (normalized_cubic_realizes D harea).dilate hr
    rw [hp, smul_smul, show 3 / D.T * (D.T / 3) = 1 by field_simp [D.T_pos.ne'], one_smul] at h
    exact ⟨fun i => cubicDilation D • cubicTuple D.A D.B D.C i, h⟩

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 14
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarCubicVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/HigherLiftCoordinates.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# From independent planes to the literal planar integral

The first coordinate of the three-dimensional frame is the `z` coordinate.
Dropping that coordinate on the first body's fibers gives an actual compact
convex total set in `Plane × Space k`. Fubini transports the original
volume identity, retaining the positive Haar factor of the plane frame.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

open ConvexFibers FiberVolume PlanarExtrusion

def planarTotalMap (k : ℕ)
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) :
    (Space 3 × Space k) →L[ℝ] (Plane × Space k) :=
  ((ContinuousLinearMap.snd ℝ ℝ Plane).comp S.toContinuousLinearMap).prodMap
    (ContinuousLinearMap.id ℝ (Space k))

@[simp] theorem planarTotalMap_apply (k : ℕ)
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) (p : Space 3 × Space k) :
    planarTotalMap k S p = ((S p.1).2, p.2) := rfl

def extractYZ : PlanarInteraction.Space →L[ℝ] Plane :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)).prod
    (ContinuousLinearMap.fst ℝ ℝ Plane)

def extractXZ : PlanarInteraction.Space →L[ℝ] Plane :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)).prod
    (ContinuousLinearMap.fst ℝ ℝ Plane)

@[simp] theorem extractYZ_apply (p : PlanarInteraction.Space) : extractYZ p = (p.2.2, p.1) := rfl
@[simp] theorem extractXZ_apply (p : PlanarInteraction.Space) : extractXZ p = (p.2.1, p.1) := rfl

theorem projection_planarTotal {k : ℕ}
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) (F : ConvexBody (Space 3 × Space k)) :
    projection (mapBody (planarTotalMap k S) F) = projection F := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hpy⟩
      exact ⟨p, hp, hpy⟩
    · rintro ⟨p, hp, hpy⟩
      exact ⟨planarTotalMap k S p, ⟨p, hp, rfl⟩, hpy⟩

theorem map_fiberBody_planarTotal {k : ℕ}
    (S : Space 3 ≃L[ℝ] PlanarInteraction.Space) (F : ConvexBody (Space 3 × Space k))
    (hflat : ∀ p ∈ F, (S p.1).1 = 0) {y : Space k} (hy : y ∈ projection F) :
    mapBody S.toContinuousLinearMap (fiberBody F y) =
      mapBody PlanarInteraction.embedXY (fiberBody (mapBody (planarTotalMap k S) F) y) := by
  first
  | have hy' : y ∈ projection (mapBody (planarTotalMap k S) F) := by
      first
      | rwa [projection_planarTotal]
    apply ConvexBody.ext
    rw [coe_mapBody, coe_mapBody, coe_fiberBody F hy,
      coe_fiberBody (mapBody (planarTotalMap k S) F) hy']
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(S x).2, ?_, ?_⟩
      · exact ⟨(x, y), hx, rfl⟩
      · apply Prod.ext
        · exact (hflat (x, y) hx).symm
        · rfl
    · rintro ⟨x, ⟨⟨p, u⟩, hpu, hmap⟩, rfl⟩
      have hu : u = y := congrArg Prod.snd hmap
      subst u
      refine ⟨p, hpu, ?_⟩
      apply Prod.ext
      · exact hflat (p, y) hpu
      · exact congrArg Prod.fst hmap

theorem map_body_YZ (S : Space 3 ≃L[ℝ] PlanarInteraction.Space)
    (B : Body 3) (hB : ∀ x ∈ B, (S x).2.1 = 0) :
    mapBody S.toContinuousLinearMap B =
      mapBody PlanarInteraction.embedYZ (mapBody (extractYZ.comp S.toContinuousLinearMap) B) := by
  first
  | apply ConvexBody.ext
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨extractYZ (S x), ⟨x, hx, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext (hB x hx).symm rfl
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext (hB x hx) rfl

theorem map_body_XZ (S : Space 3 ≃L[ℝ] PlanarInteraction.Space)
    (C : Body 3) (hC : ∀ x ∈ C, (S x).2.2 = 0) :
    mapBody S.toContinuousLinearMap C =
      mapBody PlanarInteraction.embedXZ (mapBody (extractXZ.comp S.toContinuousLinearMap) C) := by
  first
  | apply ConvexBody.ext
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨extractXZ (S x), ⟨x, hx, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext rfl (hC x hx).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply Prod.ext
      · rfl
      · exact Prod.ext rfl (hC x hx)

structure CoordinateFiberData (k : ℕ) (α s z : ℝ) where
  F : ConvexBody (Plane × Space k)
  B : ConvexBody Plane
  C : ConvexBody Plane
  J : ℝ
  J_pos : 0 < J
  projection_pos : 0 < volume.real (projection F)
  integral_identity : ∀ t : Fin 3 → ℝ, (∀ i, 0 < t i) →
    J * (∫ y in projection F, PlanarInteraction.coordinateVolume (fiberBody F y) B C t) =
      CubicSlice.value (correction k * α) s z t

theorem FiberFrameData.exists_coordinateFiberData {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) (htrans : D.P 0 ⊓ D.P 1 ⊓ D.P 2 = ⊥) :
    Nonempty (CoordinateFiberData k α s z) := by
  first
  | classical
    obtain ⟨T, hT⟩ := PlaneCoordinates.exists_plane_coordinates
      (by simp [Space] : finrank ℝ (Space 3) = 3) D.P D.planes htrans
    let S : Space 3 ≃L[ℝ] PlanarInteraction.Space := T.trans PlanarInteraction.coordinateEquiv
    have hS0 (x : Space 3) : x ∈ D.P 0 ↔ (S x).1 = 0 := by
      first
      | change x ∈ D.P 0 ↔ T x 0 = 0
        exact hT 0 x
    have hS1 (x : Space 3) : x ∈ D.P 1 ↔ (S x).2.1 = 0 := by
      first
      | change x ∈ D.P 1 ↔ T x 1 = 0
        exact hT 1 x
    have hS2 (x : Space 3) : x ∈ D.P 2 ↔ (S x).2.2 = 0 := by
      first
      | change x ∈ D.P 2 ↔ T x 2 = 0
        exact hT 2 x
    let F := mapBody (planarTotalMap k S) D.F
    let B := mapBody (extractYZ.comp S.toContinuousLinearMap) D.B
    let C := mapBody (extractXZ.comp S.toContinuousLinearMap) D.C
    let j : ℝ := LinearFrame.volumeFactor S
    have hj : 0 < j := by exact_mod_cast LinearFrame.volumeFactor_pos S
    have hflat (p : Space 3 × Space k) (hp : p ∈ D.F) : (S p.1).1 = 0 :=
      (hS0 p.1).mp (D.fibers_in_plane p.2 hp)
    have hB := map_body_YZ S D.B (fun x hx => (hS1 x).mp (D.B_in_plane hx))
    have hC := map_body_XZ S D.C (fun x hx => (hS2 x).mp (D.C_in_plane hx))
    have hproj : projection F = projection D.F := projection_planarTotal S D.F
    refine ⟨⟨F, B, C, D.J * j, mul_pos D.J_pos hj, ?_, ?_⟩⟩
    · rw [hproj]
      exact D.projection_pos
    · intro t ht
      have hvol := D.volume_identity t (fun i => (ht i).le)
      rw [realVolume_scaled_sum_of_pos D.F (t 1 • D.B + t 2 • D.C) (ht 0),
        evaluate_coefficients] at hvol
      have hkdim : finrank ℝ (Space k) = k := by simp [Space]
      rw [hkdim] at hvol
      have hfiber (y : Space k) (hy : y ∈ projection D.F) :
          volume.real (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C) : Set (Space 3)) =
            j * PlanarInteraction.coordinateVolume (fiberBody F y) B C t := by
        first
        | have hm := LinearFrame.realVolume_eq_factor_mul_image S
            (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C) : Set (Space 3))
          have hsum : mapBody S.toContinuousLinearMap
              (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C)) =
              t 0 • mapBody PlanarInteraction.embedXY (fiberBody F y) +
                t 1 • mapBody PlanarInteraction.embedYZ B + t 2 • mapBody PlanarInteraction.embedXZ C := by
            rw [mapBody_add, mapBody_add, mapBody_smul, mapBody_smul, mapBody_smul,
              map_fiberBody_planarTotal S D.F hflat hy, hB, hC, ← add_assoc]
          have heq := congrArg (fun Q : ConvexBody PlanarInteraction.Space => volume.real (Q : Set PlanarInteraction.Space)) hsum
          exact hm.trans (congrArg (fun x : ℝ => j * x) heq)
      have hint : (∫ y in projection D.F, volume.real
          (t 0 • fiberBody D.F y + (t 1 • D.B + t 2 • D.C) : Set (Space 3))) =
          j * (∫ y in projection F, PlanarInteraction.coordinateVolume (fiberBody F y) B C t) := by
        first
        | rw [hproj, ← integral_const_mul]
          apply setIntegral_congr_fun (projection_compact D.F).measurableSet
          exact hfiber
      simp only [ConvexBody.coe_add, ConvexBody.coe_smul] at hvol
      rw [hint] at hvol
      apply mul_left_cancel₀ (pow_ne_zero k (ht 0).ne')
      calc
        t 0 ^ k * (D.J * j * _) = D.J * (t 0 ^ k * (j * _)) := by ring
        _ = _ := hvol

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HigherLiftCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/AveragedPlanarNormalization.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # Extracting the seven coefficients after actual fiber averaging

The input is the literal Fubini identity furnished by `CoordinateFiberData`.
Every fiber integral is justified. The mean body preserves widths and the
actual triple mixed-volume functional, while Berwald supplies its area
bound. Exact polynomial interpolation then recovers all six repeated
coefficients and the triple coefficient, retaining the common positive
Jacobian times projection-volume factor.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarCorner PlanarEdges ConvexFibers

def horizontalWidthFunctional : MinkowskiFunctional Plane :=
  MinkowskiFunctional.width (ContinuousLinearMap.fst ℝ ℝ ℝ)

def verticalWidthFunctional : MinkowskiFunctional Plane :=
  MinkowskiFunctional.width (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem horizontalWidthFunctional_apply (A : ConvexBody Plane) :
    horizontalWidthFunctional A = width A := by
  first
  | exact (image_length_eq_support A (ContinuousLinearMap.fst ℝ ℝ ℝ)).symm

@[simp] theorem verticalWidthFunctional_apply (A : ConvexBody Plane) :
    verticalWidthFunctional A = height A := by
  first
  | exact (image_length_eq_support A (ContinuousLinearMap.snd ℝ ℝ ℝ)).symm

def sevenTermValue (a : Fin 7 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  t 0 ^ 2 * t 1 * a 0 + t 0 ^ 2 * t 2 * a 1 +
  t 0 * t 1 ^ 2 * a 2 + t 1 ^ 2 * t 2 * a 3 +
  t 0 * t 2 ^ 2 * a 4 + t 1 * t 2 ^ 2 * a 5 + t 0 * t 1 * t 2 * a 6

/-- Exact linear independence of all seven monomials, for arbitrary real
coefficients. The rational interpolation identities are proved in the
kernel; this is a polynomial identity theorem, not a numerical test of a
geometric statement. -/
theorem sevenTermValue_injective {a b : Fin 7 → ℝ}
    (h : ∀ t : Fin 3 → ℝ, (∀ i, 0 < t i) → sevenTermValue a t = sevenTermValue b t) :
    a = b := by
  first
  | have h111 := h ![1, 1, 1] (by intro i; fin_cases i <;> norm_num)
    have h112 := h ![1, 1, 2] (by intro i; fin_cases i <;> norm_num)
    have h113 := h ![1, 1, 3] (by intro i; fin_cases i <;> norm_num)
    have h121 := h ![1, 2, 1] (by intro i; fin_cases i <;> norm_num)
    have h122 := h ![1, 2, 2] (by intro i; fin_cases i <;> norm_num)
    have h123 := h ![1, 2, 3] (by intro i; fin_cases i <;> norm_num)
    have h131 := h ![1, 3, 1] (by intro i; fin_cases i <;> norm_num)
    norm_num [sevenTermValue] at h111 h112 h113 h121 h122 h123 h131
    funext i
    fin_cases i
    · change a 0 = b 0
      linear_combination 6 * h111 - 6 * h112 + 2 * h113 -
        (3 / 2) * h121 + (3 / 2) * h122 - (1 / 2) * h123
    · change a 1 = b 1
      linear_combination 2 * h111 + 2 * h112 - h113 -
        (5 / 2) * h121 - h122 + (1 / 2) * h123 + h131
    · change a 2 = b 2
      linear_combination -3 * h111 + 3 * h112 - h113 +
        (3 / 2) * h121 - (3 / 2) * h122 + (1 / 2) * h123
    · change a 3 = b 3
      linear_combination (7 / 2) * h111 - 3 * h112 + h113 -
        (5 / 2) * h121 + (3 / 2) * h122 - (1 / 2) * h123 + (1 / 2) * h131
    · change a 4 = b 4
      linear_combination h111 - 2 * h112 + h113 - (1 / 2) * h121 + h122 - (1 / 2) * h123
    · change a 5 = b 5
      linear_combination -(1 / 2) * h111 + h112 - (1 / 2) * h113 +
        (1 / 2) * h121 - h122 + (1 / 2) * h123
    · change a 6 = b 6
      linear_combination -8 * h111 + 5 * h112 - (3 / 2) * h113 +
        5 * h121 - (1 / 2) * h122 - (3 / 2) * h131

def averagedCoefficients (A B C : ConvexBody Plane) (τ : ℝ) : Fin 7 → ℝ :=
  ![τ * height B, τ * height C,
    volume.real (B : Set Plane) * width A, volume.real (B : Set Plane) * width C,
    volume.real (C : Set Plane) * height A, volume.real (C : Set Plane) * width B,
    6 * triple A B C]

theorem fiber_area_integrable {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    IntegrableOn (fun y => volume.real (fiberBody F y : Set Plane)) (projection F) := by
  first
  | apply (FiberVolume.integrable_fiber_realVolume F).integrableOn.congr_fun
      (hs := (projection_compact F).measurableSet)
    intro y hy
    change volume.real (fiberSet F y) = volume.real (fiberBody F y : Set Plane)
    rw [coe_fiberBody F hy]

theorem mean_fiber_area_nonnegative {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    0 ≤ uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)) := by
  first
  | unfold uniformAverage
    exact div_nonneg (integral_nonneg (fun _ => measureReal_nonneg)) measureReal_nonneg

/-- The complete integrated cubic, with its actual mean area. Neither
fiber measurability nor integrability is an extra hypothesis. -/
theorem averaged_coordinate_volume {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) (A B C : ConvexBody Plane)
    (hvol : 0 < volume.real (projection F))
    (hA : ∀ φ : MinkowskiFunctional Plane,
      φ A = uniformAverage (projection F) (fun y => φ (fiberBody F y)))
    (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∫ y in projection F, coordinateVolume (fiberBody F y) B C t) =
      volume.real (projection F) * sevenTermValue
        (averagedCoefficients A B C
          (uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)))) t := by
  first
  | let τ := uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane))
    let a₂ := t 0 ^ 2 * t 1 * height B + t 0 ^ 2 * t 2 * height C
    let aw := t 0 * t 1 ^ 2 * volume.real (B : Set Plane)
    let ah := t 0 * t 2 ^ 2 * volume.real (C : Set Plane)
    let a₀ := t 1 ^ 2 * t 2 * (volume.real (B : Set Plane) * width C) +
      t 1 * t 2 ^ 2 * (volume.real (C : Set Plane) * width B)
    let a₃ := t 0 * t 1 * t 2
    have heval (y : VolumePolynomials.Space k) :
        coordinateVolume (fiberBody F y) B C t =
          a₂ * volume.real (fiberBody F y : Set Plane) +
            aw * width (fiberBody F y) + ah * height (fiberBody F y) +
            a₀ + a₃ * (6 * triple (fiberBody F y) B C) := by
      first
      | rw [coordinate_volume_formula _ _ _ t ht]
        dsimp only [a₂, aw, ah, a₀, a₃]
        ring
    have ha := fiber_area_integrable F
    have hw : IntegrableOn (fun y => width (fiberBody F y)) (projection F) := by
      first
      | simpa only [horizontalWidthFunctional_apply] using
          fiber_functional_integrable F horizontalWidthFunctional
    have hh : IntegrableOn (fun y => height (fiberBody F y)) (projection F) := by
      first
      | simpa only [verticalWidthFunctional_apply] using
          fiber_functional_integrable F verticalWidthFunctional
    have hv : IntegrableOn (fun y => 6 * triple (fiberBody F y) B C) (projection F) :=
      fiber_functional_integrable F (tripleFunctional B C)
    have hc : IntegrableOn (fun _ : VolumePolynomials.Space k => a₀) (projection F) :=
      integrableOn_const (projection_compact F).measure_ne_top
    have hmean (φ : MinkowskiFunctional Plane) :
        (∫ y in projection F, φ (fiberBody F y)) = volume.real (projection F) * φ A := by
      first
      | have h := hA φ
        rw [uniformAverage, eq_div_iff hvol.ne'] at h
        exact h.symm.trans (mul_comm _ _)
    have harea : (∫ y in projection F, volume.real (fiberBody F y : Set Plane)) =
        volume.real (projection F) * τ := by
      first
      | dsimp only [τ, uniformAverage]
        field_simp [hvol.ne']
    have hwidth : (∫ y in projection F, width (fiberBody F y)) =
        volume.real (projection F) * width A := by
      first
      | simpa only [horizontalWidthFunctional_apply] using hmean horizontalWidthFunctional
    have hheight : (∫ y in projection F, height (fiberBody F y)) =
        volume.real (projection F) * height A := by
      first
      | simpa only [verticalWidthFunctional_apply] using hmean verticalWidthFunctional
    have htriple : (∫ y in projection F, 6 * triple (fiberBody F y) B C) =
        volume.real (projection F) * (6 * triple A B C) := hmean (tripleFunctional B C)
    calc
      _ = ∫ y in projection F,
          a₂ * volume.real (fiberBody F y : Set Plane) +
            aw * width (fiberBody F y) + ah * height (fiberBody F y) +
            a₀ + a₃ * (6 * triple (fiberBody F y) B C) := by
        first
        | apply setIntegral_congr_fun (projection_compact F).measurableSet
          exact fun y _ => heval y
      _ = a₂ * (∫ y in projection F, volume.real (fiberBody F y : Set Plane)) +
          aw * (∫ y in projection F, width (fiberBody F y)) +
          ah * (∫ y in projection F, height (fiberBody F y)) +
          volume.real (projection F) * a₀ +
          a₃ * (∫ y in projection F, 6 * triple (fiberBody F y) B C) := by
        first
        | have h12 : IntegrableOn (fun y => a₂ * volume.real (fiberBody F y : Set Plane) +
              aw * width (fiberBody F y)) (projection F) := by
            exact Integrable.fun_add (ha.const_mul a₂) (hw.const_mul aw)
          have h123 : IntegrableOn (fun y => a₂ * volume.real (fiberBody F y : Set Plane) +
              aw * width (fiberBody F y) + ah * height (fiberBody F y)) (projection F) := by
            exact Integrable.fun_add h12 (hh.const_mul ah)
          have h1234 : IntegrableOn (fun y => a₂ * volume.real (fiberBody F y : Set Plane) +
              aw * width (fiberBody F y) + ah * height (fiberBody F y) + a₀) (projection F) := by
            exact Integrable.fun_add h123 hc
          rw [integral_add h1234 (hv.const_mul a₃), integral_add h123 hc,
            integral_add h12 (hh.const_mul ah), integral_add (ha.const_mul a₂) (hw.const_mul aw),
            integral_const_mul, integral_const_mul, integral_const_mul,
            integral_const_mul, setIntegral_const]
          rfl
      _ = _ := by
        first
        | rw [harea, hwidth, hheight, htriple]
          dsimp only [a₂, aw, ah, a₀, a₃, τ, sevenTermValue, averagedCoefficients, Matrix.cons_val]
          ring

end VolumePolynomials.PlanarInteraction

namespace VolumePolynomials.HigherLift

open PlanarExtrusion PlanarInteraction ConvexFibers

theorem CoordinateFiberData.exists_repeatedCoefficientData {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) :
    ∃ R : RepeatedCoefficientData α s z (correction k),
      (∀ φ : MinkowskiFunctional Plane,
        φ R.A = uniformAverage (projection D.F) (fun y => φ (fiberBody D.F y))) ∧
      (k = 0 → volume.real (R.A : Set Plane) = R.τ / correction k) := by
  first
  | obtain ⟨A, hA, harea, hzero⟩ := planar_average_coordinates k D.F D.projection_pos
    let τ := uniformAverage (projection D.F) (fun y => volume.real (fiberBody D.F y : Set Plane))
    let M := D.J * volume.real (projection D.F)
    have heq : (fun j : Fin 7 => M * averagedCoefficients A D.B D.C τ j) =
        ![3 * (correction k * α), 3 * (correction k * α), 3, 3, 3 * s, 3, 6 * z] := by
      first
      | apply sevenTermValue_injective
        intro t ht
        have h := D.integral_identity t ht
        rw [averaged_coordinate_volume D.F A D.B D.C D.projection_pos hA t
          (fun i => (ht i).le)] at h
        calc
          _ = D.J * (volume.real (projection D.F) *
              sevenTermValue (averagedCoefficients A D.B D.C τ) t) := by
            first
            | dsimp only [sevenTermValue, M]
              ring
          _ = CubicSlice.value (correction k * α) s z t := h
          _ = _ := by
            first
            | dsimp only [CubicSlice.value, sevenTermValue, Matrix.cons_val]
              ring
    have hcoeff (j : Fin 7) := congrFun heq j
    let R : RepeatedCoefficientData α s z (correction k) := {
      A := A
      B := D.B
      C := D.C
      M := M
      τ := τ
      M_pos := mul_pos D.J_pos D.projection_pos
      τ_nonneg := mean_fiber_area_nonnegative D.F
      AAB := by simpa [averagedCoefficients, mul_assoc] using hcoeff 0
      AAC := by simpa [averagedCoefficients, mul_assoc] using hcoeff 1
      BBA := by simpa [averagedCoefficients, mul_assoc] using hcoeff 2
      BBC := by simpa [averagedCoefficients, mul_assoc] using hcoeff 3
      CCA := by simpa [averagedCoefficients, mul_assoc] using hcoeff 4
      CCB := by simpa [averagedCoefficients, mul_assoc] using hcoeff 5
      area_lower := by simpa only [correction, berwaldConstant] using harea
      ABC := by simpa only [averagedCoefficients, Matrix.cons_val] using hcoeff 6 }
    refine ⟨R, hA, ?_⟩
    intro hk
    change volume.real (A : Set Plane) = τ / correction k
    rw [hzero hk]
    subst k
    norm_num [correction, τ]

def CoordinateFiberData.repeatedCoefficientData {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) : RepeatedCoefficientData α s z (correction k) :=
  Classical.choose D.exists_repeatedCoefficientData

theorem CoordinateFiberData.repeatedCoefficientData_average {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (φ : MinkowskiFunctional Plane) :
    φ D.repeatedCoefficientData.A =
      uniformAverage (projection D.F) (fun y => φ (fiberBody D.F y)) :=
  (Classical.choose_spec D.exists_repeatedCoefficientData).1 φ

theorem CoordinateFiberData.repeatedCoefficientData_area_zero {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (hk : k = 0) :
    volume.real (D.repeatedCoefficientData.A : Set Plane) =
      D.repeatedCoefficientData.τ / correction k :=
  (Classical.choose_spec D.exists_repeatedCoefficientData).2 hk

def CoordinateFiberData.normalize {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (hα : 0 < α) : NormalizedPlanarData α s z :=
  D.repeatedCoefficientData.normalize hα (by unfold correction; positivity)

theorem CoordinateFiberData.normalize_area_zero {k : ℕ} {α s z : ℝ}
    (D : CoordinateFiberData k α s z) (hα : 0 < α) (hk : k = 0) :
    volume.real ((D.normalize hα).A : Set Plane) = α * (D.normalize hα).T :=
  D.repeatedCoefficientData.normalize_area_eq hα (by unfold correction; positivity)
    (D.repeatedCoefficientData_area_zero hk)

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AveragedPlanarNormalization.lean -/

/- BEGIN SOURCE: VolumePolynomials/SimplexCoordinates.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Coordinate simplices and their affine height

The simplex is the actual subset of coordinate space with nonnegative
coordinates and coordinate sum at most one. Its description as a finite
convex hull is proved explicitly. The affine height is the missing
barycentric coordinate, so its positive superlevel sets are homothetic
copies of the simplex.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.SimplexCoordinates

def simplex (n : ℕ) : Set (Space n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def height {n : ℕ} (x : Space n) : ℝ := 1 - ∑ i, x i

theorem zero_mem_simplex (n : ℕ) : (0 : Space n) ∈ simplex n := by
  first
  | simp [simplex]

theorem coordinate_mem_simplex {n : ℕ} (i : Fin n) :
    (Pi.single i 1 : Space n) ∈ simplex n := by
  first
  | classical
    constructor
    · intro j
      by_cases hji : j = i <;> simp [Pi.single_apply, hji]
    · simp

theorem simplex_convex (n : ℕ) : Convex ℝ (simplex n) := by
  first
  | intro x hx y hy a b ha hb hab
    constructor
    · intro i
      exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      calc
        a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
            (mul_le_mul_of_nonneg_left hy.2 hb)
        _ = 1 := by simpa only [mul_one] using hab

theorem simplex_closed (n : ℕ) : IsClosed (simplex n) := by
  first
  | have heq : simplex n =
        (⋂ i, {x : Space n | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
      first
      | ext x
        simp [simplex]
    rw [heq]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

theorem simplex_subset_unit_box (n : ℕ) :
    simplex n ⊆ Icc (0 : Space n) (fun _ => 1) := by
  first
  | intro x hx
    exact ⟨hx.1, fun i => (Finset.single_le_sum (fun j _ => hx.1 j)
      (Finset.mem_univ i)).trans hx.2⟩

theorem simplex_compact (n : ℕ) : IsCompact (simplex n) :=
  isCompact_Icc.of_isClosed_subset (simplex_closed n) (simplex_subset_unit_box n)

def body (n : ℕ) : Body n :=
  ⟨simplex n, simplex_convex n, simplex_compact n, ⟨0, zero_mem_simplex n⟩⟩

theorem height_nonnegative {n : ℕ} {x : Space n} (hx : x ∈ simplex n) :
    0 ≤ height x := sub_nonneg.mpr hx.2

theorem height_le_one {n : ℕ} {x : Space n} (hx : x ∈ simplex n) :
    height x ≤ 1 := by
  first
  | unfold height
    exact sub_le_self _ (Finset.sum_nonneg (fun i _ => hx.1 i))

theorem continuous_height (n : ℕ) : Continuous (height : Space n → ℝ) := by
  first
  | unfold height
    fun_prop

def vertex (n : ℕ) : Fin (n + 1) → Space n :=
  Fin.cons 0 (fun i => Pi.single i 1)

theorem vertex_mem_simplex (n : ℕ) (i : Fin (n + 1)) : vertex n i ∈ simplex n := by
  first
  | cases i using Fin.cases with
    | zero => exact zero_mem_simplex n
    | succ i => exact coordinate_mem_simplex i

theorem simplex_eq_convexHull (n : ℕ) :
    simplex n = convexHull ℝ (Set.range (vertex n)) := by
  first
  | apply le_antisymm
    · intro x hx
      let w : Fin (n + 1) → ℝ := Fin.cons (height x) x
      apply mem_convexHull_of_exists_fintype w (vertex n)
      · intro i
        cases i using Fin.cases with
        | zero => exact height_nonnegative hx
        | succ i => exact hx.1 i
      · simp [w, Fin.sum_univ_succ, height]
      · intro i
        exact Set.mem_range_self i
      · ext j
        simp [w, vertex, Fin.sum_univ_succ, Finset.sum_apply, Pi.single_apply]
    · exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact vertex_mem_simplex n i)
        (simplex_convex n)

theorem simplex_finiteHull (n : ℕ) : PolytopeGeometry.IsFiniteHull (simplex n) :=
  ⟨range (vertex n), Set.finite_range _, simplex_eq_convexHull n⟩

/-- A fixed open box lies in the simplex; this proves positive ambient
volume without assuming a simplex-volume formula. -/
theorem simplex_volume_pos (n : ℕ) : 0 < volume.real (simplex n) := by
  first
  | let c : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
    have hc : 0 < c := by dsimp [c]; positivity
    have hsub : Icc (0 : Space n) (fun _ => c) ⊆ simplex n := by
      first
      | intro x hx
        refine ⟨hx.1, ?_⟩
        calc
          ∑ i, x i ≤ ∑ _ : Fin n, c := Finset.sum_le_sum (fun i _ => hx.2 i)
          _ = (n : ℝ) * c := by simp
          _ ≤ 1 := by
            dsimp [c]
            have hden : (0 : ℝ) < n + 1 := by positivity
            rw [Nat.cast_add, Nat.cast_one, ← div_eq_mul_inv]
            exact (div_le_one hden).mpr (by linarith)
    have hbox : 0 < volume.real (Icc (0 : Space n) (fun _ => c)) := by
      first
      | rw [measureReal_def, Real.volume_Icc_pi_toReal (a := (0 : Space n))
          (b := fun _ => c) (fun _ => hc.le)]
        simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        exact pow_pos hc _
    exact hbox.trans_le (measureReal_mono hsub (simplex_compact n).measure_ne_top)

theorem superlevel_eq_smul {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    {x : Space n | x ∈ simplex n ∧ t ≤ height x} = (1 - t) • simplex n := by
  first
  | have hr : 0 < 1 - t := sub_pos.mpr ht1
    ext x
    constructor
    · rintro ⟨hx, hxt⟩
      refine ⟨(1 - t)⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
      · intro i
        exact mul_nonneg (inv_nonneg.mpr hr.le) (hx.1 i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [← div_eq_inv_mul]
        apply (div_le_one hr).mpr
        dsimp only [height] at hxt
        linarith
      · change (1 - t) • ((1 - t)⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · rintro ⟨y, hy, rfl⟩
      have hsum : ∑ i, ((1 - t) • y) i = (1 - t) * ∑ i, y i := by
        first
        | simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      have hbound : (1 - t) * ∑ i, y i ≤ 1 - t := by
        first
        | simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 hr.le
      refine ⟨⟨fun i => mul_nonneg hr.le (hy.1 i), ?_⟩, ?_⟩
      · rw [hsum]
        linarith
      · unfold height
        rw [hsum]
        linarith

theorem superlevel_empty {n : ℕ} {t : ℝ} (ht : 1 < t) :
    {x : Space n | x ∈ simplex n ∧ t ≤ height x} = ∅ := by
  first
  | apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxt⟩
    exact (not_le_of_gt ht) (hxt.trans (height_le_one hx))

theorem superlevel_volume {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x} =
      (1 - t) ^ n * volume.real (simplex n) := by
  first
  | rw [superlevel_eq_smul ht0 ht1, measureReal_def,
      Measure.addHaar_smul_of_nonneg volume (sub_nonneg.mpr ht1.le),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr ht1.le) _)]
    simp only [Space, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, measureReal_def]

end VolumePolynomials.SimplexCoordinates
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SimplexCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/SimplexMoments.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The two moments of the cone height

The equalities are integrals over the actual coordinate simplex. They
follow from its homothetic superlevel sets and layer-cake integration.
The construction is valid in every dimension, including dimension zero;
no moment identity is supplied as an assumption.
-/

open Set MeasureTheory Filter

namespace VolumePolynomials.SimplexCoordinates

theorem height_moment (n p : ℕ) :
    (∫ x in simplex n, height x ^ (p + 1)) =
      (p + 1 : ℝ) * volume.real (simplex n) *
        ∫ t in Icc (0 : ℝ) 1, t ^ p * (1 - t) ^ n := by
  first
  | letI : IsFiniteMeasure (volume.restrict (simplex n)) :=
      isFiniteMeasure_restrict.mpr (simplex_compact n).measure_ne_top
    have hnonneg : 0 ≤ᵐ[volume.restrict (simplex n)] (height : Space n → ℝ) := by
      first
      | filter_upwards [ae_restrict_mem (simplex_compact n).measurableSet] with x hx
        exact height_nonnegative hx
    have htail (t : ℝ) :
        (volume.restrict (simplex n)).real {x : Space n | t ≤ height x} =
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x} := by
      first
      | rw [measureReal_restrict_apply' (simplex_compact n).measurableSet]
        congr 1
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, and_comm]
    rw [BerwaldMoments.power_layer_cake
      (continuous_height n).measurable.aemeasurable hnonneg p]
    simp only [htail]
    have hrestrict :
        (∫ t in Ioi (0 : ℝ), t ^ p *
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x}) =
        ∫ t in Ioc (0 : ℝ) 1, t ^ p *
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x} := by
      first
      | apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
          nullMeasurableSet_Ioi Ioc_subset_Ioi_self
        exact Eventually.of_forall fun t ht => by
          have ht1 : 1 < t := by
            have ht0 : 0 < t := ht.1
            by_contra h
            exact ht.2 ⟨ht0, le_of_not_gt h⟩
          rw [superlevel_empty ht1, measureReal_empty, mul_zero]
    rw [hrestrict, ← integral_Icc_eq_integral_Ioc]
    have heq : (∫ t in Icc (0 : ℝ) 1, t ^ p *
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x}) =
        (∫ t in Icc (0 : ℝ) 1, t ^ p * (1 - t) ^ n) *
          volume.real (simplex n) := by
      first
      | rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with t ht ht1
        rw [superlevel_volume ht.1 (lt_of_le_of_ne ht.2 ht1)]
        ring
    rw [heq]
    ring

theorem integral_height (n : ℕ) :
    (∫ x in simplex n, height x) = volume.real (simplex n) / (n + 1 : ℝ) := by
  first
  | have h := height_moment n 0
    have href : (∫ t in Icc (0 : ℝ) 1, (1 - t) ^ n) = 1 / (n + 1 : ℝ) := by
      first
      | simpa only [div_one] using BerwaldComparison.reference_integral n zero_lt_one
    simpa only [zero_add, pow_one, Nat.cast_zero, zero_add, one_mul, pow_zero,
      href, mul_one_div] using h

theorem integral_height_sq (n : ℕ) :
    (∫ x in simplex n, height x ^ 2) =
      2 * volume.real (simplex n) / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  first
  | have h := height_moment n 1
    have href : (∫ t in Icc (0 : ℝ) 1, t * (1 - t) ^ n) =
        1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
      first
      | simpa only [div_one, one_pow] using
          BerwaldComparison.reference_first_moment n zero_lt_one
    simpa only [one_add_one_eq_two, Nat.cast_one, pow_one, href, mul_one_div] using h

def coneHeight {n : ℕ} (x : Space n) : ℝ := (n + 1 : ℝ) * height x

theorem coneHeight_nonnegative {n : ℕ} {x : Space n} (hx : x ∈ simplex n) :
    0 ≤ coneHeight x := mul_nonneg (by positivity) (height_nonnegative hx)

theorem continuous_coneHeight (n : ℕ) : Continuous (coneHeight : Space n → ℝ) :=
  continuous_const.mul (continuous_height n)

theorem coneHeight_affine {n : ℕ} (x y : Space n) {a b : ℝ} (hab : a + b = 1) :
    coneHeight (a • x + b • y) = a * coneHeight x + b * coneHeight y := by
  first
  | simp only [coneHeight, height, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith

theorem integral_coneHeight (n : ℕ) :
    (∫ x in simplex n, coneHeight x) = volume.real (simplex n) := by
  first
  | change (∫ x in simplex n, (n + 1 : ℝ) * height x) = _
    rw [integral_const_mul, integral_height]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp

theorem integral_coneHeight_sq (n : ℕ) :
    (∫ x in simplex n, coneHeight x ^ 2) =
      (2 * (n + 1 : ℝ) / (n + 2 : ℝ)) * volume.real (simplex n) := by
  first
  | simp_rw [coneHeight, mul_pow]
    rw [integral_const_mul, integral_height_sq]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp <;> ring

/-- These are precisely the two normalized moments used in (6.5). -/
theorem coneHeight_normalized_moments (n : ℕ) :
    (∫ x in simplex n, coneHeight x) / volume.real (simplex n) = 1 ∧
      (∫ x in simplex n, coneHeight x ^ 2) / volume.real (simplex n) =
        2 * (n + 1 : ℝ) / (n + 2 : ℝ) := by
  first
  | have hm := (simplex_volume_pos n).ne'
    rw [integral_coneHeight, integral_coneHeight_sq]
    exact ⟨div_self hm, mul_div_cancel_right₀ _ hm⟩

end VolumePolynomials.SimplexCoordinates
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SimplexMoments.lean -/

/- BEGIN SOURCE: VolumePolynomials/SimplexCone.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The actual cone realizing the lifted slice

The cone is the image of a compact planar body times a coordinate simplex
under the explicit map `(a,y) ↦ (ρ(y) • a,y)`. Its convexity, exact fibers,
and finite convex-hull description are proved, including the zero-height
faces. These are geometric assertions about subsets, not assumed data in
a realization structure.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.SimplexCone

open SimplexCoordinates ConvexFibers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coneSet (A : ConvexBody E) (k : ℕ) : Set (E × Space k) :=
  (fun p : E × Space k => (coneHeight p.2 • p.1, p.2)) ''
    ((A : Set E) ×ˢ simplex k)

theorem coneSet_compact (A : ConvexBody E) (k : ℕ) : IsCompact (coneSet A k) :=
  (A.isCompact.prod (simplex_compact k)).image
    (((continuous_coneHeight k).comp continuous_snd).smul continuous_fst |>.prodMk continuous_snd)

theorem coneSet_nonempty (A : ConvexBody E) (k : ℕ) : (coneSet A k).Nonempty :=
  (A.nonempty.prod ⟨0, zero_mem_simplex k⟩).image _

theorem coneSet_convex (A : ConvexBody E) (k : ℕ) : Convex ℝ (coneSet A k) := by
  first
  | rintro _ ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩ _ ⟨⟨y, v⟩, ⟨hy, hv⟩, rfl⟩ a b ha hb hab
    let z : Space k := a • u + b • v
    let r : ℝ := coneHeight z
    have hz : z ∈ simplex k := simplex_convex k hu hv ha hb hab
    have hru : 0 ≤ coneHeight u := coneHeight_nonnegative hu
    have hrv : 0 ≤ coneHeight v := coneHeight_nonnegative hv
    have hr : 0 ≤ r := coneHeight_nonnegative hz
    have hre : r = a * coneHeight u + b * coneHeight v := coneHeight_affine u v hab
    by_cases hr0 : r = 0
    · have hu0 : a * coneHeight u = 0 := by nlinarith
      have hv0 : b * coneHeight v = 0 := by nlinarith
      obtain ⟨q, hq⟩ := A.nonempty
      refine ⟨(q, z), ⟨hq, hz⟩, Prod.ext ?_ rfl⟩
      change r • q = a • (coneHeight u • x) + b • (coneHeight v • y)
      simp only [hr0, zero_smul, smul_smul, hu0, hv0, add_zero]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      let c : ℝ := a * coneHeight u / r
      let d : ℝ := b * coneHeight v / r
      have hc : 0 ≤ c := div_nonneg (mul_nonneg ha hru) hr
      have hd : 0 ≤ d := div_nonneg (mul_nonneg hb hrv) hr
      have hcd : c + d = 1 := by
        first
        | dsimp only [c, d]
          rw [← add_div, ← hre, div_self hr0]
      have hrc : r * c = a * coneHeight u := by dsimp [c]; field_simp
      have hrd : r * d = b * coneHeight v := by dsimp [d]; field_simp
      refine ⟨(c • x + d • y, z), ⟨A.convex hx hy hc hd hcd, hz⟩, Prod.ext ?_ rfl⟩
      change r • (c • x + d • y) = a • (coneHeight u • x) + b • (coneHeight v • y)
      simp only [smul_add, smul_smul, hrc, hrd]

def coneBody (A : ConvexBody E) (k : ℕ) : ConvexBody (E × Space k) :=
  ⟨coneSet A k, coneSet_convex A k, coneSet_compact A k, coneSet_nonempty A k⟩

theorem cone_projection (A : ConvexBody E) (k : ℕ) :
    projection (coneBody A k) = simplex k := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨⟨a, z⟩, ⟨ha, hz⟩, rfl⟩, rfl⟩
      exact hz
    · intro hy
      obtain ⟨a, ha⟩ := A.nonempty
      exact ⟨(coneHeight y • a, y), ⟨(a, y), ⟨ha, hy⟩, rfl⟩, rfl⟩

theorem cone_fiber (A : ConvexBody E) (k : ℕ) {y : Space k} (hy : y ∈ simplex k) :
    fiberSet (coneBody A k) y = coneHeight y • (A : Set E) := by
  first
  | ext x
    constructor
    · rintro ⟨⟨a, z⟩, ⟨ha, hz⟩, heq⟩
      have hzy : z = y := congrArg Prod.snd heq
      subst z
      exact ⟨a, ha, congrArg Prod.fst heq⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a, y), ⟨ha, hy⟩, rfl⟩

theorem cone_fiberBody (A : ConvexBody E) (k : ℕ) {y : Space k}
    (hy : y ∈ simplex k) :
    fiberBody (coneBody A k) y = coneHeight y • A := by
  first
  | apply ConvexBody.ext
    rw [coe_fiberBody _ (by rwa [cone_projection]), cone_fiber A k hy]
    rfl

def baseMap (k : ℕ) : E →L[ℝ] E × Space k :=
  (k + 1 : ℝ) • ContinuousLinearMap.inl ℝ E (Space k)

def apex (k : ℕ) (i : Fin k) : E × Space k := (0, Pi.single i 1)

theorem base_mem_cone (A : ConvexBody E) (k : ℕ) {a : E} (ha : a ∈ A) :
    baseMap k a ∈ coneSet A k := by
  first
  | refine ⟨(a, 0), ⟨ha, zero_mem_simplex k⟩, ?_⟩
    simp [baseMap, coneHeight, height]

theorem apex_mem_cone (A : ConvexBody E) (k : ℕ) (i : Fin k) :
    apex (E := E) k i ∈ coneSet A k := by
  first
  | obtain ⟨a, ha⟩ := A.nonempty
    refine ⟨(a, Pi.single i 1), ⟨ha, coordinate_mem_simplex i⟩, ?_⟩
    simp [apex, coneHeight, height]

/-- The convex-hull description in (6.5), with every base point retained. -/
theorem cone_eq_convexHull (A : ConvexBody E) (k : ℕ) :
    coneSet A k = convexHull ℝ
      ((baseMap k '' (A : Set E)) ∪ range (apex (E := E) k)) := by
  first
  | apply le_antisymm
    · rintro _ ⟨⟨a, y⟩, ⟨ha, hy⟩, rfl⟩
      let w : Fin (k + 1) → ℝ := Fin.cons (height y) y
      let v : Fin (k + 1) → E × Space k := Fin.cons (baseMap k a) (apex k)
      apply mem_convexHull_of_exists_fintype w v
      · intro i
        cases i using Fin.cases with
        | zero => exact height_nonnegative hy
        | succ i => exact hy.1 i
      · simp [w, Fin.sum_univ_succ, height]
      · intro i
        cases i using Fin.cases with
        | zero => exact Or.inl ⟨a, ha, rfl⟩
        | succ i => exact Or.inr (mem_range_self i)
      · apply Prod.ext
        · simp [w, v, baseMap, apex, Fin.sum_univ_succ, coneHeight, smul_smul, mul_comm,
            Prod.fst_sum]
        · ext j
          simp [w, v, baseMap, apex, Fin.sum_univ_succ, Finset.sum_apply, Pi.single_apply,
            Prod.snd_sum]
    · apply convexHull_min _ (coneSet_convex A k)
      rintro _ (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
      · exact base_mem_cone A k ha
      · exact apex_mem_cone A k i

/-- A finite generating set for the planar body gives a finite generating
set for the lifted cone. This proves the polytope assertion in the converse. -/
theorem cone_finiteHull (A : ConvexBody E) (k : ℕ)
    (hA : PolytopeGeometry.IsFiniteHull (A : Set E)) :
    PolytopeGeometry.IsFiniteHull (coneSet A k) := by
  first
  | obtain ⟨S, hS, hA⟩ := hA
    refine ⟨baseMap k '' S ∪ range (apex (E := E) k),
      (hS.image _).union (Set.finite_range _), ?_⟩
    rw [cone_eq_convexHull, hA]
    have himage : baseMap k '' convexHull ℝ S = convexHull ℝ (baseMap k '' S) := by
      simpa only [ContinuousLinearMap.coe_coe] using
        (baseMap (E := E) k).toLinearMap.image_convexHull S
    rw [himage, convexHull_convexHull_union_left]

end VolumePolynomials.SimplexCone
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SimplexCone.lean -/

/- BEGIN SOURCE: VolumePolynomials/HigherLiftConverse.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The converse in the higher-dimensional lifting proposition

An arbitrary realization of the cubic slice is lifted by the actual cone
over a simplex. Fubini and its proved first two height moments produce
exactly `X₁^k P_{cₖ α,s,z}`. A positive Haar factor accounts for the chosen
coordinate equivalence and is removed by a common dilation.
-/

open Set MeasureTheory MvPolynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

open SimplexCoordinates SimplexCone ConvexFibers FiberVolume

def rawTuple (k : ℕ) (K : Fin 3 → Body 3) :
    Fin 3 → ConvexBody (Space 3 × Space k) :=
  ![coneBody (K 0) k, embedBody (K 1), embedBody (K 2)]

theorem raw_sum (k : ℕ) (K : Fin 3 → Body 3) (t : Fin 3 → ℝ) :
    (∑ i, t i • rawTuple k K i) =
      t 0 • coneBody (K 0) k + embedBody (t 1 • K 1 + t 2 • K 2) := by
  first
  | simp only [rawTuple, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      embedBody, mapBody_add, mapBody_smul, add_assoc]

theorem integrated_cubic {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z))
    (k : ℕ) (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∫ y in simplex k, bodyVolume
      ((t 0 * coneHeight y) • K 0 + t 1 • K 1 + t 2 • K 2)) =
      volume.real (simplex k) * CubicSlice.value (correction k * α) s z t := by
  first
  | let a₂ : ℝ := 3 * α * t 0 ^ 2 * t 1 + 3 * α * t 0 ^ 2 * t 2
    let a₁ : ℝ := 3 * t 0 * t 1 ^ 2 + 3 * s * t 0 * t 2 ^ 2 +
      6 * z * t 0 * t 1 * t 2
    let a₀ : ℝ := 3 * t 1 ^ 2 * t 2 + 3 * t 1 * t 2 ^ 2
    have heval (y : Space k) (hy : y ∈ simplex k) :
        bodyVolume ((t 0 * coneHeight y) • K 0 + t 1 • K 1 + t 2 • K 2) =
          a₂ * coneHeight y ^ 2 + a₁ * coneHeight y + a₀ := by
      first
      | have h := (CubicSlice.realizes_iff α s z K).mp hK
          ![t 0 * coneHeight y, t 1, t 2] (by
            intro i
            fin_cases i
            · exact mul_nonneg (ht 0) (coneHeight_nonnegative hy)
            · exact ht 1
            · exact ht 2)
        simp only [volumeFunction, weightedSum, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at h
        rw [h]
        dsimp only [CubicSlice.value, a₂, a₁, a₀]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        ring
    have hρ : IntegrableOn (coneHeight : Space k → ℝ) (simplex k) :=
      (continuous_coneHeight k).continuousOn.integrableOn_compact (simplex_compact k)
    have hρ₂ : IntegrableOn (fun y : Space k => coneHeight y ^ 2) (simplex k) :=
      ((continuous_coneHeight k).pow 2).continuousOn.integrableOn_compact (simplex_compact k)
    have hconst : IntegrableOn (fun _ : Space k => a₀) (simplex k) :=
      integrableOn_const (simplex_compact k).measure_ne_top
    calc
      _ = ∫ y in simplex k, a₂ * coneHeight y ^ 2 + a₁ * coneHeight y + a₀ := by
        first
        | apply setIntegral_congr_fun (simplex_compact k).measurableSet
          exact heval
      _ = a₂ * (∫ y in simplex k, coneHeight y ^ 2) +
          a₁ * (∫ y in simplex k, coneHeight y) + a₀ * volume.real (simplex k) := by
        first
        | rw [integral_add
            (f := fun y : Space k => a₂ * coneHeight y ^ 2 + a₁ * coneHeight y)
            (g := fun _ : Space k => a₀)
            ((hρ₂.const_mul a₂).add (hρ.const_mul a₁)) hconst,
            integral_add (f := fun y : Space k => a₂ * coneHeight y ^ 2)
              (g := fun y : Space k => a₁ * coneHeight y)
              (hρ₂.const_mul a₂) (hρ.const_mul a₁),
            integral_const_mul, integral_const_mul, setIntegral_const]
          simp only [smul_eq_mul, mul_comm a₀]
      _ = _ := by
        first
        | rw [integral_coneHeight_sq, integral_coneHeight]
          dsimp only [a₂, a₁, a₀, CubicSlice.value, correction]
          ring

/-- The full volume identity before the harmless common dilation. -/
theorem raw_volume {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z))
    {k : ℕ} (hk : 0 < k) (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    volume.real ((∑ i, t i • rawTuple k K i : ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k)) =
      volume.real (simplex k) * evaluate (coefficients k α s z) t := by
  first
  | rw [raw_sum, realVolume_scaled_sum (by simpa [Space] using hk)
      (coneBody (K 0) k) (t 1 • K 1 + t 2 • K 2) (ht 0), cone_projection]
    have hinner : (∫ y in simplex k, volume.real
        ((t 0 • fiberBody (coneBody (K 0) k) y +
          (t 1 • K 1 + t 2 • K 2) : Body 3) : Set (Space 3))) =
        ∫ y in simplex k, bodyVolume
          ((t 0 * coneHeight y) • K 0 + t 1 • K 1 + t 2 • K 2) := by
      first
      | apply setIntegral_congr_fun (simplex_compact k).measurableSet
        intro y hy
        dsimp only
        rw [cone_fiberBody (K 0) k hy, smul_smul, ← add_assoc]
        rfl
    rw [hinner, integrated_cubic hK k t ht, evaluate_coefficients]
    simp only [Space, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    ring

def productLinearEquiv (k : ℕ) : (Space 3 × Space k) ≃ₗ[ℝ] Space (3 + k) where
  toFun p := Fin.addCases p.1 p.2
  invFun x := (fun i => x (Fin.castAdd k i), fun j => x (Fin.natAdd 3 j))
  left_inv p := by ext <;> simp
  right_inv x := by
    first
    | funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp
      · intro j; simp
  map_add' p q := by
    first
    | funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp
      · intro j; simp
  map_smul' r p := by
    first
    | funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp
      · intro j; simp

def productEquiv (k : ℕ) : (Space 3 × Space k) ≃L[ℝ] Space (3 + k) :=
  (productLinearEquiv k).toContinuousLinearEquiv

def rawScale (k : ℕ) : ℝ :=
  volume.real (simplex k) / (LinearFrame.volumeFactor (productEquiv k) : ℝ)

theorem rawScale_pos (k : ℕ) : 0 < rawScale k :=
  div_pos (simplex_volume_pos k) (by exact_mod_cast LinearFrame.volumeFactor_pos (productEquiv k))

def coordinateTuple (k : ℕ) (K : Fin 3 → Body 3) : Fin 3 → Body (3 + k) :=
  fun i => mapBody (productEquiv k).toContinuousLinearMap (rawTuple k K i)

theorem coordinate_realizes {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z)) {k : ℕ} (hk : 0 < k) :
    Realizes (coordinateTuple k K) (rawScale k • coefficients k α s z) := by
  first
  | intro t ht
    rw [evaluate_smul]
    have hsum : weightedSum (coordinateTuple k K) t =
        mapBody (productEquiv k).toContinuousLinearMap (∑ i, t i • rawTuple k K i) := by
      first
      | rw [show mapBody (productEquiv k).toContinuousLinearMap (∑ i, t i • rawTuple k K i) =
            ∑ i, mapBody (productEquiv k).toContinuousLinearMap (t i • rawTuple k K i) from
          map_sum (mapBodyHom (productEquiv k).toContinuousLinearMap) _ _]
        simp only [weightedSum, coordinateTuple, mapBody_smul]
    have hmeasure := LinearFrame.realVolume_eq_factor_mul_image (productEquiv k)
      ((∑ i, t i • rawTuple k K i : ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k))
    rw [raw_volume hK hk t ht] at hmeasure
    rw [volumeFunction, hsum]
    change rawScale k * evaluate (coefficients k α s z) t =
      volume.real (productEquiv k '' ((∑ i, t i • rawTuple k K i : ConvexBody _) : Set _))
    have hf : (LinearFrame.volumeFactor (productEquiv k) : ℝ) ≠ 0 :=
      (show 0 < (LinearFrame.volumeFactor (productEquiv k) : ℝ) by
        exact_mod_cast LinearFrame.volumeFactor_pos (productEquiv k)).ne'
    unfold rawScale
    field_simp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hmeasure

def dilation (k : ℕ) : ℝ := (rawScale k)⁻¹ ^ (((3 + k : ℕ) : ℝ)⁻¹)

def liftedTuple (k : ℕ) (K : Fin 3 → Body 3) : Fin 3 → Body (3 + k) :=
  fun i => dilation k • coordinateTuple k K i

/-- Every cubic realization lifts, without restrictions on its shape or
on the parameters beyond the original realization itself. -/
theorem lifted_realizes {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (CubicSlice.coefficients α s z)) {k : ℕ} (hk : 0 < k) :
    Realizes (liftedTuple k K) (coefficients k α s z) := by
  first
  | have hr : 0 ≤ dilation k := Real.rpow_nonneg (inv_pos.mpr (rawScale_pos k)).le _
    have hpow : dilation k ^ (3 + k) = (rawScale k)⁻¹ := by
      first
      | exact Real.rpow_inv_natCast_pow (inv_pos.mpr (rawScale_pos k)).le (by omega)
    have h := (coordinate_realizes hK hk).dilate hr
    rw [hpow, smul_smul, inv_mul_cancel₀ (rawScale_pos k).ne', one_smul] at h
    exact h

theorem mem_volumeLocus_of_cubic {α s z : ℝ}
    (h : CubicSlice.coefficients α s z ∈ VolumeLocus 3 3) {k : ℕ} (hk : 0 < k) :
    coefficients k α s z ∈ VolumeLocus 3 (3 + k) := by
  first
  | obtain ⟨K, hK⟩ := h
    exact ⟨liftedTuple k K, lifted_realizes hK hk⟩

/-- Finite convex hulls remain finite convex hulls through the construction. -/
theorem lifted_finiteHull (k : ℕ) (K : Fin 3 → Body 3)
    (hK : ∀ i, PolytopeGeometry.IsFiniteHull (K i : Set (Space 3))) (i : Fin 3) :
    PolytopeGeometry.IsFiniteHull (liftedTuple k K i : Set (Space (3 + k))) := by
  first
  | apply PolytopeGeometry.IsFiniteHull.smul
    apply PolytopeGeometry.IsFiniteHull.linear_image
    fin_cases i
    · exact cone_finiteHull (K 0) k (hK 0)
    · exact (hK 1).linear_image (ContinuousLinearMap.inl ℝ (Space 3) (Space k)).toLinearMap
    · exact (hK 2).linear_image (ContinuousLinearMap.inl ℝ (Space 3) (Space k)).toLinearMap

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HigherLiftConverse.lean -/

/- BEGIN SOURCE: TauCeti/LinearAlgebra/AffineSpace/Basis.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Affine equivalences between affine bases

Two affine bases indexed by the same type are related by an affine equivalence: there is an affine
equivalence sending the points of one basis to the corresponding points of the other
(`AffineBasis.exists_affineEquiv_apply_eq`), and every affine map that does so preserves
barycentric coordinates (`AffineBasis.coord_apply_of_forall_apply_eq`). This is how a statement
about barycentric coordinates relative to an arbitrary affine basis is reduced to one about a
fixed reference basis.

The file also computes the barycentric coordinates of a point after a homothety about the centroid
of an affine basis (`AffineBasis.coord_homothety_centroid`), which describes the homothetic images
of the simplex spanned by the basis.

## Main statements

* `AffineBasis.coord_apply_of_forall_apply_eq`: an affine map sending the affine basis `b` to the
  affine basis `b₂` carries barycentric coordinates relative to `b` to those relative to `b₂`;
* `AffineBasis.exists_affineEquiv_apply_eq`: there is an affine equivalence sending `b` to `b₂`;
* `AffineBasis.coord_homothety_centroid`: the barycentric coordinates of the image of a point under
  a homothety about the centroid of an affine basis.
-/

public section

namespace AffineBasis

variable {ι k V P V₂ P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] (b : AffineBasis ι k P)
  (b₂ : AffineBasis ι k P₂)

/-- An affine map sending each point `b i` of an affine basis to the point `b₂ i` of another affine
basis preserves barycentric coordinates. -/
theorem coord_apply_of_forall_apply_eq {f : P →ᵃ[k] P₂} (hf : ∀ i, f (b i) = b₂ i) (i : ι)
    (x : P) : b₂.coord i (f x) = b.coord i x := by
  have h : (b₂.coord i).comp f = b.coord i := by
    refine AffineMap.ext_on b.tot ?_
    rintro - ⟨j, rfl⟩
    rcases eq_or_ne i j with rfl | hij
    · simp [hf, coord_apply_eq]
    · simp [hf, coord_apply_ne _ hij]
  exact congr($h x)

/-- Two affine bases indexed by the same type are related by an affine equivalence sending each
point of the first basis to the corresponding point of the second. -/
theorem exists_affineEquiv_apply_eq : ∃ T : P ≃ᵃ[k] P₂, ∀ i, T (b i) = b₂ i := by
  obtain ⟨i₀⟩ := b.nonempty
  -- Translate `b i₀` to the origin, map the linear basis `b.basisOf i₀` to `b₂.basisOf i₀`, and
  -- translate the origin to `b₂ i₀`.
  let L : V ≃ₗ[k] V₂ := (b.basisOf i₀).equiv (b₂.basisOf i₀) (Equiv.refl _)
  refine ⟨((AffineEquiv.vaddConst k (b i₀)).symm.trans L.toAffineEquiv).trans
    (AffineEquiv.vaddConst k (b₂ i₀)), fun i => ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · simp
  · have hL : L (b i -ᵥ b i₀) = b₂ i -ᵥ b₂ i₀ := by
      rw [← b.basisOf_apply i₀ ⟨i, hi⟩, Module.Basis.equiv_apply, Equiv.refl_apply,
        basisOf_apply]
    simp [hL]

end AffineBasis

namespace AffineBasis

variable {ι k V P : Type*} [Fintype ι] [Field k] [CharZero k] [AddCommGroup V] [Module k V]
  [AddTorsor V P] (b : AffineBasis ι k P)

/-- The barycentric coordinates relative to an affine basis `b` of the image of a point `z` under
the homothety of ratio `t` about the centroid of `b`: the homothety moves each coordinate
`b.coord i z` towards the centroid's coordinate `1 / card ι` by the factor `t`. -/
theorem coord_homothety_centroid (t : k) (z : P) (i : ι) :
    b.coord i (AffineMap.homothety (Finset.univ.centroid k b) t z) =
      (1 - t) / Fintype.card ι + t * b.coord i z := by
  rw [AffineMap.homothety_eq_lineMap, AffineMap.apply_lineMap,
    b.coord_apply_centroid (Finset.mem_univ i), Finset.card_univ, AffineMap.lineMap_apply_ring']
  ring

end AffineBasis
end -- closes the original EOF section from source line 33
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/LinearAlgebra/AffineSpace/Basis.lean -/

/- BEGIN SOURCE: TauCeti/LinearAlgebra/AffineSpace/Matrix.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Determinants of matrices of barycentric coordinates

Fix an affine basis `b` of an affine space `P`. For a family `q` of points of `P`, the matrix
`b.toMatrix q` has the barycentric coordinates of `q i` with respect to `b` as its rows, and when
`q` is indexed like `b` its determinant is the signed (oriented) volume of the simplex with vertices
`q i`, measured relative to the simplex of `b`; the unsigned relative volume is its absolute value.

Replacing the vertex `q i` of an affine basis `q` by a point `x` scales this determinant by the
barycentric coordinate of `x` at `i` with respect to `q`
(`AffineBasis.det_toMatrix_update`). This is Cramer's rule for barycentric coordinates
(`AffineBasis.det_smul_coords_eq_cramer_coords`) read as a statement about volumes, and it is the
reason a simplex of maximal volume inside a set controls the barycentric coordinates of all points
of the set.

## Main statements

* `AffineBasis.toMatrix_update`: replacing a point of the family replaces the corresponding row by
  its barycentric coordinates;
* `AffineBasis.det_toMatrix_update`: replacing the vertex `q i` of an affine basis `q` by `x`
  multiplies the determinant by `q.coord i x`.
-/

public section

open Matrix

namespace AffineBasis

variable {ι ι' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/-- Replacing the point `q i` of a family by `x` replaces the `i`-th row of the matrix of
barycentric coordinates by the coordinates of `x`. -/
@[simp]
theorem toMatrix_update [DecidableEq ι'] (q : ι' → P) (i : ι') (x : P) :
    b.toMatrix (Function.update q i x) = (b.toMatrix q).updateRow i (b.coords x) := by
  ext j l
  rcases eq_or_ne j i with rfl | hj
  · simp [toMatrix_apply]
  · simp [toMatrix_apply, hj]

end Ring

section CommRing

variable [CommRing k] [Module k V] [Fintype ι] [DecidableEq ι] (b b₂ : AffineBasis ι k P)

/-- Replacing the vertex `b₂ i` of the affine basis `b₂` by a point `x` multiplies the determinant
of the matrix of barycentric coordinates relative to `b` by the barycentric coordinate of `x` at
`i` with respect to `b₂`. -/
theorem det_toMatrix_update (i : ι) (x : P) :
    (b.toMatrix (Function.update b₂ i x)).det = (b.toMatrix b₂).det * b₂.coord i x := by
  have h := congr_fun (b.det_smul_coords_eq_cramer_coords b₂ x) i
  rw [Pi.smul_apply, coords_apply, smul_eq_mul, cramer_apply, updateCol_transpose,
    det_transpose] at h
  rw [toMatrix_update, h]

end CommRing

end AffineBasis
end -- closes the original EOF section from source line 33
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/LinearAlgebra/AffineSpace/Matrix.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Convex/AffineNormalization.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Affine normalization of convex bodies

A convex body in an `n`-dimensional real affine space can be moved by an affine equivalence to a
position between two balls whose radii depend only on the space. This is the normalization that
lets estimates for convex sets be proved for sets of unit size and transferred back; in the
regularity theory of the Monge–Ampère equation it is applied to the sections
`{y | u y < u x + ⟪p, y - x⟫ + h}` of a convex function `u`.

The normalization comes from a simplex of maximal volume. Let `K` be a compact set whose affine
span is the whole `n`-dimensional space, and choose `n + 1` points of `K` spanning a simplex of
maximal volume, where volume is measured by the absolute value of the determinant of the matrix of
barycentric coordinates relative to a fixed affine basis (the determinant itself is the signed
volume). Replacing the vertex `b i` by a point `x` multiplies this determinant by the barycentric
coordinate `b.coord i x` (`AffineBasis.det_toMatrix_update`), so maximality of its absolute value
forces `|b.coord i x| ≤ 1` for every `x ∈ K`
(`IsCompact.exists_affineBasis_abs_coord_le_one`).

In terms of the simplex `Δ = convexHull (range b)` with centroid `c`, the points whose barycentric
coordinates are all at most `1` form the image of `Δ` under the homothety of ratio `-n` about `c`
(`AffineBasis.mem_image_homothety_convexHull_iff`). Thus every compact spanning `K` contains the
vertices of a simplex `Δ` and lies inside its homothetic image of ratio `-n`
(`IsCompact.exists_affineBasis_subset_image_homothety_convexHull`); when `K` is convex it contains
`Δ` itself. Mapping `Δ` to a fixed reference simplex by an affine equivalence then gives the
normalization by balls (`TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`).

John's theorem gives the sharper statement in which the simplex is replaced by the ellipsoid of
maximal volume and the ratio `-n` by `n`, or by `√n` for centrally symmetric bodies. For the
normalization, a ratio depending only on the dimension suffices.

## Main statements

* `IsCompact.exists_affineBasis_abs_coord_le_one`: a compact set spanning a finite-dimensional real
  affine space contains an affine basis relative to which all its points have barycentric
  coordinates in `[-1, 1]`;
* `AffineBasis.mem_image_homothety_convexHull_iff`: the image of the simplex of an affine basis
  under the homothety of ratio `-n` about its centroid is the set of points whose barycentric
  coordinates are at most `1`;
* `IsCompact.exists_affineBasis_subset_image_homothety_convexHull`: a compact spanning set contains
  the vertices of a simplex and lies in the image of that simplex under the homothety of ratio `-n`
  about its centroid;
* `TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`: in a finite-dimensional real normed
  space there is `r > 0` such that every bounded convex set with nonempty interior is mapped by
  some affine equivalence to a set between the balls of radii `r` and `1` about `0`.

## References

* F. John, *Extremum problems with inequalities as subsidiary conditions*, Studies and Essays
  Presented to R. Courant on his 60th Birthday, Interscience, 1948, 187–204.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.8 (normalized convex sets).
* K. Ball, *An elementary introduction to modern convex geometry*, in *Flavors of Geometry*,
  MSRI Publications 31, Cambridge University Press, 1997, Lecture 3.
-/

public section

open Set Module Metric

/-! ### A simplex of maximal volume -/

section Compact

variable {ι V P : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- **Affine bases with bounded barycentric coordinates.** A compact set `K` whose affine span is
the whole finite-dimensional real affine space contains an affine basis `b`, indexed by any type
with `finrank + 1` elements, such that every point of `K` has all its barycentric coordinates
relative to `b` in `[-1, 1]`. -/
theorem IsCompact.exists_affineBasis_abs_coord_le_one {K : Set P} (hK : IsCompact K)
    (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ V + 1) :
    ∃ b : AffineBasis ι ℝ P, (∀ i, b i ∈ K) ∧ ∀ x ∈ K, ∀ i, |b.coord i x| ≤ 1 := by
  classical
  -- A reference affine basis with vertices in `K`.
  obtain ⟨s, hsK, b₀, hb₀⟩ := AffineBasis.exists_affine_subbasis hspan
  lift s to Finset P using b₀.setFinite
  let b₁ : AffineBasis ι ℝ P :=
    b₀.reindex (Fintype.equivOfCardEq (by rw [hι, ← b₀.card_eq_finrank_add_one]))
  have hb₁ : ∀ i, b₁ i ∈ K := fun i => by
    simp only [b₁, AffineBasis.reindex_apply, hb₀]
    exact hsK (Subtype.prop _)
  -- Choose vertices in `K` maximizing the volume `|det|` relative to `b₁`.
  let f : (ι → P) → ℝ := fun q => |(b₁.toMatrix q).det|
  -- Continuity goes through the linear part: Mathlib's `continuous_barycentric_coord` assumes
  -- `MetricSpace P`, which this pseudometric setting does not provide.
  have hcoord : ∀ j, Continuous (b₁.coord j) := fun j =>
    AffineMap.continuous_linear_iff.1 (b₁.coord j).linear.continuous_of_finiteDimensional
  have hf : Continuous f :=
    ((continuous_matrix fun i j => (hcoord j).comp (continuous_apply i)).matrix_det).abs
  obtain ⟨q, hqK, hq⟩ := (isCompact_univ_pi fun _ => hK).exists_isMaxOn
    ⟨b₁, fun i _ => hb₁ i⟩ hf.continuousOn
  have hfq : 0 < f q := by
    have hb₁K : (b₁ : ι → P) ∈ univ.pi fun _ => K := fun i _ => hb₁ i
    have := hq hb₁K
    simp only [mem_ofPred_eq, b₁.toMatrix_self, Matrix.det_one, abs_one, f] at this
    linarith
  -- A family of points of nonzero volume is an affine basis.
  obtain ⟨hind, htot⟩ := (b₁.isUnit_toMatrix_iff q).1 <|
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (abs_pos.1 hfq))
  let b : AffineBasis ι ℝ P := ⟨q, hind, htot⟩
  have hbq : (b : ι → P) = q := rfl
  have hbK : ∀ j, b j ∈ K := fun j => hbq ▸ hqK j (mem_univ j)
  refine ⟨b, hbK, fun x hx i => ?_⟩
  -- Replacing the vertex `b i` by `x` multiplies the volume by `|b.coord i x|`.
  have hle : f (Function.update b i x) ≤ f b := by
    rw [hbq]
    refine hq fun j _ => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simpa [hj, hbq] using hbK j
  have hupdate : f (Function.update b i x) = f b * |b.coord i x| := by
    simp only [f, b₁.det_toMatrix_update b, abs_mul]
  rw [hupdate] at hle
  exact (mul_le_iff_le_one_right (hbq ▸ hfq)).1 hle

end Compact

/-! ### The homothetic image of a simplex -/

section Homothety

variable {ι k E : Type*} [Fintype ι] [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [Module k E] (b : AffineBasis ι k E)

/-- The image of the simplex spanned by an affine basis of an `n`-dimensional space under the
homothety of ratio `-n` about its centroid is the set of points whose barycentric coordinates are
all at most `1`. -/
theorem AffineBasis.mem_image_homothety_convexHull_iff {x : E} :
    x ∈ AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)) ''
        convexHull k (range b) ↔ ∀ i, b.coord i x ≤ 1 := by
  have hn : (0 : k) ≤ finrank k E := Nat.cast_nonneg _
  have hn1 : (finrank k E : k) + 1 ≠ 0 := by positivity
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [b.convexHull_eq_nonneg_coord] at hz
    rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one,
      div_eq_one_iff_eq hn1 |>.2 (by ring)]
    nlinarith [hz i]
  · intro hx
    rcases hn.eq_or_lt with h0 | hpos
    · -- In dimension zero the homothety is constant and the space is a point.
      have : Subsingleton E := by
        have := b.finiteDimensional
        exact finrank_zero_iff.1 (by exact_mod_cast h0.symm)
      obtain ⟨i⟩ := b.nonempty
      exact ⟨b i, subset_convexHull k _ (mem_range_self i), Subsingleton.elim _ _⟩
    · refine ⟨AffineMap.homothety (Finset.univ.centroid k b) (-(finrank k E : k)⁻¹) x, ?_, ?_⟩
      · rw [b.convexHull_eq_nonneg_coord]
        intro i
        rw [b.coord_homothety_centroid, b.card_eq_finrank_add_one, Nat.cast_add_one]
        have := hx i
        field_simp
        nlinarith
      · rw [← AffineMap.homothety_mul_apply, neg_mul_neg, mul_inv_cancel₀ hpos.ne',
          AffineMap.homothety_one, AffineMap.id_apply]

end Homothety

section CompactHomothety

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Affine normalization of compact sets.** A compact set `K` whose affine span is the whole
`n`-dimensional real normed space contains the vertices of a simplex `Δ` and lies in the image of
`Δ` under the homothety of ratio `-n` about the centroid of `Δ`. When `K` is convex, it also
contains `Δ`, by `convexHull_min`. -/
theorem IsCompact.exists_affineBasis_subset_image_homothety_convexHull {K : Set E}
    (hK : IsCompact K) (hspan : affineSpan ℝ K = ⊤) (hι : Fintype.card ι = finrank ℝ E + 1) :
    ∃ b : AffineBasis ι ℝ E, (∀ i, b i ∈ K) ∧
      K ⊆ AffineMap.homothety (Finset.univ.centroid ℝ b) (-(finrank ℝ E : ℝ)) ''
        convexHull ℝ (range b) := by
  obtain ⟨b, hbK, hb⟩ := hK.exists_affineBasis_abs_coord_le_one hspan hι
  exact ⟨b, hbK, fun x hx => b.mem_image_homothety_convexHull_iff.2 fun i =>
    (le_abs_self _).trans (hb x hx i)⟩

end CompactHomothety

/-! ### Normalization by balls -/

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- **Normalization of convex bodies.** In a finite-dimensional real normed space `E` there is a
radius `r > 0`, depending only on `E`, such that every bounded convex set `s` with nonempty
interior is mapped by some affine equivalence `T` to a set between the balls of radii `r` and `1`
about `0`. -/
theorem exists_affineEquiv_ball_subset_image_subset_ball :
    ∃ r > 0, ∀ s : Set E, Convex ℝ s → Bornology.IsBounded s → (interior s).Nonempty →
      ∃ T : E ≃ᵃ[ℝ] E, ball 0 r ⊆ T '' s ∧ T '' s ⊆ ball 0 1 := by
  -- A reference simplex: its interior contains a ball about its centroid `c`, and the points with
  -- barycentric coordinates in `[-1, 1]` lie in the ball of radius `∑ i, ‖b₁ i‖` about `0`.
  let ι := Fin (finrank ℝ E + 1)
  have hι : Fintype.card ι = finrank ℝ E + 1 := Fintype.card_fin _
  obtain ⟨b₁⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional (k := ℝ) (P := E) hι
  set c := Finset.univ.centroid ℝ b₁
  have hc : c ∈ interior (convexHull ℝ (range b₁)) := b₁.centroid_mem_interior_convexHull
  rw [b₁.interior_convexHull] at hc
  have hopen : IsOpen {y | ∀ i, 0 < b₁.coord i y} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_barycentric_coord b₁ i)
  obtain ⟨ρ, hρ, hball⟩ := isOpen_iff.1 hopen c hc
  have hbound : ∀ y, (∀ i, |b₁.coord i y| ≤ 1) → ‖y‖ ≤ ∑ i, ‖b₁ i‖ := fun y hy => by
    conv_lhs => rw [← b₁.linear_combination_coord_eq_self y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hy i)
  set R := ∑ i, ‖b₁ i‖ + ‖c‖ + 1
  have hR : 0 < R := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => norm_nonneg (b₁ i)
    have := norm_nonneg c
    linarith
  refine ⟨ρ / R, div_pos hρ hR, fun s hs hsb hsi => ?_⟩
  -- An affine basis in the closure of `s` relative to which the barycentric coordinates of the
  -- points of the closure lie in `[-1, 1]`.
  have hspan : affineSpan ℝ (closure s) = ⊤ :=
    top_unique <| (isOpen_interior.affineSpan_eq_top hsi).symm.le.trans
      (affineSpan_mono ℝ (interior_subset.trans subset_closure))
  obtain ⟨b, hbs, hb⟩ := hsb.isCompact_closure.exists_affineBasis_abs_coord_le_one hspan hι
  -- Move it onto the reference simplex, then recentre at `0` and rescale by `R⁻¹`.
  obtain ⟨T₀, hT₀⟩ := b.exists_affineEquiv_apply_eq b₁
  have hcoord : ∀ x i, b₁.coord i (T₀ x) = b.coord i x := fun x i =>
    b.coord_apply_of_forall_apply_eq b₁ (f := T₀.toAffineMap) hT₀ i x
  let T : E ≃ᵃ[ℝ] E := (T₀.trans (AffineEquiv.constVAdd ℝ E (-c))).trans
    (AffineEquiv.homothetyUnitsMulHom (0 : E) (Units.mk0 R⁻¹ (inv_ne_zero hR.ne')))
  have hT : ∀ x, T x = R⁻¹ • (T₀ x - c) := fun x => by
    simp [T, AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply,
      neg_add_eq_sub]
  refine ⟨T, fun y hy => ?_, ?_⟩
  · -- The preimage of a small ball lies in the interior of the simplex of `b`, inside `s`.
    have hy' : T₀.symm (c + R • y) ∈ s := by
      have hpos : ∀ i, 0 < b.coord i (T₀.symm (c + R • y)) := fun i => by
        rw [← hcoord, AffineEquiv.apply_symm_apply]
        refine hball ?_ i
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
        rw [mem_ball_zero_iff, lt_div_iff₀ hR] at hy
        linarith
      have hhull : convexHull ℝ (range b) ⊆ closure s :=
        convexHull_min (range_subset_iff.2 hbs) hs.closure
      have hmem : T₀.symm (c + R • y) ∈ interior (convexHull ℝ (range b)) := by
        rw [b.interior_convexHull]
        exact hpos
      exact interior_subset (hs.interior_closure_eq_interior_of_nonempty_interior hsi ▸
        interior_mono hhull hmem)
    refine ⟨_, hy', ?_⟩
    rw [hT, AffineEquiv.apply_symm_apply, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hR.ne', one_smul]
  · -- The image of `s` lies within distance `R - 1` of `c` before rescaling.
    rintro - ⟨x, hx, rfl⟩
    have hle := hbound (T₀ x) fun i => by
      rw [hcoord]
      exact hb x (subset_closure hx) i
    rw [mem_ball_zero_iff, hT, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
      inv_mul_lt_iff₀ hR, mul_one]
    linarith [norm_sub_le (T₀ x) c]

end TauCeti
end -- closes the original EOF section from source line 70
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Convex/AffineNormalization.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Convex/Measure.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Measure of convex sets

The frontier of a convex set in a finite-dimensional real normed space is null for any additive
Haar measure (`Convex.addHaar_frontier`). Consequently, almost every point of the set is in its
interior (`Convex.ae_mem_interior`), so the interior meets every set that the convex set meets in
positive measure (`Convex.interior_inter_nonempty_of_addHaar_inter_ne_zero`). A convex set has
positive Haar measure exactly when its interior is nonempty, equivalently when its affine span is
the whole space
(`Convex.addHaar_pos_iff_interior_nonempty`, `Convex.addHaar_pos_iff_affineSpan_eq_top`).

For the same reason, convex sets with disjoint interiors are almost everywhere disjoint
(`Convex.aedisjoint_of_disjoint_interior`), and so are unions of countably many of them
(`TauCeti.aedisjoint_iUnion_of_convex`). Hence Haar measure is additive over countable families of
convex sets with pairwise disjoint interiors (`TauCeti.addHaar_iUnion_of_convex`), and finitely
many interior-disjoint translates of a convex set `K` have total measure `card ι * μ K`
(`Convex.addHaar_iUnion_vadd`). These are the volume computations for packings of lattice
translates of a convex body in the proof of the upper half of Minkowski's second theorem by
M. Henk, *Successive minima and lattice points*, Rend. Circ. Mat. Palermo (2) Suppl. 70 (2002),
377–384, §3, arXiv:math/0204158.

A convex set containing a ball of radius `r > 0` and a point at distance `L` from its centre has
measure at least `2 ^ (-(n + 1)) * μ (ball 0 1) * L * r ^ (n - 1)`, which is the order of the
volume of the cone spanned by the ball and the point
(`Convex.ofReal_dist_mul_pow_mul_addHaar_ball_le`). This is the volume estimate behind the
Aleksandrov maximum principle for the Monge–Ampère equation.

A convex set with nonempty interior in a finite-dimensional real normed space has finite
Haar measure exactly when it is bounded. Consequently, a set of positive finite measure
which agrees almost everywhere with a convex set has a compact convex representative
with nonempty interior. No Borel measurability or closedness of the original set is needed.
This permits geometric arguments on compact convex sets to apply to essentially convex sets.

The boundedness argument uses `Convex.ofReal_dist_mul_pow_mul_addHaar_ball_le`, the
ball-and-point volume estimate. The representative is the closure of the convex set;
Mathlib's `Convex.addHaar_frontier` ensures that taking this closure changes only a null set.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ] {s : Set E}

/-- Almost every point of a convex set in a finite-dimensional real normed space is an interior
point, since the frontier of the set is null for every additive Haar measure. -/
theorem Convex.ae_mem_interior (hs : Convex ℝ s) : ∀ᵐ x ∂μ, x ∈ s → x ∈ interior s :=
  (interior_ae_eq_of_null_frontier (hs.addHaar_frontier μ)).symm.le

/-- If a convex set in a finite-dimensional real normed space meets a set `t` in positive additive
Haar measure, then its interior meets `t`, since almost every point of the convex set is
interior. -/
theorem Convex.interior_inter_nonempty_of_addHaar_inter_ne_zero (hs : Convex ℝ s) {t : Set E}
    (h : μ (s ∩ t) ≠ 0) : (interior s ∩ t).Nonempty := by
  first
  | by_contra hne
    have hnull : μ (s \ interior s) = 0 :=
      measure_eq_zero_iff_ae_notMem.2 (hs.ae_mem_interior.mono fun x hx h ↦ h.2 (hx h.1))
    exact h (measure_mono_null (fun x (hx : x ∈ s ∩ t) ↦
      (⟨hx.1, fun hi ↦ hne ⟨x, hi, hx.2⟩⟩ : x ∈ s \ interior s)) hnull)

/-- A convex set in a finite-dimensional real normed space has zero additive Haar measure exactly
when its interior is empty. -/
theorem Convex.addHaar_eq_zero_iff_interior_eq_empty (hs : Convex ℝ s) :
    μ s = 0 ↔ interior s = ∅ := by
  first
  | rw [← measure_interior_of_null_frontier (hs.addHaar_frontier μ)]
    exact isOpen_interior.measure_eq_zero_iff μ

/-- A convex set in a finite-dimensional real normed space has positive additive Haar measure
exactly when its interior is nonempty. -/
theorem Convex.addHaar_pos_iff_interior_nonempty (hs : Convex ℝ s) :
    0 < μ s ↔ (interior s).Nonempty := by
  first
  | simpa only [pos_iff_ne_zero, Set.nonempty_iff_ne_empty] using
      not_congr hs.addHaar_eq_zero_iff_interior_eq_empty

/-- A convex set in a finite-dimensional real normed space has positive additive Haar measure
exactly when its affine span is the whole space. -/
theorem Convex.addHaar_pos_iff_affineSpan_eq_top (hs : Convex ℝ s) :
    0 < μ s ↔ affineSpan ℝ s = ⊤ := by
  first
  | rw [hs.addHaar_pos_iff_interior_nonempty, hs.interior_nonempty_iff_affineSpan_eq_top]

/-- **A convex set containing a ball and a point is large.** In a finite-dimensional real normed
space `E` of dimension `n`, if a convex set `s` contains the ball of radius `r > 0` about `x` and
the point `y`, then `dist y x * r ^ (n - 1) * μ (ball 0 1) ≤ 2 ^ (n + 1) * μ s` for every
additive Haar measure `μ`. -/
theorem Convex.ofReal_dist_mul_pow_mul_addHaar_ball_le [Nontrivial E] (hs : Convex ℝ s) {x y : E}
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ s) (hy : y ∈ s) :
    ENNReal.ofReal (dist y x * r ^ (finrank ℝ E - 1)) * μ (ball 0 1) ≤
      2 ^ (finrank ℝ E + 1) * μ s := by
  first
  | set n := finrank ℝ E
    set L := dist y x
    have hL₀ : 0 ≤ L := dist_nonneg
    rcases hL₀.eq_or_lt with hL | hL
    · rw [← hL, zero_mul, ENNReal.ofReal_zero, zero_mul]
      exact bot_le
    -- The set `s` contains the balls of radius `r / 2` about the points of the segment from `x` to
    -- the midpoint of `x` and `y`. The centres `c j = x + (j * r / L) • (y - x)` for
    -- `j ≤ m = ⌊L / (2 * r)⌋` lie on that half-segment at mutual distance at least `r`, so the
    -- `m + 1 > L / (2 * r)` balls about them are pairwise disjoint.
    set m := ⌊L / (2 * r)⌋₊
    set c : ℕ → E := fun j => x + ((j : ℝ) * r / L) • (y - x)
    have hyx : ‖y - x‖ = L := (dist_eq_norm y x).symm
    have hdist : ∀ i j : ℕ, dist (c i) (c j) = |(i : ℝ) - j| * r := fun i j => by
      simp only [c, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hyx,
        Real.norm_eq_abs, ← sub_div, ← sub_mul, abs_div, abs_mul, abs_of_pos hr]
      rw [abs_of_pos hL]
      field_simp
    have hsub : ∀ j ∈ Finset.range (m + 1), ball (c j) (r / 2) ⊆ s := fun j hj z hz => by
      set t := (j : ℝ) * r / L
      have ht₀ : 0 ≤ t := by positivity
      have ht : t ≤ 1 / 2 := by
        have hj : (j : ℝ) ≤ L / (2 * r) :=
          (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).trans
            (Nat.floor_le (by positivity))
        rw [div_le_iff₀ hL]
        rw [le_div_iff₀ (by positivity)] at hj
        linarith
      -- `z = (1 - t) • b + t • y` with `b = x + (1 - t)⁻¹ • (z - c j)` in `ball x r`.
      have hb : x + (1 - t)⁻¹ • (z - c j) ∈ ball x r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos (by linarith), ← dist_eq_norm, inv_mul_lt_iff₀ (by linarith)]
        rw [mem_ball] at hz
        nlinarith
      convert hs (hball hb) hy (by linarith : (0 : ℝ) ≤ 1 - t) ht₀ (by ring) using 1
      have hc : c j = x + t • (y - x) := rfl
      rw [smul_add, smul_smul, mul_inv_cancel₀ (by linarith : (1 - t) ≠ 0), one_smul, hc]
      first | module
    have hdisj : (Finset.range (m + 1) : Set ℕ).PairwiseDisjoint fun j => ball (c j) (r / 2) :=
      fun i _ j _ hij => ball_disjoint_ball <| by
        rw [hdist, add_halves]
        have : (1 : ℝ) ≤ |(i : ℝ) - j| := by
          rcases lt_or_gt_of_ne hij with h | h
          · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
            exact le_abs.2 (Or.inr (by linarith))
          · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
            exact le_abs.2 (Or.inl (by linarith))
        nlinarith
    have hn : 1 ≤ n := finrank_pos
    have hm : L / (2 * r) < m + 1 := Nat.lt_floor_add_one _
    calc ENNReal.ofReal (L * r ^ (n - 1)) * μ (ball 0 1)
        ≤ ENNReal.ofReal (2 ^ (n + 1) * ((m + 1) * (r / 2) ^ n)) * μ (ball 0 1) := by
          gcongr ENNReal.ofReal ?_ * _
          have hrn : r ^ n = r * r ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
          have h2 : (2 : ℝ) ^ (n + 1) * (r / 2) ^ n = 2 * r ^ n := by
            rw [div_pow, pow_succ]
            field_simp
          rw [div_lt_iff₀ (by positivity)] at hm
          calc L * r ^ (n - 1) ≤ (m + 1) * (2 * r) * r ^ (n - 1) := by gcongr
            _ = 2 ^ (n + 1) * ((m + 1) * (r / 2) ^ n) := by
              rw [mul_left_comm (2 ^ (n + 1) : ℝ), h2, hrn]
              ring
      _ = 2 ^ (n + 1) * ∑ j ∈ Finset.range (m + 1), μ (ball (c j) (r / 2)) := by
          simp only [addHaar_ball μ _ (by positivity : 0 ≤ r / 2), Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
          push_cast
          rw [ENNReal.ofReal_add (by positivity) zero_le_one]
          simp [mul_assoc, n]
      _ = 2 ^ (n + 1) * μ (⋃ j ∈ Finset.range (m + 1), ball (c j) (r / 2)) := by
          rw [measure_biUnion_finset hdisj fun _ _ => measurableSet_ball]
      _ ≤ 2 ^ (n + 1) * μ s := by
          gcongr
          exact iUnion₂_subset hsub

open Function
open scoped Pointwise

/-- Two convex sets in a finite-dimensional real normed space whose interiors are disjoint meet in
a null set for every additive Haar measure, since each differs from its interior by a subset of
its null frontier. The sets need not be closed, bounded or full-dimensional. -/
theorem Convex.aedisjoint_of_disjoint_interior (hs : Convex ℝ s) {t : Set E} (ht : Convex ℝ t)
    (h : Disjoint (interior s) (interior t)) : AEDisjoint μ s t :=
  h.aedisjoint.congr (interior_ae_eq_of_null_frontier (hs.addHaar_frontier μ)).symm
    (interior_ae_eq_of_null_frontier (ht.addHaar_frontier μ)).symm

namespace TauCeti

/-- **Unions of convex sets with disjoint interiors.** If every interior of a member of the
countable family `A` is disjoint from every interior of a member of the countable family `B`, and
all members are convex, then the unions `⋃ i, A i` and `⋃ j, B j` meet in a null set for every
additive Haar measure. The unions need not be convex, and the members need not be closed or
bounded. -/
theorem aedisjoint_iUnion_of_convex {ι κ : Sort*} [Countable ι] [Countable κ] {A : ι → Set E}
    {B : κ → Set E} (hA : ∀ i, Convex ℝ (A i)) (hB : ∀ j, Convex ℝ (B j))
    (h : ∀ i j, Disjoint (interior (A i)) (interior (B j))) :
    AEDisjoint μ (⋃ i, A i) (⋃ j, B j) :=
  AEDisjoint.iUnion_left_iff.2 fun i ↦ AEDisjoint.iUnion_right_iff.2 fun j ↦
    (hA i).aedisjoint_of_disjoint_interior (hB j) (h i j)

/-- **Additivity over convex sets with disjoint interiors.** For a countable family of convex
sets whose interiors are pairwise disjoint, the additive Haar measure of the union is the sum of
the measures of the members, although the members may share boundary points. -/
theorem addHaar_iUnion_of_convex {ι : Type*} [Countable ι] {A : ι → Set E}
    (hA : ∀ i, Convex ℝ (A i)) (h : Pairwise (Disjoint on fun i ↦ interior (A i))) :
    μ (⋃ i, A i) = ∑' i, μ (A i) :=
  measure_iUnion₀ (fun _ _ hij ↦ (hA _).aedisjoint_of_disjoint_interior (hA _) (h hij))
    fun i ↦ (hA i).nullMeasurableSet μ

end TauCeti

/-- **Volume of interior-disjoint translates.** If the translates `v i +ᵥ interior K` of the
interior of a convex set `K` are pairwise disjoint, then the union of the finitely many translates
`v i +ᵥ K` has `card ι` times the additive Haar measure of `K`. The translates may share boundary
points, and `K` need not be closed, bounded or full-dimensional. -/
theorem Convex.addHaar_iUnion_vadd {K : Set E} (hK : Convex ℝ K) {ι : Type*} [Fintype ι]
    {v : ι → E} (h : Pairwise (Disjoint on fun i ↦ v i +ᵥ interior K)) :
    μ (⋃ i, v i +ᵥ K) = Fintype.card ι * μ K := by
  first
  | rw [TauCeti.addHaar_iUnion_of_convex (fun i ↦ hK.vadd (v i))
      (by simpa only [interior_vadd] using h)]
    simp

open Bornology
open scoped ENNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}

/-- A convex set with nonempty interior has finite Haar measure if and only if it is bounded.
The interior hypothesis is essential: an unbounded proper subspace has zero ambient measure. -/
theorem isBounded_iff_measure_ne_top_of_convex (hs : Convex ℝ s)
    (hi : (interior s).Nonempty) : IsBounded s ↔ μ s ≠ ∞ := by
  first
  | refine ⟨fun hb ↦ hb.measure_lt_top.ne, fun hfin ↦ ?_⟩
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact (Set.toFinite s).isBounded
    obtain ⟨x, hx⟩ := hi
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
    have hunit : 0 < (μ (ball (0 : E) 1)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_ne_top
    have hcoeff : 0 < r ^ (finrank ℝ E - 1) * (μ (ball (0 : E) 1)).toReal :=
      mul_pos (pow_pos hr _) hunit
    refine (isBounded_iff_subset_closedBall x).2
      ⟨(2 ^ (finrank ℝ E + 1) * (μ s).toReal) /
        (r ^ (finrank ℝ E - 1) * (μ (ball (0 : E) 1)).toReal), fun y hy ↦ ?_⟩
    rw [mem_closedBall, le_div_iff₀ hcoeff]
    have h := ENNReal.toReal_mono (by finiteness :
        (2 : ℝ≥0∞) ^ (finrank ℝ E + 1) * μ s ≠ ∞)
      (hs.ofReal_dist_mul_pow_mul_addHaar_ball_le hr hball hy)
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal,
      dist_nonneg, le_of_lt hr, mul_assoc] using h

/-- Every positive finite-measure set that agrees almost everywhere with a convex set
has a compact convex representative with nonempty interior. In particular, this applies
to convex sets themselves. Equality is with respect to the given additive Haar measure. -/
theorem exists_isCompact_convex_ae_eq (hpos : 0 < μ s) (hfin : μ s ≠ ∞)
    (hc : ∃ C : Set E, Convex ℝ C ∧ s =ᵐ[μ] C) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧ s =ᵐ[μ] K := by
  first
  | obtain ⟨C, hC, heq⟩ := hc
    have hvol : μ C = μ s := (measure_congr heq).symm
    have hi : (interior C).Nonempty := by
      by_contra hempty
      have hz : μ C = 0 := by
        rw [← measure_interior_of_null_frontier (hC.addHaar_frontier μ),
          Set.not_nonempty_iff_eq_empty.1 hempty, measure_empty]
      exact (hpos.ne' (hvol.symm.trans hz))
    have hb := (isBounded_iff_measure_ne_top_of_convex μ hC hi).2 (hvol.trans_ne hfin)
    exact ⟨closure C, isCompact_of_isClosed_isBounded isClosed_closure hb.closure, hC.closure,
      hi.mono (interior_mono subset_closure),
      heq.trans (closure_ae_eq_of_null_frontier (hC.addHaar_frontier μ)).symm⟩

end MeasureTheory.Measure
end -- closes the original EOF section from source line 50
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Convex/Measure.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyNormalization.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# Uniform normalization of actual realizing tuples

This is a geometric compactness normalization. Its radius depends only on the
ambient dimension. It is deliberately distinct from the explicit numerical
radius needed by the paper's computable grid construction.
-/

noncomputable section
open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

theorem affine_image_eq_translate_linear_image {d : ℕ}
    (T : Space d ≃ᵃ[ℝ] Space d) (K : Body d) :
    T '' (K : Set (Space d)) =
      (translateBody (T 0) (mapBody T.linear.toContinuousLinearEquiv.toContinuousLinearMap K) :
        Set (Space d)) := by
  first
  | ext y
    simp only [coe_translateBody, coe_mapBody, Set.mem_vadd_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨T.linear x, ⟨x, hx, rfl⟩, ?_⟩
      simpa only [vadd_eq_add, add_zero, add_comm] using (T.map_vadd 0 x).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change T x = T 0 + T.linear x
      simpa only [vadd_eq_add, add_zero, add_comm] using T.map_vadd 0 x

theorem bodyVolume_affine_image {d : ℕ} (T : Space d ≃ᵃ[ℝ] Space d) (K : Body d) :
    volume.real (T '' (K : Set (Space d))) =
      |LinearMap.det T.linear.toLinearMap| * bodyVolume K := by
  first
  | rw [affine_image_eq_translate_linear_image]
    change bodyVolume (translateBody _ (mapBody _ K)) = _
    rw [bodyVolume_translate, bodyVolume_map]
    rfl

/-- Every total-volume-one realization admits independently translated bodies
and a common linear volume normalization inside a fixed ball. No coefficient
positivity or polynomial-existence assertion is used as an assumption. -/
theorem exists_uniform_normalization (d : ℕ) (hd : 0 < d) :
    ∃ R > 0, ∀ (n : ℕ) (K : Fin n → Body d) (c : Coefficients n d),
      Realizes K c → (∑ α, c α) = 1 →
      ∃ L : Fin n → Body d, Realizes L c ∧
        ∀ i, (0 : Space d) ∈ L i ∧ (L i : Set (Space d)) ⊆ closedBall 0 R := by
  first
  | classical
    obtain ⟨r, hr, hnormal⟩ :=
      TauCeti.exists_affineEquiv_ball_subset_image_subset_ball (Space d)
    let m : ℝ := volume.real (ball (0 : Space d) r)
    have hm : 0 < m := ENNReal.toReal_pos (measure_ball_pos volume 0 hr).ne' measure_ball_ne_top
    let q : ℝ := m ^ (-((d : ℝ)⁻¹))
    have hq : 0 < q := Real.rpow_pos_of_pos hm _
    refine ⟨2 * q, mul_pos zero_lt_two hq, ?_⟩
    intro n K c hK hc
    let S : Body d := ∑ i, K i
    have hSvol : bodyVolume S = 1 := hK.sum_coefficients.symm.trans hc
    have hSpos : 0 < volume (S : Set (Space d)) := by
      first
      | have ht : 0 < (volume (S : Set (Space d))).toReal := by
          change 0 < bodyVolume S
          rw [hSvol]
          exact zero_lt_one
        exact (ENNReal.toReal_pos_iff.mp ht).1
    obtain ⟨T, hsmall, hlarge⟩ := hnormal (S : Set (Space d)) S.convex S.isBounded
      ((S.convex.addHaar_pos_iff_interior_nonempty (μ := volume)).mp hSpos)
    let f : Space d →L[ℝ] Space d := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
    let D : ℝ := |LinearMap.det f.toLinearMap|
    have hTD : volume.real (T '' (S : Set (Space d))) = D := by
      first
      | rw [bodyVolume_affine_image, hSvol, mul_one]
        rfl
    have hmD : m ≤ D := by
      first
      | rw [← hTD]
        exact measureReal_mono hsmall (by
          rw [affine_image_eq_translate_linear_image]
          exact (translateBody (T 0) (mapBody f S)).isCompact.measure_lt_top.ne)
    have hD : 0 < D := hm.trans_le hmD
    let a : ℝ := D ^ (-((d : ℝ)⁻¹))
    have ha : 0 < a := Real.rpow_pos_of_pos hD _
    have haq : a ≤ q := Real.rpow_le_rpow_of_nonpos hm hmD
      (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg d)))
    have hapow : a ^ d = D⁻¹ := by
      first
      | dsimp [a]
        rw [Real.rpow_neg hD.le, inv_pow, Real.rpow_inv_natCast_pow hD.le hd.ne']
    choose p hp using fun i => (K i).nonempty
    let P : Fin n → Body d := fun i => translateBody (-p i) (K i)
    have hP0 : ∀ i, (0 : Space d) ∈ P i := by
      first
      | intro i
        simpa [P, mem_translateBody] using hp i
    have hpsum : (∑ i, p i) ∈ S := by
      first
      | exact (mem_sum_body K _).mpr ⟨p, hp, rfl⟩
    have hPsum : ∑ i, P i = translateBody (-(∑ i, p i)) S := by
      first
      | simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib, P, S] using
          weightedSum_translate K (fun i => -p i) (fun _ => 1)
    have hfnorm : ∀ u ∈ (∑ i, P i : Body d), ‖f u‖ < 2 := by
      first
      | intro u hu
        rw [hPsum, mem_translateBody, sub_neg_eq_add] at hu
        have h₁ := hlarge (Set.mem_image_of_mem T hu)
        have h₂ := hlarge (Set.mem_image_of_mem T hpsum)
        rw [mem_ball_zero_iff] at h₁ h₂
        have hfu : f u = T (u + ∑ i, p i) - T (∑ i, p i) := by
          apply eq_sub_iff_add_eq.mpr
          change T.linear u + T (∑ i, p i) = T (u + ∑ i, p i)
          simpa only [vadd_eq_add] using (T.map_vadd (∑ i, p i) u).symm
        rw [hfu]
        exact (norm_sub_le _ _).trans_lt (by linarith)
    let L : Fin n → Body d := fun i => a • mapBody f (P i)
    have hreal : Realizes L c := by
      first
      | have h := ((hK.translate (fun i => -p i)).map f).dilate ha.le
        have hscale : a ^ d • (D • c) = c := by
          rw [smul_smul, hapow, inv_mul_cancel₀ hD.ne', one_smul]
        change Realizes L (a ^ d • (D • c)) at h
        rwa [hscale] at h
    refine ⟨L, hreal, fun i => ⟨?_, ?_⟩⟩
    · change (0 : Space d) ∈ a • (mapBody f (P i) : Set (Space d))
      exact ⟨0, ⟨0, hP0 i, map_zero f⟩, smul_zero _⟩
    · rintro y ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ha.le]
      have huS := body_le_sum_of_zero_mem P hP0 i hu
      have hbound := hfnorm u huS
      calc
        a * ‖f u‖ ≤ a * 2 := mul_le_mul_of_nonneg_left hbound.le ha.le
        _ ≤ q * 2 := mul_le_mul_of_nonneg_right haq zero_le_two
        _ = 2 * q := mul_comm _ _

end VolumePolynomials
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodyNormalization.lean -/

/- BEGIN SOURCE: VolumePolynomials/ClosedVolumeLocus.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# Closedness of the literal volume-polynomial realization locus

The argument includes zero-volume limits. Compactness is used for tuples with
normalized total volume, and geometric monotonicity controls the zero stratum.
No general mixed-volume or coefficient-positivity theorem is assumed.
-/

noncomputable section
open Set MeasureTheory Finset Metric Filter Topology
open scoped Pointwise BigOperators

namespace VolumePolynomials

theorem continuous_coefficientSum (n d : ℕ) :
    Continuous (fun c : Coefficients n d => ∑ α, c α) := by fun_prop

theorem normalized_mem_boundedLocus {d : ℕ} (hd : 0 < d) {R : ℝ}
    (hR : ∀ (n : ℕ) (K : Fin n → Body d) (c : Coefficients n d),
      Realizes K c → (∑ α, c α) = 1 →
      ∃ L : Fin n → Body d, Realizes L c ∧
        ∀ i, (0 : Space d) ∈ L i ∧ (L i : Set (Space d)) ⊆ closedBall 0 R)
    {n : ℕ} {c : Coefficients n d} (hc : c ∈ VolumeLocus n d)
    (hs : 0 < ∑ α, c α) :
    (∑ α, c α)⁻¹ • c ∈ boundedVolumeLocus n d (closedBall 0 R) := by
  first
  | have hmem := smul_mem_volumeLocus hd hc (inv_nonneg.mpr hs.le)
    obtain ⟨K, hK⟩ := hmem
    have hsum : ∑ α, ((∑ β, c β)⁻¹ • c) α = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
    obtain ⟨L, hL, hbound⟩ := hR n K _ hK hsum
    exact ⟨L, hbound, hL⟩

/-- The realization locus for arbitrary compact convex bodies is closed in the
full finite-dimensional coefficient space, in every positive dimension. -/
theorem isClosed_volumeLocus (n d : ℕ) (hd : 0 < d) : IsClosed (VolumeLocus n d) := by
  first
  | obtain ⟨R, hRpos, hR⟩ := exists_uniform_normalization d hd
    have hcompact := isCompact_boundedVolumeLocus n d (isCompact_closedBall (0 : Space d) R)
    apply IsSeqClosed.isClosed
    intro u c hu huc
    have hsum : Tendsto (fun k => ∑ α, u k α) atTop (𝓝 (∑ α, c α)) :=
      (continuous_coefficientSum n d).continuousAt.tendsto.comp huc
    have hsum_nonneg : 0 ≤ ∑ α, c α := by
      apply le_of_tendsto_of_tendsto' tendsto_const_nhds hsum
      intro k
      obtain ⟨K, hK⟩ := hu k
      exact hK.sum_coefficients_nonneg
    by_cases hs0 : (∑ α, c α) = 0
    · have hc0 : c = 0 := by
        apply coefficients_eq_of_evaluate_nonneg
        intro t ht
        have heval : Tendsto (fun k => evaluate (u k) t) atTop (𝓝 (evaluate c t)) :=
          (continuous_evaluate t).continuousAt.tendsto.comp huc
        have hlow : 0 ≤ evaluate c t := by
          apply le_of_tendsto_of_tendsto' tendsto_const_nhds heval
          intro k
          obtain ⟨K, hK⟩ := hu k
          exact hK.evaluate_nonneg ht
        have hupp : evaluate c t ≤ (1 + ∑ i, t i) ^ d * ∑ α, c α := by
          apply le_of_tendsto_of_tendsto' heval (tendsto_const_nhds.mul hsum)
          intro k
          obtain ⟨K, hK⟩ := hu k
          exact hK.evaluate_le_sum t ht
        rw [hs0, mul_zero] at hupp
        simpa [evaluate] using le_antisymm hupp hlow
      rw [hc0]
      exact zero_mem_volumeLocus hd
    · have hspos : 0 < ∑ α, c α := lt_of_le_of_ne hsum_nonneg (Ne.symm hs0)
      have hevent : ∀ᶠ k in atTop, 0 < ∑ α, u k α := hsum.eventually_const_lt hspos
      have hnorm : Tendsto (fun k => (∑ α, u k α)⁻¹ • u k) atTop
          (𝓝 ((∑ α, c α)⁻¹ • c)) := (hsum.inv₀ hs0).smul huc
      have hnormalized : (∑ α, c α)⁻¹ • c ∈ boundedVolumeLocus n d (closedBall 0 R) := by
        apply hcompact.isClosed.mem_of_tendsto hnorm
        filter_upwards [hevent] with k hk
        exact normalized_mem_boundedLocus hd hR (hu k) hk
      have hmem := smul_mem_volumeLocus hd
        (boundedVolumeLocus_subset n d _ hnormalized) hspos.le
      simpa only [smul_smul, mul_inv_cancel₀ hs0, one_smul] using hmem

end VolumePolynomials
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ClosedVolumeLocus.lean -/

/- BEGIN SOURCE: TauCeti/Data/List/PermanencesMinusVariations.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Permanences minus variations with zero gaps

`List.permanencesMinusVariations` is the integer-valued sign statistic used in
signed subresultant formulas for Cauchy indices. Leading and trailing zeros are
ignored. Two consecutive nonzero entries with `k` intervening zeros contribute
`(-1) ^ (Nat.choose k 2) * sign(a) * sign(b)` when `k` is even, and zero otherwise.
In particular, interior zeros cannot simply be deleted.

The zero-gap recursion characterizes the statistic, and sign-preserving and
sign-reversing maps preserve it; in particular, so does scaling every entry by a
nonzero constant. For a list without zeros it is the number of
adjacent pairs minus twice Mathlib's `List.signVariations`.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
second edition, Chapter 4 (permanences minus variations of signed subresultants).
-/

public section

namespace TauCeti

private def gapWeight (k : ℕ) : ℤ :=
  if Even k then (-1) ^ (Nat.choose k 2) else 0

private def pmvAux (a : SignType) (k : ℕ) : List SignType → ℤ
  | [] => 0
  | b :: l => if b = 0 then pmvAux a (k + 1) l
    else gapWeight k * (a : ℤ) * (b : ℤ) + pmvAux b 0 l

private theorem pmvAux_zero (k : ℕ) (l : List SignType) :
    pmvAux 0 k l = pmvAux 0 0 l := by
  induction l generalizing k with
  | nil => rfl
  | cons b l ih =>
    by_cases hb : b = 0
    · simp [pmvAux, hb, ih]
    · simp [pmvAux, hb]

private theorem pmvAux_replicate (a : SignType) (k n : ℕ) :
    pmvAux a k (List.replicate n 0) = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, pmvAux, ih]

private theorem pmvAux_replicate_append (a : SignType) (k n : ℕ) (l : List SignType) :
    pmvAux a k (List.replicate n 0 ++ l) = pmvAux a (k + n) l := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, pmvAux, ite_true, ih]
    exact congrArg (fun t => pmvAux a t l) (by omega)

/-- Sum over consecutive nonzero entries, retaining the parity and length of
each intervening zero gap. Leading and trailing zeros contribute nothing. -/
def _root_.List.permanencesMinusVariations {R : Type*} [Zero R] [LinearOrder R]
    (l : List R) : ℤ := pmvAux 0 0 (l.map SignType.sign)

variable {R S : Type*} [Zero R] [LinearOrder R] [Zero S] [LinearOrder S]

@[simp] theorem _root_.List.permanencesMinusVariations_nil :
    ([] : List R).permanencesMinusVariations = 0 := (rfl)

@[simp] theorem _root_.List.permanencesMinusVariations_zero_cons (l : List R) :
    (0 :: l).permanencesMinusVariations = l.permanencesMinusVariations := by
  simp [List.permanencesMinusVariations, pmvAux, pmvAux_zero]

@[simp] theorem _root_.List.permanencesMinusVariations_singleton (a : R) :
    [a].permanencesMinusVariations = 0 := by
  simp [List.permanencesMinusVariations, pmvAux]

@[simp] theorem _root_.List.permanencesMinusVariations_replicate_zero (n : ℕ) :
    (List.replicate n (0 : R)).permanencesMinusVariations = 0 := by
  simp [List.permanencesMinusVariations, pmvAux_replicate]

/-- A prefix of zeros is ignored. -/
@[simp] theorem _root_.List.permanencesMinusVariations_replicate_zero_append
    (n : ℕ) (l : List R) :
    (List.replicate n 0 ++ l).permanencesMinusVariations =
      l.permanencesMinusVariations := by
  simp [List.permanencesMinusVariations, pmvAux_replicate_append, pmvAux_zero]

private theorem pmvAux_append_replicate (a : SignType) (k n : ℕ) (l : List SignType) :
    pmvAux a k (l ++ List.replicate n 0) = pmvAux a k l := by
  induction l generalizing a k with
  | nil => simp [pmvAux, pmvAux_replicate]
  | cons b l ih => simp [pmvAux, ih]

/-- A suffix of zeros is ignored. -/
@[simp] theorem _root_.List.permanencesMinusVariations_append_replicate_zero
    (l : List R) (n : ℕ) :
    (l ++ List.replicate n 0).permanencesMinusVariations =
      l.permanencesMinusVariations := by
  simp [List.permanencesMinusVariations, pmvAux_append_replicate]

/-- A list with only its head possibly nonzero has no adjacent nonzero pair. -/
@[simp] theorem _root_.List.permanencesMinusVariations_cons_replicate_zero
    (a : R) (n : ℕ) : (a :: List.replicate n 0).permanencesMinusVariations = 0 := by
  simpa using List.permanencesMinusVariations_append_replicate_zero [a] n

/-- Recursion across a zero gap ending at a nonzero entry. This also specifies
the sign correction for even gaps and the cancellation for odd gaps. -/
theorem _root_.List.permanencesMinusVariations_cons_replicate_zero_append
    {a b : R} (hb : b ≠ 0) (k : ℕ) (l : List R) :
    (a :: (List.replicate k 0 ++ b :: l)).permanencesMinusVariations =
      (if Even k then (-1 : ℤ) ^ (Nat.choose k 2) *
        (SignType.sign a : ℤ) * (SignType.sign b : ℤ) else 0) +
      (b :: l).permanencesMinusVariations := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [List.permanencesMinusVariations, pmvAux, ha, hb,
      pmvAux_replicate_append, gapWeight]

/-- Without an intervening zero, an adjacent pair contributes the product of
its signs. -/
theorem _root_.List.permanencesMinusVariations_cons_cons {a b : R}
    (hb : b ≠ 0) (l : List R) :
    (a :: b :: l).permanencesMinusVariations =
      (SignType.sign a : ℤ) * (SignType.sign b : ℤ) +
        (b :: l).permanencesMinusVariations := by
  simpa using List.permanencesMinusVariations_cons_replicate_zero_append hb 0 l

private theorem pmvAux_append_cons (s a : SignType) (ha : a ≠ 0) (k : ℕ)
    (l m : List SignType) :
    pmvAux s k (l ++ a :: m) = pmvAux s k (l ++ [a]) + pmvAux a 0 m := by
  induction l generalizing s k with
  | nil => simp [pmvAux, ha]
  | cons b l ih =>
    simp only [List.cons_append, pmvAux, ih]
    split_ifs <;> omega

/-- Joining two blocks whose boundary entries are nonzero adds precisely the
contribution of the intervening zero gap to their separate statistics. -/
theorem _root_.List.permanencesMinusVariations_append_replicate_zero_cons
    (l m : List R) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    (l ++ a :: (List.replicate k 0 ++ b :: m)).permanencesMinusVariations =
      (l ++ [a]).permanencesMinusVariations +
        (if Even k then (-1 : ℤ) ^ (Nat.choose k 2) *
          (SignType.sign a : ℤ) * (SignType.sign b : ℤ) else 0) +
        (b :: m).permanencesMinusVariations := by
  simp only [List.permanencesMinusVariations, List.map_append, List.map_cons,
    List.map_replicate, sign_zero, List.map_nil]
  rw [pmvAux_append_cons _ _ (sign_ne_zero.mpr ha)]
  simp [pmvAux_replicate_append, pmvAux, hb, gapWeight, add_assoc]

/-- The statistic depends only on the ordered list of signs, including zeros. -/
theorem _root_.List.permanencesMinusVariations_congr {l : List R} {m : List S}
    (h : l.map SignType.sign = m.map SignType.sign) :
    l.permanencesMinusVariations = m.permanencesMinusVariations := by
  simp only [List.permanencesMinusVariations, h]

/-- Sign-preserving maps preserve permanences minus variations. -/
theorem _root_.List.permanencesMinusVariations_map {f : R → S}
    (hf : ∀ x, SignType.sign (f x) = SignType.sign x) (l : List R) :
    (l.map f).permanencesMinusVariations = l.permanencesMinusVariations := by
  apply List.permanencesMinusVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left fun x _ => hf x

@[simp] theorem _root_.List.permanencesMinusVariations_map_sign (l : List R) :
    (l.map SignType.sign).permanencesMinusVariations = l.permanencesMinusVariations := by
  apply List.permanencesMinusVariations_map
  intro x
  cases SignType.sign x <;> decide

private theorem pmvAux_neg (a : SignType) (k : ℕ) (l : List SignType) :
    pmvAux (-a) k (l.map (- ·)) = pmvAux a k l := by
  induction l generalizing a k with
  | nil => rfl
  | cons b l ih => simp [pmvAux, ih]

/-- Reversing every sign preserves the products of consecutive nonzero signs. -/
theorem _root_.List.permanencesMinusVariations_map_of_sign_eq_neg {f : R → S}
    (hf : ∀ x, SignType.sign (f x) = -SignType.sign x) (l : List R) :
    (l.map f).permanencesMinusVariations = l.permanencesMinusVariations := by
  have h : (l.map f).map SignType.sign = (l.map SignType.sign).map (- ·) := by
    simp only [List.map_map]
    exact List.map_congr_left fun x _ => hf x
  simp only [List.permanencesMinusVariations, h]
  simpa using pmvAux_neg 0 0 (l.map SignType.sign)

/-- Multiplying every entry by a nonzero constant preserves permanences minus
variations. -/
@[simp] theorem _root_.List.permanencesMinusVariations_map_mul_left {K : Type*} [Ring K]
    [LinearOrder K] [IsStrictOrderedRing K] {c : K} (hc : c ≠ 0) (l : List K) :
    (l.map (c * ·)).permanencesMinusVariations = l.permanencesMinusVariations := by
  rcases hc.lt_or_gt with hc | hc
  · exact List.permanencesMinusVariations_map_of_sign_eq_neg
      (fun x => by simp [sign_mul, sign_neg hc]) l
  · exact List.permanencesMinusVariations_map (fun x => by simp [sign_mul, sign_pos hc]) l

/-- On a list with no zeros, permanences minus variations is the number of
adjacent pairs minus twice the number of sign changes. -/
theorem _root_.List.permanencesMinusVariations_eq_length_sub_two_mul_signVariations
    (l : List R) (h : ∀ a ∈ l, a ≠ 0) :
    l.permanencesMinusVariations = ((l.length - 1 : ℕ) : ℤ) - 2 * l.signVariations := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have ha := h a (by simp)
      have hb := h b (by simp)
      have ht : ∀ x ∈ b :: l, x ≠ 0 := fun x hx => h x (by simp [hx])
      rw [List.permanencesMinusVariations_cons_cons hb,
        List.signVariations_cons_cons_of_ne_zero _ ha hb, ih ht]
      have hs : (SignType.sign a : ℤ) * (SignType.sign b : ℤ) =
          1 - 2 * (if SignType.sign a = SignType.sign b then (0 : ℤ) else 1) := by
        have ha' := sign_ne_zero.mpr ha
        have hb' := sign_ne_zero.mpr hb
        revert ha' hb'
        cases SignType.sign a <;> cases SignType.sign b <;> decide
      simp only [hs, List.length_cons, Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_one, Nat.cast_ite, Nat.cast_zero]
      omega

end TauCeti
end -- closes the original EOF section from source line 30
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/List/PermanencesMinusVariations.lean -/

/- BEGIN SOURCE: TauCeti/Data/Set/Lattice.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sets cut out by conditions on a tuple of values

A set defined by a condition `Φ` on the tuple of values of a family of functions is the union,
over the tuples satisfying `Φ`, of the fibres of the family over those tuples.

## Main results

* `TauCeti.setOf_apply_eq_biUnion_iInter`:
  `{x | Φ (g · x)} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i}`.
-/

public section

open Set

namespace TauCeti

/-- The set of points where a family of functions `g i` satisfies a condition `Φ` on its tuple of
values is the union, over the tuples `ε` satisfying `Φ`, of the sets where `g i = ε i` for all
`i`. -/
theorem setOf_apply_eq_biUnion_iInter {α β ι : Type*} (g : ι → α → β) (Φ : (ι → β) → Prop) :
    {x | Φ fun i => g i x} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
  exact ⟨fun h => ⟨_, h, fun _ => rfl⟩, fun ⟨ε, hε, h⟩ => (funext h).symm ▸ hε⟩

end TauCeti
end -- closes the original EOF section from source line 22
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Set/Lattice.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/SetAlgebra.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Algebras of sets generated by sign conditions

Given a class of functions `α → R`, consider the algebra of sets generated by their zero sets
`{x | f x = 0}` and positivity sets `{x | 0 < f x}`. Every member of it is described by a condition
on the signs of finitely many functions of the class.

## Main results

* `TauCeti.exists_eq_setOf_sign_of_mem_generateSetAlgebra`: the sign-condition normal form.
* `MeasureTheory.IsSetAlgebra.preimage`: the sets whose preimages under a fixed map lie in an
  algebra of sets form an algebra of sets.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- **Sign-condition normal form.** Every member of the algebra of sets generated by the zero sets
and the positivity sets of the functions `f : α → R` satisfying `P` is described by a condition on
the signs of finitely many functions satisfying `P`. -/
theorem exists_eq_setOf_sign_of_mem_generateSetAlgebra {α R : Type*} [Zero R] [LinearOrder R]
    {P : (α → R) → Prop} {t : Set α}
    (ht : t ∈ generateSetAlgebra ({t | ∃ f, P f ∧ t = {x | f x = 0}} ∪
      {t | ∃ f, P f ∧ t = {x | 0 < f x}})) :
    ∃ (m : ℕ) (f : Fin m → α → R), (∀ i, P (f i)) ∧
      ∃ Φ : (Fin m → SignType) → Prop, t = {x | Φ fun i => SignType.sign (f i x)} := by
  induction ht using generateSetAlgebra_induction with
  | base u hu =>
    rcases hu with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
    · exact ⟨1, fun _ => f, fun _ => hf, fun ε => ε 0 = 0, by simp⟩
    · exact ⟨1, fun _ => f, fun _ => hf, fun ε => ε 0 = 1, by simp [sign_eq_one_iff]⟩
  | empty => exact ⟨0, Fin.elim0, fun i => i.elim0, fun _ => False, by simp⟩
  | compl u _ ih =>
    obtain ⟨m, f, hf, Φ, rfl⟩ := ih
    exact ⟨m, f, hf, fun ε => ¬Φ ε, compl_ofPred _⟩
  | union u v _ _ ihu ihv =>
    obtain ⟨m, f, hf, Φ, rfl⟩ := ihu
    obtain ⟨m', f', hf', Φ', rfl⟩ := ihv
    refine ⟨m + m', Fin.append f f', Fin.addCases (by simpa using hf) (by simpa using hf'),
      fun ε => Φ (fun i => ε (Fin.castAdd m' i)) ∨ Φ' (fun i => ε (Fin.natAdd m i)), ?_⟩
    ext x
    simp

end TauCeti

namespace MeasureTheory.IsSetAlgebra

/-- The sets whose preimages under a map `g` lie in an algebra of sets form an algebra of sets.
Combined with `IsSetAlgebra.generateSetAlgebra_subset`, this shows that a preimage of a member of
a generated algebra lies in a given algebra once the preimages of the generators do. -/
theorem preimage {α β : Type*} {𝒜 : Set (Set β)} (h𝒜 : IsSetAlgebra 𝒜) (g : β → α) :
    IsSetAlgebra {t : Set α | g ⁻¹' t ∈ 𝒜} where
  empty_mem := h𝒜.empty_mem
  compl_mem _ ht := h𝒜.compl_mem ht
  union_mem _ _ ht ht' := h𝒜.union_mem ht ht'

end MeasureTheory.IsSetAlgebra
end -- closes the original EOF section from source line 25
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/SetAlgebra.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Semialgebraic sets

A subset of `σ → R`, for a commutative ring `R` with a chosen linear order, is *semialgebraic* when
it is a finite Boolean combination of polynomial zero sets `{x | p(x) = 0}` and positivity sets
`{x | 0 < p(x)}`. We define `TauCeti.IsSemialgebraic` as membership in the algebra of sets
(`MeasureTheory.generateSetAlgebra`) generated by these basic sets. This is the intrinsic,
quantifier-free definition. When `R` is a real closed field, closure under coordinate projection is
the Tarski–Seidenberg theorem, a consequence of cylindrical algebraic decomposition; projection
closure is not built into the definition.

Every closure property proved here follows directly from the definition:

* the Boolean operations, including finite unions and intersections;
* every polynomial sign condition, such as `{x | p(x) ≤ q(x)}` or `{x | sign p(x) = ε}`;
* any condition on the signs of finitely many polynomials
  (`TauCeti.isSemialgebraic_setOf_sign_eval`), in particular a prescribed permanences minus
  variations of their values (`TauCeti.isSemialgebraic_setOf_permanencesMinusVariations_eval`);
* the vanishing of a prescribed set of coefficients of a polynomial family
  `P : Polynomial (MvPolynomial σ R)` (`TauCeti.isSemialgebraic_setOf_forall_coeff_eq_zero`);
* inverse images under polynomial maps (`TauCeti.IsSemialgebraic.preimage_eval`), and hence
  under changes of coordinates, in particular coordinate permutations;
* products, in the form `σ ⊕ τ → R` and in the form `Fin (m + n) → R`;
* the sections `{x : Fin n → R | Fin.cons t x ∈ s}` and `{y : Fin 1 → R | Fin.cons (y 0) x ∈ s}`
  of a subset of `Fin (n + 1) → R`, which are the horizontal and vertical slices of a cylinder
  over `Fin n → R` with distinguished coordinate `0`; the vertical slice is a subset of
  `Fin 1 → R`, the one-coordinate space of the definition.

Conversely, every semialgebraic set is described by a condition on the signs of finitely many
polynomials (`TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`), and so membership in it depends
on only finitely many coordinates (`TauCeti.IsSemialgebraic.exists_finset_mem_iff_of_eqOn`).

Closure under projection is recorded as the property `TauCeti.HasSemialgebraicProjections R` of the
ordered ring `R`, with field `TauCeti.HasSemialgebraicProjections.isSemialgebraic_image_tail`.
Its consequences, such as quantifier elimination and the image and composition laws of
semialgebraic functions, are stated under this assumption.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2, for semi-algebraic sets.

The generated algebra of sets is Mathlib's `MeasureTheory.generateSetAlgebra`, from
`Mathlib/MeasureTheory/SetAlgebra.lean` by Etienne Marion.
-/

public section

open MvPolynomial MeasureTheory Set

namespace TauCeti

variable {σ τ R : Type*} [CommRing R] [LinearOrder R]

/-- A set `s ⊆ σ → R` is *semialgebraic* if it belongs to the algebra of sets (closed under
complements and finite unions) generated by the polynomial zero sets `{x | p(x) = 0}` and the
positivity sets `{x | 0 < p(x)}`, for `p : MvPolynomial σ R`. -/
def IsSemialgebraic (s : Set (σ → R)) : Prop :=
  s ∈ generateSetAlgebra
    (range (fun p : MvPolynomial σ R => {x | eval x p = 0}) ∪
      range (fun p : MvPolynomial σ R => {x | 0 < eval x p}))

/-- A set is semialgebraic if and only if it belongs to the algebra of sets generated by the
polynomial zero sets and the polynomial positivity sets. -/
theorem isSemialgebraic_def {s : Set (σ → R)} :
    IsSemialgebraic s ↔ s ∈ generateSetAlgebra
      (range (fun p : MvPolynomial σ R => {x | eval x p = 0}) ∪
        range (fun p : MvPolynomial σ R => {x | 0 < eval x p})) :=
  Iff.rfl

/-- The zero set of a polynomial is semialgebraic. -/
theorem isSemialgebraic_eval_eq_zero (p : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | eval x p = 0} :=
  self_subset_generateSetAlgebra (Or.inl ⟨p, rfl⟩)

/-- The positivity set of a polynomial is semialgebraic. -/
theorem isSemialgebraic_eval_pos (p : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | 0 < eval x p} :=
  self_subset_generateSetAlgebra (Or.inr ⟨p, rfl⟩)

/-- The semialgebraic sets form an algebra of sets. -/
theorem isSetAlgebra_setOf_isSemialgebraic :
    IsSetAlgebra {s : Set (σ → R) | IsSemialgebraic s} :=
  isSetAlgebra_generateSetAlgebra

/-- The semialgebraic sets form the smallest algebra of sets containing every polynomial zero set
and every polynomial positivity set. -/
theorem setOf_isSemialgebraic_subset {ℬ : Set (Set (σ → R))} (hℬ : IsSetAlgebra ℬ)
    (eq_zero : ∀ p : MvPolynomial σ R, {x | eval x p = 0} ∈ ℬ)
    (pos : ∀ p : MvPolynomial σ R, {x | 0 < eval x p} ∈ ℬ) :
    {s : Set (σ → R) | IsSemialgebraic s} ⊆ ℬ :=
  hℬ.generateSetAlgebra_subset <| union_subset (range_subset_iff.2 eq_zero)
    (range_subset_iff.2 pos)

/-- Induction principle for semialgebraic sets: a property of sets that holds for polynomial zero
sets, polynomial positivity sets and the empty set, and is preserved by complements and binary
unions, holds for every semialgebraic set. -/
@[elab_as_elim]
theorem IsSemialgebraic.induction {motive : Set (σ → R) → Prop}
    (eq_zero : ∀ p : MvPolynomial σ R, motive {x | eval x p = 0})
    (pos : ∀ p : MvPolynomial σ R, motive {x | 0 < eval x p})
    (empty : motive ∅) (compl : ∀ s, IsSemialgebraic s → motive s → motive sᶜ)
    (union : ∀ s t, IsSemialgebraic s → IsSemialgebraic t → motive s → motive t →
      motive (s ∪ t))
    {s : Set (σ → R)} (hs : IsSemialgebraic s) : motive s := by
  induction hs using generateSetAlgebra_induction with
  | base u hu => rcases hu with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;> simp only [eq_zero, pos]
  | empty => exact empty
  | compl u hu ih => exact compl u hu ih
  | union u v hu hv ihu ihv => exact union u v hu hv ihu ihv

/-! ### Boolean operations -/

/-- The empty set is semialgebraic. -/
@[simp]
theorem isSemialgebraic_empty : IsSemialgebraic (∅ : Set (σ → R)) :=
  isSetAlgebra_setOf_isSemialgebraic.empty_mem

/-- The whole space is semialgebraic. -/
@[simp]
theorem isSemialgebraic_univ : IsSemialgebraic (univ : Set (σ → R)) :=
  isSetAlgebra_setOf_isSemialgebraic.univ_mem

/-- The complement of a semialgebraic set is semialgebraic. -/
theorem IsSemialgebraic.compl {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic sᶜ :=
  isSetAlgebra_setOf_isSemialgebraic.compl_mem hs

/-- A set whose complement is semialgebraic is semialgebraic. -/
theorem IsSemialgebraic.of_compl {s : Set (σ → R)} (hs : IsSemialgebraic sᶜ) :
    IsSemialgebraic s :=
  compl_compl s ▸ hs.compl

/-- The complement of a set is semialgebraic if and only if the set is. -/
@[simp]
theorem isSemialgebraic_compl_iff {s : Set (σ → R)} :
    IsSemialgebraic sᶜ ↔ IsSemialgebraic s :=
  ⟨.of_compl, .compl⟩

/-- The union of two semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraic.union {s t : Set (σ → R)} (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) : IsSemialgebraic (s ∪ t) :=
  isSetAlgebra_setOf_isSemialgebraic.union_mem hs ht

/-- The intersection of two semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraic.inter {s t : Set (σ → R)} (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) : IsSemialgebraic (s ∩ t) :=
  isSetAlgebra_setOf_isSemialgebraic.inter_mem hs ht

/-- The difference of two semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraic.sdiff {s t : Set (σ → R)} (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) : IsSemialgebraic (s \ t) :=
  isSetAlgebra_setOf_isSemialgebraic.sdiff_mem hs ht

/-- A finite union of semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraic.biUnion {ι : Type*} {S : Set ι} (hS : S.Finite)
    {s : ι → Set (σ → R)} (hs : ∀ i ∈ S, IsSemialgebraic (s i)) :
    IsSemialgebraic (⋃ i ∈ S, s i) := by
  simpa using isSetAlgebra_setOf_isSemialgebraic.biUnion_mem hS.toFinset (by simpa using hs)

/-- A finite intersection of semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraic.biInter {ι : Type*} {S : Set ι} (hS : S.Finite)
    {s : ι → Set (σ → R)} (hs : ∀ i ∈ S, IsSemialgebraic (s i)) :
    IsSemialgebraic (⋂ i ∈ S, s i) := by
  simpa using isSetAlgebra_setOf_isSemialgebraic.biInter_mem hS.toFinset (by simpa using hs)

/-- A union of finitely many semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraic.iUnion {ι : Type*} [Finite ι] {s : ι → Set (σ → R)}
    (hs : ∀ i, IsSemialgebraic (s i)) : IsSemialgebraic (⋃ i, s i) := by
  simpa using IsSemialgebraic.biUnion finite_univ fun i _ => hs i

/-- An intersection of finitely many semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraic.iInter {ι : Type*} [Finite ι] {s : ι → Set (σ → R)}
    (hs : ∀ i, IsSemialgebraic (s i)) : IsSemialgebraic (⋂ i, s i) := by
  simpa using IsSemialgebraic.biInter finite_univ fun i _ => hs i

/-! ### Polynomial sign conditions -/

/-- The set where a polynomial does not vanish is semialgebraic. -/
theorem isSemialgebraic_eval_ne_zero (p : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | eval x p ≠ 0} := by
  simpa only [compl_ofPred] using (isSemialgebraic_eval_eq_zero p).compl

/-- The set where two polynomials agree is semialgebraic. -/
theorem isSemialgebraic_eval_eq (p q : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | eval x p = eval x q} := by
  simpa [sub_eq_zero] using isSemialgebraic_eval_eq_zero (p - q)

/-- The set where a polynomial is nonpositive is semialgebraic. -/
theorem isSemialgebraic_eval_nonpos (p : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | eval x p ≤ 0} := by
  simpa only [compl_ofPred, not_lt] using (isSemialgebraic_eval_pos p).compl

/-- The set where a polynomial is negative is semialgebraic. -/
theorem isSemialgebraic_eval_neg (p : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | eval x p < 0} := by
  convert ((isSemialgebraic_eval_eq_zero p).union (isSemialgebraic_eval_pos p)).compl using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, not_or, not_lt]
  rw [lt_iff_le_and_ne]
  exact and_comm

/-- The set where a polynomial is nonnegative is semialgebraic. -/
theorem isSemialgebraic_eval_nonneg (p : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | 0 ≤ eval x p} := by
  simpa only [compl_ofPred, not_lt] using (isSemialgebraic_eval_neg p).compl

/-- The set where one polynomial is less than another is semialgebraic. -/
theorem isSemialgebraic_eval_lt [IsOrderedAddMonoid R] (p q : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | eval x p < eval x q} := by
  simpa using isSemialgebraic_eval_pos (q - p)

/-- The set where one polynomial is at most another is semialgebraic. -/
theorem isSemialgebraic_eval_le [IsOrderedAddMonoid R] (p q : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R | eval x p ≤ eval x q} := by
  simpa only [compl_ofPred, not_lt] using (isSemialgebraic_eval_lt q p).compl

/-- The set where a polynomial has a prescribed sign is semialgebraic. -/
theorem isSemialgebraic_sign_eval_eq (p : MvPolynomial σ R) (ε : SignType) :
    IsSemialgebraic {x : σ → R | SignType.sign (eval x p) = ε} := by
  rcases ε with _ | _ | _
  · simpa only [SignType.zero_eq_zero, sign_eq_zero_iff] using isSemialgebraic_eval_eq_zero p
  · simpa only [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] using isSemialgebraic_eval_neg p
  · simpa only [SignType.pos_eq_one, sign_eq_one_iff] using isSemialgebraic_eval_pos p

/-- A sign condition on finitely many polynomials defines a semialgebraic set: membership may
depend in any way on the signs of their values. -/
theorem isSemialgebraic_setOf_sign_eval {ι : Type*} [Finite ι] (p : ι → MvPolynomial σ R)
    (Φ : (ι → SignType) → Prop) :
    IsSemialgebraic {x : σ → R | Φ fun i => SignType.sign (eval x (p i))} := by
  rw [setOf_apply_eq_biUnion_iInter (fun i x => SignType.sign (eval x (p i)))]
  exact .biUnion (toFinite _) fun ε _ => .iInter fun i => isSemialgebraic_sign_eval_eq _ _

/-- A condition on the permanences minus variations of the values of finitely many polynomials
defines a semialgebraic set, since the statistic depends only on the signs of the values. -/
theorem isSemialgebraic_setOf_permanencesMinusVariations_eval
    (l : List (MvPolynomial σ R)) (c : ℤ) :
    IsSemialgebraic {x : σ → R | (l.map (eval x)).permanencesMinusVariations = c} := by
  have h (x : σ → R) : (l.map (eval x)).permanencesMinusVariations =
      (List.ofFn fun i : Fin l.length =>
        SignType.sign (eval x l[i])).permanencesMinusVariations := by
    rw [← List.permanencesMinusVariations_map_sign, List.map_map]
    exact congrArg List.permanencesMinusVariations (List.ofFn_getElem_eq_map l _).symm
  simpa only [h] using isSemialgebraic_setOf_sign_eval (fun i : Fin l.length => l[i])
    fun ε => (List.ofFn ε).permanencesMinusVariations = c

/-- The parameters at which the coefficients of `P` of index in `s` all vanish form a
semialgebraic set. -/
theorem isSemialgebraic_setOf_forall_coeff_eq_zero (P : Polynomial (MvPolynomial σ R))
    (s : Set ℕ) :
    IsSemialgebraic {x : σ → R | ∀ n ∈ s, eval x (P.coeff n) = 0} := by
  have : {x : σ → R | ∀ n ∈ s, eval x (P.coeff n) = 0} =
      ⋂ n ∈ s ∩ P.support, {x | eval x (P.coeff n) = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff, Finset.mem_coe]
    refine ⟨fun h n hn => h n hn.1, fun h n hn => ?_⟩
    by_cases hP : n ∈ P.support
    · exact h n ⟨hn, hP⟩
    · rw [Polynomial.notMem_support_iff.mp hP, map_zero]
  rw [this]
  exact .biInter (P.support.finite_toSet.inter_of_right s) fun n _ =>
    isSemialgebraic_eval_eq_zero _

/-! ### Finite sets -/

/-- In finitely many coordinates, a point is semialgebraic. -/
theorem isSemialgebraic_singleton [Finite σ] (a : σ → R) :
    IsSemialgebraic ({a} : Set (σ → R)) := by
  have : ({a} : Set (σ → R)) = ⋂ i, {x | eval x (X i - C (a i)) = 0} := by
    ext x
    simp [funext_iff, sub_eq_zero]
  rw [this]
  exact .iInter fun i => isSemialgebraic_eval_eq_zero _

/-- In finitely many coordinates, a finite set is semialgebraic. -/
theorem _root_.Set.Finite.isSemialgebraic [Finite σ] {s : Set (σ → R)} (hs : s.Finite) :
    IsSemialgebraic s := by
  simpa using IsSemialgebraic.biUnion hs fun a _ => isSemialgebraic_singleton a

/-! ### Inverse images and products -/

/-- The inverse image of a semialgebraic set under a polynomial map is semialgebraic. -/
theorem IsSemialgebraic.preimage_eval {s : Set (τ → R)} (hs : IsSemialgebraic s)
    (f : τ → MvPolynomial σ R) :
    IsSemialgebraic ((fun x i => eval x (f i)) ⁻¹' s) := by
  have hbind (x : σ → R) (p : MvPolynomial τ R) :
      eval (fun i => eval x (f i)) p = eval x (bind₁ f p) := by
    simp only [← coe_aeval_eq_eval]
    exact (aeval_bind₁ x f p).symm
  refine setOf_isSemialgebraic_subset (ℬ := {t | IsSemialgebraic ((fun x i => eval x (f i)) ⁻¹' t)})
    ⟨by simp, fun t ht => ?_, fun t u ht hu => ?_⟩ (fun p => ?_) (fun p => ?_) hs
  · simpa using ht.compl
  · simpa using ht.union hu
  · simpa [hbind] using isSemialgebraic_eval_eq_zero (bind₁ f p)
  · simpa [hbind] using isSemialgebraic_eval_pos (bind₁ f p)

/-- The inverse image of a semialgebraic set under a change of coordinates `x ↦ x ∘ f` is
semialgebraic. -/
theorem IsSemialgebraic.preimage_comp {s : Set (τ → R)} (hs : IsSemialgebraic s) (f : τ → σ) :
    IsSemialgebraic ((fun x : σ → R => x ∘ f) ⁻¹' s) := by
  simpa [Function.comp_def] using hs.preimage_eval fun i => X (f i)

/-- Semialgebraicity is invariant under a bijective change of coordinates, such as a coordinate
permutation. -/
@[simp]
theorem isSemialgebraic_preimage_comp_equiv {s : Set (τ → R)} (e : τ ≃ σ) :
    IsSemialgebraic ((fun x : σ → R => x ∘ e) ⁻¹' s) ↔ IsSemialgebraic s := by
  refine ⟨fun hs => ?_, fun hs => hs.preimage_comp e⟩
  convert hs.preimage_comp e.symm
  ext x
  simp [Function.comp_def]

/-- The product of semialgebraic sets, as a subset of `σ ⊕ τ → R`, is semialgebraic. -/
theorem IsSemialgebraic.preimage_sumArrowEquivProdArrow_prod {s : Set (σ → R)}
    {t : Set (τ → R)} (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) :
    IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s ×ˢ t) :=
  (hs.preimage_comp Sum.inl).inter (ht.preimage_comp Sum.inr)

/-- The product of semialgebraic sets, as a subset of `Fin (m + n) → R`, is semialgebraic. -/
theorem IsSemialgebraic.image_appendEquiv_prod {m n : ℕ} {s : Set (Fin m → R)}
    {t : Set (Fin n → R)} (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) :
    IsSemialgebraic (Fin.appendEquiv m n '' s ×ˢ t) := by
  rw [Equiv.image_eq_preimage_symm]
  exact (hs.preimage_comp (Fin.castAdd n)).inter (ht.preimage_comp (Fin.natAdd m))

/-- The cylinder `Fin.tail ⁻¹' s` over a semialgebraic subset `s` of `Fin n → R`, with
distinguished coordinate `0`, is semialgebraic. -/
theorem IsSemialgebraic.preimage_tail {n : ℕ} {s : Set (Fin n → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (Fin.tail ⁻¹' s : Set (Fin (n + 1) → R)) :=
  hs.preimage_comp Fin.succ

/-- The horizontal section at height `t` of a semialgebraic subset of `Fin (n + 1) → R`, whose
distinguished coordinate is `0`, is semialgebraic. -/
theorem IsSemialgebraic.preimage_cons_left {n : ℕ} {s : Set (Fin (n + 1) → R)}
    (hs : IsSemialgebraic s) (t : R) :
    IsSemialgebraic {x : Fin n → R | Fin.cons t x ∈ s} := by
  have hf : (fun x i => eval x ((Fin.cons (C t) X : Fin (n + 1) → MvPolynomial (Fin n) R) i)) =
      fun x : Fin n → R => (Fin.cons t x : Fin (n + 1) → R) := by
    funext x i
    cases i using Fin.cases <;> simp
  have h := hs.preimage_eval (Fin.cons (C t) X : Fin (n + 1) → MvPolynomial (Fin n) R)
  rw [hf] at h
  exact h

/-- The vertical section over a base point `x` of a semialgebraic subset of `Fin (n + 1) → R`,
whose distinguished coordinate is `0`, is semialgebraic as a subset of `Fin 1 → R`. -/
theorem IsSemialgebraic.preimage_cons_right {n : ℕ} {s : Set (Fin (n + 1) → R)}
    (hs : IsSemialgebraic s) (x : Fin n → R) :
    IsSemialgebraic {y : Fin 1 → R | Fin.cons (y 0) x ∈ s} := by
  have hf : (fun y i => eval y
      ((Fin.cons (X 0) fun j => C (x j) : Fin (n + 1) → MvPolynomial (Fin 1) R) i)) =
      fun y : Fin 1 → R => (Fin.cons (y 0) x : Fin (n + 1) → R) := by
    funext y i
    cases i using Fin.cases <;> simp
  have h := hs.preimage_eval
    (Fin.cons (X 0) fun j => C (x j) : Fin (n + 1) → MvPolynomial (Fin 1) R)
  rw [hf] at h
  exact h

/-! ### Sign-condition normal form -/

/-- **Sign-condition normal form.** Every semialgebraic set is described by a condition on the
signs of finitely many polynomials. -/
theorem IsSemialgebraic.exists_eq_setOf_sign_eval {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    ∃ (m : ℕ) (p : Fin m → MvPolynomial σ R) (Φ : (Fin m → SignType) → Prop),
      s = {x | Φ fun i => SignType.sign (eval x (p i))} := by
  obtain ⟨m, f, hf, Φ, rfl⟩ := exists_eq_setOf_sign_of_mem_generateSetAlgebra
    (P := fun f : (σ → R) → R => ∃ p, f = fun x => eval x p) <| generateSetAlgebra_mono
      (union_subset_union (by rintro _ ⟨p, rfl⟩; exact ⟨_, ⟨p, rfl⟩, rfl⟩)
        (by rintro _ ⟨p, rfl⟩; exact ⟨_, ⟨p, rfl⟩, rfl⟩)) hs
  choose p hp using hf
  exact ⟨m, p, Φ, by simp only [hp]⟩

/-- **Finitely many coordinates.** Membership in a semialgebraic set depends on only finitely
many coordinates: those of the variables of the polynomials describing it. -/
theorem IsSemialgebraic.exists_finset_mem_iff_of_eqOn {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    ∃ F : Finset σ, ∀ x y : σ → R, EqOn x y F → (x ∈ s ↔ y ∈ s) := by
  classical
  obtain ⟨m, p, Φ, rfl⟩ := hs.exists_eq_setOf_sign_eval
  refine ⟨Finset.univ.biUnion fun i => (p i).vars, fun x y hxy => ?_⟩
  have h (i : Fin m) : eval x (p i) = eval y (p i) :=
    eval₂Hom_congr' rfl (fun j hj _ => hxy (by simpa using ⟨i, hj⟩)) rfl
  simp [h]

/-! ### Projection closure -/

variable (R) in
/-- Semialgebraic subsets of the coordinate spaces over `R` *have semialgebraic projections* if,
for every `n`, forgetting the coordinate `0` (`Fin.tail`) maps semialgebraic subsets of
`Fin (n + 1) → R` to semialgebraic subsets of `Fin n → R`. For `R = ℝ` this is the
Tarski–Seidenberg theorem, proved by cylindrical algebraic decomposition in
`TauCeti.Geometry.RealAlgebraic.CAD.Existence`. It fails for some ordered fields: over `ℚ`,
forgetting `t` maps the parabola `{(t, x) | t ^ 2 = x}` to the set of rational squares, which is
dense and codense in the positive rationals and so is not semialgebraic. -/
class HasSemialgebraicProjections : Prop where
  /-- Forgetting the coordinate `0` maps semialgebraic sets to semialgebraic sets. -/
  isSemialgebraic_image_tail {n : ℕ} {s : Set (Fin (n + 1) → R)} :
    IsSemialgebraic s → IsSemialgebraic (Fin.tail '' s)

end TauCeti
end -- closes the original EOF section from source line 64
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Basic.lean -/

/- BEGIN SOURCE: VolumePolynomials/LiftedSliceCoordinates.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The literal affine coefficient slice in every dimension at least three.
Its coordinate formulas prove both continuity and polynomial preimage
compatibility. Its fibers refer to the original realization locus. -/

open Set MeasureTheory MvPolynomial
open scoped BigOperators

namespace VolumePolynomials.HigherLift

@[simp] theorem coefficients_zero (α s z : ℝ) :
    coefficients 0 α s z = CubicSlice.coefficients α s z := by
  first
  | have hc : correction 0 = 1 := by norm_num [correction]
    simp only [coefficients, polynomial, pow_zero, one_mul, hc, CubicSlice.coefficients]

theorem mem_volumeLocus_of_cubic_all (k : ℕ) {α s z : ℝ}
    (h : CubicSlice.coefficients α s z ∈ VolumeLocus 3 3) :
    coefficients k α s z ∈ VolumeLocus 3 (3 + k) := by
  first
  | rcases k with _ | k
    · simpa only [coefficients_zero] using h
    · exact mem_volumeLocus_of_cubic h (Nat.succ_pos k)

def sliceTerm (k : ℕ) : Fin 7 → MvPolynomial (Fin 2) ℝ :=
  ![C (6 * correction k) * X 0, C (6 * correction k) * X 0,
    C 3, C 3, C 3 * X 0, C 3, C 6 * X 1]

theorem eval_sliceTerm (k : ℕ) (p : Fin 2 → ℝ) (j : Fin 7) :
    MvPolynomial.eval p (sliceTerm k j) = termCoefficient k (2 * p 0) (p 0) (p 1) j := by
  first
  | fin_cases j <;> simp only [sliceTerm, termCoefficient, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ',
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] <;> ring

def sliceCoordinate (k : ℕ) (β : MultiIndex 3 (3 + k)) : MvPolynomial (Fin 2) ℝ :=
  ∑ j : Fin 7, if termExponent k j = exponent β then sliceTerm k j else 0

theorem eval_sliceCoordinate (k : ℕ) (p : Fin 2 → ℝ) (β : MultiIndex 3 (3 + k)) :
    MvPolynomial.eval p (sliceCoordinate k β) = coefficients k (2 * p 0) (p 0) (p 1) β := by
  first
  | classical
    rw [sliceCoordinate, MvPolynomial.eval_sum, coefficients_eq_terms]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact eval_sliceTerm k p j
    · exact map_zero _

def coefficientSlice (k : ℕ) : Set (Fin 2 → ℝ) :=
  {p | coefficients k (2 * p 0) (p 0) (p 1) ∈ VolumeLocus 3 (3 + k)}

theorem coefficientSlice_eq_preimage (k : ℕ) :
    coefficientSlice k = (fun p β => MvPolynomial.eval p (sliceCoordinate k β)) ⁻¹'
      VolumeLocus 3 (3 + k) := by
  first
  | ext p
    simp only [Set.mem_preimage, coefficientSlice, Set.mem_setOf_eq,
      eval_sliceCoordinate]

theorem continuous_slice_map (k : ℕ) :
    Continuous (fun p : Fin 2 → ℝ => coefficients k (2 * p 0) (p 0) (p 1)) := by
  first
  | apply continuous_pi
    intro β
    have heq : (fun p : Fin 2 → ℝ => coefficients k (2 * p 0) (p 0) (p 1) β) =
        fun p => MvPolynomial.eval p (sliceCoordinate k β) := by
      first
      | funext p
        exact (eval_sliceCoordinate k p β).symm
    rw [heq]
    exact (sliceCoordinate k β).continuous_eval

theorem isClosed_coefficientSlice (k : ℕ) : IsClosed (coefficientSlice k) :=
  (isClosed_volumeLocus 3 (3 + k) (by omega)).preimage (continuous_slice_map k)

theorem isSemialgebraic_coefficientSlice (k : ℕ)
    (h : TauCeti.IsSemialgebraic (VolumeLocus 3 (3 + k))) :
    TauCeti.IsSemialgebraic (coefficientSlice k) := by
  first
  | rw [coefficientSlice_eq_preimage]
    exact h.preimage_eval (sliceCoordinate k)

def fiberValues (k : ℕ) (s : ℝ) : Set ℝ :=
  {z | coefficients k (2 * s) s z ∈ VolumeLocus 3 (3 + k)}

def boundaryValue (k : ℕ) (s : ℝ) : ℝ := sInf (fiberValues k s)

theorem fiberValues_closed (k : ℕ) (s : ℝ) : IsClosed (fiberValues k s) := by
  first
  | have hc : Continuous (fun z : ℝ => (![s, z] : Fin 2 → ℝ)) := by fun_prop
    exact (isClosed_coefficientSlice k).preimage hc

theorem fiberValues_nonnegative {k : ℕ} {s z : ℝ} (hz : z ∈ fiberValues k s) : 0 ≤ z := by
  first
  | obtain ⟨K, hK⟩ := hz
    exact triple_parameter_nonnegative hK

theorem fiberValues_bddBelow (k : ℕ) (s : ℝ) : BddBelow (fiberValues k s) :=
  ⟨0, fun _ hz => fiberValues_nonnegative hz⟩

theorem boundaryValue_attained_of_nonempty (k : ℕ) (s : ℝ)
    (hne : (fiberValues k s).Nonempty) :
    boundaryValue k s ∈ fiberValues k s ∧
      ∀ z ∈ fiberValues k s, boundaryValue k s ≤ z := by
  first
  | exact ⟨(fiberValues_closed k s).csInf_mem hne (fiberValues_bddBelow k s),
      fun _ hz => csInf_le (fiberValues_bddBelow k s) hz⟩

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/LiftedSliceCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/GeneralInteractionGap.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The upper logarithmic interaction deficit for arbitrary convex bodies

Separate polygon deficits are retained throughout approximation. They converge
to the prescribed common deficit, so no exact-area approximation theorem is
silently assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092 PolytopeGeometry

theorem polygon_interaction_with_deficits (B C : ConvexBody Plane)
    (hB : IsFiniteHull (B : Set Plane)) (hC : IsFiniteHull (C : Set Plane))
    (hBa : 0 < volume.real (B : Set Plane)) (hCa : 0 < volume.real (C : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      ∀ δB δC : ℝ, 0 < δB → 0 < δC →
        2 * δB ≤ min (1 / 64) (Real.exp (-1)) →
        2 * δC ≤ min (1 / 64) (Real.exp (-1)) →
        volume.real (B : Set Plane) = 1 / 2 - δB →
        volume.real (C : Set Plane) = 1 / 2 - δC →
        1 / 2 - volume.real (Q : Set Plane) ≤
          2176 * (δB ^ 2 * Real.log (1 / δB) + δC ^ 2 * Real.log (1 / δC)) := by
  first
  | obtain ⟨m, b, hb⟩ := exists_representation B hB hBa
    obtain ⟨n, c, hc⟩ := exists_representation C hC hCa
    obtain ⟨Q, hQw, hQh, hQV, _, hQrep⟩ := finite_interaction_body hb hc hBw hBh hCw hCh
    refine ⟨Q, ⟨hQw, hQh, hQV⟩, ?_⟩
    intro δB δC hδB hδC hsmallB hsmallC hareaB hareaC
    exact productEdge_body_logarithmic_deficits hb hc hBw hBh hCw hCh hQrep hQw hQh
      hδB hδC hsmallB hsmallC hareaB hareaC

theorem tendsto_deficit_log_square {δ : ℝ} (hδ : 0 < δ) {d : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 δ)) :
    Tendsto (fun n => d n ^ 2 * Real.log (1 / d n)) atTop
      (𝓝 (δ ^ 2 * Real.log (1 / δ))) := by
  first
  | have hinv := (tendsto_const_nhds (x := (1 : ℝ))).div hd hδ.ne'
    have hlog := (Real.continuousAt_log (by positivity : (1 : ℝ) / δ ≠ 0)).tendsto.comp hinv
    exact (hd.pow 2).mul hlog

/-- Corollary 5.3 with an explicit absolute constant. It holds for every
interaction body satisfying the already proved geometric identity, since
that identity determines its area uniquely. -/
theorem corollary_5_3 {B C Q : ConvexBody Plane}
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1)
    (hQ : IsInteraction B C Q) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : 2 * δ < min (1 / 64) (Real.exp (-1)))
    (hBa : volume.real (B : Set Plane) = 1 / 2 - δ)
    (hCa : volume.real (C : Set Plane) = 1 / 2 - δ) :
    1 / 2 - volume.real (Q : Set Plane) ≤ 4352 * δ ^ 2 * Real.log (1 / δ) := by
  first
  | have hδhalf : δ < 1 / 2 := by
      first
      | have hs := hsmall.trans_le (min_le_left (1 / 64 : ℝ) (Real.exp (-1)))
        linarith
    have hBpos : 0 < volume.real (B : Set Plane) := by rw [hBa]; linarith
    have hCpos : 0 < volume.real (C : Set Plane) := by rw [hCa]; linarith
    obtain ⟨Bn, hBn, hBlim⟩ := exists_unit_polygon_sequence B hBpos hBw hBh
    obtain ⟨Cn, hCn, hClim⟩ := exists_unit_polygon_sequence C hCpos hCw hCh
    have hp (n : ℕ) := polygon_interaction_with_deficits (Bn n) (Cn n)
      (hBn n).1 (hCn n).1 (hBn n).2.2.2.2 (hCn n).2.2.2.2
      (hBn n).2.2.1 (hBn n).2.2.2.1 (hCn n).2.2.1 (hCn n).2.2.2.1
    choose R hRI hRbound using hp
    choose p hpR using fun n => (R n).nonempty
    let S : ℕ → ConvexBody Plane := fun n => translateBody (-(p n)) (R n)
    have hSI (n : ℕ) : IsInteraction (Bn n) (Cn n) (S n) := (hRI n).translate _
    have hSc (n : ℕ) : S n ∈ centeredUnitBodies :=
      ⟨zero_mem_translateBody_neg (hpR n), (hSI n).1, (hSI n).2.1⟩
    have hSa (n : ℕ) : volume.real (S n : Set Plane) = volume.real (R n : Set Plane) :=
      area_translate _ _
    obtain ⟨L, hLc, φ, hφ, hLlim⟩ := isCompact_centeredUnitBodies.tendsto_subseq hSc
    have hB' := hBlim.comp hφ.tendsto_atTop
    have hC' := hClim.comp hφ.tendsto_atTop
    have hLI : IsInteraction B C L := by
      first
      | refine ⟨hLc.2.1, hLc.2.2, ?_⟩
        intro A
        have hleft := (tendsto_const_nhds (x := (6 : ℝ))).mul
          ((continuous_triple A).continuousAt.tendsto.comp (hB'.prodMk_nhds hC'))
        have hright := (tendsto_const_nhds (x := (2 : ℝ))).mul
          ((continuous_mixedArea_right A).continuousAt.tendsto.comp hLlim)
        exact (isClosed_eq continuous_fst continuous_snd).mem_of_tendsto
          (hleft.prodMk_nhds hright) (Filter.Eventually.of_forall (fun n => (hSI (φ n)).2.2 A))
    have harea := interaction_area_unique hQ hLI
    rw [harea]
    let dB : ℕ → ℝ := fun n => 1 / 2 - volume.real (Bn (φ n) : Set Plane)
    let dC : ℕ → ℝ := fun n => 1 / 2 - volume.real (Cn (φ n) : Set Plane)
    have hdB : Tendsto dB atTop (𝓝 δ) := by
      first
      | have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
          ((continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hB')
        simpa only [Function.comp_apply, hBa, sub_sub_cancel, dB] using h
    have hdC : Tendsto dC atTop (𝓝 δ) := by
      first
      | have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
          ((continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hC')
        simpa only [Function.comp_apply, hCa, sub_sub_cancel, dC] using h
    have heB := hdB.eventually (Ioi_mem_nhds hδ)
    have heC := hdC.eventually (Ioi_mem_nhds hδ)
    have hsB := ((tendsto_const_nhds (x := (2 : ℝ))).mul hdB).eventually (Iio_mem_nhds hsmall)
    have hsC := ((tendsto_const_nhds (x := (2 : ℝ))).mul hdC).eventually (Iio_mem_nhds hsmall)
    have hbound : ∀ᶠ n in atTop,
        1 / 2 - volume.real (S (φ n) : Set Plane) ≤
          2176 * (dB n ^ 2 * Real.log (1 / dB n) + dC n ^ 2 * Real.log (1 / dC n)) := by
      first
      | filter_upwards [heB, heC, hsB, hsC] with n hb hc hsb hsc
        rw [hSa]
        exact hRbound (φ n) (dB n) (dC n) hb hc hsb.le hsc.le (by dsimp [dB]; ring)
          (by dsimp [dC]; ring)
    have hleft := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
      ((continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hLlim)
    have hright := (tendsto_const_nhds (x := (2176 : ℝ))).mul
      ((tendsto_deficit_log_square hδ hdB).add (tendsto_deficit_log_square hδ hdC))
    have h := le_of_tendsto_of_tendsto hleft hright hbound
    nlinarith

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 15
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/GeneralInteractionGap.lean -/

/- BEGIN SOURCE: VolumePolynomials/HalfZonotopeCaps.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Literal convex caps obtained by halving planar zonotopes

These are actual compact convex sets with Lebesgue area, not formal edge lists.
The cut through the center divides the area equally because negation exchanges
the two halves and their common line has measure zero. Nonnegative horizontal
and nonpositive vertical generators with sum `(1,-1)` give exact unit widths.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def diagonalMap : Plane →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ

@[simp] theorem diagonalMap_apply (p : Plane) : diagonalMap p = p.1 + p.2 := rfl

theorem volume_diagonal_zero : volume {p : Plane | p.1 + p.2 = 0} = 0 := by
  first
  | change volume (LinearMap.ker diagonalMap : Set Plane) = 0
    apply Measure.addHaar_submodule volume
    intro h
    have hmem : ((1, 0) : Plane) ∈ LinearMap.ker diagonalMap := by
      first
      | rw [h]
        trivial
    norm_num [LinearMap.mem_ker, diagonalMap] at hmem

theorem neg_mem_zonotope {vs : List Plane} {x : Plane} (hx : x ∈ zonotope vs) :
    -x ∈ zonotope vs := by
  first
  | induction vs generalizing x with
    | nil => simpa [zonotope] using hx
    | cons v vs ih =>
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        obtain ⟨t, ht, rfl⟩ := hz
        refine ⟨-y, ih hy, (-t) • v, ?_, ?_⟩
        · exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
        · simp [add_comm]

theorem neg_mem_zonotope_iff (vs : List Plane) (x : Plane) :
    -x ∈ zonotope vs ↔ x ∈ zonotope vs := by
  first
  | constructor
    · intro h
      simpa using neg_mem_zonotope h
    · exact neg_mem_zonotope

def lowerHalf (vs : List Plane) : Set Plane :=
  zonotope vs ∩ {p | p.1 + p.2 ≤ 0}

def upperHalf (vs : List Plane) : Set Plane :=
  zonotope vs ∩ {p | 0 ≤ p.1 + p.2}

theorem lowerHalf_compact (vs : List Plane) : IsCompact (lowerHalf vs) :=
  (zonotope_compact vs).inter_right
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const)

theorem upperHalf_compact (vs : List Plane) : IsCompact (upperHalf vs) :=
  (zonotope_compact vs).inter_right
    (isClosed_le continuous_const (continuous_fst.add continuous_snd))

theorem lowerHalf_convex (vs : List Plane) : Convex ℝ (lowerHalf vs) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨zonotope_convex vs hx.1 hy.1 ha hb hab, ?_⟩
    change (a • x + b • y).1 + (a • x + b • y).2 ≤ 0
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hax := mul_nonpos_of_nonneg_of_nonpos ha hx.2
    have hby := mul_nonpos_of_nonneg_of_nonpos hb hy.2
    nlinarith

theorem upperHalf_eq_neg_preimage (vs : List Plane) :
    upperHalf vs = Neg.neg ⁻¹' lowerHalf vs := by
  first
  | ext x
    simp only [upperHalf, lowerHalf, mem_inter_iff, mem_setOf_eq, mem_preimage,
      neg_mem_zonotope_iff, Prod.fst_neg, Prod.snd_neg]
    constructor <;> rintro ⟨hx, h⟩ <;> exact ⟨hx, by linarith⟩

theorem lowerHalf_union_upperHalf (vs : List Plane) :
    lowerHalf vs ∪ upperHalf vs = zonotope vs := by
  first
  | ext x
    simp only [lowerHalf, upperHalf, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      rcases le_total (x.1 + x.2) 0 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩

theorem volume_lowerHalf_inter_upperHalf (vs : List Plane) :
    volume (lowerHalf vs ∩ upperHalf vs) = 0 := by
  first
  | apply measure_mono_null _ volume_diagonal_zero
    intro x hx
    exact le_antisymm hx.1.2 hx.2.2

/-- Halving is a literal Lebesgue-area identity, including degenerate zonotopes. -/
theorem area_lowerHalf (vs : List Plane) :
    volume.real (lowerHalf vs) = pairArea vs / 2 := by
  first
  | have hneg : volume.real (upperHalf vs) = volume.real (lowerHalf vs) := by
      first
      | rw [upperHalf_eq_neg_preimage]
        exact congrArg ENNReal.toReal (Measure.measure_preimage_neg volume (lowerHalf vs))
    have hsplit := measureReal_union_add_inter
      (μ := (volume : Measure Plane)) (s := lowerHalf vs) (t := upperHalf vs)
      (upperHalf_compact vs).measurableSet
      (lowerHalf_compact vs).measure_lt_top.ne (upperHalf_compact vs).measure_lt_top.ne
    rw [lowerHalf_union_upperHalf, area_zonotope, hneg] at hsplit
    have hzero : volume.real (lowerHalf vs ∩ upperHalf vs) = 0 := by
      first
      | simp only [measureReal_def, volume_lowerHalf_inter_upperHalf, ENNReal.toReal_zero]
    rw [hzero] at hsplit
    linarith

/-- Translation places the diagonal endpoints at `(0,1)` and `(1,0)` when the
generators sum to `(1,-1)`. -/
def cap (vs : List Plane) : Set Plane :=
  {((1 / 2, 1 / 2) : Plane)} + lowerHalf vs

theorem cap_compact (vs : List Plane) : IsCompact (cap vs) :=
  isCompact_singleton.add (lowerHalf_compact vs)

theorem cap_convex (vs : List Plane) : Convex ℝ (cap vs) :=
  (convex_singleton _).add (lowerHalf_convex vs)

theorem area_cap (vs : List Plane) : volume.real (cap vs) = pairArea vs / 2 := by
  first
  | unfold cap
    rw [Set.singleton_add]
    simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
    exact area_lowerHalf vs

theorem constant_parameter_mem_zonotope (vs : List Plane) (t : ℝ)
    (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : t • vs.sum ∈ zonotope vs := by
  first
  | induction vs with
    | nil => simp [zonotope]
    | cons v vs ih =>
        refine ⟨t • vs.sum, ih, t • v, ⟨t, ht, rfl⟩, ?_⟩
        simp only [List.sum_cons, smul_add]
        exact add_comm _ _

theorem diagonal_endpoints_mem_cap {vs : List Plane} (hsum : vs.sum = (1, -1)) :
    ((0, 1) : Plane) ∈ cap vs ∧ ((1, 0) : Plane) ∈ cap vs := by
  first
  | constructor
    · refine ⟨(1 / 2, 1 / 2), rfl, (-1 / 2 : ℝ) • vs.sum, ?_, ?_⟩
      · refine ⟨constant_parameter_mem_zonotope vs _ ⟨by norm_num, by norm_num⟩, ?_⟩
        norm_num [hsum]
      · norm_num [hsum]
    · refine ⟨(1 / 2, 1 / 2), rfl, (1 / 2 : ℝ) • vs.sum, ?_, ?_⟩
      · refine ⟨constant_parameter_mem_zonotope vs _ ⟨by norm_num, by norm_num⟩, ?_⟩
        norm_num [hsum]
      · norm_num [hsum]

theorem zonotope_coordinate_bounds {vs : List Plane} {x : Plane} (hx : x ∈ zonotope vs) :
    |x.1| ≤ (vs.map (fun v => |v.1|)).sum / 2 ∧
      |x.2| ≤ (vs.map (fun v => |v.2|)).sum / 2 := by
  first
  | induction vs generalizing x with
    | nil =>
        have hx0 : x = 0 := hx
        subst x
        simp
    | cons v vs ih =>
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        obtain ⟨t, ht, rfl⟩ := hz
        have hi := ih hy
        have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
        have hfst := mul_le_mul_of_nonneg_right ht' (abs_nonneg v.1)
        have hsnd := mul_le_mul_of_nonneg_right ht' (abs_nonneg v.2)
        simp only [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        constructor
        · have htri := abs_add_le y.1 (t * v.1)
          rw [abs_mul] at htri
          linarith [hi.1]
        · have htri := abs_add_le y.2 (t * v.2)
          rw [abs_mul] at htri
          linarith [hi.2]

theorem sum_abs_coordinates {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    (vs.map (fun v => |v.1|)).sum = vs.sum.1 ∧
      (vs.map (fun v => |v.2|)).sum = -vs.sum.2 := by
  first
  | induction vs with
    | nil => simp
    | cons v vs ih =>
        have hv := hvs v (List.mem_cons_self)
        have hi := ih (fun w hw => hvs w (List.mem_cons_of_mem v hw))
        simp only [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add,
          abs_of_nonneg hv.1, abs_of_nonpos hv.2, hi.1, hi.2]
        constructor
        · trivial
        · ring

theorem cap_subset_unitSquare {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    cap vs ⊆ Icc ((0, 0) : Plane) (1, 1) := by
  first
  | intro x hx
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    change c = (1 / 2, 1 / 2) at hc
    subst c
    have hb := zonotope_coordinate_bounds hy.1
    have ha := sum_abs_coordinates hvs
    rw [ha.1, ha.2, hsum] at hb
    have hx := abs_le.mp hb.1
    have hy' := abs_le.mp hb.2
    constructor <;> constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;>
      norm_num at * <;> linarith

/-- Both coordinate projections are the entire unit interval, not merely subsets. -/
theorem cap_coordinate_projections {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    Prod.fst '' cap vs = Icc (0 : ℝ) 1 ∧ Prod.snd '' cap vs = Icc (0 : ℝ) 1 := by
  first
  | have hb := cap_subset_unitSquare hvs hsum
    obtain ⟨h01, h10⟩ := diagonal_endpoints_mem_cap hsum
    have hdiag (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, 1 - t) ∈ cap vs := by
      first
      | have h := cap_convex vs h01 h10 (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
        convert h using 1 <;> ext <;> simp <;> ring
    constructor
    · apply Subset.antisymm
      · rintro t ⟨x, hx, rfl⟩
        exact ⟨(hb hx).1.1, (hb hx).2.1⟩
      · intro t ht
        exact ⟨(t, 1 - t), hdiag t ht, rfl⟩
    · apply Subset.antisymm
      · rintro t ⟨x, hx, rfl⟩
        exact ⟨(hb hx).1.2, (hb hx).2.2⟩
      · intro t ht
        refine ⟨(1 - t, t), ?_, rfl⟩
        convert hdiag (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ using 1 <;>
          ext <;> simp <;> ring

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HalfZonotopeCaps.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteCornerCaps.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The exact corner deficit of a finite half-zonotope cap -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def cornerInteraction (v w : Plane) : ℝ :=
  min (v.1 * (-w.2)) (w.1 * (-v.2))

def cornerEnergy : List Plane → ℝ
  | [] => 0
  | v :: vs => cornerEnergy vs + v.1 * (-v.2) +
      2 * (vs.map (cornerInteraction v)).sum

theorem abs_sub_add_two_min (a b : ℝ) : |a - b| + 2 * min a b = a + b := by
  first
  | rcases le_total a b with hab | hba
    · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
      ring

theorem pair_corner_identity (v w : Plane) :
    |determinant v w| + 2 * cornerInteraction v w =
      v.1 * (-w.2) + w.1 * (-v.2) := by
  first
  | have h := abs_sub_add_two_min (v.1 * (-w.2)) (w.1 * (-v.2))
    have he : v.1 * (-w.2) - w.1 * (-v.2) = -determinant v w := by
      first
      | simp only [determinant]
        ring
    rw [he, abs_neg] at h
    exact h

theorem sum_pair_corner_identity (v : Plane) (vs : List Plane) :
    (vs.map (fun w => |determinant v w|)).sum +
        2 * (vs.map (cornerInteraction v)).sum =
      v.1 * (-vs.sum.2) + vs.sum.1 * (-v.2) := by
  first
  | induction vs with
    | nil => simp
    | cons w vs ih =>
        have hp := pair_corner_identity v w
        simp only [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add]
        nlinarith

/-- The full rectangle product is the sum of the zonotope area and the
double corner energy. This is an exact finite algebraic identity. -/
theorem pairArea_add_cornerEnergy (vs : List Plane) :
    pairArea vs + cornerEnergy vs = vs.sum.1 * (-vs.sum.2) := by
  first
  | induction vs with
    | nil => simp [pairArea, cornerEnergy]
    | cons v vs ih =>
        have hc := sum_pair_corner_identity v vs
        simp only [pairArea, cornerEnergy, List.sum_cons, Prod.fst_add, Prod.snd_add]
        nlinarith

/-- The area identity is proved for the actual cap defined by a halfspace cut. -/
theorem area_cap_eq_rectangle_sub_cornerEnergy (vs : List Plane) :
    volume.real (cap vs) = (vs.sum.1 * (-vs.sum.2) - cornerEnergy vs) / 2 := by
  first
  | rw [area_cap]
    linarith [pairArea_add_cornerEnergy vs]

theorem area_unit_cap {vs : List Plane} (hsum : vs.sum = (1, -1)) :
    volume.real (cap vs) = 1 / 2 - cornerEnergy vs / 2 := by
  first
  | rw [area_cap_eq_rectangle_sub_cornerEnergy, hsum]
    norm_num
    ring

theorem cornerInteraction_nonneg {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    0 ≤ cornerInteraction v w :=
  le_min (mul_nonneg hv.1 (neg_nonneg.mpr hw.2))
    (mul_nonneg hw.1 (neg_nonneg.mpr hv.2))

theorem cornerEnergy_nonneg {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) : 0 ≤ cornerEnergy vs := by
  first
  | induction vs with
    | nil => rfl
    | cons v vs ih =>
        have hv := hvs v List.mem_cons_self
        have ht := fun w hw => hvs w (List.mem_cons_of_mem v hw)
        have hs : 0 ≤ (vs.map (cornerInteraction v)).sum := by
          first
          | apply List.sum_nonneg
            intro x hx
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
            exact cornerInteraction_nonneg hv (ht w hw)
        dsimp only [cornerEnergy]
        exact add_nonneg (add_nonneg (ih ht) (mul_nonneg hv.1 (neg_nonneg.mpr hv.2)))
          (mul_nonneg (by norm_num) hs)

theorem cornerInteraction_smul (t : ℝ) (v w : Plane) :
    cornerInteraction (t • v) (t • w) = t ^ 2 * cornerInteraction v w := by
  first
  | simp only [cornerInteraction, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have h₁ : t * v.1 * -(t * w.2) = t ^ 2 * (v.1 * (-w.2)) := by ring
    have h₂ : t * w.1 * -(t * v.2) = t ^ 2 * (w.1 * (-v.2)) := by ring
    rw [h₁, h₂, ← mul_min_of_nonneg _ _ (sq_nonneg t)]

theorem cornerEnergy_smul (t : ℝ) (vs : List Plane) :
    cornerEnergy (vs.map (fun v => t • v)) = t ^ 2 * cornerEnergy vs := by
  first
  | induction vs with
    | nil => simp [cornerEnergy]
    | cons v vs ih =>
        simp only [List.map_cons, cornerEnergy, ih, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul, List.map_map, Function.comp_def, cornerInteraction_smul]
        rw [List.sum_map_mul_left]
        ring

theorem cornerEnergy_cons_horizontal {r : ℝ} (hr : 0 ≤ r) {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy ((r, 0) :: vs) = cornerEnergy vs := by
  first
  | have hs : (vs.map (cornerInteraction (r, 0))).sum = 0 := by
      first
      | apply List.sum_eq_zero
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        simp only [cornerInteraction, neg_zero, mul_zero]
        exact min_eq_right (mul_nonneg hr (neg_nonneg.mpr (hvs v hv).2))
    simp [cornerEnergy, hs]

theorem cornerEnergy_cons_vertical {r : ℝ} (hr : 0 ≤ r) {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy ((0, -r) :: vs) = cornerEnergy vs := by
  first
  | have hs : (vs.map (cornerInteraction (0, -r))).sum = 0 := by
      first
      | apply List.sum_eq_zero
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        simp only [cornerInteraction, zero_mul, neg_neg]
        exact min_eq_left (mul_nonneg (hvs v hv).1 hr)
    simp [cornerEnergy, hs]

/-- Adding the two axis directions restores widths while preserving the
quadratic scaling of the genuine area deficit. -/
def interpolatedGenerators (t : ℝ) (vs : List Plane) : List Plane :=
  (1 - t, 0) :: (0, -(1 - t)) :: vs.map (fun v => t • v)

theorem interpolatedGenerators_signed {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {vs : List Plane} (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    ∀ v ∈ interpolatedGenerators t vs, 0 ≤ v.1 ∧ v.2 ≤ 0 := by
  first
  | intro v hv
    simp only [interpolatedGenerators, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | rfl | ⟨w, hw, rfl⟩
    · exact ⟨sub_nonneg.mpr ht.2, le_rfl⟩
    · exact ⟨le_rfl, neg_nonpos.mpr (sub_nonneg.mpr ht.2)⟩
    · exact ⟨mul_nonneg ht.1 (hvs w hw).1,
        mul_nonpos_of_nonneg_of_nonpos ht.1 (hvs w hw).2⟩

theorem interpolatedGenerators_sum (t : ℝ) {vs : List Plane}
    (hsum : vs.sum = (1, -1)) : (interpolatedGenerators t vs).sum = (1, -1) := by
  first
  | simp only [interpolatedGenerators, List.sum_cons, ← List.smul_sum, hsum]
    ext <;> simp <;> ring

theorem cornerEnergy_interpolated {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {vs : List Plane} (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy (interpolatedGenerators t vs) = t ^ 2 * cornerEnergy vs := by
  first
  | have hm : ∀ w ∈ vs.map (fun v => t • v), 0 ≤ w.1 ∧ w.2 ≤ 0 := by
      first
      | intro w hw
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        exact ⟨mul_nonneg ht.1 (hvs v hv).1,
          mul_nonpos_of_nonneg_of_nonpos ht.1 (hvs v hv).2⟩
    unfold interpolatedGenerators
    rw [cornerEnergy_cons_horizontal (sub_nonneg.mpr ht.2),
      cornerEnergy_cons_vertical (sub_nonneg.mpr ht.2) hm, cornerEnergy_smul]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨le_rfl, neg_nonpos.mpr (sub_nonneg.mpr ht.2)⟩
    · exact hm v hv

theorem area_interpolated_cap {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {vs : List Plane} (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0)
    (hsum : vs.sum = (1, -1)) :
    volume.real (cap (interpolatedGenerators t vs)) =
      1 / 2 - t ^ 2 * (1 / 2 - volume.real (cap vs)) := by
  first
  | rw [area_unit_cap (interpolatedGenerators_sum t hsum), area_unit_cap hsum,
      cornerEnergy_interpolated ht hvs]
    ring

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteCornerCaps.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteCornerMeasures.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Actual slope measures and the exact area of finite convex caps -/

noncomputable section
open MeasureTheory Set
open scoped NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def edgeSlope (v : Plane) : ℝ := Real.log ((-v.2) / v.1)

def edgeWeight (v : Plane) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (v.1 * (-v.2))) (Real.sqrt_nonneg _)

def edgeVector (v : Plane) : Lp ℝ 2 (volume : Measure ℝ) :=
  (edgeWeight v : ℝ) • cornerFeature (edgeSlope v)

def edgeMeasure (v : Plane) : Measure ℝ :=
  edgeWeight v • Measure.dirac (edgeSlope v)

instance edgeMeasure_finite (v : Plane) : IsFiniteMeasure (edgeMeasure v) := by
  first
  | unfold edgeMeasure
    infer_instance

def cornerMeasure : List Plane → Measure ℝ
  | [] => 0
  | v :: vs => cornerMeasure vs + edgeMeasure v

instance cornerMeasure_finite (vs : List Plane) : IsFiniteMeasure (cornerMeasure vs) := by
  first
  | induction vs with
    | nil => dsimp only [cornerMeasure]; infer_instance
    | cons v vs ih =>
        letI : IsFiniteMeasure (cornerMeasure vs) := ih
        change IsFiniteMeasure (cornerMeasure vs + edgeMeasure v)
        infer_instance

theorem integrable_edgeMeasure (v : Plane) (f : ℝ → ℝ) : Integrable f (edgeMeasure v) :=
  (integrable_dirac (f := f) (a := edgeSlope v) enorm_lt_top).smul_measure_nnreal

theorem integrable_cornerMeasure (vs : List Plane) (f : ℝ → ℝ) :
    Integrable f (cornerMeasure vs) := by
  first
  | induction vs with
    | nil => exact integrable_zero_measure
    | cons v vs ih => exact ih.add_measure (integrable_edgeMeasure v f)

theorem integral_edgeMeasure (v : Plane) (f : ℝ → ℝ) :
    (∫ x, f x ∂edgeMeasure v) = (edgeWeight v : ℝ) * f (edgeSlope v) := by
  first
  | change (∫ x, f x ∂(edgeWeight v • Measure.dirac (edgeSlope v))) = _
    rw [integral_smul_nnreal_measure, integral_dirac]
    rfl

theorem edgeMeasure_exponential_moments_le {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    (∫ x, Real.exp (-x / 2) ∂edgeMeasure v) ≤ v.1 ∧
      (∫ x, Real.exp (x / 2) ∂edgeMeasure v) ≤ -v.2 := by
  first
  | rw [integral_edgeMeasure, integral_edgeMeasure]
    change Real.sqrt (v.1 * (-v.2)) * Real.exp (-Real.log ((-v.2) / v.1) / 2) ≤ v.1 ∧
      Real.sqrt (v.1 * (-v.2)) * Real.exp (Real.log ((-v.2) / v.1) / 2) ≤ -v.2
    by_cases ha : v.1 = 0
    · simpa [ha] using neg_nonneg.mpr hv.2
    by_cases hb : v.2 = 0
    · simpa [hb] using hv.1
    have hm := atom_exponential_moments (lt_of_le_of_ne hv.1 (Ne.symm ha))
      (neg_pos.mpr (lt_of_le_of_ne hv.2 hb))
    exact ⟨hm.1.le, hm.2.le⟩

/-- Omitting axis edges can only decrease the signed coordinate totals. -/
theorem cornerMeasure_exponential_moments_le {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    (∫ x, Real.exp (-x / 2) ∂cornerMeasure vs) ≤ vs.sum.1 ∧
      (∫ x, Real.exp (x / 2) ∂cornerMeasure vs) ≤ -vs.sum.2 := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih =>
        have hv := edgeMeasure_exponential_moments_le (hvs v List.mem_cons_self)
        have ht := ih (fun w hw => hvs w (List.mem_cons_of_mem v hw))
        simp only [cornerMeasure, integral_add_measure (integrable_cornerMeasure vs _)
          (integrable_edgeMeasure v _), List.sum_cons, Prod.fst_add, Prod.snd_add]
        constructor <;> linarith

/-- The genuine nonnegative integrals, so nonintegrability cannot make the
moment condition vacuous. -/
theorem unit_cornerMeasure_lintegral_moments {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x / 2)) ∂cornerMeasure vs) ≤ 1 ∧
      (∫⁻ x, ENNReal.ofReal (Real.exp (x / 2)) ∂cornerMeasure vs) ≤ 1 := by
  first
  | have h := cornerMeasure_exponential_moments_le hvs
    rw [hsum] at h
    constructor
    · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cornerMeasure vs _)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h.1
    · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cornerMeasure vs _)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
      simpa using ENNReal.ofReal_le_ofReal h.2

theorem inner_edgeVector {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    ⟪edgeVector v, edgeVector w⟫_ℝ = cornerInteraction v w := by
  first
  | have h := weighted_cornerKernel hv.1 (neg_nonneg.mpr hv.2)
      hw.1 (neg_nonneg.mpr hw.2)
    simpa only [edgeVector, real_inner_smul_left, real_inner_smul_right, inner_cornerFeature,
      edgeWeight, edgeSlope, NNReal.coe_mk, cornerInteraction,
      mul_comm, mul_left_comm, mul_assoc] using h

theorem cornerMean_edgeMeasure (v : Plane) : cornerMean (edgeMeasure v) = edgeVector v := by
  first
  | simp only [cornerMean, edgeMeasure, integral_smul_nnreal_measure, integral_dirac,
      NNReal.smul_def, edgeVector]

theorem cornerMean_cons (v : Plane) (vs : List Plane) :
    cornerMean (cornerMeasure (v :: vs)) = cornerMean (cornerMeasure vs) + edgeVector v := by
  first
  | change (∫ x, cornerFeature x ∂(cornerMeasure vs + edgeMeasure v)) = _
    rw [integral_add_measure (integrable_cornerFeature _) (integrable_cornerFeature _)]
    exact congrArg (cornerMean (cornerMeasure vs) + ·) (cornerMean_edgeMeasure v)

theorem inner_cornerMean_edgeVector {vs : List Plane} {v : Plane}
    (hvs : ∀ w ∈ vs, 0 ≤ w.1 ∧ w.2 ≤ 0) (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    ⟪cornerMean (cornerMeasure vs), edgeVector v⟫_ℝ =
      (vs.map (cornerInteraction v)).sum := by
  first
  | induction vs with
    | nil => simp [cornerMeasure, cornerMean]
    | cons w vs ih =>
        rw [cornerMean_cons, inner_add_left, ih (fun z hz => hvs z (List.mem_cons_of_mem w hz)),
          real_inner_comm (edgeVector v) (edgeVector w),
          inner_edgeVector hv (hvs w List.mem_cons_self)]
        simp only [List.map_cons, List.sum_cons, add_comm]

/-- The finite algebraic energy equals the genuine double exponential-kernel
integral of the actual slope measure. Axis generators automatically carry zero mass. -/
theorem cornerEnergy_eq_mean_norm {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy vs = ‖cornerMean (cornerMeasure vs)‖ ^ 2 := by
  first
  | induction vs with
    | nil => simp [cornerEnergy, cornerMeasure, cornerMean]
    | cons v vs ih =>
        have hv := hvs v List.mem_cons_self
        have ht := fun w hw => hvs w (List.mem_cons_of_mem v hw)
        rw [cornerMean_cons, norm_add_sq_real,
          inner_cornerMean_edgeVector ht hv, ← ih ht]
        have hn : ‖edgeVector v‖ ^ 2 = v.1 * (-v.2) := by
          first
          | rw [← real_inner_self_eq_norm_sq, inner_edgeVector hv hv]
            simp [cornerInteraction]
        rw [hn]
        dsimp only [cornerEnergy]
        ring

theorem area_cap_eq_kernel_energy {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    volume.real (cap vs) = 1 / 2 -
      (1 / 2) * (∫ x, ∫ y, cornerKernel x y ∂cornerMeasure vs ∂cornerMeasure vs) := by
  first
  | rw [area_unit_cap hsum, cornerEnergy_eq_mean_norm hvs, norm_cornerMean_sq]
    ring

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteCornerMeasures.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteCornerInteraction.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Literal finite cap interactions and their convolution measures

This module identifies the constructed cap's area and slope measure. The
separate mixed-volume identity of Proposition 4.3 is not assumed here.
-/

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal MeasureTheory ComplexConjugate

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def interactionVector (v w : Plane) : Plane := ((-v.2) * w.1, v.1 * w.2)

def interactionGenerators (vs ws : List Plane) : List Plane :=
  vs.flatMap (fun v => ws.map (interactionVector v))

theorem interactionVector_signed {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    0 ≤ (interactionVector v w).1 ∧ (interactionVector v w).2 ≤ 0 :=
  ⟨mul_nonneg (neg_nonneg.mpr hv.2) hw.1, mul_nonpos_of_nonneg_of_nonpos hv.1 hw.2⟩

theorem interactionGenerators_signed {vs ws : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0)
    (hw : ∀ w ∈ ws, 0 ≤ w.1 ∧ w.2 ≤ 0) :
    ∀ z ∈ interactionGenerators vs ws, 0 ≤ z.1 ∧ z.2 ≤ 0 := by
  first
  | intro z hz
    obtain ⟨v, hv', hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hz
    exact interactionVector_signed (hv v hv') (hw w hw')

theorem sum_interactionVector (v : Plane) (ws : List Plane) :
    (ws.map (interactionVector v)).sum = interactionVector v ws.sum := by
  first
  | induction ws with
    | nil => ext <;> simp [interactionVector]
    | cons w ws ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ext <;> simp [interactionVector, mul_add]

theorem interactionGenerators_sum (vs ws : List Plane) :
    (interactionGenerators vs ws).sum = interactionVector vs.sum ws.sum := by
  first
  | induction vs with
    | nil => ext <;> simp [interactionGenerators, interactionVector]
    | cons v vs ih =>
        simp only [interactionGenerators, List.flatMap_cons, List.sum_append,
          sum_interactionVector, List.sum_cons] at *
        rw [ih]
        ext <;> simp [interactionVector, add_mul] <;> ring

theorem interactionGenerators_unit {vs ws : List Plane}
    (hv : vs.sum = (1, -1)) (hw : ws.sum = (1, -1)) :
    (interactionGenerators vs ws).sum = (1, -1) := by
  first
  | rw [interactionGenerators_sum, hv, hw]
    norm_num [interactionVector]

theorem edgeWeight_interaction {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    edgeWeight (interactionVector v w) = edgeWeight v * edgeWeight w := by
  first
  | apply NNReal.eq
    change Real.sqrt (((-v.2) * w.1) * (-(v.1 * w.2))) =
      Real.sqrt (v.1 * (-v.2)) * Real.sqrt (w.1 * (-w.2))
    rw [show ((-v.2) * w.1) * (-(v.1 * w.2)) =
      (v.1 * (-v.2)) * (w.1 * (-w.2)) by ring]
    exact Real.sqrt_mul (mul_nonneg hv.1 (neg_nonneg.mpr hv.2)) _

theorem edgeSlope_interaction {v w : Plane}
    (hv : 0 < v.1 ∧ v.2 < 0) (hw : 0 < w.1 ∧ w.2 < 0) :
    edgeSlope (interactionVector v w) = edgeSlope w - edgeSlope v := by
  first
  | have hv2 : 0 < -v.2 := neg_pos.mpr hv.2
    have hw2 : 0 < -w.2 := neg_pos.mpr hw.2
    change Real.log ((-(v.1 * w.2)) / ((-v.2) * w.1)) =
      Real.log ((-w.2) / w.1) - Real.log ((-v.2) / v.1)
    rw [neg_mul_eq_mul_neg, Real.log_div (mul_pos hv.1 hw2).ne'
        (mul_pos hv2 hw.1).ne',
      Real.log_mul hv.1.ne' hw2.ne', Real.log_mul hv2.ne' hw.1.ne',
      Real.log_div hw2.ne' hw.1.ne', Real.log_div hv2.ne' hv.1.ne']
    ring

theorem coordinates_positive_of_edgeWeight_ne_zero {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hn : edgeWeight v ≠ 0) :
    0 < v.1 ∧ v.2 < 0 := by
  first
  | constructor
    · by_contra h
      have he : v.1 = 0 := le_antisymm (le_of_not_gt h) hv.1
      apply hn
      apply NNReal.eq
      change Real.sqrt (v.1 * (-v.2)) = 0
      simp [he]
    · by_contra h
      have he : v.2 = 0 := le_antisymm hv.2 (le_of_not_gt h)
      apply hn
      apply NNReal.eq
      change Real.sqrt (v.1 * (-v.2)) = 0
      simp [he]

theorem conv_nnreal_smul (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : ℝ≥0) : (a • μ) ∗ (b • ν) = (a * b) • (μ ∗ ν) := by
  first
  | rw [← Measure.coe_nnreal_smul a, ← Measure.coe_nnreal_smul b,
      Measure.conv_smul_left, Measure.conv_smul_right, smul_smul,
      ← ENNReal.coe_mul, Measure.coe_nnreal_smul]

/-- Each non-axis pair has difference logarithmic slope and product mass;
axis pairs have zero mass on both sides of the same measure identity. -/
theorem edgeMeasure_interaction {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    edgeMeasure (interactionVector v w) =
      (edgeMeasure v).map Neg.neg ∗ edgeMeasure w := by
  first
  | rw [edgeMeasure, edgeWeight_interaction hv hw]
    unfold edgeMeasure
    rw [Measure.map_smul _ (by fun_prop), Measure.map_dirac' (by fun_prop),
      conv_nnreal_smul, Measure.dirac_conv_dirac]
    by_cases hzv : edgeWeight v = 0
    · simp [hzv]
    by_cases hzw : edgeWeight w = 0
    · simp [hzw]
    rw [edgeSlope_interaction (coordinates_positive_of_edgeWeight_ne_zero hv hzv)
      (coordinates_positive_of_edgeWeight_ne_zero hw hzw)]
    congr 2
    ring

theorem cornerMeasure_append (vs ws : List Plane) :
    cornerMeasure (vs ++ ws) = cornerMeasure vs + cornerMeasure ws := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih => simp [cornerMeasure, ih, add_assoc, add_comm, add_left_comm]

theorem cornerMeasure_map_interaction {v : Plane} {ws : List Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : ∀ w ∈ ws, 0 ≤ w.1 ∧ w.2 ≤ 0) :
    cornerMeasure (ws.map (interactionVector v)) =
      (edgeMeasure v).map Neg.neg ∗ cornerMeasure ws := by
  first
  | induction ws with
    | nil => simp [cornerMeasure]
    | cons w ws ih =>
        rw [List.map_cons, cornerMeasure, cornerMeasure,
          ih (fun z hz => hw z (List.mem_cons_of_mem w hz)),
          edgeMeasure_interaction hv (hw w List.mem_cons_self), Measure.conv_add]

/-- The constructed finite cap has exactly the convolution slope measure in
equation (4.11); this does not yet identify its mixed-volume functional. -/
theorem cornerMeasure_interaction {vs ws : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0)
    (hw : ∀ w ∈ ws, 0 ≤ w.1 ∧ w.2 ≤ 0) :
    cornerMeasure (interactionGenerators vs ws) =
      (cornerMeasure vs).map Neg.neg ∗ cornerMeasure ws := by
  first
  | induction vs with
    | nil => simp [interactionGenerators, cornerMeasure]
    | cons v vs ih =>
        change cornerMeasure (ws.map (interactionVector v) ++ interactionGenerators vs ws) =
          (cornerMeasure (v :: vs)).map Neg.neg ∗ cornerMeasure ws
        rw [cornerMeasure_append,
          cornerMeasure_map_interaction (hv v List.mem_cons_self) hw,
          ih (fun z hz => hv z (List.mem_cons_of_mem v hz)), cornerMeasure,
          Measure.map_add (cornerMeasure vs) (edgeMeasure v) (by fun_prop),
          Measure.add_conv]
        exact add_comm _ _

theorem charFun_reflect (μ : Measure ℝ) (ξ : ℝ) :
    charFun (μ.map Neg.neg) ξ = conj (charFun μ ξ) := by
  first
  | have h := charFun_map_mul (μ := μ) (-1) ξ
    simpa only [neg_one_mul, charFun_neg] using h

/-- Reflection on one input leaves the self-interaction energy unchanged.
This follows for every finite measure from the proved Fourier identity. -/
theorem reflected_self_convolution_energy (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖cornerMean (μ.map Neg.neg ∗ μ)‖ ^ 2 = ‖cornerMean (μ ∗ μ)‖ ^ 2 := by
  first
  | rw [← corner_spectral_energy, ← corner_spectral_energy]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by
      dsimp only
      rw [charFun_conv, charFun_conv, charFun_reflect]
      simp only [map_mul, Complex.normSq_conj]

theorem area_self_interaction_cap {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    volume.real (cap (interactionGenerators vs vs)) =
      1 / 2 - ‖cornerMean (cornerMeasure vs ∗ cornerMeasure vs)‖ ^ 2 / 2 := by
  first
  | rw [area_unit_cap (interactionGenerators_unit hsum hsum),
      cornerEnergy_eq_mean_norm (interactionGenerators_signed hv hv),
      cornerMeasure_interaction hv hv, reflected_self_convolution_energy]

theorem self_convolution_energy_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : μ.real univ ≤ 1) :
    ‖cornerMean (μ ∗ μ)‖ ^ 2 ≤ ‖cornerMean μ‖ ^ 2 := by
  first
  | rw [← corner_spectral_energy, ← corner_spectral_energy]
    apply integral_mono (integrable_spectral_normSq (μ ∗ μ)) (integrable_spectral_normSq μ)
    intro ξ
    dsimp only
    rw [charFun_conv, map_mul]
    have hn := norm_charFun_le (μ := μ) ξ
    have hn1 : ‖charFun μ ξ‖ ≤ 1 := hn.trans hm
    have he : Complex.normSq (charFun μ ξ) ≤ 1 := by
      first
      | rw [← Complex.sq_norm]
        nlinarith [norm_nonneg (charFun μ ξ)]
    nlinarith [Complex.normSq_nonneg (charFun μ ξ)]

/-- For the literal finite cap family, the interaction area is at least the
input area, including degenerate generators. -/
theorem area_self_interaction_ge {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    volume.real (cap vs) ≤ volume.real (cap (interactionGenerators vs vs)) := by
  first
  | have hmoment := unit_cornerMeasure_lintegral_moments hv hsum
    have hm : (cornerMeasure vs).real univ ≤ 1 := by
      first
      | apply slope_mass_le_one
        · simpa [slopeExponentialMoment, div_eq_mul_inv, mul_comm] using hmoment.1
        · simpa [slopeExponentialMoment, div_eq_mul_inv, mul_comm] using hmoment.2
    have henergy := self_convolution_energy_le (cornerMeasure vs) hm
    rw [area_self_interaction_cap hv hsum, area_unit_cap hsum,
      cornerEnergy_eq_mean_norm hv]
    linarith

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteCornerInteraction.lean -/

/- BEGIN SOURCE: VolumePolynomials/GeometricCornerFamily.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # An unbounded finite family with geometrically separated corner slopes -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def stretchHorizontal (t : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun v := (t * v.1, v.2)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro a x; ext <;> simp <;> ring

@[simp] theorem stretchHorizontal_apply (t : ℝ) (v : Plane) :
    stretchHorizontal t v = (t * v.1, v.2) := rfl

theorem cornerInteraction_stretch {t : ℝ} (ht : 0 ≤ t) (v w : Plane) :
    cornerInteraction (stretchHorizontal t v) (stretchHorizontal t w) =
      t * cornerInteraction v w := by
  first
  | simp only [cornerInteraction, stretchHorizontal_apply, mul_assoc]
    exact (mul_min_of_nonneg _ _ ht).symm

theorem cornerEnergy_stretch {t : ℝ} (ht : 0 ≤ t) (vs : List Plane) :
    cornerEnergy (vs.map (stretchHorizontal t)) = t * cornerEnergy vs := by
  first
  | induction vs with
    | nil => simp [cornerEnergy]
    | cons v vs ih =>
        simp only [List.map_cons, cornerEnergy, ih, List.map_map, Function.comp_def]
        simp only [cornerInteraction_stretch ht]
        rw [List.sum_map_mul_left]
        simp only [stretchHorizontal_apply]
        ring

/-- The list consists of `(4^i,-4^(n-1-i))` for `0≤i<n`; the recursive
definition avoids truncated natural subtraction in subsequent proofs. -/
def rawGeometricGenerators : ℕ → List Plane
  | 0 => []
  | n + 1 => (1, -(4 : ℝ) ^ n) ::
      (rawGeometricGenerators n).map (stretchHorizontal 4)

@[simp] theorem rawGeometricGenerators_length (n : ℕ) :
    (rawGeometricGenerators n).length = n := by
  first
  | induction n with
    | zero => rfl
    | succ n ih => simp [rawGeometricGenerators, ih]

theorem rawGeometricGenerators_sum (n : ℕ) :
    (rawGeometricGenerators n).sum =
      (((4 : ℝ) ^ n - 1) / 3, -((4 : ℝ) ^ n - 1) / 3) := by
  first
  | induction n with
    | zero => ext <;> norm_num [rawGeometricGenerators]
    | succ n ih =>
        rw [rawGeometricGenerators, List.sum_cons, ← map_list_sum, ih]
        ext <;> simp only [Prod.fst_add, Prod.snd_add, stretchHorizontal_apply, pow_succ] <;>
          ring

theorem rawGeometricGenerators_bounds (n : ℕ) :
    ∀ v ∈ rawGeometricGenerators n,
      1 ≤ v.1 ∧ 1 ≤ -v.2 ∧ v.1 ≤ (4 : ℝ) ^ n ∧ -v.2 ≤ (4 : ℝ) ^ n := by
  first
  | induction n with
    | zero => simp [rawGeometricGenerators]
    | succ n ih =>
        intro v hv
        have hp : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
        simp only [rawGeometricGenerators, List.mem_cons, List.mem_map] at hv
        rcases hv with rfl | ⟨w, hw, rfl⟩
        · simp only [neg_neg, pow_succ]
          exact ⟨le_rfl, hp, by nlinarith, by nlinarith⟩
        · obtain ⟨h1, h2, h3, h4⟩ := ih w hw
          simp only [stretchHorizontal_apply, pow_succ]
          exact ⟨by linarith, h2, by linarith, by nlinarith⟩

theorem rawGeometricGenerators_signed (n : ℕ) :
    ∀ v ∈ rawGeometricGenerators n, 0 ≤ v.1 ∧ v.2 ≤ 0 := by
  first
  | intro v hv
    have h := rawGeometricGenerators_bounds n v hv
    exact ⟨by linarith [h.1], by linarith [h.2.1]⟩

theorem sum_neg_snd (vs : List Plane) :
    (vs.map (fun v => -v.2)).sum = -vs.sum.2 := by
  first
  | induction vs with
    | nil => simp
    | cons v vs ih => simp [ih, add_comm]

theorem raw_corner_cross_sum (n : ℕ) :
    (((rawGeometricGenerators n).map (stretchHorizontal 4)).map
      (cornerInteraction (1, -(4 : ℝ) ^ n))).sum = ((4 : ℝ) ^ n - 1) / 3 := by
  first
  | have heq : ((rawGeometricGenerators n).map (stretchHorizontal 4)).map
        (cornerInteraction (1, -(4 : ℝ) ^ n)) =
          (rawGeometricGenerators n).map (fun v => -v.2) := by
      first
      | rw [List.map_map]
        apply List.map_congr_left
        intro v hv
        obtain ⟨h1, h2, h3, h4⟩ := rawGeometricGenerators_bounds n v hv
        have hp : (0 : ℝ) ≤ 4 ^ n := pow_nonneg (by norm_num) n
        have hprod := mul_nonneg (by linarith : 0 ≤ 4 * v.1 - 1) hp
        simp only [Function.comp_apply, cornerInteraction, stretchHorizontal_apply,
          one_mul, neg_neg]
        exact min_eq_left (by nlinarith)
    rw [heq, sum_neg_snd, rawGeometricGenerators_sum]
    ring

theorem raw_cornerEnergy_succ (n : ℕ) :
    cornerEnergy (rawGeometricGenerators (n + 1)) =
      4 * cornerEnergy (rawGeometricGenerators n) + (4 : ℝ) ^ n +
        2 * (((4 : ℝ) ^ n - 1) / 3) := by
  first
  | rw [rawGeometricGenerators, cornerEnergy, cornerEnergy_stretch (by norm_num),
      raw_corner_cross_sum]
    simp

/-- Bounds valid for every index, including zero. -/
theorem raw_cornerEnergy_bounds (n : ℕ) :
    (n : ℝ) * (4 : ℝ) ^ n ≤ 4 * cornerEnergy (rawGeometricGenerators n) ∧
      4 * cornerEnergy (rawGeometricGenerators n) ≤
        (5 / 3) * (n : ℝ) * (4 : ℝ) ^ n := by
  first
  | induction n with
    | zero => norm_num [rawGeometricGenerators, cornerEnergy]
    | succ n ih =>
        have hp : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
        rw [raw_cornerEnergy_succ]
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        constructor <;> nlinarith [ih.1, ih.2]

def geometricNormalizer (n : ℕ) : ℝ := 3 / ((4 : ℝ) ^ n - 1)

def geometricGenerators (n : ℕ) : List Plane :=
  (rawGeometricGenerators n).map (fun v => geometricNormalizer n • v)

theorem geometricNormalizer_pos {n : ℕ} (hn : 0 < n) : 0 < geometricNormalizer n := by
  first
  | apply div_pos (by norm_num)
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num : (1 : ℝ) < 4) hn.ne')

theorem geometricNormalizer_identity {n : ℕ} (hn : 0 < n) :
    geometricNormalizer n * ((4 : ℝ) ^ n - 1) = 3 := by
  first
  | unfold geometricNormalizer
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr
      (ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℝ) < 4) hn.ne')))

theorem geometricGenerators_sum {n : ℕ} (hn : 0 < n) :
    (geometricGenerators n).sum = (1, -1) := by
  first
  | rw [geometricGenerators, ← List.smul_sum, rawGeometricGenerators_sum]
    have h := geometricNormalizer_identity hn
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith

theorem geometricGenerators_signed {n : ℕ} (hn : 0 < n) :
    ∀ v ∈ geometricGenerators n, 0 ≤ v.1 ∧ v.2 ≤ 0 := by
  first
  | intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have h := rawGeometricGenerators_signed n w hw
    exact ⟨mul_nonneg (geometricNormalizer_pos hn).le h.1,
      mul_nonpos_of_nonneg_of_nonpos (geometricNormalizer_pos hn).le h.2⟩

def geometricDeficit (n : ℕ) : ℝ := cornerEnergy (geometricGenerators n) / 2

theorem geometricDeficit_formula (n : ℕ) :
    geometricDeficit n = geometricNormalizer n ^ 2 *
      cornerEnergy (rawGeometricGenerators n) / 2 := by
  first
  | rw [geometricDeficit, geometricGenerators, cornerEnergy_smul]

theorem geometricDeficit_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ geometricDeficit n :=
  div_nonneg (cornerEnergy_nonneg (geometricGenerators_signed hn)) (by norm_num)

/-- The deficit is that of the actual unit-width compact convex cap. -/
theorem area_geometricCap {n : ℕ} (hn : 0 < n) :
    volume.real (cap (geometricGenerators n)) = 1 / 2 - geometricDeficit n := by
  first
  | exact area_unit_cap (geometricGenerators_sum hn)

theorem geometricDeficit_weighted_bounds (n : ℕ) :
    geometricNormalizer n ^ 2 * (n : ℝ) * (4 : ℝ) ^ n / 8 ≤ geometricDeficit n ∧
      geometricDeficit n ≤ 5 * geometricNormalizer n ^ 2 * (n : ℝ) * (4 : ℝ) ^ n / 24 := by
  first
  | have h := raw_cornerEnergy_bounds n
    have hlow := mul_le_mul_of_nonneg_left h.1 (sq_nonneg (geometricNormalizer n))
    have hupp := mul_le_mul_of_nonneg_left h.2 (sq_nonneg (geometricNormalizer n))
    rw [geometricDeficit_formula]
    constructor <;> nlinarith

theorem geometricNormalizer_scaled_bounds {n : ℕ} (hn : 0 < n) :
    3 ≤ geometricNormalizer n * (4 : ℝ) ^ n ∧
      geometricNormalizer n * (4 : ℝ) ^ n ≤ 4 := by
  first
  | have hk := geometricNormalizer_pos hn
    have hidentity := geometricNormalizer_identity hn
    have hpow : (4 : ℝ) ≤ 4 ^ n := by
      first
      | simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hn
    have hk1 : geometricNormalizer n ≤ 1 := by
      first
      | unfold geometricNormalizer
        apply (div_le_one (by linarith : 0 < (4 : ℝ) ^ n - 1)).mpr
        linarith
    constructor <;> nlinarith

/-- Exponential lower control needed to turn the first crossing into a
logarithmic bound; no monotonicity of the deficit sequence is assumed. -/
theorem geometricDeficit_bounds {n : ℕ} (hn : 0 < n) :
    ((4 : ℝ) ^ n)⁻¹ ≤ geometricDeficit n ∧
      geometricDeficit n ≤ (10 / 3) * (n : ℝ) / (4 : ℝ) ^ n := by
  first
  | have hp : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hk := geometricNormalizer_scaled_bounds hn
    have hweight := geometricDeficit_weighted_bounds n
    have hsqlo : 9 ≤ (geometricNormalizer n * (4 : ℝ) ^ n) ^ 2 := by nlinarith
    have hsqup : (geometricNormalizer n * (4 : ℝ) ^ n) ^ 2 ≤ 16 := by nlinarith
    have hlo := mul_le_mul_of_nonneg_right hweight.1 hp.le
    have hup := mul_le_mul_of_nonneg_right hweight.2 hp.le
    have hnl := mul_le_mul_of_nonneg_left hsqlo hn0
    have hnu := mul_le_mul_of_nonneg_left hsqup hn0
    constructor
    · apply (inv_le_iff_one_le_mul₀ hp).mpr
      nlinarith
    · apply (le_div_iff₀ hp).mpr
      nlinarith

theorem geometricDeficit_tendsto_zero : Tendsto geometricDeficit atTop (𝓝 0) := by
  first
  | have hupper : Tendsto (fun n : ℕ => (10 / 3 : ℝ) * (n : ℝ) / (4 : ℝ) ^ n)
        atTop (𝓝 0) := by
      first
      | simpa [pow_one, mul_div_assoc] using
          (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)).const_mul
            (10 / 3 : ℝ)
    apply squeeze_zero' _ _ hupper
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact geometricDeficit_nonneg hn
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact (geometricDeficit_bounds hn).2

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/GeometricCornerFamily.lean -/

/- BEGIN SOURCE: VolumePolynomials/CompactKernelMass.lean -/
section


@[expose] public section

/-! # The exact compact-support mass test used by the lower witnesses -/

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace RealInnerProductSpace MeasureTheory

namespace VolumePolynomials

theorem inner_cornerMean_test_eq_mass {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) :
    ⟪cornerMean μ, cornerMean (cornerTestMeasure R)⟫_ℝ = μ.real univ := by
  first
  | rw [real_inner_comm]
    change ⟪cornerMean (cornerTestMeasure R), ∫ x, cornerFeature x ∂μ⟫_ℝ = _
    rw [← integral_inner (integrable_cornerFeature μ)]
    calc
      _ = ∫ _x, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hSupport] with x hx
        rw [real_inner_comm, inner_cornerFeature_mean, integral_cornerTestMeasure hR]
        exact cornerTestPotential_inside hx.1 hx.2
      _ = μ.real univ := by simp

/-- A measure supported on an interval has energy at least its squared mass
divided by the exact energy of the test measure. -/
theorem compact_mass_sq_le_energy {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) :
    (μ.real univ) ^ 2 ≤ (1 + R / 2) * ‖cornerMean μ‖ ^ 2 := by
  first
  | have hCS := abs_real_inner_le_norm (cornerMean μ) (cornerMean (cornerTestMeasure R))
    have hsq := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hCS
    rw [inner_cornerMean_test_eq_mass hR μ hSupport, sq_abs, mul_pow,
      norm_cornerMean_test_sq hR] at hsq
    simpa only [mul_comm] using hsq

theorem convolution_real_mass (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ ∗ ν).real univ = μ.real univ * ν.real univ := by
  first
  | have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
    simp [Measure.conv, measureReal_def, Measure.map_apply hadd MeasurableSet.univ,
      ENNReal.toReal_mul]
    rw [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]

theorem convolution_interval_support {R S : ℝ} (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) (hν : ∀ᵐ y ∂ν, y ∈ Icc (-S) S) :
    ∀ᵐ z ∂(μ ∗ ν), z ∈ Icc (-(R + S)) (R + S) := by
  first
  | rw [Measure.conv]
    have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
    apply (ae_map_iff (μ := μ.prod ν) (f := fun p : ℝ × ℝ => p.1 + p.2)
      (p := fun z : ℝ => z ∈ Icc (-(R + S)) (R + S))
      hadd.aemeasurable measurableSet_Icc).mpr
    apply (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := ν)
      (measurableSet_Icc.preimage hadd)).mpr
    filter_upwards [hμ] with x hx
    filter_upwards [hν] with y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The convolution lower bound used in Proposition5.4, for every finite
positive measure supported in the stated interval. -/
theorem compact_convolution_mass_fourth_le_energy {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) :
    (μ.real univ) ^ 4 ≤ (1 + R) * ‖cornerMean (μ ∗ μ)‖ ^ 2 := by
  first
  | have h := compact_mass_sq_le_energy (add_nonneg hR hR) (μ ∗ μ)
      (convolution_interval_support μ μ hSupport hSupport)
    rw [convolution_real_mass] at h
    convert h using 1 <;> ring

end VolumePolynomials
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CompactKernelMass.lean -/

/- BEGIN SOURCE: VolumePolynomials/GeometricCornerMeasure.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The actual measures of the geometrically separated finite caps -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal MeasureTheory

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

theorem rawGeometricGenerators_product (n : ℕ) :
    ∀ v ∈ rawGeometricGenerators n,
      4 * (v.1 * (-v.2)) = (4 : ℝ) ^ n := by
  first
  | induction n with
    | zero => simp [rawGeometricGenerators]
    | succ n ih =>
        intro v hv
        simp only [rawGeometricGenerators, List.mem_cons, List.mem_map] at hv
        rcases hv with rfl | ⟨w, hw, rfl⟩
        · simp [pow_succ, mul_comm]
        · have h := ih w hw
          simp only [stretchHorizontal_apply, pow_succ]
          nlinarith

def geometricWeight (n : ℕ) : ℝ :=
  geometricNormalizer n * Real.sqrt ((4 : ℝ) ^ n) / 2

theorem geometricWeight_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ geometricWeight n := by
  first
  | exact div_nonneg (mul_nonneg (geometricNormalizer_pos hn).le (Real.sqrt_nonneg _))
      (by norm_num)

theorem geometricWeight_sq (n : ℕ) :
    geometricWeight n ^ 2 = geometricNormalizer n ^ 2 * (4 : ℝ) ^ n / 4 := by
  first
  | simp only [geometricWeight, div_pow, mul_pow,
      Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) n)]
    norm_num

theorem edgeWeight_geometric {n : ℕ} (hn : 0 < n)
    {v : Plane} (hv : v ∈ geometricGenerators n) :
    (edgeWeight v : ℝ) = geometricWeight n := by
  first
  | obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hs := rawGeometricGenerators_signed n w hw
    have hp := rawGeometricGenerators_product n w hw
    have hprod : 0 ≤ (geometricNormalizer n • w).1 *
        (-(geometricNormalizer n • w).2) := by
      first
      | simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        exact mul_nonneg (mul_nonneg (geometricNormalizer_pos hn).le hs.1)
          (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
            (geometricNormalizer_pos hn).le hs.2))
    have hsq : (edgeWeight (geometricNormalizer n • w) : ℝ) ^ 2 =
        geometricWeight n ^ 2 := by
      first
      | change (Real.sqrt ((geometricNormalizer n • w).1 *
          (-(geometricNormalizer n • w).2))) ^ 2 = _
        rw [Real.sq_sqrt hprod, geometricWeight_sq]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        nlinarith [congrArg (geometricNormalizer n ^ 2 * ·) hp]
    exact (sq_eq_sq₀ (edgeWeight _).coe_nonneg (geometricWeight_nonneg hn)).mp hsq

@[simp] theorem edgeMeasure_real_univ (v : Plane) :
    (edgeMeasure v).real univ = (edgeWeight v : ℝ) := by
  first
  | simp [edgeMeasure]

theorem cornerMeasure_real_univ (vs : List Plane) :
    (cornerMeasure vs).real univ = (vs.map (fun v => (edgeWeight v : ℝ))).sum := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih => simp [cornerMeasure, measureReal_add_apply, ih, add_comm]

theorem geometric_cornerMeasure_mass {n : ℕ} (hn : 0 < n) :
    (cornerMeasure (geometricGenerators n)).real univ = (n : ℝ) * geometricWeight n := by
  first
  | rw [cornerMeasure_real_univ]
    have he : (geometricGenerators n).map (fun v => (edgeWeight v : ℝ)) =
        (geometricGenerators n).map (fun _ => geometricWeight n) := by
      first
      | apply List.map_congr_left
        intro v hv
        exact edgeWeight_geometric hn hv
    rw [he, List.map_const', List.sum_replicate]
    simp [geometricGenerators, nsmul_eq_mul]

theorem edgeSlope_pos_smul {t : ℝ} (ht : 0 < t) (v : Plane) :
    edgeSlope (t • v) = edgeSlope v := by
  first
  | unfold edgeSlope
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [neg_mul_eq_mul_neg, mul_div_mul_left _ _ ht.ne']

theorem rawGeometricGenerators_slope_bounds {n : ℕ}
    {v : Plane} (hv : v ∈ rawGeometricGenerators n) :
    edgeSlope v ∈ Icc (-(n : ℝ) * Real.log 4) ((n : ℝ) * Real.log 4) := by
  first
  | obtain ⟨ha, hb, hA, hB⟩ := rawGeometricGenerators_bounds n v hv
    have hpow : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
    have hapos : 0 < v.1 := by linarith
    have hbpos : 0 < -v.2 := by linarith
    have hpowone : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have hrlo : 1 / (4 : ℝ) ^ n ≤ (-v.2) / v.1 := by
      first
      | apply (div_le_div_iff₀ hpow hapos).mpr
        nlinarith
    have hrhi : (-v.2) / v.1 ≤ (4 : ℝ) ^ n := by
      first
      | apply (div_le_iff₀ hapos).mpr
        nlinarith
    have hlo := Real.log_le_log (div_pos (by norm_num) hpow) hrlo
    have hhi := Real.log_le_log (div_pos hbpos hapos) hrhi
    rw [Real.log_div one_ne_zero hpow.ne', Real.log_one, Real.log_pow] at hlo
    rw [Real.log_pow] at hhi
    exact ⟨by simpa [edgeSlope] using hlo, by simpa [edgeSlope] using hhi⟩

theorem geometricGenerators_slope_bounds {n : ℕ} (hn : 0 < n)
    {v : Plane} (hv : v ∈ geometricGenerators n) :
    edgeSlope v ∈ Icc (-(n : ℝ) * Real.log 4) ((n : ℝ) * Real.log 4) := by
  first
  | obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [edgeSlope_pos_smul (geometricNormalizer_pos hn)]
    exact rawGeometricGenerators_slope_bounds hw

theorem cornerMeasure_support {vs : List Plane} {s : Set ℝ}
    (hs : MeasurableSet s) (hvs : ∀ v ∈ vs, edgeSlope v ∈ s) :
    ∀ᵐ x ∂cornerMeasure vs, x ∈ s := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih =>
        rw [cornerMeasure, ae_add_measure_iff]
        refine ⟨ih (fun w hw => hvs w (List.mem_cons_of_mem v hw)), ?_⟩
        apply Measure.ae_smul_measure _ (edgeWeight v)
        exact (ae_dirac_iff hs).mpr (hvs v List.mem_cons_self)

theorem geometric_cornerMeasure_support {n : ℕ} (hn : 0 < n) :
    ∀ᵐ x ∂cornerMeasure (geometricGenerators n),
      x ∈ Icc (-((n : ℝ) * Real.log 4)) ((n : ℝ) * Real.log 4) := by
  first
  | apply cornerMeasure_support measurableSet_Icc
    intro v hv
    simpa only [neg_mul] using geometricGenerators_slope_bounds hn hv

def geometricConvolutionDeficit (n : ℕ) : ℝ :=
  ‖cornerMean (cornerMeasure (geometricGenerators n) ∗
    cornerMeasure (geometricGenerators n))‖ ^ 2 / 2

theorem geometricConvolutionDeficit_nonneg (n : ℕ) :
    0 ≤ geometricConvolutionDeficit n := div_nonneg (sq_nonneg _) (by norm_num)

theorem geometricConvolution_mass_bound {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) * geometricWeight n) ^ 4 ≤
      2 * (1 + (n : ℝ) * Real.log 4) * geometricConvolutionDeficit n := by
  first
  | have hR : 0 ≤ (n : ℝ) * Real.log 4 :=
      mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num))
    have h := compact_convolution_mass_fourth_le_energy hR
      (cornerMeasure (geometricGenerators n)) (geometric_cornerMeasure_support hn)
    rw [geometric_cornerMeasure_mass hn] at h
    dsimp only [geometricConvolutionDeficit]
    nlinarith

theorem log_four_le_two : Real.log (4 : ℝ) ≤ 2 := by
  first
  | have h : Real.log (2 : ℝ) ≤ 1 := by
      first
      | have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      first
      | convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    rw [he]
    linarith

theorem geometricDeficit_weight_bounds (n : ℕ) :
    (n : ℝ) * geometricWeight n ^ 2 / 2 ≤ geometricDeficit n ∧
      geometricDeficit n ≤ (5 / 6) * (n : ℝ) * geometricWeight n ^ 2 := by
  first
  | have h := geometricDeficit_weighted_bounds n
    rw [geometricWeight_sq]
    constructor <;> nlinarith

/-- A bound of logarithmic size on the full unbounded finite family. The
quantity on the left is the genuine exponential-kernel convolution energy. -/
theorem geometricConvolutionDeficit_lower {n : ℕ} (hn : 0 < n) :
    (6 / 25) * (n : ℝ) * geometricDeficit n ^ 2 ≤ geometricConvolutionDeficit n := by
  first
  | have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hδ := geometricDeficit_nonneg hn
    have hη := geometricConvolutionDeficit_nonneg n
    have hw := geometricWeight_nonneg hn
    have hupper := (geometricDeficit_weight_bounds n).2
    have hsq : geometricDeficit n ^ 2 ≤
        ((5 / 6) * (n : ℝ) * geometricWeight n ^ 2) ^ 2 := by
      first
      | exact (sq_le_sq₀ hδ (by positivity)).mpr hupper
    have hmass := geometricConvolution_mass_bound hn
    have hlog : 1 + (n : ℝ) * Real.log 4 ≤ 3 * n := by
      first
      | nlinarith [mul_le_mul_of_nonneg_left log_four_le_two hn0.le]
    have hηbound : ((n : ℝ) * geometricWeight n) ^ 4 ≤
        6 * n * geometricConvolutionDeficit n := by
      first
      | nlinarith [mul_le_mul_of_nonneg_right hlog hη]
    have hsquared := mul_le_mul_of_nonneg_left hsq (sq_nonneg (n : ℝ))
    have hfinal : (n : ℝ) * ((6 / 25) * n * geometricDeficit n ^ 2) ≤
        (n : ℝ) * geometricConvolutionDeficit n := by
      first
      | nlinarith
    exact Iff.mp (mul_le_mul_iff_right₀ hn0) hfinal

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/GeometricCornerMeasure.lean -/

/- BEGIN SOURCE: VolumePolynomials/GeometricCornerInterpolation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Every small deficit is attained by an explicit finite cap -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology MeasureTheory

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

@[simp] theorem geometricDeficit_one : geometricDeficit 1 = 1 / 2 := by
  first
  | norm_num [geometricDeficit, geometricGenerators, geometricNormalizer,
      rawGeometricGenerators, cornerEnergy]

/-- A first crossing, not an assumption of monotonicity, selects a finite
member for every positive deficit at most one half. -/
theorem exists_geometricDeficit_crossing {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ n : ℕ, 0 < n ∧ δ ≤ geometricDeficit n ∧ geometricDeficit (n + 1) < δ := by
  first
  | have hevent : ∀ᶠ n : ℕ in atTop, geometricDeficit n < δ :=
      (tendsto_order.mp geometricDeficit_tendsto_zero).2 δ hδ
    have hex : ∃ n : ℕ, 0 < n ∧ geometricDeficit n < δ := by
      first
      | obtain ⟨n, hn, hlt⟩ := ((eventually_ge_atTop (1 : ℕ)).and hevent).exists
        exact ⟨n, hn, hlt⟩
    let N := Nat.find hex
    have hN : 0 < N ∧ geometricDeficit N < δ := Nat.find_spec hex
    have hN1 : N ≠ 1 := by
      first
      | intro heq
        have h := hN.2
        rw [heq, geometricDeficit_one] at h
        linarith
    have hN2 : 2 ≤ N := by omega
    refine ⟨N - 1, by omega, ?_, ?_⟩
    · by_contra h
      have hp : 0 < N - 1 ∧ geometricDeficit (N - 1) < δ :=
        ⟨by omega, lt_of_not_ge h⟩
      exact Nat.find_min hex (by omega : N - 1 < Nat.find hex) hp
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hN.2

theorem logarithm_le_crossing_index {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hcross : geometricDeficit (n + 1) < δ) :
    Real.log (1 / δ) ≤ 4 * n := by
  first
  | have hA : (0 : ℝ) < 4 ^ (n + 1) := pow_pos (by norm_num) _
    have hlo : 1 / (4 : ℝ) ^ (n + 1) < δ := by
      first
      | simpa only [one_div] using
          lt_of_le_of_lt (geometricDeficit_bounds (Nat.succ_pos n)).1 hcross
    have hmul : 1 < δ * (4 : ℝ) ^ (n + 1) := (div_lt_iff₀ hA).mp hlo
    have hdiv : 1 / δ ≤ (4 : ℝ) ^ (n + 1) :=
      (div_le_iff₀ hδ).mpr (by nlinarith)
    have hlog := Real.log_le_log (div_pos (by norm_num) hδ) hdiv
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at hlog
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbound := mul_le_mul_of_nonneg_left log_four_le_two
      (by positivity : (0 : ℝ) ≤ n + 1)
    nlinarith

/-- The square-root interpolation parameter is in the entire interval `[0,1]`
and attains the desired deficit exactly. -/
theorem geometric_interpolation_parameter {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) (hδn : δ ≤ geometricDeficit n) :
    Real.sqrt (δ / geometricDeficit n) ∈ Icc (0 : ℝ) 1 ∧
      Real.sqrt (δ / geometricDeficit n) ^ 2 * geometricDeficit n = δ := by
  first
  | have hdn : 0 < geometricDeficit n := lt_of_lt_of_le hδ hδn
    have hq : 0 ≤ δ / geometricDeficit n := (div_pos hδ hdn).le
    have hq1 : δ / geometricDeficit n ≤ 1 := (div_le_one hdn).mpr hδn
    have hsquare := Real.sq_sqrt hq
    refine ⟨⟨Real.sqrt_nonneg _, ?_⟩, ?_⟩
    · nlinarith [Real.sqrt_nonneg (δ / geometricDeficit n)]
    · rw [hsquare]
      exact div_mul_cancel₀ δ hdn.ne'

/-- All positive sufficiently small deficits occur in actual finite compact
convex unit-width caps; this is not merely a sequence of finite examples. -/
theorem exists_cap_with_exact_deficit {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ (n : ℕ) (t : ℝ), 0 < n ∧ t ∈ Icc (0 : ℝ) 1 ∧
      volume.real (cap (interpolatedGenerators t (geometricGenerators n))) = 1 / 2 - δ ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤
        t ^ 4 * geometricConvolutionDeficit n := by
  first
  | obtain ⟨n, hn, hδn, hcross⟩ := exists_geometricDeficit_crossing hδ hδhalf
    let t := Real.sqrt (δ / geometricDeficit n)
    obtain ⟨ht, hscale⟩ := geometric_interpolation_parameter hδ hn hδn
    have harea : volume.real (cap (interpolatedGenerators t (geometricGenerators n))) =
        1 / 2 - δ := by
      first
      | rw [area_interpolated_cap ht (geometricGenerators_signed hn) (geometricGenerators_sum hn),
          area_geometricCap hn]
        nlinarith
    refine ⟨n, t, hn, ht, harea, ?_⟩
    have hη := mul_le_mul_of_nonneg_left (geometricConvolutionDeficit_lower hn)
      (by positivity : 0 ≤ t ^ 4)
    have hsquare : t ^ 4 * geometricDeficit n ^ 2 = δ ^ 2 := by
      first
      | have hs := congrArg (fun x : ℝ => x ^ 2) hscale
        dsimp only [t] at *
        nlinarith
    have hlog := mul_le_mul_of_nonneg_left (logarithm_le_crossing_index hδ hn hcross)
      (sq_nonneg δ)
    nlinarith

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/GeometricCornerInterpolation.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteCapLowerWitness.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # A continuous range of actual finite caps with a logarithmic interaction gap

All sets and areas in the theorem are literal convex sets and Lebesgue areas.
Identification of the interaction cap with the mixed-volume functional remains
the distinct geometric assertion of Proposition 4.3.
-/

noncomputable section
open Set MeasureTheory
open scoped NNReal MeasureTheory

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

theorem edgeWeight_smul (t : ℝ≥0) {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    edgeWeight ((t : ℝ) • v) = t * edgeWeight v := by
  first
  | apply NNReal.eq
    change Real.sqrt ((t * v.1) * (-(t * v.2))) =
      (t : ℝ) * Real.sqrt (v.1 * (-v.2))
    rw [show (t * v.1) * (-(t * v.2)) =
      (t : ℝ) ^ 2 * (v.1 * (-v.2)) by ring,
      Real.sqrt_mul (sq_nonneg (t : ℝ)), Real.sqrt_sq t.coe_nonneg]

theorem edgeMeasure_pos_smul (t : ℝ≥0) (ht : t ≠ 0) {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    edgeMeasure ((t : ℝ) • v) = t • edgeMeasure v := by
  first
  | have htpos : (0 : ℝ) < t := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
    rw [edgeMeasure, edgeWeight_smul t hv, edgeSlope_pos_smul htpos, mul_smul]
    rfl

theorem cornerMeasure_pos_smul (t : ℝ≥0) (ht : t ≠ 0) {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerMeasure (vs.map (fun v => (t : ℝ) • v)) = t • cornerMeasure vs := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih =>
        rw [List.map_cons, cornerMeasure, cornerMeasure,
          ih (fun w hw => hv w (List.mem_cons_of_mem v hw)),
          edgeMeasure_pos_smul t ht (hv v List.mem_cons_self), smul_add]

theorem cornerMeasure_interpolated {t : ℝ} (ht : 0 < t) {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerMeasure (interpolatedGenerators t vs) =
      (NNReal.mk t ht.le) • cornerMeasure vs := by
  first
  | have htne : (NNReal.mk t ht.le) ≠ 0 := by
      first
      | intro h
        have he := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
        exact ht.ne' he
    simp only [interpolatedGenerators, cornerMeasure]
    have hhorizontal : edgeMeasure (1 - t, 0) = 0 := by simp [edgeMeasure, edgeWeight]
    have hvertical : edgeMeasure (0, -(1 - t)) = 0 := by simp [edgeMeasure, edgeWeight]
    rw [hhorizontal, hvertical, add_zero, add_zero]
    exact cornerMeasure_pos_smul (NNReal.mk t ht.le) htne hv

theorem cornerMean_nnreal_smul (t : ℝ≥0) (μ : Measure ℝ) :
    cornerMean (t • μ) = (t : ℝ) • cornerMean μ := by
  first
  | simp only [cornerMean, integral_smul_nnreal_measure, NNReal.smul_def]

theorem self_convolution_energy_nnreal_smul (t : ℝ≥0)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖cornerMean ((t • μ) ∗ (t • μ))‖ ^ 2 =
      (t : ℝ) ^ 4 * ‖cornerMean (μ ∗ μ)‖ ^ 2 := by
  first
  | rw [conv_nnreal_smul, cornerMean_nnreal_smul, norm_smul]
    simp only [NNReal.coe_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg t.coe_nonneg t.coe_nonneg)]
    ring

theorem area_interpolated_self_interaction {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    volume.real (cap (interactionGenerators
      (interpolatedGenerators t (geometricGenerators n))
      (interpolatedGenerators t (geometricGenerators n)))) =
        1 / 2 - t ^ 4 * geometricConvolutionDeficit n := by
  first
  | rw [area_self_interaction_cap
        (interpolatedGenerators_signed ⟨ht.1.le, ht.2⟩ (geometricGenerators_signed hn))
        (interpolatedGenerators_sum t (geometricGenerators_sum hn)),
      cornerMeasure_interpolated ht.1 (geometricGenerators_signed hn),
      self_convolution_energy_nnreal_smul]
    dsimp only [geometricConvolutionDeficit, NNReal.coe_mk]
    ring

/-- A full interval of target deficits, with a single positive absolute lower
constant. Both the input and interaction are explicit finite caps. -/
theorem finite_caps_logarithmic_lower_gap {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ vs : List Plane,
      (∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) ∧ vs.sum = (1, -1) ∧
      volume.real (cap vs) = 1 / 2 - δ ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤
        1 / 2 - volume.real (cap (interactionGenerators vs vs)) := by
  first
  | obtain ⟨n, hn, hδn, hcross⟩ := exists_geometricDeficit_crossing hδ hδhalf
    let t := Real.sqrt (δ / geometricDeficit n)
    have hdn : 0 < geometricDeficit n := lt_of_lt_of_le hδ hδn
    have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hδ hdn)
    obtain ⟨ht, hscale⟩ := geometric_interpolation_parameter hδ hn hδn
    refine ⟨interpolatedGenerators t (geometricGenerators n),
      interpolatedGenerators_signed ht (geometricGenerators_signed hn),
      interpolatedGenerators_sum t (geometricGenerators_sum hn), ?_, ?_⟩
    · rw [area_interpolated_cap ht (geometricGenerators_signed hn) (geometricGenerators_sum hn),
        area_geometricCap hn]
      nlinarith
    · rw [area_interpolated_self_interaction hn ⟨htpos, ht.2⟩]
      have hη := mul_le_mul_of_nonneg_left (geometricConvolutionDeficit_lower hn)
        (by positivity : 0 ≤ t ^ 4)
      have hsquare : t ^ 4 * geometricDeficit n ^ 2 = δ ^ 2 := by
        first
        | have hs := congrArg (fun x : ℝ => x ^ 2) hscale
          dsimp only [t] at *
          nlinarith
      have hlog := mul_le_mul_of_nonneg_left (logarithm_le_crossing_index hδ hn hcross)
        (sq_nonneg δ)
      nlinarith

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteCapLowerWitness.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteRepresentedPolygons.lean -/
section
/-
The active-constraint proof is generalized from
vendor/openai-math/ProjectionVolume/FiniteVertices.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, already vendored in this project.
Released under the Apache License 2.0; see vendor/openai-math/LICENSE.
The generalization removes unit-normal, distinctness and strict-interior
assumptions, retaining the same finite active-pattern argument.
-/


@[expose] public section
set_option autoImplicit false

/-! # Finite edge representations give actual polygons

An extreme point of a finite system of linear inequalities is determined by
its active constraints, even when the system has empty interior. This proves
that the compact Minkowski summands used in the edge construction are finite
convex hulls. No polygonality of an erosion is assumed.
-/

noncomputable section
open Set MeasureTheory Filter Metric Module
open scoped Topology Pointwise BigOperators RealInnerProductSpace

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def finiteInequalities {ι : Type*} (l : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i, l i x ≤ b i}

theorem finiteInequalities_extreme_unique {ι : Type*} [Fintype ι]
    (l : ι → E →L[ℝ] ℝ) (b : ι → ℝ) {x y : E}
    (hx : x ∈ (finiteInequalities l b).extremePoints ℝ)
    (ha : ∀ i, l i x = b i → l i y = b i) : y = x := by
  first
  | classical
    exact PolyhedralSupport.extreme_active_unique l b hx ha

theorem compact_finiteInequalities_isFiniteHull {ι : Type*} [Fintype ι]
    (l : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (hc : IsCompact (finiteInequalities l b)) :
    IsFiniteHull (finiteInequalities l b) := by
  first
  | classical
    let active (x : E) : Finset ι := Finset.univ.filter (fun i => l i x = b i)
    have hinj : Set.InjOn active ((finiteInequalities l b).extremePoints ℝ) := by
      first
      | intro x hx y _ hxy
        apply (finiteInequalities_extreme_unique l b hx ?_).symm
        intro i hix
        have hm : i ∈ active x := by simp [active, hix]
        rw [hxy] at hm
        exact (Finset.mem_filter.mp hm).2
    have hfinite : ((finiteInequalities l b).extremePoints ℝ).Finite :=
      (Set.toFinite (Set.univ : Set (Finset ι))).of_injOn (fun _ _ => Set.mem_univ _) hinj
    have hconv : Convex ℝ (finiteInequalities l b) := by
      first
      | simp only [finiteInequalities, Set.ofPred_forall]
        exact convex_iInter (fun i => (convex_Iic (b i)).linear_preimage (l i).toLinearMap)
    refine ⟨_, hfinite, ?_⟩
    have h := closure_convexHull_extremePoints hc hconv
    rw [hfinite.isClosed_convexHull ℝ |>.closure_eq] at h
    exact h.symm

/-- A compact convex summand of a full-dimensional polytope is a polytope.
The summand itself may have arbitrary affine dimension. -/
theorem finiteHull_of_fullDimensional_sum (Q R : ConvexBody E)
    (hpoly : IsFiniteHull ((Q + R : ConvexBody E) : Set E))
    (hint : (interior ((Q + R : ConvexBody E) : Set E)).Nonempty) : IsFiniteHull (Q : Set E) := by
  first
  | let T : E ≃L[ℝ] Euclidean (finrank ℝ E) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    have hmap := hpoly.linear_image T.toLinearMap
    have himage : (interior (T '' ((Q + R : ConvexBody E) : Set E))).Nonempty := by
      first
      | have hi : T '' interior ((Q + R : ConvexBody E) : Set E) =
            interior (T '' ((Q + R : ConvexBody E) : Set E)) := by
          simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using
            T.toHomeomorph.image_interior ((Q + R : ConvexBody E) : Set E)
        rw [← hi]
        exact hint.image T
    obtain ⟨m, P, hP⟩ := hmap.has_halfspaces himage
    let l : Fin m → E →L[ℝ] ℝ := fun i => (innerSL ℝ (P.normal i)).comp T.toContinuousLinearMap
    have hC (x : E) : x ∈ Q + R ↔ ∀ i, l i x ≤ P.offset i := by
      first
      | change x ∈ (Q + R : ConvexBody E) ↔ T x ∈ P.body
        rw [hP]
        constructor
        · exact fun hx => ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, hxy⟩
          exact T.injective hxy ▸ hy
    have heq : (Q : Set E) = finiteInequalities l
        (fun i => P.offset i - SupportGeometry.support (R : Set E) (l i)) := by
      first
      | ext x
        constructor
        · intro hx i
          obtain ⟨r, hr, hmax⟩ := SupportGeometry.exists_support R.isCompact R.nonempty (l i)
          have h := (hC (x + r)).mp (Set.mem_add.mpr ⟨x, hx, r, hr, rfl⟩) i
          rw [map_add, hmax] at h
          linarith
        · intro hx
          apply Iff.mpr (BodySupport.mem_iff_le_support Q)
          intro f
          obtain ⟨r, hr, hmax⟩ := SupportGeometry.exists_support R.isCompact R.nonempty f
          have hxr : x + r ∈ Q + R := (hC (x + r)).mpr (fun i => by
            have hi := hx i
            have hs := SupportGeometry.le_support R.isCompact (l i) hr
            rw [map_add]
            linarith)
          have hs := SupportGeometry.le_support (Q + R).isCompact f hxr
          change f (x + r) ≤ SupportGeometry.support ((Q : Set E) + (R : Set E)) f at hs
          rw [map_add, hmax, SupportGeometry.support_add Q.isCompact Q.nonempty R.isCompact R.nonempty] at hs
          change f x ≤ SupportGeometry.support (Q : Set E) f
          linarith
    rw [heq]
    apply compact_finiteInequalities_isFiniteHull
    rw [← heq]
    exact Q.isCompact

end VolumePolynomials.PolytopeGeometry

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarInteraction PolytopeGeometry OAI.Paper092

theorem triangleSum_finiteHull {ι : Type*} [Fintype ι] (e : ι → Plane) :
    IsFiniteHull (triangleSum e : Set Plane) := by
  first
  | rw [triangleSum, coe_sum_body]
    exact IsFiniteHull.sum Finset.univ (fun i => (triangleFromEdge (e i) : Set Plane))
      (fun i _ => rightTriangle_finiteHull _ _)

theorem finiteHull_translateBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (v : E) (hK : IsFiniteHull (K : Set E)) :
    IsFiniteHull (translateBody v K : Set E) := (IsFiniteHull.singleton v).add hK

theorem interior_nonempty_of_area_pos (K : ConvexBody Plane)
    (ha : 0 < volume.real (K : Set Plane)) : (interior (K : Set Plane)).Nonempty := by
  first
  | by_contra hn
    have hempty := Set.not_nonempty_iff_eq_empty.mp hn
    have hzero := K.convex.addHaar_frontier (volume : Measure Plane)
    rw [frontier, K.isClosed.closure_eq, hempty, Set.diff_empty] at hzero
    rw [measureReal_def, hzero, ENNReal.toReal_zero] at ha
    exact lt_irrefl 0 ha

/-- Every unit-width body with an actual finite mixed-area representation
is a finite convex hull, including degenerate cases. -/
theorem Represents.finiteHull_of_unit_widths {ι : Type*} [Fintype ι]
    {Q : ConvexBody Plane} {e : ι → Plane} (hQ : Represents Q e)
    (hw : width Q = 1) (hh : height Q = 1) : IsFiniteHull (Q : Set Plane) := by
  first
  | obtain ⟨v, hv⟩ := hQ.triangleSum_eq_translate
    have hrect : boundingRectangle Q = unitSquare := by
      first
      | simp only [boundingRectangle, hw, hh, one_smul, unitSquare]
    rw [hrect] at hv
    have hpoly := finiteHull_translateBody (triangleSum e) (-v) (triangleSum_finiteHull e)
    rw [hv, translateBody_translate, neg_add_cancel, translateBody_zero] at hpoly
    have harea : 0 < volume.real ((Q + unitSquare : ConvexBody Plane) : Set Plane) := by
      first
      | rw [area_add volume plane_finrank, unitSquare_area]
        have hQarea : 0 ≤ volume.real (Q : Set Plane) := measureReal_nonneg
        have hmix := mixedArea_nonnegative volume Q unitSquare
        linarith
    exact finiteHull_of_fullDimensional_sum Q unitSquare hpoly (interior_nonempty_of_area_pos _ harea)

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 25
end -- closes the original EOF section from source line 14
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteRepresentedPolygons.lean -/

/- BEGIN SOURCE: VolumePolynomials/LowerInteractionWitness.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Actual mixed-volume witnesses for the logarithmic lower gap

A finite decreasing chain is closed by its diagonal edge. The balanced-edge
construction produces an actual body with that finite mixed-area
representation. Its interaction body is therefore identified by Proposition
4.3, and its area is exactly the finite convolution energy used in Section 5.3.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped Topology Pointwise BigOperators ComplexConjugate NNReal

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092
open HalfZonotope

def closedChainEdges (vs : List Plane) : Sum (Fin vs.length) (Fin 1) → Plane :=
  Sum.elim vs.get (fun _ => (-1, 1))

theorem sum_get_map {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  first
  | rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

theorem closedChainEdges_balanced {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hs : vs.sum = (1, -1)) :
    (∑ i, max (closedChainEdges vs i).1 0) = 1 ∧
    (∑ i, max (-(closedChainEdges vs i).1) 0) = 1 ∧
    (∑ i, max (closedChainEdges vs i).2 0) = 1 ∧
    (∑ i, max (-(closedChainEdges vs i).2) 0) = 1 := by
  first
  | have hx (i : Fin vs.length) : 0 ≤ (vs.get i).1 := (hv _ (List.get_mem _ _)).1
    have hy (i : Fin vs.length) : (vs.get i).2 ≤ 0 := (hv _ (List.get_mem _ _)).2
    have hsum : (∑ i : Fin vs.length, vs.get i) = vs.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    have hsx : (∑ i : Fin vs.length, (vs.get i).1) = 1 := by
      rw [← Prod.fst_sum, hsum, hs]
    have hsy : (∑ i : Fin vs.length, (vs.get i).2) = -1 := by
      rw [← Prod.snd_sum, hsum, hs]
    simp only [closedChainEdges, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fin.sum_univ_one, max_eq_left (hx _), max_eq_right (neg_nonpos.mpr (hx _)),
      max_eq_right (hy _), max_eq_left (neg_nonneg.mpr (hy _)), Finset.sum_const_zero,
      Finset.sum_neg_distrib, hsx, hsy]
    norm_num

theorem slopeAtom_eq_edgeMeasure {v : Plane} (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    slopeAtom v = edgeMeasure v := by
  first
  | simp only [slopeAtom, atomWeight, atomSlope, edgeMeasure, edgeWeight, edgeSlope,
      abs_of_nonneg hv.1, abs_of_nonpos hv.2]

theorem cornerAtom_decreasing {v : Plane} (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (i j : Fin 2) :
    cornerAtom v i j = if i = 0 ∧ j = 1 then edgeMeasure v else 0 := by
  first
  | by_cases hx : v.1 = 0
    · rw [cornerAtom_axis (Or.inl hx)]
      simp [edgeMeasure, edgeWeight, hx]
    by_cases hy : v.2 = 0
    · rw [cornerAtom_axis (Or.inr hy)]
      simp [edgeMeasure, edgeWeight, hy]
    have hyneg : v.2 < 0 := lt_of_le_of_ne hv.2 hy
    simp only [cornerAtom, signIndex, if_pos hv.1, if_neg (not_le_of_gt hyneg),
      slopeAtom_eq_edgeMeasure hv, eq_comm]

theorem cornerMeasure_eq_sum (vs : List Plane) :
    cornerMeasure vs = (vs.map edgeMeasure).sum := by
  first
  | induction vs with
    | nil => rfl
    | cons v vs ih => simp only [cornerMeasure, List.map_cons, List.sum_cons, ih, add_comm]

/-- A two-by-two matrix with zero diagonal and the specified off-diagonal entries. -/
def offDiagonalPair {α : Type*} [Zero α] (x y : α) : Matrix (Fin 2) (Fin 2) α :=
  fun i j => if i = j then 0 else if i = 0 then x else y

theorem closedChain_cornerMatrix {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerMatrix (closedChainEdges vs) =
      offDiagonalPair (cornerMeasure vs) (Measure.dirac 0) := by
  first
  | apply Matrix.ext
    intro i j
    simp only [cornerMatrix, closedChainEdges, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one]
    simp_rw [cornerAtom_decreasing (hv _ (List.get_mem _ _))]
    have hsum : (∑ k : Fin vs.length, edgeMeasure (vs.get k)) = cornerMeasure vs := by
      first
      | rw [sum_get_map, cornerMeasure_eq_sum]
    fin_cases i <;> fin_cases j <;>
      simp [cornerAtom, signIndex, slopeAtom, atomWeight, atomSlope, hsum, cornerMeasure_eq_sum,
        offDiagonalPair]

theorem closedChain_secondMoment {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    slopeSecondMoment (cornerMatrix (closedChainEdges vs)) =
      1 + ‖cornerMean (cornerMeasure vs)‖ ^ 2 := by
  first
  | letI : ∀ i j : Fin 2,
        IsFiniteMeasure (offDiagonalPair (cornerMeasure vs) (Measure.dirac 0) i j) := by
      intro i j
      unfold offDiagonalPair
      split_ifs <;> infer_instance
    rw [closedChain_cornerMatrix hv, slopeSecondMoment_eq_entry_energies]
    simp [offDiagonalPair, Fin.sum_univ_two, cornerMean, norm_cornerFeature] <;> ring

theorem matrixSecondTrace_offDiagonal_self (z : ℂ) :
    matrixSecondTrace ((offDiagonalPair z 1)ᴴ * offDiagonalPair z 1) =
      1 + Complex.normSq (z * z) := by
  first
  | simp [offDiagonalPair, matrixSecondTrace_eq_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem closedChain_interactionMoment {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    slopeInteractionMoment (cornerMatrix (closedChainEdges vs))
        (cornerMatrix (closedChainEdges vs)) =
      1 + ‖cornerMean (cornerMeasure vs ∗ cornerMeasure vs)‖ ^ 2 := by
  first
  | have hf (ξ : ℝ) : slopeFourierMatrix (cornerMatrix (closedChainEdges vs)) ξ =
        offDiagonalPair (charFun (cornerMeasure vs) ξ) 1 := by
      first
      | rw [closedChain_cornerMatrix hv]
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [slopeFourierMatrix, offDiagonalPair, charFun_apply_real]
    have htrace (ξ : ℝ) :
        matrixSecondTrace ((slopeFourierMatrix (cornerMatrix (closedChainEdges vs)) ξ)ᴴ *
          slopeFourierMatrix (cornerMatrix (closedChainEdges vs)) ξ) =
        1 + Complex.normSq (charFun (cornerMeasure vs ∗ cornerMeasure vs) ξ) := by
      first
      | rw [hf, matrixSecondTrace_offDiagonal_self, charFun_conv]
    simp only [slopeInteractionMoment, htrace]
    rw [integral_add (integrable_const 1)
      (integrable_spectral_normSq (cornerMeasure vs ∗ cornerMeasure vs)), corner_spectral_energy]
    simp

theorem closedChain_body_area {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hs : vs.sum = (1, -1))
    {B : ConvexBody Plane} (hB : Represents B (closedChainEdges vs))
    (hw : width B = 1) (hh : height B = 1) :
    volume.real (B : Set Plane) = volume.real (cap vs) := by
  first
  | have h := hB.unit_second_moment hw hh
    rw [closedChain_secondMoment hv] at h
    rw [area_unit_cap hs, cornerEnergy_eq_mean_norm hv]
    linarith

theorem closedChain_interaction_area {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hs : vs.sum = (1, -1))
    {Q : ConvexBody Plane}
    (hQ : Represents Q (completedEdges (productEdges (closedChainEdges vs) (closedChainEdges vs))))
    (hw : width Q = 1) (hh : height Q = 1) :
    volume.real (Q : Set Plane) = volume.real (cap (interactionGenerators vs vs)) := by
  first
  | have h := hQ.unit_second_moment hw hh
    rw [productEdge_secondMoment, closedChain_interactionMoment hv] at h
    rw [area_self_interaction_cap hv hs]
    linarith

/-- The lower bound in Corollary 5.3 is attained by actual inputs and their
actual three-dimensional mixed-volume interaction, for every real deficit
in the stated interval. It is not restricted to a sequence of deficits. -/
theorem logarithmic_lower_interaction_witness {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ B Q : ConvexBody Plane, width B = 1 ∧ height B = 1 ∧
      volume.real (B : Set Plane) = 1 / 2 - δ ∧ IsInteraction B B Q ∧
      (1 / 2 - δ ≤ volume.real (Q : Set Plane)) ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤ 1 / 2 - volume.real (Q : Set Plane) := by
  first
  | obtain ⟨vs, hv, hs, harea, hgap⟩ := finite_caps_logarithmic_lower_gap hδ hδhalf
    have hbal := closedChainEdges_balanced hv hs
    obtain ⟨B, hB, hBw, hBh⟩ := exists_body_of_balanced_edges (closedChainEdges vs)
      hbal.1 hbal.2.1 hbal.2.2.1 hbal.2.2.2
    obtain ⟨Q, hQw, hQh, hQV, hQa, hQrep⟩ := finite_interaction_body hB hB hBw hBh hBw hBh
    have hBa := (closedChain_body_area hv hs hB hBw hBh).trans harea
    have hQarea := closedChain_interaction_area hv hs hQrep hQw hQh
    refine ⟨B, Q, hBw, hBh, hBa, ⟨hQw, hQh, hQV⟩, ?_, ?_⟩
    · simpa only [max_self, hBa] using hQa
    · rw [hQarea]
      exact hgap

theorem logarithmic_lower_polygon_interaction_witness {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ B Q : ConvexBody Plane,
      PolytopeGeometry.IsFiniteHull (B : Set Plane) ∧
      PolytopeGeometry.IsFiniteHull (Q : Set Plane) ∧
      width B = 1 ∧ height B = 1 ∧ volume.real (B : Set Plane) = 1 / 2 - δ ∧
      IsInteraction B B Q ∧ (1 / 2 - δ ≤ volume.real (Q : Set Plane)) ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤ 1 / 2 - volume.real (Q : Set Plane) := by
  first
  | obtain ⟨vs, hv, hs, harea, hgap⟩ := finite_caps_logarithmic_lower_gap hδ hδhalf
    have hbal := closedChainEdges_balanced hv hs
    obtain ⟨B, hB, hBw, hBh⟩ := exists_body_of_balanced_edges (closedChainEdges vs)
      hbal.1 hbal.2.1 hbal.2.2.1 hbal.2.2.2
    obtain ⟨Q, hQw, hQh, hQV, hQa, hQrep⟩ := finite_interaction_body hB hB hBw hBh hBw hBh
    have hBa := (closedChain_body_area hv hs hB hBw hBh).trans harea
    have hQarea := closedChain_interaction_area hv hs hQrep hQw hQh
    refine ⟨B, Q, hB.finiteHull_of_unit_widths hBw hBh,
      hQrep.finiteHull_of_unit_widths hQw hQh, hBw, hBh, hBa,
      ⟨hQw, hQh, hQV⟩, ?_, ?_⟩
    · simpa only [max_self, hBa] using hQa
    · rw [hQarea]
      exact hgap

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/LowerInteractionWitness.lean -/

/- BEGIN SOURCE: VolumePolynomials/ThresholdScalar.lean -/
section


@[expose] public section

/-!
# Exact scalar optimization in the logarithmic slice

These are identities and inequalities in real numbers used in equations (5.7)
and (5.8) of the supplied paper. Their assumptions are stated explicitly; no
geometric statement about mixed volumes is built into their definitions.
-/

namespace VolumePolynomials

/-- The larger root used in Section 5.4. -/
noncomputable def comparisonRoot (s : ℝ) : ℝ :=
  (1 + s + Real.sqrt (1 + s ^ 2)) / 2

/-- The comparison area deficit. -/
noncomputable def comparisonDeficit (s : ℝ) : ℝ :=
  s / (4 * comparisonRoot s ^ 2)

/-- The scalar lower bound after normalizing the three planar bodies. -/
noncomputable def sliceLowerBound (s δ η : ℝ) : ℝ :=
  (1 + s - Real.sqrt (4 * s * δ * (1 + 2 * η))) / (1 - 2 * δ)

theorem comparisonRoot_quadratic (s : ℝ) :
    comparisonRoot s ^ 2 - (1 + s) * comparisonRoot s + s / 2 = 0 := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  dsimp [comparisonRoot]
  nlinarith

theorem comparisonRoot_ge_one {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ comparisonRoot s := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  have hnonneg := Real.sqrt_nonneg (1 + s ^ 2)
  have hge : 1 ≤ Real.sqrt (1 + s ^ 2) := by nlinarith [sq_nonneg s]
  dsimp [comparisonRoot]
  linarith

theorem comparisonRoot_pos {s : ℝ} (hs : 0 ≤ s) :
    0 < comparisonRoot s := lt_of_lt_of_le zero_lt_one (comparisonRoot_ge_one hs)

theorem comparisonRoot_le_one_add {s : ℝ} (hs : 0 ≤ s) :
    comparisonRoot s ≤ 1 + s := by
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ 1 + s := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith
  dsimp [comparisonRoot]
  linarith

theorem comparisonDeficit_pos {s : ℝ} (hs : 0 < s) :
    0 < comparisonDeficit s := by
  dsimp [comparisonDeficit]
  exact div_pos hs (mul_pos (by norm_num) (sq_pos_of_pos (comparisonRoot_pos hs.le)))

theorem comparisonDeficit_le_quarter {s : ℝ} (hs : 0 ≤ s) :
    comparisonDeficit s ≤ s / 4 := by
  have hr := comparisonRoot_ge_one hs
  have hr2 : 1 ≤ comparisonRoot s ^ 2 := by nlinarith
  dsimp [comparisonDeficit]
  apply div_le_div_of_nonneg_left hs (by norm_num)
  nlinarith

theorem comparisonDeficit_ge_sixteenth {s : ℝ} (hs : 0 ≤ s) (hsle : s ≤ 1) :
    s / 16 ≤ comparisonDeficit s := by
  have hrpos := comparisonRoot_pos hs
  have hr := comparisonRoot_le_one_add hs
  have hr2 : comparisonRoot s ^ 2 ≤ 4 := by nlinarith
  dsimp [comparisonDeficit]
  apply div_le_div_of_nonneg_left hs (by positivity)
  nlinarith

/-- The completed square in (5.8). -/
theorem comparison_completed_square {s r δ : ℝ} (hr : r ≠ 0) :
    (s / (2 * r) + 2 * r * δ) ^ 2 - 4 * s * δ =
      4 * r ^ 2 * (δ - s / (4 * r ^ 2)) ^ 2 := by
  field_simp [hr]
  ring

/-- The exact gap expression, prior to any square-root estimate. -/
theorem root_sub_sliceLowerBound {s r δ η : ℝ}
    (hr : r ≠ 0) (hδ : 1 - 2 * δ ≠ 0)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0) :
    r - sliceLowerBound s δ η =
      (Real.sqrt (4 * s * δ * (1 + 2 * η)) -
        (s / (2 * r) + 2 * r * δ)) / (1 - 2 * δ) := by
  have hbase : s / (2 * r) = 1 + s - r := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hr)).mpr
    nlinarith [hroot]
  dsimp [sliceLowerBound]
  apply (eq_div_iff hδ).mpr
  rw [sub_mul, div_mul_cancel₀ _ hδ, hbase]
  ring

/-- With zero interaction deficit, the comparison value is a lower bound. -/
theorem comparison_le_sliceLowerBound_zero {s r δ : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0) :
    r ≤ sliceLowerBound s δ 0 := by
  have hden : 0 < 1 - 2 * δ := by linarith
  have hw : 0 ≤ s / (2 * r) + 2 * r * δ := by positivity
  have hcomplete := comparison_completed_square (s := s) (δ := δ) hr.ne'
  have hupper : Real.sqrt (4 * s * δ) ≤ s / (2 * r) + 2 * r * δ := by
    apply (Real.sqrt_le_left hw).mpr
    have hnonneg : 0 ≤ 4 * r ^ 2 * (δ - s / (4 * r ^ 2)) ^ 2 := by positivity
    linarith
  have heq := root_sub_sliceLowerBound (s := s) (r := r) (δ := δ) (η := 0)
    hr.ne' hden.ne' hroot
  simp only [mul_zero, add_zero, mul_one] at heq
  have : r - sliceLowerBound s δ 0 ≤ 0 := by
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hupper) hden.le
  linarith

/-- An improving candidate must have positive interaction deficit. -/
theorem positive_interaction_of_improvement {s r δ η : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0)
    (himprove : sliceLowerBound s δ η < r) : 0 < η := by
  by_contra hn
  have hη : η ≤ 0 := le_of_not_gt hn
  have hden : 0 < 1 - 2 * δ := by linarith
  have hprod : 4 * s * δ * (1 + 2 * η) ≤ 4 * s * δ := by
    have hterm : s * δ * η ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs hδ) hη
    nlinarith
  have hmono := Real.sqrt_le_sqrt hprod
  have hbound : sliceLowerBound s δ 0 ≤ sliceLowerBound s δ η := by
    dsimp [sliceLowerBound]
    simp only [mul_zero, add_zero, mul_one]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  exact (not_lt_of_ge ((comparison_le_sliceLowerBound_zero hs hr hδ hδlt hroot).trans
    hbound)) himprove

/-- The exact localization inequality in the proof of Theorem 5.5. -/
theorem completed_square_lt_of_improvement {s r δ η : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0)
    (himprove : sliceLowerBound s δ η < r) :
    (δ - s / (4 * r ^ 2)) ^ 2 < 8 * (s / (4 * r ^ 2)) * δ * η := by
  have hη := positive_interaction_of_improvement hs hr hδ hδlt hroot himprove
  have hden : 0 < 1 - 2 * δ := by linarith
  have heq := root_sub_sliceLowerBound hr.ne' hden.ne' hroot (η := η)
  have hgap : 0 < Real.sqrt (4 * s * δ * (1 + 2 * η)) -
      (s / (2 * r) + 2 * r * δ) := by
    exact (div_pos_iff_of_pos_right hden).mp (by rw [← heq]; linarith)
  have hw : 0 ≤ s / (2 * r) + 2 * r * δ := by positivity
  have hsqrt := Real.sq_sqrt
    (show 0 ≤ 4 * s * δ * (1 + 2 * η) by positivity)
  have hsquare : (s / (2 * r) + 2 * r * δ) ^ 2 <
      4 * s * δ * (1 + 2 * η) := by
    nlinarith [Real.sqrt_nonneg (4 * s * δ * (1 + 2 * η))]
  have hcomplete := comparison_completed_square (s := s) (δ := δ) hr.ne'
  have hscaled : 4 * r ^ 2 * (δ - s / (4 * r ^ 2)) ^ 2 < 8 * s * δ * η := by
    nlinarith [hsquare, hcomplete]
  apply (mul_lt_mul_iff_right₀ (show 0 < 4 * r ^ 2 by positivity)).mp
  calc
    (4 * r ^ 2) * (δ - s / (4 * r ^ 2)) ^ 2
        < 8 * s * δ * η := hscaled
    _ = (4 * r ^ 2) * (8 * (s / (4 * r ^ 2)) * δ * η) := by
      field_simp [hr.ne']

/-- A purely scalar form of the small-deficit localization. -/
theorem deficit_lt_twice_reference {δ η t : ℝ}
    (hδ : 0 < δ) (ht : 0 ≤ t) (htsmall : t < 1 / 32)
    (hη : η ≤ δ) (hsquare : (δ - t) ^ 2 < 8 * t * δ * η) :
    δ < 2 * t := by
  by_contra hn
  have hhalf : δ / 2 ≤ δ - t := by linarith
  have hnonneg : 0 ≤ δ - t := by linarith
  have hlower : δ ^ 2 / 4 ≤ (δ - t) ^ 2 := by nlinarith
  have hprod : δ * η ≤ δ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hη hδ.le]
  have hupper : 8 * t * δ * η ≤ (8 * t) * δ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8 * t by positivity)
    nlinarith
  have hstrict : (8 * t) * δ ^ 2 < δ ^ 2 / 4 := by
    have := mul_lt_mul_of_pos_right (show 8 * t < 1 / 4 by linarith) (sq_pos_of_pos hδ)
    nlinarith
  linarith

/-- Every scalar candidate improving the reference curve lies in the small
deficit regime needed for the logarithmic energy estimate. -/
theorem improving_deficit_localization {s δ η : ℝ}
    (hs : 0 < s) (hssmall : s < 1 / 8)
    (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2) (hηδ : η ≤ δ)
    (himprove : sliceLowerBound s δ η < comparisonRoot s) :
    0 < δ ∧ 0 < η ∧ δ < 2 * comparisonDeficit s ∧ δ ≤ s / 2 := by
  have hr := comparisonRoot_pos hs.le
  have hroot := comparisonRoot_quadratic s
  have hη := positive_interaction_of_improvement hs.le hr hδ hδlt hroot himprove
  have hsq := completed_square_lt_of_improvement hs.le hr hδ hδlt hroot himprove
  change (δ - comparisonDeficit s) ^ 2 < 8 * comparisonDeficit s * δ * η at hsq
  have hδpos : 0 < δ := lt_of_lt_of_le hη hηδ
  have htpos := comparisonDeficit_pos hs
  have htbound := comparisonDeficit_le_quarter hs.le
  have htsmall : comparisonDeficit s < 1 / 32 := by linarith
  have hlocal := deficit_lt_twice_reference hδpos htpos.le htsmall hηδ hsq
  exact ⟨hδpos, hη, hlocal, by linarith⟩

/-- The square root appearing at the exact comparison deficit. -/
theorem sqrt_at_comparisonDeficit {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (4 * s * comparisonDeficit s) = s / comparisonRoot s := by
  have hr := comparisonRoot_pos hs
  apply (Real.sqrt_eq_iff_eq_sq (by
    have hδ : 0 ≤ comparisonDeficit s := by
      dsimp [comparisonDeficit]
      positivity
    positivity) (by positivity)).mpr
  dsimp [comparisonDeficit]
  field_simp [hr.ne']

/-- The algebraic reference minimum is attained at exactly the stated deficit. -/
theorem sliceLowerBound_at_comparisonDeficit {s : ℝ}
    (hs : 0 ≤ s) (hslt : s < 1) :
    sliceLowerBound s (comparisonDeficit s) 0 = comparisonRoot s := by
  have hr := comparisonRoot_pos hs
  have hδ := comparisonDeficit_le_quarter hs
  have hden : 1 - 2 * comparisonDeficit s ≠ 0 := by linarith
  have heq := root_sub_sliceLowerBound (s := s) (r := comparisonRoot s)
    (δ := comparisonDeficit s) (η := 0) hr.ne' hden (comparisonRoot_quadratic s)
  simp only [mul_zero, add_zero, mul_one, sqrt_at_comparisonDeficit hs] at heq
  have hz : s / comparisonRoot s -
      (s / (2 * comparisonRoot s) + 2 * comparisonRoot s * comparisonDeficit s) = 0 := by
    dsimp [comparisonDeficit]
    field_simp [hr.ne']
    ring
  rw [hz, zero_div] at heq
  linarith

/-- The exact improvement at the algebraic comparison deficit. -/
theorem root_sub_sliceLowerBound_at_comparisonDeficit {s η : ℝ}
    (hs : 0 ≤ s) (hslt : s < 1) :
    comparisonRoot s - sliceLowerBound s (comparisonDeficit s) η =
      (s / comparisonRoot s) * (Real.sqrt (1 + 2 * η) - 1) /
        (1 - 2 * comparisonDeficit s) := by
  have hr := comparisonRoot_pos hs
  have hδnonneg : 0 ≤ comparisonDeficit s := by
    dsimp [comparisonDeficit]
    positivity
  have hδ := comparisonDeficit_le_quarter hs
  have hden : 1 - 2 * comparisonDeficit s ≠ 0 := by linarith
  rw [root_sub_sliceLowerBound hr.ne' hden (comparisonRoot_quadratic s),
    Real.sqrt_mul (by positivity), sqrt_at_comparisonDeficit hs]
  congr 1
  dsimp [comparisonDeficit]
  field_simp [hr.ne']
  ring

theorem sqrt_one_add_twice_sub_one_upper {η : ℝ} (hη : 0 ≤ η) :
    Real.sqrt (1 + 2 * η) - 1 ≤ η := by
  have hupper : Real.sqrt (1 + 2 * η) ≤ 1 + η := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith [sq_nonneg η]
  linarith

theorem sqrt_one_add_twice_sub_one_lower {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ 1) :
    η / 2 ≤ Real.sqrt (1 + 2 * η) - 1 := by
  have hlower : 1 + η / 2 ≤ Real.sqrt (1 + 2 * η) := by
    apply (Real.le_sqrt (by linarith) (by linarith)).mpr
    nlinarith [mul_nonneg hη (show 0 ≤ 1 - η by linarith)]
  linarith

/-- The improvement at the reference deficit is uniformly comparable to `s*η`.
Both constants are explicit. -/
theorem reference_improvement_bounds {s η : ℝ}
    (hs : 0 ≤ s) (hsle : s ≤ 1 / 2) (hη : 0 ≤ η) (hηle : η ≤ 1) :
    s * η / 4 ≤ comparisonRoot s - sliceLowerBound s (comparisonDeficit s) η ∧
    comparisonRoot s - sliceLowerBound s (comparisonDeficit s) η ≤ 2 * s * η := by
  have hrpos := comparisonRoot_pos hs
  have hrlo := comparisonRoot_ge_one hs
  have hrhi : comparisonRoot s ≤ 2 := by
    have := comparisonRoot_le_one_add hs
    linarith
  have hδnonneg : 0 ≤ comparisonDeficit s := by
    dsimp [comparisonDeficit]
    positivity
  have hδhi := comparisonDeficit_le_quarter hs
  have hdenlo : 1 / 2 ≤ 1 - 2 * comparisonDeficit s := by linarith
  have hdenhi : 1 - 2 * comparisonDeficit s ≤ 1 := by linarith
  have hdenpos : 0 < 1 - 2 * comparisonDeficit s := by linarith
  have hratio_lo : s / 2 ≤ s / comparisonRoot s :=
    div_le_div_of_nonneg_left hs hrpos hrhi
  have hratio_hi : s / comparisonRoot s ≤ s := by
    simpa using div_le_div_of_nonneg_left hs (show (0 : ℝ) < 1 by norm_num) hrlo
  have hglo := sqrt_one_add_twice_sub_one_lower hη hηle
  have hghi := sqrt_one_add_twice_sub_one_upper hη
  have hgpos : 0 ≤ Real.sqrt (1 + 2 * η) - 1 := by linarith
  rw [root_sub_sliceLowerBound_at_comparisonDeficit hs (by linarith)]
  constructor
  · apply (le_div_iff₀ hdenpos).mpr
    have hprod := mul_le_mul hratio_lo hglo (show 0 ≤ η / 2 by positivity)
      (show 0 ≤ s / comparisonRoot s by positivity)
    have hscale := mul_le_mul_of_nonneg_left hdenhi (show 0 ≤ s * η / 4 by positivity)
    nlinarith
  · apply (div_le_iff₀ hdenpos).mpr
    have hprod := mul_le_mul hratio_hi hghi hgpos hs
    have hscale := mul_le_mul_of_nonneg_left hdenlo (show 0 ≤ 2 * s * η by positivity)
    nlinarith

/-- After localization, every improvement is bounded above by `4*s*η`. -/
theorem improvement_le_four_mul {s δ η : ℝ}
    (hs : 0 < s) (hssmall : s < 1 / 8)
    (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2) (hηδ : η ≤ δ)
    (himprove : sliceLowerBound s δ η < comparisonRoot s) :
    comparisonRoot s - sliceLowerBound s δ η ≤ 4 * s * η := by
  obtain ⟨hδpos, hηpos, hlocal, hδbound⟩ :=
    improving_deficit_localization hs hssmall hδ hδlt hηδ himprove
  have hr := comparisonRoot_pos hs.le
  have hden : 0 < 1 - 2 * δ := by linarith
  have hdenhalf : 1 / 2 ≤ 1 - 2 * δ := by linarith
  have hvpos : 0 ≤ 4 * s * δ := by positivity
  have hrootupper : Real.sqrt (4 * s * δ) ≤ 2 * s := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδbound hs.le]
  have hw : 0 ≤ s / (2 * comparisonRoot s) + 2 * comparisonRoot s * δ := by positivity
  have hcomplete := comparison_completed_square (s := s) (δ := δ) hr.ne'
  have hrootle : Real.sqrt (4 * s * δ) ≤
      s / (2 * comparisonRoot s) + 2 * comparisonRoot s * δ := by
    apply (Real.sqrt_le_left hw).mpr
    have hnonneg : 0 ≤ 4 * comparisonRoot s ^ 2 *
        (δ - s / (4 * comparisonRoot s ^ 2)) ^ 2 := by positivity
    linarith
  rw [root_sub_sliceLowerBound hr.ne' hden.ne' (comparisonRoot_quadratic s),
    Real.sqrt_mul hvpos]
  apply (div_le_iff₀ hden).mpr
  have hnum : Real.sqrt (4 * s * δ) * Real.sqrt (1 + 2 * η) -
      (s / (2 * comparisonRoot s) + 2 * comparisonRoot s * δ) ≤ 2 * s * η := by
    calc
      _ ≤ Real.sqrt (4 * s * δ) * (Real.sqrt (1 + 2 * η) - 1) := by nlinarith
      _ ≤ Real.sqrt (4 * s * δ) * η :=
        mul_le_mul_of_nonneg_left (sqrt_one_add_twice_sub_one_upper hηpos.le)
          (Real.sqrt_nonneg _)
      _ ≤ 2 * s * η := mul_le_mul_of_nonneg_right hrootupper hηpos.le
  have hscale := mul_le_mul_of_nonneg_left hdenhalf (show 0 ≤ 4 * s * η by positivity)
  nlinarith

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ThresholdScalar.lean -/

/- BEGIN SOURCE: VolumePolynomials/GeometricThreshold.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The geometric estimates in Theorem 5.5

The upper estimate allows the averaged body in the higher-dimensional lift:
its area may exceed `2*s*T`. The lower estimate constructs actual planar
bodies and the exact attaining optimizer. All mixed areas and mixed volumes
are the coefficient functionals of their actual Lebesgue volume polynomials.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem IsInteraction.area_ge_inputs {B C Q : ConvexBody Plane}
    (hQ : IsInteraction B C Q)
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | obtain ⟨R, hR, hRa⟩ := proposition_4_3 B C hBw hBh hCw hCh
    rwa [interaction_area_unique hR hQ] at hRa

theorem geometric_slice_lower_bound {A Q : ConvexBody Plane} {s T z : ℝ}
    (hs : 0 < s) (hT : 0 < T)
    (hAw : width A = 1) (hAh : height A = s)
    (hAa : 2 * s * T ≤ volume.real (A : Set Plane))
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hz : 2 * T * z = 2 * mixedArea volume A Q) :
    T ≤ 1 / 2 ∧
      sliceLowerBound s (1 / 2 - T) (1 / 2 - volume.real (Q : Set Plane)) ≤ z := by
  first
  | have hAupper := area_le_width_mul_height A
    rw [hAw, hAh, one_mul] at hAupper
    have hThalf : T ≤ 1 / 2 := by nlinarith
    have hQupper := area_le_width_mul_height Q
    rw [hQw, hQh, one_mul] at hQupper
    have hcorner := mixedArea_corner_inequality A Q
    rw [hAw, hAh, hQw, hQh, one_mul, mul_one] at hcorner
    simp only [one_mul, mul_one] at hcorner
    have hproduct : (s - volume.real (A : Set Plane)) * (1 - volume.real (Q : Set Plane)) ≤
        (s - 2 * s * T) * (1 - volume.real (Q : Set Plane)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hroot := Real.sqrt_le_sqrt hproduct
    have hsqrt : Real.sqrt (4 * s * (1 / 2 - T) *
        (1 + 2 * (1 / 2 - volume.real (Q : Set Plane)))) =
        2 * Real.sqrt ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) := by
      first
      | rw [show 4 * s * (1 / 2 - T) * (1 + 2 * (1 / 2 - volume.real (Q : Set Plane))) =
          4 * ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    refine ⟨hThalf, ?_⟩
    unfold sliceLowerBound
    rw [hsqrt]
    apply (div_le_iff₀ (show 0 < 1 - 2 * (1 / 2 - T) by linarith)).mpr
    nlinarith

theorem deficit_log_square_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hδs : δ ≤ s) (hsExp : s ≤ Real.exp (-1)) :
    δ ^ 2 * Real.log (1 / δ) ≤ 2 * s ^ 2 * Real.log (1 / s) := by
  first
  | have hlogS : 1 ≤ Real.log (1 / s) := by
      first
      | have h := Real.log_le_log hs hsExp
        rw [Real.log_exp, Real.log_div one_ne_zero hs.ne', Real.log_one] at *
        linarith
    have hsplit : Real.log (1 / δ) = Real.log (1 / s) + Real.log (s / δ) := by
      first
      | rw [Real.log_div one_ne_zero hδ.ne', Real.log_div one_ne_zero hs.ne',
          Real.log_div hs.ne' hδ.ne', Real.log_one]
        ring
    have hratio : Real.log (s / δ) ≤ s / δ :=
      (Real.log_le_sub_one_of_pos (div_pos hs hδ)).trans (by linarith)
    have hratioMul := mul_le_mul_of_nonneg_left hratio (sq_nonneg δ)
    have hcancel : δ ^ 2 * (s / δ) = s * δ := by field_simp [hδ.ne']
    rw [hcancel] at hratioMul
    have hsquare : δ ^ 2 ≤ s ^ 2 := by nlinarith
    have hfirst := mul_le_mul_of_nonneg_right hsquare (by linarith : 0 ≤ Real.log (1 / s))
    have hsecond : s * δ ≤ s ^ 2 * Real.log (1 / s) := by
      first
      | have hds := mul_le_mul_of_nonneg_left hδs hs.le
        have hlog := mul_le_mul_of_nonneg_left hlogS (sq_nonneg s)
        nlinarith
    rw [hsplit, mul_add]
    linarith

/-- The universal upper gap, in the form that also applies to Proposition 6.2.
No equality assumption is imposed on the area of the averaged first body. -/
theorem geometric_threshold_upper {A B C Q : ConvexBody Plane} {s T z : ℝ}
    (hs : 0 < s) (hsmall : s < min (1 / 128) (Real.exp (-1))) (hT : 0 < T)
    (hAw : width A = 1) (hAh : height A = s)
    (hAa : 2 * s * T ≤ volume.real (A : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1)
    (hBa : volume.real (B : Set Plane) = T) (hCa : volume.real (C : Set Plane) = T)
    (hQ : IsInteraction B C Q) (hz : 2 * T * z = 2 * mixedArea volume A Q) :
    comparisonRoot s - z ≤ 34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | have hs128 : s < 1 / 128 := hsmall.trans_le (min_le_left _ _)
    have hsExp : s ≤ Real.exp (-1) := (hsmall.trans_le (min_le_right _ _)).le
    have hlog : 0 ≤ Real.log (1 / s) := by
      first
      | apply Real.log_nonneg
        apply (one_le_div hs).mpr
        linarith
    by_cases hzr : comparisonRoot s ≤ z
    · have hnonneg : 0 ≤ 34816 * s ^ 3 * Real.log (1 / s) := by positivity
      linarith
    have hzlt : z < comparisonRoot s := lt_of_not_ge hzr
    obtain ⟨hThalf, hf⟩ := geometric_slice_lower_bound hs hT hAw hAh hAa hQ.1 hQ.2.1 hz
    let δ : ℝ := 1 / 2 - T
    let η : ℝ := 1 / 2 - volume.real (Q : Set Plane)
    have hδ : 0 ≤ δ := by dsimp [δ]; linarith
    have hδhalf : δ < 1 / 2 := by dsimp [δ]; linarith
    have hηδ : η ≤ δ := by
      first
      | have h := hQ.area_ge_inputs hBw hBh hCw hCh
        rw [hBa, hCa, max_self] at h
        dsimp [η, δ]
        linarith
    have himprove : sliceLowerBound s δ η < comparisonRoot s := hf.trans_lt hzlt
    obtain ⟨hδpos, hηpos, _, hδbound⟩ := improving_deficit_localization hs
      (by linarith) hδ hδhalf hηδ himprove
    have hδsmall : 2 * δ < min (1 / 64) (Real.exp (-1)) := by
      first
      | apply lt_min
        · linarith
        · have hsexp := hsmall.trans_le (min_le_right _ _)
          linarith
    have henergy : η ≤ 4352 * δ ^ 2 * Real.log (1 / δ) := by
      first
      | have h := corollary_5_3 hBw hBh hCw hCh hQ hδpos hδsmall
          (show volume.real (B : Set Plane) = 1 / 2 - δ by rw [hBa]; dsimp [δ]; ring)
          (show volume.real (C : Set Plane) = 1 / 2 - δ by rw [hCa]; dsimp [δ]; ring)
        exact h
    have hlogCompare := deficit_log_square_le hδpos hs (by linarith) hsExp
    have hηbound : η ≤ 8704 * s ^ 2 * Real.log (1 / s) := by nlinarith
    have hscalar := improvement_le_four_mul hs (by linarith) hδ hδhalf hηδ himprove
    have hmult := mul_le_mul_of_nonneg_left hηbound (show 0 ≤ 4 * s by positivity)
    nlinarith

theorem reference_optimizer_fits {s η : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hη : 0 ≤ η) :
    Real.sqrt ((s - 2 * s * (1 / 2 - comparisonDeficit s)) /
      (1 - (1 / 2 - η))) ≤ min 1 s := by
  first
  | have hr := comparisonRoot_ge_one hs.le
    have hrpos := comparisonRoot_pos hs.le
    have hden : 0 < 1 - (1 / 2 - η) := by linarith
    have hratio : (s - 2 * s * (1 / 2 - comparisonDeficit s)) /
        (1 - (1 / 2 - η)) = s ^ 2 / (comparisonRoot s ^ 2 * (1 + 2 * η)) := by
      first
      | dsimp [comparisonDeficit]
        rw [show 1 - (1 / 2 - η) = (1 + 2 * η) / 2 by ring]
        have hp : 1 + 2 * η ≠ 0 := ne_of_gt (by linarith)
        field_simp [hrpos.ne', hp] <;> ring
    have hden' : 0 < comparisonRoot s ^ 2 * (1 + 2 * η) := by positivity
    have hden1 : 1 ≤ comparisonRoot s ^ 2 * (1 + 2 * η) := by
      first
      | have hr2 : 1 ≤ comparisonRoot s ^ 2 := by nlinarith
        have hp := mul_le_mul hr2 (show 1 ≤ 1 + 2 * η by linarith) (by norm_num) (by positivity)
        simpa only [one_mul] using hp
    have hsq : s ^ 2 / (comparisonRoot s ^ 2 * (1 + 2 * η)) ≤ s ^ 2 := by
      first
      | apply (div_le_iff₀ hden').mpr
        have h := mul_le_mul_of_nonneg_left hden1 (sq_nonneg s)
        simpa only [mul_one] using h
    rw [hratio]
    have hroot : Real.sqrt (s ^ 2 / (comparisonRoot s ^ 2 * (1 + 2 * η))) ≤ s :=
      (Real.sqrt_le_left hs.le).mpr hsq
    exact le_min (hroot.trans hs1) hroot

/-- The actual normalized lower witness for Theorem 5.5. The coefficient
normalization is supplied separately by Proposition 3.1 or its lifted converse. -/
theorem geometric_threshold_lower_polygons {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    ∃ A B C : ConvexBody Plane, ∃ T z : ℝ, 0 < T ∧
      width A = 1 ∧ height A = s ∧ volume.real (A : Set Plane) = 2 * s * T ∧
      width B = 1 ∧ height B = 1 ∧ width C = 1 ∧ height C = 1 ∧
      volume.real (B : Set Plane) = T ∧ volume.real (C : Set Plane) = T ∧
      6 * triple A B C = 2 * T * z ∧
      (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - z ∧
      PolytopeGeometry.IsFiniteHull (A : Set Plane) ∧
      PolytopeGeometry.IsFiniteHull (B : Set Plane) ∧
      PolytopeGeometry.IsFiniteHull (C : Set Plane) := by
  first
  | let δ := comparisonDeficit s
    have hδpos : 0 < δ := comparisonDeficit_pos hs
    have hδupper : δ ≤ s / 4 := comparisonDeficit_le_quarter hs.le
    have hδlower : s / 16 ≤ δ := comparisonDeficit_ge_sixteenth hs.le (by linarith)
    obtain ⟨B, Q, hBpoly, hQpoly, hBw, hBh, hBa, hQ, hQa, hgap⟩ := logarithmic_lower_polygon_interaction_witness
      hδpos (by linarith)
    let T := 1 / 2 - δ
    let η := 1 / 2 - volume.real (Q : Set Plane)
    have hT : 0 < T := by dsimp [T]; linarith
    have hηδ : η ≤ δ := by dsimp [η]; linarith
    have hlogδ : 0 < Real.log (1 / δ) := by
      first
      | apply Real.log_pos
        apply (one_lt_div hδpos).mpr
        linarith
    have hηpos : 0 < η := by
      first
      | have hterm : 0 < (3 / 50 : ℝ) * δ ^ 2 * Real.log (1 / δ) := by positivity
        exact hterm.trans_le hgap
    have hq1 : volume.real (Q : Set Plane) < 1 := by dsimp [η] at hηpos; linarith
    have hfit := reference_optimizer_fits hs (by linarith : s ≤ 1) hηpos.le
    obtain ⟨A, hAw, hAh, hAa, hAQ, hApoly⟩ := optimizer_attains_finiteHull Q hQpoly hQ.1 hQ.2.1 hq1
      (show 2 * s * T ≤ s by dsimp [T]; nlinarith)
      (by simpa only [T, δ, η, sub_sub_cancel] using hfit)
    let z := sliceLowerBound s δ η
    have hsqrt : Real.sqrt (4 * s * δ * (1 + 2 * η)) =
        2 * Real.sqrt ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) := by
      first
      | rw [show 4 * s * δ * (1 + 2 * η) =
          4 * ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) by dsimp [η, T]; ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hz : 6 * triple A B B = 2 * T * z := by
      first
      | rw [hQ.2.2 A, hAQ]
        dsimp only [z, sliceLowerBound]
        rw [hsqrt, show 1 - 2 * δ = 2 * T by dsimp [T]; ring]
        field_simp [hT.ne']
    have himprove := (reference_improvement_bounds hs.le hsSmall hηpos.le
      (show η ≤ 1 by linarith)).1
    change s * η / 4 ≤ comparisonRoot s - z at himprove
    have hlog : Real.log (1 / s) ≤ Real.log (1 / δ) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδpos (by linarith))
    have hlogs : 0 ≤ Real.log (1 / s) := Real.log_nonneg ((one_le_div hs).mpr (by linarith))
    have hsq : s ^ 2 / 256 ≤ δ ^ 2 := by nlinarith
    have hprod := mul_le_mul hsq hlog hlogs (sq_nonneg δ)
    change (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤ η at hgap
    have hηlower : (3 / 12800) * s ^ 2 * Real.log (1 / s) ≤ η := by nlinarith
    have hscale := mul_le_mul_of_nonneg_left hηlower (show 0 ≤ s / 4 by positivity)
    refine ⟨A, B, B, T, z, hT, hAw, hAh, hAa, hBw, hBh, hBw, hBh, hBa, hBa, hz,
      ?_, hApoly, hBpoly, hBpoly⟩
    nlinarith

theorem geometric_threshold_lower {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    ∃ A B C : ConvexBody Plane, ∃ T z : ℝ, 0 < T ∧
      width A = 1 ∧ height A = s ∧ volume.real (A : Set Plane) = 2 * s * T ∧
      width B = 1 ∧ height B = 1 ∧ width C = 1 ∧ height C = 1 ∧
      volume.real (B : Set Plane) = T ∧ volume.real (C : Set Plane) = T ∧
      6 * triple A B C = 2 * T * z ∧
      (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - z := by
  first
  | obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
      hBa, hCa, hz, hgap, _, _, _⟩ := geometric_threshold_lower_polygons hs hsSmall
    exact ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz, hgap⟩

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/GeometricThreshold.lean -/

/- BEGIN SOURCE: VolumePolynomials/BivariateCoordinates.lean -/
section


@[expose] public section

/-! # Faithful conversion between two polynomial representations -/

open Polynomial
open scoped Polynomial.Bivariate

namespace VolumePolynomials

/-- Coordinate zero becomes the outer variable; coordinate one the inner variable. -/
noncomputable def twoVariableEquiv :
    MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] ℝ[X][Y] :=
  (Polynomial.Bivariate.equivMvPolynomial ℝ).symm.trans Polynomial.Bivariate.swap

theorem twoVariableEquiv_eval (p : MvPolynomial (Fin 2) ℝ) (s y : ℝ) :
    (twoVariableEquiv p).evalEval y s = MvPolynomial.eval ![s, y] p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [twoVariableEquiv, Polynomial.Bivariate.swap_C_C]
  | add p q hp hq =>
      simpa only [map_add, evalEval_add, MvPolynomial.eval_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      rw [map_mul, evalEval_mul, MvPolynomial.eval_mul, hp]
      congr 1
      fin_cases i <;>
        simp [twoVariableEquiv,
          Polynomial.Bivariate.swap_X, Polynomial.Bivariate.swap_Y,
          evalEval_C]

/-- Swapping the two variables preserves their actual scalar evaluations. -/
theorem bivariate_eval_swap (p : ℝ[X][Y]) (s y : ℝ) :
    (Polynomial.Bivariate.swap p).evalEval s y = p.evalEval y s := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, evalEval_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.Bivariate.swap_monomial, evalEval_mul, evalEval_map_C,
        evalEval_C]
      simp only [evalEval, eval_monomial, eval_mul, eval_pow, eval_C, eval_X]

/-- Substituting a polynomial into the outer variable commutes with scalar evaluation. -/
theorem bivariate_eval_polynomial (p : ℝ[X][Y]) (q : ℝ[X]) (y : ℝ) :
    (p.eval q).eval y = p.evalEval y (q.eval y) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [eval_add, evalEval_add, hp, hr]
  | monomial n a => simp only [eval_monomial, eval_mul, eval_pow, evalEval, eval_C]

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BivariateCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/LogObstruction.lean -/
section


@[expose] public section

/-!
# The analytic obstruction behind the logarithmic boundary gap

This file proves the nonalgebraicity mechanism used in Corollary 5.6 of
*Volume polynomials and the Heine–Shephard problem*. The results are about
ordinary real polynomials and their actual evaluations. No assertion about
mixed volumes or semialgebraic sets is assumed in their definitions.
-/

open Filter Polynomial Asymptotics
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

/-- The elementary two-sided logarithmic estimates imply the two asymptotic
properties needed below. The upper constant need not be optimal. -/
theorem growth_of_two_sided_log_bounds {g : ℝ → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hbound : ∀ᶠ x in atTop, c * Real.log x ≤ g x ∧ g x ≤ C * Real.log x) :
    Tendsto g atTop atTop ∧ g =O[atTop] Real.log := by
  constructor
  · exact tendsto_atTop_mono' atTop (hbound.mono fun _ h => h.1)
      (Tendsto.const_mul_atTop hc Real.tendsto_log_atTop)
  · apply IsBigO.of_bound C
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
    have hg : 0 ≤ g x := (mul_nonneg hc.le hlog).trans hx.1
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg, abs_of_nonneg hlog] using hx.2

/-- Every polynomial of a logarithmically bounded function is negligible
compared with the independent variable. -/
theorem polynomial_comp_logBound_div_tendsto_zero
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    (hlog : g =O[atTop] Real.log) (p : ℝ[X]) :
    Tendsto (fun x => p.eval (g x) / x) atTop (𝓝 0) := by
  have hp : p.eval =O[atTop] fun y => y ^ p.natDegree := by
    simpa using p.isBigO_atTop_of_degree_le (X ^ p.natDegree)
      (by simp)
  have hpow : (fun x => g x ^ p.natDegree) =O[atTop]
      fun x => Real.log x ^ p.natDegree := hlog.pow _
  exact (((hp.comp_tendsto hg).trans hpow).trans_isLittleO
    Real.isLittleO_pow_log_id_atTop).tendsto_div_nhds_zero

/-- Allowing polynomial dependence on `1 / x` preserves the preceding bound. -/
theorem bivariate_comp_logBound_div_tendsto_zero
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    (hlog : g =O[atTop] Real.log) (p : ℝ[X][Y]) :
    Tendsto (fun x => p.evalEval (g x) x⁻¹ / x) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [evalEval_add, add_div, zero_add] using hp.add hq
  | monomial n a =>
      have h := (polynomial_comp_logBound_div_tendsto_zero hg hlog a).mul
        (tendsto_inv_atTop_zero.pow n)
      simpa only [evalEval, eval_monomial, eval_mul, eval_pow, eval_C,
        zero_mul, mul_div_right_comm] using h

/-- A nonzero polynomial evaluated along a function tending to infinity cannot
tend to zero. This also covers constant nonzero polynomials. -/
theorem polynomial_comp_not_tendsto_zero
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    {p : ℝ[X]} (hp : p ≠ 0) :
    ¬ Tendsto (fun x => p.eval (g x)) atTop (𝓝 0) := by
  intro h
  by_cases hn : p.natDegree = 0
  · have hpc : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
    have hval : p.coeff 0 = 0 := by
      rw [hpc] at h
      simpa only [eval_C, tendsto_const_nhds_iff] using h
    exact hp (by rw [hpc, hval, C_0])
  · have habs : Tendsto (fun x => |p.eval (g x)|) atTop atTop :=
      (p.abs_tendsto_atTop (Polynomial.natDegree_pos_iff_degree_pos.mp
        (Nat.pos_of_ne_zero hn))).comp hg
    have hzero : Tendsto (fun x => |p.eval (g x)|) atTop (𝓝 0) := by
      simpa using h.abs
    exact (not_tendsto_nhds_of_tendsto_atTop habs 0) hzero

/-- A function tending to infinity with logarithmic growth satisfies no
nonzero polynomial relation with the reciprocal independent variable.
This is the contradiction used after the lowest power of `s` is divided out
in Corollary 5.6, with `x = 1 / s`. -/
theorem no_bivariate_relation_of_logBound
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    (hlog : g =O[atTop] Real.log) {p : ℝ[X][Y]} (hp : p ≠ 0) :
    ¬ (∀ᶠ x in atTop, p.evalEval (g x) x⁻¹ = 0) := by
  intro hrel
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  simp only [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa only [X_dvd_iff] using hq
  have hqrel : ∀ᶠ x in atTop, q.evalEval (g x) x⁻¹ = 0 := by
    filter_upwards [hrel, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    rw [hpq, evalEval_mul, evalEval_pow, evalEval_X] at hx
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (inv_ne_zero hxpos.ne'))
  have ht := bivariate_comp_logBound_div_tendsto_zero hg hlog q.divX
  have heq : (fun x => (q.coeff 0).eval (g x)) =ᶠ[atTop]
      (fun x => -(q.divX.evalEval (g x) x⁻¹ / x)) := by
    filter_upwards [hqrel] with x hx
    have hsplit := congrArg (fun p : ℝ[X][Y] => p.evalEval (g x) x⁻¹)
      q.X_mul_divX_add
    simp only [evalEval_add, evalEval_mul, evalEval_X, evalEval_C, hx] at hsplit
    rw [div_eq_mul_inv]
    nlinarith [hsplit]
  have hneg : Tendsto (fun x => -(q.divX.evalEval (g x) x⁻¹ / x)) atTop (𝓝 0) := by
    simpa using ht.neg
  exact polynomial_comp_not_tendsto_zero hg hq0 (hneg.congr' heq.symm)

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/LogObstruction.lean -/

/- BEGIN SOURCE: VolumePolynomials/AlgebraicGerms.lean -/
section


@[expose] public section

/-!
# Algebraic closure of eventual polynomial relations

The coefficients are polynomials in an actual real-valued base function.
Germs are used only to transport Mathlib's proved closure of algebraic elements
under addition and multiplication. Every conclusion is then converted back to
an explicit nonzero real bivariate polynomial and an eventual evaluation identity.

This gives the elimination step in the logarithmic boundary argument without
assuming quantifier elimination, a Puiseux expansion, or a resultant identity.
-/

open Filter Polynomial Asymptotics
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

/-- An actual nonzero bivariate real polynomial vanishes eventually. -/
def HasPolynomialRelation {α : Type*} (l : Filter α) (s g : α → ℝ) : Prop :=
  ∃ p : ℝ[X][Y], p ≠ 0 ∧ ∀ᶠ x in l, p.evalEval (s x) (g x) = 0

/-- Evaluation of a univariate polynomial in the base function, modulo eventual equality. -/
noncomputable def germPolynomialEvaluation {α : Type*} (l : Filter α) (s : α → ℝ) :
    ℝ[X] →+* Germ l ℝ :=
  (Germ.coeRingHom l).comp (RingHom.pi fun x => Polynomial.evalRingHom (s x))

theorem germPolynomialEvaluation_apply {α : Type*} (l : Filter α) (s : α → ℝ)
    (p : ℝ[X]) :
    germPolynomialEvaluation l s p = Germ.ofFun (fun x => p.eval (s x)) := rfl

theorem aeval_germ {α : Type*} (l : Filter α) (s g : α → ℝ) (p : ℝ[X][Y]) :
    let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
    Polynomial.aeval (Germ.ofFun g : Germ l ℝ) p =
      Germ.ofFun (fun x => p.evalEval (s x) (g x)) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  change Polynomial.aeval (Germ.ofFun g : Germ l ℝ) p =
    Germ.ofFun (fun x => p.evalEval (s x) (g x))
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      change Germ.ofFun (fun x => p.evalEval (s x) (g x) + q.evalEval (s x) (g x)) = _
      congr 1
      funext x
      simp only [evalEval_add]
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      change Germ.ofFun (fun x => a.eval (s x) * g x ^ n) =
        Germ.ofFun (fun x => (monomial n a).evalEval (s x) (g x))
      congr 1
      funext x
      simp only [evalEval, eval_monomial, eval_mul, eval_pow, eval_C]

theorem hasPolynomialRelation_iff_isAlgebraic {α : Type*} (l : Filter α)
    (s g : α → ℝ) :
    let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
    HasPolynomialRelation l s g ↔ IsAlgebraic ℝ[X] (Germ.ofFun g : Germ l ℝ) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  constructor
  · rintro ⟨p, hp, hrel⟩
    refine ⟨p, hp, ?_⟩
    rw [aeval_germ]
    exact Germ.coe_eq.mpr hrel
  · rintro ⟨p, hp, hrel⟩
    refine ⟨p, hp, ?_⟩
    rw [aeval_germ] at hrel
    exact Germ.coe_eq.mp hrel

namespace HasPolynomialRelation

variable {α : Type*} {l : Filter α} {s f g : α → ℝ}

theorem congr (hf : HasPolynomialRelation l s f) (hfg : f =ᶠ[l] g) :
    HasPolynomialRelation l s g := by
  obtain ⟨p, hp, hrel⟩ := hf
  refine ⟨p, hp, ?_⟩
  filter_upwards [hrel, hfg] with x hx hfgx
  simpa only [← hfgx] using hx

theorem sub (hf : HasPolynomialRelation l s f) (hg : HasPolynomialRelation l s g) :
    HasPolynomialRelation l s (fun x => f x - g x) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  apply (hasPolynomialRelation_iff_isAlgebraic l s _).mpr
  exact ((hasPolynomialRelation_iff_isAlgebraic l s f).mp hf).sub
    ((hasPolynomialRelation_iff_isAlgebraic l s g).mp hg)

theorem mul (hf : HasPolynomialRelation l s f) (hg : HasPolynomialRelation l s g) :
    HasPolynomialRelation l s (fun x => f x * g x) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  apply (hasPolynomialRelation_iff_isAlgebraic l s _).mpr
  exact ((hasPolynomialRelation_iff_isAlgebraic l s f).mp hf).mul
    ((hasPolynomialRelation_iff_isAlgebraic l s g).mp hg)

theorem pow (hf : HasPolynomialRelation l s f) (n : ℕ) :
    HasPolynomialRelation l s (fun x => f x ^ n) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  apply (hasPolynomialRelation_iff_isAlgebraic l s _).mpr
  exact ((hasPolynomialRelation_iff_isAlgebraic l s f).mp hf).pow n

end HasPolynomialRelation

/-- The reciprocal of the base coordinate is algebraic wherever it is eventually nonzero. -/
theorem hasPolynomialRelation_inv {α : Type*} {l : Filter α} {s : α → ℝ}
    (hs : ∀ᶠ x in l, s x ≠ 0) :
    HasPolynomialRelation l s (fun x => (s x)⁻¹) := by
  refine ⟨C X * Y - 1, ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun p : ℝ[X][Y] => p.coeff 1) hzero
    simp [Polynomial.coeff_one] at hcoeff
  · filter_upwards [hs] with x hx
    simp [evalEval_C, hx]

/-- Scaling the difference of two algebraic functions by an inverse coordinate
power produces an explicit eventual polynomial relation. -/
theorem hasPolynomialRelation_scaled_gap {α : Type*} {l : Filter α}
    {s r b : α → ℝ} (hr : HasPolynomialRelation l s r)
    (hb : HasPolynomialRelation l s b) (hs : ∀ᶠ x in l, s x ≠ 0) (n : ℕ) :
    HasPolynomialRelation l s (fun x => (r x - b x) / s x ^ n) := by
  apply ((hr.sub hb).mul ((hasPolynomialRelation_inv hs).pow n)).congr
  exact Filter.Eventually.of_forall fun x => by simp only [div_eq_mul_inv, inv_pow]

/-- A divergent function with logarithmic upper growth is transcendental over
the polynomial ring in the reciprocal independent variable. -/
theorem no_polynomialRelation_of_logBound {g : ℝ → ℝ}
    (hg : Tendsto g atTop atTop) (hlog : g =O[atTop] Real.log) :
    ¬ HasPolynomialRelation atTop (fun x : ℝ => x⁻¹) g := by
  rintro ⟨p, hp, hrel⟩
  apply no_bivariate_relation_of_logBound hg hlog
    (p := Polynomial.Bivariate.swap p)
    (fun h => hp (Polynomial.Bivariate.swap.injective (by simpa using h)))
  simpa only [bivariate_eval_swap] using hrel

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AlgebraicGerms.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/AlgebraicDependence.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Polynomial relations on semialgebraic sets with empty interior

A real semialgebraic set with empty interior is contained in the zero set of a single nonzero
polynomial. No boundedness, closedness or regularity assumption is needed. This is the algebraic
step that turns semialgebraic graphs into algebraic relations.

In a finite sign presentation, a point where none of the nonzero defining polynomials vanishes
is an interior point: all the signs are locally constant there. Consequently the product of
the nonzero defining polynomials vanishes on the set. Identically zero polynomials must be
omitted from this product. The empty set is included, with the empty product equal to one.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 2.8 (dimension) and Section 8.1 (Nash functions).
-/

public section

open Filter MvPolynomial Set Topology

namespace TauCeti

/-- A real semialgebraic set with empty interior satisfies a nonzero polynomial equation.
The index type need not be finite: a semialgebraic presentation uses only finitely many
polynomials, each involving only finitely many coordinates. -/
theorem IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty {σ : Type*}
    {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) (hint : interior s = ∅) :
    ∃ p : MvPolynomial σ ℝ, p ≠ 0 ∧ ∀ x ∈ s, eval x p = 0 := by
  classical
  obtain ⟨m, p, Φ, hpres⟩ := hs.exists_eq_setOf_sign_eval
  let I : Finset (Fin m) := Finset.univ.filter fun i ↦ p i ≠ 0
  refine ⟨∏ i ∈ I, p i, Finset.prod_ne_zero_iff.mpr (fun i hi ↦ (Finset.mem_filter.mp hi).2), ?_⟩
  intro x hx
  have hzero : ∃ i ∈ I, eval x (p i) = 0 := by
    by_contra h
    have hne (i : Fin m) (hi : p i ≠ 0) : eval x (p i) ≠ 0 :=
      fun hxi ↦ h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hxi⟩
    have hsign (i : Fin m) :
        ∀ᶠ y in 𝓝 x, SignType.sign (eval y (p i)) = SignType.sign (eval x (p i)) := by
      by_cases hi : p i = 0
      · simp [hi]
      · exact ((continuousAt_sign_of_ne_zero (hne i hi)).comp
          (f := fun y : σ → ℝ ↦ eval y (p i)) (p i).continuous_eval.continuousAt).preimage_mem_nhds
            ((isOpen_discrete _).mem_nhds (mem_singleton _))
    have hmem : s ∈ 𝓝 x := by
      filter_upwards [eventually_all.mpr hsign] with y hy
      rw [hpres] at hx ⊢
      simpa only [mem_ofPred_eq, funext hy] using hx
    have := mem_interior_iff_mem_nhds.mpr hmem
    simp [hint] at this
  obtain ⟨i, hi, hxi⟩ := hzero
  rw [map_prod]
  exact Finset.prod_eq_zero hi hxi

end TauCeti
end -- closes the original EOF section from source line 32
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/AlgebraicDependence.lean -/

/- BEGIN SOURCE: VolumePolynomials/SemialgebraicBoundary.lean -/
section


@[expose] public section

/-!
# Polynomial equations on semialgebraic frontiers

This elementary boundary version of the finite-sign argument avoids a
quantifier-elimination dependency. The proof extends the argument in TauCeti's
`Semialgebraic.AlgebraicDependence`, whose Apache-2.0 source is vendored.
-/

open Filter MvPolynomial Set Topology

namespace VolumePolynomials

/-- Every frontier of a semialgebraic set is contained in a nonzero polynomial
zero set, obtained from the finite defining sign conditions. -/
theorem frontier_polynomial_relation {σ : Type*} {s : Set (σ → ℝ)}
    (hs : TauCeti.IsSemialgebraic s) :
    ∃ p : MvPolynomial σ ℝ, p ≠ 0 ∧ ∀ x ∈ frontier s, eval x p = 0 := by
  classical
  obtain ⟨m, p, Φ, hpres⟩ := hs.exists_eq_setOf_sign_eval
  let I : Finset (Fin m) := Finset.univ.filter fun i => p i ≠ 0
  refine ⟨∏ i ∈ I, p i,
    Finset.prod_ne_zero_iff.mpr (fun i hi => (Finset.mem_filter.mp hi).2), ?_⟩
  intro x hx
  have hzero : ∃ i ∈ I, eval x (p i) = 0 := by
    by_contra h
    have hne (i : Fin m) (hi : p i ≠ 0) : eval x (p i) ≠ 0 :=
      fun hxi => h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hxi⟩
    have hsign (i : Fin m) :
        ∀ᶠ y in 𝓝 x, SignType.sign (eval y (p i)) = SignType.sign (eval x (p i)) := by
      by_cases hi : p i = 0
      · simp [hi]
      · exact ((continuousAt_sign_of_ne_zero (hne i hi)).comp
          (f := fun y : σ → ℝ => eval y (p i))
          (p i).continuous_eval.continuousAt).preimage_mem_nhds
            ((isOpen_discrete _).mem_nhds (mem_singleton _))
    have hlocal : ∀ᶠ y in 𝓝 x, (y ∈ s ↔ x ∈ s) := by
      filter_upwards [eventually_all.mpr hsign] with y hy
      simp only [hpres, mem_ofPred_eq, funext hy]
    rw [frontier_eq_inter_compl_interior] at hx
    change x ∉ interior s ∧ x ∉ interior sᶜ at hx
    by_cases hxs : x ∈ s
    · apply hx.1
      apply mem_interior_iff_mem_nhds.mpr
      exact hlocal.mono fun _ hy => hy.mpr hxs
    · apply hx.2
      apply mem_interior_iff_mem_nhds.mpr
      exact hlocal.mono fun _ hy => by simpa only [mem_compl_iff, hy] using hxs
  obtain ⟨i, hi, hxi⟩ := hzero
  rw [map_prod]
  exact Finset.prod_eq_zero hi hxi

/-- An attained lower endpoint of a vertical fiber is a frontier point. -/
theorem fiber_minimum_mem_frontier {s : Set (Fin 2 → ℝ)} {x b : ℝ}
    (hmem : ![x, b] ∈ s)
    (hminimal : ∀ y : ℝ, ![x, y] ∈ s → b ≤ y) :
    ![x, b] ∈ frontier s := by
  apply (mem_frontier_iff_notMem_interior hmem).mpr
  intro hint
  have hcont : Continuous (fun y : ℝ => ![x, y]) := by
    fun_prop
  have hpre : b ∈ interior ((fun y : ℝ => ![x, y]) ⁻¹' s) :=
    preimage_interior_subset_interior_preimage hcont hint
  have hsub : (fun y : ℝ => ![x, y]) ⁻¹' s ⊆ Ici b := by
    intro y hy
    exact hminimal y hy
  have hbad := interior_mono hsub hpre
  simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at hbad

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SemialgebraicBoundary.lean -/

/- BEGIN SOURCE: VolumePolynomials/ThresholdFrontier.lean -/
section


@[expose] public section

/-!
# Logarithmic boundary gaps exclude semialgebraicity

This proves the final implication in Corollary 5.6 directly from the finite-sign
definition of a semialgebraic set. An attained fiber minimum lies on the frontier;
a frontier satisfies a nonzero polynomial relation. The explicit comparison root
is algebraic. Algebraic closure in the ring of function germs eliminates the root,
and the logarithmic growth theorem gives a contradiction.

The actual geometric fiber minima and the two-sided gap estimate remain explicit
hypotheses. They must be supplied by the volume-polynomial normalization and
Theorem 5.5 before this can imply the paper's main Theorem 1.1.
-/

open Filter Polynomial Asymptotics Set
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

theorem hasPolynomialRelation_comparisonRoot {α : Type*} (l : Filter α) (s : α → ℝ) :
    HasPolynomialRelation l s (fun x => comparisonRoot (s x)) := by
  refine ⟨Y ^ 2 - C (1 + X) * Y + C (C (1 / 2) * X), ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun p : ℝ[X][Y] => p.coeff 2) hzero
    norm_num [Polynomial.coeff_one] at hcoeff
  · apply Filter.Eventually.of_forall
    intro x
    have hquad := comparisonRoot_quadratic (s x)
    simp only [evalEval_add, evalEval_sub, evalEval_pow, evalEval_mul, evalEval_X,
      evalEval_C, eval_add, eval_one, eval_X, eval_mul, eval_C]
    nlinarith [hquad]

/-- A semialgebraic set's attained lower fiber endpoints satisfy an actual
nonzero polynomial equation on every sufficiently small positive interval. -/
theorem polynomialRelation_of_semialgebraic_minima
    {S : Set (Fin 2 → ℝ)} {b : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hS : TauCeti.IsSemialgebraic S)
    (hattain : ∀ x ∈ Ioo 0 a, ![x, b x] ∈ S)
    (hminimum : ∀ x ∈ Ioo 0 a, ∀ y : ℝ, ![x, y] ∈ S → b x ≤ y) :
    HasPolynomialRelation atTop (fun x : ℝ => x⁻¹) (fun x => b x⁻¹) := by
  obtain ⟨p, hp, hfront⟩ := frontier_polynomial_relation hS
  let q : ℝ[X][Y] := Polynomial.Bivariate.swap (twoVariableEquiv p)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hp
    apply twoVariableEquiv.injective
    apply Polynomial.Bivariate.swap.injective
    simpa only [map_zero] using hqzero
  refine ⟨q, hq, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    tendsto_inv_atTop_zero.eventually (Iio_mem_nhds ha)] with x hx hxsmall
  have hxin : x⁻¹ ∈ Ioo 0 a := ⟨inv_pos.mpr hx, hxsmall⟩
  change (Polynomial.Bivariate.swap (twoVariableEquiv p)).evalEval x⁻¹ (b x⁻¹) = 0
  rw [bivariate_eval_swap, twoVariableEquiv_eval]
  exact hfront _ (fiber_minimum_mem_frontier (hattain _ hxin) (hminimum _ hxin))

/-- The exact logarithmic minimum-gap implication, with no quantifier-elimination
assumption and no semialgebraicity hypothesis about the minimum function itself. -/
theorem not_semialgebraic_of_logarithmic_minimum_gap_frontier
    {S : Set (Fin 2 → ℝ)} {b : ℝ → ℝ} {a c C : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hattain : ∀ x ∈ Ioo 0 a, ![x, b x] ∈ S)
    (hminimum : ∀ x ∈ Ioo 0 a, ∀ y : ℝ, ![x, y] ∈ S → b x ≤ y)
    (hgap : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      c * x ^ 3 * Real.log x⁻¹ ≤ comparisonRoot x - b x ∧
      comparisonRoot x - b x ≤ C * x ^ 3 * Real.log x⁻¹) :
    ¬ TauCeti.IsSemialgebraic S := by
  intro hS
  have hb := polynomialRelation_of_semialgebraic_minima ha hS hattain hminimum
  have hr := hasPolynomialRelation_comparisonRoot atTop (fun x : ℝ => x⁻¹)
  have hnz : ∀ᶠ x in atTop, (x : ℝ)⁻¹ ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact inv_ne_zero hx.ne'
  have hrelation := hasPolynomialRelation_scaled_gap hr hb hnz 3
  have hbound : ∀ᶠ x in atTop,
      c * Real.log x ≤ (comparisonRoot x⁻¹ - b x⁻¹) / (x⁻¹) ^ 3 ∧
      (comparisonRoot x⁻¹ - b x⁻¹) / (x⁻¹) ^ 3 ≤ C * Real.log x := by
    filter_upwards [tendsto_inv_atTop_nhdsGT_zero.eventually hgap,
      eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    have hpow : 0 < (x⁻¹) ^ 3 := pow_pos (inv_pos.mpr hxpos) 3
    simp only [inv_inv] at hx
    constructor
    · apply (le_div_iff₀ hpow).mpr
      nlinarith [hx.1]
    · apply (div_le_iff₀ hpow).mpr
      nlinarith [hx.2]
  obtain ⟨hinf, hlog⟩ := growth_of_two_sided_log_bounds hc hbound
  exact no_polynomialRelation_of_logBound hinf hlog hrelation

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ThresholdFrontier.lean -/

/- BEGIN SOURCE: VolumePolynomials/NormalizedThreshold.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Attained minima of the actual normalized cubic geometry

The fiber is defined by literal bodies and the equalities in (3.2), with
`α = 2*s`. Compactness and a positive lower bound on `T` prove attainment;
the threshold is not supplied as an assumed minimum function. Proposition
3.1 is the separate equivalence with the original coefficient slice.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

structure NormalizedData (s z : ℝ) where
  A : ConvexBody Plane
  B : ConvexBody Plane
  C : ConvexBody Plane
  T : ℝ
  T_pos : 0 < T
  A_width : width A = 1
  A_height : height A = s
  A_area : volume.real (A : Set Plane) = 2 * s * T
  B_width : width B = 1
  B_height : height B = 1
  C_width : width C = 1
  C_height : height C = 1
  B_area : volume.real (B : Set Plane) = T
  C_area : volume.real (C : Set Plane) = T
  triple_value : 6 * triple A B C = 2 * T * z

def NormalizedRealizable (s z : ℝ) : Prop := Nonempty (NormalizedData s z)
def normalizedThreshold (s : ℝ) : ℝ := sInf {z : ℝ | NormalizedRealizable s z}
def normalizedSlice : Set (Fin 2 → ℝ) := {p | NormalizedRealizable (p 0) (p 1)}

theorem triple_translate (A B C : ConvexBody Plane) (a b c : Plane) :
    triple (translateBody a A) (translateBody b B) (translateBody c C) = triple A B C := by
  first
  | have h := mixed3_translate (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      (embedXY a) (embedYZ b) (embedXZ c)
    simpa only [triple, mapBody_translate] using h

def NormalizedData.translate {s z : ℝ} (D : NormalizedData s z) (a b c : Plane) :
    NormalizedData s z where
  A := translateBody a D.A
  B := translateBody b D.B
  C := translateBody c D.C
  T := D.T
  T_pos := D.T_pos
  A_width := (width_translate _ _).trans D.A_width
  A_height := (height_translate _ _).trans D.A_height
  A_area := (area_translate _ _).trans D.A_area
  B_width := (width_translate _ _).trans D.B_width
  B_height := (height_translate _ _).trans D.B_height
  C_width := (width_translate _ _).trans D.C_width
  C_height := (height_translate _ _).trans D.C_height
  B_area := (area_translate _ _).trans D.B_area
  C_area := (area_translate _ _).trans D.C_area
  triple_value := by rw [triple_translate]; exact D.triple_value

theorem normalized_nonempty {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    ∃ z : ℝ, NormalizedRealizable s z ∧ z ≤ 2 := by
  first
  | obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
      hBa, hCa, hz, hgap⟩ := geometric_threshold_lower hs hsSmall
    have hlog : 0 ≤ Real.log (1 / s) :=
      Real.log_nonneg ((one_le_div hs).mpr (by linarith))
    have hterm : 0 ≤ (3 / 51200 : ℝ) * s ^ 3 * Real.log (1 / s) := by positivity
    have hr := comparisonRoot_le_one_add hs.le
    exact ⟨z, ⟨⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz⟩⟩,
      by linarith⟩

def separationConstant (s : ℝ) : ℝ := 1 + s - 2 * Real.sqrt s

theorem separationConstant_pos {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    0 < separationConstant s := by
  first
  | have hr := Real.sqrt_nonneg s
    have hsq := Real.sq_sqrt hs
    have hr1 : Real.sqrt s < 1 := by nlinarith
    have hdiff : 0 < (1 - Real.sqrt s) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
    dsimp [separationConstant]
    nlinarith

theorem NormalizedData.separation {s z : ℝ} (D : NormalizedData s z) (hs : 0 < s) :
    separationConstant s ≤ 2 * D.T * z := by
  first
  | obtain ⟨Q, hQ, _⟩ := proposition_4_3 D.B D.C D.B_width D.B_height D.C_width D.C_height
    have hcorner := mixedArea_corner_inequality D.A Q
    rw [D.A_width, D.A_height, hQ.1, hQ.2.1, one_mul, mul_one] at hcorner
    simp only [one_mul, mul_one] at hcorner
    have hAu := area_le_width_mul_height D.A
    rw [D.A_width, D.A_height, one_mul] at hAu
    have hQu := area_le_width_mul_height Q
    rw [hQ.1, hQ.2.1, one_mul] at hQu
    have hA0 : 0 ≤ volume.real (D.A : Set Plane) := measureReal_nonneg
    have hQ0 : 0 ≤ volume.real (Q : Set Plane) := measureReal_nonneg
    have hprod : (s - volume.real (D.A : Set Plane)) * (1 - volume.real (Q : Set Plane)) ≤ s := by
      first
      | have h := mul_le_mul_of_nonneg_left (show 1 - volume.real (Q : Set Plane) ≤ 1 by linarith)
          (show 0 ≤ s - volume.real (D.A : Set Plane) by linarith)
        nlinarith
    have hroot := Real.sqrt_le_sqrt hprod
    have heq := hQ.2.2 D.A
    rw [D.triple_value] at heq
    dsimp [separationConstant]
    linarith

theorem NormalizedData.T_lower {s z : ℝ} (D : NormalizedData s z)
    (hs : 0 < s) (hz : z ≤ 2) : separationConstant s / 4 ≤ D.T := by
  first
  | have hc := D.separation hs
    have h := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * D.T from mul_nonneg (by norm_num) D.T_pos.le)
    linarith

theorem body_subset_box_of_widths (K : ConvexBody Plane) (h0 : (0 : Plane) ∈ K)
    (hw : width K ≤ 1) (hh : height K ≤ 1) :
    (K : Set Plane) ⊆ Icc (-1, -1) (1, 1) := by
  first
  | intro p hp
    have hpos (i : Fin 4) : 0 ≤ SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | simpa only [map_zero] using SupportGeometry.le_support K.isCompact (axisNormals i) h0
    have hx := support_axisX_sum K
    have hy := support_axisY_sum K
    have hpx := SupportGeometry.le_support K.isCompact (axisNormals 0) hp
    have hnx := SupportGeometry.le_support K.isCompact (axisNormals 1) hp
    have hpy := SupportGeometry.le_support K.isCompact (axisNormals 3) hp
    have hny := SupportGeometry.le_support K.isCompact (axisNormals 2) hp
    have h0' := hpos 0
    have h1' := hpos 1
    have h2' := hpos 2
    have h3' := hpos 3
    simp only [axisNormals, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      normal_apply, one_mul, zero_mul, neg_one_mul, sub_zero, zero_sub] at hpx hnx hpy hny h0' h1' h2' h3'
    change (-1 ≤ p.1 ∧ -1 ≤ p.2) ∧ (p.1 ≤ 1 ∧ p.2 ≤ 1)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

def centeredBoxBodies : Set (ConvexBody Plane) :=
  {Q | (0 : Plane) ∈ Q ∧ (Q : Set Plane) ⊆ Icc (-1, -1) (1, 1)}

def normalizedTupleConstraints (s t : ℝ) : Set (Fin 3 → ConvexBody Plane) :=
  {K | (∀ i, width (K i) = 1) ∧
    (∀ i, height (K i) = (![s, 1, 1] : Fin 3 → ℝ) i) ∧
    volume.real (K 0 : Set Plane) = 2 * s * volume.real (K 1 : Set Plane) ∧
    volume.real (K 2 : Set Plane) = volume.real (K 1 : Set Plane) ∧
    t ≤ volume.real (K 1 : Set Plane)}

def normalizedCompactTuples (s t : ℝ) : Set (Fin 3 → ConvexBody Plane) :=
  (Set.pi Set.univ (fun _ : Fin 3 => centeredBoxBodies)) ∩ normalizedTupleConstraints s t

theorem isClosed_normalizedTupleConstraints (s t : ℝ) :
    IsClosed (normalizedTupleConstraints s t) := by
  first
  | have hw : IsClosed {K : Fin 3 → ConvexBody Plane | ∀ i, width (K i) = 1} := by
      first
      | simp only [ofPred_forall]
        exact isClosed_iInter (fun i => isClosed_eq (continuous_width.comp (continuous_apply i)) continuous_const)
    have hh : IsClosed {K : Fin 3 → ConvexBody Plane |
        ∀ i, height (K i) = (![s, 1, 1] : Fin 3 → ℝ) i} := by
      first
      | simp only [ofPred_forall]
        exact isClosed_iInter (fun i => isClosed_eq (continuous_height.comp (continuous_apply i)) continuous_const)
    have ha (i : Fin 3) : Continuous (fun K : Fin 3 → ConvexBody Plane => volume.real (K i : Set Plane)) :=
      (continuous_convexBody_realMeasure volume).comp (continuous_apply i)
    exact hw.inter (hh.inter ((isClosed_eq (ha 0) (continuous_const.mul (ha 1))).inter
      ((isClosed_eq (ha 2) (ha 1)).inter (isClosed_le continuous_const (ha 1)))))

theorem isCompact_normalizedCompactTuples (s t : ℝ) :
    IsCompact (normalizedCompactTuples s t) := by
  first
  | exact (isCompact_univ_pi (fun _ : Fin 3 =>
      isCompact_bodies_in_compact (E := Plane) (isCompact_Icc : IsCompact (Icc ((-1, -1) : Plane) (1, 1))))).inter_right
        (isClosed_normalizedTupleConstraints s t)

def normalizedTupleValue (K : Fin 3 → ConvexBody Plane) : ℝ :=
  (6 * triple (K 0) (K 1) (K 2)) / (2 * volume.real (K 1 : Set Plane))

theorem continuous_triple_tuple :
    Continuous (fun K : Fin 3 → ConvexBody Plane => triple (K 0) (K 1) (K 2)) := by
  first
  | apply (continuous_mixedVolume volume 3).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_mapBody embedXY).comp (continuous_apply 0)
    · exact (continuous_mapBody embedYZ).comp (continuous_apply 1)
    · exact (continuous_mapBody embedXZ).comp (continuous_apply 2)

theorem continuousOn_normalizedTupleValue (s t : ℝ) (ht : 0 < t) :
    ContinuousOn normalizedTupleValue (normalizedCompactTuples s t) := by
  first
  | apply (continuous_const.mul continuous_triple_tuple).continuousOn.div
      (continuous_const.mul ((continuous_convexBody_realMeasure volume).comp (continuous_apply 1))).continuousOn
    intro K hK
    have hT : 0 < volume.real (K 1 : Set Plane) := ht.trans_le hK.2.2.2.2.2
    change (2 * volume.real (K 1 : Set Plane) : ℝ) ≠ 0
    exact mul_ne_zero (by norm_num) hT.ne' 

def dataOfNormalizedTuple {s t : ℝ} (ht : 0 < t)
    (K : Fin 3 → ConvexBody Plane) (hK : K ∈ normalizedCompactTuples s t) :
    NormalizedData s (normalizedTupleValue K) where
  A := K 0
  B := K 1
  C := K 2
  T := volume.real (K 1 : Set Plane)
  T_pos := ht.trans_le hK.2.2.2.2.2
  A_width := hK.2.1 0
  A_height := hK.2.2.1 0
  A_area := hK.2.2.2.1
  B_width := hK.2.1 1
  B_height := hK.2.2.1 1
  C_width := hK.2.1 2
  C_height := hK.2.2.1 2
  B_area := rfl
  C_area := hK.2.2.2.2.1
  triple_value := by
    first
    | dsimp [normalizedTupleValue]
      have hp : 0 < volume.real (K 1 : Set Plane) := ht.trans_le hK.2.2.2.2.2
      field_simp [hp.ne']

theorem NormalizedData.exists_centered_tuple {s z t : ℝ} (D : NormalizedData s z)
    (hs1 : s ≤ 1) (ht : t ≤ D.T) :
    ∃ K ∈ normalizedCompactTuples s t, normalizedTupleValue K = z := by
  first
  | obtain ⟨a, ha⟩ := D.A.nonempty
    obtain ⟨b, hb⟩ := D.B.nonempty
    obtain ⟨c, hc⟩ := D.C.nonempty
    let E := D.translate (-a) (-b) (-c)
    let K : Fin 3 → ConvexBody Plane := ![E.A, E.B, E.C]
    have h0 (i : Fin 3) : (0 : Plane) ∈ K i := by
      first
      | fin_cases i
        · exact zero_mem_translateBody_neg ha
        · exact zero_mem_translateBody_neg hb
        · exact zero_mem_translateBody_neg hc
    have hw (i : Fin 3) : width (K i) = 1 := by
      first
      | fin_cases i
        · exact E.A_width
        · exact E.B_width
        · exact E.C_width
    have hh (i : Fin 3) : height (K i) = (![s, 1, 1] : Fin 3 → ℝ) i := by
      first
      | fin_cases i
        · exact E.A_height
        · exact E.B_height
        · exact E.C_height
    have hKh (i : Fin 3) : height (K i) ≤ 1 := by
      first
      | rw [hh]
        fin_cases i
        · exact hs1
        · norm_num
        · norm_num
    refine ⟨K, ⟨?_, hw, hh, ?_, ?_, ?_⟩, ?_⟩
    · intro i _
      exact ⟨h0 i, body_subset_box_of_widths (K i) (h0 i) (hw i).le (hKh i)⟩
    · change volume.real (E.A : Set Plane) = 2 * s * volume.real (E.B : Set Plane)
      rw [E.A_area, E.B_area]
    · change volume.real (E.C : Set Plane) = volume.real (E.B : Set Plane)
      rw [E.C_area, E.B_area]
    · change t ≤ volume.real (E.B : Set Plane)
      rw [E.B_area]
      exact ht
    · change 6 * triple E.A E.B E.C / (2 * volume.real (E.B : Set Plane)) = z
      rw [E.B_area, E.triple_value]
      field_simp [E.T_pos.ne']

theorem normalized_threshold_attained {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    NormalizedRealizable s (normalizedThreshold s) ∧
      ∀ z : ℝ, NormalizedRealizable s z → normalizedThreshold s ≤ z := by
  first
  | let t : ℝ := separationConstant s / 4
    have ht : 0 < t := div_pos (separationConstant_pos hs.le (by linarith)) (by norm_num)
    obtain ⟨z0, ⟨D0⟩, hz0⟩ := normalized_nonempty hs hsSmall
    obtain ⟨K0, hK0, hvalue0⟩ := D0.exists_centered_tuple (by linarith) (D0.T_lower hs hz0)
    obtain ⟨Kmin, hKmin, hmin⟩ := (isCompact_normalizedCompactTuples s t).exists_isMinOn
      ⟨K0, hK0⟩ (continuousOn_normalizedTupleValue s t ht)
    have hdata : NormalizedRealizable s (normalizedTupleValue Kmin) :=
      ⟨dataOfNormalizedTuple ht Kmin hKmin⟩
    have hbound (z : ℝ) (hz : NormalizedRealizable s z) : normalizedTupleValue Kmin ≤ z := by
      first
      | rcases hz with ⟨D⟩
        by_cases hz2 : z ≤ 2
        · obtain ⟨K, hK, hvalue⟩ := D.exists_centered_tuple (by linarith) (D.T_lower hs hz2)
          rw [← hvalue]
          exact hmin hK
        · have h := hmin hK0
          change normalizedTupleValue Kmin ≤ normalizedTupleValue K0 at h
          rw [hvalue0] at h
          linarith
    have hleast : IsLeast {z : ℝ | NormalizedRealizable s z} (normalizedTupleValue Kmin) :=
      ⟨hdata, hbound⟩
    have heq : normalizedThreshold s = normalizedTupleValue Kmin := hleast.csInf_eq
    rw [heq]
    exact ⟨hdata, hbound⟩

/-- The full two-sided logarithmic gap for the actual normalized geometry.
The constants are explicit; the fiber minimum is proved to be attained. -/
theorem normalized_threshold_gap {s : ℝ} (hs : 0 < s)
    (hsmall : s < min (1 / 128) (Real.exp (-1))) :
    (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - normalizedThreshold s ∧
      comparisonRoot s - normalizedThreshold s ≤ 34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | have hsSmall : s ≤ 1 / 2 := by
      first
      | have h := hsmall.trans_le (min_le_left _ _)
        linarith
    obtain ⟨⟨D⟩, hmin⟩ := normalized_threshold_attained hs hsSmall
    constructor
    · obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
        hBa, hCa, hz, hgap⟩ := geometric_threshold_lower hs hsSmall
      have hle := hmin z ⟨⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh,
        hCw, hCh, hBa, hCa, hz⟩⟩
      linarith
    · obtain ⟨Q, hQ, _⟩ := proposition_4_3 D.B D.C D.B_width D.B_height D.C_width D.C_height
      apply geometric_threshold_upper hs hsmall D.T_pos D.A_width D.A_height D.A_area.ge
        D.B_width D.B_height D.C_width D.C_height D.B_area D.C_area hQ
      rw [← D.triple_value]
      exact hQ.2.2 D.A

theorem normalizedSlice_not_semialgebraic : ¬ TauCeti.IsSemialgebraic normalizedSlice := by
  first
  | let a : ℝ := min (1 / 128) (Real.exp (-1))
    have ha : 0 < a := lt_min (by norm_num) (Real.exp_pos _)
    apply not_semialgebraic_of_logarithmic_minimum_gap_frontier
      (S := normalizedSlice) (b := normalizedThreshold) (a := a)
      (c := 3 / 51200) (C := 34816) ha (by norm_num)
    · intro s hs
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (normalized_threshold_attained hs.1 hssmall).1
    · intro s hs z hz
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (normalized_threshold_attained hs.1 hssmall).2 z hz
    · filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ s in 𝓝[>] (0 : ℝ), s < a from
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (show ∀ᶠ s : ℝ in 𝓝 0, s < a from Iio_mem_nhds ha))] with s hs hsa
      simpa only [one_div] using normalized_threshold_gap hs hsa

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/NormalizedThreshold.lean -/

/- BEGIN SOURCE: VolumePolynomials/LiftedThresholdReduction.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# From the geometric lifting proposition to the boundary obstruction

The affine slice and its minimum are defined in the original coefficient
locus. Closedness proves attainment. Polygonal cubic witnesses lift to all
dimensions. The remaining forward-normalization premise in the final
transfer lemma is discharged by the geometric lifting theorem, not treated
as an axiom or a definition of realizability.
-/

open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner

def NormalizedData.toPlanarData {s z : ℝ} (D : NormalizedData s z) :
    NormalizedPlanarData (2 * s) s z where
  A := D.A
  B := D.B
  C := D.C
  T := D.T
  T_pos := D.T_pos
  A_width := D.A_width
  A_height := D.A_height
  A_area := D.A_area.ge
  B_width := D.B_width
  B_height := D.B_height
  C_width := D.C_width
  C_height := D.C_height
  B_area := D.B_area
  C_area := D.C_area
  triple_value := D.triple_value

theorem NormalizedData.mem_cubic_locus {s z : ℝ} (D : NormalizedData s z) :
    CubicSlice.coefficients (2 * s) s z ∈ VolumeLocus 3 3 :=
  normalized_mem_volumeLocus D.toPlanarData D.A_area

theorem NormalizedData.mem_lifted_slice {s z : ℝ} (D : NormalizedData s z) (k : ℕ) :
    z ∈ HigherLift.fiberValues k s :=
  HigherLift.mem_volumeLocus_of_cubic_all k D.mem_cubic_locus

theorem NormalizedPlanarData.threshold_upper {s z : ℝ}
    (D : NormalizedPlanarData (2 * s) s z) (hs : 0 < s)
    (hsmall : s < min (1 / 128) (Real.exp (-1))) :
    comparisonRoot s - z ≤ 34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | obtain ⟨Q, hQ, hQa⟩ := proposition_4_3 D.B D.C D.B_width D.B_height D.C_width D.C_height
    apply geometric_threshold_upper hs hsmall D.T_pos D.A_width D.A_height D.A_area
      D.B_width D.B_height D.C_width D.C_height D.B_area D.C_area hQ
    exact D.triple_value.symm.trans (hQ.2.2 D.A)

end PlanarInteraction

namespace HigherLift

open PlanarInteraction

theorem fiberValues_nonempty (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    (fiberValues k s).Nonempty := by
  first
  | obtain ⟨z, ⟨D⟩, hz⟩ := normalized_nonempty hs hsmall
    exact ⟨z, D.mem_lifted_slice k⟩

theorem boundaryValue_attained (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    boundaryValue k s ∈ fiberValues k s ∧
      ∀ z ∈ fiberValues k s, boundaryValue k s ≤ z :=
  boundaryValue_attained_of_nonempty k s (fiberValues_nonempty k hs hsmall)

theorem lifted_lower_gap_witness (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    ∃ z ∈ fiberValues k s,
      (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - z := by
  first
  | obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
      hBa, hCa, hz, hgap⟩ := geometric_threshold_lower hs hsmall
    let D : NormalizedData s z :=
      ⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz⟩
    exact ⟨z, D.mem_lifted_slice k, hgap⟩

theorem boundaryValue_gap_lower (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - boundaryValue k s := by
  first
  | obtain ⟨z, hz, hgap⟩ := lifted_lower_gap_witness k hs hsmall
    have hmin := (boundaryValue_attained k hs hsmall).2 z hz
    linarith

/-- This transfer lemma isolates the exact geometric statement still to be
supplied: every original realization must yield actual normalized bodies.
It does not introduce a weaker realization relation. -/
theorem coefficientSlice_not_semialgebraic_of_normalization (k : ℕ)
    (hforward : ∀ s z : ℝ, 0 < s → s < 1 → z ∈ fiberValues k s →
      Nonempty (NormalizedPlanarData (2 * s) s z)) :
    ¬ TauCeti.IsSemialgebraic (coefficientSlice k) := by
  first
  | let a : ℝ := min (1 / 128) (Real.exp (-1))
    have ha : 0 < a := lt_min (by norm_num) (Real.exp_pos _)
    apply not_semialgebraic_of_logarithmic_minimum_gap_frontier
      (S := coefficientSlice k) (b := boundaryValue k) (a := a)
      (c := 3 / 51200) (C := 34816) ha (by norm_num)
    · intro s hs
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (boundaryValue_attained k hs.1 hssmall).1
    · intro s hs z hz
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (boundaryValue_attained k hs.1 hssmall).2 z hz
    · filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ s in 𝓝[>] (0 : ℝ), s < a from
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (show ∀ᶠ s : ℝ in 𝓝 0, s < a from Iio_mem_nhds ha))] with s hs hsa
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hsa.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      obtain ⟨D⟩ := hforward s (boundaryValue k s) hs (by linarith)
        (boundaryValue_attained k hs hssmall).1
      exact ⟨by simpa only [one_div] using boundaryValue_gap_lower k hs hssmall,
        by simpa only [one_div] using D.threshold_upper hs hsa⟩

theorem volumeLocus_not_semialgebraic_of_normalization (k : ℕ)
    (hforward : ∀ s z : ℝ, 0 < s → s < 1 → z ∈ fiberValues k s →
      Nonempty (NormalizedPlanarData (2 * s) s z)) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus 3 (3 + k)) := by
  first
  | intro h
    exact coefficientSlice_not_semialgebraic_of_normalization k hforward
      (isSemialgebraic_coefficientSlice k h)

end HigherLift
end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/LiftedThresholdReduction.lean -/

/- BEGIN SOURCE: VolumePolynomials/HigherLiftForward.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Normalization of every realization of the lifted slice

The input below is the original realization relation for all ordinary
coefficients. The fiber frame, independence of its three planes, Fubini
identity, mean body, and scale factors are all constructed from that input.
No geometric normalization is an additional premise of the final result.

The zero-dimensional base recovers the equality in Proposition 3.1;
positive base dimension gives the area inequality in Proposition 6.2.
-/

open Set MeasureTheory

namespace VolumePolynomials.HigherLift

open PlanarExtrusion PlanarInteraction

theorem normalizedPlanarData_of_realizes {k : ℕ} {α s z : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    ∃ D : NormalizedPlanarData α s z,
      k = 0 → volume.real (D.A : Set Plane) = α * D.T := by
  first
  | obtain ⟨F⟩ := exists_fiberFrameData hα hs hK
    obtain ⟨C⟩ := F.exists_coordinateFiberData (F.transverse hα hs hs1)
    exact ⟨C.normalize hα, C.normalize_area_zero hα⟩

theorem normalizedPlanarData_of_mem {k : ℕ} {α s z : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1)
    (h : coefficients k α s z ∈ VolumeLocus 3 (3 + k)) :
    Nonempty (NormalizedPlanarData α s z) := by
  first
  | obtain ⟨K, hK⟩ := h
    obtain ⟨D, _⟩ := normalizedPlanarData_of_realizes hα hs hs1 hK
    exact ⟨D⟩

/-- The complete geometric conclusion of the forward direction of
Proposition 6.2, including its corner inequality. This also holds for `k = 0`.
The original cubic equality is stated separately below. -/
theorem proposition_6_2_forward {k : ℕ} {α s z : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    ∃ (D : NormalizedPlanarData α s z) (Q : ConvexBody Plane),
      IsInteraction D.B D.C Q ∧
      D.T ≤ volume.real (Q : Set Plane) ∧
      2 * D.T * z = 2 * PlanarMixedForm.mixedArea volume D.A Q ∧
      1 + s - 2 * Real.sqrt ((s - α * D.T) *
        (1 - volume.real (Q : Set Plane))) ≤ 2 * D.T * z ∧
      α * D.T ≤ s := by
  first
  | obtain ⟨D, _⟩ := normalizedPlanarData_of_realizes hα hs hs1 hK
    obtain ⟨Q, hQ, hQa⟩ := proposition_4_3 D.B D.C
      D.B_width D.B_height D.C_width D.C_height
    have hTq : D.T ≤ volume.real (Q : Set Plane) := by
      first
      | simpa only [D.B_area, D.C_area, max_self] using hQa
    have hz : 2 * D.T * z = 2 * PlanarMixedForm.mixedArea volume D.A Q :=
      D.triple_value.symm.trans (hQ.2.2 D.A)
    have hAa := area_le_width_mul_height D.A
    rw [D.A_width, D.A_height, one_mul] at hAa
    have hQa' := area_le_width_mul_height Q
    rw [hQ.1, hQ.2.1, one_mul] at hQa'
    have hprod : (s - volume.real (D.A : Set Plane)) *
        (1 - volume.real (Q : Set Plane)) ≤
        (s - α * D.T) * (1 - volume.real (Q : Set Plane)) :=
      mul_le_mul_of_nonneg_right (by linarith [D.A_area]) (by linarith)
    have hsqrt := Real.sqrt_le_sqrt hprod
    have hcorner := PlanarCorner.mixedArea_corner_inequality D.A Q
    rw [D.A_width, D.A_height, hQ.1, hQ.2.1, one_mul, mul_one] at hcorner
    simp only [one_mul, mul_one] at hcorner
    refine ⟨D, Q, hQ, hTq, hz, ?_, D.A_area.trans hAa⟩
    linarith

/-- The geometric premise used by the boundary theorem is now a theorem
of the original coefficient locus, for every base dimension. -/
theorem fiberValues_normalized (k : ℕ) (s z : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hz : z ∈ fiberValues k s) :
    Nonempty (NormalizedPlanarData (2 * s) s z) :=
  normalizedPlanarData_of_mem (by linarith) hs hs1 hz

/-- Theorem 5.5 for the actual cubic boundary (`k = 0`), together with
the same two-sided estimate on every lifted coefficient slice. -/
theorem boundaryValue_logarithmic_gap (k : ℕ) {s : ℝ} (hs : 0 < s)
    (hsmall : s < min (1 / 128) (Real.exp (-1))) :
    (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤
        comparisonRoot s - boundaryValue k s ∧
      comparisonRoot s - boundaryValue k s ≤
        34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | have hs128 : s < 1 / 128 := hsmall.trans_le (min_le_left _ _)
    have hshalf : s ≤ 1 / 2 := by linarith
    obtain ⟨D⟩ := fiberValues_normalized k s (boundaryValue k s) hs (by linarith)
      (boundaryValue_attained k hs hshalf).1
    exact ⟨boundaryValue_gap_lower k hs hshalf, D.threshold_upper hs hsmall⟩

theorem coefficientSlice_not_semialgebraic (k : ℕ) :
    ¬ TauCeti.IsSemialgebraic (coefficientSlice k) :=
  coefficientSlice_not_semialgebraic_of_normalization k (fiberValues_normalized k)

theorem volumeLocus_not_semialgebraic (k : ℕ) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus 3 (3 + k)) :=
  volumeLocus_not_semialgebraic_of_normalization k (fiberValues_normalized k)

end HigherLift

namespace PlanarInteraction

open PlanarExtrusion HigherLift

/-- Proposition 3.1 with every width, area and mixed-volume equality
retained in `NormalizedPlanarData` and the explicit area equality below. -/
theorem proposition_3_1 {α s z : ℝ} (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1) :
    CubicSlice.coefficients α s z ∈ VolumeLocus 3 3 ↔
      ∃ D : NormalizedPlanarData α s z,
        volume.real (D.A : Set Plane) = α * D.T := by
  first
  | constructor
    · intro h
      have hzero : HigherLift.coefficients 0 α s z ∈ VolumeLocus 3 (3 + 0) := by
        first
        | simpa only [HigherLift.coefficients_zero] using h
      obtain ⟨K, hK⟩ := hzero
      obtain ⟨D, hD⟩ := HigherLift.normalizedPlanarData_of_realizes hα hs hs1 hK
      exact ⟨D, hD rfl⟩
    · rintro ⟨D, hD⟩
      exact normalized_mem_volumeLocus D hD

end PlanarInteraction
end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HigherLiftForward.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinaryPolynomial.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The literal binomially normalized binary polynomial and its unique
coefficient sequence. Only the entries from zero through the degree occur. -/

open Set MeasureTheory Polynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.BinarySimplex

def value (d : ℕ) (a : ℕ → ℝ) (t s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * a i * t ^ (d - i) * s ^ i

def Realizes (d : ℕ) (a : ℕ → ℝ) (K L : Body d) : Prop :=
  ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → bodyVolume (t • K + s • L) = value d a t s

def univariate (d : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i ((d.choose i : ℝ) * a i)

theorem eval_univariate (d : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    (univariate d a).eval s = value d a 1 s := by
  first
  | simp only [univariate, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      value, one_pow, mul_one]

theorem coeff_univariate {d i : ℕ} (a : ℕ → ℝ) (hi : i ≤ d) :
    (univariate d a).coeff i = (d.choose i : ℝ) * a i := by
  first
  | simp [univariate, Polynomial.coeff_monomial, Finset.mem_range.mpr (show i < d + 1 by omega)]

theorem sequence_eq_of_value_eq {d : ℕ} {a b : ℕ → ℝ}
    (h : ∀ s : ℝ, 0 ≤ s → value d a 1 s = value d b 1 s) :
    ∀ i ≤ d, a i = b i := by
  first
  | have hp : univariate d a = univariate d b := by
      first
      | apply Polynomial.eq_of_infinite_eval_eq
        apply (Set.Ici_infinite (0 : ℝ)).mono
        intro s hs
        simpa only [Set.mem_setOf_eq, eval_univariate] using h s hs
    intro i hi
    have hc := congrArg (fun p : Polynomial ℝ => p.coeff i) hp
    rw [coeff_univariate a hi, coeff_univariate b hi] at hc
    have hchoose : (d.choose i : ℝ) ≠ 0 := by
      first
      | exact_mod_cast (Nat.choose_pos hi).ne'
    exact mul_left_cancel₀ hchoose hc

theorem Realizes.unique {d : ℕ} {a b : ℕ → ℝ} {K L : Body d}
    (ha : Realizes d a K L) (hb : Realizes d b K L) : ∀ i ≤ d, a i = b i :=
  sequence_eq_of_value_eq (fun s hs => (ha 1 s zero_le_one hs).symm.trans (hb 1 s zero_le_one hs))

end VolumePolynomials.BinarySimplex
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinaryPolynomial.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinarySequences.lean -/
section


@[expose] public section

set_option autoImplicit false

/-!
# The coefficient inequalities in the binary realization theorem

The inequalities are exactly (A.1), including all separated-index
inequalities. They are equivalent to nonnegative adjacent log-concavity
with no internal zeros. In particular, no positivity assumption is silently
added in the passage to decreasing ratios.
-/

namespace VolumePolynomials.BinarySequences

def Criterion (d : ℕ) (a : ℕ → ℝ) : Prop :=
  (∀ i ≤ d, 0 ≤ a i) ∧
    ∀ i j : ℕ, 1 ≤ i → i ≤ j → j < d → a (i - 1) * a (j + 1) ≤ a i * a j

def NoInternalZeros (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ i j k : ℕ, i ≤ j → j ≤ k → k ≤ d → 0 < a i → 0 < a k → 0 < a j

theorem Criterion.adjacent {d : ℕ} {a : ℕ → ℝ} (h : Criterion d a)
    {i : ℕ} (hi : 1 ≤ i) (hid : i < d) :
    a (i - 1) * a (i + 1) ≤ a i ^ 2 := by
  first
  | simpa only [pow_two] using h.2 i i hi le_rfl hid

/-- A zero to the left of a positive coefficient forces every earlier
coefficient to vanish. This uses the separated-index inequalities. -/
theorem Criterion.zero_propagates_left {d : ℕ} {a : ℕ → ℝ}
    (h : Criterion d a) {r : ℕ} (hrd : r ≤ d) (hr : 0 < a r) :
    ∀ i : ℕ, i < r → a i = 0 → ∀ l ≤ i, a l = 0 := by
  first
  | intro i
    induction i with
    | zero =>
        intro _ hi l hl
        have hl0 : l = 0 := by omega
        simpa only [hl0] using hi
    | succ i ih =>
        intro hir hi l hl
        by_cases heq : l = i + 1
        · simpa only [heq] using hi
        · have hpred : a i = 0 := by
            first
            | have hineq := h.2 (i + 1) (r - 1) (by omega) (by omega) (by omega)
              have hrid : r - 1 + 1 = r := by omega
              simp only [Nat.add_sub_cancel, hrid, hi, zero_mul] at hineq
              have hnonneg := h.1 i (by omega)
              have hle : a i ≤ 0 := nonpos_of_mul_nonpos_left hineq hr
              exact le_antisymm hle hnonneg
          exact ih (by omega) hpred l (by omega)

theorem Criterion.noInternalZeros {d : ℕ} {a : ℕ → ℝ} (h : Criterion d a) :
    NoInternalZeros d a := by
  first
  | intro i j k hij hjk hkd hi hk
    by_contra hj
    have hj0 : a j = 0 := le_antisymm (le_of_not_gt hj) (h.1 j (hjk.trans hkd))
    have hjlt : j < k := by
      first
      | apply lt_of_le_of_ne hjk
        intro heq
        subst j
        exact hk.ne' hj0
    have hi0 := h.zero_propagates_left hkd hk j hjlt hj0 i hij
    exact hi.ne' hi0

theorem adjacent_ratio_le {a : ℕ → ℝ} {i : ℕ}
    (ha : 0 < a i) (hb : 0 < a (i + 1))
    (hlog : a i * a (i + 2) ≤ a (i + 1) ^ 2) :
    a (i + 2) / a (i + 1) ≤ a (i + 1) / a i := by
  first
  | apply (div_le_div_iff₀ hb ha).mpr
    simpa only [pow_two, mul_comm] using hlog

/-- Adjacent log-concavity orders every pair of successive ratios inside a
positive interval. -/
theorem ratios_antitone_on_interval {a : ℕ → ℝ} {l r : ℕ}
    (hpos : ∀ i : ℕ, l ≤ i → i ≤ r → 0 < a i)
    (hlog : ∀ i : ℕ, l < i → i < r → a (i - 1) * a (i + 1) ≤ a i ^ 2) :
    ∀ i j : ℕ, l ≤ i → i ≤ j → j < r →
      a (j + 1) / a j ≤ a (i + 1) / a i := by
  first
  | intro i j hli hij hjr
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
        have hstep : a (j + 2) / a (j + 1) ≤ a (j + 1) / a j := by
          first
          | apply adjacent_ratio_le (hpos j (hli.trans hij) (by omega))
              (hpos (j + 1) (by omega) (by omega))
            simpa only [Nat.add_sub_cancel] using hlog (j + 1) (by omega) (by omega)
        exact hstep.trans (ih (by omega))

theorem criterion_iff {d : ℕ} {a : ℕ → ℝ} :
    Criterion d a ↔
      (∀ i ≤ d, 0 ≤ a i) ∧
      (∀ i : ℕ, 1 ≤ i → i < d → a (i - 1) * a (i + 1) ≤ a i ^ 2) ∧
      NoInternalZeros d a := by
  first
  | constructor
    · intro h
      exact ⟨h.1, fun _ hi hid => h.adjacent hi hid, h.noInternalZeros⟩
    · rintro ⟨hn, hlog, hnozero⟩
      refine ⟨hn, ?_⟩
      intro i j hi hij hjd
      by_cases hleft : a (i - 1) = 0
      · rw [hleft, zero_mul]
        exact mul_nonneg (hn i (by omega)) (hn j (by omega))
      by_cases hright : a (j + 1) = 0
      · rw [hright, mul_zero]
        exact mul_nonneg (hn i (by omega)) (hn j (by omega))
      have hleftpos : 0 < a (i - 1) :=
        lt_of_le_of_ne (hn (i - 1) (by omega)) (Ne.symm hleft)
      have hrightpos : 0 < a (j + 1) :=
        lt_of_le_of_ne (hn (j + 1) (by omega)) (Ne.symm hright)
      have hpos : ∀ k : ℕ, i - 1 ≤ k → k ≤ j + 1 → 0 < a k :=
        fun k hik hkj => hnozero (i - 1) k (j + 1) hik hkj (by omega) hleftpos hrightpos
      have hrat := ratios_antitone_on_interval hpos
        (fun k hik hkj => hlog k (by omega) (by omega))
        (i - 1) j le_rfl (by omega) (by omega)
      have hip : i - 1 + 1 = i := by omega
      rw [hip] at hrat
      have hx := (div_le_div_iff₀ (hpos j (by omega) (by omega)) hleftpos).mp hrat
      simpa only [mul_comm] using hx

end VolumePolynomials.BinarySequences
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinarySequences.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinaryCoordinates.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Exact equivalence between the full homogeneous coefficient vector and
the binomial normalization in Appendix A. Every degree-`d` monomial occurs
once; no coordinate is discarded. -/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials

def binaryIndex (d : ℕ) (i : Fin (d + 1)) : MultiIndex 2 d :=
  ⟨![⟨d - i.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, i], by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)⟩

def binaryIndexEquiv (d : ℕ) : Fin (d + 1) ≃ MultiIndex 2 d where
  toFun := binaryIndex d
  invFun a := a.1 1
  left_inv i := rfl
  right_inv a := by
    first
    | apply Subtype.ext
      funext j
      fin_cases j
      · apply Fin.ext
        have h := a.2
        simp only [Fin.sum_univ_two] at h
        change d - (a.1 1).val = (a.1 0).val
        omega
      · rfl

def binaryNormalizedSequence {d : ℕ} (c : Coefficients 2 d) (i : ℕ) : ℝ :=
  if hi : i ≤ d then c (binaryIndex d ⟨i, Nat.lt_succ_of_le hi⟩) / (d.choose i : ℝ) else 0

theorem binaryNormalizedSequence_apply {d : ℕ} (c : Coefficients 2 d) (i : Fin (d + 1)) :
    binaryNormalizedSequence c i.val = c (binaryIndex d i) / (d.choose i.val : ℝ) := by
  first
  | simp only [binaryNormalizedSequence, dif_pos (Nat.le_of_lt_succ i.isLt)]

theorem choose_mul_binaryNormalizedSequence {d : ℕ} (c : Coefficients 2 d)
    (i : Fin (d + 1)) :
    (d.choose i.val : ℝ) * binaryNormalizedSequence c i.val = c (binaryIndex d i) := by
  first
  | rw [binaryNormalizedSequence_apply]
    apply mul_div_cancel₀
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)).ne'

theorem evaluate_binary {d : ℕ} (c : Coefficients 2 d) (t : Fin 2 → ℝ) :
    evaluate c t = BinarySimplex.value d (binaryNormalizedSequence c) (t 0) (t 1) := by
  first
  | unfold evaluate BinarySimplex.value
    have heq := Fintype.sum_equiv (binaryIndexEquiv d)
      (fun i => c (binaryIndex d i) * ∏ j : Fin 2, t j ^ ((binaryIndex d i).1 j : ℕ))
      (fun a => c a * ∏ j : Fin 2, t j ^ (a.1 j : ℕ)) (fun _ => rfl)
    rw [← heq, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [← choose_mul_binaryNormalizedSequence c i]
    simp only [binaryIndex, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem realizes_binary_iff {d : ℕ} (c : Coefficients 2 d) (K : Fin 2 → Body d) :
    Realizes K c ↔ BinarySimplex.Realizes d (binaryNormalizedSequence c) (K 0) (K 1) := by
  first
  | constructor
    · intro h t s ht hs
      have hw : ∀ i : Fin 2, 0 ≤ (![t, s] : Fin 2 → ℝ) i := by
        first
        | intro i
          fin_cases i <;> assumption
      have he := h ![t, s] hw
      rw [evaluate_binary] at he
      simpa only [volumeFunction, weightedSum, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one] using he.symm
    · intro h t ht
      rw [evaluate_binary]
      simpa only [volumeFunction, weightedSum, Fin.sum_univ_two] using
        (h (t 0) (t 1) (ht 0) (ht 1)).symm

theorem binary_volumeLocus_iff {d : ℕ} (c : Coefficients 2 d) :
    c ∈ VolumeLocus 2 d ↔
      ∃ A B : Body d, BinarySimplex.Realizes d (binaryNormalizedSequence c) A B := by
  first
  | constructor
    · rintro ⟨K, hK⟩
      exact ⟨K 0, K 1, (realizes_binary_iff c K).mp hK⟩
    · rintro ⟨A, B, h⟩
      exact ⟨![A, B], (realizes_binary_iff c ![A, B]).mpr h⟩

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinaryCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinaryMixedCoefficients.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Binomial coefficients and actual repeated mixed volumes

Minkowski multilinearity over the nonnegative reals expands the diagonal
volume into a sum over subsets. Permutation symmetry makes each summand
depend only on the subset cardinality, and counting the subsets supplies
the exact binomial coefficient. No normalization is postulated.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.BinaryMixed

def firstPattern (d i : ℕ) (j : Fin d) : Bool := decide (j.val < i)

def patternSet {d : ℕ} (p : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun j => p j = true)

def patternCount {d : ℕ} (p : Fin d → Bool) : ℕ := (patternSet p).card

def patternBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (A B : ConvexBody E) (p : Fin d → Bool) (j : Fin d) : ConvexBody E :=
  if p j = true then B else A

theorem patternCount_le {d : ℕ} (p : Fin d → Bool) : patternCount p ≤ d := by
  first
  | simpa only [patternCount, patternSet, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun j => p j = true) Finset.univ)

theorem patternCount_cons {d : ℕ} (b : Bool) (p : Fin d → Bool) :
    patternCount (Fin.cons b p) = (if b = true then 1 else 0) + patternCount p := by
  first
  | simp only [patternCount, patternSet, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem patternCount_first {d i : ℕ} (hi : i ≤ d) : patternCount (firstPattern d i) = i := by
  first
  | have hset : patternSet (firstPattern d i) = Finset.univ.filter (fun j : Fin d => j.val < i) := by
      first
      | ext j
        simp [patternSet, firstPattern]
    unfold patternCount
    rw [hset]
    rcases lt_or_eq_of_le hi with hid | heq
    · have he : Finset.univ.filter (fun j : Fin d => j.val < i) = Finset.Iio (⟨i, hid⟩ : Fin d) := by
        first
        | ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
          rfl
      rw [he, Fin.card_Iio]
    · subst i
      have he : Finset.univ.filter (fun j : Fin d => j.val < d) = Finset.univ := by
        first
        | ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact j.isLt
      simp only [he, Finset.card_univ, Fintype.card_fin]

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def coefficient (d : ℕ) (A B : ConvexBody E) (i : ℕ) : ℝ :=
  mixedVolume μ (patternBody A B (firstPattern d i))

theorem mixedVolume_pattern {d : ℕ} (A B : ConvexBody E) (p : Fin d → Bool) :
    mixedVolume μ (patternBody A B p) = coefficient μ d A B (patternCount p) := by
  first
  | classical
    let S := patternSet p
    let T := patternSet (firstPattern d (patternCount p))
    have hcard : S.card = T.card := (patternCount_first (patternCount_le p)).symm
    obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
    have hmem (j : Fin d) : e j ∈ T ↔ j ∈ S := by
      first
      | rw [← he]
        simp only [Finset.mem_map, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨k, hk, hkj⟩
          exact e.injective hkj ▸ hk
        · intro hj
          exact ⟨j, hj, rfl⟩
    have htuple : patternBody A B p =
        fun j => patternBody A B (firstPattern d (patternCount p)) (e j) := by
      first
      | funext j
        have hiff := hmem j
        simp only [S, T, patternSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiff
        simp only [patternBody, hiff]
    rw [htuple, mixedVolume_reindex]
    rfl

theorem mixedVolume_piecewise {d : ℕ} (A B : ConvexBody E) (S : Finset (Fin d)) :
    mixedVolume μ (S.piecewise (fun _ => B) (fun _ => A)) = coefficient μ d A B S.card := by
  first
  | let p : Fin d → Bool := fun j => decide (j ∈ S)
    have hc : patternCount p = S.card := by
      first
      | change (patternSet p).card = S.card
        apply congrArg Finset.card
        ext j
        simp [p, patternSet]
    have ht : S.piecewise (fun _ => B) (fun _ => A) = patternBody A B p := by
      first
      | funext j
        simp [Finset.piecewise, patternBody, p]
    rw [ht, mixedVolume_pattern, hc]

theorem mixedVolume_scaled_piecewise {d : ℕ} (A B : ConvexBody E)
    (S : Finset (Fin d)) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    mixedVolume μ (S.piecewise (fun _ => s • B) (fun _ => t • A)) =
      t ^ (d - S.card) * s ^ S.card * coefficient μ d A B S.card := by
  first
  | let r : Fin d → ℝ := fun j => if j ∈ S then s else t
    have hr : ∀ j, 0 ≤ r j := by intro j; dsimp [r]; split_ifs <;> assumption
    have htuple : S.piecewise (fun _ => s • B) (fun _ => t • A) =
        fun j => r j • S.piecewise (fun _ => B) (fun _ => A) j := by
      first
      | funext j
        by_cases hj : j ∈ S <;> simp [r, Finset.piecewise, hj]
    have hprod : ∏ j, r j = s ^ S.card * t ^ (d - S.card) := by
      first
      | dsimp only [r]
        rw [Finset.prod_ite]
        have hyes : Finset.univ.filter (fun j : Fin d => j ∈ S) = S := by ext j; simp
        have hno : Finset.univ.filter (fun j : Fin d => j ∉ S) = Sᶜ := by ext j; simp
        rw [hyes, hno, Finset.prod_const, Finset.prod_const, Finset.card_compl]
        simp only [Fintype.card_fin]
    rw [htuple, mixedVolume_independent_smul μ _ r hr, hprod, mixedVolume_piecewise]
    ring

theorem binary_volume_formula {d : ℕ} (hdim : finrank ℝ E = d)
    (A B : ConvexBody E) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    μ.real ((t • A + s • B : ConvexBody E) : Set E) =
      BinarySimplex.value d (coefficient μ d A B) t s := by
  first
  | rw [← mixedVolume_diagonal μ hdim]
    have hsum : (fun _ : Fin d => t • A + s • B) =
        (fun i => (fun _ : Fin d => s • B) i + (fun _ : Fin d => t • A) i) := by
      first
      | funext i
        exact add_comm _ _
    rw [hsum, mixedVolume_add_all]
    simp_rw [mixedVolume_scaled_piecewise μ A B _ ht hs]
    rw [← Finset.powerset_univ, Finset.sum_powerset]
    have hcardSum (i : ℕ) :
        (∑ S ∈ Finset.powersetCard i (Finset.univ : Finset (Fin d)),
          t ^ (d - S.card) * s ^ S.card * coefficient μ d A B S.card) =
        (d.choose i : ℝ) * (t ^ (d - i) * s ^ i * coefficient μ d A B i) := by
      simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        (Finset.sum_powersetCard i (Finset.univ : Finset (Fin d))
          (fun j => t ^ (d - j) * s ^ j * coefficient μ d A B j))
    simp_rw [hcardSum]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold BinarySimplex.value
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem coefficient_nonnegative (d : ℕ) (A B : ConvexBody E) (i : ℕ) :
    0 ≤ coefficient μ d A B i := mixedVolume_nonnegative μ _

theorem continuous_coefficient (d i : ℕ) :
    Continuous (fun p : ConvexBody E × ConvexBody E => coefficient μ d p.1 p.2 i) := by
  first
  | apply (continuous_mixedVolume μ d).comp
    apply continuous_pi
    intro j
    dsimp only [patternBody]
    split_ifs <;> first | exact continuous_fst | exact continuous_snd

end Measure

theorem realizes_mixedCoefficients (d : ℕ) (A B : Body d) :
    BinarySimplex.Realizes d (coefficient volume d A B) A B := by
  first
  | intro t s ht hs
    exact binary_volume_formula volume (by simp [Space]) A B ht hs

theorem realizing_sequence_eq {d : ℕ} {a : ℕ → ℝ} {A B : Body d}
    (h : BinarySimplex.Realizes d a A B) :
    ∀ i ≤ d, a i = coefficient volume d A B i :=
  h.unique (realizes_mixedCoefficients d A B)

end VolumePolynomials.BinaryMixed
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinaryMixedCoefficients.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeOrder.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Coordinatewise monotonicity and strict positivity from a common
contained body. All inequalities concern the previously defined, actual
dimension-matched mixed volume. -/

open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_mono_update {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K : Fin (n + 1) → ConvexBody E) (i : Fin (n + 1))
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Function.update K i A) ≤ mixedVolume μ (Function.update K i B) := by
  first
  | letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
    let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i
    let L : Fin n → ConvexBody E := fun j => K (e j.succ)
    have htuple (C : ConvexBody E) :
        (fun j => (Function.update K i C) (e j)) = Fin.cons C L := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [e]
        | succ j =>
            have hne : e j.succ ≠ i := by
              first
              | intro heq
                have he0 : e 0 = i := by simp [e]
                have hzero := e.injective (heq.trans he0.symm)
                exact Fin.succ_ne_zero j hzero
            simp only [Function.update_of_ne hne, Fin.cons_succ, L]
    rw [← mixedVolume_reindex μ (Function.update K i A) e,
      ← mixedVolume_reindex μ (Function.update K i B) e, htuple A, htuple B]
    exact mixedVolume_mono_first_all μ L hdim A B hAB

theorem mixedVolume_mono_all {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K L : Fin (n + 1) → ConvexBody E) (hKL : ∀ i, K i ≤ L i) :
    mixedVolume μ K ≤ mixedVolume μ L := by
  first
  | classical
    have haux (s : Finset (Fin (n + 1))) :
        mixedVolume μ K ≤ mixedVolume μ (s.piecewise L K) := by
      first
      | induction s using Finset.induction_on with
        | empty => simp only [Finset.piecewise_empty, le_refl]
        | @insert i s hi ih =>
            have hold : Function.update (s.piecewise L K) i (K i) = s.piecewise L K := by
              first
              | ext j
                by_cases hji : j = i
                · subst j
                  simp [Finset.piecewise, hi]
                · simp [hji]
            have hnew : Function.update (s.piecewise L K) i (L i) =
                (insert i s).piecewise L K := by
              first
              | ext j
                by_cases hji : j = i
                · subst j
                  simp [Finset.piecewise]
                · simp [Finset.piecewise, hji]
            have hm := mixedVolume_mono_update μ hdim (s.piecewise L K) i (K i) (L i) (hKL i)
            rw [hold, hnew] at hm
            exact ih.trans hm
    simpa only [Finset.piecewise_univ] using haux Finset.univ

theorem mixedVolume_ge_common_body {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K : Fin (n + 1) → ConvexBody E) (S : ConvexBody E)
    (p : Fin (n + 1) → E) (hcontain : ∀ i, translateBody (p i) S ≤ K i) :
    μ.real (S : Set E) ≤ mixedVolume μ K := by
  first
  | have h := mixedVolume_mono_all μ hdim (fun i => translateBody (p i) S) K hcontain
    rwa [mixedVolume_translate, mixedVolume_diagonal μ hdim] at h

theorem mixedVolume_pos_of_common_body {n : ℕ} (hdim : finrank ℝ E = n + 1)
    (K : Fin (n + 1) → ConvexBody E) (S : ConvexBody E)
    (hS : 0 < μ.real (S : Set E))
    (p : Fin (n + 1) → E) (hcontain : ∀ i, translateBody (p i) S ≤ K i) :
    0 < mixedVolume μ K :=
  hS.trans_le (mixedVolume_ge_common_body μ hdim K S p hcontain)

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeOrder.lean -/
