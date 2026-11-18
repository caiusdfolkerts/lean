module

public import volume_polynomials.assembly_part08

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

/- BEGIN SOURCE: TauCeti/Probability/Cdf.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cumulative distribution functions

This file records basic properties of cumulative distribution functions. In particular, the cdf
of an atomless real probability measure is continuous, and convolution averages translated cdfs.

A probability measure `μ` on `ℕ` becomes a real law by pushing it forward along the cast
`ℕ → ℝ`. The resulting cumulative distribution function is determined by the cumulative masses of
`μ` itself: it vanishes below the origin, where the pushforward has no mass at all, and at a
nonnegative point `x` it is the mass `μ` gives to the initial segment below the natural floor of
`x`. Every discrete law on `ℕ` therefore reads its real cdf off its own cumulative masses.

## Main results

* `MeasureTheory.Measure.cdf_conv` computes the cdf of a convolution;
* `MeasureTheory.Measure.continuous_cdf_of_noAtoms` proves continuity for atomless real laws;
* `MeasureTheory.Measure.cdf_eq_zero_of_measure_Iio_eq_zero` shows that an atomless law with no
  mass below a point has cdf zero there;
* `TauCeti.Probability.one_sub_cdf_zero_eq_one` and
  `TauCeti.Probability.one_sub_cdf_zero_eq_one_of_absolutelyContinuous` show that survival starts
  at one for an atomless or absolutely continuous law carried by the nonnegative half-line;
* `MeasureTheory.Measure.measure_Ioc_pos_iff_cdf_lt` characterizes positive interval mass by a
  strict increase of the cdf;
* `MeasureTheory.Measure.support_eq_univ_of_strictMono_cdf` shows that a strictly increasing cdf
  has full topological support;
* `MeasureTheory.Measure.strictMonoOn_cdf_of_subset_support` proves strict increase on any
  interval contained in the support;
* `MeasureTheory.Measure.cdf_lt_one_of_strictMonoOn_Ici` gives a strict upper bound for cdfs
  that increase strictly on a right half-line;
* `MeasureTheory.Measure.cdf_sublevel_measure` evaluates the measure of a CDF sublevel set for
  an atomless real law;
* `MeasureTheory.Measure.measureReal_Iio_neg` relates the lower tail of a symmetric real law to
  its cdf;
* `MeasureTheory.Measure.cdf_neg_of_measure_singleton_eq_zero` computes the cdf of a reflected
  law away from atoms;
* `MeasureTheory.Measure.cdf_map_abs_of_nonneg` and `MeasureTheory.Measure.cdf_map_abs_of_neg`
  evaluate the cdf of the image of a real law under absolute value, and
  `MeasureTheory.Measure.cdf_map_abs_of_isNegInvariant` specializes it to symmetric laws;
* `MeasureTheory.Measure.cdf_map_const_mul_sqrt` evaluates the cdf of the image of a real law
  under a positive multiple of the square root;
* `MeasureTheory.Measure.leftLim_cdf` identifies the left limit of the cdf at a point with the
  mass of the open ray to its left;
* `Set.OrdConnected.mem_of_measureReal_Iio_le_of_le_cdf` shows that a cumulative-crossing point
  lies in every interval carrying the full mass of the measure;
* `MeasureTheory.Measure.cdf_map_natCast` evaluates the cdf at a nonnegative point;
* `MeasureTheory.Measure.cdf_map_natCast_of_neg` evaluates it below the origin;
* `MeasureTheory.Measure.cdf_map_intCast` evaluates an integer-valued law's cdf using the
  integer floor, including at negative points;
* `MeasureTheory.Measure.exists_nat_le_measureReal_Iic` shows that every level below one is
  reached by a finite cumulative mass of a natural-valued law.

## Adapted from

`continuous_cdf_of_noAtoms` and `cdf_sublevel_measure` are adapted from Cameron Freer's
independent implementation in `Graphon/MeasureIso.lean` at commit
`9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>,
under the same names; the graphon-specific packaging was removed. The original work is
copyright Cameron Freer and licensed under Apache 2.0.

These two results are the input to the probability integral transform
`MeasureTheory.Measure.cdf_map_eq_volume_restrict` in `TauCeti.Probability.Quantile`, which is
adapted from the same source, and they realize the measure-preserving equivalence of an
atomless standard-Borel space with the unit interval proved as Theorem A.7 in S. Janson,
*Graphons, cut norm and distance, couplings and rearrangements*, Arkiv för Matematik 52 (2014).
-/

public section

open Filter Function MeasureTheory ProbabilityTheory Set Topology

namespace ProbabilityTheory

/-- The cdf of the zero measure is the default step cdf at zero. -/
@[simp]
theorem cdf_zero (x : ℝ) : cdf (0 : Measure ℝ) x = if 0 ≤ x then 1 else 0 := by
  first
  | have hdirac (y : ℝ) : cdf (Measure.dirac 0) y = if 0 ≤ y then 1 else 0 := by
      rw [cdf_eq_real, measureReal_def]
      by_cases h : (0 : ℝ) ≤ y <;> simp [Measure.dirac_apply' _ measurableSet_Iic, h]
    have hstep : cdf (0 : Measure ℝ) x = cdf (Measure.dirac 0) x := by
      set f : Unit → ℚ → ℝ := fun a r ↦ (preCDF (0 : Measure (Unit × ℝ)) r a).toReal
      have hf : f () = fun _ ↦ f () 0 := funext fun r ↦ by simp [f, preCDF, Measure.IicSnd]
      have hnot : ¬IsRatStieltjesPoint f () := fun h ↦ by
        have h1 := h.tendsto_atTop_one
        have h0 := h.tendsto_atBot_zero
        rw [hf, tendsto_const_nhds_iff] at h1 h0
        exact one_ne_zero (h1.symm.trans h0)
      rw [← StieltjesFunction.iInf_rat_gt_eq, ← StieltjesFunction.iInf_rat_gt_eq]
      congr! 2 with q
      rw [cdf, Measure.prod_zero, condCDF, stieltjesOfMeasurableRat_eq, hdirac]
      -- The rewrites spell out the function `fun a r ↦ (preCDF 0 r a).toReal` of `condCDF`, which
      -- is `f` by definition: `set` folds only the occurrences present when it ran. Restate the
      -- goal through `f` so that `hnot` applies.
      change toRatCDF f () q = _
      simp only [toRatCDF, hnot, ↓reduceIte, defaultRatCDF, ← not_lt, ite_not, Rat.cast_lt_zero]
    exact hstep.trans (hdirac x)

end ProbabilityTheory

namespace MeasureTheory.Measure

/-- The cdf of a convolution is the average of the translated cdfs of its second factor. -/
theorem cdf_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : ℝ) : cdf (μ ∗ ν) x = ∫ y, cdf ν (x - y) ∂μ := by
  first
  | rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
    rw [integral_conv (f := (Iic x).indicator (1 : ℝ → ℝ))
      ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [indicator_apply, Pi.one_apply, mem_Iic, le_sub_iff_add_le, add_comm y z]

/-- Below the level `1` some point has cumulative mass at least the level, because the cumulative
distribution function tends to `1` at `+∞`. -/
theorem nonempty_setOf_le_cdf (μ : Measure ℝ) {t : ℝ} (ht : t < 1) :
    {x : ℝ | t ≤ cdf μ x}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht)).exists.imp fun _ h ↦ h.le

/-- For a symmetric real law, the mass below `-x` is the mass above `x`, which is
`1 - cdf μ x`. -/
theorem measureReal_Iio_neg (μ : Measure ℝ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (x : ℝ) : μ.real (Iio (-x)) = 1 - cdf μ x := by
  first
  | rw [← Set.neg_Ioi, measureReal_def, Measure.measure_neg, ← measureReal_def, ← compl_Iic,
      measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]

/-- **The cumulative distribution function of the reflected law.** If `μ` has no atom at `-x`,
the law of `-X` puts mass `1 - cdf μ (-x)` on `Iic x`. -/
theorem cdf_neg_of_measure_singleton_eq_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] {x : ℝ}
    (hx : μ {-x} = 0) : cdf μ.neg x = 1 - cdf μ (-x) := by
  first
  | have hpre : (Neg.neg ⁻¹' Iic x : Set ℝ) = (Iio (-x))ᶜ := by
      ext y
      simp
    rw [cdf_eq_real, neg_def, map_measureReal_apply measurable_neg measurableSet_Iic, hpre,
      measureReal_compl measurableSet_Iio, probReal_univ, measureReal_congr (Iio_ae_eq_Iic' hx),
      cdf_eq_real]

/-- The cdf of the image of `μ` under absolute value at a nonnegative point `x` is the mass of
`[-x, x]`, that is, the cdf of `μ` at `x` minus its left limit at `-x`. -/
theorem cdf_map_abs_of_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (|·|)) x = cdf μ x - μ.real (Iio (-x)) := by
  first
  | have hpre : (|·|) ⁻¹' Iic x = Iic x \ Iio (-x) := by
      ext y
      simp [abs_le, and_comm]
    rw [cdf_eq_real, map_measureReal_apply continuous_abs.measurable measurableSet_Iic, hpre,
      measureReal_sdiff (Iio_subset_Iic_self.trans (Iic_subset_Iic.2 (by linarith)))
        measurableSet_Iio, cdf_eq_real]

/-- The image of `μ` under absolute value puts no mass on the negative half-line. -/
theorem cdf_map_abs_of_neg (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} (hx : x < 0) :
    cdf (μ.map (|·|)) x = 0 := by
  first
  | have hpre : (|·|) ⁻¹' Iic x = ∅ :=
      eq_empty_of_forall_notMem fun y hy => not_le.2 hx ((abs_nonneg y).trans hy)
    rw [cdf_eq_real, map_measureReal_apply continuous_abs.measurable measurableSet_Iic, hpre,
      measureReal_empty]

/-- The cdf of the image of a symmetric law under absolute value at `x ≥ 0` is
`2 * cdf μ x - 1`. -/
theorem cdf_map_abs_of_isNegInvariant (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [μ.IsNegInvariant] {x : ℝ} (hx : 0 ≤ x) : cdf (μ.map (|·|)) x = 2 * cdf μ x - 1 := by
  first
  | rw [μ.cdf_map_abs_of_nonneg hx, μ.measureReal_Iio_neg x]
    ring

/-- At positive scale `s`, the image of `μ` under `y ↦ s * √y` puts no mass on the negative
half-line, and at `x ≥ 0` its cdf is the cdf of `μ` at `(x / s) ^ 2`. -/
theorem cdf_map_const_mul_sqrt (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (x : ℝ) :
    cdf (μ.map fun y ↦ s * √y) x = if x < 0 then 0 else cdf μ ((x / s) ^ 2) := by
  first
  | rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    by_cases hx : x < 0
    · have hpre : (fun y ↦ s * √y) ⁻¹' Iic x = ∅ :=
        eq_empty_of_forall_notMem fun y hy ↦
          not_le.2 hx ((mul_nonneg hs.le (Real.sqrt_nonneg y)).trans hy)
      rw [hpre, measureReal_empty, ite_eq_left hx]
    · have hpre : (fun y ↦ s * √y) ⁻¹' Iic x = Iic ((x / s) ^ 2) := by
        ext y
        simp only [mem_preimage, mem_Iic, ← le_div_iff₀' hs, Real.sqrt_le_iff,
          div_nonneg (le_of_not_gt hx) hs.le, true_and]
      rw [hpre, ← cdf_eq_real, ite_eq_right hx]

/-- The cdf of an integer-valued law cast to the reals is its cumulative mass through the integer
floor of the argument. Unlike natural floor, integer floor also accounts for negative values. -/
theorem cdf_map_intCast (μ : Measure ℤ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (μ.map (Int.cast : ℤ → ℝ)) x = μ.real (Iic ⌊x⌋) := by
  first
  | rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, Int.preimage_Iic]

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- At a nonnegative point, the cdf of a natural-valued law cast to the reals is the cumulative
mass of the initial segment below the natural floor of that point. -/
theorem cdf_map_natCast {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = μ.real (Iic ⌊x⌋₊) := by
  first
  | have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = Iic ⌊x⌋₊ := by
      ext k
      simp only [mem_preimage, mem_Iic]
      exact (Nat.le_floor_iff hx).symm
    rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]

/-- Below the origin, the cdf of a natural-valued law cast to the reals vanishes: the law is
carried by the natural numbers. -/
theorem cdf_map_natCast_of_neg {x : ℝ} (hx : x < 0) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = 0 := by
  first
  | have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = ∅ := by
      ext k
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hx (Nat.cast_nonneg k)
    rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
      measureReal_empty]

/-- Every level below one is reached by a finite cumulative mass of a natural-valued probability
law. This existence proof supplies the witness required by `Nat.find`. -/
theorem exists_nat_le_measureReal_Iic {u : ℝ} (hu : u < 1) : ∃ k : ℕ, u ≤ μ.real (Iic k) := by
  first
  | obtain ⟨x, hx⟩ := nonempty_setOf_le_cdf (μ.map (Nat.cast : ℕ → ℝ)) hu
    refine ⟨⌈x⌉₊, ?_⟩
    have h := hx.trans (monotone_cdf (μ.map (Nat.cast : ℕ → ℝ)) (Nat.le_ceil x))
    simpa only [cdf_map_natCast μ (Nat.cast_nonneg _), Nat.floor_natCast] using h

/-- **CDF continuity from null singletons.** The cumulative distribution function of a
probability measure on `ℝ` is continuous when every singleton has measure zero. -/
theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  first
  | have hleft : ∀ x, leftLim (cdf ν) x = cdf ν x := by
      intro x
      have hsing : (cdf ν).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
      rw [StieltjesFunction.measure_singleton] at hsing
      have hle : leftLim (cdf ν) x ≤ cdf ν x := (cdf ν).mono.leftLim_le le_rfl
      have hz : cdf ν x - leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp hsing
      exact le_antisymm hle (by linarith)
    rw [continuous_iff_continuousAt]
    intro x
    rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, hleft x,
      ((cdf ν).right_continuous x).rightLim_eq]

/-- The left limit of the cumulative distribution function of a real probability law at a point is
the mass of the open ray to the left of that point. -/
theorem leftLim_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    leftLim (cdf ν) x = ν.real (Iio x) := by
  first
  | have h := (cdf ν).measure_Iio (tendsto_cdf_atBot ν) x
    rw [measure_cdf, sub_zero] at h
    have hnonneg : 0 ≤ leftLim (cdf ν) x :=
      (cdf_nonneg ν (x - 1)).trans ((cdf ν).mono.le_leftLim (by linarith))
    rw [measureReal_def, h, ENNReal.toReal_ofReal hnonneg]

/-- The mass of the open ray to the left of a point is at most a level exactly when the cumulative
distribution function stays at most that level at every point strictly to the left. -/
theorem measureReal_Iio_le_iff_forall_cdf_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {x t : ℝ} : ν.real (Iio x) ≤ t ↔ ∀ y < x, cdf ν y ≤ t := by
  first
  | rw [← leftLim_cdf]
    exact ⟨fun h y hy ↦ ((cdf ν).mono.le_leftLim hy).trans h, fun h ↦
      le_of_tendsto ((cdf ν).mono.tendsto_leftLim x) (eventually_nhdsWithin_of_forall h)⟩

/-- The mass of a bounded interval `Ioc a b` is the increment of the cumulative distribution
function between its endpoints. -/
theorem measureReal_Ioc_eq_cdf_sub (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ}
    (hab : a ≤ b) : ν.real (Ioc a b) = cdf ν b - cdf ν a := by
  first
  | rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.2 hab) measurableSet_Iic, cdf_eq_real,
      cdf_eq_real]

/-- A probability measure with no mass below `c` has cdf zero at every point strictly below `c`. -/
theorem cdf_eq_zero_of_lt_of_measure_Iio_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {c x : ℝ}
    (hc : ν (Iio c) = 0) (hx : x < c) : cdf ν x = 0 := by
  first
  | rw [cdf_eq_real]
    exact measureReal_mono_null (Iic_subset_Iio.mpr hx) (by simp [Measure.real, hc])

/-- An atomless law that gives no mass to the open half-line below `c` has cdf zero at `c`. -/
theorem cdf_eq_zero_of_measure_Iio_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] {c : ℝ} (hc : ν (Iio c) = 0) : cdf ν c = 0 := by
  first
  | have h : ν (Iic c) = 0 := (measure_congr Iio_ae_eq_Iic).symm.trans hc
    rw [cdf_eq_real, measureReal_def, h, ENNReal.toReal_zero]

/-- A half-open interval has positive mass exactly when the cdf strictly increases across its
endpoints. -/
theorem measure_Ioc_pos_iff_cdf_lt (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ} :
    0 < ν (Ioc a b) ↔ cdf ν a < cdf ν b := by
  first
  | calc
      0 < ν (Ioc a b) ↔ 0 < (cdf ν).measure (Ioc a b) := by rw [measure_cdf]
      _ ↔ cdf ν a < cdf ν b := by
        rw [StieltjesFunction.measure_Ioc, ENNReal.ofReal_pos, sub_pos]

/-- A real probability law with a strictly increasing cdf has full topological support. -/
theorem support_eq_univ_of_strictMono_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : StrictMono (cdf ν)) : ν.support = Set.univ := by
  first
  | rw [Set.eq_univ_iff_forall]
    intro x
    rw [mem_support_iff_forall]
    intro U hU
    obtain ⟨a, b, hx, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
    have hIoc : 0 < ν (Ioc a x) := (measure_Ioc_pos_iff_cdf_lt ν).mpr (hν hx.1)
    exact hIoc.trans_le (measure_mono fun y hy ↦ hab ⟨hy.1, hy.2.trans_lt hx.2⟩)

/-- The cdf increases strictly on every order-connected set contained in the support. -/
theorem strictMonoOn_cdf_of_subset_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {s : Set ℝ} (hs : s.OrdConnected) (hν : s ⊆ ν.support) : StrictMonoOn (cdf ν) s := by
  first
  | intro a ha b hb hab
    rw [← measure_Ioc_pos_iff_cdf_lt]
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ((mem_support_iff_forall _).mp (hν (hs.out ha hb ⟨hac.le, hcb.le⟩)) (Ioo a b)
      (Ioo_mem_nhds hac hcb)).trans_le (measure_mono Ioo_subset_Ioc_self)

/-- A cdf that increases strictly on a right half-line is below one at every finite cutoff. -/
theorem cdf_lt_one_of_strictMonoOn_Ici (ν : Measure ℝ) {c : ℝ}
    (hν : StrictMonoOn (cdf ν) (Ici c)) (x : ℝ) : cdf ν x < 1 := by
  first
  | have hlt := hν (a := max x c) (b := max x c + 1) (le_max_right _ _)
      ((le_max_right x c).trans (lt_add_one _).le) (lt_add_one _)
    exact ((monotone_cdf ν (le_max_left x c)).trans_lt hlt).trans_le (cdf_le_one ν _)

/-- The measure of the sublevel set `{x | cdf ν x ≤ y}` is `ENNReal.ofReal y` when
`y < 1`. -/
theorem cdf_sublevel_measure (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (y : ℝ) (hy1 : y < 1) :
    ν {x | cdf ν x ≤ y} = ENNReal.ofReal y := by
  first
  | set S : Set ℝ := {x | cdf ν x ≤ y}
    have hScl : IsClosed S := isClosed_Iic.preimage (continuous_cdf_of_noAtoms ν)
    have hevt : ∀ᶠ x in atTop, y < cdf ν x :=
      (tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy1)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hevt
    have hSbdd : BddAbove S := by
      refine ⟨M, fun x hx => ?_⟩
      by_contra hxM
      exact absurd (hM x (le_of_lt (not_le.mp hxM))) (not_lt.2 hx)
    by_cases hSne : S.Nonempty
    · set q := sSup S
      have hq_mem : q ∈ S := hScl.csSup_mem hSne hSbdd
      have hSeq : S = Iic q := by
        ext x
        constructor
        · intro hx; exact le_csSup hSbdd hx
        · intro hx
          exact le_trans ((cdf ν).mono hx) hq_mem
      have hcdfq : cdf ν q = y := by
        refine le_antisymm hq_mem ?_
        have htend : Tendsto (cdf ν) (𝓝[>] q) (𝓝 (cdf ν q)) :=
          ((continuous_cdf_of_noAtoms ν).tendsto q).mono_left nhdsWithin_le_nhds
        have hevt2 : ∀ᶠ x in 𝓝[>] q, y ≤ cdf ν x := by
          refine Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
          have : x ∉ S := fun hxS => absurd (le_csSup hSbdd hxS) (not_le.2 hx)
          exact le_of_lt (not_le.mp this)
        exact ge_of_tendsto htend hevt2
      rw [hSeq, ← ofReal_cdf ν q, hcdfq]
    · rw [not_nonempty_iff_eq_empty] at hSne
      have hyle : y ≤ 0 := by
        have hfor : ∀ᶠ x in atBot, y ≤ cdf ν x := by
          refine Filter.Eventually.of_forall (fun x => ?_)
          have : x ∉ S := by rw [hSne]; simp
          exact le_of_lt (not_le.mp this)
        exact ge_of_tendsto (tendsto_cdf_atBot ν) hfor
      have hνS : ν S = 0 := by rw [hSne]; exact measure_empty
      rw [ENNReal.ofReal_eq_zero.mpr hyle]
      exact hνS

end MeasureTheory.Measure

namespace Set.OrdConnected

/-- A point `q` at which the level `t` lies between the left limit and the value of the cumulative
distribution function lies in every interval of full mass: otherwise the interval lies entirely
on one side of `q`, and the mass on that side is `0` or `1`. -/
theorem mem_of_measureReal_Iio_le_of_le_cdf {μ : Measure ℝ} {s : Set ℝ} {t : ℝ}
    [IsProbabilityMeasure μ] (hs : s.OrdConnected) (hμs : ∀ᵐ x ∂μ, x ∈ s) {q : ℝ}
    (hIio : μ.real (Iio q) ≤ t) (hIic : t ≤ cdf μ q) (h0 : 0 < t) (h1 : t < 1) : q ∈ s := by
  first
  | by_contra hq
    have hside : (∀ x ∈ s, x < q) ∨ ∀ x ∈ s, q < x := by
      by_contra! h
      obtain ⟨⟨a, ha, hqa⟩, b, hb, hbq⟩ := h
      exact hq (hs.out hb ha ⟨hbq, hqa⟩)
    rcases hside with hlt | hgt
    · have hfull : μ (Iio q) = μ univ :=
        (ae_mem_iff_measure_eq measurableSet_Iio.nullMeasurableSet).1 (hμs.mono hlt)
      rw [measureReal_def, hfull, measure_univ, ENNReal.toReal_one] at hIio
      exact hIio.not_gt h1
    · have hnull : μ (Iic q) = 0 :=
        measure_eq_zero_iff_ae_notMem.2 (hμs.mono fun x hx hxq ↦ (hgt x hx).not_ge hxq)
      rw [cdf_eq_real, measureReal_def, hnull, ENNReal.toReal_zero] at hIic
      exact hIic.not_gt h0

end Set.OrdConnected

namespace TauCeti.Probability

variable {μ : Measure ℝ}

/-- **Survival starts at one.** An atomless probability law carried by the nonnegative half-line
has survival probability one at zero. -/
theorem one_sub_cdf_zero_eq_one [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (h0 : μ (Iio 0) = 0) :
    1 - cdf μ 0 = 1 := by
  first
  | rw [Measure.cdf_eq_zero_of_measure_Iio_eq_zero μ h0, sub_zero]

/-- **Survival starts at one for an absolutely continuous law.** A probability law absolutely
continuous with respect to Lebesgue measure and carried by the nonnegative half-line has survival
probability one at zero. -/
theorem one_sub_cdf_zero_eq_one_of_absolutelyContinuous [IsProbabilityMeasure μ]
    (hac : μ ≪ (volume : Measure ℝ)) (h0 : μ (Iio 0) = 0) : 1 - cdf μ 0 = 1 := by
  first
  | have : NullSingletonClass μ := ⟨fun t ↦ hac (measure_singleton t)⟩
    exact one_sub_cdf_zero_eq_one h0

end TauCeti.Probability
end -- closes the original EOF section from source line 83
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Probability/Cdf.lean -/

/- BEGIN SOURCE: TauCeti/Probability/Quantile.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The quantile function of a real law

The *quantile function*, or generalized inverse cumulative distribution function, of a measure
`μ` on `ℝ` sends a level `t` to the least point at which `ProbabilityTheory.cdf μ` reaches `t`:

`μ.quantile t = sInf {x | t ≤ cdf μ x}`.

Because `cdf μ` is monotone and right continuous with limits `0` at `-∞` and `1` at `+∞`, that
infimum is attained for every level `t` strictly between `0` and `1`, and the defining set is
exactly the closed ray to the right of the quantile. The quantile is therefore characterized by
the Galois property `μ.quantile t ≤ x ↔ t ≤ cdf μ x`. At levels `t ≤ 0` and `1 < t` the infimum
ranges over all of `ℝ` or over the empty set, so the value there is the junk value `0`. The
endpoint level `t = 1` is not junk: the quantile there is the least point of full cumulative mass
when such a point exists (for instance `(dirac a).quantile 1 = a`), and `0` when the law has
unbounded support to the right. The inverse characterizations below use levels in `Ioo 0 1`,
which is also the interval the uniform law is taken on.

The *upper quantile* `μ.upperQuantile t = sInf {x | t < cdf μ x}` uses the strict inequality
instead. Where `cdf μ` has a plateau at the level `t`, the lower and upper quantiles are the two
ends of that plateau; elsewhere they agree. The upper quantile is characterized through the left
limit of the cumulative distribution function, `x ≤ μ.upperQuantile t ↔ μ.real (Iio x) ≤ t`,
which is why the quantiles of a law pushed forward along a decreasing map are expressed through
the upper quantile of the original law. The lower quantile is left continuous and the upper
quantile right continuous, and at both of them the level lies between the left limit and the
value of the cumulative distribution function.

The main result is **inverse transform sampling**: for a probability measure `μ` the quantile
function pushes the uniform law on the open unit interval forward to `μ`. It presents every real
law as the law of one explicit measurable function of a single uniform variable, and it is what
makes the monotone rearrangement of two real laws a transport plan between them.

## Main definitions

* `MeasureTheory.Measure.quantile` — the generalized inverse of the cumulative distribution
  function;
* `MeasureTheory.Measure.upperQuantile` — the upper generalized inverse, the right end of each
  plateau of the cumulative distribution function.

## Main statements

* `MeasureTheory.Measure.quantile_le_iff` — the Galois characterization of the quantile, with
  `MeasureTheory.Measure.setOf_le_cdf_eq_Ici` its set-level form and
  `MeasureTheory.Measure.lt_quantile_iff` its negation;
* `MeasureTheory.Measure.cdf_le_iff_quantile_le` — reversed pointwise comparison of two cdfs is
  equivalent to pointwise comparison of their interior quantiles;
* `MeasureTheory.Measure.cdf_quantile` and `MeasureTheory.Measure.quantile_cdf` — the exact
  inverse laws, when the cumulative distribution function is continuous, respectively strictly
  increasing where its values lie strictly between `0` and `1`; together they give
  `MeasureTheory.Measure.quantile_lt_iff`, `MeasureTheory.Measure.strictMonoOn_quantile` and
  `MeasureTheory.Measure.continuousOn_quantile`;
* `MeasureTheory.Measure.quantile_eq_of_cdf_eq` and
  `MeasureTheory.Measure.upperQuantile_eq_of_cdf_eq` — invert an interior cdf value under strict
  monotonicity;
* `MeasureTheory.Measure.quantile_eq_of_le_cdf_iff` — two quantiles agree when their defining cdf
  level sets agree;
* `MeasureTheory.Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos` and
  `MeasureTheory.Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one` — the infinite endpoint
  limits when the cdf is everywhere positive or everywhere less than one, respectively;
* `MeasureTheory.Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos` and
  `MeasureTheory.Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one` — the finite endpoint
  limits from almost-sure bounds and strict cdf inequalities toward the support interior;
* `MeasureTheory.Measure.quantile_map_abs` — the quantile of the image of a symmetric law under
  absolute value;
* `MeasureTheory.Measure.le_upperQuantile_iff` and `MeasureTheory.Measure.upperQuantile_lt_iff`
  — the characterization of the upper quantile through the mass strictly to the left of a point;
* `MeasureTheory.Measure.measureReal_Iio_quantile_le` and `MeasureTheory.Measure.le_cdf_quantile`
  — the level lies between the left limit and the value of the cumulative distribution function
  at the quantile, with the same bounds at the upper quantile; for an atomless law
  `MeasureTheory.Measure.cdf_quantile` gives equality;
* `Set.OrdConnected.quantile_mem` and `Set.OrdConnected.upperQuantile_mem` — interior quantiles
  lie in every interval carrying the full mass of the measure;
* `MeasureTheory.Measure.quantile_le_upperQuantile` and
  `MeasureTheory.Measure.upperQuantile_le_quantile` — the two quantile functions interleave;
* `MeasureTheory.Measure.continuousWithinAt_Iio_quantile` and
  `MeasureTheory.Measure.continuousWithinAt_Ioi_upperQuantile` — left continuity of the lower
  and right continuity of the upper quantile;
* `MeasureTheory.Measure.measurable_quantile_probabilityMeasure` and
  `MeasureTheory.Measure.measurable_upperQuantile_probabilityMeasure` — joint measurability of
  the two quantiles in a probability law and an interior level, with
  `MeasureTheory.Measure.measurable_quantile_cdf_family` and
  `MeasureTheory.Measure.measurable_upperQuantile_cdf_family` as parameterized-family forms;
* `MeasureTheory.Measure.map_quantile_volume_Ioo` — inverse transform sampling: the quantile
  function pushes the uniform law on `Ioo 0 1` forward to the original law, packaged as
  `MeasureTheory.Measure.measurePreserving_quantile`;
* `MeasureTheory.Measure.setIntegral_quantile_eq_integral` — the average of the quantile function
  over the levels is the mean, with integrability characterized by
  `MeasureTheory.Measure.integrableOn_quantile_iff`;
* `MeasureTheory.Measure.quantile_map_volume_Ioo_ae` — conversely, the law of a monotone function
  of a uniform variable has that function as its quantile function, almost everywhere;
* `MeasureTheory.Measure.cdf_map_eq_volume_restrict` — the probability integral transform for an
  atomless real law;
* `MeasureTheory.Measure.cdf_quantile_ae` and
  `MeasureTheory.Measure.quantile_cdf_ae` — the two almost-everywhere inverse laws, the first
  for an atomless law and the second for every law;
* `MeasureTheory.Measure.realMod0MeasureIso` — for an atomless real law, the pair
  (`cdf ν`, `ν.quantile`) as a `TauCeti.Mod0MeasureIso` between `ν` and Lebesgue measure
  restricted to `[0, 1]`.

## References

* R. B. Nelsen, *An Introduction to Copulas*, Springer 2006, §2.3, for the generalized inverse
  and its Galois property.
* P. Embrechts and M. Hofert, *A note on generalized inverses*, Mathematical Methods of
  Operations Research 77 (2013), 423--432.

## Adapted from

The probability integral transform `cdf_map_eq_volume_restrict`, the inverse laws
`cdf_quantile_ae` and `quantile_cdf_ae`, the inverse transform sampling theorem
`map_quantile_volume_Ioo` and the resulting `realMod0MeasureIso` instance are adapted from
Cameron Freer's independent implementation in `Graphon/MeasureIso.lean` at commit
`9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>,
where they appear as `cdf_map_eq_volume_restrict`, `cdf_cdfQuantile_ae`,
`cdfQuantile_cdf_ae`, `map_cdfQuantile_volume_restrict` and `realMod0MeasureIso`, with the
generalized inverse called `cdfQuantile` rather than `quantile`; the graphon-specific packaging
was removed. The original work is copyright Cameron Freer and licensed under Apache 2.0.

The measure-preserving equivalence that this file realizes on the real line is the classical
transport of an atomless standard-Borel space to the unit interval, proved as Theorem A.7 in
S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, Arkiv för
Matematik 52 (2014); see also `TauCeti.MeasureTheory.Measure.exists_mpModNull_equiv_unitInterval`
in `TauCeti.MeasureTheory.Measure.AtomlessStandardBorel`, which composes it with
`TauCeti.embeddingRealMod0MeasureIso`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Function Topology

namespace MeasureTheory.Measure

/-- The **quantile function** of a measure on `ℝ`: the least point at which its cumulative
distribution function reaches the level `t`.

This is the honest generalized inverse of `ProbabilityTheory.cdf μ` for `t` in `Set.Ioo 0 1`. At
levels `t ≤ 0` and `1 < t` the defining infimum ranges over all of `ℝ` or over the empty set, and
the value is the junk value `0` (`quantile_of_nonpos`, `quantile_of_one_lt`). At the endpoint
level `t = 1` the value is the least point where the cumulative distribution function reaches `1`
if there is one, and `0` otherwise. -/
def quantile (μ : Measure ℝ) (t : ℝ) : ℝ := sInf {x : ℝ | t ≤ cdf μ x}

/-- The quantile function is the infimum of the points at which the cumulative distribution
function reaches the level. The definition's body is not exposed, so this is the lemma downstream
modules should rewrite with. -/
theorem quantile_def (μ : Measure ℝ) (t : ℝ) :
    μ.quantile t = sInf {x : ℝ | t ≤ cdf μ x} := (rfl)

/-- Quantiles of two measures at two levels agree when the corresponding cdf level sets agree. -/
theorem quantile_eq_of_le_cdf_iff (ν μ : Measure ℝ) {u t : ℝ}
    (h : ∀ x, u ≤ cdf ν x ↔ t ≤ cdf μ x) : ν.quantile u = μ.quantile t := by
  first
  | rw [quantile_def, quantile_def]
    apply congrArg sInf
    ext x
    exact h x

/-- **The quantile of a symmetric fold.** At a positive level `u`, the quantile of the image of a
symmetric law `μ` under absolute value is the quantile of `μ` at level `(1 + u) / 2`. -/
theorem quantile_map_abs (μ : Measure ℝ) [IsProbabilityMeasure μ] [μ.IsNegInvariant] {u : ℝ}
    (hu : 0 < u) : (μ.map (|·|)).quantile u = μ.quantile ((1 + u) / 2) := by
  first
  | refine quantile_eq_of_le_cdf_iff _ _ fun x => ?_
    rcases le_or_gt 0 x with hx | hx
    · rw [μ.cdf_map_abs_of_isNegInvariant hx]
      constructor <;> intro h <;> linarith
    · rw [μ.cdf_map_abs_of_neg hx]
      -- Below `0`, the cdf of a symmetric law is at most `1 / 2`.
      have hle : cdf μ x ≤ 1 - cdf μ x := by
        rw [← μ.measureReal_Iio_neg x, cdf_eq_real]
        exact measureReal_mono (Iic_subset_Iio.2 (by linarith))
      constructor <;> intro h <;> linarith

variable {t x : ℝ}

/-- Above the level `0` the points whose cumulative mass reaches the level are bounded below,
because the cumulative distribution function tends to `0` at `-∞`. -/
theorem bddBelow_setOf_le_cdf (μ : Measure ℝ) (ht : 0 < t) : BddBelow {x : ℝ | t ≤ cdf μ x} := by
  first
  | obtain ⟨a, ha⟩ :=
      eventually_atBot.mp ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds ht))
    refine ⟨a, fun x hx ↦ ?_⟩
    by_contra hxa
    exact absurd (ha x (not_le.mp hxa).le) (not_lt.mpr hx)

/-- At a nonpositive level the quantile function takes the junk value `0`: every point has
cumulative mass at least the level. -/
@[simp]
theorem quantile_of_nonpos (μ : Measure ℝ) (ht : t ≤ 0) : μ.quantile t = 0 := by
  first
  | have hset : {x : ℝ | t ≤ cdf μ x} = univ := eq_univ_of_forall fun x ↦ ht.trans (cdf_nonneg μ x)
    rw [quantile_def, hset, Real.sInf_univ]

/-- Above the level `1` the quantile function takes the junk value `0`: no point has cumulative
mass that large. -/
@[simp]
theorem quantile_of_one_lt (μ : Measure ℝ) (ht : 1 < t) : μ.quantile t = 0 := by
  first
  | have hset : {x : ℝ | t ≤ cdf μ x} = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ absurd (hx.trans (cdf_le_one μ x)) (not_le.2 ht)
    rw [quantile_def, hset, Real.sInf_empty]

/-- The zero measure has quantile zero at every level, including the endpoint levels. -/
@[simp]
theorem quantile_zero (t : ℝ) : (0 : Measure ℝ).quantile t = 0 := by
  first
  | rcases le_or_gt t 0 with h0 | h0
    · exact quantile_of_nonpos 0 h0
    rcases le_or_gt t 1 with h1 | h1
    · have hset : {x : ℝ | t ≤ cdf (0 : Measure ℝ) x} = Ici 0 := by
        ext x
        by_cases hx : 0 ≤ x <;> simp [cdf_zero, hx, h0, h1]
      rw [quantile_def, hset, csInf_Ici]
    · exact quantile_of_one_lt 0 h1

/-- The cumulative distribution function at the quantile reaches every level strictly below
`1`. -/
theorem le_cdf_quantile (μ : Measure ℝ) (h1 : t < 1) : t ≤ cdf μ (μ.quantile t) := by
  first
  | have key : ∀ r : Ioi (μ.quantile t), t ≤ cdf μ r := by
      rintro ⟨r, hr⟩
      obtain ⟨y, hy, hyr⟩ := exists_lt_of_csInf_lt (nonempty_setOf_le_cdf μ h1) hr
      exact hy.trans (monotone_cdf μ hyr.le)
    have h := le_ciInf key
    rwa [StieltjesFunction.iInf_Ioi_eq] at h

/-- **The Galois characterization of the quantile.** For a level strictly between `0` and `1`,
the quantile lies below a point exactly when the cumulative distribution function at that point
reaches the level. -/
@[simp]
theorem quantile_le_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t ≤ x ↔ t ≤ cdf μ x :=
  ⟨fun h ↦ (le_cdf_quantile μ h1).trans (monotone_cdf μ h),
    fun h ↦ csInf_le (bddBelow_setOf_le_cdf μ h0) h⟩

/-- Reversed pointwise comparison of the cdfs of two real measures is equivalent to pointwise
comparison of their quantiles at every level strictly between zero and one. -/
theorem cdf_le_iff_quantile_le (μ ν : Measure ℝ) :
    (∀ x, cdf ν x ≤ cdf μ x) ↔
      ∀ u, 0 < u → u < 1 → μ.quantile u ≤ ν.quantile u := by
  first
  | constructor
    · intro hcdf u hu0 hu1
      rw [quantile_le_iff μ hu0 hu1]
      exact (le_cdf_quantile ν hu1).trans (hcdf _)
    · intro hquant x
      by_contra hle
      have hlt : cdf μ x < cdf ν x := lt_of_not_ge hle
      let u := (cdf μ x + cdf ν x) / 2
      have hu0 : 0 < u := by
        dsimp [u]
        linarith [cdf_nonneg μ x]
      have hu1 : u < 1 := by
        dsimp [u]
        linarith [cdf_le_one ν x]
      have hμu : cdf μ x < u := by
        dsimp [u]
        linarith
      have huν : u ≤ cdf ν x := by
        dsimp [u]
        linarith
      have hνq : ν.quantile u ≤ x := (quantile_le_iff ν hu0 hu1).2 huν
      have hμq : μ.quantile u ≤ x := (hquant u hu0 hu1).trans hνq
      exact (not_le_of_gt hμu) ((quantile_le_iff μ hu0 hu1).1 hμq)

/-- The set of points whose cumulative mass reaches a level strictly between `0` and `1` is the
closed ray to the right of the quantile at that level. -/
theorem setOf_le_cdf_eq_Ici (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    {x : ℝ | t ≤ cdf μ x} = Ici (μ.quantile t) := by
  first
  | ext x
    exact (quantile_le_iff μ h0 h1).symm

/-- A point lies strictly below the quantile at a level exactly when its cumulative mass has not
yet reached that level. -/
@[simp]
theorem lt_quantile_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    x < μ.quantile t ↔ cdf μ x < t := by
  first
  | simpa only [not_le] using (quantile_le_iff (x := x) μ h0 h1).not

/-- If the cdf is everywhere positive, quantiles tend to minus infinity as the level decreases
to zero. -/
theorem tendsto_quantile_nhdsGT_zero_of_cdf_pos (μ : Measure ℝ)
    (hpos : ∀ x, 0 < cdf μ x) :
    Tendsto (fun u ↦ (μ.quantile u : EReal)) (𝓝[>] 0) (𝓝 ⊥) := by
  first
  | apply EReal.tendsto_coe_nhds_bot_iff.mpr
    refine tendsto_atBot.mpr fun b ↦ ?_
    filter_upwards [Ioo_mem_nhdsGT (hpos b)] with u hu
    exact (quantile_le_iff μ hu.1 (hu.2.trans_le (cdf_le_one μ b))).mpr hu.2.le

/-- If the cdf is everywhere less than one, quantiles tend to plus infinity as the level increases
to one. -/
theorem tendsto_quantile_nhdsLT_one_of_cdf_lt_one (μ : Measure ℝ)
    (hlt : ∀ x, cdf μ x < 1) :
    Tendsto (fun u ↦ (μ.quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  first
  | apply EReal.tendsto_coe_nhds_top_iff.mpr
    refine tendsto_atTop.mpr fun b ↦ ?_
    filter_upwards [Ioo_mem_nhdsLT (hlt b)] with u hu
    exact ((lt_quantile_iff μ ((cdf_nonneg μ b).trans_lt hu.1) hu.2).mpr hu.1).le

/-- The quantile function is monotone on the levels where it is the honest generalized
inverse. -/
theorem monotoneOn_quantile (μ : Measure ℝ) : MonotoneOn μ.quantile (Ioo 0 1) := by
  first
  | rintro s ⟨hs0, hs1⟩ t ⟨_, ht1⟩ hst
    exact (quantile_le_iff μ hs0 hs1).mpr (hst.trans (le_cdf_quantile μ ht1))

/-- The mass strictly to the left of the quantile does not exceed the level: every point below
the quantile has cumulative mass below the level. Together with `le_cdf_quantile` this traps the
level between the left limit and the value of the cumulative distribution function at the
quantile. -/
theorem measureReal_Iio_quantile_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : 0 < t)
    (h1 : t < 1) : μ.real (Iio (μ.quantile t)) ≤ t :=
  (measureReal_Iio_le_iff_forall_cdf_le μ).mpr fun _ hy ↦ ((lt_quantile_iff μ h0 h1).mp hy).le

/-- The cumulative distribution function at the quantile is exactly the level when the law has no
atom at the quantile. -/
theorem cdf_quantile' (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1)
    (h : μ {μ.quantile t} = 0) : cdf μ (μ.quantile t) = t := by
  first
  | refine le_antisymm ?_ (le_cdf_quantile μ h1)
    rw [cdf_eq_real, ← measureReal_congr (Iio_ae_eq_Iic' h)]
    exact measureReal_Iio_quantile_le μ h0 h1

/-- For a law with continuous cumulative distribution function, the quantile is an exact right
inverse of the cumulative distribution function at every level strictly between `0` and `1`. -/
@[simp]
theorem cdf_quantile (μ : Measure ℝ) (hμ : Continuous (cdf μ)) (h0 : 0 < t) (h1 : t < 1) :
    cdf μ (μ.quantile t) = t := by
  first
  | refine le_antisymm ?_ (le_cdf_quantile μ h1)
    -- To the left of the quantile the cumulative distribution function stays below `t`, so by
    -- continuity it is at most `t` at the quantile itself.
    refine le_of_tendsto ((hμ.tendsto _).mono_left (nhdsWithin_le_nhds (s := Iio (μ.quantile t))))
      ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((lt_quantile_iff μ h0 h1).1 hy).le

/-- For a law with continuous cumulative distribution function, the quantile function is strictly
increasing on the levels strictly between `0` and `1`. -/
theorem strictMonoOn_quantile (μ : Measure ℝ) (hμ : Continuous (cdf μ)) :
    StrictMonoOn μ.quantile (Ioo 0 1) := fun s hs t ht hst => by
  rwa [lt_quantile_iff μ ht.1 ht.2, cdf_quantile μ hμ hs.1 hs.2]

/-- If the cumulative distribution function is strictly increasing where its values lie strictly
between `0` and `1`, the quantile is a left inverse of it there. -/
@[simp]
theorem quantile_cdf (μ : Measure ℝ) (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1))
    (hx : cdf μ x ∈ Ioo 0 1) : μ.quantile (cdf μ x) = x := by
  first
  | refine le_antisymm ((quantile_le_iff μ hx.1 hx.2).2 le_rfl) (not_lt.1 fun h => ?_)
    have hle := le_cdf_quantile μ hx.2
    have hq : cdf μ (μ.quantile (cdf μ x)) ∈ Ioo 0 1 :=
      ⟨hx.1.trans_le hle, (monotone_cdf μ h.le).trans_lt hx.2⟩
    exact (hmono hq hx h).not_ge hle

/-- A point whose cumulative mass is an interior level is the quantile at that level, when
its cumulative distribution function is strictly increasing on interior levels. -/
theorem quantile_eq_of_cdf_eq (μ : Measure ℝ)
    (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1))
    (hx : cdf μ x = t) (ht : t ∈ Ioo 0 1) : μ.quantile t = x :=
  (congrArg μ.quantile hx).symm.trans (quantile_cdf μ hmono (by rw [hx]; exact ht))

/-- The strict form of `MeasureTheory.Measure.quantile_le_iff`, for a law whose cumulative
distribution function is continuous, and strictly increasing where its values lie strictly between
`0` and `1`. -/
theorem quantile_lt_iff (μ : Measure ℝ) (hμ : Continuous (cdf μ))
    (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1)) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t < x ↔ t < cdf μ x := by
  first
  | have hq := cdf_quantile μ hμ h0 h1
    refine ⟨fun h => ?_, fun h => not_le.1 fun hx => ?_⟩
    · rcases lt_or_ge (cdf μ x) 1 with hx1 | hx1
      · have hle : t ≤ cdf μ x := hq ▸ monotone_cdf μ h.le
        rw [← hq]
        exact hmono (by rw [mem_preimage, hq]; exact ⟨h0, h1⟩) ⟨h0.trans_le hle, hx1⟩ h
      · exact h1.trans_le hx1
    · exact (hq ▸ monotone_cdf μ hx).not_gt h

/-- If the cdf is strictly increasing on an interval containing all interior quantiles,
the quantile is continuous on the interior levels, even when the law has atoms. -/
theorem continuousOn_quantile_of_strictMonoOn (μ : Measure ℝ) {s : Set ℝ}
    (hs : s.OrdConnected) (hmono : StrictMonoOn (cdf μ) s)
    (hq : MapsTo μ.quantile (Ioo 0 1) s) : ContinuousOn μ.quantile (Ioo 0 1) := by
  first
  | intro u hu
    refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · have ha' := (lt_quantile_iff μ hu.1 hu.2).1 ha
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds ha')] with v hv hav
      exact (lt_quantile_iff μ hv.1 hv.2).2 hav
    · by_cases hbound : ∀ v ∈ Ioo 0 1, μ.quantile v < b
      · filter_upwards [self_mem_nhdsWithin] with v hv using hbound v hv
      push Not at hbound
      obtain ⟨v, hv, hbv⟩ := hbound
      obtain ⟨c, hqc, hcb⟩ := exists_between hb
      have hcs : c ∈ s := hs.out (hq hu) (hq hv) ⟨hqc.le, hcb.le.trans hbv⟩
      have hc : u < cdf μ c := (le_cdf_quantile μ hu.2).trans_lt (hmono (hq hu) hcs hqc)
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hc)] with w hw hwc
      exact ((quantile_le_iff μ hw.1 hw.2).2 hwc.le).trans_lt hcb

/-- For a law whose cumulative distribution function is continuous, and strictly increasing where
its values lie strictly between `0` and `1`, the quantile function is continuous on the levels
strictly between `0` and `1`. -/
theorem continuousOn_quantile (μ : Measure ℝ) (hμ : Continuous (cdf μ))
    (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1)) :
    ContinuousOn μ.quantile (Ioo 0 1) := by
  first
  | refine continuousOn_quantile_of_strictMonoOn μ
      (ordConnected_Ioo.preimage_mono (monotone_cdf μ)) hmono ?_
    intro t ht
    rw [mem_preimage, cdf_quantile μ hμ ht.1 ht.2]
    exact ht

/-- The quantile function is left continuous at every level strictly between `0` and `1`. -/
theorem continuousWithinAt_Iio_quantile (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    ContinuousWithinAt μ.quantile (Iio t) t := by
  first
  | refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · -- Below the quantile at `t` the cumulative mass is below `t`, so every level strictly between
      -- that mass and `t` already has its quantile above `a`.
      have ha' : max (cdf μ a) 0 < t := max_lt ((lt_quantile_iff μ h0 h1).mp ha) h0
      filter_upwards [Ioo_mem_nhdsLT ha'] with s hs
      exact (lt_quantile_iff μ ((le_max_right _ _).trans_lt hs.1) (hs.2.trans h1)).mpr
        ((le_max_left _ _).trans_lt hs.1)
    · filter_upwards [Ioo_mem_nhdsLT h0] with s hs
      exact (monotoneOn_quantile μ ⟨hs.1, hs.2.trans h1⟩ ⟨h0, h1⟩ hs.2.le).trans_lt hb

/-! ### The upper quantile -/

/-- The **upper quantile function** of a measure on `ℝ`: the infimum of the points at which its
cumulative distribution function strictly exceeds the level `t`.

At a level `t` strictly between `0` and `1` the lower quantile `MeasureTheory.Measure.quantile`
and the upper quantile are the left and right ends of the set of points whose cumulative mass
is `t` when the cumulative distribution function has a plateau at that level, and they coincide
otherwise. Quantiles of a law pushed forward along a decreasing map are expressed through the
upper quantile.
At levels `t < 0` and `1 ≤ t` the defining infimum ranges over all of `ℝ` or over the empty set,
and the value is the junk value `0` (`upperQuantile_of_neg`, `upperQuantile_of_one_le`). -/
def upperQuantile (μ : Measure ℝ) (t : ℝ) : ℝ := sInf {x : ℝ | t < cdf μ x}

/-- The upper quantile function is the infimum of the points at which the cumulative distribution
function strictly exceeds the level. The definition's body is not exposed, so this is the lemma
downstream modules should rewrite with. -/
theorem upperQuantile_def (μ : Measure ℝ) (t : ℝ) :
    μ.upperQuantile t = sInf {x : ℝ | t < cdf μ x} := (rfl)

/-- Below the level `1` some point has cumulative mass strictly above the level, because the
cumulative distribution function tends to `1` at `+∞`. -/
theorem nonempty_setOf_lt_cdf (μ : Measure ℝ) (ht : t < 1) : {x : ℝ | t < cdf μ x}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht)).exists

/-- Above the level `0` the points whose cumulative mass strictly exceeds the level are bounded
below, because the cumulative distribution function tends to `0` at `-∞`. -/
theorem bddBelow_setOf_lt_cdf (μ : Measure ℝ) (ht : 0 < t) : BddBelow {x : ℝ | t < cdf μ x} :=
  (bddBelow_setOf_le_cdf μ ht).mono (ofPred_subset_ofPred.2 fun _ ↦ le_of_lt)

/-- At a negative level the upper quantile function takes the junk value `0`: every point has
cumulative mass strictly above the level. -/
@[simp]
theorem upperQuantile_of_neg (μ : Measure ℝ) (ht : t < 0) : μ.upperQuantile t = 0 := by
  first
  | have hset : {x : ℝ | t < cdf μ x} = univ :=
      eq_univ_of_forall fun x ↦ ht.trans_le (cdf_nonneg μ x)
    rw [upperQuantile_def, hset, Real.sInf_univ]

/-- At a level of at least `1` the upper quantile function takes the junk value `0`: no point has
cumulative mass that large. -/
@[simp]
theorem upperQuantile_of_one_le (μ : Measure ℝ) (ht : 1 ≤ t) : μ.upperQuantile t = 0 := by
  first
  | have hset : {x : ℝ | t < cdf μ x} = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ absurd (hx.trans_le (cdf_le_one μ x)) (not_lt.2 ht)
    rw [upperQuantile_def, hset, Real.sInf_empty]

/-- A point whose cumulative mass strictly exceeds a positive level lies above the upper quantile
at that level. -/
theorem upperQuantile_le_of_lt_cdf (μ : Measure ℝ) (h0 : 0 < t) (h : t < cdf μ x) :
    μ.upperQuantile t ≤ x :=
  csInf_le (bddBelow_setOf_lt_cdf μ h0) h

/-- Strictly above the upper quantile at a level below `1` the cumulative mass strictly exceeds
the level. -/
theorem lt_cdf_of_upperQuantile_lt (μ : Measure ℝ) (h1 : t < 1) (h : μ.upperQuantile t < x) :
    t < cdf μ x := by
  first
  | obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (nonempty_setOf_lt_cdf μ h1) h
    exact hy.trans_le (monotone_cdf μ hyx.le)

/-- A point lies below the upper quantile exactly when every point strictly to its left has
cumulative mass at most the level. -/
private theorem le_upperQuantile_iff_forall_cdf_le (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    x ≤ μ.upperQuantile t ↔ ∀ y < x, cdf μ y ≤ t := by
  first
  | refine ⟨fun h y hy ↦ le_of_not_gt fun hty ↦
      (upperQuantile_le_of_lt_cdf μ h0 hty).not_gt (hy.trans_le h), fun h ↦ ?_⟩
    exact le_csInf (nonempty_setOf_lt_cdf μ h1) fun z hz ↦ le_of_not_gt fun hzx ↦
      (h z hzx).not_gt hz

/-- **The characterization of the upper quantile.** For a level strictly between `0` and `1`, a
point lies below the upper quantile exactly when the mass strictly to its left is at most the
level. This is the counterpart of `MeasureTheory.Measure.quantile_le_iff`, with the left limit
of the cumulative distribution function in place of its value. -/
@[simp]
theorem le_upperQuantile_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    x ≤ μ.upperQuantile t ↔ μ.real (Iio x) ≤ t := by
  first
  | rw [le_upperQuantile_iff_forall_cdf_le μ h0 h1, measureReal_Iio_le_iff_forall_cdf_le]

/-- The upper quantile lies strictly below a point exactly when the mass strictly to the left of
that point exceeds the level. -/
@[simp]
theorem upperQuantile_lt_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    μ.upperQuantile t < x ↔ t < μ.real (Iio x) := by
  first
  | simpa only [not_le] using (le_upperQuantile_iff (x := x) μ h0 h1).not

/-- The lower quantile does not exceed the upper quantile. -/
theorem quantile_le_upperQuantile (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t ≤ μ.upperQuantile t :=
  csInf_le_csInf (bddBelow_setOf_le_cdf μ h0) (nonempty_setOf_lt_cdf μ h1)
    (ofPred_subset_ofPred.2 fun _ ↦ le_of_lt)

/-- The upper quantile at a level does not exceed the lower quantile at any strictly larger
level, so the two quantile functions interleave. -/
theorem upperQuantile_le_quantile (μ : Measure ℝ) {s : ℝ} (hs0 : 0 < s) (hst : s < t)
    (ht1 : t < 1) : μ.upperQuantile s ≤ μ.quantile t :=
  upperQuantile_le_of_lt_cdf μ hs0 (hst.trans_le (le_cdf_quantile μ ht1))

/-- The upper quantile function is monotone on the levels where it is an honest generalized
inverse. -/
theorem monotoneOn_upperQuantile (μ : Measure ℝ) : MonotoneOn μ.upperQuantile (Ioo 0 1) := by
  first
  | rintro s ⟨hs0, hs1⟩ t ⟨_, ht1⟩ hst
    exact csInf_le_csInf (bddBelow_setOf_lt_cdf μ hs0) (nonempty_setOf_lt_cdf μ ht1)
      fun _ hx ↦ hst.trans_lt hx

/-- The cumulative distribution function at the upper quantile reaches the level. -/
theorem le_cdf_upperQuantile (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    t ≤ cdf μ (μ.upperQuantile t) :=
  (le_cdf_quantile μ h1).trans (monotone_cdf μ (quantile_le_upperQuantile μ h0 h1))

/-- The mass strictly to the left of the upper quantile does not exceed the level. -/
theorem measureReal_Iio_upperQuantile_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : 0 < t)
    (h1 : t < 1) : μ.real (Iio (μ.upperQuantile t)) ≤ t :=
  (le_upperQuantile_iff μ h0 h1).mp le_rfl

/-- A point whose cumulative mass is an interior level is the upper quantile at that level, when
its cumulative distribution function is strictly increasing on interior levels. -/
theorem upperQuantile_eq_of_cdf_eq (μ : Measure ℝ)
    (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1))
    (hx : cdf μ x = t) (ht : t ∈ Ioo 0 1) : μ.upperQuantile t = x := by
  first
  | subst hx
    refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun y hy ↦ ?_) ?_
    · refine upperQuantile_le_of_lt_cdf μ ht.1 ?_
      rcases lt_or_ge (cdf μ y) 1 with hy1 | hy1
      · exact hmono ht ⟨ht.1.trans_le (monotone_cdf μ hy.le), hy1⟩ hy
      · exact ht.2.trans_le hy1
    · calc x = μ.quantile (cdf μ x) := (quantile_cdf μ hmono ht).symm
        _ ≤ μ.upperQuantile (cdf μ x) := quantile_le_upperQuantile μ ht.1 ht.2

end MeasureTheory.Measure

namespace Set.OrdConnected

/-- **Interior quantiles lie in every interval of full mass.** -/
theorem quantile_mem {μ : Measure ℝ} {s : Set ℝ} {t : ℝ} [IsProbabilityMeasure μ]
    (hs : s.OrdConnected) (hμs : ∀ᵐ x ∂μ, x ∈ s) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t ∈ s :=
  hs.mem_of_measureReal_Iio_le_of_le_cdf hμs (μ.measureReal_Iio_quantile_le h0 h1)
    (μ.le_cdf_quantile h1) h0 h1

/-- **Interior upper quantiles lie in every interval of full mass.** -/
theorem upperQuantile_mem {μ : Measure ℝ} {s : Set ℝ} {t : ℝ} [IsProbabilityMeasure μ]
    (hs : s.OrdConnected) (hμs : ∀ᵐ x ∂μ, x ∈ s) (h0 : 0 < t) (h1 : t < 1) :
    μ.upperQuantile t ∈ s :=
  hs.mem_of_measureReal_Iio_le_of_le_cdf hμs (μ.measureReal_Iio_upperQuantile_le h0 h1)
    (μ.le_cdf_upperQuantile h0 h1) h0 h1

end Set.OrdConnected

namespace MeasureTheory.Measure

/-- For a law carried by `[c, ∞)` whose cdf is positive above `c`, quantiles tend to `c` as
the level decreases to zero. An atom at `c` is allowed. -/
theorem tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {c : ℝ} (hbound : ∀ᵐ x ∂μ, c ≤ x)
    (hpos : ∀ x, c < x → 0 < cdf μ x) :
    Tendsto (fun u ↦ (μ.quantile u : EReal)) (𝓝[>] 0) (𝓝 (c : EReal)) := by
  first
  | apply EReal.tendsto_coe.2
    refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
      exact ha.trans_le (ordConnected_Ici.quantile_mem hbound hu.1 hu.2)
    · obtain ⟨x, hcx, hxb⟩ := exists_between hb
      filter_upwards [Ioo_mem_nhdsGT (hpos x hcx)] with u hu
      exact ((quantile_le_iff μ hu.1 (hu.2.trans_le (cdf_le_one μ x))).2 hu.2.le).trans_lt hxb

/-- For a law carried by `(-∞, c]` whose cdf is less than one below `c`, quantiles tend to `c`
as the level increases to one. An atom at `c` is allowed. -/
theorem tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {c : ℝ} (hbound : ∀ᵐ x ∂μ, x ≤ c)
    (hlt : ∀ x, x < c → cdf μ x < 1) :
    Tendsto (fun u ↦ (μ.quantile u : EReal)) (𝓝[<] 1) (𝓝 (c : EReal)) := by
  first
  | apply EReal.tendsto_coe.2
    refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · filter_upwards [Ioo_mem_nhdsLT (hlt a ha)] with u hu
      exact (lt_quantile_iff μ ((cdf_nonneg μ a).trans_lt hu.1) hu.2).2 hu.1
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
      exact (ordConnected_Iic.quantile_mem hbound hu.1 hu.2).trans_lt hb

/-- The cumulative distribution function at the upper quantile is exactly the level when the law
has no atom at the upper quantile. -/
theorem cdf_upperQuantile' (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1)
    (h : μ {μ.upperQuantile t} = 0) : cdf μ (μ.upperQuantile t) = t := by
  first
  | refine le_antisymm ?_ (le_cdf_upperQuantile μ h0 h1)
    rw [cdf_eq_real, ← measureReal_congr (Iio_ae_eq_Iic' h)]
    exact measureReal_Iio_upperQuantile_le μ h0 h1

/-- For an atomless law the cumulative distribution function at the upper quantile is exactly the
level. -/
@[simp]
theorem cdf_upperQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (h0 : 0 < t) (h1 : t < 1) : cdf μ (μ.upperQuantile t) = t :=
  cdf_upperQuantile' μ h0 h1 (measure_singleton _)

/-- The upper quantile function is right continuous at every level strictly between `0`
and `1`. -/
theorem continuousWithinAt_Ioi_upperQuantile (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    ContinuousWithinAt μ.upperQuantile (Ioi t) t := by
  first
  | refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT h1] with s hs
      exact ha.trans_le (monotoneOn_upperQuantile μ ⟨h0, h1⟩ ⟨h0.trans hs.1, hs.2⟩ hs.1.le)
    · -- Some point `y < b` already has cumulative mass above `t`; every level strictly between `t`
      -- and that mass then has its upper quantile at most `y`.
      obtain ⟨y, hy, hyb⟩ := exists_lt_of_csInf_lt (nonempty_setOf_lt_cdf μ h1) hb
      filter_upwards [Ioo_mem_nhdsGT hy] with s hs
      exact (upperQuantile_le_of_lt_cdf μ (h0.trans hs.1) hs.2).trans_lt hyb

/-- The quantile function is measurable. -/
@[fun_prop]
theorem measurable_quantile (μ : Measure ℝ) : Measurable μ.quantile :=
  TauCeti.measurable_of_monotoneOn_Ioo_of_eq_const (monotoneOn_quantile μ) fun _ hs ↦
    hs.elim (fun h ↦ quantile_of_nonpos μ h.le) (quantile_of_one_lt μ)

/-- The upper quantile function is measurable. -/
@[fun_prop]
theorem measurable_upperQuantile (μ : Measure ℝ) : Measurable μ.upperQuantile :=
  TauCeti.measurable_of_monotoneOn_Ioo_of_eq_const (monotoneOn_upperQuantile μ) fun _ hs ↦
    hs.elim (upperQuantile_of_neg μ) fun h ↦ upperQuantile_of_one_le μ h.le

/-! ### Measurability in the law and the level -/

/-- The lower quantile is jointly measurable in a probability measure and a level in `(0, 1)`. -/
@[fun_prop]
theorem measurable_quantile_probabilityMeasure :
    Measurable fun q : ProbabilityMeasure ℝ × Ioo (0 : ℝ) 1 ↦
      (q.1 : Measure ℝ).quantile q.2 := by
  first
    -- The Giry measurable structure is generated by evaluation on measurable sets, and
    -- `quantile_le_iff` expresses each sublevel set using evaluation on a closed ray.
  | apply measurable_of_Iic
    intro x
    have hcdf : Measurable fun P : ProbabilityMeasure ℝ ↦ cdf (P : Measure ℝ) x := by
      simp only [cdf_eq_real, Measure.real]
      exact ((Measure.measurable_coe measurableSet_Iic).comp
        measurable_subtype_coe).ennreal_toReal
    have hset :
        (fun q : ProbabilityMeasure ℝ × Ioo (0 : ℝ) 1 ↦
          (q.1 : Measure ℝ).quantile q.2) ⁻¹' Iic x =
          {q | (q.2 : ℝ) ≤ cdf (q.1 : Measure ℝ) x} := by
      ext q
      exact quantile_le_iff (q.1 : Measure ℝ) q.2.2.1 q.2.2.2
    rw [hset]
    exact measurableSet_le (measurable_subtype_coe.comp measurable_snd)
      (hcdf.comp measurable_fst)

/-- The upper quantile is jointly measurable in a probability measure and a level in `(0, 1)`. -/
@[fun_prop]
theorem measurable_upperQuantile_probabilityMeasure :
    Measurable fun q : ProbabilityMeasure ℝ × Ioo (0 : ℝ) 1 ↦
      (q.1 : Measure ℝ).upperQuantile q.2 := by
  first
    -- `upperQuantile_lt_iff` expresses each strict sublevel set using the mass that the varying law
    -- assigns to a fixed open ray.
  | apply measurable_of_Iio
    intro x
    have hleft : Measurable fun P : ProbabilityMeasure ℝ ↦
        (P : Measure ℝ).real (Iio x) := by
      simp only [Measure.real]
      exact ((Measure.measurable_coe measurableSet_Iio).comp
        measurable_subtype_coe).ennreal_toReal
    have hset :
        (fun q : ProbabilityMeasure ℝ × Ioo (0 : ℝ) 1 ↦
          (q.1 : Measure ℝ).upperQuantile q.2) ⁻¹' Iio x =
          {q | (q.2 : ℝ) < (q.1 : Measure ℝ).real (Iio x)} := by
      ext q
      exact upperQuantile_lt_iff (q.1 : Measure ℝ) q.2.2.1 q.2.2.2
    rw [hset]
    exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd)
      (hleft.comp measurable_fst)

/-- Quantiles of a measurable family of probability measures are jointly measurable in the
family parameter and an interior level. -/
@[fun_prop]
theorem measurable_quantile_cdf_family {α : Type*} [MeasurableSpace α]
    (μ : α → Measure ℝ) (hμ : Measurable μ) (hprob : ∀ a, IsProbabilityMeasure (μ a)) :
    Measurable fun q : α × Ioo (0 : ℝ) 1 ↦ (μ q.1).quantile q.2 := by
  first
  | let P : α → ProbabilityMeasure ℝ := fun a ↦ ⟨μ a, hprob a⟩
    have hP : Measurable P := hμ.subtype_mk
    exact measurable_quantile_probabilityMeasure.comp
      ((hP.comp measurable_fst).prodMk measurable_snd)

/-- Upper quantiles of a measurable family of probability measures are jointly measurable in the
family parameter and an interior level. -/
@[fun_prop]
theorem measurable_upperQuantile_cdf_family {α : Type*} [MeasurableSpace α]
    (μ : α → Measure ℝ) (hμ : Measurable μ) (hprob : ∀ a, IsProbabilityMeasure (μ a)) :
    Measurable fun q : α × Ioo (0 : ℝ) 1 ↦ (μ q.1).upperQuantile q.2 := by
  first
  | let P : α → ProbabilityMeasure ℝ := fun a ↦ ⟨μ a, hprob a⟩
    have hP : Measurable P := hμ.subtype_mk
    exact measurable_upperQuantile_probabilityMeasure.comp
      ((hP.comp measurable_fst).prodMk measurable_snd)

/-- **Inverse transform sampling.** The quantile function of a probability law on `ℝ` pushes the
uniform law on the open unit interval forward to that law. -/
theorem map_quantile_volume_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map μ.quantile = μ := by
  first
  | have huniform : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
    have _ : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map μ.quantile) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_quantile μ).aemeasurable).mpr huniform
    refine Measure.ext_of_Iic _ _ fun x ↦ ?_
    rw [Measure.map_apply (measurable_quantile μ) measurableSet_Iic,
      Measure.restrict_apply (measurable_quantile μ measurableSet_Iic), ← ofReal_cdf μ x]
    have hsub : μ.quantile ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Ioc (0 : ℝ) (cdf μ x) \ {(1 : ℝ)} := by
      ext s
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, Set.mem_sdiff, mem_Ioc,
        mem_singleton_iff]
      constructor
      · rintro ⟨hq, hs0, hs1⟩
        exact ⟨⟨hs0, (quantile_le_iff μ hs0 hs1).mp hq⟩, hs1.ne⟩
      · rintro ⟨⟨hs0, hsc⟩, hs1⟩
        have hlt : s < 1 := lt_of_le_of_ne (hsc.trans (cdf_le_one μ x)) hs1
        exact ⟨(quantile_le_iff μ hs0 hlt).mpr hsc, hs0, hlt⟩
    rw [hsub, measure_sdiff_null (measure_singleton _), Real.volume_Ioc, sub_zero]

/-- Inverse transform sampling, as a measure-preserving map from the uniform law on the open unit
interval. -/
theorem measurePreserving_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving μ.quantile (volume.restrict (Ioo (0 : ℝ) 1)) μ :=
  ⟨measurable_quantile μ, map_quantile_volume_Ioo μ⟩

/-- The quantile function of a real probability law is integrable on the levels `Ioo 0 1` exactly
when the law has a finite first moment. -/
theorem integrableOn_quantile_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IntegrableOn μ.quantile (Ioo 0 1) ↔ Integrable id μ :=
  (measurePreserving_quantile μ).integrable_comp aestronglyMeasurable_id

/-- **The mean as the average quantile.** By inverse transform sampling, the average over the levels
`Ioo 0 1` of the quantile function of a real probability law is its mean. Both sides vanish when
the law has no finite first moment. -/
theorem setIntegral_quantile_eq_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ t in Ioo 0 1, μ.quantile t = ∫ x, x ∂μ := by
  first
  | rw [← integral_map (f := fun x ↦ x) (measurable_quantile μ).aemeasurable
      aestronglyMeasurable_id, map_quantile_volume_Ioo]

/-- **The quantile of a monotone rearrangement.** The law of `f (U)`, for `U` uniform on the open
unit interval and `f` monotone there, has quantile function `f` at almost every level: they can
differ only at the countably many levels where `f` jumps. -/
theorem quantile_map_volume_Ioo_ae {f : ℝ → ℝ} (hf : MonotoneOn f (Ioo 0 1)) :
    ((volume.restrict (Ioo (0 : ℝ) 1)).map f).quantile =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
  first
  | set U := volume.restrict (Ioo (0 : ℝ) 1)
    have : IsProbabilityMeasure U := ⟨by simp [U]⟩
    have hfm : AEMeasurable f U := aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hf
    set ν := U.map f
    -- The cumulative mass of `ν` below `x` is the length of the levels sent at most to `x`.
    have hcdf (x : ℝ) : ENNReal.ofReal (cdf ν x) = volume (f ⁻¹' Iic x ∩ Ioo 0 1) := by
      rw [ofReal_cdf, map_apply_of_aemeasurable hfm measurableSet_Iic,
        restrict_apply' measurableSet_Ioo]
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [hf.countable_not_continuousWithinAt.ae_notMem volume] with t hct ht
    have hc : ContinuousAt f t := by
      by_contra h
      exact hct ⟨ht, fun h' ↦ h (h'.continuousAt (Ioo_mem_nhds ht.1 ht.2))⟩
    refine le_antisymm ((quantile_le_iff ν ht.1 ht.2).2 ?_) (le_of_forall_lt fun x hx ↦ ?_)
    · -- Every level in `(0, t]` is sent at most to `f t`.
      rw [← ENNReal.ofReal_le_ofReal_iff (cdf_nonneg ν _), hcdf]
      calc ENNReal.ofReal t = volume (Ioc 0 t) := by simp
        _ ≤ volume (f ⁻¹' Iic (f t) ∩ Ioo 0 1) := measure_mono fun s hs ↦
            ⟨hf ⟨hs.1, hs.2.trans_lt ht.2⟩ ht hs.2, hs.1, hs.2.trans_lt ht.2⟩
    · -- Below `f t`, continuity at `t` produces a level `s₀ < t` already sent above `x`.
      obtain ⟨s₀, ⟨hs₀x, hs₀⟩, hs₀t⟩ : ∃ s₀, (x < f s₀ ∧ s₀ ∈ Ioo 0 1) ∧ s₀ < t :=
        (((hc.eventually (eventually_gt_nhds hx)).and (Ioo_mem_nhds ht.1 ht.2)).filter_mono
          nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[<] t)
      rw [lt_quantile_iff ν ht.1 ht.2, ← ENNReal.ofReal_lt_ofReal_iff ht.1, hcdf]
      calc volume (f ⁻¹' Iic x ∩ Ioo 0 1) ≤ volume (Ioo 0 s₀) := measure_mono fun s hs ↦
            ⟨hs.2.1, lt_of_not_ge fun h ↦ (hs₀x.trans_le (hf hs₀ hs.2 h)).not_ge hs.1⟩
        _ < ENNReal.ofReal t := by simpa using (ENNReal.ofReal_lt_ofReal_iff ht.1).2 hs₀t

/-- **The probability integral transform.** The CDF of an atomless probability measure on
`ℝ` pushes the measure forward to Lebesgue measure restricted to `[0, 1]`. -/
@[simp]
theorem cdf_map_eq_volume_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    Measure.map (cdf ν) ν = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first
  | have hmeas : Measurable (cdf ν) := (cdf ν).mono.measurable
    refine Measure.ext_of_Iic _ _ (fun y => ?_)
    rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    rcases lt_or_ge y 1 with hy1 | hy1
    · have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 y := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨hxy, hx0, _⟩; exact ⟨hx0, hxy⟩
        · rintro ⟨hx0, hxy⟩; exact ⟨hxy, hx0, le_of_lt (lt_of_le_of_lt hxy hy1)⟩
      rw [hrset, Real.volume_Icc, sub_zero]
      exact cdf_sublevel_measure ν y hy1
    · have hset : cdf ν ⁻¹' Iic y = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact le_trans (cdf_le_one ν x) hy1
      have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc, and_iff_right_iff_imp]
        rintro ⟨_, hx1⟩; exact le_trans hx1 hy1
      rw [hset, hrset, measure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- On the closed unit interval, the CDF and quantile are inverse almost everywhere. -/
theorem cdf_quantile_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (fun u => cdf ν (ν.quantile u)) =ᵐ[volume.restrict (Set.Icc 0 1)] id := by
  first
  | refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [Set.Countable.ae_notMem
        ((Set.countable_singleton (1 : ℝ)).insert 0) volume] with u hu huIcc
    have hu0 : u ≠ 0 := fun h => hu (by simp [h])
    have hu1 : u ≠ 1 := fun h => hu (by simp [h])
    have h0 : 0 < u := lt_of_le_of_ne huIcc.1 (Ne.symm hu0)
    have h1 : u < 1 := lt_of_le_of_ne huIcc.2 hu1
    exact cdf_quantile ν (continuous_cdf_of_noAtoms ν) h0 h1

/-- The part of the plateau of `cdf ν` that lies strictly to the right of a point `y` whose
level `cdf ν y` is still below `1` is null. Equivalently: the atom of a real law sits at the *left*
end of its plateau and never strictly inside one, so above a point of level `< 1` the cumulative
function is not constant on a set of positive mass. -/
private theorem ae_not_of_lt_of_cdf_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] {y : ℝ}
    (hy : cdf ν y < 1) : ∀ᶠ x in ae ν, ¬ (y < x ∧ cdf ν y = cdf ν x) := by
  first
    -- `S` is the plateau of `cdf ν` at the level `cdf ν y`, cut off at `y`. The goal is `ν S = 0`,
    -- once `ae_iff` and `hnotMem` below have turned it into a measure-zero statement.
  | set S : Set ℝ := {z | y < z ∧ cdf ν y = cdf ν z} with hSdef
    -- `cdf ν` rises to `1 > cdf ν y`, so it eventually leaves the level `cdf ν y` for good, and no
    -- plateau point can lie above the bound that this produces.
    have hbdd : BddAbove S := by
      obtain ⟨M, hM⟩ :=
        eventually_atTop.mp ((tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy))
      refine ⟨M, fun z hz ↦ le_of_not_gt fun hzM ↦ ?_⟩
      exact absurd (hM z (le_of_lt hzM)) (not_lt_of_ge hz.2.symm.le)
    have hnotMem : {z : ℝ | ¬ ¬ (y < z ∧ cdf ν y = cdf ν z)} = S := by
      ext z
      simp only [Set.mem_ofPred_eq, not_not, hSdef]
    -- Case split on whether the plateau has any points at all. If it has none it is null outright.
    -- If it does, let `b` be its top point: `hle` below puts all of `S` inside `(y, b]`, and `hstab`
    -- shows the cumulative function is still exactly `cdf ν y` at every point of the open interval
    -- `(y, b)`. Each subcase of the next split then makes `S` null, and `measure_mono_null` turns
    -- that into the goal.
    by_cases hSne : S.Nonempty
    · set b : ℝ := sSup S with hbdef
      have hle : ∀ z : ℝ, z ∈ S → z ≤ b := fun z hz ↦ le_csSup hbdd hz
      have hstab : ∀ z : ℝ, y < z → z < b → cdf ν y = cdf ν z := by
        rintro z hz1 hz2
        obtain ⟨w, hw, hzw⟩ := exists_lt_of_lt_csSup (s := S) (b := z) hSne (hbdef ▸ hz2)
        have hupper : cdf ν z ≤ cdf ν y :=
          (monotone_cdf ν hzw.le).trans (le_of_eq ((hSdef ▸ hw).2).symm)
        exact le_antisymm (monotone_cdf ν hz1.le) hupper
      -- If the top of the plateau has the same level as `y`, the plateau is precisely the atom at
      -- `b`, whose mass is the increment `cdf ν b - cdf ν y = 0`; `S ⊆ Ioc y b` is then null as well.
      by_cases hb : cdf ν b = cdf ν y
      · have hnull : ν (Ioc y b) = 0 := by
          rw [← measure_cdf ν, StieltjesFunction.measure_Ioc, hb, sub_self, ENNReal.ofReal_zero]
        refine ae_iff.mpr ?_
        rw [hnotMem]
        exact measure_mono_null (s := S) (t := Ioc y b) (fun z hz ↦ ⟨hz.1, hle z hz⟩) hnull
      -- Otherwise `b` is above the level of the plateau, so `b` itself is no plateau point (`hne`
      -- below) while every point of `(y, b)` still sits at the level `cdf ν y` by `hstab`. The
      -- interval `(y, b)` would therefore carry the whole atom at `b`, which a constant interval
      -- cannot do. The countable cover below is what rules it out: the half-open intervals
      -- `Ioc y (b - (b - y) / (n + 2))` climb towards `b` while staying inside `(y, b)`, so each has
      -- the null increment `cdf ν y - cdf ν y = 0`, and together they cover `(y, b)`. Since
      -- `S ⊆ Ioo y b` by `hle` and `hne`, `measure_mono_null` then finishes.
      · have hyb : y < b := by
          obtain ⟨z, hzS⟩ := hSne
          exact lt_of_lt_of_le hzS.1 (hle z hzS)
        have hneS : (0 : ℝ) < b - y := sub_pos.2 hyb
        have hne : ∀ z : ℝ, z ∈ S → z ≠ b := by
          rintro z hz rfl
          exact hb ((hSdef ▸ hz).2).symm
        -- The cover: given `z` in `(y, b)`, take `n` with `(b - y) / (b - z) < n`, which pushes the
        -- right endpoint `b - (b - y) / (n + 2)` strictly between `z` and `b`, so `z` belongs to the
        -- `n`-th interval.
        have hsub : Ioo y b ⊆ ⋃ n : ℕ, Ioc y (b - (b - y) / (n + 2)) := by
          intro z hz
          obtain ⟨n, hn⟩ := exists_nat_gt ((b - y) / (b - z))
          have h1 : (b - y) / (b - z) < n + 1 := by linarith
          have h2pos : (0 : ℝ) < b - z := sub_pos.2 hz.2
          have h2 : (b - y) / (n + 2) < b - z := by
            rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)]
            rw [div_lt_iff₀ h2pos] at h1
            linarith
          have hmem : y < z ∧ z < b - (b - y) / (n + 2) := ⟨hz.1, by linarith [h2, hz.1]⟩
          exact mem_iUnion.2 ⟨n, hmem.1, le_of_lt hmem.2⟩
        refine ae_iff.mpr ?_
        rw [hnotMem]
        refine measure_mono_null (s := S) (t := Ioo y b)
          (fun z hz ↦ ⟨hz.1, lt_of_le_of_ne (hle z hz) (hne z hz)⟩) ?_
        refine le_antisymm ?_ bot_le
        -- Countable subadditivity bounds the interval by the sum of the increments of the covering
        -- intervals, and each increment vanishes because `hstab` makes the cumulative function
        -- constant at the level `cdf ν y` throughout `(y, b)`.
        calc ν (Ioo y b) ≤ ν (⋃ n : ℕ, Ioc y (b - (b - y) / (n + 2))) := measure_mono hsub
          _ ≤ ∑' n : ℕ, ν (Ioc y (b - (b - y) / (n + 2))) := measure_iUnion_le _
          _ = 0 := ENNReal.tsum_eq_zero.2 fun n ↦ by
            have h1div : (1 : ℝ) / (n + 2) < 1 :=
              (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)).2 (by
                have _h : (1 : ℝ) ≤ n + 1 := by
                  exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
                linarith)
            have hlow : (b - y) / (n + 2) < b - y := by
              rw [div_eq_mul_one_div]
              simpa using mul_lt_mul_of_pos_left h1div hneS
            have hpos : (0 : ℝ) < (b - y) / (n + 2) := div_pos hneS (by positivity)
            have hmem : y < b - (b - y) / (n + 2) ∧ b - (b - y) / (n + 2) < b :=
              ⟨by linarith, by simpa using sub_lt_sub_left hpos b⟩
            rw [← measure_cdf ν, StieltjesFunction.measure_Ioc, (hstab _ hmem.1 hmem.2).symm,
              sub_self, ENNReal.ofReal_zero]
    · refine ae_iff.mpr ?_
      rw [hnotMem, not_nonempty_iff_eq_empty.mp hSne, measure_empty]

/-- The quantile of the CDF is the identity almost everywhere, for every real probability measure.
The cumulative distribution function of a law with atoms has plateaus, but the part of a plateau
strictly to the right of a point whose cumulative mass is below `1` is null, so almost every
point is the least point reaching its own level. -/
theorem quantile_cdf_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (fun x => ν.quantile (cdf ν x)) =ᵐ[ν] id := by
  first
  | have hplat : ∀ q : ℚ, cdf ν q < 1 → ∀ᵐ (x : ℝ) ∂ν, ¬ (q < x ∧ cdf ν q = cdf ν x) :=
      fun q hq ↦ ae_not_of_lt_of_cdf_eq hq
    have htop : ∀ q : ℚ, cdf ν q = 1 → ∀ᵐ (x : ℝ) ∂ν, ¬ (q < x ∧ cdf ν q = cdf ν x) := by
      intro q hq
      have hnull : ν (Ioi (q : ℝ)) = 0 := by
        have hIic : ν (Iic (q : ℝ)) = 1 := by rw [← ofReal_cdf ν q, hq]; simp
        rw [← compl_Iic, measure_compl measurableSet_Iic (by rw [hIic]; simp), hIic]
        simp
      have hmem : ∀ᶠ (x : ℝ) in ae ν, x ∉ Ioi (q : ℝ) := by
        refine ae_iff.2 ?_
        have hset : {a : ℝ | ¬ a ∉ Ioi (q : ℝ)} = Ioi (q : ℝ) := by
          ext a
          simp
        rw [hset]
        exact hnull
      filter_upwards [hmem] with x hx
      exact fun hqx ↦ hx hqx.1
    have hplateau : ∀ᵐ (x : ℝ) ∂ν, ∀ q : ℚ, ¬ (q < x ∧ cdf ν q = cdf ν x) :=
      (eventually_countable_forall (l := ae ν) (ι := ℚ) (α := ℝ)
        (p := fun x q ↦ ¬ (q < x ∧ cdf ν q = cdf ν x))).2 fun q ↦ by
          by_cases hq : cdf ν q < 1
          · exact hplat q hq
          · exact htop q (le_antisymm (cdf_le_one ν q) (le_of_not_gt hq))
    have hpos : ∀ᵐ (x : ℝ) ∂ν, 0 < cdf ν x := by
      filter_upwards [hplateau] with x hx
      have hne0 : cdf ν x ≠ 0 := by
        rintro h0
        obtain ⟨q, _, hq2⟩ := exists_rat_btwn (show x - 1 < x from by linarith)
        have hq0 : cdf ν q = 0 := by
          refine le_antisymm ?_ (cdf_nonneg ν _)
          simpa [h0] using monotone_cdf ν hq2.le
        exact hx q ⟨hq2, h0 ▸ hq0⟩
      exact lt_of_le_of_ne (cdf_nonneg ν x) (Ne.symm hne0)
    filter_upwards [hpos, hplateau] with x hx hqx
    simp only [id_eq]
    rw [quantile_def]
    have hmem : (x : ℝ) ∈ {z | cdf ν x ≤ cdf ν z} := Set.mem_ofPred_eq.mpr le_rfl
    refine le_antisymm (csInf_le (bddBelow_setOf_le_cdf ν hx) hmem) ?_
    refine le_csInf ⟨x, hmem⟩ ?_
    intro z hz
    by_contra hzx
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_of_not_ge hzx)
    have hqc : cdf ν q = cdf ν x :=
      le_antisymm (monotone_cdf ν hq2.le) (hz.trans (monotone_cdf ν hq1.le))
    exact hqx q ⟨hq2, hqc⟩

/-- **The CDF/quantile transport of an atomless real law.** The cumulative distribution function
and the quantile function of an atomless probability measure `ν` on `ℝ` push `ν` and Lebesgue
measure restricted to `[0, 1]` forward onto one another, and are mutually inverse almost
everywhere; together they are a mod-zero isomorphism between `ν` and the unit interval. -/
def realMod0MeasureIso (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : TauCeti.Mod0MeasureIso ℝ ℝ ν (volume.restrict (Set.Icc 0 1)) where
  toFun := cdf ν
  invFun := ν.quantile
  measurable_toFun := (cdf ν).mono.measurable
  measurable_invFun := measurable_quantile ν
  map_toFun := cdf_map_eq_volume_restrict ν
  map_invFun := by
    first
    | simpa only [MeasureTheory.restrict_Ioo_eq_restrict_Icc] using (map_quantile_volume_Ioo ν)
  left_inv_ae := quantile_cdf_ae ν
  right_inv_ae := cdf_quantile_ae ν

@[simp]
theorem realMod0MeasureIso_toFun (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : (realMod0MeasureIso ν).toFun = cdf ν :=
  (rfl)

@[simp]
theorem realMod0MeasureIso_invFun (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : (realMod0MeasureIso ν).invFun = ν.quantile :=
  (rfl)

end MeasureTheory.Measure
end -- closes the original EOF section from source line 144
end -- closes the original EOF section from source line 142
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Probability/Quantile.lean -/

/- BEGIN SOURCE: TauCeti/Probability/ConditionalProbability.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Conditional measures and the law of total probability

A finite measure is the sum, over the values of a random variable with countably many values, of
its conditional measures on the fibres weighted by the masses of the fibres:

```text
μ = Measure.sum fun b => μ (f ⁻¹' {b}) • μ[|f ⁻¹' {b}].
```

Mathlib's `ProbabilityTheory.sum_meas_smul_cond_fiber` is the same decomposition for a random
variable valued in a `Fintype`; this file extends it to countable value spaces with measurable
singletons, where the finite sum of measures becomes `MeasureTheory.Measure.sum`. Fibres of mass
zero contribute nothing, so no positivity hypothesis on the fibres is needed.

Conditioning on almost-everywhere equal events gives equal conditional measures, and a function
bounded on a measurable event is integrable for the conditional measure on it. A measurable map
that scales measure by a constant factor carries conditional measures to conditional measures.
Conditioning a probability measure away from a single point removes that atom and rescales the
rest by `1 / (1 - μ {a})`; this computes the masses of, and integrals against, the conditioned
measure. Conditional measures on intervals agree across endpoint conventions whenever the relevant
endpoint atoms vanish. These identities apply to any partially ordered measurable space,
including atomless laws and atomic laws with null endpoints.

For any probability law, conditioning on a positive-mass measurable event has total variation
distance twice the excluded mass. Conditioning on events whose masses tend to one therefore
recovers the law.

## Main results

* `ProbabilityTheory.sum_meas_smul_cond_fiber_of_countable`
* `ProbabilityTheory.cond_congr_ae`
* `ProbabilityTheory.integrable_cond_of_norm_le`
* `ProbabilityTheory.map_cond_preimage`
* `ProbabilityTheory.cond_compl_singleton_real`,
  `ProbabilityTheory.cond_compl_singleton_real_singleton`,
  `ProbabilityTheory.integrable_cond_compl_singleton_iff`,
  `ProbabilityTheory.integral_cond_compl_singleton`
* `MeasureTheory.Measure.cond_Icc_eq_cond_Ioc`, `MeasureTheory.Measure.cond_Ioo_eq_cond_Ioc`,
  `MeasureTheory.Measure.cond_Ico_eq_cond_Ioc`
* `MeasureTheory.Measure.tvDist_cond_self`, `MeasureTheory.Measure.tendsto_tvDist_cond` —
  the distance to a conditioned law and convergence as the retained mass tends to one
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]

/-- Conditioning on almost-everywhere equal events gives equal conditional measures. -/
theorem cond_congr_ae {μ : Measure Ω} {s t : Set Ω} (h : s =ᵐ[μ] t) :
    μ[|s] = μ[|t] := by
  first
  | rw [cond, cond, measure_congr h, Measure.restrict_congr_set h]

/-- A function whose norm is bounded on a measurable event `s` is integrable for the conditional
measure `μ[|s]`. For instance, a point drawn uniformly from a bounded Borel set of a normed space
has integrable position. -/
theorem integrable_cond_of_norm_le {E : Type*} [NormedAddCommGroup E] {μ : Measure Ω}
    {s : Set Ω} {f : Ω → E} (hs : MeasurableSet s) (hf : AEStronglyMeasurable f μ[|s]) {C : ℝ}
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) : Integrable f μ[|s] :=
  Integrable.of_bound hf C ((ae_cond_mem hs).mono hC)

/-- A measurable map that scales measure by a constant factor transports conditional measures:
if `μ (f ⁻¹' A) = k * ν A` for every measurable `A`, with `k ≠ 0` finite, then `f` carries `μ`
conditioned on `f ⁻¹' t` to `ν` conditioned on `t`. Translations and linear isometries of a
Euclidean space (with `k = 1`) and nonzero dilations are the typical examples. -/
theorem map_cond_preimage {μ : Measure Ω} {ν : Measure β} {f : Ω → β} (hf : Measurable f)
    {k : ENNReal} (hk₀ : k ≠ 0) (hk : k ≠ ⊤) (h : ∀ A, MeasurableSet A → μ (f ⁻¹' A) = k * ν A)
    {t : Set β} (ht : MeasurableSet t) :
    (μ[|f ⁻¹' t]).map f = ν[|t] := by
  first
  | ext A hA
    rw [Measure.map_apply hf hA, cond_apply' (hf hA), cond_apply' hA, ← preimage_inter,
      h _ ht, h _ (ht.inter hA), ENNReal.mul_inv (.inl hk₀) (.inl hk), mul_mul_mul_comm,
      ENNReal.inv_mul_cancel hk₀ hk, one_mul]

/-- The **law of total probability** for a random variable with countably many values: a finite
measure `μ` is the sum of its conditional measures on the fibres of a measurable `f`, each weighted
by the mass of its fibre. -/
theorem sum_meas_smul_cond_fiber_of_countable [Countable β] [MeasurableSingletonClass β]
    {f : Ω → β} (hf : Measurable f) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Measure.sum (fun b => μ (f ⁻¹' {b}) • μ[|f ⁻¹' {b}]) = μ := by
  first
  | ext E hE
    have hfib : ∀ b, MeasurableSet (f ⁻¹' {b}) := fun b => hf (measurableSet_singleton b)
    calc (Measure.sum fun b => μ (f ⁻¹' {b}) • μ[|f ⁻¹' {b}]) E
        = ∑' b, μ (f ⁻¹' {b} ∩ E) := by
          simp only [Measure.sum_apply _ hE, Measure.smul_apply, smul_eq_mul]
          simp_rw [mul_comm (μ _), cond_mul_eq_inter (hfib _)]
      _ = μ E := by
          rw [← measure_iUnion (fun b c hbc =>
            ((Set.disjoint_singleton.2 hbc).preimage f).mono Set.inter_subset_left
              Set.inter_subset_left) fun b => (hfib b).inter hE]
          congr 1
          ext ω
          simp

/-! ### Removing one atom -/

section ComplSingleton

variable [MeasurableSingletonClass Ω] {μ : Measure Ω} {a : Ω}

/-- Conditioning away from a point leaves no mass at that point. -/
@[simp]
theorem cond_compl_singleton_apply_self : μ[|{a}ᶜ] {a} = 0 := by
  first
  | simp [cond_apply (measurableSet_singleton a).compl]

/-- A function is integrable for a finite measure conditioned away from a point exactly when it is
integrable for the measure itself: only the single atom at that point differs. -/
theorem integrable_cond_compl_singleton_iff [IsFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] {f : Ω → E} : Integrable f μ[|{a}ᶜ] ↔ Integrable f μ := by
  first
  | have hatom : IntegrableOn f {a} μ := integrableOn_singleton
    have hcompl : Integrable f μ[|{a}ᶜ] ↔ IntegrableOn f {a}ᶜ μ := by
      by_cases hμ : μ {a}ᶜ = 0
      · simp [IntegrableOn, cond, Measure.restrict_eq_zero.2 hμ]
      · rw [cond, integrable_smul_measure (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
          (ENNReal.inv_ne_top.2 hμ), IntegrableOn]
    rw [hcompl, ← integrableOn_univ, ← compl_union_self {a}, integrableOn_union,
      and_iff_left hatom]

variable [IsProbabilityMeasure μ]

/-- Conditioning a probability measure away from a point removes all mass exactly when the measure
is the point mass there. -/
theorem cond_compl_singleton_eq_zero_iff : μ[|{a}ᶜ] = 0 ↔ μ {a} = 1 := by
  first
  | rw [cond_eq_zero, prob_compl_eq_one_sub (measurableSet_singleton a)]
    constructor
    · rintro (h | h)
      · exact absurd h (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      · exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.1 h)
    · intro h
      simp [h]

/-- A probability measure conditioned away from a point is a probability measure unless it is the
point mass there. -/
theorem isProbabilityMeasure_cond_compl_singleton (h : μ {a} ≠ 1) :
    IsProbabilityMeasure μ[|{a}ᶜ] :=
  cond_isProbabilityMeasure fun h' => h (cond_compl_singleton_eq_zero_iff.1 (by simp [h']))

/-- Conditioning a probability measure away from a point rescales the other singleton masses by
`1 / (1 - μ {a})`. -/
theorem cond_compl_singleton_apply_singleton {x : Ω} (hx : x ≠ a) :
    μ[|{a}ᶜ] {x} = (1 - μ {a})⁻¹ * μ {x} := by
  first
  | rw [cond_apply (measurableSet_singleton a).compl,
      prob_compl_eq_one_sub (measurableSet_singleton a),
      inter_eq_right.2 (singleton_subset_iff.2 hx)]

/-- Conditioning a probability measure away from a point removes that point from every set and
rescales the remaining real mass by `1 / (1 - μ.real {a})`. -/
theorem cond_compl_singleton_real (s : Set Ω) :
    (μ[|{a}ᶜ]).real s = μ.real (s \ {a}) / (1 - μ.real {a}) := by
  first
  | rw [measureReal_def, cond_apply (measurableSet_singleton a).compl,
      prob_compl_eq_one_sub (measurableSet_singleton a)]
    simp [measureReal_def, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      sdiff_eq_compl_inter, div_eq_inv_mul]

/-- Conditioning a probability measure away from a point rescales the other real singleton masses
by `1 / (1 - μ.real {a})`. -/
theorem cond_compl_singleton_real_singleton {x : Ω} (hx : x ≠ a) :
    (μ[|{a}ᶜ]).real {x} = μ.real {x} / (1 - μ.real {a}) := by
  first
  | rw [cond_compl_singleton_real, sdiff_singleton_eq_self fun h => hx (mem_singleton_iff.1 h).symm]

/-- Integration against a probability measure conditioned away from a point removes the
contribution of the atom there and rescales by `1 / (1 - μ.real {a})`. -/
theorem integral_cond_compl_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : Ω → E} (hf : Integrable f μ) :
    ∫ x, f x ∂μ[|{a}ᶜ] = (1 - μ.real {a})⁻¹ • (∫ x, f x ∂μ - μ.real {a} • f a) := by
  first
  | rw [cond, integral_smul_measure, setIntegral_compl (measurableSet_singleton a) hf,
      integral_singleton, ENNReal.toReal_inv, ← measureReal_def,
      probReal_compl_eq_one_sub (measurableSet_singleton a)]

/-- For a function vanishing at `a`, integration against a probability measure conditioned away
from `a` is integration against the measure itself, rescaled by `1 / (1 - μ.real {a})`. No
integrability is needed: both sides vanish together when the function is not integrable. -/
theorem integral_cond_compl_singleton_of_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Ω → E} (hf : f a = 0) :
    ∫ x, f x ∂μ[|{a}ᶜ] = (1 - μ.real {a})⁻¹ • ∫ x, f x ∂μ := by
  first
  | rw [cond, integral_smul_measure,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [notMem_compl_iff, mem_singleton_iff] at hx
        rw [hx, hf],
      ENNReal.toReal_inv, ← measureReal_def, probReal_compl_eq_one_sub (measurableSet_singleton a)]

end ComplSingleton

end ProbabilityTheory

namespace MeasureTheory.Measure

open Filter ProbabilityTheory
open scoped ENNReal Topology

/-- Mathlib's total variation distance from a probability law conditioned on a positive-mass
measurable event to the original law is twice the excluded mass. -/
theorem tvDist_cond_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) (hμA : μ A ≠ 0) :
    tvDist (cond μ A) μ = 2 * (1 - μ.real A) := by
  first
  | let _ := cond_isProbabilityMeasure hμA
    have hH : IsHahnDecomposition μ (cond μ A) A := by
      refine ⟨hA, ?_, ?_⟩
      · rw [ProbabilityTheory.cond, Measure.restrict_smul, Measure.restrict_restrict hA,
          inter_self]
        apply Measure.le_iff.mpr
        intro B hB
        rw [Measure.smul_apply, smul_eq_mul]
        have hi : 1 ≤ (μ A)⁻¹ := by
          simpa using ENNReal.inv_le_inv.mpr (prob_le_one (μ := μ) (s := A))
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hi
          (bot_le : (0 : ℝ≥0∞) ≤ μ.restrict A B)
      · rw [ProbabilityTheory.cond, Measure.restrict_smul, Measure.restrict_restrict hA.compl]
        simp only [compl_inter_self, Measure.restrict_empty, smul_zero]
        exact bot_le
    have hfull : (cond μ A).real A = 1 := by
      simp only [measureReal_def, cond_apply_self hμA (measure_ne_top μ A), ENNReal.toReal_one]
    have hzero : (cond μ A).real Aᶜ = 0 := by
      simp [measureReal_def, cond_apply hA]
    rw [tvDist_comm, hH.tvDist_eq, hfull, hzero, probReal_compl_eq_one_sub hA]
    ring

/-- Conditioning a probability law on eventually measurable events whose masses tend to one
converges to that law in total variation. -/
theorem tendsto_tvDist_cond {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {l : Filter ι} {A : ι → Set Ω}
    (hA : ∀ᶠ i in l, MeasurableSet (A i))
    (hmass : Tendsto (fun i ↦ μ.real (A i)) l (𝓝 1)) :
    Tendsto (fun i ↦ tvDist (cond μ (A i)) μ) l (𝓝 0) := by
  first
  | have h : Tendsto (fun i ↦ 2 * (1 - μ.real (A i))) l (𝓝 (2 * (1 - 1 : ℝ))) :=
      (tendsto_const_nhds.sub hmass).const_mul 2
    simp only [sub_self, mul_zero] at h
    apply h.congr'
    filter_upwards [hA, hmass.eventually (eventually_gt_nhds zero_lt_one)] with i hi hpos
    exact (μ.tvDist_cond_self hi
      ((measureReal_ne_zero_iff (measure_ne_top μ _)).mp hpos.ne')).symm

variable {α : Type*} [PartialOrder α] [MeasurableSpace α] (μ : Measure α)

/-- Including the lower endpoint does not change the conditional law when its atom vanishes. -/
@[simp]
theorem cond_Icc_eq_cond_Ioc {l r : α} (hl : μ {l} = 0) :
    ProbabilityTheory.cond μ (Icc l r) = ProbabilityTheory.cond μ (Ioc l r) :=
  ProbabilityTheory.cond_congr_ae (Ioc_ae_eq_Icc' hl).symm

/-- Excluding the upper endpoint does not change the conditional law when its atom vanishes. -/
@[simp]
theorem cond_Ioo_eq_cond_Ioc {l r : α} (hr : μ {r} = 0) :
    ProbabilityTheory.cond μ (Ioo l r) = ProbabilityTheory.cond μ (Ioc l r) :=
  ProbabilityTheory.cond_congr_ae (Ioo_ae_eq_Ioc' hr)

/-- The two half-open conditional laws agree when both endpoint atoms vanish. -/
@[simp]
theorem cond_Ico_eq_cond_Ioc {l r : α} (hl : μ {l} = 0) (hr : μ {r} = 0) :
    ProbabilityTheory.cond μ (Ico l r) = ProbabilityTheory.cond μ (Ioc l r) :=
  ProbabilityTheory.cond_congr_ae (Ico_ae_eq_Ioc' hl hr)

end MeasureTheory.Measure
end -- closes the original EOF section from source line 58
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Probability/ConditionalProbability.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Quantile.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: almost every point of a convex set is interior, derivatives of quotients and
-- of local inverses, integrals of inner products, and integrability under conditioning.

/-!
# The height quantile of a convex set

Let `s` be a set of positive finite volume in a finite-dimensional Euclidean space and `e` a
unit vector. The height `⟪e, x⟫` of a point `x` drawn uniformly from `s` has the law
`(volume[|s]).map fun x ↦ ⟪e, x⟫`. Its cumulative distribution function at `c` is the
proportion of the volume of `s` lying below the hyperplane `⟪e, x⟫ = c`, and it is continuous
because hyperplanes are null.

For a convex set the cumulative distribution function takes a value strictly between `0` and
`1` exactly at the heights of interior points of `s`, and it is strictly increasing there.
Hence the quantile function of the height law is a strictly increasing continuous
parametrization of the open interval `⟪e, interior s⟫` by the levels in `Ioo 0 1`. If `s` is
moreover bounded and Borel, the derivative of the volume below a hyperplane is the volume of the
hyperplane section, which is positive at the height of an interior point. The inverse function
theorem then shows that at every level `τ ∈ Ioo 0 1` the quantile `z` has derivative
`volume s / volume {y ∈ (ℝ ∙ e)ᗮ | y + z τ • e ∈ s}`.
For a bounded Borel set `s`, inverse transform sampling shows that the average of the quantile
over the levels is the mean height, that is, the height of the centroid of `s`.

This volume-fraction parametrization of heights is the change of variables in the
Kneser–Süss proof of the equality case of the Brunn–Minkowski inequality for convex bodies:
two bodies of equal volume are compared along each direction at heights cutting off equal
volume fractions.

## Main results

* `TauCeti.nullSingletonClass_map_inner_cond`: the height law has no atoms.
* `TauCeti.cdf_map_inner_cond`: the cumulative distribution function of the height law.
* `TauCeti.continuous_cdf_map_inner_cond`: it is continuous.
* `Convex.cdf_map_inner_cond_mem_Ioo_iff`: for a convex set it lies strictly between `0` and `1`
  exactly at the heights of interior points.
* `Convex.strictMonoOn_cdf_map_inner_cond`: it is strictly increasing there.
* `Convex.image_quantile_map_inner_cond_Ioo`: the quantile maps `Ioo 0 1` onto the heights of
  interior points.
* `Convex.quantile_map_inner_cond_mem_image_interior`: each interior level goes to the height of
  an interior point.
* `Convex.volume_real_hyperplaneSection_quantile_pos`,
  `Convex.continuousOn_volume_real_hyperplaneSection_quantile`: the hyperplane section at the
  quantile has positive volume, depending continuously on the level.
* `Convex.hasDerivAt_quantile_map_inner_cond`: the derivative of the quantile.
* `TauCeti.setIntegral_quantile_map_inner_cond`: the quantile averages to the height of the
  centroid.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25, for the volume-fraction comparison of convex bodies.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.1, for an exposition of the Kneser–Süss argument.
-/

public section

open Filter MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E} {s : Set E}
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The height law gives a Borel set of heights the proportion of the volume of `s` at those
heights. -/
private theorem map_inner_cond_apply (e : E) (s : Set E) {I : Set ℝ} (hI : MeasurableSet I) :
    (volume[|s]).map (fun x ↦ ⟪e, x⟫) I = (volume s)⁻¹ * volume {x ∈ s | ⟪e, x⟫ ∈ I} := by
  first
  | have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
    rw [Measure.map_apply hm hI, cond_apply' (hI.preimage hm)]
    -- `s ∩ (fun x ↦ ⟪e, x⟫) ⁻¹' I` is `{x ∈ s | ⟪e, x⟫ ∈ I}` by definition.
    rfl

private theorem isProbabilityMeasure_map_inner_cond (e : E) (hs0 : volume s ≠ 0)
    (hsi : volume s ≠ ∞) : IsProbabilityMeasure ((volume[|s]).map fun x ↦ ⟪e, x⟫) :=
  have := cond_isProbabilityMeasure_of_finite hs0 hsi
  inferInstance

/-- The law of the height along a unit vector of a point drawn uniformly from any set has no
atoms, since hyperplanes are null. -/
theorem nullSingletonClass_map_inner_cond (he : ‖e‖ = 1) (s : Set E) :
    NullSingletonClass ((volume[|s]).map fun x ↦ ⟪e, x⟫) := by
  first
  | refine ⟨fun c ↦ ?_⟩
    have h : volume {x ∈ (univ : Set E) | ⟪e, x⟫ ∈ ({c} : Set ℝ)} = 0 := by
      rw [volume_sep_inner_mem_eq_setLIntegral e he nullMeasurableSet_univ
        (measurableSet_singleton c)]
      exact setLIntegral_measure_zero _ _ Real.volume_singleton
    rw [map_inner_cond_apply e s (measurableSet_singleton c),
      measure_mono_null (fun x (hx : x ∈ {x ∈ s | ⟪e, x⟫ ∈ ({c} : Set ℝ)}) ↦
        (⟨mem_univ x, hx.2⟩ : x ∈ {x ∈ (univ : Set E) | ⟪e, x⟫ ∈ ({c} : Set ℝ)})) h, mul_zero]

/-- The cumulative distribution function of the height along `e` of a point drawn uniformly from
`s` is the proportion of the volume of `s` below the hyperplane at height `c`. -/
theorem cdf_map_inner_cond (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) (c : ℝ) :
    cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) c =
      volume.real {x ∈ s | ⟪e, x⟫ ≤ c} / volume.real s := by
  first
  | have := isProbabilityMeasure_map_inner_cond e hs0 hsi
    rw [cdf_eq_real, measureReal_def, map_inner_cond_apply e s measurableSet_Iic,
      ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def, measureReal_def, div_eq_inv_mul]
    -- Membership in `Iic c` is `⟪e, x⟫ ≤ c` by definition.
    rfl

/-- The cumulative distribution function of the height law of a set of positive finite volume is
continuous, since hyperplanes are null. -/
theorem continuous_cdf_map_inner_cond (he : ‖e‖ = 1) (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) :
    Continuous (cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫)) :=
  have := isProbabilityMeasure_map_inner_cond e hs0 hsi
  have := nullSingletonClass_map_inner_cond he s
  continuous_cdf_of_noAtoms _

/-- The cumulative distribution function of the height law lies strictly between `0` and `1`
exactly when `s` has positive volume both below and above the height `c`. -/
private theorem cdf_map_inner_cond_mem_Ioo_iff_volume (he : ‖e‖ = 1) (hs0 : volume s ≠ 0)
    (hsi : volume s ≠ ∞) (c : ℝ) :
    cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) c ∈ Ioo 0 1 ↔
      volume {x ∈ s | ⟪e, x⟫ ∈ Iio c} ≠ 0 ∧ volume {x ∈ s | ⟪e, x⟫ ∈ Ioi c} ≠ 0 := by
  first
  | set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
    have := isProbabilityMeasure_map_inner_cond e hs0 hsi
    have := nullSingletonClass_map_inner_cond he s
    have hinv : (volume s)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hsi
    have hlo : 0 < cdf ν c ↔ volume {x ∈ s | ⟪e, x⟫ ∈ Iio c} ≠ 0 := by
      rw [← ENNReal.ofReal_pos, ofReal_cdf, ← measure_congr Iio_ae_eq_Iic, pos_iff_ne_zero,
        map_inner_cond_apply e s measurableSet_Iio, mul_ne_zero_iff, and_iff_right hinv]
    have hhi : cdf ν c < 1 ↔ volume {x ∈ s | ⟪e, x⟫ ∈ Ioi c} ≠ 0 := by
      rw [← ENNReal.ofReal_lt_one, ofReal_cdf, ← tsub_pos_iff_lt, ← prob_compl_eq_one_sub
        measurableSet_Iic, compl_Iic, pos_iff_ne_zero, map_inner_cond_apply e s measurableSet_Ioi,
        mul_ne_zero_iff, and_iff_right hinv]
    rw [mem_Ioo, hlo, hhi]

/-- For a convex set of positive finite volume, the cumulative distribution function of the
height law lies strictly between `0` and `1` exactly at the heights of interior points. -/
theorem _root_.Convex.cdf_map_inner_cond_mem_Ioo_iff (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) {c : ℝ} :
    cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) c ∈ Ioo 0 1 ↔ c ∈ (fun x ↦ ⟪e, x⟫) '' interior s := by
  first
  | rw [cdf_map_inner_cond_mem_Ioo_iff_volume he hs0 hsi]
    constructor
    · rintro ⟨hlo, hhi⟩
      obtain ⟨x, hx, hxc⟩ := hs.interior_inter_nonempty_of_addHaar_inter_ne_zero
        (t := (fun x ↦ ⟪e, x⟫) ⁻¹' Iio c) hlo
      obtain ⟨y, hy, hyc⟩ := hs.interior_inter_nonempty_of_addHaar_inter_ne_zero
        (t := (fun x ↦ ⟪e, x⟫) ⁻¹' Ioi c) hhi
      exact (convex_iff_ordConnected.1 (hs.interior.linear_image (innerₛₗ ℝ e))).out
        ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨le_of_lt hxc, le_of_lt hyc⟩
    · intro hc
      have hnhds : ∀ᶠ t in 𝓝 c, t ∈ (fun x ↦ ⟪e, x⟫) '' interior s :=
        (isOpen_image_inner_interior he s).mem_nhds hc
      obtain ⟨a, hac, x, hx, rfl⟩ := hnhds.exists_lt
      obtain ⟨b, hcb, y, hy, rfl⟩ := hnhds.exists_gt
      exact ⟨(volume_sep_inner_mem_pos isOpen_Iio ⟨x, hx, hac⟩).ne',
        (volume_sep_inner_mem_pos isOpen_Ioi ⟨y, hy, hcb⟩).ne'⟩

/-- For a convex set of positive finite volume, the cumulative distribution function of the
height law is strictly increasing where it lies strictly between `0` and `1`. -/
theorem _root_.Convex.strictMonoOn_cdf_map_inner_cond (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) :
    StrictMonoOn (cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫))
      (cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) ⁻¹' Ioo 0 1) := by
  first
  | set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
    have := isProbabilityMeasure_map_inner_cond e hs0 hsi
    intro c hc c' hc' hcc'
    rw [mem_preimage, hs.cdf_map_inner_cond_mem_Ioo_iff he hs0 hsi] at hc hc'
    -- An interior point lies strictly between the heights `c` and `c'`.
    have hmid := (convex_iff_ordConnected.1 (hs.interior.linear_image (innerₛₗ ℝ e))).out hc hc'
      ⟨by linarith, (by linarith : (c + c') / 2 ≤ c')⟩
    obtain ⟨x, hx, hxc⟩ := hmid
    have hpos : 0 < ν (Ioc c c') := by
      rw [map_inner_cond_apply e s measurableSet_Ioc]
      refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hsi) ((volume_sep_inner_mem_pos isOpen_Ioo
        ⟨x, hx, ?_⟩).trans_le (measure_mono fun y (hy : y ∈ {x ∈ s | ⟪e, x⟫ ∈ Ioo c c'}) ↦
        (⟨hy.1, Ioo_subset_Ioc_self hy.2⟩ : y ∈ {x ∈ s | ⟪e, x⟫ ∈ Ioc c c'}))).ne'
      have hxc' : ⟪e, x⟫ = (c + c') / 2 := hxc
      rw [hxc']
      constructor <;> linarith
    rw [cdf_eq_real, cdf_eq_real, ← Iic_union_Ioc_eq_Iic hcc'.le,
      measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
    exact lt_add_of_pos_right _ (ENNReal.toReal_pos hpos.ne' (measure_ne_top ν _))

/-- For a convex set of positive finite volume, the quantile function of the height law maps the
levels in `Ioo 0 1` onto the heights of interior points. -/
theorem _root_.Convex.image_quantile_map_inner_cond_Ioo (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) :
    ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile '' Ioo 0 1 = (fun x ↦ ⟪e, x⟫) '' interior s := by
  first
  | set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
    have hcont := continuous_cdf_map_inner_cond he hs0 hsi
    refine Subset.antisymm ?_ fun c hc ↦ ?_
    · rintro _ ⟨τ, hτ, rfl⟩
      rw [← hs.cdf_map_inner_cond_mem_Ioo_iff he hs0 hsi, cdf_quantile ν hcont hτ.1 hτ.2]
      exact hτ
    · rw [← hs.cdf_map_inner_cond_mem_Ioo_iff he hs0 hsi] at hc
      exact ⟨cdf ν c, hc, quantile_cdf ν (hs.strictMonoOn_cdf_map_inner_cond he hs0 hsi) hc⟩

/-- For a convex set of positive finite volume, the quantile function of the height law takes
every level in `Ioo 0 1` to the height of an interior point. -/
theorem _root_.Convex.quantile_map_inner_cond_mem_image_interior (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) :
    ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ ∈ (fun x ↦ ⟪e, x⟫) '' interior s :=
  hs.image_quantile_map_inner_cond_Ioo he hs0 hsi ▸ mem_image_of_mem _ hτ

/-- The hyperplane section of a bounded convex set of positive volume at its height quantile has
positive finite volume at every level in `Ioo 0 1`. -/
theorem _root_.Convex.volume_real_hyperplaneSection_quantile_pos (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hs0 : volume s ≠ 0) (he : ‖e‖ = 1) {τ : ℝ}
    (hτ : τ ∈ Ioo 0 1) :
    0 < volume.real {y : (ℝ ∙ e)ᗮ |
      (y : E) + ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ s} :=
  ENNReal.toReal_pos (volume_hyperplaneSection_pos e he
    (hs.quantile_map_inner_cond_mem_image_interior he hs0 hsb.measure_lt_top.ne hτ)).ne'
    (hsb.volume_hyperplaneSection_lt_top e _).ne

/-- The volume of the hyperplane section of a bounded convex set of positive volume at its height
quantile is continuous on the levels in `Ioo 0 1`. -/
theorem _root_.Convex.continuousOn_volume_real_hyperplaneSection_quantile (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hs0 : volume s ≠ 0) (he : ‖e‖ = 1) :
    ContinuousOn (fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ |
      (y : E) + ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ s}) (Ioo 0 1) := by
  first
  | have hsi : volume s ≠ ∞ := hsb.measure_lt_top.ne
    refine (hs.continuousOn_volume_real_hyperplaneSection he
      fun t ↦ (hsb.volume_hyperplaneSection_lt_top e t).ne).comp
      (continuousOn_quantile _ (continuous_cdf_map_inner_cond he hs0 hsi)
        (hs.strictMonoOn_cdf_map_inner_cond he hs0 hsi)) fun τ hτ ↦ ?_
    exact interior_maximal (image_mono interior_subset) (isOpen_image_inner_interior he s)
      (hs.quantile_map_inner_cond_mem_image_interior he hs0 hsi hτ)

/-- **Derivative of the height quantile.** For a bounded Borel convex set `s` of positive volume
and a unit vector `e`, the quantile function `z` of the height law along `e` is differentiable at
every level `τ ∈ Ioo 0 1`, with derivative the volume of `s` divided by the volume of the
hyperplane section of `s` at height `z τ`. -/
theorem _root_.Convex.hasDerivAt_quantile_map_inner_cond (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hsm : MeasurableSet s) (hs0 : volume s ≠ 0) (he : ‖e‖ = 1)
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) :
    HasDerivAt ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile
      (volume.real s / volume.real {y : (ℝ ∙ e)ᗮ |
        (y : E) + ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ s}) τ := by
  first
  | set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
    have hsi : volume s ≠ ∞ := hsb.measure_lt_top.ne
    have hcont := continuous_cdf_map_inner_cond he hs0 hsi
    have hz := hs.quantile_map_inner_cond_mem_image_interior he hs0 hsi hτ
    -- The quantile lies at an interior height, where the volume below a hyperplane is
    -- differentiable with the section volume as derivative.
    have hzi : ν.quantile τ ∈ interior ((fun x ↦ ⟪e, x⟫) '' s) :=
      interior_maximal (image_mono interior_subset) (isOpen_image_inner_interior he s) hz
    have hcdf : HasDerivAt (cdf ν) (volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + ν.quantile τ • e ∈ s} /
        volume.real s) (ν.quantile τ) :=
      HasDerivAt.congr_of_eventuallyEq
        (HasDerivAt.div_const (hs.hasDerivAt_volume_real_sep_inner_le hsb hsm he hzi) _)
        (Eventually.of_forall fun c ↦ cdf_map_inner_cond hs0 hsi c)
    have hne : volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + ν.quantile τ • e ∈ s} / volume.real s ≠ 0 :=
      div_ne_zero (ENNReal.toReal_pos (volume_hyperplaneSection_pos e he hz).ne'
        (hsb.volume_hyperplaneSection_lt_top e _).ne).ne'
        (ENNReal.toReal_pos hs0 hsi).ne'
    have hloc : ∀ᶠ y in 𝓝 τ, cdf ν (ν.quantile y) = y := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with y hy using cdf_quantile ν hcont hy.1 hy.2
    simpa only [inv_div] using HasDerivAt.of_local_left_inverse
      ((continuousOn_quantile ν hcont (hs.strictMonoOn_cdf_map_inner_cond he hs0 hsi)).continuousAt
        (isOpen_Ioo.mem_nhds hτ)) hcdf hne hloc

/-- The quantile function of the height law of a bounded Borel set of positive volume is
integrable on the levels `Ioo 0 1`. -/
theorem integrableOn_quantile_map_inner_cond (e : E) (hsb : Bornology.IsBounded s)
    (hsm : MeasurableSet s) (hs0 : volume s ≠ 0) :
    IntegrableOn ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile (Ioo 0 1) := by
  first
  | set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
    have := cond_isProbabilityMeasure_of_finite hs0 hsb.measure_lt_top.ne
    have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
    obtain ⟨C, hC⟩ := hsb.exists_norm_le
    have hν : Integrable id ν :=
      (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).2
        ((integrable_cond_of_norm_le hsm aestronglyMeasurable_id hC).const_inner e)
    exact (integrableOn_quantile_iff ν).2 hν

/-- **The mean height.** The average over the levels `Ioo 0 1` of the quantile function of the
height `⟪e, x⟫` of a point `x` drawn uniformly from a bounded Borel set `s` of positive volume is
the height of the centroid `∫ x, x ∂(volume[|s])` of `s`. -/
theorem setIntegral_quantile_map_inner_cond (e : E) (hsb : Bornology.IsBounded s)
    (hsm : MeasurableSet s) (hs0 : volume s ≠ 0) :
    ∫ τ in Ioo 0 1, ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ =
      ⟪e, ∫ x, x ∂(volume[|s])⟫ := by
  first
  | set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
    have := cond_isProbabilityMeasure_of_finite hs0 hsb.measure_lt_top.ne
    have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
    obtain ⟨C, hC⟩ := hsb.exists_norm_le
    calc ∫ τ in Ioo 0 1, ν.quantile τ = ∫ y, y ∂ν := setIntegral_quantile_eq_integral ν
      _ = ∫ x, ⟪e, x⟫ ∂(volume[|s]) := integral_map hm.aemeasurable aestronglyMeasurable_id
      _ = ⟪e, ∫ x, x ∂(volume[|s])⟫ := integral_inner
            (integrable_cond_of_norm_le hsm aestronglyMeasurable_id hC) e

end TauCeti
end -- closes the original EOF section from source line 71
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Quantile.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/MeanInequalities.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Mean inequalities

This file collects classical inequalities complementing `Mathlib.Analysis.MeanInequalities`.

For nonnegative weights `w i` summing to `1`, the weighted geometric mean
`G(a) = ∏ i, a i ^ w i` of a nonnegative family is superadditive:

`G(a) + G(b) ≤ G(a + b)`.

Since `G` is also positively homogeneous, this says that the weighted geometric mean is concave on
the nonnegative orthant. Applied to the eigenvalues of a positive semidefinite matrix `M` with
equal weights, it gives `1 + det M ^ (1 / n) ≤ det (1 + M) ^ (1 / n)`, the core of Minkowski's
determinant inequality (`Matrix.PosSemidef.det_rpow_add_det_rpow_le`).

The proof divides by `a i + b i` and applies the inequality of arithmetic and geometric means
`Real.geom_mean_le_arith_mean_weighted` to the two normalized families, whose weighted means add
up to at most `1`.

Minkowski's inequality also holds for unconditional sums of `ℝ≥0∞`-valued families over an
arbitrary index type, with no summability hypotheses: infinite sums and infinite terms are allowed.
Mathlib states it for finite sums (`ENNReal.Lp_add_le`) and for summable `ℝ≥0`-valued families
(`NNReal.Lp_add_le_tsum`); the `ℝ≥0∞` form follows from the finite one by taking the supremum over
finite partial sums. It is the counting-measure case of `ENNReal.lintegral_Lp_add_le`, stated
without measure theory. It gives the triangle inequality for gauges defined as `ℓᵖ` sums in `ℝ≥0∞`,
such as the Hilbert–Schmidt energy of an operator. Hölder's inequality holds for such sums in the
same way, extending `ENNReal.inner_le_Lp_mul_Lq` and `NNReal.inner_le_Lp_mul_Lq_tsum`. The `ℓᵖ`
norm of such a family is antitone in the exponent, which gives the inclusions between Schatten
classes of operators.

Finally, the two-point weighted AM-GM inequality is restated after normalizing by positive scalars
`a` and `b`: `A ^ (1 - θ) * B ^ θ ≤ ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ)`,
strictly when `0 < θ < 1` and `A / a ≠ B / b`. This is the form used to compare volumes of
hyperplane sections in the Kneser–Süss equality argument for Brunn–Minkowski.

## Main statements

* `Real.prod_rpow_add_prod_rpow_le_prod_add_rpow`: the weighted geometric mean is superadditive.
* `Real.geom_mean_le_arith_mean2_weighted_div_mul`,
  `Real.geom_mean_lt_arith_mean2_weighted_div_mul`: two-point weighted AM-GM after normalizing
  by positive scalars, with the strict form.
* `ENNReal.Lp_add_le_tsum`: Minkowski's inequality for unconditional sums in `ℝ≥0∞`.
* `ENNReal.inner_le_Lp_mul_Lq_tsum`: Hölder's inequality for unconditional sums in `ℝ≥0∞`.
* `ENNReal.Lq_le_Lp_tsum`: the `ℓᵖ` norm of an `ℝ≥0∞`-valued family is antitone in `p`.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press
  1952, Chapter II.
-/

public section

namespace Real

/-- **Superadditivity of the weighted geometric mean.** For nonnegative weights `w i` summing to
`1` and nonnegative families `a` and `b`,
`∏ i ∈ s, a i ^ w i + ∏ i ∈ s, b i ^ w i ≤ ∏ i ∈ s, (a i + b i) ^ w i`. -/
theorem prod_rpow_add_prod_rpow_le_prod_add_rpow {ι : Type*} (s : Finset ι) {w a b : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∏ i ∈ s, a i ^ w i + ∏ i ∈ s, b i ^ w i ≤ ∏ i ∈ s, (a i + b i) ^ w i := by
  first
  | have hc (i) (hi : i ∈ s) : 0 ≤ a i + b i := add_nonneg (ha i hi) (hb i hi)
    -- Factor `a i = (a i / (a i + b i)) * (a i + b i)`, and likewise for `b`; this holds even when
    -- `a i + b i = 0`, since then `a i = b i = 0`.
    have hfactor {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hfc : ∀ i ∈ s, f i ≤ a i + b i) :
        ∏ i ∈ s, f i ^ w i =
          (∏ i ∈ s, (f i / (a i + b i)) ^ w i) * ∏ i ∈ s, (a i + b i) ^ w i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [← mul_rpow (div_nonneg (hf i hi) (hc i hi)) (hc i hi),
        div_mul_cancel_of_imp fun h => le_antisymm (h ▸ hfc i hi) (hf i hi)]
    rw [hfactor ha fun i hi => le_add_of_nonneg_right (hb i hi),
      hfactor hb fun i hi => le_add_of_nonneg_left (ha i hi), ← add_mul]
    refine mul_le_of_le_one_left (Finset.prod_nonneg fun i hi => rpow_nonneg (hc i hi) _) ?_
    -- The two normalized families have weighted arithmetic means adding up to at most `1`.
    calc ∏ i ∈ s, (a i / (a i + b i)) ^ w i + ∏ i ∈ s, (b i / (a i + b i)) ^ w i
        ≤ ∑ i ∈ s, w i * (a i / (a i + b i)) + ∑ i ∈ s, w i * (b i / (a i + b i)) :=
          add_le_add
            (geom_mean_le_arith_mean_weighted s w _ hw hw' fun i hi => div_nonneg (ha i hi) (hc i hi))
            (geom_mean_le_arith_mean_weighted s w _ hw hw' fun i hi => div_nonneg (hb i hi) (hc i hi))
      _ = ∑ i ∈ s, w i * ((a i + b i) / (a i + b i)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [add_div, mul_add]
      _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum fun i hi =>
          mul_le_of_le_one_right (hw i hi) (div_self_le_one _)
      _ = 1 := hw'

/-- Splitting a weighted geometric mean through positive normalizers `a` and `b`:
`A ^ (1 - θ) * B ^ θ = (A / a) ^ (1 - θ) * (B / b) ^ θ * (a ^ (1 - θ) * b ^ θ)`. -/
theorem rpow_one_sub_mul_rpow_eq_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a)
    (hb : 0 < b) :
    A ^ (1 - θ) * B ^ θ = (A / a) ^ (1 - θ) * (B / b) ^ θ * (a ^ (1 - θ) * b ^ θ) := by
  first
  | rw [mul_mul_mul_comm, ← mul_rpow (div_nonneg hA ha.le) ha.le,
      ← mul_rpow (div_nonneg hB hb.le) hb.le, div_mul_cancel₀ A ha.ne', div_mul_cancel₀ B hb.ne']

/-- **Normalized weighted AM-GM.** For positive normalizers `a` and `b`, the weighted geometric
mean of `A` and `B` is at most the weighted arithmetic mean of `A / a` and `B / b` times the
weighted geometric mean of `a` and `b`. -/
theorem geom_mean_le_arith_mean2_weighted_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    A ^ (1 - θ) * B ^ θ ≤ ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ) := by
  first
  | rw [rpow_one_sub_mul_rpow_eq_div_mul hA hB ha hb]
    exact mul_le_mul_of_nonneg_right (geom_mean_le_arith_mean2_weighted (by linarith) hθ₀
      (div_nonneg hA ha.le) (div_nonneg hB hb.le) (by ring))
      (mul_nonneg (rpow_nonneg ha.le _) (rpow_nonneg hb.le _))

/-- The strict form of `Real.geom_mean_le_arith_mean2_weighted_div_mul` for `0 < θ < 1` and
`A / a ≠ B / b`. -/
theorem geom_mean_lt_arith_mean2_weighted_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hne : A / a ≠ B / b) :
    A ^ (1 - θ) * B ^ θ < ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ) := by
  first
  | rw [rpow_one_sub_mul_rpow_eq_div_mul hA hB ha hb]
    exact mul_lt_mul_of_pos_right ((geom_mean_lt_arith_mean2_weighted_iff_of_pos
      (by linarith) hθ₀ (div_nonneg hA ha.le) (div_nonneg hB hb.le) (by ring)).2 hne)
      (mul_pos (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _))

end Real

namespace ENNReal

open scoped ENNReal

/-- **Minkowski's inequality** for unconditional sums in `ℝ≥0∞`: for `1 ≤ p`,
`(∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)`.
No summability hypotheses are needed; both sides may be infinite. -/
theorem Lp_add_le_tsum {ι : Type*} (f g : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  first
  | have hp0 : 0 < p := zero_lt_one.trans_le hp
    -- Bound each finite partial sum by the finite Minkowski inequality.
    rw [one_div, rpow_inv_le_iff hp0, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s ↦ ?_
    rw [← rpow_inv_le_iff hp0, ← one_div]
    grw [Lp_add_le s f g hp, ENNReal.sum_le_tsum s, ENNReal.sum_le_tsum (f := fun i ↦ g i ^ p) s]

/-- **Hölder's inequality** for unconditional sums in `ℝ≥0∞`: for conjugate exponents `p` and `q`,
`∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q)`.
No summability hypotheses are needed; both sides may be infinite. -/
theorem inner_le_Lp_mul_Lq_tsum {ι : Type*} (f g : ι → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  first
    -- Bound each finite partial sum by the finite Hölder inequality.
  | rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s ↦ (inner_le_Lp_mul_Lq s f g hpq).trans ?_
    gcongr
    · exact one_div_nonneg.2 hpq.nonneg
    · exact ENNReal.sum_le_tsum s
    · exact one_div_nonneg.2 hpq.symm.nonneg
    · exact ENNReal.sum_le_tsum s

/-- The `ℓᵖ` norms of an `ℝ≥0∞`-valued family decrease as the exponent grows: for `0 < p ≤ q`,
`(∑' i, f i ^ q) ^ (1 / q) ≤ (∑' i, f i ^ p) ^ (1 / p)`. No summability hypotheses are needed;
both sides may be infinite. This is the unconditional-sum form of `ENNReal.rpow_add_rpow_le`. -/
theorem Lq_le_Lp_tsum {ι : Type*} (f : ι → ℝ≥0∞) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑' i, f i ^ q) ^ (1 / q) ≤ (∑' i, f i ^ p) ^ (1 / p) := by
  first
  | set S := (∑' i, f i ^ p) ^ (1 / p) with hS
    have hpq' : 0 ≤ q - p := sub_nonneg.2 hpq
    -- Each term is at most the `ℓᵖ` norm `S`, so `f i ^ q ≤ f i ^ p * S ^ (q - p)`.
    have hfS (i : ι) : f i ≤ S := by
      rw [hS, one_div, le_rpow_inv_iff hp]
      exact ENNReal.le_tsum (f := fun i ↦ f i ^ p) i
    have hSp : S ^ p = ∑' i, f i ^ p := by rw [hS, one_div, rpow_inv_rpow hp.ne']
    rw [one_div, rpow_inv_le_iff (hp.trans_le hpq)]
    calc ∑' i, f i ^ q = ∑' i, f i ^ p * f i ^ (q - p) := by
          simp_rw [← rpow_add_of_nonneg _ _ hp.le hpq', add_sub_cancel]
      _ ≤ ∑' i, f i ^ p * S ^ (q - p) := by gcongr with i; exact hfS i
      _ = S ^ q := by
          rw [ENNReal.tsum_mul_right, ← hSp, ← rpow_add_of_nonneg _ _ hp.le hpq', add_sub_cancel]

end ENNReal
end -- closes the original EOF section from source line 61
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/MeanInequalities.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Equality.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: weighted AM-GM with its equality case, the one-dimensional change of variables,
-- and functions with equal derivatives on an interval.

/-!
# Equality in Brunn–Minkowski for convex sets: matching height quantiles

Let `K` and `L` be bounded Borel convex sets of positive volume in a finite-dimensional Euclidean
space, let `0 < θ < 1`, and let `e` be a unit vector. Write `z_K` and `z_L` for the quantile
functions of the height `⟪e, x⟫` of a point drawn uniformly from `K` and from `L`. This file shows
that if the multiplicative Brunn–Minkowski inequality
`volume K ^ (1 - θ) * volume L ^ θ ≤ volume ((1 - θ) • K + θ • L)` is an equality, then
`z_L - z_K` is constant on the levels `Ioo 0 1`. In other words, along each direction the heights
at which `K` and `L` cut off equal volume fractions differ by a constant, which may depend on the
direction.

This is the analytic core of the Kneser–Süss proof that equality in Brunn–Minkowski forces a
homothety. Put `z = (1 - θ) z_K + θ z_L`. The weighted sum of the hyperplane sections of `K` at
height `z_K τ` and of `L` at height `z_L τ` lies in the section of `(1 - θ) • K + θ • L` at height
`z τ`, so Brunn–Minkowski in the hyperplane bounds the section of the sum from below. The change
of variables `ζ = z τ` then gives
`volume ((1 - θ) • K + θ • L) ≥ ∫ τ in Ioo 0 1, z' τ * volume (section at z τ)`,
and by the derivative of the height quantile and weighted AM-GM the integrand is at least
`volume K ^ (1 - θ) * volume L ^ θ`. It is strictly larger wherever
`volume K / volume (K_{z_K τ}) ≠ volume L / volume (L_{z_L τ})`. These two ratios are `z_K'` and
`z_L'`, so under equality they agree on all of `Ioo 0 1` by continuity, and `z_L - z_K` is constant.

The estimate on sections is
`TauCeti.volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le`.

## Main results

* `Convex.exists_quantile_map_inner_cond_eq_add_of_volume_le`: under equality in the
  multiplicative Brunn–Minkowski inequality, the height quantiles of `K` and `L` along any unit
  vector differ by a constant on `Ioo 0 1`.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Theorem 7.1.1 and its proof.
-/

public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {e : E} {K L : Set E}

/-- **The Kneser–Süss integral inequality.** Along the weighted height quantile
`z = (1 - θ) z_K + θ z_L`, the derivative `z'` times the weighted geometric mean of the section
volumes of `K` at `z_K τ` and of `L` at `z_L τ`, integrated over `Ioo 0 1`, is at most the volume of
`(1 - θ) • K + θ • L`. -/
private theorem setLIntegral_ofReal_le_volume_smul_add_smul (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∫⁻ τ in Ioo 0 1, ENNReal.ofReal
      (((1 - θ) * (volume.real K / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K}) +
        θ * (volume.real L / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L})) *
      (volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K} ^ (1 - θ) *
        volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L} ^ θ)) ≤
      volume ((1 - θ) • K + θ • L) := by
  first
  | set zK := ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile
    set zL := ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile
    set a : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zK τ • e ∈ K}
    set b : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zL τ • e ∈ L}
    set M := (1 - θ) • K + θ • L
    have ha (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < a τ :=
      hK.volume_real_hyperplaneSection_quantile_pos hKb hK0 he hτ
    have hb (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < b τ :=
      hL.volume_real_hyperplaneSection_quantile_pos hLb hL0 he hτ
    -- The weighted quantile `z` is strictly increasing with positive derivative `z'`.
    set z : ℝ → ℝ := fun τ ↦ (1 - θ) * zK τ + θ * zL τ
    set z' : ℝ → ℝ := fun τ ↦ (1 - θ) * (volume.real K / a τ) + θ * (volume.real L / b τ)
    have hz' (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : HasDerivAt z (z' τ) τ :=
      ((hK.hasDerivAt_quantile_map_inner_cond hKb hKm hK0 he hτ).const_mul (1 - θ)).add
        ((hL.hasDerivAt_quantile_map_inner_cond hLb hLm hL0 he hτ).const_mul θ)
    have hzpos (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < z' τ := by
      have hKr : 0 < volume.real K := ENNReal.toReal_pos hK0 hKb.measure_lt_top.ne
      have hLr : 0 < volume.real L := ENNReal.toReal_pos hL0 hLb.measure_lt_top.ne
      exact add_pos (mul_pos (by linarith) (div_pos hKr (ha τ hτ)))
        (mul_pos hθ₀ (div_pos hLr (hb τ hτ)))
    have hzmono : StrictMonoOn z (Ioo 0 1) := by
      intro s hs t ht hst
      have hK' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hK0
        hKb.measure_lt_top.ne) hs ht hst
      have hL' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hL0
        hLb.measure_lt_top.ne) hs ht hst
      simp only [z]
      nlinarith
    -- Pointwise, the integrand is bounded by the change-of-variables integrand along `z`, by
    -- Brunn–Minkowski in the hyperplane.
    have hpt (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : ENNReal.ofReal (z' τ * (a τ ^ (1 - θ) * b τ ^ θ)) ≤
        ENNReal.ofReal |z' τ| * volume {y : (ℝ ∙ e)ᗮ | (y : E) + z τ • e ∈ M} := by
      rw [abs_of_pos (hzpos τ hτ), ENNReal.ofReal_mul (hzpos τ hτ).le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (ha τ hτ).le _),
        ← ENNReal.ofReal_rpow_of_nonneg (ha τ hτ).le (by linarith),
        ← ENNReal.ofReal_rpow_of_nonneg (hb τ hτ).le hθ₀.le, ofReal_measureReal
          (hKb.volume_hyperplaneSection_lt_top e _).ne, ofReal_measureReal
          (hLb.volume_hyperplaneSection_lt_top e _).ne]
      exact mul_le_mul_right
        (volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le e hKm hLm hθ₀ hθ₁ _ _) _
    -- Change variables along `z`, then apply Cavalieri's formula to the convex set `M`.
    refine (setLIntegral_mono' measurableSet_Ioo hpt).trans ?_
    rw [← lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun τ hτ ↦ (hz' τ hτ).hasDerivWithinAt) hzmono.injOn
      (fun ζ ↦ volume {y : (ℝ ∙ e)ᗮ | (y : E) + ζ • e ∈ M})]
    refine (setLIntegral_le_lintegral _ _).trans_eq ?_
    rw [← volume_eq_lintegral_volume_hyperplaneSection e he
      (((hK.smul _).add (hL.smul _)).nullMeasurableSet (μ := volume))]

/-- Under equality in multiplicative Brunn–Minkowski, the derivatives of the two height quantiles,
`volume K / volume (K_{z_K τ})` and `volume L / volume (L_{z_L τ})`, agree at every level. -/
private theorem div_volume_real_hyperplaneSection_quantile_eq (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) {τ : ℝ}
    (hτ : τ ∈ Ioo 0 1) :
    volume.real K / volume.real {y : (ℝ ∙ e)ᗮ |
        (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K} =
      volume.real L / volume.real {y : (ℝ ∙ e)ᗮ |
        (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L} := by
  first
  | have hint := setLIntegral_ofReal_le_volume_smul_add_smul hK hKb hKm hK0 hL hLb hLm hL0 he
      hθ₀ hθ₁
    set a : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ |
      (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K}
    set b : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ |
      (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L}
    set c := volume.real K ^ (1 - θ) * volume.real L ^ θ
    set g : ℝ → ℝ := fun τ ↦ ((1 - θ) * (volume.real K / a τ) + θ * (volume.real L / b τ)) *
      (a τ ^ (1 - θ) * b τ ^ θ)
    have ha (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < a τ :=
      hK.volume_real_hyperplaneSection_quantile_pos hKb hK0 he hτ
    have hb (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < b τ :=
      hL.volume_real_hyperplaneSection_quantile_pos hLb hL0 he hτ
    -- By weighted AM-GM, `g` is at least the weighted geometric mean `c` of the volumes.
    have hcg (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : c ≤ g τ :=
      Real.geom_mean_le_arith_mean2_weighted_div_mul measureReal_nonneg measureReal_nonneg (ha τ hτ)
        (hb τ hτ) hθ₀.le hθ₁.le
    have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg measureReal_nonneg _)
      (Real.rpow_nonneg measureReal_nonneg _)
    have hvol' : volume ((1 - θ) • K + θ • L) ≤ ENNReal.ofReal c := by
      refine hvol.trans_eq ?_
      rw [← ofReal_measureReal hKb.measure_lt_top.ne, ← ofReal_measureReal hLb.measure_lt_top.ne,
        ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by linarith),
        ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg hθ₀.le, ← ENNReal.ofReal_mul
          (Real.rpow_nonneg measureReal_nonneg _)]
    have hgc : ContinuousOn g (Ioo 0 1) := by
      have hac := hK.continuousOn_volume_real_hyperplaneSection_quantile hKb hK0 he
      have hbc := hL.continuousOn_volume_real_hyperplaneSection_quantile hLb hL0 he
      refine (((continuousOn_const.div hac fun τ hτ ↦ (ha τ hτ).ne').const_smul (1 - θ)).add
        ((continuousOn_const.div hbc fun τ hτ ↦ (hb τ hτ).ne').const_smul θ)).mul
        ((hac.rpow_const fun τ hτ ↦ Or.inl (ha τ hτ).ne').mul
          (hbc.rpow_const fun τ hτ ↦ Or.inl (hb τ hτ).ne'))
    -- The integral of `g ≥ c` over `Ioo 0 1` is at most `c`, so the continuous `g` equals `c`.
    have hae : g =ᵐ[volume.restrict (Ioo 0 1)] fun _ ↦ c := by
      have hle : ∫⁻ τ in Ioo 0 1, ENNReal.ofReal (g τ) ≤
          ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal c := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
        exact hint.trans hvol'
      have h := ae_eq_of_ae_le_of_lintegral_le
        ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun τ hτ ↦
          ENNReal.ofReal_le_ofReal (hcg τ hτ)))
        (by simp) (ENNReal.measurable_ofReal.comp_aemeasurable
          (hgc.aemeasurable measurableSet_Ioo)) hle
      filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with τ hτ hτI
      exact ((ENNReal.ofReal_eq_ofReal_iff hc (hc.trans (hcg τ hτI))).1 hτ).symm
    have hgτ : g τ = c := eqOn_open_of_ae_eq hae isOpen_Ioo hgc continuousOn_const hτ
    -- Equality in weighted AM-GM forces the two ratios to agree.
    by_contra hne
    exact (Real.geom_mean_lt_arith_mean2_weighted_div_mul measureReal_nonneg measureReal_nonneg
      (ha τ hτ) (hb τ hτ) hθ₀ hθ₁ hne).ne' hgτ

/-- **Matching height quantiles under Brunn–Minkowski equality.** Let `K` and `L` be bounded Borel
convex sets of positive volume, `0 < θ < 1`, and `e` a unit vector. If the volume of
`(1 - θ) • K + θ • L` is at most `volume K ^ (1 - θ) * volume L ^ θ`, that is, if the multiplicative
Brunn–Minkowski inequality is an equality, then the quantile functions
of the height `⟪e, x⟫` of a point drawn uniformly from `L` and from `K` differ by a constant on
the levels `Ioo 0 1`. -/
theorem _root_.Convex.exists_quantile_map_inner_cond_eq_add_of_volume_le (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) :
    ∃ c, EqOn ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile
      (((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile · + c) (Ioo 0 1) := by
  first
  | have hKd (τ : ℝ) (hτ : τ ∈ Ioo 0 1) := hK.hasDerivAt_quantile_map_inner_cond hKb hKm hK0 he hτ
    have hLd (τ : ℝ) (hτ : τ ∈ Ioo 0 1) := hL.hasDerivAt_quantile_map_inner_cond hLb hLm hL0 he hτ
    exact isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
      (fun τ hτ ↦ (hLd τ hτ).differentiableAt.differentiableWithinAt)
      (fun τ hτ ↦ (hKd τ hτ).differentiableAt.differentiableWithinAt)
      fun τ hτ ↦ by
        rw [(hLd τ hτ).deriv, (hKd τ hτ).deriv]
        exact (div_volume_real_hyperplaneSection_quantile_eq hK hKb hKm hK0 hL hLb hLm hL0 he
          hθ₀ hθ₁ hvol hτ).symm

end TauCeti
end -- closes the original EOF section from source line 55
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Equality.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Convex/Separation.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: strict separation of a point from an open convex set, and the Riesz representation.

/-!
# Separation of points from open convex sets by heights

In a real Hilbert space, a point outside a nonempty open convex set `W` is strictly separated from
`W` by a continuous linear functional (`geometric_hahn_banach_open_point`). By the Riesz
representation, such a functional is a positive multiple of the height `x ↦ ⟪u, x⟫` along a unit
vector `u`. Hence a set whose heights along every unit vector are heights of points of `W` is
contained in `W`.

## Main results

* `Convex.subset_of_image_inner_subset`: a set whose heights along every unit vector are heights
  of points of a nonempty open convex set `W` is contained in `W`.
-/

public section

open Set
open scoped RealInnerProductSpace

/-- **Containment in an open convex set from directional images.** If the heights `⟪u, x⟫` of the
points of `U` along every unit vector `u` are heights of points of a nonempty open convex set `W`,
then `U ⊆ W`: a point outside `W` is strictly separated from it by a continuous linear functional,
which is a positive multiple of the height along a unit vector. -/
theorem Convex.subset_of_image_inner_subset {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {U W : Set E} (hW : Convex ℝ W) (hWo : IsOpen W)
    (hWn : W.Nonempty)
    (hUW : ∀ u : E, ‖u‖ = 1 → (fun x ↦ ⟪u, x⟫) '' U ⊆ (fun x ↦ ⟪u, x⟫) '' W) : U ⊆ W := by
  first
  | intro x hx
    by_contra hxW
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hW hWo hxW
    set w := (InnerProductSpace.toDual ℝ E).symm f
    have hfw (y : E) : f y = ⟪w, y⟫ := InnerProductSpace.toDual_symm_apply.symm
    have hw : w ≠ 0 := by
      rintro hw
      obtain ⟨a, ha⟩ := hWn
      simpa [hfw, hw] using hf a ha
    obtain ⟨a, ha, hax⟩ : ⟪‖w‖⁻¹ • w, x⟫ ∈ (fun y ↦ ⟪‖w‖⁻¹ • w, y⟫) '' W :=
      hUW _ (norm_smul_inv_norm (𝕜 := ℝ) hw) (mem_image_of_mem _ hx)
    simp only [real_inner_smul_left] at hax
    have := hf a ha
    rw [hfw, hfw, ← mul_left_cancel₀ (inv_ne_zero (norm_ne_zero_iff.2 hw)) hax] at this
    exact lt_irrefl _ this
end -- closes the original EOF section from source line 29
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Convex/Separation.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Homothety.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: a convex set has positive volume exactly when its interior is nonempty, and
-- containment in an open convex set from directional images.

/-!
# Equality in Brunn–Minkowski for convex bodies: homothety

Let `K` and `L` be compact convex sets of positive volume in a finite-dimensional Euclidean space
and let `0 < θ < 1`. The multiplicative Brunn–Minkowski inequality
`volume K ^ (1 - θ) * volume L ^ θ ≤ volume ((1 - θ) • K + θ • L)` is an equality exactly when `L`
is a translate of `K`. For `c, d > 0` and `n = finrank ℝ E ≥ 1`, the additive inequality
`c * volume A ^ (1 / n) + d * volume B ^ (1 / n) ≤ volume (c • A + d • B) ^ (1 / n)` is an
equality exactly when `B = v +ᵥ r • A` for a vector `v` and a scalar `r > 0`. Taking `c = 1 - θ`
and `d = θ` gives the weighted form, and `c = d = 1` the unweighted form.

The proof completes the argument of Kneser and Süss. Under multiplicative equality, the height
quantiles of `K` and `L` along each unit vector `u` differ by a constant
(`Convex.exists_quantile_map_inner_cond_eq_add_of_volume_le`). Averaging over the levels identifies
this constant as `⟪u, v⟫`, where `v` is the difference of the centroids of `L` and `K`
(`TauCeti.setIntegral_quantile_map_inner_cond`). Since the quantiles sweep out the heights of
interior points, `interior L` and `v +ᵥ interior K` have the same heights along every unit
vector, so by separation of points from open convex sets they coincide
(`Convex.subset_of_image_inner_subset`). Passing to closures gives
`L = v +ᵥ K`. The additive equality case reduces to the multiplicative one by rescaling `A` and `B`
to unit volume.

The hypothesis of positive volume is equivalent to nonempty interior
(`Convex.addHaar_pos_iff_interior_nonempty`).

## Main results

* `Convex.exists_interior_eq_vadd_interior_of_volume_le`: for bounded convex sets of positive
  volume, multiplicative equality forces the interiors to be translates.
* `Convex.volume_smul_add_smul_eq_iff`: for compact convex sets of positive volume, multiplicative
  equality holds exactly for translates.
* `Convex.volume_real_smul_add_smul_rpow_eq_iff`: for compact convex sets of positive volume,
  additive equality holds exactly for homothetic sets.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Theorem 7.1.1 and its proof.
-/

public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {K L : Set E}

/-- **Translated interiors under Brunn–Minkowski equality.** Let `K` and `L` be bounded convex sets
of positive volume and `0 < θ < 1`. If the volume of `(1 - θ) • K + θ • L` is at most
`volume K ^ (1 - θ) * volume L ^ θ`, that is, if the multiplicative Brunn–Minkowski inequality is
an equality, then the interior of `L` is a translate of the interior of `K`. -/
theorem _root_.Convex.exists_interior_eq_vadd_interior_of_volume_le (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0) (hL : Convex ℝ L)
    (hLb : Bornology.IsBounded L) (hL0 : volume L ≠ 0) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) :
    ∃ v : E, interior L = v +ᵥ interior K := by
  first
    -- The interiors are open, hence measurable, and have the same volumes, since the frontier of a
    -- convex set is null; so it suffices to treat measurable `K` and `L`.
  | wlog hm : MeasurableSet K ∧ MeasurableSet L generalizing K L
    · have hKi : volume (interior K) = volume K :=
        measure_interior_of_null_frontier (hK.addHaar_frontier volume)
      have hLi : volume (interior L) = volume L :=
        measure_interior_of_null_frontier (hL.addHaar_frontier volume)
      obtain ⟨v, hv⟩ := this hK.interior (hKb.subset interior_subset) (hKi ▸ hK0) hL.interior
        (hLb.subset interior_subset) (hLi ▸ hL0) (by
          rw [hKi, hLi]
          exact (measure_mono (add_subset_add (smul_set_mono interior_subset)
            (smul_set_mono interior_subset))).trans hvol)
        ⟨isOpen_interior.measurableSet, isOpen_interior.measurableSet⟩
      exact ⟨v, by simpa only [interior_interior] using hv⟩
    obtain ⟨hKm, hLm⟩ := hm
    set v := ∫ x, x ∂(volume[|L]) - ∫ x, x ∂(volume[|K])
    have hKi := (hK.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hK0)
    have hLi := (hL.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hL0)
    -- Along every unit vector, the heights of the interior points of `L` and of `v +ᵥ interior K`
    -- agree: the height quantiles differ by a constant, which is the difference of the means.
    have himage (u : E) (hu : ‖u‖ = 1) :
        (fun x ↦ ⟪u, x⟫) '' interior L = (fun x ↦ ⟪u, x⟫) '' (v +ᵥ interior K) := by
      obtain ⟨c, hc⟩ := hK.exists_quantile_map_inner_cond_eq_add_of_volume_le hKb hKm hK0 hL hLb
        hLm hL0 hu hθ₀ hθ₁ hvol
      have hcv : c = ⟪u, v⟫ := by
        have h := setIntegral_congr_fun (μ := volume) measurableSet_Ioo hc
        rw [integral_add (integrableOn_quantile_map_inner_cond u hKb hKm hK0)
          (integrable_const c), setIntegral_const, setIntegral_quantile_map_inner_cond u hLb hLm hL0,
          setIntegral_quantile_map_inner_cond u hKb hKm hK0] at h
        simp only [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
          ENNReal.toReal_one, one_smul] at h
        rw [inner_sub_right]
        linarith
      rw [← hL.image_quantile_map_inner_cond_Ioo hu hL0 hLb.measure_lt_top.ne, hc.image_eq,
        ← image_image (· + c), hK.image_quantile_map_inner_cond_Ioo hu hK0 hKb.measure_lt_top.ne,
        ← image_vadd, image_image, image_image]
      simp only [vadd_eq_add, inner_add_right, hcv, add_comm]
    exact ⟨v, Subset.antisymm ((hK.interior.vadd v).subset_of_image_inner_subset
      (isOpen_interior.vadd v) hKi.vadd_set fun u hu ↦ (himage u hu).le)
      (hL.interior.subset_of_image_inner_subset isOpen_interior hLi fun u hu ↦ (himage u hu).ge)⟩

/-- **Brunn–Minkowski equality for convex bodies, multiplicative form.** Let `K` and `L` be compact
convex sets of positive volume and `0 < θ < 1`. If the multiplicative Brunn–Minkowski inequality
`volume K ^ (1 - θ) * volume L ^ θ ≤ volume ((1 - θ) • K + θ • L)` is an equality, then `L` is a
translate of `K`. -/
theorem _root_.Convex.exists_eq_vadd_of_volume_le (hK : Convex ℝ K) (hKc : IsCompact K)
    (hK0 : volume K ≠ 0) (hL : Convex ℝ L) (hLc : IsCompact L) (hL0 : volume L ≠ 0) {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) :
    ∃ v : E, L = v +ᵥ K := by
  first
  | obtain ⟨v, hv⟩ := hK.exists_interior_eq_vadd_interior_of_volume_le hKc.isBounded hK0 hL
      hLc.isBounded hL0 hθ₀ hθ₁ hvol
    have hKi := (hK.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hK0)
    have hLi := (hL.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hL0)
    refine ⟨v, ?_⟩
    rw [← hLc.isClosed.closure_eq, ← hL.closure_interior_eq_closure_of_nonempty_interior hLi, hv,
      closure_vadd, hK.closure_interior_eq_closure_of_nonempty_interior hKi,
      hKc.isClosed.closure_eq]

/-- **Equality cases of multiplicative Brunn–Minkowski for convex bodies.** Let `K` and `L` be
compact convex sets of positive volume and `0 < θ < 1`. Then
`volume ((1 - θ) • K + θ • L) = volume K ^ (1 - θ) * volume L ^ θ` exactly when `L` is a translate
of `K`. -/
theorem _root_.Convex.volume_smul_add_smul_eq_iff (hK : Convex ℝ K) (hKc : IsCompact K)
    (hK0 : volume K ≠ 0) (hL : Convex ℝ L) (hLc : IsCompact L) (hL0 : volume L ≠ 0) {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    volume ((1 - θ) • K + θ • L) = volume K ^ (1 - θ) * volume L ^ θ ↔ ∃ v : E, L = v +ᵥ K := by
  first
  | refine ⟨fun h ↦ hK.exists_eq_vadd_of_volume_le hKc hK0 hL hLc hL0 hθ₀ hθ₁ h.le, ?_⟩
    rintro ⟨v, rfl⟩
    have hθK : θ • (v +ᵥ K) = θ • v +ᵥ θ • K := by
      simp only [← image_smul, ← image_vadd, image_image, vadd_eq_add, smul_add]
    rw [hθK, add_vadd_comm, ← hK.add_smul (by linarith) hθ₀.le, sub_add_cancel, one_smul,
      measure_vadd, measure_vadd, ← ENNReal.rpow_add _ _ hK0 hKc.measure_lt_top.ne, sub_add_cancel,
      ENNReal.rpow_one]

/-- **Brunn–Minkowski equality for convex bodies, additive form.** Let `A` and `B` be compact convex
sets of positive volume in a space of dimension `n`, and let `c, d > 0`. If the reverse bound
`volume (c • A + d • B) ^ (1 / n) ≤ c * volume A ^ (1 / n) + d * volume B ^ (1 / n)` holds,
then `B` is homothetic to `A`: `B = v +ᵥ r • A` for some vector `v` and some `r > 0`.
In positive dimension, the bound gives equality in the Brunn–Minkowski inequality;
in dimension zero, homothety follows from nonempty `A` and `B` alone. -/
theorem _root_.Convex.exists_eq_vadd_smul_of_volume_real_rpow_le {A B : Set E} (hA : Convex ℝ A)
    (hAc : IsCompact A) (hA0 : volume A ≠ 0) (hB : Convex ℝ B) (hBc : IsCompact B)
    (hB0 : volume B ≠ 0) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (h : volume.real (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
      c * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
        d * volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹)) :
    ∃ v : E, ∃ r : ℝ, 0 < r ∧ B = v +ᵥ r • A := by
  first
    -- In dimension zero the space is a point, and both sets, being nonempty, are all of it.
  | by_cases hn : Module.finrank ℝ E = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp hn
      refine ⟨0, 1, one_pos, ?_⟩
      rw [(nonempty_of_measure_ne_zero hA0).eq_univ, (nonempty_of_measure_ne_zero hB0).eq_univ,
        one_smul, zero_vadd]
    set n := Module.finrank ℝ E
    have hVA : 0 < volume.real A := ENNReal.toReal_pos hA0 hAc.measure_lt_top.ne
    have hVB : 0 < volume.real B := ENNReal.toReal_pos hB0 hBc.measure_lt_top.ne
    set a := volume.real A ^ (n : ℝ)⁻¹
    set b := volume.real B ^ (n : ℝ)⁻¹
    have ha : 0 < a := Real.rpow_pos_of_pos hVA _
    have hb : 0 < b := Real.rpow_pos_of_pos hVB _
    set S := c * a + d * b
    have hS : 0 < S := by positivity
    set θ := d * b / S with hθ
    have hθ₀ : 0 < θ := by positivity
    have hθ₁ : θ < 1 := (div_lt_one hS).2 (lt_add_of_pos_left _ (mul_pos hc ha))
    have h1θ : 1 - θ = c * a / S := by
      rw [eq_div_iff hS.ne', sub_mul, one_mul, div_mul_cancel₀ _ hS.ne']
      ring
    -- Rescale `A` and `B` to unit volume.
    have hunit {s : Set E} (hsc : IsCompact s) (hVs : 0 < volume.real s) :
        volume ((volume.real s ^ (n : ℝ)⁻¹)⁻¹ • s) = 1 := by
      rw [addHaar_smul_of_nonneg _ (inv_nonneg.2 (Real.rpow_nonneg hVs.le _)),
        ← ofReal_measureReal hsc.measure_lt_top.ne, ← ENNReal.ofReal_mul (by positivity), inv_pow,
        Real.rpow_inv_natCast_pow hVs.le hn, inv_mul_cancel₀ hVs.ne', ENNReal.ofReal_one]
    have hA1 : volume (a⁻¹ • A) = 1 := hunit hAc hVA
    have hB1 : volume (b⁻¹ • B) = 1 := hunit hBc hVB
    have hset : (1 - θ) • a⁻¹ • A + θ • b⁻¹ • B = S⁻¹ • (c • A + d • B) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, h1θ]
      congr 2
      · field_simp
      · rw [hθ]
        field_simp
    have hM : volume ((1 - θ) • a⁻¹ • A + θ • b⁻¹ • B) ≤
        volume (a⁻¹ • A) ^ (1 - θ) * volume (b⁻¹ • B) ^ θ := by
      have hMc : IsCompact (c • A + d • B) := (hAc.smul c).add (hBc.smul d)
      have hle : volume.real (c • A + d • B) ≤ S ^ n := by
        calc volume.real (c • A + d • B) = (volume.real (c • A + d • B) ^ (n : ℝ)⁻¹) ^ n :=
              (Real.rpow_inv_natCast_pow measureReal_nonneg hn).symm
          _ ≤ S ^ n := pow_le_pow_left₀ (Real.rpow_nonneg measureReal_nonneg _) h n
      rw [hA1, hB1, ENNReal.one_rpow, ENNReal.one_rpow, one_mul, hset,
        addHaar_smul_of_nonneg _ (inv_nonneg.2 hS.le), ← ofReal_measureReal hMc.measure_lt_top.ne,
        ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one, inv_pow,
        inv_mul_le_iff₀ (by positivity), mul_one]
      exact hle
    obtain ⟨v, hv⟩ := (hA.smul a⁻¹).exists_eq_vadd_of_volume_le (hAc.smul a⁻¹) (hA1 ▸ one_ne_zero)
      (hB.smul b⁻¹) (hBc.smul b⁻¹) (hB1 ▸ one_ne_zero) hθ₀ hθ₁ hM
    refine ⟨b • v, b / a, div_pos hb ha, ?_⟩
    rw [← smul_inv_smul₀ hb.ne' B, hv]
    simp only [← image_smul, ← image_vadd, image_image, vadd_eq_add, smul_add, smul_smul,
      div_eq_mul_inv]

/-- **Equality cases of Brunn–Minkowski for convex bodies.** Let `A` and `B` be compact convex sets
of positive volume in a space of positive dimension `n`, and let `c, d > 0`. Then
`volume (c • A + d • B) ^ (1 / n) = c * volume A ^ (1 / n) + d * volume B ^ (1 / n)` exactly when
`B` is homothetic to `A`, that is, `B = v +ᵥ r • A` for some vector `v` and some `r > 0`. -/
theorem _root_.Convex.volume_real_smul_add_smul_rpow_eq_iff
    (hn : Module.finrank ℝ E ≠ 0) {A B : Set E} (hA : Convex ℝ A) (hAc : IsCompact A)
    (hA0 : volume A ≠ 0) (hB : Convex ℝ B) (hBc : IsCompact B) (hB0 : volume B ≠ 0) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    volume.real (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
        c * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
          d * volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ↔
      ∃ v : E, ∃ r : ℝ, 0 < r ∧ B = v +ᵥ r • A := by
  first
  | refine ⟨fun h ↦ hA.exists_eq_vadd_smul_of_volume_real_rpow_le hAc hA0 hB hBc hB0 hc hd h.le, ?_⟩
    rintro ⟨v, r, hr, rfl⟩
    have hscale {k : ℝ} (hk : 0 ≤ k) : volume.real (k • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
        k * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
      rw [measureReal_def, ENNReal.toReal_rpow, volume_smul_rpow hn, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg k), abs_of_nonneg hk, ← ENNReal.toReal_rpow,
        measureReal_def]
    have hset : c • A + d • (v +ᵥ r • A) = d • v +ᵥ (c + d * r) • A := by
      have hdB : d • (v +ᵥ r • A) = d • v +ᵥ (d * r) • A := by
        simp only [← image_smul, ← image_vadd, image_image, vadd_eq_add, smul_add, smul_smul]
      rw [hdB, add_vadd_comm, hA.add_smul hc.le (by positivity)]
    have hvadd (w : E) (s : Set E) : volume.real (w +ᵥ s) = volume.real s := by
      rw [measureReal_def, measure_vadd, measureReal_def]
    rw [hset, hvadd, hvadd, hscale (by positivity), hscale hr.le]
    ring

end TauCeti
end -- closes the original EOF section from source line 56
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Homothety.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarComparison.lean -/
section


@[expose] public section
noncomputable section

/-!
# Exact planar comparison from ordinary area

The paper's equality case is used here only after its hypotheses have been
recovered from literal Lebesgue areas.  The plane `ℝ × ℝ` has the max norm in
Mathlib, so the inner-product Brunn–Minkowski theorem is applied after a
measure-preserving linear transport to `WithLp 2 (ℝ × ℝ)`.
-/

open MeasureTheory Set
open scoped Pointwise ENNReal

namespace VolumePolynomials

private theorem equal_area_translates_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 2)
    {K L : Set E} (hK : Convex ℝ K) (hKc : IsCompact K)
    (hL : Convex ℝ L) (hLc : IsCompact L)
    (hpos : 0 < volume.real K)
    (heq : volume.real L = volume.real K)
    (hsum : volume.real (K + L) = 4 * volume.real K) :
    ∃ v : E, L = v +ᵥ K := by
  first
  | have hK0 : volume K ≠ 0 := by
      intro h
      simp [Measure.real, h] at hpos
    have hvol : volume L = volume K := by
      calc
        volume L = ENNReal.ofReal (volume.real L) :=
          (ofReal_measureReal hLc.measure_lt_top.ne).symm
        _ = ENNReal.ofReal (volume.real K) := congrArg ENNReal.ofReal heq
        _ = volume K := ofReal_measureReal hKc.measure_lt_top.ne
    have hL0 : volume L ≠ 0 := hvol.symm ▸ hK0
    have hmidc : IsCompact ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L) :=
      (hKc.smul (1 / 2 : ℝ)).add (hLc.smul (1 / 2 : ℝ))
    have hmidReal : volume.real ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L) =
        volume.real K := by
      rw [← smul_add]
      change (volume ((1 / 2 : ℝ) • (K + L))).toReal = (volume K).toReal
      rw [Measure.addHaar_smul_of_nonneg volume (show 0 ≤ (1 / 2 : ℝ) by norm_num),
        hdim, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
      change (1 / 2 : ℝ) ^ 2 * volume.real (K + L) = volume.real K
      rw [hsum]
      ring
    have hmid : volume ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L) = volume K := by
      calc
        _ = ENNReal.ofReal (volume.real ((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L)) :=
          (ofReal_measureReal hmidc.measure_lt_top.ne).symm
        _ = ENNReal.ofReal (volume.real K) := congrArg ENNReal.ofReal hmidReal
        _ = volume K := ofReal_measureReal hKc.measure_lt_top.ne
    apply hK.exists_eq_vadd_of_volume_le hKc hK0 hL hLc hL0
      (show 0 < (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hmid, hvol,
      ← ENNReal.rpow_add _ _ hK0 hKc.measure_lt_top.ne]
    norm_num

/-- Two compact convex planar sets of the same positive area are translates if
the area of their sum is four times their common area. -/
theorem equal_area_translates
    {K L : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKc : IsCompact K)
    (hL : Convex ℝ L) (hLc : IsCompact L)
    (hpos : 0 < volume.real K)
    (heq : volume.real L = volume.real K)
    (hsum : volume.real (K + L) = 4 * volume.real K) :
    ∃ v : ℝ × ℝ, L = v +ᵥ K := by
  first
  | let e : (ℝ × ℝ) ≃L[ℝ] WithLp 2 (ℝ × ℝ) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm
    have he : MeasurePreserving e volume volume := WithLp.volume_preserving_toLp ℝ ℝ
    have harea (S : Set (ℝ × ℝ)) : volume.real (e '' S) = volume.real S := by
      have hm := he.measure_preimage_emb
        e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (e '' S)
      rw [Set.preimage_image_eq _ e.injective] at hm
      simpa only [measureReal_def] using congrArg ENNReal.toReal hm.symm
    have hdim : Module.finrank ℝ (WithLp 2 (ℝ × ℝ)) = 2 := by
      rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq]
      simp
    have hsum' : volume.real (e '' K + e '' L) = 4 * volume.real (e '' K) := by
      rw [← Set.image_add e, harea, harea]
      exact hsum
    obtain ⟨v, hv⟩ := equal_area_translates_inner hdim
      (hK.linear_image e.toLinearMap) (hKc.image e.continuous)
      (hL.linear_image e.toLinearMap) (hLc.image e.continuous)
      (by
        change 0 < volume.real (e '' K)
        rwa [harea])
      (by
        change volume.real (e '' L) = volume.real (e '' K)
        simpa only [harea] using heq) hsum'
    refine ⟨e.symm v, ?_⟩
    have hi := congrArg (Set.image e.symm) hv
    change e.symm '' (e '' L) = e.symm '' (v +ᵥ e '' K) at hi
    simpa only [← Set.image_vadd, Set.image_image, Function.comp_apply,
      vadd_eq_add, map_add, e.symm_apply_apply, Set.image_id'] using hi


end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarComparison.lean -/

/- BEGIN SOURCE: VolumePolynomials/MinkowskiSeries.lean -/
section


@[expose] public section
noncomputable section

/-!
Infinite Minkowski sums of centered segments, represented by an honest subset of a
complete real normed space. The existence assertions below use compactness of a
product of intervals and absolute convergence, not a postulated convex-body API.
-/

namespace VolumePolynomials

open scoped Topology
open Set

abbrev SegmentChoice := ℕ → Icc (- (1/2 : ℝ)) (1/2 : ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A point of the infinite Minkowski sum, with one coefficient per segment. -/
noncomputable def seriesPoint (u : ℕ → E) (t : SegmentChoice) : E :=
  ∑' n, (t n : ℝ) • u n

/-- The infinite Minkowski sum of the centered segments generated by `u n`. -/
def segmentSeries (u : ℕ → E) : Set E := Set.range (seriesPoint u)

theorem choice_abs_le (t : SegmentChoice) (n : ℕ) : |(t n : ℝ)| ≤ 1/2 :=
  abs_le.mpr (t n).property

theorem series_term_norm_le (u : ℕ → E) (t : SegmentChoice) (n : ℕ) :
    ‖(t n : ℝ) • u n‖ ≤ (1/2 : ℝ) * ‖u n‖ := by
  first
  | rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (choice_abs_le t n) (norm_nonneg _)

theorem series_summable (u : ℕ → E) (hu : Summable fun n => ‖u n‖)
    (t : SegmentChoice) : Summable fun n => (t n : ℝ) • u n := by
  first
  | exact (hu.mul_left (1/2)).of_norm_bounded (series_term_norm_le u t)

theorem continuous_seriesPoint (u : ℕ → E) (hu : Summable fun n => ‖u n‖) :
    Continuous (seriesPoint u) := by
  first
  | apply continuous_tsum
    · intro n
      exact ((continuous_apply n).subtype_val).smul continuous_const
    · exact hu.mul_left (1/2)
    · intro n t
      exact series_term_norm_le u t n

theorem segmentSeries_isCompact (u : ℕ → E) (hu : Summable fun n => ‖u n‖) :
    IsCompact (segmentSeries u) :=
  isCompact_range (continuous_seriesPoint u hu)

theorem zero_mem_segmentSeries (u : ℕ → E) : (0 : E) ∈ segmentSeries u := by
  first
  | refine ⟨fun _ => ⟨0, by constructor <;> norm_num⟩, ?_⟩
    simp [seriesPoint]

theorem segmentSeries_convex (u : ℕ → E) (hu : Summable fun n => ‖u n‖) :
    Convex ℝ (segmentSeries u) := by
  first
  | intro x hx y hy a b ha hb hab
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    let w : SegmentChoice := fun n =>
      ⟨a * (s n : ℝ) + b * (t n : ℝ), by
        change a • (s n : ℝ) + b • (t n : ℝ) ∈ Icc (- (1/2 : ℝ)) (1/2 : ℝ)
        exact (convex_Icc (𝕜 := ℝ) (- (1/2 : ℝ)) (1/2 : ℝ))
          (s n).property (t n).property ha hb hab⟩
    refine ⟨w, ?_⟩
    dsimp [seriesPoint, w]
    simp_rw [add_smul, mul_smul]
    rw [Summable.tsum_add ((series_summable u hu s).const_smul a)
      ((series_summable u hu t).const_smul b),
      (series_summable u hu s).tsum_const_smul,
      (series_summable u hu t).tsum_const_smul]

/-- The actual compact convex body associated with an absolutely summable segment sequence. -/
noncomputable def segmentSeriesBody (u : ℕ → E) (hu : Summable fun n => ‖u n‖) :
    ConvexBody E where
  carrier := segmentSeries u
  convex' := segmentSeries_convex u hu
  isCompact' := segmentSeries_isCompact u hu
  nonempty' := ⟨0, zero_mem_segmentSeries u⟩

/-- The centered segment with generating vector `v`. -/
def centeredSegment (v : E) : Set E :=
  {x | ∃ t : Icc (- (1/2 : ℝ)) (1/2 : ℝ), x = (t : ℝ) • v}

theorem centeredSegment_eq_image (v : E) :
    centeredSegment v = (fun t : ℝ => t • v) '' Icc (-(1/2 : ℝ)) (1/2 : ℝ) := by
  first
  | ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩

theorem centeredSegment_isCompact (v : E) : IsCompact (centeredSegment v) := by
  first
  | rw [centeredSegment_eq_image]
    exact isCompact_Icc.image (continuous_id.smul continuous_const)

theorem centeredSegment_convex (v : E) : Convex ℝ (centeredSegment v) := by
  first
  | rw [centeredSegment_eq_image]
    exact (convex_Icc (𝕜 := ℝ) (- (1/2 : ℝ)) (1/2 : ℝ)).linear_image
      (LinearMap.toSpanSingleton ℝ E v)

theorem zero_mem_centeredSegment (v : E) : (0 : E) ∈ centeredSegment v := by
  first
  | exact ⟨⟨0, by constructor <;> norm_num⟩, by simp⟩

/-- Discard the initial coefficient of a segment choice. -/
def choiceTail (t : SegmentChoice) : SegmentChoice := fun n => t (n + 1)

/-- Prepend a coefficient to an infinite segment choice. -/
def choiceCons (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) (t : SegmentChoice) : SegmentChoice
  | 0 => a
  | n + 1 => t n

@[simp] theorem choiceCons_zero (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ))
    (t : SegmentChoice) : choiceCons a t 0 = a := rfl

@[simp] theorem choiceTail_cons (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ))
    (t : SegmentChoice) : choiceTail (choiceCons a t) = t := rfl

theorem seriesPoint_split (A : E →L[ℝ] E) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (hrec : ∀ n, u (n + 1) = A (u n))
    (t : SegmentChoice) :
    seriesPoint u t = (t 0 : ℝ) • u 0 + A (seriesPoint u (choiceTail t)) := by
  first
  | rw [seriesPoint, (series_summable u hu t).tsum_eq_zero_add]
    congr 1
    rw [seriesPoint, A.map_tsum (series_summable u hu (choiceTail t))]
    apply tsum_congr
    intro n
    simp only [choiceTail, hrec, map_smul]

open scoped Pointwise in
/-- The infinite Minkowski sum satisfies its exact affine set equation. -/
theorem segmentSeries_fixed (A : E →L[ℝ] E) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (hrec : ∀ n, u (n + 1) = A (u n)) :
    segmentSeries u = centeredSegment (u 0) + A '' segmentSeries u := by
  first
  | ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact Set.mem_add.mpr ⟨(t 0 : ℝ) • u 0, ⟨t 0, rfl⟩,
        A (seriesPoint u (choiceTail t)), ⟨seriesPoint u (choiceTail t),
          ⟨choiceTail t, rfl⟩, rfl⟩, (seriesPoint_split A u hu hrec t).symm⟩
    · intro hx
      obtain ⟨y, ⟨a, rfl⟩, z, ⟨q, ⟨t, rfl⟩, rfl⟩, rfl⟩ := Set.mem_add.mp hx
      refine ⟨choiceCons a t, ?_⟩
      simpa only [choiceCons_zero, choiceTail_cons] using
        seriesPoint_split A u hu hrec (choiceCons a t)

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MinkowskiSeries.lean -/

/- BEGIN SOURCE: VolumePolynomials/AffineAttractor.lean -/
section


@[expose] public section
noncomputable section

/-! Uniqueness of compact attractors for a linear map whose powers tend to zero.
The argument retains the exact set-valued affine equation; it uses no convexity,
no support-function representation, and no unproved contraction assumption. -/

namespace VolumePolynomials

open scoped Topology Pointwise
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fixed_sets_finite_matching (A : E →L[ℝ] E)
    (S K L : Set E) (hK : K = S + A '' K) (hL : L = S + A '' L)
    (z₀ : E) (hz₀ : z₀ ∈ L) :
    ∀ n : ℕ, ∀ x ∈ K, ∃ z ∈ L, ∃ y ∈ K, x = z + (A ^ n) (y - z₀) := by
  first
  | intro n
    induction n with
    | zero =>
        intro x hx
        refine ⟨z₀, hz₀, x, hx, ?_⟩
        simp
    | succ n ih =>
        intro x hx
        rw [hK] at hx
        obtain ⟨s, hs, w, ⟨y, hy, rfl⟩, rfl⟩ := Set.mem_add.mp hx
        obtain ⟨z, hz, q, hq, heq⟩ := ih y hy
        refine ⟨s + A z, ?_, q, hq, ?_⟩
        · rw [hL]
          exact Set.mem_add.mpr ⟨s, hs, A z, ⟨z, hz, rfl⟩, rfl⟩
        · rw [heq, map_add, pow_succ', ContinuousLinearMap.mul_apply]
          abel

private theorem compact_fixed_subset (A : E →L[ℝ] E)
    (hA : Tendsto (fun n : ℕ => ‖A ^ n‖) atTop (𝓝 0))
    (S K L : Set E) (hKcompact : IsCompact K) (hLclosed : IsClosed L)
    (hLnonempty : L.Nonempty) (hK : K = S + A '' K) (hL : L = S + A '' L) :
    K ⊆ L := by
  first
  | obtain ⟨z₀, hz₀⟩ := hLnonempty
    obtain ⟨R, hRpos, hR⟩ := hKcompact.isBounded.exists_pos_norm_le
    intro x hx
    choose z hz y hy heq using
      fun n => fixed_sets_finite_matching A S K L hK hL z₀ hz₀ n x hx
    have hbound (n : ℕ) : ‖x - z n‖ ≤ ‖A ^ n‖ * (R + ‖z₀‖) := by
      calc
        ‖x - z n‖ = ‖(A ^ n) (y n - z₀)‖ := by rw [heq n]; simp
        _ ≤ ‖A ^ n‖ * ‖y n - z₀‖ := (A ^ n).le_opNorm _
        _ ≤ ‖A ^ n‖ * (R + ‖z₀‖) :=
          mul_le_mul_of_nonneg_left
            ((norm_sub_le _ _).trans (add_le_add (hR _ (hy n)) le_rfl)) (norm_nonneg _)
    have hzero : Tendsto (fun n => x - z n) atTop (𝓝 0) :=
      squeeze_zero_norm hbound (by simpa using hA.mul_const (R + ‖z₀‖))
    have hzconv : Tendsto z atTop (𝓝 x) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hzero)
    exact hLclosed.mem_of_tendsto hzconv (Eventually.of_forall hz)

/-- Two nonempty compact solutions to the same affine Minkowski equation coincide
when the powers of its linear part converge to zero in operator norm. -/
theorem compact_affine_fixed_unique (A : E →L[ℝ] E)
    (hA : Tendsto (fun n : ℕ => ‖A ^ n‖) atTop (𝓝 0))
    (S K L : Set E) (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hKnonempty : K.Nonempty) (hLnonempty : L.Nonempty)
    (hK : K = S + A '' K) (hL : L = S + A '' L) : K = L := by
  first
  | apply Set.Subset.antisymm
    · exact compact_fixed_subset A hA S K L hKcompact hLcompact.isClosed hLnonempty hK hL
    · exact compact_fixed_subset A hA S L K hLcompact hKcompact.isClosed hKnonempty hL hK

end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AffineAttractor.lean -/

/- BEGIN SOURCE: VolumePolynomials/ExposedSeries.lean -/
section


@[expose] public section
noncomputable section

/-! Explicit nontrivial exposed segments in an infinite Minkowski series. -/

namespace VolumePolynomials

open scoped Topology
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A coefficient choice maximizing a fixed linear functional, one segment at a time. -/
noncomputable def maximizingChoice (l : E →L[ℝ] ℝ) (u : ℕ → E) : SegmentChoice := by
  first
  | classical
    exact fun n => if 0 ≤ l (u n) then ⟨1/2, by constructor <;> norm_num⟩
      else ⟨-(1/2), by constructor <;> norm_num⟩

theorem maximizingChoice_term (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (t : SegmentChoice) (n : ℕ) :
    l ((t n : ℝ) • u n) ≤ l ((maximizingChoice l u n : ℝ) • u n) := by
  first
  | classical
    simp only [map_smul, smul_eq_mul]
    by_cases h : 0 ≤ l (u n)
    · simp only [maximizingChoice, if_pos h]
      exact mul_le_mul_of_nonneg_right (t n).property.2 h
    · simp only [maximizingChoice, if_neg h]
      exact mul_le_mul_of_nonpos_right (t n).property.1 (le_of_not_ge h)

theorem maximizingChoice_maximal (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) {x : E} (hx : x ∈ segmentSeries u) :
    l x ≤ l (seriesPoint u (maximizingChoice l u)) := by
  first
  | obtain ⟨t, rfl⟩ := hx
    rw [seriesPoint, seriesPoint, l.map_tsum (series_summable u hu t),
      l.map_tsum (series_summable u hu (maximizingChoice l u))]
    exact Summable.tsum_le_tsum (maximizingChoice_term l u t)
      (l.summable (series_summable u hu t))
      (l.summable (series_summable u hu (maximizingChoice l u)))

theorem seriesPoint_update_sub (u : ℕ → E) (hu : Summable fun n => ‖u n‖)
    (t : SegmentChoice) (j : ℕ) (a b : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    seriesPoint u (Function.update t j a) - seriesPoint u (Function.update t j b) =
      ((a : ℝ) - (b : ℝ)) • u j := by
  first
  | classical
    rw [seriesPoint, seriesPoint, ← Summable.tsum_sub
      (series_summable u hu (Function.update t j a))
      (series_summable u hu (Function.update t j b))]
    rw [tsum_eq_single j]
    · simp [sub_smul]
    · intro n hn
      simp [Function.update_of_ne hn]

theorem maximizingChoice_update_value (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    l (seriesPoint u (Function.update (maximizingChoice l u) j a)) =
      l (seriesPoint u (maximizingChoice l u)) := by
  first
  | classical
    rw [seriesPoint, seriesPoint,
      l.map_tsum (series_summable u hu (Function.update (maximizingChoice l u) j a)),
      l.map_tsum (series_summable u hu (maximizingChoice l u))]
    apply tsum_congr
    intro n
    by_cases hn : n = j
    · subst n
      simp [map_smul, hj]
    · simp [Function.update_of_ne hn]

theorem maximizingChoice_update_mem_exposed (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    seriesPoint u (Function.update (maximizingChoice l u) j a) ∈
      l.toExposed (segmentSeries u) := by
  first
  | constructor
    · exact ⟨Function.update (maximizingChoice l u) j a, rfl⟩
    · intro y hy
      rw [maximizingChoice_update_value l u hu j hj a]
      exact maximizingChoice_maximal l u hu hy

/-- A maximizer of a functional having a positive direction cannot be an interior point. -/
theorem exposed_mem_frontier (l : E →L[ℝ] ℝ) (s : Set E) (v : E)
    (hv : 0 < l v) {x : E} (hx : x ∈ l.toExposed s) : x ∈ frontier s := by
  first
  | rw [mem_frontier_iff_notMem_interior hx.1]
    intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    have hvne : v ≠ 0 := by intro h; simpa [h] using hv
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    let t : ℝ := ε / (2 * ‖v‖)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hvnorm)
    have hdist : dist (x + t • v) x < ε := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖v‖ = ε / 2 := by
        dsimp [t]
        field_simp [hvnorm.ne'] <;> ring
      rw [heq]
      linarith
    have hmem : x + t • v ∈ s := hball hdist
    have hle := hx.2 (x + t • v) hmem
    rw [map_add, map_smul, smul_eq_mul] at hle
    have : 0 < t * l v := mul_pos ht hv
    linarith

/-- The whole translated j-th centered segment is exposed, not just its endpoints. -/
theorem translated_segment_mem_exposed (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0) :
    ∃ a : E, ∀ t : ℝ, -(1/2 : ℝ) ≤ t → t ≤ 1/2 →
      a + t • u j ∈ l.toExposed (segmentSeries u) := by
  first
  | classical
    let z : Icc (- (1/2 : ℝ)) (1/2 : ℝ) := ⟨0, by constructor <;> norm_num⟩
    let a := seriesPoint u (Function.update (maximizingChoice l u) j z)
    refine ⟨a, ?_⟩
    intro t htlo hthi
    let q : Icc (- (1/2 : ℝ)) (1/2 : ℝ) := ⟨t, htlo, hthi⟩
    have heq := seriesPoint_update_sub u hu (maximizingChoice l u) j q z
    have heq' : seriesPoint u (Function.update (maximizingChoice l u) j q) = a + t • u j := by
      dsimp [a, q, z] at *
      simpa [sub_eq_iff_eq_add, add_comm] using heq
    rw [← heq']
    exact maximizingChoice_update_mem_exposed l u hu j hj q

theorem translated_segment_mem_frontier (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (v : E) (hv : 0 < l v) :
    ∃ a : E, ∀ t : ℝ, -(1/2 : ℝ) ≤ t → t ≤ 1/2 →
      a + t • u j ∈ frontier (segmentSeries u) := by
  first
  | obtain ⟨a, ha⟩ := translated_segment_mem_exposed l u hu j hj
    exact ⟨a, fun t htlo hthi => exposed_mem_frontier l _ v hv (ha t htlo hthi)⟩

/-- At a maximizing point, every coefficient whose direction has nonzero support value is
forced to its unique maximizing endpoint. -/
theorem maximizingChoice_unique_coordinate (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (t : SegmentChoice)
    (ht : l (seriesPoint u t) = l (seriesPoint u (maximizingChoice l u)))
    (n : ℕ) (hn : l (u n) ≠ 0) : t n = maximizingChoice l u n := by
  first
  | let f : ℕ → ℝ := fun k => l ((maximizingChoice l u k : ℝ) • u k) - l ((t k : ℝ) • u k)
    have hf : Summable f :=
      (l.summable (series_summable u hu (maximizingChoice l u))).sub
        (l.summable (series_summable u hu t))
    have hfnonneg (k : ℕ) : 0 ≤ f k := sub_nonneg.mpr (maximizingChoice_term l u t k)
    have hsum : ∑' k, f k = 0 := by
      rw [Summable.tsum_sub
        (l.summable (series_summable u hu (maximizingChoice l u)))
        (l.summable (series_summable u hu t)),
        ← l.map_tsum (series_summable u hu (maximizingChoice l u)),
        ← l.map_tsum (series_summable u hu t)]
      exact sub_eq_zero.mpr ht.symm
    have hle := hf.le_tsum n (fun k _ => hfnonneg k)
    rw [hsum] at hle
    have heq : f n = 0 := le_antisymm hle (hfnonneg n)
    dsimp [f] at heq
    simp only [map_smul, smul_eq_mul] at heq
    apply Subtype.ext
    exact (mul_right_cancel₀ hn (sub_eq_zero.mp heq)).symm

/-- If just one generating direction is perpendicular to the normal, its whole centered
segment, translated by the endpoint sum, is exactly the exposed face. -/
theorem exposed_face_eq_centered_segment (l : E →L[ℝ] ℝ) (u : ℕ → E)
    (hu : Summable fun n => ‖u n‖) (j : ℕ) (hj : l (u j) = 0)
    (hnonzero : ∀ n, n ≠ j → l (u n) ≠ 0) :
    ∃ a : E, l.toExposed (segmentSeries u) =
      {x | ∃ t : Icc (- (1/2 : ℝ)) (1/2 : ℝ), x = a + (t : ℝ) • u j} := by
  first
  | classical
    let z : Icc (- (1/2 : ℝ)) (1/2 : ℝ) := ⟨0, by constructor <;> norm_num⟩
    let a := seriesPoint u (Function.update (maximizingChoice l u) j z)
    have heq (t : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
        seriesPoint u (Function.update (maximizingChoice l u) j t) = a + (t : ℝ) • u j := by
      have h := seriesPoint_update_sub u hu (maximizingChoice l u) j t z
      dsimp [a, z] at *
      simpa [sub_eq_iff_eq_add, add_comm] using h
    refine ⟨a, Set.ext fun x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨t, rfl⟩ := hx.1
      have hval : l (seriesPoint u t) = l (seriesPoint u (maximizingChoice l u)) :=
        (maximizingChoice_maximal l u hu ⟨t, rfl⟩).antisymm
          (hx.2 _ ⟨maximizingChoice l u, rfl⟩)
      have ht : t = Function.update (maximizingChoice l u) j (t j) := by
        funext n
        by_cases hn : n = j
        · subst n
          simp
        · rw [Function.update_of_ne hn]
          exact maximizingChoice_unique_coordinate l u hu t hval n (hnonzero n hn)
      refine ⟨t j, ?_⟩
      conv_lhs => rw [ht]
      exact heq (t j)
    · rintro ⟨t, rfl⟩
      rw [← heq t]
      exact maximizingChoice_update_mem_exposed l u hu j hj t

end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ExposedSeries.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolonomySeries.lean -/
section


@[expose] public section
noncomputable section

/-! The actual compact convex Minkowski series of Theorem 7.3. -/

namespace VolumePolynomials.Holonomy

open scoped Topology Pointwise
open Set Filter

/-- The contraction times the prescribed return map. -/
def scaledReturn (lam : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := lam • returnContinuous

/-- Generating vectors of the infinite Minkowski sum in equation (7.10). -/
def weightedOrbit (lam : ℝ) (n : ℕ) : ℝ × ℝ := lam ^ n • orbit n

theorem weightedOrbit_recurrence (lam : ℝ) (n : ℕ) :
    weightedOrbit lam (n + 1) = scaledReturn lam (weightedOrbit lam n) := by
  first
  | simp only [weightedOrbit, scaledReturn, ContinuousLinearMap.smul_apply,
      map_smul, returnContinuous_apply, orbit_succ, pow_succ, smul_smul]

theorem weightedOrbit_summable (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    Summable fun n => ‖weightedOrbit lam n‖ := by
  first
  | apply ((summable_geometric_of_lt_one hlam₀ hlam₁).mul_left 2).of_norm_bounded
    intro n
    rw [norm_norm, weightedOrbit, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlam₀ n)]
    exact (mul_le_mul_of_nonneg_left (orbit_norm_le n) (pow_nonneg hlam₀ n)).trans_eq
      (mul_comm _ _)

theorem return_pow_apply (n : ℕ) (p : ℝ × ℝ) :
    (returnContinuous ^ n) p = p.1 • orbit n - p.2 • orbit (n + 1) := by
  first
  | induction n with
    | zero =>
        ext <;> simp [orbit, returnMap]
    | succ n ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_sub, map_smul, map_smul]
        rfl

theorem return_pow_norm_le (n : ℕ) : ‖returnContinuous ^ n‖ ≤ 4 := by
  first
  | apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro p
    rw [return_pow_apply]
    calc
      ‖p.1 • orbit n - p.2 • orbit (n + 1)‖
        ≤ ‖p.1 • orbit n‖ + ‖p.2 • orbit (n + 1)‖ := norm_sub_le _ _
      _ ≤ 2 * ‖p.1‖ + 2 * ‖p.2‖ := by
        simp only [norm_smul]
        have h₁ := mul_le_mul_of_nonneg_left (orbit_norm_le n) (norm_nonneg p.1)
        have h₂ := mul_le_mul_of_nonneg_left (orbit_norm_le (n + 1)) (norm_nonneg p.2)
        nlinarith
      _ ≤ 4 * ‖p‖ := by
        have h₁ : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
        have h₂ : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
        linarith

theorem scaledReturn_pow_norm_le (lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    ‖scaledReturn lam ^ n‖ ≤ 4 * lam ^ n := by
  first
  | rw [scaledReturn, smul_pow, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlam n)]
    exact (mul_le_mul_of_nonneg_left (return_pow_norm_le n) (pow_nonneg hlam n)).trans_eq
      (mul_comm _ _)

theorem scaledReturn_powers_tendsto_zero (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    Tendsto (fun n : ℕ => ‖scaledReturn lam ^ n‖) atTop (𝓝 0) := by
  first
  | apply squeeze_zero (fun n => norm_nonneg _) (scaledReturn_pow_norm_le lam hlam₀)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam₀ hlam₁).const_mul 4

/-- The compact convex set Kλ, defined by the actual infinite segment sum. -/
noncomputable def forcedBody (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) : ConvexBody (ℝ × ℝ) :=
  segmentSeriesBody (weightedOrbit lam) (weightedOrbit_summable lam hlam₀ hlam₁)

@[simp] theorem forcedBody_carrier (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) = segmentSeries (weightedOrbit lam) := rfl

/-- The exact functional equation of equation (7.10), on actual subsets of the plane. -/
theorem forcedBody_fixed (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) =
      centeredSegment (1, 0) + scaledReturn lam '' (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) := by
  first
  | simpa [weightedOrbit] using segmentSeries_fixed (scaledReturn lam) (weightedOrbit lam)
      (weightedOrbit_summable lam hlam₀ hlam₁) (weightedOrbit_recurrence lam)

/-- Uniqueness holds even among all nonempty compact sets, without assuming convexity. -/
theorem forcedBody_unique (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (K : Set (ℝ × ℝ)) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hK : K = centeredSegment (1, 0) + scaledReturn lam '' K) :
    K = (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) :=
  compact_affine_fixed_unique (scaledReturn lam)
    (scaledReturn_powers_tendsto_zero lam hlam₀ hlam₁)
    (centeredSegment (1, 0)) K (forcedBody lam hlam₀ hlam₁)
    hKcompact (forcedBody lam hlam₀ hlam₁).isCompact
    hKnonempty (forcedBody lam hlam₀ hlam₁).nonempty
    hK (forcedBody_fixed lam hlam₀ hlam₁)

theorem det_smul (a b : ℝ) (p q : ℝ × ℝ) :
    det (a • p) (b • q) = a * b * det p q := by
  first
  | dsimp [det]
    ring

theorem weightedOrbit_nonparallel (lam : ℝ) (hlam : 0 < lam) (i j : ℕ) (hij : i ≠ j) :
    det (weightedOrbit lam i) (weightedOrbit lam j) ≠ 0 := by
  first
  | rw [weightedOrbit, weightedOrbit, det_smul]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero i hlam.ne') (pow_ne_zero j hlam.ne'))
      (det_orbit_ne_zero hij)

theorem weightedOrbit_ne_zero (lam : ℝ) (hlam : 0 < lam) (j : ℕ) : weightedOrbit lam j ≠ 0 := by
  first
  | intro hz
    have hn := weightedOrbit_nonparallel lam hlam j (j + 1) (by omega)
    simp [hz, det] at hn

/-- A support functional perpendicular to the j-th generating vector. -/
def orbitNormal (lam : ℝ) (j : ℕ) : (ℝ × ℝ) →L[ℝ] ℝ where
  toFun x := det (weightedOrbit lam j) x
  map_add' := by intro x y; dsimp [det]; ring
  map_smul' := by intro c x; dsimp [det]; ring
  cont := by dsimp [det]; fun_prop

@[simp] theorem orbitNormal_self (lam : ℝ) (j : ℕ) :
    orbitNormal lam j (weightedOrbit lam j) = 0 := by
  change det (weightedOrbit lam j) (weightedOrbit lam j) = 0
  dsimp [det]
  ring

theorem orbitNormal_positive_direction (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    0 < orbitNormal lam j (-(weightedOrbit lam j).2, (weightedOrbit lam j).1) := by
  first
  | have hu : weightedOrbit lam j ≠ 0 := by
      exact weightedOrbit_ne_zero lam hlam j
    have hp : (weightedOrbit lam j).1 ≠ 0 ∨ (weightedOrbit lam j).2 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (Prod.ext h.1 h.2)
    change 0 < (weightedOrbit lam j).1 * (weightedOrbit lam j).1 -
      (weightedOrbit lam j).2 * (-(weightedOrbit lam j).2)
    rcases hp with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (weightedOrbit lam j).2]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (weightedOrbit lam j).1]

/-- For every j, an entire nontrivial segment in direction lam^j M^j e₁ lies in the frontier. -/
theorem forcedBody_boundary_segments (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∃ a : ℕ → ℝ × ℝ, ∀ j t, t ∈ Icc (- (1/2 : ℝ)) (1/2 : ℝ) →
      a j + t • weightedOrbit lam j ∈ frontier (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
  first
  | have hseg (j : ℕ) := translated_segment_mem_frontier (orbitNormal lam j)
      (weightedOrbit lam) (weightedOrbit_summable lam hlam₀.le hlam₁) j (orbitNormal_self lam j)
      (-(weightedOrbit lam j).2, (weightedOrbit lam j).1)
      (orbitNormal_positive_direction lam hlam₀ j)
    choose a ha using hseg
    exact ⟨a, fun j t ht => ha j t ht.1 ht.2⟩

/-- Each displayed boundary segment is the entire exposed face. Its generator is nonzero,
and the generators are pairwise nonparallel by `weightedOrbit_nonparallel`. -/
theorem forcedBody_exposed_faces (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∃ a : ℕ → ℝ × ℝ, ∀ j,
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) =
        {x | ∃ t : Icc (- (1/2 : ℝ)) (1/2 : ℝ),
          x = a j + (t : ℝ) • weightedOrbit lam j} := by
  first
  | have hface (j : ℕ) := exposed_face_eq_centered_segment (orbitNormal lam j)
      (weightedOrbit lam) (weightedOrbit_summable lam hlam₀.le hlam₁) j (orbitNormal_self lam j)
      (fun n hn => weightedOrbit_nonparallel lam hlam₀ j n hn.symm)
    choose a ha using hface
    exact ⟨a, ha⟩

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolonomySeries.lean -/

/- BEGIN SOURCE: VolumePolynomials/ProjectionCycle.lean -/
section


@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

/-- Linear maps carry actual translates to translates by the image vector. -/
theorem linear_image_vadd
    {E F T : Type*} [AddCommGroup E] [AddCommGroup F]
    [FunLike T E F] [AddMonoidHomClass T E F]
    (f : T) (v : E) (S : Set E) :
    f '' (v +ᵥ S) = f v +ᵥ f '' S := by
  first
  | simp only [← Set.image_vadd, Set.image_image, Function.comp_apply,
      vadd_eq_add, map_add]

def lastTransport (lam : ℝ) : Plane →L[ℝ] Plane :=
  lam • transport20.toContinuousLinearMap

@[simp] theorem lastTransport_apply (lam : ℝ) (p : Plane) :
    lastTransport lam p = lam • transport20 p := rfl

theorem image_transport_cycle (lam : ℝ) (A : Set Plane) :
    lastTransport lam '' (transport12 '' (transport01 '' A)) = scaledReturn lam '' A := by
  first
  | simp only [Set.image_image]
    congr 1
    funext p
    change lam • transport20 (transport12 (transport01 p)) = lam • returnMap p
    rw [transport_cycle]

/-- The three projected translation relations give exactly the affine return
equation, including all translation terms. -/
theorem projection_cycle_affine (lam : ℝ) (A B C S : Set Plane) (b c d : Plane)
    (hB : B = b +ᵥ transport01 '' A)
    (hC : C = c +ᵥ transport12 '' B)
    (hLast : A = d +ᵥ (S + lastTransport lam '' C)) :
    ∃ q : Plane, A = q +ᵥ (S + scaledReturn lam '' A) := by
  first
  | refine ⟨d + (lastTransport lam c + lastTransport lam (transport12 b)), ?_⟩
    rw [hC, hB] at hLast
    simpa only [linear_image_vadd, vadd_vadd, vadd_eq_add, add_vadd_comm,
      map_add, image_transport_cycle] using hLast

/-- Translating by the explicitly solved center removes the affine term. -/
theorem recenter_affine_equation (lam : ℝ) (A S : Set Plane) (q : Plane)
    (hA : A = q +ᵥ (S + scaledReturn lam '' A)) :
    -translationCenter lam q +ᵥ A =
      S + scaledReturn lam '' (-translationCenter lam q +ᵥ A) := by
  first
  | let c := translationCenter lam q
    have hc : -c + q = scaledReturn lam (-c) := by
      have ht := translationCenter_equation lam q
      change c - scaledReturn lam c = q at ht
      rw [← ht, map_neg]
      abel
    calc
      -c +ᵥ A = -c +ᵥ (q +ᵥ (S + scaledReturn lam '' A)) := congrArg (-c +ᵥ ·) hA
      _ = (-c + q) +ᵥ (S + scaledReturn lam '' A) := by
        simp only [vadd_vadd, vadd_eq_add]
      _ = scaledReturn lam (-c) +ᵥ (S + scaledReturn lam '' A) := by rw [hc]
      _ = S + (scaledReturn lam (-c) +ᵥ scaledReturn lam '' A) := by
        rw [add_vadd_comm]
      _ = S + scaledReturn lam '' (-c +ᵥ A) := by rw [linear_image_vadd]

/-- Every nonempty compact solution of the affine return equation is a translate
of the actual infinite Minkowski series. -/
theorem affine_solution_is_forced (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (A : Set Plane) (hAc : IsCompact A) (hAn : A.Nonempty)
    (q : Plane)
    (hA : A = q +ᵥ (centeredSegment (1, 0) + scaledReturn lam '' A)) :
    A = translationCenter lam q +ᵥ (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | have heq := forcedBody_unique lam hlam₀ hlam₁
      (-translationCenter lam q +ᵥ A)
      (hAc.vadd (-translationCenter lam q))
      hAn.vadd_set
      (recenter_affine_equation lam A (centeredSegment (1, 0)) q hA)
    rw [← heq]
    simp only [vadd_vadd, vadd_eq_add, add_neg_cancel, zero_vadd]

/-- Full three-plane conclusion after the projected equality cases have been
established: the three bodies are simultaneous translates of Kλ and its two
prescribed linear images. -/
theorem projection_cycle_forces_three_bodies
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (A B C : Set Plane) (hAc : IsCompact A) (hAn : A.Nonempty)
    (b c d : Plane)
    (hB : B = b +ᵥ transport01 '' A)
    (hC : C = c +ᵥ transport12 '' B)
    (hLast : A = d +ᵥ (centeredSegment (1, 0) + lastTransport lam '' C)) :
    ∃ a₀ b₀ c₀ : Plane,
      A = a₀ +ᵥ (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      B = b₀ +ᵥ transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      C = c₀ +ᵥ transport12 ''
        (transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) := by
  first
  | obtain ⟨q, hq⟩ := projection_cycle_affine lam A B C (centeredSegment (1, 0))
      b c d hB hC hLast
    let a₀ := translationCenter lam q
    have hA := affine_solution_is_forced lam hlam₀ hlam₁ A hAc hAn q hq
    refine ⟨a₀, b + transport01 a₀, c + transport12 (b + transport01 a₀), hA, ?_, ?_⟩
    · rw [hB, hA]
      simp only [linear_image_vadd, vadd_vadd, vadd_eq_add, a₀]
    · rw [hC, hB, hA]
      simp only [linear_image_vadd, vadd_vadd, vadd_eq_add, a₀]


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ProjectionCycle.lean -/

/- BEGIN SOURCE: VolumePolynomials/ProjectedShapeRigidity.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

theorem lift_projected_translation (e : Plane ≃L[ℝ] Plane)
    (A B : Set Plane) (v : Plane) (h : e '' B = v +ᵥ A) :
    B = e.symm v +ᵥ e.symm '' A := by
  first
  | have hi := congrArg (Set.image e.symm) h
    simpa only [linear_image_vadd, Set.image_image, Function.comp_apply,
      e.symm_apply_apply, Set.image_id'] using hi

def lastProjectedSet (lam : ℝ) (C : Set Plane) : Set Plane :=
  centeredSegment (1, 0) + lastTransport lam '' C

theorem lastProjectedSet_isCompact (lam : ℝ) (C : Set Plane) (hC : IsCompact C) :
    IsCompact (lastProjectedSet lam C) :=
  (centeredSegment_isCompact (1, 0)).add (hC.image (lastTransport lam).continuous)

theorem lastProjectedSet_convex (lam : ℝ) (C : Set Plane) (hC : Convex ℝ C) :
    Convex ℝ (lastProjectedSet lam C) :=
  (centeredSegment_convex (1, 0)).add (hC.linear_image (lastTransport lam).toLinearMap)

/-- The exact three planar area comparisons force the return equation. All three
equality cases are obtained from the proved Brunn–Minkowski equality theorem. -/
theorem projected_comparisons_force_shape
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (A B C : Set Plane)
    (hAc : IsCompact A) (hA : Convex ℝ A)
    (hBc : IsCompact B) (hB : Convex ℝ B)
    (hCc : IsCompact C) (hC : Convex ℝ C)
    (hApos : 0 < volume.real A)
    (hAB : volume.real (transport01 '' B) = volume.real A)
    (hABsum : volume.real (A + transport01 '' B) = 4 * volume.real A)
    (hBpos : 0 < volume.real B)
    (hBC : volume.real (transport12 '' C) = volume.real B)
    (hBCsum : volume.real (B + transport12 '' C) = 4 * volume.real B)
    (hAD : volume.real (lastProjectedSet lam C) = volume.real A)
    (hADsum : volume.real (A + lastProjectedSet lam C) = 4 * volume.real A) :
    ∃ a₀ b₀ c₀ : Plane,
      A = a₀ +ᵥ (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      B = b₀ +ᵥ transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      C = c₀ +ᵥ transport12 ''
        (transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) := by
  first
  | obtain ⟨b, hb⟩ := equal_area_translates hA hAc
      (hB.linear_image transport01.toLinearMap) (hBc.image transport01.continuous)
      hApos hAB hABsum
    have hb' : B = transport01 b +ᵥ transport01 '' A :=
      lift_projected_translation transport01 A B b hb
    obtain ⟨c, hc⟩ := equal_area_translates hB hBc
      (hC.linear_image transport12.toLinearMap) (hCc.image transport12.continuous)
      hBpos hBC hBCsum
    have hc' : C = transport12 c +ᵥ transport12 '' B :=
      lift_projected_translation transport12 B C c hc
    obtain ⟨d, hd⟩ := equal_area_translates hA hAc
      (lastProjectedSet_convex lam C hC) (lastProjectedSet_isCompact lam C hCc)
      hApos hAD hADsum
    have hd' : A = -d +ᵥ lastProjectedSet lam C := by
      rw [hd]
      simp only [vadd_vadd, vadd_eq_add, neg_add_cancel, zero_vadd]
    have hAn : A.Nonempty := by
      by_contra hn
      have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [he] at hApos
    exact projection_cycle_forces_three_bodies lam hlam₀ hlam₁ A B C hAc hAn
      (transport01 b) (transport12 c) (-d) hb' hc' hd'

theorem extrusionV_eq_projected_area (K : Set ThreeSpace)
    (hKc : IsCompact K) (hK : Convex ℝ K) :
    volume.real (K + centeredSegment directionV) - volume.real K =
      volume.real (projectionV '' K) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment frameV
      frameV_measurePreserving hKc hK frameV_direction
    rw [← centeredSegment_eq_image] at h
    rw [h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl

theorem extrusionW_eq_projected_area (K : Set ThreeSpace)
    (hKc : IsCompact K) (hK : Convex ℝ K) :
    volume.real (K + centeredSegment directionW) - volume.real K =
      volume.real (projectionW '' K) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment frameW
      frameW_measurePreserving hKc hK frameW_direction
    rw [← centeredSegment_eq_image] at h
    rw [h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl

theorem extrusionZ_eq_projected_area (K : Set ThreeSpace)
    (hKc : IsCompact K) (hK : Convex ℝ K) :
    volume.real (K + centeredSegment directionZ) - volume.real K =
      volume.real (projectionZ '' K) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment frameZ
      frameZ_measurePreserving hKc hK frameZ_direction
    rw [← centeredSegment_eq_image] at h
    rw [h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ProjectedShapeRigidity.lean -/

/- BEGIN SOURCE: VolumePolynomials/ShapeProjectionGeometry.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

def coordinateProjection (i : Fin 3) : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp (projectionFrame i 0).toContinuousLinearMap

@[simp] theorem fin3_succAbove_two_one :
    (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide

@[simp] theorem coordinateProjection_apply (i : Fin 3) (x : ThreeSpace) :
    coordinateProjection i x = (x (i.succAbove 0), x (i.succAbove 1)) := by
  first
  | simp [coordinateProjection]

@[simp] theorem coordinateProjectionXY_apply (x : ThreeSpace) :
    coordinateProjection 2 x = (x 0, x 1) := by
  first
  | simp [show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]

@[simp] theorem coordinateProjectionXZ_apply (x : ThreeSpace) :
    coordinateProjection 1 x = (x 0, x 2) := by simp

@[simp] theorem coordinateProjectionYZ_apply (x : ThreeSpace) :
    coordinateProjection 0 x = (x 1, x 2) := by simp

@[simp] theorem coordinateProjection_embedXY (p : Plane) :
    coordinateProjection 2 (embedXY p) = p := by simp [embedXY]

@[simp] theorem coordinateProjection_embedXZ (p : Plane) :
    coordinateProjection 1 (embedXZ p) = p := by simp [embedXZ]

@[simp] theorem coordinateProjection_embedYZ (p : Plane) :
    coordinateProjection 0 (embedYZ p) = p := by simp [embedYZ]

theorem embedXY_coordinateProjection {x : ThreeSpace} (hx : x 2 = 0) :
    embedXY (coordinateProjection 2 x) = x := by
  first
  | ext i
    fin_cases i <;> simp_all [embedXY]

theorem embedXZ_coordinateProjection {x : ThreeSpace} (hx : x 1 = 0) :
    embedXZ (coordinateProjection 1 x) = x := by
  first
  | ext i
    fin_cases i <;> simp_all [embedXZ]

theorem embedYZ_coordinateProjection {x : ThreeSpace} (hx : x 0 = 0) :
    embedYZ (coordinateProjection 0 x) = x := by
  first
  | ext i
    fin_cases i <;> simp_all [embedYZ]

def planarA (K : Fin 9 → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 2) (K ShapeConditions.bodyA)

def planarB (K : Fin 9 → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 1) (K ShapeConditions.bodyB)

def planarC (K : Fin 9 → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 0) (K ShapeConditions.bodyC)

theorem IsCalibratedTuple.placeA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    (K ShapeConditions.bodyA : Set ThreeSpace) = embedXY '' (planarA K : Set Plane) := by
  first
  | change _ = embedXY '' (coordinateProjection 2 '' (K ShapeConditions.bodyA : Set ThreeSpace))
    rw [Set.image_image]
    symm
    calc
      _ = id '' (K ShapeConditions.bodyA : Set ThreeSpace) :=
        Set.image_congr (fun x hx => embedXY_coordinateProjection (hK.planeA x hx))
      _ = _ := Set.image_id' _

theorem IsCalibratedTuple.placeB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    (K ShapeConditions.bodyB : Set ThreeSpace) = embedXZ '' (planarB K : Set Plane) := by
  first
  | change _ = embedXZ '' (coordinateProjection 1 '' (K ShapeConditions.bodyB : Set ThreeSpace))
    rw [Set.image_image]
    symm
    calc
      _ = id '' (K ShapeConditions.bodyB : Set ThreeSpace) :=
        Set.image_congr (fun x hx => embedXZ_coordinateProjection (hK.planeB x hx))
      _ = _ := Set.image_id' _

theorem IsCalibratedTuple.placeC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    (K ShapeConditions.bodyC : Set ThreeSpace) = embedYZ '' (planarC K : Set Plane) := by
  first
  | change _ = embedYZ '' (coordinateProjection 0 '' (K ShapeConditions.bodyC : Set ThreeSpace))
    rw [Set.image_image]
    symm
    calc
      _ = id '' (K ShapeConditions.bodyC : Set ThreeSpace) :=
        Set.image_congr (fun x hx => embedYZ_coordinateProjection (hK.planeC x hx))
      _ = _ := Set.image_id' _

theorem bodyExtrusion_eq_frame_projection (L : Body 3)
    (T : ThreeSpace ≃L[ℝ] (ℝ × Plane)) (hT : MeasurePreserving T volume volume)
    (v : ThreeSpace) (hv : T v = (1, 0)) :
    bodyVolume (L + centeredBody v) - bodyVolume L =
      volume.real (((ContinuousLinearMap.snd ℝ ℝ Plane).comp
        T.toContinuousLinearMap) '' (L : Set ThreeSpace)) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment T hT L.isCompact L.convex hv
    change volume.real ((L : Set ThreeSpace) + (centeredBody v : Set ThreeSpace)) -
      volume.real (L : Set ThreeSpace) = _
    rw [centeredBody_carrier, h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl

@[simp] theorem bodyExtrusion_V (L : Body 3) :
    bodyVolume (L + centeredBody directionV) - bodyVolume L =
      volume.real (projectionV '' (L : Set ThreeSpace)) :=
  bodyExtrusion_eq_frame_projection L frameV frameV_measurePreserving directionV frameV_direction

@[simp] theorem bodyExtrusion_W (L : Body 3) :
    bodyVolume (L + centeredBody directionW) - bodyVolume L =
      volume.real (projectionW '' (L : Set ThreeSpace)) :=
  bodyExtrusion_eq_frame_projection L frameW frameW_measurePreserving directionW frameW_direction

@[simp] theorem bodyExtrusion_Z (L : Body 3) :
    bodyVolume (L + centeredBody directionZ) - bodyVolume L =
      volume.real (projectionZ '' (L : Set ThreeSpace)) :=
  bodyExtrusion_eq_frame_projection L frameZ frameZ_measurePreserving directionZ frameZ_direction

@[simp] theorem bodyExtrusion_axis (L : Body 3) (i : Fin 3) :
    bodyVolume (L + centeredBody (axis i)) - bodyVolume L =
      volume.real (coordinateProjection i '' (L : Set ThreeSpace)) := by
  first
  | apply bodyExtrusion_eq_frame_projection L (projectionFrame i 0)
      (projectionFrame_measurePreserving i 0) (axis i)
    simp [projectionFrame_apply, axis, Pi.single_apply, Fin.succAbove_ne, Fin.ne_succAbove]

theorem IsCalibratedTuple.projectionVA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionV '' (K ShapeConditions.bodyA : Set ThreeSpace) = (planarA K : Set Plane) := by
  first
  | rw [hK.placeA]
    simp only [Set.image_image, Function.comp_apply, projectionV_embedXY, Set.image_id']

theorem IsCalibratedTuple.projectionVB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionV '' (K ShapeConditions.bodyB : Set ThreeSpace) =
      transport01 '' (planarB K : Set Plane) := by
  first
  | rw [hK.placeB]
    simp only [Set.image_image, Function.comp_apply, projectionV_embedXZ]

theorem IsCalibratedTuple.projectionWB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionW '' (K ShapeConditions.bodyB : Set ThreeSpace) = (planarB K : Set Plane) := by
  first
  | rw [hK.placeB]
    simp only [Set.image_image, Function.comp_apply, projectionW_embedXZ, Set.image_id']

theorem IsCalibratedTuple.projectionWC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionW '' (K ShapeConditions.bodyC : Set ThreeSpace) =
      transport12 '' (planarC K : Set Plane) := by
  first
  | rw [hK.placeC]
    simp only [Set.image_image, Function.comp_apply, projectionW_embedYZ]

theorem IsCalibratedTuple.projectionZA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionZ '' (K ShapeConditions.bodyA : Set ThreeSpace) = (planarA K : Set Plane) := by
  first
  | rw [hK.placeA]
    simp only [Set.image_image, Function.comp_apply, projectionZ_embedXY, Set.image_id']

theorem IsCalibratedTuple.projectionZC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionZ '' (K ShapeConditions.bodyC : Set ThreeSpace) =
      transport20 '' (planarC K : Set Plane) := by
  first
  | rw [hK.placeC]
    simp only [Set.image_image, Function.comp_apply, projectionZ_embedYZ]

theorem projectionZ_centered_axis0 :
    projectionZ '' (centeredBody (axis 0) : Set ThreeSpace) = centeredSegment (1, 0) := by
  first
  | rw [centeredBody_carrier, centeredSegment_eq_image, Set.image_image]
    congr 1
    funext t
    simp [Function.comp_apply, map_smul, axis, projectionZ_apply, Pi.single_apply]

theorem IsCalibratedTuple.projectionZ_last {K : Fin 9 → Body 3}
    (hK : IsCalibratedTuple K) (lam : ℝ) :
    projectionZ '' (lam • (K ShapeConditions.bodyC : Set ThreeSpace) +
      (K ShapeConditions.e₁ : Set ThreeSpace)) = lastProjectedSet lam (planarC K) := by
  first
  | have haxis := hK.segments 0
    change K ShapeConditions.e₁ = centeredBody (axis 0) at haxis
    rw [haxis, Set.image_add projectionZ,
      Set.image_smul_comm projectionZ lam _ (fun x => projectionZ.map_smul lam x),
      hK.projectionZC, projectionZ_centered_axis0]
    change lam • (transport20 '' (planarC K : Set Plane)) + centeredSegment (1, 0) = _
    rw [add_comm]
    congr 1
    rw [← Set.image_smul, Set.image_image]
    rfl

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ShapeProjectionGeometry.lean -/

/- BEGIN SOURCE: VolumePolynomials/ShapeProjectionEvaluation.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

variable {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K)

include hK

theorem IsCalibratedTuple.extrusion_axisA :
    extrusionValue (volumeFunction K) (unitWeight bodyA) e₃ = volume.real (planarA K : Set Plane) := by
  first
  | have hs : K e₃ = centeredBody (axis 2) := hK.segments 2
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyA), weightedSum_unitWeight,
      hs, bodyExtrusion_axis]
    rfl

theorem IsCalibratedTuple.extrusion_axisB :
    extrusionValue (volumeFunction K) (unitWeight bodyB) e₂ = volume.real (planarB K : Set Plane) := by
  first
  | have hs : K e₂ = centeredBody (axis 1) := hK.segments 1
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyB), weightedSum_unitWeight,
      hs, bodyExtrusion_axis]
    rfl

theorem IsCalibratedTuple.extrusion_axisC :
    extrusionValue (volumeFunction K) (unitWeight bodyC) e₁ = volume.real (planarC K : Set Plane) := by
  first
  | have hs : K e₁ = centeredBody (axis 0) := hK.segments 0
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyC), weightedSum_unitWeight,
      hs, bodyExtrusion_axis]
    rfl

theorem IsCalibratedTuple.extrusion_VA :
    extrusionValue (volumeFunction K) (unitWeight bodyA) sᵥ = volume.real (planarA K : Set Plane) := by
  first
  | have hs : K sᵥ = centeredBody directionV := hK.segments 3
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyA), weightedSum_unitWeight,
      hs, bodyExtrusion_V, hK.projectionVA]

theorem IsCalibratedTuple.extrusion_VB :
    extrusionValue (volumeFunction K) (unitWeight bodyB) sᵥ =
      volume.real (transport01 '' (planarB K : Set Plane)) := by
  first
  | have hs : K sᵥ = centeredBody directionV := hK.segments 3
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyB), weightedSum_unitWeight,
      hs, bodyExtrusion_V, hK.projectionVB]

theorem IsCalibratedTuple.extrusion_VAB :
    extrusionValue (volumeFunction K) (unitWeight bodyA + unitWeight bodyB) sᵥ =
      volume.real ((planarA K : Set Plane) + transport01 '' (planarB K : Set Plane)) := by
  first
  | have hs : K sᵥ = centeredBody directionV := hK.segments 3
    rw [extrusionValue_volume K (unitWeight bodyA + unitWeight bodyB) sᵥ
      (fun i => add_nonneg (unitWeight_nonneg bodyA i) (unitWeight_nonneg bodyB i)),
      weightedSum_two, hs, bodyExtrusion_V, ConvexBody.coe_add, Set.image_add projectionV,
      hK.projectionVA, hK.projectionVB]

theorem IsCalibratedTuple.extrusion_WB :
    extrusionValue (volumeFunction K) (unitWeight bodyB) s𝓌 = volume.real (planarB K : Set Plane) := by
  first
  | have hs : K s𝓌 = centeredBody directionW := hK.segments 4
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyB), weightedSum_unitWeight,
      hs, bodyExtrusion_W, hK.projectionWB]

theorem IsCalibratedTuple.extrusion_WC :
    extrusionValue (volumeFunction K) (unitWeight bodyC) s𝓌 =
      volume.real (transport12 '' (planarC K : Set Plane)) := by
  first
  | have hs : K s𝓌 = centeredBody directionW := hK.segments 4
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyC), weightedSum_unitWeight,
      hs, bodyExtrusion_W, hK.projectionWC]

theorem IsCalibratedTuple.extrusion_WBC :
    extrusionValue (volumeFunction K) (unitWeight bodyB + unitWeight bodyC) s𝓌 =
      volume.real ((planarB K : Set Plane) + transport12 '' (planarC K : Set Plane)) := by
  first
  | have hs : K s𝓌 = centeredBody directionW := hK.segments 4
    rw [extrusionValue_volume K (unitWeight bodyB + unitWeight bodyC) s𝓌
      (fun i => add_nonneg (unitWeight_nonneg bodyB i) (unitWeight_nonneg bodyC i)),
      weightedSum_two, hs, bodyExtrusion_W, ConvexBody.coe_add, Set.image_add projectionW,
      hK.projectionWB, hK.projectionWC]

theorem IsCalibratedTuple.extrusion_ZA :
    extrusionValue (volumeFunction K) (unitWeight bodyA) s𝓏 = volume.real (planarA K : Set Plane) := by
  first
  | have hs : K s𝓏 = centeredBody directionZ := hK.segments 5
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyA), weightedSum_unitWeight,
      hs, bodyExtrusion_Z, hK.projectionZA]

theorem IsCalibratedTuple.extrusion_ZD (lam : ℝ) (hlam : 0 ≤ lam) :
    extrusionValue (volumeFunction K) (lastNumericalWeight lam) s𝓏 =
      volume.real (lastProjectedSet lam (planarC K)) := by
  first
  | have hs : K s𝓏 = centeredBody directionZ := hK.segments 5
    rw [extrusionValue_volume K _ _ (lastNumericalWeight_nonneg lam hlam),
      weightedSum_last K lam hlam, hs, bodyExtrusion_Z,
      ConvexBody.coe_add, ConvexBody.coe_smul, hK.projectionZ_last]

theorem IsCalibratedTuple.extrusion_ZAD (lam : ℝ) (hlam : 0 ≤ lam) :
    extrusionValue (volumeFunction K) (unitWeight bodyA + lastNumericalWeight lam) s𝓏 =
      volume.real ((planarA K : Set Plane) + lastProjectedSet lam (planarC K)) := by
  first
  | have hs : K s𝓏 = centeredBody directionZ := hK.segments 5
    rw [extrusionValue_volume K (unitWeight bodyA + lastNumericalWeight lam) s𝓏
      (fun i => add_nonneg (unitWeight_nonneg bodyA i)
        (lastNumericalWeight_nonneg lam hlam i)),
      weightedSum_add K (unitWeight bodyA) (lastNumericalWeight lam)
        (unitWeight_nonneg bodyA) (lastNumericalWeight_nonneg lam hlam),
      weightedSum_unitWeight, weightedSum_last K lam hlam, hs, bodyExtrusion_Z,
      ConvexBody.coe_add, Set.image_add projectionZ, hK.projectionZA,
      ConvexBody.coe_add, ConvexBody.coe_smul, hK.projectionZ_last]

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 6
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ShapeProjectionEvaluation.lean -/

/- BEGIN SOURCE: VolumePolynomials/NormalizedShape.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

/-- Every calibrated realization of the finite rational conditions has exactly
the forced planar shape, in all three coordinate planes. The hypotheses here
are literal ordinary volumes, and every equality-case input is derived below. -/
theorem calibrated_conditions_force_shape (lam a : ℝ) (K : Fin 9 → Body 3)
    (hK : IsCalibratedTuple K)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1), ∃ a₀ b₀ c₀ : Plane,
      (K bodyA : Set ThreeSpace) =
        embedXY a₀ +ᵥ embedXY '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) ∧
      (K bodyB : Set ThreeSpace) =
        embedXZ b₀ +ᵥ embedXZ ''
          (transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane)) ∧
      (K bodyC : Set ThreeSpace) =
        embedYZ c₀ +ᵥ embedYZ ''
          (transport12 '' (transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane))) ∧
      a = volume.real (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
  first
  | haveI : (volume : Measure Plane).IsAddHaarMeasure := by
      change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
      exact Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    rcases hcond with ⟨hseg, ⟨hframe, hv0, hv1, hv2, hw0, hw1, hw2,
      hz0, hz1, hz2, hvwz, hplaneA, hplaneB, hplaneC,
      hAB, hABsum, hBC, hBCsum, hAD, hADsum, ha⟩,
      ⟨hlam₀, hlam₁, hApos, hBpos, hCpos, hVApos, hWBpos, hZApos⟩⟩
    rw [hK.extrusion_axisA] at hApos ha
    rw [hK.extrusion_axisB] at hBpos
    rw [hK.extrusion_VA, hK.extrusion_VB] at hAB
    rw [hK.extrusion_VAB, hK.extrusion_VA] at hABsum
    rw [hK.extrusion_WB, hK.extrusion_WC] at hBC
    rw [hK.extrusion_WBC, hK.extrusion_WB] at hBCsum
    rw [hK.extrusion_ZA, hK.extrusion_ZD lam hlam₀.le] at hAD
    rw [hK.extrusion_ZAD lam hlam₀.le, hK.extrusion_ZA] at hADsum
    obtain ⟨a₀, b₀, c₀, hA, hB, hC⟩ := projected_comparisons_force_shape lam hlam₀.le hlam₁
      (planarA K) (planarB K) (planarC K)
      (planarA K).isCompact (planarA K).convex
      (planarB K).isCompact (planarB K).convex
      (planarC K).isCompact (planarC K).convex
      hApos hAB.symm hABsum hBpos hBC.symm hBCsum hAD.symm hADsum
    refine ⟨hlam₀, hlam₁, a₀, b₀, c₀, ?_, ?_, ?_, ?_⟩
    · rw [hK.placeA, hA, linear_image_vadd]
    · rw [hK.placeB, hB, linear_image_vadd]
    · rw [hK.placeC, hC, linear_image_vadd]
    · rw [ha, hA]
      simp only [Measure.real, measure_vadd]


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 6
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/NormalizedShape.lean -/

/- BEGIN SOURCE: VolumePolynomials/MinkowskiSeriesMaps.lean -/
section


@[expose] public section
noncomputable section

open Set

namespace VolumePolynomials

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem summable_norm_linear_image (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) : Summable (fun n => ‖f (u n)‖) := by
  first
  | apply (hu.mul_left ‖f‖).of_norm_bounded
    intro n
    rw [norm_norm]
    exact f.le_opNorm (u n)

theorem map_seriesPoint (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) (t : SegmentChoice) :
    f (seriesPoint u t) = seriesPoint (fun n => f (u n)) t := by
  first
  | rw [seriesPoint, f.map_tsum (series_summable u hu t)]
    simp only [map_smul, seriesPoint]

theorem image_segmentSeries (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) :
    f '' segmentSeries u = segmentSeries (fun n => f (u n)) := by
  first
  | ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (map_seriesPoint f u hu t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨seriesPoint u t, ⟨t, rfl⟩, map_seriesPoint f u hu t⟩

theorem map_segmentSeriesBody (f : E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖)) :
    mapBody f (segmentSeriesBody u hu) =
      segmentSeriesBody (fun n => f (u n)) (summable_norm_linear_image f u hu) := by
  first
  | apply ConvexBody.ext
    exact image_segmentSeries f u hu

def oneTermSequence (v : E) (n : ℕ) : E := if n = 0 then v else 0

theorem oneTermSequence_summable (v : E) :
    Summable (fun n => ‖oneTermSequence v n‖) := by
  first
  | simpa only [oneTermSequence, apply_ite, norm_zero] using
      (hasSum_ite_eq (0 : ℕ) ‖v‖).summable

theorem seriesPoint_oneTermSequence (v : E) (t : SegmentChoice) :
    seriesPoint (oneTermSequence v) t = (t 0 : ℝ) • v := by
  first
  | simp [seriesPoint, oneTermSequence, smul_ite]

theorem segmentSeries_oneTermSequence (v : E) :
    segmentSeries (oneTermSequence v) = centeredSegment v := by
  first
  | ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t 0, seriesPoint_oneTermSequence v t⟩
    · rintro ⟨a, rfl⟩
      exact ⟨fun _ => a, seriesPoint_oneTermSequence v (fun _ => a)⟩

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MinkowskiSeriesMaps.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteZonotope.lean -/
section


@[expose] public section

/-!
# Finite zonotopes and their planar area polynomials

The generic carrier is a literal finite Minkowski sum of centered segments.
Labels may repeat: this allows many generating segments to carry the same body
variable. The planar polynomial is proved from the exact area identity.
-/

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped Pointwise

namespace VolumePolynomials.FiniteZonotope

variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]

def segment (v : E) : Set E :=
  (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2)

def carrier : List E → Set E
  | [] => {0}
  | v :: vs => carrier vs + segment v

def weightedCarrier (t : ι → ℝ) (vs : List (ι × E)) : Set E :=
  carrier (vs.map (fun p => t p.1 • p.2))

@[simp] theorem segment_zero : segment (0 : E) = {0} := by
  ext x
  simp only [segment, Set.mem_image, smul_zero, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rfl
  · intro hx
    subst x
    exact ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem zero_mem_segment (v : E) : (0 : E) ∈ segment v := by
  exact ⟨0, ⟨by norm_num, by norm_num⟩, zero_smul ℝ v⟩

theorem zero_mem_carrier (vs : List E) : (0 : E) ∈ carrier vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => exact ⟨0, ih, 0, zero_mem_segment v, zero_add 0⟩

@[simp] theorem carrier_singleton (v : E) : carrier [v] = segment v := by
  simp [carrier, Set.singleton_zero]

theorem carrier_append (xs ys : List E) :
    carrier (xs ++ ys) = carrier xs + carrier ys := by
  induction xs with
  | nil => simp [carrier, Set.singleton_zero]
  | cons v xs ih => simp [carrier, ih, add_assoc, add_comm, add_left_comm]

theorem carrier_range_succ (u : ℕ → E) (N : ℕ) :
    carrier ((List.range (N + 1)).map u) =
      carrier ((List.range N).map u) + segment (u N) := by
  simp [List.range_succ, List.map_append, carrier_append]

@[simp] theorem weightedCarrier_cons (t : ι → ℝ) (p : ι × E) (vs : List (ι × E)) :
    weightedCarrier t (p :: vs) = weightedCarrier t vs + segment (t p.1 • p.2) := rfl

section Image

variable [AddCommGroup F] [Module ℝ F]

theorem image_segment (L : E →ₗ[ℝ] F) (v : E) : L '' segment v = segment (L v) := by
  simp only [segment, Set.image_image, map_smul, Function.comp_def]

theorem image_carrier (L : E →ₗ[ℝ] F) (vs : List E) :
    L '' carrier vs = carrier (vs.map L) := by
  induction vs with
  | nil => simp [carrier]
  | cons v vs ih =>
      simp only [carrier, List.map_cons, Set.image_add L, ih, image_segment]

theorem image_weightedCarrier (L : E →ₗ[ℝ] F) (t : ι → ℝ) (vs : List (ι × E)) :
    L '' weightedCarrier t vs =
      weightedCarrier t (vs.map (fun p => (p.1, L p.2))) := by
  simp only [weightedCarrier, image_carrier, List.map_map, Function.comp_def, map_smul]

end Image

theorem smul_carrier (a : ℝ) (vs : List E) :
    a • carrier vs = carrier (vs.map (fun v => a • v)) := by
  exact image_carrier (a • (LinearMap.id : E →ₗ[ℝ] E)) vs

theorem weightedCarrier_append (t : ι → ℝ) (xs ys : List (ι × E)) :
    weightedCarrier t (xs ++ ys) = weightedCarrier t xs + weightedCarrier t ys := by
  simp only [weightedCarrier, List.map_append, carrier_append]

theorem weightedCarrier_constantLabel (t : ι → ℝ) (i : ι) (vs : List E) :
    weightedCarrier t (vs.map (fun v => (i, v))) = t i • carrier vs := by
  simp only [weightedCarrier, List.map_map, Function.comp_def, smul_carrier]

def labelled (vs : ι → List E) : List ι → List (ι × E)
  | [] => []
  | i :: is => (vs i).map (fun v => (i, v)) ++ labelled vs is

theorem weightedCarrier_labelled (vs : ι → List E) (is : List ι) (t : ι → ℝ) :
    weightedCarrier t (labelled vs is) =
      (is.map (fun i => t i • carrier (vs i))).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [labelled, weightedCarrier_append, weightedCarrier_constantLabel, ih,
        List.map_cons, List.sum_cons]

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem segment_compact (v : E) : IsCompact (segment v) :=
  isCompact_Icc.image (continuous_id.smul continuous_const)

theorem carrier_compact (vs : List E) : IsCompact (carrier vs) := by
  induction vs with
  | nil => exact isCompact_singleton
  | cons v vs ih => exact ih.add (segment_compact v)

end Topology

theorem segment_convex (v : E) : Convex ℝ (segment v) :=
  (convex_Icc _ _).linear_image (LinearMap.toSpanSingleton ℝ E v)

theorem carrier_convex (vs : List E) : Convex ℝ (carrier vs) := by
  induction vs with
  | nil => exact convex_singleton 0
  | cons v vs ih => exact ih.add (segment_convex v)

section Planar

open PlanarExtrusion

theorem planar_carrier (vs : List Plane) : carrier vs = zonotope vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [carrier, zonotope, ih, segment, PlanarExtrusion.centeredSegment]

def widthPolynomial (v : Plane) : List (ι × Plane) → MvPolynomial ι ℝ
  | [] => 0
  | (i, w) :: ws => C |determinant v w| * X i + widthPolynomial v ws

def areaPolynomial : List (ι × Plane) → MvPolynomial ι ℝ
  | [] => 0
  | (i, v) :: vs => areaPolynomial vs + X i * widthPolynomial v vs

theorem widthPolynomial_homogeneous (v : Plane) (vs : List (ι × Plane)) :
    (widthPolynomial v vs).IsHomogeneous 1 := by
  induction vs with
  | nil => exact isHomogeneous_zero (σ := ι) (R := ℝ) 1
  | cons p vs ih =>
      obtain ⟨i, w⟩ := p
      exact ((isHomogeneous_C (σ := ι) _).mul (isHomogeneous_X (R := ℝ) i)).add ih

theorem areaPolynomial_homogeneous (vs : List (ι × Plane)) :
    (areaPolynomial vs).IsHomogeneous 2 := by
  induction vs with
  | nil => exact isHomogeneous_zero (σ := ι) (R := ℝ) 2
  | cons p vs ih =>
      obtain ⟨i, v⟩ := p
      exact ih.add ((isHomogeneous_X (R := ℝ) i).mul (widthPolynomial_homogeneous v vs))

theorem widthPolynomial_eval (t : ι → ℝ) (v : Plane) (vs : List (ι × Plane)) :
    eval t (widthPolynomial v vs) =
      (vs.map (fun p => t p.1 * |determinant v p.2|)).sum := by
  induction vs with
  | nil => simp [widthPolynomial]
  | cons p vs ih =>
      obtain ⟨i, w⟩ := p
      simp [widthPolynomial, ih, mul_comm]

theorem determinant_smul (s t : ℝ) (v w : Plane) :
    determinant (s • v) (t • w) = s * t * determinant v w := by
  simp only [determinant, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem areaPolynomial_eval (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (vs : List (ι × Plane)) :
    eval t (areaPolynomial vs) =
      pairArea (vs.map (fun p => t p.1 • p.2)) := by
  induction vs with
  | nil => simp [areaPolynomial, pairArea]
  | cons p vs ih =>
      obtain ⟨i, v⟩ := p
      simp only [areaPolynomial, eval_add, eval_mul, eval_X, ih,
        List.map_cons, pairArea, widthPolynomial_eval, List.map_map, Function.comp_def]
      congr 1
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [determinant_smul, abs_mul, abs_mul, abs_of_nonneg (ht i),
        abs_of_nonneg (ht p.1)]
      ring

/-- Literal planar volume is a homogeneous quadratic for every labelled finite
family of generating segments and all nonnegative variable assignments. -/
theorem areaPolynomial_realizes (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (vs : List (ι × Plane)) :
    eval t (areaPolynomial vs) = volume.real (weightedCarrier t vs) := by
  rw [weightedCarrier, planar_carrier, area_zonotope, areaPolynomial_eval t ht]

end Planar

end VolumePolynomials.FiniteZonotope
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteZonotope.lean -/

/- BEGIN SOURCE: VolumePolynomials/ZonotopePolynomial3.lean -/
section


@[expose] public section

/-!
# Genuine volume polynomials for arbitrary finite three-dimensional zonotopes

The proof constructs a homogeneous cubic from actual product-coordinate
extrusion and actual planar zonotope area. Generators may be zero, repeated, or
linearly dependent. Labels may repeat. In particular this proves existence for
an arbitrary finite tuple of finite zonotopes, with every nonnegative real
weight simultaneously quantified.
-/

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.FiniteZonotope

open PlanarExtrusion ProductExtrusion

abbrev ThreeSpace := Fin 3 → ℝ

/-- Reflection of the first product coordinate. -/
def reverseAxisLinear : (ℝ × Plane) ≃ₗ[ℝ] ℝ × Plane where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' c p := by ext <;> simp

def reverseAxis : (ℝ × Plane) ≃L[ℝ] ℝ × Plane :=
  reverseAxisLinear.toContinuousLinearEquiv

theorem reverseAxis_measurePreserving : MeasurePreserving reverseAxis volume volume := by
  first
  | exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure Plane))

/-- Every nonzero direction has positive axial length in a volume-preserving
product frame. This is proved by extracting a nonzero coordinate, shearing the
other two coordinates, and, when needed, reflecting the first coordinate. -/
theorem exists_positive_frame (v : ThreeSpace) (hv : v ≠ 0) :
    ∃ (c : ℝ), 0 < c ∧ ∃ T : ThreeSpace ≃L[ℝ] (ℝ × Plane),
      MeasurePreserving T volume volume ∧ T v = (c, 0) := by
  first
  | have hcoord : ∃ i, v i ≠ 0 := by
      by_contra h
      apply hv
      funext i
      exact not_not.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hcoord
    let u : Plane := (v i)⁻¹ • (v (i.succAbove 0), v (i.succAbove 1))
    let S := Holonomy.projectionFrame i u
    have hS : MeasurePreserving S volume volume := Holonomy.projectionFrame_measurePreserving i u
    have hSv : S v = (v i, 0) := by
      simp only [S, Holonomy.projectionFrame_apply, u, smul_smul, mul_inv_cancel₀ hi,
        one_smul, sub_self]
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · refine ⟨-v i, neg_pos.mpr hneg, S.trans reverseAxis, ?_, ?_⟩
      · exact reverseAxis_measurePreserving.comp hS
      · change reverseAxis (S v) = (-v i, 0)
        rw [hSv]
        rfl
    · exact ⟨v i, hpos, S, hS, hSv⟩

/-- An actual homogeneous cubic exists for the volume of every labelled finite
three-dimensional zonotope. -/
theorem exists_volumePolynomial {ι : Type*} (vs : List (ι × ThreeSpace)) :
    ∃ p : MvPolynomial ι ℝ, p.IsHomogeneous 3 ∧
      ∀ t : ι → ℝ, (∀ i, 0 ≤ t i) →
        eval t p = volume.real (weightedCarrier t vs) := by
  first
  | induction vs with
    | nil =>
        refine ⟨0, isHomogeneous_zero (σ := ι) (R := ℝ) 3, ?_⟩
        intro t ht
        simp [weightedCarrier, carrier, measureReal_def]
    | cons a vs ih =>
        obtain ⟨i, v⟩ := a
        obtain ⟨p, hp, hpval⟩ := ih
        by_cases hv : v = 0
        · subst v
          refine ⟨p, hp, ?_⟩
          intro t ht
          simpa [weightedCarrier_cons, segment_zero, Set.singleton_zero]
            using hpval t ht
        · obtain ⟨c, hc, T, hT, hTv⟩ := exists_positive_frame v hv
          let P : ThreeSpace →ₗ[ℝ] Plane := (LinearMap.snd ℝ ℝ Plane).comp T.toLinearMap
          let projected : List (ι × Plane) := vs.map (fun a => (a.1, P a.2))
          let q : MvPolynomial ι ℝ := areaPolynomial projected
          have hq : q.IsHomogeneous 2 := areaPolynomial_homogeneous projected
          refine ⟨p + (C c * X i) * q, ?_, ?_⟩
          · exact hp.add (((isHomogeneous_C (σ := ι) c).mul
              (isHomogeneous_X (R := ℝ) i)).mul hq)
          · intro t ht
            have hproj : projection (T '' weightedCarrier t vs) =
                weightedCarrier t projected := by
              rw [projection, Set.image_image]
              exact image_weightedCarrier P t vs
            have hscaled : T (t i • v) = (t i * c, 0) := by
              simp only [map_smul, hTv, Prod.smul_mk, smul_eq_mul, smul_zero]
            have hvol : volume.real (weightedCarrier t ((i, v) :: vs)) =
                volume.real (weightedCarrier t vs) +
                  (t i * c) * volume.real (weightedCarrier t projected) := by
              change volume.real (weightedCarrier t vs +
                (fun s : ℝ => s • (t i • v)) '' Icc (-(1 / 2 : ℝ)) (1 / 2)) = _
              rw [realVolume_add_centered_segment_nonneg (C := weightedCarrier t vs) T hT
                (carrier_compact _) (carrier_convex _) hscaled (mul_nonneg (ht i) hc.le), hproj]
            rw [eval_add, eval_mul, eval_mul, eval_C, eval_X, hpval t ht]
            change volume.real (weightedCarrier t vs) + (c * t i) *
              eval t (areaPolynomial projected) = _
            rw [areaPolynomial_realizes t ht, hvol]
            ring

/-- The convex body associated to a finite list of generators. -/
def toBody (vs : List ThreeSpace) : Body 3 :=
  ⟨carrier vs, carrier_convex vs, carrier_compact vs, ⟨0, zero_mem_carrier vs⟩⟩

@[simp] theorem coe_toBody (vs : List ThreeSpace) :
    (toBody vs : Set ThreeSpace) = carrier vs := rfl

theorem weightedSum_toBody {n : ℕ} (vs : Fin n → List ThreeSpace) (t : Fin n → ℝ) :
    (weightedSum (fun i => toBody (vs i)) t : Set ThreeSpace) =
      weightedCarrier t (labelled vs (List.finRange n)) := by
  first
  | rw [weightedSum, coe_sum_body, weightedCarrier_labelled, ← Fin.sum_univ_def]
    simp only [ConvexBody.coe_smul, coe_toBody]

/-- Every tuple of finite three-dimensional zonotopes has a genuine volume
polynomial in the paper's complete coefficient convention. -/
theorem exists_realizes {n : ℕ} (vs : Fin n → List ThreeSpace) :
    ∃ c : Coefficients n 3, Realizes (fun i => toBody (vs i)) c := by
  first
  | obtain ⟨p, hp, hvol⟩ := exists_volumePolynomial (labelled vs (List.finRange n))
    refine ⟨coefficientsOfPolynomial p, realizes_of_homogeneous_polynomial _ p hp ?_⟩
    intro t ht
    change eval t p = volume.real (weightedSum (fun i => toBody (vs i)) t : Set ThreeSpace)
    rw [weightedSum_toBody]
    exact hvol t ht

end VolumePolynomials.FiniteZonotope
end -- closes the original EOF section from source line 22
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ZonotopePolynomial3.lean -/

/- BEGIN SOURCE: VolumePolynomials/MinkowskiSeriesLimits.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology Pointwise
open Set Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def prefixPoint (u : ℕ → E) (N : ℕ) (t : SegmentChoice) : E :=
  ∑ n ∈ Finset.range N, (t n : ℝ) • u n

def prefixSeries (u : ℕ → E) (N : ℕ) : Set E := Set.range (prefixPoint u N)

theorem prefixPoint_continuous (u : ℕ → E) (N : ℕ) : Continuous (prefixPoint u N) := by
  first
  | apply continuous_finsetSum
    intro n hn
    exact ((continuous_apply n).subtype_val).smul continuous_const

theorem prefixSeries_isCompact (u : ℕ → E) (N : ℕ) : IsCompact (prefixSeries u N) :=
  isCompact_range (prefixPoint_continuous u N)

theorem zero_mem_prefixSeries (u : ℕ → E) (N : ℕ) : (0 : E) ∈ prefixSeries u N := by
  first
  | refine ⟨fun _ => ⟨0, by constructor <;> norm_num⟩, ?_⟩
    simp [prefixPoint]

theorem prefixSeries_convex (u : ℕ → E) (N : ℕ) : Convex ℝ (prefixSeries u N) := by
  first
  | intro x hx y hy a b ha hb hab
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    let w : SegmentChoice := fun n =>
      ⟨a * (s n : ℝ) + b * (t n : ℝ), by
        change a • (s n : ℝ) + b • (t n : ℝ) ∈ Icc (- (1/2 : ℝ)) (1/2 : ℝ)
        exact (convex_Icc (𝕜 := ℝ) (- (1/2 : ℝ)) (1/2 : ℝ))
          (s n).property (t n).property ha hb hab⟩
    refine ⟨w, ?_⟩
    simp [prefixPoint, w, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

def prefixBody (u : ℕ → E) (N : ℕ) : ConvexBody E where
  carrier := prefixSeries u N
  convex' := prefixSeries_convex u N
  isCompact' := prefixSeries_isCompact u N
  nonempty' := ⟨0, zero_mem_prefixSeries u N⟩

def truncatedChoice (N : ℕ) (t : SegmentChoice) : SegmentChoice :=
  fun n => if n < N then t n else ⟨0, by constructor <;> norm_num⟩

theorem seriesPoint_truncated (u : ℕ → E) (N : ℕ) (t : SegmentChoice) :
    seriesPoint u (truncatedChoice N t) = prefixPoint u N t := by
  first
  | unfold seriesPoint
    rw [tsum_eq_sum (s := Finset.range N) (by
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [truncatedChoice, hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [truncatedChoice, Finset.mem_range.mp hn]

theorem prefixSeries_subset (u : ℕ → E) (N : ℕ) : prefixSeries u N ⊆ segmentSeries u := by
  first
  | rintro x ⟨t, rfl⟩
    exact ⟨truncatedChoice N t, seriesPoint_truncated u N t⟩

theorem prefixPoint_succ (u : ℕ → E) (N : ℕ) (t : SegmentChoice) :
    prefixPoint u (N + 1) t = prefixPoint u N t + (t N : ℝ) • u N := by
  first
  | exact Finset.sum_range_succ _ _

theorem prefixPoint_update (u : ℕ → E) (N : ℕ) (t : SegmentChoice)
    (a : Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :
    prefixPoint u N (Function.update t N a) = prefixPoint u N t := by
  first
  | classical
    apply Finset.sum_congr rfl
    intro n hn
    rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hn))]

theorem prefixSeries_zero (u : ℕ → E) : prefixSeries u 0 = {0} := by
  first
  | ext x
    constructor
    · rintro ⟨t, rfl⟩
      simp [prefixPoint]
    · intro hx
      have hxzero : x = 0 := Set.mem_singleton_iff.mp hx
      rw [hxzero]
      exact zero_mem_prefixSeries u 0

theorem prefixSeries_succ (u : ℕ → E) (N : ℕ) :
    prefixSeries u (N + 1) = prefixSeries u N + centeredSegment (u N) := by
  first
  | classical
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact Set.mem_add.mpr ⟨prefixPoint u N t, ⟨t, rfl⟩, (t N : ℝ) • u N,
        ⟨t N, rfl⟩, (prefixPoint_succ u N t).symm⟩
    · intro hx
      obtain ⟨y, ⟨t, rfl⟩, z, ⟨a, rfl⟩, rfl⟩ := Set.mem_add.mp hx
      refine ⟨Function.update t N a, ?_⟩
      rw [prefixPoint_succ, prefixPoint_update]
      simp

def seriesTailBound (u : ℕ → E) (N : ℕ) : ℝ :=
  (1/2 : ℝ) * ∑' k, ‖u (k + N)‖

theorem seriesTailBound_nonneg (u : ℕ → E) (N : ℕ) : 0 ≤ seriesTailBound u N := by
  first
  | apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun _ => norm_nonneg _)

theorem seriesTailBound_tendsto (u : ℕ → E) : Tendsto (seriesTailBound u) atTop (𝓝 0) := by
  first
  | change Tendsto (fun N => (1/2 : ℝ) * ∑' k, ‖u (k + N)‖) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_sum_nat_add (fun n => ‖u n‖)).const_mul (1/2 : ℝ)

theorem seriesPoint_sub_prefix (u : ℕ → E) (hu : Summable fun n => ‖u n‖)
    (N : ℕ) (t : SegmentChoice) :
    seriesPoint u t - prefixPoint u N t = ∑' k, (t (k + N) : ℝ) • u (k + N) := by
  first
  | have hs := (series_summable u hu t).sum_add_tsum_nat_add N
    unfold seriesPoint prefixPoint
    rw [← hs]
    simp

theorem seriesPoint_dist_prefix_le (u : ℕ → E) (hu : Summable fun n => ‖u n‖)
    (N : ℕ) (t : SegmentChoice) :
    dist (seriesPoint u t) (prefixPoint u N t) ≤ seriesTailBound u N := by
  first
  | rw [dist_eq_norm, seriesPoint_sub_prefix u hu N t]
    have htail : Summable (fun k => ‖u (k + N)‖) := (summable_nat_add_iff N).mpr hu
    have hbound := tsum_of_norm_bounded (htail.mul_left (1/2)).hasSum
      (fun k => series_term_norm_le u t (k + N))
    simpa only [tsum_mul_left, seriesTailBound] using hbound

/-- Quantitative Hausdorff convergence, for the actual compact convex finite and infinite sums. -/
theorem prefixBody_dist_le (u : ℕ → E) (hu : Summable fun n => ‖u n‖) (N : ℕ) :
    dist (prefixBody u N) (segmentSeriesBody u hu) ≤ seriesTailBound u N := by
  first
  | change hausdorffDist (prefixSeries u N) (segmentSeries u) ≤ seriesTailBound u N
    apply hausdorffDist_le_of_mem_dist (seriesTailBound_nonneg u N)
    · intro x hx
      exact ⟨x, prefixSeries_subset u N hx, by simpa using seriesTailBound_nonneg u N⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨prefixPoint u N t, ⟨t, rfl⟩, seriesPoint_dist_prefix_le u hu N t⟩

theorem prefixBody_tendsto (u : ℕ → E) (hu : Summable fun n => ‖u n‖) :
    Tendsto (prefixBody u) atTop (𝓝 (segmentSeriesBody u hu)) := by
  first
  | apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (prefixBody_dist_le u hu) (seriesTailBound_tendsto u)

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MinkowskiSeriesLimits.lean -/

/- BEGIN SOURCE: VolumePolynomials/ZonoidRealization3.lean -/
section


@[expose] public section

/-!
# Volume polynomials for arbitrary summable segment-series tuples in three dimensions

Finite prefixes are actual finite zonotopes. Their homogeneous volume polynomials
pass to the Hausdorff limit through the closed finite-dimensional evaluation
range. No coefficient-series formula, mixed-volume axiom, or general Minkowski
polynomial theorem is assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials

theorem prefixSeries_eq_finiteCarrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : ℕ → E) (N : ℕ) :
    prefixSeries u N = FiniteZonotope.carrier ((List.range N).map u) := by
  first
  | induction N with
    | zero => rw [prefixSeries_zero]; rfl
    | succ N ih =>
        have hsegment : centeredSegment (u N) = FiniteZonotope.segment (u N) :=
          centeredSegment_eq_image (u N)
        rw [prefixSeries_succ, FiniteZonotope.carrier_range_succ, ih, hsegment]

theorem prefixBody_eq_finiteBody (u : ℕ → Space 3) (N : ℕ) :
    prefixBody u N = FiniteZonotope.toBody ((List.range N).map u) := by
  first
  | apply ConvexBody.ext
    exact prefixSeries_eq_finiteCarrier u N

/-- Every finite tuple of summable three-dimensional segment series has a full
homogeneous cubic volume polynomial with the paper's exact geometric semantics. -/
theorem summable_segment_series_realizes {n : ℕ} (u : Fin n → ℕ → Space 3)
    (hu : ∀ i, Summable (fun j => ‖u i j‖)) :
    ∃ c : Coefficients n 3, Realizes (fun i => segmentSeriesBody (u i) (hu i)) c := by
  first
  | apply exists_realizes_of_tendsto (l := (Filter.atTop : Filter ℕ))
      (L := fun (N : ℕ) i => prefixBody (u i) N)
    · exact tendsto_pi_nhds.mpr (fun i => prefixBody_tendsto (u i) (hu i))
    · apply Filter.Eventually.of_forall
      intro N
      simpa only [prefixBody_eq_finiteBody] using
        FiniteZonotope.exists_realizes (fun i => (List.range N).map (u i))

end VolumePolynomials
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ZonoidRealization3.lean -/

/- BEGIN SOURCE: VolumePolynomials/CanonicalShapeTuple.lean -/
section


@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

/-- The three plane embeddings with the transport coordinates built in. -/
def placedA : Plane →L[ℝ] ThreeSpace := embedXY
def placedB : Plane →L[ℝ] ThreeSpace := embedXZ.comp transport01.toContinuousLinearMap
def placedC : Plane →L[ℝ] ThreeSpace :=
  embedYZ.comp (transport12.toContinuousLinearMap.comp transport01.toContinuousLinearMap)

/-- The nine bodies in the constructive half of Theorem 1.2. -/
def canonicalTuple (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) : Fin 9 → Body 3 :=
  ![centeredBody (axis 0), centeredBody (axis 1), centeredBody (axis 2),
    centeredBody directionV, centeredBody directionW, centeredBody directionZ,
    mapBody placedA (forcedBody lam hlam₀ hlam₁),
    mapBody placedB (forcedBody lam hlam₀ hlam₁),
    mapBody placedC (forcedBody lam hlam₀ hlam₁)]

/-- All nine entries have honest summable segment representations. -/
def canonicalGenerators (lam : ℝ) : Fin 9 → ℕ → ThreeSpace :=
  ![oneTermSequence (axis 0), oneTermSequence (axis 1), oneTermSequence (axis 2),
    oneTermSequence directionV, oneTermSequence directionW, oneTermSequence directionZ,
    fun n => placedA (weightedOrbit lam n),
    fun n => placedB (weightedOrbit lam n),
    fun n => placedC (weightedOrbit lam n)]

theorem canonicalGenerators_summable (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (i : Fin 9) : Summable (fun n => ‖canonicalGenerators lam i n‖) := by
  first
  | fin_cases i
    · exact oneTermSequence_summable (axis 0)
    · exact oneTermSequence_summable (axis 1)
    · exact oneTermSequence_summable (axis 2)
    · exact oneTermSequence_summable directionV
    · exact oneTermSequence_summable directionW
    · exact oneTermSequence_summable directionZ
    · exact summable_norm_linear_image placedA (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact summable_norm_linear_image placedB (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact summable_norm_linear_image placedC (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)

theorem segmentSeriesBody_oneTermSequence (v : ThreeSpace) :
    segmentSeriesBody (oneTermSequence v) (oneTermSequence_summable v) = centeredBody v := by
  first
  | apply ConvexBody.ext
    change segmentSeries (oneTermSequence v) = (centeredBody v : Set ThreeSpace)
    rw [segmentSeries_oneTermSequence, centeredSegment_eq_image, centeredBody_carrier]

theorem canonicalTuple_eq_series (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    canonicalTuple lam hlam₀ hlam₁ =
      fun i => segmentSeriesBody (canonicalGenerators lam i)
        (canonicalGenerators_summable lam hlam₀ hlam₁ i) := by
  first
  | funext i
    fin_cases i
    · exact (segmentSeriesBody_oneTermSequence (axis 0)).symm
    · exact (segmentSeriesBody_oneTermSequence (axis 1)).symm
    · exact (segmentSeriesBody_oneTermSequence (axis 2)).symm
    · exact (segmentSeriesBody_oneTermSequence directionV).symm
    · exact (segmentSeriesBody_oneTermSequence directionW).symm
    · exact (segmentSeriesBody_oneTermSequence directionZ).symm
    · exact map_segmentSeriesBody placedA (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact map_segmentSeriesBody placedB (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)
    · exact map_segmentSeriesBody placedC (weightedOrbit lam)
        (weightedOrbit_summable lam hlam₀ hlam₁)

/-- Full genuine cubic polynomial existence for the nine-body construction,
with all nonnegative real weights and all 165 cubic coefficient coordinates. -/
theorem canonicalTuple_realizes (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    ∃ c : Coefficients 9 3, Realizes (canonicalTuple lam hlam₀ hlam₁) c := by
  first
  | rw [canonicalTuple_eq_series]
    exact summable_segment_series_realizes (canonicalGenerators lam)
      (canonicalGenerators_summable lam hlam₀ hlam₁)

theorem canonicalTuple_calibrated (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    IsCalibratedTuple (canonicalTuple lam hlam₀ hlam₁) := by
  first
  | constructor
    · intro i
      fin_cases i <;> rfl
    · exact ⟨0, zero_mem_segmentSeries (weightedOrbit lam), map_zero placedA⟩
    · exact ⟨0, zero_mem_segmentSeries (weightedOrbit lam), map_zero placedB⟩
    · exact ⟨0, zero_mem_segmentSeries (weightedOrbit lam), map_zero placedC⟩
    · rintro x ⟨p, hp, rfl⟩
      rfl
    · rintro x ⟨p, hp, rfl⟩
      rfl
    · rintro x ⟨p, hp, rfl⟩
      rfl


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CanonicalShapeTuple.lean -/

/- BEGIN SOURCE: VolumePolynomials/ShapeCalibrationVolume.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

theorem volume_three_centered_segments (v w z : ThreeSpace) :
    bodyVolume (centeredBody v + centeredBody w + centeredBody z) =
      |determinant3 v w z| := by
  first
  | rw [centeredBody_eq_translate v, centeredBody_eq_translate w, centeredBody_eq_translate z,
      translateBody_add, translateBody_add, bodyVolume_translate, volume_three_origin_segments]

theorem volume_two_centered_segments (v w : ThreeSpace) :
    bodyVolume (centeredBody v + centeredBody w) = 0 := by
  first
  | have h := volume_three_centered_segments v w 0
    simpa [centeredBody_zero, determinant3] using h

theorem coordinate_zero_centeredBody (v : ThreeSpace) (i : Fin 3) (hv : v i = 0) :
    ∀ x ∈ centeredBody v, x i = 0 := by
  first
  | intro x hx
    change x ∈ (centeredBody v : Set ThreeSpace) at hx
    rw [centeredBody_carrier] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simp [hv]

theorem coordinate_zero_add {K L : Body 3} (i : Fin 3)
    (hK : ∀ x ∈ K, x i = 0) (hL : ∀ x ∈ L, x i = 0) :
    ∀ x ∈ K + L, x i = 0 := by
  first
  | intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
    change y i + z i = 0
    rw [hK y hy, hL z hz, add_zero]

/-- A body contained in a coordinate plane has literal three-dimensional
Lebesgue volume zero. The origin assumption is supplied in each application. -/
theorem bodyVolume_zero_of_coordinate (K : Body 3) (i : Fin 3)
    (hzero : (0 : ThreeSpace) ∈ K) (hK : ∀ x ∈ K, x i = 0) :
    bodyVolume K = 0 := by
  first
  | apply (bodyVolume_eq_zero_iff_linearHull_ne_top hzero).mpr
    intro htop
    let p : ThreeSpace →ₗ[ℝ] ℝ := (ContinuousLinearMap.proj i).toLinearMap
    have hsub : linearHull K ≤ LinearMap.ker p := by
      apply Submodule.span_le.mpr
      intro x hx
      exact hK x hx
    have hm : axis i ∈ linearHull K := by rw [htop]; trivial
    have hz : p (axis i) = 0 := hsub hm
    simpa [p, axis, Pi.single_apply] using hz

theorem IsCalibratedTuple.volume_planeA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    bodyVolume (K ShapeConditions.bodyA + K ShapeConditions.e₁ + K ShapeConditions.e₂) = 0 := by
  first
  | have h₁ : K ShapeConditions.e₁ = centeredBody (axis 0) := hK.segments 0
    have h₂ : K ShapeConditions.e₂ = centeredBody (axis 1) := hK.segments 1
    rw [h₁, h₂]
    apply bodyVolume_zero_of_coordinate _ 2
    · exact zero_mem_body_add (zero_mem_body_add hK.zeroA (zero_mem_centeredBody _))
        (zero_mem_centeredBody _)
    · exact coordinate_zero_add 2
        (coordinate_zero_add 2 hK.planeA
          (coordinate_zero_centeredBody _ 2 (by simp [axis, Pi.single_apply])))
        (coordinate_zero_centeredBody _ 2 (by simp [axis, Pi.single_apply]))

theorem IsCalibratedTuple.volume_planeB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    bodyVolume (K ShapeConditions.bodyB + K ShapeConditions.e₁ + K ShapeConditions.e₃) = 0 := by
  first
  | have h₁ : K ShapeConditions.e₁ = centeredBody (axis 0) := hK.segments 0
    have h₃ : K ShapeConditions.e₃ = centeredBody (axis 2) := hK.segments 2
    rw [h₁, h₃]
    apply bodyVolume_zero_of_coordinate _ 1
    · exact zero_mem_body_add (zero_mem_body_add hK.zeroB (zero_mem_centeredBody _))
        (zero_mem_centeredBody _)
    · exact coordinate_zero_add 1
        (coordinate_zero_add 1 hK.planeB
          (coordinate_zero_centeredBody _ 1 (by simp [axis, Pi.single_apply])))
        (coordinate_zero_centeredBody _ 1 (by simp [axis, Pi.single_apply]))

theorem IsCalibratedTuple.volume_planeC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    bodyVolume (K ShapeConditions.bodyC + K ShapeConditions.e₂ + K ShapeConditions.e₃) = 0 := by
  first
  | have h₂ : K ShapeConditions.e₂ = centeredBody (axis 1) := hK.segments 1
    have h₃ : K ShapeConditions.e₃ = centeredBody (axis 2) := hK.segments 2
    rw [h₂, h₃]
    apply bodyVolume_zero_of_coordinate _ 0
    · exact zero_mem_body_add (zero_mem_body_add hK.zeroC (zero_mem_centeredBody _))
        (zero_mem_centeredBody _)
    · exact coordinate_zero_add 0
        (coordinate_zero_add 0 hK.planeC
          (coordinate_zero_centeredBody _ 0 (by simp [axis, Pi.single_apply])))
        (coordinate_zero_centeredBody _ 0 (by simp [axis, Pi.single_apply]))

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ShapeCalibrationVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolonomyAngle.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

/-- The paper's angle is chosen in `(0, π)`, so the area formula has positive sine denominator. -/
def angle : ℝ := Real.arccos (1 / 3)

theorem cos_angle : Real.cos angle = 1 / 3 := by
  first
  | exact Real.cos_arccos (by norm_num) (by norm_num)

theorem angle_pos : 0 < angle := Real.arccos_pos.mpr (by norm_num)

theorem angle_lt_pi : angle < Real.pi := Real.arccos_lt_pi.mpr (by norm_num)

theorem sin_angle_pos : 0 < Real.sin angle := Real.sin_pos_of_pos_of_lt_pi angle_pos angle_lt_pi

/-- The angular parameter in Theorem 7.3 is not a rational multiple of π. -/
theorem angle_not_rational_multiple_pi {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    ¬ ∃ q : ℚ, θ = q * Real.pi := by
  first
  | intro hrat
    have hn := niven hrat (show ∃ q : ℚ, Real.cos θ = q from ⟨1 / 3, by simpa using hθ⟩)
    norm_num [hθ] at hn


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolonomyAngle.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolonomyDeterminants.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

open Polynomial.Chebyshev

theorem orbit_snd_recurrence (n : ℕ) :
    (orbit (n + 2)).2 = (2 / 3 : ℝ) * (orbit (n + 1)).2 - (orbit n).2 := by
  first
  | rw [show n + 2 = (n + 1) + 1 by omega, orbit_succ, orbit_succ]
    dsimp [returnMap]
    ring

/-- Cayley–Hamilton in explicit coordinates, matched with the proved Chebyshev recurrence. -/
theorem orbit_snd_eq_chebyshev (n : ℕ) :
    (orbit (n + 1)).2 = -(U ℝ (n : ℤ)).eval (1 / 3) := by
  first
  | induction n using Nat.twoStepInduction with
    | zero => norm_num [orbit, returnMap]
    | one => norm_num [orbit, returnMap]
    | more n hn hn1 =>
        have hr := orbit_snd_recurrence (n + 1)
        rw [hn1, hn] at hr
        rw [show n + 2 + 1 = n + 1 + 2 by omega, hr]
        push_cast
        rw [U_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X]
        ring

theorem orbit_snd_mul_sin (n : ℕ) :
    -(orbit n).2 * Real.sin angle = Real.sin ((n : ℝ) * angle) := by
  first
  | cases n with
    | zero => simp
    | succ n =>
        rw [orbit_snd_eq_chebyshev, neg_neg]
        simpa only [cos_angle, Int.cast_natCast, Int.cast_add, Int.cast_one,
          Nat.cast_add, Nat.cast_one] using U_real_cos angle (n : ℤ)

theorem abs_orbit_snd (n : ℕ) :
    |(orbit n).2| = |Real.sin ((n : ℝ) * angle)| / Real.sin angle := by
  first
  | apply (eq_div_iff sin_angle_pos.ne').mpr
    have h := congrArg abs (orbit_snd_mul_sin n)
    simpa only [abs_mul, abs_neg, abs_of_pos sin_angle_pos] using h

theorem abs_det_orbit_gap (i k : ℕ) :
    |det (orbit i) (orbit (i + k))| =
      |Real.sin ((k : ℝ) * angle)| / Real.sin angle := by
  first
  | rw [det_orbit_add, abs_orbit_snd]

/-- The area contribution of a pair depends on its gap and a geometric factor. -/
theorem abs_det_weighted_gap (lam : ℝ) (hlam : 0 ≤ lam) (i k : ℕ) :
    |det (weightedOrbit lam i) (weightedOrbit lam (i + (k + 1)))| =
      (lam ^ 2) ^ i *
        (|Real.sin (((k + 1 : ℕ) : ℝ) * angle)| * lam ^ (k + 1) / Real.sin angle) := by
  first
  | rw [weightedOrbit, weightedOrbit, det_smul, abs_mul,
      abs_of_nonneg (mul_nonneg (pow_nonneg hlam i) (pow_nonneg hlam _)),
      abs_det_orbit_gap]
    rw [pow_two, mul_pow, pow_add]
    ring

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolonomyDeterminants.lean -/

/- BEGIN SOURCE: VolumePolynomials/InfiniteZonotopeArea.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology Pointwise
open Set MeasureTheory Filter

theorem centeredSegment_eq_planar (v : ℝ × ℝ) :
    centeredSegment v = PlanarExtrusion.centeredSegment v := by
  first
  | ext x
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, t.property, ht.symm⟩
    · rintro ⟨t, ht, heq⟩
      exact ⟨⟨t, ht⟩, heq.symm⟩

theorem prefixSeries_eq_zonotope (u : ℕ → ℝ × ℝ) (N : ℕ) :
    prefixSeries u N = PlanarExtrusion.zonotope ((List.range N).map u) := by
  first
  | induction N with
    | zero => rw [prefixSeries_zero]; rfl
    | succ N ih =>
        rw [prefixSeries_succ, ih, centeredSegment_eq_planar, PlanarExtrusion.zonotope_range_succ]

theorem prefixBody_area (u : ℕ → ℝ × ℝ) (N : ℕ) :
    volume.real (prefixBody u N : Set (ℝ × ℝ)) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)| := by
  first
  | change volume.real (prefixSeries u N) = _
    rw [prefixSeries_eq_zonotope, PlanarExtrusion.area_zonotope_range]

theorem abs_determinant_le_norm (p q : ℝ × ℝ) :
    |PlanarExtrusion.determinant p q| ≤ 2 * ‖p‖ * ‖q‖ := by
  first
  | have hpx : |p.1| ≤ ‖p‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_left ‖p.1‖ ‖p.2‖
    have hpy : |p.2| ≤ ‖p‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_right ‖p.1‖ ‖p.2‖
    have hqx : |q.1| ≤ ‖q‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_left ‖q.1‖ ‖q.2‖
    have hqy : |q.2| ≤ ‖q‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_right ‖q.1‖ ‖q.2‖
    calc
      |PlanarExtrusion.determinant p q| ≤ |p.1 * q.2| + |p.2 * q.1| := by
        simpa only [PlanarExtrusion.determinant, Real.norm_eq_abs] using
          norm_sub_le (p.1 * q.2) (p.2 * q.1)
      _ = |p.1| * |q.2| + |p.2| * |q.1| := by rw [abs_mul, abs_mul]
      _ ≤ ‖p‖ * ‖q‖ + ‖p‖ * ‖q‖ :=
        add_le_add (mul_le_mul hpx hqy (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul hpy hqx (abs_nonneg _) (norm_nonneg _))
      _ = 2 * ‖p‖ * ‖q‖ := by ring

theorem determinant_rows_summable (u : ℕ → ℝ × ℝ) (hu : Summable fun n => ‖u n‖) :
    Summable (fun j => ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)|) := by
  first
  | let f : ℕ × ℕ → ℝ := fun p => if p.2 < p.1 then
      |PlanarExtrusion.determinant (u p.2) (u p.1)| else 0
    have hprod := hu.mul_of_nonneg hu (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hf : Summable f := by
      apply (hprod.mul_left 2).of_norm_bounded
      intro p
      by_cases hp : p.2 < p.1
      · simp only [f, if_pos hp, Real.norm_eq_abs, abs_abs]
        exact (abs_determinant_le_norm (u p.2) (u p.1)).trans_eq (by ring)
      · simp only [f, if_neg hp, norm_zero]
        positivity
    have hrow (j : ℕ) : ∑' i, f (j, i) =
        ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)| := by
      rw [tsum_eq_sum (s := Finset.range j) (by
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [f, hi])]
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, Finset.mem_range.mp hi]
    exact hf.prod.congr hrow

/-- The planar zonotope area formula passes to the actual infinite Minkowski sum by
Hausdorff convergence and continuity of actual Haar volume. -/
theorem area_infinite_segment_series (u : ℕ → ℝ × ℝ) (hu : Summable fun n => ‖u n‖) :
    volume.real (segmentSeriesBody u hu : Set (ℝ × ℝ)) =
      ∑' j, ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)| := by
  first
  | have hvol := (continuous_convexBody_realMeasure
      (volume : Measure (ℝ × ℝ))).continuousAt.tendsto.comp (prefixBody_tendsto u hu)
    have hvol' : Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)|)
        atTop (𝓝 (volume.real (segmentSeriesBody u hu : Set (ℝ × ℝ)))) := by
      simpa only [Function.comp_def, prefixBody_area] using hvol
    exact tendsto_nhds_unique hvol' (determinant_rows_summable u hu).hasSum.tendsto_sum_nat

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/InfiniteZonotopeArea.lean -/

/- BEGIN SOURCE: VolumePolynomials/RadialPoles.lean -/
section


@[expose] public section
noncomputable section

/-!
The analytic mechanism of the natural-boundary argument in Theorem 7.3:
absolutely summable weights at distinct unit-circle frequencies produce genuine
nonzero radial residues. No Fourier expansion is assumed to be proved by this file.
-/

namespace VolumePolynomials

open scoped Topology
open Filter

noncomputable def radialKernel (r : ℝ) (q : ℂ) : ℂ :=
  (1 - (r : ℂ)) * ((r : ℂ) * q) / (1 - (r : ℂ) * q)

theorem radialKernel_norm_le_one (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (q : ℂ) (hq : ‖q‖ = 1) : ‖radialKernel r q‖ ≤ 1 := by
  first
  | have hrq : ‖(r : ℂ) * q‖ = r := by
      first
      | simp [norm_mul, hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₀]
    have hden : 1 - r ≤ ‖1 - (r : ℂ) * q‖ := by
      first
      | simpa only [norm_one, hrq] using norm_sub_norm_le (1 : ℂ) ((r : ℂ) * q)
    have hdenpos : 0 < ‖1 - (r : ℂ) * q‖ := lt_of_lt_of_le (sub_pos.mpr hr₁) hden
    have hone : ‖1 - (r : ℂ)‖ = 1 - r := by
      first
      | rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr₁)]
    rw [radialKernel, norm_div, norm_mul, hone, hrq, div_le_iff₀ hdenpos, one_mul]
    nlinarith [sq_nonneg (1 - r)]

theorem radialKernel_one (r : ℝ) (hr : r < 1) : radialKernel r 1 = (r : ℂ) := by
  first
  | have hden : (1 : ℂ) - (r : ℂ) ≠ 0 := by
      first
      | exact_mod_cast (ne_of_gt (sub_pos.mpr hr))
    dsimp [radialKernel]
    simp only [mul_one]
    field_simp [hden] <;> ring

theorem radialKernel_tendsto {r : ℕ → ℝ} (hr₁ : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (q : ℂ) :
    Tendsto (fun n => radialKernel (r n) q) atTop (𝓝 (if q = 1 then 1 else 0)) := by
  first
  | classical
    have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 1) := by
      first
      | simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hrlim
    have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    by_cases hq : q = 1
    · subst q
      simpa [radialKernel_one _ (hr₁ _)] using hrC
    · have hden : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      have h := ((hone.sub hrC).mul (hrC.mul_const q)).div
        (hone.sub (hrC.mul_const q)) (by simpa only [one_mul] using hden)
      simpa only [Pi.div_def, one_mul, sub_self, zero_mul, zero_div,
        if_neg hq, radialKernel] using h

/-- A holomorphic-disc candidate obtained from weighted elementary Cauchy kernels. -/
noncomputable def weightedCauchySeries {ι : Type*} (β u : ι → ℂ) (z : ℂ) : ℂ :=
  ∑' i, β i * (z * u i) / (1 - z * u i)

theorem weighted_radial_residue {ι : Type*} (β u : ι → ℂ)
    (hβ : Summable fun i => ‖β i‖) (hu : ∀ i, ‖u i‖ = 1)
    (huinj : Function.Injective u) (r : ℕ → ℝ)
    (hr₀ : ∀ n, 0 ≤ r n) (hr₁ : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (j : ι) :
    Tendsto (fun n => (1 - (r n : ℂ)) *
      weightedCauchySeries β u ((r n : ℂ) / u j)) atTop (𝓝 (β j)) := by
  first
  | classical
    have huj : u j ≠ 0 := by intro h; simpa [h] using hu j
    have hqnorm (i : ι) : ‖u i / u j‖ = 1 := by simp [norm_div, hu]
    have hlim := tendsto_tsum_of_dominated_convergence hβ
      (f := fun n i => β i * radialKernel (r n) (u i / u j))
      (g := fun i => if i = j then β j else 0) (by
        intro i
        by_cases hij : i = j
        · subst i
          have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => β j) atTop (𝓝 (β j))).mul
            (radialKernel_tendsto hr₁ hrlim (u j / u j))
          simpa [huj] using h
        · have hq : u i / u j ≠ 1 := by
            first
            | intro heq
              exact hij (huinj ((div_eq_one_iff_eq huj).mp heq))
          have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => β i) atTop (𝓝 (β i))).mul
            (radialKernel_tendsto hr₁ hrlim (u i / u j))
          simpa [hq, hij] using h) (by
        apply Eventually.of_forall
        intro n i
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left
          (radialKernel_norm_le_one (r n) (hr₀ n) (hr₁ n) _ (hqnorm i))
          (norm_nonneg _)).trans_eq (mul_one _))
    have hsame (n : ℕ) :
        (1 - (r n : ℂ)) * weightedCauchySeries β u ((r n : ℂ) / u j) =
          ∑' i, β i * radialKernel (r n) (u i / u j) := by
      first
      | rw [weightedCauchySeries, ← tsum_mul_left]
        apply tsum_congr
        intro i
        rw [show ((r n : ℂ) / u j) * u i = (r n : ℂ) * (u i / u j) by ring]
        simp only [radialKernel, div_eq_mul_inv]
        ring
    simpa only [← hsame, tsum_ite_eq] using hlim

/-- A nonzero radial residue excludes every finite radial limit at that boundary point. -/
theorem no_finite_radial_limit {ι : Type*} (β u : ι → ℂ)
    (hβ : Summable fun i => ‖β i‖) (hu : ∀ i, ‖u i‖ = 1)
    (huinj : Function.Injective u) (r : ℕ → ℝ)
    (hr₀ : ∀ n, 0 ≤ r n) (hr₁ : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (j : ι) (hβj : β j ≠ 0) :
    ¬ ∃ w : ℂ, Tendsto (fun n => weightedCauchySeries β u ((r n : ℂ) / u j))
      atTop (𝓝 w) := by
  first
  | rintro ⟨w, hw⟩
    have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 1) := by
      first
      | simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hrlim
    have hz : Tendsto (fun n => (1 - (r n : ℂ)) *
        weightedCauchySeries β u ((r n : ℂ) / u j)) atTop (𝓝 0) := by
      first
      | simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hrC).mul hw
    exact hβj (tendsto_nhds_unique
      (weighted_radial_residue β u hβ hu huinj r hr₀ hr₁ hrlim j) hz)

end VolumePolynomials
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 12
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RadialPoles.lean -/

/- BEGIN SOURCE: VolumePolynomials/SineFourier.lean -/
section


@[expose] public section
noncomputable section

/-! Exact Fourier-integral computation for the natural-boundary argument. -/

namespace VolumePolynomials

open scoped Interval
open intervalIntegral

noncomputable def sineFourierCoefficient (m : ℤ) : ℂ :=
  2 / ((Real.pi : ℂ) * (1 - 4 * (m : ℂ)^2))

theorem odd_frequency_ne_zero (m : ℤ) : (2 * (m : ℂ) + 1) * Complex.I ≠ 0 := by
  first
  | apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)

theorem exp_odd_pi (m : ℤ) :
    Complex.exp ((2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I) = -1 := by
  first
  | have heq : (2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by ring
    rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      Complex.exp_pi_mul_I, one_mul]

theorem integral_odd_frequency (m : ℤ) :
    (∫ x in (0 : ℝ)..Real.pi,
      Complex.exp (((2 * (m : ℂ) + 1) * Complex.I) * (x : ℂ))) =
        -2 / ((2 * (m : ℂ) + 1) * Complex.I) := by
  first
  | rw [integral_exp_mul_complex (odd_frequency_ne_zero m)]
    have heq : ((2 * (m : ℂ) + 1) * Complex.I) * (Real.pi : ℂ) =
        (2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I := by ring
    rw [heq, exp_odd_pi]
    norm_num

theorem sine_exponential_integrand (m : ℤ) (x : ℝ) :
    Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * (Real.sin x : ℂ) =
      (Complex.exp (((2 * ((-m - 1 : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)) -
       Complex.exp (((2 * ((-m : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ))) * Complex.I / 2 := by
  first
  | have hm : Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
        Complex.exp (-(x : ℂ) * Complex.I) =
        Complex.exp (((2 * ((-m - 1 : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hp : Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
        Complex.exp ((x : ℂ) * Complex.I) =
        Complex.exp (((2 * ((-m : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [Complex.ofReal_sin, Complex.sin]
    calc
      _ = (Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
            Complex.exp (-(x : ℂ) * Complex.I) -
          Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
            Complex.exp ((x : ℂ) * Complex.I)) * Complex.I / 2 := by ring
      _ = _ := by rw [hm, hp]

theorem sine_fourier_integral (m : ℤ) :
    (∫ x in (0 : ℝ)..Real.pi,
      Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * (Real.sin x : ℂ)) =
        2 / (1 - 4 * (m : ℂ)^2) := by
  first
  | simp_rw [sine_exponential_integrand]
    rw [integral_div, integral_mul_const, integral_sub,
      integral_odd_frequency, integral_odd_frequency]
    · have hm : (2 * (m : ℂ) + 1) ≠ 0 := by
        exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)
      have hp : (2 * (m : ℂ) - 1) ≠ 0 := by
        exact_mod_cast (show 2 * m - 1 ≠ 0 by omega)
      have hq : (1 - 4 * (m : ℂ)^2) ≠ 0 := by
        exact_mod_cast (show 1 - 4 * m^2 ≠ 0 by omega)
      push_cast
      field_simp [Complex.I_ne_zero, hm, hp, hq,
        odd_frequency_ne_zero (-m - 1), odd_frequency_ne_zero (-m)]
      ring_nf
      norm_num [Complex.I_sq]
      have hleft : (-1 - (m : ℂ) * 2) ≠ 0 := by
        convert neg_ne_zero.mpr hm using 1 <;> ring
      have hright : (1 - (m : ℂ) * 2) ≠ 0 := by
        convert neg_ne_zero.mpr hp using 1 <;> ring
      have hquad : (1 - (m : ℂ)^2 * 4) ≠ 0 := by
        simpa only [mul_comm] using hq
      field_simp [hleft, hright, hquad]
      <;> ring
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        Complex.exp (((2 * ((-m - 1 : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        Complex.exp (((2 * ((-m : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)))).intervalIntegrable _ _

theorem abs_sine_fourier_integral (m : ℤ) :
    (1 / (Real.pi : ℂ)) * (∫ x in (0 : ℝ)..Real.pi,
      Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * ((|Real.sin x| : ℝ) : ℂ)) =
        sineFourierCoefficient m := by
  first
  | have hInt : (∫ x in (0 : ℝ)..Real.pi,
        Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * ((|Real.sin x| : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..Real.pi,
          Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * (Real.sin x : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa [Set.uIcc_of_le Real.pi_pos.le] using hx
      dsimp only
      rw [abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hx')]
    rw [hInt, sine_fourier_integral, sineFourierCoefficient]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end VolumePolynomials
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 12
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SineFourier.lean -/

/- BEGIN SOURCE: VolumePolynomials/SineFourierSeries.lean -/
section


@[expose] public section
noncomputable section

/-! Absolute convergence and reconstruction of the Fourier series of |sin|. -/

namespace VolumePolynomials

open scoped Topology
open Set Filter

private theorem sineFourier_norm_bound (m : ℤ) (hm : m ≠ 0) :
    ‖sineFourierCoefficient m‖ ≤ (2 / Real.pi) * (1 / (m : ℝ)^2) := by
  first
  | have hmsqInt : (1 : ℤ) ≤ m^2 := by
      have := sq_pos_of_ne_zero hm
      omega
    have hmsq : (1 : ℝ) ≤ (m : ℝ)^2 := by exact_mod_cast hmsqInt
    have hneg : 1 - 4 * (m : ℝ)^2 < 0 := by nlinarith
    have hden : (1 - 4 * (m : ℂ)^2) = ((1 - 4 * (m : ℝ)^2 : ℝ) : ℂ) := by
      push_cast
      rfl
    have hnorm : ‖sineFourierCoefficient m‖ = 2 / (Real.pi * (4 * (m : ℝ)^2 - 1)) := by
      rw [sineFourierCoefficient, norm_div, norm_mul, hden, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_neg hneg]
      norm_num <;> congr 1 <;> ring
    rw [hnorm]
    calc
      2 / (Real.pi * (4 * (m : ℝ)^2 - 1)) ≤ 2 / (Real.pi * (m : ℝ)^2) :=
        div_le_div_of_nonneg_left (by norm_num)
          (mul_pos Real.pi_pos (by linarith))
          (mul_le_mul_of_nonneg_left (by nlinarith) Real.pi_pos.le)
      _ = (2 / Real.pi) * (1 / (m : ℝ)^2) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

theorem sineFourier_summable_norm : Summable (fun m : ℤ => ‖sineFourierCoefficient m‖) := by
  first
  | have hp : Summable (fun m : ℤ => 1 / (m : ℝ)^2) :=
      Real.summable_one_div_int_pow.mpr (by norm_num)
    apply (hp.mul_left (2 / Real.pi)).of_norm_bounded_eventually
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with m hm
    simpa only [norm_norm] using sineFourier_norm_bound m hm

theorem sineFourier_ne_zero (m : ℤ) : sineFourierCoefficient m ≠ 0 := by
  first
  | apply div_ne_zero (by norm_num)
    apply mul_ne_zero
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast (show 1 - 4 * m^2 ≠ 0 by omega)

theorem abs_sine_periodic :
    Function.Periodic (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) Real.pi := by
  first
  | intro x
    simp [Real.sin_add_pi]

/-- The actual continuous function |sin| on the circle of period π. -/
noncomputable def absoluteSineCircle : C(AddCircle Real.pi, ℂ) where
  toFun := Function.Periodic.lift abs_sine_periodic
  continuous_toFun := continuous_coinduced_dom.mpr
    (Complex.continuous_ofReal.comp Real.continuous_sin.abs)

@[simp] theorem absoluteSineCircle_coe (x : ℝ) :
    absoluteSineCircle (x : AddCircle Real.pi) = ((|Real.sin x| : ℝ) : ℂ) := rfl

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem fourierCoeff_absoluteSineCircle (m : ℤ) :
    fourierCoeff absoluteSineCircle m = sineFourierCoefficient m := by
  first
  | rw [fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ)]
    simp only [zero_add, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    convert abs_sine_fourier_integral m using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [fourier_coe_apply, absoluteSineCircle_coe, smul_eq_mul]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring

/-- The Fourier expansion used in equation (7.12), proved through its exact integral coefficients. -/
theorem abs_sine_hasSum_fourier (t : ℝ) :
    HasSum (fun m : ℤ => sineFourierCoefficient m *
      Complex.exp (2 * (m : ℂ) * (t : ℂ) * Complex.I)) ((|Real.sin t| : ℝ) : ℂ) := by
  first
  | have hsum : Summable (fourierCoeff absoluteSineCircle) := by
      have hcoeff : fourierCoeff absoluteSineCircle = sineFourierCoefficient :=
        funext fourierCoeff_absoluteSineCircle
      rw [hcoeff]
      exact sineFourier_summable_norm.of_norm
    have h := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle Real.pi)
    convert h using 1
    · ext m
      rw [fourierCoeff_absoluteSineCircle, fourier_coe_apply, smul_eq_mul]
      congr 2
      field_simp [Real.pi_ne_zero] <;> ring
    · rfl

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SineFourierSeries.lean -/

/- BEGIN SOURCE: VolumePolynomials/FourierGeneratingSeries.lean -/
section


@[expose] public section
noncomputable section

/-! The Cauchy-kernel representation (7.12) from the proved Fourier expansion. -/

namespace VolumePolynomials

open scoped Topology

/-- The unit frequency e^(2 i m θ). -/
noncomputable def rotationFrequency (θ : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (2 * (m : ℂ) * (θ : ℂ) * Complex.I)

theorem rotationFrequency_norm (θ : ℝ) (m : ℤ) : ‖rotationFrequency θ m‖ = 1 := by
  first
  | have h : 2 * (m : ℂ) * (θ : ℂ) * Complex.I =
        ((2 * (m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; rfl
    rw [rotationFrequency, h, Complex.norm_exp_ofReal_mul_I]

noncomputable def sineGeneratingFunction (θ : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((|Real.sin ((n + 1 : ℕ) * θ)| : ℝ) : ℂ) * z^(n + 1)

theorem sine_fourier_at_multiple (θ : ℝ) (n : ℕ) :
    ((|Real.sin ((n : ℝ) * θ)| : ℝ) : ℂ) =
      ∑' m : ℤ, sineFourierCoefficient m * rotationFrequency θ m ^ n := by
  first
  | have h := (abs_sine_hasSum_fourier ((n : ℝ) * θ)).tsum_eq.symm
    rw [h]
    apply tsum_congr
    intro m
    rw [rotationFrequency, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

/-- Absolutely summable Fourier data can be interchanged with a generating series inside the disk. -/
theorem fourier_generating_cauchy {ι : Type*} (β u : ι → ℂ)
    (hβ : Summable fun i => ‖β i‖) (hu : ∀ i, ‖u i‖ = 1)
    (c : ℕ → ℂ) (hc : ∀ n, c n = ∑' i, β i * u i ^ n)
    (z : ℂ) (hz : ‖z‖ < 1) :
    (∑' n : ℕ, c (n + 1) * z^(n + 1)) = weightedCauchySeries β u z := by
  first
  | have hg : Summable (fun n : ℕ => ‖z‖^(n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hz)
    have hdouble : Summable (fun p : ℕ × ι => β p.2 * (z * u p.2)^(p.1 + 1)) := by
      apply (hg.mul_of_nonneg hβ (fun n => pow_nonneg (norm_nonneg _) _)
        (fun i => norm_nonneg _)).of_norm_bounded
      intro p
      simp only [norm_mul, norm_pow, hu, mul_one]
      exact le_of_eq (mul_comm _ _)
    calc
      (∑' n : ℕ, c (n + 1) * z^(n + 1)) =
          ∑' n : ℕ, ∑' i, β i * (z * u i)^(n + 1) := by
        apply tsum_congr
        intro n
        rw [hc, ← tsum_mul_right]
        apply tsum_congr
        intro i
        rw [mul_pow]
        ring
      _ = ∑' i, ∑' n : ℕ, β i * (z * u i)^(n + 1) := hdouble.tsum_comm.symm
      _ = weightedCauchySeries β u z := by
        apply tsum_congr
        intro i
        have hzi : ‖z * u i‖ < 1 := by simpa [norm_mul, hu] using hz
        simp_rw [pow_succ', ← mul_assoc]
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hzi]
        rfl

/-- Equation (7.12), with the actual sine sequence and all Fourier coefficients determined. -/
theorem sineGeneratingFunction_eq_cauchy (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    sineGeneratingFunction θ z =
      weightedCauchySeries sineFourierCoefficient (rotationFrequency θ) z := by
  first
  | exact fourier_generating_cauchy sineFourierCoefficient (rotationFrequency θ)
      sineFourier_summable_norm (rotationFrequency_norm θ)
      (fun n => ((|Real.sin ((n : ℝ) * θ)| : ℝ) : ℂ)) (sine_fourier_at_multiple θ) z hz

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FourierGeneratingSeries.lean -/

/- BEGIN SOURCE: VolumePolynomials/RotationFrequencies.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

noncomputable def rotationUnit (θ : ℝ) (m : ℤ) : Circle :=
  AddCircle.toCircle (m • (θ : AddCircle Real.pi))

theorem rotationUnit_coe (θ : ℝ) (m : ℤ) :
    (rotationUnit θ m : ℂ) = rotationFrequency θ m := by
  first
  | rw [rotationUnit, ← QuotientAddGroup.mk_zsmul, AddCircle.toCircle_apply_mk,
      Circle.coe_exp, rotationFrequency]
    congr 1
    simp only [zsmul_eq_mul]
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring

theorem angle_ratio_irrational {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    Irrational (θ / Real.pi) := by
  first
  | rintro ⟨q, hq⟩
    apply Holonomy.angle_not_rational_multiple_pi hθ
    exact ⟨q, (div_eq_iff Real.pi_ne_zero).mp hq.symm⟩

theorem rotationUnit_dense {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    DenseRange (rotationUnit θ) := by
  first
  | have hd : DenseRange (fun m : ℤ => m • (θ : AddCircle Real.pi)) :=
      AddCircle.denseRange_zsmul_coe_iff.mpr (angle_ratio_irrational hθ)
    let e := AddCircle.homeomorphCircle Real.pi_ne_zero
    have hcomp := e.surjective.denseRange.comp hd e.continuous
    change DenseRange (fun m : ℤ => AddCircle.toCircle (m • (θ : AddCircle Real.pi)))
    simpa only [Function.comp_def, e, AddCircle.homeomorphCircle_apply, rotationUnit] using hcomp

theorem rotationUnit_injective {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    Function.Injective (rotationUnit θ) := by
  first
  | have hd : DenseRange (fun m : ℤ => m • (θ : AddCircle Real.pi)) :=
      AddCircle.denseRange_zsmul_coe_iff.mpr (angle_ratio_irrational hθ)
    have ho : addOrderOf (θ : AddCircle Real.pi) = 0 := AddCircle.denseRange_zsmul_iff.mp hd
    have hi : Function.Injective (fun m : ℤ => m • (θ : AddCircle Real.pi)) :=
      injective_zsmul_iff_not_isOfFinAddOrder.mpr (addOrderOf_eq_zero_iff.mp ho)
    exact (AddCircle.injective_toCircle Real.pi_ne_zero).comp hi

theorem rotationFrequency_injective {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    Function.Injective (rotationFrequency θ) := by
  first
  | intro i j hij
    apply rotationUnit_injective hθ
    apply Subtype.coe_injective
    simpa only [rotationUnit_coe] using hij

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RotationFrequencies.lean -/

/- BEGIN SOURCE: VolumePolynomials/NaturalBoundary.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Set Filter Metric

/-- Local continuous continuation across a point of the unit circle. Excluding this
is stronger than excluding local holomorphic continuation. -/
def HasLocalContinuousExtension (F : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ δ > 0, ∃ g : ℂ → ℂ, ContinuousOn g (ball ζ δ) ∧
    ∀ z ∈ ball ζ δ, ‖z‖ < 1 → g z = F z

def radialSequence (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem radialSequence_nonneg (n : ℕ) : 0 ≤ radialSequence n := by
  first
  | unfold radialSequence
    positivity

theorem radialSequence_lt_one (n : ℕ) : radialSequence n < 1 := by
  first
  | unfold radialSequence
    apply (div_lt_one (by positivity)).mpr
    linarith

theorem radialSequence_tendsto : Tendsto radialSequence atTop (𝓝 1) :=
  tendsto_natCast_div_add_atTop (1 : ℝ)

/-- Dense, nonzero Cauchy residues rule out local continuous continuation everywhere on the circle. -/
theorem dense_cauchy_no_boundary_extension {ι : Type*} (β : ι → ℂ) (u : ι → Circle)
    (hβ : Summable fun i => ‖β i‖) (hβne : ∀ i, β i ≠ 0)
    (huinj : Function.Injective u) (hudense : DenseRange u) (ζ : Circle) :
    ¬ HasLocalContinuousExtension (weightedCauchySeries β (fun i => (u i : ℂ))) ζ := by
  first
  | rintro ⟨δ, hδ, g, hgcont, hgeq⟩
    have hdinv : DenseRange (fun i => (u i)⁻¹) :=
      (inv_involutive.surjective.denseRange).comp hudense continuous_inv
    have hopen : IsOpen ((fun z : Circle => (z : ℂ)) ⁻¹' ball (ζ : ℂ) δ) :=
      isOpen_ball.preimage continuous_subtype_val
    have hnonempty : (((fun z : Circle => (z : ℂ)) ⁻¹' ball (ζ : ℂ) δ)).Nonempty :=
      ⟨ζ, mem_ball_self hδ⟩
    obtain ⟨j, hj⟩ := hdinv.exists_mem_open hopen hnonempty
    change ((u j : ℂ)⁻¹) ∈ ball (ζ : ℂ) δ at hj
    have huj : (u j : ℂ) ≠ 0 := by
      first
      | intro h
        simpa [h] using (u j).norm_coe
    have hrC : Tendsto (fun n => (radialSequence n : ℂ)) atTop (𝓝 1) := by
      first
      | simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp radialSequence_tendsto
    have hray : Tendsto (fun n => (radialSequence n : ℂ) / u j)
        atTop (𝓝 ((u j : ℂ)⁻¹)) := by
      first
      | simpa only [one_div] using hrC.div_const (u j : ℂ)
    have hgpoint : ContinuousAt g ((u j : ℂ)⁻¹) := hgcont.continuousAt (isOpen_ball.mem_nhds hj)
    have hlimit : Tendsto (fun n => g ((radialSequence n : ℂ) / u j))
        atTop (𝓝 (g ((u j : ℂ)⁻¹))) := by
      first
      | simpa only [Function.comp_def] using hgpoint.tendsto.comp hray
    have hinside (n : ℕ) : ‖(radialSequence n : ℂ) / u j‖ < 1 := by
      first
      | simpa [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (radialSequence_nonneg n)] using radialSequence_lt_one n
    have hagree : ∀ᶠ n in atTop,
        g ((radialSequence n : ℂ) / u j) =
          weightedCauchySeries β (fun i => (u i : ℂ)) ((radialSequence n : ℂ) / u j) := by
      first
      | filter_upwards [hray (isOpen_ball.mem_nhds hj)] with n hn
        exact hgeq _ hn (hinside n)
    exact no_finite_radial_limit β (fun i => (u i : ℂ)) hβ (fun i => (u i).norm_coe)
      (Subtype.coe_injective.comp huinj) radialSequence radialSequence_nonneg
      radialSequence_lt_one radialSequence_tendsto j (hβne j)
      ⟨g ((u j : ℂ)⁻¹), hlimit.congr' hagree⟩

/-- The unit circle is a boundary of continuous continuation for the actual |sin(nθ)| series. -/
theorem sineGeneratingFunction_no_boundary_extension {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (ζ : Circle) :
    ¬ HasLocalContinuousExtension (sineGeneratingFunction θ) ζ := by
  first
  | intro h
    apply dense_cauchy_no_boundary_extension sineFourierCoefficient (rotationUnit θ)
      sineFourier_summable_norm sineFourier_ne_zero (rotationUnit_injective hθ)
      (rotationUnit_dense hθ) ζ
    obtain ⟨δ, hδ, g, hg, hgeq⟩ := h
    refine ⟨δ, hδ, g, hg, ?_⟩
    intro z hz hznorm
    rw [hgeq z hz hznorm, sineGeneratingFunction_eq_cauchy θ z hznorm]
    simp only [rotationUnit_coe]

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/NaturalBoundary.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolomorphicSeries.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open Set Metric
open scoped NNReal ENNReal

/-- The full coefficient sequence; its constant coefficient is zero. -/
noncomputable def sineCoefficient (θ : ℝ) (n : ℕ) : ℂ :=
  ((|Real.sin ((n : ℝ) * θ)| : ℝ) : ℂ)

theorem sineCoefficient_norm_le (θ : ℝ) (n : ℕ) : ‖sineCoefficient θ n‖ ≤ 1 := by
  first
  | simpa [sineCoefficient, Complex.norm_real, Real.norm_eq_abs] using
      Real.abs_sin_le_one ((n : ℝ) * θ)

theorem sine_powerSeries_norm_summable (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖sineCoefficient θ n * z ^ n‖) := by
  first
  | apply (summable_geometric_of_lt_one (norm_nonneg z) hz).of_nonneg_of_le
      (fun n => norm_nonneg _)
    intro n
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n) (sineCoefficient_norm_le θ n)

theorem sine_powerSeries_summable (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => sineCoefficient θ n * z ^ n) :=
  (sine_powerSeries_norm_summable θ z hz).of_norm

theorem sineGeneratingFunction_eq_full_series (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    sineGeneratingFunction θ z = ∑' n : ℕ, sineCoefficient θ n * z ^ n := by
  first
  | rw [(sine_powerSeries_summable θ z hz).tsum_eq_zero_add]
    simp [sineCoefficient, sineGeneratingFunction]

/-- Holomorphy of the actual series in the open unit disk follows from its uniformly bounded
coefficients, with the radius bound proved for the actual formal multilinear series. -/
theorem sineGeneratingFunction_analyticOnNhd (θ : ℝ) :
    AnalyticOnNhd ℂ (sineGeneratingFunction θ) (ball 0 1) := by
  first
  | let p := FormalMultilinearSeries.ofScalars ℂ (sineCoefficient θ)
    have hr : (1 : ℝ≥0∞) ≤ p.radius := by
      apply p.le_radius_of_bound (r := (1 : ℝ≥0)) 1
      intro n
      simpa [p, FormalMultilinearSeries.ofScalars_norm] using sineCoefficient_norm_le θ n
    have hp : AnalyticOnNhd ℂ p.sum (ball 0 1) := by
      intro z hz
      apply p.analyticOnNhd z
      apply lt_of_lt_of_le _ hr
      simpa only [mem_ball, dist_zero_right, mem_eball, edist_dist,
        ENNReal.ofReal_lt_one] using hz
    apply (analyticOnNhd_congr isOpen_ball ?_).mp hp
    intro z hz
    have hznorm : ‖z‖ < 1 := by simpa using hz
    rw [sineGeneratingFunction_eq_full_series θ z hznorm]
    exact FormalMultilinearSeries.ofScalars_sum_eq (sineCoefficient θ) z

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolomorphicSeries.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalTaylor.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Polynomial.Chebyshev Filter Metric

/-- The rational normalized sine coefficient, including the zero constant term. -/
def rationalSineCoefficient : ℕ → ℚ
  | 0 => 0
  | n + 1 => |(U ℚ (n : ℤ)).eval (1 / 3)|

theorem rationalSineCoefficient_eq {θ : ℝ} (hθ : Real.cos θ = 1 / 3)
    (hsin : 0 < Real.sin θ) (n : ℕ) :
    (rationalSineCoefficient n : ℝ) = |Real.sin ((n : ℝ) * θ)| / Real.sin θ := by
  first
  | cases n with
    | zero => simp [rationalSineCoefficient]
    | succ n =>
        have hcast : (((U ℚ (n : ℤ)).eval (1 / 3) : ℚ) : ℝ) =
            (U ℝ (n : ℤ)).eval (1 / 3) := by
          simpa using (algebraMap_eval_U (R := ℚ) (R' := ℝ) (1 / 3) (n : ℤ))
        simp only [rationalSineCoefficient, Rat.cast_abs, hcast]
        apply (eq_div_iff hsin.ne').mpr
        calc
          |(U ℝ (n : ℤ)).eval (1 / 3)| * Real.sin θ =
              |(U ℝ (n : ℤ)).eval (1 / 3) * Real.sin θ| := by
            rw [abs_mul, abs_of_pos hsin]
          _ = |Real.sin (((n + 1 : ℕ) : ℝ) * θ)| := by
            congr 1
            simpa [hθ] using U_real_cos θ (n : ℤ)

theorem rationalSineCoefficient_eq_complex {θ : ℝ} (hθ : Real.cos θ = 1 / 3)
    (hsin : 0 < Real.sin θ) (n : ℕ) :
    (rationalSineCoefficient n : ℂ) = sineCoefficient θ n / (Real.sin θ : ℂ) := by
  first
  | unfold sineCoefficient
    exact_mod_cast rationalSineCoefficient_eq hθ hsin n

/-- Ordinary Cauchy convolution, performed entirely over the rationals. -/
def rationalConvolution (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

theorem rationalConvolution_term (a b : ℕ → ℚ) (n : ℕ) (z : ℂ) :
    (rationalConvolution a b n : ℂ) * z ^ n =
      ∑ p ∈ Finset.antidiagonal n, ((a p.1 : ℂ) * z ^ p.1) *
        ((b p.2 : ℂ) * z ^ p.2) := by
  first
  | unfold rationalConvolution
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpn := Finset.mem_antidiagonal.mp hp
    rw [← hpn, pow_add]
    ring

/-- The Cauchy product identity together with the absolute convergence needed for iteration. -/
theorem rationalConvolution_hasSum (a b : ℕ → ℚ) (z A B : ℂ)
    (ha : Summable fun n => ‖(a n : ℂ) * z ^ n‖)
    (hb : Summable fun n => ‖(b n : ℂ) * z ^ n‖)
    (hA : HasSum (fun n => (a n : ℂ) * z ^ n) A)
    (hB : HasSum (fun n => (b n : ℂ) * z ^ n) B) :
    (Summable fun n => ‖(rationalConvolution a b n : ℂ) * z ^ n‖) ∧
      HasSum (fun n => (rationalConvolution a b n : ℂ) * z ^ n) (A * B) := by
  first
  | have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb
    simp only [← rationalConvolution_term] at hn
    refine ⟨hn, ?_⟩
    have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb
    rw [hA.tsum_eq, hB.tsum_eq] at heq
    simp only [← rationalConvolution_term] at heq
    exact heq.symm ▸ hn.of_norm.hasSum

/-- Rational Taylor coefficients of the complete area generating function. -/
def areaTaylorCoefficient : ℕ → ℚ :=
  rationalConvolution (rationalConvolution rationalSineCoefficient (fun _ => 1))
    (fun n => (-1) ^ n)

/-- The complex extension of formula (7.11). -/
noncomputable def areaGeneratingFunction (θ : ℝ) (z : ℂ) : ℂ :=
  sineGeneratingFunction θ z / ((1 - z ^ 2) * (Real.sin θ : ℂ))

theorem areaGeneratingFunction_hasSum {θ : ℝ} (hθ : Real.cos θ = 1 / 3)
    (hsin : 0 < Real.sin θ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n => (areaTaylorCoefficient n : ℂ) * z ^ n)
      (areaGeneratingFunction θ z) := by
  first
  | have hc : Summable (fun n => ‖(rationalSineCoefficient n : ℂ) * z ^ n‖) := by
      simp_rw [rationalSineCoefficient_eq_complex hθ hsin, div_mul_eq_mul_div, norm_div]
      exact (sine_powerSeries_norm_summable θ z hz).div_const _
    have hC : HasSum (fun n => (rationalSineCoefficient n : ℂ) * z ^ n)
        (sineGeneratingFunction θ z / (Real.sin θ : ℂ)) := by
      simp_rw [rationalSineCoefficient_eq_complex hθ hsin, div_mul_eq_mul_div]
      rw [sineGeneratingFunction_eq_full_series θ z hz]
      exact (sine_powerSeries_summable θ z hz).hasSum.div_const _
    have hplus : Summable (fun n : ℕ => ‖((1 : ℚ) : ℂ) * z ^ n‖) := by
      simpa only [Rat.cast_one, one_mul, norm_pow] using
        summable_geometric_of_lt_one (norm_nonneg z) hz
    have hPlus : HasSum (fun n : ℕ => ((1 : ℚ) : ℂ) * z ^ n) ((1 - z)⁻¹) := by
      simpa using hasSum_geometric_of_norm_lt_one hz
    have hminus : Summable (fun n : ℕ => ‖(((-1 : ℚ) ^ n : ℚ) : ℂ) * z ^ n‖) := by
      simpa only [Rat.cast_pow, Rat.cast_neg, Rat.cast_one, norm_mul, norm_pow,
        norm_neg, norm_one, one_pow, one_mul] using
        summable_geometric_of_lt_one (norm_nonneg z) hz
    have hMinus : HasSum (fun n : ℕ => (((-1 : ℚ) ^ n : ℚ) : ℂ) * z ^ n)
        ((1 + z)⁻¹) := by
      have hzneg : ‖-z‖ < 1 := by simpa using hz
      have hneg : (fun n : ℕ => (((-1 : ℚ) ^ n : ℚ) : ℂ) * z ^ n) =
          (fun n : ℕ => (-z) ^ n) := by
        funext n
        simp only [Rat.cast_pow, Rat.cast_neg, Rat.cast_one, ← mul_pow, neg_one_mul]
      rw [hneg]
      simpa only [sub_neg_eq_add] using hasSum_geometric_of_norm_lt_one hzneg
    obtain ⟨hfirst, hFirst⟩ := rationalConvolution_hasSum rationalSineCoefficient (fun _ => 1)
      z _ _ hc hplus hC hPlus
    have hfinal := (rationalConvolution_hasSum _ (fun n => (-1) ^ n) z _ _
      hfirst hminus hFirst hMinus).2
    convert hfinal using 1
    · rfl
    · unfold areaGeneratingFunction
      rw [show (1 - z ^ 2) = (1 - z) * (1 + z) by ring]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem areaGeneratingFunction_hasFPowerSeriesAt {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : 0 < Real.sin θ) :
    HasFPowerSeriesAt (areaGeneratingFunction θ)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (areaTaylorCoefficient n : ℂ))) 0 := by
  first
  | rw [hasFPowerSeriesAt_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm]
      using areaGeneratingFunction_hasSum hθ hsin z (by simpa using hz)

/-- The rational coefficients above are the actual normalized iterated derivatives at zero. -/
theorem areaGeneratingFunction_rational_taylor {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : 0 < Real.sin θ) (n : ℕ) :
    iteratedDeriv n (areaGeneratingFunction θ) 0 / (n.factorial : ℂ) =
      (areaTaylorCoefficient n : ℂ) := by
  first
  | have hp := areaGeneratingFunction_hasFPowerSeriesAt hθ hsin
    have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc.symm

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalTaylor.lean -/

/- BEGIN SOURCE: VolumePolynomials/AreaAnalytic.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open Metric

theorem one_sub_sq_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ^ 2 ≠ 0 := by
  first
  | intro h
    have heq : z ^ 2 = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm heq
    rw [norm_pow, norm_one] at hn
    exact ((sq_lt_one_iff₀ (norm_nonneg z)).mpr hz).ne hn

/-- The area formula extends holomorphically to the entire open unit disk. -/
theorem areaGeneratingFunction_analyticOnNhd (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    AnalyticOnNhd ℂ (areaGeneratingFunction θ) (ball 0 1) := by
  first
  | apply (sineGeneratingFunction_analyticOnNhd θ).div
    · fun_prop
    · intro z hz
      apply mul_ne_zero (one_sub_sq_ne_zero_of_norm_lt_one (by simpa using hz))
      exact_mod_cast hsin

/-- Multiplication by the polynomial denominator would turn any local continuation of area
into one of the sine generating function, including at the points `1` and `-1`. -/
theorem areaGeneratingFunction_no_boundary_extension {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0) (ζ : Circle) :
    ¬ HasLocalContinuousExtension (areaGeneratingFunction θ) ζ := by
  first
  | rintro ⟨δ, hδ, g, hg, hgeq⟩
    apply sineGeneratingFunction_no_boundary_extension hθ ζ
    refine ⟨δ, hδ, fun z => g z * ((1 - z ^ 2) * (Real.sin θ : ℂ)), ?_, ?_⟩
    · exact hg.mul (by fun_prop)
    · intro z hz hznorm
      change g z * ((1 - z ^ 2) * (Real.sin θ : ℂ)) = sineGeneratingFunction θ z
      rw [hgeq z hz hznorm, areaGeneratingFunction]
      apply div_mul_cancel₀
      apply mul_ne_zero (one_sub_sq_ne_zero_of_norm_lt_one hznorm)
      exact_mod_cast hsin

/-- The exact angle and area formula appearing in Theorem 7.3 have the stated analytic
properties, with no unspecified sign choice for the angular parameter. -/
theorem holonomy_area_analytic_properties :
    AnalyticOnNhd ℂ (areaGeneratingFunction Holonomy.angle) (ball 0 1) ∧
    (∀ ζ : Circle, ¬ HasLocalContinuousExtension (areaGeneratingFunction Holonomy.angle) ζ) ∧
    (∀ n : ℕ, iteratedDeriv n (areaGeneratingFunction Holonomy.angle) 0 / (n.factorial : ℂ) =
      (areaTaylorCoefficient n : ℂ)) := by
  first
  | exact ⟨areaGeneratingFunction_analyticOnNhd _ Holonomy.sin_angle_pos.ne',
      areaGeneratingFunction_no_boundary_extension Holonomy.cos_angle Holonomy.sin_angle_pos.ne',
      areaGeneratingFunction_rational_taylor Holonomy.cos_angle Holonomy.sin_angle_pos⟩

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AreaAnalytic.lean -/

/- BEGIN SOURCE: VolumePolynomials/RadialAlgebraicObstruction.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Filter Polynomial

/-- The precise leading-coefficient argument used in Theorem 7.3. It only uses a polynomial
identity along one sequence and a nonzero rescaled limit; no theorem about algebraic branches
is assumed. -/
theorem radial_polynomial_leadingCoeff (P : Polynomial (Polynomial ℂ))
    (z h δ : ℕ → ℂ) (ζ β : ℂ)
    (hz : Tendsto z atTop (𝓝 ζ)) (hδ : Tendsto δ atTop (𝓝 0))
    (hres : Tendsto (fun n => δ n * h n) atTop (𝓝 β))
    (hrel : ∀ n, P.eval₂ (Polynomial.evalRingHom (z n)) (h n) = 0) :
    P.leadingCoeff.eval ζ * β ^ P.natDegree = 0 := by
  first
  | classical
    let N := P.natDegree
    have heq (n : ℕ) :
        δ n ^ N * P.eval₂ (Polynomial.evalRingHom (z n)) (h n) =
          ∑ k ∈ Finset.range (N + 1),
            (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k) := by
      rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
      simp only [Polynomial.coe_evalRingHom]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hpow : δ n ^ N = δ n ^ k * δ n ^ (N - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkN]
      rw [hpow, mul_pow]
      ring
    have hterm (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
        Tendsto (fun n => (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k))
          atTop (𝓝 (if k = N then P.leadingCoeff.eval ζ * β ^ N else 0)) := by
      have hc := (P.coeff k).continuous.continuousAt.tendsto.comp hz
      have ht := (hc.mul (hres.pow k)).mul (hδ.pow (N - k))
      by_cases he : k = N
      · subst k
        simpa only [N, Function.comp_apply, Nat.sub_self, pow_zero, mul_one,
          if_pos rfl, ite_true, Polynomial.leadingCoeff] using ht
      · have hkN : k < N := lt_of_le_of_ne
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he
        have hsub : N - k ≠ 0 := Nat.sub_ne_zero_of_lt hkN
        simpa [he, zero_pow hsub] using ht
    have hsum : Tendsto (fun n => ∑ k ∈ Finset.range (N + 1),
        (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k))
        atTop (𝓝 (P.leadingCoeff.eval ζ * β ^ N)) := by
      simpa using tendsto_finsetSum (Finset.range (N + 1)) hterm
    have hzero : Tendsto (fun n => ∑ k ∈ Finset.range (N + 1),
        (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k)) atTop (𝓝 0) := by
      have hf : (fun n => ∑ k ∈ Finset.range (N + 1),
          (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k)) = fun _ => 0 := by
        funext n
        rw [← heq n, hrel, mul_zero]
      rw [hf]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hsum hzero

/-- Infinitely many distinct nonzero radial residues rule out every polynomial relation with
complex polynomial coefficients. Density is unnecessary for this algebraic assertion. -/
theorem weightedCauchySeries_no_polynomial_relation {ι : Type*} [Infinite ι]
    (β u : ι → ℂ) (hβ : Summable fun i => ‖β i‖)
    (hβne : ∀ i, β i ≠ 0) (hu : ∀ i, ‖u i‖ = 1) (huinj : Function.Injective u)
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ¬ ∀ z : ℂ, ‖z‖ < 1 →
      P.eval₂ (Polynomial.evalRingHom z) (weightedCauchySeries β u z) = 0 := by
  first
  | intro hrel
    have hroot (j : ι) : P.leadingCoeff.eval ((u j)⁻¹) = 0 := by
      have hrC : Tendsto (fun n => (radialSequence n : ℂ)) atTop (𝓝 1) := by
        simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp radialSequence_tendsto
      have hz : Tendsto (fun n => (radialSequence n : ℂ) / u j) atTop (𝓝 ((u j)⁻¹)) := by
        simpa only [one_div] using hrC.div_const (u j)
      have hδ : Tendsto (fun n => (1 : ℂ) - (radialSequence n : ℂ)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hrC
      have hc := radial_polynomial_leadingCoeff P
        (fun n => (radialSequence n : ℂ) / u j)
        (fun n => weightedCauchySeries β u ((radialSequence n : ℂ) / u j))
        (fun n => 1 - (radialSequence n : ℂ)) ((u j)⁻¹) (β j)
        hz hδ (weighted_radial_residue β u hβ hu huinj radialSequence
          radialSequence_nonneg radialSequence_lt_one radialSequence_tendsto j) (by
          intro n
          apply hrel
          simpa [norm_div, hu, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (radialSequence_nonneg n)] using radialSequence_lt_one n)
      exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (hβne j))
    have hinj : Function.Injective (fun j => (u j)⁻¹) := inv_injective.comp huinj
    have hinfinite : Set.Infinite {z : ℂ | P.leadingCoeff.IsRoot z} :=
      (Set.infinite_range_of_injective hinj).mono (by
        rintro z ⟨j, rfl⟩
        exact hroot j)
    exact (Polynomial.leadingCoeff_ne_zero.mpr hP)
      (P.leadingCoeff.eq_zero_of_infinite_isRoot hinfinite)

theorem sineGeneratingFunction_no_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ¬ ∀ z : ℂ, ‖z‖ < 1 →
      P.eval₂ (Polynomial.evalRingHom z) (sineGeneratingFunction θ z) = 0 := by
  first
  | intro hrel
    apply weightedCauchySeries_no_polynomial_relation sineFourierCoefficient (rotationFrequency θ)
      sineFourier_summable_norm sineFourier_ne_zero (rotationFrequency_norm θ)
      (rotationFrequency_injective hθ) P hP
    intro z hz
    rw [← sineGeneratingFunction_eq_cauchy θ z hz]
    exact hrel z hz

/-- Clearing the actual area denominator preserves a nonzero polynomial by `scaleRoots`.
Consequently the complete area formula has no polynomial relation over `ℂ[z]`. -/
theorem areaGeneratingFunction_no_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0)
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ¬ ∀ z : ℂ, ‖z‖ < 1 →
      P.eval₂ (Polynomial.evalRingHom z) (areaGeneratingFunction θ z) = 0 := by
  first
  | intro hrel
    let D : Polynomial ℂ := (1 - X ^ 2) * C (Real.sin θ : ℂ)
    apply sineGeneratingFunction_no_polynomial_relation hθ (P.scaleRoots D)
      (Polynomial.scaleRoots_ne_zero hP D)
    intro z hz
    have hD : D.eval z ≠ 0 := by
      simp only [D, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C]
      exact mul_ne_zero (one_sub_sq_ne_zero_of_norm_lt_one hz) (by exact_mod_cast hsin)
    have hDeval : D.eval z = (1 - z ^ 2) * (Real.sin θ : ℂ) := by
      simp [D]
    have hmul : D.eval z * areaGeneratingFunction θ z = sineGeneratingFunction θ z := by
      rw [areaGeneratingFunction, ← hDeval]
      field_simp [hD]
    have heq := Polynomial.scaleRoots_eval₂_eq_zero (s := D)
      (Polynomial.evalRingHom z) (hrel z hz)
    simpa only [Polynomial.coe_evalRingHom, hmul] using heq

end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RadialAlgebraicObstruction.lean -/

/- BEGIN SOURCE: VolumePolynomials/AreaTranscendence.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Set Filter Metric Polynomial

/-- The real area function displayed in (7.11), with the sum indexed from one. -/
def realAreaSeries (θ lam : ℝ) : ℝ :=
  (∑' n : ℕ, |Real.sin (((n + 1 : ℕ) : ℝ) * θ)| * lam ^ (n + 1)) /
    ((1 - lam ^ 2) * Real.sin θ)

theorem ofReal_realAreaSeries (θ lam : ℝ) :
    (realAreaSeries θ lam : ℂ) = areaGeneratingFunction θ (lam : ℂ) := by
  first
  | simp only [realAreaSeries, areaGeneratingFunction, sineGeneratingFunction,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_pow, Complex.ofReal_tsum]

/-- The complex identity theorem applied to zeros accumulating from the positive
real axis. An eventual identity near zero is enough. -/
theorem analytic_zero_on_disk_of_right_germ (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hz : ∀ᶠ x : ℝ in 𝓝[>] 0, f (x : ℂ) = 0) :
    Set.EqOn f 0 (ball 0 1) := by
  first
  | let r : ℕ → ℝ := fun n => (1 / 2) * (1 / 2) ^ n
    have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
    have hr : Tendsto r atTop (𝓝 0) := by
      simpa [r] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (1 / 2 : ℝ)
    have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    have hrRight : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hr, Filter.Eventually.of_forall hrpos⟩
    have hzeros : ∀ᶠ n in atTop, f (r n : ℂ) = 0 := hrRight.eventually hz
    have hclosure : (0 : ℂ) ∈ closure ({z : ℂ | f z = 0} \ {0}) := by
      apply mem_closure_of_tendsto hrC
      filter_upwards [hzeros] with n hn
      refine ⟨hn, ?_⟩
      simpa using (show (r n : ℂ) ≠ 0 by exact_mod_cast (hrpos n).ne')
    exact hf.eqOn_zero_of_preconnected_of_mem_closure (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
      (mem_ball_self (by norm_num)) hclosure

/-- The complex identity theorem applied to an actual real interval inside the disk. -/
theorem analytic_zero_on_disk_of_real_interval (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hz : ∀ x : ℝ, x ∈ Ioo 0 1 → f (x : ℂ) = 0) :
    Set.EqOn f 0 (ball 0 1) := by
  first
  | apply analytic_zero_on_disk_of_right_germ f hf
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact hz x hx

theorem analytic_bivariate_relation (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (ball 0 1))
    (P : Polynomial (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (fun z => P.eval₂ (Polynomial.evalRingHom z) (F z)) (ball 0 1) := by
  first
  | simp_rw [Polynomial.eval₂_eq_sum_range, Polynomial.coe_evalRingHom]
    apply Finset.analyticOnNhd_fun_sum
    intro n hn
    exact ((AnalyticOnNhd.eval_polynomial (P.coeff n)).mono (Set.subset_univ _)).mul (hF.pow n)

/-- A real polynomial in two variables, lifted coefficientwise to the complex numbers. -/
def complexifyBivariate (P : Polynomial (Polynomial ℝ)) : Polynomial (Polynomial ℂ) :=
  P.map (Polynomial.mapRingHom Complex.ofRealHom)

theorem complexifyBivariate_ne_zero {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0) :
    complexifyBivariate P ≠ 0 := by
  first
  | apply (Polynomial.map_ne_zero_iff (Polynomial.map_injective Complex.ofRealHom
      Complex.ofReal_injective)).mpr hP

theorem complexifyBivariate_eval (P : Polynomial (Polynomial ℝ)) (x y : ℝ) :
    (complexifyBivariate P).eval₂ (Polynomial.evalRingHom (x : ℂ)) (y : ℂ) =
      ((P.eval₂ (Polynomial.evalRingHom x) y : ℝ) : ℂ) := by
  first
  | have hcomp : (Polynomial.evalRingHom (x : ℂ)).comp
        (Polynomial.mapRingHom Complex.ofRealHom) =
          Complex.ofRealHom.comp (Polynomial.evalRingHom x) := by
      apply RingHom.ext
      intro p
      change (p.map Complex.ofRealHom).eval (Complex.ofRealHom x) =
        Complex.ofRealHom (p.eval x)
      exact Polynomial.eval_map_apply (p := p) Complex.ofRealHom x
    rw [complexifyBivariate, Polynomial.eval₂_map, hcomp]
    exact (Polynomial.hom_eval₂ (p := P) (f := Polynomial.evalRingHom x)
      (g := Complex.ofRealHom) (x := y)).symm

/-- No nonzero polynomial with arbitrary real coefficients can vanish on the graph of the
area function over the full parameter interval `(0,1)`. This is the polynomial-relation form
of transcendence over `ℝ(lam)`. -/
theorem realAreaSeries_no_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0)
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) :
    ¬ ∀ lam : ℝ, lam ∈ Ioo 0 1 →
      P.eval₂ (Polynomial.evalRingHom lam) (realAreaSeries θ lam) = 0 := by
  first
  | intro hrel
    have hreal : ∀ lam : ℝ, lam ∈ Ioo 0 1 →
        (complexifyBivariate P).eval₂ (Polynomial.evalRingHom (lam : ℂ))
          (areaGeneratingFunction θ (lam : ℂ)) = 0 := by
      intro lam hlam
      rw [← ofReal_realAreaSeries, complexifyBivariate_eval, hrel lam hlam]
      simp
    have hall := analytic_zero_on_disk_of_real_interval _
      (analytic_bivariate_relation _ (areaGeneratingFunction_analyticOnNhd θ hsin)
        (complexifyBivariate P)) hreal
    apply areaGeneratingFunction_no_polynomial_relation hθ hsin (complexifyBivariate P)
      (complexifyBivariate_ne_zero hP)
    intro z hz
    exact hall (by simpa using hz)

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AreaTranscendence.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolonomyArea.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

open scoped Topology
open Set MeasureTheory

theorem weighted_determinant_series (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (∑' j, ∑ i ∈ Finset.range j,
      |PlanarExtrusion.determinant (weightedOrbit lam i) (weightedOrbit lam j)|) =
      realAreaSeries angle lam := by
  first
  | let c : ℕ → ℝ := fun n =>
      |Real.sin (((n + 1 : ℕ) : ℝ) * angle)| * lam ^ (n + 1) / Real.sin angle
    have hgeom : Summable (fun n : ℕ => lam ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hlam₀ hlam₁)
    have hc : Summable c := by
      have hsin : 0 < Real.sin angle := sin_angle_pos
      apply (hgeom.div_const (Real.sin angle)).of_norm_bounded
      intro n
      have hnonneg : 0 ≤ c n := by dsimp [c]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (pow_nonneg hlam₀ (n + 1)) (Real.abs_sin_le_one _))
        sin_angle_pos.le
    have hlamsq : lam ^ 2 < 1 := (sq_lt_one_iff₀ hlam₀).mpr hlam₁
    have ha : Summable (fun n : ℕ => (lam ^ 2) ^ n) :=
      summable_geometric_of_lt_one (sq_nonneg lam) hlamsq
    have hrow (n : ℕ) :
        (∑ i ∈ Finset.range (n + 1),
          |PlanarExtrusion.determinant (weightedOrbit lam i) (weightedOrbit lam (n + 1))|) =
        ∑ i ∈ Finset.range (n + 1), (lam ^ 2) ^ i * c (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hind : n + 1 = i + ((n - i) + 1) := by
        have h := Finset.mem_range.mp hi
        omega
      change |det (weightedOrbit lam i) (weightedOrbit lam (n + 1))| = _
      rw [hind]
      exact abs_det_weighted_gap lam hlam₀ i (n - i)
    have hrows := determinant_rows_summable (weightedOrbit lam) (weightedOrbit_summable lam hlam₀ hlam₁)
    rw [hrows.tsum_eq_zero_add]
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    simp_rw [hrow]
    rw [← tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha.norm hc.norm]
    have hnormsq : ‖lam ^ 2‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg lam)]
      using hlamsq
    rw [tsum_geometric_of_norm_lt_one hnormsq]
    change (1 - lam ^ 2)⁻¹ *
      (∑' n : ℕ, |Real.sin (((n + 1 : ℕ) : ℝ) * angle)| * lam ^ (n + 1) /
        Real.sin angle) = realAreaSeries angle lam
    rw [tsum_div_const]
    simp only [realAreaSeries, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Formula (7.11) is the actual Lebesgue area of the uniquely forced compact convex body. -/
theorem forcedBody_area (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    volume.real (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) = realAreaSeries angle lam := by
  first
  | rw [forcedBody, area_infinite_segment_series, weighted_determinant_series lam hlam₀ hlam₁]

theorem forcedBody_area_positive (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    0 < volume.real (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
  first
  | rw [forcedBody, area_infinite_segment_series]
    have hs := determinant_rows_summable (weightedOrbit lam)
      (weightedOrbit_summable lam hlam₀.le hlam₁)
    have hle := hs.le_tsum 1 (fun j _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
    have hone : (∑ i ∈ Finset.range 1,
        |PlanarExtrusion.determinant (weightedOrbit lam i) (weightedOrbit lam 1)|) = lam := by
      simp [weightedOrbit, orbit, returnMap, PlanarExtrusion.determinant, abs_of_pos hlam₀]
    rw [hone] at hle
    exact hlam₀.trans_le hle

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolonomyArea.lean -/

/- BEGIN SOURCE: VolumePolynomials/CanonicalShapeConditions.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

theorem canonicalTuple_planarA (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (planarA (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | change coordinateProjection 2 ''
      (placedA '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) = _
    simp only [placedA, Set.image_image, Function.comp_apply,
      coordinateProjection_embedXY, Set.image_id']

theorem canonicalTuple_planarB (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (planarB (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | change coordinateProjection 1 ''
      (placedB '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) = _
    simp only [placedB, Set.image_image, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      coordinateProjection_embedXZ]

theorem canonicalTuple_planarC (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (planarC (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      transport12 '' (transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) := by
  first
  | change coordinateProjection 0 ''
      (placedC '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) = _
    simp only [placedC, Set.image_image, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      coordinateProjection_embedYZ]

theorem canonicalTuple_projectionAB (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    transport01 '' (planarB (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | rw [canonicalTuple_planarB]
    simp [Set.image_image, Function.comp_def, transport01_apply]

theorem canonicalTuple_projectionBC (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    transport12 '' (planarC (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      (planarB (canonicalTuple lam hlam₀ hlam₁) : Set Plane) := by
  first
  | rw [canonicalTuple_planarC, canonicalTuple_planarB]
    have h12 (p : Plane) : transport12 (transport12 p) = p := by
      ext <;> simp only [transport12_apply, neg_neg]
    rw [Set.image_image]
    simp only [h12, Set.image_id']

theorem canonicalTuple_projectionAD (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    lastProjectedSet lam (planarC (canonicalTuple lam hlam₀ hlam₁)) =
      (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | rw [canonicalTuple_planarC, lastProjectedSet, image_transport_cycle,
      ← forcedBody_fixed lam hlam₀ hlam₁]

theorem area_double_convex {A : Set Plane} (hA : Convex ℝ A) :
    volume.real (A + A) = 4 * volume.real A := by
  first
  | have hsum : A + A = (2 : ℝ) • A := by
      simpa only [one_smul, one_add_one_eq_two] using
        (hA.add_smul (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)).symm
    have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
    rw [hsum]
    change (volume ((2 : ℝ) • A)).toReal = 4 * (volume A).toReal
    rw [Measure.addHaar_smul_of_nonneg volume (show (0 : ℝ) ≤ 2 by norm_num),
      hdim, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    norm_num

/-- The explicit nine-body construction satisfies every equation and every
strict inequality of the finite rational system throughout the full interval. -/
theorem canonicalTuple_ordinaryConditions (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    OrdinaryConditions lam (volume.real (forcedBody lam hlam₀.le hlam₁ : Set Plane))
      (volumeFunction (canonicalTuple lam hlam₀.le hlam₁)) := by
  first
  | let K := canonicalTuple lam hlam₀.le hlam₁
    have hK : IsCalibratedTuple K := canonicalTuple_calibrated lam hlam₀.le hlam₁
    have hPA : (planarA K : Set Plane) = (forcedBody lam hlam₀.le hlam₁ : Set Plane) :=
      canonicalTuple_planarA lam hlam₀.le hlam₁
    have hPB : (planarB K : Set Plane) = transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) :=
      canonicalTuple_planarB lam hlam₀.le hlam₁
    have hPC : (planarC K : Set Plane) =
        transport12 '' (transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane)) :=
      canonicalTuple_planarC lam hlam₀.le hlam₁
    have hAB := canonicalTuple_projectionAB lam hlam₀.le hlam₁
    have hBC := canonicalTuple_projectionBC lam hlam₀.le hlam₁
    have hAD := canonicalTuple_projectionAD lam hlam₀.le hlam₁
    have hpos := forcedBody_area_positive lam hlam₀ hlam₁
    change OrdinaryConditions lam (volume.real (forcedBody lam hlam₀.le hlam₁ : Set Plane))
      (volumeFunction K)
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hs : K (segmentIndex i) = centeredBody (calibratedDirection i) := hK.segments i
      have hf : K (frameIndex j) = centeredBody (axis j) := by
        fin_cases j <;> rfl
      rw [volumeFunction, weightedSum_two, hs, hf, volume_two_centered_segments]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, e₁, e₂, e₃,
          volume_three_centered_segments, determinant3, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, sᵥ, e₂, e₃,
          volume_three_centered_segments, determinant3, directionV, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, sᵥ, e₁, e₃,
          volume_three_centered_segments, determinant3, directionV, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, sᵥ, e₁, e₂,
          volume_three_centered_segments, determinant3, directionV, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓌, e₂, e₃,
          volume_three_centered_segments, determinant3, directionW, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓌, e₁, e₃,
          volume_three_centered_segments, determinant3, directionW, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓌, e₁, e₂,
          volume_three_centered_segments, determinant3, directionW, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓏, e₂, e₃,
          volume_three_centered_segments, determinant3, directionZ, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓏, e₁, e₃,
          volume_three_centered_segments, determinant3, directionZ, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓏, e₁, e₂,
          volume_three_centered_segments, determinant3, directionZ, axis, Pi.single_apply]
      · rw [volumeFunction, weightedSum_three]
        change bodyVolume (centeredBody directionV + centeredBody directionW + centeredBody directionZ) = _
        rw [volume_three_centered_segments, calibrated_determinant]
      · simpa only [volumeFunction, weightedSum_three] using hK.volume_planeA
      · simpa only [volumeFunction, weightedSum_three] using hK.volume_planeB
      · simpa only [volumeFunction, weightedSum_three] using hK.volume_planeC
      · rw [hK.extrusion_VA, hK.extrusion_VB, hPA, hAB]
      · rw [hK.extrusion_VAB, hK.extrusion_VA, hPA, hAB]
        exact area_double_convex (forcedBody lam hlam₀.le hlam₁).convex
      · rw [hK.extrusion_WB, hK.extrusion_WC, hBC]
      · rw [hK.extrusion_WBC, hK.extrusion_WB, hBC]
        exact area_double_convex (planarB K).convex
      · rw [hK.extrusion_ZA, hK.extrusion_ZD lam hlam₀.le, hPA, hAD]
      · rw [hK.extrusion_ZAD lam hlam₀.le, hK.extrusion_ZA, hPA, hAD]
        exact area_double_convex (forcedBody lam hlam₀.le hlam₁).convex
      · rw [hK.extrusion_axisA, hPA]
    · refine ⟨hlam₀, hlam₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hK.extrusion_axisA, hPA] using hpos
      · simpa only [hK.extrusion_axisB, hPB, area_transport01] using hpos
      · simpa only [hK.extrusion_axisC, hPC, area_transport12, area_transport01] using hpos
      · simpa only [hK.extrusion_VA, hPA] using hpos
      · simpa only [hK.extrusion_WB, hPB, area_transport01] using hpos
      · simpa only [hK.extrusion_ZA, hPA] using hpos

theorem canonicalTuple_feasible (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    Feasible lam (realAreaSeries angle lam) := by
  first
  | obtain ⟨c, hc⟩ := canonicalTuple_realizes lam hlam₀.le hlam₁
    refine ⟨c, ⟨canonicalTuple lam hlam₀.le hlam₁, hc⟩, ?_⟩
    apply (holds_iff_ordinary_volume hlam₀.le hc).mpr
    rw [← forcedBody_area lam hlam₀.le hlam₁]
    exact canonicalTuple_ordinaryConditions lam hlam₀ hlam₁


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CanonicalShapeConditions.lean -/

/- BEGIN SOURCE: VolumePolynomials/InfiniteBoundarySegments.lean -/
section


@[expose] public section

/-!
# Infinitely many nonparallel boundary segments exclude semialgebraicity

This is the geometric-to-algebraic obstruction used for the forced Minkowski
series in Theorem 7.3. The statement concerns actual subsets of the real plane.
No convexity or smoothness is needed for this obstruction.

The proof uses polynomial roots over the integral domain `ℝ[X]`: every
nonhorizontal boundary segment on which a bivariate polynomial vanishes gives
an affine polynomial root. Pairwise nonparallel directions give distinct roots.
-/

open Polynomial Set
open scoped Polynomial.Bivariate

namespace VolumePolynomials

noncomputable def segmentLinePolynomial (a u : ℝ × ℝ) : ℝ[X] :=
  C (a.1 - u.1 / u.2 * a.2) + C (u.1 / u.2) * X

theorem segmentLinePolynomial_eval (a u : ℝ × ℝ) (hu : u.2 ≠ 0) (t : ℝ) :
    (segmentLinePolynomial a u).eval (a.2 + t * u.2) = a.1 + t * u.1 := by
  simp only [segmentLinePolynomial, eval_add, eval_C, eval_mul, eval_X]
  field_simp [hu]
  ring

/-- Vanishing on a genuine segment makes its affine line a polynomial root. -/
theorem line_isRoot_of_segment_vanishing (p : ℝ[X][Y]) (a u : ℝ × ℝ)
    (hu : u.2 ≠ 0)
    (hzero : ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      p.evalEval (a.2 + t * u.2) (a.1 + t * u.1) = 0) :
    p.IsRoot (segmentLinePolynomial a u) := by
  change p.eval (segmentLinePolynomial a u) = 0
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Set.InjOn (fun t : ℝ => a.2 + t * u.2)
      (Icc (-1 / 2 : ℝ) (1 / 2)) := by
    intro t ht v hv h
    have hmul : (t - v) * u.2 = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hu)
  have hinfinite : ((fun t : ℝ => a.2 + t * u.2) ''
      Icc (-1 / 2 : ℝ) (1 / 2)).Infinite :=
    (Set.Icc_infinite (show (-1 / 2 : ℝ) < 1 / 2 by norm_num)).image hinj
  apply hinfinite.mono
  rintro y ⟨t, ht, rfl⟩
  change (p.eval (segmentLinePolynomial a u)).eval (a.2 + t * u.2) = 0
  rw [bivariate_eval_polynomial, segmentLinePolynomial_eval a u hu t]
  exact hzero t ht

theorem segmentLinePolynomial_ne_of_det_ne_zero (a b u v : ℝ × ℝ)
    (hu : u.2 ≠ 0) (hv : v.2 ≠ 0)
    (hdet : u.1 * v.2 - u.2 * v.1 ≠ 0) :
    segmentLinePolynomial a u ≠ segmentLinePolynomial b v := by
  intro h
  have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 1) h
  have hslope : u.1 / u.2 = v.1 / v.2 := by
    simpa [segmentLinePolynomial] using hcoeff
  have hcross := (div_eq_div_iff hu hv).mp hslope
  apply hdet
  nlinarith

/-- A real polynomial in two variables cannot vanish on countably many
segments in pairwise nonparallel directions unless it is zero. -/
theorem bivariate_eq_zero_of_nonparallel_segments (p : ℝ[X][Y])
    (a u : ℕ → ℝ × ℝ)
    (hnonparallel : ∀ i j : ℕ, i ≠ j →
      (u i).1 * (u j).2 - (u i).2 * (u j).1 ≠ 0)
    (hzero : ∀ i : ℕ, ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      p.evalEval ((a i).2 + t * (u i).2) ((a i).1 + t * (u i).1) = 0) :
    p = 0 := by
  by_contra hp
  let J : Set ℕ := {i | (u i).2 ≠ 0}
  have hmap : Set.MapsTo (fun i => segmentLinePolynomial (a i) (u i)) J
      {q : ℝ[X] | p.IsRoot q} := by
    intro i hi
    exact line_isRoot_of_segment_vanishing p (a i) (u i) hi (hzero i)
  have hinj : Set.InjOn (fun i => segmentLinePolynomial (a i) (u i)) J := by
    intro i hi j hj hij
    by_contra hne
    exact (segmentLinePolynomial_ne_of_det_ne_zero (a i) (a j) (u i) (u j)
      hi hj (hnonparallel i j hne)) hij
  have hfinite : J.Finite :=
    Set.Finite.of_injOn hmap hinj (Polynomial.finite_setOfPred_isRoot hp)
  have hexceptional : Jᶜ.Subsingleton := by
    intro i hi j hj
    by_contra hne
    have hui : (u i).2 = 0 := by simpa only [J, mem_compl_iff, mem_ofPred_eq, not_not] using hi
    have huj : (u j).2 = 0 := by simpa only [J, mem_compl_iff, mem_ofPred_eq, not_not] using hj
    apply hnonparallel i j hne
    simp only [hui, huj, mul_zero, zero_mul, sub_self]
  have hall : (Set.univ : Set ℕ).Finite := by
    simpa only [union_compl_self] using hfinite.union hexceptional.finite
  exact Set.infinite_univ hall

/-- A planar set with the indicated boundary segments is not semialgebraic.
The coordinate conversion is an actual homeomorphism of the real plane. -/
theorem not_semialgebraic_of_nonparallel_boundary_segments
    (s : Set (ℝ × ℝ)) (a u : ℕ → ℝ × ℝ)
    (hnonparallel : ∀ i j : ℕ, i ≠ j →
      (u i).1 * (u j).2 - (u i).2 * (u j).1 ≠ 0)
    (hsegment : ∀ i : ℕ, ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      a i + t • u i ∈ frontier s) :
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹' s) := by
  intro hs
  obtain ⟨p, hp, hzero⟩ := frontier_polynomial_relation hs
  have hpoly : twoVariableEquiv p = 0 := by
    apply bivariate_eq_zero_of_nonparallel_segments (twoVariableEquiv p) a u hnonparallel
    intro i t ht
    rw [twoVariableEquiv_eval]
    apply hzero
    rw [← Homeomorph.preimage_frontier]
    change a i + t • u i ∈ frontier s
    exact hsegment i t ht
  exact hp (twoVariableEquiv.injective (by simpa using hpoly))

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/InfiniteBoundarySegments.lean -/

/- BEGIN SOURCE: VolumePolynomials/AffineSemialgebraic.lean -/
section


@[expose] public section
noncomputable section

open scoped BigOperators

namespace VolumePolynomials

/-- The actual coordinate polynomial of an affine map between finite real
coordinate spaces.  All coefficients are determined by the linear map. -/
def affineCoordinatePolynomial {n m : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (v : Fin m → ℝ) (j : Fin m) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (v j) +
    ∑ i : Fin n, MvPolynomial.C (L (Pi.single i 1) j) * MvPolynomial.X i

@[simp] theorem eval_affineCoordinatePolynomial {n m : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (v : Fin m → ℝ)
    (x : Fin n → ℝ) (j : Fin m) :
    MvPolynomial.eval x (affineCoordinatePolynomial L v j) = (v + L x) j := by
  first
  | have hx : ∑ i : Fin n, x i • (Pi.single i 1 : Fin n → ℝ) = x := by
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
        (Pi.basisFun ℝ (Fin n)).sum_repr x
    have hL : L x = ∑ i : Fin n, x i • L (Pi.single i 1) := by
      calc
        L x = L (∑ i : Fin n, x i • (Pi.single i 1 : Fin n → ℝ)) := congrArg L hx.symm
        _ = _ := by rw [map_sum]; simp only [map_smul]
    have hc := congrArg (fun y : Fin m → ℝ => y j) hL
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hc
    simp only [affineCoordinatePolynomial, MvPolynomial.eval_add, MvPolynomial.eval_C,
      MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.add_apply]
    congr 1
    rw [hc]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Preimages under arbitrary affine maps preserve the exact finite Boolean
polynomial-sign definition of semialgebraicity. -/
theorem _root_.TauCeti.IsSemialgebraic.preimage_affine {n m : ℕ}
    {S : Set (Fin m → ℝ)} (hS : TauCeti.IsSemialgebraic S)
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (v : Fin m → ℝ) :
    TauCeti.IsSemialgebraic ((fun x => v + L x) ⁻¹' S) := by
  first
  | simpa only [eval_affineCoordinatePolynomial] using
      hS.preimage_eval (affineCoordinatePolynomial L v)

theorem not_semialgebraic_affine_image {n m : ℕ} {S : Set (Fin n → ℝ)}
    (hS : ¬ TauCeti.IsSemialgebraic S)
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hL : Function.Injective L)
    (v : Fin m → ℝ) :
    ¬ TauCeti.IsSemialgebraic ((fun x => v + L x) '' S) := by
  first
  | intro h
    have hpre := h.preimage_affine L v
    have hinj : Function.Injective (fun x => v + L x) := by
      intro x y hxy
      exact hL (add_left_cancel hxy)
    rw [Set.preimage_image_eq S hinj] at hpre
    exact hS hpre


end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AffineSemialgebraic.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolonomyNonsemialgebraic.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

/-- The exact infinite Minkowski body of (7.10) is not a semialgebraic subset of the plane. -/
theorem forcedBody_not_semialgebraic (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
      (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) := by
  first
  | obtain ⟨a, ha⟩ := forcedBody_boundary_segments lam hlam₀ hlam₁
    exact not_semialgebraic_of_nonparallel_boundary_segments _ a (weightedOrbit lam)
      (weightedOrbit_nonparallel lam hlam₀) (by simpa only [neg_div] using ha)

/-- Nonsemialgebraicity persists under every injective affine placement into any
finite-dimensional coordinate space, including the specified body in 3D. -/
theorem forcedBody_affine_image_not_semialgebraic
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) {m : ℕ}
    (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hL : Function.Injective L)
    (v : Fin m → ℝ) :
    ¬ TauCeti.IsSemialgebraic ((fun x => v + L x) ''
      ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
        (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)))) :=
  not_semialgebraic_affine_image (forcedBody_not_semialgebraic lam hlam₀ hlam₁) L hL v

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolonomyNonsemialgebraic.lean -/

/- BEGIN SOURCE: VolumePolynomials/AffineShapeTransfer.lean -/
section


@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

/-- A literal affine copy of a planar set inside three-space. The linear part
is injective, so this records affine equivalence with its two-dimensional image. -/
def AffineCopy (S : Set Plane) (T : Set ThreeSpace) : Prop :=
  ∃ v : ThreeSpace, ∃ f : Plane →L[ℝ] ThreeSpace,
    Function.Injective f ∧ T = v +ᵥ f '' S

/-- The affine-copy predicate is equivalent to an affine embedding whose linear
part has a genuine continuous linear left inverse on the whole ambient space.
This makes invertibility onto the displayed image explicit. -/
theorem affineCopy_iff_exists_linear_leftInverse (S : Set Plane) (T : Set ThreeSpace) :
    AffineCopy S T ↔
      ∃ (v : ThreeSpace) (f : Plane →L[ℝ] ThreeSpace)
        (g : ThreeSpace →L[ℝ] Plane),
        Function.LeftInverse g f ∧ T = v +ᵥ f '' S := by
  first
  | constructor
    · rintro ⟨v, f, hf, hT⟩
      obtain ⟨g, hg⟩ := f.toLinearMap.exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.mpr hf)
      refine ⟨v, f, g.toContinuousLinearMap, ?_, hT⟩
      intro x
      change g (f x) = x
      exact congrArg (fun L : Plane →ₗ[ℝ] Plane => L x) hg
    · rintro ⟨v, f, g, hgf, hT⟩
      exact ⟨v, f, hgf.injective, hT⟩

/-- An affine copy has actual mutually inverse affine maps on the two sets.
The inverse is defined on all of three-space, so the assertion does not rely on
an informal interpretation of an inverse on an image or on an extra hypothesis.
-/
theorem AffineCopy.exists_affine_inverse {S : Set Plane} {T : Set ThreeSpace}
    (h : AffineCopy S T) :
    ∃ (F : Plane →ᵃ[ℝ] ThreeSpace) (G : ThreeSpace →ᵃ[ℝ] Plane),
      Function.LeftInverse G F ∧ F '' S = T ∧ G '' T = S ∧
        ∀ y ∈ T, F (G y) = y := by
  first
  | obtain ⟨v, f, g, hgf, hT⟩ :=
      (affineCopy_iff_exists_linear_leftInverse S T).mp h
    let F : Plane →ᵃ[ℝ] ThreeSpace :=
      { toFun := fun x => v + f x
        linear := f.toLinearMap
        map_vadd' := by
          first
          | intro p w
            simp only [vadd_eq_add, map_add, ContinuousLinearMap.coe_coe]
            abel }
    let G : ThreeSpace →ᵃ[ℝ] Plane :=
      { toFun := fun y => g (y - v)
        linear := g.toLinearMap
        map_vadd' := by
          first
          | intro p w
            change g (w + p - v) = g w + g (p - v)
            rw [add_sub_assoc, map_add] }
    have hGF : Function.LeftInverse G F := by
      first
      | intro x
        change g (v + f x - v) = x
        simpa only [add_sub_cancel_left] using hgf x
    have hFT : F '' S = T := by
      first
      | change (fun x => v + f x) '' S = T
        rw [hT, ← Set.image_vadd, Set.image_image]
        rfl
    refine ⟨F, G, hGF, hFT, ?_, ?_⟩
    · rw [← hFT, Set.image_image]
      have hfun : (fun x => G (F x)) = id := funext hGF
      rw [hfun, Set.image_id]
    · intro y hy
      rw [← hFT] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hGF x]

theorem AffinelyNormalized.undo_affineCopy {K L : Fin 9 → Body 3}
    (hKL : AffinelyNormalized K L) (i : Fin 9) (S : Set Plane)
    (E : Plane →L[ℝ] ThreeSpace) (hE : Function.Injective E) (a : ThreeSpace)
    (hshape : (L i : Set ThreeSpace) = a +ᵥ E '' S) :
    AffineCopy S (K i) := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    let f : Plane →L[ℝ] ThreeSpace := g.symm.toContinuousLinearMap.comp E
    refine ⟨-t i + g.symm a, f, g.symm.injective.comp hE, ?_⟩
    have heq : g '' (t i +ᵥ (K i : Set ThreeSpace)) = a +ᵥ E '' S := by
      first
      | have hh := congrArg (fun B : Body 3 => (B : Set ThreeSpace)) (ht i)
        simp only [coe_mapBody, coe_translateBody, ContinuousLinearEquiv.coe_coe] at hh
        exact hh.symm.trans hshape
    have hpre := congrArg (Set.image g.symm) heq
    have hpre' : t i +ᵥ (K i : Set ThreeSpace) = g.symm a +ᵥ f '' S := by
      first
      | have hf : (fun x => g.symm (E x)) = (f : Plane → ThreeSpace) := by
          funext x
          simp only [f, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
        simpa only [linear_image_vadd, Set.image_image, Function.comp_apply,
          ContinuousLinearEquiv.symm_apply_apply, Set.image_id', hf] using hpre
    have hshift := congrArg (fun T : Set ThreeSpace => -t i +ᵥ T) hpre'
    simpa only [vadd_vadd, vadd_eq_add, neg_add_cancel, zero_vadd] using hshift

theorem affineCopy_not_semialgebraic (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    {T : Set ThreeSpace} (hT : AffineCopy (forcedBody lam hlam₀.le hlam₁) T) :
    ¬ TauCeti.IsSemialgebraic T := by
  first
  | obtain ⟨v, f, hf, rfl⟩ := hT
    let L : (Fin 2 → ℝ) →ₗ[ℝ] ThreeSpace :=
      f.toLinearMap.comp (LinearEquiv.finTwoArrow ℝ ℝ).toLinearMap
    have hL : Function.Injective L := hf.comp (LinearEquiv.finTwoArrow ℝ ℝ).injective
    have hnon := forcedBody_affine_image_not_semialgebraic lam hlam₀ hlam₁ L hL v
    have heq : (fun x => v + L x) ''
        ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
          (forcedBody lam hlam₀.le hlam₁ : Set Plane)) =
        v +ᵥ f '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
      first
      | calc
          _ = (fun p : Plane => v + f p) ''
              ((Homeomorph.finTwoArrow (X := ℝ)) ''
                ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
                  (forcedBody lam hlam₀.le hlam₁ : Set Plane))) := by
            rw [Set.image_image]
            rfl
          _ = (fun p : Plane => v + f p) ''
              (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
            rw [Set.image_preimage_eq _ (Homeomorph.finTwoArrow (X := ℝ)).surjective]
          _ = _ := by
            rw [← Set.image_vadd, Set.image_image]
            rfl
    rwa [heq] at hnon

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AffineShapeTransfer.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolonomyEdges.lean -/
section


@[expose] public section
noncomputable section

open Set

namespace VolumePolynomials.Holonomy

/-- An exposed edge means the entire exposed face of a nonzero linear
functional is a nondegenerate closed segment. -/
def IsExposedEdge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K F : Set E) : Prop :=
  ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ F = l.toExposed K ∧
    ∃ a v : E, v ≠ 0 ∧
      F = {x | ∃ t : Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), x = a + (t : ℝ) • v}

theorem exposed_affine_image (l : Plane →L[ℝ] ℝ)
    (f : Plane →L[ℝ] ThreeSpace) (g : ThreeSpace →L[ℝ] Plane)
    (hgf : Function.LeftInverse g f) (v : ThreeSpace) (S : Set Plane) :
    (l.comp g).toExposed ((fun x => v + f x) '' S) =
      (fun x => v + f x) '' l.toExposed S := by
  first
  | ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro z hz
      have h := hmax (v + f z) ⟨z, hz, rfl⟩
      simpa only [ContinuousLinearMap.comp_apply, map_add, hgf z, hgf x,
        add_le_add_iff_left] using h
    · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      simpa only [ContinuousLinearMap.comp_apply, map_add, hgf z, hgf x,
        add_le_add_iff_left] using hmax z hz

theorem IsExposedEdge.affine_image {S R : Set Plane} (hR : IsExposedEdge S R)
    (f : Plane →L[ℝ] ThreeSpace) (g : ThreeSpace →L[ℝ] Plane)
    (hgf : Function.LeftInverse g f) (v : ThreeSpace) :
    IsExposedEdge ((fun x => v + f x) '' S) ((fun x => v + f x) '' R) := by
  first
  | obtain ⟨l, hl, hRl, a, u, hu, hsegment⟩ := hR
    refine ⟨l.comp g, ?_, ?_, v + f a, f u, ?_, ?_⟩
    · intro hz
      apply hl
      apply ContinuousLinearMap.ext
      intro x
      have h : (l.comp g) (f x) = 0 := by
        simp only [hz, ContinuousLinearMap.zero_apply]
      simpa only [ContinuousLinearMap.comp_apply, hgf x, ContinuousLinearMap.zero_apply] using h
    · rw [hRl, exposed_affine_image l f g hgf v S]
    · intro hz
      exact hu (hgf.injective (hz.trans (map_zero f).symm))
    · rw [hsegment]
      ext y
      constructor
      · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, by simp only [map_add, map_smul, add_assoc]⟩
      · rintro ⟨t, rfl⟩
        exact ⟨a + (t : ℝ) • u, ⟨t, rfl⟩,
          by simp only [map_add, map_smul, add_assoc]⟩

/-- The displayed exposed faces are pairwise different; this is an actual
infinite family of edges, not merely infinitely many normal descriptions. -/
theorem forcedBody_exposed_faces_injective (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    Function.Injective (fun j : ℕ =>
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) := by
  first
  | obtain ⟨a, ha⟩ := forcedBody_exposed_faces lam hlam₀ hlam₁
    intro i j hij
    change (orbitNormal lam i).toExposed (forcedBody lam hlam₀.le hlam₁ : Set Plane) =
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set Plane) at hij
    by_contra hne
    have hp : a i + (1 / 2 : ℝ) • weightedOrbit lam i ∈
        (orbitNormal lam i).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
      rw [ha i]
      exact ⟨⟨1 / 2, ⟨by norm_num, le_rfl⟩⟩, rfl⟩
    have hm : a i + (-(1 / 2) : ℝ) • weightedOrbit lam i ∈
        (orbitNormal lam i).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
      rw [ha i]
      exact ⟨⟨-(1 / 2), ⟨le_rfl, by norm_num⟩⟩, rfl⟩
    rw [hij] at hp hm
    have heq : orbitNormal lam j (a i + (1 / 2 : ℝ) • weightedOrbit lam i) =
        orbitNormal lam j (a i + (-(1 / 2) : ℝ) • weightedOrbit lam i) :=
      (hm.2 _ hp.1).antisymm (hp.2 _ hm.1)
    simp only [map_add, map_smul, smul_eq_mul] at heq
    have hz : orbitNormal lam j (weightedOrbit lam i) = 0 := by linarith
    exact weightedOrbit_nonparallel lam hlam₀ j i (Ne.symm hne) hz

theorem forcedBody_infinitely_many_exposed_edges
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    Set.Infinite {F : Set (ℝ × ℝ) |
      IsExposedEdge (forcedBody lam hlam₀.le hlam₁) F} := by
  first
  | obtain ⟨a, ha⟩ := forcedBody_exposed_faces lam hlam₀ hlam₁
    apply (Set.infinite_range_of_injective
      (forcedBody_exposed_faces_injective lam hlam₀ hlam₁)).mono
    rintro F ⟨j, rfl⟩
    refine ⟨orbitNormal lam j, ?_, rfl, a j, weightedOrbit lam j,
      weightedOrbit_ne_zero lam hlam₀ j, ha j⟩
    intro hz
    have hp := orbitNormal_positive_direction lam hlam₀ j
    simpa [hz] using hp

/-- Infinite exposed edges persist in every actual affine realization, with
the support functional extended to three-space using the proved left inverse. -/
theorem affineCopy_infinitely_many_exposed_edges
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    {T : Set ThreeSpace} (hT : AffineCopy (forcedBody lam hlam₀.le hlam₁) T) :
    Set.Infinite {R : Set ThreeSpace | IsExposedEdge T R} := by
  first
  | obtain ⟨v, f, g, hgf, hT⟩ :=
      (affineCopy_iff_exists_linear_leftInverse _ _).mp hT
    let F : Plane → ThreeSpace := fun x => v + f x
    have hF : Function.Injective F := by
      intro x y hxy
      exact hgf.injective (add_left_cancel hxy)
    have hTF : T = F '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
      rw [hT, ← Set.image_vadd, Set.image_image]
      rfl
    have hImage : Function.Injective (fun R : Set Plane => F '' R) := by
      intro R Q hRQ
      have h := congrArg (Set.preimage F) hRQ
      simpa only [Set.preimage_image_eq _ hF] using h
    apply ((forcedBody_infinitely_many_exposed_edges lam hlam₀ hlam₁).image hImage.injOn).mono
    rintro R ⟨Q, hQ, rfl⟩
    rw [hTF]
    exact IsExposedEdge.affine_image hQ f g hgf v


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolonomyEdges.lean -/

/- BEGIN SOURCE: VolumePolynomials/AreaRatFuncTranscendence.lean -/
section


@[expose] public section
noncomputable section

open Filter Polynomial Set Metric
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

/-- Germs of real functions on a right-hand neighborhood of zero. -/
abbrev PositiveRealGerm := Germ (𝓝[>] (0 : ℝ)) ℝ

theorem positive_nhds_le_cofinite : (𝓝[>] (0 : ℝ)) ≤ Filter.cofinite := by
  first
  | apply le_trans _ (nhdsNE_le_cofinite (0 : ℝ))
    exact nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)

/-- A nonzero real polynomial is invertible as a punctured right-hand germ,
even when it vanishes at zero itself. -/
theorem polynomial_evaluation_germ_isUnit (p : Polynomial ℝ) (hp : p ≠ 0) :
    IsUnit (germPolynomialEvaluation (𝓝[>] (0 : ℝ)) id p) := by
  first
  | have hne : ∀ᶠ x : ℝ in 𝓝[>] 0, p.eval x ≠ 0 :=
      (Polynomial.eventually_eval_ne_zero_cofinite hp).filter_mono positive_nhds_le_cofinite
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Germ.ofFun (fun x : ℝ => (p.eval x)⁻¹), ?_⟩
    change Germ.ofFun (fun x : ℝ => p.eval x * (p.eval x)⁻¹) =
      (Germ.ofFun (fun _ : ℝ => (1 : ℝ)) : PositiveRealGerm)
    apply Germ.coe_eq.mpr
    filter_upwards [hne] with x hx
    exact mul_inv_cancel₀ hx

/-- The standard rational function field is evaluated into actual right-hand
germs by the universal property of localization. -/
def rationalFunctionGermEvaluation : RatFunc ℝ →+* PositiveRealGerm :=
  IsLocalization.lift (S := RatFunc ℝ) (M := nonZeroDivisors (Polynomial ℝ))
    (g := germPolynomialEvaluation (𝓝[>] (0 : ℝ)) id)
    (fun p => polynomial_evaluation_germ_isUnit p (nonZeroDivisors.ne_zero p.property))

@[simp] theorem rationalFunctionGermEvaluation_polynomial (p : Polynomial ℝ) :
    rationalFunctionGermEvaluation (algebraMap (Polynomial ℝ) (RatFunc ℝ) p) =
      Germ.ofFun (fun x : ℝ => p.eval x) :=
  IsLocalization.lift_eq _ p

theorem rationalFunctionGermEvaluation_injective :
    Function.Injective rationalFunctionGermEvaluation := rationalFunctionGermEvaluation.injective

def rationalFunctionGermAlgebra : Algebra (RatFunc ℝ) PositiveRealGerm :=
  rationalFunctionGermEvaluation.toAlgebra

theorem realAreaSeries_no_right_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0) :
    ¬ HasPolynomialRelation (𝓝[>] (0 : ℝ)) id (realAreaSeries θ) := by
  first
  | rintro ⟨P, hP, hrel⟩
    have hreal : ∀ᶠ x : ℝ in 𝓝[>] 0,
        (complexifyBivariate P).eval₂ (Polynomial.evalRingHom (x : ℂ))
          (areaGeneratingFunction θ (x : ℂ)) = 0 := by
      filter_upwards [hrel] with x hx
      rw [← ofReal_realAreaSeries, complexifyBivariate_eval, Polynomial.eval₂_evalRingHom]
      simpa only [id_eq, hx, Complex.ofReal_zero] using congrArg Complex.ofReal hx
    have hall := analytic_zero_on_disk_of_right_germ _
      (analytic_bivariate_relation _ (areaGeneratingFunction_analyticOnNhd θ hsin)
        (complexifyBivariate P)) hreal
    apply areaGeneratingFunction_no_polynomial_relation hθ hsin (complexifyBivariate P)
      (complexifyBivariate_ne_zero hP)
    intro z hz
    exact hall (by simpa using hz)

/-- Literal transcendence over Mathlib's rational function field `RatFunc ℝ`.
The algebra structure evaluates the independent variable at the identity germ;
its injectivity is proved above. Polynomial-ring and fraction-field algebraicity
are equivalent by the kernel-checked denominator-clearing theorem. -/
theorem realAreaSeries_transcendental_ratFunc {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0) :
    letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
    Transcendental (RatFunc ℝ) (Germ.ofFun (realAreaSeries θ) : PositiveRealGerm) := by
  first
  | letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
    letI : Algebra (Polynomial ℝ) PositiveRealGerm :=
      (germPolynomialEvaluation (𝓝[>] (0 : ℝ)) id).toAlgebra
    letI : IsScalarTower (Polynomial ℝ) (RatFunc ℝ) PositiveRealGerm := by
      apply IsScalarTower.of_algebraMap_eq
      intro p
      exact (rationalFunctionGermEvaluation_polynomial p).symm
    intro h
    have hp : IsAlgebraic (Polynomial ℝ)
        (Germ.ofFun (realAreaSeries θ) : PositiveRealGerm) :=
      (IsFractionRing.isAlgebraic_iff (Polynomial ℝ) (RatFunc ℝ) PositiveRealGerm).mpr h
    exact realAreaSeries_no_right_polynomial_relation hθ hsin
      ((hasPolynomialRelation_iff_isAlgebraic (𝓝[>] (0 : ℝ)) id (realAreaSeries θ)).mpr hp)


end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AreaRatFuncTranscendence.lean -/

/- BEGIN SOURCE: VolumePolynomials/Theorem73.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

open scoped Pointwise
open Set MeasureTheory Metric

theorem return_pow_e1 (n : ℕ) : (returnContinuous ^ n) (1, 0) = orbit n := by
  first
  | rw [return_pow_apply]
    simp

theorem forcedBody_series_summable (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (t : SegmentChoice) :
    Summable (fun n => ((t n : ℝ) * lam ^ n) • (returnContinuous ^ n) (1, 0)) := by
  first
  | simpa only [weightedOrbit, smul_smul, return_pow_e1] using
      series_summable (weightedOrbit lam) (weightedOrbit_summable lam hlam₀ hlam₁) t

/-- The constructed body is exactly the infinite Minkowski sum in (7.10), interpreted as
all convergent choices of one point from every centered generating segment. -/
theorem forcedBody_eq_minkowski_series (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) =
      {x | ∃ t : SegmentChoice,
        x = ∑' n, ((t n : ℝ) * lam ^ n) • (returnContinuous ^ n) (1, 0)} := by
  first
  | ext x
    simp only [forcedBody_carrier, segmentSeries, Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      simp only [seriesPoint, weightedOrbit, smul_smul, return_pow_e1]
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [ht]
      simp only [seriesPoint, weightedOrbit, smul_smul, return_pow_e1]

/-- The exact compact-convex uniqueness assertion of Theorem 7.3. -/
theorem existsUnique_forced_body (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∃! K : ConvexBody (ℝ × ℝ), (K : Set (ℝ × ℝ)) =
      centeredSegment (1, 0) + scaledReturn lam '' (K : Set (ℝ × ℝ)) := by
  first
  | refine ⟨forcedBody lam hlam₀.le hlam₁, forcedBody_fixed lam hlam₀.le hlam₁, ?_⟩
    intro K hK
    apply SetLike.coe_injective
    exact forcedBody_unique lam hlam₀.le hlam₁ K K.isCompact K.nonempty hK

/-- The geometric conclusions of Theorem 7.3 for every parameter in its full range. -/
theorem theorem_7_3_geometric (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    (0 < volume.real (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) ∧
    (volume.real (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) = realAreaSeries angle lam) ∧
    (∃ a : ℕ → ℝ × ℝ, ∀ j,
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) =
        {x | ∃ t : Icc (- (1/2 : ℝ)) (1/2 : ℝ),
          x = a j + (t : ℝ) • weightedOrbit lam j}) ∧
    (∀ i j : ℕ, i ≠ j → det (weightedOrbit lam i) (weightedOrbit lam j) ≠ 0) ∧
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
      (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) := by
  first
  | exact ⟨forcedBody_area_positive lam hlam₀ hlam₁, forcedBody_area lam hlam₀.le hlam₁,
      forcedBody_exposed_faces lam hlam₀ hlam₁, weightedOrbit_nonparallel lam hlam₀,
      forcedBody_not_semialgebraic lam hlam₀ hlam₁⟩

/-- The analytic and algebraic conclusions of Theorem 7.3, for the actual area formula. -/
theorem theorem_7_3_analytic :
    AnalyticOnNhd ℂ (areaGeneratingFunction angle) (ball 0 1) ∧
    (∀ ζ : Circle, ¬ HasLocalContinuousExtension (areaGeneratingFunction angle) ζ) ∧
    (∀ n : ℕ, iteratedDeriv n (areaGeneratingFunction angle) 0 / (n.factorial : ℂ) =
      (areaTaylorCoefficient n : ℂ)) ∧
    (∀ P : Polynomial (Polynomial ℝ), P ≠ 0 →
      ¬ ∀ lam : ℝ, lam ∈ Ioo 0 1 →
        P.eval₂ (Polynomial.evalRingHom lam) (realAreaSeries angle lam) = 0) := by
  first
  | exact ⟨holonomy_area_analytic_properties.1, holonomy_area_analytic_properties.2.1,
      holonomy_area_analytic_properties.2.2,
      fun P hP => realAreaSeries_no_polynomial_relation cos_angle sin_angle_pos.ne' P hP⟩


/-- Transcendence in the literal rational-function field, evaluated at the
identity germ on a right-hand neighborhood of the origin. -/
theorem theorem_7_3_transcendentalRatFunc :
    letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
    Transcendental (RatFunc ℝ)
      (Filter.Germ.ofFun (realAreaSeries angle) : PositiveRealGerm) :=
  realAreaSeries_transcendental_ratFunc cos_angle sin_angle_pos.ne'



end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/Theorem73.lean -/

/- BEGIN SOURCE: VolumePolynomials/MainShape.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

/-- Exact graph projection of the explicit finite rational system. -/
theorem feasible_iff_area_graph (lam a : ℝ) :
    Feasible lam a ↔ 0 < lam ∧ lam < 1 ∧ a = realAreaSeries angle lam := by
  first
  | constructor
    · rintro ⟨c, ⟨K, hK⟩, hcond⟩
      have hv := hcond.ordinary_volume hK
      obtain ⟨L, hKL, hL⟩ := normalize_shape_conditions lam a K hv
      have hvL : OrdinaryConditions lam a (volumeFunction L) := by
        rw [hKL.volumeFunction_eq]
        exact hv
      obtain ⟨hlam₀, hlam₁, a₀, b₀, c₀, hA, hB, hC, ha⟩ :=
        calibrated_conditions_force_shape lam a L hL hvL
      exact ⟨hlam₀, hlam₁, ha.trans (forcedBody_area lam hlam₀.le hlam₁)⟩
    · rintro ⟨hlam₀, hlam₁, rfl⟩
      exact canonicalTuple_feasible lam hlam₀ hlam₁

/-- Every realization of every coefficient vector satisfying the system has
the specified body affinely equivalent to the exact infinite Minkowski sum. -/
theorem every_realization_forced (lam a : ℝ) (c : Coefficients 9 3)
    (K : Fin 9 → Body 3) (hreal : Realizes K c) (hcond : Holds lam a c) :
    ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
      AffineCopy (forcedBody lam hlam₀.le hlam₁) (K bodyA) ∧
      ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace) := by
  first
  | have hv := hcond.ordinary_volume hreal
    obtain ⟨L, hKL, hL⟩ := normalize_shape_conditions lam a K hv
    have hvL : OrdinaryConditions lam a (volumeFunction L) := by
      rw [hKL.volumeFunction_eq]
      exact hv
    obtain ⟨hlam₀, hlam₁, a₀, b₀, c₀, hA, hB, hC, ha⟩ :=
      calibrated_conditions_force_shape lam a L hL hvL
    have hcopy := hKL.undo_affineCopy bodyA (forcedBody lam hlam₀.le hlam₁)
      embedXY embedXY_injective (embedXY a₀) hA
    exact ⟨hlam₀, hlam₁, hcopy, affineCopy_not_semialgebraic lam hlam₀ hlam₁ hcopy⟩

/-- An actual volume polynomial with no semialgebraic realization exists. -/
theorem exists_no_semialgebraic_realization :
    ∃ c : Coefficients 9 3, c ∈ VolumeLocus 9 3 ∧
      ∀ K : Fin 9 → Body 3, Realizes K c →
        ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace) := by
  first
  | obtain ⟨c, hc, hcond⟩ := canonicalTuple_feasible (1 / 2) (by norm_num) (by norm_num)
    refine ⟨c, hc, ?_⟩
    intro K hK
    obtain ⟨hlam₀, hlam₁, hcopy, hnon⟩ :=
      every_realization_forced (1 / 2) (realAreaSeries angle (1 / 2)) c K hK hcond
    exact hnon

end VolumePolynomials.Holonomy

namespace VolumePolynomials.Main

open ShapeConditions Holonomy Metric

/-- Satisfaction of an arbitrary finite list of rational polynomial equalities
and strict inequalities in the parameters and all ordinary cubic coefficients. -/
def SatisfiesShapeSystem (P Q : List RationalPolynomial)
    (lam a : ℝ) (c : Coefficients 9 3) : Prop :=
  (∀ p ∈ P, polynomialValue lam a c p = 0) ∧
  (∀ q ∈ Q, 0 < polynomialValue lam a c q)

/-- The complete principal shape-forcing theorem (Theorem 1.2).

The two finite polynomial lists have rational coefficients by type. Their
projection is the exact area graph on the full open unit interval, every
realization has the prescribed affine copy, the body has an actually infinite
set of exposed edges, and the analytic area extension has rational Taylor
coefficients, a natural boundary, no nonzero real polynomial relation, and
literal transcendence over the rational-function field.
-/
theorem shape_forcing :
    ∃ P Q : List RationalPolynomial,
      P.length = 39 ∧ Q.length = 8 ∧
      (∀ lam a : ℝ,
        (∃ c ∈ VolumeLocus 9 3, SatisfiesShapeSystem P Q lam a c) ↔
          0 < lam ∧ lam < 1 ∧ a = realAreaSeries angle lam) ∧
      (∀ (lam a : ℝ) (c : Coefficients 9 3) (K : Fin 9 → Body 3),
        Realizes K c → SatisfiesShapeSystem P Q lam a c →
          ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
            AffineCopy (forcedBody lam hlam₀.le hlam₁) (K bodyA) ∧
            Set.Infinite {R : Set ThreeSpace | IsExposedEdge (K bodyA) R} ∧
            ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace)) ∧
      (∀ (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
        Set.Infinite {F : Set Plane | IsExposedEdge (forcedBody lam hlam₀.le hlam₁) F} ∧
        ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
          (forcedBody lam hlam₀.le hlam₁ : Set Plane))) ∧
      (∀ lam : ℝ, (realAreaSeries angle lam : ℂ) = areaGeneratingFunction angle (lam : ℂ)) ∧
      AnalyticOnNhd ℂ (areaGeneratingFunction angle) (ball 0 1) ∧
      (∀ ζ : Circle, ¬ HasLocalContinuousExtension (areaGeneratingFunction angle) ζ) ∧
      (∀ n : ℕ, iteratedDeriv n (areaGeneratingFunction angle) 0 / (n.factorial : ℂ) =
        (areaTaylorCoefficient n : ℂ)) ∧
      (∀ p : Polynomial (Polynomial ℝ), p ≠ 0 →
        ¬ ∀ lam : ℝ, lam ∈ Ioo 0 1 →
          p.eval₂ (Polynomial.evalRingHom lam) (realAreaSeries angle lam) = 0) ∧
      (letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
       Transcendental (RatFunc ℝ)
         (Filter.Germ.ofFun (realAreaSeries angle) : PositiveRealGerm)) := by
  first
  | refine ⟨equations, inequalities, equations_length, inequalities_length, ?_, ?_,
      ?_, ofReal_realAreaSeries angle, theorem_7_3_analytic.1,
      theorem_7_3_analytic.2.1, theorem_7_3_analytic.2.2.1, theorem_7_3_analytic.2.2.2,
      theorem_7_3_transcendentalRatFunc⟩
    · exact feasible_iff_area_graph
    · intro lam a c K hreal hcond
      obtain ⟨hlam₀, hlam₁, hcopy, hnon⟩ := every_realization_forced lam a c K hreal hcond
      exact ⟨hlam₀, hlam₁, hcopy,
        affineCopy_infinitely_many_exposed_edges lam hlam₀ hlam₁ hcopy, hnon⟩
    · intro lam hlam₀ hlam₁
      exact ⟨forcedBody_infinitely_many_exposed_edges lam hlam₀ hlam₁,
        forcedBody_not_semialgebraic lam hlam₀ hlam₁⟩


end VolumePolynomials.Main
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MainShape.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalElimination.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Executable elimination of rational linear inequalities

Fourier--Motzkin elimination is implemented by finite lists and rational
arithmetic. The correctness theorem quantifies over actual real solutions.
It includes inconsistent, empty, unbounded, and lower-dimensional systems;
no numerical tolerance or linear-programming oracle is used.
-/

open scoped BigOperators

namespace VolumePolynomials.RationalElimination

/-- A closed rational halfspace in a coordinate space. -/
structure Inequality (n : ℕ) where
  coefficient : Fin n → ℚ
  bound : ℚ
  deriving DecidableEq

namespace Inequality

def value {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (p.coefficient i : ℝ) * x i

def Holds {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) : Prop :=
  p.value x ≤ (p.bound : ℝ)

def tail {n : ℕ} (p : Inequality (n + 1)) : Inequality n :=
  ⟨fun i => p.coefficient i.castSucc, p.bound⟩

def last {n : ℕ} (p : Inequality (n + 1)) : ℚ := p.coefficient (Fin.last n)

/-- Eliminate the last variable between a negative and a positive coefficient.
Both original inequalities are multiplied by nonnegative rational scalars. -/
def combine {n : ℕ} (l u : Inequality (n + 1)) : Inequality n :=
  ⟨fun i => u.last * l.coefficient i.castSucc - l.last * u.coefficient i.castSucc,
    u.last * l.bound - l.last * u.bound⟩

theorem value_snoc {n : ℕ} (p : Inequality (n + 1)) (x : Fin n → ℝ) (t : ℝ) :
    p.value (Fin.snoc x t) = p.tail.value x + (p.last : ℝ) * t := by
  first
  | simp only [value, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    rfl

theorem combine_value {n : ℕ} (l u : Inequality (n + 1)) (x : Fin n → ℝ) :
    (combine l u).value x =
      (u.last : ℝ) * l.tail.value x - (l.last : ℝ) * u.tail.value x := by
  first
  | simp only [value, combine, tail, Rat.cast_sub, Rat.cast_mul, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

theorem holds_tail_of_zero {n : ℕ} (p : Inequality (n + 1))
    (hp : p.last = 0) (x : Fin n → ℝ) (t : ℝ) :
    p.Holds (Fin.snoc x t) ↔ p.tail.Holds x := by
  first
  | simp only [Holds, value_snoc, hp, Rat.cast_zero, zero_mul, add_zero, tail]

noncomputable def lower {n : ℕ} (p : Inequality (n + 1)) (x : Fin n → ℝ) : ℝ :=
  (p.tail.value x - (p.bound : ℝ)) / (-(p.last : ℝ))

noncomputable def upper {n : ℕ} (p : Inequality (n + 1)) (x : Fin n → ℝ) : ℝ :=
  ((p.bound : ℝ) - p.tail.value x) / (p.last : ℝ)

theorem holds_snoc_of_negative {n : ℕ} (p : Inequality (n + 1))
    (hp : p.last < 0) (x : Fin n → ℝ) (t : ℝ) :
    p.Holds (Fin.snoc x t) ↔ p.lower x ≤ t := by
  first
  | have hp' : (p.last : ℝ) < 0 := by exact_mod_cast hp
    rw [Holds, value_snoc, lower, div_le_iff₀ (neg_pos.mpr hp')]
    constructor <;> intro h <;> nlinarith only [h]

theorem holds_snoc_of_positive {n : ℕ} (p : Inequality (n + 1))
    (hp : 0 < p.last) (x : Fin n → ℝ) (t : ℝ) :
    p.Holds (Fin.snoc x t) ↔ t ≤ p.upper x := by
  first
  | have hp' : 0 < (p.last : ℝ) := by exact_mod_cast hp
    rw [Holds, value_snoc, upper, le_div_iff₀ hp']
    constructor <;> intro h <;> nlinarith only [h]

theorem holds_combine_iff {n : ℕ} (l u : Inequality (n + 1))
    (hl : l.last < 0) (hu : 0 < u.last) (x : Fin n → ℝ) :
    (combine l u).Holds x ↔ l.lower x ≤ u.upper x := by
  first
  | have hl' : (l.last : ℝ) < 0 := by exact_mod_cast hl
    have hu' : 0 < (u.last : ℝ) := by exact_mod_cast hu
    rw [Holds, combine_value, lower, upper,
      div_le_div_iff₀ (neg_pos.mpr hl') hu']
    simp only [combine, Rat.cast_sub, Rat.cast_mul]
    constructor <;> intro h <;> nlinarith only [h]

end Inequality

def Satisfies {n : ℕ} (S : List (Inequality n)) (x : Fin n → ℝ) : Prop :=
  ∀ p ∈ S, p.Holds x

/-- One elimination step. This definition has no noncomputable operations. -/
def eliminate {n : ℕ} (S : List (Inequality (n + 1))) : List (Inequality n) :=
  ((S.filter fun p => p.last = 0).map Inequality.tail) ++
    (S.filter fun p => p.last < 0).flatMap (fun l =>
      (S.filter fun p => 0 < p.last).map (Inequality.combine l))

theorem mem_zeroFilter {n : ℕ} (S : List (Inequality (n + 1))) (p : Inequality (n + 1)) :
    p ∈ S.filter (fun q => q.last = 0) ↔ p ∈ S ∧ p.last = 0 := by simp

theorem mem_negativeFilter {n : ℕ} (S : List (Inequality (n + 1)))
    (p : Inequality (n + 1)) :
    p ∈ S.filter (fun q => q.last < 0) ↔ p ∈ S ∧ p.last < 0 := by simp

theorem mem_positiveFilter {n : ℕ} (S : List (Inequality (n + 1)))
    (p : Inequality (n + 1)) :
    p ∈ S.filter (fun q => 0 < q.last) ↔ p ∈ S ∧ 0 < p.last := by simp

theorem satisfies_eliminate_iff {n : ℕ} (S : List (Inequality (n + 1)))
    (x : Fin n → ℝ) :
    Satisfies (eliminate S) x ↔
      (∀ p ∈ S, p.last = 0 → p.tail.Holds x) ∧
      (∀ l ∈ S, l.last < 0 → ∀ u ∈ S, 0 < u.last → (Inequality.combine l u).Holds x) := by
  first
  | constructor
    · intro h
      constructor
      · intro p hp hzero
        apply h
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨p, (mem_zeroFilter S p).mpr ⟨hp, hzero⟩, rfl⟩
      · intro l hl hneg u hu hpos
        apply h
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨l, (mem_negativeFilter S l).mpr ⟨hl, hneg⟩,
          List.mem_map.mpr ⟨u, (mem_positiveFilter S u).mpr ⟨hu, hpos⟩, rfl⟩⟩
    · rintro ⟨hz, hp⟩ p hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨hq, hzero⟩ := (mem_zeroFilter S q).mp hq
        exact hz q hq hzero
      · obtain ⟨l, hl, hmem⟩ := List.mem_flatMap.mp hmem
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨hl, hneg⟩ := (mem_negativeFilter S l).mp hl
        obtain ⟨hu, hpos⟩ := (mem_positiveFilter S u).mp hu
        exact hp l hl hneg u hu hpos

/-- A finite family of lower and upper real bounds has a common point exactly
when every lower bound is at most every upper bound. Empty families are allowed. -/
theorem exists_between_finite_bounds (L U : Finset ℝ)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u := by
  first
  | classical
    by_cases hL : L.Nonempty
    · refine ⟨L.max' hL, ?_, ?_⟩
      · intro l hl
        exact L.le_max' l hl
      · intro u hu
        exact L.max'_le hL u (fun l hl => h l hl u hu)
    · have hLe : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      by_cases hU : U.Nonempty
      · refine ⟨U.min' hU, ?_, ?_⟩
        · simp [hLe]
        · intro u hu
          exact U.min'_le u hu
      · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
        exact ⟨0, by simp [hLe], by simp [hUe]⟩

/-- Exact Fourier--Motzkin correctness over the real numbers. -/
theorem eliminate_correct {n : ℕ} (S : List (Inequality (n + 1))) (x : Fin n → ℝ) :
    Satisfies (eliminate S) x ↔ ∃ t : ℝ, Satisfies S (Fin.snoc x t) := by
  first
  | classical
    rw [satisfies_eliminate_iff]
    constructor
    · rintro ⟨hz, hp⟩
      let L := ((S.filter fun p => p.last < 0).map (fun p => p.lower x)).toFinset
      let U := ((S.filter fun p => 0 < p.last).map (fun p => p.upper x)).toFinset
      have hlu : ∀ l ∈ L, ∀ u ∈ U, l ≤ u := by
        intro l hl u hu
        obtain ⟨p, hpS, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
        obtain ⟨q, hqS, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
        obtain ⟨hpS, hpneg⟩ := (mem_negativeFilter S p).mp hpS
        obtain ⟨hqS, hqpos⟩ := (mem_positiveFilter S q).mp hqS
        exact (Inequality.holds_combine_iff p q hpneg hqpos x).mp
          (hp p hpS hpneg q hqS hqpos)
      obtain ⟨t, htL, htU⟩ := exists_between_finite_bounds L U hlu
      refine ⟨t, fun p hpS => ?_⟩
      rcases lt_trichotomy p.last 0 with hneg | hzero | hpos
      · apply (p.holds_snoc_of_negative hneg x t).mpr
        exact htL _ (List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨p, (mem_negativeFilter S p).mpr ⟨hpS, hneg⟩, rfl⟩))
      · exact (p.holds_tail_of_zero hzero x t).mpr (hz p hpS hzero)
      · apply (p.holds_snoc_of_positive hpos x t).mpr
        exact htU _ (List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨p, (mem_positiveFilter S p).mpr ⟨hpS, hpos⟩, rfl⟩))
    · rintro ⟨t, ht⟩
      constructor
      · intro p hp hzero
        exact (p.holds_tail_of_zero hzero x t).mp (ht p hp)
      · intro l hl hneg u hu hpos
        apply (Inequality.holds_combine_iff l u hneg hpos x).mpr
        exact ((l.holds_snoc_of_negative hneg x t).mp (ht l hl)).trans
          ((u.holds_snoc_of_positive hpos x t).mp (ht u hu))

/-- Eliminate a prescribed suffix of variables. The number of operations is
finite for every input; exponential growth does not affect computability. -/
def eliminateSuffix (n : ℕ) : (m : ℕ) → List (Inequality (n + m)) → List (Inequality n)
  | 0, S => S
  | m + 1, S => eliminateSuffix n m (eliminate S)

theorem eliminateSuffix_correct (n m : ℕ) (S : List (Inequality (n + m)))
    (x : Fin n → ℝ) :
    Satisfies (eliminateSuffix n m S) x ↔
      ∃ w : Fin m → ℝ, Satisfies S (Fin.append x w) := by
  first
  | induction m with
    | zero =>
        simp only [eliminateSuffix]
        constructor
        · intro h
          exact ⟨Fin.elim0, by simpa using h⟩
        · rintro ⟨w, hw⟩
          have hw0 : w = Fin.elim0 := by funext i; exact Fin.elim0 i
          simpa only [hw0, Fin.append_elim0, Fin.cast_refl, Function.comp_id] using hw
    | succ m ih =>
        rw [eliminateSuffix, ih]
        constructor
        · rintro ⟨w, hw⟩
          obtain ⟨t, ht⟩ := (eliminate_correct S (Fin.append x w)).mp hw
          exact ⟨Fin.snoc w t, by simpa only [Fin.append_snoc] using ht⟩
        · rintro ⟨w, hw⟩
          refine ⟨Fin.init w, (eliminate_correct S (Fin.append x (Fin.init w))).mpr
            ⟨w (Fin.last m), ?_⟩⟩
          simpa only [← Fin.append_snoc, Fin.snoc_init_self] using hw

def eliminateAll : {n : ℕ} → List (Inequality n) → List (Inequality 0)
  | 0, S => S
  | n + 1, S => eliminateAll (eliminate S)

theorem eliminateAll_correct {n : ℕ} (S : List (Inequality n)) :
    Satisfies (eliminateAll S) Fin.elim0 ↔ ∃ x, Satisfies S x := by
  first
  | induction n with
    | zero =>
        constructor
        · intro h
          exact ⟨Fin.elim0, h⟩
        · rintro ⟨x, hx⟩
          have hx0 : x = Fin.elim0 := by funext i; exact Fin.elim0 i
          simpa only [hx0, eliminateAll] using hx
    | succ n ih =>
        rw [eliminateAll, ih]
        constructor
        · rintro ⟨x, hx⟩
          obtain ⟨t, ht⟩ := (eliminate_correct S x).mp hx
          exact ⟨Fin.snoc x t, ht⟩
        · rintro ⟨x, hx⟩
          exact ⟨Fin.init x, (eliminate_correct S (Fin.init x)).mpr
            ⟨x (Fin.last n), by simpa only [Fin.snoc_init_self] using hx⟩⟩

end VolumePolynomials.RationalElimination
end -- closes the original EOF section from source line 12
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalElimination.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalPolytopeRepresentation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Exact computable halfspaces for a finite rational convex hull

The algorithm writes the usual barycentric inequalities and eliminates the
barycentric variables with the proved rational Fourier--Motzkin algorithm.
Thus the output is a finite list of rational halfspaces whose real solution
set is exactly the convex hull, including empty and lower-dimensional hulls.
-/

open Set
open scoped BigOperators

namespace VolumePolynomials.RationalElimination

theorem convexHull_range_finiteWeights {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (v : ι → E) :
    convexHull ℝ (range v) =
      {x | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∑ i, w i • v i = x} := by
  first
  | classical
    apply Set.Subset.antisymm
    · apply convexHull_min
      · rintro x ⟨i, rfl⟩
        refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
        · intro j
          change 0 ≤ if j = i then (1 : ℝ) else 0
          split_ifs <;> norm_num
        · simp
        · simp
      · rintro x ⟨w, hw, hw1, rfl⟩ y ⟨z, hz, hz1, rfl⟩ a b ha hb hab
        refine ⟨fun i => a * w i + b * z i, ?_, ?_, ?_⟩
        · intro i
          exact add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb (hz i))
        · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1, hz1, mul_one, hab]
        · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    · rintro x ⟨w, hw, hw1, hwx⟩
      exact mem_convexHull_of_exists_fintype w v hw hw1 (fun i => mem_range_self i) hwx

def negative {n : ℕ} (p : Inequality n) : Inequality n :=
  ⟨fun i => -p.coefficient i, -p.bound⟩

theorem negative_value {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) :
    (negative p).value x = -p.value x := by
  first
  | simp [negative, Inequality.value, Finset.sum_neg_distrib]

def equality {n : ℕ} (a : Fin n → ℚ) (b : ℚ) : List (Inequality n) :=
  [⟨a, b⟩, negative ⟨a, b⟩]

theorem satisfies_equality {n : ℕ} (a : Fin n → ℚ) (b : ℚ) (x : Fin n → ℝ) :
    Satisfies (equality a b) x ↔ (∑ i, (a i : ℝ) * x i) = (b : ℝ) := by
  first
  | constructor
    · intro h
      have hu : (∑ i, (a i : ℝ) * x i) ≤ (b : ℝ) :=
        h (Inequality.mk a b) (by simp [equality])
      have hl := h (negative (Inequality.mk a b)) (by simp [equality])
      change (negative (Inequality.mk a b)).value x ≤
        ((negative (Inequality.mk a b)).bound : ℝ) at hl
      rw [negative_value] at hl
      have hl' : -(∑ i, (a i : ℝ) * x i) ≤ -(b : ℝ) := by
        simpa only [negative, Inequality.value, Rat.cast_neg] using hl
      exact le_antisymm hu (neg_le_neg_iff.mp hl')
    · intro h p hp
      have hp' : p = Inequality.mk a b ∨ p = negative (Inequality.mk a b) := by
        simpa [equality] using hp
      rcases hp' with rfl | rfl
      · exact h.le
      · change (negative (Inequality.mk a b)).value x ≤
          ((negative (Inequality.mk a b)).bound : ℝ)
        rw [negative_value]
        simpa only [negative, Inequality.value, Rat.cast_neg] using neg_le_neg h.ge

theorem satisfies_append {n : ℕ} (A B : List (Inequality n)) (x : Fin n → ℝ) :
    Satisfies (A ++ B) x ↔ Satisfies A x ∧ Satisfies B x := by
  first
  | constructor
    · intro h
      exact ⟨fun p hp => h p (List.mem_append.mpr (Or.inl hp)),
        fun p hp => h p (List.mem_append.mpr (Or.inr hp))⟩
    · rintro ⟨hA, hB⟩ p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hA p hp
      · exact hB p hp

theorem satisfies_ofFn {n m : ℕ} (p : Fin m → Inequality n) (x : Fin n → ℝ) :
    Satisfies (List.ofFn p) x ↔ ∀ j, (p j).Holds x := by
  first
  | simp [Satisfies, List.mem_ofFn]

theorem satisfies_flatten_ofFn {n m : ℕ} (p : Fin m → List (Inequality n))
    (x : Fin n → ℝ) :
    Satisfies (List.ofFn p).flatten x ↔ ∀ j, Satisfies (p j) x := by
  first
  | constructor
    · intro h j q hq
      exact h q (List.mem_flatten.mpr ⟨p j, List.mem_ofFn.mpr ⟨j, rfl⟩, hq⟩)
    · intro h q hq
      obtain ⟨L, hL, hqL⟩ := List.mem_flatten.mp hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
      exact h j q hqL

theorem value_append {n m : ℕ} (a : Fin n → ℚ) (b : Fin m → ℚ)
    (c : ℚ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (Inequality.mk (Fin.append a b) c).value (Fin.append x w) =
      (∑ i, (a i : ℝ) * x i) + ∑ j, (b j : ℝ) * w j := by
  first
  | rw [Inequality.value, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

def nonnegativeConstraint (n : ℕ) {m : ℕ} (j : Fin m) : Inequality (n + m) :=
  ⟨Fin.append (fun _ => 0) (fun k => if k = j then -1 else 0), 0⟩

theorem nonnegativeConstraint_holds (n : ℕ) {m : ℕ} (j : Fin m)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (nonnegativeConstraint n j).Holds (Fin.append x w) ↔ 0 ≤ w j := by
  first
  | simp only [Inequality.Holds, nonnegativeConstraint, value_append]
    simp [apply_ite, ite_mul]

def barycentricSystem {n m : ℕ} (v : Fin m → Fin n → ℚ) : List (Inequality (n + m)) :=
  List.ofFn (nonnegativeConstraint n) ++
    equality (Fin.append (fun _ : Fin n => 0) (fun _ : Fin m => 1)) 1 ++
    (List.ofFn fun i : Fin n =>
      equality (Fin.append (fun k => if k = i then 1 else 0) (fun j => -v j i)) 0).flatten

theorem barycentricSystem_correct {n m : ℕ} (v : Fin m → Fin n → ℚ)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Satisfies (barycentricSystem v) (Fin.append x w) ↔
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
        ∑ j, w j • (fun i => (v j i : ℝ)) = x := by
  first
  | rw [barycentricSystem, satisfies_append, satisfies_append, satisfies_ofFn,
      satisfies_equality, satisfies_flatten_ofFn]
    simp only [nonnegativeConstraint_holds]
    have hsum : (∑ k : Fin (n + m),
        ((Fin.append (fun _ : Fin n => (0 : ℚ)) (fun _ : Fin m => 1)) k : ℝ) *
          Fin.append x w k) = ∑ j, w j := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Rat.cast_zero, Rat.cast_one,
        zero_mul, one_mul, Finset.sum_const_zero, zero_add]
    rw [hsum]
    have hcoord : (∀ i : Fin n,
        Satisfies (equality (Fin.append (fun k => if k = i then 1 else 0)
          (fun j => -v j i)) 0) (Fin.append x w)) ↔
        ∑ j, w j • (fun i => (v j i : ℝ)) = x := by
      simp only [satisfies_equality]
      have heval : ∀ i : Fin n,
          (∑ k : Fin (n + m),
            ((Fin.append (fun k => if k = i then (1 : ℚ) else 0) (fun j => -v j i)) k : ℝ) *
              Fin.append x w k) = x i - ∑ j, (v j i : ℝ) * w j := by
        intro i
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right, apply_ite, ite_mul,
          Finset.sum_neg_distrib, sub_eq_add_neg]
      simp only [heval, Rat.cast_zero, sub_eq_zero]
      constructor
      · intro h
        funext i
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using (h i).symm
      · intro h i
        have hi := congrFun h i
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi.symm
    rw [hcoord]
    simp only [Rat.cast_one, and_assoc]

/-- A finite executable rational halfspace representation of the hull. -/
def hullHalfspaces {n m : ℕ} (v : Fin m → Fin n → ℚ) : List (Inequality n) :=
  eliminateSuffix n m (barycentricSystem v)

/-- The computed halfspaces describe the literal real convex hull. -/
theorem hullHalfspaces_correct {n m : ℕ} (v : Fin m → Fin n → ℚ) (x : Fin n → ℝ) :
    Satisfies (hullHalfspaces v) x ↔
      x ∈ convexHull ℝ (range (fun j => fun i => (v j i : ℝ))) := by
  first
  | rw [hullHalfspaces, eliminateSuffix_correct, convexHull_range_finiteWeights]
    simp only [Set.mem_setOf_eq, barycentricSystem_correct]

end VolumePolynomials.RationalElimination
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalPolytopeRepresentation.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalBoxVolume.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Certified rational volume approximation

Closed rational halfspaces are tested on the extremal vertices of rational
grid boxes. The inner and outer counts are rational bounds on actual Lebesgue
volume. Their difference tends to zero, including for empty or degenerate
polytopes, because a convex set has null frontier. Searching the decidable
rational gap test therefore gives a terminating executable approximation.
-/

open Set Filter Metric MeasureTheory
open scoped BigOperators Topology

namespace VolumePolynomials.RationalElimination

namespace Inequality

def rationalValue {n : ℕ} (p : Inequality n) (x : Fin n → ℚ) : ℚ :=
  ∑ i, p.coefficient i * x i

theorem value_cast {n : ℕ} (p : Inequality n) (x : Fin n → ℚ) :
    p.value (fun i => (x i : ℝ)) = (p.rationalValue x : ℝ) := by
  first
  | simp [value, rationalValue]

theorem continuous_value {n : ℕ} (p : Inequality n) : Continuous p.value := by
  first
  | change Continuous (fun x : Fin n → ℝ => ∑ i, (p.coefficient i : ℝ) * x i)
    fun_prop

def upperCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) : Fin n → ℚ :=
  fun i => if 0 ≤ p.coefficient i then ((ν i : ℚ) + 1) / (k + 1) else (ν i : ℚ) / (k + 1)

def lowerCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) : Fin n → ℚ :=
  (negative p).upperCorner k ν

end Inequality

noncomputable abbrev cell {n : ℕ} (k : ℕ) (ν : Fin n → ℤ) : BoxIntegral.Box (Fin n) :=
  BoxIntegral.unitPartition.box (k + 1) ν

noncomputable def ambientBox (n R : ℕ) : BoxIntegral.Box (Fin n) :=
  ⟨fun _ => -((R : ℝ) + 1), fun _ => (R : ℝ) + 1,
    fun _ => by linarith [Nat.cast_nonneg (α := ℝ) R]⟩

theorem ambientBox_integral (n R : ℕ) : BoxIntegral.hasIntegralVertices (ambientBox n R) := by
  first
  | exact ⟨fun _ => -((R : ℤ) + 1), fun _ => (R : ℤ) + 1,
      fun _ => by simp [ambientBox], fun _ => by simp [ambientBox]⟩

/-- The explicit finite integer index set; no real-set membership is computed. -/
def gridIndices (n R k : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Ico (-((R : ℤ) + 1) * ((k : ℤ) + 1))
    (((R : ℤ) + 1) * ((k : ℤ) + 1)))

theorem mem_gridIndices_iff {n R k : ℕ} (ν : Fin n → ℤ) :
    ν ∈ gridIndices n R k ↔ cell k ν ≤ ambientBox n R := by
  first
  | have hk : 0 < (k : ℝ) + 1 := by positivity
    rw [gridIndices, Fintype.mem_piFinset, BoxIntegral.Box.le_iff_bounds]
    simp only [Finset.mem_Ico, Pi.le_def, ambientBox, cell,
      BoxIntegral.unitPartition.box_lower, BoxIntegral.unitPartition.box_upper, Nat.cast_add,
      Nat.cast_one]
    constructor
    · intro h
      constructor
      · intro i
        apply (le_div_iff₀ hk).mpr
        exact_mod_cast (h i).1
      · intro i
        apply (div_le_iff₀ hk).mpr
        exact_mod_cast (Int.add_one_le_iff.mpr (h i).2)
    · rintro ⟨hl, hu⟩ i
      constructor
      · exact_mod_cast (le_div_iff₀ hk).mp (hl i)
      · apply Int.add_one_le_iff.mp
        exact_mod_cast (div_le_iff₀ hk).mp (hu i)

theorem index_mem_gridIndices {n R k : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ ambientBox n R) :
    BoxIntegral.unitPartition.index (k + 1) x ∈ gridIndices n R k := by
  first
  | rw [mem_gridIndices_iff]
    exact BoxIntegral.unitPartition.mem_admissibleIndex_iff.mp
      (BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box (k + 1)
        (ambientBox_integral n R) hx)

theorem upperCorner_mem {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) :
    (fun i => (p.upperCorner k ν i : ℝ)) ∈ BoxIntegral.Box.Icc (cell k ν) := by
  first
  | have hk : 0 < (k : ℝ) + 1 := by positivity
    rw [BoxIntegral.Box.Icc_eq_pi]
    intro i _
    simp only [Inequality.upperCorner, cell, BoxIntegral.unitPartition.box_lower,
      BoxIntegral.unitPartition.box_upper, Set.mem_Icc, Nat.cast_add, Nat.cast_one]
    split_ifs <;> push_cast <;> constructor <;> first | rfl | gcongr <;> linarith

theorem lowerCorner_mem {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) :
    (fun i => (p.lowerCorner k ν i : ℝ)) ∈ BoxIntegral.Box.Icc (cell k ν) :=
  upperCorner_mem (negative p) k ν

theorem value_le_upperCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) :
    p.value x ≤ (p.rationalValue (p.upperCorner k ν) : ℝ) := by
  first
  | rw [← p.value_cast]
    apply Finset.sum_le_sum
    intro i hi
    have hxi : (cell k ν).lower i ≤ x i ∧ x i ≤ (cell k ν).upper i :=
      ⟨hx.1 i, hx.2 i⟩
    by_cases ha : 0 ≤ p.coefficient i
    · have ha' : 0 ≤ (p.coefficient i : ℝ) := by exact_mod_cast ha
      simpa only [Inequality.upperCorner, if_pos ha, Rat.cast_div, Rat.cast_add,
        Rat.cast_intCast, Rat.cast_natCast, Rat.cast_one, cell,
        BoxIntegral.unitPartition.box_upper, Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_left hxi.2 ha'
    · have ha' : (p.coefficient i : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge ha))
      simpa only [Inequality.upperCorner, if_neg ha, Rat.cast_div, Rat.cast_intCast,
        Rat.cast_natCast, Rat.cast_add, Rat.cast_one, cell,
        BoxIntegral.unitPartition.box_lower, Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonpos_left hxi.1 ha'

theorem lowerCorner_le_value {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) :
    (p.rationalValue (p.lowerCorner k ν) : ℝ) ≤ p.value x := by
  first
  | have h := value_le_upperCorner (negative p) k ν hx
    rw [← Inequality.value_cast, negative_value, negative_value] at h
    rw [← p.value_cast]
    exact neg_le_neg_iff.mp h

def solutionSet {n : ℕ} (S : List (Inequality n)) : Set (Fin n → ℝ) :=
  {x | Satisfies S x}

theorem isClosed_solutionSet {n : ℕ} (S : List (Inequality n)) :
    IsClosed (solutionSet S) := by
  first
  | have heq : solutionSet S =
        ⋂ p : Inequality n, ⋂ (_ : p ∈ S), {x | p.value x ≤ (p.bound : ℝ)} := by
      first
      | ext x
        simp only [solutionSet, Set.mem_setOf_eq, Satisfies, Inequality.Holds, Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter fun p => isClosed_iInter fun _ : p ∈ S =>
      isClosed_le p.continuous_value (continuous_const : Continuous (fun _ : Fin n → ℝ => (p.bound : ℝ)))

theorem convex_solutionSet {n : ℕ} (S : List (Inequality n)) :
    Convex ℝ (solutionSet S) := by
  first
  | intro x hx y hy a b ha hb hab p hp
    have hpX := hx p hp
    have hpY := hy p hp
    have heq : p.value (a • x + b • y) = a * p.value x + b * p.value y := by
      first
      | simp only [Inequality.value, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    change p.value (a • x + b • y) ≤ (p.bound : ℝ)
    rw [heq]
    calc
      _ ≤ a * (p.bound : ℝ) + b * (p.bound : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hpX ha) (mul_le_mul_of_nonneg_left hpY hb)
      _ = (p.bound : ℝ) := by rw [← add_mul, hab, one_mul]

def innerTest {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) : Prop :=
  ∀ p ∈ S, p.rationalValue (p.upperCorner k ν) ≤ p.bound

def outerTest {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) : Prop :=
  ∀ p ∈ S, p.rationalValue (p.lowerCorner k ν) ≤ p.bound

instance innerTest_decidable {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    Decidable (innerTest S k ν) := by unfold innerTest; infer_instance

instance outerTest_decidable {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    Decidable (outerTest S k ν) := by unfold outerTest; infer_instance

theorem innerTest_iff {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    innerTest S k ν ↔ BoxIntegral.Box.Icc (cell k ν) ⊆ solutionSet S := by
  first
  | constructor
    · intro h x hx p hp
      apply (value_le_upperCorner p k ν hx).trans
      exact_mod_cast h p hp
    · intro h p hp
      have hv := h (upperCorner_mem p k ν) p hp
      rw [Inequality.Holds, Inequality.value_cast] at hv
      exact_mod_cast hv

theorem outerTest_of_mem {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) (hs : x ∈ solutionSet S) :
    outerTest S k ν := by
  first
  | intro p hp
    have h := (lowerCorner_le_value p k ν hx).trans (hs p hp)
    exact_mod_cast h

def innerIndices {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : Finset (Fin n → ℤ) :=
  (gridIndices n R k).filter (innerTest S k)

def outerIndices {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : Finset (Fin n → ℤ) :=
  (gridIndices n R k).filter (outerTest S k)

noncomputable def gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) : Set (Fin n → ℝ) :=
  ⋃ ν ∈ A, (cell k ν : Set (Fin n → ℝ))

theorem measurableSet_gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) :
    MeasurableSet (gridUnion k A) := by
  first
  | exact Finset.measurableSet_biUnion A (fun ν _ => (cell k ν).measurableSet_coe)

theorem mem_gridUnion_iff {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) (x : Fin n → ℝ) :
    x ∈ gridUnion k A ↔ BoxIntegral.unitPartition.index (k + 1) x ∈ A := by
  first
  | simp only [gridUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨ν, hν, hx⟩
      have heq := BoxIntegral.unitPartition.mem_box_iff_index.mp hx
      rw [heq]
      exact hν
    · intro h
      exact ⟨_, h, BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl⟩

theorem gridUnion_subset_ambient {n R k : ℕ} {A : Finset (Fin n → ℤ)}
    (hA : A ⊆ gridIndices n R k) : gridUnion k A ⊆ ambientBox n R := by
  first
  | intro x hx
    simp only [gridUnion, Set.mem_iUnion] at hx
    obtain ⟨ν, hν, hx⟩ := hx
    exact (mem_gridIndices_iff ν).mp (hA hν) hx

theorem volume_gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) :
    volume.real (gridUnion k A) = (A.card : ℝ) / ((k : ℝ) + 1) ^ n := by
  first
  | rw [gridUnion, measureReal_biUnion_finset
      (h := fun ν _ ↦ (cell k ν).isBounded.measure_lt_top.ne)]
    · simp [measureReal_def, cell, BoxIntegral.unitPartition.volume_box,
        div_eq_mul_inv, ENNReal.toReal_add]
    · intro ν hν ν' hν' hne
      exact BoxIntegral.unitPartition.disjoint.mp hne
    · intro ν hν
      exact (cell k ν).measurableSet_coe

def lowerVolume {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : ℚ :=
  ((innerIndices S R k).card : ℚ) / ((k : ℚ) + 1) ^ n

def upperVolume {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : ℚ :=
  ((outerIndices S R k).card : ℚ) / ((k : ℚ) + 1) ^ n

theorem lowerVolume_eq {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    (lowerVolume S R k : ℝ) = volume.real (gridUnion k (innerIndices S R k)) := by
  first
  | rw [volume_gridUnion]
    simp [lowerVolume]

theorem upperVolume_eq {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    (upperVolume S R k : ℝ) = volume.real (gridUnion k (outerIndices S R k)) := by
  first
  | rw [volume_gridUnion]
    simp [upperVolume]

theorem innerUnion_subset {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    gridUnion k (innerIndices S R k) ⊆ solutionSet S := by
  first
  | intro x hx
    simp only [gridUnion, Set.mem_iUnion] at hx
    obtain ⟨ν, hν, hx⟩ := hx
    exact (innerTest_iff S k ν).mp (Finset.mem_filter.mp hν).2
      (BoxIntegral.Box.coe_subset_Icc hx)

theorem subset_outerUnion {n : ℕ} (S : List (Inequality n)) (R k : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    solutionSet S ⊆ gridUnion k (outerIndices S R k) := by
  first
  | intro x hx
    rw [mem_gridUnion_iff]
    exact Finset.mem_filter.mpr ⟨index_mem_gridIndices (hbound hx),
      outerTest_of_mem S k _ (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl)) hx⟩

theorem volume_bounds {n : ℕ} (S : List (Inequality n)) (R k : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    (lowerVolume S R k : ℝ) ≤ volume.real (solutionSet S) ∧
      volume.real (solutionSet S) ≤ (upperVolume S R k : ℝ) := by
  first
  | rw [lowerVolume_eq, upperVolume_eq]
    constructor
    · exact measureReal_mono (innerUnion_subset S R k)
        ((ambientBox n R).isBounded.subset hbound).measure_lt_top.ne
    · exact measureReal_mono (subset_outerUnion S R k hbound)
        ((ambientBox n R).isBounded.subset
          (gridUnion_subset_ambient (Finset.filter_subset _ _))).measure_lt_top.ne

theorem eventually_mem_innerUnion {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) {x : Fin n → ℝ}
    (hx : x ∈ interior (solutionSet S)) :
    ∀ᶠ k in atTop, x ∈ gridUnion k (innerIndices S R k) := by
  first
  | obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    have hevent := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)
    filter_upwards [hevent] with k hk
    rw [mem_gridUnion_iff]
    refine Finset.mem_filter.mpr ⟨index_mem_gridIndices (hbound (interior_subset hx)), ?_⟩
    rw [innerTest_iff]
    intro y hy
    apply interior_subset (hball ?_)
    apply (dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc _) hy
      (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl))).trans_lt
    exact (BoxIntegral.unitPartition.diam_boxIcc (k + 1) _).trans_lt (by simpa using hk)

theorem lowerCorner_index_tendsto {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) :
    Tendsto (fun k => fun i =>
      (p.lowerCorner k (BoxIntegral.unitPartition.index (k + 1) x) i : ℝ)) atTop (𝓝 x) := by
  first
  | apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε))
    refine ⟨N, fun k hk => ?_⟩
    apply (dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc _) (lowerCorner_mem p k _)
      (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl))).trans_lt
    exact (BoxIntegral.unitPartition.diam_boxIcc (k + 1) _).trans_lt (by simpa using hN k hk)

theorem eventually_notMem_outerUnion {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    {x : Fin n → ℝ} (hx : x ∉ solutionSet S) :
    ∀ᶠ k in atTop, x ∉ gridUnion k (outerIndices S R k) := by
  first
  | obtain ⟨p, hp, hpx⟩ : ∃ p ∈ S, (p.bound : ℝ) < p.value x := by
      first
      | simpa only [solutionSet, Set.mem_setOf_eq, Satisfies, Inequality.Holds,
          not_forall, not_le, exists_prop] using hx
    have hevent := (p.continuous_value.tendsto x |>.comp (lowerCorner_index_tendsto p x)).eventually
      (lt_mem_nhds hpx)
    filter_upwards [hevent] with k hk hxk
    rw [mem_gridUnion_iff] at hxk
    have htest := (Finset.mem_filter.mp hxk).2 p hp
    dsimp only [Function.comp_def] at hk
    rw [Inequality.value_cast] at hk
    exact (not_lt_of_ge (by exact_mod_cast htest)) hk

theorem tendsto_volume_bounds {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    Tendsto (fun k => (lowerVolume S R k : ℝ)) atTop (𝓝 (volume.real (solutionSet S))) ∧
    Tendsto (fun k => (upperVolume S R k : ℝ)) atTop (𝓝 (volume.real (solutionSet S))) := by
  first
  | have hfinite : volume (solutionSet S) ≠ ⊤ :=
      ((ambientBox n R).isBounded.subset hbound).measure_lt_top.ne
    have hnull := (convex_solutionSet S).addHaar_frontier volume
    have hae : ∀ᵐ x ∂volume, x ∉ frontier (solutionSet S) :=
      measure_eq_zero_iff_ae_notMem.mp hnull
    have hinner : Tendsto (fun k => volume (gridUnion k (innerIndices S R k)))
        atTop (𝓝 (volume (solutionSet S))) := by
      first
      | apply tendsto_measure_of_ae_tendsto_indicator atTop (isClosed_solutionSet S).measurableSet
          (fun k => measurableSet_gridUnion k _) (ambientBox n R).measurableSet_coe
          (ambientBox n R).isBounded.measure_lt_top.ne
        · exact Eventually.of_forall (fun k => gridUnion_subset_ambient (Finset.filter_subset _ _))
        · filter_upwards [hae] with x hx
          by_cases hxS : x ∈ solutionSet S
          · have hxi := (mem_interior_iff_notMem_frontier hxS).mpr hx
            filter_upwards [eventually_mem_innerUnion S R hbound hxi] with k hk
            exact iff_of_true hk hxS
          · exact Eventually.of_forall (fun k => iff_of_false
              (fun h => hxS (innerUnion_subset S R k h)) hxS)
    have houter : Tendsto (fun k => volume (gridUnion k (outerIndices S R k)))
        atTop (𝓝 (volume (solutionSet S))) := by
      first
      | apply tendsto_measure_of_ae_tendsto_indicator atTop (isClosed_solutionSet S).measurableSet
          (fun k => measurableSet_gridUnion k _) (ambientBox n R).measurableSet_coe
          (ambientBox n R).isBounded.measure_lt_top.ne
        · exact Eventually.of_forall (fun k => gridUnion_subset_ambient (Finset.filter_subset _ _))
        · filter_upwards [hae] with x hx
          by_cases hxS : x ∈ solutionSet S
          · exact Eventually.of_forall (fun k => iff_of_true (subset_outerUnion S R k hbound hxS) hxS)
          · filter_upwards [eventually_notMem_outerUnion S R hxS] with k hk
            exact iff_of_false hk hxS
    constructor
    · simpa only [Function.comp_def, lowerVolume_eq, measureReal_def] using
        (ENNReal.tendsto_toReal hfinite).comp hinner
    · simpa only [Function.comp_def, upperVolume_eq, measureReal_def] using
        (ENNReal.tendsto_toReal hfinite).comp houter

theorem exists_gap_lt {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) :
    ∃ k, upperVolume S R k - lowerVolume S R k < ε := by
  first
  | have he : 0 < (ε : ℝ) := by exact_mod_cast hε
    have h := (tendsto_volume_bounds S R hbound).2.sub (tendsto_volume_bounds S R hbound).1
    rw [sub_self] at h
    obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds he)).exists
    exact ⟨k, by exact_mod_cast hk⟩

/-- A terminating rational-arithmetic search, using only the proved existence
of an accepted index as its termination certificate. -/
def approximateVolume {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  lowerVolume S R (Nat.find (exists_gap_lt S R hbound ε hε))

theorem approximateVolume_correct {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) :
    |(approximateVolume S R hbound ε hε : ℝ) - volume.real (solutionSet S)| < (ε : ℝ) := by
  first
  | let k := Nat.find (exists_gap_lt S R hbound ε hε)
    have hk := Nat.find_spec (exists_gap_lt S R hbound ε hε)
    have hb := volume_bounds S R k hbound
    have hg : (upperVolume S R k : ℝ) - (lowerVolume S R k : ℝ) < (ε : ℝ) := by
      first
      | exact_mod_cast hk
    change |(lowerVolume S R k : ℝ) - volume.real (solutionSet S)| < (ε : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr hb.1)]
    linarith

end VolumePolynomials.RationalElimination
end -- closes the original EOF section from source line 13
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalBoxVolume.lean -/
