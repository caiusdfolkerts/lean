module

public import volume_polynomials.assembly_part05

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

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/CAD/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cylindrical algebraic decompositions

A *cylindrical algebraic decomposition* (CAD) of `ℝ ^ n` is a finite partition of `ℝ ^ n` into
semialgebraic cells, built one dimension at a time. The only CAD of `ℝ ^ 0` is the partition into
the single point. A CAD of `ℝ ^ (n + 1)` is obtained from a CAD of `ℝ ^ n` by choosing, over each
of its cells `C`, finitely many continuous functions `θ₀ < θ₁ < … < θₖ₋₁ : C → ℝ` whose sections
and sectors are semialgebraic, and taking all the sections and sectors of all these stacks. The
distinguished new coordinate is coordinate `0`, as for `TauCeti.cylinder`.

`TauCeti.IsCAD n 𝒞` is this recursive definition, for a set `𝒞` of subsets of `Fin n → ℝ`. The
cells are not assumed to be connected, nor the decomposition to be a partition: these are
theorems. Every cell of a CAD is a nonempty, connected, semialgebraic set, there are finitely many
cells, and they partition `ℝ ^ n`. The projections of the cells of a CAD of `ℝ ^ (n + 1)` form a
CAD of `ℝ ^ n`, and the decomposition is cylindrical: two cells have equal or disjoint
projections, so each cell lies over the whole of the lower cell it meets.

A CAD is *adapted* to a family of polynomials when each of them is sign-invariant on each cell.
Every set described by a condition on their signs is then a union of cells, so its projection is
a union of projected cells and is semialgebraic. Every semialgebraic set is described by such a
condition (`TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`); together with the existence of
adapted CADs this gives the closure of semialgebraic sets under projection. One sample point in
each cell of an adapted CAD realizes every sign condition that the polynomials realize anywhere.

Stacks of polynomial functions are semialgebraic. In particular finitely many points of `ℝ`,
together with the open intervals they cut out, form a CAD of `ℝ ^ 1`.

## Main declarations

* `TauCeti.IsSemialgebraicStack`: a continuous, strictly ordered stack with semialgebraic cells.
* `TauCeti.IsCAD`: cylindrical algebraic decompositions, defined recursively.
* `TauCeti.IsCAD.isPartition`, `TauCeti.IsCAD.finite`, `TauCeti.IsCAD.isSemialgebraic`,
  `TauCeti.IsCAD.isConnected`: a CAD is a finite partition into connected semialgebraic cells.
* `TauCeti.IsCAD.image_tail`, `TauCeti.IsCAD.image_tail_eq_or_disjoint`: projecting a CAD gives
  a CAD, and projections of cells are equal or disjoint.
* `TauCeti.IsCAD.isSemialgebraic_image_tail`,
  `TauCeti.IsCAD.isSemialgebraic_image_tail_setOf_sign_eval`: projections of unions of cells, in
  particular of sign-condition sets of polynomials sign-invariant on the cells, are semialgebraic.
* `TauCeti.IsCAD.exists_finite_image_sign_eval_eq`: sample points of an adapted CAD realize all
  sign conditions.
* `TauCeti.isSemialgebraicStack_eval`, `TauCeti.isCAD_stackCells_const`: polynomial stacks, and
  the CAD of `ℝ ^ 1` cut out by finitely many points.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 (cylindrical algebraic decomposition).
-/

public section

open Function Set Topology MvPolynomial

namespace TauCeti

variable {n k : ℕ}

/-! ### Semialgebraic stacks -/

section Real

variable {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}

/-- A *semialgebraic stack* over `C ⊆ ℝ ^ n`: finitely many continuous functions
`θ₀ < θ₁ < … < θₖ₋₁` on `C` whose sections and sectors, placed in `ℝ ^ (n + 1)` by
`TauCeti.cylinder`, are semialgebraic. These are the stacks from which a cylindrical algebraic
decomposition is built. -/
structure IsSemialgebraicStack (C : Set (Fin n → ℝ)) (θ : Fin k → C → ℝ) : Prop where
  /-- Each function of the stack is continuous. -/
  continuous : ∀ i, Continuous (θ i)
  /-- The functions of the stack are strictly ordered at each point. -/
  strictMono : ∀ x, StrictMono fun i ↦ θ i x
  /-- Each section of the stack is semialgebraic. -/
  isSemialgebraic_sectionSet : ∀ i, IsSemialgebraic (cylinder C '' sectionSet θ i)
  /-- Each sector of the stack is semialgebraic. -/
  isSemialgebraic_sectorSet : ∀ j, IsSemialgebraic (cylinder C '' sectorSet θ j)

/-- Every cell of a semialgebraic stack is semialgebraic. -/
theorem IsSemialgebraicStack.isSemialgebraic (hθ : IsSemialgebraicStack C θ)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) : IsSemialgebraic E := by
  first
  | rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
    exacts [hθ.isSemialgebraic_sectionSet i, hθ.isSemialgebraic_sectorSet j]

/-- A stack of polynomial functions on a semialgebraic set, strictly ordered at each point, is a
semialgebraic stack. -/
theorem isSemialgebraicStack_eval (hC : IsSemialgebraic C) (p : Fin k → MvPolynomial (Fin n) ℝ)
    (hp : ∀ x ∈ C, StrictMono fun i ↦ eval x (p i)) :
    IsSemialgebraicStack C fun i x ↦ eval x.1 (p i) := by
  first
    -- In ambient coordinates, the value of the `i`-th function is a polynomial in the last `n`
    -- coordinates.
  | have hq (i : Fin k) (y : Fin (n + 1) → ℝ) :
        eval y (rename Fin.succ (p i)) = eval (Fin.tail y) (p i) := by
      simp only [eval_rename, Fin.tail_def, comp_def]
    refine ⟨fun i ↦ (continuous_eval (p i)).comp continuous_subtype_val,
      fun x ↦ hp x.1 x.2, fun i ↦ ?_, fun j ↦ ?_⟩
    · convert hC.preimage_tail.inter (isSemialgebraic_eval_eq (rename Fin.succ (p i)) (X 0))
        using 1
      ext y
      rw [mem_image_cylinder]
      simp [hq, eq_comm]
    · have hs (i : Fin k) : IsSemialgebraic {y : Fin (n + 1) → ℝ |
          (i.castSucc < j → eval (Fin.tail y) (p i) < y 0) ∧
            (j ≤ i.castSucc → y 0 < eval (Fin.tail y) (p i))} := by
        rcases lt_or_ge i.castSucc j with h | h
        · simpa [h, h.not_ge, hq] using isSemialgebraic_eval_lt (rename Fin.succ (p i)) (X 0)
        · simpa [h, h.not_gt, hq] using isSemialgebraic_eval_lt (X 0) (rename Fin.succ (p i))
      convert hC.preimage_tail.inter (IsSemialgebraic.iInter hs) using 1
      ext y
      rw [mem_image_cylinder]
      simp [forall_and, and_left_comm]

end Real

/-! ### Cylindrical algebraic decompositions -/

/-- `IsCAD n 𝒞` says that the set `𝒞` of subsets of `ℝ ^ n` is a *cylindrical algebraic
decomposition* of `ℝ ^ n`. The decomposition of `ℝ ^ 0` is the single cell `univ`. A decomposition
of `ℝ ^ (n + 1)` consists of all the cells of the stacks over the cells of a decomposition `𝒟` of
`ℝ ^ n`, where over each cell `C ∈ 𝒟` the stack `θ C` is a semialgebraic stack. The new coordinate
is coordinate `0`. -/
inductive IsCAD : (n : ℕ) → Set (Set (Fin n → ℝ)) → Prop
  /-- The decomposition of `ℝ ^ 0` into a single point. -/
  | zero : IsCAD 0 {univ}
  /-- Lift a decomposition `𝒟` of `ℝ ^ n` by a semialgebraic stack over each of its cells. -/
  | succ {n : ℕ} {𝒟 : Set (Set (Fin n → ℝ))} (k : Set (Fin n → ℝ) → ℕ)
      (θ : ∀ C : Set (Fin n → ℝ), Fin (k C) → C → ℝ) :
      IsCAD n 𝒟 → (∀ C ∈ 𝒟, IsSemialgebraicStack C (θ C)) →
        IsCAD (n + 1) (⋃ C ∈ 𝒟, stackCells C (θ C))

namespace IsCAD

variable {𝒞 : Set (Set (Fin n → ℝ))}

/-- Stacks over every cell of a CAD assemble into a CAD whose projections are exactly the
original cells. Any property shared by all stack cells holds on every cell of the new CAD. -/
theorem exists_succ_of_forall_exists_stack (h𝒞 : IsCAD n 𝒞)
    (P : Set (Fin (n + 1) → ℝ) → Prop)
    (h : ∀ C ∈ 𝒞, ∃ k, ∃ θ : Fin k → C → ℝ, IsSemialgebraicStack C θ ∧
      ∀ E ∈ stackCells C θ, P E) :
    ∃ 𝒟, IsCAD (n + 1) 𝒟 ∧ image Fin.tail '' 𝒟 = 𝒞 ∧ ∀ E ∈ 𝒟, P E := by
  first
  | classical
    have hstack (C : Set (Fin n → ℝ)) : ∃ k, ∃ θ : Fin k → C → ℝ, C ∈ 𝒞 →
        IsSemialgebraicStack C θ ∧ ∀ E ∈ stackCells C θ, P E := by
      by_cases hC : C ∈ 𝒞
      · obtain ⟨k, θ, hθ⟩ := h C hC
        exact ⟨k, θ, fun _ ↦ hθ⟩
      · exact ⟨0, Fin.elim0, fun h ↦ (hC h).elim⟩
    choose k θ hθ using hstack
    refine ⟨_, .succ k θ h𝒞 (fun C hC ↦ (hθ C hC).1), ?_, ?_⟩
    · exact image_image_tail_iUnion_stackCells fun C hC ↦ (hθ C hC).1.strictMono
    · intro E hE
      obtain ⟨C, hC, hE⟩ := mem_iUnion₂.mp hE
      exact (hθ C hC).2 E hE

/-- A cylindrical algebraic decomposition has finitely many cells. -/
theorem finite (h : IsCAD n 𝒞) : 𝒞.Finite := by
  first
  | induction h with
    | zero => exact finite_singleton _
    | succ k θ _ _ ih => exact ih.biUnion fun C _ ↦ finite_stackCells C (θ C)

/-- Every cell of a cylindrical algebraic decomposition is semialgebraic. -/
theorem isSemialgebraic (h : IsCAD n 𝒞) {E : Set (Fin n → ℝ)} (hE : E ∈ 𝒞) :
    IsSemialgebraic E := by
  first
  | induction h with
    | zero =>
      rw [mem_singleton_iff.1 hE]
      exact isSemialgebraic_univ
    | succ k θ _ hθ _ =>
      obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
      exact (hθ C hC).isSemialgebraic hE

/-- Every cell of a cylindrical algebraic decomposition is connected, and in particular
nonempty. -/
theorem isConnected (h : IsCAD n 𝒞) {E : Set (Fin n → ℝ)} (hE : E ∈ 𝒞) : IsConnected E := by
  first
  | induction h with
    | zero =>
      rw [mem_singleton_iff.1 hE, univ_unique]
      exact isConnected_singleton
    | succ k θ _ hθ ih =>
      obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
      exact isConnected_of_mem_stackCells (ih hC) (hθ C hC).continuous (hθ C hC).strictMono hE

/-- The cells of a cylindrical algebraic decomposition of `ℝ ^ n` partition `ℝ ^ n`. -/
theorem isPartition (h : IsCAD n 𝒞) : Setoid.IsPartition 𝒞 := by
  first
  | induction h with
    | zero => exact ⟨fun h ↦ empty_ne_univ (mem_singleton_iff.1 h), fun a ↦ ⟨univ, by simp, by simp⟩⟩
    | @succ n 𝒟 k θ h𝒟 hθ ih =>
      refine PairwiseDisjoint.isPartition_of_exists_of_ne_empty ?_ (fun y ↦ ?_) fun h₀ ↦ ?_
      · -- Cells over distinct base cells have disjoint projections.
        simp only [PairwiseDisjoint, Set.Pairwise, mem_iUnion₂, onFun, id]
        rintro E ⟨C, hC, hE⟩ E' ⟨C', hC', hE'⟩ hne
        rcases eq_or_ne C C' with rfl | hCC'
        · exact pairwiseDisjoint_stackCells (fun x ↦ ((hθ C hC).strictMono x).injective) hE hE'
            hne
        · refine Disjoint.of_image (f := Fin.tail) ?_
          rw [image_tail_of_mem_stackCells (hθ C hC).strictMono hE,
            image_tail_of_mem_stackCells (hθ C' hC').strictMono hE']
          exact ih.pairwiseDisjoint hC hC' hCC'
      · -- A point lies in a cell of the stack over the base cell containing its projection.
        obtain ⟨C, ⟨hC, hyC⟩, -⟩ := ih.2 (Fin.tail y)
        have hy : y ∈ ⋃₀ stackCells C (θ C) := by
          rw [sUnion_stackCells fun x ↦ ((hθ C hC).strictMono x).monotone]
          exact hyC
        obtain ⟨E, hE, hyE⟩ := hy
        exact ⟨E, mem_iUnion₂.2 ⟨C, hC, hE⟩, hyE⟩
      · exact not_nonempty_empty ((IsCAD.succ k θ h𝒟 hθ).isConnected h₀).nonempty

/-- The projections of the cells of a cylindrical algebraic decomposition of `ℝ ^ (n + 1)`,
forgetting the distinguished coordinate `0`, form a cylindrical algebraic decomposition of
`ℝ ^ n`. -/
theorem image_tail {𝒞 : Set (Set (Fin (n + 1) → ℝ))} (h : IsCAD (n + 1) 𝒞) :
    IsCAD n (image Fin.tail '' 𝒞) := by
  first
  | cases h with
    | succ k θ h𝒟 hθ => rwa [image_image_tail_iUnion_stackCells fun C hC ↦ (hθ C hC).strictMono]

/-- A cylindrical algebraic decomposition is cylindrical: the projections of two of its cells are
equal or disjoint. -/
theorem image_tail_eq_or_disjoint {𝒞 : Set (Set (Fin (n + 1) → ℝ))} (h : IsCAD (n + 1) 𝒞)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ 𝒞) (hE' : E' ∈ 𝒞) :
    Fin.tail '' E = Fin.tail '' E' ∨ Disjoint (Fin.tail '' E) (Fin.tail '' E') :=
  h.image_tail.isPartition.pairwiseDisjoint.eq_or_disjoint (mem_image_of_mem _ hE)
    (mem_image_of_mem _ hE')

/-! ### Decompositions adapted to sign conditions -/

/-- **Projections of unions of cells.** If a set `s ⊆ ℝ ^ (n + 1)` contains or misses each cell of
a cylindrical algebraic decomposition, then its projection forgetting coordinate `0` is
semialgebraic: it is the union of the projections of the cells contained in `s`, which are cells
of the projected decomposition. -/
theorem isSemialgebraic_image_tail {𝒞 : Set (Set (Fin (n + 1) → ℝ))} (h : IsCAD (n + 1) 𝒞)
    {s : Set (Fin (n + 1) → ℝ)} (hs : ∀ E ∈ 𝒞, E ⊆ s ∨ Disjoint E s) :
    IsSemialgebraic (Fin.tail '' s) := by
  first
  | have hs' : s = ⋃ E ∈ {E ∈ 𝒞 | E ⊆ s}, E := by
      refine Subset.antisymm (fun y hy ↦ ?_) (iUnion₂_subset fun E hE ↦ hE.2)
      obtain ⟨E, hE, hyE⟩ := mem_sUnion.1 (h.isPartition.sUnion_eq_univ ▸ mem_univ y)
      exact mem_iUnion₂.2 ⟨E, ⟨hE, (hs E hE).resolve_right fun hd ↦ disjoint_left.1 hd hyE hy⟩, hyE⟩
    rw [hs', image_iUnion₂]
    exact .biUnion (h.finite.subset (sep_subset _ _)) fun E hE ↦
      h.image_tail.isSemialgebraic (mem_image_of_mem _ hE.1)

/-- If the polynomials `p i` are sign-invariant on each cell of a cylindrical algebraic
decomposition of `ℝ ^ (n + 1)`, then the projection forgetting coordinate `0` of any set described
by a condition on the signs of the `p i` is semialgebraic. -/
theorem isSemialgebraic_image_tail_setOf_sign_eval {𝒞 : Set (Set (Fin (n + 1) → ℝ))}
    (h : IsCAD (n + 1) 𝒞) {ι : Type*} {p : ι → MvPolynomial (Fin (n + 1)) ℝ}
    (hp : ∀ i, ∀ E ∈ 𝒞, SignInvariant (fun x ↦ eval x (p i)) E) (Φ : (ι → SignType) → Prop) :
    IsSemialgebraic (Fin.tail '' {x | Φ fun i ↦ SignType.sign (eval x (p i))}) :=
  h.isSemialgebraic_image_tail fun E hE ↦
    subset_or_disjoint_setOf_sign (f := fun i x ↦ eval x (p i)) (fun i ↦ hp i E hE) Φ

/-- **Sample points.** If the polynomials `p i` are sign-invariant on each cell of a cylindrical
algebraic decomposition of `ℝ ^ n`, there is a finite set `T` of sample points, exactly one in each
cell, at which the `p i` take exactly the sign vectors that they take on `ℝ ^ n`. -/
theorem exists_finite_image_sign_eval_eq (h : IsCAD n 𝒞) {ι : Type*}
    {p : ι → MvPolynomial (Fin n) ℝ} (hp : ∀ i, ∀ E ∈ 𝒞, SignInvariant (fun x ↦ eval x (p i)) E) :
    ∃ T : Set (Fin n → ℝ), T.Finite ∧ (∀ E ∈ 𝒞, ∃ x, E ∩ T = {x}) ∧
      (fun x i ↦ SignType.sign (eval x (p i))) '' T =
        range fun x i ↦ SignType.sign (eval x (p i)) := by
  first
  | choose x hx using fun E : 𝒞 ↦ (h.isConnected E.2).nonempty
    have := h.finite.to_subtype
    refine ⟨range x, finite_range x, fun E hE ↦ ⟨x ⟨E, hE⟩, ?_⟩, ?_⟩
    · refine Subset.antisymm ?_ (singleton_subset_iff.2 ⟨hx ⟨E, hE⟩, mem_range_self _⟩)
      rintro _ ⟨hyE, E', rfl⟩
      -- the sample of `E'` lies in `E`, so the cells `E'` and `E` meet and are equal
      have hE' : E' = ⟨E, hE⟩ := Subtype.ext <|
        h.isPartition.pairwiseDisjoint.elim E'.2 hE (not_disjoint_iff.2 ⟨_, hx E', hyE⟩)
      rw [mem_singleton_iff, hE']
    · rw [← range_comp]
      exact range_sign_sample_eq h.isPartition.sUnion_eq_univ hp x hx

end IsCAD

/-- The trivial cylindrical algebraic decomposition of `ℝ ^ n` into a single cell. -/
theorem isCAD_singleton_univ (n : ℕ) : IsCAD n {univ} := by
  first
  | induction n with
    | zero => exact .zero
    | succ n ih =>
      convert IsCAD.succ (fun _ ↦ 0)
        (fun C i (x : C) ↦ eval x.1 (Fin.elim0 i : MvPolynomial (Fin n) ℝ)) ih fun C hC ↦ ?_
      · ext E
        simp [range_cylinder, eq_comm]
      · rw [mem_singleton_iff.1 hC]
        exact isSemialgebraicStack_eval isSemialgebraic_univ _ fun _ _ ↦ Subsingleton.strictMono _

/-- Strictly increasing points `c₀ < c₁ < … < cₖ₋₁` of `ℝ`, together with the open intervals they
cut out, form a cylindrical algebraic decomposition of `ℝ ^ 1`. -/
theorem isCAD_stackCells_const {c : Fin k → ℝ} (hc : StrictMono c) :
    IsCAD 1 (stackCells (univ : Set (Fin 0 → ℝ)) fun i _ ↦ c i) := by
  first
  | have hθ : IsSemialgebraicStack (univ : Set (Fin 0 → ℝ)) fun i _ ↦ c i := by
      simpa using isSemialgebraicStack_eval isSemialgebraic_univ (fun i ↦ MvPolynomial.C (c i))
        fun _ _ ↦ by simpa using hc
    convert IsCAD.succ (fun _ ↦ k) (fun _ ↦ fun i _ ↦ c i) .zero fun C hC ↦ by
      rwa [mem_singleton_iff.1 hC]
    simp

end TauCeti
end -- closes the original EOF section from source line 64
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/CAD/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Data/Finsupp/Fin.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# `Finsupp.cons`, `Finsupp.snoc` and their lexicographic comparison

`Finsupp.cons x s : Fin (n + 1) →₀ M` puts `x` in front of `s`. Adding two of them adds heads and
tails separately. The lexicographic order compares the entries at `0` first, so two of them are
compared by their heads, and then by their tails.

Dually, `Finsupp.snoc s x : Fin (n + 1) →₀ M` appends `x` after `s`, and `Finsupp.init t` forgets
the last entry of `t`; these are the `Finsupp` versions of `Fin.snoc` and `Fin.init`. Adding two
such vectors adds initial parts and last entries separately. Two such vectors are compared
lexicographically by their initial parts first, and then by their last entries.

Finally, `Finsupp.ext_iff_of_fin_three` says that a finitely supported function on `Fin 3` is
determined by its values at any three distinct points, in whatever order they are listed.
-/

public section

namespace Finsupp

variable {n : ℕ} {M : Type*}

theorem cons_add_cons [AddZeroClass M] (x y : M) (s t : Fin n →₀ M) :
    cons x s + cons y t = cons (x + y) (s + t) := by
  first
  | ext i
    cases i using Fin.cases <;> simp

/-- Strict lexicographic comparison of `Finsupp.cons` compares the heads first and compares
the tails when the heads are equal. -/
theorem toLex_cons_lt_toLex_cons_iff [Zero M] [LT M] {x y : M} {s t : Fin n →₀ M} :
    toLex (cons x s) < toLex (cons y t) ↔ x < y ∨ x = y ∧ toLex s < toLex t := by
  first
  | simp only [Lex.lt_iff, ofLex_toLex]
    exact Fin.pi_lex_lt_cons_cons (α := fun _ ↦ M) (s := fun {_} ↦ (· < ·))

section Snoc

variable [Zero M]

/-- `Finsupp.snoc s y : Fin (n + 1) →₀ M` appends `y` after `s`. See `Fin.snoc`. -/
noncomputable def snoc (s : Fin n →₀ M) (y : M) : Fin (n + 1) →₀ M :=
  equivFunOnFinite.symm (Fin.snoc (s : Fin n → M) y)

/-- `Finsupp.init t : Fin n →₀ M` forgets the last entry of `t`. See `Fin.init`. -/
noncomputable def init (t : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  equivFunOnFinite.symm (Fin.init t)

@[simp]
theorem coe_snoc (s : Fin n →₀ M) (y : M) : ⇑(snoc s y) = Fin.snoc (s : Fin n → M) y :=
  (rfl)

@[simp]
theorem coe_init (t : Fin (n + 1) →₀ M) : ⇑(init t) = Fin.init t :=
  (rfl)

theorem snoc_castSucc (s : Fin n →₀ M) (y : M) (i : Fin n) : snoc s y i.castSucc = s i := by
  first
  | simp

theorem snoc_last (s : Fin n →₀ M) (y : M) : snoc s y (Fin.last n) = y := by
  first
  | simp

theorem init_apply (t : Fin (n + 1) →₀ M) (i : Fin n) : init t i = t i.castSucc :=
  (rfl)

@[simp]
theorem init_snoc (s : Fin n →₀ M) (y : M) : init (snoc s y) = s := by
  first
  | ext i
    simp

@[simp]
theorem snoc_init_self (t : Fin (n + 1) →₀ M) : snoc (init t) (t (Fin.last n)) = t := by
  first
  | ext i
    simp

@[simp]
theorem snoc_zero_zero : snoc (0 : Fin n →₀ M) 0 = 0 := by
  first
  | ext i
    cases i using Fin.lastCases <;> simp

theorem snoc_injective2 : Function.Injective2 (snoc (n := n) (M := M)) := by
  first
  | intro s s' y y' h
    exact ⟨by simpa using congrArg init h, by simpa using DFunLike.congr_fun h (Fin.last n)⟩

@[simp]
theorem snoc_inj {s s' : Fin n →₀ M} {y y' : M} : snoc s y = snoc s' y' ↔ s = s' ∧ y = y' :=
  snoc_injective2.eq_iff

theorem eq_snoc_iff {t : Fin (n + 1) →₀ M} {s : Fin n →₀ M} {y : M} :
    t = snoc s y ↔ init t = s ∧ t (Fin.last n) = y := by
  first
  | conv_lhs => rw [← snoc_init_self t]
    exact snoc_inj

/-- Strict lexicographic comparison of `Finsupp.snoc` compares the initial parts first and
compares the last entries when the initial parts are equal. -/
theorem toLex_snoc_lt_toLex_snoc_iff [LT M] {x y : M} {s t : Fin n →₀ M} :
    toLex (snoc s x) < toLex (snoc t y) ↔ toLex s < toLex t ∨ s = t ∧ x < y := by
  first
  | simp only [Lex.lt_iff, ofLex_toLex, coe_snoc]
    constructor
    · rintro ⟨i, hlt, hi⟩
      cases i using Fin.lastCases with
      | last =>
        refine .inr ⟨ext fun j ↦ ?_, by simpa using hi⟩
        simpa using hlt j.castSucc (Fin.castSucc_lt_last j)
      | cast i =>
        refine .inl ⟨i, fun j hj ↦ ?_, by simpa using hi⟩
        simpa using hlt j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hj)
    · rintro (⟨i, hlt, hi⟩ | ⟨rfl, h⟩)
      · refine ⟨i.castSucc, fun j hj ↦ ?_, by simpa using hi⟩
        cases j using Fin.lastCases with
        | last => exact absurd hj (Fin.castSucc_lt_last i).not_gt
        | cast j => simpa using hlt j (Fin.castSucc_lt_castSucc_iff.1 hj)
      · refine ⟨Fin.last n, fun j hj ↦ ?_, by simpa using h⟩
        cases j using Fin.lastCases with
        | last => exact absurd hj (lt_irrefl _)
        | cast j => simp

end Snoc

theorem snoc_add_snoc [AddZeroClass M] (s t : Fin n →₀ M) (x y : M) :
    snoc s x + snoc t y = snoc (s + t) (x + y) := by
  first
  | ext i
    cases i using Fin.lastCases <;> simp

/-- A finitely supported function on `Fin 3` is determined by its values at three distinct
points `a, b, c`. -/
theorem ext_iff_of_fin_three [Zero M] {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {d d' : Fin 3 →₀ M} : d = d' ↔ d a = d' a ∧ d b = d' b ∧ d c = d' c := by
  first
  | refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂, h₃⟩ => Finsupp.ext fun x => ?_⟩
    rcases (by omega : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;> assumption

end Finsupp
end -- closes the original EOF section from source line 28
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Finsupp/Fin.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/MvPolynomial/Equiv.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Singling out an arbitrary variable of a polynomial ring in `n + 1` variables

Mathlib's `MvPolynomial.finSuccEquiv` identifies `R[X₀, …, Xₙ]` with the polynomial ring in the
variable `X₀` over `R[X₁, …, Xₙ]`. This file does the same with an arbitrary variable `Xₚ`
singled out: the remaining variables are indexed by `Fin n` through `p.succAbove`, as in the
equivalence `finSuccEquiv' p : Fin (n + 1) ≃ Option (Fin n)`.

This is the form in which a polynomial ring acquires one new variable in the middle of its
list, as happens to the coefficient ring of a grid complex when a grid diagram is stabilized.

## Main definitions

* `MvPolynomial.finSuccEquiv'`: the `R`-algebra isomorphism
  `R[X₀, …, Xₙ] ≃ R[X_{p.succAbove 0}, …, X_{p.succAbove (n-1)}][Xₚ]`.

## Main results

* `MvPolynomial.finSuccEquiv'_X_self`, `MvPolynomial.finSuccEquiv'_rename_succAbove`: the
  singled-out variable goes to the polynomial variable, and the others are constants.
* `MvPolynomial.polynomial_eval_finSuccEquiv'`: evaluating the polynomial variable at `a`
  substitutes `a` for `X p`.
* `MvPolynomial.finSuccEquiv'_zero`: for `p = 0` this is Mathlib's `MvPolynomial.finSuccEquiv`.
* `MvPolynomial.finSuccEquiv'_map`, `MvPolynomial.finSuccEquiv_map`: singling out a variable
  commutes with mapping the coefficients along a ring homomorphism.
* `MvPolynomial.polynomial_eval_map_finSuccEquiv'`, `MvPolynomial.polynomial_eval_map_finSuccEquiv`:
  specializing the other variables to a point `s` and then evaluating the polynomial variable at
  `y` is evaluating at the point obtained by inserting `y` into `s` at position `p`.

The last two results are the compatibility of this equivalence with coefficient maps and with
evaluation. They let a polynomial in `n + 1` variables be treated as a family of univariate
polynomials in `X p` parametrized by the other coordinates, with integer input mapped to the
reals either before or after the variable is singled out.

Dually, the last variable `Xₙ` can be moved into the coefficients instead, through Mathlib's
`MvPolynomial.optionEquivRight` after renaming along `finSuccEquivLast`. This identifies
`R[X₀, …, Xₙ]` with the polynomials in `X₀, …, Xₙ₋₁` whose coefficients are polynomials in `Xₙ`.
The coefficient of `Xᵘ` then has as its coefficient of `Xₙ ^ k` the coefficient of `f` at the
exponent `Finsupp.snoc u k` (`MvPolynomial.optionEquivRight_rename_finSuccEquivLast_coeff_coeff`).
This is the form used for Lazard evaluation, where the base variables are eliminated first and
the last variable is kept.

-/

public section

namespace MvPolynomial

variable (R : Type*) [CommSemiring R] {n : ℕ}

/-- The `R`-algebra isomorphism between polynomials in the variables `Fin (n + 1)` and
polynomials in the variable `X p` over the polynomials in the other variables, which are indexed
by `Fin n` through `p.succAbove`. -/
noncomputable def finSuccEquiv' (p : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv' p)).trans (optionEquivLeft R (Fin n))

variable {R}

/-- The singled-out variable becomes the polynomial variable. -/
@[simp]
theorem finSuccEquiv'_X_self (p : Fin (n + 1)) : finSuccEquiv' R p (X p) = Polynomial.X := by
  first
  | simp [finSuccEquiv', optionEquivLeft_X_none]

/-- A variable other than the singled-out one becomes a constant. -/
@[simp]
theorem finSuccEquiv'_X_succAbove (p : Fin (n + 1)) (i : Fin n) :
    finSuccEquiv' R p (X (p.succAbove i)) = Polynomial.C (X i) := by
  first
  | simp [finSuccEquiv', optionEquivLeft_X_some]

/-- Polynomials not involving the singled-out variable become constants. -/
@[simp]
theorem finSuccEquiv'_rename_succAbove (p : Fin (n + 1)) (f : MvPolynomial (Fin n) R) :
    finSuccEquiv' R p (rename p.succAbove f) = Polynomial.C f := by
  first
  | have : ((finSuccEquiv' R p).toAlgHom.comp (rename p.succAbove) :
        MvPolynomial (Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin n) R)) = Polynomial.CAlgHom :=
      algHom_ext fun i => by simp
    exact DFunLike.congr_fun this f

/-- Constants stay constant. -/
@[simp]
theorem finSuccEquiv'_C (p : Fin (n + 1)) (r : R) :
    finSuccEquiv' R p (C r) = Polynomial.C (C r) :=
  (finSuccEquiv' R p).commutes r

/-- The polynomial variable comes from the singled-out variable. -/
@[simp]
theorem finSuccEquiv'_symm_X (p : Fin (n + 1)) :
    (finSuccEquiv' R p).symm Polynomial.X = X p :=
  (finSuccEquiv' R p).symm_apply_eq.mpr (finSuccEquiv'_X_self p).symm

/-- The constants come from the polynomials in the other variables. -/
@[simp]
theorem finSuccEquiv'_symm_C (p : Fin (n + 1)) (f : MvPolynomial (Fin n) R) :
    (finSuccEquiv' R p).symm (Polynomial.C f) = rename p.succAbove f :=
  (finSuccEquiv' R p).symm_apply_eq.mpr (finSuccEquiv'_rename_succAbove p f).symm

/-- Evaluating the singled-out variable at `a` is substituting `a` for `X p` and keeping the
other variables. -/
theorem polynomial_eval_finSuccEquiv' (p : Fin (n + 1)) (a : MvPolynomial (Fin n) R)
    (f : MvPolynomial (Fin (n + 1)) R) :
    Polynomial.eval a (finSuccEquiv' R p f) = aeval (Fin.insertNth p a X) f := by
  first
  | induction f using MvPolynomial.induction_on with
    | C r =>
      rw [← algebraMap_eq, AlgEquiv.commutes, AlgHom.commutes, Polynomial.algebraMap_apply,
        Polynomial.eval_C]
    | add f g hf hg => rw [map_add, Polynomial.eval_add, hf, hg, map_add]
    | mul_X f i hf =>
      rw [map_mul, Polynomial.eval_mul, hf, map_mul, aeval_X]
      congr 1
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Singling out the variable `X 0` is `MvPolynomial.finSuccEquiv`. -/
theorem finSuccEquiv'_zero : finSuccEquiv' R (0 : Fin (n + 1)) = finSuccEquiv R n := by
  first
  | rw [finSuccEquiv', finSuccEquiv, _root_.finSuccEquiv'_zero]

/-- Singling out a variable takes its partial derivative to the univariate derivative. -/
@[simp]
theorem finSuccEquiv'_pderiv (f : MvPolynomial (Fin (n + 1)) R) (p : Fin (n + 1)) :
    finSuccEquiv' R p (pderiv p f) = (finSuccEquiv' R p f).derivative := by
  first
  | induction f using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv'_C]
    | add f g hf hg => simp [hf, hg]
    | mul_X f i hf =>
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;>
        simp [Derivation.leibniz, smul_eq_mul, pderiv_X, hf, Polynomial.derivative_mul,
          mul_comm]

section Map

variable {S : Type*} [CommSemiring S]

/-- Singling out a variable commutes with mapping the coefficients along `φ`. -/
theorem finSuccEquiv'_map (φ : R →+* S) (p : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv' S p (map φ f) = (finSuccEquiv' R p f).map (map φ) := by
  first
  | induction f using MvPolynomial.induction_on with
    | C r => simp
    | add f g hf hg => simp only [map_add, Polynomial.map_add, hf, hg]
    | mul_X f i hf =>
      simp only [map_mul, Polynomial.map_mul, hf, map_X]
      congr 1
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Mapping the coefficients along `φ` commutes with the inverse of `finSuccEquiv' R p`. -/
theorem finSuccEquiv'_symm_map (φ : R →+* S) (p : Fin (n + 1))
    (f : Polynomial (MvPolynomial (Fin n) R)) :
    (finSuccEquiv' S p).symm (f.map (map φ)) = map φ ((finSuccEquiv' R p).symm f) := by
  first
  | rw [AlgEquiv.symm_apply_eq, finSuccEquiv'_map, AlgEquiv.apply_symm_apply]

/-- Singling out the variable `X 0` commutes with mapping the coefficients along `φ`. -/
theorem finSuccEquiv_map (φ : R →+* S) (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv S n (map φ f) = (finSuccEquiv R n f).map (map φ) := by
  first
  | simpa only [finSuccEquiv'_zero] using finSuccEquiv'_map φ 0 f

/-- Specializing the variables other than `X p` along `φ` at the point `s`, and then evaluating
the polynomial variable at `y`, is evaluating along `φ` at the point obtained by inserting `y`
into `s` at position `p`. -/
theorem polynomial_eval_map_finSuccEquiv' (φ : R →+* S) (p : Fin (n + 1)) (s : Fin n → S)
    (y : S) (f : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv' R p f).map (eval₂Hom φ s)).eval y = eval₂ φ (Fin.insertNth p y s) f := by
  first
  | induction f using MvPolynomial.induction_on with
    | C r => simp
    | add f g hf hg => simp only [map_add, Polynomial.map_add, Polynomial.eval_add, hf, hg, eval₂_add]
    | mul_X f i hf =>
      simp only [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hf, eval₂_mul, eval₂_X]
      congr 1
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Specializing the variables `X 1, …, X n` along `φ` at the point `s`, and then evaluating the
polynomial variable at `y`, is evaluating along `φ` at the point `Fin.cons y s`. -/
theorem polynomial_eval_map_finSuccEquiv (φ : R →+* S) (s : Fin n → S) (y : S)
    (f : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv R n f).map (eval₂Hom φ s)).eval y = eval₂ φ (Fin.cons y s) f := by
  first
  | simpa only [finSuccEquiv'_zero, Fin.insertNth_zero'] using
      polynomial_eval_map_finSuccEquiv' φ 0 s y f

end Map

/-- Rotating the last variable to coordinate zero before singling it out is the same as
singling out the last variable directly. This identifies the coordinate-zero convention for
polynomial families with the last-coordinate convention for successive base specialization. -/
theorem finSuccEquiv_rename_finRotate (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n (rename (finRotate (n + 1)) f) =
      optionEquivLeft R (Fin n) (rename finSuccEquivLast f) := by
  first
  | have h : (finSuccEquiv R n).toAlgHom.comp (rename (finRotate (n + 1))) =
        (optionEquivLeft R (Fin n)).toAlgHom.comp (rename finSuccEquivLast) := by
      apply algHom_ext
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [finSuccEquiv_X_zero, optionEquivLeft_X_none]
      · simp [finSuccEquiv_X_succ, optionEquivLeft_X_some]
    exact DFunLike.congr_fun h f

/-- Moving the polynomial variable into the coefficient ring maps a constant multivariate
polynomial by the univariate constant-coefficient homomorphism. -/
theorem optionEquivRight_optionEquivLeft_symm_C {σ : Type*} (g : MvPolynomial σ R) :
    ((optionEquivLeft R σ).symm.trans (optionEquivRight R σ)) (Polynomial.C g) =
      map Polynomial.C g := by
  first
  | rw [AlgEquiv.trans_apply]
    induction g using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, optionEquivLeft_symm_C_X,
        optionEquivRight_X_some, hp, map_X]

/-- Moving the univariate variable into the coefficient ring commutes with specializing the
multivariate variables, while retaining the univariate variable as a polynomial variable. -/
theorem eval₂Hom_optionEquivRight_optionEquivLeft_symm {σ S : Type*} [CommSemiring S]
    (f : R →+* S) (x : σ → S) (p : Polynomial (MvPolynomial σ R)) :
    eval₂Hom (Polynomial.mapRingHom f) (Polynomial.C ∘ x)
        (((optionEquivLeft R σ).symm.trans (optionEquivRight R σ)) p) =
      p.map (eval₂Hom f x) := by
  first
  | have hC (g : MvPolynomial σ R) :
        eval₂Hom (Polynomial.mapRingHom f) (Polynomial.C ∘ x)
            (((optionEquivLeft R σ).symm.trans (optionEquivRight R σ)) (Polynomial.C g)) =
          Polynomial.C (eval₂Hom f x g) := by
      rw [optionEquivRight_optionEquivLeft_symm_C, eval₂Hom_map_hom,
        Polynomial.mapRingHom_comp_C]
      exact (map_eval₂Hom f x Polynomial.C g).symm
    have h : (eval₂Hom (Polynomial.mapRingHom f) (Polynomial.C ∘ x)).comp
        ((optionEquivLeft R σ).symm.trans (optionEquivRight R σ)) =
          Polynomial.mapRingHom (eval₂Hom f x) := by
      apply Polynomial.ringHom_ext
      · intro g
        simpa only [RingHom.comp_apply, RingHom.coe_coe, Polynomial.coe_mapRingHom,
          Polynomial.map_C] using hC g
      · simp
    exact RingHom.congr_fun h p

/-- Moving the univariate variable into the coefficient ring and then taking constant
coefficients of all coefficients recovers the constant coefficient in the univariate
variable. -/
theorem map_constantCoeff_optionEquivRight_optionEquivLeft_symm {σ : Type*}
    (p : Polynomial (MvPolynomial σ R)) :
    map Polynomial.constantCoeff (((optionEquivLeft R σ).symm.trans (optionEquivRight R σ)) p) =
      p.coeff 0 := by
  first
  | have hC : Polynomial.constantCoeff.comp (Polynomial.C : R →+* Polynomial R) = RingHom.id R := by
      ext
      simp
    have h : (map (Polynomial.constantCoeff (R := R))).comp
        ((optionEquivLeft R σ).symm.trans (optionEquivRight R σ) :
          Polynomial (MvPolynomial σ R) →+* MvPolynomial σ (Polynomial R)) =
          Polynomial.constantCoeff := by
      apply Polynomial.ringHom_ext
      · intro g
        rw [RingHom.comp_apply, RingHom.coe_coe, optionEquivRight_optionEquivLeft_symm_C, map_map,
          hC, map_id, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
      · simp
    exact RingHom.congr_fun h p

section Last

open Finsupp

/-- Moving the last variable into the coefficients sends the monomial `r • X ^ d` to the monomial
in the first `n` variables with exponent `init d` whose coefficient is `r • Xₙ ^ d (Fin.last n)`. -/
theorem optionEquivRight_rename_finSuccEquivLast_monomial (d : Fin (n + 1) →₀ ℕ) (r : R) :
    optionEquivRight R (Fin n) (rename finSuccEquivLast (monomial d r)) =
      monomial (init d) (Polynomial.monomial (d (Fin.last n)) r) := by
  first
  | rw [monomial_eq, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp)]
    simp [Fin.prod_univ_castSucc, Fin.init, ← Polynomial.C_mul_X_pow_eq_monomial]
    ring

/-- After moving the last variable into the coefficients, the coefficient of `Xₙ ^ k` in the
coefficient of `Xᵘ` is the coefficient of `f` at the exponent `Finsupp.snoc u k`. -/
theorem optionEquivRight_rename_finSuccEquivLast_coeff_coeff (f : MvPolynomial (Fin (n + 1)) R)
    (u : Fin n →₀ ℕ) (k : ℕ) :
    ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).coeff u).coeff k =
      f.coeff (snoc u k) := by
  first
  | induction f using MvPolynomial.induction_on' with
    | monomial d r =>
      simp only [optionEquivRight_rename_finSuccEquivLast_monomial, coeff_monomial, eq_snoc_iff,
        ite_and]
      split_ifs <;> simp [Polynomial.coeff_monomial, *]
    | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hp,
        hq]

end Last

end MvPolynomial
end -- closes the original EOF section from source line 58
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/MvPolynomial/Equiv.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Reductum.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Polynomial reducta

The reductum `p.reductum k` retains exactly the terms of `p` of degree strictly below `k`.
The finite set `p.reducta` contains the reducta at every cutoff through `p.natDegree + 1`, so it
includes both zero and `p` itself.  After any coefficient specialization, one member of this set
maps to the specialized polynomial: take the cutoff immediately above its new degree.  This is
the finite degree-case decomposition needed when polynomial degrees can drop under specialization.

The reductum is `PowerSeries.trunc` applied to `p` viewed as a power series.  Reducta also agree
with repeatedly deleting leading terms, connecting the fixed cutoffs used for specialization to
Mathlib's `eraseLead` API.

## Main results

* `Polynomial.coeff_reductum`: a reductum keeps precisely the coefficients below its cutoff.
* `Polynomial.reductum_reductum`: nested reducta reduce to the smaller cutoff.
* `Polynomial.derivative_reductum`: differentiation lowers the cutoff by one.
* `Polynomial.reductum_natDegree`: the cutoff at the degree deletes the leading term.
* `Polynomial.reducta_map`: coefficient maps carry the reducta onto the reducta of the mapped
  polynomial, with no injectivity or degree-preservation hypothesis.
* `Polynomial.exists_mem_reducta_map_eq`: every coefficient specialization is the image of a
  reductum of the original polynomial.
* `Polynomial.reducta_eq_eraseLeadOrbit`: the bounded cutoffs give exactly the finite orbit under
  repeated deletion of leading terms.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapters 4 and 11.
-/

public section

namespace Polynomial

open Polynomial

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The part of `p` of degree strictly below `k`. -/
noncomputable def reductum (p : R[X]) (k : ℕ) : R[X] :=
  PowerSeries.trunc k (p : PowerSeries R)

/-- A reductum is the truncation of `p`, viewed as a power series, at the same cutoff. -/
theorem reductum_eq_trunc (p : R[X]) (k : ℕ) :
    p.reductum k = PowerSeries.trunc k (p : PowerSeries R) := by
  first
  | rw [reductum]

/-- A reductum keeps the coefficients strictly below its cutoff and discards the rest. -/
@[simp, grind =]
theorem coeff_reductum (p : R[X]) (k i : ℕ) :
    (p.reductum k).coeff i = if i < k then p.coeff i else 0 := by
  first
  | simp [reductum, PowerSeries.coeff_trunc]

/-- A reductum is the sum of the monomials of `p` below its cutoff. -/
theorem reductum_eq_sum (p : R[X]) (k : ℕ) :
    p.reductum k = ∑ i ∈ Finset.range k, monomial i (p.coeff i) := by
  first
  | ext i
    simp [coeff_monomial]

/-- The reductum at cutoff zero is zero. -/
@[simp]
theorem reductum_zero (p : R[X]) : p.reductum 0 = 0 := by
  first
  | ext
    simp

/-- Every reductum of the zero polynomial is zero. -/
@[simp]
theorem zero_reductum (k : ℕ) :
    (0 : R[X]).reductum k = 0 := by
  first
  | ext
    simp

/-- Increasing the cutoff by one adjoins the coefficient at the old cutoff. -/
theorem reductum_succ (p : R[X]) (k : ℕ) :
    p.reductum (k + 1) = p.reductum k + monomial k (p.coeff k) := by
  first
  | simpa [reductum] using PowerSeries.trunc_succ (p : PowerSeries R) k

/-- The degree of a reductum is strictly below its cutoff. -/
theorem degree_reductum_lt (p : R[X]) (k : ℕ) :
    (p.reductum k).degree < k := by
  first
  | exact PowerSeries.degree_trunc_lt (p : PowerSeries R) k

/-- The natural degree of a reductum at a positive cutoff is strictly below that cutoff. -/
theorem natDegree_reductum_lt (p : R[X]) (k : ℕ) :
    (p.reductum (k + 1)).natDegree < k + 1 := by
  first
  | exact PowerSeries.natDegree_trunc_lt (p : PowerSeries R) k

/-- A cutoff strictly above the degree does not change a polynomial. -/
theorem reductum_eq_self {p : R[X]} {k : ℕ} (h : p.natDegree < k) :
    p.reductum k = p := by
  first
  | ext i
    rw [coeff_reductum, ite_eq_left_iff]
    intro hi
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Cutting off immediately above the degree returns the original polynomial, including for zero. -/
@[simp]
theorem reductum_natDegree_add_one (p : R[X]) :
    p.reductum (p.natDegree + 1) = p := by
  first
  | exact p.reductum_eq_self (Nat.lt_succ_self _)

/-- Nested reducta use the minimum of their cutoffs. -/
@[simp]
theorem reductum_reductum (p : R[X]) (k l : ℕ) :
    (p.reductum l).reductum k = p.reductum (min k l) := by
  first
  | ext i
    simp only [coeff_reductum, lt_min_iff]
    by_cases hk : i < k <;> by_cases hl : i < l <;> simp [hk, hl]

/-- Taking a smaller reductum after a larger one is the same as taking the smaller reductum
directly. -/
theorem reductum_reductum_of_le (p : R[X]) {k l : ℕ} (h : k ≤ l) :
    (p.reductum l).reductum k = p.reductum k := by
  first
  | rw [reductum_reductum, min_eq_left h]

/-- Reducta commute with coefficient maps, with no degree-preservation hypothesis. -/
@[simp]
theorem reductum_map (f : R →+* S) (p : R[X]) (k : ℕ) :
    (p.map f).reductum k = (p.reductum k).map f := by
  first
  | ext i
    simp [apply_ite f]

/-- Differentiating a reductum lowers its cutoff by one. -/
theorem derivative_reductum (p : R[X]) (k : ℕ) :
    (p.reductum (k + 1)).derivative = p.derivative.reductum k := by
  first
  | ext i
    simp only [coeff_derivative, coeff_reductum]
    by_cases hi : i < k <;> simp [hi]

/-- The reductum at the degree is Mathlib's operation deleting the leading term. -/
theorem reductum_natDegree (p : R[X]) :
    p.reductum p.natDegree = p.eraseLead := by
  first
  | ext i
    rw [coeff_reductum, eraseLead_coeff]
    by_cases hi : i < p.natDegree
    · simp [hi, hi.ne]
    · by_cases hieq : i = p.natDegree
      · simp [hieq]
      · have hlt : p.natDegree < i := lt_of_le_of_ne (Nat.le_of_not_gt hi) (Ne.symm hieq)
        simp [hi, hieq, coeff_eq_zero_of_natDegree_lt hlt]

/-- Below the degree of `p`, taking a reductum is unaffected by first deleting the leading term. -/
theorem reductum_eraseLead (p : R[X]) {k : ℕ} (h : k ≤ p.natDegree) :
    p.eraseLead.reductum k = p.reductum k := by
  first
  | ext i
    simp only [coeff_reductum, eraseLead_coeff]
    by_cases hi : i < k
    · have hine : i ≠ p.natDegree := (hi.trans_le h).ne
      simp [hi, hine]
    · simp [hi]

/-- A cutoff above the degree of `p.eraseLead` but not above the degree of `p` deletes exactly
the leading term. -/
theorem reductum_eq_eraseLead_of_lt_of_le {p : R[X]} {k : ℕ}
    (h₁ : p.eraseLead.natDegree < k) (h₂ : k ≤ p.natDegree) :
    p.reductum k = p.eraseLead := by
  first
  | rw [← p.reductum_eraseLead h₂, p.eraseLead.reductum_eq_self h₁]

/-- The finite set of all reducta at cutoffs from zero through one above the degree. -/
noncomputable def reducta (p : R[X]) : Finset R[X] := by
  first
  | classical
    exact (Finset.range (p.natDegree + 2)).image p.reductum

/-- Membership in `reducta` is membership at one of its bounded cutoffs. -/
theorem mem_reducta {p q : R[X]} :
    q ∈ p.reducta ↔ ∃ k < p.natDegree + 2, p.reductum k = q := by
  first
  | classical
    simp [reducta]

/-- Zero belongs to the reducta of every polynomial. -/
@[simp]
theorem zero_mem_reducta (p : R[X]) : 0 ∈ p.reducta := by
  first
  | rw [mem_reducta]
    exact ⟨0, by omega, p.reductum_zero⟩

/-- Every polynomial belongs to its own reducta. -/
@[simp]
theorem self_mem_reducta (p : R[X]) : p ∈ p.reducta := by
  first
  | rw [mem_reducta]
    exact ⟨p.natDegree + 1, by omega, p.reductum_natDegree_add_one⟩

/-- The reductum at every cutoff belongs to the reducta, including cutoffs past the degree. -/
@[simp]
theorem reductum_mem_reducta (p : R[X]) (k : ℕ) : p.reductum k ∈ p.reducta := by
  first
  | by_cases hk : k < p.natDegree + 2
    · exact mem_reducta.2 ⟨k, hk, rfl⟩
    · rw [p.reductum_eq_self (by omega)]
      exact p.self_mem_reducta

/-- Deleting the leading term produces a member of the reducta. -/
theorem eraseLead_mem_reducta (p : R[X]) :
    p.eraseLead ∈ p.reducta := by
  first
  | rw [mem_reducta]
    exact ⟨p.natDegree, by omega, p.reductum_natDegree⟩

/-- The only reductum of the zero polynomial is zero. -/
@[simp]
theorem reducta_zero : (0 : R[X]).reducta = {0} := by
  first
  | ext q
    rw [mem_reducta, Finset.mem_singleton]
    constructor
    · rintro ⟨k, _, hq⟩
      simpa using hq.symm
    · intro hq
      exact ⟨0, by omega, by simp [hq]⟩

open scoped Classical in
/-- The reducta consist of `p` together with the reducta after deleting its leading term. -/
theorem reducta_eq_insert_eraseLead_reducta (p : R[X]) :
    p.reducta = insert p p.eraseLead.reducta := by
  first
  | classical
    ext q
    constructor
    · intro hq
      rw [mem_reducta] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      rw [Finset.mem_insert]
      by_cases hkp : k ≤ p.natDegree
      · right
        by_cases hke : k < p.eraseLead.natDegree + 2
        · rw [mem_reducta]
          exact ⟨k, hke, p.reductum_eraseLead hkp⟩
        · rw [reductum_eq_eraseLead_of_lt_of_le (by omega) hkp]
          exact p.eraseLead.self_mem_reducta
      · left
        have hk' : k = p.natDegree + 1 := by omega
        simp [hk']
    · intro hq
      rw [Finset.mem_insert] at hq
      rcases hq with hqp | hq
      · subst q
        exact p.self_mem_reducta
      · rw [mem_reducta] at hq
        obtain ⟨k, _, rfl⟩ := hq
        by_cases hkp : k ≤ p.natDegree
        · rw [mem_reducta]
          exact ⟨k, by omega, (p.reductum_eraseLead hkp).symm⟩
        · have hdeg : p.eraseLead.natDegree < k :=
            p.eraseLead_natDegree_le_aux.trans_lt (Nat.lt_of_not_ge hkp)
          rw [p.eraseLead.reductum_eq_self hdeg]
          exact p.eraseLead_mem_reducta

/-- The finite orbit obtained by repeatedly deleting leading terms, including the zero polynomial
at the end. -/
noncomputable def eraseLeadOrbit (p : R[X]) : Finset R[X] := by
  first
  | classical
    exact (Finset.range (p.support.card + 1)).image fun k ↦ (eraseLead^[k]) p

/-- Membership in the `eraseLead` orbit is being one of the first `p.support.card + 1` iterates
of `eraseLead` on `p`. -/
theorem mem_eraseLeadOrbit {p q : R[X]} :
    q ∈ p.eraseLeadOrbit ↔ ∃ k ≤ p.support.card, (eraseLead^[k]) p = q := by
  first
  | classical
    simp [eraseLeadOrbit]

/-- The orbit of zero under `eraseLead` is the singleton containing zero. -/
@[simp]
theorem eraseLeadOrbit_zero :
    eraseLeadOrbit (0 : R[X]) = {0} := by
  first
  | classical
    simp [eraseLeadOrbit]

open scoped Classical in
/-- The `eraseLead` orbit of a polynomial is the polynomial together with the orbit of the
polynomial with its leading term deleted. -/
theorem eraseLeadOrbit_eq_insert (p : R[X]) :
    p.eraseLeadOrbit = insert p p.eraseLead.eraseLeadOrbit := by
  first
  | classical
    by_cases hp : p = 0
    · subst hp
      simp
    ext q
    simp only [eraseLeadOrbit, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨k, hk, rfl⟩
      cases k with
      | zero => simp
      | succ k =>
          right
          refine ⟨k, ?_, ?_⟩
          · have hcard := card_support_eraseLead_add_one hp
            omega
          · exact Function.iterate_succ_apply eraseLead k p
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · refine ⟨k + 1, ?_, ?_⟩
        · have hcard := card_support_eraseLead_add_one hp
          omega
        · exact (Function.iterate_succ_apply eraseLead k p).symm

/-- The finite set of reducta at bounded cutoffs is exactly the finite orbit under deletion of
leading terms. -/
theorem reducta_eq_eraseLeadOrbit (p : R[X]) :
    p.reducta = p.eraseLeadOrbit := by
  first
  | classical
    induction hn : p.support.card using Nat.strong_induction_on generalizing p with
    | h n ih =>
        by_cases hp : p = 0
        · subst p
          rw [reducta_zero, eraseLeadOrbit_zero]
        · have hcard : p.eraseLead.support.card < n := by
            have := card_support_eraseLead_add_one hp
            omega
          rw [p.reducta_eq_insert_eraseLead_reducta, p.eraseLeadOrbit_eq_insert,
            ih _ hcard p.eraseLead rfl]

/-- Every iterate of `eraseLead` on `p` lies in its `eraseLead` orbit, including the iterates past
the point where the orbit reaches zero. -/
theorem iterate_eraseLead_mem_eraseLeadOrbit (p : R[X]) (k : ℕ) :
    (eraseLead^[k]) p ∈ p.eraseLeadOrbit := by
  first
  | classical
    rw [← reducta_eq_eraseLeadOrbit]
    induction k generalizing p with
    | zero => exact p.self_mem_reducta
    | succ k ih =>
        rw [Function.iterate_succ_apply, reducta_eq_insert_eraseLead_reducta]
        exact Finset.mem_insert_of_mem (ih _)

open scoped Classical in
/-- Coefficient maps carry all reducta exactly to the reducta of the mapped polynomial, with no
injectivity or degree-preservation hypothesis. -/
theorem reducta_map (f : R →+* S) (p : R[X]) :
    (p.map f).reducta = p.reducta.image (Polynomial.map f) := by
  first
  | classical
    have hdeg : (p.map f).natDegree ≤ p.natDegree := natDegree_map_le
    ext q
    rw [Finset.mem_image]
    constructor
    · rw [mem_reducta]
      rintro ⟨k, hk, rfl⟩
      exact ⟨p.reductum k, mem_reducta.2 ⟨k, by omega, rfl⟩, (p.reductum_map f k).symm⟩
    · rintro ⟨_, hq, rfl⟩
      obtain ⟨k, -, rfl⟩ := mem_reducta.1 hq
      rw [← reductum_map]
      by_cases hk : k < (p.map f).natDegree + 2
      · exact mem_reducta.2 ⟨k, hk, rfl⟩
      · rw [reductum_eq_self (by omega)]
        exact (p.map f).self_mem_reducta

/-- Cutting off immediately above the degree after specialization maps back to the specialized
polynomial.  This gives an explicit member of `p.reducta` witnessing
`exists_mem_reducta_map_eq`. -/
theorem map_reductum_natDegree_map_add_one (f : R →+* S) (p : R[X]) :
    (p.reductum ((p.map f).natDegree + 1)).map f = p.map f := by
  first
  | rw [← reductum_map, reductum_natDegree_add_one]

/-- Cutting off immediately above the degree after specialization gives a reductum whose own
degree is the specialized degree, so formal degree bounds taken at this reductum are the actual
degrees after specialization. -/
theorem natDegree_reductum_natDegree_map_add_one (f : R →+* S) (p : R[X]) :
    (p.reductum ((p.map f).natDegree + 1)).natDegree = (p.map f).natDegree := by
  first
  | refine Nat.le_antisymm (Nat.lt_succ_iff.mp (p.natDegree_reductum_lt _)) ?_
    conv_lhs => rw [← map_reductum_natDegree_map_add_one f p]
    exact natDegree_map_le

/-- Every coefficient specialization is the image of a member of the original polynomial's finite
set of reducta. -/
theorem exists_mem_reducta_map_eq (f : R →+* S) (p : R[X]) :
    ∃ q ∈ p.reducta, q.map f = p.map f := by
  first
  | classical
    have h := (p.map f).self_mem_reducta
    rw [reducta_map, Finset.mem_image] at h
    exact h

end Polynomial
end -- closes the original EOF section from source line 43
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Reductum.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Coeff/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coefficients of shifted polynomials with a degree bound

Multiplication by `X ^ l` shifts a polynomial's coefficients by `l`. When its degree is
bounded by `n`, the shifted coefficients vanish outside the window from `l` to `l + n`.
This identity identifies bounded coefficient rows with coefficients of shifted polynomials.
-/

public section

namespace TauCeti

open Polynomial

/-- The coefficients of `X ^ l * p` vanish outside the window from `l` to `l + n`
when `p.natDegree ≤ n`. -/
theorem _root_.Polynomial.coeff_X_pow_mul_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (l d : ℕ) :
    (X ^ l * p).coeff d = if l ≤ d ∧ d ≤ l + n then p.coeff (d - l) else 0 := by
  first
  | rw [coeff_X_pow_mul']
    by_cases h : l ≤ d
    · by_cases h' : d ≤ l + n
      · simp [h, h']
      · have hz : p.coeff (d - l) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        simp [h, h', hz]
    · simp [h]

end TauCeti
end -- closes the original EOF section from source line 18
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Coeff/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Data/Finset/Inversions.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Inversions of a map on a finite set

For a map `f : α → β` between linear orders and a finite set `s ⊆ α`, the inversions of `f` on
`s` are the pairs `a < b` of elements of `s` whose order `f` reverses, `f b < f a`. When `f` is
injective, the parity of their number is the sign of the permutation of `s` obtained by comparing
the order of `s` with the order of its image `f(s)`. For a permutation `σ` of `Fin n`,
`TauCeti.sign_eq_neg_one_pow_card_inversion` identifies `(-1) ^ #(Finset.univ.inversions σ)` with
`Equiv.Perm.sign σ`.

These signs compare two orderings of the same finite set. In a signed cube totalization the edge
`S ⟶ S ∪ {a}` carries the sign `(-1) ^ #{b ∈ S | b < a}`, and reordering the indices of the cube
by `f` changes these signs by the inversion signs of `f` on the two vertices of the edge
(`Finset.neg_one_pow_card_inversions_insert`). Inversion signs are multiplicative under
composition (`Finset.neg_one_pow_card_inversions_comp`).

## Main definitions

* `Finset.inversions f s`: the pairs `(a, b)` of elements of `s` with `a < b` and `f b < f a`.

## Main results

* `Finset.inversions_univ`: on a whole finite type, the inversions are all pairs `a < b` with
  `f b < f a`.
* `Finset.card_inversions_insert`: adjoining a new element `a` to `s` adds the inversions
  involving `a`.
* `Finset.card_inversions_insert_add_card_filter_lt`: for an injective map, the same comparison
  of `insert a s` with `s` as a count of elements, up to an even number.
* `Finset.neg_one_pow_card_inversions_insert`: the inversion sign of an injective map on
  `insert a s`, compared with that on `s`, is the sign relating the position of `a` in `s` to the
  position of `f a` in `f(s)`.
* `Finset.even_card_inversions_comp`: the inversion counts of `f` on `s`, of `g` on `f(s)` and of
  `g ∘ f` on `s` add up to an even number.
* `Finset.neg_one_pow_card_inversions_comp`: the inversion sign of `g ∘ f` on `s` is the product
  of the inversion signs of `f` on `s` and of `g` on `f(s)`.
-/

public section

open Function

namespace Finset

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- The inversions of `f` on `s`: the pairs `(a, b)` of elements of `s` with `a < b` whose order
`f` reverses, `f b < f a`. -/
def inversions (f : α → β) (s : Finset α) : Finset (α × α) :=
  {p ∈ s ×ˢ s | p.1 < p.2 ∧ f p.2 < f p.1}

@[simp]
theorem mem_inversions {f : α → β} {s : Finset α} {p : α × α} :
    p ∈ s.inversions f ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 ∧ f p.2 < f p.1 := by
  first
  | simp [inversions, and_assoc]

@[simp]
theorem inversions_empty (f : α → β) : (∅ : Finset α).inversions f = ∅ := by
  first
  | ext
    simp

/-- A monotone map has no inversions. -/
theorem inversions_eq_empty_of_monotone {f : α → β} (hf : Monotone f) (s : Finset α) :
    s.inversions f = ∅ := by
  first
  | ext p
    simp only [mem_inversions, notMem_empty, iff_false, not_and]
    exact fun _ _ h ↦ (hf h.le).not_gt

/-- On the whole of a finite type, the inversions of `f` are all the pairs `a < b` with
`f b < f a`. -/
theorem inversions_univ [Fintype α] (f : α → β) :
    univ.inversions f = univ.filter fun p : α × α ↦ p.1 < p.2 ∧ f p.2 < f p.1 := by
  first
  | rw [inversions, univ_product_univ]

@[simp]
theorem inversions_id (s : Finset α) : s.inversions id = ∅ :=
  inversions_eq_empty_of_monotone monotone_id s

/-- Adjoining a new element `a` to `s` adds the inversions `(b, a)` with `b < a` and the
inversions `(a, b)` with `a < b`. -/
theorem card_inversions_insert (f : α → β) {s : Finset α} {a : α} (ha : a ∉ s) :
    #((insert a s).inversions f) = #(s.inversions f) + #{b ∈ s | b < a ∧ f a < f b} +
      #{b ∈ s | a < b ∧ f b < f a} := by
  first
  | have hdecomp : (insert a s).inversions f = s.inversions f ∪
        {b ∈ s | b < a ∧ f a < f b}.image (·, a) ∪ {b ∈ s | a < b ∧ f b < f a}.image (a, ·) := by
      ext ⟨x, y⟩
      simp only [mem_inversions, mem_insert, mem_union, mem_image, mem_filter, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl | hx, rfl | hy, hxy, hf⟩
        · exact absurd hxy (lt_irrefl _)
        · exact Or.inr ⟨y, ⟨hy, hxy, hf⟩, rfl, rfl⟩
        · exact Or.inl (Or.inr ⟨x, ⟨hx, hxy, hf⟩, rfl, rfl⟩)
        · exact Or.inl (Or.inl ⟨hx, hy, hxy, hf⟩)
      · rintro ((⟨hx, hy, hxy, hf⟩ | ⟨b, ⟨hb, hba, hfb⟩, rfl, rfl⟩) | ⟨b, ⟨hb, hab, hfb⟩, rfl, rfl⟩)
        · exact ⟨Or.inr hx, Or.inr hy, hxy, hf⟩
        · exact ⟨Or.inr hb, Or.inl rfl, hba, hfb⟩
        · exact ⟨Or.inl rfl, Or.inr hb, hab, hfb⟩
    rw [hdecomp, card_union_of_disjoint, card_union_of_disjoint,
      card_image_of_injective _ (Prod.mk_left_injective a),
      card_image_of_injective _ (Prod.mk_right_injective a)]
    · rw [disjoint_left]
      simp only [mem_inversions, mem_image, mem_filter, not_exists, not_and]
      rintro p ⟨-, hp, -⟩ b - rfl
      exact ha hp
    · rw [disjoint_left]
      simp only [mem_union, mem_inversions, mem_image, mem_filter, not_exists, not_and]
      rintro p (⟨hp, -⟩ | ⟨b, ⟨hb, -⟩, rfl⟩) c - h
      · subst h
        exact ha hp
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h
        exact ha hb

/-- For an injective map and `a ∉ s`, the inversions on `insert a s` and the elements of `s`
below `a` together count the inversions on `s` and the elements of `s` whose image lies below
`f a`, up to an even number. -/
theorem card_inversions_insert_add_card_filter_lt {f : α → β} (hf : Injective f)
    {s : Finset α} {a : α} (ha : a ∉ s) :
    #((insert a s).inversions f) + #{b ∈ s | b < a} =
      #(s.inversions f) + #{b ∈ s | f b < f a} + 2 * #{b ∈ s | b < a ∧ f a < f b} := by
  first
  | have hne {b : α} (hb : b ∈ s) : b ≠ a := fun h ↦ ha (h ▸ hb)
    -- Split the elements below `a`, and those whose image lies below `f a`, according to the
    -- other order.
    have h₁ := card_filter_add_card_filter_not (s := {b ∈ s | b < a}) (fun b ↦ f b < f a)
    have h₂ := card_filter_add_card_filter_not (s := {b ∈ s | f b < f a}) (fun b ↦ b < a)
    simp only [filter_filter] at h₁ h₂
    rw [filter_congr fun b hb ↦ show b < a ∧ ¬f b < f a ↔ b < a ∧ f a < f b by
      grind [hf.ne (hne hb)]] at h₁
    rw [filter_congr fun b hb ↦ show f b < f a ∧ ¬b < a ↔ a < b ∧ f b < f a by
      grind [hne hb]] at h₂
    rw [filter_congr fun b _ ↦ show f b < f a ∧ b < a ↔ b < a ∧ f b < f a from and_comm] at h₂
    rw [card_inversions_insert f ha]
    omega

/-- **Reordering signs along an edge.** For an injective map `f` and `a ∉ s`, the inversion sign
of `f` on `insert a s`, times the sign recording the position of `a` in `s`, is the inversion sign
of `f` on `s` times the sign recording the position of `f a` in `f(s)`. -/
theorem neg_one_pow_card_inversions_insert {R : Type*} [Monoid R] [HasDistribNeg R]
    {f : α → β} (hf : Injective f) {s : Finset α} {a : α} (ha : a ∉ s) :
    (-1 : R) ^ #((insert a s).inversions f) * (-1) ^ #{b ∈ s | b < a} =
      (-1) ^ #(s.inversions f) * (-1) ^ #{b ∈ s | f b < f a} := by
  first
  | rw [← pow_add, ← pow_add, card_inversions_insert_add_card_filter_lt hf ha, pow_add _ _ (2 * _),
      pow_mul, neg_one_sq, one_pow, mul_one]

/-- The parities of the inversion counts of `f` on `s`, of `g` on `f(s)` and of `g ∘ f` on `s` add
up to zero. -/
theorem even_card_inversions_comp {f : α ↪ β} {g : β → γ} (hg : Injective g)
    (s : Finset α) :
    Even (#(s.inversions (g ∘ f)) + #(s.inversions f) + #((s.map f).inversions g)) := by
  first
  | classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hfa : f a ∉ s.map f := by simpa using ha
      have h₁ := card_inversions_insert_add_card_filter_lt (hg.comp f.injective) ha
      have h₂ := card_inversions_insert_add_card_filter_lt f.injective ha
      have h₃ := card_inversions_insert_add_card_filter_lt hg hfa
      rw [map_insert]
      rw [filter_map, card_map, filter_map, card_map] at h₃
      simp only [comp_apply] at h₁ h₃ ⊢
      rw [Nat.even_iff] at ih ⊢
      omega

/-- **Inversion signs are multiplicative.** For an embedding `f` and an injective map `g`, the
inversion sign of `g ∘ f` on `s` is the product of the inversion signs of `f` on `s` and of `g` on
`f(s)`. -/
theorem neg_one_pow_card_inversions_comp {R : Type*} [Monoid R] [HasDistribNeg R] (f : α ↪ β)
    {g : β → γ} (hg : Injective g) (s : Finset α) :
    (-1 : R) ^ #(s.inversions (g ∘ f)) =
      (-1) ^ #(s.inversions f) * (-1) ^ #((s.map f).inversions g) := by
  first
  | have h := even_card_inversions_comp (f := f) hg s
    rw [add_assoc, Nat.even_add] at h
    rw [← pow_add]
    rcases Nat.even_or_odd #(s.inversions (g ∘ f)) with h' | h'
    · rw [h'.neg_one_pow, (h.1 h').neg_one_pow]
    · have h'' : Odd (#(s.inversions f) + #((s.map f).inversions g)) :=
        Nat.not_even_iff_odd.1 fun h'' ↦ Nat.not_even_iff_odd.2 h' (h.2 h'')
      rw [h'.neg_one_pow, h''.neg_one_pow]

end Finset
end -- closes the original EOF section from source line 48
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Finset/Inversions.lean -/

/- BEGIN SOURCE: TauCeti/GroupTheory/Perm/Inversion.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Signs of permutations, inversions, and signed-sum reindexing

An *inversion* of `σ : Equiv.Perm (Fin n)` is a pair of indices `i < j` with `σ j < σ i`. The
sign of `σ` is `(-1)` raised to the number of inversions. Mathlib exposes the sign as the product
`Equiv.Perm.sign_eq_prod_prod_Ioi`; this file turns that product into the cardinality of the
finite set of inversions, which is the form met by combinatorial permutation counts. It also
records the sign of a shuffle of two ordered blocks. Finally, it uses the sign of a block swap to
reindex signed sums over permutations when rotating index blocks.

## Main results

* `TauCeti.sign_eq_neg_one_pow_card_inversion`: the sign of a permutation `σ` of `Fin n` is
  `(-1)` to the number of its inversions `Finset.univ.inversions σ`.
* `Fin.sign_revPerm`: reversing `Fin n` has sign `(-1) ^ n.choose 2`.
* `TauCeti.sign_shuffle`: the sign of a shuffle permutation is a power of `-1`.
* `TauCeti.sign_finAddFlip_trans_finCongr`: the block swap of `Fin (m + n)`, which exchanges the
  first `m` indices with the last `n`, has sign `(-1) ^ (m * n)`.
* `TauCeti.sum_sign_smul_permCongr_mul`: reindexing a signed sum over permutations along an
  equivalence followed by right multiplication.
* `TauCeti.sum_sign_smul_rotate_blocks`: reindexing a signed sum over permutations along a
  block swap moves the last block of `k` indices in front of the other `l + m` at the cost of
  the sign `(-1) ^ (k * (l + m))`; graded identities for iterated wedge products reorder their
  factors this way.

The sign of the block swap was first proved on the earlier Tau Ceti split branch at commit
`05c2722248` and is adapted here to current `main`.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- The sign of a permutation of `Fin n` is `(-1)` raised to the number of its inversions
`Finset.univ.inversions σ`, the pairs of columns `i < j` whose values are in the opposite order. -/
theorem sign_eq_neg_one_pow_card_inversion (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Finset.univ.inversions σ).card := by
  first
  | classical
    rw [Finset.inversions_univ]
    have hIoi : ∀ i : Fin n, Finset.Ioi i = Finset.univ.filter fun j : Fin n => i < j := by
      intro i
      ext j
      simp
    have hprod :
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1)) =
          ∏ p ∈ Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2,
            (if σ p.1 < σ p.2 then (1 : ℤˣ) else -1) := by
      rw [Finset.prod_filter, Fintype.prod_prod_type]
      exact Finset.prod_congr rfl fun i _ => by rw [hIoi i, Finset.prod_filter]
    have hinv :
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).filter
            (fun p => ¬ σ p.1 < σ p.2) =
          Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1 := by
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun p _ => ?_
      constructor
      · rintro ⟨hlt, hnot⟩
        have hne : σ p.1 ≠ σ p.2 := fun h => (ne_of_lt hlt) (σ.injective h)
        exact ⟨hlt, lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hne)⟩
      · rintro ⟨hlt, hgt⟩
        exact ⟨hlt, not_lt.mpr (le_of_lt hgt)⟩
    rw [σ.sign_eq_prod_prod_Ioi, hprod, Finset.prod_ite]
    simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
    rw [hinv]

/-- Reversing the order of `Fin n` has sign `(-1) ^ n.choose 2`: every pair of indices is an
inversion. -/
@[simp]
theorem _root_.Fin.sign_revPerm (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1) ^ n.choose 2 := by
  first
  | have h : (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ Fin.revPerm p.2 < Fin.revPerm p.1) =
        Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 :=
      Finset.filter_congr fun p _ => by simp
    rw [sign_eq_neg_one_pow_card_inversion, Finset.inversions_univ, h,
      Fintype.card_product_filter_lt, Fintype.card_fin]

private lemma card_inversion_finAddFlip_trans_finCongr (m n : ℕ) :
    (Finset.univ.filter fun p : Fin (m + n) × Fin (m + n) =>
      p.1 < p.2 ∧
        (finAddFlip.trans (finCongr (add_comm n m))) p.2 <
          (finAddFlip.trans (finCongr (add_comm n m))) p.1).card = m * n := by
  first
  | classical
    let e := Equiv.prodCongr
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
    let f : Fin m × Fin n ↪ (Fin m ⊕ Fin n) × (Fin m ⊕ Fin n) :=
      ⟨Prod.map Sum.inl Sum.inr, Sum.inl_injective.prodMap Sum.inr_injective⟩
    calc
      _ = ((Finset.univ.filter fun p : (Fin m ⊕ Fin n) × (Fin m ⊕ Fin n) =>
          (e p).1 < (e p).2 ∧
            (finAddFlip.trans (finCongr (add_comm n m))) (e p).2 <
              (finAddFlip.trans (finCongr (add_comm n m))) (e p).1).map e.toEmbedding).card := by
        congr 1
        ext p
        simp [e]
      _ = m * n := by
        rw [Finset.card_map]
        have hfilter :
            (Finset.univ.filter fun p : (Fin m ⊕ Fin n) × (Fin m ⊕ Fin n) =>
              (e p).1 < (e p).2 ∧
                (finAddFlip.trans (finCongr (add_comm n m))) (e p).2 <
                  (finAddFlip.trans (finCongr (add_comm n m))) (e p).1) =
              Finset.univ.map f := by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, e, f,
            Equiv.prodCongr_apply, Function.Embedding.coeFn_mk, Prod.map_apply, Prod.exists,
            Prod.mk.injEq]
          rcases a with a | a <;> rcases b with b | b <;>
            simp [finAddFlip, Fin.ext_iff, ← Fin.val_fin_lt, Fin.val_castAdd, Fin.val_natAdd,
              Fin.val_addNat] <;> omega
        rw [hfilter, Finset.card_map, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin]

/-- The block swap of `Fin (m + n)`, exchanging the first `m` indices with the last `n` while
preserving the order within each block, has sign `(-1) ^ (m * n)`: its inversions are exactly the
`m * n` pairs taken from different blocks. -/
theorem sign_finAddFlip_trans_finCongr (m n : ℕ) :
    Equiv.Perm.sign (finAddFlip.trans (finCongr (add_comm n m))) = (-1) ^ (m * n) := by
  first
  | rw [sign_eq_neg_one_pow_card_inversion, Finset.inversions_univ,
      card_inversion_finAddFlip_trans_finCongr]

section

open _root_.Finset

variable {k : ℕ}

/-- The sign of a shuffle permutation.  Let `e : Fin k ⊕ Fin m ≃ Fin n` be increasing on each
summand, so that the images of `Sum.inl` form a `k`-element set `I` and the images of `Sum.inr`
form its complement.  Then the sign of the shuffle, viewed as a permutation of `Fin n`, is
`(-1)` raised to the sum of the elements of `I` plus the sum of the positions in the first
summand.

Mathlib records the same sign for the `k`-subset `I` as `Set.powersetCard.sign I`, and
`Set.powersetCard.sign_eq_permOfDisjoint_sign` identifies that with the shuffle sign below; the
present form is the one met by determinants reindexed along `finSumEquivOfFinset`. -/
theorem sign_shuffle {m : ℕ} (h : k + m = n) (e : Fin k ⊕ Fin m ≃ Fin n)
    (hl : StrictMono (e ∘ Sum.inl)) (hr : StrictMono (e ∘ Sum.inr)) :
    Equiv.Perm.sign ((finSumFinEquiv.trans (finCongr h)).symm.trans e) =
      (-1) ^ (∑ a, (e (.inl a) : ℕ) + ∑ a : Fin k, (a : ℕ)) := by
  first
  | have hl' (a b) : e (.inl a) < e (.inl b) ↔ a < b := hl.lt_iff_lt
    have hr' (a b) : e (.inr a) < e (.inr b) ↔ a < b := hr.lt_iff_lt
    have h₁ (a b : Fin k) : Fin.castAdd m a < Fin.castAdd m b ↔ a < b := Iff.rfl
    have h₂ (a : Fin k) (b : Fin m) : Fin.castAdd m a < Fin.natAdd k b := by
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega
    have h₃ {α : Type} [Preorder α] (a b : α) : ¬(a < b ∧ b < a) := fun h ↦ lt_asymm h.1 h.2
    -- The only inversions are pairs `(inl a, inr b)` with `e (inr b) < e (inl a)`.
    -- For each `a`, the number of such `b` is the position of `e (inl a)` minus `a`.
    have hcount (a : Fin k) : #{b | e (.inr b) < e (.inl a)} + a = (e (.inl a) : ℕ) := by
      rw [← Fin.card_Iio, ← Fin.card_Iio (e _), ← filter_gt_eq_Iio, ← filter_gt_eq_Iio]
      simp only [card_filter, ← e.sum_comp (fun x ↦ ite _ _ _), Fintype.sum_sum_type, hl']
      ring
    -- Mathlib's product formula for the sign, with the interval `Iio` written as a filter, so that
    -- the double product can be reindexed along `E`.
    have hsign (τ : Equiv.Perm (Fin n)) :
        Equiv.Perm.sign τ = ∏ y, ∏ x, if x < y ∧ τ y < τ x then (-1 : ℤˣ) else 1 := by
      rw [τ.sign_eq_prod_prod_Iio]
      refine prod_congr rfl fun y _ ↦ ?_
      rw [← filter_gt_eq_Iio, prod_filter]
      refine prod_congr rfl fun x _ ↦ ?_
      split_ifs <;> grind [EmbeddingLike.apply_eq_iff_eq]
    set E := finSumFinEquiv.trans (finCongr h)
    rw [hsign, ← E.prod_comp]
    simp_rw [← E.prod_comp (fun x ↦ ite _ _ _)]
    have hprod :
        (∏ x : Fin k ⊕ Fin m, ∏ i : Fin k ⊕ Fin m,
            if E i < E x ∧ (E.symm.trans e) (E x) < (E.symm.trans e) (E i) then (-1 : ℤˣ) else 1) =
          ∏ x : Fin m, ∏ y : Fin k,
            if e (Sum.inr x) < e (Sum.inl y) then (-1 : ℤˣ) else 1 := by
      simp [Fintype.prod_sum_type, E, hl', hr', h₁, h₂, (h₂ _ _).not_gt, h₃]
    rw [hprod, prod_comm, ← sum_congr rfl fun a _ ↦ hcount a, sum_add_distrib, add_assoc,
      ← two_mul, pow_add, pow_mul]
    simp [prod_ite, prod_pow_eq_pow_sum]

end

/-- Reindexing a signed sum over permutations by `τ ↦ c.permCongr τ * B` contributes the sign of
`B`. -/
theorem sum_sign_smul_permCongr_mul {a b : ℕ} {M : Type*} [AddCommGroup M]
    (c : Fin a ≃ Fin b) (B : Equiv.Perm (Fin b)) (f : Equiv.Perm (Fin b) → M) :
    ∑ τ : Equiv.Perm (Fin a), Equiv.Perm.sign τ • f (c.permCongr τ * B) =
      Equiv.Perm.sign B • ∑ σ : Equiv.Perm (Fin b), Equiv.Perm.sign σ • f σ := by
  first
  | rw [Finset.smul_sum]
    refine Fintype.sum_equiv (c.permCongr.trans (Equiv.mulRight B)) _ _ fun τ => ?_
    have hsign : Equiv.Perm.sign τ =
        Equiv.Perm.sign B * Equiv.Perm.sign (c.permCongr τ * B) := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_permCongr, mul_comm, mul_assoc, ← sq]
      simp [Int.units_sq]
    simp only [Equiv.trans_apply, Equiv.coe_mulRight, hsign, mul_smul]

open Equiv in
/-- Rotating three blocks of indices in a signed sum over permutations: a summand reading its three
arguments off the blocks of sizes `l`, `m` and `k` of `Fin (l + m + k)`, in the order last, first,
second, sums to `(-1) ^ (k * (l + m))` times the same summand reading them off the blocks of sizes
`k`, `l` and `m` of `Fin (k + l + m)` in order. This is the reindexing along the block swap moving
the last `k` indices to the front. -/
theorem sum_sign_smul_rotate_blocks {γ M : Type*} [AddCommGroup M] {k l m : ℕ}
    (g : (Fin k → γ) → (Fin l → γ) → (Fin m → γ) → M) (v : Fin (k + l + m) → γ) :
    ∑ τ : Perm (Fin (l + m + k)), Perm.sign τ •
        g (fun i => v (Fin.cast (show l + m + k = k + l + m by omega)
            (τ (Fin.natAdd (l + m) i))))
          (fun j => v (Fin.cast (show l + m + k = k + l + m by omega)
            (τ (Fin.castAdd k (Fin.castAdd m j)))))
          (fun r => v (Fin.cast (show l + m + k = k + l + m by omega)
            (τ (Fin.castAdd k (Fin.natAdd l r))))) =
      (-1 : ℤˣ) ^ (k * (l + m)) • ∑ σ : Perm (Fin (k + l + m)), Perm.sign σ •
        g (fun i => v (σ (Fin.castAdd m (Fin.castAdd l i))))
          (fun j => v (σ (Fin.castAdd m (Fin.natAdd k j))))
          (fun r => v (σ (Fin.natAdd (k + l) r))) := by
  first
    -- Reindex by `τ ↦ c τ c⁻¹ * B`, where `c` is the cast and `B` moves the last block of `k`
    -- indices to the front; `B` is the block swap of `Fin (k + (l + m))`, of sign
    -- `(-1) ^ (k * (l + m))`, conjugated by the associativity cast.
  | set c : Fin (l + m + k) ≃ Fin (k + l + m) := finCongr (show l + m + k = k + l + m by omega)
    set d : Fin (k + (l + m)) ≃ Fin (k + l + m) := finCongr (Nat.add_assoc k l m).symm
    set B : Perm (Fin (k + l + m)) :=
      d.permCongr (finAddFlip.trans (finCongr (Nat.add_comm (l + m) k)))
    have hB : Perm.sign B = (-1) ^ (k * (l + m)) := by
      rw [Perm.sign_permCongr, sign_finAddFlip_trans_finCongr]
    have h₁ (i : Fin k) : B (Fin.castAdd m (Fin.castAdd l i)) = c (Fin.natAdd (l + m) i) := by
      have : d.symm (Fin.castAdd m (Fin.castAdd l i)) = Fin.castAdd (l + m) i := Fin.ext rfl
      simp only [B, Equiv.permCongr_apply, this, Equiv.trans_apply, finAddFlip_apply_castAdd]
      exact Fin.ext rfl
    have h₂ (j : Fin l) : B (Fin.castAdd m (Fin.natAdd k j)) =
        c (Fin.castAdd k (Fin.castAdd m j)) := by
      have : d.symm (Fin.castAdd m (Fin.natAdd k j)) = Fin.natAdd k (Fin.castAdd m j) := Fin.ext rfl
      simp only [B, Equiv.permCongr_apply, this, Equiv.trans_apply, finAddFlip_apply_natAdd]
      exact Fin.ext rfl
    have h₃ (r : Fin m) : B (Fin.natAdd (k + l) r) = c (Fin.castAdd k (Fin.natAdd l r)) := by
      have : d.symm (Fin.natAdd (k + l) r) = Fin.natAdd k (Fin.natAdd l r) :=
        Fin.ext (Nat.add_assoc k l r)
      simp only [B, Equiv.permCongr_apply, this, Equiv.trans_apply, finAddFlip_apply_natAdd]
      exact Fin.ext rfl
    let f : Perm (Fin (k + l + m)) → M := fun σ =>
      g (fun i => v (σ (Fin.castAdd m (Fin.castAdd l i))))
        (fun j => v (σ (Fin.castAdd m (Fin.natAdd k j))))
        (fun r => v (σ (Fin.natAdd (k + l) r)))
    calc
      _ = ∑ τ : Perm (Fin (l + m + k)), Perm.sign τ • f (c.permCongr τ * B) := by
        apply Finset.sum_congr rfl
        intro τ _
        simp only [f, Perm.mul_apply, h₁, h₂, h₃, Equiv.permCongr_apply,
          Equiv.symm_apply_apply]
        simp only [c, finCongr_apply]
      _ = _ := (sum_sign_smul_permCongr_mul c B f).trans (by rw [hB])

end TauCeti
end -- closes the original EOF section from source line 40
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/GroupTheory/Perm/Inversion.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Principal subresultant coefficients

This file defines the fixed-bound principal subresultant coefficient of two polynomials.  For
`j ≤ min m n`, its matrix is obtained from the Sylvester matrix by deleting the first and last `j`
rows and the last `j` columns from each polynomial block.  Thus the coefficient at index zero is the
resultant, while the terminal coefficient is a power of the coefficient at the smaller bound.

Keeping the bounds explicit is essential for specialization: mapping coefficients commutes with
the construction even when the degrees of the mapped polynomials drop.  These determinants are
the scalar data used by subresultant gcd criteria and projection operators.

## Main results

* `TauCeti.coefficientRow_dotProduct`: a row of shifted polynomial coefficients reads any
  coefficient of `A * q + B * p` from the coefficient vector of `(A, B)`.
* `Polynomial.subresultantMatrix_mulVec`: the matrix acts on a pair of coefficient vectors as
  `(A, B) ↦ A * q + B * p`, its row `i` reading the coefficient of degree `i + j`.
* `Polynomial.psc_zero`: the zeroth principal subresultant coefficient is the resultant.
* `Polynomial.psc_map_map`: fixed-bound principal subresultant coefficients commute with coefficient
  maps.
* `Polynomial.psc_map_of_natDegree_eq`: at the actual degrees, they commute with coefficient maps
  that preserve both degrees.
* `Polynomial.psc_comm`: swapping the polynomials multiplies by `(-1) ^ ((m - j) * (n - j))`.
* `Polynomial.psc_left_bound`, `Polynomial.psc_right_bound`: at a formal degree bound, the
  determinant is a power of the coefficient at that bound.
* `Polynomial.psc_min`: the terminal determinant is a power of the coefficient at the smaller
  degree bound.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4.
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3.
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The square coefficient matrix whose determinant is the principal subresultant coefficient at
index `j` and formal degree bounds `m` and `n`.

Row `i` reads the coefficient of degree `i + j`. The first `m - j` columns read
`q, X*q, ..., X^(m-j-1)*q` and the last `n - j` columns read `p, X*p, ..., X^(n-j-1)*p`, with
`q` and `p` truncated to their formal bounds `n` and `m`; when `q.natDegree ≤ n` and
`p.natDegree ≤ m` the entries are exactly those coefficients
(`Polynomial.subresultantMatrix_apply_eq_coeff`). For `j ≤ min m n`, the case subresultant
applications use, the rows read the degrees `j, ..., m+n-j-1`. -/
def _root_.Polynomial.subresultantMatrix [Semiring R] (p q : R[X]) (m n j : ℕ) :
    Matrix (Fin ((m - j) + (n - j))) (Fin ((m - j) + (n - j))) R :=
  Matrix.of fun i k =>
    k.addCases
      (fun k => if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + n then
        q.coeff (i.val + j - k.val) else 0)
      (fun k => if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + m then
        p.coeff (i.val + j - k.val) else 0)

/-- An entry of a principal subresultant matrix in the first, `q`-column block. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_castAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ)
    (i : Fin ((m - j) + (n - j))) (k : Fin (m - j)) :
    subresultantMatrix p q m n j i (Fin.castAdd (n - j) k) =
      if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + n then
        q.coeff (i.val + j - k.val) else 0 := by
  first
  | simp [subresultantMatrix]

/-- An entry of a principal subresultant matrix in the second, `p`-column block. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_natAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ)
    (i : Fin ((m - j) + (n - j))) (k : Fin (n - j)) :
    subresultantMatrix p q m n j i (Fin.natAdd (m - j) k) =
      if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + m then
        p.coeff (i.val + j - k.val) else 0 := by
  first
  | simp [subresultantMatrix]

/-- When the formal bounds dominate the degrees, subresultant entries are simply
coefficients of the shifted input polynomials. -/
theorem _root_.Polynomial.subresultantMatrix_apply_eq_coeff [Semiring R]
    {p q : R[X]} {m n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j : ℕ)
    (i k : Fin ((m - j) + (n - j))) :
    subresultantMatrix p q m n j i k =
      k.addCases (fun k => (X ^ k.val * q).coeff (i.val + j))
        (fun k => (X ^ k.val * p).coeff (i.val + j)) := by
  first
  | induction k using Fin.addCases <;>
      simp [subresultantMatrix, coeff_X_pow_mul_of_natDegree_le hm,
        coeff_X_pow_mul_of_natDegree_le hn]

/-- At index zero, the principal subresultant matrix is Mathlib's Sylvester matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_zero [Semiring R]
    (p q : R[X]) (m n : ℕ) :
    subresultantMatrix p q m n 0 = p.sylvester q m n := by
  first
  | ext i k
    induction k using Fin.addCases <;> simp [subresultantMatrix, Polynomial.sylvester]

/-- Mapping coefficients maps every entry of the fixed-bound principal subresultant matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_map_map [Semiring R] [Semiring S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    subresultantMatrix (p.map f) (q.map f) m n j =
      f.mapMatrix (subresultantMatrix p q m n j) := by
  first
  | ext i k
    induction k using Fin.addCases <;> simp [subresultantMatrix, apply_ite f]

/-- Swapping the polynomials and their bounds swaps the two column blocks of the principal
subresultant matrix. -/
theorem _root_.Polynomial.subresultantMatrix_comm [Semiring R] (p q : R[X]) (m n j : ℕ) :
    subresultantMatrix p q m n j =
      (subresultantMatrix q p n m j).reindex (finCongr (add_comm (n - j) (m - j))) finAddFlip := by
  first
  | ext i k
    induction k using Fin.addCases <;> simp [subresultantMatrix, finAddFlip]

/-- A row of coefficients of shifted `q` and `p` reads the coefficient of degree `d` of
`A * q + B * p`, where the two blocks of `v` are the coefficients of `A` and `B`.
The row lengths are arbitrary, and the formal bounds dominate the actual input degrees. -/
theorem coefficientRow_dotProduct [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (a b d : ℕ) (v : Fin (a + b) → R) :
    (Fin.addCases
      (fun l : Fin a => if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0)
      (fun l : Fin b => if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0))
      ⬝ᵥ v =
      (ofFn a (fun l => v (Fin.castAdd b l)) * q +
        ofFn b (fun l => v (Fin.natAdd a l)) * p).coeff d := by
  first
  | simp_rw [← coeff_X_pow_mul_of_natDegree_le hn, ← coeff_X_pow_mul_of_natDegree_le hm]
    simp only [dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      ofFn_eq_sum_monomial, Finset.sum_mul, coeff_add, finsetSum_coeff]
    congr 1 <;> refine Finset.sum_congr rfl fun l _ => ?_ <;>
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, mul_comm]

/-- The principal subresultant matrix acts on a vector as the linear map `(A, B) ↦ A * q + B * p`,
where `A` and `B` are the polynomials whose coefficients are the first `m - j` and the last `n - j`
entries of the vector: entry `i` of the result is the coefficient of degree `i + j`.  The formal
bounds must dominate the actual degrees. -/
theorem _root_.Polynomial.subresultantMatrix_mulVec [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j : ℕ)
    (v : Fin ((m - j) + (n - j)) → R) (i : Fin ((m - j) + (n - j))) :
    (subresultantMatrix p q m n j).mulVec v i =
      (ofFn (m - j) (fun k => v (Fin.castAdd (n - j) k)) * q +
        ofFn (n - j) (fun k => v (Fin.natAdd (m - j) k)) * p).coeff (i + j) :=
  coefficientRow_dotProduct hm hn (m - j) (n - j) (i.val + j) v

/-- The principal subresultant coefficient at index `j` and formal degree bounds `m` and `n`.

The bounds are part of the data: they are not recomputed after coefficient specialization. -/
def _root_.Polynomial.psc [CommRing R] (p q : R[X]) (m n j : ℕ) : R :=
  (subresultantMatrix p q m n j).det

/-- The principal subresultant coefficient is the determinant of the principal subresultant
matrix. -/
theorem _root_.Polynomial.psc_def [CommRing R] (p q : R[X]) (m n j : ℕ) :
    psc p q m n j = (subresultantMatrix p q m n j).det := by
  first
  | rw [psc]

/-- The zeroth principal subresultant coefficient is the fixed-bound resultant. -/
@[simp]
theorem _root_.Polynomial.psc_zero [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n 0 = Polynomial.resultant p q m n := by
  first
  | simp [psc_def, Polynomial.resultant]

/-- Principal subresultant coefficients commute with coefficient maps at fixed bounds.  No
degree-preservation hypothesis is needed. -/
@[simp]
theorem _root_.Polynomial.psc_map_map [CommRing R] [CommRing S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    psc (p.map f) (q.map f) m n j = f (psc p q m n j) := by
  first
  | simp [psc_def, RingHom.map_det]

/-- At the actual degrees, principal subresultant coefficients commute with a coefficient map that
preserves both degrees, for instance one that does not kill the leading coefficients
(`Polynomial.natDegree_map_of_leadingCoeff_ne_zero`). When a degree drops, the specialized
coefficients at the smaller actual degrees are given instead by the degree-drop formulas
`Polynomial.map_psc_of_right_degree_drop` and `Polynomial.map_psc_of_left_degree_drop`. -/
theorem _root_.Polynomial.psc_map_of_natDegree_eq [CommRing R] [CommRing S] (f : R →+* S)
    {p q : R[X]} (hp : (p.map f).natDegree = p.natDegree) (hq : (q.map f).natDegree = q.natDegree)
    (j : ℕ) :
    psc (p.map f) (q.map f) (p.map f).natDegree (q.map f).natDegree j =
      f (psc p q p.natDegree q.natDegree j) := by
  first
  | rw [hp, hq, psc_map_map]

/-- Swapping the polynomials and their bounds changes the principal subresultant coefficient by
the sign `(-1) ^ ((m - j) * (n - j))`. -/
theorem _root_.Polynomial.psc_comm [CommRing R] (p q : R[X]) (m n j : ℕ) :
    psc p q m n j = (-1) ^ ((m - j) * (n - j)) * psc q p n m j := by
  first
  | rw [psc_def, psc_def, subresultantMatrix_comm, Matrix.det_reindex, finCongr_symm,
      sign_finAddFlip_trans_finCongr, mul_comm (n - j)]
    simp

/-- At the left formal degree bound, the principal coefficient is the corresponding power of the
left polynomial's coefficient.  This is the terminal coefficient when `m ≤ n`; when `n < m`,
both sides reduce to `1` because the index is beyond the subresultant range. -/
@[simp]
theorem _root_.Polynomial.psc_left_bound [CommRing R]
    (p q : R[X]) (m n : ℕ) :
    psc p q m n m = p.coeff m ^ (n - m) := by
  first
  | let M := subresultantMatrix p q m n m
    have htri : M.IsUpperTriangular := by
      intro i k hki
      induction k using Fin.addCases with
      | left k => exact Fin.elim0 (Fin.cast (by simp) k)
      | right k =>
          have hki' : (k : ℕ) < (i : ℕ) := by
            simpa only [id_eq, Fin.val_natAdd, Nat.sub_self, zero_add] using Fin.lt_def.mp hki
          simp only [M, subresultantMatrix, Matrix.of_apply, Fin.addCases_right]
          split_ifs with h
          · omega
          · rfl
    have hdiag (i : Fin ((m - m) + (n - m))) : M i i = p.coeff m := by
      induction i using Fin.addCases with
      | left i => exact Fin.elim0 (Fin.cast (by simp) i)
      | right i => simp [M, subresultantMatrix]
    rw [psc_def, Matrix.det_of_isUpperTriangular htri]
    simp_rw [hdiag]
    simp

/-- At the right formal degree bound, the principal coefficient is the corresponding power of the
right polynomial's coefficient.  This is the terminal coefficient when `n ≤ m`; when `m < n`,
both sides reduce to `1` because the index is beyond the subresultant range. -/
@[simp]
theorem _root_.Polynomial.psc_right_bound [CommRing R]
    (p q : R[X]) (m n : ℕ) :
    psc p q m n n = q.coeff n ^ (m - n) := by
  first
  | rw [psc_comm, psc_left_bound]
    simp

/-- The principal coefficient at the terminal subresultant index is a power of the coefficient
at the smaller formal degree bound. -/
@[simp]
theorem _root_.Polynomial.psc_min [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n (min m n) =
      if m ≤ n then p.coeff m ^ (n - m) else q.coeff n ^ (m - n) := by
  first
  | by_cases hmn : m ≤ n
    · simp [hmn]
    · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      simp [hmn, hnm]

end TauCeti
end -- closes the original EOF section from source line 50
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Degree/Operations.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Degrees of polynomial sums and products

Mathlib's `Polynomial.degree_mul_le` bounds the degree of a product by the sum of the degrees.
This file records the strict form with one factor of degree below a natural number `a` and the
other of `natDegree` at most `n`: the product has degree below `a + n`.  Stating the bound with
`degree` on the strict side lets the zero polynomial through on either side, which is what a
coefficient window of prescribed length needs when it is read off polynomials that may vanish.

`TauCeti.degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le` combines two such product bounds
into the coefficient window used for polynomial relations with formal degree bounds `m` and `n`.
`Polynomial.natDegree_multiset_prod_X_sub_C_le` bounds the degree of a product of `card s` monic
linear factors by `card s` over any commutative ring, without the nontriviality that Mathlib's
`Polynomial.natDegree_multiset_prod_X_sub_C_eq_card` needs.
`Polynomial.natDegree_X_pow_add_C_mul_X_add_C` reads off the degree of the trinomial
`X ^ n + C a * X + C b` for `2 ≤ n`, and `Polynomial.natDegree_comp_C_mul_X_add_C` shows
that an affine substitution `X ↦ a X + b` with `a ≠ 0` keeps the degree.
`Polynomial.sub_C_ne_zero` records that a nonconstant polynomial differs from every constant
polynomial, and `Polynomial.natDegree_one_sub_C_mul_le` bounds the degree of `1 - C a * p` by that
of `p`; in particular `Polynomial.natDegree_one_sub_C_mul_X_le` shows that `1 - t X` has degree at
most one.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [Semiring R]

/-- The product of a polynomial of degree below `a` with one of degree at most `n` has degree
below `a + n`; the zero polynomial is allowed on either side. -/
theorem _root_.Polynomial.degree_mul_lt_of_degree_lt_of_natDegree_le {A q : R[X]} {a n : ℕ}
    (hA : A.degree < a) (hq : q.natDegree ≤ n) :
    (A * q).degree < ((a + n : ℕ) : WithBot ℕ) := by
  first
  | rcases eq_or_ne q 0 with rfl | hq0
    · simp
    · calc (A * q).degree ≤ A.degree + q.degree := degree_mul_le A q
        _ < (a : WithBot ℕ) + n :=
          WithBot.add_lt_add_of_lt_of_le (degree_ne_bot.mpr hq0) hA (degree_le_of_natDegree_le hq)
        _ = ((a + n : ℕ) : WithBot ℕ) := by push_cast; rfl

/-- A relation with multipliers of degrees below `m - j` and `n - j` has degree below
`(m - j) + (n - j) + j`, provided the input degrees are bounded by `m` and `n` and `j` lies
below both bounds. Either input or multiplier may be zero. -/
theorem degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le {p q A B : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n)
    (hA : A.degree < (m - j : ℕ)) (hB : B.degree < (n - j : ℕ)) :
    (A * q + B * p).degree < (((m - j) + (n - j) + j : ℕ) : WithBot ℕ) := by
  first
  | apply (degree_add_le _ _).trans_lt
    apply max_lt
    · exact (degree_mul_lt_of_degree_lt_of_natDegree_le hA hn).trans_le
        (WithBot.coe_le_coe.mpr (by omega : m - j + n ≤ (m - j) + (n - j) + j))
    · exact (degree_mul_lt_of_degree_lt_of_natDegree_le hB hm).trans_le
        (WithBot.coe_le_coe.mpr (by omega : n - j + m ≤ (m - j) + (n - j) + j))

/-- A product of `card s` monic linear factors has degree at most `card s`; unlike
`natDegree_multiset_prod_X_sub_C_eq_card`, this needs no nontriviality. -/
theorem _root_.Polynomial.natDegree_multiset_prod_X_sub_C_le {S : Type*} [CommRing S]
    (s : Multiset S) : (s.map fun a ↦ X - C a).prod.natDegree ≤ Multiset.card s := by
  first
  | induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
      exact natDegree_mul_le.trans (add_le_add (natDegree_X_sub_C_le a) ih)

/-- A nonconstant polynomial differs from every constant polynomial. -/
theorem _root_.Polynomial.sub_C_ne_zero {S : Type*} [Ring S] {p : S[X]} (hp : 0 < p.natDegree)
    (a : S) : p - C a ≠ 0 :=
  ne_zero_of_natDegree_gt (n := 0) (by rwa [natDegree_sub_C])

/-- Subtracting a constant multiple of `p` from one gives degree at most that of `p`. -/
theorem _root_.Polynomial.natDegree_one_sub_C_mul_le {S : Type*} [Ring S] (a : S) (p : S[X]) :
    (1 - C a * p).natDegree ≤ p.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))

/-- The linear polynomial `1 - t X` has degree at most one. -/
theorem _root_.Polynomial.natDegree_one_sub_C_mul_X_le {S : Type*} [Ring S] (t : S) :
    (1 - C t * X).natDegree ≤ 1 :=
  (natDegree_one_sub_C_mul_le t X).trans natDegree_X_le

/-- For `2 ≤ n`, the trinomial `X ^ n + C a * X + C b` has degree `n`. -/
theorem _root_.Polynomial.natDegree_X_pow_add_C_mul_X_add_C [Nontrivial R] (a b : R) {n : ℕ}
    (hn : 2 ≤ n) : (X ^ n + C a * X + C b).natDegree = n := by
  first
  | rw [add_assoc, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact degree_linear_le.trans_lt (by exact_mod_cast (by omega : 1 < n))

/-- An affine substitution `X ↦ a X + b` with `a ≠ 0` keeps the degree. -/
@[simp]
theorem _root_.Polynomial.natDegree_comp_C_mul_X_add_C [NoZeroDivisors R] {a : R} (ha : a ≠ 0)
    (b : R) (p : R[X]) : (p.comp (C a * X + C b)).natDegree = p.natDegree := by
  first
  | rw [natDegree_comp, natDegree_linear ha, mul_one]

end TauCeti
end -- closes the original EOF section from source line 36
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Degree/Operations.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/FieldDivision.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Linear relations between polynomials over a field

A relation `A * q + B * p = 0` between polynomials over a field says that `A * q` is divisible by
`p`; dividing by the gcd of `p` and `q` leaves coprime quotients, so in fact `p / gcd p q` divides
`A`.  So a nonzero `A` in such a relation has degree at least `deg p - deg (gcd p q)`: this is the
degree bound behind the nonvanishing of the principal subresultant coefficient at the degree of
the gcd.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- In a relation `A * q + B * p = 0` with `p ≠ 0`, if `A` has degree below
`deg p - deg (gcd p q)`, then `A = 0`: dividing by the gcd leaves coprime quotients, so
`p / gcd p q` divides `A`. -/
theorem _root_.Polynomial.eq_zero_of_mul_add_mul_eq_zero_of_degree_lt {p q A B : K[X]}
    (hp : p ≠ 0) (hAB : A * q + B * p = 0)
    (hA : A.degree < ((p.natDegree - (EuclideanDomain.gcd p q).natDegree : ℕ) : WithBot ℕ)) :
    A = 0 := by
  first
  | set g := EuclideanDomain.gcd p q
    have hg0 : g ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
    have hp' : g * (p / g) = p :=
      EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_left p q)
    have hq' : g * (q / g) = q :=
      EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_right p q)
    -- Mathlib states the coprimality of the gcd quotients for `GCDMonoid.gcd`; the `GCDMonoid`
    -- structure `EuclideanDomain.gcdMonoid` has `GCDMonoid.gcd = EuclideanDomain.gcd` by definition.
    have hcop : IsCoprime (p / g) (q / g) :=
      letI := EuclideanDomain.gcdMonoid K[X]
      isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
    have hrel : A * (q / g) + B * (p / g) = 0 := by
      refine mul_left_cancel₀ hg0 ?_
      calc g * (A * (q / g) + B * (p / g)) = A * (g * (q / g)) + B * (g * (p / g)) := by ring
        _ = A * q + B * p := by rw [hp', hq']
        _ = g * 0 := by rw [hAB, mul_zero]
    have hpA : p / g ∣ A := hcop.dvd_of_dvd_mul_right ⟨-B, by linear_combination hrel⟩
    have hp'0 : p / g ≠ 0 := by
      intro h
      rw [h, mul_zero] at hp'
      exact hp hp'.symm
    refine eq_zero_of_dvd_of_degree_lt hpA (hA.trans_le ?_)
    rw [degree_eq_natDegree hp'0]
    have := natDegree_mul hg0 hp'0
    rw [hp'] at this
    exact WithBot.coe_le_coe.mpr (by omega : p.natDegree - g.natDegree ≤ (p / g).natDegree)

end TauCeti
end -- closes the original EOF section from source line 21
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/FieldDivision.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/OfFn.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


-- Proof-only: supply `Polynomial.X_sub_C_pow_dvd_iff` and `Polynomial.X_pow_dvd_iff`.

/-!
# Recovering a polynomial of bounded degree from its coefficient vector

`Polynomial.ofFn n` and `Polynomial.toFn n` pass between vectors of length `n` and polynomials.
Mathlib records that a polynomial of `natDegree` below `n` is recovered from its first `n`
coefficients; this file states the same recovery in terms of `degree`, so that it also applies
to the zero polynomial. This file also records evaluation of the coefficient vector and
reconstruction of a coordinate vector as a power of `X`, and characterizes divisibility of
`ofFn n f` by `(X - t) ^ r` through the Taylor coefficients of order `< r` at `t`.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
/-- Evaluating the coefficient vector reads the corresponding polynomial coefficient. -/
@[simp]
theorem _root_.Polynomial.toFn_apply (n : ℕ) (p : R[X]) (i : Fin n) :
    toFn n p i = p.coeff i := (rfl)

-- Mathlib's `ofFn` takes `[DecidableEq R]`, so this instance occurs in the statement.
/-- The coordinate vector with value one at `l` reconstructs the monomial `X ^ l.val`. -/
@[simp]
theorem _root_.Polynomial.ofFn_single {n : ℕ} (l : Fin n) :
    ofFn n (fun i => if i = l then (1 : R) else 0) = X ^ l.val := by
  first
  | simp [ofFn_eq_sum_monomial, apply_ite (monomial _), monomial_one_right_eq_X_pow]

/-- A polynomial of degree below `n` is recovered from its vector of first `n` coefficients.
This is the `degree` form of `Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt`, which also covers
the zero polynomial. -/
theorem _root_.Polynomial.ofFn_comp_toFn_eq_id_of_degree_lt {n : ℕ} {p : R[X]} (h : p.degree < n) :
    ofFn n (toFn n p) = p := by
  first
  | rcases eq_or_ne p 0 with rfl | hp
    · simp
    · exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt hp).mpr h)

/-- `(X - t) ^ r` divides the polynomial with coefficient vector `f` if and only if its Taylor
coefficients of order `< r` at `t` vanish. -/
theorem _root_.Polynomial.X_sub_C_pow_dvd_ofFn_iff {R : Type*} [CommRing R] [DecidableEq R]
    (t : R) (r : ℕ) {n : ℕ} (f : Fin n → R) :
    (X - C t) ^ r ∣ ofFn n f ↔
      ∀ k < r, ∑ i : Fin n, f i * (t ^ ((i : ℕ) - k) * ((i : ℕ).choose k : R)) = 0 := by
  first
  | rw [ofFn_eq_sum_monomial, X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
    refine forall₂_congr fun k _ ↦ ?_
    simp [← C_mul_X_pow_eq_monomial, finsetSum_coeff, coeff_X_add_C_pow]

end TauCeti
end -- closes the original EOF section from source line 25
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/OfFn.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/GCD.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The subresultant gcd criterion

Over a field, the principal subresultant coefficients of two polynomials locate the degree of
their greatest common divisor: taken at the actual degree of the nonzero left polynomial and at
any bound dominating the degree of the right one, they vanish at every index below the degree
of the gcd and are nonzero at that degree.  Hence, at the actual degrees of any two polynomials,
the degree of the gcd is the least index with a nonzero principal subresultant coefficient.

Both halves read the principal subresultant matrix as the linear map `(A, B) ↦ A * q + B * p` on
polynomials of bounded degree, through `Polynomial.subresultantMatrix_mulVec`.  A common factor
of degree `d > j` supplies the kernel vector `(p / g, -(q / g))` at index `j`; at index `d`, a
kernel vector is a relation `A * q + B * p = 0` whose degrees are too small for a nonzero
solution, by the Bézout identity for the gcd.

## Main results

* `Polynomial.psc_eq_zero_of_mul_add_mul_eq_zero`: a nontrivial relation `A * q + B * p = 0` with
  `A` and `B` of degrees below `m - j` and `n - j` forces the principal coefficient at `j` to
  vanish.
* `Polynomial.psc_eq_zero_of_lt_natDegree_gcd`: the principal coefficients vanish below the
  degree of the gcd.
* `Polynomial.psc_natDegree_gcd_ne_zero`: the principal coefficient at the degree of the gcd is
  nonzero.
* `Polynomial.natDegree_gcd_eq_iff_psc`: the degree of the gcd is the least index with a nonzero
  principal subresultant coefficient.
* `Polynomial.natDegree_gcd_eq_of_psc_eq_zero_iff`: two pairs of polynomials whose principal
  subresultant coefficients vanish at the same indices have gcds of the same degree.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4, Proposition 4.25 and Corollary 4.26.
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3.
-/

public section

namespace TauCeti

open Polynomial

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nontrivial relation `A * q + B * p = 0`, with `A` and `B` of degrees below `m - j` and
`n - j`, is a kernel vector of the principal subresultant matrix at index `j`, so the principal
subresultant coefficient vanishes there. -/
theorem _root_.Polynomial.psc_eq_zero_of_mul_add_mul_eq_zero {p q A B : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hA : A.degree < (m - j : ℕ)) (hB : B.degree < (n - j : ℕ))
    (hAB : A * q + B * p = 0) (hne : A ≠ 0 ∨ B ≠ 0) :
    psc p q m n j = 0 := by
  first
  | classical
    rw [psc_def, ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨Fin.append (toFn (m - j) A) (toFn (n - j) B), fun h0 => ?_, ?_⟩
    · have hA0 : toFn (m - j) A = 0 := funext fun k => by
        simpa using congrFun h0 (Fin.castAdd (n - j) k)
      have hB0 : toFn (n - j) B = 0 := funext fun k => by
        simpa using congrFun h0 (Fin.natAdd (m - j) k)
      rcases hne with hne | hne
      · exact hne (by rw [← ofFn_comp_toFn_eq_id_of_degree_lt hA, hA0, map_zero])
      · exact hne (by rw [← ofFn_comp_toFn_eq_id_of_degree_lt hB, hB0, map_zero])
    · funext i
      rw [subresultantMatrix_mulVec hm hn]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
      rw [ofFn_comp_toFn_eq_id_of_degree_lt hA, ofFn_comp_toFn_eq_id_of_degree_lt hB, hAB, coeff_zero]

end Domain

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- Below the degree of the gcd, the principal subresultant coefficients vanish, at any formal
degree bounds dominating the actual degrees. -/
theorem _root_.Polynomial.psc_eq_zero_of_lt_natDegree_gcd {p q : K[X]}
    {m n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hj : j < (EuclideanDomain.gcd p q).natDegree) : psc p q m n j = 0 := by
  first
  | set g := EuclideanDomain.gcd p q
    have hg0 : g ≠ 0 := by
      rintro h
      rw [h, natDegree_zero] at hj
      exact absurd hj (Nat.not_lt_zero j)
    have hpg : g * (p / g) = p :=
      EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_left p q)
    have hqg : g * (q / g) = q :=
      EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_right p q)
    -- The degree of a quotient by `g` drops by `g.natDegree`, so both quotients fit the bounds.
    have hdeg : ∀ {r : K[X]} {k : ℕ}, r.natDegree ≤ k → g * (r / g) = r →
        (r / g).degree < (k - j : ℕ) := by
      intro r k hk hrg
      rcases eq_or_ne r 0 with rfl | hr
      · rw [EuclideanDomain.zero_div, degree_zero]
        exact WithBot.bot_lt_coe _
      · have hrg0 : r / g ≠ 0 := by
          rintro h
          rw [h, mul_zero] at hrg
          exact hr hrg.symm
        have := natDegree_mul hg0 hrg0
        rw [hrg] at this
        exact (natDegree_lt_iff_degree_lt hrg0).mp (by omega)
    refine psc_eq_zero_of_mul_add_mul_eq_zero (A := p / g) (B := -(q / g)) hm hn (hdeg hm hpg)
      (by rw [degree_neg]; exact hdeg hn hqg) ?_ ?_
    · rw [neg_mul, ← sub_eq_add_neg, sub_eq_zero]
      calc p / g * q = p / g * (g * (q / g)) := by rw [hqg]
        _ = q / g * (g * (p / g)) := by ring
        _ = q / g * p := by rw [hpg]
    · rcases eq_or_ne p 0 with rfl | hp
      · have hq : q ≠ 0 := fun h => hg0 (EuclideanDomain.gcd_eq_zero_iff.mpr ⟨rfl, h⟩)
        refine Or.inr (neg_ne_zero.mpr fun h => hq ?_)
        rw [h, mul_zero] at hqg
        exact hqg.symm
      · refine Or.inl fun h => hp ?_
        rw [h, mul_zero] at hpg
        exact hpg.symm

/-- At the degree of the gcd, the principal subresultant coefficient is nonzero, provided the left
bound is the actual degree of the nonzero left polynomial and the right bound dominates the degree
of the right polynomial. -/
theorem _root_.Polynomial.psc_natDegree_gcd_ne_zero {p q : K[X]} {m n : ℕ}
    (hp : p ≠ 0) (hm : p.natDegree = m) (hn : q.natDegree ≤ n) :
    psc p q m n (EuclideanDomain.gcd p q).natDegree ≠ 0 := by
  first
  | set g := EuclideanDomain.gcd p q with hg
    clear_value g
    set d := g.natDegree with hd
    clear_value d
    have hgp : g ∣ p := hg ▸ EuclideanDomain.gcd_dvd_left p q
    have hgq : g ∣ q := hg ▸ EuclideanDomain.gcd_dvd_right p q
    have hg0 : g ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp (hg ▸ h)).1
    have hdm : d ≤ m := hd ▸ hm ▸ natDegree_le_of_dvd hgp hp
    rw [psc_def, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv, hMv⟩
    -- The kernel vector encodes a relation `A * q + B * p` with no coefficients in degrees
    -- `d, …, m + n - d - 1` and degree below `m + n - d`, hence of degree below `d = deg g`.
    have hwin (i : Fin ((m - d) + (n - d))) :
        (ofFn (m - d) (fun k => v (Fin.castAdd (n - d) k)) * q +
          ofFn (n - d) (fun k => v (Fin.natAdd (m - d) k)) * p).coeff (i + d) = 0 := by
      rw [← subresultantMatrix_mulVec hm.le hn, hMv, Pi.zero_apply]
    generalize hA : ofFn (m - d) (fun k => v (Fin.castAdd (n - d) k)) = A at hwin
    generalize hB : ofFn (n - d) (fun k => v (Fin.natAdd (m - d) k)) = B at hwin
    have hAdeg : A.degree < (m - d : ℕ) := hA ▸ ofFn_degree_lt _
    have hBdeg : B.degree < (n - d : ℕ) := hB ▸ ofFn_degree_lt _
    have hsumdeg : (A * q + B * p).degree < ((m - d) + (n - d) + d : ℕ) := by
      rcases eq_or_ne q 0 with rfl | hq0
      · rw [mul_zero, zero_add]
        exact (degree_mul_lt_of_degree_lt_of_natDegree_le hBdeg hm.le).trans_le
          (WithBot.coe_le_coe.mpr (by omega : n - d + m ≤ m - d + (n - d) + d))
      · exact degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le hm.le hn hdm
          (hd ▸ (natDegree_le_of_dvd hgq hq0).trans hn) hAdeg hBdeg
    have hdeg : (A * q + B * p).degree < d := by
      rw [degree_lt_iff_coeff_zero]
      intro e he
      by_cases hlt : e < (m - d) + (n - d) + d
      · have := hwin ⟨e - d, by omega⟩
        rwa [Nat.sub_add_cancel he] at this
      · apply coeff_eq_zero_of_degree_lt
        exact hsumdeg.trans_le (WithBot.coe_le_coe.mpr
          (by omega : (m - d) + (n - d) + d ≤ e))
    have hzero : A * q + B * p = 0 :=
      eq_zero_of_dvd_of_degree_lt (dvd_add (dvd_mul_of_dvd_right hgq _) (dvd_mul_of_dvd_right hgp _))
        (by rw [degree_eq_natDegree hg0, ← hd]; exact hdeg)
    -- Divide the relation by `g` and use Bézout to see that `A = 0`, then `B = 0`.
    have hA0 : A = 0 :=
      eq_zero_of_mul_add_mul_eq_zero_of_degree_lt hp hzero (by rw [hm, ← hg, ← hd]; exact hAdeg)
    have hB0 : B = 0 := by
      rw [hA0, zero_mul, zero_add] at hzero
      exact (mul_eq_zero.mp hzero).resolve_right hp
    -- Both coefficient blocks of `v` vanish.
    apply hv
    rw [hA0] at hA
    rw [hB0] at hB
    have h1 := injective_ofFn (m - d) (hA.trans (map_zero _).symm)
    have h2 := injective_ofFn (n - d) (hB.trans (map_zero _).symm)
    funext i
    induction i using Fin.addCases with
    | left k => exact congrFun h1 k
    | right k => exact congrFun h2 k

/-- The subresultant gcd criterion: at the actual degrees, the degree of the gcd of `p` and `q`
is the least index with nonzero principal subresultant coefficient.  When `p = 0`, the gcd is `q`
and the criterion reads off the empty terminal determinant at `q.natDegree`. -/
theorem _root_.Polynomial.natDegree_gcd_eq_iff_psc (p q : K[X]) (j : ℕ) :
    (EuclideanDomain.gcd p q).natDegree = j ↔
      psc p q p.natDegree q.natDegree j ≠ 0 ∧
        ∀ i < j, psc p q p.natDegree q.natDegree i = 0 := by
  first
  | have hne : psc p q p.natDegree q.natDegree (EuclideanDomain.gcd p q).natDegree ≠ 0 := by
      rcases eq_or_ne p 0 with rfl | hp
      · rw [EuclideanDomain.gcd_zero_left, natDegree_zero, psc_right_bound, Nat.zero_sub, pow_zero]
        exact one_ne_zero
      · exact psc_natDegree_gcd_ne_zero hp rfl le_rfl
    constructor
    · rintro rfl
      exact ⟨hne, fun i hi => psc_eq_zero_of_lt_natDegree_gcd le_rfl le_rfl hi⟩
    · rintro ⟨hj, hlt⟩
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with h | h
      · exact hne (hlt _ h)
      · exact hj (psc_eq_zero_of_lt_natDegree_gcd le_rfl le_rfl h)

/-- The degree of the gcd is determined by which principal subresultant coefficients vanish, at
the actual degrees and at indices up to the smaller degree. If the coefficients of a pair `p', q'`
of nonzero polynomials vanish exactly where those of `p, q` do, the two gcds have the same degree;
the two pairs may live over different fields. -/
theorem _root_.Polynomial.natDegree_gcd_eq_of_psc_eq_zero_iff {L : Type*} [Field L]
    [DecidableEq L] {p q : K[X]} {p' q' : L[X]} (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (h : ∀ j ≤ min p'.natDegree q'.natDegree,
      psc p q p.natDegree q.natDegree j = 0 ↔ psc p' q' p'.natDegree q'.natDegree j = 0) :
    (EuclideanDomain.gcd p q).natDegree = (EuclideanDomain.gcd p' q').natDegree := by
  first
  | set d := (EuclideanDomain.gcd p' q').natDegree
    have hd : d ≤ min p'.natDegree q'.natDegree :=
      le_min (natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left p' q') hp')
        (natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right p' q') hq')
    obtain ⟨hne, hlt⟩ := (natDegree_gcd_eq_iff_psc p' q' d).1 rfl
    exact (natDegree_gcd_eq_iff_psc p q d).2
      ⟨fun h0 => hne ((h d hd).1 h0), fun i hi => (h i (hi.le.trans hd)).2 (hlt i hi)⟩

end Field

end TauCeti
end -- closes the original EOF section from source line 51
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/GCD.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Degree/Map.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Degrees of a polynomial under two coefficient maps

If two ring homomorphisms `φ` and `ψ` send exactly the same coefficients of a polynomial `p` to
zero, then `p.map φ` vanishes exactly when `p.map ψ` does, and the two have the same degree. This
is how the zero pattern of finitely many coefficients fixes the degrees of specialized
polynomials, for instance at two points of a base set on which a projection set used in
cylindrical algebraic decomposition is sign-invariant.
-/

public section

namespace Polynomial

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T] {φ : R →+* S} {ψ : R →+* T}
  {p : R[X]}

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` and `p.map ψ` have
the same degree. Only the coefficients up to `p.natDegree` need to be checked. -/
theorem degree_map_eq_of_map_coeff_eq_zero_iff
    (h : ∀ i ≤ p.natDegree, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) :
    (p.map φ).degree = (p.map ψ).degree := by
  first
  | have h' (i : ℕ) : φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0 := by
      rcases le_or_gt i p.natDegree with hi | hi
      · exact h i hi
      · simp [coeff_eq_zero_of_natDegree_lt hi]
    have key (n : WithBot ℕ) : (p.map φ).degree ≤ n ↔ (p.map ψ).degree ≤ n := by
      simp only [degree_le_iff_coeff_zero, coeff_map, h']
    exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` vanishes exactly
when `p.map ψ` does. Only the coefficients up to `p.natDegree` need to be checked. -/
theorem map_eq_zero_iff_of_map_coeff_eq_zero_iff
    (h : ∀ i ≤ p.natDegree, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) :
    p.map φ = 0 ↔ p.map ψ = 0 := by
  first
  | rw [← degree_eq_bot, ← degree_eq_bot, degree_map_eq_of_map_coeff_eq_zero_iff h]

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` and `p.map ψ` have
the same `natDegree`. Only the coefficients up to `p.natDegree` need to be checked. -/
theorem natDegree_map_eq_of_map_coeff_eq_zero_iff
    (h : ∀ i ≤ p.natDegree, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) :
    (p.map φ).natDegree = (p.map ψ).natDegree :=
  natDegree_eq_of_degree_eq (degree_map_eq_of_map_coeff_eq_zero_iff h)

end Polynomial
end -- closes the original EOF section from source line 20
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Degree/Map.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Derivative.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Polynomial derivatives

This file records auxiliary results relating Mathlib's polynomial derivative APIs, computing
iterated derivatives after a linear change of variables, and controlling degrees of derivatives
under coefficient maps.
The roots of all nonzero iterated derivatives of a polynomial form a finite set.

The derivation `Polynomial.derivative'` has `Polynomial.derivative` as its underlying function,
and every scalar multiple of it is locally nilpotent.

For a polynomial `p` with coefficients in an `R`-algebra `S`, possibly noncommutative, evaluating
`p′` at the central element `algebraMap R S t` expands as a sum of the coefficients of `p`
weighted by scalars depending on `t`.

A coefficient map can lower the degree of a polynomial, and in positive characteristic it can
lower the degree of a derivative even when it preserves the degree of the polynomial itself.
Over an additively torsion-free target the second phenomenon cannot occur: preserving the degree
of `p` preserves the degree of `p.derivative`.

A self-reciprocal polynomial `p` of even degree bound `2 g`, one with `X ^ (2 g) p (1 / X) = p (X)`,
satisfies `p' (1) = g p (1)`: the coefficients in degrees `i` and `2 g - i` agree and their
weights `i - g` and `g - i` cancel. The characteristic polynomial of a symplectic matrix is the
basic example.

For `δ ≠ 0` over a semiring without zero divisors, the operator `q ↦ q' + δ q` and all of its
iterates preserve the degree of a polynomial and have trivial kernel.
-/

public section

namespace Polynomial

open Set

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The roots of the nonzero derivatives of `p`, of every order, form a finite set. -/
theorem finite_setOfPred_isRoot_iterate_derivative (p : R[X]) :
    {z | ∃ k, derivative^[k] p ≠ 0 ∧ (derivative^[k] p).IsRoot z}.Finite := by
  first
  | have hk : {k | derivative^[k] p ≠ 0}.Finite := (finite_Iic p.natDegree).subset
      fun k hk ↦ not_lt.1 fun h ↦ hk (iterate_derivative_eq_zero h)
    exact (hk.biUnion fun k hk ↦ finite_setOfPred_isRoot hk).subset
      fun z ⟨k, hk, hz⟩ ↦ mem_biUnion hk hz

end Polynomial

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The derivation `derivative'` has the ordinary polynomial derivative as its underlying
function. -/
theorem _root_.Polynomial.coe_derivative' [CommSemiring R] :
    ⇑(derivative' : Derivation R R[X] R[X]) = derivative :=
  _root_.funext derivative'_apply

/-- The scaled derivative `r • d / dX` is locally nilpotent: some iterate of it kills each
polynomial. -/
theorem _root_.Polynomial.exists_iterate_smul_derivative'_apply_eq_zero [CommSemiring R] (r : R)
    (p : R[X]) : ∃ n, (r • derivative' : Derivation R R[X] R[X])^[n] p = 0 := by
  first
  | refine ⟨p.natDegree + 1, ?_⟩
    rw [← Derivation.coeFn_coe, ← Module.End.coe_pow, Derivation.coe_smul_linearMap, smul_pow,
      LinearMap.smul_apply, Module.End.pow_apply, Derivation.coeFn_coe, coe_derivative',
      iterate_derivative_eq_zero (Nat.lt_succ_self _), smul_zero]

/-- The `k`-th derivative of `p (a X + b)` is `a ^ k p⁽ᵏ⁾ (a X + b)`. -/
theorem _root_.Polynomial.iterate_derivative_comp_C_mul_X_add_C [CommSemiring R] (p : R[X])
    (a b : R) (k : ℕ) :
    derivative^[k] (p.comp (C a * X + C b)) =
      C (a ^ k) * (derivative^[k] p).comp (C a * X + C b) := by
  first
  | induction k with
    | zero => simp
    | succ k ih =>
      simp [Function.iterate_succ_apply', ih, derivative_comp, derivative_pow, pow_succ, C_mul]
      ring

/-- The `k`-th derivative of `p (a X)` is `a ^ k p⁽ᵏ⁾ (a X)`. -/
theorem _root_.Polynomial.iterate_derivative_comp_C_mul_X [CommSemiring R] (p : R[X]) (a : R)
    (k : ℕ) :
    derivative^[k] (p.comp (C a * X)) = C (a ^ k) * (derivative^[k] p).comp (C a * X) := by
  first
  | simpa using p.iterate_derivative_comp_C_mul_X_add_C a 0 k

/-- **Reciprocal-polynomial identity.** A polynomial `p` of degree at most `2 g` which is its own
reflection at `2 g`, that is `X ^ (2 g) p (1 / X) = p (X)`, satisfies `p' (1) = g p (1)`. -/
theorem _root_.Polynomial.derivative_eval_one_of_reflect_eq [CommRing R] {p : R[X]} {g : ℕ}
    (hp : p.natDegree ≤ 2 * g) (h : p.reflect (2 * g) = p) :
    p.derivative.eval 1 = g * p.eval 1 := by
  first
  | have hlt : p.natDegree < 2 * g + 1 := Nat.lt_succ_of_le hp
    rw [derivative_eval, sum_over_range' _ (fun _ ↦ by simp) _ hlt, eval_eq_sum_range' hlt,
      Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    -- The terms in degrees `i` and `2 g - i` cancel, and the term in degree `g` vanishes.
    refine Finset.sum_involution (fun i _ ↦ 2 * g - i) (fun i hi ↦ ?_) (fun i hi hne ↦ ?_)
      (fun i hi ↦ ?_) (fun i hi ↦ ?_) <;>
      have hi : i ≤ 2 * g := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    · have hc : p.coeff (2 * g - i) = p.coeff i := by
        conv_rhs => rw [← h]
        rw [coeff_reflect, revAt_le hi]
      rw [hc, Nat.cast_sub hi]
      push_cast
      ring
    · intro heq
      obtain rfl : i = g := by omega
      simp [mul_comm] at hne
    · simp only [Finset.mem_range]
      omega
    · omega

section AlgebraMap

variable [CommSemiring R] [Semiring S] [Algebra R S]

/-- Evaluating the derivative of a polynomial at the image of a scalar `t`, with the same range of
coefficients as `Polynomial.eval_algebraMap_eq_sum_range`. -/
theorem _root_.Polynomial.derivative_eval_algebraMap_eq_sum_range (p : S[X]) (t : R) :
    p.derivative.eval (algebraMap R S t) =
      ∑ i ∈ Finset.range (p.natDegree + 1), ((i : R) * t ^ (i - 1)) • p.coeff i := by
  first
  | rw [derivative_eval, sum_over_range _ fun n ↦ by simp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, Algebra.commutes]
    simp [mul_assoc]

end AlgebraMap

variable [Semiring R] [Semiring S] [HasUniqueDiv S]

/-- A coefficient map into an additively torsion-free semiring which preserves the degree of a
polynomial also preserves the degree of its derivative. -/
theorem _root_.Polynomial.natDegree_map_derivative_eq_of_natDegree_map_eq {f : R →+* S}
    {p : R[X]} (h : (p.map f).natDegree = p.natDegree) :
    (p.derivative.map f).natDegree = p.derivative.natDegree := by
  first
  | refine Nat.le_antisymm natDegree_map_le ?_
    rw [← derivative_map, natDegree_derivative (p.map f), h]
    exact natDegree_derivative_le p

section ShiftedDerivative

variable [NoZeroDivisors R] {δ : R} {q : R[X]}

/-- For `δ ≠ 0`, the coefficient of `X ^ deg q` in `q' + δ q` is `δ` times the leading coefficient
of `q`, so this polynomial is nonzero when `q` is. -/
private theorem coeff_natDegree_derivative_add_C_mul_ne_zero (hδ : δ ≠ 0) (hq : q ≠ 0) :
    (derivative q + C δ * q).coeff q.natDegree ≠ 0 := by
  first
  | rw [coeff_add, coeff_derivative, coeff_natDegree_succ_eq_zero, zero_mul, zero_add, coeff_C_mul]
    exact mul_ne_zero hδ (leadingCoeff_ne_zero.2 hq)

/-- For `δ ≠ 0`, the operator `q ↦ q' + δ q` (the derivative of `x ↦ q(x) e^(δ x)`, divided by
`e^(δ x)`) preserves the degree of a polynomial. -/
@[simp]
theorem _root_.Polynomial.natDegree_derivative_add_C_mul (hδ : δ ≠ 0) :
    (derivative q + C δ * q).natDegree = q.natDegree := by
  first
  | rcases eq_or_ne q 0 with rfl | hq
    · simp
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_
      (coeff_natDegree_derivative_add_C_mul_ne_zero hδ hq)
    exact natDegree_add_le_of_degree_le (natDegree_derivative_le q |>.trans (Nat.sub_le _ _))
      (natDegree_C_mul_le δ q)

/-- For `δ ≠ 0`, the operator `q ↦ q' + δ q` has trivial kernel. -/
@[simp]
theorem _root_.Polynomial.derivative_add_C_mul_eq_zero_iff (hδ : δ ≠ 0) :
    derivative q + C δ * q = 0 ↔ q = 0 := by
  first
  | refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    by_contra hq
    exact coeff_natDegree_derivative_add_C_mul_ne_zero hδ hq (by rw [h, coeff_zero])

/-- For `δ ≠ 0`, every iterate of the operator `q ↦ q' + δ q` preserves the degree of a
polynomial. -/
@[simp]
theorem _root_.Polynomial.natDegree_iterate_derivative_add_C_mul (hδ : δ ≠ 0) (n : ℕ) :
    ((fun r ↦ derivative r + C δ * r)^[n] q).natDegree = q.natDegree := by
  first
  | induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', natDegree_derivative_add_C_mul hδ, ih]

/-- For `δ ≠ 0`, every iterate of the operator `q ↦ q' + δ q` has trivial kernel. -/
@[simp]
theorem _root_.Polynomial.iterate_derivative_add_C_mul_eq_zero_iff (hδ : δ ≠ 0) (n : ℕ) :
    (fun r ↦ derivative r + C δ * r)^[n] q = 0 ↔ q = 0 := by
  first
  | induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', derivative_add_C_mul_eq_zero_iff hδ, ih]

end ShiftedDerivative

end TauCeti
end -- closes the original EOF section from source line 42
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Derivative.lean -/

/- BEGIN SOURCE: TauCeti/Data/Multiset/Rel.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Lifted relations between multisets as parallel enumerations

Mathlib's `Multiset.Rel r s t` lifts a relation `r` to multisets: it holds when the elements of
`s` and `t` can be paired off one-to-one with each pair related by `r`. This file records the
corresponding statement in terms of enumerations: `Multiset.Rel r s t` holds exactly when `s` and
`t` are enumerated by one family indexed by `Fin n`, with entries of equal index related.

This is the form in which a matching of two multisets of roots is usually produced, by
enumerating the roots of two polynomials in parallel. When each element of `t` is related to at
most one element of `s`, the file also characterizes `Multiset.Rel r s t` by counting, for each
element of `s`, the elements of `t` related to it.
-/

public section

namespace Multiset

variable {α β : Type*} {r : α → β → Prop}

/-- Two multisets are related by `Multiset.Rel r` exactly when they can be enumerated in
parallel, by families indexed by the same `Fin n`, with entries of equal index related by `r`. -/
theorem rel_iff_exists_fin {s : Multiset α} {t : Multiset β} :
    Rel r s t ↔ ∃ (n : ℕ) (a : Fin n → α) (b : Fin n → β),
      s = Finset.univ.val.map a ∧ t = Finset.univ.val.map b ∧ ∀ i, r (a i) (b i) := by
  first
  | refine ⟨fun h => ?_, fun ⟨n, a, b, hs, ht, hab⟩ => ?_⟩
    · induction h with
      | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp, by simp, fun i => i.elim0⟩
      | @cons x y _ _ hxy _ ih =>
        obtain ⟨n, a, b, rfl, rfl, hab⟩ := ih
        exact ⟨n + 1, Fin.cons x a, Fin.cons y b, by simp [List.ofFn_succ],
          by simp [List.ofFn_succ], Fin.cases hxy hab⟩
    · subst hs ht
      exact rel_map.2 (rel_refl_of_refl_on fun i _ => hab i)

/-- **Matching versus counting.** Suppose each element of `t` is related by `r` to at most one
element of `s`. Then `s` and `t` are related by `Multiset.Rel r` exactly when each `a ∈ s` is
related to as many elements of `t`, counted with multiplicity, as its multiplicity in `s`, and
every element of `t` is related to some element of `s`. -/
theorem rel_iff_forall_countP_eq_count [DecidableEq α] [∀ a, DecidablePred (r a)]
    {s : Multiset α} {t : Multiset β}
    (huniq : ∀ b ∈ t, ∀ a ∈ s, ∀ a' ∈ s, r a b → r a' b → a = a') :
    Rel r s t ↔ (∀ a ∈ s, t.countP (r a) = s.count a) ∧ ∀ b ∈ t, ∃ a ∈ s, r a b := by
  first
  | rcases s.empty_or_exists_mem with rfl | ⟨a₀, -⟩
    · simp [rel_zero_left, eq_zero_iff_forall_notMem]
    have : Nonempty α := ⟨a₀⟩
    -- on both sides `s` is the image of `t` under the map sending each element to its partner
    have hcount : ∀ φ : β → α, (∀ b ∈ t, φ b ∈ s) → (∀ b ∈ t, r (φ b) b) →
        ∀ a ∈ s, (t.map φ).count a = t.countP (r a) := fun φ hφ hφr a ha => by
      rw [count_map, ← countP_eq_card_filter]
      exact countP_congr rfl fun b hb => propext
        ⟨fun h => h ▸ hφr b hb, fun h => huniq b hb a ha (φ b) (hφ b hb) h (hφr b hb)⟩
    refine ⟨fun h => ?_, fun ⟨hst, hex⟩ => ?_⟩
    · have hex : ∀ b ∈ t, ∃ a ∈ s, r a b := fun b hb =>
        exists_mem_of_rel_of_mem (rel_flip.2 h) hb
      choose! φ hφ hφr using hex
      have hs : s = t.map φ := rel_eq.1 <| rel_map_right.2 <|
        h.mono fun a ha b hb hab => huniq b hb a ha (φ b) (hφ b hb) hab (hφr b hb)
      refine ⟨fun a ha => ?_, fun b hb => ⟨φ b, hφ b hb, hφr b hb⟩⟩
      rw [← hcount φ hφ hφr a ha, ← hs]
    · choose! φ hφ hφr using hex
      have hs : s = t.map φ := ext.2 fun a => by
        by_cases ha : a ∈ s
        · rw [hcount φ hφ hφr a ha, hst a ha]
        · rw [count_eq_zero.2 ha, count_eq_zero.2 fun hm => ha <| by
            obtain ⟨b, hb, rfl⟩ := mem_map.1 hm
            exact hφ b hb]
      rw [hs]
      exact rel_map_left.2 (rel_refl_of_refl_on hφr)

end Multiset
end -- closes the original EOF section from source line 24
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Multiset/Rel.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Vieta.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Vieta's formulas for a family of roots indexed by a finite type

Mathlib reads the coefficients of a product of linear factors off the elementary symmetric
functions of the multiset of its roots (`Multiset.prod_X_sub_C_coeff`). Here the roots are a
family `x : σ → S` indexed by a finite type and the elementary symmetric functions are the
values of `MvPolynomial.esymm`: the `k`-th elementary symmetric polynomial at `x` is `(-1) ^ k`
times the coefficient of `∏ i, (X - C (x i))` in degree `card σ - k`.

Over a domain a monic polynomial of degree `card σ` whose roots, listed with multiplicity, are
the values of `x` is exactly that product, so the same formula computes its coefficients.

## Main results

* `MvPolynomial.aeval_esymm_eq_coeff_prod_X_sub_C`: the elementary symmetric polynomials at `x`
  are the signed coefficients of `∏ i, (X - C (x i))`.
* `Polynomial.eq_prod_X_sub_C_of_monic_of_roots_eq`: a monic polynomial whose roots are listed by
  `x` is the product of the linear factors `X - C (x i)`.
-/

public section

namespace MvPolynomial

variable {σ R S : Type*} [Fintype σ] [CommSemiring R] [CommRing S] [Algebra R S]

/-- **Vieta's formulas for an indexed family of roots**: the `k`-th elementary symmetric
polynomial, evaluated at `x : σ → S`, is `(-1) ^ k` times the coefficient of the monic polynomial
`∏ i, (X - C (x i))` in degree `card σ - k`. -/
theorem aeval_esymm_eq_coeff_prod_X_sub_C (x : σ → S) {k : ℕ} (hk : k ≤ Fintype.card σ) :
    aeval x (esymm σ R k) =
      (-1) ^ k * (∏ i, (Polynomial.X - Polynomial.C (x i))).coeff (Fintype.card σ - k) := by
  first
  | have hcard : Multiset.card (Finset.univ.val.map x) = Fintype.card σ := by simp
    have hprod : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
        ((Finset.univ.val.map x).map fun t => Polynomial.X - Polynomial.C t).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
      rfl
    rw [aeval_esymm_eq_multiset_esymm, hprod,
      Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact Nat.sub_le _ _), hcard,
      Nat.sub_sub_self hk, ← mul_assoc, ← pow_add, ← Nat.two_mul, pow_mul]
    norm_num

end MvPolynomial

namespace Polynomial

variable {σ R : Type*} [Fintype σ] [CommRing R] [IsDomain R]

/-- A monic polynomial of degree `card σ` whose roots, with multiplicity, are listed by
`x : σ → R` is the product of the linear factors `X - C (x i)`. -/
theorem eq_prod_X_sub_C_of_monic_of_roots_eq {f : R[X]} {x : σ → R} (hf : f.Monic)
    (hdeg : f.natDegree = Fintype.card σ) (hroots : f.roots = Finset.univ.val.map x) :
    f = ∏ i, (X - C (x i)) := by
  first
  | have hcard : Multiset.card f.roots = f.natDegree := by simp [hroots, hdeg]
    conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf hcard]
    rw [hroots, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl

end Polynomial
end -- closes the original EOF section from source line 30
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Vieta.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Roots.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Root sets and multiplicities

This file records several facts about the roots of a polynomial, either in its coefficient field
or after base change to a domain `E`.

First, the root set of a product of polynomials whose base changes to `E` are nonzero is the
union of the root sets of the factors. This is the lemma that decomposes the roots of a
polynomial along a factorisation, for instance the roots of a monic integer polynomial along its
monic irreducible factors. The same holds for the distinct roots of a finite product.
For a separable product, the root sets of the factors are pairwise disjoint.

Second, dividing a polynomial by the linear factor of a simple root removes exactly that root
from the root set. Here `a` only has to be a simple root in `E`: `f a` vanishes and `f' a` does
not vanish after mapping to `E`, so the map `F → E` need not be injective.

Third, translating the variable moves the roots: the roots of `f(X + t)` are the points `x`
with `x + t` a root of `f`, so `x ↦ x + t` is a bijection between the two root sets, and
`f(X + t)` is separable exactly when `f` is.

Fourth, if every root of a nonzero polynomial is among a family of points `θ i`, then its roots
are exactly the `θ i` in which it has positive multiplicity. Over a domain, a nonzero polynomial
has at least `k` roots, counted with multiplicity, exactly when it is divisible by a product of
`k` linear factors `X - x j`.

Fifth, the roots of a product of linear factors over a finite family are the values of the
family. For split monic polynomials, a relation `Multiset.Rel r` between the root multisets is
the same as a pair of enumerations of the roots, indexed by `Fin f.natDegree`, factoring the two
polynomials into linear factors with entries of equal index related by `r`.

Finally, the roots of a polynomial gcd form the multiset intersection of the roots of its
inputs. So when the inputs split, the degree of their gcd counts their common roots, each with
the minimum of its two multiplicities. In characteristic zero this identifies the degree lost to
the gcd with the derivative as the number of distinct roots.

## Main results

* `Polynomial.nodup_roots_of_forall_derivative_eval_ne_zero`: nonvanishing of the derivative at
  every rational root suffices for the rational root multiset to have no repetitions.
* `Polynomial.rootSet_mul`: the root set of a product of polynomials whose base changes to `E` are
  nonzero is the union of the root sets of the factors.
* `Polynomial.roots_prod_toFinset`: the distinct roots of a finite product of nonzero polynomials
  are those of the factors together.
* `Polynomial.aroots_prod_toFinset`: the distinct roots of a finite product of polynomials whose
  base changes to `E` are nonzero are those of the factors together.
* `Polynomial.Separable.pairwiseDisjoint_rootSet`: the factors of a separable product have
  pairwise disjoint root sets.
* `Polynomial.rootSet_divByMonic_X_sub_C`: if `f a = 0` and `f' a ≠ 0` in `E`, then the roots of
  `f /ₘ (X - C a)` are the roots of `f` other than `a`.
* `Polynomial.rootSet_comp_X_add_C`: the roots of `f(X + t)` are the roots of `f` moved by `-t`.
* `Polynomial.rootSetCompXAddCEquiv`: the bijection `x ↦ x + t` from the roots of `f(X + t)` to
  the roots of `f`.
* `Polynomial.separable_comp_X_add_C_iff`: `f(X + t)` is separable exactly when `f` is.
* `Polynomial.isRoot_iff_of_rootMultiplicity`: if every root of a nonzero polynomial is among
  the `θ i`, then its roots are the `θ i` in which it has positive multiplicity.
* `Polynomial.le_card_roots_iff_exists_prod_X_sub_C_dvd`: a nonzero polynomial over a domain has
  at least `k` roots exactly when it is divisible by a product of `k` linear factors.
* `Polynomial.roots_prod_X_sub_C_map`: the roots of a product of linear factors over a finite
  family are the values of the family.
* `Polynomial.roots_C_mul_prod_X_sub_C`: the roots of a nonzero constant times a product of
  linear factors over a finite family are the values of the family.
* `Polynomial.roots_eq_map_of_eq_C_mul_prod_X_sub_C`: the same for a nonzero polynomial presented
  as its leading coefficient times such a product.
* `Polynomial.Monic.rel_roots_iff_exists_prod_X_sub_C`: for split monic polynomials, the root
  multisets are related by `Multiset.Rel r` exactly when the polynomials factor over enumerations
  of their roots with entries of equal index related by `r`.
* `Polynomial.rootMultiplicity_gcd`: a root's multiplicity in a gcd is the minimum of its
  multiplicities in the two inputs.
* `Polynomial.card_roots_inter_eq_sum_min_rootMultiplicity`: the common roots counted with
  multiplicity in the multiset intersection are counted with the minimum of their two
  multiplicities.
* `Polynomial.natDegree_gcd_eq_card_roots_inter_of_splits`: the degree of the gcd of two nonzero
  polynomials, one of them split, is the number of their common roots counted with the minimum
  of their multiplicities.
* `Polynomial.natDegree_gcd_eq_card_aroots_inter`: the same count for the common roots in an
  algebraically closed field of two polynomials over a field `k`, with the gcd taken over `k`.
* `Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset`: over an
  algebraically closed field of characteristic zero, degree minus the degree of the derivative
  gcd counts distinct roots.
* `Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_aroots_toFinset`: the same count for
  the distinct roots in such a field of a polynomial over a field `k`, with the gcd taken over
  `k`.
-/

public section

namespace TauCeti

open Finset Polynomial

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- If the derivative is nonzero at every rational root, the rational root multiset has no
repetitions. Unlike separability, this imposes no condition on roots in larger fields. -/
theorem _root_.Polynomial.nodup_roots_of_forall_derivative_eval_ne_zero [IsDomain F]
    (h : ∀ x ∈ f.roots, f.derivative.eval x ≠ 0) : f.roots.Nodup := by
  first
  | classical
    refine Multiset.nodup_iff_count_le_one.mpr fun x ↦ ?_
    by_cases hx : x ∈ f.roots
    · have hd : f.derivative ≠ 0 := fun he ↦ h x hx (by simp [he])
      have hm := rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero f x hd
      rw [rootMultiplicity_eq_zero (h x hx)] at hm
      rw [count_roots]
      omega
    · simp [Multiset.count_eq_zero_of_notMem hx]

/-- The root set of a product of polynomials is the union of the root sets of the factors,
provided neither factor vanishes after base change to `E`. -/
@[simp]
theorem _root_.Polynomial.rootSet_mul {g : F[X]} (hf : f.map (algebraMap F E) ≠ 0)
    (hg : g.map (algebraMap F E) ≠ 0) : (f * g).rootSet E = f.rootSet E ∪ g.rootSet E := by
  first
  | ext x
    simp only [Set.mem_union, mem_rootSet', Polynomial.map_mul, map_mul, mul_eq_zero, ne_eq, hf, hg,
      or_self, not_false_eq_true, true_and]

/-- The distinct roots of a finite product of nonzero polynomials are those of the factors
together. -/
theorem _root_.Polynomial.roots_prod_toFinset [IsDomain F] [DecidableEq F]
    {ι : Type*} (s : Finset ι)
    (f : ι → F[X]) (hf : ∀ k ∈ s, f k ≠ 0) :
    (s.prod f).roots.toFinset = s.biUnion fun k ↦ (f k).roots.toFinset := by
  first
  | classical
    rw [roots_prod _ _ (Finset.prod_ne_zero_iff.mpr hf), Finset.bind_toFinset, s.val_toFinset]

/-- The distinct roots in `E` of a finite product of polynomials are those of the factors together,
provided no factor vanishes after base change to `E`. -/
theorem _root_.Polynomial.aroots_prod_toFinset [DecidableEq E] {ι : Type*} (s : Finset ι)
    (f : ι → F[X]) (hf : ∀ k ∈ s, (f k).map (algebraMap F E) ≠ 0) :
    ((∏ k ∈ s, f k).aroots E).toFinset = s.biUnion fun k ↦ ((f k).aroots E).toFinset := by
  first
  | ext z
    simp only [Multiset.mem_toFinset, Finset.mem_biUnion, mem_aroots', Polynomial.map_prod,
      Finset.prod_ne_zero_iff.2 hf, ne_eq, not_false_eq_true, true_and, map_prod,
      Finset.prod_eq_zero_iff]
    exact ⟨fun ⟨k, hk, h⟩ ↦ ⟨k, hk, hf k hk, h⟩, fun ⟨k, hk, _, h⟩ ↦ ⟨k, hk, h⟩⟩

/-- The factors of a separable product have pairwise disjoint root sets: a common root of two
factors would be a repeated root of the product. Together with `Polynomial.rootSet_prod`, the
root set of the product is the disjoint union of the root sets of the factors. -/
theorem _root_.Polynomial.Separable.pairwiseDisjoint_rootSet {ι : Type*} {s : Finset ι}
    {g : ι → F[X]} (hsep : (∏ i ∈ s, g i).Separable) :
    (s : Set ι).PairwiseDisjoint fun i => (g i).rootSet E := by
  first
  | classical
    intro i hi j hj hij
    refine Set.disjoint_left.mpr fun y hyi hyj => ?_
    have hdvd : g i * g j ∣ ∏ k ∈ s, g k := by
      rw [← Finset.prod_pair hij]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.insert_subset hi (by simpa using hj))
    obtain ⟨a, b, hab⟩ := (hsep.of_dvd hdvd).isCoprime
    have := congrArg (aeval y) hab
    simp [(mem_rootSet'.mp hyi).2, (mem_rootSet'.mp hyj).2] at this

/-- Removing the linear factor of a simple root `a` removes exactly that root: if, in `E`, `f a`
vanishes and `f' a` does not, then the roots of `f /ₘ (X - C a)` in `E` are the roots of `f`
other than `a`. -/
@[simp]
theorem _root_.Polynomial.rootSet_divByMonic_X_sub_C {a : F} (ha : algebraMap F E (f.eval a) = 0)
    (ha' : algebraMap F E (f.derivative.eval a) ≠ 0) :
    (f /ₘ (X - C a)).rootSet E = f.rootSet E \ {algebraMap F E a} := by
  first
    -- `a` is not a root of the quotient in `E`: the quotient takes the value `f' a` there.
  | have hq := congrArg (eval a) (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a)
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hq
    have hq0 : aeval (algebraMap F E a) (f /ₘ (X - C a)) ≠ 0 := by
      rwa [aeval_algebraMap_apply_eq_algebraMap_eval, hq]
    -- In `E`, `f = (X - C a) * (f /ₘ (X - C a))`, since the remainder `f a` vanishes there.
    have hmap : ((X - C a) * (f /ₘ (X - C a))).map (algebraMap F E) = f.map (algebraMap F E) := by
      rw [X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval,
        Polynomial.map_sub, map_C, ha, C_0, sub_zero]
    -- So the roots of `f` are those of the two factors.
    have hsplit : f.rootSet E = (X - C a).rootSet E ∪ (f /ₘ (X - C a)).rootSet E := by
      rw [← rootSet_map E E f, ← hmap, rootSet_map, rootSet_mul ((monic_X_sub_C a).map _).ne_zero
        fun h ↦ hq0 (by rw [← eval_map_algebraMap, h, eval_zero])]
    -- The linear factor contributes only `a`, which is not a root of the quotient.
    ext x
    rw [hsplit]
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff, (monic_X_sub_C a).mem_rootSet,
      map_sub, aeval_X, aeval_C, sub_eq_zero]
    constructor
    · exact fun hx ↦ ⟨Or.inr hx, fun hxa ↦ hq0 (hxa ▸ aeval_eq_zero_of_mem_rootSet hx)⟩
    · rintro ⟨hxa | hx, hxa'⟩
      · exact absurd hxa hxa'
      · exact hx

/-- The roots of `f(X + t)` are the points `x` with `x + t` a root of `f`. -/
theorem _root_.Polynomial.rootSet_comp_X_add_C (f : F[X]) (t : F) :
    (f.comp (X + C t)).rootSet E = (· + algebraMap F E t) ⁻¹' f.rootSet E := by
  first
  | ext x
    simp [mem_rootSet', Polynomial.map_comp, comp_X_add_C_ne_zero_iff, aeval_comp]

/-- The bijection `x ↦ x + t` from the roots of `f(X + t)` to the roots of `f`. -/
def _root_.Polynomial.rootSetCompXAddCEquiv (f : F[X]) (t : F) (E : Type*) [CommRing E]
    [IsDomain E] [Algebra F E] :
    (f.comp (X + C t)).rootSet E ≃ f.rootSet E :=
  (Equiv.addRight (algebraMap F E t)).subtypeEquiv fun x => by
    rw [rootSet_comp_X_add_C, Set.mem_preimage, Equiv.coe_addRight]

/-- The bijection `Polynomial.rootSetCompXAddCEquiv` adds `t`. -/
@[simp]
theorem _root_.Polynomial.coe_rootSetCompXAddCEquiv_apply (f : F[X]) (t : F)
    (x : (f.comp (X + C t)).rootSet E) :
    (rootSetCompXAddCEquiv f t E x : E) = x + algebraMap F E t :=
  (rfl)

/-- The inverse of `Polynomial.rootSetCompXAddCEquiv` subtracts `t`. -/
@[simp]
theorem _root_.Polynomial.coe_rootSetCompXAddCEquiv_symm_apply (f : F[X]) (t : F)
    (x : f.rootSet E) :
    ((rootSetCompXAddCEquiv f t E).symm x : E) = x - algebraMap F E t := by
  first
  | obtain ⟨y, rfl⟩ := (rootSetCompXAddCEquiv f t E).surjective x
    simp

/-- Translating the variable preserves separability. -/
theorem _root_.Polynomial.Separable.comp_X_add_C (hf : f.Separable) (t : F) :
    (f.comp (X + C t)).Separable := by
  first
  | rw [Separable, derivative_comp, derivative_X_add_C, one_mul]
    exact IsCoprime.map hf (compRingHom (X + C t))

/-- `f(X + t)` is separable exactly when `f` is. -/
@[simp]
theorem _root_.Polynomial.separable_comp_X_add_C_iff {t : F} :
    (f.comp (X + C t)).Separable ↔ f.Separable := by
  first
  | refine ⟨fun h => ?_, fun h => h.comp_X_add_C t⟩
    simpa [comp_assoc, add_assoc] using h.comp_X_add_C (-t)

/-- If every root of a nonzero polynomial `p` is some `θ i`, and the multiplicity of each `θ i`
as a root of `p` is `m i`, then the roots of `p` are the `θ i` with `0 < m i`. -/
theorem _root_.Polynomial.isRoot_iff_of_rootMultiplicity {ι : Type*} {p : F[X]} {θ : ι → F}
    {m : ι → ℕ} (hm : ∀ i, p.rootMultiplicity (θ i) = m i)
    (hθ : ∀ t, p.IsRoot t → ∃ i, θ i = t) (hp : p ≠ 0) (t : F) :
    p.IsRoot t ↔ ∃ i, θ i = t ∧ 0 < m i := by
  first
  | refine ⟨fun ht ↦ ?_, fun ⟨i, hi, hpos⟩ ↦ ?_⟩
    · obtain ⟨i, rfl⟩ := hθ t ht
      exact ⟨i, rfl, hm i ▸ (rootMultiplicity_pos hp).2 ht⟩
    · rw [← hi, ← rootMultiplicity_pos hp, hm i]
      exact hpos

/-- A nonzero polynomial over a domain has at least `k` roots, counted with multiplicity, exactly
when it is divisible by `∏ j, (X - x j)` for some `x : Fin k → R`. This is
`Multiset.prod_X_sub_C_dvd_iff_le_roots` with the submultiset of roots listed by `Fin k`. -/
theorem _root_.Polynomial.le_card_roots_iff_exists_prod_X_sub_C_dvd {R : Type*} [CommRing R]
    [IsDomain R] {p : R[X]} (hp : p ≠ 0) {k : ℕ} :
    k ≤ p.roots.card ↔ ∃ x : Fin k → R, (∏ j, (X - C (x j))) ∣ p := by
  first
  | have key (x : Fin k → R) :
        ∏ j, (X - C (x j)) = ((univ.val.map x).map fun a ↦ X - C a).prod := by
      rw [prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]
    constructor
    · -- List the first `k` roots.
      intro h
      set l := p.roots.toList
      have hl : k ≤ l.length := by simpa [l] using h
      refine ⟨fun j ↦ l[j.1], ?_⟩
      rw [key, Multiset.prod_X_sub_C_dvd_iff_le_roots hp, Fin.univ_val_map]
      conv_rhs => rw [← Multiset.coe_toList p.roots]
      have : List.ofFn (fun j : Fin k ↦ l[j.1]) = l.take k :=
        List.ext_getElem (by simp; omega) fun i _ _ ↦ by simp
      rw [this]
      exact Multiset.coe_le.2 (List.take_sublist k l).subperm
    · rintro ⟨x, hx⟩
      rw [key] at hx
      have := Polynomial.roots.le_of_dvd hp hx
      rw [roots_multiset_prod_X_sub_C] at this
      simpa using Multiset.card_le_card this

section Rel

variable [IsDomain F]

/-- The roots of the product of the linear factors of a finite family are the values of the
family, with multiplicity. -/
@[simp]
theorem _root_.Polynomial.roots_prod_X_sub_C_map {ι : Type*} (s : Finset ι) (x : ι → F) :
    (∏ i ∈ s, (X - C (x i))).roots = s.val.map x := by
  first
  | simp [roots_prod, X_sub_C_ne_zero, prod_ne_zero_iff]

/-- The roots of a nonzero constant times the product of the linear factors of a finite family are
the values of the family, with multiplicity. -/
theorem _root_.Polynomial.roots_C_mul_prod_X_sub_C {ι : Type*} (s : Finset ι) (x : ι → F) {c : F}
    (hc : c ≠ 0) : (C c * ∏ i ∈ s, (X - C (x i))).roots = s.val.map x := by
  first
  | rw [roots_C_mul _ hc, roots_prod_X_sub_C_map]

/-- The roots of a nonzero polynomial presented as its leading coefficient times the product of the
linear factors of a finite family are the values of the family, with multiplicity. -/
theorem _root_.Polynomial.roots_eq_map_of_eq_C_mul_prod_X_sub_C {ι : Type*} {s : Finset ι}
    {x : ι → F} {p : F[X]} (hp : p ≠ 0) (hpx : p = C p.leadingCoeff * ∏ i ∈ s, (X - C (x i))) :
    p.roots = s.val.map x := by
  first
  | rw [hpx]
    exact roots_C_mul_prod_X_sub_C s x (leadingCoeff_ne_zero.2 hp)

/-- **Matching roots as a multiset relation.** For split monic polynomials `f` and `g`, the root
multisets are related by `Multiset.Rel r` exactly when `f` and `g` are the products of the linear
factors of enumerations `a` and `b` of their roots, indexed by `Fin f.natDegree`, with
`r (a i) (b i)` for every `i`. -/
theorem _root_.Polynomial.Monic.rel_roots_iff_exists_prod_X_sub_C {f g : F[X]} (hf : f.Monic)
    (hg : g.Monic) (hfs : f.Splits) (hgs : g.Splits) {r : F → F → Prop} :
    f.roots.Rel r g.roots ↔ ∃ a b : Fin f.natDegree → F,
      f = ∏ i, (X - C (a i)) ∧ g = ∏ i, (X - C (b i)) ∧ ∀ i, r (a i) (b i) := by
  first
  | refine ⟨fun h => ?_, fun ⟨a, b, hfa, hgb, hab⟩ => ?_⟩
    · obtain ⟨n, a, b, hfa, hgb, hab⟩ := Multiset.rel_iff_exists_fin.1 h
      obtain rfl : n = f.natDegree := by simp [hfs.natDegree_eq_card_roots, hfa]
      exact ⟨a, b, eq_prod_X_sub_C_of_monic_of_roots_eq hf (by simp) hfa,
        eq_prod_X_sub_C_of_monic_of_roots_eq hg (by simp [hgs.natDegree_eq_card_roots, hgb]) hgb,
        hab⟩
    · exact Multiset.rel_iff_exists_fin.2 ⟨_, a, b,
        (congrArg roots hfa).trans (roots_prod_X_sub_C_map _ a),
        (congrArg roots hgb).trans (roots_prod_X_sub_C_map _ b), hab⟩

end Rel

section Inter

variable [IsDomain F] [DecidableEq F]

/-- The size of the multiset intersection of the roots of two polynomials is the sum, over their
distinct common roots, of the minimum of the two multiplicities. -/
theorem _root_.Polynomial.card_roots_inter_eq_sum_min_rootMultiplicity (p q : F[X]) :
    Multiset.card (p.roots ∩ q.roots) =
      ∑ x ∈ p.roots.toFinset ∩ q.roots.toFinset,
        min (p.rootMultiplicity x) (q.rootMultiplicity x) := by
  first
  | rw [← Multiset.sum_count_eq_card (s := p.roots.toFinset ∩ q.roots.toFinset)
      fun x hx => by simpa using Multiset.mem_inter.mp hx]
    simp [Multiset.count_inter, count_roots]

end Inter

section GCD

variable {K : Type*} [Field K] [DecidableEq K]

/-- The multiplicity of a root in the gcd of two nonzero polynomials is the minimum of its
multiplicities in the two polynomials. -/
theorem _root_.Polynomial.rootMultiplicity_gcd (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (x : K) :
    (EuclideanDomain.gcd p q).rootMultiplicity x =
      min (p.rootMultiplicity x) (q.rootMultiplicity x) := by
  first
  | have hg : EuclideanDomain.gcd p q ≠ 0 := by
      intro h
      exact hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
    apply le_antisymm
    · exact le_min
        (rootMultiplicity_le_rootMultiplicity_of_dvd hp (EuclideanDomain.gcd_dvd_left p q) x)
        (rootMultiplicity_le_rootMultiplicity_of_dvd hq (EuclideanDomain.gcd_dvd_right p q) x)
    · rw [le_rootMultiplicity_iff hg]
      apply EuclideanDomain.dvd_gcd
      · exact (le_rootMultiplicity_iff hp).mp (min_le_left _ _)
      · exact (le_rootMultiplicity_iff hq).mp (min_le_right _ _)

/-- The roots of the gcd of two nonzero polynomials are the multiset intersection of their roots.
Thus a common root occurs with the minimum of its two input multiplicities. -/
theorem _root_.Polynomial.roots_gcd (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    (EuclideanDomain.gcd p q).roots = p.roots ∩ q.roots := by
  first
  | ext x
    simp [count_roots, rootMultiplicity_gcd p q hp hq]

/-- **Multiplicity formula for common roots.** If `p` and `q` are nonzero and `p` splits, then
the degree of their gcd is the number of their common roots, each counted with the minimum of its
multiplicities in `p` and in `q`. -/
theorem _root_.Polynomial.natDegree_gcd_eq_card_roots_inter_of_splits {p q : K[X]} (hp : p ≠ 0)
    (hq : q ≠ 0) (hsplit : p.Splits) :
    (EuclideanDomain.gcd p q).natDegree = Multiset.card (p.roots ∩ q.roots) := by
  first
  | rw [← roots_gcd p q hp hq]
    exact (hsplit.of_dvd hp (EuclideanDomain.gcd_dvd_left p q)).natDegree_eq_card_roots

section CharZero

variable [CharZero K]

/-- In characteristic zero, the roots of a polynomial's derivative gcd, together with one copy
of each distinct root, recover all roots with multiplicity. -/
theorem _root_.Polynomial.roots_gcd_derivative_add_dedup (p : K[X]) :
    (EuclideanDomain.gcd p p.derivative).roots + p.roots.dedup = p.roots := by
  first
  | by_cases hdeg : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hdeg, roots_C, Multiset.dedup_zero, add_zero]
      simp
    · have hp : p ≠ 0 := fun h ↦ hdeg (h ▸ natDegree_zero)
      have hd : p.derivative ≠ 0 := derivative_ne_zero.mpr hdeg
      ext x
      rw [Multiset.count_add, count_roots, rootMultiplicity_gcd p p.derivative hp hd,
        count_roots]
      by_cases hx : p.IsRoot x
      · rw [derivative_rootMultiplicity_of_root hx]
        have hm : 0 < p.rootMultiplicity x := (rootMultiplicity_pos hp).mpr hx
        rw [Multiset.count_dedup, ite_eq_left ((mem_roots hp).mpr hx)]
        omega
      · have hm : p.rootMultiplicity x = 0 := rootMultiplicity_eq_zero hx
        have hmem : x ∉ p.roots := fun h => hx ((mem_roots hp).mp h)
        rw [hm, zero_min, Multiset.count_dedup, ite_eq_right hmem]

/-- For a split polynomial in characteristic zero, the number of distinct roots of a nonzero
polynomial is its degree minus the degree of its gcd with its derivative. -/
theorem _root_.Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits
    {p : K[X]} (hp : p ≠ 0) (hsplit : p.Splits) :
    p.natDegree - (EuclideanDomain.gcd p p.derivative).natDegree = p.roots.toFinset.card := by
  first
  | by_cases hdeg : p.natDegree = 0
    · have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      rw [hdeg, hpC, roots_C]
      simp
    · have hsplitg : (EuclideanDomain.gcd p p.derivative).Splits :=
        hsplit.of_dvd hp (EuclideanDomain.gcd_dvd_left p p.derivative)
      have hcard := congrArg Multiset.card (roots_gcd_derivative_add_dedup p)
      rw [Multiset.card_add] at hcard
      rw [hsplit.natDegree_eq_card_roots, hsplitg.natDegree_eq_card_roots,
        Multiset.card_toFinset]
      omega

end CharZero

section IsAlgClosed

variable [IsAlgClosed K]

/-- **Multiplicity formula for common roots.** The degree of the gcd of two nonzero polynomials
over a field `k`, taken over `k`, is the number of their common roots in an algebraically closed
field `K`, each counted with the minimum of its two multiplicities. -/
theorem _root_.Polynomial.natDegree_gcd_eq_card_aroots_inter {k : Type*} [Field k]
    [DecidableEq k] [Algebra k K] {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (EuclideanDomain.gcd p q).natDegree = Multiset.card (p.aroots K ∩ q.aroots K) := by
  first
  | have hinj := (algebraMap k K).injective
    rw [aroots_def, aroots_def, ← natDegree_gcd_eq_card_roots_inter_of_splits
      ((Polynomial.map_ne_zero_iff hinj).2 hp) ((Polynomial.map_ne_zero_iff hinj).2 hq)
      (IsAlgClosed.splits _), gcd_map, natDegree_map]

variable [CharZero K]

/-- Over an algebraically closed field of characteristic zero, the number of distinct roots of a
nonzero polynomial is its degree minus the degree of its gcd with its derivative. -/
theorem _root_.Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset
    {p : K[X]} (hp : p ≠ 0) :
    p.natDegree - (EuclideanDomain.gcd p p.derivative).natDegree = p.roots.toFinset.card :=
  natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits hp
    (IsAlgClosed.splits p)

/-- The number of distinct roots of a nonzero polynomial over a field `k` in an algebraically
closed field `K` of characteristic zero is its degree minus the degree of its gcd with its
derivative, both taken over `k`. -/
theorem _root_.Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_aroots_toFinset
    {k : Type*} [Field k] [DecidableEq k] [Algebra k K] {p : k[X]} (hp : p ≠ 0) :
    p.natDegree - (EuclideanDomain.gcd p p.derivative).natDegree =
      (p.aroots K).toFinset.card := by
  first
  | rw [aroots_def, ← natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset
      ((Polynomial.map_ne_zero_iff (algebraMap k K).injective).2 hp), derivative_map, gcd_map,
      natDegree_map, natDegree_map]

end IsAlgClosed

end GCD

end TauCeti
end -- closes the original EOF section from source line 98
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Roots.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Projection/Collins.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Collins projection set

For a finite family `F` of univariate polynomials over a commutative ring `R`, the Collins
projection `F.collinsProjection` is a finite subset of `R`. Write `T` for the set of all reducta
of all members of `F`. The projection contains

* every coefficient `r.coeff i`, `i ≤ r.natDegree`, of every `r ∈ T`;
* every principal subresultant coefficient of `r` and `r.derivative` for `r ∈ T`;
* every principal subresultant coefficient of `r` and `s` for `r, s ∈ T`,

where the principal subresultant coefficients are taken at the actual degrees of the reducta,
at every index from zero through the smaller of the two degrees. Zero and constant entries, and
pairs coming from the same member of `F`, are retained: this gives a simple finite superset of
Collins' projection which needs no preprocessing of the family.

The intended coefficient ring is `R = MvPolynomial (Fin n) A`, so that `F` is a family of
polynomials in one distinguished variable over the base coordinates. Specializing the base
coordinates is a ring homomorphism `φ : R →+* S`, and it can lower degrees. Truncation and
principal coefficients are taken *before* specialization, and the reducta account for every
possible drop in degree. The coefficients of `p.map φ` are the images of the coefficients of
`p`, which lie in the projection. For commutative-ring targets, the specialization lemmas show
that pairwise principal subresultant coefficients at the actual specialized degrees are also
images under `φ` of elements of the projection; the derivative case requires an additively
torsion-free target. Thus the signs of the projection at a base point determine the degrees of
the specialized polynomials and, through the subresultant gcd criterion, the degrees of their
pairwise gcds and of their gcds with their derivatives. This is how the projection enters
Collins' delineability theorem.

The last section compares two specializations under which the same elements of the projection
vanish, for instance evaluation at two points of a base set on which the projection is
sign-invariant. Degrees and nullified members agree for arbitrary semiring targets. Pairwise
principal subresultant coefficients have the same zero patterns for commutative-ring targets;
the derivative case requires additively torsion-free targets. Pairwise gcd degrees agree for
field targets, and gcd degrees with derivatives agree for additively torsion-free field targets.
In characteristic-zero fields, a member that splits under both specializations has the same
number of distinct roots; algebraically closed fields satisfy the splitting hypotheses.

## Main definitions and results

* `Finset.collinsProjection`: the Collins projection set of a finite family.
* `Finset.mem_collinsProjection`: the explicit description of its elements.
* `Finset.collinsProjection_mono`: the projection is monotone in the family.
* `Finset.collinsProjection_image_map`: an injective coefficient map commutes with projection.
* `Finset.collinsProjection_image_finSuccEquiv'_map`,
  `Finset.collinsProjection_image_finSuccEquiv_map`: for a family of polynomials in `n + 1`
  variables, singling out a variable and projecting commutes with an injective coefficient map.
  In particular the projection of a family with integer coefficients, viewed over `ℝ`, is the
  image of the projection computed entirely over `ℤ`.
* `Finset.psc_map_mem_image_collinsProjection`,
  `Finset.psc_map_derivative_mem_image_collinsProjection`: principal subresultant coefficients
  of specialized polynomials, at the specialized degrees, come from the projection. The
  derivative case requires an additively torsion-free target.
* `Finset.natDegree_map_eq_of_collinsProjection`, `Finset.map_eq_zero_iff_of_collinsProjection`:
  two specializations into arbitrary semirings under which the same elements of the projection
  vanish give every member of the family the same degree, and nullify the same members.
* `Finset.natDegree_gcd_map_eq_of_collinsProjection`,
  `Finset.natDegree_gcd_map_derivative_eq_of_collinsProjection`: under the same hypothesis, the
  specialized pairwise gcds have the same degrees over fields. The gcds with derivatives have
  the same degrees over additively torsion-free fields.
* `Finset.card_roots_toFinset_map_eq_of_collinsProjection_of_splits`: over characteristic-zero
  fields, a member that splits under both specializations has the same number of distinct roots.
* `Finset.card_roots_toFinset_map_eq_of_collinsProjection`: the algebraically closed case.

## References

* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapters 5 and 11.
* D. Jovanović, *Solving Non-Linear Arithmetic*, dissertation, New York University, 2012,
  Definition 2.5 and Theorem 2.6.
-/

public section

open Polynomial

namespace Finset

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The Collins projection of a finite family of polynomials. With `T` the set of all reducta of
members of `F`, it consists of all coefficients of members of `T`, and the principal
subresultant coefficients of `(r, r.derivative)` and of `(r, s)` for `r, s ∈ T`, at the actual
degrees of these polynomials and at every index through the smaller degree. -/
noncomputable def collinsProjection (F : Finset R[X]) : Finset R := by
  first
  | classical
    let T := F.biUnion reducta
    exact (T.biUnion fun r ↦ (range (r.natDegree + 1)).image r.coeff) ∪
      (T.biUnion fun r ↦ (range (min r.natDegree r.derivative.natDegree + 1)).image
        (psc r r.derivative r.natDegree r.derivative.natDegree)) ∪
      T.biUnion fun r ↦ T.biUnion fun s ↦ (range (min r.natDegree s.natDegree + 1)).image
        (psc r s r.natDegree s.natDegree)

/-- The elements of the Collins projection: coefficients of reducta, principal subresultant
coefficients of a reductum and its derivative, and principal subresultant coefficients of two
reducta, all at actual degrees. -/
theorem mem_collinsProjection {F : Finset R[X]} {a : R} :
    a ∈ F.collinsProjection ↔
      (∃ p ∈ F, ∃ r ∈ p.reducta, ∃ i ≤ r.natDegree, r.coeff i = a) ∨
      (∃ p ∈ F, ∃ r ∈ p.reducta, ∃ j ≤ min r.natDegree r.derivative.natDegree,
        psc r r.derivative r.natDegree r.derivative.natDegree j = a) ∨
      ∃ p ∈ F, ∃ r ∈ p.reducta, ∃ q ∈ F, ∃ s ∈ q.reducta, ∃ j ≤ min r.natDegree s.natDegree,
        psc r s r.natDegree s.natDegree j = a := by
  first
  | classical
    simp only [collinsProjection, mem_union, mem_biUnion, mem_image, mem_range, Nat.lt_succ_iff,
      or_assoc]
    grind

/-- Every coefficient of a reductum of a member of the family, up to its degree, lies in the
Collins projection. -/
theorem coeff_mem_collinsProjection {F : Finset R[X]} {p r : R[X]} (hp : p ∈ F)
    (hr : r ∈ p.reducta) {i : ℕ} (hi : i ≤ r.natDegree) : r.coeff i ∈ F.collinsProjection :=
  mem_collinsProjection.2 <| Or.inl ⟨p, hp, r, hr, i, hi, rfl⟩

/-- The principal subresultant coefficients of a reductum of a member of the family and its
derivative, at their actual degrees, lie in the Collins projection. -/
theorem psc_derivative_mem_collinsProjection {F : Finset R[X]} {p r : R[X]} (hp : p ∈ F)
    (hr : r ∈ p.reducta) {j : ℕ} (hj : j ≤ min r.natDegree r.derivative.natDegree) :
    psc r r.derivative r.natDegree r.derivative.natDegree j ∈ F.collinsProjection :=
  mem_collinsProjection.2 <| Or.inr <| Or.inl ⟨p, hp, r, hr, j, hj, rfl⟩

/-- The principal subresultant coefficients of two reducta of members of the family, at their
actual degrees, lie in the Collins projection. -/
theorem psc_mem_collinsProjection {F : Finset R[X]} {p q r s : R[X]} (hp : p ∈ F)
    (hr : r ∈ p.reducta) (hq : q ∈ F) (hs : s ∈ q.reducta) {j : ℕ}
    (hj : j ≤ min r.natDegree s.natDegree) :
    psc r s r.natDegree s.natDegree j ∈ F.collinsProjection :=
  mem_collinsProjection.2 <| Or.inr <| Or.inr ⟨p, hp, r, hr, q, hq, s, hs, j, hj, rfl⟩

/-- The Collins projection of the empty family is empty. -/
@[simp]
theorem collinsProjection_empty : (∅ : Finset R[X]).collinsProjection = ∅ := by
  first
  | ext a
    simp [mem_collinsProjection]

/-- Enlarging the family enlarges its Collins projection. -/
@[gcongr]
theorem collinsProjection_mono {F G : Finset R[X]} (h : F ⊆ G) :
    F.collinsProjection ⊆ G.collinsProjection := by
  first
  | intro a ha
    rw [mem_collinsProjection] at ha ⊢
    rcases ha with ⟨p, hp, r, hr, i, hi, rfl⟩ | ⟨p, hp, r, hr, j, hj, rfl⟩ |
      ⟨p, hp, r, hr, q, hq, s, hs, j, hj, rfl⟩
    · exact Or.inl ⟨p, h hp, r, hr, i, hi, rfl⟩
    · exact Or.inr <| Or.inl ⟨p, h hp, r, hr, j, hj, rfl⟩
    · exact Or.inr <| Or.inr ⟨p, h hp, r, hr, q, h hq, s, hs, j, hj, rfl⟩

open scoped Classical in
/-- An injective coefficient map commutes with the Collins projection. Injectivity preserves the
degrees of all reducta and of their derivatives, so the principal subresultant coefficients are
taken at the same formal bounds before and after the map. Without injectivity degrees can drop,
and the two sides use different bounds. -/
theorem collinsProjection_image_map {φ : R →+* S} (hφ : Function.Injective φ)
    (F : Finset R[X]) :
    (F.image (Polynomial.map φ)).collinsProjection = F.collinsProjection.image φ := by
  first
  | have hdeg (r : R[X]) : (r.map φ).natDegree = r.natDegree := natDegree_map_eq_of_injective hφ r
    have hcoeff (r : R[X]) : (r.map φ).coeff = φ ∘ r.coeff := funext (coeff_map φ)
    have hpsc (r s : R[X]) (m n : ℕ) : psc (r.map φ) (s.map φ) m n = φ ∘ psc r s m n :=
      funext (psc_map_map φ r s m n)
    simp only [collinsProjection, image_union, image_biUnion, biUnion_image, biUnion_biUnion,
      reducta_map, image_image, hdeg, derivative_map, hpsc, hcoeff]

section MvPolynomial

variable {n : ℕ} [DecidableEq (MvPolynomial (Fin n) S)] [DecidableEq (MvPolynomial (Fin n) R)[X]]
  [DecidableEq (MvPolynomial (Fin n) S)[X]]

/-- **Projection of multivariate families along an injective coefficient map.** Let `P` be a
finite family of polynomials in the variables `X 0, …, X n` over `R`, viewed as polynomials in
the distinguished variable `X i` over the polynomials in the other variables. Mapping the
coefficients along an injective `φ : R →+* S` before singling out `X i` gives a family whose
Collins projection is the image of the Collins projection computed over `R`. -/
theorem collinsProjection_image_finSuccEquiv'_map {φ : R →+* S} (hφ : Function.Injective φ)
    (P : Finset (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1)) :
    (P.image fun f ↦ MvPolynomial.finSuccEquiv' S i (f.map φ)).collinsProjection =
      (P.image (MvPolynomial.finSuccEquiv' R i)).collinsProjection.image (MvPolynomial.map φ) := by
  first
    -- `collinsProjection_image_map` is stated with classical `DecidableEq` instances; `convert`
    -- identifies them with the ones here, leaving the two descriptions of the mapped family.
  | convert collinsProjection_image_map (MvPolynomial.map_injective φ hφ) _ using 2
    ext
    simp [MvPolynomial.finSuccEquiv'_map]

/-- **Projection of multivariate families along an injective coefficient map**, for the
distinguished variable `X 0` singled out by `MvPolynomial.finSuccEquiv`. For
`φ = Int.castRingHom ℝ`, this says that the Collins projection of a family of polynomials with
integer coefficients, read over `ℝ`, is the image of the Collins projection computed entirely
over `ℤ`. -/
theorem collinsProjection_image_finSuccEquiv_map {φ : R →+* S} (hφ : Function.Injective φ)
    (P : Finset (MvPolynomial (Fin (n + 1)) R)) :
    (P.image fun f ↦ MvPolynomial.finSuccEquiv S n (f.map φ)).collinsProjection =
      (P.image (MvPolynomial.finSuccEquiv R n)).collinsProjection.image (MvPolynomial.map φ) := by
  first
  | simpa only [MvPolynomial.finSuccEquiv'_zero] using
      collinsProjection_image_finSuccEquiv'_map hφ P 0

end MvPolynomial

/-- **Specialization of principal subresultant coefficients.** For members `p, q` of the family
and any coefficient map `φ`, the principal subresultant coefficients of `p.map φ` and `q.map φ`
at their actual degrees are images of elements of the Collins projection. The witnesses are the
corresponding coefficients of the reducta cut off just above the specialized degrees. -/
theorem psc_map_mem_image_collinsProjection [DecidableEq S] (φ : R →+* S) {F : Finset R[X]}
    {p q : R[X]} (hp : p ∈ F) (hq : q ∈ F) {j : ℕ}
    (hj : j ≤ min (p.map φ).natDegree (q.map φ).natDegree) :
    psc (p.map φ) (q.map φ) (p.map φ).natDegree (q.map φ).natDegree j ∈
      F.collinsProjection.image φ := by
  first
  | have hr := natDegree_reductum_natDegree_map_add_one φ p
    have hs := natDegree_reductum_natDegree_map_add_one φ q
    refine mem_image.2 ⟨_, psc_mem_collinsProjection hp (p.reductum_mem_reducta _) hq
      (q.reductum_mem_reducta _) (j := j) (by rwa [hr, hs]), ?_⟩
    rw [← psc_map_map, map_reductum_natDegree_map_add_one, map_reductum_natDegree_map_add_one,
      hr, hs]

/-- **Specialization of derivative principal subresultant coefficients.** For a member `p` of the
family and a coefficient map `φ` into an additively torsion-free ring, the principal subresultant
coefficients of `p.map φ` and its derivative at their actual degrees are images of elements of the
Collins projection. Torsion-freeness ensures that the specialized derivative has the expected
degree; in positive characteristic the derivative of a reductum can drop further in degree under
specialization. -/
theorem psc_map_derivative_mem_image_collinsProjection [HasUniqueDiv S] [DecidableEq S]
    (φ : R →+* S) {F : Finset R[X]} {p : R[X]} (hp : p ∈ F) {j : ℕ}
    (hj : j ≤ min (p.map φ).natDegree (p.map φ).derivative.natDegree) :
    psc (p.map φ) (p.map φ).derivative (p.map φ).natDegree (p.map φ).derivative.natDegree j ∈
      F.collinsProjection.image φ := by
  first
  | set r := p.reductum ((p.map φ).natDegree + 1)
    have hmap : r.map φ = p.map φ := map_reductum_natDegree_map_add_one φ p
    have hr : r.natDegree = (p.map φ).natDegree := natDegree_reductum_natDegree_map_add_one φ p
    have hr' : r.derivative.natDegree = (p.map φ).derivative.natDegree := by
      rw [← hmap, derivative_map,
        natDegree_map_derivative_eq_of_natDegree_map_eq (by rw [hmap, hr])]
    refine mem_image.2 ⟨_, psc_derivative_mem_collinsProjection hp (p.reductum_mem_reducta _)
      (j := j) (by rwa [hr, hr']), ?_⟩
    rw [← psc_map_map, ← derivative_map, hmap, hr, hr']

/-! ### Invariance of the specialized family

Throughout, `φ` and `ψ` are two specializations under which the same elements of the Collins
projection vanish. Nullification and degree invariance allow arbitrary semiring targets. The zero
patterns of pairwise principal subresultant coefficients agree for commutative-ring targets,
with additively torsion-free targets required for the derivative case. Pairwise gcd degrees agree
for field targets, and gcd degrees with derivatives agree for additively torsion-free field
targets. Root-count invariance requires characteristic-zero fields and splitting of the member
under both specializations; the algebraically closed case follows. -/

section Invariance

section

variable {A B : Type*} [Semiring A] [Semiring B] {φ : R →+* A} {ψ : R →+* B} {F : Finset R[X]}
  {p q : R[X]}

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then a member of the
family is nullified by `φ` exactly when it is nullified by `ψ`. -/
theorem map_eq_zero_iff_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    p.map φ = 0 ↔ p.map ψ = 0 :=
  map_eq_zero_iff_of_map_coeff_eq_zero_iff fun _ hi ↦
    h _ (coeff_mem_collinsProjection hp p.self_mem_reducta hi)

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then every member of
the family has the same degree after either specialization. -/
theorem natDegree_map_eq_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    (p.map φ).natDegree = (p.map ψ).natDegree :=
  natDegree_map_eq_of_map_coeff_eq_zero_iff fun _ hi ↦
    h _ (coeff_mem_collinsProjection hp p.self_mem_reducta hi)

/-- A single reductum of a member of the family specializes to the member under both `φ` and `ψ`,
and its own degree is the specialized degree under each of them. -/
private theorem exists_mem_reducta_map_eq_and_map_eq
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    ∃ r ∈ p.reducta, r.natDegree = (p.map φ).natDegree ∧ r.natDegree = (p.map ψ).natDegree ∧
      r.map φ = p.map φ ∧ r.map ψ = p.map ψ := by
  first
  | have hdeg := natDegree_map_eq_of_collinsProjection h hp
    refine ⟨_, p.reductum_mem_reducta _, natDegree_reductum_natDegree_map_add_one φ p, ?_,
      map_reductum_natDegree_map_add_one φ p, ?_⟩ <;> rw [hdeg]
    exacts [natDegree_reductum_natDegree_map_add_one ψ p, map_reductum_natDegree_map_add_one ψ p]

end

variable {A B : Type*} [CommRing A] [CommRing B] {φ : R →+* A} {ψ : R →+* B} {F : Finset R[X]}
  {p q : R[X]}

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for two members
of the family the principal subresultant coefficients of their specializations, at the
specialized degrees, vanish at the same indices. -/
theorem psc_map_eq_zero_iff_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) (hq : q ∈ F) {j : ℕ}
    (hj : j ≤ min (p.map φ).natDegree (q.map φ).natDegree) :
    psc (p.map φ) (q.map φ) (p.map φ).natDegree (q.map φ).natDegree j = 0 ↔
      psc (p.map ψ) (q.map ψ) (p.map ψ).natDegree (q.map ψ).natDegree j = 0 := by
  first
  | obtain ⟨r, hrT, hrφd, hrψd, hrφ, hrψ⟩ := exists_mem_reducta_map_eq_and_map_eq h hp
    obtain ⟨s, hsT, hsφd, hsψd, hsφ, hsψ⟩ := exists_mem_reducta_map_eq_and_map_eq h hq
    have hc := psc_mem_collinsProjection hp hrT hq hsT (j := j) (by rwa [hrφd, hsφd])
    -- Both sides are the images under `φ` and `ψ` of the projection element `hc`, since `r` and
    -- `s` specialize to `p` and `q` with the same degrees.
    have eφ : φ (psc r s r.natDegree s.natDegree j) =
        psc (p.map φ) (q.map φ) (p.map φ).natDegree (q.map φ).natDegree j := by
      simp only [← psc_map_map, hrφ, hsφ, hrφd, hsφd]
    have eψ : ψ (psc r s r.natDegree s.natDegree j) =
        psc (p.map ψ) (q.map ψ) (p.map ψ).natDegree (q.map ψ).natDegree j := by
      simp only [← psc_map_map, hrψ, hsψ, hrψd, hsψd]
    rw [← eφ, ← eψ]
    exact h _ hc

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for a member of
the family the principal subresultant coefficients of its specialization and their derivative,
at the specialized degrees, vanish at the same indices. The targets are additively torsion-free,
so that the derivative of a specialization has the expected degree. -/
theorem psc_map_derivative_eq_zero_iff_of_collinsProjection [HasUniqueDiv A]
    [HasUniqueDiv B] (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F)
    {j : ℕ} (hj : j ≤ min (p.map φ).natDegree (p.map φ).derivative.natDegree) :
    psc (p.map φ) (p.map φ).derivative (p.map φ).natDegree (p.map φ).derivative.natDegree j = 0 ↔
      psc (p.map ψ) (p.map ψ).derivative (p.map ψ).natDegree
        (p.map ψ).derivative.natDegree j = 0 := by
  first
  | obtain ⟨r, hrT, hrφd, hrψd, hrφ, hrψ⟩ := exists_mem_reducta_map_eq_and_map_eq h hp
    -- Over torsion-free targets, `r` keeps its derivative degree under both specializations.
    have hrφd' : r.derivative.natDegree = (p.map φ).derivative.natDegree := by
      rw [← hrφ, derivative_map, natDegree_map_derivative_eq_of_natDegree_map_eq (hrφ ▸ hrφd.symm)]
    have hrψd' : r.derivative.natDegree = (p.map ψ).derivative.natDegree := by
      rw [← hrψ, derivative_map, natDegree_map_derivative_eq_of_natDegree_map_eq (hrψ ▸ hrψd.symm)]
    have hc := psc_derivative_mem_collinsProjection hp hrT (j := j) (by rwa [hrφd, hrφd'])
    -- Both sides are the images under `φ` and `ψ` of the projection element `hc`.
    have eφ : φ (psc r r.derivative r.natDegree r.derivative.natDegree j) =
        psc (p.map φ) (p.map φ).derivative (p.map φ).natDegree
          (p.map φ).derivative.natDegree j := by
      simp only [← psc_map_map, ← derivative_map, hrφ, hrφd, hrφd']
    have eψ : ψ (psc r r.derivative r.natDegree r.derivative.natDegree j) =
        psc (p.map ψ) (p.map ψ).derivative (p.map ψ).natDegree
          (p.map ψ).derivative.natDegree j := by
      simp only [← psc_map_map, ← derivative_map, hrψ, hrψd, hrψd']
    rw [← eφ, ← eψ]
    exact h _ hc

end Invariance

section Field

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L] {φ : R →+* K}
  {ψ : R →+* L} {F : Finset R[X]} {p q : R[X]}

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for any two
members of the family the gcds of their specializations have the same degree. -/
theorem natDegree_gcd_map_eq_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) (hq : q ∈ F) :
    (EuclideanDomain.gcd (p.map φ) (q.map φ)).natDegree =
      (EuclideanDomain.gcd (p.map ψ) (q.map ψ)).natDegree := by
  first
  | rcases eq_or_ne (p.map ψ) 0 with hp0 | hp0
    · rw [hp0, (map_eq_zero_iff_of_collinsProjection h hp).2 hp0, EuclideanDomain.gcd_zero_left,
        EuclideanDomain.gcd_zero_left, natDegree_map_eq_of_collinsProjection h hq]
    rcases eq_or_ne (q.map ψ) 0 with hq0 | hq0
    · rw [hq0, (map_eq_zero_iff_of_collinsProjection h hq).2 hq0, EuclideanDomain.gcd_zero_right,
        EuclideanDomain.gcd_zero_right, natDegree_map_eq_of_collinsProjection h hp]
    refine natDegree_gcd_eq_of_psc_eq_zero_iff hp0 hq0 fun j hj => ?_
    refine psc_map_eq_zero_iff_of_collinsProjection h hp hq ?_
    rwa [natDegree_map_eq_of_collinsProjection h hp, natDegree_map_eq_of_collinsProjection h hq]

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for every member
of the family the gcd of its specialization with its derivative has the same degree under both
specializations. The targets are additively torsion-free. -/
theorem natDegree_gcd_map_derivative_eq_of_collinsProjection [HasUniqueDiv K]
    [HasUniqueDiv L]
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    (EuclideanDomain.gcd (p.map φ) (p.map φ).derivative).natDegree =
      (EuclideanDomain.gcd (p.map ψ) (p.map ψ).derivative).natDegree := by
  first
  | have hdeg := natDegree_map_eq_of_collinsProjection h hp
    rcases eq_or_ne (p.map ψ).derivative 0 with h0 | h0
    · have h0' : (p.map φ).derivative = 0 := by
        rw [derivative_eq_zero, hdeg, ← derivative_eq_zero, h0]
      rw [h0, h0', EuclideanDomain.gcd_zero_right, EuclideanDomain.gcd_zero_right, hdeg]
    have hp0 : p.map ψ ≠ 0 := fun hp0 => h0 (by rw [hp0, derivative_zero])
    refine natDegree_gcd_eq_of_psc_eq_zero_iff hp0 h0 fun j hj => ?_
    refine psc_map_derivative_eq_zero_iff_of_collinsProjection h hp ?_
    rwa [natDegree_derivative, hdeg, ← natDegree_derivative]

/-- If two specializations into characteristic-zero fields nullify the same elements of the
Collins projection and a member splits under both specializations, then it has the same number of
distinct roots after either specialization. The zero polynomial has an empty root multiset by
convention. -/
theorem card_roots_toFinset_map_eq_of_collinsProjection_of_splits [CharZero K] [CharZero L]
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F)
    (hφ : (p.map φ).Splits) (hψ : (p.map ψ).Splits) :
    (p.map φ).roots.toFinset.card = (p.map ψ).roots.toFinset.card := by
  first
  | rcases eq_or_ne (p.map ψ) 0 with h0 | h0
    · simp [h0, (map_eq_zero_iff_of_collinsProjection h hp).2 h0]
    rw [← natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits h0 hψ,
      ← natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits
        ((map_eq_zero_iff_of_collinsProjection h hp).not.2 h0) hφ,
      natDegree_map_eq_of_collinsProjection h hp,
      natDegree_gcd_map_derivative_eq_of_collinsProjection h hp]

/-- If the same elements of the Collins projection vanish under specializations `φ` and `ψ` into
algebraically closed fields of characteristic zero, then every member of the family has the same
number of distinct roots after either specialization. A member nullified by one is nullified by
both, and `Polynomial.roots` of the zero polynomial is empty by convention, so both counts are
then zero. -/
theorem card_roots_toFinset_map_eq_of_collinsProjection [CharZero K] [CharZero L]
    [IsAlgClosed K] [IsAlgClosed L]
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    (p.map φ).roots.toFinset.card = (p.map ψ).roots.toFinset.card :=
  card_roots_toFinset_map_eq_of_collinsProjection_of_splits h hp
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)

end Field

end Finset
end -- closes the original EOF section from source line 90
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Projection/Collins.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Polynomial.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Subresultant polynomials

This file defines the fixed-bound subresultant polynomial of two polynomials.  At a strict index
`j < min m n`, its coefficient of degree `k ≤ j` is the Sylvester minor obtained by replacing the
first row of the principal subresultant matrix at index `j` by the row of coefficients of degree
`k`; in particular, its coefficient of degree `j` is the principal subresultant coefficient.
Outside the strict range the minors remain scalar data (for instance the terminal empty
determinant recorded by `psc`), and the subresultant polynomial is zero.

The construction retains explicit degree bounds, so it commutes with coefficient maps even when
specialization lowers the degrees.  Its degree bound and top coefficient identify the scalar minor
that controls the subresultant gcd criterion.

## Main results

* `Polynomial.subresultantCoeffMatrix_eq_updateRow`: the coefficient matrix replaces the first row
  of the principal matrix.
* `Polynomial.subresultantCoeffMatrix_mulVec`: the coefficient matrix reads the coefficients of
  `A * q + B * p`, with degree `k` in the first row.
* `Polynomial.coeff_subresultant`: at a strict index `j < min m n`, the coefficients are the
  prescribed minors through degree `j`, and vanish above `j`; outside that range they all
  vanish.
* `Polynomial.degree_subresultant_le`: the subresultant polynomial has degree at most
  `j`.
* `Polynomial.subresultant_map_map`: fixed-bound subresultant polynomials commute with
  coefficient maps.
* `Polynomial.subresultant_map_of_natDegree_eq`: at the actual degrees, they commute with
  coefficient maps that preserve both degrees.
* `Polynomial.subresultant_comm`: swapping the inputs gives the Sylvester block-swap
  sign.
* `Polynomial.psc_C_mul_left`, `Polynomial.psc_C_mul_right`: scaling one polynomial by a constant
  scales the principal subresultant coefficient by a power of that constant.
* `Polynomial.subresultant_zero_left`, `Polynomial.subresultant_zero_right`: a zero input gives
  zero subresultant polynomials; the minors with a nonempty column block of the zero input vanish.
* `Polynomial.subresultant_succ_succ_self`: with equal bounds `j + 1`, the subresultant at index
  `j` is `p_{j+1} q - q_{j+1} p`.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4.
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3.
-/

public section

namespace Polynomial

open TauCeti

variable {R S : Type*}

/-- The coefficient matrix whose determinant is the coefficient of degree `k` in the subresultant
polynomial at a strict index `j < min m n` and formal degree bounds `m` and `n`.  The matrix is
defined for all indices; outside the strict range its determinant is only scalar data.

The first row of `subresultantMatrix p q m n j`, which reads coefficients of degree `j`, is
replaced by the row reading coefficients of degree `k`.  Applications use `k ≤ j`. -/
def subresultantCoeffMatrix [Semiring R]
    (p q : R[X]) (m n j k : ℕ) :
    Matrix (Fin ((m - j) + (n - j))) (Fin ((m - j) + (n - j))) R :=
  Matrix.of fun i l =>
    let d := if i.val = 0 then k else i.val + j
    l.addCases
      (fun l => if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0)
      (fun l => if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0)

/-- An entry in the first, `q`-column block of a subresultant coefficient matrix. -/
@[simp]
theorem subresultantCoeffMatrix_castAdd [Semiring R]
    (p q : R[X]) (m n j k : ℕ) (i : Fin ((m - j) + (n - j))) (l : Fin (m - j)) :
    subresultantCoeffMatrix p q m n j k i (Fin.castAdd (n - j) l) =
      let d := if i.val = 0 then k else i.val + j
      if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0 := by
  first
  | simp [subresultantCoeffMatrix]

/-- An entry in the second, `p`-column block of a subresultant coefficient matrix. -/
@[simp]
theorem subresultantCoeffMatrix_natAdd [Semiring R]
    (p q : R[X]) (m n j k : ℕ) (i : Fin ((m - j) + (n - j))) (l : Fin (n - j)) :
    subresultantCoeffMatrix p q m n j k i (Fin.natAdd (m - j) l) =
      let d := if i.val = 0 then k else i.val + j
      if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0 := by
  first
  | simp [subresultantCoeffMatrix]

/-- When the formal bounds dominate the input degrees, coefficient-matrix entries are
coefficients of shifted input polynomials, including the replaced first row. -/
theorem subresultantCoeffMatrix_apply_eq_coeff [Semiring R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (j k : ℕ) (i l : Fin ((m - j) + (n - j))) :
    subresultantCoeffMatrix p q m n j k i l =
      l.addCases
        (fun l => (X ^ l.val * q).coeff (if i.val = 0 then k else i.val + j))
        (fun l => (X ^ l.val * p).coeff (if i.val = 0 then k else i.val + j)) := by
  first
  | induction l using Fin.addCases <;>
      simp [subresultantCoeffMatrix, coeff_X_pow_mul_of_natDegree_le hm,
        coeff_X_pow_mul_of_natDegree_le hn]

/-- A subresultant coefficient matrix replaces the row of degree `j` of the principal
matrix by the row of degree `k`. -/
theorem subresultantCoeffMatrix_eq_updateRow [Semiring R]
    (p q : R[X]) (m n j k : ℕ)
    (i₀ : Fin ((m - j) + (n - j))) (hi₀ : i₀.val = 0) :
    subresultantCoeffMatrix p q m n j k =
      (subresultantMatrix p q m n j).updateRow i₀
        (subresultantCoeffMatrix p q m n j k i₀) := by
  first
  | ext i l
    by_cases hi : i = i₀
    · subst i
      simp
    · have hi' : i.val ≠ 0 := fun h => hi (Fin.ext (h.trans hi₀.symm))
      induction l using Fin.addCases <;> simp [Matrix.updateRow_apply, hi, hi']

/-- A subresultant coefficient matrix reads coefficients of `A * q + B * p` from the
coefficient vector of `(A, B)`. Its first row reads degree `k`; the other rows read degrees
`i.val + j`. The formal bounds dominate the actual input degrees. -/
theorem subresultantCoeffMatrix_mulVec [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j k : ℕ)
    (v : Fin ((m - j) + (n - j)) → R) (i : Fin ((m - j) + (n - j))) :
    (subresultantCoeffMatrix p q m n j k).mulVec v i =
      (ofFn (m - j) (fun l => v (Fin.castAdd (n - j) l)) * q +
        ofFn (n - j) (fun l => v (Fin.natAdd (m - j) l)) * p).coeff
        (if i.val = 0 then k else i.val + j) :=
  coefficientRow_dotProduct hm hn (m - j) (n - j) (if i.val = 0 then k else i.val + j) v

/-- At `k = j`, the coefficient matrix is the principal subresultant matrix. -/
@[simp]
theorem subresultantCoeffMatrix_self [Semiring R]
    (p q : R[X]) (m n j : ℕ) :
    subresultantCoeffMatrix p q m n j j = subresultantMatrix p q m n j := by
  first
  | ext i l
    induction l using Fin.addCases <;> by_cases hi : i.val = 0 <;> simp [hi]

/-- Mapping coefficients maps every entry of a fixed-bound subresultant coefficient matrix. -/
@[simp]
theorem subresultantCoeffMatrix_map_map [Semiring R] [Semiring S]
    (f : R →+* S) (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeffMatrix (p.map f) (q.map f) m n j k =
      f.mapMatrix (subresultantCoeffMatrix p q m n j k) := by
  first
  | ext i l
    induction l using Fin.addCases <;>
      simp [subresultantCoeffMatrix, apply_ite f]

/-- Swapping the polynomials and bounds swaps the column blocks of every subresultant coefficient
matrix. -/
theorem subresultantCoeffMatrix_comm [Semiring R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeffMatrix p q m n j k =
      (subresultantCoeffMatrix q p n m j k).reindex
        (finCongr (add_comm (n - j) (m - j))) finAddFlip := by
  first
  | ext i l
    induction l using Fin.addCases <;> simp [subresultantCoeffMatrix, finAddFlip]

/-- The scalar minor used as the coefficient of degree `k ≤ j` in the subresultant polynomial at
a strict index `j < min m n`.  It is defined for all indices; outside the strict range it is
scalar data only (the subresultant polynomial is then zero), e.g. the empty determinant `1` at
`m = n = j = 0`. -/
def subresultantCoeff [CommRing R]
    (p q : R[X]) (m n j k : ℕ) : R :=
  (subresultantCoeffMatrix p q m n j k).det

/-- A subresultant coefficient is the determinant of its coefficient matrix. -/
theorem subresultantCoeff_def [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff p q m n j k = (subresultantCoeffMatrix p q m n j k).det := by
  first
  | rw [subresultantCoeff]

/-- At the smaller right terminal index, a coefficient minor reads a coefficient of the right
input times a power of its coefficient at the bound. The empty determinant is excluded. -/
theorem subresultantCoeff_right_bound [CommRing R] (p q : R[X]) {m n k : ℕ}
    (hnm : n < m) (hk : k ≤ n) :
    subresultantCoeff p q m n n k = q.coeff k * q.coeff n ^ (m - n - 1) := by
  first
  | let i₀ : Fin ((m - n) + (n - n)) := ⟨0, by omega⟩
    have htri : (subresultantCoeffMatrix p q m n n k).IsUpperTriangular := by
      intro i l hli
      induction l using Fin.addCases with
      | left l =>
        have : l.val < i.val := hli
        simp [show i.val ≠ 0 by omega, show ¬ i.val + n ≤ l.val + n by omega]
      | right l => exact Fin.elim0 (Fin.cast (by simp) l)
    have hdiag (i : Fin ((m - n) + (n - n))) : subresultantCoeffMatrix p q m n n k i i =
        if i = i₀ then q.coeff k else q.coeff n := by
      induction i using Fin.addCases with
      | left i => by_cases hi : i.val = 0 <;> simp [i₀, Fin.ext_iff, hi, hk]
      | right i => exact Fin.elim0 (Fin.cast (by simp) i)
    rw [subresultantCoeff_def, Matrix.det_of_isUpperTriangular htri]
    simp [hdiag, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', Finset.card_erase_of_mem]

/-- The coefficient minor at `k = j` is the principal subresultant coefficient. -/
@[simp]
theorem subresultantCoeff_self [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    subresultantCoeff p q m n j j = psc p q m n j := by
  first
  | simp [subresultantCoeff_def, psc_def]

/-- Subresultant coefficient minors commute with coefficient maps at fixed bounds. -/
@[simp]
theorem subresultantCoeff_map_map [CommRing R] [CommRing S]
    (f : R →+* S) (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff (p.map f) (q.map f) m n j k =
      f (subresultantCoeff p q m n j k) := by
  first
  | simp [subresultantCoeff_def, RingHom.map_det]

/-- At the actual degrees, subresultant coefficient minors commute with a coefficient map that
preserves both degrees. -/
theorem subresultantCoeff_map_of_natDegree_eq [CommRing R] [CommRing S] (f : R →+* S)
    {p q : R[X]} (hp : (p.map f).natDegree = p.natDegree) (hq : (q.map f).natDegree = q.natDegree)
    (j k : ℕ) :
    subresultantCoeff (p.map f) (q.map f) (p.map f).natDegree (q.map f).natDegree j k =
      f (subresultantCoeff p q p.natDegree q.natDegree j k) := by
  first
  | rw [hp, hq, subresultantCoeff_map_map]

/-- Swapping the inputs changes every coefficient minor by the Sylvester block-swap sign. -/
theorem subresultantCoeff_comm [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff p q m n j k =
      (-1) ^ ((m - j) * (n - j)) * subresultantCoeff q p n m j k := by
  first
  | rw [subresultantCoeff_def, subresultantCoeff_def, subresultantCoeffMatrix_comm,
      Matrix.det_reindex, finCongr_symm, sign_finAddFlip_trans_finCongr, mul_comm (n - j)]
    simp

/-- At the smaller left terminal index, a coefficient minor reads a coefficient of the left
input times a power of its coefficient at the bound. The empty determinant is excluded. -/
theorem subresultantCoeff_left_bound [CommRing R] (p q : R[X]) {m n k : ℕ}
    (hmn : m < n) (hk : k ≤ m) :
    subresultantCoeff p q m n m k = p.coeff k * p.coeff m ^ (n - m - 1) := by
  first
  | rw [subresultantCoeff_comm, subresultantCoeff_right_bound q p hmn hk]
    simp

/-- Scaling the left polynomial by `r` scales every coefficient minor by `r ^ (n - j)`. -/
theorem subresultantCoeff_C_mul_left [CommRing R]
    (p q : R[X]) (r : R) (m n j k : ℕ) :
    subresultantCoeff (C r * p) q m n j k =
      r ^ (n - j) * subresultantCoeff p q m n j k := by
  first
  | have hmatrix : subresultantCoeffMatrix (C r * p) q m n j k = .of fun i l =>
        Fin.addCases (fun _ => 1) (fun _ => r) l * subresultantCoeffMatrix p q m n j k i l := by
      ext i l
      induction l using Fin.addCases <;> simp [subresultantCoeffMatrix, coeff_C_mul]
    rw [subresultantCoeff_def, subresultantCoeff_def, hmatrix, Matrix.det_mul_row,
      Fin.prod_univ_add]
    simp

/-- Scaling the right polynomial by `r` scales every coefficient minor by `r ^ (m - j)`. -/
theorem subresultantCoeff_C_mul_right [CommRing R]
    (p q : R[X]) (r : R) (m n j k : ℕ) :
    subresultantCoeff p (C r * q) m n j k =
      r ^ (m - j) * subresultantCoeff p q m n j k := by
  first
  | rw [subresultantCoeff_comm, subresultantCoeff_C_mul_left, mul_left_comm,
      ← subresultantCoeff_comm]

/-- Scaling the left polynomial by a constant `r` scales the principal subresultant coefficient by
`r ^ (n - j)`, where `n - j` counts the columns of the principal subresultant matrix that read
shifts of the left polynomial. At index `0` it recovers `Polynomial.resultant_C_mul_left`. -/
theorem psc_C_mul_left [CommRing R] (p q : R[X]) (r : R) (m n j : ℕ) :
    psc (C r * p) q m n j = r ^ (n - j) * psc p q m n j := by
  first
  | simpa using subresultantCoeff_C_mul_left p q r m n j j

/-- Scaling the right polynomial by a constant `r` scales the principal subresultant coefficient by
`r ^ (m - j)`, where `m - j` counts the columns of the principal subresultant matrix that read
shifts of the right polynomial. At index `0` it recovers `Polynomial.resultant_C_mul_right`. -/
theorem psc_C_mul_right [CommRing R] (p q : R[X]) (r : R) (m n j : ℕ) :
    psc p (C r * q) m n j = r ^ (m - j) * psc p q m n j := by
  first
  | simpa using subresultantCoeff_C_mul_right p q r m n j j

/-- The fixed-bound subresultant polynomial at index `j`.

Its coefficient of degree `k ≤ j` is `subresultantCoeff p q m n j k`; all coefficients above
`j` vanish.  This definition is the subresultant polynomial only at strict indices
`j < min m n` and returns zero outside that range; terminal data, including the empty
determinant, is represented by `psc` instead. -/
noncomputable def subresultant [CommRing R]
    (p q : R[X]) (m n j : ℕ) : R[X] := by
  first
  | classical
    exact if j < min m n then
        ofFn (j + 1) fun k => subresultantCoeff p q m n j k
      else 0

/-- The coefficient formula for a fixed-bound subresultant polynomial. -/
@[simp]
theorem coeff_subresultant [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    (subresultant p q m n j).coeff k =
      if j < min m n ∧ k ≤ j then subresultantCoeff p q m n j k else 0 := by
  first
  | by_cases hj : j < min m n
    · by_cases hkj : k ≤ j
      · simp [subresultant, hj, hkj]
      · have hk : j + 1 ≤ k := by omega
        simp [subresultant, hj, hkj, hk]
    · simp [subresultant, hj]

/-- `subresultant` returns zero at and beyond the terminal index `min m n`. -/
@[simp]
theorem subresultant_eq_zero_of_min_le [CommRing R]
    (p q : R[X]) (m n j : ℕ) (hj : min m n ≤ j) :
    subresultant p q m n j = 0 := by
  first
  | simp [subresultant, Nat.not_lt.mpr hj]

/-- When both formal bounds are positive, the subresultant polynomial at index zero is the
constant resultant. -/
@[simp]
theorem subresultant_zero [CommRing R]
    (p q : R[X]) (m n : ℕ) (h : 0 < min m n) :
    subresultant p q m n 0 = C (Polynomial.resultant p q m n) := by
  first
  | ext k
    by_cases hk : k = 0
    · subst k
      simp [h]
    · rw [coeff_C_of_ne_zero hk]
      simp [h, hk]

/-- The subresultant polynomial at index `j` has degree at most `j`. -/
theorem degree_subresultant_le [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    (subresultant p q m n j).degree ≤ j := by
  first
  | rw [degree_le_iff_coeff_zero]
    intro k hk
    simp [show ¬ k ≤ j by exact_mod_cast hk.not_ge]

/-- At a strict index `j < min m n`, the subresultant polynomial has degree exactly `j`
precisely when its principal coefficient does not vanish. -/
theorem degree_subresultant_eq_iff [CommRing R]
    (p q : R[X]) (m n j : ℕ) (hj : j < min m n) :
    (subresultant p q m n j).degree = j ↔ psc p q m n j ≠ 0 := by
  first
  | constructor
    · intro h
      simpa [hj] using coeff_ne_zero_of_eq_degree h
    · intro h
      apply degree_eq_of_le_of_coeff_ne_zero (degree_subresultant_le ..)
      simpa [hj]

/-- Fixed-bound subresultant polynomials commute with coefficient maps.  No degree-preservation
hypothesis is required. -/
@[simp]
theorem subresultant_map_map [CommRing R] [CommRing S]
    (f : R →+* S) (p q : R[X]) (m n j : ℕ) :
    subresultant (p.map f) (q.map f) m n j =
      (subresultant p q m n j).map f := by
  first
  | ext k
    by_cases hj : j < min m n <;> by_cases hkj : k ≤ j <;> simp [hj, hkj]

/-- At the actual degrees, subresultant polynomials commute with a coefficient map that preserves
both degrees, for instance one that does not kill the leading coefficients
(`Polynomial.natDegree_map_of_leadingCoeff_ne_zero`). When a degree drops, the degree-drop formulas
`Polynomial.map_subresultant_of_right_degree_drop` and
`Polynomial.map_subresultant_of_left_degree_drop` apply instead. -/
theorem subresultant_map_of_natDegree_eq [CommRing R] [CommRing S] (f : R →+* S)
    {p q : R[X]} (hp : (p.map f).natDegree = p.natDegree) (hq : (q.map f).natDegree = q.natDegree)
    (j : ℕ) :
    subresultant (p.map f) (q.map f) (p.map f).natDegree (q.map f).natDegree j =
      (subresultant p q p.natDegree q.natDegree j).map f := by
  first
  | rw [hp, hq, subresultant_map_map]

/-- Scaling the left input by `r` scales its subresultant polynomial at index `j` by
`r ^ (n - j)`. -/
theorem subresultant_C_mul_left [CommRing R]
    (p q : R[X]) (r : R) (m n j : ℕ) :
    subresultant (C r * p) q m n j = C (r ^ (n - j)) * subresultant p q m n j := by
  first
  | ext k
    rw [coeff_C_mul]
    by_cases hj : j < min m n <;> by_cases hkj : k ≤ j <;>
      simp [hj, hkj, subresultantCoeff_C_mul_left]

/-- Scaling the right input by `r` scales its subresultant polynomial at index `j` by
`r ^ (m - j)`. -/
theorem subresultant_C_mul_right [CommRing R]
    (p q : R[X]) (r : R) (m n j : ℕ) :
    subresultant p (C r * q) m n j = C (r ^ (m - j)) * subresultant p q m n j := by
  first
  | ext k
    rw [coeff_C_mul]
    by_cases hj : j < min m n <;> by_cases hkj : k ≤ j <;>
      simp [hj, hkj, subresultantCoeff_C_mul_right]

/-- Swapping the inputs and their bounds changes the subresultant polynomial by the Sylvester
block-swap sign. -/
theorem subresultant_comm [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    subresultant p q m n j =
      C ((-1) ^ ((m - j) * (n - j))) * subresultant q p n m j := by
  first
  | ext k
    rw [coeff_subresultant, coeff_C_mul, coeff_subresultant, min_comm n m, subresultantCoeff_comm,
      mul_ite, mul_zero]

/-! ### Zero inputs -/

/-- A zero left input makes a coefficient minor vanish when its column block, of size `n - j`,
is nonempty. -/
@[simp]
theorem subresultantCoeff_zero_left [CommRing R] (q : R[X]) {m n j : ℕ} (hjn : j < n) (k : ℕ) :
    subresultantCoeff 0 q m n j k = 0 := by
  first
  | simpa [zero_pow (Nat.sub_ne_zero_of_lt hjn)] using
      subresultantCoeff_C_mul_left (0 : R[X]) q 0 m n j k

/-- A zero right input makes a coefficient minor vanish when its column block, of size `m - j`,
is nonempty. -/
@[simp]
theorem subresultantCoeff_zero_right [CommRing R] (p : R[X]) {m n j : ℕ} (hjm : j < m) (k : ℕ) :
    subresultantCoeff p 0 m n j k = 0 := by
  first
  | simpa [zero_pow (Nat.sub_ne_zero_of_lt hjm)] using
      subresultantCoeff_C_mul_right p (0 : R[X]) 0 m n j k

/-- A zero left input makes the principal coefficient vanish below the right bound. At `j = n`
the empty column block gives instead `psc 0 q m n n = q.coeff n ^ (m - n)`
(`Polynomial.psc_right_bound`). -/
@[simp]
theorem psc_zero_left [CommRing R] (q : R[X]) {m n j : ℕ} (hjn : j < n) :
    psc 0 q m n j = 0 := by
  first
  | simpa using subresultantCoeff_zero_left q (m := m) hjn j

/-- A zero right input makes the principal coefficient vanish below the left bound. At `j = m`
the empty column block gives instead `psc p 0 m n m = p.coeff m ^ (n - m)`
(`Polynomial.psc_left_bound`). -/
@[simp]
theorem psc_zero_right [CommRing R] (p : R[X]) {m n j : ℕ} (hjm : j < m) :
    psc p 0 m n j = 0 := by
  first
  | simpa using subresultantCoeff_zero_right p (n := n) hjm j

/-- Every subresultant polynomial with a zero left input vanishes. -/
@[simp]
theorem subresultant_zero_left [CommRing R] (q : R[X]) (m n j : ℕ) :
    subresultant 0 q m n j = 0 := by
  first
  | ext k
    rw [coeff_subresultant, coeff_zero]
    split_ifs with h
    · exact subresultantCoeff_zero_left q (by omega) k
    · rfl

/-- Every subresultant polynomial with a zero right input vanishes. -/
@[simp]
theorem subresultant_zero_right [CommRing R] (p : R[X]) (m n j : ℕ) :
    subresultant p 0 m n j = 0 := by
  first
  | ext k
    rw [coeff_subresultant, coeff_zero]
    split_ifs with h
    · exact subresultantCoeff_zero_right p (by omega) k
    · rfl

/-! ### Equal degree bounds -/

/-- With equal bounds `j + 1`, the coefficient minors at index `j` are the `2 × 2`
determinants `p_{j+1} q_k - q_{j+1} p_k`. -/
theorem subresultantCoeff_succ_succ_self [CommRing R] (p q : R[X]) {j k : ℕ} (hk : k ≤ j + 1) :
    subresultantCoeff p q (j + 1) (j + 1) j k =
      p.coeff (j + 1) * q.coeff k - q.coeff (j + 1) * p.coeff k := by
  first
  | have h1 : j + 1 - j = 1 := by omega
    let e : Fin ((j + 1 - j) + (j + 1 - j)) ≃ Fin 2 := finCongr (by omega)
    have hq : (e.symm 0 : Fin _) = Fin.castAdd (j + 1 - j) ⟨0, by omega⟩ := Fin.ext (by simp [e])
    have hp : (e.symm 1 : Fin _) = Fin.natAdd (j + 1 - j) ⟨0, by omega⟩ :=
      Fin.ext (by simp [e, h1])
    rw [subresultantCoeff_def, ← Matrix.det_submatrix_equiv_self e.symm, Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, hq, hp, subresultantCoeffMatrix_castAdd,
      subresultantCoeffMatrix_natAdd, Fin.val_castAdd, Fin.val_natAdd]
    simp [hk, mul_comm, add_comm 1 j]

/-- With equal bounds `j + 1`, the principal coefficient at index `j` is
`p_{j+1} q_j - q_{j+1} p_j`. -/
theorem psc_succ_succ_self [CommRing R] (p q : R[X]) (j : ℕ) :
    psc p q (j + 1) (j + 1) j = p.coeff (j + 1) * q.coeff j - q.coeff (j + 1) * p.coeff j := by
  first
  | simpa using subresultantCoeff_succ_succ_self p q (Nat.le_succ j)

/-- **Equal degrees.** With equal bounds `j + 1` dominating both degrees, the subresultant
polynomial at index `j` is `p_{j+1} q - q_{j+1} p`, the first step of a pseudo-division of
polynomials of the same degree. -/
theorem subresultant_succ_succ_self [CommRing R] {p q : R[X]} {j : ℕ}
    (hp : p.natDegree ≤ j + 1) (hq : q.natDegree ≤ j + 1) :
    subresultant p q (j + 1) (j + 1) j = C (p.coeff (j + 1)) * q - C (q.coeff (j + 1)) * p := by
  first
  | ext k
    rw [coeff_subresultant, coeff_sub, coeff_C_mul, coeff_C_mul]
    by_cases hk : k ≤ j
    · simp only [min_self, Nat.lt_succ_self j, hk, and_self, ↓reduceIte]
      exact subresultantCoeff_succ_succ_self p q (by omega)
    · simp only [hk, and_false, ↓reduceIte]
      obtain rfl | hk' : k = j + 1 ∨ j + 1 < k := by omega
      · ring
      · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hk'),
          coeff_eq_zero_of_natDegree_lt (hq.trans_lt hk')]
        ring

end Polynomial

end -- closes the original EOF section from source line 57
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Polynomial.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Bezout.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Bézout identities for subresultant polynomials

At every index, the fixed-bound subresultant polynomial is a combination
`A * q + B * p`, where `A` and `B` have degrees below `m - j` and `n - j`, respectively.
Outside the strict range `j < min m n`, the subresultant is zero and both coefficients can be
chosen zero.
The identity holds over any commutative ring, including rings with zero divisors, and allows the
actual degrees of the inputs to be smaller than their formal bounds. Consequently every common
divisor of the inputs divides the subresultant polynomial.

These identities place subresultants in the ideal generated by the inputs and allow common
factors to be tracked through the subresultant family. No invertibility or nonvanishing of a
principal subresultant coefficient is required.

## Main results

* `TauCeti.exists_mul_add_mul_eq_subresultant`: the Bézout identity with strict degree bounds.
* `TauCeti.dvd_subresultant`: every common divisor divides the fixed-bound subresultant.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4: the determinant construction of subresultant Bézout identities.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R]

-- Cramer's rule reads a replaced-row determinant against the first adjugate column.
private theorem subresultantCoeff_eq_coeff_adjugate [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j k : ℕ)
    (i₀ : Fin ((m - j) + (n - j))) (hi₀ : i₀.val = 0) :
    subresultantCoeff p q m n j k =
      (ofFn (m - j) (fun l => (subresultantMatrix p q m n j).adjugate
          (Fin.castAdd (n - j) l) i₀) * q +
        ofFn (n - j) (fun l => (subresultantMatrix p q m n j).adjugate
          (Fin.natAdd (m - j) l) i₀) * p).coeff k := by
  first
  | classical
    have hrow := subresultantCoeffMatrix_mulVec hm hn j k
      (fun l => (subresultantMatrix p q m n j).adjugate l i₀) i₀
    simp only [hi₀, ↓reduceIte] at hrow
    rw [subresultantCoeff_def, Polynomial.subresultantCoeffMatrix_eq_updateRow p q m n j k i₀ hi₀,
      ← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose, ← hrow]
    exact dotProduct_comm _ _

/-- At every index, a subresultant polynomial is a Bézout combination of its inputs.
The coefficients of `q` and `p` have degrees strictly below `m - j` and `n - j`, respectively.
The formal bounds may exceed the actual degrees, and neither input nor the subresultant is
required to be nonzero. Outside the strict range, both Bézout coefficients can be zero. -/
theorem exists_mul_add_mul_eq_subresultant {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) :
    ∃ A B : R[X], A.degree < (m - j : ℕ) ∧ B.degree < (n - j : ℕ) ∧
      A * q + B * p = subresultant p q m n j := by
  first
  | classical
    by_cases hj : j < min m n
    · let i₀ : Fin ((m - j) + (n - j)) := ⟨0, by omega⟩
      let M := subresultantMatrix p q m n j
      let v : Fin ((m - j) + (n - j)) → R := fun l => M.adjugate l i₀
      let A := ofFn (m - j) (fun l => v (Fin.castAdd (n - j) l))
      let B := ofFn (n - j) (fun l => v (Fin.natAdd (m - j) l))
      have hA : A.degree < (m - j : ℕ) := ofFn_degree_lt _
      have hB : B.degree < (n - j : ℕ) := ofFn_degree_lt _
      -- The product degree bound handles coefficients beyond the matrix's coefficient window.
      have hdeg := degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le
        hm hn (by omega : j ≤ m) (by omega : j ≤ n) hA hB
      -- The first adjugate column maps to a vector supported in the first row only.
      have hMv (i : Fin ((m - j) + (n - j))) :
          M.mulVec v i = if i = i₀ then M.det else 0 := by
        have h : M.mulVec v = M.det • Pi.single i₀ 1 := by
          -- `v` is definitionally this adjugate column; expose it for `Matrix.mulVec_single_one`.
          change M.mulVec (M.adjugate.col i₀) = _
          rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
            Matrix.smul_mulVec, Matrix.one_mulVec]
        simpa [Pi.smul_apply, Pi.single_apply, eq_comm] using congrFun h i
      refine ⟨A, B, hA, hB, ?_⟩
      ext k
      rw [coeff_subresultant]
      by_cases hk : k ≤ j
      · rw [ite_eq_left ⟨hj, hk⟩]
        exact (subresultantCoeff_eq_coeff_adjugate hm hn j k i₀ rfl).symm
      · rw [ite_eq_right (by simp [hk])]
        by_cases hwin : k < (m - j) + (n - j) + j
        · let i : Fin ((m - j) + (n - j)) := ⟨k - j, by omega⟩
          have hi : i ≠ i₀ := by
            intro h
            have := congrArg Fin.val h
            dsimp [i, i₀] at this
            omega
          have h := subresultantMatrix_mulVec hm hn j v i
          rw [hMv, ite_eq_right hi] at h
          simpa [A, B, i, Nat.sub_add_cancel (by omega : j ≤ k)] using h.symm
        · exact coeff_eq_zero_of_degree_lt (hdeg.trans_le
            (WithBot.coe_le_coe.mpr (by omega : (m - j) + (n - j) + j ≤ k)))
    · refine ⟨0, 0, ?_, ?_, ?_⟩
      · simp
      · simp
      · rw [subresultant_eq_zero_of_min_le _ _ _ _ _ (by omega)]
        simp

/-- Every common divisor of the inputs divides their fixed-bound subresultant polynomial.
This also covers indices outside the strict range, where the subresultant polynomial is zero. -/
theorem dvd_subresultant {p q d : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hp : d ∣ p) (hq : d ∣ q) :
    d ∣ subresultant p q m n j := by
  first
  | obtain ⟨A, B, _, _, h⟩ := exists_mul_add_mul_eq_subresultant hm hn
    rw [← h]
    exact dvd_add (dvd_mul_of_dvd_right hq A) (dvd_mul_of_dvd_right hp B)

end TauCeti
end -- closes the original EOF section from source line 38
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Bezout.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/FirstNonzero.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The first nonzero subresultant polynomial

Subresultant polynomials vanish below the degree of any common divisor. At the degree of a
monic common divisor, the subresultant is that divisor multiplied by its principal coefficient.
Over a field, the first nonzero subresultant polynomial therefore recovers the monic gcd, with
its scalar fixed by the determinant convention. This identifies the terminal polynomial in
comparisons of subresultants with Euclidean remainder sequences.

The polynomial identification requires a strict index: when the gcd degree equals the smaller
input degree, the terminal principal coefficient is scalar data, not a subresultant polynomial.
Formal degree bounds are retained throughout; the nonvanishing assertion uses an actual left
degree and a right degree bound, as in the principal-coefficient gcd criterion.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4, Proposition 4.25 and Corollary 4.26 (subresultants and the gcd).
-/

public section

namespace TauCeti

open Polynomial

section Domain

variable {R : Type*} [CommRing R]

/-- Subresultant polynomials vanish below the degree of any common divisor, even when their
formal degree bounds exceed the input degrees. -/
theorem _root_.Polynomial.subresultant_eq_zero_of_lt_natDegree_commonDivisor
    [IsDomain R] {p q g : R[X]} {m n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hgp : g ∣ p) (hgq : g ∣ q) (hj : j < g.natDegree) :
    subresultant p q m n j = 0 := by
  first
  | have hg : g ≠ 0 := by
      intro h
      simp [h] at hj
    apply eq_zero_of_dvd_of_degree_lt (dvd_subresultant hm hn hgp hgq)
    exact (degree_subresultant_le p q m n j).trans_lt (by
      rw [degree_eq_natDegree hg]
      exact WithBot.coe_lt_coe.mpr hj)

/-- At the degree of a monic common divisor, a strict-index subresultant polynomial is exactly
that divisor scaled by the principal subresultant coefficient. The scalar is allowed to vanish.
No field hypothesis or actual-degree equality is required. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_of_monic_commonDivisor
    {p q g : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hg : g.Monic) (hgp : g ∣ p) (hgq : g ∣ q) (hj : g.natDegree < min m n) :
    subresultant p q m n g.natDegree = C (psc p q m n g.natDegree) * g := by
  first
  | let s := subresultant p q m n g.natDegree
    have hs : s = C s.leadingCoeff * g :=
      eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hg
        (dvd_subresultant hm hn hgp hgq)
        (natDegree_le_of_degree_le (degree_subresultant_le p q m n g.natDegree))
    have hcoeff := congrArg (fun r : R[X] => r.coeff g.natDegree) hs
    have hlc : s.leadingCoeff = psc p q m n g.natDegree := by
      simpa only [s, coeff_subresultant, hj, le_refl, and_self, ↓reduceIte,
        subresultantCoeff_self, coeff_C_mul, coeff_natDegree, hg.leadingCoeff, mul_one]
        using hcoeff.symm
    exact hs.trans (by rw [hlc])

end Domain

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- At the gcd degree, a strict-index subresultant is the monic normalization of the Euclidean
gcd scaled by its principal coefficient. This formula also permits oversized formal bounds,
where that coefficient can vanish. -/
theorem _root_.Polynomial.subresultant_natDegree_gcd {p q : K[X]} {m n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hj : (EuclideanDomain.gcd p q).natDegree < min m n) :
    subresultant p q m n (EuclideanDomain.gcd p q).natDegree =
      C (psc p q m n (EuclideanDomain.gcd p q).natDegree) *
        normalize (EuclideanDomain.gcd p q) := by
  first
  | by_cases hg : EuclideanDomain.gcd p q = 0
    · have hs := dvd_subresultant (j := (EuclideanDomain.gcd p q).natDegree) hm hn
        (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q)
      rw [hg, zero_dvd_iff] at hs
      simpa only [hg, normalize_zero, mul_zero] using hs
    simpa only [natDegree_normalize] using
      subresultant_eq_C_mul_of_monic_commonDivisor hm hn (monic_normalize hg)
        (normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left p q))
        (normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right p q))
        (by simpa only [natDegree_normalize] using hj)

/-- With an actual left degree, the subresultant at a strict gcd index is associated to the gcd.
Together with vanishing below that index, this identifies the first nonzero subresultant
polynomial. A right degree bound suffices; neither squarefreeness nor monicity is assumed. -/
theorem _root_.Polynomial.subresultant_natDegree_gcd_associated {p q : K[X]} {m n : ℕ}
    (hm : p.natDegree = m) (hn : q.natDegree ≤ n)
    (hj : (EuclideanDomain.gcd p q).natDegree < min m n) :
    Associated (subresultant p q m n (EuclideanDomain.gcd p q).natDegree)
      (EuclideanDomain.gcd p q) := by
  first
  | have hp : p ≠ 0 := by
      rintro rfl
      simp only [natDegree_zero] at hm
      omega
    rw [subresultant_natDegree_gcd hm.le hn hj]
    have hc : IsUnit (C (psc p q m n (EuclideanDomain.gcd p q).natDegree)) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr (psc_natDegree_gcd_ne_zero hp hm hn))
    exact (associated_unit_mul_left _ _ hc).trans (normalize_associated _)

end Field

end TauCeti
end -- closes the original EOF section from source line 31
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/FirstNonzero.lean -/

/- BEGIN SOURCE: TauCeti/Data/Sym/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic lemmas for symmetric powers

This file records small API extensions for Mathlib's symmetric powers, and the map
`TauCeti.Sym.ofFn` reading an ordered `n`-tuple `f : Fin n → α` as an unordered one.

`ofFn` presents `Sym α n` as a quotient of `Fin n → α`: it is surjective, and its fibres are the
orbits of the permutation action, by `TauCeti.Sym.ofFn_eq_ofFn_iff`. Nothing here is topological;
`TauCeti/Topology/Sym/Basic.lean` uses this to give `Sym α n` the quotient topology coinduced along
`ofFn`.

## Main declarations

* `TauCeti.Sym.ofFn`: the ordered tuple `f : Fin n → α` read as a point of `Sym α n`, and
  `TauCeti.Sym.ofFn_surjective`, that every unordered tuple arises this way.
* `TauCeti.Sym.map_ofFn`, `TauCeti.Sym.map_comp_ofFn` and `TauCeti.Sym.ofFn_fin_append`: `ofFn`
  intertwines postcomposition with `Sym.map`, and concatenation of ordered tuples with
  `Sym.append`.
* `TauCeti.Sym.ofFn_eq_ofFn_iff`: two ordered tuples have the same underlying unordered tuple
  exactly when one is a reindexing of the other by a permutation.
* `TauCeti.Sym.count_coe_ofFn`: the multiplicity of a value in an unordered tuple is the number
  of entries of the ordered tuple taking that value.
* `TauCeti.Sym.basepointDivisor` is the set of unordered tuples containing a fixed point;
  `TauCeti.Sym.range_cons` identifies it with the range of adjoining that point.
* `TauCeti.symFinTwoEquiv`: an unordered `d`-tuple over `Fin 2` is determined by how many of its
  entries are `0`, so there are `d + 1` of them.
-/

public section

namespace Sym

variable {X Y : Type*} {d e : ℕ}

/-- Mapping a function over an appended symmetric-power point is the append of the mapped
symmetric-power points. -/
@[simp]
theorem map_append (f : X → Y) (s : Sym X d) (t : Sym X e) :
    Sym.map f (s.append t) = (Sym.map f s).append (Sym.map f t) :=
  Subtype.ext <| by simp [Multiset.map_add]

end Sym

namespace TauCeti

namespace Sym

variable {α β : Type*} {m n : ℕ}

/-! ### Ordered tuples as unordered ones -/

/-- The ordered `n`-tuple `f : Fin n → α` read as an unordered `n`-tuple.

This is Mathlib's quotient map `Sym.ofVector` precomposed with `List.Vector.ofFn`; the `Fin n → α`
form is the one that carries a product topology, so it is the map that `Sym α n` carries the
quotient topology along in `TauCeti/Topology/Sym/Basic.lean`. -/
def ofFn (f : Fin n → α) : Sym α n :=
  Sym.ofVector (List.Vector.ofFn f)

/-- The multiset underlying `ofFn f` is the list of values of `f`. -/
@[simp]
theorem coe_ofFn (f : Fin n → α) : (ofFn f : Multiset α) = ↑(List.ofFn f) :=
  congrArg _ (List.Vector.toList_ofFn f)

/-- The multiplicity of a value in `ofFn f` is the number of entries of `f` equal to it. -/
theorem count_coe_ofFn [DecidableEq α] (f : Fin n → α) (a : α) :
    Multiset.count a (ofFn f : Multiset α) = (Finset.univ.filter fun i => f i = a).card := by
  first
  | have hmap : (ofFn f : Multiset α) = Multiset.map f Finset.univ.val := by
      simp [List.ofFn_eq_map, Finset.val_univ_fin]
    rw [hmap, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
    simp only [eq_comm]

/-- The points of `ofFn f` are exactly the values of `f`. -/
@[simp]
theorem mem_ofFn {a : α} {f : Fin n → α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  first
  | rw [← _root_.Sym.mem_coe, coe_ofFn]
    simp

/-- Every unordered `n`-tuple is the image of an ordered one: `ofFn` is the quotient map
presenting `Sym α n` as a quotient of `Fin n → α`. -/
theorem ofFn_surjective : Function.Surjective (ofFn : (Fin n → α) → Sym α n) := by
  first
  | rintro ⟨s, hs⟩
    obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
    have hlen : l.length = n := by simpa using hs
    subst hlen
    exact ⟨l.get, Subtype.ext (by simp)⟩

/-- Prepending a point to an ordered tuple adjoins it to the unordered one. -/
@[simp]
theorem ofFn_cons (a : α) (f : Fin n → α) : ofFn (Fin.cons a f) = a ::ₛ ofFn f :=
  Subtype.ext <| by simp [Sym.coe_cons, List.ofFn_succ]

/-- Applying a function to every entry of an ordered tuple applies it to every point of the
unordered one. -/
@[simp]
theorem map_ofFn (f : α → β) (g : Fin n → α) : Sym.map f (ofFn g) = ofFn (f ∘ g) :=
  Sym.coe_injective <| by simp [Sym.coe_map]

/-- The compatibility of `Sym.map` with `ofFn`, as an equality of maps out of ordered tuples. -/
theorem map_comp_ofFn (f : α → β) :
    (Sym.map f : Sym α n → Sym β n) ∘ ofFn = ofFn ∘ Pi.map fun _ : Fin n => f := by
  first
  | funext g
    simp only [Function.comp_apply, map_ofFn]
    exact congrArg ofFn (funext fun _ => rfl)

/-- The range of the map on symmetric powers consists of the unordered tuples whose every point
lies in the range of the original map. -/
theorem mem_range_map (f : α → β) {w : Sym β n} :
    w ∈ Set.range (Sym.map f) ↔ ∀ b ∈ w, b ∈ Set.range f := by
  first
  | constructor
    · rintro ⟨s, rfl⟩ b hb
      rw [← _root_.Sym.mem_coe, Sym.coe_map] at hb
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hb
      exact Set.mem_range_self a
    · intro hw
      let g : {b // b ∈ w} → α := fun b => (hw b b.2).choose
      have hg : ∀ b : {b // b ∈ w}, f (g b) = b := fun b => (hw b b.2).choose_spec
      refine ⟨Sym.map g w.attach, ?_⟩
      rw [Sym.map_map]
      convert w.attach_map_coe using 1
      exact congrArg (fun h => Sym.map h w.attach) (funext hg)

/-- Concatenating two ordered tuples adjoins the two unordered ones. -/
@[simp]
theorem ofFn_fin_append (f : Fin m → α) (g : Fin n → α) :
    ofFn (Fin.append f g) = (ofFn f).append (ofFn g) :=
  Sym.coe_injective <| by simp [Sym.coe_append, List.ofFn_fin_append]

/-! ### The fibres of the quotient map -/

/-- Reindexing an ordered tuple by a permutation leaves the underlying unordered tuple unchanged. -/
theorem ofFn_comp_perm (σ : Equiv.Perm (Fin n)) (f : Fin n → α) : ofFn (f ∘ σ) = ofFn f :=
  Sym.coe_injective <| by simpa using Multiset.coe_eq_coe.2 (σ.ofFn_comp_perm f)

/-- Two ordered tuples have the same underlying unordered tuple exactly when one is a reindexing
of the other: the fibres of `ofFn` are the orbits of the permutation action. -/
theorem ofFn_eq_ofFn_iff {f g : Fin n → α} :
    ofFn f = ofFn g ↔ ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  first
  | classical
    refine ⟨fun h => ?_, ?_⟩
    · -- the two tuples take each value the same number of times, so their fibres are equinumerous
      have hcard : ∀ c : α, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := fun c => by
        rw [Fintype.card_subtype, Fintype.card_subtype, ← count_coe_ofFn g c, ← count_coe_ofFn f c, h]
      exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
        funext fun i => Equiv.ofFiberEquiv_map _ i⟩
    · rintro ⟨σ, rfl⟩
      exact (ofFn_comp_perm σ f).symm

/-! ### Adjoining a fixed point -/

/-- The divisor of unordered tuples containing the fixed point `a`. -/
def basepointDivisor (a : α) : Set (Sym α n) := {s | a ∈ s}

@[simp]
theorem mem_basepointDivisor {a : α} {s : Sym α n} :
    s ∈ basepointDivisor a ↔ a ∈ s := Iff.rfl

/-- No unordered tuple of length zero contains a point. -/
@[simp]
theorem basepointDivisor_zero (a : α) : (basepointDivisor a : Set (Sym α 0)) = ∅ :=
  Set.eq_empty_of_forall_notMem fun s => by simp [_root_.Sym.eq_nil_of_card_zero s]

/-- The unordered `(n + 1)`-tuples obtained by adjoining the point `a` are exactly those that
contain `a`. -/
@[simp]
theorem range_cons (a : α) :
    Set.range (Sym.cons a : Sym α n → Sym α (n + 1)) = basepointDivisor a := by
  first
  | ext s
    refine ⟨?_, fun hs => ?_⟩
    · rintro ⟨t, rfl⟩
      exact Sym.mem_cons_self a t
    · obtain ⟨t, rfl⟩ := Sym.exists_cons_of_mem hs
      exact ⟨t, rfl⟩

end Sym

/-! ### Unordered tuples over a two-element type -/

/-- **A multiset of size `d` over `Fin 2` is determined by how many of its entries are `0`**, and
that count can be anything from `0` to `d`: the two counts sum to `d`, so the pair of them runs
over the antidiagonal of `d`.  This is the rank-two instance of the count
`#(Sym α d) = (#α + d - 1).choose d`. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)

/-- `TauCeti.symFinTwoEquiv` is the number of entries equal to `0`. -/
@[simp]
theorem coe_symFinTwoEquiv_apply (d : ℕ) (s : Sym (Fin 2) d) :
    (symFinTwoEquiv d s : ℕ) = Multiset.count 0 (s : Multiset (Fin 2)) := (rfl)

/-- The inverse of `TauCeti.symFinTwoEquiv` spelled out: `i` many `0`s and `d - i` many `1`s. -/
@[simp]
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := by
  first
  | simp [symFinTwoEquiv, Fin.sum_univ_two, Multiset.nsmul_singleton]

end TauCeti
end -- closes the original EOF section from source line 47
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Sym/Basic.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Substitution in symmetric multivariate polynomials

Substituting into a symmetric multivariate polynomial a family of polynomials that is permuted
along with the variables, for instance the same univariate polynomial in every variable,
preserves symmetry. For finitely many variables over a commutative ring, Mathlib's fundamental
theorem of symmetric polynomials (`MvPolynomial.esymmAlgHom_surjective`) then expresses the
substituted polynomial in the elementary symmetric polynomials.

## Main declarations

* `MvPolynomial.IsSymmetric.bind₁`: substituting an equivariant family of polynomials preserves
  symmetry.
* `MvPolynomial.IsSymmetric.bind₁_aeval_X`: uniform univariate substitution preserves
  symmetry.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R}

/-- Substituting into a symmetric polynomial a family of polynomials `f` that is equivariant
under permutations of the variables, `rename e (f i) = f (e i)`, yields a symmetric
polynomial. -/
protected theorem IsSymmetric.bind₁ (hp : p.IsSymmetric) {f : σ → MvPolynomial σ R}
    (hf : ∀ (e : Equiv.Perm σ) (i : σ), rename e (f i) = f (e i)) :
    (bind₁ f p).IsSymmetric := fun e => by
  conv_rhs => rw [← hp e, bind₁_rename, Function.comp_def]
  simp_rw [rename_bind₁, hf]

/-- Substituting the same univariate polynomial into every variable of a symmetric multivariate
polynomial preserves symmetry. -/
theorem IsSymmetric.bind₁_aeval_X (hp : p.IsSymmetric) (q : Polynomial R) :
    (bind₁ (fun i => Polynomial.aeval (X i) q) p).IsSymmetric :=
  hp.bind₁ fun e i => by rw [← Polynomial.aeval_algHom_apply, rename_X]

end MvPolynomial
end -- closes the original EOF section from source line 29
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Monic/OfCoeff.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The monic polynomial with prescribed lower coefficients

A monic polynomial of degree `n` is exactly its `n` lower coefficients: the leading term is forced
to be `X ^ n`. This file names the resulting polynomial `TauCeti.Polynomial.monicOfCoeff c` for a
tuple `c : Fin n → R`, and records that reading the coefficients back off is inverse to it.

The point of naming it is that it is the object against which analytic dependence on the
coefficients is stated: `TauCeti/Analysis/Polynomial/SimpleRoots/Basic.lean` differentiates
`(c, z) ↦ (monicOfCoeff c).eval z` in `c` and `z` jointly, so the lower coefficients must appear as
a *free* tuple rather than as the data of a polynomial subtype.

## Main declarations

* `TauCeti.Polynomial.monicOfCoeff`: the monic polynomial `X ^ n + ∑ i, c i * X ^ i` of degree `n`
  whose `n` lower coefficients are `c`.
* `TauCeti.Polynomial.monic_monicOfCoeff`, `TauCeti.Polynomial.natDegree_monicOfCoeff`,
  `TauCeti.Polynomial.eval_monicOfCoeff`: its monicity, its degree and its values.
* `TauCeti.Polynomial.coeff_monicOfCoeff` and `TauCeti.Polynomial.monicOfCoeff_coeff`: the
  coefficients are read back off, and every monic polynomial of degree `n` arises this way, so the
  two constructions are mutually inverse.
* `TauCeti.Polynomial.monicOfCoeff_add_single_zero`: moving the constant coefficient by `t` adds
  the constant `t`.

Mathlib writes the same polynomial in the same shape one universe up: `Polynomial.freeMonic R n`,
in `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean`, is
`X ^ n + ∑ i, monomial i (MvPolynomial.X i)` over `MvPolynomial (Fin n) R`, of which
`monicOfCoeff c` is the specialization at `c`. Mathlib also has the same correspondence in bundled
form, as the composite of `Polynomial.monicEquivDegreeLT` with `Polynomial.degreeLTEquiv`;
`monicOfCoeff c` is by definition the image of `c` under the inverse of that composite, with the
degree-`< n` and monic subtypes unbundled away and without the `Nontrivial R` that
`monicEquivDegreeLT` carries. `TauCeti.Sym.coeffEquiv` is built from the bundled form, and
`TauCeti.Sym.toMonic_coeffEquiv_symm` identifies its inverse with `monicOfCoeff`.
-/

public section

namespace TauCeti

open Polynomial

namespace Polynomial

section OfCoeff

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The monic polynomial of degree `n` whose `n` lower coefficients are `c`, that is, the
specialization of Mathlib's `Polynomial.freeMonic` at the coefficient tuple `c`. It is the inverse
of the coefficient-reading half of `TauCeti.Sym.coeffEquiv`, and is the natural object to state
analytic dependence on the coefficients against: `TauCeti.Sym.coeffEquiv_symm_apply` describes the
inverse chart as its root multiset. -/
noncomputable def monicOfCoeff (c : Fin n → R) : R[X] :=
  X ^ n + ∑ i : Fin n, monomial (i : ℕ) (c i)

/-- The lower part of `TauCeti.Polynomial.monicOfCoeff` has degree less than `n`, which is where its
monicity and its degree come from. -/
private theorem degree_sum_monomial_lt (c : Fin n → R) :
    degree (∑ i : Fin n, monomial (i : ℕ) (c i)) < n := by
  first
  | simpa only [C_mul_X_pow_eq_monomial] using degree_sum_fin_lt c

/-- The polynomial attached to a coefficient tuple is monic: its lower part has degree `< n`, so the
term `X ^ n` leads. -/
@[simp]
theorem monic_monicOfCoeff (c : Fin n → R) : (monicOfCoeff c).Monic :=
  monic_X_pow_add (degree_sum_monomial_lt c)

/-- The prescribed coefficients are read back off: this is the defining property of
`TauCeti.Polynomial.monicOfCoeff`. -/
@[simp]
theorem coeff_monicOfCoeff (c : Fin n → R) (i : Fin n) : (monicOfCoeff c).coeff (i : ℕ) = c i := by
  first
  | have hne : (i : ℕ) ≠ n := i.2.ne
    simp [monicOfCoeff, coeff_X_pow, coeff_monomial, hne, Fin.val_eq_val]

/-- The coefficient of `X ^ n` in `TauCeti.Polynomial.monicOfCoeff c` is its leading coefficient
`1`. -/
@[simp]
theorem coeff_monicOfCoeff_self (c : Fin n → R) : (monicOfCoeff c).coeff n = 1 := by
  first
  | simp [monicOfCoeff, coeff_monomial, fun i : Fin n ↦ i.2.ne]

/-- Monic polynomials with prescribed lower coefficients agree exactly when their
coefficient tuples agree. -/
@[simp]
theorem monicOfCoeff_inj (c d : Fin n → R) : monicOfCoeff c = monicOfCoeff d ↔ c = d := by
  first
  | refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
    exact funext fun i ↦ by
      simpa only [coeff_monicOfCoeff] using congrArg (fun p : R[X] ↦ p.coeff i) h

/-- Evaluating the monic polynomial attached to a coefficient tuple: the leading power plus the
prescribed lower part. -/
theorem eval_monicOfCoeff (c : Fin n → R) (z : R) :
    (monicOfCoeff c).eval z = z ^ n + ∑ i : Fin n, c i * z ^ (i : ℕ) := by
  first
  | simp [monicOfCoeff, eval_finsetSum]

/-- Mapping coefficients commutes with forming the monic polynomial with prescribed lower
coefficients. -/
@[simp]
theorem map_monicOfCoeff {S : Type*} [CommSemiring S] (φ : R →+* S) (c : Fin n → R) :
    (monicOfCoeff c).map φ = monicOfCoeff (fun i ↦ φ (c i)) := by
  first
  | simp [monicOfCoeff, Polynomial.map_sum]

/-- Adding `t` to the constant coefficient of the tuple adds the constant polynomial `t`. -/
@[simp]
theorem monicOfCoeff_add_single_zero (c : Fin (n + 1) → R) (t : R) :
    monicOfCoeff (c + Pi.single 0 t) = monicOfCoeff c + C t := by
  first
  | have h : ∑ i : Fin (n + 1), monomial (i : ℕ) ((Pi.single 0 t : Fin (n + 1) → R) i) = C t := by
      rw [Finset.sum_eq_single 0 (fun i _ hi ↦ by simp [hi]) (by simp)]
      simp
    simp only [monicOfCoeff, Pi.add_apply, map_add, Finset.sum_add_distrib, h, add_assoc]

variable [Nontrivial R]

/-- The polynomial attached to a tuple of `n` coefficients has degree exactly `n`, the degree of its
leading term `X ^ n`. -/
@[simp]
theorem natDegree_monicOfCoeff (c : Fin n → R) : (monicOfCoeff c).natDegree = n := by
  first
  | have hlt : degree (∑ i : Fin n, monomial (i : ℕ) (c i)) < degree (X ^ n : R[X]) := by
      rw [degree_X_pow]
      exact degree_sum_monomial_lt c
    rw [monicOfCoeff, natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow]

/-- Every monic polynomial of degree `n` is the monic polynomial attached to its own lower
coefficients: together with `TauCeti.Polynomial.coeff_monicOfCoeff` this identifies the monic
polynomials of degree `n` with the coefficient tuples. -/
theorem monicOfCoeff_coeff {p : R[X]} (hp : p.Monic) (hdeg : p.natDegree = n) :
    monicOfCoeff (fun i : Fin n => p.coeff (i : ℕ)) = p := by
  first
  | refine Polynomial.ext fun k => ?_
    rcases lt_trichotomy k n with hk | hk | hk
    · exact coeff_monicOfCoeff _ ⟨k, hk⟩
    · rw [hk, coeff_monicOfCoeff_self, ← hdeg, hp.coeff_natDegree]
    · rw [coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_monicOfCoeff]),
        coeff_eq_zero_of_natDegree_lt (by rwa [hdeg])]

end OfCoeff

end Polynomial

end TauCeti
end -- closes the original EOF section from source line 47
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Monic/OfCoeff.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/SymmetricPower.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The symmetric power of a field, charted by elementary symmetric functions

A point of the `n`-th symmetric power `Sym R n` is an unordered `n`-tuple of scalars, and the monic
polynomial `∏_{a ∈ s} (X - a)` records exactly that information: its coefficients are the
elementary symmetric functions of the tuple, up to sign. Over an algebraically closed field the
correspondence is a bijection in both directions, and composing it with Mathlib's identification of
monic degree-`n` polynomials with their lower coefficients presents `Sym K n` as the affine space
`Fin n → K`.

This is the algebraic heart of the *symmetric product chart*: for a Riemann surface `Σ` the
symmetric product `Sym^g(Σ)` is given its complex manifold structure by exactly this map, read in a
holomorphic coordinate on `Σ` — a local identification `Sym^g(ℂ) ≅ ℂ^g` whose coordinates are the
elementary symmetric functions of the `g` points. Only the pointwise algebra is settled here, and
it takes no analytic input: everything below is a statement about polynomials over a commutative
ring or a field. The topology of `Sym^g(Σ)`, its complex structure, and the analysis that uses them
are separate later steps.

## Main declarations

* `TauCeti.Sym.toMonic`: the monic polynomial of degree `n` whose roots, with multiplicity, are the
  points of `s : Sym R n`. This is Mathlib's `Polynomial.ofMultiset` restricted to a fixed
  cardinality, repackaged so that the target subtype records the degree.
* `TauCeti.Sym.coeff_toMonic`: Vieta's formulas, that the `k`-th coefficient of `toMonic s` is
  `(-1) ^ (n - k)` times the `(n - k)`-th elementary symmetric function of `s`.
* `TauCeti.Sym.toMonic_append`, `TauCeti.Sym.toMonic_cons`, `TauCeti.Sym.toMonic_replicate`: the
  map is multiplicative in the tuple, so adjoining a point multiplies by a linear factor and a
  constant tuple gives a pure power.
* `TauCeti.Sym.roots_toMonic`, `TauCeti.Sym.toMonic_injective`, `TauCeti.Sym.mem_iff_isRoot`: over
  an integral domain the tuple is recovered from the polynomial as its root multiset, and
  `TauCeti.Sym.toMonic_ofFn_eq_of_forall_isRoot`, that a monic polynomial of degree `n` with `n`
  distinct roots is the monic polynomial of the unordered tuple of those roots.
* `TauCeti.Sym.toMonic_coeffEquiv_symm`: the inverse chart, read as a polynomial rather than as a
  root multiset, is `TauCeti.Polynomial.monicOfCoeff`, the monic polynomial with prescribed lower
  coefficients of `TauCeti/RingTheory/Polynomial/Monic/OfCoeff.lean`.
* `TauCeti.Sym.monicEquiv`: over an algebraically closed field, taking roots with multiplicity
  inverts `toMonic`, so `Sym K n` is equivalent to the monic polynomials of degree `n`.
* `TauCeti.Sym.coeffEquiv`: the resulting chart `Sym K n ≃ (Fin n → K)`, with
  `TauCeti.Sym.coeffEquiv_apply` naming its coordinates as the signed elementary symmetric
  functions and `TauCeti.Sym.coeffEquiv_symm_apply` describing the inverse as a root-taking map.
* `TauCeti.Sym.mem_iff_pow_add_sum_coeffEquiv_mul_pow_eq_zero`: membership in the basepoint
  divisor is characterized by an affine equation in the chart.
* `TauCeti.Sym.coeffEquiv_one_apply` and `TauCeti.Sym.coeffEquiv_two_apply`: the chart in degrees
  one and two, pinning down the sign convention.
* `TauCeti.Sym.toMonic_ofFn` and `TauCeti.Sym.coeffEquiv_ofFn_apply`: read on an ordered tuple
  `f : Fin n → R` through `TauCeti.Sym.ofFn`, the monic polynomial is the product
  `∏ i, (X - C (f i))` of linear factors and the chart reads off its coefficients.
* `TauCeti.Sym.exists_map_eval_esymm_eq_eval`: over a commutative ring, applying a univariate
  polynomial to every point of a tuple acts on each elementary symmetric function by evaluating a
  multivariate polynomial at the elementary symmetric functions of the tuple.
* `TauCeti.Sym.exists_coeffEquiv_map_eval_coeffEquiv_symm_eq_eval`: applying a univariate
  polynomial to every point acts by multivariate polynomials in the chart coordinates, including
  at tuples where points collide.

Lane F4.1 of the analytic Heegaard Floer roadmap opens with "`Sym^g(Σ)` geometry: smooth complex
structure (elementary symmetric functions), the totally real tori `T_α`, `T_β`, …", after
Ozsváth--Szabó ([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1). This file supplies
the algebra the first clause rests on, the correspondence between an unordered tuple and its monic
polynomial, and stops there; the linear algebra behind the second clause is
`TauCeti.IsMaximalTotallyReal.finrank_eq_half` in
`TauCeti/LinearAlgebra/TotallyReal/Finrank.lean`. Vieta's formulas,
the root multiset of a split monic polynomial, the multiset-to-polynomial map itself, and the
equivalence between monic polynomials of degree `n` and polynomials of degree `< n` are all
Mathlib's (`Multiset.prod_X_sub_C_coeff`,
`Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`, `Polynomial.ofMultiset`,
`Polynomial.monicEquivDegreeLT`); nothing is vendored here.
-/

public section

open Multiset Polynomial

namespace TauCeti

namespace Sym

section Basic

variable {R : Type*} [CommRing R] {m n : ℕ}

/-! ### The monic polynomial of an unordered tuple -/

section Defs

variable [Nontrivial R]

/-- The monic polynomial `∏_{a ∈ s} (X - a)` of an unordered `n`-tuple `s`, bundled with its
monicity and the fact that its degree is `n`.

The underlying polynomial is Mathlib's `Polynomial.ofMultiset`; the point of the subtype is that
the degree is pinned to `n` rather than to the cardinality of the underlying multiset, which is
what `Polynomial.monicEquivDegreeLT` consumes. -/
@[expose]
noncomputable def toMonic (s : Sym R n) : { p : R[X] // p.Monic ∧ p.natDegree = n } :=
  ⟨ofMultiset (s : Multiset R), by simpa using monic_multisetProd_X_sub_C (s : Multiset R),
    by simp [Sym.card_coe]⟩

theorem coe_toMonic (s : Sym R n) : (toMonic s : R[X]) = ofMultiset (s : Multiset R) :=
  rfl

@[simp]
theorem monic_toMonic (s : Sym R n) : (toMonic s : R[X]).Monic :=
  (toMonic s).2.1

@[simp]
theorem natDegree_toMonic (s : Sym R n) : (toMonic s : R[X]).natDegree = n :=
  (toMonic s).2.2

@[simp]
theorem toMonic_nil : (toMonic (Sym.nil : Sym R 0) : R[X]) = 1 := by
  first
  | rw [coe_toMonic]
    simp

/-- Adjoining a point to a tuple multiplies its monic polynomial by the corresponding linear
factor. -/
@[simp]
theorem toMonic_cons (a : R) (s : Sym R n) :
    (toMonic (a ::ₛ s) : R[X]) = (X - C a) * (toMonic s : R[X]) := by
  first
  | simp only [coe_toMonic, Sym.coe_cons]
    simp

/-- The monic polynomial of a union of two tuples is the product of their monic polynomials: this
is the multiplicativity that makes `Polynomial.ofMultiset` an additive character. -/
@[simp]
theorem toMonic_append (s : Sym R n) (t : Sym R m) :
    (toMonic (s.append t) : R[X]) = (toMonic s : R[X]) * (toMonic t : R[X]) := by
  first
  | simp only [coe_toMonic, Sym.coe_append]
    exact ofMultiset.map_add_eq_mul _ _

/-- The monic polynomial of the unordered tuple underlying an ordered one `f : Fin n → R` is the
product of the corresponding linear factors. -/
theorem toMonic_ofFn (f : Fin n → R) : (toMonic (ofFn f) : R[X]) = ∏ i, (X - C (f i)) := by
  first
  | rw [coe_toMonic, coe_ofFn]
    simp [← List.prod_ofFn, List.map_ofFn, Function.comp_def]

/-- The monic polynomial of a constant tuple is a pure power of a linear factor. -/
@[simp]
theorem toMonic_replicate (a : R) : (toMonic (Sym.replicate n a) : R[X]) = (X - C a) ^ n := by
  first
  | rw [coe_toMonic, Sym.coe_replicate]
    simp

/-- Evaluating the monic polynomial of a tuple at `x` multiplies together the differences between
`x` and the points of the tuple. -/
@[simp]
theorem eval_toMonic (s : Sym R n) (x : R) :
    (toMonic s : R[X]).eval x = ((s : Multiset R).map fun a => x - a).prod := by
  first
  | rw [coe_toMonic]
    simp [eval_multiset_prod, Multiset.map_map]

/-- **Vieta's formulas** on the symmetric power: the `k`-th coefficient of the monic polynomial of
an unordered `n`-tuple is the `(n - k)`-th elementary symmetric function of the tuple, up to the
sign `(-1) ^ (n - k)`. -/
theorem coeff_toMonic (s : Sym R n) {k : ℕ} (hk : k ≤ n) :
    (toMonic s : R[X]).coeff k = (-1) ^ (n - k) * (s : Multiset R).esymm (n - k) := by
  first
  | have hcard : Multiset.card (s : Multiset R) = n := Sym.card_coe
    have hk' : k ≤ Multiset.card (s : Multiset R) := by rw [hcard]; exact hk
    rw [coe_toMonic]
    simpa [hcard] using (s : Multiset R).prod_X_sub_C_coeff hk'

/-- The constant term of the monic polynomial of a tuple is the signed product of its points. -/
@[simp]
theorem coeff_zero_toMonic (s : Sym R n) :
    (toMonic s : R[X]).coeff 0 = (-1) ^ n * (s : Multiset R).prod := by
  first
  | rw [coeff_zero_eq_eval_zero, eval_toMonic]
    simp [Sym.card_coe]

end Defs

section Domain

variable [IsDomain R]

/-- Over an integral domain the points of a tuple are recovered, with multiplicity, as the roots of
its monic polynomial. -/
@[simp]
theorem roots_toMonic (s : Sym R n) : (toMonic s : R[X]).roots = (s : Multiset R) := by
  first
  | rw [coe_toMonic]
    exact roots_ofMultiset _

/-- Over an integral domain a tuple is determined by its monic polynomial: two unordered `n`-tuples
with the same monic polynomial are equal. -/
theorem toMonic_injective : Function.Injective (toMonic (R := R) (n := n)) := fun s t h =>
  Sym.coe_injective <| ofMultiset_injective R <| by
    rw [← coe_toMonic s, ← coe_toMonic t, h]

/-- A scalar lies in a tuple exactly when it is a root of the tuple's monic polynomial. -/
theorem mem_iff_isRoot {a : R} {s : Sym R n} :
    a ∈ (s : Multiset R) ↔ (toMonic s : R[X]).IsRoot a := by
  first
  | rw [← roots_toMonic s, mem_roots (monic_toMonic s).ne_zero]

/-- A monic polynomial of degree `n` with `n` pairwise distinct roots is the monic polynomial of
the unordered tuple of those roots: a full set of simple roots pins the polynomial down. -/
theorem toMonic_ofFn_eq_of_forall_isRoot {p : R[X]} (hp : p.Monic) (hdeg : p.natDegree = n)
    {w : Fin n → R} (hw : Function.Injective w) (hroot : ∀ i, (p : R[X]).IsRoot (w i)) :
    (toMonic (ofFn w) : R[X]) = p := by
  first
  | have hle : (ofFn w : Multiset R) ≤ p.roots := by
      refine (Multiset.le_iff_subset (by rw [coe_ofFn]; simpa using List.nodup_ofFn.2 hw)).2
        fun a ha => ?_
      obtain ⟨i, rfl⟩ := mem_ofFn.1 (by simpa using ha)
      exact (mem_roots' (p := p)).2 ⟨hp.ne_zero, hroot i⟩
    have hcard : Multiset.card (ofFn w : Multiset R) = n := Sym.card_coe
    have hroots : (ofFn w : Multiset R) = p.roots :=
      Multiset.eq_of_le_of_card_le hle (by rw [hcard, ← hdeg]; exact p.card_roots')
    rw [coe_toMonic, ofMultiset_apply, hroots]
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp (by rw [← hroots, hcard, hdeg])

end Domain

end Basic

/-! ### The chart over an algebraically closed field -/

section Components

variable {K : Type*} [Field K] {n : ℕ}

/-! Mathlib builds `Polynomial.monicEquivDegreeLT` and `Polynomial.degreeLTEquiv` as anonymous
structure instances and states no `apply` or `symm_apply` lemma for either — it unfolds their
definitions where it needs them, as in `Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean`. The
four lemmas here supply those missing component lemmas once, so that the chart proofs below rewrite
with named equations instead of reducing the composite equivalence. -/

/-- `Polynomial.degreeLTEquiv` reads off coefficients. -/
private theorem degreeLTEquiv_toEquiv_apply (p : degreeLT K n) (i : Fin n) :
    (degreeLTEquiv K n).toEquiv p i = (p : K[X]).coeff (i : ℕ) :=
  rfl

/-- `Polynomial.monicEquivDegreeLT` removes the leading term. -/
private theorem coe_monicEquivDegreeLT_apply (p : { p : K[X] // p.Monic ∧ p.natDegree = n }) :
    ((monicEquivDegreeLT n p : degreeLT K n) : K[X]) = (p : K[X]).eraseLead :=
  rfl

/-- The inverse of `Polynomial.degreeLTEquiv` assembles a polynomial from its coefficients. -/
private theorem coe_degreeLTEquiv_toEquiv_symm_apply (f : Fin n → K) :
    (((degreeLTEquiv K n).toEquiv.symm f : degreeLT K n) : K[X]) =
      ∑ i : Fin n, monomial (i : ℕ) (f i) :=
  rfl

/-- The inverse of `Polynomial.monicEquivDegreeLT` restores the leading term `X ^ n`. -/
private theorem coe_monicEquivDegreeLT_symm_apply (p : degreeLT K n) :
    (((monicEquivDegreeLT n).symm p : { p : K[X] // p.Monic ∧ p.natDegree = n }) : K[X]) =
      X ^ n + (p : K[X]) :=
  rfl

end Components

section AlgClosed

variable (K : Type*) [Field K] [IsAlgClosed K] (n : ℕ)

/-- Over an algebraically closed field, `TauCeti.Sym.toMonic` is a bijection from the `n`-th
symmetric power onto the monic polynomials of degree `n`, inverted by taking roots with
multiplicity. -/
@[expose]
noncomputable def monicEquiv : Sym K n ≃ { p : K[X] // p.Monic ∧ p.natDegree = n } where
  toFun := toMonic
  invFun p := Sym.mk p.1.roots <| by
    rw [splits_iff_card_roots.mp (IsAlgClosed.splits p.1), p.2.2]
  left_inv s := Sym.coe_injective (roots_toMonic s)
  right_inv p := Subtype.ext <| by
    rw [coe_toMonic]
    simpa using prod_multiset_X_sub_C_of_monic_of_roots_card_eq p.2.1
      (splits_iff_card_roots.mp (IsAlgClosed.splits p.1))

@[simp]
theorem monicEquiv_apply (s : Sym K n) : monicEquiv K n s = toMonic s :=
  rfl

@[simp]
theorem coe_monicEquiv_symm_apply (p : { p : K[X] // p.Monic ∧ p.natDegree = n }) :
    (((monicEquiv K n).symm p : Sym K n) : Multiset K) = p.1.roots :=
  rfl

/-- The **elementary symmetric chart** on the `n`-th symmetric power of an algebraically closed
field: an unordered `n`-tuple is determined by, and freely determines, the `n` lower coefficients of
its monic polynomial.

By `TauCeti.Sym.coeffEquiv_apply` the `i`-th coordinate is `(-1) ^ (n - i)` times the `(n - i)`-th
elementary symmetric function of the tuple. -/
noncomputable def coeffEquiv : Sym K n ≃ (Fin n → K) :=
  (monicEquiv K n).trans ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)

variable {K n}

/-- The chart reads off the lower coefficients of the monic polynomial of the tuple. -/
theorem coeffEquiv_apply_eq_coeff (s : Sym K n) (i : Fin n) :
    coeffEquiv K n s i = (toMonic s : K[X]).coeff i := by
  first
  | have hne : (i : ℕ) ≠ (toMonic s : K[X]).natDegree := by
      rw [natDegree_toMonic]
      exact i.2.ne
    rw [coeffEquiv, Equiv.trans_apply, Equiv.trans_apply, monicEquiv_apply,
      degreeLTEquiv_toEquiv_apply, coe_monicEquivDegreeLT_apply]
    exact eraseLead_coeff_of_ne _ hne

/-- The coordinates of the elementary symmetric chart are the elementary symmetric functions of the
tuple, in decreasing order and with alternating signs. -/
@[simp]
theorem coeffEquiv_apply (s : Sym K n) (i : Fin n) :
    coeffEquiv K n s i = (-1) ^ (n - (i : ℕ)) * (s : Multiset K).esymm (n - (i : ℕ)) := by
  first
  | rw [coeffEquiv_apply_eq_coeff, coeff_toMonic s i.2.le]

/-- The chart of an unordered tuple presented by an ordered one `f : Fin n → K` reads off the
coefficients of the product of the linear factors of `f`. -/
theorem coeffEquiv_ofFn_apply (f : Fin n → K) (i : Fin n) :
    coeffEquiv K n (ofFn f) i = (∏ j, (X - C (f j))).coeff i := by
  first
  | rw [coeffEquiv_apply_eq_coeff, toMonic_ofFn]

/-- The inverse chart, read as a polynomial rather than as a root multiset, is
`TauCeti.Polynomial.monicOfCoeff`: the monic polynomial of the tuple with prescribed coordinates is
the monic polynomial with those lower coefficients. Equivalently, the chart itself reads off the
lower coefficients of `TauCeti.Sym.toMonic`, which is `TauCeti.Sym.coeffEquiv_apply_eq_coeff`. -/
@[simp]
theorem toMonic_coeffEquiv_symm (c : Fin n → K) :
    (toMonic ((coeffEquiv K n).symm c) : K[X]) = Polynomial.monicOfCoeff c := by
  first
  | symm
    simpa only [← coeffEquiv_apply_eq_coeff, Equiv.apply_symm_apply] using
      Polynomial.monicOfCoeff_coeff (monic_toMonic ((coeffEquiv K n).symm c))
        (natDegree_toMonic (s := (coeffEquiv K n).symm c))

/-- The inverse chart sends a coefficient tuple to the root multiset of the monic polynomial it
determines. -/
@[simp]
theorem coeffEquiv_symm_apply (f : Fin n → K) : (((coeffEquiv K n).symm f : Sym K n) : Multiset K) =
      (Polynomial.monicOfCoeff f).roots := by
  first
  | rw [← roots_toMonic ((coeffEquiv K n).symm f), toMonic_coeffEquiv_symm]

/-- **The tuples through a point satisfy an affine equation in the elementary symmetric chart.** A
point `a` belongs to `s` exactly when the monic polynomial whose lower coefficients are the
coordinates of `s` vanishes at `a`. For `0 < n`, the equation has coefficient `1` on the
constant coordinate. In degree zero it reads `1 = 0`, so its locus is empty. -/
theorem mem_iff_pow_add_sum_coeffEquiv_mul_pow_eq_zero {a : K} {s : Sym K n} :
    s ∈ basepointDivisor a ↔ a ^ n + ∑ i : Fin n, coeffEquiv K n s i * a ^ (i : ℕ) = 0 := by
  first
  | simp only [mem_basepointDivisor]
    have h := toMonic_coeffEquiv_symm (coeffEquiv K n s)
    rw [Equiv.symm_apply_apply] at h
    rw [← _root_.Sym.mem_coe, mem_iff_isRoot, h, IsRoot.def, Polynomial.eval_monicOfCoeff]

/-- In degree one the chart is negation: the single coordinate of a one-point tuple is minus that
point. -/
theorem coeffEquiv_one_apply {s : Sym K 1} {a : K} (hs : (s : Multiset K) = {a}) :
    coeffEquiv K 1 s 0 = -a := by
  first
  | rw [coeffEquiv_apply, hs]
    simp [Multiset.esymm, Multiset.powersetCard_one]

/-- In degree two the chart is `{a, b} ↦ (ab, -(a + b))`: the two lower coefficients of
`(X - a) (X - b) = X ^ 2 - (a + b) X + ab`. -/
theorem coeffEquiv_two_apply {s : Sym K 2} {a b : K} (hs : (s : Multiset K) = {a, b}) :
    coeffEquiv K 2 s = ![a * b, -(a + b)] := by
  first
  | ext i
    fin_cases i <;> rw [coeffEquiv_apply, hs] <;> simp

end AlgClosed

/-! ### The action of a polynomial map in coefficient coordinates -/

section PolynomialMapAlg

open _root_.MvPolynomial Finset

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The `j`-th variable of a fundamental-theorem polynomial, read in elementary symmetric
coefficients: the `(j+1)`-st elementary symmetric function of a root tuple is `(-1) ^ (j+1)` times
coefficient `j.rev`, by Vieta's formulas. -/
private noncomputable def esymmInCoeff (j : Fin n) : MvPolynomial (Fin n) K :=
  MvPolynomial.C ((-1 : K) ^ ((j : ℕ) + 1)) * MvPolynomial.X j.rev

/-- Substituting the signed coefficient coordinates for the elementary symmetric polynomials. -/
private noncomputable def coeffSubst :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval esymmInCoeff

/-- Evaluating the coefficient substitution reads a fundamental-theorem polynomial in the signed
coefficient coordinates. -/
private theorem aeval_coeffSubst (c : Fin n → K) (p : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval c (coeffSubst p) =
      MvPolynomial.aeval
        (fun j : Fin n => (-1 : K) ^ ((j : ℕ) + 1) * c j.rev) p := by
  first
  | rw [coeffSubst, MvPolynomial.comp_aeval_apply]
    refine congrArg (fun g => MvPolynomial.aeval g p) (funext fun j => ?_)
    rw [MvPolynomial.aeval_eq_eval]
    simp only [esymmInCoeff, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]

/-- **Applying a polynomial to a tuple acts polynomially on the elementary symmetric functions.**
Over any commutative ring, for every degree `k` there is a multivariate polynomial `Q k` such that
the `k`-th elementary symmetric function of the tuple obtained by applying `q` pointwise is the
evaluation of `Q k` at the elementary symmetric functions of the original tuple, with no
hypothesis excluding tuples of colliding points. This is the algebraic core of
`exists_coeffEquiv_map_eval_coeffEquiv_symm_eq_eval`, which reads the same statement in chart
coordinates. -/
theorem exists_map_eval_esymm_eq_eval (q : K[X]) :
    ∃ Q : ℕ → MvPolynomial (Fin n) K, ∀ (s : Sym K n) (k : ℕ),
      (Sym.map (fun z => eval z q) s : Multiset K).esymm k =
        MvPolynomial.eval (fun j : Fin n => (s : Multiset K).esymm ((j : ℕ) + 1)) (Q k) := by
  first
  | classical
    have hftsf : ∀ k : ℕ, ∃ W : MvPolynomial (Fin n) K,
        MvPolynomial.aeval (fun j : Fin n => esymm (Fin n) K ((j : ℕ) + 1)) W =
          MvPolynomial.bind₁ (fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q)
            (esymm (Fin n) K k) := fun k => by
      obtain ⟨W, hW⟩ := (esymmAlgHom_fin_bijective K n).surjective
        ⟨_, (esymm_isSymmetric (Fin n) K k).bind₁_aeval_X q⟩
      exact ⟨W, by rw [← esymmAlgHom_apply, hW]⟩
    choose W hW using hftsf
    refine ⟨W, fun s k => ?_⟩
    obtain ⟨v, hv⟩ := ofFn_surjective s
    have hcoe : (s : Multiset K) = univ.val.map v := by
      rw [← hv, Sym.coe_ofFn, ← Fin.univ_val_map]
    have hmap : (Sym.map (fun z => eval z q) s : Multiset K) =
        univ.val.map (fun j => Polynomial.eval (v j) q) := by
      rw [Sym.coe_map, hcoe, Multiset.map_map]
      rfl
    calc
      (Sym.map (fun z => eval z q) s : Multiset K).esymm k =
          MvPolynomial.aeval (fun j => Polynomial.eval (v j) q) (esymm (Fin n) K k) := by
        rw [hmap]
        exact (MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) K k
          (fun j => Polynomial.eval (v j) q)).symm
      _ = MvPolynomial.aeval (fun j => Polynomial.aeval (v j) q) (esymm (Fin n) K k) := by
        refine congrArg (fun g => MvPolynomial.aeval g (esymm (Fin n) K k))
          (funext fun j => (congrFun (Polynomial.coe_aeval_eq_eval (v j)) q).symm)
      _ = MvPolynomial.aeval v
            (MvPolynomial.bind₁ (fun j : Fin n => Polynomial.aeval (MvPolynomial.X j) q)
              (esymm (Fin n) K k)) := by
        rw [MvPolynomial.aeval_bind₁]
        refine congrArg (fun g => MvPolynomial.aeval g (esymm (Fin n) K k)) (funext fun j => ?_)
        calc
          Polynomial.aeval (v j) q =
              Polynomial.aeval (MvPolynomial.aeval v (MvPolynomial.X j)) q := by
            rw [MvPolynomial.aeval_X]
          _ = MvPolynomial.aeval v (Polynomial.aeval (MvPolynomial.X j) q) :=
            Polynomial.aeval_algHom_apply (MvPolynomial.aeval v) (MvPolynomial.X j) q
      _ = MvPolynomial.aeval v
            (MvPolynomial.aeval (fun j : Fin n => esymm (Fin n) K ((j : ℕ) + 1)) (W k)) := by
        rw [hW]
      _ = MvPolynomial.aeval (fun j : Fin n => (s : Multiset K).esymm ((j : ℕ) + 1)) (W k) := by
        rw [MvPolynomial.comp_aeval_apply]
        refine congrArg (fun g => MvPolynomial.aeval g (W k)) (funext fun j => ?_)
        rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hcoe]
      _ = MvPolynomial.eval (fun j : Fin n => (s : Multiset K).esymm ((j : ℕ) + 1)) (W k) := rfl

end PolynomialMapAlg

section PolynomialMap

open _root_.MvPolynomial Finset

variable {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}

/-- The `(j+1)`-st elementary symmetric function of a tuple equals its corresponding signed
coefficient coordinate. -/
private theorem _root_.Sym.esymm_succ_eq_neg_one_pow_mul_coeffEquiv (s : Sym K n) (j : Fin n) :
    (s : Multiset K).esymm ((j : ℕ) + 1) =
      (-1 : K) ^ ((j : ℕ) + 1) * coeffEquiv K n s j.rev := by
  first
  | rw [coeffEquiv_apply, Fin.val_rev, Nat.sub_sub_self (by have := j.isLt; omega)]
    have hsign : (-1 : K) ^ ((j : ℕ) + 1) * (-1 : K) ^ ((j : ℕ) + 1) = 1 := by
      rw [← pow_add, ← Nat.two_mul, pow_mul]
      norm_num
    rw [← mul_assoc, hsign, one_mul]

/-- **Applying a polynomial to a tuple acts polynomially in elementary symmetric
coefficients.** For every coefficient tuple `c`, including those representing colliding points,
the coefficients after applying `q` pointwise are evaluations of multivariate polynomials `Q`:
`exists_map_eval_esymm_eq_eval` read in the signed chart coordinates given by Vieta's formulas. -/
theorem exists_coeffEquiv_map_eval_coeffEquiv_symm_eq_eval (q : K[X]) :
    ∃ Q : Fin n → MvPolynomial (Fin n) K, ∀ c : Fin n → K,
      coeffEquiv K n (Sym.map (fun z => eval z q) ((coeffEquiv K n).symm c)) =
        fun i => eval c (Q i) := by
  first
  | obtain ⟨Wgen, hWgen⟩ := exists_map_eval_esymm_eq_eval (K := K) (n := n) q
    refine ⟨fun i => MvPolynomial.C ((-1 : K) ^ (n - (i : ℕ))) *
      coeffSubst (Wgen (n - (i : ℕ))), fun c => ?_⟩
    funext i
    have hsymm : ∀ j : Fin n, ((coeffEquiv K n).symm c : Multiset K).esymm ((j : ℕ) + 1) =
        (-1 : K) ^ ((j : ℕ) + 1) * c j.rev := by
      intro j
      rw [Sym.esymm_succ_eq_neg_one_pow_mul_coeffEquiv, Equiv.apply_symm_apply]
    calc
      coeffEquiv K n (Sym.map (fun z => eval z q) ((coeffEquiv K n).symm c)) i =
          (-1 : K) ^ (n - (i : ℕ)) *
            (Sym.map (fun z => eval z q) ((coeffEquiv K n).symm c) : Multiset K).esymm
              (n - (i : ℕ)) := by rw [coeffEquiv_apply]
      _ = (-1 : K) ^ (n - (i : ℕ)) * MvPolynomial.eval
            (fun j : Fin n => ((coeffEquiv K n).symm c : Multiset K).esymm ((j : ℕ) + 1))
            (Wgen (n - (i : ℕ))) := by
        rw [hWgen ((coeffEquiv K n).symm c) (n - (i : ℕ))]
      _ = (-1 : K) ^ (n - (i : ℕ)) * MvPolynomial.aeval
            (fun j : Fin n => ((coeffEquiv K n).symm c : Multiset K).esymm ((j : ℕ) + 1))
            (Wgen (n - (i : ℕ))) := rfl
      _ = (-1 : K) ^ (n - (i : ℕ)) * MvPolynomial.aeval
            (fun j : Fin n => (-1 : K) ^ ((j : ℕ) + 1) * c j.rev) (Wgen (n - (i : ℕ))) := by
        rw [funext hsymm]
      _ = MvPolynomial.eval c
          (MvPolynomial.C ((-1 : K) ^ (n - (i : ℕ))) * coeffSubst (Wgen (n - (i : ℕ)))) := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval,
          ← aeval_coeffSubst]

end PolynomialMap

end Sym

end TauCeti
end -- closes the original EOF section from source line 85
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/SymmetricPower.lean -/

/- BEGIN SOURCE: TauCeti/Topology/Algebra/Polynomial/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Continuity of polynomial families

For a family of polynomials `f x` over a topological semiring, indexed by a parameter `x`, the
coefficients of a product are finite sums of products of coefficients of the factors. Hence if
every coefficient of each factor is continuous at a point, so is every coefficient of the product.
This is used to treat the product of a finite family of polynomials with continuous coefficients
as a single polynomial family.

If the degrees of the family are bounded and its coefficients are continuous, then the evaluation
`(x, t) ↦ (f x).eval t` is jointly continuous, since it is a finite sum of products of
coefficients with powers of `t`. The basic example of a family with continuous coefficients is
the monic polynomial `TauCeti.Polynomial.monicOfCoeff a` as a function of its coefficient tuple
`a`.

## Main results

* `Polynomial.continuousAt_eval`: evaluation along a continuous point for a family of locally
  bounded degree.
* `Polynomial.continuousAt_coeff_mul`: coefficients of a product of two families.
* `Polynomial.continuousAt_coeff_prod`: coefficients of a finite product of families.
* `Polynomial.continuous_eval_of_continuous_coeff`: joint continuity of the evaluation of a family
  of bounded degree.
* `Polynomial.continuous_evalEval`: joint continuity of bivariate polynomial evaluation.
* `TauCeti.Polynomial.continuous_coeff_monicOfCoeff`: the coefficients of `monicOfCoeff a` are
  continuous in `a`.
* `TauCeti.Polynomial.continuous_coeff_prod_X_sub_C`: the coefficients of `∏ i ∈ s, (X - C (f i))`
  are continuous in the tuple of roots `f`.
-/

public section

open Filter Topology
open scoped Polynomial.Bivariate

namespace Polynomial

/-- Evaluation of a bivariate polynomial is jointly continuous in its two arguments. -/
theorem continuous_evalEval {R : Type*} [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (P : R[X][Y]) :
    Continuous fun z : R × R ↦ P.evalEval z.1 z.2 := by
  first
  | have key (x y : R) : P.evalEval x y =
        ∑ j ∈ P.support, (P.coeff j).eval x * y ^ j := by
      rw [Polynomial.evalEval, Polynomial.eval_eq_sum (p := P)]
      simp only [Polynomial.sum_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C]
    simp only [key]
    exact continuous_finsetSum _ fun j _ ↦
      ((P.coeff j).continuous.comp continuous_fst).mul (continuous_snd.pow j)

end Polynomial

namespace Polynomial

/-- Evaluation along a point continuous at `x₀` is continuous at `x₀` if the coefficients of
index at most `d` are continuous there and the family has degree bounded by `d` nearby. -/
theorem continuousAt_eval {X R : Type*} [TopologicalSpace X] [TopologicalSpace R]
    [Semiring R] [IsTopologicalSemiring R] {f : X → R[X]} {r : X → R} {x₀ : X} {d : ℕ}
    (hf : ∀ i ≤ d, ContinuousAt (fun x ↦ (f x).coeff i) x₀)
    (hd : ∀ᶠ x in 𝓝 x₀, (f x).natDegree ≤ d) (hr : ContinuousAt r x₀) :
    ContinuousAt (fun x ↦ (f x).eval (r x)) x₀ := by
  first
  | have heq : (fun x ↦ (f x).eval (r x)) =ᶠ[𝓝 x₀]
        fun x ↦ ∑ i ∈ Finset.range (d + 1), (f x).coeff i * r x ^ i := by
      filter_upwards [hd] with x hx
      exact eval_eq_sum_range' (Nat.lt_succ_of_le hx) _
    have hc : ContinuousAt (fun x ↦ ∑ i ∈ Finset.range (d + 1),
        (f x).coeff i * r x ^ i) x₀ :=
      tendsto_finsetSum _ fun i hi ↦ (hf i (Finset.mem_range_succ_iff.1 hi)).mul (hr.pow i)
    exact hc.congr_of_eventuallyEq heq

variable {X R ι : Type*} [TopologicalSpace X] [TopologicalSpace R] {x₀ : X}

/-- The coefficient of index `i` in a product of two polynomial families is continuous at `x₀`
if the coefficients of indices at most `i` in both factors are continuous there. -/
theorem continuousAt_coeff_mul [Semiring R] [IsTopologicalSemiring R] {f g : X → R[X]} {i : ℕ}
    (hf : ∀ j ≤ i, ContinuousAt (fun x ↦ (f x).coeff j) x₀)
    (hg : ∀ j ≤ i, ContinuousAt (fun x ↦ (g x).coeff j) x₀) :
    ContinuousAt (fun x ↦ (f x * g x).coeff i) x₀ := by
  first
  | simp only [coeff_mul]
    refine tendsto_finsetSum _ fun p hp ↦ ?_
    have hp := Finset.mem_antidiagonal.mp hp
    exact (hf p.1 (by omega)).mul (hg p.2 (by omega))

/-- The coefficient of index `i` in a finite product of polynomial families is continuous at `x₀`
if the coefficients of indices at most `i` in every factor are continuous there. -/
theorem continuousAt_coeff_prod [CommSemiring R] [IsTopologicalSemiring R]
    {f : ι → X → R[X]} (s : Finset ι) {i : ℕ}
    (hf : ∀ k ∈ s, ∀ j ≤ i, ContinuousAt (fun x ↦ (f k x).coeff j) x₀) :
    ContinuousAt (fun x ↦ (∏ k ∈ s, f k x).coeff i) x₀ := by
  first
  | classical
    induction s using Finset.induction_on generalizing i with
    | empty =>
      simp only [Finset.prod_empty]
      exact continuousAt_const
    | insert k s hk ih =>
      simp only [Finset.prod_insert hk]
      exact continuousAt_coeff_mul (hf k (Finset.mem_insert_self k s))
        (fun j hj ↦ ih fun l hl m hm ↦ hf l (Finset.mem_insert_of_mem hl) m (hm.trans hj))

/-- If a family of polynomials has degree at most `d` and its coefficients of index at most `d` are
continuous, then its evaluation is jointly continuous in the parameter and the point. -/
theorem continuous_eval_of_continuous_coeff [Semiring R] [IsTopologicalSemiring R]
    {f : X → R[X]} {d : ℕ}
    (hf : ∀ i ≤ d, Continuous fun x => (f x).coeff i) (hd : ∀ x, (f x).natDegree ≤ d) :
    Continuous fun z : X × R => (f z.1).eval z.2 := by
  first
  | refine continuous_iff_continuousAt.2 fun z ↦ ?_
    exact continuousAt_eval (fun i hi ↦ ((hf i hi).comp continuous_fst).continuousAt)
      (.of_forall fun y ↦ hd y.1) continuous_snd.continuousAt

end Polynomial

namespace TauCeti.Polynomial

open _root_.Polynomial

/-- Each coefficient of the monic polynomial `monicOfCoeff a` is a continuous function of the
coefficient tuple `a`: it is either constant or a coordinate of `a`. -/
theorem continuous_coeff_monicOfCoeff {R : Type*} [CommSemiring R] [TopologicalSpace R]
    {n : ℕ} (j : ℕ) : Continuous fun a : Fin n → R ↦ (monicOfCoeff a).coeff j := by
  first
  | rcases subsingleton_or_nontrivial R with hR | hR
    · exact continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
    rcases lt_trichotomy j n with hj | rfl | hj
    · rw [funext fun a ↦ coeff_monicOfCoeff a ⟨j, hj⟩]
      exact continuous_apply _
    · rw [funext (coeff_monicOfCoeff_self (R := R))]
      exact continuous_const
    · rw [funext fun a ↦ coeff_eq_zero_of_natDegree_lt ((natDegree_monicOfCoeff a).trans_lt hj)]
      exact continuous_const

/-- The coefficients of `∏ i ∈ s, (X - C (f i))` depend continuously on the tuple `f` of roots.

Each coefficient is, up to sign, an elementary symmetric function of the roots, so continuity of the
ring operations is all that is used. -/
theorem continuous_coeff_prod_X_sub_C {ι R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (s : Finset ι) (k : ℕ) :
    Continuous fun f : ι → R => (∏ i ∈ s, (X - C (f i))).coeff k := by
  first
  | refine continuous_iff_continuousAt.2 fun f₀ ↦ ?_
    refine continuousAt_coeff_prod (f := fun i (f : ι → R) ↦ X - C (f i)) s fun i _ j _ ↦ ?_
    simp only [coeff_sub, coeff_X, coeff_C]
    split_ifs <;>
      first
      | exact continuousAt_const
      | exact (continuous_const.sub (continuous_apply i)).continuousAt

end TauCeti.Polynomial
end -- closes the original EOF section from source line 45
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Topology/Algebra/Polynomial/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Data/Sym/Disjoint.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tuples mapped into pairwise disjoint ranges

An ordered tuple mapped pointwise into pairwise disjoint ranges is determined by the unordered
tuple it presents. This file proves that injectivity statement and characterizes the range by
counting how many points lie in each component range. The corresponding topological open embedding
is in `TauCeti/Topology/Sym/Disjoint.lean`.

## Main declarations

* `TauCeti.Sym.ofFn_map_injective`: ordered tuples mapped into pairwise disjoint ranges are
  determined by the unordered tuples they present, with `TauCeti.Sym.mem_range_ofFn_map`
  describing those unordered tuples.
-/

public section

namespace TauCeti

namespace Sym

variable {α : Type*} {n : ℕ}

/-! ### Tuples mapped into pairwise disjoint ranges -/

/-- An ordered tuple mapped pointwise into pairwise disjoint ranges is determined by the unordered
tuple it presents. A permutation matching two such tuples must fix every index. -/
theorem ofFn_map_injective {X : Fin n → Type*} (f : ∀ i, X i → α)
    (hf : ∀ i, Function.Injective (f i))
    (h : Pairwise (Function.onFun Disjoint fun i => Set.range (f i))) :
    Function.Injective fun x : ∀ i, X i => ofFn fun i => f i (x i) := by
  first
  | intro x y hxy
    obtain ⟨σ, hσ⟩ := ofFn_eq_ofFn_iff.1 hxy
    have hval : ∀ i, f (σ i) (x (σ i)) = f i (y i) := fun i => congrFun hσ i
    have hfix : ∀ i, σ i = i := fun i => by
      by_contra hne
      exact Set.disjoint_left.1 (h hne) (Set.mem_range_self (x (σ i)))
        ⟨y i, (hval i).symm⟩
    exact funext fun i => hf i <|
      (congrArg (fun j => f j (x j)) (hfix i)).symm.trans (hval i)

attribute [local instance] Classical.propDecidable

/-- The range of ordered tuples mapped pointwise into pairwise disjoint ranges consists exactly of
the unordered tuples having one point in each range. -/
theorem mem_range_ofFn_map {X : Fin n → Type*} (f : ∀ i, X i → α)
    (h : Pairwise (Function.onFun Disjoint fun i => Set.range (f i))) {w : Sym α n} :
    w ∈ Set.range (fun x : ∀ i, X i => ofFn fun i => f i (x i)) ↔
      ∀ i, Multiset.card
        (Multiset.filter (· ∈ Set.range (f i)) (w : Multiset α)) = 1 := by
  first
  | classical
    constructor
    · rintro ⟨x, rfl⟩ i
      set a : Fin n → α := fun j => f j (x j)
      have ha : Function.Injective a := by
        intro j k hjk
        by_contra hne
        exact Set.disjoint_left.1 (h hne) (Set.mem_range_self (x j))
          ⟨x k, hjk.symm⟩
      have hnodup : (ofFn a : Multiset α).Nodup := by
        rw [coe_ofFn]
        exact List.nodup_ofFn.2 ha
      have hfilter : Multiset.filter (· ∈ Set.range (f i)) (ofFn a : Multiset α) = {a i} := by
        apply (Multiset.Nodup.ext (hnodup.filter _) (Multiset.nodup_singleton _)).2
        intro b
        rw [Multiset.mem_filter, Multiset.mem_singleton]
        constructor
        · rintro ⟨hb, hbi⟩
          obtain ⟨j, hj⟩ := mem_ofFn.1 (_root_.Sym.mem_coe.1 hb)
          have hji : j = i := by
            by_contra hne
            exact Set.disjoint_left.1 (h hne) ⟨x j, hj⟩ hbi
          simpa [hji] using hj.symm
        · rintro rfl
          exact ⟨_root_.Sym.mem_coe.2 (mem_ofFn.2 ⟨i, rfl⟩), Set.mem_range_self (x i)⟩
      rw [hfilter]
      simp
    · intro hcount
      have hex : ∀ i, ∃ a, a ∈ w ∧ a ∈ Set.range (f i) := by
        intro i
        have hpos : 0 < Multiset.card
            (Multiset.filter (· ∈ Set.range (f i)) (w : Multiset α)) := by
          rw [hcount i]
          exact Nat.zero_lt_succ 0
        obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
        exact ⟨a, (_root_.Sym.mem_coe.1 (Multiset.mem_filter.1 ha).1),
          (Multiset.mem_filter.1 ha).2⟩
      choose a ha using hex
      have haw : ∀ i, a i ∈ w := fun i => (ha i).1
      have har : ∀ i, a i ∈ Set.range (f i) := fun i => (ha i).2
      have hainj : Function.Injective a := by
        intro i j hij
        by_contra hne
        exact Set.disjoint_left.1 (h hne) (har i) (hij.symm ▸ har j)
      choose x hx using har
      have hnodup : (↑(List.ofFn a) : Multiset α).Nodup := List.nodup_ofFn.2 hainj
      have hle : (↑(List.ofFn a) : Multiset α) ≤ (w : Multiset α) :=
        (Multiset.le_iff_subset hnodup).2 fun b hb => by
          rw [← coe_ofFn] at hb
          obtain ⟨i, hi⟩ := mem_ofFn.1 (_root_.Sym.mem_coe.1 hb)
          exact _root_.Sym.mem_coe.2 (hi ▸ haw i)
      have heq : (↑(List.ofFn a) : Multiset α) = (w : Multiset α) :=
        Multiset.eq_of_le_of_card_le hle (by simp)
      have hofa : ofFn a = w := Sym.coe_injective (by simpa using heq)
      refine ⟨x, ?_⟩
      exact (congrArg ofFn (funext hx)).trans hofa

end Sym

end TauCeti
end -- closes the original EOF section from source line 27
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Sym/Disjoint.lean -/

/- BEGIN SOURCE: TauCeti/Topology/Sym/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The symmetric power of a topological space

The `n`-th symmetric power `Sym α n` of a type is the type of unordered `n`-tuples of points of
`α`. It is the quotient of the space `Fin n → α` of ordered tuples by the permutation action, and
this file gives it the corresponding quotient topology, together with the API that a quotient
topology is used through: the quotient map is continuous, and a map out of `Sym α n` is continuous
exactly when its composition with the quotient map is.

The quotient map is `TauCeti.Sym.ofFn` of `TauCeti/Data/Sym/Basic.lean`, which reads an ordered
tuple as an unordered one; the `Fin n → α` form is the one that carries a product topology, so it
is what the quotient topology is defined against. Its surjectivity and the description
`TauCeti.Sym.ofFn_eq_ofFn_iff` of its fibres as the orbits of the permutation action are the two
facts about it used below.

## Main declarations

* `TauCeti.Sym.preimage_image_ofFn`: the saturation of a set of ordered tuples under `ofFn` is the
  union of its reindexings.
* `TauCeti.Sym.instTopologicalSpace`: the quotient topology on `Sym α n`, coinduced along `ofFn`.
* `TauCeti.Sym.isQuotientMap_ofFn`, `TauCeti.Sym.continuous_ofFn` and
  `TauCeti.Sym.continuous_iff_comp_ofFn`: the resulting quotient-map API.
* `TauCeti.Sym.isOpenMap_ofFn`, `TauCeti.Sym.isClosedMap_ofFn` and
  `TauCeti.Sym.isOpenQuotientMap_ofFn`: the quotient map is open and closed, the permutation group
  being finite.
* `TauCeti.Sym.continuous_map`, `TauCeti.Sym.isOpenMap_map` and
  `TauCeti.Sym.isOpenEmbedding_map`: the `n`-th symmetric power of a continuous, open, or open
  embedding map is again one; in particular the symmetric power of an open subspace is an open
  subspace of the symmetric power.
* `TauCeti.Sym.isOpen_setOf_forall_mem`: the tuples with all their points in an open set form an
  open set.
* `TauCeti.Sym.continuous_append` and `TauCeti.Sym.isOpenMap_append`: concatenation of symmetric
  powers is continuous and open.
* `TauCeti.Sym.instCompactSpace` and `TauCeti.Sym.instT2Space`: the symmetric power of a compact
  space is compact, and that of a Hausdorff space is Hausdorff.

Lane F4.1 of the analytic Heegaard Floer roadmap needs `Sym^g(Σ)` as a space before it can be
given a complex structure; this file supplies the underlying topology, and
`TauCeti/Analysis/Polynomial/SymmetricPower.lean` identifies it, over an algebraically closed
normed field, with affine space through the elementary symmetric functions.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {α β : Type*} {m n : ℕ}

/-! ### The fibres of the quotient map -/

/-- The saturation of a set of ordered tuples under `ofFn` is the union of its reindexings. -/
theorem preimage_image_ofFn (s : Set (Fin n → α)) :
    ofFn ⁻¹' (ofFn '' s) = ⋃ σ : Equiv.Perm (Fin n), (· ∘ σ) ⁻¹' s := by
  first
  | ext g
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨f, hf, hfg⟩
      obtain ⟨σ, rfl⟩ := ofFn_eq_ofFn_iff.1 hfg
      exact ⟨σ.symm, by simpa [Function.comp_assoc] using hf⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨g ∘ σ, hσ, ofFn_comp_perm σ g⟩

/-! ### The quotient topology -/

variable [TopologicalSpace α] [TopologicalSpace β]

/-- The `n`-th symmetric power of a topological space carries the quotient topology of the
permutation action on ordered `n`-tuples, presented as the topology coinduced along
`TauCeti.Sym.ofFn`. -/
instance instTopologicalSpace : TopologicalSpace (Sym α n) :=
  .coinduced ofFn inferInstance

/-- The quotient map onto the symmetric power is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofFn : Continuous (ofFn : (Fin n → α) → Sym α n) :=
  continuous_coinduced_rng

/-- `ofFn` presents `Sym α n` as a topological quotient of `Fin n → α`. -/
theorem isQuotientMap_ofFn : IsQuotientMap (ofFn : (Fin n → α) → Sym α n) :=
  ⟨⟨rfl⟩, ofFn_surjective⟩

/-- A map out of a symmetric power is continuous exactly when the associated map on ordered
tuples is; this is the universal property of the quotient topology. -/
theorem continuous_iff_comp_ofFn {g : Sym α n → β} : Continuous g ↔ Continuous (g ∘ ofFn) :=
  isQuotientMap_ofFn.continuous_iff

/-- The quotient map onto the symmetric power is open: the saturation of an open set is the union
of its reindexings, each of them open. -/
theorem isOpenMap_ofFn : IsOpenMap (ofFn : (Fin n → α) → Sym α n) := fun s hs => by
  rw [← isQuotientMap_ofFn.isCoinducing.isOpen_preimage, preimage_image_ofFn]
  exact isOpen_iUnion fun σ => hs.preimage (Pi.continuous_precomp σ)

/-- The quotient map onto the symmetric power is closed: the saturation of a closed set is the
union of its reindexings, a *finite* union of closed sets. -/
theorem isClosedMap_ofFn : IsClosedMap (ofFn : (Fin n → α) → Sym α n) := fun s hs => by
  rw [← isQuotientMap_ofFn.isCoinducing.isClosed_preimage, preimage_image_ofFn]
  exact isClosed_iUnion_of_finite fun σ => hs.preimage (Pi.continuous_precomp σ)

/-- The quotient map onto the symmetric power is an open quotient map. -/
theorem isOpenQuotientMap_ofFn : IsOpenQuotientMap (ofFn : (Fin n → α) → Sym α n) :=
  .of_isOpenMap_isQuotientMap isOpenMap_ofFn isQuotientMap_ofFn

/-! ### Functoriality -/

/-- The symmetric power of a continuous map is continuous. -/
@[continuity, fun_prop]
theorem continuous_map {f : α → β} (hf : Continuous f) :
    Continuous (Sym.map f : Sym α n → Sym β n) := by
  first
  | rw [continuous_iff_comp_ofFn, map_comp_ofFn]
    exact continuous_ofFn.comp (Continuous.piMap fun _ => hf)

/-- The symmetric power of an open map is open. -/
theorem isOpenMap_map {f : α → β} (hf : IsOpenMap f) :
    IsOpenMap (Sym.map f : Sym α n → Sym β n) := by
  first
  | rw [isOpenQuotientMap_ofFn.isOpenMap_iff, map_comp_ofFn]
    exact isOpenMap_ofFn.comp (IsOpenMap.piMap (fun _ => hf) (by simp))

/-- The symmetric power of an open embedding is an open embedding: the `n`-th symmetric power of
an open subspace is an open subspace of the `n`-th symmetric power. -/
theorem isOpenEmbedding_map {f : α → β} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (Sym.map f : Sym α n → Sym β n) :=
  .of_continuous_injective_isOpenMap (continuous_map hf.continuous)
    (Sym.map_injective hf.injective n) (isOpenMap_map hf.isOpenMap)

/-- The unordered tuples all of whose points lie in an open set form an open subset of the
symmetric power: the range of the symmetric power of the inclusion of that open set. -/
theorem isOpen_setOf_forall_mem {V : Set α} (hV : IsOpen V) :
    IsOpen {s : Sym α n | ∀ a ∈ s, a ∈ V} := by
  first
  | convert (isOpenEmbedding_map (n := n) hV.isOpenEmbedding_subtypeVal).isOpen_range using 1
    ext s
    rw [Set.mem_ofPred_eq, mem_range_map, Subtype.range_coe]

omit [TopologicalSpace α] in
/-- Concatenation of unordered tuples read on ordered ones: it is presented by `Fin.append`, as an
equality of maps out of pairs of ordered tuples. -/
private theorem append_comp_prodMap_ofFn :
    (fun p : Sym α n × Sym α m => p.1.append p.2) ∘ Prod.map ofFn ofFn =
      ofFn ∘ fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
  first
  | funext p
    obtain ⟨f, g⟩ := p
    exact (ofFn_fin_append f g).symm

/-- Concatenation of two symmetric-power points is continuous. -/
@[continuity, fun_prop]
theorem continuous_append :
    Continuous fun p : Sym α n × Sym α m => p.1.append p.2 := by
  first
  | rw [← (isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).continuous_comp_iff,
      append_comp_prodMap_ofFn]
    exact continuous_ofFn.comp (Fin.continuous_append n m)

/-- Concatenation of two symmetric-power points is an open map. -/
theorem isOpenMap_append :
    IsOpenMap fun p : Sym α n × Sym α m => p.1.append p.2 := by
  first
  | have hcoe : ⇑(Fin.appendHomeomorph (X := α) n m) =
        fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
      funext q i
      simp
    rw [(isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).isOpenMap_iff,
      append_comp_prodMap_ofFn, ← hcoe]
    exact isOpenMap_ofFn.comp (Fin.appendHomeomorph n m).isOpenMap

/-! ### Separation and compactness -/

/-- The symmetric power of a compact space is compact, being a continuous image of a finite power
of that space. -/
instance instCompactSpace [CompactSpace α] : CompactSpace (Sym α n) :=
  ⟨by
    rw [← Set.image_univ_of_surjective (ofFn_surjective (α := α) (n := n))]
    exact isCompact_univ.image continuous_ofFn⟩

/-- The symmetric power of a Hausdorff space is Hausdorff: `ofFn` is an open quotient map, and the
relation it induces is the finite union, over permutations, of the graphs of the reindexing maps,
hence closed. -/
instance instT2Space [T2Space α] : T2Space (Sym α n) := by
  first
  | rw [t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_ofFn]
    have hrel : {q : (Fin n → α) × (Fin n → α) | ofFn q.1 = ofFn q.2} =
        ⋃ σ : Equiv.Perm (Fin n), {q : (Fin n → α) × (Fin n → α) | q.1 ∘ σ = q.2} := by
      ext q
      simpa using ofFn_eq_ofFn_iff
    rw [hrel]
    exact isClosed_iUnion_of_finite fun σ =>
      isClosed_eq ((Pi.continuous_precomp σ).comp continuous_fst) continuous_snd

end Sym

end TauCeti
end -- closes the original EOF section from source line 56
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Topology/Sym/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Topology/Sym/Disjoint.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Disjoint open embeddings into a symmetric power

Given open embeddings with pairwise disjoint ranges, ordered tuples mapped pointwise through those
embeddings embed openly as unordered tuples. In particular, given pairwise disjoint open
neighbourhoods `U i` of `n` distinct points, their product is an open subspace of `Sym α n`;
obtaining such neighbourhoods in a Hausdorff space is a separate step. The proof comes from
`TauCeti.Sym.ofFn` being continuous and open together with `IsOpenEmbedding.piMap`.

Splitting over the distinct points of a tuple, with the multiplicities as the degrees, is how the
symmetric power of a surface is charted: a neighbourhood of a tuple with
distinct points `z₁, …, z_k` of multiplicities `n₁, …, n_k` is a product of the symmetric powers
`Sym^{n_j}` of disjoint coordinate discs, each of which is an open subspace of affine space by
`TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`. Lane F4.1 of the analytic Heegaard Floer
roadmap needs exactly this to give `Sym^g(Σ)` its complex structure, after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1). The coefficient homeomorphism
is in `TauCeti/Analysis/Polynomial/SymmetricPower.lean`, while the charts and charted structure are
in `TauCeti/Geometry/Manifold/SymmetricPower.lean`. Family-level concatenation along disjoint open
sets, and the Hausdorff separation producing the family that a given tuple needs, are in
`TauCeti/Topology/Sym/Family.lean`.

## Main declaration

* `TauCeti.Sym.isOpenEmbedding_ofFn_map`: open embeddings with pairwise disjoint ranges induce an
  open embedding from their product into the symmetric power.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {α : Type*} [TopologicalSpace α] {n : ℕ}

/-! ### Tuples mapped into pairwise disjoint open ranges -/

/-- **Away from the diagonal the symmetric power is a product.** Open embeddings with pairwise
disjoint ranges induce an open embedding from their product into the symmetric power. Applied to
subtype inclusions, this says conditionally that given pairwise disjoint open neighbourhoods `U i`
of `n` distinct points, their product is an open subspace of `Sym α n`; constructing such a family
in a Hausdorff space is a separate step. -/
theorem isOpenEmbedding_ofFn_map {X : Fin n → Type*} [∀ i, TopologicalSpace (X i)]
    (f : ∀ i, X i → α) (hf : ∀ i, IsOpenEmbedding (f i))
    (h : Pairwise (Function.onFun Disjoint fun i => Set.range (f i))) :
    IsOpenEmbedding fun x : ∀ i, X i => ofFn fun i => f i (x i) := by
  first
  | refine .of_continuous_injective_isOpenMap ?_
      (ofFn_map_injective f (fun i => (hf i).injective) h) ?_
    · exact continuous_ofFn.comp (Continuous.piMap fun i => (hf i).continuous)
    · exact isOpenMap_ofFn.comp (IsOpenEmbedding.piMap hf).isOpenMap

end Sym

end TauCeti
end -- closes the original EOF section from source line 39
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Topology/Sym/Disjoint.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Polynomial/SymmetricPower.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The elementary symmetric chart is a homeomorphism

`TauCeti.Sym.coeffEquiv` presents the `n`-th symmetric power of an algebraically closed field `K`
as the affine space `Fin n → K`, by sending an unordered `n`-tuple to the lower coefficients of the
monic polynomial having it as its root multiset. That equivalence is pure algebra. This file proves
that, when `K` is a proper normed field — `ℂ` being the case of interest — it is a
**homeomorphism** for the quotient topology of `TauCeti.Sym.instTopologicalSpace`.

Both halves are elementary, but neither is formal:

* the coefficients are polynomial in the roots, so the chart is continuous;
* the roots are *not* a polynomial function of the coefficients, and continuity of the inverse is
  the classical statement that the roots of a monic polynomial depend continuously on its
  coefficients. It is obtained here from **Cauchy's bound** `Polynomial.cauchyBound`: a root of a
  monic polynomial is bounded by its coefficients, so the coefficient map is proper, hence closed,
  and a closed continuous bijection is a homeomorphism.

## Main declarations

* `TauCeti.Sym.continuous_coeffEquiv_comp_ofFn`: the coefficients depend continuously on an
  ordered tuple of roots.
* `TauCeti.Polynomial.analyticAt_coeff_prod_X_sub_C` and
  `TauCeti.Sym.analyticAt_coeffEquiv_ofFn`: the same forward coefficient map is analytic over any
  nontrivially normed field.
* `TauCeti.Sym.norm_le_norm_coeffEquiv_ofFn_add_one`: Cauchy's bound on the symmetric power, that
  an ordered tuple is bounded by one more than the norm of its coefficient tuple.
* `TauCeti.Sym.isProperMap_coeffEquiv_comp_ofFn`: consequently the coefficient map
  `(Fin n → K) → (Fin n → K)` is proper.
* `TauCeti.Sym.coeffHomeomorph`: the **elementary symmetric chart** `Sym K n ≃ₜ (Fin n → K)`.
* `TauCeti.Sym.eventually_exists_ofFn_eq_coeffEquiv_symm`: its inverse read on ordered tuples,
  that nearby coefficient tuples come from ordered tuples close coordinate by coordinate; this is
  continuity of roots with multiplicity, stated for polynomials in
  `TauCeti/Analysis/Polynomial/ContinuityOfRoots/Basic.lean`.
* `TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`: the chart induced by an open coordinate
  embedding, whose symmetric power is an open subspace of affine space.
* `TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_ofFn_map`: the chart on a product mapped into
  pairwise disjoint open coordinate ranges, one point in each.
* `TauCeti.Sym.analyticOnNhd_coeffEquiv_map_eval_coeffEquiv_symm`: applying a univariate
  polynomial to every point induces an analytic map in coefficient coordinates, including at
  tuples where points collide.

Lane F4.1 of the analytic Heegaard Floer roadmap opens with "`Sym^g(Σ)` geometry: smooth complex
structure (elementary symmetric functions)", after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1): a holomorphic coordinate on the
surface identifies a neighbourhood in `Sym^g(Σ)` with an open subset of `Sym^g(ℂ)`, and the chart
below is what makes that a chart on a topological manifold; the charted structure is assembled
from it in `TauCeti/Geometry/Manifold/SymmetricPower.lean`. Away from the diagonal the continuity
proved here is upgraded to analyticity in
`TauCeti/Analysis/Polynomial/SimpleRoots/Basic.lean`, and its assembly across the blocks of an
elementary-symmetric chart, including colliding points over `ℂ`, is in
`TauCeti/Analysis/Polynomial/RootSum/Family.lean`. The complex atlas is
`TauCeti.isManifold_symChartedSpace`; the tangent-space criterion for products of locally
parametrized immersed curves is `TauCeti.isMaximalTotallyReal_range_fderiv_symChartAt_ofFn`.
For transition maps at colliding
tuples, this file also handles the case induced by a univariate polynomial; the general
holomorphic case over `ℂ` is
`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm_of_analyticAt` in
`TauCeti/Analysis/Polynomial/RootSum.lean`.
-/

public section

-- `Polynomial` is opened outside `namespace TauCeti` so that it names Mathlib's namespace rather
-- than `TauCeti.Polynomial`, which the import above populates.
open Filter Polynomial Topology

namespace TauCeti

namespace Polynomial

/-! ### Analyticity of the coefficients -/

section Analyticity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The image of the monic polynomial with lower coefficients `c` under a linear map depends
analytically on `c`: it is affine in `c`. -/
theorem analyticAt_linearMap_monicOfCoeff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ} (Λ : 𝕜[X] →ₗ[𝕜] F) (c₀ : Fin n → 𝕜) :
    AnalyticAt 𝕜 (fun c => Λ (monicOfCoeff c)) c₀ := by
  first
  | have h : (fun c : Fin n → 𝕜 => Λ (monicOfCoeff c)) =
        fun c => Λ (X ^ n) + ∑ i : Fin n, c i • Λ (monomial (i : ℕ) 1) := by
      funext c
      have hp : monicOfCoeff c = X ^ n + ∑ i : Fin n, c i • monomial (i : ℕ) (1 : 𝕜) :=
        Polynomial.funext fun z => by
          simp [eval_monicOfCoeff, eval_finsetSum, smul_monomial]
      simp [hp, map_sum, map_smul]
    rw [h]
    exact analyticAt_const.add (Finset.univ.analyticAt_fun_sum fun i _ =>
      ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).analyticAt c₀).smul
        analyticAt_const)

/-- The coefficients of `∏ i ∈ s, (X - C (v i))` depend analytically on the tuple `v` of roots.

This is the elementary half of the chart, and the analytic counterpart of
`TauCeti.Polynomial.continuous_coeff_prod_X_sub_C`: each coefficient is, up to sign, an elementary
symmetric function of the roots, so the analyticity of the ring operations is all that is used. -/
theorem analyticAt_coeff_prod_X_sub_C {ι : Type*} [Fintype ι] (s : Finset ι) (k : ℕ)
    (v₀ : ι → 𝕜) : AnalyticAt 𝕜 (fun v : ι → 𝕜 => (∏ i ∈ s, (X - C (v i))).coeff k) v₀ := by
  first
  | classical
    have hproj : ∀ i : ι, AnalyticAt 𝕜 (fun v : ι → 𝕜 => v i) v₀ := fun i =>
      (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).analyticAt _
    induction s using Finset.induction_on generalizing k with
    | empty =>
      simp only [Finset.prod_empty]
      exact analyticAt_const
    | @insert a s ha ih =>
      cases k with
      | zero =>
        have hpt : (fun v : ι → 𝕜 => (∏ i ∈ insert a s, (X - C (v i))).coeff 0) =
            fun v => -v a * (∏ i ∈ s, (X - C (v i))).coeff 0 := by
          funext v
          rw [Finset.prod_insert ha, mul_coeff_zero]
          simp
        rw [hpt]
        exact (hproj a).neg.mul (ih 0)
      | succ k =>
        have hpt : (fun v : ι → 𝕜 => (∏ i ∈ insert a s, (X - C (v i))).coeff (k + 1)) =
            fun v => (∏ i ∈ s, (X - C (v i))).coeff k
              - v a * (∏ i ∈ s, (X - C (v i))).coeff (k + 1) := by
          funext v
          rw [Finset.prod_insert ha, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
        rw [hpt]
        exact (ih k).sub ((hproj a).mul (ih (k + 1)))

end Analyticity

end Polynomial

namespace Sym

/-! ### Analyticity of the coefficients -/

section Analyticity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsAlgClosed 𝕜] {n : ℕ}

/-- The elementary symmetric chart is analytic in an ordered presentation of the tuple: by Vieta's
formulas its coordinates are, up to sign, the elementary symmetric polynomials of the ordered
tuple. -/
theorem analyticAt_coeffEquiv_ofFn (v₀ : Fin n → 𝕜) :
    AnalyticAt 𝕜 (fun v : Fin n → 𝕜 => coeffEquiv 𝕜 n (ofFn v)) v₀ := by
  first
  | refine AnalyticAt.pi fun i => ?_
    simp only [coeffEquiv_ofFn_apply]
    exact Polynomial.analyticAt_coeff_prod_X_sub_C _ _ _

/-- **Applying a polynomial to a tuple is analytic in elementary symmetric coefficients.**
The coordinate representation is analytic everywhere, including at coefficient tuples whose
corresponding points collide. -/
theorem analyticOnNhd_coeffEquiv_map_eval_coeffEquiv_symm (q : 𝕜[X]) :
    AnalyticOnNhd 𝕜 (fun c => coeffEquiv 𝕜 n
      (Sym.map (fun z => eval z q) ((coeffEquiv 𝕜 n).symm c))) Set.univ := by
  first
  | obtain ⟨Q, hQ⟩ := exists_coeffEquiv_map_eval_coeffEquiv_symm_eq_eval
      (K := 𝕜) (n := n) q
    refine fun c _ => AnalyticAt.congr (f := fun c i => MvPolynomial.eval c (Q i))
      (AnalyticAt.pi fun i => ?_) ?_
    · have h := AnalyticOnNhd.eval_continuousLinearMap
        (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) (Q i) c (Set.mem_univ c)
      simp only [ContinuousLinearMap.id_apply] at h
      exact h
    · filter_upwards with c using (hQ c).symm

end Analyticity

section Chart

variable {K : Type*} [NormedField K] [IsAlgClosed K] {n : ℕ}

/-- The coefficient map `(Fin n → K) → (Fin n → K)`, the elementary symmetric chart read on ordered
tuples, is continuous. -/
@[continuity, fun_prop]
theorem continuous_coeffEquiv_comp_ofFn :
    Continuous fun f : Fin n → K => coeffEquiv K n (ofFn f) := by
  first
  | refine continuous_pi fun i => ?_
    simp only [coeffEquiv_ofFn_apply]
    exact Polynomial.continuous_coeff_prod_X_sub_C Finset.univ i

/-- **Cauchy's bound** on the symmetric power: the points of an unordered tuple are bounded by one
more than the sup-norm of its elementary symmetric chart, because each of them is a root of the
monic polynomial those coordinates present. -/
theorem norm_le_norm_coeffEquiv_ofFn_add_one (f : Fin n → K) :
    ‖f‖ ≤ ‖coeffEquiv K n (ofFn f)‖ + 1 := by
  first
  | have hnonneg : (0 : ℝ) ≤ ‖coeffEquiv K n (ofFn f)‖ + 1 := by positivity
    refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun j => ?_
    have hmonic : (toMonic (ofFn f) : K[X]).Monic := monic_toMonic _
    have hroot : (toMonic (ofFn f) : K[X]).IsRoot (f j) :=
      mem_iff_isRoot.1 (_root_.Sym.mem_coe.2 (mem_ofFn.2 ⟨j, rfl⟩))
    have hcauchy := hroot.norm_lt_cauchyBound hmonic.ne_zero
    have hbound : cauchyBound (toMonic (ofFn f) : K[X]) ≤ ‖coeffEquiv K n (ofFn f)‖₊ + 1 := by
      have hsup : ((Finset.range n).sup fun i => ‖(toMonic (ofFn f) : K[X]).coeff i‖₊)
          ≤ ‖coeffEquiv K n (ofFn f)‖₊ := by
        refine Finset.sup_le fun i hi => ?_
        rw [Finset.mem_range] at hi
        have hcoord := nnnorm_le_pi_nnnorm (coeffEquiv K n (ofFn f)) ⟨i, hi⟩
        rwa [coeffEquiv_apply_eq_coeff] at hcoord
      rw [cauchyBound, hmonic.leadingCoeff, nnnorm_one, div_one, natDegree_toMonic]
      exact add_le_add hsup le_rfl
    have : ‖f j‖₊ < ‖coeffEquiv K n (ofFn f)‖₊ + 1 := hcauchy.trans_le hbound
    simpa using (NNReal.coe_lt_coe.2 this).le

variable [ProperSpace K]

/-- The coefficient map is proper: bounded coefficients force bounded roots, by Cauchy's bound. -/
theorem isProperMap_coeffEquiv_comp_ofFn :
    IsProperMap fun f : Fin n → K => coeffEquiv K n (ofFn f) := by
  first
  | rw [isProperMap_iff_tendsto_cocompact]
    refine ⟨continuous_coeffEquiv_comp_ofFn, ?_⟩
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_atTop_mono (fun f => ?_)
      (tendsto_atTop_add_const_right _ (-1) tendsto_norm_cobounded_atTop)
    have := norm_le_norm_coeffEquiv_ofFn_add_one f
    linarith

/-- The elementary symmetric chart is a closed map. -/
theorem isClosedMap_coeffEquiv : IsClosedMap (coeffEquiv K n) := by
  first
  | intro C hC
    have himage : coeffEquiv K n '' C =
        (fun f : Fin n → K => coeffEquiv K n (ofFn f)) '' (ofFn ⁻¹' C) := by
      rw [← Set.image_image (coeffEquiv K n) ofFn (ofFn ⁻¹' C),
        Set.image_preimage_eq _ ofFn_surjective]
    rw [himage]
    exact isProperMap_coeffEquiv_comp_ofFn.isClosedMap _ (hC.preimage continuous_ofFn)

variable (K n)

/-- The **elementary symmetric chart** on the `n`-th symmetric power of a proper algebraically
closed normed field is a homeomorphism onto affine `n`-space: an unordered `n`-tuple is determined,
continuously and with continuous inverse, by the lower coefficients of its monic polynomial.

Continuity of the inverse is the classical continuity of the roots of a monic polynomial in its
coefficients; it comes from `TauCeti.Sym.isProperMap_coeffEquiv_comp_ofFn`, and hence from Cauchy's
bound. -/
noncomputable def coeffHomeomorph : Sym K n ≃ₜ (Fin n → K) :=
  (coeffEquiv K n).toHomeomorphOfContinuousClosed
    (continuous_iff_comp_ofFn.2 continuous_coeffEquiv_comp_ofFn) isClosedMap_coeffEquiv

/-- The chart homeomorphism is the chart equivalence. -/
@[simp]
theorem coeffHomeomorph_apply (s : Sym K n) : coeffHomeomorph K n s = coeffEquiv K n s := by
  first
  | simp [coeffHomeomorph]

/-- The inverse chart homeomorphism is the inverse chart equivalence. -/
@[simp]
theorem coeffHomeomorph_symm_apply (f : Fin n → K) :
    ((coeffHomeomorph K n).symm f : Sym K n) = (coeffEquiv K n).symm f := by
  first
  | simp [coeffHomeomorph]

variable {K n}

/-- **Continuity of roots on ordered tuples.** Every coefficient tuple close enough to that of the
ordered tuple `a` is the coefficient tuple of an ordered tuple `b` with each `b i` close to `a i`.

This is the continuity of `(coeffHomeomorph K n).symm`, read through the open quotient map
`TauCeti.Sym.ofFn`: it matches the roots with multiplicity, not merely each root to a nearby one. -/
theorem eventually_exists_ofFn_eq_coeffEquiv_symm (a : Fin n → K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in 𝓝 (coeffEquiv K n (ofFn a)),
      ∃ b : Fin n → K, ofFn b = (coeffEquiv K n).symm c ∧ ∀ i, ‖a i - b i‖ < ε := by
  first
  | have hnhds : ofFn '' Metric.ball a ε ∈
        𝓝 ((coeffHomeomorph K n).symm (coeffHomeomorph K n (ofFn a))) := by
      rw [Homeomorph.symm_apply_apply]
      exact isOpenMap_ofFn.image_mem_nhds (Metric.ball_mem_nhds a hε)
    rw [← coeffHomeomorph_apply]
    filter_upwards [(coeffHomeomorph K n).symm.continuous.continuousAt.preimage_mem_nhds hnhds]
      with c ⟨b, hb, hbc⟩
    refine ⟨b, by simpa using hbc, fun i => ?_⟩
    rw [norm_sub_rev, ← dist_eq_norm]
    exact (dist_pi_lt_iff hε).1 hb i

/-- **The elementary symmetric chart on a coordinate patch.** An open coordinate embedding into
`K` induces an open embedding of its `n`-th symmetric power into affine `n`-space, charted by the
elementary symmetric functions of its points.

This is the local model of the symmetric power of a Riemann surface at a tuple all of whose points
lie in one coordinate patch; a general tuple is split into such groups by
`TauCeti.Sym.isOpenEmbedding_sumSubtype`. -/
theorem isOpenEmbedding_coeffEquiv_comp_map {X : Type*} [TopologicalSpace X] {f : X → K}
    (hf : IsOpenEmbedding f) :
    IsOpenEmbedding fun s : Sym X n => coeffEquiv K n (Sym.map f s) := by
  first
  | have hemb := (coeffHomeomorph K n).isOpenEmbedding.comp
      (isOpenEmbedding_map (n := n) hf)
    simpa [Function.comp_def] using hemb

/-- **The elementary symmetric chart away from the diagonal.** For open coordinate embeddings with
pairwise disjoint ranges, one point in each, the elementary symmetric functions chart the tuple of
points: their product is an open subspace of affine `n`-space.

For `Sym^g` of a Riemann surface this is the chart in which the totally real torus of a Heegaard
diagram, a product of `g` curves lying in disjoint pieces, is read. -/
theorem isOpenEmbedding_coeffEquiv_comp_ofFn_map {X : Fin n → Type*}
    [∀ i, TopologicalSpace (X i)] (f : ∀ i, X i → K)
    (hf : ∀ i, IsOpenEmbedding (f i))
    (h : Pairwise (Function.onFun Disjoint fun i => Set.range (f i))) :
    IsOpenEmbedding fun x : ∀ i, X i => coeffEquiv K n (ofFn fun i => f i (x i)) := by
  first
  | have hemb := (coeffHomeomorph K n).isOpenEmbedding.comp (isOpenEmbedding_ofFn_map f hf h)
    simpa [Function.comp_def] using hemb

end Chart

end Sym

end TauCeti
end -- closes the original EOF section from source line 80
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Polynomial/SymmetricPower.lean -/

/- BEGIN SOURCE: TauCeti/Topology/MetricSpace/SeparatedBalls.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Small closed balls around finitely many points are separated

Around finitely many points of a metric space, closed balls of a small enough common radius lie in
prescribed neighbourhoods of their centres and are pairwise far apart: the radius is less than
half the distance between any two distinct centres, so the balls are disjoint and no point of one
ball lies on the boundary sphere of another. This is the geometric input for splitting a sum over
points near the centres as a sum over the balls, as in the contour-integral computation of sums
over the roots of a polynomial.

## Main declarations

* `TauCeti.exists_pos_closedBall_subset_and_lt_dist`: a common radius that is small enough for
  every centre at once.
* `TauCeti.eq_of_dist_lt_of_dist_lt`: two such centres within the radius of a common point
  coincide.
-/

public section

open Filter Metric Topology

namespace TauCeti

variable {X : Type*} [MetricSpace X]

/-- Around finitely many points, closed balls of a small enough common radius lie in prescribed
neighbourhoods of their centres and are pairwise far apart: twice the radius is less than the
distance between any two distinct centres. -/
theorem exists_pos_closedBall_subset_and_lt_dist {T : Finset X} {U : X → Set X}
    (hU : ∀ w ∈ T, U w ∈ 𝓝 w) :
    ∃ r > 0, (∀ w ∈ T, closedBall w r ⊆ U w) ∧ ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' := by
  first
  | have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, closedBall w r ⊆ U w :=
      (eventually_all_finset T).2 fun w hw => eventually_closedBall_subset (hU w hw)
    have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' := by
      refine (eventually_all_finset T).2 fun w _ => (eventually_all_finset T).2 fun w' _ => ?_
      by_cases hww : w = w'
      · exact Eventually.of_forall fun _ h => absurd hww h
      · exact (eventually_lt_nhds (half_pos (dist_pos.2 hww))).mono fun r hr _ => by linarith
    obtain ⟨r, ⟨h1r, h2r⟩, hr⟩ :=
      (((h1.and h2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists
        (f := 𝓝[>] (0 : ℝ))
    exact ⟨r, hr, h1r, h2r⟩

/-- Two points that are either equal or more than `2 * r` apart are equal if both lie within `r`
of a common point. -/
theorem eq_of_dist_lt_of_dist_lt {Y : Type*} [PseudoMetricSpace Y] {w w' y : Y} {r : ℝ}
    (hsep : w ≠ w' → 2 * r < dist w w') (h : dist y w < r) (h' : dist y w' < r) : w = w' := by
  first
  | by_contra hne
    linarith [hsep hne, dist_triangle_left w w' y]

end TauCeti

end
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Topology/MetricSpace/SeparatedBalls.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Polynomial/ContinuityOfRoots/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Continuity of the roots of a polynomial, with multiplicities

Mathlib's `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` shows that each root of a monic
polynomial `f` has a root of every nearby monic polynomial `g` close to it. That does not control
multiplicities: a double root of `f` could be approximated by a single root of `g`, the second
root of `g` going elsewhere. This file proves the multiplicity-sensitive statement over a proper
algebraically closed normed field, `ℂ` being the case of interest: the roots of `g`, counted with
multiplicity, can be **matched bijectively** with those of `f` so that matched roots are close.

The input is `TauCeti.Sym.eventually_exists_ofFn_eq_coeffEquiv_symm`, the continuity of the inverse
of the elementary symmetric chart `TauCeti.Sym.coeffHomeomorph`, which comes from Cauchy's bound
`Polynomial.cauchyBound` through properness of the coefficient map. Nothing here chooses a
continuous labelling of the roots; the matching is made separately for each nearby polynomial.

## Main results

* `Polynomial.Monic.exists_prod_X_sub_C_norm_sub_lt`: **continuity of roots.** For monic `f` and
  `ε > 0` there is `δ > 0` such that every monic `g` of the same degree whose coefficients are
  `δ`-close to those of `f` below their degree admits enumerations `a`, `b` of their roots, with
  multiplicity, satisfying `‖a i - b i‖ < ε`.
* `Polynomial.Monic.exists_prod_X_sub_C_norm_sub_lt_iff`: for split monic `f` and `g` over a
  seminormed domain, when the `ε`-discs around the distinct roots of `f` are disjoint, a matching
  exists exactly when every disc contains as many roots of `g` as the multiplicity of its centre,
  and no root of `g` lies outside the discs.
* `Polynomial.Monic.exists_countP_roots_mem_ball_eq_rootMultiplicity`: the resulting disc form of
  continuity of roots.
* `Polynomial.Monic.exists_rel_roots_norm_sub_lt`: the multiset form of continuity of roots, the
  root multisets of `f` and `g` being related by `Multiset.Rel` for `‖z - w‖ < ε`.
* `Polynomial.rel_roots_iff_countP_roots_mem_ball`: when the `ε`-discs around the distinct roots of
  `f` are disjoint, the multiset form and the disc form are equivalent.
* `Polynomial.eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt`: the matching for a family of
  polynomials of fixed degree with continuous coefficients, normalized by its nonvanishing leading
  coefficient.
* `Polynomial.eventually_rel_roots_norm_sub_lt`: the multiset form of the same matching.
* `Polynomial.eventually_exists_bijOn_roots_toFinset`: if moreover no nearby member of the family
  has more distinct roots than the central one, the distinct roots of nearby members correspond
  bijectively to those of the central one, with matched roots close and of equal multiplicity.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of the roots of a polynomial with respect to its coefficients).
-/

public section

open Filter Metric Topology TauCeti

namespace Polynomial

section Chart

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A monic polynomial of degree `n` is the product of the linear factors of the ordered tuple
presenting its roots in the elementary symmetric chart. -/
private theorem prod_X_sub_C_eq_of_ofFn_eq {n : ℕ} {p : K[X]} (hp : p.Monic)
    (hdeg : p.natDegree = n) {a : Fin n → K}
    (ha : Sym.ofFn a = (Sym.coeffEquiv K n).symm fun i => p.coeff i) :
    ∏ i, (X - C (a i)) = p := by
  first
  | rw [← Sym.toMonic_ofFn, ha, Sym.toMonic_coeffEquiv_symm,
      TauCeti.Polynomial.monicOfCoeff_coeff hp hdeg]

/-- A polynomial of degree `d` is its leading coefficient times the product of the linear factors of
the ordered tuple presenting, in the elementary symmetric chart, its normalized lower
coefficients. -/
private theorem C_mul_prod_X_sub_C_eq_of_ofFn_eq {d : ℕ} {p : K[X]} (hp : p.degree = d)
    {a : Fin d → K}
    (ha : Sym.ofFn a = (Sym.coeffEquiv K d).symm fun i => (p.coeff d)⁻¹ * p.coeff i) :
    C p.leadingCoeff * ∏ i, (X - C (a i)) = p := by
  first
  | have hnat : p.natDegree = d := natDegree_eq_of_degree_eq_some hp
    have hlead : p.coeff d = p.leadingCoeff := by rw [leadingCoeff, hnat]
    have hlc : p.leadingCoeff ≠ 0 := hlead ▸ coeff_ne_zero_of_eq_degree hp
    have hmonic : (C p.leadingCoeff⁻¹ * p).Monic :=
      monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
    have hdeg' : (C p.leadingCoeff⁻¹ * p).natDegree = d := by
      rw [natDegree_C_mul (inv_ne_zero hlc), hnat]
    rw [prod_X_sub_C_eq_of_ofFn_eq hmonic hdeg' (by simpa only [coeff_C_mul, hlead] using ha),
      ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]

end Chart

section Matching

variable {K : Type*} [SeminormedCommRing K] [IsDomain K]

open scoped Classical in
/-- **The multiset and disc forms of a matching agree.** Suppose the `ε`-discs around the distinct
roots of `f` are pairwise disjoint. Then the root multisets of `f` and `g` are related by
`Multiset.Rel` for the relation `‖z - w‖ < ε` exactly when each disc around a root `z` of `f`
contains `rootMultiplicity z f` roots of `g`, counted with multiplicity, and every root of `g` lies
in one of these discs. -/
theorem rel_roots_iff_countP_roots_mem_ball {f g : K[X]} {ε : ℝ}
    (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    f.roots.Rel (fun z w => ‖z - w‖ < ε) g.roots ↔
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  first
    -- a point of `K` is within `ε` of at most one root of `f`
  | have huniq : ∀ w ∈ g.roots, ∀ z ∈ f.roots, ∀ z' ∈ f.roots, ‖z - w‖ < ε → ‖z' - w‖ < ε →
        z = z' := by
      intro w _ z hz z' hz' h h'
      by_contra hne
      have := hsep z hz z' hz' hne
      have := norm_sub_le_norm_sub_add_norm_sub z w z'
      have := norm_sub_rev z' w
      linarith
    rw [Multiset.rel_iff_forall_countP_eq_count huniq]
    simp only [mem_ball, dist_eq_norm, norm_sub_rev _ (_ : K), count_roots]

open scoped Classical in
/-- **Matching roots versus counting them in discs.** Let `f` and `g` be split monic polynomials,
and suppose the `ε`-discs around the distinct roots of `f` are pairwise disjoint. Then the roots of
`f` and `g`, with multiplicity, can be enumerated so that matched roots are at distance less than
`ε` exactly when each disc around a root `z` of `f` contains `rootMultiplicity z f` roots of `g`,
counted with multiplicity, and every root of `g` lies in one of these discs. -/
theorem Monic.exists_prod_X_sub_C_norm_sub_lt_iff {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (hfs : f.Splits) (hgs : g.Splits) {ε : ℝ}
    (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    (∃ a b : Fin f.natDegree → K,
        f = ∏ i, (X - C (a i)) ∧ g = ∏ i, (X - C (b i)) ∧ ∀ i, ‖a i - b i‖ < ε) ↔
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  first
  | exact (hf.rel_roots_iff_exists_prod_X_sub_C hg hfs hgs).symm.trans
      (rel_roots_iff_countP_roots_mem_ball hsep)

/-- **Distinct roots under a matching of roots.** Let `a` and `b` enumerate the roots of `f` and
`g` with multiplicity, with `‖a i - b i‖ < ρ`, where the distinct roots of `f` are more than `2 * ρ`
apart. If `g` has at most as many distinct roots as `f`, then `a i ↦ b i` is a well-defined
bijection between the distinct roots, and it preserves multiplicities. -/
private theorem exists_bijOn_roots_toFinset_of_norm_sub_lt [DecidableEq K] {f g : K[X]} {d : ℕ}
    {a b : Fin d → K} {ρ : ℝ} (hf : f.roots = Finset.univ.val.map a)
    (hg : g.roots = Finset.univ.val.map b) (hab : ∀ i, ‖a i - b i‖ < ρ)
    (hsep : ∀ z ∈ f.roots.toFinset, ∀ w ∈ f.roots.toFinset, z ≠ w → 2 * ρ < dist z w)
    (hcard : g.roots.toFinset.card ≤ f.roots.toFinset.card) :
    ∃ e : K → K, Set.BijOn e f.roots.toFinset g.roots.toFinset ∧
      ∀ z ∈ f.roots, ‖e z - z‖ < ρ ∧ g.rootMultiplicity (e z) = f.rootMultiplicity z := by
  first
  | have hmem : ∀ i, a i ∈ f.roots.toFinset := fun i => by simp [hf]
    -- matched roots of `g` agree only if their partners agree, by disjointness of the discs
    have hba : Function.FactorsThrough a b := by
      intro i j h
      apply eq_of_dist_lt_of_dist_lt (hsep (a i) (hmem i) (a j) (hmem j))
      · rw [dist_eq_norm, norm_sub_rev]
        exact hab i
      · rw [dist_eq_norm, h, norm_sub_rev]
        exact hab j
    -- conversely, `a = ψ ∘ b` and counting values shows that `ψ` is injective on the values of `b`
    have hab' : Function.FactorsThrough b a := by
      have hψ : ∀ k, Function.extend b a id (b k) = a k := fun k => hba.extend_apply id k
      have hinj : Set.InjOn (Function.extend b a id) (Finset.univ.image b) := by
        refine Finset.card_image_iff.1 (le_antisymm Finset.card_image_le ?_)
        rw [Finset.image_image, hba.extend_comp]
        simpa only [hf, hg, Multiset.toFinset_map, Finset.val_toFinset] using hcard
      intro i j h
      exact hinj (by simp) (by simp) (by rw [hψ, hψ, h])
    have he : ∀ i, Function.extend a b id (a i) = b i := hab'.extend_apply id
    have hcount : ∀ i, g.rootMultiplicity (b i) = f.rootMultiplicity (a i) := fun i => by
      rw [← count_roots, ← count_roots, hf, hg, Multiset.count_map, Multiset.count_map]
      exact congrArg Multiset.card (Multiset.filter_congr fun j _ =>
        ⟨fun h => (hba h.symm).symm, fun h => (hab' h.symm).symm⟩)
    simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, Finset.mem_coe,
      Multiset.mem_toFinset, hf, hg, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      Set.mem_image, forall_exists_index, forall_apply_eq_imp_iff]
    refine ⟨Function.extend a b id, ⟨fun i => ⟨i, (he i).symm⟩, fun i j h => ?_,
      fun i => ⟨a i, ⟨i, rfl⟩, he i⟩⟩, fun i => ⟨?_, ?_⟩⟩
    · rw [he, he] at h
      exact hba h
    · rw [he, norm_sub_rev]
      exact hab i
    · rw [he]
      exact hcount i

end Matching

section Continuity

variable {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K]

/-- **Continuity of roots, with multiplicities.** For a monic polynomial `f` and `ε > 0`, every
monic polynomial `g` of the same degree with lower coefficients close enough to those of `f` has
its roots matched bijectively with those of `f`, counted with multiplicity: there are enumerations
`a` and `b` of their roots with `‖a i - b i‖ < ε` for every `i`. This includes degree zero. -/
theorem Monic.exists_prod_X_sub_C_norm_sub_lt {f : K[X]} (hf : f.Monic) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ < δ) →
      ∃ a b : Fin f.natDegree → K,
        f = ∏ i, (X - C (a i)) ∧ g = ∏ i, (X - C (b i)) ∧ ∀ i, ‖a i - b i‖ < ε := by
  first
  | obtain ⟨a, ha⟩ := Sym.ofFn_surjective ((Sym.coeffEquiv K f.natDegree).symm fun i => f.coeff i)
    have hc : Sym.coeffEquiv K _ (Sym.ofFn a) = fun i : Fin f.natDegree => f.coeff i := by
      rw [ha, Equiv.apply_symm_apply]
    have hev := Sym.eventually_exists_ofFn_eq_coeffEquiv_symm a hε
    rw [hc] at hev
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨δ, hδ, fun g hg hdeg hcoeff => ?_⟩
    obtain ⟨b, hb, hab⟩ := hball (y := fun i : Fin f.natDegree => g.coeff i) <|
      (dist_pi_lt_iff hδ).2 fun i => by simpa [dist_eq_norm] using hcoeff i i.is_lt
    exact ⟨a, b, (prod_X_sub_C_eq_of_ofFn_eq hf rfl ha).symm,
      (prod_X_sub_C_eq_of_ofFn_eq hg hdeg hb).symm, hab⟩

open scoped Classical in
/-- **Continuity of roots in discs.** If the `ε`-discs around the distinct roots of a monic
polynomial `f` are pairwise disjoint, then every monic polynomial `g` of the same degree with
lower coefficients close enough to those of `f` has, counted with multiplicity, exactly
`rootMultiplicity z f` roots in the disc around each root `z` of `f`, and no roots outside these
discs. -/
theorem Monic.exists_countP_roots_mem_ball_eq_rootMultiplicity {f : K[X]} (hf : f.Monic) {ε : ℝ}
    (hε : 0 < ε) (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ < δ) →
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  first
  | obtain ⟨δ, hδ, h⟩ := hf.exists_prod_X_sub_C_norm_sub_lt hε
    exact ⟨δ, hδ, fun g hg hdeg hcoeff =>
      (hf.exists_prod_X_sub_C_norm_sub_lt_iff hg (IsAlgClosed.splits f) (IsAlgClosed.splits g)
        hsep).1 (h g hg hdeg hcoeff)⟩

/-- **Continuity of roots as multisets.** For a monic polynomial `f` and `ε > 0`, every monic
polynomial `g` of the same degree with lower coefficients close enough to those of `f` has its root
multiset related to that of `f` by `Multiset.Rel` for the relation `‖z - w‖ < ε`: the roots, with
multiplicity, pair off one-to-one with paired roots at distance less than `ε`. -/
theorem Monic.exists_rel_roots_norm_sub_lt {f : K[X]} (hf : f.Monic) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ < δ) →
      f.roots.Rel (fun z w => ‖z - w‖ < ε) g.roots := by
  first
  | obtain ⟨δ, hδ, h⟩ := hf.exists_prod_X_sub_C_norm_sub_lt hε
    exact ⟨δ, hδ, fun g hg hdeg hcoeff =>
      (hf.rel_roots_iff_exists_prod_X_sub_C hg (IsAlgClosed.splits f) (IsAlgClosed.splits g)).2
        (h g hg hdeg hcoeff)⟩

/-- **Continuity of roots in a family.** Let `F x` be polynomials of degree `d`, near `x₀`, whose
coefficients of index at most `d` are continuous at `x₀`. Then for `x` near `x₀` the roots of
`F x` are matched bijectively, with multiplicity, with those of `F x₀`: there are enumerations `a`
and `b` of the roots of `F x₀` and `F x` with `‖a i - b i‖ < ε` for every `i`. -/
theorem eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt {B : Type*} [TopologicalSpace B]
    {F : B → K[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ a b : Fin d → K,
      F x₀ = C (F x₀).leadingCoeff * ∏ i, (X - C (a i)) ∧
        F x = C (F x).leadingCoeff * ∏ i, (X - C (b i)) ∧ ∀ i, ‖a i - b i‖ < ε := by
  first
  | have hdeg₀ : (F x₀).degree = d := hdeg.self_of_nhds
    have hlc : (F x₀).coeff d ≠ 0 := coeff_ne_zero_of_eq_degree hdeg₀
    -- the normalized lower coefficients depend continuously on `x` at `x₀`
    set v : B → Fin d → K := fun x i => ((F x).coeff d)⁻¹ * (F x).coeff i
    have hv : ContinuousAt v x₀ :=
      continuousAt_pi.2 fun i => ((hF d le_rfl).inv₀ hlc).mul (hF i i.is_lt.le)
    obtain ⟨a, ha⟩ := Sym.ofFn_surjective ((Sym.coeffEquiv K d).symm (v x₀))
    have hc : Sym.coeffEquiv K d (Sym.ofFn a) = v x₀ := by rw [ha, Equiv.apply_symm_apply]
    have hev := Sym.eventually_exists_ofFn_eq_coeffEquiv_symm a hε
    rw [hc] at hev
    filter_upwards [hv.eventually hev, hdeg] with x ⟨b, hb, hab⟩ hx
    exact ⟨a, b, (C_mul_prod_X_sub_C_eq_of_ofFn_eq hdeg₀ ha).symm,
      (C_mul_prod_X_sub_C_eq_of_ofFn_eq hx hb).symm, hab⟩

/-- **Continuity of roots in a family, as multisets.** Let `F x` be polynomials of degree `d`, near
`x₀`, whose coefficients of index at most `d` are continuous at `x₀`. Then for `x` near `x₀` the
root multisets of `F x₀` and `F x` are related by `Multiset.Rel` for the relation
`‖z - w‖ < ε`. -/
theorem eventually_rel_roots_norm_sub_lt {B : Type*} [TopologicalSpace B]
    {F : B → K[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, (F x₀).roots.Rel (fun z w => ‖z - w‖ < ε) (F x).roots := by
  first
  | filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hF hdeg hε, hdeg]
      with x ⟨a, b, hfa, hgb, hab⟩ hx
    exact Multiset.rel_iff_exists_fin.2 ⟨d, a, b,
      roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hdeg.self_of_nhds.ge) hfa,
      roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hx.ge) hgb, hab⟩

open scoped Classical in
/-- **Distinct roots in a family.** Let `F x` be polynomials of degree `d`, near `x₀`, whose
coefficients of index at most `d` are continuous at `x₀`, and suppose that near `x₀` the polynomial
`F x` has at most as many distinct roots as `F x₀`. Then for `x` near `x₀` there is a bijection `e`
from the distinct roots of `F x₀` onto those of `F x` that moves each root by less than `ε` and
preserves its multiplicity. -/
theorem eventually_exists_bijOn_roots_toFinset {B : Type*} [TopologicalSpace B]
    {F : B → K[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀, (F x).roots.toFinset.card ≤ (F x₀).roots.toFinset.card) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : K → K,
      Set.BijOn e (F x₀).roots.toFinset (F x).roots.toFinset ∧
        ∀ z ∈ (F x₀).roots,
          ‖e z - z‖ < ε ∧ (F x).rootMultiplicity (e z) = (F x₀).rootMultiplicity z := by
  first
    -- shrink `ε` so that the discs around the distinct roots of `F x₀` are pairwise disjoint
  | obtain ⟨r, hr, -, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist
      (T := (F x₀).roots.toFinset) (U := fun _ => Set.univ) fun _ _ => univ_mem
    filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hF hdeg (lt_min hε hr), hdeg,
      hcard] with x ⟨a, b, hfa, hgb, hab⟩ hx hxcard
    obtain ⟨e, he, hed⟩ := exists_bijOn_roots_toFinset_of_norm_sub_lt
      (roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hdeg.self_of_nhds.ge) hfa)
      (roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hx.ge) hgb) hab
      (fun z hz w hw hzw => by linarith [hsep z hz w hw hzw, min_le_right ε r]) hxcard
    exact ⟨e, he, fun z hz => ⟨(hed z hz).1.trans_le (min_le_left ε r), (hed z hz).2⟩⟩

end Continuity

end Polynomial
end -- closes the original EOF section from source line 58
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Polynomial/ContinuityOfRoots/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Polynomial/GCD.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Continuous monic gcds of polynomial families

The monic gcd of two polynomial families has continuous coefficients wherever the degrees of
both inputs and of their gcd are locally constant. At a strict gcd index it is the subresultant
polynomial divided by its nonzero principal coefficient. At a terminal index it is the monic
normalization of the input of smaller degree. The terminal cases include nonzero constants and
one input dividing the other.

Consequently, every common root at a parameter is approximated by common roots at nearby
parameters. This supplies the common-root persistence needed to make individual root matchings
agree for several polynomials; fixed input degrees alone do not ensure persistence.

The number of distinct roots in an algebraically closed characteristic-zero extension is locally
constant whenever the polynomial degree and the degree of its gcd with its derivative are locally
constant. This counting result needs no topology on the coefficient or extension fields.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 4 and 5 (subresultant gcd recovery and continuity of roots).
-/

public section

open Polynomial Filter Topology

namespace TauCeti

variable {B R : Type*} [TopologicalSpace B]

section Subresultant

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {F G : B → R[X]} {x₀ : B} {m n : ℕ}

/-- A fixed-bound subresultant coefficient minor depends continuously on the input coefficients.
Only coefficients up to the respective formal bounds need be continuous. -/
@[fun_prop]
theorem continuousAt_subresultantCoeff
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀) (j k : ℕ) :
    ContinuousAt (fun x => subresultantCoeff (F x) (G x) m n j k) x₀ := by
  first
  | simp only [subresultantCoeff_def]
    apply continuous_id.matrix_det.continuousAt.comp
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro l
    induction l using Fin.addCases with
    | left l =>
        simp only [Matrix.of_apply, Fin.addCases_left]
        split_ifs <;> first | exact hG _ (by omega) | exact continuousAt_const
    | right l =>
        simp only [Matrix.of_apply, Fin.addCases_right]
        split_ifs <;> first | exact hF _ (by omega) | exact continuousAt_const

/-- Every coefficient of a fixed-bound subresultant polynomial is continuous in the input
coefficients, including outside the strict-index range where the polynomial is zero. -/
@[fun_prop]
theorem continuousAt_coeff_subresultant
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀) (j k : ℕ) :
    ContinuousAt (fun x => (subresultant (F x) (G x) m n j).coeff k) x₀ := by
  first
  | simp only [coeff_subresultant]
    split_ifs
    · exact continuousAt_subresultantCoeff hF hG j k
    · exact continuousAt_const

/-- The resultant of `monicOfCoeff a` and its derivative, taken with the formal degrees `n` and
`n - 1`, is a continuous function of the coefficient tuple `a`. It is the subresultant coefficient
of index `0 0`, a determinant of the Sylvester matrix. -/
theorem Polynomial.continuous_resultant_derivative_monicOfCoeff :
    Continuous fun a : Fin n → R ↦
      resultant (Polynomial.monicOfCoeff a) (derivative (Polynomial.monicOfCoeff a)) n (n - 1) :=
  continuous_iff_continuousAt.2 fun a ↦ by
    simpa only [subresultantCoeff_self, psc_zero] using continuousAt_subresultantCoeff
      (fun i _ ↦ (Polynomial.continuous_coeff_monicOfCoeff i).continuousAt)
      (fun i _ ↦ by
        simp only [coeff_derivative]
        exact ((Polynomial.continuous_coeff_monicOfCoeff (i + 1)).mul
          continuous_const).continuousAt)
      (x₀ := a) (m := n) (n := n - 1) 0 0

end Subresultant

section Field

variable [Field R] [DecidableEq R] [TopologicalSpace R] [IsTopologicalDivisionRing R]
  {F G : B → R[X]} {x₀ : B} {m n j : ℕ}

/-- Monic normalization has continuous coefficients on a family of fixed finite degree. -/
@[fun_prop]
theorem continuousAt_coeff_normalize
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = m) (k : ℕ) :
    ContinuousAt (fun x => (normalize (F x)).coeff k) x₀ := by
  first
  | have hcoeff : ContinuousAt (fun x => (F x).coeff k) x₀ := by
      by_cases hk : k ≤ m
      · exact hF k hk
      · have hzero : ContinuousAt (fun _ : B => (0 : R)) x₀ := continuousAt_const
        apply hzero.congr
        filter_upwards [hdeg] with x hx
        exact (coeff_eq_zero_of_natDegree_lt (by
          rw [natDegree_eq_of_degree_eq_some hx]
          omega)).symm
    apply (((hF m le_rfl).inv₀ (coeff_ne_zero_of_eq_degree hdeg.self_of_nhds)).mul hcoeff).congr
    filter_upwards [hdeg] with x hx
    have hp : F x ≠ 0 := by
      intro h
      simp [h] at hx
    simp only [Pi.mul_apply, Pi.inv_apply, normalize_apply, coe_normUnit_of_ne_zero hp,
      coeff_mul_C]
    rw [leadingCoeff, natDegree_eq_of_degree_eq_some hx, mul_comm]

/-- The monic gcd has continuous coefficients when both input degrees and the gcd degree are
locally constant. The gcd may have the full degree of either input; neither input need be monic
or squarefree. Finite input degrees exclude zero polynomials. -/
@[fun_prop]
theorem continuousAt_coeff_normalize_gcd
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).degree = m)
    (hdegG : ∀ᶠ x in 𝓝 x₀, (G x).degree = n)
    (hgcd : ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F x) (G x)).natDegree = j) (k : ℕ) :
    ContinuousAt (fun x => (normalize (EuclideanDomain.gcd (F x) (G x))).coeff k) x₀ := by
  first
  | have hf₀ : F x₀ ≠ 0 := by
      intro h
      simpa [h] using hdegF.self_of_nhds
    have hg₀ : G x₀ ≠ 0 := by
      intro h
      simpa [h] using hdegG.self_of_nhds
    have hmn : j ≤ min m n := by
      have h₁ := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left (F x₀) (G x₀)) hf₀
      have h₂ := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (F x₀) (G x₀)) hg₀
      rw [hgcd.self_of_nhds, natDegree_eq_of_degree_eq_some hdegF.self_of_nhds] at h₁
      rw [hgcd.self_of_nhds, natDegree_eq_of_degree_eq_some hdegG.self_of_nhds] at h₂
      exact le_min h₁ h₂
    -- At a strict index the nonzero principal coefficient normalizes the subresultant.
    by_cases hj : j < min m n
    · have hc : psc (F x₀) (G x₀) m n j ≠ 0 := by
        rw [← hgcd.self_of_nhds]
        exact psc_natDegree_gcd_ne_zero hf₀
          (natDegree_eq_of_degree_eq_some hdegF.self_of_nhds)
          (natDegree_eq_of_degree_eq_some hdegG.self_of_nhds).le
      have hcont : ContinuousAt (fun x => psc (F x) (G x) m n j) x₀ := by
        simpa only [subresultantCoeff_self] using continuousAt_subresultantCoeff hF hG j j
      apply ((hcont.inv₀ hc).mul (continuousAt_coeff_subresultant hF hG j k)).congr
      filter_upwards [hdegF, hdegG, hgcd] with x hf hg hx
      have hm := natDegree_eq_of_degree_eq_some hf
      have hn := natDegree_eq_of_degree_eq_some hg
      have hs := subresultant_natDegree_gcd hm.le hn.le (by rwa [hx])
      rw [hx] at hs
      have hc' : psc (F x) (G x) m n j ≠ 0 := by
        rw [← hx]
        apply psc_natDegree_gcd_ne_zero _ hm hn.le
        intro h
        simp [h] at hf
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [hs, coeff_C_mul, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
    -- At the terminal index the gcd is associated to an input of that degree.
    · have heq : j = m ∨ j = n := by omega
      rcases heq with rfl | rfl
      · apply (continuousAt_coeff_normalize hF hdegF k).congr
        filter_upwards [hdegF, hgcd] with x hf hx
        have ha := associated_of_dvd_of_natDegree_le
          (EuclideanDomain.gcd_dvd_left (F x) (G x))
          (degree_ne_bot.mp (by rw [hf]; exact WithBot.coe_ne_bot))
          (by rw [natDegree_eq_of_degree_eq_some hf, hx])
        rw [normalize_eq_normalize_iff_associated.mpr ha]
      · apply (continuousAt_coeff_normalize hG hdegG k).congr
        filter_upwards [hdegG, hgcd] with x hg hx
        have ha := associated_of_dvd_of_natDegree_le
          (EuclideanDomain.gcd_dvd_right (F x) (G x))
          (degree_ne_bot.mp (by rw [hg]; exact WithBot.coe_ne_bot))
          (by rw [natDegree_eq_of_degree_eq_some hg, hx])
        rw [normalize_eq_normalize_iff_associated.mpr ha]

end Field

section CommonRoots

variable [NormedField R] [DecidableEq R] [IsAlgClosed R] [ProperSpace R]
  {F G : B → R[X]} {x₀ : B} {m n j : ℕ}

/-- Common roots persist under continuous variation with locally constant input and gcd degrees:
every central common root has a common root arbitrarily close in every sufficiently nearby
fiber. This does not assume constancy of the number of distinct roots of either input. -/
theorem eventually_exists_common_root_norm_sub_lt
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).degree = m)
    (hdegG : ∀ᶠ x in 𝓝 x₀, (G x).degree = n)
    (hgcd : ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F x) (G x)).natDegree = j)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ z, (F x₀).IsRoot z → (G x₀).IsRoot z →
      ∃ w, (F x).IsRoot w ∧ (G x).IsRoot w ∧ ‖w - z‖ < ε := by
  first
  | let H := fun x => normalize (EuclideanDomain.gcd (F x) (G x))
    have hne : ∀ᶠ x in 𝓝 x₀, EuclideanDomain.gcd (F x) (G x) ≠ 0 := by
      filter_upwards [hdegF] with x hx
      intro h
      have := (EuclideanDomain.gcd_eq_zero_iff.mp h).1
      simp [this] at hx
    have hmonic : ∀ᶠ x in 𝓝 x₀, (H x).Monic := hne.mono fun x hx => monic_normalize hx
    have hHdeg : ∀ᶠ x in 𝓝 x₀, (H x).degree = j := by
      filter_upwards [hne, hgcd] with x hx hj
      rw [degree_normalize, degree_eq_natDegree hx, hj]
    have hH : ∀ i ≤ j, ContinuousAt (fun x => (H x).coeff i) x₀ := fun i _ =>
      continuousAt_coeff_normalize_gcd hF hG hdegF hdegG hgcd i
    filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hH hHdeg hε,
      hmonic, hne] with x ⟨a, b, ha, hb, hab⟩ hm hx z hzF hzG
    have hroot : (H x₀).IsRoot z := by
      rw [← mem_roots (monic_normalize hne.self_of_nhds).ne_zero, roots_normalize,
        mem_roots hne.self_of_nhds, isRoot_gcd_iff_isRoot_left_right]
      exact ⟨hzF, hzG⟩
    have ha' : H x₀ = ∏ i, (X - C (a i)) := by
      simpa only [hmonic.self_of_nhds.leadingCoeff, C_1, one_mul] using ha
    have hb' : H x = ∏ i, (X - C (b i)) := by
      simpa only [hm.leadingCoeff, C_1, one_mul] using hb
    obtain ⟨i, hi⟩ : ∃ i, z = a i := by
      simpa only [IsRoot.def, ha', eval_prod, eval_sub, eval_X, eval_C,
        Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] using hroot
    have hw : (H x).IsRoot (b i) := by
      simp only [IsRoot.def, hb', eval_prod, eval_sub, eval_X, eval_C,
        Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
      exact ⟨i, rfl⟩
    have hcommon : (F x).IsRoot (b i) ∧ (G x).IsRoot (b i) := by
      rw [← isRoot_gcd_iff_isRoot_left_right, ← mem_roots hx, ← roots_normalize,
        mem_roots hm.ne_zero]
      exact hw
    exact ⟨b i, hcommon.1, hcommon.2, by rw [hi, norm_sub_rev]; exact hab i⟩

end CommonRoots

end TauCeti

namespace Polynomial

/-- **Distinct roots from derivative gcd data.** Let `f x` be polynomials over a field `k`,
with roots counted in an algebraically closed characteristic-zero extension `K`. If their degree
is fixed near `x₀` and the degree of their gcd with their derivative is locally constant, then
the number of distinct roots in `K` is locally constant. -/
theorem eventually_card_aroots_toFinset_eq_of_natDegree_gcd_derivative {B k K : Type*}
    [TopologicalSpace B] [Field k] [DecidableEq k] [Field K] [DecidableEq K]
    [Algebra k K] [IsAlgClosed K] [CharZero K] {x₀ : B} {f : B → k[X]} {n : ℕ}
    (hdeg : ∀ᶠ x in 𝓝 x₀, (f x).degree = n)
    (hgcd : ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (f x) (f x).derivative).natDegree =
      (EuclideanDomain.gcd (f x₀) (f x₀).derivative).natDegree) :
    ∀ᶠ x in 𝓝 x₀, ((f x).aroots K).toFinset.card = ((f x₀).aroots K).toFinset.card := by
  first
  | have hne {x : B} (hx : (f x).degree = n) : f x ≠ 0 := by
      rintro h
      simp [h] at hx
    have hx₀ := hdeg.self_of_nhds
    filter_upwards [hdeg, hgcd] with x hx hxg
    rw [← natDegree_sub_natDegree_gcd_derivative_eq_card_aroots_toFinset (K := K) (hne hx),
      ← natDegree_sub_natDegree_gcd_derivative_eq_card_aroots_toFinset (K := K) (hne hx₀), hxg,
      natDegree_eq_of_degree_eq_some hx, natDegree_eq_of_degree_eq_some hx₀]

end Polynomial
end -- closes the original EOF section from source line 37
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Polynomial/GCD.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Polynomial/CommonRoots.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Common root matching for finite families of polynomials

Let `F k x`, for `k` in a finite index type, be polynomials over a proper algebraically closed
normed field whose coefficients depend continuously on a parameter `x`, each of fixed degree.
For a single member, `Polynomial.eventually_exists_bijOn_roots_toFinset` matches the distinct roots
of `F k x` with those of `F k x₀`, preserving multiplicities, as long as the number of distinct
roots does not increase near `x₀`. Separate matchings need not be compatible: two members sharing
a root at `x₀` could have nearby roots that drift apart.

This file shows that if, in addition, the degree of the gcd of every pair of members is locally
constant, then one bijection between the union of the distinct roots of the members at `x₀` and
at `x` works for all members simultaneously. It moves each root by less than a prescribed `ε` and
preserves its multiplicity in every member; in particular it preserves membership in every root
set. Consequently the total number of distinct roots of the family is locally constant.

Only pairwise gcd data are needed. The persistence of a common root of two members comes from
`TauCeti.eventually_exists_common_root_norm_sub_lt`; the individual matchings then force every
nearby common root to be the partner of the central root in both members.

## Main results

* `Polynomial.eventually_exists_bijOn_biUnion_roots_toFinset`: the family matching lemma.
* `Polynomial.eventually_card_biUnion_roots_toFinset_eq`: local constancy of the number of
  distinct roots of the family.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of roots and delineability).
-/

public section

open Filter Metric Topology TauCeti

namespace Polynomial

variable {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K] {B : Type*}
  [TopologicalSpace B] {ι : Type*} [Fintype ι] {F : ι → B → K[X]} {x₀ : B} {d : ι → ℕ}

open scoped Classical in
/-- **Family matching lemma.** Let `F k x` be polynomials of degree `d k` near `x₀`, for `k` in a
finite index type, whose coefficients of index at most `d k` are continuous at `x₀`. Suppose that
near `x₀` no member has more distinct roots than at `x₀`, and that the degree of the gcd of every
pair of distinct members is the same as at `x₀`. Then for `x` near `x₀` there is a single
bijection `e` from the distinct roots of all the `F k x₀` onto those of all the `F k x` that moves
each root by less than `ε` and preserves its multiplicity in every member. -/
theorem eventually_exists_bijOn_biUnion_roots_toFinset
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).roots.toFinset.card ≤ (F k x₀).roots.toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : K → K,
      Set.BijOn e (Finset.univ.biUnion fun k => (F k x₀).roots.toFinset)
        (Finset.univ.biUnion fun k => (F k x).roots.toFinset) ∧
      ∀ z ∈ Finset.univ.biUnion (fun k => (F k x₀).roots.toFinset), ‖e z - z‖ < ε ∧
        ∀ k, (F k x).rootMultiplicity (e z) = (F k x₀).rootMultiplicity z := by
  first
    -- Outline: separate the distinct roots of the family at `x₀` by discs of radius `ρ ≤ ε`, take
    -- the individual matchings `e k` and the persistence of pairwise common roots at radius `ρ`,
    -- show that a root of `F k x` in the disc around `z` must be `e k z`, deduce that the `e k`
    -- agree on common roots, and glue them into a single map `E`.
  | set T := Finset.univ.biUnion fun k => (F k x₀).roots.toFinset
    have hT (k : ι) : (F k x₀).roots.toFinset ⊆ T :=
      Finset.subset_biUnion_of_mem (fun k => (F k x₀).roots.toFinset) (Finset.mem_univ k)
    -- shrink `ε` so that the discs around the distinct roots of the family are pairwise disjoint
    obtain ⟨r, hr, -, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist
      (T := T) (U := fun _ => Set.univ) fun _ _ => univ_mem
    set ρ := min ε r
    have hρ : 0 < ρ := lt_min hε hr
    have hsep' : ∀ z ∈ T, ∀ w ∈ T, z ≠ w → 2 * ρ < dist z w := fun z hz w hw hzw => by
      linarith [hsep z hz w hw hzw, min_le_right ε r]
    have hmatch : ∀ᶠ x in 𝓝 x₀, ∀ k, ∃ e : K → K,
        Set.BijOn e (F k x₀).roots.toFinset (F k x).roots.toFinset ∧
          ∀ z ∈ (F k x₀).roots,
            ‖e z - z‖ < ρ ∧ (F k x).rootMultiplicity (e z) = (F k x₀).rootMultiplicity z :=
      eventually_all.2 fun k => eventually_exists_bijOn_roots_toFinset (hF k) (hdeg k) (hcard k) hρ
    have hcommon : ∀ᶠ x in 𝓝 x₀, ∀ k l, k ≠ l → ∀ z, (F k x₀).IsRoot z → (F l x₀).IsRoot z →
        ∃ w, (F k x).IsRoot w ∧ (F l x).IsRoot w ∧ ‖w - z‖ < ρ := by
      refine eventually_all.2 fun k => eventually_all.2 fun l => ?_
      by_cases hkl : k = l
      · exact Eventually.of_forall fun _ h => absurd hkl h
      · exact (eventually_exists_common_root_norm_sub_lt (hF k) (hF l) (hdeg k) (hdeg l)
          (hgcd hkl) hρ).mono fun _ h _ => h
    filter_upwards [hmatch, hcommon, eventually_all.2 hdeg] with x hm hc hx
    choose e he hed using hm
    have hne (k : ι) (y : B) (hy : (F k y).degree = d k) : F k y ≠ 0 := by
      rintro h
      simp [h] at hy
    -- a root of `F k x` near a point of `T` is the partner of that point under `e k`
    have huniq (k : ι) {z w : K} (hz : z ∈ T) (hw : w ∈ (F k x).roots) (hwz : ‖w - z‖ < ρ) :
        z ∈ (F k x₀).roots ∧ e k z = w := by
      obtain ⟨z', hz', rfl⟩ := (he k).surjOn (Finset.mem_coe.2 (Multiset.mem_toFinset.2 hw))
      have hz'k : z' ∈ (F k x₀).roots := Multiset.mem_toFinset.1 hz'
      obtain rfl : z = z' := eq_of_dist_lt_of_dist_lt (hsep' z hz z' (hT k hz'))
        (by rwa [dist_eq_norm]) (by rw [dist_eq_norm]; exact (hed k z' hz'k).1)
      exact ⟨hz'k, rfl⟩
    -- the matchings of two members agree at a common root
    have hagree (k l : ι) {z : K} (hk : z ∈ (F k x₀).roots) (hl : z ∈ (F l x₀).roots) :
        e k z = e l z := by
      by_cases hkl : k = l
      · rw [hkl]
      have hz : z ∈ T := hT k (Multiset.mem_toFinset.2 hk)
      obtain ⟨w, hwk, hwl, hwz⟩ := hc k l hkl z ((mem_roots (hne k x₀ (hdeg k).self_of_nhds)).1 hk)
        ((mem_roots (hne l x₀ (hdeg l).self_of_nhds)).1 hl)
      rw [(huniq k hz ((mem_roots (hne k x (hx k))).2 hwk) hwz).2,
        (huniq l hz ((mem_roots (hne l x (hx l))).2 hwl) hwz).2]
    have hmemT {z : K} (hz : z ∈ T) : ∃ k, z ∈ (F k x₀).roots := by
      simpa [T] using hz
    let E : K → K := fun z => if h : ∃ k, z ∈ (F k x₀).roots then e h.choose z else z
    have hE {k : ι} {z : K} (hz : z ∈ (F k x₀).roots) : E z = e k z := by
      have h : ∃ k, z ∈ (F k x₀).roots := ⟨k, hz⟩
      simp only [E, h, ↓reduceDIte]
      exact hagree _ _ h.choose_spec hz
    have hEclose {z : K} (hz : z ∈ T) : ‖E z - z‖ < ρ := by
      obtain ⟨k, hk⟩ := hmemT hz
      rw [hE hk]
      exact (hed k z hk).1
    refine ⟨E, ⟨fun z hz => ?_, fun z hz z' hz' hzz' => ?_, fun w hw => ?_⟩, fun z hz =>
      ⟨(hEclose hz).trans_le (min_le_left ε r), fun k => ?_⟩⟩
    · obtain ⟨k, hk⟩ := hmemT hz
      rw [hE hk]
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _,
        Finset.mem_coe.1 ((he k).mapsTo (Multiset.mem_toFinset.2 hk))⟩)
    · exact eq_of_dist_lt_of_dist_lt (hsep' z hz z' hz') (y := E z)
        (by rw [dist_eq_norm]; exact hEclose hz) (by rw [dist_eq_norm, hzz']; exact hEclose hz')
    · obtain ⟨k, -, hwk⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hw)
      obtain ⟨z, hz, rfl⟩ := (he k).surjOn hwk
      have hzk : z ∈ (F k x₀).roots := Multiset.mem_toFinset.1 hz
      exact ⟨z, Finset.mem_coe.2 (hT k hz), hE hzk⟩
    · by_cases hk : z ∈ (F k x₀).roots
      · rw [hE hk]
        exact (hed k z hk).2
      · rw [rootMultiplicity_eq_zero fun h => hk ((mem_roots (hne k x₀ (hdeg k).self_of_nhds)).2 h)]
        refine rootMultiplicity_eq_zero fun h => hk ?_
        exact (huniq k hz ((mem_roots (hne k x (hx k))).2 h) (hEclose hz)).1

open scoped Classical in
/-- **Local constancy of the number of distinct roots of a family.** Under the hypotheses of the
family matching lemma, the members of the family have, together, as many distinct roots near
`x₀` as at `x₀`. -/
theorem eventually_card_biUnion_roots_toFinset_eq
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).roots.toFinset.card ≤ (F k x₀).roots.toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∀ᶠ x in 𝓝 x₀, (Finset.univ.biUnion fun k => (F k x).roots.toFinset).card =
      (Finset.univ.biUnion fun k => (F k x₀).roots.toFinset).card := by
  first
  | filter_upwards [eventually_exists_bijOn_biUnion_roots_toFinset hF hdeg hcard hgcd one_pos]
      with x ⟨e, he, _⟩
    exact (Finset.card_nbij e he.mapsTo he.injOn he.surjOn).symm

end Polynomial
end -- closes the original EOF section from source line 44
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Polynomial/CommonRoots.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Polynomial/RealRoots/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Real roots of a family of real polynomials

Let `F x` be real polynomials of fixed degree whose coefficients depend continuously on a
parameter `x`. Nearby members of the family can lose real roots, or gain them, when two real roots
collide and leave the real line as a pair of complex conjugates, or when such a pair lands on the
real line. Both events lower the number of distinct complex roots at the collision. This file
shows that if the number of distinct **complex** roots of `F x` does not exceed that of `F x₀` for
`x` near `x₀`, then the distinct real roots of `F x` correspond bijectively to those of `F x₀`,
each moved by an arbitrarily small amount and with its multiplicity unchanged. In particular the
number of distinct real roots is then locally constant.

The proof applies `Polynomial.eventually_exists_bijOn_roots_toFinset` to the complex roots and uses
complex conjugation. The disc around a real root of `F x₀` contains a single distinct root of
`F x`, and the conjugate of that root is a root in the same disc, so it is real. The discs around
the non-real roots of `F x₀` are chosen to miss the real line, so they contain no real roots.

## Main results

* `Polynomial.eventually_exists_bijOn_roots_toFinset_of_card_aroots_le`: the distinct real roots
  of `F x` and `F x₀` correspond bijectively, nearby and with the same multiplicities.
* `Polynomial.eventually_card_roots_toFinset_eq_of_card_aroots_le`: the number of distinct real
  roots is locally constant.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of the roots of a polynomial with respect to its coefficients).
-/

public section

open Filter Metric Topology TauCeti ComplexConjugate

namespace Polynomial

/-- **Real roots under a matching of complex roots.** Let `e` be a bijection from the distinct
complex roots of a real polynomial `f` onto those of a real polynomial `g`, moving each root by less
than `ρ` and preserving multiplicities. If the roots of `f` are more than `2 * ρ` apart and every
point within `ρ` of a non-real root of `f` is non-real, then `e` restricts to such a bijection
between the distinct real roots. -/
private theorem exists_bijOn_roots_toFinset_of_bijOn_aroots {f g : ℝ[X]} {ρ : ℝ} {e : ℂ → ℂ}
    (hsep : ∀ z ∈ (f.aroots ℂ).toFinset, ∀ w ∈ (f.aroots ℂ).toFinset, z ≠ w → 2 * ρ < dist z w)
    (him : ∀ z ∈ (f.aroots ℂ).toFinset, z.im ≠ 0 → ∀ w, dist w z < ρ → w.im ≠ 0)
    (he : Set.BijOn e (f.aroots ℂ).toFinset (g.aroots ℂ).toFinset)
    (hed : ∀ z ∈ f.aroots ℂ, ‖e z - z‖ < ρ ∧
      (g.map (algebraMap ℝ ℂ)).rootMultiplicity (e z) =
        (f.map (algebraMap ℝ ℂ)).rootMultiplicity z) :
    ∃ e' : ℝ → ℝ, Set.BijOn e' f.roots.toFinset g.roots.toFinset ∧
      ∀ t ∈ f.roots, |e' t - t| < ρ ∧ g.rootMultiplicity (e' t) = f.rootMultiplicity t := by
  first
  | have hmem : ∀ {p : ℝ[X]} {t : ℝ}, t ∈ p.roots ↔ (t : ℂ) ∈ (p.aroots ℂ).toFinset := by
      intro p t
      rw [Multiset.mem_toFinset, mem_aroots, mem_roots', IsRoot.def, ← Complex.coe_algebraMap,
        aeval_algebraMap_apply_eq_algebraMap_eval, Complex.coe_algebraMap, Complex.ofReal_eq_zero]
    have hed' : ∀ t ∈ f.roots, ‖e t - t‖ < ρ := fun t ht =>
      (hed t (Multiset.mem_toFinset.1 (hmem.1 ht))).1
    -- the partner of a real root is real: its conjugate is a root of `g` in the same disc
    have hreal : ∀ t ∈ f.roots, ((e t).re : ℂ) = e t := by
      intro t ht
      rw [← Complex.conj_eq_iff_re]
      have hconj : conj (e t) ∈ (g.aroots ℂ).toFinset := by
        have := he.mapsTo (hmem.1 ht)
        simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_aroots] at this ⊢
        exact ⟨this.1, by rw [aeval_conj, this.2, map_zero]⟩
      obtain ⟨z, hz, hez⟩ := he.surjOn hconj
      have hzt : dist z t < 2 * ρ := by
        have hc : conj (e t) - t = conj (e t - t) := by rw [map_sub, Complex.conj_ofReal]
        rw [dist_eq_norm]
        calc ‖z - t‖ = ‖(z - e z) + (conj (e t) - t)‖ := by rw [← hez, sub_add_sub_cancel]
          _ ≤ ‖e z - z‖ + ‖e t - t‖ := (norm_add_le _ _).trans_eq
            (by rw [norm_sub_rev z, hc, Complex.norm_conj])
          _ < 2 * ρ := by linarith [(hed z (Multiset.mem_toFinset.1 hz)).1, hed' t ht]
      have hzt' : z = t := by
        by_contra hne
        exact (hsep z hz t (hmem.1 ht) hne).not_gt hzt
      rw [← hez, hzt']
    -- the partner of a non-real root is not real, since its disc misses the real line
    have hnonreal : ∀ z ∈ (f.aroots ℂ).toFinset, z.im ≠ 0 → (e z).im ≠ 0 := fun z hz hzim =>
      him z hz hzim _ ((dist_eq_norm _ _).trans_lt (hed z (Multiset.mem_toFinset.1 hz)).1)
    refine ⟨fun t => (e t).re, ⟨fun t ht => ?_, fun t ht t' ht' htt' => ?_, fun s hs => ?_⟩,
      fun t ht => ⟨?_, ?_⟩⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset] at ht ⊢
      exact hmem.2 (by rw [hreal t ht]; exact he.mapsTo (hmem.1 ht))
    · simp only [Finset.mem_coe, Multiset.mem_toFinset] at ht ht'
      have : e t = e t' := by rw [← hreal t ht, ← hreal t' ht']; exact congrArg _ htt'
      exact Complex.ofReal_injective (he.injOn (hmem.1 ht) (hmem.1 ht') this)
    · simp only [Finset.mem_coe, Multiset.mem_toFinset] at hs
      obtain ⟨z, hz, hez⟩ := he.surjOn (hmem.1 hs)
      have hzre : (z.re : ℂ) = z := Complex.conj_eq_iff_re.1 <| Complex.conj_eq_iff_im.2 <| by
        by_contra h
        exact hnonreal z hz h (by rw [hez, Complex.ofReal_im])
      refine ⟨z.re, Finset.mem_coe.2 (Multiset.mem_toFinset.2 (hmem.2 (hzre ▸ hz))), ?_⟩
      simp only [hzre, hez, Complex.ofReal_re]
    · have := hed' t ht
      rwa [← hreal t ht, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
    · rw [eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective,
        eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective t, Complex.coe_algebraMap, hreal t ht]
      exact (hed t (Multiset.mem_toFinset.1 (hmem.1 ht))).2

/-- **Real roots in a family.** Let `F x` be real polynomials of degree `d`, near `x₀`, whose
coefficients of index at most `d` are continuous at `x₀`, and suppose that near `x₀` the polynomial
`F x` has at most as many distinct complex roots as `F x₀`. Then for `x` near `x₀` there is a
bijection `e` from the distinct real roots of `F x₀` onto those of `F x` that moves each root by
less than `ε` and preserves its multiplicity. -/
theorem eventually_exists_bijOn_roots_toFinset_of_card_aroots_le {B : Type*}
    [TopologicalSpace B] {F : B → ℝ[X]} {x₀ : B} {d : ℕ}
    (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀, ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : ℝ → ℝ,
      Set.BijOn e (F x₀).roots.toFinset (F x).roots.toFinset ∧
        ∀ t ∈ (F x₀).roots,
          |e t - t| < ε ∧ (F x).rootMultiplicity (e t) = (F x₀).rootMultiplicity t := by
  first
    -- choose the radius so that the discs around the distinct complex roots of `F x₀` are pairwise
    -- disjoint and the discs around the non-real ones miss the real line
  | obtain ⟨r, hr, hU, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist
      (T := ((F x₀).aroots ℂ).toFinset) (U := fun z => if z.im = 0 then Set.univ else {w | w.im ≠ 0})
      fun z _ => by
        split_ifs with hz
        · exact univ_mem
        · exact (isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hz
    have hρ : min ε r ≤ r := min_le_right ε r
    have hG : ∀ i ≤ d, ContinuousAt (fun x => ((F x).map (algebraMap ℝ ℂ)).coeff i) x₀ :=
      fun i hi => by
        simpa only [coeff_map, Complex.coe_algebraMap, Function.comp_def] using
          Complex.continuous_ofReal.continuousAt.comp (hF i hi)
    have hGdeg : ∀ᶠ x in 𝓝 x₀, ((F x).map (algebraMap ℝ ℂ)).degree = d :=
      hdeg.mono fun x hx => by rw [degree_map, hx]
    filter_upwards [eventually_exists_bijOn_roots_toFinset hG hGdeg hcard (lt_min hε hr)]
      with x ⟨e, he, hed⟩
    simp only [← aroots_def] at he hed
    obtain ⟨e', he', hed'⟩ := exists_bijOn_roots_toFinset_of_bijOn_aroots
      (fun z hz w hw hzw => by linarith [hsep z hz w hw hzw])
      (fun z hz hzim w hw => by
        simpa only [hzim, ↓reduceIte, Set.mem_ofPred_eq] using
          hU z hz (mem_closedBall.2 (hw.le.trans hρ)))
      he hed
    exact ⟨e', he', fun t ht => ⟨(hed' t ht).1.trans_le (min_le_left ε r), (hed' t ht).2⟩⟩

/-- **Local constancy of the number of real roots.** Let `F x` be real polynomials of degree `d`,
near `x₀`, whose coefficients of index at most `d` are continuous at `x₀`, and suppose that near
`x₀` the polynomial `F x` has at most as many distinct complex roots as `F x₀`. Then for `x` near
`x₀` the polynomials `F x` and `F x₀` have the same number of distinct real roots. -/
theorem eventually_card_roots_toFinset_eq_of_card_aroots_le {B : Type*} [TopologicalSpace B]
    {F : B → ℝ[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀, ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card) :
    ∀ᶠ x in 𝓝 x₀, (F x).roots.toFinset.card = (F x₀).roots.toFinset.card := by
  first
  | filter_upwards [eventually_exists_bijOn_roots_toFinset_of_card_aroots_le hF hdeg hcard
      one_pos] with x ⟨e, he, _⟩
    exact (Finset.card_nbij e he.mapsTo he.injOn he.surjOn).symm

end Polynomial
end -- closes the original EOF section from source line 44
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Polynomial/RealRoots/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Polynomial/RealRoots/Ordered.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Ordered real roots in continuous polynomial families

For a real polynomial family of fixed degree with continuous coefficients, a locally
nonincreasing number of distinct complex roots forces its increasing enumeration of real roots
to vary continuously. The multiplicity at each position is locally constant. On a preconnected
base, both the number of real roots and their ordered multiplicities are constant, so a single
finite ordered list gives continuous root functions on the whole base.

The local statements require a strictly increasing complete enumeration only near the parameter,
without assuming its continuity. The connected existence theorem constructs it using Mathlib's
`Finset.orderEmbOfFin`, and excludes zero fibers by its fixed-degree hypothesis. Constant
polynomials and empty root lists are included.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of roots with respect to coefficients).
-/

public section

open Filter Metric Topology

namespace Polynomial

variable {B : Type*} [TopologicalSpace B] {F : B → ℝ[X]} {d n : ℕ}

/-- An increasing complete enumeration of the distinct real roots moves arbitrarily little
near `x₀` and preserves multiplicities, when the coefficients are continuous, the degree is
locally fixed, and the number of distinct complex roots is locally nonincreasing. The enumeration
is required to be increasing and complete only near `x₀`; no continuity is assumed. -/
theorem eventually_ordered_roots_close_of_card_aroots_le {x₀ : B}
    (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {r : B → Fin n → ℝ} (hr : ∀ᶠ x in 𝓝 x₀, StrictMono (r x))
    (hroots : ∀ᶠ x in 𝓝 x₀, Set.range (r x) = (F x).roots.toFinset)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ i,
      |r x i - r x₀ i| < ε ∧ (F x).rootMultiplicity (r x i) =
        (F x₀).rootMultiplicity (r x₀ i) := by
  first
  | classical
    have hr₀ := hr.self_of_nhds
    have hroots₀ := hroots.self_of_nhds
    obtain ⟨δ, hδ, _, hsep⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
      (T := (F x₀).roots.toFinset) (U := fun _ => Set.univ) (fun _ _ => univ_mem)
    have hmem {x : B} (hx : Set.range (r x) = (F x).roots.toFinset) (i : Fin n) :
        r x i ∈ (F x).roots.toFinset := by
      rw [← Finset.mem_coe, ← hx]
      exact Set.mem_range_self i
    filter_upwards [eventually_exists_bijOn_roots_toFinset_of_card_aroots_le
      hF hdeg hcard (lt_min hε hδ), hr, hroots] with x ⟨e, he, hed⟩ hrx hrootsx
    have hclose (i : Fin n) := hed (r x₀ i) (Multiset.mem_toFinset.1 (hmem hroots₀ i))
    have hmono : StrictMono (fun i => e (r x₀ i)) := by
      intro i j hij
      have hij' := hr₀ hij
      have hd := hsep _ (hmem hroots₀ i) _ (hmem hroots₀ j) (ne_of_lt hij')
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hij'.le)] at hd
      have hi := (abs_lt.1 (hclose i).1).2
      have hj := (abs_lt.1 (hclose j).1).1
      have := min_le_right ε δ
      linarith
    have heq : (fun i => e (r x₀ i)) = r x := by
      apply (hmono.range_inj_of_wellFoundedLT hrx).1
      rw [← Function.comp_def, Set.range_comp, hroots₀, he.image_eq, hrootsx]
    intro i
    rw [← congrFun heq i]
    exact ⟨(hclose i).1.trans_le (min_le_left ε δ), (hclose i).2⟩

/-- Every position in an increasing complete enumeration of real roots is continuous at a
parameter where the coefficients are continuous, the degree is locally fixed, and the number
of distinct complex roots is locally nonincreasing. The enumeration is required to be
increasing and complete only near that parameter. -/
theorem continuousAt_ordered_root_of_card_aroots_le {x₀ : B}
    (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {r : B → Fin n → ℝ} (hr : ∀ᶠ x in 𝓝 x₀, StrictMono (r x))
    (hroots : ∀ᶠ x in 𝓝 x₀, Set.range (r x) = (F x).roots.toFinset) (i : Fin n) :
    ContinuousAt (fun x => r x i) x₀ := by
  first
  | refine Metric.continuousAt_iff'.2 fun ε hε => ?_
    filter_upwards [eventually_ordered_roots_close_of_card_aroots_le
      hF hdeg hcard hr hroots hε] with x hx
    simpa only [Real.dist_eq] using (hx i).1

/-- Multiplicity at each position in an increasing complete enumeration of real roots is
locally constant, provided the coefficient and root-count hypotheses hold at every parameter. -/
theorem isLocallyConstant_rootMultiplicity_ordered_root_of_card_aroots_le
    (hF : ∀ i ≤ d, Continuous (fun x => (F x).coeff i))
    (hdeg : ∀ x, (F x).degree = d)
    (hcard : ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {r : B → Fin n → ℝ} (hr : ∀ x, StrictMono (r x))
    (hroots : ∀ x, Set.range (r x) = (F x).roots.toFinset) (i : Fin n) :
    IsLocallyConstant (fun x => (F x).rootMultiplicity (r x i)) := by
  first
  | refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
    filter_upwards [eventually_ordered_roots_close_of_card_aroots_le
      (fun i hi => (hF i hi).continuousAt) (Eventually.of_forall hdeg) (hcard x₀)
      (Eventually.of_forall hr) (Eventually.of_forall hroots) one_pos] with x hx
    exact (hx i).2

/-- The number of distinct real roots is constant on a preconnected base if the degree is
fixed, the coefficients are continuous, and the number of distinct complex roots is locally
nonincreasing. -/
theorem card_roots_toFinset_eq_of_preconnectedSpace [PreconnectedSpace B]
    (hF : ∀ i ≤ d, Continuous (fun x => (F x).coeff i))
    (hdeg : ∀ x, (F x).degree = d)
    (hcard : ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card) (x y : B) :
    (F x).roots.toFinset.card = (F y).roots.toFinset.card := by
  first
  | have hlocal : IsLocallyConstant (fun x => (F x).roots.toFinset.card) :=
      (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ =>
        eventually_card_roots_toFinset_eq_of_card_aroots_le
          (fun i hi => (hF i hi).continuousAt) (Eventually.of_forall hdeg) (hcard x₀)
    exact hlocal.apply_eq_of_preconnectedSpace x y

/-- On a nonempty preconnected base, a fixed-degree continuous polynomial family with locally
nonincreasing number of distinct complex roots has a global finite increasing enumeration of
all its real zeros by continuous functions. The multiplicity at each position is constant.
No fixed real root count or continuous root enumeration is assumed. -/
theorem exists_continuous_ordered_roots_of_preconnectedSpace [PreconnectedSpace B] [Nonempty B]
    (hF : ∀ i ≤ d, Continuous (fun x => (F x).coeff i))
    (hdeg : ∀ x, (F x).degree = d)
    (hcard : ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card) :
    ∃ n : ℕ, ∃ r : B → Fin n → ℝ,
      (∀ i, Continuous (fun x => r x i)) ∧ (∀ x, StrictMono (r x)) ∧
      (∀ x t, (F x).IsRoot t ↔ ∃ i, r x i = t) ∧
      (∀ i x y, (F x).rootMultiplicity (r x i) = (F y).rootMultiplicity (r y i)) := by
  first
  | classical
    let x₀ : B := Classical.arbitrary B
    let n := (F x₀).roots.toFinset.card
    have hcount (x : B) : (F x).roots.toFinset.card = n :=
      card_roots_toFinset_eq_of_preconnectedSpace hF hdeg hcard x x₀
    let r (x : B) : Fin n → ℝ := (F x).roots.toFinset.orderEmbOfFin (hcount x)
    have hr (x : B) : StrictMono (r x) := (Finset.orderEmbOfFin _ _).strictMono
    have hroots (x : B) : Set.range (r x) = (F x).roots.toFinset :=
      Finset.range_orderEmbOfFin _ _
    refine ⟨n, r, fun i => continuous_iff_continuousAt.2 (fun x => ?_), hr, ?_, ?_⟩
    · exact continuousAt_ordered_root_of_card_aroots_le
        (fun i hi => (hF i hi).continuousAt) (Eventually.of_forall hdeg) (hcard x)
        (Eventually.of_forall hr) (Eventually.of_forall hroots) i
    · intro x t
      have hne : F x ≠ 0 := degree_ne_bot.1 (by rw [hdeg x]; exact WithBot.coe_ne_bot)
      rw [← mem_roots hne, ← Multiset.mem_toFinset, ← Finset.mem_coe, ← hroots x]
      rfl
    · intro i x y
      exact (isLocallyConstant_rootMultiplicity_ordered_root_of_card_aroots_le
        hF hdeg hcard hr hroots i).apply_eq_of_preconnectedSpace x y

end Polynomial

end
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Polynomial/RealRoots/Ordered.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Taylor.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Taylor coefficients at a root and in subleading degree

The Taylor expansion `taylor r p = p(X + r)` of a polynomial `p` at `r` starts in degree
`p.rootMultiplicity r`, and its trailing coefficient is the value at `r` of `p` divided by the
largest power of `X - r` dividing it. This is the coefficient that survives when `X - r` is
divided out of `p` as often as possible before evaluating at `r`; for `p ≠ 0` it is nonzero
(`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`), so it is the lowest nonzero
coefficient of the Taylor expansion.

Since the Taylor coefficients of `p` at `r` are the values at `r` of the Hasse derivatives of `p`,
divisibility of `p` by `(X - r) ^ n` is the vanishing of its Hasse derivatives of order less than
`n` at `r`. A Hasse derivative of order `k` therefore lowers such a divisibility by at most `k`.

At the other end of the expansion, the leading coefficient is unchanged and the subleading
coefficient moves by `p.natDegree * r * p.leadingCoeff`. This is the input for the Tschirnhaus
shift, which removes the subleading coefficient whenever `p.natDegree` is invertible.

## Main results

* `Polynomial.natTrailingDegree_taylor`: the Taylor expansion at `r` starts in degree
  `p.rootMultiplicity r`.
* `Polynomial.coeff_taylor_rootMultiplicity`, `Polynomial.trailingCoeff_taylor`: its trailing
  coefficient is `(p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r`.
* `Polynomial.eval_hasseDeriv_rootMultiplicity_ne_zero`: for `p ≠ 0`, the Hasse derivative of
  order `p.rootMultiplicity r` does not vanish at `r`.
* `Polynomial.pow_sub_dvd_hasseDeriv_of_pow_dvd`: if `(X - r) ^ n` divides `p`, then
  `(X - r) ^ (n - k)` divides the Hasse derivative of `p` of order `k`.
* `Polynomial.eval_hasseDeriv_X_sub_C_pow`: the Hasse derivatives of `(X - r) ^ m` at `r`.
* `Polynomial.nextCoeff_taylor`: the subleading coefficient of the Taylor expansion of `p` at `r`
  is `p.nextCoeff + p.natDegree * r * p.leadingCoeff`.
-/

public section

namespace Polynomial

/-- The subleading coefficient of the Taylor expansion `p(X + r)` is that of `p` plus
`p.natDegree * r * p.leadingCoeff`. -/
theorem nextCoeff_taylor {R : Type*} [CommSemiring R] (p : R[X]) (r : R) :
    (taylor r p).nextCoeff = p.nextCoeff + p.natDegree * r * p.leadingCoeff := by
  first
  | rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · simp [nextCoeff, natDegree_taylor, h]
    -- The Hasse derivative of order `p.natDegree - 1` is linear; evaluate it at `r`.
    rw [nextCoeff_of_natDegree_pos (by rwa [natDegree_taylor]), nextCoeff_of_natDegree_pos h,
      natDegree_taylor, taylor_coeff,
      eq_X_add_C_of_natDegree_le_one ((natDegree_hasseDeriv_le _ _).trans (by omega))]
    obtain ⟨d, hd⟩ : ∃ d, p.natDegree = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    simp [hasseDeriv_coeff, leadingCoeff, hd, add_comm 1 d]
    ring

variable {R : Type*} [CommRing R]

/-- The Taylor expansion of `p` at `r` starts in degree `p.rootMultiplicity r`. -/
theorem natTrailingDegree_taylor (p : R[X]) (r : R) :
    (taylor r p).natTrailingDegree = p.rootMultiplicity r := by
  first
  | rw [rootMultiplicity_eq_natTrailingDegree, taylor_apply]

/-- The coefficient of `X ^ p.rootMultiplicity r` in the Taylor expansion of `p` at `r` is the
value at `r` of `p` divided by the largest power of `X - r` dividing it. -/
theorem coeff_taylor_rootMultiplicity (p : R[X]) (r : R) :
    (taylor r p).coeff (p.rootMultiplicity r) =
      (p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r := by
  first
  | set m := p.rootMultiplicity r
    conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq p r]
    simpa [taylor_mul, taylor_pow, taylor_coeff_zero] using
      coeff_X_pow_mul (taylor r (p /ₘ (X - C r) ^ m)) m 0

/-- The trailing coefficient of the Taylor expansion of `p` at `r` is the value at `r` of `p`
divided by the largest power of `X - r` dividing it. For `p ≠ 0` this is the lowest nonzero
coefficient. -/
theorem trailingCoeff_taylor (p : R[X]) (r : R) :
    (taylor r p).trailingCoeff = (p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r := by
  first
  | rw [trailingCoeff, natTrailingDegree_taylor, coeff_taylor_rootMultiplicity]

/-- For `p ≠ 0`, the Hasse derivative of `p` of order `p.rootMultiplicity r` does not vanish
at `r`. -/
theorem eval_hasseDeriv_rootMultiplicity_ne_zero {p : R[X]} (hp : p ≠ 0) (r : R) :
    (hasseDeriv (p.rootMultiplicity r) p).eval r ≠ 0 := by
  first
  | rw [← taylor_coeff, ← natTrailingDegree_taylor]
    exact coeff_natTrailingDegree_ne_zero.2 ((taylor_eq_zero _ _).not.2 hp)

/-- If `(X - r) ^ n` divides `p`, then `(X - r) ^ (n - k)` divides the Hasse derivative of `p` of
order `k`. This is the analogue of `Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd` for
Hasse derivatives; it does not follow from it when `k !` is not invertible in `R`. -/
theorem pow_sub_dvd_hasseDeriv_of_pow_dvd {p : R[X]} {r : R} {n : ℕ} (k : ℕ)
    (h : (X - C r) ^ n ∣ p) : (X - C r) ^ (n - k) ∣ hasseDeriv k p := by
  first
  | rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff] at h ⊢
    intro j hj
    have := h (j + k) (by omega)
    rw [taylor_coeff] at this ⊢
    rw [← LinearMap.comp_apply, hasseDeriv_comp, LinearMap.smul_apply, nsmul_eq_mul, eval_mul, this,
      mul_zero]

/-- The Hasse derivative of order `i` of `(X - r) ^ m` is `1` at `r` if `i = m`, and `0`
otherwise: the Taylor expansion of `(X - r) ^ m` at `r` is `X ^ m`. -/
@[simp]
theorem eval_hasseDeriv_X_sub_C_pow (r : R) (i m : ℕ) :
    (hasseDeriv i ((X - C r) ^ m)).eval r = if i = m then 1 else 0 := by
  first
  | rw [← taylor_coeff]
    simp [taylor_pow, coeff_X_pow]

end Polynomial
end -- closes the original EOF section from source line 44
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Taylor.lean -/

/- BEGIN SOURCE: TauCeti/Topology/Algebra/Polynomial/RootMultiplicity.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Multiplicities along continuous polynomial sections

For a coefficientwise continuous family of locally bounded degree, multiplicity at a continuous
point is locally bounded above by its central value, provided the central polynomial is nonzero.
Hasse derivatives give this statement in arbitrary characteristic. Over an integral domain,
if each factor is nonzero at the base point and the multiplicity in a finite product is locally
constant, every factor multiplicity is locally constant: none can increase, and their sum cannot
decrease.

This transfers the multiplicities of root sections of a product to its individual factors,
including factors sharing roots and roots of multiplicity greater than one.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Section 2 (delineability of a polynomial basis).
-/

public section

open Filter Topology

namespace Polynomial

variable {B R : Type*} [TopologicalSpace B] [TopologicalSpace R]
  {r : B → R} {x₀ : B} {d : ℕ}

/-- Evaluation of a Hasse derivative along a point continuous at `x₀` is continuous at `x₀`
for a family whose coefficients of indices from `m` through `d` are continuous at `x₀` and
whose degrees are bounded by `d` near `x₀`. Coefficients below `m` do not affect the derivative. -/
theorem continuousAt_hasseDeriv_eval [Semiring R] [IsTopologicalSemiring R] {F : B → R[X]}
    (m : ℕ) (hF : ∀ i, m ≤ i → i ≤ d → ContinuousAt (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hr : ContinuousAt r x₀) :
    ContinuousAt (fun x ↦ (hasseDeriv m (F x)).eval (r x)) x₀ := by
  first
  | have hcoeff (i : ℕ) : ContinuousAt (fun x ↦ (hasseDeriv m (F x)).coeff i) x₀ := by
      by_cases hi : i + m ≤ d
      · simp only [hasseDeriv_coeff]
        exact continuousAt_const.mul (hF _ (Nat.le_add_left m i) hi)
      · refine (continuousAt_const (y := (0 : R))).congr_of_eventuallyEq ?_
        filter_upwards [hdeg] with x hx
        simp [hasseDeriv_coeff, coeff_eq_zero_of_natDegree_lt (hx.trans_lt (Nat.lt_of_not_ge hi))]
    exact continuousAt_eval (fun i _ ↦ hcoeff i)
      (hdeg.mono fun x hx ↦
        (natDegree_hasseDeriv_le _ _).trans ((Nat.sub_le _ _).trans hx)) hr

variable [CommRing R] [IsTopologicalSemiring R] {F : B → R[X]}

/-- Multiplicity at a continuous point cannot increase nearby when the central polynomial
is nonzero. Zero nearby polynomials are allowed, with their usual multiplicity zero. -/
theorem eventually_rootMultiplicity_le [T1Space R]
    (hF : ∀ i ≤ d, ContinuousAt (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hr : ContinuousAt r x₀)
    (hne : F x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, (F x).rootMultiplicity (r x) ≤ (F x₀).rootMultiplicity (r x₀) := by
  first
  | filter_upwards [(continuousAt_hasseDeriv_eval _ (fun i _ hi ↦ hF i hi) hdeg hr).eventually_ne
      (eval_hasseDeriv_rootMultiplicity_ne_zero hne (r x₀))] with x hx
    rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
    exact natTrailingDegree_le_of_ne_zero (by rwa [taylor_coeff])

/-- Along a continuous point, locally constant multiplicity in a nonzero finite product
forces locally constant multiplicity in every factor. No coprimality is required. -/
theorem eventually_rootMultiplicity_eq_of_prod [IsDomain R] [T1Space R]
    {ι : Type*} {F : ι → B → R[X]} {d : ι → ℕ} (s : Finset ι)
    (hF : ∀ k ∈ s, ∀ i ≤ d k, ContinuousAt (fun x ↦ (F k x).coeff i) x₀)
    (hdeg : ∀ k ∈ s, ∀ᶠ x in 𝓝 x₀, (F k x).natDegree ≤ d k) (hr : ContinuousAt r x₀)
    (hne : ∀ k ∈ s, F k x₀ ≠ 0)
    (hmult : ∀ᶠ x in 𝓝 x₀,
      (∏ k ∈ s, F k x).rootMultiplicity (r x) =
        (∏ k ∈ s, F k x₀).rootMultiplicity (r x₀)) :
    ∀ᶠ x in 𝓝 x₀, ∀ k ∈ s, (F k x).rootMultiplicity (r x) =
      (F k x₀).rootMultiplicity (r x₀) := by
  first
  | classical
    have hsum (x : B) (hx : ∀ k ∈ s, F k x ≠ 0) :
        (∏ k ∈ s, F k x).rootMultiplicity (r x) =
          ∑ k ∈ s, (F k x).rootMultiplicity (r x) := by
      rw [← count_roots, roots_prod _ _ (Finset.prod_ne_zero_iff.2 hx), Multiset.count_bind]
      simp only [count_roots, Finset.sum_map_val]
    have hle := (eventually_all_finset s).2 fun k hk ↦
      eventually_rootMultiplicity_le (hF k hk) (hdeg k hk) hr (hne k hk)
    have hnonzero : ∀ᶠ x in 𝓝 x₀, ∀ k ∈ s, F k x ≠ 0 :=
      (eventually_all_finset s).2 fun k hk ↦ by
        have hc := (hF k hk _ (hdeg k hk).self_of_nhds).eventually_ne
          (by simpa only [coeff_natDegree] using (leadingCoeff_ne_zero.2 (hne k hk)))
        exact hc.mono fun x hx hzero ↦ hx (by simp [hzero])
    filter_upwards [hle, hnonzero, hmult] with x hx hxne hxm
    rw [hsum x hxne, hsum x₀ hne] at hxm
    exact (Finset.sum_eq_sum_iff_of_le hx).1 hxm

end Polynomial

namespace TauCeti.Polynomial

variable {B R ι : Type*} [TopologicalSpace B] [PreconnectedSpace B]
  [TopologicalSpace R] [CommRing R] [IsTopologicalSemiring R] [IsDomain R] [T1Space R]
  {F : ι → B → _root_.Polynomial R} {r : B → R} {d : ι → ℕ}

/-- Constant multiplicity along a continuous point in a nonzero finite product forces
constant multiplicity in each factor on a preconnected base. Only degree bounds are needed;
the factors need not be coprime. -/
theorem rootMultiplicity_eq_of_prod (s : Finset ι)
    (hF : ∀ k ∈ s, ∀ i ≤ d k, Continuous fun x ↦ (F k x).coeff i)
    (hdeg : ∀ k ∈ s, ∀ x, (F k x).natDegree ≤ d k) (hr : Continuous r)
    (hne : ∀ k ∈ s, ∀ x, F k x ≠ 0)
    (hmult : ∀ x y, (∏ k ∈ s, F k x).rootMultiplicity (r x) =
      (∏ k ∈ s, F k y).rootMultiplicity (r y))
    (k : ι) (hk : k ∈ s) (x y : B) :
    (F k x).rootMultiplicity (r x) = (F k y).rootMultiplicity (r y) := by
  first
  | have hl : IsLocallyConstant fun x ↦ (F k x).rootMultiplicity (r x) := by
      refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x₀ ↦ ?_
      exact (_root_.Polynomial.eventually_rootMultiplicity_eq_of_prod s
        (fun k hk i hi ↦ (hF k hk i hi).continuousAt)
        (fun k hk ↦ .of_forall (hdeg k hk)) hr.continuousAt
        (fun k hk ↦ hne k hk x₀) (.of_forall fun x ↦ hmult x x₀)).mono
          fun _ hx ↦ hx k hk
    exact hl.apply_eq_of_preconnectedSpace x y

end TauCeti.Polynomial
end -- closes the original EOF section from source line 34
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Topology/Algebra/Polynomial/RootMultiplicity.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Polynomial/RealRoots/Common.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Common ordered real roots of a finite family of real polynomials

Let `F k x`, for `k` in a finite index type, be real polynomials of fixed degrees whose
coefficients depend continuously on a parameter `x`. Suppose that the number of distinct complex
roots of each member is locally nonincreasing and that the degree of the gcd of every pair of
distinct members is locally constant. The family matching lemma
`Polynomial.eventually_exists_bijOn_biUnion_roots_toFinset` then shows that the product of the
members has a locally constant number of distinct complex roots, so the results of
`TauCeti/Analysis/Polynomial/RealRoots/Ordered.lean` apply to the product.

On a nonempty preconnected base this gives a single finite list of continuous, strictly increasing
functions enumerating, at every parameter, the real roots of all the members together, such that
the multiplicity of each listed root in each member is the same at every parameter. In particular
membership of a listed root in the root set of each member does not depend on the parameter. This
is the common ordered list of real roots over which a delineable family is stacked.

The hypothesis on distinct complex roots follows from gcd data: the number of distinct complex
roots of a nonzero real polynomial is its degree minus the degree of its gcd with its derivative.
So both results also hold when each member has locally constant degree of its gcd with its
derivative. By the subresultant gcd criterion, this is what fixed vanishing of principal
subresultant coefficients provides.

The underlying topological gluing argument is provided separately for any local continuous,
strictly increasing enumerations of an intrinsic set of real roots. It does not require the
coefficient hypotheses used to construct such enumerations.

## Main results

* `TauCeti.exists_roots_of_locally`: glue local ordered real-root enumerations over a nonempty
  preconnected base.
* `Polynomial.eventually_card_aroots_prod_eq`: the product of the members has locally constant
  number of distinct complex roots.
* `Polynomial.exists_continuous_ordered_common_roots_of_preconnectedSpace`: the common ordered list
  of real roots with constant multiplicities in every member.
* `Polynomial.eventually_exists_bijOn_biUnion_aroots_toFinset_of_natDegree_gcd_derivative`: the
  family matching lemma with locally constant degrees of the gcds of the members with their
  derivatives in place of the hypothesis on distinct complex roots.
* `Polynomial.exists_continuous_ordered_common_roots_of_natDegree_gcd_derivative`: the common
  ordered list of real roots under the same gcd hypotheses.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of roots and delineability).
-/

public section

open Filter Function Metric Polynomial Set Topology TauCeti

namespace TauCeti

variable {X ι : Type*} [TopologicalSpace X] {P : ι → X → ℝ[X]}

/-- Local continuous strictly increasing enumerations `θ a` of an intrinsic set `Z y ⊆ ℝ` on
open neighborhoods `U a` glue over a nonempty preconnected base. The local counts are globally
constant, the glued root functions are continuous, strictly increasing and enumerate `Z`, and
they agree with every local enumeration. If every local enumeration has constant root
multiplicities in a family `P`, so do the glued roots. -/
theorem exists_roots_of_locally [PreconnectedSpace X] [Nonempty X] {Z : X → Set ℝ}
    {U : X → Set X} (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x) {c : X → ℕ}
    {θ : ∀ a, Fin (c a) → U a → ℝ} {μ : ∀ a, ι → Fin (c a) → ℕ}
    (hθc : ∀ a i, Continuous (θ a i)) (hθmono : ∀ a (y : U a), StrictMono fun i ↦ θ a i y)
    (hθrange : ∀ a (y : U a), range (fun i ↦ θ a i y) = Z y)
    (hθmult : ∀ a k i (y : U a), (P k y).rootMultiplicity (θ a i y) = μ a k i) :
    ∃ (n : ℕ) (hc : ∀ x, c x = n) (r : Fin n → X → ℝ) (m : ι → Fin n → ℕ),
      (∀ i, Continuous (r i)) ∧ (∀ x, StrictMono fun i ↦ r i x) ∧
      (∀ x, range (fun i ↦ r i x) = Z x) ∧
      (∀ k i x, (P k x).rootMultiplicity (r i x) = m k i) ∧
      ∀ a (y : U a) i, r i y = θ a (Fin.cast (hc a).symm i) y := by
  first
  | classical
    let a₀ : X := Classical.arbitrary X
    have hcard (a : X) (y : U a) : Nat.card (Z y) = c a := by
      rw [← hθrange a y, Nat.card_range_of_injective (hθmono a y).injective]
      simp
    -- The number of roots is locally constant, hence globally constant.
    have hclocal : IsLocallyConstant fun x ↦ Nat.card (Z x) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
      filter_upwards [(hU a).mem_nhds (hxU a)] with y hy
      exact (hcard a ⟨y, hy⟩).trans (hcard a ⟨a, hxU a⟩).symm
    let n := Nat.card (Z a₀)
    have hc (a : X) : c a = n :=
      (hcard a ⟨a, hxU a⟩).symm.trans (hclocal.apply_eq_of_preconnectedSpace a a₀)
    let r (i : Fin n) (x : X) := θ x (Fin.cast (hc x).symm i) ⟨x, hxU x⟩
    have hrmono (x : X) : StrictMono fun i ↦ r i x :=
      (hθmono x ⟨x, hxU x⟩).comp (Fin.cast_strictMono (hc x).symm)
    have hrrange (x : X) : range (fun i ↦ r i x) = Z x := by
      exact ((Fin.castOrderIso (hc x).symm).surjective.range_comp _).trans
        (hθrange x ⟨x, hxU x⟩)
    -- Increasing complete lists agree on overlaps. This identifies the pointwise
    -- choice with each local continuous root function, including its multiplicity.
    have hrU (a : X) (y : U a) (i : Fin n) : r i y = θ a (Fin.cast (hc a).symm i) y := by
      have hmono := (hθmono a y).comp (Fin.cast_strictMono (hc a).symm)
      apply congrFun (((hrmono y).range_inj_of_wellFoundedLT hmono).1 ?_) i
      exact (hrrange y).trans (((Fin.castOrderIso (hc a).symm).surjective.range_comp _).trans
        (hθrange a y)).symm
    have hrc (i : Fin n) : Continuous (r i) := by
      refine continuous_iff_continuousAt.2 fun a ↦ ?_
      have hcont : ContinuousOn (r i) (U a) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact (hθc a _).congr fun y ↦ (hrU a y i).symm
      exact (hU a).continuousOn_iff.mp hcont (hxU a)
    let m (k : ι) (i : Fin n) := (P k a₀).rootMultiplicity (r i a₀)
    have hm (k : ι) (i : Fin n) (x : X) : (P k x).rootMultiplicity (r i x) = m k i := by
      have hmult : IsLocallyConstant fun y ↦ (P k y).rootMultiplicity (r i y) := by
        refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
        filter_upwards [(hU a).mem_nhds (hxU a)] with y hy
        rw [hrU a ⟨y, hy⟩ i, hrU a ⟨a, hxU a⟩ i, hθmult, hθmult]
      exact hmult.apply_eq_of_preconnectedSpace x a₀
    exact ⟨n, hc, r, m, hrc, hrmono, hrrange, hm, hrU⟩

end TauCeti

namespace Polynomial

variable {B : Type*} [TopologicalSpace B] {ι : Type*} [Fintype ι] {F : ι → B → ℝ[X]}
  {d : ι → ℕ}

/-- **Family matching lemma for real polynomials.** Let `F k x` be real polynomials of degree
`d k` near `x₀`, for `k` in a finite index type, whose coefficients of index at most `d k` are
continuous at `x₀`. Suppose that near `x₀` no member has more distinct complex roots than at `x₀`,
and that the degree of the gcd of every pair of distinct members is the same as at `x₀`. Then for
`x` near `x₀` there is a single bijection `e` from the distinct complex roots of all the `F k x₀`
onto those of all the `F k x` that moves each root by less than `ε` and preserves its multiplicity
in every member. -/
theorem eventually_exists_bijOn_biUnion_aroots_toFinset {x₀ : B}
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀,
      ((F k x).aroots ℂ).toFinset.card ≤ ((F k x₀).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : ℂ → ℂ,
      Set.BijOn e (Finset.univ.biUnion fun k => ((F k x₀).aroots ℂ).toFinset)
        (Finset.univ.biUnion fun k => ((F k x).aroots ℂ).toFinset) ∧
      ∀ z ∈ Finset.univ.biUnion (fun k => ((F k x₀).aroots ℂ).toFinset), ‖e z - z‖ < ε ∧
        ∀ k, ((F k x).map (algebraMap ℝ ℂ)).rootMultiplicity (e z) =
          ((F k x₀).map (algebraMap ℝ ℂ)).rootMultiplicity z := by
  first
  | simp only [aroots_def] at hcard ⊢
    refine eventually_exists_bijOn_biUnion_roots_toFinset (fun k i hi => ?_)
      (fun k => (hdeg k).mono fun x hx => by rw [degree_map, hx]) hcard
      (fun k l hkl => (hgcd hkl).mono fun x hx => by rw [gcd_map, gcd_map, natDegree_map,
        natDegree_map, hx]) hε
    simpa only [coeff_map, Complex.coe_algebraMap, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.comp (hF k i hi)

/-- **Distinct complex roots of the product of a family.** Under the hypotheses of the family
matching lemma for real polynomials, the product of the members has, near `x₀`, as many distinct
complex roots as at `x₀`. -/
theorem eventually_card_aroots_prod_eq {x₀ : B}
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀,
      ((F k x).aroots ℂ).toFinset.card ≤ ((F k x₀).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∀ᶠ x in 𝓝 x₀,
      ((∏ k, F k x).aroots ℂ).toFinset.card = ((∏ k, F k x₀).aroots ℂ).toFinset.card := by
  first
  | have hne {x : B} (hx : ∀ k, (F k x).degree = d k) (k : ι) (_ : k ∈ Finset.univ) :
        (F k x).map (algebraMap ℝ ℂ) ≠ 0 := by
      rw [Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective]
      rintro h
      simpa [h] using hx k
    filter_upwards [eventually_exists_bijOn_biUnion_aroots_toFinset hF hdeg hcard hgcd one_pos,
      eventually_all.2 hdeg] with x ⟨e, he, _⟩ hx
    rw [aroots_prod_toFinset _ _ (hne hx),
      aroots_prod_toFinset _ _ (hne fun k => (hdeg k).self_of_nhds)]
    exact (Finset.card_nbij e he.mapsTo he.injOn he.surjOn).symm

/-- **Family matching lemma for real polynomials, gcd form.** Let `F k x` be real polynomials of
degree `d k` near `x₀`, for `k` in a finite index type, whose coefficients of index at most `d k`
are continuous at `x₀`. Suppose that near `x₀` the degree of the gcd of each member with its
derivative, and the degree of the gcd of every pair of distinct members, are the same as at
`x₀`. Then for `x` near `x₀` there is a single bijection `e` from the distinct complex roots of
all the `F k x₀` onto those of all the `F k x` that moves each root by less than `ε` and preserves
its multiplicity in every member. -/
theorem eventually_exists_bijOn_biUnion_aroots_toFinset_of_natDegree_gcd_derivative {x₀ : B}
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hder : ∀ k, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F k x).derivative).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F k x₀).derivative).natDegree)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : ℂ → ℂ,
      Set.BijOn e (Finset.univ.biUnion fun k => ((F k x₀).aroots ℂ).toFinset)
        (Finset.univ.biUnion fun k => ((F k x).aroots ℂ).toFinset) ∧
      ∀ z ∈ Finset.univ.biUnion (fun k => ((F k x₀).aroots ℂ).toFinset), ‖e z - z‖ < ε ∧
        ∀ k, ((F k x).map (algebraMap ℝ ℂ)).rootMultiplicity (e z) =
          ((F k x₀).map (algebraMap ℝ ℂ)).rootMultiplicity z :=
  eventually_exists_bijOn_biUnion_aroots_toFinset hF hdeg
    (fun k => (eventually_card_aroots_toFinset_eq_of_natDegree_gcd_derivative (K := ℂ) (hdeg k)
      (hder k)).mono fun _ hx => hx.le) hgcd hε

omit [Fintype ι] in
/-- **Common ordered real roots.** Let `F k x` be real polynomials of degree `d k`, for `k` in a
finite index type, whose coefficients depend continuously on a parameter in a nonempty
preconnected space. Suppose that the number of distinct complex roots of each member is locally
nonincreasing, and the degree of the gcd of every pair of distinct members is locally constant.
Then there are finitely many continuous functions `r x 0 < ⋯ < r x (n - 1)` whose values at each
`x` are exactly the real roots of the members `F k x` together, and the multiplicity of `r x i` as
a root of each member `F k x` does not depend on `x`. -/
theorem exists_continuous_ordered_common_roots_of_preconnectedSpace [Finite ι]
    [PreconnectedSpace B] [Nonempty B] (hF : ∀ k, ∀ i ≤ d k, Continuous (fun x => (F k x).coeff i))
    (hdeg : ∀ k x, (F k x).degree = d k)
    (hcard : ∀ k x₀, ∀ᶠ x in 𝓝 x₀,
      ((F k x).aroots ℂ).toFinset.card ≤ ((F k x₀).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l => ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∃ n : ℕ, ∃ r : B → Fin n → ℝ,
      (∀ i, Continuous (fun x => r x i)) ∧ (∀ x, StrictMono (r x)) ∧
      (∀ x t, (∃ k, (F k x).IsRoot t) ↔ ∃ i, r x i = t) ∧
      (∀ k i x y, (F k x).rootMultiplicity (r x i) = (F k y).rootMultiplicity (r y i)) := by
  first
  | cases nonempty_fintype ι
    have hne (k : ι) (x : B) : F k x ≠ 0 := by
      rintro h
      simpa [h] using hdeg k x
    -- every coefficient of every member, not only those up to its degree, is continuous
    have hF' (k : ι) (i : ℕ) : Continuous fun x => (F k x).coeff i := by
      by_cases hi : i ≤ d k
      · exact hF k i hi
      · refine continuous_const.congr fun x => (coeff_eq_zero_of_degree_lt ?_).symm
        rw [hdeg k x]
        exact_mod_cast Nat.lt_of_not_le hi
    -- the results on ordered real roots apply to the product of the members
    obtain ⟨n, r, hrc, hrm, hroots, hmult⟩ :=
      exists_continuous_ordered_roots_of_preconnectedSpace (F := fun x => ∏ k, F k x)
        (d := ∑ k, d k)
        (fun i _ => continuous_iff_continuousAt.2 fun x =>
          continuousAt_coeff_prod _ (fun k _ i _ => (hF' k i).continuousAt))
        (fun x => by rw [degree_prod, Nat.cast_sum]; exact Finset.sum_congr rfl fun k _ => hdeg k x)
        (fun x₀ => (eventually_card_aroots_prod_eq (fun k i hi => (hF k i hi).continuousAt)
          (fun k => Eventually.of_forall (hdeg k)) (fun k => hcard k x₀)
          fun k l hkl => hgcd hkl x₀).mono fun x hx => hx.le)
    have hroot (x : B) (t : ℝ) : (∃ k, (F k x).IsRoot t) ↔ ∃ i, r x i = t := by
      rw [← hroots x t, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
      simp only [Finset.mem_univ, true_and, IsRoot.def]
    exact ⟨n, r, hrc, hrm, hroot, fun k i =>
      TauCeti.Polynomial.rootMultiplicity_eq_of_prod Finset.univ
        (fun k _ j hj => hF k j hj)
        (fun k _ x => (natDegree_eq_of_degree_eq_some (hdeg k x)).le)
        (hrc i) (fun k _ => hne k) (hmult i) k (Finset.mem_univ k)⟩

omit [Fintype ι] in
/-- **Common ordered real roots, gcd form.** Let `F k x` be real polynomials of degree `d k`, for
`k` in a finite index type, whose coefficients depend continuously on a parameter in a nonempty
preconnected space. Suppose that the degree of the gcd of each member with its derivative, and
the degree of the gcd of every pair of distinct members, are locally constant. Then there are
finitely many continuous functions `r x 0 < ⋯ < r x (n - 1)` whose values at each `x` are exactly
the real roots of the members `F k x` together, and the multiplicity of `r x i` as a root of each
member `F k x` does not depend on `x`. -/
theorem exists_continuous_ordered_common_roots_of_natDegree_gcd_derivative
    [Finite ι] [PreconnectedSpace B] [Nonempty B]
    (hF : ∀ k, ∀ i ≤ d k, Continuous (fun x => (F k x).coeff i))
    (hdeg : ∀ k x, (F k x).degree = d k)
    (hder : ∀ k x₀, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F k x).derivative).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F k x₀).derivative).natDegree)
    (hgcd : Pairwise fun k l => ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∃ n : ℕ, ∃ r : B → Fin n → ℝ,
      (∀ i, Continuous (fun x => r x i)) ∧ (∀ x, StrictMono (r x)) ∧
      (∀ x t, (∃ k, (F k x).IsRoot t) ↔ ∃ i, r x i = t) ∧
      (∀ k i x y, (F k x).rootMultiplicity (r x i) = (F k y).rootMultiplicity (r y i)) :=
  exists_continuous_ordered_common_roots_of_preconnectedSpace hF hdeg
    (fun k x₀ => (eventually_card_aroots_toFinset_eq_of_natDegree_gcd_derivative (K := ℂ)
      (Eventually.of_forall (hdeg k)) (hder k x₀)).mono fun _ hx => hx.le) hgcd

end Polynomial
end -- closes the original EOF section from source line 61
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Polynomial/RealRoots/Common.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Sign.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sign-invariance on the cells of a stack

Let `θ₀ < θ₁ < … < θₖ₋₁` be continuous functions on a preconnected base `X`, and let `f` be a
continuous function on the cylinder `X × ℝ`. If every zero of `f` lies on one of the sections,
then `f` has no zero on any sector, so it is sign-invariant on each sector, because the sectors
are preconnected. If moreover the zeros of `f` are exactly the points of the sections indexed by
some `I`, then `f` vanishes on the sections indexed by `I` and has no zero on the others, so it is
sign-invariant on each section as well.

For a family `P : X → ℝ[X]` of polynomials whose evaluation is jointly continuous, this is the
step of delineability that turns root data into sign data. Suppose either every `P x` is zero, or
none is and the roots of each `P x` are exactly the values `θ i x` for `i ∈ I`. Then
`(x, t) ↦ (P x).eval t` is sign-invariant on every section and every sector of the stack. Only
the location of the roots matters here; their multiplicities do not.

## Main declarations

* `TauCeti.signInvariant_sectionSet`, `TauCeti.signInvariant_sectorSet`: sign-invariance on the
  sections and sectors of a continuous function whose zeros lie on sections.
* `TauCeti.signInvariant_eval_sectionSet`, `TauCeti.signInvariant_eval_sectorSet`: the same for
  the evaluation of a polynomial family whose roots are given by the stack.
* `TauCeti.exists_forall_eq_zero_or_exists_forall_mem_sectorSet`: if whether `0` is a value of
  the stack does not depend on the base point, then either a section vanishes identically or `0`
  lies in one fixed sector.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1.
-/

public section

open Function Polynomial Set

namespace TauCeti

variable {X α R : Type*} {k : ℕ} [TopologicalSpace X] [PreconnectedSpace X]
  [Zero R] [LinearOrder R] [TopologicalSpace R] [OrderTopology R]

/-- Over a preconnected base, a function on the cylinder is sign-invariant on the section of a
continuous function `θ i` of a stack whose sections are disjoint, provided its zeros are exactly
the points of the sections indexed by some set `I`. It vanishes on the section if `i ∈ I`, and is
nowhere zero on it otherwise. -/
theorem signInvariant_sectionSet [TopologicalSpace α] {θ : Fin k → X → α} {f : X × α → R}
    {I : Set (Fin k)} {i : Fin k} (hf : ContinuousOn f (sectionSet θ i))
    (hc : Continuous (θ i)) (hθ : ∀ x, Injective fun i ↦ θ i x)
    (hzero : ∀ z, f z = 0 ↔ ∃ i ∈ I, z ∈ sectionSet θ i) :
    SignInvariant f (sectionSet θ i) := by
  first
  | by_cases hi : i ∈ I
    · exact (signInvariant_const 0).congr fun z hz ↦ ((hzero z).2 ⟨i, hi, hz⟩).symm
    · refine (isPreconnected_sectionSet hc).signInvariant hf fun z hz h ↦ hi ?_
      -- A zero on section `i` lies on a section indexed by `I`, which must be section `i` itself.
      obtain ⟨i', hi', hz'⟩ := (hzero z).1 h
      rwa [← hθ z.1 ((mem_sectionSet.1 hz').trans (mem_sectionSet.1 hz).symm)]

/-- Over a preconnected base, a function on the cylinder whose zeros all lie on sections is
sign-invariant on each sector of a stack of continuous, pointwise strictly ordered real
functions. -/
theorem signInvariant_sectorSet {θ : Fin k → X → ℝ} {f : X × ℝ → R} {j : Fin (k + 1)}
    (hf : ContinuousOn f (sectorSet θ j)) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hzero : ∀ z, f z = 0 → ∃ i, z ∈ sectionSet θ i) :
    SignInvariant f (sectorSet θ j) :=
  (isPreconnected_sectorSet hc hθ j).signInvariant hf fun z hz h ↦
    let ⟨i, hi⟩ := hzero z h
    disjoint_left.1 (disjoint_sectionSet_sectorSet θ i j) hi hz

/-- Let `P` be a family of polynomials over a preconnected base, with jointly continuous
evaluation, which is either zero everywhere or nowhere zero. If the roots of each nonzero `P x`
are exactly the values `θ i x` for `i ∈ I`, where the `θ i x` are pointwise distinct, then the
evaluation of `P` is sign-invariant on the section of each continuous `θ i`. -/
theorem signInvariant_eval_sectionSet {K : Type*} [Semiring K] [LinearOrder K]
    [TopologicalSpace K] [OrderTopology K] {θ : Fin k → X → K} {P : X → K[X]}
    {I : Set (Fin k)} {i : Fin k} (hP : Continuous fun z : X × K ↦ (P z.1).eval z.2)
    (hc : Continuous (θ i)) (hθ : ∀ x, Injective fun i ↦ θ i x)
    (hnull : (∀ x, P x = 0) ∨ ∀ x, P x ≠ 0)
    (hroots : ∀ x, P x ≠ 0 → ∀ t, (P x).eval t = 0 ↔ ∃ i ∈ I, θ i x = t) :
    SignInvariant (fun z : X × K ↦ (P z.1).eval z.2) (sectionSet θ i) := by
  first
  | rcases hnull with h | h
    · exact (signInvariant_const 0).congr fun z _ ↦ by simp [h]
    · exact signInvariant_sectionSet hP.continuousOn hc hθ fun z ↦ by
        simpa only [mem_sectionSet] using hroots z.1 (h z.1) z.2

/-- Let `P` be a family of real polynomials over a preconnected base, with jointly continuous
evaluation, which is either zero everywhere or nowhere zero. If every root of each nonzero `P x`
is one of the values `θ i x` of a stack of continuous, pointwise strictly ordered functions, then
the evaluation of `P` is sign-invariant on each sector of the stack. -/
theorem signInvariant_eval_sectorSet {θ : Fin k → X → ℝ} {P : X → ℝ[X]} {j : Fin (k + 1)}
    (hP : Continuous fun z : X × ℝ ↦ (P z.1).eval z.2) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hnull : (∀ x, P x = 0) ∨ ∀ x, P x ≠ 0)
    (hroots : ∀ x, P x ≠ 0 → ∀ t, (P x).eval t = 0 → ∃ i, θ i x = t) :
    SignInvariant (fun z : X × ℝ ↦ (P z.1).eval z.2) (sectorSet θ j) := by
  first
  | rcases hnull with h | h
    · exact (signInvariant_const 0).congr fun z _ ↦ by simp [h]
    · exact signInvariant_sectorSet hP.continuousOn hc hθ fun z hz ↦ by
        simpa only [mem_sectionSet] using hroots z.1 (h z.1) z.2 hz

/-- Let `θ` be a stack of continuous, pointwise strictly ordered real functions over a
preconnected base, such that whether `0` is one of the values `θ i x` does not depend on the base
point `x`. Then either one of the `θ i` vanishes identically, or `0` lies in one fixed sector over
every base point. -/
theorem exists_forall_eq_zero_or_exists_forall_mem_sectorSet {θ : Fin k → X → ℝ}
    (hθc : ∀ i, Continuous (θ i)) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    (h : ∀ x y, (∃ i, θ i x = 0) → ∃ i, θ i y = 0) (x₀ : X) :
    (∃ i, ∀ x, θ i x = 0) ∨ ∃ j, ∀ x, (x, (0 : ℝ)) ∈ sectorSet θ j := by
  first
  | by_cases hz : ∃ i, θ i x₀ = 0
    · obtain ⟨i₀, hi₀⟩ := hz
      -- The zero set of `θ i₀` is closed, and so is its complement: the union of the zero sets
      -- of the other functions of the stack.
      have hcompl : {x | θ i₀ x = 0}ᶜ = ⋃ i ∈ ({i₀}ᶜ : Set (Fin k)), {x | θ i x = 0} := by
        ext y
        simp only [mem_compl_iff, mem_ofPred_eq, mem_iUnion, mem_singleton_iff, exists_prop]
        refine ⟨fun hy ↦ ?_, fun ⟨i, hii, hi⟩ hy ↦ hii ((hθ y).injective (hi.trans hy.symm))⟩
        obtain ⟨i, hi⟩ := h x₀ y ⟨i₀, hi₀⟩
        exact ⟨i, fun hii ↦ hy (hii ▸ hi), hi⟩
      have hclopen : IsClopen {x | θ i₀ x = 0} := by
        refine ⟨isClosed_eq (hθc i₀) continuous_const, ?_⟩
        rw [← isClosed_compl_iff, hcompl]
        exact (Set.toFinite _).isClosed_biUnion fun i _ ↦ isClosed_eq (hθc i) continuous_const
      exact Or.inl ⟨i₀, fun x ↦ (hclopen.eq_univ ⟨x₀, hi₀⟩).ge (mem_univ x)⟩
    · push Not at hz
      have hne (x : X) (i : Fin k) : θ i x ≠ 0 := fun hx ↦ by
        obtain ⟨i', hi'⟩ := h x x₀ ⟨i, hx⟩
        exact hz i' hi'
      -- No function of the stack changes sign.
      have hsign (i : Fin k) (x : X) : SignType.sign (θ i x) = SignType.sign (θ i x₀) :=
        signInvariant_def.1 (isPreconnected_univ.signInvariant (hθc i).continuousOn
          fun z _ ↦ hne z i) x (mem_univ x) x₀ (mem_univ x₀)
      obtain ⟨j, hj⟩ : ∃ j, (x₀, (0 : ℝ)) ∈ sectorSet θ j := by
        have hmem := (iUnion_sectionSet_union_iUnion_sectorSet (fun x ↦ (hθ x).monotone)).symm ▸
          mem_univ (x₀, (0 : ℝ))
        rcases hmem with hs | hs
        · obtain ⟨i, hi⟩ := mem_iUnion.1 hs
          exact absurd (mem_sectionSet.1 hi) (hz i)
        · exact mem_iUnion.1 hs
      rw [mem_sectorSet] at hj
      refine Or.inr ⟨j, fun x ↦ mem_sectorSet.2 ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩⟩
      · rw [← sign_eq_neg_one_iff, hsign, sign_eq_neg_one_iff]
        exact hj.1 i hi
      · rw [← sign_eq_one_iff, hsign, sign_eq_one_iff]
        exact hj.2 i hi

end TauCeti
end -- closes the original EOF section from source line 45
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Sign.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Eval/Sign.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Polynomial evaluation signs under ordered embeddings

Mapping coefficients and the evaluation point through a strictly monotone ring homomorphism
preserves the sign of the value. This applies to embeddings into ordered real closures.
Over an ordered commutative ring, rescaling the roots by a nonzero factor `a` and multiplying by
`a ^ natDegree` preserves the sign at the correspondingly rescaled point.
-/

public section

namespace Polynomial

/-- Mapping a polynomial and its evaluation point through a strictly monotone ring homomorphism
preserves its sign. -/
theorem sign_eval_map {R S : Type*} [Semiring R] [LinearOrder R]
    [Semiring S] [Preorder S] [DecidableLT S] (p : R[X]) (f : R →+* S)
    (hf : StrictMono f) (x : R) :
    SignType.sign ((p.map f).eval (f x)) = SignType.sign (p.eval x) := by
  first
  | rw [eval_map_apply]
    exact hf.sign_comp _

/-- **Rescaling preserves signs.** Evaluating `C (a ^ q.natDegree) * q.scaleRoots a` at `f a * z`
multiplies the value of `q` at `z` by the positive square `(f a * f a) ^ q.natDegree`. -/
theorem sign_eval₂_C_pow_mul_scaleRoots {R S : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [CommSemiring S] (f : S →+* R) (q : S[X]) {a : S} (ha : f a ≠ 0)
    (z : R) :
    SignType.sign ((C (a ^ q.natDegree) * q.scaleRoots a).eval₂ f (f a * z)) =
      SignType.sign (q.eval₂ f z) := by
  first
  | simp [eval₂_pow, scaleRoots_eval₂_mul, ← mul_assoc, ← mul_pow, sign_mul, mul_self_pos, ha]

end Polynomial
end -- closes the original EOF section from source line 21
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Eval/Sign.lean -/
