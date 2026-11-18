module

public import volume_polynomials.assembly_part06

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

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Rolle.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Polynomial Rolle and mean value

`TauCeti.PolynomialRolle R` states that equal polynomial values at distinct endpoints give
an interior root of the formal derivative. From this explicit hypothesis,
`PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul` derives polynomial mean value; over an
ordered field, `PolynomialRolle.monotoneOn`, `antitoneOn`, `strictMonoOn`, and `strictAntiOn`
derive the corresponding order properties from derivative signs.

Roots of the derivative separate the roots of the polynomial. A field with polynomial Rolle has
characteristic zero (`PolynomialRolle.charZero`), a polynomial is injective on every
order-connected set free of derivative roots (`PolynomialRolle.injOn_eval`), and the number of
roots of `p`, distinct or counted with multiplicity, is at most one more than the corresponding
number for `p.derivative` (`PolynomialRolle.card_roots_toFinset_le_derivative`,
`PolynomialRolle.card_roots_le_derivative`). These are the algebraic counterparts of the
real-analytic root counts in `Mathlib.Analysis.Calculus.LocalExtr.Polynomial`, whose proofs
(by Benjamin Davidson and Yury Kudryashov) they follow with polynomial Rolle in place of Rolle's
theorem for differentiable functions.

`TauCeti.FieldTheory.RealClosure.AbstractRolle` supplies this hypothesis from `IsRealClosed`
as `TauCeti.RealClosure.polynomialRolle_of_isRealClosed`, and exports direct `Polynomial`
versions of the mean value and monotonicity results for real closed ordered fields. Over a
real closed field, the root counts are applied as, for instance,
`polynomialRolle_of_isRealClosed.card_roots_le_derivative`. The `IsRealClosed ℝ` instance
specializes those statements to the real numbers.
-/

public section

open Polynomial Set

namespace TauCeti

/-- Polynomial Rolle: whenever a polynomial takes equal values at `a < b`, its formal
derivative has a root in `Ioo a b`. -/
def PolynomialRolle (R : Type*) [Field R] [LinearOrder R] : Prop :=
  ∀ (p : R[X]) (a b : R), a < b → p.eval a = p.eval b →
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0

variable {R : Type*} [Field R] [LinearOrder R]

/-- Construct the polynomial Rolle property from its quantified statement. -/
theorem PolynomialRolle.of_forall
    (h : ∀ (p : R[X]) (a b : R), a < b → p.eval a = p.eval b →
      ∃ c ∈ Ioo a b, p.derivative.eval c = 0) : PolynomialRolle R := h

/-- Equal polynomial values at distinct endpoints give an interior derivative root. -/
theorem PolynomialRolle.exists_derivative_root (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hab : a < b) (heq : p.eval a = p.eval b) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := h p a b hab heq

/-- Polynomial Rolle implies the mean value equality
`p.eval b - p.eval a = p.derivative.eval c * (b - a)` at some point `c ∈ Ioo a b`. -/
theorem PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul
    (h : PolynomialRolle R) (p : R[X]) {a b : R} (hab : a < b) :
    ∃ c ∈ Ioo a b, p.eval b - p.eval a = p.derivative.eval c * (b - a) := by
  first
  | have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    set m := (p.eval b - p.eval a) / (b - a)
    have hm : m * (b - a) = p.eval b - p.eval a := div_mul_cancel₀ _ hba
    obtain ⟨c, hc, hd⟩ := h.exists_derivative_root (p - C m * X) hab (by
      simp only [eval_sub, eval_mul, eval_C, eval_X]
      linear_combination hm)
    have hd' : p.derivative.eval c = m := by simpa [sub_eq_zero] using hd
    exact ⟨c, hc, by rw [hd', hm]⟩

/-- The mean value point for a subinterval lies in the surrounding open interval. -/
private theorem PolynomialRolle.exists_sub_eq (h : PolynomialRolle R) (p : R[X]) {a b u v : R}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u < v) :
    ∃ c ∈ Ioo a b, p.eval v - p.eval u = p.derivative.eval c * (v - u) := by
  first
  | obtain ⟨c, hc, he⟩ := h.exists_eval_sub_eq_derivative_eval_mul p huv
    exact ⟨c, ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩, he⟩

/-! ### Root separation by derivative roots -/

/-- A field with polynomial Rolle has characteristic zero: if `(n : R) = 0` for some `n ≥ 1`,
then `X ^ n - X` vanishes at `0` and `1` while its derivative is the constant `-1`. -/
theorem PolynomialRolle.charZero (h : PolynomialRolle R) : CharZero R := by
  first
  | refine charZero_of_inj_zero fun n hn ↦ ?_
    by_contra hn0
    have key (a b : R) (hab : a < b) (ha : a ^ n - a = 0) (hb : b ^ n - b = 0) : False := by
      obtain ⟨c, -, hc⟩ := h.exists_derivative_root (X ^ n - X) hab (by simp [ha, hb])
      simp [derivative_X_pow, hn] at hc
    have h1 : (1 : R) ^ n - 1 = 0 := by simp
    have h0 : (0 : R) ^ n - 0 = 0 := by simp [hn0]
    rcases lt_or_gt_of_ne (zero_ne_one' R) with hlt | hlt
    · exact key 0 1 hlt h0 h1
    · exact key 1 0 hlt h1 h0

/-- Roots of the derivative separate the values of a polynomial: on an order-connected set
containing no root of the derivative, the polynomial is injective. In particular such a set
contains at most one root of the polynomial. -/
theorem PolynomialRolle.injOn_eval (h : PolynomialRolle R) (p : R[X]) {s : Set R}
    (hs : s.OrdConnected) (hd : ∀ x ∈ s, p.derivative.eval x ≠ 0) : InjOn p.eval s := by
  first
  | have key {x y : R} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) : p.eval x ≠ p.eval y := fun he ↦ by
      obtain ⟨c, hc, hc0⟩ := h.exists_derivative_root p hxy he
      exact hd c (hs.out hx hy (Ioo_subset_Icc_self hc)) hc0
    intro x hx y hy he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key hx hy hlt he
    · exact key hy hx hlt he.symm

/-- Between two consecutive distinct roots of a polynomial lies a root of its derivative that is
not a root of the polynomial, so the number of distinct roots of `p` is at most one more than the
number of distinct roots of `p.derivative` that are not roots of `p`. -/
theorem PolynomialRolle.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ
    (h : PolynomialRolle R) (p : R[X]) :
    p.roots.toFinset.card ≤ (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 := by
  first
  | have := h.charZero
    rcases eq_or_ne p.derivative 0 with hp' | hp'
    · rw [eq_C_of_derivative_eq_zero hp']
      simp
    have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
    refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy hxy' ↦ ?_
    rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
    obtain ⟨z, hz, hz0⟩ := h.exists_derivative_root p hxy (hx.trans hy.symm)
    exact ⟨z, by rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot], hz⟩

/-- The number of distinct roots of a polynomial is at most one more than the number of distinct
roots of its derivative. -/
theorem PolynomialRolle.card_roots_toFinset_le_derivative (h : PolynomialRolle R) (p : R[X]) :
    p.roots.toFinset.card ≤ p.derivative.roots.toFinset.card + 1 :=
  (h.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ p).trans <| by
    grw [Finset.sdiff_subset]

/-- The number of roots of a polynomial counted with multiplicity is at most one more than the
number of roots of its derivative counted with multiplicity. -/
theorem PolynomialRolle.card_roots_le_derivative (h : PolynomialRolle R) (p : R[X]) :
    Multiset.card p.roots ≤ Multiset.card p.derivative.roots + 1 := by
  first
  | have := h.charZero
    -- A root of multiplicity `m` of `p` is a root of multiplicity at least `m - 1` of `p'`; the
    -- remaining one per distinct root is paid for by the roots of `p'` that are not roots of `p`.
    calc
      Multiset.card p.roots = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
        (Multiset.toFinset_sum_count_eq _).symm
      _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
        (Finset.sum_congr rfl fun _ hx ↦ tsub_add_cancel_of_le <|
          Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx).symm
      _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
        simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
      _ ≤ (∑ x ∈ p.roots.toFinset, p.derivative.rootMultiplicity x) +
            ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
        add_le_add
          (Finset.sum_le_sum fun _ _ ↦ rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
          (h.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ p)
      _ ≤ (∑ x ∈ p.roots.toFinset, p.derivative.roots.count x) +
            ((∑ x ∈ p.derivative.roots.toFinset \ p.roots.toFinset,
              p.derivative.roots.count x) + 1) := by
        simp only [← count_roots, Finset.card_eq_sum_ones]
        gcongr with x hx
        rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
        exact (Finset.mem_sdiff.1 hx).1
      _ = Multiset.card p.derivative.roots + 1 := by
        rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union,
          ← Multiset.toFinset_sum_count_eq, ← Finset.sum_subset Finset.subset_union_right]
        intro x _ hx₂
        simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/-- For a polynomial over a commutative ring `F` with an algebra map to `R`, the number of its
roots in `R` is at most one more than the number of roots in `R` of its derivative. -/
theorem PolynomialRolle.card_rootSet_le_derivative (h : PolynomialRolle R) {F : Type*}
    [CommRing F] [Algebra F R] (p : F[X]) :
    Fintype.card (p.rootSet R) ≤ Fintype.card (p.derivative.rootSet R) + 1 := by
  first
  | classical
    simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
      h.card_roots_toFinset_le_derivative (p.map (algebraMap F R))

variable [IsStrictOrderedRing R]

/-- Polynomial Rolle implies monotonicity where the derivative is nonnegative. -/
theorem PolynomialRolle.monotoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) := by
  first
  | intro u hu v hv huv
    rcases huv.eq_or_lt with rfl | huv
    · exact le_rfl
    obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
    rw [← sub_nonneg, he]
    exact mul_nonneg (hd c hc) (sub_pos.mpr huv).le

/-- Polynomial Rolle implies antitonicity where the derivative is nonpositive. -/
theorem PolynomialRolle.antitoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x ≤ 0) : AntitoneOn p.eval (Icc a b) := by
  first
  | intro u hu v hv huv
    rcases huv.eq_or_lt with rfl | huv
    · exact le_rfl
    obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
    rw [← sub_nonpos, he]
    exact mul_nonpos_of_nonpos_of_nonneg (hd c hc) (sub_pos.mpr huv).le

/-- Strict positivity of the derivative gives strict monotonicity. -/
theorem PolynomialRolle.strictMonoOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) := by
  first
  | intro u hu v hv huv
    obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
    rw [← sub_pos, he]
    exact mul_pos (hd c hc) (sub_pos.mpr huv)

/-- Strict negativity of the derivative gives strict antitonicity. -/
theorem PolynomialRolle.strictAntiOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0) : StrictAntiOn p.eval (Icc a b) := by
  first
  | intro u hu v hv huv
    obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
    rw [← sub_neg, he]
    exact mul_neg_of_neg_of_pos (hd c hc) (sub_pos.mpr huv)

end TauCeti
end -- closes the original EOF section from source line 39
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Rolle.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Thom/Basic.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Thom sign conditions from polynomial Rolle

Sign conditions on all formal derivatives are order-convex. Consequently a
nonzero polynomial has no root between two distinct points at which all its
derivatives have the same signs, and the signs of the positive-order derivatives
distinguish roots of a nonzero polynomial, including multiple roots. No
squarefreeness assumption is needed.
The finite Thom encoding records derivatives 1 through `natDegree`. The encoding of an
iterated derivative is a restriction of the encoding of `p`, and strictly monotone ring
embeddings preserve encodings. Negating or scaling `p` negates or scales its derivative signs,
and an affine substitution `X ↦ a X + b` multiplies the sign of the `k`th derivative by
`sign a ^ k` and moves the point to `a x + b`. The last
differing derivative sign and the next common sign determine the order of two points.
The only extra premise on the ordered field is polynomial Rolle, supplied by
`TauCeti.RealClosure.polynomialRolle_of_isRealClosed` over every real closed ordered field.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Propositions 2.27 and 2.28 (Thom's lemma and root encodings).
-/

public section

open TauCeti (PolynomialRolle)

open Polynomial SignType Set

namespace Polynomial

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The sign of the `k`th formal derivative at `x`, including order zero. -/
noncomputable def derivativeSign (p : R[X]) (x : R) (k : ℕ) : SignType :=
  sign ((derivative^[k] p).eval x)

/-- Derivative signs are signs of evaluations of iterated formal derivatives. -/
theorem derivativeSign_def (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = sign ((derivative^[k] p).eval x) := (rfl)

@[grind =]
theorem derivativeSign_eq_one_iff (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = 1 ↔ 0 < (derivative^[k] p).eval x := by
  first
  | rw [derivativeSign_def, sign_eq_one_iff]

@[grind =]
theorem derivativeSign_eq_neg_one_iff (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = -1 ↔ (derivative^[k] p).eval x < 0 := by
  first
  | rw [derivativeSign_def, sign_eq_neg_one_iff]

@[simp, grind =]
theorem derivativeSign_eq_zero_iff (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = 0 ↔ (derivative^[k] p).eval x = 0 := by
  first
  | rw [derivativeSign_def, sign_eq_zero_iff]

theorem derivativeSign_ne_zero (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k ≠ 0 ↔ (derivative^[k] p).eval x ≠ 0 :=
  not_congr (derivativeSign_eq_zero_iff p x k)

@[simp, grind =]
theorem derivativeSign_zero (x : R) (k : ℕ) : derivativeSign (0 : R[X]) x k = 0 := by
  first
  | simp [derivativeSign_def]

@[simp, grind =]
theorem derivativeSign_index_zero (p : R[X]) (x : R) :
    derivativeSign p x 0 = sign (p.eval x) := by
  first
  | simp [derivativeSign_def]

@[simp, grind =]
theorem derivativeSign_eq_zero (p : R[X]) (x : R) {k : ℕ} (hk : p.natDegree < k) :
    derivativeSign p x k = 0 := by
  first
  | simp [derivativeSign_def, iterate_derivative_eq_zero hk]

/-- Agreement of derivative signs from order `n` through a degree bound extends to every order
at least `n`, since higher derivatives vanish. -/
theorem _root_.TauCeti.derivativeSign_eq_of_forall_le {p : R[X]} {a b : R} {n d k : ℕ}
    (hd : p.natDegree ≤ d)
    (h : ∀ j, n ≤ j → j ≤ d → derivativeSign p a j = derivativeSign p b j)
    (hk : n ≤ k) : derivativeSign p a k = derivativeSign p b k := by
  first
  | by_cases hkd : k ≤ d
    · exact h k hk hkd
    · simp [derivativeSign_eq_zero p _ (lt_of_le_of_lt hd (Nat.lt_of_not_ge hkd))]

@[simp, grind =]
theorem derivativeSign_C (a x : R) (k : ℕ) :
    derivativeSign (C a) x k = if k = 0 then sign a else 0 := by
  first
  | cases k with
    | zero => simp [derivativeSign_def]
    | succ k => simp

/-- Taking one derivative advances the derivative-sign index by one. -/
@[simp, grind =]
theorem derivativeSign_derivative (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p.derivative x k = derivativeSign p x (k + 1) := by
  first
  | simp only [derivativeSign_def, Function.iterate_succ_apply]

/-- Prepending `0` to the derivative signs of orders `1, …, d` at a root gives the derivative signs
of orders `0, …, d`. -/
theorem cons_zero_derivativeSign_succ_eq {p : R[X]}
    (d : ℕ) {x : R} (hx : p.eval x = 0) :
    (Fin.cons 0 (fun j : Fin d => derivativeSign p x (j.val + 1)) : Fin (d + 1) → SignType) =
      fun i => derivativeSign p x i.val := by
  first
  | ext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp [hx]

/-- Shifting the polynomial shifts the derivative index. -/
@[simp, grind =]
theorem derivativeSign_iterate_derivative (p : R[X]) (x : R) (i j : ℕ) :
    derivativeSign (derivative^[i] p) x j = derivativeSign p x (j + i) := by
  first
  | simp only [derivativeSign_def, Function.iterate_add_apply]

/-- The usual finite Thom encoding retains derivatives 1 through the degree. -/
noncomputable def thomEncoding (p : R[X]) (x : R) : Fin p.natDegree → SignType :=
  fun i => derivativeSign p x (i.val + 1)

/-- Coordinate `i` records the sign of derivative `i + 1`. -/
@[simp, grind =]
theorem thomEncoding_apply (p : R[X]) (x : R) (i : Fin p.natDegree) :
    thomEncoding p x i = derivativeSign p x (i.val + 1) := (rfl)

/-- A finite Thom word consists of the signs of derivatives 1 through the degree. -/
theorem thomEncoding_def (p : R[X]) (x : R) :
    thomEncoding p x = fun i => sign ((derivative^[i.val + 1] p).eval x) := by
  first
  | funext i
    rw [thomEncoding_apply, derivativeSign_def]

private theorem derivativeSign_tail (p : R[X]) {a b : R} {n : ℕ}
    (h : ∀ i : Fin p.natDegree, n < i.val + 1 → thomEncoding p a i = thomEncoding p b i)
    (k : ℕ) (hk : n < k) : derivativeSign p a k = derivativeSign p b k := by
  first
  | refine TauCeti.derivativeSign_eq_of_forall_le (n := n + 1) le_rfl ?_ hk
    intro j hj hjd
    have hjpos : 1 ≤ j := by omega
    have he := h ⟨j - 1, by omega⟩
      (by simpa only [Fin.val_mk, Nat.sub_add_cancel hjpos] using Nat.lt_of_succ_le hj)
    simpa only [thomEncoding_apply, Nat.sub_add_cancel hjpos] using he

/-- Finite Thom encodings agree exactly when all positive-order derivative signs agree. -/
theorem thomEncoding_eq_iff (p : R[X]) (a b : R) :
    thomEncoding p a = thomEncoding p b ↔
      ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k := by
  first
  | constructor
    · intro h
      exact derivativeSign_tail p (fun i _ => congrFun h i)
    · intro h
      funext i
      simp only [thomEncoding_apply]
      exact h (i.val + 1) (Nat.succ_pos _)

/-- At and above the degree the derivative is constant, so its sign is
independent of the point. -/
theorem derivativeSign_const (p : R[X]) (a b : R) {k : ℕ} (hk : p.natDegree ≤ k) :
    derivativeSign p a k = derivativeSign p b k := by
  first
  | have hd : (derivative^[k] p).natDegree = 0 :=
      Nat.eq_zero_of_le_zero ((natDegree_iterate_derivative p k).trans (by omega))
    simp only [derivativeSign_def]
    rw [eq_C_of_natDegree_eq_zero hd]
    simp

/-- A differing finite Thom coordinate lies below the top derivative,
so a next coordinate exists. -/
theorem thomEncoding_succ_lt_natDegree (p : R[X]) {a b : R} {i : Fin p.natDegree}
    (hne : thomEncoding p a i ≠ thomEncoding p b i) : i.val + 1 < p.natDegree := by
  first
  | by_contra! hi
    simp only [thomEncoding_apply] at hne
    exact hne (derivativeSign_const p a b hi)

/-- **Restriction to a derivative.** Coordinate `i` of the Thom encoding of the `k`th derivative
is coordinate `i + k` of the Thom encoding of `p`. -/
theorem thomEncoding_iterate_derivative_apply (p : R[X]) (x : R) (k : ℕ)
    (i : Fin (derivative^[k] p).natDegree) :
    thomEncoding (derivative^[k] p) x i =
      thomEncoding p x ⟨i.val + k, by have := natDegree_iterate_derivative p k; omega⟩ := by
  first
  | simp only [thomEncoding_apply, derivativeSign_iterate_derivative, Nat.add_right_comm]

/-- Coordinate `i` of the Thom encoding of `p'` is coordinate `i + 1` of that of `p`. -/
theorem thomEncoding_derivative_apply (p : R[X]) (x : R) (i : Fin p.derivative.natDegree) :
    thomEncoding p.derivative x i =
      thomEncoding p x ⟨i.val + 1, by have := natDegree_derivative_le p; omega⟩ := by
  first
  | simp only [thomEncoding_apply, derivativeSign_derivative]

/-- Two points have the same Thom encoding for `p` exactly when the signs of the derivatives of
orders `1, …, k` agree and the Thom encodings for the `k`th derivative agree. -/
theorem thomEncoding_eq_iff_iterate_derivative (p : R[X]) (a b : R) (k : ℕ) :
    thomEncoding p a = thomEncoding p b ↔
      (∀ j, 0 < j → j ≤ k → derivativeSign p a j = derivativeSign p b j) ∧
        thomEncoding (derivative^[k] p) a = thomEncoding (derivative^[k] p) b := by
  first
  | simp only [thomEncoding_eq_iff, derivativeSign_iterate_derivative]
    constructor
    · exact fun h ↦ ⟨fun j hj _ ↦ h j hj, fun j hj ↦ h (j + k) (by omega)⟩
    · rintro ⟨hlow, hhigh⟩ j hj
      by_cases hjk : j ≤ k
      · exact hlow j hj hjk
      · simpa only [Nat.sub_add_cancel (by omega : k ≤ j)] using hhigh (j - k) (by omega)

/-- Two points have the same Thom encoding for `p` exactly when `p'` has the same sign at both
and they have the same Thom encoding for `p'`. -/
theorem thomEncoding_eq_iff_derivative (p : R[X]) (a b : R) :
    thomEncoding p a = thomEncoding p b ↔
      derivativeSign p a 1 = derivativeSign p b 1 ∧
        thomEncoding p.derivative a = thomEncoding p.derivative b := by
  first
  | rw [thomEncoding_eq_iff_iterate_derivative p a b 1, Function.iterate_one]
    refine and_congr_left' ⟨fun h ↦ h 1 one_pos le_rfl, fun h j hj hj1 ↦ ?_⟩
    rwa [le_antisymm hj1 hj]

section Map

variable {S : Type*} [Semiring S] [LinearOrder S]

omit [LinearOrder R] in
/-- Mapping an iterated derivative and taking its sign gives the derivative sign of the mapped
polynomial. -/
theorem _root_.TauCeti.sign_eval_map_iterate_derivative {p : R[X]} {f : R →+* S}
    (x : S) (k : ℕ) :
    sign (((derivative^[k] p).map f).eval x) = derivativeSign (p.map f) x k := by
  first
  | rw [derivativeSign_def, iterate_derivative_map]

/-- Strictly monotone ring embeddings preserve the signs of all derivatives. -/
@[simp]
theorem derivativeSign_map (p : R[X]) (f : R →+* S) (hf : StrictMono f) (x : R) (k : ℕ) :
    derivativeSign (p.map f) (f x) k = derivativeSign p x k := by
  first
  | rw [derivativeSign_def, derivativeSign_def, iterate_derivative_map]
    exact sign_eval_map _ f hf x

/-- Strictly monotone ring embeddings preserve Thom encodings. The two encodings are words of
the same length, since injective maps preserve the degree. -/
theorem thomEncoding_map (p : R[X]) (f : R →+* S) (hf : StrictMono f) (x : R) :
    thomEncoding (p.map f) (f x) =
      thomEncoding p x ∘ Fin.cast (natDegree_map_eq_of_injective hf.injective p) := by
  first
  | funext i
    simp [hf]

end Map

end Basic

section Neg

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]

/-- Negating the polynomial negates every derivative sign. -/
@[simp, grind =]
theorem derivativeSign_neg (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign (-p) x k = -derivativeSign p x k := by
  first
  | rw [derivativeSign_def, derivativeSign_def, iterate_derivative_neg, eval_neg, Left.sign_neg]

/-- Negating the polynomial negates its Thom encoding. -/
theorem thomEncoding_neg (p : R[X]) (x : R) :
    thomEncoding (-p) x = -(thomEncoding p x ∘ Fin.cast (natDegree_neg p)) := by
  first
  | funext i
    simp

end Neg

section Scale

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Scaling the polynomial by `c` multiplies every derivative sign by `sign c`. -/
@[simp, grind =]
theorem derivativeSign_C_mul (c : R) (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign (C c * p) x k = sign c * derivativeSign p x k := by
  first
  | rw [derivativeSign_def, derivativeSign_def, iterate_derivative_C_mul, eval_C_mul, sign_mul]

/-- Scaling the polynomial by a nonzero `c` multiplies its Thom encoding by `sign c`. -/
theorem thomEncoding_C_mul {c : R} (hc : c ≠ 0) (p : R[X]) (x : R) :
    thomEncoding (C c * p) x =
      fun i ↦ sign c * thomEncoding p x (Fin.cast (natDegree_C_mul hc) i) := by
  first
  | funext i
    simp

end Scale

section Affine

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Affine change of variable.** The `k`th derivative sign of `p (a X + b)` at `x` is the `k`th
derivative sign of `p` at `a x + b`, multiplied by `sign a ^ k`. -/
@[simp, grind =]
theorem derivativeSign_comp_C_mul_X_add_C (p : R[X]) (a b x : R) (k : ℕ) :
    derivativeSign (p.comp (C a * X + C b)) x k = sign a ^ k * derivativeSign p (a * x + b) k := by
  first
  | rw [derivativeSign_def, derivativeSign_def, iterate_derivative_comp_C_mul_X_add_C, eval_mul,
      eval_C, eval_comp, sign_mul, sign_pow]
    simp

/-- **Affine change of variable.** Coordinate `i` of the Thom encoding of `p (a X + b)` at `x`,
for `a ≠ 0`, is coordinate `i` of the Thom encoding of `p` at `a x + b`, multiplied by
`sign a ^ (i + 1)`. -/
theorem thomEncoding_comp_C_mul_X_add_C {a : R} (ha : a ≠ 0) (b : R) (p : R[X]) (x : R) :
    thomEncoding (p.comp (C a * X + C b)) x = fun i ↦
      sign a ^ (i.val + 1) *
        thomEncoding p (a * x + b) (Fin.cast (natDegree_comp_C_mul_X_add_C ha b p) i) := by
  first
  | funext i
    simp

end Affine

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

private theorem sign_between_aux (hrolle : PolynomialRolle R) (n : ℕ) (p : R[X])
    (hn : derivative^[n] p = 0) {a b x : R} (hx : x ∈ Icc a b)
    (h : ∀ k, derivativeSign p a k = derivativeSign p b k) :
    sign (p.eval x) = sign (p.eval a) := by
  first
  | have hab := hx.1.trans hx.2
    induction n generalizing p x with
    | zero =>
      have hp : p = 0 := by simpa only [Function.iterate_zero_apply] using hn
      simp [hp]
    | succ n ih =>
      have hd : derivative^[n] p.derivative = 0 := by
        simpa only [Function.iterate_succ_apply] using hn
      have hs : ∀ k, derivativeSign p.derivative a k = derivativeSign p.derivative b k := by
        intro k
        simpa only [derivativeSign_derivative] using h (k + 1)
      have hd_sign (y : R) (hy : y ∈ Icc a b) :
          sign (p.derivative.eval y) = sign (p.derivative.eval a) := ih p.derivative hd hy hs
      have h0 : sign (p.eval a) = sign (p.eval b) := by
        simpa only [derivativeSign_index_zero] using h 0
      rcases le_total 0 (p.derivative.eval a) with hp | hp
      · have hm : MonotoneOn p.eval (Icc a b) :=
          hrolle.monotoneOn p (by
              intro y hy
              rw [← sign_nonneg_iff, hd_sign y ⟨hy.1.le, hy.2.le⟩]
              exact sign_nonneg_iff.mpr hp)
        exact le_antisymm ((sign.monotone (hm hx ⟨hab, le_rfl⟩ hx.2)).trans_eq h0.symm)
          (sign.monotone (hm ⟨le_rfl, hab⟩ hx hx.1))
      · have hm : AntitoneOn p.eval (Icc a b) :=
          hrolle.antitoneOn p (by
              intro y hy
              rw [← sign_nonpos_iff, hd_sign y ⟨hy.1.le, hy.2.le⟩]
              exact sign_nonpos_iff.mpr hp)
        exact le_antisymm (sign.monotone (hm ⟨le_rfl, hab⟩ hx hx.1))
          (h0.trans_le (sign.monotone (hm hx ⟨hab, le_rfl⟩ hx.2)))

/-- Equal derivative sign vectors at the endpoints force the sign of the polynomial
itself to be constant on the interval. -/
private theorem sign_between (p : R[X]) (hrolle : PolynomialRolle R) {a b x : R} (hx : x ∈ Icc a b)
    (h : ∀ k, derivativeSign p a k = derivativeSign p b k) :
    sign (p.eval x) = sign (p.eval a) :=
  sign_between_aux hrolle (p.natDegree + 1) p (iterate_derivative_eq_zero (by omega))
    hx h

/-- Agreement of all derivative signs from index `k` onward forces the sign at
index `k` to be constant between the endpoints. -/
theorem derivativeSign_eq_on_Icc (p : R[X]) (hrolle : PolynomialRolle R) {a b x : R}
    (hx : x ∈ Icc a b) {k : ℕ}
    (h : ∀ j, k ≤ j → derivativeSign p a j = derivativeSign p b j) :
    derivativeSign p x k = derivativeSign p a k := by
  first
  | apply sign_between (derivative^[k] p) hrolle hx
    intro j
    simp only [derivativeSign_iterate_derivative]
    exact h (j + k) (Nat.le_add_left _ _)

/-- A full derivative sign condition is order-convex. Empty conditions are
allowed; this statement does not assert that an arbitrary word is realizable. -/
theorem ordConnected_preimage_derivativeSign (p : R[X]) (hrolle : PolynomialRolle R)
    (σ : ℕ → SignType) :
    OrdConnected (derivativeSign p ⁻¹' {σ}) := by
  first
  | constructor
    intro a ha b hb x hx
    funext k
    exact (derivativeSign_eq_on_Icc p hrolle hx
      (fun j _ => congrFun (ha.trans hb.symm) j)).trans (congrFun ha k)

/-- A finite Thom sign condition is order-convex, including unrealized conditions. -/
theorem ordConnected_preimage_thomEncoding (p : R[X]) (hrolle : PolynomialRolle R)
    (τ : Fin p.natDegree → SignType) : OrdConnected (thomEncoding p ⁻¹' {τ}) := by
  first
  | constructor
    intro a ha b hb x hx
    apply Eq.trans ?_ ha
    apply (thomEncoding_eq_iff p x a).mpr
    intro k hk
    exact derivativeSign_eq_on_Icc p hrolle hx
      (fun j hj => (thomEncoding_eq_iff p a b).mp (ha.trans hb.symm) j (hk.trans_le hj))

/-- A nonzero polynomial whose derivatives of every order, including order zero, have the same
signs at two distinct points has no root between them. -/
theorem eval_ne_zero_of_derivativeSign_eq (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0)
    {a b x : R} (hab : a ≠ b) (h : ∀ k, derivativeSign p a k = derivativeSign p b k)
    (hx : x ∈ uIcc a b) : p.eval x ≠ 0 := by
  first
  | wlog hlt : a < b generalizing a b
    · exact this hab.symm (fun k ↦ (h k).symm) (uIcc_comm a b ▸ hx)
        (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
    rw [uIcc_of_le hlt.le] at hx
    have hsign {y : R} (hy : y ∈ Icc a b) : sign (p.eval y) = sign (p.eval a) := by
      simpa using derivativeSign_eq_on_Icc p hrolle hy (k := 0) fun j _ ↦ h j
    intro hx0
    apply hp
    refine p.eq_zero_of_infinite_isRoot ((Icc_infinite hlt).mono fun y hy ↦ ?_)
    have hy := (hsign hy).trans (hsign hx).symm
    rwa [hx0, sign_zero, sign_eq_zero_iff] at hy

/-- If all derivative signs of `p` agree at two distinct points, then every nonzero derivative
of `p` has a nonzero sign there. -/
theorem derivativeSign_ne_zero_of_derivativeSign_eq (p : R[X]) (hrolle : PolynomialRolle R)
    {a b : R} (hab : a ≠ b) (h : derivativeSign p a = derivativeSign p b) {k : ℕ}
    (hk : derivative^[k] p ≠ 0) : derivativeSign p a k ≠ 0 := by
  first
  | rw [derivativeSign_ne_zero]
    refine eval_ne_zero_of_derivativeSign_eq _ hrolle hk hab (fun j ↦ ?_) left_mem_uIcc
    simp only [derivativeSign_iterate_derivative, h]

/-- Roots with equal signs of every positive-order derivative are equal.
The polynomial need not be squarefree. -/
theorem eq_of_derivativeSign_eq (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hs : ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k) : a = b := by
  first
  | have h (k : ℕ) : derivativeSign p a k = derivativeSign p b k := by
      cases k with
      | zero => simp [derivativeSign_def, ha, hb]
      | succ k => exact hs _ (Nat.succ_pos _)
    by_contra hab
    exact eval_ne_zero_of_derivativeSign_eq p hrolle hp hab h left_mem_uIcc ha

/-- A finite Thom encoding uniquely identifies a root of a nonzero polynomial. -/
theorem thomEncoding_injOn (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) :
    Set.InjOn (thomEncoding p) {x | p.eval x = 0} := by
  first
  | intro a ha b hb h
    apply eq_of_derivativeSign_eq p hrolle hp ha hb
    exact (thomEncoding_eq_iff p a b).mp h

/-- Roots of a nonzero polynomial with the same derivative signs of orders `1, …, d`
(where `p.natDegree ≤ d`) are equal. -/
theorem eq_of_derivativeSign_succ_eq_of_natDegree_le {p : R[X]} {d : ℕ} (hd : p.natDegree ≤ d)
    (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R} (ha : p.eval a = 0) (hb : p.eval b = 0)
    (h : (fun j : Fin d => derivativeSign p a (j.val + 1)) =
      fun j => derivativeSign p b (j.val + 1)) : a = b := by
  first
  | refine eq_of_derivativeSign_eq p hrolle hp ha hb fun k hk =>
      TauCeti.derivativeSign_eq_of_forall_le hd (fun j hj hjd => ?_) hk
    simpa only [Nat.sub_add_cancel hj] using congrFun h ⟨j - 1, by omega⟩

private theorem sign_order_aux (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} (hab : a < b)
    (hne : sign (p.eval a) ≠ sign (p.eval b))
    (htail : ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k) :
    (sign (p.derivative.eval a) = 1 ∧ sign (p.eval a) < sign (p.eval b)) ∨
    (sign (p.derivative.eval a) = -1 ∧ sign (p.eval b) < sign (p.eval a)) := by
  first
  | have hd (x : R) (hx : x ∈ Icc a b) :
        sign (p.derivative.eval x) = sign (p.derivative.eval a) := by
      simpa only [derivativeSign_def, Function.iterate_one] using
        derivativeSign_eq_on_Icc p hrolle hx (k := 1) (fun j hj => htail j hj)
    rcases lt_trichotomy (p.derivative.eval a) 0 with hn | hz | hp
    · have hm : StrictAntiOn p.eval (Icc a b) :=
        hrolle.strictAntiOn p (by
          intro x hx
          rw [← sign_eq_neg_one_iff, hd x ⟨hx.1.le, hx.2.le⟩]
          exact sign_neg hn)
      exact Or.inr ⟨sign_neg hn,
        lt_of_le_of_ne (sign.monotone (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).le) hne.symm⟩
    · have hp0 : p.derivative = 0 := by
        apply p.derivative.eq_zero_of_infinite_isRoot
        apply (Ioo_infinite hab).mono
        intro x hx
        apply sign_eq_zero_iff.mp
        simpa only [hz, sign_zero] using hd x ⟨hx.1.le, hx.2.le⟩
      have hc := eq_C_of_derivative_eq_zero hp0
      exact (hne (by rw [hc]; simp)).elim
    · have hm : StrictMonoOn p.eval (Icc a b) :=
        hrolle.strictMonoOn p (by
          intro x hx
          rw [← sign_eq_one_iff, hd x ⟨hx.1.le, hx.2.le⟩]
          exact sign_pos hp)
      exact Or.inl ⟨sign_pos hp,
        lt_of_le_of_ne (sign.monotone (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).le) hne⟩

/-- At the largest derivative index where signs differ, the next common sign
and the two differing signs determine the order of the points. -/
theorem lt_iff_derivativeSign (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} {k : ℕ}
    (hne : derivativeSign p a k ≠ derivativeSign p b k)
    (htail : ∀ j, k < j → derivativeSign p a j = derivativeSign p b j) :
    (a < b ↔
      (derivativeSign p a (k + 1) = 1 ∧ derivativeSign p a k < derivativeSign p b k) ∨
      (derivativeSign p a (k + 1) = -1 ∧ derivativeSign p b k < derivativeSign p a k)) := by
  first
  | have forward {u v : R} (huv : u < v)
        (hne : derivativeSign p u k ≠ derivativeSign p v k)
        (ht : ∀ j, k < j → derivativeSign p u j = derivativeSign p v j) :
        (derivativeSign p u (k + 1) = 1 ∧ derivativeSign p u k < derivativeSign p v k) ∨
        (derivativeSign p u (k + 1) = -1 ∧ derivativeSign p v k < derivativeSign p u k) := by
      simp only [derivativeSign_def] at hne
      have h := sign_order_aux (derivative^[k] p) hrolle huv hne (by
        intro j hj
        rw [derivativeSign_iterate_derivative, derivativeSign_iterate_derivative]
        exact ht _ (by omega))
      simpa only [derivativeSign_def, Function.iterate_succ_apply'] using h
    constructor
    · exact fun hab => forward hab hne htail
    · intro h
      rcases lt_trichotomy a b with hab | hab | hba
      · exact hab
      · subst b; exact (hne rfl).elim
      · have hrev := forward hba hne.symm (fun j hj => (htail j hj).symm)
        have heq := htail (k + 1) (by omega)
        rcases h with ⟨hpos, hlt⟩ | ⟨hneg, hlt⟩ <;>
          rcases hrev with ⟨hpos', hlt'⟩ | ⟨hneg', hlt'⟩
        · exact (lt_asymm hlt hlt').elim
        · rw [← heq, hpos] at hneg'; cases hneg'
        · rw [← heq, hneg] at hpos'; cases hpos'
        · exact (lt_asymm hlt hlt').elim

/-- The comparison rule directly on finite Thom words. `thomEncoding_succ_lt_natDegree` supplies
existence of the next coordinate from the differing signs. Every coordinate
above the disagreement must agree. -/
theorem lt_iff_thomEncoding (p : R[X]) (hrolle : PolynomialRolle R) {a b : R}
    (i : Fin p.natDegree)
    (hne : thomEncoding p a i ≠ thomEncoding p b i)
    (htail : ∀ j : Fin p.natDegree, i < j → thomEncoding p a j = thomEncoding p b j) :
    (a < b ↔
      (thomEncoding p a ⟨i.val + 1, thomEncoding_succ_lt_natDegree p hne⟩ = 1 ∧
        thomEncoding p a i < thomEncoding p b i) ∨
      (thomEncoding p a ⟨i.val + 1, thomEncoding_succ_lt_natDegree p hne⟩ = -1 ∧
        thomEncoding p b i < thomEncoding p a i)) := by
  first
  | simp only [thomEncoding_apply] at hne ⊢
    apply lt_iff_derivativeSign p hrolle hne
    exact derivativeSign_tail p (fun j hj => htail j (Nat.lt_of_succ_lt_succ hj))

/-- The common sign immediately above the last disagreement cannot be zero. -/
theorem derivativeSign_succ_ne_zero (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} {k : ℕ}
    (hne : derivativeSign p a k ≠ derivativeSign p b k)
    (htail : ∀ j, k < j → derivativeSign p a j = derivativeSign p b j) :
    derivativeSign p a (k + 1) ≠ 0 := by
  first
  | have hab : a ≠ b := fun h => hne (congrArg (fun x => derivativeSign p x k) h)
    rcases hab.lt_or_gt with hlt | hlt
    · rcases (lt_iff_derivativeSign p hrolle hne htail).mp hlt with h | h <;>
        simp only [h.1, ne_eq, reduceCtorEq, not_false_eq_true]
    · have ht := fun j hj => (htail j hj).symm
      rw [htail (k + 1) (by omega)]
      rcases (lt_iff_derivativeSign p hrolle hne.symm ht).mp hlt with h | h <;>
        simp only [h.1, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The common finite Thom coordinate immediately above the last disagreement is nonzero. -/
theorem thomEncoding_succ_ne_zero (p : R[X]) (hrolle : PolynomialRolle R) {a b : R}
    (i : Fin p.natDegree)
    (hne : thomEncoding p a i ≠ thomEncoding p b i)
    (htail : ∀ j : Fin p.natDegree, i < j → thomEncoding p a j = thomEncoding p b j) :
    thomEncoding p a ⟨i.val + 1, thomEncoding_succ_lt_natDegree p hne⟩ ≠ 0 := by
  first
  | simp only [thomEncoding_apply] at hne ⊢
    exact derivativeSign_succ_ne_zero p hrolle hne
      (derivativeSign_tail p (fun j hj => htail j (Nat.lt_of_succ_lt_succ hj)))

/-- A root and a distinct point have different derivative signs through any degree bound. -/
theorem derivativeSign_ne_of_eval_eq_zero {p : R[X]} {d : ℕ} (hd : p.natDegree ≤ d)
    (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R} (hab : a ≠ b)
    (hb : p.eval b = 0) :
    (fun i : Fin (d + 1) => derivativeSign p a i.val) ≠
      fun i => derivativeSign p b i.val := by
  first
  | intro h
    exact eval_ne_zero_of_derivativeSign_eq p hrolle hp hab
      (fun _ => TauCeti.derivativeSign_eq_of_forall_le hd
        (fun j _ hj => congrFun h ⟨j, by omega⟩) (Nat.zero_le _)) right_mem_uIcc hb

end Polynomial
end -- closes the original EOF section from source line 42
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Thom/Basic.lean -/

/- BEGIN SOURCE: TauCeti/FieldTheory/RealClosure/FiniteExtension.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Finite extensions of an abstract real closed field

Odd-degree finite extensions of a real closed field are trivial. A field of
characteristic different from two in which every element is a square has no quadratic
extension. These are the degree reductions used by the Sylow argument in `Galois.lean`.

## References

The odd-degree and quadratic-extension steps of the Artin–Schreier argument; see
Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Theorem 2.2.
-/

public section

namespace TauCeti.RealClosure

open _root_.Polynomial Module

variable {R E : Type*} [Field R] [IsRealClosed R] [Field E] [Algebra R E]
    [FiniteDimensional R E]

/-- An odd-degree finite extension of a real closed field is trivial. -/
theorem finrank_eq_one_of_odd (h : Odd (finrank R E)) : finrank R E = 1 := by
  first
  | obtain ⟨x, hx⟩ := Field.exists_primitive_element R E
    have hdeg := (Field.primitive_element_iff_minpoly_natDegree_eq R x).mp hx
    obtain ⟨a, ha⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (hdeg ▸ h)
    rw [← hdeg]
    exact natDegree_eq_of_degree_eq_some
      (degree_eq_one_of_irreducible_of_root (minpoly.irreducible (IsIntegral.of_finite R x)) ha)

section Quadratic

variable {K L : Type*} [Field K] [NeZero (2 : K)]

/-- A square-closed field of characteristic different from two has no quadratic extension. -/
theorem finrank_ne_two_of_forall_isSquare [Field L] [Algebra K L]
    (hsq : ∀ x : K, IsSquare x) : finrank K L ≠ 2 := by
  first
  | intro htwo
    have : Algebra.IsQuadraticExtension K L := ⟨htwo⟩
    obtain ⟨a, b, ⟨e⟩⟩ :=
      Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := K) (A := L)
    exact QuadraticAlgebra.not_isField_of_isSquare_discr (hsq _)
      (e.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField L))

end Quadratic

end TauCeti.RealClosure
end -- closes the original EOF section from source line 30
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/FieldTheory/RealClosure/FiniteExtension.lean -/

/- BEGIN SOURCE: TauCeti/FieldTheory/RealClosure/Galois.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # The Galois-theoretic reduction for real closed fields

A finite Galois extension of a real closed field has a 2-group of automorphisms.
Over a square-closed intermediate extension it is trivial. These degree reductions
are used to prove algebraic closedness in `AlgebraicClosed.lean`.

## References

The Sylow 2-subgroup and index-two subgroup steps of the Artin–Schreier argument; see
Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Theorem 2.2.
-/

public section

namespace TauCeti.RealClosure

open Module IntermediateField

variable {R E : Type*} [Field R] [IsRealClosed R] [Field E] [Algebra R E]
    [FiniteDimensional R E] [IsGalois R E]

/-- A finite Galois extension of a real closed field has a 2-group as Galois group. -/
theorem isPGroup_two_algEquiv : IsPGroup 2 (E ≃ₐ[R] E) := by
  first
  | let P : Sylow 2 (E ≃ₐ[R] E) := Classical.choice inferInstance
    have hindex : finrank R (fixedField (P : Subgroup (E ≃ₐ[R] E))) = P.index := by
      rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
    have hodd : Odd (finrank R (fixedField (P : Subgroup (E ≃ₐ[R] E)))) := by
      rw [hindex]
      exact Nat.odd_iff.mpr (by have := P.not_dvd_index; omega)
    have htop : (P : Subgroup (E ≃ₐ[R] E)) = ⊤ := by
      apply Subgroup.index_eq_one.mp
      rw [← hindex]
      exact finrank_eq_one_of_odd hodd
    have hP := P.isPGroup
    rw [htop] at hP
    exact hP.of_equiv Subgroup.topEquiv

/-- A square-closed field of characteristic different from two has no nontrivial finite
Galois extension whose Galois group is a 2-group. -/
theorem finrank_eq_one_of_isPGroup {K L : Type*} [Field K] [NeZero (2 : K)]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hsq : ∀ x : K, IsSquare x) (hG : IsPGroup 2 (L ≃ₐ[K] L)) :
    finrank K L = 1 := by
  first
  | have := hG.isNilpotent
    rcases hG.card_eq_or_dvd with hcard | hdvd
    · rwa [IsGalois.card_aut_eq_finrank] at hcard
    · obtain ⟨H, hH, _⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
      have hdim : finrank K (fixedField H) = 2 := by
        rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField, hH]
      exact (finrank_ne_two_of_forall_isSquare hsq hdim).elim

/-- Over a square-closed intermediate extension of a real closed field, every
finite Galois extension of the base becomes trivial. -/
theorem finrank_eq_one_of_isGalois_of_forall_isSquare {C : Type*} [Field C] [Algebra R C]
    [Algebra C E] [IsScalarTower R C E] (hsq : ∀ x : C, IsSquare x) :
    finrank C E = 1 := by
  first
  | have : CharZero C := charZero_of_injective_algebraMap (algebraMap R C).injective
    have : FiniteDimensional C E := FiniteDimensional.right R C E
    have : IsGalois C E := IsGalois.tower_top_of_isGalois R C E
    exact finrank_eq_one_of_isPGroup hsq
      ((isPGroup_two_algEquiv (R := R) (E := E)).of_injective
        (AlgEquiv.restrictScalarsHom R) (AlgEquiv.restrictScalarsHom_injective R))

end TauCeti.RealClosure
end -- closes the original EOF section from source line 26
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/FieldTheory/RealClosure/Galois.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Order/Ring/Square.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Nonnegative square roots of square elements

A square in a linearly ordered ring has a nonnegative square root, by taking the absolute
value of any square root. Only compatibility of the order with addition is needed.
-/

public section

/-- A square in a linearly ordered ring has a nonnegative square root. -/
theorem IsSquare.exists_nonneg_sq {R : Type*} [Ring R] [LinearOrder R]
    [IsOrderedAddMonoid R] {a : R} (ha : IsSquare a) : ∃ r : R, 0 ≤ r ∧ r ^ 2 = a := by
  first
  | obtain ⟨r, hr⟩ := ha.exists_sq
    exact ⟨|r|, abs_nonneg r, by simpa using hr.symm⟩
end -- closes the original EOF section from source line 16
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Order/Ring/Square.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/QuadraticAlgebra/Square.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Square roots in quadratic complexifications

Every element of `QuadraticAlgebra R (-1) 0` is a square when `R` is an ordered field whose
nonnegative elements are squares. The algebraic formula uses two nonnegative square roots
in `R`, without completeness or an Archimedean assumption.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Every element of `R[i]` is a square if every nonnegative element of `R` is a square. -/
theorem isSquare_of_forall_nonneg_isSquare (z : QuadraticAlgebra R (-1) 0)
    (hsq : ∀ {a : R}, 0 ≤ a → IsSquare a) : IsSquare z := by
  first
  | by_cases him : z.im = 0
    · rcases le_total 0 z.re with hre | hre
      · obtain ⟨r, hr⟩ := hsq hre
        refine ⟨⟨r, 0⟩, ?_⟩
        ext <;> simp [him, hr]
      · obtain ⟨r, hr⟩ := hsq (neg_nonneg.mpr hre)
        refine ⟨⟨0, r⟩, ?_⟩
        apply QuadraticAlgebra.ext
        · simp only [QuadraticAlgebra.re_mul]
          linear_combination -hr
        · simp [him]
    · obtain ⟨m, hm0, hm⟩ :=
        (hsq (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))).exists_nonneg_sq
      have hpos : 0 < (m + z.re) / 2 := by
        have : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
        have : -z.re < m := by nlinarith
        exact div_pos (by linarith) (by norm_num)
      obtain ⟨s, _, hs⟩ := (hsq hpos.le).exists_nonneg_sq
      have hsne : s ≠ 0 := fun h => hpos.ne' (by rw [← hs, h]; ring)
      have hs2 : 2 * s ^ 2 = m + z.re := by linarith
      let t := z.im / (2 * s)
      have ht : 2 * s * t = z.im := by
        dsimp only [t]
        field_simp
      -- Multiplying by `(2 * s) ^ 2` clears the denominator of `t`; then `hm` and `hs2`
      -- identify the real part of the square.
      have hprod : (2 * s) ^ 2 * (s ^ 2 - t ^ 2 - z.re) = 0 := by
        linear_combination (2 * s ^ 2 + m - z.re) * hs2 + hm - (2 * s * t + z.im) * ht
      have hre : s ^ 2 - t ^ 2 = z.re := sub_eq_zero.mp
        ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ (mul_ne_zero two_ne_zero hsne)))
      refine ⟨⟨s, t⟩, ?_⟩
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul]
        linear_combination -hre
      · simp only [QuadraticAlgebra.im_mul]
        linear_combination -ht

end QuadraticAlgebra
end -- closes the original EOF section from source line 23
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/QuadraticAlgebra/Square.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Ring/Semireal.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Square obstructions in semireal rings

Semireality excludes `-1` from the squares. The `Fact` instance supplies this obstruction
when constructing a field by adjoining a square root of `-1`.
-/

public section

namespace TauCeti

/-- In a semireal additive group with multiplication and a distinguished `1`, `-1` is not a square.
This supplies the square obstruction used by quadratic-algebra field instances. -/
instance {R : Type*} [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    Fact (¬ IsSquare (-1 : R)) :=
  ⟨fun h => IsSemireal.not_isSumSq_neg_one R h.isSumSq⟩

end TauCeti
end -- closes the original EOF section from source line 16
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Ring/Semireal.lean -/

/- BEGIN SOURCE: TauCeti/FieldTheory/RealClosure/Sqrt.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Nonnegative square roots in real closed fields

Every nonnegative element of an ordered real closed field has a unique nonnegative square root.
`nonnegSqrt` chooses this root, and on `ℝ` it agrees with `Real.sqrt`.

## Main results

* `nonnegSqrt` chooses the root using real closedness; `nonnegSqrt_nonneg`
  and `sq_nonnegSqrt` characterize it.
* `nonnegSqrt_real_eq_sqrt` identifies the chosen root on `ℝ` with `Real.sqrt`.
-/

public section

namespace TauCeti.RealClosure

section

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The nonnegative square root of a nonnegative element in a real closed field. -/
noncomputable def nonnegSqrt [IsRealClosed R] {a : R} (ha : 0 ≤ a) : R :=
  Classical.choose ((IsSquare.of_nonneg ha).exists_nonneg_sq)

/-- The selected square root is nonnegative. -/
@[simp]
theorem nonnegSqrt_nonneg
    [IsRealClosed R] {a : R} (ha : 0 ≤ a) :
    0 ≤ nonnegSqrt ha :=
  (Classical.choose_spec ((IsSquare.of_nonneg ha).exists_nonneg_sq)).1

/-- The selected square root squares to its input. -/
@[simp]
theorem sq_nonnegSqrt
    [IsRealClosed R] {a : R} (ha : 0 ≤ a) :
    (nonnegSqrt ha) ^ 2 = a :=
  (Classical.choose_spec ((IsSquare.of_nonneg ha).exists_nonneg_sq)).2

/-- The chosen nonnegative square root on `ℝ` agrees with `Real.sqrt`. -/
theorem nonnegSqrt_real_eq_sqrt
    {a : ℝ} (ha : 0 ≤ a) : nonnegSqrt ha = Real.sqrt a := by
  first
  | apply (sq_eq_sq₀ (nonnegSqrt_nonneg ha) (Real.sqrt_nonneg a)).mp
    rw [sq_nonnegSqrt, Real.sq_sqrt ha]

end

end TauCeti.RealClosure
end -- closes the original EOF section from source line 25
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/FieldTheory/RealClosure/Sqrt.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Order/Ring/Ordering/Extension.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Extending field preorderings to orderings

A proper preordering on a field extends to a total ordering. The proof adjoins
one element to a preordering and then applies Zorn's lemma. In particular, it
preserves the prescribed positive elements, as required when ordering a field
extension of an already ordered field.

## References

This is the classical preordering extension argument; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 3](https://www.math.uni-konstanz.de/algebra/WS0910/Notes03.pdf),
Lemma 2.1 and Corollaries 3.2 and 3.4. The Lean construction uses Mathlib's
`RingPreordering` and `RingCone` interfaces.
-/

public section

variable {K : Type*} [Field K]

namespace RingPreordering

/-- Adjoin an element whose negative is absent from a field preordering. -/
def adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) : RingPreordering K :=
  RingPreordering.mk' {x | ∃ u ∈ P, ∃ v ∈ P, x = u + a * v}
    (by
      rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
      exact ⟨u + w, add_mem hu hw, v + z, add_mem hv hz, by ring⟩)
    (by
      rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
      exact ⟨u * w + a ^ 2 * (v * z),
        add_mem (mul_mem hu hw) (mul_mem (P.pow_two_mem a) (mul_mem hv hz)),
        u * z + v * w, add_mem (mul_mem hu hz) (mul_mem hv hw), by ring⟩)
    (fun x => ⟨x * x, P.mul_self_mem x, 0, zero_mem P, by simp⟩)
    (by
      rintro ⟨u, hu, v, hv, heq⟩
      by_cases hv0 : v = 0
      · apply P.neg_one_notMem
        have heq' : -1 = u := by simpa only [hv0, mul_zero, add_zero] using heq
        exact heq' ▸ hu
      · apply ha
        have hmem : (1 + u) * v⁻¹ ∈ P :=
          mul_mem (add_mem (one_mem P) hu) (RingPreordering.inv_mem hv)
        have hval : -a = (1 + u) * v⁻¹ := by
          first
          | field_simp
            linear_combination heq
        rwa [← hval] at hmem)

@[simp] theorem mem_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) {x : K} :
    x ∈ adjoin P a ha ↔ ∃ u ∈ P, ∃ v ∈ P, x = u + a * v := (Iff.rfl)

theorem le_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) :
    P ≤ adjoin P a ha :=
  fun x hx => ⟨x, hx, 0, zero_mem P, by simp⟩

theorem self_mem_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) :
    a ∈ adjoin P a ha :=
  ⟨0, zero_mem P, 1, one_mem P, by simp⟩

/-- The generated preordering is contained in every preordering containing its generators. -/
theorem adjoin_le {P Q : RingPreordering K} {a : K} {ha : -a ∉ P}
    (hPQ : P ≤ Q) (haQ : a ∈ Q) : adjoin P a ha ≤ Q := by
  first
  | rintro x ⟨u, hu, v, hv, rfl⟩
    exact add_mem (hPQ hu) (mul_mem haQ (hPQ hv))

@[simp] theorem adjoin_le_iff {P Q : RingPreordering K} {a : K} {ha : -a ∉ P} :
    adjoin P a ha ≤ Q ↔ P ≤ Q ∧ a ∈ Q :=
  ⟨fun h => ⟨(le_adjoin P a ha).trans h, h (self_mem_adjoin P a ha)⟩,
    fun h => adjoin_le h.1 h.2⟩

/-- The union of a nonempty chain of preorderings is a preordering. -/
private def chainUnion (c : Set (RingPreordering K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : RingPreordering K := by
  first
  | have := hne.to_subtype
    have hd : Directed (· ≤ ·) (fun P : c => P.val.toSubsemiring) :=
      hc.directed.mono_comp _ RingPreordering.toSubsemiring_mono
    exact
      { (⨆ P : c, P.val.toSubsemiring).copy {x | ∃ P ∈ c, x ∈ P} (by
          rw [Subsemiring.coe_iSup_of_directed hd]
          ext x
          simp) with
        mem_of_isSquare' := by
          rintro x ⟨y, rfl⟩
          obtain ⟨P, hP⟩ := hne
          exact ⟨P, hP, P.mul_self_mem y⟩
        neg_one_notMem' := by
          rintro ⟨P, _, hP⟩
          exact P.neg_one_notMem hP }

private theorem le_chainUnion (c : Set (RingPreordering K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {P : RingPreordering K} (hP : P ∈ c) :
    P ≤ chainUnion c hc hne :=
  fun _ hx => ⟨P, hP, hx⟩

/-- A field preordering extends to an ordering, retaining every prescribed sign. -/
theorem exists_le_isOrdering (P : RingPreordering K) :
    ∃ Q : RingPreordering K, P ≤ Q ∧ Q.IsOrdering := by
  first
  | obtain ⟨Q, hPQ, hQ⟩ := zorn_le_nonempty_Ici₀ P
      (fun c _ hc y hy =>
        ⟨chainUnion c hc ⟨y, hy⟩, fun z hz => le_chainUnion c hc ⟨y, hy⟩ hz⟩) P le_rfl
    have htotal : HasMemOrNegMem Q := ⟨by
      intro a
      by_cases ha : -a ∈ Q
      · exact Or.inr ha
      · exact Or.inl ((hQ (le_adjoin Q a ha)) (self_mem_adjoin Q a ha))⟩
    exact ⟨Q, hPQ, { htotal with toIsPrime := inferInstance }⟩

/-- An element whose negative is absent can be made nonnegative in an extending ordering. -/
theorem exists_le_isOrdering_mem (P : RingPreordering K) {a : K} (ha : -a ∉ P) :
    ∃ Q : RingPreordering K, P ≤ Q ∧ Q.IsOrdering ∧ a ∈ Q := by
  first
  | obtain ⟨Q, hQ, horder⟩ := exists_le_isOrdering (adjoin P a ha)
    exact ⟨Q, (le_adjoin P a ha).trans hQ, horder, hQ (self_mem_adjoin P a ha)⟩

/-- A preordering on a field is a pointed ring cone. -/
def toRingCone (P : RingPreordering K) : RingCone K where
  __ := P.toSubsemiring
  eq_zero_of_mem_of_neg_mem' := P.eq_zero_of_mem_of_neg_mem

@[simp] theorem mem_toRingCone (P : RingPreordering K) {x : K} :
    x ∈ toRingCone P ↔ x ∈ P := (Iff.rfl)

instance (P : RingPreordering K) [P.IsOrdering] : HasMemOrNegMem (toRingCone P) where
  mem_or_neg_mem := mem_or_neg_mem P

/-- The linear order associated to a field ordering. -/
@[instance_reducible] noncomputable def linearOrder (P : RingPreordering K)
    [P.IsOrdering] : LinearOrder K := by
  first
  | classical
    exact .mkOfAddGroupCone (toRingCone P)

theorem isStrictOrderedRing (P : RingPreordering K) [P.IsOrdering] :
    letI := linearOrder P
    IsStrictOrderedRing K := by
  first
  | let := linearOrder P
    have : IsOrderedRing K := .mkOfCone (toRingCone P)
    infer_instance

theorem nonneg_iff (P : RingPreordering K) [P.IsOrdering] (x : K) :
    letI := linearOrder P
    0 ≤ x ↔ x ∈ P := by
  first
  | rw [PartialOrder.mkOfAddGroupCone_le_iff, sub_zero]
    exact mem_toRingCone P

/-- Order a field while respecting all signs in a specified preordering. -/
theorem exists_linearOrder (P : RingPreordering K) :
    ∃ o : LinearOrder K, letI := o
      IsStrictOrderedRing K ∧ ∀ x ∈ P, 0 ≤ x := by
  first
  | obtain ⟨Q, hPQ, hQ⟩ := exists_le_isOrdering P
    let := hQ
    exact ⟨linearOrder Q, isStrictOrderedRing Q, fun x hx => (nonneg_iff Q x).mpr (hPQ hx)⟩

end RingPreordering
end -- closes the original EOF section from source line 30
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Order/Ring/Ordering/Extension.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Order/Ring/Ordering/Semireal.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Ordering formally real fields

The sums of squares in a formally real field form a preordering, which extends to an ordering.
This supplies an order when deriving polynomial intermediate value from `IsRealClosed`.

## References

Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 3](https://www.math.uni-konstanz.de/algebra/WS0910/Notes03.pdf),
Corollary 3.4.
-/

public section

namespace RingPreordering

variable {K : Type*} [CommRing K]

/-- The sums of squares form a proper preordering in a formally real commutative ring. -/
def sumSq [IsSemireal K] : RingPreordering K where
  __ := Subsemiring.sumSq K
  mem_of_isSquare' hx := by simpa using hx.isSumSq
  neg_one_notMem' := by simpa using IsSemireal.not_isSumSq_neg_one K

@[simp] theorem mem_sumSq [IsSemireal K] (x : K) :
    x ∈ sumSq (K := K) ↔ IsSumSq x := Subsemiring.mem_sumSq

end RingPreordering

/-- A formally real field admits a compatible linear order. -/
theorem IsSemireal.exists_linearOrder {K : Type*} [Field K] [IsSemireal K] :
    ∃ o : LinearOrder K, letI := o
      IsStrictOrderedRing K := by
  first
  | obtain ⟨o, ho, _⟩ := RingPreordering.exists_linearOrder (RingPreordering.sumSq (K := K))
    exact ⟨o, ho⟩
end -- closes the original EOF section from source line 23
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Order/Ring/Ordering/Semireal.lean -/

/- BEGIN SOURCE: TauCeti/FieldTheory/RealClosure/Complexification.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Square roots in the complexification of a real closed field

`QuadraticAlgebra.isSquare` specializes the algebraic square-root construction to a real
closed field, without requiring an order on that field as a hypothesis. This square-closure
property is used to prove algebraic closedness of the complexification.

## Main results

* `QuadraticAlgebra.sqrt` constructs a square root in `R[i]` over an ordered real closed field,
  deriving the scalar root existence it needs. `sq_sqrt`, `sqrt_coordinates`, `sqrt_unique`, and
  the sign lemmas characterize this root.
* `QuadraticAlgebra.isSquare` shows every element of `R[i]` is a square when `R` is real closed,
  without choosing an order.
* `QuadraticAlgebra.equivComplex` identifies `ℝ[i]` with `ℂ`, and
  `equivComplex_sqrt` identifies the constructed root with `Complex.sqrt`.

The semireal square obstruction supplies the field instance on
`QuadraticAlgebra R (-1) 0`.
-/

public section

namespace QuadraticAlgebra

open TauCeti.RealClosure

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [IsRealClosed R]

private noncomputable def complex_sqrt_magnitude
    (a b : R) : R :=
  nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))

private theorem complex_sqrt_magnitude_ge_abs
    (a b : R) :
    |a| ≤ complex_sqrt_magnitude a b := by
  first
  | have hm0 : 0 ≤ complex_sqrt_magnitude a b :=
      nonnegSqrt_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b))
    have hm : (complex_sqrt_magnitude a b) ^ 2 = a ^ 2 + b ^ 2 :=
      sq_nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
    apply (sq_le_sq₀ (abs_nonneg a) hm0).mp
    rw [sq_abs, hm]
    nlinarith [sq_nonneg b]

private theorem complex_sqrt_radicands_nonneg
    (a b : R) :
    0 ≤ (complex_sqrt_magnitude a b + a) / 2 ∧
      0 ≤ (complex_sqrt_magnitude a b - a) / 2 := by
  first
  | have h' := complex_sqrt_magnitude_ge_abs a b
    constructor <;> apply div_nonneg (by linarith [neg_abs_le a, le_abs_self a]) (by norm_num)

private noncomputable def complex_sqrt_real_part
    (a b : R) : R :=
  nonnegSqrt (complex_sqrt_radicands_nonneg a b).1

private noncomputable def complex_sqrt_imag_part
    (a b : R) : R :=
  nonnegSqrt (complex_sqrt_radicands_nonneg a b).2

/-- The square root in `R[i]` whose real part is nonnegative and whose imaginary part is
nonnegative when the input's imaginary part is nonnegative, and nonpositive otherwise. -/
noncomputable def _root_.QuadraticAlgebra.sqrt
    (z : QuadraticAlgebra R (-1) 0) : QuadraticAlgebra R (-1) 0 := by
  first
  | exact ⟨complex_sqrt_real_part z.re z.im,
      if 0 ≤ z.im then complex_sqrt_imag_part z.re z.im
      else -complex_sqrt_imag_part z.re z.im⟩

/-- The coordinates of the chosen square root satisfy the equations obtained by squaring. -/
theorem _root_.QuadraticAlgebra.sqrt_coordinates
    (z : QuadraticAlgebra R (-1) 0) :
    z.sqrt.re ^ 2 - z.sqrt.im ^ 2 = z.re ∧ 2 * z.sqrt.re * z.sqrt.im = z.im := by
  first
  | let a := z.re
    let b := z.im
    let m := complex_sqrt_magnitude a b
    let s := complex_sqrt_real_part a b
    let q := complex_sqrt_imag_part a b
    have hm : m ^ 2 = a ^ 2 + b ^ 2 :=
      sq_nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
    have hs0 : 0 ≤ s := nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg a b).1
    have hs : s ^ 2 = (m + a) / 2 :=
      sq_nonnegSqrt (complex_sqrt_radicands_nonneg a b).1
    have hq0 : 0 ≤ q := nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg a b).2
    have hq : q ^ 2 = (m - a) / 2 :=
      sq_nonnegSqrt (complex_sqrt_radicands_nonneg a b).2
    have hreal : s ^ 2 - q ^ 2 = a := by
      rw [hs, hq]
      ring
    have hprod_sq : (2 * s * q) ^ 2 = |b| ^ 2 := by
      calc
        (2 * s * q) ^ 2 = 4 * s ^ 2 * q ^ 2 := by ring
        _ = 4 * ((m + a) / 2) * ((m - a) / 2) := by rw [hs, hq]
        _ = b ^ 2 := by nlinarith [hm]
        _ = |b| ^ 2 := by rw [sq_abs]
    have hprod_nonneg : 0 ≤ 2 * s * q := mul_nonneg (mul_nonneg (by norm_num) hs0) hq0
    have hprod : 2 * s * q = |b| :=
      (sq_eq_sq₀ hprod_nonneg (abs_nonneg b)).mp hprod_sq
    have himag : 2 * s * (if 0 ≤ b then q else -q) = b := by
      by_cases hb : 0 ≤ b
      · simpa [hb, abs_of_nonneg hb] using hprod
      · have hbneg : b < 0 := lt_of_not_ge hb
        rw [ite_eq_right hb]
        calc
          2 * s * -q = -(2 * s * q) := by ring
          _ = -|b| := by rw [hprod]
          _ = b := by simp [abs_of_neg hbneg]
    have ha_def : a = z.re := rfl
    have hb_def : b = z.im := rfl
    have hs_def : s = complex_sqrt_real_part a b := rfl
    have hq_def : q = complex_sqrt_imag_part a b := rfl
    simp only [QuadraticAlgebra.sqrt, ← ha_def, ← hb_def, ← hs_def, ← hq_def]
    constructor
    · by_cases hb : 0 ≤ b <;> simp [hb, hreal]
    · exact himag

/-- The chosen square root squares to its input. -/
@[simp]
theorem _root_.QuadraticAlgebra.sq_sqrt
    (z : QuadraticAlgebra R (-1) 0) : z.sqrt ^ 2 = z := by
  first
  | rw [pow_two]
    obtain ⟨hre, him⟩ := QuadraticAlgebra.sqrt_coordinates z
    have hmul : z = z.sqrt * z.sqrt := by
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul]
        linear_combination -hre
      · simp only [QuadraticAlgebra.im_mul]
        linear_combination -him
    exact hmul.symm

private theorem complex_sqrt_magnitude_eq_norm (a b : ℝ) :
    complex_sqrt_magnitude a b =
      ‖(a : ℂ) + (b : ℂ) * Complex.I‖ := by
  first
  | rw [Complex.norm_add_mul_I]
    simpa [complex_sqrt_magnitude] using
      nonnegSqrt_real_eq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))

private theorem complex_sqrt_real_part_eq_mathlib (a b : ℝ) :
    complex_sqrt_real_part a b =
      Real.sqrt ((‖(a : ℂ) + (b : ℂ) * Complex.I‖ + a) / 2) := by
  first
  | rw [← complex_sqrt_magnitude_eq_norm]
    exact nonnegSqrt_real_eq_sqrt (complex_sqrt_radicands_nonneg a b).1

private theorem complex_sqrt_imag_part_eq_mathlib (a b : ℝ) :
    complex_sqrt_imag_part a b =
      Real.sqrt ((‖(a : ℂ) + (b : ℂ) * Complex.I‖ - a) / 2) := by
  first
  | rw [← complex_sqrt_magnitude_eq_norm]
    exact nonnegSqrt_real_eq_sqrt (complex_sqrt_radicands_nonneg a b).2

private noncomputable def quadratic_to_complex_hom : QuadraticAlgebra ℝ (-1) 0 →ₐ[ℝ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp⟩

private theorem quadratic_to_complex_hom_apply (z : QuadraticAlgebra ℝ (-1) 0) :
    quadratic_to_complex_hom z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  first
  | simp [quadratic_to_complex_hom, QuadraticAlgebra.lift]

/-- The real part of the chosen square root is nonnegative. -/
theorem _root_.QuadraticAlgebra.re_sqrt_nonneg
    (z : QuadraticAlgebra R (-1) 0) : 0 ≤ z.sqrt.re :=
  nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg z.re z.im).1

/-- If the input has nonnegative imaginary part, so does its chosen square root. -/
theorem _root_.QuadraticAlgebra.im_sqrt_nonneg_of_im_nonneg
    (z : QuadraticAlgebra R (-1) 0) (hz : 0 ≤ z.im) : 0 ≤ z.sqrt.im := by
  first
  | simpa only [QuadraticAlgebra.sqrt, ite_eq_left hz, complex_sqrt_imag_part] using
      (nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg z.re z.im).2)

/-- If the input has negative imaginary part, its chosen square root has nonpositive
imaginary part. -/
theorem _root_.QuadraticAlgebra.im_sqrt_nonpos_of_im_neg
    (z : QuadraticAlgebra R (-1) 0) (hz : z.im < 0) :
    z.sqrt.im ≤ 0 := by
  first
  | simpa only [QuadraticAlgebra.sqrt, ite_eq_right (not_le_of_gt hz), complex_sqrt_imag_part] using
      (neg_nonpos.mpr (nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg z.re z.im).2))

/-- A square root with nonnegative real part and the chosen imaginary-part sign is `sqrt z`. -/
theorem _root_.QuadraticAlgebra.sqrt_unique
    (z w : QuadraticAlgebra R (-1) 0) (hw_sq : w ^ 2 = z) (hw_re : 0 ≤ w.re)
    (hw_im_sign : if 0 ≤ z.im then 0 ≤ w.im else w.im ≤ 0) : w = z.sqrt := by
  first
  | let v := z.sqrt
    have hv_sq : v ^ 2 = z := by
      simp [v]
    have hfactor : (w - v) * (w + v) = 0 := by
      linear_combination (norm := ring_nf) hw_sq - hv_sq
    rcases mul_eq_zero.mp hfactor with h | h
    · exact sub_eq_zero.mp h
    · have hwv : w = -v := eq_neg_of_add_eq_zero_left h
      have hsum_re : w.re + v.re = 0 := by
        simpa using congrArg QuadraticAlgebra.re h
      have hv_re_nonneg : 0 ≤ v.re := QuadraticAlgebra.re_sqrt_nonneg z
      have hv_re_zero : v.re = 0 := by nlinarith
      have hv_im_eq : 2 * v.re * v.im = z.im := by
        simpa [v] using (QuadraticAlgebra.sqrt_coordinates z).2
      have hz_im_zero : z.im = 0 := by rw [← hv_im_eq, hv_re_zero]; ring
      have hz_im_nonneg : 0 ≤ z.im := by rw [hz_im_zero]
      have hw_im_nonneg' : 0 ≤ w.im := by simpa [hz_im_nonneg] using hw_im_sign
      have hv_im_nonneg : 0 ≤ v.im :=
        QuadraticAlgebra.im_sqrt_nonneg_of_im_nonneg z (by rw [hz_im_zero])
      have hsum_im : w.im + v.im = 0 := by
        simpa using congrArg QuadraticAlgebra.im h
      have hv_im_zero : v.im = 0 := by nlinarith
      have hv_zero : v = 0 := by
        apply QuadraticAlgebra.ext
        · exact hv_re_zero
        · exact hv_im_zero
      change w = v  -- Writing the target as `v` lets the final rewrites by `hwv` and `hv_zero` match.
      rw [hwv, hv_zero]
      simp

/-- The canonical real-algebra equivalence from `ℝ[i]` to `ℂ`. -/
noncomputable def _root_.QuadraticAlgebra.equivComplex :
    QuadraticAlgebra ℝ (-1) 0 ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofBijective quadratic_to_complex_hom (by
    constructor
    · intro z w h
      apply QuadraticAlgebra.ext
      · have hr := congrArg Complex.re h
        simpa [quadratic_to_complex_hom_apply] using hr
      · have hi := congrArg Complex.im h
        simpa [quadratic_to_complex_hom_apply] using hi
    · intro z
      use ⟨z.re, z.im⟩
      rw [quadratic_to_complex_hom_apply]
      apply Complex.ext <;> simp)

/-- The real coordinate of `QuadraticAlgebra.equivComplex` is unchanged. -/
@[simp]
theorem _root_.QuadraticAlgebra.re_equivComplex (z : QuadraticAlgebra ℝ (-1) 0) :
    (QuadraticAlgebra.equivComplex z).re = z.re := by
  first
    -- Expose the algebra hom underlying the equivalence.
  | change (quadratic_to_complex_hom z).re = z.re
    rw [quadratic_to_complex_hom_apply]
    simp

/-- The imaginary coordinate of `QuadraticAlgebra.equivComplex` is unchanged. -/
@[simp]
theorem _root_.QuadraticAlgebra.im_equivComplex (z : QuadraticAlgebra ℝ (-1) 0) :
    (QuadraticAlgebra.equivComplex z).im = z.im := by
  first
    -- Expose the algebra hom underlying the equivalence.
  | change (quadratic_to_complex_hom z).im = z.im
    rw [quadratic_to_complex_hom_apply]
    simp

/-- `QuadraticAlgebra.sqrt` agrees with Mathlib's principal complex square root over `ℝ`. -/
theorem _root_.QuadraticAlgebra.equivComplex_sqrt (z : QuadraticAlgebra ℝ (-1) 0) :
    QuadraticAlgebra.equivComplex z.sqrt =
      Complex.sqrt (QuadraticAlgebra.equivComplex z) := by
  first
    -- Expose the algebra hom underlying the equivalence to apply the complex comparison.
  | change quadratic_to_complex_hom z.sqrt = Complex.sqrt (quadratic_to_complex_hom z)
    rw [quadratic_to_complex_hom_apply, quadratic_to_complex_hom_apply,
      Complex.sqrt_eq_real_add_ite]
    apply Complex.ext
    · simp [QuadraticAlgebra.sqrt, complex_sqrt_real_part_eq_mathlib, Complex.mul_re, apply_ite]
    · simp [QuadraticAlgebra.sqrt, complex_sqrt_imag_part_eq_mathlib, Complex.mul_im, apply_ite]
      by_cases hb : 0 ≤ z.im <;> simp [hb]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Every element of `R[i]` is a square when `R` is real closed, without choosing an order. -/
theorem isSquare (z : QuadraticAlgebra R (-1) 0) : IsSquare z := by
  first
  | obtain ⟨o, ho⟩ := IsSemireal.exists_linearOrder (K := R)
    let := o
    have := ho
    use z.sqrt
    simpa [pow_two] using (QuadraticAlgebra.sq_sqrt z).symm

end QuadraticAlgebra
end -- closes the original EOF section from source line 35
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/FieldTheory/RealClosure/Complexification.lean -/

/- BEGIN SOURCE: TauCeti/FieldTheory/RealClosure/AlgebraicClosed.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Algebraic closedness of the complexification

`finrank_eq_one_of_forall_isSquare` proves that a finite extension of a finite
square-closed extension of a real closed field is trivial. `isAlgClosed_of_forall_isSquare`
then proves algebraic closedness of that square-closed field. In particular,
`isAlgClosed_quadraticAlgebra` proves that `R[i] = QuadraticAlgebra R (-1) 0` is
algebraically closed. `Polynomial.natDegree_le_two_of_irreducible` bounds irreducible degrees
by two; the polynomial IVT development uses this bound.
Open `scoped TauCeti.RealClosure` to enable the algebraic-closedness instance on this
quadratic algebra.

The proof puts finite extensions inside a finite normal closure. The 2-group argument
then applies to the Galois group over a square-closed intermediate field.

The degree bound generalizes Mathlib's `Irreducible.natDegree_le_two` from
`Mathlib.Analysis.Complex.Polynomial.Basic`, following its root, minimal polynomial,
and finite-dimension proof over an arbitrary real closed field.

## References

The algebraic argument uses a Sylow 2-subgroup of the Galois group; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Theorem 2.2.
-/

public section

namespace TauCeti.RealClosure

open Module IntermediateField

variable {R C L : Type*} [Field R] [IsRealClosed R] [Field C] [Algebra R C]
    [FiniteDimensional R C] [Field L] [Algebra R L] [Algebra C L]
    [IsScalarTower R C L] [FiniteDimensional C L]

include R in
/-- Every finite extension of a finite square-closed extension of a real
closed field is trivial. -/
theorem finrank_eq_one_of_forall_isSquare (hsq : ∀ x : C, IsSquare x) :
    finrank C L = 1 := by
  first
  | let M := AlgebraicClosure L
    have : FiniteDimensional R L := FiniteDimensional.trans R C L
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap R L).injective
    have : IsGalois R M := { }
    let N := normalClosure R L M
    let : Algebra C N := ((algebraMap L N).comp (algebraMap C L)).toAlgebra
    have : IsScalarTower C L N := .of_algebraMap_eq' rfl
    have : IsScalarTower R C N := .of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq R L N, IsScalarTower.algebraMap_eq R C L]
      rfl)
    have hN : Module.finrank C N = 1 := finrank_eq_one_of_isGalois_of_forall_isSquare (R := R) hsq
    exact Nat.eq_one_of_dvd_one (hN ▸ finrank_dvd_finrank_right C L N)

include R in
/-- A finite square-closed extension of a real closed field is algebraically closed. -/
theorem isAlgClosed_of_forall_isSquare (hsq : ∀ x : C, IsSquare x) : IsAlgClosed C := by
  first
  | apply IsAlgClosed.of_exists_root
    intro p _ hp
    have : Fact (Irreducible p) := ⟨hp⟩
    have : FiniteDimensional C (AdjoinRoot p) :=
      (AdjoinRoot.powerBasis hp.ne_zero).finite
    have hdim := finrank_eq_one_of_forall_isSquare (R := R) (L := AdjoinRoot p) hsq
    have hdeg : p.natDegree = 1 := by
      rwa [(AdjoinRoot.powerBasis hp.ne_zero).finrank] at hdim
    exact Polynomial.exists_root_of_degree_eq_one
      ((Polynomial.degree_eq_iff_natDegree_eq_of_pos one_pos).mpr hdeg)

/-- The complexification `R[i]` of a real closed field is algebraically closed. -/
scoped instance isAlgClosed_quadraticAlgebra : IsAlgClosed (QuadraticAlgebra R (-1) 0) :=
  isAlgClosed_of_forall_isSquare (R := R) QuadraticAlgebra.isSquare

open _root_.Polynomial in
/-- Irreducible polynomials over a real closed field have degree at most two. -/
theorem _root_.Polynomial.natDegree_le_two_of_irreducible (p : R[X]) (hp : Irreducible p) :
    p.natDegree ≤ 2 := by
  first
  | obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero
      (QuadraticAlgebra R (-1) 0) p (degree_pos_of_irreducible hp).ne'
    have heq := minpoly.eq_of_irreducible hp hz
    have hdeg : p.natDegree = (minpoly R z).natDegree := by
      rw [← heq, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))]
    rw [hdeg]
    exact (minpoly.natDegree_le z).trans_eq (QuadraticAlgebra.finrank_eq_two _ _)

end TauCeti.RealClosure
end -- closes the original EOF section from source line 38
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/FieldTheory/RealClosure/AlgebraicClosed.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/LinearFactor.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The linear factor `X - C x`, and its reverse

Linear factors, scalar factorizations, and the full power of a root factor.
Over an ordered field, a polynomial of degree at most one has constant sign on a root-free interval.

The *reversed* factor `C x - X` — the shape that arises as `x - θ` in `AdjoinRoot f` — has degree
`1`, like `X - C x` itself, which is the form Mathlib states.

A polynomial of degree at most one with root `x` is `C γ * (X - C x)` for a single scalar `γ`.
Writing it as `C a * X + C b`, the root condition gives `a * x + b = 0`, which identifies the
constant term and factors the polynomial. This works over noncommutative rings, with the scalar
factor on the left.

Factoring out the full multiplicity of a root of a nonzero polynomial leaves a cofactor
that does not vanish at the root.

## Main results

* `Polynomial.modByMonic_X_sub_C_eq_zero`: division by a central linear factor has zero
  remainder at a root.
* `Polynomial.natDegree_C_sub_X`: the reversed linear factor `C x - X` has degree `1`.
* `Polynomial.exists_eq_C_mul_X_sub_C_of_natDegree_le_one`: a polynomial of `natDegree ≤ 1` with
  root `x` is `C γ * (X - C x)` for some `γ`.
* `Polynomial.eval_mul_pos_of_natDegree_le_one_of_no_roots`: constant nonzero sign on a root-free
  closed interval for polynomials of degree at most one.
* `Polynomial.derivative_root_factors`: factor the derivative of a polynomial with two root powers.
* `Polynomial.IsRoot.exists_eq_pow_succ_mul`: factor out a positive power of `X - C x`, leaving a
  cofactor nonzero at `x`.
* `Polynomial.rootMultiplicity_add_eq_left_of_dvd`: adding a multiple of a higher power of
  `X - C x` leaves the root multiplicity at `x` unchanged.
* `Polynomial.rootMultiplicity_neg`: negating a polynomial leaves its root multiplicities
  unchanged.

## Provenance

The statement of `exists_eq_C_mul_X_sub_C_of_natDegree_le_one` generalizes the commutative-ring
result adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, revision `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`.
Its consumer is the `x - T` descent map of
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`, where it pins down the line
through a `2`-torsion point.
-/

public section

namespace Polynomial

variable {R : Type*} [Ring R]

/-- Division by `X - c` leaves no remainder at a root `c` that commutes with every coefficient. -/
theorem modByMonic_X_sub_C_eq_zero {B : Type*} [Ring B] {p : B[X]} {c : B}
    (hc : ∀ b, Commute c b) (hp : p.eval c = 0) : p %ₘ (Polynomial.X - C c) = 0 := by
  first
  | nontriviality B
    have hd := degree_modByMonic_lt p (monic_X_sub_C c)
    rw [degree_X_sub_C] at hd
    have hr := eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hd)
    have he := congrArg (Polynomial.eval c) (modByMonic_add_div p (Polynomial.X - C c))
    rw [hr] at he
    simp only [eval_add, eval_C, sub_mul, Polynomial.X_mul, eval_sub, eval_mul_X,
      eval_C_mul, (hc _).eq, sub_self, add_zero, hp] at he
    rw [hr, he, C_0]

/-- The reversed linear polynomial `C x - X` has degree `1`, like `X - C x`. -/
@[simp]
theorem natDegree_C_sub_X {R : Type*} [Ring R] [Nontrivial R] (x : R) :
    (C x - X).natDegree = 1 := by
  first
  | rw [natDegree_sub, natDegree_X_sub_C]

/-- A polynomial of degree at most one with prescribed root `x` is a left scalar multiple of
`X - C x`, over any ring. -/
lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  first
  | obtain ⟨a, b, hp⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg
    have hx' : a * x + b = 0 := by
      simpa only [IsRoot, hp, eval_add, eval_C_mul, eval_C, eval_X] using hx
    refine ⟨a, ?_⟩
    rw [hp, mul_sub, ← C_mul, eq_neg_of_add_eq_zero_right hx', map_neg, sub_eq_add_neg]

/-- A root of a nonzero polynomial factors out with positive multiplicity and a cofactor
that does not vanish at the root. -/
theorem IsRoot.exists_eq_pow_succ_mul {A : Type*} [CommRing A] {p : A[X]} {a : A}
    (ha : p.IsRoot a) (hp : p ≠ 0) :
    ∃ m : ℕ, ∃ q : A[X], p = (X - C a) ^ (m + 1) * q ∧ q.eval a ≠ 0 := by
  first
  | obtain ⟨q, hq, hn⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero ((rootMultiplicity_pos hp).mpr ha).ne'
    exact ⟨m, q, by simpa only [hm] using hq, fun h => hn (dvd_iff_isRoot.mpr h)⟩

/-- Adding a multiple of a higher power of `X - C a` does not change the root multiplicity
at `a` of a nonzero polynomial. -/
theorem rootMultiplicity_add_eq_left_of_dvd {A : Type*} [Ring A] {p q : A[X]} {a : A}
    (hp : p ≠ 0) (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).rootMultiplicity a = p.rootMultiplicity a := by
  first
  | have hpq : p + q ≠ 0 := by
      intro h
      rw [eq_neg_of_add_eq_zero_right h, dvd_neg] at hq
      exact pow_rootMultiplicity_not_dvd hp a hq
    refine le_antisymm ?_ ?_
    · rw [rootMultiplicity_le_iff hpq]
      intro h
      exact pow_rootMultiplicity_not_dvd hp a (by simpa using dvd_sub h hq)
    · apply (le_rootMultiplicity_iff hpq).mpr
      exact dvd_add (pow_rootMultiplicity_dvd p a) ((pow_dvd_pow _ (Nat.le_succ _)).trans hq)

/-- Negating a polynomial does not change its root multiplicity at any point. -/
@[simp]
theorem rootMultiplicity_neg (p : R[X]) (a : R) :
    (-p).rootMultiplicity a = p.rootMultiplicity a := by
  first
  | classical
    simp [rootMultiplicity_eq_multiplicity, multiplicity_neg]

/-- A polynomial of degree at most one has constant nonzero sign on an interval without a root. -/
theorem eval_mul_pos_of_natDegree_le_one_of_no_roots {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {p : R[X]} (hdeg : p.natDegree ≤ 1) {a b : R}
    (hab : a ≤ b) (hroot : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    0 < p.eval a * p.eval b := by
  first
  | by_cases hd0 : p.natDegree = 0
    · have hs : p.eval b = p.eval a := by rw [eq_C_of_natDegree_eq_zero hd0]; simp
      rw [hs]
      exact mul_self_pos.mpr (hroot a ⟨le_rfl, hab⟩)
    have hd1 : p.natDegree = 1 := by omega
    have hd : p.degree = 1 := (degree_eq_iff_natDegree_eq_of_pos (by decide)).mpr hd1
    obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hd
    obtain ⟨c, hc⟩ := exists_eq_C_mul_X_sub_C_of_natDegree_le_one hdeg hr
    have hcne : c ≠ 0 := by
      intro hz
      apply hroot a ⟨le_rfl, hab⟩
      simp [hc, hz]
    have hprod : 0 < (a - r) * (b - r) := by
      rcases lt_or_ge r a with h | h
      · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (h.trans_le hab))
      · have hb : b < r := by
          by_contra! hb
          exact hroot r ⟨h, hb⟩ hr
        exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans_lt hb)) (sub_neg.mpr hb)
    simp only [hc, eval_mul, eval_C, eval_sub, eval_X]
    convert mul_pos (mul_self_pos.mpr hcne) hprod using 1
    ring

/-- Factor the derivative after removing the powers contributed by two roots. -/
theorem derivative_root_factors {A : Type*} [CommRing A] (a b : A) (m n : ℕ) (r : A[X]) :
    ((X - C a) ^ (m + 1) * ((X - C b) ^ (n + 1) * r)).derivative =
      (X - C a) ^ m * (X - C b) ^ n *
        (C ((m : A) + 1) * (X - C b) * r + C ((n : A) + 1) * (X - C a) * r +
          (X - C a) * (X - C b) * r.derivative) := by
  first
  | simp only [derivative_mul, derivative_pow_succ, derivative_sub, derivative_X,
      derivative_C, sub_zero, mul_one]
    simp only [pow_succ]
    ring

end Polynomial

end
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/LinearFactor.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/QuadraticDiscriminant.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/


/-!
# Non-negativity of a binary quadratic form and its discriminant

Mathlib's `discrim_le_zero` shows that a quadratic polynomial over a linearly ordered field which
is non-negative at every point of the field has non-positive discriminant. This file supplies two
facts about the homogeneous two-variable form `a * x ^ 2 + b * x * y + c * y ^ 2` that it does not
give: the reverse implication, and an integral version whose hypothesis is much weaker. It also
records two elementary facts about discriminants used for positive definite integral forms: a
negative discriminant together with `0 ≤ a` forces `0 < a`, and an integral discriminant is `0` or
`1` modulo `4`.

The integral version is the substantial one, and it is worth being precise about what makes it
substantial. Over a *field*, non-negativity along a single line `y = y₀ ≠ 0` already forces
`discrim a b c ≤ 0`: the restriction is a quadratic in `x`, so `discrim_le_zero` applies and the
resulting `y₀ ^ 2 * discrim a b c ≤ 0` may be divided by `y₀ ^ 2`. Over `ℤ` the same hypothesis
with `x` ranging over the *integers* is strictly weaker, and is genuinely not enough: the map
`x ↦ x ^ 2 - x` is non-negative at every integer, yet `discrim 1 (-1) 0 = 1 > 0`, which is
`forall_int_nonneg_and_discrim_pos` below. `Int.discrim_le_zero_of_nonneg_of_lt_abs` says that one
extra condition — that `|y₀|` exceed the leading coefficient — repairs this, with no further
quantification needed.

Together with the reverse implication this gives the upgrade that motivates the file: a form known
to be non-negative only on some sparse subset of `ℤ ⨯ ℤ` — the locus where a fixed prime divides
neither coordinate — is non-negative everywhere.
`Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd` pins the discriminant from that locus alone,
and `nonneg_of_discrim_le_zero` then propagates the conclusion to every `(x, y)`.

## Main results

* `nonneg_of_discrim_le_zero`: `0 < a` and `discrim a b c ≤ 0` give `0 ≤ a x² + b x y + c y²`.
* `discrim_pos_of_exists_pos_of_exists_neg`: representing both signs forces positive discriminant.
* `Int.discrim_le_zero_of_nonneg_of_lt_abs`: for `a < |y|`, and with no sign condition on `a`,
  non-negativity of `a x² + b x y + c y²` in `x` alone forces `discrim a b c ≤ 0`.
* `Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd`: the same conclusion from non-negativity
  on `{(x, y) : d ∤ x ∧ d ∤ y}`, for any non-unit `d`.
* `pos_of_nonneg_of_discrim_lt_zero`: a quadratic of negative discriminant with `0 ≤ a` has
  `0 < a`.
* `Int.discrim_emod_four`: `discrim a b c % 4 = b % 2`, so an integral discriminant is `0` or `1`
  modulo `4`.
* `TauCeti.not_dvd_two_mul_mul_add_of_not_dvd_discrim`: a root modulo `p` of a quadratic whose
  discriminant is not divisible by `p` is simple, that is `p ∤ 2 a x + b`;
  `TauCeti.not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul` is the case of the monic quadratic
  `x² + b x − c`.

The two `Int.discrim_le_zero_…` results are proved from a common lemma in which `x` runs over an
arithmetic progression rather than all of `ℤ`. Only one `x` is ever used — the member of the
progression nearest the minimum of the restricted form — so thinning the line to gap `m` costs
exactly a factor `m` in the height hypothesis, which the choice of `y` absorbs; `m = 1` is the full
line.

The weaker hypothesis constraining only `y` is not stated separately: it is strictly stronger
than the one above, so a caller holding it applies the same theorem through
`fun x y _ hy => h x y hy`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/Discriminant.lean`, declarations `exists_int_balanced`,
`qf_nonneg_of_nonneg_on_coprime` and `qf_nonneg_of_nonneg_on_coprime_both`. The statements here
are strictly stronger: the form is arbitrary rather than `q r² − t r s + s²`, no primality is
assumed, and a single `y` replaces an infinite family of prime powers.

The source proves its two locus results independently, the `d ∤ y` one by an infinite family of
prime powers together with a balanced-remainder lemma. Neither is reproduced. The `d ∤ y`
statement is not carried at all: it follows from the `d ∤ x ∧ d ∤ y` one in a line, its hypothesis
being the stronger of the two. The balanced remainder it needed is Mathlib's `round`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.2 — the Cauchy–Schwarz step that turns
  positivity of the degree form on a rank-two lattice into the Hasse inequality of V.1.1.
-/

public section

/-- A binary quadratic form with positive leading coefficient and non-positive discriminant is
non-negative. This is the implication opposite to Mathlib's `discrim_le_zero`, stated for the
homogeneous two-variable form and over a linearly ordered commutative ring rather than a field.
The hypothesis `0 < a` cannot be dropped: `discrim 0 0 (-1) = 0`, while `- y ^ 2` is negative. -/
theorem nonneg_of_discrim_le_zero {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R} (ha : 0 < a) (hd : discrim a b c ≤ 0) (x y : R) :
    0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  first
    -- The completed square `4a·Q = (2ax + by)² + (4ac − b²)y²` uses no division.
  | have hb : 0 ≤ 4 * a * c - b ^ 2 := by rw [discrim] at hd; linarith
    nlinarith [sq_nonneg (2 * a * x + b * y), mul_nonneg hb (sq_nonneg y)]

/-- A homogeneous binary quadratic form which represents both a positive and a negative value
has positive discriminant. The statement needs no division or nondegeneracy hypothesis. -/
theorem discrim_pos_of_exists_pos_of_exists_neg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R}
    (hpos : ∃ x y, 0 < a * x ^ 2 + b * x * y + c * y ^ 2)
    (hneg : ∃ x y, a * x ^ 2 + b * x * y + c * y ^ 2 < 0) : 0 < discrim a b c := by
  first
  | by_contra! hd
    obtain ⟨xp, yp, hp⟩ := hpos
    obtain ⟨xn, yn, hn⟩ := hneg
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have h := nonneg_of_discrim_le_zero (neg_pos.mpr ha)
        ((discrim_neg a b c).symm ▸ hd) xp yp
      nlinarith
    · subst a
      have hb : b = 0 := by
        rw [discrim] at hd
        nlinarith [sq_nonneg b]
      subst b
      simp only [zero_mul, zero_add] at hp hn
      rcases le_or_gt c 0 with hc | hc
      · exact hp.not_ge (mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg yp))
      · exact hn.not_ge (mul_nonneg hc.le (sq_nonneg yn))
    · exact hn.not_ge (nonneg_of_discrim_le_zero ha hd xn yn)

/-- A quadratic of negative discriminant with a non-negative leading coefficient has a positive
one: at `a = 0` the discriminant is `b ^ 2`, which is not negative. -/
theorem pos_of_nonneg_of_discrim_lt_zero {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R} (ha : 0 ≤ a) (hd : discrim a b c < 0) : 0 < a :=
  ha.lt_of_ne' fun ha ↦ hd.not_ge <| by simp [discrim, ha, sq_nonneg]

/-- Some member of the progression `x₀ + m * ℤ` puts `2 a x + z` within `a * m` of zero, for any
constant `z`.

This is the point-selection step of `discrim_le_zero_of_pos_of_nonneg_on_progression`, and the
source of the factor `m` in that theorem's height hypothesis. There `z` is the form's `b * y`,
which enters only as a constant. -/
private theorem exists_abs_two_mul_add_le {a m x₀ z : ℤ} (ha : 0 < a) (hm : 0 < m) :
    ∃ k : ℤ, |2 * a * (x₀ + m * k) + z| ≤ a * m := by
  first
    -- take the member nearest the value that would make `2 a x + z` vanish: the rounding error is
    -- at most a half, and the progression's gap scales it by `2 a m`
  | have ham : (0 : ℚ) < 2 * (a : ℚ) * (m : ℚ) := by
      positivity
    set t : ℚ := (-(z : ℚ) - 2 * (a : ℚ) * (x₀ : ℚ)) / (2 * (a : ℚ) * (m : ℚ)) with htdef
    refine ⟨round t, ?_⟩
    have hcast : ((2 * a * (x₀ + m * round t) + z : ℤ) : ℚ)
        = 2 * (a : ℚ) * (m : ℚ) * ((round t : ℚ) - t) := by
      rw [htdef]; field_simp; push_cast; ring
    have hq : |((2 * a * (x₀ + m * round t) + z : ℤ) : ℚ)| ≤ ((a * m : ℤ) : ℚ) := by
      rw [hcast, abs_mul, abs_of_pos ham]
      push_cast
      nlinarith [abs_sub_round t, abs_nonneg ((round t : ℚ) - t), abs_sub_comm (round t : ℚ) t]
    exact_mod_cast hq

/-- **An arithmetic progression of large enough height pins the discriminant.** If a binary
quadratic form over `ℤ` with positive leading coefficient `a` is non-negative at `(x, y)` for a
fixed `y` and every `x` in the progression `x₀ + m * ℤ`, and `a * m < |y|`, then
`discrim a b c ≤ 0`.

The height hypothesis carries a factor `m` that the single-line version does not; `m = 1` is the
full line. -/
private theorem discrim_le_zero_of_pos_of_nonneg_on_progression {a b c m x₀ y : ℤ} (ha : 0 < a)
    (hm : 0 < m) (hy : a * m < |y|)
    (h : ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  first
    -- Only one `x` is used: the member of the progression nearest the minimum of the restricted
    -- form, which satisfies `|2 a x + b y| ≤ a * m`. That is why thinning the line to gap `m` costs
    -- exactly a factor `m` in the height.
  | by_contra! hcon
    rw [discrim] at hcon
    obtain ⟨k, hxa⟩ := exists_abs_two_mul_add_le (x₀ := x₀) (z := b * y) ha hm
    set x : ℤ := x₀ + m * k
    have hsq : (2 * a * x + b * y) ^ 2 ≤ (a * m) ^ 2 := by
      have habs := abs_le.mp hxa
      nlinarith [habs.1, habs.2]
    -- `a * m < |y|` makes the `(4ac − b²)y²` term outweigh it, so the form is negative at `(x, y)`.
    have ham0 : 0 < a * m := by positivity
    have hy2 : (a * m) ^ 2 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have hkey : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2)
        = (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by ring
    nlinarith [h k, hsq, hy2, hkey]

/-- A form with negative leading coefficient is eventually negative along any progression, so the
non-negativity hypothesis is unsatisfiable. -/
private theorem not_forall_nonneg_on_progression_of_neg {a b c m x₀ y : ℤ} (ha : a < 0)
    (hm : 0 < m) :
    ¬ ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2 := fun h => by
  have hA0 : 0 ≤ |b * y| := abs_nonneg _
  have hB0 : 0 ≤ |c * y ^ 2| := abs_nonneg _
  set M : ℤ := |b * y| + |c * y ^ 2| + 1
  have hM1 : 1 ≤ M := by omega
  -- The progression reaches past `M`, and there the square already dominates the rest.
  set k : ℤ := M + |x₀| with hk
  have hk0 : 0 ≤ k := by have := abs_nonneg x₀; omega
  set x : ℤ := x₀ + m * k with hx
  have hxM : M ≤ x := by
    first
    | have h1 : k ≤ m * k := le_mul_of_one_le_left hk0 hm
      have h2 : -|x₀| ≤ x₀ := neg_abs_le x₀
      rw [hx, hk] at *
      linarith
  have h1 : a * x ^ 2 ≤ -(x ^ 2) := by nlinarith [sq_nonneg x]
  have h2 : b * x * y ≤ |b * y| * x := by
    first
    | nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self (b * y))) (by linarith : (0 : ℤ) ≤ x)]
  have h3 : c * y ^ 2 ≤ |c * y ^ 2| := le_abs_self _
  have h4 : |b * y| * x + |c * y ^ 2| + 1 ≤ x ^ 2 := by nlinarith
  linarith [h k]

/-- A form with zero leading coefficient is linear along a progression, so non-negativity there
forces the slope `b * y * m` to vanish; with `y ≠ 0` and `0 < m` that makes `b = 0`. -/
private theorem eq_zero_of_forall_nonneg_on_progression_of_ne {b c m x₀ y : ℤ} (hy : y ≠ 0)
    (hm : 0 < m)
    (h : ∀ k : ℤ, 0 ≤ 0 * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) : b = 0 := by
  first
  | by_contra hb
    set C : ℤ := b * y * x₀ + c * y ^ 2 with hC
    have hid : ∀ k : ℤ, 0 * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2
        = b * y * m * k + C := fun k => by rw [hC]; ring
    have hC0 : 0 ≤ |C| := abs_nonneg _
    have hCle : C ≤ |C| := le_abs_self _
    have hpos : 0 < (b * y * m) ^ 2 := by positivity
    -- At this `k` the linear term is `-(|C| + 1) * (b y m)²`, which the constant cannot offset.
    have hx := h (-((|C| + 1) * (b * y * m)))
    rw [hid] at hx
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ |C| + 1)
      (by linarith : (0 : ℤ) ≤ (b * y * m) ^ 2 - 1)]

/-- **A progression of large enough height pins the discriminant, whatever the sign of `a`.** No
sign hypothesis on `a` is needed; this is the form both public theorems specialise. -/
private theorem discrim_le_zero_of_nonneg_on_progression {a b c m x₀ y : ℤ} (hm : 0 < m)
    (hy : a * m < |y|)
    (h : ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  first
    -- A negative leading coefficient makes the hypothesis unsatisfiable; a zero one collapses the
    -- form to a linear function, forcing `b = 0`; a positive one is the case that does the work.
  | rcases lt_trichotomy a 0 with ha | ha | ha
    · exact absurd h (not_forall_nonneg_on_progression_of_neg ha hm)
    · subst ha
      have hy0 : y ≠ 0 := by rintro rfl; simp at hy
      rw [discrim, eq_zero_of_forall_nonneg_on_progression_of_ne hy0 hm h]
      simp
    · exact discrim_le_zero_of_pos_of_nonneg_on_progression ha hm hy h

/-- **A single line of large enough height pins the discriminant.** If a binary quadratic form
over `ℤ` is non-negative at `(x, y)` for a fixed `y` with `a < |y|` and every integer `x`, then
`discrim a b c ≤ 0`, that is `b ^ 2 ≤ 4 * a * c`.

No sign hypothesis on `a` is needed. A negative leading coefficient makes the hypothesis
unsatisfiable, and a zero one collapses the form to a linear function of `x`, forcing `b = 0`.

The height hypothesis `a < |y|` is necessary, not an artefact of the proof: without it the
integer-valued hypothesis is strictly weaker than its field counterpart, as
`forall_int_nonneg_and_discrim_pos` witnesses. -/
theorem Int.discrim_le_zero_of_nonneg_of_lt_abs {a b c y : ℤ} (hy : a < |y|)
    (h : ∀ x : ℤ, 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) : discrim a b c ≤ 0 :=
  -- The whole line is the progression of gap `1` through `0`.
  discrim_le_zero_of_nonneg_on_progression (x₀ := 0) one_pos (by simpa using hy)
    fun k => by simpa using h k

/-- The height hypothesis of `Int.discrim_le_zero_of_nonneg_of_lt_abs` cannot be dropped:
`x ↦ x ^ 2 - x` is non-negative at every integer, yet its discriminant is positive. Here the
leading coefficient and `|y|` are both `1`, so `a < |y|` fails by exactly one. -/
private theorem forall_int_nonneg_and_discrim_pos :
    (∀ x : ℤ, 0 ≤ 1 * x ^ 2 + (-1) * x * 1 + 0 * 1 ^ 2) ∧ 0 < discrim (1 : ℤ) (-1) 0 := by
  first
  | refine ⟨fun x => ?_, by norm_num [discrim]⟩
    rcases le_or_gt x 0 with hx | hx
    · nlinarith
    · nlinarith [Int.add_one_le_iff.mpr hx]

/-- Every member of the progression `1 + max |d| 2 * ℤ` avoids the multiples of a non-unit `d`.

The modulus is `|d|` in the intended case, `2` being needed only for `d = 0`: there the multiples
of `d` are `{0}` alone, and what has to be said is that `1 + 2 * k` is odd, hence nonzero. -/
private theorem not_dvd_one_add_max_mul {d : ℤ} (hd : ¬ IsUnit d) (k : ℤ) :
    ¬ d ∣ 1 + max |d| 2 * k := by
  first
  | intro hdvd
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [zero_dvd_iff] at hdvd
      rw [abs_zero, max_eq_right (by norm_num)] at hdvd
      omega
    · have hd2 : 1 < |d| := by
        have h1 : d.natAbs ≠ 1 := fun hh => hd (Int.isUnit_iff_natAbs_eq.mpr hh)
        have h0 : d.natAbs ≠ 0 := fun hh => hd0 (Int.natAbs_eq_zero.mp hh)
        have : (1 : ℤ) < (d.natAbs : ℤ) := by
          exact_mod_cast Nat.lt_of_le_of_ne (by omega) (by omega)
        rwa [Int.abs_eq_natAbs]
      rw [max_eq_left (by omega), add_comm] at hdvd
      have hd1 : d ∣ (1 : ℤ) :=
        (dvd_add_right (((dvd_abs d d).mpr dvd_rfl).mul_right k)).mp hdvd
      exact absurd (Int.le_of_dvd one_pos ((abs_dvd d 1).mpr hd1)) (by omega)

/-- **The locus where `d` divides neither coordinate pins the discriminant.** If a binary
quadratic form over `ℤ` is non-negative at every `(x, y)` with `d ∤ x` and `d ∤ y`, for a non-unit
`d`, then `discrim a b c ≤ 0`.

The one-coordinate variant, constraining only `y`, is not stated separately: its hypothesis holds
on a strictly larger set of points, so it is the stronger of the two and a caller holding it
applies this theorem through `fun x y _ hy => h x y hy`. The implication does not run the other
way, and it is this form that an elliptic curve supplies, the pencil `r π − s` being known to be
an isogeny only away from both coordinates.

`d = 0` is allowed, the hypothesis then being non-negativity at every `(x, y)` with `x ≠ 0` and
`y ≠ 0`. -/
theorem Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd {a b c d : ℤ} (hd : ¬ IsUnit d)
    (h : ∀ x y : ℤ, ¬ d ∣ x → ¬ d ∣ y → 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  first
    -- Both coordinates run over `1 + max |d| 2 * ℤ`, every member of which avoids the multiples of
    -- `d`; the widened gap costs a factor `max |d| 2` in the height, which the choice of `y` absorbs.
  | set m : ℤ := max |d| 2 with hmdef
    have hm2 : 2 ≤ m := le_max_right _ _
    have hm0 : 0 < m := by omega
    have hdm : ∀ k : ℤ, ¬ d ∣ 1 + m * k := fun k => by rw [hmdef]; exact not_dvd_one_add_max_mul hd k
    -- One second coordinate serves every case: it avoids `d` and clears the widened height bound.
    have hA : 0 ≤ |a| := abs_nonneg a
    have haA : a ≤ |a| := le_abs_self a
    have hAm : 0 ≤ |a| * m := mul_nonneg hA hm0.le
    set y : ℤ := 1 + m * (|a| * m) with hy
    have hmm : 0 ≤ m * (|a| * m) := mul_nonneg hm0.le hAm
    have hy0 : 0 < y := by rw [hy]; linarith
    have hheight : a * m < |y| := by
      rw [abs_of_pos hy0, hy]
      have h1 : a * m ≤ |a| * m := mul_le_mul_of_nonneg_right haA hm0.le
      have h2 : |a| * m ≤ m * (|a| * m) := by nlinarith
      linarith
    have hyd : ¬ d ∣ y := hdm _
    exact discrim_le_zero_of_nonneg_on_progression hm0 hheight fun k => h _ y (hdm k) hyd


/-- The discriminant `b² - 4 a c` of integers `a`, `b`, `c` leaves the remainder `b % 2` on
division by `4`, so it is `0` or `1` modulo `4`. -/
@[simp]
theorem Int.discrim_emod_four (a b c : ℤ) : discrim a b c % 4 = b % 2 := by
  first
  | rw [discrim, mul_assoc, Int.sub_mul_emod_self_left, Int.sq_emod_four]

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- A root modulo `p` of a quadratic whose discriminant is not divisible by `p` is simple: the
derivative `2 a x + b` is not divisible by `p`, since
`(2 a x + b)² = 4 a (a x² + b x + c) + discrim a b c`. -/
theorem not_dvd_two_mul_mul_add_of_not_dvd_discrim {p a b c x : R}
    (hd : ¬ p ∣ discrim a b c) (hx : p ∣ a * (x * x) + b * x + c) : ¬ p ∣ 2 * a * x + b :=
  fun h ↦ hd <| by
    rw [show discrim a b c = (2 * a * x + b) ^ 2 - 4 * a * (a * (x * x) + b * x + c) by
      rw [discrim]; ring]
    exact dvd_sub (dvd_pow h two_ne_zero) (hx.mul_left _)

/-- A root modulo `p` of the monic quadratic `x² + b x − c` is simple when `p ∤ b² + 4 c`: the
derivative `2 x + b` is not divisible by `p`. This is
`TauCeti.not_dvd_two_mul_mul_add_of_not_dvd_discrim` for the monic quadratic, whose discriminant
is `b² + 4 c`. -/
theorem not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul {p b c x : R} (hd : ¬ p ∣ b ^ 2 + 4 * c)
    (hx : p ∣ x ^ 2 + b * x - c) : ¬ p ∣ 2 * x + b := by
  first
  | simpa using not_dvd_two_mul_mul_add_of_not_dvd_discrim (a := 1) (c := -c)
      (by rwa [discrim, mul_neg, sub_neg_eq_add, mul_one]) (by rwa [one_mul, ← sq, ← sub_eq_add_neg])

end TauCeti
end -- closes the original EOF section from source line 84
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/QuadraticDiscriminant.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Separability and splitting criteria for quadratic polynomials

Mathlib's `Mathlib/Algebra/QuadraticDiscriminant.lean` works with the *equation*
`a x² + b x + c = 0` and relates its solutions to `discrim a b c = b² - 4 a c`. This file reads
those facts back as statements about the *polynomial* `C a * X ^ 2 + C b * X + C c`. Wherever a
statement mentions the discriminant it uses Mathlib's `discrim` rather than its expansion, so
that Mathlib's discriminant API applies to it directly; the two criteria phrased by a root or by
an Artin-Schreier condition mention no discriminant at all.

Over an ordered commutative ring, `TauCeti.quadratic_pos_iff_of_discrim_neg` and
`TauCeti.quadratic_neg_iff_of_discrim_neg` identify the sign of a quadratic with negative
discriminant from its leading coefficient.

Over a field, with `a ≠ 0`:

* `Polynomial.separable_quadratic_iff_discrim_ne_zero`: separable exactly when `discrim a b c ≠ 0`;
* `Polynomial.splits_quadratic_iff_exists_root`: splits exactly when it has a root — the
  characteristic-free core the other two are read off from;
* `Polynomial.splits_quadratic_iff_isSquare`: away from characteristic two, splits exactly when
  `discrim a b c` is a square;
* `Polynomial.splits_quadratic_of_discrim_eq_zero`: over a perfect field, splits as soon as
  `discrim a b c = 0`;
* `Polynomial.exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero`: over a perfect
  field, if `discrim a b c = 0` then some `x` is a root of the quadratic and of its derivative;
* `Polynomial.card_rootSet_quadratic_of_discrim_eq_zero`: if it splits and `discrim a b c = 0`, it
  has exactly one root;
* `Polynomial.splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero`: in characteristic two,
  where the discriminant degenerates to `b²` (`discrim_eq_sq_of_two_eq_zero`) and the square-class
  criterion says nothing, splits exactly when the
  Artin-Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`, written division-free.
  Here `b ≠ 0` is also required, which by `separable_quadratic_iff_discrim_ne_zero` is separability.

Three statements need neither a field nor `a ≠ 0`, and are stated over a commutative (semi)ring:
`Polynomial.derivative_quadratic`, computing the derivative as `2 a X + b`; the Bézout-type
`Polynomial.sq_derivative_quadratic_sub_mul_eq_C_discrim`, `(P')² - 4 a P = C (discrim a b c)`; and
its consequence `Polynomial.separable_quadratic_of_isUnit_discrim`, that the quadratic is separable
whenever its discriminant is a unit. Over a field that last statement is one direction of
`Polynomial.separable_quadratic_iff_discrim_ne_zero`, in every characteristic.

The two splitting criteria are consumed by the node-polynomial criteria of
`TauCeti/AlgebraicGeometry/EllipticCurve/NodePolynomial.lean`, which advance
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists): whether the node polynomial of a
multiplicative reduction splits over the residue field is exactly whether that reduction is split.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/Algebra/Polynomial/QuadraticDiscriminant.lean` at the roadmap's pin `bc2fe8ff7396`,
FLT PR #1088, Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`;
following this repository's convention for adapted material, the upstream authorship is credited
here rather than in the copyright header. Ported with the source's `@[expose]` dropped, and
without its companion `FLT/Mathlib/Algebra/Polynomial/Splits.lean`: that file's
`Splits.of_natDegree_le_two_of_isRoot` is superseded here by Mathlib's own
`Polynomial.Splits.of_natDegree_eq_two`, which the one consumer can use directly since it knows
the degree is exactly two.
-/

public section

/-- In characteristic two the discriminant degenerates to `b²`, since `4 = 0` kills the `a c`
term. This is why `splits_quadratic_iff_isSquare` says nothing there: `discrim a b c` is
automatically a square. -/
theorem discrim_eq_sq_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (a b c : R) :
    discrim a b c = b ^ 2 := by
  first
  | have h4 : (4 : R) = 0 := by linear_combination (2 : R) * h2
    rw [discrim]
    linear_combination -(a * c) * h4

namespace Polynomial

/-- The derivative of the quadratic `a X² + b X + c` is `2 a X + b`. -/
-- Deliberately not `@[simp]`: Mathlib's simp set already rewrites this left-hand side to
-- `C a * ((1 + 1) * X) + C b`, so the lemma is not in simp normal form and `simpNF` rejects it.
theorem derivative_quadratic {R : Type*} [CommSemiring R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) = 2 * C a * X + C b := by
  first
  | simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
      zero_mul, zero_add, mul_one, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one, map_ofNat]
    ring

/-- The Bézout-type identity `(P')² - 4 a · P = C (discrim a b c)` for the quadratic
`P = a X² + b X + c`: the discriminant is an explicit `R[X]`-combination of `P` and its
derivative, which is what makes it a coprimality witness in
`separable_quadratic_of_isUnit_discrim`. -/
theorem sq_derivative_quadratic_sub_mul_eq_C_discrim {R : Type*} [CommRing R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) ^ 2
      - 4 * C a * (C a * X ^ 2 + C b * X + C c) = C (discrim a b c) := by
  first
  | rw [derivative_quadratic, discrim]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring

/-- A quadratic `a X² + b X + c` over any commutative ring is separable as soon as `discrim a b c`
is a unit. No hypothesis on `a` is needed: once the discriminant is inverted, the Bézout-type
identity `sq_derivative_quadratic_sub_mul_eq_C_discrim` writes `1` as an `R[X]`-combination of the
polynomial and its derivative. -/
theorem separable_quadratic_of_isUnit_discrim {R : Type*} [CommRing R] {a b c : R}
    (h : IsUnit (discrim a b c)) : (C a * X ^ 2 + C b * X + C c).Separable := by
  first
  | set P := C a * X ^ 2 + C b * X + C c
    have hid : derivative P ^ 2 - 4 * C a * P = C (discrim a b c) :=
      sq_derivative_quadratic_sub_mul_eq_C_discrim a b c
    have hinv : C ((h.unit⁻¹ : Rˣ) : R) * C (discrim a b c) = 1 := by
      rw [← C_mul, h.val_inv_mul, C_1]
    rw [separable_def]
    exact ⟨-(C ((h.unit⁻¹ : Rˣ) : R) * 4 * C a), C ((h.unit⁻¹ : Rˣ) : R) * derivative P,
      by linear_combination C ((h.unit⁻¹ : Rˣ) : R) * hid + hinv⟩

/-- A quadratic polynomial `a X² + b X + c` (with `a ≠ 0`) over a field is separable exactly when
`discrim a b c` is nonzero. This holds in every characteristic; contrast
`splits_quadratic_iff_isSquare`, which asks for the discriminant to be a square rather than
nonzero, and only away from characteristic two. The reverse direction needs neither a field nor
`a ≠ 0`: it is `separable_quadratic_of_isUnit_discrim`. -/
theorem separable_quadratic_iff_discrim_ne_zero {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Separable ↔ discrim a b c ≠ 0 := by
  first
  | set P := C a * X ^ 2 + C b * X + C c with hP
    have hid : derivative P ^ 2 - 4 * C a * P = C (discrim a b c) :=
      sq_derivative_quadratic_sub_mul_eq_C_discrim a b c
    constructor
    · intro hsep hdisc
      rw [hdisc, map_zero] at hid
      have hdvd : P ∣ derivative P ^ 2 := ⟨4 * C a, by linear_combination hid⟩
      exact not_isUnit_of_natDegree_pos P (by rw [hP, natDegree_quadratic ha]; norm_num)
        (((separable_def P).mp hsep).pow_right.isUnit_of_dvd' dvd_rfl hdvd)
    · exact fun hdisc ↦ separable_quadratic_of_isUnit_discrim (isUnit_iff_ne_zero.mpr hdisc)

/-- A quadratic `a X² + b X + c` (`a ≠ 0`) over a field splits exactly when it has a root. This is
the characteristic-free core of the two split criteria below, which only restate "has a root":
`splits_quadratic_iff_isSquare` in terms of the discriminant, and
`splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero` in terms of the Artin-Schreier
invariant `a c / b²`. -/
theorem splits_quadratic_iff_exists_root {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ x, a * x ^ 2 + b * x + c = 0 := by
  first
  | set p := C a * X ^ 2 + C b * X + C c with hp
    have hdeg : p.natDegree = 2 := natDegree_quadratic ha
    constructor
    · intro hs
      obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by rw [hdeg]; norm_num))
      refine ⟨x, ?_⟩
      simp only [hp, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx
      linear_combination hx
    · rintro ⟨x, hx⟩
      refine Splits.of_natDegree_eq_two hdeg (x := x) ?_
      simp only [hp, eval_add, eval_mul, eval_pow, eval_C, eval_X]
      linear_combination hx

/-- Over a field of characteristic `≠ 2`, a quadratic `a X² + b X + c` (with `a ≠ 0`) *splits*
exactly when `discrim a b c` is a square. Compare `separable_quadratic_iff_discrim_ne_zero`,
which asks for the discriminant to be nonzero rather than square, and holds in every
characteristic. -/
theorem splits_quadratic_iff_isSquare {k : Type*} [Field k] [NeZero (2 : k)] {a b c : k}
    (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ IsSquare (discrim a b c) := by
  first
  | rw [splits_quadratic_iff_exists_root ha]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨2 * a * x + b, by rw [discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c)
        (x := x) (by linear_combination hx)]; ring⟩
    · rintro ⟨s, hs⟩
      obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, by rw [hs]⟩
      exact ⟨x, by linear_combination hx⟩

/-- Over a field of characteristic `2`, a quadratic `a X² + b X + c` with `a, b ≠ 0` splits
exactly when its Artin-Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`, written
division-free as `∃ z, b² (z² + z) = a c`. Here the square-class criterion
`splits_quadratic_iff_isSquare` says nothing, since `discrim a b c = b²` is automatically a
square; the hypothesis `b ≠ 0` is
exactly separability, by `separable_quadratic_iff_discrim_ne_zero`. -/
theorem splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero {k : Type*} [Field k]
    (h2 : (2 : k) = 0) {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ z, b ^ 2 * (z ^ 2 + z) = a * c := by
  first
  | rw [splits_quadratic_iff_exists_root ha]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨a * x / b, ?_⟩
      field_simp
      linear_combination hx - c * h2
    · rintro ⟨z, hz⟩
      refine ⟨b * z / a, ?_⟩
      field_simp
      linear_combination hz + a * c * h2

/-- Over a perfect field, a quadratic `a X² + b X + c` (with `a ≠ 0`) whose discriminant vanishes
splits. Perfectness is needed in characteristic two, where `X² - c` can have vanishing
discriminant without a root. -/
theorem splits_quadratic_of_discrim_eq_zero {k : Type*} [Field k] [PerfectField k] {a b c : k}
    (ha : a ≠ 0) (hd : discrim a b c = 0) : (C a * X ^ 2 + C b * X + C c).Splits := by
  first
  | set p := C a * X ^ 2 + C b * X + C c
    have hdeg : p.natDegree = 2 := natDegree_quadratic ha
    have hsep : ¬ p.Separable := by
      rw [separable_quadratic_iff_discrim_ne_zero ha, not_not]
      exact hd
    have hroots : p.roots ≠ 0 := fun h0 ↦ hsep (PerfectField.separable_of_irreducible
      ((irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).2 h0))
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hroots
    exact Splits.of_natDegree_eq_two hdeg (mem_roots'.1 hx).2

/-- Over a perfect field, a quadratic `a X² + b X + c` (with `a ≠ 0`) whose discriminant vanishes
has a double root: some `x` is a root of the quadratic and of its derivative `2 a X + b`. Away from
characteristic two this is `x = -b / (2 a)`; in characteristic two `b = 0` and `x` is the square
root of `c / a`, which is where perfectness is needed. -/
theorem exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero {k : Type*} [Field k]
    [PerfectField k] {a b c : k} (ha : a ≠ 0) (hd : discrim a b c = 0) :
    ∃ x, a * x ^ 2 + b * x + c = 0 ∧ 2 * a * x + b = 0 := by
  first
  | obtain ⟨x, hx⟩ := (splits_quadratic_iff_exists_root ha).1
      (splits_quadratic_of_discrim_eq_zero ha hd)
    refine ⟨x, hx, pow_eq_zero_iff two_ne_zero |>.1 ?_⟩
    rw [← discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c) (by linear_combination hx),
      hd]

/-- A split quadratic `a X² + b X + c` (with `a ≠ 0`) whose discriminant vanishes has exactly one
root. -/
theorem card_rootSet_quadratic_of_discrim_eq_zero {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0)
    (hs : (C a * X ^ 2 + C b * X + C c).Splits) (hd : discrim a b c = 0) :
    Fintype.card ((C a * X ^ 2 + C b * X + C c).rootSet k) = 1 := by
  first
  | set p := C a * X ^ 2 + C b * X + C c
    have hdeg : p.natDegree = 2 := natDegree_quadratic ha
    have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
    have hs' : (p.map (algebraMap k k)).Splits := by rwa [Algebra.algebraMap_self, map_id]
    have hne : Fintype.card (p.rootSet k) ≠ 2 := by
      rw [← hdeg, Ne, card_rootSet_eq_natDegree_iff_of_splits hp0 hs',
        separable_quadratic_iff_discrim_ne_zero ha, not_not]
      exact hd
    have hle : Fintype.card (p.rootSet k) ≤ 2 := by
      rw [← hdeg, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact ncard_rootSet_le p k
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (by rw [degree_eq_natDegree hp0, hdeg]; decide)
    have hpos : 0 < Fintype.card (p.rootSet k) :=
      Fintype.card_pos_iff.2 ⟨⟨x, mem_rootSet.2 ⟨hp0, by simpa using hx⟩⟩⟩
    omega

end Polynomial

namespace TauCeti

open _root_.Polynomial

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A quadratic with negative discriminant is positive at every argument exactly when its
leading coefficient is positive. -/
theorem quadratic_pos_iff_of_discrim_neg {a b c : R} (hd : discrim a b c < 0) (x : R) :
    0 < (C a * X ^ 2 + C b * X + C c).eval x ↔ 0 < a := by
  first
  | simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    have ha0 : a ≠ 0 := by
      intro ha
      subst a
      simp only [discrim, zero_mul, mul_zero, sub_zero] at hd
      nlinarith [sq_nonneg b]
    have hsq : ∀ s : R, discrim a b c ≠ s ^ 2 := by
      intro s hs
      exact (not_le.mpr hd) (by rw [hs]; exact sq_nonneg s)
    have hne : a * x ^ 2 + b * x + c ≠ 0 := by
      simpa only [sq] using quadratic_ne_zero_of_discrim_ne_sq hsq x
    constructor
    · intro hx
      rcases lt_or_gt_of_ne ha0 with ha | ha
      · have hnonneg := nonneg_of_discrim_le_zero (a := -a) (b := -b) (c := -c)
          (by simpa only [neg_pos] using ha)
          (by simpa only [discrim_neg] using hd.le) x 1
        simp only [one_pow, mul_one] at hnonneg
        nlinarith
      · exact ha
    · intro ha
      have hnonneg := nonneg_of_discrim_le_zero ha hd.le x 1
      simp only [one_pow, mul_one] at hnonneg
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- With negative discriminant, a quadratic is negative everywhere exactly when its
leading coefficient is negative. -/
theorem quadratic_neg_iff_of_discrim_neg {a b c : R} (hd : discrim a b c < 0) (x : R) :
    (C a * X ^ 2 + C b * X + C c).eval x < 0 ↔ a < 0 := by
  first
  | have h := quadratic_pos_iff_of_discrim_neg (a := -a) (b := -b) (c := -c)
      (by simpa only [discrim_neg] using hd) x
    have heq : (C (-a) * X ^ 2 + C (-b) * X + C (-c)).eval x =
        -(C a * X ^ 2 + C b * X + C c).eval x := by
      simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
      ring
    simpa only [heq, neg_pos] using h

end TauCeti

end
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/RealClosed/Quadratic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-! # Signs of irreducible quadratics over real closed fields

An irreducible quadratic over an ordered real closed field has negative discriminant.
Its value is therefore everywhere nonzero and has the sign of its leading coefficient.
The discriminant criterion also gives the converse characterization of irreducibility.
These facts supply the quadratic case of the algebraic polynomial intermediate value theorem.

The general sign calculation in `TauCeti.Algebra.Polynomial.QuadraticDiscriminant` only
requires an ordered ring; real closedness is used to turn a nonnegative discriminant into a
square. The quadratic discriminant and root criteria are those of
`Mathlib.Algebra.QuadraticDiscriminant`.
-/

public section

namespace TauCeti

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

variable [IsRealClosed R]

/-- A genuine quadratic over a real closed field is irreducible exactly when its
discriminant is negative. -/
@[simp]
theorem irreducible_quadratic_iff_discrim_neg {a b c : R} (ha : a ≠ 0) :
    Irreducible (C a * X ^ 2 + C b * X + C c) ↔ discrim a b c < 0 := by
  first
  | let p : R[X] := C a * X ^ 2 + C b * X + C c
    have hdeg : p.natDegree = 2 := natDegree_quadratic ha
    constructor
    · intro hi
      by_contra hn
      have hd : 0 ≤ discrim a b c := le_of_not_gt hn
      obtain ⟨s, hs⟩ := (IsRealClosed.nonneg_iff_isSquare.mp hd)
      obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, hs⟩
      have hroot : p.IsRoot x := by
        simp only [p, IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X]
        nlinarith [hx]
      exact (hi.not_isRoot_of_natDegree_ne_one (by rw [hdeg]; decide)) hroot
    · intro hd
      have hnot : ∀ x, ¬ p.IsRoot x := by
        intro x
        have hsq : ∀ s : R, discrim a b c ≠ s ^ 2 := by
          intro s hs
          exact (not_le.mpr hd) (by rw [hs]; exact sq_nonneg s)
        simpa only [p, IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, sq] using
          quadratic_ne_zero_of_discrim_ne_sq hsq x
      exact irreducible_of_degree_le_three_of_not_isRoot (p := p)
        (by rw [Finset.mem_Icc, hdeg]; decide) hnot

/-- Positivity of the value of an irreducible quadratic over a real closed field is equivalent
to positivity of its leading coefficient. -/
theorem irreducible_quadratic_eval_pos_iff {a b c : R} (ha : a ≠ 0)
    (hi : Irreducible (C a * X ^ 2 + C b * X + C c)) (x : R) :
    0 < (C a * X ^ 2 + C b * X + C c).eval x ↔ 0 < a := by
  first
  | exact quadratic_pos_iff_of_discrim_neg ((irreducible_quadratic_iff_discrim_neg ha).mp hi) x

/-- The negative-sign counterpart of `irreducible_quadratic_eval_pos_iff`. -/
theorem irreducible_quadratic_eval_neg_iff {a b c : R} (ha : a ≠ 0)
    (hi : Irreducible (C a * X ^ 2 + C b * X + C c)) (x : R) :
    (C a * X ^ 2 + C b * X + C c).eval x < 0 ↔ a < 0 := by
  first
  | exact quadratic_neg_iff_of_discrim_neg ((irreducible_quadratic_iff_discrim_neg ha).mp hi) x

/-- The value of an irreducible polynomial of degree two is positive exactly when its leading
coefficient is positive. This form does not require a coefficient presentation. -/
@[simp]
theorem irreducible_quadratic_eval_pos_iff_leadingCoeff_pos {p : R[X]} (hi : Irreducible p)
    (hdeg : p.natDegree = 2) (x : R) : 0 < p.eval x ↔ 0 < p.leadingCoeff := by
  first
  | have hrepr := eq_quadratic_of_degree_le_two (p := p) (degree_le_of_natDegree_le hdeg.le)
    have ha : p.coeff 2 ≠ 0 := by
      simpa only [leadingCoeff, hdeg] using (leadingCoeff_ne_zero.mpr hi.ne_zero)
    have h := irreducible_quadratic_eval_pos_iff ha (hrepr ▸ hi) x
    rw [← hrepr] at h
    simpa only [leadingCoeff, hdeg] using h

/-- The negative-sign form for an arbitrary irreducible quadratic. -/
@[simp]
theorem irreducible_quadratic_eval_neg_iff_leadingCoeff_neg {p : R[X]} (hi : Irreducible p)
    (hdeg : p.natDegree = 2) (x : R) : p.eval x < 0 ↔ p.leadingCoeff < 0 := by
  first
  | have hrepr := eq_quadratic_of_degree_le_two (p := p) (degree_le_of_natDegree_le hdeg.le)
    have ha : p.coeff 2 ≠ 0 := by
      simpa only [leadingCoeff, hdeg] using (leadingCoeff_ne_zero.mpr hi.ne_zero)
    have h := irreducible_quadratic_eval_neg_iff ha (hrepr ▸ hi) x
    rw [← hrepr] at h
    simpa only [leadingCoeff, hdeg] using h

/-- An irreducible quadratic has the same nonzero sign at any two points. -/
theorem irreducible_quadratic_eval_mul_pos {p : R[X]} (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (a b : R) : 0 < p.eval a * p.eval b := by
  first
  | rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp.ne_zero) with h | h
    · exact mul_pos_of_neg_of_neg
        ((irreducible_quadratic_eval_neg_iff_leadingCoeff_neg hp hdeg a).mpr h)
        ((irreducible_quadratic_eval_neg_iff_leadingCoeff_neg hp hdeg b).mpr h)
    · exact mul_pos ((irreducible_quadratic_eval_pos_iff_leadingCoeff_pos hp hdeg a).mpr h)
        ((irreducible_quadratic_eval_pos_iff_leadingCoeff_pos hp hdeg b).mpr h)

end TauCeti
end -- closes the original EOF section from source line 28
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/RealClosed/Quadratic.lean -/

/- BEGIN SOURCE: TauCeti/FieldTheory/RealClosure/IVT.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Polynomial intermediate values over an abstract real closed field

The polynomial API gives roots from strict or weak endpoint sign changes and both
orientations of closed-interval image inclusion. `Polynomial.eval_mul_pos_of_no_roots`
is the constant-sign result used by polynomial Rolle.

Irreducible factors have degree at most two; quadratic factors have constant
nonzero sign, so a sign change forces a root of a linear factor.

## References

Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Corollaries 3.1 and 3.2.
-/

public section

namespace TauCeti.RealClosure

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A polynomial has constant nonzero sign on any closed interval containing
none of its roots. -/
theorem _root_.Polynomial.eval_mul_pos_of_no_roots (p : R[X]) {a b : R} (hab : a ≤ b)
    (hroot : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) : 0 < p.eval a * p.eval b := by
  first
  | revert hroot
    induction p using WfDvdMonoid.induction_on_irreducible with
    | zero =>
      intro hroot
      exact (hroot a ⟨le_rfl, hab⟩ (by simp)).elim
    | unit p hp =>
      intro hroot
      have heq := eq_C_of_degree_eq_zero (isUnit_iff_degree_eq_zero.mp hp)
      have hsame : p.eval b = p.eval a := by rw [heq]; simp
      rw [hsame]
      exact mul_self_pos.mpr (hroot a ⟨le_rfl, hab⟩)
    | mul p q _ hq ih =>
      intro hroot
      have hp' : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0 := by
        intro x hx hp
        apply hroot x hx
        simp [hp]
      have hq' : ∀ x ∈ Set.Icc a b, q.eval x ≠ 0 := by
        intro x hx hq
        apply hroot x hx
        simp [hq]
      have hdeg : q.natDegree = 1 ∨ q.natDegree = 2 := by
        have := q.natDegree_le_two_of_irreducible hq
        have := hq.natDegree_pos
        omega
      have hqpos : 0 < q.eval a * q.eval b := hdeg.elim
        (fun h => eval_mul_pos_of_natDegree_le_one_of_no_roots h.le hab hq')
        (fun h => irreducible_quadratic_eval_mul_pos hq h a b)
      simpa only [eval_mul, mul_mul_mul_comm] using mul_pos hqpos (ih hp')

/-- A nonpositive product of endpoint values gives a root on the closed interval. -/
theorem _root_.Polynomial.exists_root_Icc_of_mul_nonpos (p : R[X]) {a b : R} (hab : a ≤ b)
    (h : p.eval a * p.eval b ≤ 0) : ∃ c ∈ Set.Icc a b, p.eval c = 0 := by
  first
  | by_contra! hroot
    exact not_le_of_gt (eval_mul_pos_of_no_roots p hab hroot) h

/-- Weakly opposite endpoint signs give a root on the closed interval. -/
theorem _root_.Polynomial.exists_root_Icc (p : R[X]) {a b : R} (hab : a ≤ b)
    (ha : p.eval a ≤ 0) (hb : 0 ≤ p.eval b) :
    ∃ c ∈ Set.Icc a b, p.eval c = 0 :=
  exists_root_Icc_of_mul_nonpos p hab (mul_nonpos_of_nonpos_of_nonneg ha hb)

/-- Polynomial IVT over an arbitrary real closed ordered field, including
non-Archimedean fields. -/
theorem _root_.Polynomial.exists_root_Ioo (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  first
  | obtain ⟨c, ⟨hac, hcb⟩, hc⟩ := exists_root_Icc p hab.le ha.le hb.le
    refine ⟨c, ⟨hac.lt_of_ne ?_, hcb.lt_of_ne ?_⟩, hc⟩
    · rintro rfl
      exact ha.ne hc
    · rintro rfl
      exact hb.ne' hc

/-- The symmetric sign-change form of polynomial IVT. -/
theorem _root_.Polynomial.exists_root_Ioo_of_mul_neg (p : R[X]) {a b : R} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  first
  | rcases mul_neg_iff.mp h with h | h
    · obtain ⟨c, hc, he⟩ := exists_root_Ioo (-p) hab (by simpa using h.1) (by simpa using h.2)
      exact ⟨c, hc, by simpa using he⟩
    · exact exists_root_Ioo p hab h.1 h.2

/-- Polynomial intermediate value on a closed interval, for `p.eval a ≤ y ≤ p.eval b`. -/
theorem _root_.Polynomial.intermediate_value_Icc (p : R[X]) {a b : R} (hab : a ≤ b) :
    Set.Icc (p.eval a) (p.eval b) ⊆ p.eval '' Set.Icc a b := by
  first
  | rintro y ⟨hay, hyb⟩
    obtain ⟨c, hc, he⟩ := exists_root_Icc (p - C y) hab
      (by simpa using sub_nonpos.mpr hay) (by simpa using sub_nonneg.mpr hyb)
    exact ⟨c, hc, by simpa only [eval_sub, eval_C, sub_eq_zero] using he⟩

/-- Polynomial intermediate value on a closed interval, for `p.eval b ≤ y ≤ p.eval a`. -/
theorem _root_.Polynomial.intermediate_value_Icc' (p : R[X]) {a b : R} (hab : a ≤ b) :
    Set.Icc (p.eval b) (p.eval a) ⊆ p.eval '' Set.Icc a b := by
  first
  | rintro y ⟨hby, hya⟩
    obtain ⟨c, hc, he⟩ := exists_root_Icc (C y - p) hab
      (by simpa using sub_nonpos.mpr hya) (by simpa using sub_nonneg.mpr hby)
    exact ⟨c, hc, (by simpa only [eval_sub, eval_C, sub_eq_zero] using he : y = p.eval c).symm⟩

end TauCeti.RealClosure
end -- closes the original EOF section from source line 28
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/FieldTheory/RealClosure/IVT.lean -/

/- BEGIN SOURCE: TauCeti/FieldTheory/RealClosure/AbstractRolle.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Polynomial Rolle over an abstract real closed field

`polynomialRolle_of_isRealClosed` supplies `TauCeti.PolynomialRolle R` from `IsRealClosed R`.
The direct `Polynomial.exists_derivative_root` and
`Polynomial.exists_eval_sub_eq_derivative_eval_mul` give Rolle and mean value without a separate
Rolle premise. The four `Polynomial.*On_of_derivative_*` theorems give monotonicity,
antitonicity, and their strict variants on closed intervals. Under `IsRealClosed`, use these
direct statements; `TauCeti.Algebra.Polynomial.Rolle` instead derives the same consequences
from an explicit polynomial Rolle hypothesis over a general ordered field.

Between consecutive roots, removing their multiplicities leaves a polynomial
of constant nonzero sign. A factor of the derivative has opposite signs at
the endpoints, so polynomial IVT supplies the required critical point.

## References

Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 6](https://www.math.uni-konstanz.de/algebra/WS0910/Notes06.pdf),
Corollary 2.2.
-/

public section

namespace TauCeti.RealClosure

open _root_.Polynomial Set

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Rolle between consecutive distinct roots, allowing arbitrary endpoint multiplicities. -/
private theorem exists_derivative_root_of_consecutive (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hroot : ∀ x ∈ Ioo a b, p.eval x ≠ 0) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := by
  first
  | have hp : p ≠ 0 := by
      intro h
      obtain ⟨c, hc⟩ := exists_between hab
      exact hroot c hc (by simp [h])
    obtain ⟨m, q, hpq, hqa⟩ := IsRoot.exists_eq_pow_succ_mul ha hp
    have hq0 : q ≠ 0 := by intro h; exact hqa (by simp [h])
    have hqb : q.eval b = 0 := by
      rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hb
      exact (mul_eq_zero.mp hb).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hab.ne'))
    obtain ⟨n, r, hqr, hrb⟩ := IsRoot.exists_eq_pow_succ_mul hqb hq0
    have hra : r.eval a ≠ 0 := by
      intro h
      apply hqa
      rw [hqr]
      simp [h]
    have hrr : ∀ x ∈ Icc a b, r.eval x ≠ 0 := by
      intro x hx
      rcases hx.1.eq_or_lt with rfl | hax
      · exact hra
      rcases hx.2.eq_or_lt with rfl | hxb
      · exact hrb
      intro h
      apply hroot x ⟨hax, hxb⟩
      rw [hpq, hqr]
      simp [h]
    -- Removing `(X - C a) ^ m * (X - C b) ^ n` from the derivative leaves the factor `d`.
    let d : R[X] := C ((m : R) + 1) * (X - C b) * r +
      C ((n : R) + 1) * (X - C a) * r + (X - C a) * (X - C b) * r.derivative
    have hderiv : p.derivative = (X - C a) ^ m * (X - C b) ^ n * d := by
      rw [hpq, hqr]
      exact derivative_root_factors a b m n r
    have hda : d.eval a = ((m : R) + 1) * (a - b) * r.eval a := by simp [d]
    have hdb : d.eval b = ((n : R) + 1) * (b - a) * r.eval b := by simp [d]
    have hm : 0 < (m : R) + 1 := by positivity
    have hn : 0 < (n : R) + 1 := by positivity
    have hsign : d.eval a * d.eval b < 0 := by
      rw [hda, hdb]
      have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hab) (sub_pos.mpr hab)
      have hpos := eval_mul_pos_of_no_roots r hab.le hrr
      convert mul_neg_of_pos_of_neg (mul_pos hm hn) (mul_neg_of_neg_of_pos hneg hpos) using 1
      ring
    obtain ⟨c, hc, hd⟩ := exists_root_Ioo_of_mul_neg d hab hsign
    exact ⟨c, hc, by rw [hderiv]; simp [hd]⟩

/-- Between any two distinct roots there is a root of the formal derivative. -/
theorem _root_.Polynomial.exists_derivative_root_of_isRoot (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := by
  first
  | classical
    by_cases hp : p = 0
    · obtain ⟨c, hac, hcb⟩ := exists_between hab
      exact ⟨c, ⟨hac, hcb⟩, by simp [hp]⟩
    have hbmem : b ∈ p.roots.toFinset := by simpa [mem_roots hp] using hb
    obtain ⟨b', hb'mem, hab', hnext⟩ :=
      Finset.exists_next_right (s := p.roots.toFinset) ⟨b, hbmem, hab⟩
    have hb' : p.eval b' = 0 := by simpa [mem_roots hp] using hb'mem
    have hb'b : b' ≤ b := hnext b hbmem hab
    have hroot : ∀ x ∈ Ioo a b', p.eval x ≠ 0 := by
      intro x hx hz
      have hmem : x ∈ p.roots.toFinset := by simpa [mem_roots hp] using hz
      exact hx.2.not_ge (hnext x hmem hx.1)
    obtain ⟨c, hc, hd⟩ := exists_derivative_root_of_consecutive p hab' ha hb' hroot
    exact ⟨c, ⟨hc.1, hc.2.trans_le hb'b⟩, hd⟩

/-- Polynomial Rolle follows from the abstract real-closed-field axioms. -/
theorem polynomialRolle_of_isRealClosed : PolynomialRolle R := by
  first
  | apply PolynomialRolle.of_forall
    intro p a b hab heq
    obtain ⟨c, hc, hd⟩ := exists_derivative_root_of_isRoot (p - C (p.eval a)) hab
      (by simp) (by simp [heq])
    exact ⟨c, hc, by simpa using hd⟩

/-- Equal endpoint values give an interior derivative root over a real closed field. -/
theorem _root_.Polynomial.exists_derivative_root (p : R[X]) {a b : R}
    (hab : a < b) (h : p.eval a = p.eval b) : ∃ c ∈ Ioo a b, p.derivative.eval c = 0 :=
  polynomialRolle_of_isRealClosed.exists_derivative_root p hab h

/-- Polynomial mean value over an ordered real closed field. -/
theorem _root_.Polynomial.exists_eval_sub_eq_derivative_eval_mul (p : R[X]) {a b : R}
    (hab : a < b) :
    ∃ c ∈ Ioo a b, p.eval b - p.eval a = p.derivative.eval c * (b - a) :=
  polynomialRolle_of_isRealClosed.exists_eval_sub_eq_derivative_eval_mul p hab

/-- A nonnegative formal derivative makes polynomial evaluation monotone on an interval. -/
theorem _root_.Polynomial.monotoneOn_of_derivative_nonneg (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.monotoneOn p hd

/-- A nonpositive formal derivative makes polynomial evaluation antitone on an interval. -/
theorem _root_.Polynomial.antitoneOn_of_derivative_nonpos (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x ≤ 0) : AntitoneOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.antitoneOn p hd

/-- A positive formal derivative makes polynomial evaluation strictly monotone on an interval. -/
theorem _root_.Polynomial.strictMonoOn_of_derivative_pos (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.strictMonoOn p hd

/-- A negative formal derivative makes polynomial evaluation strictly antitone on an interval. -/
theorem _root_.Polynomial.strictAntiOn_of_derivative_neg (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0) : StrictAntiOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.strictAntiOn p hd

end TauCeti.RealClosure
end -- closes the original EOF section from source line 37
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/FieldTheory/RealClosure/AbstractRolle.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Delineation.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Delineations of families of real polynomials

Let `P k x`, for `k` in an index type `ι`, be real polynomials depending on a parameter `x` in a
base `X`. A *delineation* of `P` is a common stack for the whole family: finitely many
continuous functions `θ₀ < θ₁ < ⋯ < θₘ₋₁` on `X` such that

* each member is either the zero polynomial at every point of the base or at none, and has the
  same degree at every point;
* at every point, the roots of every nonzero member are among the values `θᵢ x`, every `θᵢ x` is
  a root of some member, and the multiplicity of `θᵢ x` as a root of `P k x` does not depend on
  `x`;
* every member is sign-invariant on each section and each sector of the stack.

This is the conclusion of Collins' delineability theorem, the step that lifts a cylindrical
algebraic decomposition by one dimension.

Over a nonempty base the ordered list of root functions of a delineation is the increasing
enumeration of the real roots of the nonzero members, so a delineation is unique. Delineations
restrict along continuous maps of bases.

The main theorem `TauCeti.nonempty_delineation` constructs a delineation over a preconnected base
from invariant algebraic data: if the coefficients of every member are continuous, every member is
nullified everywhere or nowhere, and the degree of every member, its number of distinct complex
roots and the degree of the gcd of every pair of distinct members are constant on the base, then
the family has a delineation. Its root functions are the common ordered real roots given by the
family matching lemma `Polynomial.exists_continuous_ordered_common_roots_of_preconnectedSpace`.

When the derivative of every member is zero or a member, Thom's lemma shows that two points of
one fiber at which all members have the same signs lie in the same section or sector. So the cells
of the stack are cut out by sign conditions on the members.

For a family obtained from polynomials `f` in `n + 1` variables by singling out the first one with
`MvPolynomial.finSuccEquiv`, every `f` is sign-invariant on each cell of the stack in
`ℝ^(n + 1)`, the cells being the images of the sections and sectors under `TauCeti.cylinder`.

## Main declarations

* `TauCeti.Delineation`: a common stack of the roots of a family of real polynomials.
* `TauCeti.Delineation.range_root`: the root functions enumerate the real roots of the nonzero
  members.
* `TauCeti.Delineation.isRoot_iff`: the roots of a nonzero member are the sections in which it has
  positive multiplicity.
* `TauCeti.Delineation.instSubsingleton`: over a nonempty base a family has at most one
  delineation.
* `TauCeti.Delineation.comp`: restriction of a delineation along a continuous map of bases.
* `TauCeti.nonempty_delineation`: existence of a delineation over a preconnected base from
  constant degrees, numbers of distinct complex roots and pairwise gcd degrees.
* `TauCeti.exists_delineation_of_isRoot_iff`: an ordered continuous enumeration of the real roots
  of a single nowhere-zero family, with constant multiplicities, is a delineation.
* `TauCeti.exists_delineation_ball_of_isRoot_iff`: the local version on a ball in a real normed
  space, for families that are nonzero, of constant degree and with continuous coefficients near
  the center.
* `TauCeti.Delineation.root_notMem_uIcc_of_sign_eval_eq`,
  `TauCeti.Delineation.mk_mem_sectionSet_iff_of_sign_eval_eq`,
  `TauCeti.Delineation.mk_mem_sectorSet_iff_of_sign_eval_eq`: when the derivative of every
  member is zero or a member, points of one fiber with the same signs are not separated by the
  stack.
* `TauCeti.Delineation.signInvariant_eval₂_of_mem_stackCells`: the polynomials in `n + 1`
  variables behind a family are sign-invariant on every ambient cell of a delineation.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 (Theorem 5.16).
-/

public section

open Function Polynomial Set

namespace TauCeti

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P : ι → X → ℝ[X]}

/-- A *delineation* of a family `P k x` of real polynomials over a base `X` is a common stack of
their roots: continuous functions `root 0 < ⋯ < root (count - 1)` on `X` such that each member is
zero everywhere or nowhere and has constant degree, the roots of each nonzero member are among
the `root i x`, each `root i` is a root of some member, the multiplicity of `root i x` as a root of
`P k x` is a constant `multiplicity k i`, and each member is sign-invariant on every section and
every sector of the stack. -/
structure Delineation (P : ι → X → ℝ[X]) where
  /-- The number of sections of the stack. -/
  count : ℕ
  /-- The root functions, listed in increasing order. -/
  root : Fin count → X → ℝ
  /-- Each root function is continuous. -/
  continuous_root (i : Fin count) : Continuous (root i)
  /-- At each point the root functions are strictly increasing in their index. -/
  strictMono_root (x : X) : StrictMono fun i ↦ root i x
  /-- The multiplicity of the `i`-th root function as a root of the `k`-th member. -/
  multiplicity : ι → Fin count → ℕ
  /-- The multiplicity of `root i x` as a root of `P k x` is `multiplicity k i` at every `x`. -/
  rootMultiplicity_root (k : ι) (i : Fin count) (x : X) :
    (P k x).rootMultiplicity (root i x) = multiplicity k i
  /-- Every root of a nonzero member is the value of a root function. -/
  exists_root_eq (k : ι) (x : X) : P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, root i x = t
  /-- Every root function is a root of some member. -/
  exists_multiplicity_pos (i : Fin count) : ∃ k, 0 < multiplicity k i
  /-- Each member is the zero polynomial at every point or at none. -/
  eq_zero_or_ne_zero (k : ι) : (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0
  /-- Each member has the same degree at every point. -/
  natDegree_eq (k : ι) (x y : X) : (P k x).natDegree = (P k y).natDegree
  /-- Each member is sign-invariant on each section. -/
  signInvariant_sectionSet (k : ι) (i : Fin count) :
    SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectionSet root i)
  /-- Each member is sign-invariant on each sector. -/
  signInvariant_sectorSet (k : ι) (j : Fin (count + 1)) :
    SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectorSet root j)

namespace Delineation

/-- Construct a delineation from continuous ordered roots with specified constant
multiplicities. The roots must cover every nonzero member, and each section must have
positive multiplicity in some member. On a preconnected base these data imply
sign-invariance on all sections and sectors. -/
def ofRoots [PreconnectedSpace X] {n : ℕ} {θ : Fin n → X → ℝ} {m : ι → Fin n → ℕ}
    (hcoeff : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
    (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
    (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
    (hθ : ∀ i, Continuous (θ i)) (hmono : ∀ x, StrictMono fun i ↦ θ i x)
    (hmult : ∀ k i x, (P k x).rootMultiplicity (θ i x) = m k i)
    (hroots : ∀ k x, P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, θ i x = t)
    (hpos : ∀ i, ∃ k, 0 < m k i) : Delineation P := by
  first
  | have hP (k : ι) : Continuous fun z : X × ℝ ↦ (P k z.1).eval z.2 := by
      rcases isEmpty_or_nonempty X with hX | hX
      · exact continuous_of_const fun z ↦ isEmptyElim z.1
      · obtain ⟨x₀⟩ := hX
        exact continuous_eval_of_continuous_coeff (fun j _ ↦ hcoeff k j)
          fun x ↦ (hdeg k x x₀).le
    exact {
      count := n
      root := θ
      continuous_root := hθ
      strictMono_root := hmono
      multiplicity := m
      rootMultiplicity_root := hmult
      exists_root_eq := hroots
      exists_multiplicity_pos := hpos
      eq_zero_or_ne_zero := hnull
      natDegree_eq := hdeg
      signInvariant_sectionSet := fun k i ↦ signInvariant_eval_sectionSet
        (I := {i | 0 < m k i}) (hP k) (hθ i) (fun x ↦ (hmono x).injective) (hnull k)
        fun x hk t ↦ (isRoot_iff_of_rootMultiplicity (fun i ↦ hmult k i x)
          (hroots k x hk) hk t).trans (by simp only [mem_ofPred_eq, and_comm])
      signInvariant_sectorSet := fun k _ ↦
        signInvariant_eval_sectorSet (hP k) hθ hmono (hnull k) fun x hk ↦ hroots k x hk }

section

variable [PreconnectedSpace X] {n : ℕ} {θ : Fin n → X → ℝ} {m : ι → Fin n → ℕ}
  (hcoeff : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
  (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
  (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
  (hθ : ∀ i, Continuous (θ i)) (hmono : ∀ x, StrictMono fun i ↦ θ i x)
  (hmult : ∀ k i x, (P k x).rootMultiplicity (θ i x) = m k i)
  (hroots : ∀ k x, P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, θ i x = t)
  (hpos : ∀ i, ∃ k, 0 < m k i)

/-- The delineation constructed from ordered roots has the specified number of sections. -/
@[simp]
theorem ofRoots_count :
    (ofRoots hcoeff hnull hdeg hθ hmono hmult hroots hpos).count = n := (rfl)

/-- The delineation constructed from ordered roots has the specified root functions. -/
@[simp]
theorem ofRoots_root
    (i : Fin (ofRoots hcoeff hnull hdeg hθ hmono hmult hroots hpos).count) (x : X) :
    (ofRoots hcoeff hnull hdeg hθ hmono hmult hroots hpos).root i x =
      θ (Fin.cast (ofRoots_count hcoeff hnull hdeg hθ hmono hmult hroots hpos) i) x := (rfl)

/-- The delineation constructed from ordered roots has the specified multiplicities. -/
@[simp]
theorem ofRoots_multiplicity (k : ι)
    (i : Fin (ofRoots hcoeff hnull hdeg hθ hmono hmult hroots hpos).count) :
    (ofRoots hcoeff hnull hdeg hθ hmono hmult hroots hpos).multiplicity k i =
      m k (Fin.cast (ofRoots_count hcoeff hnull hdeg hθ hmono hmult hroots hpos) i) := (rfl)

end

/-- Any family of real polynomials over an empty base has a delineation. -/
theorem nonempty_of_isEmpty [IsEmpty X] (P : ι → X → ℝ[X]) : Nonempty (Delineation P) :=
  ⟨{
    count := 0
    root := Fin.elim0
    continuous_root := fun i ↦ i.elim0
    strictMono_root := fun x ↦ isEmptyElim x
    multiplicity := fun _ ↦ Fin.elim0
    rootMultiplicity_root := fun _ i ↦ i.elim0
    exists_root_eq := fun _ x ↦ isEmptyElim x
    exists_multiplicity_pos := fun i ↦ i.elim0
    eq_zero_or_ne_zero := fun _ ↦ .inl isEmptyElim
    natDegree_eq := fun _ x ↦ isEmptyElim x
    signInvariant_sectionSet := fun _ i ↦ i.elim0
    signInvariant_sectorSet := fun _ _ ↦ subsingleton_of_subsingleton.signInvariant }⟩

variable (D : Delineation P)

/-- The roots of a nonzero member of the family are exactly the values of the root functions in
which it has positive multiplicity. -/
theorem isRoot_iff {k : ι} {x : X} (hk : P k x ≠ 0) (t : ℝ) :
    (P k x).IsRoot t ↔ ∃ i, D.root i x = t ∧ 0 < D.multiplicity k i :=
  isRoot_iff_of_rootMultiplicity (fun i ↦ D.rootMultiplicity_root k i x)
    (D.exists_root_eq k x hk) hk t

/-- On a sector, the evaluation of a nonzero fiber cannot vanish: every root lies
on a section, and sections are disjoint from sectors. -/
theorem eval_ne_zero_of_mem_sectorSet {k : ι} {j : Fin (D.count + 1)} {z : X × ℝ}
    (hk : P k z.1 ≠ 0) (hz : z ∈ sectorSet D.root j) : (P k z.1).eval z.2 ≠ 0 := by
  first
  | intro hzero
    obtain ⟨i, hi⟩ := D.exists_root_eq k z.1 hk z.2 hzero
    exact disjoint_left.1 (disjoint_sectionSet_sectorSet D.root i j)
      (mem_sectionSet.2 hi) hz

/-- A member of the family has positive multiplicity in a root function exactly when it is
nonzero and vanishes there. -/
theorem multiplicity_pos_iff {k : ι} {i : Fin D.count} (x : X) :
    0 < D.multiplicity k i ↔ P k x ≠ 0 ∧ (P k x).IsRoot (D.root i x) := by
  first
  | rw [← D.rootMultiplicity_root k i x, rootMultiplicity_pos']

/-- A member of the family that is zero somewhere has multiplicity zero in every root function. -/
theorem multiplicity_eq_zero {k : ι} {x : X} (hk : P k x = 0) (i : Fin D.count) :
    D.multiplicity k i = 0 := by
  first
  | rw [← D.rootMultiplicity_root k i x, hk, rootMultiplicity_zero]

/-- At every point of the base, the values of the root functions are exactly the real roots of
the nonzero members of the family. -/
theorem range_root (x : X) :
    range (fun i ↦ D.root i x) = {t | ∃ k, P k x ≠ 0 ∧ (P k x).IsRoot t} := by
  first
  | ext t
    refine ⟨?_, fun ⟨k, hk, ht⟩ ↦ D.exists_root_eq k x hk t ht⟩
    rintro ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
    exact ⟨k, (D.multiplicity_pos_iff x).1 hk⟩

/-- Over a nonempty base a family of real polynomials has at most one delineation: the root
functions are the increasing enumeration of the real roots of the nonzero members, and the
multiplicities are their root multiplicities. -/
instance instSubsingleton [Nonempty X] : Subsingleton (Delineation P) where
  allEq D D' := by
    first
    | obtain ⟨x⟩ := ‹Nonempty X›
      have hrange (y : X) : range (fun i ↦ D.root i y) = range fun i ↦ D'.root i y := by
        rw [D.range_root, D'.range_root]
      -- the two stacks have the same number of sections, the number of roots at `x`
      have hcount : D.count = D'.count := by
        have h := congrArg (fun s : Set ℝ ↦ Nat.card s) (hrange x)
        simp only [Nat.card_range_of_injective (D.strictMono_root x).injective,
          Nat.card_range_of_injective (D'.strictMono_root x).injective, Nat.card_eq_fintype_card,
          Fintype.card_fin] at h
        exact h
      revert hrange hcount
      obtain ⟨c, r, -, hr, m, hm, -⟩ := D
      obtain ⟨c', r', -, hr', m', hm', -⟩ := D'
      rintro hrange (rfl : c = c')
      obtain rfl : r = r' := funext fun i ↦ funext fun y ↦ congrFun
        (((hr y).range_inj_of_wellFoundedLT (hr' y)).1 (hrange y)) i
      obtain rfl : m = m' := funext fun k ↦ funext fun i ↦ (hm k i x).symm.trans (hm' k i x)
      rfl

/-- Restriction of a delineation along a continuous map of bases. -/
def comp (f : Y → X) (hf : Continuous f) : Delineation fun k y ↦ P k (f y) where
  count := D.count
  root i y := D.root i (f y)
  continuous_root i := (D.continuous_root i).comp hf
  strictMono_root y := D.strictMono_root (f y)
  multiplicity := D.multiplicity
  rootMultiplicity_root k i y := D.rootMultiplicity_root k i (f y)
  exists_root_eq k y := D.exists_root_eq k (f y)
  exists_multiplicity_pos := D.exists_multiplicity_pos
  eq_zero_or_ne_zero k := (D.eq_zero_or_ne_zero k).imp (fun h y ↦ h (f y)) fun h y ↦ h (f y)
  natDegree_eq k y y' := D.natDegree_eq k (f y) (f y')
  signInvariant_sectionSet k i := by
    first
    | refine (congrArg _ (sectionSet_comp D.root f i)).mpr ?_
      exact (D.signInvariant_sectionSet k i).comp (u := Prod.map f id) (mapsTo_preimage _ _)
  signInvariant_sectorSet k j := by
    first
    | refine (congrArg _ (sectorSet_comp D.root f j)).mpr ?_
      exact (D.signInvariant_sectorSet k j).comp (u := Prod.map f id) (mapsTo_preimage _ _)

/-- The restriction of a delineation has the same number of sections. -/
@[simp]
theorem comp_count (f : Y → X) (hf : Continuous f) : (D.comp f hf).count = D.count := (rfl)

/-- The root functions of the restriction of a delineation are the original root functions
composed with the map of bases. -/
@[simp]
theorem comp_root (f : Y → X) (hf : Continuous f) (i : Fin (D.comp f hf).count) (y : Y) :
    (D.comp f hf).root i y = D.root (Fin.cast (D.comp_count f hf) i) (f y) := (rfl)

/-- The restriction of a delineation has the same multiplicities. -/
@[simp]
theorem comp_multiplicity (f : Y → X) (hf : Continuous f) (k : ι) (i : Fin (D.comp f hf).count) :
    (D.comp f hf).multiplicity k i = D.multiplicity k (Fin.cast (D.comp_count f hf) i) := (rfl)

end Delineation

/-- **Delineability from invariant fiber data.** Let `P k x`, for `k` in a finite index type, be
real polynomials whose coefficients depend continuously on a parameter `x` in a preconnected
space. Suppose that each member is zero everywhere or nowhere, and that the degree of each member,
its number of distinct complex roots and the degree of the gcd of every pair of distinct members
do not depend on `x`. Then the family has a delineation. -/
theorem nonempty_delineation [Finite ι] [PreconnectedSpace X]
    (hcoeff : ∀ k i, Continuous fun x ↦ (P k x).coeff i)
    (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
    (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
    (hcard : ∀ k x y, ((P k x).aroots ℂ).toFinset.card = ((P k y).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l ↦ ∀ x y, (EuclideanDomain.gcd (P k x) (P l x)).natDegree =
      (EuclideanDomain.gcd (P k y) (P l y)).natDegree) :
    Nonempty (Delineation P) := by
  first
  | rcases isEmpty_or_nonempty X with hX | hX
    · exact Delineation.nonempty_of_isEmpty P
    obtain ⟨x₀⟩ := id hX
    -- the common ordered real roots of the members that are nowhere zero
    obtain ⟨n, r, hrc, hrm, hroot, hmult⟩ :=
      exists_continuous_ordered_common_roots_of_preconnectedSpace
        (ι := {k // ∀ x, P k x ≠ 0}) (F := fun k ↦ P k.1) (d := fun k ↦ (P k.1 x₀).natDegree)
        (fun k i _ ↦ hcoeff k.1 i)
        (fun k x ↦ by rw [degree_eq_natDegree (k.2 x), hdeg k.1 x x₀])
        (fun k x₀ ↦ .of_forall fun x ↦ (hcard k.1 x x₀).le)
        (fun k l hkl x₀ ↦ .of_forall fun x ↦ hgcd (Subtype.coe_ne_coe.2 hkl) x x₀)
    -- a member which is zero somewhere is zero everywhere
    have hzero {k : ι} (h : ¬∀ x, P k x ≠ 0) (x : X) : P k x = 0 :=
      (hnull k).resolve_right h x
    let m (k : ι) (i : Fin n) : ℕ := (P k x₀).rootMultiplicity (r x₀ i)
    have hm (k : ι) (i : Fin n) (x : X) : (P k x).rootMultiplicity (r x i) = m k i := by
      by_cases hk : ∀ x, P k x ≠ 0
      · exact hmult ⟨k, hk⟩ i x x₀
      · simp only [m, hzero hk, rootMultiplicity_zero]
    have hsub (k : ι) (x : X) (hk : P k x ≠ 0) (t : ℝ) (ht : (P k x).IsRoot t) :
        ∃ i, r x i = t :=
      (hroot x t).1 ⟨⟨k, fun y h ↦ hk (hzero (fun h' ↦ h' y h) x)⟩, ht⟩
    refine ⟨Delineation.ofRoots hcoeff hnull hdeg hrc hrm hm hsub fun i ↦ ?_⟩
    obtain ⟨⟨k, hk⟩, hki⟩ := (hroot x₀ (r x₀ i)).2 ⟨i, rfl⟩
    exact ⟨k, (rootMultiplicity_pos (hk x₀)).2 hki⟩

/-- **Delineation from an ordered root enumeration.** Let `F x` be nowhere-zero real polynomials
of constant degree whose coefficients depend continuously on a parameter `x` in a preconnected
space. If continuous, pointwise strictly increasing functions `θ i` enumerate the real roots of
every `F x`, each with a multiplicity independent of `x`, then the `θ i` are the root functions
of a delineation of `F`. -/
theorem exists_delineation_of_isRoot_iff [PreconnectedSpace X] {F : X → ℝ[X]} {k : ℕ}
    {θ : Fin k → X → ℝ} (hcoeff : ∀ j, Continuous fun x ↦ (F x).coeff j) (hF : ∀ x, F x ≠ 0)
    (hdeg : ∀ x y, (F x).natDegree = (F y).natDegree) (hθ : ∀ i, Continuous (θ i))
    (hmono : ∀ x, StrictMono fun i ↦ θ i x) (hroots : ∀ x t, (F x).IsRoot t ↔ ∃ i, θ i x = t)
    (hmult : ∀ i x y, (F x).rootMultiplicity (θ i x) = (F y).rootMultiplicity (θ i y)) :
    ∃ D : Delineation fun (_ : Unit) x ↦ F x, ∀ i, ∃ j, D.root i = θ j := by
  first
  | classical
    -- over an empty base the multiplicities are unconstrained, and `1` is a valid choice
    let m (i : Fin k) : ℕ := if h : Nonempty X then (F h.some).rootMultiplicity (θ i h.some) else 1
    have hm (i : Fin k) (x : X) : (F x).rootMultiplicity (θ i x) = m i := by
      simp only [m, show Nonempty X from ⟨x⟩, ↓reduceDIte]
      exact hmult i _ _
    have hpos (i : Fin k) : 0 < m i := by
      by_cases h : Nonempty X
      · obtain ⟨x⟩ := h
        exact hm i x ▸ (rootMultiplicity_pos (hF x)).2 ((hroots x _).2 ⟨i, rfl⟩)
      · simp [m, h]
    exact ⟨Delineation.ofRoots (fun _ ↦ hcoeff) (fun _ ↦ .inr hF) (fun _ ↦ hdeg)
      hθ hmono (fun _ ↦ hm) (fun _ x _ t ↦ (hroots x t).1)
      (fun i ↦ ⟨(), hpos i⟩), fun i ↦ ⟨i, rfl⟩⟩

open Filter Metric Topology in
/-- **Local delineation from local root data.** Let `F b` be real polynomials over a real
normed space, nonzero and of constant degree near `b₀`, whose coefficients are continuous near
`b₀`. Suppose that on a neighborhood `U` of `b₀`, continuous and pointwise strictly increasing
functions `s i` enumerate the real roots of `F b`, with multiplicities independent of `b`. Then
on some ball around `b₀` inside `U` the restrictions of the `s i` are the root functions of a
delineation of `F`. -/
theorem exists_delineation_ball_of_isRoot_iff {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {F : B → ℝ[X]} {b₀ : B} {d k : ℕ} {s : Fin k → B → ℝ} {U : Set B}
    (hcoeff : ∀ᶠ b in 𝓝 b₀, ∀ j, ContinuousAt (fun b ↦ (F b).coeff j) b)
    (hF : ∀ᶠ b in 𝓝 b₀, F b ≠ 0) (hdeg : ∀ᶠ b in 𝓝 b₀, (F b).natDegree = d)
    (hU : U ∈ 𝓝 b₀) (hs : ∀ i, ContinuousOn (s i) U)
    (hmono : ∀ b ∈ U, StrictMono fun i ↦ s i b)
    (hroots : ∀ b ∈ U, ∀ t, (F b).IsRoot t ↔ ∃ i, s i b = t)
    (hmult : ∀ b ∈ U, ∀ i, (F b).rootMultiplicity (s i b) = (F b₀).rootMultiplicity (s i b₀)) :
    ∃ ε > 0, ball b₀ ε ⊆ U ∧ ∃ D : Delineation (fun (_ : Unit) (b : ball b₀ ε) ↦ F b),
      ∀ i, ∃ j, ∀ b : ball b₀ ε, D.root i b = s j b := by
  first
  | obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (Filter.Eventually.and hU (hcoeff.and (hF.and hdeg)))
    have hVU : ball b₀ ε ⊆ U := fun b hb ↦ (hball hb).1
    have : PreconnectedSpace (ball b₀ ε) :=
      isPreconnected_iff_preconnectedSpace.1 (convex_ball b₀ ε).isPreconnected
    obtain ⟨D, hD⟩ := exists_delineation_of_isRoot_iff (θ := fun i (b : ball b₀ ε) ↦ s i b)
      (fun j ↦ continuous_iff_continuousAt.2 fun b ↦
        ((hball b.2).2.1 j).comp continuous_subtype_val.continuousAt)
      (fun b ↦ (hball b.2).2.2.1) (fun b c ↦ (hball b.2).2.2.2.trans (hball c.2).2.2.2.symm)
      (fun i ↦ ((hs i).mono hVU).domRestrict) (fun b ↦ hmono b (hVU b.2))
      (fun b ↦ hroots b (hVU b.2))
      fun i b c ↦ (hmult b (hVU b.2) i).trans (hmult c (hVU c.2) i).symm
    exact ⟨ε, hε, hVU, D, fun i ↦ (hD i).imp fun _ hj b ↦ congrFun hj b⟩

/-! ### Families closed under differentiation up to zero -/

namespace Delineation

variable (D : Delineation P)

/-- **Thom's lemma for delineations.** Suppose that at a point `x` of the base the derivative of
every member of the family is zero or a member. If every member has the same sign at two distinct
points `t ≠ t'` of the fiber over `x`, then no root function takes a value in `[t, t']` at `x`. -/
theorem root_notMem_uIcc_of_sign_eval_eq {x : X}
    (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x))
    {t t' : ℝ} (htt' : t ≠ t')
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (i : Fin D.count) : D.root i x ∉ uIcc t t' := by
  first
  | obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
    obtain ⟨hk0, hroot⟩ := (D.multiplicity_pos_iff x).1 hk
    -- every iterated derivative of a member is zero or a member, so it has the same sign at `t`
    -- and `t'`
    have hiter (j : ℕ) : derivative^[j] (P k x) = 0 ∨ ∃ l, P l x = derivative^[j] (P k x) := by
      induction j with
      | zero => exact .inr ⟨k, rfl⟩
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        obtain h0 | ⟨l, hl⟩ := ih
        · exact .inl (by rw [h0, derivative_zero])
        · rw [← hl]
          exact hder l
    have hsign (j : ℕ) : derivativeSign (P k x) t j = derivativeSign (P k x) t' j := by
      obtain h0 | ⟨l, hl⟩ := hiter j
      · simp only [derivativeSign_def, h0, eval_zero]
      · simpa only [derivativeSign_def, hl] using h l
    exact fun hi ↦ eval_ne_zero_of_derivativeSign_eq _
      (RealClosure.polynomialRolle_of_isRealClosed (R := ℝ)) hk0 htt' hsign hi hroot.eq_zero

/-- Suppose that at a point `x` of the base the derivative of every member of the family is zero
or a member. Then two points of the fiber over `x` at which every member has the same sign lie in
the same sections. -/
theorem mk_mem_sectionSet_iff_of_sign_eval_eq
    {x : X} (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x)) {t t' : ℝ}
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (i : Fin D.count) : (x, t) ∈ sectionSet D.root i ↔ (x, t') ∈ sectionSet D.root i := by
  first
  | rcases eq_or_ne t t' with rfl | htt'
    · rfl
    have hi := D.root_notMem_uIcc_of_sign_eval_eq hder htt' h i
    simp only [mem_sectionSet]
    exact iff_of_false (fun he ↦ hi (he ▸ left_mem_uIcc)) fun he ↦ hi (he ▸ right_mem_uIcc)

/-- Suppose that at a point `x` of the base the derivative of every member of the family is zero
or a member. Then two points of the fiber over `x` at which every member has the same sign lie in
the same sectors. -/
theorem mk_mem_sectorSet_iff_of_sign_eval_eq
    {x : X} (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x)) {t t' : ℝ}
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (j : Fin (D.count + 1)) : (x, t) ∈ sectorSet D.root j ↔ (x, t') ∈ sectorSet D.root j := by
  first
  | rcases eq_or_ne t t' with rfl | htt'
    · rfl
    have hi (i : Fin D.count) :
        (D.root i x < t ↔ D.root i x < t') ∧ (t < D.root i x ↔ t' < D.root i x) := by
      have := D.root_notMem_uIcc_of_sign_eval_eq hder htt' h i
      rw [mem_uIcc] at this
      grind
    simp only [mem_sectorSet, hi]

end Delineation

section MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ} {φ : A →+* ℝ}
  {F : Finset (MvPolynomial (Fin n) A)[X]} {S : Set (Fin n → ℝ)}

/-- For a delineation of the fibers of `MvPolynomial.finSuccEquiv A n f` over `S`, the polynomial
`f` in `n + 1` variables, evaluated along `φ`, is sign-invariant on every cell of the stack in
`ℝ^(n + 1)`. -/
theorem Delineation.signInvariant_eval₂_of_mem_stackCells
    (D : Delineation fun (p : F) (x : S) ↦ p.1.map (MvPolynomial.eval₂Hom φ x.1))
    {f : MvPolynomial (Fin (n + 1)) A} (hf : MvPolynomial.finSuccEquiv A n f ∈ F)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    SignInvariant (fun y ↦ MvPolynomial.eval₂ φ y f) E := by
  first
  | have key : (fun y ↦ MvPolynomial.eval₂ φ y f) ∘ cylinder S =
        fun z ↦ ((MvPolynomial.finSuccEquiv A n f).map (MvPolynomial.eval₂Hom φ z.1.1)).eval z.2 :=
      funext fun z ↦ by
        rw [Function.comp_apply, cylinder_def, MvPolynomial.polynomial_eval_map_finSuccEquiv]
    rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rw [signInvariant_image, key]
    exacts [D.signInvariant_sectionSet ⟨_, hf⟩ i, D.signInvariant_sectorSet ⟨_, hf⟩ j]

end MvPolynomial

end TauCeti
end -- closes the original EOF section from source line 87
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Delineation.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Projection/Delineability.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Collins delineability

Let `F` be a finite family of polynomials in one distinguished variable over a commutative ring
`R`, and let `φ x : R →+* ℝ` be a family of specializations parametrized by a preconnected space
`X`. If the elements of the Collins projection `F.collinsProjection` depend continuously on `x`
after specialization, and the set of those that vanish does not depend on `x`, then the
specialized family `p.map (φ x)`, `p ∈ F`, has a delineation over `X`: a common stack of
continuous, strictly ordered root functions on whose sections and sectors every member is
sign-invariant (`TauCeti.Delineation`).

The main case is `R = MvPolynomial (Fin n) A` for a coefficient map `φ : A →+* ℝ`, specialized at
the points `x` of a preconnected set `S ⊆ ℝⁿ` by `MvPolynomial.eval₂Hom φ x`. This is Collins'
delineability theorem: if every element of the projection is sign-invariant on `S`, the family is
delineable over `S`. Taking `A = ℝ` and `φ = RingHom.id ℝ` gives real families; taking `A = ℤ`
and `φ = Int.castRingHom ℝ` gives integer families whose projection is computed over `ℤ`.
Nothing is assumed about the formal leading coefficients, which may vanish on `S`, nor are
nullified members excluded: the reducta in the projection account for both. No semialgebraicity of
`S` is needed.
Only the zero pattern of the projection is used, not its signs.

## Main results

* `TauCeti.nonempty_delineation_of_collinsProjection`: a family of specializations along which the
  Collins projection is continuous and has a constant zero pattern delineates the family.
* `TauCeti.nonempty_delineation_of_signInvariant_collinsProjection`: **Collins delineability**
  over a preconnected subset of `ℝⁿ` on which the projection is sign-invariant.
* `TauCeti.nonempty_delineation_image_finSuccEquiv_map_of_signInvariant_collinsProjection`:
  delineability after mapping the coefficients of a multivariate family injectively into `ℝ`.

## References

* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Section 5.1 (Theorem 5.16) and Chapter 11.
* D. Jovanović, *Solving Non-Linear Arithmetic*, dissertation, New York University, 2012,
  Definition 2.5 and Theorem 2.6.
-/

public section

open Polynomial

namespace TauCeti

section General

variable {R X : Type*} [CommRing R] [TopologicalSpace X] [PreconnectedSpace X] {F : Finset R[X]}

/-- **Delineability from the Collins projection.** Let `φ x : R →+* ℝ` be specializations
parametrized by a preconnected space `X`. If every element of the Collins projection of `F`
specializes continuously in `x`, and whether it specializes to zero does not depend on `x`, then
the specialized family `p.map (φ x)`, `p ∈ F`, has a delineation over `X`. -/
theorem nonempty_delineation_of_collinsProjection (φ : X → R →+* ℝ)
    (hcont : ∀ a ∈ F.collinsProjection, Continuous fun x ↦ φ x a)
    (hzero : ∀ a ∈ F.collinsProjection, ∀ x y, φ x a = 0 ↔ φ y a = 0) :
    Nonempty (Delineation fun (p : F) x ↦ p.1.map (φ x)) := by
  first
  | refine nonempty_delineation (fun p i ↦ ?_) (fun p ↦ ?_)
      (fun p x y ↦ Finset.natDegree_map_eq_of_collinsProjection (fun a ha ↦ hzero a ha x y) p.2)
      (fun p x y ↦ ?_)
      fun p q _ x y ↦
        Finset.natDegree_gcd_map_eq_of_collinsProjection (fun a ha ↦ hzero a ha x y) p.2 q.2
    · -- the coefficients up to the degree are elements of the projection, the others vanish
      simp only [coeff_map]
      rcases le_or_gt i p.1.natDegree with hi | hi
      · exact hcont _ (Finset.coeff_mem_collinsProjection p.2 p.1.self_mem_reducta hi)
      · simpa [coeff_eq_zero_of_natDegree_lt hi] using continuous_const
    · by_cases h : ∃ x, p.1.map (φ x) = 0
      · obtain ⟨x, hx⟩ := h
        exact .inl fun y ↦
          (Finset.map_eq_zero_iff_of_collinsProjection (fun a ha ↦ hzero a ha x y) p.2).1 hx
      · exact .inr fun x hx ↦ h ⟨x, hx⟩
    · -- count distinct complex roots after composing with the injective map `ℝ → ℂ`
      have hzero' (a) (ha : a ∈ F.collinsProjection) :
          (algebraMap ℝ ℂ).comp (φ x) a = 0 ↔ (algebraMap ℝ ℂ).comp (φ y) a = 0 := by
        simpa using hzero a ha x y
      simpa only [aroots, map_map] using
        Finset.card_roots_toFinset_map_eq_of_collinsProjection hzero' p.2

end General

section MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ} {φ : A →+* ℝ}
  {F : Finset (MvPolynomial (Fin n) A)[X]} {S : Set (Fin n → ℝ)}

/-- **Collins delineability.** Let `F` be a finite family of polynomials in one distinguished
variable whose coefficients are polynomials over `A` in the base coordinates, and let
`φ : A →+* ℝ`. If every element of the Collins projection of `F` is sign-invariant, after
evaluation along `φ`, on a preconnected set `S ⊆ ℝⁿ`, then the family of fibers
`p.map (MvPolynomial.eval₂Hom φ x)`, `p ∈ F`, `x ∈ S`, has a delineation over `S`.

Only the zero pattern of the projection on `S` is used; see
`TauCeti.nonempty_delineation_of_collinsProjection`. -/
theorem nonempty_delineation_of_signInvariant_collinsProjection (hS : IsPreconnected S)
    (h : ∀ q ∈ F.collinsProjection, SignInvariant (fun x ↦ MvPolynomial.eval₂ φ x q) S) :
    Nonempty (Delineation fun (p : F) (x : S) ↦ p.1.map (MvPolynomial.eval₂Hom φ x.1)) := by
  first
  | have := isPreconnected_iff_preconnectedSpace.1 hS
    refine nonempty_delineation_of_collinsProjection (fun x : S ↦ MvPolynomial.eval₂Hom φ x.1)
      (fun q _ ↦ ?_) fun q hq x y ↦ ?_
    · simp only [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval_map]
      exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
    · simpa only [MvPolynomial.coe_eval₂Hom, sign_eq_zero_iff] using
        (congrArg (· = 0) (signInvariant_def.1 (h q hq) x x.2 y y.2)).to_iff

/-- **Delineability of families mapped to `ℝ`.** Let `P` be a finite family of polynomials in
the variables `X 0, …, X n` over `A`, and let `φ : A →+* ℝ` be injective. If every element of the
Collins projection computed over `A`, with `X 0` singled out, is sign-invariant after evaluation
along `φ` on a preconnected set `S ⊆ ℝⁿ`, then the family obtained by mapping `P` to `ℝ` and
singling out `X 0` has a delineation over `S`. -/
theorem nonempty_delineation_image_finSuccEquiv_map_of_signInvariant_collinsProjection
    [DecidableEq (MvPolynomial (Fin n) A)[X]] [DecidableEq (MvPolynomial (Fin n) ℝ)[X]]
    (hφ : Function.Injective φ) {P : Finset (MvPolynomial (Fin (n + 1)) A)}
    (hS : IsPreconnected S)
    (h : ∀ q ∈ (P.image (MvPolynomial.finSuccEquiv A n)).collinsProjection,
      SignInvariant (fun x ↦ MvPolynomial.eval₂ φ x q) S) :
    Nonempty (Delineation fun (p : P.image fun f ↦ MvPolynomial.finSuccEquiv ℝ n (f.map φ))
      (x : S) ↦ p.1.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) x.1)) := by
  first
  | classical
    refine nonempty_delineation_of_signInvariant_collinsProjection hS fun q hq ↦ ?_
    rw [Finset.collinsProjection_image_finSuccEquiv_map hφ] at hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
    simpa only [MvPolynomial.eval₂_id, MvPolynomial.eval_map] using h r hr

end MvPolynomial

end TauCeti
end -- closes the original EOF section from source line 53
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Projection/Delineability.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/RootCount.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Root-count characterizations of stack cells

For a strictly ordered finite stack, a point is on section `i` exactly when its height is
one of the section values and exactly `i` section values are below it. It is in sector `j`
exactly when its height is not a section value and exactly `j` section values are below it.
These descriptions identify stack cells with uniform polynomial shared-root formulas.
The order-theoretic statements allow any linearly ordered height type and include the empty
stack and both unbounded sectors.
-/

public section

namespace TauCeti

variable {X α : Type*} [LinearOrder α] {k : ℕ} {θ : Fin k → X → α}

/-- A section is characterized by membership in the finite set of section heights and the
number of section heights strictly below the point. Indices are counted from zero. -/
theorem mem_sectionSet_iff_mem_image_card_lt
    (i : Fin k) (z : X × α) (hθ : StrictMono fun l ↦ θ l z.1) :
    z ∈ sectionSet θ i ↔
      z.2 ∈ Finset.univ.image (fun l ↦ θ l z.1) ∧
        ((Finset.univ.image (fun l ↦ θ l z.1)).filter (· < z.2)).card = i.val := by
  first
  | classical
    have hcard (l : Fin k) :
        ((Finset.univ.image (fun m ↦ θ m z.1)).filter (· < θ l z.1)).card = l.val := by
      rw [Finset.filter_image, Finset.card_image_of_injective _ hθ.injective]
      simp only [hθ.lt_iff_lt]
      simpa only [Finset.filter_gt_eq_Iio] using Fin.card_Iio l
    simp only [mem_sectionSet]
    constructor
    · intro hi
      rw [← hi]
      exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hcard i⟩
    · rintro ⟨ht, hc⟩
      obtain ⟨l, _, hl⟩ := Finset.mem_image.1 ht
      have hli : l = i := Fin.ext ((hcard l).symm.trans (hl ▸ hc))
      simpa only [hli] using hl

/-- A sector is characterized by avoiding the finite set of section heights and the
number of section heights strictly below the point. This includes the empty stack. -/
theorem mem_sectorSet_iff_notMem_image_card_lt
    (j : Fin (k + 1)) (z : X × α) (hθ : StrictMono fun l ↦ θ l z.1) :
    z ∈ sectorSet θ j ↔
      z.2 ∉ Finset.univ.image (fun l ↦ θ l z.1) ∧
        ((Finset.univ.image (fun l ↦ θ l z.1)).filter (· < z.2)).card = j.val := by
  first
  | classical
    have hcard : ((Finset.univ.image (fun l ↦ θ l z.1)).filter (· < z.2)).card =
        (Finset.univ.filter fun l ↦ θ l z.1 < z.2).card := by
      rw [Finset.filter_image, Finset.card_image_of_injective _ hθ.injective]
    rw [hcard, mem_sectorSet]
    constructor
    · rintro ⟨hlo, hhi⟩
      have hlt (i : Fin k) : θ i z.1 < z.2 ↔ i.val < j.val := by
        constructor
        · intro h
          by_contra! h'
          exact (hhi i h').not_gt h
        · exact hlo i
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
        intro i hi
        rcases lt_or_ge i.castSucc j with hij | hij
        · exact (hlo i hij).ne hi
        · exact (hhi i hij).ne hi.symm
      · simp only [hlt, Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt_succ j.isLt)]
    · rintro ⟨hne, hc⟩
      have hlt (i : Fin k) : θ i z.1 < z.2 ↔ i.val < j.val := by
        rw [← hc]
        exact (Fin.lt_card_filter_univ_iff_apply_of_imp (fun l ↦ θ l z.1 < z.2)
          (fun l m hml hl ↦ (hθ.monotone hml).trans_lt hl)).symm
      refine ⟨fun i hi ↦ (hlt i).2 hi, fun i hi ↦ ?_⟩
      have hni : θ i z.1 ≠ z.2 := by
        intro h
        apply hne
        rw [← h]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      exact lt_of_le_of_ne (le_of_not_gt fun h ↦ hi.not_gt ((hlt i).1 h)) hni.symm

end TauCeti
end -- closes the original EOF section from source line 22
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/RootCount.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/RealClosed/RootsBelow.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Counting the roots below a point by a square substitution

Over an ordered real closed field, the roots of `p.comp (C t - X ^ 2)` are the square roots of
`t - r` for the roots `r ≤ t` of `p`. A root `r < t` contributes the two roots `±√(t - r)`, a root
at `t` contributes the single root `0`, and roots above `t` contribute nothing. So, for nonzero
`p`, the number of distinct roots of `p` below `t` is determined by the number of distinct roots
of `p.comp (C t - X ^ 2)` and whether `t` is a root of `p`. The underlying count of the square
roots of a single element `a`, namely two, one or none as `a` is positive, zero or negative, is
`Polynomial.card_nthRootsFinset_two`.

Since the coefficients of `p.comp (C t - X ^ 2)` are polynomials in `t` and in the coefficients
of `p`, this reduces counting the roots of `p` in `(-∞, t)` to counting all distinct roots of
another polynomial. It is used to describe the roots of a polynomial family below a moving point
by polynomial sign conditions.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Over an ordered real closed field, `a` has two square roots `±√a` when `0 < a`, the single
square root `0` when `a = 0`, and none when `a < 0`. -/
theorem card_nthRootsFinset_two (a : R) :
    (nthRootsFinset 2 a).card = if 0 < a then 2 else if a = 0 then 1 else 0 := by
  first
  | have hmem (y : R) : y ∈ nthRootsFinset 2 a ↔ y ^ 2 = a := mem_nthRootsFinset two_pos a
    rcases lt_trichotomy 0 a with h | rfl | h
    · obtain ⟨s, hs⟩ := IsRealClosed.nonneg_iff_isSquare.mp h.le
      have hs0 : s ≠ -s := by
        intro hs'
        have hs_zero : s = 0 := by linarith
        have : a = 0 := by rw [hs, hs_zero, mul_zero]
        exact h.ne' this
      have : nthRootsFinset 2 a = {s, -s} := by
        ext y
        rw [hmem, hs, sq, mul_self_eq_mul_self_iff, Finset.mem_insert, Finset.mem_singleton]
      rw [this, Finset.card_pair hs0]
      simp [h]
    · have : nthRootsFinset 2 (0 : R) = {0} := by
        ext y
        rw [hmem]
        simp
      simp [this]
    · have : nthRootsFinset 2 a = ∅ := by
        ext y
        simp only [hmem, Finset.notMem_empty, iff_false]
        nlinarith [sq_nonneg y]
      simp [this, h.not_gt, h.ne]

/-- **Roots below a point by a square substitution.** For nonzero `p`, every root of `p` below
`t` gives two distinct roots `±√(t - r)` of `p.comp (C t - X ^ 2)`, a root at `t` gives the root
`0`, and these are all of its roots. -/
theorem card_roots_toFinset_comp_C_sub_X_sq {p : R[X]} (hp : p ≠ 0) (t : R) :
    (p.comp (C t - X ^ 2)).roots.toFinset.card =
      2 * {r ∈ p.roots.toFinset | r < t}.card + if p.IsRoot t then 1 else 0 := by
  first
  | classical
    have hq : p.comp (C t - X ^ 2) ≠ 0 := by
      rw [Ne, comp_eq_zero_iff]
      rintro (h | ⟨-, h⟩)
      · exact hp h
      · simpa using congrArg (coeff · 2) h
    have hmem (y : R) : y ∈ (p.comp (C t - X ^ 2)).roots.toFinset ↔ p.IsRoot (t - y ^ 2) := by
      simp [mem_roots hq]
    -- Group the roots of the substituted polynomial by the root `t - y ^ 2` of `p` they come from.
    rw [Finset.card_eq_sum_card_fiberwise (f := fun y => t - y ^ 2) (t := p.roots.toFinset)
      fun y hy => by simpa [mem_roots hp] using (hmem y).1 hy]
    -- The fiber over a root `r` consists of the square roots of `t - r`.
    have hfiber (r : R) (hr : r ∈ p.roots.toFinset) :
        {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r}.card =
          (if r < t then 2 else 0) + if t = r then 1 else 0 := by
      have hr' : p.IsRoot r := by simpa [mem_roots hp] using hr
      have : {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r} =
          nthRootsFinset 2 (t - r) := by
        ext y
        rw [Finset.mem_filter, hmem, mem_nthRootsFinset two_pos]
        constructor
        · rintro ⟨-, h⟩
          rw [← h, sub_sub_cancel]
        · intro h
          have h' : t - y ^ 2 = r := by rw [h, sub_sub_cancel]
          exact ⟨h' ▸ hr', h'⟩
      rw [this, card_nthRootsFinset_two]
      simp only [sub_pos, sub_eq_zero]
      rcases lt_trichotomy r t with h | h | h
      · simp [h, h.ne']
      · simp [h]
      · simp [h.not_gt, h.ne]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_add_distrib, ← Finset.sum_filter,
      Finset.sum_const, smul_eq_mul, mul_comm _ 2, Finset.sum_ite_eq]
    simp [mem_roots hp]

end Polynomial
end -- closes the original EOF section from source line 27
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/RealClosed/RootsBelow.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/MvPolynomial/Rename.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Renaming variables, and discarding the ones outside the range

Renaming the variables of a multivariable polynomial along an equivalence `e : σ ≃ τ` is a
ring equivalence. Mathlib's `RingHomInvPair.of_ringEquiv` and
`RingHomInvPair.of_ringEquiv_symm` are deliberately not instances, so this file registers them
for `MvPolynomial.renameEquiv`. This lets semilinear equivalences over variable renaming be used
and inverted without requiring downstream local instances.

Injective variable renaming reindexes the native coefficient vector along the induced embedding
of exponent vectors.

Along an injective renaming `f : σ → τ`, Mathlib's `MvPolynomial.killCompl` sets the variables
outside the range of `f` to zero. When exactly one variable `X a` is discarded, the polynomials
it kills are exactly the multiples of `X a`.

## Main definitions

* `TauCeti.renameRingHomInvPair`: variable renaming and its inverse form a `RingHomInvPair`.
* `TauCeti.renameRingHomInvPairSymm`: the same inverse pair in the reverse direction.

## Main results

* `MvPolynomial.coeff_rename_eq_embDomain`: injective renaming embeds the coefficient vector
  along the induced map of exponents.
* `MvPolynomial.killCompl_X_of_notMem_range`: a variable outside the range of an injective
  renaming is killed by `killCompl`.
* `MvPolynomial.killCompl_eq_zero_iff_X_dvd`: when the range of the renaming is the complement of
  a single variable `X a`, discarding that variable kills exactly the multiples of `X a`.
* `Polynomial.map_eval_map_rename`: for a polynomial family with coefficients in `MvPolynomial`,
  specializing after renaming the parameters along `f` is specializing at the composite point.
-/

public section

namespace MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- Injective variable renaming reindexes the native coefficient vector by the induced
embedding of exponent vectors. -/
theorem coeff_rename_eq_embDomain (p : MvPolynomial σ R) {f : σ → τ}
    (hf : Function.Injective f) :
    AddMonoidAlgebra.coeff (rename f p) =
      (AddMonoidAlgebra.coeff p).embDomain
        ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective hf⟩ := by
  first
  | classical
    let e : (σ →₀ ℕ) ↪ (τ →₀ ℕ) :=
      ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective hf⟩
    ext d
    by_cases hd : ∃ a, e a = d
    · obtain ⟨a, rfl⟩ := hd
      rw [Finsupp.embDomain_apply_self]
      -- Since `MvPolynomial` abbreviates `AddMonoidAlgebra`, `.coeff` is its native coefficient
      -- evaluation, and `e a` reduces to `a.mapDomain f`. Expose this form to apply
      -- `coeff_rename_embDomain`.
      change (rename f p).coeff (a.mapDomain f) = p.coeff a
      simpa only [Finsupp.embDomain_eq_mapDomain, Function.Embedding.coeFn_mk] using
        coeff_rename_embDomain ⟨f, hf⟩ p a
    · rw [Finsupp.embDomain_of_notMem_range e _ d hd]
      exact coeff_rename_eq_zero f p d (fun a ha ↦ (hd ⟨a, ha⟩).elim)

variable {σ τ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f) {a : τ}

/-- A variable outside the range of an injective renaming is killed by `killCompl`. -/
@[simp]
theorem killCompl_X_of_notMem_range (ha : a ∉ Set.range f) :
    killCompl (R := R) hf (X a) = 0 := by
  first
  | rw [X]
    exact killCompl_monomial_eq_zero_of_notMem_range hf (s := Finsupp.single a 1) 1
      (a := a) (by simp) ha

/-- When the range of an injective renaming is the complement of a single variable `X a`,
discarding the variables outside the range kills exactly the multiples of `X a`. -/
theorem killCompl_eq_zero_iff_X_dvd (ha : Set.range f = {a}ᶜ) (p : MvPolynomial τ R) :
    killCompl hf p = 0 ↔ X a ∣ p := by
  first
  | have hna : a ∉ Set.range f := by simp [ha]
    constructor
    · intro h
      rw [X_dvd_iff_modMonomial_eq_zero]
      refine MvPolynomial.ext _ _ fun m => ?_
      rcases Nat.eq_zero_or_pos (m a) with hm | hm
      · -- A monomial avoiding `a` is renamed from a monomial in the source variables.
        have hsub : ↑m.support ⊆ Set.range f := by
          intro x hx
          rw [ha]
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          rintro rfl
          exact (Finsupp.mem_support_iff.mp hx) hm
        have hmd : Finsupp.mapDomain f (Finsupp.comapDomain f m hf.injOn) = m :=
          m.mapDomain_comapDomain f hf hsub
        rw [coeff_modMonomial_of_not_le _ (by rw [Finsupp.single_le_iff]; omega), ← hmd,
          ← coeff_killCompl hf, h]
        simp
      · rw [coeff_modMonomial_of_le _ (by rw [Finsupp.single_le_iff]; omega)]
        simp
    · rintro ⟨q, rfl⟩
      rw [map_mul, killCompl_X_of_notMem_range hf hna, zero_mul]

end MvPolynomial

namespace Polynomial

/-- Renaming the parameters of a polynomial family `P : (MvPolynomial σ R)[X]` along `f` and then
specializing them at `y` is specializing `P` at `y ∘ f`. -/
theorem map_eval_map_rename {σ τ R : Type*} [CommSemiring R] (f : σ → τ)
    (P : (MvPolynomial σ R)[X]) (y : τ → R) :
    (P.map (MvPolynomial.rename (R := R) f).toRingHom).map (MvPolynomial.eval y) =
      P.map (MvPolynomial.eval (y ∘ f)) := by
  first
  | rw [Polynomial.map_map]
    congr 1
    ext <;> simp

end Polynomial

namespace TauCeti

variable {σ τ : Type*} (R : Type*) [CommSemiring R]

/-- A polynomial variable-renaming ring equivalence and its inverse form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPair (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R) :=
  RingHomInvPair.of_ringEquiv (MvPolynomial.renameEquiv R e).toRingEquiv

/-- The inverse polynomial variable-renaming ring equivalence and the forward equivalence form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPairSymm (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R) :=
  RingHomInvPair.of_ringEquiv_symm (MvPolynomial.renameEquiv R e).toRingEquiv

end TauCeti
end -- closes the original EOF section from source line 46
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/MvPolynomial/Rename.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Eval/OneSided.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # One-sided polynomial signs

The first nonzero formal derivative determines a polynomial's sign immediately
to the right of a point. To the left, the parity of its root multiplicity
supplies the additional sign. These algebraic signs allow endpoint root-count
formulas to include multiple roots without choosing nearby evaluation points.

Both signs are zero for the zero polynomial. Over any ordered field they agree
with evaluation on sufficiently small open intervals on the appropriate side.
No completeness or Archimedean assumption is needed. The two signs agree exactly when the root
multiplicity is even, so a nonzero polynomial changes sign at a point exactly when its root
multiplicity there is odd.

In characteristic zero, the one-sided signs of the derivative at `a` are those of the increment
`p - p(a)` on the right and their negatives on the left. In particular, at a root the
derivative has the sign of `p` immediately to the right of the root and the opposite sign
immediately to the left.

## Main definitions

* `Polynomial.derivSignRight p a`: the sign of the first nonzero derivative of `p` at `a`.
* `Polynomial.derivSignLeft p a`: the parity-corrected left-hand sign of `p` at `a`.

## Implementation notes

Mathlib defines the real right-hand sign `Polynomial.signRight x p` analytically, as the eventual
sign of evaluation along `𝓝[>] x`. The signs here are algebraic and need only a commutative ring
with a linear order, so they remain separate. Over `ℝ`, the two right-hand signs agree by
`Polynomial.derivSignRight_eq_signRight` in `TauCeti.Analysis.Polynomial.SignRight`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapters 2 and 10.
-/

public section

open Polynomial SignType Set Topology

namespace Polynomial

section Definitions

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The right-hand sign, computed from the derivative at the root multiplicity.
For a nonzero polynomial over an ordered field this is its first nonzero derivative.
The zero polynomial has sign zero. -/
noncomputable def derivSignRight (p : R[X]) (a : R) : SignType :=
  p.derivativeSign a (p.rootMultiplicity a)

/-- The left-hand sign is the right-hand sign corrected by multiplicity parity. -/
noncomputable def derivSignLeft (p : R[X]) (a : R) : SignType :=
  (-1) ^ p.rootMultiplicity a * p.derivSignRight a

/-- The derivative formula for the right-hand sign. -/
theorem derivSignRight_def (p : R[X]) (a : R) :
    p.derivSignRight a = sign ((derivative^[p.rootMultiplicity a] p).eval a) :=
  derivativeSign_def p a _

/-- The parity formula for the left-hand sign. -/
theorem derivSignLeft_def (p : R[X]) (a : R) :
    p.derivSignLeft a = (-1) ^ p.rootMultiplicity a * p.derivSignRight a := (rfl)

@[simp]
theorem derivSignRight_zero (a : R) : (0 : R[X]).derivSignRight a = 0 := by
  first
  | simp [derivSignRight_def]

@[simp]
theorem derivSignLeft_zero (a : R) : (0 : R[X]).derivSignLeft a = 0 := by
  first
  | simp [derivSignLeft_def]

@[simp]
theorem derivSignRight_C (c a : R) : (C c).derivSignRight a = sign c := by
  first
  | simp [derivSignRight_def]

@[simp]
theorem derivSignLeft_C (c a : R) : (C c).derivSignLeft a = sign c := by
  first
  | simp [derivSignLeft_def]

section One

variable [ZeroLEOneClass R] [NeZero (1 : R)]

@[simp]
theorem derivSignRight_one (a : R) : (1 : R[X]).derivSignRight a = 1 := by
  first
  | simpa [sign_pos zero_lt_one] using derivSignRight_C (1 : R) a

@[simp]
theorem derivSignLeft_one (a : R) : (1 : R[X]).derivSignLeft a = 1 := by
  first
  | simpa [sign_pos zero_lt_one] using derivSignLeft_C (1 : R) a

end One

/-- Away from a root, the right-hand sign is the sign of the value itself. -/
theorem derivSignRight_eq_sign_eval (p : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    p.derivSignRight a = sign (p.eval a) := by
  first
  | simp [derivSignRight_def, rootMultiplicity_eq_zero ha]

/-- Away from a root, the left-hand sign is also the sign of the value. -/
theorem derivSignLeft_eq_sign_eval (p : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    p.derivSignLeft a = sign (p.eval a) := by
  first
  | simp [derivSignLeft_def, rootMultiplicity_eq_zero ha, derivSignRight_eq_sign_eval p ha]

/-- Adding a multiple of a higher power of `X - C a` leaves the right-hand sign at `a` of a
nonzero polynomial unchanged. -/
theorem derivSignRight_add_eq_left_of_dvd {p q : R[X]} {a : R} (hp : p ≠ 0)
    (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).derivSignRight a = p.derivSignRight a := by
  first
  | have hq0 : (derivative^[p.rootMultiplicity a] q).eval a = 0 := by
      by_cases hq0 : q = 0
      · simp [hq0]
      exact isRoot_iterate_derivative_of_lt_rootMultiplicity
        (Nat.lt_of_succ_le ((le_rootMultiplicity_iff hq0).mpr hq))
    rw [derivSignRight_def, derivSignRight_def, rootMultiplicity_add_eq_left_of_dvd hp hq,
      iterate_map_add derivative, eval_add, hq0, add_zero]

/-- Adding a multiple of a higher power of `X - C a` leaves the left-hand sign at `a` of a
nonzero polynomial unchanged. -/
theorem derivSignLeft_add_eq_left_of_dvd {p q : R[X]} {a : R} (hp : p ≠ 0)
    (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).derivSignLeft a = p.derivSignLeft a := by
  first
  | rw [derivSignLeft_def, derivSignLeft_def, rootMultiplicity_add_eq_left_of_dvd hp hq,
      derivSignRight_add_eq_left_of_dvd hp hq]

end Definitions

section Transport

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- Strictly monotone ring embeddings preserve right-hand signs. -/
@[simp]
theorem derivSignRight_map {S : Type*} [CommRing S] [LinearOrder S]
    (p : R[X]) (f : R →+* S) (hf : StrictMono f) (a : R) :
    (p.map f).derivSignRight (f a) = p.derivSignRight a := by
  first
  | rw [derivSignRight_def, derivSignRight_def, ← eq_rootMultiplicity_map hf.injective,
      iterate_derivative_map]
    exact sign_eval_map _ f hf a

/-- Strictly monotone ring embeddings preserve left-hand signs. -/
@[simp]
theorem derivSignLeft_map {S : Type*} [CommRing S] [LinearOrder S]
    (p : R[X]) (f : R →+* S) (hf : StrictMono f) (a : R) :
    (p.map f).derivSignLeft (f a) = p.derivSignLeft a := by
  first
  | rw [derivSignLeft_def, derivSignLeft_def, ← eq_rootMultiplicity_map hf.injective,
      derivSignRight_map p f hf]

end Transport

section Neg

variable {R : Type*} [CommRing R] [LinearOrder R] [AddLeftMono R]

/-- Negation reverses the right-hand sign. -/
@[simp]
theorem derivSignRight_neg (p : R[X]) (a : R) :
    (-p).derivSignRight a = -p.derivSignRight a := by
  first
  | simp only [derivSignRight_def, rootMultiplicity_eq_natTrailingDegree, neg_comp,
      natTrailingDegree_neg, iterate_derivative_neg, eval_neg, Left.sign_neg]

/-- Negation reverses the left-hand sign. -/
@[simp]
theorem derivSignLeft_neg (p : R[X]) (a : R) :
    (-p).derivSignLeft a = -p.derivSignLeft a := by
  first
  | simp only [derivSignLeft_def, rootMultiplicity_eq_natTrailingDegree, neg_comp,
      natTrailingDegree_neg, derivSignRight_neg, mul_neg]

end Neg

section Derivative

variable {R : Type*} [CommRing R] [LinearOrder R] [NoZeroDivisors R] [CharZero R]

/-- At a root, the derivative has the right-hand sign of the polynomial. -/
theorem derivSignRight_derivative_of_isRoot {p : R[X]} {a : R} (ha : p.IsRoot a) :
    p.derivative.derivSignRight a = p.derivSignRight a := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
    rw [derivSignRight, derivSignRight, derivative_rootMultiplicity_of_root ha,
      derivativeSign_derivative, Nat.sub_add_cancel hm]

/-- At a root, the derivative has the opposite of the left-hand sign of the polynomial. -/
theorem derivSignLeft_derivative_of_isRoot {p : R[X]} {a : R} (ha : p.IsRoot a) :
    p.derivative.derivSignLeft a = -p.derivSignLeft a := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [derivSignLeft_def, derivSignLeft_def, derivSignRight_derivative_of_isRoot ha,
      derivative_rootMultiplicity_of_root ha, hk]
    simp [pow_succ]

/-- At any point `a`, the right-hand sign of the derivative equals the right-hand sign of the
increment `p - C (p.eval a)`. Over an ordered field this is the sign of `p(x) - p(a)` just to the
right of `a`; see `exists_sign_eval_derivative`. -/
theorem derivSignRight_derivative (p : R[X]) (a : R) :
    p.derivative.derivSignRight a = (p - C (p.eval a)).derivSignRight a := by
  first
  | have h := derivSignRight_derivative_of_isRoot (p := p - C (p.eval a)) (a := a) (by simp)
    rwa [derivative_sub, derivative_C, sub_zero] at h

/-- At any point `a`, the left-hand sign of the derivative equals the negative of the left-hand
sign of the increment `p - C (p.eval a)`. Over an ordered field this is the opposite of the sign
of `p(x) - p(a)` just to the left of `a`; see `exists_sign_eval_derivative`. -/
theorem derivSignLeft_derivative (p : R[X]) (a : R) :
    p.derivative.derivSignLeft a = -(p - C (p.eval a)).derivSignLeft a := by
  first
  | have h := derivSignLeft_derivative_of_isRoot (p := p - C (p.eval a)) (a := a) (by simp)
    rwa [derivative_sub, derivative_C, sub_zero] at h

end Derivative

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Removing the full root factor gives the same sign as the first nonzero derivative. -/
theorem derivSignRight_eq_sign_eval_divByMonic (p : R[X]) (a : R) :
    p.derivSignRight a = sign ((p /ₘ (X - C a) ^ p.rootMultiplicity a).eval a) := by
  first
  | rw [derivSignRight_def, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul, sign_mul,
      sign_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)), one_mul]

/-- A one-sided sign vanishes exactly when the polynomial is zero. -/
@[simp]
theorem derivSignRight_eq_zero_iff (p : R[X]) (a : R) : p.derivSignRight a = 0 ↔ p = 0 := by
  first
  | constructor
    · intro h
      by_contra hp
      rw [derivSignRight_eq_sign_eval_divByMonic, sign_eq_zero_iff] at h
      exact eval_divByMonic_pow_rootMultiplicity_ne_zero a hp h
    · rintro rfl
      simp

@[simp]
theorem derivSignLeft_eq_zero_iff (p : R[X]) (a : R) : p.derivSignLeft a = 0 ↔ p = 0 := by
  first
  | rw [derivSignLeft_def, mul_eq_zero]
    simp

/-- A nonzero polynomial does not vanish where it has its right-hand sign. -/
theorem eval_ne_zero_of_sign_eq_derivSignRight {p : R[X]} (hp : p ≠ 0) {a x : R}
    (h : sign (p.eval x) = p.derivSignRight a) : p.eval x ≠ 0 := fun h0 => by
  rw [h0, sign_zero, eq_comm, derivSignRight_eq_zero_iff] at h
  exact hp h

/-- A nonzero polynomial does not vanish where it has its left-hand sign. -/
theorem eval_ne_zero_of_sign_eq_derivSignLeft {p : R[X]} (hp : p ≠ 0) {a x : R}
    (h : sign (p.eval x) = p.derivSignLeft a) : p.eval x ≠ 0 := fun h0 => by
  rw [h0, sign_zero, eq_comm, derivSignLeft_eq_zero_iff] at h
  exact hp h

omit [IsStrictOrderedRing R] in
/-- An even root multiplicity gives equal signs on the two sides. -/
theorem derivSignLeft_eq_derivSignRight_of_even (p : R[X]) (a : R)
    (h : Even (p.rootMultiplicity a)) : p.derivSignLeft a = p.derivSignRight a := by
  first
  | rw [derivSignLeft_def, h.neg_one_pow, one_mul]

omit [IsStrictOrderedRing R] in
/-- An odd root multiplicity gives opposite signs on the two sides. -/
theorem derivSignLeft_eq_neg_derivSignRight_of_odd (p : R[X]) (a : R)
    (h : Odd (p.rootMultiplicity a)) : p.derivSignLeft a = -p.derivSignRight a := by
  first
  | rw [derivSignLeft_def, h.neg_one_pow, neg_one_mul]

/-- The one-sided signs agree exactly when the root multiplicity is even. This includes the zero
polynomial, whose one-sided signs are both zero. -/
@[simp]
theorem derivSignLeft_eq_derivSignRight_iff (p : R[X]) (a : R) :
    p.derivSignLeft a = p.derivSignRight a ↔ Even (p.rootMultiplicity a) := by
  first
  | rcases Nat.even_or_odd (p.rootMultiplicity a) with h | h
    · simp [derivSignLeft_eq_derivSignRight_of_even p a h, h]
    by_cases hp : p = 0
    · simp [hp] at h
    rw [derivSignLeft_eq_neg_derivSignRight_of_odd p a h, iff_false_intro (Nat.not_even_iff_odd.2 h),
      iff_false, eq_comm, SignType.self_eq_neg_iff]
    simpa using hp

/-- For a nonzero polynomial, the one-sided signs are opposite exactly when the root multiplicity
is odd. -/
@[simp]
theorem derivSignLeft_eq_neg_derivSignRight_iff {p : R[X]} (hp : p ≠ 0) (a : R) :
    p.derivSignLeft a = -p.derivSignRight a ↔ Odd (p.rootMultiplicity a) := by
  first
  | rcases Nat.even_or_odd (p.rootMultiplicity a) with h | h
    · rw [derivSignLeft_eq_derivSignRight_of_even p a h,
        iff_false_intro (Nat.not_odd_iff_even.2 h), iff_false, SignType.self_eq_neg_iff]
      simpa using hp
    · simp [derivSignLeft_eq_neg_derivSignRight_of_odd p a h, h]

/-- Multiplication multiplies right-hand signs, including when a factor is zero. -/
@[simp]
theorem derivSignRight_mul (p q : R[X]) (a : R) :
    (p * q).derivSignRight a = p.derivSignRight a * q.derivSignRight a := by
  first
  | simp only [derivSignRight_eq_sign_eval_divByMonic, eval_divByMonic_eq_trailingCoeff_comp,
      mul_comp, trailingCoeff_mul, sign_mul]

/-- Multiplication multiplies left-hand signs, including when a factor is zero. -/
@[simp]
theorem derivSignLeft_mul (p q : R[X]) (a : R) :
    (p * q).derivSignLeft a = p.derivSignLeft a * q.derivSignLeft a := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    by_cases hq : q = 0
    · simp [hq]
    simp only [derivSignLeft_def, rootMultiplicity_mul (mul_ne_zero hp hq), pow_add,
      derivSignRight_mul]
    ac_rfl

/-- Powers raise the right-hand sign to the same power, with the convention `0^0 = 1`. -/
@[simp]
theorem derivSignRight_pow (p : R[X]) (a : R) (n : ℕ) :
    (p ^ n).derivSignRight a = p.derivSignRight a ^ n := by
  first
  | induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]

/-- Powers raise the left-hand sign to the same power, with the convention `0^0 = 1`. -/
@[simp]
theorem derivSignLeft_pow (p : R[X]) (a : R) (n : ℕ) :
    (p ^ n).derivSignLeft a = p.derivSignLeft a ^ n := by
  first
  | induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]

end OrderedRing

section OrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The algebraic one-sided signs are realized on intervals immediately to the
left and right, including at multiple roots and for the zero polynomial. -/
theorem exists_derivSignLeft_derivSignRight (p : R[X]) (a : R) :
    ∃ l u, l < a ∧ a < u ∧
      (∀ x ∈ Ioo l a, sign (p.eval x) = p.derivSignLeft a) ∧
      (∀ x ∈ Ioo a u, sign (p.eval x) = p.derivSignRight a) := by
  first
  | by_cases hp : p = 0
    · subst p
      exact ⟨a - 1, a + 1, by simp, by simp, by simp, by simp⟩
    -- Use the order topology only to choose a root-free interval for the cofactor.
    let : TopologicalSpace R := Preorder.topology R
    let : OrderTopology R := ⟨rfl⟩
    let q := p /ₘ (X - C a) ^ p.rootMultiplicity a
    have hq : q.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
    have hc : ContinuousAt (fun x : R => sign (q.eval x)) a :=
      (continuousAt_sign_of_ne_zero hq).comp (x := a) q.continuousAt
    have he : ∀ᶠ x in nhds a, sign (q.eval x) = sign (q.eval a) :=
      hc.eventually ((isOpen_discrete _).mem_nhds (Set.mem_singleton _))
    obtain ⟨l, u, ⟨hla, hau⟩, hlu⟩ := he.exists_Ioo_subset
    have hs : sign (q.eval a) = p.derivSignRight a :=
      (derivSignRight_eq_sign_eval_divByMonic p a).symm
    have hf (x : R) : sign (p.eval x) =
        sign (x - a) ^ p.rootMultiplicity a * sign (q.eval x) := by
      conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq a]
      simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sign_mul, sign_pow, q]
    refine ⟨l, u, hla, hau, ?_, ?_⟩
    · intro x hx
      rw [hf, sign_neg (sub_neg.mpr hx.2), hlu ⟨hx.1, hx.2.trans hau⟩, hs,
        derivSignLeft_def]
    · intro x hx
      rw [hf, sign_pos (sub_pos.mpr hx.1), one_pow, one_mul,
        hlu ⟨hla.trans hx.1, hx.2⟩, hs]

/-- A nonzero polynomial changes sign at `a` exactly when its root multiplicity at `a` is odd:
its signs immediately to the left of `a` are the negatives of those immediately to the right. -/
theorem odd_rootMultiplicity_iff_exists_sign_eval_eq_neg {p : R[X]} (hp : p ≠ 0) (a : R) :
    Odd (p.rootMultiplicity a) ↔ ∃ l u, l < a ∧ a < u ∧
      ∀ x ∈ Ioo l a, ∀ y ∈ Ioo a u, sign (p.eval x) = -sign (p.eval y) := by
  first
  | obtain ⟨l, u, hl, hu, hL, hR⟩ := p.exists_derivSignLeft_derivSignRight a
    rw [← derivSignLeft_eq_neg_derivSignRight_iff hp]
    constructor
    · intro h
      exact ⟨l, u, hl, hu, fun x hx y hy => by rw [hL x hx, hR y hy, h]⟩
    · rintro ⟨l', u', hl', hu', h⟩
      obtain ⟨x, hx, hxa⟩ := exists_between (max_lt hl hl')
      obtain ⟨y, hay, hy⟩ := exists_between (lt_min hu hu')
      rw [← hL x ⟨(le_max_left _ _).trans_lt hx, hxa⟩, ← hR y ⟨hay, hy.trans_le (min_le_left _ _)⟩]
      exact h x ⟨(le_max_right _ _).trans_lt hx, hxa⟩ y ⟨hay, hy.trans_le (min_le_right _ _)⟩

/-- Immediately to the right of a point `a`, the derivative has the sign of `p(x) - p(a)`, and
immediately to the left it has the opposite sign. This includes points where `p - p(a)` has a
multiple root, and constant polynomials. -/
theorem exists_sign_eval_derivative (p : R[X]) (a : R) :
    ∃ l u, l < a ∧ a < u ∧
      (∀ x ∈ Ioo l a, sign (p.derivative.eval x) = -sign (p.eval x - p.eval a)) ∧
      (∀ x ∈ Ioo a u, sign (p.derivative.eval x) = sign (p.eval x - p.eval a)) := by
  first
  | obtain ⟨l₁, u₁, hl₁, hu₁, hL₁, hR₁⟩ := p.derivative.exists_derivSignLeft_derivSignRight a
    obtain ⟨l₂, u₂, hl₂, hu₂, hL₂, hR₂⟩ := (p - C (p.eval a)).exists_derivSignLeft_derivSignRight a
    refine ⟨max l₁ l₂, min u₁ u₂, max_lt hl₁ hl₂, lt_min hu₁ hu₂, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hL₁ x ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩, derivSignLeft_derivative,
        ← hL₂ x ⟨(le_max_right _ _).trans_lt hx.1, hx.2⟩, eval_sub, eval_C]
    · rw [hR₁ x ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩, derivSignRight_derivative,
        ← hR₂ x ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩, eval_sub, eval_C]

end OrderedField

end Polynomial

namespace List

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A uniform interval immediately to the right of `a` on which every polynomial of a list
has its right-hand sign at `a`. -/
theorem exists_signs_right (cs : List R[X]) (a : R) :
    ∃ u, a < u ∧ ∀ p ∈ cs, ∀ x ∈ Ioo a u, sign (p.eval x) = p.derivSignRight a := by
  first
    -- Use the order topology only to combine the finitely many right-hand intervals.
  | let : TopologicalSpace R := Preorder.topology R
    let : OrderTopology R := ⟨rfl⟩
    have he : ∀ᶠ x in 𝓝[>] a, ∀ p ∈ cs, sign (p.eval x) = p.derivSignRight a := by
      refine cs.finite_toSet.eventually_all.mpr fun p _ => ?_
      obtain ⟨-, u, -, hau, -, hu⟩ := p.exists_derivSignLeft_derivSignRight a
      exact Filter.mem_of_superset (Ioo_mem_nhdsGT hau) hu
    obtain ⟨u, hau, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
    exact ⟨u, hau, fun p hp x hx => hu hx p hp⟩

/-- A uniform interval immediately to the left of `a` on which every polynomial of a list
has its left-hand sign at `a`. -/
theorem exists_signs_left (cs : List R[X]) (a : R) :
    ∃ l, l < a ∧ ∀ p ∈ cs, ∀ x ∈ Ioo l a, sign (p.eval x) = p.derivSignLeft a := by
  first
    -- Use the order topology only to combine the finitely many left-hand intervals.
  | let : TopologicalSpace R := Preorder.topology R
    let : OrderTopology R := ⟨rfl⟩
    have he : ∀ᶠ x in 𝓝[<] a, ∀ p ∈ cs, sign (p.eval x) = p.derivSignLeft a := by
      refine cs.finite_toSet.eventually_all.mpr fun p _ => ?_
      obtain ⟨l, -, hla, -, hl, -⟩ := p.exists_derivSignLeft_derivSignRight a
      exact Filter.mem_of_superset (Ioo_mem_nhdsLT hla) hl
    obtain ⟨l, hla, hl⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
    exact ⟨l, hla, fun p hp x hx => hl hx p hp⟩

end List
end -- closes the original EOF section from source line 53
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Eval/OneSided.lean -/

/- BEGIN SOURCE: TauCeti/Data/Finset/Jumps.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Summing finitely many jumps on an ordered interval

A function into an additive commutative group, constant between finitely many events, has total
change equal to the sum of its local changes. This is the finite telescoping
step in the signed Sturm theorem; it uses no topology or completeness.
-/

public section

namespace Finset

open Set

variable {R : Type*} [LinearOrder R] [DenselyOrdered R]

/-- Choose a point to the right of an event, before all later events and a given bound. -/
theorem exists_right_gap (S : Finset R) {r b : R} (hrb : r < b) :
    ∃ c, r < c ∧ c < b ∧ ∀ x ∈ S, r < x → c < x := by
  first
  | classical
    by_cases h : ∃ y ∈ S, r < y
    · obtain ⟨y, _, hry, hy⟩ := S.exists_next_right h
      obtain ⟨c, hrc, hcyb⟩ := exists_between (lt_min hry hrb)
      exact ⟨c, hrc, hcyb.trans_le (min_le_right _ _),
        fun x hx hrx => (hcyb.trans_le (min_le_left _ _)).trans_le (hy x hx hrx)⟩
    · obtain ⟨c, hrc, hcb⟩ := exists_between hrb
      exact ⟨c, hrc, hcb, fun x hx hrx => (h ⟨x, hx, hrx⟩).elim⟩

/-- Choose a point to the left of an event, after all earlier events and a given bound. -/
theorem exists_left_gap (S : Finset R) {a r : R} (har : a < r) :
    ∃ c, a < c ∧ c < r ∧ ∀ x ∈ S, x < r → x < c := by
  first
  | obtain ⟨c, hcr, hac, hc⟩ := exists_right_gap (R := OrderDual R) S (r := r) (b := a) har
    exact ⟨c, hac, hcr, hc⟩

/-- Local changes at isolated events sum to the total change between two
points outside the event set. -/
theorem sum_jumps {G : Type*} [AddCommGroup G] (S : Finset R) (V w : R → G)
    {a₀ b₀ : R}
    (hconst : ∀ a b, a₀ ≤ a → b ≤ b₀ → a < b → (∀ x ∈ S, x ∉ Set.Icc a b) → V a = V b)
    (hjump : ∀ a r b, a₀ ≤ a → b ≤ b₀ → a < r → r < b → r ∈ S →
      (∀ x ∈ S, x ∈ Set.Icc a b → x = r) → V a - V b = w r)
    (hab : a₀ < b₀) (ha : a₀ ∉ S) (hb : b₀ ∉ S) :
    V a₀ - V b₀ = ∑ x ∈ S.filter (fun x => a₀ < x ∧ x < b₀), w x := by
  first
  | classical
    -- Induct on the number of events inside the interval. Isolate the first event,
    -- account for its jump, and apply the induction hypothesis to the remaining interval.
    have aux (a b : R) (haa : a₀ ≤ a) (hbb : b ≤ b₀)
        (hab : a < b) (ha : a ∉ S) (hb : b ∉ S) :
        V a - V b = ∑ x ∈ S.filter (fun x => a < x ∧ x < b), w x := by
      induction hn : (S.filter (fun x => a < x ∧ x < b)).card using Nat.strong_induction_on
          generalizing a b with
      | h n ih =>
        set T := S.filter (fun x => a < x ∧ x < b)
        by_cases hT : T.Nonempty
        · let r := T.min' hT
          have hrT : r ∈ T := Finset.min'_mem T hT
          obtain ⟨hrS, har, hrb⟩ := Finset.mem_filter.mp hrT
          obtain ⟨c, hrc, hcb, hc⟩ := exists_right_gap S hrb
          have hcS : c ∉ S := fun hcS => (hc c hcS hrc).false
          have hsingle : ∀ x ∈ S, x ∈ Set.Icc a c → x = r := by
            intro x hx haxc
            have hax : a < x := haxc.1.lt_of_ne (by rintro rfl; exact ha hx)
            have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hax, haxc.2.trans_lt hcb⟩
            have hrx : r ≤ x := Finset.min'_le T x hxT
            by_contra hne
            have hrcx := hc x hx (hrx.lt_of_ne (Ne.symm hne))
            exact hrcx.not_ge haxc.2
          let U := S.filter (fun x => c < x ∧ x < b)
          have hrU : r ∉ U := by
            simp only [U, Finset.mem_filter]
            rintro ⟨_, hcr, _⟩
            exact hcr.not_gt hrc
          have hTU : T = insert r U := by
            ext x
            constructor
            · intro hx
              obtain ⟨hxS, hax, hxb⟩ := Finset.mem_filter.mp hx
              by_cases hxr : x = r
              · exact Finset.mem_insert.mpr (Or.inl hxr)
              · apply Finset.mem_insert.mpr
                right
                refine Finset.mem_filter.mpr ⟨hxS, ?_, hxb⟩
                by_contra! hxc
                exact hxr (hsingle x hxS ⟨hax.le, hxc⟩)
            · intro hx
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact hrT
              · obtain ⟨hxS, hcx, hxb⟩ := Finset.mem_filter.mp hx
                exact Finset.mem_filter.mpr ⟨hxS, har.trans (hrc.trans hcx), hxb⟩
          have hcard : U.card < n := by
            have heq : T.card = U.card + 1 := by rw [hTU, Finset.card_insert_of_notMem hrU]
            omega
          have hlocal := hjump a r c haa (hcb.le.trans hbb) har hrc hrS hsingle
          have hrest : V c - V b = ∑ x ∈ U, w x :=
            ih U.card hcard c b (haa.trans (har.trans hrc).le) hbb hcb hcS hb rfl
          rw [hTU, Finset.sum_insert hrU]
          calc
            V a - V b = (V a - V c) + (V c - V b) := by abel
            _ = w r + ∑ x ∈ U, w x := by rw [hlocal, hrest]
        · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
          have hno : ∀ x ∈ S, x ∉ Set.Icc a b := by
            intro x hx hxab
            have hax : a < x := hxab.1.lt_of_ne (by rintro rfl; exact ha hx)
            have hxb : x < b := hxab.2.lt_of_ne (by rintro rfl; exact hb hx)
            have : x ∈ T := Finset.mem_filter.mpr ⟨hx, hax, hxb⟩
            simp [hT0] at this
          simp [hT0, hconst a b haa hbb hab hno]
    exact aux a₀ b₀ le_rfl le_rfl hab ha hb

end Finset
end -- closes the original EOF section from source line 20
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Finset/Jumps.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/RealClosed/Sign.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Polynomial signs between roots in a real closed field

Signs are constant on root-free intervals. Up to the next root on either side of a point,
a polynomial has the algebraic one-sided signs `derivSignLeft` and `derivSignRight` of that point.
Consequently a polynomial changes sign across an isolated root exactly when the root has odd
multiplicity, and at a simple root the signs on either side are determined by the sign of the
derivative. Between two nonroots, the change of sign is the sum of the jumps
`derivSignRight - derivSignLeft` of the one-sided signs at the roots in between.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapter 2.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A polynomial has a constant sign on a root-free interval. -/
theorem sign_eval_const (p : R[X]) {a b : R} (hab : a ≤ b)
    (hz : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
  first
  | rcases mul_pos_iff.mp (p.eval_mul_pos_of_no_roots hab hz) with h | h
    · rw [sign_pos h.1, sign_pos h.2]
    · rw [sign_neg h.1, sign_neg h.2]

/-- Up to its next root to the right of `r`, a polynomial has its right-hand sign at `r`. -/
theorem sign_eval_eq_derivSignRight (p : R[X]) {r b : R} (hrb : r < b)
    (hz : ∀ x ∈ Set.Ioc r b, p.eval x ≠ 0) :
    SignType.sign (p.eval b) = p.derivSignRight r := by
  first
  | obtain ⟨-, u, -, hu, -, hR⟩ := p.exists_derivSignLeft_derivSignRight r
    obtain ⟨y, hry, hy⟩ := exists_between (lt_min hu hrb)
    rw [← hR y ⟨hry, hy.trans_le (min_le_left _ _)⟩]
    exact (p.sign_eval_const (hy.trans_le (min_le_right _ _)).le
      fun x hx => hz x ⟨hry.trans_le hx.1, hx.2⟩).symm

/-- Up to its next root to the left of `r`, a polynomial has its left-hand sign at `r`. -/
theorem sign_eval_eq_derivSignLeft (p : R[X]) {a r : R} (har : a < r)
    (hz : ∀ x ∈ Set.Ico a r, p.eval x ≠ 0) :
    SignType.sign (p.eval a) = p.derivSignLeft r := by
  first
  | obtain ⟨l, -, hl, -, hL, -⟩ := p.exists_derivSignLeft_derivSignRight r
    obtain ⟨x, hx, hxr⟩ := exists_between (max_lt hl har)
    rw [← hL x ⟨(le_max_left _ _).trans_lt hx, hxr⟩]
    exact p.sign_eval_const ((le_max_right _ _).trans_lt hx).le
      fun y hy => hz y ⟨hy.1, hy.2.trans_lt hxr⟩

/-- If a polynomial has no zeros in `[a, b]` except possibly at an interior point `r`, its
endpoint signs are its one-sided signs at `r`. Multiple roots and nonroots are allowed. -/
theorem signs_at_isolated_point (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = p.derivSignLeft r ∧
      SignType.sign (p.eval b) = p.derivSignRight r :=
  ⟨p.sign_eval_eq_derivSignLeft har fun x hx => hz x ⟨hx.1, hx.2.le.trans hrb.le⟩ hx.2.ne,
    p.sign_eval_eq_derivSignRight hrb fun x hx => hz x ⟨har.le.trans hx.1.le, hx.2⟩ hx.1.ne'⟩

/-- A polynomial keeps its sign across an isolated point of `[a, b]` exactly when its root
multiplicity there is even. This includes a nonroot, of multiplicity zero. -/
theorem sign_eval_eq_sign_eval_iff_even_rootMultiplicity (p : R[X]) {a r b : R} (har : a < r)
    (hrb : r < b) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval b) ↔ Even (p.rootMultiplicity r) := by
  first
  | obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
    rw [ha, hb, derivSignLeft_eq_derivSignRight_iff]

/-- A polynomial changes sign across an isolated root in `[a, b]` exactly when the root has odd
multiplicity. -/
theorem sign_eval_eq_neg_sign_eval_iff_odd_rootMultiplicity (p : R[X]) {a r b : R} (har : a < r)
    (hrb : r < b) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = -SignType.sign (p.eval b) ↔ Odd (p.rootMultiplicity r) := by
  first
  | have hp : p ≠ 0 := fun h => hz b ⟨(har.trans hrb).le, le_rfl⟩ hrb.ne' (by simp [h])
    obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
    rw [ha, hb, derivSignLeft_eq_neg_derivSignRight_iff hp]

/-- If a polynomial has no zeros except possibly at an interior point, and does
not vanish there either, both endpoint signs agree with its sign at that point. -/
theorem signs_at_nonroot (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r ≠ 0) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval r) ∧
      SignType.sign (p.eval b) = SignType.sign (p.eval r) := by
  first
  | obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
    exact ⟨ha.trans (p.derivSignLeft_eq_sign_eval hr), hb.trans (p.derivSignRight_eq_sign_eval hr)⟩

/-- Near an isolated simple root, a polynomial changes from the negative
of its derivative's sign to its derivative's sign. -/
theorem signs_at_root (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0)
    (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = -SignType.sign (p.derivative.eval r) ∧
    SignType.sign (p.eval b) = SignType.sign (p.derivative.eval r) := by
  first
    -- At a root the derivative has the right-hand sign of `p` and the opposite left-hand sign.
  | have hL := derivSignLeft_derivative_of_isRoot (p := p) hr
    have hR := derivSignRight_derivative_of_isRoot (p := p) hr
    rw [derivSignLeft_eq_sign_eval _ hd] at hL
    rw [derivSignRight_eq_sign_eval _ hd] at hR
    obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
    exact ⟨ha.trans (by rw [hL, neg_neg]), hb.trans hR.symm⟩

/-- Between two nonroots, the change of sign of a polynomial is the sum of the jumps of its
one-sided signs at the roots in between. Multiple roots are allowed. -/
theorem sign_eval_sub_sign_eval_eq_sum (p : R[X]) {a b : R} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0) :
    (SignType.sign (p.eval b) : ℤ) - SignType.sign (p.eval a) =
      ∑ x ∈ p.roots.toFinset.filter (fun x => a < x ∧ x < b),
        ((p.derivSignRight x : ℤ) - p.derivSignLeft x) := by
  first
  | classical
    have hp : p ≠ 0 := fun h => ha (by simp [h])
    have hS (x : R) : x ∈ p.roots.toFinset ↔ p.eval x = 0 := by simp [mem_roots hp]
    -- Telescope the negated sign over the roots: it is constant on root-free intervals, and at an
    -- isolated root it changes by the jump of the one-sided signs.
    have h := Finset.sum_jumps p.roots.toFinset (fun x => -(SignType.sign (p.eval x) : ℤ))
      (fun x => (p.derivSignRight x : ℤ) - p.derivSignLeft x)
      (fun c d _ _ hcd hn => by
        rw [p.sign_eval_const hcd.le fun x hx hx0 => hn x ((hS x).2 hx0) hx])
      (fun c r d _ _ hcr hrd _ hn => by
        obtain ⟨hc, hd⟩ := p.signs_at_isolated_point hcr hrd fun x hx hxr hx0 =>
          hxr (hn x ((hS x).2 hx0) hx)
        rw [hc, hd]
        ring)
      hab (by simpa [hS] using ha) (by simpa [hS] using hb)
    rw [← h]
    ring

end Polynomial
end -- closes the original EOF section from source line 28
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/RealClosed/Sign.lean -/

/- BEGIN SOURCE: TauCeti/Data/Fintype/Fiber.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Occurrence counts in finite families

`occCount f y` counts the indices at which a family `f` takes the value `y`.
For an infinite fiber its value is zero, following the convention of `Nat.card`.
Occurrence counts regroup sums over a finite family by fibers: each value in a finite set
covering the range is weighted by its occurrence count.

## Main results

* `Function.occCount_pos`: for a finite fiber, the count is positive exactly when it is nonempty.
* `Function.occCount_of_injective`: an injective function has count one on its range
  and zero outside.
* `Function.occCount_le_of_comp`, `Function.occCount_lt_of_comp`: comparison along embeddings.
* `Function.occCount_eq_card_preimage`: the count as the cardinality of a singleton preimage.
* `Function.prod_occCount_pow` and its additive form `Function.sum_occCount_nsmul`:
  regroup a product or sum by counting the occurrences of each value.
* `Function.occCount_castSucc`, `Function.occCount_succ`: split off the last or first position.
* `Function.sum_occCount_eq_card`: the total occurrence count is the cardinality of the index type.
* `Function.exists_perm_of_occCount_eq`: equal counts on finite families give a permutation.
* `Function.occCount_eq_count_map_univ`: occurrence counts as multiset multiplicities.
* `Function.exists_perm_of_map_univ_eq`: equal multisets give a permutation.
* `Multiset.exists_map_univ_eq`: enumeration of a multiset by any type of matching size.

-/

public section

open Finset

namespace Function

variable {X S : Type*}

/-- The cardinality of a fiber, counting occurrences of a value in a family. -/
noncomputable def occCount (f : X → S) (y : S) : ℕ := Nat.card {x // f x = y}

/-- Occurrence counts are natural cardinalities of fibers. -/
theorem occCount_def (f : X → S) (y : S) :
    occCount f y = Nat.card {x // f x = y} := (rfl)

/-- The occurrence count is the `Finset.card` of the indices taking the given value. -/
theorem occCount_eq_card_filter [Fintype X] [DecidableEq S] (f : X → S) (y : S) :
    occCount f y = (Finset.univ.filter (fun x => f x = y)).card := by
  first
  | rw [occCount_def, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The occurrence count as a sum of indicators over the positions. -/
theorem occCount_eq_sum [Fintype X] [DecidableEq S] (w : X → S) (a : S) :
    occCount w a = ∑ i : X, if w i = a then 1 else 0 := by
  first
  | rw [occCount_eq_card_filter, card_filter]

/-- When the target fiber is finite, occurrence counts grow along an embedding
preserving the values. -/
theorem occCount_le_of_comp {Y : Type*} {u : X → S} {v : Y → S}
    (e : X ↪ Y) (he : ∀ i, v (e i) = u i) (a : S) [Finite {y // v y = a}] :
    occCount u a ≤ occCount v a := by
  first
  | let f : {x // u x = a} ↪ {y // v y = a} :=
      e.subtypeMap (fun {x} hx => (he x).trans hx)
    exact Nat.card_le_card_of_injective f f.injective

/-- When the target fiber is finite, an embedding that misses an occurrence gives a
strictly smaller occurrence count. -/
theorem occCount_lt_of_comp {Y : Type*} {u : X → S} {v : Y → S} {a : S}
    [Finite {y // v y = a}] {j : Y} (e : X ↪ Y) (he : ∀ i, v (e i) = u i)
    (hj : v j = a) (hmiss : ∀ i, e i ≠ j) : occCount u a < occCount v a := by
  first
  | let f : {x // u x = a} ↪ {y // v y = a} :=
      e.subtypeMap (fun {x} hx => (he x).trans hx)
    have : Finite {x // u x = a} := Finite.of_injective f f.injective
    let _ := Fintype.ofFinite {x // u x = a}
    let _ := Fintype.ofFinite {y // v y = a}
    rw [occCount_def, occCount_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_injective_not_surjective f f.injective
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj ⟨j, hj⟩
    exact hmiss x (congrArg Subtype.val hx)

/-- For a finite fiber, positive occurrence count is equivalent to the value being attained. -/
@[simp, grind =]
theorem occCount_pos (f : X → S) (y : S) [Finite {x // f x = y}] :
    0 < occCount f y ↔ ∃ x, f x = y := by
  first
  | simp only [occCount_def, Nat.card_pos_iff, nonempty_subtype,
      and_iff_left (inferInstance : Finite {x // f x = y})]

/-- Occurrence counts are the cardinalities of singleton preimages. -/
theorem occCount_eq_card_preimage (f : X → S) (y : S) :
    occCount f y = Nat.card (f ⁻¹' {y}) := by
  first
  | rw [occCount_def]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff])

/-- A value outside the range has occurrence count zero. -/
@[simp]
theorem occCount_of_notMem_range (f : X → S) (y : S) (h : y ∉ Set.range f) :
    occCount f y = 0 := by
  first
  | rw [occCount_eq_card_preimage, Set.preimage_singleton_eq_empty.mpr h]
    exact Nat.card_of_isEmpty

/-- An injective function gives occurrence count one precisely on its range. -/
theorem occCount_of_injective (f : X → S) (hinj : Function.Injective f) (y : S)
    [Decidable (∃ x, f x = y)] :
    occCount f y = if ∃ x, f x = y then 1 else 0 := by
  first
  | split_ifs with h
    · rw [occCount_eq_card_preimage]
      simpa only [Nat.card_unique] using
        Nat.card_preimage_of_injective hinj (Set.singleton_subset_iff.mpr h)
    · exact occCount_of_notMem_range f y h

/-- Every value of an injective function occurs exactly once. -/
@[simp]
theorem occCount_apply_of_injective (f : X → S) (hinj : Function.Injective f) (x : X) :
    occCount f (f x) = 1 := by
  first
  | classical
    rw [occCount_of_injective f hinj, ite_eq_left ⟨x, rfl⟩]

/-- Raising each weight to its occurrence count gives the product over all indices. -/
@[to_additive
  /-- Weighting each value by its occurrence count gives the sum over all indices. -/]
theorem prod_occCount_pow [Fintype X] {K : Type*} [CommMonoid K]
    (f : X → S) {T : Finset S} (hT : ∀ x, f x ∈ T) (weight : S → K) :
    ∏ y ∈ T, weight y ^ occCount f y = ∏ x, weight (f x) := by
  first
  | classical
    simpa only [Finset.prod_const, occCount_eq_card_filter] using
      Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := T) (g := f)
        (fun x _ => hT x) weight

/-- Occurrence counts over a finite set containing the range sum to the size of
the original family. -/
theorem sum_occCount_eq_card [Finite X] (f : X → S) {T : Finset S}
    (hT : ∀ x, f x ∈ T) : ∑ y ∈ T, occCount f y = Nat.card X := by
  first
  | classical
    let _ := Fintype.ofFinite X
    simpa [Nat.card_eq_fintype_card] using sum_occCount_nsmul f hT (fun _ => (1 : ℕ))

/-- Splitting off the last position: the occurrences of `a` in a word are those in its initial
segment together with a possible occurrence at the last position. -/
theorem occCount_castSucc [DecidableEq S] {n : ℕ} (w : Fin (n + 1) → S) (a : S) :
    occCount (w ∘ Fin.castSucc) a + (if w (Fin.last n) = a then 1 else 0) = occCount w a := by
  first
  | rw [occCount_eq_sum, occCount_eq_sum, Fin.sum_univ_castSucc]
    rfl

/-- Splitting off the first position: the occurrences of `a` in a word are those in its final
segment together with a possible occurrence at the first position. -/
theorem occCount_succ [DecidableEq S] {n : ℕ} (w : Fin (n + 1) → S) (a : S) :
    occCount (w ∘ Fin.succ) a + (if w 0 = a then 1 else 0) = occCount w a := by
  first
  | rw [occCount_eq_sum, occCount_eq_sum, Fin.sum_univ_succ, Nat.add_comm]
    rfl

/-- Two families on a finite index type with equal occurrence counts differ by a permutation. -/
theorem exists_perm_of_occCount_eq [Finite X] {u v : X → S}
    (h : ∀ a, occCount u a = occCount v a) :
    ∃ σ : Equiv.Perm X, v ∘ σ = u := by
  first
  | classical
    let _ := Fintype.ofFinite X
    refine ⟨Equiv.ofFiberEquiv (f := u) (g := v) fun c =>
      Fintype.equivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact (occCount_def u c).symm.trans ((h c).trans (occCount_def v c))), ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map _ i

/-- Occurrence counts are the multiplicities in the multiset of values of a finite family. -/
theorem occCount_eq_count_map_univ [Fintype X] [DecidableEq S] (f : X → S) (y : S) :
    occCount f y = (Finset.univ.val.map f).count y := by
  first
  | rw [occCount_eq_card_filter, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
    congr 1
    exact Finset.filter_congr fun _ _ => eq_comm

/-- Finite families with the same multiset of values differ by a permutation of their indices. -/
theorem exists_perm_of_map_univ_eq [Fintype X] {u v : X → S}
    (h : Finset.univ.val.map u = Finset.univ.val.map v) :
    ∃ σ : Equiv.Perm X, v ∘ σ = u := by
  first
  | classical
    apply exists_perm_of_occCount_eq
    intro a
    rw [occCount_eq_count_map_univ, occCount_eq_count_map_univ, h]

end Function

namespace Multiset

variable {X S : Type*}

/-- Any multiset with as many entries as a finite type can be enumerated by that type. -/
theorem exists_map_univ_eq [Fintype X] (s : Multiset S) (h : s.card = Fintype.card X) :
    ∃ f : X → S, Finset.univ.val.map f = s := by
  first
  | classical
    let e : X ≃ s := Fintype.equivOfCardEq (by simp [h])
    refine ⟨(fun x : s => (x : S)) ∘ e, ?_⟩
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Multiset.map_univ_coe]

end Multiset
end -- closes the original EOF section from source line 39
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Fintype/Fiber.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/SignDetermination/Defs.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Polynomial sign counts and Tarski queries

`Finset.signCount` counts the points of a finite set realizing a given polynomial
sign condition. `Finset.signSum` sums a polynomial's signs on that set.
`Polynomial.tarskiQuery p q` specializes the sum to the distinct roots of `p`.
For nonzero `p` its cardinality characterization counts the actual zeros of `p`;
for `p = 0` the value is zero and does not describe the infinite zero set.

The definitions and their basic API are independent of matrix inversion.
Sign counts and sign sums are unchanged when the points and polynomials are mapped through a
strictly monotone ring homomorphism (`Finset.signCount_map_image`, `Finset.signSum_map_image`).
Over a field, `Polynomial.tarskiQuery_integralNormalization` clears the leading coefficient of
the root polynomial, so Tarski queries can always be computed at a monic root polynomial.

The algebraic laws of Tarski queries follow. In the queried polynomial, the query depends only on
signs at the roots (`Polynomial.tarskiQuery_congr`), so it is unchanged by adding multiples of the
root polynomial or reducing modulo it, changes sign under negation, is multiplied by the sign of a
constant factor, and for a square counts the roots at which the polynomial does not vanish. In
the root polynomial, it depends only on the set of distinct roots: it is unchanged under
associates and positive powers, and is additive over products of coprime factors.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 10, for sign conditions and Tarski queries.
-/

public section

open Polynomial SignType
open Function (occCount occCount_eq_card_filter)

namespace Finset

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The number of points realizing a specified polynomial sign condition. -/
noncomputable def signCount {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) : ℕ :=
  occCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ

/-- Polynomial sign counts are multiplicities in the finite family of pointwise signs. -/
theorem signCount_eq_occCount {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = occCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ := (rfl)

open scoped Classical in
/-- Sign counts are cardinalities of the realizing subset of the original finite set. -/
theorem signCount_eq_card_filter {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = (Z.filter fun x => ∀ j, sign ((Q j).eval x) = σ j).card := by
  first
  | classical
    simp only [signCount_eq_occCount, occCount_eq_card_filter, Finset.card_filter,
      funext_iff]
    exact Finset.sum_coe_sort Z
      (fun x : R => if ∀ j, sign ((Q j).eval x) = σ j then (1 : ℕ) else 0)

@[simp, grind =]
theorem signCount_empty {J : Type*}
    (Q : J → R[X]) (σ : J → SignType) : signCount ∅ Q σ = 0 := by
  first
  | simp [signCount_eq_card_filter]

/-- The sign conditions partition the original finite set of points. -/
theorem sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) : ∑ σ, signCount Z Q σ = Z.card := by
  first
  | classical
    simpa only [signCount_eq_occCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
      Function.sum_occCount_eq_card (fun x : Z => fun j => sign ((Q j).eval x.val))
        (fun _ => Finset.mem_univ _)

/-- A positive sign count is equivalent to realization at a point of the finite set. -/
@[simp, grind =]
theorem signCount_pos {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount Z Q σ ↔ ∃ x ∈ Z, ∀ j, sign ((Q j).eval x) = σ j := by
  first
  | classical
    simp [signCount_eq_card_filter, Finset.card_pos, Finset.Nonempty]

/-- The integer sum of signs at a specified finite set of points. -/
noncomputable def signSum (Z : Finset R) (p : R[X]) : ℤ := ∑ x : Z, (sign (p.eval x.val) : ℤ)

/-- Sign sums are integer sums of pointwise polynomial signs. -/
theorem signSum_eq_sum_subtype (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x : Z, (sign (p.eval x.val) : ℤ) := (rfl)

/-- Sign sums expressed directly over the original finite set. -/
theorem signSum_eq_sum (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x ∈ Z, (sign (p.eval x) : ℤ) := by
  first
  | rw [signSum_eq_sum_subtype, Finset.sum_coe_sort Z (fun x : R => (sign (p.eval x) : ℤ))]

@[simp, grind =]
theorem signSum_empty (p : R[X]) : signSum ∅ p = 0 := by
  first
  | simp [signSum_eq_sum]

@[simp, grind =]
theorem signSum_zero (Z : Finset R) : signSum Z 0 = 0 := by
  first
  | simp [signSum_eq_sum]

@[simp, grind =]
theorem signSum_one [ZeroLEOneClass R] [NeZero (1 : R)] (Z : Finset R) : signSum Z 1 = Z.card := by
  first
  | simp [signSum_eq_sum]

/-- A finite sign sum is the number of positive evaluations minus the number of negative ones. -/
theorem signSum_eq_card_sub_card (Z : Finset R) (p : R[X]) :
    signSum Z p = ((Z.filter (fun x => 0 < p.eval x)).card : ℤ) -
      (Z.filter (fun x => p.eval x < 0)).card := by
  first
  | classical
    rw [signSum_eq_sum]
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hpos : 0 < p.eval x
    · have hneg : ¬ p.eval x < 0 := not_lt_of_ge hpos.le
      simp [hpos, hneg]
    · by_cases hneg : p.eval x < 0 <;> simp [sign_apply, hpos, hneg]

section Map

variable {S : Type*} [Semiring S] [LinearOrder S] [DecidableEq S] {f : R →+* S}

/-- Sign counts are preserved by mapping the points and the polynomials through a strictly
monotone ring homomorphism. -/
@[simp]
theorem signCount_map_image {J : Type*} (hf : StrictMono f) (Z : Finset R) (Q : J → R[X])
    (σ : J → SignType) :
    signCount (Z.image f) (fun j => (Q j).map f) σ = signCount Z Q σ := by
  first
  | classical
    rw [signCount_eq_card_filter, signCount_eq_card_filter, filter_image,
      card_image_of_injective _ hf.injective]
    simp only [sign_eval_map _ f hf]

/-- Sign sums are preserved by mapping the points and the polynomial through a strictly
monotone ring homomorphism. -/
@[simp]
theorem signSum_map_image (hf : StrictMono f) (Z : Finset R) (p : R[X]) :
    signSum (Z.image f) (p.map f) = signSum Z p := by
  first
  | rw [signSum_eq_sum, signSum_eq_sum, sum_image fun _ _ _ _ h => hf.injective h]
    simp only [sign_eval_map _ f hf]

end Map

end Basic

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Negating a polynomial negates its sign sum over a finite set of points. -/
@[simp]
theorem signSum_neg (Z : Finset R) (p : R[X]) : signSum Z (-p) = -signSum Z p := by
  first
  | simp [signSum_eq_sum, Left.sign_neg]

/-- Scaling a polynomial by a constant multiplies its sign sums by the sign of the constant. -/
@[simp]
theorem signSum_C_mul (Z : Finset R) (c : R) (p : R[X]) :
    signSum Z (C c * p) = sign c * signSum Z p := by
  first
  | simp [signSum_eq_sum, sign_mul, Finset.mul_sum]

end OrderedRing

section CommOrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The sign sum of a square counts the points at which the polynomial does not vanish. -/
theorem signSum_sq (Z : Finset R) (p : R[X]) :
    signSum Z (p ^ 2) = (Z.filter fun x => p.eval x ≠ 0).card := by
  first
  | classical
    rw [signSum_eq_sum, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [eval_pow, sign_pow]
    rcases lt_trichotomy (p.eval x) 0 with h | h | h
    · simp [h, h.ne]
    · simp [h]
    · simp [h, h.ne']

end CommOrderedRing

end Finset

namespace Polynomial

open Finset

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R]

/-- Sum of the signs of `q` at the distinct roots of `p`, with value zero when `p = 0`. -/
noncomputable def tarskiQuery (p q : R[X]) : ℤ := signSum p.roots.toFinset q

theorem tarskiQuery_eq_signSum (p q : R[X]) :
    tarskiQuery p q = signSum p.roots.toFinset q := (rfl)

/-- The Tarski query expressed as a sum over distinct polynomial roots. -/
theorem tarskiQuery_eq_sum (p q : R[X]) :
    tarskiQuery p q = ∑ x ∈ p.roots.toFinset, (sign (q.eval x) : ℤ) := by
  first
  | rw [tarskiQuery_eq_signSum, signSum_eq_sum]

/-- The number of distinct roots of `p` where `q` is positive minus the number
where `q` is negative. -/
theorem tarskiQuery_eq_card_sub_card (p q : R[X]) :
    tarskiQuery p q = ((p.roots.toFinset.filter (fun x => 0 < q.eval x)).card : ℤ) -
      (p.roots.toFinset.filter (fun x => q.eval x < 0)).card := by
  first
  | rw [tarskiQuery_eq_signSum, signSum_eq_card_sub_card]

/-- A Tarski query lies between minus the degree of its root polynomial and its degree. -/
theorem tarskiQuery_mem_Icc_natDegree (p q : R[X]) :
    tarskiQuery p q ∈ Set.Icc (-(p.natDegree : ℤ)) (p.natDegree : ℤ) := by
  first
  | rw [tarskiQuery_eq_card_sub_card]
    have hroots : p.roots.toFinset.card ≤ p.natDegree :=
      (Multiset.toFinset_card_le p.roots).trans (card_roots' p)
    have hpos := Finset.card_filter_le p.roots.toFinset (fun x => 0 < q.eval x)
    have hneg := Finset.card_filter_le p.roots.toFinset (fun x => q.eval x < 0)
    constructor <;> omega

@[simp, grind =]
theorem tarskiQuery_zero_left (q : R[X]) : tarskiQuery 0 q = 0 := by
  first
  | simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_zero_right (p : R[X]) : tarskiQuery p 0 = 0 := by
  first
  | simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_one_right [ZeroLEOneClass R] (p : R[X]) :
    tarskiQuery p 1 = p.roots.toFinset.card := by
  first
  | simp [tarskiQuery_eq_signSum]

/-- A Tarski query with a constant root polynomial is zero, including when the constant is zero. -/
@[simp, grind =]
theorem tarskiQuery_C_left (c : R) (q : R[X]) : tarskiQuery (C c) q = 0 := by
  first
  | simp [tarskiQuery_eq_signSum]

/-- A Tarski query depends only on the signs of the queried polynomial at the roots. -/
theorem tarskiQuery_congr {p q r : R[X]}
    (h : ∀ x ∈ p.roots, sign (q.eval x) = sign (r.eval x)) :
    tarskiQuery p q = tarskiQuery p r := by
  first
  | rw [tarskiQuery_eq_sum, tarskiQuery_eq_sum]
    exact Finset.sum_congr rfl fun x hx => by rw [h x (Multiset.mem_toFinset.mp hx)]

/-- Adding a multiple of `p` to the queried polynomial does not change the query, since it does
not change the values at the roots of `p`. -/
@[simp]
theorem tarskiQuery_add_mul (p q r : R[X]) : tarskiQuery p (q + p * r) = tarskiQuery p q :=
  tarskiQuery_congr fun x hx => by
    rw [eval_add, eval_mul, (isRoot_of_mem_roots hx).eq_zero, zero_mul, add_zero]

/-- Associated root polynomials have the same Tarski queries. -/
theorem _root_.Associated.tarskiQuery_eq {p s : R[X]} (h : Associated p s) (q : R[X]) :
    tarskiQuery p q = tarskiQuery s q := by
  first
  | rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, h.roots_eq]

/-- Multiplying the root polynomial by a nonzero constant leaves its Tarski queries unchanged. -/
@[simp]
theorem tarskiQuery_C_mul_left {c : R} (hc : c ≠ 0) (p q : R[X]) :
    tarskiQuery (C c * p) q = tarskiQuery p q := by
  first
  | rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, roots_C_mul _ hc]

/-- Negating the root polynomial leaves its Tarski queries unchanged. -/
@[simp]
theorem tarskiQuery_neg_left (p q : R[X]) : tarskiQuery (-p) q = tarskiQuery p q := by
  first
  | rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, roots_neg]

/-- A positive power of `p` has the same distinct roots as `p`, hence the same Tarski queries. -/
@[simp]
theorem tarskiQuery_pow_left (p q : R[X]) {n : ℕ} (hn : n ≠ 0) :
    tarskiQuery (p ^ n) q = tarskiQuery p q := by
  first
  | rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, roots_pow, Multiset.toFinset_nsmul _ _ hn]

/-- The query at the roots of a nonzero product of two polynomials without common roots is the
sum of the queries at the roots of the factors. -/
theorem tarskiQuery_mul_left_of_disjoint {p s : R[X]} (hps : p * s ≠ 0)
    (h : Disjoint p.roots.toFinset s.roots.toFinset) (q : R[X]) :
    tarskiQuery (p * s) q = tarskiQuery p q + tarskiQuery s q := by
  first
  | classical
    rw [tarskiQuery_eq_sum, tarskiQuery_eq_sum, tarskiQuery_eq_sum, roots_mul hps,
      Multiset.toFinset_add, Finset.sum_union h]

/-- The query at the roots of a product of coprime polynomials is the sum of the queries at the
roots of the factors. No nonvanishing hypothesis is needed: if one factor is zero, the other is
a unit and has no roots. -/
theorem tarskiQuery_mul_left_of_isCoprime {p s : R[X]} (h : IsCoprime p s) (q : R[X]) :
    tarskiQuery (p * s) q = tarskiQuery p q + tarskiQuery s q := by
  first
  | rcases eq_or_ne p 0 with rfl | hp
    · simp [tarskiQuery_eq_signSum,
        (associated_one_iff_isUnit.mpr (isCoprime_zero_left.mp h)).roots_eq]
    rcases eq_or_ne s 0 with rfl | hs
    · simp [tarskiQuery_eq_signSum,
        (associated_one_iff_isUnit.mpr (isCoprime_zero_right.mp h)).roots_eq]
    refine tarskiQuery_mul_left_of_disjoint (mul_ne_zero hp hs)
      (Finset.disjoint_left.mpr fun x hxp hxs => ?_) q
    simpa [coe_aeval_eq_eval, (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxp)).eq_zero,
      (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxs)).eq_zero] using
      aeval_ne_zero_of_isCoprime h x

/-- Counts at the roots of a nonzero polynomial count exactly its realizing zeros. -/
theorem signCount_roots_eq_natCard {J : Type*} {p : R[X]} (hp : p ≠ 0)
    (Q : J → R[X]) (σ : J → SignType) :
    signCount p.roots.toFinset Q σ =
      Nat.card {x : R // p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j} := by
  first
  | classical
    rw [signCount_eq_card_filter, ← Nat.card_eq_finsetCard]
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

/-- A Tarski query counts the zeros of `p` where `q` is positive, minus those
where `q` is negative. -/
theorem tarskiQuery_eq_sub {p : R[X]} (hp : p ≠ 0) (q : R[X]) :
    tarskiQuery p q = (Nat.card {x : R // p.eval x = 0 ∧ 0 < q.eval x} : ℤ) -
      Nat.card {x : R // p.eval x = 0 ∧ q.eval x < 0} := by
  first
  | classical
    rw [tarskiQuery_eq_card_sub_card]
    simp only [← Nat.card_eq_finsetCard, Finset.mem_filter, Multiset.mem_toFinset,
      mem_roots hp, IsRoot.def]

/-- A positive count at the roots of a nonzero polynomial is an actual realizable condition. -/
theorem signCount_roots_pos {J : Type*}
    {p : R[X]} (hp : p ≠ 0) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount p.roots.toFinset Q σ ↔
      ∃ x : R, p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j := by
  first
  | classical
    simp only [signCount_pos, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

end Basic

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Negating the queried polynomial negates the Tarski query. -/
@[simp]
theorem tarskiQuery_neg_right (p q : R[X]) : tarskiQuery p (-q) = -tarskiQuery p q := by
  first
  | rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum]
    exact signSum_neg _ _

/-- Scaling the queried polynomial by a constant multiplies the query by the sign of the
constant. -/
@[simp]
theorem tarskiQuery_C_mul_right (c : R) (p q : R[X]) :
    tarskiQuery p (C c * q) = sign c * tarskiQuery p q := by
  first
  | rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum]
    exact signSum_C_mul _ _ _

/-- The query of a square counts the distinct roots of `p` at which `q` does not vanish. -/
theorem tarskiQuery_sq_right (p q : R[X]) :
    tarskiQuery p (q ^ 2) = (p.roots.toFinset.filter fun x => q.eval x ≠ 0).card := by
  first
  | rw [tarskiQuery_eq_signSum]
    exact signSum_sq _ _

end OrderedRing

section Field

variable {R : Type*} [Field R] [LinearOrder R]

/-- **Clearing the leading coefficient of the root polynomial.** The distinct roots of the monic
polynomial `p.integralNormalization` are those of `p` multiplied by the leading coefficient `a`
of `p`. Hence a Tarski query of `p` equals one of `p.integralNormalization` against any `r`
whose sign at `a * x` agrees with the sign of `q` at each root `x` of `p`. -/
theorem tarskiQuery_integralNormalization {p q r : R[X]} (hp : p ≠ 0)
    (h : ∀ x, p.eval x = 0 → sign (r.eval (p.leadingCoeff * x)) = sign (q.eval x)) :
    tarskiQuery p.integralNormalization r = tarskiQuery p q := by
  first
  | classical
    have ha : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have hroots : p.integralNormalization.roots = p.roots.map (p.leadingCoeff * ·) := by
      rw [← roots_C_mul _ ha, mul_comm, integralNormalization_mul_C_leadingCoeff,
        roots_scaleRoots _ (isUnit_iff_ne_zero.mpr ha)]
    rw [tarskiQuery_eq_sum, tarskiQuery_eq_sum, hroots, Multiset.toFinset_map,
      Finset.sum_image fun x _ y _ hxy => mul_left_cancel₀ ha hxy]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [h x (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)).eq_zero]

/-- Reducing the queried polynomial modulo `p` does not change the query. -/
@[simp]
theorem tarskiQuery_mod (p q : R[X]) : tarskiQuery p (q % p) = tarskiQuery p q := by
  first
  | rw [EuclideanDomain.mod_eq_sub_mul_div, sub_eq_add_neg, ← mul_neg, tarskiQuery_add_mul]

end Field

end Polynomial
end -- closes the original EOF section from source line 44
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/SignDetermination/Defs.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/CauchyIndex/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # The Cauchy index of a quotient of polynomials

`Polynomial.cauchyJump p q a` is the jump of the rational function `q / p` at `a`. It is zero
unless `a` is a pole of `q / p` of odd order. At such a pole it is `+1` for a jump from `-∞` to
`+∞` and `-1` for a jump from `+∞` to `-∞`. The sign of `q / p` immediately to the right of `a`
is the right-hand sign of `p * q`, so the jump is defined algebraically from root multiplicities
and `Polynomial.derivSignRight`. It needs no topology and makes sense over any ordered field.
The jump is `1` exactly at a pole across which the sign of `p * q` changes from negative to
positive, and `-1` exactly at a pole where it changes from positive to negative. Over an ordered
field with its order topology, these are the poles at which `q / p` jumps from `-∞` to `+∞`, and
from `+∞` to `-∞` (`TauCeti.Analysis.Polynomial.CauchyJump`).

`Polynomial.cauchyIndex p q s` sums these jumps over a set `s`. Only roots of `p` contribute, so
the sum is finite. As for `Polynomial.tarskiQuery p q`, the first argument supplies the
denominator, and hence the roots. With this convention the index of `p' / p` counts distinct
roots, and the index of `p' * q / p` on the whole line is the Tarski query `TaQ(q, p)`.

The index depends only on the rational function `q / p`: cancelling a common factor does not
change it, and neither does reducing `q` modulo `p`. Negating the numerator or the denominator
reverses it, and scaling either by a constant multiplies it by the sign of the constant.
Jumps and indices are unchanged when the polynomials and the points are mapped through a strictly
monotone ring homomorphism. The inversion formula and Euclidean recurrence, including endpoint
roots, are in `TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Inversion`.

## Main declarations

* `Polynomial.cauchyJump`: the jump of `q / p` at a point.
* `Polynomial.cauchyIndex`: the sum of the jumps of `q / p` over a set.
* `Polynomial.cauchyJump_eq_one_iff`, `Polynomial.cauchyJump_eq_neg_one_iff`: the sign
  convention, by the one-sided signs of `p * q` at a pole.
* `Polynomial.cauchyIndex_neg_left`, `Polynomial.cauchyIndex_C_mul_left`,
  `Polynomial.cauchyIndex_C_mul_right`: negating and scaling the denominator or numerator.
* `Polynomial.cauchyIndex_mul_right`: cancellation of a common factor.
* `Polynomial.cauchyIndex_mod`: reduction of the numerator modulo the denominator.
* `Polynomial.cauchyIndex_map_image`: transport along a strictly monotone ring homomorphism.
* `Polynomial.cauchyIndex_derivative`: the index of `p' / p` counts distinct roots.
* `Polynomial.cauchyIndex_derivative_mul_univ`: the whole-line index of `p' * q / p` is
  `tarskiQuery p q`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (the Cauchy index and its properties).
-/

public section

namespace Polynomial

open SignType Set

section Definitions

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The jump of `q / p` at `a`. It is the right-hand sign of `p * q` at `a` when `a` is a pole
of `q / p` of odd order, and zero otherwise. -/
noncomputable def cauchyJump (p q : R[X]) (a : R) : ℤ :=
  if q.rootMultiplicity a < p.rootMultiplicity a ∧
      Odd (p.rootMultiplicity a - q.rootMultiplicity a) then
    ((p * q).derivSignRight a : ℤ)
  else 0

theorem cauchyJump_def (p q : R[X]) (a : R) :
    cauchyJump p q a =
      if q.rootMultiplicity a < p.rootMultiplicity a ∧
          Odd (p.rootMultiplicity a - q.rootMultiplicity a) then
        ((p * q).derivSignRight a : ℤ)
      else 0 := (rfl)

/-- The jump vanishes where `q / p` has no pole. -/
theorem cauchyJump_of_rootMultiplicity_le {p q : R[X]} {a : R}
    (h : p.rootMultiplicity a ≤ q.rootMultiplicity a) : cauchyJump p q a = 0 := by
  first
  | simp only [cauchyJump_def, ite_eq_right_iff]
    exact fun h' => absurd h'.1 (not_lt.mpr h)

/-- The jump vanishes away from the roots of `p`. -/
theorem cauchyJump_of_eval_ne_zero {p : R[X]} (q : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    cauchyJump p q a = 0 :=
  cauchyJump_of_rootMultiplicity_le (by simp [rootMultiplicity_eq_zero ha])

@[simp]
theorem cauchyJump_zero_left (q : R[X]) (a : R) : cauchyJump 0 q a = 0 :=
  cauchyJump_of_rootMultiplicity_le (by simp)

@[simp]
theorem cauchyJump_zero_right (p : R[X]) (a : R) : cauchyJump p 0 a = 0 := by
  first
  | simp [cauchyJump_def]

/-- A constant denominator has no poles. -/
@[simp]
theorem cauchyJump_C (c : R) (q : R[X]) (a : R) : cauchyJump (C c) q a = 0 := by
  first
  | rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact cauchyJump_of_eval_ne_zero q (by simpa using hc)

/-- The Cauchy index of `q / p` on `s`: the sum of the jumps of `q / p` at the points of `s`. -/
noncomputable def cauchyIndex (p q : R[X]) (s : Set R) : ℤ :=
  ∑ᶠ x ∈ s, cauchyJump p q x

theorem cauchyIndex_def (p q : R[X]) (s : Set R) :
    cauchyIndex p q s = ∑ᶠ x ∈ s, cauchyJump p q x := (rfl)

@[simp]
theorem cauchyIndex_empty (p q : R[X]) : cauchyIndex p q ∅ = 0 := by
  first
  | simp [cauchyIndex_def]

@[simp]
theorem cauchyIndex_singleton (p q : R[X]) (a : R) : cauchyIndex p q {a} = cauchyJump p q a := by
  first
  | simp [cauchyIndex_def]

@[simp]
theorem cauchyIndex_zero_left (q : R[X]) (s : Set R) : cauchyIndex 0 q s = 0 := by
  first
  | simp [cauchyIndex_def]

@[simp]
theorem cauchyIndex_zero_right (p : R[X]) (s : Set R) : cauchyIndex p 0 s = 0 := by
  first
  | simp [cauchyIndex_def]

@[simp]
theorem cauchyIndex_C (c : R) (q : R[X]) (s : Set R) : cauchyIndex (C c) q s = 0 := by
  first
  | simp [cauchyIndex_def]

section Map

variable {S : Type*} [CommRing S] [LinearOrder S] {f : R →+* S}

/-- Jumps are preserved by mapping the polynomials and the point through a strictly monotone
ring homomorphism. -/
@[simp]
theorem cauchyJump_map (hf : StrictMono f) (p q : R[X]) (a : R) :
    cauchyJump (p.map f) (q.map f) (f a) = cauchyJump p q a := by
  first
  | rw [cauchyJump_def, cauchyJump_def, ← eq_rootMultiplicity_map hf.injective,
      ← eq_rootMultiplicity_map hf.injective, ← Polynomial.map_mul, derivSignRight_map _ f hf]

/-- Cauchy indices are preserved by mapping the polynomials and the set through a strictly
monotone ring homomorphism. -/
@[simp]
theorem cauchyIndex_map_image (hf : StrictMono f) (p q : R[X]) (s : Set R) :
    cauchyIndex (p.map f) (q.map f) (f '' s) = cauchyIndex p q s := by
  first
  | rw [cauchyIndex_def, cauchyIndex_def, finsum_mem_image hf.injective.injOn]
    simp only [cauchyJump_map hf]

end Map

end Definitions

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Only roots of `p` carry a jump of `q / p`. -/
theorem support_cauchyJump_subset (p q : R[X]) :
    Function.support (cauchyJump p q) ⊆ p.roots.toFinset := by
  first
  | intro x hx
    by_cases hp : p = 0
    · simp [hp] at hx
    by_contra hr
    exact hx (cauchyJump_of_eval_ne_zero q (by simpa [mem_roots hp] using hr))

/-- Only finitely many points carry a jump of `q / p`. -/
theorem finite_support_cauchyJump (p q : R[X]) : (Function.support (cauchyJump p q)).Finite :=
  p.roots.toFinset.finite_toSet.subset (support_cauchyJump_subset p q)

/-- Negating the numerator reverses every Cauchy jump. -/
@[simp]
theorem cauchyJump_neg_right (p q : R[X]) (a : R) :
    cauchyJump p (-q) a = -cauchyJump p q a := by
  first
  | simp only [cauchyJump_def, rootMultiplicity_neg, mul_neg, derivSignRight_neg, SignType.coe_neg]
    split_ifs <;> simp

/-- Negating the numerator reverses the Cauchy index on any set. -/
@[simp]
theorem cauchyIndex_neg_right (p q : R[X]) (s : Set R) :
    cauchyIndex p (-q) s = -cauchyIndex p q s := by
  first
  | simp_rw [cauchyIndex_def, cauchyJump_neg_right, finsum_neg_distrib]

/-- Negating the denominator reverses every Cauchy jump. -/
@[simp]
theorem cauchyJump_neg_left (p q : R[X]) (a : R) :
    cauchyJump (-p) q a = -cauchyJump p q a := by
  first
  | simp only [cauchyJump_def, rootMultiplicity_neg, neg_mul, derivSignRight_neg, SignType.coe_neg]
    split_ifs <;> simp

/-- Negating the denominator reverses the Cauchy index on any set. -/
@[simp]
theorem cauchyIndex_neg_left (p q : R[X]) (s : Set R) :
    cauchyIndex (-p) q s = -cauchyIndex p q s := by
  first
  | simp_rw [cauchyIndex_def, cauchyJump_neg_left, finsum_neg_distrib]

/-- Scaling the denominator by a constant `c` multiplies every Cauchy jump by the sign
of `c`. -/
theorem cauchyJump_C_mul_left (c : R) (p q : R[X]) (a : R) :
    cauchyJump (C c * p) q a = sign c * cauchyJump p q a := by
  first
  | by_cases hc : c = 0
    · simp [hc]
    by_cases hp : p = 0
    · simp [hp]
    rw [cauchyJump_def, cauchyJump_def, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hc) hp),
      rootMultiplicity_C, zero_add, mul_assoc, derivSignRight_mul, derivSignRight_C]
    split_ifs <;> simp

/-- Scaling the denominator by a constant `c` multiplies the Cauchy index on any set by
the sign of `c`. -/
theorem cauchyIndex_C_mul_left (c : R) (p q : R[X]) (s : Set R) :
    cauchyIndex (C c * p) q s = sign c * cauchyIndex p q s := by
  first
  | simp_rw [cauchyIndex_def, cauchyJump_C_mul_left, mul_finsum_mem]

/-- Scaling the numerator by a constant `c` multiplies every Cauchy jump by the sign
of `c`. -/
theorem cauchyJump_C_mul_right (c : R) (p q : R[X]) (a : R) :
    cauchyJump p (C c * q) a = sign c * cauchyJump p q a := by
  first
  | by_cases hc : c = 0
    · simp [hc]
    by_cases hq : q = 0
    · simp [hq]
    rw [cauchyJump_def, cauchyJump_def, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hc) hq),
      rootMultiplicity_C, zero_add, mul_left_comm, derivSignRight_mul, derivSignRight_C]
    split_ifs <;> simp

/-- Scaling the numerator by a constant `c` multiplies the Cauchy index on any set by
the sign of `c`. -/
theorem cauchyIndex_C_mul_right (c : R) (p q : R[X]) (s : Set R) :
    cauchyIndex p (C c * q) s = sign c * cauchyIndex p q s := by
  first
  | simp_rw [cauchyIndex_def, cauchyJump_C_mul_right, mul_finsum_mem]

/-- **The sign convention of the Cauchy jump.** The jump of `q / p` at `a` is `1` exactly when
`a` is a pole of `q / p` across which its sign, which is the sign of `p * q`, changes from
negative on the left to positive on the right. -/
theorem cauchyJump_eq_one_iff {p q : R[X]} {a : R} :
    cauchyJump p q a = 1 ↔ q.rootMultiplicity a < p.rootMultiplicity a ∧
      (p * q).derivSignLeft a = -1 ∧ (p * q).derivSignRight a = 1 := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    by_cases hq : q = 0
    · simp [hq]
    rw [cauchyJump_def, derivSignLeft_def, rootMultiplicity_mul (mul_ne_zero hp hq)]
    generalize (p * q).derivSignRight a = s
    generalize p.rootMultiplicity a = m
    generalize q.rootMultiplicity a = n
    by_cases hnm : n < m
    · -- Across a pole, the parity of the order `m - n` is the parity of `m + n`.
      have hodd : Odd (m - n) ↔ Odd (m + n) := (Nat.odd_sub hnm.le).trans Nat.odd_add.symm
      rcases Nat.even_or_odd (m + n) with he | ho
      · simp only [hnm, hodd, Nat.not_odd_iff_even.mpr he, he.neg_one_pow, one_mul, true_and,
          and_false, ite_false]
        cases s <;> decide
      · simp only [hnm, hodd, ho, ho.neg_one_pow, true_and, and_self, ite_true]
        cases s <;> decide
    · simp [hnm]

/-- The jump of `q / p` at `a` is `-1` exactly when `a` is a pole of `q / p` across which its
sign, which is the sign of `p * q`, changes from positive on the left to negative on the
right. -/
theorem cauchyJump_eq_neg_one_iff {p q : R[X]} {a : R} :
    cauchyJump p q a = -1 ↔ q.rootMultiplicity a < p.rootMultiplicity a ∧
      (p * q).derivSignLeft a = 1 ∧ (p * q).derivSignRight a = -1 := by
  first
  | rw [← neg_inj, ← cauchyJump_neg_right, neg_neg, cauchyJump_eq_one_iff, rootMultiplicity_neg,
      mul_neg,
      derivSignLeft_neg, derivSignRight_neg, neg_inj, neg_eq_iff_eq_neg]

/-- The Cauchy index as a finite sum over the distinct roots of `p` in `s`. -/
theorem cauchyIndex_eq_sum (p q : R[X]) (s : Set R) [DecidablePred (· ∈ s)] :
    cauchyIndex p q s = ∑ x ∈ p.roots.toFinset with x ∈ s, cauchyJump p q x := by
  first
  | rw [cauchyIndex_def]
    refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
    ext x
    simp only [mem_inter_iff, Finset.coe_filter, mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨support_cauchyJump_subset p q h.2, h.1⟩, h.2⟩,
      fun h => ⟨h.1.2, h.2⟩⟩

/-- The Cauchy index on a set depends only on which roots of `p` the set contains. -/
theorem cauchyIndex_congr_of_isRoot {p : R[X]} (q : R[X]) {s t : Set R}
    (h : ∀ r, p.IsRoot r → (r ∈ s ↔ r ∈ t)) : cauchyIndex p q s = cauchyIndex p q t := by
  first
  | classical
    rw [cauchyIndex_eq_sum, cauchyIndex_eq_sum]
    exact Finset.sum_congr (Finset.filter_congr fun r hr =>
      h r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))) fun _ _ => rfl

/-- The Cauchy index is additive over disjoint sets. -/
theorem cauchyIndex_union (p q : R[X]) {s t : Set R} (h : Disjoint s t) :
    cauchyIndex p q (s ∪ t) = cauchyIndex p q s + cauchyIndex p q t :=
  finsum_mem_union' h ((finite_support_cauchyJump p q).inter_of_right s)
    ((finite_support_cauchyJump p q).inter_of_right t)

/-- Adding a point to a set adds the jump at that point to the Cauchy index. -/
theorem cauchyIndex_insert (p q : R[X]) {a : R} {s : Set R} (h : a ∉ s) :
    cauchyIndex p q (insert a s) = cauchyJump p q a + cauchyIndex p q s :=
  finsum_mem_insert' _ h ((finite_support_cauchyJump p q).inter_of_right s)

/-- Splitting an open interval at an interior point adds the jump at that point. -/
theorem cauchyIndex_Ioo_eq_add {p q : R[X]} {a b c : R} (hab : a < b) (hbc : b < c) :
    cauchyIndex p q (Ioo a c) =
      cauchyIndex p q (Ioo a b) + cauchyJump p q b + cauchyIndex p q (Ioo b c) := by
  first
  | have hdisj : Disjoint (Ioc a b) (Ioo b c) :=
      disjoint_left.mpr fun _ hx hx' ↦ hx'.1.not_ge hx.2
    rw [← Ioc_union_Ioo_eq_Ioo hab.le hbc, cauchyIndex_union _ _ hdisj,
      ← Ioo_insert_right hab, cauchyIndex_insert _ _ (by simp)]
    ring

/-- Cancelling a common nonzero factor of `p` and `q` does not change the jumps of `q / p`. -/
theorem cauchyJump_mul_right (p q : R[X]) {r : R[X]} (hr : r ≠ 0) (a : R) :
    cauchyJump (p * r) (q * r) a = cauchyJump p q a := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    by_cases hq : q = 0
    · simp [hq]
    have hs : p.derivSignRight a * r.derivSignRight a * (q.derivSignRight a * r.derivSignRight a) =
        p.derivSignRight a * q.derivSignRight a := by
      have h0 : r.derivSignRight a ≠ 0 := by simpa using hr
      generalize p.derivSignRight a = s at *
      generalize q.derivSignRight a = t at *
      generalize r.derivSignRight a = u at *
      cases s <;> cases t <;> cases u <;> simp_all
    simp only [cauchyJump_def, rootMultiplicity_mul (mul_ne_zero hp hr),
      rootMultiplicity_mul (mul_ne_zero hq hr), Nat.add_sub_add_right, Nat.add_lt_add_iff_right,
      derivSignRight_mul, hs]

/-- Cancelling a common nonzero factor of `p` and `q` does not change the index of `q / p`. -/
theorem cauchyIndex_mul_right (p q : R[X]) {r : R[X]} (hr : r ≠ 0) (s : Set R) :
    cauchyIndex (p * r) (q * r) s = cauchyIndex p q s := by
  first
  | simp only [cauchyIndex_def, cauchyJump_mul_right p q hr]

/-- Adding a multiple of `p` to `q` does not change the jumps of `q / p`. -/
theorem cauchyJump_add_mul (p q r : R[X]) (a : R) :
    cauchyJump p (q + p * r) a = cauchyJump p q a := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    by_cases hr : r = 0
    · simp [hr]
    by_cases hq : q = 0
    · rw [hq, zero_add, cauchyJump_zero_right]
      exact cauchyJump_of_rootMultiplicity_le
        (by rw [rootMultiplicity_mul (mul_ne_zero hp hr)]; omega)
    rcases lt_or_ge (q.rootMultiplicity a) (p.rootMultiplicity a) with h | h
    · -- At a pole of `q / p`, the term `p * r` vanishes to higher order than `q`.
      have hd : (X - C a) ^ (q.rootMultiplicity a + 1) ∣ p * r :=
        (pow_dvd_pow _ h).trans ((pow_rootMultiplicity_dvd p a).mul_right r)
      rw [cauchyJump_def, cauchyJump_def, rootMultiplicity_add_eq_left_of_dvd hq hd,
        derivSignRight_mul, derivSignRight_mul, derivSignRight_add_eq_left_of_dvd hq hd]
    · -- Away from poles of `q / p`, there is no pole of `(q + p * r) / p` either.
      rw [cauchyJump_of_rootMultiplicity_le h]
      by_cases hs : q + p * r = 0
      · simp [hs]
      refine cauchyJump_of_rootMultiplicity_le ((le_min h ?_).trans (rootMultiplicity_add a hs))
      rw [rootMultiplicity_mul (mul_ne_zero hp hr)]
      omega

/-- Adding a multiple of `p` to `q` does not change the index of `q / p`. -/
theorem cauchyIndex_add_mul (p q r : R[X]) (s : Set R) :
    cauchyIndex p (q + p * r) s = cauchyIndex p q s := by
  first
  | simp only [cauchyIndex_def, cauchyJump_add_mul]

/-- The jumps of `q / p` and of `p / q` at a point add up to half the jump of the one-sided
signs of `p * q` there. -/
theorem two_mul_cauchyJump_add_cauchyJump (p q : R[X]) (a : R) :
    2 * (cauchyJump p q a + cauchyJump q p a) =
      ((p * q).derivSignRight a : ℤ) - (p * q).derivSignLeft a := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    by_cases hq : q = 0
    · simp [hq]
    have hl : ((p * q).derivSignLeft a : ℤ) =
        (-1) ^ (p.rootMultiplicity a + q.rootMultiplicity a) * (p * q).derivSignRight a := by
      rw [derivSignLeft_def, rootMultiplicity_mul (mul_ne_zero hp hq)]
      simp
    rw [hl, cauchyJump_def, cauchyJump_def, mul_comm q p]
    generalize ((p * q).derivSignRight a : ℤ) = s
    generalize p.rootMultiplicity a = m
    generalize q.rootMultiplicity a = n
    -- Only the side with the larger multiplicity can jump, and only at an odd difference,
    -- which has the parity of the multiplicity `m + n` of `p * q`.
    have key (hpar : Prop) [Decidable hpar] (h : hpar ↔ Odd (m + n)) :
        2 * (if hpar then s else 0) = s - (-1) ^ (m + n) * s := by
      rcases Nat.even_or_odd (m + n) with he | ho
      · simp [h, he.neg_one_pow, Nat.not_odd_iff_even.mpr he]
      · simp [h, ho.neg_one_pow, ho]
        ring
    rcases lt_trichotomy n m with h | rfl | h
    · simpa [h, not_lt_of_gt h] using key _ ((Nat.odd_sub h.le).trans Nat.odd_add.symm)
    · simp [← two_mul, pow_mul]
    · simpa [h, not_lt_of_gt h] using key _ ((Nat.odd_sub h.le).trans Nat.odd_add'.symm)

/-- At a root of a nonzero `p`, the jump of `p' * q / p` is the sign of `q`. -/
theorem cauchyJump_derivative_mul {p : R[X]} (hp : p ≠ 0) (q : R[X]) {a : R}
    (ha : p.eval a = 0) : cauchyJump p (derivative p * q) a = sign (q.eval a) := by
  first
  | have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
    have hd : derivative p ≠ 0 := by
      rw [Ne, derivative_eq_zero]
      intro h
      rw [eq_C_of_natDegree_eq_zero h, eval_C] at ha
      exact hp (by rw [eq_C_of_natDegree_eq_zero h, ha, C_0])
    by_cases hq : q.eval a = 0
    · rw [hq, sign_zero, SignType.coe_zero]
      by_cases hq0 : q = 0
      · simp [hq0]
      refine cauchyJump_of_rootMultiplicity_le ?_
      rw [rootMultiplicity_mul (mul_ne_zero hd hq0), derivative_rootMultiplicity_of_root ha]
      have := (rootMultiplicity_pos hq0).mpr hq
      omega
    have hq0 : q ≠ 0 := fun h => hq (by simp [h])
    have hsp : p.derivSignRight a * p.derivSignRight a = 1 := by
      have h0 : p.derivSignRight a ≠ 0 := by simpa using hp
      generalize p.derivSignRight a = u at *
      cases u <;> simp_all
    -- `a` is a simple pole of `p' * q / p`.
    have hpole : p.rootMultiplicity a - 1 < p.rootMultiplicity a ∧
        Odd (p.rootMultiplicity a - (p.rootMultiplicity a - 1)) :=
      ⟨Nat.sub_lt hm one_pos, by rw [Nat.sub_sub_self hm]; exact odd_one⟩
    rw [cauchyJump_def, rootMultiplicity_mul (mul_ne_zero hd hq0),
      derivative_rootMultiplicity_of_root ha, rootMultiplicity_eq_zero hq, add_zero]
    simp only [hpole, and_self, ite_true]
    rw [← mul_assoc, derivSignRight_mul, derivSignRight_mul,
      derivSignRight_derivative_of_isRoot ha, hsp, one_mul,
      derivSignRight_eq_sign_eval q hq]

/-- The index of `p' * q / p` on `s` is the sum of the signs of `q` at the distinct roots of
`p` in `s`. -/
theorem cauchyIndex_derivative_mul (p q : R[X]) (s : Set R) [DecidablePred (· ∈ s)] :
    cauchyIndex p (derivative p * q) s =
      ∑ x ∈ p.roots.toFinset with x ∈ s, (sign (q.eval x) : ℤ) := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    rw [cauchyIndex_eq_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx : p.eval x = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1)
    exact cauchyJump_derivative_mul hp q hx

/-- The whole-line index of `p' * q / p` is the Tarski query of `q` at the roots of `p`. -/
theorem cauchyIndex_derivative_mul_univ (p q : R[X]) :
    cauchyIndex p (derivative p * q) univ = tarskiQuery p q := by
  first
  | classical
    rw [cauchyIndex_derivative_mul, tarskiQuery_eq_sum]
    simp

/-- The index of `p' / p` on `s` is the number of distinct roots of `p` in `s`. -/
theorem cauchyIndex_derivative (p : R[X]) (s : Set R) [DecidablePred (· ∈ s)] :
    cauchyIndex p (derivative p) s = (p.roots.toFinset.filter (· ∈ s)).card := by
  first
  | simpa using cauchyIndex_derivative_mul p 1 s

end OrderedRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Reducing `q` modulo `p` does not change the jumps of `q / p`. -/
theorem cauchyJump_mod (p q : R[X]) (a : R) : cauchyJump p (q % p) a = cauchyJump p q a := by
  first
  | rw [EuclideanDomain.mod_eq_sub_mul_div, sub_eq_add_neg, ← mul_neg, cauchyJump_add_mul]

/-- Reducing `q` modulo `p` does not change the index of `q / p`. -/
theorem cauchyIndex_mod (p q : R[X]) (s : Set R) : cauchyIndex p (q % p) s = cauchyIndex p q s := by
  first
  | simp only [cauchyIndex_def, cauchyJump_mod]

end Field

end Polynomial
end -- closes the original EOF section from source line 58
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/CauchyIndex/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/CauchyIndex/Inversion.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Inversion and Euclidean recurrence for Cauchy indices

The indices of `q / p` and `p / q` on a bounded interval add up to half the
change in the one-sided signs of `p * q`. This gives a Euclidean recurrence
without excluding poles or common roots at either endpoint.

An excluded endpoint uses the sign inside the interval; an included endpoint
uses the sign outside it. Thus the open interval uses the right-hand sign at
the left endpoint and the left-hand sign at the right endpoint. All four
bounded interval conventions are provided, including singleton closed intervals.
Zero polynomials and common factors are allowed throughout.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (the Cauchy index and its inversion formula).
-/

public section

namespace TauCeti

open _root_.Polynomial Set SignType

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

private theorem inversion_of_eval_ne_zero {p q : R[X]} {a b : R} (hab : a < b)
    (ha : (p * q).eval a ≠ 0) (hb : (p * q).eval b ≠ 0) :
    2 * (cauchyIndex p q (Ioo a b) + cauchyIndex q p (Ioo a b)) =
      (sign ((p * q).eval b) : ℤ) - sign ((p * q).eval a) := by
  first
  | have hpq : p * q ≠ 0 := fun h => ha (by simp [h])
    rw [sign_eval_sub_sign_eval_eq_sum _ hab ha hb, cauchyIndex_def, cauchyIndex_def,
      ← finsum_mem_add_distrib' ((finite_support_cauchyJump p q).inter_of_right _)
        ((finite_support_cauchyJump q p).inter_of_right _), mul_finsum_mem]
    simp_rw [two_mul_cauchyJump_add_cauchyJump]
    refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
    ext x
    simp only [mem_inter_iff, Finset.coe_filter, mem_ofPred_eq, Function.mem_support, mem_Ioo,
      Multiset.mem_toFinset, mem_roots hpq, IsRoot.def]
    refine ⟨fun h => ⟨⟨by_contra fun hx => h.2 ?_, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
    rw [derivSignRight_eq_sign_eval _ hx, derivSignLeft_eq_sign_eval _ hx, sub_self]

/-- **Inversion on an open interval.** The endpoint signs are taken inside the interval,
so poles and common roots at the endpoints need no special cases. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Ioo (p q : R[X])
    {a b : R} (hab : a < b) :
    2 * (cauchyIndex p q (Ioo a b) + cauchyIndex q p (Ioo a b)) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignRight a := by
  first
  | classical
    by_cases hp : p = 0
    · simp [hp]
    by_cases hq : q = 0
    · simp [hq]
    -- Move both endpoints inward to nonroots, preserving the indices and endpoint signs.
    obtain ⟨u, hau, hu⟩ := [p, q].exists_signs_right a
    obtain ⟨l, hlb, hl⟩ := [p, q].exists_signs_left b
    obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hau hab)
    obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hlb (ha'.trans_le (min_le_right _ _)))
    have ha'u : a' ∈ Ioo a u := ⟨haa', ha'.trans_le (min_le_left _ _)⟩
    have hb'l : b' ∈ Ioo l b := ⟨(le_max_left _ _).trans_lt hb', hb'b⟩
    have hindex (r s : R[X]) (hr : r ∈ [p, q]) (hr0 : r ≠ 0) :
        cauchyIndex r s (Ioo a b) = cauchyIndex r s (Ioo a' b') := by
      rw [cauchyIndex_def, cauchyIndex_def]
      apply finsum_mem_inter_support_eq'
      intro x hx
      constructor
      · intro hxab
        have ha'x : a' < x := by
          by_contra h
          exact hx (cauchyJump_of_eval_ne_zero s
            (eval_ne_zero_of_sign_eq_derivSignRight hr0
              (hu r hr x ⟨hxab.1, (not_lt.mp h).trans_lt ha'u.2⟩)))
        have hxb' : x < b' := by
          by_contra h
          exact hx (cauchyJump_of_eval_ne_zero s
            (eval_ne_zero_of_sign_eq_derivSignLeft hr0
              (hl r hr x ⟨hb'l.1.trans_le (not_lt.mp h), hxab.2⟩)))
        exact ⟨ha'x, hxb'⟩
      · exact fun hx => ⟨haa'.trans hx.1, hx.2.trans hb'b⟩
    have hpa := hu p (by simp) a' ha'u
    have hqa := hu q (by simp) a' ha'u
    have hpb := hl p (by simp) b' hb'l
    have hqb := hl q (by simp) b' hb'l
    rw [hindex p q (by simp) hp, hindex q p (by simp) hq,
      inversion_of_eval_ne_zero ((le_max_right _ _).trans_lt hb')
        (by simpa using (mul_ne_zero (eval_ne_zero_of_sign_eq_derivSignRight hp hpa)
          (eval_ne_zero_of_sign_eq_derivSignRight hq hqa)))
        (by simpa using (mul_ne_zero (eval_ne_zero_of_sign_eq_derivSignLeft hp hpb)
          (eval_ne_zero_of_sign_eq_derivSignLeft hq hqb)))]
    simp only [eval_mul, sign_mul, hpa, hqa, hpb, hqb, derivSignLeft_mul, derivSignRight_mul]

/-- Inversion on a left-open, right-closed interval uses right-hand signs at both endpoints. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Ioc (p q : R[X])
    {a b : R} (hab : a ≤ b) :
    2 * (cauchyIndex p q (Ioc a b) + cauchyIndex q p (Ioc a b)) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignRight a := by
  first
  | rcases hab.eq_or_lt with rfl | hab
    · simp
    have hi (r s : R[X]) :
        cauchyIndex r s (Ioc a b) = cauchyIndex r s (Ioo a b) + cauchyJump r s b := by
      rw [← Ioo_insert_right hab, insert_eq, union_comm,
        cauchyIndex_union _ _ (disjoint_singleton_right.mpr (by simp)), cauchyIndex_singleton]
    have h := two_mul_cauchyIndex_add_cauchyIndex_Ioo p q hab
    have hj := two_mul_cauchyJump_add_cauchyJump p q b
    rw [hi, hi]
    linarith

/-- Inversion on a left-closed, right-open interval uses left-hand signs at both endpoints. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Ico (p q : R[X])
    {a b : R} (hab : a ≤ b) :
    2 * (cauchyIndex p q (Ico a b) + cauchyIndex q p (Ico a b)) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignLeft a := by
  first
  | rcases hab.eq_or_lt with rfl | hab
    · simp
    have hi (r s : R[X]) :
        cauchyIndex r s (Ico a b) = cauchyJump r s a + cauchyIndex r s (Ioo a b) := by
      rw [← Ioo_insert_left hab, insert_eq,
        cauchyIndex_union _ _ (disjoint_singleton_left.mpr (by simp)), cauchyIndex_singleton]
    have h := two_mul_cauchyIndex_add_cauchyIndex_Ioo p q hab
    have hj := two_mul_cauchyJump_add_cauchyJump p q a
    rw [hi, hi]
    linarith

/-- Inversion on a closed interval uses the signs outside it, including when it is a singleton. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Icc (p q : R[X])
    {a b : R} (hab : a ≤ b) :
    2 * (cauchyIndex p q (Icc a b) + cauchyIndex q p (Icc a b)) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignLeft a := by
  first
  | have hi (r s : R[X]) :
        cauchyIndex r s (Icc a b) = cauchyJump r s a + cauchyIndex r s (Ioc a b) := by
      rw [← Ioc_insert_left hab, insert_eq,
        cauchyIndex_union _ _ (disjoint_singleton_left.mpr (by simp)), cauchyIndex_singleton]
    have h := two_mul_cauchyIndex_add_cauchyIndex_Ioc p q hab
    have hj := two_mul_cauchyJump_add_cauchyJump p q a
    rw [hi, hi]
    linarith

/-- **Euclidean recurrence on an open interval**, allowing arbitrary endpoint roots. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Ioo (p q : R[X]) {a b : R} (hab : a < b) :
    2 * cauchyIndex p q (Ioo a b) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignRight a -
        2 * cauchyIndex q (p % q) (Ioo a b) := by
  first
  | rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Ioo p q hab]
    ring

/-- Euclidean recurrence on a left-open, right-closed interval. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Ioc (p q : R[X]) {a b : R} (hab : a ≤ b) :
    2 * cauchyIndex p q (Ioc a b) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignRight a -
        2 * cauchyIndex q (p % q) (Ioc a b) := by
  first
  | rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Ioc p q hab]
    ring

/-- Euclidean recurrence on a left-closed, right-open interval. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Ico (p q : R[X]) {a b : R} (hab : a ≤ b) :
    2 * cauchyIndex p q (Ico a b) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignLeft a -
        2 * cauchyIndex q (p % q) (Ico a b) := by
  first
  | rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Ico p q hab]
    ring

/-- Euclidean recurrence on a closed interval, including singleton intervals. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Icc (p q : R[X]) {a b : R} (hab : a ≤ b) :
    2 * cauchyIndex p q (Icc a b) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignLeft a -
        2 * cauchyIndex q (p % q) (Icc a b) := by
  first
  | rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Icc p q hab]
    ring

end TauCeti
end -- closes the original EOF section from source line 29
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/CauchyIndex/Inversion.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/BigOperators/Finset/Filter.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Filtered products

Weakening the condition `P` of a filtered product over `s` to `P i ∨ i = c`, for a point `c`
with `¬P c`, multiplies the product by the factor at `c` exactly when `c ∈ s`. This is the
bookkeeping that adds a closed endpoint to a sum over the points of a finite set in an open
interval.

For a family `u` of square roots of `1` with levels `k : ι → ℕ`, the products
`∏_{i ∈ s} u i ^ (k i - j)` for all `j` determine the products of the `u i` of each level `m ≥ 1`:
if they all equal one, so do the level products.

## Main results

* `Finset.prod_filter_or_eq_of_not`, `Finset.sum_filter_or_eq_of_not`: adjoining one point to
  the condition of a filtered product or sum.
* `Finset.prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one`: the level products of square roots
  of `1` are trivial when all their truncated power products are.
-/

public section

namespace TauCeti

/-- Adjoining a point `c` with `¬P c` to the condition `P` of a filtered product over `s`
multiplies it by the factor at `c` exactly when `c ∈ s`. -/
@[to_additive /-- Adjoining a point `c` with `¬P c` to the condition `P` of a filtered sum over
`s` adds the term at `c` exactly when `c ∈ s`. -/]
theorem _root_.Finset.prod_filter_or_eq_of_not {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ι → M) (P : ι → Prop) [DecidablePred P] {c : ι} (hc : ¬P c) :
    ∏ i ∈ s with P i ∨ i = c, f i = (∏ i ∈ s with P i, f i) * if c ∈ s then f c else 1 := by
  first
  | rw [Finset.filter_or, Finset.prod_union (Finset.disjoint_filter.mpr fun i _ hi (hic : i = c) =>
      hc (hic ▸ hi)), Finset.filter_eq']
    split_ifs <;> simp

/-- If `u i ^ 2 = 1` whenever `0 < k i`, and `∏_{i ∈ s} u i ^ (k i - j) = 1` for every `j`, then
the product of the `u i` with `k i = m` is `1` for every `m ≥ 1`. -/
theorem _root_.Finset.prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one {ι M : Type*}
    [CommMonoid M] (s : Finset ι) (k : ι → ℕ) (u : ι → M) (hu : ∀ i ∈ s, 0 < k i → u i ^ 2 = 1)
    (h : ∀ j, ∏ i ∈ s, u i ^ (k i - j) = 1) {m : ℕ} (hm : 0 < m) :
    ∏ i ∈ s with k i = m, u i = 1 := by
  first
    -- Multiplying the identities at `j = m - 1` and `j = m` isolates the product over `k i ≥ m`,
    -- and the product over `k i = m` is a quotient of two such.
  | have hT (m : ℕ) (hm : 0 < m) : ∏ i ∈ s with m ≤ k i, u i = 1 := by
      calc ∏ i ∈ s with m ≤ k i, u i = ∏ i ∈ s, u i ^ ((k i - (m - 1)) + (k i - m)) := by
            rw [Finset.prod_filter]
            refine Finset.prod_congr rfl fun i hi ↦ ?_
            split_ifs with hmi
            · rw [show k i - (m - 1) + (k i - m) = 2 * (k i - m) + 1 by omega, pow_succ, pow_mul,
                hu i hi (by omega), one_pow, one_mul]
            · rw [show k i - (m - 1) + (k i - m) = 0 by omega, pow_zero]
        _ = 1 := by simp only [pow_add, Finset.prod_mul_distrib, h, one_mul]
    have h₁ : (s.filter (m ≤ k ·)).filter (k · = m) = s.filter (k · = m) := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun i _ ↦ by omega
    have h₂ : (s.filter (m ≤ k ·)).filter (fun i ↦ ¬k i = m) = s.filter (m + 1 ≤ k ·) := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun i _ ↦ by omega
    have hsplit := Finset.prod_filter_mul_prod_filter_not (s.filter (m ≤ k ·)) (k · = m) u
    rwa [h₁, h₂, hT m hm, hT (m + 1) m.succ_pos, mul_one] at hsplit

end TauCeti
end -- closes the original EOF section from source line 30
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/BigOperators/Finset/Filter.lean -/

/- BEGIN SOURCE: TauCeti/Data/List/SignVariations.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Leading signs and variations of lists

The first nonzero sign determines the change in sign variations when a nonzero
entry is prepended to a list. Dually, the last nonzero sign `List.lastSign` and
the first nonzero sign of a second list decide whether concatenation creates one
extra variation at the junction (`List.signVariations_append`). Consequences are
invariance under reversal and splitting the count at any nonzero entry. Finally,
scaling every entry by a nonzero element of an ordered ring, or a list of signs by a nonzero
sign, preserves the count.

These are the append and scaling laws for variations of sign sequences used in
the Sturm and Descartes counting arguments; see Basu–Pollack–Roy, *Algorithms
in Real Algebraic Geometry*, Chapter 2.
-/

public section

namespace List

variable {R : Type*} [Zero R] [LinearOrder R]

/-- The sign of the first nonzero entry of a list, or `0` if every entry is zero. -/
def firstSign (l : List R) : SignType :=
  ((l.filter (fun v => decide (v ≠ 0))).head?.map SignType.sign).getD 0

@[simp, grind =]
theorem firstSign_nil : firstSign ([] : List R) = 0 := (rfl)

@[simp, grind =]
theorem firstSign_zero_cons (l : List R) : firstSign (0 :: l) = firstSign l := by
  first
  | simp [firstSign]

@[simp, grind =]
theorem firstSign_cons_of_ne_zero {a : R} (l : List R) (ha : a ≠ 0) :
    firstSign (a :: l) = SignType.sign a := by
  first
  | simp [firstSign, ha]

/-- Prepending an entry `a` adds one sign variation exactly when its sign is
opposite the sign of the next surviving entry. -/
theorem signVariations_cons {a : R} (l : List R) :
    List.signVariations (a :: l) =
      (if SignType.sign a * firstSign l = -1 then 1 else 0) + List.signVariations l := by
  first
  | by_cases ha : a = 0
    · subst a
      simp
    · induction l with
      | nil => simp [firstSign]
      | cons b l ih =>
        by_cases hb : b = 0
        · subst b
          simpa only [List.signVariations_cons_zero_cons, List.signVariations_zero_cons,
            firstSign_zero_cons] using ih
        · rw [firstSign_cons_of_ne_zero l hb, List.signVariations_cons_cons_of_ne_zero l ha hb]
          have ha' : SignType.sign a ≠ 0 := by simpa using ha
          have hb' : SignType.sign b ≠ 0 := by simpa using hb
          have h : (if SignType.sign a = SignType.sign b then (0 : ℕ) else 1) =
              (if SignType.sign a * SignType.sign b = -1 then 1 else 0) := by
            revert ha' hb'
            cases SignType.sign a <;> cases SignType.sign b <;> decide
          rw [h, Nat.add_comm]

@[simp, grind =]
theorem firstSign_singleton (a : R) : firstSign [a] = SignType.sign a := by
  first
  | by_cases ha : a = 0
    · simp [ha]
    · exact firstSign_cons_of_ne_zero [] ha

/-- A list has leading sign `0` exactly when all its entries vanish. -/
theorem firstSign_eq_zero_iff {l : List R} : firstSign l = 0 ↔ ∀ x ∈ l, x = 0 := by
  first
  | induction l with
    | nil => simp
    | cons a l ih =>
      by_cases ha : a = 0
      · simp [ha, ih]
      · simp [ha]

/-- The leading sign of a concatenation is that of the first list, unless the
first list vanishes identically. -/
theorem firstSign_append (l₁ l₂ : List R) :
    firstSign (l₁ ++ l₂) = if firstSign l₁ = 0 then firstSign l₂ else firstSign l₁ := by
  first
  | induction l₁ with
    | nil => simp
    | cons a l ih =>
      by_cases ha : a = 0
      · simp [ha, ih]
      · simp [firstSign_cons_of_ne_zero _ ha, ha]

/-- A list whose entries all vanish has no sign variations. -/
theorem signVariations_eq_zero_of_forall_eq_zero {l : List R} (h : ∀ x ∈ l, x = 0) :
    List.signVariations l = 0 := by
  first
  | induction l with
    | nil => simp
    | cons a l ih =>
      rw [h a mem_cons_self, signVariations_zero_cons]
      exact ih fun x hx => h x (mem_cons_of_mem a hx)

/-- The sign of the last nonzero entry of a list, or `0` if every entry is zero. -/
def lastSign (l : List R) : SignType :=
  firstSign l.reverse

@[simp, grind =]
theorem firstSign_reverse (l : List R) : firstSign l.reverse = lastSign l := (rfl)

@[simp, grind =]
theorem lastSign_reverse (l : List R) : lastSign l.reverse = firstSign l := by
  first
  | rw [← firstSign_reverse, reverse_reverse]

@[simp, grind =]
theorem lastSign_nil : lastSign ([] : List R) = 0 := (rfl)

@[simp, grind =]
theorem lastSign_singleton (a : R) : lastSign [a] = SignType.sign a := by
  first
  | rw [← firstSign_reverse, reverse_singleton, firstSign_singleton]

/-- A list has trailing sign `0` exactly when all its entries vanish. -/
theorem lastSign_eq_zero_iff {l : List R} : lastSign l = 0 ↔ ∀ x ∈ l, x = 0 := by
  first
  | simp [← firstSign_reverse, firstSign_eq_zero_iff]

/-- The trailing sign of a concatenation is that of the second list, unless the
second list vanishes identically. -/
theorem lastSign_append (l₁ l₂ : List R) :
    lastSign (l₁ ++ l₂) = if lastSign l₂ = 0 then lastSign l₁ else lastSign l₂ := by
  first
  | simp only [← firstSign_reverse, reverse_append, firstSign_append]

/-- Prepending an entry determines the trailing sign only when the rest of the
list vanishes identically. -/
theorem lastSign_cons (a : R) (l : List R) :
    lastSign (a :: l) = if lastSign l = 0 then SignType.sign a else lastSign l := by
  first
  | rw [← singleton_append, lastSign_append, lastSign_singleton]

/-- A list has trailing sign `0` exactly when it has leading sign `0`. -/
theorem lastSign_eq_zero_iff_firstSign_eq_zero {l : List R} :
    lastSign l = 0 ↔ firstSign l = 0 := by
  first
  | rw [lastSign_eq_zero_iff, firstSign_eq_zero_iff]

/-- Concatenating two lists adds their sign variations, plus one exactly when the
last nonzero entry of the first list and the first nonzero entry of the second
have opposite signs. -/
theorem signVariations_append (l₁ l₂ : List R) :
    List.signVariations (l₁ ++ l₂) =
      List.signVariations l₁ + (if lastSign l₁ * firstSign l₂ = -1 then 1 else 0) +
        List.signVariations l₂ := by
  first
  | induction l₁ with
    | nil => simp
    | cons a l ih =>
      by_cases hl : firstSign l = 0
      · simp [signVariations_cons, firstSign_append, lastSign_cons, ih, hl,
          lastSign_eq_zero_iff_firstSign_eq_zero.mpr hl,
          signVariations_eq_zero_of_forall_eq_zero (firstSign_eq_zero_iff.mp hl)]
      · simp [signVariations_cons, firstSign_append, lastSign_cons, ih, hl,
          lastSign_eq_zero_iff_firstSign_eq_zero.not.mpr hl]
        omega

/-- Reversing a list does not change its sign variations. -/
@[simp]
theorem signVariations_reverse (l : List R) :
    List.signVariations l.reverse = List.signVariations l := by
  first
  | induction l with
    | nil => simp
    | cons a l ih =>
      simp [signVariations_append, signVariations_cons, ih, mul_comm]
      omega

/-- The sign variations of a list split at any nonzero entry. -/
theorem signVariations_append_cons_of_ne_zero (l₁ l₂ : List R) {a : R} (ha : a ≠ 0) :
    List.signVariations (l₁ ++ a :: l₂) =
      List.signVariations (l₁ ++ [a]) + List.signVariations (a :: l₂) := by
  first
  | rw [signVariations_append, signVariations_append, firstSign_cons_of_ne_zero _ ha,
      firstSign_singleton, signVariations_singleton, add_zero]

end List

namespace List

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying every entry on the left by a nonzero constant preserves the sign
variations. -/
theorem signVariations_map_mul_left (l : List R) {c : R} (hc : c ≠ 0) :
    List.signVariations (l.map (c * ·)) = List.signVariations l := by
  first
  | rcases hc.lt_or_gt with hc | hc
    · exact signVariations_map_of_sign_eq_neg (fun x => by rw [sign_mul, sign_neg hc, neg_one_mul]) l
    · exact signVariations_map (fun x => by rw [sign_mul, sign_pos hc, one_mul]) l

/-- Multiplying every entry of a list of signs on the left by a nonzero sign preserves the sign
variations. -/
theorem signVariations_map_signType_mul_left (l : List SignType) {s : SignType} (hs : s ≠ 0) :
    List.signVariations (l.map (s * ·)) = List.signVariations l := by
  first
  | cases s
    · exact absurd rfl hs
    · exact signVariations_map_of_sign_eq_neg (by decide) l
    · exact signVariations_map (by decide) l

end List
end -- closes the original EOF section from source line 25
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/List/SignVariations.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/Signs.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Sign bookkeeping for abstract Sturm chains

Zero-skipping variations are unchanged when an interior zero has neighbors of
opposite signs. This bookkeeping works over a strictly ordered ring. The closing
constancy lemma uses the intermediate value property of a real closed field.

The variations `TauCeti.Sturm.signVariationsAt` of a polynomial list at a point inherit the
append, negation, scaling and zero-deletion laws of `List.signVariations`: they split at any
entry that does not vanish at the point, and are unchanged by negating every entry, by
multiplying every entry by a polynomial that does not vanish at the point, and by deleting the
entries that do.
-/

public section

namespace TauCeti.Sturm

open List

section Signs

variable {R : Type*} [Zero R] [LinearOrder R]

/-- A local sign-pattern relation between two lists: they agree entry by
entry except that a nonzero entry flanked by two opposite-sign neighbours may
collapse to `0`. Such a collapse is variation-neutral, so `List.signVariations` and
the leading sign are preserved (`SignRelation.signVariations_eq`). -/
private inductive SignRelation : List R → List R → Prop
  | nil : SignRelation [] []
  | same {x y : R} {l m : List R} (hx : x ≠ 0) (hy : y ≠ 0)
      (hs : SignType.sign x = SignType.sign y) (h : SignRelation l m) :
      SignRelation (x :: l) (y :: m)
  | collapse {x X x' : R} {l m : List R} {y y' : R}
      (hx : x ≠ 0) (hX : X ≠ 0) (hy' : y' ≠ 0)
      (hsx : SignType.sign x = SignType.sign x')
      (hsy : SignType.sign y = SignType.sign y')
      (hopp : SignType.sign x * SignType.sign y = -1)
      (h : SignRelation (y :: l) (y' :: m)) :
      SignRelation (x :: X :: y :: l) (x' :: 0 :: y' :: m)

private theorem sign_changes_of_opposite (u v w : SignType) (huw : u * w = -1) (hv : v ≠ 0) :
    (if u * v = -1 then (1 : ℕ) else 0) + (if v * w = -1 then 1 else 0) = 1 := by
  first
  | revert huw hv; revert u v w; decide

/-- Lists related by `SignRelation` have equal sign variations and equal leading signs. -/
private theorem SignRelation.signVariations_eq {L M : List R} (h : SignRelation L M) :
    List.signVariations L = List.signVariations M ∧ firstSign L = firstSign M := by
  first
  | induction h with
    | nil => exact ⟨rfl, rfl⟩
    | @same x y l m hx hy hs _ ih =>
      refine ⟨?_, ?_⟩
      · rw [signVariations_cons l, signVariations_cons m, ih.1, ih.2, hs]
      · rw [firstSign_cons_of_ne_zero l hx, firstSign_cons_of_ne_zero m hy, hs]
    | @collapse x X x' l m y y' hx hX hy' hsx hsy hopp h ih =>
      have hy : y ≠ 0 := by
        intro hy0; rw [hy0, sign_zero, mul_zero] at hopp; exact absurd hopp (by decide)
      have hx' : x' ≠ 0 := by
        intro hx0; rw [hx0, sign_zero] at hsx; exact hx (sign_eq_zero_iff.mp hsx)
      refine ⟨?_, ?_⟩
      · rw [signVariations_cons (X :: y :: l),
          firstSign_cons_of_ne_zero (y :: l) hX, signVariations_cons (y :: l),
          firstSign_cons_of_ne_zero l hy]
        rw [signVariations_cons (0 :: y' :: m),
          firstSign_zero_cons (y' :: m), firstSign_cons_of_ne_zero m hy',
          List.signVariations_zero_cons]
        rw [← add_assoc, ih.1]
        congr 1
        rw [← hsx, ← hsy, ite_eq_left hopp]
        exact sign_changes_of_opposite _ _ _ hopp (fun h => hX (sign_eq_zero_iff.mp h))
      · rw [firstSign_cons_of_ne_zero (X :: y :: l) hx,
          firstSign_cons_of_ne_zero (0 :: y' :: m) hx', hsx]

end Signs

section Polynomials

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The zero-skipping variations of a polynomial list at a point. -/
noncomputable def signVariationsAt (cs : List (Polynomial R)) (x : R) : ℕ :=
  List.signVariations (cs.map (Polynomial.eval x))

/-- Variations are computed on the list of evaluations. -/
theorem signVariationsAt_def (cs : List (Polynomial R)) (x : R) :
    signVariationsAt cs x = List.signVariations (cs.map (Polynomial.eval x)) := (rfl)

@[simp, grind =]
theorem signVariationsAt_nil (x : R) : signVariationsAt [] x = 0 := by simp [signVariationsAt_def]

@[simp, grind =]
theorem signVariationsAt_singleton (p : Polynomial R) (x : R) : signVariationsAt [p] x = 0 := by
  first
  | simp [signVariationsAt_def]

/-- Prepending an evaluation contributes one variation exactly when its
sign is opposite to the first nonzero sign of the remaining evaluations. -/
theorem signVariationsAt_cons (cs : List (Polynomial R)) {p : Polynomial R} {x : R}
    : signVariationsAt (p :: cs) x =
      (if SignType.sign (p.eval x) * List.firstSign (cs.map (Polynomial.eval x)) = -1
        then 1 else 0) + signVariationsAt cs x := by
  first
  | rw [signVariationsAt_def, List.map_cons, List.signVariations_cons,
      signVariationsAt_def]

/-- Ordered coefficient embeddings preserve variations at the corresponding evaluation point. -/
@[simp]
theorem signVariationsAt_map {S : Type*} [Semiring S] [LinearOrder S]
    (cs : List (Polynomial R)) (f : R →+* S) (hf : StrictMono f) (x : R) :
    signVariationsAt (cs.map (Polynomial.map f)) (f x) = signVariationsAt cs x := by
  first
  | rw [signVariationsAt_def, signVariationsAt_def]
    apply List.signVariations_congr
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun p _ ↦ p.sign_eval_map f hf x

/-- The variations at `x` of a concatenation are those of the two parts, plus one exactly when
the last nonzero value of the first part and the first nonzero value of the second part have
opposite signs. -/
theorem signVariationsAt_append (cs ds : List (Polynomial R)) (x : R) :
    signVariationsAt (cs ++ ds) x =
      signVariationsAt cs x +
        (if List.lastSign (cs.map (Polynomial.eval x)) *
            List.firstSign (ds.map (Polynomial.eval x)) = -1 then 1 else 0) +
        signVariationsAt ds x := by
  first
  | simp only [signVariationsAt_def, List.map_append, List.signVariations_append]

/-- The variations at `x` split at any entry that does not vanish at `x`. -/
theorem signVariationsAt_append_cons_of_eval_ne_zero (cs ds : List (Polynomial R))
    {p : Polynomial R} {x : R} (hp : p.eval x ≠ 0) :
    signVariationsAt (cs ++ p :: ds) x =
      signVariationsAt (cs ++ [p]) x + signVariationsAt (p :: ds) x := by
  first
  | simpa only [signVariationsAt_def, List.map_append, List.map_cons, List.map_nil] using
      List.signVariations_append_cons_of_ne_zero _ _ hp

/-- Deleting the entries that vanish at `x` does not change the variations at `x`. -/
@[simp]
theorem signVariationsAt_filter_eval_ne_zero (cs : List (Polynomial R)) (x : R) :
    signVariationsAt (cs.filter fun p ↦ !decide (p.eval x = 0)) x = signVariationsAt cs x := by
  first
  | rw [signVariationsAt_def, signVariationsAt_def,
      ← List.signVariations_filter_ne_zero (cs.map _), List.filter_map]
    simp [Function.comp_def]

end Basic

section Neg

variable {R : Type*} [Ring R] [LinearOrder R] [AddLeftStrictMono R]

/-- Negating every entry does not change the variations at a point. -/
@[simp]
theorem signVariationsAt_map_neg (cs : List (Polynomial R)) (x : R) :
    signVariationsAt (cs.map Neg.neg) x = signVariationsAt cs x := by
  first
  | simpa only [signVariationsAt_def, List.map_map, Function.comp_def, Polynomial.eval_neg] using
      List.signVariations_map_of_sign_eq_neg Left.sign_neg (cs.map (Polynomial.eval x))

end Neg

section OrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying every entry by a polynomial that does not vanish at the point
preserves the sign variations at that point. -/
theorem signVariationsAt_map_mul (cs : List (Polynomial R)) {d : Polynomial R} {x : R}
    (hd : d.eval x ≠ 0) : signVariationsAt (cs.map (d * ·)) x = signVariationsAt cs x := by
  first
  | simp only [signVariationsAt_def]
    have heq : (cs.map (d * ·)).map (Polynomial.eval x) =
        (cs.map (Polynomial.eval x)).map (d.eval x * ·) := by simp [List.map_map, Function.comp_def]
    rw [heq, List.signVariations_map_mul_left _ hd]

end OrderedCommRing

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Evaluation hypotheses that persist when entries are removed from the front.
Nonvanishing of the first entry at `r` is supplied separately to the induction. -/
private structure EvalSigns (a r : R) (cs : List (Polynomial R)) : Prop where
  nonzero : ∀ q ∈ cs, q.eval a ≠ 0
  last : ∀ q, cs.getLast? = some q → q.eval r ≠ 0
  alternate : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
    cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → q1.eval r = 0 →
    q0.eval r * q2.eval r < 0
  same : ∀ q ∈ cs, q.eval r ≠ 0 → SignType.sign (q.eval a) = SignType.sign (q.eval r)

omit [IsStrictOrderedRing R] in
private theorem EvalSigns.tail {a r : R} {p : Polynomial R} {cs : List (Polynomial R)}
    (h : EvalSigns a r (p :: cs)) : EvalSigns a r cs where
  nonzero q hq := h.nonzero q (List.mem_cons_of_mem _ hq)
  last q hq := by
    first
    | cases cs with
      | nil => simp at hq
      | cons q0 rest => exact h.last q (by simpa using hq)
  alternate i q0 q1 q2 h0 h1 h2 :=
    h.alternate (i + 1) q0 q1 q2 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  same q hq := h.same q (List.mem_cons_of_mem _ hq)

-- Induct along the list: a zero second entry collapses between opposite signs;
-- otherwise the first entries match and the induction continues on the tail.
private theorem signRelation_eval (a r : R) :
    ∀ (cs : List (Polynomial R)), EvalSigns a r cs →
      (∀ q, cs.head? = some q → q.eval r ≠ 0) →
      SignRelation (cs.map (Polynomial.eval a)) (cs.map (Polynomial.eval r))
  | [], _, _ => SignRelation.nil
  | [q0], h, hfront => by
      have hr : q0.eval r ≠ 0 := hfront q0 rfl
      exact SignRelation.same (h.nonzero q0 (by simp)) hr (h.same q0 (by simp) hr) SignRelation.nil
  | q0 :: q1 :: rest, h, hfront => by
      have hr0 : q0.eval r ≠ 0 := hfront q0 rfl
      have ha0 : q0.eval a ≠ 0 := h.nonzero q0 (by simp)
      by_cases hq1 : q1.eval r = 0
      · cases rest with
        | nil => exact absurd hq1 (h.last q1 (by simp))
        | cons q2 rest' =>
            have hoppR := h.alternate 0 q0 q1 q2 rfl rfl rfl hq1
            have hn0 := left_ne_zero_of_mul hoppR.ne
            have hn2 := right_ne_zero_of_mul hoppR.ne
            have hsx := h.same q0 (by simp) hn0
            have hsy := h.same q2 (by simp) hn2
            have hoppA : SignType.sign (q0.eval a) * SignType.sign (q2.eval a) = -1 := by
              first
              | rw [hsx, hsy, ← sign_mul, sign_eq_neg_one_iff]
                exact hoppR
            have hfront' : ∀ q, (q2 :: rest').head? = some q → q.eval r ≠ 0 := by
              first
              | intro q hq
                cases hq
                exact hn2
            have ih := signRelation_eval a r (q2 :: rest') h.tail.tail hfront'
            simp only [List.map_cons] at ih ⊢
            rw [hq1]
            exact SignRelation.collapse ha0 (h.nonzero q1 (by simp)) hn2 hsx hsy hoppA ih
      · have hfront' : ∀ q, (q1 :: rest).head? = some q → q.eval r ≠ 0 := by
          first
          | intro q hq
            cases hq
            exact hq1
        have ih := signRelation_eval a r (q1 :: rest) h.tail hfront'
        simp only [List.map_cons] at ih ⊢
        exact SignRelation.same ha0 hr0 (h.same q0 (by simp) hr0) ih

/-- Evaluations at `a` and `r` have the same variation count if no entry
vanishes at `a`, the first and last entries do not vanish at `r`, zeros at `r`
have nonvanishing opposite-sign neighbours, and the surviving signs agree. -/
theorem signVariationsAt_eq_of_alternate (cs : List (Polynomial R)) (a r : R)
    (hne : ∀ q ∈ cs, q.eval a ≠ 0)
    (hfront : ∀ q, cs.head? = some q → q.eval r ≠ 0)
    (hlast : ∀ q, cs.getLast? = some q → q.eval r ≠ 0)
    (halt : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
      cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → q1.eval r = 0 →
      q0.eval r * q2.eval r < 0)
    (hsame : ∀ q ∈ cs, q.eval r ≠ 0 →
      SignType.sign (q.eval a) = SignType.sign (q.eval r)) :
    signVariationsAt cs a = signVariationsAt cs r :=
  (signRelation_eval a r cs ⟨hne, hlast, halt, hsame⟩ hfront).signVariations_eq.1

end OrderedRing

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Variations are constant if no chain entry vanishes on the interval. -/
theorem signVariationsAt_const (cs : List (Polynomial R)) {a b : R} (hab : a ≤ b)
    (hz : ∀ q ∈ cs, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    signVariationsAt cs a = signVariationsAt cs b := by
  first
  | apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left fun q hq => Polynomial.sign_eval_const q hab (hz q hq)

end Polynomials

end TauCeti.Sturm
end -- closes the original EOF section from source line 24
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/Signs.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/Local.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Local variation jumps for alternating polynomial chains

`IsAlternating` records the sign conditions of a chain whose last entry has no roots.
Interior zeros preserve sign variations. Crossing a simple root of the first
entry changes the variation by the sign of its derivative times the second entry.
These local identities supply the signed root sum in `Sturm.Sum`.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial List

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A alternating chain has opposite neighbors at every interior zero and
no real zero in its last entry. These are the properties of a signed remainder
chain after its common polynomial factor has been removed. -/
structure IsAlternating (cs : List (Polynomial R)) : Prop where
  /-- Every entry is a nonzero polynomial. -/
  nonzero : ∀ q ∈ cs, q ≠ 0
  /-- The terminal polynomial has no root in the coefficient ring. -/
  last : ∀ q, cs.getLast? = some q → ∀ r, q.eval r ≠ 0
  /-- At an interior zero the adjacent values are nonzero and have opposite signs. -/
  alternate : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
    cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → ∀ r, q1.eval r = 0 →
    q0.eval r * q2.eval r < 0

namespace IsAlternating

omit [IsStrictOrderedRing R] in
theorem tail {p : Polynomial R} {cs : List (Polynomial R)} (h : IsAlternating (p :: cs)) :
    IsAlternating cs where
  nonzero q hq := h.nonzero q (List.mem_cons_of_mem _ hq)
  last q hq r := by
    first
    | cases cs with
      | nil => simp at hq
      | cons q0 rest => exact h.last q (by simpa using hq) r
  alternate i q0 q1 q2 h0 h1 h2 r hz :=
    h.alternate (i + 1) q0 q1 q2
      (by simpa using h0) (by simpa using h1) (by simpa using h2) r hz

/-- A alternating chain has the same variations at two points if no entry vanishes
at the first, the head does not vanish at the second, and all surviving signs agree. -/
theorem signVariationsAt_eq {cs : List (Polynomial R)} (h : IsAlternating cs) (a r : R)
    (hne : ∀ q ∈ cs, q.eval a ≠ 0)
    (hfront : ∀ q, cs.head? = some q → q.eval r ≠ 0)
    (hsame : ∀ q ∈ cs, q.eval r ≠ 0 →
      SignType.sign (q.eval a) = SignType.sign (q.eval r)) :
    signVariationsAt cs a = signVariationsAt cs r :=
  signVariationsAt_eq_of_alternate cs a r hne hfront (fun q hq => h.last q hq r)
    (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 r) hsame

omit [IsStrictOrderedRing R] in
/-- Consecutive entries of a alternating chain cannot both vanish. -/
theorem second_eval_ne_zero {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsAlternating (p :: q :: cs)) {r : R} (hr : p.eval r = 0) : q.eval r ≠ 0 := by
  first
  | cases cs with
    | nil => exact h.last q (by simp) r
    | cons s cs =>
      intro hq
      exact left_ne_zero_of_mul (h.alternate 0 p q s rfl rfl rfl r hq).ne hr

end IsAlternating

end OrderedRing

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

namespace IsAlternating

/-- Crossing isolated interior zeros does not change variations. -/
theorem signVariationsAt_nonroot {cs : List (Polynomial R)} (h : IsAlternating cs) {a r b : R}
    (har : a < r) (hrb : r < b)
    (hfront : ∀ q, cs.head? = some q → q.eval r ≠ 0)
    (hz : ∀ q ∈ cs, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    signVariationsAt cs a = signVariationsAt cs r ∧
      signVariationsAt cs r = signVariationsAt cs b := by
  first
  | have hab := (har.trans hrb).le
    constructor
    · refine h.signVariationsAt_eq a r
        (fun q hq => hz q hq a ⟨le_rfl, hab⟩ har.ne) hfront ?_
      intro q hq hqr
      exact (q.signs_at_nonroot har hrb hqr (hz q hq)).1
    · symm
      refine h.signVariationsAt_eq b r
        (fun q hq => hz q hq b ⟨hab, le_rfl⟩ hrb.ne.symm) hfront ?_
      intro q hq hqr
      exact (q.signs_at_nonroot har hrb hqr (hz q hq)).2

/-- At a simple root of the head, the variation jump is the sign of the
product of the head derivative and the second entry. -/
theorem root_jump {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsAlternating (p :: q :: cs)) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0)
    (hz : ∀ s ∈ p :: q :: cs, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  first
  | have hq := h.second_eval_ne_zero hr
    have hab := (har.trans hrb).le
    have ht := h.tail.signVariationsAt_nonroot har hrb
      (fun s hs => by cases hs; simpa using hq)
      (fun s hs => hz s (List.mem_cons_of_mem _ hs))
    have hpz := hz p (by simp)
    obtain ⟨hpa, hpb⟩ := Polynomial.signs_at_root p har hrb hr hd hpz
    obtain ⟨hqa, hqb⟩ := q.signs_at_nonroot har hrb hq (hz q (by simp))
    have hqa0 := hz q (by simp) a ⟨le_rfl, hab⟩ har.ne
    have hqb0 := hz q (by simp) b ⟨hab, le_rfl⟩ hrb.ne.symm
    have ha : signVariationsAt (p :: q :: cs) a =
        (if -SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
        signVariationsAt (q :: cs) a := by
      rw [signVariationsAt_cons, List.map_cons, firstSign_cons_of_ne_zero _ hqa0,
        hpa, hqa, neg_mul, ← sign_mul]
    have hb : signVariationsAt (p :: q :: cs) b =
        (if SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
        signVariationsAt (q :: cs) b := by
      rw [signVariationsAt_cons, List.map_cons, firstSign_cons_of_ne_zero _ hqb0,
        hpb, hqb, ← sign_mul]
    rw [ha, hb, ht.1.trans ht.2, Nat.cast_add, Nat.cast_add]
    have numeric (s : SignType) :
        ((if -s = -1 then 1 else 0 : ℕ) : ℤ) -
          ((if s = -1 then 1 else 0 : ℕ) : ℤ) = (s : ℤ) := by
      cases s <;> decide
    have := numeric (SignType.sign (p.derivative.eval r * q.eval r))
    omega


end IsAlternating

end TauCeti.Sturm
end -- closes the original EOF section from source line 18
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/Local.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/Sequence.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Entries of a Sturm sequence

Reading a missing second entry as zero recovers the second input uniformly,
including the singleton sequence with zero second input. Each entry after the second is the
negated remainder of its two predecessors, and from the second entry on the degrees strictly
decrease. These facts let results about one Euclidean step be propagated along the whole
sequence.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- Mapping coefficients through a field homomorphism maps every entry of the signed
Euclidean remainder sequence, including when either input is zero. -/
@[simp]
theorem sturmSeq_map {L : Type*} [Field L] [DecidableEq L]
    (p q : K[X]) (f : K →+* L) :
    sturmSeq (p.map f) (q.map f) = (sturmSeq p q).map (Polynomial.map f) := by
  first
  | induction p, q using sturmSeq.induct with
    | case1 q => simp
    | case2 p q hp ih =>
      rw [sturmSeq_cons (map_ne_zero hp), sturmSeq_cons hp, List.map_cons,
        ← Polynomial.map_neg, ← map_mod, ih]

/-- A nonzero-headed Sturm sequence has its second input as its second entry,
with zero representing the missing entry of a singleton sequence. -/
@[simp, grind =]
theorem getD_getElem?_sturmSeq {p : K[X]} (hp : p ≠ 0) (q : K[X]) :
    (sturmSeq p q)[1]?.getD 0 = q := by
  first
  | rw [← List.head?_tail]
    rw [sturmSeq_cons hp, List.tail_cons]
    by_cases hq : q = 0
    · simp only [hq, sturmSeq_zero_left, List.head?_nil, Option.getD_none]
    · simp only [head?_sturmSeq hq, Option.getD_some]

/-- An entry at index zero of a Sturm sequence is its first input. -/
theorem eq_of_getElem?_zero_sturmSeq {p q a : K[X]}
    (ha : (sturmSeq p q)[0]? = some a) : a = p := by
  first
  | have hp : p ≠ 0 := by rintro rfl; simp at ha
    simpa [sturmSeq_cons hp] using ha.symm

/-- An entry at index one of a Sturm sequence is its second input. -/
theorem eq_of_getElem?_one_sturmSeq {p q b : K[X]}
    (hb : (sturmSeq p q)[1]? = some b) : b = q := by
  first
  | have hp : p ≠ 0 := by rintro rfl; simp at hb
    have h := congrArg (fun o ↦ o.getD 0) hb
    simpa only [getD_getElem?_sturmSeq hp, Option.getD_some] using h.symm

/-- If a Sturm sequence has an entry at a successor index, it has a preceding entry. -/
theorem exists_getElem?_sturmSeq_of_succ {p q s : K[X]} {i : ℕ}
    (hs : (sturmSeq p q)[i + 1]? = some s) : ∃ a, (sturmSeq p q)[i]? = some a := by
  first
  | have hi := (List.getElem?_eq_some_iff.mp hs).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- Every entry of a Sturm sequence after the second is the negated remainder of its two
predecessors. -/
theorem eq_neg_mod_of_getElem?_sturmSeq {p q a b c : K[X]} {i : ℕ}
    (ha : (sturmSeq p q)[i]? = some a) (hb : (sturmSeq p q)[i + 1]? = some b)
    (hc : (sturmSeq p q)[i + 2]? = some c) : c = -a % b := by
  first
  | induction p, q using sturmSeq.induct generalizing i with
    | case1 q => simp at ha
    | case2 p q hp ih =>
      rw [sturmSeq_cons hp] at ha hb hc
      rcases i with _ | i
      · have hq : q ≠ 0 := by
          rintro rfl
          simp at hb
        have hr : -p % q ≠ 0 := by
          rintro hr
          simp [sturmSeq_cons hq, hr] at hc
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
        simp only [List.getElem?_cons_succ, sturmSeq_cons hq, List.getElem?_cons_zero,
          Option.some.injEq] at hb
        simp only [List.getElem?_cons_succ, sturmSeq_cons hq, sturmSeq_cons hr,
          List.getElem?_cons_zero, Option.some.injEq] at hc
        rw [← ha, ← hb, ← hc]
      · exact ih ha hb hc

/-- From the second entry on, the degrees of the entries of a Sturm sequence strictly
decrease. The first two entries are unconstrained. -/
theorem natDegree_lt_of_getElem?_sturmSeq {p q s t : K[X]} {i : ℕ}
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t) :
    t.natDegree < s.natDegree := by
  first
  | induction p, q using sturmSeq.induct generalizing i with
    | case1 q => simp at hs
    | case2 p q hp ih =>
      rw [sturmSeq_cons hp] at hs ht
      rcases i with _ | i
      · have hq : q ≠ 0 := by
          rintro rfl
          simp at hs
        have hr : -p % q ≠ 0 := by
          rintro hr
          simp [sturmSeq_cons hq, hr] at ht
        simp only [List.getElem?_cons_succ, sturmSeq_cons hq, List.getElem?_cons_zero,
          Option.some.injEq] at hs
        simp only [List.getElem?_cons_succ, sturmSeq_cons hq, sturmSeq_cons hr,
          List.getElem?_cons_zero, Option.some.injEq] at ht
        rw [← hs, ← ht]
        exact natDegree_lt_natDegree hr (degree_mod_lt _ hq)
      · exact ih hs ht

/-- If the second input has degree at most that of the first, then so does every entry of the
Sturm sequence. -/
theorem natDegree_le_of_mem_sturmSeq {p q s : K[X]} (hs : s ∈ sturmSeq p q)
    (hq : q.natDegree ≤ p.natDegree) : s.natDegree ≤ p.natDegree := by
  first
  | induction p, q using sturmSeq.induct with
    | case1 q => simp at hs
    | case2 p q hp ih =>
      rw [sturmSeq_cons hp, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact le_rfl
      · by_cases hq0 : q = 0
        · simp [hq0] at hs
        · exact (ih hs (natDegree_le_natDegree (degree_mod_lt _ hq0).le)).trans hq

end Polynomial
end -- closes the original EOF section from source line 19
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/Sequence.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/SignedRemainders.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Positive-scaled signed remainder chains

The defining relations allow pseudo-remainder scaling. The terminal entry
may be nonconstant; no coprimality is imposed on the first two entries.

`Polynomial.sturmSeq` satisfies these relations. The relational formulation also
allows positive pseudo-remainder scalings without changing root sign sums.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R]

/-- A positively scaled signed remainder identity. -/
def IsRemainder (p q r : Polynomial R) : Prop :=
  ∃ a b : R, ∃ u : Polynomial R, 0 < a ∧ 0 < b ∧ C a * p = u * q - C b * r

/-- The algebraic relations of a signed remainder chain, including its exact
termination. Degree descent is needed to construct such a chain, but not to
verify its signed root-sum identity. -/
structure IsSignedRemainderSeq (cs : List (Polynomial R)) : Prop where
  /-- Every entry is a nonzero polynomial. -/
  nonzero : ∀ p ∈ cs, p ≠ 0
  /-- Successive triples satisfy a positively scaled signed remainder identity. -/
  relation : ∀ (i : ℕ) (p q r : Polynomial R), cs[i]? = some p →
    cs[i + 1]? = some q → cs[i + 2]? = some r → IsRemainder p q r
  /-- The final remainder vanishes, so the last entry divides its predecessor. -/
  terminal : ∀ pre p q, cs = pre ++ [p, q] → q ∣ p

namespace IsRemainder

/-- Construct the signed remainder relation from positive scalings and a polynomial identity. -/
theorem of_identity {p q r : Polynomial R} (a b : R) (u : Polynomial R)
    (ha : 0 < a) (hb : 0 < b) (heq : C a * p = u * q - C b * r) : IsRemainder p q r :=
  ⟨a, b, u, ha, hb, heq⟩

/-- A signed remainder relation supplies positive scalings and its polynomial identity. -/
theorem exists_identity {p q r : Polynomial R} (h : IsRemainder p q r) :
    ∃ a b : R, ∃ u : Polynomial R, 0 < a ∧ 0 < b ∧ C a * p = u * q - C b * r := h

/-- A common divisor of the two later entries divides the earlier entry. -/
theorem dvd {p q r d : Polynomial R} (h : IsRemainder p q r) (hq : d ∣ q) (hr : d ∣ r) :
    d ∣ p := by
  first
  | obtain ⟨a, b, u, ha, _, heq⟩ := h.exists_identity
    have hu : IsUnit (C a) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha.ne')
    apply hu.dvd_mul_left.mp
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_right hq _) (dvd_mul_of_dvd_right hr _)

/-- Cancel a nonzero common polynomial factor from a signed remainder identity. -/
theorem cancel {d p q r : Polynomial R} (hd : d ≠ 0)
    (h : IsRemainder (d * p) (d * q) (d * r)) : IsRemainder p q r := by
  first
  | obtain ⟨a, b, u, ha, hb, heq⟩ := h.exists_identity
    refine IsRemainder.of_identity a b u ha hb (mul_left_cancel₀ hd ?_)
    calc
      d * (C a * p) = C a * (d * p) := by ring
      _ = u * (d * q) - C b * (d * r) := heq
      _ = d * (u * q - C b * r) := by ring

variable [IsStrictOrderedRing R]

/-- At a zero of the middle entry, the neighbors have opposite signs,
provided the right neighbor does not vanish. -/
theorem alternate {p q r : Polynomial R} (h : IsRemainder p q r) {x : R}
    (hq : q.eval x = 0) (hr : r.eval x ≠ 0) :
    p.eval x * r.eval x < 0 := by
  first
  | obtain ⟨a, b, u, ha, hb, heq⟩ := h.exists_identity
    have he := congrArg (Polynomial.eval x) heq
    simp only [eval_mul, eval_C, eval_sub, hq, mul_zero, zero_sub] at he
    rcases lt_or_gt_of_ne hr with hr | hr
    · have hp' : 0 < p.eval x := (mul_pos_iff_of_pos_left ha).mp (by
        rw [he]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hb hr))
      exact mul_neg_of_pos_of_neg hp' hr
    · have hn : a * p.eval x < 0 := by
        rw [he]; exact neg_neg_of_pos (mul_pos hb hr)
      have hp' : p.eval x < 0 := by
        by_contra! hp
        exact (mul_nonneg ha.le hp).not_gt hn
      exact mul_neg_of_neg_of_pos hp' hr

end IsRemainder

namespace IsSignedRemainderSeq

/-- A nonzero polynomial alone forms a signed remainder sequence. -/
theorem singleton {p : Polynomial R} (hp : p ≠ 0) : IsSignedRemainderSeq [p] where
  nonzero := by simpa
  relation i p0 p1 p2 _ _ h2 := by
    first
    | have hi : i + 2 < 1 := by
        simpa using (List.getElem?_eq_some_iff.mp h2).1
      omega
  terminal pre p0 p1 heq := by
    first
    | have := congrArg List.length heq
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega

/-- A two-entry chain terminates when its second polynomial divides its first. -/
theorem pair {p q : Polynomial R} (hp : p ≠ 0) (hdvd : q ∣ p) :
    IsSignedRemainderSeq [p, q] where
  nonzero s hs := by
    first
    | have hq : q ≠ 0 := fun h => hp (zero_dvd_iff.mp (h ▸ hdvd))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hp
      · exact hq
  relation i p0 p1 p2 _ _ h2 := by
    first
    | have hi : i + 2 < 2 := by
        have := List.getElem?_eq_some_iff.mp h2
        simpa using this.1
      omega
  terminal pre p0 p1 heq := by
    first
    | have hlen : 2 = pre.length + 2 := by
        simpa only [List.length_cons, List.length_nil, List.length_append] using
          congrArg List.length heq
      have hpre : pre = [] := List.length_eq_zero_iff.mp (by omega)
      subst pre
      simp only [List.nil_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, _⟩
      exact hdvd

/-- Prepend one signed recurrence to a chain. -/
theorem cons {p q r : Polynomial R} {cs : List (Polynomial R)}
    (hp : p ≠ 0) (hrel : IsRemainder p q r) (h : IsSignedRemainderSeq (q :: r :: cs)) :
    IsSignedRemainderSeq (p :: q :: r :: cs) where
  nonzero s hs := by
    first
    | rcases List.mem_cons.mp hs with rfl | hs
      · exact hp
      · exact h.nonzero s hs
  relation i p0 p1 p2 h0 h1 h2 := by
    first
    | cases i with
      | zero =>
        have he0 : p = p0 := by simpa using h0
        have he1 : q = p1 := by simpa using h1
        have he2 : r = p2 := by simpa using h2
        simpa [← he0, ← he1, ← he2] using hrel
      | succ i =>
        exact h.relation i p0 p1 p2 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  terminal pre p0 p1 heq := by
    first
    | cases pre with
      | nil => simp at heq
      | cons s pre =>
        have ht : q :: r :: cs = pre ++ [p0, p1] := (List.cons.inj heq).2
        exact h.terminal pre p0 p1 ht

theorem tail {p : Polynomial R} {cs : List (Polynomial R)} (h : IsSignedRemainderSeq (p :: cs)) :
    IsSignedRemainderSeq cs where
  nonzero q hq := h.nonzero q (List.mem_cons_of_mem _ hq)
  relation i q0 q1 q2 h0 h1 h2 :=
    h.relation (i + 1) q0 q1 q2 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  terminal pre q r heq := h.terminal (p :: pre) q r (by simp [heq])

/-- The terminal polynomial divides every chain entry. -/
theorem last_dvd {cs : List (Polynomial R)} (h : IsSignedRemainderSeq cs) {d : Polynomial R}
    (hd : cs.getLast? = some d) : ∀ p ∈ cs, d ∣ p := by
  first
  | induction cs with
    | nil => simp at hd
    | cons p cs ih =>
      cases cs with
      | nil =>
        have hpd : p = d := by simpa using hd
        subst p
        simp
      | cons q cs =>
        have hd' : (q :: cs).getLast? = some d := by simpa using hd
        have ht := ih h.tail hd'
        have hdp : d ∣ p := by
          cases cs with
          | nil => exact dvd_trans (ht q (by simp)) (h.terminal [] p q rfl)
          | cons r cs =>
            exact (h.relation 0 p q r rfl rfl rfl).dvd
              (ht q (by simp)) (ht r (by simp))
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hdp
        · exact ht s hs

/-- Dividing out a nonzero common factor preserves the signed chain conditions:
if `cs.map (d * ·)` is signed, so is `cs`. -/
theorem cancel {d : Polynomial R} {cs : List (Polynomial R)} (hd : d ≠ 0)
    (h : IsSignedRemainderSeq (cs.map (d * ·))) : IsSignedRemainderSeq cs where
  nonzero p hp hp0 := h.nonzero (d * p) (List.mem_map.mpr ⟨p, hp, rfl⟩) (by simp [hp0])
  relation i p q r h0 h1 h2 := IsRemainder.cancel hd (h.relation i (d * p) (d * q) (d * r)
    (by simp [List.getElem?_map, h0]) (by simp [List.getElem?_map, h1])
    (by simp [List.getElem?_map, h2]))
  terminal pre p q heq := (mul_dvd_mul_iff_left hd).mp
    (h.terminal (pre.map (d * ·)) (d * p) (d * q) (by simp [heq]))

variable [IsStrictOrderedRing R]

/-- A signed remainder chain with a root-free last entry is alternating. -/
theorem isAlternating {cs : List (Polynomial R)} (h : IsSignedRemainderSeq cs)
    (hlast : ∀ q, cs.getLast? = some q → ∀ x, q.eval x ≠ 0) : IsAlternating cs := by
  first
  | induction cs with
    | nil => exact ⟨h.nonzero, hlast, by simp⟩
    | cons p cs ih =>
      have ht : IsAlternating cs := ih h.tail (fun q hq x => by
        cases cs with
        | nil => simp at hq
        | cons s cs => exact hlast q (by simpa using hq) x)
      refine ⟨h.nonzero, hlast, ?_⟩
      intro i q0 q1 q2 h0 h1 h2 x hz
      cases i with
      | succ i =>
        exact ht.alternate i q0 q1 q2
          (by simpa using h0) (by simpa using h1) (by simpa using h2) x hz
      | zero =>
        have h0' : p = q0 := by simpa using h0
        subst q0
        cases cs with
        | nil => simp at h1
        | cons q cs =>
          have h1' : q = q1 := by simpa using h1
          subst q1
          cases cs with
          | nil => simp at h2
          | cons r cs =>
            have h2' : r = q2 := by simpa using h2
            subst q2
            exact (h.relation 0 p q r rfl rfl rfl).alternate hz (ht.second_eval_ne_zero hz)

/-- Mathlib's signed remainder sequence satisfies the algebraic chain conditions. -/
theorem sturmSeq (p q : R[X]) : IsSignedRemainderSeq (Polynomial.sturmSeq p q) := by
  first
  | classical
    induction p, q using Polynomial.sturmSeq.induct
    next q =>
      rw [sturmSeq_zero_left]
      exact ⟨by simp, by simp, by simp⟩
    next p q hp ih =>
      by_cases hq : q = 0
      · subst q
        rw [sturmSeq_zero_right, ite_eq_right hp]
        exact IsSignedRemainderSeq.singleton hp
      rw [sturmSeq_cons hp, sturmSeq_cons hq]
      by_cases hr : -p % q = 0
      · rw [hr, sturmSeq_zero_left]
        exact IsSignedRemainderSeq.pair hp (dvd_neg.mp (EuclideanDomain.mod_eq_zero.mp hr))
      · rw [sturmSeq_cons hr]
        refine IsSignedRemainderSeq.cons hp ?_ ?_
        · refine IsRemainder.of_identity 1 1 (p / q) zero_lt_one zero_lt_one ?_
          rw [map_one, one_mul, one_mul, neg_mod, sub_neg_eq_add]
          exact (EuclideanDomain.mod_add_div p q).symm.trans (by ring)
        · rwa [sturmSeq_cons hq, sturmSeq_cons hr] at ih

/-- Divide every entry by the terminal common factor. The resulting chain is
alternating and ends at `1`, even when the original terminal factor is nonconstant. -/
theorem exists_isAlternating {cs : List (Polynomial R)} (h : IsSignedRemainderSeq cs)
    {d : Polynomial R}
    (hd : cs.getLast? = some d) :
    ∃ ds : List (Polynomial R), cs = ds.map (d * ·) ∧
      ds.getLast? = some 1 ∧ IsSignedRemainderSeq ds ∧ IsAlternating ds := by
  first
  | have hdm : d ∈ cs := List.mem_of_getLast? hd
    have hd0 : d ≠ 0 := h.nonzero d hdm
    let ds := cs.map (· / d)
    have hmap : cs = ds.map (d * ·) := by
      symm
      rw [List.map_map]
      conv_rhs => rw [← List.map_id cs]
      exact List.map_congr_left (fun p hp => EuclideanDomain.mul_div_cancel' hd0 (h.last_dvd hd p hp))
    have hlast : ds.getLast? = some 1 := by
      simp [ds, List.getLast?_map, hd, EuclideanDomain.div_self hd0]
    have hs : IsSignedRemainderSeq ds := cancel hd0 (hmap ▸ h)
    refine ⟨ds, hmap, hlast, hs, hs.isAlternating ?_⟩
    intro q hq x
    rw [hlast] at hq
    cases hq
    simp

end IsSignedRemainderSeq

end TauCeti.Sturm
end -- closes the original EOF section from source line 20
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/SignedRemainders.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/Sum.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Signed root sums for alternating Sturm chains

The local jumps of a alternating chain telescope to a signed sum over the roots
of its first polynomial in an open interval. Only those roots must be simple;
the endpoints may be roots of interior entries, but not of the first entry.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The finite union of the roots of all entries of a polynomial list. -/
private noncomputable def rootsFinset (cs : List (Polynomial R)) : Finset R :=
  cs.toFinset.biUnion (fun q => q.roots.toFinset)

omit [IsStrictOrderedRing R] in
private theorem mem_rootsFinset {cs : List (Polynomial R)} (hne : ∀ q ∈ cs, q ≠ 0) {x : R} :
    x ∈ rootsFinset cs ↔ ∃ q ∈ cs, q.eval x = 0 := by
  first
  | simp only [rootsFinset, Finset.mem_biUnion, List.mem_toFinset, Multiset.mem_toFinset]
    exact exists_congr fun q => and_congr_right fun hq => Polynomial.mem_roots (hne q hq)

namespace IsAlternating

variable [IsRealClosed R]

/-- Moving right from a nonroot of the head changes no variations until the
next chain zero, even if an interior entry vanishes at the endpoint. -/
private theorem eq_right {cs : List (Polynomial R)} (h : IsAlternating cs) {a c : R} (hac : a < c)
    (ha : ∀ p, cs.head? = some p → p.eval a ≠ 0)
    (hz : ∀ x, a < x → x ≤ c → x ∉ rootsFinset cs) :
    signVariationsAt cs a = signVariationsAt cs c := by
  first
  | symm
    refine h.signVariationsAt_eq c a ?_ ha ?_
    · intro q hq hqc
      exact hz c hac le_rfl ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqc⟩)
    · intro q hq hqa
      symm
      apply Polynomial.sign_eval_const _ hac.le
      intro x hx hqx
      rcases hx.1.eq_or_lt with hax | hax
      · exact hqa (hax ▸ hqx)
      · exact hz x hax hx.2 ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqx⟩)

/-- The corresponding left-endpoint identity. -/
private theorem eq_left {cs : List (Polynomial R)} (h : IsAlternating cs) {c b : R} (hcb : c < b)
    (hb : ∀ p, cs.head? = some p → p.eval b ≠ 0)
    (hz : ∀ x, c ≤ x → x < b → x ∉ rootsFinset cs) :
    signVariationsAt cs c = signVariationsAt cs b := by
  first
  | refine h.signVariationsAt_eq c b ?_ hb ?_
    · intro q hq hqc
      exact hz c le_rfl hcb ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqc⟩)
    · intro q hq hqb
      apply Polynomial.sign_eval_const _ hcb.le
      intro x hx hqx
      rcases hx.2.eq_or_lt with hxb | hxb
      · exact hqb (hxb ▸ hqx)
      · exact hz x hx.1 hxb ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqx⟩)

/-- The signed variation formula with endpoints away from every chain zero. -/
private theorem sum_sign_of_nonzero {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsAlternating (p :: q :: cs))
    {a b : R} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : a ∉ rootsFinset (p :: q :: cs))
    (hb : b ∉ rootsFinset (p :: q :: cs)) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  first
  | classical
    set chain := p :: q :: cs
    let w : R → ℤ := fun r => if p.eval r = 0 then
      (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) else 0
    have hsum := Finset.sum_jumps (a₀ := a) (b₀ := b)
      (rootsFinset chain) (fun x => (signVariationsAt chain x : ℤ)) w
      (fun a b _ _ hab hn => by
        congr 1
        apply signVariationsAt_const chain hab.le
        intro s hs x hx hz
        exact hn x ((mem_rootsFinset h.nonzero).mpr ⟨s, hs, hz⟩) hx)
      (fun a r b haa hbb har hrb _ hn => by
        have hz : ∀ s ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0 := by
          intro s hs x hx hxr hsx
          exact hxr (hn x ((mem_rootsFinset h.nonzero).mpr ⟨s, hs, hsx⟩) hx)
        by_cases hr : p.eval r = 0
        · simpa [w, hr] using h.root_jump har hrb hr
            (hsimple r (haa.trans_lt har) (hrb.trans_le hbb) hr) hz
        · have hsame := h.signVariationsAt_nonroot har hrb (fun s hs => by cases hs; exact hr) hz
          simp only [w, chain, ite_eq_right hr, hsame.1.trans hsame.2, sub_self]) hab ha hb
    rw [hsum]
    let A := p.roots.toFinset.filter (fun r => a < r ∧ r < b)
    let B := (rootsFinset chain).filter (fun r => a < r ∧ r < b)
    have hAB : A ⊆ B := by
      intro r hr
      obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
      have hpr : p.eval r = 0 := (Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mp
        (Multiset.mem_toFinset.mp hr)
      exact Finset.mem_filter.mpr ⟨(mem_rootsFinset h.nonzero).mpr ⟨p, by simp [chain], hpr⟩, hi⟩
    have hrestrict : ∑ r ∈ A, w r = ∑ r ∈ B, w r := by
      apply Finset.sum_subset hAB
      intro r hr hn
      have hpr : p.eval r ≠ 0 := by
        intro hz
        apply hn
        exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mpr hz),
          (Finset.mem_filter.mp hr).2⟩
      simp [w, hpr]
    rw [← hrestrict]
    apply Finset.sum_congr rfl
    intro r hr
    have hpr : p.eval r = 0 := (Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mp
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)
    simp [w, hpr]

/-- The signed Sturm formula on an interval whose endpoints are not roots of
the head polynomial. Interior entries may vanish at either endpoint. -/
theorem sum_sign {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsAlternating (p :: q :: cs))
    {a b : R} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  first
  | classical
    set chain := p :: q :: cs
    obtain ⟨m, ham, hmb⟩ := exists_between hab
    obtain ⟨c, hac, hcm, hc⟩ := Finset.exists_right_gap (rootsFinset chain) ham
    obtain ⟨d, hmd, hdb, hd⟩ := Finset.exists_left_gap (rootsFinset chain) hmb
    have hcd := hcm.trans hmd
    have hcZ : c ∉ rootsFinset chain := fun hz => (hc c hz hac).false
    have hdZ : d ∉ rootsFinset chain := fun hz => (hd d hz hdb).false
    have haV : signVariationsAt chain a = signVariationsAt chain c :=
      h.eq_right hac (fun s hs => by cases hs; exact ha)
        (fun x hax hxc hx => (hc x hx hax).not_ge hxc)
    have hbV : signVariationsAt chain d = signVariationsAt chain b :=
      h.eq_left hdb (fun s hs => by cases hs; exact hb)
        (fun x hdx hxb hx => (hd x hx hxb).not_ge hdx)
    have hfilters : p.roots.toFinset.filter (fun r => a < r ∧ r < b) =
        p.roots.toFinset.filter (fun r => c < r ∧ r < d) := by
      ext r
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hr, har, hrb⟩
        have hrZ : r ∈ rootsFinset chain := (mem_rootsFinset h.nonzero).mpr
          ⟨p, by simp [chain], (Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mp
            (Multiset.mem_toFinset.mp hr)⟩
        exact ⟨hr, hc r hrZ har, hd r hrZ hrb⟩
      · rintro ⟨hr, hcr, hrd⟩
        exact ⟨hr, hac.trans hcr, hrd.trans hdb⟩
    rw [hfilters]
    rw [haV, ← hbV]
    exact h.sum_sign_of_nonzero
      (fun r hcr hrd => hsimple r (hac.trans hcr) (hrd.trans hdb)) hcd hcZ hdZ

end IsAlternating

end TauCeti.Sturm
end -- closes the original EOF section from source line 18
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/Sum.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/Tarski.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Sturm–Tarski over an arbitrary real closed ordered field

`IsTarskiSeed` relates the second chain entry to `f * p'` modulo `p`.
`sum_sign` identifies the variation difference of a signed remainder chain
with the sum of query signs at the distinct roots in an open interval. Positive
pseudo-remainder scalings and a nonconstant terminal common factor are allowed,
and the head polynomial need not be squarefree. `IsTarskiSeed.sign_eq_of_mul`,
`IsTarskiSeed.eval_eq_zero_of_mul`, `IsTarskiSeed.derivative_eval_ne_zero_of_mul` and
`IsTarskiSeed.sign_mul_eq_of_mul` describe the query at the roots of a seed from which a
common factor of the head and second entry has been removed; `IsTarskiSeed.sign_eq` and
`IsTarskiSeed.eval_eq_zero` are the forms without a common factor.
The concrete `Polynomial.sturmSeq` specialization supplies sign sums and root
counts, and is the finite-interval basis for the infinite-endpoint formulas.

## References

For the classical sign-sum identity, see S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://mariefrancoiseroy.pages.math.cnrs.fr/bpr-ed2-posted3.pdf),
revised second edition, §2.2.2, Theorem 2.73 (Tarski’s theorem).
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The positive-scaled seed congruence between the second entry and `f * p'`
modulo `p`. Both scalings are explicit to cover signed pseudo-remainders.
A degree bound identifies the actual remainder, but is unnecessary for soundness. -/
def IsTarskiSeed (p f q : Polynomial R) : Prop :=
  IsRemainder (f * p.derivative) p (-q)

namespace IsTarskiSeed

omit [IsStrictOrderedRing R] in
/-- Construct a query seed from its positive-scaled congruence identity. -/
theorem of_identity {p f q : Polynomial R} (a b : R) (u : Polynomial R)
    (ha : 0 < a) (hb : 0 < b)
    (heq : C a * (f * p.derivative) = u * p + C b * q) : IsTarskiSeed p f q := by
  first
  | exact IsRemainder.of_identity a b u ha hb (by simpa using heq)

omit [IsStrictOrderedRing R] in
/-- A query seed supplies positive scalings and the congruence identity. -/
theorem exists_identity {p f q : Polynomial R} (h : IsTarskiSeed p f q) :
    ∃ a b : R, ∃ u : Polynomial R,
      0 < a ∧ 0 < b ∧ C a * (f * p.derivative) = u * p + C b * q := by
  first
  | obtain ⟨a, b, u, ha, hb, heq⟩ := IsRemainder.exists_identity h
    exact ⟨a, b, u, ha, hb, by simpa using heq⟩

/-- The unreduced derivative query is a valid Tarski seed. -/
theorem mul_derivative (p f : R[X]) : IsTarskiSeed p f (f * p.derivative) :=
  of_identity 1 1 0 zero_lt_one zero_lt_one (by simp)

/-- Reducing the derivative query modulo the head gives a valid Tarski seed. -/
theorem mod (p f : R[X]) : IsTarskiSeed p f ((f * p.derivative) % p) := by
  first
  | classical
    refine of_identity 1 1 ((f * p.derivative) / p) zero_lt_one zero_lt_one ?_
    rw [map_one, one_mul, one_mul]
    exact (EuclideanDomain.mod_add_div (f * p.derivative) p).symm.trans (by ring)

/-- Clearing every factor `X - C r` of a common factor `d` from the seed identity of
`d * p` and `d * q`. The scalar `k` is the multiplicity of `r` as a root of `d`, and `e` is the
cofactor of `(X - C r) ^ k` in `d`. -/
private theorem exists_identity_X_sub_C {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q))
    (hd : d ≠ 0) (r : R) :
    ∃ a b : R, ∃ u e : R[X], ∃ k : ℕ, 0 < a ∧ 0 < b ∧ e.eval r ≠ 0 ∧
      (d.eval r = 0 → k ≠ 0) ∧
      C a * f * (C (k : R) * (e * p) + (X - C r) * derivative (e * p)) =
        (X - C r) * (e * (u * p + C b * q)) := by
  first
  | obtain ⟨a, b, u, ha, hb, heq⟩ := h.exists_identity
    obtain ⟨e, hde, he⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd r
    refine ⟨a, b, u, e, rootMultiplicity r d, ha, hb, fun h => he (dvd_iff_isRoot.mpr h),
      fun h => (rootMultiplicity_pos hd).mpr h |>.ne', ?_⟩
    -- Multiplying by `X - C r` turns the derivative of `(X - C r) ^ k * g` into a multiple
    -- of `(X - C r) ^ k`, which is then cancelled.
    have hpow (k : ℕ) (g : R[X]) : (X - C r) * derivative ((X - C r) ^ k * g) =
        (X - C r) ^ k * (C (k : R) * g + (X - C r) * derivative g) := by
      rcases k with _ | k
      · simp
      · rw [derivative_mul, derivative_X_sub_C_pow, Nat.add_sub_cancel]
        ring
    have hd' := hpow (rootMultiplicity r d) (e * p)
    -- Reassociate so that the opaque `derivative` atom matches `d * p` after `rw [hde]`.
    rw [← mul_assoc] at hd'
    rw [hde] at heq
    apply mul_left_cancel₀ (pow_ne_zero (rootMultiplicity r d) (X_sub_C_ne_zero r))
    linear_combination (X - C r) * heq - C a * f * hd'

/-- If `q` is a Tarski seed for the head `d * p` and query `f` after the common factor `d` is
removed from it, then at every root `r` of `p` the sign of `p' r * f r` is the sign of `q r`.
The point `r` may be a multiple root of `d * p`. -/
theorem sign_eq_of_mul {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q)) (hd : d ≠ 0) {r : R}
    (hr : p.eval r = 0) :
    SignType.sign (p.derivative.eval r * f.eval r) = SignType.sign (q.eval r) := by
  first
  | obtain ⟨a, b, u, e, k, ha, hb, he, -, heq⟩ := exists_identity_X_sub_C h hd r
    obtain ⟨s, rfl⟩ := dvd_iff_isRoot.mpr hr
    have hcancel : C a * f * (C (k : R) * (e * s) + derivative (e * ((X - C r) * s))) =
        e * (u * ((X - C r) * s) + C b * q) :=
      mul_left_cancel₀ (X_sub_C_ne_zero r) (by linear_combination heq)
    have hev := congrArg (eval r) hcancel
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_mul, eval_add,
      eval_sub, eval_C, eval_X, sub_self, sub_zero, zero_mul, mul_zero, zero_add, add_zero,
      one_mul] at hev
    have hk : (0 : R) < a * (k + 1) := by positivity
    have hbq : b * q.eval r = a * (k + 1) * (s.eval r * f.eval r) :=
      mul_left_cancel₀ he (by linear_combination -hev)
    have hs := congrArg SignType.sign hbq
    rw [sign_mul, sign_mul (a * (k + 1)), sign_pos hb, sign_pos hk, one_mul, one_mul] at hs
    simpa [derivative_mul] using hs.symm

/-- A root of the removed common factor `d` that is not a root of the reduced head `p` is a
zero of the query. -/
theorem eval_eq_zero_of_mul {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q)) (hd : d ≠ 0)
    {r : R} (hdr : d.eval r = 0) (hp : p.eval r ≠ 0) : f.eval r = 0 := by
  first
  | obtain ⟨a, b, u, e, k, ha, _, he, hk, heq⟩ := exists_identity_X_sub_C h hd r
    have hev := congrArg (eval r) heq
    simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self, zero_mul, add_zero] at hev
    simpa [ha.ne', hk hdr, he, hp] using hev

/-- At a root `r` of the reduced head `p` at which the reduced second entry `q` does not
vanish, `r` is a simple root of `p`. This holds even if `r` is a multiple root of `d * p`. -/
theorem derivative_eval_ne_zero_of_mul {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q))
    (hd : d ≠ 0) {r : R} (hr : p.eval r = 0) (hq : q.eval r ≠ 0) :
    p.derivative.eval r ≠ 0 := by
  first
  | intro hz
    have hs := h.sign_eq_of_mul hd hr
    rw [hz, zero_mul, sign_zero] at hs
    exact hq (sign_eq_zero_iff.mp hs.symm)

/-- At a root `r` of the reduced head `p` at which the reduced second entry `q` does not
vanish, the sign of `p' r * q r` is the sign of the query `f r`. -/
theorem sign_mul_eq_of_mul {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q)) (hd : d ≠ 0)
    {r : R} (hr : p.eval r = 0) (hq : q.eval r ≠ 0) :
    SignType.sign (p.derivative.eval r * q.eval r) = SignType.sign (f.eval r) := by
  first
  | have hd' : SignType.sign (p.derivative.eval r) ≠ 0 := by
      simpa using h.derivative_eval_ne_zero_of_mul hd hr hq
    have numeric : ∀ s t : SignType, s ≠ 0 → s * (s * t) = t := by decide
    rw [sign_mul, ← h.sign_eq_of_mul hd hr, sign_mul]
    exact numeric _ _ hd'

/-- At every root `r` of the head `p` of a Tarski seed, the sign of `p' r * f r` is the sign
of `q r`. The point `r` may be a multiple root of `p`. -/
theorem sign_eq {p f q : R[X]} (h : IsTarskiSeed p f q) {r : R} (hr : p.eval r = 0) :
    SignType.sign (p.derivative.eval r * f.eval r) = SignType.sign (q.eval r) :=
  IsTarskiSeed.sign_eq_of_mul (d := 1) (by simpa using h) one_ne_zero hr

/-- A zero query seed makes the query vanish at every root of the nonzero head. -/
theorem eval_eq_zero {p f : R[X]} (h : IsTarskiSeed p f 0) (hp : p ≠ 0) {r : R}
    (hr : p.eval r = 0) : f.eval r = 0 :=
  IsTarskiSeed.eval_eq_zero_of_mul (p := 1) (q := 0) (by simpa using h) hp hr (by simp)

/-- A valid query seed remains valid as the second entry of Mathlib's sequence,
including the singleton case. -/
theorem sturmSeq {p f q : R[X]} (h : IsTarskiSeed p f q) :
    IsTarskiSeed p f ((Polynomial.sturmSeq p q).tail.head?.getD 0) := by
  first
  | classical
    by_cases hp : p = 0
    · subst p
      simpa using mul_derivative (0 : R[X]) f
    simpa only [List.head?_tail, getD_getElem?_sturmSeq hp] using h

end IsTarskiSeed

/-- Removing a common factor preserves the query sum: its lost roots have zero query sign. -/
private theorem IsTarskiSeed.sum_roots_mul {d p0 f q0 : R[X]}
    (hseed : IsTarskiSeed (d * p0) f (d * q0)) (hd : d ≠ 0) (hp0 : p0 ≠ 0) (P : R → Prop)
    [DecidablePred P] :
    (∑ r ∈ p0.roots.toFinset.filter P, (SignType.sign (f.eval r) : ℤ)) =
      ∑ r ∈ (d * p0).roots.toFinset.filter P, (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    have hpne : d * p0 ≠ 0 := mul_ne_zero hd hp0
    apply Finset.sum_subset
    · intro r hr
      obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
      have hr0 : p0.eval r = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hr)
      exact Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((mem_roots hpne).mpr (by simp [hr0])), hi⟩
    · intro r hr hn
      obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
      have hpr : (d * p0).eval r = 0 := (mem_roots hpne).mp (Multiset.mem_toFinset.mp hr)
      have hpr0 : p0.eval r ≠ 0 := by
        intro hz
        exact hn (Finset.mem_filter.mpr
          ⟨Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr hz), hi⟩)
      have hdr : d.eval r = 0 := by
        rw [eval_mul] at hpr
        exact (mul_eq_zero.mp hpr).resolve_right hpr0
      rw [hseed.eval_eq_zero_of_mul hd hdr hpr0, sign_zero]
      rfl

/-- A zero query seed makes the query vanish at every root of the nonzero head, so its
sign sum is zero on any finite set of such roots. -/
theorem IsTarskiSeed.sum_sign_eq_zero {p f : Polynomial R} (hseed : IsTarskiSeed p f 0)
    (hp : p ≠ 0) (Z : Finset R) (hZ : ∀ r ∈ Z, p.eval r = 0) :
    ∑ r ∈ Z, (SignType.sign (f.eval r) : ℤ) = 0 := by
  first
  | apply Finset.sum_eq_zero
    intro r hr
    rw [hseed.eval_eq_zero hp (hZ r hr), sign_zero]
    rfl

variable [IsRealClosed R]

/-- **Sturm–Tarski**, for a positively scaled signed remainder chain. The last
entry may be a nonconstant common factor. Roots at which the query vanishes
contribute zero, and roots of interior entries at the endpoints are allowed.
The roots of the head polynomial may be multiple. -/
private theorem sum_sign_cons {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: q :: cs)) (hseed : IsTarskiSeed p f q)
    {a b : R} (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    -- Remove the terminal common factor, apply the alternating-chain formula,
    -- then restore roots of the common factor, whose query contributions vanish.
    obtain ⟨d, hd⟩ : ∃ d, (p :: q :: cs).getLast? = some d :=
      ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
    have hd0 : d ≠ 0 := h.nonzero d (List.mem_of_getLast? hd)
    obtain ⟨ds, hmap, _, _, hreg⟩ := h.exists_isAlternating hd
    cases ds with
    | nil => simp at hmap
    | cons p0 ds =>
      cases ds with
      | nil => simp at hmap
      | cons q0 ds =>
        have hp : p = d * p0 := by
          have := hmap
          simp only [List.map_cons, List.cons.injEq] at this
          exact this.1
        have hq : q = d * q0 := by
          have := hmap
          simp only [List.map_cons, List.cons.injEq] at this
          exact this.2.1
        subst hp hq
        have ha0 : d.eval a ≠ 0 ∧ p0.eval a ≠ 0 := by simpa [eval_mul] using ha
        have hb0 : d.eval b ≠ 0 ∧ p0.eval b ≠ 0 := by simpa [eval_mul] using hb
        have hV (x : R) (hx : d.eval x ≠ 0) :
            signVariationsAt (d * p0 :: d * q0 :: cs) x = signVariationsAt (p0 :: q0 :: ds) x := by
          rw [hmap]
          exact signVariationsAt_map_mul _ hx
        rw [hV a ha0.1, hV b hb0.1,
          hreg.sum_sign (fun r _ _ hr => hseed.derivative_eval_ne_zero_of_mul hd0 hr
            (hreg.second_eval_ne_zero hr)) hab ha0.2 hb0.2]
        have hp0 : p0 ≠ 0 := hreg.nonzero p0 (by simp)
        calc
          _ = ∑ r ∈ p0.roots.toFinset.filter (fun r => a < r ∧ r < b),
              (SignType.sign (f.eval r) : ℤ) := by
            apply Finset.sum_congr rfl
            intro r hr
            have hr0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)
            rw [hseed.sign_mul_eq_of_mul hd0 hr0 (hreg.second_eval_ne_zero hr0)]
          _ = _ := hseed.sum_roots_mul hd0 hp0 _

/-- **Sturm–Tarski** for any nonempty signed remainder chain, including a singleton.
The seed is the second entry, or zero when the chain has only its head.
The head polynomial may have multiple roots. -/
theorem sum_sign {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    {a b : R} (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: cs) a : ℤ) - signVariationsAt (p :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    cases cs with
    | nil =>
      simpa using (hseed.sum_sign_eq_zero (h.nonzero p (by simp)) _
        (fun r hr => isRoot_of_mem_roots
          (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))).symm
    | cons q cs => exact sum_sign_cons h hseed hab ha hb

/-- Sturm–Tarski directly for Mathlib's concrete signed remainder sequence. -/
theorem sum_sign_sturmSeq (p f : R[X]) {a b : R} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0) :
    (signVariationsAt (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAt (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    have hp : p ≠ 0 := fun h => ha (by simp [h])
    have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign hsigned hseed hab ha hb

/-- Classical Sturm counting of distinct roots in `(a, b)`, counted without
multiplicity. Neither endpoint may be a root. -/
theorem card_roots_toFinset (p : R[X]) {a b : R} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0) :
    (signVariationsAt (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAt (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r < b)).card := by
  first
  | simpa using sum_sign_sturmSeq p 1 hab ha hb

end TauCeti.Sturm
end -- closes the original EOF section from source line 32
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/Tarski.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/OneSided.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Sturm–Tarski with one-sided endpoints

`TauCeti.Sturm.signVariationsRight cs a` and `TauCeti.Sturm.signVariationsLeft cs a` count the
sign variations of a polynomial list immediately to the right and to the left of `a`. They are
computed algebraically from the one-sided signs `Polynomial.derivSignRight` and
`Polynomial.derivSignLeft`, and are realized by evaluation at every point of a small enough interval
on the corresponding side of `a`. They satisfy the append, negation and zero-deletion laws of
`List.signVariations`, and multiplying every entry by a common nonzero polynomial does not change
them, even at a root of that polynomial. So a common factor of the two inputs of
`Polynomial.sturmSeq` does not change its one-sided variations anywhere.

With these, Sturm–Tarski holds on every bounded interval, with no condition on the endpoints.
Write `V(a⁺)` and `V(b⁻)` for the right-hand variations at `a` and the left-hand variations at
`b` of a signed remainder chain whose head is `p` and whose second entry is the seed of the
query `f`. For `a < b`, the difference `V(a⁺) - V(b⁻)` is the sum of the signs of `f` at the
distinct roots of `p` in `(a, b)`, even when `a` or `b` is a root of `p` or of another chain
entry. A root `c` of `p` contributes the sign of `f` at `c` to a closed endpoint, and this
contribution is the drop `V(c⁻) - V(c⁺)` in variations across `c`. The formulas for
`(a, b]`, `[a, b)` and `[a, b]` add these endpoint contributions explicitly to `V(a⁺) - V(b⁻)`.
Specializing to `Polynomial.sturmSeq` and to the query `1` counts distinct roots.

## Main declarations

* `TauCeti.Sturm.signVariationsRight`, `TauCeti.Sturm.signVariationsLeft`: one-sided
  variations.
* `TauCeti.Sturm.signVariationsRight_append`, `TauCeti.Sturm.signVariationsRight_map_neg`,
  `TauCeti.Sturm.signVariationsRight_map_mul`, `TauCeti.Sturm.signVariationsRight_filter_ne_zero`
  and their left-hand analogues: the append, negation, scaling and zero-deletion laws.
* `TauCeti.Sturm.sum_sign_Ioo`: Sturm–Tarski on `(a, b)` as `V(a⁺) - V(b⁻)`.
* `TauCeti.Sturm.signVariationsLeft_sub_signVariationsRight`: the contribution of a point.
* `TauCeti.Sturm.sum_sign_Ioc`, `TauCeti.Sturm.sum_sign_Ico`, `TauCeti.Sturm.sum_sign_Icc`:
  Sturm–Tarski on half-open and closed intervals.
* `TauCeti.Sturm.card_roots_toFinset_Ioo` and its half-open and closed analogues: Sturm's
  count of distinct roots.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (Tarski's theorem) and Chapter 10.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial Set SignType

section Basic

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The sign variations of a polynomial list immediately to the right of `a`: the variations
of the right-hand signs `Polynomial.derivSignRight` of its entries at `a`. -/
noncomputable def signVariationsRight (cs : List R[X]) (a : R) : ℕ :=
  List.signVariations (cs.map (·.derivSignRight a))

/-- The sign variations of a polynomial list immediately to the left of `a`: the variations
of the left-hand signs `Polynomial.derivSignLeft` of its entries at `a`. -/
noncomputable def signVariationsLeft (cs : List R[X]) (a : R) : ℕ :=
  List.signVariations (cs.map (·.derivSignLeft a))

theorem signVariationsRight_def (cs : List R[X]) (a : R) :
    signVariationsRight cs a = List.signVariations (cs.map (·.derivSignRight a)) := (rfl)

theorem signVariationsLeft_def (cs : List R[X]) (a : R) :
    signVariationsLeft cs a = List.signVariations (cs.map (·.derivSignLeft a)) := (rfl)

@[simp, grind =]
theorem signVariationsRight_nil (a : R) : signVariationsRight ([] : List R[X]) a = 0 := by
  first
  | simp [signVariationsRight_def]

@[simp, grind =]
theorem signVariationsLeft_nil (a : R) : signVariationsLeft ([] : List R[X]) a = 0 := by
  first
  | simp [signVariationsLeft_def]

@[simp, grind =]
theorem signVariationsRight_singleton (p : R[X]) (a : R) : signVariationsRight [p] a = 0 := by
  first
  | simp [signVariationsRight_def]

@[simp, grind =]
theorem signVariationsLeft_singleton (p : R[X]) (a : R) : signVariationsLeft [p] a = 0 := by
  first
  | simp [signVariationsLeft_def]

/-- Evaluation at a point where every entry has its right-hand sign at `a` realizes the
right-hand variations at `a`. -/
theorem signVariationsAt_eq_right {cs : List R[X]} {a x : R}
    (h : ∀ p ∈ cs, sign (p.eval x) = p.derivSignRight a) :
    signVariationsAt cs x = signVariationsRight cs a := by
  first
  | rw [signVariationsAt_def, signVariationsRight_def,
      ← List.signVariations_map_sign (cs.map (eval x)), List.map_map]
    exact congrArg _ (List.map_congr_left h)

/-- Evaluation at a point where every entry has its left-hand sign at `a` realizes the
left-hand variations at `a`. -/
theorem signVariationsAt_eq_left {cs : List R[X]} {a x : R}
    (h : ∀ p ∈ cs, sign (p.eval x) = p.derivSignLeft a) :
    signVariationsAt cs x = signVariationsLeft cs a := by
  first
  | rw [signVariationsAt_def, signVariationsLeft_def,
      ← List.signVariations_map_sign (cs.map (eval x)), List.map_map]
    exact congrArg _ (List.map_congr_left h)

/-- If no entry vanishes at `a`, the right-hand variations are the variations at `a`. -/
theorem signVariationsRight_eq_signVariationsAt {cs : List R[X]} {a : R}
    (h : ∀ p ∈ cs, p.eval a ≠ 0) : signVariationsRight cs a = signVariationsAt cs a :=
  (signVariationsAt_eq_right fun p hp => (derivSignRight_eq_sign_eval p (h p hp)).symm).symm

/-- If no entry vanishes at `a`, the left-hand variations are the variations at `a`. -/
theorem signVariationsLeft_eq_signVariationsAt {cs : List R[X]} {a : R}
    (h : ∀ p ∈ cs, p.eval a ≠ 0) : signVariationsLeft cs a = signVariationsAt cs a :=
  (signVariationsAt_eq_left fun p hp => (derivSignLeft_eq_sign_eval p (h p hp)).symm).symm

/-- Ordered coefficient embeddings preserve variations immediately to the right of a point. -/
@[simp]
theorem signVariationsRight_map {S : Type*} [CommRing S] [LinearOrder S]
    (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) (x : R) :
    signVariationsRight (cs.map (Polynomial.map f)) (f x) = signVariationsRight cs x := by
  first
  | simp only [signVariationsRight_def, List.map_map, Function.comp_def, derivSignRight_map _ f hf]

/-- Ordered coefficient embeddings preserve variations immediately to the left of a point. -/
@[simp]
theorem signVariationsLeft_map {S : Type*} [CommRing S] [LinearOrder S]
    (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) (x : R) :
    signVariationsLeft (cs.map (Polynomial.map f)) (f x) = signVariationsLeft cs x := by
  first
  | simp only [signVariationsLeft_def, List.map_map, Function.comp_def, derivSignLeft_map _ f hf]

/-- The right-hand variations at `a` of a concatenation are those of the two parts, plus one
exactly when the last nonzero right-hand sign of the first part is opposite to the first nonzero
right-hand sign of the second part. -/
theorem signVariationsRight_append (cs ds : List R[X]) (a : R) :
    signVariationsRight (cs ++ ds) a =
      signVariationsRight cs a +
        (if List.lastSign (cs.map (·.derivSignRight a)) *
            List.firstSign (ds.map (·.derivSignRight a)) = -1 then 1 else 0) +
        signVariationsRight ds a := by
  first
  | simp only [signVariationsRight_def, List.map_append, List.signVariations_append]

/-- The left-hand variations at `a` of a concatenation are those of the two parts, plus one
exactly when the last nonzero left-hand sign of the first part is opposite to the first nonzero
left-hand sign of the second part. -/
theorem signVariationsLeft_append (cs ds : List R[X]) (a : R) :
    signVariationsLeft (cs ++ ds) a =
      signVariationsLeft cs a +
        (if List.lastSign (cs.map (·.derivSignLeft a)) *
            List.firstSign (ds.map (·.derivSignLeft a)) = -1 then 1 else 0) +
        signVariationsLeft ds a := by
  first
  | simp only [signVariationsLeft_def, List.map_append, List.signVariations_append]

/-- Negating every entry does not change the right-hand variations at a point. -/
@[simp]
theorem signVariationsRight_map_neg [AddLeftMono R] (cs : List R[X]) (a : R) :
    signVariationsRight (cs.map Neg.neg) a = signVariationsRight cs a := by
  first
  | simpa only [signVariationsRight_def, List.map_map, Function.comp_def, derivSignRight_neg] using
      List.signVariations_map_of_sign_eq_neg (f := Neg.neg) (by decide) (cs.map (·.derivSignRight a))

/-- Negating every entry does not change the left-hand variations at a point. -/
@[simp]
theorem signVariationsLeft_map_neg [AddLeftMono R] (cs : List R[X]) (a : R) :
    signVariationsLeft (cs.map Neg.neg) a = signVariationsLeft cs a := by
  first
  | simpa only [signVariationsLeft_def, List.map_map, Function.comp_def, derivSignLeft_neg] using
      List.signVariations_map_of_sign_eq_neg (f := Neg.neg) (by decide) (cs.map (·.derivSignLeft a))

end Basic

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The right-hand variations at `a` split at any nonzero entry. -/
theorem signVariationsRight_append_cons_of_ne_zero (cs ds : List R[X]) {p : R[X]} (hp : p ≠ 0)
    (a : R) :
    signVariationsRight (cs ++ p :: ds) a =
      signVariationsRight (cs ++ [p]) a + signVariationsRight (p :: ds) a := by
  first
  | simpa only [signVariationsRight_def, List.map_append, List.map_cons, List.map_nil] using
      List.signVariations_append_cons_of_ne_zero _ _ ((derivSignRight_eq_zero_iff p a).not.2 hp)

/-- The left-hand variations at `a` split at any nonzero entry. -/
theorem signVariationsLeft_append_cons_of_ne_zero (cs ds : List R[X]) {p : R[X]} (hp : p ≠ 0)
    (a : R) :
    signVariationsLeft (cs ++ p :: ds) a =
      signVariationsLeft (cs ++ [p]) a + signVariationsLeft (p :: ds) a := by
  first
  | simpa only [signVariationsLeft_def, List.map_append, List.map_cons, List.map_nil] using
      List.signVariations_append_cons_of_ne_zero _ _ ((derivSignLeft_eq_zero_iff p a).not.2 hp)

/-- Deleting the zero entries does not change the right-hand variations. -/
@[simp]
theorem signVariationsRight_filter_ne_zero (cs : List R[X]) (a : R) :
    signVariationsRight (cs.filter fun p ↦ !decide (p = 0)) a = signVariationsRight cs a := by
  first
  | rw [signVariationsRight_def, signVariationsRight_def,
      ← List.signVariations_filter_ne_zero (cs.map _), List.filter_map]
    simp [Function.comp_def]

/-- Deleting the zero entries does not change the left-hand variations. -/
@[simp]
theorem signVariationsLeft_filter_ne_zero (cs : List R[X]) (a : R) :
    signVariationsLeft (cs.filter fun p ↦ !decide (p = 0)) a = signVariationsLeft cs a := by
  first
  | rw [signVariationsLeft_def, signVariationsLeft_def,
      ← List.signVariations_filter_ne_zero (cs.map _), List.filter_map]
    simp [Function.comp_def]

/-- Multiplying every entry by a common nonzero polynomial does not change the right-hand
variations at any point, even one where that polynomial vanishes. -/
theorem signVariationsRight_map_mul (cs : List R[X]) {d : R[X]} (hd : d ≠ 0) (a : R) :
    signVariationsRight (cs.map (d * ·)) a = signVariationsRight cs a := by
  first
  | simpa only [signVariationsRight_def, List.map_map, Function.comp_def, derivSignRight_mul] using
      List.signVariations_map_signType_mul_left (cs.map (·.derivSignRight a))
        ((derivSignRight_eq_zero_iff d a).not.2 hd)

/-- Multiplying every entry by a common nonzero polynomial does not change the left-hand
variations at any point, even one where that polynomial vanishes. -/
theorem signVariationsLeft_map_mul (cs : List R[X]) {d : R[X]} (hd : d ≠ 0) (a : R) :
    signVariationsLeft (cs.map (d * ·)) a = signVariationsLeft cs a := by
  first
  | simpa only [signVariationsLeft_def, List.map_map, Function.comp_def, derivSignLeft_mul] using
      List.signVariations_map_signType_mul_left (cs.map (·.derivSignLeft a))
        ((derivSignLeft_eq_zero_iff d a).not.2 hd)

end OrderedRing

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying both inputs by a common nonzero polynomial does not change the right-hand
variations of their signed remainder sequence. -/
@[simp]
theorem signVariationsRight_sturmSeq_mul_left {r : R[X]} (hr : r ≠ 0) (p q : R[X]) (a : R) :
    signVariationsRight (sturmSeq (r * p) (r * q)) a = signVariationsRight (sturmSeq p q) a := by
  first
  | rw [sturmSeq_mul_left hr, signVariationsRight_map_mul _ hr]

/-- Multiplying both inputs by a common nonzero polynomial does not change the left-hand
variations of their signed remainder sequence. -/
@[simp]
theorem signVariationsLeft_sturmSeq_mul_left {r : R[X]} (hr : r ≠ 0) (p q : R[X]) (a : R) :
    signVariationsLeft (sturmSeq (r * p) (r * q)) a = signVariationsLeft (sturmSeq p q) a := by
  first
  | rw [sturmSeq_mul_left hr, signVariationsLeft_map_mul _ hr]

/-- The right-hand variations at `a` are the variations at every point of a small enough
interval to the right of `a`. -/
theorem exists_signVariationsRight (cs : List R[X]) (a : R) :
    ∃ u, a < u ∧ ∀ x ∈ Ioo a u, signVariationsAt cs x = signVariationsRight cs a := by
  first
  | obtain ⟨u, hau, hu⟩ := cs.exists_signs_right a
    exact ⟨u, hau, fun x hx => signVariationsAt_eq_right fun p hp => hu p hp x hx⟩

/-- The left-hand variations at `a` are the variations at every point of a small enough
interval to the left of `a`. -/
theorem exists_signVariationsLeft (cs : List R[X]) (a : R) :
    ∃ l, l < a ∧ ∀ x ∈ Ioo l a, signVariationsAt cs x = signVariationsLeft cs a := by
  first
  | obtain ⟨l, hla, hl⟩ := cs.exists_signs_left a
    exact ⟨l, hla, fun x hx => signVariationsAt_eq_left fun p hp => hl p hp x hx⟩

variable [IsRealClosed R]

section Chain

variable {p f : R[X]} {cs : List R[X]}

/-- **Sturm–Tarski with one-sided endpoints.** For a signed remainder chain with head `p` and
query seed `f`, and any `a < b`, the right-hand variations at `a` minus the left-hand
variations at `b` is the sum of the signs of `f` at the distinct roots of `p` in `(a, b)`.
The endpoints may be roots of any chain entry. -/
theorem sum_sign_Ioo (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a < b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r < b, (sign (f.eval r) : ℤ) := by
  first
  | have hp : p ≠ 0 := h.nonzero p (by simp)
    -- Move the endpoints inwards to nearby points `a' < b'` realizing the one-sided signs.
    -- Then `p` has no roots in `(a, a']` or `[b', b)`, and `sum_sign` applies on `(a', b')`.
    obtain ⟨u, hau, hu⟩ := (p :: cs).exists_signs_right a
    obtain ⟨l, hlb, hl⟩ := (p :: cs).exists_signs_left b
    obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hau hab)
    obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hlb (ha'.trans_le (min_le_right _ _)))
    have hpu (x : R) (hx : x ∈ Ioo a u) : p.eval x ≠ 0 :=
      eval_ne_zero_of_sign_eq_derivSignRight hp (hu p (by simp) x hx)
    have hpl (x : R) (hx : x ∈ Ioo l b) : p.eval x ≠ 0 :=
      eval_ne_zero_of_sign_eq_derivSignLeft hp (hl p (by simp) x hx)
    have ha'u : a' ∈ Ioo a u := ⟨haa', ha'.trans_le (min_le_left _ _)⟩
    have hb'l : b' ∈ Ioo l b := ⟨(le_max_left _ _).trans_lt hb', hb'b⟩
    have hfilter : p.roots.toFinset.filter (fun r => a < r ∧ r < b) =
        p.roots.toFinset.filter (fun r => a' < r ∧ r < b') := by
      refine Finset.filter_congr fun r hr => ?_
      have hr0 : p.eval r = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
      refine ⟨fun ⟨har, hrb⟩ => ⟨lt_of_not_ge fun hra' => hpu r ⟨har, hra'.trans_lt ha'u.2⟩ hr0,
        lt_of_not_ge fun hb'r => hpl r ⟨hb'l.1.trans_le hb'r, hrb⟩ hr0⟩,
        fun ⟨ha'r, hrb'⟩ => ⟨haa'.trans ha'r, hrb'.trans hb'b⟩⟩
    rw [hfilter, ← signVariationsAt_eq_right fun q hq => hu q hq a' ha'u,
      ← signVariationsAt_eq_left fun q hq => hl q hq b' hb'l]
    exact sum_sign h hseed ((le_max_right _ _).trans_lt hb') (hpu a' ha'u) (hpl b' hb'l)

/-- **The contribution of a point.** For a signed remainder chain with head `p` and query seed
`f`, the variations drop across `a` by the sign of `f` at `a` if `a` is a root of `p`, and do
not change otherwise. -/
theorem signVariationsLeft_sub_signVariationsRight (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) (a : R) :
    (signVariationsLeft (p :: cs) a : ℤ) - signVariationsRight (p :: cs) a =
      if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0 := by
  first
  | have hp : p ≠ 0 := h.nonzero p (by simp)
    -- Compare with Sturm–Tarski on an interval around `a` containing no other root of `p`.
    obtain ⟨l, hla, hl⟩ := (p :: cs).exists_signs_left a
    obtain ⟨u, hau, hu⟩ := (p :: cs).exists_signs_right a
    obtain ⟨l', hll', hl'a⟩ := exists_between hla
    obtain ⟨u', hau', hu'u⟩ := exists_between hau
    have hpl (x : R) (hx : x ∈ Ioo l a) : p.eval x ≠ 0 :=
      eval_ne_zero_of_sign_eq_derivSignLeft hp (hl p (by simp) x hx)
    have hpu (x : R) (hx : x ∈ Ioo a u) : p.eval x ≠ 0 :=
      eval_ne_zero_of_sign_eq_derivSignRight hp (hu p (by simp) x hx)
    have hfilter : p.roots.toFinset.filter (fun r => l' < r ∧ r < u') =
        p.roots.toFinset.filter (fun r => False ∨ r = a) := by
      refine Finset.filter_congr fun r hr => ?_
      have hr0 : p.eval r = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
      refine ⟨fun ⟨hl'r, hru'⟩ => .inr ?_, ?_⟩
      · rcases lt_trichotomy r a with hra | rfl | har
        · exact absurd hr0 (hpl r ⟨hll'.trans hl'r, hra⟩)
        · rfl
        · exact absurd hr0 (hpu r ⟨har, hru'.trans hu'u⟩)
      · rintro (h | rfl)
        exacts [h.elim, ⟨hl'a, hau'⟩]
    have hs := sum_sign h hseed (hl'a.trans hau') (hpl l' ⟨hll', hl'a⟩) (hpu u' ⟨hau', hu'u⟩)
    rw [signVariationsAt_eq_left fun q hq => hl q hq l' ⟨hll', hl'a⟩,
      signVariationsAt_eq_right fun q hq => hu q hq u' ⟨hau', hu'u⟩, hfilter,
      Finset.sum_filter_or_eq_of_not _ _ _ not_false] at hs
    simpa [mem_roots hp] using hs

/-- **Sturm–Tarski on `(a, b]`.** The contribution of the closed endpoint `b` is added
explicitly to the open-interval formula. -/
theorem sum_sign_Ioc (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a ≤ b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  first
  | rcases hab.lt_or_eq with hab | rfl
    · have hIoc (r : R) : a < r ∧ r ≤ b ↔ (a < r ∧ r < b) ∨ r = b := by
        rw [← mem_Ioc, ← Ioo_insert_right hab, mem_insert_iff, mem_Ioo, or_comm]
      rw [Finset.filter_congr fun r _ => hIoc r,
        Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.2.false,
        sum_sign_Ioo h hseed hab]
      simp [mem_roots (h.nonzero p (by simp))]
    · rw [← signVariationsLeft_sub_signVariationsRight h hseed a,
        Finset.filter_false_of_mem fun r _ h => h.1.not_ge h.2]
      simp

/-- **Sturm–Tarski on `[a, b)`.** The contribution of the closed endpoint `a` is added
explicitly to the open-interval formula. -/
theorem sum_sign_Ico (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a ≤ b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r < b, (sign (f.eval r) : ℤ) := by
  first
  | rcases hab.lt_or_eq with hab | rfl
    · have hIco (r : R) : a ≤ r ∧ r < b ↔ (a < r ∧ r < b) ∨ r = a := by
        rw [← mem_Ico, ← Ioo_insert_left hab, mem_insert_iff, mem_Ioo, or_comm]
      rw [Finset.filter_congr fun r _ => hIco r,
        Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.1.false,
        sum_sign_Ioo h hseed hab]
      simp [mem_roots (h.nonzero p (by simp))]
    · rw [← signVariationsLeft_sub_signVariationsRight h hseed a,
        Finset.filter_false_of_mem fun r _ h => h.2.not_ge h.1]
      simp

/-- **Sturm–Tarski on `[a, b]`.** The contributions of both closed endpoints are added
explicitly to the open-interval formula. For `a = b` this is the contribution of a point. -/
theorem sum_sign_Icc (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a ≤ b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  first
  | have hIcc (r : R) : a ≤ r ∧ r ≤ b ↔ (a < r ∧ r ≤ b) ∨ r = a := by
      rw [← mem_Icc, ← Ioc_insert_left hab, mem_insert_iff, mem_Ioc, or_comm]
    rw [Finset.filter_congr fun r _ => hIcc r,
      Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.1.false, ← sum_sign_Ioc h hseed hab]
    simp [mem_roots (h.nonzero p (by simp))]
    ring

end Chain

section SturmSeq

variable {a b : R}

/-- One-sided Sturm–Tarski on `(a, b)` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Ioo (p f : R[X]) (hab : a < b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r < b, (sign (f.eval r) : ℤ) := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign_Ioo hsigned hseed hab

/-- One-sided Sturm–Tarski on `(a, b]` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Ioc {p : R[X]} (hp : p ≠ 0) (f : R[X]) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  first
  | have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign_Ioc hsigned hseed hab

/-- One-sided Sturm–Tarski on `[a, b)` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Ico {p : R[X]} (hp : p ≠ 0) (f : R[X]) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r < b, (sign (f.eval r) : ℤ) := by
  first
  | have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign_Ico hsigned hseed hab

/-- One-sided Sturm–Tarski on `[a, b]` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Icc {p : R[X]} (hp : p ≠ 0) (f : R[X]) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  first
  | have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign_Icc hsigned hseed hab

/-- Sturm's count of the distinct roots in `(a, b)`, with no condition on the endpoints. -/
theorem card_roots_toFinset_Ioo (p : R[X]) (hab : a < b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter fun r => a < r ∧ r < b).card := by
  first
  | simpa using sum_sign_sturmSeq_Ioo p 1 hab

/-- Sturm's count of the distinct roots in `(a, b]`. -/
theorem card_roots_toFinset_Ioc {p : R[X]} (hp : p ≠ 0) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b +
        (if p.eval b = 0 then 1 else 0) =
      (p.roots.toFinset.filter fun r => a < r ∧ r ≤ b).card := by
  first
  | simpa using sum_sign_sturmSeq_Ioc hp 1 hab

/-- Sturm's count of the distinct roots in `[a, b)`. -/
theorem card_roots_toFinset_Ico {p : R[X]} (hp : p ≠ 0) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b +
        (if p.eval a = 0 then 1 else 0) =
      (p.roots.toFinset.filter fun r => a ≤ r ∧ r < b).card := by
  first
  | simpa using sum_sign_sturmSeq_Ico hp 1 hab

/-- Sturm's count of the distinct roots in `[a, b]`. -/
theorem card_roots_toFinset_Icc {p : R[X]} (hp : p ≠ 0) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b +
        (if p.eval a = 0 then 1 else 0) + (if p.eval b = 0 then 1 else 0) =
      (p.roots.toFinset.filter fun r => a ≤ r ∧ r ≤ b).card := by
  first
  | simpa using sum_sign_sturmSeq_Icc hp 1 hab

end SturmSeq

end TauCeti.Sturm
end -- closes the original EOF section from source line 54
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/OneSided.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Eval/Infinity.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Polynomial signs at infinity over an ordered field

A coefficient bound makes the leading term dominate all lower terms.
The bound belongs to the field itself; no Archimedean assumption is used.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Beyond a field-valued coefficient bound, a polynomial has the sign
of its leading coefficient. -/
theorem exists_sign_atTop (p : R[X]) : ∃ B : R, ∀ x, B < x →
    SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  first
  | classical
    by_cases hn : p.natDegree = 0
    · refine ⟨0, fun x _ => ?_⟩
      rw [eq_C_of_natDegree_eq_zero hn]
      simp
    have hdegree : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hn
    have hp : p ≠ 0 := fun h => hn (by simp [h])
    have hlc : 0 < |p.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr hp)
    let S := ∑ i ∈ Finset.range p.natDegree, |p.coeff i|
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg (p.coeff i)
    refine ⟨1 + S / |p.leadingCoeff|, fun x hx => ?_⟩
    have hx1 : 1 < x := lt_of_le_of_lt
      (le_add_of_nonneg_right (div_nonneg hS hlc.le)) hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hdom : S < |p.leadingCoeff| * x := by
      rw [mul_comm]
      apply (div_lt_iff₀ hlc).mp
      linarith
    let t := ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i
    have ht : |t| ≤ S * x ^ (p.natDegree - 1) := by
      calc
        |t| ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i| * x ^ (p.natDegree - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_pow, abs_of_pos hx0]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hx1.le (by simpa using Nat.le_pred_of_lt (Finset.mem_range.mp hi)))
            (abs_nonneg _)
        _ = S * x ^ (p.natDegree - 1) := (Finset.sum_mul _ _ _).symm
    have hsmall : |t| < |p.leadingCoeff| * x ^ p.natDegree := by
      have h := mul_lt_mul_of_pos_right hdom (pow_pos hx0 (p.natDegree - 1))
      rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hdegree] at h
      exact ht.trans_lt h
    have heval : p.eval x = t + p.leadingCoeff * x ^ p.natDegree := by
      rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree]
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hneg | hpos
    · rw [abs_of_neg hneg] at hsmall
      rw [sign_neg hneg, heval]
      apply sign_neg
      have := le_abs_self t
      nlinarith
    · rw [abs_of_pos hpos] at hsmall
      rw [sign_pos hpos, heval]
      apply sign_pos
      have := neg_abs_le t
      nlinarith

/-- Below some field-valued bound, the sign gains the degree-parity factor. -/
theorem exists_sign_atBot (p : R[X]) : ∃ B : R, ∀ x, x < B →
    SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  first
  | obtain ⟨B, hB⟩ := exists_sign_atTop (p.comp (-X))
    refine ⟨-B, fun x hx => ?_⟩
    have hs := hB (-x) (by linarith)
    simpa only [eval_comp, eval_neg, eval_X, neg_neg,
      leadingCoeff_comp (by simp : (-X : R[X]).natDegree ≠ 0),
      leadingCoeff_neg, leadingCoeff_X] using hs

end Polynomial

namespace List

open Polynomial Filter

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A uniform right bound for the leading-coefficient signs of a polynomial list. -/
theorem exists_signs_atTop (cs : List (Polynomial R)) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, B < x → SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  first
  | have he : ∀ᶠ x in atTop, ∀ p ∈ cs,
        SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
      apply cs.finite_toSet.eventually_all.mpr
      intro p _
      obtain ⟨B, hB⟩ := exists_sign_atTop p
      exact (eventually_gt_atTop B).mono fun x hx => hB x hx
    obtain ⟨B, hB⟩ := eventually_atTop.mp he
    exact ⟨B, fun p hp x hx => hB x hx.le p hp⟩

/-- A uniform left bound for the degree-parity signs of a polynomial list. -/
theorem exists_signs_atBot (cs : List (Polynomial R)) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, x < B →
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  first
  | have he : ∀ᶠ x in atBot, ∀ p ∈ cs,
        SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
      apply cs.finite_toSet.eventually_all.mpr
      intro p _
      obtain ⟨B, hB⟩ := exists_sign_atBot p
      exact (eventually_lt_atBot B).mono fun x hx => hB x hx
    obtain ⟨B, hB⟩ := eventually_atBot.mp he
    exact ⟨B, fun p hp x hx => hB x hx.le p hp⟩

end List
end -- closes the original EOF section from source line 23
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Eval/Infinity.lean -/
