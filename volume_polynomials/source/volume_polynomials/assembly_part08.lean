module

public import volume_polynomials.assembly_part07

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

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/Infinity.lean -/
section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/


/-! # Sturm–Tarski with infinite endpoints

Leading coefficients and degree parity compute the sign variations at both
infinities. These satisfy the append, negation and zero-deletion laws of
`List.signVariations`, and are unchanged by multiplying every entry by a common
nonzero polynomial. Together with one-sided signs at finite endpoints, they give
half-line and whole-field Sturm–Tarski identities for signed remainder chains
and for `Polynomial.sturmSeq`, including root counts. Finite endpoints may be
roots of any chain entry.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial

section Semiring

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- Sign variations at positive infinity. -/
noncomputable def signVariationsAtTop (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map Polynomial.leadingCoeff)

/-- Unfold positive-infinity variations as variations of the leading coefficients. -/
theorem signVariationsAtTop_def (cs : List (Polynomial R)) :
    signVariationsAtTop cs = List.signVariations (cs.map Polynomial.leadingCoeff) := (rfl)

@[simp, grind =]
theorem signVariationsAtTop_nil : signVariationsAtTop ([] : List R[X]) = 0 := by
  first
  | simp [signVariationsAtTop_def]

@[simp, grind =]
theorem signVariationsAtTop_singleton (p : R[X]) : signVariationsAtTop [p] = 0 := by
  first
  | simp [signVariationsAtTop_def]

/-- Matching the leading-coefficient signs realizes positive-infinity variations. -/
theorem signVariationsAt_eq_atTop {cs : List (Polynomial R)} {x : R}
    (h : ∀ p ∈ cs, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff) :
    signVariationsAt cs x = signVariationsAtTop cs := by
  first
  | rw [signVariationsAt_def, signVariationsAtTop_def]
    apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left h

/-- Ordered coefficient embeddings preserve variations at positive infinity. -/
@[simp]
theorem signVariationsAtTop_map {S : Type*} [Semiring S] [LinearOrder S]
    (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) :
    signVariationsAtTop (cs.map (Polynomial.map f)) = signVariationsAtTop cs := by
  first
  | rw [signVariationsAtTop_def, signVariationsAtTop_def]
    apply List.signVariations_congr
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun p _ ↦ by
      rw [leadingCoeff_map_of_injective hf.injective]
      exact hf.sign_comp _

/-- The variations at positive infinity of a concatenation are those of the two parts, plus one
exactly when the last nonzero leading coefficient of the first part and the first nonzero leading
coefficient of the second part have opposite signs. -/
theorem signVariationsAtTop_append (cs ds : List R[X]) :
    signVariationsAtTop (cs ++ ds) =
      signVariationsAtTop cs +
        (if List.lastSign (cs.map leadingCoeff) * List.firstSign (ds.map leadingCoeff) = -1
          then 1 else 0) +
        signVariationsAtTop ds := by
  first
  | simp only [signVariationsAtTop_def, List.map_append, List.signVariations_append]

/-- The variations at positive infinity split at any nonzero entry. -/
theorem signVariationsAtTop_append_cons_of_ne_zero (cs ds : List R[X]) {p : R[X]} (hp : p ≠ 0) :
    signVariationsAtTop (cs ++ p :: ds) =
      signVariationsAtTop (cs ++ [p]) + signVariationsAtTop (p :: ds) := by
  first
  | simpa only [signVariationsAtTop_def, List.map_append, List.map_cons, List.map_nil] using
      List.signVariations_append_cons_of_ne_zero _ _ (leadingCoeff_ne_zero.2 hp)

/-- Deleting the zero entries does not change the variations at positive infinity. -/
@[simp]
theorem signVariationsAtTop_filter_ne_zero (cs : List R[X]) :
    signVariationsAtTop (cs.filter fun p ↦ !decide (p = 0)) = signVariationsAtTop cs := by
  first
  | rw [signVariationsAtTop_def, signVariationsAtTop_def,
      ← List.signVariations_filter_ne_zero (cs.map _), List.filter_map]
    simp [Function.comp_def]

end Semiring

section Ring

variable {R : Type*} [Ring R] [LinearOrder R]

/-- Sign variations at negative infinity. -/
noncomputable def signVariationsAtBot (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree))

/-- Unfold negative-infinity variations using leading coefficients and degree parity. -/
theorem signVariationsAtBot_def (cs : List (Polynomial R)) :
    signVariationsAtBot cs =
      List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree)) := (rfl)

@[simp, grind =]
theorem signVariationsAtBot_nil : signVariationsAtBot ([] : List R[X]) = 0 := by
  first
  | simp [signVariationsAtBot_def]

@[simp, grind =]
theorem signVariationsAtBot_singleton (p : R[X]) : signVariationsAtBot [p] = 0 := by
  first
  | simp [signVariationsAtBot_def]

/-- Matching the parity-adjusted leading signs realizes negative-infinity variations. -/
theorem signVariationsAt_eq_atBot {cs : List (Polynomial R)} {x : R}
    (h : ∀ p ∈ cs,
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree)) :
    signVariationsAt cs x = signVariationsAtBot cs := by
  first
  | rw [signVariationsAt_def, signVariationsAtBot_def]
    apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left h

/-- Ordered coefficient embeddings preserve variations at negative infinity. -/
@[simp]
theorem signVariationsAtBot_map {S : Type*} [Ring S] [LinearOrder S]
    (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) :
    signVariationsAtBot (cs.map (Polynomial.map f)) = signVariationsAtBot cs := by
  first
  | rw [signVariationsAtBot_def, signVariationsAtBot_def]
    apply List.signVariations_congr
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun p _ ↦ by
      rw [leadingCoeff_map_of_injective hf.injective, natDegree_map_eq_of_injective hf.injective]
      simpa only [map_mul, map_pow, map_neg, map_one] using
        hf.sign_comp (p.leadingCoeff * (-1) ^ p.natDegree)

/-- The variations at negative infinity of a concatenation are those of the two parts, plus one
exactly when the last nonzero parity-adjusted leading coefficient of the first part and the first
nonzero one of the second part have opposite signs. -/
theorem signVariationsAtBot_append (cs ds : List R[X]) :
    signVariationsAtBot (cs ++ ds) =
      signVariationsAtBot cs +
        (if List.lastSign (cs.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree) *
            List.firstSign (ds.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree) = -1
          then 1 else 0) +
        signVariationsAtBot ds := by
  first
  | simp only [signVariationsAtBot_def, List.map_append, List.signVariations_append]

/-- The variations at negative infinity split at any nonzero entry. -/
theorem signVariationsAtBot_append_cons_of_ne_zero (cs ds : List R[X]) {p : R[X]} (hp : p ≠ 0) :
    signVariationsAtBot (cs ++ p :: ds) =
      signVariationsAtBot (cs ++ [p]) + signVariationsAtBot (p :: ds) := by
  first
  | simpa only [signVariationsAtBot_def, List.map_append, List.map_cons, List.map_nil] using
      List.signVariations_append_cons_of_ne_zero _ _
        ((isUnit_neg_one.pow _).mul_left_eq_zero.not.2 (leadingCoeff_ne_zero.2 hp))

/-- Deleting the zero entries does not change the variations at negative infinity. -/
@[simp]
theorem signVariationsAtBot_filter_ne_zero (cs : List R[X]) :
    signVariationsAtBot (cs.filter fun p ↦ !decide (p = 0)) = signVariationsAtBot cs := by
  first
  | rw [signVariationsAtBot_def, signVariationsAtBot_def,
      ← List.signVariations_filter_ne_zero (cs.map _), List.filter_map]
    simp [Function.comp_def, (isUnit_neg_one.pow _).mul_left_eq_zero]

/-- Negating every entry does not change the variations at positive infinity. -/
@[simp]
theorem signVariationsAtTop_map_neg [AddLeftStrictMono R] (cs : List R[X]) :
    signVariationsAtTop (cs.map Neg.neg) = signVariationsAtTop cs := by
  first
  | simpa only [signVariationsAtTop_def, List.map_map, Function.comp_def, leadingCoeff_neg] using
      List.signVariations_map_of_sign_eq_neg Left.sign_neg (cs.map leadingCoeff)

/-- Negating every entry does not change the variations at negative infinity. -/
@[simp]
theorem signVariationsAtBot_map_neg [AddLeftStrictMono R] (cs : List R[X]) :
    signVariationsAtBot (cs.map Neg.neg) = signVariationsAtBot cs := by
  first
  | simpa only [signVariationsAtBot_def, List.map_map, Function.comp_def, leadingCoeff_neg,
      natDegree_neg, neg_mul] using
      List.signVariations_map_of_sign_eq_neg Left.sign_neg
        (cs.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree)

variable [IsStrictOrderedRing R]

/-- Multiplying every entry by a common nonzero polynomial does not change the variations at
positive infinity. -/
theorem signVariationsAtTop_map_mul (cs : List R[X]) {d : R[X]} (hd : d ≠ 0) :
    signVariationsAtTop (cs.map (d * ·)) = signVariationsAtTop cs := by
  first
  | simpa only [signVariationsAtTop_def, List.map_map, Function.comp_def, leadingCoeff_mul] using
      List.signVariations_map_mul_left (cs.map leadingCoeff) (leadingCoeff_ne_zero.2 hd)

/-- Multiplying every entry by a common nonzero polynomial does not change the variations at
negative infinity. -/
theorem signVariationsAtBot_map_mul (cs : List R[X]) {d : R[X]} (hd : d ≠ 0) :
    signVariationsAtBot (cs.map (d * ·)) = signVariationsAtBot cs := by
  first
  | have h (p : R[X]) : (d * p).leadingCoeff * (-1) ^ (d * p).natDegree =
        d.leadingCoeff * (-1) ^ d.natDegree * (p.leadingCoeff * (-1) ^ p.natDegree) := by
      rcases eq_or_ne p 0 with rfl | hp
      · simp
      rw [leadingCoeff_mul, natDegree_mul hd hp, pow_add]
      rcases neg_one_pow_eq_or R d.natDegree with h | h <;> simp [h, mul_assoc]
    simpa only [signVariationsAtBot_def, List.map_map, Function.comp_def, h] using
      List.signVariations_map_mul_left (cs.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree)
        ((isUnit_neg_one.pow _).mul_left_eq_zero.not.2 (leadingCoeff_ne_zero.2 hd))

end Ring

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying both inputs by a common nonzero polynomial does not change the variations at
positive infinity of their signed remainder sequence. -/
@[simp]
theorem signVariationsAtTop_sturmSeq_mul_left {r : R[X]} (hr : r ≠ 0) (p q : R[X]) :
    signVariationsAtTop (sturmSeq (r * p) (r * q)) = signVariationsAtTop (sturmSeq p q) := by
  first
  | rw [sturmSeq_mul_left hr, signVariationsAtTop_map_mul _ hr]

/-- Multiplying both inputs by a common nonzero polynomial does not change the variations at
negative infinity of their signed remainder sequence. -/
@[simp]
theorem signVariationsAtBot_sturmSeq_mul_left {r : R[X]} (hr : r ≠ 0) (p q : R[X]) :
    signVariationsAtBot (sturmSeq (r * p) (r * q)) = signVariationsAtBot (sturmSeq p q) := by
  first
  | rw [sturmSeq_mul_left hr, signVariationsAtBot_map_mul _ hr]

/-- The variation count stabilizes at positive infinity, even for lists containing zero. -/
theorem exists_signVariationsAtTop (cs : List (Polynomial R)) :
    ∃ B : R, ∀ x, B < x → signVariationsAt cs x = signVariationsAtTop cs := by
  first
  | obtain ⟨B, hB⟩ := List.exists_signs_atTop cs
    exact ⟨B, fun x hx => signVariationsAt_eq_atTop (fun p hp => hB p hp x hx)⟩

/-- The variation count stabilizes at negative infinity, even for lists containing zero. -/
theorem exists_signVariationsAtBot (cs : List (Polynomial R)) :
    ∃ B : R, ∀ x, x < B → signVariationsAt cs x = signVariationsAtBot cs := by
  first
  | obtain ⟨B, hB⟩ := List.exists_signs_atBot cs
    exact ⟨B, fun x hx => signVariationsAt_eq_atBot (fun p hp => hB p hp x hx)⟩

/-- Far enough to the right, finite evaluation realizes the infinity signs and
lies beyond every chain root. The bound belongs to the ordered field itself. -/
theorem exists_atTop (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, (∀ x, B < x → signVariationsAt cs x = signVariationsAtTop cs) ∧
      ∀ p ∈ cs, ∀ r, p.eval r = 0 → r ≤ B := by
  first
  | obtain ⟨B, hB⟩ := List.exists_signs_atTop cs
    refine ⟨B, ?_, ?_⟩
    · exact fun x hx => signVariationsAt_eq_atTop (fun p hp => hB p hp x hx)
    · intro p hp r hr
      by_contra! hBr
      have hs := hB p hp r hBr
      rw [hr, sign_zero] at hs
      exact leadingCoeff_ne_zero.mpr (hne p hp) (sign_eq_zero_iff.mp hs.symm)

/-- Far enough to the left, finite evaluation realizes the negative-infinity
variations, and every chain root lies above the bound. -/
theorem exists_atBot (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, (∀ x, x < B → signVariationsAt cs x = signVariationsAtBot cs) ∧
      ∀ p ∈ cs, ∀ r, p.eval r = 0 → B ≤ r := by
  first
  | obtain ⟨B, hB⟩ := List.exists_signs_atBot cs
    refine ⟨B, ?_, ?_⟩
    · exact fun x hx => signVariationsAt_eq_atBot (fun p hp => hB p hp x hx)
    · intro p hp r hr
      by_contra! hrB
      have hs := hB p hp r hrB
      rw [hr, sign_zero] at hs
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr (hne p hp))
        (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (sign_eq_zero_iff.mp hs.symm)

variable [IsRealClosed R]

/-- Sturm–Tarski on `(a, ∞)`, using right-hand variations at any finite endpoint. -/
theorem sum_sign_Ioi {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    (a : R) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsAtTop (p :: cs) =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    obtain ⟨B, hB, hR⟩ := exists_atTop _ h.nonzero
    let b := max a B + 1
    have hab : a < b := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
    have hBb : B < b := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
    have hroots : ∀ r ∈ p.roots.toFinset, r < b := fun r hr =>
      (hR p (by simp) r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))).trans_lt hBb
    have hf : p.roots.toFinset.filter (fun r => a < r ∧ r < b) = p.roots.toFinset.filter (a < ·) := by
      apply Finset.filter_congr
      intro r hr
      simp [hroots r hr]
    have hne : ∀ q ∈ p :: cs, q.eval b ≠ 0 :=
      fun q hq hz => (hR q hq b hz).not_gt hBb
    have ht := sum_sign_Ioo h hseed hab
    rwa [signVariationsLeft_eq_signVariationsAt hne, hB b hBb, hf] at ht

/-- Sturm–Tarski on `(-∞, b)`, using left-hand variations at any finite endpoint. -/
theorem sum_sign_Iio {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    (b : R) :
    (signVariationsAtBot (p :: cs) : ℤ) - signVariationsLeft (p :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    obtain ⟨B, hB, hR⟩ := exists_atBot _ h.nonzero
    let a := min b B - 1
    have hab : a < b := lt_of_lt_of_le (sub_one_lt _) (min_le_left _ _)
    have haB : a < B := lt_of_lt_of_le (sub_one_lt _) (min_le_right _ _)
    have hroots : ∀ r ∈ p.roots.toFinset, a < r := fun r hr =>
      haB.trans_le (hR p (by simp) r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)))
    have hf : p.roots.toFinset.filter (fun r => a < r ∧ r < b) = p.roots.toFinset.filter (· < b) := by
      apply Finset.filter_congr
      intro r hr
      simp [hroots r hr]
    have hne : ∀ q ∈ p :: cs, q.eval a ≠ 0 :=
      fun q hq hz => (hR q hq a hz).not_gt haB
    have ht := sum_sign_Ioo h hseed hab
    rwa [signVariationsRight_eq_signVariationsAt hne, hB a haB, hf] at ht

/-- Sturm–Tarski on the whole real closed field. -/
theorem sum_sign_univ {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0)) :
    (signVariationsAtBot (p :: cs) : ℤ) - signVariationsAtTop (p :: cs) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    obtain ⟨B, hB, hR⟩ := exists_atBot _ h.nonzero
    let a := B - 1
    have haB : a < B := sub_one_lt _
    have hroots : ∀ r ∈ p.roots.toFinset, a < r := fun r hr =>
      haB.trans_le (hR p (by simp) r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)))
    have hf : p.roots.toFinset.filter (a < ·) = p.roots.toFinset := Finset.filter_true_of_mem hroots
    have hne : ∀ q ∈ p :: cs, q.eval a ≠ 0 :=
      fun q hq hz => (hR q hq a hz).not_gt haB
    have ht := sum_sign_Ioi h hseed a
    rwa [signVariationsRight_eq_signVariationsAt hne, hB a haB, hf] at ht


/-- Sturm–Tarski for Mathlib's sequence on `(a, ∞)`, even when `a` is a root. -/
theorem sum_sign_sturmSeq_Ioi {p : R[X]} (hp : p ≠ 0) (f : R[X]) (a : R) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign_Ioi hsigned hseed a

/-- Sturm–Tarski for Mathlib's sequence on `(-∞, b)`, even when `b` is a root. -/
theorem sum_sign_sturmSeq_Iio {p : R[X]} (hp : p ≠ 0) (f : R[X]) (b : R) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign_Iio hsigned hseed b

/-- Sturm–Tarski for Mathlib's signed remainder sequence on the whole real closed field. -/
theorem sum_sign_sturmSeq_univ (p f : R[X]) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  first
  | classical
    by_cases hp : p = 0
    · simp [hp]
    have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
    have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
    rw [sturmSeq_cons hp] at hsigned hseed ⊢
    exact sum_sign_univ hsigned hseed

/-- Sturm counting of distinct roots in `(a, ∞)`, with no restriction on the endpoint. -/
theorem card_roots_toFinset_Ioi {p : R[X]} (hp : p ≠ 0) (a : R) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      (p.roots.toFinset.filter (a < ·)).card := by
  first
  | classical
    simpa using sum_sign_sturmSeq_Ioi hp 1 a

/-- Sturm counting of distinct roots in `(-∞, b)`, with no restriction on the endpoint. -/
theorem card_roots_toFinset_Iio {p : R[X]} (hp : p ≠ 0) (b : R) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter (· < b)).card := by
  first
  | classical
    simpa using sum_sign_sturmSeq_Iio hp 1 b

/-- Classical Sturm counting of all distinct roots of a nonzero polynomial. For `p = 0` both
sides are zero: `sturmSeq 0 _ = []` and `Polynomial.roots 0 = 0` by convention. -/
theorem card_roots_toFinset_univ (p : R[X]) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      p.roots.toFinset.card := by
  first
  | simpa using sum_sign_sturmSeq_univ p 1

end TauCeti.Sturm
end -- closes the original EOF section from source line 22
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/Infinity.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/Variation.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Variations of a Sturm sequence at a point

The variation of a signed Euclidean remainder sequence is the number used in
Sturm's root-counting formula. Mathlib's `Polynomial.sturmSeq` supplies the
sequence and `TauCeti.Sturm.signVariationsAt` counts its evaluated sign changes.
At a zero of the nonzero second polynomial where the first is nonzero, the first and third
values are opposite, so deleting the zero reveals exactly one sign change. This file
records that local calculation alongside the sequence recurrence. The existing
empty-list and singleton variation lemmas supply the zero cases. The calculation works over
any ordered field; it does not require real closedness.
Negating both inputs or multiplying them by a polynomial nonzero at the
evaluation point leaves the variation unchanged, while a common root makes it zero.
The evaluated variation uses the existing `TauCeti.Sturm.signVariationsAt` API
on `Polynomial.sturmSeq p q`.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial

variable {K : Type*} [Field K] [LinearOrder K]

/-- Evaluation of the first entry gives the recursion for Sturm variations. -/
private theorem signVariationsAt_sturmSeq_cons {p : K[X]} (hp : p ≠ 0) (q : K[X]) (x : K) :
    signVariationsAt (sturmSeq p q) x =
      (p.eval x :: (sturmSeq q (-p % q)).map (fun r => r.eval x)).signVariations := by
  first
  | simp only [signVariationsAt_def, sturmSeq_cons hp, List.map_cons]

/-- A zero first value is deleted when counting Sturm variations. -/
theorem signVariationsAt_sturmSeq_eq_of_eval_eq_zero {p q : K[X]} {x : K}
    (hp : p.eval x = 0) :
    signVariationsAt (sturmSeq p q) x = signVariationsAt (sturmSeq q (-p % q)) x := by
  first
  | by_cases hp0 : p = 0
    · simp only [hp0, neg_zero, EuclideanDomain.zero_mod, sturmSeq_zero_left, sturmSeq_zero_right]
      split_ifs <;> simp only [signVariationsAt_nil, signVariationsAt_singleton]
    · rw [signVariationsAt_sturmSeq_cons hp0]
      simp only [hp, List.signVariations_zero_cons, signVariationsAt_def]

/-- When the first two evaluations are nonzero, a Sturm variation step adds
one exactly when their signs differ. -/
theorem signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero {p q : K[X]} {x : K}
    (hp : p.eval x ≠ 0) (hq : q.eval x ≠ 0) :
    signVariationsAt (sturmSeq p q) x = signVariationsAt (sturmSeq q (-p % q)) x +
      (if SignType.sign (p.eval x) = SignType.sign (q.eval x) then 0 else 1) := by
  first
  | have hp0 : p ≠ 0 := by rintro rfl; simp at hp
    have hq0 : q ≠ 0 := by rintro rfl; simp at hq
    rw [signVariationsAt_sturmSeq_cons hp0, signVariationsAt_sturmSeq_cons hq0, sturmSeq_cons hq0,
      List.map_cons, List.signVariations_cons_cons_of_ne_zero _ hp hq]

/-- At a zero of the nonzero second polynomial that is not a zero of the first,
the first Sturm variation step contributes exactly one sign change. -/
theorem signVariationsAt_sturmSeq_eq_add_one_of_eval_ne_zero_of_eval_eq_zero
    [AddLeftStrictMono K] {p q : K[X]} {x : K}
    (hp : p.eval x ≠ 0) (hq0 : q ≠ 0) (hq : q.eval x = 0) :
    signVariationsAt (sturmSeq p q) x = signVariationsAt (sturmSeq q (-p % q)) x + 1 := by
  first
  | have hp0 : p ≠ 0 := by rintro rfl; simp at hp
    rw [signVariationsAt_sturmSeq_cons hp0, signVariationsAt_sturmSeq_cons hq0,
      sturmSeq_cons hq0]
    have hr : (-p % q).eval x = -p.eval x := by
      rw [mod_def, ← eval_neg]
      exact eval₂_modByMonic_eq_self_of_root (by simp [hq])
    have hr0 : -p % q ≠ 0 := by
      intro hz
      apply neg_ne_zero.mpr hp
      rw [← hr, hz, eval_zero]
    rw [sturmSeq_cons hr0]
    simp only [List.map_cons, hq, hr]
    rw [List.signVariations_cons_zero_cons, List.signVariations_zero_cons,
      List.signVariations_cons_cons_of_ne_zero _ hp (neg_ne_zero.mpr hp)]
    have hs : SignType.sign (p.eval x) ≠ SignType.sign (-p.eval x) := by
      rw [Left.sign_neg]
      exact mt SignType.self_eq_neg_iff.mp (sign_ne_zero.mpr hp)
    simp only [hs, ite_false]

/-- Multiplying both inputs by a common polynomial does not alter their
Sturm variation away from its roots. -/
@[simp] theorem signVariationsAt_sturmSeq_mul_left [IsStrictOrderedRing K]
    {r : K[X]} (p q : K[X]) {x : K}
    (hrx : r.eval x ≠ 0) :
    signVariationsAt (sturmSeq (r * p) (r * q)) x = signVariationsAt (sturmSeq p q) x := by
  first
  | have hr : r ≠ 0 := by rintro rfl; simp at hrx
    rw [sturmSeq_mul_left hr]
    exact signVariationsAt_map_mul (sturmSeq p q) hrx

/-- Negating both inputs preserves their Sturm variation. -/
@[simp] theorem signVariationsAt_sturmSeq_neg_neg [AddLeftStrictMono K]
    (p q : K[X]) (x : K) :
    signVariationsAt (sturmSeq (-p) (-q)) x = signVariationsAt (sturmSeq p q) x := by
  first
  | have hseq := sturmSeq_mul_left (r := -(1 : K[X])) (by simp) p q
    simp only [neg_one_mul] at hseq
    rw [hseq, signVariationsAt_map_neg]

/-- A common root of the two input polynomials annihilates every entry of
their Sturm sequence, so its variation at that point is zero. -/
@[simp] theorem signVariationsAt_sturmSeq_eq_zero_of_eval_eq_zero_of_eval_eq_zero
    {p q : K[X]} {x : K}
    (hp : p.eval x = 0) (hq : q.eval x = 0) : signVariationsAt (sturmSeq p q) x = 0 := by
  first
  | have hpd : X - C x ∣ p := dvd_iff_isRoot.mpr hp
    have hqd : X - C x ∣ q := dvd_iff_isRoot.mpr hq
    have hz (s : K[X]) (hs : s ∈ sturmSeq p q) : s.eval x = 0 :=
      (dvd_iff_isRoot.mp (dvd_of_mem_sturmSeq hpd hqd hs))
    rw [← signVariationsAt_filter_eval_ne_zero, List.filter_eq_nil_iff.mpr, signVariationsAt_nil]
    simpa using hz

end TauCeti.Sturm
end -- closes the original EOF section from source line 28
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/Variation.lean -/

/- BEGIN SOURCE: TauCeti/Data/SignType/Parity.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sign changes twisted by powers of `-1`

Sturm-type counts compare the signs of consecutive entries at `+∞` and at `-∞`. At `-∞` a
leading sign `s` of a degree-`m` polynomial becomes `s * (-1) ^ m`. For nonzero signs `s` and
`t`, the sign-change indicator of the twisted pair minus that of the original pair is `s * t`
when `m + n` is odd and `0` otherwise.

## Main results

* `SignType.ite_mul_neg_one_pow_sub_ite`: the difference of the two sign-change indicators.
-/

public section

namespace TauCeti

/-- Comparing the nonzero signs `s * (-1) ^ m` and `t * (-1) ^ n` instead of `s` and `t`
changes the sign-change indicator by `s * t` exactly when `m + n` is odd. -/
theorem _root_.SignType.ite_mul_neg_one_pow_sub_ite (m n : ℕ) {s t : SignType} (hs : s ≠ 0)
    (ht : t ≠ 0) :
    ((if s * (-1) ^ m = t * (-1) ^ n then 0 else 1 : ℕ) : ℤ) -
        ((if s = t then 0 else 1 : ℕ) : ℤ) =
      if Odd (m + n) then (s : ℤ) * t else 0 := by
  first
  | rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn <;>
      simp only [hm.neg_one_pow, hn.neg_one_pow, Nat.odd_add, hm, hn, mul_one, mul_neg] <;>
      cases s <;> cases t <;> simp_all [Nat.not_odd_iff_even.mpr, Nat.not_even_iff_odd.mpr]

end TauCeti
end -- closes the original EOF section from source line 24
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/SignType/Parity.lean -/

/- BEGIN SOURCE: TauCeti/Algebra/Polynomial/Sturm/CauchyIndex/Sequence.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Computing Cauchy indices by Sturm sequences

The Cauchy index of an arbitrary quotient `q / p` is the difference of the
sign variations of `Polynomial.sturmSeq p q` at the two endpoints. On the
whole line these variations depend only on leading coefficients and degree
parities. The numerator need not be a multiple of the derivative of the
denominator, and common factors and multiple roots are allowed.

Write `V(a⁻)` and `V(a⁺)` for the left-hand and right-hand variations of the
Sturm sequence at `a`, and `V(-∞)`, `V(+∞)` for its variations at infinity.
The jump of `q / p` at `a` is the local contribution `V(a⁻) - V(a⁺)`
(`Polynomial.cauchyJump_eq_sub_signVariations`). So every interval is handled
by one rule, whether or not its endpoints are roots of `p` or `q`: an included
endpoint contributes the variations just outside the interval, and an excluded
endpoint the variations just inside it. For instance the index on `(a, b)` is
`V(a⁺) - V(b⁻)`, on `[a, b]` it is `V(a⁻) - V(b⁺)`, and on `(a, ∞)` it is
`V(a⁺) - V(+∞)`.

This connects signed Euclidean remainder sequences to Cauchy indices, so
coefficient formulas for the sequences can compute indices and Tarski queries.
In particular, one Euclidean step changes the whole-line index of `q / p` only
by the contribution of the leading coefficients of `p` and `q`
(`Polynomial.cauchyIndex_univ_eq_add_cauchyIndex_neg_mod`), and the Tarski query
`TaQ(q, p)` is the drop in variations at infinity of the Sturm sequence of `p` and
`p' * q` (`Polynomial.tarskiQuery_eq_signVariationsAtBot_sub_signVariationsAtTop`).

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (the Cauchy index and signed remainder sequences).
The sequence used here is Mathlib's `Polynomial.sturmSeq`, by Tomaz Mascarenhas,
Pedro Saccomani, and Sarah Pereira.
-/

public section

namespace TauCeti

open _root_.Polynomial Set SignType Sturm

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The Cauchy index of `q / p` between endpoints where every entry of its
Sturm sequence is nonzero is the drop in evaluated sign variations. -/
private theorem cauchyIndex_Ioo_aux (p q : R[X]) {a b : R} (hab : a < b)
    (ha : ∀ r ∈ sturmSeq p q, r.eval a ≠ 0)
    (hb : ∀ r ∈ sturmSeq p q, r.eval b ≠ 0) :
    cauchyIndex p q (Ioo a b) =
      (signVariationsAt (sturmSeq p q) a : ℤ) - signVariationsAt (sturmSeq p q) b := by
  first
  | classical
    induction p, q using sturmSeq.induct with
    | case1 q => simp
    | case2 p q hp ih =>
      by_cases hq : q = 0
      · simp [hq, hp]
      have hat : ∀ r ∈ sturmSeq q (-p % q), r.eval a ≠ 0 := by
        intro r hr
        exact ha r (by rw [sturmSeq_cons hp]; simp [hr])
      have hbt : ∀ r ∈ sturmSeq q (-p % q), r.eval b ≠ 0 := by
        intro r hr
        exact hb r (by rw [sturmSeq_cons hp]; simp [hr])
      have hpa := ha p (mem_sturmSeq_self hp)
      have hpb := hb p (mem_sturmSeq_self hp)
      have hqa := hat q (mem_sturmSeq_self hq)
      have hqb := hbt q (mem_sturmSeq_self hq)
      have hrec := two_mul_cauchyIndex_Ioo p q hab
      rw [derivSignLeft_eq_sign_eval _ (by simpa using mul_ne_zero hpb hqb),
        derivSignRight_eq_sign_eval _ (by simpa using mul_ne_zero hpa hqa)] at hrec
      have ht := ih hat hbt
      rw [neg_mod, cauchyIndex_neg_right] at ht
      rw [signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero hpa hqa,
        signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero hpb hqb]
      have hs :
          2 * ((if sign (p.eval a) = sign (q.eval a) then 0 else 1 : ℤ) -
            (if sign (p.eval b) = sign (q.eval b) then 0 else 1 : ℤ)) =
          (sign ((p * q).eval b) : ℤ) - sign ((p * q).eval a) := by
        simp only [eval_mul, sign_mul, SignType.coe_mul]
        have step (s t : SignType) (hs : s ≠ 0) (ht : t ≠ 0) :
            2 * (if s = t then 0 else 1 : ℤ) = 1 - (s : ℤ) * t := by
          cases s <;> cases t <;> simp_all
        rw [mul_sub, step _ _ (sign_ne_zero.mpr hpa) (sign_ne_zero.mpr hqa),
          step _ _ (sign_ne_zero.mpr hpb) (sign_ne_zero.mpr hqb)]
        ring
      simp only [neg_mod]
      push_cast
      linarith only [hrec, ht, hs]

/-- On an arbitrary open interval, the Cauchy index is the right-hand variation
at the left endpoint minus the left-hand variation at the right endpoint.
Either endpoint may be a pole or a common root. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Ioo (p q : R[X]) {a b : R}
    (hab : a < b) :
    cauchyIndex p q (Ioo a b) =
      (signVariationsRight (sturmSeq p q) a : ℤ) - signVariationsLeft (sturmSeq p q) b := by
  first
  | classical
    by_cases hp : p = 0
    · simp [hp]
    let cs := sturmSeq p q
    have hnonzero : ∀ r ∈ cs, r ≠ 0 := fun _ hr => ne_zero_of_mem_sturmSeq hr
    obtain ⟨u, hau, hu⟩ := cs.exists_signs_right a
    obtain ⟨l, hlb, hl⟩ := cs.exists_signs_left b
    obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hau hab)
    obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hlb (ha'.trans_le (min_le_right _ _)))
    have ha'u : a' ∈ Ioo a u := ⟨haa', ha'.trans_le (min_le_left _ _)⟩
    have hb'l : b' ∈ Ioo l b := ⟨(le_max_left _ _).trans_lt hb', hb'b⟩
    have hpu (x : R) (hx : x ∈ Ioo a u) : p.eval x ≠ 0 :=
      eval_ne_zero_of_sign_eq_derivSignRight hp (hu p (mem_sturmSeq_self hp) x hx)
    have hpl (x : R) (hx : x ∈ Ioo l b) : p.eval x ≠ 0 :=
      eval_ne_zero_of_sign_eq_derivSignLeft hp (hl p (mem_sturmSeq_self hp) x hx)
    have hindex : cauchyIndex p q (Ioo a b) = cauchyIndex p q (Ioo a' b') := by
      rw [cauchyIndex_eq_sum, cauchyIndex_eq_sum]
      symm
      apply Finset.sum_subset
      · intro r hr
        simp only [Finset.mem_filter, mem_Ioo] at hr ⊢
        exact ⟨hr.1, haa'.trans hr.2.1, hr.2.2.trans hb'b⟩
      · intro r hr hr'
        have hrab := (Finset.mem_filter.mp hr).2
        have hrout : ¬ (a' < r ∧ r < b') := by
          simpa only [Finset.mem_filter, (Finset.mem_filter.mp hr).1, mem_Ioo, true_and] using hr'
        apply cauchyJump_of_eval_ne_zero
        rcases le_or_gt r a' with hra' | ha'r
        · exact hpu r ⟨hrab.1, hra'.trans_lt ha'u.2⟩
        · exact hpl r ⟨hb'l.1.trans_le (not_lt.mp fun hrb' => hrout ⟨ha'r, hrb'⟩), hrab.2⟩
    rw [hindex, cauchyIndex_Ioo_aux p q ((le_max_right _ _).trans_lt hb')
      (fun r hr => eval_ne_zero_of_sign_eq_derivSignRight (hnonzero r hr) (hu r hr a' ha'u))
      (fun r hr => eval_ne_zero_of_sign_eq_derivSignLeft (hnonzero r hr) (hl r hr b' hb'l)),
      signVariationsAt_eq_right (fun r hr => hu r hr a' ha'u),
      signVariationsAt_eq_left (fun r hr => hl r hr b' hb'l)]

/-- **The jump as a local contribution.** The jump of `q / p` at `a` is the drop in the
one-sided variations of its Sturm sequence across `a`. This holds at every point, including
common roots of `p` and `q` and points that are not roots of `p`. -/
theorem _root_.Polynomial.cauchyJump_eq_sub_signVariations (p q : R[X]) (a : R) :
    cauchyJump p q a =
      (signVariationsLeft (sturmSeq p q) a : ℤ) - signVariationsRight (sturmSeq p q) a := by
  first
  | have h := cauchyIndex_Ioo_eq_add (p := p) (q := q) (sub_one_lt a) (lt_add_one a)
    rw [cauchyIndex_eq_sub_signVariations_Ioo _ _ ((sub_one_lt a).trans (lt_add_one a)),
      cauchyIndex_eq_sub_signVariations_Ioo _ _ (sub_one_lt a),
      cauchyIndex_eq_sub_signVariations_Ioo _ _ (lt_add_one a)] at h
    linarith only [h]

/-- On `(a, b]` the Cauchy index is the drop in right-hand variations from `a` to `b`. The
closed endpoint uses the variations on the far side of `b`. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Ioc (p q : R[X]) {a b : R}
    (hab : a ≤ b) :
    cauchyIndex p q (Ioc a b) =
      (signVariationsRight (sturmSeq p q) a : ℤ) - signVariationsRight (sturmSeq p q) b := by
  first
  | rcases hab.lt_or_eq with hab | rfl
    · rw [← Ioo_insert_right hab, cauchyIndex_insert _ _ (by simp),
        cauchyIndex_eq_sub_signVariations_Ioo _ _ hab, cauchyJump_eq_sub_signVariations]
      ring
    · simp

/-- On `[a, b]` the Cauchy index is the left-hand variations at `a` minus the right-hand
variations at `b`. For `a = b` this is the jump at `a`. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Icc (p q : R[X]) {a b : R}
    (hab : a ≤ b) :
    cauchyIndex p q (Icc a b) =
      (signVariationsLeft (sturmSeq p q) a : ℤ) - signVariationsRight (sturmSeq p q) b := by
  first
  | rw [← Ioc_insert_left hab, cauchyIndex_insert _ _ (by simp),
      cauchyIndex_eq_sub_signVariations_Ioc _ _ hab, cauchyJump_eq_sub_signVariations]
    ring

/-- On `[a, b)` the Cauchy index is the drop in left-hand variations from `a` to `b`. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Ico (p q : R[X]) {a b : R}
    (hab : a ≤ b) :
    cauchyIndex p q (Ico a b) =
      (signVariationsLeft (sturmSeq p q) a : ℤ) - signVariationsLeft (sturmSeq p q) b := by
  first
  | have h := cauchyIndex_eq_sub_signVariations_Icc p q hab
    rw [← Ico_insert_right hab, cauchyIndex_insert _ _ (by simp),
      cauchyJump_eq_sub_signVariations] at h
    linarith only [h]

/-- On `(a, ∞)` the Cauchy index is the right-hand variations at `a` minus the variations
at `+∞`. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Ioi (p q : R[X]) (a : R) :
    cauchyIndex p q (Ioi a) =
      (signVariationsRight (sturmSeq p q) a : ℤ) - signVariationsAtTop (sturmSeq p q) := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    obtain ⟨B, hB, hR⟩ := exists_atTop (sturmSeq p q) (fun _ hr => ne_zero_of_mem_sturmSeq hr)
    set b := max a B + 1
    have hab : a < b := (le_max_left _ _).trans_lt (lt_add_one _)
    have hBb : B < b := (le_max_right _ _).trans_lt (lt_add_one _)
    -- Every root of `p` lies below `b`, so only `(a, b)` contributes.
    have hindex : cauchyIndex p q (Ioi a) = cauchyIndex p q (Ioo a b) :=
      cauchyIndex_congr_of_isRoot q fun r hr =>
        ⟨fun h => ⟨h, (hR p (mem_sturmSeq_self hp) r hr).trans_lt hBb⟩, And.left⟩
    rw [hindex, cauchyIndex_eq_sub_signVariations_Ioo p q hab,
      signVariationsLeft_eq_signVariationsAt fun r hr hz => (hR r hr b hz).not_gt hBb, hB b hBb]

/-- On `[a, ∞)` the Cauchy index is the left-hand variations at `a` minus the variations
at `+∞`. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Ici (p q : R[X]) (a : R) :
    cauchyIndex p q (Ici a) =
      (signVariationsLeft (sturmSeq p q) a : ℤ) - signVariationsAtTop (sturmSeq p q) := by
  first
  | rw [← Ioi_insert, cauchyIndex_insert _ _ (by simp), cauchyIndex_eq_sub_signVariations_Ioi,
      cauchyJump_eq_sub_signVariations]
    ring

/-- On `(-∞, b)` the Cauchy index is the variations at `-∞` minus the left-hand variations
at `b`. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Iio (p q : R[X]) (b : R) :
    cauchyIndex p q (Iio b) =
      (signVariationsAtBot (sturmSeq p q) : ℤ) - signVariationsLeft (sturmSeq p q) b := by
  first
  | by_cases hp : p = 0
    · simp [hp]
    obtain ⟨A, hA, hR⟩ := exists_atBot (sturmSeq p q) (fun _ hr => ne_zero_of_mem_sturmSeq hr)
    set a := min A b - 1
    have hab : a < b := (sub_one_lt _).trans_le (min_le_right _ _)
    have haA : a < A := (sub_one_lt _).trans_le (min_le_left _ _)
    -- Every root of `p` lies above `a`, so only `(a, b)` contributes.
    have hindex : cauchyIndex p q (Iio b) = cauchyIndex p q (Ioo a b) :=
      cauchyIndex_congr_of_isRoot q fun r hr =>
        ⟨fun h => ⟨haA.trans_le (hR p (mem_sturmSeq_self hp) r hr), h⟩, And.right⟩
    rw [hindex, cauchyIndex_eq_sub_signVariations_Ioo p q hab,
      signVariationsRight_eq_signVariationsAt fun r hr hz => (hR r hr a hz).not_gt haA, hA a haA]

/-- On `(-∞, b]` the Cauchy index is the variations at `-∞` minus the right-hand variations
at `b`. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Iic (p q : R[X]) (b : R) :
    cauchyIndex p q (Iic b) =
      (signVariationsAtBot (sturmSeq p q) : ℤ) - signVariationsRight (sturmSeq p q) b := by
  first
  | rw [← Iio_insert, cauchyIndex_insert _ _ (by simp), cauchyIndex_eq_sub_signVariations_Iio,
      cauchyJump_eq_sub_signVariations]
    ring

/-- The Cauchy index of `q / p` on the whole ordered real closed field is
computed by the degree-parity and leading-coefficient variations of its Sturm
sequence. No squarefreeness or coprimality assumption is needed. For a zero
denominator both sides are zero by convention. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_univ (p q : R[X]) :
    cauchyIndex p q univ =
      (signVariationsAtBot (sturmSeq p q) : ℤ) - signVariationsAtTop (sturmSeq p q) := by
  first
  | rw [← Iic_union_Ioi (a := (0 : R)), cauchyIndex_union _ _ (Iic_disjoint_Ioi le_rfl),
      cauchyIndex_eq_sub_signVariations_Iic, cauchyIndex_eq_sub_signVariations_Ioi]
    ring

/-- **Sturm–Tarski on the whole line.** The Tarski query of `q` at the distinct roots of `p` is
the drop in sign variations from `-∞` to `+∞` of the Sturm sequence of `p` and `p' * q`. No
squarefreeness assumption is needed. For `p = 0` both sides are zero. -/
theorem _root_.Polynomial.tarskiQuery_eq_signVariationsAtBot_sub_signVariationsAtTop
    (p q : R[X]) :
    tarskiQuery p q =
      (signVariationsAtBot (sturmSeq p (derivative p * q)) : ℤ) -
        signVariationsAtTop (sturmSeq p (derivative p * q)) := by
  first
  | rw [← cauchyIndex_derivative_mul_univ, cauchyIndex_eq_sub_signVariations_univ]

/-- The Euclidean recurrence for the whole-line Cauchy index. Passing from `q / p` to
`-(p % q) / q` changes the index by `sign p.leadingCoeff * sign q.leadingCoeff` when the degrees
of `p` and `q` have opposite parities, and leaves it unchanged otherwise. -/
theorem _root_.Polynomial.cauchyIndex_univ_eq_add_cauchyIndex_neg_mod {p q : R[X]} (hp : p ≠ 0)
    (hq : q ≠ 0) :
    cauchyIndex p q univ =
      (if Odd (p.natDegree + q.natDegree) then
        (sign p.leadingCoeff : ℤ) * sign q.leadingCoeff else 0) +
        cauchyIndex q (-(p % q)) univ := by
  first
  | classical
    have hp' : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
    rw [cauchyIndex_eq_sub_signVariations_univ, cauchyIndex_eq_sub_signVariations_univ,
      sturmSeq_cons hp, neg_mod, sturmSeq_cons hq]
    simp only [signVariationsAtTop_def, signVariationsAtBot_def, List.map_cons]
    rw [List.signVariations_cons_cons_of_ne_zero _ (by simpa using hp') (by simpa using hq'),
      List.signVariations_cons_cons_of_ne_zero _ hp' hq']
    simp only [sign_mul, sign_pow, Left.sign_neg, sign_one]
    rw [← SignType.ite_mul_neg_one_pow_sub_ite _ _ (sign_ne_zero.mpr hp') (sign_ne_zero.mpr hq')]
    push_cast
    ring

end TauCeti
end -- closes the original EOF section from source line 48
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Algebra/Polynomial/Sturm/CauchyIndex/Sequence.lean -/

/- BEGIN SOURCE: TauCeti/LinearAlgebra/Matrix/Congruence.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Traces and determinant pencils under rectangular congruence

For a rectangular matrix `M`, congruence `A ↦ M * A * Mᵀ` can be moved across a trace pairing
or a determinant pencil `det (1 + c • (B * _))` by congruating the test matrix `B` with the
transpose instead. These identities transport Wishart trace transforms along congruence. The file
also records the scalar regrouping that produces a congruence in the first place: expanding the
two weights of a doubly indexed family along the rows of `M` replaces the weight matrix by its
congruate. The basis substitution `r ↦ r + a + b` has determinant one when `r` differs
from `a` and `b`; its action on a bilinear form is computed entrywise below.

## Main results

* `Matrix.trace_mul_congruence` — `trace (B * (M * A * Mᵀ)) = trace ((Mᵀ * B * M) * A)`.
* `Matrix.sum_sum_smul_congruence` — expanding the weights of `∑ x y, A x y • T x y` along the
  rows of `M` congruates `A`.
* `Matrix.det_one_add_smul_transpose_mul_mul`,
  `Matrix.det_one_sub_smul_transpose_mul_mul` — the corresponding determinant pencil identities,
  instances of the Weinstein--Aronszajn identity `Matrix.det_one_add_mul_comm`.
* `Matrix.submatrix_one_mul_mul_submatrix_one` — congruence by a selection matrix is the
  corresponding submatrix.
* `Matrix.det_one_add_vecMulVec_single_add_single` and
  `Matrix.one_add_vecMulVec_single_add_single_mul_mul_transpose_apply` — the determinant and
  entries of congruence under the basis substitution `r ↦ r + a + b`.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapters 2–3.
-/

public section

namespace Matrix

/-- Moving a rectangular congruence across a trace pairing transposes the congruence matrix.
No symmetry hypotheses on `A` or `B` are needed. -/
theorem trace_mul_congruence {m n R : Type*} [Fintype m] [Fintype n]
    [NonUnitalCommSemiring R]
    (B : Matrix m m R) (M : Matrix m n R) (A : Matrix n n R) :
    (B * (M * A * Mᵀ)).trace = ((Mᵀ * B * M) * A).trace := by
  first
  | simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * M * A) Mᵀ

/-- The Weinstein--Aronszajn identity in the form used by a rectangular congruence: the
determinant pencil can be computed either before or after applying the congruence. -/
theorem det_one_add_smul_transpose_mul_mul {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R] (c : R) (B : Matrix m m R)
    (M : Matrix m n R) (A : Matrix n n R) :
    det (1 + c • ((Mᵀ * B * M) * A)) = det (1 + c • (B * (M * A * Mᵀ))) := by
  first
  | calc
      det (1 + c • ((Mᵀ * B * M) * A)) = det (1 + Mᵀ * (c • (B * M * A))) := by
        simp only [Matrix.mul_assoc, Matrix.mul_smul]
      _ = det (1 + (c • (B * M * A)) * Mᵀ) :=
        Matrix.det_one_add_mul_comm Mᵀ (c • (B * M * A))
      _ = det (1 + c • (B * (M * A * Mᵀ))) := by
        simp only [Matrix.smul_mul, Matrix.mul_assoc]

/-- The subtractive form of `Matrix.det_one_add_smul_transpose_mul_mul`. This is the form of the
determinant pencil occurring in Wishart moment-generating functions. -/
theorem det_one_sub_smul_transpose_mul_mul {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R] (c : R) (B : Matrix m m R)
    (M : Matrix m n R) (A : Matrix n n R) :
    det (1 - c • ((Mᵀ * B * M) * A)) = det (1 - c • (B * (M * A * Mᵀ))) := by
  first
  | simpa only [sub_eq_add_neg, neg_smul] using
      det_one_add_smul_transpose_mul_mul (-c) B M A

/-- **Congruence by a selection matrix reads off a submatrix.** The matrix
`(1 : Matrix n n R).submatrix f id` keeps the rows named by `f` and its transpose
`(1 : Matrix n n R).submatrix id f` keeps the columns, so congruating with it keeps exactly the
rows and columns named by `f`. -/
@[simp]
theorem submatrix_one_mul_mul_submatrix_one {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] (f : m → n) (A : Matrix n n R) :
    (1 : Matrix n n R).submatrix f id * A * (1 : Matrix n n R).submatrix id f =
      A.submatrix f f := by
  first
  | ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- **Congruence from a double expansion of the weights.** Pushing a matrix `M` through both
indices of a doubly indexed family `T` in a module turns the weight matrix `A` into the congruate
`M * A * Mᵀ`. The family is arbitrary, so the regrouping serves both a bivector in a tensor square
and two slots of a larger tensor power, where those two slots cannot be split off as a tensor
square. -/
theorem sum_sum_smul_congruence {m n R P : Type*} [Fintype m] [Fintype n] [CommSemiring R]
    [AddCommMonoid P] [Module R P] (M : Matrix m n R) (A : Matrix n n R) (T : m → m → P) :
    ∑ x : n, ∑ y : n, A x y • ∑ a : m, ∑ b : m, (M a x * M b y) • T a b =
      ∑ a : m, ∑ b : m, (M * A * Mᵀ) a b • T a b := by
  first
  | have hcoef : ∀ a b : m, ∑ x : n, ∑ y : n, A x y * (M a x * M b y) = (M * A * Mᵀ) a b := by
      intro a b
      rw [Matrix.mul_apply, Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.transpose_apply]
      ring
    calc ∑ x : n, ∑ y : n, A x y • ∑ a : m, ∑ b : m, (M a x * M b y) • T a b
        = ∑ x : n, ∑ y : n, ∑ a : m, ∑ b : m, (A x y * (M a x * M b y)) • T a b := by
          simp only [Finset.smul_sum, smul_smul]
      -- move the two outer sums past the two inner ones, one adjacent swap at a time
      _ = ∑ x : n, ∑ a : m, ∑ y : n, ∑ b : m, (A x y * (M a x * M b y)) • T a b :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ a : m, ∑ x : n, ∑ y : n, ∑ b : m, (A x y * (M a x * M b y)) • T a b := Finset.sum_comm
      _ = ∑ a : m, ∑ x : n, ∑ b : m, ∑ y : n, (A x y * (M a x * M b y)) • T a b :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ a : m, ∑ b : m, ∑ x : n, ∑ y : n, (A x y * (M a x * M b y)) • T a b :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ a : m, ∑ b : m, (M * A * Mᵀ) a b • T a b := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          simp only [← Finset.sum_smul]
          rw [hcoef a b]

section BasisSubstitution

variable {R κ : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]

/-- Replacing the basis vector `r` by `r + a + b` is unimodular. -/
theorem det_one_add_vecMulVec_single_add_single {r a b : κ} (ha : r ≠ a) (hb : r ≠ b) :
    (1 + vecMulVec (Pi.single r (1 : R)) (Pi.single a 1 + Pi.single b 1)).det = 1 := by
  first
  | rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_single]
    simp [Ne.symm ha, Ne.symm hb]

/-- The entries of a bilinear form after replacing the basis vector `r` by `r + a + b`. -/
theorem one_add_vecMulVec_single_add_single_mul_mul_transpose_apply
    (M : Matrix κ κ R) (r a b x y : κ) :
    ((1 + vecMulVec (Pi.single r 1) (Pi.single a 1 + Pi.single b 1)) * M *
        (1 + vecMulVec (Pi.single r 1) (Pi.single a 1 + Pi.single b 1))ᵀ : Matrix κ κ R) x y =
      M x y + (if x = r then M a y + M b y else 0) + (if y = r then M x a + M x b else 0) +
        (if x = r ∧ y = r then M a a + M a b + M b a + M b b else 0) := by
  first
  | simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, transpose_add,
      transpose_one, transpose_vecMulVec, vecMulVec_mul, mul_vecMulVec, Matrix.add_apply,
      vecMulVec_apply, add_vecMul, mulVec_add, single_one_vecMul, mulVec_single_one,
      Pi.add_apply, Matrix.row, Matrix.col, Pi.single_apply, mul_one]
    split_ifs <;> simp_all
    ring

end BasisSubstitution

end Matrix
end -- closes the original EOF section from source line 42
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/LinearAlgebra/Matrix/Congruence.lean -/

/- BEGIN SOURCE: TauCeti/LinearAlgebra/Matrix/CornerMinor.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The corner minor of a doubly singular matrix

The *corner minor* of a square matrix `A` indexed by `Fin (n + 1)` is the determinant of the
submatrix obtained by deleting its last row and its last column, that is, the determinant of
`A.submatrix Fin.castSucc Fin.castSucc`. Unlike the determinant it is not a conjugation
invariant in general. It becomes one on a matrix that is annihilated on the right by a column
vector `u` and on the left by a row vector `w`, as soon as the conjugating matrix fixes `u` and
`w` as well and the last coordinates of `u` and `w` are units: this is
`Matrix.det_submatrix_castSucc_conj`.

The mechanism is that `u` and `w` give `A` a factorisation through the corner minor's own index
type `Fin n`: the identity with its last row replaced by `w` carries `A` into the image of the
inclusion `Fin n ↪ Fin (n + 1)`, and the identity with its last column replaced by `u` does the
same on the other side. A conjugation `A ↦ N * A * N⁻¹` by a matrix fixing `u` and `w` therefore
multiplies the corner minor by `N.det` on one side and by `N.det⁻¹` on the other.

The rectangular deletion and inclusion matrices and the row and column framing matrices are
recorded first under `[Zero R] [One R]`, followed by their interaction with matrix
multiplication under `[NonAssocSemiring R]`. The sparse Laplace expansions along the last row
and column, the description of the corner minor as an ordinary determinant after replacing the
last column by the last standard basis vector, and the conjugation invariance formula are
proved under `[CommRing R]`.

The intended source of such a matrix is `burau b - 1` for a braid `b`, where `u` is the all-ones
vector and `w` is the geometric vector `(1, t, …, t ^ n)`.

## Main results

* `Matrix.det_eq_mul_det_submatrix_castSucc_of_row` and
  `Matrix.det_eq_mul_det_submatrix_castSucc_of_col`: the determinant of a matrix whose last row,
  or whose last column, vanishes off the diagonal is the corner entry times the corner minor.
* `Matrix.det_eq_det_submatrix_castSucc_of_apply_last`: the determinant of a matrix whose last
  row is that of the identity is its corner minor.
* `Matrix.det_updateCol_last_single`: replacing the last column by the last standard basis vector
  turns the determinant into the corner minor.
* `Matrix.submatrix_mul_of_mulVec_single`: deleting the last row and column commutes with a
  product when the left factor fixes the last standard basis vector.
* `Matrix.det_updateCol_last_smul_col_sub_single_of_det_sub_one_eq_zero`: a determinant formula
  for replacing the last column of `M - 1` by a linear combination of the last columns of `M`
  and `1`.
* `Matrix.det_submatrix_castSucc_conj`: the corner minor of `N * A * N⁻¹` equals that of `A`,
  when `A` is annihilated by `u` on the right and by `w` on the left and `N` fixes both.
-/

public section

namespace Matrix

variable {n : ℕ} {R : Type*}

section ZeroOne

variable [Zero R] [One R]

/-! ### The two rectangular matrices that delete and restore the last coordinate -/

/-- The `n × (n + 1)` matrix that deletes the last coordinate. -/
private def projCastSucc (n : ℕ) (R : Type*) [Zero R] [One R] :
    Matrix (Fin n) (Fin (n + 1)) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix Fin.castSucc id

/-- The `(n + 1) × n` matrix that includes the first `n` coordinates. -/
private def inclCastSucc (n : ℕ) (R : Type*) [Zero R] [One R] :
    Matrix (Fin (n + 1)) (Fin n) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix id Fin.castSucc

private theorem projCastSucc_apply (a : Fin n) (b : Fin (n + 1)) :
    projCastSucc n R a b = if a.castSucc = b then 1 else 0 := by
  first
  | rw [projCastSucc, Matrix.submatrix_apply, Matrix.one_apply]
    rfl

private theorem inclCastSucc_apply (a : Fin (n + 1)) (b : Fin n) :
    inclCastSucc n R a b = if a = b.castSucc then 1 else 0 := by
  first
  | rw [inclCastSucc, Matrix.submatrix_apply, Matrix.one_apply]
    rfl

/-! ### The two square matrices built from the annihilating vectors -/

/-- The identity with its last row replaced by `w`. -/
private def rowFrame (w : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).updateRow (Fin.last n) w

/-- The identity with its last column replaced by `u`. -/
private def colFrame (u : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).updateCol (Fin.last n) u

private theorem rowFrame_castSucc (w : Fin (n + 1) → R) (a : Fin n) (b : Fin (n + 1)) :
    rowFrame w a.castSucc b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) a.castSucc b := by
  first
  | rw [rowFrame, Matrix.updateRow_ne (Fin.castSucc_lt_last a).ne]

private theorem colFrame_castSucc (u : Fin (n + 1) → R) (a : Fin (n + 1)) (b : Fin n) :
    colFrame u a b.castSucc = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) a b.castSucc := by
  first
  | rw [colFrame, Matrix.updateCol_ne (Fin.castSucc_lt_last b).ne]

private theorem submatrix_rowFrame (w : Fin (n + 1) → R) :
    (rowFrame w).submatrix Fin.castSucc Fin.castSucc = 1 := by
  first
  | ext a b
    rw [Matrix.submatrix_apply, rowFrame_castSucc]
    simp [Matrix.one_apply]

private theorem submatrix_colFrame (u : Fin (n + 1) → R) :
    (colFrame u).submatrix Fin.castSucc Fin.castSucc = 1 := by
  first
  | ext a b
    rw [Matrix.submatrix_apply, colFrame_castSucc]
    simp [Matrix.one_apply]

end ZeroOne

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- Deleting the last row and column of a product is the product of the deletions, provided the
left factor has the last standard basis vector as its last column. -/
theorem submatrix_mul_of_mulVec_single (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hX : X *ᵥ Pi.single (Fin.last n) 1 = Pi.single (Fin.last n) 1) :
    (X * Y).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc * Y.submatrix Fin.castSucc Fin.castSucc := by
  first
  | have hcol : X.col (Fin.last n) = Pi.single (Fin.last n) 1 := by
      rw [← Matrix.mulVec_single_one]
      exact hX
    have hentry : ∀ i : Fin (n + 1),
        X i (Fin.last n) = (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) i :=
      fun i => congrFun hcol i
    ext u v
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hentry,
      Pi.single_eq_of_ne (Fin.castSucc_lt_last u).ne, zero_mul, add_zero]
    rfl

private theorem projCastSucc_mul {m : Type*} (A : Matrix (Fin (n + 1)) m R) :
    projCastSucc n R * A = A.submatrix Fin.castSucc id := by
  first
  | have h := Matrix.one_submatrix_mul Fin.castSucc (Equiv.refl (Fin (n + 1))) A
    simpa [projCastSucc] using h

private theorem mul_inclCastSucc {m : Type*} (A : Matrix m (Fin (n + 1)) R) :
    A * inclCastSucc n R = A.submatrix id Fin.castSucc := by
  first
  | have h := Matrix.mul_submatrix_one (Equiv.refl (Fin (n + 1))) Fin.castSucc A
    simpa [inclCastSucc] using h

private theorem projCastSucc_mul_mul_inclCastSucc (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    projCastSucc n R * A * inclCastSucc n R = A.submatrix Fin.castSucc Fin.castSucc := by
  first
  | simpa only [projCastSucc, inclCastSucc] using
      Matrix.submatrix_one_mul_mul_submatrix_one Fin.castSucc A

private theorem projCastSucc_mul_rowFrame (w : Fin (n + 1) → R) :
    projCastSucc n R * rowFrame w = projCastSucc n R := by
  first
  | rw [projCastSucc_mul]
    ext a b
    rw [Matrix.submatrix_apply, rowFrame_castSucc]
    rfl

private theorem colFrame_mul_inclCastSucc (u : Fin (n + 1) → R) :
    colFrame u * inclCastSucc n R = inclCastSucc n R := by
  first
  | rw [mul_inclCastSucc]
    ext a b
    rw [Matrix.submatrix_apply, colFrame_castSucc]
    rfl

private theorem rowFrame_mul (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {w : Fin (n + 1) → R}
    (hw : w ᵥ* A = 0) :
    rowFrame w * A = inclCastSucc n R * (projCastSucc n R * A) := by
  first
  | rw [projCastSucc_mul]
    ext i k
    rcases eq_or_ne i (Fin.last n) with rfl | hi
    · have h1 : (rowFrame w * A) (Fin.last n) k = (w ᵥ* A) k := by
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, rowFrame, Matrix.updateRow_self]
      have h2 : ∀ j : Fin n, inclCastSucc n R (Fin.last n) j = 0 := fun j => by
        rw [inclCastSucc_apply]
        simp [(Fin.castSucc_lt_last j).ne']
      rw [h1, hw, Pi.zero_apply, Matrix.mul_apply]
      simp [h2]
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      have h2 : ∀ j : Fin n, inclCastSucc n R i.castSucc j = if i = j then 1 else 0 := fun j => by
        rw [inclCastSucc_apply]
        simp [Fin.castSucc_inj]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [rowFrame_castSucc, h2, Matrix.one_apply, ite_mul, zero_mul, one_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.submatrix_apply, id]

private theorem mul_colFrame (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {u : Fin (n + 1) → R}
    (hu : A *ᵥ u = 0) :
    A * colFrame u = A * inclCastSucc n R * projCastSucc n R := by
  first
  | rw [mul_inclCastSucc]
    ext i k
    rcases eq_or_ne k (Fin.last n) with rfl | hk
    · have h1 : (A * colFrame u) i (Fin.last n) = (A *ᵥ u) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colFrame, Matrix.updateCol_self]
      have h2 : ∀ j : Fin n, projCastSucc n R j (Fin.last n) = 0 := fun j => by
        rw [projCastSucc_apply]
        simp [(Fin.castSucc_lt_last j).ne]
      rw [h1, hu, Pi.zero_apply, Matrix.mul_apply]
      simp [h2]
    · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      have h2 : ∀ j : Fin n, projCastSucc n R j k.castSucc = if j = k then 1 else 0 := fun j => by
        rw [projCastSucc_apply]
        simp [Fin.castSucc_inj]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [colFrame_castSucc, h2, Matrix.one_apply, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.submatrix_apply, id]

end NonAssocSemiring

variable [CommRing R]

/-- Laplace expansion along the last row of a matrix whose last row vanishes off the diagonal. -/
theorem det_eq_mul_det_submatrix_castSucc_of_row (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ j, j ≠ Fin.last n → A (Fin.last n) j = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  first
  | rw [Matrix.det_succ_row A (Fin.last n),
      Finset.sum_eq_single (Fin.last n) (fun j _ hj => by rw [h j hj]; ring) (by simp)]
    rw [Fin.succAbove_last, Fin.val_last, Even.neg_one_pow ⟨n, rfl⟩, one_mul]

/-- Laplace expansion along the last column of a matrix whose last column vanishes off the
diagonal. -/
theorem det_eq_mul_det_submatrix_castSucc_of_col (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ i, i ≠ Fin.last n → A i (Fin.last n) = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  first
  | rw [← Matrix.det_transpose A, det_eq_mul_det_submatrix_castSucc_of_row Aᵀ h,
      Matrix.transpose_apply, ← Matrix.transpose_submatrix, Matrix.det_transpose]

/-- The determinant of a matrix whose last row is that of the identity is its corner minor. -/
theorem det_eq_det_submatrix_castSucc_of_apply_last {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (h : A (Fin.last n) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n)) :
    A.det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
  first
  | rw [det_eq_mul_det_submatrix_castSucc_of_row A fun j hj ↦ by rw [h, one_apply_ne' hj], h,
      one_apply_eq, one_mul]

/-- Replacing the last column of a matrix by the last standard basis vector turns its determinant
into its corner minor. -/
theorem det_updateCol_last_single (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (A.updateCol (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  first
  | rw [det_eq_mul_det_submatrix_castSucc_of_col _ fun i hi => by
        rw [Matrix.updateCol_self, Pi.single_eq_of_ne hi],
      Matrix.updateCol_self, Pi.single_eq_same, one_mul]
    congr 1
    ext a b
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply,
      Matrix.updateCol_ne (Fin.castSucc_lt_last b).ne]

/-- The determinant of a matrix `M - 1` whose last column has been replaced by
`c • M.col (last) - e (last)`, in terms of the corner minor of `M - 1`. -/
theorem det_updateCol_last_smul_col_sub_single_of_det_sub_one_eq_zero
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hdet : (M - 1).det = 0) (c : R) :
    ((M - 1).updateCol (Fin.last n)
        (fun u => c * M u (Fin.last n) - (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) u)).det =
      (c - 1) * ((M - 1).submatrix Fin.castSucc Fin.castSucc).det := by
  first
  | have hfun : (fun u => c * M u (Fin.last n) - (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) u) =
        c • (fun u => (M - 1) u (Fin.last n)) +
          (c - 1) • (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) := by
      funext u
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply,
        Pi.single_apply]
      split_ifs <;> ring
    rw [hfun, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, Matrix.det_updateCol_smul,
      Matrix.updateCol_eq_self, hdet, Matrix.det_updateCol_last_single, mul_zero, zero_add]

private theorem det_rowFrame (w : Fin (n + 1) → R) : (rowFrame w).det = w (Fin.last n) := by
  first
  | rw [det_eq_mul_det_submatrix_castSucc_of_col _ ?_, submatrix_rowFrame, Matrix.det_one, mul_one,
      rowFrame, Matrix.updateRow_self]
    intro i hi
    rw [rowFrame, Matrix.updateRow_ne hi, Matrix.one_apply_ne hi]

private theorem det_colFrame (u : Fin (n + 1) → R) : (colFrame u).det = u (Fin.last n) := by
  first
  | rw [det_eq_mul_det_submatrix_castSucc_of_row _ ?_, submatrix_colFrame, Matrix.det_one, mul_one,
      colFrame, Matrix.updateCol_self]
    intro j hj
    rw [colFrame, Matrix.updateCol_ne hj, Matrix.one_apply_ne' hj]

/-! ### Conjugation invariance of the corner minor -/

private theorem det_projCastSucc_mul_mul (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {w : Fin (n + 1) → R} (hwN : w ᵥ* N = w) (hw : IsUnit (w (Fin.last n))) :
    (projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R)).det = N.det := by
  first
  | have hdet : IsUnit (rowFrame w).det := by rw [det_rowFrame]; exact hw
    have hmul : rowFrame w * (rowFrame w)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have hlast : rowFrame w (Fin.last n) = w := Matrix.updateRow_self
    have hrow : (rowFrame w * N * (rowFrame w)⁻¹) (Fin.last n) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) := by
      have h1 : (rowFrame w * N) (Fin.last n) = rowFrame w (Fin.last n) := by
        rw [Matrix.mul_apply_eq_vecMul, hlast, hwN]
      rw [Matrix.mul_apply_eq_vecMul, h1, ← Matrix.mul_apply_eq_vecMul, hmul]
    have hsub : (rowFrame w * N * (rowFrame w)⁻¹).submatrix Fin.castSucc Fin.castSucc =
        projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R) := by
      rw [← projCastSucc_mul_mul_inclCastSucc]
      calc projCastSucc n R * (rowFrame w * N * (rowFrame w)⁻¹) * inclCastSucc n R
          = projCastSucc n R * rowFrame w * (N * ((rowFrame w)⁻¹ * inclCastSucc n R)) := by
            simp only [Matrix.mul_assoc]
        _ = projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R) := by
            rw [projCastSucc_mul_rowFrame, Matrix.mul_assoc]
    have hone : (rowFrame w).det * ((rowFrame w)⁻¹).det = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hexp : (rowFrame w * N * (rowFrame w)⁻¹).det =
        (projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R)).det := by
      rw [det_eq_mul_det_submatrix_castSucc_of_row _ fun j hj => by
        rw [congrFun hrow j, Matrix.one_apply_ne' hj], hsub, congrFun hrow (Fin.last n),
        Matrix.one_apply_eq, one_mul]
    rw [← hexp, Matrix.det_mul, Matrix.det_mul]
    linear_combination N.det * hone

private theorem det_mul_mul_inclCastSucc (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {u : Fin (n + 1) → R} (hMu : M *ᵥ u = u) (hu : IsUnit (u (Fin.last n))) :
    (projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R).det = M.det := by
  first
  | have hdet : IsUnit (colFrame u).det := by rw [det_colFrame]; exact hu
    have hmul : (colFrame u)⁻¹ * colFrame u = 1 := Matrix.nonsing_inv_mul _ hdet
    have hUe : colFrame u *ᵥ Pi.single (Fin.last n) 1 = u := by
      rw [Matrix.mulVec_single_one]
      funext i
      rw [Matrix.col_apply, colFrame, Matrix.updateCol_self]
    have hUinv : (colFrame u)⁻¹ *ᵥ u = Pi.single (Fin.last n) 1 := by
      have h : (colFrame u)⁻¹ *ᵥ (colFrame u *ᵥ Pi.single (Fin.last n) 1) =
          Pi.single (Fin.last n) 1 := by
        rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
      rwa [hUe] at h
    have key : ∀ i, ((colFrame u)⁻¹ * M * colFrame u) i (Fin.last n) =
        (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) i := by
      have hkey : ((colFrame u)⁻¹ * M * colFrame u) *ᵥ Pi.single (Fin.last n) 1 =
          Pi.single (Fin.last n) 1 := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUe, hMu, hUinv]
      intro i
      have h := congrFun hkey i
      rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h
    have hsub : ((colFrame u)⁻¹ * M * colFrame u).submatrix Fin.castSucc Fin.castSucc =
        projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R := by
      rw [← projCastSucc_mul_mul_inclCastSucc]
      calc projCastSucc n R * ((colFrame u)⁻¹ * M * colFrame u) * inclCastSucc n R
          = projCastSucc n R * (colFrame u)⁻¹ * M * (colFrame u * inclCastSucc n R) := by
            simp only [Matrix.mul_assoc]
        _ = projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R := by
            rw [colFrame_mul_inclCastSucc]
    have hone : ((colFrame u)⁻¹).det * (colFrame u).det = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hexp : ((colFrame u)⁻¹ * M * colFrame u).det =
        (projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R).det := by
      rw [det_eq_mul_det_submatrix_castSucc_of_col _ fun i hi => by
        rw [key i, Pi.single_eq_of_ne hi], hsub, key (Fin.last n), Pi.single_eq_same, one_mul]
    rw [← hexp, Matrix.det_mul, Matrix.det_mul]
    linear_combination M.det * hone

/-- **The corner minor is a conjugation invariant on doubly singular matrices.** If a square
matrix `A` is annihilated on the right by a column vector `u` and on the left by a row vector `w`,
both of which have a unit in their last coordinate, then conjugating `A` by any invertible matrix
that fixes `u` and `w` leaves the determinant of `A.submatrix Fin.castSucc Fin.castSucc`
unchanged. -/
theorem det_submatrix_castSucc_conj (A N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {u w : Fin (n + 1) → R} (hAu : A *ᵥ u = 0) (hwA : w ᵥ* A = 0) (hNu : N *ᵥ u = u)
    (hwN : w ᵥ* N = w) (hN : IsUnit N.det) (hu : IsUnit (u (Fin.last n)))
    (hw : IsUnit (w (Fin.last n))) :
    ((N * A * N⁻¹).submatrix Fin.castSucc Fin.castSucc).det =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  first
  | have hNinv : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv _ hN
    have hNinv' : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul _ hN
    have hNinvu : N⁻¹ *ᵥ u = u := by
      conv_lhs => rw [← hNu]
      rw [Matrix.mulVec_mulVec, hNinv', Matrix.one_mulVec]
    have hrowdet : IsUnit (rowFrame w).det := by rw [det_rowFrame]; exact hw
    have hcoldet : IsUnit (colFrame u).det := by rw [det_colFrame]; exact hu
    have hGinv : (rowFrame w)⁻¹ * rowFrame w = 1 := Matrix.nonsing_inv_mul _ hrowdet
    have hUinv : colFrame u * (colFrame u)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hcoldet
    -- the canonical factorisation of `A` through the corner index type
    have hA1 : (rowFrame w)⁻¹ * inclCastSucc n R * (projCastSucc n R * A) = A := by
      calc (rowFrame w)⁻¹ * inclCastSucc n R * (projCastSucc n R * A)
          = (rowFrame w)⁻¹ * (inclCastSucc n R * (projCastSucc n R * A)) := by
            rw [Matrix.mul_assoc]
        _ = A := by rw [← rowFrame_mul A hwA, ← Matrix.mul_assoc, hGinv, Matrix.one_mul]
    have hA2 : A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹) = A := by
      calc A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹)
          = A * inclCastSucc n R * projCastSucc n R * (colFrame u)⁻¹ :=
            (Matrix.mul_assoc _ _ _).symm
        _ = A := by rw [← mul_colFrame A hAu, Matrix.mul_assoc, hUinv, Matrix.mul_one]
    have hPA : projCastSucc n R * A =
        A.submatrix Fin.castSucc Fin.castSucc * (projCastSucc n R * (colFrame u)⁻¹) := by
      calc projCastSucc n R * A
          = projCastSucc n R * (A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹)) := by
            rw [hA2]
        _ = projCastSucc n R * A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [projCastSucc_mul_mul_inclCastSucc]
    have main : (N * A * N⁻¹).submatrix Fin.castSucc Fin.castSucc =
        projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R) *
          (A.submatrix Fin.castSucc Fin.castSucc) *
          (projCastSucc n R * (colFrame u)⁻¹ * N⁻¹ * inclCastSucc n R) := by
      rw [← projCastSucc_mul_mul_inclCastSucc]
      conv_lhs => rw [← hA1]
      rw [hPA]
      simp only [Matrix.mul_assoc]
    rw [main, Matrix.det_mul, Matrix.det_mul,
      det_projCastSucc_mul_mul N hwN hw, det_mul_mul_inclCastSucc N⁻¹ hNinvu hu]
    have hone : N.det * (N⁻¹).det = 1 := by rw [← Matrix.det_mul, hNinv, Matrix.det_one]
    linear_combination (A.submatrix Fin.castSucc Fin.castSucc).det * hone

end Matrix
end -- closes the original EOF section from source line 57
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/LinearAlgebra/Matrix/CornerMinor.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/DegreeDrop/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Degree drops in subresultant coefficient minors

Fixed-bound principal subresultants need not equal the principal subresultants computed at
smaller actual degrees. Lowering the right bound contributes a power of the coefficient at
the left bound; lowering the left bound also contributes a block-order sign. The coefficient-minor
identities specialize to principal coefficients, including their terminal cases. These identities
explain how specialization interacts with degree drops, without assuming nonvanishing of
specialized leading coefficients.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4 (specialization of subresultants).
-/

public section

namespace TauCeti

open _root_.Polynomial

variable {R : Type*}

private theorem lastRow_of_degree_drop [Semiring R] {p q : R[X]} {m n j k : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j < m) (hjn : j ≤ n)
    (i l : Fin ((m - j) + (n + 1 - j))) (hi : i.val = (m - j) + (n - j)) :
    subresultantCoeffMatrix p q m (n + 1) j k i l =
      if l.val = (m - j) + (n - j) then p.coeff m else 0 := by
  first
  | have hi0 : i.val ≠ 0 := by omega
    rw [subresultantCoeffMatrix_apply_eq_coeff hm (hn.trans (Nat.le_succ n))]
    simp only [hi0, ↓reduceIte]
    induction l using Fin.addCases with
    | left l =>
      have hdeg : q.natDegree < i.val + j - l.val := by omega
      have hle : l.val ≤ i.val + j := by omega
      have hne : l.val ≠ (m - j) + (n - j) := by omega
      simp [coeff_X_pow_mul', hle, coeff_eq_zero_of_natDegree_lt hdeg, hne]
    | right l =>
      by_cases h : (m - j) + l.val = (m - j) + (n - j)
      · have hcoeff : i.val + j - l.val = m := by omega
        have hle : l.val ≤ i.val + j := by omega
        simp [coeff_X_pow_mul', h, hcoeff, hle]
      · have hdeg : p.natDegree < i.val + j - l.val := by omega
        have hle : l.val ≤ i.val + j := by omega
        have hne : l.val ≠ n - j := by omega
        simp [coeff_X_pow_mul', hle, hne, coeff_eq_zero_of_natDegree_lt hdeg]

variable [CommRing R]

/-- Lowering an oversized right bound by one scales every coefficient minor by the coefficient
at the left bound. The smaller right terminal index is included, but `j < m` is essential. -/
theorem _root_.Polynomial.subresultantCoeff_succ_right {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j < m) (hjn : j ≤ n)
    (k : ℕ) :
    subresultantCoeff p q m (n + 1) j k =
      p.coeff m * subresultantCoeff p q m n j k := by
  first
  | classical
    let d := (m - j) + (n - j)
    have hd : (m - j) + (n + 1 - j) = d + 1 := by dsimp [d]; omega
    let e := finCongr hd
    let M := (subresultantCoeffMatrix p q m (n + 1) j k).reindex e e
    have hlast (l : Fin (d + 1)) :
        M (Fin.last d) l = if l = Fin.last d then p.coeff m else 0 := by
      simpa only [M, Matrix.reindex_apply, Matrix.submatrix_apply, e, finCongr_apply,
        finCongr_symm, Fin.val_cast, Fin.val_last, Fin.ext_iff] using
        lastRow_of_degree_drop hm hn hjm hjn (e.symm (Fin.last d)) (e.symm l) rfl
    -- Removing the last row and column preserves the replaced first row.
    have hminor : M.submatrix Fin.castSucc Fin.castSucc =
        subresultantCoeffMatrix p q m n j k := by
      ext i l
      simp only [Matrix.submatrix_apply, M, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [subresultantCoeffMatrix_apply_eq_coeff hm (hn.trans (Nat.le_succ n)),
        subresultantCoeffMatrix_apply_eq_coeff hm hn]
      induction l using Fin.addCases with
      | left l =>
        have hl : e.symm (Fin.castSucc (Fin.castAdd (n - j) l)) =
            Fin.castAdd (n + 1 - j) l := by ext; rfl
        rw [hl]
        simp [e]
      | right l =>
        have hle : n - j ≤ n + 1 - j := by omega
        have hl : e.symm (Fin.castSucc (Fin.natAdd (m - j) l)) =
            Fin.natAdd (m - j) (Fin.castLE hle l) := by ext; rfl
        rw [hl]
        simp [e]
    have hdet : subresultantCoeff p q m (n + 1) j k = M.det := by
      simp only [M, Matrix.det_reindex_self, subresultantCoeff_def]
    rw [hdet, Matrix.det_eq_mul_det_submatrix_castSucc_of_row M (by
      intro l hl
      simp [hlast, hl]), hlast, hminor]
    simp [subresultantCoeff_def]

/-- Lowering an oversized right bound scales every coefficient minor by the corresponding
power of the coefficient at the left bound, including the smaller right terminal index. -/
theorem _root_.Polynomial.subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j < m) (hjn : j ≤ n) (k : ℕ) :
    subresultantCoeff p q m N j k =
      p.coeff m ^ (N - n) * subresultantCoeff p q m n j k := by
  first
  | induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      rw [subresultantCoeff_succ_right hm (hn.trans hN) hjm (hjn.trans hN), ih]
      have hgap : N + 1 - n = (N - n) + 1 := by omega
      rw [hgap, pow_succ]
      ring

/-- Lowering an oversized left bound scales coefficient minors by the right coefficient
power and the column-block sign. The smaller left terminal index is included. -/
theorem _root_.Polynomial.subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j < n) (k : ℕ) :
    subresultantCoeff p q M n j k = (-1) ^ ((M - m) * (n - j)) *
      q.coeff n ^ (M - m) * subresultantCoeff p q m n j k := by
  first
  | have hgap : M - j = (M - m) + (m - j) := by omega
    calc
      subresultantCoeff p q M n j k = (-1) ^ ((M - j) * (n - j)) *
          (q.coeff n ^ (M - m) * subresultantCoeff q p n m j k) := by
        rw [subresultantCoeff_comm p q M n j k,
          subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hn hm hM hjn hjm]
      _ = _ := by
        rw [subresultantCoeff_comm p q m n j k, hgap, add_mul, pow_add]
        ring

/-- Lowering an oversized right degree bound by one multiplies the principal
subresultant by the coefficient at the left bound. The terminal smaller index is included. -/
theorem _root_.Polynomial.psc_succ_right {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m (n + 1) j = p.coeff m * psc p q m n j := by
  first
  | by_cases hjm' : j < m
    · simpa only [subresultantCoeff_self] using
        subresultantCoeff_succ_right hm hn hjm' hjn j
    · have hjeq : j = m := by omega
      subst j
      rw [psc_left_bound, psc_left_bound]
      have hgap : n + 1 - m = (n - m) + 1 := by omega
      rw [hgap, pow_succ, mul_comm]

/-- An arbitrary drop in the right bound contributes the corresponding power of the
coefficient at the left bound. The lower right bound need only dominate the degree. -/
theorem _root_.Polynomial.psc_eq_coeff_pow_mul_of_right_degree_drop {p q : R[X]}
    {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m N j = p.coeff m ^ (N - n) * psc p q m n j := by
  first
  | by_cases hjm' : j < m
    · simpa only [subresultantCoeff_self] using
        subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm' hjn j
    · have hjeq : j = m := by omega
      subst j
      rw [psc_left_bound, psc_left_bound, ← pow_add]
      congr 1
      omega

/-- Dropping the left bound also contributes the sign of moving its removed columns
past the right block. The lower left bound need only dominate the degree. -/
theorem _root_.Polynomial.psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop {p q : R[X]}
    {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q M n j =
      (-1) ^ ((M - m) * (n - j)) * q.coeff n ^ (M - m) * psc p q m n j := by
  first
  | by_cases hjn' : j < n
    · simpa only [subresultantCoeff_self] using
        subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hjm hjn' j
    · have hjeq : j = n := by omega
      subst j
      simp only [psc_right_bound, Nat.sub_self, mul_zero, pow_zero, one_mul, ← pow_add]
      congr 1
      omega

/-- At strict subresultant indices, simultaneous drops in both degree bounds force
vanishing. Terminal indices are excluded: their empty determinant can still be `1`. -/
theorem _root_.Polynomial.psc_eq_zero_of_natDegree_lt_bounds {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree < m) (hn : q.natDegree < n) (hj : j < min m n) :
    psc p q m n j = 0 := by
  first
  | have hnpos : 0 < n := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    rw [psc_succ_right hm.le (by omega) (by omega) (by omega),
      coeff_eq_zero_of_natDegree_lt hm, zero_mul]

/-- After coefficient specialization, lowering the right bound amounts to truncating
that input and multiplying by a power of the specialized coefficient at the left bound.
In particular, the lower bound can be the actual degree of the specialized right input. -/
theorem _root_.Polynomial.map_psc_of_right_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m n N j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (psc p q m N j) = f (p.coeff m) ^ (N - n) *
      psc (p.map f) ((q.reductum (n + 1)).map f) m n j := by
  first
  | have htrunc : (q.reductum (n + 1)).map f = q.map f := by
      rw [← reductum_map]
      exact reductum_eq_self (by omega)
    rw [htrunc, ← psc_map_map,
      psc_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm hjn, coeff_map]

/-- The left-bound specialization formula retains the column-block sign as well as the
power of the specialized coefficient at the right bound. Truncation occurs before mapping. -/
theorem _root_.Polynomial.map_psc_of_left_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m M n j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (psc p q M n j) = (-1) ^ ((M - m) * (n - j)) * f (q.coeff n) ^ (M - m) *
      psc ((p.reductum (m + 1)).map f) (q.map f) m n j := by
  first
  | have htrunc : (p.reductum (m + 1)).map f = p.map f := by
      rw [← reductum_map]
      exact reductum_eq_self (by omega)
    rw [htrunc, ← psc_map_map,
      psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hjm hjn, coeff_map]

end TauCeti
end -- closes the original EOF section from source line 28
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/DegreeDrop/Basic.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/DegreeDrop/Polynomial.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Degree drops in subresultant polynomials

Below the smaller degree bounds, lowering a bound scales the entire subresultant polynomial,
not just its principal coefficient. At a smaller terminal bound, the surviving polynomial is
instead a scalar multiple of the corresponding input. Thus terminal scalar data must not be replaced
by the zero polynomial used outside the strict subresultant range.

The coefficient-minor formulas retain formal bounds and hold over arbitrary commutative rings.
The specialization formulas use reducta taken before mapping coefficients, allowing degree
drops and zero fibers. These identities supply the specialization laws for comparisons with
polynomial remainder sequences.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4 (specialization of subresultants).
-/

public section

namespace TauCeti

open _root_.Polynomial

variable {R : Type*}

variable [CommRing R]

/-- Below both smaller bounds, an arbitrary right-bound drop scales the whole subresultant
polynomial. The formula does not replace a terminal scalar minor by a polynomial. -/
theorem _root_.Polynomial.subresultant_eq_C_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hj : j < min m n) :
    subresultant p q m N j = C (p.coeff m ^ (N - n)) * subresultant p q m n j := by
  first
  | ext k
    have hj' : j < min m N := by omega
    by_cases hk : k ≤ j
    · simp only [coeff_subresultant, hj, hj', hk, and_self, ↓reduceIte, coeff_C_mul]
      exact subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hN
        (by omega) (by omega) k
    · simp only [coeff_C_mul, coeff_subresultant, hk, and_false, ↓reduceIte, mul_zero]

/-- Below both smaller bounds, a left-bound drop scales the whole subresultant polynomial,
including the column-block sign. -/
theorem _root_.Polynomial.subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hj : j < min m n) :
    subresultant p q M n j = C ((-1) ^ ((M - m) * (n - j)) * q.coeff n ^ (M - m)) *
      subresultant p q m n j := by
  first
  | ext k
    have hj' : j < min M n := by omega
    by_cases hk : k ≤ j
    · simp only [coeff_subresultant, hj, hj', hk, and_self, ↓reduceIte, coeff_C_mul]
      simpa only [mul_assoc] using
        subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM
          (by omega) (by omega) k
    · simp only [coeff_C_mul, coeff_subresultant, hk, and_false, ↓reduceIte, mul_zero]

/-- When only the right bound drops, the subresultant at its smaller terminal index survives
as a scalar multiple of the right polynomial, rather than a terminal subresultant polynomial. -/
@[simp]
theorem _root_.Polynomial.subresultant_right_bound_of_degree_drop {p q : R[X]} {m n N : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hnm : n < m) (hnN : n < N) :
    subresultant p q m N n =
      C (p.coeff m ^ (N - n) * q.coeff n ^ (m - n - 1)) * q := by
  first
  | ext k
    have hj : n < min m N := by omega
    rw [coeff_C_mul, coeff_subresultant]
    by_cases hk : k ≤ n
    · simp only [hj, hk, and_self, ↓reduceIte]
      rw [subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hnN.le hnm le_rfl,
        subresultantCoeff_right_bound p q hnm hk]
      ring
    · have hq : q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hk, hq]

/-- The smaller left terminal index likewise survives as a scalar multiple of the left input,
with the sign from swapping the formal column blocks. -/
@[simp]
theorem _root_.Polynomial.subresultant_left_bound_of_degree_drop {p q : R[X]} {m M n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hmn : m < n) (hmM : m < M) :
    subresultant p q M n m =
      C ((-1) ^ ((M - m) * (n - m)) * q.coeff n ^ (M - m) *
        p.coeff m ^ (n - m - 1)) * p := by
  first
  | rw [subresultant_comm, subresultant_right_bound_of_degree_drop hn hm hmn hmM,
      ← mul_assoc, ← C_mul]
    congr 2
    ring

/-- Dropping both formal bounds forces every subresultant polynomial to vanish, not merely
its principal coefficient. Outside the strict range the polynomial is zero by convention. -/
@[simp]
theorem _root_.Polynomial.subresultant_eq_zero_of_natDegree_lt_bounds {p q : R[X]}
    {m n j : ℕ} (hm : p.natDegree < m) (hn : q.natDegree < n) :
    subresultant p q m n j = 0 := by
  first
  | by_cases hj : j < min m n
    · have hnpos : 0 < n := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
      ext k
      rw [coeff_subresultant]
      by_cases hk : k ≤ j
      · simp only [hj, hk, and_self, ↓reduceIte, coeff_zero]
        rw [subresultantCoeff_succ_right hm.le (by omega) (by omega) (by omega),
          coeff_eq_zero_of_natDegree_lt hm, zero_mul]
      · simp [hk]
    · exact subresultant_eq_zero_of_min_le p q m n j (by omega)

/-- After specialization, a right-bound drop below the smaller bounds scales the mapped
subresultant. The reduced input is obtained by truncating before mapping. -/
theorem _root_.Polynomial.map_subresultant_of_right_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m n N j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hj : j < min m n) :
    (subresultant p q m N j).map f = C (f (p.coeff m) ^ (N - n)) *
      subresultant (p.map f) ((q.reductum (n + 1)).map f) m n j := by
  first
  | have htrunc : (q.reductum (n + 1)).map f = q.map f := by
      rw [← reductum_map]
      exact reductum_eq_self (by omega)
    rw [htrunc, ← subresultant_map_map,
      subresultant_eq_C_coeff_pow_mul_of_right_degree_drop hm hn hN hj, coeff_map]

/-- The left-bound specialization formula retains the column-block sign and the right
coefficient power, with truncation before mapping. -/
theorem _root_.Polynomial.map_subresultant_of_left_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m M n j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hM : m ≤ M) (hj : j < min m n) :
    (subresultant p q M n j).map f =
      C ((-1) ^ ((M - m) * (n - j)) * f (q.coeff n) ^ (M - m)) *
        subresultant ((p.reductum (m + 1)).map f) (q.map f) m n j := by
  first
  | have htrunc : (p.reductum (m + 1)).map f = p.map f := by
      rw [← reductum_map]
      exact reductum_eq_self (by omega)
    rw [htrunc, ← subresultant_map_map,
      subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hj, coeff_map]

end TauCeti
end -- closes the original EOF section from source line 29
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/DegreeDrop/Polynomial.lean -/

/- BEGIN SOURCE: TauCeti/Data/Nat/Choose/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Elementary identities for binomial coefficients

This file records arithmetic identities involving natural-number binomial coefficients.

Besides three identities and a parity formula for the second binomial coefficient and the sum
`2ⁿ - 2` of the inner binomial coefficients `C(n, i)`, `0 < i < n`, it develops Vandermonde's
convolution `∑ i, C(A, i) * C(B, r - i) = C(A + B, r)` in the shape taken by factorial moments of a
law supported on such a convolution: each summand is weighted by the falling factorial `(i)ₘ` of
the summation index. The weighted sum is again a single binomial coefficient,
`(A)ₘ * C(A + B - m, r - m)`, because `(i)ₘ` lowers both indices of `C(A, i)` at once.

## Main results

* `Nat.choose_two_add_mul_succ_div_two`: the sum of the second binomial coefficient and
  the triangular number is the corresponding square.
* `Nat.add_choose_two`: the second binomial coefficient of a sum, with its cross term.
* `Nat.pow_three_sub_self_eq_mul_choose_two`: `g³ - g = (2g + 2) · C(g, 2)`.
* `Nat.even_choose_two_iff`, `Nat.neg_one_pow_choose_two`: `C(m, 2)` and `⌊m / 2⌋` have the same
  parity, so `(-1) ^ C(m, 2) = (-1) ^ ⌊m / 2⌋`.
* `Nat.sum_Icc_choose_eq_two_pow_sub_two`: the binomial coefficients `C(n, i)`, `0 < i < n`,
  sum to `2ⁿ - 2`.
* `Nat.descFactorial_mul_choose`: a falling factorial of the lower index lowers both indices,
  `(i)ₘ * C(A, i) = (A)ₘ * C(A - m, i - m)`.
* `Nat.sum_range_descFactorial_mul_choose_mul_choose`: Vandermonde's convolution weighted by a
  falling factorial of the summation index.
* `Nat.add_choose_mul_choose_mul_choose`: choosing `r` of `i` objects and `s` of `j` objects
  factors through choosing `r + s` of all `i + j` objects.
* `Nat.add_ascFactorial_mul_multichoose`: a rising factorial absorbed into a multiset
  coefficient, `(r + k)⁽ᵐ⁾ * multichoose r k = r⁽ᵐ⁾ * multichoose (r + m) k`.
* `Nat.mem_filter_range_not_dvd_choose`: among `k ≤ n`, the condition `p ∤ n choose k` alone
  decides membership, since `n choose k = 0` for `k > n`.

## References

* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley, 1994,
  Section 5.1 (the absorption identity and Vandermonde's convolution, equation (5.27)).
-/

public section

open Finset

namespace Nat

/-- The sum of `N.choose 2` and the `N`th triangular number is `N ^ 2`. -/
theorem choose_two_add_mul_succ_div_two (N : ℕ) :
    N.choose 2 + N * (N + 1) / 2 = N * N := by
  first
  | rw [Nat.choose_two_right]
    apply Nat.mul_right_cancel (by norm_num : 0 < 2)
    rw [Nat.add_mul, Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd,
      Nat.div_mul_cancel (Nat.even_mul_succ_self N).two_dvd]
    by_cases hN : N = 0
    · simp [hN]
    · rw [← Nat.mul_add]
      have hsum : N - 1 + (N + 1) = 2 * N := by omega
      rw [hsum]
      ring

/-- The second binomial coefficient of a sum: `C(m + n, 2) = C(m, 2) + C(n, 2) + mn`. -/
theorem add_choose_two (m n : ℕ) : (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
  first
  | induction n with
    | zero => simp
    | succ n ih =>
        have h1 : (m + (n + 1)).choose 2 = (m + n).choose 1 + (m + n).choose 2 := by
          rw [← Nat.add_assoc]
          exact Nat.choose_succ_succ (m + n) 1
        have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
        rw [h1, h2, ih, Nat.choose_one_right, Nat.choose_one_right]
        ring

/-- `g³ - g = (2g + 2) · C(g, 2)`. -/
theorem pow_three_sub_self_eq_mul_choose_two (g : ℕ) :
    g ^ 3 - g = (2 * g + 2) * g.choose 2 := by
  first
  | have h2 : g.choose 2 * 2 = g * (g - 1) := by
      rw [Nat.choose_two_right, Nat.div_mul_cancel g.even_mul_pred_self.two_dvd]
    rcases g with _ | g
    · simp
    · rw [Nat.add_sub_cancel] at h2
      have h : (2 * (g + 1) + 2) * (g + 1).choose 2 = (g + 2) * ((g + 1) * g) := by
        rw [← h2]
        ring
      rw [h]
      exact Nat.sub_eq_of_eq_add (by ring)

/-- `C(m, 2)` and `⌊m / 2⌋` have the same parity: going from `m` to `m + 2` adds `2m + 1` to the
first and `1` to the second. -/
theorem even_choose_two_iff (m : ℕ) : Even (m.choose 2) ↔ Even (m / 2) := by
  first
  | induction m using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more m ih _ =>
      have h : (m + 2).choose 2 = m.choose 2 + 2 * m + 1 := by
        rw [add_choose_two, Nat.choose_self]
        ring
      rw [h, show (m + 2) / 2 = m / 2 + 1 by omega]
      simp [Nat.even_add_one, parity_simps, ih]

/-- The sign `(-1) ^ C(m, 2)` of the order-reversing permutation of `m` letters is
`(-1) ^ ⌊m / 2⌋`. -/
theorem neg_one_pow_choose_two {R : Type*} [Monoid R] [HasDistribNeg R] (m : ℕ) :
    (-1 : R) ^ m.choose 2 = (-1) ^ (m / 2) :=
  neg_one_pow_congr (even_choose_two_iff m)

/-- The binomial coefficients `C(n, i)` with `0 < i < n` sum to `2ⁿ - 2`. -/
theorem sum_Icc_choose_eq_two_pow_sub_two (n : ℕ) :
    ∑ i ∈ Icc 1 (n - 1), n.choose i = 2 ^ n - 2 := by
  first
  | rcases n with _ | n
    · simp
    have h := sum_range_choose (n + 1)
    rw [sum_range_succ, sum_range_succ'] at h
    rw [Nat.add_sub_cancel, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1]
    simp at h
    omega

/-- **A falling factorial of the lower index lowers both indices of a binomial coefficient:**
`(i)ₘ * C(A, i) = (A)ₘ * C(A - m, i - m)` for `m ≤ i`.

Both sides count the pairs consisting of an `i`-element subset of an `A`-element set and an
ordered `m`-tuple of distinct elements of that subset. The hypothesis `m ≤ i` is needed: for
`i < m` the left-hand side vanishes while the right-hand side need not. -/
theorem descFactorial_mul_choose {m i : ℕ} (hmi : m ≤ i) (A : ℕ) :
    i.descFactorial m * A.choose i = A.descFactorial m * (A - m).choose (i - m) := by
  first
  | rw [descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose,
      Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (i.choose m) (A.choose i), choose_mul hmi]

/-- **A rising factorial absorbed into a multiset coefficient:**
`(r + k)⁽ᵐ⁾ * multichoose r k = r⁽ᵐ⁾ * multichoose (r + m) k`, where `n⁽ᵐ⁾` is the rising
factorial `n.ascFactorial m` and `multichoose r k = C(r + k - 1, k)`.

No hypothesis is needed: for `r = 0` both sides vanish unless `k = m = 0`. -/
theorem add_ascFactorial_mul_multichoose (r m k : ℕ) :
    (r + k).ascFactorial m * r.multichoose k = r.ascFactorial m * (r + m).multichoose k := by
  first
    -- Multiplying by `k !` turns both sides into `r⁽ᵏ⁺ᵐ⁾`, since `k ! * multichoose r k = r⁽ᵏ⁾`.
  | apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k)
    calc k ! * ((r + k).ascFactorial m * r.multichoose k)
        = r.ascFactorial k * (r + k).ascFactorial m := by
          rw [ascFactorial_eq_factorial_mul_choose' r k, multichoose_eq]; ring
      _ = r.ascFactorial m * (r + m).ascFactorial k := by
        rw [ascFactorial_mul_ascFactorial, ascFactorial_mul_ascFactorial, Nat.add_comm k m]
      _ = k ! * (r.ascFactorial m * (r + m).multichoose k) := by
        rw [ascFactorial_eq_factorial_mul_choose' (r + m) k, multichoose_eq]; ring

/-- **Vandermonde's convolution weighted by a falling factorial of the summation index.**

Weighting the `i`th summand of `∑ i, C(A, i) * C(B, r - i) = C(A + B, r)` by `(i)ₘ` multiplies
the value by `(A)ₘ` and lowers both indices by `m`. After division by `C(A + B, r)`, the cases
`m = 1` and `m = 2` give the first two factorial moments of a hypergeometric law. -/
theorem sum_range_descFactorial_mul_choose_mul_choose {m r : ℕ} (hmr : m ≤ r) (A B : ℕ) :
    ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
      A.descFactorial m * (A + B - m).choose (r - m) := by
  first
    -- Only the indices `m ≤ i` contribute, since `(i)ₘ` vanishes below `m`.
  | have hsub : Ico m (r + 1) ⊆ range (r + 1) := fun i hi => mem_range.2 (mem_Ico.1 hi).2
    have hvanish : ∀ i ∈ range (r + 1), i ∉ Ico m (r + 1) →
        i.descFactorial m * (A.choose i * B.choose (r - i)) = 0 := by
      intro i hi hni
      simp only [mem_range] at hi
      simp only [mem_Ico, not_and, not_lt] at hni
      simp [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : i < m)]
    -- After shifting the index by `m`, the weight becomes the constant `(A)ₘ` and what is left
    -- is the unweighted convolution of `A - m` with `B`.
    have key : ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
        A.descFactorial m * (A - m + B).choose (r - m) := by
      have hrange : r + 1 - m = r - m + 1 := by omega
      rw [← Finset.sum_subset hsub hvanish, Finset.sum_Ico_eq_sum_range,
        hrange, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j ↦ (A - m).choose i * B.choose j) (r - m), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hri : r - (m + i) = r - m - i := by omega
      rw [hri, ← Nat.mul_assoc, Nat.descFactorial_mul_choose (Nat.le_add_right m i) A,
        Nat.add_sub_cancel_left, Nat.mul_assoc]
    -- The two ways of subtracting `m` agree unless `A < m`, where `(A)ₘ` is zero anyway.
    rcases le_or_gt m A with hmA | hmA
    · have hsub_add : A + B - m = A - m + B := by omega
      rwa [hsub_add]
    · rw [Nat.descFactorial_eq_zero_iff_lt.2 hmA] at key ⊢
      simpa using key

/-- **Choosing from two blocks at once.** Choosing an `i`-element block of `i + j` objects, then
`r` elements of that block and `s` elements of its complement, amounts to choosing the `r + s`
selected elements first, then which `r` of them lie in the block, and finally which `j - s` of the
unselected elements lie in the complement:
`C(i + j, i) * C(i, r) * C(j, s) = C(i + j, r + s) * C(r + s, r) * C(i + j - (r + s), j - s)`.

In particular `C(i + j, r + s)` divides `C(i + j, i) * C(i, r) * C(j, s)`. -/
theorem add_choose_mul_choose_mul_choose {i j r s : ℕ} (hr : r ≤ i) (hs : s ≤ j) :
    (i + j).choose i * i.choose r * j.choose s =
      (i + j).choose (r + s) * (r + s).choose r * (i + j - (r + s)).choose (j - s) := by
  first
  | rw [choose_mul hr, choose_symm_of_eq_add (by omega : i + j - r = i - r + j), Nat.mul_assoc,
      choose_mul hs, ← Nat.mul_assoc, choose_mul (Nat.le_add_right r s),
      Nat.add_sub_cancel_left, Nat.sub_sub]

/-- Membership in the set of `k ≤ n` with `p ∤ n choose k` only depends on the divisibility:
`n choose k = 0` is divisible by `p` for `k > n`. -/
theorem mem_filter_range_not_dvd_choose {p n k : ℕ} :
    k ∈ {k ∈ range (n + 1) | ¬p ∣ n.choose k} ↔ ¬p ∣ n.choose k := by
  first
  | refine ⟨fun h ↦ (mem_filter.mp h).2, fun h ↦ mem_filter.mpr ⟨mem_range.mpr ?_, h⟩⟩
    by_contra! hk
    exact h (by simp [choose_eq_zero_of_lt (lt_of_succ_le hk)])

end Nat
end -- closes the original EOF section from source line 57
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/Nat/Choose/Basic.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Signed principal subresultant coefficients

The signed principal coefficients used in real-root counting differ from the
Sylvester principal minors by a degree-dependent sign. `Polynomial.signedPsc`
records this normalization, including the leading coefficients above the smaller
formal bound. `Polynomial.signedPsc_def` gives the full Sylvester–Habicht sign
conversion; its two binomial terms and column-block sign simplify to
`(-1) ^ (m - j).choose 2`.

The degree-drop identities retain the formal bounds and include the smaller
terminal index. Mapping coefficients commutes with the signed coefficients
without a degree-preservation assumption at fixed bounds, and at the actual
degrees when the map preserves both degrees. The specialization formulas use
reducta taken before mapping, so they can be used with nullified leading terms.
These are the scalar coefficients for permanences-minus-variations formulas.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
  second edition, Chapter 4 (Sylvester–Habicht normalization).
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3
  (`subresultantE` uses the signed normalization).
-/

public section

namespace TauCeti

open _root_.Polynomial

variable {R S : Type*} [CommRing R]

/-- Signed principal subresultant coefficients at fixed bounds. Inside the
subresultant range they are signed Sylvester minors. Above that range the
coefficients at the two input bounds are retained, and all other entries vanish.
The equal-bound terminal entry is `1`, including for zero inputs. -/
noncomputable def _root_.Polynomial.signedPsc (p q : R[X]) (m n j : ℕ) : R :=
  if j ≤ min m n then (-1) ^ (m - j).choose 2 * psc p q m n j
  else if j = m then p.coeff m
  else if j = n then q.coeff n
  else 0

/-- Conversion from the Sylvester convention to the signed Sylvester–Habicht
normalization. The last exponent accounts for swapping the column blocks. -/
theorem _root_.Polynomial.signedPsc_def (p q : R[X]) (m n j : ℕ) :
    signedPsc p q m n j =
      if j ≤ min m n then
        (-1) ^ ((m + n - 2 * j).choose 2 + (n - j).choose 2 +
          (m - j) * (n - j)) * psc p q m n j
      else if j = m then p.coeff m
      else if j = n then q.coeff n
      else 0 := by
  first
  | by_cases hj : j ≤ min m n
    · have hsize : m + n - 2 * j = (m - j) + (n - j) := by omega
      have hexp : (m + n - 2 * j).choose 2 + (n - j).choose 2 +
          (m - j) * (n - j) =
          (m - j).choose 2 + 2 * ((n - j).choose 2 + (m - j) * (n - j)) := by
        rw [hsize, Nat.add_choose_two]
        omega
      simp [signedPsc, hj, hexp, pow_add, pow_mul]
    · simp [signedPsc, hj]

/-- Within the subresultant range only the left-bound gap determines the sign. -/
@[simp]
theorem _root_.Polynomial.signedPsc_of_le (p q : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p q m n j = (-1) ^ (m - j).choose 2 * psc p q m n j := by
  first
  | simp [signedPsc, hj]

/-- Above the smaller bound only the two input-bound coefficients are retained. -/
@[simp]
theorem _root_.Polynomial.signedPsc_of_lt (p q : R[X]) {m n j : ℕ}
    (hj : min m n < j) :
    signedPsc p q m n j =
      if j = m then p.coeff m else if j = n then q.coeff n else 0 := by
  first
  | simp [signedPsc, hj.not_ge]

/-- Coefficients beyond both formal bounds vanish. -/
@[simp]
theorem _root_.Polynomial.signedPsc_eq_zero_of_max_lt (p q : R[X]) {m n j : ℕ}
    (hj : max m n < j) : signedPsc p q m n j = 0 := by
  first
  | have hle : ¬ j ≤ min m n := by omega
    have hm : j ≠ m := by omega
    have hn : j ≠ n := by omega
    simp [signedPsc, hle, hm, hn]

/-- Signed coefficients specialize at fixed bounds, even when degrees drop. -/
@[simp]
theorem _root_.Polynomial.signedPsc_map_map [CommRing S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    signedPsc (p.map f) (q.map f) m n j = f (signedPsc p q m n j) := by
  first
  | simp [signedPsc, apply_ite f]

/-- At the actual degrees, signed coefficients commute with a coefficient map that preserves both
degrees, for instance one that does not kill the leading coefficients
(`Polynomial.natDegree_map_of_leadingCoeff_ne_zero`). When a degree drops,
`Polynomial.map_signedPsc_of_right_degree_drop` and `Polynomial.map_signedPsc_of_left_degree_drop`
apply instead. -/
theorem _root_.Polynomial.signedPsc_map_of_natDegree_eq [CommRing S] (f : R →+* S) {p q : R[X]}
    (hp : (p.map f).natDegree = p.natDegree) (hq : (q.map f).natDegree = q.natDegree) (j : ℕ) :
    signedPsc (p.map f) (q.map f) (p.map f).natDegree (q.map f).natDegree j =
      f (signedPsc p q p.natDegree q.natDegree j) := by
  first
  | rw [hp, hq, signedPsc_map_map]

/-- The smaller left bound has no sign correction; a larger left bound retains
the left input coefficient itself. -/
@[simp]
theorem _root_.Polynomial.signedPsc_left_bound (p q : R[X]) (m n : ℕ) :
    signedPsc p q m n m =
      if m ≤ n then p.coeff m ^ (n - m) else p.coeff m := by
  first
  | by_cases hmn : m ≤ n <;> simp [signedPsc, hmn]

/-- The smaller right bound retains the gap sign and the terminal power; a larger
right bound retains the right input coefficient itself. -/
@[simp]
theorem _root_.Polynomial.signedPsc_right_bound (p q : R[X]) (m n : ℕ) :
    signedPsc p q m n n =
      if n ≤ m then (-1) ^ (m - n).choose 2 * q.coeff n ^ (m - n)
      else q.coeff n := by
  first
  | by_cases hnm : n ≤ m
    · simp [signedPsc, hnm]
    · have hne : n ≠ m := by omega
      simp [signedPsc, hnm, hne]

/-- Swapping inputs changes both the normalization and the column-block order. -/
theorem _root_.Polynomial.signedPsc_comm (p q : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p q m n j =
      (-1) ^ ((m - j).choose 2 + (n - j).choose 2 + (m - j) * (n - j)) *
        signedPsc q p n m j := by
  first
  | rw [signedPsc_of_le p q hj, signedPsc_of_le q p (by omega), psc_comm]
    simp only [pow_add]
    rcases neg_one_pow_eq_or R ((n - j).choose 2) with h | h <;> rw [h] <;> ring

/-- Scaling the left input scales its signed minor by the number of its columns. -/
theorem _root_.Polynomial.signedPsc_C_mul_left (p q : R[X]) (r : R) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc (C r * p) q m n j = r ^ (n - j) * signedPsc p q m n j := by
  first
  | simp only [signedPsc_of_le _ _ hj, psc_C_mul_left]
    ring

/-- Scaling the right input scales its signed minor by the number of its columns. -/
theorem _root_.Polynomial.signedPsc_C_mul_right (p q : R[X]) (r : R) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p (C r * q) m n j = r ^ (m - j) * signedPsc p q m n j := by
  first
  | simp only [signedPsc_of_le _ _ hj, psc_C_mul_right]
    ring

/-- A zero left input makes an in-range signed minor vanish when its column
block is nonempty. This excludes the empty-determinant terminal case.
Not a simp lemma: `signedPsc_of_le` already rewrites its left-hand side. -/
theorem _root_.Polynomial.signedPsc_zero_left (q : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) (hjn : j < n) : signedPsc 0 q m n j = 0 := by
  first
  | have h := signedPsc_C_mul_left (0 : R[X]) q 0 hj
    simpa [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hjn))] using h

/-- A zero right input makes an in-range signed minor vanish when its column
block is nonempty. This excludes the empty-determinant terminal case.
Not a simp lemma: `signedPsc_of_le` already rewrites its left-hand side. -/
theorem _root_.Polynomial.signedPsc_zero_right (p : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) (hjm : j < m) : signedPsc p 0 m n j = 0 := by
  first
  | have h := signedPsc_C_mul_right p (0 : R[X]) 0 hj
    simpa [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hjm))] using h

/-- Lowering the right bound contributes a leading-coefficient power, with no
additional sign. The smaller terminal index is included. -/
theorem _root_.Polynomial.signedPsc_eq_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    signedPsc p q m N j = p.coeff m ^ (N - n) * signedPsc p q m n j := by
  first
  | rw [signedPsc_of_le p q (by omega), signedPsc_of_le p q (by omega),
      psc_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm hjn]
    ring

/-- Lowering the left bound contributes the normalization-gap sign as well as
the power of the coefficient at the right bound. Terminal indices are included. -/
theorem _root_.Polynomial.signedPsc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    signedPsc p q M n j =
      (-1) ^ ((M - m).choose 2 + (M - m) * (m + n - 2 * j)) *
        q.coeff n ^ (M - m) * signedPsc p q m n j := by
  first
  | have hgap : M - j = (M - m) + (m - j) := by omega
    have hsize : m + n - 2 * j = (m - j) + (n - j) := by omega
    rw [signedPsc_of_le p q (by omega), signedPsc_of_le p q (by omega),
      psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hjm hjn,
      hgap, Nat.add_choose_two, hsize]
    simp only [mul_add, pow_add]
    ring

/-- Simultaneous strict degree drops make every strict-index signed minor zero.
The equal-bound terminal determinant is deliberately excluded. -/
theorem _root_.Polynomial.signedPsc_eq_zero_of_natDegree_lt_bounds {p q : R[X]}
    {m n j : ℕ} (hm : p.natDegree < m) (hn : q.natDegree < n)
    (hj : j < min m n) : signedPsc p q m n j = 0 := by
  first
  | rw [signedPsc_of_le p q hj.le, psc_eq_zero_of_natDegree_lt_bounds hm hn hj, mul_zero]

/-- Specialization with a right degree drop. The right input is truncated before
mapping coefficients, and the fixed left bound is retained. -/
theorem _root_.Polynomial.map_signedPsc_of_right_degree_drop [CommRing S]
    (f : R →+* S) {p q : R[X]} {m n N j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (signedPsc p q m N j) = f (p.coeff m) ^ (N - n) *
      signedPsc (p.map f) ((q.reductum (n + 1)).map f) m n j := by
  first
  | have htrunc : (q.reductum (n + 1)).map f = q.map f := by
      rw [← reductum_map]
      exact reductum_eq_self (by omega)
    rw [htrunc, ← signedPsc_map_map,
      signedPsc_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm hjn, coeff_map]

/-- Specialization with a left degree drop, including its gap sign. Truncation
is performed over the original coefficient ring. -/
theorem _root_.Polynomial.map_signedPsc_of_left_degree_drop [CommRing S]
    (f : R →+* S) {p q : R[X]} {m M n j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (signedPsc p q M n j) =
      (-1) ^ ((M - m).choose 2 + (M - m) * (m + n - 2 * j)) *
        f (q.coeff n) ^ (M - m) *
          signedPsc ((p.reductum (m + 1)).map f) (q.map f) m n j := by
  first
  | have htrunc : (p.reductum (m + 1)).map f = p.map f := by
      rw [← reductum_map]
      exact reductum_eq_self (by omega)
    rw [htrunc, ← signedPsc_map_map,
      signedPsc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hjm hjn, coeff_map]

end TauCeti
end -- closes the original EOF section from source line 36
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Euclidean.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Euclidean reduction of subresultants

Adding a polynomial multiple of the right input to the left input preserves all
fixed-bound subresultant minors, provided the multiplier fits the difference of the
bounds. In particular, division with remainder preserves the minors before the bounds
are lowered. The principal-coefficient recurrence then records the power of the leading
coefficient and the sign introduced by lowering bounds and swapping inputs.

Reduction invariance holds over any commutative ring and at every index, including the
terminal principal index. Division with remainder requires a field; the divisor and
remainder may be zero. The principal-coefficient recurrences require the index to lie
at or below both the remainder bound and the divisor degree. Strictly between the
degree of the remainder and the degree of the divisor, the principal coefficients vanish.
The polynomial subresultants also satisfy an exact Euclidean recurrence, with explicit
endpoint multiples and vanishing inside degree gaps.
For the signed principal coefficients, one step of the signed remainder sequence
`p, q, -(p % q)` multiplies the coefficients at or below the remainder bound by a common
factor independent of the index.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
second edition, Chapters 4 and 8 (subresultants and polynomial remainder sequences).
-/

public section

namespace TauCeti

open _root_.Polynomial Matrix

variable {R : Type*} [CommRing R]

/-- Add shifted multiples of the `q`-columns (first block) to the `p`-columns (second block),
realising `X ^ l * p ↦ X ^ l * (p + a * q)`. -/
private noncomputable def reductionShear (a : R[X]) (u v : ℕ) :
    Matrix (Fin (u + v)) (Fin (u + v)) R :=
  (Matrix.fromBlocks (1 : Matrix (Fin u) (Fin u) R)
    (Matrix.of fun i l => (X ^ l.val * a).coeff i.val) 0
    (1 : Matrix (Fin v) (Fin v) R)).reindex finSumFinEquiv finSumFinEquiv

private theorem reductionShear_apply_castAdd (a : R[X]) (u v : ℕ)
    (i : Fin (u + v)) (l : Fin u) :
    reductionShear a u v i (Fin.castAdd v l) =
      i.addCases (fun i => if i = l then 1 else 0) (fun _ => 0) := by
  first
  | classical
    induction i using Fin.addCases <;> simp [reductionShear, Matrix.one_apply]

private theorem reductionShear_apply_natAdd (a : R[X]) (u v : ℕ)
    (i : Fin (u + v)) (l : Fin v) :
    reductionShear a u v i (Fin.natAdd u l) =
      i.addCases (fun i => (X ^ l.val * a).coeff i.val)
        (fun i => if i = l then 1 else 0) := by
  first
  | classical
    induction i using Fin.addCases <;> simp [reductionShear, Matrix.one_apply]

private theorem det_reductionShear (a : R[X]) (u v : ℕ) :
    (reductionShear a u v).det = 1 := by
  first
  | classical
    simp [reductionShear]

private theorem subresultantCoeffMatrix_add_mul {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (k : ℕ) :
    subresultantCoeffMatrix (p + a * q) q m n j k =
      subresultantCoeffMatrix p q m n j k * reductionShear a (m - j) (n - j) := by
  first
  | classical
    have hp' : (p + a * q).natDegree ≤ m :=
      natDegree_add_le_of_degree_le hp (natDegree_mul_le.trans (by omega))
    ext i l
    rw [subresultantCoeffMatrix_apply_eq_coeff hp' hq]
    have hmul := subresultantCoeffMatrix_mulVec hp hq j k
      (fun i => reductionShear a (m - j) (n - j) i l) i
    -- Matrix multiplication reads each column through the coefficient-map API.
    rw [Matrix.mul_apply']
    -- Identify the column dot product with mulVec to apply hmul without expanding the sum.
    change _ = (subresultantCoeffMatrix p q m n j k).mulVec
      (fun i => reductionShear a (m - j) (n - j) i l) i
    rw [hmul]
    induction l using Fin.addCases with
    | left l =>
        simp [reductionShear_apply_castAdd, ← Pi.zero_def]
    | right l =>
        have hdeg : (X ^ l.val * a).natDegree < m - j := by
          have hbound : (X ^ l.val * a).natDegree ≤ l.val + a.natDegree :=
            natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_pow_le l.val) _)
          omega
        have hpoly : ofFn (m - j) (fun i => (X ^ l.val * a).coeff i.val) =
            X ^ l.val * a := by
          have hvec : (fun i : Fin (m - j) => (X ^ l.val * a).coeff i.val) =
              toFn (m - j) (X ^ l.val * a) := by
            ext i
            rw [toFn_apply]
          rw [hvec]
          exact ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg
        simp only [Fin.addCases_right, reductionShear_apply_natAdd,
          Fin.addCases_left, ofFn_single, hpoly]
        rw [mul_add, mul_assoc, add_comm]

/-- Adding a multiple of the right input preserves every fixed-bound coefficient minor.
The multiplier's degree plus the right bound must not exceed the left bound. -/
theorem _root_.Polynomial.subresultantCoeff_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (k : ℕ) :
    subresultantCoeff (p + a * q) q m n j k = subresultantCoeff p q m n j k := by
  first
  | simp [subresultantCoeff_def, subresultantCoeffMatrix_add_mul hp hq ha,
      Matrix.det_mul, det_reductionShear]

/-- Polynomial reduction preserves principal coefficients, including the terminal index. -/
theorem _root_.Polynomial.psc_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) :
    psc (p + a * q) q m n j = psc p q m n j := by
  first
  | simpa only [subresultantCoeff_self] using
      subresultantCoeff_add_mul_left (j := j) hp hq ha j

/-- Polynomial reduction preserves the fixed-bound subresultant polynomial. -/
theorem _root_.Polynomial.subresultant_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) :
    subresultant (p + a * q) q m n j = subresultant p q m n j := by
  first
  | ext k
    simp only [coeff_subresultant, subresultantCoeff_add_mul_left hp hq ha]

section Field

variable {K : Type*} [Field K]

/-- Division with remainder preserves coefficient minors at the original left bound and
actual right degree. The left bound may be oversized, and the divisor and remainder may be zero. -/
theorem _root_.Polynomial.subresultantCoeff_mod_left {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m)
    (k : ℕ) :
    subresultantCoeff (p % q) q m q.natDegree j k =
      subresultantCoeff p q m q.natDegree j k := by
  first
  | by_cases hq : q = 0
    · subst q
      simp only [EuclideanDomain.mod_zero]
    by_cases hqm : q.natDegree ≤ m
    · have hquot : (p / q).natDegree ≤ p.natDegree - q.natDegree := by
        rw [div_def]
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [natDegree_divByMonic p (monic_mul_leadingCoeff_inv hq),
          natDegree_mul_leadingCoeff_inv q hq]
      have ha : (-(p / q)).natDegree + q.natDegree ≤ m := by
        rw [natDegree_neg]
        omega
      have heq : p + -(p / q) * q = p % q := by
        rw [EuclideanDomain.mod_eq_sub_mul_div]
        ring
      simpa only [heq] using subresultantCoeff_add_mul_left hp le_rfl ha k
    · have hmod : p % q = p :=
        (mod_eq_self_iff hq).mpr (degree_lt_degree (by omega))
      rw [hmod]

/-- Division with remainder preserves principal coefficients before the left bound drops. -/
theorem _root_.Polynomial.psc_mod_left {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) :
    psc (p % q) q m q.natDegree j = psc p q m q.natDegree j := by
  first
  | simpa only [subresultantCoeff_self] using subresultantCoeff_mod_left (j := j) hp j

/-- Division with remainder preserves the subresultant polynomial at fixed bounds. -/
theorem _root_.Polynomial.subresultant_mod_left {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) :
    subresultant (p % q) q m q.natDegree j = subresultant p q m q.natDegree j := by
  first
  | ext k
    simp only [coeff_subresultant, subresultantCoeff_mod_left hp]

/-- A Euclidean step for principal subresultant coefficients. Lowering the remainder's
bound from `m` to `r` contributes `q.leadingCoeff ^ (m - r)`; the displayed sign
comes from both the bound drop and the input swap. The smaller terminal index, zero
divisors, and zero remainders are included. -/
theorem _root_.Polynomial.psc_eq_sign_mul_leadingCoeff_pow_mul_psc_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m)
    (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    psc p q m q.natDegree j =
      (-1) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
        psc q (p % q) q.natDegree r j := by
  first
  | rw [← psc_mod_left hp,
      psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hr le_rfl hrm hjr hjq,
      psc_comm (p % q) q r q.natDegree j, coeff_natDegree]
    have hgap : m - j = (m - r) + (r - j) := by omega
    rw [hgap, add_mul, pow_add]
    ring

/-- The principal-coefficient recurrence for the signed remainder `-(p % q)`.
Negating the remainder adds the sign of its `q.natDegree - j` columns. -/
theorem _root_.Polynomial.psc_eq_sign_mul_leadingCoeff_pow_mul_psc_neg_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m)
    (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    psc p q m q.natDegree j =
      (-1) ^ ((m - j + 1) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
        psc q (-(p % q)) q.natDegree r j := by
  first
  | have hneg := psc_C_mul_right q (p % q) (-1) q.natDegree r j
    simp only [map_neg, map_one, neg_mul, one_mul] at hneg
    rw [hneg, psc_eq_sign_mul_leadingCoeff_pow_mul_psc_mod hp hr hrm hjr hjq,
      add_mul, one_mul, pow_add]
    have hsq : ((-1 : K) ^ (q.natDegree - j)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      simp
    linear_combination
      -((-1 : K) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
        psc q (p % q) q.natDegree r j) * hsq

/-- Principal coefficients vanish at the indices strictly between the degree of the
remainder `p % q` and the degree of `q`. The remainder may be zero. -/
theorem _root_.Polynomial.psc_eq_zero_of_natDegree_mod_lt {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hrj : (p % q).natDegree < j) (hjq : j < q.natDegree)
    (hjm : j ≤ m) :
    psc p q m q.natDegree j = 0 := by
  first
  | rw [← psc_mod_left hp,
      psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hrj.le le_rfl hjm le_rfl hjq.le,
      psc_left_bound, coeff_eq_zero_of_natDegree_lt hrj, zero_pow (by omega), mul_zero]

/-- One step of the signed remainder sequence multiplies the signed principal coefficients by a
common factor. For indices at most a bound `r` for the remainder, the signed coefficients of
`(p, q)` are those of `(q, -(p % q))` times `(-1) ^ (m - q.natDegree).choose 2 *
q.leadingCoeff ^ (m - r)`, which does not depend on the index. -/
theorem _root_.Polynomial.signedPsc_eq_mul_signedPsc_neg_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m) (hr : (p % q).natDegree ≤ r)
    (hrm : r ≤ m) (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    signedPsc p q m q.natDegree j =
      (-1) ^ (m - q.natDegree).choose 2 * q.leadingCoeff ^ (m - r) *
        signedPsc q (-(p % q)) q.natDegree r j := by
  first
  | rw [signedPsc_of_le p q (le_min (hjq.trans hqm) hjq), signedPsc_of_le _ _ (le_min hjq hjr),
      psc_eq_sign_mul_leadingCoeff_pow_mul_psc_neg_mod hp hr hrm hjr hjq]
    obtain ⟨t, ht⟩ := Nat.even_mul_succ_self (q.natDegree - j)
    have hmj : m - j = (m - q.natDegree) + (q.natDegree - j) := by omega
    have hexp : (m - j).choose 2 + (m - j + 1) * (q.natDegree - j) =
        (m - q.natDegree).choose 2 + (q.natDegree - j).choose 2 +
          2 * ((m - q.natDegree) * (q.natDegree - j) + t) := by
      rw [hmj, Nat.add_choose_two]
      nlinarith [ht]
    have hsign : (-1 : K) ^ (m - j).choose 2 * (-1) ^ ((m - j + 1) * (q.natDegree - j)) =
        (-1) ^ (m - q.natDegree).choose 2 * (-1) ^ (q.natDegree - j).choose 2 := by
      rw [← pow_add, hexp, pow_add, pow_add, pow_mul]
      simp
    linear_combination (q.leadingCoeff ^ (m - r) * psc q (-(p % q)) q.natDegree r j) * hsign

/-- The signed principal coefficients vanish at the indices strictly between the degree of the
remainder `p % q` and the degree of `q`. -/
theorem _root_.Polynomial.signedPsc_eq_zero_of_natDegree_mod_lt {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hrj : (p % q).natDegree < j) (hjq : j < q.natDegree)
    (hjm : j ≤ m) :
    signedPsc p q m q.natDegree j = 0 := by
  first
  | rw [signedPsc_of_le p q (le_min hjm hjq.le), psc_eq_zero_of_natDegree_mod_lt hp hrj hjq hjm,
      mul_zero]

/-! ### One Euclidean step -/

/-- A Euclidean step for subresultant polynomials. Below the remainder bound `r`, the
subresultant of `(p, q)` is that of `(q, p % q)` times `± q.leadingCoeff ^ (m - r)`. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_subresultant_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hj : j < min r q.natDegree) :
    subresultant p q m q.natDegree j =
      C ((-1) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r)) *
        subresultant q (p % q) q.natDegree r j := by
  first
  | rw [← subresultant_mod_left hp,
      subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop hr le_rfl hrm hj,
      subresultant_comm (p % q) q r q.natDegree j, coeff_natDegree, ← mul_assoc, ← C_mul]
    congr 2
    have hmj : m - j = (m - r) + (r - j) := by omega
    rw [hmj, add_mul, pow_add]
    ring

/-- The Euclidean step for the signed remainder `-(p % q)`, the next entry of the signed
remainder sequence. Negating the remainder adds the sign of its `q.natDegree - j` columns. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_subresultant_neg_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hj : j < min r q.natDegree) :
    subresultant p q m q.natDegree j =
      C ((-1) ^ ((m - j + 1) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r)) *
        subresultant q (-(p % q)) q.natDegree r j := by
  first
  | have hneg : -(p % q) = C (-1) * (p % q) := by simp
    have hsq : ((-1 : K) ^ (q.natDegree - j)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [hneg, subresultant_C_mul_right, subresultant_eq_C_mul_subresultant_mod hp hr hrm hj,
      ← mul_assoc, ← C_mul, add_mul, one_mul, pow_add]
    congr 2
    linear_combination -((-1 : K) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r)) * hsq

/-! ### The degree gap -/

/-- From the degree of the remainder up to `q.natDegree - 1`, the subresultant of `(p, q)` is an
explicit multiple of the remainder `p % q`. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_mod {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).natDegree ≤ j) (hjq : j < q.natDegree)
    (hjm : j < m) :
    subresultant p q m q.natDegree j =
      C ((-1) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - j) *
        (p % q).coeff j ^ (q.natDegree - j - 1)) * (p % q) := by
  first
  | rw [← subresultant_mod_left hp, subresultant_left_bound_of_degree_drop hr le_rfl hjq hjm,
      coeff_natDegree]

/-- The subresultant at index `q.natDegree - 1` is `(-q.leadingCoeff) ^ (m + 1 - q.natDegree)`
times the remainder `p % q`. -/
theorem _root_.Polynomial.subresultant_natDegree_sub_one {p q : K[X]} {m : ℕ}
    (hp : p.natDegree ≤ m) (hq : 0 < q.natDegree) (hqm : q.natDegree ≤ m) :
    subresultant p q m q.natDegree (q.natDegree - 1) =
      C ((-q.leadingCoeff) ^ (m + 1 - q.natDegree)) * (p % q) := by
  first
  | have hm : m - (q.natDegree - 1) = m + 1 - q.natDegree := by omega
    have hq1 : q.natDegree - (q.natDegree - 1) = 1 := by omega
    rw [subresultant_eq_C_mul_mod hp (Nat.le_sub_one_of_lt (natDegree_mod_lt p hq.ne')) (by omega)
      (by omega), hm, hq1, Nat.sub_self, pow_zero, mul_one, mul_one, neg_pow q.leadingCoeff]

/-- Strictly inside the degree gap, between the degree of the remainder and
`q.natDegree - 1`, the subresultants of `(p, q)` vanish. This includes every index below
`q.natDegree - 1` when `q` divides `p`. -/
theorem _root_.Polynomial.subresultant_eq_zero_of_degree_mod_lt {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).degree < j) (hjq : j + 1 < q.natDegree) :
    subresultant p q m q.natDegree j = 0 := by
  first
  | by_cases hjm : j < m
    · rw [subresultant_eq_C_mul_mod hp (natDegree_le_of_degree_le hr.le) (by omega) hjm,
        coeff_eq_zero_of_degree_lt hr, zero_pow (by omega), mul_zero, C_0, zero_mul]
    · exact subresultant_eq_zero_of_min_le _ _ _ _ _ (by omega)

end Field

end TauCeti
end -- closes the original EOF section from source line 41
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/Euclidean.lean -/

/- BEGIN SOURCE: TauCeti/Data/List/Range.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Mapping along a reversed range

Lists of the form `[f (b - 1), …, f 0]`, that is `(List.range b).reverse.map f`, record
coefficient sequences from the top index down. This file peels off the top entry and collapses a
run of vanishing entries at the top into a block of zeros.

## Main results

* `List.map_reverse_range_succ`: the list `[f k, …, f 0]` begins with `f k`.
* `List.map_reverse_range_eq_replicate_append`: if `f` vanishes on `[a, b)`, then
  `[f (b - 1), …, f 0]` is `b - a` zeros followed by `[f (a - 1), …, f 0]`.
-/

public section

namespace TauCeti

/-- The list `[f k, …, f 0]` begins with `f k`. -/
theorem _root_.List.map_reverse_range_succ {α : Type*} (f : ℕ → α) (k : ℕ) :
    (List.range (k + 1)).reverse.map f = f k :: (List.range k).reverse.map f := by
  first
  | simp [List.range_succ]

/-- Mapping a function along the reversed range `[b - 1, …, 0]`, where it vanishes on
`[a, b)`, gives `b - a` zeros followed by the map along `[a - 1, …, 0]`. -/
theorem _root_.List.map_reverse_range_eq_replicate_append {α : Type*} [Zero α] (f : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) (h : ∀ j, a ≤ j → j < b → f j = 0) :
    (List.range b).reverse.map f = List.replicate (b - a) 0 ++ (List.range a).reverse.map f := by
  first
  | induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have hlen : b + 1 - a = (b - a) + 1 := by omega
      rw [List.map_reverse_range_succ, h b hab (by omega), ih fun j h1 h2 => h j h1 (by omega),
        hlen, List.replicate_succ, List.cons_append]

end TauCeti
end -- closes the original EOF section from source line 24
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Data/List/Range.lean -/

/- BEGIN SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/CauchyIndex.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-! # Cauchy indices from signed subresultant coefficients

Let `p` and `q` be polynomials over an ordered real closed field with
`q.natDegree < p.natDegree = m`, and let `s_j = signedPsc p q m q.natDegree j` be their signed
principal subresultant coefficients at the actual degrees. The permanences minus variations of
the list `[s_m, …, s_0]` is the Cauchy index of `q / p` on the whole line. Applied to suitable
pairs, this computes roots and Tarski queries from signs of principal subresultant
coefficients, which are polynomials in the coefficients of the pair: the number of distinct
roots of `p` uses the pair `(p, derivative p)`, and the Tarski query of `q` at the roots of `p`
uses the pair `(p, derivative p * q % p)`.

The proof follows the signed remainder sequence `p, q, -(p % q), …`. One Euclidean step
multiplies the signed coefficients of index at most `(p % q).natDegree` by a common nonzero
constant (`Polynomial.signedPsc_eq_mul_signedPsc_neg_mod`), and the coefficients of larger
index below `q.natDegree` vanish (`Polynomial.signedPsc_eq_zero_of_natDegree_mod_lt`). On the
Cauchy-index side, the same step changes the whole-line index by the contribution of the
leading pair.

## Main declarations

* `Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc`: the Cauchy index of
  `q / p` is permanences minus variations of the signed principal coefficients.
* `Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc_mod`: the same for an
  arbitrary numerator, reduced modulo `p`.
* `Polynomial.tarskiQuery_eq_permanencesMinusVariations_signedPsc`,
  `Polynomial.card_roots_toFinset_eq_permanencesMinusVariations_signedPsc`: Tarski queries and
  the number of distinct roots from principal coefficients.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 4 (signed subresultants and the Cauchy index).
-/

public section

namespace TauCeti

open _root_.Polynomial Set SignType

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The leading pair `[s_m, 0, …, 0, s_n]` contributes the sign of `p * q` at infinity when
the degrees have opposite parities. -/
private theorem permanencesMinusVariations_signedPsc_eq_add {p q : K[X]} (hq : q ≠ 0)
    (h : q.natDegree < p.natDegree) :
    ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations =
      (if Odd (p.natDegree + q.natDegree) then
        (sign p.leadingCoeff : ℤ) * sign q.leadingCoeff else 0) +
      ((List.range (q.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations := by
  first
  | set m := p.natDegree with hm
    set n := q.natDegree with hn
    set s := signedPsc p q m n
    have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
    have hpn : ¬ p.natDegree ≤ n := by omega
    have hqm : q.natDegree ≤ m := by omega
    have hsm : s m = p.leadingCoeff := by simp [s, hm, hpn]
    have hsn : s n = (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - n) := by simp [s, hn, hqm]
    have hsn0 : s n ≠ 0 := by simp [hsn, hq']
    rw [List.map_reverse_range_succ,
      List.map_reverse_range_eq_replicate_append s (a := n + 1) (b := m) h fun j hj hjm => by
        have hmin : min m n < j := by omega
        have hjn : j ≠ n := by omega
        simp [s, signedPsc_of_lt p q hmin, hjm.ne, hjn],
      List.map_reverse_range_succ, List.permanencesMinusVariations_cons_replicate_zero_append hsn0]
    congr 1
    obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
    have hk' : m - (n + 1) = k := by omega
    have hodd : Odd (m + n) ↔ Even k := by
      simp only [Nat.odd_iff, Nat.even_iff]
      omega
    rw [hk']
    by_cases hke : Even k
    · simp only [hke, hodd.2 hke, ↓reduceIte, hsm, hsn, hk]
      have hc : (k + 1).choose 2 = k.choose 2 + k := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      simp only [sign_mul, sign_pow, Left.sign_neg, sign_one,
        SignType.pow_even _ hke (sign_ne_zero.mpr hq'),
        hc, pow_add, SignType.coe_mul, SignType.coe_pow, SignType.coe_neg, SignType.coe_one]
      rw [hke.neg_one_pow]
      have h2 : ((-1 : ℤ) ^ k.choose 2) * (-1) ^ k.choose 2 = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      linear_combination (sign p.leadingCoeff * sign q.leadingCoeff : ℤ) * h2
    · simp only [hke, mt hodd.1 hke, ↓reduceIte]

/-- After the leading entry, the signed coefficients of `(p, q)` and of `(q, -(p % q))` have the
same permanences minus variations. -/
private theorem permanencesMinusVariations_signedPsc_neg_mod {p q : K[X]}
    (h : q.natDegree < p.natDegree) (hn : q.natDegree ≠ 0) :
    ((List.range (q.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations =
      ((List.range (q.natDegree + 1)).reverse.map (signedPsc q (-(p % q)) q.natDegree
        (-(p % q)).natDegree)).permanencesMinusVariations := by
  first
  | set m := p.natDegree
    set n := q.natDegree with hn'
    set ρ := (-(p % q)).natDegree with hρ'
    have hq : q ≠ 0 := by rintro rfl; simp [n] at hn
    have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
    have hρr : (p % q).natDegree = ρ := (natDegree_neg _).symm
    have hρ : ρ < n := hρr ▸ natDegree_mod_lt p hn
    set s := signedPsc p q m n
    set t := signedPsc q (-(p % q)) n ρ
    set c : K := (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - ρ) with hcdef
    have hc : c ≠ 0 := by simp [c, hq']
    -- Below the remainder degree the two coefficient lists are proportional.
    have hst : (List.range (ρ + 1)).reverse.map s =
        ((List.range (ρ + 1)).reverse.map t).map (c * ·) := by
      simp only [List.map_map]
      refine List.map_congr_left fun j hj => ?_
      have hj : j ≤ ρ := by
        rw [List.mem_reverse, List.mem_range] at hj
        omega
      exact signedPsc_eq_mul_signedPsc_neg_mod le_rfl h.le hρr.le (by omega) hj (by omega)
    have hqm : q.natDegree ≤ m := by omega
    have hqρ : ¬ q.natDegree ≤ ρ := by omega
    have hsn : s n = (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - n) := by simp [s, hn', hqm]
    have htn : t n = q.leadingCoeff := by simp [t, hn', hqρ]
    have htρ : t ρ = (-1) ^ (n - ρ).choose 2 * (-(p % q)).coeff ρ ^ (n - ρ) := by
      simp [t, hρ.le]
    rw [List.map_reverse_range_succ s n,
      List.map_reverse_range_eq_replicate_append s (a := ρ + 1) (b := n) hρ fun j hj hjn =>
        signedPsc_eq_zero_of_natDegree_mod_lt le_rfl (by omega) hjn (by omega), hst,
      List.map_reverse_range_succ t n,
      List.map_reverse_range_eq_replicate_append t (a := ρ + 1) (b := n) hρ fun j hj hjn => by
        have hmin : min n ρ < j := by omega
        have hjρ : j ≠ ρ := by omega
        simp [t, signedPsc_of_lt q _ hmin, hjn.ne, hjρ],
      htn, List.map_reverse_range_succ t ρ]
    by_cases hr : p % q = 0
    · -- A zero remainder leaves no nonzero entry after the first one.
      have hρ0 : ρ = 0 := by simp [ρ, hr]
      have hnρ : n - ρ ≠ 0 := by omega
      have ht0 : t ρ = 0 := by simp [htρ, hr, hnρ]
      rw [hρ0] at ht0
      simp [ht0, hρ0, ← List.replicate_succ']
    · have hlc : (-(p % q)).coeff ρ ≠ 0 := by
        rw [hρ', coeff_natDegree]
        simpa using hr
      have htρ0 : t ρ ≠ 0 := by
        rw [htρ]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hlc)
      rw [List.map_cons, List.permanencesMinusVariations_cons_replicate_zero_append
          (mul_ne_zero hc htρ0), ← List.map_cons, List.permanencesMinusVariations_map_mul_left hc,
        List.permanencesMinusVariations_cons_replicate_zero_append htρ0]
      congr 1
      split_ifs with hk
      · -- Across an even gap, `s n * c` has the sign of `q.leadingCoeff ^ (odd)`.
        have hodd : Odd ((m - n) + (m - ρ)) := by
          obtain ⟨i, hi⟩ := hk
          exact ⟨m - n + i, by omega⟩
        have h1 : ((-1 : K) ^ (m - n).choose 2) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul]
          simp
        have hprod : (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - n) *
            ((-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - ρ)) =
              q.leadingCoeff ^ ((m - n) + (m - ρ)) := by
          linear_combination (q.leadingCoeff ^ (m - n) * q.leadingCoeff ^ (m - ρ)) * h1
        have key : (sign (s n) : ℤ) * sign c = sign q.leadingCoeff := by
          rw [← SignType.coe_mul, ← sign_mul, hsn, hcdef, hprod]
          simp [sign_pow, SignType.pow_odd _ hodd]
        simp only [sign_mul, SignType.coe_mul]
        linear_combination ((-1) ^ (n - (ρ + 1)).choose 2 * (sign (t ρ) : ℤ)) * key
      · rfl

end Ordered

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Cauchy index by signed subresultants.** For `q.natDegree < p.natDegree = m`, the
whole-line Cauchy index of `q / p` is the permanences minus variations of the signed principal
subresultant coefficients `[s_m, …, s_0]` of `p` and `q` at their actual degrees. The numerator
may be zero, and `p` and `q` may have common factors and multiple roots. -/
theorem _root_.Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc {p q : R[X]}
    (h : q.natDegree < p.natDegree) :
    cauchyIndex p q univ =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations := by
  first
  | induction hn : q.natDegree using Nat.strong_induction_on generalizing p q with
    | _ n ih =>
    subst hn
    by_cases hq : q = 0
    · -- Only the leading entry `p.leadingCoeff` is nonzero.
      subst hq
      rw [cauchyIndex_zero_right, List.map_reverse_range_succ,
        List.map_reverse_range_eq_replicate_append _ (Nat.zero_le _) fun j _ hj => ?_]
      · simp
      · rcases eq_or_ne j 0 with rfl | hj0
        · exact signedPsc_zero_right p (by simp) (by simpa using h)
        · rw [signedPsc_of_lt _ _ (by simp only [natDegree_zero]; omega)]
          simp [hj.ne, hj0]
    have hp : p ≠ 0 := by rintro rfl; simp at h
    rw [cauchyIndex_univ_eq_add_cauchyIndex_neg_mod hp hq,
      permanencesMinusVariations_signedPsc_eq_add hq h]
    congr 1
    by_cases hn : q.natDegree = 0
    · -- A constant `q` has no poles, and the remaining list is a singleton.
      have hq0 : cauchyIndex q (-(p % q)) univ = 0 := by
        rw [eq_C_of_natDegree_eq_zero hn, cauchyIndex_C]
      rw [hq0, hn]
      simp
    rw [permanencesMinusVariations_signedPsc_neg_mod h hn]
    have hr : (-(p % q)).natDegree < q.natDegree := by
      rw [natDegree_neg]
      exact natDegree_mod_lt p hn
    exact ih _ hr hr rfl

/-- **Cauchy index by signed subresultants, general numerator.** Reducing `q` modulo `p` does not
change the Cauchy index of `q / p`, so it is the permanences minus variations of the signed
principal subresultant coefficients of `p` and `q % p`. For constant `p` both sides vanish. -/
theorem _root_.Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc_mod
    (p q : R[X]) :
    cauchyIndex p q univ =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p (q % p) p.natDegree (q % p).natDegree)).permanencesMinusVariations := by
  first
  | rcases eq_or_ne p.natDegree 0 with hp | hp
    · rw [eq_C_of_natDegree_eq_zero hp, cauchyIndex_C, natDegree_C]
      simp
    rw [← cauchyIndex_mod]
    exact cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc (natDegree_mod_lt q hp)

/-- The Tarski query of `q` at the roots of `p` is the permanences minus variations of the signed
principal subresultant coefficients of `p` and `p' * q % p`. -/
theorem _root_.Polynomial.tarskiQuery_eq_permanencesMinusVariations_signedPsc (p q : R[X]) :
    tarskiQuery p q =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p (derivative p * q % p) p.natDegree
          (derivative p * q % p).natDegree)).permanencesMinusVariations := by
  first
  | rw [← cauchyIndex_derivative_mul_univ,
      cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc_mod]

/-- The number of distinct roots of `p` is the permanences minus variations of the signed
principal subresultant coefficients of `p` and its derivative. -/
theorem _root_.Polynomial.card_roots_toFinset_eq_permanencesMinusVariations_signedPsc
    (p : R[X]) :
    (p.roots.toFinset.card : ℤ) =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p (derivative p) p.natDegree
          (derivative p).natDegree)).permanencesMinusVariations := by
  first
  | classical
    rcases eq_or_ne p.natDegree 0 with hp | hp
    · rw [eq_C_of_natDegree_eq_zero hp]
      simp
    rw [← cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc
      (natDegree_derivative_lt hp), cauchyIndex_derivative]
    simp

end TauCeti
end -- closes the original EOF section from source line 48
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/RingTheory/Polynomial/Subresultant/CauchyIndex.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/RootCount.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Root counts of polynomial families are semialgebraic

A polynomial `P : (MvPolynomial σ R)[X]` is a family of univariate polynomials
`P.map (MvPolynomial.eval x)` parametrized by `x : σ → R`. This file shows that the number of
distinct roots of the specialized polynomial, and the number of its distinct roots below a point
`t = T(x)` given by a polynomial `T`, are described by finitely many polynomial sign conditions on
the parameters. So the sets of parameters with a prescribed count are semialgebraic. In the
cylinder coordinates of `TauCeti.cylinder`, this describes, without any projection, the loci of a
family over `R ^ n` where the distinguished coordinate is a root, respectively not a root, with a
prescribed number of roots below it. Over base points where the family does not specialize to zero,
these are the graph of the `i`-th distinct root and the `j`-th sector, where the sectors are counted
from below and include the two unbounded outer sectors.

The specialized degree is described by the vanishing of the coefficients of `P`. Where it equals
`d`, the specialization is the specialization of the reductum of `P` below `d + 1`, and the formal
bounds `d` and `d - 1` of this reductum and its derivative are the actual degrees there. Their
signed principal subresultant coefficients are polynomials in the parameters, and the number of
distinct roots is the permanences minus variations of their values
(`Polynomial.card_roots_toFinset_eq_permanencesMinusVariations_signedPsc`). Roots below `t` are
counted as roots of `p.comp (C t - X ^ 2)` (`Polynomial.card_roots_toFinset_comp_C_sub_X_sq`),
whose coefficients are again polynomials in the parameters.

Zero specializations, whose zero set is the whole line, are separated explicitly. By convention
their `Polynomial.roots` is empty, so they lie in the sets with count zero.

## Main declarations

* `TauCeti.isSemialgebraic_setOf_map_eval_eq_zero`,
  `TauCeti.isSemialgebraic_setOf_natDegree_map_eval_eq`: the parameters with a zero specialization,
  and with a prescribed specialized degree.
* `TauCeti.isSemialgebraic_setOf_card_roots_map_eval`: the parameters whose specialization has a
  prescribed number of distinct roots.
* `TauCeti.isSemialgebraic_setOf_card_roots_map_eval_lt`: the parameters whose specialization has a
  prescribed number of distinct roots below `T(x)`.
* `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_eq`: equality of a polynomial
  threshold with the distinct root of a prescribed zero-based index.
* `TauCeti.isSemialgebraic_setOf_isRoot_card_roots_lt`,
  `TauCeti.isSemialgebraic_setOf_not_isRoot_card_roots_lt`: the root locus with `i` roots below
  and the non-root locus with `j` roots below of a family over `R ^ n`, as subsets of
  `R ^ (n + 1)`. Over nonzero fibers these are the graph of the `i`-th root and the `j`-th sector.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapters 4 and 10 (root counting by signed subresultants and uniform sign
descriptions).
-/

public section

open Polynomial Set

namespace TauCeti

section CommRing

variable {σ R : Type*} [CommRing R] [LinearOrder R]

/-- The parameters at which a polynomial family specializes to zero form a semialgebraic set. -/
theorem isSemialgebraic_setOf_map_eval_eq_zero (P : (MvPolynomial σ R)[X]) :
    IsSemialgebraic {x : σ → R | P.map (MvPolynomial.eval x) = 0} := by
  first
  | simpa [Polynomial.ext_iff] using isSemialgebraic_setOf_forall_coeff_eq_zero P univ

/-- The parameters at which the specialization of a polynomial family has degree at most `d` form
a semialgebraic set. -/
theorem isSemialgebraic_setOf_natDegree_map_eval_le (P : (MvPolynomial σ R)[X]) (d : ℕ) :
    IsSemialgebraic {x : σ → R | (P.map (MvPolynomial.eval x)).natDegree ≤ d} := by
  first
  | simpa [natDegree_le_iff_coeff_eq_zero] using isSemialgebraic_setOf_forall_coeff_eq_zero P (Ioi d)

/-- The parameters at which the specialization of a polynomial family has degree exactly `d` form
a semialgebraic set. The zero specializations have degree `0`. -/
theorem isSemialgebraic_setOf_natDegree_map_eval_eq (P : (MvPolynomial σ R)[X]) (d : ℕ) :
    IsSemialgebraic {x : σ → R | (P.map (MvPolynomial.eval x)).natDegree = d} := by
  first
  | cases d with
    | zero => simpa using isSemialgebraic_setOf_natDegree_map_eval_le P 0
    | succ d =>
      convert (isSemialgebraic_setOf_natDegree_map_eval_le P (d + 1)).sdiff
        (isSemialgebraic_setOf_natDegree_map_eval_le P d) using 1
      ext x
      simp only [mem_ofPred_eq, mem_sdiff]
      omega

end CommRing

section RealClosed

variable {σ R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Uniform root count.** The parameters at which the specialization of a polynomial family has
exactly `k` distinct roots form a semialgebraic set. A zero specialization has no roots in
`Polynomial.roots`, so it counts towards `k = 0`; the zero specializations themselves form the
semialgebraic set of `TauCeti.isSemialgebraic_setOf_map_eval_eq_zero`. -/
theorem isSemialgebraic_setOf_card_roots_map_eval (P : (MvPolynomial σ R)[X]) (k : ℕ) :
    IsSemialgebraic {x : σ → R | (P.map (MvPolynomial.eval x)).roots.toFinset.card = k} := by
  first
    -- The signed principal subresultant coefficients of the reductum below `d + 1` and its
    -- derivative, at the formal degrees `d` and `d - 1`.
  | set s : ℕ → ℕ → MvPolynomial σ R := fun d =>
      signedPsc (P.reductum (d + 1)) (derivative (P.reductum (d + 1))) d (d - 1)
    have hcount (x : σ → R) {d : ℕ} (hd : (P.map (MvPolynomial.eval x)).natDegree = d) :
        ((P.map (MvPolynomial.eval x)).roots.toFinset.card : ℤ) =
          (((List.range (d + 1)).reverse.map (s d)).map
            (MvPolynomial.eval x)).permanencesMinusVariations := by
      rw [card_roots_toFinset_eq_permanencesMinusVariations_signedPsc, natDegree_derivative, hd]
      have hP : P.map (MvPolynomial.eval x) = (P.reductum (d + 1)).map (MvPolynomial.eval x) := by
        rw [← hd, map_reductum_natDegree_map_add_one]
      have hs : signedPsc ((P.reductum (d + 1)).map (MvPolynomial.eval x))
          ((derivative (P.reductum (d + 1))).map (MvPolynomial.eval x)) d (d - 1) =
            fun j => MvPolynomial.eval x (s d j) :=
        funext fun j => signedPsc_map_map _ _ _ _ _ _
      rw [hP, derivative_map, hs, List.map_map, Function.comp_def]
    have : {x : σ → R | (P.map (MvPolynomial.eval x)).roots.toFinset.card = k} =
        ⋃ d ∈ Iic P.natDegree, {x | (P.map (MvPolynomial.eval x)).natDegree = d} ∩
          {x | (((List.range (d + 1)).reverse.map (s d)).map
            (MvPolynomial.eval x)).permanencesMinusVariations = k} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_Iic, exists_prop]
      constructor
      · intro h
        refine ⟨_, natDegree_map_le, rfl, ?_⟩
        rw [← hcount x rfl, h]
      · rintro ⟨d, -, hd, h⟩
        exact_mod_cast (hcount x hd).trans h
    rw [this]
    exact .biUnion (finite_Iic _) fun d _ => (isSemialgebraic_setOf_natDegree_map_eval_eq P d).inter
      (isSemialgebraic_setOf_permanencesMinusVariations_eval _ _)

/-- **Uniform count of the roots below a point.** For polynomials `P` and `T`, the parameters `x`
at which the specialization of `P` has exactly `k` distinct roots below `T(x)` form a semialgebraic
set. A zero specialization has no roots in `Polynomial.roots`, so it counts towards `k = 0`. -/
theorem isSemialgebraic_setOf_card_roots_map_eval_lt (P : (MvPolynomial σ R)[X])
    (T : MvPolynomial σ R) (k : ℕ) :
    IsSemialgebraic
      {x : σ → R | {r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset |
        r < MvPolynomial.eval x T}.card = k} := by
  first
  | classical
    -- The roots of the specialization below `T(x)` are counted by the roots of the specialization
    -- of `P.comp (C T - X ^ 2)` and by whether `T(x)` is itself a root.
    set Q := P.comp (C T - X ^ 2)
    have hQ (x : σ → R) : Q.map (MvPolynomial.eval x) =
        (P.map (MvPolynomial.eval x)).comp (C (MvPolynomial.eval x T) - X ^ 2) := by
      simp [Q, Polynomial.map_comp]
    -- Zero specializations count towards `k = 0` only; elsewhere the count is read off from the
    -- root count of the specialization of `Q` and whether `T(x)` is a root.
    have : {x : σ → R | {r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset |
          r < MvPolynomial.eval x T}.card = k} =
        {x | P.map (MvPolynomial.eval x) = 0 ∧ k = 0} ∪
          {x | P.map (MvPolynomial.eval x) = 0}ᶜ ∩
            ({x | MvPolynomial.eval x (P.eval T) = 0} ∩
                {x | (Q.map (MvPolynomial.eval x)).roots.toFinset.card = 2 * k + 1} ∪
              {x | MvPolynomial.eval x (P.eval T) ≠ 0} ∩
                {x | (Q.map (MvPolynomial.eval x)).roots.toFinset.card = 2 * k}) := by
      ext x
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      by_cases h0 : P.map (MvPolynomial.eval x) = 0
      · simp [h0, eq_comm]
      have hroot : (P.map (MvPolynomial.eval x)).IsRoot (MvPolynomial.eval x T) ↔
          MvPolynomial.eval x (P.eval T) = 0 := by
        rw [IsRoot.def, eval_map_apply]
      rw [hQ, card_roots_toFinset_comp_C_sub_X_sq h0]
      by_cases hr : MvPolynomial.eval x (P.eval T) = 0
      · simp only [h0, hr, hroot.mpr hr, ↓reduceIte, false_and, false_or, not_false_eq_true,
          true_and, ne_eq, not_true_eq_false, or_false]
        omega
      · simp only [h0, hr, mt hroot.mp hr, ↓reduceIte, false_and, false_or, not_false_eq_true,
          true_and, ne_eq]
        omega
    have hZ := isSemialgebraic_setOf_map_eval_eq_zero P
    rw [this]
    refine .union ?_ (hZ.compl.inter
      (((isSemialgebraic_eval_eq_zero _).inter (isSemialgebraic_setOf_card_roots_map_eval Q _)).union
        ((isSemialgebraic_eval_ne_zero _).inter (isSemialgebraic_setOf_card_roots_map_eval Q _))))
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using hZ
    · simp [hk]

/-- **Equality with the `i`-th distinct root.** For polynomials `P` and `T`, the parameters `x` at
which `P.map (MvPolynomial.eval x)` has an `i`-th distinct root `r` (with `i` distinct roots
strictly below `r`, so `i = 0` is the smallest root) and `MvPolynomial.eval x T = r` form a
semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_eq
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (i : ℕ) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i ∧
        MvPolynomial.eval x T = r} := by
  first
  | convert (isSemialgebraic_setOf_map_eval_eq_zero P).compl.inter
      ((isSemialgebraic_eval_eq_zero (P.eval T)).inter
        (isSemialgebraic_setOf_card_roots_map_eval_lt P T i)) using 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, ← eval_map_apply,
      Multiset.mem_toFinset, Polynomial.mem_roots', IsRoot.def]
    exact ⟨fun ⟨r, ⟨hp, hr⟩, hcard, h⟩ => h ▸ ⟨hp, hr, hcard⟩,
      fun ⟨hp, hr, hcard⟩ => ⟨_, ⟨hp, hr⟩, hcard, rfl⟩⟩

/-! ### Roots and sectors in cylinder coordinates

A family `P : (MvPolynomial (Fin n) R)[X]` over `R ^ n` has its root graphs and sectors in
`R ^ (n + 1)`, with the distinguished coordinate `0` as for `TauCeti.cylinder`. Over a base point
where the specialization at `Fin.tail y` is nonzero, a point `y` lies on the graph of the `i`-th
distinct root of `P` (counted from `0`) when `y 0` is a root with exactly `i` roots below it, and in
the `j`-th sector when `y 0` is not a root and has exactly `j` roots below it. The sectors are
counted from below: sector `0` lies below the smallest root, the last one above the largest root,
and over a fiber without roots sector `0` is the whole fiber. Over a base point where `P`
specializes to zero, the root predicate holds on the whole fiber for `i = 0` and nowhere else, and
the non-root predicate holds nowhere. -/

variable {n : ℕ}

/-- **The root locus with `i` roots below.** The points of `R ^ (n + 1)` whose coordinate `0` is a
root of the specialization of `P` at the remaining coordinates, with exactly `i` distinct roots
below it, form a semialgebraic set. Over a base point where `P` does not specialize to zero, this is
the graph of the `i`-th distinct root (counted from `0`). Over a base point where `P` specializes to
zero, it is the whole fiber for `i = 0` and empty otherwise. -/
theorem isSemialgebraic_setOf_isRoot_card_roots_lt (P : (MvPolynomial (Fin n) R)[X]) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R | (P.map (MvPolynomial.eval (Fin.tail y))).IsRoot (y 0) ∧
      {r ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset | r < y 0}.card = i} := by
  first
    -- The family over `R ^ (n + 1)` whose specialization at `y` is that of `P` at `Fin.tail y`.
  | set Q := P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
    convert (isSemialgebraic_eval_eq_zero (Q.eval (MvPolynomial.X 0))).inter
      (isSemialgebraic_setOf_card_roots_map_eval_lt Q (MvPolynomial.X 0) i) using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, IsRoot.def, ← eval_map_apply, Q, map_eval_map_rename,
      MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

/-- **The non-root locus with `j` roots below.** The points of `R ^ (n + 1)` whose coordinate `0`
is not a root of the specialization of `P` at the remaining coordinates, with exactly `j` distinct
roots below it, form a semialgebraic set. Over a base point where `P` does not specialize to zero,
this is the `j`-th sector counted from below, including the unbounded sectors below the smallest
and above the largest root. Over a base point where `P` specializes to zero there are no such
points. -/
theorem isSemialgebraic_setOf_not_isRoot_card_roots_lt (P : (MvPolynomial (Fin n) R)[X])
    (j : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      ¬ (P.map (MvPolynomial.eval (Fin.tail y))).IsRoot (y 0) ∧
      {r ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset | r < y 0}.card = j} := by
  first
    -- The family over `R ^ (n + 1)` whose specialization at `y` is that of `P` at `Fin.tail y`.
  | set Q := P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
    convert (isSemialgebraic_eval_ne_zero (Q.eval (MvPolynomial.X 0))).inter
      (isSemialgebraic_setOf_card_roots_map_eval_lt Q (MvPolynomial.X 0) j) using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, IsRoot.def, ← eval_map_apply, Q, map_eval_map_rename,
      MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

end RealClosed

end TauCeti
end -- closes the original EOF section from source line 64
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/RootCount.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/SharedRoots.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Semialgebraic descriptions of shared roots

The shared roots of a finite polynomial family are the union of the distinct roots of its
nonzero specializations. Their number, and their number below a polynomial threshold, have
finite polynomial sign descriptions. In cylinder coordinates this gives the graph of each
ordered shared root and every complementary sector, including the two unbounded sectors.

At each parameter, only the active (nonzero) specializations enter the product. Stratifying
by this active subfamily reduces the descriptions to the uniform single-polynomial root
formulas. No closure under projection, constancy of degrees, or continuity of roots is needed.
Repeated roots and roots shared by several members are counted once. A nullified member is
omitted: its entire zero set is not part of the finite shared root set. When all members are
nullified, or the family is empty, the shared root set is empty and sector zero is the whole
fiber.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapters 10 and 11
(uniform sign descriptions and the roots of an active polynomial family).
-/

public section

open Polynomial Set TauCeti

namespace Finset

variable {σ R : Type*}

section Domain

variable [CommRing R] [IsDomain R] [LinearOrder R]

/-- Membership in the shared distinct root set at a polynomial threshold is semialgebraic.
Zero specializations are omitted, rather than contributing their entire zero set. -/
theorem isSemialgebraic_setOf_mem_biUnion_roots_map_eval
    (F : Finset (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R |
      MvPolynomial.eval x T ∈ F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset} := by
  first
  | classical
    have h : {x : σ → R |
        MvPolynomial.eval x T ∈ F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset} =
        ⋃ P ∈ F, {x | P.map (MvPolynomial.eval x) ≠ 0} ∩
          {x | MvPolynomial.eval x (P.eval T) = 0} := by
      ext x
      simp only [mem_ofPred_eq, mem_biUnion, Multiset.mem_toFinset, mem_roots', IsRoot.def,
        eval_map_apply, mem_iUnion, mem_inter_iff, exists_prop]
    rw [h]
    exact .biUnion F.finite_toSet fun P _ =>
      (isSemialgebraic_setOf_map_eval_eq_zero P).compl.inter (isSemialgebraic_eval_eq_zero _)

/-- Reduce a condition on shared roots to conditions on the products of the active subfamilies.
This helper keeps the finite stratification common to the total and below-threshold counts. -/
private theorem isSemialgebraic_setOf_biUnion_roots_map_eval
    (F : Finset (MvPolynomial σ R)[X]) (φ : (σ → R) → Finset R → Prop)
    (hφ : ∀ Q : (MvPolynomial σ R)[X],
      IsSemialgebraic {x | φ x (Q.map (MvPolynomial.eval x)).roots.toFinset}) :
    IsSemialgebraic {x | φ x (F.biUnion fun P =>
      (P.map (MvPolynomial.eval x)).roots.toFinset)} := by
  first
  | classical
    let active := fun (A : Finset (MvPolynomial σ R)[X]) =>
      {x : σ → R | ∀ P ∈ F, P ∈ A ↔ P.map (MvPolynomial.eval x) ≠ 0}
    have hactive (A : Finset (MvPolynomial σ R)[X]) : IsSemialgebraic (active A) := by
      have hP (P : (MvPolynomial σ R)[X]) :
          IsSemialgebraic {x : σ → R | P ∈ A ↔ P.map (MvPolynomial.eval x) ≠ 0} := by
        by_cases hPA : P ∈ A
        · simpa only [hPA, true_iff, compl_ofPred] using
            (isSemialgebraic_setOf_map_eval_eq_zero P).compl
        · simpa only [hPA, false_iff, not_not] using isSemialgebraic_setOf_map_eval_eq_zero P
      simpa only [active, ofPred_forall, Finset.mem_coe] using
        IsSemialgebraic.biInter F.finite_toSet (fun P _ => hP P)
    have hroots (A : Finset (MvPolynomial σ R)[X]) (hA : A ⊆ F) (x : σ → R)
        (hx : x ∈ active A) :
        ((∏ P ∈ A, P).map (MvPolynomial.eval x)).roots.toFinset =
          F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset := by
      have hne : ∀ P ∈ A, P.map (MvPolynomial.eval x) ≠ 0 :=
        fun P hP => (hx P (hA hP)).mp hP
      rw [Polynomial.map_prod, roots_prod _ _ (prod_ne_zero_iff.mpr hne), bind_toFinset,
        A.val_toFinset]
      ext r
      simp only [mem_biUnion, Multiset.mem_toFinset]
      constructor
      · rintro ⟨P, hP, hr⟩
        exact ⟨P, hA hP, hr⟩
      · rintro ⟨P, hP, hr⟩
        exact ⟨P, (hx P hP).mpr (ne_zero_of_mem_roots hr), hr⟩
    have h : {x | φ x (F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset)} =
        ⋃ A ∈ F.powerset, active A ∩
          {x | φ x ((∏ P ∈ A, P).map (MvPolynomial.eval x)).roots.toFinset} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_powerset]
      constructor
      · intro hx
        let A := F.filter fun P => P.map (MvPolynomial.eval x) ≠ 0
        have hxA : x ∈ active A := by
          intro P hP
          simp only [A, mem_filter, hP, true_and]
        exact ⟨A, filter_subset _ _, hxA, by rw [hroots A (filter_subset _ _) x hxA]; exact hx⟩
      · rintro ⟨A, hA, hxA, hx⟩
        rwa [hroots A hA x hxA] at hx
    rw [h]
    exact .biUnion F.powerset.finite_toSet fun A _ => (hactive A).inter (hφ _)

end Domain

section RealClosed

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The number of shared distinct roots is semialgebraic in the parameters, even when members
are nullified or their degrees drop. An empty active subfamily has count zero. -/
theorem isSemialgebraic_setOf_card_biUnion_roots_map_eval
    (F : Finset (MvPolynomial σ R)[X]) (k : ℕ) :
    IsSemialgebraic {x : σ → R |
      (F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset).card = k} := by
  first
  | classical
    exact isSemialgebraic_setOf_biUnion_roots_map_eval F (fun _ s => s.card = k)
      (fun Q => isSemialgebraic_setOf_card_roots_map_eval Q k)

/-- The number of shared distinct roots strictly below a polynomial threshold is semialgebraic.
The strict inequality includes the case where the threshold is itself a shared root. -/
theorem isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt
    (F : Finset (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (k : ℕ) :
    IsSemialgebraic {x : σ → R |
      {r ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval x)).roots.toFinset) |
        r < MvPolynomial.eval x T}.card = k} := by
  first
  | classical
    exact isSemialgebraic_setOf_biUnion_roots_map_eval F
      (fun x s => (s.filter fun r => r < MvPolynomial.eval x T).card = k)
      (fun Q => isSemialgebraic_setOf_card_roots_map_eval_lt Q T k)

variable {n : ℕ}

/-- The graph of the `i`th ordered shared distinct root, counted from zero, is semialgebraic
in cylinder coordinates. Where fewer than `i + 1` shared roots exist the fiber is empty. -/
theorem isSemialgebraic_setOf_mem_biUnion_roots_card_lt
    (F : Finset (MvPolynomial (Fin n) R)[X]) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      y 0 ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
      {r ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
        r < y 0}.card = i} := by
  first
  | classical
    let G := F.image fun P => P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
    convert (G.isSemialgebraic_setOf_mem_biUnion_roots_map_eval (MvPolynomial.X 0)).inter
      (G.isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt (MvPolynomial.X 0) i) using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, G, image_biUnion, map_eval_map_rename,
      MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

/-- The locus of the `j`th shared-root sector, counted from below, is semialgebraic.
Sector zero is the whole fiber if no active member has a root. -/
theorem isSemialgebraic_setOf_notMem_biUnion_roots_card_lt
    (F : Finset (MvPolynomial (Fin n) R)[X]) (j : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      y 0 ∉ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
      {r ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
        r < y 0}.card = j} := by
  first
  | classical
    let G := F.image fun P => P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
    convert (G.isSemialgebraic_setOf_mem_biUnion_roots_map_eval (MvPolynomial.X 0)).compl.inter
      (G.isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt (MvPolynomial.X 0) j) using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, G, image_biUnion, map_eval_map_rename,
      MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

end RealClosed

end Finset
end -- closes the original EOF section from source line 34
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/SharedRoots.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Semialgebraic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Semialgebraicity of polynomial delineations

Every delineation of a finite polynomial family over a semialgebraic base is a semialgebraic
stack. No closure under differentiation is needed. The sections and sectors are described by
membership in the shared distinct root set and the number of shared roots strictly below the
height, using the uniform formulas of
`Finset.isSemialgebraic_setOf_mem_biUnion_roots_card_lt` and
`Finset.isSemialgebraic_setOf_notMem_biUnion_roots_card_lt`.

Coefficients may come from any commutative ring equipped with a homomorphism to `ℝ`.
Nullified fibers contribute no roots to the finite shared root set; they do not contribute
their entire zero set. Repeated roots and roots shared by several members are counted once.
The empty family and a stack with no sections are included.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 10 and 11 (uniform shared-root descriptions and semialgebraic stacks).
-/

public section

open Set MvPolynomial
open scoped Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {n : ℕ} {φ : A →+* ℝ}
  {F : Finset (MvPolynomial (Fin n) A)[X]} {C : Set (Fin n → ℝ)}

/-- A delineation of a finite polynomial family over a semialgebraic base is a semialgebraic
stack. The family need not be closed under differentiation. Nullified members are allowed. -/
theorem Delineation.isSemialgebraicStack (hC : IsSemialgebraic C)
    (D : Delineation fun (p : F) (x : C) ↦ p.1.map (eval₂Hom φ x.1)) :
    IsSemialgebraicStack C D.root := by
  first
  | classical
    -- Pass the coefficients to ℝ; the homomorphism may identify different family members.
    let G := F.image fun p ↦ p.map (MvPolynomial.map φ)
    have hmap (p : (MvPolynomial (Fin n) A)[X]) (x : Fin n → ℝ) :
        (p.map (MvPolynomial.map φ)).map (MvPolynomial.eval x) = p.map (eval₂Hom φ x) := by
      ext j
      simp [Polynomial.coeff_map, MvPolynomial.eval_map]
    have hroots (x : C) :
        G.biUnion (fun p ↦ (p.map (MvPolynomial.eval x.1)).roots.toFinset) =
          Finset.univ.image (fun i ↦ D.root i x) := by
      ext t
      simp only [G, Finset.image_biUnion, hmap, Finset.mem_biUnion,
        Multiset.mem_toFinset, Polynomial.mem_roots', Finset.mem_image, Finset.mem_univ,
        true_and]
      simpa only [mem_range, mem_ofPred_eq, Subtype.exists, exists_prop] using
        (Set.ext_iff.1 (D.range_root x) t).symm
    -- Identify the ambient cells with the shared-root rank formulas on the base.
    have hsection (i : Fin D.count) : cylinder C '' sectionSet D.root i =
        {y : Fin (n + 1) → ℝ | Fin.tail y ∈ C} ∩ {y : Fin (n + 1) → ℝ |
          y 0 ∈ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
          {r ∈ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
            r < y 0}.card = i.val} := by
      ext y
      simp only [mem_image_cylinder, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hy, hi⟩
        refine ⟨hy, ?_⟩
        rw [hroots ⟨Fin.tail y, hy⟩]
        exact (mem_sectionSet_iff_mem_image_card_lt i _ (D.strictMono_root _)).1 hi
      · rintro ⟨hy, hi⟩
        refine ⟨hy, ?_⟩
        rw [hroots ⟨Fin.tail y, hy⟩] at hi
        exact (mem_sectionSet_iff_mem_image_card_lt i _ (D.strictMono_root _)).2 hi
    have hsector (j : Fin (D.count + 1)) : cylinder C '' sectorSet D.root j =
        {y : Fin (n + 1) → ℝ | Fin.tail y ∈ C} ∩ {y : Fin (n + 1) → ℝ |
          y 0 ∉ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
          {r ∈ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
            r < y 0}.card = j.val} := by
      ext y
      simp only [mem_image_cylinder, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hy, hj⟩
        refine ⟨hy, ?_⟩
        rw [hroots ⟨Fin.tail y, hy⟩]
        exact (mem_sectorSet_iff_notMem_image_card_lt j _ (D.strictMono_root _)).1 hj
      · rintro ⟨hy, hj⟩
        refine ⟨hy, ?_⟩
        rw [hroots ⟨Fin.tail y, hy⟩] at hj
        exact (mem_sectorSet_iff_notMem_image_card_lt j _ (D.strictMono_root _)).2 hj
    refine ⟨D.continuous_root, D.strictMono_root, fun i ↦ ?_, fun j ↦ ?_⟩
    · rw [hsection]
      exact hC.preimage_tail.inter (G.isSemialgebraic_setOf_mem_biUnion_roots_card_lt i.val)
    · rw [hsector]
      exact hC.preimage_tail.inter (G.isSemialgebraic_setOf_notMem_biUnion_roots_card_lt j.val)

end TauCeti
end -- closes the original EOF section from source line 35
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Semialgebraic.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/CAD/Existence.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Existence of adapted cylindrical algebraic decompositions

For every finite set `F` of real polynomials in `n` variables there is a cylindrical algebraic
decomposition of `ℝ ^ n` adapted to `F`: every member of `F` is sign-invariant on every cell
(`TauCeti.exists_isCAD_signInvariant`).

The proof is by induction on `n`. Single out the first variable with `MvPolynomial.finSuccEquiv`
and take an adapted CAD of `ℝ ^ n` for the Collins projection of the resulting family.
By Collins delineability, the family has a delineation over each cell. Its stacks give the CAD
of `ℝ ^ (n + 1)`.

These stacks are semialgebraic by `TauCeti.Delineation.isSemialgebraicStack`: their sections
and sectors are described by membership in the shared distinct root set and the number of
shared roots below the height. No derivatives need to be added to the input family.
Nullified members, repeated roots, the empty family and stacks without sections are included.

## Main results

* `TauCeti.exists_isCAD_signInvariant`: every finite set of polynomials has an adapted CAD.
* `TauCeti.HasSemialgebraicProjections ℝ`: **projection closure**, the Tarski–Seidenberg theorem.
  Forgetting the coordinate `0` maps semialgebraic subsets of `ℝ ^ (n + 1)` to semialgebraic
  subsets of `ℝ ^ n` (`TauCeti.HasSemialgebraicProjections.isSemialgebraic_image_tail`). A
  semialgebraic set is a sign condition on finitely many polynomials, so it is a union of cells
  of an adapted CAD, and its projection is a union of cells of the projected CAD. With this
  instance the results of `TauCeti.Geometry.RealAlgebraic.Semialgebraic.QuantifierElimination` and
  `TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image` apply to `ℝ`.
* `TauCeti.exists_finite_image_sign_eval_eq`: finitely many sample points realize every sign
  vector of a finite family of polynomials.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 and Chapter 11 (cylindrical decomposition).
-/

public section

open Function Set MvPolynomial
open scoped Polynomial

namespace TauCeti

variable {n : ℕ}

/-- **Existence of adapted cylindrical algebraic decompositions.** For every finite set `F` of
real polynomials in `n` variables there is a cylindrical algebraic decomposition of `ℝ ^ n` on
each cell of which every member of `F` is sign-invariant. -/
theorem exists_isCAD_signInvariant (F : Finset (MvPolynomial (Fin n) ℝ)) :
    ∃ 𝒞, IsCAD n 𝒞 ∧ ∀ f ∈ F, ∀ E ∈ 𝒞, SignInvariant (fun x ↦ eval x f) E := by
  first
  | induction n with
    | zero =>
      exact ⟨{univ}, .zero, fun f _ E hE ↦ by
        rw [mem_singleton_iff.1 hE]
        exact subsingleton_of_subsingleton.signInvariant⟩
    | succ n ih =>
      classical
      let G := F.image (finSuccEquiv ℝ n)
      have hFG {f} (hf : f ∈ F) : finSuccEquiv ℝ n f ∈ G :=
        Finset.mem_image_of_mem _ hf
      obtain ⟨𝒟, h𝒟, hproj⟩ := ih G.collinsProjection
      -- over each base cell, the stack of a delineation of the fibers of `G`
      obtain ⟨𝒞, h𝒞, -, hsign⟩ := h𝒟.exists_succ_of_forall_exists_stack
        (fun E ↦ ∀ f ∈ F, SignInvariant (fun y ↦ eval y f) E) fun C hC ↦ by
          obtain ⟨D⟩ := nonempty_delineation_of_signInvariant_collinsProjection
            (φ := RingHom.id ℝ) (h𝒟.isConnected hC).isPreconnected fun q hq ↦ by
              simpa only [eval₂_id] using hproj q hq C hC
          refine ⟨D.count, D.root, D.isSemialgebraicStack (h𝒟.isSemialgebraic hC),
            fun E hE f hf ↦ ?_⟩
          simpa only [eval₂_id] using D.signInvariant_eval₂_of_mem_stackCells (hFG hf) hE
      exact ⟨𝒞, h𝒞, fun f hf E hE ↦ hsign E hE f hf⟩

/-- **The Tarski–Seidenberg theorem.** The projection of a semialgebraic subset of `ℝ ^ (n + 1)`
forgetting the coordinate `0` is semialgebraic. So quantifier elimination, the identification of
semialgebraic sets with definable sets, and the image and composition laws of semialgebraic
functions, which assume `HasSemialgebraicProjections`, hold over `ℝ` unconditionally. -/
instance : HasSemialgebraicProjections ℝ where
  isSemialgebraic_image_tail {_ _} hs := by
    first
    | classical
      obtain ⟨m, p, Φ, rfl⟩ := hs.exists_eq_setOf_sign_eval
      obtain ⟨𝒞, h𝒞, hp⟩ := exists_isCAD_signInvariant (Finset.univ.image p)
      exact h𝒞.isSemialgebraic_image_tail_setOf_sign_eval
        (fun i ↦ hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) Φ

/-- **Sample points.** For finitely many real polynomials `p i` in `n` variables there is a
finite set of points of `ℝ ^ n` at which the `p i` take every sign vector that they take on
`ℝ ^ n`. -/
theorem exists_finite_image_sign_eval_eq {ι : Type*} [Finite ι]
    (p : ι → MvPolynomial (Fin n) ℝ) :
    ∃ T : Set (Fin n → ℝ), T.Finite ∧
      (fun x i ↦ SignType.sign (eval x (p i))) '' T =
        range fun x i ↦ SignType.sign (eval x (p i)) := by
  first
  | classical
    have := Fintype.ofFinite ι
    obtain ⟨𝒞, h𝒞, hp⟩ := exists_isCAD_signInvariant (Finset.univ.image p)
    obtain ⟨T, hT, -, hTp⟩ := h𝒞.exists_finite_image_sign_eval_eq
      fun i ↦ hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact ⟨T, hT, hTp⟩

end TauCeti
end -- closes the original EOF section from source line 49
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/CAD/Existence.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Function.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Semialgebraic functions

A function between coordinate spaces is semialgebraic on a set when its domain and graph are
semialgebraic.  The graph is regarded as a subset of the coordinate space indexed by the disjoint
union of the input and output coordinates.  Requiring the specified domain to be semialgebraic is
useful before projection closure is available: semialgebraicity of a graph alone does not yet let
us recover its projection onto the input coordinates.

This file gives the graph predicate its basic API.  It proves restriction, congruence, and
piecewise-gluing laws and shows that polynomial maps are semialgebraic.  It also proves the
operations whose graphs are inverse images of the given graphs, so that no coordinate has to be
eliminated: pairing two functions on the same domain (`TauCeti.IsSemialgebraicOn.sumElim`),
precomposition with a polynomial map (`TauCeti.IsSemialgebraicOn.comp_eval`), pointwise
negation (`TauCeti.IsSemialgebraicOn.neg`), and bijective changes of the input or output
coordinates (`TauCeti.isSemialgebraicOn_preimage_comp_equiv_iff`,
`TauCeti.isSemialgebraicOn_comp_equiv_iff`).  It deliberately does not assert closure under
arbitrary composition, whose graph generally requires eliminating the intermediate coordinates;
images, inverse images, composition, and pointwise sums, products, and differences are derived
from projection closure in `TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {σ τ R : Type*} [CommRing R] [LinearOrder R]

/-- A function `f : (σ → R) → (τ → R)` is semialgebraic on `s` if `s` is semialgebraic and the
graph of `f` over `s`, encoded in the coordinate space `σ ⊕ τ → R`, is semialgebraic. -/
def IsSemialgebraicOn (f : (σ → R) → (τ → R)) (s : Set (σ → R)) : Prop :=
  IsSemialgebraic s ∧
    IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f)

/-- A function between coordinate spaces is semialgebraic if its graph over the whole input space
is semialgebraic. -/
def IsSemialgebraicMap (f : (σ → R) → (τ → R)) : Prop :=
  IsSemialgebraicOn f univ

/-- Semialgebraicity on the whole domain is semialgebraicity as a map. -/
@[simp]
theorem isSemialgebraicOn_univ {f : (σ → R) → (τ → R)} :
    IsSemialgebraicOn f univ ↔ IsSemialgebraicMap f :=
  Iff.rfl

/-- Characterization of a function being semialgebraic on a specified domain. -/
theorem isSemialgebraicOn_def {f : (σ → R) → (τ → R)} {s : Set (σ → R)} :
    IsSemialgebraicOn f s ↔ IsSemialgebraic s ∧
      IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) :=
  Iff.rfl

/-- Characterization of a semialgebraic map by its graph. -/
theorem isSemialgebraicMap_def {f : (σ → R) → (τ → R)} :
    IsSemialgebraicMap f ↔
      IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' univ.graphOn f) := by
  first
  | simp [IsSemialgebraicMap, IsSemialgebraicOn]

omit [CommRing R] [LinearOrder R] in
/-- A point of `σ ⊕ τ → R` lies on the encoded graph of `f` over `s` exactly when its input
coordinates lie in `s` and `f` sends them to its output coordinates. -/
theorem mem_preimage_sumArrowEquivProdArrow_graphOn {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    {z : σ ⊕ τ → R} :
    z ∈ Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f ↔
      z ∘ Sum.inl ∈ s ∧ f (z ∘ Sum.inl) = z ∘ Sum.inr := by
  first
  | rw [mem_preimage, mem_graphOn]
    -- `Equiv.sumArrowEquivProdArrow σ τ R z` is `(z ∘ Sum.inl, z ∘ Sum.inr)` by definition.
    rfl

/-- The domain of a function semialgebraic on a set is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) : IsSemialgebraic s :=
  hf.1

/-- The graph of a function semialgebraic on a set is semialgebraic. -/
theorem IsSemialgebraicOn.graph {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) :
    IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) :=
  hf.2

/-- Restricting a semialgebraic function to a semialgebraic subset preserves
semialgebraicity. -/
theorem IsSemialgebraicOn.mono {f : (σ → R) → (τ → R)} {s t : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (ht : IsSemialgebraic t) (h : t ⊆ s) :
    IsSemialgebraicOn f t := by
  first
  | refine ⟨ht, ?_⟩
    have hgraph : Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' t.graphOn f =
        (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) ∩
          (fun z : σ ⊕ τ → R => z ∘ Sum.inl) ⁻¹' t := by
      ext z
      have hfst : (Equiv.sumArrowEquivProdArrow σ τ R z).1 = z ∘ Sum.inl := by
        funext i
        exact Equiv.sumArrowEquivProdArrow_apply_fst z i
      simp only [mem_preimage, mem_graphOn, mem_inter_iff, hfst]
      constructor
      · intro hz
        exact ⟨⟨h hz.1, hz.2⟩, hz.1⟩
      · intro hz
        exact ⟨hz.2, hz.1.2⟩
    rw [hgraph]
    exact hf.graph.inter (ht.preimage_comp Sum.inl)

/-- A semialgebraic map is semialgebraic on every semialgebraic domain. -/
theorem IsSemialgebraicMap.isSemialgebraicOn {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraicOn f s :=
  hf.mono hs (subset_univ s)

/-- Semialgebraicity on a set depends only on the values of the function on that set. -/
theorem IsSemialgebraicOn.congr {f g : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (h : s.EqOn f g) : IsSemialgebraicOn g s := by
  first
  | refine ⟨hf.isSemialgebraic, ?_⟩
    rw [← Set.graphOn_inj.2 h]
    exact hf.graph

/-- Every function is semialgebraic on the empty set. -/
@[simp]
theorem isSemialgebraicOn_empty (f : (σ → R) → (τ → R)) :
    IsSemialgebraicOn f ∅ := by
  first
  | simp [IsSemialgebraicOn]

/-- Semialgebraic functions on two semialgebraic pieces glue to a semialgebraic function. -/
theorem IsSemialgebraicOn.glue {f g h : (σ → R) → (τ → R)} {s t : Set (σ → R)}
    (hf : IsSemialgebraicOn f (s ∩ t)) (hg : IsSemialgebraicOn g (s \ t))
    (hft : (s ∩ t).EqOn h f) (hgt : (s \ t).EqOn h g) : IsSemialgebraicOn h s := by
  first
  | have hhst := hf.congr hft.symm
    have hhst' := hg.congr hgt.symm
    have hst : s = (s ∩ t) ∪ (s \ t) := by
      ext x
      simp
    have hs : IsSemialgebraic s := by
      rw [hst]
      exact hf.isSemialgebraic.union hg.isSemialgebraic
    refine ⟨hs, ?_⟩
    rw [hst, Set.graphOn_union, preimage_union]
    exact hhst.graph.union hhst'.graph

section PolynomialMap

/-- A map whose output coordinates are polynomials in the input coordinates is semialgebraic on
every semialgebraic domain. -/
theorem isSemialgebraicOn_eval [Finite τ] (p : τ → MvPolynomial σ R)
    {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraicOn (fun x i => eval x (p i)) s := by
  first
  | refine ⟨hs, ?_⟩
    have hgraph : Equiv.sumArrowEquivProdArrow σ τ R ⁻¹'
        s.graphOn (fun x i => eval x (p i)) =
        ((fun z : σ ⊕ τ → R => z ∘ Sum.inl) ⁻¹' s) ∩
          ⋂ i, {z | eval z (X (Sum.inr i) - rename Sum.inl (p i)) = 0} := by
      ext z
      have hfst : (Equiv.sumArrowEquivProdArrow σ τ R z).1 = z ∘ Sum.inl := by
        funext i
        exact Equiv.sumArrowEquivProdArrow_apply_fst z i
      have hsnd : (Equiv.sumArrowEquivProdArrow σ τ R z).2 = z ∘ Sum.inr := by
        funext i
        exact Equiv.sumArrowEquivProdArrow_apply_snd z i
      simp only [mem_preimage, mem_graphOn, mem_inter_iff, mem_iInter, mem_ofPred_eq, hfst, hsnd]
      constructor
      · rintro ⟨hz, hp⟩
        refine ⟨hz, fun i => ?_⟩
        simpa [sub_eq_zero, MvPolynomial.eval_rename] using (congrFun hp i).symm
      · rintro ⟨hz, hp⟩
        refine ⟨hz, funext fun i => ?_⟩
        have hi := hp i
        have hi' : z (Sum.inr i) = eval (z ∘ Sum.inl) (p i) := by
          simpa [sub_eq_zero, MvPolynomial.eval_rename] using hi
        exact hi'.symm
    rw [hgraph]
    exact (hs.preimage_comp Sum.inl).inter <|
      .iInter fun i => isSemialgebraic_eval_eq_zero (X (Sum.inr i) - rename Sum.inl (p i))

/-- A polynomial map between coordinate spaces is semialgebraic. -/
theorem isSemialgebraicMap_eval [Finite τ] (p : τ → MvPolynomial σ R) :
    IsSemialgebraicMap (fun x i => eval x (p i)) := by
  first
  | rw [← isSemialgebraicOn_univ]
    exact isSemialgebraicOn_eval p isSemialgebraic_univ

/-- A constant map into a finite-dimensional coordinate space is semialgebraic on every
semialgebraic domain. -/
theorem isSemialgebraicOn_const [Finite τ] (c : τ → R) {s : Set (σ → R)}
    (hs : IsSemialgebraic s) : IsSemialgebraicOn (fun _ => c) s := by
  first
  | simpa using isSemialgebraicOn_eval (fun i : τ => C (c i)) hs

/-- A constant map into a finite-dimensional coordinate space is semialgebraic. -/
@[simp]
theorem isSemialgebraicMap_const [Finite τ] (c : τ → R) :
    IsSemialgebraicMap (fun _ : σ → R => c) := by
  first
  | rw [← isSemialgebraicOn_univ]
    exact isSemialgebraicOn_const c isSemialgebraic_univ

/-- The identity map on a finite-dimensional coordinate space is semialgebraic. -/
@[simp]
theorem isSemialgebraicMap_id [Finite σ] :
    IsSemialgebraicMap (id : (σ → R) → (σ → R)) := by
  first
  | rw [← isSemialgebraicOn_univ]
    apply IsSemialgebraicOn.congr <|
      (isSemialgebraicMap_eval (R := R) (σ := σ) (τ := σ) (fun i : σ => X i)).isSemialgebraicOn
        isSemialgebraic_univ
    intro x _
    funext i
    simp

end PolynomialMap

section Operations

variable {σ' τ' : Type*}

/-- Pairing two semialgebraic functions on the same domain gives a semialgebraic function into
the coordinate space indexed by the disjoint union of their output coordinates.  No projection is
needed: the graph of the pair is the intersection of the inverse images of the two graphs. -/
theorem IsSemialgebraicOn.sumElim {f : (σ → R) → (τ → R)} {g : (σ → R) → (τ' → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (fun x => Sum.elim (f x) (g x)) s := by
  first
  | refine ⟨hf.isSemialgebraic, ?_⟩
    convert (hf.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))).inter
      (hg.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))) using 1
    ext z
    simp only [mem_inter_iff, mem_preimage_sumArrowEquivProdArrow_graphOn,
      mem_preimage (f := fun x : σ ⊕ τ ⊕ τ' → R => x ∘ Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)),
      mem_preimage (f := fun x : σ ⊕ τ ⊕ τ' → R => x ∘ Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)),
      Function.comp_assoc, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← Sum.elim_comp_inl_inr (z ∘ Sum.inr), Sum.elim_eq_iff]
    tauto

/-- Pairing two semialgebraic maps gives a semialgebraic map. -/
theorem IsSemialgebraicMap.sumElim {f : (σ → R) → (τ → R)} {g : (σ → R) → (τ' → R)}
    (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap fun x => Sum.elim (f x) (g x) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).sumElim (isSemialgebraicOn_univ.2 hg)

/-- Precomposing a semialgebraic function with a polynomial map gives a semialgebraic function on
the inverse image of its domain.  No projection is needed: the new graph is the inverse image of
the old one under a polynomial map. -/
theorem IsSemialgebraicOn.comp_eval {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (p : σ → MvPolynomial σ' R) :
    IsSemialgebraicOn (f ∘ fun x i => eval x (p i)) ((fun x i => eval x (p i)) ⁻¹' s) := by
  first
  | refine ⟨hf.isSemialgebraic.preimage_eval p, ?_⟩
    convert hf.graph.preimage_eval (Sum.elim (fun i => rename Sum.inl (p i)) fun j => X (Sum.inr j))
      using 1
    ext z
    simp only [mem_preimage_sumArrowEquivProdArrow_graphOn,
      mem_preimage (f := fun (x : σ' ⊕ τ → R) (i : σ ⊕ τ) => eval x _), Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, eval_rename, eval_X]
    simp only [mem_preimage]

/-- Precomposing a semialgebraic map with a polynomial map gives a semialgebraic map. -/
theorem IsSemialgebraicMap.comp_eval {f : (σ → R) → (τ → R)} (hf : IsSemialgebraicMap f)
    (p : σ → MvPolynomial σ' R) : IsSemialgebraicMap (f ∘ fun x i => eval x (p i)) := by
  first
  | simpa using (isSemialgebraicOn_univ.2 hf).comp_eval p

/-- The pointwise negation of a semialgebraic function is semialgebraic.  No projection is needed:
the new graph is the inverse image of the old one under negation of the output coordinates. -/
theorem IsSemialgebraicOn.neg {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) : IsSemialgebraicOn (-f) s := by
  first
  | refine ⟨hf.isSemialgebraic, ?_⟩
    convert hf.graph.preimage_eval (Sum.elim (fun i => X (Sum.inl i)) fun j => -X (Sum.inr j))
      using 1
    ext z
    simp only [mem_preimage_sumArrowEquivProdArrow_graphOn,
      mem_preimage (f := fun (x : σ ⊕ τ → R) (i : σ ⊕ τ) => eval x _), Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, eval_X, map_neg]
    rw [Pi.neg_apply, neg_eq_iff_eq_neg]
    rfl

/-- The pointwise negation of a semialgebraic map is semialgebraic. -/
theorem IsSemialgebraicMap.neg {f : (σ → R) → (τ → R)} (hf : IsSemialgebraicMap f) :
    IsSemialgebraicMap (-f) :=
  isSemialgebraicOn_univ.1 (isSemialgebraicOn_univ.2 hf).neg

/-- Semialgebraicity of a function is invariant under a bijective change of input coordinates,
such as a permutation, applied to both the function and its domain. -/
@[simp]
theorem isSemialgebraicOn_preimage_comp_equiv_iff {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (e : σ ≃ σ') :
    IsSemialgebraicOn (fun x : σ' → R => f (x ∘ e)) ((fun x : σ' → R => x ∘ e) ⁻¹' s) ↔
      IsSemialgebraicOn f s := by
  first
  | refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa [Function.comp_def, preimage_preimage] using h.comp_eval fun i => X (e.symm i)
    · simpa [Function.comp_def] using h.comp_eval fun i => X (e i)

/-- Changing the output coordinates of a semialgebraic function by a bijection preserves
semialgebraicity. -/
private theorem IsSemialgebraicOn.comp_equiv {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (e : τ' ≃ τ) : IsSemialgebraicOn (fun x => f x ∘ e) s := by
  first
  | refine ⟨hf.isSemialgebraic, ?_⟩
    convert hf.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ e.symm)) using 1
    ext z
    simp only [mem_preimage_sumArrowEquivProdArrow_graphOn,
      mem_preimage (f := fun x : σ ⊕ τ' → R => x ∘ Sum.elim Sum.inl (Sum.inr ∘ e.symm)),
      Function.comp_assoc, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← Function.comp_assoc z Sum.inr, Equiv.eq_comp_symm]

/-- Semialgebraicity of a function is invariant under a bijective change of output coordinates,
such as a permutation. -/
@[simp]
theorem isSemialgebraicOn_comp_equiv_iff {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (e : τ' ≃ τ) :
    IsSemialgebraicOn (fun x => f x ∘ e) s ↔ IsSemialgebraicOn f s := by
  first
  | refine ⟨fun h => ?_, fun h => h.comp_equiv e⟩
    simpa [Function.comp_assoc] using h.comp_equiv e.symm

end Operations

end TauCeti
end -- closes the original EOF section from source line 38
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Function.lean -/

/- BEGIN SOURCE: TauCeti/ModelTheory/Algebra/OrderedRing/MvPolynomial.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Terms of the language of ordered rings as polynomials

The first-order language of ordered rings is `Language.ring.sum Language.order`: the ring
operations `+`, `*`, `-`, `0`, `1` together with the single relation symbol `≤`. Its terms use
only the ring operations, so a term with variables in `α` is an integer polynomial in `α`.

This file defines that polynomial, `FirstOrder.Language.Term.toMvPolynomial`, with its equations
for variables and the ring operations, and proves:

* `FirstOrder.Language.Term.realize_eq_aeval_toMvPolynomial`: in a commutative ring whose ring
  symbols have their usual meaning (`FirstOrder.Ring.CompatibleRing`), realizing a term is
  evaluating its polynomial, and `FirstOrder.Language.Term.realize_eq_eval_map_toMvPolynomial`
  states the same with the polynomial mapped to `R`;
* `FirstOrder.Language.Term.toMvPolynomial_surjective`: every integer polynomial comes from a term;
* `MvPolynomial.exists_term_realize_eq_eval`: a polynomial with coefficients in `R` is realized by
  a term whose extra variables are assigned the coefficients, that is, by a term with parameters
  from `R`.

These are the term-level translation laws between formulas of ordered rings and polynomial sign
conditions, used to identify semialgebraic sets with quantifier-free definable sets.

## Implementation notes

The construction of a term realizing a given polynomial follows the corresponding construction
for `FreeCommRing` in Mathlib's `Mathlib/ModelTheory/Algebra/Ring/FreeCommRing.lean`, by Chris
Hughes.
-/

public section

open FirstOrder FirstOrder.Language MvPolynomial

namespace FirstOrder.Language.Term

variable {α β : Type*}

/-- The integer polynomial computed by a term of the language of ordered rings. -/
noncomputable def toMvPolynomial : (Language.ring.sum Language.order).Term α → MvPolynomial α ℤ
  | var a => X a
  | func (Sum.inl .add) ts => toMvPolynomial (ts 0) + toMvPolynomial (ts 1)
  | func (Sum.inl .mul) ts => toMvPolynomial (ts 0) * toMvPolynomial (ts 1)
  | func (Sum.inl .neg) ts => -toMvPolynomial (ts 0)
  | func (Sum.inl .zero) _ => 0
  | func (Sum.inl .one) _ => 1
  | func (Sum.inr f) _ => nomatch f

/-- The polynomial of a variable is that variable. -/
@[simp]
theorem toMvPolynomial_var (a : α) :
    (var a : (Language.ring.sum Language.order).Term α).toMvPolynomial = X a := by
  first
  | simp [toMvPolynomial]

/-- The polynomial of a sum of terms is the sum of their polynomials. -/
@[simp]
theorem toMvPolynomial_func_add (ts : Fin 2 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.addFunc) ts).toMvPolynomial =
      (ts 0).toMvPolynomial + (ts 1).toMvPolynomial := by
  first
  | simp [toMvPolynomial]

/-- The polynomial of a product of terms is the product of their polynomials. -/
@[simp]
theorem toMvPolynomial_func_mul (ts : Fin 2 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.mulFunc) ts).toMvPolynomial =
      (ts 0).toMvPolynomial * (ts 1).toMvPolynomial := by
  first
  | simp [toMvPolynomial]

/-- The polynomial of the negation of a term is the negation of its polynomial. -/
@[simp]
theorem toMvPolynomial_func_neg (ts : Fin 1 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.negFunc) ts).toMvPolynomial = -(ts 0).toMvPolynomial := by
  first
  | simp [toMvPolynomial]

/-- The polynomial of the constant `0` is `0`. -/
@[simp]
theorem toMvPolynomial_func_zero (ts : Fin 0 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.zeroFunc) ts).toMvPolynomial = 0 := by
  first
  | simp [toMvPolynomial]

/-- The polynomial of the constant `1` is `1`. -/
@[simp]
theorem toMvPolynomial_func_one (ts : Fin 0 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.oneFunc) ts).toMvPolynomial = 1 := by
  first
  | simp [toMvPolynomial]

/-- Renaming the variables of a term renames the variables of its polynomial. -/
theorem toMvPolynomial_relabel (t : (Language.ring.sum Language.order).Term α) (g : α → β) :
    (t.relabel g).toMvPolynomial = rename g t.toMvPolynomial := by
  first
  | induction t with
    | var a => simp [Term.relabel]
    | func f ts ih =>
      rcases f with f | f
      · cases f <;> simp [Term.relabel, ih]
      · exact nomatch f

/-- Every integer polynomial is the polynomial of a term of the language of ordered rings. -/
theorem toMvPolynomial_surjective :
    Function.Surjective (toMvPolynomial : (Language.ring.sum Language.order).Term α → _) := by
  first
    -- The polynomials of terms form a subring containing every variable.
  | let S : Subring (MvPolynomial α ℤ) :=
      { carrier := Set.range toMvPolynomial
        add_mem' := by
          rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
          exact ⟨func (Sum.inl Ring.addFunc) ![s, t], by simp⟩
        mul_mem' := by
          rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
          exact ⟨func (Sum.inl Ring.mulFunc) ![s, t], by simp⟩
        neg_mem' := by
          rintro _ ⟨s, rfl⟩
          exact ⟨func (Sum.inl Ring.negFunc) ![s], by simp⟩
        zero_mem' := ⟨func (Sum.inl Ring.zeroFunc) ![], by simp⟩
        one_mem' := ⟨func (Sum.inl Ring.oneFunc) ![], by simp⟩ }
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      rw [eq_intCast]
      exact intCast_mem S n
    | add p q hp hq => exact S.add_mem hp hq
    | mul_X p i hp => exact S.mul_mem hp ⟨var i, toMvPolynomial_var i⟩

variable {R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]

/-- In a commutative ring whose ring symbols have their usual meaning, realizing a term of the
language of ordered rings is evaluating its integer polynomial. -/
theorem realize_eq_aeval_toMvPolynomial (t : (Language.ring.sum Language.order).Term α)
    (v : α → R) : t.realize v = aeval v t.toMvPolynomial := by
  first
  | induction t with
    | var a => simp
    | func f ts ih =>
      rw [realize_func]
      rcases f with f | f
      · rw [funMap_sumInl]
        cases f <;> simp [ih]
      · exact nomatch f

/-- In a commutative ring whose ring symbols have their usual meaning, realizing a term of the
language of ordered rings is evaluating its integer polynomial mapped to `R`. -/
theorem realize_eq_eval_map_toMvPolynomial (t : (Language.ring.sum Language.order).Term α)
    (v : α → R) : t.realize v = eval v (t.toMvPolynomial.map (Int.castRingHom R)) := by
  first
  | rw [t.realize_eq_aeval_toMvPolynomial, aeval_eq_eval₂Hom, eval_map, algebraMap_int_eq,
      coe_eval₂Hom]

end FirstOrder.Language.Term

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]

/-- Every polynomial over `R` is realized by a term of the language of ordered rings with
parameters from `R`: the variables `Sum.inl r` of the term are assigned the values `r`. -/
theorem exists_term_realize_eq_eval (p : MvPolynomial σ R) :
    ∃ t : (Language.ring.sum Language.order).Term (R ⊕ σ),
      ∀ v : σ → R, t.realize (Sum.elim id v) = eval v p := by
  first
  | obtain ⟨q, hq⟩ : ∃ q : MvPolynomial (R ⊕ σ) ℤ, ∀ v : σ → R,
        aeval (Sum.elim id v) q = eval v p := by
      induction p using MvPolynomial.induction_on with
      | C a => exact ⟨X (Sum.inl a), by simp⟩
      | add p q hp hq =>
        obtain ⟨p', hp'⟩ := hp
        obtain ⟨q', hq'⟩ := hq
        exact ⟨p' + q', by simp [hp', hq']⟩
      | mul_X p i hp =>
        obtain ⟨p', hp'⟩ := hp
        exact ⟨p' * X (Sum.inr i), by simp [hp']⟩
    obtain ⟨t, rfl⟩ := Term.toMvPolynomial_surjective q
    exact ⟨t, fun v => (t.realize_eq_aeval_toMvPolynomial _).trans (hq v)⟩

end MvPolynomial
end -- closes the original EOF section from source line 41
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/ModelTheory/Algebra/OrderedRing/MvPolynomial.lean -/

/- BEGIN SOURCE: TauCeti/ModelTheory/Complexity.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Complexity and realization of first-order formulas

Mathlib's `FirstOrder.Language.BoundedFormula.iSup` and `FirstOrder.Language.BoundedFormula.iInf`
form the disjunction and conjunction of a finite family of formulas. This file shows that both are
quantifier-free when every member of the family is.

In an algebraic language, every atomic formula holds in a subsingleton structure: atomic
formulas can only assert equality of terms.
-/

public section

namespace FirstOrder.Language.BoundedFormula.IsQF

variable {L : Language} {α β : Type*} {n : ℕ}

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
theorem iSup [Finite β] {f : β → L.BoundedFormula α n} (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iSup f).IsQF := by
  first
    -- Mirror the Fintype.ofFinite instance chosen by BoundedFormula.iSup;
    -- its finite-connective goal then reduces to the corresponding list fold.
  | let _ := Fintype.ofFinite β
    suffices ∀ l : List β, (l.map f).foldr (· ⊔ ·) ⊥ |>.IsQF from this _
    intro l
    induction l with
    | nil => exact isQF_bot
    | cons b l ih => exact (hf b).sup ih

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
theorem iInf [Finite β] {f : β → L.BoundedFormula α n} (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iInf f).IsQF := by
  first
    -- Mirror the Fintype.ofFinite instance chosen by BoundedFormula.iInf;
    -- its finite-connective goal then reduces to the corresponding list fold.
  | let _ := Fintype.ofFinite β
    suffices ∀ l : List β, (l.map f).foldr (· ⊓ ·) ⊤ |>.IsQF from this _
    intro l
    induction l with
    | nil => exact top
    | cons b l ih => exact (hf b).inf ih

end FirstOrder.Language.BoundedFormula.IsQF

namespace FirstOrder.Language.BoundedFormula

open FirstOrder

/-- Every atomic formula over an algebraic language holds in a subsingleton structure. -/
theorem realize_of_isAtomic_subsingleton {L : Language} [L.IsAlgebraic]
    {G α : Type*} [Subsingleton G] [L.Structure G]
    {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic)
    (v : α → G) (xs : Fin n → G) : φ.Realize v xs := by
  first
  | cases hφ with
    | equal _ _ => exact Subsingleton.elim _ _
    | rel r _ => exact isEmptyElim r

end FirstOrder.Language.BoundedFormula
end -- closes the original EOF section from source line 21
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/ModelTheory/Complexity.lean -/

/- BEGIN SOURCE: TauCeti/ModelTheory/Algebra/OrderedRing/SignCondition.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Quantifier-free formulas of ordered rings as sign conditions

A quantifier-free formula of the language of ordered rings `Language.ring.sum Language.order` is a
Boolean combination of equations `t₁ = t₂` and inequalities `t₁ ≤ t₂` between terms, and a term is
an integer polynomial (`FirstOrder.Language.Term.toMvPolynomial`). This file proves that such
formulas are exactly the sign conditions on finitely many integer polynomials: conditions that
depend only on the signs of the values of the polynomials.

* `FirstOrder.Language.BoundedFormula.IsQF.exists_realize_iff_sign`: a quantifier-free formula
  holds exactly when a fixed condition `Φ` holds of the signs of finitely many fixed integer
  polynomials `p i` in its free and bound variables.
* `FirstOrder.Language.BoundedFormula.exists_isQF_realize_iff_sign`: conversely, every condition
  on the signs of finitely many integer polynomials is expressed by a quantifier-free formula,
  built from the atomic formulas `FirstOrder.Language.Term.signFormula` saying that a term has a
  given sign.

The polynomials, the sign condition and the formula do not depend on the structure in which the
formula is interpreted: the equivalences hold in every commutative ring with a compatible linear
order, with the ring symbols and `≤` interpreted as usual. The first statement needs the order to
be compatible with addition, since `t₁ ≤ t₂` becomes the condition that `t₁ - t₂` is not positive.
The second needs no such compatibility, since a sign condition on `p` compares `p` with `0`.

These are the formula-level translation laws between formulas of ordered rings and polynomial sign
conditions. Over a fixed ring they identify semialgebraic sets with quantifier-free definable sets,
as in `TauCeti.Geometry.RealAlgebraic.Semialgebraic.Formula`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 2.3, for quantifier-free formulas and sign conditions.
-/

public section

universe u

open FirstOrder FirstOrder.Language MvPolynomial

namespace FirstOrder.Language.Term

variable {α : Type*} {n : ℕ}

/-- The quantifier-free formula saying that the value of the term `t` has sign `s`. -/
noncomputable def signFormula (t : (Language.ring.sum Language.order).Term (α ⊕ Fin n)) :
    SignType → (Language.ring.sum Language.order).BoundedFormula α n
  | .zero => t.bdEqual (func (Sum.inl Ring.zeroFunc) ![])
  | .neg => (leSymb.boundedFormula₂ (func (Sum.inl Ring.zeroFunc) ![]) t).not
  | .pos => (leSymb.boundedFormula₂ t (func (Sum.inl Ring.zeroFunc) ![])).not

/-- The formula `t.signFormula s` is quantifier-free. -/
theorem isQF_signFormula (t : (Language.ring.sum Language.order).Term (α ⊕ Fin n))
    (s : SignType) : (t.signFormula s).IsQF := by
  first
  | cases s
    · exact (BoundedFormula.IsAtomic.equal _ _).isQF
    · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not
    · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not

/-- The formula `t.signFormula s` holds exactly when the value of `t` has sign `s`. -/
@[simp]
theorem realize_signFormula {R : Type*} [CommRing R] [Ring.CompatibleRing R]
    [Language.order.Structure R] [LinearOrder R]
    [(Language.ring.sum Language.order).OrderedStructure R]
    (t : (Language.ring.sum Language.order).Term (α ⊕ Fin n)) (s : SignType) (v : α → R)
    (xs : Fin n → R) :
    (t.signFormula s).Realize v xs ↔ SignType.sign (t.realize (Sum.elim v xs)) = s := by
  first
  | have h0 : (func (Sum.inl Ring.zeroFunc) ![] :
        (Language.ring.sum Language.order).Term (α ⊕ Fin n)).realize (Sum.elim v xs) = 0 := by
      simp [realize_eq_aeval_toMvPolynomial]
    cases s <;>
      simp [signFormula, h0, relMap_leSymb (L := Language.ring.sum Language.order),
        sign_eq_neg_one_iff, sign_eq_one_iff]

end FirstOrder.Language.Term

namespace FirstOrder.Language.BoundedFormula

variable {α : Type*} {n : ℕ}

/-- A **quantifier-free formula is a sign condition**. For a quantifier-free formula `φ` of
ordered rings there are finitely many integer polynomials `p i` in the free and bound variables of
`φ`, and a condition `Φ` on their signs, such that in every commutative ring with a compatible
linear order `φ` holds exactly when `Φ` holds of the signs of the values of the `p i`. -/
theorem IsQF.exists_realize_iff_sign {φ : (Language.ring.sum Language.order).BoundedFormula α n}
    (hφ : φ.IsQF) :
    ∃ (m : ℕ) (p : Fin m → MvPolynomial (α ⊕ Fin n) ℤ) (Φ : (Fin m → SignType) → Prop),
      ∀ (R : Type u) [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]
        [LinearOrder R] [IsOrderedAddMonoid R]
        [(Language.ring.sum Language.order).OrderedStructure R] (v : α → R) (xs : Fin n → R),
        φ.Realize v xs ↔ Φ fun i ↦ SignType.sign (aeval (Sum.elim v xs) (p i)) := by
  first
  | induction hφ with
    | falsum => exact ⟨0, finZeroElim, fun _ ↦ False, fun _ _ _ _ _ _ _ _ _ ↦ realize_bot⟩
    | of_isAtomic h =>
      cases h with
      | equal t₁ t₂ =>
        -- `t₁ = t₂` holds exactly when `t₁ - t₂` has sign zero.
        refine ⟨1, ![t₁.toMvPolynomial - t₂.toMvPolynomial], fun s ↦ s 0 = 0,
          fun _ _ _ _ _ _ _ v xs ↦ ?_⟩
        simp [Term.realize_eq_aeval_toMvPolynomial, sub_eq_zero]
      | rel r ts =>
        -- The ring language has no relation symbols; the only one of the order language is `≤`,
        -- and `t₁ ≤ t₂` holds exactly when `t₁ - t₂` is not positive.
        rcases r with r | r
        · exact nomatch r
        · cases r
          refine ⟨1, ![(ts 0).toMvPolynomial - (ts 1).toMvPolynomial], fun s ↦ s 0 ≠ 1,
            fun _ _ _ _ _ _ _ v xs ↦ ?_⟩
          refine (relMap_leSymb (L := Language.ring.sum Language.order) _).trans ?_
          simp [Term.realize_eq_aeval_toMvPolynomial, sign_eq_one_iff]
    | imp _ _ ih₁ ih₂ =>
      -- Concatenate the two lists of polynomials.
      obtain ⟨m₁, p₁, Φ₁, h₁⟩ := ih₁
      obtain ⟨m₂, p₂, Φ₂, h₂⟩ := ih₂
      refine ⟨m₁ + m₂, Fin.append p₁ p₂,
        fun s ↦ Φ₁ (fun i ↦ s (Fin.castAdd m₂ i)) → Φ₂ (fun j ↦ s (Fin.natAdd m₁ j)),
        fun R _ _ _ _ _ _ v xs ↦ ?_⟩
      simp only [realize_imp, h₁ R v xs, h₂ R v xs, Fin.append_left, Fin.append_right]

/-- A **sign condition is a quantifier-free formula**. For finitely many integer polynomials
`p i` and a condition `Φ` on their signs there is a quantifier-free formula of ordered rings which,
in every commutative ring with a compatible linear order, holds exactly when `Φ` holds of the signs
of the values of the `p i`. -/
theorem exists_isQF_realize_iff_sign {ι : Type*} [Finite ι]
    (p : ι → MvPolynomial (α ⊕ Fin n) ℤ) (Φ : (ι → SignType) → Prop) :
    ∃ φ : (Language.ring.sum Language.order).BoundedFormula α n, φ.IsQF ∧
      ∀ (R : Type u) [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]
        [LinearOrder R] [(Language.ring.sum Language.order).OrderedStructure R]
        (v : α → R) (xs : Fin n → R),
        φ.Realize v xs ↔ Φ fun i ↦ SignType.sign (aeval (Sum.elim v xs) (p i)) := by
  first
  | choose t ht using fun i ↦ Term.toMvPolynomial_surjective (p i)
    -- The disjunction, over the sign vectors `s` satisfying `Φ`, of the statements that the
    -- polynomials have the signs `s`.
    refine ⟨iSup fun s : {s // Φ s} ↦ iInf fun i ↦ (t i).signFormula (s.1 i),
      IsQF.iSup fun _ ↦ IsQF.iInf fun _ ↦ Term.isQF_signFormula _ _, fun R _ _ _ _ _ v xs ↦ ?_⟩
    simp only [realize_iSup, realize_iInf, Term.realize_signFormula,
      Term.realize_eq_aeval_toMvPolynomial, ht]
    exact ⟨fun ⟨s, hs⟩ ↦ (funext hs : _ = s.1) ▸ s.2, fun h ↦ ⟨⟨_, h⟩, fun _ ↦ rfl⟩⟩

end FirstOrder.Language.BoundedFormula
end -- closes the original EOF section from source line 46
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/ModelTheory/Algebra/OrderedRing/SignCondition.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Formula.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Semialgebraic sets are the quantifier-free definable sets

Let `R` be a commutative ring with a linear order compatible with addition, regarded as a structure
in the first-order language of ordered rings `Language.ring.sum Language.order`, with the ring
symbols and `≤` interpreted as usual. This file identifies the semialgebraic subsets of `σ → R`,
defined intrinsically as finite Boolean combinations of polynomial zero sets and positivity sets
(`TauCeti.IsSemialgebraic`), with the sets defined by quantifier-free formulas with parameters
from `R`.

* `FirstOrder.Language.BoundedFormula.IsQF.isSemialgebraic_setOf_realize` and
  `FirstOrder.Language.BoundedFormula.IsQF.isSemialgebraic_setOf_formula_realize`: a
  quantifier-free formula without parameters defines a semialgebraic set, since it is a sign
  condition on finitely many integer polynomials
  (`FirstOrder.Language.BoundedFormula.IsQF.exists_realize_iff_sign`).
* `TauCeti.isSemialgebraic_iff_exists_isQF`: a set is semialgebraic if and only if it is defined
  by a quantifier-free formula whose extra variables `Sum.inl r` are assigned the parameters
  `r ∈ R`. The strict inequality `0 < p` is expressed as the negation `¬ p ≤ 0`.
* `TauCeti.IsSemialgebraic.definable`: hence every semialgebraic set is definable with parameters,
  in the sense of Mathlib's `Set.Definable`.

The converse of the last statement, that every definable set is semialgebraic, is quantifier
elimination; over a real closed field it is the Tarski–Seidenberg theorem.
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.QuantifierElimination` derives it from closure of
semialgebraic sets under projection.

To apply these results to a concrete ordered field such as `ℝ`, install the structures
`FirstOrder.Ring.compatibleRingOfRing ℝ` and `FirstOrder.Language.orderStructure ℝ`; the
`OrderedStructure` hypothesis is then found by the instances
`FirstOrder.Language.orderedStructure_orderStructure` and
`FirstOrder.Language.orderedStructure_sum` of `TauCeti.ModelTheory.Order`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2, for semi-algebraic sets as the realizations of quantifier-free formulas.
-/

public section

open FirstOrder FirstOrder.Language MvPolynomial TauCeti

variable {R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]

variable [LinearOrder R] [IsOrderedAddMonoid R]
  [(Language.ring.sum Language.order).OrderedStructure R]

namespace FirstOrder.Language.BoundedFormula.IsQF

variable {α : Type*} {n : ℕ}

/-- A quantifier-free formula of ordered rings, with free variables `α` and `n` bound variables,
defines a semialgebraic subset of `α ⊕ Fin n → R`. -/
theorem isSemialgebraic_setOf_realize {φ : (Language.ring.sum Language.order).BoundedFormula α n}
    (hφ : φ.IsQF) :
    IsSemialgebraic {x : α ⊕ Fin n → R | φ.Realize (x ∘ Sum.inl) (x ∘ Sum.inr)} := by
  first
    -- The formula is a sign condition on finitely many integer polynomials.
  | obtain ⟨m, p, Φ, h⟩ := hφ.exists_realize_iff_sign
    convert isSemialgebraic_setOf_sign_eval (fun i ↦ (p i).map (Int.castRingHom R)) Φ using 3 with x
    rw [h R, Sum.elim_comp_inl_inr]
    simp only [aeval_def, algebraMap_int_eq, eval_map]

/-- A quantifier-free formula of ordered rings with free variables `α` defines a semialgebraic
subset of `α → R`. -/
theorem isSemialgebraic_setOf_formula_realize
    {φ : (Language.ring.sum Language.order).Formula α} (hφ : φ.IsQF) :
    IsSemialgebraic {v : α → R | φ.Realize v} := by
  first
  | convert (hφ.isSemialgebraic_setOf_realize (R := R)).preimage_comp
      (Sum.elim id finZeroElim : α ⊕ Fin 0 → α) using 1
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Formula.Realize, Function.comp_assoc,
      Sum.elim_comp_inl, Function.comp_id]
    exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

end FirstOrder.Language.BoundedFormula.IsQF

namespace TauCeti

variable {σ : Type*}

/-- A subset of `σ → R` is semialgebraic if and only if it is defined by a quantifier-free formula
of ordered rings with parameters from `R`: the formula has free variables `R ⊕ σ`, and each
variable `Sum.inl r` is assigned the value `r`. -/
theorem isSemialgebraic_iff_exists_isQF {s : Set (σ → R)} :
    IsSemialgebraic s ↔ ∃ φ : (Language.ring.sum Language.order).Formula (R ⊕ σ),
      φ.IsQF ∧ s = {v | φ.Realize (Sum.elim id v)} := by
  first
  | constructor
    · intro hs
      refine IsSemialgebraic.induction (fun p => ?_) (fun p => ?_)
        ⟨⊥, BoundedFormula.isQF_bot, by simp⟩
        (fun s _ ⟨φ, hφ, hs⟩ => ⟨φ.not, hφ.not, by ext; simp [hs]⟩)
        (fun s t _ _ ⟨φ, hφ, hs⟩ ⟨ψ, hψ, ht⟩ => ⟨φ ⊔ ψ, hφ.sup hψ, by ext; simp [hs, ht]⟩) hs
      · -- The zero set of `p` is defined by the equation `p = 0`.
        obtain ⟨t, ht⟩ := p.exists_term_realize_eq_eval
        obtain ⟨z, hz⟩ := (0 : MvPolynomial σ R).exists_term_realize_eq_eval
        refine ⟨t.equal z, (BoundedFormula.IsAtomic.equal _ _).isQF, ?_⟩
        ext v
        simp [ht, hz]
      · -- The positivity set of `p` is defined by `¬ p ≤ 0`.
        obtain ⟨t, ht⟩ := p.exists_term_realize_eq_eval
        obtain ⟨z, hz⟩ := (0 : MvPolynomial σ R).exists_term_realize_eq_eval
        refine ⟨(leSymb.formula₂ t z).not, (BoundedFormula.IsAtomic.rel _ _).isQF.not, ?_⟩
        ext v
        simp [ht, hz]
    · rintro ⟨φ, hφ, rfl⟩
      -- Substituting the parameters is a polynomial map.
      have h := hφ.isSemialgebraic_setOf_formula_realize.preimage_eval
        (Sum.elim C X : R ⊕ σ → MvPolynomial σ R)
      have hf : (fun (v : σ → R) i => eval v (Sum.elim C X i)) = fun v => Sum.elim id v := by
        ext v (r | i) <;> simp
      rwa [hf] at h

/-- A semialgebraic subset of `σ → R` is definable in the language of ordered rings with
parameters from `R`. -/
theorem IsSemialgebraic.definable {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    (Set.univ : Set R).Definable (Language.ring.sum Language.order) s := by
  first
  | obtain ⟨φ, -, rfl⟩ := isSemialgebraic_iff_exists_isQF.1 hs
    rw [Set.definable_iff_exists_formula_sum]
    refine ⟨φ.relabel (Sum.map (fun r => ⟨r, Set.mem_univ r⟩) id), ?_⟩
    ext v
    simp only [Set.mem_ofPred_eq, Formula.realize_relabel]
    congr! 1
    ext (r | i) <;> simp

end TauCeti
end -- closes the original EOF section from source line 52
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Formula.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/QuantifierElimination.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Quantifier elimination from projection closure

Let `R` be a commutative ring with a compatible linear order, regarded as a structure in the
first-order language of ordered rings `Language.ring.sum Language.order`. Suppose that semialgebraic
sets are closed under projection: for every semialgebraic `s ⊆ R ^ (n + 1)`, the image
`Fin.tail '' s ⊆ R ^ n` forgetting coordinate `0` is semialgebraic
(`TauCeti.HasSemialgebraicProjections R`). For `ℝ` this is the Tarski–Seidenberg theorem, an
instance proved in `TauCeti.Geometry.RealAlgebraic.CAD.Existence`, so every result below holds
over `ℝ` unconditionally. This file shows that projection closure gives quantifier elimination in
the language of ordered rings, with parameters from `R`.

The argument is by induction on formulas. Atomic formulas define semialgebraic sets, and so do
implications of semialgebraic conditions. An existential quantifier over the last bound variable
is a projection of a semialgebraic set; a universal quantifier is the complement of the existential
quantifier of the complement. The projection hypothesis concerns `R ^ (n + 1)` only, but formulas
may have infinitely many free variables (the parameters are free variables indexed by `R`). Since
membership in a semialgebraic set depends on only finitely many coordinates
(`TauCeti.IsSemialgebraic.exists_finset_mem_iff_of_eqOn`), projections in arbitrary dimension
reduce to the finite-dimensional case.

## Main results

All results but the last assume projection closure, `[TauCeti.HasSemialgebraicProjections R]`.

* `TauCeti.IsSemialgebraic.image_comp_some`: semialgebraic subsets of `Option σ → R` have
  semialgebraic projections to `σ → R`, for every index type `σ`.
* `FirstOrder.Language.BoundedFormula.isSemialgebraic_setOf_realize`,
  `FirstOrder.Language.Formula.isSemialgebraic_setOf_realize`: every formula of ordered rings
  defines a semialgebraic set, and so does every formula whose free variables `Sum.inl a` are
  assigned parameters from `R`
  (`FirstOrder.Language.Formula.isSemialgebraic_setOf_realize_sumElim`).
* `Set.Definable.isSemialgebraic`: every set definable with parameters is semialgebraic, and so
  `TauCeti.isSemialgebraic_iff_definable` identifies the semialgebraic sets with the sets
  definable with parameters from `R`.
* `TauCeti.exists_isQF_realize_iff`: **quantifier elimination**. Every formula of ordered rings
  with parameters from `R` is equivalent, under every assignment of its free variables, to a
  quantifier-free formula with parameters.
* `TauCeti.hasSemialgebraicProjections_iff_forall_definable_isSemialgebraic`: conversely, if every
  definable subset of `R ^ n` is semialgebraic then semialgebraic sets are closed under projection.
  So the projection hypothesis is exactly what quantifier elimination needs.

## References

* S. Basu, R. Pollack, and M.-F. Roy,
  [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
  second edition, Sections 2.3 and 2.4: Tarski–Seidenberg and quantifier elimination.
* D. Marker, *Model Theory: An Introduction*, Graduate Texts in Mathematics 217, Springer (2002),
  Section 3.3.
-/

public section

open FirstOrder FirstOrder.Language MvPolynomial Set TauCeti

section Projection

variable {R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

namespace TauCeti

/-- **Projection in arbitrary dimension.** If semialgebraic subsets of `R ^ (n + 1)` have
semialgebraic projections to `R ^ n`, then for every index type `σ` the projection of a
semialgebraic subset of `Option σ → R`, forgetting the coordinate `none`, is semialgebraic. -/
theorem IsSemialgebraic.image_comp_some
    {σ : Type*} {s : Set (Option σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun x : Option σ → R => x ∘ some) '' s) := by
  first
  | classical
    -- `s` only depends on the coordinate `none` and the coordinates in a finite set `F`.
    obtain ⟨G, hG⟩ := hs.exists_finset_mem_iff_of_eqOn
    set F := G.eraseNone
    set e := F.equivFin
    -- Read off a point of `Option σ → R` from its coordinates `none` and `F`, listed in
    -- `Fin (F.card + 1)`; the other coordinates are set to zero.
    let g : Option σ → MvPolynomial (Fin (F.card + 1)) R := fun o =>
      o.elim (X 0) fun i => if h : i ∈ F then X (e ⟨i, h⟩).succ else 0
    set t := (fun y i => eval y (g i)) ⁻¹' s
    have hg (x : Option σ → R) (y : Fin (F.card + 1) → R) (h0 : y 0 = x none)
        (hF : ∀ i : F, y (e i).succ = x (some i)) : (fun i => eval y (g i)) ∈ s ↔ x ∈ s := by
      refine hG _ _ fun o ho => ?_
      cases o with
      | none => simpa [g] using h0
      | some i =>
        have hi : i ∈ F := Finset.mem_eraseNone.2 ho
        simpa [g, hi] using hF ⟨i, hi⟩
    convert (HasSemialgebraicProjections.isSemialgebraic_image_tail
      (hs.preimage_eval g)).preimage_comp fun j => (e.symm j : σ) using 1
    ext x
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨Fin.cons (z none) (z ∘ some ∘ fun j => (e.symm j : σ)),
        (hg z _ rfl fun i => by simp).2 hz, Fin.tail_cons _ _⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨fun o => o.elim (y 0) x, (hg _ y rfl fun i => ?_).1 hy, rfl⟩
      simpa [Fin.tail] using congrFun hyx (e i)

end TauCeti

/-- The existential quantifier over the last of `n + 1` bound variables preserves
semialgebraicity, given projection closure. -/
private theorem TauCeti.IsSemialgebraic.setOf_exists_sumElim_snoc
    {α : Type*} {n : ℕ} {S : Set (α ⊕ Fin (n + 1) → R)} (hS : IsSemialgebraic S) :
    IsSemialgebraic
      {x : α ⊕ Fin n → R | ∃ a, Sum.elim (x ∘ Sum.inl) (Fin.snoc (x ∘ Sum.inr) a) ∈ S} := by
  first
    -- Single out the last bound variable as the coordinate `none` of `Option (α ⊕ Fin n)`.
  | let g : α ⊕ Fin (n + 1) → Option (α ⊕ Fin n) :=
      Sum.elim (some ∘ Sum.inl) (Fin.snoc (some ∘ Sum.inr) none)
    have hg (z : Option (α ⊕ Fin n) → R) :
        z ∘ g = Sum.elim (z ∘ some ∘ Sum.inl) (Fin.snoc (z ∘ some ∘ Sum.inr) (z none)) := by
      simp [g, Sum.comp_elim, Fin.comp_snoc]
    convert (hS.preimage_comp g).image_comp_some using 1
    ext x
    simp only [mem_ofPred_eq, mem_image, mem_preimage, hg]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨fun o => o.elim a x, ha, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z none, hz⟩

end Projection

variable {R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]
  [LinearOrder R] [IsOrderedAddMonoid R] [(Language.ring.sum Language.order).OrderedStructure R]
  [HasSemialgebraicProjections R]

namespace FirstOrder.Language.BoundedFormula

/-- Given projection closure, a formula of ordered rings with free variables `α` and `n` bound
variables defines a semialgebraic subset of `α ⊕ Fin n → R`. -/
theorem isSemialgebraic_setOf_realize
    {α : Type*} {n : ℕ} (φ : (Language.ring.sum Language.order).BoundedFormula α n) :
    IsSemialgebraic {x : α ⊕ Fin n → R | φ.Realize (x ∘ Sum.inl) (x ∘ Sum.inr)} := by
  first
  | induction φ with
    | falsum => exact isQF_bot.isSemialgebraic_setOf_realize
    | equal t₁ t₂ => exact (IsAtomic.equal t₁ t₂).isQF.isSemialgebraic_setOf_realize
    | rel r ts => exact (IsAtomic.rel r ts).isQF.isSemialgebraic_setOf_realize
    | imp φ ψ ihφ ihψ =>
      simpa [Set.ofPred_or, imp_iff_not_or, Set.compl_ofPred] using ihφ.compl.union ihψ
    | all φ ih =>
      -- `∀ a, φ` is the complement of `∃ a, ¬ φ`.
      convert (IsSemialgebraic.setOf_exists_sumElim_snoc ih.compl).compl using 1
      ext x
      simp

end FirstOrder.Language.BoundedFormula

/-- Given projection closure, a formula of ordered rings with free variables `α` defines a
semialgebraic subset of `α → R`. -/
theorem FirstOrder.Language.Formula.isSemialgebraic_setOf_realize
    {α : Type*} (φ : (Language.ring.sum Language.order).Formula α) :
    IsSemialgebraic {v : α → R | φ.Realize v} := by
  first
  | convert (BoundedFormula.isSemialgebraic_setOf_realize (R := R) φ).preimage_comp
      (Sum.elim id finZeroElim : α ⊕ Fin 0 → α) using 1
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Formula.Realize, Function.comp_assoc,
      Sum.elim_comp_inl, Function.comp_id]
    exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Given projection closure, a formula of ordered rings with free variables `A ⊕ σ` defines a
semialgebraic subset of `σ → R` once the variables `Sum.inl a` are assigned parameters `f a`. -/
theorem FirstOrder.Language.Formula.isSemialgebraic_setOf_realize_sumElim
    {A σ : Type*} (φ : (Language.ring.sum Language.order).Formula (A ⊕ σ)) (f : A → R) :
    IsSemialgebraic {v : σ → R | φ.Realize (Sum.elim f v)} := by
  first
    -- Substituting the parameters is a polynomial map.
  | have h := φ.isSemialgebraic_setOf_realize.preimage_eval
      (Sum.elim (fun a => C (f a)) X : A ⊕ σ → MvPolynomial σ R)
    have hf : (fun (v : σ → R) (i : A ⊕ σ) => eval v (Sum.elim (fun a => C (f a)) X i)) =
        fun v => Sum.elim f v := by
      ext v (a | i) <;> simp
    rwa [hf] at h

/-- Given projection closure, a subset of `σ → R` definable with parameters from a set `A ⊆ R` in
the language of ordered rings is semialgebraic. -/
theorem Set.Definable.isSemialgebraic
    {σ : Type*} {A : Set R} {s : Set (σ → R)}
    (hs : A.Definable (Language.ring.sum Language.order) s) : IsSemialgebraic s := by
  first
  | obtain ⟨φ, rfl⟩ := Set.definable_iff_exists_formula_sum.1 hs
    exact φ.isSemialgebraic_setOf_realize_sumElim _

namespace TauCeti

/-- Given projection closure, a subset of `σ → R` is semialgebraic if and only if it is definable
in the language of ordered rings with parameters from `R`. -/
theorem isSemialgebraic_iff_definable {σ : Type*} {s : Set (σ → R)} :
    IsSemialgebraic s ↔ (Set.univ : Set R).Definable (Language.ring.sum Language.order) s :=
  ⟨IsSemialgebraic.definable, Set.Definable.isSemialgebraic⟩

/-- **Quantifier elimination**, given projection closure. Every formula of ordered rings whose
free variables `Sum.inl r` are assigned the parameters `r ∈ R` is equivalent, for every
assignment `v` of the remaining free variables, to a quantifier-free formula with parameters. -/
theorem exists_isQF_realize_iff {σ : Type*}
    (φ : (Language.ring.sum Language.order).Formula (R ⊕ σ)) :
    ∃ ψ : (Language.ring.sum Language.order).Formula (R ⊕ σ), ψ.IsQF ∧
      ∀ v : σ → R, φ.Realize (Sum.elim id v) ↔ ψ.Realize (Sum.elim id v) := by
  first
  | obtain ⟨ψ, hψ, hs⟩ :=
      isSemialgebraic_iff_exists_isQF.1 (φ.isSemialgebraic_setOf_realize_sumElim id)
    exact ⟨ψ, hψ, fun v => Set.ext_iff.1 hs v⟩

omit [HasSemialgebraicProjections R] in
/-- **Projection closure is equivalent to quantifier elimination.** Semialgebraic subsets of
`R ^ (n + 1)` have semialgebraic projections to `R ^ n`, for every `n`, if and only if every
subset of every `R ^ n` definable with parameters in the language of ordered rings is
semialgebraic. -/
theorem hasSemialgebraicProjections_iff_forall_definable_isSemialgebraic :
    HasSemialgebraicProjections R ↔ ∀ (n : ℕ) (s : Set (Fin n → R)),
      (Set.univ : Set R).Definable (Language.ring.sum Language.order) s → IsSemialgebraic s := by
  first
  | refine ⟨fun _ _ _ => Set.Definable.isSemialgebraic, fun h => ⟨fun hs => ?_⟩⟩
    -- Definable sets are closed under projection.
    exact h _ _ (hs.definable.image_comp Fin.succ)

end TauCeti
end -- closes the original EOF section from source line 61
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/QuantifierElimination.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Image.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Images and composition of semialgebraic functions

Let `R` be a commutative ring with a compatible linear order, and suppose that semialgebraic sets
are closed under projection: for every semialgebraic `s ⊆ R ^ (n + 1)`, the image
`Fin.tail '' s ⊆ R ^ n` forgetting coordinate `0` is semialgebraic
(`TauCeti.HasSemialgebraicProjections R`). For `ℝ` this is the Tarski–Seidenberg theorem, an
instance proved in `TauCeti.Geometry.RealAlgebraic.CAD.Existence`, so every result below holds
over `ℝ` unconditionally. This file develops the parts of the theory of semialgebraic sets and
functions that need projection.

Eliminating one coordinate at a time, the projection of a semialgebraic subset of `σ ⊕ τ → R` onto
the coordinates `τ` is semialgebraic whenever `σ` is finite. Since the graph of a function
`f : (σ → R) → (τ → R)` is encoded as a subset of `σ ⊕ τ → R` (`TauCeti.IsSemialgebraicOn`), this
gives the following consequences.

* The image of a semialgebraic set under a semialgebraic function with finitely many input
  coordinates is semialgebraic, and so is the inverse image of a semialgebraic set under a
  semialgebraic function with finitely many output coordinates.
* The domain of a function with finitely many output coordinates and semialgebraic graph is the
  projection of that graph, so it is semialgebraic: the domain hypothesis in
  `TauCeti.IsSemialgebraicOn` becomes redundant.
* Semialgebraic functions compose when the intermediate space has finitely many coordinates: the
  graph of `g ∘ f` is obtained from the graphs of `f` and `g` by eliminating the intermediate
  coordinates.
* Composing the pair of two semialgebraic functions with a polynomial map shows that pointwise
  sums, products, and differences of semialgebraic functions with finitely many output
  coordinates are semialgebraic, and that the loci where two of them agree, or are ordered, are
  semialgebraic.

## Main results

All results assume projection closure, `[TauCeti.HasSemialgebraicProjections R]`.

* `TauCeti.IsSemialgebraic.image_comp_inr`, `TauCeti.IsSemialgebraic.image_comp_inl`: projections
  of semialgebraic sets that forget finitely many coordinates are semialgebraic.
* `TauCeti.IsSemialgebraicOn.isSemialgebraic_image`,
  `TauCeti.IsSemialgebraicMap.isSemialgebraic_image`: images under semialgebraic functions with
  finitely many input coordinates; `TauCeti.IsSemialgebraic.image_eval`: images under polynomial
  maps with finitely many input and output coordinates.
* `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_preimage`,
  `TauCeti.IsSemialgebraicMap.isSemialgebraic_preimage`: inverse images under semialgebraic
  functions with finitely many output coordinates.
* `TauCeti.isSemialgebraicOn_iff_graph`: a function with finitely many output coordinates is
  semialgebraic on `s` exactly when its graph over `s` is semialgebraic.
* `TauCeti.IsSemialgebraicOn.comp`, `TauCeti.IsSemialgebraicMap.comp`: composition, when the
  intermediate space has finitely many coordinates.
* `TauCeti.IsSemialgebraicOn.eval_comp`: applying a polynomial map to the values;
  `TauCeti.isSemialgebraicOn_sumElim_iff`: a pair is semialgebraic exactly when its components
  are; `TauCeti.IsSemialgebraicOn.add`, `TauCeti.IsSemialgebraicOn.mul`,
  `TauCeti.IsSemialgebraicOn.sub`: pointwise arithmetic.  Negation needs no projection and is
  proved in `TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function`.
* `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_setOf_eq`,
  `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_setOf_le`: the loci where two semialgebraic
  functions agree, or where one is bounded above by the other, are semialgebraic.

## References

* S. Basu, R. Pollack, and M.-F. Roy,
  [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
  second edition, Chapter 2.
* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Section 2.2.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {σ τ υ R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `σ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inr [Finite σ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s) := by
  first
  | revert τ
    refine Finite.induction_empty_option
      (P := fun σ => ∀ {τ : Type _} {s : Set (σ ⊕ τ → R)}, IsSemialgebraic s →
        IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s))
      (fun {α β} e ih {τ} {s} hs => ?_) (fun {τ} {s} hs => ?_)
      (fun {α} _ ih {τ} {s} hs => ?_) σ
    · -- Transport along `e : α ≃ β` in the coordinates to be forgotten.
      convert ih (hs.preimage_comp (Equiv.sumCongr e.symm (Equiv.refl τ))) using 1
      ext y
      simp only [mem_image, mem_preimage]
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z ∘ Equiv.sumCongr e (Equiv.refl τ), ?_, rfl⟩
        convert hz using 1
        ext (b | c) <;> simp
      · rintro ⟨z, hz, rfl⟩
        exact ⟨_, hz, rfl⟩
    · -- With no coordinates to forget, the projection is the bijection `Sum.inr`.
      convert hs.preimage_comp (Equiv.emptySum PEmpty τ) using 1
      ext y
      simp only [mem_image, mem_preimage]
      constructor
      · rintro ⟨z, hz, rfl⟩
        convert hz using 1
        ext (b | c)
        · exact b.elim
        · rfl
      · intro hy
        exact ⟨_, hy, rfl⟩
    · -- Forget the coordinate `none` with `IsSemialgebraic.image_comp_some`, then the coordinates
      -- `α` by induction.
      let k : Option α ⊕ τ → Option (α ⊕ τ) :=
        Sum.elim (Option.elim · none (some ∘ Sum.inl)) (some ∘ Sum.inr)
      convert ih (hs.preimage_comp k).image_comp_some using 1
      ext y
      simp only [mem_image, mem_preimage, exists_exists_and_eq_and]
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(Option.elim · (z (.inl none)) (z ∘ Sum.elim (Sum.inl ∘ some) Sum.inr)), ?_, rfl⟩
        convert hz using 1
        ext ((_ | a) | c) <;> rfl
      · rintro ⟨w, hw, rfl⟩
        exact ⟨_, hw, rfl⟩

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `τ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inl [Finite τ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inl) '' s) := by
  first
  | convert (hs.preimage_comp (Equiv.sumComm σ τ)).image_comp_inr using 1
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z ∘ Equiv.sumComm τ σ, ?_, rfl⟩
      convert hz using 1
      ext (a | b) <;> rfl
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hz, rfl⟩

/-- Given projection closure, the image of the domain of a semialgebraic function with finitely
many input coordinates is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic_image [Finite σ] {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) : IsSemialgebraic (f '' s) := by
  first
  | convert hf.graph.image_comp_inr using 1
    ext y
    simp only [mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Sum.elim x (f x), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hfz⟩, rfl⟩
      exact ⟨_, hz, hfz⟩

/-- Given projection closure, the image of a semialgebraic set under a semialgebraic map with
finitely many input coordinates is semialgebraic. -/
theorem IsSemialgebraicMap.isSemialgebraic_image [Finite σ] {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (f '' s) :=
  (hf.isSemialgebraicOn hs).isSemialgebraic_image

/-- Given projection closure, the image of a semialgebraic set under a polynomial map with finitely
many input coordinates and finitely many output coordinates is semialgebraic. -/
theorem IsSemialgebraic.image_eval [Finite σ] [Finite τ] {s : Set (σ → R)}
    (hs : IsSemialgebraic s) (p : τ → MvPolynomial σ R) :
    IsSemialgebraic ((fun x i => eval x (p i)) '' s) :=
  (isSemialgebraicOn_eval p hs).isSemialgebraic_image

/-- Given projection closure, the points of the domain of a semialgebraic function with finitely
many output coordinates at which it takes values in a semialgebraic set form a semialgebraic
set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_preimage [Finite τ] {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) {t : Set (τ → R)} (ht : IsSemialgebraic t) :
    IsSemialgebraic (s ∩ f ⁻¹' t) := by
  first
  | convert (hf.graph.inter (ht.preimage_comp Sum.inr)).image_comp_inl using 1
    ext x
    simp only [mem_inter_iff, mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨Sum.elim x (f x), ⟨⟨hx, rfl⟩, hfx⟩, rfl⟩
    · rintro ⟨z, ⟨⟨hz, hfz⟩, hzt⟩, rfl⟩
      exact ⟨hz, by rw [mem_preimage, hfz]; exact hzt⟩

/-- Given projection closure, the inverse image of a semialgebraic set under a semialgebraic map
with finitely many output coordinates is semialgebraic. -/
theorem IsSemialgebraicMap.isSemialgebraic_preimage [Finite τ] {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {t : Set (τ → R)} (ht : IsSemialgebraic t) :
    IsSemialgebraic (f ⁻¹' t) := by
  first
  | simpa using (isSemialgebraicOn_univ.2 hf).isSemialgebraic_inter_preimage ht

/-- Given projection closure, a function with finitely many output coordinates is semialgebraic on
`s` if and only if its graph over `s` is semialgebraic: the domain `s` is the projection of the
graph. -/
theorem isSemialgebraicOn_iff_graph [Finite τ] {f : (σ → R) → (τ → R)} {s : Set (σ → R)} :
    IsSemialgebraicOn f s ↔
      IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) := by
  first
  | refine ⟨IsSemialgebraicOn.graph, fun h => isSemialgebraicOn_def.2 ⟨?_, h⟩⟩
    convert h.image_comp_inl using 1
    ext x
    simp only [mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
    constructor
    · intro hx
      exact ⟨Sum.elim x (f x), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨hz, -⟩, rfl⟩
      exact hz

/-- Given projection closure, the composition of semialgebraic functions is semialgebraic: if `f`
is semialgebraic on `s` and maps it into `t`, and `g` is semialgebraic on `t`, then `g ∘ f` is
semialgebraic on `s`. The intermediate space has finitely many coordinates. -/
theorem IsSemialgebraicOn.comp [Finite τ] {g : (τ → R) → (υ → R)} {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} {t : Set (τ → R)} (hg : IsSemialgebraicOn g t)
    (hf : IsSemialgebraicOn f s) (hst : MapsTo f s t) : IsSemialgebraicOn (g ∘ f) s := by
  first
  | refine isSemialgebraicOn_def.2 ⟨hf.isSemialgebraic, ?_⟩
    -- In the coordinates `τ ⊕ (σ ⊕ υ)`, cut out the points `(f x, x, g (f x))` with `x ∈ s` and
    -- forget the intermediate coordinates `τ`.
    convert ((hf.graph.preimage_comp (Sum.elim (Sum.inr ∘ Sum.inl) Sum.inl)).inter
      (hg.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))).image_comp_inr using 1
    ext z
    rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_image]
    constructor
    · rintro ⟨hz, hgz⟩
      exact ⟨Sum.elim (f (z ∘ Sum.inl)) z,
        ⟨mem_preimage_sumArrowEquivProdArrow_graphOn.2 ⟨hz, rfl⟩,
          mem_preimage_sumArrowEquivProdArrow_graphOn.2 ⟨hst hz, hgz⟩⟩, rfl⟩
    · rintro ⟨w, ⟨hwf, hwg⟩, rfl⟩
      obtain ⟨hw, hfw⟩ := mem_preimage_sumArrowEquivProdArrow_graphOn.1 hwf
      obtain ⟨-, hgw⟩ := mem_preimage_sumArrowEquivProdArrow_graphOn.1 hwg
      exact ⟨hw, (congrArg g hfw).trans hgw⟩

/-- Given projection closure, the composition of semialgebraic maps is semialgebraic when the
intermediate space has finitely many coordinates. -/
theorem IsSemialgebraicMap.comp [Finite τ] {g : (τ → R) → (υ → R)} {f : (σ → R) → (τ → R)}
    (hg : IsSemialgebraicMap g) (hf : IsSemialgebraicMap f) : IsSemialgebraicMap (g ∘ f) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hg).comp
    (isSemialgebraicOn_univ.2 hf) (mapsTo_univ f univ)

/-! ### Polynomial operations on semialgebraic functions -/

section Operations

variable {τ' : Type*} {f : (σ → R) → (τ → R)} {s : Set (σ → R)}

/-- Given projection closure, applying a polynomial map to the values of a semialgebraic function
with finitely many output coordinates gives a semialgebraic function. -/
theorem IsSemialgebraicOn.eval_comp [Finite τ] [Finite υ] (hf : IsSemialgebraicOn f s)
    (p : υ → MvPolynomial τ R) :
    IsSemialgebraicOn (fun x i => eval (f x) (p i)) s :=
  (isSemialgebraicOn_eval p isSemialgebraic_univ).comp hf (mapsTo_univ f s)

/-- Given projection closure, a pair of functions with finitely many output coordinates is
semialgebraic exactly when both of its components are. -/
@[simp]
theorem isSemialgebraicOn_sumElim_iff [Finite τ] [Finite τ'] {g : (σ → R) → (τ' → R)} :
    IsSemialgebraicOn (fun x => Sum.elim (f x) (g x)) s ↔
      IsSemialgebraicOn f s ∧ IsSemialgebraicOn g s := by
  first
  | refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1.sumElim h.2⟩
    · simpa using h.eval_comp fun i : τ => X (Sum.inl i)
    · simpa using h.eval_comp fun i : τ' => X (Sum.inr i)

variable [Finite τ] {g : (σ → R) → (τ → R)}

/-- Given projection closure, the pointwise sum of semialgebraic functions is semialgebraic. -/
theorem IsSemialgebraicOn.add (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (f + g) s := by
  first
  | convert (hf.sumElim hg).eval_comp fun i : τ => X (Sum.inl i) + X (Sum.inr i) using 1
    funext x i
    simp

/-- Given projection closure, the pointwise product of semialgebraic functions is
semialgebraic. -/
theorem IsSemialgebraicOn.mul (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (f * g) s := by
  first
  | convert (hf.sumElim hg).eval_comp fun i : τ => X (Sum.inl i) * X (Sum.inr i) using 1
    funext x i
    simp

/-- Given projection closure, the pointwise difference of semialgebraic functions is
semialgebraic. -/
theorem IsSemialgebraicOn.sub (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (f - g) s := by
  first
  | convert (hf.sumElim hg).eval_comp fun i : τ => X (Sum.inl i) - X (Sum.inr i) using 1
    funext x i
    simp

/-- Given projection closure, the pointwise sum of semialgebraic maps is semialgebraic. -/
theorem IsSemialgebraicMap.add (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap (f + g) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).add (isSemialgebraicOn_univ.2 hg)

/-- Given projection closure, the pointwise product of semialgebraic maps is semialgebraic. -/
theorem IsSemialgebraicMap.mul (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap (f * g) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).mul (isSemialgebraicOn_univ.2 hg)

/-- Given projection closure, the pointwise difference of semialgebraic maps is semialgebraic. -/
theorem IsSemialgebraicMap.sub (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap (f - g) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).sub (isSemialgebraicOn_univ.2 hg)

/-- Given projection closure, the points of the common domain at which two semialgebraic
functions agree form a semialgebraic set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_setOf_eq (hf : IsSemialgebraicOn f s)
    (hg : IsSemialgebraicOn g s) : IsSemialgebraic (s ∩ {x | f x = g x}) := by
  first
  | convert (hf.sumElim hg).isSemialgebraic_inter_preimage
      (.iInter fun i : τ => isSemialgebraic_eval_eq (X (Sum.inl i)) (X (Sum.inr i))) using 2
    ext x
    simp [funext_iff]

/-- Given projection closure, the points of the common domain at which one semialgebraic function
is bounded above by another, coordinatewise, form a semialgebraic set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_setOf_le [IsOrderedAddMonoid R]
    (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraic (s ∩ {x | f x ≤ g x}) := by
  first
  | convert (hf.sumElim hg).isSemialgebraic_inter_preimage
      (.iInter fun i : τ => isSemialgebraic_eval_le (X (Sum.inl i)) (X (Sum.inr i))) using 2
    ext x
    simp [Pi.le_def]

end Operations

end TauCeti
end -- closes the original EOF section from source line 76
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Image.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Topology.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Balls, closures and interiors of real semialgebraic sets

This file shows that the basic metric and topological constructions on the real coordinate space
`σ → ℝ`, for a finite index type `σ`, preserve semialgebraicity.

* Open and closed balls are semialgebraic, both for the sup norm, which is the norm Mathlib puts
  on `σ → ℝ`, and for the Euclidean norm of `EuclideanSpace ℝ σ`. In particular every point has
  arbitrarily small open semialgebraic neighbourhoods of either kind.
* The closure, interior and frontier of a semialgebraic set are semialgebraic.

The ball statements only use the polynomial description of the two norms. The closure statement
uses the Tarski–Seidenberg theorem in the form of projection closure
(`TauCeti.HasSemialgebraicProjections ℝ`): a point `x` lies in `closure s` exactly when for every
`ε > 0` there is `y ∈ s` with `dist x y < ε`, and the two quantifiers are eliminated by two
projections and a complement. Interiors and frontiers then follow from closures by complements
and differences.

## Main results

* `TauCeti.isSemialgebraic_setOf_dist_eval_lt`, `TauCeti.isSemialgebraic_setOf_dist_eval_le`:
  the locus where the sup distance between two polynomial maps is bounded by a polynomial is
  semialgebraic.
* `TauCeti.isSemialgebraic_ball`, `TauCeti.isSemialgebraic_closedBall`: sup-norm balls.
* `TauCeti.isSemialgebraic_preimage_toLp_ball`, `TauCeti.isSemialgebraic_preimage_toLp_closedBall`:
  Euclidean balls, read in the coordinates `σ → ℝ`.
* `TauCeti.IsSemialgebraic.closure`, `TauCeti.IsSemialgebraic.interior`,
  `TauCeti.IsSemialgebraic.frontier`.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Proposition 2.2.2.
* S. Basu, R. Pollack, and M.-F. Roy,
  [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
  second edition, Section 3.1.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {σ τ : Type*}

/-! ### Balls -/

/-- The locus where the sup distance between two polynomial maps is less than the value of a
polynomial is semialgebraic. -/
theorem isSemialgebraic_setOf_dist_eval_lt [Fintype σ] (p q : σ → MvPolynomial τ ℝ)
    (r : MvPolynomial τ ℝ) :
    IsSemialgebraic
      {z : τ → ℝ | dist (fun i => eval z (p i)) (fun i => eval z (q i)) < eval z r} := by
  first
  | convert (isSemialgebraic_eval_pos r).inter (IsSemialgebraic.iInter fun i =>
      (isSemialgebraic_eval_lt (-r) (p i - q i)).inter
        (isSemialgebraic_eval_lt (p i - q i) r)) using 1
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, map_neg, map_sub]
    refine ⟨fun h => ?_, fun ⟨hr, h⟩ => ?_⟩
    · have hr : 0 < eval z r := dist_nonneg.trans_lt h
      exact ⟨hr, fun i => abs_lt.1 (by simpa [Real.dist_eq] using (dist_pi_lt_iff hr).1 h i)⟩
    · exact (dist_pi_lt_iff hr).2 fun i => by simpa [Real.dist_eq] using abs_lt.2 (h i)

/-- The locus where the sup distance between two polynomial maps is at most the value of a
polynomial is semialgebraic. -/
theorem isSemialgebraic_setOf_dist_eval_le [Fintype σ] (p q : σ → MvPolynomial τ ℝ)
    (r : MvPolynomial τ ℝ) :
    IsSemialgebraic
      {z : τ → ℝ | dist (fun i => eval z (p i)) (fun i => eval z (q i)) ≤ eval z r} := by
  first
  | convert (isSemialgebraic_eval_nonneg r).inter (IsSemialgebraic.iInter fun i =>
      (isSemialgebraic_eval_le (-r) (p i - q i)).inter
        (isSemialgebraic_eval_le (p i - q i) r)) using 1
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, map_neg, map_sub]
    refine ⟨fun h => ?_, fun ⟨hr, h⟩ => ?_⟩
    · have hr : 0 ≤ eval z r := dist_nonneg.trans h
      exact ⟨hr, fun i => abs_le.1 (by simpa [Real.dist_eq] using (dist_pi_le_iff hr).1 h i)⟩
    · exact (dist_pi_le_iff hr).2 fun i => by simpa [Real.dist_eq] using abs_le.2 (h i)

/-- An open ball for the sup norm on `σ → ℝ` is semialgebraic. -/
theorem isSemialgebraic_ball [Fintype σ] (x : σ → ℝ) (r : ℝ) :
    IsSemialgebraic (Metric.ball x r) := by
  first
  | simpa [Metric.ball] using
      isSemialgebraic_setOf_dist_eval_lt (fun i => X i) (fun i => C (x i)) (C r)

/-- A closed ball for the sup norm on `σ → ℝ` is semialgebraic. -/
theorem isSemialgebraic_closedBall [Fintype σ] (x : σ → ℝ) (r : ℝ) :
    IsSemialgebraic (Metric.closedBall x r) := by
  first
  | simpa [Metric.closedBall] using
      isSemialgebraic_setOf_dist_eval_le (fun i => X i) (fun i => C (x i)) (C r)

/-- An open ball of the Euclidean space `EuclideanSpace ℝ σ`, read in the coordinates `σ → ℝ`, is
semialgebraic. -/
theorem isSemialgebraic_preimage_toLp_ball [Fintype σ] (x : EuclideanSpace ℝ σ) (r : ℝ) :
    IsSemialgebraic (WithLp.toLp 2 ⁻¹' Metric.ball x r : Set (σ → ℝ)) := by
  first
  | convert (isSemialgebraic_eval_pos (C r)).inter
      (isSemialgebraic_eval_lt (∑ i, (X i - C (x i)) ^ 2) (C r ^ 2)) using 1
    ext y
    have hS : 0 ≤ ∑ i, (y i - x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    simp only [mem_preimage, Metric.mem_ball, EuclideanSpace.dist_eq,
      Real.dist_eq, sq_abs, mem_inter_iff, mem_ofPred_eq, eval_C, map_sum, map_pow, map_sub, eval_X]
    refine ⟨fun h => ?_, fun ⟨hr, h⟩ => (Real.sqrt_lt' hr).2 h⟩
    have hr : 0 < r := (Real.sqrt_nonneg _).trans_lt h
    exact ⟨hr, (Real.sqrt_lt' hr).1 h⟩

/-- A closed ball of the Euclidean space `EuclideanSpace ℝ σ`, read in the coordinates `σ → ℝ`,
is semialgebraic. -/
theorem isSemialgebraic_preimage_toLp_closedBall [Fintype σ] (x : EuclideanSpace ℝ σ) (r : ℝ) :
    IsSemialgebraic (WithLp.toLp 2 ⁻¹' Metric.closedBall x r : Set (σ → ℝ)) := by
  first
  | convert (isSemialgebraic_eval_nonneg (C r)).inter
      (isSemialgebraic_eval_le (∑ i, (X i - C (x i)) ^ 2) (C r ^ 2)) using 1
    ext y
    simp only [mem_preimage, Metric.mem_closedBall, EuclideanSpace.dist_eq,
      Real.dist_eq, sq_abs, mem_inter_iff, mem_ofPred_eq, eval_C, map_sum, map_pow, map_sub, eval_X,
      Real.sqrt_le_iff]

/-! ### Closures, interiors and frontiers -/

/-- The closure of a semialgebraic subset of `σ → ℝ` is semialgebraic. -/
theorem IsSemialgebraic.closure [Finite σ] {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (closure s) := by
  first
  | cases nonempty_fintype σ
    -- In the coordinates `(σ ⊕ Unit) ⊕ σ`, a point `z` encodes a centre `x = z ∘ inl ∘ inl`, a
    -- radius `ε = z (inl (inr ()))` and a point `y = z ∘ inr`; `T` says `y ∈ s` and `dist x y < ε`.
    let T : Set ((σ ⊕ Unit) ⊕ σ → ℝ) := (fun z => z ∘ Sum.inr) ⁻¹' s ∩
      {z | dist (fun i => eval z (X (.inl (.inl i)))) (fun i => eval z (X (.inr i))) <
        eval z (X (.inl (.inr ())))}
    have hT : IsSemialgebraic T :=
      (hs.preimage_comp _).inter (isSemialgebraic_setOf_dist_eval_lt _ _ _)
    -- Projecting away `y`, then the radius among the `ε > 0` for which no such `y` exists, gives
    -- the complement of the closure.
    let A : Set (σ ⊕ Unit → ℝ) := (fun z => z ∘ Sum.inl) '' T
    have hB : IsSemialgebraic ((fun w : σ ⊕ Unit → ℝ => w ∘ Sum.inl) ''
        ({w | 0 < eval w (X (.inr ()))} ∩ Aᶜ)) :=
      ((isSemialgebraic_eval_pos _).inter hT.image_comp_inl.compl).image_comp_inl
    convert hB.compl using 1
    ext x
    have hA (ε : ℝ) : Sum.elim x (fun _ => ε) ∈ A ↔ ∃ y ∈ s, dist x y < ε := by
      constructor
      · rintro ⟨z, ⟨hzs, hzd⟩, hz⟩
        refine ⟨z ∘ Sum.inr, hzs, ?_⟩
        have hx : (fun i => z (.inl (.inl i))) = x := funext fun i => congrFun hz (.inl i)
        have hε : z (.inl (.inr ())) = ε := congrFun hz (.inr ())
        simpa [hx, hε, Function.comp_def] using hzd
      · rintro ⟨y, hys, hy⟩
        exact ⟨Sum.elim (Sum.elim x fun _ => ε) y, ⟨hys, by simpa using hy⟩, rfl⟩
    simp only [Metric.mem_closure_iff, mem_compl_iff, mem_image, mem_inter_iff, mem_ofPred_eq,
      eval_X, not_exists, not_and]
    refine ⟨fun h w ⟨hw, hwA⟩ hwx => hwA ?_, fun h ε hε => ?_⟩
    · have hw' : w = Sum.elim x fun _ => w (.inr ()) := by
        ext (i | ⟨⟩)
        · exact congrFun hwx i
        · rfl
      rw [hw', hA]
      exact h _ hw
    · by_contra hne
      exact h (Sum.elim x fun _ => ε) ⟨hε, fun hA' => hne ((hA ε).1 hA')⟩ rfl

/-- The interior of a semialgebraic subset of `σ → ℝ` is semialgebraic. -/
theorem IsSemialgebraic.interior [Finite σ] {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (interior s) := by
  first
  | rw [interior_eq_compl_closure_compl]
    exact hs.compl.closure.compl

/-- The frontier of a semialgebraic subset of `σ → ℝ` is semialgebraic. -/
theorem IsSemialgebraic.frontier [Finite σ] {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (frontier s) :=
  hs.closure.sdiff hs.interior

end TauCeti
end -- closes the original EOF section from source line 50
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Semialgebraic/Topology.lean -/

/- BEGIN SOURCE: VolumePolynomials/FullDimensionalPolytopes.lean -/
section

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace VolumePolynomials

/-- No complexity or vertex bound is imposed on the polytopes. This is a transfer
lemma: the nonsemialgebraicity of the full convex-body locus must be established
before applying it. -/
theorem fullDimensionalPolytopeLocus_not_semialgebraic_of_volumeLocus
    {n d : ℕ} (hd : 0 < d) (h : ¬ TauCeti.IsSemialgebraic (VolumeLocus n d)) :
    ¬ TauCeti.IsSemialgebraic (FullDimensionalPolytopeLocus n d) := by
  first
  | intro hp
    apply h
    rw [← closure_fullDimensionalPolytopeLocus n d hd]
    exact hp.closure

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FullDimensionalPolytopes.lean -/

/- BEGIN SOURCE: VolumePolynomials/MainSemialgebraicity.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # The sharp algebraic threshold

Both loci below retain every homogeneous coefficient. The polytope locus
requires each realizing body to be full dimensional and places no bound
on its number of vertices or facets.
-/

namespace VolumePolynomials.Main

theorem volumeLocus_not_semialgebraic {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus n d) := by
  first
  | apply not_semialgebraic_volumeLocus_of_three hn
    have heq : 3 + (d - 3) = d := by omega
    rw [← heq]
    exact HigherLift.volumeLocus_not_semialgebraic (d - 3)

/-- Theorem 1.1, for every number of bodies and every dimension in the
stated range, with realizability defined by actual Lebesgue volume. -/
theorem semialgebraicity_iff {n d : ℕ} (hn : 1 ≤ n) (hd : 3 ≤ d) :
    TauCeti.IsSemialgebraic (VolumeLocus n d) ↔ n ≤ 2 := by
  first
  | constructor
    · intro h
      by_contra hn2
      exact volumeLocus_not_semialgebraic (by omega) hd h
    · exact isSemialgebraic_volumeLocus_of_le_two hn (by omega)

/-- The full-dimensional polytope clause of Theorem 1.1. -/
theorem polytope_locus_not_semialgebraic {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ TauCeti.IsSemialgebraic (FullDimensionalPolytopeLocus n d) :=
  fullDimensionalPolytopeLocus_not_semialgebraic_of_volumeLocus (by omega)
    (volumeLocus_not_semialgebraic hn hd)

end VolumePolynomials.Main
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MainSemialgebraicity.lean -/

/- BEGIN SOURCE: VolumePolynomials/ShapeConditions.lean -/
section


@[expose] public section
noncomputable section

/-!
# A finite rational shape-forcing system

This is an evaluation form of the coefficient conditions in Section 7.  Its
unknowns are the two parameters and all ordinary cubic coefficients in nine
variables.  The polynomial `volumeSymbol w` is the ordinary coefficient
polynomial evaluated at the symbolic weight vector `w`.

The system has 39 equations and eight strict inequalities.  No mixed-volume
coefficient, geometric equality case, or realization condition is built into
its definition.  Membership in the actual volume locus is imposed separately.
-/

open scoped BigOperators

namespace VolumePolynomials.ShapeConditions

abbrev Label := Fin 9
abbrev Variable := Fin 2 ⊕ MultiIndex 9 3
abbrev RationalPolynomial := MvPolynomial Variable ℚ

def e₁ : Label := 0
def e₂ : Label := 1
def e₃ : Label := 2
def sᵥ : Label := 3
def s𝓌 : Label := 4
def s𝓏 : Label := 5
/-- Exact natural bound for the distinguished body label. -/
theorem palomarBodyAIndexBound : (6 : ℕ) < 9 := by decide
/-- Exact natural bound for the first of the two parameter positions. -/
theorem palomarAssignmentIndexBound : (0 : ℕ) < 2 := by decide

def bodyA : Label := ⟨6, palomarBodyAIndexBound⟩
def bodyB : Label := 7
def bodyC : Label := 8

def segmentIndex (i : Fin 6) : Label := i.castLE (by decide)
def frameIndex (i : Fin 3) : Label := i.castLE (by decide)

def parameter : RationalPolynomial := MvPolynomial.X (Sum.inl 0)
def areaParameter : RationalPolynomial := MvPolynomial.X (Sum.inl 1)

def unitWeight {R : Type*} [Zero R] [One R] (i : Label) : Label → R :=
  fun j => if j = i then 1 else 0

def volumeSymbol (w : Label → RationalPolynomial) : RationalPolynomial :=
  ∑ α : MultiIndex 9 3,
    MvPolynomial.X (Sum.inr α) * ∏ i, w i ^ (α.1 i : ℕ)

def extrusionSymbol (w : Label → RationalPolynomial) (h : Label) : RationalPolynomial :=
  volumeSymbol (w + unitWeight h) - volumeSymbol w

def lastWeight : Label → RationalPolynomial :=
  fun i => parameter * unitWeight bodyC i + unitWeight e₁ i

/-- The eighteen zero-volume tests force all six calibrated labels to have
affine dimension at most one, once the frame has positive total volume. -/
def segmentEquations : List RationalPolynomial :=
  (List.finRange 6).flatMap fun h =>
    (List.finRange 3).map fun j =>
      volumeSymbol (unitWeight (segmentIndex h) + unitWeight (frameIndex j))

/-- Explicit equations, with the unspecified cubic coefficients left free. -/
def equations : List RationalPolynomial := segmentEquations ++
  [ volumeSymbol (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight sᵥ + unitWeight e₂ + unitWeight e₃),
    volumeSymbol (unitWeight sᵥ + unitWeight e₁ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight sᵥ + unitWeight e₁ + unitWeight e₂) - 1,
    volumeSymbol (unitWeight s𝓌 + unitWeight e₂ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₂),
    volumeSymbol (unitWeight s𝓏 + unitWeight e₂ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₃) -
      MvPolynomial.C (2 / 3 : ℚ),
    volumeSymbol (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₂) - 1,
    volumeSymbol (unitWeight sᵥ + unitWeight s𝓌 + unitWeight s𝓏) -
      MvPolynomial.C (4 / 3 : ℚ),
    volumeSymbol (unitWeight bodyA + unitWeight e₁ + unitWeight e₂),
    volumeSymbol (unitWeight bodyB + unitWeight e₁ + unitWeight e₃),
    volumeSymbol (unitWeight bodyC + unitWeight e₂ + unitWeight e₃),
    extrusionSymbol (unitWeight bodyA) sᵥ - extrusionSymbol (unitWeight bodyB) sᵥ,
    extrusionSymbol (unitWeight bodyA + unitWeight bodyB) sᵥ -
      4 * extrusionSymbol (unitWeight bodyA) sᵥ,
    extrusionSymbol (unitWeight bodyB) s𝓌 - extrusionSymbol (unitWeight bodyC) s𝓌,
    extrusionSymbol (unitWeight bodyB + unitWeight bodyC) s𝓌 -
      4 * extrusionSymbol (unitWeight bodyB) s𝓌,
    extrusionSymbol (unitWeight bodyA) s𝓏 - extrusionSymbol lastWeight s𝓏,
    extrusionSymbol (unitWeight bodyA + lastWeight) s𝓏 -
      4 * extrusionSymbol (unitWeight bodyA) s𝓏,
    areaParameter - extrusionSymbol (unitWeight bodyA) e₃ ]

def inequalities : List RationalPolynomial :=
  [ parameter, 1 - parameter,
    extrusionSymbol (unitWeight bodyA) e₃,
    extrusionSymbol (unitWeight bodyB) e₂,
    extrusionSymbol (unitWeight bodyC) e₁,
    extrusionSymbol (unitWeight bodyA) sᵥ,
    extrusionSymbol (unitWeight bodyB) s𝓌,
    extrusionSymbol (unitWeight bodyA) s𝓏 ]

def assignment (lam a : ℝ) (c : Coefficients 9 3) : Variable → ℝ :=
  Sum.elim (fun i => if i = (⟨0, palomarAssignmentIndexBound⟩ : Fin 2) then lam else a) c

def polynomialValue (lam a : ℝ) (c : Coefficients 9 3) : RationalPolynomial →+* ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (assignment lam a c)

def Holds (lam a : ℝ) (c : Coefficients 9 3) : Prop :=
  (∀ p ∈ equations, polynomialValue lam a c p = 0) ∧
  (∀ p ∈ inequalities, 0 < polynomialValue lam a c p)

/-- The actual geometric locus is not absorbed into the polynomial tests. -/
def Feasible (lam a : ℝ) : Prop :=
  ∃ c ∈ VolumeLocus 9 3, Holds lam a c

def extrusionValue (V : (Label → ℝ) → ℝ) (w : Label → ℝ) (h : Label) : ℝ :=
  V (w + unitWeight h) - V w

def lastNumericalWeight (lam : ℝ) : Label → ℝ :=
  fun i => lam * unitWeight bodyC i + unitWeight e₁ i

/-- The exact ordinary-volume meaning of the finite rational system. -/
def OrdinaryConditions (lam a : ℝ) (V : (Label → ℝ) → ℝ) : Prop :=
  (∀ h : Fin 6, ∀ j : Fin 3,
    V (unitWeight (segmentIndex h) + unitWeight (frameIndex j)) = 0) ∧
  (V (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) = 1 ∧
    V (unitWeight sᵥ + unitWeight e₂ + unitWeight e₃) = 0 ∧
    V (unitWeight sᵥ + unitWeight e₁ + unitWeight e₃) = 1 ∧
    V (unitWeight sᵥ + unitWeight e₁ + unitWeight e₂) = 1 ∧
    V (unitWeight s𝓌 + unitWeight e₂ + unitWeight e₃) = 1 ∧
    V (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₃) = 1 ∧
    V (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₂) = 0 ∧
    V (unitWeight s𝓏 + unitWeight e₂ + unitWeight e₃) = 1 ∧
    V (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₃) = (2 / 3 : ℝ) ∧
    V (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₂) = 1 ∧
    V (unitWeight sᵥ + unitWeight s𝓌 + unitWeight s𝓏) = (4 / 3 : ℝ) ∧
    V (unitWeight bodyA + unitWeight e₁ + unitWeight e₂) = 0 ∧
    V (unitWeight bodyB + unitWeight e₁ + unitWeight e₃) = 0 ∧
    V (unitWeight bodyC + unitWeight e₂ + unitWeight e₃) = 0 ∧
    extrusionValue V (unitWeight bodyA) sᵥ = extrusionValue V (unitWeight bodyB) sᵥ ∧
    extrusionValue V (unitWeight bodyA + unitWeight bodyB) sᵥ =
      4 * extrusionValue V (unitWeight bodyA) sᵥ ∧
    extrusionValue V (unitWeight bodyB) s𝓌 = extrusionValue V (unitWeight bodyC) s𝓌 ∧
    extrusionValue V (unitWeight bodyB + unitWeight bodyC) s𝓌 =
      4 * extrusionValue V (unitWeight bodyB) s𝓌 ∧
    extrusionValue V (unitWeight bodyA) s𝓏 = extrusionValue V (lastNumericalWeight lam) s𝓏 ∧
    extrusionValue V (unitWeight bodyA + lastNumericalWeight lam) s𝓏 =
      4 * extrusionValue V (unitWeight bodyA) s𝓏 ∧
    a = extrusionValue V (unitWeight bodyA) e₃) ∧
  (0 < lam ∧ lam < 1 ∧
    0 < extrusionValue V (unitWeight bodyA) e₃ ∧
    0 < extrusionValue V (unitWeight bodyB) e₂ ∧
    0 < extrusionValue V (unitWeight bodyC) e₁ ∧
    0 < extrusionValue V (unitWeight bodyA) sᵥ ∧
    0 < extrusionValue V (unitWeight bodyB) s𝓌 ∧
    0 < extrusionValue V (unitWeight bodyA) s𝓏)

@[simp] theorem equations_length : equations.length = 39 := by
  first
  | simp [equations, segmentEquations, List.length_flatMap, List.map_const]

@[simp] theorem inequalities_length : inequalities.length = 8 := rfl

@[simp] theorem polynomialValue_parameter (lam a : ℝ) (c : Coefficients 9 3) :
    polynomialValue lam a c parameter = lam := by
  first
  | simp [polynomialValue, parameter, assignment]

@[simp] theorem polynomialValue_areaParameter (lam a : ℝ) (c : Coefficients 9 3) :
    polynomialValue lam a c areaParameter = a := by
  first
  | simp [polynomialValue, areaParameter, assignment]

@[simp] theorem polynomialValue_coefficient (lam a : ℝ) (c : Coefficients 9 3)
    (α : MultiIndex 9 3) :
    polynomialValue lam a c (MvPolynomial.X (Sum.inr α)) = c α := by
  first
  | simp [polynomialValue, assignment]

@[simp] theorem polynomialValue_C (lam a : ℝ) (c : Coefficients 9 3) (r : ℚ) :
    polynomialValue lam a c (MvPolynomial.C r) = (r : ℝ) := by
  first
  | simp [polynomialValue]

@[simp] theorem polynomialValue_unitWeight (lam a : ℝ) (c : Coefficients 9 3)
    (i j : Label) :
    polynomialValue lam a c (unitWeight i j) = unitWeight i j := by
  first
  | simp [unitWeight]

/-- Symbolic evaluation is exactly ordinary polynomial evaluation, with no
factorial rescaling of the ordinary coefficients. -/
@[simp] theorem polynomialValue_volumeSymbol (lam a : ℝ) (c : Coefficients 9 3)
    (w : Label → RationalPolynomial) :
    polynomialValue lam a c (volumeSymbol w) =
      evaluate c (fun i => polynomialValue lam a c (w i)) := by
  first
  | classical
    simp [volumeSymbol, evaluate]

@[simp] theorem polynomialValue_extrusionSymbol (lam a : ℝ) (c : Coefficients 9 3)
    (w : Label → RationalPolynomial) (h : Label) :
    polynomialValue lam a c (extrusionSymbol w h) =
      evaluate c ((fun i => polynomialValue lam a c (w i)) + unitWeight h) -
      evaluate c (fun i => polynomialValue lam a c (w i)) := by
  first
  | simp [extrusionSymbol, Pi.add_def]

@[simp] theorem polynomialValue_lastWeight (lam a : ℝ) (c : Coefficients 9 3)
    (i : Label) :
    polynomialValue lam a c (lastWeight i) =
      lam * unitWeight bodyC i + unitWeight e₁ i := by
  first
  | simp [lastWeight]

theorem holds_iff_ordinary (lam a : ℝ) (c : Coefficients 9 3) :
    Holds lam a c ↔ OrdinaryConditions lam a (evaluate c) := by
  first
  | simp only [Holds, equations, List.forall_mem_append, segmentEquations,
      List.forall_mem_flatMap, List.forall_mem_map]
    simp [inequalities, OrdinaryConditions, extrusionValue, lastNumericalWeight,
      Pi.add_def, map_ofNat, sub_eq_zero, sub_pos, and_assoc]
    all_goals
      intros
      rfl

theorem Holds.parameter_range {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) : 0 < lam ∧ lam < 1 := by
  first
  | have h₀ := h.2 parameter (by simp [inequalities])
    have h₁ := h.2 (1 - parameter) (by simp [inequalities])
    simp only [polynomialValue_parameter, map_sub, map_one] at h₀ h₁
    exact ⟨h₀, sub_pos.mp h₁⟩

theorem Holds.segment_zero {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) (i : Fin 6) (j : Fin 3) :
    evaluate c (unitWeight (segmentIndex i) + unitWeight (frameIndex j)) = 0 := by
  first
  | have hm : volumeSymbol (unitWeight (segmentIndex i) + unitWeight (frameIndex j)) ∈
        equations := by
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_finRange i, ?_⟩
      exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    simpa [Pi.add_def] using h.1 _ hm

theorem Holds.frame_volume {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) :
    evaluate c (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) = 1 := by
  first
  | have hm := h.1 (volumeSymbol (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) - 1)
      (by simp [equations])
    simpa [Pi.add_def, sub_eq_zero] using hm

theorem Holds.area_value {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) :
    a = evaluate c (unitWeight bodyA + unitWeight e₃) - evaluate c (unitWeight bodyA) := by
  first
  | have hm := h.1 (areaParameter - extrusionSymbol (unitWeight bodyA) e₃)
      (by simp [equations])
    simpa [Pi.add_def, sub_eq_zero] using hm

end VolumePolynomials.ShapeConditions
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ShapeConditions.lean -/

/- BEGIN SOURCE: VolumePolynomials/ShapeTuple.lean -/
section


@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

def axis (i : Fin 3) : ThreeSpace := Pi.single i 1

def calibratedDirection : Fin 6 → ThreeSpace :=
  ![axis 0, axis 1, axis 2, directionV, directionW, directionZ]

/-- A centered segment of the specified full generating vector. -/
def centeredBody (v : ThreeSpace) : Body 3 :=
  segmentBody (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)

theorem centeredBody_carrier (v : ThreeSpace) :
    (centeredBody v : Set ThreeSpace) =
      (fun t : ℝ => t • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  first
  | have h := image_segment ℝ (LinearMap.toSpanSingleton ℝ ThreeSpace v).toAffineMap
      (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
    rw [segment_eq_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] at h
    exact h.symm

theorem zero_mem_centeredBody (v : ThreeSpace) : (0 : ThreeSpace) ∈ centeredBody v := by
  first
  | change (0 : ThreeSpace) ∈ (centeredBody v : Set ThreeSpace)
    rw [centeredBody_carrier]
    exact ⟨0, ⟨by norm_num, by norm_num⟩, zero_smul ℝ v⟩

theorem centeredBody_eq_translate (v : ThreeSpace) :
    centeredBody v = translateBody (-(1 / 2 : ℝ) • v) (segmentBody 0 v) := by
  first
  | rw [translate_segmentBody, add_zero]
    have heq : -(1 / 2 : ℝ) • v + v = (1 / 2 : ℝ) • v := by
      calc
        _ = (-(1 / 2 : ℝ) + 1) • v := by rw [add_smul, one_smul]
        _ = _ := by norm_num
    rw [heq]
    rfl

@[simp] theorem centeredBody_zero : centeredBody (0 : ThreeSpace) = 0 := by
  first
  | apply ConvexBody.ext
    change segment ℝ (-(1 / 2 : ℝ) • (0 : ThreeSpace))
      ((1 / 2 : ℝ) • (0 : ThreeSpace)) = ({0} : Set ThreeSpace)
    simp

theorem centeredBody_smul_sign (s : ℝ) (hs : |s| = 1) (v : ThreeSpace) :
    centeredBody (s • v) = centeredBody v := by
  first
  | rcases eq_or_eq_neg_of_abs_eq hs with rfl | rfl
    · simp
    · apply ConvexBody.ext
      simp only [centeredBody, coe_segmentBody, neg_one_smul, smul_neg, neg_smul, neg_neg,
        one_smul]
      simpa only [neg_smul] using
        (segment_symm ℝ ((1 / 2 : ℝ) • v) (-(1 / 2 : ℝ) • v))

@[simp] theorem map_centeredBody (g : ThreeSpace →L[ℝ] ThreeSpace) (v : ThreeSpace) :
    mapBody g (centeredBody v) = centeredBody (g v) := by
  first
  | simp only [centeredBody, map_segmentBody, map_smul]

/-- The coordinate-normalized geometry needed by the projected comparison
argument.  The last three bodies remain arbitrary compact convex sets. -/
structure IsCalibratedTuple (K : Fin 9 → Body 3) : Prop where
  segments : ∀ i : Fin 6,
    K (ShapeConditions.segmentIndex i) = centeredBody (calibratedDirection i)
  zeroA : (0 : ThreeSpace) ∈ K ShapeConditions.bodyA
  zeroB : (0 : ThreeSpace) ∈ K ShapeConditions.bodyB
  zeroC : (0 : ThreeSpace) ∈ K ShapeConditions.bodyC
  planeA : ∀ x ∈ K ShapeConditions.bodyA, x 2 = 0
  planeB : ∀ x ∈ K ShapeConditions.bodyB, x 1 = 0
  planeC : ∀ x ∈ K ShapeConditions.bodyC, x 0 = 0

/-- Provenance of a normalized tuple: one common volume-preserving linear
equivalence and independent translations of the original bodies. -/
def AffinelyNormalized (K K' : Fin 9 → Body 3) : Prop :=
  ∃ g : ThreeSpace ≃L[ℝ] ThreeSpace,
    |LinearMap.det g.toLinearMap| = 1 ∧
    ∃ t : Fin 9 → ThreeSpace, ∀ i,
      K' i = mapBody g.toContinuousLinearMap (translateBody (t i) (K i))

namespace AffinelyNormalized

theorem refl (K : Fin 9 → Body 3) : AffinelyNormalized K K := by
  first
  | refine ⟨ContinuousLinearEquiv.refl ℝ ThreeSpace, ?_, fun _ => 0, ?_⟩
    · change |LinearMap.det (LinearMap.id : ThreeSpace →ₗ[ℝ] ThreeSpace)| = 1
      rw [LinearMap.det_id, abs_one]
    · intro i
      rw [translateBody_zero]
      apply ConvexBody.ext
      exact (Set.image_id' (K i : Set ThreeSpace)).symm

theorem of_translate (K : Fin 9 → Body 3) (t : Fin 9 → ThreeSpace) :
    AffinelyNormalized K (fun i => translateBody (t i) (K i)) := by
  first
  | refine ⟨ContinuousLinearEquiv.refl ℝ ThreeSpace, ?_, t, ?_⟩
    · change |LinearMap.det (LinearMap.id : ThreeSpace →ₗ[ℝ] ThreeSpace)| = 1
      rw [LinearMap.det_id, abs_one]
    · intro i
      apply ConvexBody.ext
      exact (Set.image_id' (translateBody (t i) (K i) : Set ThreeSpace)).symm

theorem of_map (K : Fin 9 → Body 3) (g : ThreeSpace ≃L[ℝ] ThreeSpace)
    (hg : |LinearMap.det g.toLinearMap| = 1) :
    AffinelyNormalized K (fun i => mapBody g.toContinuousLinearMap (K i)) := by
  first
  | exact ⟨g, hg, fun _ => 0, fun i => by rw [translateBody_zero]⟩

theorem trans {K L M : Fin 9 → Body 3}
    (hKL : AffinelyNormalized K L) (hLM : AffinelyNormalized L M) :
    AffinelyNormalized K M := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    obtain ⟨h, hh, u, hu⟩ := hLM
    refine ⟨g.trans h, ?_, fun i => t i + g.symm (u i), ?_⟩
    · change |LinearMap.det (h.toLinearMap.comp g.toLinearMap)| = 1
      rw [LinearMap.det_comp, abs_mul, hh, hg, mul_one]
    · intro i
      rw [hu i, ht i]
      change mapBody h.toContinuousLinearMap
        (translateBody (u i) (mapBody g.toContinuousLinearMap
          (translateBody (t i) (K i)))) =
        mapBody (h.toContinuousLinearMap.comp g.toContinuousLinearMap)
          (translateBody (t i + g.symm (u i)) (K i))
      rw [← mapBody_comp]
      simp only [mapBody_translate, translateBody_translate, map_add,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, add_comm]

theorem preservesRealizes {K L : Fin 9 → Body 3} {c : Coefficients 9 3}
    (hKL : AffinelyNormalized K L) (hK : Realizes K c) : Realizes L c := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    have h := (hK.translate t).map_of_abs_det_one g.toContinuousLinearMap hg
    have heq : L = fun i => mapBody g.toContinuousLinearMap
        (translateBody (t i) (K i)) := funext ht
    rw [heq]
    exact h

theorem volumeFunction_eq {K L : Fin 9 → Body 3}
    (hKL : AffinelyNormalized K L) : volumeFunction L = volumeFunction K := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    have heq : L = fun i => mapBody g.toContinuousLinearMap
        (translateBody (t i) (K i)) := funext ht
    funext w
    rw [heq, volumeFunction_map]
    change |LinearMap.det g.toLinearMap| *
      volumeFunction (fun i => translateBody (t i) (K i)) w = volumeFunction K w
    rw [hg, one_mul, volumeFunction_translate]

end AffinelyNormalized

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ShapeTuple.lean -/

/- BEGIN SOURCE: VolumePolynomials/FrameCalibration.lean -/
section


@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.Holonomy

/-- The usual oriented determinant of three column vectors. -/
def determinant3 (v w z : ThreeSpace) : ℝ :=
  v 0 * (w 1 * z 2 - w 2 * z 1) -
    v 1 * (w 0 * z 2 - w 2 * z 0) +
    v 2 * (w 0 * z 1 - w 1 * z 0)

theorem frameColumnMap_toMatrix_apply (v : Fin 3 → ThreeSpace) (i j : Fin 3) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (frameColumnMap v).toLinearMap i j = v j i := by
  first
  | simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    exact congrFun (frameColumnMap_basis v j) i

theorem frameColumnMap_det_three (v w z : ThreeSpace) :
    LinearMap.det (frameColumnMap ![v, w, z]).toLinearMap = determinant3 v w z := by
  first
  | rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)), Matrix.det_fin_three]
    simp only [frameColumnMap_toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, determinant3]
    ring

/-- This determinant identity is for actual Lebesgue volume of actual segments. -/
theorem volume_three_origin_segments (v w z : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 w + segmentBody 0 z) =
      |determinant3 v w z| := by
  first
  | have h := bodyVolume_sum_origin_segments ![v, w, z]
    rw [frameColumnMap_det_three] at h
    simpa [Fin.sum_univ_three] using h

theorem volume_coordinate_test₁ (v : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 (Pi.single 1 1) +
      segmentBody 0 (Pi.single 2 1)) = |v 0| := by
  first
  | rw [volume_three_origin_segments]
    simp [determinant3, Pi.single_apply]

theorem volume_coordinate_test₂ (v : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 (Pi.single 0 1) +
      segmentBody 0 (Pi.single 2 1)) = |v 1| := by
  first
  | rw [volume_three_origin_segments]
    simp [determinant3, Pi.single_apply]

theorem volume_coordinate_test₃ (v : ThreeSpace) :
    bodyVolume (segmentBody 0 v + segmentBody 0 (Pi.single 0 1) +
      segmentBody 0 (Pi.single 1 1)) = |v 2| := by
  first
  | rw [volume_three_origin_segments]
    simp [determinant3, Pi.single_apply]

theorem determinant3_of_zero_coordinates (v w z : ThreeSpace)
    (hv : v 0 = 0) (hw : w 2 = 0) :
    determinant3 v w z =
      -(w 0) * v 1 * z 2 + w 0 * v 2 * z 1 - z 0 * v 2 * w 1 := by
  first
  | simp only [determinant3, hv, hw]
    ring

theorem calibrated_determinant : |determinant3 directionV directionW directionZ| =
    (4 / 3 : ℝ) := by
  first
  | norm_num [determinant3, directionV, directionW, directionZ]

private theorem sign_mul_self (s : ThreeSpace) (hs : ∀ i, |s i| = 1) (i : Fin 3) :
    s i * s i = 1 := by
  first
  | nlinarith [sq_abs (s i), hs i]

/-- Coordinate reflections as a genuine continuous linear equivalence. -/
def coordinateReflection (s : ThreeSpace) (hs : ∀ i, |s i| = 1) : ThreeSpace ≃L[ℝ] ThreeSpace where
  toFun x i := s i * x i
  invFun x i := s i * x i
  left_inv x := by
    first
    | funext i
      change s i * (s i * x i) = x i
      rw [← mul_assoc, sign_mul_self s hs, one_mul]
  right_inv x := by
    first
    | funext i
      change s i * (s i * x i) = x i
      rw [← mul_assoc, sign_mul_self s hs, one_mul]
  map_add' x y := by funext i; dsimp; ring
  map_smul' c x := by funext i; dsimp; ring
  continuous_toFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i))
  continuous_invFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i))

@[simp] theorem coordinateReflection_apply (s : ThreeSpace) (hs : ∀ i, |s i| = 1)
    (x : ThreeSpace) (i : Fin 3) : coordinateReflection s hs x i = s i * x i := rfl

theorem coordinateReflection_basis (s : ThreeSpace) (hs : ∀ i, |s i| = 1) (i : Fin 3) :
    coordinateReflection s hs (Pi.single i 1) = s i • (Pi.single i 1 : ThreeSpace) := by
  first
  | funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Pi.single_apply, hj, Ne.symm hj]

theorem coordinateReflection_abs_det (s : ThreeSpace) (hs : ∀ i, |s i| = 1) :
    |LinearMap.det (coordinateReflection s hs).toLinearMap| = 1 := by
  first
  | have hm : LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
        (coordinateReflection s hs).toLinearMap = Matrix.diagonal s := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [LinearMap.toMatrix_apply, Pi.basisFun_apply]
      · simp [LinearMap.toMatrix_apply, Pi.basisFun_apply, Matrix.diagonal_apply,
          Pi.single_apply, hij, Ne.symm hij]
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)), hm, Matrix.det_diagonal,
      Finset.abs_prod]
    simp [hs]

/-- The determinant calibration provides one common volume-preserving reflection
and independent orientations of the three oblique segment vectors. -/
theorem calibrate_vectors (v w z : ThreeSpace)
    (hv₀ : v 0 = 0) (hv₁ : |v 1| = 1) (hv₂ : |v 2| = 1)
    (hw₀ : |w 0| = 1) (hw₁ : |w 1| = 1) (hw₂ : w 2 = 0)
    (hz₀ : |z 0| = 1) (hz₁ : |z 1| = (2 / 3 : ℝ)) (hz₂ : |z 2| = 1)
    (hdet : |determinant3 v w z| = (4 / 3 : ℝ)) :
    ∃ g : ThreeSpace ≃L[ℝ] ThreeSpace,
      |LinearMap.det g.toLinearMap| = 1 ∧
      (∀ i : Fin 3, ∃ s : ℝ, |s| = 1 ∧
        g (Pi.single i 1) = s • (Pi.single i 1 : ThreeSpace)) ∧
      ∃ rv rw rz : ℝ, |rv| = 1 ∧ |rw| = 1 ∧ |rz| = 1 ∧
        g (rv • v) = directionV ∧ g (rw • w) = directionW ∧ g (rz • z) = directionZ := by
  first
  | rw [determinant3_of_zero_coordinates v w z hv₀ hw₂] at hdet
    obtain ⟨s₁, s₃, rv, rw, rz, hs₁, hs₃, hrv, hrw, hrz,
        hV₁, hV₂, hW₀, hW₁, hZ₀, hZ₁, hZ₂⟩ :=
      calibration_signs (v 1) (v 2) (w 0) (w 1) (z 0) (z 1) (z 2)
        hv₁ hv₂ hw₀ hw₁ hz₀ hz₁ hz₂ hdet
    let s : ThreeSpace := ![s₁, 1, s₃]
    have hs : ∀ i, |s i| = 1 := by
      intro i
      fin_cases i <;> simp [s, hs₁, hs₃]
    refine ⟨coordinateReflection s hs, coordinateReflection_abs_det s hs,
      fun i => ⟨s i, hs i, coordinateReflection_basis s hs i⟩,
      rv, rw, rz, hrv, hrw, hrz, ?_, ?_, ?_⟩
    · funext i
      change s i * (rv * v i) = directionV i
      fin_cases i
      · simp [s, directionV, hv₀]
      · simpa [s, directionV] using hV₁
      · simpa [s, directionV, mul_comm, mul_left_comm, mul_assoc] using hV₂
    · funext i
      change s i * (rw * w i) = directionW i
      fin_cases i
      · simpa [s, directionW, mul_comm, mul_left_comm, mul_assoc] using hW₀
      · simpa [s, directionW] using hW₁
      · simp [s, directionW, hw₂]
    · funext i
      change s i * (rz * z i) = directionZ i
      fin_cases i
      · simpa [s, directionZ, mul_comm, mul_left_comm, mul_assoc] using hZ₀
      · simpa [s, directionZ] using hZ₁
      · simpa [s, directionZ, mul_comm, mul_left_comm, mul_assoc] using hZ₂


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FrameCalibration.lean -/

/- BEGIN SOURCE: VolumePolynomials/ShapeEvaluation.lean -/
section


@[expose] public section
noncomputable section

open scoped Pointwise

namespace VolumePolynomials.ShapeConditions

theorem unitWeight_nonneg (i : Label) : ∀ j, (0 : ℝ) ≤ unitWeight i j := by
  first
  | intro j
    simp only [unitWeight]
    split <;> norm_num

theorem unitWeight_eq_single (i : Label) :
    (unitWeight i : Label → ℝ) = Pi.single i 1 := by
  first
  | funext j
    simp [unitWeight, Pi.single_apply]

theorem lastNumericalWeight_nonneg (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ i, 0 ≤ lastNumericalWeight lam i := by
  first
  | intro i
    exact add_nonneg (mul_nonneg hlam (unitWeight_nonneg bodyC i)) (unitWeight_nonneg e₁ i)

@[simp] theorem weightedSum_unitWeight (K : Label → Body 3) (i : Label) :
    weightedSum K (unitWeight i) = K i := by
  first
  | rw [unitWeight_eq_single, weightedSum_single, one_smul]

@[simp] theorem weightedSum_two (K : Label → Body 3) (i j : Label) :
    weightedSum K (unitWeight i + unitWeight j) = K i + K j := by
  first
  | rw [weightedSum_add K _ _ (unitWeight_nonneg i) (unitWeight_nonneg j),
      weightedSum_unitWeight, weightedSum_unitWeight]

@[simp] theorem weightedSum_three (K : Label → Body 3) (i j k : Label) :
    weightedSum K (unitWeight i + unitWeight j + unitWeight k) = K i + K j + K k := by
  first
  | rw [weightedSum_add K (unitWeight i + unitWeight j) (unitWeight k)
      (fun l => add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l))
      (unitWeight_nonneg k), weightedSum_two, weightedSum_unitWeight]

@[simp] theorem weightedSum_last (K : Label → Body 3) (lam : ℝ) (hlam : 0 ≤ lam) :
    weightedSum K (lastNumericalWeight lam) = lam • K bodyC + K e₁ := by
  first
  | have hweight : lastNumericalWeight lam =
        Pi.single bodyC lam + (unitWeight e₁ : Label → ℝ) := by
      funext i
      simp only [lastNumericalWeight, unitWeight, Pi.add_apply, Pi.single_apply]
      split <;> simp_all
    rw [hweight, weightedSum_add]
    · rw [weightedSum_single, weightedSum_unitWeight]
    · intro i
      simp only [Pi.single_apply]
      split <;> simp_all
    · exact unitWeight_nonneg e₁

theorem extrusionValue_volume (K : Label → Body 3) (w : Label → ℝ) (h : Label)
    (hw : ∀ i, 0 ≤ w i) :
    extrusionValue (volumeFunction K) w h =
      bodyVolume (weightedSum K w + K h) - bodyVolume (weightedSum K w) := by
  first
  | simp only [extrusionValue, volumeFunction]
    rw [weightedSum_add K _ _ hw (unitWeight_nonneg h), weightedSum_unitWeight]

theorem OrdinaryConditions.congr_nonnegative {lam a : ℝ}
    {V W : (Label → ℝ) → ℝ} (hlam : 0 ≤ lam)
    (hVW : ∀ w, (∀ i, 0 ≤ w i) → V w = W w) :
    OrdinaryConditions lam a V ↔ OrdinaryConditions lam a W := by
  first
  | have hunit (i : Label) : V (unitWeight i) = W (unitWeight i) :=
      hVW (unitWeight i) (unitWeight_nonneg i)
    have hpair (i j : Label) :
        V (unitWeight i + unitWeight j) = W (unitWeight i + unitWeight j) :=
      hVW (unitWeight i + unitWeight j)
        (fun k => add_nonneg (unitWeight_nonneg i k) (unitWeight_nonneg j k))
    have htriple (i j k : Label) :
        V (unitWeight i + unitWeight j + unitWeight k) =
          W (unitWeight i + unitWeight j + unitWeight k) :=
      hVW (unitWeight i + unitWeight j + unitWeight k)
        (fun l => add_nonneg
          (add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l))
          (unitWeight_nonneg k l))
    have hlast : V (lastNumericalWeight lam) = W (lastNumericalWeight lam) :=
      hVW (lastNumericalWeight lam) (lastNumericalWeight_nonneg lam hlam)
    have hlast_add (i : Label) :
        V (lastNumericalWeight lam + unitWeight i) =
          W (lastNumericalWeight lam + unitWeight i) :=
      hVW (lastNumericalWeight lam + unitWeight i)
        (fun k => add_nonneg (lastNumericalWeight_nonneg lam hlam k)
          (unitWeight_nonneg i k))
    have hadd_last (i : Label) :
        V (unitWeight i + lastNumericalWeight lam) =
          W (unitWeight i + lastNumericalWeight lam) :=
      hVW (unitWeight i + lastNumericalWeight lam)
        (fun k => add_nonneg (unitWeight_nonneg i k)
          (lastNumericalWeight_nonneg lam hlam k))
    have hadd_last_add (i j : Label) :
        V (unitWeight i + lastNumericalWeight lam + unitWeight j) =
          W (unitWeight i + lastNumericalWeight lam + unitWeight j) :=
      hVW (unitWeight i + lastNumericalWeight lam + unitWeight j)
        (fun k => add_nonneg
          (add_nonneg (unitWeight_nonneg i k) (lastNumericalWeight_nonneg lam hlam k))
          (unitWeight_nonneg j k))
    simp only [OrdinaryConditions, extrusionValue, hunit, hpair, htriple,
      hlast, hlast_add, hadd_last, hadd_last_add]

/-- Exact equivalence of symbolic coefficient tests and their literal geometric
volume evaluations, proved using only weights in the nonnegative orthant. -/
theorem holds_iff_ordinary_volume {lam a : ℝ} {c : Coefficients 9 3}
    {K : Label → Body 3} (hlam : 0 ≤ lam) (hK : Realizes K c) :
    Holds lam a c ↔ OrdinaryConditions lam a (volumeFunction K) := by
  first
  | rw [holds_iff_ordinary]
    exact OrdinaryConditions.congr_nonnegative hlam hK

theorem Holds.ordinary_volume {lam a : ℝ} {c : Coefficients 9 3}
    {K : Label → Body 3} (h : Holds lam a c) (hK : Realizes K c) :
    OrdinaryConditions lam a (volumeFunction K) :=
  (holds_iff_ordinary_volume h.parameter_range.1.le hK).mp h

end VolumePolynomials.ShapeConditions
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ShapeEvaluation.lean -/

/- BEGIN SOURCE: VolumePolynomials/ShapeNormalization.lean -/
section

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.Holonomy
open ShapeConditions

@[simp] theorem weightedSum_unitWeight_pair (K : Fin 9 → Body 3) (i j : Label) :
    weightedSum K (unitWeight i + unitWeight j) = K i + K j := by
  first
  | rw [weightedSum_add K _ _ (unitWeight_nonneg i) (unitWeight_nonneg j)]
    simp only [weightedSum_unitWeight]

@[simp] theorem weightedSum_unitWeight_triple (K : Fin 9 → Body 3) (i j k : Label) :
    weightedSum K (unitWeight i + unitWeight j + unitWeight k) = K i + K j + K k := by
  first
  | rw [weightedSum_add K (unitWeight i + unitWeight j) (unitWeight k)
      (fun h => add_nonneg (unitWeight_nonneg i h)
      (unitWeight_nonneg j h)) (unitWeight_nonneg k)]
    simp only [weightedSum_unitWeight_pair, weightedSum_unitWeight]

@[simp] theorem volumeFunction_unitWeight_pair (K : Fin 9 → Body 3) (i j : Label) :
    volumeFunction K (unitWeight i + unitWeight j) = bodyVolume (K i + K j) := by
  first
  | simp only [volumeFunction, weightedSum_unitWeight_pair]

@[simp] theorem volumeFunction_unitWeight_triple (K : Fin 9 → Body 3) (i j k : Label) :
    volumeFunction K (unitWeight i + unitWeight j + unitWeight k) =
      bodyVolume (K i + K j + K k) := by
  first
  | simp only [volumeFunction, weightedSum_unitWeight_triple]

/-- The frame and plane constraints read from literal volume evaluations.
This is a proved consequence of `OrdinaryConditions`, not an extra hypothesis
in the eventual shape-forcing theorem. -/
structure BasicCalibration (K : Fin 9 → Body 3) : Prop where
  segmentZero : ∀ i : Fin 6, ∀ j : Fin 3,
    bodyVolume (K (segmentIndex i) + K (frameIndex j)) = 0
  frameVolume : bodyVolume (K e₁ + K e₂ + K e₃) = 1
  v₀ : bodyVolume (K sᵥ + K e₂ + K e₃) = 0
  v₁ : bodyVolume (K sᵥ + K e₁ + K e₃) = 1
  v₂ : bodyVolume (K sᵥ + K e₁ + K e₂) = 1
  w₀ : bodyVolume (K s𝓌 + K e₂ + K e₃) = 1
  w₁ : bodyVolume (K s𝓌 + K e₁ + K e₃) = 1
  w₂ : bodyVolume (K s𝓌 + K e₁ + K e₂) = 0
  z₀ : bodyVolume (K s𝓏 + K e₂ + K e₃) = 1
  z₁ : bodyVolume (K s𝓏 + K e₁ + K e₃) = (2 / 3 : ℝ)
  z₂ : bodyVolume (K s𝓏 + K e₁ + K e₂) = 1
  obliqueVolume : bodyVolume (K sᵥ + K s𝓌 + K s𝓏) = (4 / 3 : ℝ)
  planeA : bodyVolume (K bodyA + K e₁ + K e₂) = 0
  planeB : bodyVolume (K bodyB + K e₁ + K e₃) = 0
  planeC : bodyVolume (K bodyC + K e₂ + K e₃) = 0

theorem OrdinaryConditions.basicCalibration {lam a : ℝ} {K : Fin 9 → Body 3}
    (h : OrdinaryConditions lam a (volumeFunction K)) : BasicCalibration K := by
  first
  | obtain ⟨hf, hv₀, hv₁, hv₂, hw₀, hw₁, hw₂, hz₀, hz₁, hz₂,
      hs, hA, hB, hC, _⟩ := h.2.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      simpa only [volumeFunction_unitWeight_pair] using h.1 i j
    all_goals
      first
      | simpa only [volumeFunction_unitWeight_triple] using hf
      | simpa only [volumeFunction_unitWeight_triple] using hv₀
      | simpa only [volumeFunction_unitWeight_triple] using hv₁
      | simpa only [volumeFunction_unitWeight_triple] using hv₂
      | simpa only [volumeFunction_unitWeight_triple] using hw₀
      | simpa only [volumeFunction_unitWeight_triple] using hw₁
      | simpa only [volumeFunction_unitWeight_triple] using hw₂
      | simpa only [volumeFunction_unitWeight_triple] using hz₀
      | simpa only [volumeFunction_unitWeight_triple] using hz₁
      | simpa only [volumeFunction_unitWeight_triple] using hz₂
      | simpa only [volumeFunction_unitWeight_triple] using hs
      | simpa only [volumeFunction_unitWeight_triple] using hA
      | simpa only [volumeFunction_unitWeight_triple] using hB
      | simpa only [volumeFunction_unitWeight_triple] using hC

theorem BasicCalibration.segments {K : Fin 9 → Body 3} (h : BasicCalibration K)
    (hzero : ∀ i, (0 : ThreeSpace) ∈ K i) :
    ∀ i : Fin 6, ∃ x y : ThreeSpace,
      x ∈ K (segmentIndex i) ∧ y ∈ K (segmentIndex i) ∧
      K (segmentIndex i) = segmentBody x y := by
  first
  | intro i
    obtain ⟨x, y, hx, hy, hxy⟩ := body_is_segment_of_three_zero_volumes
      (K (segmentIndex i)) (K e₁) (K e₂) (K e₃)
      (hzero _) (hzero _) (hzero _) (hzero _)
      (h.segmentZero i 0) (h.segmentZero i 1) (h.segmentZero i 2)
      (by rw [h.frameVolume]; exact zero_lt_one)
    exact ⟨x, y, hx, hy, body_eq_segmentBody hxy⟩

/-- Independent translations put every body through the origin and put an
endpoint of each of the six forced segments at the origin. -/
theorem normalize_segment_origins {lam a : ℝ} (K : Label → Body 3)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ L : Label → Body 3, ∃ u : Fin 6 → ThreeSpace,
      AffinelyNormalized K L ∧
      (∀ i, (0 : ThreeSpace) ∈ L i) ∧
      (∀ i, L (segmentIndex i) = segmentBody 0 (u i)) ∧
      OrdinaryConditions lam a (volumeFunction L) := by
  first
  | classical
    choose p hp using fun i => (K i).nonempty
    let K₀ : Label → Body 3 := fun i => translateBody (-p i) (K i)
    have hK₀ : AffinelyNormalized K K₀ := AffinelyNormalized.of_translate K _
    have hz₀ : ∀ i, (0 : ThreeSpace) ∈ K₀ i :=
      fun i => zero_mem_translateBody_neg (hp i)
    have hc₀ : OrdinaryConditions lam a (volumeFunction K₀) := by
      rw [hK₀.volumeFunction_eq]
      exact hcond
    choose x y hx hy hxy using BasicCalibration.segments
      (OrdinaryConditions.basicCalibration hc₀) hz₀
    let t : Label → ThreeSpace := fun i => if h : i.val < 6 then -x ⟨i.val, h⟩ else 0
    let L : Label → Body 3 := fun i => translateBody (t i) (K₀ i)
    have hL : AffinelyNormalized K₀ L := AffinelyNormalized.of_translate K₀ t
    refine ⟨L, fun i => y i - x i, hK₀.trans hL, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < 6
      · let j : Fin 6 := ⟨i.val, hi⟩
        have hji : segmentIndex j = i := Fin.ext rfl
        have hx' : x j ∈ K₀ i := by rw [← hji]; exact hx j
        simpa only [L, t, dif_pos hi] using zero_mem_translateBody_neg hx'
      · simpa only [L, t, dif_neg hi, translateBody_zero] using hz₀ i
    · intro i
      have ht : t (segmentIndex i) = -x i := by
        simp only [t, segmentIndex, Fin.coe_castLE, dif_pos i.isLt]
      change translateBody (t (segmentIndex i)) (K₀ (segmentIndex i)) = _
      rw [ht, hxy i, translate_segmentBody, neg_add_cancel, neg_add_eq_sub]
    · rw [hL.volumeFunction_eq]
      exact hc₀

/-- A common determinant-one change of coordinates fixes the frame vectors
exactly.  Its hypotheses still concern the actual nine convex bodies. -/
theorem normalize_coordinate_frame {lam a : ℝ} (K : Label → Body 3)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ L : Label → Body 3, ∃ u : Fin 6 → ThreeSpace,
      AffinelyNormalized K L ∧
      (∀ i, (0 : ThreeSpace) ∈ L i) ∧
      (∀ i, L (segmentIndex i) = segmentBody 0 (u i)) ∧
      (∀ i : Fin 3, u (i.castLE (by decide)) = axis i) ∧
      OrdinaryConditions lam a (volumeFunction L) := by
  first
  | obtain ⟨P, v, hKP, hzero, hseg, hP⟩ := normalize_segment_origins K hcond
    let vf : Fin 3 → ThreeSpace := fun i => v (i.castLE (by decide))
    have hframe : bodyVolume (∑ i, segmentBody 0 (vf i)) = 1 := by
      simp only [Fin.sum_univ_three, vf, ← hseg, segmentIndex]
      change bodyVolume (P e₁ + P e₂ + P e₃) = 1
      exact (OrdinaryConditions.basicCalibration hP).frameVolume
    obtain ⟨g, hg, hgv⟩ := normalize_origin_segment_frame vf hframe
    let L : Label → Body 3 := fun i => mapBody g.toContinuousLinearMap (P i)
    have hPL : AffinelyNormalized P L := AffinelyNormalized.of_map P g hg
    refine ⟨L, fun i => g (v i), hKP.trans hPL, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨0, hzero i, map_zero g⟩
    · intro i
      change mapBody g.toContinuousLinearMap (P (segmentIndex i)) = _
      rw [hseg, map_segmentBody, map_zero]
      change segmentBody (0 : Space 3) (g (v i)) = segmentBody 0 (g (v i))
      rfl
    · exact hgv
    · rw [hPL.volumeFunction_eq]
      exact hP

/-- A linear map preserving all three coordinate axes preserves each of the
three coordinate planes. -/
theorem coordinate_zero_of_axis_preserving (g : ThreeSpace →L[ℝ] ThreeSpace)
    (hg : ∀ i : Fin 3, ∃ s : ℝ, g (axis i) = s • axis i)
    (x : ThreeSpace) (k : Fin 3) (hx : x k = 0) : g x k = 0 := by
  first
  | classical
    have hdecomp : x = ∑ i : Fin 3, x i • axis i := by
      ext j
      simp [axis, Pi.single_apply]
    rw [hdecomp, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨s, hs⟩ := hg i
    by_cases hik : i = k
    · subst i
      simp only [hx, zero_mul]
    · rw [hs]
      simp [axis, Pi.single_apply, hik, Ne.symm hik]

theorem mapBody_zero_mem (g : ThreeSpace →L[ℝ] ThreeSpace) {K : Body 3}
    (hK : (0 : ThreeSpace) ∈ K) : (0 : ThreeSpace) ∈ mapBody g K :=
  ⟨0, hK, map_zero g⟩

theorem mapBody_coordinate_zero (g : ThreeSpace →L[ℝ] ThreeSpace)
    (hg : ∀ i : Fin 3, ∃ s : ℝ, g (axis i) = s • axis i)
    {K : Body 3} {k : Fin 3} (hK : ∀ x ∈ K, x k = 0) :
    ∀ x ∈ mapBody g K, x k = 0 := by
  first
  | rintro _ ⟨x, hx, rfl⟩
    exact coordinate_zero_of_axis_preserving g hg x k (hK x hx)

/-- Complete calibration from the finite volume tests.  No segment, plane,
normalization, or Minkowski equality is assumed in this statement. -/
theorem normalize_shape_conditions (lam a : ℝ) (K : Label → Body 3)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ L, AffinelyNormalized K L ∧ IsCalibratedTuple L := by
  first
  | classical
    obtain ⟨Q, u, hKQ, hz, hseg, haxis, hQ⟩ := normalize_coordinate_frame K hcond
    have hc : BasicCalibration Q := OrdinaryConditions.basicCalibration hQ
    have hu₀ : u 0 = axis 0 := by
      have h := haxis 0
      change u 0 = axis 0 at h
      exact h
    have hu₁ : u 1 = axis 1 := by
      have h := haxis 1
      change u 1 = axis 1 at h
      exact h
    have hu₂ : u 2 = axis 2 := by
      have h := haxis 2
      change u 2 = axis 2 at h
      exact h
    have he₁ : Q e₁ = segmentBody 0 (axis 0) := by
      have h := hseg 0
      change Q e₁ = segmentBody 0 (u 0) at h
      exact h.trans (congrArg (segmentBody 0) hu₀)
    have he₂ : Q e₂ = segmentBody 0 (axis 1) := by
      have h := hseg 1
      change Q e₂ = segmentBody 0 (u 1) at h
      exact h.trans (congrArg (segmentBody 0) hu₁)
    have he₃ : Q e₃ = segmentBody 0 (axis 2) := by
      have h := hseg 2
      change Q e₃ = segmentBody 0 (u 2) at h
      exact h.trans (congrArg (segmentBody 0) hu₂)
    have hv : Q sᵥ = segmentBody 0 (u 3) := hseg 3
    have hw : Q s𝓌 = segmentBody 0 (u 4) := hseg 4
    have hzseg : Q s𝓏 = segmentBody 0 (u 5) := hseg 5
    have hv₀ : u 3 0 = 0 := by
      have h := hc.v₀
      simp only [hv, he₂, he₃, axis, volume_coordinate_test₁] at h
      exact abs_eq_zero.mp h
    have hv₁ : |u 3 1| = 1 := by
      simpa only [hv, he₁, he₃, axis, volume_coordinate_test₂] using hc.v₁
    have hv₂ : |u 3 2| = 1 := by
      simpa only [hv, he₁, he₂, axis, volume_coordinate_test₃] using hc.v₂
    have hw₀ : |u 4 0| = 1 := by
      simpa only [hw, he₂, he₃, axis, volume_coordinate_test₁] using hc.w₀
    have hw₁ : |u 4 1| = 1 := by
      simpa only [hw, he₁, he₃, axis, volume_coordinate_test₂] using hc.w₁
    have hw₂ : u 4 2 = 0 := by
      have h := hc.w₂
      simp only [hw, he₁, he₂, axis, volume_coordinate_test₃] at h
      exact abs_eq_zero.mp h
    have hz₀ : |u 5 0| = 1 := by
      simpa only [hzseg, he₂, he₃, axis, volume_coordinate_test₁] using hc.z₀
    have hz₁ : |u 5 1| = (2 / 3 : ℝ) := by
      simpa only [hzseg, he₁, he₃, axis, volume_coordinate_test₂] using hc.z₁
    have hz₂ : |u 5 2| = 1 := by
      simpa only [hzseg, he₁, he₂, axis, volume_coordinate_test₃] using hc.z₂
    have hd : |determinant3 (u 3) (u 4) (u 5)| = (4 / 3 : ℝ) := by
      simpa only [hv, hw, hzseg, volume_three_origin_segments] using hc.obliqueVolume
    obtain ⟨g, hg, hga, rv, rw, rz, hrv, hrw, hrz, hgv, hgw, hgz⟩ :=
      calibrate_vectors (u 3) (u 4) (u 5)
        hv₀ hv₁ hv₂ hw₀ hw₁ hw₂ hz₀ hz₁ hz₂ hd
    have hga' : ∀ i : Fin 3, ∃ s : ℝ, g (axis i) = s • axis i :=
      fun i => ⟨(hga i).choose, (hga i).choose_spec.2⟩
    have hplaneA : ∀ x ∈ Q bodyA, x 2 = 0 := by
      apply coordinate_eq_zero_of_volume_zero (Q bodyA) 0 1 2
        (by decide) (by decide) (by decide) (hz bodyA)
      simpa only [he₁, he₂, coordinateSegment, axis] using hc.planeA
    have hplaneB : ∀ x ∈ Q bodyB, x 1 = 0 := by
      apply coordinate_eq_zero_of_volume_zero (Q bodyB) 0 2 1
        (by decide) (by decide) (by decide) (hz bodyB)
      simpa only [he₁, he₃, coordinateSegment, axis] using hc.planeB
    have hplaneC : ∀ x ∈ Q bodyC, x 0 = 0 := by
      apply coordinate_eq_zero_of_volume_zero (Q bodyC) 1 2 0
        (by decide) (by decide) (by decide) (hz bodyC)
      simpa only [he₂, he₃, coordinateSegment, axis] using hc.planeC
    let R : Label → Body 3 := fun i => mapBody g.toContinuousLinearMap (Q i)
    let t : Label → ThreeSpace := fun i => if h : i.val < 6 then
      -(1 / 2 : ℝ) • g (u ⟨i.val, h⟩) else 0
    let L : Label → Body 3 := fun i => translateBody (t i) (R i)
    have hQR : AffinelyNormalized Q R := AffinelyNormalized.of_map Q g hg
    have hRL : AffinelyNormalized R L := AffinelyNormalized.of_translate R t
    refine ⟨L, (hKQ.trans hQR).trans hRL, ?_⟩
    have hLseg : ∀ i : Fin 6, L (segmentIndex i) = centeredBody (g (u i)) := by
      intro i
      have ht : t (segmentIndex i) = -(1 / 2 : ℝ) • g (u i) := by
        simp only [t, segmentIndex, Fin.coe_castLE, dif_pos i.isLt]
      change translateBody (t (segmentIndex i))
        (mapBody g.toContinuousLinearMap (Q (segmentIndex i))) = _
      rw [ht, hseg, map_segmentBody, map_zero]
      change translateBody (-(1 / 2 : ℝ) • g (u i)) (segmentBody 0 (g (u i))) =
        centeredBody (g (u i))
      exact (centeredBody_eq_translate (g (u i))).symm
    have hLA : L bodyA = R bodyA := by simp [L, t, bodyA]
    have hLB : L bodyB = R bodyB := by simp [L, t, bodyB]
    have hLC : L bodyC = R bodyC := by simp [L, t, bodyC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [hLseg]
      fin_cases i
      · obtain ⟨s, hs, he⟩ := hga 0
        change centeredBody (g (u 0)) = centeredBody (axis 0)
        change g (axis 0) = s • axis 0 at he
        rw [hu₀, he, centeredBody_smul_sign s hs]
      · obtain ⟨s, hs, he⟩ := hga 1
        change centeredBody (g (u 1)) = centeredBody (axis 1)
        change g (axis 1) = s • axis 1 at he
        rw [hu₁, he, centeredBody_smul_sign s hs]
      · obtain ⟨s, hs, he⟩ := hga 2
        change centeredBody (g (u 2)) = centeredBody (axis 2)
        change g (axis 2) = s • axis 2 at he
        rw [hu₂, he, centeredBody_smul_sign s hs]
      · change centeredBody (g (u 3)) = centeredBody directionV
        calc
          centeredBody (g (u 3)) = centeredBody (rv • g (u 3)) :=
            (centeredBody_smul_sign rv hrv _).symm
          _ = centeredBody (g (rv • u 3)) := congrArg centeredBody (map_smul g rv (u 3)).symm
          _ = centeredBody directionV := congrArg centeredBody hgv
      · change centeredBody (g (u 4)) = centeredBody directionW
        calc
          centeredBody (g (u 4)) = centeredBody (rw • g (u 4)) :=
            (centeredBody_smul_sign rw hrw _).symm
          _ = centeredBody (g (rw • u 4)) := congrArg centeredBody (map_smul g rw (u 4)).symm
          _ = centeredBody directionW := congrArg centeredBody hgw
      · change centeredBody (g (u 5)) = centeredBody directionZ
        calc
          centeredBody (g (u 5)) = centeredBody (rz • g (u 5)) :=
            (centeredBody_smul_sign rz hrz _).symm
          _ = centeredBody (g (rz • u 5)) := congrArg centeredBody (map_smul g rz (u 5)).symm
          _ = centeredBody directionZ := congrArg centeredBody hgz
    · rw [hLA]
      exact mapBody_zero_mem _ (hz bodyA)
    · rw [hLB]
      exact mapBody_zero_mem _ (hz bodyB)
    · rw [hLC]
      exact mapBody_zero_mem _ (hz bodyC)
    · rw [hLA]
      exact mapBody_coordinate_zero _ hga' hplaneA
    · rw [hLB]
      exact mapBody_coordinate_zero _ hga' hplaneB
    · rw [hLC]
      exact mapBody_coordinate_zero _ hga' hplaneC

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ShapeNormalization.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Convex/Prod.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Fibers of convex subsets of products

For a convex set `s ⊆ V × W`, each fiber `Prod.mk v ⁻¹' s` is convex, and a convex combination
of two fibers, formed by pointwise Minkowski operations, lies in the fiber over the
corresponding convex combination of base points. The second inclusion is the set-level input
for Brunn's concavity principle, which compares fiber volumes by the Brunn–Minkowski inequality.
-/

public section

open Set
open scoped Pointwise

variable {𝕜 V W : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid V] [Module 𝕜 V] [AddCommMonoid W] [Module 𝕜 W] {s : Set (V × W)}

/-- The fibers of a convex subset of a product are convex. -/
theorem Convex.preimage_prodMk (hs : Convex 𝕜 s) (v : V) : Convex 𝕜 (Prod.mk v ⁻¹' s) := by
  first
  | intro y hy z hz a b ha hb hab
    simpa only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk, Convex.combo_self hab] using
      hs hy hz ha hb hab

/-- A convex combination of two fibers of a convex set lies in the fiber over the convex
combination of the base points. -/
theorem Convex.smul_preimage_prodMk_add_smul_preimage_prodMk_subset (hs : Convex 𝕜 s) (p q : V)
    {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • (Prod.mk p ⁻¹' s) + b • (Prod.mk q ⁻¹' s) ⊆ Prod.mk (a • p + b • q) ⁻¹' s := by
  first
  | rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk] using hs hy hz ha hb hab
end -- closes the original EOF section from source line 19
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Convex/Prod.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/InnerProductSpace/Projection/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/


/-!
# Products and norms of orthogonal projections

For submodules `U` and `V` of an inner product space admitting orthogonal projections `P_U` and
`P_V`, the two products `P_U P_V` and `P_V P_U` have the same operator norm. Since
`P_V P_U = (P_U P_V)†`, this is the identity `‖T‖ = ‖T†‖`, stated here without any completeness
hypothesis on the ambient space, where the adjoint of a bounded operator need not exist.

A map `T P_U` that factors through the projection onto a finite-dimensional `U` has rank at most
`dim U`. For subspaces `U` and `V` of the same finite dimension, `U ⊓ Vᗮ` and `V ⊓ Uᗮ` have the
same dimension. The orthogonal complement of a nonzero vector has codimension one, and fewer than
`dim E` vectors have a common nonzero orthogonal vector, which may be taken of norm one.

For finite-dimensional `U` and `V` with `dim V ≤ dim U`, a lower bound `k ‖u‖² ≤ ‖P_V u‖²` for
`u ∈ U` transfers to the same lower bound `k ‖v‖² ≤ ‖P_U v‖²` for `v ∈ V`.

The projection `P_U v` is the point of `v + Uᗮ` of least norm, and it is the only one: a vector
`w` with `‖w‖ ≤ ‖P_U w‖` equals `P_U w`. Equivalently, `v ∈ U` exactly when adding a vector of
`Uᗮ` never decreases the norm of `v`.

Since the kernel of `P_V` is `Vᗮ`, the projection `P_V` is injective on `U` exactly when no
nonzero vector of `U` is orthogonal to `V`.

Compressing the square of the difference `P_U - P_V` to `U`, from either side, gives
`P_U - P_U P_V P_U`.

A linear map agrees with its composition with the orthogonal projection onto the orthogonal
complement of its kernel whenever the kernel admits an orthogonal projection.

## Provenance

The submodule inclusion-adjoint identity is adapted from
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean` in the
AIQ-Kitware DKPS formalization (Apache-2.0; Jon Crall and GPT-6).

## Main results

* `Submodule.adjoint_subtype`: the adjoint of subspace inclusion is orthogonal projection
  onto that subspace.
* `Submodule.adjoint_orthogonalProjectionOnto_toLinearMap`: the adjoint of restricted
  orthogonal projection is subspace inclusion.
* `Submodule.norm_starProjection_comp_starProjection_comm`: `‖P_U P_V‖ = ‖P_V P_U‖`.
* `Submodule.finrank_range_comp_starProjection_le`: `rank (T P_U) ≤ dim U`.
* `Submodule.finrank_inf_orthogonal_comm`: `dim (U ⊓ Vᗮ) = dim (V ⊓ Uᗮ)` when `dim U = dim V`.
* `Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one`: `dim (𝕜 ∙ v)ᗮ = dim E - 1`
  for a nonzero vector `v`.
* `TauCeti.exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank`,
  `TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank`: fewer than `dim E` vectors
  have a common nonzero, and hence a common unit, orthogonal vector.
* `TauCeti.ne_neg_of_inner_eq_zero`: a vector orthogonal to a nonzero vector `b` is not `-b`.
* `Submodule.mul_norm_sq_le_norm_starProjection_sq_of_finrank_le`: for finite-dimensional
  subspaces with `dim V ≤ dim U`, a lower bound on `‖P_V u‖²` over `U` transfers to the same
  bound on `‖P_U v‖²` over `V`.
* `Submodule.eq_starProjection_of_norm_le`: a vector whose norm is at most that of its projection
  is its projection.
* `Submodule.mem_iff_forall_mem_orthogonal_norm_le_norm_add`: `v ∈ U` if and only if
  `‖v‖ ≤ ‖v + w‖` for every `w ∈ Uᗮ`.
* `Submodule.injOn_starProjection_iff_disjoint`: `P_V` is injective on `U` if and only if
  `U ⊓ Vᗮ = ⊥`.
* `Submodule.starProjection_sub_starProjection_sq_mul_starProjection`,
  `Submodule.starProjection_mul_starProjection_sub_starProjection_sq`:
  `(P_U - P_V)² P_U = P_U (P_U - P_V)² = P_U - P_U P_V P_U`.
* `LinearMap.apply_sub_starProjection_ker`,
  `ContinuousLinearMap.comp_starProjection_orthogonal_ker`: maps ignore their kernel component.
-/

public section

noncomputable section

namespace Submodule

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- One half of `norm_starProjection_comp_starProjection_comm`. -/
private theorem norm_starProjection_comp_starProjection_le :
    ‖U.starProjection ∘L V.starProjection‖ ≤ ‖V.starProjection ∘L U.starProjection‖ := by
  first
    -- For `y = P_U P_V x`, `‖y‖² = Re ⟪x, P_V P_U y⟫` because both projections are symmetric and
    -- `P_U y = y`.
  | refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set y := U.starProjection (V.starProjection x)
    have hy : U.starProjection y = y := starProjection_eq_self_iff.mpr (U.starProjection_apply_mem _)
    have hinner : ⟪y, y⟫_𝕜 = ⟪x, V.starProjection y⟫_𝕜 :=
      calc ⟪y, y⟫_𝕜 = ⟪V.starProjection x, U.starProjection y⟫_𝕜 :=
            inner_starProjection_left_eq_right U _ _
        _ = ⟪x, V.starProjection y⟫_𝕜 := by rw [hy, inner_starProjection_left_eq_right]
    have key : ‖y‖ * ‖y‖ ≤ ‖V.starProjection ∘L U.starProjection‖ * ‖x‖ * ‖y‖ := by
      calc ‖y‖ * ‖y‖ = RCLike.re ⟪x, V.starProjection y⟫_𝕜 := by
            rw [← inner_self_eq_norm_mul_norm (𝕜 := 𝕜), hinner]
        _ ≤ ‖x‖ * ‖(V.starProjection ∘L U.starProjection) y‖ := by
            rw [comp_apply, hy]
            exact re_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖V.starProjection ∘L U.starProjection‖ * ‖y‖) := by
            gcongr
            exact le_opNorm _ _
        _ = ‖V.starProjection ∘L U.starProjection‖ * ‖x‖ * ‖y‖ := by ring
    rcases (norm_nonneg y).eq_or_lt with h | h
    · rw [comp_apply, ← h]
      positivity
    · exact le_of_mul_le_mul_right key h

/-- The two products of a pair of orthogonal projections have the same operator norm, that is,
`‖T‖ = ‖T†‖` for `T = P_U P_V`. No completeness of `E` is assumed. -/
theorem norm_starProjection_comp_starProjection_comm :
    ‖U.starProjection ∘L V.starProjection‖ = ‖V.starProjection ∘L U.starProjection‖ :=
  (norm_starProjection_comp_starProjection_le U V).antisymm
    (norm_starProjection_comp_starProjection_le V U)

/-- A map `T P_U` that factors through the projection onto `U` has rank at most `dim U`. -/
theorem finrank_range_comp_starProjection_le {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [FiniteDimensional 𝕜 U] (T : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearMap.range (T ∘ₗ (U.starProjection : E →ₗ[𝕜] E))) ≤
      Module.finrank 𝕜 U := by
  first
  | rw [LinearMap.range_comp, range_starProjection]
    exact finrank_map_le _ _

omit [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- For finite-dimensional subspaces of the same dimension, `U ⊓ Vᗮ` and `V ⊓ Uᗮ` have the same
dimension. -/
theorem finrank_inf_orthogonal_comm [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]
    (h : Module.finrank 𝕜 U = Module.finrank 𝕜 V) :
    Module.finrank 𝕜 ↥(U ⊓ Vᗮ) = Module.finrank 𝕜 ↥(V ⊓ Uᗮ) := by
  first
    -- `U ⊓ Vᗮ` and `V ⊓ Uᗮ` are the kernels of `P_V|_U : U → V` and of its adjoint `P_U|_V`, and a
    -- map and its adjoint have the same rank.
  | have hker (U V : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V] :
        Module.finrank 𝕜 ↥(U ⊓ Vᗮ) = Module.finrank 𝕜
          (LinearMap.ker (V.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype)) := by
      rw [LinearMap.ker_comp, ← map_comap_subtype, finrank_map_subtype_eq]
      exact congrArg (fun W : Submodule 𝕜 E ↦ Module.finrank 𝕜 (W.comap U.subtype))
        ker_orthogonalProjectionOnto.symm
    let T : U →ₗ[𝕜] V := V.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
    have hT : T.adjoint = U.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype :=
      ((LinearMap.eq_adjoint_iff _ _).2 fun v u ↦ by simp [T]).symm
    have h₁ := T.finrank_range_add_finrank_ker
    have h₂ := T.adjoint.finrank_range_add_finrank_ker
    rw [T.finrank_range_adjoint, hT, ← hker] at h₂
    rw [← hker] at h₁
    omega

/-- In a finite-dimensional inner product space, the orthogonal complement of the span of a
nonzero vector has codimension one. Unlike `Submodule.finrank_orthogonal_span_singleton`, the
dimension of the ambient space is not fixed in advance. -/
theorem finrank_orthogonal_span_singleton_eq_finrank_sub_one [FiniteDimensional 𝕜 E] {v : E}
    (hv : v ≠ 0) : Module.finrank 𝕜 (𝕜 ∙ v)ᗮ = Module.finrank 𝕜 E - 1 := by
  first
  | have := Module.finrank_pos_iff_exists_ne_zero (R := 𝕜).2 ⟨v, hv⟩
    exact finrank_add_finrank_orthogonal' <| by rw [finrank_span_singleton hv]; omega

/-- For finite-dimensional subspaces with `dim V ≤ dim U`, a lower bound `k ‖u‖² ≤ ‖P_V u‖²` on
the cosines of `U` towards `V` transfers to the same lower bound for `V` towards `U`. -/
theorem mul_norm_sq_le_norm_starProjection_sq_of_finrank_le [FiniteDimensional 𝕜 U]
    [FiniteDimensional 𝕜 V] (h : Module.finrank 𝕜 V ≤ Module.finrank 𝕜 U) {k : ℝ}
    (hU : ∀ u ∈ U, k * ‖u‖ ^ 2 ≤ ‖V.starProjection u‖ ^ 2) {v : E} (hv : v ∈ V) :
    k * ‖v‖ ^ 2 ≤ ‖U.starProjection v‖ ^ 2 := by
  first
  | rcases le_or_gt k 0 with hk | hk
    · exact (mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg _)).trans (sq_nonneg _)
    -- For `k > 0`, `P_V` maps `U` injectively, so `dim U ≤ dim V`; by the dimension hypothesis the
    -- dimensions agree and `P_V` maps `U` onto `V`.
    let T : U →ₗ[𝕜] V := V.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
    have hT : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).mpr fun u hu => ?_
      have h0 : V.starProjection u = 0 := by
        simpa [T] using congrArg (Subtype.val : V → E) hu
      have := hU u u.2
      rw [h0, norm_zero, zero_pow two_ne_zero] at this
      have : ‖(u : E)‖ ^ 2 = 0 :=
        le_antisymm (nonpos_of_mul_nonpos_right this hk) (sq_nonneg _)
      simpa using this
    obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (le_antisymm (LinearMap.finrank_le_finrank_of_injective hT) h)).mp hT ⟨v, hv⟩
    have hPw : V.starProjection w = v := by
      simpa [T] using congrArg (Subtype.val : V → E) hw
    -- The preimage `w ∈ U` of `v` gives `‖v‖² = ⟪P_U v, w⟫ ≤ ‖P_U v‖ ‖w‖`.
    have hinner : ‖v‖ ^ 2 ≤ ‖U.starProjection v‖ * ‖(w : E)‖ := by
      have : ⟪U.starProjection v, (w : E)⟫_𝕜 = ⟪v, v⟫_𝕜 := calc
        _ = ⟪v, U.starProjection w⟫_𝕜 := inner_starProjection_left_eq_right U v w
        _ = ⟪V.starProjection v, (w : E)⟫_𝕜 := by
          rw [starProjection_eq_self_iff.mpr w.2, starProjection_eq_self_iff.mpr hv]
        _ = ⟪v, v⟫_𝕜 := by rw [inner_starProjection_left_eq_right, hPw]
      have h := norm_inner_le_norm (𝕜 := 𝕜) (U.starProjection v) (w : E)
      rwa [this, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h
    -- Combined with `k ‖w‖² ≤ ‖P_V w‖² = ‖v‖²`, this gives `k ‖v‖⁴ ≤ ‖P_U v‖² ‖v‖²`.
    have hw' := hU w w.2
    rw [hPw] at hw'
    rcases (norm_nonneg v).eq_or_lt with hv0 | hv0
    · rw [← hv0, zero_pow two_ne_zero, mul_zero]
      positivity
    have hv2 : 0 < ‖v‖ ^ 2 := by positivity
    nlinarith [norm_nonneg (U.starProjection v), norm_nonneg (w : E),
      mul_le_mul_of_nonneg_left hw' (sq_nonneg ‖U.starProjection v‖),
      pow_le_pow_left₀ (by positivity) hinner 2]

/-- A vector whose norm is at most that of its orthogonal projection onto `U` is that projection,
since the projection never increases the norm and only fixes the norm of vectors of `U`. -/
theorem eq_starProjection_of_norm_le {w : E} (hw : ‖w‖ ≤ ‖U.starProjection w‖) :
    w = U.starProjection w :=
  (starProjection_eq_self_iff.2 ((U.mem_iff_norm_starProjection w).2
    ((U.norm_starProjection_apply_le w).antisymm hw))).symm

/-- A vector lies in `U` if and only if adding a vector of `Uᗮ` never decreases its norm. -/
theorem mem_iff_forall_mem_orthogonal_norm_le_norm_add {v : E} :
    v ∈ U ↔ ∀ w ∈ Uᗮ, ‖v‖ ≤ ‖v + w‖ := by
  first
  | refine ⟨fun hv w hw ↦ ?_, fun h ↦ ?_⟩
    · -- Pythagoras: `‖v + w‖² = ‖v‖² + ‖w‖²`.
      refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v w
        (inner_right_of_mem_orthogonal hv hw)]
      exact le_add_of_nonneg_right (mul_self_nonneg _)
    · have hle := h _ (sub_mem_comm_iff.1 (U.sub_starProjection_mem_orthogonal v))
      rw [add_sub_cancel] at hle
      rw [U.eq_starProjection_of_norm_le hle]
      exact U.starProjection_apply_mem v

omit [U.HasOrthogonalProjection] in
/-- The orthogonal projection onto `V` is injective on `U` exactly when `U ⊓ Vᗮ = ⊥`, since its
kernel is `Vᗮ`. -/
theorem injOn_starProjection_iff_disjoint :
    Set.InjOn V.starProjection U ↔ Disjoint U Vᗮ := by
  first
  | simpa using (LinearMap.disjoint_ker_iff_injOn (f := (V.starProjection : E →ₗ[𝕜] E))
      (p := U)).symm

/-- Compressing `(P_U - P_V)²` to `U` on the right gives `P_U - P_U P_V P_U`. -/
theorem starProjection_sub_starProjection_sq_mul_starProjection :
    (U.starProjection - V.starProjection) ^ 2 * U.starProjection =
      U.starProjection - U.starProjection * V.starProjection * U.starProjection := by
  first
  | have hP := U.isIdempotentElem_starProjection
    have hQ := V.isIdempotentElem_starProjection
    simp only [sq, sub_mul, mul_sub, mul_assoc, hP.eq, hQ.mul_self_mul]
    abel

/-- Compressing `(P_U - P_V)²` to `U` on the left gives `P_U - P_U P_V P_U`. -/
theorem starProjection_mul_starProjection_sub_starProjection_sq :
    U.starProjection * (U.starProjection - V.starProjection) ^ 2 =
      U.starProjection - U.starProjection * V.starProjection * U.starProjection := by
  first
  | have hP := U.isIdempotentElem_starProjection
    have hQ := V.isIdempotentElem_starProjection
    simp only [sq, sub_mul, mul_sub, mul_assoc, hP.eq, hQ.eq, hP.mul_self_mul]
    abel

/-- The adjoint of the inclusion `U → E` is the orthogonal projection `E → U`.
Both maps are regarded as finite-dimensional algebraic linear maps. -/
@[simp]
theorem adjoint_subtype [FiniteDimensional 𝕜 E] :
    LinearMap.adjoint U.subtype = U.orthogonalProjectionOnto.toLinearMap := by
  first
  | rw [eq_comm]
    apply (LinearMap.eq_adjoint_iff
      U.orthogonalProjectionOnto.toLinearMap U.subtype).2
    intro x y
    -- Identify the ambient action of the restricted orthogonal projection with
    -- `starProjection`; the inner-product identity is then a projection property.
    change ⟪U.starProjection x, (y : E)⟫_𝕜 = ⟪x, (y : E)⟫_𝕜
    rw [U.inner_starProjection_left_eq_right,
      U.starProjection_eq_self_iff.mpr y.2]

/-- The algebraic adjoint of the orthogonal projection `E → U` is the inclusion `U → E`.
This is the elementary simplification rule for the adjoints of cross-projections and
self-adjoint compressions, together with `LinearMap.adjoint_comp`. -/
@[simp]
theorem adjoint_orthogonalProjectionOnto_toLinearMap [FiniteDimensional 𝕜 E] :
    LinearMap.adjoint U.orthogonalProjectionOnto.toLinearMap = U.subtype := by
  first
  | rw [← U.adjoint_subtype, LinearMap.adjoint_adjoint]

end Submodule

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Fewer than `dim E` vectors have a common nonzero orthogonal vector: the orthogonal complement
of their span is nontrivial. -/
theorem exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank (s : Finset E)
    (hs : s.card < Module.finrank 𝕜 E) : ∃ e : E, e ≠ 0 ∧ ∀ u ∈ s, ⟪u, e⟫_𝕜 = 0 := by
  first
  | have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_pos (by omega)
    set K := Submodule.span 𝕜 (s : Set E)
    have hK : Module.finrank 𝕜 K < Module.finrank 𝕜 E := (finrank_span_finset_le_card s).trans_lt hs
    obtain ⟨e, he, he₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Kᗮ) fun h ↦ by
      have := K.finrank_add_finrank_orthogonal
      rw [h, finrank_bot] at this
      omega
    exact ⟨e, he₀, fun u hu ↦ Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hu) he⟩

/-- Fewer than `dim E` vectors have a common orthogonal unit vector. -/
theorem exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (s : Finset E)
    (hs : s.card < Module.finrank 𝕜 E) : ∃ e : E, ‖e‖ = 1 ∧ ∀ u ∈ s, ⟪u, e⟫_𝕜 = 0 := by
  first
  | obtain ⟨e, he₀, he⟩ := exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank s hs
    exact ⟨(‖e‖⁻¹ : 𝕜) • e, norm_smul_inv_norm he₀, fun u hu ↦ by
      rw [inner_smul_right, he u hu, mul_zero]⟩

/-- A vector orthogonal to a nonzero vector `b` is not `-b`. -/
theorem ne_neg_of_inner_eq_zero {a b : E} (hb : b ≠ 0) (hab : ⟪a, b⟫_𝕜 = 0) : a ≠ -b := by
  first
  | rintro rfl
    rw [inner_neg_left, neg_eq_zero, inner_self_eq_zero] at hab
    exact hb hab

end TauCeti

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- A linear map does not see the component of a vector in its kernel. -/
@[simp]
theorem apply_sub_starProjection_ker (u : E →ₗ[𝕜] F) [u.ker.HasOrthogonalProjection]
    (x : E) : u (x - u.ker.starProjection x) = u x := by
  first
  | have hx := Submodule.starProjection_apply_mem u.ker x
    rw [mem_ker] at hx
    simpa only [map_add, hx, add_zero] using
      congrArg u (sub_add_cancel x (u.ker.starProjection x))

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- Composing a continuous linear map with the orthogonal projection onto the orthogonal
complement of its kernel does not change it. -/
@[simp]
theorem comp_starProjection_orthogonal_ker (u : E →L[𝕜] F) [u.ker.HasOrthogonalProjection] :
    u ∘L u.kerᗮ.starProjection = u := by
  first
  | ext x
    simpa only [comp_apply, Submodule.starProjection_orthogonal_val, coe_coe] using
      u.toLinearMap.apply_sub_starProjection_ker x

end ContinuousLinearMap
end -- closes the original EOF section from source line 80
end -- closes the original EOF section from source line 78
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/InnerProductSpace/Projection/Basic.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/InnerProductSpace/LinearIsometry.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Linear isometries, orthogonal complements, and product decompositions

A linear isometry `f : E →ₗᵢ[ℝ] F` into a finite-dimensional inner product space identifies `F`
with the product of `E` and the orthogonal complement of the range of `f`, by
`(u, w) ↦ f u + w`. Read through this identification, `f` itself is the inclusion `u ↦ (u, 0)` of
the first factor. This is the normal form in which Mathlib's `Manifold.IsImmersionAt` asks for a
map to be written in charts, so this decomposition is what exhibits a linear isometry, and the maps
of spheres and balls it induces, as immersions.

A linear isometry also carries the orthogonal complement of a vector into the orthogonal
complement of its image; this is how it transports the stereographic charts of unit spheres. For
Euclidean spaces, a linear isometry matching a pair of standard basis vectors matches the
corresponding coordinates; this is how it transports the half-space charts of closed balls.

An isometry between the orthogonal complements of two unit vectors extends uniquely to
an ambient isometry sending one vector to the other. This extension works over both real
and complex inner product spaces, without completeness or dimension assumptions.

Orthogonal line coordinates associated with a unit vector identify the ambient space with
the product of its orthogonal hyperplane and the scalar line. The `L²` product version is
isometric; the ordinary product version is a continuous linear equivalence used for line
sections and product integration.

Along a smooth family of linear isometries of a finite-dimensional real inner product space, the
inverses again depend smoothly on the parameter: expanding in an orthonormal basis `bᵢ`,
`(R p)⁻¹ x = ∑ i, ⟪R p bᵢ, x⟫ bᵢ`. So a smooth path of linear isometries moves the unit sphere by
diffeomorphisms.

## Main definitions

* `TauCeti.orthogonalLineIsometry` and `TauCeti.orthogonalLineEquiv`: orthogonal line coordinates.
* `LinearIsometry.prodOrthogonalRangeEquiv`: the continuous linear equivalence
  `E × (range f)ᗮ ≃L[ℝ] F` given by `(u, w) ↦ f u + w`.
* `LinearIsometry.orthogonalComplementSingletonMap`: the restriction of a linear isometry to a map
  `(ℝ ∙ v)ᗮ →ₗᵢ[ℝ] (ℝ ∙ w)ᗮ`, where `w` is the image of `v`.

* `LinearIsometryEquiv.extendOrthogonalComplement`: extend an isometry of orthogonal
  complements by its prescribed action on the radial line.

## Main results

* `LinearIsometry.apply_eq_of_map_single`: a linear isometry of Euclidean spaces sending the `i`-th
  standard basis vector to the `j`-th one reads the `i`-th coordinate off as the `j`-th coordinate
  of the image.
* `LinearMap.eq_of_apply_eq_of_eqOn_orthogonal`: linear maps agreeing on a vector and
  its orthogonal complement are equal, without a unit-norm assumption.
* `LinearIsometryEquiv.eq_extendOrthogonalComplement`: a linear isometry equals the
  extension if it agrees on the unit vector and its orthogonal complement.
* `LinearIsometryEquiv.eq_refl_or_eq_neg`: the only real linear isometry equivalences of `ℝ`
  are the identity and negation.
* `ContDiff.linearIsometryEquiv_symm_apply`: the inverses along a smooth family of linear
  isometries of a finite-dimensional space form a smooth family.
-/

public section

noncomputable section

namespace LinearIsometry

open Module

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- A linear isometry `f` maps the orthogonal complement of `v` into the orthogonal complement of
`f v`. -/
theorem map_mem_orthogonal_singleton (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w) {y : E}
    (hy : y ∈ (ℝ ∙ v)ᗮ) : f y ∈ (ℝ ∙ w)ᗮ := by
  first
  | subst hw
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy ⊢
    rwa [f.inner_map_map]

/-- The restriction of a linear isometry `f` to a linear isometry from the orthogonal complement
of `v` to the orthogonal complement of its image `w`. -/
def orthogonalComplementSingletonMap (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w) :
    (ℝ ∙ v)ᗮ →ₗᵢ[ℝ] (ℝ ∙ w)ᗮ where
  toLinearMap := (f.toLinearMap.domRestrict (ℝ ∙ v)ᗮ).codRestrict (ℝ ∙ w)ᗮ fun y ↦
    f.map_mem_orthogonal_singleton hw y.2
  norm_map' y := f.norm_map y

@[simp]
theorem coe_orthogonalComplementSingletonMap_apply (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w)
    (y : (ℝ ∙ v)ᗮ) : (f.orthogonalComplementSingletonMap hw y : F) = f y :=
  (rfl)

variable [FiniteDimensional ℝ F]

/-- A linear isometry `f : E →ₗᵢ[ℝ] F` into a finite-dimensional space identifies the product of
`E` with the orthogonal complement of the range of `f` with `F`, by `(u, w) ↦ f u + w`. -/
def prodOrthogonalRangeEquiv (f : E →ₗᵢ[ℝ] F) :
    (E × (LinearMap.range f.toLinearMap)ᗮ) ≃L[ℝ] F :=
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_injective f.toLinearMap f.injective
  ((f.equivRange.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ _)).trans
    (Submodule.prodEquivOfIsCompl _ _
      (Submodule.isCompl_orthogonal _))).toContinuousLinearEquiv

@[simp]
theorem prodOrthogonalRangeEquiv_apply (f : E →ₗᵢ[ℝ] F) (u : E)
    (w : (LinearMap.range f.toLinearMap)ᗮ) : f.prodOrthogonalRangeEquiv (u, w) = f u + w := by
  first
  | rfl

/-- Through `LinearIsometry.prodOrthogonalRangeEquiv`, the linear isometry `f` is the inclusion of
the first factor. -/
theorem prodOrthogonalRangeEquiv_apply_zero (f : E →ₗᵢ[ℝ] F) (u : E) :
    f.prodOrthogonalRangeEquiv (u, 0) = f u := by
  first
  | simp

section EuclideanSpace

variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A linear isometry of Euclidean spaces sending the `i`-th standard basis vector to the `j`-th
one reads the `i`-th coordinate of its argument off as the `j`-th coordinate of the image. -/
theorem apply_eq_of_map_single {L : EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] EuclideanSpace 𝕜 κ} {i : ι} {j : κ}
    (hL : L (EuclideanSpace.single i 1) = EuclideanSpace.single j 1) (u : EuclideanSpace 𝕜 ι) :
    L u j = u i := by
  first
  | have h := L.inner_map_map (EuclideanSpace.single i 1) u
    rw [hL] at h
    simpa [EuclideanSpace.inner_single_left] using h

end EuclideanSpace

end LinearIsometry

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] {x : E}

/-- Linear maps are determined by their value on a vector and their restriction to its
orthogonal complement. The vector need not be a unit vector or even nonzero. -/
theorem eq_of_apply_eq_of_eqOn_orthogonal {f g : E →ₗ[𝕜] F} (hx : f x = g x)
    (h : ∀ v : (𝕜 ∙ x)ᗮ, f v = g v) : f = g := by
  first
  | apply ext_on_codisjoint (𝕜 ∙ x).isCompl_orthogonal.codisjoint
    · exact eqOn_span' (by simpa only [Set.eqOn_singleton] using hx)
    · intro v hv
      exact h ⟨v, hv⟩

end LinearMap

namespace LinearIsometryEquiv

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {x : E} {y : F}

/-- Extend an isometry between the orthogonal complements of two unit vectors by sending
one unit vector to the other. The extension uses Mathlib's
`Submodule.orthogonalDecomposition` and `LinearIsometryEquiv.toSpanUnitSingleton`. -/
noncomputable def extendOrthogonalComplement
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    E ≃ₗᵢ[𝕜] F :=
  (𝕜 ∙ x).orthogonalDecomposition.trans
    (((toSpanUnitSingleton x hx).symm.trans (toSpanUnitSingleton y hy)).withLpProdCongr 2 e |>.trans
      (𝕜 ∙ y).orthogonalDecomposition.symm)

/-- On the orthogonal direct sum, the extension acts on the radial and transverse
components separately. -/
@[simp]
theorem extendOrthogonalComplement_apply_smul_add
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (r : 𝕜) (v : (𝕜 ∙ x)ᗮ) :
    e.extendOrthogonalComplement hx hy (r • x + v) = r • y + e v := by
  first
  | have h := (𝕜 ∙ x).orthogonalDecomposition.apply_symm_apply
      (WithLp.toLp 2 (toSpanUnitSingleton x hx r, v))
    conv_lhs at h =>
      simp only [Submodule.orthogonalDecomposition_symm_apply, WithLp.toLp_fst,
        WithLp.toLp_snd, toSpanUnitSingleton_apply]
    simp only [extendOrthogonalComplement, trans_apply, h, withLpProdCongr_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, symm_apply_apply]
    simp only [Submodule.orthogonalDecomposition_symm_apply, WithLp.toLp_fst,
      WithLp.toLp_snd, toSpanUnitSingleton_apply]

/-- The extension sends the distinguished unit vector to the distinguished target vector. -/
@[simp]
theorem extendOrthogonalComplement_apply_self
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    e.extendOrthogonalComplement hx hy x = y := by
  first
  | simpa using e.extendOrthogonalComplement_apply_smul_add hx hy 1 0

/-- The extension agrees with the original isometry on the orthogonal complement. -/
@[simp]
theorem extendOrthogonalComplement_apply_coe
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (v : (𝕜 ∙ x)ᗮ) : e.extendOrthogonalComplement hx hy v = e v := by
  first
  | simpa using e.extendOrthogonalComplement_apply_smul_add hx hy 0 v

/-- An ambient linear isometry is uniquely determined by its value on a unit vector and
its restriction to the orthogonal complement. -/
theorem eq_extendOrthogonalComplement
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (f : E →ₗᵢ[𝕜] F) (hfx : f x = y)
    (hf : ∀ v : (𝕜 ∙ x)ᗮ, f v = e v) :
    f = (e.extendOrthogonalComplement hx hy).toLinearIsometry := by
  first
  | apply LinearIsometry.toLinearMap_injective
    apply LinearMap.eq_of_apply_eq_of_eqOn_orthogonal (x := x)
    · simpa only [LinearIsometry.coe_toLinearMap, coe_toLinearIsometry,
        extendOrthogonalComplement_apply_self] using hfx
    · intro v
      simpa only [LinearIsometry.coe_toLinearMap, coe_toLinearIsometry,
        extendOrthogonalComplement_apply_coe] using hf v

/-- The only real linear isometry equivalences of the real line are the identity and negation. -/
theorem eq_refl_or_eq_neg (A : ℝ ≃ₗᵢ[ℝ] ℝ) : A = .refl ℝ ℝ ∨ A = .neg ℝ := by
  first
  | have hsq : (A 1) ^ 2 = 1 := by
      simpa only [RCLike.inner_apply, conj_trivial, mul_one, one_mul, pow_two]
        using A.inner_map_map (1 : ℝ) 1
    -- By linearity, `A` is multiplication by `A 1`.
    have hA (x : ℝ) : A x = x * A 1 := by simpa using _root_.map_smul A x (1 : ℝ)
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact .inl (ext fun x ↦ by simp [hA x, h])
    · exact .inr (ext fun x ↦ by simp [hA x, h])

end LinearIsometryEquiv

namespace TauCeti

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The isometric form of orthogonal line coordinates, using the `L²` norm on the product.
Constructed from Mathlib's `Submodule.orthogonalDecomposition` and
`LinearIsometryEquiv.toSpanUnitSingleton`. -/
def orthogonalLineIsometry (e : E) (he : ‖e‖ = 1) :
    WithLp 2 ((ℝ ∙ e)ᗮ × ℝ) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2 (.refl ℝ _) (.toSpanUnitSingleton e he)).trans
    ((LinearIsometryEquiv.withLpProdComm 2 ℝ _ _).trans
      (ℝ ∙ e).orthogonalDecomposition.symm)

@[simp]
theorem orthogonalLineIsometry_apply (e : E) (he : ‖e‖ = 1)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    orthogonalLineIsometry e he (WithLp.toLp 2 (y, t)) = (y : E) + t • e := by
  first
  | simp [orthogonalLineIsometry, add_comm]

/-- Orthogonal line coordinates: the transverse coordinate lies in `eᗮ` and the longitudinal
coordinate is real. This version uses the ordinary product norm;
`orthogonalLineIsometry` supplies the isometric version on the `L²` product. -/
def orthogonalLineEquiv (e : E) (he : ‖e‖ = 1) : ((ℝ ∙ e)ᗮ × ℝ) ≃L[ℝ] E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ ∙ e)ᗮ ℝ).symm.trans
    (orthogonalLineIsometry e he).toContinuousLinearEquiv

/-- The ordinary product coordinates are the isometric coordinates after changing the
product norm to the `L²` norm. -/
theorem orthogonalLineEquiv_def (e : E) (he : ‖e‖ = 1) :
    orthogonalLineEquiv e he =
      (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ ∙ e)ᗮ ℝ).symm.trans
        (orthogonalLineIsometry e he).toContinuousLinearEquiv := (rfl)

@[simp]
theorem orthogonalLineEquiv_apply (e : E) (he : ‖e‖ = 1)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    orthogonalLineEquiv e he (y, t) = (y : E) + t • e :=
  orthogonalLineIsometry_apply e he y t

/-- The longitudinal inverse coordinate is the inner product with the unit direction. -/
@[simp]
theorem orthogonalLineEquiv_symm_snd (e : E) (he : ‖e‖ = 1) (x : E) :
    ((orthogonalLineEquiv e he).symm x).2 = ⟪e, x⟫ := by
  first
  | obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
    have hy : ⟪e, (y : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
    rw [ContinuousLinearEquiv.symm_apply_apply, orthogonalLineEquiv_apply]
    simp [inner_add_right, inner_smul_right, hy, inner_self_eq_norm_sq_to_K, he]

/-- The transverse inverse coordinate is obtained by subtracting the longitudinal component. -/
@[simp]
theorem orthogonalLineEquiv_symm_fst (e : E) (he : ‖e‖ = 1) (x : E) :
    (((orthogonalLineEquiv e he).symm x).1 : E) = x - ⟪e, x⟫ • e := by
  first
  | have h := (orthogonalLineEquiv e he).apply_symm_apply x
    rw [← Prod.eta (p := (orthogonalLineEquiv e he).symm x),
      orthogonalLineEquiv_apply, orthogonalLineEquiv_symm_snd] at h
    exact eq_sub_iff_add_eq.mpr h

/-- Pythagoras in orthogonal line coordinates. -/
theorem norm_add_smul_sq (e : E) (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    ‖(y : E) + t • e‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  first
  | rw [← orthogonalLineIsometry_apply e he y t,
      (orthogonalLineIsometry e he).norm_map, WithLp.prod_norm_sq_eq_of_L2]
    simp

/-- A point `y + t • e` in orthogonal line coordinates lies at height `t` along `e`. -/
theorem inner_add_smul (e : E) (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    ⟪e, (y : E) + t • e⟫ = t := by
  first
  | rw [← orthogonalLineEquiv_apply e he, ← orthogonalLineEquiv_symm_snd e he,
      ContinuousLinearEquiv.symm_apply_apply]

end TauCeti

/-! ### Smooth paths of linear isometries -/

open scoped InnerProductSpace in
/-- Along a smooth family of linear isometries of a finite-dimensional real inner product space,
the inverses also depend smoothly on the parameter: expanding in an orthonormal basis `bᵢ`,
`(R p)⁻¹ x = ∑ i, ⟪R p bᵢ, x⟫ bᵢ`. -/
theorem ContDiff.linearIsometryEquiv_symm_apply {F G : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : WithTop ℕ∞} {R : G → F ≃ₗᵢ[ℝ] F} (hR : ContDiff ℝ m fun p : G × F => R p.1 p.2) :
    ContDiff ℝ m fun p : G × F => (R p.1).symm p.2 := by
  first
  | let b := stdOrthonormalBasis ℝ F
    have hexp : (fun p : G × F => (R p.1).symm p.2) =
        fun p => ∑ i, ⟪R p.1 (b i), p.2⟫_ℝ • b i := by
      funext p
      conv_lhs => rw [← b.sum_repr' ((R p.1).symm p.2)]
      simp only [LinearIsometryEquiv.inner_map_eq_flip]
    rw [hexp]
    exact ContDiff.sum fun i _ =>
      ((hR.comp (contDiff_fst.prodMk contDiff_const)).inner ℝ contDiff_snd).smul contDiff_const
end -- closes the original EOF section from source line 73
end -- closes the original EOF section from source line 71
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/InnerProductSpace/LinearIsometry.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Integral/Lebesgue/Subsequence.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Almost everywhere convergence along a subsequence

If the Lebesgue integrals of nonnegative functions `F n : α → ℝ≥0∞` tend to `0`, then along a
subsequence the functions themselves tend to `0` almost everywhere. Choose the subsequence with
integrals below `2⁻ʲ`: the sum `∑ⱼ F (φ j)` then has finite integral, so it is finite almost
everywhere, and its terms tend to `0` there.

## Main statements

* `TauCeti.exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral`: a subsequence of functions
  whose integrals tend to `0` tends to `0` almost everywhere.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **A subsequence converging almost everywhere.** If `F n : α → ℝ≥0∞` are almost everywhere
measurable and `∫⁻ F n ∂μ → 0`, then along a subsequence `F (φ j) a → 0` for almost every `a`. -/
theorem exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral {F : ℕ → α → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ) (h : Tendsto (fun n ↦ ∫⁻ a, F n a ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ a ∂μ, Tendsto (fun j ↦ F (φ j) a) atTop (𝓝 0) := by
  first
    -- Along a subsequence with `∫⁻ F (φ j) < 2⁻ʲ`, the sum `∑ⱼ F (φ j) a` has finite integral.
  | obtain ⟨φ, hφ, hlt⟩ := extraction_forall_of_eventually fun j ↦
      h.eventually (gt_mem_nhds (ENNReal.pow_pos (a := 2⁻¹) (by simp) j))
    refine ⟨φ, hφ, ?_⟩
    have hsum : ∫⁻ a, ∑' j, F (φ j) a ∂μ ≠ ∞ := by
      rw [lintegral_tsum fun j ↦ hF (φ j)]
      exact ((ENNReal.tsum_le_tsum fun j ↦ (hlt j).le).trans_lt (by simp)).ne
    -- So the sum is finite almost everywhere, and its terms tend to `0` there.
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun j ↦ hF (φ j)) hsum] with a ha
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne

end TauCeti
end -- closes the original EOF section from source line 27
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Integral/Lebesgue/Subsequence.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/OrthogonalSlices.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Orthogonal line coordinates and Lebesgue sections

For a unit vector `e` in a finite-dimensional real inner product space, the coordinates
`(y, t) ↦ y + t • e`, with `y ∈ (ℝ ∙ e)ᗮ`, preserve product volume. Consequently the volume
of a Lebesgue-measurable set is the integral of the lengths of its parallel line sections.
Replacing a set by a volume-a.e. equal representative changes almost every section only
on a one-dimensional null set. This permits line-section arguments for measurable sets
without choosing a Borel representative permanently.
The length of a line section is independent of its base point along the line, in any real module.

Dually, the volume is the integral over heights `t` of the volumes of the hyperplane sections
`{y ∈ (ℝ ∙ e)ᗮ | y + t • e ∈ s}`, and restricting the heights to a Borel set gives the volume
of the corresponding part of the set. Hyperplane sections of bounded sets have finite volume,
and hyperplane sections through interior points have positive volume. The heights of interior
points form an open set, and a set has positive volume at any open set of heights containing the
height of an interior point.

More generally, for any subspace `K`, Tonelli's theorem splits Lebesgue integrals over `E` along
the orthogonal decomposition `E = Kᗮ ⊕ K` (`Submodule.lintegral_eq_lintegral_lintegral_add`),
via Mathlib's `Submodule.measurePreserving_measurableEquivProd`. In these coordinates based at a
point `p`, a product of sets has the product volume, every point `x` is recovered as the sum of
its two coordinates and `p`, and each coordinate moves no farther than `x` does.

The coordinate construction uses Mathlib's `Submodule.orthogonalDecomposition` and
`LinearIsometryEquiv.toSpanUnitSingleton`; its normalization follows Mathlib's volume
preservation for linear isometries and for the `L²` product.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

/-- Moving the base point along the direction does not change the length of a line section. -/
theorem volume_lineSection_add_smul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (e : E) (s : Set E) (x : E) (c : ℝ) :
    volume {t : ℝ | x + c • e + t • e ∈ s} = volume {t : ℝ | x + t • e ∈ s} := by
  first
  | have h : {t : ℝ | x + c • e + t • e ∈ s} = (fun t ↦ t + c) ⁻¹' {t : ℝ | x + t • e ∈ s} := by
      ext t
      simp [add_smul, add_assoc, add_comm (t • e)]
    rw [h, measure_preimage_add_right]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal line coordinates preserve the product of transverse and longitudinal volumes. -/
theorem measurePreserving_orthogonalLineEquiv (e : E) (he : ‖e‖ = 1) :
    MeasurePreserving (orthogonalLineEquiv e he) (volume.prod volume) volume := by
  first
  | rw [orthogonalLineEquiv_def]
    exact (orthogonalLineIsometry e he).measurePreserving.comp
      (WithLp.volume_preserving_toLp (ℝ ∙ e)ᗮ ℝ)

private theorem aemeasurable_comp_orthogonalLineEquiv (e : E) (he : ‖e‖ = 1)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g volume) :
    AEMeasurable (g ∘ orthogonalLineEquiv e he) (volume.prod volume) := by
  first
  | exact hg.comp_quasiMeasurePreserving
      (measurePreserving_orthogonalLineEquiv e he).quasiMeasurePreserving

/-- Integrating an a.e. measurable nonnegative function along parallel lines gives an
a.e. measurable function of the transverse coordinate. -/
theorem aemeasurable_lintegral_line (e : E) (he : ‖e‖ = 1)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g volume) :
    AEMeasurable (fun y : (ℝ ∙ e)ᗮ ↦ ∫⁻ t : ℝ, g ((y : E) + t • e)) volume := by
  first
  | simpa only [Function.comp_apply, orthogonalLineEquiv_apply] using
      (aemeasurable_comp_orthogonalLineEquiv e he hg).lintegral_prod_right'

/-- Tonelli's theorem in orthogonal line coordinates. -/
theorem lintegral_eq_lintegral_lintegral_line (e : E) (he : ‖e‖ = 1)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g volume) :
    ∫⁻ x, g x = ∫⁻ y : (ℝ ∙ e)ᗮ, ∫⁻ t : ℝ, g ((y : E) + t • e) := by
  first
  | rw [← (measurePreserving_orthogonalLineEquiv e he).lintegral_comp' hg,
      lintegral_prod (fun p ↦ g (orthogonalLineEquiv e he p))
        (aemeasurable_comp_orthogonalLineEquiv e he hg)]
    simp only [orthogonalLineEquiv_apply]

open Filter Topology in
/-- If `∫⁻ g n → 0`, then along a subsequence the integrals of `g` along almost every line
parallel to `e` tend to `0`. Applied to `g n = ‖f n - u‖ₑ`, `L¹` convergence of `f n` to `u`
gives `L¹` convergence of their restrictions on almost every line, along a subsequence. -/
theorem exists_strictMono_ae_tendsto_lintegral_line (e : E) (he : ‖e‖ = 1)
    {g : ℕ → E → ℝ≥0∞} (hg : ∀ n, AEMeasurable (g n) volume)
    (h : Tendsto (fun n ↦ ∫⁻ x, g n x) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ y : (ℝ ∙ e)ᗮ,
      Tendsto (fun j ↦ ∫⁻ t : ℝ, g (φ j) ((y : E) + t • e)) atTop (𝓝 0) :=
  exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral
    (fun n ↦ aemeasurable_lintegral_line e he (hg n))
    (by simpa only [lintegral_eq_lintegral_lintegral_line e he (hg _)] using h)

/-- Volume-a.e. equal sets have a.e. equal parallel sections for almost every transverse point.
The exceptional transverse null set is allowed to depend on the direction. -/
theorem ae_lineSection_eq (e : E) (he : ‖e‖ = 1) {s u : Set E} (h : s =ᵐ[volume] u) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume]
        {t : ℝ | (y : E) + t • e ∈ u} := by
  first
  | have hp := (measurePreserving_orthogonalLineEquiv e he).quasiMeasurePreserving.preimage_ae_eq h
    have hsections := Measure.ae_ae_of_ae_prod hp
    filter_upwards [hsections] with y hy
    filter_upwards [hy] with t ht
    simpa only [mem_preimage, orthogonalLineEquiv_apply, mem_ofPred_eq] using ht

/-- Having interval sections up to null sets is independent of the ambient a.e. representative,
for each fixed unit direction. The intervals may be empty or unbounded. -/
theorem ae_lineSection_ordConnected_iff (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (h : s =ᵐ[volume] u) :
    (∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) ↔
    (∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
      {t : ℝ | (y : E) + t • e ∈ u} =ᵐ[volume] I) := by
  first
  | have transport {v w : Set E} (hvw : v =ᵐ[volume] w)
        (hv : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
          {t : ℝ | (y : E) + t • e ∈ v} =ᵐ[volume] I) :
        ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
          {t : ℝ | (y : E) + t • e ∈ w} =ᵐ[volume] I := by
      filter_upwards [ae_lineSection_eq e he hvw, hv] with y hy hI
      obtain ⟨I, hIc, hIe⟩ := hI
      exact ⟨I, hIc, hy.symm.trans hIe⟩
    exact ⟨transport h, transport h.symm⟩

/-- A Lebesgue-measurable set has Lebesgue-measurable sections on almost every parallel line. -/
theorem ae_nullMeasurableSet_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, NullMeasurableSet {t : ℝ | (y : E) + t • e ∈ s} volume := by
  first
  | filter_upwards [ae_lineSection_eq e he hs.toMeasurable_ae_eq] with y hy
    have hm : MeasurableSet {t : ℝ | (y : E) + t • e ∈ toMeasurable volume s} :=
      (measurableSet_toMeasurable volume s).preimage
        (continuous_const.add (continuous_id.smul continuous_const)).measurable
    exact hm.nullMeasurableSet.congr hy

/-- The lengths of the parallel sections of a Lebesgue-measurable set form an a.e. measurable
extended nonnegative function on the orthogonal subspace. -/
theorem aemeasurable_volume_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    AEMeasurable (fun y : (ℝ ∙ e)ᗮ => volume {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  first
  | have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℝ))
      ((measurableSet_toMeasurable volume s).preimage
        (measurePreserving_orthogonalLineEquiv e he).measurable)
    refine hm.aemeasurable.congr ?_
    filter_upwards [ae_lineSection_eq e he hs.toMeasurable_ae_eq] with y hy
    refine (congrArg volume ?_).trans (measure_congr hy)
    ext t
    simp only [mem_preimage, mem_ofPred_eq, orthogonalLineEquiv_apply]

/-- Cavalieri's formula for Lebesgue-measurable sets in orthogonal line coordinates, with
extended nonnegative values and no finite-volume assumption. -/
theorem volume_eq_lintegral_volume_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = ∫⁻ y : (ℝ ∙ e)ᗮ, volume {t : ℝ | (y : E) + t • e ∈ s} := by
  first
  | have hp := hs.preimage (measurePreserving_orthogonalLineEquiv e he).quasiMeasurePreserving
    rw [← (measurePreserving_orthogonalLineEquiv e he).measure_preimage hs,
      Measure.prod_apply₀ hp]
    congr 1 with y
    congr 1
    ext t
    simp only [mem_preimage, mem_ofPred_eq, orthogonalLineEquiv_apply]

/-- Finite ambient volume implies finite length of almost every parallel section. -/
theorem ae_volume_lineSection_lt_top (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hfinite : volume s ≠ ∞) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume {t : ℝ | (y : E) + t • e ∈ s} < ∞ := by
  first
  | apply ae_lt_top' (aemeasurable_volume_lineSection e he hs)
    rwa [← volume_eq_lintegral_volume_lineSection e he hs]

/-- A Lebesgue-measurable set is null exactly when almost every parallel line section is null. -/
theorem volume_eq_zero_iff_ae_volume_lineSection_eq_zero (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = 0 ↔
      ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume {t : ℝ | (y : E) + t • e ∈ s} = 0 := by
  first
  | rw [volume_eq_lintegral_volume_lineSection e he hs,
      lintegral_eq_zero_iff' (aemeasurable_volume_lineSection e he hs)]
    rfl

/-- The hyperplane sections of a Borel set along a unit vector have measurable volume as a
function of the height. -/
theorem measurable_volume_hyperplaneSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : MeasurableSet s) :
    Measurable fun t : ℝ ↦ volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} := by
  first
  | convert measurable_measure_prodMk_right (μ := (volume : Measure (ℝ ∙ e)ᗮ))
      (hs.preimage (measurePreserving_orthogonalLineEquiv e he).measurable) using 3 with t
    ext y
    simp

/-- Cavalieri's formula along a unit vector: the volume of a Lebesgue-measurable set is the
integral over heights of the volumes of its orthogonal hyperplane sections. -/
theorem volume_eq_lintegral_volume_hyperplaneSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = ∫⁻ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} := by
  first
  | have hBorel {u : Set E} (hu : MeasurableSet u) :
        volume u = ∫⁻ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ u} := by
      rw [← (measurePreserving_orthogonalLineEquiv e he).measure_preimage hu.nullMeasurableSet,
        Measure.prod_apply_symm (hu.preimage (measurePreserving_orthogonalLineEquiv e he).measurable)]
      congr 1 with t
      congr 1 with y
      simp
    -- The sections of `s` lie between those of a measurable subset and a measurable superset,
    -- both of the same volume as `s`.
    obtain ⟨u, hus, hu, hue⟩ := hs.exists_measurable_subset_ae_eq
    refine le_antisymm ?_ ?_
    · rw [← measure_congr hue, hBorel hu]
      exact lintegral_mono fun t ↦ measure_mono fun y hy ↦ hus hy
    · rw [← measure_toMeasurable s, hBorel (measurableSet_toMeasurable volume s)]
      exact lintegral_mono fun t ↦ measure_mono fun y hy ↦ subset_toMeasurable volume s hy

/-- The hyperplane sections of a bounded set have finite volume. -/
theorem _root_.Bornology.IsBounded.volume_hyperplaneSection_lt_top {s : Set E}
    (hs : Bornology.IsBounded s) (e : E) (t : ℝ) :
    volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} < ∞ :=
  ((Isometry.of_dist_eq fun y z : (ℝ ∙ e)ᗮ ↦ by
    simp [dist_add_right, Subtype.dist_eq]).antilipschitzWith.isBounded_preimage hs).measure_lt_top

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The heights along a unit vector of the interior points of a set form an open set. -/
theorem isOpen_image_inner_interior {e : E} (he : ‖e‖ = 1) (s : Set E) :
    IsOpen ((fun x ↦ ⟪e, x⟫) '' interior s) := by
  first
  | refine (innerₛₗ ℝ e).isOpenMap_of_finiteDimensional (fun t ↦ ⟨t • e, ?_⟩) _ isOpen_interior
    simp [he]

/-- The hyperplane section along a unit vector through an interior point of a set has positive
volume. -/
theorem volume_hyperplaneSection_pos (e : E) (he : ‖e‖ = 1) {s : Set E} {c : ℝ}
    (hc : c ∈ (fun x ↦ ⟪e, x⟫) '' interior s) :
    0 < volume {y : (ℝ ∙ e)ᗮ | (y : E) + c • e ∈ s} := by
  first
  | obtain ⟨x, hx, rfl⟩ := hc
    dsimp only
    -- The transverse coordinate of `x` lies in the open preimage of the interior of `s`.
    have hU : IsOpen {y : (ℝ ∙ e)ᗮ | (y : E) + ⟪e, x⟫ • e ∈ interior s} :=
      isOpen_interior.preimage (continuous_subtype_val.add continuous_const)
    refine (hU.measure_pos volume ⟨((orthogonalLineEquiv e he).symm x).1, ?_⟩).trans_le
      (measure_mono fun y (hy : (y : E) + ⟪e, x⟫ • e ∈ interior s) ↦
        (interior_subset hy : (y : E) + ⟪e, x⟫ • e ∈ s))
    simpa [orthogonalLineEquiv_symm_fst] using hx

/-- If an interior point of `s` lies at a height along `e` in the open set `I`, then `s` has
positive volume at heights in `I`. -/
theorem volume_sep_inner_mem_pos {e : E} {s : Set E} {I : Set ℝ} (hI : IsOpen I)
    (h : ∃ x ∈ interior s, ⟪e, x⟫ ∈ I) : 0 < volume {x ∈ s | ⟪e, x⟫ ∈ I} := by
  first
  | obtain ⟨x, hx, hxI⟩ := h
    have hU : IsOpen (interior s ∩ (fun x ↦ ⟪e, x⟫) ⁻¹' I) :=
      isOpen_interior.inter (hI.preimage (continuous_const.inner continuous_id))
    exact (hU.measure_pos volume ⟨x, hx, hxI⟩).trans_le
      (measure_mono fun y hy ↦ ⟨interior_subset hy.1, hy.2⟩)

/-- Cavalieri's formula for the part of a Lebesgue-measurable set at heights in a Borel set `I`
along a unit vector `e`. -/
theorem volume_sep_inner_mem_eq_setLIntegral (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) {I : Set ℝ} (hI : MeasurableSet I) :
    volume {x ∈ s | ⟪e, x⟫ ∈ I} =
      ∫⁻ t in I, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} := by
  first
  | have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
    rw [volume_eq_lintegral_volume_hyperplaneSection e he (s := {x ∈ s | ⟪e, x⟫ ∈ I})
      (hs.inter (hI.preimage hm).nullMeasurableSet), ← lintegral_indicator hI]
    congr 1 with t
    by_cases ht : t ∈ I <;> simp [ht, inner_add_smul e he]

end TauCeti

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Tonelli's theorem along an orthogonal decomposition `E = Kᗮ ⊕ K`. -/
theorem lintegral_eq_lintegral_lintegral_add (K : Submodule ℝ E)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g) :
    ∫⁻ x, g x = ∫⁻ w : Kᗮ, ∫⁻ a : K, g (w + a) := by
  first
  | set e := K.measurableEquivProd (0 : E)
    have he : MeasurePreserving e := by
      simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
        K.measurePreserving_measurableEquivProd (0 : E)
    rw [MeasurePreserving.lintegral_map_equiv g e.symm he.symm, Measure.volume_eq_prod,
      lintegral_prod_symm (fun q ↦ g (e.symm q))
        (hg.comp_quasiMeasurePreserving he.symm.quasiMeasurePreserving)]
    simp [e, add_comm]

/-- In orthogonal coordinates along a subspace, a product of sets has the product volume. -/
theorem volume_preimage_measurableEquivProd_prod (V : Submodule ℝ E) (p : E) (S : Set V)
    (T : Set Vᗮ) : volume (V.measurableEquivProd p ⁻¹' S ×ˢ T) = volume S * volume T := by
  first
  | have hΦ : MeasurePreserving (V.measurableEquivProd p) volume volume := by
      simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
        V.measurePreserving_measurableEquivProd p
    rw [hΦ.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]

/-- A point is recovered from its orthogonal coordinates along a subspace based at `p`. -/
theorem measurableEquivProd_fst_add_add_snd (V : Submodule ℝ E) (p x : E) :
    ((V.measurableEquivProd p x).1 : E) + p + (V.measurableEquivProd p x).2 = x := by
  first
  | conv_rhs => rw [← (V.measurableEquivProd p).symm_apply_apply x]
    rw [measurableEquivProd_symm_apply, vadd_eq_add]
    abel

/-- If `k - p ∈ V`, both orthogonal coordinates of `x` along `V` based at `p` are at most as far
from those of `k` as `x` is from `k`. -/
theorem norm_measurableEquivProd_le (V : Submodule ℝ E) {p k : E} (hkp : k - p ∈ V) (x : E) :
    ‖((V.measurableEquivProd p x).1 : E) + p - k‖ ≤ ‖x - k‖ ∧
      ‖((V.measurableEquivProd p x).2 : E)‖ ≤ ‖x - k‖ := by
  first
    -- Both coordinates are orthogonal projections of `x - k`, since `k - p ∈ V`.
  | have hx : x -ᵥ p = (x - k) + (k - p) := by rw [vsub_eq_sub]; abel
    rw [measurableEquivProd_apply, hx]
    simp only [map_add, V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hkp⟩,
      V.orthogonalProjectionOnto_orthogonal_apply_eq_zero hkp, add_zero, coe_add]
    refine ⟨Eq.trans_le ?_ (V.norm_orthogonalProjectionOnto_apply_le _),
      Vᗮ.norm_orthogonalProjectionOnto_apply_le _⟩
    rw [← norm_coe]
    congr 1
    abel

end Submodule
end -- closes the original EOF section from source line 43
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/OrthogonalSlices.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Section.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Brunn's concavity principle

Let `s ⊆ P × F` be convex, where `F` is a finite-dimensional real inner product space of
dimension `m`. A weighted sum of two fibers of `s` lies in the fiber over the weighted base
point, so the Brunn–Minkowski inequality in `F` shows that the dimension root of the fiber
volume, `p ↦ volume (Prod.mk p ⁻¹' s) ^ (1 / m)`, is concave on the projection `Prod.fst '' s`.
This is **Brunn's concavity principle**. When the fibers have finite volume, a concave function
on a finite-dimensional base is continuous on the interior of its domain, hence so is the fiber
volume itself.

The main specialization concerns the hyperplane sections `{y ∈ (ℝ ∙ e)ᗮ | y + t • e ∈ s}` of a
convex set `s` in a Euclidean space of dimension `n`, along a unit vector `e`. Their volume,
raised to the power `1 / (n - 1)`, is concave in `t` on the interval `⟪e, s⟫`. For a bounded
Borel convex set, the volume of the part `{x ∈ s | ⟪e, x⟫ ≤ c}` below a hyperplane is the
integral of the section volumes up to height `c`, and the continuity of the sections shows that
it is differentiable, with derivative the section volume, at every interior height. These are
the inputs for the classical analysis of equality cases in the Brunn–Minkowski inequality for
convex bodies, which compares the volume distributions of two bodies along each direction.

No dimension assumption is made. In a zero-dimensional fiber space every nonempty fiber is the
whole space and the dimension root is the constant `1` on the projection, so concavity and
continuity hold trivially.

## Main results

* `Convex.concaveOn_volume_real_preimage_prodMk_rpow`: Brunn's concavity principle for fibers.
* `Convex.continuousOn_volume_real_preimage_prodMk`: continuity of fiber volumes on the interior
  of the projection.
* `Convex.concaveOn_volume_real_hyperplaneSection_rpow`: concavity of hyperplane sections.
* `Convex.continuousOn_volume_real_hyperplaneSection`: continuity of hyperplane sections.
* `Convex.hasDerivAt_volume_real_sep_inner_le`: the volume below a hyperplane has the section
  volume as derivative.
* `TauCeti.volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le`: multiplicative
  Brunn–Minkowski for the hyperplane sections of two sets, at the weighted height.

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, Section 4, for Brunn's concavity principle as a consequence of the Brunn–Minkowski
  inequality.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.1.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace

section Fiber

variable {P F : Type*} [AddCommGroup P] [Module ℝ P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Brunn's concavity principle**, extended form: the dimension root of the fiber volume of
a convex set is concave along segments joining points with nonempty fibers. Fibers may have
infinite volume, and no dimension assumption is needed. -/
theorem Convex.mul_volume_preimage_prodMk_rpow_add_mul_volume_preimage_prodMk_rpow_le
    {s : Set (P × F)} (hs : Convex ℝ s) {p q : P} (hp : (Prod.mk p ⁻¹' s).Nonempty)
    (hq : (Prod.mk q ⁻¹' s).Nonempty) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ENNReal.ofReal a * volume (Prod.mk p ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹ +
      ENNReal.ofReal b * volume (Prod.mk q ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹ ≤
        volume (Prod.mk (a • p + b • q) ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹ := by
  first
  | have hsub := hs.smul_preimage_prodMk_add_smul_preimage_prodMk_subset p q ha hb hab
    rcases eq_or_ne (Module.finrank ℝ F) 0 with hn | hn
    · -- In dimension zero every dimension root is `1`, so the claim is `a + b ≤ 1`.
      simp [hn, ← ENNReal.ofReal_add ha hb, hab]
    · exact (TauCeti.mul_volume_rpow_add_mul_volume_rpow_le hn hp
        (Convex.nullMeasurableSet volume (hs.preimage_prodMk p)) hq
        (Convex.nullMeasurableSet volume (hs.preimage_prodMk q)) ha hb).trans
        (ENNReal.rpow_le_rpow (measure_mono hsub) (by positivity))

/-- **Brunn's concavity principle**: if every fiber of a convex set has finite volume, the
dimension root of the fiber volume is concave on the projection of the set. -/
theorem Convex.concaveOn_volume_real_preimage_prodMk_rpow {s : Set (P × F)} (hs : Convex ℝ s)
    (hfin : ∀ p, volume (Prod.mk p ⁻¹' s) ≠ ∞) :
    ConcaveOn ℝ (Prod.fst '' s)
      (fun p ↦ volume.real (Prod.mk p ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹) := by
  first
  | refine ⟨hs.linear_image (LinearMap.fst ℝ P F), ?_⟩
    rintro _ ⟨⟨p, y⟩, hy, rfl⟩ _ ⟨⟨q, z⟩, hz, rfl⟩ a b ha hb hab
    have hr : (0 : ℝ) ≤ (Module.finrank ℝ F : ℝ)⁻¹ := by positivity
    have h := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hr (hfin _))
      (hs.mul_volume_preimage_prodMk_rpow_add_mul_volume_preimage_prodMk_rpow_le
        ⟨y, hy⟩ ⟨z, hz⟩ ha hb hab)
    rwa [ENNReal.toReal_add (by finiteness [ENNReal.rpow_ne_top_of_nonneg hr (hfin p)])
        (by finiteness [ENNReal.rpow_ne_top_of_nonneg hr (hfin q)]),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h

end Fiber

section FiberContinuous

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- If every fiber of a convex set has finite volume, the fiber volume is continuous on the
interior of the projection of the set. This follows from Brunn's concavity principle. -/
theorem Convex.continuousOn_volume_real_preimage_prodMk {s : Set (P × F)} (hs : Convex ℝ s)
    (hfin : ∀ p, volume (Prod.mk p ⁻¹' s) ≠ ∞) :
    ContinuousOn (fun p ↦ volume.real (Prod.mk p ⁻¹' s)) (interior (Prod.fst '' s)) := by
  first
  | rcases eq_or_ne (Module.finrank ℝ F) 0 with hn | hn
    · -- In dimension zero every nonempty fiber is the whole space.
      have : Subsingleton F := Module.finrank_zero_iff.1 hn
      refine continuousOn_const (c := volume.real (univ : Set F)).congr fun p hp ↦ ?_
      obtain ⟨⟨p, y⟩, hy, rfl⟩ := interior_subset hp
      rw [(Subsingleton.eq_univ_of_nonempty ⟨y, hy⟩ : Prod.mk p ⁻¹' s = univ)]
    · refine ((hs.concaveOn_volume_real_preimage_prodMk_rpow hfin).continuousOn_interior.pow
        (Module.finrank ℝ F)).congr fun p _ ↦ ?_
      exact (Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn).symm

end FiberContinuous

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hyperplane sections of `s` along `e`, as fibers of a subset of `ℝ × (ℝ ∙ e)ᗮ`. -/
private def hyperplaneFibers (e : E) (s : Set E) : Set (ℝ × (ℝ ∙ e)ᗮ) :=
  {z | (z.2 : E) + z.1 • e ∈ s}

private theorem convex_hyperplaneFibers (e : E) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (hyperplaneFibers e s) := by
  first
  | convert hs.linear_preimage ((ℝ ∙ e)ᗮ.subtype ∘ₗ LinearMap.snd ℝ ℝ (ℝ ∙ e)ᗮ +
      (LinearMap.fst ℝ ℝ (ℝ ∙ e)ᗮ).smulRight e) using 1
    ext z
    simp [hyperplaneFibers]

/-- Along a unit vector, the heights with a nonempty hyperplane section are the values of the
inner product on the set. -/
private theorem fst_image_hyperplaneFibers (e : E) (he : ‖e‖ = 1) (s : Set E) :
    Prod.fst '' hyperplaneFibers e s = (fun x ↦ ⟪e, x⟫) '' s := by
  first
  | ext t
    constructor
    · rintro ⟨⟨t, y⟩, hy, rfl⟩
      exact ⟨_, hy, inner_add_smul e he y t⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(⟪e, x⟫, ((orthogonalLineEquiv e he).symm x).1), ?_, rfl⟩
      simpa [hyperplaneFibers, orthogonalLineEquiv_symm_fst] using hx

/-- A weighted sum of hyperplane sections of two sets lies in the hyperplane section of their
weighted sum, at the weighted height. -/
theorem smul_hyperplaneSection_add_smul_hyperplaneSection_subset (e : E) (K L : Set E)
    (a b s t : ℝ) :
    a • {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ K} + b • {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ L} ⊆
      {y : (ℝ ∙ e)ᗮ | (y : E) + (a * s + b * t) • e ∈ a • K + b • L} := by
  first
  | rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨a • ((y : E) + s • e), smul_mem_smul_set hy, b • ((z : E) + t • e),
      smul_mem_smul_set hz, ?_⟩
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, add_smul, smul_smul]
    abel

variable [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

/-- **Brunn's concavity principle** for hyperplane sections, extended form. Along a unit vector
`e` in a space of dimension `n`, the `(n - 1)`-th root of the section volume of a convex set is
concave on the heights at which the section is nonempty. -/
theorem _root_.Convex.mul_volume_hyperplaneSection_rpow_add_mul_volume_hyperplaneSection_rpow_le
    {s : Set E} (hs : Convex ℝ s) {e : E} (he : ‖e‖ = 1) {t u : ℝ}
    (ht : t ∈ (fun x ↦ ⟪e, x⟫) '' s) (hu : u ∈ (fun x ↦ ⟪e, x⟫) '' s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ENNReal.ofReal a * volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ^
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹ +
      ENNReal.ofReal b * volume {y : (ℝ ∙ e)ᗮ | (y : E) + u • e ∈ s} ^
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹ ≤
        volume {y : (ℝ ∙ e)ᗮ | (y : E) + (a * t + b * u) • e ∈ s} ^
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹ := by
  first
  | rw [← fst_image_hyperplaneFibers e he] at ht hu
    obtain ⟨⟨t, y⟩, hy, rfl⟩ := ht
    obtain ⟨⟨u, z⟩, hz, rfl⟩ := hu
    rw [← Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one
      (norm_ne_zero_iff.1 (he ▸ one_ne_zero))]
    exact Convex.mul_volume_preimage_prodMk_rpow_add_mul_volume_preimage_prodMk_rpow_le
      (convex_hyperplaneFibers e hs) ⟨y, hy⟩ ⟨z, hz⟩ ha hb hab

/-- **Brunn's concavity principle** for hyperplane sections. If the hyperplane sections of a
convex set along a unit vector `e` have finite volume, then in a space of dimension `n` the
`(n - 1)`-th root of their volume is concave on the interval `⟪e, s⟫`. -/
theorem _root_.Convex.concaveOn_volume_real_hyperplaneSection_rpow {s : Set E} (hs : Convex ℝ s)
    {e : E} (he : ‖e‖ = 1) (hfin : ∀ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ≠ ∞) :
    ConcaveOn ℝ ((fun x ↦ ⟪e, x⟫) '' s) (fun t : ℝ ↦
      volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ^
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹) := by
  first
  | rw [← fst_image_hyperplaneFibers e he,
      ← Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one
        (norm_ne_zero_iff.1 (he ▸ one_ne_zero))]
    exact (convex_hyperplaneFibers e hs).concaveOn_volume_real_preimage_prodMk_rpow hfin

/-- If the hyperplane sections of a convex set along a unit vector have finite volume, their
volume is continuous on the interior of the interval `⟪e, s⟫`. -/
theorem _root_.Convex.continuousOn_volume_real_hyperplaneSection {s : Set E} (hs : Convex ℝ s)
    {e : E} (he : ‖e‖ = 1) (hfin : ∀ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ≠ ∞) :
    ContinuousOn (fun t : ℝ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s})
      (interior ((fun x ↦ ⟪e, x⟫) '' s)) := by
  first
  | rw [← fst_image_hyperplaneFibers e he]
    exact (convex_hyperplaneFibers e hs).continuousOn_volume_real_preimage_prodMk hfin

/-- For a bounded Borel convex set, the volume of the part below the hyperplane `⟪e, x⟫ = c` is
differentiable in `c` at every height interior to `⟪e, s⟫`, and its derivative is the volume of
the hyperplane section at height `c`. -/
theorem _root_.Convex.hasDerivAt_volume_real_sep_inner_le {s : Set E} (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hsm : MeasurableSet s) {e : E} (he : ‖e‖ = 1) {c : ℝ}
    (hc : c ∈ interior ((fun x ↦ ⟪e, x⟫) '' s)) :
    HasDerivAt (fun c ↦ volume.real {x ∈ s | ⟪e, x⟫ ≤ c})
      (volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + c • e ∈ s}) c := by
  first
  | set φ : ℝ → ℝ := fun t ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s}
    have hfin (t : ℝ) := (hsb.volume_hyperplaneSection_lt_top e t).ne
    have hm := measurable_volume_hyperplaneSection e he hsm
    -- `φ` is integrable since its integral is the volume of `s`.
    have hφi : Integrable φ := integrable_toReal_of_lintegral_ne_top hm.aemeasurable (by
      rw [← volume_eq_lintegral_volume_hyperplaneSection e he hsm.nullMeasurableSet]
      exact hsb.measure_lt_top.ne)
    -- Choose a height `a < c` below `s`; near `c` the volume below `c'` is an interval integral.
    obtain ⟨m, hmin⟩ := ((innerSL ℝ e).lipschitzWith.isBounded_image hsb).bddBelow
    set a := min m c - 1
    have ha (x : E) (hx : x ∈ s) : a < ⟪e, x⟫ :=
      (sub_one_lt _).trans_le ((min_le_left _ _).trans (hmin ⟨x, hx, rfl⟩))
    have hvol : ∀ᶠ c' in nhds c, volume.real {x ∈ s | ⟪e, x⟫ ≤ c'} = ∫ t in a..c', φ t := by
      filter_upwards [lt_mem_nhds ((sub_one_lt _).trans_le (min_le_right m c))] with c' hc'
      have hsep : {x ∈ s | ⟪e, x⟫ ≤ c'} = {x ∈ s | ⟪e, x⟫ ∈ Ioc a c'} := by
        ext x
        exact and_congr_right fun hx ↦ ⟨fun h ↦ ⟨ha x hx, h⟩, And.right⟩
      have hlin : ∫⁻ t in Ioc a c', volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} =
          ENNReal.ofReal (∫ t in Ioc a c', φ t) := by
        rw [ofReal_integral_eq_lintegral_ofReal hφi.integrableOn
          (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
        exact setLIntegral_congr_fun measurableSet_Ioc fun t _ ↦
          (ENNReal.ofReal_toReal (hfin t)).symm
      rw [intervalIntegral.integral_of_le hc'.le, measureReal_def, hsep,
        volume_sep_inner_mem_eq_setLIntegral e he hsm.nullMeasurableSet measurableSet_Ioc, hlin]
      exact ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
        fun _ _ ↦ ENNReal.toReal_nonneg)
    -- By Brunn's concavity principle `φ` is continuous at the interior height `c`.
    have hcont : ContinuousAt φ c :=
      (hs.continuousOn_volume_real_hyperplaneSection he hfin).continuousAt
        (isOpen_interior.mem_nhds hc)
    exact (intervalIntegral.integral_hasDerivAt_right hφi.intervalIntegrable
      hm.ennreal_toReal.stronglyMeasurable.stronglyMeasurableAtFilter hcont).congr_of_eventuallyEq
      hvol

/-- **Multiplicative Brunn–Minkowski for hyperplane sections.** The weighted geometric mean of the
volumes of a section of `K` and a section of `L` is at most the volume of the section of
`(1 - θ) • K + θ • L` at the weighted height. -/
theorem volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le (e : E) {K L : Set E}
    (hK : MeasurableSet K) (hL : MeasurableSet L) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (s t : ℝ) :
    volume {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ K} ^ (1 - θ) *
        volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ L} ^ θ ≤
      volume {y : (ℝ ∙ e)ᗮ | (y : E) + ((1 - θ) * s + θ * t) • e ∈ (1 - θ) • K + θ • L} := by
  first
  | have hsec {u : ℝ} {S : Set E} (hS : MeasurableSet S) :
        MeasurableSet {y : (ℝ ∙ e)ᗮ | (y : E) + u • e ∈ S} :=
      hS.preimage (continuous_subtype_val.add continuous_const).measurable
    exact (volume_rpow_mul_volume_rpow_le (hsec hK).nullMeasurableSet (hsec hL).nullMeasurableSet
      hθ₀ hθ₁).trans (measure_mono
        (smul_hyperplaneSection_add_smul_hyperplaneSection_subset e K L (1 - θ) θ s t))

end TauCeti
end -- closes the original EOF section from source line 61
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Section.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Function/Monotone.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Measurability of partially monotone functions

This file gives a measurability criterion for real functions that are monotone on an open
interval and constant away from its endpoints.
-/

public section

open Set

namespace TauCeti

/-- A real function that is monotone on an open interval and equal to a fixed constant strictly
outside the closed interval is measurable. No relation between the endpoints is required. -/
theorem measurable_of_monotoneOn_Ioo_of_eq_const {f : ℝ → ℝ} {a b c : ℝ}
    (hf : MonotoneOn f (Ioo a b)) (hconst : ∀ x : ℝ, x < a ∨ b < x → f x = c) :
    Measurable f := by
  first
  | refine measurable_of_Iic fun x ↦ ?_
    have hcover : f ⁻¹' Iic x = (f ⁻¹' Iic x ∩ Ioo a b) ∪ (f ⁻¹' Iic x ∩ {a, b}) ∪
        (f ⁻¹' Iic x ∩ (Iio a ∪ Ioi b)) := by
      rw [← inter_union_distrib_left, ← inter_union_distrib_left, left_eq_inter]
      intro y _
      simp only [mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff, mem_Iio, mem_Ioi]
      grind
    have hconn : (f ⁻¹' Iic x ∩ Ioo a b).OrdConnected := by
      refine ⟨fun y hy z hz w hw ↦ ?_⟩
      have hw' : w ∈ Ioo a b := ⟨hy.2.1.trans_le hw.1, hw.2.trans_lt hz.2.2⟩
      exact ⟨(hf hw' hz.2 hw.2).trans hz.1, hw'⟩
    have hjunk : MeasurableSet (f ⁻¹' Iic x ∩ (Iio a ∪ Ioi b)) := by
      by_cases hx : c ≤ x
      · rw [inter_eq_right.mpr fun y hy ↦ by simpa [hconst y hy] using hx]
        exact measurableSet_Iio.union measurableSet_Ioi
      · rw [eq_empty_of_forall_notMem (s := f ⁻¹' Iic x ∩ (Iio a ∪ Ioi b)) fun y hy ↦
          hx (by simpa [hconst y hy.2] using hy.1)]
        exact MeasurableSet.empty
    rw [hcover]
    exact (hconn.measurableSet.union ((toFinite _).subset inter_subset_right).measurableSet).union
      hjunk

end TauCeti
end -- closes the original EOF section from source line 17
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Function/Monotone.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Mod0MeasureIso.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Measure-preserving isomorphisms modulo null sets

`Mod0MeasureIso` bundles two measurable maps between measured spaces which push the two measures
forward onto one another and which are mutually inverse outside a null set. It is the
modulo-null-set counterpart of `MeasurePreserving`, for the situation in which two spaces carry
the same law only up to null sets, as happens when standard transport constructions are composed.

The packaging is adapted from Cameron Freer's independent implementation in
`Graphon/MeasureIso.lean` at commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>.
The original work is copyright Cameron Freer and licensed under Apache 2.0.

## Main results

* `TauCeti.Mod0MeasureIso` is the structure; `TauCeti.Mod0MeasureIso.measurePreserving` and
  `TauCeti.Mod0MeasureIso.measurePreserving_invFun` read off the two measure-preserving maps,
  `TauCeti.Mod0MeasureIso.symm` inverts an isomorphism, and `TauCeti.Mod0MeasureIso.trans`
  composes two of them;
* `TauCeti.embeddingRealMod0MeasureIso` transports a standard-Borel space into `ℝ` by
  `embeddingReal`;
* `TauCeti.mod0MeasureIso_to_unitInterval` turns a mod-zero isomorphism into `ℝ` carrying the
  unit interval measure into measure-preserving maps in both directions between that space and
  the unit interval.

The instance built from the cumulative distribution function and the quantile of an atomless
real law is `MeasureTheory.Measure.realMod0MeasureIso`, in `TauCeti.Probability.Quantile`.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped unitInterval

namespace TauCeti

/-- Two measurable maps that push `μ` and `ν` forward onto one another and that are mutually
inverse outside a null set: a measure-preserving isomorphism of the two measured spaces modulo
null sets. -/
structure Mod0MeasureIso (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) where
  /-- The forward map, which pushes `μ` forward to `ν`. -/
  toFun : α → β
  /-- The backward map, which pushes `ν` forward to `μ`. -/
  invFun : β → α
  measurable_toFun : Measurable toFun
  measurable_invFun : Measurable invFun
  map_toFun : Measure.map toFun μ = ν
  map_invFun : Measure.map invFun ν = μ
  left_inv_ae : (fun x => invFun (toFun x)) =ᵐ[μ] id
  right_inv_ae : (fun y => toFun (invFun y)) =ᵐ[ν] id

/-- The forward map of a mod-zero isomorphism preserves the measure. -/
theorem Mod0MeasureIso.measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    MeasurePreserving e.toFun μ ν :=
  ⟨e.measurable_toFun, e.map_toFun⟩

/-- The backward map of a mod-zero isomorphism preserves the measure. -/
theorem Mod0MeasureIso.measurePreserving_invFun {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    MeasurePreserving e.invFun ν μ :=
  ⟨e.measurable_invFun, e.map_invFun⟩

/-- The inverse of a mod-zero isomorphism is a mod-zero isomorphism between the reversed spaces,
with the two maps interchanged. -/
def Mod0MeasureIso.symm {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) : Mod0MeasureIso β α ν μ where
  toFun := e.invFun
  invFun := e.toFun
  measurable_toFun := e.measurable_invFun
  measurable_invFun := e.measurable_toFun
  map_toFun := e.map_invFun
  map_invFun := e.map_toFun
  left_inv_ae := e.right_inv_ae
  right_inv_ae := e.left_inv_ae

@[simp]
theorem Mod0MeasureIso.symm_toFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    e.symm.toFun = e.invFun :=
  (rfl)

@[simp]
theorem Mod0MeasureIso.symm_invFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    e.symm.invFun = e.toFun :=
  (rfl)

/-- The composition of two mod-zero isomorphisms is again a mod-zero isomorphism. -/
def Mod0MeasureIso.trans {α β γ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    Mod0MeasureIso α γ μ ξ where
  toFun := f.toFun ∘ e.toFun
  invFun := e.invFun ∘ f.invFun
  measurable_toFun := f.measurable_toFun.comp e.measurable_toFun
  measurable_invFun := e.measurable_invFun.comp f.measurable_invFun
  map_toFun := by
    first
    | rw [← Measure.map_map f.measurable_toFun e.measurable_toFun, e.map_toFun, f.map_toFun]
  map_invFun := by
    first
    | rw [← Measure.map_map e.measurable_invFun f.measurable_invFun, f.map_invFun, e.map_invFun]
  left_inv_ae := by
    first
    | have hqmp : QuasiMeasurePreserving e.toFun μ ν := by
        refine ⟨e.measurable_toFun, ?_⟩
        rw [e.map_toFun]
      have h1 := hqmp.ae_eq_comp f.left_inv_ae
      filter_upwards [h1, e.left_inv_ae] with x hx1 hx2
      simp only [Function.comp_apply, id_eq] at hx1 hx2 ⊢
      rw [hx1]
      exact hx2
  right_inv_ae := by
    first
    | have hqmp : QuasiMeasurePreserving f.invFun ξ ν := by
        refine ⟨f.measurable_invFun, ?_⟩
        rw [f.map_invFun]
      have h2 := hqmp.ae_eq_comp e.right_inv_ae
      filter_upwards [h2, f.right_inv_ae] with y hy1 hy2
      simp only [Function.comp_apply, id_eq] at hy1 hy2 ⊢
      rw [hy1]
      exact hy2

@[simp]
theorem Mod0MeasureIso.trans_toFun {α β γ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    (e.trans f).toFun = f.toFun ∘ e.toFun :=
  (rfl)

@[simp]
theorem Mod0MeasureIso.trans_invFun {α β γ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    (e.trans f).invFun = e.invFun ∘ f.invFun :=
  (rfl)

/-- Transporting a standard-Borel space into `ℝ` by `embeddingReal` is a mod-zero isomorphism
onto the pushforward of the measure. -/
def embeddingRealMod0MeasureIso (α) [MeasurableSpace α] [StandardBorelSpace α] (μ : Measure α)
    [Nonempty α] : Mod0MeasureIso α ℝ μ (Measure.map (embeddingReal α) μ) :=
  let he := measurableEmbedding_embeddingReal α
  { toFun := embeddingReal α
    invFun := he.invFun
    measurable_toFun := he.measurable
    measurable_invFun := he.measurable_invFun
    map_toFun := rfl
    map_invFun := by
      first
      | rw [Measure.map_map he.measurable_invFun he.measurable]
        have h : he.invFun ∘ embeddingReal α = id := funext he.leftInverse_invFun
        rw [h, Measure.map_id]
    left_inv_ae := ae_of_all _ he.leftInverse_invFun
    right_inv_ae := by
      first
      | have hmem : ∀ᵐ y ∂(Measure.map (embeddingReal α) μ), y ∈ range (embeddingReal α) :=
          ae_map_mem_range he.measurableSet_range he.measurable.aemeasurable
        filter_upwards [hmem] with y hy
        obtain ⟨x, rfl⟩ := hy
        simp only [id_eq]
        rw [he.leftInverse_invFun x] }

@[simp]
theorem embeddingRealMod0MeasureIso_toFun (α) [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [Nonempty α] :
    (embeddingRealMod0MeasureIso α μ).toFun = embeddingReal α :=
  (rfl)

@[simp]
theorem embeddingRealMod0MeasureIso_invFun (α) [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [Nonempty α] :
    (embeddingRealMod0MeasureIso α μ).invFun = (measurableEmbedding_embeddingReal α).invFun :=
  (rfl)

/-- A mod-zero isomorphism into `ℝ` carrying the unit interval measure gives measure-preserving
maps in both directions between the space and the unit interval: the forward map clipped to the
unit interval, and the backward map composed with the coercion. Since the forward map takes
values in the unit interval outside a null set, the two maps are mutually inverse almost
everywhere. -/
theorem mod0MeasureIso_to_unitInterval
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (e : Mod0MeasureIso α ℝ μ (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∃ (f : α → I) (g : I → α),
      MeasurePreserving f μ volume ∧ MeasurePreserving g volume μ ∧
      (∀ᵐ x ∂μ, g (f x) = x) ∧ (∀ᵐ y ∂(volume : Measure I), f (g y) = y) := by
  first
  | have hempty : (I : Set ℝ)ᶜ ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc]
      grind
    have hnull : (volume.restrict (Set.Icc (0 : ℝ) 1)) (I : Set ℝ)ᶜ = 0 := by
      rw [Measure.restrict_apply measurableSet_Icc.compl, hempty, measure_empty]
    have hmem : ∀ᵐ x ∂μ, e.toFun x ∈ I := by
      have hpre : {x | e.toFun x ∉ I} = e.toFun ⁻¹' (I : Set ℝ)ᶜ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff]
      rw [ae_iff, hpre]
      exact e.measurePreserving.preimage_null hnull
    have hclip : ∀ x : α, max (0 : ℝ) (min 1 (e.toFun x)) ∈ I := by
      intro x
      exact ⟨by grind, by grind⟩
    let f : α → I := fun x => ⟨max (0 : ℝ) (min 1 (e.toFun x)), hclip x⟩
    let g : I → α := fun y => e.invFun y.1
    have hfmeas : Measurable f := by
      dsimp [f]
      exact Measurable.subtype_mk
        (measurable_const.max (measurable_const.min e.measurable_toFun)) (h := hclip)
    have hgmeas : Measurable g := by
      dsimp [g]
      exact e.measurable_invFun.comp measurable_subtype_coe
    have hclip_id : ∀ᵐ x ∂μ, max (0 : ℝ) (min 1 (e.toFun x)) = e.toFun x := by
      filter_upwards [hmem] with x hx
      grind
    have hgf : (g ∘ f) =ᵐ[μ] id := by
      filter_upwards [hclip_id, e.left_inv_ae] with x hx hx'
      simp [f, g, hx, hx']
    have hval : (fun y : I => e.toFun (e.invFun (y : ℝ))) =ᵐ[(volume : Measure I)]
        (fun y : I => (y : ℝ)) := by
      simpa [Function.comp_def] using
        (unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae_eq_comp e.right_inv_ae)
    have hfg : (f ∘ g) =ᵐ[(volume : Measure I)] id := by
      filter_upwards [hval] with y hy
      apply Subtype.ext
      simp only [Function.comp_apply, f, g, id_eq]
      rw [hy]
      grind [y.2.1, y.2.2]
    have hmapf : Measure.map f μ = volume := by
      apply unitInterval.measurableEmbedding_coe.map_injective
      have hcomp : (Subtype.val : I → ℝ) ∘ f =ᵐ[μ] e.toFun := hclip_id
      rw [Measure.map_map unitInterval.measurePreserving_coe.measurable hfmeas,
        Measure.map_congr hcomp, unitInterval.measurePreserving_coe.map_eq]
      exact e.map_toFun
    have hmapg : Measure.map g volume = μ := by
      have hcomp : g = e.invFun ∘ (Subtype.val : I → ℝ) := by
        funext y
        rfl
      rw [hcomp, ← Measure.map_map e.measurable_invFun measurable_subtype_coe,
        unitInterval.measurePreserving_coe.map_eq, e.map_invFun]
    exact ⟨f, g, ⟨hfmeas, hmapf⟩, ⟨hgmeas, hmapg⟩, hgf, hfg⟩

end TauCeti
end -- closes the original EOF section from source line 44
end -- closes the original EOF section from source line 42
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Mod0MeasureIso.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Group/Measure.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: change of variables in set integrals along a measurable embedding.

/-!
# Measures and the group operations

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells. Dually, a set that each point sees
in only boundedly many of infinitely many translates inside a subgroup of finite measure is null
in that subgroup; over a local field this shows without Fubini's theorem that a set meeting every
line of a fixed direction in boundedly many points is null. It also records that inverting or
negating a probability measure gives a probability measure, so that the law of `X⁻¹` or `-X` can
be used wherever a probability law is expected, and that restricting an inversion-invariant
measure to a symmetric set, or weighting it by an even density, keeps it inversion-invariant.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
* `Measure.measure_inter_addSubgroup_eq_zero_of_encard_le`: if `x + w j ∈ Z` holds for at most
  `D` indices `j`, for every `x`, where the translations `w j` range over infinitely many indices
  in a subgroup `H` of finite measure, then `Z ∩ H` is null.
* `Measure.isProbabilityMeasure_inv`, `Measure.isProbabilityMeasure_neg`: the inverse and the
  negation of a probability measure are probability measures.
* `Measure.map_inv_comp`, `Measure.map_neg_comp`: composing a pushforward from the inverted or
  negated measure with inversion or negation recovers the original pushforward.
* `Measure.ae_inv_mem_preimage`, `Measure.ae_neg_mem_preimage`: a full-mass set reflects to a
  full-mass set for the inverted or negated measure.
* `Measure.isInvInvariant_restrict`, `Measure.isNegInvariant_restrict`,
  `Measure.isInvInvariant_withDensity`, `Measure.isNegInvariant_withDensity`: restriction to a
  symmetric set and an even density preserve inversion or negation invariance.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem _root_.MeasureTheory.Measure.measure_biUnion_sub_mem
    (mu : Measure E) [mu.IsAddRightInvariant]
    {G F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  first
  | rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
      fun w _ ↦ by
        have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
        rw [h]
        exact measurableSet_preimage (measurable_id.add_const (-w)) hFm]
    have htranslate (w : E) : mu {y : E | y - w ∈ F} = mu F := by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
      rw [h, measure_preimage_add_right]
    simp_rw [htranslate]
    simp

/-- A set that every point sees in boundedly many translates is null inside a subgroup of finite
measure. Precisely, let `w : ι → E` be a family, indexed by an infinite type, of elements of a
measurable subgroup `H` of finite measure, and suppose that for every `x` at most `D` indices `j`
have `x + w j ∈ Z`. Then `Z ∩ H` is null for every right-invariant measure. -/
theorem _root_.MeasureTheory.Measure.measure_inter_addSubgroup_eq_zero_of_encard_le
    {ι : Type*} [Infinite ι] (μ : Measure E) [μ.IsAddRightInvariant] {Z : Set E}
    (hZ : MeasurableSet Z) {H : AddSubgroup E} (hH : MeasurableSet (H : Set E))
    (hμH : μ H ≠ ∞) {w : ι → E} (hw : ∀ j, w j ∈ H) {D : ℕ}
    (hD : ∀ x, {j | x + w j ∈ Z}.encard ≤ D) :
    μ (Z ∩ H) = 0 := by
  first
  | classical
    have hZH : MeasurableSet (Z ∩ H) := hZ.inter hH
    -- The translates `(· + w j) ⁻¹' (Z ∩ H)` all have the measure of `Z ∩ H` and lie in `H`, and no
    -- point lies in more than `D` of them. Integrating the number of them containing `x`, for `j` in
    -- a finite set `s`, bounds `#s` copies of `μ (Z ∩ H)` by `D` copies of `μ H`.
    have key (s : Finset ι) : (s.card : ℝ≥0∞) * μ (Z ∩ H) ≤ D * μ H := by
      calc (s.card : ℝ≥0∞) * μ (Z ∩ H)
          = ∑ j ∈ s, μ ((· + w j) ⁻¹' (Z ∩ H)) := by
            rw [Finset.sum_congr rfl fun j _ ↦ measure_preimage_add_right μ (w j) (Z ∩ H)]
            simp
        _ = ∫⁻ x, ∑ j ∈ s, ((· + w j) ⁻¹' (Z ∩ H)).indicator 1 x ∂μ := by
            rw [lintegral_finsetSum _ fun j _ ↦
              (measurable_one.indicator (measurable_add_const (w j) hZH))]
            simp_rw [lintegral_indicator_one (measurable_add_const _ hZH)]
        _ ≤ ∫⁻ x, (H : Set E).indicator (fun _ ↦ (D : ℝ≥0∞)) x ∂μ := by
            refine lintegral_mono fun x ↦ ?_
            by_cases hx : x ∈ H
            · rw [indicator_of_mem hx]
              calc ∑ j ∈ s, ((· + w j) ⁻¹' (Z ∩ H)).indicator 1 x
                  = ((s.filter fun j ↦ x + w j ∈ Z ∩ H).card : ℝ≥0∞) := by
                    simp [indicator_apply, Finset.sum_boole]
                _ ≤ D := by
                    have := (encard_le_encard (s := ↑(s.filter fun j ↦ x + w j ∈ Z ∩ H))
                      (t := {j | x + w j ∈ Z}) fun j hj ↦ by
                        simp only [Finset.coe_filter, mem_ofPred_eq] at hj
                        exact hj.2.1).trans (hD x)
                    rw [encard_coe_eq_coe_finsetCard] at this
                    exact_mod_cast this
            · rw [indicator_of_notMem hx]
              refine (Finset.sum_eq_zero fun j _ ↦ indicator_of_notMem ?_ _).le
              exact fun h ↦ hx ((H.add_mem_cancel_right (hw j)).mp h.2)
        _ = D * μ H := lintegral_indicator_const hH _
    by_contra h0
    have htop : (D : ℝ≥0∞) * μ H / μ (Z ∩ H) ≠ ∞ :=
      ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hμH) h0
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt htop
    obtain ⟨s, rfl⟩ := Infinite.exists_subset_card_eq ι N
    exact ((ENNReal.le_div_iff_mul_le (Or.inl h0)
      (Or.inl (ne_top_of_le_ne_top hμH (measure_mono inter_subset_right)))).mpr (key s)).not_gt hN

end TauCeti

namespace MeasureTheory.Measure

/-- The inverse of a probability measure is a probability measure. -/
@[to_additive /-- The negation of a probability measure is a probability measure. -/]
instance isProbabilityMeasure_inv {G : Type*} [MeasurableSpace G] [Inv G] (μ : Measure G)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure μ.inv := by
  first
  | rw [inv_def]
    infer_instance

/-- Pushing an inverted measure forward along `f` after inversion gives the pushforward of the
original measure along `f`. -/
@[to_additive /-- Pushing a negated measure forward along `f` after negation gives the pushforward
of the original measure along `f`. -/]
theorem map_inv_comp {G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [InvolutiveInv G]
    [MeasurableInv G] (μ : Measure G) {f : G → H} (hf : AEMeasurable (f ∘ Inv.inv) μ.inv) :
    μ.inv.map (f ∘ Inv.inv) = μ.map f := by
  first
  | rw [inv_def] at hf ⊢
    rw [AEMeasurable.map_map_of_aemeasurable hf measurable_inv.aemeasurable]
    congr 1
    ext x
    simp

/-- A set of full measure reflects to a set of full measure for the inverted measure. -/
@[to_additive /-- A set of full measure reflects to a set of full measure for the negated
measure. -/]
theorem ae_inv_mem_preimage {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G]
    (μ : Measure G) {s : Set G} (hs : MeasurableSet s) (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ.inv, x ∈ Inv.inv ⁻¹' s := by
  first
  | simp only [Set.mem_preimage]
    rw [inv_def, ae_map_iff measurable_inv.aemeasurable (measurable_inv hs)]
    simpa only [inv_inv] using hμs

section InvolutiveInv

variable {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] {μ : Measure G}

/-- The restriction of an inversion-invariant measure to a set closed under inversion is
inversion-invariant. -/
@[to_additive /-- The restriction of a negation-invariant measure to a set closed under negation
is negation-invariant. -/]
theorem isInvInvariant_restrict [μ.IsInvInvariant] {s : Set G} (hs : s⁻¹ = s) :
    (μ.restrict s).IsInvInvariant := by
  first
  | refine ⟨Measure.ext fun t ht ↦ ?_⟩
    rw [inv_apply, restrict_apply ht.inv, restrict_apply ht, ← measure_inv μ, Set.inter_inv,
      inv_inv, hs]

/-- An inversion-invariant measure weighted by a density invariant under inversion is
inversion-invariant. -/
@[to_additive /-- A negation-invariant measure weighted by an even density is
negation-invariant. -/]
theorem isInvInvariant_withDensity [μ.IsInvInvariant] {f : G → ℝ≥0∞} (hf : ∀ x, f x⁻¹ = f x) :
    (μ.withDensity f).IsInvInvariant := by
  first
  | refine ⟨Measure.ext fun t ht ↦ ?_⟩
    rw [inv_apply, withDensity_apply _ ht.inv, withDensity_apply _ ht, ← Set.inv_preimage]
    simpa only [hf] using (measurePreserving_inv μ).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.inv G).measurableEmbedding f t

end InvolutiveInv

end MeasureTheory.Measure
end -- closes the original EOF section from source line 44
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Group/Measure.lean -/
