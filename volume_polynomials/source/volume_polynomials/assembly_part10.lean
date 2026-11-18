module

public import volume_polynomials.assembly_part09

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

/- BEGIN SOURCE: VolumePolynomials/RationalInterpolation.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# Explicit rational extraction of every coefficient

Substitution `tᵢ = z^((d+2)^i)` sends distinct degree-`d` monomials to distinct
powers of `z`, all below `(d+2)^n`. Ordinary univariate Lagrange interpolation
at the positive integers then extracts every coefficient by a fixed rational
linear combination of volume evaluations. The larger sampling set avoids
any unproved multivariate interpolation theorem.
-/

open Finset Polynomial
open scoped BigOperators

namespace VolumePolynomials

def coefficientCode {n d : ℕ} (α : MultiIndex n d) : ℕ :=
  Nat.ofDigits (d + 2) (List.ofFn fun i => (α.1 i : ℕ))

def interpolationSize (n d : ℕ) : ℕ := (d + 2) ^ n

theorem coefficientCode_lt {n d : ℕ} (α : MultiIndex n d) :
    coefficientCode α < interpolationSize n d := by
  first
  | have h := Nat.ofDigits_lt_base_pow_length (b := d + 2) (by omega)
      (l := List.ofFn fun i => (α.1 i : ℕ)) (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (α.1 i).isLt.trans (by omega))
    simpa only [coefficientCode, interpolationSize, List.length_ofFn] using h

theorem coefficientCode_injective (n d : ℕ) :
    Function.Injective (coefficientCode (n := n) (d := d)) := by
  first
  | intro α β h
    have hlist := Nat.ofDigits_inj_of_len_eq (b := d + 2) (by omega)
      (by simp : (List.ofFn fun i => (α.1 i : ℕ)).length =
        (List.ofFn fun i => (β.1 i : ℕ)).length)
      (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (α.1 i).isLt.trans (by omega))
      (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (β.1 i).isLt.trans (by omega)) h
    have hfun := List.ofFn_injective hlist
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hfun i)

theorem coefficientCode_eq_sum {n d : ℕ} (α : MultiIndex n d) :
    coefficientCode α = ∑ i : Fin n, (α.1 i : ℕ) * (d + 2) ^ (i : ℕ) := by
  first
  | have hmap : (List.ofFn fun i => (α.1 i : ℕ)).mapIdx
        (fun i a => a * (d + 2) ^ i) =
        List.ofFn (fun i : Fin n => (α.1 i : ℕ) * (d + 2) ^ (i : ℕ)) := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp
    rw [coefficientCode, Nat.ofDigits_eq_sum_mapIdx, hmap, List.sum_ofFn]

def interpolationNode {n d : ℕ} (j : Fin (interpolationSize n d)) : ℚ :=
  (j.val : ℚ) + 1

def interpolationWeight {n d : ℕ} (j : Fin (interpolationSize n d)) (i : Fin n) : ℚ :=
  interpolationNode j ^ ((d + 2) ^ (i : ℕ))

/-- Coefficients of the product of the normalized linear factors
`(X-a)/(x-a)`. This recursion uses only executable rational arithmetic. -/
def lagrangeCoefficient (x : ℚ) : List ℚ → ℕ → ℚ
  | [], m => if m = 0 then 1 else 0
  | a :: l, 0 => (x - a)⁻¹ * (-(a * lagrangeCoefficient x l 0))
  | a :: l, m + 1 =>
      (x - a)⁻¹ * (lagrangeCoefficient x l m - a * lagrangeCoefficient x l (m + 1))

theorem lagrangeCoefficient_eq (x : ℚ) (l : List ℚ) (m : ℕ) :
    lagrangeCoefficient x l m =
      ((l.map (Lagrange.basisDivisor x)).prod).coeff m := by
  first
  | induction l generalizing m with
    | nil => simp [lagrangeCoefficient, Polynomial.coeff_one]
    | cons a l ih =>
        cases m with
        | zero =>
            simp only [lagrangeCoefficient, List.map_cons, List.prod_cons,
              Lagrange.basisDivisor, mul_assoc, sub_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, zero_sub, ih]
        | succ m =>
            simp only [lagrangeCoefficient, List.map_cons, List.prod_cons,
              Lagrange.basisDivisor, mul_assoc, sub_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_sub, Polynomial.coeff_X_mul, ih]

/-- Every arithmetic entry is rational, with a finite, executable formula.
The definition does not call Mathlib's noncomputable polynomial operations. -/
def coefficientExtractionWeight {n d : ℕ} (α : MultiIndex n d)
    (j : Fin (interpolationSize n d)) : ℚ :=
  lagrangeCoefficient (interpolationNode j)
    (((List.finRange (interpolationSize n d)).filter (fun k => decide (k ≠ j))).map
      interpolationNode) (coefficientCode α)

/-- The executable recursion computes the exact Lagrange coefficient. -/
theorem coefficientExtractionWeight_eq {n d : ℕ} (α : MultiIndex n d)
    (j : Fin (interpolationSize n d)) :
    coefficientExtractionWeight α j =
      (Lagrange.basis Finset.univ (interpolationNode (n := n) (d := d)) j).coeff
        (coefficientCode α) := by
  first
  | let l := (List.finRange (interpolationSize n d)).filter (fun k => decide (k ≠ j))
    have hl : l.Nodup := (List.nodup_finRange _).filter _
    have hs : l.toFinset = (Finset.univ : Finset (Fin (interpolationSize n d))).erase j := by
      ext k
      simp [l, and_comm]
    unfold coefficientExtractionWeight
    rw [lagrangeCoefficient_eq]
    simp only [List.map_map]
    rw [← List.prod_toFinset _ hl, hs]
    rfl

theorem interpolationNode_pos {n d : ℕ} (j : Fin (interpolationSize n d)) :
    0 < interpolationNode j := by
  first
  | dsimp [interpolationNode]
    positivity

theorem interpolationWeight_pos {n d : ℕ} (j : Fin (interpolationSize n d)) (i : Fin n) :
    0 < interpolationWeight j i := pow_pos (interpolationNode_pos j) _

noncomputable def codedPolynomial {n d : ℕ} (c : Coefficients n d) : Polynomial ℝ :=
  ∑ α, Polynomial.monomial (coefficientCode α) (c α)

theorem codedPolynomial_coeff {n d : ℕ} (c : Coefficients n d) (α : MultiIndex n d) :
    (codedPolynomial c).coeff (coefficientCode α) = c α := by
  first
  | classical
    simp only [codedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      (coefficientCode_injective n d).eq_iff]
    simp

theorem codedPolynomial_degree_lt {n d : ℕ} (c : Coefficients n d) :
    (codedPolynomial c).degree < interpolationSize n d := by
  first
  | classical
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [codedPolynomial, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro α _
    exact Polynomial.coeff_monomial_of_ne (c α)
      (ne_of_gt ((coefficientCode_lt α).trans_le hm))

theorem codedPolynomial_eval {n d : ℕ} (c : Coefficients n d) (z : ℝ) :
    (codedPolynomial c).eval z = evaluate c (fun i => z ^ ((d + 2) ^ (i : ℕ))) := by
  first
  | classical
    simp only [codedPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, evaluate]
    apply Finset.sum_congr rfl
    intro α _
    rw [coefficientCode_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, Nat.mul_comm]

theorem map_rational_lagrange_basis {n d : ℕ}
    (j : Fin (interpolationSize n d)) :
    Polynomial.map (algebraMap ℚ ℝ)
      (Lagrange.basis Finset.univ (interpolationNode (n := n) (d := d)) j) =
      Lagrange.basis Finset.univ (fun k : Fin (interpolationSize n d) =>
        (interpolationNode k : ℝ)) j := by
  first
  | classical
    simp [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod,
      Polynomial.map_mul, Polynomial.map_sub]

/-- Exact coefficient recovery from a fixed finite list of strictly positive
integer weight vectors. There is no coefficient omission or bounded parameter
restriction in this statement. -/
theorem coefficient_eq_rational_samples {n d : ℕ} (c : Coefficients n d)
    (α : MultiIndex n d) :
    c α = ∑ j : Fin (interpolationSize n d),
      (coefficientExtractionWeight α j : ℝ) *
        evaluate c (fun i => (interpolationWeight j i : ℝ)) := by
  first
  | classical
    have hnode : Set.InjOn (fun j : Fin (interpolationSize n d) =>
        (interpolationNode j : ℝ))
        (↑(Finset.univ : Finset (Fin (interpolationSize n d))) : Set _) := by
      intro i _ j _ hij
      apply Fin.ext
      have hrat : interpolationNode i = interpolationNode j := Rat.cast_injective hij
      have hval : (i.val : ℚ) = (j.val : ℚ) := add_right_cancel hrat
      exact Nat.cast_injective hval
    have hdeg : (codedPolynomial c).degree <
        (Finset.univ : Finset (Fin (interpolationSize n d))).card := by
      simpa using codedPolynomial_degree_lt c
    have hp := Lagrange.eq_interpolate (f := codedPolynomial c) hnode hdeg
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff (coefficientCode α)) hp
    rw [codedPolynomial_coeff, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at hcoeff
    refine hcoeff.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Polynomial.coeff_C_mul, codedPolynomial_eval]
    have hw : (Lagrange.basis Finset.univ
        (fun k : Fin (interpolationSize n d) => (interpolationNode k : ℝ)) j).coeff
          (coefficientCode α) = (coefficientExtractionWeight α j : ℝ) := by
      rw [← map_rational_lagrange_basis, Polynomial.coeff_map]
      exact congrArg (fun q : ℚ => (q : ℝ)) (coefficientExtractionWeight_eq α j).symm
    rw [hw, mul_comm]
    simp only [interpolationWeight, Rat.cast_pow]

def coefficientExtractionBound (n d : ℕ) : ℚ :=
  ∑ α : MultiIndex n d, ∑ j : Fin (interpolationSize n d),
    |coefficientExtractionWeight α j|

theorem coefficientExtractionBound_nonneg (n d : ℕ) :
    0 ≤ coefficientExtractionBound n d :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- The interpolation formula supplies an explicit rational modulus for
coefficient error from uniformly bounded sample-evaluation errors. -/
theorem abs_coefficient_sub_le_of_samples {n d : ℕ} (c c' : Coefficients n d)
    {η : ℝ} (hη : 0 ≤ η)
    (hsample : ∀ j : Fin (interpolationSize n d),
      |evaluate c (fun i => (interpolationWeight j i : ℝ)) -
        evaluate c' (fun i => (interpolationWeight j i : ℝ))| ≤ η)
    (α : MultiIndex n d) :
    |c α - c' α| ≤ (coefficientExtractionBound n d : ℝ) * η := by
  first
  | classical
    rw [coefficient_eq_rational_samples c α, coefficient_eq_rational_samples c' α,
      ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)| * η := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hsample j) (abs_nonneg _)
      _ = (∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)|) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ (coefficientExtractionBound n d : ℝ) * η := by
        apply mul_le_mul_of_nonneg_right _ hη
        simp only [coefficientExtractionBound, Rat.cast_sum, Rat.cast_abs]
        exact Finset.single_le_sum
          (fun β _ => Finset.sum_nonneg (fun j _ =>
            abs_nonneg (coefficientExtractionWeight β j : ℝ)))
          (Finset.mem_univ α)

end VolumePolynomials
end -- closes the original EOF section from source line 12
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalInterpolation.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalHullSampling.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Executable samples for rational vertex lists

All lists used in the algorithm have explicit order. In particular no
noncomputable conversion from a finset to a list is used. Actual finite
Minkowski sums are represented by all finite choices of one listed vertex
from each summand; their volume samples are computed with the certified
box-counting search.
-/

open Set Finset MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.RationalHulls

abbrev RationalPoint (d : ℕ) := Fin d → ℚ

def realPoint {d : ℕ} (x : RationalPoint d) : Space d := fun i => (x i : ℝ)

theorem realPoint_zero (d : ℕ) : realPoint (0 : RationalPoint d) = (0 : Space d) := by
  first
  | funext i
    change ((0 : ℚ) : ℝ) = 0
    exact Rat.cast_zero

def vertices {d : ℕ} (L : List (RationalPoint d)) : Set (Space d) :=
  realPoint '' {x | x ∈ L}

def hull {d : ℕ} (L : List (RationalPoint d)) : Set (Space d) := convexHull ℝ (vertices L)

theorem vertices_finite {d : ℕ} (L : List (RationalPoint d)) : (vertices L).Finite := by
  first
  | simpa only [vertices, List.coe_toFinset] using L.toFinset.finite_toSet.image realPoint

theorem vertices_eq_range {d : ℕ} (L : List (RationalPoint d)) :
    vertices L = range (fun i : Fin L.length => realPoint (L.get i)) := by
  first
  | ext x
    simp only [vertices, Set.mem_image, Set.mem_setOf_eq, List.mem_iff_get, Set.mem_range]
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨L.get i, ⟨i, rfl⟩, rfl⟩

noncomputable def body {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L) : Body d where
  carrier := hull L
  convex' := convex_convexHull ℝ _
  isCompact' := (vertices_finite L).isCompact_convexHull ℝ
  nonempty' := ⟨(0 : Space d),
    subset_convexHull ℝ _ ⟨(0 : RationalPoint d), hL, realPoint_zero d⟩⟩

theorem zero_mem_body {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L) :
    (0 : Space d) ∈ body L hL :=
  subset_convexHull ℝ _ ⟨(0 : RationalPoint d), hL, realPoint_zero d⟩

theorem body_subset_box {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L)
    (R : ℚ) (hbox : ∀ v ∈ L, ∀ i, |v i| ≤ R) :
    (body L hL : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | apply convexHull_min _ (convex_Icc _ _)
    rintro x ⟨v, hv, rfl⟩
    constructor
    · intro i
      have h := (abs_le.mp (hbox v hv i)).1
      change -(R : ℝ) ≤ (v i : ℝ)
      exact_mod_cast h
    · intro i
      have h := (abs_le.mp (hbox v hv i)).2
      change (v i : ℝ) ≤ (R : ℝ)
      exact_mod_cast h

def radiusBound {d : ℕ} (L : List (RationalPoint d)) : ℚ :=
  (L.map (fun v => ∑ i, |v i|)).sum

def integerRadius {d : ℕ} (L : List (RationalPoint d)) : ℕ := ⌈radiusBound L⌉₊

theorem abs_le_radiusBound {d : ℕ} (L : List (RationalPoint d))
    {v : RationalPoint d} (hv : v ∈ L) (i : Fin d) : |v i| ≤ radiusBound L := by
  first
  | apply (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)).trans
    exact List.single_le_sum (by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
      exact Finset.sum_nonneg (fun j _ => abs_nonneg (w j))) _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem hull_subset_ambient {d : ℕ} (L : List (RationalPoint d)) :
    hull L ⊆ RationalElimination.ambientBox d (integerRadius L) := by
  first
  | have hclosed : hull L ⊆ Icc (fun _ : Fin d => -(integerRadius L : ℝ))
        (fun _ => (integerRadius L : ℝ)) := by
      apply convexHull_min _ (convex_Icc _ _)
      rintro x ⟨v, hv, rfl⟩
      have hcoord (i : Fin d) : |realPoint v i| ≤ (integerRadius L : ℝ) := by
        have h := (abs_le_radiusBound L hv i).trans (Nat.le_ceil (radiusBound L))
        change |(v i : ℝ)| ≤ (integerRadius L : ℝ)
        rw [← Rat.cast_abs]
        exact_mod_cast h
      exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
    intro x hx i
    have h := hclosed hx
    exact ⟨by change -((integerRadius L : ℝ) + 1) < x i; linarith [h.1 i],
      by change x i ≤ (integerRadius L : ℝ) + 1; linarith [h.2 i]⟩

theorem halfspaces_solution_eq_hull {d : ℕ} (L : List (RationalPoint d)) :
    RationalElimination.solutionSet (RationalElimination.hullHalfspaces L.get) = hull L := by
  first
  | ext x
    rw [RationalElimination.solutionSet, Set.mem_setOf_eq,
      RationalElimination.hullHalfspaces_correct, hull, vertices_eq_range]
    rfl

/-- The radius and every halfspace are computed from the given finite list. -/
def approximateHullVolume {d : ℕ} (L : List (RationalPoint d)) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  RationalElimination.approximateVolume (RationalElimination.hullHalfspaces L.get)
    (integerRadius L) (by rw [halfspaces_solution_eq_hull]; exact hull_subset_ambient L) ε hε

theorem approximateHullVolume_correct {d : ℕ} (L : List (RationalPoint d))
    (ε : ℚ) (hε : 0 < ε) :
    |(approximateHullVolume L ε hε : ℝ) - volume.real (hull L)| < (ε : ℝ) := by
  first
  | unfold approximateHullVolume
    simpa only [halfspaces_solution_eq_hull] using
      RationalElimination.approximateVolume_correct
        (RationalElimination.hullHalfspaces L.get) (integerRadius L)
        (by rw [halfspaces_solution_eq_hull]; exact hull_subset_ambient L) ε hε

/-- Ordered finite Cartesian products. -/
def selections {α : Type*} : {n : ℕ} → (Fin n → List α) → List (Fin n → α)
  | 0, _ => [Fin.elim0]
  | n + 1, L => (L 0).flatMap (fun a => (selections (Fin.tail L)).map (Fin.cons a))

theorem mem_selections {α : Type*} {n : ℕ} (L : Fin n → List α) (f : Fin n → α) :
    f ∈ selections L ↔ ∀ i, f i ∈ L i := by
  first
  | induction n with
    | zero =>
        simp only [selections, List.mem_singleton]
        constructor
        · intro _ i
          exact Fin.elim0 i
        · intro _
          funext i
          exact Fin.elim0 i
    | succ n ih =>
        simp only [selections, List.mem_flatMap, List.mem_map]
        constructor
        · rintro ⟨a, ha, g, hg, rfl⟩ i
          cases i using Fin.cases with
          | zero => exact ha
          | succ i => exact (ih (Fin.tail L) g).mp hg i
        · intro h
          exact ⟨f 0, h 0, Fin.tail f, (ih (Fin.tail L) (Fin.tail f)).mpr (fun i => h i.succ),
            Fin.cons_self_tail f⟩

def weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) : List (RationalPoint d) :=
  (selections L).map (fun f => ∑ i, t i • f i)

theorem mem_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) (v : RationalPoint d) :
    v ∈ weightedVertices L t ↔ ∃ f : Fin n → RationalPoint d,
      (∀ i, f i ∈ L i) ∧ ∑ i, t i • f i = v := by
  first
  | simp only [weightedVertices, List.mem_map, mem_selections]

theorem zero_mem_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) (t : Fin n → ℚ) : 0 ∈ weightedVertices L t := by
  first
  | exact Iff.mpr (mem_weightedVertices L t 0) ⟨fun _ => 0, hL, by simp⟩

theorem vertices_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) :
    vertices (weightedVertices L t) = ∑ i, (t i : ℝ) • vertices (L i) := by
  first
  | classical
    ext x
    rw [Set.mem_fintype_sum]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨f, hf, rfl⟩ := Iff.mp (mem_weightedVertices L t v) hv
      refine ⟨fun i => (t i : ℝ) • realPoint (f i), ?_, ?_⟩
      · intro i
        exact ⟨realPoint (f i), ⟨f i, hf i, rfl⟩, rfl⟩
      · ext j
        simp [realPoint]
    · rintro ⟨a, ha, rfl⟩
      have hpoints : ∀ i, ∃ q ∈ L i, (t i : ℝ) • realPoint q = a i := by
        intro i
        obtain ⟨y, ⟨q, hq, rfl⟩, hqy⟩ := ha i
        exact ⟨q, hq, hqy⟩
      choose q hq hqa using hpoints
      refine ⟨∑ i, t i • q i, Iff.mpr (mem_weightedVertices L t _) ⟨q, hq, rfl⟩, ?_⟩
      rw [show (∑ i, a i) = ∑ i, (t i : ℝ) • realPoint (q i) by simp only [hqa]]
      ext j
      simp [realPoint]

theorem hull_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) :
    hull (weightedVertices L t) = ∑ i, (t i : ℝ) • hull (L i) := by
  first
  | rw [hull, vertices_weightedVertices, convexHull_sum]
    simp only [convexHull_smul, hull]

theorem weightedSum_body {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) (t : Fin n → ℚ) :
    (weightedSum (fun i => body (L i) (hL i)) (fun i => (t i : ℝ)) : Set (Space d)) =
      hull (weightedVertices L t) := by
  first
  | rw [weightedSum, coe_sum_body, hull_weightedVertices]
    rfl

/-- Pure rational approximate coefficient vector recovered from all prescribed
positive rational samples. -/
def approximateCoefficients {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (ε : ℚ) (hε : 0 < ε) : MultiIndex n d → ℚ :=
  fun α => ∑ j : Fin (interpolationSize n d), coefficientExtractionWeight α j *
    approximateHullVolume (weightedVertices L (interpolationWeight j)) ε hε

theorem approximateCoefficients_correct {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) {c : Coefficients n d}
    (hc : Realizes (fun i => body (L i) (hL i)) c) (ε : ℚ) (hε : 0 < ε)
    (α : MultiIndex n d) :
    |(approximateCoefficients L ε hε α : ℝ) - c α| ≤
      (coefficientExtractionBound n d : ℝ) * (ε : ℝ) := by
  first
  | rw [coefficient_eq_rational_samples c α]
    simp only [approximateCoefficients, Rat.cast_sum, Rat.cast_mul, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)| * (ε : ℝ) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul, hc _ (fun i => by exact_mod_cast (interpolationWeight_pos j i).le)]
        change |(coefficientExtractionWeight α j : ℝ)| *
          |(approximateHullVolume _ ε hε : ℝ) - volume.real
            (weightedSum (fun i => body (L i) (hL i))
              (fun i => (interpolationWeight j i : ℝ)) : Set (Space d))| ≤ _
        rw [weightedSum_body]
        exact mul_le_mul_of_nonneg_left (approximateHullVolume_correct _ ε hε).le (abs_nonneg _)
      _ = (∑ j : Fin (interpolationSize n d), |(coefficientExtractionWeight α j : ℝ)|) * (ε : ℝ) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (coefficientExtractionBound n d : ℝ) * (ε : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast hε.le)
        simp only [coefficientExtractionBound, Rat.cast_sum, Rat.cast_abs]
        exact Finset.single_le_sum
          (fun β _ => Finset.sum_nonneg (fun j _ => abs_nonneg (coefficientExtractionWeight β j : ℝ)))
          (Finset.mem_univ α)

end VolumePolynomials.RationalHulls
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalHullSampling.lean -/

/- BEGIN SOURCE: VolumePolynomials/FinitePathSelection.lean -/
section


@[expose] public section

/-!
# Convergence of the whole least-path output sequence

This is the finite-tree selection argument in Proposition 8.4. Each `A n`
is the finite linearly ordered set of accepted paths of height `n`; `π`
is restriction to a prefix. Prefix restriction preserves lexicographic order.
The terminal metric data are required to satisfy the proved tail estimate.
No compatible branch is assumed or chosen, and no convergence rate for the
sequence of least-path terminal states is asserted.
-/

open scoped Topology
open Filter

namespace VolumePolynomials.FinitePathSelection

/-- Any decreasing sequence of finite sets eventually stops changing. -/
theorem antitone_finsets_stabilize {α : Type*} (S : ℕ → Finset α) (hS : Antitone S) :
    ∃ N, ∀ n, N ≤ n → S n = S N := by
  classical
  let P : ℕ → Prop := fun k => ∃ n, (S n).card = k
  have hex : ∃ k, P k := ⟨(S 0).card, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  refine ⟨N, fun n hn => ?_⟩
  apply Finset.eq_of_subset_of_card_le (hS hn)
  rw [hN]
  exact Nat.find_min' hex ⟨n, rfl⟩

/-- Telescoping consecutive-path bounds give the exact finite tail bound. -/
theorem prefix_distance_le_sub
    {A : ℕ → Type*} {X : Type*} [PseudoMetricSpace X]
    (π : {i j : ℕ} → i ≤ j → A j → A i)
    (hrefl : ∀ n (a : A n), π (le_refl n) a = a)
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hstep : ∀ n (a : A (n + 1)),
      dist (point (n + 1) a) (point n (π (Nat.le_succ n) a)) ≤
        radius n - radius (n + 1))
    {i j : ℕ} (h : i ≤ j) :
    ∀ a : A j, dist (point j a) (point i (π h a)) ≤ radius i - radius j := by
  induction j, h using Nat.le_induction with
  | base =>
      intro a
      simp [hrefl]
  | succ j hj ih =>
      intro a
      have hs := hstep j a
      have hp := ih (π (Nat.le_succ j) a)
      have ht := dist_triangle (point (j + 1) a)
        (point j (π (Nat.le_succ j) a))
        (point i (π hj (π (Nat.le_succ j) a)))
      rw [htrans] at ht hp
      linarith

/-- A nonnegative tail radius bounds the distance from a terminal state to every prefix. -/
theorem prefix_distance_le_radius
    {A : ℕ → Type*} {X : Type*} [PseudoMetricSpace X]
    (π : {i j : ℕ} → i ≤ j → A j → A i)
    (hrefl : ∀ n (a : A n), π (le_refl n) a = a)
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ radius n)
    (hstep : ∀ n (a : A (n + 1)),
      dist (point (n + 1) a) (point n (π (Nat.le_succ n) a)) ≤
        radius n - radius (n + 1))
    {i j : ℕ} (h : i ≤ j) (a : A j) :
    dist (point j a) (point i (π h a)) ≤ radius i := by
  have hb := prefix_distance_le_sub π hrefl htrans point radius hstep h a
  linarith [hr j]

section FiniteLevels

variable {A : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, LinearOrder (A n)]
variable [∀ n, Nonempty (A n)]

/-- The actual least accepted path at the indicated height. -/
def leastPath (n : ℕ) : A n := Finset.univ.min' Finset.univ_nonempty

theorem leastPath_le (n : ℕ) (a : A n) : leastPath n ≤ a :=
  Finset.min'_le _ _ (Finset.mem_univ a)

variable (π : {i j : ℕ} → i ≤ j → A j → A i)

/-- Possible prefixes at depth `j` of paths of height at least `n`. -/
def extendible (j n : ℕ) : Finset (A j) :=
  Finset.univ.image (π (Nat.le_max_left j n))

/-- Prefix of the chosen least path, using `max j n` to avoid partial definitions. -/
def chosenPrefix (j n : ℕ) : A j :=
  π (Nat.le_max_left j n) (leastPath (max j n))

theorem chosenPrefix_eq {j n : ℕ} (h : j ≤ n) :
    chosenPrefix π j n = π h (leastPath n) := by
  have heq : ∀ k (hk : j ≤ k), k = n →
      π hk (leastPath k) = π h (leastPath n) := by
    intro k hk he
    subst k
    rfl
  exact heq (max j n) (Nat.le_max_left j n) (max_eq_right h)

theorem chosenPrefix_mem (j n : ℕ) : chosenPrefix π j n ∈ extendible π j n := by
  apply Finset.mem_image.mpr
  exact ⟨leastPath (max j n), Finset.mem_univ _, rfl⟩

theorem chosenPrefix_le
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h)) (j n : ℕ)
    {a : A j} (ha : a ∈ extendible π j n) : chosenPrefix π j n ≤ a := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
  exact hmono _ (leastPath_le _ b)

omit [∀ n, Nonempty (A n)] in
theorem extendible_antitone
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a) (j : ℕ) :
    Antitone (extendible π j) := by
  intro n m hnm a ha
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ha
  apply Finset.mem_image.mpr
  refine ⟨π (max_le_max_left j hnm) b, Finset.mem_univ _, ?_⟩
  exact (htrans (Nat.le_max_left j n) (max_le_max_left j hnm) b).trans hb

/-- At every fixed depth, prefixes of the least paths eventually stabilize. -/
theorem chosenPrefix_stabilizes
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h)) (j : ℕ) :
    ∃ N, ∀ n, N ≤ n → chosenPrefix π j n = chosenPrefix π j N := by
  obtain ⟨N, hN⟩ := antitone_finsets_stabilize (extendible π j)
    (extendible_antitone π htrans j)
  refine ⟨N, fun n hn => le_antisymm ?_ ?_⟩
  · apply chosenPrefix_le π hmono
    rw [hN n hn]
    exact chosenPrefix_mem π j N
  · apply chosenPrefix_le π hmono
    rw [← hN n hn]
    exact chosenPrefix_mem π j n

variable {X : Type*} [PseudoMetricSpace X]

/--
The entire output sequence of least-path terminal states is Cauchy. The proof
uses only eventual stabilization of fixed-depth prefixes, so it does not
assume that the least paths at successive heights are compatible.
-/
theorem terminal_cauchy
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i) :
    CauchySeq (fun n => point n (leastPath n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (hradius.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨N, hN⟩ := chosenPrefix_stabilizes π htrans hmono j
  refine ⟨max j N, fun n hn m hm => ?_⟩
  have hjn : j ≤ n := (le_max_left _ _).trans hn
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  have hjm : j ≤ m := (le_max_left _ _).trans hm
  have hNm : N ≤ m := (le_max_right _ _).trans hm
  have hpn : π hjn (leastPath n) = chosenPrefix π j N := by
    exact (chosenPrefix_eq π hjn).symm.trans (hN n hNn)
  have hpm : π hjm (leastPath m) = chosenPrefix π j N := by
    exact (chosenPrefix_eq π hjm).symm.trans (hN m hNm)
  have hdn := hnear hjn (leastPath n)
  have hdm := hnear hjm (leastPath m)
  rw [hpn] at hdn
  rw [hpm] at hdm
  have htri := dist_triangle_right (point n (leastPath n)) (point m (leastPath m))
    (point j (chosenPrefix π j N))
  linarith

/-- Completeness produces a limit for the entire least-path terminal sequence. -/
theorem terminal_converges [CompleteSpace X]
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i) :
    ∃ x, Tendsto (fun n => point n (leastPath n)) atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete (terminal_cauchy π htrans hmono point radius hradius hnear)

/-- A continuous coefficient map of the limit is the exact target coefficient vector. -/
theorem terminal_limit_realizes [CompleteSpace X]
    {Y : Type*} [MetricSpace Y]
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius error : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (herror : Tendsto error atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i)
    (Φ : X → Y) (hΦ : Continuous Φ) (target : Y)
    (hcoeff : ∀ n (a : A n), dist (Φ (point n a)) target ≤ error n) :
    ∃ x, Tendsto (fun n => point n (leastPath n)) atTop (𝓝 x) ∧ Φ x = target := by
  obtain ⟨x, hx⟩ := terminal_converges π htrans hmono point radius hradius hnear
  refine ⟨x, hx, ?_⟩
  have hlim : Tendsto (fun n => Φ (point n (leastPath n))) atTop (𝓝 target) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => hcoeff n (leastPath n)) herror
  exact tendsto_nhds_unique ((hΦ.tendsto x).comp hx) hlim

end FiniteLevels

/--
If no exact realization exists, some finite height has no accepted path.
Thus enumerating and testing successive finite path sets eventually rejects.
-/
theorem exists_empty_level_of_not_realizable
    {A : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, LinearOrder (A n)]
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {Y : Type*} [MetricSpace Y]
    (π : {i j : ℕ} → i ≤ j → A j → A i)
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius error : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (herror : Tendsto error atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i)
    (Φ : X → Y) (hΦ : Continuous Φ) (target : Y)
    (hcoeff : ∀ n (a : A n), dist (Φ (point n a)) target ≤ error n)
    (hno : target ∉ Set.range Φ) :
    ∃ n, IsEmpty (A n) := by
  classical
  by_contra h
  have hne : ∀ n, Nonempty (A n) := by
    intro n
    by_contra hn
    exact h ⟨n, ⟨fun a => hn ⟨a⟩⟩⟩
  let : ∀ n, Nonempty (A n) := hne
  obtain ⟨x, _, hx⟩ := terminal_limit_realizes π htrans hmono point radius error
    hradius herror hnear Φ hΦ target hcoeff
  exact hno ⟨x, hx⟩

end VolumePolynomials.FinitePathSelection
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FinitePathSelection.lean -/

/- BEGIN SOURCE: VolumePolynomials/ComputableFinitePaths.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Finite executable path sets and lexicographic output

This instantiates the checked finite-prefix stabilization argument for actual
finite lists of states and decidable edges. It computes every finite path set,
its least path, and its terminal state. Prefix closure and monotonicity are
proved from the literal list operations.
-/

open Filter
open scoped Topology

namespace VolumePolynomials.ComputableFinitePaths

variable {α : Type*} [LinearOrder α] [Inhabited α]

def Valid (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    (h : ℕ) (p : List α) : Prop :=
  p.length = h + 1 ∧
    (∀ i : Fin (h + 1), p.getD i.val default ∈ states i.val) ∧
    ∀ i : Fin h, edge i.val (p.getD i.val default) (p.getD (i.val + 1) default)

instance validDecidable (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : List α) : Decidable (Valid states edge h p) := by
  first
  | unfold Valid
    infer_instance

def paths (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) : Finset (List α) :=
  ((RationalHulls.selections (fun i : Fin (h + 1) => states i.val)).map List.ofFn).toFinset.filter
    (Valid states edge h)

theorem getD_take {p : List α} {j i : ℕ} (hi : i < j) :
    (p.take j).getD i default = p.getD i default := by
  first
  | simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem ofFn_getD (p : List α) (h : ℕ) (hp : p.length = h) :
    List.ofFn (fun i : Fin h => p.getD i.val default) = p := by
  first
  | apply List.ext_getElem
    · simpa using hp.symm
    · intro i hi hi'
      simp only [List.getElem_ofFn, List.getD_eq_getElem p default hi']

theorem mem_paths (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : List α) :
    p ∈ paths states edge h ↔ Valid states edge h p := by
  first
  | constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr (List.mem_map.mpr ?_), hp⟩
      exact ⟨fun i : Fin (h + 1) => p.getD i.val default,
        Iff.mpr (RationalHulls.mem_selections _ _) hp.2.1, ofFn_getD p (h + 1) hp.1⟩

theorem valid_take (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    {i j : ℕ} (hij : i ≤ j) {p : List α} (hp : Valid states edge j p) :
    Valid states edge i (p.take (i + 1)) := by
  first
  | refine ⟨by simp [hp.1, Nat.min_eq_left (Nat.succ_le_succ hij)], ?_, ?_⟩
    · intro k
      rw [getD_take k.isLt]
      exact hp.2.1 ⟨k.val, k.isLt.trans_le (Nat.succ_le_succ hij)⟩
    · intro k
      rw [getD_take (by omega : k.val < i + 1), getD_take (by omega : k.val + 1 < i + 1)]
      exact hp.2.2 ⟨k.val, k.isLt.trans_le hij⟩

theorem take_monotone (k : ℕ) : Monotone (List.take k : List α → List α) := by
  first
  | intro p q hpq
    rcases lt_or_eq_of_le hpq with h | rfl
    · change List.Lex (· < ·) p q at h
      clear hpq
      induction h generalizing k with
      | nil =>
          cases k with
          | zero => exact le_rfl
          | succ k =>
              apply le_of_lt
              exact List.Lex.nil
      | cons h ih =>
          cases k with
          | zero => exact le_rfl
          | succ k => exact List.cons_le_cons _ (ih k)
      | rel h =>
          cases k with
          | zero => exact le_rfl
          | succ k =>
              apply le_of_lt
              exact List.Lex.rel h
    · exact le_rfl

abbrev Path (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) :=
  {p : List α // p ∈ paths states edge h}

def pathPrefix (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j : ℕ} (hij : i ≤ j)
    (p : Path states edge j) : Path states edge i :=
  ⟨p.val.take (i + 1), Iff.mpr (mem_paths states edge i _)
    (valid_take states edge hij (Iff.mp (mem_paths states edge j _) p.property))⟩

theorem prefix_refl (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge h) :
    pathPrefix states edge (le_refl h) p = p := by
  first
  | apply Subtype.ext
    exact List.take_of_length_le (Iff.mp (mem_paths states edge h p.val) p.property).1.le

theorem prefix_trans (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (p : Path states edge k) :
    pathPrefix states edge hij (pathPrefix states edge hjk p) =
      pathPrefix states edge (hij.trans hjk) p := by
  first
  | apply Subtype.ext
    simp only [pathPrefix, List.take_take, Nat.min_eq_left (Nat.succ_le_succ hij)]

theorem prefix_monotone (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j : ℕ} (hij : i ≤ j) :
    Monotone (pathPrefix states edge hij) := fun _ _ h => take_monotone (i + 1) h

def terminal (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge h) : α :=
  p.val.getD h default

theorem terminal_mem (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge h) :
    terminal states edge h p ∈ states h :=
  (Iff.mp (mem_paths states edge h p.val) p.property).2.1 ⟨h, Nat.lt_succ_self h⟩

theorem terminal_prefix (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j : ℕ} (hij : i ≤ j) (p : Path states edge j) :
    terminal states edge i (pathPrefix states edge hij p) = p.val.getD i default :=
  getD_take (Nat.lt_succ_self i)

theorem terminal_edge (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge (h + 1)) :
    edge h (terminal states edge h (pathPrefix states edge (Nat.le_succ h) p))
      (terminal states edge (h + 1) p) := by
  first
  | rw [terminal_prefix]
    exact (Iff.mp (mem_paths states edge (h + 1) p.val) p.property).2.2 ⟨h, Nat.lt_succ_self h⟩

/-- The finite algorithm returns `none` exactly at an empty height. -/
def output (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) : Option α :=
  if hp : (paths states edge h).Nonempty then
    some (((paths states edge h).min' hp).getD h default)
  else none

theorem output_eq_none_iff (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) :
    output states edge h = none ↔ IsEmpty (Path states edge h) := by
  first
  | simp only [output]
    split_ifs with hp
    · simp only [Option.some_ne_none, false_iff]
      intro hi
      obtain ⟨p, hp⟩ := hp
      exact hi.false ⟨p, hp⟩
    · simp only [true_iff]
      exact ⟨fun p => hp ⟨p.val, p.property⟩⟩

theorem output_eq_least_terminal (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] [∀ h, Nonempty (Path states edge h)] (h : ℕ) :
    output states edge h = some (terminal states edge h
      (FinitePathSelection.leastPath (A := Path states edge) h)) := by
  first
  | have hp : (paths states edge h).Nonempty := by
      obtain ⟨p⟩ := (inferInstance : Nonempty (Path states edge h))
      exact ⟨p.val, p.property⟩
    have heq : (paths states edge h).min' hp =
        (FinitePathSelection.leastPath (A := Path states edge) h).val := by
      apply le_antisymm
      · exact Finset.min'_le _ _
          (FinitePathSelection.leastPath (A := Path states edge) h).property
      · exact FinitePathSelection.leastPath_le (A := Path states edge) h
          ⟨(paths states edge h).min' hp, Finset.min'_mem _ _⟩
    simp only [output, dif_pos hp, heq, terminal]

theorem paths_nonempty_of_sequence (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (f : ℕ → α)
    (hf : ∀ j, f j ∈ states j) (he : ∀ j, edge j (f j) (f (j + 1))) (h : ℕ) :
    Nonempty (Path states edge h) := by
  first
  | let p := List.ofFn (fun j : Fin (h + 1) => f j.val)
    have hpget (i : ℕ) (hi : i < h + 1) : p.getD i default = f i := by
      have hip : i < p.length := by simpa only [p, List.length_ofFn] using hi
      simpa only [p, List.getElem_ofFn] using List.getD_eq_getElem p default hip
    refine ⟨⟨p, Iff.mpr (mem_paths states edge h p) ⟨by simp [p], ?_, ?_⟩⟩⟩
    · intro i
      rw [hpget i.val i.isLt]
      exact hf i.val
    · intro i
      rw [hpget i.val (by omega), hpget (i.val + 1) (by omega)]
      exact he i.val

/-- The complete executable least-path sequence converges, provided the
verified edge radii and coefficient errors tend to zero. -/
theorem output_converges
    (states : ℕ → List α) (edge : ℕ → α → α → Prop) [∀ i, DecidableRel (edge i)]
    [∀ h, Nonempty (Path states edge h)]
    {X Y : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Y]
    (point : α → X) (Φ : X → Y) (hΦ : Continuous Φ) (target : Y)
    (radius error : ℕ → ℝ) (hr : ∀ j, 0 ≤ radius j)
    (hr0 : Tendsto radius atTop (𝓝 0)) (he0 : Tendsto error atTop (𝓝 0))
    (hedge : ∀ j, ∀ s ∈ states j, ∀ t ∈ states (j + 1), edge j s t →
      dist (point t) (point s) ≤ radius j - radius (j + 1))
    (hcoeff : ∀ j, ∀ s ∈ states j, dist (Φ (point s)) target ≤ error j) :
    ∃ x, Tendsto (fun h => point ((output states edge h).getD default)) atTop (𝓝 x) ∧ Φ x = target := by
  first
  | let π : {i j : ℕ} → i ≤ j → Path states edge j → Path states edge i :=
      @pathPrefix α _ _ states edge _
    let P : (h : ℕ) → Path states edge h → X := fun h p => point (terminal states edge h p)
    have hnear : ∀ {i j} (h : i ≤ j) (p : Path states edge j),
        dist (P j p) (P i (π h p)) ≤ radius i := by
      apply FinitePathSelection.prefix_distance_le_radius π
        (prefix_refl states edge) (prefix_trans states edge) P radius hr
      intro j p
      exact hedge j _ (terminal_mem states edge j (pathPrefix states edge (Nat.le_succ j) p))
        _ (terminal_mem states edge (j + 1) p) (terminal_edge states edge j p)
    obtain ⟨x, hx, hΦx⟩ := FinitePathSelection.terminal_limit_realizes π
      (prefix_trans states edge) (prefix_monotone states edge) P radius error hr0 he0 hnear Φ hΦ target
      (fun h p => hcoeff h _ (terminal_mem states edge h p))
    refine ⟨x, ?_, hΦx⟩
    simpa only [output_eq_least_terminal, Option.getD_some] using hx

end VolumePolynomials.ComputableFinitePaths
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ComputableFinitePaths.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalGridBodies.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Finite rational grids for every bounded convex body

The enumerable objects are ordered sublists of a finite rational grid,
containing the origin. Every compact convex body in the prescribed box and
containing the origin has a listed convex hull at Hausdorff distance at most
`1/(k+1)`. The approximation theorem covers all dimensions and degenerate bodies.
-/

open Set Metric
open scoped BigOperators Pointwise

namespace VolumePolynomials.RationalHulls

def coordinateGrid (R k : ℕ) : List ℚ :=
  List.ofFn (fun i : Fin (2 * R * (k + 1) + 1) =>
    ((i.val : ℚ) - (R : ℚ) * (k + 1)) / (k + 1))

theorem zero_mem_coordinateGrid (R k : ℕ) : (0 : ℚ) ∈ coordinateGrid R k := by
  first
  | apply List.mem_ofFn.mpr
    refine ⟨⟨R * (k + 1),
      Nat.lt_succ_of_le (Nat.mul_le_mul_right (k + 1) (by omega))⟩, ?_⟩
    simp

theorem abs_le_of_mem_coordinateGrid {R k : ℕ} {q : ℚ}
    (hq : q ∈ coordinateGrid R k) : |q| ≤ (R : ℚ) := by
  first
  | obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    have hk : 0 < (k : ℚ) + 1 := by positivity
    have hi : (i.val : ℚ) ≤ 2 * (R : ℚ) * ((k : ℚ) + 1) := by
      exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have hi0 : 0 ≤ (i.val : ℚ) := by positivity
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ hk).mpr
      nlinarith
    · apply (div_le_iff₀ hk).mpr
      nlinarith

theorem exists_coordinateGrid_near {R k : ℕ} {x : ℝ}
    (hx : -(R : ℝ) ≤ x ∧ x ≤ (R : ℝ)) :
    ∃ q ∈ coordinateGrid R k, |x - (q : ℝ)| ≤ 1 / ((k : ℝ) + 1) := by
  first
  | let a : ℝ := ((k : ℝ) + 1) * (x + (R : ℝ))
    have ha : 0 ≤ a := mul_nonneg (by positivity) (by linarith)
    have hb : a ≤ (2 * R * (k + 1) : ℕ) := by
      dsimp [a]
      push_cast
      nlinarith
    let i : Fin (2 * R * (k + 1) + 1) :=
      ⟨⌊a⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hb)⟩
    let q : ℚ := ((i.val : ℚ) - (R : ℚ) * (k + 1)) / (k + 1)
    refine ⟨q, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hlo := Nat.floor_le ha
    have hhi := Nat.lt_floor_add_one a
    have hq : (q : ℝ) * ((k : ℝ) + 1) = (⌊a⌋₊ : ℝ) - (R : ℝ) * ((k : ℝ) + 1) := by
      dsimp [q, i]
      push_cast
      exact div_mul_cancel₀ _ hk.ne'
    have hnonneg : 0 ≤ x - (q : ℝ) := by
      apply (mul_nonneg_iff_of_pos_right hk).mp
      dsimp [a] at hlo
      nlinarith
    rw [abs_of_nonneg hnonneg]
    apply (le_div_iff₀ hk).mpr
    dsimp [a] at hhi
    nlinarith

def vertexGrid (d R k : ℕ) : List (RationalPoint d) :=
  selections (fun _ : Fin d => coordinateGrid R k)

theorem mem_vertexGrid {d R k : ℕ} (v : RationalPoint d) :
    v ∈ vertexGrid d R k ↔ ∀ i, v i ∈ coordinateGrid R k := mem_selections _ _

theorem zero_mem_vertexGrid (d R k : ℕ) : (0 : RationalPoint d) ∈ vertexGrid d R k :=
  Iff.mpr (mem_vertexGrid 0) (fun _ => zero_mem_coordinateGrid R k)

theorem vertexGrid_bounded {d R k : ℕ} {v : RationalPoint d}
    (hv : v ∈ vertexGrid d R k) (i : Fin d) : |v i| ≤ (R : ℚ) :=
  abs_le_of_mem_coordinateGrid (Iff.mp (mem_vertexGrid v) hv i)

theorem exists_vertexGrid_near {d R k : ℕ} {x : Space d}
    (hx : x ∈ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) :
    ∃ v ∈ vertexGrid d R k, dist x (realPoint v) ≤ 1 / ((k : ℝ) + 1) := by
  first
  | choose v hv hdist using fun i => exists_coordinateGrid_near (R := R) (k := k)
      (x := x i) ⟨hx.1 i, hx.2 i⟩
    refine ⟨v, Iff.mpr (mem_vertexGrid v) hv, ?_⟩
    exact (dist_pi_le_iff (by positivity)).mpr
      (fun i => by simpa only [Real.dist_eq, realPoint] using hdist i)

/-- All finite vertex-list candidates. Membership is an executable rational
list predicate, and every candidate is a nonempty actual body. -/
def candidates (d R k : ℕ) : List (List (RationalPoint d)) :=
  (vertexGrid d R k).sublists.filter (fun L => 0 ∈ L)

theorem mem_candidates {d R k : ℕ} (L : List (RationalPoint d)) :
    L ∈ candidates d R k ↔ L.Sublist (vertexGrid d R k) ∧ 0 ∈ L := by
  first
  | simp [candidates, List.mem_sublists]

theorem candidate_bounded {d R k : ℕ} (L : List (RationalPoint d))
    (hL : L ∈ candidates d R k) :
    (body L (Iff.mp (mem_candidates L) hL).2 : Set (Space d)) ⊆
      Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | apply body_subset_box L _ (R : ℚ)
    intro v hv i
    exact vertexGrid_bounded ((Iff.mp (mem_candidates L) hL).1.subset hv) i

/-- Quantitative completeness of the finite rational body enumeration. -/
theorem exists_candidate_near {d R k : ℕ} (K : Body d)
    (h0 : (0 : Space d) ∈ K)
    (hbox : (K : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) :
    ∃ L, ∃ hL : L ∈ candidates d R k,
      dist K (body L (Iff.mp (mem_candidates L) hL).2) ≤ 1 / ((k : ℝ) + 1) := by
  first
  | classical
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 ≤ ε := by positivity
    let P : RationalPoint d → Prop := fun v => ∃ x ∈ K, dist (realPoint v) x ≤ ε
    let L : List (RationalPoint d) := (vertexGrid d R k).filter (fun v => P v)
    have hL0 : (0 : RationalPoint d) ∈ L := by
      apply List.mem_filter.mpr
      refine ⟨zero_mem_vertexGrid d R k, ?_⟩
      simp only [decide_eq_true_eq]
      exact ⟨0, h0, by simpa only [realPoint_zero, dist_self] using hε⟩
    have hL : L ∈ candidates d R k :=
      Iff.mpr (mem_candidates L) ⟨List.filter_sublist, hL0⟩
    let Q := body L hL0
    have hQ : (Q : Set (Space d)) ⊆ (K : Set (Space d)) + closedBall 0 ε := by
      apply convexHull_min _ (K.convex.add (convex_closedBall _ _))
      rintro y ⟨v, hv, rfl⟩
      have hv' : v ∈ vertexGrid d R k ∧ P v := by
        simpa only [L, List.mem_filter, decide_eq_true_eq, Set.mem_setOf_eq] using hv
      obtain ⟨x, hx, hdist⟩ := hv'.2
      refine ⟨x, hx, realPoint v - x, ?_, by abel⟩
      simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hdist
    refine ⟨L, hL, ?_⟩
    change hausdorffDist (K : Set (Space d)) (Q : Set (Space d)) ≤ ε
    apply hausdorffDist_le_of_mem_dist hε
    · intro x hx
      obtain ⟨v, hv, hdist⟩ := exists_vertexGrid_near (hbox hx)
      have hvm : v ∈ L := by
        apply List.mem_filter.mpr
        refine ⟨hv, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨x, hx, by rwa [dist_comm]⟩
      exact ⟨realPoint v, subset_convexHull ℝ _ ⟨v, hvm, rfl⟩, hdist⟩
    · intro y hy
      obtain ⟨x, hx, z, hz, rfl⟩ := hQ hy
      refine ⟨x, hx, ?_⟩
      simpa only [mem_closedBall, dist_eq_norm, sub_zero, add_sub_cancel_left] using hz

/-- All candidate tuples, generated by the same finite-list product algorithm. -/
def candidateTuples (n d R k : ℕ) : List (Fin n → List (RationalPoint d)) :=
  selections (fun _ : Fin n => candidates d R k)

theorem mem_candidateTuples {n d R k : ℕ} (L : Fin n → List (RationalPoint d)) :
    L ∈ candidateTuples n d R k ↔ ∀ i, L i ∈ candidates d R k := mem_selections _ _

end VolumePolynomials.RationalHulls
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalGridBodies.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalHausdorff.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Exact rational Hausdorff tests

A rational point is within sup-norm distance `r` of a rational convex hull
exactly when a finite rational linear system is feasible. Elimination checks
this system exactly. Testing only the listed vertices then suffices for both
Hausdorff inclusions, because convex hulls and norm balls are convex.
-/

open Set Metric
open scoped BigOperators Pointwise

namespace VolumePolynomials.RationalHulls

open RationalElimination

def feasibleTest {d : ℕ} (S : List (Inequality d)) : Prop :=
  ∀ p ∈ eliminateAll S, 0 ≤ p.bound

instance feasibleTest_decidable {d : ℕ} (S : List (Inequality d)) :
    Decidable (feasibleTest S) := by unfold feasibleTest; infer_instance

theorem feasibleTest_correct {d : ℕ} (S : List (Inequality d)) :
    feasibleTest S ↔ ∃ x : Space d, Satisfies S x := by
  first
  | rw [← eliminateAll_correct]
    unfold feasibleTest Satisfies Inequality.Holds Inequality.value
    simp

def coordinateConstraint {d : ℕ} (i : Fin d) (b : ℚ) : Inequality d :=
  ⟨fun j => if j = i then 1 else 0, b⟩

theorem coordinateConstraint_holds {d : ℕ} (i : Fin d) (b : ℚ) (x : Space d) :
    (coordinateConstraint i b).Holds x ↔ x i ≤ (b : ℝ) := by
  first
  | simp [Inequality.Holds, Inequality.value, coordinateConstraint, apply_ite, ite_mul]

def boxConstraints {d : ℕ} (q : RationalPoint d) (r : ℚ) : List (Inequality d) :=
  List.ofFn (fun i => coordinateConstraint i (q i + r)) ++
    List.ofFn (fun i => negative (coordinateConstraint i (q i - r)))

theorem boxConstraints_correct {d : ℕ} (q : RationalPoint d) (r : ℚ) (x : Space d) :
    Satisfies (boxConstraints q r) x ↔ ∀ i, |x i - (q i : ℝ)| ≤ (r : ℝ) := by
  first
  | simp only [boxConstraints, satisfies_append, satisfies_ofFn, coordinateConstraint_holds]
    have hneg : ∀ i, (negative (coordinateConstraint i (q i - r))).Holds x ↔
        (q i : ℝ) - (r : ℝ) ≤ x i := by
      intro i
      simp [Inequality.Holds, negative_value, coordinateConstraint, Inequality.value,
        negative, Rat.cast_sub, apply_ite, ite_mul, add_comm]
    simp only [hneg, Rat.cast_add]
    constructor
    · rintro ⟨hu, hl⟩ i
      exact abs_le.mpr ⟨by linarith [hl i], by linarith [hu i]⟩
    · intro h
      constructor <;> intro i <;> have hi := abs_le.mp (h i) <;> linarith

def pointNearTest {d : ℕ} (L : List (RationalPoint d)) (q : RationalPoint d) (r : ℚ) : Prop :=
  feasibleTest (hullHalfspaces L.get ++ boxConstraints q r)

instance pointNearTest_decidable {d : ℕ} (L : List (RationalPoint d))
    (q : RationalPoint d) (r : ℚ) : Decidable (pointNearTest L q r) := by
  first
  | unfold pointNearTest
    infer_instance

theorem pointNearTest_correct {d : ℕ} (L : List (RationalPoint d))
    (q : RationalPoint d) (r : ℚ) (hr : 0 ≤ r) :
    pointNearTest L q r ↔ ∃ x ∈ hull L, dist (realPoint q) x ≤ (r : ℝ) := by
  first
  | rw [pointNearTest, feasibleTest_correct]
    simp only [satisfies_append, boxConstraints_correct]
    have hh : ∀ x, Satisfies (hullHalfspaces L.get) x ↔ x ∈ hull L := by
      intro x
      change x ∈ solutionSet _ ↔ _
      rw [halfspaces_solution_eq_hull]
    simp only [hh]
    constructor
    · rintro ⟨x, hx, hdist⟩
      refine ⟨x, hx, (dist_pi_le_iff (by exact_mod_cast hr)).mpr ?_⟩
      intro i
      simpa only [realPoint, Real.dist_eq, abs_sub_comm] using hdist i
    · rintro ⟨x, hx, hdist⟩
      refine ⟨x, hx, ?_⟩
      intro i
      simpa only [realPoint, Real.dist_eq, abs_sub_comm] using
        (dist_pi_le_iff (by exact_mod_cast hr)).mp hdist i

def hausdorffTest {d : ℕ} (L M : List (RationalPoint d)) (r : ℚ) : Prop :=
  (∀ p ∈ L, pointNearTest M p r) ∧ ∀ q ∈ M, pointNearTest L q r

instance hausdorffTest_decidable {d : ℕ} (L M : List (RationalPoint d)) (r : ℚ) :
    Decidable (hausdorffTest L M r) := by unfold hausdorffTest; infer_instance

theorem hull_subset_add_closedBall {d : ℕ} (L M : List (RationalPoint d))
    (r : ℚ) (hr : 0 ≤ r) (h : ∀ p ∈ L, pointNearTest M p r) :
    hull L ⊆ hull M + closedBall 0 (r : ℝ) := by
  first
  | apply convexHull_min _ ((convex_convexHull ℝ _).add (convex_closedBall _ _))
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨y, hy, hdist⟩ := Iff.mp (pointNearTest_correct M p r hr) (h p hp)
    exact ⟨y, hy, realPoint p - y,
      by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hdist, by abel⟩

/-- The test is exactly the Hausdorff bound between the actual convex bodies. -/
theorem hausdorffTest_correct {d : ℕ} (L M : List (RationalPoint d))
    (hL : 0 ∈ L) (hM : 0 ∈ M) (r : ℚ) (hr : 0 ≤ r) :
    hausdorffTest L M r ↔ dist (body L hL) (body M hM) ≤ (r : ℝ) := by
  first
  | constructor
    · rintro ⟨hLM, hML⟩
      change hausdorffDist (hull L) (hull M) ≤ (r : ℝ)
      apply hausdorffDist_le_of_mem_dist (by exact_mod_cast hr)
      · intro x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := hull_subset_add_closedBall L M r hr hLM hx
        exact ⟨y, hy, by simpa only [mem_closedBall, dist_eq_norm, sub_zero,
          add_sub_cancel_left] using hz⟩
      · intro y hy
        obtain ⟨x, hx, z, hz, rfl⟩ := hull_subset_add_closedBall M L r hr hML hy
        exact ⟨x, hx, by simpa only [mem_closedBall, dist_eq_norm, sub_zero,
          add_sub_cancel_left] using hz⟩
    · intro hdist
      have hdir (A B : List (RationalPoint d)) (hA : 0 ∈ A) (hB : 0 ∈ B)
          (hdist : dist (body A hA) (body B hB) ≤ (r : ℝ)) :
          ∀ p ∈ A, pointNearTest B p r := by
        intro p hp
        have hpa : realPoint p ∈ body A hA := subset_convexHull ℝ _ ⟨p, hp, rfl⟩
        obtain ⟨x, hx, hdx⟩ := (body B hB).isCompact.exists_infDist_eq_dist
          (body B hB).nonempty (realPoint p)
        apply Iff.mpr (pointNearTest_correct B p r hr)
        refine ⟨x, hx, ?_⟩
        rw [← hdx]
        exact (infDist_le_hausdorffDist_of_mem hpa ConvexBody.hausdorffEDist_ne_top).trans hdist
      exact ⟨hdir L M hL hM hdist, hdir M L hM hL (by rwa [dist_comm])⟩

def tupleHausdorffTest {n d : ℕ}
    (L M : Fin n → List (RationalPoint d)) (r : ℚ) : Prop :=
  ∀ i, hausdorffTest (L i) (M i) r

instance tupleHausdorffTest_decidable {n d : ℕ}
    (L M : Fin n → List (RationalPoint d)) (r : ℚ) :
    Decidable (tupleHausdorffTest L M r) := by unfold tupleHausdorffTest; infer_instance

theorem tupleHausdorffTest_correct {n d : ℕ}
    (L M : Fin n → List (RationalPoint d)) (hL : ∀ i, 0 ∈ L i) (hM : ∀ i, 0 ∈ M i)
    (r : ℚ) (hr : 0 ≤ r) :
    tupleHausdorffTest L M r ↔
      dist (fun i => body (L i) (hL i)) (fun i => body (M i) (hM i)) ≤ (r : ℝ) := by
  first
  | rw [dist_pi_le_iff (by exact_mod_cast hr)]
    exact forall_congr' (fun i => hausdorffTest_correct (L i) (M i) (hL i) (hM i) r hr)

end VolumePolynomials.RationalHulls
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalHausdorff.lean -/

/- BEGIN SOURCE: VolumePolynomials/CoefficientModulus.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# A rational modulus for all ordinary coefficients

The coefficient map is controlled by the literal Hausdorff distances of the
input bodies. The constants are explicit rational expressions in the dimension,
number of bodies, box radius, and rational interpolation data. No effective
modulus is inferred merely from qualitative compactness or continuity.
-/

open Set Finset MeasureTheory Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

section Geometry

theorem exists_near_weightedSum {n d : ℕ} (K L : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {ε : ℝ}
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) {x : Space d}
    (hx : x ∈ weightedSum K t) :
    ∃ y ∈ weightedSum L t, dist x y ≤ ε * ∑ i, t i := by
  first
  | classical
    obtain ⟨a, ha, hax⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    have hpoints : ∀ i, ∃ p ∈ K i, t i • p = a i := by
      first
      | intro i
        exact Set.mem_smul_set.mp (ha i)
    choose p hp hpa using hpoints
    choose q hq hdist using fun i =>
      (L i).isCompact.exists_infDist_eq_dist (L i).nonempty (p i)
    have hpq : ∀ i, dist (p i) (q i) ≤ ε := by
      first
      | intro i
        rw [← hdist i]
        exact (infDist_le_hausdorffDist_of_mem (hp i)
          ConvexBody.hausdorffEDist_ne_top).trans (hKL i)
    have hpx : ∑ i, t i • p i = x := by
      first
      | simpa only [hpa] using hax
    refine ⟨∑ i, t i • q i, (mem_sum_body _ _).mpr
      ⟨fun i => t i • q i, fun i => ⟨q i, hq i, rfl⟩, rfl⟩, ?_⟩
    rw [← hpx, dist_eq_norm, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖t i • p i - t i • q i‖ := norm_sum_le _ _
      _ = ∑ i, t i * dist (p i) (q i) := by
        first
        | apply Finset.sum_congr rfl
          intro i _
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (ht i), dist_eq_norm]
      _ ≤ ∑ i, t i * ε := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hpq i) (ht i)
      _ = ε * ∑ i, t i := by rw [← Finset.sum_mul, mul_comm]

theorem dist_weightedSum_le {n d : ℕ} (K L : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {ε : ℝ} (hε : 0 ≤ ε)
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) :
    dist (weightedSum K t) (weightedSum L t) ≤ ε * ∑ i, t i := by
  first
  | change hausdorffDist (weightedSum K t : Set (Space d))
      (weightedSum L t : Set (Space d)) ≤ _
    exact hausdorffDist_le_of_mem_dist (mul_nonneg hε (Finset.sum_nonneg fun i _ => ht i))
      (fun _ hx => exists_near_weightedSum K L t ht hKL hx)
      (fun _ hy => exists_near_weightedSum L K t ht
        (fun i => by simpa only [dist_comm] using hKL i) hy)

theorem weightedSum_subset_box {n d : ℕ} (K : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {R : ℝ}
    (hK : ∀ i, (K i : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R)) :
    (weightedSum K t : Set (Space d)) ⊆
      Icc (fun _ => -(R * ∑ i, t i)) (fun _ => R * ∑ i, t i) := by
  first
  | intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    have hpoints : ∀ i, ∃ p ∈ K i, t i • p = a i := by
      first
      | intro i
        exact Set.mem_smul_set.mp (ha i)
    choose p hp hpa using hpoints
    have hupper (j : Fin d) : (∑ i, a i) j ≤ R * ∑ i, t i := by
      first
      | simp only [Finset.sum_apply, ← hpa, Pi.smul_apply, smul_eq_mul]
        calc
          _ ≤ ∑ i, t i * R := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ((hK i (hp i)).2 j) (ht i)
          _ = R * ∑ i, t i := by rw [← Finset.sum_mul, mul_comm]
    have hlower (j : Fin d) : -(R * ∑ i, t i) ≤ (∑ i, a i) j := by
      first
      | simp only [Finset.sum_apply, ← hpa, Pi.smul_apply, smul_eq_mul]
        calc
          _ = ∑ i, t i * -R := by rw [← Finset.sum_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ((hK i (hp i)).1 j) (ht i)
    exact ⟨hlower, hupper⟩

end Geometry

/-- One strict rational bound for the sum of every interpolation weight vector. -/
def interpolationWeightBound (n d : ℕ) : ℚ :=
  1 + ∑ j : Fin (interpolationSize n d), ∑ i : Fin n, interpolationWeight j i

theorem interpolationWeightBound_pos (n d : ℕ) : 0 < interpolationWeightBound n d := by
  first
  | exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
        (interpolationWeight_pos j i).le)

theorem interpolationWeight_sum_le {n d : ℕ} (j : Fin (interpolationSize n d)) :
    (∑ i : Fin n, interpolationWeight j i) ≤ interpolationWeightBound n d := by
  first
  | apply (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun i _ => (interpolationWeight_pos k i).le)
      (Finset.mem_univ j)).trans
    exact le_add_of_nonneg_left zero_le_one

/-- Entirely rational coefficient-modulus constant for bodies in `[-R,R]^d`. -/
def coefficientModulus (n d : ℕ) (R : ℚ) : ℚ :=
  coefficientExtractionBound n d * interpolationWeightBound n d *
    (2 * R * interpolationWeightBound n d + 2) ^ d

/-- Uniform coefficient control, including lower-dimensional bodies. The only
smallness restriction is on the approximation error, not on the geometry. -/
theorem Realizes.coefficient_sub_le_of_dist_le {n d : ℕ}
    {K L : Fin n → Body d} {c c' : Coefficients n d}
    (hc : Realizes K c) (hc' : Realizes L c') (R : ℚ) (hR : 0 ≤ R)
    (hK : ∀ i, (K i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    (hL : ∀ i, (L i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε * (interpolationWeightBound n d : ℝ) ≤ 1)
    (hKL : ∀ i, dist (K i) (L i) ≤ ε) (α : MultiIndex n d) :
    |c α - c' α| ≤ ε * (coefficientModulus n d R : ℝ) := by
  first
  | let T : ℝ := interpolationWeightBound n d
    have hT : 0 < T := by
      first
      | dsimp [T]
        exact_mod_cast interpolationWeightBound_pos n d
    have hR' : 0 ≤ (R : ℝ) := by exact_mod_cast hR
    have hη : 0 ≤ ε * T * (2 * (R : ℝ) * T + 2) ^ d := by positivity
    have hsamples : ∀ j : Fin (interpolationSize n d),
        |evaluate c (fun i => (interpolationWeight j i : ℝ)) -
          evaluate c' (fun i => (interpolationWeight j i : ℝ))| ≤
            ε * T * (2 * (R : ℝ) * T + 2) ^ d := by
      first
      | intro j
        let t : Fin n → ℝ := fun i => interpolationWeight j i
        have ht : ∀ i, 0 ≤ t i := by
          intro i
          dsimp [t]
          exact_mod_cast (interpolationWeight_pos j i).le
        have hsum : ∑ i, t i ≤ T := by
          dsimp [t, T]
          exact_mod_cast interpolationWeight_sum_le j
        have hbox : ∀ P : Fin n → Body d,
            (∀ i, (P i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) →
            (weightedSum P t : Set (Space d)) ⊆
              Icc (fun _ => -((R : ℝ) * T)) (fun _ => (R : ℝ) * T) := by
          intro P hP x hx
          obtain ⟨hlo, hhi⟩ := weightedSum_subset_box P t ht hP hx
          have hbound := mul_le_mul_of_nonneg_left hsum hR'
          exact ⟨fun k => (neg_le_neg hbound).trans (hlo k),
            fun k => (hhi k).trans hbound⟩
        rw [hc _ ht, hc' _ ht]
        simpa only [volumeFunction, mul_assoc] using
          abs_bodyVolume_sub_le_of_dist_le (weightedSum K t) (weightedSum L t)
          (mul_nonneg hR' hT.le) (mul_nonneg hε hT.le) hsmall
          (hbox K hK) (hbox L hL)
          ((dist_weightedSum_le K L t ht hε hKL).trans
            (mul_le_mul_of_nonneg_left hsum hε))
    have h := abs_coefficient_sub_le_of_samples c c' hη hsamples α
    convert h using 1
    simp only [coefficientModulus, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_ofNat]
    dsimp [T]
    ring

end VolumePolynomials
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CoefficientModulus.lean -/

/- BEGIN SOURCE: VolumePolynomials/QuadraticSeparation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Rational quadratic separation from certified finite rational nets

This file verifies the abstract separation step used in Section 8 of
`Volume polynomials and the Heine–Shephard problem`.

It does **not** assume or assert that a particular set is a volume-polynomial
locus. Its interface records every geometric input needed to apply the result:
a closed target, finite rational approximations to that target, and certified
vanishing errors in both directions. The centers need not lie exactly in the
target. Proving these inputs for convex bodies is a separate obligation.
-/

open scoped BigOperators Topology
open Filter Metric

namespace VolumePolynomials.QuadraticSeparation

variable {ι : Type*} [Fintype ι]

abbrev Space (ι : Type*) := PiLp 2 (fun _ : ι => ℝ)

/-- A vector with rational coordinates, regarded as a Euclidean vector. -/
def ofRat (a : ι → ℚ) : Space ι := WithLp.toLp 2 (fun i => (a i : ℝ))

theorem real_norm_sq_eq (x : Space ι) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  first
  | simpa only [Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x)

@[simp] theorem ofRat_apply (a : ι → ℚ) (i : ι) : ofRat a i = (a i : ℝ) := rfl

theorem denseRange_ofRat : DenseRange (ofRat (ι := ι)) := by
  first
  | have h : DenseRange (fun a : ι → ℚ => fun i => (a i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    exact (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.surjective.denseRange.comp h
      (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))

/-- Squared distances between rational vectors can be tested using only rationals. -/
theorem dist_ofRat_sq (a b : ι → ℚ) :
    dist (ofRat a) (ofRat b) ^ 2 = ((∑ i, (a i - b i) ^ 2 : ℚ) : ℝ) := by
  first
  | rw [dist_eq_norm, real_norm_sq_eq]
    simp [ofRat, Rat.cast_sum]

/-- The precise interface supplied by the finite-net construction in Section 8.1. -/
structure Model (ι : Type*) [Fintype ι] where
  target : Set (Space ι)
  closed : IsClosed target
  net : ℕ → Finset (ι → ℚ)
  error : ℕ → ℚ
  error_nonneg : ∀ m, 0 ≤ error m
  error_tendsto : Tendsto (fun m => (error m : ℝ)) atTop (𝓝 0)
  net_near : ∀ m q, q ∈ net m →
    ∃ y ∈ target, dist (ofRat q) y ≤ (error m : ℝ)
  covers : ∀ m x, x ∈ target → ∃ q ∈ net m, dist x (ofRat q) ≤ (error m : ℝ)

namespace Model

variable (M : Model ι)

/-- The finite rational admission test (8.4), with the net's certified radius. -/
def Admitted (a : ι → ℚ) (r : ℚ) (m : ℕ) : Prop :=
  0 < r ∧ ∀ q ∈ M.net m, (r + M.error m) ^ 2 < ∑ i, (a i - q i) ^ 2

instance admittedDecidable (a : ι → ℚ) (r : ℚ) (m : ℕ) :
    Decidable (M.Admitted a r m) := by
  first
  | unfold Admitted
    infer_instance

/-- An admitted rational ball is disjoint from the target, with strict separation. -/
theorem admitted_separates {a : ι → ℚ} {r : ℚ} {m : ℕ}
    (ha : M.Admitted a r m) {x : Space ι} (hx : x ∈ M.target) :
    (r : ℝ) < dist x (ofRat a) := by
  first
  | obtain ⟨q, hq, hdist⟩ := M.covers m x hx
    have hr : 0 < (r : ℝ) := by exact_mod_cast ha.1
    have he : 0 ≤ (M.error m : ℝ) := by exact_mod_cast M.error_nonneg m
    have hsq : ((r : ℝ) + (M.error m : ℝ)) ^ 2 < dist (ofRat a) (ofRat q) ^ 2 := by
      first
      | rw [dist_ofRat_sq]
        exact_mod_cast ha.2 q hq
    have hlt : (r : ℝ) + (M.error m : ℝ) < dist (ofRat a) (ofRat q) :=
      (sq_lt_sq₀ (by positivity) dist_nonneg).mp hsq
    have htri := dist_triangle (ofRat a) x (ofRat q)
    rw [dist_comm (ofRat a) x] at htri
    linarith

/-- Every point outside the closed target belongs to an admitted rational ball. -/
theorem exists_admitted_of_not_mem {x : Space ι} (hx : x ∉ M.target) :
    ∃ a : ι → ℚ, ∃ r : ℚ, ∃ m : ℕ,
      M.Admitted a r m ∧ dist x (ofRat a) < (r : ℝ) := by
  first
  | obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp M.closed.isOpen_compl x hx
    obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp denseRange_ofRat x (δ / 8) (by positivity)
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show δ / 4 < δ / 2 by linarith)
    have hevent : ∀ᶠ m in atTop, (M.error m : ℝ) < δ / 8 :=
      M.error_tendsto.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hevent.exists
    have hr : 0 < (r : ℝ) := by linarith
    refine ⟨a, r, m, ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hr
    · intro q hq
      obtain ⟨y, hy, hqy⟩ := M.net_near m q hq
      have hδy : δ ≤ dist x y := by
        first
        | by_contra! h
          exact hball (by simpa [Metric.mem_ball, dist_comm] using h) hy
      have hxy := dist_triangle x (ofRat q) y
      have htri := dist_triangle x (ofRat a) (ofRat q)
      have hlt : (r : ℝ) + (M.error m : ℝ) < dist (ofRat a) (ofRat q) := by
        first
        | linarith
      have he : 0 ≤ (M.error m : ℝ) := by exact_mod_cast M.error_nonneg m
      have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ (r : ℝ) + (M.error m : ℝ))
        dist_nonneg).mpr hlt
      rw [dist_ofRat_sq] at hsq
      exact_mod_cast hsq
    · linarith

/-- The exact rational-ball characterization before homogenizing (8.5). -/
theorem mem_iff_admitted_balls (x : Space ι) :
    x ∈ M.target ↔
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m →
        (r : ℝ) ^ 2 ≤ dist x (ofRat a) ^ 2 := by
  first
  | constructor
    · intro hx a r m ha
      have hr : 0 ≤ (r : ℝ) := by exact_mod_cast ha.1.le
      exact (sq_le_sq₀ hr dist_nonneg).mpr (M.admitted_separates ha hx).le
    · intro h
      by_contra hx
      obtain ⟨a, r, m, hadm, hdist⟩ := M.exists_admitted_of_not_mem hx
      have hr : 0 ≤ (r : ℝ) := by exact_mod_cast hadm.1.le
      have hlt := (sq_lt_sq₀ dist_nonneg hr).mpr hdist
      exact (not_lt_of_ge (h a r m hadm)) hlt

/-- The finite tests at every scale characterize membership in the closed target. -/
theorem mem_iff_all_finite_tests (x : Space ι) :
    x ∈ M.target ↔ ∀ m, ∃ q ∈ M.net m, dist x (ofRat q) ≤ (M.error m : ℝ) := by
  first
  | refine ⟨fun hx m => M.covers m x hx, ?_⟩
    intro h
    by_contra hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp M.closed.isOpen_compl x hx
    obtain ⟨m, hm⟩ :=
      (M.error_tendsto.eventually (gt_mem_nhds (by positivity : 0 < δ / 2))).exists
    obtain ⟨q, hq, hdist⟩ := h m
    obtain ⟨y, hy, hqy⟩ := M.net_near m q hq
    have hxy : dist x y < δ := by
      first
      | have htri := dist_triangle x (ofRat q) y
        linarith
    exact hball (by simpa [Metric.mem_ball, dist_comm] using hxy) hy

end Model

/-- The paper's exact rational nets are a special case of the certified
approximate-net interface. This constructor makes the equivalence explicit. -/
def Model.ofExact (target : Set (Space ι)) (closed : IsClosed target)
    (net : ℕ → Finset (ι → ℚ)) (error : ℕ → ℚ)
    (error_nonneg : ∀ m, 0 ≤ error m)
    (error_tendsto : Tendsto (fun m => (error m : ℝ)) atTop (𝓝 0))
    (net_mem : ∀ m q, q ∈ net m → ofRat q ∈ target)
    (covers : ∀ m x, x ∈ target → ∃ q ∈ net m, dist x (ofRat q) ≤ (error m : ℝ)) :
    Model ι where
  target := target
  closed := closed
  net := net
  error := error
  error_nonneg := error_nonneg
  error_tendsto := error_tendsto
  net_near := by
    first
    | intro m q hq
      refine ⟨ofRat q, net_mem m q hq, ?_⟩
      have hm : 0 ≤ (error m : ℝ) := by exact_mod_cast error_nonneg m
      simpa only [dist_self] using hm
  covers := covers

/-- Sum of the ordinary coefficients. -/
def total (c : Space ι) : ℝ := ∑ i, c i

/-- Division by the coefficient sum, used only with a proved nonzero sum. -/
noncomputable def normalize (c : Space ι) : Space ι := (total c)⁻¹ • c

/-- The real quadratic form in (8.5), written intrinsically in Euclidean space. -/
noncomputable def quadratic (a : ι → ℚ) (r : ℚ) (c : Space ι) : ℝ :=
  ‖c - total c • ofRat a‖ ^ 2 - (r : ℝ) ^ 2 * total c ^ 2

theorem quadratic_eq_sum (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = ∑ i, (c i - total c * (a i : ℝ)) ^ 2 -
      (r : ℝ) ^ 2 * total c ^ 2 := by
  first
  | rw [quadratic, real_norm_sq_eq]
    rfl

@[simp] theorem total_zero : total (0 : Space ι) = 0 := by simp [total]

@[simp] theorem total_smul (t : ℝ) (c : Space ι) : total (t • c) = t * total c := by
  first
  | simp [total, Finset.mul_sum]

@[simp] theorem quadratic_zero (a : ι → ℚ) (r : ℚ) :
    quadratic a r (0 : Space ι) = 0 := by simp [quadratic]

/-- Exact homogeneity: each admitted inequality is a homogeneous quadratic. -/
theorem quadratic_smul (a : ι → ℚ) (r : ℚ) (t : ℝ) (c : Space ι) :
    quadratic a r (t • c) = t ^ 2 * quadratic a r c := by
  first
  | simp only [quadratic, total_smul, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring

theorem quadratic_eq_normalized (a : ι → ℚ) (r : ℚ) (c : Space ι)
    (hc : total c ≠ 0) :
    quadratic a r c = total c ^ 2 *
      (dist (normalize c) (ofRat a) ^ 2 - (r : ℝ) ^ 2) := by
  first
  | have heq : c - total c • ofRat a = total c • (normalize c - ofRat a) := by
      first
      | simp [normalize, smul_sub, smul_smul, hc]
    rw [quadratic, heq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, dist_eq_norm]
    ring

/-- Rational polynomial representing exactly the real quadratic form. -/
noncomputable def rationalForm (a : ι → ℚ) (r : ℚ) : MvPolynomial ι ℚ :=
  ∑ i, (MvPolynomial.X i - (∑ j, MvPolynomial.X j) * MvPolynomial.C (a i)) ^ 2 -
    MvPolynomial.C (r ^ 2) * (∑ j, MvPolynomial.X j) ^ 2

theorem eval_rationalForm (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (rationalForm a r) =
      quadratic a r c := by
  first
  | rw [quadratic_eq_sum]
    simp [rationalForm, total, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul]

/-- The polynomial form, not merely its evaluation, is homogeneous of degree two. -/
theorem rationalForm_isHomogeneous (a : ι → ℚ) (r : ℚ) :
    (rationalForm a r).IsHomogeneous 2 := by
  first
  | have hsum : (∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℚ)).IsHomogeneous 1 :=
      MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X _ i)
    unfold rationalForm
    apply MvPolynomial.IsHomogeneous.sub
    · apply MvPolynomial.IsHomogeneous.sum
      intro i _
      have hlin : (MvPolynomial.X i - (∑ j, MvPolynomial.X j) *
          MvPolynomial.C (a i) : MvPolynomial ι ℚ).IsHomogeneous 1 := by
        first
        | apply (MvPolynomial.isHomogeneous_X _ i).sub
          simpa [mul_comm] using hsum.C_mul (a i)
      simpa using hlin.pow 2
    · exact (hsum.pow 2).C_mul (r ^ 2)

/-- A computable index type for the rational centers, radii, and net scales. -/
abbrev CertificateIndex (ι : Type*) := (ι → ℚ) × ℚ × ℕ

/-- Computable enumeration of the admitted descriptors, relative to the rational net data. -/
def enumeratedCertificate [Encodable ι] (M : Model ι) (k : ℕ) : Option (CertificateIndex ι) :=
  match Encodable.decode (α := CertificateIndex ι) k with
  | none => none
  | some (a, r, m) => if M.Admitted a r m then some (a, r, m) else none

/-- Every admitted descriptor is returned at its explicit natural-number code. -/
theorem enumeratedCertificate_encode [Encodable ι] (M : Model ι)
    (a : ι → ℚ) (r : ℚ) (m : ℕ) (h : M.Admitted a r m) :
    enumeratedCertificate M (Encodable.encode (a, r, m)) = some (a, r, m) := by
  first
  | simp [enumeratedCertificate, h]

/-- An explicitly computable rational matrix of coefficients for (8.5). -/
def rationalMatrix [DecidableEq ι] (a : ι → ℚ) (r : ℚ) (i j : ι) : ℚ :=
  (if i = j then 1 else 0) - a i - a j + (∑ k, a k ^ 2) - r ^ 2

theorem quadratic_expansion (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = (∑ i, c i ^ 2) -
      2 * total c * (∑ i, (a i : ℝ) * c i) +
      total c ^ 2 * ((∑ i, (a i : ℝ) ^ 2) - (r : ℝ) ^ 2) := by
  first
  | rw [quadratic_eq_sum]
    have h : (∑ i, (c i - total c * (a i : ℝ)) ^ 2) =
        (∑ i, c i ^ 2) - 2 * total c * (∑ i, (a i : ℝ) * c i) +
          total c ^ 2 * (∑ i, (a i : ℝ) ^ 2) := by
      first
      | calc
          _ = ∑ i, (c i ^ 2 - 2 * total c * ((a i : ℝ) * c i) +
              total c ^ 2 * (a i : ℝ) ^ 2) := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              ring
          _ = _ := by
            first
            | simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h]
    ring

/-- The computable rational matrix evaluates to exactly (8.5), with every coefficient checked. -/
theorem quadratic_eq_matrix [DecidableEq ι] (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = ∑ i, ∑ j, (rationalMatrix a r i j : ℝ) * c i * c j := by
  first
  | rw [quadratic_expansion]
    have hdiag : (∑ i, ∑ j, ((if i = j then 1 else 0 : ℝ) * c i * c j)) =
        ∑ i, c i ^ 2 := by
      first
      | simp [sq, ite_mul]
    have hleft : (∑ i, ∑ j, (a i : ℝ) * c i * c j) =
        (∑ i, (a i : ℝ) * c i) * total c := by
      first
      | calc
          _ = ∑ i, ((a i : ℝ) * c i) * total c := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              rw [total, Finset.mul_sum]
          _ = _ := (Finset.sum_mul _ _ _).symm
    have hright : (∑ i, ∑ j, (a j : ℝ) * c i * c j) =
        total c * (∑ i, (a i : ℝ) * c i) := by
      first
      | calc
          _ = ∑ i, c i * (∑ j, (a j : ℝ) * c j) := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
          _ = _ := (Finset.sum_mul _ _ _).symm
    have hconst (t : ℝ) : (∑ i, ∑ j, t * c i * c j) = t * total c ^ 2 := by
      first
      | simp only [total, sq, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    have hexpand : (∑ i, ∑ j, (rationalMatrix a r i j : ℝ) * c i * c j) =
        (∑ i, ∑ j, ((if i = j then 1 else 0 : ℝ) * c i * c j)) -
        (∑ i, ∑ j, (a i : ℝ) * c i * c j) -
        (∑ i, ∑ j, (a j : ℝ) * c i * c j) +
        (∑ i, ∑ j, ((∑ k, (a k : ℝ) ^ 2) - (r : ℝ) ^ 2) * c i * c j) := by
      first
      | simp only [rationalMatrix, Rat.cast_sub, Rat.cast_add, Rat.cast_sum, Rat.cast_pow,
          apply_ite, Rat.cast_one, Rat.cast_zero]
        simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        ring
    rw [hexpand, hdiag, hleft, hright, hconst]
    ring

/--
An explicit countable sequence of rational forms. Nonadmitted indices and unused
natural-number codes produce the zero form. Its rational descriptors are computed
by `enumeratedCertificate`; the `MvPolynomial` representation uses Mathlib's
noncomputable polynomial implementation.
-/
noncomputable def enumeratedForm [Encodable ι] (M : Model ι) (k : ℕ) : MvPolynomial ι ℚ :=
  match Encodable.decode (α := CertificateIndex ι) k with
  | none => 0
  | some (a, r, m) => if M.Admitted a r m then rationalForm a r else 0

theorem enumeratedForm_isHomogeneous [Encodable ι] (M : Model ι) (k : ℕ) :
    (enumeratedForm M k).IsHomogeneous 2 := by
  first
  | unfold enumeratedForm
    split
    · exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℚ) 2
    · split
      · exact rationalForm_isHomogeneous _ _
      · exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℚ) 2

/-- Enumerating all natural-number codes loses no admitted inequality. -/
theorem forall_enumerated_iff [Encodable ι] (M : Model ι) (c : Space ι) :
    (∀ k, 0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k)) ↔
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m → 0 ≤ quadratic a r c := by
  first
  | constructor
    · intro h a r m ha
      have hk := h (Encodable.encode (a, r, m))
      simpa [enumeratedForm, Encodable.encodek, ha, eval_rationalForm] using hk
    · intro h k
      unfold enumeratedForm
      split
      · simp
      · split
        · rw [eval_rationalForm]
          exact h _ _ _ ‹_›
        · simp

/-- A nonzero nonnegative coefficient vector has a strictly positive total. -/
theorem total_pos {c : Space ι} (hn : ∀ i, 0 ≤ c i) (hc : c ≠ 0) : 0 < total c := by
  first
  | have hnonneg : 0 ≤ total c := Finset.sum_nonneg (fun i _ => hn i)
    refine lt_of_le_of_ne hnonneg ?_
    intro heq
    apply hc
    ext i
    have hzero : ∀ i, c i = 0 := by
      first
      | simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp heq.symm
    exact hzero i

/--
The full abstract homogenized characterization.

The four hypotheses explicitly connect the target set to the intended coefficient
locus; none is silently treated as an axiom about convex geometry.
-/
theorem coefficient_characterization (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m → 0 ≤ quadratic a r c := by
  first
  | constructor
    · intro hc
      refine ⟨hnonneg c hc, ?_⟩
      intro a r m ha
      by_cases hz : c = 0
      · simp [hz]
      have hs := total_pos (hnonneg c hc) hz
      rw [quadratic_eq_normalized _ _ _ hs.ne']
      apply mul_nonneg (sq_nonneg _)
      exact sub_nonneg.mpr ((M.mem_iff_admitted_balls _).mp (hnormalize c hc hz) a r m ha)
    · rintro ⟨hn, hq⟩
      by_cases hz : c = 0
      · simpa [hz] using hzero
      have hs := total_pos hn hz
      apply hrealize c hs
      apply (M.mem_iff_admitted_balls _).mpr
      intro a r m ha
      have hquad := hq a r m ha
      rw [quadratic_eq_normalized _ _ _ hs.ne'] at hquad
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sq_pos_of_pos hs)).mp hquad)

/-- Countably indexed rational homogeneous quadratic forms give the same exact criterion. -/
theorem countable_coefficient_characterization [Encodable ι]
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧
      ∀ k, 0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) := by
  first
  | rw [forall_enumerated_iff]
    exact coefficient_characterization M V hzero hnonneg hnormalize hrealize c

/-- Every vector outside the intended locus has one strictly violated finite certificate. -/
theorem exists_strict_certificate [Encodable ι]
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) (hc : c ∉ V) :
    (∃ i, c i < 0) ∨ ∃ k,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) < 0 := by
  first
  | have h := (countable_coefficient_characterization M V hzero hnonneg hnormalize hrealize c).not.mp hc
    push_neg at h
    by_cases hn : ∀ i, 0 ≤ c i
    · exact Or.inr (h hn)
    · exact Or.inl (by simpa only [not_forall, not_le] using hn)

end VolumePolynomials.QuadraticSeparation
end -- closes the original EOF section from source line 13
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/QuadraticSeparation.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalCoefficientNets.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Certified computable finite nets of actual volume-polynomial coefficients

The finite list of rational hull tuples is evaluated by the terminating
rational box-volume algorithm. Exact interpolation gives rational coefficient
centers. The explicit Hausdorff coefficient modulus supplies the uniform
covering bound, while every center is close to an actual bounded realization.
This constructs the geometric/computational Model required by Section 8.
-/

open Set Filter Metric
open scoped BigOperators Topology

namespace VolumePolynomials.RationalCoefficientNets

open RationalHulls

def samplingTolerance (k : ℕ) : ℚ := 1 / ((k : ℚ) + 1)

theorem samplingTolerance_pos (k : ℕ) : 0 < samplingTolerance k := by
  first
  | unfold samplingTolerance
    positivity

def gridMultiplier (n d : ℕ) : ℕ := ⌈interpolationWeightBound n d⌉₊ + 1

def resolution (n d k : ℕ) : ℕ := gridMultiplier n d * (k + 1)

theorem gridMultiplier_pos (n d : ℕ) : 0 < gridMultiplier n d := by
  first
  | unfold gridMultiplier
    omega

theorem weightBound_le_gridMultiplier (n d : ℕ) :
    interpolationWeightBound n d ≤ (gridMultiplier n d : ℚ) := by
  first
  | exact (Nat.le_ceil _).trans (by simp [gridMultiplier])

theorem resolution_bounds (n d k : ℕ) :
    1 / ((resolution n d k : ℝ) + 1) ≤ (samplingTolerance k : ℝ) ∧
      (1 / ((resolution n d k : ℝ) + 1)) * (interpolationWeightBound n d : ℝ) ≤ 1 := by
  first
  | have hA : (1 : ℝ) ≤ gridMultiplier n d := by exact_mod_cast gridMultiplier_pos n d
    have hT : (interpolationWeightBound n d : ℝ) ≤ gridMultiplier n d := by
      exact_mod_cast weightBound_le_gridMultiplier n d
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hres : (resolution n d k : ℝ) + 1 =
        (gridMultiplier n d : ℝ) * ((k : ℝ) + 1) + 1 := by simp [resolution]
    have hd : 0 < (resolution n d k : ℝ) + 1 := by positivity
    constructor
    · simp only [samplingTolerance, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast]
      apply one_div_le_one_div_of_le (by positivity)
      rw [hres]
      nlinarith
    · rw [one_div, inv_mul_eq_div, div_le_one hd]
      rw [hres]
      nlinarith

def coordinateBudget (n d R : ℕ) : ℚ :=
  coefficientExtractionBound n d + coefficientModulus n d (R : ℚ) + 1

theorem coefficientModulus_nonneg (n d R : ℕ) : 0 ≤ coefficientModulus n d (R : ℚ) := by
  first
  | have hT : 0 ≤ interpolationWeightBound n d := (interpolationWeightBound_pos n d).le
    unfold coefficientModulus
    exact mul_nonneg (mul_nonneg (coefficientExtractionBound_nonneg n d)
      (interpolationWeightBound_pos n d).le) (by positivity)

theorem coordinateBudget_pos (n d R : ℕ) : 0 < coordinateBudget n d R := by
  first
  | have hE := coefficientExtractionBound_nonneg n d
    have hC := coefficientModulus_nonneg n d R
    unfold coordinateBudget
    linarith

def netError (n d R k : ℕ) : ℚ :=
  (Fintype.card (MultiIndex n d) + 1) * coordinateBudget n d R * samplingTolerance k

def coefficientNet (n d R k : ℕ) : Finset (MultiIndex n d → ℚ) :=
  ((candidateTuples n d R (resolution n d k)).map
    (fun L => approximateCoefficients L (samplingTolerance k) (samplingTolerance_pos k))).toFinset

def boundedTarget (n d R : ℕ) : Set (QuadraticSeparation.Space (MultiIndex n d)) :=
  WithLp.toLp 2 '' boundedVolumeLocus n d
    (Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))

theorem isCompact_boundedTarget (n d R : ℕ) : IsCompact (boundedTarget n d R) := by
  first
  | apply (isCompact_boundedVolumeLocus n d isCompact_Icc).image
    exact PiLp.continuous_toLp 2 _

theorem norm_le_sum_abs {ι : Type*} [Fintype ι] (x : QuadraticSeparation.Space ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  first
  | apply (sq_le_sq₀ (norm_nonneg x) (Finset.sum_nonneg fun i _ => abs_nonneg (x i))).mp
    rw [QuadraticSeparation.real_norm_sq_eq]
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x i|)
        (fun i _ => abs_nonneg (x i)))

theorem dist_le_card_mul {ι : Type*} [Fintype ι] (x y : QuadraticSeparation.Space ι)
    {δ : ℝ} (h : ∀ i, |x i - y i| ≤ δ) : dist x y ≤ Fintype.card ι * δ := by
  first
  | rw [dist_eq_norm]
    apply (norm_le_sum_abs (x - y)).trans
    calc
      _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum (fun i _ => h i)
      _ = Fintype.card ι * δ := by simp

theorem budget_to_netError {n d R k : ℕ}
    {x y : QuadraticSeparation.Space (MultiIndex n d)}
    (h : ∀ α, |x α - y α| ≤ (coordinateBudget n d R : ℝ) * (samplingTolerance k : ℝ)) :
    dist x y ≤ (netError n d R k : ℝ) := by
  first
  | apply (dist_le_card_mul x y h).trans
    simp only [netError, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    have hB : 0 ≤ (coordinateBudget n d R : ℝ) := by
      exact_mod_cast (coordinateBudget_pos n d R).le
    have he : 0 ≤ (samplingTolerance k : ℝ) := by exact_mod_cast (samplingTolerance_pos k).le
    nlinarith

theorem coefficientNet_near (n d R k : ℕ) (q : MultiIndex n d → ℚ)
    (hq : q ∈ coefficientNet n d R k) :
    ∃ c ∈ boundedTarget n d R,
      dist (QuadraticSeparation.ofRat q) c ≤ (netError n d R k : ℝ) := by
  first
  | obtain ⟨L, hL, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have hLi := (mem_candidateTuples L).mp hL
    have hL0 : ∀ i, 0 ∈ L i := fun i => ((mem_candidates (L i)).mp (hLi i)).2
    let K : Fin n → Body d := fun i => body (L i) (hL0 i)
    obtain ⟨c, hc⟩ := exists_volume_polynomial K
    refine ⟨WithLp.toLp 2 c, ⟨c, ⟨K, ?_, hc⟩, rfl⟩, ?_⟩
    · intro i
      exact ⟨zero_mem_body (L i) (hL0 i), candidate_bounded (L i) (hLi i)⟩
    · apply budget_to_netError
      intro α
      have ha := approximateCoefficients_correct L hL0 hc (samplingTolerance k)
        (samplingTolerance_pos k) α
      apply ha.trans
      apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast (samplingTolerance_pos k).le)
      have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
        exact_mod_cast coefficientModulus_nonneg n d R
      simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
      linarith

theorem coefficientNet_covers (n d R k : ℕ)
    (c : QuadraticSeparation.Space (MultiIndex n d)) (hc : c ∈ boundedTarget n d R) :
    ∃ q ∈ coefficientNet n d R k, dist c (QuadraticSeparation.ofRat q) ≤ (netError n d R k : ℝ) := by
  first
  | classical
    obtain ⟨c', ⟨K, hK, hc'⟩, rfl⟩ := hc
    choose L hL hdist using fun i => exists_candidate_near (R := R)
      (k := resolution n d k) (K i) (hK i).1 (hK i).2
    have hL0 : ∀ i, 0 ∈ L i := fun i => ((mem_candidates (L i)).mp (hL i)).2
    let P : Fin n → Body d := fun i => body (L i) (hL0 i)
    obtain ⟨cP, hcP⟩ := exists_volume_polynomial P
    let q := approximateCoefficients L (samplingTolerance k) (samplingTolerance_pos k)
    refine ⟨q, List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨L, (mem_candidateTuples L).mpr hL, rfl⟩), ?_⟩
    apply budget_to_netError
    intro α
    have hgeom := hc'.coefficient_sub_le_of_dist_le hcP (R : ℚ) (by positivity)
      (fun i => (hK i).2) (fun i => candidate_bounded (L i) (hL i))
      (by positivity : 0 ≤ 1 / ((resolution n d k : ℝ) + 1))
      (resolution_bounds n d k).2 hdist α
    have happ := approximateCoefficients_correct L hL0 hcP (samplingTolerance k)
      (samplingTolerance_pos k) α
    have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
      exact_mod_cast coefficientModulus_nonneg n d R
    have hgeom' : |c' α - cP α| ≤
        (samplingTolerance k : ℝ) * (coefficientModulus n d (R : ℚ) : ℝ) :=
      hgeom.trans (mul_le_mul_of_nonneg_right (resolution_bounds n d k).1 hC)
    have htri := abs_sub_le (c' α) (cP α) (q α : ℝ)
    rw [abs_sub_comm (cP α) (q α : ℝ)] at htri
    change |c' α - (q α : ℝ)| ≤ _
    have he : 0 ≤ (samplingTolerance k : ℝ) := by exact_mod_cast (samplingTolerance_pos k).le
    simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
    dsimp [q] at htri ⊢
    nlinarith

/-- The complete finite-net input, with its rational data executable and its
geometric meaning proved for actual compact convex bodies. -/
def model (n d R : ℕ) : QuadraticSeparation.Model (MultiIndex n d) where
  target := boundedTarget n d R
  closed := (isCompact_boundedTarget n d R).isClosed
  net := coefficientNet n d R
  error := netError n d R
  error_nonneg := by
    first
    | intro k
      exact mul_nonneg (mul_nonneg (by positivity) (coordinateBudget_pos n d R).le)
        (samplingTolerance_pos k).le
  error_tendsto := by
    first
    | have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (((Fintype.card (MultiIndex n d) : ℝ) + 1) * (coordinateBudget n d R : ℝ))
      simpa only [netError, samplingTolerance, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_one, mul_zero] using h
  net_near := coefficientNet_near n d R
  covers := coefficientNet_covers n d R

end VolumePolynomials.RationalCoefficientNets
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalCoefficientNets.lean -/

/- BEGIN SOURCE: VolumePolynomials/ExplicitNormalization.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# The explicit normalization box

The maximal-simplex coordinates bound the image by the unit cube. The coordinate
simplex contains the cube of side `1/d`; its elementary product volume suffices
to obtain the paper's final radius `d`, without needing a simplex-volume formula.
-/

noncomputable section
open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators ENNReal

namespace VolumePolynomials

def droppedCoordinateMap {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Space d →ᵃ[ℝ] Space d := AffineMap.pi (fun i => b.coord i.succ)

@[simp] theorem droppedCoordinateMap_apply {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (x : Space d) (i : Fin d) :
    droppedCoordinateMap b x i = b.coord i.succ x := rfl

theorem droppedCoordinateMap_bijective {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Function.Bijective (droppedCoordinateMap b) := by
  first
  | constructor
    · intro x y hxy
      apply b.ext_elem
      intro i
      cases i using Fin.cases with
      | zero =>
          have hx := b.sum_coord_apply_eq_one x
          have hy := b.sum_coord_apply_eq_one y
          rw [Fin.sum_univ_succ] at hx hy
          have hh : (∑ j : Fin d, b.coord j.succ x) = ∑ j : Fin d, b.coord j.succ y := by
            first
            | apply Finset.sum_congr rfl
              intro j _
              exact congrFun hxy j
          linarith
      | succ j => exact congrFun hxy j
    · intro y
      let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
      have hw : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_succ]
      refine ⟨Finset.univ.affineCombination ℝ b w, ?_⟩
      funext i
      exact (b.coord_apply_combination_of_mem (Finset.mem_univ i.succ) hw).trans
        (by simp [w])

def droppedCoordinateEquiv {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Space d ≃ᵃ[ℝ] Space d := AffineEquiv.ofBijective (droppedCoordinateMap_bijective b)

@[simp] theorem droppedCoordinateEquiv_apply {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (x : Space d) (i : Fin d) :
    droppedCoordinateEquiv b x i = b.coord i.succ x := rfl

@[simp] theorem droppedCoordinateEquiv_zero_vertex {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) : droppedCoordinateEquiv b (b 0) = 0 := by
  first
  | funext i
    simp [b.coord_apply_ne i.succ_ne_zero]

theorem smallCube_subset_coordinate_image {d : ℕ} (hd : 0 < d) (K : Body d)
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (hb : ∀ i, b i ∈ K) :
    Icc (0 : Space d) (fun _ => (d : ℝ)⁻¹) ⊆ droppedCoordinateEquiv b '' (K : Set (Space d)) := by
  first
  | classical
    intro y hy
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hsum : ∑ i, y i ≤ 1 := by
      first
      | calc
          ∑ i, y i ≤ ∑ _i : Fin d, (d : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hy.2 i)
          _ = 1 := by simp [hdpos.ne']
    let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
    have hw : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_succ]
    have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))), 0 ≤ w i := by
      first
      | intro i _
        cases i using Fin.cases with
        | zero => exact sub_nonneg.mpr hsum
        | succ i => exact hy.1 i
    let x := Finset.univ.affineCombination ℝ b w
    have hx : x ∈ K := (convexHull_min (Set.range_subset_iff.mpr hb) K.convex)
      (affineCombination_mem_convexHull hw0 hw)
    refine ⟨x, hx, ?_⟩
    funext i
    exact (b.coord_apply_combination_of_mem (Finset.mem_univ i.succ) hw).trans
      (by simp [w])

/-- Lemma 2.3's actual affine normalization, including its common determinant-one
linear map and the bound on the whole Minkowski sum. -/
theorem explicit_normalization {n d : ℕ} (hd : 0 < d) (K : Fin n → Body d)
    (hvol : bodyVolume (∑ i, K i) = 1) :
    ∃ (g : Space d →L[ℝ] Space d) (p : Fin n → Space d),
      |LinearMap.det g.toLinearMap| = 1 ∧ (∀ i, p i ∈ K i) ∧
      let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (K i))
      (∀ i, (0 : Space d) ∈ L i) ∧
        ((∑ i, L i : Body d) : Set (Space d)) ⊆
          Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ)) := by
  first
  | classical
    let S : Body d := ∑ i, K i
    have hSpos : 0 < volume (S : Set (Space d)) := by
      first
      | have ht : 0 < (volume (S : Set (Space d))).toReal := by
          first
          | change 0 < bodyVolume S
            rw [show bodyVolume S = 1 from hvol]
            exact zero_lt_one
        exact (ENNReal.toReal_pos_iff.mp ht).1
    have hspan : affineSpan ℝ (S : Set (Space d)) = ⊤ :=
      (S.convex.addHaar_pos_iff_affineSpan_eq_top (μ := volume)).mp hSpos
    obtain ⟨b, hb, hcoord⟩ := S.isCompact.exists_affineBasis_abs_coord_le_one
      (ι := Fin (d + 1)) hspan (by simp [Space])
    let T : Space d ≃ᵃ[ℝ] Space d := droppedCoordinateEquiv b
    let f : Space d →L[ℝ] Space d := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
    let D : ℝ := |LinearMap.det f.toLinearMap|
    have hTD : volume.real (T '' (S : Set (Space d))) = D := by
      first
      | rw [bodyVolume_affine_image, show bodyVolume S = 1 from hvol, mul_one]
        rfl
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hlow : ((d : ℝ)⁻¹) ^ d ≤ D := by
      first
      | rw [← hTD]
        have h := measureReal_mono (smallCube_subset_coordinate_image hd S b hb)
          (show volume (T '' (S : Set (Space d))) ≠ ∞ from by
            rw [affine_image_eq_translate_linear_image]
            exact (translateBody (T 0) (mapBody f S)).isCompact.measure_lt_top.ne)
        have hcube : volume.real (Icc (0 : Space d) (fun _ => (d : ℝ)⁻¹)) =
            ((d : ℝ)⁻¹) ^ d := by
          first
          | rw [measureReal_def, Real.volume_Icc_pi_toReal
              (show (0 : Space d) ≤ (fun _ => (d : ℝ)⁻¹) from
                fun _ => inv_nonneg.mpr hdpos.le)]
            simp
        rwa [hcube] at h
    have hD : 0 < D := (pow_pos (inv_pos.mpr hdpos) d).trans_le hlow
    let a : ℝ := D ^ (-((d : ℝ)⁻¹))
    have ha : 0 < a := Real.rpow_pos_of_pos hD _
    have hapow : a ^ d = D⁻¹ := by
      first
      | dsimp [a]
        rw [Real.rpow_neg hD.le, inv_pow, Real.rpow_inv_natCast_pow hD.le hd.ne']
    have had : a ≤ d := by
      first
      | apply (pow_le_pow_iff_left₀ ha.le hdpos.le hd.ne').mp
        rw [hapow]
        have hinv := (inv_le_inv₀ hD (pow_pos (inv_pos.mpr hdpos) d)).mpr hlow
        simpa only [inv_pow, inv_inv] using hinv
    let g : Space d →L[ℝ] Space d := a • f
    have hg : |LinearMap.det g.toLinearMap| = 1 := by
      first
      | change |LinearMap.det (a • f.toLinearMap)| = 1
        rw [LinearMap.det_smul, abs_mul, abs_pow, abs_of_pos ha]
        have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
        rw [hdim]
        change a ^ d * D = 1
        rw [hapow, inv_mul_cancel₀ hD.ne']
    obtain ⟨p, hp, hpsum⟩ := (mem_sum_body K (b 0)).mp (hb 0)
    let P : Fin n → Body d := fun i => translateBody (-p i) (K i)
    have hP0 : ∀ i, (0 : Space d) ∈ P i := by
      first
      | intro i
        simpa [P, mem_translateBody] using hp i
    have hPsum : ∑ i, P i = translateBody (-(b 0)) S := by
      first
      | simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib, hpsum, P, S] using
          weightedSum_translate K (fun i => -p i) (fun _ => 1)
    refine ⟨g, p, hg, hp, ?_⟩
    constructor
    · intro i
      exact ⟨0, hP0 i, map_zero g⟩
    · intro y hy
      have hmapsum : (∑ i, mapBody g (P i)) = mapBody g (∑ i, P i) :=
        (map_sum (mapBodyHom g) P Finset.univ).symm
      change y ∈ ∑ i, mapBody g (P i) at hy
      rw [hmapsum] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hPsum] at hu
      change u ∈ translateBody (-(b 0)) S at hu
      rw [mem_translateBody, sub_neg_eq_add] at hu
      have hfu : f u = T (u + b 0) := by
        first
        | change T.linear u = T (u + b 0)
          have h := T.map_vadd (b 0) u
          simpa only [vadd_eq_add, T, droppedCoordinateEquiv_zero_vertex, add_zero] using h.symm
      have hbound : ∀ j, |g u j| ≤ d := by
        first
        | intro j
          have hc : |f u j| ≤ 1 := by
            first
            | rw [hfu]
              exact hcoord (u + b 0) hu j.succ
          change |a * f u j| ≤ d
          rw [abs_mul, abs_of_pos ha]
          exact (mul_le_of_le_one_right ha.le hc).trans had
      exact ⟨fun j => (abs_le.mp (hbound j)).1, fun j => (abs_le.mp (hbound j)).2⟩

end VolumePolynomials
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ExplicitNormalization.lean -/

/- BEGIN SOURCE: VolumePolynomials/EnumeratedQuadraticMatrices.lean -/
section

@[expose] public section

set_option autoImplicit false

/-!
# Executable coefficients of the enumerated quadratic forms

The enumerator returns a rational matrix, using only rational arithmetic and
the finite rational admission test. Its specification is proved equal to the
semantic polynomial enumerator. Thus no polynomial implementation is needed
to compute the actual coefficients of the certificates.
-/

open scoped BigOperators

namespace VolumePolynomials.QuadraticSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Encodable ι]

def enumeratedRationalMatrix (M : Model ι) (k : ℕ) : ι → ι → ℚ :=
  match enumeratedCertificate M k with
  | none => fun _ _ => 0
  | some (a, r, _) => rationalMatrix a r

/-- Exact agreement of the executable rational coefficients and the
homogeneous polynomial used in the mathematical characterization. -/
theorem enumeratedRationalMatrix_eval (M : Model ι) (k : ℕ) (c : Space ι) :
    (∑ i, ∑ j, (enumeratedRationalMatrix M k i j : ℝ) * c i * c j) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) := by
  first
  | cases hd : Encodable.decode (α := CertificateIndex ι) k with
    | none => simp [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm, hd]
    | some z =>
        obtain ⟨a, r, m⟩ := z
        by_cases ha : M.Admitted a r m
        · simp only [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm,
            hd, if_pos ha, eval_rationalForm]
          exact (quadratic_eq_matrix a r c).symm
        · simp [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm, hd, ha]

theorem enumeratedRationalMatrix_encode (M : Model ι)
    (a : ι → ℚ) (r : ℚ) (m : ℕ) (h : M.Admitted a r m) :
    enumeratedRationalMatrix M (Encodable.encode (a, r, m)) = rationalMatrix a r := by
  first
  | rw [enumeratedRationalMatrix, enumeratedCertificate_encode M a r m h]

/-- The complete abstract criterion with a literally executable rational
matrix at every natural-number index. Geometry must supply the model and the
four stated identifications before this is applied to a volume locus. -/
theorem countable_matrix_characterization
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧ ∀ k : ℕ,
      0 ≤ ∑ i, ∑ j, (enumeratedRationalMatrix M k i j : ℝ) * c i * c j := by
  first
  | simp only [enumeratedRationalMatrix_eval]
    exact countable_coefficient_characterization M V hzero hnonneg hnormalize hrealize c

end VolumePolynomials.QuadraticSeparation
end -- closes the original EOF section from source line 4
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/EnumeratedQuadraticMatrices.lean -/

/- BEGIN SOURCE: VolumePolynomials/MainQuadraticCharacterization.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# The rational quadratic characterization

This file connects the certified executable finite nets to the literal
volume-polynomial realization locus. The normalization is the proved affine
normalization of actual convex bodies, and nonnegativity comes from the full
volume-polynomial existence theorem. No geometric or computational premise
is added to the final characterization.
-/

open Set
open scoped BigOperators Pointwise

namespace VolumePolynomials

theorem normalized_mem_explicit_boundedLocus {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} (hc : c ∈ VolumeLocus n d) (hs : 0 < ∑ α, c α) :
    (∑ α, c α)⁻¹ • c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ))) := by
  first
  | have hn := smul_mem_volumeLocus hd hc (inv_nonneg.mpr hs.le)
    obtain ⟨K, hK⟩ := hn
    have hsum : ∑ α, ((∑ β, c β)⁻¹ • c) α = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
    have hvol : bodyVolume (∑ i, K i) = 1 := hK.sum_coefficients.symm.trans hsum
    obtain ⟨g, p, hg, hp, h0, hbox⟩ := explicit_normalization hd K hvol
    let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (K i))
    have hL : Realizes L ((∑ α, c α)⁻¹ • c) :=
      (hK.translate (fun i => -p i)).map_of_abs_det_one g hg
    refine ⟨L, ?_, hL⟩
    intro i
    exact ⟨h0 i, fun x hx => hbox (body_le_sum_of_zero_mem L h0 i hx)⟩

namespace Main

open QuadraticSeparation

/-- At every natural-number index this returns the actual rational
coefficients of a homogeneous quadratic form. -/
def volumeInequalityMatrix (n d k : ℕ) : MultiIndex n d → MultiIndex n d → ℚ :=
  enumeratedRationalMatrix (RationalCoefficientNets.model n d d) k

/-- The equivalent semantic multivariate polynomial. Its matrix coefficients
are given by the executable definition above. -/
noncomputable def volumeInequalityPolynomial (n d k : ℕ) : MvPolynomial (MultiIndex n d) ℚ :=
  enumeratedForm (RationalCoefficientNets.model n d d) k

theorem volumeInequalityPolynomial_homogeneous (n d k : ℕ) :
    (volumeInequalityPolynomial n d k).IsHomogeneous 2 :=
  enumeratedForm_isHomogeneous _ _

theorem volumeInequalityMatrix_eval (n d k : ℕ) (c : Coefficients n d) :
    (∑ α, ∑ β, (volumeInequalityMatrix n d k α β : ℝ) * c α * c β) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) :=
  enumeratedRationalMatrix_eval _ _ (WithLp.toLp 2 c)

/-- Theorem 1.3, in executable rational-matrix form, for every number of
bodies and every positive ambient dimension. Every coefficient, every real
nonnegative Minkowski weight, and every realization is retained. -/
theorem volumeLocus_iff_countableQuadratics (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) :
    c ∈ VolumeLocus n d ↔
      (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
        0 ≤ ∑ α, ∑ β, (volumeInequalityMatrix n d k α β : ℝ) * c α * c β := by
  first
  | let V : Set (QuadraticSeparation.Space (MultiIndex n d)) :=
      {x | WithLp.ofLp x ∈ VolumeLocus n d}
    have hzero : (0 : QuadraticSeparation.Space (MultiIndex n d)) ∈ V :=
      zero_mem_volumeLocus hd
    have hnonneg : ∀ x ∈ V, ∀ α, 0 ≤ x α := by
      intro x hx α
      obtain ⟨K, hK⟩ := hx
      exact hK.coefficients_nonnegative α
    have hnormalize : ∀ x ∈ V, x ≠ 0 →
        normalize x ∈ (RationalCoefficientNets.model n d d).target := by
      intro x hx hx0
      have hs : 0 < total x := total_pos (hnonneg x hx) hx0
      have h := normalized_mem_explicit_boundedLocus hd hx hs
      exact ⟨(total x)⁻¹ • WithLp.ofLp x, h, rfl⟩
    have hrealize : ∀ x, 0 < total x →
        normalize x ∈ (RationalCoefficientNets.model n d d).target → x ∈ V := by
      intro x hs hx
      obtain ⟨y, hy, hyeq⟩ := hx
      have hnorm : WithLp.ofLp (normalize x) ∈ VolumeLocus n d := by
        rw [← hyeq]
        exact boundedVolumeLocus_subset n d _ hy
      have h := smul_mem_volumeLocus hd hnorm hs.le
      change (total x) • ((total x)⁻¹ • WithLp.ofLp x) ∈ VolumeLocus n d at h
      change WithLp.ofLp x ∈ VolumeLocus n d
      simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] using h
    exact countable_matrix_characterization (RationalCoefficientNets.model n d d)
      V hzero hnonneg hnormalize hrealize (WithLp.toLp 2 c)

/-- The original polynomial formulation of the same exact characterization. -/
theorem volumeLocus_iff_enumeratedPolynomials (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) :
    c ∈ VolumeLocus n d ↔
      (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
        0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) := by
  first
  | rw [volumeLocus_iff_countableQuadratics n d hd]
    simp only [volumeInequalityMatrix_eval]

/-- The complete countable homogeneous rational quadratic family in Theorem 1.3.
Its actual rational coefficients are computed by `volumeInequalityMatrix`. -/
theorem countable_characterization (n d : ℕ) (hd : 0 < d) :
    (∀ k, (volumeInequalityPolynomial n d k).IsHomogeneous 2) ∧
      ∀ c : Coefficients n d, c ∈ VolumeLocus n d ↔
        (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) :=
  ⟨volumeInequalityPolynomial_homogeneous n d,
    volumeLocus_iff_enumeratedPolynomials n d hd⟩

end Main
end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MainQuadraticCharacterization.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalRejection.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Finite rational certificates for computable inputs

An input is supplied by rational approximations with a certified error bound.
The finite certificate predicate uses rational arithmetic only. Its soundness
is an interval bound proved for every real vector, and completeness follows
from the strict inequality furnished by the exact volume-locus criterion.
The executable enumeration never tests equality of a real coefficient sum.
-/

open Filter
open scoped BigOperators Topology

namespace VolumePolynomials.RationalCertificates

variable {ι : Type*} [Fintype ι]

def quadraticValue (M : ι → ι → ℚ) (q : ι → ℚ) : ℚ :=
  ∑ i, ∑ j, M i j * q i * q j

def realQuadratic (M : ι → ι → ℚ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j : ℝ) * c i * c j

def quadraticError (M : ι → ι → ℚ) (q : ι → ℚ) (δ : ℚ) : ℚ :=
  ∑ i, ∑ j, |M i j| * δ * (|q i| + |q j| + δ)

theorem product_error {x y a b δ : ℝ} (hδ : 0 ≤ δ)
    (hx : |x - a| ≤ δ) (hy : |y - b| ≤ δ) :
    |x * y - a * b| ≤ δ * (|a| + |b| + δ) := by
  first
  | have hid : x * y - a * b = (x - a) * (y - b) + a * (y - b) + b * (x - a) := by ring
    rw [hid]
    calc
      _ ≤ |(x - a) * (y - b)| + |a * (y - b)| + |b * (x - a)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |x - a| * |y - b| + |a| * |y - b| + |b| * |x - a| := by simp only [abs_mul]
      _ ≤ δ * δ + |a| * δ + |b| * δ := by gcongr
      _ = δ * (|a| + |b| + δ) := by ring

theorem quadratic_interval_bound (M : ι → ι → ℚ) (c : ι → ℝ) (q : ι → ℚ)
    (δ : ℚ) (hδ : 0 ≤ δ) (hq : ∀ i, |c i - (q i : ℝ)| ≤ (δ : ℝ)) :
    |realQuadratic M c - (quadraticValue M q : ℝ)| ≤ (quadraticError M q δ : ℝ) := by
  first
  | simp only [realQuadratic, quadraticValue, quadraticError, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_add, Rat.cast_abs, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [show (M i j : ℝ) * c i * c j - (M i j : ℝ) * (q i : ℝ) * (q j : ℝ) =
      (M i j : ℝ) * (c i * c j - (q i : ℝ) * (q j : ℝ)) by ring, abs_mul]
    have hp := product_error (by exact_mod_cast hδ) (hq i) (hq j)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (abs_nonneg (M i j : ℝ))

def precision (h : ℕ) : ℚ := 1 / ((h : ℚ) + 1)

theorem precision_pos (h : ℕ) : 0 < precision h := by unfold precision; positivity

def IsName (c : ι → ℝ) (a : ℕ → ι → ℚ) : Prop :=
  ∀ h i, |c i - (a h i : ℝ)| ≤ (precision h : ℝ)

theorem precision_tendsto : Tendsto (fun h => (precision h : ℝ)) atTop (𝓝 0) := by
  first
  | simpa only [precision, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem name_tendsto {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a) :
    Tendsto (fun h i => (a h i : ℝ)) atTop (𝓝 c) := by
  first
  | apply tendsto_pi_nhds.mpr
    intro i
    apply (tendsto_iff_dist_tendsto_zero).mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ precision_tendsto
    intro h
    simpa only [Real.dist_eq, abs_sub_comm] using ha h i

theorem quadraticUpper_tendsto (M : ι → ι → ℚ)
    {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a) :
    Tendsto (fun h => ((quadraticValue M (a h) + quadraticError M (a h) (precision h) : ℚ) : ℝ))
      atTop (𝓝 (realQuadratic M c)) := by
  first
  | have hq : Continuous (realQuadratic M) := by unfold realQuadratic; fun_prop
    have he : Continuous (fun z : (ι → ℝ) × ℝ =>
        ∑ i, ∑ j, |(M i j : ℝ)| * z.2 * (|z.1 i| + |z.1 j| + z.2)) := by fun_prop
    have hv := (hq.tendsto c).comp (name_tendsto ha)
    have he' := (he.tendsto (c, 0)).comp ((name_tendsto ha).prodMk_nhds precision_tendsto)
    have h := hv.add he'
    simpa [quadraticValue, quadraticError, realQuadratic] using h

/-- A certificate specifies a negative coordinate or a violated enumerated
quadratic, together with one finite rational input precision. -/
abbrev Certificate (ι : Type*) := (ι × ℕ) ⊕ (ℕ × ℕ)

def Valid (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ) : Certificate ι → Prop
  | .inl (i, h) => a h i + precision h < 0
  | .inr (k, h) => quadraticValue (matrices k) (a h) +
      quadraticError (matrices k) (a h) (precision h) < 0

instance validDecidable (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    (cert : Certificate ι) : Decidable (Valid matrices a cert) := by
  first
  | cases cert <;> unfold Valid <;> infer_instance

theorem valid_sound (matrices : ℕ → ι → ι → ℚ) {c : ι → ℝ} {a : ℕ → ι → ℚ}
    (ha : IsName c a) (cert : Certificate ι) (hcert : Valid matrices a cert) :
    (∃ i, c i < 0) ∨ ∃ k, realQuadratic (matrices k) c < 0 := by
  first
  | cases cert with
    | inl z =>
        obtain ⟨i, h⟩ := z
        apply Or.inl
        refine ⟨i, ?_⟩
        have hq := (abs_le.mp (ha h i)).2
        have hv : (a h i : ℝ) + (precision h : ℝ) < 0 := by exact_mod_cast hcert
        linarith
    | inr z =>
        obtain ⟨k, h⟩ := z
        apply Or.inr
        refine ⟨k, ?_⟩
        have hb := (abs_le.mp (quadratic_interval_bound (matrices k) c (a h) (precision h)
          (precision_pos h).le (ha h))).2
        have hv : (quadraticValue (matrices k) (a h) : ℝ) +
            (quadraticError (matrices k) (a h) (precision h) : ℝ) < 0 := by exact_mod_cast hcert
        linarith

theorem exists_valid_of_strict (matrices : ℕ → ι → ι → ℚ)
    {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a)
    (hbad : (∃ i, c i < 0) ∨ ∃ k, realQuadratic (matrices k) c < 0) :
    ∃ cert, Valid matrices a cert := by
  first
  | rcases hbad with ⟨i, hi⟩ | ⟨k, hk⟩
    · have hlim := ((continuous_apply i).tendsto c |>.comp (name_tendsto ha)).add precision_tendsto
      rw [add_zero] at hlim
      obtain ⟨h, hh⟩ := (hlim.eventually (gt_mem_nhds hi)).exists
      refine ⟨.inl (i, h), ?_⟩
      change a h i + precision h < 0
      change (a h i : ℝ) + (precision h : ℝ) < 0 at hh
      exact_mod_cast hh
    · obtain ⟨h, hh⟩ := ((quadraticUpper_tendsto (matrices k) ha).eventually (gt_mem_nhds hk)).exists
      refine ⟨.inr (k, h), ?_⟩
      change quadraticValue (matrices k) (a h) +
        quadraticError (matrices k) (a h) (precision h) < 0
      exact_mod_cast hh

/-- Exhaustive executable enumeration of all valid finite rational certificates. -/
def enumerate [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    (j : ℕ) : Option (Certificate ι) :=
  match Encodable.decode j with
  | none => none
  | some cert => if Valid matrices a cert then some cert else none

theorem enumerate_sound [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    {j : ℕ} {cert : Certificate ι} (h : enumerate matrices a j = some cert) :
    Valid matrices a cert := by
  first
  | unfold enumerate at h
    split at h
    · contradiction
    · split at h
      · cases h
        assumption
      · contradiction

theorem enumerate_complete [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    {cert : Certificate ι} (h : Valid matrices a cert) :
    enumerate matrices a (Encodable.encode cert) = some cert := by
  first
  | simp [enumerate, Encodable.encodek, h]

end RationalCertificates

namespace Main

/-- Every nonrealizable vector has a strict violated inequality, without
assuming positivity or nonzero total coefficient sum. -/
theorem nonrealizable_strict_inequality (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (hc : c ∉ VolumeLocus n d) :
    (∃ α, c α < 0) ∨ ∃ k, RationalCertificates.realQuadratic (volumeInequalityMatrix n d k) c < 0 := by
  first
  | have h := Iff.mp (not_congr (volumeLocus_iff_countableQuadratics n d hd c)) hc
    by_cases hn : ∀ α, 0 ≤ c α
    · right
      push_neg at h
      exact h hn
    · left
      simpa only [not_forall, not_le] using hn

/-- Rational input names permit a finite rational certificate exactly when
the actual real coefficient vector is nonrealizable. -/
theorem finite_rational_certificate (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔
      ∃ cert, RationalCertificates.Valid (volumeInequalityMatrix n d) a cert := by
  first
  | constructor
    · intro hc
      exact RationalCertificates.exists_valid_of_strict _ ha
        (nonrealizable_strict_inequality n d hd c hc)
    · rintro ⟨cert, hcert⟩ hc
      have hgood := Iff.mp (volumeLocus_iff_countableQuadratics n d hd c) hc
      rcases RationalCertificates.valid_sound _ ha cert hcert with ⟨α, hα⟩ | ⟨k, hk⟩
      · exact (not_lt_of_ge (hgood.1 α)) hα
      · exact (not_lt_of_ge (hgood.2 k)) hk

/-- Dovetailing the finite codes rejects every nonrealizable named input at
some finite index and accepts no false certificate. -/
theorem rational_rejection_terminates (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔ ∃ j cert,
      RationalCertificates.enumerate (volumeInequalityMatrix n d) a j = some cert := by
  first
  | rw [finite_rational_certificate n d hd c a ha]
    constructor
    · rintro ⟨cert, hc⟩
      exact ⟨Encodable.encode cert, cert, RationalCertificates.enumerate_complete _ _ hc⟩
    · rintro ⟨j, cert, hc⟩
      exact ⟨cert, RationalCertificates.enumerate_sound _ _ hc⟩

end Main
end VolumePolynomials
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalRejection.lean -/

/- BEGIN SOURCE: VolumePolynomials/BoundedRealization.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# An explicit box for unnormalized realizations

A bound on the sum of coefficients yields a bound on all realizing bodies
after a volume-preserving normalization and a common dilation. This permits
the rational reconstruction procedure to work with the original coefficients;
it need not decide whether their total is zero or compute its reciprocal.
The proof itself treats the zero case separately.
-/

open Set MeasureTheory Finset
open scoped Pointwise BigOperators

namespace VolumePolynomials

theorem zero_mem_boundedVolumeLocus_box (n d : ℕ) (hd : 0 < d)
    {R : ℝ} (hR : 0 ≤ R) :
    (0 : Coefficients n d) ∈ boundedVolumeLocus n d
      (Icc (fun _ => -R) (fun _ => R)) := by
  first
  | letI : NeZero d := ⟨hd.ne'⟩
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i
      constructor
      · change (0 : Space d) ∈ ({0} : Set (Space d))
        exact Set.mem_singleton 0
      · intro x hx
        change x ∈ ({0} : Set (Space d)) at hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact ⟨fun _ => neg_nonpos.mpr hR, fun _ => hR⟩
    · intro t _
      simp [evaluate, volumeFunction, weightedSum, bodyVolume, Measure.real]
      change 0 = (volume {(0 : Space d)}).toReal
      simp

/-- Every realizable coefficient vector with bounded total admits an actual
tuple in a specified box, including the zero coefficient vector. -/
theorem bounded_realization_of_sum_le {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} (hc : c ∈ VolumeLocus n d)
    {B : ℝ} (hB : 0 ≤ B) (hsB : (∑ α, c α) ≤ B) :
    c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -((d : ℝ) * (B + 1))) (fun _ => (d : ℝ) * (B + 1))) := by
  first
  | obtain ⟨K, hK⟩ := hc
    let s : ℝ := ∑ α, c α
    have hs0 : 0 ≤ s := hK.sum_coefficients_nonneg
    have hR : 0 ≤ (d : ℝ) * (B + 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    by_cases hs : s = 0
    · have hc0 : c = 0 := hK.eq_zero_of_sum_eq_zero hs
      rw [hc0]
      exact zero_mem_boundedVolumeLocus_box n d hd hR
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hmem : s⁻¹ • c ∈ VolumeLocus n d :=
        smul_mem_volumeLocus hd ⟨K, hK⟩ (inv_nonneg.mpr hs0)
      obtain ⟨N, hN⟩ := hmem
      have hsum : ∑ α, (s⁻¹ • c) α = 1 := by
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        exact inv_mul_cancel₀ hs
      have hvol : bodyVolume (∑ i, N i) = 1 := hN.sum_coefficients.symm.trans hsum
      obtain ⟨g, p, hg, hp, hzero, hbox⟩ := explicit_normalization hd N hvol
      let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (N i))
      have hL : Realizes L (s⁻¹ • c) :=
        (hN.translate (fun i => -p i)).map_of_abs_det_one g hg
      have hLbox : ∀ i, (L i : Set (Space d)) ⊆
          Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ)) := by
        intro i x hx
        exact hbox (body_le_sum_of_zero_mem L hzero i hx)
      let r : ℝ := s ^ ((d : ℝ)⁻¹)
      have hr0 : 0 ≤ r := Real.rpow_nonneg hs0 _
      have hrpow : r ^ d = s := Real.rpow_inv_natCast_pow hs0 hd.ne'
      have hrB : r ≤ B + 1 := by
        apply (pow_le_pow_iff_left₀ hr0 (by linarith : 0 ≤ B + 1) hd.ne').mp
        rw [hrpow]
        exact hsB.trans ((le_add_of_nonneg_right zero_le_one).trans
          (le_self_pow₀ (by linarith : 1 ≤ B + 1) hd.ne'))
      have hreal : Realizes (fun i => r • L i) c := by
        have h := hL.dilate hr0
        simpa only [hrpow, smul_smul, mul_inv_cancel₀ hs, one_smul] using h
      refine ⟨fun i => r • L i, ?_, hreal⟩
      intro i
      constructor
      · exact ⟨0, hzero i, smul_zero r⟩
      · rintro x ⟨y, hy, rfl⟩
        have hybox := hLbox i hy
        have habs (j : Fin d) : |r * y j| ≤ (d : ℝ) * (B + 1) := by
          rw [abs_mul, abs_of_nonneg hr0]
          have hcoord : |y j| ≤ d := abs_le.mpr ⟨hybox.1 j, hybox.2 j⟩
          calc
            r * |y j| ≤ r * (d : ℝ) := mul_le_mul_of_nonneg_left hcoord hr0
            _ ≤ (B + 1) * (d : ℝ) := mul_le_mul_of_nonneg_right hrB (Nat.cast_nonneg _)
            _ = (d : ℝ) * (B + 1) := mul_comm _ _
        exact ⟨fun j => (abs_le.mp (habs j)).1, fun j => (abs_le.mp (habs j)).2⟩

theorem bounded_realization_of_sum_le_of_radius_le {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} (hc : c ∈ VolumeLocus n d)
    {B R : ℝ} (hB : 0 ≤ B) (hsB : (∑ α, c α) ≤ B)
    (hR : (d : ℝ) * (B + 1) ≤ R) :
    c ∈ boundedVolumeLocus n d (Icc (fun _ => -R) (fun _ => R)) := by
  first
  | obtain ⟨K, hK, hreal⟩ := bounded_realization_of_sum_le hd hc hB hsB
    refine ⟨K, ?_, hreal⟩
    intro i
    refine ⟨(hK i).1, ?_⟩
    intro x hx
    have h := (hK i).2 hx
    exact ⟨fun j => (neg_le_neg hR).trans (h.1 j), fun j => (h.2 j).trans hR⟩

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BoundedRealization.lean -/

/- BEGIN SOURCE: VolumePolynomials/RationalPolytopeReconstruction.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Reconstruction by finite rational polytope paths

All finite states, adjacency tests, coefficient tests, and selected outputs are
computed from rational data. The geometric interpretation is the actual convex
hull of each output vertex list. Prefix stabilization proves convergence of the
entire output sequence whenever every finite level is nonempty. No rate of
convergence is claimed or used.
-/

open Set Filter Metric
open scoped BigOperators Topology

namespace VolumePolynomials.RationalReconstruction

open RationalHulls RationalCoefficientNets

/-- A wrapper gives finite rational tuples a fixed computable linear order. -/
structure State (n d : ℕ) where
  vertices : Fin n → List (RationalPoint d)
  deriving DecidableEq

instance stateEncodable (n d : ℕ) : Encodable (State n d) :=
  Encodable.ofEquiv (Fin n → List (RationalPoint d))
    { toFun := State.vertices
      invFun := State.mk
      left_inv := fun s => by cases s; rfl
      right_inv := fun _ => rfl }

instance stateLinearOrder (n d : ℕ) : LinearOrder (State n d) :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

instance stateInhabited (n d : ℕ) : Inhabited (State n d) := ⟨⟨fun _ => [0]⟩⟩

noncomputable def stateBodies {n d : ℕ} (s : State n d) : Fin n → Body d :=
  fun i => if h : 0 ∈ s.vertices i then body (s.vertices i) h else 0

theorem stateBodies_eq {n d : ℕ} (s : State n d) (h : ∀ i, 0 ∈ s.vertices i) :
    stateBodies s = fun i => body (s.vertices i) (h i) := by
  first
  | funext i
    simp only [stateBodies, dif_pos (h i)]

def stage (j : ℕ) : ℕ := 2 ^ (j + 2)

def tolerance (j : ℕ) : ℚ := samplingTolerance (stage j)

def dyadic (j : ℕ) : ℚ := (1 / 2) ^ (j + 2)

def edgeRadius (j : ℕ) : ℚ := 3 * dyadic (j + 1)

noncomputable def tailRadius (j : ℕ) : ℝ := 3 * (dyadic j : ℝ)

theorem tolerance_pos (j : ℕ) : 0 < tolerance j := samplingTolerance_pos _

theorem dyadic_pos (j : ℕ) : 0 < dyadic j := by unfold dyadic; positivity

theorem dyadic_succ (j : ℕ) : dyadic (j + 1) = dyadic j / 2 := by
  first
  | unfold dyadic
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, pow_succ]
    ring

theorem tolerance_le_dyadic (j : ℕ) : tolerance j ≤ dyadic j := by
  first
  | have hp : (0 : ℚ) < 2 ^ (j + 2) := by positivity
    have h := one_div_le_one_div_of_le hp (le_add_of_nonneg_right (by norm_num : (0 : ℚ) ≤ 1))
    simpa only [tolerance, samplingTolerance, stage, Nat.cast_pow, Nat.cast_ofNat,
      dyadic, one_div, inv_pow] using h

theorem dyadic_tendsto : Tendsto (fun j => (dyadic j : ℝ)) atTop (𝓝 0) := by
  first
  | have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
      ((1 / 2 : ℝ) ^ 2)
    simpa only [dyadic, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      pow_add, zero_mul] using h

theorem tolerance_tendsto : Tendsto (fun j => (tolerance j : ℝ)) atTop (𝓝 0) := by
  first
  | apply squeeze_zero (fun j => by exact_mod_cast (tolerance_pos j).le)
      (fun j => by exact_mod_cast tolerance_le_dyadic j) dyadic_tendsto

theorem edgeRadius_nonneg (j : ℕ) : 0 ≤ edgeRadius j := by
  first
  | exact mul_nonneg (by norm_num) (dyadic_pos _).le

theorem tailRadius_nonneg (j : ℕ) : 0 ≤ tailRadius j := by
  first
  | unfold tailRadius
    have h : 0 ≤ (dyadic j : ℝ) := by exact_mod_cast (dyadic_pos j).le
    positivity

theorem tailRadius_tendsto : Tendsto tailRadius atTop (𝓝 0) := by
  first
  | change Tendsto (fun j => 3 * (dyadic j : ℝ)) atTop (𝓝 0)
    simpa only [mul_zero] using dyadic_tendsto.const_mul 3

theorem edgeRadius_eq_tail_sub (j : ℕ) :
    (edgeRadius j : ℝ) = tailRadius j - tailRadius (j + 1) := by
  first
  | have h : (dyadic (j + 1) : ℝ) = (dyadic j : ℝ) / 2 := by
      exact_mod_cast dyadic_succ j
    simp only [edgeRadius, Rat.cast_mul, Rat.cast_ofNat, tailRadius]
    linarith

theorem tolerance_add_le_edgeRadius (j : ℕ) :
    tolerance j + tolerance (j + 1) ≤ edgeRadius j := by
  first
  | have h₁ := tolerance_le_dyadic j
    have h₂ := tolerance_le_dyadic (j + 1)
    have h₃ := dyadic_succ j
    unfold edgeRadius
    linarith

def sampledCoefficients {n d : ℕ} (j : ℕ) (s : State n d) : MultiIndex n d → ℚ :=
  approximateCoefficients s.vertices (tolerance j) (tolerance_pos j)

def coefficientTest (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ)
    (j : ℕ) (s : State n d) : Prop :=
  ∀ α, |sampledCoefficients j s α - a (stage j) α| ≤ coordinateBudget n d R * tolerance j

instance coefficientTest_decidable (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ)
    (j : ℕ) (s : State n d) : Decidable (coefficientTest n d R a j s) := by
  first
  | unfold coefficientTest
    infer_instance

/-- A finite list computed by rational inequalities and rational volume search. -/
def states (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ) (j : ℕ) : List (State n d) :=
  ((candidateTuples n d R (resolution n d (stage j))).map State.mk).filter
    (coefficientTest n d R a j)

theorem mem_states {n d R j : ℕ} (a : ℕ → MultiIndex n d → ℚ) (s : State n d) :
    s ∈ states n d R a j ↔
      s.vertices ∈ candidateTuples n d R (resolution n d (stage j)) ∧
      coefficientTest n d R a j s := by
  first
  | cases s
    simp [states]

theorem state_contains_zero {n d R j : ℕ} {a : ℕ → MultiIndex n d → ℚ}
    {s : State n d} (hs : s ∈ states n d R a j) (i : Fin n) : 0 ∈ s.vertices i :=
  (Iff.mp (mem_candidates _) (Iff.mp (mem_candidateTuples _) (Iff.mp (mem_states a s) hs).1 i)).2

theorem state_bounded {n d R j : ℕ} {a : ℕ → MultiIndex n d → ℚ}
    {s : State n d} (hs : s ∈ states n d R a j) (i : Fin n) :
    (stateBodies s i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | rw [stateBodies_eq s (state_contains_zero hs)]
    exact candidate_bounded _ (Iff.mp (mem_candidateTuples _) (Iff.mp (mem_states a s) hs).1 i)

def edge {n d : ℕ} (j : ℕ) (s t : State n d) : Prop :=
  tupleHausdorffTest s.vertices t.vertices (edgeRadius j)

instance edge_decidable {n d : ℕ} (j : ℕ) : DecidableRel (@edge n d j) := by
  first
  | intro s t
    unfold edge
    infer_instance

theorem edge_distance {n d R j : ℕ} {a : ℕ → MultiIndex n d → ℚ}
    {s t : State n d} (hs : s ∈ states n d R a j)
    (ht : t ∈ states n d R a (j + 1)) (hst : edge j s t) :
    dist (stateBodies t) (stateBodies s) ≤ tailRadius j - tailRadius (j + 1) := by
  first
  | rw [← edgeRadius_eq_tail_sub, dist_comm,
      stateBodies_eq s (state_contains_zero hs), stateBodies_eq t (state_contains_zero ht)]
    exact Iff.mp (tupleHausdorffTest_correct _ _ (state_contains_zero hs) (state_contains_zero ht)
      (edgeRadius j) (edgeRadius_nonneg j)) hst

noncomputable def coefficientError (n d R j : ℕ) : ℝ :=
  ((coefficientExtractionBound n d + coordinateBudget n d R + 1 : ℚ) : ℝ) * (tolerance j : ℝ)

theorem coefficientError_nonneg (n d R j : ℕ) : 0 ≤ coefficientError n d R j := by
  first
  | have hE : 0 ≤ (coefficientExtractionBound n d : ℝ) := by
      exact_mod_cast coefficientExtractionBound_nonneg n d
    have hB : 0 ≤ (coordinateBudget n d R : ℝ) := by
      exact_mod_cast (coordinateBudget_pos n d R).le
    have he : 0 ≤ (tolerance j : ℝ) := by exact_mod_cast (tolerance_pos j).le
    simp only [coefficientError, Rat.cast_add, Rat.cast_one]
    positivity

theorem coefficientError_tendsto (n d R : ℕ) :
    Tendsto (coefficientError n d R) atTop (𝓝 0) := by
  first
  | change Tendsto (fun j =>
      (((coefficientExtractionBound n d + coordinateBudget n d R + 1 : ℚ) : ℝ)) *
        (tolerance j : ℝ)) atTop (𝓝 0)
    simpa only [mul_zero] using tolerance_tendsto.const_mul
      (((coefficientExtractionBound n d + coordinateBudget n d R + 1 : ℚ) : ℝ))

theorem state_coefficient_error {n d R j : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    {s : State n d} (hs : s ∈ states n d R a j) :
    dist (coefficientMap (stateBodies s)) c ≤ coefficientError n d R j := by
  first
  | apply (dist_pi_le_iff (coefficientError_nonneg n d R j)).mpr
    intro α
    have hzero := state_contains_zero hs
    have hreal : Realizes (fun i => body (s.vertices i) (hzero i))
        (coefficientMap (stateBodies s)) := by
      rw [← stateBodies_eq s hzero]
      exact coefficientMap_realizes _
    have happ := approximateCoefficients_correct s.vertices hzero hreal
      (tolerance j) (tolerance_pos j) α
    have htest : |(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| ≤
        (coordinateBudget n d R : ℝ) * (tolerance j : ℝ) := by
      exact_mod_cast (Iff.mp (mem_states a s) hs).2 α
    have hname : |c α - (a (stage j) α : ℝ)| ≤ (tolerance j : ℝ) := ha (stage j) α
    have hname' : |(a (stage j) α : ℝ) - c α| ≤ (tolerance j : ℝ) := by
      simpa only [abs_sub_comm] using hname
    change |coefficientMap (stateBodies s) α - c α| ≤ _
    calc
      _ ≤ |coefficientMap (stateBodies s) α - (sampledCoefficients j s α : ℝ)| +
          |(sampledCoefficients j s α : ℝ) - c α| := abs_sub_le _ _ _
      _ ≤ (coefficientExtractionBound n d : ℝ) * (tolerance j : ℝ) +
          (|(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| +
            |(a (stage j) α : ℝ) - c α|) := by
        apply add_le_add
        · simpa only [sampledCoefficients, abs_sub_comm] using happ
        · exact abs_sub_le _ _ _
      _ ≤ (coefficientExtractionBound n d : ℝ) * (tolerance j : ℝ) +
          ((coordinateBudget n d R : ℝ) * (tolerance j : ℝ) + (tolerance j : ℝ)) := by
        exact add_le_add le_rfl (add_le_add htest hname')
      _ = coefficientError n d R j := by
        simp only [coefficientError, Rat.cast_add, Rat.cast_one]
        ring

/-- Every actual bounded realization supplies an accepted state at each scale,
with the stated Hausdorff approximation to that same tuple. -/
theorem exists_state_near {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (K : Fin n → Body d)
    (hK : ∀ i, (0 : Space d) ∈ K i ∧
      (K i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    (hc : Realizes K c) (j : ℕ) :
    ∃ s ∈ states n d R a j, dist K (stateBodies s) ≤ (tolerance j : ℝ) := by
  first
  | classical
    choose L hL hdist using fun i => exists_candidate_near
      (R := R) (k := resolution n d (stage j)) (K i) (hK i).1 (hK i).2
    let s : State n d := ⟨L⟩
    have hzero : ∀ i, 0 ∈ L i := fun i => (Iff.mp (mem_candidates _) (hL i)).2
    let P := fun i => body (L i) (hzero i)
    have hsP : stateBodies s = P := stateBodies_eq s hzero
    have hreal := coefficientMap_realizes P
    have hstate : coefficientTest n d R a j s := by
      intro α
      have hg := hc.coefficient_sub_le_of_dist_le hreal (R : ℚ) (by positivity)
        (fun i => (hK i).2) (fun i => candidate_bounded (L i) (hL i))
        (by positivity : 0 ≤ 1 / ((resolution n d (stage j) : ℝ) + 1))
        (resolution_bounds n d (stage j)).2 hdist α
      have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
        exact_mod_cast coefficientModulus_nonneg n d R
      have hg' := hg.trans (mul_le_mul_of_nonneg_right
        (resolution_bounds n d (stage j)).1 hC)
      have happ := approximateCoefficients_correct L hzero hreal
        (tolerance j) (tolerance_pos j) α
      have hname : |c α - (a (stage j) α : ℝ)| ≤ (tolerance j : ℝ) := ha (stage j) α
      have htri₁ := abs_sub_le ((sampledCoefficients j s α : ℚ) : ℝ)
        (coefficientMap P α) (a (stage j) α : ℝ)
      have htri₂ := abs_sub_le (coefficientMap P α) (c α) (a (stage j) α : ℝ)
      rw [abs_sub_comm (coefficientMap P α) (c α)] at htri₂
      have hbound : |(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| ≤
          (coordinateBudget n d R : ℝ) * (tolerance j : ℝ) := by
        simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
        change |(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| ≤ _
        change |(sampledCoefficients j s α : ℝ) - coefficientMap P α| ≤ _ at happ
        change |c α - coefficientMap P α| ≤ (tolerance j : ℝ) * _ at hg'
        nlinarith
      exact_mod_cast hbound
    refine ⟨s, Iff.mpr (mem_states a s) ⟨Iff.mpr (mem_candidateTuples L) hL, hstate⟩, ?_⟩
    rw [hsP]
    apply (dist_pi_le_iff (by exact_mod_cast (tolerance_pos j).le)).mpr
    intro i
    exact (hdist i).trans (resolution_bounds n d (stage j)).1

/-- A realization supplies a compatible infinite sequence of finite states;
this is a proof of nonemptiness, not a choice used by the program. -/
theorem all_paths_nonempty_of_bounded_realization {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hc : c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))) :
    ∀ h, Nonempty (ComputableFinitePaths.Path (states n d R a) edge h) := by
  first
  | classical
    obtain ⟨K, hK, hreal⟩ := hc
    choose s hs hdist using fun j => exists_state_near ha K hK hreal j
    have he : ∀ j, edge j (s j) (s (j + 1)) := by
      intro j
      apply Iff.mpr (tupleHausdorffTest_correct _ _ (state_contains_zero (hs j))
        (state_contains_zero (hs (j + 1))) (edgeRadius j) (edgeRadius_nonneg j))
      rw [← stateBodies_eq (s j) (state_contains_zero (hs j)),
        ← stateBodies_eq (s (j + 1)) (state_contains_zero (hs (j + 1)))]
      have htri := dist_triangle (stateBodies (s j)) K (stateBodies (s (j + 1)))
      have hnear : dist (stateBodies (s j)) (stateBodies (s (j + 1))) ≤
          (tolerance j : ℝ) + (tolerance (j + 1) : ℝ) := by
        apply htri.trans
        exact add_le_add (by simpa only [dist_comm] using hdist j) (hdist (j + 1))
      exact hnear.trans (by exact_mod_cast tolerance_add_le_edgeRadius j)
    exact ComputableFinitePaths.paths_nonempty_of_sequence _ _ s hs he

/-- Literal finite rational output, including a finite rejection marker. -/
def output (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ) (h : ℕ) : Option (State n d) :=
  ComputableFinitePaths.output (states n d R a) edge h

theorem output_converges_of_all_paths {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hp : ∀ h, Nonempty (ComputableFinitePaths.Path (states n d R a) edge h)) :
    ∃ K : Fin n → Body d,
      Tendsto (fun h => stateBodies ((output n d R a h).getD default)) atTop (𝓝 K) ∧
      Realizes K c := by
  first
  | letI := hp
    obtain ⟨K, hK, hc⟩ := ComputableFinitePaths.output_converges
      (states n d R a) edge stateBodies coefficientMap (continuous_coefficientMap n d) c
      tailRadius (coefficientError n d R) tailRadius_nonneg tailRadius_tendsto
      (coefficientError_tendsto n d R)
      (fun _ _ hs _ ht he => edge_distance hs ht he)
      (fun _ _ hs => state_coefficient_error ha hs)
    refine ⟨K, hK, ?_⟩
    rw [← hc]
    exact coefficientMap_realizes K

/-- Every failure of realization eventually makes a finite path level empty. -/
theorem exists_rejection_of_not_realizable {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hc : c ∉ VolumeLocus n d) : ∃ h, output n d R a h = none := by
  first
  | classical
    by_contra h
    have hp : ∀ h, Nonempty (ComputableFinitePaths.Path (states n d R a) edge h) := by
      intro k
      have hne : ¬IsEmpty (ComputableFinitePaths.Path (states n d R a) edge k) := by
        intro he
        exact h ⟨k, Iff.mpr (ComputableFinitePaths.output_eq_none_iff _ _ k) he⟩
      exact not_isEmpty_iff.mp hne
    obtain ⟨K, _, hK⟩ := output_converges_of_all_paths ha hp
    exact hc ⟨K, hK⟩

/-- A rational bound read at the first input precision. -/
def inputBound {n d : ℕ} (a : ℕ → MultiIndex n d → ℚ) : ℚ :=
  ∑ α, (|a 0 α| + 1)

def inputRadius (n d : ℕ) (a : ℕ → MultiIndex n d → ℚ) : ℕ :=
  ⌈(d : ℚ) * (inputBound a + 1)⌉₊

theorem inputBound_nonneg {n d : ℕ} (a : ℕ → MultiIndex n d → ℚ) : 0 ≤ inputBound a :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem sum_le_inputBound {n d : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a) :
    (∑ α, c α) ≤ (inputBound a : ℝ) := by
  first
  | simp only [inputBound, Rat.cast_sum, Rat.cast_add, Rat.cast_abs, Rat.cast_one]
    apply Finset.sum_le_sum
    intro α _
    have h := (abs_le.mp (ha 0 α)).2
    have ha₀ := le_abs_self (a 0 α : ℝ)
    norm_num [RationalCertificates.precision] at h
    linarith

theorem realizable_mem_input_box {n d : ℕ} (hd : 0 < d) {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hc : c ∈ VolumeLocus n d) :
    c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -(inputRadius n d a : ℝ)) (fun _ => (inputRadius n d a : ℝ))) := by
  first
  | apply bounded_realization_of_sum_le_of_radius_le hd hc
      (by exact_mod_cast inputBound_nonneg a) (sum_le_inputBound ha)
    exact_mod_cast Nat.le_ceil ((d : ℚ) * (inputBound a + 1))

/-- The reconstruction algorithm computes its ambient radius from the input. -/
def reconstruct (n d : ℕ) (a : ℕ → MultiIndex n d → ℚ) (h : ℕ) : Option (State n d) :=
  output n d (inputRadius n d a) a h

theorem reconstruct_ne_none_of_realizable {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} {a : ℕ → MultiIndex n d → ℚ}
    (ha : RationalCertificates.IsName c a) (hc : c ∈ VolumeLocus n d) (h : ℕ) :
    reconstruct n d a h ≠ none := by
  first
  | have hp := all_paths_nonempty_of_bounded_realization ha (realizable_mem_input_box hd ha hc) h
    intro hn
    have hi := Iff.mp (ComputableFinitePaths.output_eq_none_iff _ _ h) hn
    obtain ⟨p⟩ := hp
    exact hi.false p

theorem reconstruction_converges {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} {a : ℕ → MultiIndex n d → ℚ}
    (ha : RationalCertificates.IsName c a) (hc : c ∈ VolumeLocus n d) :
    ∃ K : Fin n → Body d,
      Tendsto (fun h => stateBodies ((reconstruct n d a h).getD default)) atTop (𝓝 K) ∧
      Realizes K c :=
  output_converges_of_all_paths ha
    (all_paths_nonempty_of_bounded_realization ha (realizable_mem_input_box hd ha hc))

theorem reconstruct_some_is_rational_polytope {n d : ℕ}
    (a : ℕ → MultiIndex n d → ℚ) {h : ℕ} {s : State n d}
    (hs : reconstruct n d a h = some s) :
    ∀ i, 0 ∈ s.vertices i ∧ (stateBodies s i : Set (Space d)) = hull (s.vertices i) := by
  first
  | have hm : s ∈ states n d (inputRadius n d a) a h := by
      unfold reconstruct output ComputableFinitePaths.output at hs
      split_ifs at hs with hp
      · have heq : ((ComputableFinitePaths.paths (states n d (inputRadius n d a) a) edge h).min' hp).getD h default = s :=
          Option.some.inj hs
        rw [← heq]
        exact (Iff.mp (ComputableFinitePaths.mem_paths _ _ _ _) (Finset.min'_mem _ _)).2.1
          ⟨h, Nat.lt_succ_self h⟩
    intro i
    refine ⟨state_contains_zero hm i, ?_⟩
    rw [stateBodies_eq s (state_contains_zero hm)]
    rfl

end RationalReconstruction

namespace Main

/-- The entire finite rational polytope output sequence converges to an actual
realization for every realizable named input. Every nonrealizable input is
rejected at a finite height. Every output is a literal rational convex hull. -/
theorem rational_polytope_reconstruction (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) (a : ℕ → MultiIndex n d → ℚ)
    (ha : RationalCertificates.IsName c a) :
    (c ∈ VolumeLocus n d →
      (∀ h, RationalReconstruction.reconstruct n d a h ≠ none) ∧
      ∃ K : Fin n → Body d,
        Tendsto (fun h => RationalReconstruction.stateBodies
          ((RationalReconstruction.reconstruct n d a h).getD default)) atTop (𝓝 K) ∧
        Realizes K c) ∧
    (c ∉ VolumeLocus n d ↔ ∃ h, RationalReconstruction.reconstruct n d a h = none) ∧
    (∀ h s, RationalReconstruction.reconstruct n d a h = some s →
      ∀ i, 0 ∈ s.vertices i ∧
        (RationalReconstruction.stateBodies s i : Set (Space d)) = RationalHulls.hull (s.vertices i)) := by
  first
  | constructor
    · intro hc
      exact ⟨RationalReconstruction.reconstruct_ne_none_of_realizable hd ha hc,
        RationalReconstruction.reconstruction_converges hd ha hc⟩
    constructor
    · constructor
      · exact RationalReconstruction.exists_rejection_of_not_realizable ha
      · rintro ⟨h, hh⟩ hc
        exact RationalReconstruction.reconstruct_ne_none_of_realizable hd ha hc h hh
    · intro h s hs
      exact RationalReconstruction.reconstruct_some_is_rational_polytope a hs

end Main
end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RationalPolytopeReconstruction.lean -/
