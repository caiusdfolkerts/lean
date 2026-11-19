module

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

/- BEGIN SOURCE: VolumePolynomials/Definitions.lean -/
section

@[expose] public section

/-!
# Literal geometric semantics for volume-polynomial coefficients

The carrier is the actual set of points in `ℝᵈ`, with Mathlib's product Lebesgue
measure. `ConvexBody` means nonempty, compact, convex; it does not require
nonempty interior. No mixed-volume axioms or realization hypotheses are built
into the definitions below.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped Pointwise BigOperators ENNReal

namespace VolumePolynomials

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Body (d : ℕ) := ConvexBody (Space d)

/-- Exactly the multi-indices of total degree `d`. The coordinate bound is
redundant mathematically, and makes the finiteness instance explicit. -/
abbrev MultiIndex (n d : ℕ) :=
  {α : Fin n → Fin (d + 1) // ∑ i, (α i : ℕ) = d}

abbrev Coefficients (n d : ℕ) := MultiIndex n d → ℝ

def exponent {n d : ℕ} (α : MultiIndex n d) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α.1 i : ℕ))

@[simp] theorem exponent_apply {n d : ℕ} (α : MultiIndex n d) (i : Fin n) :
    exponent α i = (α.1 i : ℕ) := by simp [exponent]

theorem exponent_injective {n d : ℕ} : Function.Injective (exponent (n := n) (d := d)) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  simpa using congrArg (fun e : Fin n →₀ ℕ => e i) h

def coefficientPolynomial {n d : ℕ} (c : Coefficients n d) : MvPolynomial (Fin n) ℝ :=
  ∑ α, MvPolynomial.monomial (exponent α) (c α)

def evaluate {n d : ℕ} (c : Coefficients n d) (t : Fin n → ℝ) : ℝ :=
  ∑ α, c α * ∏ i, t i ^ (α.1 i : ℕ)

theorem evaluate_eq_polynomial_eval {n d : ℕ} (c : Coefficients n d) (t : Fin n → ℝ) :
    evaluate c t = MvPolynomial.eval t (coefficientPolynomial c) := by
  classical
  simp only [evaluate, coefficientPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [exponent_apply]

@[simp] theorem coefficientPolynomial_coeff {n d : ℕ} (c : Coefficients n d)
    (α : MultiIndex n d) : (coefficientPolynomial c).coeff (exponent α) = c α := by
  classical
  simp [coefficientPolynomial, MvPolynomial.coeff_monomial, exponent_injective.eq_iff]

theorem coefficientPolynomial_injective {n d : ℕ} :
    Function.Injective (coefficientPolynomial (n := n) (d := d)) := by
  intro c e h
  funext α
  simpa using congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff (exponent α)) h

/-- The geometric definition determines every coefficient, even though weights
are only required to be nonnegative. The proof uses the infinite positive
orthant, not a finite-instance check. -/
theorem coefficients_eq_of_evaluate_nonneg {n d : ℕ} {c e : Coefficients n d}
    (h : ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) → evaluate c t = evaluate e t) : c = e := by
  apply coefficientPolynomial_injective
  apply MvPolynomial.funext_set (fun _ => Set.Ici (0 : ℝ)) (fun _ => Set.Ici_infinite 0)
  intro t ht
  simpa only [← evaluate_eq_polynomial_eval] using h t (fun i => ht i (Set.mem_univ i))

@[simp] theorem degree_exponent {n d : ℕ} (α : MultiIndex n d) :
    (exponent α).degree = d := by
  simpa only [Finsupp.degree_eq_sum, exponent_apply] using α.2

theorem coefficientPolynomial_homogeneous {n d : ℕ} (c : Coefficients n d) :
    (coefficientPolynomial c).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum
  intro α _
  exact MvPolynomial.isHomogeneous_monomial (c α) (degree_exponent α)

def weightedSum {n d : ℕ} (K : Fin n → Body d) (t : Fin n → ℝ) : Body d :=
  ∑ i, t i • K i

def bodyVolume {d : ℕ} (K : Body d) : ℝ := volume.real (K : Set (Space d))

def volumeFunction {n d : ℕ} (K : Fin n → Body d) (t : Fin n → ℝ) : ℝ :=
  bodyVolume (weightedSum K t)

/-- The paper's realization condition, with every nonnegative real weight
universally quantified. This does not mean merely matching finitely many samples. -/
def Realizes {n d : ℕ} (K : Fin n → Body d) (c : Coefficients n d) : Prop :=
  ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) → evaluate c t = volumeFunction K t

def VolumeLocus (n d : ℕ) : Set (Coefficients n d) := {c | ∃ K, Realizes K c}

@[simp] theorem mem_volumeLocus {n d : ℕ} {c : Coefficients n d} :
    c ∈ VolumeLocus n d ↔ ∃ K, Realizes K c := Iff.rfl

theorem bodyVolume_nonneg {d : ℕ} (K : Body d) : 0 ≤ bodyVolume K :=
  ENNReal.toReal_nonneg

theorem bodyVolume_finite {d : ℕ} (K : Body d) : volume (K : Set (Space d)) ≠ ∞ :=
  K.isCompact.measure_lt_top.ne

theorem bodyVolume_smul {d : ℕ} (K : Body d) {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (r • K) = r ^ d * bodyVolume K := by
  simp only [bodyVolume, Measure.real, ConvexBody.coe_smul]
  rw [Measure.addHaar_smul_of_nonneg volume hr]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal, pow_nonneg hr]

@[simp] theorem evaluate_one {n d : ℕ} (c : Coefficients n d) :
    evaluate c (fun _ => 1) = ∑ α, c α := by simp [evaluate]

@[simp] theorem weightedSum_one {n d : ℕ} (K : Fin n → Body d) :
    weightedSum K (fun _ => 1) = ∑ i, K i := by simp [weightedSum]

theorem Realizes.sum_coefficients {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) :
    ∑ α, c α = bodyVolume (∑ i, K i) := by
  simpa [volumeFunction] using h (fun _ => 1) (fun _ => zero_le_one)

theorem Realizes.sum_coefficients_nonneg {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) : 0 ≤ ∑ α, c α := by
  rw [h.sum_coefficients]
  exact bodyVolume_nonneg _

theorem Realizes.evaluate_nonneg {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) {t : Fin n → ℝ}
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ evaluate c t := by
  rw [h t ht]
  exact bodyVolume_nonneg _

theorem Realizes.unique {n d : ℕ} {K : Fin n → Body d} {c e : Coefficients n d}
    (hc : Realizes K c) (he : Realizes K e) : c = e := by
  apply coefficients_eq_of_evaluate_nonneg
  intro t ht
  exact (hc t ht).trans (he t ht).symm

end VolumePolynomials
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/Definitions.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlaneCoordinates.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Coordinates for three planes in general position

A nonzero vector on each pairwise intersection gives a basis. The vanishing
of the corresponding coordinate characterizes each original plane exactly.
The construction applies to every real three-dimensional normed space and
does not assume preselected normals or an orthogonal configuration.
-/

open Set Module
open scoped BigOperators

namespace VolumePolynomials.PlaneCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem pair_intersection_nonzero (hdim : finrank ℝ E = 3)
    (P Q : Submodule ℝ E) (hP : finrank ℝ P = 2) (hQ : finrank ℝ Q = 2) :
    P ⊓ Q ≠ ⊥ := by
  first
  | intro hzero
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    have hle := (P ⊔ Q).finrank_le
    rw [hzero, finrank_bot, hP, hQ, add_zero] at h
    rw [hdim] at hle
    omega

theorem exists_coordinate_vectors (hdim : finrank ℝ E = 3)
    (P : Fin 3 → Submodule ℝ E) (hP : ∀ i, finrank ℝ (P i) = 2)
    (htriple : P 0 ⊓ P 1 ⊓ P 2 = ⊥) :
    ∃ v : Fin 3 → E, (∀ i, v i ∉ P i) ∧ ∀ i j, i ≠ j → v i ∈ P j := by
  first
  | obtain ⟨v0, hv0, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (pair_intersection_nonzero hdim (P 1) (P 2) (hP 1) (hP 2))
    obtain ⟨v1, hv1, hn1⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (pair_intersection_nonzero hdim (P 0) (P 2) (hP 0) (hP 2))
    obtain ⟨v2, hv2, hn2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (pair_intersection_nonzero hdim (P 0) (P 1) (hP 0) (hP 1))
    have hnP0 : v0 ∉ P 0 := by
      first
      | intro h0
        have hmem : v0 ∈ P 0 ⊓ P 1 ⊓ P 2 := ⟨⟨h0, hv0.1⟩, hv0.2⟩
        rw [htriple, Submodule.mem_bot] at hmem
        exact hn0 hmem
    have hnP1 : v1 ∉ P 1 := by
      first
      | intro h1
        have hmem : v1 ∈ P 0 ⊓ P 1 ⊓ P 2 := ⟨⟨hv1.1, h1⟩, hv1.2⟩
        rw [htriple, Submodule.mem_bot] at hmem
        exact hn1 hmem
    have hnP2 : v2 ∉ P 2 := by
      first
      | intro h2
        have hmem : v2 ∈ P 0 ⊓ P 1 ⊓ P 2 := ⟨hv2, h2⟩
        rw [htriple, Submodule.mem_bot] at hmem
        exact hn2 hmem
    refine ⟨![v0, v1, v2], ?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · intro i j hij
      fin_cases i
      · fin_cases j
        · exact (hij rfl).elim
        · exact hv0.1
        · exact hv0.2
      · fin_cases j
        · exact hv1.1
        · exact (hij rfl).elim
        · exact hv1.2
      · fin_cases j
        · exact hv2.1
        · exact hv2.2
        · exact (hij rfl).elim

theorem independent_coordinate_vectors (P : Fin 3 → Submodule ℝ E)
    (v : Fin 3 → E) (hnot : ∀ i, v i ∉ P i)
    (hmem : ∀ i j, i ≠ j → v i ∈ P j) : LinearIndependent ℝ v := by
  first
  | classical
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hrest : (∑ j ∈ Finset.univ.erase i, a j • v j) ∈ P i := by
      first
      | apply Submodule.sum_mem
        intro j hj
        exact (P i).smul_mem (a j) (hmem j i (Finset.ne_of_mem_erase hj))
    have hsplit : a i • v i + ∑ j ∈ Finset.univ.erase i, a j • v j = 0 := by
      first
      | rw [Finset.add_sum_erase Finset.univ (fun j => a j • v j) (Finset.mem_univ i)]
        exact ha
    have hai : a i • v i ∈ P i := by
      first
      | have heq : a i • v i = -(∑ j ∈ Finset.univ.erase i, a j • v j) := by
          exact eq_neg_of_add_eq_zero_left hsplit
        rw [heq]
        exact (P i).neg_mem hrest
    by_contra hne
    exact hnot i ((P i).smul_mem_iff hne |>.mp hai)

theorem coordinate_zero_iff_mem (P : Fin 3 → Submodule ℝ E)
    (b : Basis (Fin 3) ℝ E) (hnot : ∀ i, b i ∉ P i)
    (hmem : ∀ i j, i ≠ j → b i ∈ P j) (i : Fin 3) (x : E) :
    b.equivFun x i = 0 ↔ x ∈ P i := by
  first
  | classical
    constructor
    · intro hz
      rw [← b.sum_equivFun x]
      apply Submodule.sum_mem
      intro j _
      by_cases hji : j = i
      · subst j
        rw [hz, zero_smul]
        exact (P i).zero_mem
      · exact (P i).smul_mem _ (hmem j i hji)
    · intro hx
      have hrest : (∑ j ∈ Finset.univ.erase i, b.equivFun x j • b j) ∈ P i := by
        first
        | apply Submodule.sum_mem
          intro j hj
          exact (P i).smul_mem _ (hmem j i (Finset.ne_of_mem_erase hj))
      have hsplit : b.equivFun x i • b i +
          ∑ j ∈ Finset.univ.erase i, b.equivFun x j • b j = x := by
        first
        | rw [Finset.add_sum_erase Finset.univ
            (fun j => b.equivFun x j • b j) (Finset.mem_univ i)]
          exact b.sum_equivFun x
      have hi : b.equivFun x i • b i ∈ P i := by
        first
        | have heq : b.equivFun x i • b i = x -
              ∑ j ∈ Finset.univ.erase i, b.equivFun x j • b j := by
            exact eq_sub_iff_add_eq.mpr hsplit
          rw [heq]
          exact (P i).sub_mem hx hrest
      by_contra hne
      exact hnot i ((P i).smul_mem_iff hne |>.mp hi)

/-- The geometric planes become the three coordinate planes, with both
directions of the membership equivalence retained. -/
theorem exists_plane_coordinates (hdim : finrank ℝ E = 3)
    (P : Fin 3 → Submodule ℝ E) (hP : ∀ i, finrank ℝ (P i) = 2)
    (htriple : P 0 ⊓ P 1 ⊓ P 2 = ⊥) :
    ∃ T : E ≃L[ℝ] Space 3, ∀ i : Fin 3, ∀ x : E, x ∈ P i ↔ T x i = 0 := by
  first
  | obtain ⟨v, hnot, hmem⟩ := exists_coordinate_vectors hdim P hP htriple
    have hli := independent_coordinate_vectors P v hnot hmem
    let b : Basis (Fin 3) ℝ E := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hdim.symm)
    have hb : ∀ i, b i = v i := by
      first
      | intro i
        exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli
          (by simpa using hdim.symm)) i
    refine ⟨b.equivFun.toContinuousLinearEquiv, ?_⟩
    intro i x
    exact (coordinate_zero_iff_mem P b (by simpa only [hb] using hnot)
      (by simpa only [hb] using hmem) i x).symm

end VolumePolynomials.PlaneCoordinates
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlaneCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/Holonomy.lean -/
section


@[expose] public section
noncomputable section

/-!
Algebraic lemmas for Section 7 of Volume polynomials and the Heine–Shephard problem.
This file does not assert the geometric realization theorem or the natural-boundary theorem.
-/

namespace VolumePolynomials.Holonomy

/-- The return map in equation (7.1), expressed in planar coordinates. -/
def returnMap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -p.1 + (2 / 3 : ℝ) * p.2)

/-- The positive quadratic form preserved by the return map, equation (7.9). -/
def preservedForm (p : ℝ × ℝ) : ℝ := p.1 ^ 2 - (2 / 3 : ℝ) * p.1 * p.2 + p.2 ^ 2

theorem preservedForm_eq_squares (p : ℝ × ℝ) :
    preservedForm p = (p.1 - p.2 / 3)^2 + (8 / 9 : ℝ) * p.2^2 := by
  dsimp [preservedForm]
  ring

theorem preservedForm_nonneg (p : ℝ × ℝ) : 0 ≤ preservedForm p := by
  rw [preservedForm_eq_squares]
  positivity

theorem preservedForm_eq_zero_iff (p : ℝ × ℝ) : preservedForm p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rw [preservedForm_eq_squares] at h
    have hy : p.2 = 0 := by nlinarith [sq_nonneg (p.1 - p.2 / 3), sq_nonneg p.2]
    have hx : p.1 = 0 := by simpa [hy] using h
    exact Prod.ext hx hy
  · rintro rfl
    norm_num [preservedForm]

theorem preservedForm_pos {p : ℝ × ℝ} (hp : p ≠ 0) : 0 < preservedForm p := by
  exact lt_of_le_of_ne (preservedForm_nonneg p)
    (fun h => hp ((preservedForm_eq_zero_iff p).mp h.symm))

theorem returnMap_preserves (p : ℝ × ℝ) :
    preservedForm (returnMap p) = preservedForm p := by
  dsimp [returnMap, preservedForm]
  ring

/-- `I - lam M` has positive determinant for every real parameter lam. -/
theorem fixed_translation_determinant_pos (lam : ℝ) :
    0 < 1 - (2 / 3 : ℝ) * lam + lam ^ 2 := by
  nlinarith [sq_nonneg (lam - 1/3)]

/-- Integral recurrence obtained from `3 M`; `b(n+1)` has no factors of three. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * b (n + 1) - 9 * b n

@[simp] theorem b_zero : b 0 = 0 := rfl
@[simp] theorem b_one : b 1 = 1 := rfl
@[simp] theorem b_recurrence (n : ℕ) : b (n + 2) = 2 * b (n + 1) - 9 * b n := rfl

theorem b_mod_three (n : ℕ) : (b (n + 1) : ZMod 3) = (2 : ZMod 3)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, b_recurrence]
      push_cast
      rw [show (9 : ZMod 3) = 0 by decide, zero_mul, sub_zero, ih, pow_succ]
      ring

theorem b_succ_ne_zero (n : ℕ) : b (n + 1) ≠ 0 := by
  intro h
  have hm := b_mod_three n
  rw [h] at hm
  simp only [Int.cast_zero] at hm
  have hunit : IsUnit (2 : ZMod 3) := ⟨⟨2, 2, by decide, by decide⟩, rfl⟩
  exact (hunit.pow n).ne_zero hm.symm

/-- The return map bundled as a continuous linear map. -/
def returnContinuous : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) where
  toFun := returnMap
  map_add' := by
    intro p q
    ext <;> simp only [returnMap, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' := by
    intro c p
    ext <;> simp only [returnMap, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      RingHom.id_apply] <;> ring
  cont := continuous_snd.prodMk
    (continuous_fst.neg.add (continuous_const.mul continuous_snd))

@[simp] theorem returnContinuous_apply (p : ℝ × ℝ) : returnContinuous p = returnMap p := rfl

/-- Orbit of the generating vector e₁ under the actual matrix M. -/
def orbit : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => returnMap (orbit n)

@[simp] theorem orbit_zero : orbit 0 = (1, 0) := rfl
@[simp] theorem orbit_succ (n : ℕ) : orbit (n + 1) = returnMap (orbit n) := rfl

theorem orbit_form (n : ℕ) : preservedForm (orbit n) = 1 := by
  induction n with
  | zero => norm_num [orbit, preservedForm]
  | succ n ih => rw [orbit_succ, returnMap_preserves, ih]

theorem orbit_norm_le (n : ℕ) : ‖orbit n‖ ≤ 2 := by
  have hq := orbit_form n
  have hx : (8/9 : ℝ) * (orbit n).1^2 ≤ preservedForm (orbit n) := by
    dsimp [preservedForm]
    nlinarith [sq_nonneg ((orbit n).2 - (orbit n).1/3)]
  have hy : (8/9 : ℝ) * (orbit n).2^2 ≤ preservedForm (orbit n) := by
    dsimp [preservedForm]
    nlinarith [sq_nonneg ((orbit n).1 - (orbit n).2/3)]
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

theorem orbit_eq_rational (n : ℕ) :
    orbit (n + 1) =
      (-3 * (b n : ℝ) / (3 : ℝ)^n, -(b (n + 1) : ℝ) / (3 : ℝ)^n) := by
  induction n with
  | zero => norm_num [orbit, returnMap, b]
  | succ n ih =>
      rw [orbit_succ, ih]
      ext <;> simp only [returnMap, Prod.fst, Prod.snd]
      · rw [pow_succ]
        field_simp
      · rw [show n + 1 + 1 = n + 2 by omega, b_recurrence, pow_succ]
        push_cast
        field_simp
        ring

theorem orbit_succ_snd_ne_zero (n : ℕ) : (orbit (n + 1)).2 ≠ 0 := by
  rw [orbit_eq_rational]
  dsimp
  exact div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast b_succ_ne_zero n))
    (pow_ne_zero n (by norm_num))

/-- The standard oriented determinant on the plane. -/
def det (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

theorem det_returnMap (p q : ℝ × ℝ) :
    det (returnMap p) (returnMap q) = det p q := by
  dsimp [returnMap, det]
  ring

theorem det_orbit_add (i n : ℕ) : det (orbit i) (orbit (i + n)) = (orbit n).2 := by
  induction i with
  | zero => simp [det, orbit_zero]
  | succ i ih =>
      rw [show i + 1 + n = (i + n) + 1 by omega, orbit_succ, orbit_succ,
        det_returnMap, ih]

theorem det_orbit_ne_zero {i j : ℕ} (hij : i ≠ j) : det (orbit i) (orbit j) ≠ 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    simpa [Nat.add_assoc] using
      (show det (orbit i) (orbit (i + (n + 1))) ≠ 0 by
        rw [det_orbit_add]
        exact orbit_succ_snd_ne_zero n)
  · have hswap : det (orbit j) (orbit i) ≠ 0 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      simpa [Nat.add_assoc] using
        (show det (orbit j) (orbit (j + (n + 1))) ≠ 0 by
          rw [det_orbit_add]
          exact orbit_succ_snd_ne_zero n)
    intro h
    apply hswap
    dsimp [det] at *
    linarith

#print axioms returnMap_preserves
#print axioms b_succ_ne_zero
#print axioms det_orbit_ne_zero

end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 16
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/Holonomy.lean -/

/- BEGIN SOURCE: VolumePolynomials/HolonomyCoordinates.lean -/
section


@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

abbrev Plane := ℝ × ℝ

/-- Coordinate form of projection from the xy-plane to the xz-plane along v. -/
def transport01 : Plane ≃L[ℝ] Plane where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' c p := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk continuous_snd.neg
  continuous_invFun := continuous_fst.prodMk continuous_snd.neg

/-- Coordinate form of projection from the xz-plane to the yz-plane along w. -/
def transport12 : Plane ≃L[ℝ] Plane where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' c p := by ext <;> simp
  continuous_toFun := continuous_fst.neg.prodMk continuous_snd
  continuous_invFun := continuous_fst.neg.prodMk continuous_snd

/-- Coordinate form of projection from the yz-plane to the xy-plane along z. -/
def transport20 : Plane ≃L[ℝ] Plane where
  toFun p := (-p.2, p.1 - (2 / 3 : ℝ) * p.2)
  invFun p := (p.2 - (2 / 3 : ℝ) * p.1, -p.1)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, RingHom.id_apply] <;> ring
  continuous_toFun := continuous_snd.neg.prodMk
    (continuous_fst.sub (continuous_const.mul continuous_snd))
  continuous_invFun := (continuous_snd.sub (continuous_const.mul continuous_fst)).prodMk
    continuous_fst.neg

@[simp] theorem transport01_apply (p : Plane) : transport01 p = (p.1, -p.2) := rfl
@[simp] theorem transport12_apply (p : Plane) : transport12 p = (-p.1, p.2) := rfl
@[simp] theorem transport20_apply (p : Plane) :
    transport20 p = (-p.2, p.1 - (2 / 3 : ℝ) * p.2) := rfl

@[simp] theorem transport_cycle (p : Plane) :
    transport20 (transport12 (transport01 p)) = returnMap p := by
  first
  | ext <;> simp [returnMap] <;> ring

/-- The unique center that absorbs an affine translation in the return equation.
The determinant is positive for every real parameter, not just the contracting
range used in Theorem 1.2. -/
def translationCenter (lam : ℝ) (q : Plane) : Plane :=
  (((1 - (2 / 3 : ℝ) * lam) * q.1 + lam * q.2) /
      (1 - (2 / 3 : ℝ) * lam + lam ^ 2),
    (-lam * q.1 + q.2) / (1 - (2 / 3 : ℝ) * lam + lam ^ 2))

theorem translationCenter_equation (lam : ℝ) (q : Plane) :
    translationCenter lam q - lam • returnMap (translationCenter lam q) = q := by
  first
  | have hd := ne_of_gt (fixed_translation_determinant_pos lam)
    have hd₃ : (3 - lam * 2 + lam ^ 2 * 3 : ℝ) ≠ 0 := by
      have hpos := fixed_translation_determinant_pos lam
      nlinarith
    ext <;> dsimp [translationCenter, returnMap] <;> field_simp [hd, hd₃] <;>
      ring_nf <;> field_simp [hd₃] <;> ring

theorem translationCenter_fixed (lam : ℝ) (q : Plane) :
    translationCenter lam q = q + lam • returnMap (translationCenter lam q) := by
  first
  | exact sub_eq_iff_eq_add.mp (translationCenter_equation lam q)

theorem translationCenter_unique (lam : ℝ) (q c : Plane)
    (hc : c - lam • returnMap c = q) : c = translationCenter lam q := by
  first
  | have hc₁ := congrArg Prod.fst hc
    have hc₂ := congrArg Prod.snd hc
    have ht := translationCenter_equation lam q
    have ht₁ := congrArg Prod.fst ht
    have ht₂ := congrArg Prod.snd ht
    dsimp [returnMap] at hc₁ hc₂ ht₁ ht₂
    have hd := ne_of_gt (fixed_translation_determinant_pos lam)
    have hx : lam * (c.1 - (translationCenter lam q).1) =
        lam ^ 2 * (c.2 - (translationCenter lam q).2) := by
      calc
        _ = lam * (lam * (c.2 - (translationCenter lam q).2)) := by
          congr 1
          linarith
        _ = _ := by ring
    have hy : (1 - (2 / 3 : ℝ) * lam + lam ^ 2) *
        (c.2 - (translationCenter lam q).2) = 0 := by
      nlinarith
    have hy' := (mul_eq_zero.mp hy).resolve_left hd
    have hcy := sub_eq_zero.mp hy'
    apply Prod.ext
    · rw [hcy] at hc₁
      linarith
    · exact hcy

/-- The final determinant distinguishes the four remaining sign patterns. -/
theorem final_calibration_signs {s t : ℝ} (hs : |s| = 1)
    (ht : |t| = (2 / 3 : ℝ)) (hd : |t - s - 1| = (4 / 3 : ℝ)) :
    s = 1 ∧ t = (2 / 3 : ℝ) := by
  first
  | rcases eq_or_eq_neg_of_abs_eq hs with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq ht with rfl | rfl <;>
      norm_num at hd
    all_goals norm_num

/-- Complete scalar sign calibration for Lemma 7.1 at τ = 2/3.

The conclusion supplies two coordinate reflections (the middle coordinate is
fixed) and three independent segment orientations.  The hypotheses are exactly
the absolute coordinates and absolute triple determinant read from the volume
tests.  The finite sign split exhausts all real solutions of those hypotheses.
-/
theorem calibration_signs
    (vy vz wx wy zx zy zz : ℝ)
    (hvy : |vy| = 1) (hvz : |vz| = 1)
    (hwx : |wx| = 1) (hwy : |wy| = 1)
    (hzx : |zx| = 1) (hzy : |zy| = (2 / 3 : ℝ)) (hzz : |zz| = 1)
    (hdet : |-wx * vy * zz + wx * vz * zy - zx * vz * wy| = (4 / 3 : ℝ)) :
    ∃ σ₁ σ₃ rv rw rz : ℝ,
      |σ₁| = 1 ∧ |σ₃| = 1 ∧ |rv| = 1 ∧ |rw| = 1 ∧ |rz| = 1 ∧
      rv * vy = 1 ∧ rv * σ₃ * vz = 1 ∧
      rw * σ₁ * wx = 1 ∧ rw * wy = 1 ∧
      rz * σ₁ * zx = 1 ∧ rz * zy = (2 / 3 : ℝ) ∧ rz * σ₃ * zz = 1 := by
  first
  | refine ⟨wx * wy, vy * vz, vy, wy, vy * vz * zz, ?_⟩
    rcases eq_or_eq_neg_of_abs_eq hvy with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hvz with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hwx with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hwy with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hzx with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hzy with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hzz with rfl | rfl <;>
      norm_num at hdet
    all_goals norm_num


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HolonomyCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/ProjectionCoordinates.lean -/
section


@[expose] public section
noncomputable section

open MeasureTheory

namespace VolumePolynomials.Holonomy

abbrev ThreeSpace := Fin 3 → ℝ

def directionV : ThreeSpace := ![0, 1, 1]
def directionW : ThreeSpace := ![1, 1, 0]
def directionZ : ThreeSpace := ![1, (2 / 3 : ℝ), 1]

/-- Extract one coordinate, retaining the other two in their original order. -/
def coordinateExtract (i : Fin 3) : ThreeSpace ≃ₗ[ℝ] ℝ × Plane where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).toEquiv.trans
    (Equiv.prodCongr (Equiv.refl ℝ) (finTwoArrowEquiv ℝ))
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

@[simp] theorem coordinateExtract_apply (i : Fin 3) (x : ThreeSpace) :
    coordinateExtract i x = (x i, (x (i.succAbove 0), x (i.succAbove 1))) := rfl

theorem coordinateExtract_measurePreserving (i : Fin 3) :
    MeasurePreserving (coordinateExtract i) volume volume := by
  first
  | have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
    have h₂ : MeasurePreserving
        (Prod.map (id : ℝ → ℝ) (@MeasurableEquiv.finTwoArrow ℝ _)) volume volume :=
      (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
    exact h₂.comp h₁

/-- A shear that subtracts a fixed multiple of the extracted coordinate. -/
def projectionShear (u : Plane) : (ℝ × Plane) ≃ₗ[ℝ] ℝ × Plane where
  toFun p := (p.1, p.2 - p.1 • u)
  invFun p := (p.1, p.2 + p.1 • u)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> dsimp <;> ring

@[simp] theorem projectionShear_apply (u : Plane) (p : ℝ × Plane) :
    projectionShear u p = (p.1, p.2 - p.1 • u) := rfl

/-- Product-measure invariance of the shear follows directly from translation
invariance of each planar fiber.  No determinant convention across different
coordinate types is assumed. -/
theorem projectionShear_measurePreserving (u : Plane) :
    MeasurePreserving (projectionShear u) volume volume := by
  first
  | haveI : Measure.IsAddLeftInvariant (volume : Measure Plane) := by
      change Measure.IsAddLeftInvariant ((volume : Measure ℝ).prod (volume : Measure ℝ))
      infer_instance
    change MeasurePreserving (fun p : ℝ × Plane => (p.1, p.2 - p.1 • u)) volume volume
    simp only [Measure.volume_eq_prod ℝ Plane]
    have hm : Measurable
        (Function.uncurry (fun (t : ℝ) (p : Plane) => -(t • u) + p)) := by
      exact ((continuous_fst.smul continuous_const).neg.add continuous_snd).measurable
    have ht : ∀ᵐ t ∂(volume : Measure ℝ),
        Measure.map (fun p : Plane => -(t • u) + p) volume = volume :=
      Filter.Eventually.of_forall (fun t => map_add_left_eq_self (volume : Measure Plane) (-(t • u)))
    simpa only [id_eq, sub_eq_add_neg, add_comm] using
      (MeasurePreserving.id (volume : Measure ℝ)).skew_product hm ht

def projectionFrame (i : Fin 3) (u : Plane) : ThreeSpace ≃L[ℝ] ℝ × Plane :=
  ((coordinateExtract i).trans (projectionShear u)).toContinuousLinearEquiv

@[simp] theorem projectionFrame_apply (i : Fin 3) (u : Plane) (x : ThreeSpace) :
    projectionFrame i u x =
      (x i, (x (i.succAbove 0), x (i.succAbove 1)) - x i • u) := rfl

theorem projectionFrame_measurePreserving (i : Fin 3) (u : Plane) :
    MeasurePreserving (projectionFrame i u) volume volume :=
  (projectionShear_measurePreserving u).comp (coordinateExtract_measurePreserving i)

theorem transport01_measurePreserving : MeasurePreserving transport01 volume volume := by
  first
  | exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem transport12_measurePreserving : MeasurePreserving transport12 volume volume := by
  first
  | exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure ℝ))

@[simp] theorem area_transport01 (A : Set Plane) :
    volume.real (transport01 '' A) = volume.real A := by
  first
  | have h := transport01_measurePreserving.measure_preimage_emb
      transport01.toHomeomorph.measurableEmbedding (transport01 '' A)
    rw [Set.preimage_image_eq A transport01.injective] at h
    simpa only [measureReal_def] using congrArg ENNReal.toReal h.symm

@[simp] theorem area_transport12 (A : Set Plane) :
    volume.real (transport12 '' A) = volume.real A := by
  first
  | have h := transport12_measurePreserving.measure_preimage_emb
      transport12.toHomeomorph.measurableEmbedding (transport12 '' A)
    rw [Set.preimage_image_eq A transport12.injective] at h
    simpa only [measureReal_def] using congrArg ENNReal.toReal h.symm

def frameV : ThreeSpace ≃L[ℝ] ℝ × Plane := projectionFrame 2 (0, 1)
def frameW : ThreeSpace ≃L[ℝ] ℝ × Plane := projectionFrame 1 (1, 0)
def frameZ : ThreeSpace ≃L[ℝ] ℝ × Plane := projectionFrame 2 (1, (2 / 3 : ℝ))

@[simp] theorem frameV_apply (x : ThreeSpace) :
    frameV x = (x 2, (x 0, x 1 - x 2)) := by
  first
  | simp [frameV, projectionFrame_apply,
      show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]

@[simp] theorem frameW_apply (x : ThreeSpace) :
    frameW x = (x 1, (x 0 - x 1, x 2)) := by
  first
  | simp [frameW, projectionFrame_apply]

@[simp] theorem frameZ_apply (x : ThreeSpace) :
    frameZ x = (x 2, (x 0 - x 2, x 1 - (2 / 3 : ℝ) * x 2)) := by
  first
  | simp [frameZ, projectionFrame_apply, mul_comm,
      show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]

theorem frameV_measurePreserving : MeasurePreserving frameV volume volume :=
  projectionFrame_measurePreserving 2 (0, 1)

theorem frameW_measurePreserving : MeasurePreserving frameW volume volume :=
  projectionFrame_measurePreserving 1 (1, 0)

theorem frameZ_measurePreserving : MeasurePreserving frameZ volume volume :=
  projectionFrame_measurePreserving 2 (1, (2 / 3 : ℝ))

@[simp] theorem frameV_direction : frameV directionV = (1, 0) := by
  first
  | norm_num [frameV_apply, directionV]

@[simp] theorem frameW_direction : frameW directionW = (1, 0) := by
  first
  | norm_num [frameW_apply, directionW]

@[simp] theorem frameZ_direction : frameZ directionZ = (1, 0) := by
  first
  | norm_num [frameZ_apply, directionZ]

def projectionV : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp frameV.toContinuousLinearMap

def projectionW : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp frameW.toContinuousLinearMap

def projectionZ : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp frameZ.toContinuousLinearMap

@[simp] theorem projectionV_apply (x : ThreeSpace) :
    projectionV x = (x 0, x 1 - x 2) := by simp [projectionV]

@[simp] theorem projectionW_apply (x : ThreeSpace) :
    projectionW x = (x 0 - x 1, x 2) := by simp [projectionW]

@[simp] theorem projectionZ_apply (x : ThreeSpace) :
    projectionZ x = (x 0 - x 2, x 1 - (2 / 3 : ℝ) * x 2) := by simp [projectionZ]

def embedXY : Plane →L[ℝ] ThreeSpace where
  toFun p := ![p.1, p.2, 0]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  cont := by apply continuous_pi; intro i; fin_cases i <;> fun_prop

def embedXZ : Plane →L[ℝ] ThreeSpace where
  toFun p := ![p.1, 0, p.2]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  cont := by apply continuous_pi; intro i; fin_cases i <;> fun_prop

def embedYZ : Plane →L[ℝ] ThreeSpace where
  toFun p := ![0, p.1, p.2]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  cont := by apply continuous_pi; intro i; fin_cases i <;> fun_prop

@[simp] theorem projectionV_embedXY (p : Plane) : projectionV (embedXY p) = p := by
  first
  | simp [embedXY]

@[simp] theorem projectionV_embedXZ (p : Plane) :
    projectionV (embedXZ p) = transport01 p := by simp [embedXZ]

@[simp] theorem projectionW_embedXZ (p : Plane) : projectionW (embedXZ p) = p := by
  first
  | simp [embedXZ]

@[simp] theorem projectionW_embedYZ (p : Plane) :
    projectionW (embedYZ p) = transport12 p := by simp [embedYZ]

@[simp] theorem projectionZ_embedXY (p : Plane) : projectionZ (embedXY p) = p := by
  first
  | simp [embedXY]

@[simp] theorem projectionZ_embedYZ (p : Plane) :
    projectionZ (embedYZ p) = transport20 p := by simp [embedYZ]

theorem embedXY_injective : Function.Injective embedXY := by
  first
  | intro p q h
    simpa only [projectionV_embedXY] using congrArg projectionV h

theorem embedXZ_injective : Function.Injective embedXZ := by
  first
  | intro p q h
    simpa only [projectionW_embedXZ] using congrArg projectionW h

theorem embedYZ_injective : Function.Injective embedYZ := by
  first
  | intro p q h
    apply transport12.injective
    simpa only [projectionW_embedYZ] using congrArg projectionW h

theorem range_embedXY : Set.range embedXY = {x : ThreeSpace | x 2 = 0} := by
  first
  | ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [embedXY]
    · intro hx
      refine ⟨(x 0, x 1), ?_⟩
      ext i
      fin_cases i <;> simp_all [embedXY]

theorem range_embedXZ : Set.range embedXZ = {x : ThreeSpace | x 1 = 0} := by
  first
  | ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [embedXZ]
    · intro hx
      refine ⟨(x 0, x 2), ?_⟩
      ext i
      fin_cases i <;> simp_all [embedXZ]

theorem range_embedYZ : Set.range embedYZ = {x : ThreeSpace | x 0 = 0} := by
  first
  | ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [embedYZ]
    · intro hx
      refine ⟨(x 1, x 2), ?_⟩
      ext i
      fin_cases i <;> simp_all [embedYZ]


end VolumePolynomials.Holonomy
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 12
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ProjectionCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/CommonLineCoordinates.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Compatible coordinates for planes sharing a line

One nonzero vector on the common line is used in all three planar
parameterizations. Each plane has one fixed transverse vector. Every pair
of planes then has an actual three-dimensional coordinate equivalence,
so its positive Haar factor multiplies both repeated mixed coefficients.
No angular factor or determinant normalization is assumed.
-/

open Set Module
open scoped BigOperators

namespace VolumePolynomials.CommonLineCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

structure Data (P : Fin 3 → Submodule ℝ E) where
  z : E
  z_ne_zero : z ≠ 0
  z_mem : ∀ i, z ∈ P i
  u : Fin 3 → E
  u_mem : ∀ i, u i ∈ P i
  u_not_line : ∀ i, u i ∉ ℝ ∙ z
  plane_span : ∀ i, P i = Submodule.span ℝ ({z, u i} : Set E)

theorem transverse_pair_independent {z u : E} (hz : z ≠ 0) (hu : u ∉ ℝ ∙ z) :
    LinearIndependent ℝ (![u, z] : Fin 2 → E) := by
  first
  | apply linearIndependent_fin2.mpr
    refine ⟨hz, ?_⟩
    intro a ha
    apply hu
    exact Submodule.mem_span_singleton.mpr ⟨a, ha⟩

theorem exists_data (P : Fin 3 → Submodule ℝ E)
    (hP : ∀ i, finrank ℝ (P i) = 2) (hcommon : P 0 ⊓ P 1 ⊓ P 2 ≠ ⊥) :
    Nonempty (Data P) := by
  first
  | classical
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcommon
    have hzP (i : Fin 3) : z ∈ P i := by
      first
      | fin_cases i
        · exact hz.1.1
        · exact hz.1.2
        · exact hz.2
    have hex (i : Fin 3) : ∃ u : E, u ∈ P i ∧ u ∉ ℝ ∙ z := by
      first
      | by_contra! h
        have hle : P i ≤ ℝ ∙ z := h
        have hd := Submodule.finrank_mono hle
        rw [hP i, finrank_span_singleton hz0] at hd
        omega
    choose u hu hnot using hex
    refine ⟨⟨z, hz0, hzP, u, hu, hnot, ?_⟩⟩
    intro i
    have hli := transverse_pair_independent hz0 (hnot i)
    have hrange : Set.range (![u i, z] : Fin 2 → E) = ({z, u i} : Set E) := by
      first
      | ext x
        constructor
        · rintro ⟨j, rfl⟩
          fin_cases j <;> simp
        · rintro (rfl | rfl)
          · exact ⟨1, rfl⟩
          · exact ⟨0, rfl⟩
    have hdim : finrank ℝ (Submodule.span ℝ ({z, u i} : Set E)) = 2 := by
      first
      | rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]
    have hle : Submodule.span ℝ ({z, u i} : Set E) ≤ P i := by
      first
      | apply Submodule.span_le.mpr
        rintro x (rfl | rfl)
        · exact hzP i
        · exact hu i
    exact (Submodule.eq_of_le_of_finrank_eq hle (hdim.trans (hP i).symm)).symm

def Data.planeMap {P : Fin 3 → Submodule ℝ E} (D : Data P) (i : Fin 3) :
    (ℝ × ℝ) →L[ℝ] E where
  toFun p := p.1 • D.z + p.2 • D.u i
  map_add' p q := by
    first
    | change (p.1 + q.1) • D.z + (p.2 + q.2) • D.u i =
        (p.1 • D.z + p.2 • D.u i) + (q.1 • D.z + q.2 • D.u i)
      simp only [add_smul]
      abel
  map_smul' r p := by
    first
    | change (r * p.1) • D.z + (r * p.2) • D.u i = r • (p.1 • D.z + p.2 • D.u i)
      simp only [smul_add, smul_smul]
  cont := by fun_prop

@[simp] theorem Data.planeMap_apply {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (i : Fin 3) (p : ℝ × ℝ) :
    D.planeMap i p = p.1 • D.z + p.2 • D.u i := rfl

theorem Data.planeMap_injective {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (i : Fin 3) : Function.Injective (D.planeMap i) := by
  first
  | intro p q hpq
    have hli := transverse_pair_independent D.z_ne_zero (D.u_not_line i)
    have hsum : (∑ j : Fin 2,
        (![p.2 - q.2, p.1 - q.1] : Fin 2 → ℝ) j • (![D.u i, D.z] : Fin 2 → E) j) = 0 := by
      first
      | simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_smul]
        change p.1 • D.z + p.2 • D.u i = q.1 • D.z + q.2 • D.u i at hpq
        linear_combination (norm := module) hpq
    have heq := Fintype.linearIndependent_iff.mp hli _ hsum
    exact Prod.ext (sub_eq_zero.mp (heq 1)) (sub_eq_zero.mp (heq 0))

theorem Data.range_planeMap {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (i : Fin 3) : Set.range (D.planeMap i) = (P i : Set E) := by
  first
  | ext x
    rw [D.plane_span i]
    change (∃ p, D.planeMap i p = x) ↔ x ∈ Submodule.span ℝ {D.z, D.u i}
    rw [Submodule.mem_span_pair]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.1, p.2, hp⟩
    · rintro ⟨a, b, hab⟩
      exact ⟨(a, b), hab⟩

theorem Data.transverse_not_mem_other {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) : D.u j ∉ P i := by
  first
  | intro hj
    have hji : P j ≤ P i := by
      first
      | rw [D.plane_span j]
        apply Submodule.span_le.mpr
        rintro x (rfl | rfl)
        · exact D.z_mem i
        · exact hj
    have htop : P i = ⊤ := by
      first
      | have h := hpair i j hij
        rwa [sup_eq_left.mpr hji] at h
    have he := hP i
    rw [htop, finrank_top, hdim] at he
    omega

theorem Data.pair_independent {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) :
    LinearIndependent ℝ (![D.z, D.u i, D.u j] : Fin 3 → E) := by
  first
  | rw [Fintype.linearIndependent_iff]
    intro a ha r
    have hsum : a 0 • D.z + a 1 • D.u i + a 2 • D.u j = 0 := by
      first
      | simpa only [Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using ha
    have hterm : a 2 • D.u j ∈ P i := by
      first
      | have he : a 2 • D.u j = -(a 0 • D.z + a 1 • D.u i) := by
          linear_combination (norm := module) hsum
        rw [he]
        exact (P i).neg_mem ((P i).add_mem ((P i).smul_mem _ (D.z_mem i))
          ((P i).smul_mem _ (D.u_mem i)))
    have ha2 : a 2 = 0 := by
      first
      | by_contra hne
        exact D.transverse_not_mem_other hdim hP hpair i j hij ((P i).smul_mem_iff hne |>.mp hterm)
    rw [ha2, zero_smul, add_zero] at hsum
    have hterm1 : a 1 • D.u i ∈ ℝ ∙ D.z := by
      first
      | have he : a 1 • D.u i = -(a 0 • D.z) := eq_neg_of_add_eq_zero_right hsum
        rw [he]
        exact (ℝ ∙ D.z).neg_mem ((ℝ ∙ D.z).smul_mem _ (Submodule.mem_span_singleton_self D.z))
    have ha1 : a 1 = 0 := by
      first
      | by_contra hne
        exact D.u_not_line i ((ℝ ∙ D.z).smul_mem_iff hne |>.mp hterm1)
    rw [ha1, zero_smul, add_zero] at hsum
    have ha0 : a 0 = 0 := (smul_eq_zero.mp hsum).resolve_right D.z_ne_zero
    fin_cases r <;> assumption

def Data.pairBasis {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) : Basis (Fin 3) ℝ E :=
  basisOfLinearIndependentOfCardEqFinrank (D.pair_independent hdim hP hpair i j hij)
    (by simpa only [Fintype.card_fin] using hdim.symm)

theorem Data.pairBasis_apply {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (r : Fin 3) :
    D.pairBasis hdim hP hpair i j hij r = (![D.z, D.u i, D.u j] : Fin 3 → E) r :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
    (D.pair_independent hdim hP hpair i j hij)
    (by simpa only [Fintype.card_fin] using hdim.symm)) r

def Data.pairFrame {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) : E ≃L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (D.pairBasis hdim hP hpair i j hij).equivFun.toContinuousLinearEquiv.trans
    (Holonomy.coordinateExtract 0).toContinuousLinearEquiv

theorem Data.pairFrame_basis {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (r : Fin 3) :
    D.pairFrame hdim hP hpair i j hij (D.pairBasis hdim hP hpair i j hij r) =
      (![(1, (0, 0)), (0, (1, 0)), (0, (0, 1))] : Fin 3 → ℝ × (ℝ × ℝ)) r := by
  first
  | change ((D.pairBasis hdim hP hpair i j hij).equivFun
        (D.pairBasis hdim hP hpair i j hij r) 0,
      ((D.pairBasis hdim hP hpair i j hij).equivFun
        (D.pairBasis hdim hP hpair i j hij r) 1,
       (D.pairBasis hdim hP hpair i j hij).equivFun
        (D.pairBasis hdim hP hpair i j hij r) 2)) = _
    simp only [Basis.equivFun_self]
    fin_cases r <;> norm_num

theorem Data.pairFrame_left {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (p : ℝ × ℝ) :
    D.pairFrame hdim hP hpair i j hij (D.planeMap i p) = (p.1, (p.2, 0)) := by
  first
  | have hz := D.pairFrame_basis hdim hP hpair i j hij 0
    have hi := D.pairFrame_basis hdim hP hpair i j hij 1
    simp only [D.pairBasis_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hz hi
    rw [D.planeMap_apply, map_add, map_smul, map_smul, hz, hi]
    ext <;> simp

theorem Data.pairFrame_right {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (p : ℝ × ℝ) :
    D.pairFrame hdim hP hpair i j hij (D.planeMap j p) = (p.1, (0, p.2)) := by
  first
  | have hz := D.pairFrame_basis hdim hP hpair i j hij 0
    have hj := D.pairFrame_basis hdim hP hpair i j hij 2
    simp only [D.pairBasis_apply, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hz hj
    rw [D.planeMap_apply, map_add, map_smul, map_smul, hz, hj]
    ext <;> simp

end VolumePolynomials.CommonLineCoordinates
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CommonLineCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarExtrusion.lean -/
section


@[expose] public section

/-!
# Extrusion from interval fibers and product Lebesgue measure

The statements here use actual compact convex subsets of `ℝ × E`. The first
factor carries Lebesgue measure and the second carries a locally finite Borel
measure on a second-countable real normed space. The plane is obtained by
`E = ℝ`. No mixed-volume functional or extrusion axiom is assumed. Empty and
lower-dimensional sets are permitted.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal

namespace VolumePolynomials.PlanarExtrusion

variable {E : Type*} [NormedAddCommGroup E]

/-- A horizontal segment of length `t` when `0 ≤ t`. -/
def horizontal (t : ℝ) : Set (ℝ × E) := Icc 0 t ×ˢ {0}

/-- The horizontal fiber at height `y`. -/
def fiber (C : Set (ℝ × E)) (y : E) : Set ℝ := (fun x : ℝ => (x, y)) ⁻¹' C

/-- Projection to the vertical coordinate. -/
def projection (C : Set (ℝ × E)) : Set E := Prod.snd '' C

theorem horizontal_compact (t : ℝ) : IsCompact (horizontal (E := E) t) :=
  isCompact_Icc.prod (isCompact_singleton (x := (0 : E)))

theorem fiber_nonempty_iff (C : Set (ℝ × E)) (y : E) :
    (fiber C y).Nonempty ↔ y ∈ projection C := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x, y), hx, rfl⟩
  · rintro ⟨⟨x, z⟩, hx, hz⟩
    change z = y at hz
    subst z
    exact ⟨x, hx⟩

theorem fiber_compact {C : Set (ℝ × E)} (hC : IsCompact C) (y : E) :
    IsCompact (fiber C y) := by
  have heq : fiber C y = Prod.fst '' (C ∩ {p : ℝ × E | p.2 = y}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, y), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨hab, hb⟩, ha⟩
      change b = y at hb
      change a = x at ha
      subst a
      subst b
      exact hab
  rw [heq]
  exact (hC.inter_right (isClosed_eq continuous_snd continuous_const)).image continuous_fst

theorem fiber_convex [NormedSpace ℝ E] {C : Set (ℝ × E)} (hC : Convex ℝ C) (y : E) :
    Convex ℝ (fiber C y) := by
  intro x hx z hz a b ha hb hab
  have h := hC hx hz ha hb hab
  change (a * x + b * z, y) ∈ C
  convert h using 1
  ext
  · simp [smul_eq_mul]
  · simp [← add_smul, hab]

/-- Minkowski addition by a horizontal segment acts independently in each fiber. -/
theorem fiber_add_horizontal (C : Set (ℝ × E)) (t : ℝ) (y : E) :
    fiber (C + horizontal t) y = fiber C y + Icc 0 t := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hab, ⟨u, v⟩, ⟨hu, hv⟩, heq⟩
    change v = 0 at hv
    subst v
    have hb : b = y := by simpa using congrArg Prod.snd heq
    subst b
    refine ⟨a, hab, u, hu, ?_⟩
    simpa using congrArg Prod.fst heq
  · rintro ⟨a, ha, u, hu, hau⟩
    refine ⟨(a, y), ha, (u, 0), ⟨hu, rfl⟩, ?_⟩
    ext <;> simp [hau]

/-- Exact one-dimensional length increment, including point intervals. -/
theorem length_add_interval {K : Set ℝ} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    volume (K + Icc 0 t) = volume K + ENNReal.ofReal t := by
  have hI : K = Icc (sInf K) (sSup K) :=
    eq_Icc_of_connected_compact ⟨hne, Real.convex_iff_isPreconnected.mp hc⟩ hK
  have hab : sInf K ≤ sSup K := csInf_le_csSup hne hK.bddBelow hK.bddAbove
  rw [hI, Icc_add_Icc hab ht, Real.volume_Icc, Real.volume_Icc]
  simp only [add_zero]
  rw [show sSup K + t - sInf K = (sSup K - sInf K) + t by ring,
    ENNReal.ofReal_add (sub_nonneg.mpr hab) ht]

/-- The measurable indicator records exactly which fibers are nonempty. -/
theorem fiber_measure_increment [NormedSpace ℝ E] {C : Set (ℝ × E)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) (y : E) :
    volume (fiber (C + horizontal t) y) = volume (fiber C y) +
      (projection C).indicator (fun _ => ENNReal.ofReal t) y := by
  classical
  rw [fiber_add_horizontal]
  by_cases hy : y ∈ projection C
  · rw [Set.indicator_of_mem hy]
    exact length_add_interval (fiber_compact hC y) (fiber_convex hc y)
      ((fiber_nonempty_iff C y).mpr hy) ht
  · have hempty : fiber C y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ((fiber_nonempty_iff C y).mp ⟨x, hx⟩)
    simp [hempty, Set.indicator_of_notMem hy]

section Measure

variable [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsLocallyFiniteMeasure (volume : Measure E)]

/-- Product extrusion, proved with actual product measure and Tonelli's theorem. -/
theorem volume_add_horizontal {C : Set (ℝ × E)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) :
    volume (C + horizontal t) = volume C + ENNReal.ofReal t * volume (projection C) := by
  have hsum : IsCompact (C + horizontal t) := hC.add (horizontal_compact t)
  have hp : IsCompact (projection C) := hC.image continuous_snd
  calc
    volume (C + horizontal t) = ∫⁻ y, volume (fiber (C + horizontal t) y) :=
      Measure.prod_apply_symm hsum.measurableSet
    _ = ∫⁻ y, volume (fiber C y) +
        (projection C).indicator (fun _ => ENNReal.ofReal t) y :=
      lintegral_congr (fun y => fiber_measure_increment hC hc ht y)
    _ = (∫⁻ y, volume (fiber C y)) +
        ∫⁻ y, (projection C).indicator (fun _ => ENNReal.ofReal t) y :=
      lintegral_add_left (measurable_measure_prodMk_right hC.measurableSet) _
    _ = volume C + ENNReal.ofReal t * volume (projection C) := by
      rw [lintegral_indicator_const hp.measurableSet]
      congr 1
      exact (Measure.prod_apply_symm hC.measurableSet).symm

/-- The real-valued volume identity, with finiteness justified by compactness. -/
theorem realVolume_add_horizontal {C : Set (ℝ × E)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + horizontal t) = volume.real C + t * volume.real (projection C) := by
  change (volume (C + horizontal t)).toReal =
    (volume C).toReal + t * (volume (projection C)).toReal
  have hp : IsCompact (projection C) := hC.image continuous_snd
  have h := congrArg ENNReal.toReal (volume_add_horizontal hC hc ht)
  rw [ENNReal.toReal_add hC.measure_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp.measure_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht] at h
  exact h

end Measure

/-- The planar specialization of the product extrusion theorem. -/
theorem area_add_horizontal {C : Set (ℝ × ℝ)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + horizontal t) = volume.real C + t * volume.real (projection C) :=
  realVolume_add_horizontal hC hc ht

end VolumePolynomials.PlanarExtrusion
end -- closes the original EOF section from source line 23
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarExtrusion.lean -/

/- BEGIN SOURCE: VolumePolynomials/CrossPlaneVolume.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Volumes of sums in two transverse planes

The two planar sets share the first coordinate axis. A fiber of their sum
is the sum of the two corresponding compact intervals. Tonelli therefore
expresses the three-dimensional volume as area times transverse width in
each of the two directions. All measures here are actual Lebesgue measures.
-/

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace VolumePolynomials.CrossPlaneVolume

open PlanarExtrusion

abbrev Plane := ℝ × ℝ
abbrev ThreeSpace := ℝ × (ℝ × ℝ)

def firstPlane : Plane →L[ℝ] ThreeSpace where
  toFun p := (p.1, (p.2, 0))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def secondPlane : Plane →L[ℝ] ThreeSpace where
  toFun p := (p.1, (0, p.2))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def planeSum (A B : Set Plane) : Set ThreeSpace := firstPlane '' A + secondPlane '' B

theorem planeSum_compact {A B : Set Plane} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (planeSum A B) :=
  (hA.image firstPlane.continuous).add (hB.image secondPlane.continuous)

theorem fiber_planeSum (A B : Set Plane) (y z : ℝ) :
    fiber (planeSum A B) (y, z) = fiber A y + fiber B z := by
  first
  | ext x
    constructor
    · rintro ⟨a, ⟨⟨u, v⟩, huv, rfl⟩, b, ⟨⟨r, s⟩, hrs, rfl⟩, heq⟩
      have hv : v = y := by
        first
        | simpa [firstPlane, secondPlane] using
            (congrArg (fun p : ThreeSpace => p.2.1) heq)
      have hs : s = z := by
        first
        | simpa [firstPlane, secondPlane] using
            (congrArg (fun p : ThreeSpace => p.2.2) heq)
      subst v
      subst s
      exact ⟨u, huv, r, hrs, by
        simpa [firstPlane, secondPlane] using congrArg Prod.fst heq⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      refine ⟨firstPlane (u, y), ⟨(u, y), hu, rfl⟩,
        secondPlane (v, z), ⟨(v, z), hv, rfl⟩, ?_⟩
      ext <;> simp [firstPlane, secondPlane, huv]

theorem length_add_nonempty_intervals {I J : Set ℝ}
    (hI : IsCompact I) (hJ : IsCompact J) (hcI : Convex ℝ I) (hcJ : Convex ℝ J)
    (hneI : I.Nonempty) (hneJ : J.Nonempty) :
    volume (I + J) = volume I + volume J := by
  first
  | have hreprI : I = Icc (sInf I) (sSup I) :=
      eq_Icc_of_connected_compact ⟨hneI, Real.convex_iff_isPreconnected.mp hcI⟩ hI
    have hreprJ : J = Icc (sInf J) (sSup J) :=
      eq_Icc_of_connected_compact ⟨hneJ, Real.convex_iff_isPreconnected.mp hcJ⟩ hJ
    have hi : sInf I ≤ sSup I := csInf_le_csSup hneI hI.bddBelow hI.bddAbove
    have hj : sInf J ≤ sSup J := csInf_le_csSup hneJ hJ.bddBelow hJ.bddAbove
    rw [hreprI, hreprJ, Icc_add_Icc hi hj, Real.volume_Icc, Real.volume_Icc,
      Real.volume_Icc]
    rw [show sSup I + sSup J - (sInf I + sInf J) =
      (sSup I - sInf I) + (sSup J - sInf J) by ring]
    exact ENNReal.ofReal_add (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)

theorem fiber_measure_planeSum {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B)
    (y z : ℝ) :
    volume (fiber (planeSum A B) (y, z)) =
      volume (fiber A y) * (projection B).indicator (fun _ => (1 : ℝ≥0∞)) z +
      (projection A).indicator (fun _ => (1 : ℝ≥0∞)) y * volume (fiber B z) := by
  first
  | classical
    rw [fiber_planeSum]
    by_cases hy : y ∈ projection A
    · by_cases hz : z ∈ projection B
      · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hz, mul_one, one_mul]
        exact length_add_nonempty_intervals (fiber_compact hA y) (fiber_compact hB z)
          (fiber_convex hcA y) (fiber_convex hcB z)
          ((fiber_nonempty_iff A y).mpr hy) ((fiber_nonempty_iff B z).mpr hz)
      · have hempty : fiber B z = ∅ := Set.not_nonempty_iff_eq_empty.mp
          (fun h => hz ((fiber_nonempty_iff B z).mp h))
        simp [hempty, Set.indicator_of_notMem hz]
    · have hempty : fiber A y = ∅ := Set.not_nonempty_iff_eq_empty.mp
        (fun h => hy ((fiber_nonempty_iff A y).mp h))
      simp [hempty, Set.indicator_of_notMem hy]

/-- The exact product-volume identity, including empty and degenerate sets. -/
theorem volume_planeSum {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B) :
    volume (planeSum A B) =
      volume A * volume (projection B) + volume (projection A) * volume B := by
  first
  | have ha : Measurable (fun y => volume (fiber A y)) :=
      measurable_measure_prodMk_right hA.measurableSet
    have hb : Measurable (fun z => volume (fiber B z)) :=
      measurable_measure_prodMk_right hB.measurableSet
    have hpA : IsCompact (projection A) := hA.image continuous_snd
    have hpB : IsCompact (projection B) := hB.image continuous_snd
    have hia : Measurable ((projection A).indicator (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hpA.measurableSet
    have hib : Measurable ((projection B).indicator (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hpB.measurableSet
    have hvolA : (∫⁻ y : ℝ, volume (fiber A y)) = volume A :=
      (Measure.prod_apply_symm hA.measurableSet).symm
    have hvolB : (∫⁻ z : ℝ, volume (fiber B z)) = volume B :=
      (Measure.prod_apply_symm hB.measurableSet).symm
    calc
      volume (planeSum A B) = ∫⁻ p : Plane, volume (fiber (planeSum A B) p) :=
        Measure.prod_apply_symm (planeSum_compact hA hB).measurableSet
      _ = ∫⁻ p : Plane,
          volume (fiber A p.1) * (projection B).indicator (fun _ => (1 : ℝ≥0∞)) p.2 +
          (projection A).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * volume (fiber B p.2) :=
        lintegral_congr (fun p => fiber_measure_planeSum hA hB hcA hcB p.1 p.2)
      _ = (∫⁻ p : Plane,
          volume (fiber A p.1) * (projection B).indicator (fun _ => (1 : ℝ≥0∞)) p.2) +
          ∫⁻ p : Plane,
          (projection A).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * volume (fiber B p.2) :=
        lintegral_add_left ((ha.comp measurable_fst).mul (hib.comp measurable_snd)) _
      _ = (∫⁻ y, volume (fiber A y)) *
          (∫⁻ z, (projection B).indicator (fun _ => (1 : ℝ≥0∞)) z) +
          (∫⁻ y, (projection A).indicator (fun _ => (1 : ℝ≥0∞)) y) *
          ∫⁻ z, volume (fiber B z) := by
        rw [Measure.volume_eq_prod, lintegral_prod_mul ha.aemeasurable hib.aemeasurable,
          lintegral_prod_mul hia.aemeasurable hb.aemeasurable]
      _ = volume A * volume (projection B) + volume (projection A) * volume B := by
        rw [hvolA, hvolB,
          lintegral_indicator_const hpA.measurableSet,
          lintegral_indicator_const hpB.measurableSet, one_mul, one_mul]

theorem realVolume_planeSum {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B) :
    volume.real (planeSum A B) =
      volume.real A * volume.real (projection B) + volume.real (projection A) * volume.real B := by
  first
  | have hpA : IsCompact (projection A) := hA.image continuous_snd
    have hpB : IsCompact (projection B) := hB.image continuous_snd
    have h := congrArg ENNReal.toReal (volume_planeSum hA hB hcA hcB)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hA.measure_ne_top hpB.measure_ne_top)
        (ENNReal.mul_ne_top hpA.measure_ne_top hB.measure_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul] at h
    exact h

theorem projection_smul (r : ℝ) (A : Set Plane) :
    projection (r • A) = r • projection A := by
  first
  | ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, hpy⟩
      exact ⟨q.2, ⟨q, hq, rfl⟩, hpy⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨r • p, ⟨p, hp, rfl⟩, rfl⟩

theorem realVolume_smul_plane (A : Set Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (r • A) = r ^ 2 * volume.real A := by
  first
  | haveI : (volume : Measure Plane).IsAddHaarMeasure := by
      change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
      infer_instance
    simp only [measureReal_def,
      Measure.addHaar_smul_of_nonneg (volume : Measure Plane) hr A,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]
    simp

theorem realVolume_smul_line (A : Set ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (r • A) = r * volume.real A := by
  first
  | simp only [measureReal_def, Measure.addHaar_smul_of_nonneg volume hr A,
      Module.finrank_self, pow_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]

/-- Repeated coefficients for two transverse planar summands, derived from
the volume of every nonnegative weighted sum. -/
theorem realVolume_planeSum_smul {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    volume.real (planeSum (s • A) (t • B)) =
      (volume.real A * volume.real (projection B)) * s ^ 2 * t +
      (volume.real (projection A) * volume.real B) * s * t ^ 2 := by
  first
  | rw [realVolume_planeSum (hA.smul s) (hB.smul t) (hcA.smul s) (hcB.smul t),
      projection_smul, projection_smul,
      realVolume_smul_plane A hs, realVolume_smul_plane B ht,
      realVolume_smul_line (projection A) hs, realVolume_smul_line (projection B) ht]
    ring

/-- The cyclic-product cancellation used when all three planes share a line.
The two angular factors occur once on each side. This algebraic lemma is
kept separate from the geometric task of deriving its six coefficients. -/
theorem cyclic_product
    (A₀ A₁ A₂ w₀ w₁ w₂ a b : ℝ) :
    (A₀ * w₁) * (|a| * A₁ * w₂) * (|b| * w₀ * A₂) =
      (|b| * A₀ * w₂) * (w₀ * A₁) * (|a| * w₁ * A₂) := by
  first
  | ring

end VolumePolynomials.CrossPlaneVolume
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CrossPlaneVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/LinearFrame.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Linear frames adapted to a nonzero functional

The kernel coordinate is literal subtraction of a chosen right inverse.
The volume factor is the positive scalar furnished by uniqueness of actual
additive Haar measures. No determinant or orthonormal-basis normalization is
needed, and no change of measure is left as an unproved hypothesis.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Module

namespace VolumePolynomials.LinearFrame

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def kernelPart (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    E →ₗ[ℝ] LinearMap.ker l.toLinearMap where
  toFun x := ⟨x - l x • v, by simp [map_sub, map_smul, hv]⟩
  map_add' x y := by
    first
    | apply Subtype.ext
      change x + y - l (x + y) • v = (x - l x • v) + (y - l y • v)
      simp only [map_add, add_smul]
      abel
  map_smul' r x := by
    first
    | apply Subtype.ext
      change r • x - l (r • x) • v = r • (x - l x • v)
      simp only [map_smul, smul_eq_mul, smul_sub, smul_smul]

@[simp] theorem kernelPart_coe (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) (x : E) :
    ((kernelPart l v hv x : LinearMap.ker l.toLinearMap) : E) = x - l x • v := rfl

def equiv (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    E ≃ₗ[ℝ] ℝ × LinearMap.ker l.toLinearMap where
  toFun x := (l x, kernelPart l v hv x)
  invFun p := p.1 • v + p.2.val
  left_inv x := by
    first
    | change l x • v + (x - l x • v) = x
      abel
  right_inv p := by
    first
    | apply Prod.ext
      · change l (p.1 • v + p.2.val) = p.1
        simp [map_add, map_smul, hv, p.2.property]
      · apply Subtype.ext
        change p.1 • v + p.2.val - l (p.1 • v + p.2.val) • v = p.2.val
        simp [map_add, map_smul, hv, p.2.property]
  map_add' x y := Prod.ext (map_add l x y) (map_add (kernelPart l v hv) x y)
  map_smul' r x := Prod.ext (map_smul l r x) (map_smul (kernelPart l v hv) r x)

def continuousEquiv [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    E ≃L[ℝ] ℝ × LinearMap.ker l.toLinearMap :=
  (equiv l v hv).toContinuousLinearEquiv

@[simp] theorem continuousEquiv_fst [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) (x : E) :
    (continuousEquiv l v hv x).1 = l x := rfl

@[simp] theorem continuousEquiv_snd [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) (x : E) :
    (continuousEquiv l v hv x).2 = kernelPart l v hv x := rfl

theorem exists_unit_value (l : E →L[ℝ] ℝ) (hl : l ≠ 0) : ∃ v, l v = 1 := by
  first
  | have hn : ∃ x, l x ≠ 0 := by
      by_contra! h
      apply hl
      ext x
      exact h x
    obtain ⟨x, hx⟩ := hn
    exact ⟨(l x)⁻¹ • x, by simp [map_smul, hx]⟩

theorem finrank_kernel_add_one [FiniteDimensional ℝ E]
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    finrank ℝ (LinearMap.ker l.toLinearMap) + 1 = finrank ℝ E := by
  first
  | have h := (equiv l v hv).finrank_eq
    simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using h.symm

section Measure

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]
  [IsAddHaarMeasure (volume : Measure E)] [IsAddHaarMeasure (volume : Measure F)]

/-- Expose the product-volume identity before instance search. This wrapper is
useful with Lean's public module interfaces, which otherwise may leave the
`volume` projection opaque during synthesis. -/
instance volume_product_isAddHaarMeasure :
    IsAddHaarMeasure (volume : Measure (E × F)) := by
  first
  | rw [Measure.volume_eq_prod]
    infer_instance

/-- The scalar multiplying target volume to recover source volume. -/
def volumeFactor (T : E ≃L[ℝ] F) : NNReal :=
  addHaarScalarFactor ((volume : Measure E).map T) (volume : Measure F)

theorem volumeFactor_pos (T : E ≃L[ℝ] F) : 0 < volumeFactor T :=
  addHaarScalarFactor_pos_of_isAddHaarMeasure ((volume : Measure E).map T) (volume : Measure F)

theorem realVolume_eq_factor_mul_image (T : E ≃L[ℝ] F) (S : Set E) :
    volume.real S = (volumeFactor T : ℝ) * volume.real (T '' S) := by
  first
  | have hm : ((volume : Measure E).map T) (T '' S) = volume S := by
      change ((volume : Measure E).map T.toHomeomorph) (T.toHomeomorph '' S) = volume S
      rw [T.toHomeomorph.measurableEmbedding.map_apply,
        Set.preimage_image_eq S T.toHomeomorph.injective]
    have heq : (volume : Measure E).map T = volumeFactor T • (volume : Measure F) :=
      isAddLeftInvariant_eq_smul _ _
    have h := congrArg ENNReal.toReal hm.symm
    rw [heq, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul] at h
    simpa only [ENNReal.coe_toReal, measureReal_def] using h

end Measure
end VolumePolynomials.LinearFrame
end -- closes the original EOF section from source line 22
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/LinearFrame.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyOperations.lean -/
section

@[expose] public section

/-! Actual translations and linear changes of coordinates, including singular maps. -/

noncomputable section
open Set MeasureTheory Finset
open scoped Pointwise BigOperators

namespace VolumePolynomials

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def bodySetHom : ConvexBody E →+ Set E where
  toFun := SetLike.coe
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem body_zero_smul (K : ConvexBody E) : (0 : ℝ) • K = 0 := by
  apply ConvexBody.ext
  exact Set.zero_smul_set K.nonempty

theorem body_add_smul (K : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) • K = a • K + b • K := by
  apply ConvexBody.ext
  exact K.convex.add_smul ha hb

@[simp] theorem coe_sum_body {ι : Type*} (s : Finset ι) (K : ι → ConvexBody E) :
    ((∑ i ∈ s, K i : ConvexBody E) : Set E) = ∑ i ∈ s, (K i : Set E) :=
  map_sum (bodySetHom (E := E)) K s

theorem mem_sum_body {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) (x : E) :
    x ∈ ∑ i, K i ↔ ∃ p : ι → E, (∀ i, p i ∈ K i) ∧ ∑ i, p i = x := by
  change x ∈ (((∑ i, K i : ConvexBody E) : Set E)) ↔ _
  rw [coe_sum_body]
  change x ∈ ∑ i, (K i : Set E) ↔
    ∃ p : ι → E, (∀ i, p i ∈ (K i : Set E)) ∧ ∑ i, p i = x
  simpa only [exists_prop] using Set.mem_fintype_sum (fun i => (K i : Set E)) x

theorem sum_body_mono {ι : Type*} [Fintype ι] {K L : ι → ConvexBody E}
    (h : ∀ i, K i ≤ L i) : (∑ i, K i) ≤ ∑ i, L i := by
  change (((∑ i, K i : ConvexBody E) : Set E)) ⊆ (((∑ i, L i : ConvexBody E) : Set E))
  simp only [coe_sum_body]
  exact Set.finsetSum_subset_finsetSum _ _ _ (fun i _ => h i)

theorem body_le_sum_of_zero_mem {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (h0 : ∀ i, (0 : E) ∈ K i) (i : ι) : K i ≤ ∑ j, K j := by
  classical
  intro x hx
  apply (mem_sum_body K x).mpr
  refine ⟨fun j => if j = i then x else 0, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · simpa [hji] using hx
    · simpa [hji] using h0 j
  · simp

def pointBody (x : E) : ConvexBody E :=
  ⟨{x}, convex_singleton x, isCompact_singleton, singleton_nonempty x⟩

@[simp] theorem coe_pointBody (x : E) : (pointBody x : Set E) = {x} := rfl

def pointBodyHom : E →+ ConvexBody E where
  toFun := pointBody
  map_zero' := rfl
  map_add' x y := ConvexBody.ext (by simp)

@[simp] theorem pointBody_smul (r : ℝ) (x : E) : pointBody (r • x) = r • pointBody x := by
  apply ConvexBody.ext
  simp

def translateBody (v : E) (K : ConvexBody E) : ConvexBody E := pointBody v + K

@[simp] theorem coe_translateBody (v : E) (K : ConvexBody E) :
    (translateBody v K : Set E) = v +ᵥ (K : Set E) := by
  simp [translateBody, Set.singleton_add, ← Set.image_vadd, vadd_eq_add]

theorem mem_translateBody (v : E) (K : ConvexBody E) (x : E) :
    x ∈ translateBody v K ↔ x - v ∈ K := by
  change x ∈ (translateBody v K : Set E) ↔ x - v ∈ (K : Set E)
  rw [coe_translateBody, Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [vadd_eq_add, sub_eq_add_neg, add_comm]

def mapBody (f : E →L[ℝ] F) (K : ConvexBody E) : ConvexBody F where
  carrier := f '' (K : Set E)
  convex' := K.convex.linear_image f.toLinearMap
  isCompact' := K.isCompact.image f.continuous
  nonempty' := K.nonempty.image f

@[simp] theorem coe_mapBody (f : E →L[ℝ] F) (K : ConvexBody E) :
    (mapBody f K : Set F) = f '' (K : Set E) := rfl

theorem mapBody_add (f : E →L[ℝ] F) (K L : ConvexBody E) :
    mapBody f (K + L) = mapBody f K + mapBody f L := by
  apply ConvexBody.ext
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases Set.mem_add.mp hw with ⟨x, hx, y, hy, rfl⟩
    exact Set.mem_add.mpr
      ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, (map_add f x y).symm⟩
  · intro hz
    rcases Set.mem_add.mp hz with ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, Set.mem_add.mpr ⟨x, hx, y, hy, rfl⟩, map_add f x y⟩

def mapBodyHom (f : E →L[ℝ] F) : ConvexBody E →+ ConvexBody F where
  toFun := mapBody f
  map_zero' := ConvexBody.ext (by
    change f '' {(0 : E)} = {(0 : F)}
    simp)
  map_add' := mapBody_add f

theorem mapBody_smul (f : E →L[ℝ] F) (r : ℝ) (K : ConvexBody E) :
    mapBody f (r • K) = r • mapBody f K := by
  apply ConvexBody.ext
  simp only [coe_mapBody, ConvexBody.coe_smul]
  exact Set.image_smul_comm f r (K : Set E) (fun x => f.map_smul r x)

@[simp] theorem mapBody_pointBody (f : E →L[ℝ] F) (v : E) :
    mapBody f (pointBody v) = pointBody (f v) := by
  apply ConvexBody.ext
  simp only [coe_mapBody, coe_pointBody, Set.image_singleton]

theorem mapBody_translate (f : E →L[ℝ] F) (v : E) (K : ConvexBody E) :
    mapBody f (translateBody v K) = translateBody (f v) (mapBody f K) := by
  simp only [translateBody, mapBody_add, mapBody_pointBody]

theorem translateBody_translate (v w : E) (K : ConvexBody E) :
    translateBody v (translateBody w K) = translateBody (v + w) K := by
  change pointBody v + (pointBody w + K) = pointBody (v + w) + K
  have h : pointBody (v + w) = pointBody v + pointBody w :=
    (pointBodyHom (E := E)).map_add v w
  rw [h, add_assoc]

theorem translateBody_add (v w : E) (K L : ConvexBody E) :
    translateBody v K + translateBody w L = translateBody (v + w) (K + L) := by
  change (pointBody v + K) + (pointBody w + L) = pointBody (v + w) + (K + L)
  have h : pointBody (v + w) = pointBody v + pointBody w :=
    (pointBodyHom (E := E)).map_add v w
  rw [h]
  ac_rfl

@[simp] theorem translateBody_zero (K : ConvexBody E) : translateBody 0 K = K :=
  zero_add K

theorem zero_mem_translateBody_neg {K : ConvexBody E} {x : E} (hx : x ∈ K) :
    (0 : E) ∈ translateBody (-x) K := by
  simpa only [mem_translateBody, zero_sub, neg_neg] using hx

end General

theorem mapBody_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E →L[ℝ] F) (g : F →L[ℝ] G) (K : ConvexBody E) :
    mapBody g (mapBody f K) = mapBody (g.comp f) K := by
  apply ConvexBody.ext
  exact Set.image_image g f (K : Set E)

@[simp] theorem weightedSum_single {n d : ℕ} (K : Fin n → Body d)
    (i : Fin n) (a : ℝ) : weightedSum K (Pi.single i a) = a • K i := by
  classical
  simp [weightedSum, Pi.single_apply]

theorem weightedSum_add {n d : ℕ} (K : Fin n → Body d)
    (s t : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i) :
    weightedSum K (s + t) = weightedSum K s + weightedSum K t := by
  simp only [weightedSum, Pi.add_apply,
    body_add_smul _ (hs _) (ht _), Finset.sum_add_distrib]

theorem weightedSum_translate {n d : ℕ} (K : Fin n → Body d)
    (v : Fin n → Space d) (t : Fin n → ℝ) :
    weightedSum (fun i => translateBody (v i) (K i)) t =
      translateBody (∑ i, t i • v i) (weightedSum K t) := by
  simp only [weightedSum, translateBody, smul_add, ← pointBody_smul, Finset.sum_add_distrib]
  congr 1
  exact (map_sum (pointBodyHom (E := Space d)) _ _).symm

@[simp] theorem bodyVolume_translate {d : ℕ} (v : Space d) (K : Body d) :
    bodyVolume (translateBody v K) = bodyVolume K := by
  simp [bodyVolume, Measure.real, measure_vadd]

theorem volumeFunction_translate {n d : ℕ} (K : Fin n → Body d)
    (v : Fin n → Space d) (t : Fin n → ℝ) :
    volumeFunction (fun i => translateBody (v i) (K i)) t = volumeFunction K t := by
  simp only [volumeFunction, weightedSum_translate, bodyVolume_translate]

theorem Realizes.translate {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c) (v : Fin n → Space d) :
    Realizes (fun i => translateBody (v i) (K i)) c := by
  intro t ht
  rw [h t ht]
  simp only [volumeFunction, weightedSum_translate, bodyVolume_translate]

theorem weightedSum_map {n d : ℕ} (f : Space d →L[ℝ] Space d)
    (K : Fin n → Body d) (t : Fin n → ℝ) :
    weightedSum (fun i => mapBody f (K i)) t = mapBody f (weightedSum K t) := by
  simp only [weightedSum]
  rw [show mapBody f (∑ i, t i • K i) = ∑ i, mapBody f (t i • K i) from
    map_sum (mapBodyHom f) _ _]
  simp only [mapBody_smul]

theorem bodyVolume_map {d : ℕ} (f : Space d →L[ℝ] Space d) (K : Body d) :
    bodyVolume (mapBody f K) = |LinearMap.det f.toLinearMap| * bodyVolume K := by
  simp only [bodyVolume, Measure.real, coe_mapBody]
  rw [Measure.addHaar_image_continuousLinearMap]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem volumeFunction_map {n d : ℕ} (f : Space d →L[ℝ] Space d)
    (K : Fin n → Body d) (t : Fin n → ℝ) :
    volumeFunction (fun i => mapBody f (K i)) t =
      |LinearMap.det f.toLinearMap| * volumeFunction K t := by
  simp only [volumeFunction, weightedSum_map, bodyVolume_map]

theorem Realizes.map {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c) (f : Space d →L[ℝ] Space d) :
    Realizes (fun i => mapBody f (K i)) (|LinearMap.det f.toLinearMap| • c) := by
  intro t ht
  simp only [evaluate, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  change |LinearMap.det f.toLinearMap| * evaluate c t = _
  rw [h t ht]
  simp only [volumeFunction, weightedSum_map, bodyVolume_map]

theorem Realizes.map_of_abs_det_one {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) (f : Space d →L[ℝ] Space d)
    (hf : |LinearMap.det f.toLinearMap| = 1) : Realizes (fun i => mapBody f (K i)) c := by
  intro t ht
  rw [h t ht]
  simp only [volumeFunction, weightedSum_map, bodyVolume_map, hf, one_mul]

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodyOperations.lean -/

/- BEGIN SOURCE: VolumePolynomials/ConvexFibersBasic.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Actual compact convex fibers in a product and their set-valued concavity. -/

open Set Metric MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def FiberConcave {U : Type*} [AddCommMonoid U] [Module ℝ U]
    (Z : Set U) (K : U → ConvexBody E) : Prop :=
  Convex ℝ Z ∧ ∀ x ∈ Z, ∀ y ∈ Z, ∀ a b : ℝ,
    0 ≤ a → 0 ≤ b → a + b = 1 →
      ((a • K x + b • K y : ConvexBody E) : Set E) ⊆ K (a • x + b • y)

end VolumePolynomials

namespace VolumePolynomials.ConvexFibers

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def projection (C : ConvexBody (E × U)) : Set U := Prod.snd '' (C : Set (E × U))

def fiberSet (C : ConvexBody (E × U)) (y : U) : Set E := {x | (x, y) ∈ C}

theorem projection_compact (C : ConvexBody (E × U)) : IsCompact (projection C) :=
  C.isCompact.image continuous_snd

theorem projection_convex (C : ConvexBody (E × U)) : Convex ℝ (projection C) :=
  C.convex.linear_image (LinearMap.snd ℝ E U)

theorem fiberSet_nonempty_iff (C : ConvexBody (E × U)) (y : U) :
    (fiberSet C y).Nonempty ↔ y ∈ projection C := by
  first
  | constructor
    · rintro ⟨x, hx⟩
      exact ⟨(x, y), hx, rfl⟩
    · rintro ⟨⟨x, z⟩, hx, hzy⟩
      change z = y at hzy
      subst z
      exact ⟨x, hx⟩

theorem fiberSet_compact (C : ConvexBody (E × U)) (y : U) : IsCompact (fiberSet C y) := by
  first
  | have heq : fiberSet C y = Prod.fst '' ((C : Set (E × U)) ∩ Prod.snd ⁻¹' {y}) := by
      first
      | ext x
        constructor
        · intro hx
          exact ⟨(x, y), ⟨hx, rfl⟩, rfl⟩
        · rintro ⟨⟨u, v⟩, ⟨huv, hv⟩, hux⟩
          have hvy : v = y := hv
          subst v
          change u = x at hux
          subst u
          exact huv
    rw [heq]
    exact (C.isCompact.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

theorem fiberSet_convex (C : ConvexBody (E × U)) (y : U) : Convex ℝ (fiberSet C y) := by
  first
  | intro x hx z hz a b ha hb hab
    have h := C.convex hx hz ha hb hab
    have hy : a • y + b • y = y := by rw [← add_smul, hab, one_smul]
    change (a • x + b • z, y) ∈ (C : Set (E × U))
    simpa only [Prod.smul_mk, Prod.mk_add_mk, hy] using h

def fiberBody (C : ConvexBody (E × U)) (y : U) : ConvexBody E := by
  classical
  exact if h : y ∈ projection C then
    ⟨fiberSet C y, fiberSet_convex C y, fiberSet_compact C y,
      Iff.mpr (fiberSet_nonempty_iff C y) h⟩
  else 0

theorem coe_fiberBody (C : ConvexBody (E × U)) {y : U} (hy : y ∈ projection C) :
    (fiberBody C y : Set E) = fiberSet C y := by
  first
  | rw [fiberBody, dif_pos hy]
    rfl

theorem fiberBody_concave (C : ConvexBody (E × U)) :
    FiberConcave (projection C) (fiberBody C) := by
  first
  | refine ⟨projection_convex C, ?_⟩
    intro y hy z hz a b ha hb hab x hx
    rcases hx with ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    rw [coe_fiberBody C hy] at hu
    rw [coe_fiberBody C hz] at hv
    rw [coe_fiberBody C (projection_convex C hy hz ha hb hab)]
    exact C.convex hu hv ha hb hab

theorem fibers_uniformly_bounded (C : ConvexBody (E × U)) :
    ∃ R : ℝ, ∀ y ∈ projection C,
      (fiberBody C y : Set E) ⊆ closedBall 0 R := by
  first
  | obtain ⟨R, hR⟩ := C.isCompact.isBounded.exists_norm_le
    refine ⟨R, ?_⟩
    intro y hy x hx
    rw [coe_fiberBody C hy] at hx
    have h := (norm_fst_le (x, y)).trans (hR _ hx)
    simpa only [mem_closedBall, dist_zero_right] using h

end VolumePolynomials.ConvexFibers
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ConvexFibersBasic.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiberVolume.lean -/
section


@[expose] public section
noncomputable section

/-!
# Fubini for the higher-dimensional lift

The quotient Jacobian and the actual fiber of the weighted Minkowski sum
are identified explicitly. The lower-dimensional summands are embedded at
quotient coordinate zero. The formula includes scalar zero when the
quotient dimension is positive.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.FiberVolume

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

open ConvexFibers

def embedBody (D : ConvexBody E) : ConvexBody (E × U) :=
  mapBody (ContinuousLinearMap.inl ℝ E U) D

theorem coe_embedBody (D : ConvexBody E) :
    (embedBody (U := U) D : Set (E × U)) = (D : Set E) ×ˢ {0} := by
  first
  | ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
    · rintro ⟨hp, hp0⟩
      exact ⟨p.1, hp, Prod.ext rfl hp0.symm⟩

theorem scaled_sum_fiber (C : ConvexBody (E × U)) (D : ConvexBody E)
    {t : ℝ} (ht : t ≠ 0) (y : U) :
    fiberSet (t • C + embedBody D) (t • y) = t • fiberSet C y + (D : Set E) := by
  first
  | ext x
    constructor
    · rintro ⟨_, ⟨⟨u, z⟩, huz, rfl⟩, _, ⟨v, hv, rfl⟩, hsum⟩
      have hy := congrArg Prod.snd hsum
      change t • z + (0 : U) = t • y at hy
      rw [add_zero] at hy
      have hzy : z = y := (smul_right_injective U ht) hy
      subst z
      exact ⟨t • u, ⟨u, huz, rfl⟩, v, hv, congrArg Prod.fst hsum⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, v, hv, huv⟩
      refine ⟨t • (u, y), ⟨(u, y), hu, rfl⟩,
        (v, 0), ⟨v, hv, rfl⟩, ?_⟩
      exact Prod.ext huv (by simp)

section Measure

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
  [MeasureSpace E] [BorelSpace E] [MeasureSpace U] [BorelSpace U]
  [Measure.IsAddHaarMeasure (volume : Measure E)]
  [Measure.IsAddHaarMeasure (volume : Measure U)]

theorem realVolume_eq_integral_fibers (C : ConvexBody (E × U)) :
    volume.real (C : Set (E × U)) = ∫ y : U, volume.real (fiberSet C y) := by
  first
  | let f : E × U → ℝ := (C : Set (E × U)).indicator (fun _ => 1)
    have hf : Integrable f (volume : Measure (E × U)) :=
      (integrableOn_const C.isCompact.measure_ne_top).integrable_indicator C.isCompact.measurableSet
    have htotal : (∫ p : E × U, f p) = volume.real (C : Set (E × U)) := by
      first
      | rw [integral_indicator C.isCompact.measurableSet, setIntegral_const]
        simp only [smul_eq_mul, mul_one]
    have hfiber (y : U) : (∫ x : E, f (x, y)) = volume.real (fiberSet C y) := by
      first
      | change (∫ x : E, (fiberSet C y).indicator (fun _ => (1 : ℝ)) x) = _
        rw [integral_indicator (fiberSet_compact C y).measurableSet, setIntegral_const]
        simp only [smul_eq_mul, mul_one]
    have h := integral_prod_symm f (by simpa only [Measure.volume_eq_prod] using hf)
    simpa only [← Measure.volume_eq_prod, htotal, hfiber] using h

theorem integrable_fiber_realVolume (C : ConvexBody (E × U)) :
    Integrable (fun y : U => volume.real (fiberSet C y)) := by
  first
  | let f : E × U → ℝ := (C : Set (E × U)).indicator (fun _ => 1)
    have hf : Integrable f ((volume : Measure E).prod (volume : Measure U)) := by
      rw [← Measure.volume_eq_prod]
      exact (integrableOn_const C.isCompact.measure_ne_top).integrable_indicator C.isCompact.measurableSet
    have hfiber (y : U) : (∫ x : E, f (x, y)) = volume.real (fiberSet C y) := by
      change (∫ x : E, (fiberSet C y).indicator (fun _ => (1 : ℝ)) x) = _
      rw [integral_indicator (fiberSet_compact C y).measurableSet, setIntegral_const]
      simp only [smul_eq_mul, mul_one]
    simpa only [hfiber] using hf.integral_prod_right

theorem scaled_sum_fiber_volume (C : ConvexBody (E × U)) (D : ConvexBody E)
    {t : ℝ} (ht : t ≠ 0) (y : U) :
    volume.real (fiberSet (t • C + embedBody D) (t • y)) =
      (projection C).indicator (fun z => volume.real
        ((t • fiberBody C z + D : ConvexBody E) : Set E)) y := by
  first
  | classical
    rw [scaled_sum_fiber C D ht y]
    by_cases hy : y ∈ projection C
    · rw [Set.indicator_of_mem hy]
      simp only [ConvexBody.coe_add, ConvexBody.coe_smul, coe_fiberBody C hy]
    · rw [Set.indicator_of_notMem hy]
      have he : fiberSet C y = ∅ := not_nonempty_iff_eq_empty.mp
        (fun h => hy ((fiberSet_nonempty_iff C y).mp h))
      simp only [he, Set.smul_set_empty, Set.empty_add, measureReal_empty]

/-- Formula (6.4), with all lower-dimensional summands collected into `D`.
This version is independent of any polynomial coefficient calculation. -/
theorem realVolume_scaled_sum_of_pos (C : ConvexBody (E × U)) (D : ConvexBody E)
    {t : ℝ} (ht : 0 < t) :
    volume.real ((t • C + embedBody D : ConvexBody (E × U)) : Set (E × U)) =
      t ^ finrank ℝ U * ∫ y in projection C,
        volume.real ((t • fiberBody C y + D : ConvexBody E) : Set E) := by
  first
  | let f : U → ℝ := fun y => volume.real (fiberSet (t • C + embedBody D) y)
    have hchange := Measure.integral_comp_smul_of_nonneg volume f t (hR := ht.le)
    have hleft : (∫ y : U, f (t • y)) =
        ∫ y in projection C, volume.real ((t • fiberBody C y + D : ConvexBody E) : Set E) := by
      first
      | simp only [f, scaled_sum_fiber_volume C D ht.ne']
        exact integral_indicator (projection_compact C).measurableSet
    rw [hleft, smul_eq_mul] at hchange
    rw [realVolume_eq_integral_fibers]
    change (∫ y, f y) = t ^ finrank ℝ U * _
    rw [hchange, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]

theorem realVolume_embedBody [Nontrivial U] (D : ConvexBody E) :
    volume.real (embedBody (U := U) D : Set (E × U)) = 0 := by
  first
  | rw [coe_embedBody, measureReal_def, Measure.volume_eq_prod, Measure.prod_prod]
    simp only [measure_singleton, mul_zero, ENNReal.toReal_zero]

theorem realVolume_scaled_sum (hk : 0 < finrank ℝ U)
    (C : ConvexBody (E × U)) (D : ConvexBody E) {t : ℝ} (ht : 0 ≤ t) :
    volume.real ((t • C + embedBody D : ConvexBody (E × U)) : Set (E × U)) =
      t ^ finrank ℝ U * ∫ y in projection C,
        volume.real ((t • fiberBody C y + D : ConvexBody E) : Set E) := by
  first
  | rcases ht.eq_or_lt with rfl | ht
    · letI : Nontrivial U := finrank_pos_iff.mp hk
      have hz : ((0 : ℝ) • C + embedBody D : ConvexBody (E × U)) = embedBody D := by
        rw [body_zero_smul]
        exact zero_add (embedBody (U := U) D)
      rw [hz, realVolume_embedBody, zero_pow hk.ne', zero_mul]
    · exact realVolume_scaled_sum_of_pos C D ht

end Measure

end VolumePolynomials.FiberVolume
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiberVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyContinuity.lean -/
section

@[expose] public section

/-!
# Lebesgue-volume continuity for actual convex bodies

The proof uses separating linear functionals to show that Hausdorff convergence
preserves membership of every interior point eventually. Exterior points are
handled by positive distance. The exceptional frontier has Haar measure zero,
so dominated convergence proves continuity, including lower-dimensional limits.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology Pointwise

namespace VolumePolynomials
namespace BodySupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def support (K : ConvexBody E) (f : E →L[ℝ] ℝ) : ℝ := sSup (f '' (K : Set E))

theorem le_support (K : ConvexBody E) (f : E →L[ℝ] ℝ) {x : E} (hx : x ∈ K) :
    f x ≤ support K f :=
  le_csSup (K.isCompact.image f.continuous).bddAbove (mem_image_of_mem f hx)

theorem support_le (K : ConvexBody E) (f : E →L[ℝ] ℝ) {a : ℝ}
    (ha : ∀ x ∈ K, f x ≤ a) : support K f ≤ a :=
  csSup_le (K.nonempty.image f) (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)

theorem exists_support (K : ConvexBody E) (f : E →L[ℝ] ℝ) :
    ∃ x ∈ K, f x = support K f :=
  (K.isCompact.image f.continuous).sSup_mem (K.nonempty.image f)

theorem mem_iff_le_support (K : ConvexBody E) {x : E} :
    x ∈ K ↔ ∀ f : E →L[ℝ] ℝ, f x ≤ support K f := by
  refine ⟨fun hx f => le_support K f hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point K.convex K.isClosed hx
  exact (hux.trans_le ((h f).trans (support_le K f fun y hy => (hu y hy).le))).false

theorem support_le_add_norm_mul_dist (K L : ConvexBody E) (f : E →L[ℝ] ℝ) :
    support K f ≤ support L f + ‖f‖ * dist K L := by
  obtain ⟨x, hx, hfx⟩ := exists_support K f
  obtain ⟨y, hy, hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  have hd : dist x y ≤ dist K L := by
    rw [← hxy]
    exact infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top
  have hf : f x - f y ≤ ‖f‖ * dist x y := by
    calc
      f x - f y = f (x - y) := (map_sub f x y).symm
      _ ≤ ‖f (x - y)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖x - y‖ := f.le_opNorm _
      _ = ‖f‖ * dist x y := by rw [dist_eq_norm]
  have hfy := le_support L f hy
  have hmul := mul_le_mul_of_nonneg_left hd (norm_nonneg f)
  rw [← hfx]
  linarith

theorem support_margin_of_closedBall_subset (K : ConvexBody E) {x : E} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ (K : Set E)) (f : E →L[ℝ] ℝ) :
    f x + r * ‖f‖ ≤ support K f := by
  have hnorm : ‖f‖ ≤ (support K f - f x) / r := by
    apply ContinuousLinearMap.opNorm_bound_of_ball_bound hr (support K f - f x) f
    intro z hz
    have hzp : x + z ∈ K := hball (by
      simpa [mem_closedBall, dist_eq_norm] using hz)
    have hzm : x - z ∈ K := hball (by
      simpa [mem_closedBall, dist_eq_norm] using hz)
    have hp := le_support K f hzp
    have hm := le_support K f hzm
    rw [map_add] at hp
    rw [map_sub] at hm
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hm := (le_div_iff₀ hr).mp hnorm
  nlinarith

theorem mem_of_dist_lt_of_closedBall_subset (K L : ConvexBody E) {x : E} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ (K : Set E)) (hKL : dist K L < r) :
    x ∈ L := by
  apply (mem_iff_le_support L).mpr
  intro f
  have h1 := support_margin_of_closedBall_subset K hr hball f
  have h2 := support_le_add_norm_mul_dist K L f
  have h3 := mul_le_mul_of_nonneg_left hKL.le (norm_nonneg f)
  nlinarith

theorem eventually_mem_of_mem_interior {ι : Type*} {l : Filter ι}
    {K : ConvexBody E} {L : ι → ConvexBody E} (hL : Tendsto L l (𝓝 K))
    {x : E} (hx : x ∈ interior (K : Set E)) : ∀ᶠ i in l, x ∈ L i := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hevent : ∀ᶠ i in l, dist K (L i) < r := by
    have := hL.eventually (Metric.ball_mem_nhds K hr)
    simpa only [mem_ball, dist_comm] using this
  filter_upwards [hevent] with i hi
  exact mem_of_dist_lt_of_closedBall_subset K (L i) hr hball hi

theorem eventually_notMem_of_notMem {ι : Type*} {l : Filter ι}
    {K : ConvexBody E} {L : ι → ConvexBody E} (hL : Tendsto L l (𝓝 K))
    {x : E} (hx : x ∉ K) : ∀ᶠ i in l, x ∉ L i := by
  have hr : 0 < infDist x (K : Set E) :=
    (K.isClosed.notMem_iff_infDist_pos K.nonempty).mp hx
  have hevent := hL.eventually (Metric.ball_mem_nhds K hr)
  filter_upwards [hevent] with i hi hxi
  have hd : infDist x (K : Set E) ≤ dist (L i) K :=
    infDist_le_hausdorffDist_of_mem hxi ConvexBody.hausdorffEDist_ne_top
  exact (not_lt_of_ge hd) hi

end BodySupport

section MeasureContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem tendsto_convexBody_measure {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {K : ConvexBody E} {L : ι → ConvexBody E} (hL : Tendsto L l (𝓝 K)) :
    Tendsto (fun i => μ (L i : Set E)) l (𝓝 (μ (K : Set E))) := by
  apply tendsto_measure_of_ae_tendsto_indicator l K.isCompact.measurableSet
    (fun i => (L i).isCompact.measurableSet)
    (isClosed_cthickening (E := (K : Set E)) (δ := 1)).measurableSet
    K.isBounded.cthickening.measure_lt_top.ne
  · have hevent := hL.eventually (Metric.ball_mem_nhds K zero_lt_one)
    filter_upwards [hevent] with i hi x hx
    obtain ⟨y, hy, hxy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
    apply mem_cthickening_of_dist_le x y 1 (K : Set E) hy
    rw [← hxy]
    exact (infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top).trans hi.le
  · have hnull := K.convex.addHaar_frontier μ
    have hae : ∀ᵐ x ∂μ, x ∉ frontier (K : Set E) := by
      exact measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hae] with x hx
    by_cases hxK : x ∈ K
    · have hxi : x ∈ interior (K : Set E) := (mem_interior_iff_notMem_frontier hxK).mpr hx
      filter_upwards [BodySupport.eventually_mem_of_mem_interior hL hxi] with i hi
      exact iff_of_true hi hxK
    · filter_upwards [BodySupport.eventually_notMem_of_notMem hL hxK] with i hi
      exact iff_of_false hi hxK

theorem continuous_convexBody_measure :
    Continuous (fun K : ConvexBody E => μ (K : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  exact tendsto_convexBody_measure μ tendsto_id

theorem continuous_convexBody_realMeasure :
    Continuous (fun K : ConvexBody E => μ.real (K : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  have hfinite : μ (K : Set E) ≠ ⊤ := K.isCompact.measure_lt_top.ne
  exact (ENNReal.tendsto_toReal hfinite).comp
    ((continuous_convexBody_measure μ).tendsto K)

end MeasureContinuity
end VolumePolynomials
end -- closes the original EOF section from source line 22
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodyContinuity.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyTopology.lean -/
section

@[expose] public section

/-!
# Compactness of bounded families of convex bodies

This module proves the hyperspace compactness needed in Section 2 from Mathlib's
Vietoris/Hausdorff topology on nonempty compact sets. Convexity and containing
the origin are closed conditions; no support-function representation is assumed.
-/

noncomputable section

open Set TopologicalSpace Metric Filter
open scoped Topology Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bodyToNonemptyCompacts (K : ConvexBody E) : NonemptyCompacts E :=
  ⟨⟨K, K.isCompact⟩, K.nonempty⟩

@[simp] theorem coe_bodyToNonemptyCompacts (K : ConvexBody E) :
    (bodyToNonemptyCompacts K : Set E) = (K : Set E) := rfl

theorem isometry_bodyToNonemptyCompacts : Isometry (bodyToNonemptyCompacts (E := E)) := by
  apply Isometry.of_dist_eq
  intro K L
  rfl

omit [NormedSpace ℝ E] in
theorem isClosed_compacts_subset_relation :
    IsClosed {p : NonemptyCompacts E × NonemptyCompacts E | p.1 ≤ p.2} := by
  have h := isClosed_eq (NonemptyCompacts.lipschitz_sup (α := E)).continuous continuous_snd
  simpa only [sup_eq_right] using h

def combinationImage (a b : ℝ) (K : NonemptyCompacts E) : NonemptyCompacts E :=
  (K ×ˢ K).map (fun p : E × E => a • p.1 + b • p.2) (by fun_prop)

theorem continuous_combinationImage (a b : ℝ) :
    Continuous (combinationImage (E := E) a b) := by
  exact (Continuous.nonemptyCompacts_map (by fun_prop :
    Continuous (fun p : E × E => a • p.1 + b • p.2))).comp
      (NonemptyCompacts.continuous_prod.comp (continuous_id.prodMk continuous_id))

theorem convex_iff_combinationImage_le (K : NonemptyCompacts E) :
    Convex ℝ (K : Set E) ↔
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → combinationImage a b K ≤ K := by
  constructor
  · intro h a b ha hb hab x hx
    rcases hx with ⟨⟨y,z⟩, ⟨hy,hz⟩, rfl⟩
    exact h hy hz ha hb hab
  · intro h x hx y hy a b ha hb hab
    exact h a b ha hb hab ⟨(x,y), ⟨hx,hy⟩, rfl⟩

theorem isClosed_compacts_convex :
    IsClosed {K : NonemptyCompacts E | Convex ℝ (K : Set E)} := by
  simp_rw [convex_iff_combinationImage_le]
  simp only [ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun _ha => isClosed_iInter fun _hb => isClosed_iInter fun _hab =>
      isClosed_compacts_subset_relation.preimage
        ((continuous_combinationImage a b).prodMk continuous_id)

theorem range_bodyToNonemptyCompacts :
    Set.range (bodyToNonemptyCompacts (E := E)) =
      {K : NonemptyCompacts E | Convex ℝ (K : Set E)} := by
  ext K
  constructor
  · rintro ⟨L, rfl⟩
    exact L.convex
  · intro h
    exact ⟨⟨K, h, K.isCompact, K.nonempty⟩, rfl⟩

instance completeSpace_convexBody [CompleteSpace E] : CompleteSpace (ConvexBody E) := by
  have hr : IsClosed (Set.range (bodyToNonemptyCompacts (E := E))) := by
    rw [range_bodyToNonemptyCompacts]
    exact isClosed_compacts_convex
  exact isometry_bodyToNonemptyCompacts.isUniformEmbedding.completeSpace hr.isComplete

theorem continuous_bodyToNonemptyCompacts : Continuous (bodyToNonemptyCompacts (E := E)) :=
  isometry_bodyToNonemptyCompacts.continuous

theorem bodyToNonemptyCompacts_add (K L : ConvexBody E) :
    bodyToNonemptyCompacts (K + L) =
      (bodyToNonemptyCompacts K ×ˢ bodyToNonemptyCompacts L).map
        (fun p : E × E => p.1 + p.2) (by fun_prop) := by
  apply NonemptyCompacts.ext
  ext x
  change x ∈ ((K : Set E) + (L : Set E)) ↔ _
  rw [Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨(y, z), ⟨hy, hz⟩, rfl⟩
  · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
    exact ⟨y, hy, z, hz, rfl⟩

theorem continuous_add_convexBody :
    Continuous (fun p : ConvexBody E × ConvexBody E => p.1 + p.2) := by
  apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
  simp only [Function.comp_def, bodyToNonemptyCompacts_add]
  exact (Continuous.nonemptyCompacts_map (by fun_prop :
    Continuous (fun p : E × E => p.1 + p.2))).comp
      (NonemptyCompacts.continuous_prod.comp
        ((continuous_bodyToNonemptyCompacts.comp continuous_fst).prodMk
          (continuous_bodyToNonemptyCompacts.comp continuous_snd)))

instance continuousAdd_convexBody : ContinuousAdd (ConvexBody E) :=
  ⟨continuous_add_convexBody⟩

theorem bodyToNonemptyCompacts_smul (r : ℝ) (K : ConvexBody E) :
    bodyToNonemptyCompacts (r • K) =
      (bodyToNonemptyCompacts K).map (fun x => r • x) (by fun_prop) := by
  apply NonemptyCompacts.ext
  rfl

theorem continuous_smul_convexBody :
    Continuous (fun p : ℝ × ConvexBody E => p.1 • p.2) := by
  apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
  simp only [Function.comp_def, bodyToNonemptyCompacts_smul]
  apply Continuous.nonemptyCompacts_map'
    (continuous_bodyToNonemptyCompacts.comp continuous_snd)
  fun_prop

instance continuousSMul_convexBody : ContinuousSMul ℝ (ConvexBody E) :=
  ⟨continuous_smul_convexBody⟩

omit [NormedSpace ℝ E] in
theorem isClosed_compacts_contains (x : E) :
    IsClosed {K : NonemptyCompacts E | x ∈ K} := by
  have h := isClosed_compacts_subset_relation.preimage
    (continuous_const.prodMk continuous_id :
      Continuous (fun K : NonemptyCompacts E => (({x} : NonemptyCompacts E), K)))
  simpa only [Set.preimage_ofPred_eq, NonemptyCompacts.singleton_le_iff] using h

theorem isCompact_normalized_compacts {C : Set E} (hC : IsCompact C) :
    IsCompact {K : NonemptyCompacts E |
      Convex ℝ (K : Set E) ∧ (0 : E) ∈ K ∧ (K : Set E) ⊆ C} := by
  have hbase := NonemptyCompacts.isCompact_subsets_of_isCompact hC
  have hclosed := isClosed_compacts_convex.inter (isClosed_compacts_contains (0 : E))
  have h := hbase.inter_right hclosed
  convert h using 1
  ext K
  simp only [mem_ofPred_eq, mem_inter_iff]
  tauto

theorem isCompact_bodies_in_compact {C : Set E} (hC : IsCompact C) :
    IsCompact {K : ConvexBody E | (0 : E) ∈ K ∧ (K : Set E) ⊆ C} := by
  have hr : IsClosed (Set.range (bodyToNonemptyCompacts (E := E))) := by
    rw [range_bodyToNonemptyCompacts]
    exact isClosed_compacts_convex
  have h := isometry_bodyToNonemptyCompacts.isUniformInducing.isInducing.isCompact_preimage
    hr (isCompact_normalized_compacts hC)
  convert h using 1
  ext K
  simp only [mem_ofPred_eq, mem_preimage, coe_bodyToNonemptyCompacts]
  exact ⟨fun hK => ⟨K.convex, hK⟩, fun hK => hK.2⟩

end VolumePolynomials
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodyTopology.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolynomialCoordinates.lean -/
section

@[expose] public section

/-!
# Exact correspondence with homogeneous multivariate polynomials

The finite coordinate convention retains every exponent of total degree `d`.
The mutually inverse coefficient maps below justify this point formally.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace VolumePolynomials

def multiIndexOfDegree {n d : ℕ} (e : Fin n →₀ ℕ) (he : e.degree = d) : MultiIndex n d := by
  have hle : ∀ i, e i ≤ d := by
    intro i
    rw [← he, Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
  exact ⟨fun i => ⟨e i, Nat.lt_succ_of_le (hle i)⟩, by
    simpa only [← Finsupp.degree_eq_sum] using he⟩

@[simp] theorem exponent_multiIndexOfDegree {n d : ℕ} (e : Fin n →₀ ℕ)
    (he : e.degree = d) : exponent (multiIndexOfDegree e he) = e := by
  ext i
  rfl

def coefficientsOfPolynomial {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) : Coefficients n d :=
  fun α => p.coeff (exponent α)

@[simp] theorem coefficientsOfPolynomial_coefficientPolynomial {n d : ℕ}
    (c : Coefficients n d) : coefficientsOfPolynomial (coefficientPolynomial c) = c := by
  funext α
  exact coefficientPolynomial_coeff c α

theorem coefficientPolynomial_coefficientsOfPolynomial {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d) :
    coefficientPolynomial (coefficientsOfPolynomial (d := d) p) = p := by
  classical
  apply MvPolynomial.ext
  intro e
  by_cases he : e.degree = d
  · rw [← exponent_multiIndexOfDegree e he, coefficientPolynomial_coeff]
    rfl
  · have hzero : p.coeff e = 0 := by
      by_contra h
      apply he
      rw [Finsupp.degree_eq_weight_one]
      exact hp h
    have hne : ∀ α : MultiIndex n d, exponent α ≠ e := by
      intro α h
      apply he
      rw [← h]
      exact degree_exponent α
    simp [coefficientPolynomial, MvPolynomial.coeff_monomial, hne, hzero]

/-- All homogeneous degree-`d` polynomials, and only those, are represented by the
finite coefficient vectors used by the geometric realization relation. -/
theorem exists_coefficientPolynomial_iff {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    (∃ c : Coefficients n d, coefficientPolynomial c = p) ↔ p.IsHomogeneous d := by
  constructor
  · rintro ⟨c, rfl⟩
    exact coefficientPolynomial_homogeneous c
  · intro hp
    exact ⟨coefficientsOfPolynomial p, coefficientPolynomial_coefficientsOfPolynomial p hp⟩

theorem realizes_of_homogeneous_polynomial {n d : ℕ} (K : Fin n → Body d)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
    (hvol : ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) → MvPolynomial.eval t p = volumeFunction K t) :
    Realizes K (coefficientsOfPolynomial (d := d) p) := by
  intro t ht
  rw [evaluate_eq_polynomial_eval, coefficientPolynomial_coefficientsOfPolynomial p hp]
  exact hvol t ht

end VolumePolynomials
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 4
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolynomialCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/PositiveVolumePolynomial.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Algebra and continuity for the facet induction

The polynomial constructed from facet heights has its ordinary monomial
coefficients nonnegative. Its geometric inputs are actual lower-dimensional
volume polynomials and an exact pyramid-volume decomposition. This module
proves the algebraic induction step, including extension from positive to
nonnegative weights; it does not assume or assert that facet data exist.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Topology Pointwise

namespace VolumePolynomials

def PolynomialNonnegativeCoefficients {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m, 0 ≤ p.coeff m

theorem PolynomialNonnegativeCoefficients.zero {σ : Type*} :
    PolynomialNonnegativeCoefficients (0 : MvPolynomial σ ℝ) := by
  first
  | intro m
    simp

theorem PolynomialNonnegativeCoefficients.C {σ : Type*} {c : ℝ} (hc : 0 ≤ c) :
    PolynomialNonnegativeCoefficients (MvPolynomial.C c : MvPolynomial σ ℝ) := by
  first
  | classical
    intro m
    rw [MvPolynomial.coeff_C]
    split_ifs <;> first | exact hc | exact le_rfl

theorem PolynomialNonnegativeCoefficients.X {σ : Type*} (i : σ) :
    PolynomialNonnegativeCoefficients (MvPolynomial.X i : MvPolynomial σ ℝ) := by
  first
  | classical
    intro m
    rw [MvPolynomial.coeff_X]
    split_ifs <;> first | exact zero_le_one | exact le_rfl

theorem PolynomialNonnegativeCoefficients.mul {σ : Type*}
    {p q : MvPolynomial σ ℝ} (hp : PolynomialNonnegativeCoefficients p)
    (hq : PolynomialNonnegativeCoefficients q) : PolynomialNonnegativeCoefficients (p * q) := by
  first
  | classical
    intro m
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a.1) (hq a.2))

theorem PolynomialNonnegativeCoefficients.sum {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i, PolynomialNonnegativeCoefficients (p i)) :
    PolynomialNonnegativeCoefficients (∑ i, p i) := by
  first
  | intro m
    rw [MvPolynomial.coeff_sum]
    exact Finset.sum_nonneg (fun i _ => hp i m)

def heightPolynomial {n : ℕ} (h : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (h i) * MvPolynomial.X i

theorem heightPolynomial_homogeneous {n : ℕ} (h : Fin n → ℝ) :
    (heightPolynomial h).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _
    (fun i _ => MvPolynomial.isHomogeneous_C_mul_X (h i) i)

theorem heightPolynomial_nonnegative {n : ℕ} {h : Fin n → ℝ} (hh : ∀ i, 0 ≤ h i) :
    PolynomialNonnegativeCoefficients (heightPolynomial h) :=
  PolynomialNonnegativeCoefficients.sum _ (fun i =>
    (PolynomialNonnegativeCoefficients.C (hh i)).mul
      (PolynomialNonnegativeCoefficients.X i))

@[simp] theorem eval_heightPolynomial {n : ℕ} (h t : Fin n → ℝ) :
    MvPolynomial.eval t (heightPolynomial h) = ∑ i, h i * t i := by
  first
  | simp only [heightPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]

section Volume
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {n : ℕ}

def HasPositiveVolumePolynomial (K : Fin n → ConvexBody E) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.IsHomogeneous (finrank ℝ E) ∧ PolynomialNonnegativeCoefficients p ∧
    ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)

theorem continuous_weight_volume (K : Fin n → ConvexBody E) :
    Continuous (fun t : Fin n → ℝ =>
      μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)) :=
  (continuous_convexBody_realMeasure μ).comp (by fun_prop)

/-- Equality on strictly positive weights extends to every boundary face of the
closed positive orthant by continuity of actual convex-body volume. -/
theorem polynomial_volume_eq_of_positive (K : Fin n → ConvexBody E)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ t : Fin n → ℝ, (∀ i, 0 < t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)) :
    ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E) := by
  first
  | have hc := isClosed_eq p.continuous_eval (continuous_weight_volume μ K)
    have hsub : Set.pi Set.univ (fun _ : Fin n => Set.Ioi (0 : ℝ)) ⊆
        {t | MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)} := by
      intro t ht
      exact hp t (fun i => ht i (Set.mem_univ i))
    intro t ht
    apply closure_minimal hsub hc
    rw [closure_pi_set]
    intro i _
    rw [closure_Ioi]
    exact ht i

/-- A geometric facet decomposition produces the next homogeneous polynomial.
The lower-dimensional polynomials and the displayed volume identity are
explicit proof obligations; this lemma supplies only their algebraic assembly. -/
theorem hasPositiveVolumePolynomial_of_facets {ι : Type*} [Fintype ι]
    (K : Fin n → ConvexBody E) (d : ℕ) (hdim : finrank ℝ E = d + 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (h : ι → Fin n → ℝ)
    (hh : ∀ i j, 0 ≤ h i j) (q : ι → MvPolynomial (Fin n) ℝ)
    (hqdegree : ∀ i, (q i).IsHomogeneous d)
    (hqcoeff : ∀ i, PolynomialNonnegativeCoefficients (q i))
    (hvolume : ∀ t : Fin n → ℝ, (∀ j, 0 < t j) →
      μ.real ((∑ j, t j • K j : ConvexBody E) : Set E) =
        ∑ i, c i * (∑ j, h i j * t j) * MvPolynomial.eval t (q i)) :
    HasPositiveVolumePolynomial μ K := by
  first
  | let p : MvPolynomial (Fin n) ℝ :=
      ∑ i, MvPolynomial.C (c i) * (heightPolynomial (h i) * q i)
    refine ⟨p, ?_, ?_, polynomial_volume_eq_of_positive μ K p ?_⟩
    · rw [hdim]
      apply MvPolynomial.IsHomogeneous.sum
      intro i _
      simpa only [Nat.add_comm] using
        ((heightPolynomial_homogeneous (h i)).mul (hqdegree i)).C_mul (c i)
    · exact PolynomialNonnegativeCoefficients.sum _ (fun i =>
        (PolynomialNonnegativeCoefficients.C (hc i)).mul
          ((heightPolynomial_nonnegative (hh i)).mul (hqcoeff i)))
    · intro t ht
      rw [hvolume t ht]
      simp only [p, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, eval_heightPolynomial, mul_assoc]

/-- Independent body translations do not change the resulting polynomial. -/
theorem HasPositiveVolumePolynomial.translate {K : Fin n → ConvexBody E}
    (hK : HasPositiveVolumePolynomial μ K) (v : Fin n → E) :
    HasPositiveVolumePolynomial μ (fun i => translateBody (v i) (K i)) := by
  first
  | obtain ⟨p, hp, hn, hv⟩ := hK
    refine ⟨p, hp, hn, fun t ht => ?_⟩
    have hsum : (∑ i, t i • translateBody (v i) (K i)) =
        translateBody (∑ i, t i • v i) (∑ i, t i • K i) := by
      simp only [translateBody, smul_add, ← pointBody_smul, Finset.sum_add_distrib]
      congr 1
      exact (map_sum (pointBodyHom (E := E)) _ _).symm
    rw [hsum, coe_translateBody, Measure.real, measure_vadd]
    exact hv t ht

end Volume

/-- The generic Haar formulation gives the exact ordinary coefficient convention
used by the paper's realization locus. -/
theorem HasPositiveVolumePolynomial.exists_realizes {n d : ℕ}
    {K : Fin n → Body d} (hK : HasPositiveVolumePolynomial volume K) :
    ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c := by
  first
  | obtain ⟨p, hp, hn, hv⟩ := hK
    have hd : p.IsHomogeneous d := by simpa [Space] using hp
    refine ⟨coefficientsOfPolynomial (d := d) p,
      (fun α => hn (exponent α)), realizes_of_homogeneous_polynomial K p hd ?_⟩
    exact hv

end VolumePolynomials
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PositiveVolumePolynomial.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeFaces.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Exposed faces and the fixed direction spaces of positive Minkowski sums

These lemmas concern the literal exposed set of a continuous linear functional.
They are valid for arbitrary nonempty compact sets where indicated; no abstract
face lattice, polytope representation, or mixed-volume assertion is assumed.

The final equality is the algebraic step needed to use the facet directions of
the single sum at weights one for every strictly positive assignment of weights.
-/

noncomputable section
open Set
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeFaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A maximizer of a sum is exactly a sum of maximizers. No attainment assumption
is needed: membership on either side already supplies the relevant points. -/
theorem exposed_add (l : E →L[ℝ] ℝ) (A B : Set E) :
    l.toExposed (A + B) = l.toExposed A + l.toExposed B := by
  first
  | ext x
    constructor
    · rintro ⟨⟨a, ha, b, hb, rfl⟩, hmax⟩
      refine ⟨a, ⟨ha, ?_⟩, b, ⟨hb, ?_⟩, rfl⟩
      · intro y hy
        have h := hmax (y + b) ⟨y, hy, b, hb, rfl⟩
        simpa only [map_add, add_le_add_iff_right] using h
      · intro y hy
        have h := hmax (a + y) ⟨a, ha, y, hy, rfl⟩
        simpa only [map_add, add_le_add_iff_left] using h
    · rintro ⟨a, ⟨ha, hma⟩, b, ⟨hb, hmb⟩, rfl⟩
      refine ⟨⟨a, ha, b, hb, rfl⟩, ?_⟩
      rintro y ⟨u, hu, v, hv, rfl⟩
      simpa only [map_add] using add_le_add (hma u hu) (hmb v hv)

theorem exposed_smul (l : E →L[ℝ] ℝ) (A : Set E) {c : ℝ} (hc : 0 < c) :
    l.toExposed (c • A) = c • l.toExposed A := by
  first
  | ext x
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hmax⟩
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      intro y hy
      have h := hmax (c • y) ⟨y, hy, rfl⟩
      simp only [map_smul, smul_eq_mul] at h
      exact (mul_le_mul_iff_right₀ hc).mp h
    · rintro ⟨a, ⟨ha, hmax⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ?_⟩
      rintro y ⟨b, hb, rfl⟩
      simpa only [map_smul, smul_eq_mul] using mul_le_mul_of_nonneg_left (hmax b hb) hc.le

@[simp] theorem exposed_singleton (l : E →L[ℝ] ℝ) (x : E) :
    l.toExposed ({x} : Set E) = {x} := by
  first
  | ext y
    simp only [ContinuousLinearMap.toExposed, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro h
      subst y
      exact ⟨rfl, fun z hz => by subst z; exact le_rfl⟩

theorem exposed_nonempty (l : E →L[ℝ] ℝ) {A : Set E}
    (hA : IsCompact A) (hne : A.Nonempty) : (l.toExposed A).Nonempty := by
  first
  | obtain ⟨x, hx, hmax⟩ := hA.exists_isMaxOn hne l.continuous.continuousOn
    exact ⟨x, hx, hmax⟩

/-- Direction spaces add by taking their supremum, with nonemptiness ensuring
that each original direction can be recovered while the other point is fixed. -/
theorem vectorSpan_add {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty) :
    vectorSpan ℝ (A + B) = vectorSpan ℝ A ⊔ vectorSpan ℝ B := by
  first
  | let L : (E × E) →ₗ[ℝ] E := (LinearMap.id : E →ₗ[ℝ] E).coprod LinearMap.id
    have hset : L.toAffineMap '' (A ×ˢ B) = A + B := by
      ext x
      constructor
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    rw [← hset, ← AffineMap.map_vectorSpan, vectorSpan_prod_eq hA hB]
    simpa only [L, LinearMap.toAffineMap_linear, LinearMap.coprod_map_prod,
      Submodule.map_id]

theorem vectorSpan_smul (A : Set E) {c : ℝ} (hc : c ≠ 0) :
    vectorSpan ℝ (c • A) = vectorSpan ℝ A := by
  first
  | let L : E →ₗ[ℝ] E := c • LinearMap.id
    change vectorSpan ℝ (L.toAffineMap '' A) = _
    rw [← AffineMap.map_vectorSpan]
    exact (Submodule.map_smul LinearMap.id (vectorSpan ℝ A) c hc).trans
      (Submodule.map_id _)

variable {ι : Type*}

theorem exposed_sum (l : E →L[ℝ] ℝ) (s : Finset ι) (A : ι → Set E) :
    l.toExposed (∑ i ∈ s, A i) = ∑ i ∈ s, l.toExposed (A i) := by
  first
  | classical
    induction s using Finset.induction_on with
    | empty => simp [← Set.singleton_zero]
    | @insert i s hi ih => simp only [Finset.sum_insert hi, exposed_add, ih]

theorem nonempty_sum (s : Finset ι) (A : ι → Set E)
    (hA : ∀ i ∈ s, (A i).Nonempty) : (∑ i ∈ s, A i).Nonempty := by
  first
  | classical
    exact Finset.sum_induction A Set.Nonempty (fun _ _ ha hb => ha.add hb)
      (singleton_nonempty 0) hA

theorem vectorSpan_sum (s : Finset ι) (A : ι → Set E) :
    (∀ i ∈ s, (A i).Nonempty) →
      vectorSpan ℝ (∑ i ∈ s, A i) = s.sup (fun i => vectorSpan ℝ (A i)) := by
  first
  | classical
    induction s using Finset.induction_on with
    | empty => intro _; simp [← Set.singleton_zero]
    | @insert i s hi ih =>
        intro hA
        have hs : ∀ j ∈ s, (A j).Nonempty := fun j hj => hA j (Finset.mem_insert_of_mem hj)
        rw [Finset.sum_insert hi,
          vectorSpan_add (hA i (Finset.mem_insert_self i s)) (nonempty_sum s A hs),
          Finset.sup_insert, ih hs]

/-- Strictly positive rescaling preserves the direction space of a finite
Minkowski sum, without requiring the individual sets to be full dimensional. -/
theorem vectorSpan_weighted_sum (s : Finset ι) (A : ι → Set E) (t : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).Nonempty) (ht : ∀ i ∈ s, 0 < t i) :
    vectorSpan ℝ (∑ i ∈ s, t i • A i) = vectorSpan ℝ (∑ i ∈ s, A i) := by
  first
  | have hne : ∀ i ∈ s, (t i • A i).Nonempty := by
      intro i hi
      exact (hA i hi).image (fun x => t i • x)
    rw [vectorSpan_sum s _ hne, vectorSpan_sum s A hA]
    apply Finset.sup_congr rfl
    intro i hi
    exact vectorSpan_smul (A i) (ht i hi).ne'

theorem exposed_weighted_sum (l : E →L[ℝ] ℝ) (s : Finset ι)
    (A : ι → Set E) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 < t i) :
    l.toExposed (∑ i ∈ s, t i • A i) = ∑ i ∈ s, t i • l.toExposed (A i) := by
  first
  | rw [exposed_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact exposed_smul l (A i) (ht i hi)

/-- The direction space of every exposed face is independent of the strictly
positive weights. In particular, its codimension-one property is unchanged. -/
theorem vectorSpan_exposed_weighted_sum (l : E →L[ℝ] ℝ) (s : Finset ι)
    (A : ι → Set E) (t : ι → ℝ)
    (hA : ∀ i ∈ s, IsCompact (A i)) (hne : ∀ i ∈ s, (A i).Nonempty)
    (ht : ∀ i ∈ s, 0 < t i) :
    vectorSpan ℝ (l.toExposed (∑ i ∈ s, t i • A i)) =
      vectorSpan ℝ (l.toExposed (∑ i ∈ s, A i)) := by
  first
  | rw [exposed_weighted_sum l s A t ht, exposed_sum]
    exact vectorSpan_weighted_sum s (fun i => l.toExposed (A i)) t
      (fun i hi => exposed_nonempty l (hA i hi) (hne i hi)) ht

end VolumePolynomials.PolytopeFaces
end -- closes the original EOF section from source line 24
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeFaces.lean -/

/- BEGIN SOURCE: VolumePolynomials/FinitePolytope.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Finite convex hulls and their exposed faces

All operations below preserve the existence of an actual finite generating set.
Exposed faces remain finite convex hulls by Krein--Milman and the fact that an
extreme point of an exposed face is an extreme point of the original hull.
No general-position or full-dimensional hypothesis is needed.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsFiniteHull (C : Set E) : Prop := ∃ S : Set E, S.Finite ∧ C = convexHull ℝ S

theorem IsFiniteHull.isCompact {C : Set E} (hC : IsFiniteHull C) : IsCompact C := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact hS.isCompact_convexHull ℝ

theorem IsFiniteHull.convex {C : Set E} (hC : IsFiniteHull C) : Convex ℝ C := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact convex_convexHull ℝ S

theorem IsFiniteHull.finite_extremePoints {C : Set E} (hC : IsFiniteHull C) :
    (C.extremePoints ℝ).Finite := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact hS.subset extremePoints_convexHull_subset

theorem IsFiniteHull.singleton (x : E) : IsFiniteHull ({x} : Set E) := by
  first
  | exact ⟨{x}, finite_singleton x, (convexHull_singleton (𝕜 := ℝ) x).symm⟩

theorem IsFiniteHull.zero : IsFiniteHull (0 : Set E) := IsFiniteHull.singleton 0

theorem IsFiniteHull.affine_image {C : Set E} (hC : IsFiniteHull C)
    (f : E →ᵃ[ℝ] F) : IsFiniteHull (f '' C) := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact ⟨f '' S, hS.image f, f.image_convexHull S⟩

theorem IsFiniteHull.linear_image {C : Set E} (hC : IsFiniteHull C)
    (f : E →ₗ[ℝ] F) : IsFiniteHull (f '' C) :=
  hC.affine_image f.toAffineMap

theorem IsFiniteHull.add {A B : Set E} (hA : IsFiniteHull A) (hB : IsFiniteHull B) :
    IsFiniteHull (A + B) := by
  first
  | obtain ⟨S, hS, rfl⟩ := hA
    obtain ⟨T, hT, rfl⟩ := hB
    exact ⟨S + T, hS.add hT, (convexHull_add S T).symm⟩

theorem IsFiniteHull.smul {C : Set E} (hC : IsFiniteHull C) (r : ℝ) :
    IsFiniteHull (r • C) := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact ⟨r • S, hS.image (fun x => r • x), (convexHull_smul r S).symm⟩

theorem IsFiniteHull.sum {ι : Type*} (s : Finset ι) (C : ι → Set E)
    (hC : ∀ i ∈ s, IsFiniteHull (C i)) : IsFiniteHull (∑ i ∈ s, C i) := by
  first
  | exact Finset.sum_induction C IsFiniteHull (fun _ _ ha hb => ha.add hb)
      IsFiniteHull.zero hC

theorem IsFiniteHull.weighted_sum {ι : Type*} (s : Finset ι) (C : ι → Set E)
    (hC : ∀ i ∈ s, IsFiniteHull (C i)) (t : ι → ℝ) :
    IsFiniteHull (∑ i ∈ s, t i • C i) :=
  IsFiniteHull.sum s _ (fun i hi => (hC i hi).smul (t i))

/-- A face may be empty or lower dimensional; both cases are included. -/
theorem IsFiniteHull.exposed {C : Set E} (hC : IsFiniteHull C) (l : E →L[ℝ] ℝ) :
    IsFiniteHull (l.toExposed C) := by
  first
  | have he : IsExposed ℝ C (l.toExposed C) := ContinuousLinearMap.toExposed.isExposed
    have hf : ((l.toExposed C).extremePoints ℝ).Finite :=
      hC.finite_extremePoints.subset he.isExtreme.extremePoints_subset_extremePoints
    have hclosed : IsClosed (convexHull ℝ ((l.toExposed C).extremePoints ℝ)) :=
      hf.isClosed_convexHull ℝ
    refine ⟨(l.toExposed C).extremePoints ℝ, hf, ?_⟩
    have h := closure_convexHull_extremePoints (he.isCompact hC.isCompact) (he.convex hC.convex)
    rw [hclosed.closure_eq] at h
    exact h.symm

theorem IsFiniteHull.exists_finset {C : Set E} (hC : IsFiniteHull C) :
    ∃ S : Finset E, C = convexHull ℝ (S : Set E) := by
  first
  | classical
    obtain ⟨S, hS, hC⟩ := hC
    exact ⟨hS.toFinset, by simpa using hC⟩

section Volume

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- A convex body with empty interior has zero ambient volume. -/
theorem volume_eq_zero_of_empty_interior {C : Set E} (hc : Convex ℝ C)
    (hC : interior C = ∅) : volume C = 0 := by
  first
  | have hspan : affineSpan ℝ C ≠ ⊤ := by
      intro h
      have hn := hc.interior_nonempty_iff_affineSpan_eq_top.mpr h
      rw [hC] at hn
      exact Set.not_nonempty_empty hn
    exact measure_mono_null (subset_affineSpan ℝ C)
      (Measure.addHaar_affineSubspace volume _ hspan)

end Volume
end VolumePolynomials.PolytopeGeometry
end -- closes the original EOF section from source line 21
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FinitePolytope.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyCentering.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Centering the tuple for the facet induction

An interior point of a Minkowski sum is the sum of points in its summands.
Translating by these points puts zero in every summand and in the interior of
the total sum. If the total sum has empty interior, all weighted sums have zero
ambient volume after centering. Thus no full-dimensional hypothesis is needed
in the eventual polynomiality theorem.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials
open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem sum_translateBody (K : ι → ConvexBody E) (v : ι → E) :
    (∑ i, translateBody (v i) (K i)) = translateBody (∑ i, v i) (∑ i, K i) := by
  first
  | simp only [translateBody, Finset.sum_add_distrib]
    congr 1
    exact (map_sum (pointBodyHom (E := E)) _ _).symm

theorem zero_mem_sum_body (K : ι → ConvexBody E) (hK : ∀ i, (0 : E) ∈ K i) :
    (0 : E) ∈ ∑ i, K i := by
  first
  | rw [mem_sum_body]
    exact ⟨fun _ => 0, hK, Finset.sum_const_zero⟩

/-- The translation vectors are actual points of the original summands. -/
theorem exists_centered_translates (K : ι → ConvexBody E)
    (hfull : (interior ((∑ i, K i : ConvexBody E) : Set E)).Nonempty) :
    ∃ p : ι → E, (∀ i, p i ∈ K i) ∧
      (∀ i, (0 : E) ∈ translateBody (-p i) (K i)) ∧
      (0 : E) ∈ interior ((∑ i, translateBody (-p i) (K i) : ConvexBody E) : Set E) := by
  first
  | obtain ⟨x, hx⟩ := hfull
    obtain ⟨p, hp, hsum⟩ := (mem_sum_body K x).mp (interior_subset hx)
    refine ⟨p, hp, (fun i => zero_mem_translateBody_neg (hp i)), ?_⟩
    rw [sum_translateBody, Finset.sum_neg_distrib, hsum, coe_translateBody, interior_vadd]
    exact ⟨x, hx, neg_add_cancel x⟩

theorem isFiniteHull_translateBody {K : ConvexBody E}
    (hK : IsFiniteHull (K : Set E)) (v : E) :
    IsFiniteHull (translateBody v K : Set E) := by
  first
  | change IsFiniteHull (({v} : Set E) + (K : Set E))
    exact (IsFiniteHull.singleton v).add hK

section Measure
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem weighted_sum_measure_zero_of_empty_interior (K : ι → ConvexBody E)
    (hK : ∀ i, (0 : E) ∈ K i)
    (hempty : interior ((∑ i, K i : ConvexBody E) : Set E) = ∅) (t : ι → ℝ) :
    μ ((∑ i, t i • K i : ConvexBody E) : Set E) = 0 := by
  first
  | let S : Set E := ((∑ i, K i : ConvexBody E) : Set E)
    let U : Submodule ℝ E := Submodule.span ℝ S
    have hspan : affineSpan ℝ S ≠ ⊤ := by
      intro h
      have hn := (∑ i, K i : ConvexBody E).convex.interior_nonempty_iff_affineSpan_eq_top.mpr h
      rw [hempty] at hn
      exact Set.not_nonempty_empty hn
    have hU : U ≠ ⊤ := by
      intro h
      apply hspan
      rw [affineSpan_eq_span_of_zero_mem
        (mem_affineSpan ℝ (zero_mem_sum_body K hK))]
      change U.toAffineSubspace = ⊤
      rw [h]
      rfl
    apply measure_mono_null _ (Measure.addHaar_submodule μ U hU)
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    apply Submodule.sum_mem
    intro i _
    obtain ⟨y, hy, heq⟩ := hp i
    rw [← heq]
    exact U.smul_mem (t i) (Submodule.subset_span (body_le_sum_of_zero_mem K hK i hy))

theorem hasPositiveVolumePolynomial_of_empty_interior {n : ℕ}
    (K : Fin n → ConvexBody E) (hK : ∀ i, (0 : E) ∈ K i)
    (hempty : interior ((∑ i, K i : ConvexBody E) : Set E) = ∅) :
    HasPositiveVolumePolynomial μ K := by
  first
  | refine ⟨0, MvPolynomial.isHomogeneous_zero (σ := Fin n) (R := ℝ) _,
      PolynomialNonnegativeCoefficients.zero, fun t _ => ?_⟩
    rw [map_zero, Measure.real,
      weighted_sum_measure_zero_of_empty_interior μ K hK hempty t, ENNReal.toReal_zero]

/-- Removing the centering and full-dimensional restrictions from the finite
polytope induction. Its premise is precisely the centered geometric case. -/
theorem hasPositiveVolumePolynomial_of_centered_case {n : ℕ}
    (hcenter : ∀ L : Fin n → ConvexBody E,
      (∀ i, IsFiniteHull (L i : Set E)) → (∀ i, (0 : E) ∈ L i) →
      (0 : E) ∈ interior ((∑ i, L i : ConvexBody E) : Set E) →
      HasPositiveVolumePolynomial μ L)
    (K : Fin n → ConvexBody E) (hpoly : ∀ i, IsFiniteHull (K i : Set E)) :
    HasPositiveVolumePolynomial μ K := by
  first
  | classical
    choose p hp using fun i => (K i).nonempty
    let L : Fin n → ConvexBody E := fun i => translateBody (-p i) (K i)
    have hzero : ∀ i, (0 : E) ∈ L i := fun i => zero_mem_translateBody_neg (hp i)
    have hfinite : ∀ i, IsFiniteHull (L i : Set E) :=
      fun i => isFiniteHull_translateBody (hpoly i) (-p i)
    have hL : HasPositiveVolumePolynomial μ L := by
      by_cases hfull : (interior ((∑ i, L i : ConvexBody E) : Set E)).Nonempty
      · obtain ⟨q, _, hqzero, hqfull⟩ := exists_centered_translates L hfull
        have hQ := hcenter (fun i => translateBody (-q i) (L i))
          (fun i => isFiniteHull_translateBody (hfinite i) (-q i)) hqzero hqfull
        have hback := HasPositiveVolumePolynomial.translate μ hQ (fun i => q i)
        simpa only [translateBody_translate, add_neg_cancel, translateBody_zero] using hback
      · exact hasPositiveVolumePolynomial_of_empty_interior μ L hzero
          (Set.not_nonempty_iff_eq_empty.mp hfull)
    have hback := HasPositiveVolumePolynomial.translate μ hL p
    simpa only [L, translateBody_translate, add_neg_cancel, translateBody_zero] using hback

end Measure
end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodyCentering.lean -/

/- BEGIN SOURCE: VolumePolynomials/RealizationContinuity.lean -/
section

@[expose] public section

/-!
# Closed realization relation and compact bounded coefficient locus

These statements concern the actual volume function of arbitrary compact convex
bodies. Polynomial existence is not assumed. The finite-dimensional space of
homogeneous coefficients embeds as a closed subspace of all functions on the
nonnegative orthant; this avoids assuming a coefficient-extraction formula.
-/

noncomputable section
open Set MeasureTheory Finset Topology
open scoped Pointwise BigOperators

namespace VolumePolynomials

abbrev NonnegativeWeights (n : ℕ) := {t : Fin n → ℝ // ∀ i, 0 ≤ t i}

def evaluationEmbedding (n d : ℕ) :
    Coefficients n d →ₗ[ℝ] (NonnegativeWeights n → ℝ) where
  toFun c t := evaluate c t.1
  map_add' c e := by
    funext t
    simp [evaluate, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext t
    simp [evaluate, Finset.mul_sum, mul_assoc]

theorem evaluationEmbedding_injective (n d : ℕ) :
    Function.Injective (evaluationEmbedding n d) := by
  intro c e h
  apply coefficients_eq_of_evaluate_nonneg
  intro t ht
  exact congrFun h ⟨t, ht⟩

theorem isClosedEmbedding_evaluation (n d : ℕ) :
    IsClosedEmbedding (evaluationEmbedding n d) :=
  LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (evaluationEmbedding_injective n d))

theorem continuous_evaluate {n d : ℕ} (t : Fin n → ℝ) :
    Continuous (fun c : Coefficients n d => evaluate c t) := by
  unfold evaluate
  fun_prop

theorem continuous_weightedSum {n d : ℕ} (t : Fin n → ℝ) :
    Continuous (fun K : Fin n → Body d => weightedSum K t) := by
  unfold weightedSum
  fun_prop

theorem continuous_bodyVolume (d : ℕ) : Continuous (bodyVolume (d := d)) :=
  continuous_convexBody_realMeasure (volume : Measure (Space d))

theorem continuous_volumeFunction {n d : ℕ} (t : Fin n → ℝ) :
    Continuous (fun K : Fin n → Body d => volumeFunction K t) :=
  (continuous_bodyVolume d).comp (continuous_weightedSum t)

def volumeEvaluation {n d : ℕ} (K : Fin n → Body d) : NonnegativeWeights n → ℝ :=
  fun t => volumeFunction K t.1

theorem continuous_volumeEvaluation (n d : ℕ) :
    Continuous (volumeEvaluation (n := n) (d := d)) := by
  apply continuous_pi
  intro t
  exact continuous_volumeFunction t.1

theorem realizes_iff_evaluation_eq {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} : Realizes K c ↔ evaluationEmbedding n d c = volumeEvaluation K := by
  constructor
  · intro h
    funext t
    exact h t.1 t.2
  · intro h t ht
    exact congrFun h ⟨t, ht⟩

theorem isClosed_realizes (n d : ℕ) :
    IsClosed {p : (Fin n → Body d) × Coefficients n d | Realizes p.1 p.2} := by
  simp_rw [realizes_iff_evaluation_eq]
  exact isClosed_eq ((isClosedEmbedding_evaluation n d).continuous.comp continuous_snd)
    ((continuous_volumeEvaluation n d).comp continuous_fst)

/-- Existence of a homogeneous volume polynomial passes to every Hausdorff limit
of tuples for which it has already been proved. The argument uses the closed
finite-dimensional evaluation range, so no coefficient convergence or mixed-volume
formula is assumed. -/
theorem exists_realizes_of_tendsto {n d : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Fin n → Body d} {L : ι → Fin n → Body d}
    (hL : Filter.Tendsto L l (𝓝 K))
    (hpoly : ∀ᶠ j in l, ∃ c : Coefficients n d, Realizes (L j) c) :
    ∃ c : Coefficients n d, Realizes K c := by
  have hlim : Filter.Tendsto (fun j => volumeEvaluation (L j)) l (𝓝 (volumeEvaluation K)) :=
    (continuous_volumeEvaluation n d).continuousAt.tendsto.comp hL
  have hmem : volumeEvaluation K ∈ Set.range (evaluationEmbedding n d) := by
    apply (isClosedEmbedding_evaluation n d).isClosed_range.mem_of_tendsto hlim
    filter_upwards [hpoly] with j hj
    obtain ⟨c, hc⟩ := hj
    exact ⟨c, realizes_iff_evaluation_eq.mp hc⟩
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, realizes_iff_evaluation_eq.mpr hc⟩

/-- The set of tuples whose actual volume function is a homogeneous degree-`d`
polynomial is closed. This is an existence statement, not merely uniqueness of
coefficient vectors attached to a tuple. -/
theorem isClosed_tuples_with_volume_polynomial (n d : ℕ) :
    IsClosed {K : Fin n → Body d | ∃ c : Coefficients n d, Realizes K c} := by
  have heq : {K : Fin n → Body d | ∃ c : Coefficients n d, Realizes K c} =
      volumeEvaluation ⁻¹' Set.range (evaluationEmbedding n d) := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_range, realizes_iff_evaluation_eq]
  rw [heq]
  exact (isClosedEmbedding_evaluation n d).isClosed_range.preimage
    (continuous_volumeEvaluation n d)

def boundedTuples (n d : ℕ) (C : Set (Space d)) : Set (Fin n → Body d) :=
  {K | ∀ i, (0 : Space d) ∈ K i ∧ (K i : Set (Space d)) ⊆ C}

theorem isCompact_boundedTuples (n d : ℕ) {C : Set (Space d)} (hC : IsCompact C) :
    IsCompact (boundedTuples n d C) := by
  have h := isCompact_univ_pi (fun _ : Fin n => isCompact_bodies_in_compact hC)
  simpa [Set.pi, boundedTuples] using h

def boundedVolumeLocus (n d : ℕ) (C : Set (Space d)) : Set (Coefficients n d) :=
  {c | ∃ K ∈ boundedTuples n d C, Realizes K c}

theorem boundedVolumeLocus_eq_preimage (n d : ℕ) (C : Set (Space d)) :
    boundedVolumeLocus n d C =
      evaluationEmbedding n d ⁻¹' (volumeEvaluation '' boundedTuples n d C) := by
  ext c
  constructor
  · rintro ⟨K, hK, hc⟩
    exact ⟨K, hK, (realizes_iff_evaluation_eq.mp hc).symm⟩
  · rintro ⟨K, hK, hc⟩
    exact ⟨K, hK, realizes_iff_evaluation_eq.mpr hc.symm⟩

/-- Compactness of the paper's bounded coefficient model, formulated using the
literal geometric realization relation. Lower-dimensional bodies are included. -/
theorem isCompact_boundedVolumeLocus (n d : ℕ) {C : Set (Space d)} (hC : IsCompact C) :
    IsCompact (boundedVolumeLocus n d C) := by
  rw [boundedVolumeLocus_eq_preimage]
  exact (isClosedEmbedding_evaluation n d).isCompact_preimage
    ((isCompact_boundedTuples n d hC).image (continuous_volumeEvaluation n d))

theorem boundedVolumeLocus_subset (n d : ℕ) (C : Set (Space d)) :
    boundedVolumeLocus n d C ⊆ VolumeLocus n d := by
  rintro c ⟨K, _, hK⟩
  exact ⟨K, hK⟩

end VolumePolynomials
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RealizationContinuity.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteBodyApproximation.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Approximation by actual finite convex hulls

Finite nets inside a compact convex body give inscribed polytopes at arbitrarily
small Hausdorff distance. The closed finite-dimensional evaluation range then
transfers polynomiality, including nonnegativity of every coefficient, from
all polytopes to all convex bodies. The polytope theorem remains an explicit
premise of the transfer lemma and must be proved separately.
-/

open Set Metric Topology
open scoped Topology BigOperators

namespace VolumePolynomials
open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteHullBody (S : Set E) (hS : S.Finite) (hne : S.Nonempty) : ConvexBody E where
  carrier := convexHull ℝ S
  convex' := convex_convexHull ℝ S
  isCompact' := hS.isCompact_convexHull ℝ
  nonempty' := hne.mono (subset_convexHull ℝ S)

theorem finiteHullBody_isFiniteHull (S : Set E) (hS : S.Finite) (hne : S.Nonempty) :
    IsFiniteHull (finiteHullBody S hS hne : Set E) := ⟨S, hS, rfl⟩

/-- The approximating vertices lie in the original body. -/
theorem exists_inscribed_finiteHullBody (K : ConvexBody E) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ConvexBody E, IsFiniteHull (P : Set E) ∧ P ≤ K ∧ dist P K < ε := by
  first
  | obtain ⟨S, hSK, hS, hcover⟩ :=
      Metric.finite_approx_of_totallyBounded K.isCompact.totallyBounded (ε / 2) (half_pos hε)
    have hne : S.Nonempty := by
      obtain ⟨x, hx⟩ := K.nonempty
      obtain ⟨y, hy, _⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact ⟨y, hy⟩
    let P := finiteHullBody S hS hne
    have hPK : P ≤ K := convexHull_min hSK K.convex
    refine ⟨P, finiteHullBody_isFiniteHull S hS hne, hPK, ?_⟩
    have hdist : dist P K ≤ ε / 2 := by
      change hausdorffDist (P : Set E) (K : Set E) ≤ ε / 2
      apply hausdorffDist_le_of_mem_dist (half_pos hε).le
      · intro x hx
        exact ⟨x, hPK hx, by simpa using (half_pos hε).le⟩
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
        exact ⟨y, subset_convexHull ℝ S hy, (Metric.mem_ball.mp hxy).le⟩
    exact hdist.trans_lt (half_lt_self hε)

theorem dense_finiteHullBodies :
    Dense {K : ConvexBody E | IsFiniteHull (K : Set E)} := by
  first
  | rw [Metric.dense_iff]
    intro K ε hε
    obtain ⟨P, hp, _, hdist⟩ := exists_inscribed_finiteHullBody K hε
    exact ⟨P, hdist, hp⟩

theorem dense_finiteHullBodyTuples (n : ℕ) :
    Dense {K : Fin n → ConvexBody E | ∀ i, IsFiniteHull (K i : Set E)} := by
  first
  | simpa [Set.pi] using
      (dense_pi Set.univ (fun (_ : Fin n) _ => dense_finiteHullBodies (E := E)))

def NonnegativeCoefficients (n d : ℕ) : Set (Coefficients n d) :=
  {c | ∀ α, 0 ≤ c α}

theorem isClosed_nonnegativeCoefficients (n d : ℕ) :
    IsClosed (NonnegativeCoefficients n d) := by
  first
  | change IsClosed {c : Coefficients n d | ∀ α, c α ∈ Set.Ici (0 : ℝ)}
    simp only [ofPred_forall]
    exact isClosed_iInter fun α => isClosed_Ici.preimage (continuous_apply α)

theorem isClosed_tuples_with_nonnegative_volume_polynomial (n d : ℕ) :
    IsClosed {K : Fin n → Body d |
      ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c} := by
  first
  | have hclosed := (isClosedEmbedding_evaluation n d).isClosedMap
      (NonnegativeCoefficients n d) (isClosed_nonnegativeCoefficients n d)
    have heq : {K : Fin n → Body d |
        ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c} =
        volumeEvaluation ⁻¹' (evaluationEmbedding n d '' NonnegativeCoefficients n d) := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image,
        NonnegativeCoefficients, realizes_iff_evaluation_eq]
    rw [heq]
    exact hclosed.preimage (continuous_volumeEvaluation n d)

/-- The only premise is the full polytope theorem, with no vertex bound or
general-position restriction. The conclusion covers every compact convex body. -/
theorem exists_nonnegative_realizes_of_all_finiteHulls (n d : ℕ)
    (hpoly : ∀ K : Fin n → Body d, (∀ i, IsFiniteHull (K i : Set (Space d))) →
      ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c)
    (K : Fin n → Body d) :
    ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c := by
  first
  | have hsub : {L : Fin n → Body d | ∀ i, IsFiniteHull (L i : Set (Space d))} ⊆
        {L | ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes L c} := hpoly
    exact closure_minimal hsub (isClosed_tuples_with_nonnegative_volume_polynomial n d)
      (dense_finiteHullBodyTuples (E := Space d) n K)

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteBodyApproximation.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeFoundation.lean -/
section
/-
Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Released under the Apache License 2.0; see vendor/openai-math/LICENSE.
Unused surface-measure definitions are omitted; two support proofs use direct compact maximizers.
All adaptations and exact unchanged source lines are recorded in audit/polytope-foundation-lines.json.
Original sources and hashes: audit/openai-polytope-provenance.json.
Regenerate with scripts/bundle-polytope-foundation.py. No checked status is implied.
-/

@[expose] public section

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/Model.lean -/
noncomputable section

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

noncomputable def simplexConstant (d : ℕ) : ℝ :=
  (d + 1) * (d : ℝ) ^ d / d.factorial

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def normalHyperplane {n : ℕ} (u : Euclidean n) : Submodule ℝ (Euclidean n) :=
  (Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ

def projectionVolume {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ENNReal :=
  (volume : Measure (normalHyperplane u))
    ((normalHyperplane u).orthogonalProjectionOnto '' K)

def brightness {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ℝ :=
  ‖u‖ * (projectionVolume K u).toReal

def projectionBody {n : ℕ} (K : Set (Euclidean n)) : Set (Euclidean n) :=
  {y | ∀ u, ⟪u, y⟫ ≤ brightness K u}

def normalizedProjectionVolume {n : ℕ} (K : Set (Euclidean n)) : ℝ :=
  (volume (projectionBody K)).toReal / (volume K).toReal ^ (n - 1)

def standardSimplex (n : ℕ) : Set (Euclidean n) :=
  convexHull ℝ (insert 0 (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)))

def firstBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.castAdd 10 i))

def secondBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.natAdd 10 i))

def productWitness : Set (Euclidean 20) :=
  {x | firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10}

end Paper092

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/Basic.lean -/
noncomputable section

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem normalHyperplane_volume_is_canonical {n : ℕ} (u : Euclidean n) :
    (volume : Measure (normalHyperplane u)) =
      (stdOrthonormalBasis ℝ (normalHyperplane u)).toBasis.addHaar := rfl

theorem normalHyperplane_finrank {n : ℕ} (u : Euclidean n) (hu : u ≠ 0) :
    Module.finrank ℝ (normalHyperplane u) = n - 1 := by
  have h := (Submodule.span ℝ ({u} : Set (Euclidean n))).finrank_add_finrank_orthogonal
  simp only [finrank_span_singleton hu, finrank_euclideanSpace_fin] at h
  change Module.finrank ℝ ((Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ) = n - 1
  omega

end Paper092

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/PolytopeDefinitions.lean -/
noncomputable section

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section

namespace Paper092

structure HPolytope (d : ℕ) (ι : Type uι) [Fintype ι] where
  normal : ι → Euclidean d
  offset : ι → ℝ
  normal_unit : ∀ i, ‖normal i‖ = 1
  compact : IsCompact {x : Euclidean d | ∀ i, ⟪normal i, x⟫ ≤ offset i}
  strict_feasible : ∃ x : Euclidean d, ∀ i, ⟪normal i, x⟫ < offset i
  distinct : Function.Injective (fun i => (normal i, offset i))

namespace HPolytope

def body {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) : Set (Euclidean d) :=
  {x | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i}

def face {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) (i : ι) :
    Set (Euclidean d) :=
  {x | x ∈ P.body ∧ ⟪P.normal i, x⟫ = P.offset i}

end HPolytope
end Paper092

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/PolytopeOperations.lean -/
noncomputable section

namespace OAI

universe uι uκ

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section
namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

def reindex (P : HPolytope d ι) (e : κ ≃ ι) : HPolytope d κ where
  normal i := P.normal (e i)
  offset i := P.offset (e i)
  normal_unit i := P.normal_unit (e i)
  compact := by
    convert P.compact using 1
    ext x
    constructor
    · intro h i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact h j
    · intro h j
      exact h (e j)
  strict_feasible := by
    obtain ⟨x, hx⟩ := P.strict_feasible
    exact ⟨x, fun i => hx (e i)⟩
  distinct := fun i j h => e.injective (P.distinct h)

theorem reindex_body (P : HPolytope d ι) (e : κ ≃ ι) :
    (P.reindex e).body = P.body := by
  ext x
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact h j
  · intro h j
    exact h (e j)

def translate (P : HPolytope d ι) (v : Euclidean d) : HPolytope d ι where
  normal := P.normal
  offset i := P.offset i + ⟪P.normal i, v⟫
  normal_unit := P.normal_unit
  compact := by
    have heq : {x : Euclidean d | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i + ⟪P.normal i, v⟫} =
        (fun x => v + x) '' P.body := by
      ext x
      constructor
      · intro hx
        refine ⟨x - v, ?_, by abel_nf⟩
        intro i
        have := hx i
        simpa only [inner_sub_right, sub_le_iff_le_add] using this
      · rintro ⟨x, hx, rfl⟩ i
        simpa only [inner_add_right, add_comm] using add_le_add_right (hx i) ⟪P.normal i, v⟫
    rw [heq]
    exact P.compact.image (continuous_const.add continuous_id)
  strict_feasible := by
    obtain ⟨x, hx⟩ := P.strict_feasible
    refine ⟨v + x, fun i => ?_⟩
    simpa only [inner_add_right, add_comm] using add_lt_add_right (hx i) ⟪P.normal i, v⟫
  distinct := by
    intro i j h
    apply P.distinct
    have hn := congrArg Prod.fst h
    have ho := congrArg Prod.snd h
    dsimp at hn ho
    exact Prod.ext hn (by simpa only [hn, add_left_inj] using ho)

theorem translate_body (P : HPolytope d ι) (v : Euclidean d) :
    (P.translate v).body = v +ᵥ P.body := by
  ext x
  constructor
  · intro hx
    refine ⟨x - v, ?_, by dsimp; abel_nf⟩
    intro i
    have h := hx i
    change ⟪P.normal i, x⟫ ≤ P.offset i + ⟪P.normal i, v⟫ at h
    simpa only [inner_sub_right, sub_le_iff_le_add] using h
  · rintro ⟨x, hx, rfl⟩ i
    change ⟪P.normal i, v + x⟫ ≤ P.offset i + ⟪P.normal i, v⟫
    simpa only [inner_add_right, add_comm] using add_le_add_right (hx i) ⟪P.normal i, v⟫

end Paper092.HPolytope

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/FiniteVertices.lean -/
noncomputable section

namespace OAI

universe uι

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Paper092
namespace HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem extreme_active_unique {x y : Euclidean d}
    (hx : x ∈ P.body.extremePoints ℝ)
    (ha : ∀ i, ⟪P.normal i, x⟫ = P.offset i → ⟪P.normal i, y⟫ = P.offset i) :
    y = x := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,
      ⟪P.normal i, x⟫ < P.offset i →
        ⟪P.normal i, x + t • (y - x)⟫ < P.offset i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : ⟪P.normal i, x⟫ < P.offset i
    · have h : ∀ᶠ t : ℝ in 𝓝 0,
          ⟪P.normal i, x + t • (y - x)⟫ < P.offset i :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hi)
      filter_upwards [h] with t ht
      exact fun _ => ht
    · exact Filter.Eventually.of_forall fun _ h => (hi h).elim
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  have hpert (t : ℝ) (ht : dist t 0 < ε) : x + t • (y - x) ∈ P.body := by
    intro i
    rcases (hx.1 i).lt_or_eq with hi | hi
    · exact (hsmall ht i hi).le
    · simp [inner_add_right, inner_smul_right, inner_sub_right, hi, ha i hi]
  have hp : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hm : dist (-(ε / 2)) 0 < ε := by simpa using hp
  have hxplus := hx.2 (hpert (ε / 2) hp)
    (show x - (ε / 2) • (y - x) ∈ P.body by simpa only [neg_smul, ← sub_eq_add_neg] using hpert (-(ε / 2)) hm)
    (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • (y - x)))
  have hz : (ε / 2) • (y - x) = 0 := add_left_cancel (hxplus.trans (add_zero x).symm)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt (half_pos hε)))

theorem finite_extremePoints : (P.body.extremePoints ℝ).Finite := by
  classical
  let active (x : Euclidean d) : Finset ι :=
    Finset.univ.filter (fun i => ⟪P.normal i, x⟫ = P.offset i)
  have hi : Set.InjOn active (P.body.extremePoints ℝ) := by
    intro x hx y _ hxy
    apply (P.extreme_active_unique hx ?_).symm
    intro i hix
    have hm : i ∈ active x := by simp [active, hix]
    rw [hxy] at hm
    exact (Finset.mem_filter.mp hm).2
  exact (Set.toFinite (Set.univ : Set (Finset ι))).of_injOn
    (fun _ _ => Set.mem_univ _) hi

theorem eq_convexHull_extremePoints : P.body = convexHull ℝ (P.body.extremePoints ℝ) := by
  have hc : Convex ℝ P.body := by
    change Convex ℝ {x : Euclidean d | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i}
    simp only [Set.ofPred_forall]
    exact convex_iInter fun i => (convex_Iic (P.offset i)).linear_preimage
      (innerSL ℝ (P.normal i)).toLinearMap
  have h := closure_convexHull_extremePoints P.compact hc
  change closure (convexHull ℝ (P.body.extremePoints ℝ)) = P.body at h
  rw [P.finite_extremePoints.isClosed_convexHull ℝ |>.closure_eq] at h
  exact h.symm

end HPolytope

theorem halfspaces_are_finite_convex_hull {d : ℕ} {ι : Type uι} [Fintype ι]
    (P : HPolytope d ι) :
    ∃ S : Finset (Euclidean d), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  classical
  exact ⟨P.finite_extremePoints.toFinset, by simpa using P.eq_convexHull_extremePoints⟩
end Paper092

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/SupportGeometry.lean -/
noncomputable section

namespace OAI

universe uE uF uι uH

open Set
open scoped Pointwise

namespace Paper092.SupportGeometry

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def support (K : Set E) (f : E →L[ℝ] ℝ) : ℝ := sSup (f '' K)

theorem le_support {K : Set E} (hK : IsCompact K) (f : E →L[ℝ] ℝ)
    {x : E} (hx : x ∈ K) : f x ≤ support K f :=
  le_csSup (hK.image f.continuous).bddAbove (mem_image_of_mem f hx)

theorem support_le {K : Set E} (hK : K.Nonempty) (f : E →L[ℝ] ℝ)
    {a : ℝ} (ha : ∀ x ∈ K, f x ≤ a) : support K f ≤ a :=
  csSup_le (hK.image f) (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)

theorem exists_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →L[ℝ] ℝ) : ∃ x ∈ K, f x = support K f :=
  (hK.image f.continuous).sSup_mem (hne.image f)

theorem support_add {A B : Set E} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) :
    support (A + B) f = support A f + support B f := by
  first
  | obtain ⟨a, ha, hea⟩ := exists_support hA hneA f
    obtain ⟨b, hb, heb⟩ := exists_support hB hneB f
    apply le_antisymm
    · apply support_le (hneA.add hneB) f
      rintro x ⟨u, hu, v, hv, rfl⟩
      simpa only [map_add] using add_le_add (le_support hA f hu) (le_support hB f hv)
    · have h := le_support (hA.add hB) f (show a + b ∈ A + B from ⟨a, ha, b, hb, rfl⟩)
      simpa only [map_add, hea, heb] using h

theorem support_smul (K : Set E) (f : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) :
    support (c • K) f = c * support K f := by
  unfold support
  rw [image_smul_comm f c K (fun x => f.map_smul c x), Real.sSup_smul_of_nonneg hc]
  rfl

theorem support_prod {A : Set E} {B : Set F} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) (g : F →L[ℝ] ℝ) :
    support (A ×ˢ B) (f.coprod g) = support A f + support B g := by
  first
  | obtain ⟨a, ha, hea⟩ := exists_support hA hneA f
    obtain ⟨b, hb, heb⟩ := exists_support hB hneB g
    apply le_antisymm
    · apply support_le (hneA.prod hneB) (f.coprod g)
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      change f u + g v ≤ support A f + support B g
      exact add_le_add (le_support hA f hu) (le_support hB g hv)
    · have h := le_support (hA.prod hB) (f.coprod g)
        (show (a, b) ∈ A ×ˢ B from ⟨ha, hb⟩)
      change f a + g b ≤ support (A ×ˢ B) (f.coprod g) at h
      simpa only [hea, heb] using h

theorem support_sum {ι : Type uι} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hne : ∀ i ∈ s, (K i).Nonempty)
    (f : E →L[ℝ] ℝ) : support (∑ i ∈ s, K i) f = ∑ i ∈ s, support (K i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [support]
  | @insert i s hi ih =>
    have hKs : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hnes : ∀ j ∈ s, (K j).Nonempty := fun j hj => hne j (Finset.mem_insert_of_mem hj)
    have hcompact : IsCompact (∑ j ∈ s, K j) :=
      Finset.sum_induction K IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton hKs
    have hnonempty : (∑ j ∈ s, K j).Nonempty :=
      Finset.sum_induction K Set.Nonempty (fun _ _ ha hb => ha.add hb)
        (singleton_nonempty 0) hnes
    rw [Finset.sum_insert hi,
      support_add (hK i (Finset.mem_insert_self i s)) (hne i (Finset.mem_insert_self i s))
        hcompact hnonempty, ih hKs hnes, Finset.sum_insert hi]

theorem mem_iff_le_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : E} :
    x ∈ K ↔ ∀ f : E →L[ℝ] ℝ, f x ≤ support K f := by
  refine ⟨fun hx f => le_support hK f hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hconv hK.isClosed hx
  exact (hux.trans_le ((h f).trans (support_le hne f fun y hy => (hu y hy).le))).false

theorem eq_of_support_eq {A B : Set E} (hA : IsCompact A) (hneA : A.Nonempty)
    (hconvA : Convex ℝ A) (hB : IsCompact B) (hneB : B.Nonempty)
    (hconvB : Convex ℝ B) (h : ∀ f : E →L[ℝ] ℝ, support A f = support B f) : A = B := by
  ext x
  simp only [mem_iff_le_support hA hneA hconvA, mem_iff_le_support hB hneB hconvB, h]

theorem isCompact_segment (x y : E) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem support_segment (x y : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ x y) f = max (f x) (f y) := by
  unfold support
  rw [show f '' segment ℝ x y = segment ℝ (f x) (f y) from
    image_segment ℝ f.toLinearMap.toAffineMap x y]
  rw [segment_eq_Icc', csSup_Icc (min_le_max)]

theorem support_centered_segment (v : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)) f = |f v| / 2 := by
  simp only [support_segment, map_smul, smul_eq_mul, neg_mul]
  rw [max_comm, ← abs_eq_max_neg, abs_mul]
  norm_num
  ring

theorem support_sum_centered_segments {ι : Type uι} (s : Finset ι) (v : ι → E)
    (f : E →L[ℝ] ℝ) :
    support (∑ i ∈ s, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i)) f =
      (1 / 2 : ℝ) * ∑ i ∈ s, |f (v i)| := by
  rw [support_sum s _ (fun _ _ => isCompact_segment _ _)
    (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)]
  simp_rw [support_centered_segment, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem eq_sum_centered_segments_iff {ι : Type uι} {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) (s : Finset ι) (v : ι → E) :
    K = ∑ i ∈ s, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i) ↔
      ∀ f : E →L[ℝ] ℝ, support K f = (1 / 2 : ℝ) * ∑ i ∈ s, |f (v i)| := by
  constructor
  · intro h f
    rw [h, support_sum_centered_segments]
  · intro h
    apply eq_of_support_eq hK hne hconv
    · exact Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton (fun _ _ => isCompact_segment _ _)
    · exact Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
        (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)
    · exact Finset.sum_induction _ (Convex ℝ) (fun _ _ ha hb => ha.add hb)
        (convex_singleton 0) (fun _ _ => convex_segment _ _)
    · intro f
      rw [h f, support_sum_centered_segments]

section InnerProduct

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem mem_iff_inner_le_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : H} :
    x ∈ K ↔ ∀ u : H, inner ℝ u x ≤ support K (innerSL ℝ u) := by
  rw [mem_iff_le_support hK hne hconv]
  constructor
  · intro h u
    exact h (innerSL ℝ u)
  · intro h f
    obtain ⟨u, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective f
    exact h u

theorem halfSpaces_eq_of_eq_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) (p : H → ℝ) (hp : ∀ u, p u = support K (innerSL ℝ u)) :
    {x | ∀ u : H, inner ℝ u x ≤ p u} = K := by
  ext x
  simp_rw [mem_ofPred_eq, hp]
  exact (mem_iff_inner_le_support hK hne hconv).symm

theorem eq_of_inner_support_eq {A B : Set H} (hA : IsCompact A) (hneA : A.Nonempty)
    (hconvA : Convex ℝ A) (hB : IsCompact B) (hneB : B.Nonempty)
    (hconvB : Convex ℝ B)
    (h : ∀ u : H, support A (innerSL ℝ u) = support B (innerSL ℝ u)) : A = B := by
  ext x
  simp only [mem_iff_inner_le_support hA hneA hconvA,
    mem_iff_inner_le_support hB hneB hconvB, h]

end InnerProduct

end Paper092.SupportGeometry

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/PolarRepresentation.lean -/
noncomputable section

namespace OAI

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section
namespace Paper092

def halfspacePolar {d : ℕ} (K : Set (Euclidean d)) : Set (Euclidean d) :=
  {u | ∀ x ∈ K, ⟪u, x⟫ ≤ 1}

theorem halfspacePolar_convexHull {d : ℕ} (S : Set (Euclidean d)) :
    halfspacePolar (convexHull ℝ S) = halfspacePolar S := by
  ext u
  constructor
  · intro h x hx
    exact h x (subset_convexHull ℝ S hx)
  · intro h x hx
    have hc : Convex ℝ {y : Euclidean d | ⟪u, y⟫ ≤ 1} :=
      (convex_Iic (1 : ℝ)).linear_preimage (innerSL ℝ u).toLinearMap
    exact convexHull_min h hc hx

theorem halfspacePolar_isClosed {d : ℕ} (K : Set (Euclidean d)) :
    IsClosed (halfspacePolar K) := by
  unfold halfspacePolar
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) continuous_const

theorem halfspacePolar_bipolar {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsClosed K) (hc : Convex ℝ K) (h0 : (0 : Euclidean d) ∈ K) :
    halfspacePolar (halfspacePolar K) = K := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    obtain ⟨f, r, hr, hxgt⟩ := geometric_hahn_banach_closed_point hc hK hnot
    have hr0 : 0 < r := by simpa using hr 0 h0
    obtain ⟨u, hu⟩ := (InnerProductSpace.toDual ℝ (Euclidean d)).surjective f
    have hf (z : Euclidean d) : ⟪u, z⟫ = f z := by
      exact congrArg (fun g : StrongDual ℝ (Euclidean d) => g z) hu
    have hp : r⁻¹ • u ∈ halfspacePolar K := by
      intro z hz
      rw [real_inner_smul_left, hf]
      have := mul_le_mul_of_nonneg_left (hr z hz).le (inv_nonneg.mpr hr0.le)
      simpa [hr0.ne'] using this
    have h := hx (r⁻¹ • u) hp
    rw [real_inner_smul_right, real_inner_comm u x, hf] at h
    have hh := mul_le_mul_of_nonneg_left h hr0.le
    have hle : f x ≤ r := by simpa [← mul_assoc, hr0.ne'] using hh
    exact (not_le_of_gt hxgt) hle
  · intro hx u hu
    simpa only [real_inner_comm] using hu x hx

theorem halfspacePolar_isCompact {d : ℕ} {K : Set (Euclidean d)}
    (h0 : (0 : Euclidean d) ∈ interior K) : IsCompact (halfspacePolar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨halfspacePolar_isClosed K, isBounded_iff_forall_norm_le.mpr ⟨2 / r, ?_⟩⟩
  intro y hy
  by_cases hz : y = 0
  · subst y
    simp only [norm_zero]
    positivity
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hz
  have hx : ((r / 2) / ‖y‖) • y ∈ K := by
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos (half_pos hr) hn), div_mul_cancel₀ _ hn.ne']
    linarith
  have h := hy _ hx
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  have heq : (r / 2 / ‖y‖) * ‖y‖ ^ 2 = (r / 2) * ‖y‖ := by field_simp
  rw [heq] at h
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem finite_polar_has_halfspaces {d : ℕ} (S : Finset (Euclidean d))
    (hc : IsCompact (halfspacePolar (S : Set (Euclidean d)))) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = halfspacePolar (S : Set (Euclidean d)) := by
  classical
  let T := S.filter (fun x => x ≠ 0)
  let J := {x // x ∈ T}
  have hn (i : J) : 0 < ‖(i : Euclidean d)‖ :=
    norm_pos_iff.mpr (Finset.mem_filter.mp i.property).2
  have heq : {x : Euclidean d | ∀ i : J,
      ⟪‖(i : Euclidean d)‖⁻¹ • (i : Euclidean d), x⟫ ≤ ‖(i : Euclidean d)‖⁻¹} =
      halfspacePolar (S : Set (Euclidean d)) := by
    ext x
    constructor
    · intro hx y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      let i : J := ⟨y, Finset.mem_filter.mpr ⟨hy, hy0⟩⟩
      have h := mul_le_mul_of_nonneg_left (hx i) (hn i).le
      rw [real_inner_smul_left] at h
      dsimp only [i] at h
      simpa only [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_mul, real_inner_comm] using h
    · intro hx i
      have h := mul_le_mul_of_nonneg_left (hx i (Finset.mem_filter.mp i.property).1)
        (inv_nonneg.mpr (hn i).le)
      rw [real_inner_smul_left]
      simpa only [mul_one, real_inner_comm] using h
  let P : HPolytope d J := {
    normal := fun i => ‖(i : Euclidean d)‖⁻¹ • (i : Euclidean d)
    offset := fun i => ‖(i : Euclidean d)‖⁻¹
    normal_unit := fun i => by simp [norm_smul, (hn i).ne']
    compact := by rw [heq]; exact hc
    strict_feasible := ⟨0, fun i => by simpa using inv_pos.mpr (hn i)⟩
    distinct := by
      intro i j h
      have hnorm : ‖(i : Euclidean d)‖ = ‖(j : Euclidean d)‖ :=
        inv_inj.mp (congrArg Prod.snd h)
      have hv := congrArg Prod.fst h
      apply Subtype.ext
      have hs := congrArg (fun v : Euclidean d => ‖(i : Euclidean d)‖ • v) hv
      simpa only [smul_smul, ← hnorm, mul_inv_cancel₀ (hn i).ne', one_smul] using hs }
  refine ⟨Fintype.card J, P.reindex (Fintype.equivFin J).symm, ?_⟩
  rw [HPolytope.reindex_body]
  exact heq

theorem finite_convex_hull_has_halfspaces_centered {d : ℕ} (S : Finset (Euclidean d))
    (h0 : (0 : Euclidean d) ∈ interior (convexHull ℝ (S : Set (Euclidean d)))) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  have hc : IsCompact (halfspacePolar (S : Set (Euclidean d))) := by
    rw [← halfspacePolar_convexHull]
    exact halfspacePolar_isCompact h0
  obtain ⟨m, P, hP⟩ := finite_polar_has_halfspaces S hc
  obtain ⟨T, hT⟩ := halfspaces_are_finite_convex_hull P
  have heq : halfspacePolar (T : Set (Euclidean d)) = convexHull ℝ (S : Set (Euclidean d)) := by
    calc
      halfspacePolar (T : Set (Euclidean d)) =
          halfspacePolar (convexHull ℝ (T : Set (Euclidean d))) := (halfspacePolar_convexHull _).symm
      _ = halfspacePolar P.body := by rw [hT]
      _ = halfspacePolar (halfspacePolar (S : Set (Euclidean d))) := by rw [hP]
      _ = halfspacePolar (halfspacePolar (convexHull ℝ (S : Set (Euclidean d)))) := by
        rw [halfspacePolar_convexHull]
      _ = convexHull ℝ (S : Set (Euclidean d)) := halfspacePolar_bipolar
        (S.finite_toSet.isClosed_convexHull ℝ) (convex_convexHull ℝ _) (interior_subset h0)
  obtain ⟨n, Q, hQ⟩ := finite_polar_has_halfspaces T
    (by rw [heq]; exact S.finite_toSet.isCompact_convexHull ℝ)
  exact ⟨n, Q, hQ.trans heq⟩

theorem finite_convex_hull_has_halfspaces {d : ℕ} (S : Finset (Euclidean d))
    (hint : (interior (convexHull ℝ (S : Set (Euclidean d)))).Nonempty) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  classical
  obtain ⟨v, hv⟩ := hint
  let S₀ : Finset (Euclidean d) := S.image (fun x => x - v)
  have hS₀ : convexHull ℝ (S₀ : Set (Euclidean d)) =
      (-v) +ᵥ convexHull ℝ (S : Set (Euclidean d)) := by
    dsimp [S₀]
    rw [Finset.coe_image]
    have himage : (fun x : Euclidean d => x - v) '' (S : Set (Euclidean d)) =
        (-v) +ᵥ (S : Set (Euclidean d)) := by
      change (fun x : Euclidean d => x - v) '' (S : Set (Euclidean d)) =
        (fun x => -v + x) '' (S : Set (Euclidean d))
      congr 1
      funext x
      abel
    rw [himage, convexHull_vadd]
  have h0 : (0 : Euclidean d) ∈ interior (convexHull ℝ (S₀ : Set (Euclidean d))) := by
    rw [hS₀, interior_vadd]
    exact ⟨v, hv, by simp⟩
  obtain ⟨m, P, hP⟩ := finite_convex_hull_has_halfspaces_centered S₀ h0
  refine ⟨m, P.translate v, ?_⟩
  rw [HPolytope.translate_body, hP, hS₀]
  simp

end Paper092

end

end OAI
end
end -- closes the original EOF section from source line 24
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeFoundation.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeFacetGeometry.lean -/
section
/-
The exposed-face span and intrinsic-interior arguments below are adapted from
openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0.
Original source files and hashes are retained under vendor/openai-math and
in audit/openai-polytope-provenance.json. Selected original theorem bodies are
preserved verbatim. The active-constraint proof and unit-normal comparison are
new proofs here, avoiding the upstream projection-front and surface-area theory.
-/


@[expose] public section
set_option autoImplicit false

noncomputable section
open Set
open scoped RealInnerProductSpace Pointwise

namespace OAI.Paper092

def exposedFace {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : Set (Euclidean n) :=
  (innerSL ℝ u).toExposed K

@[simp] theorem exposedFace_zero {n : ℕ} (K : Set (Euclidean n)) : exposedFace K 0 = K := by
  first
  | ext x
    simp [exposedFace, ContinuousLinearMap.toExposed]

theorem exposedFace_nonempty {n : ℕ} (K : Set (Euclidean n)) (hK : IsCompact K)
    (hne : K.Nonempty) (u : Euclidean n) : (exposedFace K u).Nonempty := by
  first
  | obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (innerSL ℝ u).continuous.continuousOn
    exact ⟨x, hx, hmax⟩

theorem exposedFace_vectorSpan_le_normalHyperplane {n : ℕ}
    (K : Set (Euclidean n)) (u : Euclidean n) :
    vectorSpan ℝ (exposedFace K u) ≤ normalHyperplane u := by
  first
  | rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪u, x - y⟫ = 0
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (le_antisymm (hy.2 x hx.1) (hx.2 y hy.1))

theorem exposedFace_finrank_le {n : ℕ} (K : Set (Euclidean n))
    {u : Euclidean n} (hu : u ≠ 0) :
    Module.finrank ℝ (vectorSpan ℝ (exposedFace K u)) ≤ n - 1 := by
  first
  | have h := Submodule.finrank_mono (exposedFace_vectorSpan_le_normalHyperplane K u)
    rwa [normalHyperplane_finrank u hu] at h

theorem inner_eq_of_mem_intrinsicInterior {d : ℕ} {S : Set (Euclidean d)}
    {x : Euclidean d} (hx : x ∈ intrinsicInterior ℝ S) (v : Euclidean d)
    (hmax : ∀ z ∈ S, ⟪v, z⟫ ≤ ⟪v, x⟫) :
    ∀ z ∈ S, ⟪v, z⟫ = ⟪v, x⟫ := by
  first
  | obtain ⟨xQ, hxQ, rfl⟩ := mem_intrinsicInterior.mp hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxQ)
    intro z hz
    by_cases hzx : z = xQ.val
    · simp only [hzx]
    let t : ℝ := ε / (2 * ‖xQ.val - z‖)
    have hnorm : 0 < ‖xQ.val - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzx))
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
    let y : affineSpan ℝ S := ⟨xQ.val + t • (xQ.val - z), by
      simpa only [vsub_eq_sub, vadd_eq_add, add_comm] using
        (affineSpan ℝ S).smul_vsub_vadd_mem t xQ.property
          (subset_affineSpan ℝ S hz) xQ.property⟩
    have hyball : y ∈ Metric.ball xQ ε := by
      change dist (xQ.val + t • (xQ.val - z)) xQ.val < ε
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖xQ.val - z‖ = ε / 2 := by
        dsimp [t]
        field_simp
      rw [heq]
      linarith
    have hy : y.val ∈ S := hball hyball
    have hle := hmax y.val hy
    change ⟪v, xQ.val + t • (xQ.val - z)⟫ ≤ ⟪v, xQ.val⟫ at hle
    rw [inner_add_right, real_inner_smul_right, inner_sub_right] at hle
    exact le_antisymm (hmax z hz) (by nlinarith)

namespace HPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι] (P : HPolytope d ι)

theorem body_convex : Convex ℝ P.body := by
  first
  | intro x hx y hy a b ha hb hab i
    simp only [inner_add_right, real_inner_smul_right]
    calc
      a * ⟪P.normal i, x⟫ + b * ⟪P.normal i, y⟫ ≤
          a * P.offset i + b * P.offset i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
          (mul_le_mul_of_nonneg_left (hy i) hb)
      _ = P.offset i := by rw [← add_mul, hab, one_mul]

theorem body_nonempty : P.body.Nonempty := by
  first
  | obtain ⟨x, hx⟩ := P.strict_feasible
    exact ⟨x, fun i => (hx i).le⟩

theorem exists_active_of_mem_exposedFace {u x : Euclidean d} (hu : u ≠ 0)
    (hx : x ∈ exposedFace P.body u) : ∃ i, x ∈ P.face i := by
  first
  | classical
    by_contra hnone
    have hstrict : ∀ i, ⟪P.normal i, x⟫ < P.offset i := by
      intro i
      exact lt_of_le_of_ne (hx.1 i) (fun h => hnone ⟨i, hx.1, h⟩)
    let S : Set (Euclidean d) := ⋂ i, {y | ⟪P.normal i, y⟫ < P.offset i}
    have hS : IsOpen S := isOpen_iInter_of_finite fun i =>
      isOpen_lt (innerSL ℝ (P.normal i)).continuous continuous_const
    have hxS : x ∈ S := mem_iInter.mpr hstrict
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hxS
    have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let t : ℝ := ε / (2 * ‖u‖)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
    have hyball : x + t • u ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖u‖ = ε / 2 := by dsimp [t]; field_simp
      rw [heq]
      linarith
    have hy : x + t • u ∈ P.body :=
      fun i => (mem_iInter.mp (hball hyball) i).le
    have hmax := hx.2 (x + t • u) hy
    change ⟪u, x + t • u⟫ ≤ ⟪u, x⟫ at hmax
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hmax
    have hpos := mul_pos ht (sq_pos_of_pos hnorm)
    linarith

theorem exposedFace_eq_face {u : Euclidean d} (hu : u ≠ 0)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace P.body u)) = d - 1) :
    ∃ i, exposedFace P.body u = P.face i := by
  first
  | have hconv : Convex ℝ (exposedFace P.body u) :=
      (show IsExposed ℝ P.body (exposedFace P.body u) from
        ContinuousLinearMap.toExposed.isExposed).convex P.body_convex
    have hne := exposedFace_nonempty P.body P.compact P.body_nonempty u
    obtain ⟨x, hx⟩ := (intrinsicInterior_nonempty hconv).mpr hne
    have hxF : x ∈ exposedFace P.body u := intrinsicInterior_subset hx
    obtain ⟨i, hxi⟩ := P.exists_active_of_mem_exposedFace hu hxF
    have hinner : ∀ z ∈ exposedFace P.body u, ⟪P.normal i, z⟫ = P.offset i := by
      intro z hz
      apply Eq.trans (inner_eq_of_mem_intrinsicInterior hx (P.normal i) ?_ z hz) hxi.2
      intro y hy
      rw [hxi.2]
      exact hy.1 i
    have hle : vectorSpan ℝ (exposedFace P.body u) ≤ normalHyperplane (P.normal i) := by
      rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, b, hb, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      change ⟪P.normal i, a - b⟫ = 0
      rw [inner_sub_right, hinner a ha, hinner b hb, sub_self]
    have hn : P.normal i ≠ 0 := by
      intro h
      have hnorm := P.normal_unit i
      rw [h, norm_zero] at hnorm
      norm_num at hnorm
    have hspan_i : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane (P.normal i) :=
      Submodule.eq_of_le_of_finrank_eq hle (hdim.trans (normalHyperplane_finrank _ hn).symm)
    have hspan_u : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane u :=
      Submodule.eq_of_le_of_finrank_eq (exposedFace_vectorSpan_le_normalHyperplane P.body u)
        (hdim.trans (normalHyperplane_finrank u hu).symm)
    refine ⟨i, Subset.antisymm (fun z hz => ⟨hz.1, hinner z hz⟩) ?_⟩
    intro y hy
    have hyi : y - x ∈ normalHyperplane (P.normal i) := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, hy.2, hxi.2, sub_self]
    have hyu : y - x ∈ normalHyperplane u := by
      rwa [← hspan_u, hspan_i]
    have heq : ⟪u, y⟫ = ⟪u, x⟫ := by
      have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hyu
      simpa only [inner_sub_right, sub_eq_zero] using h
    refine ⟨hy.1, ?_⟩
    intro z hz
    change ⟪u, z⟫ ≤ ⟪u, y⟫
    rw [heq]
    exact hxF.2 z hz

theorem exists_strict_face_point_of_essential (i : ι)
    (hessential : ¬ ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    ∃ x ∈ P.face i, ∀ j, j ≠ i → ⟪P.normal j, x⟫ < P.offset j := by
  first
  | classical
    push Not at hessential
    obtain ⟨y, hy, hyi⟩ := hessential
    obtain ⟨z, hz⟩ := P.strict_feasible
    have hden : 0 < ⟪P.normal i, y⟫ - ⟪P.normal i, z⟫ := by linarith [hz i]
    let t : ℝ := (P.offset i - ⟪P.normal i, z⟫) /
      (⟪P.normal i, y⟫ - ⟪P.normal i, z⟫)
    have ht0 : 0 < t := div_pos (sub_pos.mpr (hz i)) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    have htmul : t * (⟪P.normal i, y⟫ - ⟪P.normal i, z⟫) =
        P.offset i - ⟪P.normal i, z⟫ := div_mul_cancel₀ _ hden.ne'
    let x := (1 - t) • z + t • y
    have hxi : ⟪P.normal i, x⟫ = P.offset i := by
      dsimp [x]
      simp only [inner_add_right, real_inner_smul_right]
      nlinarith
    have hxj : ∀ j, j ≠ i → ⟪P.normal j, x⟫ < P.offset j := by
      intro j hji
      have hleft := mul_lt_mul_of_pos_left (hz j) (sub_pos.mpr ht1)
      have hright := mul_le_mul_of_nonneg_left (hy j hji) ht0.le
      dsimp [x]
      simp only [inner_add_right, real_inner_smul_right]
      nlinarith
    refine ⟨x, ⟨?_, hxi⟩, hxj⟩
    intro j
    by_cases hji : j = i
    · simpa only [hji, hxi] using le_refl (P.offset i)
    · exact (hxj j hji).le

theorem affineSpan_face_of_essential (i : ι)
    (hessential : ¬ ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    (affineSpan ℝ (P.face i) : Set (Euclidean d)) =
      {y | ⟪P.normal i, y⟫ = P.offset i} := by
  first
  | classical
    let Q : AffineSubspace ℝ (Euclidean d) :=
      (affineSpan ℝ ({P.offset i} : Set ℝ)).comap (innerₛₗ ℝ (P.normal i)).toAffineMap
    have hQ (y : Euclidean d) : y ∈ Q ↔ ⟪P.normal i, y⟫ = P.offset i := by
      simp [Q]
    have hle : affineSpan ℝ (P.face i) ≤ Q := by
      apply affineSpan_le.mpr
      intro y hy
      exact (hQ y).mpr hy.2
    ext y
    constructor
    · exact fun hy => (hQ y).mp (hle hy)
    · intro hy
      change ⟪P.normal i, y⟫ = P.offset i at hy
      change y ∈ affineSpan ℝ (P.face i)
      obtain ⟨x, hx, hxstrict⟩ := P.exists_strict_face_point_of_essential i hessential
      have hxspan : x ∈ affineSpan ℝ (P.face i) := subset_affineSpan ℝ _ hx
      by_cases hxy : y = x
      · simpa only [hxy] using hxspan
      let S : Set (Euclidean d) := ⋂ j : {j : ι // j ≠ i},
        {z | ⟪P.normal j.val, z⟫ < P.offset j.val}
      have hopen : IsOpen S := isOpen_iInter_of_finite fun j =>
        isOpen_lt (innerSL ℝ (P.normal j.val)).continuous continuous_const
      have hxS : x ∈ S := mem_iInter.mpr (fun j => hxstrict j.val j.property)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxS
      have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      let t : ℝ := ε / (2 * ‖y - x‖)
      have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
      let z := x + t • (y - x)
      have hzball : z ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        change ‖x + t • (y - x) - x‖ < ε
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        dsimp [t]
        have heq : ε / (2 * ‖y - x‖) * ‖y - x‖ = ε / 2 := by field_simp
        rw [heq]
        linarith
      have hzS := hball hzball
      have hzi : ⟪P.normal i, z⟫ = P.offset i := by
        dsimp [z]
        simp only [inner_add_right, real_inner_smul_right, inner_sub_right, hy, hx.2,
          sub_self, mul_zero, add_zero]
      have hzface : z ∈ P.face i := by
        refine ⟨?_, hzi⟩
        intro j
        by_cases hji : j = i
        · simpa only [hji, hzi] using le_refl (P.offset i)
        · exact (mem_iInter.mp hzS ⟨j, hji⟩).le
      have hzspan := subset_affineSpan ℝ (P.face i) hzface
      have hmem := (affineSpan ℝ (P.face i)).smul_vsub_vadd_mem t⁻¹ hzspan hxspan hxspan
      have heq : t⁻¹ • (z - x) + x = y := by
        dsimp [z]
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, sub_add_cancel]
      simpa only [vsub_eq_sub, vadd_eq_add, heq] using hmem

/-- The outward unit normal of a genuine exposed facet is one of the finite
halfspace normals. Strict feasibility fixes its orientation. -/
theorem unit_normal_mem_of_exposed_finrank {u : Euclidean d}
    (hu : ‖u‖ = 1)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace P.body u)) = d - 1) :
    ∃ i, u = P.normal i := by
  first
  | have hu0 : u ≠ 0 := by intro h; simpa [h] using hu
    obtain ⟨i, hi⟩ := P.exposedFace_eq_face hu0 hdim
    have hn0 : P.normal i ≠ 0 := by
      intro h
      simpa [h] using P.normal_unit i
    have hFi : vectorSpan ℝ (exposedFace P.body u) ≤ normalHyperplane (P.normal i) := by
      rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, b, hb, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      change ⟪P.normal i, a - b⟫ = 0
      have ha' : a ∈ P.face i := hi ▸ ha
      have hb' : b ∈ P.face i := hi ▸ hb
      rw [inner_sub_right, ha'.2, hb'.2, sub_self]
    have hspan_i : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane (P.normal i) :=
      Submodule.eq_of_le_of_finrank_eq hFi
        (hdim.trans (normalHyperplane_finrank _ hn0).symm)
    have hspan_u : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane u :=
      Submodule.eq_of_le_of_finrank_eq (exposedFace_vectorSpan_le_normalHyperplane _ u)
        (hdim.trans (normalHyperplane_finrank u hu0).symm)
    have hH : normalHyperplane (P.normal i) = normalHyperplane u :=
      hspan_i.symm.trans hspan_u
    have hspan : Submodule.span ℝ {P.normal i} = Submodule.span ℝ {u} := by
      have h := congrArg Submodule.orthogonal hH
      simpa only [normalHyperplane, Submodule.orthogonal_orthogonal] using h
    have humem : u ∈ Submodule.span ℝ {P.normal i} := by
      rw [hspan]
      exact Submodule.subset_span (mem_singleton u)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp humem
    have habs : |c| = 1 := by
      have h := congrArg norm hc
      simpa only [norm_smul, Real.norm_eq_abs, P.normal_unit, hu, mul_one] using h
    obtain ⟨x, hx⟩ := exposedFace_nonempty P.body P.compact P.body_nonempty u
    have hxi : x ∈ P.face i := hi ▸ hx
    obtain ⟨p, hp⟩ := P.strict_feasible
    have hpbody : p ∈ P.body := fun j => (hp j).le
    have hm := hx.2 p hpbody
    change ⟪u, p⟫ ≤ ⟪u, x⟫ at hm
    rw [← hc, real_inner_smul_left, real_inner_smul_left, hxi.2] at hm
    have hdiff : 0 < P.offset i - ⟪P.normal i, p⟫ := sub_pos.mpr (hp i)
    have hc0 : 0 ≤ c := by nlinarith
    have hc1 : c = 1 := by simpa only [abs_of_nonneg hc0] using habs
    refine ⟨i, ?_⟩
    simpa only [hc1, one_smul] using hc.symm

end HPolytope
end OAI.Paper092

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

/-- Every positive weighted sum uses only the finite facet-normal directions of
its unweighted total. The constituent sets may be lower dimensional. -/
theorem positive_sum_facet_normals {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Set (Euclidean d)) (hA : ∀ i, IsCompact (A i))
    (hne : ∀ i, (A i).Nonempty) (P : HPolytope d κ)
    (hP : P.body = ∑ i, A i) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    {u : Euclidean d} (hu : ‖u‖ = 1)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace (∑ i, t i • A i) u)) = d - 1) :
    ∃ i, u = P.normal i := by
  first
  | apply P.unit_normal_mem_of_exposed_finrank hu
    rw [hP]
    change Module.finrank ℝ (vectorSpan ℝ ((innerSL ℝ u).toExposed (∑ i, A i))) = _
    have heq := PolytopeFaces.vectorSpan_exposed_weighted_sum (innerSL ℝ u)
      Finset.univ A t (fun i _ => hA i) (fun i _ => hne i) (fun i _ => ht i)
    rw [← heq]
    exact hdim

end VolumePolynomials.PolytopeGeometry
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 16
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeFacetGeometry.lean -/

/- BEGIN SOURCE: VolumePolynomials/IrredundantHalfspaces.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Removing redundant inequalities from a finite halfspace representation

The finite family of inequalities is reduced by a minimum-cardinality argument.
Its body is preserved exactly. No assumption about the original presentation
being irredundant, or about every listed supporting face being a facet, is made.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace OAI.Paper092.HPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι] (P : HPolytope d ι)

def IsEssential (i : ι) : Prop :=
  ¬ ∀ x : Euclidean d,
    (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i

theorem vectorSpan_face_of_essential (i : ι) (hi : P.IsEssential i) :
    vectorSpan ℝ (P.face i) = normalHyperplane (P.normal i) := by
  first
  | apply le_antisymm
    · rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, y, hy, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      change ⟪P.normal i, x - y⟫ = 0
      rw [inner_sub_right, hx.2, hy.2, sub_self]
    · intro v hv
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential i hi
      have hxspan := subset_affineSpan ℝ (P.face i) hx
      have hvinner := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv
      have hyspan : x + v ∈ affineSpan ℝ (P.face i) := by
        change x + v ∈ (affineSpan ℝ (P.face i) : Set (Euclidean d))
        rw [P.affineSpan_face_of_essential i hi]
        change ⟪P.normal i, x + v⟫ = P.offset i
        rw [inner_add_right, hx.2, hvinner, add_zero]
      have hvdir := (affineSpan ℝ (P.face i)).vsub_mem_direction hyspan hxspan
      simpa only [direction_affineSpan, vsub_eq_sub, add_sub_cancel_left] using hvdir

theorem finrank_face_of_essential (i : ι) (hi : P.IsEssential i) :
    Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1 := by
  first
  | rw [P.vectorSpan_face_of_essential i hi]
    apply normalHyperplane_finrank
    intro h
    simpa [h] using P.normal_unit i

theorem face_eq_exposedFace (i : ι) (hne : (P.face i).Nonempty) :
    P.face i = exposedFace P.body (P.normal i) := by
  first
  | ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro y hy
      change ⟪P.normal i, y⟫ ≤ ⟪P.normal i, x⟫
      rw [hx.2]
      exact hy i
    · intro hx
      obtain ⟨y, hy⟩ := hne
      refine ⟨hx.1, le_antisymm (hx.1 i) ?_⟩
      have h := hx.2 y hy.1
      change ⟪P.normal i, y⟫ ≤ ⟪P.normal i, x⟫ at h
      rwa [hy.2] at h

theorem offset_eq_support (i : ι) (hne : (P.face i).Nonempty) :
    P.offset i = SupportGeometry.support P.body (innerSL ℝ (P.normal i)) := by
  first
  | obtain ⟨x, hx⟩ := hne
    apply le_antisymm
    · have h := SupportGeometry.le_support P.compact (innerSL ℝ (P.normal i)) hx.1
      change ⟪P.normal i, x⟫ ≤ SupportGeometry.support P.body (innerSL ℝ (P.normal i)) at h
      rwa [hx.2] at h
    · exact SupportGeometry.support_le P.body_nonempty _ (fun y hy => hy i)

/-- A subset of the original inequalities with exactly the original body. -/
def RepresentsBody (s : Finset ι) : Prop :=
  ∀ x : Euclidean d, (∀ i ∈ s, ⟪P.normal i, x⟫ ≤ P.offset i) ↔ x ∈ P.body

theorem representsBody_univ : P.RepresentsBody Finset.univ := by
  first
  | intro x
    simp [body]

def restrict (s : Finset ι) (hs : P.RepresentsBody s) : HPolytope d s where
  normal i := P.normal i.val
  offset i := P.offset i.val
  normal_unit i := P.normal_unit i.val
  compact := by
    first
    | convert P.compact using 1
      ext x
      constructor
      · intro hx
        exact (hs x).mp (fun i hi => hx ⟨i, hi⟩)
      · intro hx i
        exact (hs x).mpr hx i.val i.property
  strict_feasible := by
    first
    | obtain ⟨x, hx⟩ := P.strict_feasible
      exact ⟨x, fun i => hx i.val⟩
  distinct := by
    first
    | intro i j h
      apply Subtype.ext
      exact P.distinct h

@[simp] theorem restrict_body (s : Finset ι) (hs : P.RepresentsBody s) :
    (P.restrict s hs).body = P.body := by
  first
  | ext x
    constructor
    · intro hx
      exact (hs x).mp (fun i hi => hx ⟨i, hi⟩)
    · intro hx i
      exact (hs x).mpr hx i.val i.property

/-- A finite halfspace presentation always contains an irredundant subfamily. -/
theorem exists_irredundant_restriction :
    ∃ s : Finset ι, ∃ hs : P.RepresentsBody s,
      ∀ i : s, (P.restrict s hs).IsEssential i := by
  first
  | classical
    have hex : ∃ k : ℕ, ∃ s : Finset ι, P.RepresentsBody s ∧ s.card = k :=
      ⟨Finset.univ.card, Finset.univ, P.representsBody_univ, rfl⟩
    obtain ⟨s, hs, hcard⟩ := Nat.find_spec hex
    have hminimal : ∀ r : Finset ι, P.RepresentsBody r → s.card ≤ r.card := by
      intro r hr
      rw [hcard]
      exact Nat.find_min' hex ⟨r, hr, rfl⟩
    refine ⟨s, hs, ?_⟩
    intro i hi
    change ∀ x : Euclidean d,
      (∀ j : s, j ≠ i → ⟪P.normal j.val, x⟫ ≤ P.offset j.val) →
        ⟪P.normal i.val, x⟫ ≤ P.offset i.val at hi
    have herase : P.RepresentsBody (s.erase i.val) := by
      intro x
      constructor
      · intro hx
        apply (hs x).mp
        intro j hj
        by_cases hji : j = i.val
        · subst j
          apply hi x
          intro k hki
          exact hx k.val (Finset.mem_erase.mpr
            ⟨fun h => hki (Subtype.ext h), k.property⟩)
        · exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
      · intro hx j hj
        exact (hs x).mpr hx j (Finset.mem_of_mem_erase hj)
    exact (not_lt_of_ge (hminimal _ herase)) (Finset.card_erase_lt_of_mem i.property)

theorem exists_irredundant :
    ∃ k : ℕ, ∃ Q : HPolytope d (Fin k),
      Q.body = P.body ∧ ∀ i, Q.IsEssential i := by
  first
  | classical
    obtain ⟨s, hs, he⟩ := P.exists_irredundant_restriction
    let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
    refine ⟨Fintype.card s, (P.restrict s hs).reindex e, ?_, ?_⟩
    · rw [reindex_body, restrict_body]
    · intro i hred
      apply he (e i)
      intro x hx
      apply hred x
      intro j hji
      apply hx (e j)
      exact fun h => hji (e.injective h)

end OAI.Paper092.HPolytope
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/IrredundantHalfspaces.lean -/

/- BEGIN SOURCE: VolumePolynomials/FixedFacetNormals.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# One finite family of normals for every positive Minkowski sum

The proof uses finite V/H representation, removal of redundant inequalities,
and the invariant direction spaces of exposed faces. The resulting halfspace
formula is an exact equality of the original sets for every positive real
assignment of weights. Summands may have arbitrary affine dimension.
-/

noncomputable section
open Set
open scoped Pointwise RealInnerProductSpace BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

theorem IsFiniteHull.has_halfspaces {d : ℕ} {C : Set (Euclidean d)}
    (hC : IsFiniteHull C) (hint : (interior C).Nonempty) :
    ∃ k : ℕ, ∃ P : HPolytope d (Fin k), P.body = C := by
  first
  | obtain ⟨S, rfl⟩ := hC.exists_finset
    exact finite_convex_hull_has_halfspaces S hint

theorem IsFiniteHull.has_irredundant_halfspaces {d : ℕ} {C : Set (Euclidean d)}
    (hC : IsFiniteHull C) (hint : (interior C).Nonempty) :
    ∃ k : ℕ, ∃ P : HPolytope d (Fin k),
      P.body = C ∧ ∀ i, P.IsEssential i := by
  first
  | obtain ⟨k, P, hP⟩ := hC.has_halfspaces hint
    obtain ⟨m, Q, hQ, he⟩ := P.exists_irredundant
    exact ⟨m, Q, hQ.trans hP, he⟩

theorem positive_sum_interior_nonempty_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hc : ∀ i, Convex ℝ (A i)) (hne : ∀ i, (A i).Nonempty)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    (interior (∑ i, t i • A i)).Nonempty ↔ (interior (∑ i, A i)).Nonempty := by
  first
  | have hneA : (∑ i, A i).Nonempty :=
      PolytopeFaces.nonempty_sum Finset.univ A (fun i _ => hne i)
    have hnet : (∑ i, t i • A i).Nonempty :=
      PolytopeFaces.nonempty_sum Finset.univ _ (fun i _ => (hne i).image _)
    have hconvA : Convex ℝ (∑ i, A i) := convex_sum A (fun i _ => hc i)
    have hconvt : Convex ℝ (∑ i, t i • A i) :=
      convex_sum _ (fun i _ => (hc i).smul (t i))
    rw [hconvt.interior_nonempty_iff_affineSpan_eq_top,
      hconvA.interior_nonempty_iff_affineSpan_eq_top,
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E hnet,
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E hneA,
      PolytopeFaces.vectorSpan_weighted_sum Finset.univ A t
        (fun i _ => hne i) (fun i _ => ht i)]

theorem support_positive_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, IsCompact (A i)) (hne : ∀ i, (A i).Nonempty)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) (l : E →L[ℝ] ℝ) :
    SupportGeometry.support (∑ i, t i • A i) l =
      ∑ i, t i * SupportGeometry.support (A i) l := by
  first
  | have hcompact : ∀ i, IsCompact (t i • A i) := fun i =>
      (hA i).image (continuous_const.smul continuous_id)
    have hnonempty : ∀ i, (t i • A i).Nonempty := fun i =>
      (hne i).image (fun x => t i • x)
    rw [SupportGeometry.support_sum Finset.univ (fun i => t i • A i)
      (fun i _ => hcompact i) (fun i _ => hnonempty i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact SupportGeometry.support_smul (A i) l (ht i).le

/-- Every positive sum has precisely the halfspaces determined by the normals
of any fixed H-representation of the unweighted total and its own supports. -/
theorem positive_sum_eq_support_halfspaces
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Set (Euclidean d)) (hA : ∀ i, IsFiniteHull (A i))
    (hne : ∀ i, (A i).Nonempty) (hint : (interior (∑ i, A i)).Nonempty)
    (P : HPolytope d κ) (hP : P.body = ∑ i, A i)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, t i • A i) =
      {x | ∀ i, ⟪P.normal i, x⟫ ≤
        SupportGeometry.support (∑ j, t j • A j) (innerSL ℝ (P.normal i))} := by
  first
  | have hCt := IsFiniteHull.weighted_sum Finset.univ A (fun i _ => hA i) t
    have hnt : (interior (∑ i, t i • A i)).Nonempty :=
      (positive_sum_interior_nonempty_iff A (fun i => (hA i).convex) hne t ht).mpr hint
    obtain ⟨m, Q, hQ, he⟩ := hCt.has_irredundant_halfspaces hnt
    ext x
    constructor
    · intro hx i
      exact SupportGeometry.le_support hCt.isCompact (innerSL ℝ (P.normal i)) hx
    · intro hx
      rw [← hQ]
      intro j
      have hneF : (Q.face j).Nonempty := by
        obtain ⟨y, hy, _⟩ := Q.exists_strict_face_point_of_essential j (he j)
        exact ⟨y, hy⟩
      have hface : Q.face j = exposedFace (∑ i, t i • A i) (Q.normal j) := by
        rw [Q.face_eq_exposedFace j hneF, hQ]
      have hdim : Module.finrank ℝ
          (vectorSpan ℝ (exposedFace (∑ i, t i • A i) (Q.normal j))) = d - 1 := by
        rw [← hface]
        exact Q.finrank_face_of_essential j (he j)
      obtain ⟨i, hi⟩ := positive_sum_facet_normals A (fun i => (hA i).isCompact)
        hne P hP t ht (Q.normal_unit j) hdim
      rw [Q.offset_eq_support j hneF, hQ, hi]
      exact hx i

/-- The fixed halfspace offsets are linear functions of the positive weights. -/
theorem positive_sum_eq_fixed_halfspaces
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Set (Euclidean d)) (hA : ∀ i, IsFiniteHull (A i))
    (hne : ∀ i, (A i).Nonempty) (hint : (interior (∑ i, A i)).Nonempty)
    (P : HPolytope d κ) (hP : P.body = ∑ i, A i)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, t i • A i) =
      {x | ∀ i, ⟪P.normal i, x⟫ ≤
        ∑ j, t j * SupportGeometry.support (A j) (innerSL ℝ (P.normal i))} := by
  first
  | rw [positive_sum_eq_support_halfspaces A hA hne hint P hP t ht]
    congr 1
    funext x
    apply propext
    simp_rw [support_positive_sum A (fun i => (hA i).isCompact) hne t ht]

end VolumePolynomials.PolytopeGeometry

namespace OAI.Paper092.HPolytope

open VolumePolynomials.PolytopeGeometry

theorem normal_injective_of_essential {d : ℕ} {ι : Type*} [Fintype ι]
    (P : HPolytope d ι) (he : ∀ i, P.IsEssential i) : Function.Injective P.normal := by
  first
  | intro i j hij
    have hnei : (P.face i).Nonempty := by
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential i (he i)
      exact ⟨x, hx⟩
    have hnej : (P.face j).Nonempty := by
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential j (he j)
      exact ⟨x, hx⟩
    apply P.distinct
    refine Prod.ext hij ?_
    change P.offset i = P.offset j
    rw [P.offset_eq_support i hnei, P.offset_eq_support j hnej, hij]

end OAI.Paper092.HPolytope
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FixedFacetNormals.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteFacetFamily.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Fixed finite facet functionals in an arbitrary finite-dimensional space

The Euclidean halfspace representation is transported through an actual linear
equivalence. The retained data include nonzero functionals, their distinct
positive rays, the exact halfspace formula, and a relative interior witness on
each facet of the unweighted sum.
-/

noncomputable section
open Set Module
open scoped Pointwise RealInnerProductSpace BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem image_weighted_sum {ι : Type*} [Fintype ι]
    (L : E →ₗ[ℝ] F) (A : ι → Set E) (t : ι → ℝ) :
    L '' (∑ i, t i • A i) = ∑ i, t i • (L '' A i) := by
  first
  | rw [Set.image_finsetSum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Set.image_smul_comm L (t i) (A i) (fun x => L.map_smul (t i) x)

theorem support_image (L : E →L[ℝ] F) (A : Set E) (l : F →L[ℝ] ℝ) :
    SupportGeometry.support (L '' A) l = SupportGeometry.support A (l.comp L) := by
  first
  | unfold SupportGeometry.support
    rw [Set.image_image]
    rfl

structure FixedFacets {ι : Type*} [Fintype ι] (A : ι → Set E) where
  count : ℕ
  normal : Fin count → E →L[ℝ] ℝ
  normal_ne_zero : ∀ i, normal i ≠ 0
  positive_ray_injective : ∀ i j {c : ℝ}, 0 < c → normal i = c • normal j → i = j
  body_eq : ∀ t : ι → ℝ, (∀ j, 0 < t j) →
    (∑ j, t j • A j) =
      {x | ∀ i, normal i x ≤ ∑ j, t j * SupportGeometry.support (A j) (normal i)}
  strict_face_point : ∀ i, ∃ x : E,
    normal i x = ∑ j, SupportGeometry.support (A j) (normal i) ∧
    ∀ k, k ≠ i → normal k x < ∑ j, SupportGeometry.support (A j) (normal k)

/-- This proof-data object is constructed from the actual finite hulls. Its
halfspace identity is a conclusion, not an assumed geometric interface. -/
theorem exists_fixedFacets [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, IsFiniteHull (A i)) (hne : ∀ i, (A i).Nonempty)
    (hint : (interior (∑ i, A i)).Nonempty) : Nonempty (FixedFacets A) := by
  first
  | classical
    let e : E ≃L[ℝ] Euclidean (finrank ℝ E) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    let B : ι → Set (Euclidean (finrank ℝ E)) := fun i => e '' A i
    have hB : ∀ i, IsFiniteHull (B i) := fun i => (hA i).linear_image e.toLinearMap
    have hneB : ∀ i, (B i).Nonempty := fun i => (hne i).image e
    have hsum : (∑ i, B i) = e '' (∑ i, A i) := by
      rw [Set.image_finsetSum]
    have hintB : (interior (∑ i, B i)).Nonempty := by
      rw [hsum]
      change (interior (e.toHomeomorph '' (∑ i, A i))).Nonempty
      rw [← e.toHomeomorph.image_interior]
      exact hint.image e
    have hsumFinite : IsFiniteHull (∑ i, B i) :=
      IsFiniteHull.sum Finset.univ B (fun i _ => hB i)
    obtain ⟨k, P, hP, he⟩ := hsumFinite.has_irredundant_halfspaces hintB
    let l : Fin k → E →L[ℝ] ℝ := fun i => (innerSL ℝ (P.normal i)).comp e.toContinuousLinearMap
    have hsupport (i : Fin k) (j : ι) :
        SupportGeometry.support (B j) (innerSL ℝ (P.normal i)) =
          SupportGeometry.support (A j) (l i) :=
      support_image e.toContinuousLinearMap (A j) (innerSL ℝ (P.normal i))
    have hheight (i : Fin k) : P.offset i =
        ∑ j, SupportGeometry.support (A j) (l i) := by
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential i (he i)
      have hs : SupportGeometry.support P.body (innerSL ℝ (P.normal i)) = P.offset i :=
        (P.offset_eq_support i ⟨x, hx⟩).symm
      rw [← hs, hP, SupportGeometry.support_sum Finset.univ B
        (fun j _ => (hB j).isCompact) (fun j _ => hneB j)]
      exact Finset.sum_congr rfl (fun j _ => hsupport i j)
    refine ⟨⟨k, l, ?_, ?_, ?_, ?_⟩⟩
    · intro i hi
      have h := congrArg (fun f : E →L[ℝ] ℝ => f (e.symm (P.normal i))) hi
      simpa only [l, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply,
        innerSL_apply_apply, real_inner_self_eq_norm_sq, P.normal_unit,
        one_pow, ContinuousLinearMap.zero_apply, one_ne_zero] using h
    · intro i j c hc hij
      have hn : P.normal i = c • P.normal j := by
        apply ext_inner_right ℝ
        intro y
        have h := congrArg (fun f : E →L[ℝ] ℝ => f (e.symm y)) hij
        simpa only [l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, innerSL_apply_apply, real_inner_smul_left] using h
      have hc1 : c = 1 := by
        have h := congrArg norm hn
        simpa only [P.normal_unit, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_one]
          using h.symm
      apply P.normal_injective_of_essential he
      simpa only [hc1, one_smul] using hn
    · intro t ht
      have hBt := positive_sum_eq_fixed_halfspaces B hB hneB hintB P hP t ht
      have himage : e '' (∑ i, t i • A i) = ∑ i, t i • B i := by
        have hecoe : (e.toLinearMap : E → Euclidean (finrank ℝ E)) = e := rfl
        simpa only [B, hecoe]
          using image_weighted_sum e.toLinearMap A t
      ext x
      constructor
      · intro hx i
        have hxB : e x ∈ ∑ j, t j • B j := by
          rw [← himage]
          exact mem_image_of_mem e hx
        rw [hBt] at hxB
        simpa only [hsupport, l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, innerSL_apply_apply]
          using hxB i
      · intro hx
        have hxB : e x ∈ ∑ j, t j • B j := by
          rw [hBt]
          intro i
          simpa only [hsupport, l, ContinuousLinearMap.comp_apply,
            ContinuousLinearEquiv.coe_coe, innerSL_apply_apply]
            using hx i
        rw [← himage] at hxB
        obtain ⟨y, hy, hyx⟩ := hxB
        exact e.injective hyx ▸ hy
    · intro i
      obtain ⟨x, hx, hstrict⟩ := P.exists_strict_face_point_of_essential i (he i)
      refine ⟨e.symm x, ?_, fun j hji => ?_⟩
      · simpa only [l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, innerSL_apply_apply, hheight] using hx.2
      · simpa only [l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, innerSL_apply_apply, hheight] using hstrict j hji

end VolumePolynomials.PolytopeGeometry
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteFacetFamily.lean -/

/- BEGIN SOURCE: VolumePolynomials/ExtrusionTransport.lean -/
section


@[expose] public section

/-!
# Extrusion in volume-preserving product coordinates

This transports the interval-fiber theorem across an actual continuous linear
equivalence preserving the specified measures. It is suitable for the rational
quotient coordinates in Section 7. No relation between a coordinate determinant
and two differently represented spaces is left implicit.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.ProductExtrusion

open PlanarExtrusion

variable {F E : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsLocallyFiniteMeasure (volume : Measure E)]

theorem realVolume_image_of_measurePreserving
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume) (S : Set F) :
    volume.real (T '' S) = volume.real S := by
  have h := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' S)
  rw [Set.preimage_image_eq S T.injective] at h
  exact congrArg ENNReal.toReal h.symm

theorem image_origin_segment (T : F ≃L[ℝ] (ℝ × E)) {v : F}
    (hv : T v = (1, 0)) (t : ℝ) :
    T '' ((fun s : ℝ => s • v) '' Icc 0 t) = horizontal t := by
  rw [Set.image_image]
  ext p
  constructor
  · rintro ⟨s, hs, hsp⟩
    have heq : (s, (0 : E)) = p := by
      simpa only [Function.comp_apply, map_smul, hv, Prod.smul_mk,
        smul_eq_mul, mul_one, smul_zero] using hsp
    rw [← heq]
    exact ⟨hs, rfl⟩
  · rintro ⟨hp, hp0⟩
    refine ⟨p.1, hp, ?_⟩
    change p.2 = 0 at hp0
    simp only [Function.comp_apply, map_smul, hv, Prod.smul_mk,
      smul_eq_mul, mul_one, smul_zero]
    exact Prod.ext rfl hp0.symm

theorem image_origin_segment_nonneg (T : F ≃L[ℝ] (ℝ × E)) {v : F} {c : ℝ}
    (hv : T v = (c, 0)) (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    T '' ((fun s : ℝ => s • v) '' Icc 0 t) = horizontal (t * c) := by
  have himage : T '' ((fun s : ℝ => s • v) '' Icc 0 t) =
      (fun a : ℝ => (a, (0 : E))) '' ((fun s : ℝ => s * c) '' Icc 0 t) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext s
    simp only [Function.comp_apply, map_smul, hv, Prod.smul_mk,
      smul_eq_mul, smul_zero]
  rw [himage, image_mul_right_Icc ht hc]
  simp only [zero_mul]
  ext ⟨x, y⟩
  constructor
  · rintro ⟨s, hs, heq⟩
    rw [← heq]
    exact ⟨hs, rfl⟩
  · rintro ⟨hx, hy⟩
    change y = 0 at hy
    subst y
    exact ⟨x, hx, rfl⟩

/-- The axial component may have any nonnegative length. -/
theorem realVolume_add_origin_segment_nonneg
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F} {c : ℝ}
    (hv : T v = (c, 0)) (hc0 : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
      volume.real C + (t * c) * volume.real (projection (T '' C)) := by
  calc
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
        volume.real (T '' (C + (fun s : ℝ => s • v) '' Icc 0 t)) :=
      (realVolume_image_of_measurePreserving T hT _).symm
    _ = volume.real (T '' C + horizontal (t * c)) := by
      rw [Set.image_add T, image_origin_segment_nonneg T hv hc0 ht]
    _ = volume.real (T '' C) + (t * c) * volume.real (projection (T '' C)) :=
      realVolume_add_horizontal (hC.image T.continuous) (hc.linear_image T.toLinearMap)
        (mul_nonneg ht hc0)
    _ = volume.real C + (t * c) * volume.real (projection (T '' C)) := by
      rw [realVolume_image_of_measurePreserving T hT]

/-- Extrusion by an arbitrary nonnegative interval in a volume-preserving frame. -/
theorem realVolume_add_origin_segment
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F}
    (hv : T v = (1, 0)) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
      volume.real C + t * volume.real (projection (T '' C)) := by
  calc
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
        volume.real (T '' (C + (fun s : ℝ => s • v) '' Icc 0 t)) :=
      (realVolume_image_of_measurePreserving T hT _).symm
    _ = volume.real (T '' C + horizontal t) := by
      rw [Set.image_add T, image_origin_segment T hv]
    _ = volume.real (T '' C) + t * volume.real (projection (T '' C)) :=
      realVolume_add_horizontal (hC.image T.continuous) (hc.linear_image T.toLinearMap) ht
    _ = volume.real C + t * volume.real (projection (T '' C)) := by
      rw [realVolume_image_of_measurePreserving T hT]

theorem centered_segment_eq_singleton_add_origin (v : F) :
    (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2) =
      {(-(1 / 2 : ℝ)) • v} + (fun s : ℝ => s • v) '' Icc 0 1 := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(-(1 / 2 : ℝ)) • v, rfl, (s + 1 / 2) • v, ?_, ?_⟩
    · exact ⟨s + 1 / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
    · change (-(1 / 2 : ℝ)) • v + (s + 1 / 2) • v = s • v
      rw [← add_smul]
      congr 1
      ring
  · rintro ⟨a, ha, b, ⟨s, hs, rfl⟩, rfl⟩
    change a = (-(1 / 2 : ℝ)) • v at ha
    subst a
    refine ⟨s - 1 / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    change (s - 1 / 2) • v = (-(1 / 2 : ℝ)) • v + s • v
    rw [← add_smul]
    congr 1
    ring

theorem realVolume_add_centered_segment_nonneg
    [Measure.IsAddLeftInvariant (volume : Measure F)]
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F} {c : ℝ}
    (hv : T v = (c, 0)) (hc0 : 0 ≤ c) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2)) =
      volume.real C + c * volume.real (projection (T '' C)) := by
  rw [centered_segment_eq_singleton_add_origin, ← add_assoc, add_comm C, add_assoc]
  rw [Set.singleton_add]
  simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
  simpa only [one_mul, measureReal_def] using
    realVolume_add_origin_segment_nonneg T hT hC hc hv hc0 (by norm_num : (0 : ℝ) ≤ 1)

/-- The centered-segment form used for the three quotient projections in Section 7. -/
theorem realVolume_add_centered_segment
    [Measure.IsAddLeftInvariant (volume : Measure F)]
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F}
    (hv : T v = (1, 0)) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2)) =
      volume.real C + volume.real (projection (T '' C)) := by
  rw [centered_segment_eq_singleton_add_origin, ← add_assoc, add_comm C, add_assoc]
  rw [Set.singleton_add]
  simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
  simpa only [one_mul, measureReal_def] using
    realVolume_add_origin_segment T hT hC hc hv (by norm_num : (0 : ℝ) ≤ 1)

end VolumePolynomials.ProductExtrusion
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ExtrusionTransport.lean -/

/- BEGIN SOURCE: VolumePolynomials/PyramidVolume.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Pyramid volume from scaled product fibers

The pyramid is the actual image of a compact base and a closed parameter
interval. Tonelli's theorem and Haar scaling give its volume, including bases
of lower dimension. There is no simplex decomposition or polytope volume axiom.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal

namespace VolumePolynomials.PyramidVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial segments from the origin to a set. -/
def radialHull (A : Set E) : Set E :=
  (fun p : ℝ × E => p.1 • p.2) '' (Icc (0 : ℝ) 1 ×ˢ A)

theorem radialHull_compact {A : Set E} (hA : IsCompact A) : IsCompact (radialHull A) :=
  (isCompact_Icc.prod hA).image (by fun_prop)

theorem image_radialHull {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (A : Set E) :
    L '' radialHull A = radialHull (L '' A) := by
  first
  | ext y
    constructor
    · rintro ⟨z, ⟨⟨r, x⟩, ⟨hr, hx⟩, rfl⟩, rfl⟩
      exact ⟨(r, L x), ⟨hr, ⟨x, hx, rfl⟩⟩, (map_smul L r x).symm⟩
    · rintro ⟨⟨r, z⟩, ⟨hr, ⟨x, hx, rfl⟩⟩, rfl⟩
      exact ⟨r • x, ⟨(r, x), ⟨hr, hx⟩, rfl⟩, map_smul L r x⟩

/-- Unit-height pyramid with its base in the first-coordinate-one hyperplane. -/
def unitPyramid (A : Set E) : Set (ℝ × E) :=
  (fun p : ℝ × E => (p.1, p.1 • p.2)) '' (Icc (0 : ℝ) 1 ×ˢ A)

theorem unitPyramid_compact {A : Set E} (hA : IsCompact A) :
    IsCompact (unitPyramid A) :=
  (isCompact_Icc.prod hA).image (by fun_prop)

theorem unitPyramid_fiber (A : Set E) (s : ℝ) :
    Prod.mk s ⁻¹' unitPyramid A = if s ∈ Icc (0 : ℝ) 1 then s • A else ∅ := by
  first
  | classical
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [if_pos hs]
      ext y
      constructor
      · rintro ⟨⟨r, x⟩, ⟨hr, hx⟩, heq⟩
        have hrs : r = s := congrArg Prod.fst heq
        subst r
        exact ⟨x, hx, congrArg Prod.snd heq⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(s, x), ⟨hs, hx⟩, rfl⟩
    · rw [if_neg hs]
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨⟨r, x⟩, ⟨hr, hx⟩, heq⟩
      have hrs : r = s := congrArg Prod.fst heq
      exact hs (hrs ▸ hr)

/-- The sole scalar integral in the pyramid formula. -/
theorem lintegral_unit_pow (d : ℕ) :
    (∫⁻ s : ℝ in Icc 0 1, ENNReal.ofReal (s ^ d)) =
      ENNReal.ofReal (((d + 1 : ℕ) : ℝ)⁻¹) := by
  first
  | have hi : IntegrableOn (fun s : ℝ => s ^ d) (Icc (0 : ℝ) 1) :=
      (continuous_id.pow d).integrableOn_Icc
    have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun s : ℝ => s ^ d) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact pow_nonneg hs.1 d
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    simp

section Measure

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

theorem unitPyramid_fiber_measure (A : Set E) (s : ℝ) :
    volume (Prod.mk s ⁻¹' unitPyramid A) =
      (Icc (0 : ℝ) 1).indicator
        (fun r => ENNReal.ofReal (r ^ finrank ℝ E) * volume A) s := by
  first
  | classical
    rw [unitPyramid_fiber]
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [if_pos hs, Set.indicator_of_mem hs,
        Measure.addHaar_smul_of_nonneg volume hs.1]
    · simp only [if_neg hs, measure_empty, Set.indicator_of_notMem hs]

/-- Actual product volume of a unit-height pyramid over any compact base. -/
theorem volume_unitPyramid {A : Set E} (hA : IsCompact A) :
    volume (unitPyramid A) =
      ENNReal.ofReal (((finrank ℝ E + 1 : ℕ) : ℝ)⁻¹) * volume A := by
  first
  | calc
      volume (unitPyramid A) = ∫⁻ s : ℝ, volume (Prod.mk s ⁻¹' unitPyramid A) :=
        Measure.prod_apply (unitPyramid_compact hA).measurableSet
      _ = ∫⁻ s : ℝ, (Icc (0 : ℝ) 1).indicator
          (fun r => ENNReal.ofReal (r ^ finrank ℝ E) * volume A) s :=
        lintegral_congr (unitPyramid_fiber_measure A)
      _ = ∫⁻ s : ℝ in Icc 0 1, ENNReal.ofReal (s ^ finrank ℝ E) * volume A :=
        lintegral_indicator measurableSet_Icc _
      _ = (∫⁻ s : ℝ in Icc 0 1, ENNReal.ofReal (s ^ finrank ℝ E)) * volume A :=
        lintegral_mul_const _ (by fun_prop)
      _ = ENNReal.ofReal (((finrank ℝ E + 1 : ℕ) : ℝ)⁻¹) * volume A := by
        rw [lintegral_unit_pow]

theorem realVolume_unitPyramid {A : Set E} (hA : IsCompact A) :
    volume.real (unitPyramid A) =
      (((finrank ℝ E + 1 : ℕ) : ℝ)⁻¹) * volume.real A := by
  first
  | simp only [measureReal_def, volume_unitPyramid hA, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _))]

/-- Scaling only the first coordinate, with no change to the base coordinates. -/
def axisMap (h : ℝ) : (ℝ × E) →ₗ[ℝ] ℝ × E :=
  (h • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).prodMap (LinearMap.id : E →ₗ[ℝ] E)

@[simp] theorem axisMap_apply (h : ℝ) (p : ℝ × E) :
    axisMap h p = (h * p.1, p.2) := rfl

theorem axisMap_det (h : ℝ) : LinearMap.det (axisMap (E := E) h) = h := by
  first
  | simp [axisMap, LinearMap.det_prodMap]

def pyramid (h : ℝ) (A : Set E) : Set (ℝ × E) := axisMap h '' unitPyramid A

theorem pyramid_eq_parametric (h : ℝ) (A : Set E) :
    pyramid h A =
      (fun p : ℝ × E => (h * p.1, p.1 • p.2)) '' (Icc (0 : ℝ) 1 ×ˢ A) := by
  first
  | rw [pyramid, unitPyramid, Set.image_image]
    rfl

theorem radialHull_singleton_prod (h : ℝ) (A : Set E) :
    radialHull ({h} ×ˢ A) = pyramid h A := by
  first
  | rw [pyramid_eq_parametric]
    ext y
    constructor
    · rintro ⟨⟨r, ⟨s, x⟩⟩, ⟨hr, hs, hx⟩, rfl⟩
      change s = h at hs
      subst s
      exact ⟨(r, x), ⟨hr, hx⟩, Prod.ext (mul_comm h r) rfl⟩
    · rintro ⟨⟨r, x⟩, ⟨hr, hx⟩, rfl⟩
      exact ⟨(r, (h, x)), ⟨hr, rfl, hx⟩, Prod.ext (mul_comm r h) rfl⟩

theorem pyramid_compact {A : Set E} (hA : IsCompact A) (h : ℝ) :
    IsCompact (pyramid h A) :=
  (unitPyramid_compact hA).image (axisMap (E := E) h).continuous_of_finiteDimensional

/-- The height may be positive, negative, or zero. -/
theorem realVolume_pyramid {A : Set E} (hA : IsCompact A) (h : ℝ) :
    volume.real (pyramid h A) =
      (|h| / ((finrank ℝ E + 1 : ℕ) : ℝ)) * volume.real A := by
  first
  | change (volume (axisMap (E := E) h '' unitPyramid A)).toReal = _
    rw [Measure.addHaar_image_linearMap volume (axisMap (E := E) h), axisMap_det,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg h)]
    change |h| * volume.real (unitPyramid A) = _
    rw [realVolume_unitPyramid hA]
    ring

theorem realVolume_pyramid_nonneg {A : Set E} (hA : IsCompact A) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (pyramid h A) =
      (h / ((finrank ℝ E + 1 : ℕ) : ℝ)) * volume.real A := by
  first
  | simpa only [abs_of_nonneg hh] using realVolume_pyramid hA h

/-- A pyramid over an arbitrary compact subset of a coordinate hyperplane,
transported through an actual volume-preserving linear frame. -/
theorem realVolume_radialHull_of_frame
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace F] [BorelSpace F]
    (T : F ≃L[ℝ] ℝ × E) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) {h : ℝ}
    (hplane : ∀ x ∈ C, (T x).1 = h) :
    volume.real (radialHull C) =
      (|h| / ((finrank ℝ E + 1 : ℕ) : ℝ)) * volume.real (Prod.snd '' (T '' C)) := by
  first
  | have himage : T '' C = {h} ×ˢ (Prod.snd '' (T '' C)) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hplane x hx, ⟨T x, ⟨x, hx, rfl⟩, rfl⟩⟩
      · rintro ⟨hp, ⟨q, ⟨x, hx, rfl⟩, hq⟩⟩
        change p.1 = h at hp
        refine ⟨x, hx, Prod.ext ?_ hq⟩
        exact (hplane x hx).trans hp.symm
    calc
      volume.real (radialHull C) = volume.real (T '' radialHull C) :=
        (ProductExtrusion.realVolume_image_of_measurePreserving T hT _).symm
      _ = volume.real (radialHull (T '' C)) := by
        exact congrArg volume.real (image_radialHull T.toLinearMap C)
      _ = volume.real (pyramid h (Prod.snd '' (T '' C))) := by
        exact congrArg volume.real ((congrArg radialHull himage).trans
          (radialHull_singleton_prod h (Prod.snd '' (T '' C))))
      _ = _ := realVolume_pyramid ((hC.image T.continuous).image continuous_snd) h

/-- The same formula for an arbitrary continuous linear frame. Its fixed
positive Haar scalar is explicit, so no measure-preservation hypothesis is
needed. -/
theorem realVolume_radialHull_of_equiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
    [IsAddHaarMeasure (volume : Measure F)]
    (T : F ≃L[ℝ] ℝ × E) {C : Set F} (hC : IsCompact C) {h : ℝ}
    (hplane : ∀ x ∈ C, (T x).1 = h) :
    volume.real (radialHull C) =
      ((LinearFrame.volumeFactor T : ℝ) * |h| / ((finrank ℝ E + 1 : ℕ) : ℝ)) *
        volume.real (Prod.snd '' (T '' C)) := by
  first
  | have himage : T '' C = {h} ×ˢ (Prod.snd '' (T '' C)) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hplane x hx, ⟨T x, ⟨x, hx, rfl⟩, rfl⟩⟩
      · rintro ⟨hp, ⟨q, ⟨x, hx, rfl⟩, hq⟩⟩
        change p.1 = h at hp
        refine ⟨x, hx, Prod.ext ?_ hq⟩
        exact (hplane x hx).trans hp.symm
    rw [LinearFrame.realVolume_eq_factor_mul_image T]
    have himageRadial : T '' radialHull C = radialHull (T '' C) :=
      image_radialHull T.toLinearMap C
    rw [himageRadial]
    have hrad := (congrArg radialHull himage).trans
      (radialHull_singleton_prod h (Prod.snd '' (T '' C)))
    rw [hrad, realVolume_pyramid ((hC.image T.continuous).image continuous_snd) h]
    ring

theorem frame_pyramid_constant_pos
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
    [IsAddHaarMeasure (volume : Measure F)] (T : F ≃L[ℝ] ℝ × E) :
    0 < (LinearFrame.volumeFactor T : ℝ) / ((finrank ℝ E + 1 : ℕ) : ℝ) := by
  first
  | apply div_pos
    · exact_mod_cast LinearFrame.volumeFactor_pos T
    · positivity

end Measure
end VolumePolynomials.PyramidVolume
end -- closes the original EOF section from source line 24
end -- closes the original EOF section from source line 13
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PyramidVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/HalfspacePyramids.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Volume decomposition of a bounded finite halfspace intersection

Inequalities are normalized to `lᵢ x ≤ 1`, so the origin is strictly feasible.
Every nonzero point lies on a radial segment to an active face. Distinct radial
pyramids overlap only in the kernel of a nonzero linear functional, hence in a
Lebesgue-null set. This proves the full facet-pyramid volume identity from set
geometry and measure additivity; no triangulation or divergence theorem is used.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise BigOperators

namespace VolumePolynomials.HalfspacePyramids

open PyramidVolume

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def body (l : ι → E →L[ℝ] ℝ) : Set E := {x | ∀ i, l i x ≤ 1}

def face (l : ι → E →L[ℝ] ℝ) (i : ι) : Set E :=
  {x | x ∈ body l ∧ l i x = 1}

theorem zero_mem_body (l : ι → E →L[ℝ] ℝ) : (0 : E) ∈ body l := by
  first
  | intro i
    simp

theorem face_compact (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) (i : ι) :
    IsCompact (face l i) :=
  hC.inter_right (isClosed_eq (l i).continuous continuous_const)

theorem radialHull_face_subset (l : ι → E →L[ℝ] ℝ) (i : ι) :
    radialHull (face l i) ⊆ body l := by
  first
  | rintro x ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩ j
    change l j (r • y) ≤ 1
    rw [map_smul, smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left (hy.1 j) hr.1).trans (by simpa using hr.2)

/-- Boundedness excludes a nonzero direction on which all defining functionals
are nonpositive, since its entire positive ray would remain in the body. -/
theorem exists_positive_normal (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l))
    {x : E} (hx : x ≠ 0) : ∃ i, 0 < l i x := by
  first
  | by_contra! h
    obtain ⟨R, hR, hbound⟩ := hC.isBounded.exists_pos_norm_le
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let c : ℝ := (R + 1) / ‖x‖
    have hc : 0 < c := div_pos (by linarith) hn
    have hcx : c • x ∈ body l := by
      intro i
      rw [map_smul, smul_eq_mul]
      exact (mul_nonpos_of_nonneg_of_nonpos hc.le (h i)).trans zero_le_one
    have hb := hbound (c • x) hcx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hb
    dsimp only [c] at hb
    rw [div_mul_cancel₀ _ hn.ne'] at hb
    linarith

/-- The maximum active value provides an exact radial representation. -/
theorem mem_radialHull_face_of_ne_zero
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l))
    {x : E} (hx : x ∈ body l) (hx0 : x ≠ 0) :
    ∃ i, x ∈ radialHull (face l i) := by
  first
  | classical
    obtain ⟨j, hj⟩ := exists_positive_normal l hC hx0
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => l i x)
      ⟨j, Finset.mem_univ j⟩
    have hm : 0 < l i x := hj.trans_le (hmax j (Finset.mem_univ j))
    let y : E := (l i x)⁻¹ • x
    have hy : y ∈ face l i := by
      constructor
      · intro k
        change l k ((l i x)⁻¹ • x) ≤ 1
        rw [map_smul, smul_eq_mul]
        have h := mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k))
          (inv_nonneg.mpr hm.le)
        simpa only [inv_mul_cancel₀ hm.ne'] using h
      · change l i ((l i x)⁻¹ • x) = 1
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hm.ne']
    refine ⟨i, (l i x, y), ⟨⟨hm.le, hx i⟩, hy⟩, ?_⟩
    simp only [y, smul_smul, mul_inv_cancel₀ hm.ne', one_smul]

theorem body_subset_radialHull_union_zero
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) :
    body l ⊆ (⋃ i, radialHull (face l i)) ∪ {0} := by
  first
  | intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · obtain ⟨i, hi⟩ := mem_radialHull_face_of_ne_zero l hC hx hx0
      exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)

/-- On the intersection of two radial pyramids the normalized facet functionals
agree. This statement also includes the common apex. -/
theorem radialHull_inter_subset_ker (l : ι → E →L[ℝ] ℝ) (i j : ι) :
    radialHull (face l i) ∩ radialHull (face l j) ⊆
      LinearMap.ker ((l i - l j).toLinearMap) := by
  first
  | rintro x ⟨⟨⟨r, a⟩, ⟨hr, ha⟩, hax⟩, ⟨⟨s, b⟩, ⟨hs, hb⟩, hbx⟩⟩
    have hi : l i x = r := by
      rw [← hax, map_smul, smul_eq_mul, ha.2, mul_one]
    have hj : l j x = s := by
      rw [← hbx, map_smul, smul_eq_mul, hb.2, mul_one]
    have hij : l i x ≤ s := by
      rw [← hbx, map_smul, smul_eq_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb.1 i) hs.1
    have hji : l j x ≤ r := by
      rw [← hax, map_smul, smul_eq_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha.1 j) hr.1
    change l i x - l j x = 0
    linarith

section Measure

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

theorem radialHull_faces_aedisjoint
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l) :
    Pairwise (fun i j => AEDisjoint volume (radialHull (face l i)) (radialHull (face l j))) := by
  first
  | intro i j hij
    change volume (radialHull (face l i) ∩ radialHull (face l j)) = 0
    have hk : LinearMap.ker ((l i - l j).toLinearMap) ≠ ⊤ := by
      intro htop
      apply hij
      apply hl
      ext x
      have hx : x ∈ LinearMap.ker ((l i - l j).toLinearMap) := by
        rw [htop]
        exact Submodule.mem_top
      change l i x - l j x = 0 at hx
      exact sub_eq_zero.mp hx
    exact measure_mono_null (radialHull_inter_subset_ker l i j)
      (Measure.addHaar_submodule volume _ hk)

theorem volume_body_eq_radialHull_union
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) :
    volume (body l) = volume (⋃ i, radialHull (face l i)) := by
  first
  | apply le_antisymm
    · calc
        volume (body l) ≤ volume ((⋃ i, radialHull (face l i)) ∪ {0}) :=
          measure_mono (body_subset_radialHull_union_zero l hC)
        _ ≤ volume (⋃ i, radialHull (face l i)) + volume ({0} : Set E) := measure_union_le _ _
        _ = volume (⋃ i, radialHull (face l i)) := by simp
    · apply measure_mono
      exact iUnion_subset (radialHull_face_subset l)

/-- The full finite pyramid decomposition of actual Lebesgue volume. Redundant
inequalities are allowed; their pyramids automatically have zero volume when
their faces have smaller dimension. -/
theorem realVolume_body_eq_sum_radialHull
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) (hl : Function.Injective l) :
    volume.real (body l) = ∑ i, volume.real (radialHull (face l i)) := by
  first
  | have hmeasure : volume.real (body l) = volume.real (⋃ i, radialHull (face l i)) :=
      congrArg ENNReal.toReal (volume_body_eq_radialHull_union l hC)
    rw [hmeasure]
    classical
    simpa using measureReal_biUnion_finset₀ (μ := volume) (s := Finset.univ)
      (f := fun i => radialHull (face l i))
      (fun i _ j _ hij => radialHull_faces_aedisjoint l hl hij)
      (fun i _ => (radialHull_compact (face_compact l hC i)).measurableSet.nullMeasurableSet)
      (fun i _ => (radialHull_compact (face_compact l hC i)).measure_ne_top)

end Measure
end VolumePolynomials.HalfspacePyramids
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HalfspacePyramids.lean -/

/- BEGIN SOURCE: VolumePolynomials/CenteredFacetFamily.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Centered finite facet families and their genuine lower-dimensional bodies

The height coefficients are supports of the original summands. Containing the
origin makes each one nonnegative; interior of the total makes every positive
weighted height positive. The lower-dimensional bodies are actual projected
exposed faces in the kernels of the facet functionals.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem support_nonneg_of_zero_mem {A : Set E} (hA : IsCompact A)
    (h0 : (0 : E) ∈ A) (l : E →L[ℝ] ℝ) :
    0 ≤ SupportGeometry.support A l := by
  first
  | simpa only [map_zero] using SupportGeometry.le_support hA l h0

theorem support_pos_of_zero_mem_interior {A : Set E} (hA : IsCompact A)
    (h0 : (0 : E) ∈ interior A) (l : E →L[ℝ] ℝ) (hl : l ≠ 0) :
    0 < SupportGeometry.support A l := by
  first
  | obtain ⟨v, hv⟩ := LinearFrame.exists_unit_value l hl
    have hv0 : v ≠ 0 := by intro h; simpa [h] using hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
    let t : ℝ := ε / (2 * ‖v‖)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hn)
    have htv : t • v ∈ A := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖v‖ = ε / 2 := by dsimp [t]; field_simp
      rw [heq]
      linarith
    have h := SupportGeometry.le_support hA l htv
    simp only [map_smul, smul_eq_mul, hv, mul_one] at h
    exact ht.trans_le h

theorem exposed_eq_support_level {A : Set E} (hA : IsCompact A) (hne : A.Nonempty)
    (l : E →L[ℝ] ℝ) :
    l.toExposed A = {x | x ∈ A ∧ l x = SupportGeometry.support A l} := by
  first
  | ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm (SupportGeometry.le_support hA l hx.1)
        (SupportGeometry.support_le hne l hx.2)⟩
    · rintro ⟨hx, heq⟩
      refine ⟨hx, ?_⟩
      intro y hy
      rw [heq]
      exact SupportGeometry.le_support hA l hy

namespace FixedFacets

variable {ι : Type*} [Fintype ι] {A : ι → Set E} (D : FixedFacets A)

def heightCoefficient (i : Fin D.count) (j : ι) : ℝ :=
  SupportGeometry.support (A j) (D.normal i)

def height (t : ι → ℝ) (i : Fin D.count) : ℝ :=
  ∑ j, t j * D.heightCoefficient i j

theorem heightCoefficient_nonneg (hA : ∀ j, IsCompact (A j))
    (h0 : ∀ j, (0 : E) ∈ A j) (i : Fin D.count) (j : ι) :
    0 ≤ D.heightCoefficient i j :=
  support_nonneg_of_zero_mem (hA j) (h0 j) (D.normal i)

theorem height_eq_support (hA : ∀ j, IsCompact (A j))
    (hne : ∀ j, (A j).Nonempty) (t : ι → ℝ) (ht : ∀ j, 0 < t j) (i : Fin D.count) :
    D.height t i = SupportGeometry.support (∑ j, t j • A j) (D.normal i) :=
  (support_positive_sum A hA hne t ht (D.normal i)).symm

theorem height_one_pos (hA : ∀ j, IsCompact (A j))
    (h0 : ∀ j, (0 : E) ∈ A j) (hint : (0 : E) ∈ interior (∑ j, A j))
    (i : Fin D.count) : 0 < ∑ j, D.heightCoefficient i j := by
  first
  | have hcompact : IsCompact (∑ j, A j) :=
      Finset.sum_induction A IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton (fun j _ => hA j)
    have h := support_pos_of_zero_mem_interior hcompact hint (D.normal i) (D.normal_ne_zero i)
    rw [SupportGeometry.support_sum Finset.univ A (fun j _ => hA j)
      (fun j _ => ⟨0, h0 j⟩)] at h
    exact h

theorem height_pos (hA : ∀ j, IsCompact (A j))
    (h0 : ∀ j, (0 : E) ∈ A j) (hint : (0 : E) ∈ interior (∑ j, A j))
    (t : ι → ℝ) (ht : ∀ j, 0 < t j) (i : Fin D.count) : 0 < D.height t i := by
  first
  | have hn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ D.heightCoefficient i j :=
      fun j _ => D.heightCoefficient_nonneg hA h0 i j
    obtain ⟨j, hj, hjpos⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp (D.height_one_pos hA h0 hint i)
    apply (Finset.sum_pos_iff_of_nonneg (fun j _ =>
      mul_nonneg (ht j).le (D.heightCoefficient_nonneg hA h0 i j))).mpr
    exact ⟨j, hj, mul_pos (ht j) hjpos⟩

def normalized (t : ι → ℝ) (i : Fin D.count) : E →L[ℝ] ℝ :=
  (D.height t i)⁻¹ • D.normal i

theorem normalized_le_one_iff (t : ι → ℝ) (i : Fin D.count)
    (hi : 0 < D.height t i) (x : E) :
    D.normalized t i x ≤ 1 ↔ D.normal i x ≤ D.height t i := by
  first
  | change (D.height t i)⁻¹ * D.normal i x ≤ 1 ↔ _
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hi]

theorem normalized_eq_one_iff (t : ι → ℝ) (i : Fin D.count)
    (hi : 0 < D.height t i) (x : E) :
    D.normalized t i x = 1 ↔ D.normal i x = D.height t i := by
  first
  | change (D.height t i)⁻¹ * D.normal i x = 1 ↔ _
    rw [mul_comm, ← div_eq_mul_inv, div_eq_one_iff_eq hi.ne']

theorem normalized_body (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (hheight : ∀ i, 0 < D.height t i) :
    HalfspacePyramids.body (D.normalized t) = ∑ j, t j • A j := by
  first
  | rw [D.body_eq t ht]
    ext x
    change (∀ i, D.normalized t i x ≤ 1) ↔ _
    simp_rw [D.normalized_le_one_iff t _ (hheight _) x]
    rfl

theorem normalized_injective (t : ι → ℝ) (hheight : ∀ i, 0 < D.height t i) :
    Function.Injective (D.normalized t) := by
  first
  | intro i j hij
    apply D.positive_ray_injective i j (div_pos (hheight i) (hheight j))
    have h := congrArg (fun L : E →L[ℝ] ℝ => D.height t i • L) hij
    simpa only [normalized, smul_smul, mul_inv_cancel₀ (hheight i).ne', one_smul,
      ← div_eq_mul_inv] using h

theorem normalized_face (hA : ∀ j, IsCompact (A j))
    (hne : ∀ j, (A j).Nonempty) (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (hheight : ∀ i, 0 < D.height t i) (i : Fin D.count) :
    HalfspacePyramids.face (D.normalized t) i =
      (D.normal i).toExposed (∑ j, t j • A j) := by
  first
  | have hc : IsCompact (∑ j, t j • A j) :=
      Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton (fun j _ => (hA j).image (continuous_const.smul continuous_id))
    have hn : (∑ j, t j • A j).Nonempty :=
      PolytopeFaces.nonempty_sum Finset.univ _ (fun j _ => (hne j).image (fun x => t j • x))
    rw [exposed_eq_support_level hc hn, ← D.height_eq_support hA hne t ht i]
    ext x
    change (x ∈ HalfspacePyramids.body (D.normalized t) ∧ D.normalized t i x = 1) ↔ _
    rw [D.normalized_body t ht hheight, D.normalized_eq_one_iff t i (hheight i) x]
    rfl

end FixedFacets

section KernelBody

variable [FiniteDimensional ℝ E]

def kernelBody (K : ConvexBody E) (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    ConvexBody (LinearMap.ker l.toLinearMap) where
  carrier := LinearFrame.kernelPart l v hv '' l.toExposed (K : Set E)
  convex' := (ContinuousLinearMap.toExposed.isExposed.convex K.convex).linear_image
    (LinearFrame.kernelPart l v hv)
  isCompact' := (ContinuousLinearMap.toExposed.isExposed.isCompact K.isCompact).image
    (LinearFrame.kernelPart l v hv).continuous_of_finiteDimensional
  nonempty' := (PolytopeFaces.exposed_nonempty l K.isCompact K.nonempty).image _

theorem kernelBody_isFiniteHull (K : ConvexBody E) (hK : IsFiniteHull (K : Set E))
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    IsFiniteHull (kernelBody K l v hv : Set (LinearMap.ker l.toLinearMap)) :=
  (hK.exposed l).linear_image (LinearFrame.kernelPart l v hv)

theorem image_exposed_positive_sum {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody E) (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j) :
    Prod.snd '' (LinearFrame.continuousEquiv l v hv ''
      l.toExposed (∑ j, t j • (K j : Set E))) =
        (↑(∑ j, t j • kernelBody (K j) l v hv) : Set (LinearMap.ker l.toLinearMap)) := by
  first
  | rw [Set.image_image]
    change LinearFrame.kernelPart l v hv '' l.toExposed (∑ j, t j • (K j : Set E)) = _
    rw [PolytopeFaces.exposed_weighted_sum l Finset.univ _ t (fun j _ => ht j),
      image_weighted_sum, coe_sum_body]
    apply Finset.sum_congr rfl
    intro j hj
    rfl

end KernelBody
end VolumePolynomials.PolytopeGeometry
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CenteredFacetFamily.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeVolumeDecomposition.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Facet-volume decomposition of positive sums of finite convex hulls

Every entry of the decomposition is built from the given bodies: a nonzero
facet functional, its kernel, a genuine additive Haar measure on that kernel,
and the projected exposed faces of the summands. The volume identity follows
from the exact halfspace representation, disjoint radial pyramids, and Fubini.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

def kernelMeasure (l : E →L[ℝ] ℝ) : Measure (LinearMap.ker l.toLinearMap) :=
  Measure.addHaar

instance kernelMeasure_isAddHaarMeasure (l : E →L[ℝ] ℝ) :
    IsAddHaarMeasure (kernelMeasure l) := by
  first
  | unfold kernelMeasure
    infer_instance

def facetConstant (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) : ℝ :=
  letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
  letI : IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
    kernelMeasure_isAddHaarMeasure l
  (LinearFrame.volumeFactor (LinearFrame.continuousEquiv l v hv) : ℝ) /
    ((finrank ℝ (LinearMap.ker l.toLinearMap) + 1 : ℕ) : ℝ)

theorem facetConstant_pos (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    0 < facetConstant l v hv := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    exact PyramidVolume.frame_pyramid_constant_pos (LinearFrame.continuousEquiv l v hv)

theorem realVolume_radialHull_exposed_sum {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody E) (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (hh : 0 ≤ SupportGeometry.support (∑ j, t j • (K j : Set E)) l) :
    volume.real (PyramidVolume.radialHull (l.toExposed (∑ j, t j • (K j : Set E)))) =
      facetConstant l v hv * SupportGeometry.support (∑ j, t j • (K j : Set E)) l *
        (kernelMeasure l).real
          (↑(∑ j, t j • kernelBody (K j) l v hv) : Set (LinearMap.ker l.toLinearMap)) := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    have hc : IsCompact (∑ j, t j • (K j : Set E)) := by
      simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).isCompact
    have hn : (∑ j, t j • (K j : Set E)).Nonempty := by
      simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).nonempty
    have he : IsExposed ℝ (∑ j, t j • (K j : Set E))
        (l.toExposed (∑ j, t j • (K j : Set E))) := ContinuousLinearMap.toExposed.isExposed
    have hplane : ∀ x ∈ l.toExposed (∑ j, t j • (K j : Set E)),
        (LinearFrame.continuousEquiv l v hv x).1 =
          SupportGeometry.support (∑ j, t j • (K j : Set E)) l := by
      intro x hx
      rw [exposed_eq_support_level hc hn l] at hx
      exact hx.2
    have h := PyramidVolume.realVolume_radialHull_of_equiv
      (LinearFrame.continuousEquiv l v hv) (he.isCompact hc) hplane
    rw [image_exposed_positive_sum K l v hv t ht, abs_of_nonneg hh] at h
    rw [h]
    change ((_ : ℝ) * _ / _) * (kernelMeasure l).real _ = (_ / _) * _ * _
    ring

theorem FixedFacets.volume_decomposition [Nontrivial E]
    {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j)
    (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j) :
    volume.real (↑(∑ j, t j • K j) : Set E) =
      ∑ i, facetConstant (D.normal i) (v i) (hv i) * D.height t i *
        (kernelMeasure (D.normal i)).real
          (↑(∑ j, t j • kernelBody (K j) (D.normal i) (v i) (hv i)) :
            Set (LinearMap.ker (D.normal i).toLinearMap)) := by
  first
  | have hheight : ∀ i, 0 < D.height t i :=
      D.height_pos (fun j => (K j).isCompact) h0 hint t ht
    have hbody := D.normalized_body t ht hheight
    have hc : IsCompact (HalfspacePyramids.body (D.normalized t)) := by
      rw [hbody]
      simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).isCompact
    rw [coe_sum_body]
    change volume.real (∑ j, t j • (K j : Set E)) = _
    rw [← hbody, HalfspacePyramids.realVolume_body_eq_sum_radialHull
      (D.normalized t) hc (D.normalized_injective t hheight)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [D.normalized_face (fun j => (K j).isCompact) (fun j => (K j).nonempty)
      t ht hheight i]
    have hh : 0 ≤ SupportGeometry.support (∑ j, t j • (K j : Set E)) (D.normal i) := by
      rw [← D.height_eq_support (fun j => (K j).isCompact) (fun j => (K j).nonempty) t ht i]
      exact (hheight i).le
    rw [realVolume_radialHull_exposed_sum K (D.normal i) (v i) (hv i) t ht hh,
      ← D.height_eq_support (fun j => (K j).isCompact) (fun j => (K j).nonempty) t ht i]

/-- The complete geometric data needed by induction on dimension. In
particular, the lower-dimensional bodies and their Haar measures are part of
the constructed data, and the identity concerns actual set volume. -/
structure CenteredDecomposition {n : ℕ} (K : Fin n → ConvexBody E) where
  count : ℕ
  kernel : Fin count → Submodule ℝ E
  lowerBody : ∀ i, Fin n → ConvexBody (kernel i)
  lowerMeasure : ∀ i, Measure (kernel i)
  lowerMeasure_haar : ∀ i, IsAddHaarMeasure (lowerMeasure i)
  lowerBody_finite : ∀ i j, IsFiniteHull (lowerBody i j : Set (kernel i))
  lower_finrank : ∀ i, finrank ℝ (kernel i) + 1 = finrank ℝ E
  constant : Fin count → ℝ
  constant_pos : ∀ i, 0 < constant i
  height : Fin count → Fin n → ℝ
  height_nonneg : ∀ i j, 0 ≤ height i j
  volume_identity : ∀ t : Fin n → ℝ, (∀ j, 0 < t j) →
    volume.real (↑(∑ j, t j • K j) : Set E) =
      ∑ i, constant i * (∑ j, t j * height i j) *
        (lowerMeasure i).real (↑(∑ j, t j • lowerBody i j) : Set (kernel i))

/-- Every centered full-dimensional finite-hull tuple has the exact inductive
volume decomposition, with no simplicity or general-position assumption. -/
theorem exists_centeredDecomposition [Nontrivial E] {n : ℕ}
    (K : Fin n → ConvexBody E) (hK : ∀ j, IsFiniteHull (K j : Set E))
    (h0 : ∀ j, (0 : E) ∈ K j)
    (hint : (0 : E) ∈ interior (∑ j, (K j : Set E))) :
    Nonempty (CenteredDecomposition K) := by
  first
  | classical
    obtain ⟨D⟩ := exists_fixedFacets (fun j => (K j : Set E)) hK
      (fun j => (K j).nonempty) ⟨0, hint⟩
    choose v hv using fun i => LinearFrame.exists_unit_value (D.normal i) (D.normal_ne_zero i)
    refine ⟨{
      count := D.count
      kernel := fun i => LinearMap.ker (D.normal i).toLinearMap
      lowerBody := fun i j => kernelBody (K j) (D.normal i) (v i) (hv i)
      lowerMeasure := fun i => kernelMeasure (D.normal i)
      lowerMeasure_haar := fun i => inferInstance
      lowerBody_finite := fun i j => kernelBody_isFiniteHull (K j) (hK j) _ _ _
      lower_finrank := fun i => LinearFrame.finrank_kernel_add_one (D.normal i) (v i) (hv i)
      constant := fun i => facetConstant (D.normal i) (v i) (hv i)
      constant_pos := fun i => facetConstant_pos (D.normal i) (v i) (hv i)
      height := D.heightCoefficient
      height_nonneg := D.heightCoefficient_nonneg (fun j => (K j).isCompact) h0
      volume_identity := fun t ht => D.volume_decomposition K h0 hint v hv t ht
    }⟩

end VolumePolynomials.PolytopeGeometry
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeVolumeDecomposition.lean -/

/- BEGIN SOURCE: VolumePolynomials/VolumePolynomialExistence.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Polynomiality of volume and nonnegative mixed coefficients

The proof is induction on ambient dimension for arbitrary finite convex hulls,
using the actual facet/kernel decomposition. Finite-hull approximation and the
closed evaluation embedding then give the theorem for every tuple of nonempty
compact convex bodies. Degenerate bodies and zero weights are included.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials
open PolytopeGeometry

theorem finiteHull_hasPositiveVolumePolynomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {n : ℕ} (K : Fin n → ConvexBody E)
    (hpoly : ∀ i, IsFiniteHull (K i : Set E)) :
    HasPositiveVolumePolynomial volume K := by
  first
  | classical
    suffices ∀ d, finrank ℝ E = d → HasPositiveVolumePolynomial volume K from this _ rfl
    intro d hdim
    induction d using Nat.strong_induction_on generalizing E with
    | h d ih =>
      cases d with
      | zero =>
          letI : Subsingleton E := Module.finrank_zero_iff.mp hdim
          refine ⟨MvPolynomial.C (volume.real (Set.univ : Set E)), ?_,
            PolynomialNonnegativeCoefficients.C ENNReal.toReal_nonneg, ?_⟩
          · rw [hdim]
            exact MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ)
              (volume.real (Set.univ : Set E))
          · intro t _
            have hset : ((∑ i, t i • K i : ConvexBody E) : Set E) = Set.univ := by
              apply Set.eq_univ_of_forall
              intro x
              obtain ⟨y, hy⟩ := (∑ i, t i • K i : ConvexBody E).nonempty
              exact (Subsingleton.elim y x) ▸ hy
            rw [MvPolynomial.eval_C, hset]
      | succ d =>
          letI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; exact Nat.zero_lt_succ d)
          apply hasPositiveVolumePolynomial_of_centered_case volume ?_ K hpoly
          intro L hL hzero hinterior
          have hint : (0 : E) ∈ interior (∑ i, (L i : Set E)) := by
            simpa only [coe_sum_body] using hinterior
          obtain ⟨D⟩ := exists_centeredDecomposition L hL hzero hint
          have hd : ∀ i, finrank ℝ (D.kernel i) = d := by
            intro i
            exact Nat.add_right_cancel ((D.lower_finrank i).trans hdim)
          have hsmall : ∀ i, HasPositiveVolumePolynomial (D.lowerMeasure i) (D.lowerBody i) := by
            intro i
            letI : MeasureSpace (D.kernel i) := ⟨D.lowerMeasure i⟩
            letI : Measure.IsAddHaarMeasure (volume : Measure (D.kernel i)) := D.lowerMeasure_haar i
            exact ih d (Nat.lt_succ_self d) (K := D.lowerBody i)
              (hpoly := D.lowerBody_finite i) (hd i)
          choose q hqdegree hqcoeff hqvolume using hsmall
          apply hasPositiveVolumePolynomial_of_facets volume L d hdim D.constant
            (fun i => (D.constant_pos i).le) D.height D.height_nonneg q
            (fun i => (hd i) ▸ hqdegree i) hqcoeff
          intro t ht
          rw [D.volume_identity t ht]
          apply Finset.sum_congr rfl
          intro i _
          rw [hqvolume i t (fun j => (ht j).le)]
          congr 2
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- Minkowski's volume polynomial for every tuple and every dimension, with
ordinary monomial coefficients nonnegative and no interior assumption. -/
theorem exists_nonnegative_volume_polynomial {n d : ℕ} (K : Fin n → Body d) :
    ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c := by
  first
  | apply exists_nonnegative_realizes_of_all_finiteHulls n d _ K
    intro L hL
    exact (finiteHull_hasPositiveVolumePolynomial L hL).exists_realizes

theorem exists_volume_polynomial {n d : ℕ} (K : Fin n → Body d) :
    ∃ c : Coefficients n d, Realizes K c := by
  first
  | obtain ⟨c, _, hc⟩ := exists_nonnegative_volume_polynomial K
    exact ⟨c, hc⟩

theorem Realizes.coefficients_nonnegative {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) : ∀ α, 0 ≤ c α := by
  first
  | obtain ⟨c', hn, hc'⟩ := exists_nonnegative_volume_polynomial K
    rw [hc.unique hc']
    exact hn

theorem volumeLocus_coefficients_nonnegative {n d : ℕ} {c : Coefficients n d}
    (hc : c ∈ VolumeLocus n d) : ∀ α, 0 ≤ c α := by
  first
  | obtain ⟨K, hK⟩ := hc
    exact hK.coefficients_nonnegative

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/VolumePolynomialExistence.lean -/

/- BEGIN SOURCE: VolumePolynomials/GenericVolumePolynomial.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Volume polynomials in arbitrary finite-dimensional Haar spaces

An actual continuous linear coordinate equivalence transports a compact
convex tuple to the coordinate space. Haar uniqueness supplies its positive
volume factor. Thus the coordinate-space existence theorem gives the same
polynomial theorem for every specified additive Haar measure.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials

theorem polynomialNonnegativeCoefficients_coefficientPolynomial {n d : ℕ}
    {c : Coefficients n d} (hc : ∀ α, 0 ≤ c α) :
    PolynomialNonnegativeCoefficients (coefficientPolynomial c) := by
  first
  | classical
    intro m
    simp only [coefficientPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    apply Finset.sum_nonneg
    intro α _
    split_ifs <;> first | exact hc α | exact le_rfl

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- General Minkowski polynomiality, with a specified actual Haar measure
and no full-dimensionality assumption on any of the bodies. -/
theorem hasPositiveVolumePolynomial {n : ℕ} (K : Fin n → ConvexBody E) :
    HasPositiveVolumePolynomial μ K := by
  first
  | letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) :=
      inferInstanceAs (Measure.IsAddHaarMeasure μ)
    let e : E ≃L[ℝ] Space (finrank ℝ E) := (Module.finBasis ℝ E).equivFunL
    let L : Fin n → Body (finrank ℝ E) := fun i => mapBody e.toContinuousLinearMap (K i)
    obtain ⟨c, hc, hreal⟩ := exists_nonnegative_volume_polynomial L
    let q := coefficientPolynomial c
    let a : ℝ := LinearFrame.volumeFactor e
    have ha : 0 ≤ a := NNReal.coe_nonneg _
    refine ⟨C a * q, (coefficientPolynomial_homogeneous c).C_mul a,
      (PolynomialNonnegativeCoefficients.C ha).mul
        (polynomialNonnegativeCoefficients_coefficientPolynomial hc), ?_⟩
    intro t ht
    have hm : (∑ i, t i • L i) = mapBody e.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | rw [show mapBody e.toContinuousLinearMap (∑ i, t i • K i) =
          ∑ i, mapBody e.toContinuousLinearMap (t i • K i) from
            map_sum (mapBodyHom e.toContinuousLinearMap) _ _]
        simp only [L, mapBody_smul]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
    change a * MvPolynomial.eval t (coefficientPolynomial c) = _
    rw [← evaluate_eq_polynomial_eval, hreal t ht]
    change a * volume.real
      ((∑ i, t i • L i : ConvexBody (Space (finrank ℝ E))) : Set (Space (finrank ℝ E))) = _
    rw [hm, coe_mapBody]
    exact (LinearFrame.realVolume_eq_factor_mul_image e
      ((∑ i, t i • K i : ConvexBody E) : Set E)).symm

def volumePolynomial {n : ℕ} (K : Fin n → ConvexBody E) : MvPolynomial (Fin n) ℝ :=
  Classical.choose (hasPositiveVolumePolynomial μ K)

theorem volumePolynomial_homogeneous {n : ℕ} (K : Fin n → ConvexBody E) :
    (volumePolynomial μ K).IsHomogeneous (finrank ℝ E) :=
  (Classical.choose_spec (hasPositiveVolumePolynomial μ K)).1

theorem volumePolynomial_nonnegative {n : ℕ} (K : Fin n → ConvexBody E) :
    PolynomialNonnegativeCoefficients (volumePolynomial μ K) :=
  (Classical.choose_spec (hasPositiveVolumePolynomial μ K)).2.1

theorem volumePolynomial_eval {n : ℕ} (K : Fin n → ConvexBody E)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    MvPolynomial.eval t (volumePolynomial μ K) =
      μ.real ((∑ i, t i • K i : ConvexBody E) : Set E) :=
  (Classical.choose_spec (hasPositiveVolumePolynomial μ K)).2.2 t ht

/-- The polynomial is unique from its values on the whole nonnegative
orthant. No assumed coefficient identity is used. -/
theorem volumePolynomial_eq_of_eval {n : ℕ} (K : Fin n → ConvexBody E)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)) :
    volumePolynomial μ K = p := by
  first
  | apply MvPolynomial.funext_set (fun _ => Ici (0 : ℝ)) (fun _ => Ici_infinite 0)
    intro t ht
    exact (volumePolynomial_eval μ K t (fun i => ht i (mem_univ i))).trans
      (hp t (fun i => ht i (mem_univ i))).symm

def genericCoefficientMap {n : ℕ} (K : Fin n → ConvexBody E) :
    Coefficients n (finrank ℝ E) := coefficientsOfPolynomial (volumePolynomial μ K)

theorem coefficientPolynomial_genericCoefficientMap {n : ℕ} (K : Fin n → ConvexBody E) :
    coefficientPolynomial (genericCoefficientMap μ K) = volumePolynomial μ K :=
  coefficientPolynomial_coefficientsOfPolynomial _ (volumePolynomial_homogeneous μ K)

theorem evaluate_genericCoefficientMap {n : ℕ} (K : Fin n → ConvexBody E)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    evaluate (genericCoefficientMap μ K) t =
      μ.real ((∑ i, t i • K i : ConvexBody E) : Set E) := by
  first
  | rw [evaluate_eq_polynomial_eval, coefficientPolynomial_genericCoefficientMap]
    exact volumePolynomial_eval μ K t ht

theorem continuous_genericCoefficientMap (n : ℕ) :
    Continuous (genericCoefficientMap μ (n := n)) := by
  first
  | apply (isClosedEmbedding_evaluation n (finrank ℝ E)).isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro t
    have heq : (fun K : Fin n → ConvexBody E =>
        evaluationEmbedding n (finrank ℝ E) (genericCoefficientMap μ K) t) =
        (fun K => μ.real ((∑ i, t.1 i • K i : ConvexBody E) : Set E)) := by
      first
      | funext K
        exact evaluate_genericCoefficientMap μ K t.1 t.2
    change Continuous (fun K : Fin n → ConvexBody E =>
      evaluationEmbedding n (finrank ℝ E) (genericCoefficientMap μ K) t)
    rw [heq]
    exact (continuous_convexBody_realMeasure μ).comp (by fun_prop)

theorem continuous_volumePolynomial_coeff {n : ℕ} (m : Fin n →₀ ℕ) :
    Continuous (fun K : Fin n → ConvexBody E => (volumePolynomial μ K).coeff m) := by
  first
  | have heq : (fun K : Fin n → ConvexBody E => (volumePolynomial μ K).coeff m) =
        (fun K => (coefficientPolynomial (genericCoefficientMap μ K)).coeff m) := by
      first
      | funext K
        rw [coefficientPolynomial_genericCoefficientMap]
    rw [heq]
    classical
    simp only [coefficientPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    apply continuous_finsetSum Finset.univ
    intro α _
    split_ifs
    · exact (continuous_apply α).comp (continuous_genericCoefficientMap μ n)
    · exact continuous_const

theorem volumePolynomial_translate {n : ℕ} (K : Fin n → ConvexBody E) (v : Fin n → E) :
    volumePolynomial μ (fun i => translateBody (v i) (K i)) = volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • translateBody (v i) (K i)) =
        translateBody (∑ i, t i • v i) (∑ i, t i • K i) := by
      first
      | simp only [translateBody, smul_add, ← pointBody_smul, Finset.sum_add_distrib]
        congr 1
        exact (map_sum (pointBodyHom (E := E)) (fun i => t i • v i) Finset.univ).symm
    rw [hsum, coe_translateBody]
    simp only [measureReal_def, measure_vadd]

end Generic
end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/GenericVolumePolynomial.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedVolume.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Normalized mixed volume of actual convex bodies

The definition extracts the squarefree coefficient of the proved volume
polynomial and divides it by the factorial of the number of arguments.
Its geometric use has exactly as many arguments as the ambient dimension.
It is not an abstract functional supplied with assumed mixed-volume laws.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials

def squarefreeExponent (d : ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem squarefreeExponent_apply (d : ℕ) (i : Fin d) :
    squarefreeExponent d i = 1 := by simp [squarefreeExponent]

theorem squarefreeExponent_sum (d : ℕ) :
    (squarefreeExponent d).sum (fun _ m => m) = d := by
  first
  | rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp

theorem squarefreeExponent_multinomial (d : ℕ) :
    (squarefreeExponent d).multinomial = d.factorial := by
  first
  | rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial]
    simp

theorem squarefreeExponent_mapDomain {d : ℕ} (e : Equiv.Perm (Fin d)) :
    (squarefreeExponent d).mapDomain e = squarefreeExponent d := by
  first
  | ext i
    rw [Finsupp.mapDomain_equiv_apply]
    simp

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolume {d : ℕ} (K : Fin d → ConvexBody E) : ℝ :=
  (volumePolynomial μ K).coeff (squarefreeExponent d) / d.factorial

theorem mixedVolume_nonnegative {d : ℕ} (K : Fin d → ConvexBody E) :
    0 ≤ mixedVolume μ K :=
  div_nonneg (volumePolynomial_nonnegative μ K _) (Nat.cast_nonneg _)

theorem continuous_mixedVolume (d : ℕ) : Continuous (mixedVolume μ (d := d)) :=
  (continuous_volumePolynomial_coeff μ (squarefreeExponent d)).div_const _

theorem mixedVolume_translate {d : ℕ} (K : Fin d → ConvexBody E) (v : Fin d → E) :
    mixedVolume μ (fun i => translateBody (v i) (K i)) = mixedVolume μ K := by
  first
  | simp only [mixedVolume, volumePolynomial_translate]

theorem volumePolynomial_reindex {n : ℕ} (K : Fin n → ConvexBody E)
    (e : Equiv.Perm (Fin n)) :
    volumePolynomial μ (fun i => K (e.symm i)) =
      MvPolynomial.rename e (volumePolynomial μ K) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [MvPolynomial.eval_rename, volumePolynomial_eval μ K (t ∘ e)
      (fun i => ht (e i))]
    congr 2
    exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem mixedVolume_reindex {d : ℕ} (K : Fin d → ConvexBody E)
    (e : Equiv.Perm (Fin d)) : mixedVolume μ (fun i => K (e i)) = mixedVolume μ K := by
  first
  | have h := volumePolynomial_reindex μ K e.symm
    simp only [Equiv.symm_symm] at h
    change (volumePolynomial μ (fun i => K (e i))).coeff _ / _ = _
    rw [h]
    apply congrArg (fun r : ℝ => r / (d.factorial : ℝ))
    simpa only [squarefreeExponent_mapDomain] using
      MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective
        (volumePolynomial μ K) (squarefreeExponent d)

theorem sum_smul_one_body {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → ℝ) (K : ConvexBody E) (hr : ∀ i ∈ s, 0 ≤ r i) :
    (∑ i ∈ s, r i • K) = (∑ i ∈ s, r i) • K := by
  first
  | induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, body_zero_smul]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          ih (fun j hj => hr j (Finset.mem_insert_of_mem hj)),
          body_add_smul K (hr i (Finset.mem_insert_self i s))
            (Finset.sum_nonneg (fun j hj => hr j (Finset.mem_insert_of_mem hj)))]

theorem haar_real_smul_body (K : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    μ.real ((r • K : ConvexBody E) : Set E) = r ^ finrank ℝ E * μ.real (K : Set E) := by
  first
  | simp only [ConvexBody.coe_smul, measureReal_def,
      Measure.addHaar_smul_of_nonneg μ hr (K : Set E), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr _)]

theorem volumePolynomial_diagonal {n : ℕ} (K : ConvexBody E) :
    volumePolynomial μ (fun _ : Fin n => K) =
      C (μ.real (K : Set E)) * (∑ i : Fin n, X i) ^ finrank ℝ E := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [sum_smul_one_body Finset.univ t K (fun i _ => ht i),
      haar_real_smul_body μ K (Finset.sum_nonneg (fun i _ => ht i))]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
      MvPolynomial.eval_sum, MvPolynomial.eval_X]
    exact mul_comm _ _

/-- The normalization agrees with ordinary volume on the diagonal, in the
ambient dimension, including dimension zero. -/
theorem mixedVolume_diagonal {d : ℕ} (hdim : finrank ℝ E = d) (K : ConvexBody E) :
    mixedVolume μ (fun _ : Fin d => K) = μ.real (K : Set E) := by
  first
  | rw [mixedVolume, volumePolynomial_diagonal, hdim, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_sum_X_pow_of_fintype, squarefreeExponent_sum,
      if_pos rfl, squarefreeExponent_multinomial]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast (Nat.factorial_ne_zero d))

/-- Simultaneously scaling the bodies has exactly the ambient volume degree. -/
theorem volumePolynomial_common_smul {n : ℕ} (K : Fin n → ConvexBody E)
    {r : ℝ} (hr : 0 ≤ r) :
    volumePolynomial μ (fun i => r • K i) =
      C (r ^ finrank ℝ E) * volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • (r • K i)) = r • (∑ i, t i • K i) := by
      first
      | rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul, smul_smul, mul_comm]
    rw [hsum, haar_real_smul_body μ _ hr]

theorem mixedVolume_common_smul {d : ℕ} (K : Fin d → ConvexBody E)
    {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume μ (fun i => r • K i) = r ^ finrank ℝ E * mixedVolume μ K := by
  first
  | rw [mixedVolume, volumePolynomial_common_smul μ K hr, MvPolynomial.coeff_C_mul,
      mixedVolume]
    ring

end Generic
end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolynomialMergeCoefficient.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Squarefree coefficients when two variables are identified

Identifying a new variable with one old variable has exactly two preimages
over the squarefree exponent. The resulting coefficient identity supplies
the algebraic additivity step for actual mixed volume.
-/

open MvPolynomial
open scoped BigOperators

namespace VolumePolynomials

theorem coeff_rename_two_preimages {σ τ : Type*}
    (f : σ → τ) (a b : σ →₀ ℕ) (e : τ →₀ ℕ) (hab : a ≠ b)
    (hfiber : ∀ u : σ →₀ ℕ, u.mapDomain f = e ↔ u = a ∨ u = b)
    (p : MvPolynomial σ ℝ) :
    (MvPolynomial.rename f p).coeff e = p.coeff a + p.coeff b := by
  first
  | classical
    induction p using MvPolynomial.induction_on' with
    | monomial u r =>
        simp only [MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial, hfiber]
        by_cases ha : u = a
        · subst u
          simp [hab]
        · by_cases hb : u = b
          · subst u
            simp [ha]
          · simp [ha, hb]
    | add p q hp hq =>
        simp only [map_add, MvPolynomial.coeff_add, hp, hq]
        ring

def mergeIndex {d : ℕ} (i : Fin d) : Fin (d + 1) → Fin d := Fin.cases i id

def oldSquarefreeLift (d : ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons 0 (fun _ : Fin d => 1))

def newSquarefreeLift {d : ℕ} (i : Fin d) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons 1 (fun j : Fin d => if j = i then 0 else 1))

@[simp] theorem oldSquarefreeLift_zero (d : ℕ) : oldSquarefreeLift d 0 = 0 := by
  first
  | simp [oldSquarefreeLift]

@[simp] theorem oldSquarefreeLift_succ {d : ℕ} (j : Fin d) :
    oldSquarefreeLift d j.succ = 1 := by simp [oldSquarefreeLift]

@[simp] theorem newSquarefreeLift_zero {d : ℕ} (i : Fin d) : newSquarefreeLift i 0 = 1 := by
  first
  | simp [newSquarefreeLift]

@[simp] theorem newSquarefreeLift_succ {d : ℕ} (i j : Fin d) :
    newSquarefreeLift i j.succ = if j = i then 0 else 1 := by simp [newSquarefreeLift]

theorem mapDomain_mergeIndex_apply {d : ℕ} (i j : Fin d) (u : Fin (d + 1) →₀ ℕ) :
    u.mapDomain (mergeIndex i) j = (if i = j then u 0 else 0) + u j.succ := by
  first
  | classical
    rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
      Fin.sum_univ_succ]
    simp [mergeIndex, Finsupp.single_apply, eq_comm]

theorem mergeIndex_squarefree_fiber {d : ℕ} (i : Fin d) (u : Fin (d + 1) →₀ ℕ) :
    u.mapDomain (mergeIndex i) = squarefreeExponent d ↔
      u = oldSquarefreeLift d ∨ u = newSquarefreeLift i := by
  first
  | constructor
    · intro h
      have hsum : u 0 + u i.succ = 1 := by
        first
        | have hi := congrArg (fun v : Fin d →₀ ℕ => v i) h
          rw [mapDomain_mergeIndex_apply, if_pos rfl, squarefreeExponent_apply] at hi
          exact hi
      have hothers (j : Fin d) (hj : j ≠ i) : u j.succ = 1 := by
        first
        | simpa only [mapDomain_mergeIndex_apply, if_neg (Ne.symm hj), zero_add,
            squarefreeExponent_apply] using congrArg (fun v : Fin d →₀ ℕ => v j) h
      have hcases : u 0 = 0 ∨ u 0 = 1 := by omega
      rcases hcases with hzero | hone
      · left
        ext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [oldSquarefreeLift_zero] using hzero
        · rw [oldSquarefreeLift_succ]
          by_cases hj : j = i
          · subst j
            omega
          · exact hothers j hj
      · right
        ext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [newSquarefreeLift_zero] using hone
        · rw [newSquarefreeLift_succ]
          by_cases hj : j = i
          · subst j
            rw [if_pos rfl]
            omega
          · rw [if_neg hj]
            exact hothers j hj
    · rintro (rfl | rfl)
      · ext j
        rw [mapDomain_mergeIndex_apply]
        simp
      · ext j
        rw [mapDomain_mergeIndex_apply]
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij, Ne.symm hij]

theorem coeff_mergeIndex_squarefree {d : ℕ} (i : Fin d)
    (p : MvPolynomial (Fin (d + 1)) ℝ) :
    (MvPolynomial.rename (mergeIndex i) p).coeff (squarefreeExponent d) =
      p.coeff (oldSquarefreeLift d) + p.coeff (newSquarefreeLift i) := by
  first
  | apply coeff_rename_two_preimages _ _ _ _ _ (mergeIndex_squarefree_fiber i) p
    intro h
    have hz := congrArg (fun v : Fin (d + 1) →₀ ℕ => v 0) h
    have hzero : (0 : ℕ) = 1 := by
      first
      | simpa only [oldSquarefreeLift_zero, newSquarefreeLift_zero] using hz
    omega

theorem oldSquarefreeLift_eq_mapDomain (d : ℕ) :
    oldSquarefreeLift d = (squarefreeExponent d).mapDomain Fin.succ := by
  first
  | ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [oldSquarefreeLift_zero,
        Finsupp.mapDomain_of_notMem_range _ _ (by
          rintro ⟨i, hi⟩
          exact Fin.succ_ne_zero i hi)]
    · rw [oldSquarefreeLift_succ,
        Finsupp.mapDomain_apply_of_injective (Fin.succ_injective d), squarefreeExponent_apply]

def replaceIndex {d : ℕ} (i : Fin d) (j : Fin d) : Fin (d + 1) :=
  Equiv.swap 0 i.succ j.succ

theorem replaceIndex_injective {d : ℕ} (i : Fin d) : Function.Injective (replaceIndex i) :=
  (Equiv.swap 0 i.succ).injective.comp (Fin.succ_injective d)

@[simp] theorem replaceIndex_self {d : ℕ} (i : Fin d) : replaceIndex i i = 0 := by
  first
  | simp [replaceIndex]

theorem replaceIndex_of_ne {d : ℕ} {i j : Fin d} (hji : j ≠ i) :
    replaceIndex i j = j.succ := by
  first
  | simp [replaceIndex, Equiv.swap_apply_def, hji, Ne.symm hji, Fin.succ_inj]

theorem newSquarefreeLift_eq_mapDomain {d : ℕ} (i : Fin d) :
    newSquarefreeLift i = (squarefreeExponent d).mapDomain (replaceIndex i) := by
  first
  | ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [newSquarefreeLift_zero, ← replaceIndex_self i,
        Finsupp.mapDomain_apply_of_injective (replaceIndex_injective i),
        squarefreeExponent_apply]
    · rw [newSquarefreeLift_succ]
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl]
        symm
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨j, hj⟩
        have h := congrArg (Equiv.swap 0 i.succ) hj
        simp only [replaceIndex, Equiv.swap_apply_self, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero j h
      · rw [if_neg hji, ← replaceIndex_of_ne hji,
          Finsupp.mapDomain_apply_of_injective (replaceIndex_injective i),
          squarefreeExponent_apply]

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolynomialMergeCoefficient.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeMultilinear.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Additivity of actual mixed volume

Selecting a subtuple sets the unused variables to zero. Adding two bodies
identifies their two variables. The squarefree-coefficient calculation then
proves additivity directly from the full volume-polynomial theorem.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials

def extendedWeights {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (t : Fin m → ℝ) (j : Fin n) : ℝ :=
  if h : j ∈ Set.range f then t ((Equiv.ofInjective f hf).symm ⟨j, h⟩) else 0

@[simp] theorem extendedWeights_apply {m n : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) (t : Fin m → ℝ) (i : Fin m) :
    extendedWeights f hf t (f i) = t i := by
  first
  | simp [extendedWeights, Equiv.ofInjective_symm_apply]

theorem extendedWeights_nonnegative {m n : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∀ j, 0 ≤ extendedWeights f hf t j := by
  first
  | intro j
    unfold extendedWeights
    split_ifs <;> first | exact ht _ | exact le_rfl

theorem eval_killCompl {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (t : Fin m → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval t (MvPolynomial.killCompl hf p) =
      MvPolynomial.eval (extendedWeights f hf t) p := by
  first
  | classical
    have h : (MvPolynomial.aeval t : MvPolynomial (Fin m) ℝ →ₐ[ℝ] ℝ).comp
        (MvPolynomial.killCompl hf) =
        MvPolynomial.aeval (extendedWeights f hf t) := by
      first
      | apply MvPolynomial.algHom_ext
        intro j
        simp only [AlgHom.comp_apply, MvPolynomial.killCompl, MvPolynomial.aeval_X]
        unfold extendedWeights
        split_ifs <;> simp only [MvPolynomial.aeval_X, map_zero]
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using
      congrArg (fun q : MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℝ => q p) h

/-- Continuity extends additive nonnegative scalar behavior to every
nonnegative real scalar. The extension to the real line is proved additive
from the positive/negative-part identity. -/
theorem continuous_nonnegative_additive (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : f 0 = 0)
    (hadd : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → f (r + s) = f r + f s)
    {r : ℝ} (hr : 0 ≤ r) : f r = r * f 1 := by
  first
  | have hparts (x : ℝ) : max x 0 - max (-x) 0 = x := by
      first
      | rcases le_total 0 x with hx | hx
        · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
        · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
          ring
    let g : ℝ →+ ℝ :=
      { toFun := fun x => f (max x 0) - f (max (-x) 0)
        map_zero' := by simp only [neg_zero, max_self, hf0, sub_self]
        map_add' := fun x y => by
          have hb : max (x + y) 0 + max (-x) 0 + max (-y) 0 =
              max x 0 + max y 0 + max (-(x + y)) 0 := by
            first
            | linarith [hparts x, hparts y, hparts (x + y)]
          have h := congrArg f hb
          rw [hadd _ _ (add_nonneg (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _),
            hadd _ _ (le_max_right _ _) (le_max_right _ _),
            hadd _ _ (add_nonneg (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _),
            hadd _ _ (le_max_right _ _) (le_max_right _ _)] at h
          linarith }
    have hg : Continuous g :=
      (hf.comp (continuous_id.max continuous_const)).sub
        (hf.comp (continuous_neg.max continuous_const))
    have h := map_real_smul g hg r (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at h
    change f (max r 0) - f (max (-r) 0) =
      r * (f (max 1 0) - f (max (-1) 0)) at h
    simpa only [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr),
      max_eq_left zero_le_one, max_eq_right (by norm_num : (-1 : ℝ) ≤ 0),
      hf0, sub_zero] using h

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem sum_extendedWeights {m n : ℕ} (K : Fin n → ConvexBody E)
    (f : Fin m → Fin n) (hf : Function.Injective f) (t : Fin m → ℝ) :
    (∑ j, extendedWeights f hf t j • K j) = ∑ i, t i • K (f i) := by
  first
  | classical
    calc
      (∑ j, extendedWeights f hf t j • K j) =
          ∑ j ∈ Finset.univ.image f, extendedWeights f hf t j • K j := by
        first
        | symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hj' : j ∉ Set.range f := by
            first
            | rintro ⟨i, hi⟩
              exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
          simp only [extendedWeights, dif_neg hj', body_zero_smul]
      _ = ∑ i, extendedWeights f hf t (f i) • K (f i) :=
        Finset.sum_image (fun i _ j _ h => hf h)
      _ = ∑ i, t i • K (f i) := by simp only [extendedWeights_apply]

theorem volumePolynomial_subtuple {m n : ℕ} (K : Fin n → ConvexBody E)
    (f : Fin m → Fin n) (hf : Function.Injective f) :
    volumePolynomial μ (fun i => K (f i)) =
      MvPolynomial.killCompl hf (volumePolynomial μ K) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [eval_killCompl f hf, volumePolynomial_eval μ K _
      (extendedWeights_nonnegative f hf t ht), sum_extendedWeights K f hf t]

def mergedTuple {d : ℕ} (i : Fin d) (K : Fin (d + 1) → ConvexBody E) :
    Fin d → ConvexBody E := Function.update (fun j => K j.succ) i (K 0 + K i.succ)

theorem sum_mergedTuple {d : ℕ} (i : Fin d) (K : Fin (d + 1) → ConvexBody E)
    (t : Fin d → ℝ) :
    (∑ j, t j • mergedTuple i K j) = ∑ j, t (mergeIndex i j) • K j := by
  first
  | classical
    rw [Fin.sum_univ_succ]
    change (∑ j, t j • mergedTuple i K j) = t i • K 0 + ∑ j, t j • K j.succ
    calc
      (∑ j, t j • mergedTuple i K j) =
          ∑ j, ((if j = i then t i • K 0 else 0) + t j • K j.succ) := by
        first
        | apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [mergedTuple, smul_add]
          · simp [mergedTuple, hji]
      _ = t i • K 0 + ∑ j, t j • K j.succ := by simp [Finset.sum_add_distrib]

theorem volumePolynomial_merge {d : ℕ} (i : Fin d) (K : Fin (d + 1) → ConvexBody E) :
    volumePolynomial μ (mergedTuple i K) =
      MvPolynomial.rename (mergeIndex i) (volumePolynomial μ K) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [MvPolynomial.eval_rename]
    change MvPolynomial.eval (fun j => t (mergeIndex i j)) (volumePolynomial μ K) =
      μ.real (↑(∑ j, t j • mergedTuple i K j) : Set E)
    rw [volumePolynomial_eval μ K _
      (fun j => ht (mergeIndex i j)), sum_mergedTuple i K t]

/-- Additivity in every argument, proved for arbitrary compact convex bodies.
Together with nonnegative scalar homogeneity this is Minkowski multilinearity. -/
theorem mixedVolume_add {d : ℕ} (K : Fin d → ConvexBody E) (i : Fin d)
    (A B : ConvexBody E) :
    mixedVolume μ (Function.update K i (A + B)) =
      mixedVolume μ (Function.update K i A) + mixedVolume μ (Function.update K i B) := by
  first
  | classical
    let L : Fin (d + 1) → ConvexBody E := Fin.cons A (Function.update K i B)
    have hmerged : mergedTuple i L = Function.update K i (A + B) := by
      first
      | funext j
        by_cases hj : j = i
        · subst j
          simp only [mergedTuple, Function.update_self, L, Fin.cons_zero, Fin.cons_succ]
        · simp only [mergedTuple, Function.update_of_ne hj, L, Fin.cons_succ]
    have hold : (fun j : Fin d => L j.succ) = Function.update K i B := by
      first
      | funext j
        simp only [L, Fin.cons_succ]
    have hnew : (fun j : Fin d => L (replaceIndex i j)) = Function.update K i A := by
      first
      | funext j
        by_cases hj : j = i
        · subst j
          simp only [replaceIndex_self, L, Fin.cons_zero, Function.update_self]
        · rw [replaceIndex_of_ne hj]
          simp only [L, Fin.cons_succ, Function.update_of_ne hj]
    have hpoly := volumePolynomial_merge μ i L
    rw [hmerged] at hpoly
    have holdpoly := volumePolynomial_subtuple μ L Fin.succ (Fin.succ_injective d)
    rw [hold] at holdpoly
    have hnewpoly := volumePolynomial_subtuple μ L (replaceIndex i) (replaceIndex_injective i)
    rw [hnew] at hnewpoly
    have holdcoeff : (volumePolynomial μ L).coeff (oldSquarefreeLift d) =
        (volumePolynomial μ (Function.update K i B)).coeff (squarefreeExponent d) := by
      first
      | rw [holdpoly, MvPolynomial.coeff_killCompl, oldSquarefreeLift_eq_mapDomain]
    have hnewcoeff : (volumePolynomial μ L).coeff (newSquarefreeLift i) =
        (volumePolynomial μ (Function.update K i A)).coeff (squarefreeExponent d) := by
      first
      | rw [hnewpoly, MvPolynomial.coeff_killCompl, newSquarefreeLift_eq_mapDomain]
    simp only [mixedVolume, hpoly, coeff_mergeIndex_squarefree, holdcoeff, hnewcoeff]
    ring

theorem mixedVolume_zero_arg {d : ℕ} (K : Fin d → ConvexBody E) (i : Fin d) :
    mixedVolume μ (Function.update K i 0) = 0 := by
  first
  | have h := mixedVolume_add μ K i (0 : ConvexBody E) 0
    rw [zero_add] at h
    linarith

/-- Positive homogeneity in every argument, including scalar zero. -/
theorem mixedVolume_smul {d : ℕ} (K : Fin d → ConvexBody E) (i : Fin d)
    (A : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume μ (Function.update K i (r • A)) =
      r * mixedVolume μ (Function.update K i A) := by
  first
  | let f : ℝ → ℝ := fun t => mixedVolume μ (Function.update K i (t • A))
    have hf : Continuous f := by
      first
      | apply (continuous_mixedVolume μ d).comp
        apply continuous_pi
        intro j
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self, Pi.smul_def', id_eq] using
            (continuous_id.smul continuous_const : Continuous (fun r : ℝ => r • A))
        · simpa only [Function.update_of_ne hji] using
            (continuous_const : Continuous (fun _ : ℝ => K j))
    have hf0 : f 0 = 0 := by
      first
      | dsimp only [f]
        rw [body_zero_smul, mixedVolume_zero_arg]
    have hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → f (s + t) = f s + f t := by
      first
      | intro s t hs ht
        dsimp only [f]
        rw [body_add_smul A hs ht, mixedVolume_add]
    have h := continuous_nonnegative_additive f hf hf0 hadd hr
    simpa only [f, one_smul] using h

end Generic
end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeMultilinear.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeMultilinearMap.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The actual mixed-volume functional as a multilinear map over `ℝ≥0`.
Mathlib's convex bodies form a module over this semiring, so no formal
differences of convex bodies and no negative dilations are introduced. -/

open MeasureTheory Module
open scoped NNReal BigOperators Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolumeMultilinear (d : ℕ) :
    MultilinearMap ℝ≥0 (fun _ : Fin d => ConvexBody E) ℝ :=
  MultilinearMap.mk' (mixedVolume μ)
    (fun K i A B => mixedVolume_add μ K i A B)
    (fun K i r A => by
      first
      | change mixedVolume μ (Function.update K i ((r : ℝ) • A)) =
          (r : ℝ) * mixedVolume μ (Function.update K i A)
        exact mixedVolume_smul μ K i A r.coe_nonneg)

@[simp] theorem mixedVolumeMultilinear_apply {d : ℕ} (K : Fin d → ConvexBody E) :
    mixedVolumeMultilinear μ d K = mixedVolume μ K := rfl

theorem mixedVolume_independent_smul {d : ℕ} (K : Fin d → ConvexBody E)
    (r : Fin d → ℝ) (hr : ∀ i, 0 ≤ r i) :
    mixedVolume μ (fun i => r i • K i) = (∏ i, r i) * mixedVolume μ K := by
  first
  | let c : Fin d → ℝ≥0 := fun i => ⟨r i, hr i⟩
    have h := MultilinearMap.map_smul_univ (mixedVolumeMultilinear μ d) c K
    have hprod : ((∏ i, c i : ℝ≥0) : ℝ) = ∏ i, r i :=
      NNReal.coe_prod Finset.univ c
    change mixedVolume μ (fun i => r i • K i) =
      ((∏ i, c i : ℝ≥0) : ℝ) * mixedVolume μ K at h
    rw [hprod] at h
    exact h

theorem mixedVolume_add_all {d : ℕ} (K L : Fin d → ConvexBody E) :
    mixedVolume μ (fun i => K i + L i) =
      ∑ s : Finset (Fin d), mixedVolume μ (s.piecewise K L) := by
  first
  | have h := MultilinearMap.map_add_univ (mixedVolumeMultilinear μ d) K L
    change mixedVolume μ (K + L) =
      ∑ s : Finset (Fin d), mixedVolume μ (s.piecewise K L) at h
    have he : K + L = (fun i => K i + L i) := rfl
    rw [he] at h
    exact h

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeMultilinearMap.lean -/

/- BEGIN SOURCE: VolumePolynomials/TrivariateMixedVolume.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The exact ten-term cubic expansion of actual three-dimensional volume.
The factors three and six come from expanding the genuine multilinear map.
The planar seven-term specialization is a consequence of zero pure volumes. -/

open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolume3 (A B C : ConvexBody E) : ℝ := mixedVolume μ ![A, B, C]

theorem mixedVolume3_swap_first (A B C : ConvexBody E) :
    mixedVolume3 μ B A C = mixedVolume3 μ A B C := by
  first
  | have h := mixedVolume_reindex μ (![A, B, C] : Fin 3 → ConvexBody E) (Equiv.swap 0 1)
    have heq : (fun i => (![A, B, C] : Fin 3 → ConvexBody E) ((Equiv.swap 0 1) i)) =
        ![B, A, C] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [heq, mixedVolume3] using h

theorem mixedVolume3_swap_last (A B C : ConvexBody E) :
    mixedVolume3 μ A C B = mixedVolume3 μ A B C := by
  first
  | have h := mixedVolume_reindex μ (![A, B, C] : Fin 3 → ConvexBody E) (Equiv.swap 1 2)
    have heq : (fun i => (![A, B, C] : Fin 3 → ConvexBody E) ((Equiv.swap 1 2) i)) =
        ![A, C, B] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [heq, mixedVolume3] using h

theorem mixedVolume3_cycle (A B C : ConvexBody E) :
    mixedVolume3 μ B C A = mixedVolume3 μ A B C := by
  first
  | rw [mixedVolume3_swap_last μ B A C, mixedVolume3_swap_first μ A B C]

theorem mixedVolume3_diagonal (hdim : finrank ℝ E = 3) (A : ConvexBody E) :
    mixedVolume3 μ A A A = μ.real (A : Set E) := by
  first
  | have heq : (![A, A, A] : Fin 3 → ConvexBody E) = fun _ => A := by
      funext i
      fin_cases i <;> rfl
    simpa only [mixedVolume3, heq] using mixedVolume_diagonal μ hdim A

def tripleTupleEquiv (ι : Type*) : (Fin 3 → ι) ≃ ι × (ι × ι) where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl

theorem sum_three_functions {ι : Type*} [Fintype ι] (f : (Fin 3 → ι) → ℝ) :
    (∑ p : Fin 3 → ι, f p) = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
  first
  | classical
    calc
      _ = ∑ p : ι × (ι × ι), f ![p.1, p.2.1, p.2.2] :=
        Fintype.sum_equiv (tripleTupleEquiv ι) _ _ (fun p =>
          congrArg f ((tripleTupleEquiv ι).left_inv p).symm)
      _ = _ := by simp only [Fintype.sum_prod_type]

theorem mixedVolume_weighted_sum_expansion {n d : ℕ}
    (K : Fin n → ConvexBody E) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    mixedVolume μ (fun _ : Fin d => ∑ i, t i • K i) =
      ∑ p : Fin d → Fin n, (∏ j, t (p j)) * mixedVolume μ (fun j => K (p j)) := by
  first
  | have h := (mixedVolumeMultilinear μ d).map_sum (fun (_ : Fin d) (i : Fin n) => t i • K i)
    rw [mixedVolumeMultilinear_apply] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro p _
    exact mixedVolume_independent_smul μ (fun j => K (p j)) (fun j => t (p j)) (fun j => ht (p j))

theorem trivariate_volume_formula (hdim : finrank ℝ E = 3)
    (A B C : ConvexBody E) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    μ.real (a • A + b • B + c • C : Set E) =
      a ^ 3 * μ.real (A : Set E) + b ^ 3 * μ.real (B : Set E) + c ^ 3 * μ.real (C : Set E) +
      3 * a ^ 2 * b * mixedVolume3 μ A A B +
      3 * a ^ 2 * c * mixedVolume3 μ A A C +
      3 * a * b ^ 2 * mixedVolume3 μ B B A +
      3 * b ^ 2 * c * mixedVolume3 μ B B C +
      3 * a * c ^ 2 * mixedVolume3 μ C C A +
      3 * b * c ^ 2 * mixedVolume3 μ C C B +
      6 * a * b * c * mixedVolume3 μ A B C := by
  first
  | let K : Fin 3 → ConvexBody E := ![A, B, C]
    let t : Fin 3 → ℝ := ![a, b, c]
    have ht : ∀ i, 0 ≤ t i := by intro i; fin_cases i <;> assumption
    have h := mixedVolume_weighted_sum_expansion μ (d := 3) K t ht
    rw [mixedVolume_diagonal μ hdim] at h
    rw [sum_three_functions] at h
    have htuple (i j l : Fin 3) : (fun r => K (![i, j, l] r)) = ![K i, K j, K l] := by
      funext r
      fin_cases r <;> rfl
    simp only [Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, htuple] at h
    change μ.real (a • A + b • B + c • C : Set E) = _ at h
    have hAAA := mixedVolume3_diagonal μ hdim A
    have hBBB := mixedVolume3_diagonal μ hdim B
    have hCCC := mixedVolume3_diagonal μ hdim C
    have hABA := mixedVolume3_swap_last μ A A B
    have hBAA := (mixedVolume3_cycle μ A B A).trans hABA
    have hACA := mixedVolume3_swap_last μ A A C
    have hCAA := (mixedVolume3_cycle μ A C A).trans hACA
    have hBAB := mixedVolume3_swap_last μ B B A
    have hABB := (mixedVolume3_cycle μ B A B).trans hBAB
    have hBCB := mixedVolume3_swap_last μ B B C
    have hCBB := (mixedVolume3_cycle μ B C B).trans hBCB
    have hCAC := mixedVolume3_swap_last μ C C A
    have hACC := (mixedVolume3_cycle μ C A C).trans hCAC
    have hCBC := mixedVolume3_swap_last μ C C B
    have hBCC := (mixedVolume3_cycle μ C B C).trans hCBC
    have hACB := mixedVolume3_swap_last μ A B C
    have hBAC := mixedVolume3_swap_first μ A B C
    have hBCA := mixedVolume3_cycle μ A B C
    have hCAB : mixedVolume3 μ C A B = mixedVolume3 μ A B C :=
      (mixedVolume3_cycle μ B C A).trans hBCA
    have hCBA : mixedVolume3 μ C B A = mixedVolume3 μ A B C :=
      (mixedVolume3_swap_first μ B C A).trans hBCA
    change mixedVolume μ ![A, A, A] = μ.real (A : Set E) at hAAA
    dsimp only [mixedVolume3] at hBBB hCCC hABA hBAA hACA hCAA hBAB hABB hBCB hCBB
    dsimp only [mixedVolume3] at hCAC hACC hCBC hBCC hACB hBAC hBCA hCAB hCBA ⊢
    dsimp only [K, t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    simp only [Matrix.head_cons, Matrix.tail_cons] at h
    rw [hAAA, hBBB, hCCC, hABA, hBAA, hACA, hCAA, hBAB, hABB, hBCB, hCBB,
      hCAC, hACC, hCBC, hBCC, hACB, hBAC, hBCA, hCAB, hCBA] at h
    rw [h]
    ring

theorem trivariate_volume_formula_planar (hdim : finrank ℝ E = 3)
    (A B C : ConvexBody E) (hA : μ.real (A : Set E) = 0)
    (hB : μ.real (B : Set E) = 0) (hC : μ.real (C : Set E) = 0)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    μ.real (a • A + b • B + c • C : Set E) =
      3 * a ^ 2 * b * mixedVolume3 μ A A B +
      3 * a ^ 2 * c * mixedVolume3 μ A A C +
      3 * a * b ^ 2 * mixedVolume3 μ B B A +
      3 * b ^ 2 * c * mixedVolume3 μ B B C +
      3 * a * c ^ 2 * mixedVolume3 μ C C A +
      3 * b * c ^ 2 * mixedVolume3 μ C C B +
      6 * a * b * c * mixedVolume3 μ A B C := by
  first
  | simpa only [hA, hB, hC, mul_zero, zero_add] using
      trivariate_volume_formula μ hdim A B C ha hb hc

end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/TrivariateMixedVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/CommonLineVolume.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # Actual volume identities in compatible common-line coordinates

Every pair uses the same intrinsic coordinates on each plane. Its actual
Haar factor appears in both repeated coefficients, so no determinant or
angular factor is postulated. Fiber integrability follows from Fubini on
the images of the actual total compact convex body.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.CommonLineVolume

abbrev Plane := ℝ × ℝ
abbrev ProductThree := ℝ × Plane

def area (A : ConvexBody Plane) : ℝ := volume.real (A : Set Plane)
def width (A : ConvexBody Plane) : ℝ :=
  volume.real (PlanarExtrusion.projection (A : Set Plane))

theorem pair_volume
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (A B : ConvexBody Plane) :
    volume.real (mapBody f A + mapBody g B : Set (Space 3)) =
      (LinearFrame.volumeFactor T : ℝ) *
        (area A * width B + width A * area B) := by
  first
  | have himage : T '' (mapBody f A + mapBody g B : Set (Space 3)) =
        CrossPlaneVolume.planeSum (A : Set Plane) (B : Set Plane) := by
      change T '' (f '' (A : Set Plane) + g '' (B : Set Plane)) = _
      rw [Set.image_add T, Set.image_image, Set.image_image]
      apply congrArg₂ (· + ·)
      · exact Set.image_congr (fun p _ => hf p)
      · exact Set.image_congr (fun p _ => hg p)
    have hv := LinearFrame.realVolume_eq_factor_mul_image T
      (mapBody f A + mapBody g B : Set (Space 3))
    rw [himage, CrossPlaneVolume.realVolume_planeSum
      A.isCompact B.isCompact A.convex B.convex] at hv
    exact hv

theorem pair_volume_smul
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (A B : ConvexBody Plane) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume.real (a • mapBody f A + b • mapBody g B : Set (Space 3)) =
      (LinearFrame.volumeFactor T : ℝ) *
        (area A * width B * a ^ 2 * b + width A * area B * a * b ^ 2) := by
  first
  | have h := pair_volume T f g hf hg (a • A) (b • B)
    rw [mapBody_smul, mapBody_smul] at h
    calc
      _ = (LinearFrame.volumeFactor T : ℝ) *
          (area (a • A) * width (b • B) + width (a • A) * area (b • B)) := h
      _ = _ := by
        simp only [area, width, ConvexBody.coe_smul, CrossPlaneVolume.projection_smul,
          CrossPlaneVolume.realVolume_smul_plane _ ha,
          CrossPlaneVolume.realVolume_smul_plane _ hb,
          CrossPlaneVolume.realVolume_smul_line _ ha,
          CrossPlaneVolume.realVolume_smul_line _ hb]
        ring

theorem pair_repeated_coefficients
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (A B : ConvexBody Plane) :
    3 * mixedVolume3 volume (mapBody f A) (mapBody f A) (mapBody g B) =
      (LinearFrame.volumeFactor T : ℝ) * area A * width B ∧
    3 * mixedVolume3 volume (mapBody g B) (mapBody g B) (mapBody f A) =
      (LinearFrame.volumeFactor T : ℝ) * width A * area B := by
  first
  | have hA := pair_volume_smul T f g hf hg A B
      (a := 1) (b := 0) (by norm_num) (by norm_num)
    have hB := pair_volume_smul T f g hf hg A B
      (a := 0) (b := 1) (by norm_num) (by norm_num)
    simp only [one_smul, Set.zero_smul_set (mapBody f A).nonempty,
      Set.zero_smul_set (mapBody g B).nonempty, add_zero, zero_add,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hA hB
    have hdim : finrank ℝ (Space 3) = 3 := by simp [Space]
    have h1 := trivariate_volume_formula volume hdim
      (mapBody f A) (mapBody g B) (mapBody g B)
      (a := 1) (b := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num)
    have h2 := trivariate_volume_formula volume hdim
      (mapBody f A) (mapBody g B) (mapBody g B)
      (a := 2) (b := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num)
    have hp1 := pair_volume_smul T f g hf hg A B
      (a := 1) (b := 1) (by norm_num) (by norm_num)
    have hp2 := pair_volume_smul T f g hf hg A B
      (a := 2) (b := 1) (by norm_num) (by norm_num)
    simp only [one_smul, Set.zero_smul_set (mapBody g B).nonempty, add_zero] at h1 h2 hp1 hp2
    rw [hA, hB] at h1 h2
    constructor <;> nlinarith

section FiberMap

variable {E F U : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def mapTotal (f : E →L[ℝ] F) (C : ConvexBody (E × U)) : ConvexBody (F × U) :=
  mapBody (f.prodMap (ContinuousLinearMap.id ℝ U)) C

theorem projection_mapTotal (f : E →L[ℝ] F) (C : ConvexBody (E × U)) :
    ConvexFibers.projection (mapTotal f C) = ConvexFibers.projection C := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hpy⟩
      exact ⟨p, hp, hpy⟩
    · rintro ⟨p, hp, hpy⟩
      exact ⟨(f p.1, p.2), ⟨p, hp, rfl⟩, hpy⟩

theorem fiberSet_mapTotal (f : E →L[ℝ] F) (C : ConvexBody (E × U)) (y : U) :
    ConvexFibers.fiberSet (mapTotal f C) y = f '' ConvexFibers.fiberSet C y := by
  first
  | ext x
    constructor
    · rintro ⟨⟨u, v⟩, huv, heq⟩
      have hv : v = y := congrArg Prod.snd heq
      subst v
      exact ⟨u, huv, congrArg Prod.fst heq⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u, y), hu, rfl⟩

theorem map_fiberBody (f : E →L[ℝ] F) (C : ConvexBody (E × U))
    {y : U} (hy : y ∈ ConvexFibers.projection C) :
    mapBody f (ConvexFibers.fiberBody C y) = ConvexFibers.fiberBody (mapTotal f C) y := by
  first
  | apply ConvexBody.ext
    have hy' : y ∈ ConvexFibers.projection (mapTotal f C) := by
      rwa [projection_mapTotal]
    rw [coe_mapBody, ConvexFibers.coe_fiberBody C hy,
      ConvexFibers.coe_fiberBody (mapTotal f C) hy', fiberSet_mapTotal]

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ U]
  [MeasureSpace F] [BorelSpace F] [MeasureSpace U] [BorelSpace U]
  [Measure.IsAddHaarMeasure (volume : Measure F)]
  [Measure.IsAddHaarMeasure (volume : Measure U)]

theorem integrable_image_fiberBody (f : E →L[ℝ] F) (C : ConvexBody (E × U)) :
    IntegrableOn (fun y => volume.real (f ''
      (ConvexFibers.fiberBody C y : Set E))) (ConvexFibers.projection C) := by
  first
  | apply (FiberVolume.integrable_fiber_realVolume (mapTotal f C)).integrableOn.congr_fun
      (hs := (ConvexFibers.projection_compact C).measurableSet)
    intro y hy
    dsimp only
    rw [ConvexFibers.coe_fiberBody C hy, fiberSet_mapTotal]

end FiberMap

theorem integral_pair_volume {k : ℕ}
    (T : Space 3 ≃L[ℝ] ProductThree)
    (f g : Plane →L[ℝ] Space 3)
    (hf : ∀ p, T (f p) = CrossPlaneVolume.firstPlane p)
    (hg : ∀ p, T (g p) = CrossPlaneVolume.secondPlane p)
    (F : ConvexBody (Plane × Space k)) (B : ConvexBody Plane)
    {r : ℝ} (hr : 0 ≤ r) :
    (∫ y in ConvexFibers.projection F,
      volume.real (mapBody f (ConvexFibers.fiberBody F y) + r • mapBody g B : Set (Space 3))) =
      (LinearFrame.volumeFactor T : ℝ) *
        ((∫ y in ConvexFibers.projection F, area (ConvexFibers.fiberBody F y)) * width B * r +
         (∫ y in ConvexFibers.projection F, width (ConvexFibers.fiberBody F y)) * area B * r ^ 2) := by
  first
  | have ha : IntegrableOn (fun y => area (ConvexFibers.fiberBody F y))
        (ConvexFibers.projection F) := by
      apply (FiberVolume.integrable_fiber_realVolume F).integrableOn.congr_fun
        (hs := (ConvexFibers.projection_compact F).measurableSet)
      intro y hy
      dsimp only
      rw [area, ConvexFibers.coe_fiberBody F hy]
    have hw : IntegrableOn (fun y => width (ConvexFibers.fiberBody F y))
        (ConvexFibers.projection F) :=
      integrable_image_fiberBody (ContinuousLinearMap.snd ℝ ℝ ℝ) F
    have hp (y : Space k) := pair_volume_smul T f g hf hg
      (ConvexFibers.fiberBody F y) B (a := 1) (b := r) (by norm_num) hr
    simp only [one_smul, one_pow, mul_one] at hp
    simp_rw [hp]
    rw [integral_const_mul, integral_add
      ((ha.mul_const (width B)).mul_const r)
      ((hw.mul_const (area B)).mul_const (r ^ 2))]
    simp only [integral_mul_const]

/-- The third finite difference is independent of the first body. This is an
identity of actual cubic volumes, derived from the verified multilinear expansion. -/
theorem third_difference (A B C : Body 3) :
    volume.real (A + (3 : ℝ) • B + (2 : ℝ) • C : Set (Space 3)) -
      2 * volume.real (A + (2 : ℝ) • B + (2 : ℝ) • C : Set (Space 3)) +
      volume.real (A + B + (2 : ℝ) • C : Set (Space 3)) -
      volume.real (A + (3 : ℝ) • B + C : Set (Space 3)) +
      2 * volume.real (A + (2 : ℝ) • B + C : Set (Space 3)) -
      volume.real (A + B + C : Set (Space 3)) = 6 * mixedVolume3 volume B B C := by
  first
  | have hd : finrank ℝ (Space 3) = 3 := by simp [Space]
    have h32 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 3) (c := 2) (by norm_num) (by norm_num) (by norm_num)
    have h22 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 2) (c := 2) (by norm_num) (by norm_num) (by norm_num)
    have h12 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 1) (c := 2) (by norm_num) (by norm_num) (by norm_num)
    have h31 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 3) (c := 1) (by norm_num) (by norm_num) (by norm_num)
    have h21 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 2) (c := 1) (by norm_num) (by norm_num) (by norm_num)
    have h11 := trivariate_volume_formula volume hd A B C
      (a := 1) (b := 1) (c := 1) (by norm_num) (by norm_num) (by norm_num)
    simp only [one_smul] at h32 h22 h12 h31 h21 h11
    rw [h32, h22, h12, h31, h21, h11]
    ring

def differenceGrid : Fin 6 → ℝ × ℝ := ![(3, 2), (2, 2), (1, 2), (3, 1), (2, 1), (1, 1)]
def differenceWeight : Fin 6 → ℝ := ![1, -2, 1, -1, 2, -1]

def fiberSumVolume {k : ℕ} (F : ConvexBody (Space 3 × Space k))
    (B C : Body 3) (b c : ℝ) (y : Space k) : ℝ :=
  volume.real (ConvexFibers.fiberBody F y + b • B + c • C : Set (Space 3))

theorem integrable_fiberSumVolume {k : ℕ} (F : ConvexBody (Space 3 × Space k))
    (B C : Body 3) (b c : ℝ) :
    IntegrableOn (fiberSumVolume F B C b c) (ConvexFibers.projection F) := by
  first
  | have h : IntegrableOn
        (fun y => volume.real (ConvexFibers.fiberSet
          (F + FiberVolume.embedBody (b • B + c • C)) y))
        (ConvexFibers.projection F) :=
      (FiberVolume.integrable_fiber_realVolume
        (F + FiberVolume.embedBody (b • B + c • C))).integrableOn
    apply h.congr_fun (hs := (ConvexFibers.projection_compact F).measurableSet)
    intro y hy
    have heq := FiberVolume.scaled_sum_fiber_volume F (b • B + c • C)
      (t := 1) (by norm_num) y
    rw [show (1 : ℝ) • F = F from one_smul ℝ F] at heq
    simpa only [one_smul, Set.indicator_of_mem hy, fiberSumVolume,
      ConvexBody.coe_add, ConvexBody.coe_smul, add_assoc] using heq

/-- Finite differences commute with the actual fiber integral. Every summand
is integrable because it is the fiber volume of an actual compact convex sum. -/
theorem integral_third_difference {k : ℕ}
    (F : ConvexBody (Space 3 × Space k)) (B C : Body 3) (J : ℝ) :
    (∑ i : Fin 6, differenceWeight i *
      (J * ∫ y in ConvexFibers.projection F,
        fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y)) =
      J * volume.real (ConvexFibers.projection F) * (6 * mixedVolume3 volume B B C) := by
  first
  | have hpoint (y : Space k) :
        (∑ i : Fin 6, differenceWeight i *
          fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) =
            6 * mixedVolume3 volume B B C := by
      have h := third_difference (ConvexFibers.fiberBody F y) B C
      simp only [Fin.sum_univ_succ, differenceWeight, differenceGrid,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
        add_zero, one_mul, neg_mul, fiberSumVolume, one_smul] at ⊢
      linarith
    have hint : (∫ y in ConvexFibers.projection F,
        ∑ i : Fin 6, differenceWeight i *
          fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) =
          volume.real (ConvexFibers.projection F) * (6 * mixedVolume3 volume B B C) := by
      simp_rw [hpoint]
      rw [setIntegral_const, smul_eq_mul]
    have hsum : (∫ y in ConvexFibers.projection F,
        ∑ i : Fin 6, differenceWeight i *
          fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) =
        ∑ i : Fin 6, differenceWeight i *
          ∫ y in ConvexFibers.projection F,
            fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y := by
      rw [integral_finsetSum _ (fun i _ =>
        (integrable_fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2).const_mul _)]
      simp only [integral_const_mul]
    calc
      _ = J * (∑ i : Fin 6, differenceWeight i *
          ∫ y in ConvexFibers.projection F,
            fiberSumVolume F B C (differenceGrid i).1 (differenceGrid i).2 y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← hsum, hint]; ring

end VolumePolynomials.CommonLineVolume
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 13
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CommonLineVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodySpan.lean -/
section

@[expose] public section

/-!
# Reading subspace constraints directly from volume evaluations

For bodies translated to contain zero, the linear hull of a Minkowski sum is
the sum of their linear hulls. In dimension three, pairwise zero volumes and a
positive triple volume force the three hulls to be lines. This proof does not
assume any sign property of mixed coefficients.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials

section Hull
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearHull (K : ConvexBody E) : Submodule ℝ E := Submodule.span ℝ (K : Set E)

theorem mem_linearHull {K : ConvexBody E} {x : E} (hx : x ∈ K) : x ∈ linearHull K :=
  Submodule.subset_span hx

theorem linearHull_mono {K L : ConvexBody E} (h : K ≤ L) : linearHull K ≤ linearHull L :=
  Submodule.span_mono h

theorem zero_mem_body_add {K L : ConvexBody E} (hK : (0 : E) ∈ K) (hL : (0 : E) ∈ L) :
    (0 : E) ∈ K + L := Set.mem_add.mpr ⟨0, hK, 0, hL, zero_add 0⟩

theorem linearHull_add {K L : ConvexBody E} (hK : (0 : E) ∈ K) (hL : (0 : E) ∈ L) :
    linearHull (K + L) = linearHull K ⊔ linearHull L := by
  first
  | apply le_antisymm
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
      exact Submodule.add_mem _
        ((show linearHull K ≤ linearHull K ⊔ linearHull L from le_sup_left)
          (mem_linearHull hx))
        ((show linearHull L ≤ linearHull K ⊔ linearHull L from le_sup_right)
          (mem_linearHull hy))
    · apply sup_le
      · apply Submodule.span_le.mpr
        intro x hx
        exact mem_linearHull (Set.mem_add.mpr ⟨x, hx, 0, hL, add_zero x⟩)
      · apply Submodule.span_le.mpr
        intro y hy
        exact mem_linearHull (Set.mem_add.mpr ⟨0, hK, y, hy, zero_add y⟩)

theorem affineSpan_eq_linearHull {K : ConvexBody E} (hK : (0 : E) ∈ K) :
    affineSpan ℝ (K : Set E) = (linearHull K).toAffineSubspace :=
  affineSpan_eq_span_of_zero_mem (mem_affineSpan ℝ hK)

end Hull

theorem bodyVolume_pos_iff_linearHull_eq_top {d : ℕ} {K : Body d}
    (hK : (0 : Space d) ∈ K) : 0 < bodyVolume K ↔ linearHull K = ⊤ := by
  first
  | have hreal : 0 < bodyVolume K ↔ 0 < volume (K : Set (Space d)) := by
      constructor
      · intro h
        exact (ENNReal.toReal_pos_iff.mp h).1
      · intro h
        exact ENNReal.toReal_pos h.ne' (bodyVolume_finite K)
    have hpos : 0 < volume (K : Set (Space d)) ↔
        (interior (K : Set (Space d))).Nonempty := by
      rw [pos_iff_ne_zero, ← measure_interior_of_null_frontier
        (K.convex.addHaar_frontier volume)]
      simpa only [Set.nonempty_iff_ne_empty] using
        not_congr (isOpen_interior.measure_eq_zero_iff volume)
    rw [hreal, hpos, K.convex.interior_nonempty_iff_affineSpan_eq_top,
      affineSpan_eq_linearHull hK]
    constructor
    · intro h
      simpa only [Submodule.toAffineSubspace_direction, AffineSubspace.direction_top] using
        congrArg AffineSubspace.direction h
    · intro h
      rw [h]
      rfl

theorem bodyVolume_eq_zero_iff_linearHull_ne_top {d : ℕ} {K : Body d}
    (hK : (0 : Space d) ∈ K) : bodyVolume K = 0 ↔ linearHull K ≠ ⊤ := by
  first
  | constructor
    · intro h hz
      have hp := (bodyVolume_pos_iff_linearHull_eq_top hK).mpr hz
      rw [h] at hp
      exact lt_irrefl 0 hp
    · intro h
      apply le_antisymm _ (bodyVolume_nonneg K)
      apply le_of_not_gt
      intro hp
      exact h ((bodyVolume_pos_iff_linearHull_eq_top hK).mp hp)

section ThreeDimensions
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem finrank_le_one_of_pair_sums_proper (U V W : Submodule ℝ E)
    (hdim : finrank ℝ E = 3) (hUV : U ⊔ V ≠ ⊤) (hUW : U ⊔ W ≠ ⊤)
    (hfull : U ⊔ V ⊔ W = ⊤) : finrank ℝ U ≤ 1 := by
  first
  | by_contra h
    have hU : 2 ≤ finrank ℝ U := by omega
    have hUVdim : finrank ℝ (U ⊔ V : Submodule ℝ E) ≤ 2 := by
      have hh := Submodule.finrank_lt hUV
      rw [hdim] at hh
      omega
    have hUWdim : finrank ℝ (U ⊔ W : Submodule ℝ E) ≤ 2 := by
      have hh := Submodule.finrank_lt hUW
      rw [hdim] at hh
      omega
    have hUVeq : U = U ⊔ V :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (hUVdim.trans hU)
    have hUWeq : U = U ⊔ W :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (hUWdim.trans hU)
    have hVU : V ≤ U := le_sup_right.trans_eq hUVeq.symm
    have hWU : W ≤ U := le_sup_right.trans_eq hUWeq.symm
    have hfullU : U ⊔ V ⊔ W ≤ U := sup_le (sup_le le_rfl hVU) hWU
    rw [hfull] at hfullU
    exact hUV (by rw [top_unique hfullU, top_sup_eq])

theorem finrank_eq_one_of_pair_sums_proper (U V W : Submodule ℝ E)
    (hdim : finrank ℝ E = 3) (hUV : U ⊔ V ≠ ⊤) (hUW : U ⊔ W ≠ ⊤)
    (hVW : V ⊔ W ≠ ⊤) (hfull : U ⊔ V ⊔ W = ⊤) : finrank ℝ U = 1 := by
  first
  | apply le_antisymm (finrank_le_one_of_pair_sums_proper U V W hdim hUV hUW hfull)
    apply Submodule.one_le_finrank_iff.mpr
    intro hU
    apply hVW
    simpa only [hU, bot_sup_eq] using hfull

theorem finrank_le_one_of_three_pair_sums_proper (U A B C : Submodule ℝ E)
    (hdim : finrank ℝ E = 3) (hUA : U ⊔ A ≠ ⊤) (hUB : U ⊔ B ≠ ⊤)
    (hUC : U ⊔ C ≠ ⊤) (hABC : A ⊔ B ⊔ C = ⊤) : finrank ℝ U ≤ 1 := by
  first
  | by_contra h
    have hU : 2 ≤ finrank ℝ U := by omega
    have hsubset : ∀ V : Submodule ℝ E, U ⊔ V ≠ ⊤ → V ≤ U := by
      intro V hV
      have hdimUV : finrank ℝ (U ⊔ V : Submodule ℝ E) ≤ 2 := by
        have hh := Submodule.finrank_lt hV
        rw [hdim] at hh
        omega
      have heq : U = U ⊔ V :=
        Submodule.eq_of_le_of_finrank_le le_sup_left (hdimUV.trans hU)
      exact le_sup_right.trans_eq heq.symm
    have hle : A ⊔ B ⊔ C ≤ U :=
      sup_le (sup_le (hsubset A hUA) (hsubset B hUB)) (hsubset C hUC)
    rw [hABC] at hle
    exact hUA (by rw [top_unique hle, top_sup_eq])

end ThreeDimensions

/-- Three compact convex bodies in three-space have one-dimensional hulls when
every pair has zero volume and the triple has positive volume. -/
theorem frame_linearHulls_are_lines (A B C : Body 3)
    (hA : (0 : Space 3) ∈ A) (hB : (0 : Space 3) ∈ B) (hC : (0 : Space 3) ∈ C)
    (hAB : bodyVolume (A + B) = 0) (hAC : bodyVolume (A + C) = 0)
    (hBC : bodyVolume (B + C) = 0) (hABC : 0 < bodyVolume (A + B + C)) :
    finrank ℝ (linearHull A) = 1 ∧ finrank ℝ (linearHull B) = 1 ∧
      finrank ℝ (linearHull C) = 1 := by
  first
  | have hUV := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hA hB)).mp hAB
    have hUW := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hA hC)).mp hAC
    have hVW := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hB hC)).mp hBC
    have hfull := (bodyVolume_pos_iff_linearHull_eq_top
      (zero_mem_body_add (zero_mem_body_add hA hB) hC)).mp hABC
    rw [linearHull_add hA hB] at hUV
    rw [linearHull_add hA hC] at hUW
    rw [linearHull_add hB hC] at hVW
    rw [linearHull_add (zero_mem_body_add hA hB) hC, linearHull_add hA hB] at hfull
    have hdim : finrank ℝ (Space 3) = 3 := by simp [Space]
    refine ⟨finrank_eq_one_of_pair_sums_proper _ _ _ hdim hUV hUW hVW hfull, ?_, ?_⟩
    · apply finrank_eq_one_of_pair_sums_proper (linearHull B) (linearHull A) (linearHull C)
        hdim (by simpa [sup_comm] using hUV) hVW hUW
      simpa [sup_comm, sup_left_comm, sup_assoc] using hfull
    · apply finrank_eq_one_of_pair_sums_proper (linearHull C) (linearHull A) (linearHull B)
        hdim (by simpa [sup_comm] using hUW) (by simpa [sup_comm] using hVW) hUV
      simpa [sup_comm, sup_left_comm, sup_assoc] using hfull

/-- A nonempty compact convex body with one-dimensional linear hull is an
actual closed segment. The endpoints are attained extrema of a linear
coordinate, including the possibility of a degenerate segment. -/
theorem exists_segment_of_finrank_linearHull_eq_one {d : ℕ} (K : Body d)
    (hK : finrank ℝ (linearHull K) = 1) :
    ∃ a b : Space d, a ∈ K ∧ b ∈ K ∧ (K : Set (Space d)) = segment ℝ a b := by
  first
  | have hnonzero : linearHull K ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hK
      exact Nat.zero_ne_one hK
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnonzero
    have hspan : linearHull K = ℝ ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hK hv hv0
    obtain ⟨i, hi⟩ : ∃ i : Fin d, v i ≠ 0 := by
      by_contra h
      apply hv0
      funext i
      exact not_not.mp (fun hi => h ⟨i, hi⟩)
    let f : Space d →L[ℝ] ℝ := (v i)⁻¹ • ContinuousLinearMap.proj i
    have hreconstruct : ∀ x ∈ linearHull K, f x • v = x := by
      intro x hx
      rw [hspan] at hx
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
      change ((v i)⁻¹ * (r * v i)) • v = r • v
      congr 1
      field_simp
    obtain ⟨a, ha, hmin⟩ := K.isCompact.exists_isMinOn K.nonempty f.continuous.continuousOn
    obtain ⟨b, hb, hmax⟩ := K.isCompact.exists_isMaxOn K.nonempty f.continuous.continuousOn
    refine ⟨a, b, ha, hb, subset_antisymm ?_ (K.convex.segment_subset ha hb)⟩
    intro x hx
    have hfx : f x ∈ segment ℝ (f a) (f b) := by
      rw [segment_eq_Icc (hmin hb)]
      exact ⟨hmin hx, hmax hx⟩
    change f.toLinearMap.toAffineMap x ∈
      segment ℝ (f.toLinearMap.toAffineMap a) (f.toLinearMap.toAffineMap b) at hfx
    rw [← image_segment ℝ f.toLinearMap.toAffineMap a b] at hfx
    obtain ⟨y, hy, hfy⟩ := hfx
    change f y = f x at hfy
    have hyK := K.convex.segment_subset ha hb hy
    have hyx : y = x := by
      calc
        y = f y • v := (hreconstruct y (mem_linearHull hyK)).symm
        _ = f x • v := by rw [hfy]
        _ = x := hreconstruct x (mem_linearHull hx)
    simpa only [hyx] using hy

theorem exists_segment_of_finrank_linearHull_le_one {d : ℕ} (K : Body d)
    (hzero : (0 : Space d) ∈ K) (hK : finrank ℝ (linearHull K) ≤ 1) :
    ∃ a b : Space d, a ∈ K ∧ b ∈ K ∧ (K : Set (Space d)) = segment ℝ a b := by
  first
  | rcases Nat.eq_zero_or_pos (finrank ℝ (linearHull K)) with hdim | hdim
    · have hbot : linearHull K = ⊥ := Submodule.finrank_eq_zero.mp hdim
      refine ⟨0, 0, hzero, hzero, ?_⟩
      rw [segment_same]
      apply subset_antisymm
      · intro x hx
        have hmem := mem_linearHull hx
        rw [hbot] at hmem
        simpa only [Submodule.mem_bot, Set.mem_singleton_iff] using hmem
      · exact singleton_subset_iff.mpr hzero
    · exact exists_segment_of_finrank_linearHull_eq_one K (by omega)

/-- Testing zero volume against the three spanning frame lines forces each
additional compact convex body to be a segment (possibly a point). -/
theorem body_is_segment_of_three_zero_volumes (H A B C : Body 3)
    (hH : (0 : Space 3) ∈ H) (hA : (0 : Space 3) ∈ A)
    (hB : (0 : Space 3) ∈ B) (hC : (0 : Space 3) ∈ C)
    (hHA : bodyVolume (H + A) = 0) (hHB : bodyVolume (H + B) = 0)
    (hHC : bodyVolume (H + C) = 0) (hABC : 0 < bodyVolume (A + B + C)) :
    ∃ a b : Space 3, a ∈ H ∧ b ∈ H ∧ (H : Set (Space 3)) = segment ℝ a b := by
  first
  | apply exists_segment_of_finrank_linearHull_le_one H hH
    have hUA := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hH hA)).mp hHA
    have hUB := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hH hB)).mp hHB
    have hUC := (bodyVolume_eq_zero_iff_linearHull_ne_top (zero_mem_body_add hH hC)).mp hHC
    have hfull := (bodyVolume_pos_iff_linearHull_eq_top
      (zero_mem_body_add (zero_mem_body_add hA hB) hC)).mp hABC
    rw [linearHull_add hH hA] at hUA
    rw [linearHull_add hH hB] at hUB
    rw [linearHull_add hH hC] at hUC
    rw [linearHull_add (zero_mem_body_add hA hB) hC, linearHull_add hA hB] at hfull
    exact finrank_le_one_of_three_pair_sums_proper _ _ _ _ (by simp [Space])
      hUA hUB hUC hfull

/-- A zero volume test against a two-dimensional body forces containment in
that body's plane once both bodies have been translated to contain zero. -/
theorem linearHull_le_of_volume_zero_sum (K L : Body 3)
    (hK : (0 : Space 3) ∈ K) (hL : (0 : Space 3) ∈ L)
    (hdimL : finrank ℝ (linearHull L) = 2)
    (hvol : bodyVolume (K + L) = 0) : linearHull K ≤ linearHull L := by
  first
  | have hproper := (bodyVolume_eq_zero_iff_linearHull_ne_top
      (zero_mem_body_add hK hL)).mp hvol
    rw [linearHull_add hK hL] at hproper
    have hdim : finrank ℝ (linearHull K ⊔ linearHull L : Submodule ℝ (Space 3)) ≤ 2 := by
      have h := Submodule.finrank_lt hproper
      have hspace : finrank ℝ (Space 3) = 3 := by simp [Space]
      rw [hspace] at h
      omega
    have heq : linearHull L = linearHull K ⊔ linearHull L :=
      Submodule.eq_of_le_of_finrank_le le_sup_right (hdim.trans_eq hdimL.symm)
    exact le_sup_left.trans_eq heq.symm

theorem body_subset_linearHull_of_volume_zero_sum (K L : Body 3)
    (hK : (0 : Space 3) ∈ K) (hL : (0 : Space 3) ∈ L)
    (hdimL : finrank ℝ (linearHull L) = 2)
    (hvol : bodyVolume (K + L) = 0) : (K : Set (Space 3)) ⊆ linearHull L := by
  first
  | intro x hx
    exact linearHull_le_of_volume_zero_sum K L hK hL hdimL hvol (mem_linearHull hx)

/-- All three members of a volume-calibrated frame are genuine segments. -/
theorem frame_bodies_are_segments (A B C : Body 3)
    (hA : (0 : Space 3) ∈ A) (hB : (0 : Space 3) ∈ B) (hC : (0 : Space 3) ∈ C)
    (hAB : bodyVolume (A + B) = 0) (hAC : bodyVolume (A + C) = 0)
    (hBC : bodyVolume (B + C) = 0) (hABC : 0 < bodyVolume (A + B + C)) :
    (∃ a b : Space 3, a ∈ A ∧ b ∈ A ∧ (A : Set (Space 3)) = segment ℝ a b) ∧
    (∃ a b : Space 3, a ∈ B ∧ b ∈ B ∧ (B : Set (Space 3)) = segment ℝ a b) ∧
    (∃ a b : Space 3, a ∈ C ∧ b ∈ C ∧ (C : Set (Space 3)) = segment ℝ a b) := by
  first
  | obtain ⟨ha, hb, hc⟩ := frame_linearHulls_are_lines A B C hA hB hC hAB hAC hBC hABC
    exact ⟨exists_segment_of_finrank_linearHull_eq_one A ha,
      exists_segment_of_finrank_linearHull_eq_one B hb,
      exists_segment_of_finrank_linearHull_eq_one C hc⟩

end VolumePolynomials
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodySpan.lean -/

/- BEGIN SOURCE: VolumePolynomials/OneBody.lean -/
section

@[expose] public section

/-!
# The complete one-body realization locus

This is the one-body branch of Theorem 1.1, for every positive dimension. It is
proved directly with Lebesgue volume and a dilated unit cube. No mixed-volume
existence theorem is assumed.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped Pointwise BigOperators

namespace VolumePolynomials

def oneIndex (d : ℕ) : MultiIndex 1 d :=
  ⟨fun _ => ⟨d, Nat.lt_succ_self d⟩, by simp⟩

theorem oneIndex_unique {d : ℕ} (α : MultiIndex 1 d) : α = oneIndex d := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa [oneIndex] using α.2

instance unique_oneIndex (d : ℕ) : Unique (MultiIndex 1 d) where
  default := oneIndex d
  uniq := oneIndex_unique

@[simp] theorem evaluate_oneVariable {d : ℕ} (c : Coefficients 1 d) (t : Fin 1 → ℝ) :
    evaluate c t = c (oneIndex d) * t 0 ^ d := by
  have hdefault : (default : MultiIndex 1 d) = oneIndex d := oneIndex_unique _
  simp only [evaluate, Fintype.sum_unique, hdefault, oneIndex, Fin.prod_univ_one]

@[simp] theorem sum_coefficients_oneVariable {d : ℕ} (c : Coefficients 1 d) :
    ∑ α, c α = c (oneIndex d) := by
  exact Fintype.sum_unique c

def unitCube (d : ℕ) : Body d where
  carrier := Set.Icc 0 1
  convex' := convex_Icc _ _
  isCompact' := isCompact_Icc
  nonempty' := ⟨0, le_rfl, by intro i; exact zero_le_one⟩

@[simp] theorem bodyVolume_unitCube (d : ℕ) : bodyVolume (unitCube d) = 1 := by
  have h : (0 : Space d) ≤ 1 := fun _ => zero_le_one
  change (volume (Set.Icc (0 : Space d) 1)).toReal = 1
  simpa using Real.volume_Icc_pi_toReal h

theorem exists_body_of_volume {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 ≤ a) :
    ∃ K : Body d, bodyVolume K = a := by
  refine ⟨(a ^ (d : ℝ)⁻¹) • unitCube d, ?_⟩
  rw [bodyVolume_smul _ (Real.rpow_nonneg ha _), bodyVolume_unitCube, mul_one]
  exact Real.rpow_inv_natCast_pow ha hd.ne'

/-- Every nonnegative coefficient, including zero, is realized by one compact
convex body in every positive dimension. -/
theorem oneBody_realizable_iff {d : ℕ} (hd : 0 < d) (c : Coefficients 1 d) :
    c ∈ VolumeLocus 1 d ↔ 0 ≤ c (oneIndex d) := by
  constructor
  · rintro ⟨K, hK⟩
    simpa only [sum_coefficients_oneVariable] using hK.sum_coefficients_nonneg
  · intro hc
    obtain ⟨K, hK⟩ := exists_body_of_volume hd hc
    refine ⟨fun _ => K, fun t ht => ?_⟩
    simp only [volumeFunction, weightedSum, Fin.sum_univ_one, evaluate_oneVariable]
    rw [bodyVolume_smul _ (ht 0), hK, mul_comm]

theorem oneBody_realizable_iff_coefficients_nonneg {d : ℕ} (hd : 0 < d)
    (c : Coefficients 1 d) : c ∈ VolumeLocus 1 d ↔ ∀ α, 0 ≤ c α := by
  rw [oneBody_realizable_iff hd]
  exact ⟨fun h α => oneIndex_unique α ▸ h, fun h => h _⟩

end VolumePolynomials
end -- closes the original EOF section from source line 15
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/OneBody.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyFrames.lean -/
section

@[expose] public section

/-!
# Normalizing segment frames by their actual volume

A finite family of segments is the linear image of a unit cube after
independent translations. A volume-one hypothesis therefore forces the
column map to have determinant modulus one and supplies an invertible
normalizing map. No mixed-volume or determinant formula is assumed.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials

section Segments
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def segmentBody (a b : E) : ConvexBody E where
  carrier := segment ℝ a b
  convex' := convex_segment a b
  isCompact' := by
    first
    | rw [segment_eq_image]
      exact isCompact_Icc.image (by fun_prop)
  nonempty' := ⟨a, left_mem_segment ℝ a b⟩

@[simp] theorem coe_segmentBody (a b : E) :
    (segmentBody a b : Set E) = segment ℝ a b := rfl

@[simp] theorem translate_segmentBody (v a b : E) :
    translateBody v (segmentBody a b) = segmentBody (v + a) (v + b) := by
  first
  | apply ConvexBody.ext
    simp only [coe_translateBody, coe_segmentBody, vadd_segment, vadd_eq_add]

@[simp] theorem map_segmentBody (f : E →L[ℝ] F) (a b : E) :
    mapBody f (segmentBody a b) = segmentBody (f a) (f b) := by
  first
  | apply ConvexBody.ext
    exact image_segment ℝ f.toLinearMap.toAffineMap a b

theorem body_eq_segmentBody {K : ConvexBody E} {a b : E}
    (h : (K : Set E) = segment ℝ a b) : K = segmentBody a b :=
  ConvexBody.ext h

end Segments

def coordinateSegment {d : ℕ} (i : Fin d) : Body d :=
  segmentBody 0 (Pi.single i 1)

@[simp] theorem zero_mem_coordinateSegment {d : ℕ} (i : Fin d) :
    (0 : Space d) ∈ coordinateSegment i := left_mem_segment ℝ _ _

theorem linearHull_segmentBody_zero {d : ℕ} (v : Space d) :
    linearHull (segmentBody 0 v) = ℝ ∙ v := by
  first
  | apply le_antisymm
    · apply Submodule.span_le.mpr
      exact (Submodule.convex (ℝ ∙ v)).segment_subset
        (Submodule.zero_mem _) (Submodule.mem_span_singleton_self v)
    · apply Submodule.span_le.mpr
      intro x hx
      have h : x = v := Set.mem_singleton_iff.mp hx
      rw [h]
      exact mem_linearHull (right_mem_segment ℝ (0 : Space d) v)

theorem linearHull_coordinateSegment_pair {d : ℕ} (i j : Fin d) :
    linearHull (coordinateSegment i + coordinateSegment j) =
      Submodule.span ℝ {Pi.single i (1 : ℝ), Pi.single j 1} := by
  first
  | rw [linearHull_add (zero_mem_coordinateSegment i) (zero_mem_coordinateSegment j)]
    simp only [coordinateSegment, linearHull_segmentBody_zero, ← Submodule.span_union,
      Set.singleton_union]

theorem finrank_coordinateSegment_pair {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    finrank ℝ (linearHull (coordinateSegment i + coordinateSegment j)) = 2 := by
  first
  | have hli : LinearIndependent ℝ ![(Pi.single i (1 : ℝ) : Space d), Pi.single j 1] := by
      rw [LinearIndependent.pair_iff]
      intro s t h
      constructor
      · have hi := congrFun h i
        simpa [Pi.single_apply, hij, hij.symm] using hi
      · have hj := congrFun h j
        simpa [Pi.single_apply, hij, hij.symm] using hj
    rw [linearHull_coordinateSegment_pair]
    have hrange : Set.range ![(Pi.single i (1 : ℝ) : Space d), Pi.single j 1] =
        {(Pi.single i (1 : ℝ) : Space d), Pi.single j 1} := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hdim := finrank_span_eq_card hli
    rw [hrange] at hdim
    simpa only [Fintype.card_fin] using hdim

/-- The volume test against two coordinate segments has its literal geometric
meaning: the body has zero remaining coordinate after translation to the
origin. This is the plane constraint used in the nine-body pattern. -/
theorem coordinate_eq_zero_of_volume_zero (K : Body 3) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzero : (0 : Space 3) ∈ K)
    (hvol : bodyVolume (K + coordinateSegment i + coordinateSegment j) = 0) :
    ∀ x ∈ K, x k = 0 := by
  first
  | have hvol' : bodyVolume (K + (coordinateSegment i + coordinateSegment j)) = 0 := by
      simpa only [add_assoc] using hvol
    have hsub := body_subset_linearHull_of_volume_zero_sum K
      (coordinateSegment i + coordinateSegment j) hzero
      (zero_mem_body_add (zero_mem_coordinateSegment i) (zero_mem_coordinateSegment j))
      (finrank_coordinateSegment_pair i j hij) hvol'
    intro x hx
    have hmem := hsub hx
    rw [linearHull_coordinateSegment_pair] at hmem
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hmem
    simp [Pi.single_apply, hik, hjk, hik.symm, hjk.symm]

def frameColumnMap {d : ℕ} (v : Fin d → Space d) : Space d →L[ℝ] Space d :=
  (Pi.basisFun ℝ (Fin d)).constrL v

@[simp] theorem frameColumnMap_apply {d : ℕ} (v : Fin d → Space d) (x : Space d) :
    frameColumnMap v x = ∑ i, x i • v i := by
  first
  | simp [frameColumnMap, Basis.constrL_apply]

@[simp] theorem frameColumnMap_basis {d : ℕ} (v : Fin d → Space d) (i : Fin d) :
    frameColumnMap v (Pi.single i 1) = v i := by
  first
  | simpa only [frameColumnMap, Pi.basisFun_apply] using
      (Pi.basisFun ℝ (Fin d)).constrL_basis v i

theorem map_unitCube_eq_sum_segments {d : ℕ} (v : Fin d → Space d) :
    mapBody (frameColumnMap v) (unitCube d) = ∑ i, segmentBody 0 (v i) := by
  first
  | apply ConvexBody.ext
    rw [coe_mapBody, coe_sum_body]
    change (frameColumnMap v) '' Set.Icc 0 1 = ∑ i, segment ℝ 0 (v i)
    rw [← parallelepiped_eq_sum_segment]
    simp only [parallelepiped, frameColumnMap_apply]

theorem bodyVolume_sum_origin_segments {d : ℕ} (v : Fin d → Space d) :
    bodyVolume (∑ i, segmentBody 0 (v i)) =
      |LinearMap.det (frameColumnMap v).toLinearMap| := by
  first
  | rw [← map_unitCube_eq_sum_segments, bodyVolume_map, bodyVolume_unitCube, mul_one]

theorem sum_origin_segments_eq_translate {d : ℕ} (a b : Fin d → Space d) :
    (∑ i, segmentBody 0 (b i - a i)) =
      translateBody (-(∑ i, a i)) (∑ i, segmentBody (a i) (b i)) := by
  first
  | have h := weightedSum_translate (fun i => segmentBody (a i) (b i))
      (fun i => -a i) (fun _ => (1 : ℝ))
    simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib,
      translate_segmentBody, neg_add_cancel, neg_add_eq_sub] using h

theorem normalize_origin_segment_frame {d : ℕ} (v : Fin d → Space d)
    (hvol : bodyVolume (∑ i, segmentBody 0 (v i)) = 1) :
    ∃ g : Space d ≃L[ℝ] Space d,
      |LinearMap.det g.toLinearEquiv.toLinearMap| = 1 ∧
      ∀ i, g (v i) = Pi.single i 1 := by
  first
  | let f : Space d →L[ℝ] Space d := frameColumnMap v
    have hdet : |LinearMap.det f.toLinearMap| = 1 := by
      rw [← bodyVolume_sum_origin_segments, hvol]
    have hne : LinearMap.det f.toLinearMap ≠ 0 := by
      intro h
      rw [h, abs_zero] at hdet
      exact zero_ne_one hdet
    let e : Space d ≃L[ℝ] Space d := f.toContinuousLinearEquivOfDetNeZero hne
    refine ⟨e.symm, ?_, fun i => ?_⟩
    · change |LinearMap.det e.toLinearEquiv.symm.toLinearMap| = 1
      rw [LinearEquiv.det_coe_symm, abs_inv]
      change |LinearMap.det f.toLinearMap|⁻¹ = 1
      rw [hdet, inv_one]
    · apply e.injective
      rw [e.apply_symm_apply]
      exact (frameColumnMap_basis v i).symm

/-- A volume-one segment frame in any dimension is carried to the standard
coordinate segments by independent translations and a common continuous
linear equivalence whose determinant has modulus one. -/
theorem normalize_segment_frame {d : ℕ} (a b : Fin d → Space d)
    (hvol : bodyVolume (∑ i, segmentBody (a i) (b i)) = 1) :
    ∃ g : Space d ≃L[ℝ] Space d,
      |LinearMap.det g.toLinearEquiv.toLinearMap| = 1 ∧
      ∀ i, mapBody g.toContinuousLinearMap
        (translateBody (-a i) (segmentBody (a i) (b i))) =
          segmentBody 0 (Pi.single i 1) := by
  first
  | have hv : bodyVolume (∑ i, segmentBody 0 (b i - a i)) = 1 := by
      rw [sum_origin_segments_eq_translate, bodyVolume_translate, hvol]
    obtain ⟨g, hg, hgv⟩ := normalize_origin_segment_frame (fun i => b i - a i) hv
    refine ⟨g, hg, fun i => ?_⟩
    rw [translate_segmentBody, neg_add_cancel, neg_add_eq_sub, map_segmentBody,
      map_zero]
    change segmentBody (0 : Space d) (g (b i - a i)) = segmentBody 0 (Pi.single i 1)
    rw [hgv]

end VolumePolynomials
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodyFrames.lean -/

/- BEGIN SOURCE: VolumePolynomials/SegmentVolume.lean -/
section

@[expose] public section
noncomputable section

/-!
# Affine dependence of volume on a segment summand

The interval-fiber extrusion theorem gives affine dependence on every
nonnegative segment length in every ambient dimension. The coordinate frame
is constructed from a nonzero coordinate of the segment vector. Uniqueness of
Haar measure supplies its proved volume factor, which cancels from the final
identity. Translated and degenerate segments are included.
-/

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials

theorem smul_segment_zero_eq_parameter_image {d : ℕ} (v : Space d) {r : ℝ}
    (hr : 0 ≤ r) :
    r • segment ℝ 0 v = (fun s : ℝ => s • v) '' Icc 0 r := by
  rw [segment_eq_image]
  simp only [smul_zero, zero_add]
  rw [← Set.image_smul, Set.image_image]
  have hf : (fun s : ℝ => r • (s • v)) =
      (fun s : ℝ => s • v) ∘ (fun s : ℝ => s * r) := by
    funext s
    simp only [Function.comp_apply, smul_smul, mul_comm]
  rw [hf, Set.image_comp, image_mul_right_Icc zero_le_one hr]
  simp only [zero_mul, one_mul]

theorem realVolume_add_segment_parameter_affine {d : ℕ}
    {C : Set (Space d)} (hC : IsCompact C) (hc : Convex ℝ C) (v : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 r) =
      volume.real C + r *
        (volume.real (C + (fun s : ℝ => s • v) '' Icc 0 1) - volume.real C) := by
  by_cases hv0 : v = 0
  · subst v
    have hne : (Icc (0 : ℝ) r).Nonempty := ⟨0, le_rfl, hr⟩
    have hne1 : (Icc (0 : ℝ) 1).Nonempty := ⟨0, le_rfl, zero_le_one⟩
    simp only [smul_zero, hne.image_const (0 : Space d), hne1.image_const (0 : Space d),
      Set.add_singleton, add_zero, Set.image_id', sub_self, mul_zero, add_zero]
  · obtain ⟨i, hi⟩ : ∃ i : Fin d, v i ≠ 0 := by
      by_contra h
      apply hv0
      funext i
      exact not_not.mp (fun hi => h ⟨i, hi⟩)
    let l : Space d →L[ℝ] ℝ := (v i)⁻¹ • ContinuousLinearMap.proj i
    have hlv : l v = 1 := by simp [l, hi]
    let E := LinearMap.ker l.toLinearMap
    letI : MeasureSpace E := ⟨Measure.addHaar⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := by
      change Measure.IsAddHaarMeasure (Measure.addHaar : Measure E)
      infer_instance
    let T : Space d ≃L[ℝ] ℝ × E := LinearFrame.continuousEquiv l v hlv
    have hTv : T v = (1, 0) := by
      apply Prod.ext
      · exact hlv
      · apply Subtype.ext
        change v - l v • v = 0
        simp only [hlv, one_smul, sub_self]
    let J : ℝ := LinearFrame.volumeFactor T
    let A : ℝ := volume.real (T '' C)
    let B : ℝ := volume.real (PlanarExtrusion.projection (T '' C))
    have hformula (t : ℝ) (ht : 0 ≤ t) :
        volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) = J * (A + t * B) := by
      rw [LinearFrame.realVolume_eq_factor_mul_image T,
        Set.image_add T, ProductExtrusion.image_origin_segment T hTv]
      rw [PlanarExtrusion.realVolume_add_horizontal (hC.image T.continuous)
        (hc.linear_image T.toLinearMap) ht]
    have hbase : volume.real C = J * A :=
      LinearFrame.realVolume_eq_factor_mul_image T C
    rw [hformula r hr, hformula 1 zero_le_one, hbase]
    ring

theorem bodyVolume_add_smul_originSegment {d : ℕ} (L : Body d) (v : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (L + r • segmentBody 0 v) = bodyVolume L + r *
      (bodyVolume (L + segmentBody 0 v) - bodyVolume L) := by
  change volume.real ((L : Set (Space d)) + r • segment ℝ 0 v) = _
  rw [smul_segment_zero_eq_parameter_image v hr]
  have h := realVolume_add_segment_parameter_affine L.isCompact L.convex v hr
  have hone : segment ℝ (0 : Space d) v = (fun s : ℝ => s • v) '' Icc 0 1 := by
    simp only [segment_eq_image, smul_zero, zero_add]
  simpa only [bodyVolume, ConvexBody.coe_add, coe_segmentBody, hone] using h

/-- No centering, nondegeneracy or full-dimensionality hypothesis is needed. -/
theorem bodyVolume_add_smul_segment {d : ℕ} (L : Body d) (a b : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (L + r • segmentBody a b) = bodyVolume L + r *
      (bodyVolume (L + segmentBody a b) - bodyVolume L) := by
  have hseg : segmentBody a b = translateBody a (segmentBody 0 (b - a)) := by
    rw [translate_segmentBody]
    congr 1 <;> abel
  have htranslate (t : ℝ) :
      L + t • translateBody a (segmentBody 0 (b - a)) =
        translateBody (t • a) (L + t • segmentBody 0 (b - a)) := by
    simp only [translateBody, smul_add, ← pointBody_smul]
    ac_rfl
  rw [hseg, htranslate, bodyVolume_translate]
  have hone : L + translateBody a (segmentBody 0 (b - a)) =
      translateBody a (L + segmentBody 0 (b - a)) := by
    simpa only [one_smul] using htranslate 1
  rw [hone, bodyVolume_translate]
  exact bodyVolume_add_smul_originSegment L (b - a) hr

theorem bodyVolume_segment_second_difference {d : ℕ} (K L : Body d)
    (hK : ∃ a b : Space d, (K : Set (Space d)) = segment ℝ a b) :
    bodyVolume (L + (2 : ℝ) • K) - 2 * bodyVolume (L + K) + bodyVolume L = 0 := by
  obtain ⟨a, b, hK⟩ := hK
  have hbody := body_eq_segmentBody hK
  rw [hbody, bodyVolume_add_smul_segment L a b (by norm_num)]
  ring

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SegmentVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/CubicSlice.lean -/
section

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The literal ternary-cubic coefficient slice

The polynomial is exactly (3.1), with ordinary monomial coefficients. Its
zero pure terms and positive repeated terms force every realizing body to
have affine dimension two. The argument uses actual volume evaluations and
the general segment extrusion theorem; it does not assume degree/dimension
correspondence or a mixed-volume positivity axiom.
-/

open Set Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials.CubicSlice

def polynomial (α s z : ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (3 * α) * X 0 ^ 2 * X 1 + C (3 * α) * X 0 ^ 2 * X 2 +
  C 3 * X 0 * X 1 ^ 2 + C 3 * X 1 ^ 2 * X 2 +
  C (3 * s) * X 0 * X 2 ^ 2 + C 3 * X 1 * X 2 ^ 2 +
  C (6 * z) * X 0 * X 1 * X 2

theorem polynomial_homogeneous (α s z : ℝ) : (polynomial α s z).IsHomogeneous 3 := by
  first
  | have h21 (a : ℝ) (i j : Fin 3) :
        (C a * X i ^ 2 * X j : MvPolynomial (Fin 3) ℝ).IsHomogeneous 3 := by
      simpa only [zero_add, one_mul] using
        ((isHomogeneous_C (σ := Fin 3) a).mul
          ((isHomogeneous_X ℝ i).pow 2)).mul (isHomogeneous_X ℝ j)
    have h12 (a : ℝ) (i j : Fin 3) :
        (C a * X i * X j ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 3 := by
      simpa only [zero_add, one_mul] using
        ((isHomogeneous_C (σ := Fin 3) a).mul
          (isHomogeneous_X ℝ i)).mul ((isHomogeneous_X ℝ j).pow 2)
    have h111 : (C (6 * z) * X 0 * X 1 * X 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 3 := by
      simpa only [zero_add] using
        (((isHomogeneous_C (σ := Fin 3) (6 * z)).mul
          (isHomogeneous_X ℝ (0 : Fin 3))).mul (isHomogeneous_X ℝ (1 : Fin 3))).mul
          (isHomogeneous_X ℝ (2 : Fin 3))
    exact (((((h21 (3 * α) 0 1).add (h21 (3 * α) 0 2)).add (h12 3 0 1)).add
      (h21 3 1 2)).add (h12 (3 * s) 0 2)).add (h12 3 1 2) |>.add h111

def coefficients (α s z : ℝ) : Coefficients 3 3 :=
  coefficientsOfPolynomial (polynomial α s z)

def value (α s z : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  3 * α * t 0 ^ 2 * t 1 + 3 * α * t 0 ^ 2 * t 2 +
  3 * t 0 * t 1 ^ 2 + 3 * t 1 ^ 2 * t 2 +
  3 * s * t 0 * t 2 ^ 2 + 3 * t 1 * t 2 ^ 2 +
  6 * z * t 0 * t 1 * t 2

theorem evaluate_coefficients (α s z : ℝ) (t : Fin 3 → ℝ) :
    evaluate (coefficients α s z) t = value α s z t := by
  first
  | rw [coefficients, evaluate_eq_polynomial_eval,
      coefficientPolynomial_coefficientsOfPolynomial _ (polynomial_homogeneous α s z)]
    simp only [polynomial, value, map_add, map_mul, map_pow, eval_C, eval_X]

theorem realizes_iff (α s z : ℝ) (K : Fin 3 → Body 3) :
    Realizes K (coefficients α s z) ↔
      ∀ t : Fin 3 → ℝ, (∀ i, 0 ≤ t i) → volumeFunction K t = value α s z t := by
  first
  | simp only [Realizes, evaluate_coefficients, eq_comm]

theorem pure_volumes_zero {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (coefficients α s z)) (i : Fin 3) : bodyVolume (K i) = 0 := by
  first
  | have h := (realizes_iff α s z K).mp hK (Pi.single i 1) (by
      intro j
      by_cases hji : j = i <;> simp [Pi.single_apply, hji])
    rw [volumeFunction, weightedSum_single, one_smul] at h
    fin_cases i <;> simpa [value, Pi.single_apply] using h

theorem pair_volumes {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (coefficients α s z)) :
    bodyVolume (K 0 + K 1) = 3 * α + 3 ∧
    bodyVolume (K 0 + K 2) = 3 * α + 3 * s ∧
    bodyVolume (K 1 + K 2) = 6 := by
  first
  | have hvol := (realizes_iff α s z K).mp hK
    have h01 := hvol ![1, 1, 0] (by intro i; fin_cases i <;> norm_num)
    have h02 := hvol ![1, 0, 1] (by intro i; fin_cases i <;> norm_num)
    have h12 := hvol ![0, 1, 1] (by intro i; fin_cases i <;> norm_num)
    norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h01 h02 h12
    exact ⟨h01, h02, h12⟩

def nextBody : Fin 3 → Fin 3 := ![1, 2, 0]

theorem second_difference_positive {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z)) (i : Fin 3) :
    0 < bodyVolume (K (nextBody i) + (2 : ℝ) • K i) -
      2 * bodyVolume (K (nextBody i) + K i) + bodyVolume (K (nextBody i)) := by
  first
  | have hvol := (realizes_iff α s z K).mp hK
    obtain ⟨h01, h02, h12⟩ := pair_volumes hK
    have hzero := pure_volumes_zero hK
    fin_cases i
    · have h2 := hvol ![2, 1, 0] (by intro j; fin_cases j <;> norm_num)
      norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h2
      change 0 < bodyVolume (K 1 + (2 : ℝ) • K 0) -
        2 * bodyVolume (K 1 + K 0) + bodyVolume (K 1)
      rw [add_comm (K 1) ((2 : ℝ) • K 0), add_comm (K 1) (K 0), h2, h01, hzero]
      linarith
    · have h2 := hvol ![0, 2, 1] (by intro j; fin_cases j <;> norm_num)
      norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h2
      change 0 < bodyVolume (K 2 + (2 : ℝ) • K 1) -
        2 * bodyVolume (K 2 + K 1) + bodyVolume (K 2)
      rw [add_comm (K 2) ((2 : ℝ) • K 1), add_comm (K 2) (K 1), h2, h12, hzero]
      norm_num
    · have h2 := hvol ![1, 0, 2] (by intro j; fin_cases j <;> norm_num)
      norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h2
      change 0 < bodyVolume (K 0 + (2 : ℝ) • K 2) -
        2 * bodyVolume (K 0 + K 2) + bodyVolume (K 0)
      rw [h2, h02, hzero]
      linarith

/-- The first geometric assertion of Proposition 3.1, with the full parameter
range and every realization retained. -/
theorem centered_linearHulls_are_planes {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (h0 : ∀ i, (0 : Space 3) ∈ K i) (i : Fin 3) :
    finrank ℝ (linearHull (K i)) = 2 := by
  first
  | have hproper := (bodyVolume_eq_zero_iff_linearHull_ne_top (h0 i)).mp
      (pure_volumes_zero hK i)
    have hlt := Submodule.finrank_lt hproper
    have hspace : finrank ℝ (Space 3) = 3 := by simp [Space]
    rw [hspace] at hlt
    have hnot : ¬ finrank ℝ (linearHull (K i)) ≤ 1 := by
      intro hdim
      obtain ⟨a, b, _, _, hseg⟩ := exists_segment_of_finrank_linearHull_le_one (K i) (h0 i) hdim
      have hz := bodyVolume_segment_second_difference (K i) (K (nextBody i)) ⟨a, b, hseg⟩
      have hp := second_difference_positive hα hs hK i
      rw [hz] at hp
      exact lt_irrefl 0 hp
    omega

theorem pair_volumes_positive {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (i j : Fin 3) (hij : i ≠ j) : 0 < bodyVolume (K i + K j) := by
  first
  | obtain ⟨h01, h02, h12⟩ := pair_volumes hK
    have hp01 : 0 < bodyVolume (K 0 + K 1) := by rw [h01]; linarith
    have hp02 : 0 < bodyVolume (K 0 + K 2) := by rw [h02]; linarith
    have hp12 : 0 < bodyVolume (K 1 + K 2) := by rw [h12]; norm_num
    have hp10 : 0 < bodyVolume (K 1 + K 0) := by rwa [add_comm]
    have hp20 : 0 < bodyVolume (K 2 + K 0) := by rwa [add_comm]
    have hp21 : 0 < bodyVolume (K 2 + K 1) := by rwa [add_comm]
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact (hij rfl).elim
      | exact hp01
      | exact hp02
      | exact hp12
      | exact hp10
      | exact hp20
      | exact hp21

theorem centered_pair_linearHulls_eq_top {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (h0 : ∀ i, (0 : Space 3) ∈ K i) (i j : Fin 3) (hij : i ≠ j) :
    linearHull (K i) ⊔ linearHull (K j) = ⊤ := by
  first
  | have h := (bodyVolume_pos_iff_linearHull_eq_top
      (zero_mem_body_add (h0 i) (h0 j))).mp (pair_volumes_positive hα hs hK i j hij)
    rwa [linearHull_add (h0 i) (h0 j)] at h

theorem centered_plane_intersection_is_line {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (h0 : ∀ i, (0 : Space 3) ∈ K i) (i j : Fin 3) (hij : i ≠ j) :
    finrank ℝ ((linearHull (K i) ⊓ linearHull (K j)) : Submodule ℝ (Space 3)) = 1 := by
  first
  | have h := Submodule.finrank_sup_add_finrank_inf_eq (linearHull (K i)) (linearHull (K j))
    rw [centered_pair_linearHulls_eq_top hα hs hK h0 i j hij,
      centered_linearHulls_are_planes hα hs hK h0 i,
      centered_linearHulls_are_planes hα hs hK h0 j] at h
    have hspace : finrank ℝ (⊤ : Submodule ℝ (Space 3)) = 3 := by simp [Space]
    rw [hspace] at h
    omega

theorem exists_centered_planar_realization {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z)) :
    ∃ p : Fin 3 → Space 3, (∀ i, p i ∈ K i) ∧
      Realizes (fun i => translateBody (-p i) (K i)) (coefficients α s z) ∧
      ∀ i, (0 : Space 3) ∈ translateBody (-p i) (K i) ∧
        finrank ℝ (linearHull (translateBody (-p i) (K i))) = 2 := by
  first
  | choose p hp using fun i => (K i).nonempty
    have hreal := hK.translate (fun i => -p i)
    have h0 : ∀ i, (0 : Space 3) ∈ translateBody (-p i) (K i) :=
      fun i => zero_mem_translateBody_neg (hp i)
    exact ⟨p, hp, hreal, fun i => ⟨h0 i, centered_linearHulls_are_planes hα hs hreal h0 i⟩⟩

end VolumePolynomials.CubicSlice
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CubicSlice.lean -/

/- BEGIN SOURCE: VolumePolynomials/HigherLiftCoefficients.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # The exact higher-dimensional coefficient slice

These definitions and evaluation lemmas are shared by the two geometric
implications. Their declaration bodies are preserved from HigherLiftConverse;
no construction or existence of a realizing tuple is part of this specification.
-/

open Set MeasureTheory MvPolynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

def correction (k : ℕ) : ℝ := 2 * (k + 1 : ℝ) / (k + 2 : ℝ)

def polynomial (k : ℕ) (α s z : ℝ) : MvPolynomial (Fin 3) ℝ :=
  X 0 ^ k * CubicSlice.polynomial (correction k * α) s z

theorem polynomial_homogeneous (k : ℕ) (α s z : ℝ) :
    (polynomial k α s z).IsHomogeneous (3 + k) := by
  first
  | simpa only [polynomial, Nat.add_comm, one_mul] using
      ((isHomogeneous_X ℝ (0 : Fin 3)).pow k).mul
        (CubicSlice.polynomial_homogeneous (correction k * α) s z)

def coefficients (k : ℕ) (α s z : ℝ) : Coefficients 3 (3 + k) :=
  coefficientsOfPolynomial (polynomial k α s z)

theorem evaluate_coefficients (k : ℕ) (α s z : ℝ) (t : Fin 3 → ℝ) :
    evaluate (coefficients k α s z) t =
      t 0 ^ k * CubicSlice.value (correction k * α) s z t := by
  first
  | rw [coefficients, evaluate_eq_polynomial_eval,
      coefficientPolynomial_coefficientsOfPolynomial _ (polynomial_homogeneous k α s z)]
    simp only [polynomial, map_mul, map_pow, eval_X,
      ← CubicSlice.evaluate_coefficients, CubicSlice.coefficients,
      evaluate_eq_polynomial_eval,
      coefficientPolynomial_coefficientsOfPolynomial _
        (CubicSlice.polynomial_homogeneous (correction k * α) s z)]

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HigherLiftCoefficients.lean -/

/- BEGIN SOURCE: VolumePolynomials/RealizationCone.lean -/
section

@[expose] public section

/-!
# Scaling and zero-volume realizations

The zero-coefficient conclusion below is derived from actual geometric
monotonicity, without assuming coefficient nonnegativity or Minkowski's
polynomial-existence theorem.
-/

noncomputable section
open Set MeasureTheory Finset
open scoped Pointwise BigOperators NNReal

namespace VolumePolynomials

theorem evaluate_smul {n d : ℕ} (r : ℝ) (c : Coefficients n d) (t : Fin n → ℝ) :
    evaluate (r • c) t = r * evaluate c t := by
  simp [evaluate, Finset.mul_sum, mul_assoc]

theorem weightedSum_smul {n d : ℕ} (r : ℝ) (K : Fin n → Body d) (t : Fin n → ℝ) :
    weightedSum (fun i => r • K i) t = r • weightedSum K t := by
  simp [weightedSum, Finset.smul_sum, smul_smul, mul_comm]

theorem Realizes.dilate {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c) {r : ℝ} (hr : 0 ≤ r) :
    Realizes (fun i => r • K i) (r ^ d • c) := by
  intro t ht
  rw [evaluate_smul, h t ht]
  simp only [volumeFunction, weightedSum_smul, bodyVolume_smul _ hr]

theorem smul_mem_volumeLocus {n d : ℕ} (hd : 0 < d) {c : Coefficients n d}
    (hc : c ∈ VolumeLocus n d) {a : ℝ} (ha : 0 ≤ a) : a • c ∈ VolumeLocus n d := by
  obtain ⟨K, hK⟩ := hc
  have h := hK.dilate (Real.rpow_nonneg ha ((d : ℝ)⁻¹))
  rw [Real.rpow_inv_natCast_pow ha hd.ne'] at h
  exact ⟨_, h⟩

theorem bodyVolume_mono {d : ℕ} {K L : Body d} (h : K ≤ L) :
    bodyVolume K ≤ bodyVolume L :=
  ENNReal.toReal_mono L.isCompact.measure_lt_top.ne (measure_mono h)

theorem weightedSum_le_smul_of_zero_mem {n d : ℕ} (K : Fin n → Body d)
    (h0 : ∀ i, (0 : Space d) ∈ K i) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {r : ℝ} (hr : 0 ≤ r) (htr : ∀ i, t i ≤ r) : weightedSum K t ≤ r • ∑ i, K i := by
  rw [Finset.smul_sum]
  apply sum_body_mono
  intro i
  change (⟨t i, ht i⟩ : ℝ≥0) • K i ≤ (⟨r, hr⟩ : ℝ≥0) • K i
  exact (K i).smul_le_of_le (h0 i) (htr i)

theorem volumeFunction_le_of_zero_mem {n d : ℕ} (K : Fin n → Body d)
    (h0 : ∀ i, (0 : Space d) ∈ K i) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {r : ℝ} (hr : 0 ≤ r) (htr : ∀ i, t i ≤ r) :
    volumeFunction K t ≤ r ^ d * bodyVolume (∑ i, K i) := by
  calc
    volumeFunction K t ≤ bodyVolume (r • ∑ i, K i) :=
      bodyVolume_mono (weightedSum_le_smul_of_zero_mem K h0 t ht hr htr)
    _ = r ^ d * bodyVolume (∑ i, K i) := bodyVolume_smul _ hr

theorem volumeFunction_le {n d : ℕ} (K : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {r : ℝ} (hr : 0 ≤ r)
    (htr : ∀ i, t i ≤ r) :
    volumeFunction K t ≤ r ^ d * bodyVolume (∑ i, K i) := by
  choose p hp using fun i => (K i).nonempty
  let L : Fin n → Body d := fun i => translateBody (-p i) (K i)
  have h0 : ∀ i, (0 : Space d) ∈ L i := by
    intro i
    simpa [L, mem_translateBody] using hp i
  have h := volumeFunction_le_of_zero_mem L h0 t ht hr htr
  have hsum : bodyVolume (∑ i, L i) = bodyVolume (∑ i, K i) := by
    simpa only [volumeFunction, weightedSum_one] using
      volumeFunction_translate K (fun i => -p i) (fun _ => 1)
  rwa [hsum, volumeFunction_translate] at h

theorem Realizes.evaluate_le_sum {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    evaluate c t ≤ (1 + ∑ i, t i) ^ d * ∑ α, c α := by
  rw [hc t ht, hc.sum_coefficients]
  apply volumeFunction_le K t ht
  · exact add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => ht i)
  · intro i
    exact (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)

/-- A realizing tuple of total volume zero realizes only the zero polynomial.
This includes all configurations whose total Minkowski sum is lower dimensional. -/
theorem Realizes.eq_zero_of_sum_eq_zero {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) (hzero : ∑ α, c α = 0) : c = 0 := by
  apply coefficients_eq_of_evaluate_nonneg
  intro t ht
  have hu := hc.evaluate_le_sum t ht
  rw [hzero, mul_zero] at hu
  have hl := hc.evaluate_nonneg ht
  simpa [evaluate] using le_antisymm hu hl

theorem zero_mem_volumeLocus {n d : ℕ} (hd : 0 < d) :
    (0 : Coefficients n d) ∈ VolumeLocus n d := by
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨fun _ => 0, fun t _ => ?_⟩
  simp [evaluate, volumeFunction, weightedSum, bodyVolume, Measure.real]
  change 0 = (volume {(0 : Space d)}).toReal
  simp

end VolumePolynomials
end -- closes the original EOF section from source line 15
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RealizationCone.lean -/
