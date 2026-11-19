module

public import volume_polynomials.assembly_part01

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

/- BEGIN SOURCE: VolumePolynomials/FiberGrowth.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Volume growth along a fixed subspace

An embedded `k`-dimensional summand changes only the fibers. Fubini gives
upper growth of order `t^k`, and the contained translate in each nonempty
fiber gives a matching lower bound whenever the summand and quotient
projection have positive volume. Both bounds are literal measure bounds.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.FiberGrowth

open ConvexFibers FiberVolume

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def projectionBody (C : ConvexBody (E × U)) : ConvexBody U :=
  mapBody (ContinuousLinearMap.snd ℝ E U) C

theorem coe_projectionBody (C : ConvexBody (E × U)) :
    (projectionBody C : Set U) = projection C := rfl

theorem embedded_sum_fiber (A : ConvexBody E) (C : ConvexBody (E × U)) (y : U) :
    fiberSet (embedBody A + C) y = (A : Set E) + fiberSet C y := by
  first
  | ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, ⟨b, z⟩, hbz, heq⟩
      have hz : z = y := by simpa using congrArg Prod.snd heq
      subst z
      exact ⟨a, ha, b, hbz, congrArg Prod.fst heq⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨(a, 0), ⟨a, ha, rfl⟩, (b, y), hb, Prod.ext hab (zero_add _)⟩

theorem embedded_sum_fiber_of_notMem (A : ConvexBody E) (C : ConvexBody (E × U))
    {y : U} (hy : y ∉ projection C) : fiberSet (embedBody A + C) y = ∅ := by
  first
  | have he : fiberSet C y = ∅ := Set.not_nonempty_iff_eq_empty.mp
      (fun h => hy ((fiberSet_nonempty_iff C y).mp h))
    rw [embedded_sum_fiber, he, Set.add_empty]

theorem embedded_sum_fiber_of_mem (A : ConvexBody E) (C : ConvexBody (E × U))
    {y : U} (hy : y ∈ projection C) :
    fiberSet (embedBody A + C) y = (A + fiberBody C y : ConvexBody E) := by
  first
  | rw [embedded_sum_fiber, ConvexBody.coe_add, coe_fiberBody C hy]

theorem map_snd_embedBody (A : ConvexBody E) :
    mapBody (ContinuousLinearMap.snd ℝ E U) (embedBody A) = 0 := by
  first
  | apply ConvexBody.ext
    ext y
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rfl
    · intro hy
      have hy0 : y = 0 := hy
      subst y
      obtain ⟨a, ha⟩ := A.nonempty
      exact ⟨(a, 0), ⟨a, ha, rfl⟩, rfl⟩

section Coordinates

variable {k q : ℕ}

theorem upper_bound (A : Body k) (C : ConvexBody (Space k × Space q))
    {t : ℝ} (ht : 1 ≤ t) :
    volume.real ((embedBody (t • A) + C : ConvexBody (Space k × Space q)) : Set (Space k × Space q)) ≤
      t ^ k * volume.real ((embedBody A + C : ConvexBody (Space k × Space q)) : Set (Space k × Space q)) := by
  first
  | have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hpoint (y : Space q) :
        volume.real (fiberSet (embedBody (t • A) + C) y) ≤
          t ^ k * volume.real (fiberSet (embedBody A + C) y) := by
      by_cases hy : y ∈ projection C
      · rw [embedded_sum_fiber_of_mem _ _ hy, embedded_sum_fiber_of_mem _ _ hy]
        have hw : ∀ i : Fin 2, 0 ≤ (![t, 1] : Fin 2 → ℝ) i := by
          intro i
          fin_cases i <;> first | exact ht0 | exact zero_le_one
        have hb : ∀ i : Fin 2, (![t, 1] : Fin 2 → ℝ) i ≤ t := by
          intro i
          fin_cases i <;> first | exact le_rfl | exact ht
        have h := volumeFunction_le (![A, fiberBody C y] : Fin 2 → Body k) ![t, 1] hw ht0 hb
        simpa only [volumeFunction, weightedSum, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, bodyVolume] using h
      · rw [embedded_sum_fiber_of_notMem _ _ hy, embedded_sum_fiber_of_notMem _ _ hy,
          measureReal_empty, mul_zero]
    rw [realVolume_eq_integral_fibers, realVolume_eq_integral_fibers, ← integral_const_mul]
    exact integral_mono (integrable_fiber_realVolume _)
      ((integrable_fiber_realVolume _).const_mul _) hpoint

theorem lower_bound (A : Body k) (C : ConvexBody (Space k × Space q))
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ k * bodyVolume A * bodyVolume (projectionBody C) ≤
      volume.real ((embedBody (t • A) + C : ConvexBody (Space k × Space q)) : Set (Space k × Space q)) := by
  first
  | let g : Space q → ℝ := (projection C).indicator (fun _ => t ^ k * bodyVolume A)
    have hg : Integrable g :=
      (integrableOn_const (projection_compact C).measure_ne_top).integrable_indicator
        (projection_compact C).measurableSet
    have hpoint (y : Space q) : g y ≤ volume.real (fiberSet (embedBody (t • A) + C) y) := by
      by_cases hy : y ∈ projection C
      · dsimp only [g]
        rw [Set.indicator_of_mem hy, embedded_sum_fiber_of_mem _ _ hy]
        obtain ⟨p, hp⟩ := (fiberBody C y).nonempty
        have hsub : translateBody p (t • A) ≤ t • A + fiberBody C y := by
          rintro x ⟨u, hu, v, hv, rfl⟩
          have hup : u = p := hu
          subst u
          exact ⟨v, hv, p, hp, add_comm _ _⟩
        have h := bodyVolume_mono hsub
        rwa [bodyVolume_translate, bodyVolume_smul _ ht] at h
      · dsimp only [g]
        rw [Set.indicator_of_notMem hy, embedded_sum_fiber_of_notMem _ _ hy, measureReal_empty]
    have hgint : (∫ y : Space q, g y) = t ^ k * bodyVolume A * bodyVolume (projectionBody C) := by
      dsimp only [g]
      rw [integral_indicator (projection_compact C).measurableSet, setIntegral_const]
      simp only [smul_eq_mul, bodyVolume, coe_projectionBody]
      ring
    rw [realVolume_eq_integral_fibers, ← hgint]
    exact integral_mono hg (integrable_fiber_realVolume _) hpoint

end Coordinates
end VolumePolynomials.FiberGrowth
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiberGrowth.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodySubspaceCoordinates.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Coordinates adapted to the actual linear hull of a convex body.
The coordinate factors are finite real coordinate spaces with their actual
Lebesgue measures. Complement and basis choices construct an equivalence;
they are not geometric hypotheses added to a realization theorem. -/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.SubspaceCoordinates

open FiberGrowth FiberVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def frame (H U : Submodule ℝ E) (hHU : IsCompl H U) :
    E ≃L[ℝ] (Space (finrank ℝ H) × Space (finrank ℝ U)) :=
  ((H.prodEquivOfIsCompl U hHU).symm.trans
    ((Module.finBasis ℝ H).equivFun.prodCongr (Module.finBasis ℝ U).equivFun)).toContinuousLinearEquiv

theorem frame_on_left (H U : Submodule ℝ E) (hHU : IsCompl H U) (x : H) :
    frame H U hHU (x : E) = ((Module.finBasis ℝ H).equivFun x, 0) := by
  first
  | change ((Module.finBasis ℝ H).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).1,
      (Module.finBasis ℝ U).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp only [map_zero]

theorem frame_on_right (H U : Submodule ℝ E) (hHU : IsCompl H U) (x : U) :
    frame H U hHU (x : E) = (0, (Module.finBasis ℝ U).equivFun x) := by
  first
  | change ((Module.finBasis ℝ H).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).1,
      (Module.finBasis ℝ U).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp only [map_zero]

def coordinateBody (H U : Submodule ℝ E) (hHU : IsCompl H U) (K : ConvexBody E) :
    Body (finrank ℝ H) :=
  mapBody (ContinuousLinearMap.fst ℝ (Space (finrank ℝ H)) (Space (finrank ℝ U)))
    (mapBody (frame H U hHU).toContinuousLinearMap K)

theorem frame_body_eq_embed (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hKH : (K : Set E) ⊆ H) :
    mapBody (frame H U hHU).toContinuousLinearMap K = embedBody (coordinateBody H U hHU K) := by
  first
  | have hz (x : E) (hx : x ∈ K) : (frame H U hHU x).2 = 0 := by
      first
      | have h := frame_on_left H U hHU ⟨x, hKH hx⟩
        exact congrArg Prod.snd h
    apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(frame H U hHU x).1, ⟨frame H U hHU x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact Prod.ext rfl (hz x hx).symm
    · rintro ⟨y, ⟨_, ⟨x, hx, rfl⟩, hxy⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      exact Prod.ext hxy (hz x hx)

theorem linearHull_mapBody {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (K : ConvexBody E) :
    linearHull (mapBody f K) = (linearHull K).map f.toLinearMap :=
  (Submodule.map_span f.toLinearMap (K : Set E)).symm

theorem linearHull_map_eq_top {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (hf : Function.Surjective f) (K : ConvexBody E)
    (hK : linearHull K = ⊤) : linearHull (mapBody f K) = ⊤ := by
  first
  | rw [linearHull_mapBody, hK, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

theorem coordinateBody_span_top (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hKH : linearHull K = H) :
    linearHull (coordinateBody H U hHU K) = ⊤ := by
  first
  | rw [coordinateBody, linearHull_mapBody, linearHull_mapBody, ← Submodule.map_comp, hKH]
    apply top_unique
    intro y _
    let x : H := (Module.finBasis ℝ H).equivFun.symm y
    refine ⟨(x : E), x.property, ?_⟩
    change (frame H U hHU (x : E)).1 = y
    rw [frame_on_left]
    exact (Module.finBasis ℝ H).equivFun.apply_symm_apply y

theorem zero_mem_coordinateBody (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hK : (0 : E) ∈ K) :
    (0 : Space (finrank ℝ H)) ∈ coordinateBody H U hHU K := by
  first
  | refine ⟨0, ⟨0, hK, map_zero _⟩, map_zero _⟩

theorem coordinateBody_volume_pos (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hK : (0 : E) ∈ K) (hKH : linearHull K = H) :
    0 < bodyVolume (coordinateBody H U hHU K) :=
  Iff.mpr (bodyVolume_pos_iff_linearHull_eq_top (zero_mem_coordinateBody H U hHU K hK))
    (coordinateBody_span_top H U hHU K hKH)

theorem projection_span_top (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K L : ConvexBody E) (hKH : (K : Set E) ⊆ H)
    (hfull : linearHull (K + L) = ⊤) :
    linearHull (projectionBody (mapBody (frame H U hHU).toContinuousLinearMap L)) = ⊤ := by
  first
  | let T := (frame H U hHU).toContinuousLinearMap
    let snd := ContinuousLinearMap.snd ℝ (Space (finrank ℝ H)) (Space (finrank ℝ U))
    have hfullT := linearHull_map_eq_top T (frame H U hHU).surjective (K + L) hfull
    have hsnd : Function.Surjective snd := fun y => ⟨(0, y), rfl⟩
    have hfullP := linearHull_map_eq_top snd hsnd (mapBody T (K + L)) hfullT
    have heq : mapBody snd (mapBody T (K + L)) = projectionBody (mapBody T L) := by
      first
      | rw [mapBody_add, mapBody_add]
        have hK := frame_body_eq_embed H U hHU K hKH
        change mapBody snd (mapBody (frame H U hHU).toContinuousLinearMap K) + _ = _
        rw [hK, map_snd_embedBody, zero_add]
        rfl
    rwa [heq] at hfullP

theorem projection_volume_pos (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K L : ConvexBody E) (hKH : (K : Set E) ⊆ H) (hL : (0 : E) ∈ L)
    (hfull : linearHull (K + L) = ⊤) :
    0 < bodyVolume (projectionBody (mapBody (frame H U hHU).toContinuousLinearMap L)) := by
  first
  | apply Iff.mpr (bodyVolume_pos_iff_linearHull_eq_top _)
      (projection_span_top H U hHU K L hKH hfull)
    exact ⟨0, ⟨0, hL, map_zero _⟩, map_zero _⟩

end VolumePolynomials.SubspaceCoordinates
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodySubspaceCoordinates.lean -/

/- BEGIN SOURCE: VolumePolynomials/BodyDimensionGrowth.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Dimension is the exponent of volume growth

Every full-dimensional sum `K + L` has two-sided growth of exact order
`t^(dim K)` when only `K` is dilated. The proof constructs subspace
coordinates and uses the literal fiber bounds. This supplies the geometric
foundation of Lemma 2.1 in every dimension.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

def affineDimension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) : ℕ := finrank ℝ (vectorSpan ℝ (K : Set E))

theorem affineDimension_eq_direction_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) : affineDimension K = finrank ℝ (affineSpan ℝ (K : Set E)).direction := by
  first
  | rw [direction_affineSpan]
    rfl

theorem linearHull_translate_eq_vectorSpan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) {p : E} (hp : p ∈ K) :
    linearHull (translateBody (-p) K) = vectorSpan ℝ (K : Set E) := by
  first
  | rw [linearHull, vectorSpan_eq_span_vsub_set_right ℝ hp]
    congr 1
    rw [coe_translateBody]
    change (fun x : E => -p + x) '' (K : Set E) = (fun x : E => x - p) '' (K : Set E)
    congr 1
    funext x
    abel

theorem bodyVolume_pos_iff_affineSpan_eq_top {d : ℕ} (K : Body d) :
    0 < bodyVolume K ↔ affineSpan ℝ (K : Set (Space d)) = ⊤ := by
  first
  | have hreal : 0 < bodyVolume K ↔ 0 < volume (K : Set (Space d)) := by
      first
      | constructor
        · intro h
          exact (ENNReal.toReal_pos_iff.mp h).1
        · intro h
          exact ENNReal.toReal_pos h.ne' (bodyVolume_finite K)
    have hpos : 0 < volume (K : Set (Space d)) ↔
        (interior (K : Set (Space d))).Nonempty := by
      first
      | rw [pos_iff_ne_zero, ← measure_interior_of_null_frontier (K.convex.addHaar_frontier volume)]
        simpa only [Set.nonempty_iff_ne_empty] using
          not_congr (isOpen_interior.measure_eq_zero_iff volume)
    rw [hreal, hpos, K.convex.interior_nonempty_iff_affineSpan_eq_top]

theorem centered_volume_growth {d : ℕ} (K L : Body d)
    (hK : (0 : Space d) ∈ K) (hL : (0 : Space d) ∈ L)
    (hfull : 0 < bodyVolume (K + L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      c * t ^ finrank ℝ (linearHull K) ≤ bodyVolume (t • K + L) ∧
        bodyVolume (t • K + L) ≤ C * t ^ finrank ℝ (linearHull K) := by
  first
  | let H := linearHull K
    obtain ⟨U, hHU⟩ := Submodule.exists_isCompl H
    let T := SubspaceCoordinates.frame H U hHU
    let A := SubspaceCoordinates.coordinateBody H U hHU K
    let B := mapBody T.toContinuousLinearMap L
    let J : ℝ := LinearFrame.volumeFactor T
    have hJ : 0 < J := by exact_mod_cast LinearFrame.volumeFactor_pos T
    have hKH : (K : Set (Space d)) ⊆ H := fun _ hx => mem_linearHull hx
    have htotal : linearHull (K + L) = ⊤ :=
      (bodyVolume_pos_iff_linearHull_eq_top (zero_mem_body_add hK hL)).mp hfull
    have hA : 0 < bodyVolume A := SubspaceCoordinates.coordinateBody_volume_pos H U hHU K hK rfl
    have hB : 0 < bodyVolume (FiberGrowth.projectionBody B) :=
      SubspaceCoordinates.projection_volume_pos H U hHU K L hKH hL htotal
    have hmap (t : ℝ) : mapBody T.toContinuousLinearMap (t • K + L) =
        FiberVolume.embedBody (t • A) + B := by
      first
      | rw [mapBody_add, mapBody_smul]
        have hKA := SubspaceCoordinates.frame_body_eq_embed H U hHU K hKH
        change t • mapBody (SubspaceCoordinates.frame H U hHU).toContinuousLinearMap K + B = _
        rw [hKA]
        congr 1
        exact (mapBody_smul
          (ContinuousLinearMap.inl ℝ (Space (finrank ℝ H)) (Space (finrank ℝ U))) t A).symm
    have hvolume (t : ℝ) : bodyVolume (t • K + L) =
        J * volume.real ((FiberVolume.embedBody (t • A) + B :
          ConvexBody (Space (finrank ℝ H) × Space (finrank ℝ U))) :
          Set (Space (finrank ℝ H) × Space (finrank ℝ U))) := by
      first
      | have h := LinearFrame.realVolume_eq_factor_mul_image T (t • K + L : Set (Space d))
        change bodyVolume (t • K + L) = J * volume.real
          (mapBody T.toContinuousLinearMap (t • K + L) : Set (Space (finrank ℝ H) × Space (finrank ℝ U))) at h
        rwa [hmap] at h
    have hbase : bodyVolume (K + L) =
        J * volume.real ((FiberVolume.embedBody A + B :
          ConvexBody (Space (finrank ℝ H) × Space (finrank ℝ U))) :
          Set (Space (finrank ℝ H) × Space (finrank ℝ U))) := by
      first
      | simpa only [one_smul] using hvolume 1
    refine ⟨J * bodyVolume A * bodyVolume (FiberGrowth.projectionBody B), bodyVolume (K + L),
      mul_pos (mul_pos hJ hA) hB, hfull, ?_⟩
    intro t ht
    constructor
    · rw [hvolume]
      have h := mul_le_mul_of_nonneg_left (FiberGrowth.lower_bound A B (zero_le_one.trans ht)) hJ.le
      change (J * bodyVolume A * bodyVolume (FiberGrowth.projectionBody B)) * t ^ finrank ℝ H ≤ _
      nlinarith only [h]
    · rw [hvolume, hbase]
      have h := mul_le_mul_of_nonneg_left (FiberGrowth.upper_bound A B ht) hJ.le
      change _ ≤ (J * volume.real ((FiberVolume.embedBody A + B :
        ConvexBody (Space (finrank ℝ H) × Space (finrank ℝ U))) :
        Set (Space (finrank ℝ H) × Space (finrank ℝ U)))) * t ^ finrank ℝ H
      nlinarith only [h]

/-- Exact growth order for arbitrary translations and lower-dimensional
summands, under the paper's full-dimensional total-sum hypothesis. -/
theorem volume_growth {d : ℕ} (K L : Body d) (hfull : 0 < bodyVolume (K + L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      c * t ^ affineDimension K ≤ bodyVolume (t • K + L) ∧
        bodyVolume (t • K + L) ≤ C * t ^ affineDimension K := by
  first
  | obtain ⟨p, hp⟩ := K.nonempty
    obtain ⟨q, hq⟩ := L.nonempty
    let K' := translateBody (-p) K
    let L' := translateBody (-q) L
    have hvol (t : ℝ) : bodyVolume (t • K' + L') = bodyVolume (t • K + L) := by
      first
      | have h := volumeFunction_translate (![K, L] : Fin 2 → Body d) ![-p, -q] ![t, 1]
        simpa only [volumeFunction, weightedSum, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] using h
    have hfull' : 0 < bodyVolume (K' + L') := by
      first
      | have heq : bodyVolume (K' + L') = bodyVolume (K + L) := by
          simpa only [one_smul] using hvol 1
        rwa [heq]
    obtain ⟨c, C, hc, hC, hbound⟩ := centered_volume_growth K' L'
      (zero_mem_translateBody_neg hp) (zero_mem_translateBody_neg hq) hfull'
    refine ⟨c, C, hc, hC, ?_⟩
    intro t ht
    have h := hbound t ht
    rw [hvol] at h
    have hdim : finrank ℝ (linearHull K') = affineDimension K := by
      first
      | dsimp only [K']
        rw [linearHull_translate_eq_vectorSpan K hp]
        rfl
    simpa only [hdim] using h

theorem exponent_le_of_growth_bound {a b : ℕ} {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ t : ℝ, 1 ≤ t → c * t ^ a ≤ C * t ^ b) : a ≤ b := by
  first
  | by_contra hab
    have hba : b + 1 ≤ a := by omega
    let t := max 1 (C / c + 1)
    have ht : 1 ≤ t := le_max_left _ _
    have htpos : 0 < t := zero_lt_one.trans_le ht
    have hp := pow_le_pow_right₀ ht hba
    have h := (mul_le_mul_of_nonneg_left hp hc.le).trans (hbound t ht)
    rw [pow_succ] at h
    have hct : c * t ≤ C := by
      first
      | apply Iff.mp (mul_le_mul_iff_left₀ (pow_pos htpos b))
        nlinarith only [h]
    have hlarge : C / c + 1 ≤ t := le_max_right _ _
    have hlarge' := mul_le_mul_of_nonneg_left hlarge hc.le
    have hcancel : c * (C / c) = C := mul_div_cancel₀ C hc.ne'
    nlinarith

theorem affineDimension_eq_of_growth {d m : ℕ} (K L : Body d)
    (hfull : 0 < bodyVolume (K + L)) {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ t : ℝ, 1 ≤ t → c * t ^ m ≤ bodyVolume (t • K + L) ∧
      bodyVolume (t • K + L) ≤ C * t ^ m) : affineDimension K = m := by
  first
  | obtain ⟨a, A, ha, hA, hgrowth⟩ := volume_growth K L hfull
    apply le_antisymm
    · exact exponent_le_of_growth_bound ha (fun t ht =>
        (hgrowth t ht).1.trans (hbound t ht).2)
    · exact exponent_le_of_growth_bound hc (fun t ht =>
        (hbound t ht).1.trans (hgrowth t ht).2)

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BodyDimensionGrowth.lean -/

/- BEGIN SOURCE: VolumePolynomials/DegreeDimension.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Degrees and dimensions of every partial Minkowski sum

The support statement is derived from actual volume growth, rather than from
an assumed positivity criterion for mixed volumes. The empty partial sum is
also covered; its value is the point body at zero and its dimension is zero.
-/

open Set Finset MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials

def partialBodySum {n d : ℕ} (K : Fin n → Body d) (I : Finset (Fin n)) : Body d :=
  ∑ i ∈ I, K i

def partialExponent {n d : ℕ} (I : Finset (Fin n)) (α : MultiIndex n d) : ℕ :=
  ∑ i ∈ I, (α.1 i : ℕ)

def partialWeights {n : ℕ} (I : Finset (Fin n)) (t : ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then t else 1

theorem partialBodySum_add_compl {n d : ℕ} (K : Fin n → Body d)
    (I : Finset (Fin n)) : partialBodySum K I + partialBodySum K Iᶜ = ∑ i, K i := by
  first
  | classical
    exact Finset.sum_add_sum_compl I K

theorem partialWeights_nonneg {n : ℕ} (I : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i, 0 ≤ partialWeights I t i := by
  first
  | intro i
    simp only [partialWeights]
    split_ifs <;> positivity

theorem weightedSum_partialWeights {n d : ℕ} (K : Fin n → Body d)
    (I : Finset (Fin n)) (t : ℝ) :
    weightedSum K (partialWeights I t) = t • partialBodySum K I + partialBodySum K Iᶜ := by
  first
  | classical
    rw [weightedSum, partialBodySum, partialBodySum, Finset.smul_sum]
    calc
      (∑ i, partialWeights I t i • K i) =
          ∑ i, if i ∈ I then t • K i else K i := by
        first
        | apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ I <;> simp [partialWeights, hi]
      _ = (∑ i ∈ I, t • K i) + ∑ i ∈ Iᶜ, K i := by
        first
        | simpa only [Finset.piecewise, Finset.univ_inter, Finset.compl_eq_univ_sdiff] using
            Finset.sum_piecewise (Finset.univ : Finset (Fin n)) I (fun i => t • K i) K

theorem evaluate_partialWeights {n d : ℕ} (c : Coefficients n d)
    (I : Finset (Fin n)) (t : ℝ) :
    evaluate c (partialWeights I t) = ∑ α, c α * t ^ partialExponent I α := by
  first
  | classical
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    calc
      (∏ i, partialWeights I t i ^ (α.1 i : ℕ)) =
          ∏ i, if i ∈ I then t ^ (α.1 i : ℕ) else 1 := by
        first
        | apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i ∈ I <;> simp [partialWeights, hi]
      _ = ∏ i ∈ I, t ^ (α.1 i : ℕ) := by
        first
        | exact Fintype.prod_ite_mem I _
      _ = t ^ partialExponent I α := Finset.prod_pow_eq_pow_sum I _ t

theorem Realizes.partial_volume_formula {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) (I : Finset (Fin n))
    {t : ℝ} (ht : 0 ≤ t) :
    bodyVolume (t • partialBodySum K I + partialBodySum K Iᶜ) =
      ∑ α, c α * t ^ partialExponent I α := by
  first
  | have hv := h (partialWeights I t) (partialWeights_nonneg I ht)
    rw [evaluate_partialWeights, volumeFunction, weightedSum_partialWeights] at hv
    exact hv.symm

theorem finite_nonnegative_polynomial_growth {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : ι → ℕ) (ha : ∀ i, 0 ≤ a i)
    (hpos : 0 < ∑ i, a i) :
    ∃ j, 0 < a j ∧ (∀ i, a i ≠ 0 → e i ≤ e j) ∧
      ∀ t : ℝ, 1 ≤ t →
        a j * t ^ e j ≤ ∑ i, a i * t ^ e i ∧
          (∑ i, a i * t ^ e i) ≤ (∑ i, a i) * t ^ e j := by
  first
  | classical
    let S : Finset ι := Finset.univ.filter (fun i => a i ≠ 0)
    have hS : S.Nonempty := by
      first
      | by_contra h
        have hz : ∀ i, a i = 0 := by
          first
          | intro i
            by_contra hi
            exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        simp only [hz, Finset.sum_const_zero, lt_self_iff_false] at hpos
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S e hS
    have hjpos : 0 < a j := lt_of_le_of_ne (ha j)
      (Ne.symm (Finset.mem_filter.mp hj).2)
    have hle (i : ι) (hi : a i ≠ 0) : e i ≤ e j :=
      hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    refine ⟨j, hjpos, hle, ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    constructor
    · exact Finset.single_le_sum (fun i _ => mul_nonneg (ha i) (pow_nonneg ht0 _))
        (Finset.mem_univ j)
    · calc
        (∑ i, a i * t ^ e i) ≤ ∑ i, a i * t ^ e j := by
          first
          | apply Finset.sum_le_sum
            intro i _
            by_cases hi : a i = 0
            · simp only [hi, zero_mul, le_refl]
            · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (hle i hi)) (ha i)
        _ = (∑ i, a i) * t ^ e j := (Finset.sum_mul ..).symm

/-- Lemma 2.1, expressed without a convention for the maximum of an empty
support: a positive coefficient attains the affine dimension, and every other
nonzero coefficient has no larger partial exponent. -/
theorem degree_dimension {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c)
    (hfull : 0 < bodyVolume (∑ i, K i)) (I : Finset (Fin n)) :
    ∃ α : MultiIndex n d, 0 < c α ∧
      partialExponent I α = affineDimension (partialBodySum K I) ∧
      ∀ β : MultiIndex n d, c β ≠ 0 →
        partialExponent I β ≤ affineDimension (partialBodySum K I) := by
  first
  | have hc : ∀ α, 0 ≤ c α := Realizes.coefficients_nonnegative h
    have hsum : 0 < ∑ α, c α := h.sum_coefficients.symm ▸ hfull
    obtain ⟨α, hα, hmax, hgrowth⟩ := finite_nonnegative_polynomial_growth c
      (partialExponent I) hc hsum
    have hfull' : 0 < bodyVolume (partialBodySum K I + partialBodySum K Iᶜ) := by
      first
      | rwa [partialBodySum_add_compl]
    have hdim : affineDimension (partialBodySum K I) = partialExponent I α :=
      affineDimension_eq_of_growth (partialBodySum K I) (partialBodySum K Iᶜ)
        hfull' hα (by
          intro t ht
          rw [Realizes.partial_volume_formula h I (zero_le_one.trans ht)]
          exact hgrowth t ht)
    exact ⟨α, hα, hdim.symm, fun β hβ => (hmax β hβ).trans_eq hdim.symm⟩

/-- The paper's hypothesis of a full-dimensional total body, stated literally
as equality of its affine span with the ambient affine space. -/
theorem lemma_2_1 {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c)
    (hfull : affineSpan ℝ ((∑ i, K i : Body d) : Set (Space d)) = ⊤)
    (I : Finset (Fin n)) (_hI : I.Nonempty) :
    ∃ α : MultiIndex n d, 0 < c α ∧
      partialExponent I α = affineDimension (partialBodySum K I) ∧
      ∀ β : MultiIndex n d, c β ≠ 0 →
        partialExponent I β ≤ affineDimension (partialBodySum K I) := by
  first
  | exact degree_dimension h (Iff.mpr (bodyVolume_pos_iff_affineSpan_eq_top _) hfull) I

theorem degree_dimension_eq_of_support_bound {n d m : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) (I : Finset (Fin n))
    (hupper : ∀ β : MultiIndex n d, c β ≠ 0 → partialExponent I β ≤ m)
    (hlower : ∃ α : MultiIndex n d, 0 < c α ∧ partialExponent I α = m) :
    affineDimension (partialBodySum K I) = m := by
  first
  | obtain ⟨α, hα, heα⟩ := hlower
    have hc := Realizes.coefficients_nonnegative h
    have hsum : 0 < ∑ β, c β := lt_of_lt_of_le hα
      (Finset.single_le_sum (fun β _ => hc β) (Finset.mem_univ α))
    have hfull : 0 < bodyVolume (∑ i, K i) := h.sum_coefficients ▸ hsum
    obtain ⟨β, hβ, heβ, hmax⟩ := degree_dimension h hfull I
    apply le_antisymm
    · rw [← heβ]
      exact hupper β hβ.ne'
    · rw [← heα]
      exact hmax α hα.ne'

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/DegreeDimension.lean -/

/- BEGIN SOURCE: VolumePolynomials/HigherLiftSupport.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The exact support of the lifted slice

All seven possible monomials are retained, including the potentially zero
triple coefficient. Their support bounds, together with the literal degree
and dimension theorem, determine the dimensions in Proposition 6.2.
-/

open Set MvPolynomial Module
open scoped BigOperators Pointwise

namespace VolumePolynomials.HigherLift

def ternaryExponent (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] theorem ternaryExponent_apply (a b c : ℕ) (i : Fin 3) :
    ternaryExponent a b c i = ![a, b, c] i := by
  first
  | fin_cases i <;> simp [ternaryExponent]

theorem ternaryExponent_degree (a b c : ℕ) :
    (ternaryExponent a b c).degree = a + b + c := by
  first
  | simp [Finsupp.degree_eq_sum, Fin.sum_univ_three]

theorem ternaryMonomial (a b c : ℕ) (r : ℝ) :
    (C r * X 0 ^ a * X 1 ^ b * X 2 ^ c : MvPolynomial (Fin 3) ℝ) =
      monomial (ternaryExponent a b c) r := by
  first
  | simp only [C_apply, X_pow_eq_monomial, monomial_mul_monomial,
      zero_add, mul_one, ternaryExponent]

def termExponent (k : ℕ) : Fin 7 → Fin 3 →₀ ℕ :=
  ![ternaryExponent (k + 2) 1 0, ternaryExponent (k + 2) 0 1,
    ternaryExponent (k + 1) 2 0, ternaryExponent k 2 1,
    ternaryExponent (k + 1) 0 2, ternaryExponent k 1 2,
    ternaryExponent (k + 1) 1 1]

def termCoefficient (k : ℕ) (α s z : ℝ) : Fin 7 → ℝ :=
  ![3 * (correction k * α), 3 * (correction k * α), 3, 3, 3 * s, 3, 6 * z]

theorem termExponent_degree (k : ℕ) (j : Fin 7) :
    (termExponent k j).degree = 3 + k := by
  first
  | fin_cases j <;> simp [termExponent, ternaryExponent_degree] <;> omega

def termIndex (k : ℕ) (j : Fin 7) : MultiIndex 3 (3 + k) :=
  multiIndexOfDegree (termExponent k j) (termExponent_degree k j)

@[simp] theorem exponent_termIndex (k : ℕ) (j : Fin 7) :
    exponent (termIndex k j) = termExponent k j :=
  exponent_multiIndexOfDegree _ _

@[simp] theorem termIndex_apply (k : ℕ) (j : Fin 7) (i : Fin 3) :
    ((termIndex k j).1 i : ℕ) = termExponent k j i := rfl

theorem termExponent_injective (k : ℕ) : Function.Injective (termExponent k) := by
  first
  | intro i j hij
    have h0 := congrArg (fun e : Fin 3 →₀ ℕ => e 0) hij
    have h1 := congrArg (fun e : Fin 3 →₀ ℕ => e 1) hij
    have h2 := congrArg (fun e : Fin 3 →₀ ℕ => e 2) hij
    fin_cases i <;> fin_cases j <;>
      simp [termExponent] at h0 h1 h2 ⊢ <;> omega

theorem polynomial_eq_terms (k : ℕ) (α s z : ℝ) :
    polynomial k α s z = ∑ j : Fin 7, monomial (termExponent k j) (termCoefficient k α s z j) := by
  first
  | simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, termExponent, termCoefficient,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    simp only [← ternaryMonomial, polynomial, CubicSlice.polynomial,
      pow_zero, pow_one, pow_add, mul_one]
    ring

theorem coefficients_eq_terms (k : ℕ) (α s z : ℝ) (β : MultiIndex 3 (3 + k)) :
    coefficients k α s z β = ∑ j : Fin 7,
      if termExponent k j = exponent β then termCoefficient k α s z j else 0 := by
  first
  | classical
    simp only [coefficients, coefficientsOfPolynomial, polynomial_eq_terms,
      coeff_sum, coeff_monomial]

theorem coefficient_termIndex (k : ℕ) (α s z : ℝ) (j : Fin 7) :
    coefficients k α s z (termIndex k j) = termCoefficient k α s z j := by
  first
  | classical
    rw [coefficients_eq_terms, exponent_termIndex]
    simp only [(termExponent_injective k).eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem nonzero_coefficient_mem_terms {k : ℕ} {α s z : ℝ}
    (β : MultiIndex 3 (3 + k)) (hβ : coefficients k α s z β ≠ 0) :
    ∃ j : Fin 7, β = termIndex k j := by
  first
  | classical
    by_contra h
    have hne (j : Fin 7) : termExponent k j ≠ exponent β := by
      first
      | intro he
        apply h
        refine ⟨j, ?_⟩
        apply exponent_injective
        rw [exponent_termIndex]
        exact he.symm
    rw [coefficients_eq_terms] at hβ
    simp only [hne, if_false, Finset.sum_const_zero, ne_self_iff_false] at hβ

theorem correction_pos (k : ℕ) : 0 < correction k := by
  first
  | unfold correction
    positivity

theorem triple_parameter_nonnegative {k : ℕ} {α s z : ℝ}
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) : 0 ≤ z := by
  first
  | have h := Realizes.coefficients_nonnegative hK (termIndex k 6)
    rw [coefficient_termIndex] at h
    norm_num [termCoefficient] at h
    linarith

theorem dimensions_of_realization {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    affineDimension (K 0) = k + 2 ∧ affineDimension (K 1) = 2 ∧
      affineDimension (K 2) = 2 ∧ affineDimension (K 1 + K 2) = 3 ∧
      affineDimension (K 0 + K 1) = 3 + k ∧
      affineDimension (K 0 + K 2) = 3 + k := by
  first
  | have hpos0 : 0 < coefficients k α s z (termIndex k 0) := by
      first
      | rw [coefficient_termIndex]
        simpa only [termCoefficient, Matrix.cons_val_zero] using
          mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (correction_pos k) hα)
    have hpos1 : 0 < coefficients k α s z (termIndex k 1) := by
      first
      | rw [coefficient_termIndex]
        change 0 < 3 * (correction k * α)
        exact mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (correction_pos k) hα)
    have hpos2 : 0 < coefficients k α s z (termIndex k 2) := by
      first
      | rw [coefficient_termIndex]
        norm_num [termCoefficient]
    have hpos3 : 0 < coefficients k α s z (termIndex k 3) := by
      first
      | rw [coefficient_termIndex]
        norm_num [termCoefficient]
    have hpos4 : 0 < coefficients k α s z (termIndex k 4) := by
      first
      | rw [coefficient_termIndex]
        change 0 < 3 * s
        exact mul_pos (by norm_num : (0 : ℝ) < 3) hs
    have h0 := degree_dimension_eq_of_support_bound hK ({0} : Finset (Fin 3))
      (m := k + 2) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent] <;> omega)
      ⟨termIndex k 0, hpos0, by simp [partialExponent, termExponent]⟩
    have h1 := degree_dimension_eq_of_support_bound hK ({1} : Finset (Fin 3))
      (m := 2) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent])
      ⟨termIndex k 2, hpos2, by simp [partialExponent, termExponent]⟩
    have h2 := degree_dimension_eq_of_support_bound hK ({2} : Finset (Fin 3))
      (m := 2) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent])
      ⟨termIndex k 4, hpos4, by simp [partialExponent, termExponent]⟩
    have h12 := degree_dimension_eq_of_support_bound hK ({1, 2} : Finset (Fin 3))
      (m := 3) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent])
      ⟨termIndex k 3, hpos3, by simp [partialExponent, termExponent]⟩
    have h01 := degree_dimension_eq_of_support_bound hK ({0, 1} : Finset (Fin 3))
      (m := 3 + k) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent] <;> omega)
      ⟨termIndex k 0, hpos0, by simp [partialExponent, termExponent]; omega⟩
    have h02 := degree_dimension_eq_of_support_bound hK ({0, 2} : Finset (Fin 3))
      (m := 3 + k) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent] <;> omega)
      ⟨termIndex k 1, hpos1, by simp [partialExponent, termExponent]; omega⟩
    simp only [partialBodySum, Finset.sum_singleton, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1),
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2),
      Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)] at h0 h1 h2 h12 h01 h02
    exact ⟨h0, h1, h2, h12, h01, h02⟩

theorem affineDimension_eq_linearHull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (h0 : (0 : E) ∈ K) : affineDimension K = finrank ℝ (linearHull K) := by
  first
  | rw [affineDimension, vectorSpan_eq_span_vsub_set_right ℝ h0]
    change finrank ℝ (Submodule.span ℝ ((fun x : E => x - 0) '' (K : Set E))) =
      finrank ℝ (linearHull K)
    have heq : Submodule.span ℝ ((fun x : E => x - 0) '' (K : Set E)) = linearHull K := by
      rw [show (fun x : E => x - 0) = id from funext (fun x => sub_zero x), Set.image_id]
      rfl
    exact congrArg (fun V : Submodule ℝ E => finrank ℝ V) heq

theorem centered_dimensions {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z))
    (h0 : ∀ i, (0 : Space (3 + k)) ∈ K i) :
    finrank ℝ (linearHull (K 0)) = k + 2 ∧
      finrank ℝ (linearHull (K 1)) = 2 ∧ finrank ℝ (linearHull (K 2)) = 2 ∧
      finrank ℝ ((linearHull (K 1) ⊔ linearHull (K 2)) : Submodule ℝ (Space (3 + k))) = 3 ∧
      linearHull (K 0) ⊔ linearHull (K 1) = ⊤ ∧
      linearHull (K 0) ⊔ linearHull (K 2) = ⊤ := by
  first
  | obtain ⟨hd0, hd1, hd2, hd12, hd01, hd02⟩ := dimensions_of_realization hα hs hK
    rw [affineDimension_eq_linearHull _ (h0 0)] at hd0
    rw [affineDimension_eq_linearHull _ (h0 1)] at hd1
    rw [affineDimension_eq_linearHull _ (h0 2)] at hd2
    rw [affineDimension_eq_linearHull _ (zero_mem_body_add (h0 1) (h0 2)),
      linearHull_add (h0 1) (h0 2)] at hd12
    have hfull (i : Fin 3) (hi : affineDimension (K 0 + K i) = 3 + k) :
        linearHull (K 0) ⊔ linearHull (K i) = ⊤ := by
      first
      | rw [affineDimension_eq_linearHull _ (zero_mem_body_add (h0 0) (h0 i)),
          linearHull_add (h0 0) (h0 i)] at hi
        apply Submodule.eq_top_of_finrank_eq
        simpa [Space] using hi
    exact ⟨hd0, hd1, hd2, hd12, hfull 1 hd01, hfull 2 hd02⟩

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HigherLiftSupport.lean -/

/- BEGIN SOURCE: VolumePolynomials/HigherLiftFrame.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Product coordinates forced by the lifted slice

The quotient complement is constructed inside the first body's hyperplane.
Consequently its fibers in the three-dimensional factor lie in one fixed
plane. No product structure of the original body is assumed.
-/

open Set Module MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

theorem exists_complement_inside {E : Type*} [AddCommGroup E] [Module ℝ E]
    (H W : Submodule ℝ E) (hHW : H ⊔ W = ⊤) :
    ∃ U : Submodule ℝ E, U ≤ H ∧ IsCompl W U ∧ (H ⊓ W) ⊔ U = H := by
  first
  | obtain ⟨V, hV⟩ := Submodule.exists_isCompl (H ⊓ W)
    let U := H ⊓ V
    have hUH : U ≤ H := inf_le_left
    have hsplit : (H ⊓ W) ⊔ U = H := by
      first
      | apply le_antisymm
        · exact sup_le inf_le_left hUH
        · intro x hx
          obtain ⟨e, v, hev, _⟩ := Submodule.existsUnique_add_of_isCompl hV x
          have hvH : (v : E) ∈ H := by
            have hv : (v : E) = x - (e : E) := by rw [← hev]; abel
            rw [hv]
            exact H.sub_mem hx e.property.1
          exact Submodule.mem_sup.mpr ⟨e, e.property, v, ⟨hvH, v.property⟩, hev⟩
    have hinf : W ⊓ U = ⊥ := by
      first
      | change W ⊓ (H ⊓ V) = ⊥
        rw [← inf_assoc, inf_comm W H]
        exact hV.inf_eq_bot
    have hsup : W ⊔ U = ⊤ := by
      first
      | apply top_unique
        rw [← hHW, ← hsplit]
        exact sup_le (sup_le (inf_le_right.trans le_sup_left) le_sup_right) le_sup_left
    exact ⟨U, hUH, IsCompl.of_le hinf.le hsup.ge, hsplit⟩

theorem lifted_subspaces {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z))
    (h0 : ∀ i, (0 : Space (3 + k)) ∈ K i) :
    ∃ U : Submodule ℝ (Space (3 + k)),
      U ≤ linearHull (K 0) ∧
      IsCompl (linearHull (K 1) ⊔ linearHull (K 2)) U ∧
      finrank ℝ U = k ∧
      finrank ℝ ((linearHull (K 0) ⊓ (linearHull (K 1) ⊔ linearHull (K 2))) :
        Submodule ℝ (Space (3 + k))) = 2 ∧
      (linearHull (K 0) ⊓ (linearHull (K 1) ⊔ linearHull (K 2))) ⊔ U = linearHull (K 0) := by
  first
  | obtain ⟨hdH, hdB, hdC, hdW, hHB, hHC⟩ := centered_dimensions hα hs hK h0
    let H := linearHull (K 0)
    let W := linearHull (K 1) ⊔ linearHull (K 2)
    have hHW : H ⊔ W = ⊤ := by
      first
      | change linearHull (K 0) ⊔ (linearHull (K 1) ⊔ linearHull (K 2)) = ⊤
        rw [← sup_assoc, hHB, top_sup_eq]
    have hdE : finrank ℝ ((H ⊓ W) : Submodule ℝ (Space (3 + k))) = 2 := by
      first
      | have h := Submodule.finrank_sup_add_finrank_inf_eq H W
        rw [hHW] at h
        have htop : finrank ℝ (⊤ : Submodule ℝ (Space (3 + k))) = 3 + k := by simp [Space]
        change finrank ℝ H = k + 2 at hdH
        change finrank ℝ W = 3 at hdW
        rw [htop, hdH, hdW] at h
        omega
    obtain ⟨U, hUH, hWU, hsplit⟩ := exists_complement_inside H W hHW
    have hdU : finrank ℝ U = k := by
      first
      | have h := Submodule.finrank_add_eq_of_isCompl hWU
        change finrank ℝ W = 3 at hdW
        rw [hdW] at h
        have hspace : finrank ℝ (Space (3 + k)) = 3 + k := by simp [Space]
        rw [hspace] at h
        omega
    exact ⟨U, hUH, hWU, hdU, hdE, hsplit⟩

variable {k : ℕ}

def threeFrame (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k) :
    Space (3 + k) ≃L[ℝ] (Space 3 × Space k) :=
  ((W.prodEquivOfIsCompl U hWU).symm.trans
    ((LinearEquiv.ofFinrankEq W (Space 3) (by simpa [Space] using hdW)).prodCongr
      (LinearEquiv.ofFinrankEq U (Space k) (by simpa [Space] using hdU)))).toContinuousLinearEquiv

def threeFrameLeft (W : Submodule ℝ (Space (3 + k))) (hdW : finrank ℝ W = 3) :
    W ≃ₗ[ℝ] Space 3 := LinearEquiv.ofFinrankEq W (Space 3) (by simpa [Space] using hdW)

def threeFrameRight (U : Submodule ℝ (Space (3 + k))) (hdU : finrank ℝ U = k) :
    U ≃ₗ[ℝ] Space k := LinearEquiv.ofFinrankEq U (Space k) (by simpa [Space] using hdU)

theorem threeFrame_on_left (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k) (x : W) :
    threeFrame W U hWU hdW hdU (x : Space (3 + k)) = (threeFrameLeft W hdW x, 0) := by
  first
  | change ((threeFrameLeft W hdW) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).1,
      (threeFrameRight U hdU) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp only [map_zero]

theorem threeFrame_on_right (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k) (x : U) :
    threeFrame W U hWU hdW hdU (x : Space (3 + k)) = (0, threeFrameRight U hdU x) := by
  first
  | change ((threeFrameLeft W hdW) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).1,
      (threeFrameRight U hdU) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp only [map_zero]

def sectionPlane (H W : Submodule ℝ (Space (3 + k))) (hdW : finrank ℝ W = 3) :
    Submodule ℝ (Space 3) :=
  (H.comap W.subtype).map (threeFrameLeft W hdW).toLinearMap

theorem sectionPlane_finrank (H W : Submodule ℝ (Space (3 + k)))
    (hdW : finrank ℝ W = 3)
    (hdE : finrank ℝ ((H ⊓ W) : Submodule ℝ (Space (3 + k))) = 2) :
    finrank ℝ (sectionPlane H W hdW) = 2 := by
  first
  | rw [sectionPlane, LinearEquiv.finrank_map_eq]
    have heq : H.comap W.subtype = (H ⊓ W).comap W.subtype := by
      first
      | ext x
        change (x : Space (3 + k)) ∈ H ↔
          (x : Space (3 + k)) ∈ H ∧ (x : Space (3 + k)) ∈ W
        exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
    rw [heq, (Submodule.comapSubtypeEquivOfLe
      (show H ⊓ W ≤ W from inf_le_right)).finrank_eq]
    exact hdE

theorem frame_fiber_subset_plane (H W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hUH : U ≤ H)
    (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (C : Body (3 + k)) (hCH : (C : Set (Space (3 + k))) ⊆ H)
    (y : Space k) :
    ConvexFibers.fiberSet (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap C) y ⊆
      sectionPlane H W hdW := by
  first
  | intro x hx
    obtain ⟨p, hp, hxy⟩ := hx
    let q := (W.prodEquivOfIsCompl U hWU).symm p
    have hq : (q.1 : Space (3 + k)) + (q.2 : Space (3 + k)) = p :=
      (W.prodEquivOfIsCompl U hWU).apply_symm_apply p
    have hleftH : (q.1 : Space (3 + k)) ∈ H := by
      first
      | have heq : (q.1 : Space (3 + k)) = p - (q.2 : Space (3 + k)) := by
          rw [← hq]; abel
        rw [heq]
        exact H.sub_mem (hCH hp) (hUH q.2.property)
    refine ⟨q.1, hleftH, ?_⟩
    exact congrArg Prod.fst hxy

theorem frame_body_in_threeSpace (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (B : Body (3 + k)) (hBW : (B : Set (Space (3 + k))) ⊆ W) :
    mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap B =
      FiberVolume.embedBody (mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
        (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap B)) := by
  first
  | let T := threeFrame W U hWU hdW hdU
    have hz (x : Space (3 + k)) (hx : x ∈ B) : (T x).2 = 0 :=
      congrArg Prod.snd (threeFrame_on_left W U hWU hdW hdU ⟨x, hBW hx⟩)
    apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(T x).1, ⟨T x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact Prod.ext rfl (hz x hx).symm
    · rintro ⟨y, ⟨_, ⟨x, hx, rfl⟩, hxy⟩, rfl⟩
      exact ⟨x, hx, Prod.ext hxy (hz x hx)⟩

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HigherLiftFrame.lean -/

/- BEGIN SOURCE: VolumePolynomials/HigherLiftFiberFrame.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The actual fiber frame of an arbitrary lifted realization

The planes, total fiber body, quotient measure, and positive Jacobian are
constructed from the realizing tuple. The volume identity is a transported
identity of the original bodies, before any independence of the three
planes is proved.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

open ConvexFibers FiberVolume

structure FiberFrameData (k : ℕ) (α s z : ℝ) where
  F : ConvexBody (Space 3 × Space k)
  B : Body 3
  C : Body 3
  J : ℝ
  J_pos : 0 < J
  P : Fin 3 → Submodule ℝ (Space 3)
  planes : ∀ i, finrank ℝ (P i) = 2
  pair_spans : ∀ i j, i ≠ j → P i ⊔ P j = ⊤
  fibers_in_plane : ∀ y, fiberSet F y ⊆ P 0
  B_in_plane : (B : Set (Space 3)) ⊆ P 1
  C_in_plane : (C : Set (Space 3)) ⊆ P 2
  projection_pos : 0 < volume.real (projection F)
  volume_identity : ∀ t : Fin 3 → ℝ, (∀ i, 0 ≤ t i) →
    J * volume.real ((t 0 • F + embedBody (U := Space k) (t 1 • B + t 2 • C) :
      ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k)) =
      evaluate (coefficients k α s z) t

theorem sectionPlane_finrank_of_le {k : ℕ}
    (V W : Submodule ℝ (Space (3 + k))) (hVW : V ≤ W)
    (hdW : finrank ℝ W = 3) (hdV : finrank ℝ V = 2) :
    finrank ℝ (sectionPlane V W hdW) = 2 := by
  first
  | apply sectionPlane_finrank
    exact (congrArg (fun S : Submodule ℝ (Space (3 + k)) => finrank ℝ S)
      (inf_eq_left.mpr hVW)).trans hdV

theorem sectionPlane_sup_eq_top {k : ℕ}
    (H V W : Submodule ℝ (Space (3 + k))) (hVW : V ≤ W)
    (hspan : W ≤ H ⊔ V) (hdW : finrank ℝ W = 3) :
    sectionPlane H W hdW ⊔ sectionPlane V W hdW = ⊤ := by
  first
  | apply top_unique
    intro x _
    let w : W := (threeFrameLeft W hdW).symm x
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hspan w.property)
    have huW : u ∈ W := by
      first
      | have heq : u = (w : Space (3 + k)) - v := by rw [← huv]; abel
        rw [heq]
        exact W.sub_mem w.property (hVW hv)
    let u' : W := ⟨u, huW⟩
    let v' : W := ⟨v, hVW hv⟩
    apply Submodule.mem_sup.mpr
    refine ⟨threeFrameLeft W hdW u', ⟨u', hu, rfl⟩,
      threeFrameLeft W hdW v', ⟨v', hv, rfl⟩, ?_⟩
    rw [← map_add]
    have heq : u' + v' = w := Subtype.ext huv
    rw [heq]
    exact (threeFrameLeft W hdW).apply_symm_apply x

theorem coordinate_body_in_plane {k : ℕ}
    (V W U : Submodule ℝ (Space (3 + k))) (hVW : V ≤ W)
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (K : Body (3 + k)) (hKV : (K : Set (Space (3 + k))) ⊆ V) :
    (mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
      (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap K) : Set (Space 3)) ⊆
      sectionPlane V W hdW := by
  first
  | rintro x ⟨_, ⟨p, hp, rfl⟩, hpx⟩
    refine ⟨(⟨p, hVW (hKV hp)⟩ : W), hKV hp, ?_⟩
    have ht := congrArg Prod.fst
      (threeFrame_on_left W U hWU hdW hdU ⟨p, hVW (hKV hp)⟩)
    exact ht.symm.trans hpx

theorem threeFrame_projection_positive {k : ℕ}
    (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (A B : Body (3 + k)) (hA0 : (0 : Space (3 + k)) ∈ A)
    (hBW : (B : Set (Space (3 + k))) ⊆ W)
    (hfull : linearHull (A + B) = ⊤) :
    0 < volume.real (projection (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap A)) := by
  first
  | let T := threeFrame W U hWU hdW hdU
    let snd := ContinuousLinearMap.snd ℝ (Space 3) (Space k)
    let F := mapBody T.toContinuousLinearMap A
    let Z := mapBody snd F
    have hfullT := SubspaceCoordinates.linearHull_map_eq_top T.toContinuousLinearMap T.surjective
      (A + B) hfull
    have hfullZ := SubspaceCoordinates.linearHull_map_eq_top snd
      (show Function.Surjective snd from fun y => ⟨(0, y), rfl⟩)
      (mapBody T.toContinuousLinearMap (A + B)) hfullT
    have hmapB : mapBody snd (mapBody T.toContinuousLinearMap B) = 0 := by
      first
      | rw [frame_body_in_threeSpace W U hWU hdW hdU B hBW]
        exact FiberGrowth.map_snd_embedBody _
    rw [mapBody_add, mapBody_add, hmapB, add_zero] at hfullZ
    have hZ0 : (0 : Space k) ∈ Z := ⟨0, ⟨0, hA0, map_zero _⟩, map_zero _⟩
    have hp := (bodyVolume_pos_iff_linearHull_eq_top hZ0).mpr hfullZ
    exact hp

theorem exists_fiberFrameData {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    Nonempty (FiberFrameData k α s z) := by
  first
  | classical
    choose p hp using fun i => (K i).nonempty
    let L : Fin 3 → Body (3 + k) := fun i => translateBody (-p i) (K i)
    have hL : Realizes L (coefficients k α s z) := hK.translate (fun i => -p i)
    have h0 (i : Fin 3) : (0 : Space (3 + k)) ∈ L i := zero_mem_translateBody_neg (hp i)
    obtain ⟨hdH, hdB, hdC, hdW, hHB, hHC⟩ := centered_dimensions hα hs hL h0
    obtain ⟨U, hUH, hWU, hdU, hdE, hsplit⟩ := lifted_subspaces hα hs hL h0
    let H := linearHull (L 0)
    let W := linearHull (L 1) ⊔ linearHull (L 2)
    let T := threeFrame W U hWU hdW hdU
    let F := mapBody T.toContinuousLinearMap (L 0)
    let B := mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
      (mapBody T.toContinuousLinearMap (L 1))
    let C := mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
      (mapBody T.toContinuousLinearMap (L 2))
    let P : Fin 3 → Submodule ℝ (Space 3) :=
      ![sectionPlane H W hdW, sectionPlane (linearHull (L 1)) W hdW,
        sectionPlane (linearHull (L 2)) W hdW]
    have hBW : (L 1 : Set (Space (3 + k))) ⊆ W :=
      fun _ hx => (le_sup_left : linearHull (L 1) ≤ W) (mem_linearHull hx)
    have hCW : (L 2 : Set (Space (3 + k))) ⊆ W :=
      fun _ hx => (le_sup_right : linearHull (L 2) ≤ W) (mem_linearHull hx)
    have hBembed : mapBody T.toContinuousLinearMap (L 1) = embedBody B :=
      frame_body_in_threeSpace W U hWU hdW hdU (L 1) hBW
    have hCembed : mapBody T.toContinuousLinearMap (L 2) = embedBody C :=
      frame_body_in_threeSpace W U hWU hdW hdU (L 2) hCW
    refine ⟨⟨F, B, C, LinearFrame.volumeFactor T, ?_, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact_mod_cast LinearFrame.volumeFactor_pos T
    · intro i
      fin_cases i
      · exact sectionPlane_finrank H W hdW hdE
      · exact sectionPlane_finrank_of_le (linearHull (L 1)) W le_sup_left hdW hdB
      · exact sectionPlane_finrank_of_le (linearHull (L 2)) W le_sup_right hdW hdC
    · have h01 : P 0 ⊔ P 1 = ⊤ := by
        first
        | apply sectionPlane_sup_eq_top H (linearHull (L 1)) W le_sup_left _ hdW
          change W ≤ linearHull (L 0) ⊔ linearHull (L 1)
          rw [hHB]
          exact le_top
      have h02 : P 0 ⊔ P 2 = ⊤ := by
        first
        | apply sectionPlane_sup_eq_top H (linearHull (L 2)) W le_sup_right _ hdW
          change W ≤ linearHull (L 0) ⊔ linearHull (L 2)
          rw [hHC]
          exact le_top
      have h12 : P 1 ⊔ P 2 = ⊤ :=
        sectionPlane_sup_eq_top (linearHull (L 1)) (linearHull (L 2)) W le_sup_right le_rfl hdW
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | exact h01 | exact h02 | exact h12 |
        exact (sup_comm _ _).trans h01 | exact (sup_comm _ _).trans h02 |
        exact (sup_comm _ _).trans h12
    · intro y
      exact frame_fiber_subset_plane H W U hWU hUH hdW hdU (L 0)
        (fun _ hx => mem_linearHull hx) y
    · exact coordinate_body_in_plane (linearHull (L 1)) W U le_sup_left hWU hdW hdU
        (L 1) (fun _ hx => mem_linearHull hx)
    · exact coordinate_body_in_plane (linearHull (L 2)) W U le_sup_right hWU hdW hdU
        (L 2) (fun _ hx => mem_linearHull hx)
    · apply threeFrame_projection_positive W U hWU hdW hdU (L 0) (L 1) (h0 0) hBW
      rw [linearHull_add (h0 0) (h0 1)]
      exact hHB
    · intro t ht
      have hsum : mapBody T.toContinuousLinearMap (weightedSum L t) =
          t 0 • F + embedBody (t 1 • B + t 2 • C) := by
        first
        | simp only [weightedSum, Fin.sum_univ_three, mapBody_add, mapBody_smul,
            hBembed, hCembed, embedBody, mapBody_add, mapBody_smul]
          exact add_assoc _ _ _
      have hv := LinearFrame.realVolume_eq_factor_mul_image T
        (weightedSum L t : Set (Space (3 + k)))
      have heq : volume.real (T '' (weightedSum L t : Set (Space (3 + k)))) =
          volume.real ((t 0 • F + embedBody (U := Space k) (t 1 • B + t 2 • C) :
            ConvexBody (Space 3 × Space k)) : Set (Space 3 × Space k)) := by
        first
        | exact congrArg (fun S : ConvexBody (Space 3 × Space k) =>
            volume.real (S : Set (Space 3 × Space k))) hsum
      rw [heq] at hv
      exact hv.symm.trans (hL t ht).symm

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HigherLiftFiberFrame.lean -/

/- BEGIN SOURCE: VolumePolynomials/CommonLineTransversality.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # The common-line obstruction, including averaged fibers in dimension zero

All six repeated coefficients are derived from the actual volume identity.
The two quantities contributed by the first body are its integrated planar
fiber area and its integrated transverse width. Each pair's positive Haar
factor occurs on both sides of the cyclic product, so the prescribed slice
with `0 < s < 1` cannot have a common line in its three planes.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.CommonLineCoordinates

open CommonLineVolume

def nextPlane : Fin 3 → Fin 3 := ![1, 2, 0]

theorem nextPlane_ne (i : Fin 3) : i ≠ nextPlane i := by
  first
  | fin_cases i <;> decide

def firstTwo : ProductThree →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ Plane).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane))

def Data.coordinate {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3) : Space 3 →L[ℝ] Plane :=
  firstTwo.comp (L.pairFrame (by simp [Space]) hP hp i (nextPlane i)
    (nextPlane_ne i)).toContinuousLinearMap

theorem Data.coordinate_planeMap {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3) (p : Plane) :
    L.coordinate hP hp i (L.planeMap i p) = p := by
  first
  | change firstTwo (L.pairFrame (by simp [Space]) hP hp i (nextPlane i)
      (nextPlane_ne i) (L.planeMap i p)) = p
    rw [L.pairFrame_left]
    rfl

theorem Data.planeMap_coordinate {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3)
    {x : Space 3} (hx : x ∈ P i) :
    L.planeMap i (L.coordinate hP hp i x) = x := by
  first
  | change x ∈ (P i : Set (Space 3)) at hx
    rw [← L.range_planeMap i] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [L.coordinate_planeMap]

theorem Data.body_reconstruction {P : Fin 3 → Submodule ℝ (Space 3)}
    (L : Data P) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hp : ∀ i j, i ≠ j → P i ⊔ P j = ⊤) (i : Fin 3)
    (K : Body 3) (hK : (K : Set (Space 3)) ⊆ P i) :
    mapBody (L.planeMap i) (mapBody (L.coordinate hP hp i) K) = K := by
  first
  | apply ConvexBody.ext
    change L.planeMap i '' (L.coordinate hP hp i '' (K : Set (Space 3))) = _
    rw [Set.image_image]
    calc
      _ = id '' (K : Set (Space 3)) :=
        Set.image_congr (fun x hx => L.planeMap_coordinate hP hp i (hK hx))
      _ = _ := Set.image_id' _

end VolumePolynomials.CommonLineCoordinates

namespace VolumePolynomials.HigherLift

open CommonLineVolume ConvexFibers FiberVolume

theorem FiberFrameData.integral_volume {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    D.J * (∫ y in projection D.F, fiberSumVolume D.F D.B D.C b c y) =
      CubicSlice.value (correction k * α) s z ![1, b, c] := by
  first
  | have h := D.volume_identity ![1, b, c] (by
      intro i
      fin_cases i
      · norm_num
      · exact hb
      · exact hc)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, evaluate_coefficients,
      one_pow, one_smul, one_mul] at h
    have hf := realVolume_scaled_sum_of_pos D.F (b • D.B + c • D.C)
      (t := 1) (by norm_num)
    simp only [one_smul, one_pow, one_mul] at hf
    rw [hf] at h
    simpa only [fiberSumVolume, ConvexBody.coe_add, ConvexBody.coe_smul,
      add_assoc] using h

theorem FiberFrameData.pure_pair_coefficients {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) :
    D.J * volume.real (projection D.F) * (3 * mixedVolume3 volume D.B D.B D.C) = 3 ∧
    D.J * volume.real (projection D.F) * (3 * mixedVolume3 volume D.C D.C D.B) = 3 := by
  first
  | have hnonneg (i : Fin 6) : 0 ≤ (differenceGrid i).1 ∧ 0 ≤ (differenceGrid i).2 := by
      first
      | fin_cases i <;> norm_num [differenceGrid]
    have hnum : (∑ i : Fin 6, differenceWeight i *
        CubicSlice.value (correction k * α) s z
          ![1, (differenceGrid i).1, (differenceGrid i).2]) = 6 := by
      first
      | simp only [Fin.sum_univ_succ, differenceWeight, differenceGrid,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_zero, CubicSlice.value]
        ring
    have hnum' : (∑ i : Fin 6, differenceWeight i *
        CubicSlice.value (correction k * α) s z
          ![1, (differenceGrid i).2, (differenceGrid i).1]) = 6 := by
      first
      | simp only [Fin.sum_univ_succ, differenceWeight, differenceGrid,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_zero, CubicSlice.value]
        ring
    have hBC := integral_third_difference D.F D.B D.C D.J
    have hCB := integral_third_difference D.F D.C D.B D.J
    have hval (i : Fin 6) := D.integral_volume (hnonneg i).1 (hnonneg i).2
    simp_rw [hval] at hBC
    rw [hnum] at hBC
    have hval' (i : Fin 6) :
        D.J * (∫ y in projection D.F,
          fiberSumVolume D.F D.C D.B (differenceGrid i).1 (differenceGrid i).2 y) =
        CubicSlice.value (correction k * α) s z
          ![1, (differenceGrid i).2, (differenceGrid i).1] := by
      first
      | have h := D.integral_volume (hnonneg i).2 (hnonneg i).1
        convert h using 1
        congr 1
        apply setIntegral_congr_fun (projection_compact D.F).measurableSet
        intro y _
        unfold fiberSumVolume
        congr 1
        ac_rfl
    simp_rw [hval'] at hCB
    rw [hnum'] at hCB
    constructor <;> nlinarith

theorem FiberFrameData.transverse {k : ℕ} {α s z : ℝ}
    (D : FiberFrameData k α s z) (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1) :
    D.P 0 ⊓ D.P 1 ⊓ D.P 2 = ⊥ := by
  first
  | by_contra hcommon
    obtain ⟨L⟩ := CommonLineCoordinates.exists_data D.P D.planes hcommon
    let f (i : Fin 3) := L.planeMap i
    let c (i : Fin 3) := L.coordinate D.planes D.pair_spans i
    let A := mapTotal (c 0) D.F
    let B := mapBody (c 1) D.B
    let C := mapBody (c 2) D.C
    let T01 := L.pairFrame (by simp [Space]) D.planes D.pair_spans 0 1 (by decide)
    let T02 := L.pairFrame (by simp [Space]) D.planes D.pair_spans 0 2 (by decide)
    let T12 := L.pairFrame (by simp [Space]) D.planes D.pair_spans 1 2 (by decide)
    let j01 : ℝ := LinearFrame.volumeFactor T01
    let j02 : ℝ := LinearFrame.volumeFactor T02
    let j12 : ℝ := LinearFrame.volumeFactor T12
    let a : ℝ := ∫ y in projection A, area (fiberBody A y)
    let w : ℝ := ∫ y in projection A, width (fiberBody A y)
    let M : ℝ := volume.real (projection A)
    let β : ℝ := correction k * α
    have hβ : 0 < β := by
      first
      | apply mul_pos _ hα
        unfold correction
        positivity
    have hproj : projection A = projection D.F := projection_mapTotal (c 0) D.F
    have hA (y : Space k) (hy : y ∈ projection D.F) :
        mapBody (f 0) (fiberBody A y) = fiberBody D.F y := by
      first
      | rw [show fiberBody A y = mapBody (c 0) (fiberBody D.F y) from
          (map_fiberBody (c 0) D.F hy).symm]
        apply L.body_reconstruction D.planes D.pair_spans 0
        rw [coe_fiberBody D.F hy]
        exact D.fibers_in_plane y
    have hB : mapBody (f 1) B = D.B :=
      L.body_reconstruction D.planes D.pair_spans 1 D.B D.B_in_plane
    have hC : mapBody (f 2) C = D.C :=
      L.body_reconstruction D.planes D.pair_spans 2 D.C D.C_in_plane
    have h01l (p : Plane) : T01 (f 0 p) = CrossPlaneVolume.firstPlane p :=
      L.pairFrame_left (by simp [Space]) D.planes D.pair_spans 0 1 (by decide) p
    have h01r (p : Plane) : T01 (f 1 p) = CrossPlaneVolume.secondPlane p :=
      L.pairFrame_right (by simp [Space]) D.planes D.pair_spans 0 1 (by decide) p
    have h02l (p : Plane) : T02 (f 0 p) = CrossPlaneVolume.firstPlane p :=
      L.pairFrame_left (by simp [Space]) D.planes D.pair_spans 0 2 (by decide) p
    have h02r (p : Plane) : T02 (f 2 p) = CrossPlaneVolume.secondPlane p :=
      L.pairFrame_right (by simp [Space]) D.planes D.pair_spans 0 2 (by decide) p
    have h12l (p : Plane) : T12 (f 1 p) = CrossPlaneVolume.firstPlane p :=
      L.pairFrame_left (by simp [Space]) D.planes D.pair_spans 1 2 (by decide) p
    have h12r (p : Plane) : T12 (f 2 p) = CrossPlaneVolume.secondPlane p :=
      L.pairFrame_right (by simp [Space]) D.planes D.pair_spans 1 2 (by decide) p
    have hAB (r : ℝ) (hr : 0 ≤ r) :
        D.J * j01 * (a * width B * r + w * area B * r ^ 2) = 3 * β * r + 3 * r ^ 2 := by
      first
      | have hv := D.integral_volume hr (show (0 : ℝ) ≤ 0 by rfl)
        have heq : (∫ y in projection D.F, fiberSumVolume D.F D.B D.C r 0 y) =
            ∫ y in projection A,
              volume.real (mapBody (f 0) (fiberBody A y) + r • mapBody (f 1) B : Set (Space 3)) := by
          rw [hproj]
          apply setIntegral_congr_fun (projection_compact D.F).measurableSet
          intro y hy
          dsimp only
          rw [hA y hy, hB]
          change volume.real ((fiberBody D.F y + r • D.B + (0 : ℝ) • D.C : Body 3) :
            Set (Space 3)) =
            volume.real ((fiberBody D.F y + r • D.B : Body 3) : Set (Space 3))
          rw [body_zero_smul, add_zero]
        rw [heq, integral_pair_volume T01 (f 0) (f 1) h01l h01r A B hr] at hv
        change D.J * (j01 * (a * width B * r + w * area B * r ^ 2)) =
          CubicSlice.value β s z ![1, r, 0] at hv
        simpa [CubicSlice.value, mul_assoc] using hv
    have hAC (r : ℝ) (hr : 0 ≤ r) :
        D.J * j02 * (a * width C * r + w * area C * r ^ 2) = 3 * β * r + 3 * s * r ^ 2 := by
      first
      | have hv := D.integral_volume (show (0 : ℝ) ≤ 0 by rfl) hr
        have heq : (∫ y in projection D.F, fiberSumVolume D.F D.B D.C 0 r y) =
            ∫ y in projection A,
              volume.real (mapBody (f 0) (fiberBody A y) + r • mapBody (f 2) C : Set (Space 3)) := by
          rw [hproj]
          apply setIntegral_congr_fun (projection_compact D.F).measurableSet
          intro y hy
          dsimp only
          rw [hA y hy, hC]
          change volume.real ((fiberBody D.F y + (0 : ℝ) • D.B + r • D.C : Body 3) :
            Set (Space 3)) =
            volume.real ((fiberBody D.F y + r • D.C : Body 3) : Set (Space 3))
          rw [body_zero_smul, add_zero]
        rw [heq, integral_pair_volume T02 (f 0) (f 2) h02l h02r A C hr] at hv
        change D.J * (j02 * (a * width C * r + w * area C * r ^ 2)) =
          CubicSlice.value β s z ![1, 0, r] at hv
        simpa [CubicSlice.value, mul_assoc] using hv
    have hab1 := hAB 1 (by norm_num)
    have hab2 := hAB 2 (by norm_num)
    have hac1 := hAC 1 (by norm_num)
    have hac2 := hAC 2 (by norm_num)
    have hAAB : D.J * j01 * a * width B = 3 * β := by nlinarith
    have hABB : D.J * j01 * w * area B = 3 := by nlinarith
    have hAAC : D.J * j02 * a * width C = 3 * β := by nlinarith
    have hACC : D.J * j02 * w * area C = 3 * s := by nlinarith
    have hp := pair_repeated_coefficients T12 (f 1) (f 2) h12l h12r B C
    have hm := D.pure_pair_coefficients
    rw [← hB, ← hC] at hm
    have hBBC : D.J * M * j12 * area B * width C = 3 := by
      first
      | have h := hm.1
        rw [hp.1] at h
        simpa only [M, hproj, j12, mul_assoc] using h
    have hBCC : D.J * M * j12 * width B * area C = 3 := by
      first
      | have h := hm.2
        rw [hp.2] at h
        simpa only [M, hproj, j12, mul_assoc] using h
    have hcyclic :
        (D.J * j01 * a * width B) * (D.J * M * j12 * area B * width C) *
          (D.J * j02 * w * area C) =
        (D.J * j02 * a * width C) * (D.J * j01 * w * area B) *
          (D.J * M * j12 * width B * area C) := by ring
    rw [hAAB, hBBC, hACC, hAAC, hABB, hBCC] at hcyclic
    have hprod : (27 * β) * (s - 1) = 0 := by nlinarith [hcyclic]
    have hsEq : s - 1 = 0 := (mul_eq_zero.mp hprod).resolve_left (by positivity)
    linarith

end VolumePolynomials.HigherLift
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CommonLineTransversality.lean -/

/- BEGIN SOURCE: VolumePolynomials/MinkowskiFunctional.lean -/
section



@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Continuous monotone Minkowski functionals

Support values and directional widths are examples. The construction of
Minkowski averages will preserve all such functionals simultaneously.
-/

open Set Metric MeasureTheory
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Blaschke compactness for bodies in a fixed compact set, with no
requirement that the individual bodies contain the origin. -/
theorem isCompact_bodies_subset_compact {C : Set E} (hC : IsCompact C) :
    IsCompact {K : ConvexBody E | (K : Set E) ⊆ C} := by
  first
  | have hr : IsClosed (Set.range (bodyToNonemptyCompacts (E := E))) := by
      first
      | rw [range_bodyToNonemptyCompacts]
        exact isClosed_compacts_convex
    have hbase := TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hC
    have hc : IsCompact {K : TopologicalSpace.NonemptyCompacts E |
        (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)} :=
      hbase.inter_right isClosed_compacts_convex
    have h := isometry_bodyToNonemptyCompacts.isUniformInducing.isInducing.isCompact_preimage hr hc
    convert h using 1
    ext K
    simp only [mem_ofPred_eq, mem_preimage, coe_bodyToNonemptyCompacts]
    exact ⟨fun hK => ⟨hK, K.convex⟩, fun hK => hK.1⟩

namespace BodySupport

theorem continuous_support (f : E →L[ℝ] ℝ) :
    Continuous (fun K : ConvexBody E => support K f) := by
  first
  | apply LipschitzWith.continuous (K := ‖f‖₊)
    apply LipschitzWith.of_dist_le_mul
    intro K L
    have hKL := support_le_add_norm_mul_dist K L f
    have hLK := support_le_add_norm_mul_dist L K f
    rw [dist_comm L K] at hLK
    rw [Real.dist_eq, coe_nnnorm, abs_le]
    constructor <;> linarith

theorem support_add (K L : ConvexBody E) (f : E →L[ℝ] ℝ) :
    support (K + L) f = support K f + support L f := by
  first
  | apply le_antisymm
    · apply support_le
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [map_add]
      exact add_le_add (le_support K f hx) (le_support L f hy)
    · obtain ⟨x, hx, hfx⟩ := exists_support K f
      obtain ⟨y, hy, hfy⟩ := exists_support L f
      simpa only [map_add, hfx, hfy] using
        le_support (K + L) f (Set.add_mem_add hx hy)

theorem support_smul (K : ConvexBody E) (f : E →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) : support (r • K) f = r * support K f := by
  first
  | apply le_antisymm
    · apply support_le
      rintro _ ⟨x, hx, rfl⟩
      simp only [map_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (le_support K f hx) hr
    · obtain ⟨x, hx, hfx⟩ := exists_support K f
      simpa only [map_smul, smul_eq_mul, hfx] using
        le_support (r • K) f (smul_mem_smul_set hx)

theorem support_mono {K L : ConvexBody E} (h : (K : Set E) ⊆ L)
    (f : E →L[ℝ] ℝ) : support K f ≤ support L f :=
  support_le K f (fun _ hx => le_support L f (h hx))

end BodySupport

structure MinkowskiFunctional (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ConvexBody E → ℝ
  continuous_toFun : Continuous toFun
  monotone : ∀ {K L : ConvexBody E}, (K : Set E) ⊆ L → toFun K ≤ toFun L
  map_add : ∀ K L, toFun (K + L) = toFun K + toFun L
  map_nonneg_smul : ∀ r : ℝ, 0 ≤ r → ∀ K, toFun (r • K) = r * toFun K

instance : CoeFun (MinkowskiFunctional E) (fun _ => ConvexBody E → ℝ) :=
  ⟨MinkowskiFunctional.toFun⟩

namespace MinkowskiFunctional

def support (f : E →L[ℝ] ℝ) : MinkowskiFunctional E where
  toFun K := BodySupport.support K f
  continuous_toFun := BodySupport.continuous_support f
  monotone h := BodySupport.support_mono h f
  map_add K L := BodySupport.support_add K L f
  map_nonneg_smul _ hr K := BodySupport.support_smul K f hr

def add (f g : MinkowskiFunctional E) : MinkowskiFunctional E where
  toFun K := f K + g K
  continuous_toFun := f.continuous_toFun.add g.continuous_toFun
  monotone h := add_le_add (f.monotone h) (g.monotone h)
  map_add K L := by rw [f.map_add, g.map_add]; ring
  map_nonneg_smul r hr K := by rw [f.map_nonneg_smul r hr, g.map_nonneg_smul r hr]; ring

def width (f : E →L[ℝ] ℝ) : MinkowskiFunctional E := add (support f) (support (-f))

theorem map_convex_combination (φ : MinkowskiFunctional E)
    (K L : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    φ (a • K + b • L) = a * φ K + b * φ L := by
  first
  | rw [φ.map_add, φ.map_nonneg_smul a ha, φ.map_nonneg_smul b hb]

/-- Equality of all monotone Minkowski functionals implies equality of the
actual bodies, because support values are among the functionals. -/
theorem separating {K L : ConvexBody E} (h : ∀ φ : MinkowskiFunctional E, φ K = φ L) :
    K = L := by
  first
  | apply SetLike.coe_injective
    ext x
    change x ∈ K ↔ x ∈ L
    rw [BodySupport.mem_iff_le_support K, BodySupport.mem_iff_le_support L]
    have hs : ∀ f : E →L[ℝ] ℝ, BodySupport.support K f = BodySupport.support L f :=
      fun f => h (support f)
    simp only [hs]

end MinkowskiFunctional

/-- Concavity of a body-valued family means literal set containment. -/
theorem FiberConcave.functional_concave {U : Type*} [AddCommMonoid U] [Module ℝ U]
    {Z : Set U} {K : U → ConvexBody E} (hK : FiberConcave Z K)
    (φ : MinkowskiFunctional E) : ConcaveOn ℝ Z (fun y => φ (K y)) := by
  first
  | refine ⟨hK.1, ?_⟩
    intro x hx y hy a b ha hb hab
    rw [smul_eq_mul, smul_eq_mul, ← φ.map_convex_combination _ _ ha hb]
    exact φ.monotone (hK.2 x hx y hy a b ha hb hab)

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MinkowskiFunctional.lean -/

/- BEGIN SOURCE: VolumePolynomials/PowerLayerCake.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The real power layer-cake identity for arbitrary finite measures. -/

open Set MeasureTheory Filter

namespace VolumePolynomials.BerwaldMoments

section LayerCake

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- A real-valued power version of layer cake on a finite measure space. -/
theorem power_layer_cake {f : α → ℝ} (hf : AEMeasurable f μ)
    (hn : 0 ≤ᵐ[μ] f) (p : ℕ) :
    (∫ x, f x ^ (p + 1) ∂μ) =
      (p + 1 : ℝ) * ∫ t in Ioi 0, t ^ p * μ.real {x | t ≤ f x} := by
  first
  | have hg : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ t ^ p := by
      first
      | filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact pow_nonneg ht.le p
    have h := lintegral_comp_eq_lintegral_meas_le_mul (g := fun t : ℝ => t ^ p) μ hn hf
      (fun t _ => (continuous_id.pow p).intervalIntegrable 0 t) hg
    have hint (x : α) : (∫ t in 0..f x, t ^ p) =
        f x ^ (p + 1) / (p + 1 : ℝ) := by
      first
      | rw [integral_pow]
        simp
    simp only [hint] at h
    have htail : Measurable (fun t : ℝ => μ {x | t ≤ f x}) :=
      Antitone.measurable (fun _ _ hst => measure_mono (fun _ hx => hst.trans hx))
    have hrhs : AEStronglyMeasurable
        (fun t : ℝ => t ^ p * μ.real {x | t ≤ f x}) (volume.restrict (Ioi 0)) :=
      ((measurable_id.pow_const p).mul htail.ennreal_toReal).aestronglyMeasurable
    have hrhsn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        (fun t : ℝ => t ^ p * μ.real {x | t ≤ f x}) := by
      first
      | filter_upwards [hg] with t ht
        exact mul_nonneg ht measureReal_nonneg
    have hlhsn : 0 ≤ᵐ[μ] (fun x => f x ^ (p + 1) / (p + 1 : ℝ)) := by
      first
      | filter_upwards [hn] with x hx
        exact div_nonneg (pow_nonneg hx _) (by positivity)
    have hlin : (∫ t in Ioi 0, t ^ p * μ.real {x | t ≤ f x}) =
        ENNReal.toReal (∫⁻ t in Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (t ^ p)) := by
      first
      | rw [integral_eq_lintegral_of_nonneg_ae hrhsn hrhs]
        congr 1
        apply lintegral_congr_ae
        filter_upwards [hg] with t ht
        rw [ENNReal.ofReal_mul ht, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ _), mul_comm]
    have hreal : (∫ x, f x ^ (p + 1) / (p + 1 : ℝ) ∂μ) =
        ∫ t in Ioi 0, t ^ p * μ.real {x | t ≤ f x} := by
      first
      | rw [integral_eq_lintegral_of_nonneg_ae hlhsn
          ((hf.pow_const (p + 1)).div_const _).aestronglyMeasurable, h, hlin]
    rw [integral_div] at hreal
    have hp : (p + 1 : ℝ) ≠ 0 := by positivity
    exact (div_eq_iff hp).mp hreal |>.trans (mul_comm _ _)

end LayerCake

end VolumePolynomials.BerwaldMoments
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PowerLayerCake.lean -/

/- BEGIN SOURCE: VolumePolynomials/BerwaldComparison.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The one-crossing comparison in the sharp second-moment inequality

This file proves the scalar comparison used in the level-set proof of
Berwald's inequality. The geometric superlevel-set concavity and layer-cake
identifications must be proved separately before applying these lemmas to
fibers of convex bodies.
-/

open Set MeasureTheory Filter

namespace VolumePolynomials.BerwaldComparison

/-- If a function can change sign only from positive to negative, a crossing
point makes its product with the centered coordinate nonpositive everywhere. -/
theorem exists_crossing_point {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℝ)
    (hcross : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y → g x < 0 → g y ≤ 0) :
    ∃ τ ∈ Icc 0 a, ∀ t ∈ Icc 0 a, (t - τ) * g t ≤ 0 := by
  first
  | classical
    let S : Set ℝ := {t | t ∈ Icc 0 a ∧ 0 < g t}
    by_cases hS : S.Nonempty
    · have hbounded : BddAbove S := ⟨a, fun t ht => ht.1.2⟩
      have hτa : sSup S ≤ a := csSup_le hS (fun t ht => ht.1.2)
      obtain ⟨t₀, ht₀⟩ := hS
      have hτ0 : 0 ≤ sSup S := ht₀.1.1.trans (le_csSup hbounded ht₀)
      refine ⟨sSup S, ⟨hτ0, hτa⟩, ?_⟩
      intro t ht
      rcases lt_trichotomy t (sSup S) with hlt | heq | hgt
      · have hgt0 : 0 ≤ g t := by
          first
          | by_contra h
            obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup ⟨t₀, ht₀⟩ hlt
            exact (not_lt_of_ge (hcross t ht u hu.1 htu (lt_of_not_ge h))) hu.2
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlt.le) hgt0
      · simp only [heq, sub_self, zero_mul, le_refl]
      · have hgt0 : g t ≤ 0 := by
          first
          | by_contra h
            have hm : t ∈ S := ⟨ht, lt_of_not_ge h⟩
            exact (not_le_of_gt hgt) (le_csSup hbounded hm)
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hgt.le) hgt0
    · refine ⟨0, ⟨le_rfl, ha⟩, ?_⟩
      intro t ht
      have hg : g t ≤ 0 := by
        first
        | by_contra h
          exact hS ⟨t, ht, lt_of_not_ge h⟩
      simpa only [sub_zero] using mul_nonpos_of_nonneg_of_nonpos ht.1 hg

theorem first_moment_nonpos {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Icc 0 a))
    (hxg : IntegrableOn (fun t => t * g t) (Icc 0 a))
    (hzero : (∫ t in Icc 0 a, g t) = 0)
    (hcross : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y → g x < 0 → g y ≤ 0) :
    (∫ t in Icc 0 a, t * g t) ≤ 0 := by
  first
  | obtain ⟨τ, _, hτ⟩ := exists_crossing_point ha g hcross
    have hnonpos : (∫ t in Icc 0 a, (t - τ) * g t) ≤ 0 :=
      integral_nonpos_of_ae ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hτ t ht)
    have heq : (∫ t in Icc 0 a, (t - τ) * g t) = ∫ t in Icc 0 a, t * g t := by
      first
      | calc
          (∫ t in Icc 0 a, (t - τ) * g t) =
              ∫ t in Icc 0 a, t * g t - τ * g t := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun t => by ring)
          _ = (∫ t in Icc 0 a, t * g t) - τ * ∫ t in Icc 0 a, g t := by
            rw [integral_sub hxg (hg.const_mul τ), integral_const_mul]
          _ = ∫ t in Icc 0 a, t * g t := by rw [hzero, mul_zero, sub_zero]
    rwa [heq] at hnonpos

/-- Equal masses and one crossing imply the required comparison of first
moments of the survival functions. -/
theorem first_moment_le {a : ℝ} (ha : 0 ≤ a) (v w : ℝ → ℝ)
    (hv : IntegrableOn v (Icc 0 a)) (hw : IntegrableOn w (Icc 0 a))
    (hxv : IntegrableOn (fun t => t * v t) (Icc 0 a))
    (hxw : IntegrableOn (fun t => t * w t) (Icc 0 a))
    (hmass : (∫ t in Icc 0 a, v t) = ∫ t in Icc 0 a, w t)
    (hcross : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y → v x < w x → v y ≤ w y) :
    (∫ t in Icc 0 a, t * v t) ≤ ∫ t in Icc 0 a, t * w t := by
  first
  | have hg : IntegrableOn (fun t => v t - w t) (Icc 0 a) := hv.sub hw
    have hxg : IntegrableOn (fun t => t * (v t - w t)) (Icc 0 a) := by
      first
      | convert hxv.sub hxw using 1
        ext t
        simp only [Pi.sub_apply]
        ring
    have hzero : (∫ t in Icc 0 a, v t - w t) = 0 := by
      first
      | rw [integral_sub hv hw, hmass, sub_self]
    have hn := first_moment_nonpos ha (fun t => v t - w t) hg hxg hzero
      (fun x hx y hy hxy h => sub_nonpos.mpr (hcross x hx y hy hxy (sub_neg.mp h)))
    have heq : (∫ t in Icc 0 a, t * (v t - w t)) =
        (∫ t in Icc 0 a, t * v t) - ∫ t in Icc 0 a, t * w t := by
      first
      | simp_rw [mul_sub]
        exact integral_sub hxv hxw
    rw [heq] at hn
    exact sub_nonpos.mp hn

/-- The reference survival function has exactly the mass required in the
Berwald comparison. -/
theorem reference_integral (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Icc 0 a, (1 - t / a) ^ k) = a / (k + 1) := by
  first
  | rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le]
    have h := intervalIntegral.integral_comp_sub_div (fun u : ℝ => u ^ k) ha.ne' 1
      (a := (0 : ℝ)) (b := a)
    rw [div_self ha.ne', sub_self, zero_div, sub_zero,
      integral_pow] at h
    simpa only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero,
      smul_eq_mul, mul_one_div] using h

/-- The first moment of the reference survival function gives the sharp
constant `2*(k+1)/(k+2)` after layer-cake integration. -/
theorem reference_first_moment (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Icc 0 a, t * (1 - t / a) ^ k) =
      a ^ 2 / ((k + 1) * (k + 2)) := by
  first
  | have hidentity (t : ℝ) : t * (1 - t / a) ^ k =
        a * ((1 - t / a) ^ k - (1 - t / a) ^ (k + 1)) := by
      first
      | rw [pow_succ]
        field_simp
        ring
    have hk : IntegrableOn (fun t : ℝ => (1 - t / a) ^ k) (Icc 0 a) :=
      ((continuous_const.sub (continuous_id.div_const a)).pow k).integrableOn_Icc
    have hk1 : IntegrableOn (fun t : ℝ => (1 - t / a) ^ (k + 1)) (Icc 0 a) :=
      ((continuous_const.sub (continuous_id.div_const a)).pow (k + 1)).integrableOn_Icc
    simp_rw [hidentity]
    rw [integral_const_mul, integral_sub hk hk1,
      reference_integral k ha, reference_integral (k + 1) ha]
    push_cast
    field_simp
    ring

/-- A concave graph starting at height one can cross an affine graph
starting at the same point only once, from above to below. -/
theorem concave_below_line_persists {M a : ℝ} {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Ico 0 M) u) (hM : 0 < M) (hu0 : u 0 = 1)
    {x y : ℝ} (hx : x ∈ Ico 0 M) (hy : y ∈ Ico 0 M)
    (hxy : x < y) (hux : u x < 1 - x / a) : u y < 1 - y / a := by
  first
  | have hxpos : 0 < x := by
      first
      | by_contra h
        have hx0 : x = 0 := le_antisymm (le_of_not_gt h) hx.1
        simpa only [hx0, hu0, zero_div, sub_zero, lt_self_iff_false] using hux
    have hypos : 0 < y := hxpos.trans hxy
    have hweight : 0 ≤ 1 - x / y :=
      sub_nonneg.mpr ((div_le_one hypos).mpr hxy.le)
    have hpoint : (1 - x / y) * 0 + (x / y) * y = x := by
      first
      | rw [mul_zero, zero_add, div_mul_cancel₀ x hypos.ne']
    have hconc : 1 - x / y + x / y * u y ≤ u x := by
      first
      | simpa only [smul_eq_mul, hu0, mul_one, hpoint] using
          hu.2 (show (0 : ℝ) ∈ Ico 0 M from ⟨le_rfl, hM⟩) hy
            hweight (div_nonneg hx.1 hypos.le) (by ring : (1 - x / y) + x / y = 1)
    have hscaled := mul_le_mul_of_nonneg_left hconc hypos.le
    have hidentity : y * (1 - x / y + x / y * u y) = y - x + x * u y := by
      first
      | field_simp [hypos.ne'] <;> ring
    rw [hidentity] at hscaled
    have hsmall := mul_lt_mul_of_pos_left hux hypos
    have hprod : x * u y < x * (1 - y / a) := by
      first
      | calc
          x * u y ≤ y * u x - y + x := by linarith
          _ < y * (1 - x / a) - y + x := by linarith
          _ = x * (1 - y / a) := by ring
    by_contra h
    exact (not_le_of_gt hprod)
      (mul_le_mul_of_nonneg_left (le_of_not_gt h) hxpos.le)

/-- The dimension-root concavity of a survival function implies the exact
one-crossing condition for the polynomial reference survival function. -/
theorem root_concavity_one_crossing {k : ℕ} (hk : 0 < k)
    {M a : ℝ} (hM : 0 < M) (ha : 0 < a)
    (u v : ℝ → ℝ) (hu : ConcaveOn ℝ (Ico 0 M) u) (hu0 : u 0 = 1)
    (hunonneg : ∀ t ∈ Ico 0 M, 0 ≤ u t)
    (hv : ∀ t ∈ Ico 0 M, v t = (u t) ^ k)
    (hvzero : ∀ t, M ≤ t → v t = 0) :
    ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y →
      v x < (1 - x / a) ^ k → v y ≤ (1 - y / a) ^ k := by
  first
  | intro x hx y hy hxy hsmall
    have hbase (t : ℝ) (ht : t ∈ Icc 0 a) : 0 ≤ 1 - t / a :=
      sub_nonneg.mpr ((div_le_one ha).mpr ht.2)
    by_cases hyM : M ≤ y
    · rw [hvzero y hyM]
      exact pow_nonneg (hbase y hy) k
    · have hy' : y ∈ Ico 0 M := ⟨hy.1, lt_of_not_ge hyM⟩
      have hx' : x ∈ Ico 0 M := ⟨hx.1, hxy.trans hy'.2⟩
      rw [hv x hx'] at hsmall
      have hxroot : u x < 1 - x / a :=
        (pow_lt_pow_iff_left₀ (hunonneg x hx') (hbase x hx) hk.ne').mp hsmall
      have hyroot := concave_below_line_persists hu hM hu0 hx' hy' hxy hxroot
      rw [hv y hy']
      exact pow_le_pow_left₀ (hunonneg y hy') hyroot.le k

/-- Concavity and nonnegativity force the chord joining `(0,1)` to the
limiting endpoint `(M,0)` to lie below the graph. No endpoint continuity
at `M` is required. -/
theorem concave_reference_lower_bound {M : ℝ} (hM : 0 < M) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Ico 0 M) u) (hu0 : u 0 = 1)
    (hn : ∀ t ∈ Ico 0 M, 0 ≤ u t) {t : ℝ} (ht : t ∈ Ico 0 M) :
    1 - t / M ≤ u t := by
  first
  | have hclosed : IsClosed {b : ℝ | b - t ≤ b * u t} :=
      isClosed_le (continuous_id.sub continuous_const)
        (continuous_id.mul continuous_const)
    have hsubset : Ioo t M ⊆ {b : ℝ | b - t ≤ b * u t} := by
      first
      | intro b hb
        have hb0 : 0 < b := ht.1.trans_lt hb.1
        have hwt : 0 ≤ 1 - t / b :=
          sub_nonneg.mpr ((div_le_one hb0).mpr hb.1.le)
        have hpoint : (1 - t / b) * 0 + (t / b) * b = t := by
          rw [mul_zero, zero_add, div_mul_cancel₀ t hb0.ne']
        have hc := hu.2 (show (0 : ℝ) ∈ Ico 0 M from ⟨le_rfl, hM⟩)
          (show b ∈ Ico 0 M from ⟨hb0.le, hb.2⟩) hwt
          (div_nonneg ht.1 hb0.le) (by ring : 1 - t / b + t / b = 1)
        simp only [smul_eq_mul, hu0, mul_one, hpoint] at hc
        have hterm : 0 ≤ t / b * u b :=
          mul_nonneg (div_nonneg ht.1 hb0.le) (hn b ⟨hb0.le, hb.2⟩)
        have hlow : 1 - t / b ≤ u t := by linarith
        have hh := mul_le_mul_of_nonneg_left hlow hb0.le
        have hid : b * (1 - t / b) = b - t := by
          field_simp [hb0.ne']
        change b - t ≤ b * u t
        simpa only [hid] using hh
    have hMc : M ∈ closure (Ioo t M) := by
      first
      | rw [closure_Ioo ht.2.ne]
        exact ⟨ht.2.le, le_rfl⟩
    have hlim : M - t ≤ M * u t := closure_minimal hsubset hclosed hMc
    have hid : 1 - t / M = (M - t) / M := by field_simp <;> ring
    rw [hid]
    exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hlim)

/-- The complete scalar comparison, with no assumed upper bound on the
support in terms of its first moment. That bound is a conclusion of
concavity, and fixes the comparison interval. -/
theorem sharp_moment_bound {k : ℕ} (hk : 0 < k) {M : ℝ} (hM : 0 < M)
    (u v : ℝ → ℝ) (hu : ConcaveOn ℝ (Ico 0 M) u) (hu0 : u 0 = 1)
    (hun : ∀ t ∈ Ico 0 M, 0 ≤ u t)
    (hvp : ∀ t ∈ Ico 0 M, v t = u t ^ k)
    (hvz : ∀ t, M ≤ t → v t = 0)
    (hvint : ∀ a : ℝ, 0 ≤ a → IntegrableOn v (Icc 0 a))
    (hxvint : ∀ a : ℝ, 0 ≤ a → IntegrableOn (fun t => t * v t) (Icc 0 a)) :
    2 * (∫ t in Icc 0 M, t * v t) ≤
      (2 * (k + 1 : ℝ) / (k + 2 : ℝ)) * (∫ t in Icc 0 M, v t) ^ 2 := by
  first
  | let m : ℝ := ∫ t in Icc 0 M, v t
    have hk1 : 0 < (k + 1 : ℝ) := by positivity
    have hmasslow : M / (k + 1 : ℝ) ≤ m := by
      first
      | rw [← reference_integral k hM]
        apply integral_mono_ae
          (((continuous_const.sub (continuous_id.div_const M)).pow k).integrableOn_Icc)
          (hvint M hM.le)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        change (1 - t / M) ^ k ≤ v t
        by_cases hlt : t < M
        · rw [hvp t ⟨ht.1, hlt⟩]
          exact pow_le_pow_left₀
            (sub_nonneg.mpr ((div_le_one hM).mpr ht.2))
            (concave_reference_lower_bound hM hu hu0 hun ⟨ht.1, hlt⟩) k
        · have heq : t = M := le_antisymm ht.2 (le_of_not_gt hlt)
          subst t
          simp only [hvz M le_rfl, div_self hM.ne', sub_self, zero_pow hk.ne', le_refl]
    have hm : 0 < m := (div_pos hM hk1).trans_le hmasslow
    let a : ℝ := (k + 1 : ℝ) * m
    have ha : 0 < a := mul_pos hk1 hm
    have hMa : M ≤ a := by
      first
      | exact (div_le_iff₀ hk1).mp hmasslow |>.trans_eq (mul_comm _ _)
    have hvmass : (∫ t in Icc 0 a, v t) = m := by
      first
      | apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Icc
          (Icc_subset_Icc_right hMa)
        exact Eventually.of_forall fun t ht => by
          have hMt : M < t := by
            have ht0 := ht.1.1
            by_contra h
            exact ht.2 ⟨ht0, le_of_not_gt h⟩
          exact hvz t hMt.le
    have hxveq : (∫ t in Icc 0 a, t * v t) = ∫ t in Icc 0 M, t * v t := by
      first
      | apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Icc
          (Icc_subset_Icc_right hMa)
        exact Eventually.of_forall fun t ht => by
          have hMt : M < t := by
            have ht0 := ht.1.1
            by_contra h
            exact ht.2 ⟨ht0, le_of_not_gt h⟩
          rw [hvz t hMt.le, mul_zero]
    have hrefint : IntegrableOn (fun t : ℝ => (1 - t / a) ^ k) (Icc 0 a) :=
      ((continuous_const.sub (continuous_id.div_const a)).pow k).integrableOn_Icc
    have hrefxint : IntegrableOn (fun t : ℝ => t * (1 - t / a) ^ k) (Icc 0 a) :=
      (continuous_id.mul ((continuous_const.sub (continuous_id.div_const a)).pow k)).integrableOn_Icc
    have hmass : (∫ t in Icc 0 a, v t) = ∫ t in Icc 0 a, (1 - t / a) ^ k := by
      first
      | rw [hvmass, reference_integral k ha]
        dsimp only [a]
        field_simp
    have hcmp := first_moment_le ha.le v (fun t => (1 - t / a) ^ k)
      (hvint a ha.le) hrefint (hxvint a ha.le) hrefxint hmass
      (root_concavity_one_crossing hk hM ha u v hu hu0 hun hvp hvz)
    rw [hxveq, reference_first_moment k ha] at hcmp
    have htwice := mul_le_mul_of_nonneg_left hcmp (by norm_num : (0 : ℝ) ≤ 2)
    have hconstant : 2 * (a ^ 2 / ((k + 1 : ℝ) * (k + 2 : ℝ))) =
        (2 * (k + 1 : ℝ) / (k + 2 : ℝ)) * m ^ 2 := by
      first
      | dsimp only [a]
        field_simp <;> ring
    simpa only [hconstant, m] using htwice

end VolumePolynomials.BerwaldComparison
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BerwaldComparison.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/Convex/LogConcave.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: convexity of powers of a nonnegative convex function.

/-!
# Log-concave functions

A function `f : E → ℝ≥0∞` on a real vector space is *log-concave* if
`f x ^ a * f y ^ b ≤ f (a • x + b • y)` whenever `0 ≤ a`, `0 ≤ b` and `a + b = 1`. For a
positive real-valued function this says exactly that its logarithm is concave
(`TauCeti.logConcave_ofReal_exp_iff`), while the value `0` allowed by `ℝ≥0∞` makes the indicator
of a convex set log-concave.

Taking values in `ℝ≥0∞` is what makes the notion stable under integration: the marginal
`x ↦ ∫⁻ y, f (x, y) ∂ν` of a log-concave function is log-concave whenever `ν` satisfies the
Prékopa–Leindler inequality, with no finiteness hypothesis on the integrals
(`TauCeti.LogConcave.lintegral_prod_right`, in
`TauCeti.MeasureTheory.Integral.PrekopaLeindler`). Marginals of this kind are the measures of
the slices of a convex body, and are the objects of Vaaler's cube-slicing theorem.

## Main definitions

* `TauCeti.LogConcave f`: the function `f : E → ℝ≥0∞` is log-concave.

## Main results

* `TauCeti.logConcave_ofReal_exp_iff`: `x ↦ exp (g x)` is log-concave if and only if `g` is
  concave.
* `TauCeti.logConcave_ofReal_exp_neg_mul_sq_norm`: the Gaussian `x ↦ exp (-c ‖x‖ ^ 2)` is
  log-concave.
* `TauCeti.logConcave_indicator_iff`: the indicator of a set at a nonzero value is log-concave if
  and only if the set is convex.
* `TauCeti.LogConcave.convex_support`, `TauCeti.LogConcave.convex_ge`,
  `TauCeti.LogConcave.convex_gt`: the support and the superlevel sets of a log-concave function
  are convex.
* `TauCeti.LogConcave.mul`, `TauCeti.LogConcave.comp_linearMap`: products and linear
  substitutions preserve log-concavity.
* `TauCeti.LogConcave.apply_le_apply_zero`: an even log-concave function is largest at the
  origin.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Definition C.3.1 and Remark C.3.2.

The definition and the convexity statements are adapted from the Apache-2.0 formalization of
Vaaler's theorem in `rwst/Subspace-Theorems` (file `ArithmeticHeights/LogConcave.lean`), by
Ralf Stephan.
-/

public section

open Set
open scoped ENNReal

namespace TauCeti

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- A function `f : E → ℝ≥0∞` on a real vector space is **log-concave** if
`f x ^ a * f y ^ b ≤ f (a • x + b • y)` for all `x`, `y` and all weights `0 ≤ a`, `0 ≤ b` with
`a + b = 1`. For positive real-valued `f` this says that `Real.log ∘ f` is concave. -/
def LogConcave (f : E → ℝ≥0∞) : Prop :=
  ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f x ^ a * f y ^ b ≤ f (a • x + b • y)

theorem logConcave_def {f : E → ℝ≥0∞} :
    LogConcave f ↔ ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f x ^ a * f y ^ b ≤ f (a • x + b • y) :=
  Iff.rfl

namespace LogConcave

variable {f g : E → ℝ≥0∞}

/-- The defining inequality of a log-concave function. -/
theorem rpow_mul_rpow_le (hf : LogConcave f) {x y : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : f x ^ a * f y ^ b ≤ f (a • x + b • y) :=
  hf ha hb hab

/-- The minimum of two values of a log-concave function is at most its value at any convex
combination of the two points. -/
theorem ge_on_segment' (hf : LogConcave f) {x y : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : min (f x) (f y) ≤ f (a • x + b • y) := by
  first
  | calc min (f x) (f y) = min (f x) (f y) ^ a * min (f x) (f y) ^ b := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ ha hb, hab, ENNReal.rpow_one]
      _ ≤ f x ^ a * f y ^ b := by gcongr <;> simp
      _ ≤ f (a • x + b • y) := hf ha hb hab

/-- **Every superlevel set of a log-concave function is convex.** -/
theorem convex_ge (hf : LogConcave f) (r : ℝ≥0∞) : Convex ℝ {x | r ≤ f x} :=
  fun _ hx _ hy _ _ ha hb hab ↦ (le_min hx hy).trans (hf.ge_on_segment' ha hb hab)

/-- **Every strict superlevel set of a log-concave function is convex.** -/
theorem convex_gt (hf : LogConcave f) (r : ℝ≥0∞) : Convex ℝ {x | r < f x} :=
  fun _ hx _ hy _ _ ha hb hab ↦ (lt_min hx hy).trans_le (hf.ge_on_segment' ha hb hab)

/-- **The support of a log-concave function is convex** (Bombieri–Gubler, Remark C.3.2). -/
theorem convex_support (hf : LogConcave f) : Convex ℝ (Function.support f) := by
  first
  | simpa only [Function.support, pos_iff_ne_zero] using hf.convex_gt 0

/-- A product of log-concave functions is log-concave. -/
protected theorem mul (hf : LogConcave f) (hg : LogConcave g) : LogConcave (f * g) := by
  first
  | intro x y a b ha hb hab
    simp only [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.mul_rpow_of_nonneg _ _ hb]
    calc f x ^ a * g x ^ a * (f y ^ b * g y ^ b) = f x ^ a * f y ^ b * (g x ^ a * g y ^ b) := by
          ring
      _ ≤ f (a • x + b • y) * g (a • x + b • y) := mul_le_mul' (hf ha hb hab) (hg ha hb hab)

/-- Composing a log-concave function with a linear map gives a log-concave function. -/
theorem comp_linearMap (hf : LogConcave f) (L : F →ₗ[ℝ] E) : LogConcave (f ∘ L) := by
  first
  | intro x y a b ha hb hab
    simpa only [Function.comp_apply, map_add, map_smul] using hf (x := L x) (y := L y) ha hb hab

/-- **An even log-concave function is largest at the origin.** Applied to the measures of the
parallel slices of a symmetric convex body, this says that the central slice is the largest. -/
theorem apply_le_apply_zero {G : Type*} [AddCommGroup G] [Module ℝ G] {f : G → ℝ≥0∞}
    (hf : LogConcave f) (hfe : f.Even) (x : G) : f x ≤ f 0 := by
  first
  | have h := hf.ge_on_segment' (x := x) (y := -x) (a := 1 / 2) (b := 1 / 2) (by norm_num)
      (by norm_num) (by norm_num)
    rwa [hfe x, min_self, show (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • -x = 0 by module] at h

end LogConcave

/-- A constant function is log-concave. -/
theorem logConcave_const (c : ℝ≥0∞) : LogConcave fun _ : E ↦ c := fun _ _ _ _ ha hb hab ↦ by
  rw [← ENNReal.rpow_add_of_nonneg _ _ ha hb, hab, ENNReal.rpow_one]

/-- The indicator of a convex set is log-concave, at any value. -/
theorem _root_.Convex.logConcave_indicator {s : Set E} (hs : Convex ℝ s) (c : ℝ≥0∞) :
    LogConcave (s.indicator fun _ ↦ c) := by
  first
  | intro x y a b ha hb hab
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem (hs hx hy ha hb hab),
          ← ENNReal.rpow_add_of_nonneg _ _ ha hb, hab, ENNReal.rpow_one]
      · rcases hb.eq_or_lt with rfl | hb
        · simp_all
        · simp [indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
    · rcases ha.eq_or_lt with rfl | ha
      · simp_all
      · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha]

/-- The indicator of a set at a nonzero value is log-concave if and only if the set is convex. -/
theorem logConcave_indicator_iff {s : Set E} {c : ℝ≥0∞} (hc : c ≠ 0) :
    LogConcave (s.indicator fun _ ↦ c) ↔ Convex ℝ s :=
  ⟨fun h ↦ by simpa [Function.support_const hc] using h.convex_support,
    fun hs ↦ hs.logConcave_indicator c⟩

/-- A function `x ↦ exp (g x)` is log-concave if and only if `g` is concave. -/
theorem logConcave_ofReal_exp_iff {g : E → ℝ} :
    LogConcave (fun x ↦ ENNReal.ofReal (Real.exp (g x))) ↔ ConcaveOn ℝ univ g := by
  first
  | have key (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
        ENNReal.ofReal (Real.exp (g x)) ^ a * ENNReal.ofReal (Real.exp (g y)) ^ b =
          ENNReal.ofReal (Real.exp (a * g x + b * g y)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ha,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hb, ← Real.exp_mul, ← Real.exp_mul,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_comm (g x), mul_comm (g y)]
    refine ⟨fun h ↦ ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩,
      fun h x y a b ha hb hab ↦ ?_⟩
    · have := h (x := x) (y := y) ha hb hab
      rw [key x y ha hb, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp] at this
      simpa only [smul_eq_mul] using this
    · rw [key x y ha hb]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (h.2 trivial trivial ha hb hab))

/-- The Gaussian `x ↦ exp (-c ‖x‖ ^ 2)` on a real normed space is log-concave for `0 ≤ c`. -/
theorem logConcave_ofReal_exp_neg_mul_sq_norm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace ℝ G] {c : ℝ} (hc : 0 ≤ c) :
    LogConcave fun x : G ↦ ENNReal.ofReal (Real.exp (-c * ‖x‖ ^ 2)) := by
  first
  | refine logConcave_ofReal_exp_iff.2 ?_
    have h := ((convexOn_norm (convex_univ (𝕜 := ℝ) (E := G))).pow
      (fun x _ ↦ norm_nonneg x) 2).neg.smul hc
    convert h using 2 with x
    simp [neg_mul, smul_eq_mul]

end TauCeti
end -- closes the original EOF section from source line 61
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/Convex/LogConcave.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/SpecialFunctions/Pow/Integral.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals` is imported privately: it supplies
-- `not_integrableOn_Ioi_rpow`, used only inside the proof of
-- `TauCeti.lintegral_ofReal_rpow_Ioi`.
-- `Mathlib.Analysis.SpecialFunctions.Integrals.Basic` is imported privately: it supplies the
-- interval integral of `t ^ s`, used only inside the proof of
-- `TauCeti.lintegral_ofReal_rpow_Ioo`.

/-!
# Lower integrals of a real power, and the layer cake formula in `ℝ≥0∞`

This file collects the two lower integrals of `t ↦ t ^ s` on a half-line that the real
interpolation method needs, and uses them to transport Mathlib's layer cake formula from
real-valued to `ℝ≥0∞`-valued functions.

For `-1 < s` the function `t ↦ t ^ s` is integrable near `0` and not integrable near `∞`, and the
two computations below are the two halves of that dichotomy:
`TauCeti.lintegral_ofReal_rpow_Ioo` evaluates `∫⁻ t in (0, a), t ^ s` to the expected
antiderivative for such an `s`, while `TauCeti.lintegral_ofReal_rpow_Ioi` records that
`∫⁻ t in (0, ∞), t ^ s` diverges — the latter for *every* exponent `s`, since a power that is
integrable at the origin is not integrable at infinity and conversely.

`TauCeti.lintegral_indicator_ofReal_rpow_Ioi` packages the two together as the single formula the
real interpolation method uses: the integral over `(0, ∞)` of `t ^ s` cut off at the height where
`c * t` reaches a threshold `a : ℝ≥0∞`, which is the finite antiderivative when `a` is finite and
`∞` when it is not.

`TauCeti.lintegral_indicator_le_ofReal_rpow_Ioi` is the companion over the complementary region,
where `c * t` has already passed the threshold. There the roles of the two endpoints are
exchanged: the integral converges at infinity and diverges at the origin, so the exponent range is
`s < -1` and the value is `∞` exactly when the threshold is `0`. The two together are what the
real interpolation method between two finite exponents integrates against, the first for the part
of a function above a height and the second for the part below it.

The layer cake formula `∫⁻ u ^ p = p * ∫⁻ t in (0, ∞), ν {u > t} * t ^ (p - 1)` is in Mathlib as
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`, but only for a nonnegative *real-valued*
`u`. Analysis in `ℝ≥0∞` — where the operators of interpolation theory naturally land, since a
supremum of averages such as the Hardy–Littlewood maximal function is defined without any
finiteness hypothesis — needs the version for `u : β → ℝ≥0∞`, which is
`TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul` below. The superlevel sets there are cut
at the `ℝ≥0∞`-valued threshold `ENNReal.ofReal t`, which is what distinguishes the statement from
Mathlib's.

The passage between the two is by `ENNReal.toReal`, which is faithful exactly where `u` is finite.
Where `u = ∞` on a set of positive measure both sides are `∞`: the left because `u ^ p = ∞`
there, and the right because every superlevel set then has measure at least that of `{u = ∞}`,
and `∫⁻ t in (0, ∞), t ^ (p - 1)` diverges. That is where `TauCeti.lintegral_ofReal_rpow_Ioi` is
used, and it is why the statement needs no finiteness hypothesis on `u`.

## Main declarations

* `TauCeti.lintegral_ofReal_rpow_Ioo`: `∫⁻ t in (0, a), t ^ s = a ^ (s + 1) / (s + 1)` for
  `-1 < s` and `0 ≤ a`.
* `TauCeti.lintegral_ofReal_rpow_Ioi`: `∫⁻ t in (0, ∞), t ^ s = ∞`, for every `s`.
* `TauCeti.lintegral_indicator_ofReal_rpow_Ioi`: the same integral truncated at the height where
  `c * t` reaches `a : ℝ≥0∞`, evaluated to `c ^ (-(s + 1)) / (s + 1) * a ^ (s + 1)`.
* `TauCeti.lintegral_indicator_le_ofReal_rpow_Ioi`: the integral over the complementary region,
  where `c * t` is at least `a`, evaluated to `c ^ (-(s + 1)) / (-(s + 1)) * a ^ (s + 1)` for
  `s < -1`.
* `TauCeti.setLIntegral_Ioc_ite_rpow_le`: an upper-tail bound for a negative power restricted by
  a linear threshold.
* `TauCeti.setLIntegral_Ioc_rpow_mul_ite_le`: the same bound with constant and linear weights.
* `TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul`: the layer cake formula for an
  `ℝ≥0∞`-valued function.
* `TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`: a function with finite positive
  power integral is carried by a σ-finite part of the measure.

## References

* L. Grafakos, *Classical Fourier Analysis*, Proposition 1.1.4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {s : ℝ}

/-- The lower integral of `t ^ s` over a bounded interval `(0, a)`, for `-1 < s` and `0 ≤ a`: the
power is integrable at the origin and the value is the expected antiderivative.

Nonnegativity of `a` is needed: for `a < 0` the interval is empty while `a ^ (s + 1)`, a real power
at a negative base, need not vanish. -/
theorem lintegral_ofReal_rpow_Ioo (hs : -1 < s) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ t in Ioo (0 : ℝ) a, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (a ^ (s + 1) / (s + 1)) := by
  first
  | have hs1 : (0 : ℝ) < s + 1 := by linarith
    have hint : IntegrableOn (fun t : ℝ => t ^ s) (Ioo 0 a) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a) hs
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at h
      exact h.mono_set Ioo_subset_Ioc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) a)] fun t : ℝ => t ^ s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le s
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hs), Real.zero_rpow hs1.ne',
      sub_zero]

/-- The lower integral of `t ^ s` over `(0, ∞)` diverges, for every exponent `s`: the power fails
to be integrable at the origin or at infinity, according as `s ≤ -1` or `-1 < s`. -/
theorem lintegral_ofReal_rpow_Ioi (s : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) = ∞ := by
  first
  | by_contra hne
    have hmeas : Measurable fun t : ℝ => t ^ s := measurable_id.pow measurable_const
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => t ^ s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (le_of_lt ht) s
    exact not_integrableOn_Ioi_rpow s
      ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 hne)⟩

/-- The tail integral `∫_{r / D}^∞ t ^ (-n - 1) dt = D ^ n r ^ (-n) / n` bounds the integral of
`t ^ (-n - 1)` over those `t ∈ (0, 1]` with `r ≤ t * D`. -/
theorem setLIntegral_Ioc_ite_rpow_le {n : ℕ} (hn : 0 < n) {r D : ℝ} (hr : 0 < r) :
    ∫⁻ t in Ioc (0 : ℝ) 1, (if r ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) else 0) ≤
      ENNReal.ofReal (D ^ n / n) * ENNReal.ofReal (r ^ (-(n : ℝ))) := by
  first
  | rcases le_or_gt D 0 with hD | hD
    · have hzero : ∀ t ∈ Ioc (0 : ℝ) 1,
          (if r ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) else 0) = 0 := fun t ht =>
        ite_eq_right (by nlinarith [ht.1])
      rw [setLIntegral_congr_fun measurableSet_Ioc hzero]
      simp
    have hc : 0 < r / D := div_pos hr hD
    have hn' : -(n : ℝ) - 1 < -1 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      linarith
    calc
      _ ≤ ∫⁻ t, (Ici (r / D)).indicator (fun t => ENNReal.ofReal (t ^ (-(n : ℝ) - 1))) t := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun t => ?_)
        split_ifs with h
        · have hmem : t ∈ Ici (r / D) := mem_Ici.2 ((div_le_iff₀ hD).2 h)
          rw [indicator_of_mem hmem]
        · exact bot_le
      _ = ∫⁻ t in Ioi (r / D), ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) := by
        rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici]
      _ = ENNReal.ofReal (∫ t in Ioi (r / D), t ^ (-(n : ℝ) - 1)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hn' hc)]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpow_nonneg (hc.trans ht).le _
      _ = ENNReal.ofReal (D ^ n / n) * ENNReal.ofReal (r ^ (-(n : ℝ))) := by
        rw [integral_Ioi_rpow_of_lt hn' hc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have hexp : -(n : ℝ) - 1 + 1 = -(n : ℝ) := by ring
        rw [hexp, Real.div_rpow hr.le hD.le, Real.rpow_neg hD.le, Real.rpow_natCast]
        field_simp

/-- The bound of `setLIntegral_Ioc_ite_rpow_le`, multiplied by the length `r` of a segment and by
a weight `a`, gives the kernel `r ^ (1 - n)`. -/
theorem setLIntegral_Ioc_rpow_mul_ite_le {n : ℕ} (hn : 0 < n) (a : ℝ≥0∞) {r : ℝ}
    (hr : 0 ≤ r) (D : ℝ) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) *
        (a * if r ≤ t * D then ENNReal.ofReal r else 0) ≤
      ENNReal.ofReal (D ^ n / n) * (a * ENNReal.ofReal r ^ (1 - (n : ℝ))) := by
  first
  | have hL : ∀ t : ℝ, ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) *
        (a * if r ≤ t * D then ENNReal.ofReal r else 0) = a * ENNReal.ofReal r *
          if r ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) else 0 := by
      intro t
      split_ifs <;> ring
    simp_rw [hL]
    rw [lintegral_const_mul _ (Measurable.ite (measurableSet_le measurable_const (by fun_prop))
      (by fun_prop) measurable_const)]
    rcases hr.eq_or_lt with rfl | hr
    · simp
    calc
      _ ≤ a * ENNReal.ofReal r *
          (ENNReal.ofReal (D ^ n / n) * ENNReal.ofReal (r ^ (-(n : ℝ)))) := by
        gcongr
        exact setLIntegral_Ioc_ite_rpow_le hn hr
      _ = _ := by
        have hexp : (1 : ℝ) - n = 1 + -(n : ℝ) := by ring
        rw [ENNReal.ofReal_rpow_of_pos hr, hexp, Real.rpow_add hr, Real.rpow_one,
          ENNReal.ofReal_mul hr.le]
        ring

/-- **A finite threshold on `c * t` cuts `(0, ∞)` down to a bounded interval.** For `0 < c` and
`a ≠ ∞`, the indicator of `{t | ENNReal.ofReal (c * t) < a}` agrees at every positive `t` with the
indicator of `(0, a.toReal / c)`, whatever the integrand. -/
private theorem indicator_ofReal_mul_lt_eq_indicator_Ioo {a : ℝ≥0∞} (ha : a ≠ ∞) {c : ℝ}
    (hc : 0 < c) (f : ℝ → ℝ≥0∞) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    {t : ℝ | ENNReal.ofReal (c * t) < a}.indicator f t =
      (Ioo (0 : ℝ) (a.toReal / c)).indicator f t := by
  first
  | have ht' : (0 : ℝ) < t := ht
    have hiff : t ∈ {t : ℝ | ENNReal.ofReal (c * t) < a} ↔ t ∈ Ioo (0 : ℝ) (a.toReal / c) := by
      rw [Set.mem_ofPred, Set.mem_Ioo, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ha,
        lt_div_iff₀ hc, mul_comm c t]
      exact ⟨fun h => ⟨ht', h⟩, fun h => h.2⟩
    by_cases hmem : t ∈ Ioo (0 : ℝ) (a.toReal / c)
    · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem fun h => hmem (hiff.1 h), Set.indicator_of_notMem hmem]

/-- The lower integral of `t ^ s` over `(0, ∞)`, truncated at the height where `c * t` reaches a
threshold `a : ℝ≥0∞`: for `-1 < s` and `0 < c`,

`∫⁻ t in (0, ∞), [c * t < a] * t ^ s = c ^ (-(s + 1)) / (s + 1) * a ^ (s + 1)`.

For a finite `a` the cut-off makes this the integral over `(0, a / c)` evaluated by
`TauCeti.lintegral_ofReal_rpow_Ioo`; for `a = ∞` the cut-off is vacuous and both sides are `∞`, by
`TauCeti.lintegral_ofReal_rpow_Ioi`. This is the inner integral of the real interpolation method,
where `a` is the value of the function being interpolated at a point. -/
theorem lintegral_indicator_ofReal_rpow_Ioi (hs : -1 < s) {c : ℝ} (hc : 0 < c) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | ENNReal.ofReal (c * t) < a}.indicator (fun t => ENNReal.ofReal (t ^ s)) t =
      ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * a ^ (s + 1) := by
  first
  | have hs1 : (0 : ℝ) < s + 1 := by linarith
    have hconst : (0 : ℝ) < c ^ (-(s + 1)) / (s + 1) := by positivity
    rcases eq_or_ne a ∞ with rfl | ha
    · -- The cut-off is vacuous and the integral diverges.
      have hmem : ∀ t : ℝ, t ∈ {t : ℝ | ENNReal.ofReal (c * t) < ∞} := fun t =>
        Set.mem_ofPred.2 ENNReal.ofReal_lt_top
      rw [setLIntegral_congr_fun measurableSet_Ioi
          (fun t _ => Set.indicator_of_mem (hmem t) _),
        lintegral_ofReal_rpow_Ioi, ENNReal.top_rpow_of_pos hs1,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hconst).ne']
    rcases eq_or_ne a 0 with rfl | ha0
    · -- The cut-off is empty and both sides vanish.
      simp [ENNReal.zero_rpow_of_pos hs1]
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun t ht => indicator_ofReal_mul_lt_eq_indicator_Ioo ha hc _ ht)]
    -- abbreviate only now: `set` folds `a.toReal`, which the cut-off lemma above spells out
    set b : ℝ := a.toReal
    have hb0 : 0 < b := ENNReal.toReal_pos ha0 ha
    have hab : a = ENNReal.ofReal b := (ENNReal.ofReal_toReal ha).symm
    -- The elementary real identity behind the constant `c ^ (-(s + 1))`.
    have hreal : (b / c) ^ (s + 1) / (s + 1) = c ^ (-(s + 1)) / (s + 1) * b ^ (s + 1) := by
      have hcp : c ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
      rw [Real.div_rpow hb0.le hc.le, Real.rpow_neg hc.le]
      field_simp
    rw [lintegral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left Ioo_subset_Ioi_self,
      lintegral_ofReal_rpow_Ioo hs (by positivity), hab,
      ENNReal.ofReal_rpow_of_nonneg hb0.le hs1.le, ← ENNReal.ofReal_mul hconst.le, hreal]

/-- **A threshold already passed by `c * t` cuts `(0, ∞)` down to a half-line.** For `0 < c` and
`a ≠ ∞`, the indicator of `{t | a ≤ ENNReal.ofReal (c * t)}` agrees at every positive `t` with the
indicator of `[a.toReal / c, ∞)`, whatever the integrand. -/
private theorem indicator_le_ofReal_mul_eq_indicator_Ici {a : ℝ≥0∞} (ha : a ≠ ∞) {c : ℝ}
    (hc : 0 < c) (f : ℝ → ℝ≥0∞) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    {t : ℝ | a ≤ ENNReal.ofReal (c * t)}.indicator f t =
      (Ici (a.toReal / c)).indicator f t := by
  first
  | have ht' : (0 : ℝ) < t := ht
    have hiff : t ∈ {t : ℝ | a ≤ ENNReal.ofReal (c * t)} ↔ t ∈ Ici (a.toReal / c) := by
      rw [Set.mem_ofPred, Set.mem_Ici,
        ENNReal.le_ofReal_iff_toReal_le ha (by positivity), div_le_iff₀ hc, mul_comm c t]
    by_cases hmem : t ∈ Ici (a.toReal / c)
    · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem fun h => hmem (hiff.1 h), Set.indicator_of_notMem hmem]

/-- The lower integral of `t ^ s` over `(0, ∞)`, restricted to the heights at which `c * t` has
already reached a threshold `a : ℝ≥0∞`: for `s < -1` and `0 < c`,

`∫⁻ t in (0, ∞), [a ≤ c * t] * t ^ s = c ^ (-(s + 1)) / (-(s + 1)) * a ^ (s + 1)`.

For a nonzero `a` this is the convergent tail integral over `[a / c, ∞)`; for `a = 0` the
restriction is vacuous and both sides are `∞`, by `TauCeti.lintegral_ofReal_rpow_Ioi`, while for
`a = ∞` the region is empty and both sides vanish. This is the inner integral that the real
interpolation method pairs with the part of a function *below* the height `c * t`, the exponent
range `s < -1` being the one in which the power is integrable at infinity; the complementary
region is `TauCeti.lintegral_indicator_ofReal_rpow_Ioi`. -/
theorem lintegral_indicator_le_ofReal_rpow_Ioi (hs : s < -1) {c : ℝ} (hc : 0 < c) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | a ≤ ENNReal.ofReal (c * t)}.indicator (fun t => ENNReal.ofReal (t ^ s)) t =
      ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) * a ^ (s + 1) := by
  first
  | have hs1 : s + 1 < 0 := by linarith
    have hs1' : (0 : ℝ) < -(s + 1) := by linarith
    have hconst : (0 : ℝ) < c ^ (-(s + 1)) / (-(s + 1)) := by positivity
    rcases eq_or_ne a ∞ with rfl | ha
    · -- No positive `t` reaches the threshold, and `∞ ^ (s + 1) = 0`.
      have hempty : ∀ t : ℝ, t ∉ {t : ℝ | (∞ : ℝ≥0∞) ≤ ENNReal.ofReal (c * t)} := fun t ht =>
        absurd (top_le_iff.1 ht) ENNReal.ofReal_ne_top
      rw [setLIntegral_congr_fun measurableSet_Ioi
        (fun t _ => Set.indicator_of_notMem (hempty t) _)]
      simp [ENNReal.top_rpow_of_neg hs1]
    rcases eq_or_ne a 0 with rfl | ha0
    · -- Every positive `t` reaches the threshold, and the integral diverges at the origin.
      have hall : ∀ t : ℝ, t ∈ {t : ℝ | (0 : ℝ≥0∞) ≤ ENNReal.ofReal (c * t)} := fun _ =>
        Set.mem_ofPred.2 zero_le
      rw [setLIntegral_congr_fun measurableSet_Ioi (fun t _ => Set.indicator_of_mem (hall t) _),
        lintegral_ofReal_rpow_Ioi, ENNReal.zero_rpow_of_neg hs1,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hconst).ne']
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun t ht => indicator_le_ofReal_mul_eq_indicator_Ici ha hc _ ht)]
    -- abbreviate only now: `set` folds `a.toReal`, which the cut-off lemma above spells out
    set b : ℝ := a.toReal
    have hb0 : 0 < b := ENNReal.toReal_pos ha0 ha
    have hbc : 0 < b / c := by positivity
    have hab : a = ENNReal.ofReal b := (ENNReal.ofReal_toReal ha).symm
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (b / c))] fun t : ℝ => t ^ s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (hbc.trans ht).le s
    -- The elementary real identity behind the constant `c ^ (-(s + 1))`.
    have hreal : -(b / c) ^ (s + 1) / (s + 1) = c ^ (-(s + 1)) / (-(s + 1)) * b ^ (s + 1) := by
      have hcp : c ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
      rw [Real.div_rpow hb0.le hc.le, Real.rpow_neg hc.le]
      field_simp
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      Set.inter_eq_self_of_subset_left (Set.Ici_subset_Ioi.2 hbc),
      ← setLIntegral_congr Ioi_ae_eq_Ici,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hs hbc) hnn,
      integral_Ioi_rpow_of_lt hs hbc, hreal, hab, ENNReal.ofReal_rpow_of_pos hb0,
      ← ENNReal.ofReal_mul hconst.le]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞} {p : ℝ}

/-- A function with a finite `L^p` norm is carried by a σ-finite part of the measure: the level
sets `{f ≥ 1 / (n + 1)}` have finite measure by Chebyshev's inequality applied to `f ^ p`, and they
exhaust `{f > 0}`. -/
theorem sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top (hf : AEMeasurable f μ)
    (hp : 0 < p) (htop : ∫⁻ x, f x ^ p ∂μ ≠ ∞) : SigmaFinite (μ.restrict {x | 0 < f x}) := by
  first
  | let g := hf.mk f
    have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
    have htopg : ∫⁻ x, g x ^ p ∂μ ≠ ∞ := by
      have heq : ∫⁻ x, f x ^ p ∂μ = ∫⁻ x, g x ^ p ∂μ :=
        lintegral_congr_ae (hfg.fun_comp fun z => z ^ p)
      rwa [← heq]
    have hsigma : SigmaFinite (μ.restrict {x | 0 < g x}) := by
      have hg : Measurable g := hf.measurable_mk
      have hsmeas : MeasurableSet {x | 0 < g x} := measurableSet_lt measurable_const hg
      have hlevel : ∀ n : ℕ, μ {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x} ≠ ∞ := by
        intro n
        have hne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
        have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
          ENNReal.inv_pos.2 (by simp [ENNReal.natCast_ne_top])
        have hεpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ ^ p := ENNReal.rpow_pos hpos hne
        have hset : {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x} =
            {x | ((n : ℝ≥0∞) + 1)⁻¹ ^ p ≤ g x ^ p} :=
          Set.ext fun x => (ENNReal.rpow_le_rpow_iff hp).symm
        rw [hset]
        refine ne_top_of_le_ne_top (ENNReal.div_lt_top htopg hεpos.ne').ne
          (meas_ge_le_lintegral_div (hg.pow_const p).aemeasurable hεpos.ne'
            (ENNReal.rpow_ne_top_of_nonneg hp.le hne))
      refine ⟨⟨⟨fun n => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x} ∪ {x | 0 < g x}ᶜ,
        fun _ => trivial, ?_, ?_⟩⟩⟩
      · intro n
        have hcompl : μ.restrict {x | 0 < g x} {x | 0 < g x}ᶜ = 0 := by
          rw [Measure.restrict_apply hsmeas.compl, Set.compl_inter_self, measure_empty]
        refine lt_of_le_of_lt (measure_union_le _ _) ?_
        rw [hcompl, add_zero]
        exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) (lt_top_iff_ne_top.2 (hlevel n))
      · refine Set.eq_univ_of_forall fun x => ?_
        rcases eq_or_ne (g x) 0 with hx | hx
        · exact Set.mem_iUnion.2 ⟨0, Set.mem_union_right _ (by simp [hx])⟩
        · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx
          exact Set.mem_iUnion.2
            ⟨n, Set.mem_union_left _ ((ENNReal.inv_le_inv' le_self_add).trans hn.le)⟩
    have hpos : {x | 0 < f x} =ᵐ[μ] {x | 0 < g x} :=
      hfg.mono fun _ hx => by simp only [Set.mem_ofPred_eq]; rw [hx]
    rw [Measure.restrict_congr_set hpos]
    exact hsigma

variable {β : Type*} [MeasurableSpace β]

/-- **The layer cake formula** for an `ℝ≥0∞`-valued function: for `0 < p`,

`∫⁻ u ^ p ∂ν = p * ∫⁻ t in (0, ∞), ν {u > t} * t ^ (p - 1)`,

where the superlevel set is cut at the threshold `ENNReal.ofReal t`.

This is `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` for a function that is allowed to
take the value `∞`; no finiteness hypothesis is needed, because both sides are `∞` as soon as
`{u = ∞}` has positive measure. -/
theorem lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul (ν : Measure β) {u : β → ℝ≥0∞}
    (hu : AEMeasurable u ν) {p : ℝ} (hp : 0 < p) :
    ∫⁻ y, u y ^ p ∂ν = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1)) := by
  first
  | rcases eq_or_ne (ν {y | u y = ∞}) 0 with hnull | hnull
    · -- `u` is finite almost everywhere, so `ENNReal.toReal` transports Mathlib's formula.
      have hfin : ∀ᵐ y ∂ν, u y ≠ ∞ := by rw [ae_iff]; simpa using hnull
      have hg : AEMeasurable (fun y => (u y).toReal) ν := hu.ennreal_toReal
      have hnn : 0 ≤ᵐ[ν] fun y => (u y).toReal := .of_forall fun _ => ENNReal.toReal_nonneg
      have hL : ∫⁻ y, u y ^ p ∂ν = ∫⁻ y, ENNReal.ofReal ((u y).toReal ^ p) ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin] with y hy
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, ENNReal.ofReal_toReal hy]
      rw [hL, lintegral_rpow_eq_lintegral_meas_lt_mul ν hnn hg hp]
      refine congrArg _ (setLIntegral_congr_fun measurableSet_Ioi fun t ht => congrArg₂ _ ?_ rfl)
      refine measure_congr ?_
      filter_upwards [hfin] with y hy
      exact propext (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) hy).symm
    · -- `u = ∞` on a set of positive measure: both sides are `∞`.
      have hL : ∫⁻ y, u y ^ p ∂ν = ∞ := by
        have hlevel : {y | u y ^ p = ∞} = {y | u y = ∞} :=
          Set.ext fun y => ENNReal.rpow_eq_top_iff_of_pos hp
        refine lintegral_eq_top_of_measure_eq_top_ne_zero (hu.pow_const p) ?_
        rwa [hlevel]
      have hR : ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} *
          ENNReal.ofReal (t ^ (p - 1)) = ∞ := by
        have hsub : ∀ {t : ℝ}, {y | u y = ∞} ⊆ {y | ENNReal.ofReal t < u y} := by
          intro t y (hy : u y = ∞)
          rw [Set.mem_ofPred_eq, hy]
          exact ENNReal.ofReal_lt_top
        refine top_le_iff.1 ?_
        calc (∞ : ℝ≥0∞)
            = ν {y | u y = ∞} * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) := by
              rw [lintegral_ofReal_rpow_Ioi (p - 1), ENNReal.mul_top hnull]
          _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | u y = ∞} * ENNReal.ofReal (t ^ (p - 1)) :=
              (lintegral_const_mul _ ((measurable_id.pow measurable_const).ennreal_ofReal)).symm
          _ ≤ _ := lintegral_mono fun t => mul_le_mul_left (measure_mono hsub) _
      rw [hL, hR, ENNReal.mul_top (ENNReal.ofReal_pos.2 hp).ne']

end TauCeti
end -- closes the original EOF section from source line 82
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/SpecialFunctions/Pow/Integral.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/SpecialFunctions/Pow/Real.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Real powers

The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`. Like
Mathlib's `Real.sqrt_eq_rpow`, this holds for every real `x`. For `x < 0` both sides vanish: the
square root is `0`, and `x ^ y = exp (log x * y) * cos (y * π)` has the factor `cos (-π / 2) = 0`.
This is the form in which a kernel `1 / √d` is compared with the singular powers `|x - c| ^ (-1/2)`.
For `0 ≤ t`, its natural powers are `(√t)⁻¹ ^ n = t ^ (-n/2)`, the factor of a parabolic scaling.

Eventually along a filter on which `x` is positive, the power `x ^ q` is `exp (q * log x)`. This is
the form in which power weights `x ^ q` are compared with exponential tilting weights.

The square root of a natural power of a nonnegative real is the real power with half the exponent:
`√(x ^ n) = x ^ (n / 2)`. This is the form in which a determinant `det (c • G) = c ^ n det G` of
an `n × n` matrix contributes to a volume density `√(det G)`.

A real power of a nonnegative base can also be written as a power of its square:
`(x ^ 2) ^ (s / 2) = x ^ s`.

For `i < d`, comparing the `(d - i)`-th root `x ^ (1 / (d - i))` with `y` is comparing `x` with
the natural power `y ^ (d - i)`, the form in which spectral values of polynomials are bounded.

For `n ≠ 0`, the `n`-th power of `x ^ (1 - 1/n)` is `x ^ (n - 1)` for nonnegative `x`, the form in
which the volume factor `V ^ (1 - 1/n)` of an isoperimetric inequality is raised to the `n`-th
power.

A natural power `b ^ n` with `1 ≤ b` and `n ≤ δ r` is at most `(b ^ δ) ^ r`, which turns a degree
bound with a real factor `δ` into a bound by an `r`-th power.

A positive power `x ↦ x ^ a` maps the open unit interval onto itself, with inverse `y ↦ y ^ a⁻¹`.
This is the image needed when a change of variables `y = x ^ a` is performed on `(0, 1)`.

A real number whose natural powers grow at most polynomially, `r ^ n ≤ C * (1 + n) ^ s` for all
`n`, is at most `1`. This is how a spectral radius bound is read off from polynomially growing
norms, as for the monomials of a weighted Sobolev algebra.

A positive real raised to a finitely supported sum of exponents is the product of the powers:
`a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i`, the `finsum` form of `Real.rpow_sum_of_pos`.

An exponential upper bound on a nonnegative base passes to its nonnegative real powers: if
`0 ≤ A ≤ e^{-t}` and `0 ≤ c`, then `A ^ c ≤ e^{-c t}`. This is how a bound `|q| ≤ e^{-t}` on a
nome is turned into bounds on the fractional powers `|q| ^ c` in a product estimate.

## Main results

* `Real.inv_sqrt_eq_rpow`: `(√x)⁻¹ = x ^ (-2⁻¹)` for every real `x`.
* `Real.inv_sqrt_pow_eq_rpow`: `(√t)⁻¹ ^ n = t ^ (-n/2)` for `0 ≤ t`.
* `Real.rpow_eventuallyEq_exp_mul_log`: `x ^ q = exp (q * log x)` eventually along a filter on
  which `x` is eventually positive.
* `Real.sqrt_pow_eq_rpow`: `√(x ^ n) = x ^ (n / 2)` for `0 ≤ x`.
* `Real.sq_rpow_div_two`: `(x ^ 2) ^ (s / 2) = x ^ s` for `0 ≤ x`.
* `Real.rpow_one_div_natCast_sub_le_iff`: `x ^ (1 / (d - i)) ≤ y ↔ x ≤ y ^ (d - i)` for `i < d`
  and nonnegative `x`, `y`.
* `Real.rpow_one_sub_inv_natCast_pow`: `(x ^ (1 - 1/n)) ^ n = x ^ (n - 1)` for `0 ≤ x` and
  `n ≠ 0`.
* `Real.pow_le_rpow_pow_of_le_mul`: `b ^ n ≤ (b ^ δ) ^ r` when `1 ≤ b` and `n ≤ δ r`.
* `Real.image_rpow_Ioo_zero_one`: a positive power maps the open unit interval onto itself.
* `Real.le_one_of_forall_pow_le_mul_rpow`: `r ≤ 1` when `r ^ n ≤ C * (1 + n) ^ s` for all `n`.
* `Real.rpow_le_exp_neg_mul`: `A ^ c ≤ e^{-c t}` when `0 ≤ A ≤ e^{-t}` and `0 ≤ c`.
* `Function.HasFiniteSupport.hasFiniteMulSupport_fun_rpow`: real powers with finitely supported
  exponents have finite multiplicative support.
* `Real.rpow_finsum_of_pos`: `a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i` for `0 < a` and finitely supported
  `f`.
-/

public section

open Filter Topology

namespace Real

/-- The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`, for
every real `x`. -/
theorem inv_sqrt_eq_rpow (x : ℝ) : (√x)⁻¹ = x ^ (-2⁻¹ : ℝ) := by
  first
  | rcases le_or_gt 0 x with hx | hx
    · rw [sqrt_eq_rpow, rpow_neg hx, one_div]
    · rw [sqrt_eq_zero'.mpr hx.le, inv_zero, rpow_def_of_neg hx, neg_mul, cos_neg, inv_mul_eq_div,
        cos_pi_div_two, mul_zero]

/-- A natural power of the inverse square root is a real power: `(√t)⁻¹ ^ n = t ^ (-n/2)` for
`0 ≤ t`. This is the factor of a parabolic scaling `x ↦ (√t)⁻¹ • x` in dimension `n`. -/
theorem inv_sqrt_pow_eq_rpow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : (√t)⁻¹ ^ n = t ^ (-(n : ℝ) / 2) := by
  first
  | rw [rpow_div_two_eq_sqrt _ ht, rpow_neg (sqrt_nonneg t), rpow_natCast, inv_pow]

/-- Along a filter on which `x` is eventually positive, `x ^ q` is eventually `exp (q * log x)`. -/
theorem rpow_eventuallyEq_exp_mul_log {l : Filter ℝ} (hpos : ∀ᶠ x in l, 0 < x) (q : ℝ) :
    (fun x => x ^ q) =ᶠ[l] fun x => exp (q * log x) :=
  hpos.mono fun _ hx => (rpow_def_of_pos hx q).trans (congrArg exp (mul_comm _ _))

/-- The square root of a natural power of a nonnegative real is the real power with half the
exponent: `√(x ^ n) = x ^ (n / 2)`. -/
theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : √(x ^ n) = x ^ ((n : ℝ) / 2) := by
  first
  | rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hx, mul_one_div]

/-- For a nonnegative real number `a`, taking the real power `s / 2` of `a ^ 2` gives `a ^ s`. -/
@[simp]
theorem sq_rpow_div_two {a : ℝ} (ha : 0 ≤ a) (s : ℝ) : (a ^ 2) ^ (s / 2) = a ^ s := by
  first
  | rw [rpow_div_two_eq_sqrt s (sq_nonneg a), sqrt_sq ha]

/-- For `i < d`, the `(d - i)`-th root of a nonnegative `x` is at most a nonnegative `y` exactly
when `x ≤ y ^ (d - i)`. -/
theorem rpow_one_div_natCast_sub_le_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {d i : ℕ}
    (h : i < d) : x ^ (1 / (d - i : ℝ)) ≤ y ↔ x ≤ y ^ (d - i) := by
  first
  | rw [← Nat.cast_sub h.le, one_div,
      rpow_inv_le_iff_of_pos hx hy (by exact_mod_cast Nat.sub_pos_of_lt h), rpow_natCast]

/-- For `n ≠ 0` and nonnegative `x`, the `n`-th power of `x ^ (1 - 1/n)` is `x ^ (n - 1)`. -/
theorem rpow_one_sub_inv_natCast_pow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (x ^ (1 - (n : ℝ)⁻¹)) ^ n = x ^ (n - 1) := by
  first
  | rw [← rpow_mul_natCast hx, sub_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_mul,
      ← Nat.cast_pred (Nat.pos_of_ne_zero hn), rpow_natCast]

/-- A natural power `b ^ n` with `1 ≤ b` and `n ≤ δ r` is at most `(b ^ δ) ^ r`. This converts a
degree bound `n ≤ δ r` with a real factor `δ` into a bound by an `r`-th power. -/
theorem pow_le_rpow_pow_of_le_mul {b δ : ℝ} (hb : 1 ≤ b) {n r : ℕ} (hn : (n : ℝ) ≤ δ * r) :
    b ^ n ≤ (b ^ δ) ^ r := by
  first
  | rw [← rpow_mul_natCast (by linarith), ← rpow_natCast]
    exact rpow_le_rpow_of_exponent_le hb hn

/-- A positive power `x ↦ x ^ a` maps the open unit interval onto itself. -/
theorem image_rpow_Ioo_zero_one {a : ℝ} (ha : 0 < a) :
    (fun x : ℝ ↦ x ^ a) '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
  first
  | ext y
    refine ⟨?_, fun hy ↦ ⟨y ^ a⁻¹, ⟨rpow_pos_of_pos hy.1 _,
      rpow_lt_one hy.1.le hy.2 (inv_pos.mpr ha)⟩, rpow_inv_rpow hy.1.le ha.ne'⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨rpow_pos_of_pos hx.1 a, rpow_lt_one hx.1.le hx.2 ha⟩

/-- A real number whose natural powers grow at most polynomially is at most `1`: otherwise
`r ^ x = exp (log r * x)` with `log r > 0` outgrows every power of `1 + x`. -/
theorem le_one_of_forall_pow_le_mul_rpow {r C s : ℝ}
    (h : ∀ n : ℕ, r ^ n ≤ C * (1 + n) ^ s) : r ≤ 1 := by
  first
  | by_contra! h1
    have h0 : 0 < r := zero_lt_one.trans h1
    have hlim : Tendsto (fun n : ℕ ↦ C * r * ((1 + n) ^ s / r ^ (1 + (n : ℝ)))) atTop (𝓝 0) := by
      simpa [rpow_def_of_pos h0] using
        (((isLittleO_rpow_exp_pos_mul_atTop s (log_pos h1)).comp_tendsto
          (tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)).tendsto_div_nhds_zero
            ).const_mul (C * r)
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
    refine hn.not_ge ?_
    rw [rpow_add h0, rpow_one, rpow_natCast, mul_div_assoc', le_div_iff₀ (by positivity), one_mul]
    calc r * r ^ n ≤ r * (C * (1 + n) ^ s) := by gcongr; exact h n
      _ = C * r * (1 + n) ^ s := by ring

/-- If `0 ≤ A ≤ e^{-t}` and `0 ≤ c`, then `A ^ c ≤ e^{-c t}`. -/
theorem rpow_le_exp_neg_mul {A t c : ℝ} (hA : 0 ≤ A) (hAt : A ≤ exp (-t)) (hc : 0 ≤ c) :
    A ^ c ≤ exp (-(c * t)) := by
  first
  | refine (rpow_le_rpow hA hAt hc).trans_eq ?_
    rw [← exp_mul]
    ring_nf

end Real

/-- Real powers `g i ^ f i` with finitely supported exponents `f` have finite multiplicative
support. -/
theorem Function.HasFiniteSupport.hasFiniteMulSupport_fun_rpow {α : Type*} (g : α → ℝ)
    {f : α → ℝ} (hf : f.HasFiniteSupport) : (fun i ↦ g i ^ f i).HasFiniteMulSupport :=
  hf.subset fun i hi h ↦ hi (by simp [h])

/-- A positive real raised to a finitely supported sum is the product of the powers. -/
theorem Real.rpow_finsum_of_pos {α : Type*} {a : ℝ} (ha : 0 < a) {f : α → ℝ}
    (hf : f.HasFiniteSupport) : a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i := by
  first
  | rw [finsum_eq_sum f hf, finprod_eq_prod_of_mulSupport_subset _ (s := hf.toFinset)
      fun i hi ↦ hf.mem_toFinset.mpr fun h ↦ hi (by simp [h]), Real.rpow_sum_of_pos ha]
end -- closes the original EOF section from source line 76
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/SpecialFunctions/Pow/Real.lean -/

/- BEGIN SOURCE: TauCeti/Analysis/SpecialFunctions/Pow/NNReal.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Real powers in `ℝ≥0∞`

If `X ^ r ≤ C * X ^ (r - 1)` for a finite `X`, then `X ≤ C`: the factor `X ^ (r - 1)` cancels,
since it is neither `0` nor `∞` unless `X = 0`, in which case the conclusion is trivial. This is
the last step of every norming argument for `Lᵖ` norms, where `X` is a norm and `X ^ r` is its
pairing with the extremal function. In the same way, `m ≤ K * m ^ p` for a finite `m` and an
exponent `p < 1` gives `m ^ (1 - p) ≤ K`, which turns an estimate `μ(A) ≤ K μ(A) ^ (1/n)` into the
isoperimetric form `μ(A) ^ (1 - 1/n) ≤ K`.

For an exponent `p ∈ [0, 1]` the powers `x ^ p` and `x ^ (1 - p)` multiply back to `x`, with no
finiteness or positivity hypothesis on `x`. This is the case `s = t` of geometric interpolations
`t ^ p s ^ (1 - p)`, such as the distortion coefficient `τ_{K,N}^{(t)}(θ)` with `p = 1 / N`.
For distinct `x` and `y` such a weighted geometric mean `x ^ (1 - p) * y ^ p` still dominates
`min x y`, which compares the hypotheses of the Prékopa–Leindler inequality and of its version
for the minimum.

A nonpositive real power is antitone on `ℝ≥0∞`. Because `0 ^ z = ∞` for `z < 0`, no positivity
hypothesis is needed, unlike its `ℝ≥0` counterpart `NNReal.rpow_le_rpow_of_nonpos`; this is what
makes `ℝ≥0∞`-valued bounds on weakly singular integrands such as `|x - c| ^ (-1/2)` hold
everywhere, the pole included. In the same spirit, the inverse square root of a real `x` is at
most `‖x‖ₑ ^ (-1/2)`, with equality for `x > 0`. Two bounds on kernels `1 / √d` with `d` a
product of three linear factors follow: at infinity the kernel decays like `y ^ (-3/2)`, and near
three distinct poles the product of the factors `‖z - eᵢ‖ₑ ^ (-1/2)` is controlled by their sum,
since at most one of them can be large.

A real power `y ↦ y ^ d` on `ℝ≥0∞` is upper semicontinuous from the right uniformly on intervals:
for `ε ≠ 0`, every `y ∈ [x, z]` satisfies `y ^ d ≤ x ^ d + ε` once `z` is close enough to `x`.
For `d ≥ 0` this is monotonicity and continuity; for `d < 0` the power is antitone. Enlarging a
set slightly thus changes its `d`-dimensional diameter sum by little, as in Hausdorff measure
approximations by open covers.

For a base in `ℝ≥0` greater than one, power comparisons also express rational bounds and
closed intervals for a reciprocal radius parameter `α / r`.

## Main declarations

* `ENNReal.le_of_rpow_le_mul_rpow_sub_one`: `X ^ r ≤ C * X ^ (r - 1)` gives `X ≤ C` for a finite
  `X`.
* `ENNReal.rpow_one_sub_le_of_le_mul_rpow`: `m ≤ K * m ^ p` gives `m ^ (1 - p) ≤ K` for a finite
  `m` and `p < 1`.
* `ENNReal.rpow_mul_rpow_one_sub`: `x ^ p * x ^ (1 - p) = x` for `p ∈ [0, 1]`.
* `ENNReal.sq_rpow_one_half`: `(x ^ 2) ^ (1 / 2) = x`, with no hypothesis on `x`.
* `ENNReal.min_le_rpow_one_sub_mul_rpow`: `min x y ≤ x ^ (1 - p) * y ^ p` for `p ∈ [0, 1]`.
* `ENNReal.rpow_le_rpow_of_nonpos`: `x ≤ y` gives `y ^ z ≤ x ^ z` for `z ≤ 0`.
* `ENNReal.eventually_forall_mem_Icc_rpow_le_add`: `y ^ d ≤ x ^ d + ε` for `y ∈ [x, z]` and `z`
  near `x`.
* `ENNReal.exists_pos_forall_mem_Icc_rpow_le_add`: for `x < r`, a radius `η > 0` with
  `x + η ≤ r` and `y ^ d ≤ x ^ d + ε` for `y ∈ [x, x + η]`.
* `ENNReal.ofReal_inv_sqrt_le_enorm_rpow`: `ofReal (√x)⁻¹ ≤ ‖x‖ₑ ^ (-2⁻¹)` for every real `x`.
* `ENNReal.ofReal_inv_sqrt_le_of_pow_three_le`: `y³ ≤ 2 |d|` gives `1 / √d ≤ √2 y^(-3/2)`.
* `ENNReal.exists_enorm_sub_rpow_neg_half_mul_le`: for three distinct points `eᵢ`, the product of
  the `‖z - eᵢ‖ₑ ^ (-1/2)` is at most a constant times their sum.
* `NNReal.rpow_neg_mem_Icc_iff`: an interval of negative powers is equivalent to an interval
  for the reciprocal parameter `α / r`.
-/

public section

open scoped ENNReal NNReal Topology

namespace ENNReal

/-- If `X ^ r ≤ C * X ^ (r - 1)` for a finite `X`, then `X ≤ C`. -/
theorem le_of_rpow_le_mul_rpow_sub_one {X C : ℝ≥0∞} {r : ℝ} (hX : X ≠ ∞)
    (h : X ^ r ≤ C * X ^ (r - 1)) : X ≤ C := by
  first
  | rcases eq_or_ne X 0 with hX0 | hX0
    · simp [hX0]
    have hXr : X ^ r = X ^ (r - 1) * X := by
      conv_lhs => rw [show r = (r - 1) + 1 by ring]
      rw [rpow_add _ _ hX0 hX, rpow_one]
    have hpow0 : X ^ (r - 1) ≠ 0 := by simp [rpow_eq_zero_iff, hX0, hX]
    rw [hXr, mul_comm C] at h
    exact (ENNReal.mul_le_mul_iff_right hpow0 (rpow_ne_top_of_ne_zero hX0 hX)).1 h

/-- If `m ≤ K * m ^ p` for a finite `m` and an exponent `p < 1`, then `m ^ (1 - p) ≤ K`: the
factor `m ^ p` cancels. -/
theorem rpow_one_sub_le_of_le_mul_rpow {m K : ℝ≥0∞} {p : ℝ} (hp : p < 1) (hm : m ≠ ∞)
    (h : m ≤ K * m ^ p) : m ^ (1 - p) ≤ K := by
  first
  | rcases eq_or_ne m 0 with rfl | h0
    · rw [zero_rpow_of_pos (sub_pos.2 hp)]
      exact zero_le
    rwa [rpow_sub _ _ h0 hm, rpow_one, ENNReal.div_le_iff
      (rpow_pos (pos_iff_ne_zero.2 h0) hm).ne' (rpow_ne_top_of_ne_zero h0 hm)]

/-- For `p ∈ [0, 1]`, the powers `x ^ p` and `x ^ (1 - p)` multiply back to `x`. -/
theorem rpow_mul_rpow_one_sub (x : ℝ≥0∞) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    x ^ p * x ^ (1 - p) = x := by
  first
  | rw [← rpow_add_of_nonneg _ _ hp₀ (sub_nonneg.2 hp₁), add_sub_cancel, rpow_one]

/-- The square root of a square in `ℝ≥0∞`, written as a real power: `(x ^ 2) ^ (1 / 2) = x`. -/
theorem sq_rpow_one_half (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  first
  | rw [← rpow_two, ← rpow_mul]
    norm_num

/-- For `p ∈ [0, 1]`, the weighted geometric mean `x ^ (1 - p) * y ^ p` dominates `min x y`. -/
theorem min_le_rpow_one_sub_mul_rpow (x y : ℝ≥0∞) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    min x y ≤ x ^ (1 - p) * y ^ p :=
  calc min x y = min x y ^ (1 - p) * min x y ^ p := by
        first
        | rw [mul_comm, rpow_mul_rpow_one_sub _ hp₀ hp₁]
    _ ≤ x ^ (1 - p) * y ^ p := mul_le_mul' (rpow_le_rpow (min_le_left _ _) (sub_nonneg.2 hp₁))
        (rpow_le_rpow (min_le_right _ _) hp₀)

/-- A nonpositive real power is antitone on `ℝ≥0∞`: `x ≤ y` gives `y ^ z ≤ x ^ z` for `z ≤ 0`. -/
theorem rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} {z : ℝ} (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  first
  | obtain ⟨w, hw, rfl⟩ : ∃ w, 0 ≤ w ∧ z = -w := ⟨-z, neg_nonneg.mpr hz, (neg_neg z).symm⟩
    rw [rpow_neg, rpow_neg]
    exact ENNReal.inv_le_inv.mpr (rpow_le_rpow hxy hw)

/-- For `ε ≠ 0`, every `y ∈ [x, z]` satisfies `y ^ d ≤ x ^ d + ε` once `z` is close enough to
`x`. -/
theorem eventually_forall_mem_Icc_rpow_le_add (x : ℝ≥0∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) (d : ℝ) :
    ∀ᶠ z in 𝓝 x, ∀ y ∈ Set.Icc x z, y ^ d ≤ x ^ d + ε := by
  first
  | rcases le_or_gt 0 d with hd | hd
    · rcases eq_or_ne (x ^ d) ∞ with hx | hx
      · exact Filter.Eventually.of_forall fun _ _ _ ↦ by simp [hx]
      filter_upwards [(continuous_rpow_const.tendsto x).eventually_lt_const
        (ENNReal.lt_add_right hx hε)] with z hz y hy
      exact (rpow_le_rpow hy.2 hd).trans hz.le
    · exact Filter.Eventually.of_forall fun _ y hy ↦
        (rpow_le_rpow_of_nonpos hy.1 hd.le).trans le_self_add

/-- For `x < r` and `ε ≠ 0` there is `η > 0` with `x + η ≤ r` such that every `y ∈ [x, x + η]`
satisfies `y ^ d ≤ x ^ d + ε`. -/
theorem exists_pos_forall_mem_Icc_rpow_le_add {x r ε : ℝ≥0∞} (hxr : x < r) (hε : ε ≠ 0) (d : ℝ) :
    ∃ η : ℝ≥0, 0 < η ∧ x + η ≤ r ∧ ∀ y ∈ Set.Icc x (x + η), y ^ d ≤ x ^ d + ε := by
  first
  | have hg : Filter.Tendsto (fun η : ℝ≥0 ↦ x + η) (𝓝 0) (𝓝 x) := by
      have hc : Continuous fun η : ℝ≥0 ↦ x + η := continuous_const.add continuous_coe
      simpa using hc.tendsto 0
    obtain ⟨η, ⟨hηr, hηd⟩, hη0⟩ := (((hg.eventually_lt_const hxr).and
      (hg.eventually (eventually_forall_mem_Icc_rpow_le_add x hε d))).filter_mono
      nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ≥0))
    exact ⟨η, hη0, hηr.le, hηd⟩

/-- The inverse square root of a real `x` is at most `‖x‖ₑ ^ (-1/2)`, as a value in `ℝ≥0∞`. The two
agree for `x > 0`; for `x ≤ 0` the left side is `0`. -/
theorem ofReal_inv_sqrt_le_enorm_rpow (x : ℝ) : ENNReal.ofReal (√x)⁻¹ ≤ ‖x‖ₑ ^ (-2⁻¹ : ℝ) := by
  first
  | rcases le_or_gt x 0 with hx | hx
    · simp [Real.sqrt_eq_zero'.mpr hx]
    rw [Real.inv_sqrt_eq_rpow, ← ofReal_rpow_of_pos hx, Real.enorm_of_nonneg hx.le]

/-- If `y > 0` and `y³ ≤ 2 |d|`, then `1 / √d ≤ √2 y^(-3/2)`, as values in `ℝ≥0∞`. This is the
decay at infinity of a kernel `1 / √d(x)` for a cubic `d` with leading coefficient `4`, with
`y = 1 + |x|`. -/
theorem ofReal_inv_sqrt_le_of_pow_three_le {d y : ℝ} (hy : 0 < y) (h : y ^ 3 ≤ 2 * |d|) :
    ENNReal.ofReal (√d)⁻¹ ≤ ENNReal.ofReal √2 * ENNReal.ofReal (y ^ (-(3 / 2 : ℝ))) := by
  first
  | rcases le_or_gt d 0 with hd | hd
    · simp [Real.sqrt_eq_zero'.mpr hd]
    rw [abs_of_pos hd] at h
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hy3 : 0 < y ^ 3 / 2 := by positivity
    calc (√d)⁻¹ ≤ (√(y ^ 3 / 2))⁻¹ :=
          inv_anti₀ (Real.sqrt_pos.mpr hy3) (Real.sqrt_le_sqrt (by linarith))
      _ = √2 * (y ^ 3) ^ (-2⁻¹ : ℝ) := by
          rw [Real.sqrt_div' _ zero_le_two, inv_div, div_eq_mul_inv, Real.inv_sqrt_eq_rpow]
      _ = √2 * y ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast_mul hy.le]; norm_num

/-- For three distinct points `e₁, e₂, e₃` of a normed additive group, at most one of the factors
`‖z - eᵢ‖ₑ ^ (-1/2)` is large: the product of the three is at most a constant times their sum. -/
theorem exists_enorm_sub_rpow_neg_half_mul_le {E : Type*} [NormedAddGroup E] {e₁ e₂ e₃ : E}
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ z : E,
      ‖z - e₁‖ₑ ^ (-2⁻¹ : ℝ) * ‖z - e₂‖ₑ ^ (-2⁻¹ : ℝ) * ‖z - e₃‖ₑ ^ (-2⁻¹ : ℝ) ≤
        K * (‖z - e₁‖ₑ ^ (-2⁻¹ : ℝ) + ‖z - e₂‖ₑ ^ (-2⁻¹ : ℝ) + ‖z - e₃‖ₑ ^ (-2⁻¹ : ℝ)) := by
  first
  | set δ := min (min ‖e₁ - e₂‖ ‖e₁ - e₃‖) ‖e₂ - e₃‖
    have hδ : 0 < δ := lt_min (lt_min (norm_sub_pos_iff.mpr h₁₂) (norm_sub_pos_iff.mpr h₁₃))
      (norm_sub_pos_iff.mpr h₂₃)
    set k := ENNReal.ofReal (δ / 2) ^ (-2⁻¹ : ℝ)
    have hk : k ≠ ∞ := by simp [k, ENNReal.rpow_eq_top_iff, hδ]
    -- a point at distance at least `δ / 2` contributes a factor at most `k`
    have far {z e : E} (h : δ / 2 ≤ ‖z - e‖) : ‖z - e‖ₑ ^ (-2⁻¹ : ℝ) ≤ k :=
      ENNReal.rpow_le_rpow_of_nonpos (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h)
        (by norm_num)
    -- no point is within `δ / 2` of two of the `eᵢ`
    have near {z a b : E} (hab : δ ≤ ‖a - b‖) : δ / 2 ≤ ‖z - a‖ ∨ δ / 2 ≤ ‖z - b‖ := by
      by_contra! h
      have := norm_sub_le_norm_sub_add_norm_sub a z b
      rw [norm_sub_rev a z] at this
      linarith
    refine ⟨k * k, ENNReal.mul_ne_top hk hk, fun z ↦ ?_⟩
    set h₁ := ‖z - e₁‖ₑ ^ (-2⁻¹ : ℝ)
    set h₂ := ‖z - e₂‖ₑ ^ (-2⁻¹ : ℝ)
    set h₃ := ‖z - e₃‖ₑ ^ (-2⁻¹ : ℝ)
    have hδ₁₂ : δ ≤ ‖e₁ - e₂‖ := (min_le_left _ _).trans (min_le_left _ _)
    have hδ₁₃ : δ ≤ ‖e₁ - e₃‖ := (min_le_left _ _).trans (min_le_right _ _)
    have hδ₂₃ : δ ≤ ‖e₂ - e₃‖ := min_le_right _ _
    by_cases f₁ : δ / 2 ≤ ‖z - e₁‖
    · by_cases f₂ : δ / 2 ≤ ‖z - e₂‖
      · calc h₁ * h₂ * h₃ ≤ k * k * h₃ := by gcongr <;> exact far ‹_›
          _ ≤ k * k * (h₁ + h₂ + h₃) := by gcongr; exact le_add_self
      · have f₃ := (near hδ₂₃).resolve_left f₂
        calc h₁ * h₂ * h₃ ≤ k * h₂ * k := by gcongr <;> exact far ‹_›
          _ = k * k * h₂ := by ring
          _ ≤ k * k * (h₁ + h₂ + h₃) := by gcongr; exact le_add_self.trans le_self_add
    · have f₂ := (near hδ₁₂).resolve_left f₁
      have f₃ := (near hδ₁₃).resolve_left f₁
      calc h₁ * h₂ * h₃ ≤ h₁ * k * k := by gcongr <;> exact far ‹_›
        _ = k * k * h₁ := by ring
        _ ≤ k * k * (h₁ + h₂ + h₃) := by gcongr; exact le_self_add.trans le_self_add

end ENNReal

namespace NNReal

/-- For a base greater than one, real powers are ordered exactly by their exponents. -/
theorem rpow_le_rpow_iff_of_one_lt {b : ℝ≥0} (hb : 1 < b) {x y : ℝ} :
    b ^ x ≤ b ^ y ↔ x ≤ y := by
  first
  | constructor
    · contrapose!
      exact rpow_lt_rpow_of_exponent_lt hb
    · exact rpow_le_rpow_of_exponent_le hb.le

/-- **Reciprocal radius interval dictionary.** For a base `c > 1`, the interval
`c ^ (-α/a) ≤ c ^ (-r) ≤ c ^ (-α/b)` is equivalent to `a ≤ α / r ≤ b` when
`r`, `a`, and `b` are positive. -/
theorem rpow_neg_mem_Icc_iff {c : ℝ≥0} (hc : 1 < c) (α r a b : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    c ^ (-r) ∈ Set.Icc (c ^ (-α / a)) (c ^ (-α / b)) ↔
      α / r ∈ Set.Icc a b := by
  first
  | simp only [Set.mem_Icc]
    rw [rpow_le_rpow_iff_of_one_lt hc, rpow_le_rpow_iff_of_one_lt hc]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor
      · apply (le_div_iff₀ hr).2
        have := (div_le_iff₀ ha).1 h₁
        nlinarith
      · apply (div_le_iff₀ hr).2
        have := (le_div_iff₀ hb).1 h₂
        nlinarith
    · rintro ⟨h₁, h₂⟩
      constructor
      · have := (le_div_iff₀ hr).1 h₁
        exact (div_le_iff₀ ha).2 (by nlinarith)
      · have := (div_le_iff₀ hr).1 h₂
        exact (le_div_iff₀ hb).2 (by nlinarith)

/-- A rational lower bound on the ratio `α / r`, expressed as a comparison of powers.

For `r > 0`, the inequality `(b ^ (-α)) ^ q.den ≤ (b ^ (-r)) ^ q.num` is equivalent to
`q ≤ α / r`; the base is arbitrary above one. -/
theorem rpow_num_den_le_iff {b : ℝ≥0} (hb : 1 < b) (r : ℝ) (hr : 0 < r)
    (α : ℝ) (q : ℚ≥0) :
    (b ^ (-α)) ^ q.den ≤ (b ^ (-r)) ^ q.num ↔ (q : ℝ) ≤ α / r := by
  first
  | rw [← rpow_mul_natCast, ← rpow_mul_natCast, rpow_le_rpow_iff_of_one_lt hb,
      NNRat.cast_def, div_le_div_iff₀ (by exact_mod_cast q.den_pos) hr]
    constructor <;> intro h <;> nlinarith

/-- A rational upper bound on the ratio `α / r`, expressed as a comparison of powers.

For `r > 0`, the inequality `(b ^ (-r)) ^ q.num ≤ (b ^ (-α)) ^ q.den` is equivalent to
`α / r ≤ q`; the base is arbitrary above one. -/
theorem rpow_den_num_le_iff {b : ℝ≥0} (hb : 1 < b) (r : ℝ) (hr : 0 < r)
    (α : ℝ) (q : ℚ≥0) :
    (b ^ (-r)) ^ q.num ≤ (b ^ (-α)) ^ q.den ↔ α / r ≤ (q : ℝ) := by
  first
  | rw [← rpow_mul_natCast, ← rpow_mul_natCast, rpow_le_rpow_iff_of_one_lt hb,
      NNRat.cast_def, div_le_div_iff₀ hr (by exact_mod_cast q.den_pos)]
    constructor <;> intro h <;> nlinarith

end NNReal
end -- closes the original EOF section from source line 69
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Analysis/SpecialFunctions/Pow/NNReal.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Real.lean -/
section
/-
Copyright (c) 2026 Weiyi Wang, Jonathan Ho, The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Jonathan Ho, The Tau Ceti contributors
-/


/-!
# One-dimensional Brunn–Minkowski inequality

For two nonempty Lebesgue-measurable subsets of the real line, the outer volume of their
Minkowski sum is at least the sum of their volumes. No measurability of the Minkowski sum
is required, and the inequality includes zero and infinite volumes. Nonemptiness is essential:
adding the empty set to a positive-volume set gives the empty set.

The compact-set and Borel-set arguments are adapted from Weiyi Wang and Jonathan Ho's
[Mathlib PR #44802](https://github.com/leanprover-community/mathlib4/pull/44802), originating
in [Jonathan Ho's isoperimetric formalization](https://github.com/hojonathanho/isoperimetric).
The proof translates the compact sets so that their extreme points meet at zero; the two
translates have null intersection and their union lies in their Minkowski sum. Inner
regularity then gives the Borel-set inequality. Measurable subsets with the same volume
extend it to Lebesgue-measurable sets. The weighted form uses Mathlib's `Measure.addHaar_smul`.

This is the one-dimensional set inequality used in the Prékopa–Leindler argument.

## References

* Terence Tao, [The Brunn–Minkowski inequality for nilpotent groups]
  (https://terrytao.wordpress.com/2011/09/16/the-brunn-minkowski-inequality-for-nilpotent-groups/),
  for the one-dimensional set argument and its role in the functional inequality.
-/

public section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace TauCeti.Real

/-- One-dimensional **Brunn–Minkowski theorem** for compact sets. -/
theorem volume_add_volume_le_of_isCompact {A B : Set ℝ} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hBn : B.Nonempty) (hBc : IsCompact B) : volume A + volume B ≤ volume (A + B) :=
  calc
    _ = volume (A + {-sSup A}) + volume (B + {-sInf B}) := by simp
    _ = volume ((A + {-sSup A}) ∪ (B + {-sInf B})) +
        volume ((A + {-sSup A}) ∩ (B + {-sInf B})) := by
      first
      | rw [measure_union_add_inter _ (hBc.add isCompact_singleton).measurableSet]
    _ ≤ volume ((A + {-sSup A}) ∪ (B + {-sInf B})) := by
      first
      | suffices (A + {-sSup A}) ∩ (B + {-sInf B}) ⊆ {0} by
          grw [this]
          simp
        refine fun x ⟨hA, hB⟩ ↦ le_antisymm ?_ ?_
        · exact nonpos_of_add_le_left <| le_csSup hAc.bddAbove <| by simpa using hA
        · exact nonneg_of_le_add_left <| csInf_le hBc.bddBelow <| by simpa using hB
    _ ≤ volume ((A + {-sSup A}) + (B + {-sInf B})) := by
      first
      | refine measure_mono <| Set.union_subset_iff.mpr ⟨?_, ?_⟩
        · exact Set.subset_add_left _ (by simpa using hBc.sInf_mem hBn)
        · exact Set.subset_add_right _ (by simpa using hAc.sSup_mem hAn)
    _ = _ := by
      first
      | rw [add_add_add_comm]
        simp

/-- One-dimensional **Brunn–Minkowski theorem** for Borel sets, with outer volume on the
right. The sum need not be Borel, and the input sets may have infinite volume. -/
theorem volume_add_volume_le {A B : Set ℝ} (hAn : A.Nonempty) (hAm : MeasurableSet A)
    (hBn : B.Nonempty) (hBm : MeasurableSet B) : volume A + volume B ≤ volume (A + B) := by
  first
  | obtain ⟨a, ha⟩ := hAn
    obtain ⟨b, hb⟩ := hBn
    by_cases hA : volume A = ∞
    · trans volume (A + {b})
      · simp [hA]
      · gcongr
        simpa using hb
    by_cases hB : volume B = ∞
    · trans volume ({a} + B)
      · simp [hB]
      · gcongr
        simpa using ha
    calc
      _ = (⨆ (K) (_ : K ⊆ A) (_ : IsCompact K), volume K) +
          (⨆ (K) (_ : K ⊆ B) (_ : IsCompact K), volume K) := by
        rw [hAm.measure_eq_iSup_isCompact_of_ne_top hA, hBm.measure_eq_iSup_isCompact_of_ne_top hB]
      _ ≤ ⨆ (K) (_ : K ⊆ A) (_ : IsCompact K) (L) (_ : L ⊆ B) (_ : IsCompact L),
          volume K + volume L := by
        simp_rw [iSup_and']
        refine ENNReal.biSup_add_biSup_le' ⟨∅, by simp⟩ ⟨∅, by simp⟩ fun K hK L hL ↦ ?_
        aesop (add safe [le_iSup_of_le])
      _ ≤ _ := by
        refine iSup₂_le fun K hKA ↦ iSup₂_le fun hK L ↦ iSup₂_le fun hLB hL ↦ ?_
        trans volume (K ∪ {a}) + volume (L ∪ {b})
        · gcongr <;> simp
        grw [volume_add_volume_le_of_isCompact (by simp) (hK.union isCompact_singleton)
          (by simp) (hL.union isCompact_singleton), Set.union_subset hKA (by simpa using ha),
          Set.union_subset hLB (by simpa using hb)]

/-- One-dimensional **Brunn–Minkowski theorem** for Lebesgue-measurable sets, with outer
volume on the right. No finiteness or measurability of the sum is assumed. -/
theorem volume_add_volume_le_of_nullMeasurableSet {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) : volume A + volume B ≤ volume (A + B) := by
  first
  | obtain ⟨a, ha⟩ := hAn
    obtain ⟨b, hb⟩ := hBn
    obtain ⟨K, hKA, hKm, hK⟩ := hAm.exists_measurable_subset_ae_eq
    obtain ⟨L, hLB, hLm, hL⟩ := hBm.exists_measurable_subset_ae_eq
    -- Adjoin points to retain nonemptiness even when a measurable representative is empty.
    have hKvol : volume (K ∪ {a}) = volume A := by
      simpa using measure_congr (hK.union (ae_eq_empty.2 (measure_singleton a)))
    have hLvol : volume (L ∪ {b}) = volume B := by
      simpa using measure_congr (hL.union (ae_eq_empty.2 (measure_singleton b)))
    rw [← hKvol, ← hLvol]
    exact (volume_add_volume_le (by simp) (hKm.union (measurableSet_singleton a))
      (by simp) (hLm.union (measurableSet_singleton b))).trans
      (measure_mono (add_subset_add (union_subset hKA (by simpa using ha))
        (union_subset hLB (by simpa using hb))))

/-- Weighted one-dimensional **Brunn–Minkowski theorem** for Lebesgue-measurable sets.
The coefficients may vanish; extended multiplication uses `0 * ∞ = 0`. Taking
`c = 1 - θ` and `d = θ` gives the convex-combination form for every `θ ∈ [0,1]`. -/
theorem mul_volume_add_mul_volume_le {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal c * volume A + ENNReal.ofReal d * volume B ≤
      volume (c • A + d • B) := by
  first
  | have h := volume_add_volume_le_of_nullMeasurableSet hAn.smul_set
      (Measure.NullMeasurableSet.const_smul hAm c) hBn.smul_set
      (Measure.NullMeasurableSet.const_smul hBm d)
    simpa [Measure.addHaar_smul, abs_of_nonneg hc, abs_of_nonneg hd] using h

/-- Real-valued one-dimensional Brunn–Minkowski inequality. Finiteness of the outer
volume of the sum implies finiteness of both input volumes. -/
theorem volume_real_add_volume_real_le {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) (hfin : volume (A + B) ≠ ∞) :
    volume.real A + volume.real B ≤ volume.real (A + B) := by
  first
  | have h := volume_add_volume_le_of_nullMeasurableSet hAn hAm hBn hBm
    have hA : volume A ≠ ∞ := ne_top_of_le_ne_top hfin ((le_self_add).trans h)
    have hB : volume B ≠ ∞ := ne_top_of_le_ne_top hfin ((le_add_self).trans h)
    simpa [measureReal_def, ENNReal.toReal_add hA hB] using ENNReal.toReal_mono hfin h

/-- Real-valued weighted one-dimensional Brunn–Minkowski inequality. The outer volume
of the weighted sum must be finite; a zero coefficient still permits an infinite input volume. -/
theorem mul_volume_real_add_mul_volume_real_le {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfin : volume (c • A + d • B) ≠ ∞) :
    c * volume.real A + d * volume.real B ≤ volume.real (c • A + d • B) := by
  first
  | have h := mul_volume_add_mul_volume_le hAn hAm hBn hBm hc hd
    have hA : ENNReal.ofReal c * volume A ≠ ∞ :=
      ne_top_of_le_ne_top hfin (le_self_add.trans h)
    have hB : ENNReal.ofReal d * volume B ≠ ∞ :=
      ne_top_of_le_ne_top hfin (le_add_self.trans h)
    simpa [measureReal_def, ENNReal.toReal_add hA hB, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd] using ENNReal.toReal_mono hfin h

end TauCeti.Real
end -- closes the original EOF section from source line 35
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Real.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: weighted AM-GM, the minimum below a geometric mean, the layer-cake formula in
-- `ℝ≥0∞` and one-dimensional Brunn–Minkowski.

/-!
# The Prékopa–Leindler inequality

For a measure on a real module, `Measure.HasPrekopaLeindler θ` records the weighted
Prékopa–Leindler inequality for measurable `ℝ≥0∞`-valued functions.  Its pointwise hypothesis
is imposed on the chosen measurable representatives, rather than only almost everywhere, so it is
stable under taking sections.

The property tensorizes: if two measures have the Prékopa–Leindler property at the same
weight, then their product measure has it as well.  Tonelli's theorem first applies the inequality
in the second variable and then applies it to the resulting marginal integrals in the first
variable, so only the second factor needs to be s-finite.  Iterating over the coordinates, a
finite product of σ-finite measures with the property has it as well.

The property is also transported by measure-preserving maps which preserve the weighted affine
combination.  This makes tensorization usable after changing linear coordinates or projecting to a
marginal.

Lebesgue measure on `ℝ` has the property for every weight `0 ≤ θ ≤ 1`; the endpoints are
monotonicity of the integral.  The interior case rests on a version of the inequality for the
minimum: if `f` and `g` have the same supremum and `min (f x) (g y) ≤ h (c * x + d * y)`, then
each superlevel set of `h` contains the weighted Minkowski sum of those of `f` and `g`, which are
nonempty below the common supremum, so one-dimensional Brunn–Minkowski and the layer-cake formula
give `c ∫ f + d ∫ g ≤ ∫ h`.  Normalizing the suprema of bounded `f` and `g` to one and applying
the weighted AM-GM inequality gives Prékopa–Leindler, and truncation removes the boundedness.
Tensorization then gives the inequality for Lebesgue measure on `ι → ℝ`, and linear isometries
transport it to every finite-dimensional real inner product space.

Applied once in the second variable, the inequality says that a marginal
`x ↦ ∫⁻ y, f (x, y) ∂ν` of a log-concave function `f` is log-concave. For the indicator of a
convex set this is Brunn's principle in log-concave form: the measures of the parallel slices of
a convex set form a log-concave function, so for a symmetric convex set the central slice is the
largest. This is the form in which Vaaler's cube-slicing theorem uses the inequality.

## Main results

* `MeasureTheory.Measure.HasPrekopaLeindler`: the measurable extended-integral inequality.
* `MeasureTheory.Measure.HasPrekopaLeindler.prod`: tensorization over product measures.
* `MeasureTheory.Measure.HasPrekopaLeindler.pi`: tensorization over finite products.
* `MeasureTheory.Measure.HasPrekopaLeindler.map`: transport by a measure-preserving affine map.
* `MeasureTheory.Measure.HasPrekopaLeindler.withDensity`,
  `MeasureTheory.Measure.HasPrekopaLeindler.restrict`: log-concave densities and restriction to
  convex sets preserve the property.
* `TauCeti.Real.mul_lintegral_add_mul_lintegral_le`: the inequality for the minimum on `ℝ`.
* `TauCeti.Real.hasPrekopaLeindler_volume`: the **Prékopa–Leindler inequality** on `ℝ`.
* `TauCeti.hasPrekopaLeindler_volume_pi`, `TauCeti.hasPrekopaLeindler_volume`: the inequality on
  `ι → ℝ` and on finite-dimensional real inner product spaces.
* `TauCeti.LogConcave.lintegral_prod_right`, `TauCeti.LogConcave.setLIntegral_prod_right`:
  marginals of log-concave functions are log-concave.
* `Convex.logConcave_measure_preimage_prodMk`: the slice measures of a convex set are
  log-concave.
* `Convex.measure_preimage_prodMk_le_measure_preimage_prodMk_zero`: the central slice of a
  symmetric convex set is the largest.

## References

* A. Prékopa, *Logarithmic concave measures with application to stochastic programming*, Acta
  Scientiarum Mathematicarum **32** (1971), 301–316.
* L. Leindler, *On a certain converse of Hölder's inequality II*, Acta Scientiarum Mathematicarum
  **33** (1972), 217–223.
* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., AMS, 2001, Section 4.3.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for the one-dimensional level-set argument.
* Terence Tao, [The Brunn–Minkowski inequality for nilpotent groups]
  (https://terrytao.wordpress.com/2011/09/16/the-brunn-minkowski-inequality-for-nilpotent-groups/).
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Lemma C.3.4, for marginals of log-concave functions. The statements and proofs of the marginal
  results are adapted from the Apache-2.0 formalization in `rwst/Subspace-Theorems` (files
  `ArithmeticHeights/LogConcave.lean` and `ArithmeticHeights/CubeSlicing.lean`), by Ralf Stephan.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace MeasureTheory.Measure

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- A measure has the **Prékopa–Leindler property** at weight `θ` if every three measurable
nonnegative extended-valued functions satisfying the pointwise weighted geometric-mean bound also
satisfy the corresponding bound on their integrals.

The pointwise bound is deliberately imposed on the supplied measurable representatives.  This is
the form which tensorizes without choosing new representatives on individual sections. -/
def HasPrekopaLeindler (mu : Measure E) (theta : ℝ) : Prop :=
  ∀ {f g h : E → ENNReal}, Measurable f → Measurable g → Measurable h →
    (∀ x y, (f x).rpow (1 - theta) * (g y).rpow theta ≤
      h ((1 - theta) • x + theta • y)) →
    (∫⁻ x, f x ∂mu).rpow (1 - theta) * (∫⁻ x, g x ∂mu).rpow theta ≤
      ∫⁻ x, h x ∂mu

/-- The Prékopa–Leindler property unfolded into its measurable-function formulation. -/
theorem hasPrekopaLeindler_def (mu : Measure E) (theta : ℝ) :
    mu.HasPrekopaLeindler theta ↔
      ∀ {f g h : E → ENNReal}, Measurable f → Measurable g → Measurable h →
        (∀ x y, (f x).rpow (1 - theta) * (g y).rpow theta ≤
          h ((1 - theta) • x + theta • y)) →
        (∫⁻ x, f x ∂mu).rpow (1 - theta) * (∫⁻ x, g x ∂mu).rpow theta ≤
          ∫⁻ x, h x ∂mu :=
  Iff.rfl

/-- A Dirac mass has the Prékopa–Leindler property at every weight. -/
theorem hasPrekopaLeindler_dirac (a : E) (theta : ℝ) :
    (Measure.dirac a).HasPrekopaLeindler theta := by
  first
  | intro f g h hf hg hh hfg
    rw [lintegral_dirac' _ hf, lintegral_dirac' _ hg, lintegral_dirac' _ hh]
    simpa only [← add_smul, sub_add_cancel, one_smul] using hfg a a

/-- Transport the Prékopa–Leindler property through a measure-preserving map
which preserves the weighted affine combination. -/
theorem HasPrekopaLeindler.map {mu : Measure E} {nu : Measure F} {theta : ℝ}
    (hmu : mu.HasPrekopaLeindler theta) (e : E → F) (he : MeasurePreserving e mu nu)
    (haffine : ∀ x y, e ((1 - theta) • x + theta • y) =
      (1 - theta) • e x + theta • e y) :
    nu.HasPrekopaLeindler theta := by
  first
  | intro f g h hf hg hh hfg
    have hbound := hmu (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable)
      fun x y => by simpa only [Function.comp_apply, haffine] using hfg (e x) (e y)
    simpa only [Function.comp_apply, he.lintegral_comp hf, he.lintegral_comp hg,
      he.lintegral_comp hh] using hbound

/-- **Tensorization of Prékopa–Leindler.** If `mu` and `nu` satisfy the inequality at the same
weight, then so does their product measure. -/
theorem HasPrekopaLeindler.prod {mu : Measure E} {nu : Measure F} [SFinite nu]
    {theta : ℝ} (hmu : mu.HasPrekopaLeindler theta) (hnu : nu.HasPrekopaLeindler theta) :
    (mu.prod nu).HasPrekopaLeindler theta := by
  first
  | intro f g h hf hg hh hfg
    let fMarginal : E → ENNReal := fun x => ∫⁻ y, f (x, y) ∂nu
    let gMarginal : E → ENNReal := fun x => ∫⁻ y, g (x, y) ∂nu
    let hMarginal : E → ENNReal := fun x => ∫⁻ y, h (x, y) ∂nu
    have hfMarginal : Measurable fMarginal := hf.lintegral_prod_right'
    have hgMarginal : Measurable gMarginal := hg.lintegral_prod_right'
    have hhMarginal : Measurable hMarginal := hh.lintegral_prod_right'
    have hmarginal (x y : E) :
        (fMarginal x).rpow (1 - theta) * (gMarginal y).rpow theta ≤
          hMarginal ((1 - theta) • x + theta • y) := by
      apply hnu (hf.comp (measurable_const.prodMk measurable_id))
        (hg.comp (measurable_const.prodMk measurable_id))
        (hh.comp (measurable_const.prodMk measurable_id))
      intro a b
      simpa only [Function.comp_apply, id_eq, Prod.smul_mk, Prod.add_def] using hfg (x, a) (y, b)
    have hresult := hmu hfMarginal hgMarginal hhMarginal hmarginal
    rw [lintegral_prod f hf.aemeasurable, lintegral_prod g hg.aemeasurable,
      lintegral_prod h hh.aemeasurable]
    exact hresult

/-- Pull the Prékopa–Leindler property back along a measure-preserving measurable equivalence
whose forward map preserves the weighted affine combination. -/
theorem HasPrekopaLeindler.of_measurePreserving {mu : Measure E} {nu : Measure F} {theta : ℝ}
    (hnu : nu.HasPrekopaLeindler theta) (e : E ≃ᵐ F) (he : MeasurePreserving e mu nu)
    (haffine : ∀ x y, e ((1 - theta) • x + theta • y) = (1 - theta) • e x + theta • e y) :
    mu.HasPrekopaLeindler theta :=
  hnu.map e.symm he.symm fun x y ↦ e.injective <| by
    simp only [haffine, MeasurableEquiv.apply_symm_apply]

/-- **Tensorization of Prékopa–Leindler over finite products.** If σ-finite measures `μ i`
on finitely many real modules all satisfy the inequality at the same weight, then so does their
product measure. -/
theorem HasPrekopaLeindler.pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, AddCommMonoid (α i)] [∀ i, Module ℝ (α i)]
    {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)] {theta : ℝ}
    (h : ∀ i, (μ i).HasPrekopaLeindler theta) :
    (Measure.pi μ).HasPrekopaLeindler theta := by
  first
    -- First treat the index types `Fin n`, splitting off the zeroth coordinate inductively.
  | have hfin : ∀ (n : ℕ) (α : Fin n → Type _) [∀ i, MeasurableSpace (α i)]
        [∀ i, AddCommMonoid (α i)] [∀ i, Module ℝ (α i)] (μ : ∀ i, Measure (α i))
        [∀ i, SigmaFinite (μ i)], (∀ i, (μ i).HasPrekopaLeindler theta) →
        (Measure.pi μ).HasPrekopaLeindler theta := by
      intro n
      induction n with
      | zero =>
        intro α _ _ _ μ _ _
        rw [Measure.pi_of_empty μ isEmptyElim]
        exact hasPrekopaLeindler_dirac _ _
      | succ n ih =>
        intro α _ _ _ μ _ h f g k hf hg hk hfgk
        refine HasPrekopaLeindler.of_measurePreserving
          (HasPrekopaLeindler.prod (h 0) (ih _ (fun j ↦ μ (Fin.succAbove 0 j)) fun j ↦ h _))
          (MeasurableEquiv.piFinSuccAbove α 0) (measurePreserving_piFinSuccAbove μ 0)
          (fun x y ↦ ?_) hf hg hk hfgk
        -- Both components of `piFinSuccAbove` are coordinate evaluations, hence linear.
        ext j <;> rfl
    intro f g k hf hg hk hfgk
    let e := Fintype.equivFin ι
    refine HasPrekopaLeindler.map (hfin _ (fun j ↦ α (e.symm j)) (fun j ↦ μ (e.symm j)) fun j ↦ h _)
      (MeasurableEquiv.piCongrLeft α e.symm) (measurePreserving_piCongrLeft μ e.symm)
      (fun x y ↦ ?_) hf hg hk hfgk
    ext i
    obtain ⟨j, rfl⟩ := e.symm.surjective i
    simp [MeasurableEquiv.piCongrLeft_apply_apply]

/-- **A log-concave density preserves Prékopa–Leindler.** If `mu` has the Prékopa–Leindler
property at a weight `0 ≤ θ ≤ 1` and `φ` is measurable and log-concave, then `mu.withDensity φ`
has it as well. For instance, the Gaussian density `exp (-π ‖x‖ ^ 2)` is log-concave. -/
theorem HasPrekopaLeindler.withDensity {mu : Measure E} {theta : ℝ}
    (hmu : mu.HasPrekopaLeindler theta) (hθ₀ : 0 ≤ theta) (hθ₁ : theta ≤ 1) {φ : E → ℝ≥0∞}
    (hφ : Measurable φ) (hlc : TauCeti.LogConcave φ) :
    (mu.withDensity φ).HasPrekopaLeindler theta := by
  first
  | intro f g h hf hg hh hfg
    simp only [lintegral_withDensity_eq_lintegral_mul _ hφ hf,
      lintegral_withDensity_eq_lintegral_mul _ hφ hg, lintegral_withDensity_eq_lintegral_mul _ hφ hh]
    refine hmu (hφ.mul hf) (hφ.mul hg) (hφ.mul hh) fun x y ↦ ?_
    have h1θ : 0 ≤ 1 - theta := by linarith
    simp only [Pi.mul_apply, ENNReal.rpow_eq_pow] at hfg ⊢
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ, ENNReal.mul_rpow_of_nonneg _ _ hθ₀]
    calc φ x ^ (1 - theta) * f x ^ (1 - theta) * (φ y ^ theta * g y ^ theta)
        = φ x ^ (1 - theta) * φ y ^ theta * (f x ^ (1 - theta) * g y ^ theta) := by ring
      _ ≤ _ := mul_le_mul' (hlc.rpow_mul_rpow_le h1θ hθ₀ (by ring)) (hfg x y)

/-- The restriction of a measure with the Prékopa–Leindler property at a weight `0 ≤ θ ≤ 1` to a
measurable convex set has the Prékopa–Leindler property as well. -/
theorem HasPrekopaLeindler.restrict {mu : Measure E} {theta : ℝ}
    (hmu : mu.HasPrekopaLeindler theta) (hθ₀ : 0 ≤ theta) (hθ₁ : theta ≤ 1) {s : Set E}
    (hs : MeasurableSet s) (hsc : Convex ℝ s) : (mu.restrict s).HasPrekopaLeindler theta := by
  first
  | rw [← withDensity_indicator_one hs]
    exact hmu.withDensity hθ₀ hθ₁ (measurable_one.indicator hs) (hsc.logConcave_indicator 1)

end MeasureTheory.Measure

namespace TauCeti.Real

/-- At each level `s`, the weighted volumes of the superlevel sets of `f` and `g` are bounded by
the volume of the superlevel set of `h`: below the common supremum the two sets are nonempty and
one-dimensional Brunn–Minkowski applies, and above it they are empty. -/
private theorem mul_volume_add_mul_volume_lt_le {f g h : ℝ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) (hfg : ⨆ x, f x = ⨆ y, g y) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hmin : ∀ x y, min (f x) (g y) ≤ h (c * x + d * y)) (s : ℝ≥0∞) :
    ENNReal.ofReal c * volume {x | s < f x} + ENNReal.ofReal d * volume {y | s < g y} ≤
      volume {z | s < h z} := by
  first
  | by_cases hs : s < ⨆ x, f x
    · obtain ⟨x, hx⟩ := lt_iSup_iff.1 hs
      obtain ⟨y, hy⟩ := lt_iSup_iff.1 (hfg ▸ hs)
      refine (mul_volume_add_mul_volume_le ⟨x, hx⟩ (hf.nullMeasurable measurableSet_Ioi)
        ⟨y, hy⟩ (hg.nullMeasurable measurableSet_Ioi) hc hd).trans (measure_mono ?_)
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact (lt_min hx hy).trans_le (hmin x y)
    · have hf0 : {x | s < f x} = ∅ :=
        eq_empty_of_forall_notMem fun x hx ↦ hs (hx.trans_le (le_iSup f x))
      have hg0 : {y | s < g y} = ∅ :=
        eq_empty_of_forall_notMem fun y hy ↦ hs (hfg ▸ hy.trans_le (le_iSup g y))
      simp [hf0, hg0]

/-- **Prékopa–Leindler inequality for the minimum** on `ℝ`. If `f` and `g` have the same
supremum and `h (c * x + d * y)` dominates `min (f x) (g y)` for all `x` and `y`, then
`c ∫ f + d ∫ g ≤ ∫ h`. The coefficients may vanish, and the common supremum and the integrals may
be infinite. -/
theorem mul_lintegral_add_mul_lintegral_le {f g h : ℝ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) (hh : AEMeasurable h) (hfg : ⨆ x, f x = ⨆ y, g y) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hmin : ∀ x y, min (f x) (g y) ≤ h (c * x + d * y)) :
    ENNReal.ofReal c * (∫⁻ x, f x) + ENNReal.ofReal d * ∫⁻ y, g y ≤ ∫⁻ z, h z := by
  first
    -- The layer-cake formula in `ℝ≥0∞`, at the exponent one.
  | have hlayer {u : ℝ → ℝ≥0∞} (hu : AEMeasurable u) :
        ∫⁻ x, u x = ∫⁻ t in Ioi 0, volume {x | ENNReal.ofReal t < u x} := by
      simpa using lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume hu one_pos
    rw [hlayer hf, hlayer hg, hlayer hh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact (le_lintegral_add _ _).trans <| lintegral_mono fun t ↦
      mul_volume_add_mul_volume_lt_le hf hg hfg hc hd hmin _

/-- The one-dimensional Prékopa–Leindler inequality at an interior weight, for `f` and `g` with
finite suprema. -/
private theorem rpow_mul_rpow_le_of_iSup_ne_top {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hF : ⨆ x, f x ≠ ∞) (hG : ⨆ y, g y ≠ ∞)
    (hfgh : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ ≤ ∫⁻ z, h z := by
  first
  | set F := ⨆ x, f x
    set G := ⨆ y, g y
    have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
    rcases eq_or_ne F 0 with hF0 | hF0
    · simp [ENNReal.iSup_eq_zero.1 hF0, ENNReal.zero_rpow_of_pos h1θ]
    rcases eq_or_ne G 0 with hG0 | hG0
    · simp [ENNReal.iSup_eq_zero.1 hG0, ENNReal.zero_rpow_of_pos hθ₀]
    -- Normalize the suprema of `f` and `g` to one, and scale `h` by the matching factor `K⁻¹`.
    set K := F ^ (1 - θ) * G ^ θ
    have hK0 : K ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 hF0) hF).ne'
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hG0) hG).ne'
    have hKtop : K ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1θ.le hF)
      (ENNReal.rpow_ne_top_of_nonneg hθ₀.le hG)
    have hscale (a b : ℝ≥0∞) :
        (F⁻¹ * a) ^ (1 - θ) * (G⁻¹ * b) ^ θ = K⁻¹ * (a ^ (1 - θ) * b ^ θ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ₀.le,
        ENNReal.inv_rpow, ENNReal.inv_rpow, ENNReal.mul_inv (.inr (ENNReal.rpow_ne_top_of_nonneg
        hθ₀.le hG)) (.inl (ENNReal.rpow_ne_top_of_nonneg h1θ.le hF))]
      ring
    have hsup : ⨆ x, F⁻¹ * f x = ⨆ y, G⁻¹ * g y := by
      rw [← ENNReal.mul_iSup, ← ENNReal.mul_iSup, ENNReal.inv_mul_cancel hF0 hF,
        ENNReal.inv_mul_cancel hG0 hG]
    have key := mul_lintegral_add_mul_lintegral_le (hf.const_mul _).aemeasurable
      (hg.const_mul _).aemeasurable (hh.const_mul K⁻¹).aemeasurable hsup h1θ.le hθ₀.le
      fun x y ↦ (ENNReal.min_le_rpow_one_sub_mul_rpow _ _ hθ₀.le hθ₁.le).trans <| by
        rw [hscale]
        gcongr
        exact hfgh x y
    rw [lintegral_const_mul _ hf, lintegral_const_mul _ hg, lintegral_const_mul _ hh] at key
    have hamgm := ENNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal (1 - θ))
      (Real.toNNReal θ) (F⁻¹ * ∫⁻ x, f x) (G⁻¹ * ∫⁻ y, g y) (by
        rw [← Real.toNNReal_add h1θ.le hθ₀.le, sub_add_cancel, Real.toNNReal_one])
    rw [Real.coe_toNNReal _ h1θ.le, Real.coe_toNNReal _ hθ₀.le, hscale] at hamgm
    rw [← ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.2 hKtop) (ENNReal.inv_ne_top.2 hK0)]
    exact hamgm.trans key

/-- The **Prékopa–Leindler inequality** on `ℝ`: Lebesgue measure has the Prékopa–Leindler
property at every weight `0 ≤ θ ≤ 1`. -/
theorem hasPrekopaLeindler_volume {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (volume : Measure ℝ).HasPrekopaLeindler θ := by
  first
  | intro f g h hf hg hh hfgh
    simp only [ENNReal.rpow_eq_pow] at hfgh ⊢
    rcases hθ₀.eq_or_lt with rfl | hθ₀
    · simpa using lintegral_mono fun x ↦ by simpa using hfgh x x
    rcases hθ₁.eq_or_lt with rfl | hθ₁
    · simpa using lintegral_mono fun y ↦ by simpa using hfgh y y
    have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
    -- Truncate `f` and `g` at finite heights and pass to the limit by monotone convergence.
    have htrunc {u : ℝ → ℝ≥0∞} (hu : Measurable u) :
        ∫⁻ x, u x = ⨆ n : ℕ, ∫⁻ x, min (u x) n := by
      rw [← lintegral_iSup (fun n ↦ hu.min measurable_const)
        fun m n hmn x ↦ min_le_min_left _ (Nat.cast_le.2 hmn)]
      simp [← inf_iSup_eq, ENNReal.iSup_natCast]
    have hbdd {u : ℝ → ℝ≥0∞} (n : ℕ) : ⨆ x, min (u x) n ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (iSup_le fun _ ↦ min_le_right _ _)
    have key (m n : ℕ) :
        (∫⁻ x, min (f x) m) ^ (1 - θ) * (∫⁻ y, min (g y) n) ^ θ ≤ ∫⁻ z, h z :=
      rpow_mul_rpow_le_of_iSup_ne_top hθ₀ hθ₁ (hf.min measurable_const)
        (hg.min measurable_const) hh (hbdd m) (hbdd n) fun x y ↦
        (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) h1θ.le)
          (ENNReal.rpow_le_rpow (min_le_left _ _) hθ₀.le)).trans (hfgh x y)
    rw [htrunc hf, htrunc hg, ← ENNReal.orderIsoRpow_apply _ h1θ,
      ← ENNReal.orderIsoRpow_apply _ hθ₀, OrderIso.map_iSup, OrderIso.map_iSup, ENNReal.iSup_mul]
    exact iSup_le fun m ↦ by
      rw [ENNReal.mul_iSup]
      exact iSup_le fun n ↦ by simpa using key m n

end TauCeti.Real

namespace TauCeti

/-- The **Prékopa–Leindler inequality** on `ι → ℝ`: Lebesgue measure on a finite power of `ℝ` has
the Prékopa–Leindler property at every weight `0 ≤ θ ≤ 1`. -/
theorem hasPrekopaLeindler_volume_pi (ι : Type*) [Fintype ι] {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) : (volume : Measure (ι → ℝ)).HasPrekopaLeindler θ := by
  first
  | intro f g h hf hg hh hfgh
    exact Measure.HasPrekopaLeindler.pi (fun _ ↦ Real.hasPrekopaLeindler_volume hθ₀ hθ₁)
      hf hg hh hfgh

/-- The **Prékopa–Leindler inequality** on a finite-dimensional real inner product space, such as
`EuclideanSpace ℝ (Fin n)`: its volume has the Prékopa–Leindler property at every weight
`0 ≤ θ ≤ 1`. -/
theorem hasPrekopaLeindler_volume (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) : (volume : Measure E).HasPrekopaLeindler θ := by
  first
  | intro f g h hf hg hh hfgh
    let b := stdOrthonormalBasis ℝ E
    exact Measure.HasPrekopaLeindler.map (hasPrekopaLeindler_volume_pi (Fin _) hθ₀ hθ₁)
      (b.repr.symm ∘ WithLp.toLp 2)
      (b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp _))
      (fun x y ↦ by simp) hf hg hh hfgh

end TauCeti

/-! ### Marginals of log-concave functions -/

namespace TauCeti

section AddCommMonoid

variable {E F : Type*} [MeasurableSpace E] [AddCommMonoid E] [Module ℝ E]
  [MeasurableSpace F] [AddCommMonoid F] [Module ℝ F] {ν : Measure F}

/-- **Marginals of log-concave functions are log-concave** (Prékopa; Bombieri–Gubler, Lemma
C.3.4). If `f : E × F → ℝ≥0∞` is measurable and log-concave and `ν` has the Prékopa–Leindler
property at every weight, then `x ↦ ∫⁻ y, f (x, y) ∂ν` is log-concave. No measure on `E` and no
finiteness of the integrals is needed. -/
theorem LogConcave.lintegral_prod_right
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {f : E × F → ℝ≥0∞}
    (hf : Measurable f) (hlc : LogConcave f) :
    LogConcave fun x ↦ ∫⁻ y, f (x, y) ∂ν := by
  first
  | refine logConcave_def.2 fun x₁ x₂ a b ha hb hab ↦ ?_
    obtain rfl : a = 1 - b := by linarith
    have hPL := hν hb (by linarith) (hf.comp measurable_prodMk_left)
      (hf.comp measurable_prodMk_left) (hf.comp measurable_prodMk_left) fun y₁ y₂ ↦ by
        simpa [ENNReal.rpow_eq_pow] using
          hlc.rpow_mul_rpow_le (x := (x₁, y₁)) (y := (x₂, y₂)) ha hb hab
    simpa [ENNReal.rpow_eq_pow] using hPL

/-- **Marginals over a convex set of log-concave functions are log-concave** (Bombieri–Gubler,
Lemma C.3.4). If `f : E × F → ℝ≥0∞` is measurable and log-concave, `s ⊆ F` is measurable and
convex, and `ν` has the Prékopa–Leindler property at every weight, then
`x ↦ ∫⁻ y in s, f (x, y) ∂ν` is log-concave. -/
theorem LogConcave.setLIntegral_prod_right
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {f : E × F → ℝ≥0∞}
    (hf : Measurable f) (hlc : LogConcave f) {s : Set F} (hs : MeasurableSet s)
    (hsc : Convex ℝ s) :
    LogConcave fun x ↦ ∫⁻ y in s, f (x, y) ∂ν := by
  first
  | have h := (hlc.mul ((hsc.linear_preimage (LinearMap.snd ℝ E F)).logConcave_indicator 1)
      ).lintegral_prod_right hν (hf.mul (measurable_const.indicator (hs.preimage measurable_snd)))
    convert h using 2 with x
    rw [← lintegral_indicator hs]
    congr 1 with y
    by_cases hy : y ∈ s <;> simp [hy]

/-- **Brunn's principle, in log-concave form.** For a measurable convex set `s ⊆ E × F` and a
measure `ν` with the Prékopa–Leindler property at every weight, the measure of the slices,
`x ↦ ν (Prod.mk x ⁻¹' s)`, is log-concave. -/
theorem _root_.Convex.logConcave_measure_preimage_prodMk
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {s : Set (E × F)}
    (hs : MeasurableSet s) (hsc : Convex ℝ s) :
    LogConcave fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  first
  | convert (hsc.logConcave_indicator 1).lintegral_prod_right hν
      (measurable_const.indicator hs) using 2 with x
    rw [← lintegral_indicator_one (measurable_prodMk_left hs)]
    exact lintegral_congr fun y ↦ by by_cases hy : (x, y) ∈ s <;> simp [hy]

end AddCommMonoid

variable {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
  [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {ν : Measure F}

/-- **The central slice of a symmetric convex set is the largest.** For a measurable convex set
`s ⊆ E × F` with `-s = s` and a negation-invariant measure `ν` with the Prékopa–Leindler
property at every weight, every slice `Prod.mk x ⁻¹' s` has measure at most that of the central
slice `Prod.mk 0 ⁻¹' s`. -/
theorem _root_.Convex.measure_preimage_prodMk_le_measure_preimage_prodMk_zero
    [MeasurableNeg F] [ν.IsNegInvariant]
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {s : Set (E × F)}
    (hs : MeasurableSet s) (hsc : Convex ℝ s) (hneg : ∀ p ∈ s, -p ∈ s) (x : E) :
    ν (Prod.mk x ⁻¹' s) ≤ ν (Prod.mk 0 ⁻¹' s) := by
  first
  | refine (hsc.logConcave_measure_preimage_prodMk hν hs).apply_le_apply_zero (fun x ↦ ?_) x
    have hslice : Prod.mk (-x) ⁻¹' s = -(Prod.mk x ⁻¹' s) := by
      ext y
      simp only [mem_preimage, Set.mem_neg]
      exact ⟨fun h ↦ by simpa using hneg _ h, fun h ↦ by simpa using hneg _ h⟩
    dsimp only
    rw [hslice, Measure.measure_neg]

end TauCeti
end -- closes the original EOF section from source line 92
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/EqHaar.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Haar measure under dilations and affine maps

The dimension root of outer volume scales by the absolute value of a real dilation
in a positive-dimensional real inner product space. The identity applies to arbitrary
sets and infinite outer volumes, and supplies the scaling law for volume inequalities.

An affine map of a finite-dimensional real normed space multiplies every additive Haar measure
by the absolute value of the determinant of its linear part
(`MeasureTheory.Measure.addHaar_image_affineMap`, and
`MeasureTheory.Measure.addHaar_image_affineEquiv` for affine equivalences), the affine form of
Mathlib's `MeasureTheory.Measure.addHaar_image_linearMap`.

A linear map into a finite-dimensional real normed space that is not surjective has almost every
fibre empty for every additive Haar measure on the codomain
(`LinearMap.ae_preimage_singleton_eq_empty`), since its range is a strict subspace.

For an invertible real square matrix `A` and nonnegative bounds `a i`, the region
`{x | ∀ i, |(A *ᵥ x) i| ≤ a i}` cut out by the linear forms of `A` has volume
`2 ^ n * (∏ i, a i) / |det A|`, where `n` is the size of `A`
(`Matrix.volume_setOf_forall_abs_mulVec_le`). It is the preimage of a coordinate box under `A`;
this is the volume computation behind Minkowski's linear forms theorem.

We also bound the additive Haar measure of the closure of a set in a finite-dimensional real
normed space by the measure of the unit ball times the dimension power of its diameter. This is
the elementary estimate converting coverings by sets of small diameter into measure bounds.
Combined with the diameter bound for Lipschitz images, it bounds the measure of the closure of
the image of a set under a Lipschitz map.

An element of finite order acting linearly on a finite-dimensional real space preserves every
additive Haar measure, because its determinant has finite order and so absolute value one
(`MeasureTheory.Measure.addHaar_preimage_smul_of_isOfFinOrder`). Hence a finite group acting
linearly preserves every additive Haar measure
(`MeasureTheory.Measure.smulInvariantMeasure_addHaar`).
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dimension-root volume scales linearly under every real dilation, including zero.
This identity holds for arbitrary sets and infinite outer volumes. -/
theorem volume_smul_rpow {A : Set E} (hn : Module.finrank ℝ E ≠ 0) (c : ℝ) :
    volume (c • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
      ENNReal.ofReal |c| * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  first
  | rw [Measure.addHaar_smul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      abs_pow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast (abs_nonneg c) hn]

end TauCeti

namespace MeasureTheory.Measure

section Affine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- The image of a set under an affine map has Haar measure equal to the absolute value of the
determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineMap (f : F →ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f.linear| * μ s := by
  first
  | have hf : f '' s = (fun y ↦ y + f 0) '' (f.linear '' s) := by
      rw [image_image]
      exact image_congr fun x _ ↦ by simpa using f.map_vadd 0 x
    rw [hf, image_add_right, measure_preimage_add_right, addHaar_image_linearMap]

/-- The image of a set under an affine equivalence has Haar measure equal to the absolute value of
the determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineEquiv (f : F ≃ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f.linear : F →ₗ[ℝ] F)| * μ s :=
  addHaar_image_affineMap μ (f : F →ᵃ[ℝ] F) s

end Affine

section Diameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The closure of a set of diameter `d` in an `n`-dimensional real normed space has additive
Haar measure at most `μ (ball 0 1) * d ^ n`, since it lies in a closed ball of radius `d`.
This holds for every set, including empty and unbounded ones. -/
theorem addHaar_closure_le_mul_ediam_pow (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) :
    μ (closure s) ≤ μ (Metric.ball 0 1) * Metric.ediam s ^ Module.finrank ℝ E := by
  first
  | rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    by_cases hs : Metric.ediam s = ∞
    · have hE : Module.finrank ℝ E ≠ 0 := by
        intro hE
        have : Subsingleton E := Module.finrank_zero_iff.1 hE
        rw [Metric.ediam_subsingleton Set.subsingleton_of_subsingleton] at hs
        exact ENNReal.zero_ne_top hs
      rw [hs, ENNReal.top_pow hE, ENNReal.mul_top (Metric.measure_ball_pos μ 0 one_pos).ne']
      exact le_top
    have hb : Bornology.IsBounded s := Metric.isBounded_iff_ediam_ne_top.2 hs
    have hsub : closure s ⊆ Metric.closedBall x (Metric.diam s) := fun y hy ↦ by
      rw [Metric.mem_closedBall, ← Metric.diam_closure]
      exact Metric.dist_le_diam_of_mem hb.closure hy (subset_closure hx)
    calc μ (closure s) ≤ μ (Metric.closedBall x (Metric.diam s)) := measure_mono hsub
      _ = μ (Metric.ball 0 1) * Metric.ediam s ^ Module.finrank ℝ E := by
        rw [addHaar_closedBall μ x Metric.diam_nonneg, mul_comm,
          ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam, ENNReal.ofReal_toReal hs]

end Diameter

section FiniteOrder

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- An element of finite order acting linearly on a finite-dimensional real space preserves
every additive Haar measure. Its determinant has finite order in `ℝ`, hence absolute value
one. -/
theorem addHaar_preimage_smul_of_isOfFinOrder [Monoid G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] {g : G} (hg : IsOfFinOrder g) (s : Set E) :
    μ ((g • ·) ⁻¹' s) = μ s := by
  first
  | set L := DistribMulAction.toModuleEnd ℝ E g
    have habs : |LinearMap.det L| = 1 :=
      ((((absHom (α := ℝ)).toMonoidHom).comp
        (LinearMap.det.comp (DistribMulAction.toModuleEnd ℝ E))).isOfFinOrder hg).eq_one
        (abs_nonneg _)
    have hdet : LinearMap.det L ≠ 0 := fun h => by simp [h] at habs
    have h := addHaar_preimage_linearMap μ hdet s
    rwa [abs_inv, habs, inv_one, ENNReal.ofReal_one, one_mul] at h

/-- A finite group acting linearly on a finite-dimensional real space preserves every additive
Haar measure. -/
theorem smulInvariantMeasure_addHaar [Group G] [Finite G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] : SMulInvariantMeasure G E μ :=
  ⟨fun g s _ => addHaar_preimage_smul_of_isOfFinOrder μ (isOfFinOrder_of_finite g) s⟩

end FiniteOrder

end MeasureTheory.Measure

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A linear map that is not surjective has almost every fibre empty, for every additive Haar
measure on its finite-dimensional codomain. -/
theorem ae_preimage_singleton_eq_empty (μ : Measure F) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] F)
    (hL : ¬Function.Surjective L) :
    ∀ᵐ y ∂μ, L ⁻¹' {y} = ∅ := by
  first
  | filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (Measure.addHaar_submodule μ _ (mt range_eq_top.mp hL))] with y hy
    exact eq_empty_of_forall_notMem fun x hx ↦ hy ⟨x, hx⟩

end LinearMap

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The region cut out by the linear forms of an invertible real square matrix `A`: for
nonnegative bounds `a i`, the set of `x : ι → ℝ` with `|(A *ᵥ x) i| ≤ a i` for every `i` has
volume `2 ^ n * (∏ i, a i) / |det A|`, where `n` is the cardinality of `ι`. This includes the case
of an empty `ι`, where both sides are `1`. -/
theorem volume_setOf_forall_abs_mulVec_le (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) {a : ι → ℝ}
    (ha : 0 ≤ a) :
    volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| ≤ a i} =
      ENNReal.ofReal (2 ^ Fintype.card ι * (∏ i, a i) / |A.det|) := by
  first
  | have hS : {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| ≤ a i} = toLin' A ⁻¹' Icc (-a) a := by
      ext x
      simp [abs_le, Pi.le_def, forall_and]
    rw [hS, Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin']),
      LinearMap.det_toLin', Real.volume_Icc_pi]
    simp_rw [Pi.neg_apply, sub_neg_eq_add, ← two_mul]
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ mul_nonneg zero_le_two (ha i),
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, inv_mul_eq_div]

end Matrix

namespace LipschitzOnWith

open MeasureTheory
open scoped NNReal

variable {X E : Type*} [PseudoEMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The closure of the image of a set `A` under a `K`-Lipschitz map into an `n`-dimensional real
normed space has additive Haar measure at most `μ (ball 0 1) * K ^ n * ediam A ^ n`. -/
theorem addHaar_closure_image_le_mul_ediam_pow (μ : Measure E) [μ.IsAddHaarMeasure] {K : ℝ≥0}
    {f : X → E} {A : Set X} (hf : LipschitzOnWith K f A) :
    μ (closure (f '' A)) ≤
      μ (Metric.ball 0 1) * K ^ Module.finrank ℝ E * Metric.ediam A ^ Module.finrank ℝ E := by
  first
  | have hdiam : Metric.ediam (f '' A) ≤ K * Metric.ediam A :=
      Metric.ediam_image_le_iff.2 fun x hx x' hx' ↦
        (hf hx hx').trans (by gcongr; exact Metric.edist_le_ediam_of_mem hx hx')
    calc μ (closure (f '' A)) ≤ μ (Metric.ball 0 1) * Metric.ediam (f '' A) ^ Module.finrank ℝ E :=
          Measure.addHaar_closure_le_mul_ediam_pow μ _
      _ ≤ μ (Metric.ball 0 1) * (K * Metric.ediam A) ^ Module.finrank ℝ E := by gcongr
      _ = _ := by rw [mul_pow, mul_assoc]

end LipschitzOnWith
end -- closes the original EOF section from source line 47
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/EqHaar.lean -/

/- BEGIN SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Brunn–Minkowski in finite-dimensional Euclidean spaces

The Brunn–Minkowski inequality bounds the outer volume of a Minkowski sum from below
by the sum of the dimension roots of the input volumes. We work with Lebesgue-measurable
sets and do not require their sum to be measurable. Nonemptiness is retained even when
an input has zero volume.

The multiplicative formulation bounds the volume of a convex combination by a weighted
geometric mean of volumes. The additive formulation bounds its dimension root by a
weighted sum of dimension roots, for arbitrary nonnegative coefficients. Real-valued
versions assume finite outer volume of the weighted sum. These inequalities support
convex isoperimetric estimates and concavity of outer parallel volumes.

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for the deduction from Prékopa–Leindler by indicators and rescaling.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The multiplicative Brunn–Minkowski inequality, with outer volume on the right.
The weight is strictly between zero and one; input volumes may be zero or infinite. -/
theorem volume_rpow_mul_volume_rpow_le {A B : Set E}
    (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    volume A ^ (1 - θ) * volume B ^ θ ≤ volume ((1 - θ) • A + θ • B) := by
  first
  | obtain ⟨K, hKA, hK, hKv⟩ := hA.exists_measurable_subset_ae_eq
    obtain ⟨L, hLB, hL, hLv⟩ := hB.exists_measurable_subset_ae_eq
    let S := toMeasurable volume ((1 - θ) • A + θ • B)
    have hS : MeasurableSet S := measurableSet_toMeasurable _ _
    have hPL : (volume : Measure E).HasPrekopaLeindler θ :=
      hasPrekopaLeindler_volume E hθ₀.le hθ₁.le
    rw [Measure.hasPrekopaLeindler_def] at hPL
    have key := hPL (f := K.indicator (fun _ ↦ (1 : ℝ≥0∞)))
      (g := L.indicator (fun _ ↦ (1 : ℝ≥0∞))) (h := S.indicator (fun _ ↦ (1 : ℝ≥0∞)))
      (measurable_const.indicator hK) (measurable_const.indicator hL)
      (measurable_const.indicator hS)
      (fun x y ↦ by
        by_cases hx : x ∈ K
        · by_cases hy : y ∈ L
          · have hz : (1 - θ) • x + θ • y ∈ S :=
              subset_toMeasurable volume _ (add_mem_add (smul_mem_smul_set (hKA hx))
                (smul_mem_smul_set (hLB hy)))
            simp [hx, hy, hz]
          · simp [hy, ENNReal.zero_rpow_of_pos hθ₀]
        · simp [hx, ENNReal.zero_rpow_of_pos (sub_pos.2 hθ₁)])
    simpa only [lintegral_indicator_const hK, lintegral_indicator_const hL,
      lintegral_indicator_const hS, one_mul, measure_congr hKv, measure_congr hLv,
      S, measure_toMeasurable, ENNReal.rpow_eq_pow] using key

/-- The additive lower bound in terms of positive dimension roots of the input volumes. -/
private theorem volume_pow_add_root_le {A B : Set E}
    (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hAv : volume A = ENNReal.ofReal (a ^ Module.finrank ℝ E))
    (hBv : volume B = ENNReal.ofReal (b ^ Module.finrank ℝ E)) :
    ENNReal.ofReal ((a + b) ^ Module.finrank ℝ E) ≤ volume (A + B) := by
  first
    -- Both rescaled volumes are `(a + b) ^ dim`, and their weighted sum is `A + B`.
  | let θ := b / (a + b)
    have hθ₀ : 0 < θ := div_pos hb (add_pos ha hb)
    have hθ₁ : θ < 1 := (div_lt_one (add_pos ha hb)).2 (lt_add_of_pos_left _ ha)
    have hscale {S : Set E} {r : ℝ} (hr : 0 < r)
        (hSv : volume S = ENNReal.ofReal (r ^ Module.finrank ℝ E)) :
        volume (((a + b) / r) • S) =
          ENNReal.ofReal ((a + b) ^ Module.finrank ℝ E) := by
      rw [Measure.addHaar_smul_of_nonneg volume (by positivity), hSv,
        ← ENNReal.ofReal_mul (by positivity), div_pow,
        div_mul_cancel₀ _ (pow_ne_zero _ hr.ne')]
    have hleft : (1 - θ) * ((a + b) / a) = 1 := by
      dsimp [θ]
      field_simp
      ring
    have hright : θ * ((a + b) / b) = 1 := by
      dsimp [θ]
      field_simp
    have key := volume_rpow_mul_volume_rpow_le
      (Measure.NullMeasurableSet.const_smul hA ((a + b) / a))
      (Measure.NullMeasurableSet.const_smul hB ((a + b) / b)) hθ₀ hθ₁
    rw [hscale ha hAv, hscale hb hBv,
      ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hθ₁.le) hθ₀.le,
      sub_add_cancel, ENNReal.rpow_one, smul_smul, smul_smul,
      hleft, hright, one_smul, one_smul] at key
    exact key

/-- Weighted **Brunn–Minkowski inequality** with arbitrary nonnegative coefficients.
It includes the convex-combination weights `1 - θ, θ` for every `θ ∈ [0,1]`.
Zero coefficients and infinite input volumes use extended multiplication `0 * ∞ = 0`. -/
theorem mul_volume_rpow_add_mul_volume_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal c * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      ENNReal.ofReal d * volume B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  first
    -- Apply the volume argument to the dilated sets, retaining zero coefficients.
  | let C := c • A
    let D := d • B
    have hC := Measure.NullMeasurableSet.const_smul hA c
    have hD := Measure.NullMeasurableSet.const_smul hB d
    suffices h : volume C ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
        volume D ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
          volume (C + D) ^ ((Module.finrank ℝ E : ℝ)⁻¹) by
      simpa only [C, D, volume_smul_rpow hn, abs_of_nonneg hc, abs_of_nonneg hd] using h
    have hp : 0 < (Module.finrank ℝ E : ℝ)⁻¹ := by positivity
    have hAle : volume C ≤ volume (C + D) := by
      obtain ⟨b, hb⟩ := (hBn.smul_set : D.Nonempty)
      calc
        volume C = volume (C + {b}) := by simp
        _ ≤ volume (C + D) := measure_mono (add_subset_add Subset.rfl (by simpa using hb))
    have hBle : volume D ≤ volume (C + D) := by
      obtain ⟨a, ha⟩ := (hAn.smul_set : C.Nonempty)
      calc
        volume D = volume ({a} + D) := by simp
        _ ≤ volume (C + D) := measure_mono (add_subset_add (by simpa using ha) Subset.rfl)
    -- Translation bounds settle infinite and zero volumes.
    by_cases hAfin : volume C = ∞
    · have hsum : volume (C + D) = ∞ := top_unique (hAfin ▸ hAle)
      simp [hAfin, hsum, ENNReal.top_rpow_of_pos hp]
    by_cases hBfin : volume D = ∞
    · have hsum : volume (C + D) = ∞ := top_unique (hBfin ▸ hBle)
      simp [hBfin, hsum, ENNReal.top_rpow_of_pos hp]
    by_cases hAz : volume C = 0
    · simpa only [hAz, ENNReal.zero_rpow_of_pos hp, zero_add] using
        ENNReal.rpow_le_rpow hBle hp.le
    by_cases hBz : volume D = 0
    · simpa only [hBz, ENNReal.zero_rpow_of_pos hp, add_zero] using
        ENNReal.rpow_le_rpow hAle hp.le
    -- Positive finite volumes admit dimension roots for the rescaling lemma.
    let a := (volume C).toReal ^ ((Module.finrank ℝ E : ℝ)⁻¹)
    let b := (volume D).toReal ^ ((Module.finrank ℝ E : ℝ)⁻¹)
    have ha : 0 < a := Real.rpow_pos_of_pos (ENNReal.toReal_pos hAz hAfin) _
    have hb : 0 < b := Real.rpow_pos_of_pos (ENNReal.toReal_pos hBz hBfin) _
    have hAv : volume C = ENNReal.ofReal (a ^ Module.finrank ℝ E) := by
      rw [Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn, ENNReal.ofReal_toReal hAfin]
    have hBv : volume D = ENNReal.ofReal (b ^ Module.finrank ℝ E) := by
      rw [Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn, ENNReal.ofReal_toReal hBfin]
    have key := ENNReal.rpow_le_rpow (volume_pow_add_root_le hC hD ha hb hAv hBv) hp.le
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
      Real.pow_rpow_inv_natCast (by positivity) hn, ENNReal.ofReal_add ha.le hb.le] at key
    simpa only [a, b, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal hAfin, ENNReal.ofReal_toReal hBfin] using key

/-- **Brunn–Minkowski inequality** for nonempty Lebesgue-measurable sets
in a positive-dimensional real inner product space. The sum has its outer volume and
need not be measurable or have finite volume. -/
theorem volume_rpow_add_volume_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume) :
    volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      volume B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume (A + B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  first
  | simpa only [ENNReal.ofReal_one, one_mul, one_smul] using
      mul_volume_rpow_add_mul_volume_rpow_le hn hAn hA hBn hB
        (c := 1) (d := 1) zero_le_one zero_le_one

/-- Real-valued weighted **Brunn–Minkowski inequality**. Only the weighted sum is
required to have finite outer volume: an input with zero coefficient may have infinite volume. -/
theorem mul_volume_real_rpow_add_mul_volume_real_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hfin : volume (c • A + d • B) ≠ ∞) :
    c * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      d * volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume.real (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  first
  | have h := mul_volume_rpow_add_mul_volume_rpow_le hn hAn hA hBn hB hc hd
    have hsum := ENNReal.rpow_ne_top_of_nonneg (by positivity :
      0 ≤ (Module.finrank ℝ E : ℝ)⁻¹) hfin
    have hAfin := ne_top_of_le_ne_top hsum (le_self_add.trans h)
    have hBfin := ne_top_of_le_ne_top hsum (le_add_self.trans h)
    simpa only [ENNReal.toReal_add hAfin hBfin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd, ← ENNReal.toReal_rpow,
      measureReal_def] using ENNReal.toReal_mono hsum h

/-- Real-valued **Brunn–Minkowski inequality**. The sum's outer volume must be finite;
this implies finiteness of both input volumes. -/
theorem volume_real_rpow_add_volume_real_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume) (hfin : volume (A + B) ≠ ∞) :
    volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume.real (A + B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  first
  | simpa only [one_mul, one_smul] using
      mul_volume_real_rpow_add_mul_volume_real_rpow_le hn hAn hA hBn hB
        (c := 1) (d := 1) zero_le_one zero_le_one (by simpa only [one_smul] using hfin)

end TauCeti
end -- closes the original EOF section from source line 31
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Basic.lean -/

/- BEGIN SOURCE: VolumePolynomials/BerwaldLevelSets.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Actual superlevel sets of concave functions

Brunn--Minkowski gives concavity of the normalized dimension root of their
volumes. Superlevel sets need not be closed: convexity supplies their null
measurability, and compact containment supplies finiteness.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.BerwaldLevelSets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def superlevel (Z : Set E) (f : E → ℝ) (t : ℝ) : Set E := {x | x ∈ Z ∧ t ≤ f x}

theorem superlevel_subset (Z : Set E) (f : E → ℝ) (t : ℝ) : superlevel Z f t ⊆ Z :=
  fun _ h => h.1

theorem superlevel_convex {Z : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ Z f) (t : ℝ) :
    Convex ℝ (superlevel Z f t) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨hf.1 hx.1 hy.1 ha hb hab, ?_⟩
    have h := hf.2 hx.1 hy.1 ha hb hab
    change a * f x + b * f y ≤ f (a • x + b • y) at h
    have hleft := mul_le_mul_of_nonneg_left hx.2 ha
    have hright := mul_le_mul_of_nonneg_left hy.2 hb
    have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
    linarith

theorem superlevel_minkowski_subset {Z : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ Z f)
    (s t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • superlevel Z f s + b • superlevel Z f t ⊆ superlevel Z f (a * s + b * t) := by
  first
  | rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨hf.1 hx.1 hy.1 ha hb hab, ?_⟩
    exact (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
      (mul_le_mul_of_nonneg_left hy.2 hb)).trans (hf.2 hx.1 hy.1 ha hb hab)

theorem superlevel_zero {Z : Set E} {f : E → ℝ} (hf : ∀ x ∈ Z, 0 ≤ f x) :
    superlevel Z f 0 = Z := by
  first
  | ext x
    exact ⟨fun h => h.1, fun hx => ⟨hx, hf x hx⟩⟩

theorem superlevel_nonempty_of_lt_sup {Z : Set E} {f : E → ℝ}
    (hZ : Z.Nonempty) {t : ℝ} (ht : t < sSup (f '' Z)) :
    (superlevel Z f t).Nonempty := by
  first
  | obtain ⟨v, ⟨x, hx, rfl⟩, htx⟩ := exists_lt_of_lt_csSup (hZ.image f) ht
    exact ⟨x, hx, htx.le⟩

def rootTail (Z : Set E) (f : E → ℝ) (t : ℝ) : ℝ :=
  volume.real (superlevel Z f t) ^ ((finrank ℝ E : ℝ)⁻¹) /
    volume.real Z ^ ((finrank ℝ E : ℝ)⁻¹)

theorem rootTail_nonnegative (Z : Set E) (f : E → ℝ) (t : ℝ) :
    0 ≤ rootTail Z f t := by
  first
  | exact div_nonneg (Real.rpow_nonneg (measureReal_nonneg) _)
      (Real.rpow_nonneg measureReal_nonneg _)

theorem rootTail_zero {Z : Set E} {f : E → ℝ}
    (hvol : 0 < volume.real Z) (hf : ∀ x ∈ Z, 0 ≤ f x) : rootTail Z f 0 = 1 := by
  first
  | unfold rootTail
    rw [superlevel_zero hf, div_self (Real.rpow_pos_of_pos hvol _).ne']

theorem rootTail_pow {Z : Set E} {f : E → ℝ} (hdim : finrank ℝ E ≠ 0) (t : ℝ) :
    rootTail Z f t ^ finrank ℝ E = volume.real (superlevel Z f t) / volume.real Z := by
  first
  | unfold rootTail
    rw [div_pow, Real.rpow_inv_natCast_pow measureReal_nonneg hdim,
      Real.rpow_inv_natCast_pow measureReal_nonneg hdim]

/-- The geometric concavity input to the scalar Berwald comparison. -/
theorem rootTail_concave {Z : Set E} {f : E → ℝ}
    (hdim : finrank ℝ E ≠ 0) (hZ : IsCompact Z) (hne : Z.Nonempty)
    (hvol : 0 < volume.real Z) (hf : ConcaveOn ℝ Z f) :
    ConcaveOn ℝ (Iio (sSup (f '' Z))) (rootTail Z f) := by
  first
  | refine ⟨convex_Iio _, ?_⟩
    intro s hs t ht a b ha hb hab
    have hsne := superlevel_nonempty_of_lt_sup hne hs
    have htne := superlevel_nonempty_of_lt_sup hne ht
    have hsubset := superlevel_minkowski_subset hf s t ha hb hab
    have hbound : volume (a • superlevel Z f s + b • superlevel Z f t) ≠ ⊤ :=
      ne_top_of_le_ne_top hZ.measure_ne_top
        (measure_mono (hsubset.trans (superlevel_subset Z f _)))
    have hbm := TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le hdim
      hsne ((superlevel_convex hf s).nullMeasurableSet volume)
      htne ((superlevel_convex hf t).nullMeasurableSet volume) ha hb hbound
    have hmono := Real.rpow_le_rpow (measureReal_nonneg (μ := volume)
      (s := a • superlevel Z f s + b • superlevel Z f t))
      (measureReal_mono hsubset
        (ne_top_of_le_ne_top hZ.measure_ne_top (measure_mono (superlevel_subset Z f _))))
      (inv_nonneg.mpr (Nat.cast_nonneg (finrank ℝ E)))
    have hden : 0 < volume.real Z ^ ((finrank ℝ E : ℝ)⁻¹) :=
      Real.rpow_pos_of_pos hvol _
    have h := div_le_div_of_nonneg_right (hbm.trans hmono) hden.le
    simpa only [rootTail, smul_eq_mul, add_div, mul_div_assoc] using h

theorem rootTail_concave_nonnegative {Z : Set E} {f : E → ℝ}
    (hdim : finrank ℝ E ≠ 0) (hZ : IsCompact Z) (hne : Z.Nonempty)
    (hvol : 0 < volume.real Z) (hf : ConcaveOn ℝ Z f) :
    ConcaveOn ℝ (Ico 0 (sSup (f '' Z))) (rootTail Z f) :=
  (rootTail_concave hdim hZ hne hvol hf).subset (fun _ h => h.2) (convex_Ico _ _)

end VolumePolynomials.BerwaldLevelSets
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BerwaldLevelSets.lean -/

/- BEGIN SOURCE: VolumePolynomials/BerwaldMoments.lean -/
section



@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Measurability and the actual moment identities

A bounded concave function is allowed to be discontinuous on the boundary
of its convex domain. Its interior continuity and the null frontier give
the required almost-everywhere measurability. The moment identities below
are actual Lebesgue integrals, obtained from Mathlib's layer-cake theorem.
-/

open Set MeasureTheory Filter

namespace VolumePolynomials.BerwaldMoments



section ConvexDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open BerwaldLevelSets

theorem convex_ae_eq_interior {Z : Set E} (hZ : Convex ℝ Z) :
    Z =ᵐ[volume] interior Z := by
  first
  | filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hZ.addHaar_frontier volume)] with x hx
    apply propext
    exact ⟨fun hxZ => (mem_interior_iff_notMem_frontier hxZ).mpr hx,
      fun hxZ => interior_subset hxZ⟩

theorem concave_aestronglyMeasurable {Z : Set E} {f : E → ℝ}
    (hf : ConcaveOn ℝ Z f) : AEStronglyMeasurable f (volume.restrict Z) := by
  first
  | rw [Measure.restrict_congr_set (convex_ae_eq_interior hf.1)]
    exact hf.continuousOn_interior.aestronglyMeasurable isOpen_interior.measurableSet

theorem bounded_concave_integrable_signed {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) {C : ℝ}
    (hb : ∀ x ∈ Z, ‖f x‖ ≤ C) : IntegrableOn f Z := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    apply (integrable_const C).mono' (concave_aestronglyMeasurable hf)
    filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
    exact hb x hx

/-- Boundary values require no continuity hypothesis. -/
theorem bounded_concave_integrable {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) {M : ℝ}
    (hn : ∀ x ∈ Z, 0 ≤ f x) (hb : ∀ x ∈ Z, f x ≤ M) :
    IntegrableOn f Z := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    apply Integrable.of_mem_Icc 0 M (concave_aestronglyMeasurable hf).aemeasurable
    filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
    exact ⟨hn x hx, hb x hx⟩

theorem concave_pow_integrable {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ x ∈ Z, 0 ≤ f x) (hb : ∀ x ∈ Z, f x ≤ M) (p : ℕ) :
    IntegrableOn (fun x => f x ^ p) Z := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    apply Integrable.of_mem_Icc 0 (M ^ p)
      ((concave_aestronglyMeasurable hf).aemeasurable.pow_const p)
    filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
    exact ⟨pow_nonneg (hn x hx) p, pow_le_pow_left₀ (hn x hx) (hb x hx) p⟩

def tail (Z : Set E) (f : E → ℝ) (t : ℝ) : ℝ :=
  volume.real (superlevel Z f t) / volume.real Z

theorem tail_nonnegative (Z : Set E) (f : E → ℝ) (t : ℝ) : 0 ≤ tail Z f t :=
  div_nonneg measureReal_nonneg measureReal_nonneg

theorem tail_antitone {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ) :
    Antitone (tail Z f) := by
  first
  | intro s t hst
    apply div_le_div_of_nonneg_right _ measureReal_nonneg
    exact measureReal_mono (fun _ hx => ⟨hx.1, hst.trans hx.2⟩)
      (ne_top_of_le_ne_top hZ.measure_ne_top
        (measure_mono (superlevel_subset Z f s)))

theorem tail_le_one {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ) (t : ℝ) :
    tail Z f t ≤ 1 := by
  first
  | by_cases hz : volume.real Z = 0
    · simp [tail, hz]
    · apply (div_le_one (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz))).mpr
      exact measureReal_mono (superlevel_subset Z f t) hZ.measure_ne_top

theorem tail_zero_of_sup_lt {Z : Set E} {f : E → ℝ}
    (hb : BddAbove (f '' Z)) {t : ℝ} (ht : sSup (f '' Z) < t) : tail Z f t = 0 := by
  first
  | have he : superlevel Z f t = ∅ := by
      first
      | apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact not_le_of_gt ht (hx.2.trans (le_csSup hb ⟨x, hx.1, rfl⟩))
    simp only [tail, he, measureReal_empty, zero_div]

def clippedTail (Z : Set E) (f : E → ℝ) (t : ℝ) : ℝ :=
  if t < sSup (f '' Z) then tail Z f t else 0

theorem clippedTail_ae_eq_tail {Z : Set E} {f : E → ℝ}
    (hb : BddAbove (f '' Z)) : clippedTail Z f =ᵐ[volume] tail Z f := by
  first
  | filter_upwards [volume.ae_ne (sSup (f '' Z))] with t ht
    by_cases hlt : t < sSup (f '' Z)
    · simp only [clippedTail, if_pos hlt]
    · rw [clippedTail, if_neg hlt]
      exact (tail_zero_of_sup_lt hb (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm ht))).symm

theorem clippedTail_nonnegative (Z : Set E) (f : E → ℝ) (t : ℝ) :
    0 ≤ clippedTail Z f t := by
  first
  | unfold clippedTail
    split_ifs
    · exact tail_nonnegative Z f t
    · exact le_rfl

theorem clippedTail_antitone {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ) :
    Antitone (clippedTail Z f) := by
  first
  | intro s t hst
    by_cases ht : t < sSup (f '' Z)
    · simp only [clippedTail, if_pos ht, if_pos (hst.trans_lt ht)]
      exact tail_antitone hZ f hst
    · rw [clippedTail, if_neg ht]
      exact clippedTail_nonnegative Z f s

theorem clippedTail_integrableOn {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ)
    (a b : ℝ) : IntegrableOn (clippedTail Z f) (Icc a b) :=
  ((clippedTail_antitone hZ f).antitoneOn (Icc a b)).integrableOn_isCompact isCompact_Icc

theorem clippedTail_first_moment_integrableOn {Z : Set E} (hZ : IsCompact Z)
    (f : E → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t => t * clippedTail Z f t) (Icc 0 a) := by
  first
  | apply (clippedTail_integrableOn hZ f 0 a).bdd_mul (c := a)
      continuous_id.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

theorem moment_identity {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) (hn : ∀ x ∈ Z, 0 ≤ f x)
    (hb : BddAbove (f '' Z)) (p : ℕ) :
    (∫ x in Z, f x ^ (p + 1)) / volume.real Z =
      (p + 1 : ℝ) * ∫ t in Ioi 0, t ^ p * clippedTail Z f t := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    have hn' : 0 ≤ᵐ[volume.restrict Z] f := by
      first
      | filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
        exact hn x hx
    have ht (t : ℝ) : (volume.restrict Z).real {x | t ≤ f x} =
        volume.real (superlevel Z f t) := by
      first
      | unfold Measure.real
        rw [Measure.restrict_apply' hZ.measurableSet]
        apply congrArg (fun S : Set E => (volume S).toReal)
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, superlevel, and_comm]
    rw [power_layer_cake (concave_aestronglyMeasurable hf).aemeasurable hn' p]
    simp only [ht]
    rw [mul_div_assoc, ← integral_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (clippedTail_ae_eq_tail hb)] with t ht'
    rw [ht', tail, mul_div_assoc]

/-- A finite upper integration limit is justified by the actual support of
the survival function, including a possible positive plateau at its maximum. -/
theorem moment_identity_bounded {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) (hn : ∀ x ∈ Z, 0 ≤ f x)
    (hb : BddAbove (f '' Z)) {a : ℝ} (ha : sSup (f '' Z) ≤ a) (p : ℕ) :
    (∫ x in Z, f x ^ (p + 1)) / volume.real Z =
      (p + 1 : ℝ) * ∫ t in Icc 0 a, t ^ p * clippedTail Z f t := by
  first
  | rw [moment_identity hZ hf hn hb p, integral_Icc_eq_integral_Ioc]
    congr 1
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self
    exact Eventually.of_forall fun t ht => by
      have hta : a < t := by
        first
        | have ht0 := ht.1
          simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and] at ht
          exact lt_of_not_ge (ht.2 ht0)
      simp only [clippedTail, if_neg (not_lt.mpr (ha.trans hta.le)), mul_zero]

end ConvexDomain

end VolumePolynomials.BerwaldMoments
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BerwaldMoments.lean -/

/- BEGIN SOURCE: VolumePolynomials/SharpBerwald.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The sharp second-moment inequality for bounded concave functions

All moments are uniform Lebesgue averages over the actual convex domain.
No regularity at its boundary, strict positivity of the function, or
attainment of its supremum is assumed.
-/

open Set MeasureTheory Module

namespace VolumePolynomials

open BerwaldComparison BerwaldLevelSets BerwaldMoments

def berwaldConstant (k : ℕ) : ℝ := 2 * (k + 1 : ℝ) / (k + 2 : ℝ)

def uniformAverage {E : Type*} [MeasurableSpace E] [MeasureSpace E]
    (Z : Set E) (f : E → ℝ) : ℝ := (∫ x in Z, f x) / volume.real Z

/-- The scalar assertion of Lemma 6.1, in arbitrary positive finite
dimension. The positive volume assumption specifies the uniform averaging
operation already required in the paper's notation. -/
theorem sharp_berwald_second_moment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : 0 < finrank ℝ E) {Z : Set E} (hZ : IsCompact Z)
    (hvol : 0 < volume.real Z) {f : E → ℝ} (hf : ConcaveOn ℝ Z f)
    (hn : ∀ x ∈ Z, 0 ≤ f x) (hb : BddAbove (f '' Z)) :
    uniformAverage Z (fun x => f x ^ 2) ≤
      berwaldConstant (finrank ℝ E) * uniformAverage Z f ^ 2 := by
  first
  | have hne : Z.Nonempty := by
      first
      | by_contra h
        have hz : Z = ∅ := not_nonempty_iff_eq_empty.mp h
        simpa only [hz, measureReal_empty, lt_self_iff_false] using hvol
    let M : ℝ := sSup (f '' Z)
    have hM0 : 0 ≤ M := by
      first
      | obtain ⟨x, hx⟩ := hne
        exact (hn x hx).trans (le_csSup hb ⟨x, hx, rfl⟩)
    by_cases hM : M = 0
    · have hzero : ∀ x ∈ Z, f x = 0 := by
        first
        | intro x hx
          apply le_antisymm _ (hn x hx)
          have hfx : f x ≤ M := le_csSup hb ⟨x, hx, rfl⟩
          simpa only [hM] using hfx
      have hi : (∫ x in Z, f x) = 0 := by
        first
        | calc
            (∫ x in Z, f x) = ∫ x in Z, (0 : ℝ) :=
              setIntegral_congr_fun hZ.measurableSet hzero
            _ = 0 := integral_zero _ _
      have hi2 : (∫ x in Z, f x ^ 2) = 0 := by
        first
        | calc
            (∫ x in Z, f x ^ 2) = ∫ x in Z, (0 : ℝ) := by
              apply setIntegral_congr_fun hZ.measurableSet
              intro x hx
              change f x ^ 2 = 0
              rw [hzero x hx, zero_pow (by decide : 2 ≠ 0)]
            _ = 0 := integral_zero _ _
      simp only [uniformAverage, hi, hi2, zero_div, zero_pow (by decide : 2 ≠ 0),
        mul_zero, le_refl]
    · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
      have hconc := rootTail_concave_nonnegative hdim.ne' hZ hne hvol hf
      have hpow : ∀ t ∈ Ico 0 M, clippedTail Z f t = rootTail Z f t ^ finrank ℝ E := by
        first
        | intro t ht
          rw [clippedTail, if_pos ht.2, rootTail_pow hdim.ne', tail]
      have hz : ∀ t, M ≤ t → clippedTail Z f t = 0 := by
        first
        | intro t ht
          exact if_neg (not_lt.mpr ht)
      have hbound := sharp_moment_bound hdim hMpos
        (rootTail Z f) (clippedTail Z f) hconc (rootTail_zero hvol hn)
        (fun t _ => rootTail_nonnegative Z f t) hpow hz
        (fun a _ => clippedTail_integrableOn hZ f 0 a)
        (fun _ ha => clippedTail_first_moment_integrableOn hZ f ha)
      have hfirst : uniformAverage Z f = ∫ t in Icc 0 M, clippedTail Z f t := by
        first
        | simpa only [uniformAverage, Nat.zero_add, pow_one, Nat.cast_zero,
            zero_add, pow_zero, one_mul] using
            moment_identity_bounded hZ hf hn hb (a := M) le_rfl 0
      have hsecond : uniformAverage Z (fun x => f x ^ 2) =
          2 * ∫ t in Icc 0 M, t * clippedTail Z f t := by
        first
        | simpa only [uniformAverage, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two,
            pow_one] using moment_identity_bounded hZ hf hn hb (a := M) le_rfl 1
      rw [hsecond, hfirst]
      exact hbound

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SharpBerwald.lean -/

/- BEGIN SOURCE: VolumePolynomials/MinkowskiAverages.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Minkowski averages of actual convex fibers

Finite-dimensional averaging is applied to finitely many support or other
monotone Minkowski functionals at a time. Blaschke compactness and the finite
intersection property then produce one actual body satisfying every average
identity simultaneously. This avoids assuming a representation theorem for
abstract support functions or continuity of fibers at the boundary.
-/

open Set Metric MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.MinkowskiAverages

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rootVolume (K : ConvexBody E) : ℝ :=
  volume.real (K : Set E) ^ ((finrank ℝ E : ℝ)⁻¹)

theorem rootVolume_nonnegative (K : ConvexBody E) : 0 ≤ rootVolume K :=
  Real.rpow_nonneg measureReal_nonneg _

theorem continuous_rootVolume : Continuous (rootVolume (E := E)) :=
  (continuous_convexBody_realMeasure volume).rpow_const
    (fun _ => Or.inr (inv_nonneg.mpr (Nat.cast_nonneg _)))

theorem rootVolume_mono {K L : ConvexBody E} (h : (K : Set E) ⊆ L) :
    rootVolume K ≤ rootVolume L :=
  Real.rpow_le_rpow measureReal_nonneg (measureReal_mono h L.isCompact.measure_ne_top)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem rootVolume_minkowski_concave (hdim : finrank ℝ E ≠ 0)
    (K L : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * rootVolume K + b * rootVolume L ≤ rootVolume (a • K + b • L) := by
  first
  | exact TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le hdim
      K.nonempty K.isCompact.measurableSet.nullMeasurableSet
      L.nonempty L.isCompact.measurableSet.nullMeasurableSet ha hb
      (a • K + b • L).isCompact.measure_ne_top

def boundedBodies (R : ℝ) : Set (ConvexBody E) :=
  {K | (K : Set E) ⊆ closedBall 0 R}

theorem boundedBodies_compact (R : ℝ) : IsCompact (boundedBodies (E := E) R) :=
  isCompact_bodies_subset_compact (isCompact_closedBall 0 R)

theorem boundedBodies_combination {R : ℝ} {K L : ConvexBody E}
    (hK : K ∈ boundedBodies R) (hL : L ∈ boundedBodies R)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • K + b • L ∈ boundedBodies R := by
  first
  | rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact convex_closedBall (0 : E) R (hK hx) (hL hy) ha hb hab

def bodyHypograph (R : ℝ) : Set (ConvexBody E × ℝ) :=
  {p | p.1 ∈ boundedBodies R ∧ 0 ≤ p.2 ∧ p.2 ≤ rootVolume p.1}

theorem bodyHypograph_compact (R : ℝ) : IsCompact (bodyHypograph (E := E) R) := by
  first
  | obtain ⟨B, hB⟩ := ((boundedBodies_compact (E := E) R).image continuous_rootVolume).bddAbove
    have heq : bodyHypograph (E := E) R =
        (boundedBodies R ×ˢ Icc 0 B) ∩ {p : ConvexBody E × ℝ | p.2 ≤ rootVolume p.1} := by
      first
      | ext p
        constructor
        · rintro ⟨hp, hz0, hzK⟩
          exact ⟨⟨hp, hz0, hzK.trans (hB ⟨p.1, hp, rfl⟩)⟩, hzK⟩
        · rintro ⟨⟨hp, hz0, _⟩, hzK⟩
          exact ⟨hp, hz0, hzK⟩
    rw [heq]
    exact ((boundedBodies_compact R).prod isCompact_Icc).inter_right
      (isClosed_le continuous_snd (continuous_rootVolume.comp continuous_fst))

def finiteObservation {ι : Type*} (F : ι → MinkowskiFunctional E)
    (p : ConvexBody E × ℝ) : (ι → ℝ) × ℝ := (fun i => F i p.1, p.2)

theorem continuous_finiteObservation {ι : Type*} (F : ι → MinkowskiFunctional E) :
    Continuous (finiteObservation F) :=
  (continuous_pi (fun i => (F i).continuous_toFun.comp continuous_fst)).prodMk continuous_snd

theorem finiteObservation_image_convex {ι : Type*} (hdim : finrank ℝ E ≠ 0)
    (F : ι → MinkowskiFunctional E) (R : ℝ) :
    Convex ℝ (finiteObservation F '' bodyHypograph R) := by
  first
  | rintro _ ⟨⟨K, x⟩, ⟨hK, hx0, hxK⟩, rfl⟩
      _ ⟨⟨L, y⟩, ⟨hL, hy0, hyL⟩, rfl⟩ a b ha hb hab
    refine ⟨(a • K + b • L, a * x + b * y), ?_, ?_⟩
    · refine ⟨boundedBodies_combination hK hL ha hb hab,
        add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0), ?_⟩
      exact (add_le_add (mul_le_mul_of_nonneg_left hxK ha)
        (mul_le_mul_of_nonneg_left hyL hb)).trans
        (rootVolume_minkowski_concave hdim K L ha hb)
    · ext i
      · exact (F i).map_convex_combination K L ha hb
      · rfl

section Fibers

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  {Z : Set U} {K : U → ConvexBody E}

theorem rootVolume_fiber_concave (hdim : finrank ℝ E ≠ 0)
    (hK : FiberConcave Z K) : ConcaveOn ℝ Z (fun y => rootVolume (K y)) := by
  first
  | refine ⟨hK.1, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (rootVolume_minkowski_concave hdim (K x) (K y) ha hb).trans
      (rootVolume_mono (hK.2 x hx y hy a b ha hb hab))

theorem functional_fiber_integrable (hZ : IsCompact Z) (hK : FiberConcave Z K)
    {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R) (φ : MinkowskiFunctional E) :
    IntegrableOn (fun y => φ (K y)) Z := by
  first
  | obtain ⟨B, hB⟩ := ((boundedBodies_compact (E := E) R).image
      φ.continuous_toFun).isBounded.exists_norm_le
    exact BerwaldMoments.bounded_concave_integrable_signed hZ
      (hK.functional_concave φ) (fun y hy => hB _ ⟨K y, hR y hy, rfl⟩)

theorem rootVolume_fiber_integrable (hdim : finrank ℝ E ≠ 0)
    (hZ : IsCompact Z) (hK : FiberConcave Z K)
    {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R) :
    IntegrableOn (fun y => rootVolume (K y)) Z := by
  first
  | obtain ⟨B, hB⟩ := ((boundedBodies_compact (E := E) R).image
      continuous_rootVolume).isBounded.exists_norm_le
    exact BerwaldMoments.bounded_concave_integrable_signed hZ
      (rootVolume_fiber_concave hdim hK) (fun y hy => hB _ ⟨K y, hR y hy, rfl⟩)

theorem finite_average_body {ι : Type*} [Fintype ι]
    (hdim : finrank ℝ E ≠ 0) (hZ : IsCompact Z) (hvol : 0 < volume.real Z)
    (hK : FiberConcave Z K) {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R)
    (F : ι → MinkowskiFunctional E) :
    ∃ A ∈ boundedBodies R,
      (∀ i, F i A = ⨍ y in Z, F i (K y)) ∧
      (⨍ y in Z, rootVolume (K y)) ≤ rootVolume A := by
  first
  | have hF (i : ι) := functional_fiber_integrable hZ hK hR (F i)
    have hFi : IntegrableOn (fun y => fun i => F i (K y)) Z := Integrable.of_eval hF
    have hroot := rootVolume_fiber_integrable hdim hZ hK hR
    have hs := finiteObservation_image_convex hdim F R
    have hsc := ((bodyHypograph_compact R).image (continuous_finiteObservation F)).isClosed
    have hvol0 : volume Z ≠ 0 := by
      first
      | intro hz
        simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hvol
    have hp := hs.set_average_mem hsc hvol0 hZ.measure_ne_top
      (show ∀ᵐ y ∂volume.restrict Z,
        (fun i => F i (K y), rootVolume (K y)) ∈ finiteObservation F '' bodyHypograph R from by
        filter_upwards [ae_restrict_mem hZ.measurableSet] with y hy
        exact ⟨(K y, rootVolume (K y)), ⟨hR y hy, rootVolume_nonnegative _, le_rfl⟩, rfl⟩)
      (hFi.prodMk hroot)
    rw [average_pair hFi hroot] at hp
    obtain ⟨⟨A, z⟩, ⟨hA, hz0, hzA⟩, hobs⟩ := hp
    have hz : z = ⨍ y in Z, rootVolume (K y) := congrArg Prod.snd hobs
    refine ⟨A, hA, ?_, hz ▸ hzA⟩
    intro i
    have hi := congrArg (fun p : (ι → ℝ) × ℝ => p.1 i) hobs
    simpa only [finiteObservation, setAverage_eq, Pi.smul_apply, smul_eq_mul,
      eval_integral hF i] using hi

/-- Existence of a single actual Minkowski average, with the Brunn--Minkowski
lower bound and all continuous monotone Minkowski functionals preserved. -/
theorem exists_average_body (hdim : finrank ℝ E ≠ 0)
    (hZ : IsCompact Z) (hvol : 0 < volume.real Z) (hK : FiberConcave Z K)
    {R : ℝ} (hR : ∀ y ∈ Z, K y ∈ boundedBodies R) :
    ∃ A ∈ boundedBodies R,
      (∀ φ : MinkowskiFunctional E, φ A = ⨍ y in Z, φ (K y)) ∧
      (⨍ y in Z, rootVolume (K y)) ≤ rootVolume A := by
  first
  | classical
    let q : ℝ := ⨍ y in Z, rootVolume (K y)
    let C : Set (ConvexBody E) := boundedBodies R ∩ {A | q ≤ rootVolume A}
    have hC : IsCompact C := (boundedBodies_compact R).inter_right
      (isClosed_le continuous_const continuous_rootVolume)
    let T : MinkowskiFunctional E → Set (ConvexBody E) :=
      fun φ => {A | φ A = ⨍ y in Z, φ (K y)}
    have hT (φ : MinkowskiFunctional E) : IsClosed (T φ) :=
      isClosed_eq φ.continuous_toFun continuous_const
    have hfinite (s : Finset (MinkowskiFunctional E)) : (C ∩ ⋂ φ ∈ s, T φ).Nonempty := by
      first
      | obtain ⟨A, hA, heq, hq⟩ := finite_average_body hdim hZ hvol hK hR
          (fun φ : s => φ.1)
        refine ⟨A, ⟨hA, hq⟩, ?_⟩
        simp only [mem_iInter]
        intro φ hφ
        exact heq ⟨φ, hφ⟩
    obtain ⟨A, hA, hAT⟩ := hC.inter_iInter_nonempty T hT hfinite
    exact ⟨A, hA.1, fun φ => mem_iInter.mp hAT φ, hA.2⟩

theorem average_body_unique {A B : ConvexBody E}
    (hA : ∀ φ : MinkowskiFunctional E, φ A = ⨍ y in Z, φ (K y))
    (hB : ∀ φ : MinkowskiFunctional E, φ B = ⨍ y in Z, φ (K y)) : A = B :=
  MinkowskiFunctional.separating (fun φ => (hA φ).trans (hB φ).symm)

end Fibers

end VolumePolynomials.MinkowskiAverages
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MinkowskiAverages.lean -/

/- BEGIN SOURCE: VolumePolynomials/ConvexFibers.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Fibers of compact convex sets and their planar average

The fibers are literal sections of a compact convex subset of a product.
Only nonempty fibers over the actual projection enter the averaging measure.
-/

open Set Metric MeasureTheory Module
open scoped Pointwise



namespace VolumePolynomials.MinkowskiAverages

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]

open ConvexFibers

theorem uniformAverage_eq_setAverage (Z : Set U) (f : U → ℝ) :
    uniformAverage Z f = ⨍ y in Z, f y := by
  first
  | rw [uniformAverage, setAverage_eq, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem rootVolume_sq_of_finrank_two (hdim : finrank ℝ E = 2) (K : ConvexBody E) :
    rootVolume K ^ 2 = volume.real (K : Set E) := by
  first
  | have hn : finrank ℝ E ≠ 0 := by omega
    have h := Real.rpow_inv_natCast_pow (x := volume.real (K : Set E)) measureReal_nonneg hn
    simpa only [rootVolume, hdim] using h

/-- The geometric assertion of Lemma 6.1 for an arbitrary compact convex
total set, with an actual Minkowski average. It preserves support values,
widths, and every other continuous monotone Minkowski functional. -/
theorem planar_average_area (hdim : finrank ℝ E = 2) (hbase : 0 < finrank ℝ U)
    (C : ConvexBody (E × U)) (hvol : 0 < volume.real (projection C)) :
    ∃ A : ConvexBody E,
      (∀ φ : MinkowskiFunctional E,
        φ A = uniformAverage (projection C) (fun y => φ (fiberBody C y))) ∧
      (berwaldConstant (finrank ℝ U))⁻¹ *
          uniformAverage (projection C) (fun y => volume.real (fiberBody C y : Set E)) ≤
        volume.real (A : Set E) := by
  first
  | obtain ⟨R, hR⟩ := fibers_uniformly_bounded C
    have hn : finrank ℝ E ≠ 0 := by omega
    have hZ := projection_compact C
    have hK := fiberBody_concave C
    obtain ⟨A, hA, hφ, hroot⟩ := exists_average_body hn hZ hvol hK hR
    refine ⟨A, ?_, ?_⟩
    · intro φ
      rw [uniformAverage_eq_setAverage]
      exact hφ φ
    · let f : U → ℝ := fun y => rootVolume (fiberBody C y)
      have hf : ConcaveOn ℝ (projection C) f := rootVolume_fiber_concave hn hK
      have hfn : ∀ y ∈ projection C, 0 ≤ f y := fun y _ => rootVolume_nonnegative _
      have hfb : BddAbove (f '' projection C) := by
        first
        | apply (((boundedBodies_compact (E := E) R).image continuous_rootVolume).bddAbove).mono
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨fiberBody C y, hR y hy, rfl⟩
      have hB := sharp_berwald_second_moment hbase hZ hvol hf hfn hfb
      have hmean0 : 0 ≤ uniformAverage (projection C) f := by
        first
        | unfold uniformAverage
          apply div_nonneg _ hvol.le
          apply integral_nonneg_of_ae
          filter_upwards [ae_restrict_mem hZ.measurableSet] with y hy
          exact hfn y hy
      have hmean : uniformAverage (projection C) f ≤ rootVolume A := by
        first
        | rw [uniformAverage_eq_setAverage]
          exact hroot
      have hmean2 : uniformAverage (projection C) f ^ 2 ≤ volume.real (A : Set E) := by
        first
        | rw [← rootVolume_sq_of_finrank_two hdim A]
          nlinarith [rootVolume_nonnegative A]
      have hsecond : uniformAverage (projection C) (fun y => f y ^ 2) =
          uniformAverage (projection C) (fun y => volume.real (fiberBody C y : Set E)) := by
        first
        | congr 1
          funext y
          exact rootVolume_sq_of_finrank_two hdim _
      have hc : 0 < berwaldConstant (finrank ℝ U) := by
        first
        | unfold berwaldConstant
          positivity
      rw [hsecond] at hB
      have hfinal := hB.trans (mul_le_mul_of_nonneg_left hmean2 hc.le)
      have hh := mul_le_mul_of_nonneg_left hfinal (inv_pos.mpr hc).le
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh

end VolumePolynomials.MinkowskiAverages
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ConvexFibers.lean -/

/- BEGIN SOURCE: VolumePolynomials/FirstVariableCoefficient.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Extracting the first added-body coefficient by actual differentiation

The coefficient in the first variable is a polynomial in all the remaining
variables. Its evaluation is the genuine derivative at zero, and its
squarefree coefficient is the squarefree coefficient of the original volume
polynomial. These identities justify coefficient extraction after first
variation without any assumption about a mixed-volume functional.
-/

noncomputable section
open Set Filter MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials

def firstVariableCoefficient {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ := (MvPolynomial.finSuccEquiv ℝ n p).coeff 1

theorem firstVariableCoefficient_coeff {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (m : Fin n →₀ ℕ) :
    (firstVariableCoefficient p).coeff m = p.coeff (m.cons 1) :=
  MvPolynomial.finSuccEquiv_coeff_coeff m p 1

theorem squarefreeExponent_cons (n : ℕ) :
    (squarefreeExponent n).cons 1 = squarefreeExponent (n + 1) := by
  first
  | ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem firstVariableCoefficient_squarefree {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    (firstVariableCoefficient p).coeff (squarefreeExponent n) =
      p.coeff (squarefreeExponent (n + 1)) := by
  first
  | rw [firstVariableCoefficient_coeff, squarefreeExponent_cons]

theorem hasDerivAt_eval_firstVariableCoefficient {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (t : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (Fin.cons s t) p)
      (MvPolynomial.eval t (firstVariableCoefficient p)) 0 := by
  first
  | let q : Polynomial ℝ :=
      Polynomial.map (MvPolynomial.eval t) (MvPolynomial.finSuccEquiv ℝ n p)
    have he (s : ℝ) : q.eval s = MvPolynomial.eval (Fin.cons s t) p :=
      (MvPolynomial.eval_eq_eval_mv_eval' t s p).symm
    have hd : q.derivative.eval 0 = MvPolynomial.eval t (firstVariableCoefficient p) := by
      first
      | rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
        simp only [Nat.zero_add, Nat.cast_zero, Nat.cast_one, zero_add, mul_one, q,
          Polynomial.coeff_map, firstVariableCoefficient]
    simpa only [he, hd] using q.hasDerivAt 0

section Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem volumePolynomial_eval_cons {n : ℕ} (A : ConvexBody E)
    (K : Fin n → ConvexBody E) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {s : ℝ} (hs : 0 ≤ s) :
    MvPolynomial.eval (Fin.cons s t) (volumePolynomial μ (Fin.cons A K)) =
      μ.real ((↑(∑ i, t i • K i) : Set E) + s • (A : Set E)) := by
  first
  | rw [volumePolynomial_eval μ (Fin.cons A K) (Fin.cons s t)
      (by intro i; exact Fin.cases hs ht i)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ConvexBody.coe_add,
      ConvexBody.coe_smul, add_comm]

/-- A genuine right derivative of actual Minkowski volume identifies the
first-variable coefficient, for every fixed nonnegative background tuple. -/
theorem eval_firstVariableCoefficient_eq_of_volume_derivative {n : ℕ}
    (A : ConvexBody E) (K : Fin n → ConvexBody E)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {c : ℝ}
    (hc : HasDerivWithinAt
      (fun s : ℝ => μ.real ((↑(∑ i, t i • K i) : Set E) + s • (A : Set E))) c (Ioi 0) 0) :
    MvPolynomial.eval t (firstVariableCoefficient (volumePolynomial μ (Fin.cons A K))) = c := by
  first
  | let p := volumePolynomial μ (Fin.cons A K)
    have hp := (hasDerivAt_eval_firstVariableCoefficient p t).hasDerivWithinAt
      (s := Ioi (0 : ℝ))
    have he := volumePolynomial_eval_cons μ A K t ht (s := 0) le_rfl
    have hv : HasDerivWithinAt
        (fun s : ℝ => μ.real ((↑(∑ i, t i • K i) : Set E) + s • (A : Set E)))
        (MvPolynomial.eval t (firstVariableCoefficient p)) (Ioi 0) 0 :=
      hp.congr (fun s hs => (volumePolynomial_eval_cons μ A K t ht hs.le).symm) he.symm
    have h₁ := (hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hv
    have h₂ := (hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hc
    exact tendsto_nhds_unique h₁ h₂

end Volume
end VolumePolynomials
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FirstVariableCoefficient.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarErosion.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Removing an actual horizontal segment from a planar convex body

The eroded set is the literal intersection of the body with its translate
by the negative segment endpoint. If the bottom and top support faces each
contain a horizontal segment of length `r`, convexity supplies such a
segment in every nonempty horizontal fiber. Compact interval fibers then
prove the exact Minkowski decomposition, including zero height and `r = 0`.
-/

noncomputable section
open Set
open scoped Pointwise

namespace VolumePolynomials.PlanarErosion

open PlanarExtrusion

def erosion (C : Set (ℝ × ℝ)) (r : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ C ∧ p + (r, 0) ∈ C}

theorem erosion_subset (C : Set (ℝ × ℝ)) (r : ℝ) : erosion C r ⊆ C :=
  fun _ hp => hp.1

theorem erosion_compact {C : Set (ℝ × ℝ)} (hC : IsCompact C) (r : ℝ) :
    IsCompact (erosion C r) := by
  first
  | exact hC.inter_right (hC.isClosed.preimage (continuous_id.add continuous_const))

theorem erosion_convex {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) (r : ℝ) :
    Convex ℝ (erosion C r) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
    have h := hC hx.2 hy.2 ha hb hab
    have he : a • (x + (r, 0)) + b • (y + (r, 0)) =
        (a • x + b • y) + (r, 0) := by
      rw [smul_add, smul_add]
      calc
        _ = (a • x + b • y) + (a • (r, 0) + b • (r, 0)) := by abel
        _ = _ := by rw [← add_smul, hab, one_smul]
    rwa [he] at h

theorem fiber_erosion (C : Set (ℝ × ℝ)) (r y : ℝ) :
    fiber (erosion C r) y = fiber C y ∩ {x : ℝ | x + r ∈ fiber C y} := by
  first
  | ext x
    change ((x, y) ∈ C ∧ (x, y) + (r, 0) ∈ C) ↔
      ((x, y) ∈ C ∧ (x + r, y) ∈ C)
    simp only [Prod.mk_add_mk, add_zero]

theorem fiber_erosion_eq_interval {C : Set (ℝ × ℝ)} {a b r y : ℝ}
    (hr : 0 ≤ r) (hI : fiber C y = Icc a b) :
    fiber (erosion C r) y = Icc a (b - r) := by
  first
  | rw [fiber_erosion, hI]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨ha, hb⟩, ⟨har, hbr⟩⟩
      exact ⟨ha, by linarith⟩
    · rintro ⟨ha, hb⟩
      exact ⟨⟨ha, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A segment in each nonempty fiber is sufficient for the exact erosion
identity; compactness and convexity identify all fibers as closed intervals. -/
theorem eq_erosion_add_horizontal_of_fiber_segments
    {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hc : Convex ℝ C) {r : ℝ} (hr : 0 ≤ r)
    (hsegments : ∀ y ∈ projection C, ∃ a : ℝ, (a, y) ∈ C ∧ (a + r, y) ∈ C) :
    C = erosion C r + horizontal r := by
  first
  | ext p
    rcases p with ⟨x, y⟩
    change x ∈ fiber C y ↔ x ∈ fiber (erosion C r + horizontal r) y
    rw [fiber_add_horizontal]
    by_cases hne : (fiber C y).Nonempty
    · have hcompact := fiber_compact hC y
      have hI : fiber C y = Icc (sInf (fiber C y)) (sSup (fiber C y)) :=
        eq_Icc_of_connected_compact
          ⟨hne, Real.convex_iff_isPreconnected.mp (fiber_convex hc y)⟩ hcompact
      obtain ⟨a, ha, har⟩ := hsegments y ((fiber_nonempty_iff C y).mp hne)
      have hlo : sInf (fiber C y) ≤ a := csInf_le hcompact.bddBelow ha
      have hhi : a + r ≤ sSup (fiber C y) := le_csSup hcompact.bddAbove har
      have hwidth : sInf (fiber C y) ≤ sSup (fiber C y) - r := by linarith
      rw [fiber_erosion_eq_interval hr hI, Icc_add_Icc hwidth hr]
      simp only [add_zero, sub_add_cancel]
      exact Iff.mp Set.ext_iff hI x
    · have hI : fiber C y = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hE : fiber (erosion C r) y = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hne ⟨z, hz.1⟩
      simp only [hI, hE, Set.empty_add]

/-- The two extreme horizontal segments interpolate to a segment in every
intermediate horizontal slice. No positive-height hypothesis is needed. -/
theorem fiber_segment_of_extreme_endpoints
    {C : Set (ℝ × ℝ)} (hc : Convex ℝ C)
    {lo hi r a b y : ℝ} (hy : lo ≤ y ∧ y ≤ hi)
    (ha : (a, lo) ∈ C) (har : (a + r, lo) ∈ C)
    (hb : (b, hi) ∈ C) (hbr : (b + r, hi) ∈ C) :
    ∃ z : ℝ, (z, y) ∈ C ∧ (z + r, y) ∈ C := by
  first
  | by_cases heq : lo = hi
    · have hylo : y = lo := by linarith
      subst y
      exact ⟨a, ha, har⟩
    · have hheight : 0 < hi - lo := by
        have hle := hy.1.trans hy.2
        exact sub_pos.mpr (lt_of_le_of_ne hle heq)
      let t : ℝ := (y - lo) / (hi - lo)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hy.1) hheight.le
      have ht1 : t ≤ 1 := (div_le_one hheight).mpr (by linarith)
      have hty : t * (hi - lo) = y - lo := div_mul_cancel₀ _ hheight.ne'
      let z : ℝ := (1 - t) * a + t * b
      have hpoint : ((1 - t) • (a, lo) + t • (b, hi) : ℝ × ℝ) = (z, y) := by
        apply Prod.ext
        · rfl
        · change (1 - t) * lo + t * hi = y
          nlinarith [hty]
      have hpointR : ((1 - t) • (a + r, lo) + t • (b + r, hi) : ℝ × ℝ) = (z + r, y) := by
        apply Prod.ext
        · change (1 - t) * (a + r) + t * (b + r) = z + r
          dsimp only [z]
          ring
        · change (1 - t) * lo + t * hi = y
          nlinarith [hty]
      refine ⟨z, ?_, ?_⟩
      · exact hpoint ▸ hc ha hb (sub_nonneg.mpr ht1) ht0 (by ring)
      · exact hpointR ▸ hc har hbr (sub_nonneg.mpr ht1) ht0 (by ring)

theorem eq_erosion_add_horizontal_of_vertical_bounds
    {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hc : Convex ℝ C)
    {lo hi r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ p ∈ C, lo ≤ p.2 ∧ p.2 ≤ hi)
    (hlo : ∃ a : ℝ, (a, lo) ∈ C ∧ (a + r, lo) ∈ C)
    (hhi : ∃ b : ℝ, (b, hi) ∈ C ∧ (b + r, hi) ∈ C) :
    C = erosion C r + horizontal r := by
  first
  | apply eq_erosion_add_horizontal_of_fiber_segments hC hc hr
    intro y hy
    obtain ⟨p, hp, hpy⟩ := hy
    obtain ⟨a, ha, har⟩ := hlo
    obtain ⟨b, hb, hbr⟩ := hhi
    exact fiber_segment_of_extreme_endpoints hc (hpy ▸ hbound p hp) ha har hb hbr

/-- The support-face formulation, with the actual minimum and maximum of
the vertical projection. These hypotheses say precisely that both horizontal
support faces contain a translate of the segment being removed. -/
theorem eq_erosion_add_horizontal_of_extreme_fibers
    {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hc : Convex ℝ C) (hne : C.Nonempty)
    {r : ℝ} (hr : 0 ≤ r)
    (hlo : ∃ a : ℝ, (a, sInf (projection C)) ∈ C ∧ (a + r, sInf (projection C)) ∈ C)
    (hhi : ∃ b : ℝ, (b, sSup (projection C)) ∈ C ∧ (b + r, sSup (projection C)) ∈ C) :
    C = erosion C r + horizontal r := by
  first
  | have hprojection : IsCompact (projection C) := hC.image continuous_snd
    apply eq_erosion_add_horizontal_of_vertical_bounds hC hc hr _ hlo hhi
    intro p hp
    have hmem : p.2 ∈ projection C := ⟨p, hp, rfl⟩
    exact ⟨csInf_le hprojection.bddBelow hmem, le_csSup hprojection.bddAbove hmem⟩

def erosionBody (C : ConvexBody (ℝ × ℝ)) (r : ℝ) (hne : (erosion (C : Set _) r).Nonempty) :
    ConvexBody (ℝ × ℝ) where
  carrier := erosion (C : Set _) r
  convex' := erosion_convex C.convex r
  isCompact' := erosion_compact C.isCompact r
  nonempty' := hne

theorem erosion_nonempty_of_bottom_segment
    {C : Set (ℝ × ℝ)} {r : ℝ}
    (hlo : ∃ a : ℝ, (a, sInf (projection C)) ∈ C ∧ (a + r, sInf (projection C)) ∈ C) :
    (erosion C r).Nonempty := by
  first
  | obtain ⟨a, ha, har⟩ := hlo
    refine ⟨(a, sInf (projection C)), ha, ?_⟩
    simpa only [Prod.mk_add_mk, add_zero] using har

end VolumePolynomials.PlanarErosion
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarErosion.lean -/

/- BEGIN SOURCE: VolumePolynomials/HyperbolicForm.lean -/
section

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The algebraic part of the Alexandrov–Fenchel argument

This proves the reverse Cauchy–Schwarz implication for a symmetric bilinear form
from negativity on one orthogonal hyperplane. It is only an algebraic dependency:
the mixed-volume form must still be constructed and its hyperplane inequality
proved geometrically before applying this to the binary realization theorem.

The reduction is the quadratic-form step used in Shenfeld–van Handel,
*Mixed volumes and the Bochner method*, Lemma 2.9. The proof below is direct
bilinear algebra and does not assume a spectral theorem or a geometric inequality.
-/

namespace VolumePolynomials

open LinearMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Negativity on one orthogonal hyperplane implies negativity on the
orthogonal hyperplane of any vector with positive quadratic value. -/
theorem bilinear_nonpos_on_positive_orthogonal
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ x y, B x y = B y x) (e : E)
    (he : ∀ x, B x e = 0 → B x x ≤ 0)
    {y : E} (hy : 0 < B y y) {x : E} (hxy : B x y = 0) : B x x ≤ 0 := by
  first
  | by_contra hx
    have hxpos : 0 < B x x := lt_of_not_ge hx
    let z : E := B y e • x - B x e • y
    have hze : B z e = 0 := by
      simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
      ring
    have hzz := he z hze
    have hyx : B y x = 0 := (hB y x).trans hxy
    have hzexp : B z z = (B y e) ^ 2 * B x x + (B x e) ^ 2 * B y y := by
      simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hxy, hyx]
      ring
    rw [hzexp] at hzz
    have hterm : 0 ≤ (B x e) ^ 2 * B y y := mul_nonneg (sq_nonneg _) hy.le
    have hye : B y e = 0 := by
      by_contra hne
      have hpos := mul_pos (sq_pos_of_ne_zero hne) hxpos
      linarith
    exact (not_lt_of_ge (he y hye)) hy

/-- The reverse Cauchy–Schwarz inequality, including the zero quadratic-value
boundary case, follows from the one-positive-direction condition. -/
theorem bilinear_reverse_cauchy_schwarz
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ x y, B x y = B y x) (e : E)
    (he : ∀ x, B x e = 0 → B x x ≤ 0)
    (x y : E) (hy : 0 ≤ B y y) : B x x * B y y ≤ (B x y) ^ 2 := by
  first
  | rcases hy.eq_or_lt with hyzero | hypos
    · rw [← hyzero, mul_zero]
      exact sq_nonneg _
    · let z : E := B y y • x - B x y • y
      have hzy : B z y = 0 := by
        simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
        ring
      have hzz := bilinear_nonpos_on_positive_orthogonal B hB e he hypos hzy
      have hzexp : B z z = B y y * (B x x * B y y - (B x y) ^ 2) := by
        simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
          LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hB y x]
        ring
      rw [hzexp] at hzz
      by_contra h
      have hpos := mul_pos hypos (sub_pos.mpr (lt_of_not_ge h))
      exact (not_lt_of_ge hzz) hpos

/-- A single positive reference vector is enough to test the hyperplane
condition by its reverse Cauchy–Schwarz inequality. -/
theorem bilinear_hyperplane_iff_reference_inequality
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ x y, B x y = B y x) (e : E)
    (he : 0 < B e e) :
    (∀ x, B x e = 0 → B x x ≤ 0) ↔
      ∀ x, B x x * B e e ≤ (B x e) ^ 2 := by
  first
  | constructor
    · intro h x
      exact bilinear_reverse_cauchy_schwarz B hB e h x e he.le
    · intro h x hxe
      have hx := h x
      rw [hxe, zero_pow (by decide : 2 ≠ 0)] at hx
      by_contra hxx
      exact (not_lt_of_ge hx) (mul_pos (lt_of_not_ge hxx) he)

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HyperbolicForm.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarMixedForm.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The actual planar mixed-area form

Mixed area is the normalized coefficient of the genuine volume polynomial.
Brunn--Minkowski proves its reverse Cauchy--Schwarz inequality. Every finite
family of convex bodies then gives a symmetric bilinear form on its real
coefficient space; positivity of coefficients is removed by an explicit shift.
No virtual-body existence or unproved Alexandrov--Fenchel assertion is used.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarMixedForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedArea (A B : ConvexBody E) : ℝ := mixedVolume μ ![A, B]

theorem mixedArea_nonnegative (A B : ConvexBody E) : 0 ≤ mixedArea μ A B :=
  mixedVolume_nonnegative μ _

theorem mixedArea_symm (A B : ConvexBody E) : mixedArea μ A B = mixedArea μ B A := by
  first
  | have h := mixedVolume_reindex μ ![A, B] (Equiv.swap (0 : Fin 2) 1)
    have he : (fun i => ![A, B] (Equiv.swap (0 : Fin 2) 1 i)) = ![B, A] := by
      first
      | funext i
        fin_cases i <;> simp
    rw [he] at h
    exact h.symm

theorem mixedArea_add_left (A B C : ConvexBody E) :
    mixedArea μ (A + B) C = mixedArea μ A C + mixedArea μ B C := by
  first
  | simpa only [mixedArea, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_add μ ![A, C] 0 A B

theorem mixedArea_add_right (A B C : ConvexBody E) :
    mixedArea μ A (B + C) = mixedArea μ A B + mixedArea μ A C := by
  first
  | rw [mixedArea_symm μ A, mixedArea_add_left,
      mixedArea_symm μ B A, mixedArea_symm μ C A]

theorem mixedArea_smul_left (A B : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedArea μ (r • A) B = r * mixedArea μ A B := by
  first
  | simpa only [mixedArea, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_smul μ ![A, B] 0 A hr

theorem mixedArea_smul_right (A B : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedArea μ A (r • B) = r * mixedArea μ A B := by
  first
  | rw [mixedArea_symm, mixedArea_smul_left μ B A hr, mixedArea_symm μ B A]

@[simp] theorem mixedArea_zero_left (A : ConvexBody E) : mixedArea μ 0 A = 0 := by
  first
  | simpa only [mixedArea, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_zero_arg μ ![A, A] 0

@[simp] theorem mixedArea_zero_right (A : ConvexBody E) : mixedArea μ A 0 = 0 := by
  first
  | rw [mixedArea_symm, mixedArea_zero_left]

theorem mixedArea_translate (A B : ConvexBody E) (v w : E) :
    mixedArea μ (translateBody v A) (translateBody w B) = mixedArea μ A B := by
  first
  | have h := mixedVolume_translate μ ![A, B] ![v, w]
    have he : (fun i : Fin 2 => translateBody (![v, w] i) (![A, B] i)) =
        ![translateBody v A, translateBody w B] := by
      first
      | funext i
        fin_cases i <;> rfl
    simpa only [he, mixedArea] using h

theorem mixedArea_translate_right (A B : ConvexBody E) (v : E) :
    mixedArea μ A (translateBody v B) = mixedArea μ A B := by
  first
  | simpa only [translateBody_zero] using mixedArea_translate μ A B 0 v

@[simp] theorem mixedArea_point_left (v : E) (A : ConvexBody E) :
    mixedArea μ (pointBody v) A = 0 := by
  first
  | have h := mixedArea_translate μ (0 : ConvexBody E) A v 0
    rw [translateBody_zero] at h
    change mixedArea μ (pointBody v + 0) A = _ at h
    simpa only [add_zero, mixedArea_zero_left] using h

theorem mixedArea_diagonal (hdim : finrank ℝ E = 2) (A : ConvexBody E) :
    mixedArea μ A A = μ.real (A : Set E) := by
  first
  | have he : (![A, A] : Fin 2 → ConvexBody E) = fun _ => A := by
      first
      | funext i
        fin_cases i <;> rfl
    simpa only [mixedArea, he] using mixedVolume_diagonal μ hdim A

theorem area_add (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    μ.real (A + B : ConvexBody E) =
      μ.real (A : Set E) + 2 * mixedArea μ A B + μ.real (B : Set E) := by
  first
  | rw [← mixedArea_diagonal μ hdim, mixedArea_add_left,
      mixedArea_add_right, mixedArea_add_right, mixedArea_symm μ B A,
      mixedArea_diagonal μ hdim, mixedArea_diagonal μ hdim]
    ring

/-- Brunn--Minkowski transported through an actual continuous linear coordinate
equivalence. It applies to every norm on the two-dimensional ambient space and
every specified additive Haar measure. -/
theorem sqrt_area_add (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    Real.sqrt (μ.real (A : Set E)) + Real.sqrt (μ.real (B : Set E)) ≤
      Real.sqrt (μ.real (A + B : ConvexBody E)) := by
  first
  | letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := inferInstanceAs (Measure.IsAddHaarMeasure μ)
    let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      ContinuousLinearEquiv.ofFinrankEq (hdim.trans finrank_euclideanSpace_fin.symm)
    let C := mapBody T.toContinuousLinearMap A
    let D := mapBody T.toContinuousLinearMap B
    let c : ℝ := LinearFrame.volumeFactor T
    have hc : 0 ≤ c := NNReal.coe_nonneg _
    have hscale (K : ConvexBody E) :
        μ.real (K : Set E) = c * volume.real
          (mapBody T.toContinuousLinearMap K : Set (EuclideanSpace ℝ (Fin 2))) := by
      first
      | rw [coe_mapBody, ContinuousLinearEquiv.coe_coe]
        exact LinearFrame.realVolume_eq_factor_mul_image T (K : Set E)
    have h := TauCeti.volume_real_rpow_add_volume_real_rpow_le
      (E := EuclideanSpace ℝ (Fin 2)) (by simp) C.nonempty
      C.isCompact.measurableSet.nullMeasurableSet D.nonempty
      D.isCompact.measurableSet.nullMeasurableSet (C + D).isCompact.measure_ne_top
    have hexp : (finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹ = 1 / 2 := by simp
    have h' : Real.sqrt (volume.real (C : Set (EuclideanSpace ℝ (Fin 2)))) +
        Real.sqrt (volume.real (D : Set (EuclideanSpace ℝ (Fin 2)))) ≤
        Real.sqrt (volume.real
          ((C + D : ConvexBody (EuclideanSpace ℝ (Fin 2))) :
            Set (EuclideanSpace ℝ (Fin 2)))) := by
      first
      | simpa only [hexp, ← Real.sqrt_eq_rpow, ConvexBody.coe_add] using h
    rw [hscale A, hscale B, hscale (A + B), mapBody_add]
    simp only [Real.sqrt_mul hc]
    simpa only [mul_add, C, D] using mul_le_mul_of_nonneg_left h' (Real.sqrt_nonneg c)

/-- The planar Minkowski inequality for literal Haar area and literal mixed area. -/
theorem sqrt_area_mul_le_mixedArea (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    Real.sqrt (μ.real (A : Set E)) * Real.sqrt (μ.real (B : Set E)) ≤
      mixedArea μ A B := by
  first
  | have h := sqrt_area_add μ hdim A B
    have hs := mul_self_le_mul_self (by positivity :
        0 ≤ Real.sqrt (μ.real (A : Set E)) + Real.sqrt (μ.real (B : Set E))) h
    have hA := Real.sq_sqrt (show 0 ≤ μ.real (A : Set E) from measureReal_nonneg)
    have hB := Real.sq_sqrt (show 0 ≤ μ.real (B : Set E) from measureReal_nonneg)
    have hsum := Real.sq_sqrt (show 0 ≤ μ.real (A + B : ConvexBody E) from measureReal_nonneg)
    have harea := area_add μ hdim A B
    nlinarith

theorem minkowski_squared (hdim : finrank ℝ E = 2) (A B : ConvexBody E) :
    μ.real (A : Set E) * μ.real (B : Set E) ≤ mixedArea μ A B ^ 2 := by
  first
  | have h := sqrt_area_mul_le_mixedArea μ hdim A B
    have hs := mul_self_le_mul_self (by positivity :
      0 ≤ Real.sqrt (μ.real (A : Set E)) * Real.sqrt (μ.real (B : Set E))) h
    have he : (Real.sqrt (μ.real (A : Set E)) * Real.sqrt (μ.real (B : Set E))) ^ 2 =
        μ.real (A : Set E) * μ.real (B : Set E) := by
      first
      | rw [mul_pow, Real.sq_sqrt measureReal_nonneg, Real.sq_sqrt measureReal_nonneg]
    nlinarith

theorem mixedArea_sum_left {ι : Type*} (s : Finset ι)
    (K : ι → ConvexBody E) (B : ConvexBody E) :
    mixedArea μ (∑ i ∈ s, K i) B = ∑ i ∈ s, mixedArea μ (K i) B := by
  first
  | classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.sum_insert hi, mixedArea_add_left, ih,
        Finset.sum_insert hi]

theorem mixedArea_sum_right {ι : Type*} (s : Finset ι)
    (K : ι → ConvexBody E) (A : ConvexBody E) :
    mixedArea μ A (∑ i ∈ s, K i) = ∑ i ∈ s, mixedArea μ A (K i) := by
  first
  | rw [mixedArea_symm, mixedArea_sum_left]
    exact Finset.sum_congr rfl (fun i _ => mixedArea_symm μ (K i) A)

def form {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) : LinearMap.BilinForm ℝ (ι → ℝ) :=
  Matrix.toBilin'Aux (fun i j => mixedArea μ (K i) (K j))

theorem form_apply {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) (x y : ι → ℝ) :
    form μ K x y = ∑ i, ∑ j, x i * mixedArea μ (K i) (K j) * y j := by
  first
  | classical
    exact Matrix.toBilin'_apply _ _ _

@[simp] theorem form_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ConvexBody E) (i j : ι) :
    form μ K (Pi.single i 1) (Pi.single j 1) = mixedArea μ (K i) (K j) :=
  Matrix.toBilin'Aux_single _ _ _

set_option maxHeartbeats 800000 in
theorem form_one_positive_of_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ConvexBody E) (i j : ι) (hij : 0 < mixedArea μ (K i) (K j)) :
    0 < form μ K (fun _ : ι => (1 : ℝ)) (fun _ : ι => (1 : ℝ)) := by
  first
  | rw [form_apply]
    simp only [one_mul, mul_one]
    have hrow : mixedArea μ (K i) (K j) ≤ ∑ k, mixedArea μ (K i) (K k) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun k : ι => mixedArea μ (K i) (K k))
        (fun k _ => mixedArea_nonnegative μ (K i) (K k)) (Finset.mem_univ j)
    have hsum : (∑ k, mixedArea μ (K i) (K k)) ≤
        ∑ l, ∑ k, mixedArea μ (K l) (K k) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun l : ι => ∑ k, mixedArea μ (K l) (K k))
        (fun l _ => Finset.sum_nonneg (fun k _ =>
          mixedArea_nonnegative μ (K l) (K k))) (Finset.mem_univ i)
    exact hij.trans_le (hrow.trans hsum)

theorem form_symmetric {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (x y : ι → ℝ) : form μ K x y = form μ K y x := by
  first
  | simp only [form_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mixedArea_symm μ (K j) (K i)]
    ring

theorem form_eq_mixedArea {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    form μ K x y = mixedArea μ (∑ i, x i • K i) (∑ i, y i • K i) := by
  first
  | rw [form_apply, mixedArea_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [mixedArea_smul_left μ _ _ (hx i), mixedArea_sum_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mixedArea_smul_right μ _ _ (hy j)]
    ring

theorem form_one_one {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) :
    form μ K (fun _ => 1) (fun _ => 1) = mixedArea μ (∑ i, K i) (∑ i, K i) := by
  first
  | simpa only [one_smul] using
      form_eq_mixedArea μ K (fun _ => 1) (fun _ => 1) (fun _ => zero_le_one)
        (fun _ => zero_le_one)

/-- The one-positive-direction property in the complete real coefficient space.
All signed vectors are covered by shifting them into the nonnegative orthant. -/
theorem form_nonpositive_on_orthogonal {ι : Type*} [Fintype ι]
    (hdim : finrank ℝ E = 2) (K : ι → ConvexBody E)
    (hpositive : 0 < form μ K (fun _ => 1) (fun _ => 1))
    (x : ι → ℝ) (hx : form μ K x (fun _ => 1) = 0) :
    form μ K x x ≤ 0 := by
  first
  | classical
    let t : ℝ := ∑ i, |x i|
    let e : ι → ℝ := fun _ => 1
    let y : ι → ℝ := x + t • e
    have hy (i : ι) : 0 ≤ y i := by
      first
      | have hi : |x i| ≤ t := Finset.single_le_sum (fun j _ => abs_nonneg (x j))
          (Finset.mem_univ i)
        dsimp only [y, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
        linarith [neg_abs_le (x i)]
    have he : ∀ i, 0 ≤ e i := fun _ => zero_le_one
    have h := minkowski_squared μ hdim (∑ i, y i • K i) (∑ i, e i • K i)
    rw [← mixedArea_diagonal μ hdim, ← mixedArea_diagonal μ hdim,
      ← form_eq_mixedArea μ K y y hy hy, ← form_eq_mixedArea μ K e e he he,
      ← form_eq_mixedArea μ K y e hy he] at h
    have hex : form μ K e x = 0 := (form_symmetric μ K e x).trans hx
    have hxe : form μ K x e = 0 := hx
    simp only [y, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hxe, hex, mul_zero, zero_add, add_zero] at h
    have hprod : form μ K x x * form μ K e e ≤ 0 := by nlinarith
    by_contra hxx
    exact (not_lt_of_ge hprod) (mul_pos (lt_of_not_ge hxx) hpositive)

/-- The planar Alexandrov--Fenchel inequality for every real coefficient vector
and every vector with nonnegative quadratic value. -/
theorem form_reverse_cauchy_schwarz {ι : Type*} [Fintype ι]
    (hdim : finrank ℝ E = 2) (K : ι → ConvexBody E)
    (hpositive : 0 < form μ K (fun _ => 1) (fun _ => 1))
    (x y : ι → ℝ) (hy : 0 ≤ form μ K y y) :
    form μ K x x * form μ K y y ≤ form μ K x y ^ 2 :=
  bilinear_reverse_cauchy_schwarz (form μ K) (form_symmetric μ K) (fun _ => 1)
    (form_nonpositive_on_orthogonal μ hdim K hpositive) x y hy

end VolumePolynomials.PlanarMixedForm

namespace VolumePolynomials

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Ordinary Cauchy--Schwarz on the negative orthogonal hyperplane, including
null directions. -/
theorem bilinear_negative_cauchy_schwarz (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (e : V)
    (hneg : ∀ x, B x e = 0 → B x x ≤ 0)
    (x y : V) (hx : B x e = 0) (hy : B y e = 0) :
    B x y ^ 2 ≤ B x x * B y y := by
  first
  | have hyy := hneg y hy
    have hquad (r : ℝ) : B x x + 2 * r * B x y + r ^ 2 * B y y ≤ 0 := by
      first
      | have hz : B (x + r • y) e = 0 := by
          first
          | simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hx, hy, mul_zero, add_zero]
        have h := hneg (x + r • y) hz
        simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hB y x] at h
        nlinarith
    rcases hyy.eq_or_lt with hzero | hstrict
    · have hxy : B x y = 0 := by
        first
        | by_contra hne
          have h := hquad ((1 - B x x) / (2 * B x y))
          rw [hzero] at h
          have he : B x x + 2 * ((1 - B x x) / (2 * B x y)) * B x y = 1 := by
            first
            | field_simp [hne]
              ring
          nlinarith
      rw [hxy, hzero]
      simp
    · have h := hquad (-B x y / B y y)
      have he : B x x + 2 * (-B x y / B y y) * B x y +
          (-B x y / B y y) ^ 2 * B y y =
          (B x x * B y y - B x y ^ 2) / B y y := by
        first
        | field_simp [ne_of_lt hstrict]
          ring
      rw [he] at h
      have hn : 0 ≤ B x x * B y y - B x y ^ 2 := by
        first
        | by_contra hnum
          exact (not_lt_of_ge h) (div_pos_of_neg_of_neg (lt_of_not_ge hnum) hstrict)
      linarith

end VolumePolynomials
end -- closes the original EOF section from source line 21
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarMixedForm.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarLinearExtrusion.lean -/
section


@[expose] public section

/-!
# Extrusion in an arbitrary planar direction

The determinant-coordinate version avoids normalization by the Euclidean
length of the direction. The area increment is the one-dimensional Lebesgue
measure of the image under `x ↦ det(v,x)`. It follows from the horizontal
fiber theorem by a determinant-one linear change of coordinates.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise ENNReal

namespace VolumePolynomials.PlanarExtrusion

abbrev Plane := ℝ × ℝ

instance plane_volume_isAddHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure Plane) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The standard oriented planar determinant. -/
def determinant (v x : Plane) : ℝ := v.1 * x.2 - v.2 * x.1

/-- The closed segment from the origin to `v`. -/
def originSegment (v : Plane) : Set Plane := (fun s : ℝ => s • v) '' Icc 0 1

/-- The length-one centered parameter interval in direction `v`. -/
def centeredSegment (v : Plane) : Set Plane :=
  (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- The linear map with columns `v` and `w`. -/
def frameMap (v w : Plane) : Plane →ₗ[ℝ] Plane where
  toFun p := p.1 • v + p.2 • w
  map_add' := by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' := by
    intro a x
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add,
      RingHom.id_apply]

theorem frameMap_det (v w : Plane) : LinearMap.det (frameMap v w) = determinant v w := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Basis.coe_finTwoProd_repr, frameMap, determinant, mul_comm]

theorem exists_unit_frame {v : Plane} (hv : v ≠ 0) :
    ∃ w : Plane, determinant v w = 1 := by
  by_cases h : v.1 = 0
  · have h₂ : v.2 ≠ 0 := by
      intro hz
      apply hv
      exact Prod.ext h hz
    refine ⟨(-(v.2)⁻¹, 0), ?_⟩
    simp [determinant, h, h₂]
  · refine ⟨(0, (v.1)⁻¹), ?_⟩
    simp [determinant, h]

/-- A determinant-one frame is an actual linear equivalence. -/
def frameEquiv (v w : Plane) (hw : determinant v w = 1) : Plane ≃ₗ[ℝ] Plane :=
  (frameMap v w).equivOfDetNeZero (by rw [frameMap_det, hw]; exact one_ne_zero)

@[simp] theorem frameEquiv_apply (v w : Plane) (hw : determinant v w = 1) (x : Plane) :
    frameEquiv v w hw x = x.1 • v + x.2 • w := rfl

theorem frameEquiv_det (v w : Plane) (hw : determinant v w = 1) :
    LinearMap.det (frameEquiv v w hw : Plane →ₗ[ℝ] Plane) = 1 := by
  change LinearMap.det (frameMap v w) = 1
  rw [frameMap_det, hw]

theorem determinant_frame (v w : Plane) (hw : determinant v w = 1) (x : Plane) :
    determinant v (frameEquiv v w hw x) = x.2 := by
  rw [frameEquiv_apply]
  have h : determinant v (x.1 • v + x.2 • w) = x.2 * determinant v w := by
    simp only [determinant, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    ring
  rw [h, hw, mul_one]

theorem inverse_frame_snd (v w : Plane) (hw : determinant v w = 1) (x : Plane) :
    ((frameEquiv v w hw).symm x).2 = determinant v x := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (determinant_frame v w hw ((frameEquiv v w hw).symm x)).symm

theorem frame_image_horizontal (v w : Plane) (hw : determinant v w = 1) :
    frameEquiv v w hw '' horizontal 1 = originSegment v := by
  ext x
  constructor
  · rintro ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    change z = 0 at hz
    subst z
    refine ⟨s, hs, ?_⟩
    simp
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(s, 0), ⟨hs, rfl⟩, ?_⟩
    simp

theorem area_image_linear (f : Plane →ₗ[ℝ] Plane) (C : Set Plane) :
    volume.real (f '' C) = |LinearMap.det f| * volume.real C := by
  simp only [measureReal_def]
  rw [Measure.addHaar_image_linearMap volume f C, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Transport of the horizontal extrusion theorem by a determinant-one map. -/
theorem area_add_linear_horizontal
    {C : Set Plane} (hC : IsCompact C) (hc : Convex ℝ C)
    (e : Plane ≃ₗ[ℝ] Plane) (he : LinearMap.det (e : Plane →ₗ[ℝ] Plane) = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + e '' horizontal t) =
      volume.real C + t * volume.real (projection (e.symm '' C)) := by
  let D : Set Plane := e.symm '' C
  have hD : IsCompact D := hC.image e.symm.toContinuousLinearEquiv.continuous
  have hcD : Convex ℝ D := hc.linear_image (e.symm : Plane →ₗ[ℝ] Plane)
  have hDC : e '' D = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
      have hz' : z = x := by simpa only [LinearEquiv.apply_symm_apply] using hzx
      exact hz' ▸ hz
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
  have hsum : e '' (D + horizontal t) = C + e '' horizontal t := by
    rw [Set.image_add e, hDC]
  have harea : ∀ S : Set Plane, volume.real (e '' S) = volume.real S := by
    intro S
    simpa [he] using area_image_linear (e : Plane →ₗ[ℝ] Plane) S
  calc
    volume.real (C + e '' horizontal t) = volume.real (D + horizontal t) := by
      rw [← hsum, harea]
    _ = volume.real D + t * volume.real (projection D) := area_add_horizontal hD hcD ht
    _ = volume.real C + t * volume.real (projection D) := by
      rw [← harea D, hDC]

/-- Arbitrary-direction planar extrusion, including the zero direction. -/
theorem area_add_originSegment {C : Set Plane} (hC : IsCompact C) (hc : Convex ℝ C)
    (v : Plane) :
    volume.real (C + originSegment v) =
      volume.real C + volume.real (determinant v '' C) := by
  by_cases hv : v = 0
  · subst v
    have hseg : originSegment (0 : Plane) = {0} := by
      simp [originSegment]
    have hproj : volume.real (determinant (0 : Plane) '' C) = 0 := by
      have hsub : determinant (0 : Plane) '' C ⊆ {0} := by
        rintro x ⟨y, hy, rfl⟩
        simp [determinant]
      have hm : volume (determinant (0 : Plane) '' C) = 0 :=
        measure_mono_null hsub (measure_singleton 0)
      simp [measureReal_def, hm]
    simp [hseg, hproj, Set.singleton_zero]
  · obtain ⟨w, hw⟩ := exists_unit_frame hv
    have hproj : projection ((frameEquiv v w hw).symm '' C) = determinant v '' C := by
      rw [projection, Set.image_image]
      congr 1
      funext x
      exact inverse_frame_snd v w hw x
    have h := area_add_linear_horizontal hC hc (frameEquiv v w hw)
      (frameEquiv_det v w hw) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [frame_image_horizontal, hproj, one_mul] using h

theorem centeredSegment_eq_translate (v : Plane) :
    centeredSegment v = {(-(1 / 2 : ℝ)) • v} + originSegment v := by
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

/-- Centering a segment changes no area; this is the zonotope-ready form. -/
theorem area_add_centeredSegment {C : Set Plane} (hC : IsCompact C) (hc : Convex ℝ C)
    (v : Plane) :
    volume.real (C + centeredSegment v) =
      volume.real C + volume.real (determinant v '' C) := by
  rw [centeredSegment_eq_translate, ← add_assoc, add_comm C, add_assoc]
  rw [Set.singleton_add]
  simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
  simpa only [measureReal_def] using area_add_originSegment hC hc v

end VolumePolynomials.PlanarExtrusion
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarLinearExtrusion.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarZonotope.lean -/
section


@[expose] public section

/-!
# Area and directional widths of arbitrary finite planar zonotopes

These are identities for Lebesgue measure of actual Minkowski sums of actual
segments. Repeated, collinear, and zero generating vectors are all allowed.
The only geometric input is the extrusion theorem proved from Fubini.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarExtrusion

/-- Length is additive under Minkowski addition of nonempty compact intervals. -/
theorem length_add_compact_convex {S T : Set ℝ}
    (hS : IsCompact S) (hSc : Convex ℝ S) (hSn : S.Nonempty)
    (hT : IsCompact T) (hTc : Convex ℝ T) (hTn : T.Nonempty) :
    volume.real (S + T) = volume.real S + volume.real T := by
  have hs : S = Icc (sInf S) (sSup S) :=
    eq_Icc_of_connected_compact ⟨hSn, Real.convex_iff_isPreconnected.mp hSc⟩ hS
  have ht : T = Icc (sInf T) (sSup T) :=
    eq_Icc_of_connected_compact ⟨hTn, Real.convex_iff_isPreconnected.mp hTc⟩ hT
  have hab : sInf S ≤ sSup S := csInf_le_csSup hSn hS.bddBelow hS.bddAbove
  have hcd : sInf T ≤ sSup T := csInf_le_csSup hTn hT.bddBelow hT.bddAbove
  rw [hs, ht, Icc_add_Icc hab hcd, Real.volume_real_Icc_of_le (add_le_add hab hcd),
    Real.volume_real_Icc_of_le hab, Real.volume_real_Icc_of_le hcd]
  ring

/-- Determinant in the second entry, bundled as a linear map. -/
def determinantMap (v : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := determinant v
  map_add' := by
    intro x y
    simp only [determinant, Prod.fst_add, Prod.snd_add]
    ring
  map_smul' := by
    intro a x
    simp only [determinant, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem determinantMap_apply (v x : Plane) : determinantMap v x = determinant v x := rfl

theorem continuous_determinant (v : Plane) : Continuous (determinant v) :=
  (continuous_const.mul continuous_snd).sub (continuous_const.mul continuous_fst)

theorem centeredSegment_compact (v : Plane) : IsCompact (centeredSegment v) :=
  isCompact_Icc.image (continuous_id.smul continuous_const)

theorem centeredSegment_convex (v : Plane) : Convex ℝ (centeredSegment v) :=
  (convex_Icc _ _).linear_image (LinearMap.toSpanSingleton ℝ Plane v)

theorem zero_mem_centeredSegment (v : Plane) : (0 : Plane) ∈ centeredSegment v := by
  refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp

theorem length_image_mul (k : ℝ) (S : Set ℝ) :
    volume.real ((fun s : ℝ => k * s) '' S) = |k| * volume.real S := by
  have h := congrArg ENNReal.toReal
    (Measure.addHaar_image_linearMap (volume : Measure ℝ)
      (k • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) S)
  simpa [measureReal_def, LinearMap.det_ring, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg k)] using h

theorem length_determinant_centeredSegment (v w : Plane) :
    volume.real (determinant v '' centeredSegment w) = |determinant v w| := by
  have himage : determinant v '' centeredSegment w =
      (fun s : ℝ => determinant v w * s) '' Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    rw [centeredSegment, Set.image_image]
    congr 1
    funext s
    simp only [Function.comp_apply, determinant, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [himage, length_image_mul]
  norm_num

/-- The finite Minkowski sum of centered generating segments. -/
def zonotope : List Plane → Set Plane
  | [] => {0}
  | v :: vs => zonotope vs + centeredSegment v

@[simp] theorem zonotope_singleton (v : Plane) : zonotope [v] = centeredSegment v := by
  simp [zonotope, Set.singleton_zero]

theorem zonotope_append (xs ys : List Plane) :
    zonotope (xs ++ ys) = zonotope xs + zonotope ys := by
  induction xs with
  | nil => simp [zonotope, Set.singleton_zero]
  | cons v xs ih => simp [zonotope, ih, add_assoc, add_comm, add_left_comm]

theorem zonotope_range_succ (u : ℕ → Plane) (N : ℕ) :
    zonotope ((List.range (N + 1)).map u) =
      zonotope ((List.range N).map u) + centeredSegment (u N) := by
  simp [List.range_succ, List.map_append, zonotope_append]

theorem zonotope_compact (vs : List Plane) : IsCompact (zonotope vs) := by
  induction vs with
  | nil => exact isCompact_singleton
  | cons v vs ih => exact ih.add (centeredSegment_compact v)

theorem zonotope_convex (vs : List Plane) : Convex ℝ (zonotope vs) := by
  induction vs with
  | nil => exact convex_singleton 0
  | cons v vs ih => exact ih.add (centeredSegment_convex v)

theorem zero_mem_zonotope (vs : List Plane) : (0 : Plane) ∈ zonotope vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      exact ⟨0, ih, 0, zero_mem_centeredSegment v, zero_add 0⟩

theorem determinant_width_zonotope (v : Plane) (vs : List Plane) :
    volume.real (determinant v '' zonotope vs) =
      (vs.map (fun w => |determinant v w|)).sum := by
  induction vs with
  | nil => simp [zonotope, determinant, measureReal_def]
  | cons w vs ih =>
      change volume.real (determinantMap v '' (zonotope vs + centeredSegment w)) = _
      rw [Set.image_add (determinantMap v)]
      have hlen := length_add_compact_convex
        ((zonotope_compact vs).image (continuous_determinant v))
        ((zonotope_convex vs).linear_image (determinantMap v))
        ((show (zonotope vs).Nonempty from ⟨0, zero_mem_zonotope vs⟩).image _)
        ((centeredSegment_compact w).image (continuous_determinant v))
        ((centeredSegment_convex w).linear_image (determinantMap v))
        ((show (centeredSegment w).Nonempty from ⟨0, zero_mem_centeredSegment w⟩).image _)
      change volume.real (determinant v '' zonotope vs + determinant v '' centeredSegment w) = _
      rw [hlen]
      change volume.real (determinant v '' zonotope vs) +
        volume.real (determinant v '' centeredSegment w) = _
      rw [ih, length_determinant_centeredSegment]
      simp [add_comm]

/-- Sum of absolute determinants over every unordered pair of occurrences. -/
def pairArea : List Plane → ℝ
  | [] => 0
  | v :: vs => pairArea vs + (vs.map (fun w => |determinant v w|)).sum

theorem pairArea_append_singleton (vs : List Plane) (w : Plane) :
    pairArea (vs ++ [w]) = pairArea vs + (vs.map (fun v => |determinant v w|)).sum := by
  induction vs with
  | nil => simp [pairArea]
  | cons v vs ih =>
      simp only [List.cons_append, pairArea, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih]
      ring

theorem list_sum_map_range (f : ℕ → ℝ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ, ih]

theorem pairArea_range_succ (u : ℕ → Plane) (N : ℕ) :
    pairArea ((List.range (N + 1)).map u) = pairArea ((List.range N).map u) +
      ∑ i ∈ Finset.range N, |determinant (u i) (u N)| := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
    pairArea_append_singleton, List.map_map, Function.comp_def, list_sum_map_range]

theorem pairArea_range (u : ℕ → Plane) (N : ℕ) :
    pairArea ((List.range N).map u) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, |determinant (u i) (u j)| := by
  induction N with
  | zero => simp [pairArea]
  | succ N ih => rw [pairArea_range_succ, Finset.sum_range_succ, ih]

/-- The exact planar zonotope area identity, with no general-position assumption. -/
theorem area_zonotope (vs : List Plane) : volume.real (zonotope vs) = pairArea vs := by
  induction vs with
  | nil => simp [zonotope, pairArea, measureReal_def]
  | cons v vs ih =>
      rw [zonotope, area_add_centeredSegment (zonotope_compact vs) (zonotope_convex vs),
        ih, determinant_width_zonotope, pairArea]

theorem area_zonotope_range (u : ℕ → Plane) (N : ℕ) :
    volume.real (zonotope ((List.range N).map u)) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, |determinant (u i) (u j)| := by
  rw [area_zonotope, pairArea_range]

theorem determinant_width_zonotope_range (v : Plane) (u : ℕ → Plane) (N : ℕ) :
    volume.real (determinant v '' zonotope ((List.range N).map u)) =
      ∑ i ∈ Finset.range N, |determinant v (u i)| := by
  rw [determinant_width_zonotope, List.map_map, list_sum_map_range]
  rfl

end VolumePolynomials.PlanarExtrusion
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarZonotope.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarCornerInequality.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The universal planar corner inequality

This proves equation (4.6) for actual compact convex planar sets, including
degenerate sets. The proof uses the actual mixed-area form and coordinate
segment extrusion. The width-zero formal differences lie in a negative
orthogonal hyperplane, where ordinary Cauchy--Schwarz applies.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped BigOperators Pointwise

namespace VolumePolynomials

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem bilinear_corner_inequality (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (e : V)
    (hneg : ∀ x, B x e = 0 → B x x ≤ 0)
    (s t p q : V) (hss : B s s = 0) (htt : B t t = 0)
    (hst : 2 * B s t = 1) (w h w' h' : ℝ)
    (hps : 2 * B p s = h) (hpt : 2 * B p t = w)
    (hqs : 2 * B q s = h') (hqt : 2 * B q t = w') :
    2 * B p q ≥ w * h' + h * w' -
      2 * Real.sqrt ((w * h - B p p) * (w' * h' - B q q)) := by
  first
  | let r := s + t
    let x := w • s + h • t - p
    let y := w' • s + h' • t - q
    have hst' : B s t = 1 / 2 := by linarith
    have hps' : B p s = h / 2 := by linarith
    have hpt' : B p t = w / 2 := by linarith
    have hqs' : B q s = h' / 2 := by linarith
    have hqt' : B q t = w' / 2 := by linarith
    have hts : B t s = 1 / 2 := (hB t s).trans hst'
    have hsp : B s p = h / 2 := (hB s p).trans hps'
    have htp : B t p = w / 2 := (hB t p).trans hpt'
    have hsq : B s q = h' / 2 := (hB s q).trans hqs'
    have htq : B t q = w' / 2 := (hB t q).trans hqt'
    have hrr : B r r = 1 := by
      first
      | simp only [r, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hss, htt, hst', hts]
        norm_num
    have hxr : B x r = 0 := by
      first
      | simp only [x, r, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.smul_left, hss, htt, hst', hts, hps', hpt']
        ring
    have hyr : B y r = 0 := by
      first
      | simp only [y, r, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.smul_left, hss, htt, hst', hts, hqs', hqt']
        ring
    have hxx : B x x = B p p - w * h := by
      first
      | simp only [x, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
          hss, htt, hst', hts, hsp, htp, hps', hpt']
        ring
    have hyy : B y y = B q q - w' * h' := by
      first
      | simp only [y, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
          hss, htt, hst', hts, hsq, htq, hqs', hqt']
        ring
    have hxy : B x y = B p q - (w * h' + h * w') / 2 := by
      first
      | simp only [x, y, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
          hss, htt, hst', hts, hsq, htq, hps', hpt']
        ring
    have hnegR : ∀ z, B z r = 0 → B z z ≤ 0 := fun z hz =>
      bilinear_nonpos_on_positive_orthogonal B hB e hneg (by rw [hrr]; norm_num) hz
    have hcs := bilinear_negative_cauchy_schwarz B hB r hnegR x y hxr hyr
    rw [hxx, hyy, hxy] at hcs
    have hcs' : (B p q - (w * h' + h * w') / 2) ^ 2 ≤
        (w * h - B p p) * (w' * h' - B q q) := by nlinarith
    have hsqrt := Real.sqrt_le_sqrt hcs'
    rw [Real.sqrt_sq_eq_abs] at hsqrt
    have hlo := (neg_le_neg hsqrt).trans
      (neg_abs_le (B p q - (w * h' + h * w') / 2))
    linarith

end VolumePolynomials

namespace VolumePolynomials.PlanarCorner

open PlanarExtrusion PlanarMixedForm

def segmentBody (v : Plane) : ConvexBody Plane where
  carrier := centeredSegment v
  convex' := centeredSegment_convex v
  isCompact' := centeredSegment_compact v
  nonempty' := ⟨0, zero_mem_centeredSegment v⟩

def unitX : ConvexBody Plane := segmentBody (1, 0)
def unitY : ConvexBody Plane := segmentBody (0, 1)

/-- Literal Lebesgue length of the horizontal projection. -/
def width (P : ConvexBody Plane) : ℝ := volume.real (Prod.fst '' (P : Set Plane))

/-- Literal Lebesgue length of the vertical projection. -/
def height (P : ConvexBody Plane) : ℝ := volume.real (Prod.snd '' (P : Set Plane))

theorem plane_finrank : finrank ℝ Plane = 2 := by simp [Plane]

theorem area_segmentBody (v : Plane) : volume.real (segmentBody v : Set Plane) = 0 := by
  first
  | change volume.real (centeredSegment v) = 0
    simpa only [zonotope_singleton, pairArea, List.map_nil,
      List.sum_nil, add_zero] using area_zonotope [v]

theorem twice_mixedArea_segment (P : ConvexBody Plane) (v : Plane) :
    2 * mixedArea volume P (segmentBody v) = volume.real (determinant v '' (P : Set Plane)) := by
  first
  | have h := area_add_centeredSegment P.isCompact P.convex v
    have hp := area_add volume plane_finrank P (segmentBody v)
    rw [area_segmentBody, add_zero] at hp
    change volume.real ((P + segmentBody v : ConvexBody Plane) : Set Plane) = _ at h
    linarith

theorem twice_mixedArea_unitX (P : ConvexBody Plane) :
    2 * mixedArea volume P unitX = height P := by
  first
  | have hd : determinant (1, 0) = Prod.snd := by
      funext x
      simp [determinant]
    rw [unitX, twice_mixedArea_segment, hd]
    rfl

theorem twice_mixedArea_unitY (P : ConvexBody Plane) :
    2 * mixedArea volume P unitY = width P := by
  first
  | rw [unitY, twice_mixedArea_segment]
    have himage : determinant (0, 1) '' (P : Set Plane) =
        (fun r : ℝ => (-1) * r) '' (Prod.fst '' (P : Set Plane)) := by
      first
      | rw [Set.image_image]
        congr 1
        funext x
        simp [determinant]
    rw [himage, length_image_mul]
    norm_num [width]

theorem twice_mixedArea_axes : 2 * mixedArea volume unitX unitY = 1 := by
  first
  | rw [mixedArea_symm, unitX, twice_mixedArea_segment]
    change volume.real (determinant (1, 0) '' centeredSegment (0, 1)) = 1
    rw [length_determinant_centeredSegment]
    norm_num [determinant]

/-- Equation (4.6), with no nondegeneracy, polygonality, or normalization
assumption. All areas and widths retain their ordinary geometric meanings. -/
theorem mixedArea_corner_inequality (P Q : ConvexBody Plane) :
    2 * mixedArea volume P Q ≥ width P * height Q + height P * width Q -
      2 * Real.sqrt ((width P * height P - volume.real (P : Set Plane)) *
        (width Q * height Q - volume.real (Q : Set Plane))) := by
  first
  | let K : Fin 4 → ConvexBody Plane := ![P, Q, unitX, unitY]
    let B := form volume K
    let p : Fin 4 → ℝ := Pi.single 0 1
    let q : Fin 4 → ℝ := Pi.single 1 1
    let s : Fin 4 → ℝ := Pi.single 2 1
    let t : Fin 4 → ℝ := Pi.single 3 1
    have hK0 : K 0 = P := rfl
    have hK1 : K 1 = Q := rfl
    have hK2 : K 2 = unitX := rfl
    have hK3 : K 3 = unitY := rfl
    have hentry : 0 < mixedArea volume (K 2) (K 3) := by
      first
      | change 0 < mixedArea volume unitX unitY
        linarith [twice_mixedArea_axes]
    have hpositive := form_one_positive_of_entry volume K 2 3 hentry
    have hneg : ∀ x, B x (fun _ => 1) = 0 → B x x ≤ 0 :=
      form_nonpositive_on_orthogonal volume plane_finrank K hpositive
    have hss : B s s = 0 := by
      first
      | simp only [B, s, form_single, hK2]
        rw [mixedArea_diagonal volume plane_finrank, unitX, area_segmentBody]
    have htt : B t t = 0 := by
      first
      | simp only [B, t, form_single, hK3]
        rw [mixedArea_diagonal volume plane_finrank, unitY, area_segmentBody]
    have hst : 2 * B s t = 1 := by
      first
      | simpa only [B, s, t, form_single, hK2, hK3]
          using twice_mixedArea_axes
    have hps : 2 * B p s = height P := by
      first
      | simpa only [B, p, s, form_single, hK0, hK2]
          using twice_mixedArea_unitX P
    have hpt : 2 * B p t = width P := by
      first
      | simpa only [B, p, t, form_single, hK0, hK3]
          using twice_mixedArea_unitY P
    have hqs : 2 * B q s = height Q := by
      first
      | simpa only [B, q, s, form_single, hK1, hK2]
          using twice_mixedArea_unitX Q
    have hqt : 2 * B q t = width Q := by
      first
      | simpa only [B, q, t, form_single, hK1, hK3]
          using twice_mixedArea_unitY Q
    have h := bilinear_corner_inequality B (form_symmetric volume K) (fun _ => 1)
      hneg s t p q hss htt hst (width P) (height P) (width Q) (height Q) hps hpt hqs hqt
    simpa only [B, p, q, form_single, hK0, hK1,
      mixedArea_diagonal volume plane_finrank] using h

end VolumePolynomials.PlanarCorner
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarCornerInequality.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeRadialGeometry.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Radial fibers of an actual Minkowski perturbation

The old polytope is the literal bounded intersection `lᵢ x ≤ 1`. At a point
lying on exactly one old facet, a maximizer of that facet functional on the
added body gives the exact moving radial endpoint for all sufficiently small
nonnegative parameters. This is the geometric input to first variation;
no mixed-volume or first-variation formula is assumed.
-/

noncomputable section
open Set Filter
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials.PolytopeRadialGeometry

open HalfspacePyramids

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem convex_body (l : ι → E →L[ℝ] ℝ) : Convex ℝ (body l) := by
  first
  | intro x hx y hy a b ha hb hab i
    change l i (a • x + b • y) ≤ 1
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)
    simpa only [mul_one, hab] using h

theorem mem_smul_body_iff (l : ι → E →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) (x : E) :
    x ∈ r • body l ↔ ∀ i, l i x ≤ r := by
  first
  | constructor
    · rintro ⟨y, hy, rfl⟩ i
      simpa only [map_smul, smul_eq_mul, mul_one] using
        mul_le_mul_of_nonneg_left (hy i) hr.le
    · intro hx
      refine ⟨r⁻¹ • x, ?_, by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
      intro i
      change l i (r⁻¹ • x) ≤ 1
      rw [map_smul, smul_eq_mul]
      simpa only [inv_mul_cancel₀ hr.ne'] using
        mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hr.le)

theorem body_subset_add_smul (l : ι → E →L[ℝ] ℝ) {A : Set E}
    (hA0 : (0 : E) ∈ A) (t : ℝ) : body l ⊆ body l + t • A := by
  first
  | intro x hx
    exact ⟨x, hx, 0, ⟨0, hA0, by simp⟩, add_zero x⟩

theorem add_smul_subset_smul_body (l : ι → E →L[ℝ] ℝ) {A : Set E}
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hbound : ∀ i a, a ∈ A → l i a ≤ C) :
    body l + t • A ⊆ (1 + t * C) • body l := by
  first
  | rintro x ⟨s, hs, z, ⟨a, ha, rfl⟩, rfl⟩
    apply Iff.mpr (mem_smul_body_iff l (by positivity) _)
    intro i
    change l i (s + t • a) ≤ 1 + t * C
    rw [map_add, map_smul, smul_eq_mul]
    exact add_le_add (hs i) (mul_le_mul_of_nonneg_left (hbound i a ha) ht)

/-- The candidate endpoint is obtained by translating an old facet point back
by an actual support maximizer. All inactive inequalities remain strict locally. -/
theorem eventually_radial_endpoint_mem
    (l : ι → E →L[ℝ] ℝ) (i : ι) {q a : E}
    (hq : q ∈ face l i) (hstrict : ∀ j, j ≠ i → l j q < 1)
    {A : Set E} (ha : a ∈ A) :
    ∀ᶠ t : ℝ in 𝓝 0, (1 + t * l i a) • q ∈ body l + t • A := by
  first
  | have hall : ∀ j, ∀ᶠ t : ℝ in 𝓝 0,
        l j ((1 + t * l i a) • q - t • a) ≤ 1 := by
      first
      | intro j
        by_cases hji : j = i
        · subst j
          exact Eventually.of_forall fun t => by
            rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hq.2]
            linarith
        · have hc : Continuous (fun t : ℝ => l j ((1 + t * l i a) • q - t • a)) := by
            first
            | fun_prop
          have hh : l j ((1 + (0 : ℝ) * l i a) • q - (0 : ℝ) • a) < 1 := by
            first
            | simpa using hstrict j hji
          exact (hc.continuousAt.eventually (Iio_mem_nhds hh)).mono fun _ h => h.le
    filter_upwards [Filter.eventually_all.mpr hall] with t ht
    refine ⟨(1 + t * l i a) • q - t • a, ht, t • a, ⟨a, ha, rfl⟩, ?_⟩
    exact sub_add_cancel _ _

/-- At almost every old facet point, every nonnegative radial coordinate has
the exact interval-membership description for a small positive perturbation. -/
theorem eventually_radial_mem_iff
    (l : ι → E →L[ℝ] ℝ) (i : ι) {q a : E}
    (hq : q ∈ face l i) (hstrict : ∀ j, j ≠ i → l j q < 1)
    {A : Set E} (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a) :
    ∀ᶠ t : ℝ in 𝓝[≥] 0, ∀ r : ℝ, 0 ≤ r →
      (r • q ∈ body l + t • A ↔ r ≤ 1 + t * l i a) := by
  first
  | have hc : 0 ≤ l i a := by simpa using hmax 0 hA0
    have hend : ∀ᶠ t : ℝ in 𝓝[≥] 0,
        (1 + t * l i a) • q ∈ body l + t • A :=
      (eventually_radial_endpoint_mem l i hq hstrict ha).filter_mono nhdsWithin_le_nhds
    filter_upwards [hend, self_mem_nhdsWithin] with t ht htn
    have ht0 : 0 ≤ t := htn
    have hlam : 0 < 1 + t * l i a := by positivity
    have hzero : (0 : E) ∈ body l + t • A :=
      body_subset_add_smul l hA0 t (zero_mem_body l)
    have hconv : Convex ℝ (body l + t • A) := (convex_body l).add (hA.smul t)
    intro r hr
    constructor
    · rintro ⟨s, hs, z, ⟨b, hb, rfl⟩, heq⟩
      have hli := congrArg (l i) heq
      simp only [map_add, map_smul, smul_eq_mul, hq.2, mul_one] at hli
      have hb' := mul_le_mul_of_nonneg_left (hmax b hb) ht0
      linarith [hs i]
    · intro hrlam
      have hratio : r / (1 + t * l i a) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hr hlam.le, (div_le_one hlam).mpr hrlam⟩
      have hm := hconv.smul_mem_of_zero_mem hzero ht hratio
      simpa only [smul_smul, div_mul_cancel₀ _ hlam.ne'] using hm

/-- Compactness supplies a genuine uniform bound on every normal, independent
of the boundary point and of the perturbation parameter. -/
theorem exists_uniform_normal_bound
    (l : ι → E →L[ℝ] ℝ) {A : Set E} (hA : IsCompact A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i a, a ∈ A → |l i a| ≤ C := by
  first
  | classical
    obtain ⟨R, hR, hbound⟩ := hA.isBounded.exists_pos_norm_le
    refine ⟨R * ∑ j, ‖l j‖, mul_nonneg hR.le (Finset.sum_nonneg fun _ _ => norm_nonneg _), ?_⟩
    intro i a ha
    have hnorm : ‖l i‖ ≤ ∑ j, ‖l j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (l j)) (Finset.mem_univ i)
    calc
      |l i a| = ‖l i a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖l i‖ * ‖a‖ := (l i).le_opNorm a
      _ ≤ ‖l i‖ * R := mul_le_mul_of_nonneg_left (hbound a ha) (norm_nonneg _)
      _ ≤ (∑ j, ‖l j‖) * R := mul_le_mul_of_nonneg_right hnorm hR.le
      _ = _ := mul_comm _ _

end VolumePolynomials.PolytopeRadialGeometry
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeRadialGeometry.lean -/

/- BEGIN SOURCE: VolumePolynomials/FacetAlmostEverywhere.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Null exceptional sets in the actual facet Haar measure

Distinct normalized facet functionals cut a proper affine subspace of the
chosen facet coordinates. Thus almost every point of each old facet satisfies
all the other defining inequalities strictly. This is a statement in the
lower-dimensional Haar measure, not merely an ambient null-set assertion.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.FacetAlmostEverywhere

open HalfspacePyramids LinearFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def facetCut (l m : E →L[ℝ] ℝ) (v : E) :
    AffineSubspace ℝ (LinearMap.ker l.toLinearMap) where
  carrier := {y | m (v + y.val) = 1}
  smul_vsub_vadd_mem' c p₁ p₂ p₃ h₁ h₂ h₃ := by
    first
    | change m (v + (c • (p₁.val - p₂.val) + p₃.val)) = 1
      change m (v + p₁.val) = 1 at h₁
      change m (v + p₂.val) = 1 at h₂
      change m (v + p₃.val) = 1 at h₃
      simp only [map_add] at h₁ h₂ h₃
      have he : m p₁.val = m p₂.val := by linarith
      simpa only [map_add, map_smul, map_sub, smul_eq_mul, he, sub_self,
        mul_zero, zero_add] using h₃

theorem facetCut_ne_top (l m : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (hlm : l ≠ m) : facetCut l m v ≠ ⊤ := by
  first
  | intro htop
    have hall : ∀ y : LinearMap.ker l.toLinearMap, m (v + y.val) = 1 := by
      first
      | intro y
        have hy : y ∈ facetCut l m v := by rw [htop]; trivial
        exact hy
    have hmv : m v = 1 := by simpa using hall 0
    have hker : ∀ y : LinearMap.ker l.toLinearMap, m y.val = 0 := by
      first
      | intro y
        have h := hall y
        rw [map_add, hmv] at h
        linarith
    apply hlm
    ext x
    have h := hker (kernelPart l v hv x)
    rw [kernelPart_coe, map_sub, map_smul, smul_eq_mul, hmv, mul_one] at h
    exact (sub_eq_zero.mp h).symm

section FiniteDimensional

variable [FiniteDimensional ℝ E]

theorem measure_facetCut_eq_zero (l m : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (hlm : l ≠ m)
    [MeasurableSpace (LinearMap.ker l.toLinearMap)]
    [BorelSpace (LinearMap.ker l.toLinearMap)]
    (μ : Measure (LinearMap.ker l.toLinearMap))
    [Measure.IsAddHaarMeasure μ] :
    μ {y : LinearMap.ker l.toLinearMap | m (v + y.val) = 1} = 0 :=
  Measure.addHaar_affineSubspace μ (facetCut l m v) (facetCut_ne_top l m v hv hlm)

variable {ι : Type*} [Fintype ι]

def facetBase (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) :
    Set (LinearMap.ker (l i).toLinearMap) :=
  {y | v + y.val ∈ body l}

theorem facetBase_eq_image (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E)
    (hv : l i v = 1) :
    facetBase l i v = Prod.snd '' (continuousEquiv (l i) v hv '' face l i) := by
  first
  | ext y
    constructor
    · intro hy
      refine ⟨continuousEquiv (l i) v hv (v + y.val), ?_, ?_⟩
      · exact ⟨v + y.val, ⟨hy, by simp [map_add, hv, y.property]⟩, rfl⟩
      · apply Subtype.ext
        change v + y.val - l i (v + y.val) • v = y.val
        have hy0 : l i y.val = 0 := y.property
        simp only [map_add, hv, hy0, add_zero, one_smul]
        abel
    · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
      change v + (x - l i x • v) ∈ body l
      have he : v + (x - v) = x := by abel
      simpa only [hx.2, one_smul, he] using hx.1

theorem facetBase_compact (l : ι → E →L[ℝ] ℝ)
    (hC : IsCompact (body l)) (i : ι) (v : E) (hv : l i v = 1) :
    IsCompact (facetBase l i v) := by
  first
  | rw [facetBase_eq_image l i v hv]
    exact ((face_compact l hC i).image (continuousEquiv (l i) v hv).continuous).image
      continuous_snd

theorem facetBase_point_mem_face (l : ι → E →L[ℝ] ℝ)
    (i : ι) (v : E) (hv : l i v = 1)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v) :
    v + y.val ∈ face l i :=
  ⟨hy, by simp [map_add, hv, y.property]⟩

/-- Exceptional intersections with other facets have zero measure in the
actual kernel coordinates, including redundant and lower-dimensional facets. -/
theorem ae_strict_other_facets
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l)
    (hC : IsCompact (body l)) (i : ι) (v : E) (hv : l i v = 1)
    [MeasurableSpace (LinearMap.ker (l i).toLinearMap)]
    [BorelSpace (LinearMap.ker (l i).toLinearMap)]
    (μ : Measure (LinearMap.ker (l i).toLinearMap)) [Measure.IsAddHaarMeasure μ] :
    ∀ᵐ y ∂μ.restrict (facetBase l i v), ∀ j, j ≠ i → l j (v + y.val) < 1 := by
  first
  | have hall : ∀ j, ∀ᵐ y ∂μ, j ≠ i → l j (v + y.val) ≠ 1 := by
      first
      | intro j
        by_cases hji : j = i
        · exact Filter.Eventually.of_forall fun _ h => (h hji).elim
        · have hnull := measure_facetCut_eq_zero (l i) (l j) v hv
            (fun h => hji (hl h).symm) μ
          have hne : ∀ᵐ y ∂μ, l j (v + y.val) ≠ 1 := by
            first
            | rw [ae_iff]
              simpa only [not_not] using hnull
          exact hne.mono fun _ h _ => h
    have hne : ∀ᵐ y ∂μ, ∀ j, j ≠ i → l j (v + y.val) ≠ 1 :=
      Filter.eventually_all.mpr hall
    filter_upwards [ae_restrict_mem (facetBase_compact l hC i v hv).measurableSet,
      ae_restrict_of_ae hne] with y hy hyne
    intro j hji
    exact lt_of_le_of_ne (hy j) (hyne j hji)

end FiniteDimensional
end VolumePolynomials.FacetAlmostEverywhere
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FacetAlmostEverywhere.lean -/

/- BEGIN SOURCE: VolumePolynomials/ClippedConeVolume.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Fubini formula for a fixed cone clipped by a moving compact set

The radial integration coordinates are over a fixed old facet. Consequently
no continuity of a moving radial function is needed for first variation.
-/

noncomputable section
open Set MeasureTheory Module
open scoped ENNReal Pointwise

namespace VolumePolynomials.ClippedConeVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialMap (p : ℝ × E) : ℝ × E := (p.1, p.1 • p.2)

theorem continuous_radialMap : Continuous (radialMap (E := E)) := by
  first
  | unfold radialMap
    fun_prop

def clippedCone (R : ℝ) (A : Set E) (K : Set (ℝ × E)) : Set (ℝ × E) :=
  (radialMap '' (Icc (0 : ℝ) R ×ˢ A)) ∩ K

theorem clippedCone_compact {R : ℝ} {A : Set E} (hA : IsCompact A)
    {K : Set (ℝ × E)} (hK : IsClosed K) : IsCompact (clippedCone R A K) :=
  ((isCompact_Icc.prod hA).image continuous_radialMap).inter_right hK

theorem clippedCone_fiber (R : ℝ) (A : Set E) (K : Set (ℝ × E)) (r : ℝ) :
    Prod.mk r ⁻¹' clippedCone R A K =
      if r ∈ Icc (0 : ℝ) R then
        r • {x : E | x ∈ A ∧ radialMap (r, x) ∈ K} else ∅ := by
  first
  | classical
    by_cases hr : r ∈ Icc (0 : ℝ) R
    · rw [if_pos hr]
      ext y
      constructor
      · rintro ⟨⟨⟨s, x⟩, ⟨hs, hx⟩, heq⟩, hyK⟩
        have hsr : s = r := congrArg Prod.fst heq
        subst s
        have hxy : r • x = y := congrArg Prod.snd heq
        refine ⟨x, ⟨hx, ?_⟩, hxy⟩
        simpa only [radialMap, hxy] using hyK
      · rintro ⟨x, ⟨hxA, hxK⟩, rfl⟩
        exact ⟨⟨(r, x), ⟨hr, hxA⟩, rfl⟩, hxK⟩
    · rw [if_neg hr]
      apply eq_empty_iff_forall_notMem.mpr
      rintro y ⟨⟨⟨s, x⟩, ⟨hs, hx⟩, heq⟩, hyK⟩
      have hsr : s = r := congrArg Prod.fst heq
      exact hr (hsr ▸ hs)

def radialWeight (k : ℕ) (K : Set (ℝ × E)) : ℝ × E → ℝ≥0∞ :=
  (radialMap ⁻¹' K).indicator (fun p => ENNReal.ofReal (p.1 ^ k))

section Measure

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem measurable_radialWeight (k : ℕ) {K : Set (ℝ × E)}
    (hK : MeasurableSet K) : Measurable (radialWeight k K) := by
  first
  | apply Measurable.indicator (by fun_prop)
    exact hK.preimage continuous_radialMap.measurable

theorem clippedCone_fiber_measure (R : ℝ) (A : Set E) (K : Set (ℝ × E)) (r : ℝ) :
    volume (Prod.mk r ⁻¹' clippedCone R A K) =
      (Icc (0 : ℝ) R).indicator
        (fun s => ENNReal.ofReal (s ^ finrank ℝ E) *
          volume {x : E | x ∈ A ∧ radialMap (s, x) ∈ K}) r := by
  first
  | classical
    rw [clippedCone_fiber]
    by_cases hr : r ∈ Icc (0 : ℝ) R
    · rw [if_pos hr, Set.indicator_of_mem hr,
        Measure.addHaar_smul_of_nonneg volume hr.1]
    · simp only [if_neg hr, measure_empty, Set.indicator_of_notMem hr]

theorem lintegral_radialWeight (k : ℕ) (A : Set E) {K : Set (ℝ × E)}
    (hK : MeasurableSet K) (r : ℝ) :
    (∫⁻ x in A, radialWeight k K (r, x)) =
      ENNReal.ofReal (r ^ k) * volume {x : E | x ∈ A ∧ radialMap (r, x) ∈ K} := by
  first
  | have hm : MeasurableSet {x : E | radialMap (r, x) ∈ K} :=
      hK.preimage (continuous_radialMap.comp (continuous_const.prodMk continuous_id)).measurable
    have heq : (fun x : E => radialWeight k K (r, x)) =
        {x : E | radialMap (r, x) ∈ K}.indicator (fun _ => ENNReal.ofReal (r ^ k)) := rfl
    rw [heq, lintegral_indicator_const hm, Measure.restrict_apply hm]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, and_comm]

/-- The genuine volume of the clipped cone as an integral over the fixed base
and a fixed interval. The moving set occurs only in a measurable indicator. -/
theorem volume_clippedCone {R : ℝ} {A : Set E} (hA : IsCompact A)
    {K : Set (ℝ × E)} (hK : IsClosed K) :
    volume (clippedCone R A K) =
      ∫⁻ x in A, ∫⁻ r in Icc (0 : ℝ) R, radialWeight (finrank ℝ E) K (r, x) := by
  first
  | calc
      volume (clippedCone R A K) =
          ∫⁻ r : ℝ, volume (Prod.mk r ⁻¹' clippedCone R A K) :=
        Measure.prod_apply (clippedCone_compact hA hK).measurableSet
      _ = ∫⁻ r : ℝ, (Icc (0 : ℝ) R).indicator
          (fun s => ENNReal.ofReal (s ^ finrank ℝ E) *
            volume {x : E | x ∈ A ∧ radialMap (s, x) ∈ K}) r :=
        lintegral_congr (clippedCone_fiber_measure R A K)
      _ = ∫⁻ r in Icc (0 : ℝ) R, ENNReal.ofReal (r ^ finrank ℝ E) *
          volume {x : E | x ∈ A ∧ radialMap (r, x) ∈ K} :=
        lintegral_indicator measurableSet_Icc _
      _ = ∫⁻ r in Icc (0 : ℝ) R, ∫⁻ x in A, radialWeight (finrank ℝ E) K (r, x) := by
        first
        | apply lintegral_congr
          intro r
          exact (lintegral_radialWeight _ A hK.measurableSet r).symm
      _ = _ := lintegral_lintegral_swap (measurable_radialWeight _ hK.measurableSet).aemeasurable

end Measure
end VolumePolynomials.ClippedConeVolume
end -- closes the original EOF section from source line 15
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ClippedConeVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/ConeDerivative.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Dominated right differentiation of radial cone integrals

These are ordinary calculus and integration lemmas. Their hypotheses concern
pointwise radial fibers and an explicit integrable difference-quotient bound;
the geometric input is proved separately for literal Minkowski sums.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace VolumePolynomials.ConeDerivative

theorem radialPower_hasDerivAt (k : ℕ) (c : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t * c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) c 0 := by
  first
  | have hn : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    convert ((((hasDerivAt_id (0 : ℝ)).mul_const c).const_add 1).pow (k + 1)).div_const
      (((k + 1 : ℕ) : ℝ)) using 1 <;> simp [hn] <;> field_simp <;> ring

theorem tendsto_radialPower_quotient (k : ℕ) (c : ℝ) :
    Tendsto (fun t : ℝ =>
      ((1 + t * c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
        1 / ((k + 1 : ℕ) : ℝ)) / t) (𝓝[>] 0) (𝓝 c) := by
  first
  | have h := (radialPower_hasDerivAt k c).tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
    change Tendsto
      (fun t : ℝ => slope
        (fun u : ℝ => (1 + u * c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) 0 t)
      (𝓝[>] 0) (𝓝 c) at h
    simpa only [slope_def_field, zero_mul, add_zero, one_pow, sub_zero] using h

theorem radialPower_quotient_bound (k : ℕ) {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1) :
    (((1 + t * C) ^ (k + 1) - 1) / (((k + 1 : ℕ) : ℝ) * t)) ≤
      C * (1 + C) ^ k := by
  first
  | have hbase : 1 ≤ 1 + t * C := by linarith [mul_nonneg ht.le hC]
    have hpow : 1 ≤ (1 + t * C) ^ (k + 1) := one_le_pow₀ hbase
    have hdiff := abs_pow_sub_pow_le (a := 1 + t * C) (b := (1 : ℝ)) (n := k + 1)
    rw [one_pow, abs_of_nonneg (sub_nonneg.mpr hpow),
      show 1 + t * C - 1 = t * C by ring,
      abs_of_nonneg (mul_nonneg ht.le hC),
      abs_of_nonneg (zero_le_one.trans hbase), abs_one,
      max_eq_left hbase, Nat.add_sub_cancel] at hdiff
    have hmono : (1 + t * C) ^ k ≤ (1 + C) ^ k := by
      apply pow_le_pow_left₀ (zero_le_one.trans hbase)
      nlinarith
    have hbound := hdiff.trans (mul_le_mul_of_nonneg_left hmono
      (mul_nonneg (mul_nonneg ht.le hC) (Nat.cast_nonneg _)))
    apply (div_le_iff₀ (mul_pos (by positivity) ht)).mpr
    nlinarith

/-- Differentiation of an actual integral along the positive parameter filter.
The finite-measure constant bound is particularly convenient on compact facets. -/
theorem tendsto_integral_difference_quotient
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℝ → α → ℝ) (g : α → ℝ) (C : ℝ)
    (hF0 : Integrable (F 0) μ)
    (hF : ∀ᶠ t : ℝ in 𝓝[>] 0, Integrable (F t) μ)
    (hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ x ∂μ, |(F t x - F 0 x) / t| ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => (F t x - F 0 x) / t)
      (𝓝[>] 0) (𝓝 (g x))) :
    Tendsto (fun t : ℝ => ((∫ x, F t x ∂μ) - ∫ x, F 0 x ∂μ) / t)
      (𝓝[>] 0) (𝓝 (∫ x, g x ∂μ)) := by
  first
  | have hmeas : ∀ᶠ t : ℝ in 𝓝[>] 0,
        AEStronglyMeasurable (fun x => (F t x - F 0 x) / t) μ :=
      hF.mono fun t ht => ((ht.sub hF0).div_const t).aestronglyMeasurable
    have hnorm : ∀ᶠ t : ℝ in 𝓝[>] 0,
        ∀ᵐ x ∂μ, ‖(F t x - F 0 x) / t‖ ≤ C := by
      simpa only [Real.norm_eq_abs] using hbound
    have h := tendsto_integral_filter_of_dominated_convergence (fun _ : α => C)
      hmeas hnorm (integrable_const C) hlim
    apply h.congr'
    filter_upwards [hF] with t ht
    rw [integral_div, integral_sub ht hF0]

end VolumePolynomials.ConeDerivative
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ConeDerivative.lean -/

/- BEGIN SOURCE: VolumePolynomials/RadialSliceIntegral.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Finite radial slice integrals

Actual nonnegative cone fibers are converted to finite real integrals. Uniform
bounds come from a containing radial interval, while exact interval fibers
give the elementary power primitive used in first variation.
-/

noncomputable section
open Set MeasureTheory Module
open scoped ENNReal Topology

namespace VolumePolynomials.ClippedConeVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialSlice (k : ℕ) (R : ℝ) (K : Set (ℝ × E)) (x : E) : ℝ :=
  (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)).toReal

theorem lintegral_radial_pow (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∫⁻ r in Icc (0 : ℝ) R, ENNReal.ofReal (r ^ k)) =
      ENNReal.ofReal (R ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  first
  | have hi : IntegrableOn (fun r : ℝ => r ^ k) (Icc (0 : ℝ) R) :=
      (continuous_id.pow k).integrableOn_Icc
    have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) R)] (fun r : ℝ => r ^ k) := by
      first
      | filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact pow_nonneg hr.1 _
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR, integral_pow]
    simp

theorem lintegral_radialWeight_le (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × E)) (x : E) :
    (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)) ≤
      ENNReal.ofReal (R ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  first
  | rw [← lintegral_radial_pow k hR]
    apply lintegral_mono
    intro r
    by_cases h : radialMap (r, x) ∈ K
    · simp [radialWeight, h]
    · simp [radialWeight, h]

theorem lintegral_radialWeight_lt_top (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × E)) (x : E) :
    (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)) < ∞ :=
  (lintegral_radialWeight_le k hR K x).trans_lt ENNReal.ofReal_lt_top

theorem radialSlice_nonneg (k : ℕ) (R : ℝ) (K : Set (ℝ × E)) (x : E) :
    0 ≤ radialSlice k R K x := ENNReal.toReal_nonneg

theorem radialSlice_le (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × E)) (x : E) :
    radialSlice k R K x ≤ R ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_radialWeight_le k hR K x)
    simpa only [radialSlice, ENNReal.toReal_ofReal
      (div_nonneg (pow_nonneg hR _) (Nat.cast_nonneg _))] using h

theorem radialSlice_mono (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {K L : Set (ℝ × E)} (hKL : K ⊆ L) (x : E) :
    radialSlice k R K x ≤ radialSlice k R L x := by
  first
  | apply ENNReal.toReal_mono (lintegral_radialWeight_lt_top k hR L x).ne
    apply lintegral_mono
    intro r
    by_cases h : radialMap (r, x) ∈ K
    · simp [radialWeight, h, hKL h]
    · simp [radialWeight, h]

theorem radialSlice_mono_on_ray (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K L : Set (ℝ × E)) (x : E)
    (hKL : ∀ r : ℝ, 0 ≤ r → radialMap (r, x) ∈ K → radialMap (r, x) ∈ L) :
    radialSlice k R K x ≤ radialSlice k R L x := by
  first
  | apply ENNReal.toReal_mono (lintegral_radialWeight_lt_top k hR L x).ne
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    by_cases h : radialMap (r, x) ∈ K
    · simp [radialWeight, h, hKL r hr.1 h]
    · simp [radialWeight, h]

theorem radialSlice_eq_power_of_interval (k : ℕ) {R L : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (K : Set (ℝ × E)) (x : E)
    (hfiber : ∀ r : ℝ, 0 ≤ r → (radialMap (r, x) ∈ K ↔ r ≤ L)) :
    radialSlice k R K x = L ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | have heq : (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)) =
        ∫⁻ r in Icc (0 : ℝ) R,
          (Icc (0 : ℝ) L).indicator (fun s => ENNReal.ofReal (s ^ k)) r := by
      first
      | apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        by_cases hrL : r ≤ L
        · have hrI : r ∈ Icc (0 : ℝ) L := ⟨hr.1, hrL⟩
          simp [radialWeight, (hfiber r hr.1).mpr hrL, Set.indicator_of_mem hrI]
        · simp [radialWeight, (hfiber r hr.1).not.mpr hrL, Set.indicator_of_notMem
            (show r ∉ Icc (0 : ℝ) L from fun h => hrL h.2)]
    have hsub : Icc (0 : ℝ) L ⊆ Icc (0 : ℝ) R := fun r hr => ⟨hr.1, hr.2.trans hLR⟩
    rw [radialSlice, heq, setLIntegral_indicator measurableSet_Icc,
      inter_eq_left.mpr hsub, lintegral_radial_pow k hL,
      ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hL _) (Nat.cast_nonneg _))]

theorem radialSlice_le_power_of_upper_bound (k : ℕ) {R L : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (K : Set (ℝ × E)) (x : E)
    (hupper : ∀ r : ℝ, 0 ≤ r → radialMap (r, x) ∈ K → r ≤ L) :
    radialSlice k R K x ≤ L ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | let S : Set (ℝ × E) := {p | p.1 ≤ L}
    have hm := radialSlice_mono_on_ray k (hL.trans hLR) K S x hupper
    rw [radialSlice_eq_power_of_interval k hL hLR S x (fun _ _ => Iff.rfl)] at hm
    exact hm

theorem power_le_radialSlice_of_lower_bound (k : ℕ) {R L : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (K : Set (ℝ × E)) (x : E)
    (hlower : ∀ r : ℝ, 0 ≤ r → r ≤ L → radialMap (r, x) ∈ K) :
    L ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ≤ radialSlice k R K x := by
  first
  | let S : Set (ℝ × E) := {p | p.1 ≤ L}
    have hm := radialSlice_mono_on_ray k (hL.trans hLR) S K x hlower
    rw [radialSlice_eq_power_of_interval k hL hLR S x (fun _ _ => Iff.rfl)] at hm
    exact hm

section Measurable

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem measurable_radialSlice (k : ℕ) (R : ℝ) {K : Set (ℝ × E)}
    (hK : MeasurableSet K) : Measurable (radialSlice k R K) :=
  ((measurable_radialWeight k hK).lintegral_prod_left'
    (μ := volume.restrict (Icc (0 : ℝ) R))).ennreal_toReal

theorem integrableOn_radialSlice (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {A : Set E} (hA : IsCompact A) {K : Set (ℝ × E)} (hK : MeasurableSet K) :
    IntegrableOn (radialSlice k R K) A := by
  first
  | letI : IsFiniteMeasure (volume.restrict A) := ⟨by
      simpa only [Measure.restrict_apply_univ] using hA.measure_lt_top⟩
    apply (integrable_const (R ^ (k + 1) / ((k + 1 : ℕ) : ℝ))).mono'
      (measurable_radialSlice k R hK).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (radialSlice_nonneg k R K x)]
      exact radialSlice_le k hR K x

theorem realVolume_clippedCone {R : ℝ} (hR : 0 ≤ R) {A : Set E} (hA : IsCompact A)
    {K : Set (ℝ × E)} (hK : IsClosed K) :
    volume.real (clippedCone R A K) = ∫ x in A, radialSlice (finrank ℝ E) R K x := by
  first
  | rw [measureReal_def, volume_clippedCone hA hK]
    exact (integral_toReal
      ((measurable_radialWeight (finrank ℝ E) hK.measurableSet).lintegral_prod_left'
        (μ := volume.restrict (Icc (0 : ℝ) R))).aemeasurable
      (Filter.Eventually.of_forall fun x => lintegral_radialWeight_lt_top _ hR K x)).symm

end Measurable
end VolumePolynomials.ClippedConeVolume
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RadialSliceIntegral.lean -/

/- BEGIN SOURCE: VolumePolynomials/RadialSectorDecomposition.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Fixed radial sectors and actual volume decomposition

The sectors are truncated rays through the old facets. They cover every set
inside a fixed positive dilation of the old polytope and have pairwise null
overlaps. Each sector is integrated in its actual linear Haar frame.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.RadialSectorDecomposition

open HalfspacePyramids LinearFrame FacetAlmostEverywhere ClippedConeVolume

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def radialTruncation (R : ℝ) (A : Set E) : Set E :=
  (fun p : ℝ × E => p.1 • p.2) '' (Icc (0 : ℝ) R ×ˢ A)

theorem radialTruncation_compact (R : ℝ) {A : Set E} (hA : IsCompact A) :
    IsCompact (radialTruncation R A) :=
  (isCompact_Icc.prod hA).image (by fun_prop)

theorem smul_body_subset_sectors (l : ι → E →L[ℝ] ℝ)
    (hC : IsCompact (body l)) {R : ℝ} (hR : 0 ≤ R) :
    R • body l ⊆ (⋃ i, radialTruncation R (face l i)) ∪ {0} := by
  first
  | rintro x ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · right
      simp only [hy0, smul_zero, mem_singleton_iff]
    · obtain ⟨i, ⟨⟨r, q⟩, ⟨hr, hq⟩, hyq⟩⟩ :=
        mem_radialHull_face_of_ne_zero l hC hy hy0
      left
      apply mem_iUnion.mpr
      refine ⟨i, (R * r, q), ⟨⟨mul_nonneg hR hr.1, ?_⟩, hq⟩, ?_⟩
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hr.2 hR
      · change (R * r) • q = R • y
        have hyq' : r • q = y := hyq
        rw [mul_smul, hyq']

theorem radialTruncation_inter_subset_ker (l : ι → E →L[ℝ] ℝ)
    (R : ℝ) (i j : ι) :
    radialTruncation R (face l i) ∩ radialTruncation R (face l j) ⊆
      LinearMap.ker ((l i - l j).toLinearMap) := by
  first
  | rintro x ⟨⟨⟨r, a⟩, ⟨hr, ha⟩, hax⟩, ⟨⟨s, b⟩, ⟨hs, hb⟩, hbx⟩⟩
    have hi : l i x = r := by
      first
      | rw [← hax, map_smul, smul_eq_mul, ha.2, mul_one]
    have hj : l j x = s := by
      first
      | rw [← hbx, map_smul, smul_eq_mul, hb.2, mul_one]
    have hij : l i x ≤ s := by
      first
      | rw [← hbx, map_smul, smul_eq_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb.1 i) hs.1
    have hji : l j x ≤ r := by
      first
      | rw [← hax, map_smul, smul_eq_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha.1 j) hr.1
    change l i x - l j x = 0
    linarith

section Measure

variable [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem radialTruncation_faces_aedisjoint (l : ι → E →L[ℝ] ℝ)
    (hl : Function.Injective l) (R : ℝ) :
    Pairwise (fun i j => AEDisjoint volume
      (radialTruncation R (face l i)) (radialTruncation R (face l j))) := by
  first
  | intro i j hij
    have hker : LinearMap.ker ((l i - l j).toLinearMap) ≠ ⊤ := by
      first
      | intro htop
        apply hij
        apply hl
        ext x
        have hx : x ∈ LinearMap.ker ((l i - l j).toLinearMap) := by
          first
          | rw [htop]
            exact Submodule.mem_top
        change l i x - l j x = 0 at hx
        exact sub_eq_zero.mp hx
    exact measure_mono_null (radialTruncation_inter_subset_ker l R i j)
      (Measure.addHaar_submodule volume _ hker)

theorem realVolume_eq_sum_sector_intersections
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l)
    (hC : IsCompact (body l)) {R : ℝ} (hR : 0 ≤ R)
    {K : Set E} (hK : IsCompact K) (hKR : K ⊆ R • body l) :
    volume.real K = ∑ i, volume.real (K ∩ radialTruncation R (face l i)) := by
  first
  | classical
    let S : ι → Set E := fun i => K ∩ radialTruncation R (face l i)
    have hcover : K ⊆ (⋃ i, S i) ∪ {0} := by
      first
      | intro x hx
        rcases smul_body_subset_sectors l hC hR (hKR hx) with hi | hz
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hi
          exact Or.inl (mem_iUnion.mpr ⟨i, hx, hi⟩)
        · exact Or.inr hz
    have hvol : volume K = volume (⋃ i, S i) := by
      first
      | apply le_antisymm
        · calc
            volume K ≤ volume ((⋃ i, S i) ∪ {0}) := measure_mono hcover
            _ ≤ volume (⋃ i, S i) + volume ({0} : Set E) := measure_union_le _ _
            _ = _ := by simp
        · exact measure_mono (iUnion_subset fun i => inter_subset_left)
    have hcomp (i : ι) : IsCompact (S i) :=
      hK.inter (radialTruncation_compact R (face_compact l hC i))
    have hdis : Pairwise (fun i j => AEDisjoint volume (S i) (S j)) := by
      first
      | intro i j hij
        exact (radialTruncation_faces_aedisjoint l hl R hij).mono inter_subset_right inter_subset_right
    rw [measureReal_def, hvol]
    change volume.real (⋃ i, S i) = _
    simpa only [S, Finset.mem_univ, iUnion_true] using
      measureReal_biUnion_finset₀ (μ := volume) (s := Finset.univ) (f := S)
      (fun i _ j _ hij => hdis hij)
      (fun i _ => (hcomp i).measurableSet.nullMeasurableSet)
      (fun i _ => (hcomp i).measure_ne_top)

end Measure

section Frame

variable [FiniteDimensional ℝ E]

theorem frame_radialMap (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (y : LinearMap.ker l.toLinearMap) (r : ℝ) :
    continuousEquiv l v hv (r • (v + y.val)) = radialMap (r, y) := by
  first
  | apply Prod.ext
    · change l (r • (v + y.val)) = r
      simp [map_smul, map_add, hv, y.property]
    · apply Subtype.ext
      change r • (v + y.val) - l (r • (v + y.val)) • v = r • y.val
      have hy0 : l y.val = 0 := y.property
      simp only [map_smul, map_add, hv, hy0, mul_zero, add_zero, smul_eq_mul, mul_one,
        smul_add]
      abel

theorem radialMap_mem_frame_image_iff (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (y : LinearMap.ker l.toLinearMap) (r : ℝ) (K : Set E) :
    radialMap (r, y) ∈ continuousEquiv l v hv '' K ↔ r • (v + y.val) ∈ K := by
  first
  | rw [← frame_radialMap l v hv y r]
    constructor
    · rintro ⟨x, hx, heq⟩
      have hxq := (continuousEquiv l v hv).injective heq
      simpa only [hxq] using hx
    · intro hx
      exact ⟨r • (v + y.val), hx, rfl⟩

theorem image_sector_frame (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E)
    (hv : l i v = 1) (R : ℝ) :
    continuousEquiv (l i) v hv '' radialTruncation R (face l i) =
      radialMap '' (Icc (0 : ℝ) R ×ˢ facetBase l i v) := by
  first
  | ext z
    constructor
    · rintro ⟨x, ⟨⟨r, q⟩, ⟨hr, hq⟩, rfl⟩, rfl⟩
      refine ⟨(r, kernelPart (l i) v hv q), ⟨hr, ?_⟩, ?_⟩
      · have he : v + (q - v) = q := by abel
        change v + (q - l i q • v) ∈ body l
        simpa only [hq.2, one_smul, he] using hq.1
      · apply Prod.ext
        · change r = l i (r • q)
          simp only [map_smul, smul_eq_mul, hq.2, mul_one]
        · change r • kernelPart (l i) v hv q = kernelPart (l i) v hv (r • q)
          exact (map_smul (kernelPart (l i) v hv) r q).symm
    · rintro ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩
      refine ⟨r • (v + y.val),
        ⟨(r, v + y.val), ⟨hr, facetBase_point_mem_face l i v hv hy⟩, rfl⟩, ?_⟩
      exact frame_radialMap (l i) v hv y r

theorem image_sector_intersection_frame
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    (R : ℝ) (K : Set E) :
    continuousEquiv (l i) v hv '' (K ∩ radialTruncation R (face l i)) =
      clippedCone R (facetBase l i v) (continuousEquiv (l i) v hv '' K) := by
  first
  | rw [Set.image_inter (continuousEquiv (l i) v hv).injective, image_sector_frame]
    exact Set.inter_comm _ _

end Frame
end VolumePolynomials.RadialSectorDecomposition
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RadialSectorDecomposition.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeConeFirstVariation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # First variation on one fixed old facet cone

The moving body is the actual Minkowski sum. The proof uses the exact radial
endpoint off the lower-dimensional intersections, a uniform polynomial bound,
and dominated convergence. The support maximizer is an actual point of the
added compact body, whose existence follows from compactness.
-/

noncomputable section
open Set Filter MeasureTheory Module
open scoped Pointwise Topology BigOperators

-- The supplied kernel MeasureSpace determines its measurable-space structure.
-- Give that projection priority over the inherited ambient subtype instance.
attribute [local instance 1100] MeasureSpace.toMeasurableSpace

namespace VolumePolynomials.PolytopeConeFirstVariation

open HalfspacePyramids LinearFrame FacetAlmostEverywhere PolytopeRadialGeometry
open RadialSectorDecomposition ClippedConeVolume ConeDerivative

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

def movingFrame (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    (A : Set E) (t : ℝ) : Set (ℝ × LinearMap.ker (l i).toLinearMap) :=
  continuousEquiv (l i) v hv '' (body l + t • A)

theorem movingFrame_compact (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E)
    (hv : l i v = 1) (hS : IsCompact (body l)) {A : Set E} (hA : IsCompact A)
    (t : ℝ) : IsCompact (movingFrame l i v hv A t) :=
  (hS.add (hA.smul t)).image (continuousEquiv (l i) v hv).continuous

theorem radialSlice_moving_bounds
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA0 : (0 : E) ∈ A) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a ∈ A, l i a ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1 / ((k + 1 : ℕ) : ℝ) ≤ radialSlice k (1 + C) (movingFrame l i v hv A t) y ∧
      radialSlice k (1 + C) (movingFrame l i v hv A t) y ≤
        (1 + t * C) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | have hq := facetBase_point_mem_face l i v hv hy
    constructor
    · simpa only [one_pow] using power_le_radialSlice_of_lower_bound k
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + C)
        (movingFrame l i v hv A t) y (by
          intro r hr hr1
          rw [movingFrame, radialMap_mem_frame_image_iff]
          exact body_subset_add_smul l hA0 t
            ((convex_body l).smul_mem_of_zero_mem (zero_mem_body l) hq.1 ⟨hr, hr1⟩))
    · apply radialSlice_le_power_of_upper_bound k (by positivity)
        (by nlinarith : 1 + t * C ≤ 1 + C)
      intro r hr hrK
      rw [movingFrame, radialMap_mem_frame_image_iff] at hrK
      rcases hrK with ⟨s, hs, z, ⟨a, ha, rfl⟩, heq⟩
      have he := congrArg (l i) heq
      simp only [map_add, map_smul, smul_eq_mul, hq.2, mul_one] at he
      have hb := mul_le_mul_of_nonneg_left (hbound a ha) ht
      linarith [hs i]

theorem radialSlice_moving_zero
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA0 : (0 : E) ∈ A) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a ∈ A, l i a ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v) :
    radialSlice k (1 + C) (movingFrame l i v hv A 0) y = 1 / ((k + 1 : ℕ) : ℝ) := by
  first
  | have h := radialSlice_moving_bounds l i v hv hA0 hC hbound k hy (t := 0)
      le_rfl zero_le_one
    simp only [zero_mul, add_zero, one_pow] at h
    exact le_antisymm h.2 h.1

theorem radialSlice_moving_quotient_bound
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA0 : (0 : E) ∈ A) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a ∈ A, l i a ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |(radialSlice k (1 + C) (movingFrame l i v hv A t) y -
        radialSlice k (1 + C) (movingFrame l i v hv A 0) y) / t| ≤ C * (1 + C) ^ k := by
  first
  | rw [radialSlice_moving_zero l i v hv hA0 hC hbound k hy]
    have hb := radialSlice_moving_bounds l i v hv hA0 hC hbound k hy ht.le ht1
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hb.1) ht.le)]
    calc
      (radialSlice k (1 + C) (movingFrame l i v hv A t) y - 1 / ((k + 1 : ℕ) : ℝ)) / t ≤
          ((1 + t * C) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
            1 / ((k + 1 : ℕ) : ℝ)) / t :=
        div_le_div_of_nonneg_right (sub_le_sub_right hb.2 _) ht.le
      _ = ((1 + t * C) ^ (k + 1) - 1) / (((k + 1 : ℕ) : ℝ) * t) := by ring
      _ ≤ _ := radialPower_quotient_bound k hC ht ht1

theorem tendsto_radialSlice_moving_quotient
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    {a : E} (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ A, l i x ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v)
    (hstrict : ∀ j, j ≠ i → l j (v + y.val) < 1) :
    Tendsto (fun t : ℝ =>
      (radialSlice k (1 + C) (movingFrame l i v hv A t) y -
        radialSlice k (1 + C) (movingFrame l i v hv A 0) y) / t)
      (𝓝[>] 0) (𝓝 (l i a)) := by
  first
  | have hc : 0 ≤ l i a := by simpa using hmax 0 hA0
    have hcC : l i a ≤ C := hbound a ha
    have hevent := (eventually_radial_mem_iff l i
      (facetBase_point_mem_face l i v hv hy) hstrict hA hA0 ha hmax).filter_mono
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 from Iio_mem_nhds zero_lt_one)
    apply (tendsto_radialPower_quotient k (l i a)).congr'
    filter_upwards [hevent, self_mem_nhdsWithin, hlt] with t ht ht0 ht1
    change 0 < t at ht0
    have hlam : 0 ≤ 1 + t * l i a := by positivity
    have hlamR : 1 + t * l i a ≤ 1 + C := by nlinarith
    rw [radialSlice_moving_zero l i v hv hA0 hC hbound k hy,
      radialSlice_eq_power_of_interval k hlam hlamR (movingFrame l i v hv A t) y]
    intro r hr
    rw [movingFrame, radialMap_mem_frame_image_iff]
    exact ht r hr

section Measure

variable [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The actual integral over one old facet has right derivative equal to its
support displacement times its actual lower-dimensional Haar measure. -/
theorem tendsto_facet_integral_quotient
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l) (hS : IsCompact (body l))
    (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    {a : E} (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ A, l i x ≤ C)
    [MeasureSpace (LinearMap.ker (l i).toLinearMap)]
    [BorelSpace (LinearMap.ker (l i).toLinearMap)]
    [Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l i).toLinearMap))] :
    Tendsto (fun t : ℝ =>
      ((∫ y in facetBase l i v, radialSlice (finrank ℝ (LinearMap.ker (l i).toLinearMap))
          (1 + C) (movingFrame l i v hv A t) y) -
        ∫ y in facetBase l i v, radialSlice (finrank ℝ (LinearMap.ker (l i).toLinearMap))
          (1 + C) (movingFrame l i v hv A 0) y) / t)
      (𝓝[>] 0) (𝓝 (l i a * volume.real (facetBase l i v))) := by
  first
  | let k := finrank ℝ (LinearMap.ker (l i).toLinearMap)
    let B := facetBase l i v
    let μ : Measure (LinearMap.ker (l i).toLinearMap) := volume.restrict B
    let F : ℝ → (LinearMap.ker (l i).toLinearMap) → ℝ :=
      fun t => radialSlice k (1 + C) (movingFrame l i v hv A t)
    have hB := facetBase_compact l hS i v hv
    letI : IsFiniteMeasure μ := ⟨by
      simpa only [μ, B, Measure.restrict_apply_univ] using hB.measure_lt_top⟩
    have hFi (t : ℝ) : Integrable (F t) μ :=
      integrableOn_radialSlice k (by positivity) hB
        (IsCompact.measurableSet (movingFrame_compact l i v hv hS hAcompact t))
    have hbound' : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ y ∂μ,
        |(F t y - F 0 y) / t| ≤ C * (1 + C) ^ k := by
      first
      | have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 from Iio_mem_nhds zero_lt_one)
        filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
        filter_upwards [ae_restrict_mem hB.measurableSet] with y hy
        exact radialSlice_moving_quotient_bound l i v hv hA0 hC hbound k hy ht ht1.le
    have hlim : ∀ᵐ y ∂μ, Tendsto (fun t : ℝ => (F t y - F 0 y) / t)
        (𝓝[>] 0) (𝓝 (l i a)) := by
      first
      | filter_upwards [ae_restrict_mem hB.measurableSet,
          ae_strict_other_facets l hl hS i v hv volume] with y hy hstrict
        exact tendsto_radialSlice_moving_quotient l i v hv hA hA0 ha hmax hC hbound k hy hstrict
    have h := tendsto_integral_difference_quotient μ F (fun _ => l i a)
      (C * (1 + C) ^ k) (hFi 0) (Eventually.of_forall hFi) hbound' hlim
    simpa only [F, k, μ, B, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, mul_comm] using h

end Measure
end VolumePolynomials.PolytopeConeFirstVariation
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeConeFirstVariation.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeFirstVariation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Actual first variation of a finite halfspace polytope

The derivative is proved by summing fixed old facet sectors. Each coefficient
is the actual Haar change-of-frame factor times the actual facet-base measure.
No mixed-volume formula, divergence theorem, or cancellation of moving facet
derivatives is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Module
open scoped Pointwise Topology BigOperators

-- Keep the specified facet measures and their Borel structures on the same
-- measurable space when the facet is presented as an ambient subtype.
attribute [local instance 1100] MeasureSpace.toMeasurableSpace

namespace VolumePolynomials.PolytopeFirstVariation

open HalfspacePyramids LinearFrame FacetAlmostEverywhere PolytopeRadialGeometry
open RadialSectorDecomposition ClippedConeVolume PolytopeConeFirstVariation
open OAI.Paper092

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

section GivenFacetMeasures

variable (l : ι → E →L[ℝ] ℝ)
  [∀ i, MeasureSpace (LinearMap.ker (l i).toLinearMap)]
  [∀ i, BorelSpace (LinearMap.ker (l i).toLinearMap)]
  [∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l i).toLinearMap))]

def facetWeight (i : ι) (v : E) (hv : l i v = 1) : ℝ :=
  (volumeFactor (continuousEquiv (l i) v hv) : ℝ) * volume.real (facetBase l i v)

theorem facetWeight_nonneg (i : ι) (v : E) (hv : l i v = 1) :
    0 ≤ facetWeight l i v hv :=
  mul_nonneg (NNReal.coe_nonneg _) measureReal_nonneg

theorem realVolume_add_smul_translate (S A : Set E) (a : E) (t : ℝ) :
    volume.real (S + t • (({a} : Set E) + A)) = volume.real (S + t • A) := by
  first
  | rw [smul_add, Set.smul_set_singleton,
      show S + (({t • a} : Set E) + t • A) = ({t • a} : Set E) + (S + t • A) by ac_rfl,
      Set.singleton_add]
    simp only [measureReal_def, Set.image_add_left, measure_preimage_add]

theorem sector_volume_identity (hS : IsCompact (body l)) (i : ι)
    (v : E) (hv : l i v = 1) {A : Set E} (hA : IsCompact A)
    {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    volume.real ((body l + t • A) ∩ radialTruncation R (face l i)) =
      (volumeFactor (continuousEquiv (l i) v hv) : ℝ) *
        ∫ y in facetBase l i v, radialSlice (finrank ℝ (LinearMap.ker (l i).toLinearMap))
          R (movingFrame l i v hv A t) y := by
  first
  | rw [realVolume_eq_factor_mul_image (continuousEquiv (l i) v hv),
      image_sector_intersection_frame]
    change (volumeFactor (continuousEquiv (l i) v hv) : ℝ) *
      volume.real (clippedCone R (facetBase l i v) (movingFrame l i v hv A t)) = _
    rw [realVolume_clippedCone hR (facetBase_compact l hS i v hv)
      (IsCompact.isClosed (movingFrame_compact l i v hv hS hA t))]

theorem tendsto_sector_volume_quotient
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    {a : E} (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ A, l i x ≤ C) :
    Tendsto (fun t : ℝ =>
      (volume.real ((body l + t • A) ∩ radialTruncation (1 + C) (face l i)) -
        volume.real ((body l + (0 : ℝ) • A) ∩ radialTruncation (1 + C) (face l i))) / t)
      (𝓝[>] 0) (𝓝 (facetWeight l i v hv * l i a)) := by
  first
  | have h := Filter.Tendsto.const_mul
      (volumeFactor (continuousEquiv (l i) v hv) : ℝ)
      (tendsto_facet_integral_quotient l hl hS i v hv hAcompact hA hA0 ha hmax hC hbound)
    have heq : (volumeFactor (continuousEquiv (l i) v hv) : ℝ) *
        (l i a * volume.real (facetBase l i v)) = facetWeight l i v hv * l i a := by
      first
      | unfold facetWeight
        ring
    rw [heq] at h
    apply h.congr'
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [sector_volume_identity l hS i v hv hAcompact (by positivity) t,
        sector_volume_identity l hS i v hv hAcompact (by positivity) 0]
      ring

/-- First variation for any compact convex added set containing the origin.
All support values on the right are the actual suprema on that set. -/
theorem tendsto_volume_quotient_centered
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A) :
    Tendsto (fun t : ℝ => (volume.real (body l + t • A) - volume.real (body l)) / t)
      (𝓝[>] 0)
      (𝓝 (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))) := by
  first
  | classical
    obtain ⟨C, hC, hbound⟩ := exists_uniform_normal_bound l hAcompact
    choose a ha hsupp using fun i => SupportGeometry.exists_support hAcompact ⟨0, hA0⟩ (l i)
    have hmax (i : ι) (x : E) (hx : x ∈ A) : l i x ≤ l i (a i) := by
      first
      | rw [hsupp i]
        exact SupportGeometry.le_support hAcompact (l i) hx
    let f : ι → ℝ → ℝ := fun i t =>
      volume.real ((body l + t • A) ∩ radialTruncation (1 + C) (face l i))
    have hlim (i : ι) :
        Tendsto (fun t : ℝ => (f i t - f i 0) / t) (𝓝[>] 0)
          (𝓝 (facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))) := by
      first
      | rw [← hsupp i]
        exact tendsto_sector_volume_quotient l hl hS i (v i) (hv i) hAcompact hA hA0
          (ha i) (hmax i) hC (fun x hx => (le_abs_self _).trans (hbound i x hx))
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
    have hdecomp {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
        volume.real (body l + t • A) = ∑ i, f i t := by
      first
      | apply realVolume_eq_sum_sector_intersections l hl hS (by positivity)
          (hS.add (hAcompact.smul t))
        intro x hx
        apply Iff.mpr (mem_smul_body_iff l (by positivity : 0 < 1 + C) x)
        have hx' := add_smul_subset_smul_body l hC ht
          (fun i a ha => (le_abs_self _).trans (hbound i a ha)) hx
        have hb := Iff.mp (mem_smul_body_iff l (by positivity : 0 < 1 + t * C) x) hx'
        intro i
        exact (hb i).trans (by nlinarith)
    have hzero : body l + (0 : ℝ) • A = body l := by
      first
      | rw [Set.zero_smul_set ⟨0, hA0⟩]
        simp
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 from Iio_mem_nhds zero_lt_one)
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
    rw [hdecomp ht.le ht1.le, ← hzero, hdecomp le_rfl zero_le_one,
      ← Finset.sum_sub_distrib, Finset.sum_div]

/-- The balance identity follows from actual translation invariance applied to
the two oppositely oriented segments. It is not an assumed divergence theorem. -/
theorem facet_balance
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1) (a : E) :
    (∑ i, facetWeight l i (v i) (hv i) * l i a) = 0 := by
  first
  | have hp := tendsto_volume_quotient_centered l hl hS v hv
      (SupportGeometry.isCompact_segment (0 : E) a) (convex_segment (0 : E) a)
      (left_mem_segment ℝ (0 : E) a)
    have hm := tendsto_volume_quotient_centered l hl hS v hv
      (SupportGeometry.isCompact_segment (0 : E) (-a)) (convex_segment (0 : E) (-a))
      (left_mem_segment ℝ (0 : E) (-a))
    have htranslate : segment ℝ (0 : E) a = ({a} : Set E) + segment ℝ (0 : E) (-a) := by
      first
      | rw [Set.singleton_add]
        change segment ℝ (0 : E) a = a +ᵥ segment ℝ (0 : E) (-a)
        rw [vadd_segment]
        simp only [vadd_eq_add, add_zero, add_neg_cancel]
        exact segment_symm ℝ 0 a
    have hsame (t : ℝ) : volume.real (body l + t • segment ℝ (0 : E) a) =
        volume.real (body l + t • segment ℝ (0 : E) (-a)) := by
      first
      | rw [htranslate, realVolume_add_smul_translate]
    have heq := tendsto_nhds_unique hp (hm.congr' (Eventually.of_forall fun t => by
      dsimp only
      rw [hsame]))
    simp only [SupportGeometry.support_segment, map_zero, map_neg] at heq
    have hmax (x : ℝ) : max 0 x - max 0 (-x) = x := by
      first
      | by_cases hx : 0 ≤ x
        · rw [max_eq_right hx, max_eq_left (neg_nonpos.mpr hx), sub_zero]
        · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
          rw [max_eq_left hx', max_eq_right (neg_nonneg.mpr hx'), zero_sub, neg_neg]
    calc
      (∑ i, facetWeight l i (v i) (hv i) * l i a) =
          ∑ i, facetWeight l i (v i) (hv i) * (max 0 (l i a) - max 0 (-l i a)) := by
        first
        | simp only [hmax]
      _ = (∑ i, facetWeight l i (v i) (hv i) * max 0 (l i a)) -
          ∑ i, facetWeight l i (v i) (hv i) * max 0 (-l i a) := by
        first
        | simp only [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr heq

/-- Full first variation for an arbitrary nonempty compact convex added set.
The support values and Haar facet weights retain their literal meanings. -/
theorem tendsto_volume_quotient
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    Tendsto (fun t : ℝ => (volume.real (body l + t • A) - volume.real (body l)) / t)
      (𝓝[>] 0)
      (𝓝 (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))) := by
  first
  | classical
    obtain ⟨a, ha⟩ := hAne
    let A' : Set E := ({-a} : Set E) + A
    have hA'compact : IsCompact A' := isCompact_singleton.add hAcompact
    have hA' : Convex ℝ A' := (convex_singleton (-a)).add hA
    have hA'0 : (0 : E) ∈ A' := ⟨-a, rfl, a, ha, neg_add_cancel a⟩
    have hsupp (i : ι) : SupportGeometry.support A' (l i) =
        -l i a + SupportGeometry.support A (l i) := by
      first
      | dsimp only [A']
        rw [SupportGeometry.support_add isCompact_singleton (singleton_nonempty _)
          hAcompact ⟨a, ha⟩]
        simp [SupportGeometry.support, map_neg]
    have h := tendsto_volume_quotient_centered l hl hS v hv hA'compact hA' hA'0
    have hsum : (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A' (l i)) =
        ∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i) := by
      first
      | simp_rw [hsupp, mul_add, mul_neg]
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, facet_balance l hl hS v hv a,
          neg_zero, zero_add]
    rw [hsum] at h
    apply h.congr'
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [show A' = ({-a} : Set E) + A from rfl, realVolume_add_smul_translate]

theorem hasDerivWithinAt_volume
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (body l + t • A))
      (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i)) (Ioi 0) 0 := by
  first
  | apply (hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mpr
    have hzero : body l + (0 : ℝ) • A = body l := by
      first
      | rw [Set.zero_smul_set hAne]
        simp
    change Tendsto (fun t : ℝ => slope (fun s : ℝ => volume.real (body l + s • A)) 0 t) _ _
    simpa only [slope_def_field, hzero, sub_zero] using
      tendsto_volume_quotient l hl hS v hv hAcompact hA hAne

end GivenFacetMeasures

/-- Canonical actual Haar measures on the facet kernels, so the final endpoint
has no unprovided family of lower-dimensional measures as a hypothesis. -/
def canonicalFacetWeight (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1) : ℝ :=
  letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
  letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
    fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
  facetWeight l i v hv

theorem canonicalFacetWeight_nonneg (l : ι → E →L[ℝ] ℝ)
    (i : ι) (v : E) (hv : l i v = 1) : 0 ≤ canonicalFacetWeight l i v hv := by
  first
  | letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
    letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
      fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
    exact facetWeight_nonneg l i v hv

theorem firstVariation_coefficient_mono (l : ι → E →L[ℝ] ℝ)
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A B : Set E} (hA : A.Nonempty) (hB : IsCompact B) (hAB : A ⊆ B) :
    (∑ i, canonicalFacetWeight l i (v i) (hv i) * SupportGeometry.support A (l i)) ≤
      ∑ i, canonicalFacetWeight l i (v i) (hv i) * SupportGeometry.support B (l i) := by
  first
  | apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (canonicalFacetWeight_nonneg l i (v i) (hv i))
    exact SupportGeometry.support_le hA (l i)
      (fun x hx => SupportGeometry.le_support hB (l i) (hAB hx))

theorem first_variation (l : ι → E →L[ℝ] ℝ)
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (body l + t • A))
      (∑ i, canonicalFacetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))
      (Ioi 0) 0 := by
  first
  | letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
    letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
      fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
    exact hasDerivWithinAt_volume l hl hS v hv hAcompact hA hAne

end VolumePolynomials.PolytopeFirstVariation
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeFirstVariation.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolyhedralSupport.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Finite halfspace systems and generic support heights

The exceptional support vectors form a finite union of proper linear
subspaces. Outside this union every feasible active system is independent,
and at an extreme point it is an actual coordinate system. This is the
linear-algebraic content of the simple-polytope perturbation argument in
Schneider, *Convex Bodies*, Lemmas 2.4.13--2.4.14.

No assertion about mixed volumes is assumed or encoded in these definitions.
-/

noncomputable section
open Set Filter Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def body (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Set E :=
  {x | ∀ i, l i x ≤ h i}

theorem body_convex (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    Convex ℝ (body l h) := by
  first
  | have he (i : ι) : (l i).toLinearMap ⁻¹' Iic (h i) = {x : E | l i x ≤ h i} := by
      ext x
      simp only [mem_preimage, mem_Iic, ContinuousLinearMap.coe_coe, mem_ofPred_eq]
    simpa only [body, Set.ofPred_forall, he] using
      (convex_iInter fun i => (convex_Iic (h i)).linear_preimage (l i).toLinearMap)

theorem body_isClosed (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    IsClosed (body l h) := by
  first
  | simpa only [body, Set.ofPred_forall] using
      (isClosed_iInter fun i => isClosed_le (l i).continuous (continuous_const (y := h i)))

def restriction (s : Finset ι) : (ι → ℝ) →ₗ[ℝ] (s → ℝ) where
  toFun h i := h i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evaluation (l : ι → E →L[ℝ] ℝ) (s : Finset ι) : E →ₗ[ℝ] (s → ℝ) :=
  LinearMap.pi (fun i : s => (l i).toLinearMap)

@[simp] theorem restriction_apply (s : Finset ι) (h : ι → ℝ) (i : s) :
    restriction s h i = h i := rfl

@[simp] theorem evaluation_apply (l : ι → E →L[ℝ] ℝ)
    (s : Finset ι) (x : E) (i : s) : evaluation l s x i = l i x := rfl

theorem restriction_surjective (s : Finset ι) : Function.Surjective (restriction s) := by
  first
  | intro r
    refine ⟨fun i => if hi : i ∈ s then r ⟨i, hi⟩ else 0, ?_⟩
    funext i
    simp only [restriction_apply, dif_pos i.property]

/-- Heights on `s` that are jointly attained by some point of the ambient
space. If the active equations are dependent, this is a proper subspace. -/
def compatibleHeights (l : ι → E →L[ℝ] ℝ) (s : Finset ι) :
    Submodule ℝ (ι → ℝ) := (evaluation l s).range.comap (restriction s)

theorem mem_compatibleHeights (l : ι → E →L[ℝ] ℝ) (s : Finset ι) (h : ι → ℝ) :
    h ∈ compatibleHeights l s ↔ ∃ x : E, ∀ i ∈ s, l i x = h i := by
  first
  | constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, fun i hi => congrFun hx ⟨i, hi⟩⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, funext fun i => hx i i.property⟩

theorem compatibleHeights_ne_top (l : ι → E →L[ℝ] ℝ) (s : Finset ι)
    (hs : ¬ Function.Surjective (evaluation l s)) : compatibleHeights l s ≠ ⊤ := by
  first
  | intro heq
    apply hs
    intro r
    obtain ⟨h, hh⟩ := restriction_surjective s r
    have hm : h ∈ compatibleHeights l s := by rw [heq]; trivial
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, hx.trans hh⟩

def Generic (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Prop :=
  ∀ s : Finset ι, h ∈ compatibleHeights l s →
    Function.Surjective (evaluation l s)

open scoped Classical in
theorem generic_eq_iInter (l : ι → E →L[ℝ] ℝ) :
    {h | Generic l h} = ⋂ s : Finset ι,
      if Function.Surjective (evaluation l s) then Set.univ
      else (compatibleHeights l s : Set (ι → ℝ))ᶜ := by
  first
  | classical
    ext h
    simp only [Generic, mem_setOf_eq, mem_iInter]
    apply forall_congr'
    intro s
    by_cases hs : Function.Surjective (evaluation l s) <;> simp [hs]

theorem isOpen_generic (l : ι → E →L[ℝ] ℝ) : IsOpen {h | Generic l h} := by
  first
  | classical
    rw [generic_eq_iInter]
    apply isOpen_iInter_of_finite
    intro s
    split_ifs
    · exact isOpen_univ
    · exact (compatibleHeights l s).closed_of_finiteDimensional.isOpen_compl

/-- Generic support vectors occur in every nonempty open subset of the full
space of heights; no restriction of the number of facets is imposed. -/
theorem dense_generic (l : ι → E →L[ℝ] ℝ) : Dense {h | Generic l h} := by
  first
  | classical
    rw [generic_eq_iInter]
    apply dense_iInter_of_isOpen
    · intro s
      split_ifs
      · exact isOpen_univ
      · exact (compatibleHeights l s).closed_of_finiteDimensional.isOpen_compl
    · intro s
      split_ifs with hs
      · exact dense_univ
      · apply interior_eq_empty_iff_dense_compl.mp
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hi
        exact compatibleHeights_ne_top l s hs
          ((compatibleHeights l s).eq_top_of_nonempty_interior' hi)

def active (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (x : E) : Finset ι :=
  Finset.univ.filter fun i => l i x = h i

@[simp] theorem mem_active (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (x : E) (i : ι) :
    i ∈ active l h x ↔ l i x = h i := by simp [active]

/-- A point with the same active equalities as an extreme point must equal
that extreme point. The proof uses a two-sided sufficiently small segment. -/
theorem extreme_active_unique (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {x y : E} (hx : x ∈ (body l h).extremePoints ℝ)
    (hy : ∀ i, l i x = h i → l i y = h i) : y = x := by
  first
  | have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,
        l i x < h i → l i (x + t • (y - x)) < h i := by
      apply Filter.eventually_all.mpr
      intro i
      by_cases hi : l i x < h i
      · have ht : ∀ᶠ t : ℝ in 𝓝 0, l i (x + t • (y - x)) < h i :=
          (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hi)
        filter_upwards [ht] with t ht
        exact fun _ => ht
      · exact Filter.Eventually.of_forall fun _ hi' => (hi hi').elim
    obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
    have hpert (t : ℝ) (ht : dist t 0 < ε) : x + t • (y - x) ∈ body l h := by
      intro i
      rcases (hx.1 i).lt_or_eq with hi | hi
      · exact (hsmall ht i hi).le
      · simp only [map_add, map_smul, map_sub, smul_eq_mul, hi, hy i hi,
          sub_self, mul_zero, add_zero, le_refl]
    have hp : dist (ε / 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith
    have hm : dist (-(ε / 2)) 0 < ε := by simpa using hp
    have he := hx.2 (hpert (ε / 2) hp)
      (show x - (ε / 2) • (y - x) ∈ body l h by
        simpa only [neg_smul, ← sub_eq_add_neg] using hpert (-(ε / 2)) hm)
      (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • (y - x)))
    have hz : (ε / 2) • (y - x) = 0 := add_left_cancel (he.trans (add_zero x).symm)
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt (half_pos hε)))

theorem active_evaluation_injective (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    Function.Injective (evaluation l (active l h v)) := by
  first
  | intro x y hxy
    have hz : v + (x - y) = v := by
      apply extreme_active_unique l h hv
      intro i hi
      have he : l i x = l i y := congrFun hxy ⟨i, (mem_active l h v i).mpr hi⟩
      simp [map_add, map_sub, hi, he]
    have hzero : x - y = 0 := add_left_cancel (hz.trans (add_zero v).symm)
    exact sub_eq_zero.mp hzero

theorem active_evaluation_bijective (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    Function.Bijective (evaluation l (active l h v)) := by
  first
  | refine ⟨active_evaluation_injective l h hv, hg (active l h v) ?_⟩
    exact (mem_compatibleHeights l _ h).mpr ⟨v, fun i hi => (mem_active l h v i).mp hi⟩

/-- The finite type of sets of normals that give an ambient coordinate system. -/
def BasisIndex (l : ι → E →L[ℝ] ℝ) :=
  {s : Finset ι // Function.Bijective (evaluation l s)}

instance basisIndex_fintype (l : ι → E →L[ℝ] ℝ) : Fintype (BasisIndex l) := by
  classical
  change Fintype {s : Finset ι // Function.Bijective (evaluation l s)}
  exact Fintype.ofFinite _

def coordinates (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) : E ≃L[ℝ] (b.val → ℝ) :=
  (LinearEquiv.ofBijective (evaluation l b.val) b.property).toContinuousLinearEquiv

@[simp] theorem coordinates_apply (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (x : E) (i : b.val) : coordinates l b x i = l i x := rfl

def vertexMap (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) : (ι → ℝ) →L[ℝ] E :=
  ((coordinates l b).symm.toLinearMap.comp (restriction b.val)).toContinuousLinearMap

@[simp] theorem vertexMap_active (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (h : ι → ℝ) (i : b.val) : l i (vertexMap l b h) = h i := by
  first
  | change (coordinates l b ((coordinates l b).symm (restriction b.val h))) i = h i
    simp only [ContinuousLinearEquiv.apply_symm_apply, restriction_apply]

theorem vertexMap_unique (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (h : ι → ℝ) {x : E} (hx : ∀ i ∈ b.val, l i x = h i) :
    vertexMap l b h = x := by
  first
  | apply (coordinates l b).injective
    funext i
    exact (vertexMap_active l b h i).trans (hx i i.property).symm

theorem extreme_eq_vertexMap (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    ∃ b : BasisIndex l, vertexMap l b h = v := by
  first
  | refine ⟨⟨active l h v, active_evaluation_bijective l h hg hv⟩, ?_⟩
    exact vertexMap_unique l _ h (fun i hi => (mem_active l h v i).mp hi)

theorem vertexMap_mem_extremePoints (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (h : ι → ℝ) (hv : vertexMap l b h ∈ body l h) :
    vertexMap l b h ∈ (body l h).extremePoints ℝ := by
  first
  | refine ⟨hv, ?_⟩
    intro x hx y hy hseg
    apply (coordinates l b).injective
    funext i
    have he : IsExposed ℝ (body l h) ((l i).toExposed (body l h)) :=
      ContinuousLinearMap.toExposed.isExposed
    have hve : vertexMap l b h ∈ (l i).toExposed (body l h) := by
      refine ⟨hv, fun z hz => ?_⟩
      rw [vertexMap_active]
      exact hz i
    have hxe := he.isExtreme.left_mem_of_mem_openSegment hx hy hve hseg
    have hmax := hxe.2 (vertexMap l b h) hv
    rw [vertexMap_active] at hmax
    exact (le_antisymm (hx i) hmax).trans (vertexMap_active l b h i).symm

theorem finite_extremePoints (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    ((body l h).extremePoints ℝ).Finite := by
  first
  | have hinj : Set.InjOn (active l h) ((body l h).extremePoints ℝ) := by
      intro x hx y _ hxy
      apply (extreme_active_unique l h hx ?_).symm
      intro i hi
      have hm := (mem_active l h x i).mpr hi
      rw [hxy] at hm
      exact (mem_active l h y i).mp hm
    exact (Set.toFinite (Set.univ : Set (Finset ι))).of_injOn
      (fun _ _ => Set.mem_univ _) hinj

theorem body_eq_convexHull_extremePoints (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (body l h)) :
    body l h = convexHull ℝ ((body l h).extremePoints ℝ) := by
  first
  | have he := closure_convexHull_extremePoints hc (body_convex l h)
    rw [(finite_extremePoints l h).isClosed_convexHull ℝ |>.closure_eq] at he
    exact he.symm

theorem generic_active_card (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    (active l h v).card = finrank ℝ E := by
  first
  | let b : BasisIndex l := ⟨active l h v, active_evaluation_bijective l h hg hv⟩
    have he := (coordinates l b).toLinearEquiv.finrank_eq
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe] using he.symm

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 25
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolyhedralSupport.lean -/

/- BEGIN SOURCE: VolumePolynomials/FacetWeightPyramid.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# First variation in fixed, unnormalized facet coordinates

The normalization is justified through actual pyramid volumes. For a facet
at normalized height one, its first-variation weight is the ambient dimension
times its radial pyramid volume. Computing that same pyramid in a fixed
unnormalized frame multiplies the fixed facet weight by its height. The
inverse height in the support function cancels it. Thus no identification of
different kernel measures is assumed or hidden in a change of coordinates.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

-- Let the explicitly supplied kernel measure choose its Borel measurable
-- structure before the generic measurable-space instance for a subtype.
attribute [local instance 1100] MeasureSpace.toMeasurableSpace

namespace VolumePolynomials.FacetWeightPyramid

open HalfspacePyramids LinearFrame FacetAlmostEverywhere PolytopeFirstVariation
open OAI.Paper092

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem facetWeight_eq_dimension_mul_pyramid
    (l : ι → E →L[ℝ] ℝ)
    [∀ i, MeasureSpace (LinearMap.ker (l i).toLinearMap)]
    [∀ i, BorelSpace (LinearMap.ker (l i).toLinearMap)]
    [∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l i).toLinearMap))]
    (hS : IsCompact (body l)) (i : ι) (v : E) (hv : l i v = 1) :
    facetWeight l i v hv = (finrank ℝ E : ℝ) *
      volume.real (PyramidVolume.radialHull (face l i)) := by
  first
  | have he := PyramidVolume.realVolume_radialHull_of_equiv
      (continuousEquiv (l i) v hv) (face_compact l hS i)
      (fun x hx => (show l i x = 1 from hx.2))
    rw [← facetBase_eq_image l i v hv, abs_one, mul_one,
      finrank_kernel_add_one (l i) v hv] at he
    have hd : (finrank ℝ E : ℝ) ≠ 0 := by
      first
      | have hn : finrank ℝ E ≠ 0 := by
          rw [← finrank_kernel_add_one (l i) v hv]
          omega
        exact_mod_cast hn
    rw [he, facetWeight]
    field_simp [hd]

theorem canonicalFacetWeight_eq_dimension_mul_pyramid
    (l : ι → E →L[ℝ] ℝ) (hS : IsCompact (body l))
    (i : ι) (v : E) (hv : l i v = 1) :
    canonicalFacetWeight l i v hv = (finrank ℝ E : ℝ) *
      volume.real (PyramidVolume.radialHull (face l i)) := by
  first
  | letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
    letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
      fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
    exact facetWeight_eq_dimension_mul_pyramid l hS i v hv

def normalized (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (i : ι) : E →L[ℝ] ℝ :=
  (h i)⁻¹ • u i

def fixedFace (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (i : ι) : Set E :=
  {x | x ∈ PolyhedralSupport.body u h ∧ u i x = h i}

theorem normalized_body (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) : body (normalized u h) = PolyhedralSupport.body u h := by
  first
  | ext x
    apply forall_congr'
    intro i
    change (h i)⁻¹ * u i x ≤ 1 ↔ u i x ≤ h i
    rw [← div_eq_inv_mul, div_le_one (hp i)]

theorem normalized_face (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) (i : ι) : face (normalized u h) i = fixedFace u h i := by
  first
  | ext x
    change (x ∈ body (normalized u h) ∧ (h i)⁻¹ * u i x = 1) ↔ _
    rw [normalized_body u h hp, ← div_eq_inv_mul, div_eq_one_iff_eq (hp i).ne']
    rfl

theorem normalized_injective (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i)
    (hrel : ∀ i j {c : ℝ}, 0 < c → u i = c • u j → i = j) :
    Function.Injective (normalized u h) := by
  first
  | intro i j hij
    apply hrel i j (div_pos (hp i) (hp j))
    have he := congrArg (fun f : E →L[ℝ] ℝ => h i • f) hij
    simpa only [normalized, smul_smul, mul_inv_cancel₀ (hp i).ne', one_smul,
      div_eq_mul_inv] using he

theorem normalized_unit (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) (i : ι) (v : E) (hv : u i v = 1) :
    normalized u h i (h i • v) = 1 := by
  first
  | simp only [normalized, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul,
      hv, mul_one, inv_mul_cancel₀ (hp i).ne', mul_inv_cancel₀ (hp i).ne']

section FixedMeasures

variable (u : ι → E →L[ℝ] ℝ)
  [∀ i, MeasureSpace (LinearMap.ker (u i).toLinearMap)]
  [∀ i, BorelSpace (LinearMap.ker (u i).toLinearMap)]
  [∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (u i).toLinearMap))]

def fixedFacetBase (h : ι → ℝ) (i : ι) (v : E) (hv : u i v = 1) :
    Set (LinearMap.ker (u i).toLinearMap) :=
  Prod.snd '' (continuousEquiv (u i) v hv '' fixedFace u h i)

def fixedFacetWeight (h : ι → ℝ) (i : ι) (v : E) (hv : u i v = 1) : ℝ :=
  (volumeFactor (continuousEquiv (u i) v hv) : ℝ) * volume.real (fixedFacetBase u h i v hv)

theorem dimension_mul_pyramid_eq_height_mul_weight
    (h : ι → ℝ) (hp : ∀ i, 0 < h i) (hS : IsCompact (PolyhedralSupport.body u h))
    (i : ι) (v : E) (hv : u i v = 1) :
    (finrank ℝ E : ℝ) * volume.real (PyramidVolume.radialHull (fixedFace u h i)) =
      h i * fixedFacetWeight u h i v hv := by
  first
  | have hface : IsCompact (fixedFace u h i) :=
      hS.inter_right (isClosed_eq (u i).continuous continuous_const)
    have he := PyramidVolume.realVolume_radialHull_of_equiv
      (continuousEquiv (u i) v hv) hface (fun x hx => hx.2)
    rw [abs_of_pos (hp i), finrank_kernel_add_one (u i) v hv] at he
    have hd : (finrank ℝ E : ℝ) ≠ 0 := by
      first
      | have hn : finrank ℝ E ≠ 0 := by
          rw [← finrank_kernel_add_one (u i) v hv]
          omega
        exact_mod_cast hn
    rw [he, fixedFacetWeight, fixedFacetBase]
    field_simp [hd]

theorem normalized_weight_mul_support (h : ι → ℝ) (hp : ∀ i, 0 < h i)
    (hS : IsCompact (PolyhedralSupport.body u h)) (i : ι) (v : E) (hv : u i v = 1)
    (A : Set E) :
    canonicalFacetWeight (normalized u h) i (h i • v) (normalized_unit u h hp i v hv) *
      SupportGeometry.support A (normalized u h i) =
        fixedFacetWeight u h i v hv * SupportGeometry.support A (u i) := by
  first
  | have hSn : IsCompact (body (normalized u h)) := by rwa [normalized_body u h hp]
    rw [canonicalFacetWeight_eq_dimension_mul_pyramid (normalized u h) hSn,
      normalized_face u h hp,
      dimension_mul_pyramid_eq_height_mul_weight u h hp hS i v hv]
    have hs : SupportGeometry.support A (normalized u h i) =
        (h i)⁻¹ * SupportGeometry.support A (u i) := by
      first
      | unfold SupportGeometry.support normalized
        rw [show ((h i)⁻¹ • u i) '' A = (h i)⁻¹ • (u i '' A) by
          ext y; simp only [Set.mem_image, Set.mem_smul_set, ContinuousLinearMap.smul_apply];
          constructor
          · rintro ⟨x, hx, rfl⟩; exact ⟨u i x, ⟨x, hx, rfl⟩, rfl⟩
          · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩]
        simpa only [smul_eq_mul] using
          Real.sSup_smul_of_nonneg (inv_nonneg.mpr (hp i).le) (u i '' A)
    rw [hs]
    field_simp [(hp i).ne']

/-- First variation with arbitrary positive heights and fixed lower-dimensional
kernel spaces. Every weight is a literal frame factor times a literal facet
measure, so it is suitable for exact coefficient comparison. -/
theorem first_variation_fixed_heights
    (h : ι → ℝ) (hp : ∀ i, 0 < h i)
    (hrel : ∀ i j {c : ℝ}, 0 < c → u i = c • u j → i = j)
    (hS : IsCompact (PolyhedralSupport.body u h))
    (v : ι → E) (hv : ∀ i, u i (v i) = 1)
    {A : Set E} (hAc : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (PolyhedralSupport.body u h + t • A))
      (∑ i, fixedFacetWeight u h i (v i) (hv i) * SupportGeometry.support A (u i))
      (Ioi 0) 0 := by
  first
  | have hSn : IsCompact (body (normalized u h)) := by rwa [normalized_body u h hp]
    have hd := PolytopeFirstVariation.first_variation (normalized u h)
      (normalized_injective u h hp hrel) hSn (fun i => h i • v i)
      (fun i => normalized_unit u h hp i (v i) (hv i)) hAc hA hAne
    rw [normalized_body u h hp] at hd
    have he : (∑ i, canonicalFacetWeight (normalized u h) i (h i • v i)
        (normalized_unit u h hp i (v i) (hv i)) * SupportGeometry.support A (normalized u h i)) =
        ∑ i, fixedFacetWeight u h i (v i) (hv i) * SupportGeometry.support A (u i) :=
      Finset.sum_congr rfl (fun i _ => normalized_weight_mul_support u h hp hS i (v i) (hv i) A)
    rw [he] at hd
    exact hd

end FixedMeasures
end VolumePolynomials.FacetWeightPyramid
end -- closes the original EOF section from source line 22
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FacetWeightPyramid.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedFacetIdentity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The mixed-facet identity from genuine first variation

The first-variable coefficient is identified on the entire positive orthant,
then its squarefree coefficient is extracted. Lower-dimensional coefficient
nonnegativity comes from the proved volume-polynomial theorem, not from
pointwise comparison of unrelated polynomials.
-/

noncomputable section
open Set Filter MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092
open LinearFrame FacetWeightPyramid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

def facetFrameFactor (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) : ℝ :=
  letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
    kernelMeasure_isAddHaarMeasure l
  volumeFactor (continuousEquiv l v hv)

theorem facetFrameFactor_nonneg (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    0 ≤ facetFrameFactor l v hv := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    exact NNReal.coe_nonneg _

def facetDerivativePolynomial {n : ℕ} (K : Fin n → ConvexBody E)
    (D : FixedFacets (fun j => (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1) (A : ConvexBody E) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, C (facetFrameFactor (D.normal i) (v i) (hv i) *
      SupportGeometry.support (A : Set E) (D.normal i)) *
    volumePolynomial (kernelMeasure (D.normal i))
      (fun j => kernelBody (K j) (D.normal i) (v i) (hv i))

theorem firstVariableCoefficient_eq_facetPolynomial {n : ℕ}
    (K : Fin n → ConvexBody E) (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1) (A : ConvexBody E) :
    firstVariableCoefficient (volumePolynomial volume (Fin.cons A K)) =
      facetDerivativePolynomial K D v hv A := by
  first
  | classical
    letI : ∀ i, MeasureSpace (LinearMap.ker (D.normal i).toLinearMap) :=
      fun i => ⟨kernelMeasure (D.normal i)⟩
    letI : ∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (D.normal i).toLinearMap)) :=
      fun i => kernelMeasure_isAddHaarMeasure (D.normal i)
    apply MvPolynomial.funext_set (fun _ => Ioi (0 : ℝ)) (fun _ => Ioi_infinite 0)
    intro t ht'
    have ht : ∀ j, 0 < t j := fun j => ht' j (mem_univ j)
    have hp : ∀ i, 0 < D.height t i :=
      D.height_pos (fun j => (K j).isCompact) h0 hint t ht
    have hbody : PolyhedralSupport.body D.normal (D.height t) =
        (↑(∑ j, t j • K j) : Set E) := by
      first
      | rw [coe_sum_body]
        exact (D.body_eq t ht).symm
    have hS : IsCompact (PolyhedralSupport.body D.normal (D.height t)) := by
      first
      | rw [hbody]
        exact (∑ j, t j • K j).isCompact
    have hface (i : Fin D.count) : fixedFace D.normal (D.height t) i =
        (D.normal i).toExposed (∑ j, t j • (K j : Set E)) := by
      first
      | have hc : IsCompact (∑ j, t j • (K j : Set E)) := by
          simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).isCompact
        have hn : (∑ j, t j • (K j : Set E)).Nonempty := by
          simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).nonempty
        rw [exposed_eq_support_level hc hn,
          ← D.height_eq_support (fun j => (K j).isCompact) (fun j => (K j).nonempty) t ht i]
        unfold fixedFace
        rw [hbody, coe_sum_body]
        rfl
    have hbase (i : Fin D.count) : fixedFacetBase D.normal (D.height t) i (v i) (hv i) =
        (↑(∑ j, t j • kernelBody (K j) (D.normal i) (v i) (hv i)) :
          Set (LinearMap.ker (D.normal i).toLinearMap)) := by
      first
      | rw [fixedFacetBase, hface, image_exposed_positive_sum K _ _ _ t ht]
    have hd := first_variation_fixed_heights D.normal (D.height t) hp
      D.positive_ray_injective hS v hv A.isCompact A.convex A.nonempty
    rw [hbody] at hd
    have he := eval_firstVariableCoefficient_eq_of_volume_derivative volume A K t
      (fun j => (ht j).le) hd
    rw [he]
    simp only [facetDerivativePolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_C]
    apply Finset.sum_congr rfl
    intro i hi
    rw [volumePolynomial_eval (kernelMeasure (D.normal i)) _ t (fun j => (ht j).le)]
    rw [fixedFacetWeight, hbase]
    let q : ℝ := (kernelMeasure (D.normal i)).real
      (↑(∑ j, t j • kernelBody (K j) (D.normal i) (v i) (hv i)) :
        Set (LinearMap.ker (D.normal i).toLinearMap))
    change (facetFrameFactor (D.normal i) (v i) (hv i) * q) *
        SupportGeometry.support (A : Set E) (D.normal i) =
      (facetFrameFactor (D.normal i) (v i) (hv i) *
        SupportGeometry.support (A : Set E) (D.normal i)) * q
    ring

/-- The genuine mixed-facet identity. The `(n+1)` factor is the exact factorial
normalization in the definition of mixed volume. -/
theorem mixedVolume_facet_identity {n : ℕ}
    (K : Fin n → ConvexBody E) (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1) (A : ConvexBody E) :
    ((n + 1 : ℕ) : ℝ) * mixedVolume volume (Fin.cons A K) =
      ∑ i, facetFrameFactor (D.normal i) (v i) (hv i) *
        SupportGeometry.support (A : Set E) (D.normal i) *
        mixedVolume (kernelMeasure (D.normal i))
          (fun j => kernelBody (K j) (D.normal i) (v i) (hv i)) := by
  first
  | classical
    have hc := congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff (squarefreeExponent n))
      (firstVariableCoefficient_eq_facetPolynomial K D h0 hint v hv A)
    simp only [firstVariableCoefficient_squarefree, facetDerivativePolynomial,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] at hc
    have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    calc
      ((n + 1 : ℕ) : ℝ) * mixedVolume volume (Fin.cons A K) =
          (volumePolynomial volume (Fin.cons A K)).coeff (squarefreeExponent (n + 1)) /
            (n.factorial : ℝ) := by
        first
        | rw [mixedVolume, Nat.factorial_succ, Nat.cast_mul]
          field_simp [hn, hn1]
      _ = (∑ i, facetFrameFactor (D.normal i) (v i) (hv i) *
          SupportGeometry.support (A : Set E) (D.normal i) *
          (volumePolynomial (kernelMeasure (D.normal i))
            (fun j => kernelBody (K j) (D.normal i) (v i) (hv i))).coeff
              (squarefreeExponent n)) / (n.factorial : ℝ) := congrArg (fun x => x / _) hc
      _ = _ := by
        first
        | rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          unfold mixedVolume
          ring

/-- Monotonicity in the first argument, for a finite background facet family.
Nonnegativity is coefficientwise on the lower-dimensional volume polynomials. -/
theorem mixedVolume_mono_first_of_fixedFacets {n : ℕ}
    (K : Fin n → ConvexBody E) (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1)
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume volume (Fin.cons A K) ≤ mixedVolume volume (Fin.cons B K) := by
  first
  | apply Iff.mp (mul_le_mul_iff_right₀ (by positivity : 0 < ((n + 1 : ℕ) : ℝ)))
    rw [mixedVolume_facet_identity K D h0 hint v hv A,
      mixedVolume_facet_identity K D h0 hint v hv B]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_left _ (facetFrameFactor_nonneg _ _ _)
      exact SupportGeometry.support_le A.nonempty (D.normal i)
        (fun x hx => SupportGeometry.le_support B.isCompact (D.normal i) (hAB hx))
    · exact mixedVolume_nonnegative (kernelMeasure (D.normal i)) _

theorem mixedVolume_mono_first_of_finite_polytopes {n : ℕ}
    (K : Fin n → ConvexBody E) (hK : ∀ j, IsFiniteHull (K j : Set E))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume volume (Fin.cons A K) ≤ mixedVolume volume (Fin.cons B K) := by
  first
  | classical
    obtain ⟨D⟩ := exists_fixedFacets (fun j => (K j : Set E)) hK
      (fun j => (K j).nonempty) ⟨0, hint⟩
    choose v hv using fun i => LinearFrame.exists_unit_value (D.normal i) (D.normal_ne_zero i)
    exact mixedVolume_mono_first_of_fixedFacets K D h0 hint v hv A B hAB

end VolumePolynomials.PolytopeGeometry
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedFacetIdentity.lean -/
