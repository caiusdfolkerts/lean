module

public import volume_polynomials.assembly_part02

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

/- BEGIN SOURCE: VolumePolynomials/PlanarEdgeMeasure.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The finite edge measure of an actual planar polytope

The edge vectors are extracted from the genuine facet first-variation formula.
Their defining identity concerns mixed areas of all actual test bodies. The
construction theorem proves that identity for every positive-area finite hull;
it is not an additional hypothesis on the paper's bodies.
-/

noncomputable section
open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PolytopeGeometry OAI.Paper092

def normal (e : Plane) : Plane →L[ℝ] ℝ :=
  e.2 • ContinuousLinearMap.fst ℝ ℝ ℝ - e.1 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem normal_apply (e x : Plane) : normal e x = e.2 * x.1 - e.1 * x.2 := rfl

def edgeOfFunctional (l : Plane →L[ℝ] ℝ) : Plane := (-l (0, 1), l (1, 0))

theorem functional_coordinates (l : Plane →L[ℝ] ℝ) (x : Plane) :
    l x = x.1 * l (1, 0) + x.2 * l (0, 1) := by
  first
  | have hx : x = x.1 • ((1, 0) : Plane) + x.2 • ((0, 1) : Plane) := by
      first
      | ext <;> simp
    conv_lhs => rw [hx]
    simp only [map_add, map_smul, smul_eq_mul]

@[simp] theorem normal_edgeOfFunctional (l : Plane →L[ℝ] ℝ) :
    normal (edgeOfFunctional l) = l := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    rw [normal_apply]
    dsimp only [edgeOfFunctional]
    rw [functional_coordinates l x]
    ring

theorem support_smul_functional (A : Set Plane) (l : Plane →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    SupportGeometry.support A (r • l) = r * SupportGeometry.support A l := by
  first
  | unfold SupportGeometry.support
    have he : (r • l) '' A = r • (l '' A) := by
      first
      | ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨l x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
    rw [he, Real.sSup_smul_of_nonneg hr]
    rfl

/-- Literal first-variation representation of mixed area by finitely many
oriented vectors. Zero vectors and repeated directions are allowed. -/
def Represents {ι : Type*} [Fintype ι] (P : ConvexBody Plane) (e : ι → Plane) : Prop :=
  ∀ A : ConvexBody Plane,
    2 * mixedArea volume A P = ∑ i, SupportGeometry.support (A : Set Plane) (normal (e i))

theorem exists_representation_centered (P : ConvexBody Plane)
    (hP : IsFiniteHull (P : Set Plane)) (hint : (0 : Plane) ∈ interior (P : Set Plane)) :
    ∃ n : ℕ, ∃ e : Fin n → Plane, Represents P e := by
  first
  | classical
    let K : Fin 1 → ConvexBody Plane := fun _ => P
    have h0 : ∀ j, (0 : Plane) ∈ K j := fun _ => interior_subset hint
    have hsum : (∑ j, (K j : Set Plane)) = (P : Set Plane) := by simp [K]
    have hfull : (interior (∑ j, (K j : Set Plane))).Nonempty := by
      first
      | rw [hsum]
        exact ⟨0, hint⟩
    obtain ⟨D⟩ := exists_fixedFacets (fun j => (K j : Set Plane)) (fun _ => hP)
      (fun _ => P.nonempty) hfull
    choose v hv using fun i => LinearFrame.exists_unit_value (D.normal i) (D.normal_ne_zero i)
    let w : Fin D.count → ℝ := fun i => facetFrameFactor (D.normal i) (v i) (hv i) *
      mixedVolume (kernelMeasure (D.normal i))
        (fun j => kernelBody (K j) (D.normal i) (v i) (hv i))
    have hw (i) : 0 ≤ w i := mul_nonneg (facetFrameFactor_nonneg _ _ _)
      (mixedVolume_nonnegative _ _)
    refine ⟨D.count, fun i => edgeOfFunctional (w i • D.normal i), ?_⟩
    intro A
    have he : Fin.cons A K = ![A, P] := by
      first
      | funext i
        fin_cases i <;> rfl
    have h := mixedVolume_facet_identity K D h0 (by rwa [hsum]) v hv A
    norm_num only [Nat.cast_add, Nat.cast_one, he] at h
    change 2 * mixedArea volume A P = _ at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [normal_edgeOfFunctional, support_smul_functional _ _ (hw i)]
    dsimp only [w]
    ring

theorem Represents.translate {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) (v : Plane) : Represents (translateBody v P) e := by
  first
  | intro A
    rw [mixedArea_translate_right]
    exact h A

theorem exists_representation_of_interior (P : ConvexBody Plane)
    (hP : IsFiniteHull (P : Set Plane)) (hint : (interior (P : Set Plane)).Nonempty) :
    ∃ n : ℕ, ∃ e : Fin n → Plane, Represents P e := by
  first
  | classical
    obtain ⟨p, hp⟩ := hint
    let Q := translateBody (-p) P
    have hQ : IsFiniteHull (Q : Set Plane) := isFiniteHull_translateBody hP (-p)
    have hQint : (0 : Plane) ∈ interior (Q : Set Plane) := by
      first
      | dsimp only [Q]
        rw [coe_translateBody, interior_vadd]
        exact ⟨p, hp, neg_add_cancel p⟩
    obtain ⟨n, e, he⟩ := exists_representation_centered Q hQ hQint
    refine ⟨n, e, ?_⟩
    have h := he.translate p
    simpa only [Q, translateBody_translate, add_neg_cancel, translateBody_zero] using h

/-- Every polygon needed in the positive-area coefficient slice has a proved
finite edge representation. -/
theorem exists_representation (P : ConvexBody Plane)
    (hP : IsFiniteHull (P : Set Plane)) (harea : 0 < volume.real (P : Set Plane)) :
    ∃ n : ℕ, ∃ e : Fin n → Plane, Represents P e := by
  first
  | have hpos : 0 < volume (P : Set Plane) := (ENNReal.toReal_pos_iff.mp harea).1
    have hint : (interior (P : Set Plane)).Nonempty := by
      first
      | have hne : volume (interior (P : Set Plane)) ≠ 0 := by
          rw [measure_interior_of_null_frontier (P.convex.addHaar_frontier volume)]
          exact hpos.ne'
        apply Set.nonempty_iff_ne_empty.mpr
        intro hempty
        apply hne
        rw [hempty, measure_empty]
    exact exists_representation_of_interior P hP hint

theorem support_pointBody (v : Plane) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (pointBody v : Set Plane) l = l v := by
  first
  | simp only [SupportGeometry.support, coe_pointBody, Set.image_singleton, csSup_singleton]

theorem Represents.balance {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) :
    (∑ i, (e i).1) = 0 ∧ (∑ i, (e i).2) = 0 := by
  first
  | have hx := h (pointBody (0, 1))
    have hy := h (pointBody (1, 0))
    simp only [mixedArea_point_left, mul_zero, support_pointBody, normal_apply,
      mul_zero, mul_one, zero_sub, sub_zero, Finset.sum_neg_distrib] at hx hy
    constructor <;> linarith

theorem support_segmentBody (v : Plane) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (PlanarCorner.segmentBody v : Set Plane) l = |l v| / 2 := by
  first
  | apply le_antisymm
    · apply SupportGeometry.support_le (PlanarCorner.segmentBody v).nonempty l
      rintro x ⟨t, ht, rfl⟩
      have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
      have hmul := mul_le_mul_of_nonneg_right ht' (abs_nonneg (l v))
      have hle : t * l v ≤ |t| * |l v| := by simpa only [abs_mul] using le_abs_self (t * l v)
      simp only [map_smul, smul_eq_mul]
      nlinarith
    · by_cases hv : 0 ≤ l v
      · have hp : (1 / 2 : ℝ) • v ∈ PlanarCorner.segmentBody v :=
          ⟨1 / 2, ⟨by norm_num, le_rfl⟩, rfl⟩
        have h := SupportGeometry.le_support (PlanarCorner.segmentBody v).isCompact l hp
        simpa only [map_smul, smul_eq_mul, abs_of_nonneg hv, div_eq_mul_inv,
          one_mul, mul_comm] using h
      · have hp : (-(1 / 2) : ℝ) • v ∈ PlanarCorner.segmentBody v :=
          ⟨-(1 / 2), ⟨le_rfl, by norm_num⟩, rfl⟩
        have h := SupportGeometry.le_support (PlanarCorner.segmentBody v).isCompact l hp
        simp only [map_smul, smul_eq_mul] at h
        rw [abs_of_neg (lt_of_not_ge hv)]
        nlinarith

theorem support_unitX (e : Plane) :
    SupportGeometry.support (unitX : Set Plane) (normal e) = |e.2| / 2 := by
  first
  | simpa only [unitX, normal_apply, mul_one, mul_zero, sub_zero] using
      support_segmentBody (1, 0) (normal e)

theorem support_unitY (e : Plane) :
    SupportGeometry.support (unitY : Set Plane) (normal e) = |e.1| / 2 := by
  first
  | simpa only [unitY, normal_apply, mul_one, mul_zero, zero_sub, abs_neg] using
      support_segmentBody (0, 1) (normal e)

theorem Represents.total_variation {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) :
    (∑ i, |(e i).1|) = 2 * width P ∧ (∑ i, |(e i).2|) = 2 * height P := by
  first
  | have hx := h unitY
    have hy := h unitX
    rw [mixedArea_symm, twice_mixedArea_unitY] at hx
    rw [mixedArea_symm, twice_mixedArea_unitX] at hy
    simp only [support_unitY, support_unitX, ← Finset.sum_div] at hx hy
    constructor <;> linarith

theorem twice_positive_part (x : ℝ) : 2 * max x 0 = |x| + x := by
  first
  | rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · rw [max_eq_right hx, abs_of_nonpos hx]
      ring

theorem Represents.signed_variation {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) :
    (∑ i, max (e i).1 0) = width P ∧ (∑ i, max (e i).2 0) = height P ∧
    (∑ i, max (-(e i).1) 0) = width P ∧ (∑ i, max (-(e i).2) 0) = height P := by
  first
  | have hbal := h.balance
    have hvar := h.total_variation
    have hp (f : ι → ℝ) : 2 * (∑ i, max (f i) 0) = (∑ i, |f i|) + ∑ i, f i := by
      first
      | rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => twice_positive_part (f i))
    have hxp := hp (fun i => (e i).1)
    have hyp := hp (fun i => (e i).2)
    have hxn := hp (fun i => -(e i).1)
    have hyn := hp (fun i => -(e i).2)
    simp only [abs_neg, Finset.sum_neg_distrib] at hxn hyn
    constructor
    · linarith [hbal.1, hvar.1]
    constructor
    · linarith [hbal.2, hvar.2]
    constructor
    · linarith [hbal.1, hvar.1]
    · linarith [hbal.2, hvar.2]

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarEdgeMeasure.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarFacetFormula.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # First variation as a literal planar mixed-area formula -/

noncomputable section
open Set Filter MeasureTheory Module
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials.PlanarMixedForm

open PlanarExtrusion OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem area_add_smul (hdim : finrank ℝ E = 2) (P A : ConvexBody E)
    {r : ℝ} (hr : 0 ≤ r) :
    μ.real (P + r • A : ConvexBody E) = μ.real (P : Set E) +
      r * (2 * mixedArea μ A P) + r ^ 2 * μ.real (A : Set E) := by
  first
  | rw [area_add μ hdim, mixedArea_smul_right μ _ _ hr,
      haar_real_smul_body μ A hr, hdim, mixedArea_symm μ P A]
    ring

theorem hasDerivWithinAt_area_add_smul (hdim : finrank ℝ E = 2)
    (P A : ConvexBody E) :
    HasDerivWithinAt (fun t : ℝ => μ.real (P + t • A : ConvexBody E))
      (2 * mixedArea μ A P) (Ioi 0) 0 := by
  first
  | have hp : HasDerivAt (fun t : ℝ => μ.real (P : Set E) +
        t * (2 * mixedArea μ A P) + t ^ 2 * μ.real (A : Set E))
        (2 * mixedArea μ A P) 0 := by
      convert ((hasDerivAt_const (0 : ℝ) (μ.real (P : Set E))).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (2 * mixedArea μ A P))).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (μ.real (A : Set E))) using 1 <;> norm_num
      all_goals rfl
    exact hp.hasDerivWithinAt.congr
      (fun t ht => area_add_smul μ hdim P A ht.le) (area_add_smul μ hdim P A le_rfl)

end VolumePolynomials.PlanarMixedForm

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm OAI.Paper092 PolytopeFirstVariation

theorem mixedArea_facet_formula {ι : Type*} [Fintype ι]
    (P : ConvexBody Plane) (l : ι → Plane →L[ℝ] ℝ)
    (hl : Function.Injective l) (hbody : HalfspacePyramids.body l = (P : Set Plane))
    (v : ι → Plane) (hv : ∀ i, l i (v i) = 1) (A : ConvexBody Plane) :
    2 * mixedArea volume A P =
      ∑ i, canonicalFacetWeight l i (v i) (hv i) *
        SupportGeometry.support (A : Set Plane) (l i) := by
  first
  | have hcompact : IsCompact (HalfspacePyramids.body l) := by rw [hbody]; exact P.isCompact
    have hd := first_variation l hl hcompact v hv A.isCompact A.convex A.nonempty
    rw [hbody] at hd
    have hp := hasDerivWithinAt_area_add_smul volume PlanarCorner.plane_finrank P A
    have h₁ := (hasDerivWithinAt_iff_tendsto_slope'
      (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hp
    have h₂ := (hasDerivWithinAt_iff_tendsto_slope'
      (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hd
    exact tendsto_nhds_unique h₁ h₂

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarFacetFormula.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarCornerOptimizer.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The actual optimizer in equation (4.15)

The body is a Minkowski sum of the specified planar body and two coordinate
segments. Its projection widths, Lebesgue area and mixed area are computed
exactly. No corner-measure representation is assumed.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.PlanarCorner

open PlanarExtrusion PlanarMixedForm

theorem unit_width_lower_bound (A Q : ConvexBody Plane) {s a q : ℝ}
    (hAw : width A = 1) (hAh : height A = s) (hAa : volume.real (A : Set Plane) = a)
    (hQw : width Q = 1) (hQh : height Q = 1) (hQa : volume.real (Q : Set Plane) = q) :
    2 * mixedArea volume A Q ≥ 1 + s - 2 * Real.sqrt ((s - a) * (1 - q)) := by
  first
  | simpa only [hAw, hAh, hAa, hQw, hQh, hQa, one_mul, mul_one] using
      mixedArea_corner_inequality A Q

theorem width_add (A B : ConvexBody Plane) : width (A + B) = width A + width B := by
  first
  | have h := twice_mixedArea_unitY (A + B)
    rw [mixedArea_add_left] at h
    linarith [twice_mixedArea_unitY A, twice_mixedArea_unitY B]

theorem height_add (A B : ConvexBody Plane) : height (A + B) = height A + height B := by
  first
  | have h := twice_mixedArea_unitX (A + B)
    rw [mixedArea_add_left] at h
    linarith [twice_mixedArea_unitX A, twice_mixedArea_unitX B]

theorem width_smul (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    width (r • A) = r * width A := by
  first
  | have h := twice_mixedArea_unitY (r • A)
    rw [mixedArea_smul_left volume _ _ hr] at h
    nlinarith [twice_mixedArea_unitY A]

theorem height_smul (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    height (r • A) = r * height A := by
  first
  | have h := twice_mixedArea_unitX (r • A)
    rw [mixedArea_smul_left volume _ _ hr] at h
    nlinarith [twice_mixedArea_unitX A]

theorem width_translate (P : ConvexBody Plane) (v : Plane) :
    width (translateBody v P) = width P := by
  first
  | have h := mixedArea_translate_right volume unitY P v
    rw [mixedArea_symm volume unitY, mixedArea_symm volume unitY] at h
    linarith [twice_mixedArea_unitY (translateBody v P), twice_mixedArea_unitY P]

theorem height_translate (P : ConvexBody Plane) (v : Plane) :
    height (translateBody v P) = height P := by
  first
  | have h := mixedArea_translate_right volume unitX P v
    rw [mixedArea_symm volume unitX, mixedArea_symm volume unitX] at h
    linarith [twice_mixedArea_unitX (translateBody v P), twice_mixedArea_unitX P]

@[simp] theorem width_unitX : width unitX = 1 := by
  first
  | rw [← twice_mixedArea_unitY, twice_mixedArea_axes]

@[simp] theorem height_unitY : height unitY = 1 := by
  first
  | rw [← twice_mixedArea_unitX, mixedArea_symm, twice_mixedArea_axes]

@[simp] theorem width_unitY : width unitY = 0 := by
  first
  | rw [← twice_mixedArea_unitY, mixedArea_diagonal volume plane_finrank,
      unitY, area_segmentBody, mul_zero]

@[simp] theorem height_unitX : height unitX = 0 := by
  first
  | rw [← twice_mixedArea_unitX, mixedArea_diagonal volume plane_finrank,
      unitX, area_segmentBody, mul_zero]

theorem area_smul (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real ((r • A : ConvexBody Plane) : Set Plane) = r ^ 2 * volume.real (A : Set Plane) := by
  first
  | simpa only [plane_finrank] using haar_real_smul_body volume A hr

theorem area_add_scaled_unitX (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real ((A + r • unitX : ConvexBody Plane) : Set Plane) =
      volume.real (A : Set Plane) + r * height A := by
  first
  | rw [area_add volume plane_finrank, mixedArea_smul_right volume _ _ hr,
      area_smul _ hr, unitX, area_segmentBody, mul_zero, add_zero]
    have h := twice_mixedArea_unitX A
    change 2 * mixedArea volume A (segmentBody (1, 0)) = height A at h
    nlinarith

theorem area_add_scaled_unitY (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real ((A + r • unitY : ConvexBody Plane) : Set Plane) =
      volume.real (A : Set Plane) + r * width A := by
  first
  | rw [area_add volume plane_finrank, mixedArea_smul_right volume _ _ hr,
      area_smul _ hr, unitY, area_segmentBody, mul_zero, add_zero]
    have h := twice_mixedArea_unitY A
    change 2 * mixedArea volume A (segmentBody (0, 1)) = width A at h
    nlinarith

def optimizerBody (Q : ConvexBody Plane) (s lam : ℝ) : ConvexBody Plane :=
  lam • Q + (1 - lam) • unitX + (s - lam) • unitY

theorem segmentBody_finiteHull (v : Plane) :
    PolytopeGeometry.IsFiniteHull (segmentBody v : Set Plane) := by
  first
  | have hI : PolytopeGeometry.IsFiniteHull (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
      first
      | refine ⟨{-(1 / 2 : ℝ), 1 / 2}, (Set.finite_singleton _).insert _, ?_⟩
        rw [convexHull_pair, segment_eq_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
    exact hI.linear_image (LinearMap.toSpanSingleton ℝ Plane v)

theorem optimizerBody_finiteHull (Q : ConvexBody Plane) (s lam : ℝ)
    (hQ : PolytopeGeometry.IsFiniteHull (Q : Set Plane)) :
    PolytopeGeometry.IsFiniteHull (optimizerBody Q s lam : Set Plane) :=
  ((hQ.smul lam).add ((segmentBody_finiteHull (1, 0)).smul (1 - lam))).add
    ((segmentBody_finiteHull (0, 1)).smul (s - lam))

theorem optimizerBody_widths (Q : ConvexBody Plane) {s lam : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlams : lam ≤ s) :
    width (optimizerBody Q s lam) = 1 ∧ height (optimizerBody Q s lam) = s := by
  first
  | have ha : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    have hb : 0 ≤ s - lam := sub_nonneg.mpr hlams
    simp only [optimizerBody, width_add, height_add, width_smul _ hlam,
      width_smul _ ha, width_smul _ hb, height_smul _ hlam, height_smul _ ha,
      height_smul _ hb, width_unitX, width_unitY, height_unitX, height_unitY, hQw, hQh]
    constructor <;> ring

theorem optimizerBody_area (Q : ConvexBody Plane) {s lam : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlams : lam ≤ s) :
    volume.real (optimizerBody Q s lam : Set Plane) =
      s - lam ^ 2 * (1 - volume.real (Q : Set Plane)) := by
  first
  | have ha : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    have hb : 0 ≤ s - lam := sub_nonneg.mpr hlams
    rw [optimizerBody, area_add_scaled_unitY _ hb, area_add_scaled_unitX _ ha,
      area_smul _ hlam, height_smul _ hlam, width_add,
      width_smul _ hlam, width_smul _ ha, width_unitX, hQw, hQh]
    ring

theorem optimizerBody_mixedArea (Q : ConvexBody Plane) {s lam : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlams : lam ≤ s) :
    2 * mixedArea volume (optimizerBody Q s lam) Q =
      1 + s - 2 * lam * (1 - volume.real (Q : Set Plane)) := by
  first
  | have ha : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    have hb : 0 ≤ s - lam := sub_nonneg.mpr hlams
    have hx : 2 * mixedArea volume unitX Q = 1 := by
      first
      | rw [mixedArea_symm, twice_mixedArea_unitX, hQh]
    have hy : 2 * mixedArea volume unitY Q = 1 := by
      first
      | rw [mixedArea_symm, twice_mixedArea_unitY, hQw]
    rw [optimizerBody, mixedArea_add_left, mixedArea_add_left,
      mixedArea_smul_left volume _ _ hlam, mixedArea_smul_left volume _ _ ha,
      mixedArea_smul_left volume _ _ hb, mixedArea_diagonal volume plane_finrank]
    nlinarith

/-- The geometric content of Lemma4.4 after the interaction body is known:
its lower bound holds for every actual A, and the stated body attains it whenever
the square-root scale fits both requested widths. -/
theorem optimizer_attains (Q : ConvexBody Plane) {s a : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hq : volume.real (Q : Set Plane) < 1) (ha : a ≤ s)
    (hfit : Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane))) ≤ min 1 s) :
    ∃ A : ConvexBody Plane, width A = 1 ∧ height A = s ∧
      volume.real (A : Set Plane) = a ∧
      2 * mixedArea volume A Q =
        1 + s - 2 * Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) := by
  first
  | let lam := Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane)))
    have hlam : 0 ≤ lam := Real.sqrt_nonneg _
    have hlam1 : lam ≤ 1 := hfit.trans (min_le_left _ _)
    have hlams : lam ≤ s := hfit.trans (min_le_right _ _)
    have hden : 0 < 1 - volume.real (Q : Set Plane) := sub_pos.mpr hq
    have hsq : lam ^ 2 = (s - a) / (1 - volume.real (Q : Set Plane)) :=
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ha) hden.le)
    have hprod : lam ^ 2 * (1 - volume.real (Q : Set Plane)) = s - a := by
      first
      | rw [hsq, div_mul_cancel₀ _ hden.ne']
    have hroot : lam * (1 - volume.real (Q : Set Plane)) =
        Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) := by
      first
      | have hnonneg : 0 ≤ lam * (1 - volume.real (Q : Set Plane)) := mul_nonneg hlam hden.le
        have hpower : (lam * (1 - volume.real (Q : Set Plane))) ^ 2 =
            (s - a) * (1 - volume.real (Q : Set Plane)) := by
          nlinarith [congrArg (fun z : ℝ => z * (1 - volume.real (Q : Set Plane))) hprod]
        rw [← hpower, Real.sqrt_sq hnonneg]
    obtain ⟨hw, hh⟩ := optimizerBody_widths Q hQw hQh hlam hlam1 hlams
    refine ⟨optimizerBody Q s lam, hw, hh, ?_, ?_⟩
    · rw [optimizerBody_area Q hQw hQh hlam hlam1 hlams, hprod]
      ring
    · rw [optimizerBody_mixedArea Q hQw hQh hlam hlam1 hlams]
      nlinarith [hroot]

theorem optimizer_attains_finiteHull (Q : ConvexBody Plane) {s a : ℝ}
    (hQpoly : PolytopeGeometry.IsFiniteHull (Q : Set Plane))
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hq : volume.real (Q : Set Plane) < 1) (ha : a ≤ s)
    (hfit : Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane))) ≤ min 1 s) :
    ∃ A : ConvexBody Plane, width A = 1 ∧ height A = s ∧
      volume.real (A : Set Plane) = a ∧
      2 * mixedArea volume A Q =
        1 + s - 2 * Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) ∧
      PolytopeGeometry.IsFiniteHull (A : Set Plane) := by
  first
  | let lam := Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane)))
    have hlam : 0 ≤ lam := Real.sqrt_nonneg _
    have hlam1 : lam ≤ 1 := hfit.trans (min_le_left _ _)
    have hlams : lam ≤ s := hfit.trans (min_le_right _ _)
    have hden : 0 < 1 - volume.real (Q : Set Plane) := sub_pos.mpr hq
    have hsq : lam ^ 2 = (s - a) / (1 - volume.real (Q : Set Plane)) :=
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ha) hden.le)
    have hprod : lam ^ 2 * (1 - volume.real (Q : Set Plane)) = s - a := by
      first
      | rw [hsq, div_mul_cancel₀ _ hden.ne']
    have hroot : lam * (1 - volume.real (Q : Set Plane)) =
        Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) := by
      first
      | have hn : 0 ≤ lam * (1 - volume.real (Q : Set Plane)) := mul_nonneg hlam hden.le
        have hp : (lam * (1 - volume.real (Q : Set Plane))) ^ 2 =
            (s - a) * (1 - volume.real (Q : Set Plane)) := by
          nlinarith [congrArg (fun z : ℝ => z * (1 - volume.real (Q : Set Plane))) hprod]
        rw [← hp, Real.sqrt_sq hn]
    obtain ⟨hw, hh⟩ := optimizerBody_widths Q hQw hQh hlam hlam1 hlams
    refine ⟨optimizerBody Q s lam, hw, hh, ?_, ?_, optimizerBody_finiteHull Q s lam hQpoly⟩
    · rw [optimizerBody_area Q hQw hQh hlam hlam1 hlams, hprod]
      ring
    · rw [optimizerBody_mixedArea Q hQw hQh hlam hlam1 hlams]
      nlinarith [hroot]

end VolumePolynomials.PlanarCorner
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarCornerOptimizer.lean -/

/- BEGIN SOURCE: VolumePolynomials/RightTriangleFormula.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The exact three-term mixed-area formula for a right triangle

The three facet weights are determined from actual first variation, translation
balance and coordinate extrusion. No unproved triangle-area or surface-area
formula is used.
-/

noncomputable section
open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PolytopeGeometry OAI.Paper092
open PolytopeFirstVariation

def unitTriangle : ConvexBody Plane where
  carrier := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1}
  convex' := by
    first
    | intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
        add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), ?_⟩
      nlinarith [mul_le_mul_of_nonneg_left hx.2.2 ha,
        mul_le_mul_of_nonneg_left hy.2.2 hb]
  isCompact' := by
    first
    | have hc : IsClosed {x : Plane | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1} :=
        (isClosed_le continuous_const continuous_fst).inter
          ((isClosed_le continuous_const continuous_snd).inter
            (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
      refine (isCompact_Icc : IsCompact (Icc ((0, 0) : Plane) (1, 1))).of_isClosed_subset hc ?_
      intro x hx
      exact ⟨⟨hx.1, hx.2.1⟩, ⟨by linarith [hx.2.2, hx.2.1], by linarith [hx.2.2, hx.1]⟩⟩
  nonempty' := ⟨(0, 0), by norm_num⟩

@[simp] theorem mem_unitTriangle (x : Plane) :
    x ∈ unitTriangle ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1 := Iff.rfl

theorem unitTriangle_projections :
    Prod.fst '' (unitTriangle : Set Plane) = Icc (0 : ℝ) 1 ∧
      Prod.snd '' (unitTriangle : Set Plane) = Icc (0 : ℝ) 1 := by
  first
  | constructor
    · ext t
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.1, by linarith [hx.2.1, hx.2.2]⟩
      · intro ht
        exact ⟨(t, 0), ⟨ht.1, le_rfl, by simpa using ht.2⟩, rfl⟩
    · ext t
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.2.1, by linarith [hx.1, hx.2.2]⟩
      · intro ht
        exact ⟨(0, t), ⟨le_rfl, ht.1, by simpa using ht.2⟩, rfl⟩

@[simp] theorem width_unitTriangle : width unitTriangle = 1 := by
  first
  | rw [width, unitTriangle_projections.1]
    norm_num

@[simp] theorem height_unitTriangle : height unitTriangle = 1 := by
  first
  | rw [height, unitTriangle_projections.2]
    norm_num

def triangleVertices : Fin 3 → Plane := ![(0, 0), (1, 0), (0, 1)]

theorem unitTriangle_eq_convexHull :
    (unitTriangle : Set Plane) = convexHull ℝ (Set.range triangleVertices) := by
  first
  | apply subset_antisymm
    · intro x hx
      apply mem_convexHull_of_exists_fintype
        (![1 - x.1 - x.2, x.1, x.2] : Fin 3 → ℝ) triangleVertices
      · intro i
        fin_cases i
        · change 0 ≤ 1 - x.1 - x.2
          linarith [hx.2.2]
        · change 0 ≤ x.1
          exact hx.1
        · change 0 ≤ x.2
          exact hx.2.1
      · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Fin.sum_univ_zero, add_zero]
        ring
      · exact fun i => Set.mem_range_self i
      · ext <;> simp [triangleVertices, Fin.sum_univ_succ]
    · apply convexHull_min
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> norm_num [triangleVertices, mem_unitTriangle]
      · exact unitTriangle.convex

theorem unitTriangle_finiteHull : IsFiniteHull (unitTriangle : Set Plane) :=
  ⟨Set.range triangleVertices, Set.finite_range _, unitTriangle_eq_convexHull⟩

def centeredTriangle : ConvexBody Plane := translateBody (-(1 / 3), -(1 / 3)) unitTriangle

def triangleNormals : Fin 3 → Plane →L[ℝ] ℝ :=
  ![normal (0, -3), normal (3, 0), normal (-3, 3)]

def triangleRightInverse : Fin 3 → Plane :=
  ![(-(1 / 3), 0), (0, -(1 / 3)), (1 / 3, 0)]

theorem triangle_normal_unit (i : Fin 3) : triangleNormals i (triangleRightInverse i) = 1 := by
  first
  | fin_cases i <;> norm_num [triangleNormals, triangleRightInverse, normal_apply]

theorem triangleNormals_injective : Function.Injective triangleNormals := by
  first
  | intro i j hij
    have hx := congrArg (fun l : Plane →L[ℝ] ℝ => l (1, 0)) hij
    fin_cases i
    all_goals fin_cases j
    all_goals first | rfl | norm_num [triangleNormals, normal_apply] at hx

theorem triangle_halfspace_body :
    HalfspacePyramids.body triangleNormals = (centeredTriangle : Set Plane) := by
  first
  | ext x
    change (∀ i, triangleNormals i x ≤ 1) ↔ x ∈ centeredTriangle
    rw [centeredTriangle, mem_translateBody]
    change (∀ i, triangleNormals i x ≤ 1) ↔
      0 ≤ x.1 - (-(1 / 3)) ∧ 0 ≤ x.2 - (-(1 / 3)) ∧
        (x.1 - (-(1 / 3))) + (x.2 - (-(1 / 3))) ≤ 1
    constructor
    · intro hx
      have h0 := hx 0
      have h1 := hx 1
      have h2 := hx 2
      norm_num [triangleNormals, normal_apply] at h0 h1 h2
      exact ⟨by linarith, by linarith, by linarith⟩
    · intro hx i
      fin_cases i <;> norm_num [triangleNormals, normal_apply] <;>
        linarith [hx.1, hx.2.1, hx.2.2]

def triangleWeight (i : Fin 3) : ℝ :=
  canonicalFacetWeight triangleNormals i (triangleRightInverse i) (triangle_normal_unit i)

theorem triangle_facet_formula (A : ConvexBody Plane) :
    2 * mixedArea volume A centeredTriangle =
      ∑ i, triangleWeight i * SupportGeometry.support (A : Set Plane) (triangleNormals i) :=
  mixedArea_facet_formula centeredTriangle triangleNormals triangleNormals_injective
    triangle_halfspace_body triangleRightInverse triangle_normal_unit A

theorem triangleWeight_value (i : Fin 3) : triangleWeight i = 1 / 3 := by
  first
  | have hx := triangle_facet_formula (pointBody (1, 0))
    have hy := triangle_facet_formula (pointBody (0, 1))
    simp only [mixedArea_point_left, mul_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
      support_pointBody, triangleNormals, Matrix.cons_val_zero, Matrix.cons_val_succ,
      normal_apply, mul_one, mul_zero, zero_sub, sub_zero, add_zero] at hx hy
    have hs := triangle_facet_formula unitX
    rw [mixedArea_symm, twice_mixedArea_unitX, centeredTriangle,
      height_translate, height_unitTriangle] at hs
    norm_num [Fin.sum_univ_succ, triangleNormals, support_unitX] at hs
    norm_num at hx hy
    fin_cases i <;> norm_num <;> linarith

theorem support_third_normal (A : ConvexBody Plane) (e : Plane) :
    (1 / 3 : ℝ) * SupportGeometry.support (A : Set Plane) (normal ((3 : ℝ) • e)) =
      SupportGeometry.support (A : Set Plane) (normal e) := by
  first
  | rw [← support_smul_functional _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    congr 1
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.smul_apply, normal_apply, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring

/-- Exact mixed-area functional of the actual unit right triangle. -/
theorem unitTriangle_mixedArea (A : ConvexBody Plane) :
    2 * mixedArea volume A unitTriangle =
      SupportGeometry.support (A : Set Plane) (normal (0, -1)) +
      SupportGeometry.support (A : Set Plane) (normal (1, 0)) +
      SupportGeometry.support (A : Set Plane) (normal (-1, 1)) := by
  first
  | have h := triangle_facet_formula A
    rw [centeredTriangle, mixedArea_translate_right] at h
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, triangleWeight_value,
      triangleNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero] at h
    have h0 := support_third_normal A (0, -1)
    have h1 := support_third_normal A (1, 0)
    have h2 := support_third_normal A (-1, 1)
    have he0 : (3 : ℝ) • ((0, -1) : Plane) = (0, -3) := by ext <;> norm_num
    have he1 : (3 : ℝ) • ((1, 0) : Plane) = (3, 0) := by ext <;> norm_num
    have he2 : (3 : ℝ) • ((-1, 1) : Plane) = (-3, 3) := by ext <;> norm_num
    rw [he0] at h0
    rw [he1] at h1
    rw [he2] at h2
    linarith

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RightTriangleFormula.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarLinearMixedArea.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Linear changes of planar mixed area and right triangles -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem area_mapBody (L : Plane →L[ℝ] Plane) (P : ConvexBody Plane) :
    volume.real (mapBody L P : Set Plane) =
      |LinearMap.det L.toLinearMap| * volume.real (P : Set Plane) := by
  first
  | have h := congrArg ENNReal.toReal
      (Measure.addHaar_image_linearMap (volume : Measure Plane) L.toLinearMap (P : Set Plane))
    simpa only [coe_mapBody, ContinuousLinearMap.coe_coe, measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h

theorem mixedArea_mapBody (L : Plane →L[ℝ] Plane) (P Q : ConvexBody Plane) :
    mixedArea volume (mapBody L P) (mapBody L Q) =
      |LinearMap.det L.toLinearMap| * mixedArea volume P Q := by
  first
  | have h := area_add volume plane_finrank (mapBody L P) (mapBody L Q)
    rw [← mapBody_add, area_mapBody, area_mapBody, area_mapBody,
      area_add volume plane_finrank] at h
    nlinarith

def diagonalLinear (a b : ℝ) : Plane →L[ℝ] Plane :=
  (frameMap (a, 0) (0, b)).toContinuousLinearMap

@[simp] theorem diagonalLinear_apply (a b : ℝ) (x : Plane) :
    diagonalLinear a b x = (a * x.1, b * x.2) := by
  first
  | change x.1 • ((a, 0) : Plane) + x.2 • ((0, b) : Plane) = _
    ext <;> simp [mul_comm]

@[simp] theorem diagonalLinear_det (a b : ℝ) :
    LinearMap.det (diagonalLinear a b).toLinearMap = a * b := by
  first
  | change LinearMap.det (frameMap (a, 0) (0, b)) = _
    rw [frameMap_det]
    simp [determinant]

def diagonalEquiv (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Plane ≃L[ℝ] Plane :=
  ((diagonalLinear a b).toLinearMap.equivOfDetNeZero
    (by rw [diagonalLinear_det]; exact mul_ne_zero ha hb)).toContinuousLinearEquiv

@[simp] theorem diagonalEquiv_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (x : Plane) :
    diagonalEquiv a b ha hb x = (a * x.1, b * x.2) := diagonalLinear_apply a b x

theorem diagonalEquiv_toContinuousLinearMap (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (diagonalEquiv a b ha hb).toContinuousLinearMap = diagonalLinear a b := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    rfl

theorem diagonalEquiv_symm_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (x : Plane) :
    (diagonalEquiv a b ha hb).symm x = (x.1 / a, x.2 / b) := by
  first
  | apply (diagonalEquiv a b ha hb).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, diagonalEquiv_apply]
    ext <;> simp [ha, hb, mul_div_cancel₀, mul_comm]

theorem width_map_diagonal (a b : ℝ) (P : ConvexBody Plane) :
    width (mapBody (diagonalLinear a b) P) = |a| * width P := by
  first
  | have he : Prod.fst '' (mapBody (diagonalLinear a b) P : Set Plane) =
        (fun x : ℝ => a * x) '' (Prod.fst '' (P : Set Plane)) := by
      simp only [coe_mapBody, Set.image_image]
      congr 1
      funext x
      simp only [Function.comp_apply, diagonalLinear_apply]
    rw [width, he, length_image_mul]
    rfl

theorem height_map_diagonal (a b : ℝ) (P : ConvexBody Plane) :
    height (mapBody (diagonalLinear a b) P) = |b| * height P := by
  first
  | have he : Prod.snd '' (mapBody (diagonalLinear a b) P : Set Plane) =
        (fun x : ℝ => b * x) '' (Prod.snd '' (P : Set Plane)) := by
      simp only [coe_mapBody, Set.image_image]
      congr 1
      funext x
      simp only [Function.comp_apply, diagonalLinear_apply]
    rw [height, he, length_image_mul]
    rfl

theorem support_mapBody (L : Plane →L[ℝ] Plane) (P : ConvexBody Plane)
    (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (mapBody L P : Set Plane) l =
      SupportGeometry.support (P : Set Plane) (l.comp L) := by
  first
  | simp only [SupportGeometry.support, coe_mapBody, Set.image_image]
    rfl

theorem support_inverse_diagonal (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (P : ConvexBody Plane) (e : Plane) :
    |a * b| * SupportGeometry.support
        (mapBody (diagonalEquiv a b ha hb).symm.toContinuousLinearMap P : Set Plane) (normal e) =
      SupportGeometry.support (P : Set Plane)
        (normal (|a * b| / b * e.1, |a * b| / a * e.2)) := by
  first
  | rw [support_mapBody, ← support_smul_functional _ _ (abs_nonneg _)]
    congr 1
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, diagonalEquiv_symm_apply, normal_apply, smul_eq_mul]
    field_simp [ha, hb] <;> ring

def rightTriangle (a b : ℝ) : ConvexBody Plane := mapBody (diagonalLinear a b) unitTriangle

@[simp] theorem rightTriangle_width (a b : ℝ) : width (rightTriangle a b) = |a| := by
  first
  | rw [rightTriangle, width_map_diagonal, width_unitTriangle, mul_one]

@[simp] theorem rightTriangle_height (a b : ℝ) : height (rightTriangle a b) = |b| := by
  first
  | rw [rightTriangle, height_map_diagonal, height_unitTriangle, mul_one]

theorem rightTriangle_finiteHull (a b : ℝ) :
    PolytopeGeometry.IsFiniteHull (rightTriangle a b : Set Plane) :=
  unitTriangle_finiteHull.linear_image (diagonalLinear a b).toLinearMap

theorem rightTriangle_support (a b : ℝ) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (rightTriangle a b : Set Plane) l =
      max 0 (max (a * l (1, 0)) (b * l (0, 1))) := by
  first
  | let M := max 0 (max (a * l (1, 0)) (b * l (0, 1)))
    have hM0 : 0 ≤ M := le_max_left _ _
    have hMa : a * l (1, 0) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hMb : b * l (0, 1) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    apply le_antisymm
    · apply SupportGeometry.support_le (rightTriangle a b).nonempty l
      rintro x ⟨y, hy, rfl⟩
      rw [diagonalLinear_apply, functional_coordinates]
      have h1 := mul_le_mul_of_nonneg_left hMa hy.1
      have h2 := mul_le_mul_of_nonneg_left hMb hy.2.1
      have hsum := mul_le_mul_of_nonneg_right hy.2.2 hM0
      change _ ≤ M
      nlinarith
    · apply max_le
      · have hx : (0 : Plane) ∈ rightTriangle a b :=
          ⟨0, ⟨le_rfl, le_rfl, by norm_num⟩, by simp⟩
        simpa only [map_zero] using SupportGeometry.le_support (rightTriangle a b).isCompact l hx
      · apply max_le
        · have hx : ((a, 0) : Plane) ∈ rightTriangle a b :=
            ⟨(1, 0), ⟨zero_le_one, le_rfl, by norm_num⟩, by simp⟩
          have h := SupportGeometry.le_support (rightTriangle a b).isCompact l hx
          simpa only [functional_coordinates l (a, 0), zero_mul, add_zero] using h
        · have hx : ((0, b) : Plane) ∈ rightTriangle a b :=
            ⟨(0, 1), ⟨le_rfl, zero_le_one, by norm_num⟩, by simp⟩
          have h := SupportGeometry.le_support (rightTriangle a b).isCompact l hx
          simpa only [functional_coordinates l (0, b), zero_mul, zero_add] using h

theorem rightTriangle_mixedArea (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (A : ConvexBody Plane) :
    2 * mixedArea volume A (rightTriangle a b) =
      SupportGeometry.support (A : Set Plane) (normal (0, -(|a * b| / a))) +
      SupportGeometry.support (A : Set Plane) (normal (|a * b| / b, 0)) +
      SupportGeometry.support (A : Set Plane) (normal (-(|a * b| / b), |a * b| / a)) := by
  first
  | let T := diagonalEquiv a b ha hb
    let A' := mapBody T.symm.toContinuousLinearMap A
    have hA : mapBody T.toContinuousLinearMap A' = A := by
      apply ConvexBody.ext
      simp only [A', coe_mapBody, Set.image_image]
      change (fun x => T (T.symm x)) '' (A : Set Plane) = (A : Set Plane)
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        have hyx : y = x := by simpa only [ContinuousLinearEquiv.apply_symm_apply] using he
        exact hyx ▸ hy
      · intro hx
        exact ⟨x, hx, T.apply_symm_apply x⟩
    have h := mixedArea_mapBody T.toContinuousLinearMap A' unitTriangle
    rw [hA, show T.toContinuousLinearMap = diagonalLinear a b from
        diagonalEquiv_toContinuousLinearMap a b ha hb, diagonalLinear_det] at h
    change mixedArea volume A (rightTriangle a b) = |a * b| * mixedArea volume A' unitTriangle at h
    have hf := unitTriangle_mixedArea A'
    have h0 := support_inverse_diagonal a b ha hb A (0, -1)
    have h1 := support_inverse_diagonal a b ha hb A (1, 0)
    have h2 := support_inverse_diagonal a b ha hb A (-1, 1)
    simp only [mul_zero, mul_one, mul_neg_one] at h0 h1 h2
    change |a * b| * SupportGeometry.support (A' : Set Plane) (normal (0, -1)) = _ at h0
    change |a * b| * SupportGeometry.support (A' : Set Plane) (normal (1, 0)) = _ at h1
    change |a * b| * SupportGeometry.support (A' : Set Plane) (normal (-1, 1)) = _ at h2
    nlinarith [congrArg (fun z : ℝ => |a * b| * z) hf]

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarLinearMixedArea.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarSupportWidth.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Directional widths as sums of actual support values -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem image_length_eq_support (P : ConvexBody Plane) (l : Plane →L[ℝ] ℝ) :
    volume.real (l '' (P : Set Plane)) =
      SupportGeometry.support (P : Set Plane) l +
        SupportGeometry.support (P : Set Plane) (-l) := by
  first
  | let S := l '' (P : Set Plane)
    have hc : IsCompact S := P.isCompact.image l.continuous
    have hv : Convex ℝ S := P.convex.linear_image l.toLinearMap
    have hn : S.Nonempty := P.nonempty.image l
    have hI : S = Icc (sInf S) (sSup S) :=
      eq_Icc_of_connected_compact ⟨hn, Real.convex_iff_isPreconnected.mp hv⟩ hc
    have hle : sInf S ≤ sSup S := csInf_le_csSup hn hc.bddBelow hc.bddAbove
    have hneg : (-l) '' (P : Set Plane) = -S := by
      ext z
      change (∃ x, x ∈ P ∧ (-l) x = z) ↔ -z ∈ S
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by simp⟩
      · rintro ⟨x, hx, he⟩
        refine ⟨x, hx, ?_⟩
        change -l x = z
        linarith
    change volume.real S = sSup S + sSup ((-l) '' (P : Set Plane))
    rw [hneg, Real.sSup_neg]
    calc
      volume.real S = volume.real (Icc (sInf S) (sSup S)) := congrArg volume.real hI
      _ = sSup S - sInf S := Real.volume_real_Icc_of_le hle
      _ = sSup S + -sInf S := sub_eq_add_neg _ _

@[simp] theorem normal_neg (e : Plane) : normal (-e) = -normal e := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    simp only [normal_apply, Prod.fst_neg, Prod.snd_neg, ContinuousLinearMap.neg_apply]
    ring

@[simp] theorem normal_zero : normal (0 : Plane) = 0 := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    simp only [normal_apply, Prod.fst_zero, Prod.snd_zero, zero_mul, sub_self,
      ContinuousLinearMap.zero_apply]

@[simp] theorem normal_pair_zero : normal ((0, 0) : Plane) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [normal_apply, zero_mul, sub_self, ContinuousLinearMap.zero_apply]

@[simp] theorem support_zero (P : ConvexBody Plane) :
    SupportGeometry.support (P : Set Plane) (0 : Plane →L[ℝ] ℝ) = 0 := by
  first
  | apply le_antisymm
    · exact SupportGeometry.support_le P.nonempty 0 (fun _ _ => le_rfl)
    · obtain ⟨p, hp⟩ := P.nonempty
      exact SupportGeometry.le_support P.isCompact 0 hp

theorem twice_mixedArea_segment_support (P : ConvexBody Plane) (e : Plane) :
    2 * mixedArea volume P (PlanarCorner.segmentBody e) =
      SupportGeometry.support (P : Set Plane) (normal e) +
        SupportGeometry.support (P : Set Plane) (normal (-e)) := by
  first
  | rw [twice_mixedArea_segment]
    have he : (determinantMap e).toContinuousLinearMap = normal (-e) := by
      apply ContinuousLinearMap.ext
      intro x
      change determinantMap e x = normal (-e) x
      simp only [determinantMap_apply, normal_apply, Prod.fst_neg, Prod.snd_neg, determinant]
      ring
    change volume.real ((determinantMap e).toContinuousLinearMap '' (P : Set Plane)) = _
    rw [he, image_length_eq_support, normal_neg, neg_neg]
    exact add_comm _ _

theorem support_axisX_sum (P : ConvexBody Plane) :
    SupportGeometry.support (P : Set Plane) (normal (0, 1)) +
      SupportGeometry.support (P : Set Plane) (normal (0, -1)) = width P := by
  first
  | have h := twice_mixedArea_segment_support P (0, 1)
    rw [show PlanarCorner.segmentBody (0, 1) = unitY from rfl, twice_mixedArea_unitY] at h
    simpa only [Prod.neg_mk, neg_zero] using h.symm

theorem support_axisY_sum (P : ConvexBody Plane) :
    SupportGeometry.support (P : Set Plane) (normal (1, 0)) +
      SupportGeometry.support (P : Set Plane) (normal (-1, 0)) = height P := by
  first
  | have h := twice_mixedArea_segment_support P (1, 0)
    rw [show PlanarCorner.segmentBody (1, 0) = unitX from rfl, twice_mixedArea_unitX] at h
    simpa only [Prod.neg_mk, neg_zero] using h.symm

theorem originSegment_eq_translate_centered (v : Plane) :
    originSegment v = ({(1 / 2 : ℝ) • v} : Set Plane) + centeredSegment v := by
  first
  | ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(1 / 2 : ℝ) • v, rfl, (t - 1 / 2) • v,
        ⟨t - 1 / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩, ?_⟩
      change (1 / 2 : ℝ) • v + (t - 1 / 2) • v = t • v
      rw [← add_smul]
      congr 1
      ring
    · rintro ⟨u, hu, y, ⟨t, ht, rfl⟩, rfl⟩
      change u = (1 / 2 : ℝ) • v at hu
      subst u
      refine ⟨t + 1 / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      change (t + 1 / 2) • v = (1 / 2 : ℝ) • v + t • v
      rw [← add_smul]
      congr 1
      ring

theorem rightTriangle_zero_right (a : ℝ) :
    rightTriangle a 0 = translateBody ((1 / 2 : ℝ) • (a, 0)) (PlanarCorner.segmentBody (a, 0)) := by
  first
  | apply ConvexBody.ext
    have he : (rightTriangle a 0 : Set Plane) = originSegment (a, 0) := by
      change (diagonalLinear a 0) '' (unitTriangle : Set Plane) = _
      have hf : (diagonalLinear a 0 : Plane → Plane) =
          (fun t : ℝ => t • ((a, 0) : Plane)) ∘ Prod.fst := by
        funext x
        ext <;> simp [diagonalLinear_apply, mul_comm]
      rw [hf, Set.image_comp, unitTriangle_projections.1]
      rfl
    rw [he, originSegment_eq_translate_centered]
    rfl

theorem rightTriangle_zero_left (b : ℝ) :
    rightTriangle 0 b = translateBody ((1 / 2 : ℝ) • (0, b)) (PlanarCorner.segmentBody (0, b)) := by
  first
  | apply ConvexBody.ext
    have he : (rightTriangle 0 b : Set Plane) = originSegment (0, b) := by
      change (diagonalLinear 0 b) '' (unitTriangle : Set Plane) = _
      have hf : (diagonalLinear 0 b : Plane → Plane) =
          (fun t : ℝ => t • ((0, b) : Plane)) ∘ Prod.snd := by
        funext x
        ext <;> simp [diagonalLinear_apply, mul_comm]
      rw [hf, Set.image_comp, unitTriangle_projections.2]
      rfl
    rw [he, originSegment_eq_translate_centered]
    rfl

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarSupportWidth.lean -/

/- BEGIN SOURCE: VolumePolynomials/EdgeTriangles.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # A literal right triangle for each oriented edge

Axis vectors give degenerate triangles, namely actual segments. Every vector
has the same three-term support formula. Consequently no sorting of edge
directions is needed in the finite corner calculus.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def orientation (e : Plane) : ℝ := if 0 ≤ e.1 * e.2 then 1 else -1

theorem abs_orientation (e : Plane) : |orientation e| = 1 := by
  first
  | unfold orientation
    split_ifs <;> norm_num

theorem orientation_ne_zero (e : Plane) : orientation e ≠ 0 := by
  first
  | intro h
    have h' := abs_orientation e
    rw [h, abs_zero] at h'
    norm_num at h'

theorem orientation_mul_product (e : Plane) :
    orientation e * (e.1 * e.2) = |e.1 * e.2| := by
  first
  | unfold orientation
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]

def triangleFromEdge (e : Plane) : ConvexBody Plane :=
  rightTriangle (orientation e * e.1) (-orientation e * e.2)

@[simp] theorem triangleFromEdge_width (e : Plane) : width (triangleFromEdge e) = |e.1| := by
  first
  | rw [triangleFromEdge, rightTriangle_width, abs_mul, abs_orientation, one_mul]

@[simp] theorem triangleFromEdge_height (e : Plane) : height (triangleFromEdge e) = |e.2| := by
  first
  | rw [triangleFromEdge, rightTriangle_height, abs_mul, abs_neg, abs_orientation, one_mul]

theorem triangleFromEdge_finiteHull (e : Plane) :
    PolytopeGeometry.IsFiniteHull (triangleFromEdge e : Set Plane) :=
  rightTriangle_finiteHull _ _

theorem triangleFromEdge_mixedArea (e : Plane) (A : ConvexBody Plane) :
    2 * mixedArea volume A (triangleFromEdge e) =
      SupportGeometry.support (A : Set Plane) (normal e) +
      SupportGeometry.support (A : Set Plane) (normal (0, -e.2)) +
      SupportGeometry.support (A : Set Plane) (normal (-e.1, 0)) := by
  first
  | rcases e with ⟨x, y⟩
    by_cases hx : x = 0
    · subst x
      have h := twice_mixedArea_segment_support A (0, -y)
      simp only [triangleFromEdge, orientation, zero_mul, le_refl, if_pos, one_mul,
        neg_one_mul, rightTriangle_zero_left, mixedArea_translate_right,
        neg_zero, normal_zero, normal_pair_zero, support_zero, add_zero]
      simpa only [Prod.neg_mk, neg_zero, neg_neg, add_comm] using h
    by_cases hy : y = 0
    · subst y
      have h := twice_mixedArea_segment_support A (x, 0)
      simp only [triangleFromEdge, orientation, mul_zero, le_refl, if_pos, one_mul,
        rightTriangle_zero_right, mixedArea_translate_right,
        neg_zero, normal_zero, normal_pair_zero, support_zero, add_zero]
      simpa only [Prod.neg_mk, neg_zero] using h
    let k := orientation (x, y)
    have hk : k ≠ 0 := orientation_ne_zero _
    have ha : k * x ≠ 0 := mul_ne_zero hk hx
    have hb : -k * y ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hk) hy
    have hab : |(k * x) * (-k * y)| = |x * y| := by
      first
      | simp only [abs_mul, abs_neg, show |k| = 1 from abs_orientation _, one_mul]
    have hdiva : |(k * x) * (-k * y)| / (k * x) = y := by
      first
      | apply (div_eq_iff ha).mpr
        rw [hab]
        calc
          |x * y| = k * (x * y) := (orientation_mul_product (x, y)).symm
          _ = y * (k * x) := by ring
    have hdivb : |(k * x) * (-k * y)| / (-k * y) = -x := by
      first
      | apply (div_eq_iff hb).mpr
        rw [hab]
        calc
          |x * y| = k * (x * y) := (orientation_mul_product (x, y)).symm
          _ = -x * (-k * y) := by ring
    have h := rightTriangle_mixedArea (k * x) (-k * y) ha hb A
    rw [hdiva, hdivb, neg_neg] at h
    change 2 * mixedArea volume A (triangleFromEdge (x, y)) = _ at h
    linarith

def edgeTriple (e : Plane) : Fin 3 → Plane := ![e, (0, -e.2), (-e.1, 0)]

theorem triangleFromEdge_represents (e : Plane) : Represents (triangleFromEdge e) (edgeTriple e) := by
  first
  | intro A
    simpa only [edgeTriple, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero, add_assoc] using triangleFromEdge_mixedArea e A

theorem positive_negative_parts (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  first
  | rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]

theorem hinge_kernel_identity (u v : ℝ) :
    max 0 (max u v) + max 0 (-u) + max 0 (-v) =
      |u| + |v| - min (max u 0) (max v 0) := by
  first
  | have hm : max 0 (max u v) = max (max u 0) (max v 0) := by
      first
      | simp only [max_assoc, max_left_comm, max_comm, max_self]
    rw [hm, max_comm 0 (-u), max_comm 0 (-v)]
    linarith [max_add_min (max u 0) (max v 0), positive_negative_parts u,
      positive_negative_parts v]

def pairKernel (e f : Plane) : ℝ :=
  min (max (orientation e * e.1 * f.2) 0) (max (orientation e * e.2 * f.1) 0)

theorem pairKernel_nonnegative (e f : Plane) : 0 ≤ pairKernel e f :=
  le_min (le_max_right _ _) (le_max_right _ _)

theorem triangleFromEdge_support (e f : Plane) :
    SupportGeometry.support (triangleFromEdge e : Set Plane) (normal f) =
      max 0 (max (orientation e * e.1 * f.2) (orientation e * e.2 * f.1)) := by
  first
  | rw [triangleFromEdge, rightTriangle_support]
    simp only [normal_apply, mul_one, mul_zero, zero_sub, sub_zero]
    congr 2 <;> ring

theorem triangle_pair_mixedArea (e f : Plane) :
    2 * mixedArea volume (triangleFromEdge e) (triangleFromEdge f) =
      |e.1| * |f.2| + |e.2| * |f.1| - pairKernel e f := by
  first
  | let u := orientation e * e.1 * f.2
    let v := orientation e * e.2 * f.1
    have h0 : SupportGeometry.support (triangleFromEdge e : Set Plane) (normal f) =
        max 0 (max u v) := triangleFromEdge_support e f
    have h1 : SupportGeometry.support (triangleFromEdge e : Set Plane) (normal (0, -f.2)) =
        max 0 (-u) := by
      first
      | rw [triangleFromEdge_support]
        simp only [u, mul_zero, mul_neg, max_assoc, max_comm, max_left_comm, max_self]
        exact max_eq_right (le_max_left _ _)
    have h2 : SupportGeometry.support (triangleFromEdge e : Set Plane) (normal (-f.1, 0)) =
        max 0 (-v) := by
      first
      | rw [triangleFromEdge_support]
        simp only [v, mul_zero, mul_neg, max_assoc, max_comm, max_left_comm, max_self]
        exact max_eq_right (le_max_left _ _)
    have hu : |u| = |e.1| * |f.2| := by simp only [u, abs_mul, abs_orientation, one_mul]
    have hv : |v| = |e.2| * |f.1| := by simp only [v, abs_mul, abs_orientation, one_mul]
    rw [triangleFromEdge_mixedArea, h0, h1, h2, hinge_kernel_identity, hu, hv]
    rfl

theorem positive_parts_min (u v : ℝ) :
    min (max u 0) (max v 0) =
      if 0 < u ∧ 0 < v then min |u| |v| else 0 := by
  first
  | by_cases h : 0 < u ∧ 0 < v
    · rw [if_pos h, max_eq_left h.1.le, max_eq_left h.2.le,
        abs_of_pos h.1, abs_of_pos h.2]
    · rw [if_neg h]
      rcases not_and_or.mp h with hu | hv
      · rw [max_eq_right (le_of_not_gt hu), min_eq_left (le_max_right _ _)]
      · rw [max_eq_right (le_of_not_gt hv), min_eq_right (le_max_right _ _)]

theorem positive_cross_iff (e f : Plane) :
    (0 < orientation e * e.1 * f.2 ∧ 0 < orientation e * e.2 * f.1) ↔
      (0 < e.1 * f.1 ∧ 0 < e.2 * f.2) := by
  first
  | by_cases hx : e.1 = 0
    · simp [hx]
    by_cases hy : e.2 = 0
    · simp [hy]
    have hprod : 0 < |e.1 * e.2| := abs_pos.mpr (mul_ne_zero hx hy)
    have hfirst : (orientation e * e.1 * f.2) * e.2 ^ 2 =
        |e.1 * e.2| * (e.2 * f.2) := by
      first
      | calc
          _ = (orientation e * (e.1 * e.2)) * (e.2 * f.2) := by ring
          _ = _ := by rw [orientation_mul_product]
    have hsecond : (orientation e * e.2 * f.1) * e.1 ^ 2 =
        |e.1 * e.2| * (e.1 * f.1) := by
      first
      | calc
          _ = (orientation e * (e.1 * e.2)) * (e.1 * f.1) := by ring
          _ = _ := by rw [orientation_mul_product]
    have h₁ : (0 < orientation e * e.1 * f.2) ↔ 0 < e.2 * f.2 := by
      first
      | rw [← mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hy), hfirst,
          mul_pos_iff_of_pos_left hprod]
    have h₂ : (0 < orientation e * e.2 * f.1) ↔ 0 < e.1 * f.1 := by
      first
      | rw [← mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hx), hsecond,
          mul_pos_iff_of_pos_left hprod]
    rw [h₁, h₂, and_comm]

/-- Exactly the same-corner minimum appearing in the paper. Axis vectors
contribute zero automatically. -/
theorem pairKernel_eq_min (e f : Plane) :
    pairKernel e f = if 0 < e.1 * f.1 ∧ 0 < e.2 * f.2 then
      min (|e.1| * |f.2|) (|e.2| * |f.1|) else 0 := by
  first
  | rw [pairKernel, positive_parts_min]
    simp only [positive_cross_iff, abs_mul, abs_orientation, one_mul]

theorem pairKernel_symmetric (e f : Plane) : pairKernel e f = pairKernel f e := by
  first
  | rw [pairKernel_eq_min, pairKernel_eq_min]
    simp only [mul_comm, min_comm]

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 15
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/EdgeTriangles.lean -/

/- BEGIN SOURCE: VolumePolynomials/CornerAreaIdentity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Exact corner area identities from actual right triangles

Each vector is replaced by a literal right triangle. Summing their three-term
mixed-area formulas and using the proved balance and width identities supplies
the exact area and mixed-area corner formulas. No shoelace formula, angular
sorting, or polygon reconstruction is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

@[simp] theorem normal_smul (r : ℝ) (e : Plane) : normal (r • e) = r • normal e := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    simp only [normal_apply, Prod.smul_fst, Prod.smul_snd,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem support_normal_signed_smul (P : ConvexBody Plane) (r : ℝ) (e : Plane) :
    SupportGeometry.support (P : Set Plane) (normal (r • e)) =
      max r 0 * SupportGeometry.support (P : Set Plane) (normal e) +
        max (-r) 0 * SupportGeometry.support (P : Set Plane) (normal (-e)) := by
  first
  | rcases le_total 0 r with hr | hr
    · rw [normal_smul, support_smul_functional _ _ hr, max_eq_left hr,
        max_eq_right (neg_nonpos.mpr hr), zero_mul, add_zero]
    · have he : r • e = (-r) • (-e) := by module
      rw [he, normal_smul, support_smul_functional _ _ (neg_nonneg.mpr hr),
        max_eq_right hr, max_eq_left (neg_nonneg.mpr hr), zero_mul, zero_add]

theorem support_sum_balanced {ι : Type*} [Fintype ι]
    (A : ConvexBody Plane) (r : ι → ℝ) (v : Plane) (c : ℝ)
    (hp : (∑ i, max (r i) 0) = c) (hn : (∑ i, max (-r i) 0) = c) :
    (∑ i, SupportGeometry.support (A : Set Plane) (normal (r i • v))) =
      c * (SupportGeometry.support (A : Set Plane) (normal v) +
        SupportGeometry.support (A : Set Plane) (normal (-v))) := by
  first
  | simp_rw [support_normal_signed_smul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp, hn]
    ring

theorem width_sum {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) :
    width (∑ i, K i) = ∑ i, width (K i) := by
  first
  | calc
      width (∑ i, K i) = 2 * mixedArea volume (∑ i, K i) unitY :=
        (twice_mixedArea_unitY _).symm
      _ = 2 * ∑ i, mixedArea volume (K i) unitY := by rw [mixedArea_sum_left]
      _ = ∑ i, width (K i) := by
        first
        | rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => twice_mixedArea_unitY (K i))

theorem height_sum {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) :
    height (∑ i, K i) = ∑ i, height (K i) := by
  first
  | calc
      height (∑ i, K i) = 2 * mixedArea volume (∑ i, K i) unitX :=
        (twice_mixedArea_unitX _).symm
      _ = 2 * ∑ i, mixedArea volume (K i) unitX := by rw [mixedArea_sum_left]
      _ = ∑ i, height (K i) := by
        first
        | rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => twice_mixedArea_unitX (K i))

def triangleSum {ι : Type*} [Fintype ι] (e : ι → Plane) : ConvexBody Plane :=
  ∑ i, triangleFromEdge (e i)

theorem triangleSum_width {ι : Type*} [Fintype ι] (e : ι → Plane) :
    width (triangleSum e) = ∑ i, |(e i).1| := by
  first
  | simp only [triangleSum, width_sum, triangleFromEdge_width]

theorem triangleSum_height {ι : Type*} [Fintype ι] (e : ι → Plane) :
    height (triangleSum e) = ∑ i, |(e i).2| := by
  first
  | simp only [triangleSum, height_sum, triangleFromEdge_height]

theorem Represents.axis_correction_x {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (A : ConvexBody Plane) :
    (∑ i, SupportGeometry.support (A : Set Plane) (normal (0, -(e i).2))) =
      height P * width A := by
  first
  | have hp := h.signed_variation
    have hsum := support_sum_balanced A (fun i => -(e i).2) (0, 1) (height P)
      hp.2.2.2 (by simpa only [neg_neg] using hp.2.1)
    have he (i : ι) : (-(e i).2) • ((0, 1) : Plane) = (0, -(e i).2) := by
      first
      | ext <;> simp
    simp only [he, Prod.neg_mk, neg_zero, support_axisX_sum] at hsum
    exact hsum

theorem Represents.axis_correction_y {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (A : ConvexBody Plane) :
    (∑ i, SupportGeometry.support (A : Set Plane) (normal (-(e i).1, 0))) =
      width P * height A := by
  first
  | have hp := h.signed_variation
    have hsum := support_sum_balanced A (fun i => -(e i).1) (1, 0) (width P)
      hp.2.2.1 (by simpa only [neg_neg] using hp.1)
    have he (i : ι) : (-(e i).1) • ((1, 0) : Plane) = (-(e i).1, 0) := by
      first
      | ext <;> simp
    simp only [he, Prod.neg_mk, neg_zero, support_axisY_sum] at hsum
    exact hsum

theorem Represents.triangleSum_functional {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (A : ConvexBody Plane) :
    2 * mixedArea volume A (triangleSum e) = 2 * mixedArea volume A P +
      height P * width A + width P * height A := by
  first
  | rw [triangleSum, mixedArea_sum_right, Finset.mul_sum]
    simp_rw [triangleFromEdge_mixedArea]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← h A,
      h.axis_correction_x A, h.axis_correction_y A]

def cornerPairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) : ℝ := ∑ i, ∑ j, pairKernel (e i) (f j)

theorem cornerPairing_nonnegative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) : 0 ≤ cornerPairing e f :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => pairKernel_nonnegative _ _))

theorem cornerPairing_symmetric {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) : cornerPairing e f = cornerPairing f e := by
  first
  | rw [cornerPairing, cornerPairing, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_congr rfl (fun i _ => pairKernel_symmetric _ _)

theorem triangleSum_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) :
    2 * mixedArea volume (triangleSum e) (triangleSum f) =
      (∑ i, |(e i).1|) * (∑ j, |(f j).2|) +
      (∑ i, |(e i).2|) * (∑ j, |(f j).1|) - cornerPairing e f := by
  first
  | rw [triangleSum, triangleSum, mixedArea_sum_left, Finset.mul_sum]
    simp_rw [mixedArea_sum_right, Finset.mul_sum, triangle_pair_mixedArea]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, cornerPairing]

/-- Exact mixed-area formula (4.5) for the actual finite edge representations. -/
theorem Represents.mixedArea_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    {P Q : ConvexBody Plane} {e : ι → Plane} {f : κ → Plane}
    (hP : Represents P e) (hQ : Represents Q f) :
    2 * mixedArea volume P Q =
      width P * height Q + height P * width Q - cornerPairing e f := by
  first
  | have hQP := hQ.triangleSum_functional P
    have hPT := hP.triangleSum_functional (triangleSum f)
    have hpair := triangleSum_pairing e f
    rw [mixedArea_symm volume (triangleSum f) (triangleSum e),
      mixedArea_symm volume (triangleSum f) P,
      triangleSum_width, triangleSum_height, hQ.total_variation.1, hQ.total_variation.2] at hPT
    rw [hP.total_variation.1, hP.total_variation.2,
      hQ.total_variation.1, hQ.total_variation.2] at hpair
    nlinarith

/-- Exact ordinary-area identity (4.3), not an abstract edge-area definition. -/
theorem Represents.area_identity {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) :
    volume.real (P : Set Plane) = width P * height P - cornerPairing e e / 2 := by
  first
  | have harea := h.mixedArea_identity h
    rw [mixedArea_diagonal volume plane_finrank] at harea
    nlinarith

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CornerAreaIdentity.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedAreaDetermination.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Mixed area determines an actual planar body up to translation

The proof uses the already computed right triangles as test bodies. It recovers
each support value from the mixed area and four coordinate support values.
Thus the triangle decomposition is an actual Minkowski identity, available
inside higher-dimensional mixed-volume expressions.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem support_translateBody (P : ConvexBody Plane) (v : Plane) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (translateBody v P : Set Plane) l =
      l v + SupportGeometry.support (P : Set Plane) l := by
  first
  | change SupportGeometry.support ((pointBody v : Set Plane) + (P : Set Plane)) l = _
    rw [SupportGeometry.support_add (pointBody v).isCompact (pointBody v).nonempty
      P.isCompact P.nonempty, support_pointBody]

theorem positive_part_sub_negative_part (x : ℝ) : max x 0 - max (-x) 0 = x := by
  first
  | rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring

theorem support_axis_difference (P Q : ConvexBody Plane) (v : Plane) (r d : ℝ)
    (hp : SupportGeometry.support (P : Set Plane) (normal v) -
      SupportGeometry.support (Q : Set Plane) (normal v) = d)
    (hn : SupportGeometry.support (P : Set Plane) (normal (-v)) -
      SupportGeometry.support (Q : Set Plane) (normal (-v)) = -d) :
    SupportGeometry.support (P : Set Plane) (normal (r • v)) -
      SupportGeometry.support (Q : Set Plane) (normal (r • v)) = r * d := by
  first
  | rw [support_normal_signed_smul, support_normal_signed_smul]
    calc
      _ = max r 0 *
          (SupportGeometry.support (P : Set Plane) (normal v) -
            SupportGeometry.support (Q : Set Plane) (normal v)) +
          max (-r) 0 *
          (SupportGeometry.support (P : Set Plane) (normal (-v)) -
            SupportGeometry.support (Q : Set Plane) (normal (-v))) := by ring
      _ = (max r 0 - max (-r) 0) * d := by rw [hp, hn]; ring
      _ = r * d := by rw [positive_part_sub_negative_part]

/-- Equality of all literal mixed areas gives equality up to an actual
translation; no uniqueness theorem for surface-area measures is assumed. -/
theorem eq_translate_of_mixedArea_eq (P Q : ConvexBody Plane)
    (h : ∀ A : ConvexBody Plane, mixedArea volume A P = mixedArea volume A Q) :
    ∃ v : Plane, P = translateBody v Q := by
  first
  | let dx : ℝ := SupportGeometry.support (P : Set Plane) (normal (0, 1)) -
      SupportGeometry.support (Q : Set Plane) (normal (0, 1))
    let dy : ℝ := SupportGeometry.support (P : Set Plane) (normal (1, 0)) -
      SupportGeometry.support (Q : Set Plane) (normal (1, 0))
    have hw : width P = width Q := by
      have hs := h unitY
      rw [mixedArea_symm volume unitY P, mixedArea_symm volume unitY Q] at hs
      linarith [twice_mixedArea_unitY P, twice_mixedArea_unitY Q]
    have hh : height P = height Q := by
      have hs := h unitX
      rw [mixedArea_symm volume unitX P, mixedArea_symm volume unitX Q] at hs
      linarith [twice_mixedArea_unitX P, twice_mixedArea_unitX Q]
    have hnx : SupportGeometry.support (P : Set Plane) (normal (0, -1)) -
        SupportGeometry.support (Q : Set Plane) (normal (0, -1)) = -dx := by
      dsimp only [dx]
      linarith [support_axisX_sum P, support_axisX_sum Q]
    have hny : SupportGeometry.support (P : Set Plane) (normal (-1, 0)) -
        SupportGeometry.support (Q : Set Plane) (normal (-1, 0)) = -dy := by
      dsimp only [dy]
      linarith [support_axisY_sum P, support_axisY_sum Q]
    have hx (r : ℝ) : SupportGeometry.support (P : Set Plane) (normal (0, r)) -
        SupportGeometry.support (Q : Set Plane) (normal (0, r)) = r * dx := by
      have hn : -((0, 1) : Plane) = (0, -1) := by ext <;> simp
      have he : r • ((0, 1) : Plane) = (0, r) := by ext <;> simp
      simpa only [hn, he] using support_axis_difference P Q (0, 1) r dx rfl (by rwa [hn])
    have hy (r : ℝ) : SupportGeometry.support (P : Set Plane) (normal (r, 0)) -
        SupportGeometry.support (Q : Set Plane) (normal (r, 0)) = r * dy := by
      have hn : -((1, 0) : Plane) = (-1, 0) := by ext <;> simp
      have he : r • ((1, 0) : Plane) = (r, 0) := by ext <;> simp
      simpa only [hn, he] using support_axis_difference P Q (1, 0) r dy rfl (by rwa [hn])
    have hall (e : Plane) : SupportGeometry.support (P : Set Plane) (normal e) -
        SupportGeometry.support (Q : Set Plane) (normal e) = e.2 * dx + e.1 * dy := by
      have ht := h (triangleFromEdge e)
      rw [mixedArea_symm volume (triangleFromEdge e) P,
        mixedArea_symm volume (triangleFromEdge e) Q] at ht
      have hp := triangleFromEdge_mixedArea e P
      have hq := triangleFromEdge_mixedArea e Q
      linarith [hx (-e.2), hy (-e.1)]
    refine ⟨(dx, -dy), ConvexBody.ext ?_⟩
    apply SupportGeometry.eq_of_support_eq P.isCompact P.nonempty P.convex
      (translateBody (dx, -dy) Q).isCompact (translateBody (dx, -dy) Q).nonempty
      (translateBody (dx, -dy) Q).convex
    intro l
    have he := hall (edgeOfFunctional l)
    rw [normal_edgeOfFunctional] at he
    rw [support_translateBody, ← normal_edgeOfFunctional l, normal_apply]
    rw [normal_edgeOfFunctional l]
    linarith

def boundingRectangle (P : ConvexBody Plane) : ConvexBody Plane :=
  width P • unitX + height P • unitY

theorem boundingRectangle_mixedArea (P A : ConvexBody Plane) :
    2 * mixedArea volume A (boundingRectangle P) =
      width P * height A + height P * width A := by
  first
  | rw [boundingRectangle, mixedArea_add_right,
      mixedArea_smul_right volume A unitX (show 0 ≤ width P from measureReal_nonneg),
      mixedArea_smul_right volume A unitY (show 0 ≤ height P from measureReal_nonneg)]
    rw [← twice_mixedArea_unitX A, ← twice_mixedArea_unitY A]
    ring

/-- Every finite facet representation yields an actual Minkowski decomposition
into the explicit right triangles, with only a harmless translation. -/
theorem Represents.triangleSum_eq_translate {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) :
    ∃ v : Plane, triangleSum e = translateBody v (P + boundingRectangle P) := by
  first
  | apply eq_translate_of_mixedArea_eq
    intro A
    have ht := h.triangleSum_functional A
    have hr := boundingRectangle_mixedArea P A
    rw [mixedArea_add_right]
    linarith

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedAreaDetermination.lean -/

/- BEGIN SOURCE: VolumePolynomials/TriangleExtremeFaces.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Extreme coordinate segments of the literal edge triangles -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem rightTriangle_zero (a b : ℝ) : (0 : Plane) ∈ rightTriangle a b := by
  first
  | exact ⟨0, by norm_num [mem_unitTriangle], by simp⟩

theorem rightTriangle_axisX {a b x : ℝ} (hx : min 0 a ≤ x ∧ x ≤ max 0 a) :
    (x, 0) ∈ rightTriangle a b := by
  first
  | by_cases ha : a = 0
    · have hx' : 0 ≤ x ∧ x ≤ 0 := by simpa [ha] using hx
      have hx0 : x = 0 := le_antisymm hx'.2 hx'.1
      subst x
      exact rightTriangle_zero a b
    have ht : 0 ≤ x / a ∧ x / a ≤ 1 := by
      first
      | rcases lt_or_gt_of_ne ha with ha | ha
        · have hx' : a ≤ x ∧ x ≤ 0 := by simpa [min_eq_right ha.le, max_eq_left ha.le] using hx
          exact ⟨div_nonneg_of_nonpos hx'.2 ha.le, (div_le_one_of_neg ha).mpr hx'.1⟩
        · have hx' : 0 ≤ x ∧ x ≤ a := by simpa [min_eq_left ha.le, max_eq_right ha.le] using hx
          exact ⟨div_nonneg hx'.1 ha.le, (div_le_one ha).mpr hx'.2⟩
    refine ⟨(x / a, 0), (mem_unitTriangle _).mpr ⟨ht.1, le_rfl, by simpa using ht.2⟩, ?_⟩
    ext <;> simp only [diagonalLinear_apply, Prod.fst, Prod.snd, mul_zero] <;> field_simp [ha]

theorem rightTriangle_axisY {a b y : ℝ} (hy : min 0 b ≤ y ∧ y ≤ max 0 b) :
    (0, y) ∈ rightTriangle a b := by
  first
  | by_cases hb : b = 0
    · have hy' : 0 ≤ y ∧ y ≤ 0 := by simpa [hb] using hy
      have hy0 : y = 0 := le_antisymm hy'.2 hy'.1
      subst y
      exact rightTriangle_zero a b
    have ht : 0 ≤ y / b ∧ y / b ≤ 1 := by
      first
      | rcases lt_or_gt_of_ne hb with hb | hb
        · have hy' : b ≤ y ∧ y ≤ 0 := by simpa [min_eq_right hb.le, max_eq_left hb.le] using hy
          exact ⟨div_nonneg_of_nonpos hy'.2 hb.le, (div_le_one_of_neg hb).mpr hy'.1⟩
        · have hy' : 0 ≤ y ∧ y ≤ b := by simpa [min_eq_left hb.le, max_eq_right hb.le] using hy
          exact ⟨div_nonneg hy'.1 hb.le, (div_le_one hb).mpr hy'.2⟩
    refine ⟨(0, y / b), (mem_unitTriangle _).mpr ⟨le_rfl, ht.1, by simpa using ht.2⟩, ?_⟩
    ext <;> simp only [diagonalLinear_apply, Prod.fst, Prod.snd, mul_zero] <;> field_simp [hb]

theorem rightTriangle_bounds (a b : ℝ) {p : Plane} (hp : p ∈ rightTriangle a b) :
    (min 0 a ≤ p.1 ∧ p.1 ≤ max 0 a) ∧ (min 0 b ≤ p.2 ∧ p.2 ≤ max 0 b) := by
  first
  | obtain ⟨q, hq, rfl⟩ := hp
    have hq := (mem_unitTriangle q).mp hq
    have hqx : q.1 ≤ 1 := by linarith [hq.2.1, hq.2.2]
    have hqy : q.2 ≤ 1 := by linarith [hq.1, hq.2.2]
    simp only [diagonalLinear_apply]
    constructor
    · rcases le_total 0 a with ha | ha
      · rw [min_eq_left ha, max_eq_right ha]
        exact ⟨mul_nonneg ha hq.1, (mul_le_mul_of_nonneg_left hqx ha).trans_eq (mul_one a)⟩
      · rw [min_eq_right ha, max_eq_left ha]
        exact ⟨by nlinarith [mul_le_mul_of_nonpos_left hqx ha], mul_nonpos_of_nonpos_of_nonneg ha hq.1⟩
    · rcases le_total 0 b with hb | hb
      · rw [min_eq_left hb, max_eq_right hb]
        exact ⟨mul_nonneg hb hq.2.1, (mul_le_mul_of_nonneg_left hqy hb).trans_eq (mul_one b)⟩
      · rw [min_eq_right hb, max_eq_left hb]
        exact ⟨by nlinarith [mul_le_mul_of_nonpos_left hqy hb], mul_nonpos_of_nonpos_of_nonneg hb hq.2.1⟩

theorem max_sub_min_eq_abs (a : ℝ) : max 0 a - min 0 a = |a| := by
  first
  | rcases le_total 0 a with ha | ha
    · rw [max_eq_right ha, min_eq_left ha, abs_of_nonneg ha]
      ring
    · rw [max_eq_left ha, min_eq_right ha, abs_of_nonpos ha]
      ring

theorem rightTriangle_bottom_segment (a b r : ℝ) (hr : 0 ≤ r) (hra : r ≤ |a|)
    (hrb : b < 0 → r = 0) :
    ∃ x : ℝ, (x, min 0 b) ∈ rightTriangle a b ∧ (x + r, min 0 b) ∈ rightTriangle a b := by
  first
  | by_cases hb : 0 ≤ b
    · rw [min_eq_left hb]
      refine ⟨min 0 a, rightTriangle_axisX ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisX
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs a]
    · have hr0 := hrb (lt_of_not_ge hb)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisY ⟨le_rfl, min_le_max⟩,
        rightTriangle_axisY ⟨le_rfl, min_le_max⟩⟩

theorem rightTriangle_top_segment (a b r : ℝ) (hr : 0 ≤ r) (hra : r ≤ |a|)
    (hrb : 0 < b → r = 0) :
    ∃ x : ℝ, (x, max 0 b) ∈ rightTriangle a b ∧ (x + r, max 0 b) ∈ rightTriangle a b := by
  first
  | by_cases hb : b ≤ 0
    · rw [max_eq_left hb]
      refine ⟨min 0 a, rightTriangle_axisX ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisX
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs a]
    · have hr0 := hrb (lt_of_not_ge hb)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisY ⟨min_le_max, le_rfl⟩,
        rightTriangle_axisY ⟨min_le_max, le_rfl⟩⟩

theorem rightTriangle_left_segment (a b r : ℝ) (hr : 0 ≤ r) (hrb : r ≤ |b|)
    (hra : a < 0 → r = 0) :
    ∃ y : ℝ, (min 0 a, y) ∈ rightTriangle a b ∧ (min 0 a, y + r) ∈ rightTriangle a b := by
  first
  | by_cases ha : 0 ≤ a
    · rw [min_eq_left ha]
      refine ⟨min 0 b, rightTriangle_axisY ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisY
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs b]
    · have hr0 := hra (lt_of_not_ge ha)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisX ⟨le_rfl, min_le_max⟩,
        rightTriangle_axisX ⟨le_rfl, min_le_max⟩⟩

theorem rightTriangle_right_segment (a b r : ℝ) (hr : 0 ≤ r) (hrb : r ≤ |b|)
    (hra : 0 < a → r = 0) :
    ∃ y : ℝ, (max 0 a, y) ∈ rightTriangle a b ∧ (max 0 a, y + r) ∈ rightTriangle a b := by
  first
  | by_cases ha : a ≤ 0
    · rw [max_eq_left ha]
      refine ⟨min 0 b, rightTriangle_axisY ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisY
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs b]
    · have hr0 := hra (lt_of_not_ge ha)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisX ⟨min_le_max, le_rfl⟩,
        rightTriangle_axisX ⟨min_le_max, le_rfl⟩⟩

theorem triangleFromEdge_extreme_segments (e : Plane) :
    (∃ x : ℝ, (x, min 0 (-orientation e * e.2)) ∈ triangleFromEdge e ∧
      (x + max (-e.1) 0, min 0 (-orientation e * e.2)) ∈ triangleFromEdge e) ∧
    (∃ x : ℝ, (x, max 0 (-orientation e * e.2)) ∈ triangleFromEdge e ∧
      (x + max e.1 0, max 0 (-orientation e * e.2)) ∈ triangleFromEdge e) ∧
    (∃ y : ℝ, (min 0 (orientation e * e.1), y) ∈ triangleFromEdge e ∧
      (min 0 (orientation e * e.1), y + max e.2 0) ∈ triangleFromEdge e) ∧
    (∃ y : ℝ, (max 0 (orientation e * e.1), y) ∈ triangleFromEdge e ∧
      (max 0 (orientation e * e.1), y + max (-e.2) 0) ∈ triangleFromEdge e) := by
  first
  | have ha : |orientation e * e.1| = |e.1| := by rw [abs_mul, abs_orientation, one_mul]
    have hb : |-orientation e * e.2| = |e.2| := by rw [abs_mul, abs_neg, abs_orientation, one_mul]
    have hxy : (-orientation e * e.2) * e.1 ≤ 0 := by
      first
      | have h := orientation_mul_product e
        nlinarith [abs_nonneg (e.1 * e.2)]
    have hyx : (orientation e * e.1) * e.2 ≥ 0 := by
      first
      | have h := orientation_mul_product e
        nlinarith [abs_nonneg (e.1 * e.2)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply rightTriangle_bottom_segment _ _ _ (le_max_right _ _)
      · rw [ha]
        exact max_le (neg_le_abs _) (abs_nonneg _)
      · intro hneg
        apply max_eq_right
        have hx : 0 ≤ e.1 := by nlinarith
        exact neg_nonpos.mpr hx
    · apply rightTriangle_top_segment _ _ _ (le_max_right _ _)
      · rw [ha]
        exact max_le (le_abs_self _) (abs_nonneg _)
      · intro hpos
        apply max_eq_right
        nlinarith
    · apply rightTriangle_left_segment _ _ _ (le_max_right _ _)
      · rw [hb]
        exact max_le (le_abs_self _) (abs_nonneg _)
      · intro hneg
        apply max_eq_right
        nlinarith
    · apply rightTriangle_right_segment _ _ _ (le_max_right _ _)
      · rw [hb]
        exact max_le (neg_le_abs _) (abs_nonneg _)
      · intro hpos
        apply max_eq_right
        have hy : 0 ≤ e.2 := by nlinarith
        exact neg_nonpos.mpr hy

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/TriangleExtremeFaces.lean -/

/- BEGIN SOURCE: VolumePolynomials/CoordinateErosionBody.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Actual removal of the two coordinate segments -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarErosion OAI.Paper092

def vertical (h : ℝ) : Set Plane := {0} ×ˢ Icc 0 h

def verticalErosion (C : Set Plane) (h : ℝ) : Set Plane :=
  {p | p ∈ C ∧ p + (0, h) ∈ C}

theorem swap_add_coordinates (p q : Plane) : (p + q).swap = p.swap + q.swap := rfl

theorem verticalErosion_compact {C : Set Plane} (hC : IsCompact C) (h : ℝ) :
    IsCompact (verticalErosion C h) :=
  hC.inter_right (hC.isClosed.preimage (continuous_id.add continuous_const))

theorem verticalErosion_convex {C : Set Plane} (hC : Convex ℝ C) (h : ℝ) :
    Convex ℝ (verticalErosion C h) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
    have hp := hC hx.2 hy.2 ha hb hab
    have he : a • (x + (0, h)) + b • (y + (0, h)) =
        (a • x + b • y) + (0, h) := by
      rw [smul_add, smul_add]
      calc
        _ = (a • x + b • y) + (a • (0, h) + b • (0, h)) := by abel
        _ = _ := by rw [← add_smul, hab, one_smul]
    rwa [he] at hp

theorem eq_verticalErosion_add_of_bounds {C : Set Plane}
    (hC : IsCompact C) (hc : Convex ℝ C) {lo hi h : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ p ∈ C, lo ≤ p.1 ∧ p.1 ≤ hi)
    (hlo : ∃ a : ℝ, (lo, a) ∈ C ∧ (lo, a + h) ∈ C)
    (hhi : ∃ b : ℝ, (hi, b) ∈ C ∧ (hi, b + h) ∈ C) :
    C = verticalErosion C h + vertical h := by
  first
  | let D : Set Plane := Prod.swap '' C
    have hDc : IsCompact D := hC.image continuous_swap
    have hDv : Convex ℝ D := hc.linear_image (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap
    have hD := eq_erosion_add_horizontal_of_vertical_bounds hDc hDv hh
      (lo := lo) (hi := hi) (by
        rintro p ⟨q, hq, rfl⟩
        exact hbound q hq)
      (by
        obtain ⟨a, ha, har⟩ := hlo
        exact ⟨a, ⟨(lo, a), ha, rfl⟩, ⟨(lo, a + h), har, rfl⟩⟩)
      (by
        obtain ⟨b, hb, hbr⟩ := hhi
        exact ⟨b, ⟨(hi, b), hb, rfl⟩, ⟨(hi, b + h), hbr, rfl⟩⟩)
    have hswap (p : Plane) : p.swap ∈ D ↔ p ∈ C := by
      constructor
      · rintro ⟨q, hq, he⟩
        have hqp : q = p := by simpa only [Prod.swap_swap] using congrArg Prod.swap he
        exact hqp ▸ hq
      · intro hp
        exact ⟨p, hp, rfl⟩
    ext p
    constructor
    · intro hp
      have hs : p.swap ∈ erosion D h + horizontal h := hD ▸ (hswap p).mpr hp
      obtain ⟨q, hq, r, hr, he⟩ := hs
      have hr0 : r.2 = 0 := hr.2
      refine ⟨q.swap, ⟨(hswap q.swap).mp (by simpa using hq.1), ?_⟩,
        r.swap, ⟨hr0, hr.1⟩, ?_⟩
      · apply (hswap (q.swap + (0, h))).mp
        simpa only [swap_add_coordinates, Prod.swap_swap, Prod.swap_prod_mk] using hq.2
      · have h := congrArg Prod.swap he
        simpa only [swap_add_coordinates, Prod.swap_swap] using h
    · rintro ⟨q, hq, r, hr, rfl⟩
      apply (hswap (q + r)).mp
      rw [hD]
      refine ⟨q.swap, ⟨(hswap q).mpr hq.1, ?_⟩, r.swap, ⟨hr.2, hr.1⟩, ?_⟩
      · have h := (hswap (q + (0, h))).mpr hq.2
        simpa only [swap_add_coordinates, Prod.swap_prod_mk] using h
      · simp only [swap_add_coordinates]

/-- Removing a horizontal summand preserves the left supporting face and
translates the right supporting face by its length. -/
theorem erosion_extreme_vertical_endpoints {C : Set Plane} {r lo hi yl yr : ℝ}
    (hbound : ∀ p ∈ C, lo ≤ p.1 ∧ p.1 ≤ hi)
    (hdecomp : C = erosion C r + horizontal r)
    (hl : (lo, yl) ∈ C) (hr : (hi, yr) ∈ C) :
    (lo, yl) ∈ erosion C r ∧ (hi - r, yr) ∈ erosion C r := by
  first
  | constructor
    · have hp : (lo, yl) ∈ erosion C r + horizontal r := hdecomp ▸ hl
      obtain ⟨q, hq, v, hv, he⟩ := hp
      have hb := hbound q hq.1
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      have hv0 : v.2 = 0 := hv.2
      have hfv : v.1 = 0 := by
        change q.1 + v.1 = lo at hx
        linarith [hv.1.1]
      have hqeq : q = (lo, yl) := by
        ext
        · change q.1 + v.1 = lo at hx
          simpa only [hfv, add_zero] using hx
        · change q.2 + v.2 = yl at hy
          simpa only [hv0, add_zero] using hy
      exact hqeq ▸ hq
    · have hp : (hi, yr) ∈ erosion C r + horizontal r := hdecomp ▸ hr
      obtain ⟨q, hq, v, hv, he⟩ := hp
      have hb := hbound (q + (r, 0)) hq.2
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      have hv0 : v.2 = 0 := hv.2
      have hfv : v.1 = r := by
        have hb2 : q.1 + r ≤ hi := hb.2
        change q.1 + v.1 = hi at hx
        linarith [hv.1.2]
      have hqeq : q = (hi - r, yr) := by
        ext
        · change q.1 + v.1 = hi at hx
          linarith
        · change q.2 + v.2 = yr at hy
          simpa only [hv0, add_zero] using hy
      exact hqeq ▸ hq

/-- Two extreme horizontal and two extreme vertical segments yield a literal
rectangle summand, including all degenerate cases. -/
theorem exists_rectangle_remainder (C : ConvexBody Plane)
    {lx ux ly uy w h : ℝ} (hw : 0 ≤ w) (hh : 0 ≤ h)
    (hbound : ∀ p ∈ C, (lx ≤ p.1 ∧ p.1 ≤ ux) ∧ (ly ≤ p.2 ∧ p.2 ≤ uy))
    (hbottom : ∃ a : ℝ, (a, ly) ∈ C ∧ (a + w, ly) ∈ C)
    (htop : ∃ a : ℝ, (a, uy) ∈ C ∧ (a + w, uy) ∈ C)
    (hleft : ∃ a : ℝ, (lx, a) ∈ C ∧ (lx, a + h) ∈ C)
    (hright : ∃ a : ℝ, (ux, a) ∈ C ∧ (ux, a + h) ∈ C) :
    ∃ Q : ConvexBody Plane, (C : Set Plane) =
      ((Q : Set Plane) + vertical h) + horizontal w := by
  first
  | let E := erosion (C : Set Plane) w
    have hE : (C : Set Plane) = E + horizontal w :=
      eq_erosion_add_horizontal_of_vertical_bounds C.isCompact C.convex hw
        (fun p hp => (hbound p hp).2) hbottom htop
    have hEb : ∀ p ∈ E, lx ≤ p.1 ∧ p.1 ≤ ux - w := by
      intro p hp
      have h0 := (hbound p hp.1).1
      have h1 := (hbound (p + (w, 0)) hp.2).1
      have h12 : p.1 + w ≤ ux := h1.2
      exact ⟨h0.1, by linarith⟩
    obtain ⟨a, ha, hah⟩ := hleft
    obtain ⟨b, hb, hbh⟩ := hright
    have hleftE : (lx, a) ∈ E ∧ (lx, a + h) ∈ E := by
      constructor
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE ha hb).1
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE hah hbh).1
    have hrightE : (ux - w, b) ∈ E ∧ (ux - w, b + h) ∈ E := by
      constructor
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE ha hb).2
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE hah hbh).2
    have hEc := erosion_compact C.isCompact w
    have hEv := erosion_convex C.convex w
    have hQne : (verticalErosion E h).Nonempty := by
      refine ⟨(lx, a), hleftE.1, ?_⟩
      simpa only [Prod.mk_add_mk, add_zero] using hleftE.2
    let Q : ConvexBody Plane :=
      ⟨verticalErosion E h, verticalErosion_convex hEv h,
        verticalErosion_compact hEc h, hQne⟩
    refine ⟨Q, ?_⟩
    have hV := eq_verticalErosion_add_of_bounds hEc hEv hh hEb
      ⟨a, hleftE.1, hleftE.2⟩ ⟨b, hrightE.1, hrightE.2⟩
    change E = (Q : Set Plane) + vertical h at hV
    rw [hE, hV]

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CoordinateErosionBody.lean -/

/- BEGIN SOURCE: VolumePolynomials/BalancedEdgeBody.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Construction of an actual body from balanced finite edge vectors

Summing literal right triangles and removing an actual rectangle replaces
angular sorting. The resulting body has the prescribed mixed-area functional
and coordinate widths, with no nondegeneracy assumption on individual vectors.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem rightTriangle_horizontal {r : ℝ} (hr : 0 ≤ r) :
    (rightTriangle r 0 : Set Plane) = horizontal r := by
  first
  | ext p
    constructor
    · intro hp
      have h := rightTriangle_bounds r 0 hp
      have hy' : 0 ≤ p.2 ∧ p.2 ≤ 0 := by simpa using h.2
      have hy : p.2 = 0 := le_antisymm hy'.2 hy'.1
      exact ⟨by simpa [min_eq_left hr, max_eq_right hr] using h.1, hy⟩
    · intro hp
      have hy : p.2 = 0 := hp.2
      have he : p = (p.1, 0) := by ext <;> simp [hy]
      rw [he]
      apply rightTriangle_axisX
      simpa [min_eq_left hr, max_eq_right hr] using hp.1

theorem rightTriangle_vertical {r : ℝ} (hr : 0 ≤ r) :
    (rightTriangle 0 r : Set Plane) = vertical r := by
  first
  | ext p
    constructor
    · intro hp
      have h := rightTriangle_bounds 0 r hp
      have hx' : 0 ≤ p.1 ∧ p.1 ≤ 0 := by simpa using h.1
      have hx : p.1 = 0 := le_antisymm hx'.2 hx'.1
      exact ⟨hx, by simpa [min_eq_left hr, max_eq_right hr] using h.2⟩
    · intro hp
      have hx : p.1 = 0 := hp.1
      have he : p = (0, p.2) := by ext <;> simp [hx]
      rw [he]
      apply rightTriangle_axisY
      simpa [min_eq_left hr, max_eq_right hr] using hp.2

theorem rightTriangle_axisX_mixedArea (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    2 * mixedArea volume A (rightTriangle r 0) = r * height A := by
  first
  | rw [rightTriangle_zero_right, mixedArea_translate_right, twice_mixedArea_segment_support]
    have h1 : ((r, 0) : Plane) = r • ((1, 0) : Plane) := by ext <;> simp
    have h2 : -((r, 0) : Plane) = r • ((-1, 0) : Plane) := by ext <;> simp
    rw [h2, h1, normal_smul, normal_smul,
      support_smul_functional _ _ hr, support_smul_functional _ _ hr, ← mul_add,
      support_axisY_sum]

theorem rightTriangle_axisY_mixedArea (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    2 * mixedArea volume A (rightTriangle 0 r) = r * width A := by
  first
  | rw [rightTriangle_zero_left, mixedArea_translate_right, twice_mixedArea_segment_support]
    have h1 : ((0, r) : Plane) = r • ((0, 1) : Plane) := by ext <;> simp
    have h2 : -((0, r) : Plane) = r • ((0, -1) : Plane) := by ext <;> simp
    rw [h2, h1, normal_smul, normal_smul,
      support_smul_functional _ _ hr, support_smul_functional _ _ hr, ← mul_add,
      support_axisX_sum]

theorem sum_horizontal_segments {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody Plane) (y r : ι → ℝ)
    (h : ∀ i, ∃ x : ℝ, (x, y i) ∈ K i ∧ (x + r i, y i) ∈ K i) :
    ∃ x : ℝ, (x, ∑ i, y i) ∈ ∑ i, K i ∧
      (x + ∑ i, r i, ∑ i, y i) ∈ ∑ i, K i := by
  first
  | choose x hx hxr using h
    refine ⟨∑ i, x i, ?_, ?_⟩
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i, y i), hx, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum]
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i + r i, y i), hxr, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib]

theorem sum_vertical_segments {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody Plane) (x r : ι → ℝ)
    (h : ∀ i, ∃ y : ℝ, (x i, y) ∈ K i ∧ (x i, y + r i) ∈ K i) :
    ∃ y : ℝ, (∑ i, x i, y) ∈ ∑ i, K i ∧
      (∑ i, x i, y + ∑ i, r i) ∈ ∑ i, K i := by
  first
  | choose y hy hyr using h
    refine ⟨∑ i, y i, ?_, ?_⟩
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i, y i), hy, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum]
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i, y i + r i), hyr, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib]

/-- The hypotheses are the four signed coordinate totals, not an assumed
existence theorem for polygons. The conclusion constructs an actual convex body. -/
theorem exists_body_of_balanced_edges {ι : Type*} [Fintype ι] (e : ι → Plane)
    {w h : ℝ}
    (hxp : (∑ i, max (e i).1 0) = w) (hxn : (∑ i, max (-(e i).1) 0) = w)
    (hyp : (∑ i, max (e i).2 0) = h) (hyn : (∑ i, max (-(e i).2) 0) = h) :
    ∃ Q : ConvexBody Plane, Represents Q e ∧ width Q = w ∧ height Q = h := by
  first
  | have hw : 0 ≤ w := by rw [← hxp]; positivity
    have hh : 0 ≤ h := by rw [← hyp]; positivity
    let a (i : ι) := orientation (e i) * (e i).1
    let b (i : ι) := -orientation (e i) * (e i).2
    let lx := ∑ i, min 0 (a i)
    let ux := ∑ i, max 0 (a i)
    let ly := ∑ i, min 0 (b i)
    let uy := ∑ i, max 0 (b i)
    have hbound : ∀ p ∈ triangleSum e,
        (lx ≤ p.1 ∧ p.1 ≤ ux) ∧ (ly ≤ p.2 ∧ p.2 ≤ uy) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := (mem_sum_body (fun i => triangleFromEdge (e i)) p).mp hp
      simp only [Prod.fst_sum, Prod.snd_sum]
      exact ⟨⟨Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).1.1),
        Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).1.2)⟩,
        ⟨Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).2.1),
        Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).2.2)⟩⟩
    have hbottom : ∃ x, (x, ly) ∈ triangleSum e ∧ (x + w, ly) ∈ triangleSum e := by
      simpa only [hxn, ly, triangleSum] using sum_horizontal_segments (fun i => triangleFromEdge (e i))
        (fun i => min 0 (b i)) (fun i => max (-(e i).1) 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).1)
    have htop : ∃ x, (x, uy) ∈ triangleSum e ∧ (x + w, uy) ∈ triangleSum e := by
      simpa only [hxp, uy, triangleSum] using sum_horizontal_segments (fun i => triangleFromEdge (e i))
        (fun i => max 0 (b i)) (fun i => max (e i).1 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).2.1)
    have hleft : ∃ y, (lx, y) ∈ triangleSum e ∧ (lx, y + h) ∈ triangleSum e := by
      simpa only [hyp, lx, triangleSum] using sum_vertical_segments (fun i => triangleFromEdge (e i))
        (fun i => min 0 (a i)) (fun i => max (e i).2 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).2.2.1)
    have hright : ∃ y, (ux, y) ∈ triangleSum e ∧ (ux, y + h) ∈ triangleSum e := by
      simpa only [hyn, ux, triangleSum] using sum_vertical_segments (fun i => triangleFromEdge (e i))
        (fun i => max 0 (a i)) (fun i => max (-(e i).2) 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).2.2.2)
    obtain ⟨Q, hQ⟩ := exists_rectangle_remainder (triangleSum e) hw hh hbound
      hbottom htop hleft hright
    have hbody : triangleSum e = (Q + rightTriangle 0 h) + rightTriangle w 0 := by
      apply ConvexBody.ext
      change (triangleSum e : Set Plane) = ((Q : Set Plane) + (rightTriangle 0 h : Set Plane)) + _
      rwa [rightTriangle_horizontal hw, rightTriangle_vertical hh]
    have hvarx : (∑ i, |(e i).1|) = 2 * w := by
      have hi (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
        rcases le_total 0 x with hx | hx <;> simp [abs_of_nonneg, abs_of_nonpos, hx,
          max_eq_left, max_eq_right, neg_nonpos, neg_nonneg]
      simp_rw [hi]
      rw [Finset.sum_add_distrib, hxp, hxn]
      ring
    have hvary : (∑ i, |(e i).2|) = 2 * h := by
      have hi (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
        rcases le_total 0 x with hx | hx <;> simp [abs_of_nonneg, abs_of_nonpos, hx,
          max_eq_left, max_eq_right, neg_nonpos, neg_nonneg]
      simp_rw [hi]
      rw [Finset.sum_add_distrib, hyp, hyn]
      ring
    refine ⟨Q, ?_, ?_, ?_⟩
    · intro A
      have ht : 2 * mixedArea volume A (triangleSum e) =
          (∑ i, SupportGeometry.support (A : Set Plane) (normal (e i))) +
            h * width A + w * height A := by
        rw [triangleSum, mixedArea_sum_right, Finset.mul_sum]
        simp_rw [triangleFromEdge_mixedArea]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hx := support_sum_balanced A (fun i => -(e i).2) (0, 1) h hyn
          (by simpa using hyp)
        have hy := support_sum_balanced A (fun i => -(e i).1) (1, 0) w hxn
          (by simpa using hxp)
        have heX (i : ι) : (-(e i).2) • ((0, 1) : Plane) = (0, -(e i).2) := by ext <;> simp
        have heY (i : ι) : (-(e i).1) • ((1, 0) : Plane) = (-(e i).1, 0) := by ext <;> simp
        simp only [heX, Prod.neg_mk, neg_zero, support_axisX_sum] at hx
        simp only [heY, Prod.neg_mk, neg_zero, support_axisY_sum] at hy
        rw [hx, hy]
      rw [hbody, mixedArea_add_right, mixedArea_add_right] at ht
      nlinarith [rightTriangle_axisX_mixedArea A hw, rightTriangle_axisY_mixedArea A hh]
    · have ht := triangleSum_width e
      rw [hbody, width_add, width_add, rightTriangle_width, rightTriangle_width,
        abs_zero, abs_of_nonneg hw, hvarx] at ht
      linarith
    · have ht := triangleSum_height e
      rw [hbody, height_add, height_add, rightTriangle_height, rightTriangle_height,
        abs_zero, abs_of_nonneg hh, hvary] at ht
      linarith

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BalancedEdgeBody.lean -/

/- BEGIN SOURCE: VolumePolynomials/ExponentialKernel.lean -/
section


@[expose] public section

/-!
# A Hilbert-space realization of the corner-energy kernel

The feature function `1_{t ≤ x} exp ((t-x)/2)` is an actual element of real L².
Its inner product with the feature at `y` is exactly `exp (-|x-y|/2)`.
This provides positivity and Cauchy–Schwarz for the kernel without assuming
a Fourier-transform formula.
-/

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

noncomputable def cornerKernel (x y : ℝ) : ℝ := Real.exp (-|x - y| / 2)

theorem cornerKernel_of_le {x y : ℝ} (hxy : x ≤ y) :
    cornerKernel x y = Real.exp ((x - y) / 2) := by
  unfold cornerKernel
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  congr 1
  ring

theorem cornerKernel_of_ge {x y : ℝ} (hyx : y ≤ x) :
    cornerKernel x y = Real.exp ((y - x) / 2) := by
  unfold cornerKernel
  rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
  congr 1
  ring

theorem cornerKernel_pos (x y : ℝ) : 0 < cornerKernel x y := Real.exp_pos _

theorem cornerKernel_le_one (x y : ℝ) : cornerKernel x y ≤ 1 := by
  unfold cornerKernel
  apply Real.exp_le_one_iff.mpr
  linarith [abs_nonneg (x - y)]

theorem continuous_cornerKernel (x : ℝ) : Continuous (cornerKernel x) := by
  unfold cornerKernel
  fun_prop

theorem integrable_cornerKernel (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (cornerKernel x) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_cornerKernel x).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  simpa only [Real.norm_eq_abs, abs_of_pos (cornerKernel_pos x y)] using
    cornerKernel_le_one x y

noncomputable def cornerFeatureFn (x : ℝ) : ℝ → ℝ :=
  (Iic x).indicator (fun t => Real.exp ((t - x) / 2))

theorem cornerFeatureFn_sq (x t : ℝ) :
    cornerFeatureFn x t ^ 2 = (Iic x).indicator (fun z => Real.exp (z - x)) t := by
  by_cases ht : t ≤ x
  · simp only [cornerFeatureFn, indicator_of_mem (show t ∈ Iic x from ht)]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · simp [cornerFeatureFn, ht]

theorem cornerFeatureFn_measurable (x : ℝ) : Measurable (cornerFeatureFn x) := by
  apply Measurable.indicator _ measurableSet_Iic
  fun_prop

theorem cornerFeatureFn_memLp (x : ℝ) : MemLp (cornerFeatureFn x) 2 := by
  apply (memLp_two_iff_integrable_sq (cornerFeatureFn_measurable x).aestronglyMeasurable).mpr
  have hi : IntegrableOn (fun t : ℝ => Real.exp (t - x)) (Iic x) := by
    change Integrable (fun t : ℝ => Real.exp (t - x)) (volume.restrict (Iic x))
    apply Integrable.congr ((integrableOn_exp_Iic x).mul_const (Real.exp x)⁻¹)
    exact Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [Real.exp_sub, div_eq_mul_inv]
  simpa only [cornerFeatureFn_sq] using hi.integrable_indicator measurableSet_Iic

noncomputable def cornerFeature (x : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (cornerFeatureFn_memLp x).toLp (cornerFeatureFn x)

theorem cornerFeature_coe (x : ℝ) :
    (cornerFeature x : ℝ → ℝ) =ᵐ[volume] cornerFeatureFn x :=
  (cornerFeatureFn_memLp x).coeFn_toLp

theorem cornerFeatureFn_mul (x y t : ℝ) :
    cornerFeatureFn x t * cornerFeatureFn y t =
      (Iic (min x y)).indicator
        (fun z => Real.exp (-(x + y) / 2) * Real.exp z) t := by
  by_cases hx : t ≤ x <;> by_cases hy : t ≤ y
  · simp only [cornerFeatureFn, indicator_of_mem (show t ∈ Iic x from hx),
      indicator_of_mem (show t ∈ Iic y from hy),
      indicator_of_mem (show t ∈ Iic (min x y) from le_min hx hy)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · have hn : ¬t ≤ min x y := fun h => hy (h.trans (min_le_right _ _))
    simp [cornerFeatureFn, hx, hy, hn]
  · have hn : ¬t ≤ min x y := fun h => hx (h.trans (min_le_left _ _))
    simp [cornerFeatureFn, hx, hy, hn]
  · have hn : ¬t ≤ min x y := fun h => hx (h.trans (min_le_left _ _))
    simp [cornerFeatureFn, hx, hy, hn]

theorem integral_cornerFeatureFn_mul (x y : ℝ) :
    (∫ t : ℝ, cornerFeatureFn x t * cornerFeatureFn y t) = cornerKernel x y := by
  simp_rw [cornerFeatureFn_mul]
  rw [integral_indicator measurableSet_Iic, integral_const_mul, integral_exp_Iic,
    ← Real.exp_add]
  unfold cornerKernel
  congr 1
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · rw [min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring

theorem inner_cornerFeature (x y : ℝ) :
    ⟪cornerFeature x, cornerFeature y⟫_ℝ = cornerKernel x y := by
  rw [L2.inner_def]
  apply Eq.trans _ (integral_cornerFeatureFn_mul x y)
  apply integral_congr_ae
  filter_upwards [cornerFeature_coe x, cornerFeature_coe y] with t hx hy
  simp only [Real.inner_apply, hx, hy]

theorem norm_cornerFeature (x : ℝ) : ‖cornerFeature x‖ = 1 := by
  have hsquare : ‖cornerFeature x‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_cornerFeature]
    simp [cornerKernel]
  nlinarith [norm_nonneg (cornerFeature x)]

theorem norm_sub_cornerFeature (x y : ℝ) :
    ‖cornerFeature x - cornerFeature y‖ =
      Real.sqrt (2 - 2 * cornerKernel x y) := by
  rw [← Real.sqrt_sq (norm_nonneg (cornerFeature x - cornerFeature y)),
    norm_sub_sq_real, norm_cornerFeature, norm_cornerFeature, inner_cornerFeature]
  congr 1
  ring

theorem continuous_cornerFeature : Continuous cornerFeature := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [norm_sub_cornerFeature]
  have hcont : Continuous (fun y : ℝ => Real.sqrt (2 - 2 * cornerKernel y x)) := by
    unfold cornerKernel
    fun_prop
  simpa [cornerKernel] using hcont.tendsto x

theorem integrable_cornerFeature (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable cornerFeature μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    continuous_cornerFeature.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (norm_cornerFeature x).le

noncomputable def cornerMean (μ : Measure ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  ∫ x, cornerFeature x ∂μ

theorem inner_cornerFeature_mean (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    ⟪cornerFeature x, cornerMean μ⟫_ℝ = ∫ y, cornerKernel x y ∂μ := by
  rw [cornerMean, ← integral_inner (integrable_cornerFeature μ)]
  simp_rw [inner_cornerFeature]

/-- The nonnegative Hilbert energy is the actual double integral of the kernel. -/
theorem norm_cornerMean_sq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖cornerMean μ‖ ^ 2 = ∫ x, ∫ y, cornerKernel x y ∂μ ∂μ := by
  rw [← real_inner_self_eq_norm_sq, cornerMean, ← integral_inner (integrable_cornerFeature μ)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [real_inner_comm]
  exact inner_cornerFeature_mean μ x

end VolumePolynomials
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ExponentialKernel.lean -/

/- BEGIN SOURCE: VolumePolynomials/SlopeAtomKernel.lean -/
section


@[expose] public section

/-! # Exact weighted exponential kernels for arbitrary nonnegative atom data -/

noncomputable section

namespace VolumePolynomials.HalfZonotope

theorem exponential_half_log_sq {q : ℝ} (hq : 0 < q) :
    Real.exp (Real.log q / 2) ^ 2 = q := by
  first
  | rw [pow_two, ← Real.exp_add]
    have h : Real.log q / 2 + Real.log q / 2 = Real.log q := by ring
    rw [h, Real.exp_log hq]

theorem atom_exponential_moments {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) * Real.exp (-Real.log (b / a) / 2) = a ∧
      Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2) = b := by
  first
  | have hab : 0 ≤ a * b := (mul_pos ha hb).le
    have hplus : Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2) = b := by
      have hsquare : (Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2)) ^ 2 = b ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hab, exponential_half_log_sq (div_pos hb ha)]
        field_simp [ha.ne']
      have hnonneg := mul_nonneg (Real.sqrt_nonneg (a * b))
        (Real.exp_pos (Real.log (b / a) / 2)).le
      nlinarith
    refine ⟨?_, hplus⟩
    have hproduct :
        (Real.sqrt (a * b) * Real.exp (-Real.log (b / a) / 2)) *
          (Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2)) = a * b := by
      calc
        _ = Real.sqrt (a * b) ^ 2 *
            Real.exp (-Real.log (b / a) / 2 + Real.log (b / a) / 2) := by
          rw [Real.exp_add]
          ring
        _ = a * b := by
          rw [Real.sq_sqrt hab,
            show -Real.log (b / a) / 2 + Real.log (b / a) / 2 = 0 by ring,
            Real.exp_zero, mul_one]
    rw [hplus] at hproduct
    exact mul_right_cancel₀ hb.ne' hproduct

theorem weighted_cornerKernel_of_positive {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.sqrt (a * b) * Real.sqrt (c * d) *
        cornerKernel (Real.log (b / a)) (Real.log (d / c)) = min (a * d) (c * b) := by
  first
  | have hm := atom_exponential_moments ha hb
    have hn := atom_exponential_moments hc hd
    rcases le_total (Real.log (b / a)) (Real.log (d / c)) with hxy | hyx
    · have hratio : b / a ≤ d / c := by
        simpa only [Real.exp_log (div_pos hb ha), Real.exp_log (div_pos hd hc)] using
          Real.exp_le_exp.mpr hxy
      have hmin : c * b ≤ a * d := by
        have h := (div_le_div_iff₀ ha hc).mp hratio
        nlinarith
      rw [min_eq_right hmin, cornerKernel_of_le hxy]
      have he : Real.exp ((Real.log (b / a) - Real.log (d / c)) / 2) =
          Real.exp (Real.log (b / a) / 2) * Real.exp (-Real.log (d / c) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2)) *
            (Real.sqrt (c * d) * Real.exp (-Real.log (d / c) / 2)) := by
          rw [he]
          ring
        _ = c * b := by rw [hm.2, hn.1]; ring
    · have hratio : d / c ≤ b / a := by
        simpa only [Real.exp_log (div_pos hd hc), Real.exp_log (div_pos hb ha)] using
          Real.exp_le_exp.mpr hyx
      have hmin : a * d ≤ c * b := by
        have h := (div_le_div_iff₀ hc ha).mp hratio
        nlinarith
      rw [min_eq_left hmin, cornerKernel_of_ge hyx]
      have he : Real.exp ((Real.log (d / c) - Real.log (b / a)) / 2) =
          Real.exp (-Real.log (b / a) / 2) * Real.exp (Real.log (d / c) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.sqrt (a * b) * Real.exp (-Real.log (b / a) / 2)) *
            (Real.sqrt (c * d) * Real.exp (Real.log (d / c) / 2)) := by
          rw [he]
          ring
        _ = a * d := by rw [hm.1, hn.2]

theorem weighted_cornerKernel {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) * Real.sqrt (c * d) *
        cornerKernel (Real.log (b / a)) (Real.log (d / c)) = min (a * d) (c * b) := by
  first
  | by_cases ha0 : a = 0
    · subst a
      simp [mul_nonneg hc hb]
    by_cases hb0 : b = 0
    · subst b
      simp [mul_nonneg ha hd]
    by_cases hc0 : c = 0
    · subst c
      simp [mul_nonneg ha hd]
    by_cases hd0 : d = 0
    · subst d
      simp [mul_nonneg hc hb]
    exact weighted_cornerKernel_of_positive (lt_of_le_of_ne ha (Ne.symm ha0))
      (lt_of_le_of_ne hb (Ne.symm hb0)) (lt_of_le_of_ne hc (Ne.symm hc0))
      (lt_of_le_of_ne hd (Ne.symm hd0))

end VolumePolynomials.HalfZonotope
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SlopeAtomKernel.lean -/

/- BEGIN SOURCE: VolumePolynomials/KernelTestMeasure.lean -/
section


@[expose] public section

/-! # Exact test potential and its energy, equation (5.1) -/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem integral_exp_half_sub (a b x : ℝ) :
    (∫ t in a..b, Real.exp ((t - x) / 2)) =
      2 * (Real.exp ((b - x) / 2) - Real.exp ((a - x) / 2)) := by
  simp_rw [sub_div]
  rw [intervalIntegral.integral_comp_div_sub Real.exp (by norm_num : (2 : ℝ) ≠ 0),
    integral_exp]
  rfl

theorem integral_exp_sub_half (a b x : ℝ) :
    (∫ t in a..b, Real.exp ((x - t) / 2)) =
      2 * (Real.exp ((x - a) / 2) - Real.exp ((x - b) / 2)) := by
  simp_rw [sub_div]
  rw [intervalIntegral.integral_comp_sub_div Real.exp (by norm_num : (2 : ℝ) ≠ 0),
    integral_exp]
  rfl

theorem integral_cornerKernel_left {a b x : ℝ} (hab : a ≤ b) (hbx : b ≤ x) :
    (∫ t in a..b, cornerKernel x t) =
      2 * (Real.exp ((b - x) / 2) - Real.exp ((a - x) / 2)) := by
  rw [← integral_exp_half_sub a b x]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact cornerKernel_of_ge (ht.2.trans hbx)

theorem integral_cornerKernel_right {a b x : ℝ} (hab : a ≤ b) (hxa : x ≤ a) :
    (∫ t in a..b, cornerKernel x t) =
      2 * (Real.exp ((x - a) / 2) - Real.exp ((x - b) / 2)) := by
  rw [← integral_exp_sub_half a b x]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact cornerKernel_of_le (hxa.trans ht.1)

noncomputable def cornerTestPotential (R x : ℝ) : ℝ :=
  (1 / 4) * (∫ t in -R..R, cornerKernel x t) +
    (1 / 2) * (cornerKernel x (-R) + cornerKernel x R)

theorem cornerTestPotential_inside {R x : ℝ} (hRx : -R ≤ x) (hxR : x ≤ R) :
    cornerTestPotential R x = 1 := by
  have hleft : IntervalIntegrable (cornerKernel x) volume (-R) x :=
    (continuous_cornerKernel x).intervalIntegrable (-R) x
  have hright : IntervalIntegrable (cornerKernel x) volume x R :=
    (continuous_cornerKernel x).intervalIntegrable x R
  unfold cornerTestPotential
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    integral_cornerKernel_left hRx le_rfl,
    integral_cornerKernel_right hxR le_rfl,
    cornerKernel_of_ge hRx, cornerKernel_of_le hxR]
  simp only [sub_self, zero_div, Real.exp_zero]
  ring

theorem cornerTestPotential_right {R x : ℝ} (hR : 0 ≤ R) (hx : R ≤ x) :
    cornerTestPotential R x = Real.exp (-(|x| - R) / 2) := by
  have hnegR : -R ≤ R := by linarith
  unfold cornerTestPotential
  rw [integral_cornerKernel_left hnegR hx,
    cornerKernel_of_ge (hnegR.trans hx), cornerKernel_of_ge hx,
    abs_of_nonneg (hR.trans hx)]
  have heq : -(x - R) / 2 = (R - x) / 2 := by ring
  rw [heq]
  ring

theorem cornerTestPotential_left {R x : ℝ} (hR : 0 ≤ R) (hx : x ≤ -R) :
    cornerTestPotential R x = Real.exp (-(|x| - R) / 2) := by
  have hnegR : -R ≤ R := by linarith
  unfold cornerTestPotential
  rw [integral_cornerKernel_right hnegR hx,
    cornerKernel_of_le hx, cornerKernel_of_le (hx.trans hnegR),
    abs_of_nonpos (hx.trans (by linarith : -R ≤ 0))]
  have heq : -(-x - R) / 2 = (x - -R) / 2 := by ring
  rw [heq]
  ring

theorem cornerTestPotential_eq {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    cornerTestPotential R x =
      if |x| ≤ R then 1 else Real.exp (-(|x| - R) / 2) := by
  by_cases hx : |x| ≤ R
  · rw [ite_eq_left hx]
    exact cornerTestPotential_inside (abs_le.mp hx).1 (abs_le.mp hx).2
  · rw [ite_eq_right hx]
    by_cases hxr : R ≤ x
    · exact cornerTestPotential_right hR hxr
    · apply cornerTestPotential_left hR
      by_contra hn
      exact hx (abs_lt.mpr ⟨lt_of_not_ge hn, lt_of_not_ge hxr⟩).le

theorem cornerTestPotential_eq_exp_max {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    cornerTestPotential R x = Real.exp (-max (|x| - R) 0 / 2) := by
  rw [cornerTestPotential_eq hR]
  split_ifs with hx
  · rw [max_eq_right (sub_nonpos.mpr hx)]
    simp
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hx))]

theorem continuous_cornerTestPotential {R : ℝ} (hR : 0 ≤ R) :
    Continuous (cornerTestPotential R) := by
  have heq := funext (cornerTestPotential_eq_exp_max hR)
  rw [heq]
  fun_prop

theorem cornerTestPotential_pos {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    0 < cornerTestPotential R x := by
  rw [cornerTestPotential_eq_exp_max hR]
  exact Real.exp_pos _

theorem cornerTestPotential_le_one {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    cornerTestPotential R x ≤ 1 := by
  rw [cornerTestPotential_eq_exp_max hR]
  apply Real.exp_le_one_iff.mpr
  linarith [le_max_right (|x| - R) 0]

theorem integrable_cornerTestPotential {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (cornerTestPotential R) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_cornerTestPotential hR).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs, abs_of_pos (cornerTestPotential_pos hR x)] using
    cornerTestPotential_le_one hR x

/-- The measure used literally in equation (5.1). -/
noncomputable def cornerTestMeasure (R : ℝ) : Measure ℝ :=
  (1 / 4 : ℝ≥0) • volume.restrict (Icc (-R) R) +
    (1 / 2 : ℝ≥0) • Measure.dirac (-R) +
    (1 / 2 : ℝ≥0) • Measure.dirac R

instance cornerTestMeasure_finite (R : ℝ) : IsFiniteMeasure (cornerTestMeasure R) := by
  unfold cornerTestMeasure
  infer_instance

theorem integral_cornerTestMeasure {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    (∫ y, cornerKernel x y ∂cornerTestMeasure R) = cornerTestPotential R x := by
  unfold cornerTestMeasure
  rw [integral_add_measure, integral_add_measure]
  · rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_dirac, integral_dirac, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    norm_num [cornerTestPotential, NNReal.smul_def, smul_eq_mul]
    ring
  all_goals exact integrable_cornerKernel _ x

theorem integral_cornerTestPotential {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, cornerTestPotential R x ∂cornerTestMeasure R) = 1 + R / 2 := by
  have hinterval : (∫ x in Icc (-R) R, cornerTestPotential R x) = 2 * R := by
    calc
      _ = ∫ _x in Icc (-R) R, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact cornerTestPotential_inside hx.1 hx.2
      _ = 2 * R := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
  unfold cornerTestMeasure
  rw [integral_add_measure, integral_add_measure]
  · rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_dirac, integral_dirac, hinterval,
      cornerTestPotential_inside le_rfl (by linarith : -R ≤ R),
      cornerTestPotential_inside (by linarith : -R ≤ R) le_rfl]
    norm_num [NNReal.smul_def, smul_eq_mul]
    ring
  all_goals exact integrable_cornerTestPotential hR _

/-- The exact energy of the actual positive test measure. -/
theorem norm_cornerMean_test_sq {R : ℝ} (hR : 0 ≤ R) :
    ‖cornerMean (cornerTestMeasure R)‖ ^ 2 = 1 + R / 2 := by
  rw [norm_cornerMean_sq]
  simp_rw [integral_cornerTestMeasure hR]
  exact integral_cornerTestPotential hR

end VolumePolynomials
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/KernelTestMeasure.lean -/

/- BEGIN SOURCE: VolumePolynomials/SignedKernelEnergy.lean -/
section


@[expose] public section

/-!
# Kernel energy for every finite real signed measure

Integration is the difference of the integrals against the two actual Jordan
parts. The energy is the corresponding double integral of the exponential
kernel, and is proved equal to a squared Hilbert norm. No positive-definiteness
or energy Cauchy–Schwarz assertion is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

noncomputable def signedRealIntegral (ν : SignedMeasure ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x, f x ∂ν.toJordanDecomposition.posPart) -
    ∫ x, f x ∂ν.toJordanDecomposition.negPart

/-- Agreement with Mathlib's signed-measure integral on its full integrable domain. -/
theorem signedRealIntegral_eq_vectorIntegral (ν : SignedMeasure ℝ) (f : ℝ → ℝ)
    (hp : Integrable f ν.toJordanDecomposition.posPart)
    (hn : Integrable f ν.toJordanDecomposition.negPart) :
    signedRealIntegral ν f = ∫ᵛ x, f x ∂<•ν := by
  have hp' : ν.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hp
  have hn' : ν.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hn
  conv_rhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.integral_sub_vectorMeasure hp' hn',
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
  rfl

noncomputable def cornerSignedMean (ν : SignedMeasure ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  cornerMean ν.toJordanDecomposition.posPart - cornerMean ν.toJordanDecomposition.negPart

/-- The genuine double kernel integral against the signed measure. -/
noncomputable def cornerSignedEnergy (ν : SignedMeasure ℝ) : ℝ :=
  signedRealIntegral ν (fun x => signedRealIntegral ν (cornerKernel x))

theorem signedRealIntegral_const_one (ν : SignedMeasure ℝ) :
    signedRealIntegral ν (fun _ => 1) = ν univ := by
  rw [ν.apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ]
  simp only [signedRealIntegral, integral_const, smul_eq_mul, mul_one]

theorem inner_cornerFeature_signedMean (ν : SignedMeasure ℝ) (x : ℝ) :
    ⟪cornerFeature x, cornerSignedMean ν⟫_ℝ = signedRealIntegral ν (cornerKernel x) := by
  simp only [cornerSignedMean, inner_sub_right, inner_cornerFeature_mean, signedRealIntegral]

theorem signedRealIntegral_inner_cornerFeature (ν : SignedMeasure ℝ)
    (u : Lp ℝ 2 (volume : Measure ℝ)) :
    signedRealIntegral ν (fun x => ⟪cornerFeature x, u⟫_ℝ) =
      ⟪cornerSignedMean ν, u⟫_ℝ := by
  have hf : (fun x => ⟪cornerFeature x, u⟫_ℝ) =
      (fun x => ⟪u, cornerFeature x⟫_ℝ) :=
    funext (fun x => (real_inner_comm (cornerFeature x) u).symm)
  rw [hf, signedRealIntegral, integral_inner (integrable_cornerFeature _),
    integral_inner (integrable_cornerFeature _)]
  change ⟪u, cornerMean ν.toJordanDecomposition.posPart⟫_ℝ -
      ⟪u, cornerMean ν.toJordanDecomposition.negPart⟫_ℝ =
    ⟪cornerMean ν.toJordanDecomposition.posPart - cornerMean ν.toJordanDecomposition.negPart, u⟫_ℝ
  rw [inner_sub_left, real_inner_comm u (cornerMean ν.toJordanDecomposition.posPart),
    real_inner_comm u (cornerMean ν.toJordanDecomposition.negPart)]

theorem cornerSignedEnergy_eq_norm_sq (ν : SignedMeasure ℝ) :
    cornerSignedEnergy ν = ‖cornerSignedMean ν‖ ^ 2 := by
  unfold cornerSignedEnergy
  simp_rw [← inner_cornerFeature_signedMean]
  rw [signedRealIntegral_inner_cornerFeature, real_inner_self_eq_norm_sq]

/-- The energy agrees with the iterated signed-measure integral in the paper. -/
theorem cornerSignedEnergy_eq_double_vectorIntegral (ν : SignedMeasure ℝ) :
    cornerSignedEnergy ν = ∫ᵛ x, (∫ᵛ y, cornerKernel x y ∂<•ν) ∂<•ν := by
  have hint (μ : Measure ℝ) [IsFiniteMeasure μ] :
      Integrable (fun x => signedRealIntegral ν (cornerKernel x)) μ := by
    simp_rw [← inner_cornerFeature_signedMean]
    exact (integrable_cornerFeature μ).inner_const (cornerSignedMean ν)
  rw [cornerSignedEnergy,
    signedRealIntegral_eq_vectorIntegral ν _ (hint _) (hint _)]
  apply VectorMeasure.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact signedRealIntegral_eq_vectorIntegral ν (cornerKernel x)
    (integrable_cornerKernel _ x) (integrable_cornerKernel _ x)

theorem cornerSignedEnergy_nonneg (ν : SignedMeasure ℝ) : 0 ≤ cornerSignedEnergy ν := by
  rw [cornerSignedEnergy_eq_norm_sq]
  exact sq_nonneg _

theorem inner_cornerSignedMean_test {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ) :
    ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ =
      signedRealIntegral ν (cornerTestPotential R) := by
  rw [← signedRealIntegral_inner_cornerFeature]
  simp_rw [inner_cornerFeature_mean, integral_cornerTestMeasure hR]

theorem cornerTestPotential_error_nonneg {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    0 ≤ 1 - cornerTestPotential R x := sub_nonneg.mpr (cornerTestPotential_le_one hR x)

theorem cornerTestPotential_error_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    1 - cornerTestPotential R x ≤ Real.exp (-R / 2) * Real.exp (|x| / 2) := by
  rw [← Real.exp_add]
  have hexponent : -R / 2 + |x| / 2 = (|x| - R) / 2 := by ring
  rw [hexponent, cornerTestPotential_eq hR]
  split_ifs with hx
  · simpa using (Real.exp_pos ((|x| - R) / 2)).le
  · have hnonneg : 0 ≤ (|x| - R) / 2 := by linarith [le_of_not_ge hx]
    have hle : 1 ≤ Real.exp ((|x| - R) / 2) := Real.one_le_exp_iff.mpr hnonneg
    linarith [Real.exp_pos (-(|x| - R) / 2)]

theorem integrable_cornerTestPotential_error {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x => 1 - cornerTestPotential R x) μ :=
  (integrable_const 1).sub (integrable_cornerTestPotential hR μ)

theorem signedRealIntegral_test_error {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ) :
    ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ =
      signedRealIntegral ν (fun x => 1 - cornerTestPotential R x) := by
  rw [inner_cornerSignedMean_test hR, ← signedRealIntegral_const_one ν]
  simp only [signedRealIntegral,
    integral_sub (integrable_const 1) (integrable_cornerTestPotential hR _)]
  ring

/-- The signed testing error is controlled by the actual exponential moment of
the total variation. Integrability is stated explicitly to avoid Bochner's
zero value on nonintegrable functions. -/
theorem signed_test_error_bound {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4) :
    |ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ| ≤
      4 * Real.exp (-R / 2) := by
  rw [signedRealIntegral_test_error hR]
  have hp : 0 ≤ ∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.posPart :=
    integral_nonneg (cornerTestPotential_error_nonneg hR)
  have hn : 0 ≤ ∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.negPart :=
    integral_nonneg (cornerTestPotential_error_nonneg hR)
  calc
    |signedRealIntegral ν (fun x => 1 - cornerTestPotential R x)|
        ≤ (∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.posPart) +
          ∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.negPart := by
      unfold signedRealIntegral
      apply abs_le.mpr
      constructor <;> linarith
    _ = ∫ x, (1 - cornerTestPotential R x) ∂ν.totalVariation := by
      rw [SignedMeasure.totalVariation,
        integral_add_measure (integrable_cornerTestPotential_error hR _)
          (integrable_cornerTestPotential_error hR _)]
    _ ≤ Real.exp (-R / 2) * ∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation := by
      rw [← integral_const_mul]
      apply integral_mono (integrable_cornerTestPotential_error hR _)
        (hInt.const_mul _)
      exact cornerTestPotential_error_le hR
    _ ≤ 4 * Real.exp (-R / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hMoment (Real.exp_pos (-R / 2)).le]

/-- The complete testing estimate in the first line of the proof of Lemma5.1. -/
theorem signed_mass_test_bound {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4) :
    |ν univ| ≤ ‖cornerSignedMean ν‖ * ‖cornerMean (cornerTestMeasure R)‖ +
      4 * Real.exp (-R / 2) := by
  have herror := signed_test_error_bound hR ν hInt hMoment
  have hCS := abs_real_inner_le_norm (cornerSignedMean ν) (cornerMean (cornerTestMeasure R))
  have htriangle := abs_add_le
    ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ
    (ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ)
  have hsum : ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ +
      (ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ) = ν univ := by
    ring
  rw [hsum] at htriangle
  linarith

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SignedKernelEnergy.lean -/

/- BEGIN SOURCE: VolumePolynomials/ExponentialFourier.lean -/
section
/-
Adapted from the three exact TauCeti sources recorded in
`audit/tauceti-exponential-fourier-provenance.json`, commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362.
Copyright (c) 2026 The Tau Ceti contributors.
Released under Apache 2.0; see audit/TauCeti-LICENSE.
-/


@[expose] public section

/-!
# The complete two-sided exponential Fourier pair

Only the four supporting theorems needed for the actual Cauchy spectral measure
are included. Their proofs are adapted without mathematical changes from the
recorded upstream sources. Compilation status is recorded separately in the audit.
-/

open MeasureTheory Set
open scoped FourierTransform Real

namespace VolumePolynomials

theorem integrable_comp_abs {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntegrableOn f (Set.Ioi 0)) : Integrable fun x : ℝ => f |x| := by
  have hIoi : IntegrableOn (fun x : ℝ => f |x|) (Set.Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have hIic : IntegrableOn (fun x : ℝ => f |x|) (Set.Iic 0) := by
    have hIoi' : IntegrableOn (fun x : ℝ => f |x|) (Set.Ioi (-(0 : ℝ))) := by
      simpa only [neg_zero] using hIoi
    have hIio : IntegrableOn (fun x : ℝ => f |-x|) (Set.Iio 0) :=
      hIoi'.comp_neg_Iio (μ := volume) (c := 0)
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    simpa only [abs_neg] using hIio
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  simpa only [neg_mul] using integrable_comp_abs
    (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)

variable {a : ℝ}

/-- **The Lorentzian pairing of the two-sided exponential with a complex oscillation.** -/
theorem integral_exp_mul_I_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      = ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  -- Rewrite the integrand as a single complex exponential on each half-line.
  have hre₁ : ((a : ℂ) + b * Complex.I).re = a := by simp
  have hre₂ : (-(a : ℂ) + b * Complex.I).re = -a := by simp
  have key : ∀ c x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (c * x) : ℂ)
      = Complex.exp (((c : ℂ) + b * Complex.I) * x) := by
    intro c x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp (((a : ℂ) + b * Complex.I) * x)) (Iic 0) := by
    intro x hx
    have hxa : -(a * |x|) = a * x := by rw [abs_of_nonpos (mem_Iic.mp hx)]; ring
    simpa only [hxa] using key a x
  have hp : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp ((-(a : ℂ) + b * Complex.I) * x)) (Ioi 0) := by
    intro x hx
    have hxa : -(a * |x|) = -a * x := by rw [abs_of_pos (mem_Ioi.mp hx)]; ring
    simpa only [hxa, Complex.ofReal_neg] using key (-a) x
  -- Integrability comes from the real two-sided exponential, since the oscillation has norm one.
  have hint : Integrable
      (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      := ((integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) (by fun_prop)
        (.of_forall fun x ↦ by simp [Complex.norm_exp])
  have hne₁ : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₁
    exact ha.ne' (by simpa using hre₁.symm)
  have hne₂ : -(a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₂
    simp only [Complex.zero_re] at hre₂
    exact ha.ne' (by linarith)
  have hsq : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
  -- Evaluate the two half-line integrals and combine the resulting rational functions.
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    setIntegral_congr_fun measurableSet_Iic hm, setIntegral_congr_fun measurableSet_Ioi hp,
    integral_exp_mul_complex_Iic (by rw [hre₁]; exact ha),
    integral_exp_mul_complex_Ioi (by rw [hre₂]; linarith)]
  have hprod : ((a : ℂ) + b * Complex.I) * (-(a : ℂ) + b * Complex.I)
      = -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
    linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have hdenom : ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : ((a ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
    push_cast at this
    exact this
  rw [Complex.ofReal_div]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (-2 * (a : ℂ)) * hprod

/-- **The Fourier transform of the two-sided exponential.** With Mathlib's normalisation
`𝓕 f ξ = ∫ x, exp (-2 π i x ξ) f x`, the transform of `x ↦ exp (-(a * |x|))` is the Lorentzian
`2 * a / (a ^ 2 + (2 * π * ξ) ^ 2)`. -/
theorem fourier_exp_neg_mul_abs (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (Real.exp (-(a * |x|)) : ℂ)) ξ
      = ((2 * a / (a ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  -- Unfold the real inner product and scalar action to match the oscillatory-integral lemma.
  calc
    _ = ∫ x : ℝ, Complex.exp (((-(2 * π * ξ) : ℝ) : ℂ) * x * Complex.I) *
        (Real.exp (-(a * |x|)) : ℂ) := integral_congr_ae (.of_forall fun x ↦ by
      change Complex.exp ((↑(-2 * π * (inner ℝ x ξ : ℝ)) * Complex.I)) •
        (Real.exp (-(a * |x|)) : ℂ) = _
      rw [smul_eq_mul]
      congr 2
      push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring)
    _ = _ := by
      rw [integral_exp_mul_I_mul_exp_neg_mul_abs ha]
      norm_num

end VolumePolynomials
end -- closes the original EOF section from source line 18
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ExponentialFourier.lean -/

/- BEGIN SOURCE: VolumePolynomials/CauchySpectralMeasure.lean -/
section
/-
The two Fourier-pair proofs below are adapted from
TauCeti/Probability/Distributions/Cauchy/Basic.lean, commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362, lines 381–417.
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc.
Released under the Apache 2.0 license; see audit/TauCeti-LICENSE.
-/


@[expose] public section

/-!
# The actual probability measure in the corner Fourier representation

The spectral measure is Mathlib's Cauchy probability measure with location zero
and scale one half. The density and characteristic function are proved, including
all normalizing constants. Fourier inversion is a theorem of the pinned Mathlib.
-/

open MeasureTheory ProbabilityTheory Set
open scoped FourierTransform Real ENNReal NNReal

namespace VolumePolynomials

theorem fourier_exponential_eq_cauchy_density {γ : ℝ≥0} (hγ : γ ≠ 0) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) ξ =
      (cauchyPDFReal 0 γ ξ : ℂ) := by
  have hγ' : (0 : ℝ) < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have ha : (0 : ℝ) < 2 * Real.pi * γ := mul_pos (by positivity) hγ'
  rw [fourier_exp_neg_mul_abs ha, Complex.ofReal_inj, cauchyPDFReal_def]
  field_simp
  ring

theorem integral_character_cauchy_density {γ : ℝ≥0} (hγ : γ ≠ 0) (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((t : ℂ) * x * Complex.I) * (cauchyPDFReal 0 γ x : ℂ)) =
      (Real.exp (-((γ : ℝ) * |t|)) : ℂ) := by
  have hγ' : (0 : ℝ) < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have ha : (0 : ℝ) < 2 * Real.pi * γ := mul_pos hπ hγ'
  have hcont : Continuous (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) := by
    fun_prop
  have hint : Integrable (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) :=
    (integrable_exp_neg_mul_abs ha).ofReal
  have hFf : 𝓕 (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) =
      fun ξ : ℝ => (cauchyPDFReal 0 γ ξ : ℂ) :=
    funext (fourier_exponential_eq_cauchy_density hγ)
  have hintF : Integrable (𝓕 (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ))) := by
    rw [hFf]
    exact (integrable_cauchyPDFReal 0).ofReal
  have hinv := congrFun (hcont.fourierInv_fourier_eq hint hintF) (t / (2 * Real.pi))
  rw [hFf, Real.fourierInv_eq'] at hinv
  have habs : 2 * Real.pi * (γ : ℝ) * |t / (2 * Real.pi)| = (γ : ℝ) * |t| := by
    rw [abs_div, abs_of_pos hπ]
    field_simp
  rw [← habs, ← hinv]
  refine integral_congr_ae (.of_forall fun v => ?_)
  dsimp only
  rw [smul_eq_mul]
  congr 2
  push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  field_simp

/-- The spectral probability measure appearing in equations (4.1) and (4.7). -/
noncomputable def cornerSpectralMeasure : Measure ℝ := cauchyMeasure 0 (1 / 2)

instance : IsProbabilityMeasure cornerSpectralMeasure := by
  unfold cornerSpectralMeasure
  infer_instance

theorem cornerSpectralMeasure_density :
    cornerSpectralMeasure = volume.withDensity
      (fun ξ : ℝ => ENNReal.ofReal (1 / (2 * Real.pi * (ξ ^ 2 + 1 / 4)))) := by
  rw [cornerSpectralMeasure, cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  congr 1
  funext ξ
  unfold cauchyPDF cauchyPDFReal
  congr 1
  norm_num
  field_simp [Real.pi_ne_zero, ne_of_gt (by positivity : 0 < ξ ^ 2 + (1 / 4 : ℝ))]

theorem integral_cornerSpectralMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ x, f x ∂cornerSpectralMeasure) = ∫ x, cauchyPDFReal 0 (1 / 2) x • f x := by
  rw [cornerSpectralMeasure, cauchyMeasure_of_scale_ne_zero 0 (by norm_num),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 (1 / 2))
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos 0 (by norm_num) x).le]

theorem charFun_cornerSpectralMeasure (t : ℝ) :
    charFun cornerSpectralMeasure t = (Real.exp (-|t| / 2) : ℂ) := by
  rw [charFun_apply_real, integral_cornerSpectralMeasure]
  simpa [Complex.real_smul, mul_comm, div_eq_mul_inv] using
    integral_character_cauchy_density (γ := (1 / 2 : ℝ≥0)) (by norm_num) t

end VolumePolynomials
end -- closes the original EOF section from source line 16
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CauchySpectralMeasure.lean -/

/- BEGIN SOURCE: VolumePolynomials/MatrixDeterminantReduction.lean -/
section


@[expose] public section

/-!
# The two-by-two determinant reduction for the fourth moment

All quantities below are the traces and determinant of an actual complex matrix.
The contraction predicate is the usual squared Euclidean norm inequality, and is
proved equivalent to positivity of `1 - Fᴴ * F`. No singular-value data are assumed.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace VolumePolynomials

/-- The usual Euclidean contraction condition, with no choice of matrix norm. -/
def IsEuclideanContraction {m n : Type*} [Fintype m] [Fintype n]
    (F : Matrix m n ℂ) : Prop :=
  ∀ x : n → ℂ, (∑ i, Complex.normSq ((F *ᵥ x) i)) ≤ ∑ j, Complex.normSq (x j)

/-- The contraction predicate is precisely the operator-norm bound for the
associated linear map on the standard Euclidean spaces. -/
theorem isEuclideanContraction_iff_operatorNorm_le_one {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (F : Matrix m n ℂ) :
    IsEuclideanContraction F ↔ ‖F.toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff zero_le_one]
  constructor
  · intro h x
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply,
      Complex.sq_norm] using h (WithLp.ofLp x)
  · intro h x
    have hx := h (WithLp.toLp 2 x)
    rw [one_mul] at hx
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx
    simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply,
      WithLp.ofLp_toLp, Complex.sq_norm] using hsquare

theorem star_dotProduct_self_eq_normSq_sum {n : Type*} [Fintype n] (x : n → ℂ) :
    star x ⬝ᵥ x = ((∑ j, Complex.normSq (x j) : ℝ) : ℂ) := by
  simp only [dotProduct, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Complex.normSq_eq_conj_mul_self.symm

theorem contraction_gram_form {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (F : Matrix m n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((1 - Fᴴ * F) *ᵥ x) =
      (((∑ j, Complex.normSq (x j)) - ∑ i, Complex.normSq ((F *ᵥ x) i) : ℝ) : ℂ) := by
  rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec,
    dotProduct_mulVec, ← star_mulVec, star_dotProduct_self_eq_normSq_sum,
    star_dotProduct_self_eq_normSq_sum, Complex.ofReal_sub]

theorem isEuclideanContraction_iff_posSemidef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (F : Matrix m n ℂ) :
    IsEuclideanContraction F ↔ (1 - Fᴴ * F).PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self F)) ?_
    intro x
    rw [contraction_gram_form]
    exact_mod_cast sub_nonneg.mpr (h x)
  · intro h x
    have hx := h.dotProduct_mulVec_nonneg x
    rw [contraction_gram_form] at hx
    have hx' : 0 ≤ (∑ j, Complex.normSq (x j)) - ∑ i, Complex.normSq ((F *ᵥ x) i) := by
      exact_mod_cast hx
    exact sub_nonneg.mp hx'

/-- The weighted row/column Cauchy--Schwarz argument used for admissible matrices. -/
theorem isEuclideanContraction_of_weighted_entries {m n : Type*}
    [Fintype m] [Fintype n] (F : Matrix m n ℂ) (p q : Matrix m n ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (hq : ∀ i j, 0 ≤ q i j)
    (hentry : ∀ i j, Complex.normSq (F i j) ≤ p i j * q i j)
    (hrow : ∀ i, ∑ j, p i j ≤ 1) (hcol : ∀ j, ∑ i, q i j ≤ 1) :
    IsEuclideanContraction F := by
  classical
  intro x
  have hrowNorm (i : m) :
      Complex.normSq ((F *ᵥ x) i) ≤ ∑ j, q i j * Complex.normSq (x j) := by
    have htri : ‖(F *ᵥ x) i‖ ≤ ∑ j, ‖F i j‖ * ‖x j‖ := by
      simpa only [mulVec, dotProduct, norm_mul] using
        (norm_sum_le (s := Finset.univ) (f := fun j => F i j * x j))
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => ‖F i j‖ * ‖x j‖) (f := fun j => p i j)
      (g := fun j => q i j * Complex.normSq (x j))
      (fun j _ => hp i j)
      (fun j _ => mul_nonneg (hq i j) (Complex.normSq_nonneg _))
      (fun j _ => by
        rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
        nlinarith [mul_le_mul_of_nonneg_right (hentry i j) (Complex.normSq_nonneg (x j))])
    have hsum : 0 ≤ ∑ j, q i j * Complex.normSq (x j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hq i j) (Complex.normSq_nonneg _)
    have hsquare := (sq_le_sq₀ (norm_nonneg ((F *ᵥ x) i))
      (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
    rw [Complex.sq_norm] at hsquare
    exact hsquare.trans (hcs.trans (by simpa using mul_le_mul_of_nonneg_right (hrow i) hsum))
  calc
    (∑ i, Complex.normSq ((F *ᵥ x) i)) ≤ ∑ i, ∑ j, q i j * Complex.normSq (x j) :=
      Finset.sum_le_sum fun i _ => hrowNorm i
    _ = ∑ j, (∑ i, q i j) * Complex.normSq (x j) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ j, Complex.normSq (x j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa using mul_le_mul_of_nonneg_right (hcol j) (Complex.normSq_nonneg (x j))

/-- The pointwise second spectral moment. -/
def matrixSecondTrace (F : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (Fᴴ * F).trace.re

/-- The pointwise fourth spectral moment. -/
def matrixFourthTrace (F : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((Fᴴ * F) * (Fᴴ * F)).trace.re

/-- The pointwise determinant energy. -/
def matrixDeterminantEnergy (F : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Complex.normSq F.det

theorem matrixSecondTrace_eq_sum (F : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace F = ∑ i, ∑ j, Complex.normSq (F i j) := by
  simp [matrixSecondTrace, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re]
  ring

/-- The complex trace is genuinely real; taking its real part loses no data. -/
theorem gram_trace_eq_real (F : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fᴴ * F).trace = (matrixSecondTrace F : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.add_im, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

/-- The fourth-moment trace too has zero imaginary part. -/
theorem gram_square_trace_eq_real (F : Matrix (Fin 2) (Fin 2) ℂ) :
    ((Fᴴ * F) * (Fᴴ * F)).trace = (matrixFourthTrace F : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.add_im, Complex.add_re, Complex.mul_im,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_im]
    ring

theorem matrixSecondTrace_nonneg (F : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ matrixSecondTrace F := by
  rw [matrixSecondTrace_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem matrixFourthTrace_nonneg (F : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ matrixFourthTrace F := by
  simpa only [matrixSecondTrace, matrixFourthTrace, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] using matrixSecondTrace_nonneg (Fᴴ * F)

theorem matrixDeterminantEnergy_nonneg (F : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ matrixDeterminantEnergy F := Complex.normSq_nonneg _

/-- The Cayley--Hamilton trace identity, expanded and checked in actual matrix entries. -/
theorem matrixFourthTrace_eq (F : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixFourthTrace F = matrixSecondTrace F ^ 2 - 2 * matrixDeterminantEnergy F := by
  simp [matrixFourthTrace, matrixSecondTrace, matrixDeterminantEnergy,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.det_fin_two,
    Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem det_one_sub_gram (F : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 - Fᴴ * F).det = ((1 - matrixSecondTrace F + matrixDeterminantEnergy F : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [matrixSecondTrace, matrixDeterminantEnergy, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.det_fin_two, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem contraction_determinant_lower (F : Matrix (Fin 2) (Fin 2) ℂ)
    (hF : IsEuclideanContraction F) :
    matrixSecondTrace F - 1 ≤ matrixDeterminantEnergy F := by
  have h := ((isEuclideanContraction_iff_posSemidef F).mp hF).det_nonneg
  rw [det_one_sub_gram] at h
  have hreal : 0 ≤ 1 - matrixSecondTrace F + matrixDeterminantEnergy F := by exact_mod_cast h
  linarith

theorem matrixDeterminantEnergy_le_column_product (F : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixDeterminantEnergy F ≤
      (Complex.normSq (F 0 0) + Complex.normSq (F 1 0)) *
        (Complex.normSq (F 0 1) + Complex.normSq (F 1 1)) := by
  have h := Complex.normSq_nonneg (star (F 0 0) * F 0 1 + star (F 1 0) * F 1 1)
  simp only [matrixDeterminantEnergy, Matrix.det_fin_two, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im] at *
  nlinarith

theorem contraction_determinant_le_one (F : Matrix (Fin 2) (Fin 2) ℂ)
    (hF : IsEuclideanContraction F) : matrixDeterminantEnergy F ≤ 1 := by
  have h0 := hF ![1, 0]
  have h1 := hF ![0, 1]
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add,
    Complex.normSq_one, Complex.normSq_zero] at h0 h1
  have hnonneg : 0 ≤ Complex.normSq (F 0 1) + Complex.normSq (F 1 1) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact (matrixDeterminantEnergy_le_column_product F).trans (by nlinarith)

/-- Scalar algebra behind the fourth-moment improvement. -/
theorem fourth_moment_scalar_bounds {t d b : ℝ}
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (htb : t ≤ 1 + b) (hdt : t - 1 ≤ d) :
    t ^ 2 - 2 * d ≤ 1 + b * (t - 1) ∧
      (1 - b) * d ≤ t - (t ^ 2 - 2 * d) := by
  constructor
  · by_cases ht1 : t ≤ 1
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (by linarith : 0 ≤ 1 + t - b)]
    · have ht1' : 0 ≤ t - 1 := by linarith
      nlinarith [mul_nonneg ht1' (by linarith : 0 ≤ b - (t - 1))]
  · by_cases ht1 : t ≤ 1
    · nlinarith [mul_nonneg hb hd, mul_nonneg ht (sub_nonneg.mpr ht1)]
    · have ht1' : 0 ≤ t - 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hdt (by linarith : 0 ≤ 1 + b)
      nlinarith [mul_nonneg ht1' (sub_nonneg.mpr htb)]

/-- Pointwise fourth-moment control for an entrywise dominated pair of contractions. -/
theorem matrixFourthTrace_bounds (F M : Matrix (Fin 2) (Fin 2) ℂ)
    (hF : IsEuclideanContraction F) (hM : IsEuclideanContraction M)
    (hdom : ∀ i j, Complex.normSq (F i j) ≤ Complex.normSq (M i j)) :
    matrixFourthTrace F ≤ 1 + matrixDeterminantEnergy M * (matrixSecondTrace F - 1) ∧
      (1 - matrixDeterminantEnergy M) * matrixDeterminantEnergy F ≤
        matrixSecondTrace F - matrixFourthTrace F := by
  have htrace : matrixSecondTrace F ≤ matrixSecondTrace M := by
    simp only [matrixSecondTrace_eq_sum]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hdom i j
  have hbound : matrixSecondTrace F ≤ 1 + matrixDeterminantEnergy M := by
    linarith [contraction_determinant_lower M hM]
  rw [matrixFourthTrace_eq]
  exact fourth_moment_scalar_bounds (matrixSecondTrace_nonneg F)
    (matrixDeterminantEnergy_nonneg F) (matrixDeterminantEnergy_nonneg M)
    (contraction_determinant_le_one M hM) hbound (contraction_determinant_lower F hF)


/-- A small entry energy forces a quantitative gap in its mass fourth power. -/
theorem mass_fourth_le_of_small_energy {m I : ℝ}
    (hmoment : m ^ 4 ≤ I * (2 - I)) (hsmall : I ≤ 3 / 4) :
    m ^ 4 ≤ 15 / 16 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 4 - I)
    (by linarith : 0 ≤ 5 / 4 - I)]

theorem determinant_gap_of_entry {D m I : ℝ} (_hm : 0 ≤ m)
    (hdom : |D| ≤ m) (hmoment : m ^ 4 ≤ I * (2 - I)) (hsmall : I ≤ 3 / 4) :
    D ^ 2 ≤ 31 / 32 := by
  have hpow : |D| ^ 4 ≤ m ^ 4 := pow_le_pow_left₀ (abs_nonneg D) hdom 4
  rw [(by decide : Even (4 : ℕ)).pow_abs] at hpow
  have hm4 := mass_fourth_le_of_small_energy hmoment hsmall
  nlinarith [sq_nonneg (D ^ 2 - 1)]

/-- A rational uniform determinant gap. The hypotheses are precisely the entry
mass/energy consequences of the two exponential moment bounds. -/
theorem nonnegative_mass_matrix_determinant_gap (M I : Matrix (Fin 2) (Fin 2) ℝ)
    (hm0 : ∀ i j, 0 ≤ M i j) (hm1 : ∀ i j, M i j ≤ 1)
    (hI0 : ∀ i j, 0 ≤ I i j)
    (hentry : ∀ i j, M i j ^ 4 ≤ I i j * (2 - I i j))
    (hsmall : (∑ i, ∑ j, I i j) ≤ 3 / 2) :
    M.det ^ 2 ≤ 31 / 32 := by
  have hsum : I 0 0 + I 0 1 + (I 1 0 + I 1 1) ≤ 3 / 2 := by
    simpa only [Fin.sum_univ_two] using hsmall
  by_cases hdiag : M 0 1 * M 1 0 ≤ M 0 0 * M 1 1
  · have hD : 0 ≤ M.det := by rw [Matrix.det_fin_two]; linarith
    have h00 : |M.det| ≤ M 0 0 := by
      rw [abs_of_nonneg hD, Matrix.det_fin_two]
      have hprod := mul_le_mul_of_nonneg_left (hm1 1 1) (hm0 0 0)
      nlinarith [mul_nonneg (hm0 0 1) (hm0 1 0)]
    have h11 : |M.det| ≤ M 1 1 := by
      rw [abs_of_nonneg hD, Matrix.det_fin_two]
      have hprod := mul_le_mul_of_nonneg_right (hm1 0 0) (hm0 1 1)
      nlinarith [mul_nonneg (hm0 0 1) (hm0 1 0)]
    by_cases hI : I 0 0 ≤ 3 / 4
    · exact determinant_gap_of_entry (hm0 0 0) h00 (hentry 0 0) hI
    · exact determinant_gap_of_entry (hm0 1 1) h11 (hentry 1 1)
        (by linarith [hI0 0 1, hI0 1 0])
  · have hD : M.det ≤ 0 := by rw [Matrix.det_fin_two]; linarith
    have h01 : |M.det| ≤ M 0 1 := by
      rw [abs_of_nonpos hD, Matrix.det_fin_two]
      have hprod := mul_le_mul_of_nonneg_left (hm1 1 0) (hm0 0 1)
      nlinarith [mul_nonneg (hm0 0 0) (hm0 1 1)]
    have h10 : |M.det| ≤ M 1 0 := by
      rw [abs_of_nonpos hD, Matrix.det_fin_two]
      have hprod := mul_le_mul_of_nonneg_right (hm1 0 1) (hm0 1 0)
      nlinarith [mul_nonneg (hm0 0 0) (hm0 1 1)]
    by_cases hI : I 0 1 ≤ 3 / 4
    · exact determinant_gap_of_entry (hm0 0 1) h01 (hentry 0 1) hI
    · exact determinant_gap_of_entry (hm0 1 0) h10 (hentry 1 0)
        (by linarith [hI0 0 0, hI0 1 1])

theorem matrixDeterminantEnergy_ofReal (M : Matrix (Fin 2) (Fin 2) ℝ) :
    matrixDeterminantEnergy (M.map Complex.ofReal) = M.det ^ 2 := by
  simp only [matrixDeterminantEnergy, Matrix.det_fin_two, Matrix.map_apply,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.normSq_ofReal, pow_two]

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MatrixDeterminantReduction.lean -/

/- BEGIN SOURCE: VolumePolynomials/SlopeMeasureMoments.lean -/
section


@[expose] public section

/-!
# Exponential moment bounds for arbitrary finite slope measures

Admissibility uses nonnegative Lebesgue integrals. Thus an infinite exponential
moment cannot be mistaken for a vanishing Bochner integral. The real integrals
and the weighted contraction are derived only after integrability is proved.
-/

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators MeasureTheory InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

/-- The exponential moment, with its genuine extended nonnegative value. -/
noncomputable def slopeExponentialMoment (μ : Measure ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (a * x)) ∂μ

theorem slopeExponentialMoment_integrable {μ : Measure ℝ} {a : ℝ}
    (h : slopeExponentialMoment μ a < ∞) :
    Integrable (fun x : ℝ => Real.exp (a * x)) μ := by
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).mpr h⟩

theorem integral_exponential_eq_moment (μ : Measure ℝ) (a : ℝ) :
    (∫ x : ℝ, Real.exp (a * x) ∂μ) = (slopeExponentialMoment μ a).toReal := by
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) (by fun_prop)

theorem integral_exponential_le_one {μ : Measure ℝ} {a : ℝ}
    (h : slopeExponentialMoment μ a ≤ 1) :
    (∫ x : ℝ, Real.exp (a * x) ∂μ) ≤ 1 := by
  rw [integral_exponential_eq_moment]
  simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) h

theorem slopeExponentialMoment_conv (μ ν : Measure ℝ) [SFinite ν] (a : ℝ) :
    slopeExponentialMoment (μ ∗ ν) a =
      slopeExponentialMoment μ a * slopeExponentialMoment ν a := by
  unfold slopeExponentialMoment
  rw [Measure.lintegral_conv (by fun_prop)]
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x))) := by fun_prop
  simp_rw [mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
    lintegral_const_mul _ hm]
  exact lintegral_mul_const _ hm

/-- Squared Cauchy--Schwarz with the actual real integrals. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  let u := hf.toLp f
  let v := hg.toLp g
  have hu : (u : α → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  have hv : (v : α → ℝ) =ᵐ[μ] g := hg.coeFn_toLp
  have hinner : ⟪u, v⟫_ℝ = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, hv] with x hux hvx
    simp [hux, hvx, mul_comm]
  have hnu : ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    simp [hx, pow_two]
  have hnv : ‖v‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx, pow_two]
  have hCS := abs_real_inner_le_norm u v
  have hsquare := (sq_le_sq₀ (abs_nonneg ⟪u, v⟫_ℝ)
    (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mpr hCS
  rw [sq_abs, mul_pow, hinner, hnu, hnv] at hsquare
  exact hsquare

/-- The mass is bounded by the geometric mean of the reciprocal exponential moments. -/
theorem slope_mass_sq_le_moments (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hp : slopeExponentialMoment μ (-1 / 2) < ∞)
    (hq : slopeExponentialMoment μ (1 / 2) < ∞) :
    (μ.real univ) ^ 2 ≤
      (∫ x : ℝ, Real.exp ((-1 / 2) * x) ∂μ) * ∫ x : ℝ, Real.exp ((1 / 2) * x) ∂μ := by
  have hf : MemLp (fun x : ℝ => Real.exp (-x / 4)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    convert slopeExponentialMoment_integrable hp using 1
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hg : MemLp (fun x : ℝ => Real.exp (x / 4)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    convert slopeExponentialMoment_integrable hq using 1
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hprod (x : ℝ) : Real.exp (-x / 4) * Real.exp (x / 4) = 1 := by
    have he : -x / 4 + x / 4 = 0 := by ring
    rw [← Real.exp_add, he, Real.exp_zero]
  have hfsq (x : ℝ) : Real.exp (-x / 4) ^ 2 = Real.exp ((-1 / 2) * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hgsq (x : ℝ) : Real.exp (x / 4) ^ 2 = Real.exp ((1 / 2) * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [hprod, hfsq, hgsq, integral_const, smul_eq_mul, mul_one] using
    integral_mul_sq_le hf hg

/-- The measure-matrix hypothesis in Section 4.2, with its full measure semantics. -/
def IsAdmissibleSlopeMatrix (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : Prop :=
  (∀ i, ∑ j, slopeExponentialMoment (ρ i j) (-1 / 2) ≤ 1) ∧
    (∀ j, ∑ i, slopeExponentialMoment (ρ i j) (1 / 2) ≤ 1)

noncomputable def slopeFourierMatrix (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun i j => charFun (ρ i j) ξ

noncomputable def slopeMassMatrix (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => (ρ i j).real univ

theorem admissible_entry_negative_moment {ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)}
    (hρ : IsAdmissibleSlopeMatrix ρ) (i j : Fin 2) :
    slopeExponentialMoment (ρ i j) (-1 / 2) ≤ 1 :=
  (Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ slopeExponentialMoment (ρ i k) (-1 / 2)))
    (Finset.mem_univ j)).trans (hρ.1 i)

theorem admissible_entry_positive_moment {ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)}
    (hρ : IsAdmissibleSlopeMatrix ρ) (i j : Fin 2) :
    slopeExponentialMoment (ρ i j) (1 / 2) ≤ 1 :=
  (Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ slopeExponentialMoment (ρ k j) (1 / 2)))
    (Finset.mem_univ i)).trans (hρ.2 j)

theorem normSq_slopeFourier_le_mass (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    (ξ : ℝ) (i j : Fin 2) :
    Complex.normSq (slopeFourierMatrix ρ ξ i j) ≤ (slopeMassMatrix ρ i j) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact (sq_le_sq₀ (norm_nonneg _) measureReal_nonneg).mpr (norm_charFun_le ξ)

/-- Lemma 4.2, proved directly for the complete class of admissible finite measures. -/
theorem admissible_fourier_contraction
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (ξ : ℝ) :
    IsEuclideanContraction (slopeFourierMatrix ρ ξ) := by
  let p : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ x : ℝ, Real.exp ((-1 / 2) * x) ∂ρ i j
  let q : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ x : ℝ, Real.exp ((1 / 2) * x) ∂ρ i j
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => integral_nonneg fun x => (Real.exp_pos _).le
  have hq0 : ∀ i j, 0 ≤ q i j := fun i j => integral_nonneg fun x => (Real.exp_pos _).le
  have hrow : ∀ i, ∑ j, p i j ≤ 1 := by
    intro i
    have hfinite : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
        slopeExponentialMoment (ρ i j) (-1 / 2) ≠ ∞ := fun j _ =>
      ((admissible_entry_negative_moment hρ i j).trans_lt (by norm_num)).ne
    have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hρ.1 i)
    simpa only [p, integral_exponential_eq_moment, ENNReal.toReal_sum hfinite,
      ENNReal.toReal_one] using hreal
  have hcol : ∀ j, ∑ i, q i j ≤ 1 := by
    intro j
    have hfinite : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
        slopeExponentialMoment (ρ i j) (1 / 2) ≠ ∞ := fun i _ =>
      ((admissible_entry_positive_moment hρ i j).trans_lt (by norm_num)).ne
    have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hρ.2 j)
    simpa only [q, integral_exponential_eq_moment, ENNReal.toReal_sum hfinite,
      ENNReal.toReal_one] using hreal
  apply isEuclideanContraction_of_weighted_entries _ p q hp0 hq0 _ hrow hcol
  intro i j
  exact (normSq_slopeFourier_le_mass ρ ξ i j).trans
    (slope_mass_sq_le_moments (ρ i j)
      ((admissible_entry_negative_moment hρ i j).trans_lt (by norm_num))
      ((admissible_entry_positive_moment hρ i j).trans_lt (by norm_num)))

/-- The literal operator-norm conclusion of Lemma 4.2. -/
theorem admissible_fourier_operatorNorm_le_one
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (ξ : ℝ) :
    ‖(slopeFourierMatrix ρ ξ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 :=
  (isEuclideanContraction_iff_operatorNorm_le_one _).mp
    (admissible_fourier_contraction ρ hρ ξ)

theorem slopeFourierMatrix_zero (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) :
    slopeFourierMatrix ρ 0 = (slopeMassMatrix ρ).map Complex.ofReal := by
  ext i j
  simp only [slopeFourierMatrix, slopeMassMatrix, Matrix.map_apply, charFun_zero]

theorem admissible_mass_contraction
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    IsEuclideanContraction ((slopeMassMatrix ρ).map Complex.ofReal) := by
  rw [← slopeFourierMatrix_zero]
  exact admissible_fourier_contraction ρ hρ 0

theorem admissible_fourier_domination
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) (ξ : ℝ) (i j : Fin 2) :
    Complex.normSq (slopeFourierMatrix ρ ξ i j) ≤
      Complex.normSq (((slopeMassMatrix ρ).map Complex.ofReal) i j) := by
  simpa only [Matrix.map_apply, Complex.normSq_ofReal, pow_two] using
    normSq_slopeFourier_le_mass ρ ξ i j

/-- The signed determinant measure uses actual additive convolution. -/
noncomputable def slopeDeterminantMeasure
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] : SignedMeasure ℝ :=
  (ρ 0 0 ∗ ρ 1 1).toSignedMeasure - (ρ 0 1 ∗ ρ 1 0).toSignedMeasure

/-- Total variation is bounded by the two positive convolution measures. -/
theorem slopeDeterminantMeasure_totalVariation_le
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] :
    (slopeDeterminantMeasure ρ).totalVariation ≤ (ρ 0 0 ∗ ρ 1 1) + (ρ 0 1 ∗ ρ 1 0) := by
  rw [SignedMeasure.totalVariation_eq_variation]
  simpa only [slopeDeterminantMeasure, Measure.variation_toSignedMeasure] using
    (VectorMeasure.variation_sub_le (μ := (ρ 0 0 ∗ ρ 1 1).toSignedMeasure)
      (ν := (ρ 0 1 ∗ ρ 1 0).toSignedMeasure))

/-- The determinant measure has the exact exponential-moment bound in Lemma 5.1. -/
theorem slopeDeterminantMeasure_exponential_moment
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] (hρ : IsAdmissibleSlopeMatrix ρ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2))
      ∂(slopeDeterminantMeasure ρ).totalVariation) ≤ 4 := by
  have hconv (i j k l : Fin 2) :
      slopeExponentialMoment (ρ i j ∗ ρ k l) (-1 / 2) ≤ 1 ∧
        slopeExponentialMoment (ρ i j ∗ ρ k l) (1 / 2) ≤ 1 := by
    constructor
    · rw [slopeExponentialMoment_conv]
      exact (mul_le_mul' (admissible_entry_negative_moment hρ i j)
        (admissible_entry_negative_moment hρ k l)).trans_eq (one_mul 1)
    · rw [slopeExponentialMoment_conv]
      exact (mul_le_mul' (admissible_entry_positive_moment hρ i j)
        (admissible_entry_positive_moment hρ k l)).trans_eq (one_mul 1)
  have habs (x : ℝ) : Real.exp (|x| / 2) ≤ Real.exp ((-1 / 2) * x) + Real.exp ((1 / 2) * x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have heq : (1 / 2 : ℝ) * x = x / 2 := by ring
      rw [heq]
      linarith [Real.exp_pos ((-1 / 2) * x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have heq : (-1 / 2 : ℝ) * x = -x / 2 := by ring
      rw [heq]
      linarith [Real.exp_pos ((1 / 2) * x)]
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2))
        ∂((ρ 0 0 ∗ ρ 1 1) + (ρ 0 1 ∗ ρ 1 0)) :=
      lintegral_mono' (slopeDeterminantMeasure_totalVariation_le ρ) (fun _ => le_rfl)
    _ ≤ ∫⁻ x : ℝ,
        ENNReal.ofReal (Real.exp ((-1 / 2) * x)) +
          ENNReal.ofReal (Real.exp ((1 / 2) * x))
        ∂((ρ 0 0 ∗ ρ 1 1) + (ρ 0 1 ∗ ρ 1 0)) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      exact ENNReal.ofReal_mono (habs x)
    _ = (slopeExponentialMoment (ρ 0 0 ∗ ρ 1 1) (-1 / 2) +
          slopeExponentialMoment (ρ 0 0 ∗ ρ 1 1) (1 / 2)) +
        (slopeExponentialMoment (ρ 0 1 ∗ ρ 1 0) (-1 / 2) +
          slopeExponentialMoment (ρ 0 1 ∗ ρ 1 0) (1 / 2)) := by
      rw [lintegral_add_measure]
      have hm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp ((-1 / 2) * x))) :=
        by fun_prop
      simp only [lintegral_add_left hm, slopeExponentialMoment]
    _ ≤ (1 + 1) + (1 + 1) := add_le_add
      (add_le_add (hconv 0 0 1 1).1 (hconv 0 0 1 1).2)
      (add_le_add (hconv 0 1 1 0).1 (hconv 0 1 1 0).2)
    _ = 4 := by norm_num

end VolumePolynomials
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SlopeMeasureMoments.lean -/

/- BEGIN SOURCE: VolumePolynomials/KernelFourier.lean -/
section


@[expose] public section

/-!
# The Fourier representation of the actual signed corner energy

This file connects the iterated signed-measure energy to the Cauchy spectral
integral. Fubini is applied to bounded characters on products of finite measures.
The determinant transform is then the actual signed convolution difference.
-/

open MeasureTheory Set Matrix
open scoped ENNReal InnerProductSpace RealInnerProductSpace ComplexConjugate MeasureTheory

namespace VolumePolynomials

theorem integrable_character (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((ξ : ℂ) * x * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_exp]

theorem character_product (ξ x y : ℝ) :
    conj (Complex.exp ((ξ : ℂ) * x * Complex.I)) *
      Complex.exp ((ξ : ℂ) * y * Complex.I) =
        Complex.exp (((y - x : ℝ) : ℂ) * ξ * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

/-- The exact complex bilinear Fourier/kernel identity for two finite positive measures. -/
theorem corner_spectral_pairing (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ ξ : ℝ, conj (charFun μ ξ) * charFun ν ξ ∂cornerSpectralMeasure) =
      Complex.ofReal (∫ x : ℝ, ∫ y : ℝ, cornerKernel x y ∂ν ∂μ) := by
  have hproduct (ξ : ℝ) : conj (charFun μ ξ) * charFun ν ξ =
      ∫ p : ℝ × ℝ, Complex.exp (((p.2 - p.1 : ℝ) : ℂ) * ξ * Complex.I) ∂μ.prod ν := by
    rw [charFun_apply_real, charFun_apply_real, ← integral_conj, ← integral_prod_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => character_product ξ p.1 p.2
  have hint : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      Complex.exp (((p.2.2 - p.2.1 : ℝ) : ℂ) * p.1 * Complex.I))
        (cornerSpectralMeasure.prod (μ.prod ν)) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun p => by simp [Complex.norm_exp]
  simp_rw [hproduct]
  rw [integral_integral_swap hint]
  have hinner (p : ℝ × ℝ) :
      (∫ ξ : ℝ, Complex.exp (((p.2 - p.1 : ℝ) : ℂ) * ξ * Complex.I)
        ∂cornerSpectralMeasure) = (cornerKernel p.1 p.2 : ℂ) := by
    simpa only [charFun_apply_real, cornerKernel, abs_sub_comm] using
      charFun_cornerSpectralMeasure (p.2 - p.1)
  simp_rw [hinner]
  have hK : Integrable (fun p : ℝ × ℝ => cornerKernel p.1 p.2) (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold cornerKernel; fun_prop)
    exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, abs_of_pos (cornerKernel_pos _ _)] using
        cornerKernel_le_one p.1 p.2
  simpa only [integral_complex_ofReal] using
    congrArg Complex.ofReal (integral_prod (fun p : ℝ × ℝ => cornerKernel p.1 p.2) hK)

theorem integrable_spectral_pairing (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun ξ : ℝ => conj (charFun μ ξ) * charFun ν ξ) cornerSpectralMeasure := by
  apply (integrable_const (μ.real univ * ν.real univ)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro ξ
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (norm_charFun_le ξ) (norm_charFun_le ξ) (norm_nonneg _)
    measureReal_nonneg

theorem integrable_real_spectral_pairing (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun ξ : ℝ => (conj (charFun μ ξ) * charFun ν ξ).re)
      cornerSpectralMeasure := by
  exact Complex.reCLM.integrable_comp (integrable_spectral_pairing μ ν)

theorem real_corner_spectral_pairing (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ ξ : ℝ, (conj (charFun μ ξ) * charFun ν ξ).re ∂cornerSpectralMeasure) =
      ∫ x : ℝ, ∫ y : ℝ, cornerKernel x y ∂ν ∂μ := by
  have h := Complex.reCLM.integral_comp_comm (integrable_spectral_pairing μ ν)
  change (∫ ξ : ℝ, (conj (charFun μ ξ) * charFun ν ξ).re ∂cornerSpectralMeasure) =
    (∫ ξ : ℝ, conj (charFun μ ξ) * charFun ν ξ ∂cornerSpectralMeasure).re at h
  rw [h, corner_spectral_pairing]
  rfl

theorem integrable_spectral_normSq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun ξ : ℝ => Complex.normSq (charFun μ ξ)) cornerSpectralMeasure := by
  have h := integrable_real_spectral_pairing μ μ
  simpa only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using h

theorem corner_spectral_energy (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ ξ : ℝ, Complex.normSq (charFun μ ξ) ∂cornerSpectralMeasure) =
      ‖cornerMean μ‖ ^ 2 := by
  rw [norm_cornerMean_sq]
  simpa only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using
    real_corner_spectral_pairing μ μ

theorem inner_cornerMean_mean (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪cornerMean μ, cornerMean ν⟫_ℝ = ∫ x : ℝ, ∫ y : ℝ, cornerKernel x y ∂ν ∂μ := by
  rw [real_inner_comm]
  change ⟪cornerMean ν, ∫ x : ℝ, cornerFeature x ∂μ⟫_ℝ = _
  rw [← integral_inner (integrable_cornerFeature μ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [real_inner_comm, inner_cornerFeature_mean]

theorem complex_normSq_sub_eq (z w : ℂ) :
    Complex.normSq (z - w) = Complex.normSq z - 2 * (conj z * w).re + Complex.normSq w := by
  rw [Complex.normSq_sub]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The energy of a difference uses the actual two positive measures, with no
assumption that they are mutually singular. -/
theorem corner_spectral_difference_energy (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ ξ : ℝ, Complex.normSq (charFun μ ξ - charFun ν ξ) ∂cornerSpectralMeasure) =
      ‖cornerMean μ - cornerMean ν‖ ^ 2 := by
  simp_rw [complex_normSq_sub_eq]
  erw [integral_add ((integrable_spectral_normSq μ).sub
      ((integrable_real_spectral_pairing μ ν).const_mul 2)) (integrable_spectral_normSq ν),
    integral_sub (integrable_spectral_normSq μ)
      ((integrable_real_spectral_pairing μ ν).const_mul 2), integral_const_mul,
    corner_spectral_energy, corner_spectral_energy, real_corner_spectral_pairing,
    norm_sub_sq_real, inner_cornerMean_mean]

/-- Characteristic transform of an actual finite real signed measure. -/
noncomputable def signedSlopeFourier (ν : SignedMeasure ℝ) (ξ : ℝ) : ℂ :=
  ∫ᵛ x : ℝ, Complex.exp ((ξ : ℂ) * x * Complex.I) ∂<•ν

theorem signedSlopeFourier_sub (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    signedSlopeFourier (μ.toSignedMeasure - ν.toSignedMeasure) ξ =
      charFun μ ξ - charFun ν ξ := by
  have hp : μ.toSignedMeasure.Integrable
      (fun x : ℝ => Complex.exp ((ξ : ℂ) * x * Complex.I)) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      integrable_character μ ξ
  have hn : ν.toSignedMeasure.Integrable
      (fun x : ℝ => Complex.exp ((ξ : ℂ) * x * Complex.I)) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      integrable_character ν ξ
  rw [signedSlopeFourier, VectorMeasure.integral_sub_vectorMeasure hp hn,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    charFun_apply_real, charFun_apply_real]

theorem signedSlopeFourier_jordan (ν : SignedMeasure ℝ) (ξ : ℝ) :
    signedSlopeFourier ν ξ = charFun ν.toJordanDecomposition.posPart ξ -
      charFun ν.toJordanDecomposition.negPart ξ := by
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, signedSlopeFourier_sub]

/-- The exact Fourier representation (4.1) for every finite real signed measure. -/
theorem cornerSignedEnergy_eq_spectral (ν : SignedMeasure ℝ) :
    cornerSignedEnergy ν =
      ∫ ξ : ℝ, Complex.normSq (signedSlopeFourier ν ξ) ∂cornerSpectralMeasure := by
  simp_rw [signedSlopeFourier_jordan]
  rw [corner_spectral_difference_energy, cornerSignedEnergy_eq_norm_sq, cornerSignedMean]

/-- Convolution makes the determinant transform an identity, not an assumption. -/
theorem signedSlopeFourier_determinant
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] (ξ : ℝ) :
    signedSlopeFourier (slopeDeterminantMeasure ρ) ξ = (slopeFourierMatrix ρ ξ).det := by
  rw [slopeDeterminantMeasure, signedSlopeFourier_sub, charFun_conv, charFun_conv,
    Matrix.det_fin_two]
  rfl

theorem determinant_measure_energy
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] :
    cornerSignedEnergy (slopeDeterminantMeasure ρ) =
      ∫ ξ : ℝ, matrixDeterminantEnergy (slopeFourierMatrix ρ ξ) ∂cornerSpectralMeasure := by
  rw [cornerSignedEnergy_eq_spectral]
  simp only [signedSlopeFourier_determinant, matrixDeterminantEnergy]

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/KernelFourier.lean -/

/- BEGIN SOURCE: VolumePolynomials/KernelLogMass.lean -/
section


@[expose] public section

/-!
# The logarithmic mass estimate for finite signed measures

This is Lemma5.1 with the explicit absolute constant34. Its energy is the actual
double integral of `exp (-|x-y|/2)` against the signed measure, not an assumed
quadratic form. The proof uses the constructed Hilbert features and the exactly
integrated test measure.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem signed_mass_zero_of_energy_zero (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4)
    (hEnergy : cornerSignedEnergy ν = 0) : ν univ = 0 := by
  have hnorm : ‖cornerSignedMean ν‖ = 0 := by
    rw [cornerSignedEnergy_eq_norm_sq] at hEnergy
    nlinarith [norm_nonneg (cornerSignedMean ν)]
  have hbound : ∀ᶠ R : ℝ in atTop, |ν univ| ≤ 4 * Real.exp (-R / 2) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simpa only [hnorm, zero_mul, zero_add] using signed_mass_test_bound hR ν hInt hMoment
  have hlim : Tendsto (fun R : ℝ => 4 * Real.exp (-R / 2)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) tendsto_id
    simpa only [Function.comp_def, neg_div, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv).const_mul 4
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hbound) (abs_nonneg _))

/-- Lemma5.1, with no restriction to discrete measures and an explicit constant. -/
theorem signed_mass_sq_le_log_energy (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4)
    (hEnergyPos : 0 < cornerSignedEnergy ν)
    (hEnergySmall : cornerSignedEnergy ν ≤ 1 / 2) :
    |ν univ| ^ 2 ≤ 34 * cornerSignedEnergy ν *
      Real.log (Real.exp 1 / cornerSignedEnergy ν) := by
  let E := cornerSignedEnergy ν
  let R := -Real.log E
  have hE : 0 < E := hEnergyPos
  have hEone : E ≤ 1 := by dsimp [E]; linarith
  have hR : 0 ≤ R := neg_nonneg.mpr (Real.log_nonpos hE.le hEone)
  let n := ‖cornerSignedMean ν‖
  let t := ‖cornerMean (cornerTestMeasure R)‖
  let q := Real.exp (-R / 2)
  have hn : 0 ≤ n := norm_nonneg _
  have ht : 0 ≤ t := norm_nonneg _
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hn2 : n ^ 2 = E := (cornerSignedEnergy_eq_norm_sq ν).symm
  have ht2 : t ^ 2 = 1 + R / 2 := norm_cornerMean_test_sq hR
  have hq2 : q ^ 2 = E := by
    dsimp [q]
    rw [pow_two, ← Real.exp_add]
    have he : -R / 2 + -R / 2 = Real.log E := by dsimp [R]; ring
    rw [he, Real.exp_log hE]
  have hnt2 : (n * t) ^ 2 = E * (1 + R / 2) := by
    rw [mul_pow, hn2, ht2]
  have hbound : |ν univ| ≤ n * t + 4 * q := signed_mass_test_bound hR ν hInt hMoment
  have hBnonneg : 0 ≤ n * t + 4 * q :=
    add_nonneg (mul_nonneg hn ht) (mul_nonneg (by norm_num) hq)
  have hsquare : |ν univ| ^ 2 ≤ (n * t + 4 * q) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hBnonneg).mpr hbound
  have hupper : (n * t + 4 * q) ^ 2 ≤ E * (R + 34) := by
    have htwo : (n * t + 4 * q) ^ 2 ≤ 2 * (n * t) ^ 2 + 32 * q ^ 2 := by
      nlinarith [sq_nonneg (n * t - 4 * q)]
    rw [hnt2, hq2] at htwo
    nlinarith
  have hlog : Real.log (Real.exp 1 / E) = 1 + R := by
    rw [Real.log_div (Real.exp_ne_zero _) hE.ne', Real.log_exp]
    dsimp [R]
    ring
  change |ν univ| ^ 2 ≤ 34 * E * Real.log (Real.exp 1 / E)
  rw [hlog]
  nlinarith [mul_nonneg hE.le hR]

/-- The exponential-moment assumption stated as a nonnegative Lebesgue integral
automatically supplies the integrability needed in the preceding proofs. -/
theorem exponentialMoment_integrable_and_le (ν : SignedMeasure ℝ)
    (hMoment : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2)) ∂ν.totalVariation) ≤ 4) :
    Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation ∧
      (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4 := by
  have hnonneg : ∀ᵐ x : ℝ ∂ν.totalVariation, 0 ≤ Real.exp (|x| / 2) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation := by
    fun_prop
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hnonneg).mpr ?_⟩, ?_⟩
  · exact hMoment.trans_lt (by norm_num)
  · rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
    simpa using ENNReal.toReal_mono (by norm_num : (4 : ℝ≥0∞) ≠ ∞) hMoment

/-- The paper's full Lemma5.1 for arbitrary finite real signed measures, in the
exact moment formulation and with the universal constant34. -/
theorem lemma_5_1_logarithmic_mass (ν : SignedMeasure ℝ)
    (hMoment : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2)) ∂ν.totalVariation) ≤ 4) :
    (cornerSignedEnergy ν = 0 → ν univ = 0) ∧
      (0 < cornerSignedEnergy ν → cornerSignedEnergy ν ≤ 1 / 2 →
        |ν univ| ^ 2 ≤ 34 * cornerSignedEnergy ν *
          Real.log (Real.exp 1 / cornerSignedEnergy ν)) := by
  obtain ⟨hInt, hReal⟩ := exponentialMoment_integrable_and_le ν hMoment
  exact ⟨signed_mass_zero_of_energy_zero ν hInt hReal,
    signed_mass_sq_le_log_energy ν hInt hReal⟩

end VolumePolynomials
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/KernelLogMass.lean -/

/- BEGIN SOURCE: VolumePolynomials/SlopeEntryEnergy.lean -/
section


@[expose] public section

/-!
# The entrywise energy and mass inequality

For every finite positive measure with both reciprocal exponential moments at
most one, the genuine corner energy I satisfies m⁴ ≤ I(2-I). No restriction to
atomic measures is made. This supplies the uniform determinant gap in Lemma 5.2.
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem slope_mass_le_one (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hp : slopeExponentialMoment μ (-1 / 2) ≤ 1)
    (hq : slopeExponentialMoment μ (1 / 2) ≤ 1) : μ.real univ ≤ 1 := by
  have hCS := slope_mass_sq_le_moments μ
    (hp.trans_lt (by norm_num)) (hq.trans_lt (by norm_num))
  have hp0 : 0 ≤ ∫ x : ℝ, Real.exp ((-1 / 2) * x) ∂μ :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hq0 : 0 ≤ ∫ x : ℝ, Real.exp ((1 / 2) * x) ∂μ :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hprod := mul_le_mul (integral_exponential_le_one hp)
    (integral_exponential_le_one hq) hq0 (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [measureReal_nonneg (μ := μ) (s := univ)]

theorem slope_entry_mass_fourth_le_energy (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hp : slopeExponentialMoment μ (-1 / 2) ≤ 1)
    (hq : slopeExponentialMoment μ (1 / 2) ≤ 1) :
    (μ.real univ) ^ 4 ≤ ‖cornerMean μ‖ ^ 2 * (2 - ‖cornerMean μ‖ ^ 2) := by
  let p : ℝ → ℝ := fun x => Real.exp ((-1 / 2) * x)
  let q : ℝ → ℝ := fun x => Real.exp ((1 / 2) * x)
  let K : ℝ × ℝ → ℝ := fun z => cornerKernel z.1 z.2
  let J : ℝ × ℝ → ℝ := fun z => Real.exp (|z.1 - z.2| / 2)
  have hpint : Integrable p μ := slopeExponentialMoment_integrable (hp.trans_lt (by norm_num))
  have hqint : Integrable q μ := slopeExponentialMoment_integrable (hq.trans_lt (by norm_num))
  have hKint : Integrable K (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by dsimp [K]; unfold cornerKernel; fun_prop)
    exact Filter.Eventually.of_forall fun z => by
      simpa only [K, Real.norm_eq_abs, abs_of_pos (cornerKernel_pos _ _)] using
        cornerKernel_le_one z.1 z.2
  have hsum (z : ℝ × ℝ) : K z + J z = p z.1 * q z.2 + q z.1 * p z.2 := by
    dsimp [K, J, p, q, cornerKernel]
    rw [← Real.exp_add, ← Real.exp_add]
    by_cases hz : 0 ≤ z.1 - z.2
    · rw [abs_of_nonneg hz]
      congr 1 <;> congr 1 <;> ring
    · rw [abs_of_neg (lt_of_not_ge hz), add_comm]
      congr 1 <;> congr 1 <;> ring
  have hJint : Integrable J (μ.prod μ) := by
    apply ((hpint.mul_prod hqint).add (hqint.mul_prod hpint)).mono' (by dsimp [J]; fun_prop)
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change J z ≤ p z.1 * q z.2 + q z.1 * p z.2
    have hKpos : 0 ≤ K z := (cornerKernel_pos _ _).le
    linarith [hsum z]
  have hIeq : ∫ z : ℝ × ℝ, K z ∂μ.prod μ = ‖cornerMean μ‖ ^ 2 := by
    rw [norm_cornerMean_sq, integral_prod _ hKint]
  have hIJ : ‖cornerMean μ‖ ^ 2 + (∫ z : ℝ × ℝ, J z ∂μ.prod μ) ≤ 2 := by
    rw [← hIeq, ← integral_add hKint hJint]
    simp_rw [hsum]
    rw [integral_add (hpint.mul_prod hqint) (hqint.mul_prod hpint),
      integral_prod_mul, integral_prod_mul]
    have hp0 : 0 ≤ ∫ x, p x ∂μ := integral_nonneg fun x => (Real.exp_pos _).le
    have hq0 : 0 ≤ ∫ x, q x ∂μ := integral_nonneg fun x => (Real.exp_pos _).le
    have hprod := mul_le_mul (integral_exponential_le_one hp)
      (integral_exponential_le_one hq) hq0 (by norm_num : (0 : ℝ) ≤ 1)
    have hprod' : (∫ x, p x ∂μ) * (∫ x, q x ∂μ) ≤ 1 := by
      simpa only [p, q, mul_one] using hprod
    nlinarith
  let f : ℝ × ℝ → ℝ := fun z => Real.exp (-|z.1 - z.2| / 4)
  let g : ℝ × ℝ → ℝ := fun z => Real.exp (|z.1 - z.2| / 4)
  have hfsq (z : ℝ × ℝ) : f z ^ 2 = K z := by
    dsimp [f, K, cornerKernel]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hgsq (z : ℝ × ℝ) : g z ^ 2 = J z := by
    dsimp [g, J]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hfg (z : ℝ × ℝ) : f z * g z = 1 := by
    dsimp [f, g]
    have he : -|z.1 - z.2| / 4 + |z.1 - z.2| / 4 = 0 := by ring
    rw [← Real.exp_add, he, Real.exp_zero]
  have hf : MemLp f 2 (μ.prod μ) :=
    (memLp_two_iff_integrable_sq (by dsimp [f]; fun_prop)).mpr (by simpa only [hfsq] using hKint)
  have hg : MemLp g 2 (μ.prod μ) :=
    (memLp_two_iff_integrable_sq (by dsimp [g]; fun_prop)).mpr (by simpa only [hgsq] using hJint)
  have hmass : (∫ z : ℝ × ℝ, (1 : ℝ) ∂μ.prod μ) = (μ.real univ) ^ 2 := by
    simpa only [one_mul, integral_const, smul_eq_mul, mul_one, pow_two] using
      (integral_prod_mul (μ := μ) (ν := μ) (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (1 : ℝ)))
  have hCS := integral_mul_sq_le hf hg
  simp only [hfg, hfsq, hgsq, hmass, hIeq] at hCS
  have hbound := mul_le_mul_of_nonneg_left hIJ (sq_nonneg ‖cornerMean μ‖)
  nlinarith

end VolumePolynomials
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SlopeEntryEnergy.lean -/

/- BEGIN SOURCE: VolumePolynomials/FourthMoment.lean -/
section


@[expose] public section

/-!
# The full fourth-moment estimate for admissible Fourier matrices

The entry measures are arbitrary finite Borel measures on the real line.
Every matrix, energy, mass and moment in this statement is computed from those
measures. The proof uses the actual signed determinant measure and the proved
logarithmic energy estimate; no singular-value or spectral representation is
assumed as an additional hypothesis.
-/

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem signedSlopeFourier_zero (ν : SignedMeasure ℝ) :
    signedSlopeFourier ν 0 = (ν univ : ℂ) := by
  rw [signedSlopeFourier_jordan, charFun_zero, charFun_zero,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real ν MeasurableSet.univ,
    Complex.ofReal_sub]

theorem slopeDeterminantMeasure_mass
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)] :
    slopeDeterminantMeasure ρ univ = (slopeMassMatrix ρ).det := by
  have h := signedSlopeFourier_determinant ρ 0
  rw [signedSlopeFourier_zero, slopeFourierMatrix_zero] at h
  apply Complex.ofReal_injective
  simpa only [Matrix.det_fin_two, Matrix.map_apply, Complex.ofReal_sub,
    Complex.ofReal_mul] using h

/-- The exact second moment in Section 4.2. -/
noncomputable def slopeSecondMoment (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : ℝ :=
  ∫ ξ : ℝ, matrixSecondTrace (slopeFourierMatrix ρ ξ) ∂cornerSpectralMeasure

/-- The exact fourth moment in Section 5.2. -/
noncomputable def slopeFourthMoment (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : ℝ :=
  ∫ ξ : ℝ, matrixFourthTrace (slopeFourierMatrix ρ ξ) ∂cornerSpectralMeasure

theorem integrable_slopeSecondTrace
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)] :
    Integrable (fun ξ : ℝ => matrixSecondTrace (slopeFourierMatrix ρ ξ))
      cornerSpectralMeasure := by
  simp only [matrixSecondTrace_eq_sum, Fin.sum_univ_two, slopeFourierMatrix]
  exact ((integrable_spectral_normSq (ρ 0 0)).add (integrable_spectral_normSq (ρ 0 1))).add
    ((integrable_spectral_normSq (ρ 1 0)).add (integrable_spectral_normSq (ρ 1 1)))

theorem slopeSecondMoment_eq_entry_energies
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)] :
    slopeSecondMoment ρ = ∑ i, ∑ j, ‖cornerMean (ρ i j)‖ ^ 2 := by
  simp only [slopeSecondMoment, matrixSecondTrace_eq_sum, Fin.sum_univ_two, slopeFourierMatrix]
  erw [integral_add
      ((integrable_spectral_normSq (ρ 0 0)).add (integrable_spectral_normSq (ρ 0 1)))
      ((integrable_spectral_normSq (ρ 1 0)).add (integrable_spectral_normSq (ρ 1 1))),
    integral_add (integrable_spectral_normSq (ρ 0 0)) (integrable_spectral_normSq (ρ 0 1)),
    integral_add (integrable_spectral_normSq (ρ 1 0)) (integrable_spectral_normSq (ρ 1 1))]
  simp only [corner_spectral_energy]

theorem integrable_slopeDeterminantEnergy
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    Integrable (fun ξ : ℝ => matrixDeterminantEnergy (slopeFourierMatrix ρ ξ))
      cornerSpectralMeasure := by
  apply (integrable_const (1 : ℝ)).mono' ?_ ?_
  · dsimp [matrixDeterminantEnergy, slopeFourierMatrix]
    simp only [Matrix.det_fin_two, slopeFourierMatrix, ← Complex.sq_norm]
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (matrixDeterminantEnergy_nonneg _)]
      exact contraction_determinant_le_one _ (admissible_fourier_contraction ρ hρ ξ)

theorem integrable_slopeFourthTrace
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    Integrable (fun ξ : ℝ => matrixFourthTrace (slopeFourierMatrix ρ ξ))
      cornerSpectralMeasure := by
  apply (integrable_const (4 : ℝ)).mono' ?_ ?_
  · simp_rw [matrixFourthTrace_eq]
    exact ((integrable_slopeSecondTrace ρ).aestronglyMeasurable.pow 2).sub
      ((integrable_slopeDeterminantEnergy ρ hρ).aestronglyMeasurable.const_mul 2)
  · apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (matrixFourthTrace_nonneg _), matrixFourthTrace_eq]
    have ht := matrixSecondTrace_nonneg (slopeFourierMatrix ρ ξ)
    have hd := matrixDeterminantEnergy_nonneg (slopeFourierMatrix ρ ξ)
    have hF := admissible_fourier_contraction ρ hρ ξ
    have hlow := contraction_determinant_lower _ hF
    have hupp := contraction_determinant_le_one _ hF
    have ht2 : matrixSecondTrace (slopeFourierMatrix ρ ξ) ≤ 2 := by linarith
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht2)]

/-- Both integrated matrix inequalities use the actual spectral probability measure. -/
theorem slopeFourthMoment_determinant_bounds
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    slopeFourthMoment ρ ≤ 1 + (slopeMassMatrix ρ).det ^ 2 * (slopeSecondMoment ρ - 1) ∧
      (1 - (slopeMassMatrix ρ).det ^ 2) * cornerSignedEnergy (slopeDeterminantMeasure ρ) ≤
        slopeSecondMoment ρ - slopeFourthMoment ρ := by
  have hpoint (ξ : ℝ) := matrixFourthTrace_bounds (slopeFourierMatrix ρ ξ)
    ((slopeMassMatrix ρ).map Complex.ofReal)
    (admissible_fourier_contraction ρ hρ ξ) (admissible_mass_contraction ρ hρ)
    (admissible_fourier_domination ρ ξ)
  simp only [matrixDeterminantEnergy_ofReal] at hpoint
  constructor
  · have h := integral_mono (integrable_slopeFourthTrace ρ hρ)
      ((integrable_const (1 : ℝ)).add
        (((integrable_slopeSecondTrace ρ).sub (integrable_const (1 : ℝ))).const_mul
          ((slopeMassMatrix ρ).det ^ 2))) (fun ξ => (hpoint ξ).1)
    dsimp only [Pi.add_apply, Pi.sub_apply] at h
    erw [integral_add (integrable_const (1 : ℝ))
        (((integrable_slopeSecondTrace ρ).sub (integrable_const (1 : ℝ))).const_mul
          ((slopeMassMatrix ρ).det ^ 2)), integral_const_mul,
      integral_sub (integrable_slopeSecondTrace ρ) (integrable_const (1 : ℝ)),
      integral_const, probReal_univ, one_smul] at h
    simpa only [slopeFourthMoment, slopeSecondMoment] using h
  · have h := integral_mono
      ((integrable_slopeDeterminantEnergy ρ hρ).const_mul (1 - (slopeMassMatrix ρ).det ^ 2))
      ((integrable_slopeSecondTrace ρ).sub (integrable_slopeFourthTrace ρ hρ))
      (fun ξ => (hpoint ξ).2)
    dsimp only [Pi.sub_apply] at h
    erw [integral_const_mul,
      ← determinant_measure_energy,
      integral_sub (integrable_slopeSecondTrace ρ) (integrable_slopeFourthTrace ρ hρ)] at h
    simpa only [slopeFourthMoment, slopeSecondMoment] using h

/-- A uniform gap for the genuine determinant mass when the second moment is small. -/
theorem admissible_determinant_gap
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hsmall : slopeSecondMoment ρ ≤ 3 / 2) :
    (slopeMassMatrix ρ).det ^ 2 ≤ 31 / 32 := by
  apply nonnegative_mass_matrix_determinant_gap (slopeMassMatrix ρ)
    (fun i j => ‖cornerMean (ρ i j)‖ ^ 2)
  · exact fun i j => measureReal_nonneg
  · exact fun i j => slope_mass_le_one (ρ i j)
      (admissible_entry_negative_moment hρ i j) (admissible_entry_positive_moment hρ i j)
  · exact fun i j => sq_nonneg _
  · exact fun i j => slope_entry_mass_fourth_le_energy (ρ i j)
      (admissible_entry_negative_moment hρ i j) (admissible_entry_positive_moment hρ i j)
  · rwa [← slopeSecondMoment_eq_entry_energies]

/-- Elementary monotonicity of the logarithmic energy scale, proved from log's
supporting-line inequality rather than a differentiability assumption. -/
theorem mul_log_exp_div_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    x * Real.log (Real.exp 1 / x) ≤ y * Real.log (Real.exp 1 / y) := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hlog : Real.log (Real.exp 1 / x) =
      Real.log (Real.exp 1 / y) + Real.log (y / x) := by
    rw [Real.log_div (Real.exp_ne_zero _) hx.ne', Real.log_div (Real.exp_ne_zero _) hy0.ne',
      Real.log_div hy0.ne' hx.ne']
    ring
  have hLy : 1 ≤ Real.log (Real.exp 1 / y) := by
    rw [Real.log_div (Real.exp_ne_zero _) hy0.ne', Real.log_exp]
    linarith [Real.log_nonpos hy0.le hy]
  have hsec := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy0 hx)) hx.le
  have hsec' : x * Real.log (y / x) ≤ y - x := by
    convert hsec using 1
    field_simp [hx.ne']
  rw [hlog, mul_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hLy)]

theorem log_inverse_ge_one {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / ε) := by
  have hlog := Real.log_le_log hε hsmall
  rw [Real.log_exp] at hlog
  rw [Real.log_div one_ne_zero hε.ne', Real.log_one]
  linarith

theorem logarithmic_energy_scale_bound {E ε : ℝ} (hE : 0 < E) (hε : 0 < ε)
    (hEε : E ≤ 32 * ε) (hsmall : ε ≤ 1 / 64) (hlog : 1 ≤ Real.log (1 / ε)) :
    E * Real.log (Real.exp 1 / E) ≤ 64 * ε * Real.log (1 / ε) := by
  have h32 : 0 < 32 * ε := by positivity
  have hmono := mul_log_exp_div_mono hE hEε (by linarith : 32 * ε ≤ 1)
  have hlog32 : Real.log (Real.exp 1 / (32 * ε)) ≤ 1 + Real.log (1 / ε) := by
    have harg : Real.exp 1 / (32 * ε) ≤ Real.exp 1 / ε := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le hε
      linarith
    have h := Real.log_le_log (div_pos (Real.exp_pos _) h32) harg
    rw [Real.log_div (Real.exp_ne_zero _) hε.ne', Real.log_exp] at h
    rw [Real.log_div one_ne_zero hε.ne', Real.log_one]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog32 h32.le
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hlog)]

/-- Lemma 5.2 with explicit universal constants and a concrete sufficiently-small
range. This retains every admissible finite slope measure, not just polygons or
atomic measures. -/
theorem lemma_5_2_fourth_moment
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ min (1 / 64) (Real.exp (-1)))
    (hsecond : slopeSecondMoment ρ = 1 + ε) :
    slopeFourthMoment ρ ≤ 1 + 2176 * ε ^ 2 * Real.log (1 / ε) := by
  have hε64 : ε ≤ 1 / 64 := hsmall.trans (min_le_left _ _)
  have hεexp : ε ≤ Real.exp (-1) := hsmall.trans (min_le_right _ _)
  have hlog : 1 ≤ Real.log (1 / ε) := log_inverse_ge_one hε hεexp
  have hL0 : 0 ≤ Real.log (1 / ε) := zero_le_one.trans hlog
  by_cases hfourth : slopeFourthMoment ρ ≤ 1
  · exact hfourth.trans (le_add_of_nonneg_right (by positivity))
  have hfourth' : 1 < slopeFourthMoment ρ := lt_of_not_ge hfourth
  let E := cornerSignedEnergy (slopeDeterminantMeasure ρ)
  let β := (slopeMassMatrix ρ).det ^ 2
  have hβ0 : 0 ≤ β := sq_nonneg _
  have hβgap : β ≤ 31 / 32 := admissible_determinant_gap ρ hρ (by rw [hsecond]; linarith)
  obtain ⟨hupper, hlower⟩ := slopeFourthMoment_determinant_bounds ρ hρ
  change slopeFourthMoment ρ ≤ 1 + β * (slopeSecondMoment ρ - 1) at hupper
  change (1 - β) * E ≤ slopeSecondMoment ρ - slopeFourthMoment ρ at hlower
  rw [hsecond] at hupper hlower
  have hE0 : 0 ≤ E := cornerSignedEnergy_nonneg _
  have hEε : E ≤ 32 * ε := by
    have hgapE := mul_le_mul_of_nonneg_right hβgap hE0
    nlinarith
  have hmoment := slopeDeterminantMeasure_exponential_moment ρ hρ
  have hmass := lemma_5_1_logarithmic_mass (slopeDeterminantMeasure ρ) hmoment
  have hEpos : 0 < E := by
    by_contra hn
    have hzero : E = 0 := le_antisymm (le_of_not_gt hn) hE0
    have hmzero := hmass.1 hzero
    rw [slopeDeterminantMeasure_mass] at hmzero
    have hβzero : β = 0 := by dsimp [β]; rw [hmzero]; norm_num
    rw [hβzero] at hupper
    linarith
  have hmassBound := hmass.2 hEpos (by change E ≤ 1 / 2; linarith)
  rw [slopeDeterminantMeasure_mass, sq_abs] at hmassBound
  change β ≤ 34 * E * Real.log (Real.exp 1 / E) at hmassBound
  have hscale := logarithmic_energy_scale_bound hEpos hε hEε hε64 hlog
  have hβ : β ≤ 2176 * ε * Real.log (1 / ε) := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hβ hε.le
  nlinarith

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FourthMoment.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolygonCornerMeasures.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Literal finite corner measures and their geometric second moment

The four measures are constructed from the actual facet representation. Axis
vectors have zero mass. Their admissibility follows from the actual projection
widths, and the spectral second moment is exactly twice the area deficit.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped ENNReal NNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def signIndex (x : ℝ) : Fin 2 := if 0 ≤ x then 0 else 1

def atomSlope (e : Plane) : ℝ := Real.log (|e.2| / |e.1|)

def atomWeight (e : Plane) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (|e.1| * |e.2|)) (Real.sqrt_nonneg _)

def slopeAtom (e : Plane) : Measure ℝ := atomWeight e • Measure.dirac (atomSlope e)

instance slopeAtom_finite (e : Plane) : IsFiniteMeasure (slopeAtom e) := by
  first
  | unfold slopeAtom
    infer_instance

def atomFeature (e : Plane) : Lp ℝ 2 (volume : Measure ℝ) :=
  (atomWeight e : ℝ) • cornerFeature (atomSlope e)

def cornerAtom (e : Plane) (i j : Fin 2) : Measure ℝ :=
  if signIndex e.1 = i ∧ signIndex e.2 = j then slopeAtom e else 0

instance cornerAtom_finite (e : Plane) (i j : Fin 2) : IsFiniteMeasure (cornerAtom e i j) := by
  first
  | unfold cornerAtom
    split_ifs <;> infer_instance

def cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane) :
    Matrix (Fin 2) (Fin 2) (Measure ℝ) := fun i j => ∑ k, cornerAtom (e k) i j

instance cornerMatrix_finite {ι : Type*} [Fintype ι] (e : ι → Plane) (i j : Fin 2) :
    IsFiniteMeasure (cornerMatrix e i j) := by
  first
  | unfold cornerMatrix
    infer_instance

theorem integrable_slopeAtom (e : Plane) (f : ℝ → ℝ) : Integrable f (slopeAtom e) :=
  (integrable_dirac (f := f) (a := atomSlope e) enorm_lt_top).smul_measure_nnreal

theorem integrable_cornerAtom (e : Plane) (i j : Fin 2) (f : ℝ → ℝ) :
    Integrable f (cornerAtom e i j) := by
  first
  | unfold cornerAtom
    split_ifs
    · exact integrable_slopeAtom e f
    · exact integrable_zero_measure

theorem integrable_cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane)
    (i j : Fin 2) (f : ℝ → ℝ) : Integrable f (cornerMatrix e i j) := by
  first
  | exact integrable_finsetSum_measure.mpr (fun k _ => integrable_cornerAtom (e k) i j f)

theorem integral_slopeAtom (e : Plane) (f : ℝ → ℝ) :
    (∫ x, f x ∂slopeAtom e) = (atomWeight e : ℝ) * f (atomSlope e) := by
  first
  | change (∫ x, f x ∂(atomWeight e • Measure.dirac (atomSlope e))) = _
    rw [integral_smul_nnreal_measure, integral_dirac]
    rfl

theorem slopeAtom_exponential_moments (e : Plane) :
    (∫ x, Real.exp ((-1 / 2 : ℝ) * x) ∂slopeAtom e) ≤ |e.1| ∧
      (∫ x, Real.exp ((1 / 2 : ℝ) * x) ∂slopeAtom e) ≤ |e.2| := by
  first
  | rw [integral_slopeAtom, integral_slopeAtom]
    change Real.sqrt (|e.1| * |e.2|) * Real.exp ((-1 / 2 : ℝ) * Real.log (|e.2| / |e.1|)) ≤ |e.1| ∧
      Real.sqrt (|e.1| * |e.2|) * Real.exp ((1 / 2 : ℝ) * Real.log (|e.2| / |e.1|)) ≤ |e.2|
    by_cases hx : e.1 = 0
    · simp [hx, abs_nonneg e.2]
    by_cases hy : e.2 = 0
    · simp [hy, abs_nonneg e.1]
    have h := HalfZonotope.atom_exponential_moments (abs_pos.mpr hx) (abs_pos.mpr hy)
    constructor
    · convert h.1.le using 1 <;> congr 2 <;> ring
    · convert h.2.le using 1 <;> congr 2 <;> ring

theorem integral_cornerMatrix_row {ι : Type*} [Fintype ι] (e : ι → Plane)
    (i : Fin 2) (f : ℝ → ℝ) :
    (∑ j, ∫ x, f x ∂cornerMatrix e i j) =
      ∑ k, if signIndex (e k).1 = i then ∫ x, f x ∂slopeAtom (e k) else 0 := by
  first
  | simp only [cornerMatrix, integral_finsetSum_measure
      (fun k _ => integrable_cornerAtom (e k) i _ f)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hi : signIndex (e k).1 = i
    · simp only [cornerAtom, hi, true_and, ite_true]
      by_cases hs : 0 ≤ (e k).2 <;> simp [signIndex, hs]
    · simp [cornerAtom, hi]

theorem integral_cornerMatrix_col {ι : Type*} [Fintype ι] (e : ι → Plane)
    (j : Fin 2) (f : ℝ → ℝ) :
    (∑ i, ∫ x, f x ∂cornerMatrix e i j) =
      ∑ k, if signIndex (e k).2 = j then ∫ x, f x ∂slopeAtom (e k) else 0 := by
  first
  | simp only [cornerMatrix, integral_finsetSum_measure
      (fun k _ => integrable_cornerAtom (e k) _ j f)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hj : signIndex (e k).2 = j
    · simp only [cornerAtom, hj, and_true, ite_true]
      by_cases hs : 0 ≤ (e k).1 <;> simp [signIndex, hs]
    · simp [cornerAtom, hj]

theorem sign_part_bound (x a : ℝ) (r : Fin 2) (ha : a ≤ |x|) :
    (if signIndex x = r then a else 0) ≤
      if r = 0 then max x 0 else max (-x) 0 := by
  first
  | fin_cases r
    · by_cases hx : 0 ≤ x
      · simpa [signIndex, hx, abs_of_nonneg hx, max_eq_left hx] using ha
      · simp [signIndex, hx, max_eq_right (le_of_not_ge hx)]
    · by_cases hx : 0 ≤ x
      · simp [signIndex, hx, max_eq_right (neg_nonpos.mpr hx)]
      · simpa [signIndex, hx, abs_of_nonpos (le_of_not_ge hx),
          max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))] using ha

theorem Represents.row_moment_le_width {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (i : Fin 2) :
    (∑ j, ∫ x, Real.exp ((-1 / 2 : ℝ) * x) ∂cornerMatrix e i j) ≤ width P := by
  first
  | rw [integral_cornerMatrix_row]
    calc
      _ ≤ ∑ k, if i = 0 then max (e k).1 0 else max (-(e k).1) 0 :=
        Finset.sum_le_sum (fun k _ => sign_part_bound _ _ i (slopeAtom_exponential_moments (e k)).1)
      _ = width P := by
        first
        | fin_cases i
          · simpa using h.signed_variation.1
          · simpa using h.signed_variation.2.2.1

theorem Represents.col_moment_le_height {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (j : Fin 2) :
    (∑ i, ∫ x, Real.exp ((1 / 2 : ℝ) * x) ∂cornerMatrix e i j) ≤ height P := by
  first
  | rw [integral_cornerMatrix_col]
    calc
      _ ≤ ∑ k, if j = 0 then max (e k).2 0 else max (-(e k).2) 0 :=
        Finset.sum_le_sum (fun k _ => sign_part_bound _ _ j (slopeAtom_exponential_moments (e k)).2)
      _ = height P := by
        first
        | fin_cases j
          · simpa using h.signed_variation.2.1
          · simpa using h.signed_variation.2.2.2

theorem cornerMatrix_moment_eq_ofReal_integral {ι : Type*} [Fintype ι]
    (e : ι → Plane) (i j : Fin 2) (a : ℝ) :
    slopeExponentialMoment (cornerMatrix e i j) a =
      ENNReal.ofReal (∫ x, Real.exp (a * x) ∂cornerMatrix e i j) := by
  first
  | exact (ofReal_integral_eq_lintegral_ofReal (integrable_cornerMatrix e i j _)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm

/-- Admissibility is proved for the genuine nonnegative exponential integrals. -/
theorem Represents.admissible {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e)
    (hw : width P = 1) (hh : height P = 1) : IsAdmissibleSlopeMatrix (cornerMatrix e) := by
  first
  | constructor
    · intro i
      simp_rw [cornerMatrix_moment_eq_ofReal_integral]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg
        (fun x => (Real.exp_pos ((-1 / 2 : ℝ) * x)).le))]
      have hm := h.row_moment_le_width i
      rw [hw] at hm
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hm
    · intro j
      simp_rw [cornerMatrix_moment_eq_ofReal_integral]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg
        (fun x => (Real.exp_pos ((1 / 2 : ℝ) * x)).le))]
      have hm := h.col_moment_le_height j
      rw [hh] at hm
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hm

@[simp] theorem cornerMean_slopeAtom (e : Plane) : cornerMean (slopeAtom e) = atomFeature e := by
  first
  | simp only [cornerMean, slopeAtom, integral_smul_nnreal_measure, integral_dirac,
      NNReal.smul_def, atomFeature]

theorem inner_atomFeature (e f : Plane) :
    ⟪atomFeature e, atomFeature f⟫_ℝ = min (|e.1| * |f.2|) (|f.1| * |e.2|) := by
  first
  | simp only [atomFeature, real_inner_smul_left, real_inner_smul_right,
      inner_cornerFeature, atomWeight, NNReal.coe_mk, atomSlope]
    rw [← mul_assoc]
    change Real.sqrt (|f.1| * |f.2|) * Real.sqrt (|e.1| * |e.2|) *
      cornerKernel (Real.log (|e.2| / |e.1|)) (Real.log (|f.2| / |f.1|)) = _
    rw [mul_comm (Real.sqrt (|f.1| * |f.2|)) (Real.sqrt (|e.1| * |e.2|))]
    exact HalfZonotope.weighted_cornerKernel (abs_nonneg e.1) (abs_nonneg e.2)
      (abs_nonneg f.1) (abs_nonneg f.2)

theorem cornerMean_cornerAtom (e : Plane) (i j : Fin 2) :
    cornerMean (cornerAtom e i j) =
      if signIndex e.1 = i ∧ signIndex e.2 = j then atomFeature e else 0 := by
  first
  | unfold cornerAtom
    split_ifs
    · exact cornerMean_slopeAtom e
    · simp [cornerMean]

theorem cornerMean_cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane) (i j : Fin 2) :
    cornerMean (cornerMatrix e i j) = ∑ k, cornerMean (cornerAtom (e k) i j) := by
  first
  | exact integral_finsetSum_measure (fun k _ => integrable_cornerFeature (cornerAtom (e k) i j))

theorem signIndex_eq_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    signIndex a = signIndex b ↔ 0 < a * b := by
  first
  | rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
    · simp [signIndex, not_le_of_gt ha, not_le_of_gt hb, mul_pos_of_neg_of_neg ha hb]
    · simp [signIndex, not_le_of_gt ha, hb.le, not_lt_of_ge
        (mul_nonpos_of_nonpos_of_nonneg ha.le hb.le)]
    · simp [signIndex, ha.le, not_le_of_gt hb, not_lt_of_ge
        (mul_nonpos_of_nonneg_of_nonpos ha.le hb.le)]
    · simp [signIndex, ha.le, hb.le, mul_pos ha hb]

theorem cornerAtom_inner_sum (e f : Plane) :
    (∑ i, ∑ j, ⟪cornerMean (cornerAtom e i j), cornerMean (cornerAtom f i j)⟫_ℝ) =
      if signIndex e.1 = signIndex f.1 ∧ signIndex e.2 = signIndex f.2
        then ⟪atomFeature e, atomFeature f⟫_ℝ else 0 := by
  first
  | have h (i j : Fin 2) :
        ⟪cornerMean (cornerAtom e i j), cornerMean (cornerAtom f i j)⟫_ℝ =
          if signIndex e.1 = i then if signIndex e.2 = j then
            (if signIndex e.1 = signIndex f.1 ∧ signIndex e.2 = signIndex f.2
              then ⟪atomFeature e, atomFeature f⟫_ℝ else 0) else 0 else 0 := by
      first
      | rw [cornerMean_cornerAtom, cornerMean_cornerAtom]
        by_cases hi : signIndex e.1 = i <;> by_cases hj : signIndex e.2 = j
        · subst i
          subst j
          by_cases hf : signIndex e.1 = signIndex f.1 ∧ signIndex e.2 = signIndex f.2
          · simp [hf.1, hf.2]
          · have hf' : ¬(signIndex f.1 = signIndex e.1 ∧ signIndex f.2 = signIndex e.2) :=
              fun h => hf ⟨h.1.symm, h.2.symm⟩
            simp [hf, hf']
        · simp [hi, hj]
        · simp [hi, hj]
        · simp [hi, hj]
    simp_rw [h]
    simp

theorem pairKernel_eq_cornerAtom_inner (e f : Plane) :
    pairKernel e f = ∑ i, ∑ j,
      ⟪cornerMean (cornerAtom e i j), cornerMean (cornerAtom f i j)⟫_ℝ := by
  first
  | rw [cornerAtom_inner_sum, inner_atomFeature, pairKernel_eq_min]
    by_cases he1 : e.1 = 0
    · simp [he1, mul_nonneg (abs_nonneg f.1) (abs_nonneg e.2)]
    by_cases he2 : e.2 = 0
    · simp [he2, mul_nonneg (abs_nonneg e.1) (abs_nonneg f.2)]
    by_cases hf1 : f.1 = 0
    · simp [hf1, mul_nonneg (abs_nonneg e.1) (abs_nonneg f.2)]
    by_cases hf2 : f.2 = 0
    · simp [hf2, mul_nonneg (abs_nonneg f.1) (abs_nonneg e.2)]
    simp only [signIndex_eq_iff he1 hf1, signIndex_eq_iff he2 hf2]
    congr 1
    rw [mul_comm |e.2| |f.1|]

theorem cornerPairing_eq_matrix_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) :
    cornerPairing e f = ∑ i, ∑ j,
      ⟪cornerMean (cornerMatrix e i j), cornerMean (cornerMatrix f i j)⟫_ℝ := by
  first
  | simp_rw [cornerMean_cornerMatrix, sum_inner, inner_sum]
    simp_rw [cornerPairing, pairKernel_eq_cornerAtom_inner]
    let g (a : ι) (b : κ) (i j : Fin 2) :=
      ⟪cornerMean (cornerAtom (e a) i j), cornerMean (cornerAtom (f b) i j)⟫_ℝ
    change (∑ a, ∑ b, ∑ i, ∑ j, g a b i j) = ∑ i, ∑ j, ∑ a, ∑ b, g a b i j
    calc
      _ = ∑ a, ∑ i, ∑ b, ∑ j, g a b i j :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ i, ∑ a, ∑ b, ∑ j, g a b i j := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b, g a b i j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
      _ = ∑ i, ∑ j, ∑ a, ∑ b, g a b i j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

/-- Formula (4.7) for the actual polygon and the actual Cauchy spectral measure. -/
theorem Represents.second_moment {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) :
    slopeSecondMoment (cornerMatrix e) =
      2 * (width P * height P - volume.real (P : Set Plane)) := by
  first
  | have ha := h.area_identity
    rw [cornerPairing_eq_matrix_inner] at ha
    simp only [real_inner_self_eq_norm_sq] at ha
    rw [slopeSecondMoment_eq_entry_energies]
    linarith

theorem Represents.unit_second_moment {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e)
    (hw : width P = 1) (hh : height P = 1) :
    slopeSecondMoment (cornerMatrix e) = 2 * (1 - volume.real (P : Set Plane)) := by
  first
  | rw [h.second_moment, hw, hh, one_mul]

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolygonCornerMeasures.lean -/

/- BEGIN SOURCE: VolumePolynomials/InteractionEdges.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The actual product-edge construction

The four signed totals are bounded using the proved input widths. Four explicit
axis vectors complete those totals to one, and the erosion construction supplies
an actual compact convex body with this finite edge representation.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def interactionEdge (b c : Plane) : Plane :=
  if 0 < b.1 * c.1 then (-|c.1| * b.2, |b.1| * c.2) else 0

def positiveX {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (e i).1 0
def negativeX {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (-(e i).1) 0
def positiveY {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (e i).2 0
def negativeY {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (-(e i).2) 0

theorem positiveX_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ positiveX e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
theorem negativeX_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ negativeX e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
theorem positiveY_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ positiveY e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
theorem negativeY_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ negativeY e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem max_mul_nonnegative (a x : ℝ) (ha : 0 ≤ a) :
    max (a * x) 0 = a * max x 0 := by
  first
  | rcases le_total 0 x with hx | hx
    · rw [max_eq_left (mul_nonneg ha hx), max_eq_left hx]
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha hx), max_eq_right hx, mul_zero]

theorem matching_abs_sum_le {ι : Type*} [Fintype ι] (f : ι → Plane)
    {w : ℝ} (hp : positiveX f = w) (hn : negativeX f = w) (hw : 0 ≤ w) (x : ℝ) :
    (∑ i, if 0 < x * (f i).1 then |(f i).1| else 0) ≤ w := by
  first
  | rcases lt_trichotomy x 0 with hx | hx | hx
    · have he (i : ι) : (if 0 < x * (f i).1 then |(f i).1| else 0) = max (-(f i).1) 0 := by
        first
        | by_cases hy : (f i).1 < 0
          · rw [if_pos (mul_pos_of_neg_of_neg hx hy), abs_of_neg hy, max_eq_left (neg_pos.mpr hy).le]
          · have hy0 := le_of_not_gt hy
            rw [if_neg (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hx.le hy0)),
              max_eq_right (neg_nonpos.mpr hy0)]
      simp_rw [he]
      exact hn.le
    · subst x
      simpa using hw
    · have he (i : ι) : (if 0 < x * (f i).1 then |(f i).1| else 0) = max (f i).1 0 := by
        first
        | by_cases hy : 0 < (f i).1
          · rw [if_pos (mul_pos hx hy), abs_of_pos hy, max_eq_left hy.le]
          · have hy0 := le_of_not_gt hy
            rw [if_neg (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hx.le hy0)), max_eq_right hy0]
      simp_rw [he]
      exact hp.le

theorem interactionEdge_positiveX (b c : Plane) :
    max (interactionEdge b c).1 0 =
      max (-b.2) 0 * (if 0 < b.1 * c.1 then |c.1| else 0) := by
  first
  | unfold interactionEdge
    split_ifs
    · change max (-|c.1| * b.2) 0 = _
      rw [show -|c.1| * b.2 = |c.1| * (-b.2) by ring,
        max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

theorem interactionEdge_negativeX (b c : Plane) :
    max (-(interactionEdge b c).1) 0 =
      max b.2 0 * (if 0 < b.1 * c.1 then |c.1| else 0) := by
  first
  | unfold interactionEdge
    split_ifs
    · change max (-(-|c.1| * b.2)) 0 = _
      rw [show -(-|c.1| * b.2) = |c.1| * b.2 by ring,
        max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

theorem interactionEdge_positiveY (b c : Plane) :
    max (interactionEdge b c).2 0 =
      max c.2 0 * (if 0 < c.1 * b.1 then |b.1| else 0) := by
  first
  | unfold interactionEdge
    rw [mul_comm c.1 b.1]
    split_ifs
    · rw [max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

theorem interactionEdge_negativeY (b c : Plane) :
    max (-(interactionEdge b c).2) 0 =
      max (-c.2) 0 * (if 0 < c.1 * b.1 then |b.1| else 0) := by
  first
  | unfold interactionEdge
    rw [mul_comm c.1 b.1]
    split_ifs
    · change max (-(|b.1| * c.2)) 0 = _
      rw [show -(|b.1| * c.2) = |b.1| * (-c.2) by ring,
        max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

def productEdges {ι κ : Type*} (b : ι → Plane) (c : κ → Plane) : ι × κ → Plane :=
  fun i => interactionEdge (b i.1) (c i.2)

theorem productEdges_signed_totals_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1) :
    positiveX (productEdges b c) ≤ 1 ∧ negativeX (productEdges b c) ≤ 1 ∧
      positiveY (productEdges b c) ≤ 1 ∧ negativeY (productEdges b c) ≤ 1 := by
  first
  | have hb := hB.signed_variation
    have hc := hC.signed_variation
    rw [hBw, hBh] at hb
    rw [hCw, hCh] at hc
    have hmatchB := matching_abs_sum_le b hb.1 hb.2.2.1 (by norm_num : (0 : ℝ) ≤ 1)
    have hmatchC := matching_abs_sum_le c hc.1 hc.2.2.1 (by norm_num : (0 : ℝ) ≤ 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [positiveX, productEdges, Fintype.sum_prod_type, interactionEdge_positiveX,
        ← Finset.mul_sum]
      calc
        _ ≤ ∑ i, max (-(b i).2) 0 * 1 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hmatchC (b i).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hb.2.2.2
    · simp only [negativeX, productEdges, Fintype.sum_prod_type, interactionEdge_negativeX,
        ← Finset.mul_sum]
      calc
        _ ≤ ∑ i, max (b i).2 0 * 1 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hmatchC (b i).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hb.2.1
    · simp only [positiveY, productEdges, Fintype.sum_prod_type, interactionEdge_positiveY]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      calc
        _ ≤ ∑ j, max (c j).2 0 * 1 := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hmatchB (c j).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hc.2.1
    · simp only [negativeY, productEdges, Fintype.sum_prod_type, interactionEdge_negativeY]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      calc
        _ ≤ ∑ j, max (-(c j).2) 0 * 1 := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hmatchB (c j).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hc.2.2.2

def axisCompletion {ι : Type*} [Fintype ι] (e : ι → Plane) : Fin 4 → Plane :=
  ![(1 - positiveX e, 0), (negativeX e - 1, 0),
    (0, 1 - positiveY e), (0, negativeY e - 1)]

def completedEdges {ι : Type*} [Fintype ι] (e : ι → Plane) : ι ⊕ Fin 4 → Plane :=
  Sum.elim e (axisCompletion e)

theorem completedEdges_signed_totals {ι : Type*} [Fintype ι] (e : ι → Plane)
    (hpX : positiveX e ≤ 1) (hnX : negativeX e ≤ 1)
    (hpY : positiveY e ≤ 1) (hnY : negativeY e ≤ 1) :
    positiveX (completedEdges e) = 1 ∧ negativeX (completedEdges e) = 1 ∧
      positiveY (completedEdges e) = 1 ∧ negativeY (completedEdges e) = 1 := by
  first
  | have hpx : 0 ≤ 1 - positiveX e := sub_nonneg.mpr hpX
    have hnx : negativeX e - 1 ≤ 0 := sub_nonpos.mpr hnX
    have hpy : 0 ≤ 1 - positiveY e := sub_nonneg.mpr hpY
    have hny : negativeY e - 1 ≤ 0 := sub_nonpos.mpr hnY
    dsimp only [positiveX, negativeX, positiveY, negativeY] at *
    simp only [positiveX, negativeX, positiveY, negativeY, completedEdges,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, axisCompletion, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
      max_eq_left hpx, max_eq_right hnx, max_eq_left hpy, max_eq_right hny,
      max_eq_right (neg_nonpos.mpr hpx), max_eq_left (neg_nonneg.mpr hnx),
      max_eq_right (neg_nonpos.mpr hpy), max_eq_left (neg_nonneg.mpr hny), neg_zero,
      max_self, zero_add]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals linarith

theorem exists_productEdge_body {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, Represents Q (completedEdges (productEdges b c)) ∧
      width Q = 1 ∧ height Q = 1 := by
  first
  | obtain ⟨hpx, hnx, hpy, hny⟩ := productEdges_signed_totals_le_one hB hC hBw hBh hCw hCh
    obtain ⟨hpx', hnx', hpy', hny'⟩ := completedEdges_signed_totals (productEdges b c) hpx hnx hpy hny
    exact exists_body_of_balanced_edges (completedEdges (productEdges b c)) hpx' hnx' hpy' hny'

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/InteractionEdges.lean -/

/- BEGIN SOURCE: VolumePolynomials/InteractionSpectralBound.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The mixed Fourier interaction bound

Positivity of the squared Hilbert--Schmidt distance between the two Gram
matrices gives an arithmetic-mean bound. This proves the analytic estimate
used in Corollary 5.3 without adding a spectral-decomposition hypothesis.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace VolumePolynomials

theorem gram_difference_trace_identity (F G : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace (F * Fᴴ - G * Gᴴ) =
      matrixFourthTrace F + matrixFourthTrace G - 2 * matrixSecondTrace (Fᴴ * G) := by
  first
  | simp [matrixSecondTrace, matrixFourthTrace, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]
    ring

theorem mixed_matrix_trace_le_mean (F G : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace (Fᴴ * G) ≤ (matrixFourthTrace F + matrixFourthTrace G) / 2 := by
  first
  | have h := matrixSecondTrace_nonneg (F * Fᴴ - G * Gᴴ)
    rw [gram_difference_trace_identity] at h
    linarith

noncomputable def slopeInteractionMoment
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : ℝ :=
  ∫ ξ : ℝ, matrixSecondTrace ((slopeFourierMatrix ρ ξ)ᴴ * slopeFourierMatrix σ ξ)
    ∂cornerSpectralMeasure

theorem integrable_slopeInteractionTrace
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ) :
    Integrable (fun ξ : ℝ =>
      matrixSecondTrace ((slopeFourierMatrix ρ ξ)ᴴ * slopeFourierMatrix σ ξ))
      cornerSpectralMeasure := by
  first
  | apply (((integrable_slopeFourthTrace ρ hρ).add
      (integrable_slopeFourthTrace σ hσ)).div_const 2).mono' ?_ ?_
    · simp only [matrixSecondTrace_eq_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, slopeFourierMatrix, ← Complex.sq_norm]
      fun_prop
    · exact Filter.Eventually.of_forall fun ξ => by
        dsimp only [Pi.add_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (matrixSecondTrace_nonneg _)]
        exact mixed_matrix_trace_le_mean _ _

theorem slopeInteractionMoment_le_mean
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ) :
    slopeInteractionMoment ρ σ ≤ (slopeFourthMoment ρ + slopeFourthMoment σ) / 2 := by
  first
  | have h := integral_mono (integrable_slopeInteractionTrace ρ σ hρ hσ)
      (((integrable_slopeFourthTrace ρ hρ).add (integrable_slopeFourthTrace σ hσ)).div_const 2)
      (fun ξ => mixed_matrix_trace_le_mean (slopeFourierMatrix ρ ξ) (slopeFourierMatrix σ ξ))
    dsimp only [Pi.add_apply] at h
    erw [integral_div, integral_add (integrable_slopeFourthTrace ρ hρ)
      (integrable_slopeFourthTrace σ hσ)] at h
    exact h

/-- The exact analytic consequence needed for Corollary 5.3. The actual
polygon-to-matrix area identities remain separate geometric theorems. -/
theorem slopeInteractionMoment_logarithmic_bound
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ min (1 / 64) (Real.exp (-1)))
    (hsecondρ : slopeSecondMoment ρ = 1 + ε)
    (hsecondσ : slopeSecondMoment σ = 1 + ε) :
    slopeInteractionMoment ρ σ ≤ 1 + 2176 * ε ^ 2 * Real.log (1 / ε) := by
  first
  | have hρ4 := lemma_5_2_fourth_moment ρ hρ hε hsmall hsecondρ
    have hσ4 := lemma_5_2_fourth_moment σ hσ hε hsmall hsecondσ
    have h := slopeInteractionMoment_le_mean ρ σ hρ hσ
    linarith

end VolumePolynomials
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/InteractionSpectralBound.lean -/

/- BEGIN SOURCE: VolumePolynomials/InteractionFourier.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Exact Fourier matrix of the product-edge body -/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def flipCorner (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem flipCorner_flip (i : Fin 2) : flipCorner (flipCorner i) = i := by
  first
  | fin_cases i <;> norm_num [flipCorner]

theorem flipCorner_eq_iff (i j : Fin 2) : flipCorner i = j ↔ i = flipCorner j := by
  first
  | constructor
    · intro h
      simpa using congrArg flipCorner h
    · intro h
      simpa using congrArg flipCorner h

theorem signIndex_neg {x : ℝ} (hx : x ≠ 0) : signIndex (-x) = flipCorner (signIndex x) := by
  first
  | rcases lt_or_gt_of_ne hx with hx | hx
    · simp [signIndex, flipCorner, not_le_of_gt hx, (neg_pos.mpr hx).le]
    · simp [signIndex, flipCorner, hx.le, not_le_of_gt (neg_neg_of_pos hx)]

theorem signIndex_pos_mul {a x : ℝ} (ha : 0 < a) : signIndex (a * x) = signIndex x := by
  first
  | unfold signIndex
    simp only [mul_nonneg_iff_of_pos_left ha]

theorem slopeAtom_axis {e : Plane} (he : e.1 = 0 ∨ e.2 = 0) : slopeAtom e = 0 := by
  first
  | have hw : atomWeight e = 0 := by
      first
      | apply Subtype.ext
        change Real.sqrt (|e.1| * |e.2|) = 0
        rcases he with he | he <;> simp [he]
    rw [slopeAtom, hw, zero_smul]

theorem cornerAtom_axis {e : Plane} (he : e.1 = 0 ∨ e.2 = 0) (i j : Fin 2) :
    cornerAtom e i j = 0 := by
  first
  | simp only [cornerAtom, slopeAtom_axis he]
    split_ifs <;> rfl

theorem cornerMatrix_completed {ι : Type*} [Fintype ι] (e : ι → Plane) :
    cornerMatrix (completedEdges e) = cornerMatrix e := by
  first
  | ext i j : 2
    simp only [cornerMatrix, completedEdges, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have haxis (k : Fin 4) : cornerAtom (axisCompletion e k) i j = 0 := by
      first
      | apply cornerAtom_axis
        fin_cases k <;> simp [axisCompletion]
    simp only [haxis, Finset.sum_const_zero, add_zero]

theorem charFun_slopeAtom (e : Plane) (ξ : ℝ) :
    charFun (slopeAtom e) ξ = (atomWeight e : ℂ) *
      Complex.exp (((ξ * atomSlope e : ℝ) : ℂ) * Complex.I) := by
  first
  | simp only [charFun_apply_real, slopeAtom, integral_smul_nnreal_measure,
      integral_dirac, NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]

theorem charFun_cornerAtom (e : Plane) (i j : Fin 2) (ξ : ℝ) :
    charFun (cornerAtom e i j) ξ =
      if signIndex e.1 = i ∧ signIndex e.2 = j then charFun (slopeAtom e) ξ else 0 := by
  first
  | unfold cornerAtom
    split_ifs <;> simp

theorem charFun_cornerMatrix {ι : Type*} [Fintype ι] (e : ι → Plane)
    (i j : Fin 2) (ξ : ℝ) :
    charFun (cornerMatrix e i j) ξ = ∑ k, charFun (cornerAtom (e k) i j) ξ := by
  first
  | simp only [charFun_eq_integral_innerProbChar, cornerMatrix]
    exact integral_finsetSum_measure (fun k _ =>
      (BoundedContinuousFunction.innerProbChar ξ).integrable (cornerAtom (e k) i j))

theorem interactionEdge_axis_left {b c : Plane} (hb : b.1 = 0 ∨ b.2 = 0) :
    (interactionEdge b c).1 = 0 ∨ (interactionEdge b c).2 = 0 := by
  first
  | rcases hb with hb | hb
    · left
      simp [interactionEdge, hb]
    · left
      unfold interactionEdge
      split_ifs <;> simp [hb]

theorem interactionEdge_axis_right {b c : Plane} (hc : c.1 = 0 ∨ c.2 = 0) :
    (interactionEdge b c).1 = 0 ∨ (interactionEdge b c).2 = 0 := by
  first
  | rcases hc with hc | hc
    · left
      simp [interactionEdge, hc]
    · right
      unfold interactionEdge
      split_ifs <;> simp [hc]

theorem interactionEdge_weight {b c : Plane} (h : 0 < b.1 * c.1) :
    (atomWeight (interactionEdge b c) : ℝ) =
      (atomWeight b : ℝ) * (atomWeight c : ℝ) := by
  first
  | change Real.sqrt (|(interactionEdge b c).1| * |(interactionEdge b c).2|) =
      Real.sqrt (|b.1| * |b.2|) * Real.sqrt (|c.1| * |c.2|)
    rw [show interactionEdge b c = (-|c.1| * b.2, |b.1| * c.2) from
      by simp only [interactionEdge, if_pos h]]
    simp only [abs_mul, abs_neg, abs_abs]
    rw [← Real.sqrt_mul (mul_nonneg (abs_nonneg b.1) (abs_nonneg b.2))]
    congr 1
    ring

theorem interactionEdge_slope {b c : Plane} (h : 0 < b.1 * c.1)
    (hb : b.2 ≠ 0) (hc : c.2 ≠ 0) :
    atomSlope (interactionEdge b c) = atomSlope c - atomSlope b := by
  first
  | have hb1 : b.1 ≠ 0 := fun hb1 => by simp [hb1] at h
    have hc1 : c.1 ≠ 0 := fun hc1 => by simp [hc1] at h
    simp only [atomSlope, interactionEdge, if_pos h, abs_mul, abs_neg, abs_abs]
    rw [Real.log_div (mul_ne_zero (abs_ne_zero.mpr hb1) (abs_ne_zero.mpr hc))
        (mul_ne_zero (abs_ne_zero.mpr hc1) (abs_ne_zero.mpr hb)),
      Real.log_mul (abs_ne_zero.mpr hb1) (abs_ne_zero.mpr hc),
      Real.log_mul (abs_ne_zero.mpr hc1) (abs_ne_zero.mpr hb),
      Real.log_div (abs_ne_zero.mpr hc) (abs_ne_zero.mpr hc1),
      Real.log_div (abs_ne_zero.mpr hb) (abs_ne_zero.mpr hb1)]
    ring

theorem charFun_interactionAtom {b c : Plane} (h : 0 < b.1 * c.1) (ξ : ℝ) :
    charFun (slopeAtom (interactionEdge b c)) ξ =
      conj (charFun (slopeAtom b) ξ) * charFun (slopeAtom c) ξ := by
  first
  | by_cases hb : b.2 = 0
    · rw [slopeAtom_axis (interactionEdge_axis_left (Or.inr hb)),
        slopeAtom_axis (Or.inr hb)]
      simp
    by_cases hc : c.2 = 0
    · rw [slopeAtom_axis (interactionEdge_axis_right (Or.inr hc)),
        slopeAtom_axis (Or.inr hc)]
      simp
    rw [← charFun_neg, charFun_slopeAtom, charFun_slopeAtom, charFun_slopeAtom]
    have hw := interactionEdge_weight h
    have hwc : (atomWeight (interactionEdge b c) : ℂ) =
        (atomWeight b : ℂ) * (atomWeight c : ℂ) := by exact_mod_cast hw
    rw [hwc, interactionEdge_slope h hb hc]
    have he : (((ξ * (atomSlope c - atomSlope b) : ℝ) : ℂ) * Complex.I) =
        (((-ξ * atomSlope b : ℝ) : ℂ) * Complex.I) +
        (((ξ * atomSlope c : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_add]
    ring

theorem cornerAtom_fourier_product_sum (b c : Plane) (j k : Fin 2) (ξ : ℝ) :
    (∑ i, conj (charFun (cornerAtom b i j) ξ) * charFun (cornerAtom c i k) ξ) =
      if signIndex b.1 = signIndex c.1 ∧ signIndex b.2 = j ∧ signIndex c.2 = k
        then conj (charFun (slopeAtom b) ξ) * charFun (slopeAtom c) ξ else 0 := by
  first
  | have hterm (i : Fin 2) :
        conj (charFun (cornerAtom b i j) ξ) * charFun (cornerAtom c i k) ξ =
          if signIndex b.1 = i then
            (if signIndex b.1 = signIndex c.1 ∧ signIndex b.2 = j ∧ signIndex c.2 = k
              then conj (charFun (slopeAtom b) ξ) * charFun (slopeAtom c) ξ else 0) else 0 := by
      first
      | rw [charFun_cornerAtom, charFun_cornerAtom]
        by_cases hi : signIndex b.1 = i
        · subst i
          by_cases hc : signIndex b.1 = signIndex c.1 <;>
            by_cases hj : signIndex b.2 = j <;> by_cases hk : signIndex c.2 = k <;>
            simp [hc, hj, hk, eq_comm]
        · simp [hi]
    simp_rw [hterm]
    simp

theorem charFun_interactionCornerAtom (b c : Plane) (i j : Fin 2) (ξ : ℝ) :
    charFun (cornerAtom (interactionEdge b c) i j) ξ =
      ∑ k, conj (charFun (cornerAtom b k (flipCorner i)) ξ) *
        charFun (cornerAtom c k j) ξ := by
  first
  | by_cases hb : b.1 = 0 ∨ b.2 = 0
    · rw [cornerAtom_axis (interactionEdge_axis_left hb)]
      simp only [cornerAtom_axis hb, charFun_zero_measure, map_zero, zero_mul,
        Finset.sum_const_zero]
    by_cases hc : c.1 = 0 ∨ c.2 = 0
    · rw [cornerAtom_axis (interactionEdge_axis_right hc)]
      simp only [cornerAtom_axis hc, charFun_zero_measure, mul_zero, Finset.sum_const_zero]
    have hb1 : b.1 ≠ 0 := fun h => hb (Or.inl h)
    have hb2 : b.2 ≠ 0 := fun h => hb (Or.inr h)
    have hc1 : c.1 ≠ 0 := fun h => hc (Or.inl h)
    have hc2 : c.2 ≠ 0 := fun h => hc (Or.inr h)
    rw [cornerAtom_fourier_product_sum]
    simp only [signIndex_eq_iff hb1 hc1]
    by_cases h : 0 < b.1 * c.1
    · have hs1 : signIndex (interactionEdge b c).1 = flipCorner (signIndex b.2) := by
        first
        | rw [interactionEdge, if_pos h]
          change signIndex (-|c.1| * b.2) = _
          rw [show -|c.1| * b.2 = |c.1| * (-b.2) by ring,
            signIndex_pos_mul (abs_pos.mpr hc1), signIndex_neg hb2]
      have hs2 : signIndex (interactionEdge b c).2 = signIndex c.2 := by
        first
        | rw [interactionEdge, if_pos h]
          exact signIndex_pos_mul (abs_pos.mpr hb1)
      rw [charFun_cornerAtom, hs1, hs2, charFun_interactionAtom h]
      simp only [flipCorner_eq_iff, h, true_and]
    · simp only [h, false_and, ite_false]
      simp [interactionEdge, h, cornerAtom_axis (e := (0 : Plane)) (Or.inl rfl)]

def cornerSwapMatrix : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if j = flipCorner i then 1 else 0

theorem cornerSwapMatrix_mul (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (cornerSwapMatrix * M) i j = M (flipCorner i) j := by
  first
  | simp [cornerSwapMatrix, Matrix.mul_apply]

theorem productEdges_fourier {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Plane) (c : κ → Plane) (ξ : ℝ) :
    slopeFourierMatrix (cornerMatrix (productEdges b c)) ξ =
      cornerSwapMatrix * (slopeFourierMatrix (cornerMatrix b) ξ)ᴴ *
        slopeFourierMatrix (cornerMatrix c) ξ := by
  first
  | ext i j
    rw [Matrix.mul_assoc, cornerSwapMatrix_mul]
    simp only [slopeFourierMatrix, charFun_cornerMatrix, productEdges,
      Fintype.sum_prod_type, charFun_interactionCornerAtom,
      Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum]
    calc
      _ = ∑ a, ∑ k, ∑ d,
          conj (charFun (cornerAtom (b a) k (flipCorner i)) ξ) *
            charFun (cornerAtom (c d) k j) ξ :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ k, ∑ a, ∑ d,
          conj (charFun (cornerAtom (b a) k (flipCorner i)) ξ) *
            charFun (cornerAtom (c d) k j) ξ := Finset.sum_comm
      _ = _ := by
        first
        | symm
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          simp only [starRingEnd_apply]

/-- Exact formula (4.10), including the four explicitly added axis edges. -/
theorem completed_productEdges_fourier {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Plane) (c : κ → Plane) (ξ : ℝ) :
    slopeFourierMatrix (cornerMatrix (completedEdges (productEdges b c))) ξ =
      cornerSwapMatrix * (slopeFourierMatrix (cornerMatrix b) ξ)ᴴ *
        slopeFourierMatrix (cornerMatrix c) ξ := by
  first
  | rw [cornerMatrix_completed, productEdges_fourier]

theorem matrixSecondTrace_cornerSwap (M : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace (cornerSwapMatrix * M) = matrixSecondTrace M := by
  first
  | simp only [matrixSecondTrace_eq_sum, cornerSwapMatrix_mul, Fin.sum_univ_two]
    norm_num [flipCorner]
    ring

theorem productEdge_secondMoment {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Plane) (c : κ → Plane) :
    slopeSecondMoment (cornerMatrix (completedEdges (productEdges b c))) =
      slopeInteractionMoment (cornerMatrix b) (cornerMatrix c) := by
  first
  | unfold slopeSecondMoment slopeInteractionMoment
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    change matrixSecondTrace (slopeFourierMatrix (cornerMatrix (completedEdges (productEdges b c))) ξ) =
      matrixSecondTrace ((slopeFourierMatrix (cornerMatrix b) ξ)ᴴ *
        slopeFourierMatrix (cornerMatrix c) ξ)
    rw [completed_productEdges_fourier, Matrix.mul_assoc, matrixSecondTrace_cornerSwap]

end VolumePolynomials.PlanarEdges
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/InteractionFourier.lean -/

/- BEGIN SOURCE: VolumePolynomials/InteractionGeometryBounds.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The area bounds for the actual product-edge body

These estimates use its proved finite edge representation and exact Fourier
matrix, followed by the arbitrary-measure contraction and fourth-moment lemmas.
The three-dimensional mixed-volume identification is a separate geometric step.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace VolumePolynomials

theorem IsEuclideanContraction.conjTranspose {F : Matrix (Fin 2) (Fin 2) ℂ}
    (hF : IsEuclideanContraction F) : IsEuclideanContraction Fᴴ := by
  first
  | rw [isEuclideanContraction_iff_operatorNorm_le_one,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map]
    exact (isEuclideanContraction_iff_operatorNorm_le_one F).mp hF

theorem matrixSecondTrace_conjTranspose (F : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace Fᴴ = matrixSecondTrace F := by
  first
  | simp only [matrixSecondTrace_eq_sum, Matrix.conjTranspose_apply,
      ← starRingEnd_apply, Complex.normSq_conj]
    exact Finset.sum_comm (f := fun i j : Fin 2 => Complex.normSq (F j i))

theorem matrixSecondTrace_mul_le_right (F G : Matrix (Fin 2) (Fin 2) ℂ)
    (hF : IsEuclideanContraction F) : matrixSecondTrace (F * G) ≤ matrixSecondTrace G := by
  first
  | rw [matrixSecondTrace_eq_sum, Finset.sum_comm, matrixSecondTrace_eq_sum]
    calc
      (∑ j, ∑ i, Complex.normSq ((F * G) i j)) ≤ ∑ j, ∑ k, Complex.normSq (G k j) := by
        first
        | apply Finset.sum_le_sum
          intro j _
          simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hF (fun k => G k j)
      _ = ∑ k, ∑ j, Complex.normSq (G k j) := Finset.sum_comm

theorem mixed_matrix_trace_le_second (F G : Matrix (Fin 2) (Fin 2) ℂ)
    (hF : IsEuclideanContraction F) (hG : IsEuclideanContraction G) :
    matrixSecondTrace (Fᴴ * G) ≤ matrixSecondTrace F ∧
      matrixSecondTrace (Fᴴ * G) ≤ matrixSecondTrace G := by
  first
  | constructor
    · have he : matrixSecondTrace (Fᴴ * G) = matrixSecondTrace (Gᴴ * F) := by
        first
        | rw [← matrixSecondTrace_conjTranspose (Fᴴ * G), Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
      rw [he]
      exact matrixSecondTrace_mul_le_right _ _ hG.conjTranspose
    · exact matrixSecondTrace_mul_le_right _ _ hF.conjTranspose

theorem slopeInteractionMoment_le_second
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ) :
    slopeInteractionMoment ρ σ ≤ slopeSecondMoment ρ ∧
      slopeInteractionMoment ρ σ ≤ slopeSecondMoment σ := by
  first
  | have hp (ξ : ℝ) := mixed_matrix_trace_le_second (slopeFourierMatrix ρ ξ)
      (slopeFourierMatrix σ ξ) (admissible_fourier_contraction ρ hρ ξ)
      (admissible_fourier_contraction σ hσ ξ)
    exact ⟨integral_mono (integrable_slopeInteractionTrace ρ σ hρ hσ)
        (integrable_slopeSecondTrace ρ) (fun ξ => (hp ξ).1),
      integral_mono (integrable_slopeInteractionTrace ρ σ hρ hσ)
        (integrable_slopeSecondTrace σ) (fun ξ => (hp ξ).2)⟩

namespace PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem productEdge_body_area_ge_inputs {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1) :
    max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤
      volume.real (Q : Set Plane) := by
  first
  | have h := slopeInteractionMoment_le_second (cornerMatrix b) (cornerMatrix c)
      (hB.admissible hBw hBh) (hC.admissible hCw hCh)
    have hQmoment := hQ.unit_second_moment hQw hQh
    rw [productEdge_secondMoment] at hQmoment
    rw [hB.unit_second_moment hBw hBh, hC.unit_second_moment hCw hCh] at h
    exact max_le (by linarith [h.1]) (by linarith [h.2])

/-- The upper logarithmic deficit in Corollary 5.3 for the literal constructed
body, with explicit absolute constants and a full real parameter interval. -/
theorem productEdge_body_logarithmic_deficit {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : 2 * δ ≤ min (1 / 64) (Real.exp (-1)))
    (hBa : volume.real (B : Set Plane) = 1 / 2 - δ)
    (hCa : volume.real (C : Set Plane) = 1 / 2 - δ) :
    1 / 2 - volume.real (Q : Set Plane) ≤ 4352 * δ ^ 2 * Real.log (1 / δ) := by
  first
  | have hb2 : slopeSecondMoment (cornerMatrix b) = 1 + 2 * δ := by
      first
      | rw [hB.unit_second_moment hBw hBh, hBa]
        ring
    have hc2 : slopeSecondMoment (cornerMatrix c) = 1 + 2 * δ := by
      first
      | rw [hC.unit_second_moment hCw hCh, hCa]
        ring
    have h := slopeInteractionMoment_logarithmic_bound (cornerMatrix b) (cornerMatrix c)
      (hB.admissible hBw hBh) (hC.admissible hCw hCh)
      (mul_pos (by norm_num) hδ) hsmall hb2 hc2
    have hQmoment := hQ.unit_second_moment hQw hQh
    rw [productEdge_secondMoment] at hQmoment
    have hlog : Real.log (1 / (2 * δ)) ≤ Real.log (1 / δ) := by
      first
      | apply Real.log_le_log (by positivity)
        exact one_div_le_one_div_of_le hδ (by linarith)
    have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4352 * δ ^ 2 by positivity)
    nlinarith

/-- The version with separate deficits is used before taking a Hausdorff
limit; inscribed approximation need not preserve the two areas exactly. -/
theorem productEdge_body_logarithmic_deficits {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1)
    {δB δC : ℝ} (hδB : 0 < δB) (hδC : 0 < δC)
    (hsmallB : 2 * δB ≤ min (1 / 64) (Real.exp (-1)))
    (hsmallC : 2 * δC ≤ min (1 / 64) (Real.exp (-1)))
    (hBa : volume.real (B : Set Plane) = 1 / 2 - δB)
    (hCa : volume.real (C : Set Plane) = 1 / 2 - δC) :
    1 / 2 - volume.real (Q : Set Plane) ≤
      2176 * (δB ^ 2 * Real.log (1 / δB) + δC ^ 2 * Real.log (1 / δC)) := by
  first
  | have hb2 : slopeSecondMoment (cornerMatrix b) = 1 + 2 * δB := by
      first
      | rw [hB.unit_second_moment hBw hBh, hBa]
        ring
    have hc2 : slopeSecondMoment (cornerMatrix c) = 1 + 2 * δC := by
      first
      | rw [hC.unit_second_moment hCw hCh, hCa]
        ring
    have hb := lemma_5_2_fourth_moment (cornerMatrix b) (hB.admissible hBw hBh)
      (mul_pos (by norm_num) hδB) hsmallB hb2
    have hc := lemma_5_2_fourth_moment (cornerMatrix c) (hC.admissible hCw hCh)
      (mul_pos (by norm_num) hδC) hsmallC hc2
    have hi := slopeInteractionMoment_le_mean (cornerMatrix b) (cornerMatrix c)
      (hB.admissible hBw hBh) (hC.admissible hCw hCh)
    have hQmoment := hQ.unit_second_moment hQw hQh
    rw [productEdge_secondMoment] at hQmoment
    have hlog (δ : ℝ) (hδ : 0 < δ) :
        δ ^ 2 * Real.log (1 / (2 * δ)) ≤ δ ^ 2 * Real.log (1 / δ) := by
      first
      | apply mul_le_mul_of_nonneg_left _ (sq_nonneg δ)
        apply Real.log_le_log (by positivity)
        exact one_div_le_one_div_of_le hδ (by linarith)
    nlinarith [hlog δB hδB, hlog δC hδC]

end PlanarEdges
end VolumePolynomials
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/InteractionGeometryBounds.lean -/

/- BEGIN SOURCE: VolumePolynomials/ThreeDimensionalMixedVolume.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Literal mixed volume in the three coordinate planes

The coordinate order is `(z,(x,y))`; its measure is the actual product Lebesgue
measure. The trilinear laws and first derivative are obtained from the proved
volume polynomial and its normalized coefficients.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

abbrev Space := ℝ × Plane

def embedXY : Plane →L[ℝ] Space where
  toFun p := (0, p)
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def embedYZ : Plane →L[ℝ] Space where
  toFun p := (p.2, (0, p.1))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def embedXZ : Plane →L[ℝ] Space where
  toFun p := (p.2, (p.1, 0))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

theorem space_finrank : finrank ℝ Space = 3 := by
  first
  | simp [Space, Plane, Module.finrank_prod, Module.finrank_self]

def mixed3 (A B C : ConvexBody Space) : ℝ := mixedVolume volume ![A, B, C]

theorem mixed3_swap_first (A B C : ConvexBody Space) : mixed3 A B C = mixed3 B A C := by
  first
  | have h := mixedVolume_reindex volume ![A, B, C] (Equiv.swap (0 : Fin 3) 1)
    have he : (fun i => (![A, B, C] : Fin 3 → ConvexBody Space) (Equiv.swap 0 1 i)) =
        ![B, A, C] := by funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [he, mixed3] using h.symm

theorem mixed3_swap_last (A B C : ConvexBody Space) : mixed3 A B C = mixed3 A C B := by
  first
  | have h := mixedVolume_reindex volume ![A, B, C] (Equiv.swap (1 : Fin 3) 2)
    have he : (fun i => (![A, B, C] : Fin 3 → ConvexBody Space) (Equiv.swap 1 2 i)) =
        ![A, C, B] := by funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [he, mixed3] using h.symm

theorem mixed3_add_first (A D B C : ConvexBody Space) :
    mixed3 (A + D) B C = mixed3 A B C + mixed3 D B C := by
  first
  | simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_add volume ![A, B, C] 0 A D

theorem mixed3_add_middle (A B D C : ConvexBody Space) :
    mixed3 A (B + D) C = mixed3 A B C + mixed3 A D C := by
  first
  | rw [mixed3_swap_first A, mixed3_add_first, mixed3_swap_first B A, mixed3_swap_first D A]

theorem mixed3_add_last (A B C D : ConvexBody Space) :
    mixed3 A B (C + D) = mixed3 A B C + mixed3 A B D := by
  first
  | rw [mixed3_swap_last A B, mixed3_add_middle, mixed3_swap_last A C B, mixed3_swap_last A D B]

theorem mixed3_smul_first (A B C : ConvexBody Space) {r : ℝ} (hr : 0 ≤ r) :
    mixed3 (r • A) B C = r * mixed3 A B C := by
  first
  | simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_smul volume ![A, B, C] 0 A hr

theorem mixed3_smul_middle (A B C : ConvexBody Space) {r : ℝ} (hr : 0 ≤ r) :
    mixed3 A (r • B) C = r * mixed3 A B C := by
  first
  | rw [mixed3_swap_first A, mixed3_smul_first B A C hr, mixed3_swap_first B A]

theorem mixed3_smul_last (A B C : ConvexBody Space) {r : ℝ} (hr : 0 ≤ r) :
    mixed3 A B (r • C) = r * mixed3 A B C := by
  first
  | rw [mixed3_swap_last A B, mixed3_smul_middle A C B hr, mixed3_swap_last A C B]

theorem mixed3_diagonal (A : ConvexBody Space) : mixed3 A A A = volume.real (A : Set Space) := by
  first
  | have he : (![A, A, A] : Fin 3 → ConvexBody Space) = fun _ => A := by
      first
      | funext i; fin_cases i <;> rfl
    simpa only [mixed3, he] using mixedVolume_diagonal volume space_finrank A

theorem mixed3_translate (A B C : ConvexBody Space) (a b c : Space) :
    mixed3 (translateBody a A) (translateBody b B) (translateBody c C) = mixed3 A B C := by
  first
  | have he : (fun i : Fin 3 => translateBody (![a, b, c] i) (![A, B, C] i)) =
        ![translateBody a A, translateBody b B, translateBody c C] := by
      first
      | funext i; fin_cases i <;> rfl
    simpa only [mixed3, he] using mixedVolume_translate volume ![A, B, C] ![a, b, c]

theorem cubic_volume_expansion (A S : ConvexBody Space) {t : ℝ} (ht : 0 ≤ t) :
    volume.real ((S + t • A : ConvexBody Space) : Set Space) =
      volume.real (S : Set Space) + 3 * t * mixed3 A S S +
        3 * t ^ 2 * mixed3 A A S + t ^ 3 * volume.real (A : Set Space) := by
  first
  | rw [← mixed3_diagonal]
    simp only [mixed3_add_first, mixed3_add_middle, mixed3_add_last,
      mixed3_smul_first _ _ _ ht, mixed3_smul_middle _ _ _ ht,
      mixed3_smul_last _ _ _ ht]
    rw [mixed3_diagonal S, mixed3_diagonal A,
      mixed3_swap_first S A S, mixed3_swap_last S S A,
      mixed3_swap_first S A S, mixed3_swap_last A S A,
      mixed3_swap_first S A A, mixed3_swap_last A S A]
    ring

theorem mixed3_hasDerivWithinAt_volume (A S : ConvexBody Space) :
    HasDerivWithinAt (fun t : ℝ => volume.real ((S + t • A : ConvexBody Space) : Set Space))
      (3 * mixed3 A S S) (Ioi 0) 0 := by
  first
  | have hd : HasDerivAt (fun t : ℝ => volume.real (S : Set Space) +
        3 * t * mixed3 A S S + 3 * t ^ 2 * mixed3 A A S +
        t ^ 3 * volume.real (A : Set Space)) (3 * mixed3 A S S) 0 := by
      first
      | convert (((hasDerivAt_const (0 : ℝ) (volume.real (S : Set Space))).add
          (((hasDerivAt_id (0 : ℝ)).const_mul 3).mul_const (mixed3 A S S))).add
          ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 3).mul_const (mixed3 A A S))).add
          (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (volume.real (A : Set Space))) using 1 <;> norm_num <;> rfl
    exact hd.hasDerivWithinAt.congr (fun t ht => cubic_volume_expansion A S ht.le)
      (cubic_volume_expansion A S le_rfl)

def triple (A B C : ConvexBody Plane) : ℝ :=
  mixed3 (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ThreeDimensionalMixedVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/CrossPlaneMixedVolume.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # Repeated mixed volumes in the coordinate planes

The coefficients are recovered from the literal two-plane Fubini formula at
two positive dilation values. Coordinate permutations preserve the actual
product measures; no proportionality factor is suppressed.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def reframeY : Space ≃L[ℝ] Space where
  toFun p := (p.2.2, (p.2.1, p.1))
  invFun p := (p.2.2, (p.2.1, p.1))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reframeX : Space ≃L[ℝ] Space where
  toFun p := (p.2.1, (p.2.2, p.1))
  invFun p := (p.2.2, (p.1, p.2.1))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem reframeX_measurePreserving : MeasurePreserving reframeX := by
  first
  | have hswap : MeasurePreserving (Prod.swap : Space → Plane × ℝ) :=
      Measure.measurePreserving_swap
    have hassoc : MeasurePreserving
        (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ Space) :=
      volume_preserving_prodAssoc
    exact hassoc.comp hswap

theorem reframeY_measurePreserving : MeasurePreserving reframeY := by
  first
  | have hswap : MeasurePreserving (Prod.swap : Plane → Plane) :=
      Measure.measurePreserving_swap
    have hinner : MeasurePreserving (Prod.map id Prod.swap : Space → Space) :=
      (MeasurePreserving.id (volume : Measure ℝ)).prod hswap
    exact reframeX_measurePreserving.comp hinner

theorem realVolume_image_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T) (S : Set E) :
    volume.real (T '' S) = volume.real S := by
  first
  | have hm := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' S)
    rw [Set.preimage_image_eq S T.injective] at hm
    exact congrArg ENNReal.toReal hm.symm

def swapBody (P : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap P

theorem swapBody_area (P : ConvexBody Plane) :
    volume.real (swapBody P : Set Plane) = volume.real (P : Set Plane) :=
  realVolume_image_equiv (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
    Measure.measurePreserving_swap _

theorem swapBody_projection (P : ConvexBody Plane) :
    PlanarExtrusion.projection (swapBody P : Set Plane) = Prod.fst '' (P : Set Plane) := by
  first
  | simp only [PlanarExtrusion.projection, swapBody, coe_mapBody, Set.image_image]
    rfl

theorem reframeY_planeSum (A B : ConvexBody Plane) :
    reframeY '' (mapBody embedXY A + mapBody embedYZ B : ConvexBody Space) =
      CrossPlaneVolume.planeSum (swapBody A : Set Plane) (B : Set Plane) := by
  first
  | change reframeY.toLinearEquiv '' (embedXY '' (A : Set Plane) + embedYZ '' (B : Set Plane)) = _
    rw [Set.image_add reframeY.toLinearEquiv]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv, Set.image_image,
      CrossPlaneVolume.planeSum, swapBody, coe_mapBody]
    congr 1

theorem reframeX_planeSum (A C : ConvexBody Plane) :
    reframeX '' (mapBody embedXY A + mapBody embedXZ C : ConvexBody Space) =
      CrossPlaneVolume.planeSum (A : Set Plane) (C : Set Plane) := by
  first
  | change reframeX.toLinearEquiv '' (embedXY '' (A : Set Plane) + embedXZ '' (C : Set Plane)) = _
    rw [Set.image_add reframeX.toLinearEquiv]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv, Set.image_image, CrossPlaneVolume.planeSum]
    rfl

theorem volume_XY_YZ (A B : ConvexBody Plane) :
    volume.real ((mapBody embedXY A + mapBody embedYZ B : ConvexBody Space) : Set Space) =
      volume.real (A : Set Plane) * height B + width A * volume.real (B : Set Plane) := by
  first
  | rw [← realVolume_image_equiv reframeY reframeY_measurePreserving,
      reframeY_planeSum, CrossPlaneVolume.realVolume_planeSum
        (swapBody A).isCompact B.isCompact (swapBody A).convex B.convex,
      swapBody_area, swapBody_projection]
    rfl

theorem volume_XY_XZ (A C : ConvexBody Plane) :
    volume.real ((mapBody embedXY A + mapBody embedXZ C : ConvexBody Space) : Set Space) =
      volume.real (A : Set Plane) * height C + height A * volume.real (C : Set Plane) := by
  first
  | rw [← realVolume_image_equiv reframeX reframeX_measurePreserving,
      reframeX_planeSum, CrossPlaneVolume.realVolume_planeSum
        A.isCompact C.isCompact A.convex C.convex]
    rfl

theorem area_zeroBody : volume.real ((0 : ConvexBody Plane) : Set Plane) = 0 := by
  first
  | change (volume ({0} : Set Plane)).toReal = 0
    simp

theorem width_zeroBody : width (0 : ConvexBody Plane) = 0 := by
  first
  | simp [width, measureReal_def]

theorem height_zeroBody : height (0 : ConvexBody Plane) = 0 := by
  first
  | simp [height, measureReal_def]

@[simp] theorem mapBody_zero (f : Plane →L[ℝ] Space) : mapBody f 0 = 0 :=
  (mapBodyHom f).map_zero

theorem volume_embedXY (A : ConvexBody Plane) : volume.real (mapBody embedXY A : Set Space) = 0 := by
  first
  | have h := volume_XY_YZ A 0
    simpa only [mapBody_zero, add_zero, height_zeroBody, area_zeroBody, mul_zero, add_zero] using h

theorem volume_embedYZ (B : ConvexBody Plane) : volume.real (mapBody embedYZ B : Set Space) = 0 := by
  first
  | have h := volume_XY_YZ 0 B
    simpa only [mapBody_zero, zero_add, width_zeroBody, area_zeroBody, zero_mul, zero_add] using h

theorem volume_embedXZ (C : ConvexBody Plane) : volume.real (mapBody embedXZ C : Set Space) = 0 := by
  first
  | have h := volume_XY_XZ 0 C
    simpa only [mapBody_zero, zero_add, height_zeroBody, area_zeroBody, zero_mul, zero_add] using h

theorem repeated_XY_YZ (A B : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedYZ B) =
      volume.real (B : Set Plane) * width A := by
  first
  | let A' := mapBody embedXY A
    let B' := mapBody embedYZ B
    have h1 := cubic_volume_expansion B' A' (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := cubic_volume_expansion B' A' (by norm_num : (0 : ℝ) ≤ 2)
    have hp1 := volume_XY_YZ A B
    have hp2 := volume_XY_YZ A ((2 : ℝ) • B)
    rw [mapBody_smul] at hp2
    rw [height_smul B (by norm_num : (0 : ℝ) ≤ 2),
      haar_real_smul_body volume B (by norm_num : (0 : ℝ) ≤ 2), plane_finrank] at hp2
    have hA : volume.real (A' : Set Space) = 0 := volume_embedXY A
    have hB : volume.real (B' : Set Space) = 0 := volume_embedYZ B
    rw [hA, hB] at h1 h2
    have hB1 : (1 : ℝ) • B' = B' := one_smul ℝ B'
    rw [hB1] at h1
    simp only [one_pow, mul_zero, add_zero, zero_add] at h1
    have hsym : mixed3 B' B' A' = mixed3 A' B' B' := by
      first
      | rw [mixed3_swap_last B' B' A', mixed3_swap_first B' A' B']
    rw [hsym] at h1 h2
    change volume.real ((A' + B' : ConvexBody Space) : Set Space) = _ at hp1
    change volume.real ((A' + (2 : ℝ) • B' : ConvexBody Space) : Set Space) = _ at hp2
    dsimp only [A', B'] at h1 h2 hp1 hp2
    nlinarith

theorem repeated_XY_XZ (A C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedXZ C) =
      volume.real (C : Set Plane) * height A := by
  first
  | let A' := mapBody embedXY A
    let C' := mapBody embedXZ C
    have h1 := cubic_volume_expansion C' A' (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := cubic_volume_expansion C' A' (by norm_num : (0 : ℝ) ≤ 2)
    have hp1 := volume_XY_XZ A C
    have hp2 := volume_XY_XZ A ((2 : ℝ) • C)
    rw [mapBody_smul] at hp2
    rw [height_smul C (by norm_num : (0 : ℝ) ≤ 2),
      haar_real_smul_body volume C (by norm_num : (0 : ℝ) ≤ 2), plane_finrank] at hp2
    have hA : volume.real (A' : Set Space) = 0 := volume_embedXY A
    have hC : volume.real (C' : Set Space) = 0 := volume_embedXZ C
    rw [hA, hC] at h1 h2
    have hC1 : (1 : ℝ) • C' = C' := one_smul ℝ C'
    rw [hC1] at h1
    simp only [one_pow, mul_zero, add_zero, zero_add] at h1
    have hsym : mixed3 C' C' A' = mixed3 A' C' C' := by
      first
      | rw [mixed3_swap_last C' C' A', mixed3_swap_first C' A' C']
    rw [hsym] at h1 h2
    change volume.real ((A' + C' : ConvexBody Space) : Set Space) = _ at hp1
    change volume.real ((A' + (2 : ℝ) • C' : ConvexBody Space) : Set Space) = _ at hp2
    dsimp only [A', C'] at h1 h2 hp1 hp2
    nlinarith

theorem derivative_planeSum (A B C : ConvexBody Plane) :
    HasDerivWithinAt (fun t : ℝ => volume.real
      (((mapBody embedYZ B + mapBody embedXZ C) + t • mapBody embedXY A : ConvexBody Space) : Set Space))
      (6 * triple A B C + volume.real (B : Set Plane) * width A +
        volume.real (C : Set Plane) * height A) (Ioi 0) 0 := by
  first
  | have hd := mixed3_hasDerivWithinAt_volume (mapBody embedXY A)
      (mapBody embedYZ B + mapBody embedXZ C)
    have he : 3 * mixed3 (mapBody embedXY A)
        (mapBody embedYZ B + mapBody embedXZ C) (mapBody embedYZ B + mapBody embedXZ C) =
        6 * triple A B C + volume.real (B : Set Plane) * width A +
          volume.real (C : Set Plane) * height A := by
      first
      | rw [mixed3_add_middle, mixed3_add_last, mixed3_add_last,
          mixed3_swap_last (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedYZ B)]
        have hb := repeated_XY_YZ A B
        have hc := repeated_XY_XZ A C
        dsimp only [triple]
        linarith
    rwa [he] at hd

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CrossPlaneMixedVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/AxisFunctionals.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # Rigidity of the four coordinate support terms -/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def axisNormals : Fin 4 → Plane →L[ℝ] ℝ :=
  ![normal (0, 1), normal (0, -1), normal (1, 0), normal (-1, 0)]

def AxisFunctional (F : ConvexBody Plane → ℝ) : Prop :=
  ∃ c : Fin 4 → ℝ, ∀ A, F A = ∑ i, c i * SupportGeometry.support (A : Set Plane) (axisNormals i)

theorem AxisFunctional.zero : AxisFunctional (fun _ => 0) := by
  first
  | exact ⟨fun _ => 0, by intro A; simp⟩

theorem AxisFunctional.add {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (hG : AxisFunctional G) : AxisFunctional (fun A => F A + G A) := by
  first
  | obtain ⟨c, hc⟩ := hF
    obtain ⟨d, hd⟩ := hG
    refine ⟨fun i => c i + d i, ?_⟩
    intro A
    dsimp only
    rw [hc, hd]
    simp only [add_mul, Finset.sum_add_distrib]

theorem AxisFunctional.smul {F : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (r : ℝ) : AxisFunctional (fun A => r * F A) := by
  first
  | obtain ⟨c, hc⟩ := hF
    refine ⟨fun i => r * c i, ?_⟩
    intro A
    dsimp only
    rw [hc, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

theorem AxisFunctional.neg {F : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) : AxisFunctional (fun A => -F A) := by
  first
  | simpa only [neg_one_mul] using hF.smul (-1)

theorem AxisFunctional.sub {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (hG : AxisFunctional G) : AxisFunctional (fun A => F A - G A) := by
  first
  | simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem AxisFunctional.sum {ι : Type*} [Fintype ι]
    {F : ι → ConvexBody Plane → ℝ} (hF : ∀ i, AxisFunctional (F i)) :
    AxisFunctional (fun A => ∑ i, F i A) := by
  first
  | choose c hc using hF
    refine ⟨fun j => ∑ i, c i j, ?_⟩
    intro A
    simp_rw [hc]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]

theorem AxisFunctional.congr {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (h : ∀ A, F A = G A) : AxisFunctional G := by
  first
  | obtain ⟨c, hc⟩ := hF
    exact ⟨c, fun A => (h A).symm.trans (hc A)⟩

theorem axisFunctional_support (i : Fin 4) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (axisNormals i)) := by
  first
  | refine ⟨Pi.single i 1, ?_⟩
    intro A
    simp [Pi.single_apply]

theorem axisFunctional_support_normal_X (r : ℝ) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (normal (0, r))) := by
  first
  | have h := ((axisFunctional_support 0).smul (max r 0)).add
      ((axisFunctional_support 1).smul (max (-r) 0))
    apply h.congr
    intro A
    have he : r • ((0, 1) : Plane) = (0, r) := by ext <;> simp
    have hn : -((0, 1) : Plane) = (0, -1) := by ext <;> simp
    simpa only [axisNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, he, hn] using
      (support_normal_signed_smul A r (0, 1)).symm

theorem axisFunctional_support_normal_Y (r : ℝ) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (normal (r, 0))) := by
  first
  | have h := ((axisFunctional_support 2).smul (max r 0)).add
      ((axisFunctional_support 3).smul (max (-r) 0))
    apply h.congr
    intro A
    have he : r • ((1, 0) : Plane) = (r, 0) := by ext <;> simp
    have hn : -((1, 0) : Plane) = (-1, 0) := by ext <;> simp
    simpa only [axisNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, he, hn] using
      (support_normal_signed_smul A r (1, 0)).symm

theorem axisFunctional_support_normal {e : Plane} (he : e.1 = 0 ∨ e.2 = 0) :
    AxisFunctional (fun A => SupportGeometry.support (A : Set Plane) (normal e)) := by
  first
  | rcases he with he | he
    · have h : e = (0, e.2) := Prod.ext he rfl
      rw [h]
      exact axisFunctional_support_normal_X _
    · have h : e = (e.1, 0) := Prod.ext rfl he
      rw [h]
      exact axisFunctional_support_normal_Y _

theorem axisFunctional_width : AxisFunctional width := by
  first
  | apply ((axisFunctional_support 0).add (axisFunctional_support 1)).congr
    intro A
    exact support_axisX_sum A

theorem axisFunctional_height : AxisFunctional height := by
  first
  | apply ((axisFunctional_support 2).add (axisFunctional_support 3)).congr
    intro A
    exact support_axisY_sum A

/-- Translation invariance and the two unit-segment values determine an
axis-supported difference completely. Four tests suffice, even for signed
coefficients and degenerate test bodies. -/
theorem AxisFunctional.eq_zero {F : ConvexBody Plane → ℝ} (hF : AxisFunctional F)
    (hpx : F (pointBody (1, 0)) = 0) (hpy : F (pointBody (0, 1)) = 0)
    (hx : F unitX = 0) (hy : F unitY = 0) : ∀ A, F A = 0 := by
  first
  | obtain ⟨c, hc⟩ := hF
    rw [hc] at hpx hpy hx hy
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, axisNormals,
      Matrix.cons_val_zero, Matrix.cons_val_succ, support_pointBody, normal_apply,
      mul_zero, mul_one, zero_sub, sub_zero, zero_mul, neg_zero,
      support_unitX, support_unitY, abs_zero, abs_one, abs_neg] at hpx hpy hx hy
    norm_num at hpx hpy hx hy
    have h0 : c 0 = 0 := by linarith
    have h1 : c 1 = 0 := by linarith
    have h2 : c 2 = 0 := by linarith
    have h3 : c 3 = 0 := by linarith
    have hcz : ∀ i, c i = 0 := by
      intro i
      fin_cases i <;> assumption
    intro A
    rw [hc]
    simp only [hcz, zero_mul, Finset.sum_const_zero]

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AxisFunctionals.lean -/

/- BEGIN SOURCE: VolumePolynomials/RightTrianglePrism.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The six actual halfspaces of a sum of two right triangles -/

noncomputable section
open Set MeasureTheory Matrix
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem mem_rightTriangle_quotients {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (p : Plane) :
    p ∈ rightTriangle a b ↔ 0 ≤ p.1 / a ∧ 0 ≤ p.2 / b ∧ p.1 / a + p.2 / b ≤ 1 := by
  first
  | constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [diagonalLinear_apply, mul_div_cancel_left₀ _ ha,
        mul_div_cancel_left₀ _ hb] using (mem_unitTriangle q).mp hq
    · intro hp
      refine ⟨(p.1 / a, p.2 / b), (mem_unitTriangle _).mpr hp, ?_⟩
      ext <;> simp only [diagonalLinear_apply, Prod.fst, Prod.snd] <;> field_simp [ha, hb]

theorem mem_rightTriangle_slice {a b x z : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (x, z) ∈ rightTriangle a b ↔
      0 ≤ x / a ∧ x / a ≤ 1 ∧
        min b 0 * (1 - x / a) ≤ z ∧ z ≤ max b 0 * (1 - x / a) := by
  first
  | rw [mem_rightTriangle_quotients ha hb]
    rcases lt_or_gt_of_ne hb with hb | hb
    · rw [min_eq_left hb.le, max_eq_right hb.le, zero_mul]
      constructor
      · rintro ⟨hx, hz, hsum⟩
        have hzu : z / b ≤ 1 - x / a := by linarith
        have hlo := (div_le_iff_of_neg hb).mp hzu
        have hhi := (le_div_iff_of_neg hb).mp hz
        exact ⟨hx, by linarith, by nlinarith, by simpa using hhi⟩
      · rintro ⟨hx, hxu, hlo, hhi⟩
        have hz : 0 ≤ z / b := (le_div_iff_of_neg hb).mpr (by simpa using hhi)
        have hzu : z / b ≤ 1 - x / a := (div_le_iff_of_neg hb).mpr (by nlinarith)
        exact ⟨hx, hz, by linarith⟩
    · rw [min_eq_right hb.le, max_eq_left hb.le, zero_mul]
      constructor
      · rintro ⟨hx, hz, hsum⟩
        have hzu : z / b ≤ 1 - x / a := by linarith
        have hlo := (le_div_iff₀ hb).mp hz
        have hhi := (div_le_iff₀ hb).mp hzu
        exact ⟨hx, by linarith, by simpa using hlo, by nlinarith⟩
      · rintro ⟨hx, hxu, hlo, hhi⟩
        have hz : 0 ≤ z / b := (le_div_iff₀ hb).mpr (by simpa using hlo)
        have hzu : z / b ≤ 1 - x / a := (div_le_iff₀ hb).mpr (by nlinarith)
        exact ⟨hx, hz, by linarith⟩

def trianglePlaneSum (a b c d : ℝ) : ConvexBody Space :=
  mapBody embedYZ (rightTriangle a b) + mapBody embedXZ (rightTriangle c d)

theorem mem_trianglePlaneSum {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (p : Space) :
    p ∈ trianglePlaneSum a b c d ↔
      (0 ≤ p.2.1 / c ∧ p.2.1 / c ≤ 1) ∧
      (0 ≤ p.2.2 / a ∧ p.2.2 / a ≤ 1) ∧
      min b 0 * (1 - p.2.2 / a) + min d 0 * (1 - p.2.1 / c) ≤ p.1 ∧
      p.1 ≤ max b 0 * (1 - p.2.2 / a) + max d 0 * (1 - p.2.1 / c) := by
  first
  | constructor
    · rintro ⟨u, ⟨u', hu, rfl⟩, v, ⟨v', hv, rfl⟩, he⟩
      have hx : v'.1 = p.2.1 := by simpa [embedYZ, embedXZ] using congrArg (fun q : Space => q.2.1) he
      have hy : u'.1 = p.2.2 := by simpa [embedYZ, embedXZ] using congrArg (fun q : Space => q.2.2) he
      have hz : u'.2 + v'.2 = p.1 := by simpa [embedYZ, embedXZ] using congrArg Prod.fst he
      have hB := (mem_rightTriangle_slice ha hb).mp hu
      have hC := (mem_rightTriangle_slice hc hd).mp hv
      rw [hx] at hC
      rw [hy] at hB
      exact ⟨⟨hC.1, hC.2.1⟩, ⟨hB.1, hB.2.1⟩,
        by linarith [hB.2.2.1, hC.2.2.1], by linarith [hB.2.2.2, hC.2.2.2]⟩
    · rintro ⟨hx, hy, hlo, hhi⟩
      have hB : min b 0 * (1 - p.2.2 / a) ≤ max b 0 * (1 - p.2.2 / a) :=
        mul_le_mul_of_nonneg_right min_le_max (sub_nonneg.mpr hy.2)
      have hC : min d 0 * (1 - p.2.1 / c) ≤ max d 0 * (1 - p.2.1 / c) :=
        mul_le_mul_of_nonneg_right min_le_max (sub_nonneg.mpr hx.2)
      have hmem : p.1 ∈ Icc (min b 0 * (1 - p.2.2 / a)) (max b 0 * (1 - p.2.2 / a)) +
          Icc (min d 0 * (1 - p.2.1 / c)) (max d 0 * (1 - p.2.1 / c)) := by
        first
        | rw [Icc_add_Icc hB hC]
          exact ⟨hlo, hhi⟩
      obtain ⟨zB, hzB, zC, hzC, hz⟩ := hmem
      refine ⟨embedYZ (p.2.2, zB), ⟨(p.2.2, zB), ?_, rfl⟩,
        embedXZ (p.2.1, zC), ⟨(p.2.1, zC), ?_, rfl⟩, ?_⟩
      · exact (mem_rightTriangle_slice ha hb).mpr ⟨hy.1, hy.2, hzB.1, hzB.2⟩
      · exact (mem_rightTriangle_slice hc hd).mpr ⟨hx.1, hx.2, hzC.1, hzC.2⟩
      · ext <;> simp [embedYZ, embedXZ, hz]

def zCoord : Space →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ Plane
def xCoord : Space →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
  (ContinuousLinearMap.snd ℝ ℝ Plane)
def yCoord : Space →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
  (ContinuousLinearMap.snd ℝ ℝ Plane)

def prismCenter (a b c d : ℝ) : Space := ((b + d) / 3, (c / 3, a / 3))
def prismHalfHeight (b d : ℝ) : ℝ := (|b| + |d|) / 3

def upperPrismNormal (a b c d : ℝ) : Space →L[ℝ] ℝ :=
  zCoord + (max d 0 / c) • xCoord + (max b 0 / a) • yCoord

def lowerPrismNormal (a b c d : ℝ) : Space →L[ℝ] ℝ :=
  -zCoord - (min d 0 / c) • xCoord - (min b 0 / a) • yCoord

def prismNormals (a b c d : ℝ) : Fin 6 → Space →L[ℝ] ℝ :=
  ![(-3 / c) • xCoord, (3 / (2 * c)) • xCoord,
    (-3 / a) • yCoord, (3 / (2 * a)) • yCoord,
    (prismHalfHeight b d)⁻¹ • upperPrismNormal a b c d,
    (prismHalfHeight b d)⁻¹ • lowerPrismNormal a b c d]

theorem prismHalfHeight_positive {b d : ℝ} (hb : b ≠ 0) : 0 < prismHalfHeight b d := by
  first
  | unfold prismHalfHeight
    positivity

theorem upperPrismNormal_center {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    upperPrismNormal a b c d (prismCenter a b c d) = max b 0 + max d 0 - prismHalfHeight b d := by
  first
  | have hb := twice_positive_part b
    have hd := twice_positive_part d
    simp only [upperPrismNormal, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, prismCenter, zCoord, xCoord, yCoord, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    have hb' : max b 0 / a * (a / 3) = max b 0 / 3 := by field_simp [ha] <;> ring
    have hd' : max d 0 / c * (c / 3) = max d 0 / 3 := by field_simp [hc] <;> ring
    rw [hb', hd']
    dsimp only [prismHalfHeight]
    linarith

theorem lowerPrismNormal_center {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    lowerPrismNormal a b c d (prismCenter a b c d) = -min b 0 - min d 0 - prismHalfHeight b d := by
  first
  | have hb : b - 2 * min b 0 = |b| := by
      first
      | rcases le_total b 0 with hb | hb
        · rw [min_eq_left hb, abs_of_nonpos hb] <;> ring
        · rw [min_eq_right hb, abs_of_nonneg hb] <;> ring
    have hd : d - 2 * min d 0 = |d| := by
      first
      | rcases le_total d 0 with hd | hd
        · rw [min_eq_left hd, abs_of_nonpos hd] <;> ring
        · rw [min_eq_right hd, abs_of_nonneg hd] <;> ring
    simp only [lowerPrismNormal, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, prismCenter, zCoord, xCoord, yCoord,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    have hb' : min b 0 / a * (a / 3) = min b 0 / 3 := by field_simp [ha] <;> ring
    have hd' : min d 0 / c * (c / 3) = min d 0 / 3 := by field_simp [hc] <;> ring
    rw [hb', hd']
    dsimp only [prismHalfHeight]
    linarith

theorem prism_halfspace_body {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    HalfspacePyramids.body (prismNormals a b c d) =
      (translateBody (-prismCenter a b c d) (trianglePlaneSum a b c d) : Set Space) := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    ext p
    change (∀ i : Fin 6, prismNormals a b c d i p ≤ 1) ↔
      p ∈ translateBody (-prismCenter a b c d) (trianglePlaneSum a b c d)
    rw [mem_translateBody]
    have hp : p - -prismCenter a b c d = p + prismCenter a b c d := by abel
    rw [hp, mem_trianglePlaneSum ha hb hc hd]
    have hx : (p.2.1 + c / 3) / c = p.2.1 / c + 1 / 3 := by field_simp [hc] <;> ring
    have hy : (p.2.2 + a / 3) / a = p.2.2 / a + 1 / 3 := by field_simp [ha] <;> ring
    have hupper := upperPrismNormal_center (b := b) (d := d) ha hc
    have hlower := lowerPrismNormal_center (b := b) (d := d) ha hc
    have hU : upperPrismNormal a b c d (p + prismCenter a b c d) =
        p.1 + max d 0 / c * p.2.1 + max b 0 / a * p.2.2 +
          (max b 0 + max d 0 - prismHalfHeight b d) := by
      first
      | rw [map_add, hupper]
        rfl
    have hL : lowerPrismNormal a b c d (p + prismCenter a b c d) =
        -p.1 - min d 0 / c * p.2.1 - min b 0 / a * p.2.2 +
          (-min b 0 - min d 0 - prismHalfHeight b d) := by
      first
      | rw [map_add, hlower]
        rfl
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, prismNormals,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ContinuousLinearMap.smul_apply,
      smul_eq_mul, upperPrismNormal, lowerPrismNormal, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, zCoord, xCoord, yCoord,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Prod.fst_add, Prod.snd_add, prismCenter] at *
    rw [hx, hy]
    have heX : (-3 / c) * p.2.1 = -3 * (p.2.1 / c) := by ring
    have heX' : (3 / (2 * c)) * p.2.1 = (3 / 2) * (p.2.1 / c) := by field_simp [hc] <;> ring
    have heY : (-3 / a) * p.2.2 = -3 * (p.2.2 / a) := by ring
    have heY' : (3 / (2 * a)) * p.2.2 = (3 / 2) * (p.2.2 / a) := by field_simp [ha] <;> ring
    rw [heX, heX', heY, heY', ← div_eq_inv_mul, ← div_eq_inv_mul,
      div_le_one hH, div_le_one hH]
    have hca (r : ℝ) : r / a * (a / 3) = r / 3 := by field_simp [ha] <;> ring
    have hcc (r : ℝ) : r / c * (c / 3) = r / 3 := by field_simp [hc] <;> ring
    rw [hca, hcc] at hupper hlower
    simp only [div_eq_mul_inv] at *
    constructor
    · rintro ⟨h0, h1, h2, h3, h4, h5, _⟩
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_, ?_⟩ <;>
        nlinarith [hU, hL]
    · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hlo, hhi⟩
      refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, ?_, trivial⟩ <;>
        nlinarith [hU, hL]

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RightTrianglePrism.lean -/

/- BEGIN SOURCE: VolumePolynomials/PrismFirstVariation.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Actual roof and floor weights of the right-triangle prism

The two weights are recovered from actual vertical extrusion and translation
invariance. This avoids assuming a surface-measure normalization formula.
-/

noncomputable section
open Set MeasureTheory Matrix Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092
open PolytopeFirstVariation

theorem mixed3_zero_first (B C : ConvexBody Space) : mixed3 0 B C = 0 := by
  first
  | simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_zero_arg volume ![B, B, C] 0

theorem mixed3_point_first (v : Space) (B C : ConvexBody Space) : mixed3 (pointBody v) B C = 0 := by
  first
  | have h := mixed3_translate (0 : ConvexBody Space) B C v 0 0
    simp only [translateBody_zero] at h
    change mixed3 (pointBody v + 0) B C = _ at h
    simpa only [add_zero, mixed3_zero_first] using h

def verticalUnit : ConvexBody Space where
  carrier := horizontal (E := Plane) 1
  convex' := (convex_Icc (0 : ℝ) 1).prod (convex_singleton (0 : Plane))
  isCompact' := horizontal_compact 1
  nonempty' := ⟨0, ⟨by norm_num, rfl⟩⟩

theorem verticalUnit_support (l : Space →L[ℝ] ℝ) :
    SupportGeometry.support (verticalUnit : Set Space) l = max 0 (l (1, 0)) := by
  first
  | have h0 : (0 : Space) ∈ verticalUnit := ⟨by norm_num, rfl⟩
    have h1 : ((1, 0) : Space) ∈ verticalUnit := ⟨by norm_num, rfl⟩
    apply le_antisymm
    · apply SupportGeometry.support_le verticalUnit.nonempty l
      rintro p ⟨hp, hp0⟩
      have hp' : p = p.1 • ((1, 0) : Space) := by
        first
        | apply Prod.ext
          · simp
          · simpa using hp0
      rw [hp', map_smul, smul_eq_mul]
      rcases le_total 0 (l (1, 0)) with hl | hl
      · rw [max_eq_right hl]
        nlinarith [hp.2]
      · rw [max_eq_left hl]
        exact mul_nonpos_of_nonneg_of_nonpos hp.1 hl
    · apply max_le
      · simpa using SupportGeometry.le_support verticalUnit.isCompact l h0
      · exact SupportGeometry.le_support verticalUnit.isCompact l h1

theorem smul_verticalUnit {t : ℝ} (ht : 0 ≤ t) :
    ((t • verticalUnit : ConvexBody Space) : Set Space) = horizontal t := by
  first
  | by_cases ht0 : t = 0
    · subst t
      ext p
      simp [verticalUnit, horizontal, Set.mem_prod, Prod.ext_iff]
    have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    ext p
    constructor
    · rintro ⟨q, ⟨hq, hq0⟩, rfl⟩
      exact ⟨⟨mul_nonneg ht hq.1, by simpa using mul_le_mul_of_nonneg_left hq.2 ht⟩,
        by
          change t • q.2 = (0 : Plane)
          rw [show q.2 = (0 : Plane) from hq0, smul_zero]⟩
    · rintro ⟨hp, hp0⟩
      refine ⟨(p.1 / t, 0), ⟨⟨div_nonneg hp.1 ht, (div_le_one htp).mpr hp.2⟩, rfl⟩, ?_⟩
      apply Prod.ext
      · change t * (p.1 / t) = p.1
        field_simp [ht0]
      · simpa using hp0.symm

theorem mixed3_verticalUnit (S : ConvexBody Space) :
    3 * mixed3 verticalUnit S S = volume.real (PlanarExtrusion.projection (S : Set Space)) := by
  first
  | have hp := mixed3_hasDerivWithinAt_volume verticalUnit S
    have he (t : ℝ) (ht : 0 ≤ t) : volume.real ((S + t • verticalUnit : ConvexBody Space) : Set Space) =
        volume.real (S : Set Space) + t * volume.real (PlanarExtrusion.projection (S : Set Space)) := by
      first
      | change volume.real ((S : Set Space) + ((t • verticalUnit : ConvexBody Space) : Set Space)) = _
        rw [smul_verticalUnit ht]
        exact realVolume_add_horizontal S.isCompact S.convex ht
    have hd : HasDerivWithinAt (fun t : ℝ => volume.real ((S + t • verticalUnit : ConvexBody Space) : Set Space))
        (volume.real (PlanarExtrusion.projection (S : Set Space))) (Ioi 0) 0 := by
      first
      | have h := ((hasDerivAt_id (0 : ℝ)).mul_const
          (volume.real (PlanarExtrusion.projection (S : Set Space)))).const_add
          (volume.real (S : Set Space))
        simpa only [one_mul] using h.hasDerivWithinAt.congr
          (fun (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) => he t ht.le) (he 0 le_rfl)
    exact tendsto_nhds_unique
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hp)
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hd)

theorem trianglePlaneSum_projection (a b c d : ℝ) :
    PlanarExtrusion.projection (trianglePlaneSum a b c d : Set Space) =
      Icc (min 0 c) (max 0 c) ×ˢ Icc (min 0 a) (max 0 a) := by
  first
  | ext p
    constructor
    · rintro ⟨q, ⟨u, ⟨u', hu, rfl⟩, v, ⟨v', hv, rfl⟩, he⟩, hqp⟩
      have hx : v'.1 = p.1 := by
        first
        | have hh := congrArg (fun z : Space => z.2.1) he
          have hp := congrArg Prod.fst hqp
          simpa [embedYZ, embedXZ, ← hp] using hh
      have hy : u'.1 = p.2 := by
        first
        | have hh := congrArg (fun z : Space => z.2.2) he
          have hp := congrArg Prod.snd hqp
          simpa [embedYZ, embedXZ, ← hp] using hh
      exact ⟨hx ▸ (rightTriangle_bounds c d hv).1, hy ▸ (rightTriangle_bounds a b hu).1⟩
    · intro hp
      refine ⟨(0, p), ?_, rfl⟩
      refine ⟨embedYZ (p.2, 0), ⟨(p.2, 0), rightTriangle_axisX hp.2, rfl⟩,
        embedXZ (p.1, 0), ⟨(p.1, 0), rightTriangle_axisX hp.1, rfl⟩, ?_⟩
      ext <;> simp [embedYZ, embedXZ]

theorem trianglePlaneSum_projection_area (a b c d : ℝ) :
    volume.real (PlanarExtrusion.projection (trianglePlaneSum a b c d : Set Space)) = |a| * |c| := by
  first
  | rw [trianglePlaneSum_projection, Measure.volume_eq_prod, measureReal_prod_prod,
      Real.volume_real_Icc_of_le min_le_max, Real.volume_real_Icc_of_le min_le_max,
      max_sub_min_eq_abs, max_sub_min_eq_abs]
    ring

def prismRightInverse (a b c d : ℝ) : Fin 6 → Space :=
  ![(0, (-c / 3, 0)), (0, (2 * c / 3, 0)),
    (0, (0, -a / 3)), (0, (0, 2 * a / 3)),
    (prismHalfHeight b d, 0), (-prismHalfHeight b d, 0)]

theorem prism_normal_unit {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (i : Fin 6) :
    prismNormals a b c d i (prismRightInverse a b c d i) = 1 := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    fin_cases i <;>
      simp [prismNormals, prismRightInverse, upperPrismNormal, lowerPrismNormal,
        zCoord, xCoord, yCoord, ha, hc, hH.ne'] <;> field_simp [ha, hc, hH.ne'] <;> ring

theorem prismNormals_injective {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : Function.Injective (prismNormals a b c d) := by
  first
  | intro i j hij
    have hH := prismHalfHeight_positive (d := d) hb
    have hz := congrArg (fun l : Space →L[ℝ] ℝ => l (1, 0)) hij
    have hx := congrArg (fun l : Space →L[ℝ] ℝ => l (0, (1, 0))) hij
    have hy := congrArg (fun l : Space →L[ℝ] ℝ => l (0, (0, 1))) hij
    fin_cases i <;> fin_cases j
    all_goals first
    | rfl
    | exfalso
      simp [prismNormals, upperPrismNormal, lowerPrismNormal, zCoord, xCoord, yCoord] at hz hx hy
      all_goals
        try field_simp [ha, hc, hH.ne'] at hz
        try field_simp [ha, hc, hH.ne'] at hx
        try field_simp [ha, hc, hH.ne'] at hy
        nlinarith

def prismWeight (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (i : Fin 6) : ℝ :=
  canonicalFacetWeight (prismNormals a b c d) i (prismRightInverse a b c d i)
    (prism_normal_unit ha hb hc i)

theorem prism_first_variation {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (A : ConvexBody Space) :
    3 * mixed3 A (trianglePlaneSum a b c d) (trianglePlaneSum a b c d) =
      ∑ i, prismWeight a b c d ha hb hc i *
        SupportGeometry.support (A : Set Space) (prismNormals a b c d i) := by
  first
  | let S := translateBody (-prismCenter a b c d) (trianglePlaneSum a b c d)
    have hbody := prism_halfspace_body ha hb hc hd
    have hcompact : IsCompact (HalfspacePyramids.body (prismNormals a b c d)) := by
      first
      | rw [hbody]
        exact S.isCompact
    have hf := PolytopeFirstVariation.first_variation (prismNormals a b c d)
      (prismNormals_injective ha hb hc) hcompact (prismRightInverse a b c d)
      (prism_normal_unit ha hb hc) A.isCompact A.convex A.nonempty
    have hp := mixed3_hasDerivWithinAt_volume A S
    rw [hbody] at hf
    have he := tendsto_nhds_unique
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hp)
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hf)
    have ht := mixed3_translate A (trianglePlaneSum a b c d) (trianglePlaneSum a b c d)
      0 (-prismCenter a b c d) (-prismCenter a b c d)
    simp only [translateBody_zero] at ht
    change 3 * mixed3 A S S = _ at he
    rw [ht] at he
    exact he

theorem prism_roof_weights {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    prismWeight a b c d ha hb hc 4 / prismHalfHeight b d = |a| * |c| ∧
      prismWeight a b c d ha hb hc 5 / prismHalfHeight b d = |a| * |c| := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    have hsegment := prism_first_variation ha hb hc hd verticalUnit
    rw [mixed3_verticalUnit, trianglePlaneSum_projection_area] at hsegment
    have hpoint := prism_first_variation ha hb hc hd (pointBody (1, 0))
    rw [mixed3_point_first, mul_zero] at hpoint
    have hs (l : Space →L[ℝ] ℝ) : SupportGeometry.support (pointBody ((1, 0) : Space) : Set Space) l = l (1, 0) := by
      first
      | simp [SupportGeometry.support, coe_pointBody]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, verticalUnit_support, hs,
      prismNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, upperPrismNormal,
      lowerPrismNormal, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
      zCoord, xCoord, yCoord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.fst_zero, Prod.snd_zero,
      mul_zero, mul_one, zero_mul, add_zero, sub_zero,
      neg_zero, zero_sub, zero_add, mul_neg_one, one_mul, max_self, max_eq_right (inv_nonneg.mpr hH.le),
      max_eq_left (neg_nonpos.mpr (inv_nonneg.mpr hH.le))] at hsegment hpoint
    change |a| * |c| = prismWeight a b c d ha hb hc 4 * (prismHalfHeight b d)⁻¹ at hsegment
    change (0 : ℝ) = prismWeight a b c d ha hb hc 4 * (prismHalfHeight b d)⁻¹ +
      prismWeight a b c d ha hb hc 5 * -(prismHalfHeight b d)⁻¹ at hpoint
    constructor <;> simp only [div_eq_mul_inv] <;> linarith

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 14
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PrismFirstVariation.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeTransport.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # Exact transport of actual mixed volume through measure-preserving frames -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators NNReal

namespace VolumePolynomials

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  (ν : Measure F) [Measure.IsAddHaarMeasure ν]

theorem measureReal_image_measurePreserving (T : E ≃L[ℝ] F)
    (hT : MeasurePreserving T μ ν) (S : Set E) : ν.real (T '' S) = μ.real S := by
  first
  | have h := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' S)
    rw [Set.preimage_image_eq S T.injective] at h
    exact congrArg ENNReal.toReal h.symm

theorem volumePolynomial_map_measurePreserving {n : ℕ}
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T μ ν) (K : Fin n → ConvexBody E) :
    volumePolynomial ν (fun i => mapBody T.toContinuousLinearMap (K i)) = volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • mapBody T.toContinuousLinearMap (K i)) =
        mapBody T.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody T.toContinuousLinearMap (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul T.toContinuousLinearMap (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom T.toContinuousLinearMap) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    exact (measureReal_image_measurePreserving μ ν T hT _).symm

theorem mixedVolume_map_measurePreserving {n : ℕ}
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T μ ν) (K : Fin n → ConvexBody E) :
    mixedVolume ν (fun i => mapBody T.toContinuousLinearMap (K i)) = mixedVolume μ K := by
  first
  | simp only [mixedVolume, volumePolynomial_map_measurePreserving μ ν T hT K]

/-- The actual Haar conversion factor; it is positive and is not supplied as
an unverified Jacobian hypothesis. -/
def mixedVolumeFrameFactor (T : E ≃L[ℝ] F) : ℝ≥0 :=
  Measure.addHaarScalarFactor (μ.map T) ν

theorem mixedVolumeFrameFactor_pos (T : E ≃L[ℝ] F) :
    0 < mixedVolumeFrameFactor μ ν T :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem measureReal_eq_frameFactor_mul_image (T : E ≃L[ℝ] F) (S : Set E) :
    μ.real S = (mixedVolumeFrameFactor μ ν T : ℝ) * ν.real (T '' S) := by
  first
  | have hm : (μ.map T) (T '' S) = μ S := by
      first
      | change (μ.map T.toHomeomorph) (T.toHomeomorph '' S) = μ S
        rw [T.toHomeomorph.measurableEmbedding.map_apply,
          Set.preimage_image_eq S T.toHomeomorph.injective]
    have hs : μ.map T = mixedVolumeFrameFactor μ ν T • ν :=
      Measure.isAddLeftInvariant_eq_smul _ _
    have he := congrArg ENNReal.toReal hm.symm
    rw [hs, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul] at he
    simpa only [ENNReal.coe_toReal, measureReal_def] using he

theorem volumePolynomial_eq_frameFactor_mul {n : ℕ}
    (T : E ≃L[ℝ] F) (K : Fin n → ConvexBody E) :
    volumePolynomial μ K = MvPolynomial.C (mixedVolumeFrameFactor μ ν T : ℝ) *
      volumePolynomial ν (fun i => mapBody T.toContinuousLinearMap (K i)) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [map_mul, MvPolynomial.eval_C, volumePolynomial_eval ν _ t ht]
    have hsum : (∑ i, t i • mapBody T.toContinuousLinearMap (K i)) =
        mapBody T.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody T.toContinuousLinearMap (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul T.toContinuousLinearMap (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom T.toContinuousLinearMap) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    exact (measureReal_eq_frameFactor_mul_image μ ν T _).symm

theorem mixedVolume_eq_frameFactor_mul {n : ℕ}
    (T : E ≃L[ℝ] F) (K : Fin n → ConvexBody E) :
    mixedVolume μ K = (mixedVolumeFrameFactor μ ν T : ℝ) *
      mixedVolume ν (fun i => mapBody T.toContinuousLinearMap (K i)) := by
  first
  | rw [mixedVolume, volumePolynomial_eq_frameFactor_mul μ ν T K, MvPolynomial.coeff_C_mul,
      mixedVolume]
    ring

theorem volumePolynomial_map_linear {n : ℕ} (L : E →L[ℝ] E) (K : Fin n → ConvexBody E) :
    volumePolynomial μ (fun i => mapBody L (K i)) =
      MvPolynomial.C |LinearMap.det L.toLinearMap| * volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [map_mul, MvPolynomial.eval_C, volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • mapBody L (K i)) = mapBody L (∑ i, t i • K i) := by
      first
      | calc
          _ = ∑ i, mapBody L (t i • K i) := by
            first
            | exact Finset.sum_congr rfl (fun i _ => (mapBody_smul L (t i) (K i)).symm)
          _ = _ := (map_sum (mapBodyHom L) (fun i => t i • K i) Finset.univ).symm
    rw [hsum]
    have h := congrArg ENNReal.toReal (Measure.addHaar_image_linearMap μ L.toLinearMap
      ((∑ i, t i • K i : ConvexBody E) : Set E))
    simpa only [coe_mapBody, ContinuousLinearMap.coe_coe, measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h.symm

/-- Full determinant transport, including singular linear maps. -/
theorem mixedVolume_map_linear {n : ℕ} (L : E →L[ℝ] E) (K : Fin n → ConvexBody E) :
    mixedVolume μ (fun i => mapBody L (K i)) =
      |LinearMap.det L.toLinearMap| * mixedVolume μ K := by
  first
  | rw [mixedVolume, volumePolynomial_map_linear μ L K, MvPolynomial.coeff_C_mul, mixedVolume]
    ring

end VolumePolynomials
end -- closes the original EOF section from source line 14
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeTransport.lean -/

/- BEGIN SOURCE: VolumePolynomials/CoordinateMixedProjection.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # The exact mixed-area formula for a coordinate-segment argument -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def projectBase : Space →L[ℝ] Plane := ContinuousLinearMap.snd ℝ ℝ Plane

def baseBody (S : ConvexBody Space) : ConvexBody Plane := mapBody projectBase S

theorem mixed3_vertical_projection (B C : ConvexBody Space) :
    6 * mixed3 verticalUnit B C = 2 * mixedArea volume (baseBody B) (baseBody C) := by
  first
  | have h := mixed3_verticalUnit (B + C)
    have hB := mixed3_verticalUnit B
    have hC := mixed3_verticalUnit C
    have he (S : ConvexBody Space) : PlanarExtrusion.projection (S : Set Space) =
        (baseBody S : Set Plane) := rfl
    simp only [he] at h hB hC
    have hsum : baseBody (B + C) = baseBody B + baseBody C := mapBody_add projectBase B C
    rw [mixed3_add_middle, mixed3_add_last, mixed3_add_last,
      mixed3_swap_last verticalUnit C B, hsum, area_add volume plane_finrank] at h
    linarith

theorem mixed3_map_measurePreserving (T : Space ≃L[ℝ] Space) (hT : MeasurePreserving T)
    (A B C : ConvexBody Space) :
    mixed3 (mapBody T.toContinuousLinearMap A) (mapBody T.toContinuousLinearMap B)
      (mapBody T.toContinuousLinearMap C) = mixed3 A B C := by
  first
  | have he : (fun i : Fin 3 => mapBody T.toContinuousLinearMap (![A, B, C] i)) =
        ![mapBody T.toContinuousLinearMap A, mapBody T.toContinuousLinearMap B,
          mapBody T.toContinuousLinearMap C] := by funext i; fin_cases i <;> rfl
    simpa only [he, mixed3] using mixedVolume_map_measurePreserving volume volume T hT ![A, B, C]

def verticalProjection (P : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear 0 1) P

def horizontalProjection (P : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear 1 0) P

theorem verticalProjection_eq_translate (P : ConvexBody Plane) :
    ∃ v : Plane, verticalProjection P = translateBody v (rightTriangle 0 (height P)) := by
  first
  | let J := Prod.snd '' (P : Set Plane)
    have hJ : IsCompact J := P.isCompact.image continuous_snd
    have hJc : Convex ℝ J := P.convex.linear_image (LinearMap.snd ℝ ℝ ℝ)
    have hJn : J.Nonempty := P.nonempty.image Prod.snd
    have hI : J = Icc (sInf J) (sSup J) :=
      eq_Icc_of_connected_compact ⟨hJn, Real.convex_iff_isPreconnected.mp hJc⟩ hJ
    have hle : sInf J ≤ sSup J := csInf_le_csSup hJn hJ.bddBelow hJ.bddAbove
    have hheight : height P = sSup J - sInf J := by
      first
      | change volume.real J = _
        calc
          volume.real J = volume.real (Icc (sInf J) (sSup J)) := congrArg volume.real hI
          _ = _ := Real.volume_real_Icc_of_le hle
    refine ⟨(0, sInf J), ConvexBody.ext ?_⟩
    rw [coe_translateBody, rightTriangle_vertical (show 0 ≤ height P from measureReal_nonneg)]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqJ : q.2 ∈ J := ⟨q, hq, rfl⟩
      rw [hI] at hqJ
      refine ⟨(0, q.2 - sInf J), ⟨rfl, ?_⟩, ?_⟩
      · rw [hheight]
        exact ⟨by linarith [hqJ.1], by linarith [hqJ.2]⟩
      · ext <;> simp [diagonalLinear_apply] <;> ring
    · rintro ⟨q, ⟨hq0, hq⟩, rfl⟩
      change q.1 = 0 at hq0
      have hj : sInf J + q.2 ∈ J := by
        first
        | apply (congrArg (fun S : Set ℝ => sInf J + q.2 ∈ S) hI).mpr
          rw [hheight] at hq
          constructor <;> linarith [hq.1, hq.2]
      obtain ⟨r, hr, hre⟩ := hj
      refine ⟨r, hr, ?_⟩
      ext <;> simp [diagonalLinear_apply, hq0, hre]

theorem horizontalProjection_eq_translate (P : ConvexBody Plane) :
    ∃ v : Plane, horizontalProjection P = translateBody v (rightTriangle (width P) 0) := by
  first
  | let J := Prod.fst '' (P : Set Plane)
    have hJ : IsCompact J := P.isCompact.image continuous_fst
    have hJc : Convex ℝ J := P.convex.linear_image (LinearMap.fst ℝ ℝ ℝ)
    have hJn : J.Nonempty := P.nonempty.image Prod.fst
    have hI : J = Icc (sInf J) (sSup J) :=
      eq_Icc_of_connected_compact ⟨hJn, Real.convex_iff_isPreconnected.mp hJc⟩ hJ
    have hle : sInf J ≤ sSup J := csInf_le_csSup hJn hJ.bddBelow hJ.bddAbove
    have hwidth : width P = sSup J - sInf J := by
      first
      | change volume.real J = _
        calc
          volume.real J = volume.real (Icc (sInf J) (sSup J)) := congrArg volume.real hI
          _ = _ := Real.volume_real_Icc_of_le hle
    refine ⟨(sInf J, 0), ConvexBody.ext ?_⟩
    rw [coe_translateBody, rightTriangle_horizontal (show 0 ≤ width P from measureReal_nonneg)]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqJ : q.1 ∈ J := ⟨q, hq, rfl⟩
      rw [hI] at hqJ
      refine ⟨(q.1 - sInf J, 0), ⟨?_, rfl⟩, ?_⟩
      · rw [hwidth]
        exact ⟨by linarith [hqJ.1], by linarith [hqJ.2]⟩
      · ext <;> simp [diagonalLinear_apply] <;> ring
    · rintro ⟨q, ⟨hq, hq0⟩, rfl⟩
      change q.2 = 0 at hq0
      have hj : sInf J + q.1 ∈ J := by
        first
        | apply (congrArg (fun S : Set ℝ => sInf J + q.1 ∈ S) hI).mpr
          rw [hwidth] at hq
          constructor <;> linarith [hq.1, hq.2]
      obtain ⟨r, hr, hre⟩ := hj
      refine ⟨r, hr, ?_⟩
      ext <;> simp [diagonalLinear_apply, hq0, hre]

theorem mixedArea_verticalProjection (A P : ConvexBody Plane) :
    2 * mixedArea volume A (verticalProjection P) = height P * width A := by
  first
  | obtain ⟨v, hv⟩ := verticalProjection_eq_translate P
    rw [hv, mixedArea_translate_right]
    exact rightTriangle_axisY_mixedArea A measureReal_nonneg

theorem mixedArea_horizontalProjection (A P : ConvexBody Plane) :
    2 * mixedArea volume A (horizontalProjection P) = width P * height A := by
  first
  | obtain ⟨v, hv⟩ := horizontalProjection_eq_translate P
    rw [hv, mixedArea_translate_right]
    exact rightTriangle_axisX_mixedArea A measureReal_nonneg

def liftVertical : Plane →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] Plane)

theorem liftVertical_rightTriangle : mapBody liftVertical (rightTriangle 1 0) = verticalUnit := by
  first
  | apply ConvexBody.ext
    rw [coe_mapBody, rightTriangle_horizontal (by norm_num : (0 : ℝ) ≤ 1)]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, rfl⟩
    · intro hp
      refine ⟨(p.1, 0), ⟨hp.1, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact hp.2.symm

theorem liftVertical_unitX :
    mapBody liftVertical unitX = translateBody (-(1 / 2), 0) verticalUnit := by
  first
  | have h := congrArg (mapBody liftVertical) (rightTriangle_zero_right 1)
    rw [liftVertical_rightTriangle, mapBody_translate] at h
    have hc : liftVertical ((1 / 2 : ℝ) • ((1, 0) : Plane)) = (1 / 2, 0) := by ext <;> simp [liftVertical]
    rw [hc] at h
    have h' := congrArg (translateBody (-(1 / 2), 0)) h
    simpa only [translateBody_translate, show ((-(1 / 2), 0) : Space) + (1 / 2, 0) = 0 by ext <;> norm_num,
      translateBody_zero, show PlanarCorner.segmentBody (1, 0) = unitX from rfl] using h'.symm

theorem mixed3_vertical_centered (B C : ConvexBody Space) :
    6 * mixed3 (mapBody liftVertical unitX) B C =
      2 * mixedArea volume (baseBody B) (baseBody C) := by
  first
  | rw [liftVertical_unitX]
    have h := mixed3_translate verticalUnit B C (-(1 / 2), 0) 0 0
    simp only [translateBody_zero] at h
    rw [h]
    exact mixed3_vertical_projection B C

theorem reframeX_unitX : mapBody reframeX.toContinuousLinearMap (mapBody embedXY unitX) =
    mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [reframeX, embedXY, liftVertical]⟩
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [reframeX, embedXY, liftVertical]⟩

theorem reframeY_unitY : mapBody reframeY.toContinuousLinearMap (mapBody embedXY unitY) =
    mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t • ((1, 0) : Plane), ⟨t, ht, rfl⟩, ?_⟩
      ext <;> simp [reframeY, embedXY, liftVertical]
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t • ((0, 1) : Plane), ⟨t, ht, rfl⟩, ?_⟩
      ext <;> simp [reframeY, embedXY, liftVertical]

theorem base_reframeX_YZ (B : ConvexBody Plane) :
    baseBody (mapBody reframeX.toContinuousLinearMap (mapBody embedYZ B)) = B := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, coe_mapBody, Set.image_image]
    change id '' (B : Set Plane) = (B : Set Plane)
    exact Set.image_id _

theorem base_reframeX_XZ (C : ConvexBody Plane) :
    baseBody (mapBody reframeX.toContinuousLinearMap (mapBody embedXZ C)) = verticalProjection C := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, verticalProjection, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, reframeX, reframeY, embedXZ, embedYZ, diagonalLinear_apply]

theorem base_reframeY_YZ (B : ConvexBody Plane) :
    baseBody (mapBody reframeY.toContinuousLinearMap (mapBody embedYZ B)) = verticalProjection B := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, verticalProjection, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, reframeX, reframeY, embedXZ, embedYZ, diagonalLinear_apply]

theorem base_reframeY_XZ (C : ConvexBody Plane) :
    baseBody (mapBody reframeY.toContinuousLinearMap (mapBody embedXZ C)) = C := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, coe_mapBody, Set.image_image]
    change id '' (C : Set Plane) = (C : Set Plane)
    exact Set.image_id _

theorem triple_unitX (B C : ConvexBody Plane) :
    6 * triple unitX B C = width B * height C := by
  first
  | have h := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedXY unitX) (mapBody embedYZ B) (mapBody embedXZ C)
    rw [reframeX_unitX] at h
    change _ = triple unitX B C at h
    rw [← h, mixed3_vertical_centered, base_reframeX_YZ, base_reframeX_XZ,
      mixedArea_verticalProjection]
    ring

theorem triple_unitY (B C : ConvexBody Plane) :
    6 * triple unitY B C = height B * width C := by
  first
  | have h := mixed3_map_measurePreserving reframeY reframeY_measurePreserving
      (mapBody embedXY unitY) (mapBody embedYZ B) (mapBody embedXZ C)
    rw [reframeY_unitY] at h
    change _ = triple unitY B C at h
    rw [← h, mixed3_vertical_centered, base_reframeY_YZ, base_reframeY_XZ,
      mixedArea_symm, mixedArea_verticalProjection]

theorem base_XY (A : ConvexBody Plane) : baseBody (mapBody embedXY A) = A := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, coe_mapBody, Set.image_image]
    change id '' (A : Set Plane) = (A : Set Plane)
    exact Set.image_id _

theorem base_YZ (B : ConvexBody Plane) :
    baseBody (mapBody embedYZ B) = verticalProjection (swapBody B) := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, verticalProjection, swapBody, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, embedYZ, diagonalLinear_apply]

theorem base_XZ (C : ConvexBody Plane) : baseBody (mapBody embedXZ C) = horizontalProjection C := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, horizontalProjection, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, embedXZ, diagonalLinear_apply]

theorem embedYZ_unitY : mapBody embedYZ unitY = mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, liftVertical]⟩
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (0, 1), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, liftVertical]⟩

theorem embedXZ_unitY : mapBody embedXZ unitY = mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, liftVertical]⟩
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (0, 1), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, liftVertical]⟩

theorem triple_middle_unitY (A C : ConvexBody Plane) :
    6 * triple A unitY C = height A * width C := by
  first
  | rw [triple, embedYZ_unitY, mixed3_swap_first, mixed3_vertical_centered,
      base_XY, base_XZ, mixedArea_horizontalProjection]
    ring

theorem triple_last_unitY (A B : ConvexBody Plane) :
    6 * triple A B unitY = width A * width B := by
  first
  | have hheight : height (swapBody B) = width B := by
      first
      | unfold height width swapBody
        simp only [coe_mapBody, Set.image_image]
        rfl
    rw [triple, embedXZ_unitY, mixed3_swap_last, mixed3_swap_first,
      mixed3_vertical_centered, base_XY, base_YZ, mixedArea_verticalProjection, hheight]
    ring

theorem triple_middle_unitX (A C : ConvexBody Plane) :
    6 * triple A unitX C = width A * height C := by
  first
  | have hB : mapBody embedYZ unitX = mapBody embedXY unitY := by
      first
      | apply ConvexBody.ext
        ext p
        constructor
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (0, 1), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, embedXY]⟩
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, embedXY]⟩
    have hbase : baseBody (mapBody reframeY.toContinuousLinearMap (mapBody embedXY A)) =
        horizontalProjection A := by
      first
      | apply ConvexBody.ext
        simp only [baseBody, horizontalProjection, coe_mapBody, Set.image_image]
        congr 1
        funext p
        ext <;> simp [projectBase, reframeY, embedXY, diagonalLinear_apply]
    have ht := mixed3_map_measurePreserving reframeY reframeY_measurePreserving
      (mapBody embedXY unitY) (mapBody embedXY A) (mapBody embedXZ C)
    rw [reframeY_unitY] at ht
    rw [triple, hB, mixed3_swap_first, ← ht, mixed3_vertical_centered, hbase,
      base_reframeY_XZ, mixedArea_symm, mixedArea_horizontalProjection]

theorem triple_last_unitX (A B : ConvexBody Plane) :
    6 * triple A B unitX = height A * height B := by
  first
  | have hC : mapBody embedXZ unitX = mapBody embedXY unitX := by
      first
      | apply ConvexBody.ext
        ext p
        constructor
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, embedXY]⟩
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, embedXY]⟩
    have hbase' : baseBody (mapBody reframeX.toContinuousLinearMap (mapBody embedXY A)) =
        horizontalProjection (swapBody A) := by
      first
      | apply ConvexBody.ext
        simp only [baseBody, horizontalProjection, swapBody, coe_mapBody, Set.image_image]
        congr 1
        funext p
        ext <;> simp [projectBase, reframeX, embedXY, diagonalLinear_apply]
    have hw : width (swapBody A) = height A := by
      first
      | unfold width height swapBody
        simp only [coe_mapBody, Set.image_image]
        rfl
    have ht := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedXY unitX) (mapBody embedXY A) (mapBody embedYZ B)
    rw [reframeX_unitX] at ht
    rw [triple, hC, mixed3_swap_last, mixed3_swap_first, ← ht,
      mixed3_vertical_centered, hbase', base_reframeX_YZ, mixedArea_symm,
      mixedArea_horizontalProjection, hw]


end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CoordinateMixedProjection.lean -/

/- BEGIN SOURCE: VolumePolynomials/TripleAlgebra.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # Exact trilinearity and coordinate-supported remainders -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem triple_add_middle (A B D C : ConvexBody Plane) :
    triple A (B + D) C = triple A B C + triple A D C := by
  first
  | simp only [triple, mapBody_add, mixed3_add_middle]

theorem triple_add_last (A B C D : ConvexBody Plane) :
    triple A B (C + D) = triple A B C + triple A B D := by
  first
  | simp only [triple, mapBody_add, mixed3_add_last]

theorem triple_smul_middle (A B C : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    triple A (r • B) C = r * triple A B C := by
  first
  | simp only [triple, mapBody_smul, mixed3_smul_middle _ _ _ hr]

theorem triple_smul_last (A B C : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    triple A B (r • C) = r * triple A B C := by
  first
  | simp only [triple, mapBody_smul, mixed3_smul_last _ _ _ hr]

theorem triple_translate_middle (A B C : ConvexBody Plane) (v : Plane) :
    triple A (translateBody v B) C = triple A B C := by
  first
  | have h := mixed3_translate (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      0 (embedYZ v) 0
    simpa only [triple, mapBody_translate, translateBody_zero] using h

theorem triple_translate_last (A B C : ConvexBody Plane) (v : Plane) :
    triple A B (translateBody v C) = triple A B C := by
  first
  | have h := mixed3_translate (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      0 0 (embedXZ v)
    simpa only [triple, mapBody_translate, translateBody_zero] using h

theorem triple_point (v : Plane) (B C : ConvexBody Plane) : triple (pointBody v) B C = 0 := by
  first
  | rw [triple, mapBody_pointBody, mixed3_point_first]

theorem triple_zero_middle (A C : ConvexBody Plane) : triple A 0 C = 0 := by
  first
  | rw [triple, mapBody_zero, mixed3_swap_first, mixed3_zero_first]

theorem triple_zero_last (A B : ConvexBody Plane) : triple A B 0 = 0 := by
  first
  | rw [triple, mapBody_zero, mixed3_swap_last, mixed3_swap_first, mixed3_zero_first]

theorem triple_sum_middle {ι : Type*} [Fintype ι] (A C : ConvexBody Plane)
    (B : ι → ConvexBody Plane) : triple A (∑ i, B i) C = ∑ i, triple A (B i) C := by
  first
  | classical
    have h (s : Finset ι) : triple A (∑ i ∈ s, B i) C = ∑ i ∈ s, triple A (B i) C := by
      first
      | induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty, triple_zero_middle]
        | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, triple_add_middle, ih]
    exact h Finset.univ

theorem triple_sum_last {ι : Type*} [Fintype ι] (A B : ConvexBody Plane)
    (C : ι → ConvexBody Plane) : triple A B (∑ i, C i) = ∑ i, triple A B (C i) := by
  first
  | classical
    have h (s : Finset ι) : triple A B (∑ i ∈ s, C i) = ∑ i ∈ s, triple A B (C i) := by
      first
      | induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty, triple_zero_last]
        | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, triple_add_last, ih]
    exact h Finset.univ

def AxisEquivalent (F G : ConvexBody Plane → ℝ) : Prop := AxisFunctional (fun A => F A - G A)

theorem AxisEquivalent.refl (F : ConvexBody Plane → ℝ) : AxisEquivalent F F := by
  first
  | simpa only [AxisEquivalent, sub_self] using AxisFunctional.zero

theorem AxisEquivalent.symm {F G : ConvexBody Plane → ℝ} (h : AxisEquivalent F G) :
    AxisEquivalent G F := by
  first
  | exact h.neg.congr (fun A => by ring)

theorem AxisEquivalent.trans {F G H : ConvexBody Plane → ℝ}
    (hFG : AxisEquivalent F G) (hGH : AxisEquivalent G H) : AxisEquivalent F H := by
  first
  | exact (hFG.add hGH).congr (fun A => by ring)

theorem AxisEquivalent.add {F F' G G' : ConvexBody Plane → ℝ}
    (hF : AxisEquivalent F F') (hG : AxisEquivalent G G') :
    AxisEquivalent (fun A => F A + G A) (fun A => F' A + G' A) := by
  first
  | exact (AxisFunctional.add hF hG).congr (fun A => by ring)

theorem AxisEquivalent.sum {ι : Type*} [Fintype ι]
    {F G : ι → ConvexBody Plane → ℝ} (h : ∀ i, AxisEquivalent (F i) (G i)) :
    AxisEquivalent (fun A => ∑ i, F i A) (fun A => ∑ i, G i A) := by
  first
  | change AxisFunctional (fun A => (∑ i, F i A) - ∑ i, G i A)
    apply (AxisFunctional.sum (F := fun i A => F i A - G i A) h).congr
    intro A
    exact Finset.sum_sub_distrib (s := Finset.univ) (fun i : ι => F i A) (fun i : ι => G i A)

theorem axisEquivalent_of_axisFunctional {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (hG : AxisFunctional G) : AxisEquivalent F G := hF.sub hG

theorem support_scaled_axis_pair (A : ConvexBody Plane) (v : Plane) (r : ℝ) :
    SupportGeometry.support (A : Set Plane) (normal (r • v)) +
      SupportGeometry.support (A : Set Plane) (normal (-(r • v))) =
        |r| * (SupportGeometry.support (A : Set Plane) (normal v) +
          SupportGeometry.support (A : Set Plane) (normal (-v))) := by
  first
  | have hn : -(r • v) = (-r) • v := by module
    rw [hn, support_normal_signed_smul, support_normal_signed_smul, neg_neg]
    have hsum : max r 0 + max (-r) 0 = |r| := by
      first
      | have hp := twice_positive_part r
        have hm := twice_positive_part (-r)
        rw [abs_neg] at hm
        linarith
    calc
      _ = (max r 0 + max (-r) 0) *
          (SupportGeometry.support (A : Set Plane) (normal v) +
            SupportGeometry.support (A : Set Plane) (normal (-v))) := by ring
      _ = _ := by rw [hsum]

theorem rightTriangle_axisX_eq_translate (r : ℝ) :
    ∃ v : Plane, rightTriangle r 0 = translateBody v (|r| • unitX) := by
  first
  | apply eq_translate_of_mixedArea_eq
    intro A
    have h : 2 * mixedArea volume A (rightTriangle r 0) = |r| * height A := by
      first
      | rw [rightTriangle_zero_right, mixedArea_translate_right, twice_mixedArea_segment_support]
        have he : ((r, 0) : Plane) = r • ((1, 0) : Plane) := by ext <;> simp
        rw [he, support_scaled_axis_pair]
        simpa using congrArg (|r| * ·) (support_axisY_sum A)
    rw [mixedArea_smul_right volume A unitX (abs_nonneg r)]
    rw [← twice_mixedArea_unitX A] at h
    nlinarith [h]

theorem rightTriangle_axisY_eq_translate (r : ℝ) :
    ∃ v : Plane, rightTriangle 0 r = translateBody v (|r| • unitY) := by
  first
  | apply eq_translate_of_mixedArea_eq
    intro A
    have h : 2 * mixedArea volume A (rightTriangle 0 r) = |r| * width A := by
      first
      | rw [rightTriangle_zero_left, mixedArea_translate_right, twice_mixedArea_segment_support]
        have he : ((0, r) : Plane) = r • ((0, 1) : Plane) := by ext <;> simp
        rw [he, support_scaled_axis_pair]
        simpa using congrArg (|r| * ·) (support_axisX_sum A)
    rw [mixedArea_smul_right volume A unitY (abs_nonneg r)]
    rw [← twice_mixedArea_unitY A] at h
    nlinarith [h]

theorem axisFunctional_triple_middle_triangle {b : Plane} (hb : b.1 = 0 ∨ b.2 = 0)
    (C : ConvexBody Plane) : AxisFunctional (fun A => 6 * triple A (triangleFromEdge b) C) := by
  first
  | rcases hb with hb | hb
    · have he : triangleFromEdge b = rightTriangle 0 (-b.2) := by simp [triangleFromEdge, orientation, hb]
      obtain ⟨v, hv⟩ := rightTriangle_axisY_eq_translate (-b.2)
      apply (axisFunctional_height.smul (|b.2| * width C)).congr
      intro A
      rw [he, hv, triple_translate_middle, triple_smul_middle _ _ _ (abs_nonneg _), abs_neg]
      nlinarith [congrArg (fun x : ℝ => |b.2| * x) (triple_middle_unitY A C)]
    · have he : triangleFromEdge b = rightTriangle b.1 0 := by simp [triangleFromEdge, orientation, hb]
      obtain ⟨v, hv⟩ := rightTriangle_axisX_eq_translate b.1
      apply (axisFunctional_width.smul (|b.1| * height C)).congr
      intro A
      rw [he, hv, triple_translate_middle, triple_smul_middle _ _ _ (abs_nonneg _)]
      nlinarith [congrArg (fun x : ℝ => |b.1| * x) (triple_middle_unitX A C)]

theorem axisFunctional_triple_last_triangle {c : Plane} (hc : c.1 = 0 ∨ c.2 = 0)
    (B : ConvexBody Plane) : AxisFunctional (fun A => 6 * triple A B (triangleFromEdge c)) := by
  first
  | rcases hc with hc | hc
    · have he : triangleFromEdge c = rightTriangle 0 (-c.2) := by simp [triangleFromEdge, orientation, hc]
      obtain ⟨v, hv⟩ := rightTriangle_axisY_eq_translate (-c.2)
      apply (axisFunctional_width.smul (|c.2| * width B)).congr
      intro A
      rw [he, hv, triple_translate_last, triple_smul_last _ _ _ (abs_nonneg _), abs_neg]
      nlinarith [congrArg (fun x : ℝ => |c.2| * x) (triple_last_unitY A B)]
    · have he : triangleFromEdge c = rightTriangle c.1 0 := by simp [triangleFromEdge, orientation, hc]
      obtain ⟨v, hv⟩ := rightTriangle_axisX_eq_translate c.1
      apply (axisFunctional_height.smul (|c.1| * height B)).congr
      intro A
      rw [he, hv, triple_translate_last, triple_smul_last _ _ _ (abs_nonneg _)]
      nlinarith [congrArg (fun x : ℝ => |c.1| * x) (triple_last_unitX A B)]

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/TripleAlgebra.lean -/

/- BEGIN SOURCE: VolumePolynomials/RoofInteractionAlgebra.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The exact non-axis vector contributed by the two roof facets -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def upperRoofEdge (a b c d : ℝ) : Plane :=
  (-|a| * |c| * max b 0 / a, |a| * |c| * max d 0 / c)

def lowerRoofEdge (a b c d : ℝ) : Plane :=
  (|a| * |c| * min b 0 / a, -|a| * |c| * min d 0 / c)

def upperProductEdge (b c : Plane) : Plane :=
  (if b.1 < 0 then -|c.1| * b.2 else 0, if c.1 < 0 then |b.1| * c.2 else 0)

def lowerProductEdge (b c : Plane) : Plane :=
  (if 0 < b.1 then -|c.1| * b.2 else 0, if 0 < c.1 then |b.1| * c.2 else 0)

theorem oriented_vertical_ratios {e : Plane} (hx : e.1 ≠ 0) (hy : e.2 ≠ 0) :
    |e.1| * max (-orientation e * e.2) 0 / (orientation e * e.1) =
      (if e.1 < 0 then e.2 else 0) ∧
    |e.1| * min (-orientation e * e.2) 0 / (orientation e * e.1) =
      (if 0 < e.1 then -e.2 else 0) := by
  first
  | have hprod : (-orientation e * e.2) * e.1 < 0 := by
      first
      | have h := orientation_mul_product e
        have hp := abs_pos.mpr (mul_ne_zero hx hy)
        nlinarith
    have hk := orientation_ne_zero e
    rcases lt_or_gt_of_ne hx with hx' | hx'
    · have hb : 0 < -orientation e * e.2 := by
        first
        | by_contra h
          have hn := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt h) hx'.le
          linarith
      rw [max_eq_left hb.le, min_eq_right hb.le, abs_of_neg hx',
        if_pos hx', if_neg (not_lt_of_ge hx'.le)]
      constructor
      · field_simp [hk, hx] <;> ring
      · simp
    · have hb : -orientation e * e.2 < 0 := by
        first
        | by_contra h
          have hn := mul_nonneg (le_of_not_gt h) hx'.le
          linarith
      rw [max_eq_right hb.le, min_eq_left hb.le, abs_of_pos hx',
        if_neg (not_lt_of_ge hx'.le), if_pos hx']
      constructor
      · simp
      · field_simp [hk, hx] <;> ring

theorem upperRoofEdge_oriented {b c : Plane}
    (hb1 : b.1 ≠ 0) (hb2 : b.2 ≠ 0) (hc1 : c.1 ≠ 0) (hc2 : c.2 ≠ 0) :
    upperRoofEdge (orientation b * b.1) (-orientation b * b.2)
      (orientation c * c.1) (-orientation c * c.2) = upperProductEdge b c := by
  first
  | have hb := (oriented_vertical_ratios hb1 hb2).1
    have hc := (oriented_vertical_ratios hc1 hc2).1
    have hab : |orientation b * b.1| = |b.1| := by rw [abs_mul, abs_orientation, one_mul]
    have hac : |orientation c * c.1| = |c.1| := by rw [abs_mul, abs_orientation, one_mul]
    apply Prod.ext
    · change -|orientation b * b.1| * |orientation c * c.1| *
        max (-orientation b * b.2) 0 / (orientation b * b.1) = _
      rw [hab, hac]
      calc
        _ = -|c.1| * (|b.1| * max (-orientation b * b.2) 0 / (orientation b * b.1)) := by ring
        _ = _ := by rw [hb]; split_ifs with h <;> simp [upperProductEdge, h]
    · change |orientation b * b.1| * |orientation c * c.1| *
        max (-orientation c * c.2) 0 / (orientation c * c.1) = _
      rw [hab, hac]
      calc
        _ = |b.1| * (|c.1| * max (-orientation c * c.2) 0 / (orientation c * c.1)) := by ring
        _ = _ := by rw [hc]; split_ifs with h <;> simp [upperProductEdge, h]

theorem lowerRoofEdge_oriented {b c : Plane}
    (hb1 : b.1 ≠ 0) (hb2 : b.2 ≠ 0) (hc1 : c.1 ≠ 0) (hc2 : c.2 ≠ 0) :
    lowerRoofEdge (orientation b * b.1) (-orientation b * b.2)
      (orientation c * c.1) (-orientation c * c.2) = lowerProductEdge b c := by
  first
  | have hb := (oriented_vertical_ratios hb1 hb2).2
    have hc := (oriented_vertical_ratios hc1 hc2).2
    have hab : |orientation b * b.1| = |b.1| := by rw [abs_mul, abs_orientation, one_mul]
    have hac : |orientation c * c.1| = |c.1| := by rw [abs_mul, abs_orientation, one_mul]
    apply Prod.ext
    · change |orientation b * b.1| * |orientation c * c.1| *
        min (-orientation b * b.2) 0 / (orientation b * b.1) = _
      rw [hab, hac]
      calc
        _ = |c.1| * (|b.1| * min (-orientation b * b.2) 0 / (orientation b * b.1)) := by ring
        _ = _ := by rw [hb]; split_ifs with h <;> simp [lowerProductEdge, h] <;> ring
    · change -|orientation b * b.1| * |orientation c * c.1| *
        min (-orientation c * c.2) 0 / (orientation c * c.1) = _
      rw [hab, hac]
      calc
        _ = -|b.1| * (|c.1| * min (-orientation c * c.2) 0 / (orientation c * c.1)) := by ring
        _ = _ := by rw [hc]; split_ifs with h <;> simp [lowerProductEdge, h] <;> ring

theorem roof_product_axis_equivalent {b c : Plane} (hb : b.1 ≠ 0) (hc : c.1 ≠ 0) :
    AxisEquivalent (fun A => SupportGeometry.support (A : Set Plane) (normal (upperProductEdge b c)) +
      SupportGeometry.support (A : Set Plane) (normal (lowerProductEdge b c)))
      (fun A => SupportGeometry.support (A : Set Plane) (normal (interactionEdge b c))) := by
  first
  | rcases lt_or_gt_of_ne hb with hb | hb <;> rcases lt_or_gt_of_ne hc with hc | hc
    · have hq := mul_pos_of_neg_of_neg hb hc
      have hup : upperProductEdge b c = interactionEdge b c := by
        first
        | simp [upperProductEdge, interactionEdge, hb, hc, hq]
      have hlo : lowerProductEdge b c = 0 := by
        first
        | simp [lowerProductEdge, not_lt_of_ge hb.le, not_lt_of_ge hc.le]
      rw [hup, hlo]
      simpa only [normal_zero, support_zero, add_zero, sub_self, AxisEquivalent] using AxisFunctional.zero
    · have hq : ¬0 < b.1 * c.1 := not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hb.le hc.le)
      have hu : (upperProductEdge b c).2 = 0 := by simp [upperProductEdge, not_lt_of_ge hc.le]
      have hl : (lowerProductEdge b c).1 = 0 := by simp [lowerProductEdge, not_lt_of_ge hb.le]
      have h := (axisFunctional_support_normal (Or.inr hu)).add (axisFunctional_support_normal (Or.inl hl))
      simpa only [AxisEquivalent, interactionEdge, if_neg hq, normal_zero, support_zero, sub_zero] using h
    · have hq : ¬0 < b.1 * c.1 := not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hb.le hc.le)
      have hu : (upperProductEdge b c).1 = 0 := by simp [upperProductEdge, not_lt_of_ge hb.le]
      have hl : (lowerProductEdge b c).2 = 0 := by simp [lowerProductEdge, not_lt_of_ge hc.le]
      have h := (axisFunctional_support_normal (Or.inl hu)).add (axisFunctional_support_normal (Or.inr hl))
      simpa only [AxisEquivalent, interactionEdge, if_neg hq, normal_zero, support_zero, sub_zero] using h
    · have hq := mul_pos hb hc
      have hup : upperProductEdge b c = 0 := by
        first
        | simp [upperProductEdge, not_lt_of_ge hb.le, not_lt_of_ge hc.le]
      have hlo : lowerProductEdge b c = interactionEdge b c := by
        first
        | simp [lowerProductEdge, interactionEdge, hb, hc, hq]
      rw [hup, hlo]
      simpa only [normal_zero, support_zero, zero_add, sub_self, AxisEquivalent] using AxisFunctional.zero

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RoofInteractionAlgebra.lean -/

/- BEGIN SOURCE: VolumePolynomials/PrismAxisRemainder.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Identification of the non-axis part of the actual triple mixed volume -/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem support_embedXY (A : ConvexBody Plane) (l : Space →L[ℝ] ℝ) :
    SupportGeometry.support (mapBody embedXY A : Set Space) l =
      SupportGeometry.support (A : Set Plane) (l.comp embedXY) := by
  first
  | unfold SupportGeometry.support
    rw [coe_mapBody, Set.image_image]
    rfl

theorem normal_upperRoofEdge (a b c d : ℝ) :
    normal (upperRoofEdge a b c d) =
      (|a| * |c|) • ((upperPrismNormal a b c d).comp embedXY) := by
  first
  | apply ContinuousLinearMap.ext
    intro p
    change (|a| * |c| * max d 0 / c) * p.1 - (-|a| * |c| * max b 0 / a) * p.2 =
      (|a| * |c|) * (0 + (max d 0 / c) * p.1 + (max b 0 / a) * p.2)
    ring

theorem normal_lowerRoofEdge (a b c d : ℝ) :
    normal (lowerRoofEdge a b c d) =
      (|a| * |c|) • ((lowerPrismNormal a b c d).comp embedXY) := by
  first
  | apply ContinuousLinearMap.ext
    intro p
    change (-|a| * |c| * min d 0 / c) * p.1 - (|a| * |c| * min b 0 / a) * p.2 =
      (|a| * |c|) * (-(0 : ℝ) - (min d 0 / c) * p.1 - (min b 0 / a) * p.2)
    ring

theorem prism_roof_support {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (A : ConvexBody Plane) :
    prismWeight a b c d ha hb hc 4 *
        SupportGeometry.support (A : Set Plane) ((prismNormals a b c d 4).comp embedXY) =
      SupportGeometry.support (A : Set Plane) (normal (upperRoofEdge a b c d)) ∧
    prismWeight a b c d ha hb hc 5 *
        SupportGeometry.support (A : Set Plane) ((prismNormals a b c d 5).comp embedXY) =
      SupportGeometry.support (A : Set Plane) (normal (lowerRoofEdge a b c d)) := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    have hw := prism_roof_weights ha hb hc hd
    have hsmul (r : ℝ) (l : Space →L[ℝ] ℝ) : (r • l).comp embedXY = r • (l.comp embedXY) := by
      first
      | apply ContinuousLinearMap.ext
        intro p
        rfl
    constructor
    · change prismWeight a b c d ha hb hc 4 *
        SupportGeometry.support (A : Set Plane)
          (((prismHalfHeight b d)⁻¹ • upperPrismNormal a b c d).comp embedXY) = _
      rw [hsmul, support_smul_functional _ _ (inv_nonneg.mpr hH.le), normal_upperRoofEdge,
        support_smul_functional _ _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      calc
        _ = (prismWeight a b c d ha hb hc 4 / prismHalfHeight b d) *
          SupportGeometry.support (A : Set Plane) ((upperPrismNormal a b c d).comp embedXY) := by ring
        _ = _ := by rw [hw.1]
    · change prismWeight a b c d ha hb hc 5 *
        SupportGeometry.support (A : Set Plane)
          (((prismHalfHeight b d)⁻¹ • lowerPrismNormal a b c d).comp embedXY) = _
      rw [hsmul, support_smul_functional _ _ (inv_nonneg.mpr hH.le), normal_lowerRoofEdge,
        support_smul_functional _ _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      calc
        _ = (prismWeight a b c d ha hb hc 5 / prismHalfHeight b d) *
          SupportGeometry.support (A : Set Plane) ((lowerPrismNormal a b c d).comp embedXY) := by ring
        _ = _ := by rw [hw.2]

theorem prism_axis_remainder {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    AxisEquivalent (fun A => 3 * mixed3 (mapBody embedXY A)
      (trianglePlaneSum a b c d) (trianglePlaneSum a b c d))
      (fun A => SupportGeometry.support (A : Set Plane) (normal (upperRoofEdge a b c d)) +
        SupportGeometry.support (A : Set Plane) (normal (lowerRoofEdge a b c d))) := by
  first
  | let index (i : Fin 4) : Fin 6 := ⟨i.val, by omega⟩
    let F (i : Fin 4) (A : ConvexBody Plane) := prismWeight a b c d ha hb hc (index i) *
      SupportGeometry.support (A : Set Plane) ((prismNormals a b c d (index i)).comp embedXY)
    have hF (i : Fin 4) : AxisFunctional (F i) := by
      first
      | let l := (prismNormals a b c d (index i)).comp embedXY
        have he : (edgeOfFunctional l).1 = 0 ∨ (edgeOfFunctional l).2 = 0 := by
          first
          | fin_cases i <;> simp [l, index, prismNormals, edgeOfFunctional, embedXY,
              zCoord, xCoord, yCoord]
        have hs := axisFunctional_support_normal he
        simp only [normal_edgeOfFunctional] at hs
        exact hs.smul (prismWeight a b c d ha hb hc (index i))
    apply (AxisFunctional.sum hF).congr
    intro A
    have h := prism_first_variation ha hb hc hd (mapBody embedXY A)
    simp only [support_embedXY] at h
    let G (i : Fin 6) : ℝ := prismWeight a b c d ha hb hc i *
      SupportGeometry.support (A : Set Plane) ((prismNormals a b c d i).comp embedXY)
    change 3 * mixed3 (mapBody embedXY A) (trianglePlaneSum a b c d)
      (trianglePlaneSum a b c d) = ∑ i, G i at h
    have hroof := prism_roof_support ha hb hc hd A
    change G 4 = SupportGeometry.support (A : Set Plane) (normal (upperRoofEdge a b c d)) ∧
      G 5 = SupportGeometry.support (A : Set Plane) (normal (lowerRoofEdge a b c d)) at hroof
    have hsum6 : (∑ i, G i) = G 0 + (G 1 + (G 2 + (G 3 + (G 4 + G 5)))) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl
    have hsum4 : (∑ i, F i A) = G 0 + (G 1 + (G 2 + G 3)) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl
    rw [hsum6, hroof.1, hroof.2] at h
    change (∑ i, F i A) = _
    rw [hsum4]
    linarith

theorem triple_sum_axis_difference (B C : ConvexBody Plane) :
    AxisEquivalent (fun A => 6 * triple A B C)
      (fun A => 3 * mixed3 (mapBody embedXY A)
        (mapBody embedYZ B + mapBody embedXZ C) (mapBody embedYZ B + mapBody embedXZ C)) := by
  first
  | have h := ((axisFunctional_width.smul (-volume.real (B : Set Plane))).add
      (axisFunctional_height.smul (-volume.real (C : Set Plane))))
    apply h.congr
    intro A
    dsimp only
    rw [mixed3_add_middle, mixed3_add_last, mixed3_add_last,
      mixed3_swap_last (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedYZ B)]
    have hB := repeated_XY_YZ A B
    have hC := repeated_XY_XZ A C
    dsimp only [triple]
    linarith

/-- For a pair of actual right triangles, the sole non-axis contribution is
exactly the product vector in (4.11). The remaining terms are proved to lie
in the four-dimensional coordinate support space. -/
theorem triangle_pair_axis_equivalent (b c : Plane) :
    AxisEquivalent (fun A => 6 * triple A (triangleFromEdge b) (triangleFromEdge c))
      (fun A => SupportGeometry.support (A : Set Plane) (normal (interactionEdge b c))) := by
  first
  | by_cases hb : b.1 = 0 ∨ b.2 = 0
    · exact axisEquivalent_of_axisFunctional
        (axisFunctional_triple_middle_triangle hb (triangleFromEdge c))
        (axisFunctional_support_normal (interactionEdge_axis_left hb))
    by_cases hc : c.1 = 0 ∨ c.2 = 0
    · exact axisEquivalent_of_axisFunctional
        (axisFunctional_triple_last_triangle hc (triangleFromEdge b))
        (axisFunctional_support_normal (interactionEdge_axis_right hc))
    have hb1 : b.1 ≠ 0 := fun h => hb (Or.inl h)
    have hb2 : b.2 ≠ 0 := fun h => hb (Or.inr h)
    have hc1 : c.1 ≠ 0 := fun h => hc (Or.inl h)
    have hc2 : c.2 ≠ 0 := fun h => hc (Or.inr h)
    have hab : orientation b * b.1 ≠ 0 := mul_ne_zero (orientation_ne_zero b) hb1
    have hbb : -orientation b * b.2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (orientation_ne_zero b)) hb2
    have hac : orientation c * c.1 ≠ 0 := mul_ne_zero (orientation_ne_zero c) hc1
    have hbc : -orientation c * c.2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (orientation_ne_zero c)) hc2
    have hp := prism_axis_remainder hab hbb hac hbc
    rw [upperRoofEdge_oriented hb1 hb2 hc1 hc2,
      lowerRoofEdge_oriented hb1 hb2 hc1 hc2] at hp
    exact ((triple_sum_axis_difference (triangleFromEdge b) (triangleFromEdge c)).trans hp).trans
      (roof_product_axis_equivalent hb1 hc1)

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PrismAxisRemainder.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteInteractionBody.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The genuine three-dimensional interaction identity for finite edge data

Actual Minkowski decompositions reduce arbitrary finite representations to
right-triangle pairs. Their four-axis remainder is eliminated by translation
and the two unit segments. This proves the mixed-volume identity, not merely
the existence of a body with a prescribed Fourier matrix.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem AxisEquivalent.congr {F G F' G' : ConvexBody Plane → ℝ}
    (h : AxisEquivalent F G) (hF : ∀ A, F A = F' A) (hG : ∀ A, G A = G' A) :
    AxisEquivalent F' G' := by
  first
  | apply AxisFunctional.congr h
    intro A
    rw [hF A, hG A]

theorem axisFunctional_triple_middle_rectangle (B C : ConvexBody Plane) :
    AxisFunctional (fun A => 6 * triple A (boundingRectangle B) C) := by
  first
  | have h := (axisFunctional_width.smul (width B * height C)).add
      (axisFunctional_height.smul (height B * width C))
    apply h.congr
    intro A
    rw [boundingRectangle, triple_add_middle,
      triple_smul_middle _ _ _ (show 0 ≤ width B from measureReal_nonneg),
      triple_smul_middle _ _ _ (show 0 ≤ height B from measureReal_nonneg)]
    have hx := congrArg (width B * ·) (triple_middle_unitX A C)
    have hy := congrArg (height B * ·) (triple_middle_unitY A C)
    nlinarith

theorem axisFunctional_triple_last_rectangle (B C : ConvexBody Plane) :
    AxisFunctional (fun A => 6 * triple A B (boundingRectangle C)) := by
  first
  | have h := (axisFunctional_height.smul (width C * height B)).add
      (axisFunctional_width.smul (height C * width B))
    apply h.congr
    intro A
    rw [boundingRectangle, triple_add_last,
      triple_smul_last _ _ _ (show 0 ≤ width C from measureReal_nonneg),
      triple_smul_last _ _ _ (show 0 ≤ height C from measureReal_nonneg)]
    have hx := congrArg (width C * ·) (triple_last_unitX A B)
    have hy := congrArg (height C * ·) (triple_last_unitY A B)
    nlinarith

theorem finite_representation_triple_reduction {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c) :
    AxisEquivalent (fun A => 6 * triple A B C)
      (fun A => 6 * triple A (triangleSum b) (triangleSum c)) := by
  first
  | obtain ⟨vB, hvB⟩ := hB.triangleSum_eq_translate
    obtain ⟨vC, hvC⟩ := hC.triangleSum_eq_translate
    have hR := ((axisFunctional_triple_middle_rectangle B C).add
      (axisFunctional_triple_last_rectangle B C)).add
      (axisFunctional_triple_middle_rectangle B (boundingRectangle C))
    apply hR.neg.congr
    intro A
    dsimp only
    rw [hvB, hvC, triple_translate_middle, triple_translate_last,
      triple_add_middle, triple_add_last, triple_add_last]
    ring

theorem finite_representation_product_axis {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c) :
    AxisEquivalent (fun A => 6 * triple A B C)
      (fun A => ∑ i, ∑ j, SupportGeometry.support (A : Set Plane) (normal (interactionEdge (b i) (c j)))) := by
  first
  | have hsum := AxisEquivalent.sum (fun i : ι => AxisEquivalent.sum
      (fun j : κ => triangle_pair_axis_equivalent (b i) (c j)))
    have hpair : AxisEquivalent (fun A => 6 * triple A (triangleSum b) (triangleSum c))
        (fun A => ∑ i, ∑ j, SupportGeometry.support (A : Set Plane)
          (normal (interactionEdge (b i) (c j)))) := by
      first
      | apply hsum.congr
        · intro A
          simp only [triangleSum, triple_sum_middle, triple_sum_last, Finset.mul_sum]
          rw [Finset.sum_comm]
        · intro A
          rfl
    exact (finite_representation_triple_reduction hB hC).trans hpair

theorem completed_representation_axis {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hQ : Represents Q (completedEdges (productEdges b c))) :
    AxisEquivalent (fun A => ∑ i, ∑ j,
      SupportGeometry.support (A : Set Plane) (normal (interactionEdge (b i) (c j))))
      (fun A => 2 * mixedArea volume A Q) := by
  first
  | have haxis (k : Fin 4) : AxisFunctional (fun A =>
        SupportGeometry.support (A : Set Plane) (normal (axisCompletion (productEdges b c) k))) := by
      first
      | apply axisFunctional_support_normal
        fin_cases k <;> simp [axisCompletion]
    apply (AxisFunctional.sum haxis).neg.congr
    intro A
    have h := hQ A
    simp only [completedEdges, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      productEdges, Fintype.sum_prod_type] at h
    linarith

/-- Formula (4.8) for every input with an actual finite first-variation
representation. This includes every positive-area polygon and the explicit
finite logarithmic witnesses constructed from balanced vectors. -/
theorem finite_interaction_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1) :
    ∀ A : ConvexBody Plane, 6 * triple A B C = 2 * mixedArea volume A Q := by
  first
  | have haxis := (finite_representation_product_axis hB hC).trans (completed_representation_axis hQ)
    have hpoint (v : Plane) : 6 * triple (pointBody v) B C - 2 * mixedArea volume (pointBody v) Q = 0 := by
      first
      | rw [triple_point, mixedArea_point_left]
        ring
    have hx : 6 * triple unitX B C - 2 * mixedArea volume unitX Q = 0 := by
      first
      | rw [triple_unitX, mixedArea_symm volume unitX Q, twice_mixedArea_unitX, hBw, hCh, hQh]
        norm_num
    have hy : 6 * triple unitY B C - 2 * mixedArea volume unitY Q = 0 := by
      first
      | rw [triple_unitY, mixedArea_symm volume unitY Q, twice_mixedArea_unitY, hBh, hCw, hQw]
        norm_num
    have hzero := AxisFunctional.eq_zero haxis (hpoint (1, 0)) (hpoint (0, 1)) hx hy
    intro A
    exact sub_eq_zero.mp (hzero A)

theorem finite_interaction_body {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, width Q = 1 ∧ height Q = 1 ∧
      (∀ A, 6 * triple A B C = 2 * mixedArea volume A Q) ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) ∧
      Represents Q (completedEdges (productEdges b c)) := by
  first
  | obtain ⟨Q, hQ, hQw, hQh⟩ := exists_productEdge_body hB hC hBw hBh hCw hCh
    exact ⟨Q, hQw, hQh, finite_interaction_identity hB hC hBw hBh hCw hCh hQ hQw hQh,
      productEdge_body_area_ge_inputs hB hC hBw hBh hCw hCh hQ hQw hQh, hQ⟩

/-- Proposition 4.3 for arbitrary positive-area polygons, with the literal
mixed-volume functional and ordinary coordinate widths. -/
theorem polygon_interaction_body (B C : ConvexBody Plane)
    (hB : PolytopeGeometry.IsFiniteHull (B : Set Plane))
    (hC : PolytopeGeometry.IsFiniteHull (C : Set Plane))
    (hBa : 0 < volume.real (B : Set Plane)) (hCa : 0 < volume.real (C : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, width Q = 1 ∧ height Q = 1 ∧
      (∀ A, 6 * triple A B C = 2 * mixedArea volume A Q) ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | obtain ⟨m, b, hb⟩ := exists_representation B hB hBa
    obtain ⟨n, c, hc⟩ := exists_representation C hC hCa
    obtain ⟨Q, hQw, hQh, hQV, hQa, _⟩ := finite_interaction_body hb hc hBw hBh hCw hCh
    exact ⟨Q, hQw, hQh, hQV, hQa⟩

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteInteractionBody.lean -/

/- BEGIN SOURCE: VolumePolynomials/PlanarApproximation.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # Polygon approximation with the four coordinate supports fixed

Adding four attained support points to an inscribed finite net preserves both
projection widths exactly. Thus the approximation used in the interaction
argument never changes the normalization of either input body.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials

theorem continuous_mapBody {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    Continuous (mapBody L) := by
  first
  | apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
    change Continuous (fun K : ConvexBody E =>
      (bodyToNonemptyCompacts K).map L L.continuous)
    exact (Continuous.nonemptyCompacts_map L.continuous).comp continuous_bodyToNonemptyCompacts

namespace PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092 PolytopeGeometry

theorem continuous_mixedArea_pair :
    Continuous (fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2) := by
  first
  | apply (continuous_mixedVolume volume 2).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

theorem continuous_width : Continuous (width : ConvexBody Plane → ℝ) := by
  first
  | have hp : Continuous (fun P : ConvexBody Plane => (P, unitY)) :=
      continuous_id.prodMk continuous_const
    have hm : Continuous (fun P : ConvexBody Plane => mixedArea volume P unitY) :=
      Continuous.comp'
        (f := fun P : ConvexBody Plane => (P, unitY))
        (g := fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2)
        continuous_mixedArea_pair hp
    have h : Continuous (fun P : ConvexBody Plane => (2 : ℝ) * mixedArea volume P unitY) :=
      continuous_const.mul hm
    simpa only [twice_mixedArea_unitY] using h

theorem continuous_height : Continuous (height : ConvexBody Plane → ℝ) := by
  first
  | have hp : Continuous (fun P : ConvexBody Plane => (P, unitX)) :=
      continuous_id.prodMk continuous_const
    have hm : Continuous (fun P : ConvexBody Plane => mixedArea volume P unitX) :=
      Continuous.comp'
        (f := fun P : ConvexBody Plane => (P, unitX))
        (g := fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2)
        continuous_mixedArea_pair hp
    have h : Continuous (fun P : ConvexBody Plane => (2 : ℝ) * mixedArea volume P unitX) :=
      continuous_const.mul hm
    simpa only [twice_mixedArea_unitX] using h

theorem continuous_triple (A : ConvexBody Plane) :
    Continuous (fun p : ConvexBody Plane × ConvexBody Plane => triple A p.1 p.2) := by
  first
  | apply (continuous_mixedVolume volume 3).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact (continuous_mapBody embedYZ).comp continuous_fst
    · exact (continuous_mapBody embedXZ).comp continuous_snd

theorem continuous_mixedArea_right (A : ConvexBody Plane) :
    Continuous (fun Q : ConvexBody Plane => mixedArea volume A Q) := by
  first
  | have hp : Continuous (fun Q : ConvexBody Plane => (A, Q)) :=
      continuous_const.prodMk continuous_id
    exact Continuous.comp'
      (f := fun Q : ConvexBody Plane => (A, Q))
      (g := fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2)
      continuous_mixedArea_pair hp

theorem exists_inscribed_polygon_preserving_axes (K : ConvexBody Plane)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ConvexBody Plane, IsFiniteHull (P : Set Plane) ∧ P ≤ K ∧
      width P = width K ∧ height P = height K ∧ dist P K < ε := by
  first
  | classical
    have hp : ∀ i : Fin 4, ∃ p ∈ K,
        axisNormals i p = SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | intro i
        exact BodySupport.exists_support K (axisNormals i)
    choose p hpK hps using hp
    obtain ⟨S, hSK, hS, hcover⟩ := Metric.finite_approx_of_totallyBounded
      K.isCompact.totallyBounded (ε / 2) (half_pos hε)
    let V : Set Plane := S ∪ Set.range p
    have hV : V.Finite := hS.union (Set.finite_range p)
    have hVne : V.Nonempty := ⟨p 0, Or.inr ⟨0, rfl⟩⟩
    let P := finiteHullBody V hV hVne
    have hPK : P ≤ K := by
      first
      | apply convexHull_min _ K.convex
        rintro x (hx | ⟨i, rfl⟩)
        · exact hSK hx
        · exact hpK i
    have hpP (i : Fin 4) : p i ∈ P := subset_convexHull ℝ V (Or.inr ⟨i, rfl⟩)
    have hs (i : Fin 4) : SupportGeometry.support (P : Set Plane) (axisNormals i) =
        SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | apply le_antisymm
        · exact SupportGeometry.support_le P.nonempty _
            (fun x hx => SupportGeometry.le_support K.isCompact _ (hPK hx))
        · rw [← hps i]
          exact SupportGeometry.le_support P.isCompact _ (hpP i)
    have hw : width P = width K := by
      first
      | rw [← support_axisX_sum, ← support_axisX_sum]
        exact congrArg₂ (· + ·) (hs 0) (hs 1)
    have hh : height P = height K := by
      first
      | rw [← support_axisY_sum, ← support_axisY_sum]
        exact congrArg₂ (· + ·) (hs 2) (hs 3)
    refine ⟨P, finiteHullBody_isFiniteHull V hV hVne, hPK, hw, hh, ?_⟩
    have hd : dist P K ≤ ε / 2 := by
      first
      | change hausdorffDist (P : Set Plane) (K : Set Plane) ≤ ε / 2
        apply hausdorffDist_le_of_mem_dist (half_pos hε).le
        · intro x hx
          exact ⟨x, hPK hx, by simpa using (half_pos hε).le⟩
        · intro x hx
          obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
          exact ⟨y, subset_convexHull ℝ V (Or.inl hy), (Metric.mem_ball.mp hxy).le⟩
    exact hd.trans_lt (half_lt_self hε)

theorem exists_unit_polygon_sequence (K : ConvexBody Plane)
    (hKa : 0 < volume.real (K : Set Plane)) (hKw : width K = 1) (hKh : height K = 1) :
    ∃ P : ℕ → ConvexBody Plane,
      (∀ n, IsFiniteHull (P n : Set Plane) ∧ P n ≤ K ∧
        width (P n) = 1 ∧ height (P n) = 1 ∧ 0 < volume.real (P n : Set Plane)) ∧
      Tendsto P atTop (𝓝 K) := by
  first
  | have hp (n : ℕ) := exists_inscribed_polygon_preserving_axes K
      (show 0 < 1 / ((n : ℝ) + 1) by positivity)
    choose P hpoly hPK hw hh hd using hp
    have ht : Tendsto P atTop (𝓝 K) := by
      first
      | rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
    have ha : Tendsto (fun n => volume.real (P n : Set Plane)) atTop
        (𝓝 (volume.real (K : Set Plane))) :=
      (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp ht
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ha.eventually (Ioi_mem_nhds hKa))
    refine ⟨fun n => P (n + N), ?_, ht.comp (tendsto_add_atTop_nat N)⟩
    intro n
    exact ⟨hpoly _, hPK _, (hw _).trans hKw, (hh _).trans hKh,
      hN _ (Nat.le_add_left N n)⟩

/-- Every centered body with unit widths is in one fixed compact box. This
uses the actual coordinate extrema, not a choice of a bounding rectangle
which need not have a vertex in the body. -/
theorem unit_body_subset_box (K : ConvexBody Plane) (h0 : (0 : Plane) ∈ K)
    (hw : width K = 1) (hh : height K = 1) :
    (K : Set Plane) ⊆ Icc (-1, -1) (1, 1) := by
  first
  | intro p hp
    have hpos (i : Fin 4) : 0 ≤ SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | simpa only [map_zero] using SupportGeometry.le_support K.isCompact (axisNormals i) h0
    have hx := support_axisX_sum K
    have hy := support_axisY_sum K
    rw [hw] at hx
    rw [hh] at hy
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

def centeredUnitBodies : Set (ConvexBody Plane) :=
  {Q | (0 : Plane) ∈ Q ∧ width Q = 1 ∧ height Q = 1}

theorem isCompact_centeredUnitBodies : IsCompact centeredUnitBodies := by
  first
  | have hbox := isCompact_bodies_in_compact (E := Plane)
      (isCompact_Icc : IsCompact (Icc ((-1, -1) : Plane) (1, 1)))
    have hw := isClosed_eq continuous_width (continuous_const : Continuous (fun _ : ConvexBody Plane => (1 : ℝ)))
    have hh := isClosed_eq continuous_height (continuous_const : Continuous (fun _ : ConvexBody Plane => (1 : ℝ)))
    have h := (hbox.inter_right hw).inter_right hh
    convert h using 1
    ext Q
    constructor
    · rintro ⟨h0, hqw, hqh⟩
      exact ⟨⟨⟨h0, unit_body_subset_box Q h0 hqw hqh⟩, hqw⟩, hqh⟩
    · rintro ⟨⟨⟨h0, _⟩, hqw⟩, hqh⟩
      exact ⟨h0, hqw, hqh⟩

end PlanarInteraction
end VolumePolynomials
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PlanarApproximation.lean -/

/- BEGIN SOURCE: VolumePolynomials/GeneralInteractionBody.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Proposition 4.3 for arbitrary planar convex bodies

The finite construction is passed to a Hausdorff limit in a fixed compact box.
The output identity concerns the actual mixed volumes in the three coordinate
planes. A final square thickening includes zero-area and segment inputs.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092 PolytopeGeometry

theorem area_translate (Q : ConvexBody Plane) (v : Plane) :
    volume.real (translateBody v Q : Set Plane) = volume.real (Q : Set Plane) := by
  first
  | rw [← mixedArea_diagonal volume plane_finrank, mixedArea_translate,
      mixedArea_diagonal volume plane_finrank]

theorem area_le_width_mul_height (Q : ConvexBody Plane) :
    volume.real (Q : Set Plane) ≤ width Q * height Q := by
  first
  | have hsub : (Q : Set Plane) ⊆
        (Prod.fst '' (Q : Set Plane)) ×ˢ (Prod.snd '' (Q : Set Plane)) := by
      first
      | intro p hp
        exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
    have hc := (Q.isCompact.image continuous_fst).prod (Q.isCompact.image continuous_snd)
    have h := measureReal_mono (μ := volume) hsub hc.measure_lt_top.ne
    simpa only [width, height, Measure.volume_eq_prod, measureReal_prod_prod] using h

def IsInteraction (B C Q : ConvexBody Plane) : Prop :=
  width Q = 1 ∧ height Q = 1 ∧
    ∀ A : ConvexBody Plane, 6 * triple A B C = 2 * mixedArea volume A Q

theorem IsInteraction.translate {B C Q : ConvexBody Plane}
    (h : IsInteraction B C Q) (v : Plane) : IsInteraction B C (translateBody v Q) := by
  first
  | refine ⟨(width_translate Q v).trans h.1, (height_translate Q v).trans h.2.1, ?_⟩
    intro A
    rw [mixedArea_translate_right]
    exact h.2.2 A

theorem interaction_area_unique {B C Q R : ConvexBody Plane}
    (hQ : IsInteraction B C Q) (hR : IsInteraction B C R) :
    volume.real (Q : Set Plane) = volume.real (R : Set Plane) := by
  first
  | obtain ⟨v, hv⟩ := eq_translate_of_mixedArea_eq Q R (fun A => by
      have hq := hQ.2.2 A
      have hr := hR.2.2 A
      linarith)
    rw [hv, area_translate]

theorem interaction_closed_limit {B C : ConvexBody Plane}
    (Bn Cn : ℕ → ConvexBody Plane) (hB : Tendsto Bn atTop (𝓝 B))
    (hC : Tendsto Cn atTop (𝓝 C))
    (hQ : ∀ n, ∃ Q : ConvexBody Plane, IsInteraction (Bn n) (Cn n) Q ∧
      max (volume.real (Bn n : Set Plane)) (volume.real (Cn n : Set Plane)) ≤ volume.real (Q : Set Plane)) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | choose Q hQI hQa using hQ
    choose p hp using fun n => (Q n).nonempty
    let R : ℕ → ConvexBody Plane := fun n => translateBody (-(p n)) (Q n)
    have hRI (n : ℕ) : IsInteraction (Bn n) (Cn n) (R n) := (hQI n).translate _
    have hRc (n : ℕ) : R n ∈ centeredUnitBodies :=
      ⟨zero_mem_translateBody_neg (hp n), (hRI n).1, (hRI n).2.1⟩
    have hRa (n : ℕ) : volume.real (R n : Set Plane) = volume.real (Q n : Set Plane) :=
      area_translate _ _
    obtain ⟨L, hLc, φ, hφ, hL⟩ := isCompact_centeredUnitBodies.tendsto_subseq hRc
    have hB' := hB.comp hφ.tendsto_atTop
    have hC' := hC.comp hφ.tendsto_atTop
    refine ⟨L, ⟨hLc.2.1, hLc.2.2, ?_⟩, ?_⟩
    · intro A
      have hleft := (tendsto_const_nhds (x := (6 : ℝ))).mul
        ((continuous_triple A).continuousAt.tendsto.comp (hB'.prodMk_nhds hC'))
      have hright := (tendsto_const_nhds (x := (2 : ℝ))).mul
        ((continuous_mixedArea_right A).continuousAt.tendsto.comp hL)
      exact (isClosed_eq continuous_fst continuous_snd).mem_of_tendsto
        (hleft.prodMk_nhds hright) (Filter.Eventually.of_forall (fun n => (hRI (φ n)).2.2 A))
    · have hBa := (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hB'
      have hCa := (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hC'
      have hLa := (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hL
      exact le_of_tendsto_of_tendsto (hBa.max hCa) hLa
        (Filter.Eventually.of_forall (fun n => by
          change max (volume.real (Bn (φ n) : Set Plane))
            (volume.real (Cn (φ n) : Set Plane)) ≤ volume.real (R (φ n) : Set Plane)
          rw [hRa]
          exact hQa (φ n)))

theorem interaction_body_of_positive_area (B C : ConvexBody Plane)
    (hBa : 0 < volume.real (B : Set Plane)) (hCa : 0 < volume.real (C : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | obtain ⟨Bn, hBn, hBlim⟩ := exists_unit_polygon_sequence B hBa hBw hBh
    obtain ⟨Cn, hCn, hClim⟩ := exists_unit_polygon_sequence C hCa hCw hCh
    apply interaction_closed_limit Bn Cn hBlim hClim
    intro n
    obtain ⟨Q, hQw, hQh, hQV, hQa⟩ := polygon_interaction_body (Bn n) (Cn n)
      (hBn n).1 (hCn n).1 (hBn n).2.2.2.2 (hCn n).2.2.2.2
      (hBn n).2.2.1 (hBn n).2.2.2.1 (hCn n).2.2.1 (hCn n).2.2.2.1
    exact ⟨Q, ⟨hQw, hQh, hQV⟩, hQa⟩

def unitSquare : ConvexBody Plane := unitX + unitY

theorem unitSquare_width : width unitSquare = 1 := by simp [unitSquare, width_add]
theorem unitSquare_height : height unitSquare = 1 := by simp [unitSquare, height_add]
theorem unitSquare_area : volume.real (unitSquare : Set Plane) = 1 := by
  first
  | rw [unitSquare, area_add volume plane_finrank, unitX, unitY, area_segmentBody,
      area_segmentBody]
    change 0 + 2 * mixedArea volume unitX unitY + 0 = 1
    simpa only [zero_add, add_zero] using twice_mixedArea_axes

def squareThickening (K : ConvexBody Plane) (t : ℝ) : ConvexBody Plane :=
  (1 - t) • K + t • unitSquare

theorem squareThickening_widths (K : ConvexBody Plane) (hKw : width K = 1)
    (hKh : height K = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    width (squareThickening K t) = 1 ∧ height (squareThickening K t) = 1 := by
  first
  | have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    constructor
    · rw [squareThickening, width_add, width_smul _ h1, width_smul _ ht.1,
        hKw, unitSquare_width]
      ring
    · rw [squareThickening, height_add, height_smul _ h1, height_smul _ ht.1,
        hKh, unitSquare_height]
      ring

theorem squareThickening_area_pos (K : ConvexBody Plane) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < volume.real (squareThickening K t : Set Plane) := by
  first
  | have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rw [squareThickening, area_add volume plane_finrank, area_smul _ h1,
      area_smul _ ht.1.le, unitSquare_area]
    have hm := mixedArea_nonnegative volume ((1 - t) • K) (t • unitSquare)
    have ha : 0 ≤ (1 - t) ^ 2 * volume.real (K : Set Plane) :=
      mul_nonneg (sq_nonneg _) measureReal_nonneg
    nlinarith [sq_pos_of_pos ht.1]

theorem squareThickening_tendsto (K : ConvexBody Plane) :
    Tendsto (fun n : ℕ => squareThickening K (1 / ((n : ℝ) + 1))) atTop (𝓝 K) := by
  first
  | have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h : Tendsto
        (fun n : ℕ => (1 - 1 / ((n : ℝ) + 1)) • K +
          (1 / ((n : ℝ) + 1)) • unitSquare) atTop
        (𝓝 (((1 : ℝ) - 0) • K + (0 : ℝ) • unitSquare)) :=
      (((tendsto_const_nhds (x := (1 : ℝ))).sub ht).smul
        (tendsto_const_nhds (x := K))).add
          (ht.smul (tendsto_const_nhds (x := unitSquare)))
    simpa only [sub_zero, one_smul, body_zero_smul, add_zero, squareThickening] using h

/-- Proposition 4.3, including arbitrary compact convex unit-width inputs
with zero area. The normalized mixed volumes have their ordinary Lebesgue
meaning in dimensions two and three. -/
theorem proposition_4_3 (B C : ConvexBody Plane)
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | apply interaction_closed_limit
      (fun n : ℕ => squareThickening B (1 / ((n : ℝ) + 1)))
      (fun n : ℕ => squareThickening C (1 / ((n : ℝ) + 1)))
      (squareThickening_tendsto B) (squareThickening_tendsto C)
    intro n
    have ht : (1 : ℝ) / ((n : ℝ) + 1) ∈ Ioc (0 : ℝ) 1 := by
      first
      | refine ⟨by positivity, ?_⟩
        apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
    have hB := squareThickening_widths B hBw hBh ⟨ht.1.le, ht.2⟩
    have hC := squareThickening_widths C hCw hCh ⟨ht.1.le, ht.2⟩
    exact interaction_body_of_positive_area _ _
      (squareThickening_area_pos B ht) (squareThickening_area_pos C ht)
      hB.1 hB.2 hC.1 hC.2

end VolumePolynomials.PlanarInteraction
end -- closes the original EOF section from source line 15
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/GeneralInteractionBody.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedVolumeMonotonicity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Monotonicity of genuine mixed volume for arbitrary convex bodies

The finite-polytope first-variation formula is extended first by a positive
finite-simplex thickening, then by finite-hull approximation and continuity.
All reference bodies and approximations are constructed in the actual space.
-/

noncomputable section
open Set Filter MeasureTheory Module
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finiteHull_with_zero_interior :
    ∃ P : ConvexBody E, IsFiniteHull (P : Set E) ∧ (0 : E) ∈ interior (P : Set E) := by
  first
  | classical
    let b := Module.finBasis ℝ E
    let V : Set E := insert 0 (Set.range b)
    have hV : V.Finite := (Set.finite_range b).insert 0
    have hVne : V.Nonempty := ⟨0, Set.mem_insert _ _⟩
    let Q := finiteHullBody V hV hVne
    have hspan : affineSpan ℝ (Q : Set E) = ⊤ := by
      first
      | change affineSpan ℝ (convexHull ℝ (insert 0 (Set.range b))) = ⊤
        rw [affineSpan_convexHull, affineSpan_insert_zero, b.span_eq]
        ext x <;> rfl
    obtain ⟨q, hq⟩ := Q.convex.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
    refine ⟨translateBody (-q) Q,
      isFiniteHull_translateBody (finiteHullBody_isFiniteHull V hV hVne) (-q), ?_⟩
    rw [coe_translateBody, interior_vadd]
    exact ⟨q, hq, neg_add_cancel q⟩

section Measure

variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_mono_first_finite_background {n : ℕ}
    (K : Fin n → ConvexBody E) (hn : 0 < n)
    (hK : ∀ i, IsFiniteHull (K i : Set E))
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Fin.cons A K) ≤ mixedVolume μ (Fin.cons B K) := by
  first
  | classical
    letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := inferInstanceAs (Measure.IsAddHaarMeasure μ)
    choose p hp using fun i => (K i).nonempty
    let L : Fin n → ConvexBody E := fun i => translateBody (-p i) (K i)
    have hL0 : ∀ i, (0 : E) ∈ L i := fun i => zero_mem_translateBody_neg (hp i)
    have hLpoly : ∀ i, IsFiniteHull (L i : Set E) :=
      fun i => isFiniteHull_translateBody (hK i) (-p i)
    obtain ⟨P, hPpoly, hPint⟩ := exists_finiteHull_with_zero_interior (E := E)
    have hP0 : (0 : E) ∈ P := interior_subset hPint
    let Q : ℝ → Fin n → ConvexBody E := fun r i => L i + r • P
    have hQ0 (r : ℝ) (i : Fin n) : (0 : E) ∈ Q r i :=
      ⟨0, hL0 i, 0, ⟨0, hP0, by simp⟩, zero_add 0⟩
    have hQpoly (r : ℝ) (i : Fin n) : IsFiniteHull (Q r i : Set E) :=
      (hLpoly i).add (hPpoly.smul r)
    have hQint {r : ℝ} (hr : 0 < r) :
        (0 : E) ∈ interior (∑ i, (Q r i : Set E)) := by
      first
      | have hsmall : (0 : E) ∈ interior (r • (P : Set E)) := by
          rw [interior_smul₀ hr.ne']
          exact ⟨0, hPint, by simp⟩
        have hsub : r • (P : Set E) ⊆ (↑(∑ i, Q r i) : Set E) := by
          intro x hx
          apply body_le_sum_of_zero_mem (Q r) (hQ0 r) (⟨0, hn⟩ : Fin n)
          exact ⟨0, hL0 _, x, hx, zero_add x⟩
        simpa only [coe_sum_body] using interior_mono hsub hsmall
    have hmono : ∀ᶠ r : ℝ in 𝓝[>] 0,
        mixedVolume μ (Fin.cons A (Q r)) ≤ mixedVolume μ (Fin.cons B (Q r)) := by
      first
      | filter_upwards [self_mem_nhdsWithin] with r hr
        exact mixedVolume_mono_first_of_finite_polytopes (Q r) (hQpoly r)
          (hQ0 r) (hQint hr) A B hAB
    have hcont (C : ConvexBody E) :
        Continuous (fun r : ℝ => mixedVolume μ (Fin.cons C (Q r))) := by
      first
      | apply (continuous_mixedVolume μ (n + 1)).comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using (continuous_const : Continuous (fun _ : ℝ => C))
        · simp only [Fin.cons_succ, Q]
          fun_prop
    have hlim (C : ConvexBody E) :
        Tendsto (fun r : ℝ => mixedVolume μ (Fin.cons C (Q r)))
          (𝓝[>] 0) (𝓝 (mixedVolume μ (Fin.cons C L))) := by
      first
      | simpa only [Q, body_zero_smul, add_zero] using
          ((hcont C).tendsto 0).mono_left nhdsWithin_le_nhds
    have hL := le_of_tendsto_of_tendsto (hlim A) (hlim B) hmono
    have htranslate (C : ConvexBody E) :
        mixedVolume μ (Fin.cons C L) = mixedVolume μ (Fin.cons C K) := by
      first
      | have h := mixedVolume_translate μ (Fin.cons C K) (Fin.cons (0 : E) (fun i => -p i))
        have he : (fun i : Fin (n + 1) =>
            (translateBody ((Fin.cons (0 : E) (fun j : Fin n => -p j) :
                Fin (n + 1) → E) i)
              ((Fin.cons C K : Fin (n + 1) → ConvexBody E) i) : ConvexBody E)) =
            (Fin.cons C L : Fin (n + 1) → ConvexBody E) := by
          funext i
          refine Fin.cases ?_ (fun j => rfl) i
          simp only [Fin.cons_zero, translateBody_zero]
        rwa [he] at h
    simpa only [htranslate] using hL

/-- Monotonicity in a genuine argument of dimension-matched mixed volume.
There is no full-dimensional, polytope, smoothness, or centering restriction
on any of the bodies. The background is nonempty, as in every dimension at
least two. -/
theorem mixedVolume_mono_first {n : ℕ}
    (K : Fin n → ConvexBody E) (hn : 0 < n) (_hdim : finrank ℝ E = n + 1)
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Fin.cons A K) ≤ mixedVolume μ (Fin.cons B K) := by
  first
  | let S : Set (Fin n → ConvexBody E) :=
      {L | mixedVolume μ (Fin.cons A L) ≤ mixedVolume μ (Fin.cons B L)}
    have hcont (C : ConvexBody E) :
        Continuous (fun L : Fin n → ConvexBody E => mixedVolume μ (Fin.cons C L)) := by
      first
      | apply (continuous_mixedVolume μ (n + 1)).comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact continuous_const
        · exact continuous_apply j
    have hclosed : IsClosed S := isClosed_le (hcont A) (hcont B)
    have hsub : {L : Fin n → ConvexBody E | ∀ i, IsFiniteHull (L i : Set E)} ⊆ S := by
      first
      | intro L hL
        exact mixedVolume_mono_first_finite_background μ L hn hL A B hAB
    exact closure_minimal hsub hclosed (dense_finiteHullBodyTuples (E := E) n K)

/-- The dimension-matched monotonicity theorem also includes the one-dimensional
case, where there are no background bodies and mixed volume is ordinary Haar
length. -/
theorem mixedVolume_mono_first_all {n : ℕ}
    (K : Fin n → ConvexBody E) (hdim : finrank ℝ E = n + 1)
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume μ (Fin.cons A K) ≤ mixedVolume μ (Fin.cons B K) := by
  first
  | cases n with
    | zero =>
        have hcons (C : ConvexBody E) : Fin.cons C K = fun _ : Fin 1 => C := by
          first
          | funext i
            exact Fin.cases rfl (fun j => Fin.elim0 j) i
        rw [hcons A, hcons B, mixedVolume_diagonal μ hdim A,
          mixedVolume_diagonal μ hdim B]
        exact measureReal_mono hAB B.isCompact.measure_ne_top
    | succ n =>
        exact mixedVolume_mono_first μ K (Nat.succ_pos n) hdim A B hAB

end Measure
end VolumePolynomials
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedVolumeMonotonicity.lean -/

/- BEGIN SOURCE: VolumePolynomials/TripleMinkowskiFunctional.lean -/
section


@[expose] public section

set_option autoImplicit false

/-! # Actual mixed volume as a monotone Minkowski functional -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolumeFunctional {n : ℕ} (K : Fin n → ConvexBody E)
    (hdim : finrank ℝ E = n + 1) : MinkowskiFunctional E where
  toFun A := mixedVolume μ (Fin.cons A K)
  continuous_toFun := by
    first
    | apply (continuous_mixedVolume μ (n + 1)).comp
      apply continuous_pi
      intro i
      refine Fin.cases continuous_id (fun _ => continuous_const) i
  monotone h := by
    first
    | letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
      exact mixedVolume_mono_first_all μ K hdim _ _ h
  map_add A B := by
    first
    | simpa only [Fin.update_cons_zero] using mixedVolume_add μ (Fin.cons A K) 0 A B
  map_nonneg_smul r hr A := by
    first
    | simpa only [Fin.update_cons_zero] using mixedVolume_smul μ (Fin.cons A K) 0 A hr

namespace PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner

theorem triple_add_first (A D B C : ConvexBody Plane) :
    triple (A + D) B C = triple A B C + triple D B C := by
  first
  | simp only [triple, mapBody_add, mixed3_add_first]

theorem triple_smul_first (A B C : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    triple (r • A) B C = r * triple A B C := by
  first
  | simp only [triple, mapBody_smul, mixed3_smul_first _ _ _ hr]

theorem triple_mono_first {A D : ConvexBody Plane} (B C : ConvexBody Plane)
    (hAD : A ≤ D) : triple A B C ≤ triple D B C := by
  first
  | exact mixedVolume_mono_first_all volume ![mapBody embedYZ B, mapBody embedXZ C]
      space_finrank (mapBody embedXY A) (mapBody embedXY D) (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hAD hx, rfl⟩)

theorem continuous_triple_first (B C : ConvexBody Plane) :
    Continuous (fun A : ConvexBody Plane => triple A B C) := by
  first
  | apply (continuous_mixedVolume volume 3).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_mapBody embedXY
    · exact continuous_const
    · exact continuous_const

/-- This is exactly the functional averaged in (6.4): its value is the
ordinary squarefree cubic coefficient for the three coordinate-plane bodies. -/
def tripleFunctional (B C : ConvexBody Plane) : MinkowskiFunctional Plane where
  toFun A := 6 * triple A B C
  continuous_toFun := continuous_const.mul (continuous_triple_first B C)
  monotone h := mul_le_mul_of_nonneg_left (triple_mono_first B C h) (by norm_num)
  map_add A D := by rw [triple_add_first]; ring
  map_nonneg_smul r hr A := by rw [triple_smul_first _ _ _ hr]; ring

@[simp] theorem tripleFunctional_apply (B C A : ConvexBody Plane) :
    tripleFunctional B C A = 6 * triple A B C := rfl

end PlanarInteraction
end VolumePolynomials
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/TripleMinkowskiFunctional.lean -/
