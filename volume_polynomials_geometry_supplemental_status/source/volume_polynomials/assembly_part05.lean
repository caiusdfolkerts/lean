module

public import volume_polynomials.assembly_part04

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

/- BEGIN SOURCE: VolumePolynomials/PolyhedralBasis.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Choosing independent active constraints

At every extreme point of a finite halfspace system, including a nonsimple
one, some active constraints form an ambient coordinate system. This permits
all extreme points to be indexed by a fixed finite set of normal bases.
-/

noncomputable section
open Set Module
open scoped BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem basisIndex_card (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) :
    b.val.card = finrank ℝ E := by
  first
  | have he := (coordinates l b).toLinearEquiv.finrank_eq
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe] using he.symm

theorem exists_basisIndex_subset (l : ι → E →L[ℝ] ℝ) (s : Finset ι)
    (hs : Function.Injective (evaluation l s)) :
    ∃ b : BasisIndex l, b.val ⊆ s := by
  first
  | classical
    let v : s → Module.Dual ℝ E := fun i => (l i).toLinearMap
    have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
      apply Submodule.span_eq_top_of_ne_zero
      intro z hz
      by_contra! h
      apply hz
      apply hs
      funext i
      simpa only [v, evaluation_apply, map_zero, ContinuousLinearMap.coe_coe] using
        h (v i) ⟨i, rfl⟩
    obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ v
    letI : Finite κ := Finite.of_injective a ha
    letI : Fintype κ := Fintype.ofFinite κ
    let f : κ → ι := fun k => (a k).val
    have hf : Function.Injective f := Subtype.val_injective.comp ha
    let t : Finset ι := Finset.univ.image f
    have ht : t ⊆ s := by
      intro i hi
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      exact (a k).property
    have hcard : t.card = finrank ℝ E := by
      let B : Basis κ ℝ (Module.Dual ℝ E) := Basis.mk hli (by rw [hsp, hspan])
      rw [show t.card = Fintype.card κ by
        simp only [t, Finset.card_image_of_injective _ hf, Finset.card_univ]]
      simpa only [Subspace.dual_finrank_eq] using (Module.finrank_eq_card_basis B).symm
    have hinj : Function.Injective (evaluation l t) := by
      intro x y hxy
      apply sub_eq_zero.mp
      apply (Module.forall_dual_apply_eq_zero_iff ℝ (x - y)).mp
      intro φ
      have hφ : φ ∈ Submodule.span ℝ (Set.range (v ∘ a)) := by
        rw [hsp, hspan]
        trivial
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨k, rfl⟩ := hφ
        have hk : f k ∈ t := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
        have he := congrFun hxy ⟨f k, hk⟩
        change l (f k) x = l (f k) y at he
        change l (f k) (x - y) = 0
        rw [map_sub, he, sub_self]
      | zero => rfl
      | add φ ψ _ _ hφ hψ => simp only [LinearMap.add_apply, hφ, hψ, add_zero]
      | smul r φ _ hφ => simp only [LinearMap.smul_apply, hφ, smul_zero]
    have hdim : finrank ℝ E = finrank ℝ (t → ℝ) := by
      simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe] using hcard.symm
    exact ⟨⟨t, hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩,
      ht⟩

theorem extreme_eq_vertexMap_without_generic (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {x : E} (hx : x ∈ (body l h).extremePoints ℝ) :
    ∃ b : BasisIndex l, vertexMap l b h = x := by
  first
  | obtain ⟨b, hb⟩ := exists_basisIndex_subset l (active l h x)
      (active_evaluation_injective l h hx)
    exact ⟨b, vertexMap_unique l b h (fun i hi => (mem_active l h x i).mp (hb hi))⟩

def feasibleBases (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Set (BasisIndex l) :=
  {b | vertexMap l b h ∈ body l h}

theorem extremePoints_eq_vertices (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    (body l h).extremePoints ℝ =
      (fun b : BasisIndex l => vertexMap l b h) '' feasibleBases l h := by
  first
  | ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := extreme_eq_vertexMap_without_generic l h hx
      refine ⟨b, ?_, hb⟩
      change vertexMap l b h ∈ body l h
      rw [hb]
      exact hx.1
    · rintro ⟨b, hb, rfl⟩
      exact vertexMap_mem_extremePoints l b h hb

theorem body_eq_convexHull_vertices (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (body l h)) :
    body l h = convexHull ℝ
      ((fun b : BasisIndex l => vertexMap l b h) '' feasibleBases l h) := by
  first
  | rw [body_eq_convexHull_extremePoints l h hc, extremePoints_eq_vertices]

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolyhedralBasis.lean -/

/- BEGIN SOURCE: VolumePolynomials/SimpleSupportChamber.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Open cones of simple support vectors

A chamber fixes the strict sign of every inactive constraint at every
coordinate vertex. Consequently its feasible vertices have the same active
bases. The resulting bodies add exactly by adding their height vectors, and
every vector of real heights is a positive multiple of a difference of two
support vectors in the chamber.
-/

noncomputable section
open Set Filter Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def slack (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  ((LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) -
    (l i).toLinearMap.comp (vertexMap l b).toLinearMap).toContinuousLinearMap

@[simp] theorem slack_apply (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (i : ι) (h : ι → ℝ) : slack l b i h = h i - l i (vertexMap l b h) := rfl

theorem slack_eq_zero_of_mem (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    {i : ι} (hi : i ∈ b.val) (h : ι → ℝ) : slack l b i h = 0 := by
  first
  | rw [slack_apply, vertexMap_active l b h ⟨i, hi⟩, sub_self]

theorem slack_ne_zero_of_generic (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) (b : BasisIndex l) {i : ι} (hi : i ∉ b.val) :
    slack l b i h ≠ 0 := by
  first
  | intro hz
    rw [slack_apply] at hz
    have hvi : l i (vertexMap l b h) = h i := (sub_eq_zero.mp hz).symm
    have hs : Function.Surjective (evaluation l (insert i b.val)) := by
      first
      | apply hg
        apply Iff.mpr (mem_compatibleHeights l _ h)
        refine ⟨vertexMap l b h, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hvi
        · exact vertexMap_active l b h ⟨j, hj⟩
    obtain ⟨x, hx⟩ := hs (fun j => if j.val = i then 1 else 0)
    have hbx : coordinates l b x = 0 := by
      first
      | funext j
        have hj : j.val ≠ i := by rintro rfl; exact hi j.property
        have he := congrFun hx ⟨j, Finset.mem_insert_of_mem j.property⟩
        simpa only [evaluation_apply, coordinates_apply, if_neg hj, Pi.zero_apply] using he
    have hx0 : x = 0 := (coordinates l b).injective (by simpa using hbx)
    have he := congrFun hx ⟨i, Finset.mem_insert_self _ _⟩
    simp only [evaluation_apply, hx0, map_zero, if_pos rfl, ite_true, zero_ne_one] at he

def chamber (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) : Set (ι → ℝ) :=
  {h | (∀ i, 0 < h i) ∧
    ∀ b : BasisIndex l, ∀ i ∉ b.val, 0 < slack l b i h₀ * slack l b i h}

theorem isOpen_chamber (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) :
    IsOpen (chamber l h₀) := by
  first
  | change IsOpen ({h | ∀ i, 0 < h i} ∩
      {h | ∀ b : BasisIndex l, ∀ i, i ∉ b.val →
        0 < slack l b i h₀ * slack l b i h})
    apply IsOpen.inter
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    · simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro b
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro hi
      have hc : Continuous (fun h : ι → ℝ => slack l b i h₀ * slack l b i h) := by
        first
        | fun_prop
      exact isOpen_lt continuous_const hc

theorem mem_chamber_self (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) (hpos : ∀ i, 0 < h i) : h ∈ chamber l h := by
  first
  | refine ⟨hpos, fun b i hi => ?_⟩
    exact mul_self_pos.mpr (slack_ne_zero_of_generic l h hg b hi)

theorem chamber_add (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    {h k : ι → ℝ} (hh : h ∈ chamber l h₀) (hk : k ∈ chamber l h₀) :
    h + k ∈ chamber l h₀ := by
  first
  | refine ⟨fun i => add_pos (hh.1 i) (hk.1 i), fun b i hi => ?_⟩
    rw [map_add, mul_add]
    exact add_pos (hh.2 b i hi) (hk.2 b i hi)

theorem chamber_smul (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    {h : ι → ℝ} (hh : h ∈ chamber l h₀) {r : ℝ} (hr : 0 < r) :
    r • h ∈ chamber l h₀ := by
  first
  | refine ⟨fun i => mul_pos hr (hh.1 i), fun b i hi => ?_⟩
    rw [map_smul, smul_eq_mul, mul_left_comm]
    exact mul_pos hr (hh.2 b i hi)

theorem feasibleBases_eq_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hg : Generic l h₀) {h : ι → ℝ} (hh : h ∈ chamber l h₀) :
    feasibleBases l h = feasibleBases l h₀ := by
  first
  | ext b
    constructor
    · intro hb i
      by_cases hi : i ∈ b.val
      · exact (vertexMap_active l b h₀ ⟨i, hi⟩).le
      · have hp := hh.2 b i hi
        have hb' : 0 ≤ slack l b i h := by
          first
          | simpa only [slack_apply] using sub_nonneg.mpr (hb i)
        have hs : 0 ≤ slack l b i h₀ := (pos_of_mul_pos_left hp hb').le
        exact sub_nonneg.mp (by simpa only [slack_apply] using hs)
    · intro hb i
      by_cases hi : i ∈ b.val
      · exact (vertexMap_active l b h ⟨i, hi⟩).le
      · have hp := hh.2 b i hi
        have hb' : 0 ≤ slack l b i h₀ := by
          first
          | simpa only [slack_apply] using sub_nonneg.mpr (hb i)
        have hs : 0 ≤ slack l b i h := (pos_of_mul_pos_right hp hb').le
        exact sub_nonneg.mp (by simpa only [slack_apply] using hs)

theorem active_eq_basis_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) {h : ι → ℝ} (hh : h ∈ chamber l h₀)
    (b : BasisIndex l) : active l h (vertexMap l b h) = b.val := by
  first
  | ext i
    rw [mem_active]
    constructor
    · intro he
      by_contra hi
      have hp := hh.2 b i hi
      simp only [slack_apply, he, sub_self, mul_zero, lt_self_iff_false] at hp
    · intro hi
      exact vertexMap_active l b h ⟨i, hi⟩

theorem simple_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) {h : ι → ℝ} (hh : h ∈ chamber l h₀)
    {x : E} (hx : x ∈ (body l h).extremePoints ℝ) :
    Function.Bijective (evaluation l (active l h x)) := by
  first
  | obtain ⟨b, rfl⟩ := extreme_eq_vertexMap_without_generic l h hx
    rw [active_eq_basis_of_mem_chamber l h₀ hh b]
    exact b.property

theorem isCompact_body_of_positive_reference (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hpos : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) : IsCompact (body l h) := by
  first
  | let r : ℝ := 1 + ∑ i, |h i / h₀ i|
    have hr : 0 < r := by
      first
      | have hs : 0 ≤ ∑ i, |h i / h₀ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp [r]
        linarith
    have hbound : ∀ i, h i ≤ r * h₀ i := by
      first
      | intro i
        have hi : |h i / h₀ i| ≤ ∑ j, |h j / h₀ j| :=
          Finset.single_le_sum (s := Finset.univ) (f := fun j : ι => |h j / h₀ j|)
            (fun j _ => abs_nonneg (h j / h₀ j)) (Finset.mem_univ i)
        have hd : h i / h₀ i ≤ r := by
          have ha := le_abs_self (h i / h₀ i)
          dsimp [r]
          linarith
        exact (div_le_iff₀ (hpos i)).mp hd
    have hsub : body l h ⊆ (fun x : E => r • x) '' body l h₀ := by
      first
      | intro x hx
        refine ⟨r⁻¹ • x, ?_, by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
        intro i
        rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
        exact (div_le_iff₀ hr).mpr ((hx i).trans (hbound i) |>.trans_eq (mul_comm r (h₀ i)))
    exact (hc.image (continuous_const.smul continuous_id)).of_isClosed_subset
      (body_isClosed l h) hsub

theorem zero_mem_interior_body (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) : (0 : E) ∈ interior (body l h) := by
  first
  | let U : Set E := {x | ∀ i, l i x < h i}
    have hU : IsOpen U := by
      first
      | simp only [U, Set.ofPred_forall]
        exact isOpen_iInter_of_finite fun i => isOpen_lt (l i).continuous continuous_const
    have h0 : (0 : E) ∈ U := by intro i; simpa only [map_zero] using hpos i
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hU.mem_nhds h0) (fun x hx i => (hx i).le))

theorem body_add_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hg : Generic l h₀) (hpos : ∀ i, 0 < h₀ i)
    (hc : IsCompact (body l h₀)) {h k : ι → ℝ}
    (hh : h ∈ chamber l h₀) (hk : k ∈ chamber l h₀) :
    body l (h + k) = body l h + body l k := by
  first
  | apply Subset.antisymm
    · rw [body_eq_convexHull_vertices l (h + k)
        (isCompact_body_of_positive_reference l h₀ hpos hc _)]
      apply convexHull_min _ ((body_convex l h).add (body_convex l k))
      rintro x ⟨b, hb, rfl⟩
      have hb₀ : b ∈ feasibleBases l h₀ := by
        first
        | rwa [feasibleBases_eq_of_mem_chamber l h₀ hg (chamber_add l h₀ hh hk)] at hb
      have hbh : b ∈ feasibleBases l h := by
        first
        | rwa [feasibleBases_eq_of_mem_chamber l h₀ hg hh]
      have hbk : b ∈ feasibleBases l k := by
        first
        | rwa [feasibleBases_eq_of_mem_chamber l h₀ hg hk]
      change vertexMap l b (h + k) ∈ body l h + body l k
      rw [map_add]
      exact Set.add_mem_add hbh hbk
    · rintro x ⟨y, hy, z, hz, rfl⟩ i
      simpa only [map_add, Pi.add_apply] using add_le_add (hy i) (hz i)

theorem body_smul (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    body l (r • h) = r • body l h := by
  first
  | ext x
    constructor
    · intro hx
      refine ⟨r⁻¹ • x, ?_, by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
      intro i
      rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
      exact (div_le_iff₀ hr).mpr (by simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hx i)
    · rintro ⟨y, hy, rfl⟩ i
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using
        mul_le_mul_of_nonneg_left (hy i) hr.le

/-- Every real support direction is represented by two actual bodies in one
simple chamber. This is the precise unrestricted extension used in the
finite-dimensional Alexandrov--Fenchel operator. -/
theorem exists_chamber_difference (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    {h : ι → ℝ} (hh : h ∈ chamber l h₀) (x : ι → ℝ) :
    ∃ (a : ℝ) (k : ι → ℝ), 0 < a ∧ k ∈ chamber l h₀ ∧ x = a • (k - h) := by
  first
  | have ht : Tendsto (fun t : ℝ => h + t • x) (𝓝 0) (𝓝 h) := by
      first
      | have hc : Continuous (fun t : ℝ => h + t • x) := by fun_prop
        simpa only [zero_smul, add_zero] using
          hc.tendsto (0 : ℝ)
    have he := ht.eventually ((isOpen_chamber l h₀).mem_nhds hh)
    obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp he
    have heps : dist (ε / 2) 0 < ε := by
      first
      | rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
        linarith
    refine ⟨(ε / 2)⁻¹, h + (ε / 2) • x, inv_pos.mpr (half_pos hε), hsmall heps, ?_⟩
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (half_pos hε).ne', one_smul]

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 21
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SimpleSupportChamber.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolyhedralRefinement.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Simple refinements of a fixed bounded halfspace system

The neighborhood used to choose a generic perturbation excludes every basis
that was infeasible in the original system. At a simple vertex, maximizing
linear functionals have nonnegative coefficients in the active normal basis.
This is proved by actual short feasible segments, without invoking an
unformalized normal-cone or linear-programming theorem.
-/

noncomputable section
open Set Filter Module Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def toBody (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hpos : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) (hh : ∀ i, 0 < h i) : ConvexBody E where
  carrier := body l h
  convex' := body_convex l h
  isCompact' := isCompact_body_of_positive_reference l h₀ hpos hc h
  nonempty' := ⟨0, fun i => by simpa only [map_zero] using (hh i).le⟩

theorem toBody_isFiniteHull (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hpos : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) (hh : ∀ i, 0 < h i) :
    PolytopeGeometry.IsFiniteHull (toBody l h₀ hpos hc h hh : Set E) := by
  first
  | exact ⟨(body l h).extremePoints ℝ, finite_extremePoints l h,
      body_eq_convexHull_extremePoints l h
        (isCompact_body_of_positive_reference l h₀ hpos hc h)⟩

def refinementRegion (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) : Set (ι → ℝ) :=
  {h | feasibleBases l h ⊆ feasibleBases l h₀}

theorem isClosed_feasibleBasis (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) :
    IsClosed {h | b ∈ feasibleBases l h} := by
  first
  | change IsClosed {h | ∀ i, l i (vertexMap l b h) ≤ h i}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le ((l i).continuous.comp (vertexMap l b).continuous) (continuous_apply i)

theorem isOpen_refinementRegion (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) :
    IsOpen (refinementRegion l h₀) := by
  first
  | classical
    have he : refinementRegion l h₀ = ⋂ b : BasisIndex l,
        if b ∈ feasibleBases l h₀ then Set.univ else {h | b ∈ feasibleBases l h}ᶜ := by
      ext h
      simp only [refinementRegion, mem_setOf_eq, Set.subset_def, mem_iInter]
      apply forall_congr'
      intro b
      by_cases hb : b ∈ feasibleBases l h₀ <;> simp [hb]
    rw [he]
    apply isOpen_iInter_of_finite
    intro b
    split_ifs
    · exact isOpen_univ
    · exact (isClosed_feasibleBasis l b).isOpen_compl

theorem isOpen_positiveHeights : IsOpen {h : ι → ℝ | ∀ i, 0 < h i} := by
  first
  | simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

/-- A bounded system with positive heights has a generic positive refinement
whose every feasible normal basis was already feasible in the original body. -/
theorem exists_generic_refinement (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hpos : ∀ i, 0 < h₀ i) :
    ∃ h : ι → ℝ, Generic l h ∧ (∀ i, 0 < h i) ∧
      feasibleBases l h ⊆ feasibleBases l h₀ := by
  first
  | have ho : IsOpen ({h : ι → ℝ | ∀ i, 0 < h i} ∩ refinementRegion l h₀) :=
      isOpen_positiveHeights.inter (isOpen_refinementRegion l h₀)
    obtain ⟨h, hg, hh⟩ := (dense_generic l).exists_mem_open ho ⟨h₀, hpos, Set.Subset.rfl⟩
    exact ⟨h, hg, hh.1, hh.2⟩

def StrictFacets (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Prop :=
  ∀ i, ∃ x : E, l i x = h i ∧ ∀ j, j ≠ i → l j x < h j

theorem eventually_strictFacets (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hn : ∀ i, l i ≠ 0) (hs : StrictFacets l h₀) :
    ∀ᶠ h : ι → ℝ in 𝓝 h₀, StrictFacets l h := by
  first
  | choose v hv using fun i => LinearFrame.exists_unit_value (l i) (hn i)
    choose x hxi hxj using hs
    have he : ∀ᶠ h : ι → ℝ in 𝓝 h₀, ∀ i j, j ≠ i →
        l j (x i + (h i - h₀ i) • v i) < h j := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun _ hn => (hn hji).elim
      · have ht : ∀ᶠ h : ι → ℝ in 𝓝 h₀,
            l j (x i + (h i - h₀ i) • v i) < h j :=
          (isOpen_lt (by fun_prop) (continuous_apply j)).mem_nhds (by
            change l j (x i + (h₀ i - h₀ i) • v i) < h₀ j
            simpa only [sub_self, zero_smul, add_zero] using hxj i j hji)
        filter_upwards [ht] with h hh
        exact fun _ => hh
    filter_upwards [he] with h hh
    intro i
    refine ⟨x i + (h i - h₀ i) • v i, ?_, hh i⟩
    rw [map_add, map_smul, smul_eq_mul, hxi i, hv i, mul_one]
    ring

/-- Generic perturbation preserving every genuine facet, not merely the
bounded body. This supplies strictly positive facet measures in the operator. -/
theorem exists_generic_refinement_strictFacets (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hn : ∀ i, l i ≠ 0) (hpos : ∀ i, 0 < h₀ i)
    (hs : StrictFacets l h₀) :
    ∃ h : ι → ℝ, Generic l h ∧ (∀ i, 0 < h i) ∧
      feasibleBases l h ⊆ feasibleBases l h₀ ∧ StrictFacets l h := by
  first
  | have he : ∀ᶠ h : ι → ℝ in 𝓝 h₀,
        (∀ i, 0 < h i) ∧ feasibleBases l h ⊆ feasibleBases l h₀ ∧ StrictFacets l h := by
      filter_upwards [isOpen_positiveHeights.mem_nhds hpos,
        (isOpen_refinementRegion l h₀).mem_nhds (show h₀ ∈ refinementRegion l h₀ from Set.Subset.rfl),
        eventually_strictFacets l h₀ hn hs] with h hp hr hf
      exact ⟨hp, hr, hf⟩
    obtain ⟨U, hUsub, hUopen, hUmem⟩ := _root_.mem_nhds_iff.mp he
    obtain ⟨h, hg, hh⟩ := (dense_generic l).exists_mem_open hUopen ⟨h₀, hUmem⟩
    exact ⟨h, hg, hUsub hh⟩

def basisDirection (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) (j : b.val) : E :=
  (coordinates l b).symm (Pi.single j 1)

@[simp] theorem normal_basisDirection (l : ι → E →L[ℝ] ℝ)
    (b : BasisIndex l) (i j : b.val) :
    l i (basisDirection l b j) = if i = j then 1 else 0 := by
  first
  | change (coordinates l b ((coordinates l b).symm (Pi.single j 1))) i = _
    simp only [ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]

theorem sum_basisDirection (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) (x : E) :
    (∑ j : b.val, l j x • basisDirection l b j) = x := by
  first
  | apply (coordinates l b).injective
    ext i
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, coordinates_apply,
      normal_basisDirection, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp

theorem functional_expansion (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (f : E →L[ℝ] ℝ) (x : E) :
    f x = ∑ j : b.val, f (basisDirection l b j) * l j x := by
  first
  | conv_lhs => rw [← sum_basisDirection l b x]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

theorem strict_inactive_of_generic (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (hg : Generic l h) (b : BasisIndex l)
    (hb : b ∈ feasibleBases l h) (i : ι) (hi : i ∉ b.val) :
    l i (vertexMap l b h) < h i := by
  first
  | have hz := slack_ne_zero_of_generic l h hg b hi
    rw [slack_apply] at hz
    have hs : 0 ≤ h i - l i (vertexMap l b h) := sub_nonneg.mpr (hb i)
    exact sub_pos.mp (lt_of_le_of_ne hs (Ne.symm hz))

theorem exists_negative_basis_step (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (b : BasisIndex l) (hb : b ∈ feasibleBases l h)
    (hstrict : ∀ i ∉ b.val, l i (vertexMap l b h) < h i) (j : b.val) :
    ∃ t : ℝ, 0 < t ∧ vertexMap l b h - t • basisDirection l b j ∈ body l h := by
  first
  | have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i ∉ b.val,
        l i (vertexMap l b h - t • basisDirection l b j) < h i := by
      apply Filter.eventually_all.mpr
      intro i
      by_cases hi : i ∈ b.val
      · exact Filter.Eventually.of_forall fun _ hn => (hn hi).elim
      · have he : ∀ᶠ t : ℝ in 𝓝 0,
            l i (vertexMap l b h - t • basisDirection l b j) < h i :=
          (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by
            change l i (vertexMap l b h - (0 : ℝ) • basisDirection l b j) < h i
            simpa only [zero_smul, sub_zero] using hstrict i hi)
        filter_upwards [he] with t ht
        exact fun _ => ht
    obtain ⟨ε, hε, hs⟩ := Metric.eventually_nhds_iff.mp hnear
    have ht : dist (ε / 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith
    refine ⟨ε / 2, half_pos hε, fun i => ?_⟩
    by_cases hi : i ∈ b.val
    · rw [map_sub, map_smul, smul_eq_mul, vertexMap_active l b h ⟨i, hi⟩,
        normal_basisDirection l b ⟨i, hi⟩ j]
      split_ifs <;> nlinarith
    · exact (hs ht i hi).le

/-- The usual normal-cone statement at a simple vertex, with explicit
coefficients in the actual active normal basis. -/
theorem maximizing_coefficients_nonnegative (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (b : BasisIndex l) (hb : b ∈ feasibleBases l h)
    (hstrict : ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (f : E →L[ℝ] ℝ) (hf : ∀ x ∈ body l h, f x ≤ f (vertexMap l b h)) :
    ∀ j : b.val, 0 ≤ f (basisDirection l b j) := by
  first
  | intro j
    obtain ⟨t, ht, hstep⟩ := exists_negative_basis_step l h b hb hstrict j
    have he := hf _ hstep
    rw [map_sub, map_smul, smul_eq_mul] at he
    nlinarith

theorem functional_le_vertex_of_normal_bounds (l : ι → E →L[ℝ] ℝ)
    (b : BasisIndex l) (f : E →L[ℝ] ℝ)
    (hf : ∀ j : b.val, 0 ≤ f (basisDirection l b j))
    (h : ι → ℝ) {x : E} (hx : ∀ j : b.val, l j x ≤ h j) :
    f x ≤ f (vertexMap l b h) := by
  first
  | rw [functional_expansion l b f x, functional_expansion l b f (vertexMap l b h)]
    apply Finset.sum_le_sum
    intro j _
    rw [vertexMap_active]
    exact mul_le_mul_of_nonneg_left (hx j) (hf j)

theorem exists_maximizing_basis (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (hc : IsCompact (body l h)) (hne : (body l h).Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ b : BasisIndex l, b ∈ feasibleBases l h ∧
      ∀ x ∈ body l h, f x ≤ f (vertexMap l b h) := by
  first
  | have he : IsExposed ℝ (body l h) (f.toExposed (body l h)) :=
      ContinuousLinearMap.toExposed.isExposed
    have hface : (f.toExposed (body l h)).Nonempty :=
      PolytopeFaces.exposed_nonempty f hc hne
    obtain ⟨x, hx⟩ := (he.isCompact hc).extremePoints_nonempty hface
    have hxbody := he.isExtreme.extremePoints_subset_extremePoints hx
    obtain ⟨b, hb⟩ := extreme_eq_vertexMap_without_generic l h hxbody
    refine ⟨b, ?_, ?_⟩
    · change vertexMap l b h ∈ body l h
      rw [hb]
      exact hxbody.1
    · intro y hy
      rw [hb]
      exact hx.1.2 y hy

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 21
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolyhedralRefinement.lean -/

/- BEGIN SOURCE: VolumePolynomials/SimpleMinkowskiRefinement.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Minkowski sums with a common simple refinement

Every vertex of the perturbed total sum determines compatible supporting
vertices in each summand. Adding any positive multiple of the refinement to
each summand therefore produces exactly the same finite vertex/facet
incidence structure. This proves the common-refinement step directly from
support inequalities and finite convex hulls.
-/

noncomputable section
open Set Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem minkowski_eq_halfspaces_of_refinement
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (R Q : ConvexBody E) (hR : (R : Set E) = body l h) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) :
    (↑(Q + r • R) : Set E) = body l (g + r • h) := by
  first
  | ext x
    constructor
    · change x ∈ (Q : Set E) + r • (R : Set E) → _
      rintro ⟨q, hq, y, ⟨p, hp, rfl⟩, rfl⟩ i
      rw [hR] at hp
      simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        add_le_add (hbound q hq i) (mul_le_mul_of_nonneg_left (hp i) hr.le)
    · intro hx
      apply (BodySupport.mem_iff_le_support (Q + r • R)).mpr
      intro f
      obtain ⟨b, hb, hbmax⟩ := exists_maximizing_basis l h
        (hR ▸ R.isCompact) (hR ▸ R.nonempty) f
      have hcoeff := maximizing_coefficients_nonnegative l h b hb
        (hsimple b hb) f hbmax
      have hle := functional_le_vertex_of_normal_bounds l b f hcoeff
        (g + r • h) (fun j => hx j)
      have hp : vertexMap l b g + r • vertexMap l b h ∈ Q + r • R := by
        exact Set.add_mem_add (hvertex b hb)
          (Set.smul_mem_smul_set (by rwa [hR]))
      have hmap : vertexMap l b (g + r • h) =
          vertexMap l b g + r • vertexMap l b h := by rw [map_add, map_smul]
      rw [hmap] at hle
      exact hle.trans (BodySupport.le_support (Q + r • R) f hp)

theorem minkowski_eq_convexHull_refinement_vertices
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (R Q : ConvexBody E) (hR : (R : Set E) = body l h) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) :
    (↑(Q + r • R) : Set E) = convexHull ℝ
      ((fun b : BasisIndex l => vertexMap l b (g + r • h)) '' feasibleBases l h) := by
  first
  | let V : Set E :=
      (fun b : BasisIndex l => vertexMap l b (g + r • h)) '' feasibleBases l h
    have hVfin : V.Finite := (Set.toFinite _).image _
    have hVsub : V ⊆ (↑(Q + r • R) : Set E) := by
      rintro x ⟨b, hb, rfl⟩
      dsimp only
      rw [map_add, map_smul]
      exact Set.add_mem_add (hvertex b hb)
        (Set.smul_mem_smul_set (by rwa [hR]))
    apply Subset.antisymm
    · intro x hx
      by_contra hnot
      obtain ⟨f, a, hf, hfx⟩ := geometric_hahn_banach_closed_point
        (convex_convexHull ℝ V) (hVfin.isClosed_convexHull ℝ) hnot
      obtain ⟨b, hb, hbmax⟩ := exists_maximizing_basis l h
        (hR ▸ R.isCompact) (hR ▸ R.nonempty) f
      have hcoeff := maximizing_coefficients_nonnegative l h b hb
        (hsimple b hb) f hbmax
      have hxb : x ∈ body l (g + r • h) := by
        rwa [← minkowski_eq_halfspaces_of_refinement l h hsimple R Q hR g hbound hvertex hr]
      have hle := functional_le_vertex_of_normal_bounds l b f hcoeff
        (g + r • h) (fun j => hxb j)
      have hv : vertexMap l b (g + r • h) ∈ convexHull ℝ V :=
        subset_convexHull ℝ V ⟨b, hb, rfl⟩
      exact (hfx.trans_le (hle.trans (hf _ hv).le)).false
    · exact convexHull_min hVsub (Q + r • R).convex

theorem refinement_vertex_strict_inactive
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (Q : ConvexBody E) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) (b : BasisIndex l) (hb : b ∈ feasibleBases l h)
    (i : ι) (hi : i ∉ b.val) :
    l i (vertexMap l b (g + r • h)) < (g + r • h) i := by
  first
  | have hq := hbound _ (hvertex b hb) i
    have hp := hsimple b hb i hi
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_lt_add_of_le_of_lt hq (mul_lt_mul_of_pos_left hp hr)

theorem active_eq_basis_of_strict (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (b : BasisIndex l)
    (hs : ∀ i ∉ b.val, l i (vertexMap l b h) < h i) :
    active l h (vertexMap l b h) = b.val := by
  first
  | ext i
    rw [mem_active]
    constructor
    · intro hi
      by_contra hni
      exact (hs i hni).ne hi
    · intro hi
      exact vertexMap_active l b h ⟨i, hi⟩

theorem feasibleBases_minkowski_refinement
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (R Q : ConvexBody E) (hR : (R : Set E) = body l h) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) :
    feasibleBases l (g + r • h) = feasibleBases l h := by
  first
  | ext b
    constructor
    · intro hb
      have he := vertexMap_mem_extremePoints l b (g + r • h) hb
      rw [← minkowski_eq_halfspaces_of_refinement l h hsimple R Q hR g hbound hvertex hr,
        minkowski_eq_convexHull_refinement_vertices l h hsimple R Q hR g hbound hvertex hr] at he
      obtain ⟨a, ha, hab⟩ := extremePoints_convexHull_subset he
      dsimp only at hab
      have hactive : active l (g + r • h) (vertexMap l a (g + r • h)) = a.val :=
        active_eq_basis_of_strict l _ a
          (refinement_vertex_strict_inactive l h hsimple Q g hbound hvertex hr a ha)
      have hsub : b.val ⊆ a.val := by
        intro i hi
        rw [← hactive, mem_active, hab]
        exact vertexMap_active l b _ ⟨i, hi⟩
      have hba : b.val = a.val := Finset.eq_of_subset_of_card_le hsub (by
        rw [basisIndex_card l b, basisIndex_card l a])
      simpa only [show b = a from Subtype.ext hba] using ha
    · intro hb i
      by_cases hi : i ∈ b.val
      · exact (vertexMap_active l b _ ⟨i, hi⟩).le
      · exact (refinement_vertex_strict_inactive l h hsimple Q g hbound hvertex hr b hb i hi).le

/-- A feasible coordinate vertex of the total sum determines a feasible
supporting vertex of each summand. No simplicity of the summands is assumed. -/
theorem summand_vertex_mem {κ : Type*} [Fintype κ]
    (K : κ → ConvexBody E) (l : ι → E →L[ℝ] ℝ)
    (hbody : (↑(∑ k, K k) : Set E) =
      body l (fun i => ∑ k, BodySupport.support (K k) (l i)))
    (b : BasisIndex l)
    (hb : b ∈ feasibleBases l (fun i => ∑ k, BodySupport.support (K k) (l i)))
    (k : κ) : vertexMap l b (fun i => BodySupport.support (K k) (l i)) ∈ K k := by
  first
  | have hx : vertexMap l b (fun i => ∑ k, BodySupport.support (K k) (l i)) ∈ ∑ k, K k := by
      change vertexMap l b (fun i => ∑ k, BodySupport.support (K k) (l i)) ∈
        (↑(∑ k, K k) : Set E)
      rwa [hbody]
    obtain ⟨p, hp, hsum⟩ := (mem_sum_body K _).mp hx
    have heq : ∀ i ∈ b.val, l i (p k) = BodySupport.support (K k) (l i) := by
      intro i hi
      have hs : (∑ j, l i (p j)) = ∑ j, BodySupport.support (K j) (l i) := by
        rw [← map_sum, hsum, vertexMap_active l b _ ⟨i, hi⟩]
      exact (Finset.sum_eq_sum_iff_of_le
        (fun j (_ : j ∈ Finset.univ) => BodySupport.le_support (K j) (l i) (hp j))).mp hs
          k (Finset.mem_univ k)
    rw [vertexMap_unique l b _ heq]
    exact hp k

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SimpleMinkowskiRefinement.lean -/

/- BEGIN SOURCE: VolumePolynomials/CommonSimplePolytopes.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Constructing a common simple refinement

The data below are constructed from the finite convex hulls in the tuple.
Their generic reference body is a small perturbation of the support heights
of the total sum. Adding a positive multiple of this body to every summand
gives actual simple polytopes with identical feasible normal bases.
-/

noncomputable section
open Set Filter Module Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {κ : Type*} [Fintype κ]

structure CommonRefinement (K : κ → ConvexBody E) where
  facets : PolytopeGeometry.FixedFacets (fun k => (K k : Set E))
  reference : ConvexBody E
  reference_finite : PolytopeGeometry.IsFiniteHull (reference : Set E)
  height : Fin facets.count → ℝ
  height_pos : ∀ i, 0 < height i
  generic : Generic facets.normal height
  strict_facets : StrictFacets facets.normal height
  reference_eq : (reference : Set E) = body facets.normal height
  refines : feasibleBases facets.normal height ⊆
    feasibleBases facets.normal (fun i => ∑ k, BodySupport.support (K k) (facets.normal i))

namespace CommonRefinement

variable {K : κ → ConvexBody E} (D : CommonRefinement K)

theorem reference_strict_inactive : ∀ b ∈ feasibleBases D.facets.normal D.height,
    ∀ i ∉ b.val, D.facets.normal i (vertexMap D.facets.normal b D.height) < D.height i :=
  strict_inactive_of_generic D.facets.normal D.height D.generic

def summandHeight (k : κ) (i : Fin D.facets.count) : ℝ :=
  BodySupport.support (K k) (D.facets.normal i)

theorem total_body_eq : (↑(∑ k, K k) : Set E) =
    body D.facets.normal (fun i => ∑ k, D.summandHeight k i) := by
  first
  | have he := D.facets.body_eq (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
    simpa only [one_smul, one_mul, ← coe_sum_body,
      summandHeight, BodySupport.support, OAI.Paper092.SupportGeometry.support, body] using he

theorem summand_vertex (k : κ) (b : BasisIndex D.facets.normal)
    (hb : b ∈ feasibleBases D.facets.normal D.height) :
    vertexMap D.facets.normal b (D.summandHeight k) ∈ K k :=
  summand_vertex_mem K D.facets.normal D.total_body_eq b (D.refines hb) k

def approximant (r : ℝ) (k : κ) : ConvexBody E := K k + r • D.reference

def approximantHeight (r : ℝ) (k : κ) : Fin D.facets.count → ℝ :=
  D.summandHeight k + r • D.height

theorem approximant_eq_halfspaces {r : ℝ} (hr : 0 < r) (k : κ) :
    (D.approximant r k : Set E) = body D.facets.normal (D.approximantHeight r k) :=
  minkowski_eq_halfspaces_of_refinement D.facets.normal D.height D.reference_strict_inactive
    D.reference (K k) D.reference_eq (D.summandHeight k)
    (fun x hx i => BodySupport.le_support (K k) (D.facets.normal i) hx)
    (D.summand_vertex k) hr

theorem approximant_feasibleBases {r : ℝ} (hr : 0 < r) (k : κ) :
    feasibleBases D.facets.normal (D.approximantHeight r k) =
      feasibleBases D.facets.normal D.height :=
  feasibleBases_minkowski_refinement D.facets.normal D.height D.reference_strict_inactive
    D.reference (K k) D.reference_eq (D.summandHeight k)
    (fun x hx i => BodySupport.le_support (K k) (D.facets.normal i) hx)
    (D.summand_vertex k) hr

theorem approximant_strict_inactive {r : ℝ} (hr : 0 < r) (k : κ)
    (b : BasisIndex D.facets.normal) (hb : b ∈ feasibleBases D.facets.normal D.height)
    (i : Fin D.facets.count) (hi : i ∉ b.val) :
    D.facets.normal i (vertexMap D.facets.normal b (D.approximantHeight r k)) <
      D.approximantHeight r k i :=
  refinement_vertex_strict_inactive D.facets.normal D.height D.reference_strict_inactive (K k)
    (D.summandHeight k)
    (fun x hx i => BodySupport.le_support (K k) (D.facets.normal i) hx)
    (D.summand_vertex k) hr b hb i hi

theorem approximant_is_simple {r : ℝ} (hr : 0 < r) (k : κ)
    {x : E} (hx : x ∈ (D.approximant r k : Set E).extremePoints ℝ) :
    Function.Bijective
      (evaluation D.facets.normal (active D.facets.normal (D.approximantHeight r k) x)) := by
  first
  | rw [D.approximant_eq_halfspaces hr k] at hx
    obtain ⟨b, rfl⟩ := extreme_eq_vertexMap_without_generic D.facets.normal _ hx
    have hb : b ∈ feasibleBases D.facets.normal D.height := by
      rw [← D.approximant_feasibleBases hr k]
      exact hx.1
    rw [active_eq_basis_of_strict D.facets.normal _ b (D.approximant_strict_inactive hr k b hb)]
    exact b.property

theorem approximant_strictFacets {r : ℝ} (hr : 0 < r) (k : κ) :
    StrictFacets D.facets.normal (D.approximantHeight r k) := by
  first
  | intro i
    obtain ⟨p, hpi, hpj⟩ := D.strict_facets i
    obtain ⟨q, hq, hqi⟩ := BodySupport.exists_support (K k) (D.facets.normal i)
    refine ⟨q + r • p, ?_, fun j hji => ?_⟩
    · simp only [approximantHeight, summandHeight, Pi.add_apply, Pi.smul_apply,
        map_add, map_smul, smul_eq_mul, hqi, hpi]
    · have hqj := BodySupport.le_support (K k) (D.facets.normal j) hq
      have hp := mul_lt_mul_of_pos_left (hpj j hji) hr
      simpa only [approximantHeight, summandHeight, Pi.add_apply, Pi.smul_apply,
        map_add, map_smul, smul_eq_mul] using add_lt_add_of_le_of_lt hqj hp

theorem approximantHeight_pos (h0 : ∀ k, (0 : E) ∈ K k)
    {r : ℝ} (hr : 0 < r) (k : κ) (i : Fin D.facets.count) :
    0 < D.approximantHeight r k i := by
  first
  | have hg : 0 ≤ D.summandHeight k i := by
      simpa only [summandHeight, map_zero] using
        BodySupport.le_support (K k) (D.facets.normal i) (h0 k)
    exact add_pos_of_nonneg_of_pos hg (mul_pos hr (D.height_pos i))

theorem approximant_zero_mem_interior (h0 : ∀ k, (0 : E) ∈ K k)
    {r : ℝ} (hr : 0 < r) (k : κ) :
    (0 : E) ∈ interior (D.approximant r k : Set E) := by
  first
  | rw [D.approximant_eq_halfspaces hr k]
    exact zero_mem_interior_body D.facets.normal _ (D.approximantHeight_pos h0 hr k)

theorem approximant_isFiniteHull
    (hK : ∀ k, PolytopeGeometry.IsFiniteHull (K k : Set E)) (r : ℝ) (k : κ) :
    PolytopeGeometry.IsFiniteHull (D.approximant r k : Set E) :=
  (hK k).add (D.reference_finite.smul r)

theorem continuous_approximant : Continuous (fun r : ℝ => D.approximant r) := by
  first
  | unfold approximant
    fun_prop

theorem tendsto_approximant_zero : Tendsto (fun r : ℝ => D.approximant r) (𝓝 0) (𝓝 K) := by
  first
  | have hzero : D.approximant 0 = K := by
      funext k
      change K k + (0 : ℝ) • D.reference = K k
      rw [body_zero_smul, add_zero]
    have h := D.continuous_approximant.tendsto 0
    rw [hzero] at h
    exact h

end CommonRefinement

/-- The common simple refinement is constructed for every finite-hull tuple
whose centered sum has interior. Individual summands may be lower dimensional. -/
theorem exists_commonRefinement (K : κ → ConvexBody E)
    (hK : ∀ k, PolytopeGeometry.IsFiniteHull (K k : Set E))
    (h0 : ∀ k, (0 : E) ∈ K k)
    (hint : (0 : E) ∈ interior (↑(∑ k, K k) : Set E)) :
    Nonempty (CommonRefinement K) := by
  first
  | have hintSet : (0 : E) ∈ interior (∑ k, (K k : Set E)) := by
      simpa only [coe_sum_body] using hint
    obtain ⟨D⟩ := PolytopeGeometry.exists_fixedFacets (fun k => (K k : Set E))
      hK (fun k => (K k).nonempty) ⟨0, hintSet⟩
    let hbase : Fin D.count → ℝ := fun i => ∑ k, BodySupport.support (K k) (D.normal i)
    have hbody : (↑(∑ k, K k) : Set E) = body D.normal hbase := by
      have he := D.body_eq (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
      simpa only [one_smul, one_mul, ← coe_sum_body, hbase,
        BodySupport.support, OAI.Paper092.SupportGeometry.support, body] using he
    have hbasepos : ∀ i, 0 < hbase i := by
      intro i
      have hp := D.height_one_pos (fun k => (K k).isCompact) h0
        (by simpa only [coe_sum_body] using hint) i
      simpa only [hbase, PolytopeGeometry.FixedFacets.heightCoefficient,
        BodySupport.support, OAI.Paper092.SupportGeometry.support] using hp
    have hbasecompact : IsCompact (body D.normal hbase) := hbody ▸ (∑ k, K k).isCompact
    have hstrict : StrictFacets D.normal hbase := by
      simpa only [StrictFacets, hbase, BodySupport.support,
        OAI.Paper092.SupportGeometry.support] using D.strict_face_point
    obtain ⟨h, hg, hpos, href, hsf⟩ := exists_generic_refinement_strictFacets
      D.normal hbase D.normal_ne_zero hbasepos hstrict
    exact ⟨{
      facets := D
      reference := toBody D.normal hbase hbasepos hbasecompact h hpos
      reference_finite := toBody_isFiniteHull D.normal hbase hbasepos hbasecompact h hpos
      height := h
      height_pos := hpos
      generic := hg
      strict_facets := hsf
      reference_eq := rfl
      refines := href
    }⟩

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CommonSimplePolytopes.lean -/

/- BEGIN SOURCE: VolumePolynomials/OpenConeExtension.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Extending additive functionals from a nonempty open convex cone

Every vector is an actual difference of two cone elements. Additivity makes
the difference of functional values independent of the representation. The
construction extends linear and bilinear mixed-support functionals to all
real support vectors, including directions that are not support functions.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace VolumePolynomials.OpenConeExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (C : ConvexCone ℝ V) (hopen : IsOpen (C : Set V)) (hne : (C : Set V).Nonempty)

include hopen in
theorem exists_pos_sub_mem {h : V} (hh : h ∈ C) (x : V) :
    ∃ ε : ℝ, 0 < ε ∧ h - ε • x ∈ C := by
  first
  | have ht : Tendsto (fun t : ℝ => h - t • x) (𝓝 0) (𝓝 h) := by
      first
      | have hc : Continuous (fun t : ℝ => h - t • x) := by fun_prop
        simpa only [zero_smul, sub_zero] using
          hc.tendsto (0 : ℝ)
    obtain ⟨r, hr, hs⟩ := Metric.eventually_nhds_iff.mp
      (ht.eventually (hopen.mem_nhds hh))
    refine ⟨r / 2, half_pos hr, hs ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith

include hopen in
theorem exists_pos_sub_all {κ : Type*} [Finite κ]
    (h : κ → V) (hh : ∀ i, h i ∈ C) (x : V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, h i - ε • x ∈ C := by
  first
  | have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, h i - t • x ∈ C := by
      first
      | apply Filter.eventually_all.mpr
        intro i
        have ht : Tendsto (fun t : ℝ => h i - t • x) (𝓝 0) (𝓝 (h i)) := by
          have hc : Continuous (fun t : ℝ => h i - t • x) := by fun_prop
          simpa only [zero_smul, sub_zero] using
            hc.tendsto (0 : ℝ)
        exact ht.eventually (hopen.mem_nhds (hh i))
    obtain ⟨r, hr, hs⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨r / 2, half_pos hr, hs ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith

include hopen hne in
theorem exists_difference (x : V) : ∃ a ∈ C, ∃ b ∈ C, a - b = x := by
  first
  | obtain ⟨p, hp⟩ := hne
    have ht : Tendsto (fun t : ℝ => p + t • x) (𝓝 0) (𝓝 p) := by
      first
      | have hc : Continuous (fun t : ℝ => p + t • x) := by fun_prop
        simpa only [zero_smul, add_zero] using
          hc.tendsto (0 : ℝ)
    obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (hopen.mem_nhds hp))
    have heps : dist (ε / 2) 0 < ε := by
      first
      | rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
        linarith
    refine ⟨(ε / 2)⁻¹ • (p + (ε / 2) • x),
      C.smul_mem (inv_pos.mpr (half_pos hε)) (hsmall heps),
      (ε / 2)⁻¹ • p, C.smul_mem (inv_pos.mpr (half_pos hε)) hp, ?_⟩
    rw [smul_add, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (half_pos hε).ne', one_smul]

def positivePart (x : V) : V := Classical.choose (exists_difference C hopen hne x)

def negativePart (x : V) : V :=
  Classical.choose (Classical.choose_spec (exists_difference C hopen hne x)).2

theorem positivePart_mem (x : V) : positivePart C hopen hne x ∈ C :=
  (Classical.choose_spec (exists_difference C hopen hne x)).1

theorem negativePart_mem (x : V) : negativePart C hopen hne x ∈ C :=
  (Classical.choose_spec (Classical.choose_spec (exists_difference C hopen hne x)).2).1

theorem positivePart_sub_negativePart (x : V) :
    positivePart C hopen hne x - negativePart C hopen hne x = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_difference C hopen hne x)).2).2

/-- This operation is defined for every function. Its linearity in the
function is unconditional; linearity in the vector will use cone additivity. -/
def extension (f : V → ℝ) (x : V) : ℝ :=
  f (positivePart C hopen hne x) - f (negativePart C hopen hne x)

theorem extension_add_function (f g : V → ℝ) (x : V) :
    extension C hopen hne (fun y => f y + g y) x =
      extension C hopen hne f x + extension C hopen hne g x := by
  first
  | unfold extension
    ring

theorem extension_smul_function (r : ℝ) (f : V → ℝ) (x : V) :
    extension C hopen hne (fun y => r * f y) x = r * extension C hopen hne f x := by
  first
  | unfold extension
    ring

theorem extension_congr {f g : V → ℝ} (hfg : ∀ x ∈ C, f x = g x) (x : V) :
    extension C hopen hne f x = extension C hopen hne g x := by
  first
  | rw [extension, extension, hfg _ (positivePart_mem C hopen hne x),
      hfg _ (negativePart_mem C hopen hne x)]

def AdditiveOn (f : V → ℝ) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, f (a + b) = f a + f b

def PositiveHomogeneousOn (f : V → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ C, f (r • x) = r * f x

theorem extension_sub (f : V → ℝ) (hf : AdditiveOn C f)
    {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    extension C hopen hne f (a - b) = f a - f b := by
  first
  | let p := positivePart C hopen hne (a - b)
    let q := negativePart C hopen hne (a - b)
    have hp : p ∈ C := positivePart_mem C hopen hne _
    have hq : q ∈ C := negativePart_mem C hopen hne _
    have he : p - q = a - b := positivePart_sub_negativePart C hopen hne _
    have hadd : p + b = a + q := by
      first
      | have := sub_eq_sub_iff_add_eq_add.mp he
        simpa only [add_comm, add_left_comm, add_assoc] using this
    have hval := congrArg f hadd
    rw [hf p hp b hb, hf a ha q hq] at hval
    change f p - f q = f a - f b
    linarith

theorem extension_eq (f : V → ℝ) (hf : AdditiveOn C f) {x : V} (hx : x ∈ C) :
    extension C hopen hne f x = f x := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    have he := extension_sub C hopen hne f hf (C.add_mem hx hp) hp
    rw [add_sub_cancel_right, hf x hx p hp] at he
    simpa only [add_sub_cancel_right] using he

theorem extension_zero (f : V → ℝ) (hf : AdditiveOn C f) :
    extension C hopen hne f 0 = 0 := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    simpa only [sub_self] using extension_sub C hopen hne f hf hp hp

theorem extension_add (f : V → ℝ) (hf : AdditiveOn C f) (x y : V) :
    extension C hopen hne f (x + y) =
      extension C hopen hne f x + extension C hopen hne f y := by
  first
  | obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    obtain ⟨c, hc, d, hd, rfl⟩ := exists_difference C hopen hne y
    rw [extension_sub C hopen hne f hf ha hb, extension_sub C hopen hne f hf hc hd,
      show (a - b) + (c - d) = (a + c) - (b + d) by abel,
      extension_sub C hopen hne f hf (C.add_mem ha hc) (C.add_mem hb hd),
      hf a ha c hc, hf b hb d hd]
    ring

theorem extension_neg (f : V → ℝ) (hf : AdditiveOn C f) (x : V) :
    extension C hopen hne f (-x) = -extension C hopen hne f x := by
  first
  | have he := extension_add C hopen hne f hf x (-x)
    rw [add_neg_cancel, extension_zero C hopen hne f hf] at he
    linarith

theorem extension_smul (f : V → ℝ) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) (r : ℝ) (x : V) :
    extension C hopen hne f (r • x) = r * extension C hopen hne f x := by
  first
  | rcases lt_trichotomy r 0 with hr | rfl | hr
    · have hpos : 0 < -r := neg_pos.mpr hr
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [show r • (a - b) = (-r) • b - (-r) • a by
        rw [neg_smul, neg_smul, neg_sub_neg, smul_sub],
        extension_sub C hopen hne f hf (C.smul_mem hpos hb) (C.smul_mem hpos ha),
        hh (-r) hpos b hb, hh (-r) hpos a ha,
        extension_sub C hopen hne f hf ha hb]
      ring
    · rw [zero_smul, extension_zero C hopen hne f hf, zero_mul]
    · obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [smul_sub, extension_sub C hopen hne f hf (C.smul_mem hr ha) (C.smul_mem hr hb),
        hh r hr a ha, hh r hr b hb, extension_sub C hopen hne f hf ha hb]
      ring

def linearExtension (f : V → ℝ) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) : V →ₗ[ℝ] ℝ where
  toFun := extension C hopen hne f
  map_add' := extension_add C hopen hne f hf
  map_smul' := extension_smul C hopen hne f hf hh

theorem linearExtension_eq (f : V → ℝ) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) {x : V} (hx : x ∈ C) :
    linearExtension C hopen hne f hf hh x = f x := extension_eq C hopen hne f hf hx

include hopen hne in
theorem linearMap_ext_of_eq_on_cone {F G : V →ₗ[ℝ] ℝ}
    (hFG : ∀ x ∈ C, F x = G x) : F = G := by
  first
  | ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    rw [map_sub, map_sub, hFG a ha, hFG b hb]

/-- The two-variable extension is the actual four-term polarization of pairs
of cone elements. -/
def bilinearExtensionValue (f : V → V → ℝ) (x y : V) : ℝ :=
  extension C hopen hne (fun a => extension C hopen hne (f a) y) x

theorem bilinearExtensionValue_add_function (f g : V → V → ℝ) (x y : V) :
    bilinearExtensionValue C hopen hne (fun a b => f a b + g a b) x y =
      bilinearExtensionValue C hopen hne f x y + bilinearExtensionValue C hopen hne g x y := by
  first
  | simp only [bilinearExtensionValue, extension_add_function]

theorem bilinearExtensionValue_smul_function (r : ℝ) (f : V → V → ℝ) (x y : V) :
    bilinearExtensionValue C hopen hne (fun a b => r * f a b) x y =
      r * bilinearExtensionValue C hopen hne f x y := by
  first
  | simp only [bilinearExtensionValue, extension_smul_function]

include hopen in
theorem bilinear_reference_inequality_of_cone
    (B : LinearMap.BilinForm ℝ V) (hsym : ∀ x y, B x y = B y x)
    {h : V} (hh : h ∈ C)
    (hineq : ∀ y ∈ C, B y y * B h h ≤ B y h ^ 2) (x : V) :
    B x x * B h h ≤ B x h ^ 2 := by
  first
  | obtain ⟨ε, hε, hy⟩ := exists_pos_sub_mem C hopen hh (-x)
    rw [smul_neg, sub_neg_eq_add] at hy
    have hi := hineq _ hy
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hsym h x] at hi
    have he : ε ^ 2 * (B x x * B h h - B x h ^ 2) ≤ 0 := by nlinarith
    have he' : ε ^ 2 * (B x x * B h h - B x h ^ 2) ≤ ε ^ 2 * 0 := by
      simpa only [mul_zero] using he
    exact sub_nonpos.mp (Iff.mp (mul_le_mul_iff_right₀ (sq_pos_of_pos hε)) he')

theorem bilinearExtensionValue_symmetric (f : V → V → ℝ)
    (hs : ∀ x ∈ C, ∀ y ∈ C, f x y = f y x) (x y : V) :
    bilinearExtensionValue C hopen hne f x y = bilinearExtensionValue C hopen hne f y x := by
  first
  | unfold bilinearExtensionValue extension
    dsimp only
    rw [hs _ (positivePart_mem C hopen hne x) _ (positivePart_mem C hopen hne y),
      hs _ (positivePart_mem C hopen hne x) _ (negativePart_mem C hopen hne y),
      hs _ (negativePart_mem C hopen hne x) _ (positivePart_mem C hopen hne y),
      hs _ (negativePart_mem C hopen hne x) _ (negativePart_mem C hopen hne y)]
    ring

theorem bilinearExtensionValue_eq (f : V → V → ℝ)
    (ha : ∀ y ∈ C, AdditiveOn C (fun x => f x y))
    (hb : ∀ x ∈ C, AdditiveOn C (f x))
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) :
    bilinearExtensionValue C hopen hne f x y = f x y := by
  first
  | unfold bilinearExtensionValue
    have he : extension C hopen hne (fun a => extension C hopen hne (f a) y) x =
        extension C hopen hne (fun a => f a y) x :=
      extension_congr C hopen hne (fun a ha => extension_eq C hopen hne (f a) (hb a ha) hy) x
    rw [he, extension_eq C hopen hne _ (ha y hy) hx]

def bilinearExtension (f : V → V → ℝ)
    (ha : ∀ y ∈ C, AdditiveOn C (fun x => f x y))
    (hha : ∀ y ∈ C, PositiveHomogeneousOn C (fun x => f x y))
    (hb : ∀ x ∈ C, AdditiveOn C (f x))
    (hhb : ∀ x ∈ C, PositiveHomogeneousOn C (f x)) : LinearMap.BilinForm ℝ V := by
  first
  | let F := bilinearExtensionValue C hopen hne f
    have hleftadd (x z y : V) : F (x + z) y = F x y + F z y := by
      first
      | apply extension_add C hopen hne
        intro a ha' b hb'
        apply Eq.trans (extension_congr C hopen hne
          (fun u hu => ha u hu a ha' b hb') y)
        exact extension_add_function C hopen hne (f a) (f b) y
    have hleftsmul (r : ℝ) (x y : V) : F (r • x) y = r * F x y := by
      first
      | apply extension_smul C hopen hne
        · intro a ha' b hb'
          exact Eq.trans (extension_congr C hopen hne (fun u hu => ha u hu a ha' b hb') y)
            (extension_add_function C hopen hne (f a) (f b) y)
        · intro t ht a ha'
          exact Eq.trans (extension_congr C hopen hne (fun u hu => hha u hu t ht a ha') y)
            (extension_smul_function C hopen hne t (f a) y)
    have hrightadd (x y z : V) : F x (y + z) = F x y + F x z := by
      first
      | exact Eq.trans (extension_congr C hopen hne
          (fun a ha' => extension_add C hopen hne (f a) (hb a ha') y z) x)
            (extension_add_function C hopen hne _ _ x)
    have hrightsmul (r : ℝ) (x y : V) : F x (r • y) = r * F x y := by
      first
      | exact Eq.trans (extension_congr C hopen hne
          (fun a ha' => extension_smul C hopen hne (f a) (hb a ha') (hhb a ha') r y) x)
            (extension_smul_function C hopen hne r _ x)
    exact {
      toFun := fun x => {
        toFun := F x
        map_add' := hrightadd x
        map_smul' := fun r y => hrightsmul r x y
      }
      map_add' := fun x y => LinearMap.ext (hleftadd x y)
      map_smul' := fun r x => LinearMap.ext (hleftsmul r x)
    }

end VolumePolynomials.OpenConeExtension
end -- closes the original EOF section from source line 24
end -- closes the original EOF section from source line 12
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/OpenConeExtension.lean -/

/- BEGIN SOURCE: VolumePolynomials/SupportTypeCone.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# The full open cone of a simple support type

The cone remembers exactly the feasible active bases. Its definition imposes
strict inequalities only at feasible vertices, so it does not subdivide the
type by irrelevant intersections of exterior hyperplanes. It contains all
positive common-refinement approximants and is closed under addition and
positive scaling.
-/

noncomputable section
open Set Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def typeRegion (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l)) : Set (ι → ℝ) :=
  {h | (∀ i, 0 < h i) ∧
    (∀ b ∈ F, ∀ i ∉ b.val, l i (vertexMap l b h) < h i) ∧
    feasibleBases l h ⊆ F}

theorem typeRegion_feasibleBases (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    {h : ι → ℝ} (hh : h ∈ typeRegion l F) : feasibleBases l h = F := by
  first
  | apply Subset.antisymm hh.2.2
    intro b hb i
    by_cases hi : i ∈ b.val
    · exact (vertexMap_active l b h ⟨i, hi⟩).le
    · exact (hh.2.1 b hb i hi).le

theorem typeRegion_strict (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    {h : ι → ℝ} (hh : h ∈ typeRegion l F) :
    ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i := by
  first
  | rw [typeRegion_feasibleBases l F hh]
    exact hh.2.1

theorem isOpen_typeRegion (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l)) :
    IsOpen (typeRegion l F) := by
  first
  | classical
    have he : typeRegion l F = {h | ∀ i, 0 < h i} ∩
        (⋂ b : BasisIndex l, if b ∈ F then
          ⋂ i : ι, if i ∈ b.val then Set.univ
          else {h | l i (vertexMap l b h) < h i}
        else {h | b ∈ feasibleBases l h}ᶜ) := by
      ext h
      simp only [typeRegion, mem_ofPred_eq, mem_inter_iff, mem_iInter, Set.subset_def]
      constructor
      · rintro ⟨hp, hs, hf⟩
        refine ⟨hp, fun b => ?_⟩
        by_cases hb : b ∈ F
        · simp only [hb, ite_true, mem_iInter]
          intro i
          by_cases hi : i ∈ b.val
          · simp only [hi, ite_true, mem_univ]
          · simpa only [hi, ite_false, mem_ofPred_eq] using hs b hb i hi
        · simpa only [hb, ite_false, mem_compl_iff, mem_ofPred_eq] using mt (hf b) hb
      · rintro ⟨hp, hs⟩
        refine ⟨hp, ?_, ?_⟩
        · intro b hb i hi
          have hb' := hs b
          simp only [hb, ite_true, mem_iInter] at hb'
          simpa only [hi, ite_false, mem_ofPred_eq] using hb' i
        · intro b hb
          by_contra hnot
          have hn := hs b
          simpa only [hnot, ite_false, mem_compl_iff, mem_ofPred_eq, hb, not_true_eq_false] using hn
    rw [he]
    apply isOpen_positiveHeights.inter
    apply isOpen_iInter_of_finite
    intro b
    split_ifs
    · apply isOpen_iInter_of_finite
      intro i
      split_ifs
      · exact isOpen_univ
      · exact isOpen_lt ((l i).continuous.comp (vertexMap l b).continuous) (continuous_apply i)
    · exact (isClosed_feasibleBasis l b).isOpen_compl

theorem mem_typeRegion_self (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) (hp : ∀ i, 0 < h i) :
    h ∈ typeRegion l (feasibleBases l h) :=
  ⟨hp, strict_inactive_of_generic l h hg, Set.Subset.rfl⟩

theorem feasibleBases_smul (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {r : ℝ} (hr : 0 < r) : feasibleBases l (r • h) = feasibleBases l h := by
  first
  | ext b
    change (∀ i, l i (vertexMap l b (r • h)) ≤ (r • h) i) ↔
      (∀ i, l i (vertexMap l b h) ≤ h i)
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul, mul_le_mul_iff_of_pos_left hr]

theorem typeRegion_smul (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    {h : ι → ℝ} (hh : h ∈ typeRegion l F) {r : ℝ} (hr : 0 < r) :
    r • h ∈ typeRegion l F := by
  first
  | refine ⟨fun i => mul_pos hr (hh.1 i), ?_, ?_⟩
    · intro b hb i hi
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using
        mul_lt_mul_of_pos_left (hh.2.1 b hb i hi) hr
    · rw [feasibleBases_smul l h hr]
      exact hh.2.2

theorem typeRegion_add (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    (h₀ : ι → ℝ) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h k : ι → ℝ} (hh : h ∈ typeRegion l F) (hk : k ∈ typeRegion l F) :
    h + k ∈ typeRegion l F := by
  first
  | let Q := toBody l h₀ hp hc h hh.1
    let R := toBody l h₀ hp hc k hk.1
    have hvertex : ∀ b ∈ feasibleBases l k, vertexMap l b h ∈ Q := by
      intro b hb
      have hbh : b ∈ feasibleBases l h := by
        rw [typeRegion_feasibleBases l F hh, ← typeRegion_feasibleBases l F hk]
        exact hb
      exact hbh
    have hsimple := typeRegion_strict l F hk
    refine ⟨fun i => add_pos (hh.1 i) (hk.1 i), ?_, ?_⟩
    · intro b hb i hi
      have hbk : b ∈ feasibleBases l k := by rw [typeRegion_feasibleBases l F hk]; exact hb
      simpa only [one_smul] using refinement_vertex_strict_inactive l k hsimple Q h
        (fun x hx i => hx i) hvertex zero_lt_one b hbk i hi
    · have he := feasibleBases_minkowski_refinement l k hsimple R Q rfl h
        (fun x hx i => hx i) hvertex zero_lt_one
      simpa only [one_smul, typeRegion_feasibleBases l F hk] using he.subset

theorem body_add_of_typeRegion (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    (h₀ : ι → ℝ) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h k : ι → ℝ} (hh : h ∈ typeRegion l F) (hk : k ∈ typeRegion l F) :
    body l (h + k) = body l h + body l k := by
  first
  | let Q := toBody l h₀ hp hc h hh.1
    let R := toBody l h₀ hp hc k hk.1
    have hvertex : ∀ b ∈ feasibleBases l k, vertexMap l b h ∈ Q := by
      intro b hb
      rw [typeRegion_feasibleBases l F hk] at hb
      have hbh : b ∈ feasibleBases l h := by rw [typeRegion_feasibleBases l F hh]; exact hb
      exact hbh
    have he := minkowski_eq_halfspaces_of_refinement l k (typeRegion_strict l F hk)
      R Q rfl h (fun x hx i => hx i) hvertex zero_lt_one
    have hQ : (Q : Set E) = body l h := rfl
    have hR : (R : Set E) = body l k := rfl
    simpa only [one_smul, ConvexBody.coe_add, hQ, hR] using he.symm

def typeCone (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) : ConvexCone ℝ (ι → ℝ) where
  carrier := typeRegion l (feasibleBases l h₀)
  smul_mem' := by
    intro r hr h hh
    exact typeRegion_smul l _ hh hr
  add_mem' := by
    intro h hh k hk
    exact typeRegion_add l _ h₀ hp hc hh hk

theorem typeCone_isOpen (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) :
    IsOpen (typeCone l h₀ hp hc : Set (ι → ℝ)) := isOpen_typeRegion l _

theorem typeCone_nonempty (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) :
    (typeCone l h₀ hp hc : Set (ι → ℝ)).Nonempty :=
  ⟨h₀, mem_typeRegion_self l h₀ hg hp⟩

def coneBody (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : typeCone l h₀ hp hc) : ConvexBody E := toBody l h₀ hp hc h.val h.property.1

theorem coneBody_add (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h k : typeCone l h₀ hp hc) :
    coneBody l h₀ hp hc ⟨h.val + k.val, (typeCone l h₀ hp hc).add_mem h.property k.property⟩ =
      coneBody l h₀ hp hc h + coneBody l h₀ hp hc k := by
  first
  | apply ConvexBody.ext
    exact body_add_of_typeRegion l _ h₀ hp hc h.property k.property

theorem coneBody_smul (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : typeCone l h₀ hp hc) {r : ℝ} (hr : 0 < r) :
    coneBody l h₀ hp hc ⟨r • h.val, (typeCone l h₀ hp hc).smul_mem hr h.property⟩ =
      r • coneBody l h₀ hp hc h := by
  first
  | apply ConvexBody.ext
    exact body_smul l h.val hr

namespace CommonRefinement

variable {κ : Type*} [Fintype κ] {K : κ → ConvexBody E} (D : CommonRefinement K)

def supportCone : ConvexCone ℝ (Fin D.facets.count → ℝ) :=
  typeCone D.facets.normal D.height D.height_pos (D.reference_eq ▸ D.reference.isCompact)

theorem supportCone_isOpen : IsOpen (D.supportCone : Set (Fin D.facets.count → ℝ)) :=
  typeCone_isOpen _ _ _ _

theorem supportCone_nonempty : (D.supportCone : Set (Fin D.facets.count → ℝ)).Nonempty :=
  typeCone_nonempty _ _ D.generic _ _

theorem approximantHeight_mem_supportCone (h0 : ∀ k, (0 : E) ∈ K k)
    {r : ℝ} (hr : 0 < r) (k : κ) : D.approximantHeight r k ∈ D.supportCone :=
  ⟨D.approximantHeight_pos h0 hr k, D.approximant_strict_inactive hr k,
    (D.approximant_feasibleBases hr k).subset⟩

end CommonRefinement
end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SupportTypeCone.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedSupportForm.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# The actual mixed-volume form on all support vectors

On the open cone of a fixed simple support type, support addition is actual
Minkowski addition. The proved mixed-volume laws therefore extend uniquely to
an ordinary symmetric bilinear form on every real height vector. Its matrix
is defined by evaluation on the ordinary coordinate basis. No geometric
inequality or sign condition is part of this construction.
-/

noncomputable section
open Set MeasureTheory Module LinearMap Matrix
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- A harmless total extension of the genuine support-body map. Every use in
the bilinear extension evaluates this map at an element of the support cone. -/
def bodyAtHeight (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) : ConvexBody E :=
  if hh : h ∈ typeCone l h₀ hp hc then coneBody l h₀ hp hc ⟨h, hh⟩ else 0

theorem bodyAtHeight_eq (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) :
    bodyAtHeight l h₀ hp hc h = coneBody l h₀ hp hc ⟨h, hh⟩ := by
  first
  | simp only [bodyAtHeight, dif_pos hh]

theorem coe_bodyAtHeight (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) :
    (bodyAtHeight l h₀ hp hc h : Set E) = body l h := by
  first
  | rw [bodyAtHeight_eq l h₀ hp hc hh]
    rfl

theorem bodyAtHeight_add (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h k : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (hk : k ∈ typeCone l h₀ hp hc) :
    bodyAtHeight l h₀ hp hc (h + k) =
      bodyAtHeight l h₀ hp hc h + bodyAtHeight l h₀ hp hc k := by
  first
  | rw [bodyAtHeight_eq l h₀ hp hc ((typeCone l h₀ hp hc).add_mem hh hk),
      bodyAtHeight_eq l h₀ hp hc hh, bodyAtHeight_eq l h₀ hp hc hk]
    exact coneBody_add l h₀ hp hc ⟨h, hh⟩ ⟨k, hk⟩

theorem bodyAtHeight_smul (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) {r : ℝ} (hr : 0 < r) :
    bodyAtHeight l h₀ hp hc (r • h) = r • bodyAtHeight l h₀ hp hc h := by
  first
  | rw [bodyAtHeight_eq l h₀ hp hc ((typeCone l h₀ hp hc).smul_mem hr hh),
      bodyAtHeight_eq l h₀ hp hc hh]
    exact coneBody_smul l h₀ hp hc ⟨h, hh⟩ hr

variable [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_cons_cons_swap {d : ℕ} (A B : ConvexBody E)
    (K : Fin d → ConvexBody E) :
    mixedVolume μ (Fin.cons A (Fin.cons B K)) =
      mixedVolume μ (Fin.cons B (Fin.cons A K)) := by
  first
  | have he := mixedVolume_reindex μ (Fin.cons A (Fin.cons B K))
      (Equiv.swap (0 : Fin (d + 2)) 1)
    change mixedVolume μ ((Matrix.vecCons A (Matrix.vecCons B K)) ∘
      Equiv.swap 0 1) = _ at he
    rw [Matrix.cons_cons_comp_swap_zero_one] at he
    exact he.symm

theorem mixedVolume_cons_add {d : ℕ} (A B : ConvexBody E)
    (K : Fin d → ConvexBody E) :
    mixedVolume μ (Fin.cons (A + B) K) =
      mixedVolume μ (Fin.cons A K) + mixedVolume μ (Fin.cons B K) := by
  first
  | simpa only [Fin.update_cons_zero] using
      mixedVolume_add μ (Fin.cons A K) 0 A B

theorem mixedVolume_cons_smul {d : ℕ} (A : ConvexBody E)
    (K : Fin d → ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume μ (Fin.cons (r • A) K) = r * mixedVolume μ (Fin.cons A K) := by
  first
  | simpa only [Fin.update_cons_zero] using
      mixedVolume_smul μ (Fin.cons A K) 0 A hr

def mixedSupportValue (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) : ℝ :=
  mixedVolume μ (Fin.cons (bodyAtHeight l h₀ hp hc x)
    (Fin.cons (bodyAtHeight l h₀ hp hc y) K))

theorem mixedSupportValue_symmetric (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) :
    mixedSupportValue μ l h₀ hp hc K x y = mixedSupportValue μ l h₀ hp hc K y x :=
  mixedVolume_cons_cons_swap μ _ _ K

theorem mixedSupportValue_additive_left (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (y : ι → ℝ) :
    OpenConeExtension.AdditiveOn (typeCone l h₀ hp hc)
      (fun x => mixedSupportValue μ l h₀ hp hc K x y) := by
  first
  | intro a ha b hb
    unfold mixedSupportValue
    dsimp only
    rw [bodyAtHeight_add l h₀ hp hc ha hb, mixedVolume_cons_add]

theorem mixedSupportValue_homogeneous_left (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (y : ι → ℝ) :
    OpenConeExtension.PositiveHomogeneousOn (typeCone l h₀ hp hc)
      (fun x => mixedSupportValue μ l h₀ hp hc K x y) := by
  first
  | intro r hr x hx
    unfold mixedSupportValue
    dsimp only
    rw [bodyAtHeight_smul l h₀ hp hc hx hr, mixedVolume_cons_smul μ _ _ hr.le]

theorem mixedSupportValue_additive_right (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x : ι → ℝ) :
    OpenConeExtension.AdditiveOn (typeCone l h₀ hp hc)
      (mixedSupportValue μ l h₀ hp hc K x) := by
  first
  | intro a ha b hb
    simpa only [mixedSupportValue_symmetric μ l h₀ hp hc K x] using
      mixedSupportValue_additive_left μ l h₀ hp hc K x a ha b hb

theorem mixedSupportValue_homogeneous_right (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x : ι → ℝ) :
    OpenConeExtension.PositiveHomogeneousOn (typeCone l h₀ hp hc)
      (mixedSupportValue μ l h₀ hp hc K x) := by
  first
  | intro r hr y hy
    simpa only [mixedSupportValue_symmetric μ l h₀ hp hc K x] using
      mixedSupportValue_homogeneous_left μ l h₀ hp hc K x r hr y hy

/-- The full symmetric bilinear form, defined from the actual mixed volumes
of genuine compact convex bodies through their open support cone. -/
def mixedSupportForm (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) : LinearMap.BilinForm ℝ (ι → ℝ) :=
  OpenConeExtension.bilinearExtension (typeCone l h₀ hp hc)
    (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
    (mixedSupportValue μ l h₀ hp hc K)
    (fun y _ => mixedSupportValue_additive_left μ l h₀ hp hc K y)
    (fun y _ => mixedSupportValue_homogeneous_left μ l h₀ hp hc K y)
    (fun x _ => mixedSupportValue_additive_right μ l h₀ hp hc K x)
    (fun x _ => mixedSupportValue_homogeneous_right μ l h₀ hp hc K x)

theorem mixedSupportForm_eq_value (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) {x y : ι → ℝ}
    (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    mixedSupportForm μ l h₀ hg hp hc K x y = mixedSupportValue μ l h₀ hp hc K x y :=
  OpenConeExtension.bilinearExtensionValue_eq _ _ _ _
    (fun z _ => mixedSupportValue_additive_left μ l h₀ hp hc K z)
    (fun z _ => mixedSupportValue_additive_right μ l h₀ hp hc K z) hx hy

theorem mixedSupportForm_eq (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) {x y : ι → ℝ}
    (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    mixedSupportForm μ l h₀ hg hp hc K x y =
      mixedVolume μ (Fin.cons (coneBody l h₀ hp hc ⟨x, hx⟩)
        (Fin.cons (coneBody l h₀ hp hc ⟨y, hy⟩) K)) := by
  first
  | change OpenConeExtension.bilinearExtensionValue _ _ _ _ x y = _
    rw [OpenConeExtension.bilinearExtensionValue_eq _ _ _ _
      (fun z _ => mixedSupportValue_additive_left μ l h₀ hp hc K z)
      (fun z _ => mixedSupportValue_additive_right μ l h₀ hp hc K z) hx hy]
    simp only [mixedSupportValue, bodyAtHeight_eq l h₀ hp hc hx,
      bodyAtHeight_eq l h₀ hp hc hy]

theorem mixedSupportForm_symmetric (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) :
    mixedSupportForm μ l h₀ hg hp hc K x y =
      mixedSupportForm μ l h₀ hg hp hc K y x :=
  OpenConeExtension.bilinearExtensionValue_symmetric _ _ _ _
    (fun x _ y _ => mixedSupportValue_symmetric μ l h₀ hp hc K x y) x y

def mixedSupportMatrix (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) : Matrix ι ι ℝ :=
  fun i j => mixedSupportForm μ l h₀ hg hp hc K (Pi.single i 1) (Pi.single j 1)

theorem mixedSupportMatrix_symmetric (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) :
    ∀ i j, mixedSupportMatrix μ l h₀ hg hp hc K i j =
      mixedSupportMatrix μ l h₀ hg hp hc K j i :=
  fun i j => mixedSupportForm_symmetric μ l h₀ hg hp hc K _ _

theorem mixedSupportForm_eq_dotProduct (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) :
    mixedSupportForm μ l h₀ hg hp hc K x y =
      x ⬝ᵥ (mixedSupportMatrix μ l h₀ hg hp hc K *ᵥ y) := by
  first
  | let B := mixedSupportForm μ l h₀ hg hp hc K
    change B x y = _
    calc
      B x y = B (∑ i, x i • Pi.single i 1) (∑ j, y j • Pi.single j 1) := by
        rw [← pi_eq_sum_univ' x, ← pi_eq_sum_univ' y]
      _ = ∑ i, x i * ∑ j, y j * B (Pi.single i 1) (Pi.single j 1) := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = x ⬝ᵥ (mixedSupportMatrix μ l h₀ hg hp hc K *ᵥ y) := by
        simp only [dotProduct, mulVec, mixedSupportMatrix]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 22
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedSupportForm.lean -/

/- BEGIN SOURCE: VolumePolynomials/SupportConeFacets.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Actual facets throughout the open support cone

Every defining height is the attained support value throughout the type cone.
Strict relative-interior facet points persist as a consequence of openness:
lower all the other heights by a small common amount. The fixed-kernel facet
bodies are therefore literal slices in a fixed hyperplane, and increasing a
different height gives actual set inclusion of these lower-dimensional bodies.
-/

noncomputable section
open Set Module Filter
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_feasibleBasis_containing (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (i : ι) :
    ∃ b : BasisIndex l, b ∈ feasibleBases l h₀ ∧ i ∈ b.val := by
  first
  | have hn : (body l h₀).Nonempty := ⟨0, fun i => by
      simpa only [map_zero] using (hp i).le⟩
    obtain ⟨b, hb, hmax⟩ := exists_maximizing_basis l h₀ hc hn (l i)
    obtain ⟨x, hxi, hxj⟩ := hf i
    have hx : x ∈ body l h₀ := by
      intro j
      by_cases hj : j = i
      · subst j
        exact hxi.le
      · exact (hxj j hj).le
    refine ⟨b, hb, ?_⟩
    by_contra hi
    have hstrict := strict_inactive_of_generic l h₀ hg b hb i hi
    have hbound := hmax x hx
    rw [hxi] at hbound
    exact (not_lt_of_ge hbound) hstrict

theorem bodyAtHeight_support (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (i : ι) :
    SupportGeometry.support (bodyAtHeight l h₀ hp hc h : Set E) (l i) = h i := by
  first
  | obtain ⟨b, hb, hi⟩ := exists_feasibleBasis_containing l h₀ hg hp hc hf i
    have hbh : b ∈ feasibleBases l h := by
      rw [typeRegion_feasibleBases l _ hh]
      exact hb
    apply le_antisymm
    · apply SupportGeometry.support_le (bodyAtHeight l h₀ hp hc h).nonempty
      intro x hx
      rw [coe_bodyAtHeight l h₀ hp hc hh] at hx
      exact hx i
    · have hm : vertexMap l b h ∈ bodyAtHeight l h₀ hp hc h := by
        change vertexMap l b h ∈ (bodyAtHeight l h₀ hp hc h : Set E)
        rw [coe_bodyAtHeight l h₀ hp hc hh]
        exact hbh
      simpa only [vertexMap_active l b h ⟨i, hi⟩] using
        SupportGeometry.le_support (bodyAtHeight l h₀ hp hc h).isCompact (l i) hm

theorem typeCone_strictFacets (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) : StrictFacets l h := by
  first
  | intro i
    let q : ι → ℝ := fun j => if j = i then 0 else 1
    obtain ⟨ε, hε, hh'⟩ := OpenConeExtension.exists_pos_sub_mem
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc) hh q
    obtain ⟨b, hb, hi⟩ := exists_feasibleBasis_containing l h₀ hg hp hc hf i
    have hbh : b ∈ feasibleBases l (h - ε • q) := by
      rw [typeRegion_feasibleBases l _ hh']
      exact hb
    refine ⟨vertexMap l b (h - ε • q), ?_, ?_⟩
    · rw [vertexMap_active l b _ ⟨i, hi⟩]
      simp only [Pi.sub_apply, Pi.smul_apply, q, if_pos rfl, ite_true, smul_zero, sub_zero]
    · intro j hji
      have hj := hbh j
      simp only [Pi.sub_apply, Pi.smul_apply, q, if_neg hji, smul_eq_mul, mul_one] at hj
      linarith

theorem kernelBody_bodyAtHeight_mem_iff (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (i : ι) (v : E) (hv : l i v = 1)
    (z : LinearMap.ker (l i).toLinearMap) :
    z ∈ kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv ↔
      h i • v + (z : E) ∈ body l h := by
  first
  | change z ∈ LinearFrame.kernelPart (l i) v hv ''
      (l i).toExposed (bodyAtHeight l h₀ hp hc h : Set E) ↔ _
    rw [exposed_eq_support_level (bodyAtHeight l h₀ hp hc h).isCompact
      (bodyAtHeight l h₀ hp hc h).nonempty,
      bodyAtHeight_support l h₀ hg hp hc hf hh i,
      coe_bodyAtHeight l h₀ hp hc hh]
    constructor
    · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
      change h i • v + (x - l i x • v) ∈ body l h
      rw [hxi]
      rw [show h i • v + (x - h i • v) = x by abel]
      exact hx
    · intro hz
      refine ⟨h i • v + (z : E), ⟨hz, ?_⟩, ?_⟩
      · simp only [map_add, map_smul, smul_eq_mul, hv, mul_one,
          show l i (z : E) = 0 from z.property, add_zero]
      · apply Subtype.ext
        change h i • v + (z : E) - l i (h i • v + (z : E)) • v = (z : E)
        simp only [map_add, map_smul, smul_eq_mul, hv, mul_one,
          show l i (z : E) = 0 from z.property, add_zero]
        abel

/-- Raising any constraints while keeping the selected facet height fixed
enlarges its body in the same kernel coordinates. -/
theorem kernelBody_bodyAtHeight_mono (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h k : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (hk : k ∈ typeCone l h₀ hp hc)
    (hmono : ∀ j, h j ≤ k j) (i : ι) (hi : h i = k i)
    (v : E) (hv : l i v = 1) :
    kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv ≤
      kernelBody (bodyAtHeight l h₀ hp hc k) (l i) v hv := by
  first
  | intro z hz
    rw [kernelBody_bodyAtHeight_mem_iff l h₀ hg hp hc hf hh i v hv] at hz
    rw [kernelBody_bodyAtHeight_mem_iff l h₀ hg hp hc hf hk i v hv, ← hi]
    exact fun j => (hz j).trans (hmono j)

theorem kernelBody_add (K L : ConvexBody E) (l : E →L[ℝ] ℝ)
    (v : E) (hv : l v = 1) :
    kernelBody (K + L) l v hv = kernelBody K l v hv + kernelBody L l v hv := by
  first
  | apply ConvexBody.ext
    change LinearFrame.kernelPart l v hv '' l.toExposed ((K : Set E) + (L : Set E)) = _
    rw [PolytopeFaces.exposed_add, Set.image_add (LinearFrame.kernelPart l v hv)]
    rfl

theorem kernelBody_smul (K : ConvexBody E) (l : E →L[ℝ] ℝ)
    (v : E) (hv : l v = 1) {r : ℝ} (hr : 0 < r) :
    kernelBody (r • K) l v hv = r • kernelBody K l v hv := by
  first
  | apply ConvexBody.ext
    change LinearFrame.kernelPart l v hv '' l.toExposed (r • (K : Set E)) = _
    rw [PolytopeFaces.exposed_smul l _ hr,
      Set.image_smul_comm (LinearFrame.kernelPart l v hv) r _
        (fun x => (LinearFrame.kernelPart l v hv).map_smul r x)]
    rfl

/-- The selected facet has nonempty interior in its own kernel, in every
ambient dimension. This is proved by the actual strict slice inequalities. -/
theorem kernelBody_bodyAtHeight_interior_nonempty
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (i : ι) (v : E) (hv : l i v = 1) :
    (interior (kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv :
      Set (LinearMap.ker (l i).toLinearMap))).Nonempty := by
  first
  | obtain ⟨x, hxi, hxj⟩ := typeCone_strictFacets l h₀ hg hp hc hf hh i
    let U : Set (LinearMap.ker (l i).toLinearMap) :=
      {z | ∀ j, j ≠ i → l j (h i • v + (z : E)) < h j}
    have hopen : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
        isOpen_lt ((l j).continuous.comp (continuous_const.add continuous_subtype_val))
          continuous_const
    have hsub : U ⊆ (kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv :
        Set (LinearMap.ker (l i).toLinearMap)) := by
      intro z hz
      change z ∈ kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv
      rw [kernelBody_bodyAtHeight_mem_iff l h₀ hg hp hc hf hh i v hv]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [map_add, map_smul, smul_eq_mul, hv, mul_one,
          show l i (z : E) = 0 from z.property, add_zero, le_refl]
      · exact (hz j hji).le
    have hpoint : h i • v + ((LinearFrame.kernelPart (l i) v hv x :
        LinearMap.ker (l i).toLinearMap) : E) = x := by
      rw [LinearFrame.kernelPart_coe, hxi]
      abel
    refine ⟨LinearFrame.kernelPart (l i) v hv x, ?_⟩
    apply (hopen.subset_interior_iff.mpr hsub)
    intro j hji
    rw [hpoint]
    exact hxj j hji

theorem typeCone_sum_mem {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : κ → ι → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc) :
    (∑ j, h j) ∈ typeCone l h₀ hp hc :=
  Finset.sum_induction_nonempty h (fun x => x ∈ typeCone l h₀ hp hc)
    (fun _ _ ha hb => (typeCone l h₀ hp hc).add_mem ha hb)
    Finset.univ_nonempty (fun j _ => hh j)

theorem bodyAtHeight_sum {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : κ → ι → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc) :
    bodyAtHeight l h₀ hp hc (∑ j, h j) = ∑ j, bodyAtHeight l h₀ hp hc (h j) := by
  first
  | have he := Finset.sum_induction_nonempty
      (fun j => (h j, bodyAtHeight l h₀ hp hc (h j)))
      (fun p : (ι → ℝ) × ConvexBody E =>
        p.1 ∈ typeCone l h₀ hp hc ∧ bodyAtHeight l h₀ hp hc p.1 = p.2)
      (fun a b ha hb => ⟨(typeCone l h₀ hp hc).add_mem ha.1 hb.1,
        (bodyAtHeight_add l h₀ hp hc ha.1 hb.1).trans (congrArg₂ (· + ·) ha.2 hb.2)⟩)
      (Finset.univ_nonempty : (Finset.univ : Finset κ).Nonempty)
      (fun j _ => ⟨hh j, rfl⟩)
    rw [← prod_mk_sum] at he
    exact he.2

theorem bodyAtHeight_weighted_sum {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : κ → ι → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc)
    (t : κ → ℝ) (ht : ∀ j, 0 < t j) :
    bodyAtHeight l h₀ hp hc (∑ j, t j • h j) =
      ∑ j, t j • bodyAtHeight l h₀ hp hc (h j) := by
  first
  | rw [bodyAtHeight_sum l h₀ hp hc _
      (fun j => (typeCone l h₀ hp hc).smul_mem (ht j) (hh j))]
    exact Finset.sum_congr rfl (fun j _ => bodyAtHeight_smul l h₀ hp hc (hh j) (ht j))

/-- The same, originally constructed normals form a genuine `FixedFacets`
family for every finite nonempty tuple from the type cone. This exposes the
already proved first-variation identity without choosing a new facet system. -/
def fixedFacetsOfCone {m : ℕ} {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (h : κ → Fin m → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc) :
    FixedFacets (fun j => (bodyAtHeight l h₀ hp hc (h j) : Set E)) where
  count := m
  normal := l
  normal_ne_zero := hn
  positive_ray_injective := hray
  body_eq t ht := by
    first
    | have hsupport (j : κ) (i : Fin m) :
          SupportGeometry.support (bodyAtHeight l h₀ hp hc (h j) : Set E) (l i) = h j i :=
        bodyAtHeight_support l h₀ hg hp hc hf (hh j) i
      simp only [hsupport]
      have hs := typeCone_sum_mem l h₀ hp hc (fun j => t j • h j)
        (fun j => (typeCone l h₀ hp hc).smul_mem (ht j) (hh j))
      have he := congrArg (fun K : ConvexBody E => (K : Set E))
        (bodyAtHeight_weighted_sum l h₀ hp hc h hh t ht)
      rw [coe_bodyAtHeight l h₀ hp hc hs, coe_sum_body] at he
      simpa only [ConvexBody.coe_smul, body, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using he.symm
  strict_face_point := by
    first
    | have hsupport (j : κ) (i : Fin m) :
          SupportGeometry.support (bodyAtHeight l h₀ hp hc (h j) : Set E) (l i) = h j i :=
        bodyAtHeight_support l h₀ hg hp hc hf (hh j) i
      have hs := typeCone_sum_mem l h₀ hp hc h hh
      have hf' := typeCone_strictFacets l h₀ hg hp hc hf hs
      simpa only [hsupport, StrictFacets, Finset.sum_apply] using hf'

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SupportConeFacets.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedSupportOperator.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Facet coordinates and the sign of the genuine mixed-support operator

The first-variation identity identifies every row of the symmetric form with
an actual lower-dimensional mixed volume. Increasing a distinct support
height enlarges the corresponding fixed-hyperplane slice, so monotonicity of
actual mixed volume proves every off-diagonal matrix entry nonnegative.
This avoids assuming a ridge formula or an abstract operator representation.
-/

noncomputable section
open Set MeasureTheory Module Matrix LinearMap
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m d : ℕ}

private theorem map_finCons {α β : Type*} {n : ℕ}
    (f : α → β) (a : α) (s : Fin n → α) :
    (fun j : Fin (n + 1) => f ((Fin.cons a s : Fin (n + 1) → α) j)) =
      (Fin.cons (f a) (fun j : Fin n => f (s j)) : Fin (n + 1) → β) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

private theorem kernelBody_finCons (a : ConvexBody E) (s : Fin d → ConvexBody E)
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    (fun j : Fin (d + 1) =>
      kernelBody ((Fin.cons a s : Fin (d + 1) → ConvexBody E) j) l v hv) =
      (Fin.cons (kernelBody a l v hv) (fun j : Fin d => kernelBody (s j) l v hv) :
        Fin (d + 1) → ConvexBody (LinearMap.ker l.toLinearMap)) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

def coneTuple (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin d → Fin m → ℝ) : Fin d → ConvexBody E :=
  fun j => bodyAtHeight l h₀ hp hc (H j)

def facetMixedValue (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin d → Fin m → ℝ) (y : Fin m → ℝ)
    (i : Fin m) (v : E) (hv : l i v = 1) : ℝ :=
  mixedVolume (kernelMeasure (l i))
    (Fin.cons (kernelBody (bodyAtHeight l h₀ hp hc y) (l i) v hv)
      (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv))

theorem mixedSupportForm_facet_on_cone
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    {x y : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc)
    (hy : y ∈ typeCone l h₀ hp hc) :
    ((d + 2 : ℕ) : ℝ) *
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) x y =
      ∑ i, facetFrameFactor (l i) (v i) (hv i) * x i *
        facetMixedValue l h₀ hp hc H y i (v i) (hv i) := by
  first
  | let G : Fin (d + 1) → Fin m → ℝ := Fin.cons y H
    have hG : ∀ j, G j ∈ typeCone l h₀ hp hc :=
      fun j => Fin.cases hy hH j
    let K : Fin (d + 1) → ConvexBody E := fun j => bodyAtHeight l h₀ hp hc (G j)
    let D := fixedFacetsOfCone l h₀ hg hp hc hf hn hray G hG
    have hK0 : ∀ j, (0 : E) ∈ K j := by
      intro j
      change (0 : E) ∈ (K j : Set E)
      rw [show (K j : Set E) = body l (G j) from coe_bodyAtHeight l h₀ hp hc (hG j)]
      exact fun i => by simpa only [map_zero] using ((hG j).1 i).le
    have hsum : (∑ j, (K j : Set E)) = body l (∑ j, G j) := by
      rw [← coe_sum_body, ← bodyAtHeight_sum l h₀ hp hc G hG,
        coe_bodyAtHeight l h₀ hp hc (typeCone_sum_mem l h₀ hp hc G hG)]
    have hKint : (0 : E) ∈ interior (∑ j, (K j : Set E)) := by
      rw [hsum]
      exact zero_mem_interior_body l _ (typeCone_sum_mem l h₀ hp hc G hG).1
    have he := mixedVolume_facet_identity K D hK0 hKint v hv
      (bodyAtHeight l h₀ hp hc x)
    have hsupport (i : Fin m) :
        SupportGeometry.support (bodyAtHeight l h₀ hp hc x : Set E) (l i) = x i :=
      bodyAtHeight_support l h₀ hg hp hc hf hx i
    rw [mixedSupportForm_eq_value volume l h₀ hg hp hc _ hx hy]
    unfold mixedSupportValue coneTuple facetMixedValue
    have hadd : d + 1 + 1 = d + 2 := by omega
    simp only [D, fixedFacetsOfCone, K, G, coneTuple, mixedSupportValue,
      hsupport, facetMixedValue, map_finCons, kernelBody_finCons, hadd] at he
    convert he using 1 <;> rfl

/-- The facet formula extends in its first argument to every real height
direction, not just those that define a convex body. -/
theorem mixedSupportForm_facet
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (x : Fin m → ℝ) {y : Fin m → ℝ} (hy : y ∈ typeCone l h₀ hp hc) :
    ((d + 2 : ℕ) : ℝ) *
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) x y =
      ∑ i, facetFrameFactor (l i) (v i) (hv i) * x i *
        facetMixedValue l h₀ hp hc H y i (v i) (hv i) := by
  first
  | obtain ⟨a, ha, b, hb, rfl⟩ := OpenConeExtension.exists_difference
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (typeCone_nonempty l h₀ hg hp hc) x
    have hfa := mixedSupportForm_facet_on_cone l h₀ hg hp hc hf hn hray H hH v hv ha hy
    have hfb := mixedSupportForm_facet_on_cone l h₀ hg hp hc hf hn hray H hH v hv hb hy
    rw [LinearMap.BilinForm.sub_left, mul_sub, hfa, hfb, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring

theorem mixedSupportForm_coordinate_facet
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (i : Fin m) {y : Fin m → ℝ} (hy : y ∈ typeCone l h₀ hp hc) :
    ((d + 2 : ℕ) : ℝ) *
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) (Pi.single i 1) y =
      facetFrameFactor (l i) (v i) (hv i) *
        facetMixedValue l h₀ hp hc H y i (v i) (hv i) := by
  first
  | simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      mixedSupportForm_facet l h₀ hg hp hc hf hn hray H hH v hv (Pi.single i 1) hy

/-- Every off-diagonal entry of the actual symmetric mixed-support matrix is
nonnegative. The proof uses inclusion of genuine fixed-kernel facet bodies. -/
theorem mixedSupportMatrix_offdiag_nonnegative
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ k, H k ∈ typeCone l h₀ hp hc)
    (hdim : finrank ℝ E = d + 2) (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (i j : Fin m) (hij : i ≠ j) :
    0 ≤ mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) i j := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    obtain ⟨ε, hε, hplus⟩ := OpenConeExtension.exists_pos_sub_mem
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc) href (-(Pi.single j 1))
    rw [smul_neg, sub_neg_eq_add] at hplus
    have hle : kernelBody (bodyAtHeight l h₀ hp hc h₀) (l i) (v i) (hv i) ≤
        kernelBody (bodyAtHeight l h₀ hp hc (h₀ + ε • Pi.single j 1)) (l i) (v i) (hv i) := by
      apply kernelBody_bodyAtHeight_mono l h₀ hg hp hc hf href hplus
      · intro k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact le_add_of_nonneg_right (mul_nonneg hε.le (by
          by_cases hk : k = j <;> simp [Pi.single_apply, hk]))
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hij,
          smul_zero, add_zero]
    have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = d + 1 := by
      have he := LinearFrame.finrank_kernel_add_one (l i) (v i) (hv i)
      rw [hdim] at he
      omega
    letI : Nontrivial (LinearMap.ker (l i).toLinearMap) :=
      Module.nontrivial_of_finrank_eq_succ hkdim
    have hmono : facetMixedValue l h₀ hp hc H h₀ i (v i) (hv i) ≤
        facetMixedValue l h₀ hp hc H (h₀ + ε • Pi.single j 1) i (v i) (hv i) :=
      mixedVolume_mono_first_all (kernelMeasure (l i)) _ hkdim _ _ hle
    have hf0 := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray H hH v hv i href
    have hf1 := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray H hH v hv i hplus
    have hscaled := mul_le_mul_of_nonneg_left hmono (facetFrameFactor_nonneg (l i) (v i) (hv i))
    rw [← hf0, ← hf1, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right] at hscaled
    change 0 ≤ mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H)
      (Pi.single i 1) (Pi.single j 1)
    have hdimpos : (0 : ℝ) < ((d + 2 : ℕ) : ℝ) := by positivity
    have hs := Iff.mp (mul_le_mul_iff_of_pos_left hdimpos) hscaled
    have hz : 0 ≤ ε * mixedSupportForm volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc H) (Pi.single i 1) (Pi.single j 1) := by linarith
    exact nonneg_of_mul_nonneg_right hz hε

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 19
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedSupportOperator.lean -/

/- BEGIN SOURCE: VolumePolynomials/OpenConeModuleExtension.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Linear extension from an open cone with an arbitrary module as target

The target needs no topology. This permits finite multilinear maps to be
constructed one argument at a time, without analytic or infinite-dimensional
extension theorems.
-/

noncomputable section
open Set

namespace VolumePolynomials.OpenConeModuleExtension

open OpenConeExtension

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  (C : ConvexCone ℝ V) (hopen : IsOpen (C : Set V)) (hne : (C : Set V).Nonempty)

def AdditiveOn (f : V → W) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, f (a + b) = f a + f b

def PositiveHomogeneousOn (f : V → W) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ C, f (r • x) = r • f x

def extension (f : V → W) (x : V) : W :=
  f (positivePart C hopen hne x) - f (negativePart C hopen hne x)

theorem extension_sub (f : V → W) (hf : AdditiveOn C f)
    {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    extension C hopen hne f (a - b) = f a - f b := by
  first
  | let p := positivePart C hopen hne (a - b)
    let q := negativePart C hopen hne (a - b)
    have hp : p ∈ C := positivePart_mem C hopen hne _
    have hq : q ∈ C := negativePart_mem C hopen hne _
    have he : p - q = a - b := positivePart_sub_negativePart C hopen hne _
    have hadd : p + b = a + q := sub_eq_sub_iff_add_eq_add.mp he
    have hval := congrArg f hadd
    rw [hf p hp b hb, hf a ha q hq] at hval
    exact sub_eq_sub_iff_add_eq_add.mpr hval

theorem extension_eq (f : V → W) (hf : AdditiveOn C f) {x : V} (hx : x ∈ C) :
    extension C hopen hne f x = f x := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    have he := extension_sub C hopen hne f hf (C.add_mem hx hp) hp
    rw [add_sub_cancel_right, hf x hx p hp] at he
    simpa only [add_sub_cancel_right] using he

theorem extension_zero (f : V → W) (hf : AdditiveOn C f) :
    extension C hopen hne f 0 = 0 := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    simpa only [sub_self] using extension_sub C hopen hne f hf hp hp

theorem extension_add (f : V → W) (hf : AdditiveOn C f) (x y : V) :
    extension C hopen hne f (x + y) =
      extension C hopen hne f x + extension C hopen hne f y := by
  first
  | obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    obtain ⟨c, hc, d, hd, rfl⟩ := exists_difference C hopen hne y
    rw [extension_sub C hopen hne f hf ha hb, extension_sub C hopen hne f hf hc hd,
      show (a - b) + (c - d) = (a + c) - (b + d) by abel,
      extension_sub C hopen hne f hf (C.add_mem ha hc) (C.add_mem hb hd),
      hf a ha c hc, hf b hb d hd]
    abel

theorem extension_smul (f : V → W) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) (r : ℝ) (x : V) :
    extension C hopen hne f (r • x) = r • extension C hopen hne f x := by
  first
  | rcases lt_trichotomy r 0 with hr | rfl | hr
    · have hpos : 0 < -r := neg_pos.mpr hr
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [show r • (a - b) = (-r) • b - (-r) • a by
        rw [neg_smul, neg_smul, neg_sub_neg, smul_sub],
        extension_sub C hopen hne f hf (C.smul_mem hpos hb) (C.smul_mem hpos ha),
        hh (-r) hpos b hb, hh (-r) hpos a ha,
        extension_sub C hopen hne f hf ha hb,
        neg_smul, neg_smul, neg_sub_neg, smul_sub]
    · rw [zero_smul, extension_zero C hopen hne f hf, zero_smul]
    · obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [smul_sub, extension_sub C hopen hne f hf (C.smul_mem hr ha) (C.smul_mem hr hb),
        hh r hr a ha, hh r hr b hb, extension_sub C hopen hne f hf ha hb, smul_sub]

def linearExtension (f : V → W) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) : V →ₗ[ℝ] W where
  toFun := extension C hopen hne f
  map_add' := extension_add C hopen hne f hf
  map_smul' := extension_smul C hopen hne f hf hh

theorem linearExtension_eq (f : V → W) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) {x : V} (hx : x ∈ C) :
    linearExtension C hopen hne f hf hh x = f x := extension_eq C hopen hne f hf hx

include hopen hne in
theorem linearMap_ext_of_eq_on_cone {F G : V →ₗ[ℝ] W}
    (hFG : ∀ x ∈ C, F x = G x) : F = G := by
  first
  | ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    rw [map_sub, map_sub, hFG a ha, hFG b hb]

include hopen hne in
/-- Agreement on all genuine cone tuples determines a multilinear map on the
entire vector space. -/
theorem multilinearMap_ext_of_eq_on_cone {n : ℕ}
    {F G : MultilinearMap ℝ (fun _ : Fin n => V) W}
    (hFG : ∀ x : Fin n → V, (∀ i, x i ∈ C) → F x = G x) : F = G := by
  first
  | induction n with
    | zero =>
        ext x
        exact hFG x (fun i => Fin.elim0 i)
    | succ n ih =>
        have he : F.curryLeft = G.curryLeft := by
          apply linearMap_ext_of_eq_on_cone C hopen hne
          intro a ha
          apply ih
          intro x hx
          exact hFG (Fin.cons a x) (fun i => Fin.cases ha hx i)
        ext x
        have he' := congrArg
          (fun T : V →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => V) W =>
            T (x 0) (Fin.tail x)) he
        simpa only [MultilinearMap.curryLeft_apply, Fin.cons_self_tail] using he'

end VolumePolynomials.OpenConeModuleExtension
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/OpenConeModuleExtension.lean -/

/- BEGIN SOURCE: VolumePolynomials/OpenConeMultilinear.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The unique finite multilinear extension from a genuine open cone

The construction is a finite induction on the arity. At each step, the
remaining arguments form an ordinary vector space of multilinear maps, and
the first argument is extended by actual differences of cone elements.
-/

noncomputable section
open Set

namespace VolumePolynomials.OpenConeModuleExtension

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  (C : ConvexCone ℝ V) (hopen : IsOpen (C : Set V)) (hne : (C : Set V).Nonempty)

structure IsMultilinearOnCone {n : ℕ} (f : (Fin n → V) → W) : Prop where
  add : ∀ (x : Fin n → V), (∀ j, x j ∈ C) → ∀ i a, a ∈ C → ∀ b, b ∈ C →
    f (Function.update x i (a + b)) = f (Function.update x i a) + f (Function.update x i b)
  smul : ∀ (x : Fin n → V), (∀ j, x j ∈ C) → ∀ i (r : ℝ), 0 < r → ∀ a, a ∈ C →
    f (Function.update x i (r • a)) = r • f (Function.update x i a)

theorem IsMultilinearOnCone.cons {n : ℕ} {f : (Fin (n + 1) → V) → W}
    (hf : IsMultilinearOnCone C f) {a : V} (ha : a ∈ C) :
    IsMultilinearOnCone C (fun x : Fin n → V => f (Fin.cons a x)) where
  add x hx i b hb c hc := by
    first
    | simpa only [Fin.cons_update] using
        hf.add (Fin.cons a x) (fun j => Fin.cases ha hx j) i.succ b hb c hc
  smul x hx i r hr b hb := by
    first
    | simpa only [Fin.cons_update] using
        hf.smul (Fin.cons a x) (fun j => Fin.cases ha hx j) i.succ r hr b hb

include hopen hne in
theorem exists_multilinearExtension {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f) :
    ∃ F : MultilinearMap ℝ (fun _ : Fin n => V) W,
      ∀ x : Fin n → V, (∀ i, x i ∈ C) → F x = f x := by
  first
  | classical
    induction n with
    | zero =>
        refine ⟨MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => V)
          (f (fun i : Fin 0 => Fin.elim0 i)), ?_⟩
        intro x _
        have he : x = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
        rw [he]
        rfl
    | succ n ih =>
        let G : V → MultilinearMap ℝ (fun _ : Fin n => V) W := fun a =>
          if ha : a ∈ C then
            Classical.choose (ih (fun x => f (Fin.cons a x)) (hf.cons C ha))
          else 0
        have hG (a : V) (ha : a ∈ C) (x : Fin n → V) (hx : ∀ i, x i ∈ C) :
            G a x = f (Fin.cons a x) := by
          dsimp only [G]
          rw [dif_pos ha]
          exact Classical.choose_spec (ih (fun x => f (Fin.cons a x)) (hf.cons C ha)) x hx
        have hadd : AdditiveOn C G := by
          intro a ha b hb
          apply multilinearMap_ext_of_eq_on_cone C hopen hne
          intro x hx
          rw [MultilinearMap.add_apply, hG a ha x hx, hG b hb x hx,
            hG (a + b) (C.add_mem ha hb) x hx]
          simpa only [Fin.update_cons_zero] using
            hf.add (Fin.cons a x) (fun j => Fin.cases ha hx j) 0 a ha b hb
        have hsmul : PositiveHomogeneousOn C G := by
          intro r hr a ha
          apply multilinearMap_ext_of_eq_on_cone C hopen hne
          intro x hx
          rw [MultilinearMap.smul_apply, hG a ha x hx,
            hG (r • a) (C.smul_mem hr ha) x hx]
          simpa only [Fin.update_cons_zero] using
            hf.smul (Fin.cons a x) (fun j => Fin.cases ha hx j) 0 r hr a ha
        refine ⟨(linearExtension C hopen hne G hadd hsmul).uncurryLeft, ?_⟩
        intro x hx
        rw [LinearMap.uncurryLeft_apply, linearExtension_eq C hopen hne G hadd hsmul (hx 0),
          hG (x 0) (hx 0) (Fin.tail x) (fun j => hx j.succ), Fin.cons_self_tail]

def multilinearExtension {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f) : MultilinearMap ℝ (fun _ : Fin n => V) W :=
  Classical.choose (exists_multilinearExtension C hopen hne f hf)

theorem multilinearExtension_eq {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f) (x : Fin n → V) (hx : ∀ i, x i ∈ C) :
    multilinearExtension C hopen hne f hf x = f x :=
  Classical.choose_spec (exists_multilinearExtension C hopen hne f hf) x hx

theorem multilinearExtension_unique {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f)
    (F : MultilinearMap ℝ (fun _ : Fin n => V) W)
    (hF : ∀ x : Fin n → V, (∀ i, x i ∈ C) → F x = f x) :
    F = multilinearExtension C hopen hne f hf :=
  multilinearMap_ext_of_eq_on_cone C hopen hne (fun x hx =>
    (hF x hx).trans (multilinearExtension_eq C hopen hne f hf x hx).symm)

include hopen in
theorem positive_of_nonnegative_on_cone {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => V) ℝ)
    (hF : ∀ x : Fin n → V, (∀ i, x i ∈ C) → 0 ≤ F x)
    {p : V} (hp : p ∈ C) (hdiag : 0 < F (fun _ => p))
    (H : Fin n → V) (hH : ∀ i, H i ∈ C) : 0 < F H := by
  first
  | obtain ⟨ε, hε, hG⟩ := OpenConeExtension.exists_pos_sub_all C hopen H hH p
    let G : Fin n → V := fun i => H i - ε • p
    have hscale : ε • p ∈ C := C.smul_mem hε hp
    have hdecomp : H = (fun _ : Fin n => ε • p) + G := by
      funext i
      change H i = ε • p + (H i - ε • p)
      abel
    have hterm (s : Finset (Fin n)) : 0 ≤ F (s.piecewise (fun _ => ε • p) G) := by
      apply hF
      intro i
      by_cases hi : i ∈ s
      · simpa only [Finset.piecewise, hi, if_true] using hscale
      · simpa only [Finset.piecewise, hi, if_false, G] using hG i
    have hle : F (fun _ : Fin n => ε • p) ≤ F H := by
      rw [hdecomp, F.map_add_univ]
      have he := Finset.single_le_sum (s := Finset.univ)
        (f := fun s : Finset (Fin n) => F (s.piecewise (fun _ => ε • p) G))
        (fun s _ => hterm s) (Finset.mem_univ (Finset.univ : Finset (Fin n)))
      simpa only [Finset.piecewise_univ] using he
    have hhom : F (fun _ : Fin n => ε • p) = ε ^ n * F (fun _ => p) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
        F.map_smul_univ (fun _ : Fin n => ε) (fun _ => p)
    rw [hhom] at hle
    exact (mul_pos (pow_pos hε n) hdiag).trans_le hle

end VolumePolynomials.OpenConeModuleExtension
end -- closes the original EOF section from source line 15
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/OpenConeMultilinear.lean -/

/- BEGIN SOURCE: VolumePolynomials/SupportMultilinearVolume.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The actual volume polynomial on unrestricted support directions

The full finite multilinear extension is constructed from actual mixed
volumes of the cone bodies. Its diagonal agrees with their genuine Haar
volume in the ambient dimension. Permutation symmetry is inherited from the
proved coefficient definition, and its first two arguments agree with the
previously constructed symmetric support form.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem bodyAtHeight_tuple_update
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (i : Fin n) (a : ι → ℝ) :
    (fun j => bodyAtHeight l h₀ hp hc (Function.update H i a j)) =
      Function.update (fun j => bodyAtHeight l h₀ hp hc (H j)) i
        (bodyAtHeight l h₀ hp hc a) := by
  first
  | funext j
    by_cases hji : j = i <;> simp [hji]

def heightVolumeValue
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) : ℝ :=
  mixedVolume μ (fun j => bodyAtHeight l h₀ hp hc (H j))

theorem heightVolumeValue_isMultilinearOnCone
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) (n : ℕ) :
    OpenConeModuleExtension.IsMultilinearOnCone (typeCone l h₀ hp hc)
      (heightVolumeValue μ l h₀ hp hc (n := n)) where
  add H hH i a ha b hb := by
    first
    | simp only [heightVolumeValue, bodyAtHeight_tuple_update]
      rw [bodyAtHeight_add l h₀ hp hc ha hb, mixedVolume_add]
  smul H hH i r hr a ha := by
    first
    | simp only [heightVolumeValue, bodyAtHeight_tuple_update]
      rw [bodyAtHeight_smul l h₀ hp hc ha hr, mixedVolume_smul μ _ _ _ hr.le]
      rfl

def supportMultilinearVolume
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (n : ℕ) : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ :=
  OpenConeModuleExtension.multilinearExtension (typeCone l h₀ hp hc)
    (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
    (heightVolumeValue μ l h₀ hp hc)
    (heightVolumeValue_isMultilinearOnCone μ l h₀ hp hc n)

theorem supportMultilinearVolume_eq
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    supportMultilinearVolume μ l h₀ hg hp hc n H =
      mixedVolume μ (fun j => bodyAtHeight l h₀ hp hc (H j)) :=
  OpenConeModuleExtension.multilinearExtension_eq _ _ _ _ _ H hH

theorem supportMultilinearVolume_diagonal
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) :
    supportMultilinearVolume μ l h₀ hg hp hc n (fun _ => h) = μ.real (body l h) := by
  first
  | rw [supportMultilinearVolume_eq μ l h₀ hg hp hc _ (fun _ => hh),
      mixedVolume_diagonal μ hdim, coe_bodyAtHeight l h₀ hp hc hh]

theorem supportMultilinearVolume_reindex
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (e : Equiv.Perm (Fin n)) :
    supportMultilinearVolume μ l h₀ hg hp hc n (fun j => H (e j)) =
      supportMultilinearVolume μ l h₀ hg hp hc n H := by
  first
  | let F := supportMultilinearVolume μ l h₀ hg hp hc n
    have he : F.domDomCongr e = F := by
      apply OpenConeModuleExtension.multilinearMap_ext_of_eq_on_cone
        (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
        (typeCone_nonempty l h₀ hg hp hc)
      intro x hx
      change supportMultilinearVolume μ l h₀ hg hp hc n (fun j => x (e j)) = _
      rw [supportMultilinearVolume_eq μ l h₀ hg hp hc _ (fun j => hx (e j)),
        supportMultilinearVolume_eq μ l h₀ hg hp hc _ hx]
      exact mixedVolume_reindex μ (fun j => bodyAtHeight l h₀ hp hc (x j)) e
    exact congrArg (fun G : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ => G H) he

/-- Fixing all but the first two arguments of a genuine multilinear map gives
its ordinary bilinear form. -/
def firstTwoForm {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 2) => V) ℝ) (H : Fin n → V) :
    LinearMap.BilinForm ℝ V where
  toFun x := {
    toFun := fun y => F (Fin.cons x (Fin.cons y H))
    map_add' := fun y z => (F.curryLeft x).cons_add H y z
    map_smul' := fun r y => (F.curryLeft x).cons_smul H r y
  }
  map_add' x y := by
    first
    | ext z
      exact F.cons_add (Fin.cons z H) x y
  map_smul' r x := by
    first
    | ext y
      exact F.cons_smul (Fin.cons y H) r x

theorem firstTwoForm_apply {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 2) => V) ℝ) (H : Fin n → V)
    (x y : V) : firstTwoForm (n := n) F H x y =
      F (Fin.cons x (Fin.cons y H) : Fin (n + 2) → V) := rfl

theorem bilinear_ext_of_eq_on_cone
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : ConvexCone ℝ V) (ho : IsOpen (C : Set V)) (hn : (C : Set V).Nonempty)
    {F G : LinearMap.BilinForm ℝ V}
    (hFG : ∀ x ∈ C, ∀ y ∈ C, F x y = G x y) : F = G := by
  first
  | apply LinearMap.ext
    intro x
    apply OpenConeExtension.linearMap_ext_of_eq_on_cone C ho hn
    intro y hy
    have he : F.flip y = G.flip y :=
      OpenConeExtension.linearMap_ext_of_eq_on_cone C ho hn (fun z hz => hFG z hz y hy)
    exact congrArg (fun f : V →ₗ[ℝ] ℝ => f x) he

set_option maxHeartbeats 1000000 in
theorem supportMultilinearVolume_firstTwoForm
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    firstTwoForm (n := n) (V := ι → ℝ)
      (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H =
      mixedSupportForm μ l h₀ hg hp hc (d := n)
        (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) := by
  first
  | refine bilinear_ext_of_eq_on_cone (typeCone l h₀ hp hc)
      (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
      (F := firstTwoForm (n := n) (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H)
      (G := mixedSupportForm μ l h₀ hg hp hc
        (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j))) ?_
    intro x hx y hy
    let T : Fin (n + 2) → ι → ℝ := Fin.cons x (Fin.cons y H)
    have hT : ∀ j : Fin (n + 2), T j ∈ typeCone l h₀ hp hc :=
      fun j => Fin.cases hx (fun k => Fin.cases hy hH k) j
    calc
      firstTwoForm (n := n) (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H x y =
          supportMultilinearVolume μ l h₀ hg hp hc (n + 2) T :=
        firstTwoForm_apply (n := n) (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H x y
      _ = mixedVolume μ (fun j : Fin (n + 2) => bodyAtHeight l h₀ hp hc (T j)) :=
        supportMultilinearVolume_eq μ l h₀ hg hp hc T hT
      _ = mixedSupportValue μ l h₀ hp hc
          (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) x y := by
        change mixedVolume μ (fun j : Fin (n + 2) => bodyAtHeight l h₀ hp hc (T j)) =
          mixedVolume μ (Fin.cons (bodyAtHeight l h₀ hp hc x)
            (Fin.cons (bodyAtHeight l h₀ hp hc y)
              (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j))) :
            Fin (n + 2) → ConvexBody E)
        apply congrArg (fun L : Fin (n + 2) → ConvexBody E => mixedVolume μ L)
        funext j
        exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j
      _ = mixedSupportForm μ l h₀ hg hp hc
          (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) x y :=
        (mixedSupportForm_eq_value μ l h₀ hg hp hc
          (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) (x := x) (y := y) hx hy).symm

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/SupportMultilinearVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/MultilinearDiagonalDerivatives.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The first two derivatives of a finite symmetric multilinear diagonal

Continuity is proved by an explicit finite coordinate expansion. The
derivative formula then follows from Mathlib's genuine derivative of a
continuous multilinear map. Symmetry identifies every summand, giving the
exact factors `n` and `n (n-1)` without an informal coefficient comparison.
-/

noncomputable section
open Set
open scoped BigOperators

namespace VolumePolynomials.MultilinearDiagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cons_const {V : Type*} (p : V) (n : ℕ) :
    Fin.cons p (fun _ : Fin n => p) = (fun _ : Fin (n + 1) => p) :=
  Fin.cons_self_tail (fun _ : Fin (n + 1) => p)

theorem coordinate_expansion {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ)
    (x : Fin n → ι → ℝ) :
    F x = ∑ r : Fin n → ι, (∏ i, x i (r i)) * F (fun i => Pi.single (r i) 1) := by
  first
  | calc
      F x = F (fun i => ∑ j, x i j • Pi.single j 1) := by
        congr 1
        funext i
        exact pi_eq_sum_univ' (x i)
      _ = ∑ r : Fin n → ι, F (fun i => x i (r i) • Pi.single (r i) 1) :=
        F.map_sum (fun i j => x i j • Pi.single j 1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        exact F.map_smul_univ (fun i => x i (r i)) (fun i => Pi.single (r i) 1)

theorem continuous {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ) : Continuous F := by
  first
  | have he : (F : (Fin n → ι → ℝ) → ℝ) =
        fun x => ∑ r : Fin n → ι, (∏ i, x i (r i)) * F (fun i => Pi.single (r i) 1) :=
      funext (coordinate_expansion F)
    rw [he]
    apply continuous_finsetSum
    intro r _
    apply Continuous.mul _ continuous_const
    exact continuous_finsetProd _ (fun i _ => (continuous_apply (r i)).comp (continuous_apply i))

def toContinuous {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ :=
  ⟨F, continuous F⟩

def PermutationSymmetric {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) : Prop :=
  ∀ x : Fin n → V, ∀ e : Equiv.Perm (Fin n), F (fun j => x (e j)) = F x

def liftPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cons 0 (fun i => (e i).succ)
  invFun := Fin.cons 0 (fun i => (e.symm i).succ)
  left_inv i := by
    first
    | exact Fin.cases rfl (fun j => by simp only [Fin.cons_succ, Equiv.symm_apply_apply]) i
  right_inv i := by
    first
    | exact Fin.cases rfl (fun j => by simp only [Fin.cons_succ, Equiv.apply_symm_apply]) i

theorem PermutationSymmetric.curryLeft
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ}
    (hF : PermutationSymmetric F) (a : V) : PermutationSymmetric (F.curryLeft a) := by
  first
  | intro x e
    have he : (fun j : Fin (n + 1) =>
        (Fin.cons a x : Fin (n + 1) → V) (liftPermutation e j)) =
        (Fin.cons a (fun j : Fin n => x (e j)) : Fin (n + 1) → V) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have h := hF (Fin.cons a x) (liftPermutation e)
    rw [he] at h
    exact h

theorem PermutationSymmetric.update_const
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ}
    (hF : PermutationSymmetric F) (p x : V) (i : Fin (n + 1)) :
    F (Function.update (fun _ => p) i x) = F (Fin.cons x (fun _ => p)) := by
  first
  | have he := hF (Function.update (fun _ => p) i x) (Equiv.swap 0 i)
    change F ((Function.update (fun _ => p) i x) ∘ Equiv.swap 0 i) = _ at he
    rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right] at he
    have ht : Function.update ((fun _ : Fin (n + 1) => p) ∘ Equiv.swap 0 i) 0 x =
        Fin.cons x (fun _ : Fin n => p) := by
      funext j
      exact Fin.cases (by simp) (fun k => by simp [Function.comp_def]) j
    rw [ht] at he
    exact he.symm

theorem PermutationSymmetric.swap_first_two
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 2) => V) ℝ}
    (hF : PermutationSymmetric F) (x y : V) (H : Fin n → V) :
    F (Fin.cons x (Fin.cons y H)) = F (Fin.cons y (Fin.cons x H)) := by
  first
  | have he := hF (Fin.cons x (Fin.cons y H)) (Equiv.swap 0 1)
    change F ((Matrix.vecCons x (Matrix.vecCons y H)) ∘ Equiv.swap 0 1) = _ at he
    rw [Matrix.cons_cons_comp_swap_zero_one] at he
    exact he.symm

theorem PermutationSymmetric.rotate_first_three
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 3) => V) ℝ}
    (hF : PermutationSymmetric F) (x y h : V) (H : Fin n → V) :
    F (Fin.cons x (Fin.cons y (Fin.cons h H))) =
      F (Fin.cons h (Fin.cons x (Fin.cons y H))) := by
  first
  | calc
      _ = F (Fin.cons x (Fin.cons h (Fin.cons y H))) :=
        (hF.curryLeft x).swap_first_two y h H
      _ = _ := hF.swap_first_two x h (Fin.cons y H)

theorem hasDerivAt_diagonal {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => ι → ℝ) ℝ)
    (hF : PermutationSymmetric F) (p x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (fun _ => p + s • x))
      (((n + 1 : ℕ) : ℝ) * F (Fin.cons x (fun _ => p + t • x))) t := by
  first
  | have hcurve : HasDerivAt (fun s : ℝ => (fun _ : Fin (n + 1) => p + s • x))
        (fun _ => x) t := by
      apply hasDerivAt_pi.mpr
      intro i
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const x).const_add p
    have hd := (toContinuous F).hasFDerivAt (fun _ => p + t • x)
    have he := hd.comp_hasDerivAt t hcurve
    simp only [Function.comp_def, ContinuousMultilinearMap.linearDeriv_apply] at he
    change HasDerivAt (fun s : ℝ => F (fun _ : Fin (n + 1) => p + s • x))
      (∑ i : Fin (n + 1), F (Function.update (fun _ => p + t • x) i x)) t at he
    simpa only [hF.update_const, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using he

theorem hasDerivAt_first_diagonal_derivative {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 2) => ι → ℝ) ℝ)
    (hF : PermutationSymmetric F) (p x : ι → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((n + 2 : ℕ) : ℝ) * F (Fin.cons x (fun _ => p + s • x)))
      (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) *
        F (Fin.cons x (Fin.cons x (fun _ => p + t • x)))) t := by
  first
  | have hd := HasDerivAt.const_mul (((n + 2 : ℕ) : ℝ))
      (hasDerivAt_diagonal (F.curryLeft x) (hF.curryLeft x) p x t)
    convert hd using 1 <;> simp only [MultilinearMap.curryLeft_apply]
    push_cast
    ring

end VolumePolynomials.MultilinearDiagonal
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MultilinearDiagonalDerivatives.lean -/

/- BEGIN SOURCE: VolumePolynomials/HaarBrunnMinkowski.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Brunn--Minkowski for the specified Haar measure in any finite normed space

An actual continuous linear coordinate equivalence transports the theorem to
Euclidean space. The positive Haar normalization factor is carried through
the dimension root explicitly.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem haar_brunn_minkowski (hdim : finrank ℝ E ≠ 0)
    (A B : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * μ.real (A : Set E) ^ ((finrank ℝ E : ℝ)⁻¹) +
      b * μ.real (B : Set E) ^ ((finrank ℝ E : ℝ)⁻¹) ≤
      μ.real (a • A + b • B : ConvexBody E) ^ ((finrank ℝ E : ℝ)⁻¹) := by
  first
  | letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := inferInstanceAs (Measure.IsAddHaarMeasure μ)
    let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    let C := mapBody T.toContinuousLinearMap A
    let D := mapBody T.toContinuousLinearMap B
    let c : ℝ := LinearFrame.volumeFactor T
    have hc : 0 ≤ c := NNReal.coe_nonneg _
    have hscale (K : ConvexBody E) :
        μ.real (K : Set E) = c * volume.real (mapBody T.toContinuousLinearMap K :
          Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) := by
      first
      | rw [coe_mapBody, ContinuousLinearEquiv.coe_coe]
        exact LinearFrame.realVolume_eq_factor_mul_image T (K : Set E)
    have hfin : volume (a • (C : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) + b • (D : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) ≠ ⊤ := by
      simpa only [ConvexBody.coe_add, ConvexBody.coe_smul] using
        (a • C + b • D).isCompact.measure_ne_top
    have h := TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le
      (E := EuclideanSpace ℝ (Fin (finrank ℝ E))) (by simpa using hdim)
      C.nonempty C.isCompact.measurableSet.nullMeasurableSet
      D.nonempty D.isCompact.measurableSet.nullMeasurableSet ha hb hfin
    have h' : a * volume.real (C : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ^ ((finrank ℝ E : ℝ)⁻¹) +
        b * volume.real (D : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ^ ((finrank ℝ E : ℝ)⁻¹) ≤
        volume.real ((a • C + b • D : ConvexBody _) :
          Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ^ ((finrank ℝ E : ℝ)⁻¹) := by
      simpa only [finrank_euclideanSpace_fin, ConvexBody.coe_add, ConvexBody.coe_smul] using h
    rw [hscale A, hscale B, hscale (a • A + b • B), mapBody_add,
      mapBody_smul, mapBody_smul]
    simp only [Real.mul_rpow hc measureReal_nonneg]
    have hmul := mul_le_mul_of_nonneg_left h' (Real.rpow_nonneg hc ((finrank ℝ E : ℝ)⁻¹))
    convert hmul using 1 <;> simp only [C, D] <;> ring

end VolumePolynomials
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/HaarBrunnMinkowski.lean -/

/- BEGIN SOURCE: VolumePolynomials/RootConcavitySecondDerivative.lean -/
section


@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The differential consequence of root concavity

This is the scalar calculus step needed to obtain the diagonal mixed-volume
form's reference inequality directly from Brunn--Minkowski. All derivatives
in the hypotheses are actual derivatives of the indicated real functions.
-/

open Set

namespace VolumePolynomials

/-- The logarithmic second-derivative bound implied by positive-power
concavity. The domain is an actual open neighborhood, so no one-sided or
boundary derivative is substituted for the derivative at the reference. -/
theorem root_concave_second_derivative
    {f f' : ℝ → ℝ} {ε q B : ℝ} (hε : 0 < ε) (hq : 0 < q)
    (hpos : ∀ x ∈ Ioo (-ε) ε, 0 < f x)
    (hf : ∀ x ∈ Ioo (-ε) ε, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' B 0)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε) (fun x => f x ^ q)) :
    f 0 * B ≤ (1 - q) * (f' 0) ^ 2 := by
  first
  | have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hf0 : 0 < f 0 := hpos 0 h0
    let g' : ℝ → ℝ := fun x => q * f x ^ (q - 1) * f' x
    have hderiv (x : ℝ) (hx : x ∈ Ioo (-ε) ε) :
        deriv (fun y => f y ^ q) x = g' x := by
      first
      | rw [((hf x hx).rpow_const (p := q) (Or.inl (hpos x hx).ne')).deriv]
        dsimp only [g']
        ring
    have hanti : AntitoneOn g' (Ioo (-ε) ε) := by
      first
      | have ha := hc.antitoneOn_deriv
          (fun x hx => ((hf x hx).rpow_const (p := q) (Or.inl (hpos x hx).ne')).differentiableAt)
        intro x hx y hy hxy
        rw [← hderiv x hx, ← hderiv y hy]
        exact ha hx hy hxy
    have hp : HasDerivAt (fun x => f x ^ (q - 1))
        (f' 0 * (q - 1) * f 0 ^ (q - 2)) 0 := by
      first
      | simpa only [show q - 1 - 1 = q - 2 by ring] using
          (hf 0 h0).rpow_const (p := q - 1) (Or.inl hf0.ne')
    have hgp : HasDerivAt g'
        (q * (q - 1) * f 0 ^ (q - 2) * (f' 0) ^ 2 +
          q * f 0 ^ (q - 1) * B) 0 := by
      first
      | convert (hp.const_mul q).mul hf' using 1
        ring
    have hn := hanti.derivWithin_nonpos (x := 0)
    rw [hgp.hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt h0)] at hn
    have hexp : f 0 ^ (q - 1) = f 0 ^ (q - 2) * f 0 := by
      first
      | calc
          f 0 ^ (q - 1) = f 0 ^ ((q - 2) + 1) := by congr 1; ring
          _ = f 0 ^ (q - 2) * f 0 ^ (1 : ℝ) := Real.rpow_add hf0 _ _
          _ = f 0 ^ (q - 2) * f 0 := by rw [Real.rpow_one]
    rw [hexp] at hn
    have hfactor : 0 < q * f 0 ^ (q - 2) := mul_pos hq (Real.rpow_pos_of_pos hf0 _)
    have hform : q * (q - 1) * f 0 ^ (q - 2) * (f' 0) ^ 2 +
          q * (f 0 ^ (q - 2) * f 0) * B =
        (q * f 0 ^ (q - 2)) * ((q - 1) * (f' 0) ^ 2 + f 0 * B) := by ring
    rw [hform] at hn
    have hinner := nonpos_of_mul_nonpos_right hn hfactor
    linarith

/-- The normalization of first and second volume derivatives gives the
reference reverse Cauchy--Schwarz inequality in every dimension at least
two. The geometric application supplies `f` from actual volume. -/
theorem root_concavity_reference_inequality
    {d : ℕ} (hd : 2 ≤ d) {f f' : ℝ → ℝ} {ε a b c : ℝ} (hε : 0 < ε)
    (hpos : ∀ x ∈ Ioo (-ε) ε, 0 < f x)
    (hf : ∀ x ∈ Ioo (-ε) ε, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' ((d : ℝ) * ((d : ℝ) - 1) * b) 0)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε) (fun x => f x ^ ((d : ℝ)⁻¹)))
    (hvalue : f 0 = c) (hfirst : f' 0 = (d : ℝ) * a) : c * b ≤ a ^ 2 := by
  first
  | have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hd1 : 0 < (d : ℝ) - 1 := by
      first
      | have htwo : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
    have h := root_concave_second_derivative hε (inv_pos.mpr hdpos) hpos hf hf' hc
    rw [hvalue, hfirst] at h
    have hleft : c * ((d : ℝ) * ((d : ℝ) - 1) * b) =
        ((d : ℝ) * ((d : ℝ) - 1)) * (c * b) := by ring
    have hright : (1 - (d : ℝ)⁻¹) * ((d : ℝ) * a) ^ 2 =
        ((d : ℝ) * ((d : ℝ) - 1)) * a ^ 2 := by
      first
      | field_simp [ne_of_gt hdpos] <;> ring
    rw [hleft, hright] at h
    exact Iff.mp (mul_le_mul_iff_of_pos_left (mul_pos hdpos hd1)) h

end VolumePolynomials
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 11
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/RootConcavitySecondDerivative.lean -/

/- BEGIN SOURCE: VolumePolynomials/DiagonalSupportHyperbolicity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Diagonal-background hyperbolicity from actual Brunn--Minkowski

The function along each real support direction is the diagonal of the
constructed multilinear volume extension. On an actual open interval it is
the genuine volume of the corresponding convex body. Brunn--Minkowski gives
root concavity, and the genuine first and second derivatives give the
reference reverse Cauchy--Schwarz inequality. No Alexandrov--Fenchel result
is used in this diagonal-background step.
-/

noncomputable section
open Set MeasureTheory Module Filter LinearMap
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem rootVolume_concave_typeCone
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hdim : finrank ℝ E ≠ 0) :
    ConcaveOn ℝ (typeCone l h₀ hp hc : Set (ι → ℝ))
      (fun h => μ.real (body l h) ^ ((finrank ℝ E : ℝ)⁻¹)) := by
  first
  | apply concaveOn_iff_forall_pos.mpr
    refine ⟨(typeCone l h₀ hp hc).convex, ?_⟩
    intro h hh k hk a b ha hb hab
    have hah : a • h ∈ typeCone l h₀ hp hc := (typeCone l h₀ hp hc).smul_mem ha hh
    have hbk : b • k ∈ typeCone l h₀ hp hc := (typeCone l h₀ hp hc).smul_mem hb hk
    have hsum : a • h + b • k ∈ typeCone l h₀ hp hc :=
      (typeCone l h₀ hp hc).add_mem hah hbk
    have h := haar_brunn_minkowski μ hdim
      (bodyAtHeight l h₀ hp hc h) (bodyAtHeight l h₀ hp hc k) ha.le hb.le
    rw [← bodyAtHeight_smul l h₀ hp hc hh ha,
      ← bodyAtHeight_smul l h₀ hp hc hk hb,
      ← bodyAtHeight_add l h₀ hp hc hah hbk] at h
    simpa only [coe_bodyAtHeight l h₀ hp hc hh,
      coe_bodyAtHeight l h₀ hp hc hk, coe_bodyAtHeight l h₀ hp hc hsum,
      smul_eq_mul] using h

theorem realVolume_body_pos
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) : 0 < μ.real (body l h) := by
  first
  | have hpos := Measure.measure_pos_of_nonempty_interior μ
      ⟨0, zero_mem_interior_body l h hh.1⟩
    have hfin := (isCompact_body_of_positive_reference l h₀ hp hc h).measure_ne_top (μ := μ)
    exact ENNReal.toReal_pos hpos.ne' hfin

/-- The diagonal mixed-support form obeys the reference inequality on every
real direction, including directions which are not support functions. -/
theorem diagonal_mixedSupportForm_reference_inequality
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n + 2) (x : ι → ℝ) :
    let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    B x x * B h₀ h₀ ≤ B x h₀ ^ 2 := by
  first
  | let C := typeCone l h₀ hp hc
    let F := supportMultilinearVolume μ l h₀ hg hp hc (n + 2)
    let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have href : h₀ ∈ C := mem_typeRegion_self l h₀ hg hp
    have hsym : MultilinearDiagonal.PermutationSymmetric F :=
      fun H e => supportMultilinearVolume_reindex μ l h₀ hg hp hc H e
    have hform : firstTwoForm F (fun _ : Fin n => h₀) = B :=
      supportMultilinearVolume_firstTwoForm μ l h₀ hg hp hc _ (fun _ => href)
    have hpair (a b : ι → ℝ) :
        F (Fin.cons a (Fin.cons b (fun _ : Fin n => h₀))) = B a b :=
      congrArg (fun T : LinearMap.BilinForm ℝ (ι → ℝ) => T a b) hform
    let f : ℝ → ℝ := fun t => F (fun _ => h₀ + t • x)
    let f' : ℝ → ℝ := fun t => ((n + 2 : ℕ) : ℝ) * F (Fin.cons x (fun _ => h₀ + t • x))
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, h₀ + t • x ∈ C := by
      have ht : Tendsto (fun t : ℝ => h₀ + t • x) (𝓝 0) (𝓝 h₀) := by
        have hcurve : Continuous (fun t : ℝ => h₀ + t • x) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa only [zero_smul, add_zero] using
          hcurve.tendsto (0 : ℝ)
      exact ht.eventually ((typeCone_isOpen l h₀ hp hc).mem_nhds href)
    obtain ⟨ε, hε, hs⟩ := Metric.eventually_nhds_iff.mp hnear
    have hmem (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : h₀ + t • x ∈ C := by
      apply hs
      rw [Real.dist_eq, sub_zero]
      exact abs_lt.mpr ht
    have hvol (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : f t = μ.real (body l (h₀ + t • x)) :=
      supportMultilinearVolume_diagonal μ l h₀ hg hp hc hdim (hmem t ht)
    have hpos (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : 0 < f t := by
      rw [hvol t ht]
      exact realVolume_body_pos μ l h₀ hp hc (hmem t ht)
    have hd (t : ℝ) (_ht : t ∈ Ioo (-ε) ε) : HasDerivAt f (f' t) t :=
      MultilinearDiagonal.hasDerivAt_diagonal F hsym h₀ x t
    have hd' : HasDerivAt f'
        (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) * B x x) 0 := by
      simpa only [zero_smul, add_zero, hpair] using
        MultilinearDiagonal.hasDerivAt_first_diagonal_derivative F hsym h₀ x 0
    have hcroot : ConcaveOn ℝ (Ioo (-ε) ε)
        (fun t => f t ^ (((n + 2 : ℕ) : ℝ)⁻¹)) := by
      have hroot := rootVolume_concave_typeCone μ l h₀ hp hc (by rw [hdim]; omega)
      refine ⟨convex_Ioo _ _, ?_⟩
      intro s hs t ht a b ha hb hab
      have hst : a * s + b * t ∈ Ioo (-ε) ε :=
        (convex_Ioo (-ε) ε) hs ht ha hb hab
      have he : a • (h₀ + s • x) + b • (h₀ + t • x) = h₀ + (a * s + b * t) • x := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc
          a * (h₀ i + s * x i) + b * (h₀ i + t * x i) =
              (a + b) * h₀ i + (a * s + b * t) * x i := by ring
          _ = _ := by rw [hab, one_mul]
      have hineq := hroot.2 (hmem s hs) (hmem t ht) ha hb hab
      rw [he, hdim] at hineq
      simpa only [smul_eq_mul, hvol s hs, hvol t ht, hvol _ hst] using hineq
    have hvalue : f 0 = B h₀ h₀ := by
      dsimp only [f]
      simp only [zero_smul, add_zero]
      simpa only [MultilinearDiagonal.cons_const] using hpair h₀ h₀
    have hfirst : f' 0 = ((n + 2 : ℕ) : ℝ) * B x h₀ := by
      dsimp only [f']
      simp only [zero_smul, add_zero]
      congr 1
      simpa only [MultilinearDiagonal.cons_const] using hpair x h₀
    have h := root_concavity_reference_inequality (d := n + 2) (by omega)
      hε hpos hd hd' hcroot hvalue hfirst
    simpa only [mul_comm] using h

theorem diagonal_mixedSupportForm_positive_reference
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n + 2) :
    0 < mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) h₀ h₀ := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    rw [mixedSupportForm_eq_value μ l h₀ hg hp hc _ href href]
    unfold mixedSupportValue
    rw [MultilinearDiagonal.cons_const, MultilinearDiagonal.cons_const,
      mixedVolume_diagonal μ hdim, coe_bodyAtHeight l h₀ hp hc href]
    exact realVolume_body_pos μ l h₀ hp hc href

theorem diagonal_mixedSupportForm_reverse_cauchy_schwarz
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n + 2) (x y : ι → ℝ)
    (hy : 0 ≤ mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) y y) :
    let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    B x x * B y y ≤ B x y ^ 2 := by
  first
  | let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have hs := mixedSupportForm_symmetric μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have hpB : 0 < B h₀ h₀ := diagonal_mixedSupportForm_positive_reference μ l h₀ hg hp hc hdim
    have hperp : ∀ z, B z h₀ = 0 → B z z ≤ 0 :=
      (bilinear_hyperplane_iff_reference_inequality B hs h₀ hpB).mpr
        (diagonal_mixedSupportForm_reference_inequality μ l h₀ hg hp hc hdim)
    exact bilinear_reverse_cauchy_schwarz B hs h₀ hperp x y hy

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 21
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/DiagonalSupportHyperbolicity.lean -/

/- BEGIN SOURCE: VolumePolynomials/MatrixMaximumPrinciple.lean -/
section

@[expose] public section
noncomputable section

/-!
# The maximum principle for the finite Alexandrov operator

For a matrix with nonnegative off-diagonal entries and row sum one, every real
eigenvalue is at most one. Connectivity of its positive off-diagonal entries
makes the one-eigenspace consist precisely of constant vectors. This is the
part of Perron–Frobenius used by the finite Bochner argument; it is proved here
directly, including matrices with negative diagonal entries.
-/

namespace VolumePolynomials
open Finset Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_row_difference (A : Matrix ι ι ℝ) (hrow : ∀ i, ∑ j, A i j = 1)
    (x : ι → ℝ) (i : ι) :
    (A *ᵥ x) i - x i = ∑ j, A i j * (x j - x i) := by
  first
  | simp only [Matrix.mulVec, dotProduct, mul_sub, sum_sub_distrib,
      ← sum_mul, hrow, one_mul]

/-- No irreducibility hypothesis is required for the upper spectral bound. -/
theorem matrix_eigenvalue_le_one (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (r : ℝ) (x : ι → ℝ) (hx : x ≠ 0) (heig : A *ᵥ x = r • x) : r ≤ 1 := by
  first
  | classical
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      apply hx
      funext i
      exact not_not.mp (fun hi => h ⟨i, hi⟩)
    letI : Nonempty ι := ⟨j⟩
    obtain ⟨k, hk⟩ := Finite.exists_max (fun i => |x i|)
    have hkpos : 0 < |x k| := (abs_pos.mpr hj).trans_le (hk j)
    have hkne : x k ≠ 0 := abs_pos.mp hkpos
    have hnonpos : ∑ i, A k i * ((x i - x k) * x k) ≤ 0 := by
      apply sum_nonpos
      intro i _
      by_cases hik : k = i
      · subst i
        simp
      · have hprod : x i * x k ≤ (x k) ^ 2 := by
          calc
            x i * x k ≤ |x i * x k| := le_abs_self _
            _ = |x i| * |x k| := abs_mul _ _
            _ ≤ |x k| * |x k| := mul_le_mul_of_nonneg_right (hk i) (abs_nonneg _)
            _ = (x k) ^ 2 := by rw [← pow_two, sq_abs]
        apply mul_nonpos_of_nonneg_of_nonpos (hoff k i hik)
        nlinarith
    have heq : ∑ i, A k i * ((x i - x k) * x k) = (r - 1) * (x k) ^ 2 := by
      calc
        _ = (∑ i, A k i * (x i - x k)) * x k := by
          rw [sum_mul]
          exact sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)
        _ = ((A *ᵥ x) k - x k) * x k := by rw [matrix_row_difference A hrow]
        _ = (r - 1) * (x k) ^ 2 := by
          rw [heig]
          change (r * x k - x k) * x k = _
          ring
    rw [heq] at hnonpos
    by_contra h
    exact (not_lt_of_ge hnonpos)
      (mul_pos (sub_pos.mpr (lt_of_not_ge h)) (sq_pos_of_ne_zero hkne))

def MatrixPositiveEdge (A : Matrix ι ι ℝ) (i j : ι) : Prop := i ≠ j ∧ 0 < A i j

/-- At a maximal coordinate of a fixed vector, every positive edge leads to
another maximal coordinate. -/
theorem matrix_fixed_maximum_propagates (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (x : ι → ℝ) (hfix : A *ᵥ x = x) {i j : ι}
    (hmax : ∀ k, x k ≤ x i) (hij : MatrixPositiveEdge A i j) : x j = x i := by
  first
  | have hzero : ∑ k, A i k * (x k - x i) = 0 := by
      rw [← matrix_row_difference A hrow, hfix, sub_self]
    have hnonpos : ∀ k ∈ (univ : Finset ι), A i k * (x k - x i) ≤ 0 := by
      intro k _
      by_cases hik : i = k
      · subst k
        simp
      · exact mul_nonpos_of_nonneg_of_nonpos (hoff i k hik) (sub_nonpos.mpr (hmax k))
    have hjzero := (sum_eq_zero_iff_of_nonpos hnonpos).mp hzero j (mem_univ j)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hjzero).resolve_left hij.2.ne')

/-- Connectivity supplies the simplicity of the maximal eigenvalue. The
reachability predicate is an ordinary finite path in the positive-entry graph. -/
theorem matrix_fixed_eq_constant [Nonempty ι] (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j)
    (x : ι → ℝ) (hfix : A *ᵥ x = x) : ∃ c : ℝ, x = fun _ => c := by
  first
  | obtain ⟨k, hk⟩ := Finite.exists_max x
    refine ⟨x k, funext fun j => ?_⟩
    have hpath := hconn k j
    induction hpath with
    | refl => rfl
    | @tail a b hab hab' ih =>
        exact (matrix_fixed_maximum_propagates A hoff hrow x hfix
          (fun i => (hk i).trans_eq ih.symm) hab').trans ih

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MatrixMaximumPrinciple.lean -/

/- BEGIN SOURCE: VolumePolynomials/MatrixGraphFromHyperbolicity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-!
# Connectivity from one positive direction

A symmetric matrix with nonnegative off-diagonal entries, a positive vector
whose image is positive, and the reverse Cauchy--Schwarz inequality has a
connected positive-entry graph. A disconnected component would give two
orthogonal vectors with strictly positive quadratic values. This permits the
diagonal Brunn--Minkowski case to supply connectivity without a separate
polytope face-graph theorem.
-/

noncomputable section
open Finset Matrix
open scoped BigOperators

namespace VolumePolynomials

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_positive_graph_connected_of_reverse_cauchy_schwarz
    (B : Matrix ι ι ℝ) (hsym : ∀ i j, B i j = B j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ B i j)
    (h : ι → ℝ) (hpos : ∀ i, 0 < h i) (himage : ∀ i, 0 < (B *ᵥ h) i)
    (hrev : ∀ x y : ι → ℝ, 0 ≤ dotProduct y (B *ᵥ y) →
      dotProduct x (B *ᵥ x) * dotProduct y (B *ᵥ y) ≤ dotProduct x (B *ᵥ y) ^ 2) :
    ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge B) i j := by
  first
  | classical
    intro a b
    by_contra hab
    let S : Set ι := {i | Relation.ReflTransGen (MatrixPositiveEdge B) a i}
    have ha : a ∈ S := Relation.ReflTransGen.refl
    have hb : b ∉ S := hab
    have hcross : ∀ i ∈ S, ∀ j ∉ S, B i j = 0 := by
      intro i hi j hj
      have hij : i ≠ j := by rintro rfl; exact hj hi
      apply le_antisymm _ (hoff i j hij)
      by_contra hnot
      have hposij : 0 < B i j := lt_of_not_ge hnot
      exact hj (Relation.ReflTransGen.tail hi ⟨hij, hposij⟩)
    have hcross' : ∀ i ∉ S, ∀ j ∈ S, B i j = 0 := by
      intro i hi j hj
      rw [hsym i j]
      exact hcross j hj i hi
    let x : ι → ℝ := fun i => if i ∈ S then h i else 0
    let y : ι → ℝ := fun i => if i ∈ S then 0 else h i
    have hx : ∀ i, (B *ᵥ x) i = if i ∈ S then (B *ᵥ h) i else 0 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi, if_pos, if_true]
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ S
        · simp only [x, hj, if_pos, if_true]
        · simp only [x, hj, if_neg, if_false, mul_zero, hcross i hi j hj, zero_mul]
      · simp only [hi, if_neg, if_false]
        apply sum_eq_zero
        intro j _
        by_cases hj : j ∈ S
        · simp only [x, hj, if_pos, if_true, hcross' i hi j hj, zero_mul]
        · simp only [x, hj, if_neg, if_false, mul_zero]
    have hy : ∀ i, (B *ᵥ y) i = if i ∈ S then 0 else (B *ᵥ h) i := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi, if_pos, if_true]
        apply sum_eq_zero
        intro j _
        by_cases hj : j ∈ S
        · simp only [y, hj, if_pos, if_true, mul_zero]
        · simp only [y, hj, if_neg, if_false, hcross i hi j hj, zero_mul]
      · simp only [hi, if_neg, if_false]
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ S
        · simp only [y, hj, if_pos, if_true, mul_zero, hcross' i hi j hj, zero_mul]
        · simp only [y, hj, if_neg, if_false]
    have hxx : 0 < dotProduct x (B *ᵥ x) := by
      have hn : ∀ i ∈ (univ : Finset ι), 0 ≤ x i * (B *ᵥ x) i := by
        intro i _
        rw [hx]
        by_cases hi : i ∈ S
        · simpa only [x, hi, if_pos, if_true] using (mul_pos (hpos i) (himage i)).le
        · simp only [x, hi, if_neg, if_false, mul_zero, le_refl]
      exact (sum_pos_iff_of_nonneg hn).mpr ⟨a, mem_univ a, by
        simpa only [x, ha, if_pos, if_true, hx] using mul_pos (hpos a) (himage a)⟩
    have hyy : 0 < dotProduct y (B *ᵥ y) := by
      have hn : ∀ i ∈ (univ : Finset ι), 0 ≤ y i * (B *ᵥ y) i := by
        intro i _
        rw [hy]
        by_cases hi : i ∈ S
        · simp only [y, hi, if_pos, if_true, mul_zero, le_refl]
        · simpa only [y, hi, if_neg, if_false] using (mul_pos (hpos i) (himage i)).le
      exact (sum_pos_iff_of_nonneg hn).mpr ⟨b, mem_univ b, by
        simpa only [y, hb, if_neg, if_false, hy] using mul_pos (hpos b) (himage b)⟩
    have hxy : dotProduct x (B *ᵥ y) = 0 := by
      apply sum_eq_zero
      intro i _
      rw [hy]
      by_cases hi : i ∈ S <;> simp only [x, hi, if_pos, if_true, if_neg, if_false, zero_mul, mul_zero]
    have he := hrev x y hyy.le
    rw [hxy, zero_pow (by decide : 2 ≠ 0)] at he
    exact (not_le_of_gt (mul_pos hxx hyy)) he

/-- A positive lower comparison on off-diagonal entries transfers every
positive path. Only this direction of comparison is required. -/
theorem matrix_positive_graph_connected_of_dominates
    (A B : Matrix ι ι ℝ) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ i j, i ≠ j → c * B i j ≤ A i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge B) i j) :
    ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j := by
  first
  | intro i j
    exact Relation.ReflTransGen.mono
      (fun a b hab => ⟨hab.1, (mul_pos hc hab.2).trans_le (hdom a b hab.1)⟩) i j (hconn i j)

end VolumePolynomials
end -- closes the original EOF section from source line 21
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MatrixGraphFromHyperbolicity.lean -/

/- BEGIN SOURCE: VolumePolynomials/MixedSupportConnectivity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Connectivity of the genuine mixed-support operator

Every cone background contains a positive scalar multiple of the reference
in the Minkowski sense. Expanding the actual multilinear extension gives a
positive lower comparison with the diagonal-background matrix. The latter
has positive image on the reference heights, and Brunn--Minkowski supplies
its one-positive-direction inequality. Thus the positive-entry graph is
connected without a separately assumed facet-adjacency theorem.
-/

noncomputable section
open Set MeasureTheory Module Matrix LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m n : ℕ}

theorem facetFrameFactor_pos (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    0 < facetFrameFactor l v hv := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    change 0 < (LinearFrame.volumeFactor (LinearFrame.continuousEquiv l v hv) : ℝ)
    exact_mod_cast LinearFrame.volumeFactor_pos (LinearFrame.continuousEquiv l v hv)

theorem diagonal_mixedSupportMatrix_image_pos
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 2)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) :
    0 < (mixedSupportMatrix volume l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) *ᵥ h₀) i := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = n + 1 := by
      have he := LinearFrame.finrank_kernel_add_one (l i) (v i) (hv i)
      rw [hdim] at he
      omega
    let Q := kernelBody (bodyAtHeight l h₀ hp hc h₀) (l i) (v i) (hv i)
    have hQint : (interior (Q : Set (LinearMap.ker (l i).toLinearMap))).Nonempty :=
      kernelBody_bodyAtHeight_interior_nonempty l h₀ hg hp hc hf href i (v i) (hv i)
    have hQpos : 0 < (kernelMeasure (l i)).real (Q : Set _) := by
      exact ENNReal.toReal_pos
        (Measure.measure_pos_of_nonempty_interior (kernelMeasure (l i)) hQint).ne'
        (Q.isCompact.measure_ne_top (μ := kernelMeasure (l i)))
    have hlow : 0 < facetMixedValue l h₀ hp hc (fun _ : Fin n => h₀) h₀ i (v i) (hv i) := by
      unfold facetMixedValue
      rw [MultilinearDiagonal.cons_const, mixedVolume_diagonal (kernelMeasure (l i)) hkdim]
      exact hQpos
    have he := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray
      (fun _ : Fin n => h₀) (fun _ => href) v hv i href
    have hprod : 0 < facetFrameFactor (l i) (v i) (hv i) *
        facetMixedValue l h₀ hp hc (fun _ : Fin n => h₀) h₀ i (v i) (hv i) :=
      mul_pos (facetFrameFactor_pos (l i) (v i) (hv i)) hlow
    rw [← he, mixedSupportForm_eq_dotProduct, single_one_dotProduct] at hprod
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))).mp hprod

theorem exists_positive_mixedSupportMatrix_domination
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 2)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ i j, i ≠ j →
      c * mixedSupportMatrix volume l h₀ hg hp hc
        (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) i j ≤
      mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) i j := by
  first
  | let C := typeCone l h₀ hp hc
    have href : h₀ ∈ C := mem_typeRegion_self l h₀ hg hp
    obtain ⟨ε, hε, hG⟩ := OpenConeExtension.exists_pos_sub_all C
      (typeCone_isOpen l h₀ hp hc) H hH h₀
    let G : Fin n → Fin m → ℝ := fun k => H k - ε • h₀
    have hscale : ε • h₀ ∈ C := C.smul_mem hε href
    refine ⟨ε ^ n, pow_pos hε n, ?_⟩
    intro i j hij
    let F := ((supportMultilinearVolume volume l h₀ hg hp hc (n + 2)).curryLeft
      (Pi.single i 1)).curryLeft (Pi.single j 1)
    have hF (L : Fin n → Fin m → ℝ) (hL : ∀ k, L k ∈ C) :
        F L = mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc L) i j := by
      exact congrArg (fun B : LinearMap.BilinForm ℝ (Fin m → ℝ) => B (Pi.single i 1) (Pi.single j 1))
        (supportMultilinearVolume_firstTwoForm volume l h₀ hg hp hc L hL)
    have hFnonneg (L : Fin n → Fin m → ℝ) (hL : ∀ k, L k ∈ C) : 0 ≤ F L := by
      rw [hF L hL]
      exact mixedSupportMatrix_offdiag_nonnegative l h₀ hg hp hc hf hn hray
        L hL hdim v hv i j hij
    have hdecomp : H = (fun _ : Fin n => ε • h₀) + G := by
      funext k
      change H k = ε • h₀ + (H k - ε • h₀)
      abel
    have hterm (s : Finset (Fin n)) :
        0 ≤ F (s.piecewise (fun _ => ε • h₀) G) := by
      apply hFnonneg
      intro k
      by_cases hk : k ∈ s
      · simpa only [Finset.piecewise, hk, if_true] using hscale
      · simpa only [Finset.piecewise, hk, if_false, G] using hG k
    have hsingle : F (fun _ : Fin n => ε • h₀) ≤ F H := by
      rw [hdecomp, F.map_add_univ]
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun s : Finset (Fin n) => F (s.piecewise (fun _ => ε • h₀) G))
        (fun s _ => hterm s) (Finset.mem_univ (Finset.univ : Finset (Fin n)))
      simpa only [Finset.piecewise_univ] using h
    have hhom : F (fun _ : Fin n => ε • h₀) = ε ^ n * F (fun _ => h₀) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
        F.map_smul_univ (fun _ : Fin n => ε) (fun _ => h₀)
    rw [hhom, hF H hH, hF (fun _ => h₀) (fun _ => href)] at hsingle
    exact hsingle

/-- Positive-entry connectivity for the actual mixed-support matrix, with
every geometric and Brunn--Minkowski input discharged. -/
theorem mixedSupportMatrix_positive_graph_connected
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 2)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) :
    ∀ i j, Relation.ReflTransGen
      (MatrixPositiveEdge (mixedSupportMatrix volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc H))) i j := by
  first
  | let B := mixedSupportMatrix volume l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    have hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge B) i j := by
      apply matrix_positive_graph_connected_of_reverse_cauchy_schwarz B
        (mixedSupportMatrix_symmetric volume l h₀ hg hp hc _)
        (mixedSupportMatrix_offdiag_nonnegative l h₀ hg hp hc hf hn hray
          (fun _ : Fin n => h₀) (fun _ => href) hdim v hv) h₀ hp
        (diagonal_mixedSupportMatrix_image_pos l h₀ hg hp hc hf hn hray hdim v hv)
      intro x y hy
      have hy' : 0 ≤ mixedSupportForm volume l h₀ hg hp hc
          (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) y y := by
        simpa only [mixedSupportForm_eq_dotProduct] using hy
      have he := diagonal_mixedSupportForm_reverse_cauchy_schwarz
        volume l h₀ hg hp hc hdim x y hy'
      simpa only [mixedSupportForm_eq_dotProduct] using he
    obtain ⟨c, hcpos, hdom⟩ := exists_positive_mixedSupportMatrix_domination
      l h₀ hg hp hc hf hn hray hdim H hH v hv
    exact matrix_positive_graph_connected_of_dominates _ B hcpos hdom hconn

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 20
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MixedSupportConnectivity.lean -/

/- BEGIN SOURCE: VolumePolynomials/FacetMixedForms.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Actual lower-dimensional mixed forms in fixed facet coordinates

Each kernel facet map is Minkowski additive on the genuine upper support
cone. Its actual mixed volumes therefore have finite multilinear extensions
on the same real height space. Their positivity and symmetry are proved
from the genuine kernel bodies; no lower-dimensional inequality is assumed
in these constructions.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m : ℕ}

def facetHeightValue
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) : ℝ :=
  mixedVolume (kernelMeasure (l i))
    (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv)

theorem facetBody_tuple_update
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (j : Fin n) (a : Fin m → ℝ) :
    (fun k => kernelBody (bodyAtHeight l h₀ hp hc (Function.update H j a k)) (l i) v hv) =
      Function.update (fun k => kernelBody (bodyAtHeight l h₀ hp hc (H k)) (l i) v hv) j
        (kernelBody (bodyAtHeight l h₀ hp hc a) (l i) v hv) := by
  first
  | funext k
    by_cases hkj : k = j <;> simp [hkj]

theorem facetHeightValue_isMultilinearOnCone
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) (n : ℕ) :
    OpenConeModuleExtension.IsMultilinearOnCone (typeCone l h₀ hp hc)
      (facetHeightValue l h₀ hp hc i v hv (n := n)) where
  add H hH j a ha b hb := by
    first
    | simp only [facetHeightValue, facetBody_tuple_update]
      rw [bodyAtHeight_add l h₀ hp hc ha hb, kernelBody_add, mixedVolume_add]
  smul H hH j r hr a ha := by
    first
    | simp only [facetHeightValue, facetBody_tuple_update]
      rw [bodyAtHeight_smul l h₀ hp hc ha hr, kernelBody_smul _ _ _ _ hr,
        mixedVolume_smul (kernelMeasure (l i)) _ _ _ hr.le]
      rfl

def facetMultilinearVolume
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) (n : ℕ) :
    MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ :=
  OpenConeModuleExtension.multilinearExtension (typeCone l h₀ hp hc)
    (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
    (facetHeightValue l h₀ hp hc i v hv)
    (facetHeightValue_isMultilinearOnCone l h₀ hp hc i v hv n)

theorem facetMultilinearVolume_eq
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    facetMultilinearVolume l h₀ hg hp hc i v hv n H =
      mixedVolume (kernelMeasure (l i))
        (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv) :=
  OpenConeModuleExtension.multilinearExtension_eq _ _ _ _ _ H hH

theorem facetMultilinearVolume_nonnegative
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    0 ≤ facetMultilinearVolume l h₀ hg hp hc i v hv n H := by
  first
  | rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv H hH]
    exact mixedVolume_nonnegative _ _

theorem facetMultilinearVolume_positive
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀)
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (hdim : finrank ℝ E = n + 1)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    0 < facetMultilinearVolume l h₀ hg hp hc i v hv n H := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = n := by
      first
      | have he := LinearFrame.finrank_kernel_add_one (l i) v hv
        rw [hdim] at he
        omega
    apply OpenConeModuleExtension.positive_of_nonnegative_on_cone
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (facetMultilinearVolume l h₀ hg hp hc i v hv n)
      (facetMultilinearVolume_nonnegative l h₀ hg hp hc i v hv) href _ H hH
    rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv _ (fun _ => href),
      mixedVolume_diagonal (kernelMeasure (l i)) hkdim]
    let Q := kernelBody (bodyAtHeight l h₀ hp hc h₀) (l i) v hv
    have hQint : (interior (Q : Set (LinearMap.ker (l i).toLinearMap))).Nonempty :=
      kernelBody_bodyAtHeight_interior_nonempty l h₀ hg hp hc hf href i v hv
    exact ENNReal.toReal_pos
      (Measure.measure_pos_of_nonempty_interior (kernelMeasure (l i)) hQint).ne'
      (Q.isCompact.measure_ne_top (μ := kernelMeasure (l i)))

theorem facetMultilinearVolume_reindex
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (e : Equiv.Perm (Fin n)) :
    facetMultilinearVolume l h₀ hg hp hc i v hv n (fun j => H (e j)) =
      facetMultilinearVolume l h₀ hg hp hc i v hv n H := by
  first
  | let F := facetMultilinearVolume l h₀ hg hp hc i v hv n
    have he : F.domDomCongr e = F := by
      first
      | apply OpenConeModuleExtension.multilinearMap_ext_of_eq_on_cone
          (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
          (typeCone_nonempty l h₀ hg hp hc)
        intro x hx
        change facetMultilinearVolume l h₀ hg hp hc i v hv n (fun j => x (e j)) = _
        rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv _ (fun j => hx (e j)),
          facetMultilinearVolume_eq l h₀ hg hp hc i v hv _ hx]
        exact mixedVolume_reindex (kernelMeasure (l i))
          (fun j : Fin n => kernelBody (bodyAtHeight l h₀ hp hc (x j)) (l i) v hv) e
    exact congrArg (fun G : MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ => G H) he

def facetMixedForm
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) : LinearMap.BilinForm ℝ (Fin m → ℝ) :=
  firstTwoForm (facetMultilinearVolume l h₀ hg hp hc i v hv (n + 2)) H

theorem facetMixedForm_eq
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {x y : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    facetMixedForm l h₀ hg hp hc i v hv H x y =
      mixedVolume (kernelMeasure (l i))
        (Fin.cons (kernelBody (bodyAtHeight l h₀ hp hc x) (l i) v hv)
          (Fin.cons (kernelBody (bodyAtHeight l h₀ hp hc y) (l i) v hv)
            (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv))) := by
  first
  | change facetMultilinearVolume l h₀ hg hp hc i v hv _ (Fin.cons x (Fin.cons y H)) = _
    rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv _
      (fun j => Fin.cases hx (fun k => Fin.cases hy hH k) j)]
    apply congrArg (mixedVolume (kernelMeasure (l i)))
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j

theorem facetMixedForm_symmetric
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (x y : Fin m → ℝ) :
    facetMixedForm l h₀ hg hp hc i v hv H x y =
      facetMixedForm l h₀ hg hp hc i v hv H y x := by
  first
  | have he := facetMultilinearVolume_reindex l h₀ hg hp hc i v hv
      (Fin.cons x (Fin.cons y H)) (Equiv.swap (0 : Fin (n + 2)) 1)
    change facetMultilinearVolume l h₀ hg hp hc i v hv _
      ((Matrix.vecCons x (Matrix.vecCons y H)) ∘ Equiv.swap 0 1) = _ at he
    rw [Matrix.cons_cons_comp_swap_zero_one] at he
    exact he.symm

theorem facetMixedForm_positive
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀)
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {x y : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    0 < facetMixedForm l h₀ hg hp hc i v hv H x y :=
  facetMultilinearVolume_positive l h₀ hg hp hc hf i v hv hdim
    (Fin.cons x (Fin.cons y H)) (fun j => Fin.cases hx (fun k => Fin.cases hy hH k) j)

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FacetMixedForms.lean -/

/- BEGIN SOURCE: VolumePolynomials/FacetBochnerIdentity.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The exact facet identities for the mixed-support Bochner argument

The fixed background begins with one genuine support vector `h`. Symmetry
of actual mixed volume moves that argument into the support slot of the
first-variation formula. Extending the resulting identity from the open
support cone gives a bilinear identity on every real height direction.
The coordinate form of the same formula identifies each actual matrix row.
-/

noncomputable section
open Set MeasureTheory Module Matrix LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m n : ℕ}

theorem facetMixedValue_cons_eq
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (i : Fin m) (v : E) (hv : l i v = 1)
    {x h : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc) (hh : h ∈ typeCone l h₀ hp hc) :
    facetMixedValue l h₀ hp hc (Fin.cons h H) x i v hv =
      facetMixedForm l h₀ hg hp hc i v hv H x h := by
  first
  | rw [facetMixedForm_eq l h₀ hg hp hc i v hv H hH hx hh]
    unfold facetMixedValue
    congr 1
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j

theorem mixedSupportForm_row_facetMixedForm
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) (x : Fin m → ℝ) :
    ((n + 3 : ℕ) : ℝ) * mixedSupportForm volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H)) (Pi.single i 1) x =
      facetFrameFactor (l i) (v i) (hv i) * facetMixedForm l h₀ hg hp hc i (v i) (hv i) H x h := by
  first
  | have hon (y : Fin m → ℝ) (hy : y ∈ typeCone l h₀ hp hc) :
        ((n + 3 : ℕ) : ℝ) * mixedSupportForm volume l h₀ hg hp hc
          (coneTuple l h₀ hp hc (Fin.cons h H)) (Pi.single i 1) y =
        facetFrameFactor (l i) (v i) (hv i) * facetMixedForm l h₀ hg hp hc i (v i) (hv i) H y h := by
      first
      | have he := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray
          (Fin.cons h H) (fun j => Fin.cases hh hH j) v hv i hy
        rw [facetMixedValue_cons_eq l h₀ hg hp hc H hH i (v i) (hv i) hy hh] at he
        exact he
    obtain ⟨a, ha, b, hb, rfl⟩ := OpenConeExtension.exists_difference
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (typeCone_nonempty l h₀ hg hp hc) x
    rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sub_left, mul_sub, mul_sub, hon a ha, hon b hb]

theorem mixedSupportMatrix_row_facetMixedForm
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) (x : Fin m → ℝ) :
    ((n + 3 : ℕ) : ℝ) *
        (mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ x) i =
      facetFrameFactor (l i) (v i) (hv i) * facetMixedForm l h₀ hg hp hc i (v i) (hv i) H x h := by
  first
  | simpa only [mixedSupportForm_eq_dotProduct, single_one_dotProduct] using
      mixedSupportForm_row_facetMixedForm l h₀ hg hp hc hf hn hray H hH hh v hv i x

theorem mixedSupportForm_facet_bilinear_identity
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (x y : Fin m → ℝ) :
    ((n + 3 : ℕ) : ℝ) * mixedSupportForm volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H)) x y =
      ∑ i, facetFrameFactor (l i) (v i) (hv i) * h i *
        facetMixedForm l h₀ hg hp hc i (v i) (hv i) H x y := by
  first
  | let B := mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H))
    let L : Fin m → LinearMap.BilinForm ℝ (Fin m → ℝ) :=
      fun i => facetMixedForm l h₀ hg hp hc i (v i) (hv i) H
    let α : Fin m → ℝ := fun i => facetFrameFactor (l i) (v i) (hv i)
    have heq : (((n + 3 : ℕ) : ℝ) • B) = ∑ i, (α i * h i) • L i := by
      first
      | apply bilinear_ext_of_eq_on_cone (typeCone l h₀ hp hc)
          (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
        intro a ha b hb
        change ((n + 3 : ℕ) : ℝ) * B a b = _
        have hF : MultilinearDiagonal.PermutationSymmetric
            (supportMultilinearVolume volume l h₀ hg hp hc (n + 3)) :=
          supportMultilinearVolume_reindex volume l h₀ hg hp hc
        have hrotate := hF.rotate_first_three a b h H
        have hfirst := supportMultilinearVolume_firstTwoForm volume l h₀ hg hp hc
          (Fin.cons h H) (fun j => Fin.cases hh hH j)
        have hsecond := supportMultilinearVolume_firstTwoForm volume l h₀ hg hp hc
          (Fin.cons b H) (fun j => Fin.cases hb hH j)
        have hswap : B a b = mixedSupportForm volume l h₀ hg hp hc
            (coneTuple l h₀ hp hc (Fin.cons b H)) h a := by
          dsimp only [B]
          unfold coneTuple
          rw [← hfirst, ← hsecond]
          exact hrotate
        rw [hswap, mixedSupportForm_facet_on_cone l h₀ hg hp hc hf hn hray
          (Fin.cons b H) (fun j => Fin.cases hb hH j) v hv hh ha]
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [facetMixedValue_cons_eq l h₀ hg hp hc H hH i (v i) (hv i) ha hb]
    have he := congrArg (fun G : LinearMap.BilinForm ℝ (Fin m → ℝ) => G x y) heq
    simpa only [B, L, α, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using he

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 17
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FacetBochnerIdentity.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteBochner.lean -/
section

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The finite-dimensional Bochner reduction

This is the spectral step in the polytope proof of Alexandrov–Fenchel. All
operator hypotheses are explicit; a geometric application must prove them for
its actual mixed-volume operator. No geometric theorem is asserted here.
-/

namespace VolumePolynomials

open LinearMap Module
open scoped BigOperators RealInnerProductSpace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The Bochner inequality and a simple maximal eigenvalue one imply that the
quadratic form is nonpositive on the ordinary orthogonal complement of its
one-eigenvector. This uses Mathlib's full finite-dimensional spectral theorem. -/
theorem finite_bochner_nonpos_orthogonal (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (e : E)
    (hmax : ∀ (r : ℝ) (v : E), v ≠ 0 → T v = r • v → r ≤ 1)
    (hsimple : ∀ v : E, T v = v → ∃ c : ℝ, v = c • e)
    (hbochner : ∀ v : E, ⟪T v, v⟫_ℝ ≤ ⟪T v, T v⟫_ℝ)
    (x : E) (hxe : ⟪x, e⟫_ℝ = 0) : ⟪T x, x⟫_ℝ ≤ 0 := by
  first
  | classical
    let b := hT.eigenvectorBasis (n := finrank ℝ E) rfl
    let ev := hT.eigenvalues (n := finrank ℝ E) rfl
    have heig : ∀ i, T (b i) = ev i • b i := hT.apply_eigenvectorBasis rfl
    have hle : ∀ i, ev i ≤ 1 := fun i =>
      hmax (ev i) (b i) (b.toBasis.ne_zero i) (heig i)
    have hsq : ∀ i, ev i ≤ (ev i) ^ 2 := by
      first
      | intro i
        have h := hbochner (b i)
        simp only [heig, real_inner_smul_left, real_inner_smul_right] at h
        simpa only [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow, mul_one,
          pow_two] using h
    have hterm : ∀ i, ev i * (b.repr x i) ^ 2 ≤ 0 := by
      first
      | intro i
        by_cases hi : ev i ≤ 0
        · exact mul_nonpos_of_nonpos_of_nonneg hi (sq_nonneg _)
        · have hpos : 0 < ev i := lt_of_not_ge hi
          have hge : 1 ≤ ev i := by
            by_contra h
            have hp := mul_pos hpos (sub_pos.mpr (lt_of_not_ge h))
            nlinarith [hsq i]
          have heq : ev i = 1 := le_antisymm (hle i) hge
          obtain ⟨c, hc⟩ := hsimple (b i) (by rw [heig, heq, one_smul])
          have hcoord : b.repr x i = 0 := by
            rw [b.repr_apply_apply, hc, real_inner_smul_left,
              real_inner_comm x e, hxe, mul_zero]
          simp only [hcoord, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    have hquad : ⟪T x, x⟫_ℝ = ∑ i, ev i * (b.repr x i) ^ 2 := by
      first
      | rw [← b.sum_inner_mul_inner (T x) x]
        apply Finset.sum_congr rfl
        intro i _
        rw [hT x (b i), heig, real_inner_smul_right,
          real_inner_comm (b i) x, b.repr_apply_apply]
        ring
    rw [hquad]
    exact Finset.sum_nonpos (fun i _ => hterm i)

/-- The finite Bochner hypotheses imply the full reverse Cauchy–Schwarz
inequality for the associated bilinear form, including its null boundary. -/
theorem finite_bochner_reverse_cauchy_schwarz (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (e : E) (he : T e = e)
    (hmax : ∀ (r : ℝ) (v : E), v ≠ 0 → T v = r • v → r ≤ 1)
    (hsimple : ∀ v : E, T v = v → ∃ c : ℝ, v = c • e)
    (hbochner : ∀ v : E, ⟪T v, v⟫_ℝ ≤ ⟪T v, T v⟫_ℝ)
    (x y : E) (hy : 0 ≤ ⟪T y, y⟫_ℝ) :
    ⟪T x, x⟫_ℝ * ⟪T y, y⟫_ℝ ≤ ⟪T x, y⟫_ℝ ^ 2 := by
  first
  | let B : LinearMap.BilinForm ℝ E := LinearMap.comp (innerₗ E) T
    have hB : ∀ v w, B v w = B w v := by
      first
      | intro v w
        change ⟪T v, w⟫_ℝ = ⟪T w, v⟫_ℝ
        rw [hT v w, real_inner_comm (T w) v]
    have hperp : ∀ v, B v e = 0 → B v v ≤ 0 := by
      first
      | intro v hv
        change ⟪T v, e⟫_ℝ = 0 at hv
        rw [hT v e, he] at hv
        exact finite_bochner_nonpos_orthogonal T hT e hmax hsimple hbochner v hv
    exact bilinear_reverse_cauchy_schwarz B hB e hperp x y hy

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteBochner.lean -/

/- BEGIN SOURCE: VolumePolynomials/MatrixPositiveEigenvector.lean -/
section

@[expose] public section
noncomputable section

/-!
# Normalizing a positive eigenvector

Diagonal conjugation reduces the maximum principle for an operator with a
strictly positive fixed vector to the row-sum-one case. Diagonal entries may
have either sign, as they do for mixed-volume operators.
-/

namespace VolumePolynomials
open Finset Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveConjugate (A : Matrix ι ι ℝ) (h : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j * h j / h i

theorem positiveConjugate_row_sum (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (hfix : A *ᵥ h = h) :
    ∀ i, ∑ j, positiveConjugate A h i j = 1 := by
  first
  | intro i
    simp only [positiveConjugate, ← sum_div]
    change (A *ᵥ h) i / h i = 1
    rw [hfix, div_self (hpos i).ne']

theorem positiveConjugate_offdiag (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) :
    ∀ i j, i ≠ j → 0 ≤ positiveConjugate A h i j := by
  first
  | intro i j hij
    exact div_nonneg (mul_nonneg (hoff i j hij) (hpos j).le) (hpos i).le

theorem positiveConjugate_positiveEdge_iff (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (i j : ι) :
    MatrixPositiveEdge (positiveConjugate A h) i j ↔ MatrixPositiveEdge A i j := by
  first
  | simp only [MatrixPositiveEdge, positiveConjugate,
      div_pos_iff_of_pos_right (hpos i), mul_pos_iff_of_pos_right (hpos j)]

theorem positiveConjugate_mulVec (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hne : ∀ i, h i ≠ 0) (x : ι → ℝ) (i : ι) :
    (positiveConjugate A h *ᵥ (fun j => x j / h j)) i = (A *ᵥ x) i / h i := by
  first
  | change (∑ j, (A i j * h j / h i) * (x j / h j)) =
      (∑ j, A i j * x j) / h i
    rw [sum_div]
    apply sum_congr rfl
    intro j _
    field_simp [hne i, hne j]

/-- A positive fixed vector bounds every real eigenvalue by one. -/
theorem matrix_eigenvalue_le_one_of_positive_fixed (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (hfix : A *ᵥ h = h)
    (r : ℝ) (x : ι → ℝ) (hx : x ≠ 0) (heig : A *ᵥ x = r • x) : r ≤ 1 := by
  first
  | let y : ι → ℝ := fun i => x i / h i
    have hy : y ≠ 0 := by
      intro hyzero
      apply hx
      funext i
      have hi : x i / h i = 0 := congrFun hyzero i
      exact (div_eq_zero_iff).mp hi |>.resolve_right (hpos i).ne'
    have hyeig : positiveConjugate A h *ᵥ y = r • y := by
      funext i
      rw [positiveConjugate_mulVec A h (fun j => (hpos j).ne'), heig]
      change (r * x i) / h i = r * (x i / h i)
      exact mul_div_assoc _ _ _
    exact matrix_eigenvalue_le_one (positiveConjugate A h)
      (positiveConjugate_offdiag A h hpos hoff)
      (positiveConjugate_row_sum A h hpos hfix) r y hy hyeig

/-- Positive-entry connectivity makes the fixed space exactly the span of the
positive fixed vector. -/
theorem matrix_fixed_eq_smul_positive [Nonempty ι] (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j)
    (h : ι → ℝ) (hpos : ∀ i, 0 < h i) (hfix : A *ᵥ h = h)
    (x : ι → ℝ) (hx : A *ᵥ x = x) : ∃ c : ℝ, x = c • h := by
  first
  | let y : ι → ℝ := fun i => x i / h i
    have hyfix : positiveConjugate A h *ᵥ y = y := by
      funext i
      rw [positiveConjugate_mulVec A h (fun j => (hpos j).ne'), hx]
    have hc : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge (positiveConjugate A h)) i j := by
      intro i j
      exact Relation.ReflTransGen.mono
        (fun a b hab => (positiveConjugate_positiveEdge_iff A h hpos a b).mpr hab)
        i j (hconn i j)
    obtain ⟨c, hc⟩ := matrix_fixed_eq_constant (positiveConjugate A h)
      (positiveConjugate_offdiag A h hpos hoff)
      (positiveConjugate_row_sum A h hpos hfix) hc y hyfix
    refine ⟨c, funext fun i => ?_⟩
    have hi : x i / h i = c := congrFun hc i
    exact (div_eq_iff (hpos i).ne').mp hi

end VolumePolynomials
end -- closes the original EOF section from source line 6
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/MatrixPositiveEigenvector.lean -/

/- BEGIN SOURCE: VolumePolynomials/WeightedMatrixBochner.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The weighted matrix form of the finite Bochner argument

For a symmetric matrix `M`, a positive vector `h` with positive `M h`
determines positive weights `mᵢ = (M h)ᵢ / hᵢ`. Conjugation by their square
roots turns the weighted operator into an ordinary symmetric Euclidean
operator. The maximum principle and the finite-dimensional spectral
theorem then give the full reverse Cauchy--Schwarz inequality.
-/

open Matrix Finset
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace VolumePolynomials

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixForm (M : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ i, (M *ᵥ x) i * y i

theorem euclidean_matrix_inner (M : Matrix ι ι ℝ)
    (x y : EuclideanSpace ℝ ι) :
    ⟪M.toEuclideanLin x, y⟫_ℝ = matrixForm M x.ofLp y.ofLp := by
  first
  | simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct, Pi.star_apply, star_trivial, matrixForm]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- A matrix version of the already proved Euclidean Bochner reduction.
The positive-entry graph may have arbitrary diagonal entries. -/
theorem matrix_bochner_reverse_cauchy_schwarz
    (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    (h : ι → ℝ) (hpos : ∀ i, 0 < h i) (hfix : M *ᵥ h = h)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge M) i j)
    (hbochner : ∀ x : ι → ℝ,
      matrixForm M x x ≤ ∑ i, (M *ᵥ x) i ^ 2)
    (x y : ι → ℝ) (hy : 0 ≤ matrixForm M y y) :
    matrixForm M x x * matrixForm M y y ≤ matrixForm M x y ^ 2 := by
  first
  | cases isEmpty_or_nonempty ι with
    | inl hi =>
        letI := hi
        simp [matrixForm]
    | inr hi =>
        letI := hi
        let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := M.toEuclideanLin
        let e : EuclideanSpace ℝ ι := WithLp.toLp 2 h
        have hT : T.IsSymmetric := by
          apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
          ext i j
          simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym j i
        have he : T e = e := by
          change WithLp.toLp 2 (M *ᵥ h) = WithLp.toLp 2 h
          rw [hfix]
        have hmax : ∀ (r : ℝ) (v : EuclideanSpace ℝ ι),
            v ≠ 0 → T v = r • v → r ≤ 1 := by
          intro r v hv heig
          have hv' : v.ofLp ≠ 0 := by
            intro hz
            apply hv
            apply WithLp.ofLp_injective
            exact hz
          have heig' : M *ᵥ v.ofLp = r • v.ofLp :=
            congrArg WithLp.ofLp heig
          exact matrix_eigenvalue_le_one_of_positive_fixed M hoff h hpos hfix r v.ofLp hv' heig'
        have hsimple : ∀ v : EuclideanSpace ℝ ι,
            T v = v → ∃ c : ℝ, v = c • e := by
          intro v hv
          have hv' : M *ᵥ v.ofLp = v.ofLp := congrArg WithLp.ofLp hv
          obtain ⟨c, hc⟩ := matrix_fixed_eq_smul_positive M hoff hconn h hpos hfix v.ofLp hv'
          exact ⟨c, WithLp.ofLp_injective 2 hc⟩
        have hbochner' : ∀ v : EuclideanSpace ℝ ι,
            ⟪T v, v⟫_ℝ ≤ ⟪T v, T v⟫_ℝ := by
          intro v
          rw [euclidean_matrix_inner]
          have hnorm : ⟪T v, T v⟫_ℝ = ∑ i, (M *ᵥ v.ofLp) i ^ 2 := by
            simp only [EuclideanSpace.inner_eq_star_dotProduct, T,
              Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct,
              Pi.star_apply, star_trivial, pow_two]
          rw [hnorm]
          exact hbochner v.ofLp
        have hresult := finite_bochner_reverse_cauchy_schwarz T hT e he hmax hsimple hbochner'
          (WithLp.toLp 2 x) (WithLp.toLp 2 y)
          (by simpa only [T, euclidean_matrix_inner, WithLp.ofLp_toLp] using hy)
        simpa only [T, euclidean_matrix_inner, WithLp.ofLp_toLp] using hresult

def sqrtConjugate (M : Matrix ι ι ℝ) (m : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => M i j / (Real.sqrt (m i) * Real.sqrt (m j))

def sqrtWeighted (m x : ι → ℝ) : ι → ℝ := fun i => Real.sqrt (m i) * x i

theorem sqrtConjugate_mulVec (M : Matrix ι ι ℝ) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (x : ι → ℝ) (i : ι) :
    (sqrtConjugate M m *ᵥ sqrtWeighted m x) i = (M *ᵥ x) i / Real.sqrt (m i) := by
  first
  | change (∑ j, M i j / (Real.sqrt (m i) * Real.sqrt (m j)) *
        (Real.sqrt (m j) * x j)) = (∑ j, M i j * x j) / Real.sqrt (m i)
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [(Real.sqrt_pos.mpr (hm i)).ne', (Real.sqrt_pos.mpr (hm j)).ne']

theorem sqrtConjugate_form (M : Matrix ι ι ℝ) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (x y : ι → ℝ) :
    matrixForm (sqrtConjugate M m) (sqrtWeighted m x) (sqrtWeighted m y) =
      matrixForm M x y := by
  first
  | unfold matrixForm
    apply Finset.sum_congr rfl
    intro i _
    rw [sqrtConjugate_mulVec M m hm x i]
    dsimp only [sqrtWeighted]
    field_simp [(Real.sqrt_pos.mpr (hm i)).ne']

theorem sqrtConjugate_norm (M : Matrix ι ι ℝ) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (x : ι → ℝ) :
    (∑ i, (sqrtConjugate M m *ᵥ sqrtWeighted m x) i ^ 2) =
      ∑ i, (M *ᵥ x) i ^ 2 / m i := by
  first
  | apply Finset.sum_congr rfl
    intro i _
    rw [sqrtConjugate_mulVec M m hm x i, div_pow, Real.sq_sqrt (hm i).le]

/-- The weighted spectral criterion, with independently specified positive
weights and their actual eigenvector equation. -/
theorem weighted_matrix_reverse_cauchy_schwarz
    (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    (m h : ι → ℝ) (hm : ∀ i, 0 < m i) (hh : ∀ i, 0 < h i)
    (hweighted : ∀ i, (M *ᵥ h) i = m i * h i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge M) i j)
    (hbochner : ∀ x : ι → ℝ,
      matrixForm M x x ≤ ∑ i, (M *ᵥ x) i ^ 2 / m i)
    (x y : ι → ℝ) (hy : 0 ≤ matrixForm M y y) :
    matrixForm M x x * matrixForm M y y ≤ matrixForm M x y ^ 2 := by
  first
  | let A := sqrtConjugate M m
    let e := sqrtWeighted m h
    have hA : ∀ i j, A i j = A j i := by
      intro i j
      dsimp only [A, sqrtConjugate]
      rw [hsym i j, mul_comm (Real.sqrt (m i))]
    have he : ∀ i, 0 < e i := fun i => mul_pos (Real.sqrt_pos.mpr (hm i)) (hh i)
    have hfix : A *ᵥ e = e := by
      funext i
      rw [sqrtConjugate_mulVec M m hm h i, hweighted i]
      change m i * h i / Real.sqrt (m i) = Real.sqrt (m i) * h i
      calc
        _ = Real.sqrt (m i) ^ 2 * h i / Real.sqrt (m i) :=
          congrArg (fun a : ℝ => a * h i / Real.sqrt (m i)) (Real.sq_sqrt (hm i).le).symm
        _ = _ := by
          field_simp [(Real.sqrt_pos.mpr (hm i)).ne']
    have hoffA : ∀ i j, i ≠ j → 0 ≤ A i j := by
      intro i j hij
      exact div_nonneg (hoff i j hij)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hedges : ∀ i j, MatrixPositiveEdge M i j → MatrixPositiveEdge A i j := by
      rintro i j ⟨hne, hpos⟩
      exact ⟨hne, div_pos hpos (mul_pos (Real.sqrt_pos.mpr (hm i)) (Real.sqrt_pos.mpr (hm j)))⟩
    have hconnA : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j :=
      fun i j => Relation.ReflTransGen.mono hedges i j (hconn i j)
    have hbochnerA : ∀ v : ι → ℝ, matrixForm A v v ≤ ∑ i, (A *ᵥ v) i ^ 2 := by
      intro v
      let u : ι → ℝ := fun i => v i / Real.sqrt (m i)
      have hu : sqrtWeighted m u = v := by
        funext i
        exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr (hm i)).ne'
      rw [← hu, sqrtConjugate_form M m hm, sqrtConjugate_norm M m hm]
      exact hbochner u
    have hresult := matrix_bochner_reverse_cauchy_schwarz A hA e he hfix hoffA hconnA hbochnerA
      (sqrtWeighted m x) (sqrtWeighted m y)
      (by rwa [sqrtConjugate_form M m hm])
    simpa only [A, sqrtConjugate_form M m hm] using hresult

/-- The form used by the geometric Alexandrov operator. The weights are
computed from `M` and `h`; there is no independent operator premise. -/
theorem matrix_reverse_cauchy_schwarz_of_weighted_bochner
    (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    (h : ι → ℝ) (hh : ∀ i, 0 < h i) (hMh : ∀ i, 0 < (M *ᵥ h) i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge M) i j)
    (hbochner : ∀ x : ι → ℝ,
      matrixForm M x x ≤ ∑ i, (M *ᵥ x) i ^ 2 / ((M *ᵥ h) i / h i))
    (x y : ι → ℝ) (hy : 0 ≤ matrixForm M y y) :
    matrixForm M x x * matrixForm M y y ≤ matrixForm M x y ^ 2 := by
  first
  | apply weighted_matrix_reverse_cauchy_schwarz M hsym
      (fun i => (M *ᵥ h) i / h i) h
      (fun i => div_pos (hMh i) (hh i)) hh
      (fun i => (div_mul_cancel₀ _ (hh i).ne').symm) hoff hconn hbochner x y hy

end VolumePolynomials
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/WeightedMatrixBochner.lean -/

/- BEGIN SOURCE: VolumePolynomials/FacetBochnerStep.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # The dimension step of Alexandrov--Fenchel on a common simple type

The only inductive input is the literal mixed-volume inequality on the
actual lower-dimensional facet spaces. All operator identities, positivity,
off-diagonal signs, and connectivity are derived from the genuine bodies.
The endpoint of this module is an induction step; the dimension induction
and approximation to arbitrary bodies are supplied separately.
-/

noncomputable section
open Set MeasureTheory Module Matrix LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m n : ℕ}

theorem facet_bochner_summand
    {N α h u v w r s : ℝ} (hN : 0 < N) (hα : 0 < α) (hh : 0 < h)
    (hw : 0 < w) (hr : N * r = α * v) (hs : N * s = α * w)
    (hi : u * w ≤ v ^ 2) : (α * h / N) * u ≤ r ^ 2 / (s / h) := by
  first
  | have hr' : r = α * v / N := by
      first
      | apply (eq_div_iff hN.ne').mpr
        nlinarith [hr]
    have hs' : s = α * w / N := by
      first
      | apply (eq_div_iff hN.ne').mpr
        nlinarith [hs]
    have he : r ^ 2 / (s / h) = (α * h / N) * (v ^ 2 / w) := by
      first
      | rw [hr', hs']
        field_simp [hN.ne', hα.ne', hh.ne', hw.ne']
    rw [he]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hw).mpr hi)
      (div_nonneg (mul_nonneg hα.le hh.le) hN.le)

theorem facetMixedForm_reference_inequality_of_lower_dimension
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (i : Fin m) (v : E) (hv : l i v = 1)
    (hIH : ∀ (K : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
      (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A K)) *
        mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B K)) ^ 2)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc) (x : Fin m → ℝ) :
    facetMixedForm l h₀ hg hp hc i v hv H x x *
        facetMixedForm l h₀ hg hp hc i v hv H h h ≤
      facetMixedForm l h₀ hg hp hc i v hv H x h ^ 2 := by
  first
  | apply OpenConeExtension.bilinear_reference_inequality_of_cone
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (facetMixedForm l h₀ hg hp hc i v hv H)
      (facetMixedForm_symmetric l h₀ hg hp hc i v hv H) hh
    intro y hy
    rw [facetMixedForm_eq l h₀ hg hp hc i v hv H hH hy hy,
      facetMixedForm_eq l h₀ hg hp hc i v hv H hH hh hh,
      facetMixedForm_eq l h₀ hg hp hc i v hv H hH hy hh]
    exact hIH _ _ _

theorem matrixForm_mixedSupportMatrix
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : Fin m → ℝ) :
    matrixForm (mixedSupportMatrix volume l h₀ hg hp hc K) x y =
      mixedSupportForm volume l h₀ hg hp hc K x y := by
  first
  | rw [mixedSupportForm_symmetric volume l h₀ hg hp hc K x y,
      mixedSupportForm_eq_dotProduct]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem mixedSupportMatrix_image_pos
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) :
    0 < (mixedSupportMatrix volume l h₀ hg hp hc
      (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ h) i := by
  first
  | have he := mixedSupportMatrix_row_facetMixedForm l h₀ hg hp hc hf hn hray
      H hH hh v hv i h
    have hpos := mul_pos (facetFrameFactor_pos (l i) (v i) (hv i))
      (facetMixedForm_positive l h₀ hg hp hc hf i (v i) (hv i) hdim H hH hh hh)
    rw [← he] at hpos
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < ((n + 3 : ℕ) : ℝ))).mp hpos

theorem mixedSupportMatrix_bochner_of_lower_dimension
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (hIH : ∀ i (K : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
      (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A K)) *
        mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B K)) ^ 2)
    (x : Fin m → ℝ) :
    matrixForm (mixedSupportMatrix volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H))) x x ≤
      ∑ i, ((mixedSupportMatrix volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ x) i) ^ 2 /
        ((mixedSupportMatrix volume l h₀ hg hp hc
          (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ h) i / h i) := by
  first
  | let N : ℝ := ((n + 3 : ℕ) : ℝ)
    have hN : 0 < N := by dsimp [N]; positivity
    let α : Fin m → ℝ := fun i => facetFrameFactor (l i) (v i) (hv i)
    let L : Fin m → LinearMap.BilinForm ℝ (Fin m → ℝ) :=
      fun i => facetMixedForm l h₀ hg hp hc i (v i) (hv i) H
    let A := mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H))
    have hsum : matrixForm A x x = ∑ i, (α i * h i / N) * L i x x := by
      first
      | rw [matrixForm_mixedSupportMatrix]
        have he := mixedSupportForm_facet_bilinear_identity l h₀ hg hp hc hf hn hray
          H hH hh v hv x x
        calc
          _ = (∑ i, α i * h i * L i x x) / N := by
            apply (eq_div_iff hN.ne').mpr
            nlinarith [he]
          _ = _ := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
    rw [hsum]
    apply Finset.sum_le_sum
    intro i _
    exact facet_bochner_summand hN (facetFrameFactor_pos (l i) (v i) (hv i)) (hh.1 i)
      (facetMixedForm_positive l h₀ hg hp hc hf i (v i) (hv i) hdim H hH hh hh)
      (mixedSupportMatrix_row_facetMixedForm l h₀ hg hp hc hf hn hray H hH hh v hv i x)
      (mixedSupportMatrix_row_facetMixedForm l h₀ hg hp hc hf hn hray H hH hh v hv i h)
      (facetMixedForm_reference_inequality_of_lower_dimension l h₀ hg hp hc
        H hH i (v i) (hv i) (hIH i) hh x)

theorem mixedSupportForm_reverse_cauchy_schwarz_of_lower_dimension
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (hIH : ∀ i (K : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
      (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A K)) *
        mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B K)) ^ 2)
    (x y : Fin m → ℝ)
    (hy : 0 ≤ mixedSupportForm volume l h₀ hg hp hc
      (coneTuple l h₀ hp hc (Fin.cons h H)) y y) :
    mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) x x *
        mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) y y ≤
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) x y ^ 2 := by
  first
  | let G : Fin (n + 1) → Fin m → ℝ := Fin.cons h H
    have hG : ∀ j, G j ∈ typeCone l h₀ hp hc := fun j => Fin.cases hh hH j
    let A := mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc G)
    have he := matrix_reverse_cauchy_schwarz_of_weighted_bochner A
      (mixedSupportMatrix_symmetric volume l h₀ hg hp hc _) h hh.1
      (mixedSupportMatrix_image_pos l h₀ hg hp hc hf hn hray hdim H hH hh v hv)
      (mixedSupportMatrix_offdiag_nonnegative l h₀ hg hp hc hf hn hray G hG hdim v hv)
      (mixedSupportMatrix_positive_graph_connected l h₀ hg hp hc hf hn hray hdim G hG v hv)
      (mixedSupportMatrix_bochner_of_lower_dimension l h₀ hg hp hc hf hn hray
        hdim H hH hh v hv hIH) x y
      (by simpa only [A, matrixForm_mixedSupportMatrix] using hy)
    simpa only [A, G, matrixForm_mixedSupportMatrix] using he

end VolumePolynomials.PolyhedralSupport
end -- closes the original EOF section from source line 18
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FacetBochnerStep.lean -/

/- BEGIN SOURCE: VolumePolynomials/FiniteHullInvariantTransfer.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Closed translation-invariant properties of tuples of convex bodies

Actual finite convex hulls are dense in the Hausdorff metric. A finite
simplex thickening makes their centered total sum full dimensional. These
two limit arguments remove the auxiliary centering and interior conditions
from any closed property invariant under independent translations.
-/

noncomputable section
open Set Filter Module
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}

theorem all_bodyTuples_of_centered_finiteHull
    (hN : 0 < N) (S : Set (Fin N → ConvexBody E)) (hclosed : IsClosed S)
    (htranslate : ∀ K ∈ S, ∀ v : Fin N → E,
      (fun i => translateBody (v i) (K i)) ∈ S)
    (hcenter : ∀ K : Fin N → ConvexBody E,
      (∀ i, IsFiniteHull (K i : Set E)) → (∀ i, (0 : E) ∈ K i) →
      (0 : E) ∈ interior (↑(∑ i, K i) : Set E) → K ∈ S)
    (K : Fin N → ConvexBody E) : K ∈ S := by
  first
  | have hfinite : {L : Fin N → ConvexBody E | ∀ i, IsFiniteHull (L i : Set E)} ⊆ S := by
      intro L hL
      choose p hp using fun i => (L i).nonempty
      let Q : Fin N → ConvexBody E := fun i => translateBody (-p i) (L i)
      have hQ0 : ∀ i, (0 : E) ∈ Q i := fun i => zero_mem_translateBody_neg (hp i)
      have hQfinite : ∀ i, IsFiniteHull (Q i : Set E) :=
        fun i => isFiniteHull_translateBody (hL i) (-p i)
      obtain ⟨P, hPfinite, hPint⟩ := exists_finiteHull_with_zero_interior (E := E)
      have hP0 : (0 : E) ∈ P := interior_subset hPint
      let R : ℝ → Fin N → ConvexBody E := fun r i => Q i + r • P
      have hR0 (r : ℝ) (i : Fin N) : (0 : E) ∈ R r i :=
        ⟨0, hQ0 i, 0, ⟨0, hP0, by simp⟩, zero_add 0⟩
      have hRfinite (r : ℝ) (i : Fin N) : IsFiniteHull (R r i : Set E) :=
        (hQfinite i).add (hPfinite.smul r)
      have hRint {r : ℝ} (hr : 0 < r) :
          (0 : E) ∈ interior (↑(∑ i, R r i) : Set E) := by
        have hpint : (0 : E) ∈ interior (r • (P : Set E)) := by
          rw [interior_smul₀ hr.ne']
          exact ⟨0, hPint, by simp⟩
        have hsub : r • (P : Set E) ⊆ (↑(∑ i, R r i) : Set E) := by
          intro x hx
          apply body_le_sum_of_zero_mem (R r) (hR0 r) (⟨0, hN⟩ : Fin N)
          exact ⟨0, hQ0 _, x, hx, zero_add x⟩
        exact interior_mono hsub hpint
      have hcont : Continuous R := by
        dsimp [R]
        fun_prop
      have ht : Tendsto R (𝓝[>] 0) (𝓝 Q) := by
        simpa only [R, body_zero_smul, add_zero] using
          (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      have hRmem : ∀ᶠ r : ℝ in 𝓝[>] 0, R r ∈ S := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact hcenter (R r) (hRfinite r) (hR0 r) (hRint hr)
      have hQ : Q ∈ S := hclosed.mem_of_tendsto ht hRmem
      have hback := htranslate Q hQ p
      simpa only [Q, translateBody_translate, add_neg_cancel, translateBody_zero] using hback
    exact closure_minimal hfinite hclosed (dense_finiteHullBodyTuples (E := E) N K)

end VolumePolynomials
end -- closes the original EOF section from source line 16
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/FiniteHullInvariantTransfer.lean -/

/- BEGIN SOURCE: VolumePolynomials/AlexandrovFenchel.lean -/
section


@[expose] public section
set_option autoImplicit false

/-! # Alexandrov--Fenchel for actual compact convex bodies

The induction begins with the actual planar Brunn--Minkowski inequality.
The next dimension is proved on a constructed common simple support type
by the actual facet identities and the finite Bochner argument. Genuine
common-refinement approximants, independent translations, simplex
thickening, and finite-hull density remove every geometric restriction.

Mixed volume throughout is the normalized coefficient of the proved
Minkowski volume polynomial, with the specified actual Haar measure.
-/

noncomputable section
open Set Filter MeasureTheory Module Matrix LinearMap
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials

open PolytopeGeometry PolyhedralSupport

universe u

def firstRepeatIndex (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cons 0 (Fin.cons 0 (fun i : Fin n => i.succ.succ))

def secondRepeatIndex (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cons 1 (Fin.cons 1 (fun i : Fin n => i.succ.succ))

section Tuple

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ] {n : ℕ}

def AFBodyTuple (K : Fin (n + 2) → ConvexBody E) : Prop :=
  mixedVolume μ (fun i => K (firstRepeatIndex n i)) *
      mixedVolume μ (fun i => K (secondRepeatIndex n i)) ≤ mixedVolume μ K ^ 2

theorem AFBodyTuple_cons (A B : ConvexBody E) (K : Fin n → ConvexBody E) :
    AFBodyTuple μ (Fin.cons A (Fin.cons B K)) ↔
      mixedVolume μ (Fin.cons A (Fin.cons A K)) *
        mixedVolume μ (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume μ (Fin.cons A (Fin.cons B K)) ^ 2 := by
  first
  | have hfirst : (fun i : Fin (n + 2) =>
        (Fin.cons A (Fin.cons B K) : Fin (n + 2) → ConvexBody E) (firstRepeatIndex n i)) =
        (Fin.cons A (Fin.cons A K) : Fin (n + 2) → ConvexBody E) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    have hsecond : (fun i : Fin (n + 2) =>
        (Fin.cons A (Fin.cons B K) : Fin (n + 2) → ConvexBody E) (secondRepeatIndex n i)) =
        (Fin.cons B (Fin.cons B K) : Fin (n + 2) → ConvexBody E) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    simp only [AFBodyTuple, hfirst, hsecond]

theorem isClosed_afBodyTuples : IsClosed {K : Fin (n + 2) → ConvexBody E | AFBodyTuple μ K} := by
  first
  | apply isClosed_le
    · exact ((continuous_mixedVolume μ (n + 2)).comp
        (continuous_pi (fun i => continuous_apply (firstRepeatIndex n i)))).mul
        ((continuous_mixedVolume μ (n + 2)).comp
          (continuous_pi (fun i => continuous_apply (secondRepeatIndex n i))))
    · exact (continuous_mixedVolume μ (n + 2)).pow 2

theorem AFBodyTuple.translate {K : Fin (n + 2) → ConvexBody E}
    (hK : AFBodyTuple μ K) (v : Fin (n + 2) → E) :
    AFBodyTuple μ (fun i => translateBody (v i) (K i)) := by
  first
  | change mixedVolume μ (fun i => translateBody (v (firstRepeatIndex n i))
        (K (firstRepeatIndex n i))) *
      mixedVolume μ (fun i => translateBody (v (secondRepeatIndex n i))
        (K (secondRepeatIndex n i))) ≤
      mixedVolume μ (fun i => translateBody (v i) (K i)) ^ 2
    simpa only [AFBodyTuple, mixedVolume_translate] using hK

end Tuple

/-- The induction predicate has no restriction on the norm, Haar
normalization, or dimension of the individual convex bodies. -/
def AlexandrovFenchelDimension (n : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ],
    finrank ℝ E = n + 2 → ∀ K : Fin (n + 2) → ConvexBody E, AFBodyTuple μ K

theorem alexandrovFenchelDimension_zero : AlexandrovFenchelDimension.{u} 0 := by
  first
  | intro E _ _ _ _ _ μ _ hdim K
    have hK : K = ![K 0, K 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hK]
    apply (AFBodyTuple_cons μ (K 0) (K 1) (fun i : Fin 0 => Fin.elim0 i)).mpr
    have hdiag (A : ConvexBody E) :
        mixedVolume μ (Fin.cons A (Fin.cons A (fun i : Fin 0 => Fin.elim0 i))) =
          μ.real (A : Set E) := by
      have he : Fin.cons A (Fin.cons A (fun i : Fin 0 => Fin.elim0 i)) =
          (fun _ : Fin 2 => A) := by
        funext i
        fin_cases i <;> rfl
      rw [he, mixedVolume_diagonal μ hdim]
    rw [hdiag, hdiag]
    exact PlanarMixedForm.minkowski_squared μ hdim (K 0) (K 1)

section DimensionStep

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {n : ℕ}

theorem AFBodyTuple_commonRefinement
    (hIH : AlexandrovFenchelDimension.{u} n) (hdim : finrank ℝ E = n + 3)
    (K : Fin (n + 3) → ConvexBody E) (D : CommonRefinement K)
    (h0 : ∀ i, (0 : E) ∈ K i) {r : ℝ} (hr : 0 < r) :
    AFBodyTuple volume (D.approximant r) := by
  first
  | let l := D.facets.normal
    let h₀ := D.height
    have hc : IsCompact (body l h₀) := D.reference_eq ▸ D.reference.isCompact
    let G := D.approximantHeight r
    have hG : ∀ j, G j ∈ typeCone l h₀ D.height_pos hc :=
      D.approximantHeight_mem_supportCone h0 hr
    have hbody (j : Fin (n + 3)) :
        bodyAtHeight l h₀ D.height_pos hc (G j) = D.approximant r j := by
      apply ConvexBody.ext
      rw [coe_bodyAtHeight l h₀ D.height_pos hc (hG j), D.approximant_eq_halfspaces hr j]
    have hw : ∀ i, ∃ v : E, l i v = 1 := by
      intro i
      have hnot : ¬ ∀ x : E, l i x = 0 := by
        intro hz
        apply D.facets.normal_ne_zero i
        ext x
        exact hz x
      obtain ⟨x, hx⟩ := not_forall.mp hnot
      refine ⟨(l i x)⁻¹ • x, ?_⟩
      simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
    choose v hv using hw
    let x := G 0
    let y := G 1
    let h := G 2
    let H : Fin n → Fin D.facets.count → ℝ := fun j => G j.succ.succ.succ
    have hx : x ∈ typeCone l h₀ D.height_pos hc := hG 0
    have hy : y ∈ typeCone l h₀ D.height_pos hc := hG 1
    have hh : h ∈ typeCone l h₀ D.height_pos hc := hG 2
    have hH : ∀ j, H j ∈ typeCone l h₀ D.height_pos hc := fun j => hG _
    have hlow : ∀ i (J : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
        (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
        mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A J)) *
          mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B J)) ≤
        mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B J)) ^ 2 := by
      intro i J A B
      have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = n + 2 := by
        have he := LinearFrame.finrank_kernel_add_one (l i) (v i) (hv i)
        rw [hdim] at he
        omega
      exact (AFBodyTuple_cons (kernelMeasure (l i)) A B J).mp
        (hIH _ (kernelMeasure (l i)) hkdim (Fin.cons A (Fin.cons B J)))
    let B := mixedSupportForm volume l h₀ D.generic D.height_pos hc
      (coneTuple l h₀ D.height_pos hc (Fin.cons h H))
    have hBnonneg : 0 ≤ B y y := by
      rw [mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hy hy]
      exact mixedVolume_nonnegative volume _
    have hi := mixedSupportForm_reverse_cauchy_schwarz_of_lower_dimension
      l h₀ D.generic D.height_pos hc D.strict_facets D.facets.normal_ne_zero
      D.facets.positive_ray_injective hdim H hH hh v hv hlow x y hBnonneg
    rw [mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hx hx,
      mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hy hy,
      mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hx hy] at hi
    have htuple : D.approximant r =
        Fin.cons (bodyAtHeight l h₀ D.height_pos hc x)
          (Fin.cons (bodyAtHeight l h₀ D.height_pos hc y)
            (coneTuple l h₀ D.height_pos hc (Fin.cons h H))) := by
      funext j
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.cases ?_ (fun s => ?_) q) k) j
      · exact (hbody 0).symm
      · exact (hbody 1).symm
      · exact (hbody 2).symm
      · exact (hbody s.succ.succ.succ).symm
    rw [htuple, AFBodyTuple_cons]
    exact hi

theorem AFBodyTuple_centered_finiteHull
    (hIH : AlexandrovFenchelDimension.{u} n) (hdim : finrank ℝ E = n + 3)
    (K : Fin (n + 3) → ConvexBody E)
    (hK : ∀ i, IsFiniteHull (K i : Set E)) (h0 : ∀ i, (0 : E) ∈ K i)
    (hint : (0 : E) ∈ interior (↑(∑ i, K i) : Set E)) : AFBodyTuple volume K := by
  first
  | obtain ⟨D⟩ := exists_commonRefinement K hK h0 hint
    have hlim : Tendsto D.approximant (𝓝[>] (0 : ℝ)) (𝓝 K) :=
      D.tendsto_approximant_zero.mono_left nhdsWithin_le_nhds
    apply (isClosed_afBodyTuples volume).mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact AFBodyTuple_commonRefinement hIH hdim K D h0 hr

end DimensionStep

theorem alexandrovFenchelDimension_succ {n : ℕ}
    (hIH : AlexandrovFenchelDimension.{u} n) : AlexandrovFenchelDimension.{u} (n + 1) := by
  first
  | intro E _ _ _ _ _ μ _ hdim K
    letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
    letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) :=
      inferInstanceAs (Measure.IsAddHaarMeasure μ)
    exact all_bodyTuples_of_centered_finiteHull (by omega)
      {L : Fin (n + 3) → ConvexBody E | AFBodyTuple μ L}
      (isClosed_afBodyTuples μ)
      (fun L hL v => AFBodyTuple.translate μ hL v)
      (fun L hL h0 hint => AFBodyTuple_centered_finiteHull hIH hdim L hL h0 hint) K

theorem alexandrovFenchelDimension (n : ℕ) : AlexandrovFenchelDimension.{u} n := by
  first
  | induction n with
    | zero => exact alexandrovFenchelDimension_zero
    | succ n ih => exact alexandrovFenchelDimension_succ ih

/-- The full Alexandrov--Fenchel inequality for actual compact convex bodies,
in every ambient dimension at least two and for every actual Haar measure. -/
theorem mixedVolume_alexandrovFenchel
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {n : ℕ}
    (hdim : finrank ℝ E = n + 2) (K : Fin n → ConvexBody E) (A B : ConvexBody E) :
    mixedVolume μ (Fin.cons A (Fin.cons A K)) *
        mixedVolume μ (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume μ (Fin.cons A (Fin.cons B K)) ^ 2 :=
  (AFBodyTuple_cons μ A B K).mp
    (alexandrovFenchelDimension n E μ hdim (Fin.cons A (Fin.cons B K)))

end VolumePolynomials
end -- closes the original EOF section from source line 22
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AlexandrovFenchel.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinaryMixedInequalities.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Necessity of all binary coefficient inequalities

Alexandrov--Fenchel gives the adjacent inequalities for the exact repeated
mixed-volume coefficients. Adding a positive multiple of the unit cube
makes every coefficient positive, with positivity proved by inclusion and
actual diagonal volume. The separated-index inequalities pass to the
Hausdorff limit, so no internal-zero assumption is imposed on a realizing
tuple.
-/

open Set MeasureTheory Module Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.BinaryMixed

open BinarySequences

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem coefficient_adjacent {n i : ℕ} (hdim : finrank ℝ E = n + 2)
    (A B : ConvexBody E) (hi : i ≤ n) :
    coefficient μ (n + 2) A B i * coefficient μ (n + 2) A B (i + 2) ≤
      coefficient μ (n + 2) A B (i + 1) ^ 2 := by
  first
  | let p := firstPattern n i
    let K := patternBody A B p
    have hAA : Fin.cons A (Fin.cons A K) = patternBody A B (Fin.cons false (Fin.cons false p)) := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [patternBody]
        | succ j =>
            cases j using Fin.cases with
            | zero => simp [patternBody]
            | succ j => rfl
    have hBB : Fin.cons B (Fin.cons B K) = patternBody A B (Fin.cons true (Fin.cons true p)) := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [patternBody]
        | succ j =>
            cases j using Fin.cases with
            | zero => simp [patternBody]
            | succ j => rfl
    have hAB : Fin.cons A (Fin.cons B K) = patternBody A B (Fin.cons false (Fin.cons true p)) := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [patternBody]
        | succ j =>
            cases j using Fin.cases with
            | zero => simp [patternBody]
            | succ j => rfl
    have h := mixedVolume_alexandrovFenchel μ hdim K A B
    rw [hAA, hBB, hAB, mixedVolume_pattern, mixedVolume_pattern, mixedVolume_pattern] at h
    simpa only [patternCount_cons, Bool.false_eq_true, if_false, if_true, zero_add,
      p, patternCount_first hi, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem coefficient_logconcave {d : ℕ} (hdim : finrank ℝ E = d)
    (A B : ConvexBody E) {i : ℕ} (hi : 1 ≤ i) (hid : i < d) :
    coefficient μ d A B (i - 1) * coefficient μ d A B (i + 1) ≤
      coefficient μ d A B i ^ 2 := by
  first
  | cases d with
    | zero => omega
    | succ d =>
        cases d with
        | zero => omega
        | succ n =>
            have h := coefficient_adjacent μ hdim A B (i := i - 1) (by omega)
            have h1 : i - 1 + 1 = i := by omega
            have h2 : i - 1 + 2 = i + 1 := by omega
            simpa only [h1, h2] using h

end Measure

def thickened {d : ℕ} (eps : ℝ) (A : Body d) : Body d := A + eps • unitCube d

theorem coefficient_pos_thickened {d : ℕ} (hd : 0 < d)
    (A B : Body d) {eps : ℝ} (heps : 0 < eps) (i : ℕ) :
    0 < coefficient volume d (thickened eps A) (thickened eps B) i := by
  first
  | cases d with
    | zero => omega
    | succ n =>
        obtain ⟨a, ha⟩ := A.nonempty
        obtain ⟨b, hb⟩ := B.nonempty
        let S : Body (n + 1) := eps • unitCube (n + 1)
        have hS : 0 < volume.real (S : Set (Space (n + 1))) := by
          first
          | change 0 < bodyVolume (eps • unitCube (n + 1))
            rw [bodyVolume_smul _ heps.le, bodyVolume_unitCube, mul_one]
            exact pow_pos heps _
        let p : Fin (n + 1) → Space (n + 1) :=
          fun j => if firstPattern (n + 1) i j = true then b else a
        apply mixedVolume_pos_of_common_body volume (by simp [Space])
          (patternBody (thickened eps A) (thickened eps B) (firstPattern (n + 1) i)) S hS p
        intro j
        by_cases hj : firstPattern (n + 1) i j = true
        · change translateBody (if firstPattern (n + 1) i j = true then b else a) S ≤ _
          rw [if_pos hj]
          simp only [patternBody, if_pos hj, thickened]
          rintro x ⟨u, hu, v, hv, rfl⟩
          have hub : u = b := hu
          subst u
          exact ⟨b, hb, v, hv, rfl⟩
        · change translateBody (if firstPattern (n + 1) i j = true then b else a) S ≤ _
          rw [if_neg hj]
          simp only [patternBody, if_neg hj, thickened]
          rintro x ⟨u, hu, v, hv, rfl⟩
          have hua : u = a := hu
          subst u
          exact ⟨a, ha, v, hv, rfl⟩

theorem thickened_criterion {d : ℕ} (hd : 0 < d) (A B : Body d)
    {eps : ℝ} (heps : 0 < eps) :
    Criterion d (coefficient volume d (thickened eps A) (thickened eps B)) := by
  first
  | apply criterion_iff.mpr
    refine ⟨fun i _ => coefficient_nonnegative volume d _ _ i, ?_, ?_⟩
    · intro i hi hid
      exact coefficient_logconcave volume (by simp [Space]) _ _ hi hid
    · intro i j k hij hjk hkd hi hk
      exact coefficient_pos_thickened hd A B heps j

theorem coefficient_thickened_tendsto (d i : ℕ) (A B : Body d) :
    Tendsto (fun eps : ℝ => coefficient volume d (thickened eps A) (thickened eps B) i)
      (𝓝[>] (0 : ℝ)) (𝓝 (coefficient volume d A B i)) := by
  first
  | have hc : Continuous (fun eps : ℝ => (thickened eps A, thickened eps B)) := by
      first
      | unfold thickened
        fun_prop
    have h := (((continuous_coefficient (volume : Measure (Space d)) d i).comp' hc).continuousAt (x := (0 : ℝ))).tendsto
    simpa only [Function.comp_def, thickened, body_zero_smul, add_zero] using h.mono_left nhdsWithin_le_nhds

/-- Every actual binary mixed-volume sequence satisfies all of (A.1),
including the separated-index inequalities at degenerate limits. -/
theorem coefficient_criterion {d : ℕ} (hd : 0 < d) (A B : Body d) :
    Criterion d (coefficient volume d A B) := by
  first
  | refine ⟨fun i _ => coefficient_nonnegative volume d A B i, ?_⟩
    intro i j hi hij hjd
    have hleft := (coefficient_thickened_tendsto d (i - 1) A B).mul
      (coefficient_thickened_tendsto d (j + 1) A B)
    have hright := (coefficient_thickened_tendsto d i A B).mul
      (coefficient_thickened_tendsto d j A B)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact (thickened_criterion hd A B heps).2 i j hi hij hjd

theorem criterion_of_realizes {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ} {A B : Body d}
    (h : BinarySimplex.Realizes d a A B) : Criterion d a := by
  first
  | have heq := realizing_sequence_eq h
    have hc := coefficient_criterion hd A B
    constructor
    · intro i hid
      rw [heq i hid]
      exact hc.1 i hid
    · intro i j hi hij hjd
      rw [heq (i - 1) (by omega), heq (j + 1) (by omega),
        heq i (by omega), heq j (by omega)]
      exact hc.2 i j hi hij hjd

end VolumePolynomials.BinaryMixed
end -- closes the original EOF section from source line 13
end -- closes the original EOF section from source line 10
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinaryMixedInequalities.lean -/

/- BEGIN SOURCE: VolumePolynomials/AxisSimplex.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Axis simplices and their literal coordinate sections

The defining body is a linear image of the coordinate simplex, hence the
convex hull of the origin and the listed axis vertices. Positive axis
lengths give an exact linear-inequality description, including a zero
dilation parameter. This is the geometric input to Appendix A.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

def diagonalMap {n : ℕ} (lam : Fin n → ℝ) : Space n →L[ℝ] Space n where
  toFun x i := lam i * x i
  map_add' x y := by ext i; simp only [Pi.add_apply, mul_add]
  map_smul' r x := by
    ext i
    change lam i * (r * x i) = r * (lam i * x i)
    ring
  cont := continuous_pi (fun i => continuous_const.mul (continuous_apply i))

@[simp] theorem diagonalMap_apply {n : ℕ} (lam : Fin n → ℝ) (x : Space n) (i : Fin n) :
    diagonalMap lam x i = lam i * x i := rfl

def axisBody {n : ℕ} (lam : Fin n → ℝ) : Body n :=
  mapBody (diagonalMap lam) (body n)

theorem zero_mem_axisBody {n : ℕ} (lam : Fin n → ℝ) :
    (0 : Space n) ∈ axisBody lam :=
  ⟨0, zero_mem_simplex n, map_zero _⟩

theorem axisBody_finiteHull {n : ℕ} (lam : Fin n → ℝ) :
    PolytopeGeometry.IsFiniteHull (axisBody lam : Set (Space n)) :=
  (simplex_finiteHull n).linear_image (diagonalMap lam).toLinearMap

theorem axisBody_one (n : ℕ) : axisBody (fun _ : Fin n => 1) = body n := by
  first
  | apply ConvexBody.ext
    change diagonalMap (fun _ : Fin n => (1 : ℝ)) '' simplex n = simplex n
    have heq : (diagonalMap (fun _ : Fin n => (1 : ℝ)) : Space n → Space n) = id := by
      first
      | funext x i
        simp [diagonalMap]
    rw [heq, Set.image_id]

theorem axisBody_scalar {n : ℕ} (lam : Fin n → ℝ) (r : ℝ) :
    axisBody (fun i => r * lam i) = r • axisBody lam := by
  first
  | apply ConvexBody.ext
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨diagonalMap lam y, ⟨y, hy, rfl⟩, ?_⟩
      ext i
      simp [diagonalMap, mul_assoc]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      ext i
      simp [diagonalMap, mul_assoc]

theorem mem_axisBody_iff {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) (x : Space n) :
    x ∈ axisBody lam ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i / lam i ≤ 1 := by
  first
  | constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun i => mul_nonneg (hlam i).le (hy.1 i), ?_⟩
      have heq (i : Fin n) : diagonalMap lam y i / lam i = y i := by
        first
        | dsimp only [diagonalMap]
          exact mul_div_cancel_left₀ _ (hlam i).ne'
      simpa only [heq] using hy.2
    · rintro ⟨hx, hs⟩
      refine ⟨fun i => x i / lam i,
        ⟨fun i => div_nonneg (hx i) (hlam i).le, hs⟩, ?_⟩
      ext i
      exact mul_div_cancel₀ _ (hlam i).ne'

theorem mem_smul_axisBody_iff {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) (x : Space n) :
    x ∈ t • axisBody lam ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i / lam i ≤ t := by
  first
  | constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' := (mem_axisBody_iff hlam y).mp hy
      refine ⟨fun i => mul_nonneg ht (hy'.1 i), ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, ← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left hy'.2 ht).trans_eq (mul_one t)
    · rintro ⟨hx, hs⟩
      by_cases ht0 : t = 0
      · have hx0 : x = 0 := by
          first
          | ext i
            change x i = 0
            have hsum : x i / lam i ≤ ∑ j, x j / lam j :=
              Finset.single_le_sum (fun j _ => div_nonneg (hx j) (hlam j).le)
                (Finset.mem_univ i)
            have hdiv : x i / lam i ≤ 0 := hsum.trans (ht0 ▸ hs)
            exact le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ (hlam i)).mp hdiv) (hx i)
        rw [ht0, hx0, body_zero_smul]
        rfl
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        refine ⟨t⁻¹ • x, (mem_axisBody_iff hlam _).mpr ⟨?_, ?_⟩, ?_⟩
        · intro i
          exact mul_nonneg (inv_nonneg.mpr ht) (hx i)
        · simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, ← Finset.mul_sum]
          rw [← div_eq_inv_mul]
          exact (div_le_one htpos).mpr hs
        · change t • (t⁻¹ • x) = x
          rw [smul_smul, mul_inv_cancel₀ ht0, one_smul]

theorem coordinate_nonnegative {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) {x : Space n}
    (hx : x ∈ t • axisBody lam) (i : Fin n) : 0 ≤ x i :=
  ((mem_smul_axisBody_iff hlam ht x).mp hx).1 i

theorem coordinate_upper_bound {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) {x : Space n}
    (hx : x ∈ t • axisBody lam) (i : Fin n) : x i ≤ t * lam i := by
  first
  | have hx' := (mem_smul_axisBody_iff hlam ht x).mp hx
    have h : x i / lam i ≤ t :=
      (Finset.single_le_sum (fun j _ => div_nonneg (hx'.1 j) (hlam j).le)
        (Finset.mem_univ i)).trans hx'.2
    exact (div_le_iff₀ (hlam i)).mp h

/-- A section at the first coordinate, before any Minkowski summation. -/
theorem section_smul_axisBody {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) {t z : ℝ} (ht : 0 ≤ t)
    (hz0 : 0 ≤ z) (hzt : z ≤ t * lam 0) :
    {x : Space n | Fin.cons z x ∈ t • axisBody lam} =
      (t - z / lam 0) • (axisBody (Fin.tail lam) : Set (Space n)) := by
  first
  | have hr : 0 ≤ t - z / lam 0 :=
      sub_nonneg.mpr ((div_le_iff₀ (hlam 0)).mpr hzt)
    ext x
    rw [Set.mem_setOf_eq, mem_smul_axisBody_iff hlam ht,
      show x ∈ (t - z / lam 0) • (axisBody (Fin.tail lam) : Set (Space n)) ↔
        x ∈ (t - z / lam 0) • axisBody (Fin.tail lam) from Iff.rfl,
      mem_smul_axisBody_iff (lam := Fin.tail lam) (fun i => hlam i.succ) hr x]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ,
      Fin.tail_def]
    constructor
    · rintro ⟨⟨_, hx⟩, hs⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hs⟩
      exact ⟨⟨hz0, hx⟩, by linarith⟩

theorem scaled_simplex_subset_axisBody {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) {r : ℝ} (hr : 0 ≤ r) (hle : ∀ i, r ≤ lam i) :
    r • body n ≤ axisBody lam := by
  first
  | rintro _ ⟨x, hx, rfl⟩
    apply (mem_axisBody_iff hlam _).mpr
    refine ⟨fun i => mul_nonneg hr (hx.1 i), ?_⟩
    apply (Finset.sum_le_sum (fun i _ => ?_)).trans hx.2
    change r * x i / lam i ≤ x i
    apply (div_le_iff₀ (hlam i)).mpr
    nlinarith [mul_le_mul_of_nonneg_right (hle i) (hx.1 i)]

theorem diagonal_dist_le {n : ℕ} (lam mu : Fin n → ℝ)
    {x : Space n} (hx : x ∈ simplex n) :
    dist (diagonalMap lam x) (diagonalMap mu x) ≤ dist lam mu := by
  first
  | apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    have hxi := (simplex_subset_unit_box n hx).2 i
    have habs : |x i| ≤ 1 := by rwa [abs_of_nonneg (hx.1 i)]
    calc
      dist (diagonalMap lam x i) (diagonalMap mu x i) =
          |lam i - mu i| * |x i| := by
        first
        | rw [Real.dist_eq]
          change |lam i * x i - mu i * x i| = |lam i - mu i| * |x i|
          rw [← sub_mul, abs_mul]
      _ ≤ |lam i - mu i| := by
        first
        | simpa only [mul_one] using mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ ≤ dist lam mu := by simpa only [Real.dist_eq] using dist_le_pi_dist lam mu i

theorem axisBody_dist_le {n : ℕ} (lam mu : Fin n → ℝ) :
    dist (axisBody lam) (axisBody mu) ≤ dist lam mu := by
  first
  | rw [← ConvexBody.hausdorffDist_coe]
    apply Metric.hausdorffDist_le_of_mem_dist dist_nonneg
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨diagonalMap mu x, ⟨x, hx, rfl⟩, diagonal_dist_le lam mu hx⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨diagonalMap lam x, ⟨x, hx, rfl⟩, by
        simpa only [dist_comm mu lam] using diagonal_dist_le mu lam hx⟩

theorem continuous_axisBody (n : ℕ) : Continuous (axisBody (n := n)) := by
  first
  | have h : LipschitzWith 1 (axisBody (n := n)) :=
      LipschitzWith.of_dist_le_mul (fun lam mu => by
        simpa only [NNReal.coe_one, one_mul] using axisBody_dist_le lam mu)
    exact h.continuous

end VolumePolynomials.AxisSimplex
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AxisSimplex.lean -/

/- BEGIN SOURCE: VolumePolynomials/AxisSimplexSections.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Sections of a sum of two ordered axis simplices

When the first axis of the second simplex is its shortest, a section of
`t Δ + s Λ` allocates as much first-coordinate height as possible to Δ.
The proof is a literal set equality. Moving height from Λ to Δ enlarges
the remaining section because the shortest-axis multiple of Δ is
contained in the tail simplex.
-/

open Set
open scoped Pointwise BigOperators

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

theorem add_body_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C D : ConvexBody E} (hAB : A ≤ B) (hCD : C ≤ D) : A + C ≤ B + D := by
  first
  | rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hAB hx, y, hCD hy, rfl⟩

theorem smul_body_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : ConvexBody E} (hAB : A ≤ B) (r : ℝ) : r • A ≤ r • B := by
  first
  | rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hAB hx, rfl⟩

theorem transfer_summand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : ConvexBody E) {c : ℝ} (hc : 0 < c) (hPQ : c • P ≤ Q)
    {a b δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδb : δ / c ≤ b) :
    (a + δ) • P + (b - δ / c) • Q ≤ a • P + b • Q := by
  first
  | have hd : 0 ≤ δ / c := div_nonneg hδ hc.le
    have hrest : 0 ≤ b - δ / c := sub_nonneg.mpr hδb
    have hdelta : δ • P ≤ (δ / c) • Q := by
      first
      | have heq : δ • P = (δ / c) • (c • P) := by
          rw [smul_smul, div_mul_cancel₀ δ hc.ne']
        rw [heq]
        exact smul_body_mono hPQ _
    calc
      (a + δ) • P + (b - δ / c) • Q =
          (a • P + δ • P) + (b - δ / c) • Q := by rw [body_add_smul P ha hδ]
      _ ≤ (a • P + (δ / c) • Q) + (b - δ / c) • Q :=
        add_body_mono (add_body_mono le_rfl hdelta) le_rfl
      _ = a • P + b • Q := by
        first
        | rw [add_assoc, ← body_add_smul Q hd hrest]
          congr 2
          ring

def firstSection {n : ℕ} (K : Body (n + 1)) (z : ℝ) : Set (Space n) :=
  {x | Fin.cons z x ∈ K}

theorem firstSection_sum_support {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hne : (firstSection (t • body (n + 1) + s • axisBody lam) z).Nonempty) :
    0 ≤ z ∧ z ≤ t + s * lam 0 := by
  first
  | obtain ⟨x, u, hu, v, hv, heq⟩ := hne
    have hu' : u ∈ t • axisBody (fun _ : Fin (n + 1) => 1) := by
      first
      | rwa [axisBody_one]
    have h0 : u 0 + v 0 = z := congrArg (fun w : Space (n + 1) => w 0) heq
    have hu0 := coordinate_nonnegative (fun _ => zero_lt_one) ht hu' 0
    have hv0 := coordinate_nonnegative hlam hs hv 0
    have hut := coordinate_upper_bound (fun _ => zero_lt_one) ht hu' 0
    have hvs := coordinate_upper_bound hlam hs hv 0
    constructor <;> nlinarith

theorem firstSection_sum_empty {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hz : z ∉ Icc (0 : ℝ) (t + s * lam 0)) :
    firstSection (t • body (n + 1) + s • axisBody lam) z = ∅ := by
  first
  | apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    exact hz (firstSection_sum_support hlam ht hs hne)

theorem firstSection_sum_lower {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ)
    {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hz0 : 0 ≤ z) (hzt : z ≤ t) :
    firstSection (t • body (n + 1) + s • axisBody lam) z =
      ((t - z) • body n + s • axisBody (Fin.tail lam) : Body n) := by
  first
  | have hcontain : lam 0 • body n ≤ axisBody (Fin.tail lam) :=
      scaled_simplex_subset_axisBody (fun i => hlam i.succ) (hlam 0).le hmin
    ext x
    constructor
    · rintro ⟨u, hu, v, hv, heq⟩
      have hu' : u ∈ t • axisBody (fun _ : Fin (n + 1) => 1) := by
        first
        | rwa [axisBody_one]
      have hu0 := coordinate_nonnegative (fun _ => zero_lt_one) ht hu' 0
      have hv0 := coordinate_nonnegative hlam hs hv 0
      have hut : u 0 ≤ t := by
        first
        | simpa only [mul_one] using coordinate_upper_bound (fun _ => zero_lt_one) ht hu' 0
      have hvs := coordinate_upper_bound hlam hs hv 0
      have h0 : u 0 + v 0 = z := congrArg (fun w : Space (n + 1) => w 0) heq
      have htail : Fin.tail u + Fin.tail v = x := by
        first
        | funext i
          exact congrArg (fun w : Space (n + 1) => w i.succ) heq
      have husection : Fin.tail u ∈ (t - u 0) • body n := by
        first
        | have h := Set.ext_iff.mp (section_smul_axisBody (fun _ => zero_lt_one) ht hu0
            (by simpa only [mul_one] using hut)) (Fin.tail u)
          have hone : Fin.tail (fun _ : Fin (n + 1) => (1 : ℝ)) =
              (fun _ : Fin n => (1 : ℝ)) := rfl
          simp only [hone, axisBody_one, div_one, Set.mem_setOf_eq,
            ← ConvexBody.coe_smul] at h
          apply Iff.mp h
          simpa only [axisBody_one, Fin.cons_self_tail] using hu'
      have hvsection : Fin.tail v ∈ (s - v 0 / lam 0) • axisBody (Fin.tail lam) := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs hv0 hvs) (Fin.tail v)).mp
          change Fin.cons (v 0) (Fin.tail v) ∈
            ((s • axisBody lam : Body (n + 1)) : Set (Space (n + 1)))
          rw [Fin.cons_self_tail]
          exact hv
      have htransfer := transfer_summand (body n) (axisBody (Fin.tail lam))
        (hlam 0) hcontain (sub_nonneg.mpr hzt) hv0
        ((div_le_iff₀ (hlam 0)).mpr hvs)
      have harith : (t - z) + v 0 = t - u 0 := by linarith
      rw [harith] at htransfer
      exact htransfer ⟨Fin.tail u, husection, Fin.tail v, hvsection, htail⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      have hu' : Fin.cons z u ∈ t • body (n + 1) := by
        first
        | have h := Set.ext_iff.mp (section_smul_axisBody (fun _ : Fin (n + 1) => zero_lt_one)
            ht hz0 (by simpa only [mul_one] using hzt)) u
          have hone : Fin.tail (fun _ : Fin (n + 1) => (1 : ℝ)) =
              (fun _ : Fin n => (1 : ℝ)) := rfl
          simp only [hone, axisBody_one, div_one, Set.mem_setOf_eq,
            ← ConvexBody.coe_smul] at h
          apply Iff.mpr h
          change u ∈ (t - z) • body n
          exact hu
      have hv' : Fin.cons 0 v ∈ s • axisBody lam := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs le_rfl
            (mul_nonneg hs (hlam 0).le)) v).mpr
          simp only [zero_div, sub_zero]
          change v ∈ s • axisBody (Fin.tail lam)
          exact hv
      refine ⟨Fin.cons z u, hu', Fin.cons 0 v, hv', ?_⟩
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ i => exact congrFun huv i

theorem firstSection_sum_upper {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ)
    {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (htz : t ≤ z)
    (hzs : z ≤ t + s * lam 0) :
    firstSection (t • body (n + 1) + s • axisBody lam) z =
      (s - (z - t) / lam 0) • (axisBody (Fin.tail lam) : Set (Space n)) := by
  first
  | have hcontain : lam 0 • body n ≤ axisBody (Fin.tail lam) :=
      scaled_simplex_subset_axisBody (fun i => hlam i.succ) (hlam 0).le hmin
    have hr : 0 ≤ s - (z - t) / lam 0 :=
      sub_nonneg.mpr ((div_le_iff₀ (hlam 0)).mpr (by linarith))
    ext x
    constructor
    · rintro ⟨u, hu, v, hv, heq⟩
      have hu' : u ∈ t • axisBody (fun _ : Fin (n + 1) => 1) := by
        first
        | rwa [axisBody_one]
      have hu0 := coordinate_nonnegative (fun _ => zero_lt_one) ht hu' 0
      have hv0 := coordinate_nonnegative hlam hs hv 0
      have hut : u 0 ≤ t := by
        first
        | simpa only [mul_one] using coordinate_upper_bound (fun _ => zero_lt_one) ht hu' 0
      have hvs := coordinate_upper_bound hlam hs hv 0
      have h0 : u 0 + v 0 = z := congrArg (fun w : Space (n + 1) => w 0) heq
      have htail : Fin.tail u + Fin.tail v = x := by
        first
        | funext i
          exact congrArg (fun w : Space (n + 1) => w i.succ) heq
      have husection : Fin.tail u ∈ (t - u 0) • body n := by
        first
        | have h := Set.ext_iff.mp (section_smul_axisBody (fun _ => zero_lt_one) ht hu0
            (by simpa only [mul_one] using hut)) (Fin.tail u)
          have hone : Fin.tail (fun _ : Fin (n + 1) => (1 : ℝ)) =
              (fun _ : Fin n => (1 : ℝ)) := rfl
          simp only [hone, axisBody_one, div_one, Set.mem_setOf_eq,
            ← ConvexBody.coe_smul] at h
          apply Iff.mp h
          simpa only [axisBody_one, Fin.cons_self_tail] using hu'
      have hvsection : Fin.tail v ∈ (s - v 0 / lam 0) • axisBody (Fin.tail lam) := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs hv0 hvs) (Fin.tail v)).mp
          change Fin.cons (v 0) (Fin.tail v) ∈
            ((s • axisBody lam : Body (n + 1)) : Set (Space (n + 1)))
          rw [Fin.cons_self_tail]
          exact hv
      have hδb : (t - u 0) / lam 0 ≤ s - (z - t) / lam 0 := by
        first
        | have hvs' := (div_le_iff₀ (hlam 0)).mpr hvs
          have hid : (t - u 0) / lam 0 + (z - t) / lam 0 = v 0 / lam 0 := by
            rw [← add_div]
            congr 1
            linarith
          linarith
      have htransfer := transfer_summand (body n) (axisBody (Fin.tail lam))
        (hlam 0) hcontain (a := 0) le_rfl (sub_nonneg.mpr hut) hδb
      have harith : s - (z - t) / lam 0 - (t - u 0) / lam 0 = s - v 0 / lam 0 := by
        first
        | rw [sub_sub, ← add_div]
          congr 2
          linarith
      simp only [zero_add, body_zero_smul, harith] at htransfer
      exact htransfer ⟨Fin.tail u, husection, Fin.tail v, hvsection, htail⟩
    · intro hx
      have hu : Fin.cons t (0 : Space n) ∈ t • body (n + 1) := by
        first
        | refine ⟨Pi.single (0 : Fin (n + 1)) 1, coordinate_mem_simplex 0, ?_⟩
          funext i
          cases i using Fin.cases <;> simp [Pi.single_apply]
      have hv : Fin.cons (z - t) x ∈ s • axisBody lam := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs (sub_nonneg.mpr htz)
            (by linarith)) x).mpr
          exact hx
      refine ⟨Fin.cons t 0, hu, Fin.cons (z - t) x, hv, ?_⟩
      funext i
      cases i using Fin.cases <;> simp

end VolumePolynomials.AxisSimplex
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AxisSimplexSections.lean -/

/- BEGIN SOURCE: VolumePolynomials/AxisSimplexVolume.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Actual volume recurrence for ordered axis simplices

The coordinate splitting is the measure-preserving equivalence already
proved for product Lebesgue measure. Fubini and the exact section identities
give the recurrence in Appendix A, including zero Minkowski coefficients.
The axis lengths are strictly positive here; the final polynomial identity
extends to nonnegative lengths by Hausdorff continuity.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

theorem firstSection_measurable {n : ℕ} (K : Body (n + 1)) (z : ℝ) :
    MeasurableSet (firstSection K z) := by
  first
  | have hc : Continuous (fun x : Space n => (Fin.cons z x : Space (n + 1))) := by
      first
      | apply continuous_pi
        intro i
        cases i using Fin.cases with
        | zero => exact continuous_const
        | succ i => exact continuous_apply i
    exact K.isCompact.measurableSet.preimage hc.measurable

/-- Both the integrability assertion and the equality concern the actual
Lebesgue volumes of the coordinate sections. -/
theorem firstSection_fubini {n : ℕ} (K : Body (n + 1)) :
    Integrable (fun z : ℝ => volume.real (firstSection K z)) ∧
      bodyVolume K = ∫ z : ℝ, volume.real (firstSection K z) := by
  first
  | let e : ℝ × Space n ≃ᵐ Space (n + 1) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have he : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
    have he_apply (z : ℝ) (x : Space n) : e (z, x) = (Fin.cons z x : Space (n + 1)) := by
      first
      | change Fin.insertNth 0 z x = (Fin.cons z x : Space (n + 1))
        exact Fin.insertNth_zero' z x
    let f : Space (n + 1) → ℝ := (K : Set (Space (n + 1))).indicator (fun _ => 1)
    have hf : Integrable f :=
      (integrableOn_const K.isCompact.measure_ne_top).integrable_indicator
        K.isCompact.measurableSet
    have hfe : Integrable (f ∘ e) ((volume : Measure ℝ).prod (volume : Measure (Space n))) := by
      first
      | simpa only [← Measure.volume_eq_prod] using he.integrable_comp_of_integrable hf
    have hinner (z : ℝ) : (∫ x : Space n, f (e (z, x))) =
        volume.real (firstSection K z) := by
      first
      | simp only [he_apply]
        change (∫ x : Space n, (firstSection K z).indicator (fun _ => (1 : ℝ)) x) = _
        rw [integral_indicator (firstSection_measurable K z), setIntegral_const]
        simp only [smul_eq_mul, mul_one]
    have htotal : (∫ x : Space (n + 1), f x) = bodyVolume K := by
      first
      | rw [integral_indicator K.isCompact.measurableSet, setIntegral_const]
        simp only [smul_eq_mul, mul_one, bodyVolume]
    constructor
    · simpa only [Function.comp_apply, hinner] using hfe.integral_prod_left
    · have hp := integral_prod (f ∘ e) hfe
      rw [← Measure.volume_eq_prod] at hp
      simpa only [Function.comp_apply, he.integral_comp' f, htotal, hinner] using hp

theorem integral_upper_section_power (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (t s : ℝ) :
    (∫ z in t..t + s * lam, (s - (z - t) / lam) ^ n) =
      lam * s ^ (n + 1) / (n + 1) := by
  first
  | have hshift := intervalIntegral.integral_comp_sub_right
      (fun w : ℝ => (s - w / lam) ^ n) t (a := t) (b := t + s * lam)
    simp only [sub_self, add_sub_cancel_left] at hshift
    rw [hshift, intervalIntegral.integral_comp_sub_div (fun w : ℝ => w ^ n) hlam.ne' s]
    have hcancel : s * lam / lam = s := mul_div_cancel_right₀ s hlam.ne'
    rw [hcancel, zero_div, sub_zero, sub_self, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, smul_eq_mul]
    ring

/-- The recurrence obtained from the actual sections, with the shortest
axis listed first. -/
theorem volume_sum_recurrence {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body (n + 1) + s • axisBody lam) =
      (∫ u in 0..t, bodyVolume (u • body n + s • axisBody (Fin.tail lam))) +
        lam 0 * s ^ (n + 1) / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
  first
  | let K : Body (n + 1) := t • body (n + 1) + s • axisBody lam
    let f : ℝ → ℝ := fun z => volume.real (firstSection K z)
    have hf : Integrable f := (firstSection_fubini K).1
    have htop : t ≤ t + s * lam 0 := le_add_of_nonneg_right (mul_nonneg hs (hlam 0).le)
    have hsupport : ∀ z, z ∉ Icc (0 : ℝ) (t + s * lam 0) → f z = 0 := by
      first
      | intro z hz
        dsimp only [f, K]
        rw [firstSection_sum_empty hlam ht hs hz, measureReal_empty]
    have hwhole : bodyVolume K = ∫ z in 0..t + s * lam 0, f z := by
      first
      | rw [(firstSection_fubini K).2]
        change (∫ z, f z) = _
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,
          integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (ht.trans htop)]
    have hlower : (∫ z in 0..t, f z) =
        ∫ u in 0..t, bodyVolume (u • body n + s • axisBody (Fin.tail lam)) := by
      first
      | calc
          (∫ z in 0..t, f z) = ∫ z in 0..t,
              bodyVolume ((t - z) • body n + s • axisBody (Fin.tail lam)) := by
            apply intervalIntegral.integral_congr_Ioo_of_le ht
            intro z hz
            dsimp only [f, K]
            rw [firstSection_sum_lower hlam hmin ht hs hz.1.le hz.2.le]
            rfl
          _ = _ := by
            simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left
              (fun u : ℝ => bodyVolume (u • body n + s • axisBody (Fin.tail lam)))
              t (a := 0) (b := t)
    have hupper : (∫ z in t..t + s * lam 0, f z) =
        lam 0 * s ^ (n + 1) / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
      first
      | calc
          (∫ z in t..t + s * lam 0, f z) =
              ∫ z in t..t + s * lam 0,
                (s - (z - t) / lam 0) ^ n * bodyVolume (axisBody (Fin.tail lam)) := by
            apply intervalIntegral.integral_congr_Ioo_of_le htop
            intro z hz
            dsimp only [f, K]
            rw [firstSection_sum_upper hlam hmin ht hs hz.1.le hz.2.le]
            change bodyVolume ((s - (z - t) / lam 0) • axisBody (Fin.tail lam)) = _
            apply bodyVolume_smul
            apply sub_nonneg.mpr
            apply (div_le_iff₀ (hlam 0)).mpr
            linarith [hz.2]
          _ = _ := by rw [intervalIntegral.integral_mul_const, integral_upper_section_power n (hlam 0)]
    change bodyVolume K = _
    rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (a := 0) (b := t))
      (hf.intervalIntegrable (a := t) (b := t + s * lam 0)), hlower, hupper]

theorem simplex_volume_zero : bodyVolume (body 0) = 1 := by
  first
  | have heq : simplex 0 = Icc (0 : Space 0) (fun _ => 1) := by
      first
      | ext x
        simp [simplex, Pi.le_def]
    change volume.real (simplex 0) = 1
    rw [heq]
    simp [measureReal_def, Real.volume_Icc_pi]

theorem simplex_volume (n : ℕ) : bodyVolume (body n) = 1 / (n.factorial : ℝ) := by
  first
  | induction n with
    | zero => simpa only [Nat.factorial_zero, Nat.cast_one, div_one] using simplex_volume_zero
    | succ n ih =>
        have hrec := volume_sum_recurrence (fun _ : Fin (n + 1) => zero_lt_one)
          (fun _ => le_rfl) (t := 1) (s := 0) zero_le_one le_rfl
        simp only [one_smul, body_zero_smul, add_zero,
          zero_pow (Nat.succ_ne_zero n), mul_zero, zero_div, zero_mul] at hrec
        rw [hrec]
        have hfn : (∫ u in (0 : ℝ)..1, bodyVolume (u • body n)) =
            ∫ u in (0 : ℝ)..1, u ^ n * bodyVolume (body n) := by
          first
          | apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
            intro u hu
            exact bodyVolume_smul _ hu.1.le
        rw [hfn, intervalIntegral.integral_mul_const, integral_pow, ih,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, one_div, ← mul_inv]

theorem det_diagonalMap {n : ℕ} (lam : Fin n → ℝ) :
    LinearMap.det (diagonalMap lam).toLinearMap = ∏ i, lam i := by
  first
  | rw [← LinearMap.det_toMatrix']
    have hm : LinearMap.toMatrix' (diagonalMap lam).toLinearMap = Matrix.diagonal lam := by
      first
      | ext i j
        simp [LinearMap.toMatrix'_apply, diagonalMap, Matrix.diagonal_apply, Pi.single_apply]
    rw [hm, Matrix.det_diagonal]

theorem axisBody_volume {n : ℕ} (lam : Fin n → ℝ) :
    bodyVolume (axisBody lam) = |∏ i, lam i| / (n.factorial : ℝ) := by
  first
  | rw [axisBody, bodyVolume_map, det_diagonalMap, simplex_volume]
    ring

end VolumePolynomials.AxisSimplex
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AxisSimplexVolume.lean -/

/- BEGIN SOURCE: VolumePolynomials/AxisSimplexPolynomial.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The complete two-simplex volume formula

Axes are ordered increasingly, so the product in the coefficient of
`t^(n-i) s^i` is the product of the final `i` axes. This is exactly (A.2)
after reversing the coordinate order. All nonnegative axes are included.
-/

open Set MeasureTheory Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

def upperProduct {n : ℕ} (lam : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => n - i ≤ j.val), lam j

def orderedCoefficient {n : ℕ} (lam : Fin n → ℝ) (i : ℕ) : ℝ :=
  upperProduct lam i / ((n - i).factorial * i.factorial : ℕ)

def orderedValue {n : ℕ} (lam : Fin n → ℝ) (t s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), orderedCoefficient lam i * t ^ (n - i) * s ^ i

theorem upperProduct_top {n : ℕ} (lam : Fin n → ℝ) :
    upperProduct lam n = ∏ j, lam j := by
  first
  | simp [upperProduct]

theorem upperProduct_zero {n : ℕ} (lam : Fin n → ℝ) : upperProduct lam 0 = 1 := by
  first
  | have hempty : Finset.univ.filter (fun j : Fin n => n - 0 ≤ j.val) = ∅ := by
      first
      | apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have h := (Finset.mem_filter.mp hj).2
        omega
    simp only [upperProduct, hempty, Finset.prod_empty]

theorem upperProduct_tail {n i : ℕ} (lam : Fin (n + 1) → ℝ) (hi : i ≤ n) :
    upperProduct lam i = upperProduct (Fin.tail lam) i := by
  first
  | simp only [upperProduct, Finset.prod_filter, Fin.prod_univ_succ]
    have hzero : ¬n + 1 - i ≤ (0 : Fin (n + 1)).val := by simp only [Fin.val_zero]; omega
    rw [if_neg hzero, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    have htest : n + 1 - i ≤ j.succ.val ↔ n - i ≤ j.val := by
      first
      | simp only [Fin.val_succ]
        omega
    simp only [htest, Fin.tail_def]

theorem orderedCoefficient_succ {n i : ℕ} (lam : Fin (n + 1) → ℝ) (hi : i ≤ n) :
    orderedCoefficient lam i = orderedCoefficient (Fin.tail lam) i / (n - i + 1) := by
  first
  | have hsub : n + 1 - i = (n - i) + 1 := by omega
    simp only [orderedCoefficient, upperProduct_tail lam hi, hsub,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub hi, div_eq_mul_inv, mul_inv_rev]
    ring

theorem orderedCoefficient_top {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) :
    orderedCoefficient lam (n + 1) =
      lam 0 / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
  first
  | rw [orderedCoefficient, upperProduct_top, Fin.prod_univ_succ, axisBody_volume]
    rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => hlam i.succ))]
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.one_mul, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Fin.tail_def, div_eq_mul_inv, mul_inv_rev]
    ring

theorem orderedValue_zero (lam : Fin 0 → ℝ) (t s : ℝ) : orderedValue lam t s = 1 := by
  first
  | simp [orderedValue, orderedCoefficient, upperProduct_zero]

theorem integral_orderedValue_tail {n : ℕ} (lam : Fin (n + 1) → ℝ) (t s : ℝ) :
    (∫ u in 0..t, orderedValue (Fin.tail lam) u s) =
      ∑ i ∈ Finset.range (n + 1), orderedCoefficient lam i * t ^ (n + 1 - i) * s ^ i := by
  first
  | unfold orderedValue
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_pow]
      have hsub : n + 1 - i = (n - i) + 1 := by omega
      rw [hsub, orderedCoefficient_succ lam hin]
      simp only [zero_pow (Nat.succ_ne_zero (n - i)), sub_zero, Nat.cast_sub hin]
      ring
    · intro i _
      exact ((continuous_const.mul (continuous_id.pow (n - i))).mul continuous_const).intervalIntegrable _ _

theorem orderedValue_recurrence {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (t s : ℝ) :
    orderedValue lam t s =
      (∫ u in 0..t, orderedValue (Fin.tail lam) u s) +
        lam 0 * s ^ (n + 1) / (n + 1) * bodyVolume (axisBody (Fin.tail lam)) := by
  first
  | rw [integral_orderedValue_tail]
    unfold orderedValue
    rw [Finset.sum_range_succ]
    congr 1
    rw [orderedCoefficient_top hlam]
    simp only [Nat.sub_self, pow_zero, mul_one]
    ring

theorem volume_sum_positive {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmono : Monotone lam)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body n + s • axisBody lam) = orderedValue lam t s := by
  first
  | induction n generalizing t s with
    | zero =>
        have hbody : t • body 0 + s • axisBody lam = body 0 := by
          first
          | apply ConvexBody.ext
            ext x
            constructor
            · intro _
              simp [SimplexCoordinates.body, simplex]
            · intro _
              obtain ⟨y, hy⟩ := (t • body 0 + s • axisBody lam).nonempty
              simpa only [Subsingleton.elim y x] using hy
        rw [hbody, simplex_volume_zero, orderedValue_zero]
    | succ n ih =>
        have hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ := fun i => hmono (Fin.zero_le _)
        rw [volume_sum_recurrence hlam hmin ht hs, orderedValue_recurrence (fun i => (hlam i).le)]
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le ht
        intro u hu
        exact ih (fun i => hlam i.succ) (fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij))
          hu.1.le hs

theorem continuous_upperProduct (n i : ℕ) : Continuous (fun lam : Fin n → ℝ => upperProduct lam i) := by
  first
  | unfold upperProduct
    fun_prop

theorem continuous_orderedValue (n : ℕ) (t s : ℝ) :
    Continuous (fun lam : Fin n → ℝ => orderedValue lam t s) := by
  first
  | unfold orderedValue orderedCoefficient
    apply continuous_finsetSum
    intro i _
    exact (((continuous_upperProduct n i).div_const _).mul continuous_const).mul continuous_const

set_option maxHeartbeats 1000000 in
/-- Formula (A.2), including zero axis lengths. -/
theorem volume_sum {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hmono : Monotone lam)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body n + s • axisBody lam) = orderedValue lam t s := by
  first
  | let axes : ℝ → Fin n → ℝ := fun eps i => lam i + eps
    have hcaxes : Continuous axes := continuous_pi (fun i => continuous_const.add continuous_id)
    have hleft : Tendsto (fun eps : ℝ => bodyVolume (t • body n + s • axisBody (axes eps)))
        (𝓝[>] (0 : ℝ)) (𝓝 (bodyVolume (t • body n + s • axisBody lam))) := by
      first
      | have hK : Continuous (fun eps : ℝ => axisBody (axes eps)) :=
          (continuous_axisBody n).comp hcaxes
        have hsum : Continuous (fun eps : ℝ => t • body n + s • axisBody (axes eps)) :=
          continuous_const.fun_add (hK.fun_const_smul s)
        have hc : Continuous (fun eps : ℝ => bodyVolume (t • body n + s • axisBody (axes eps))) :=
          (continuous_bodyVolume n).comp hsum
        simpa only [axes, add_zero] using
          (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hright : Tendsto (fun eps : ℝ => orderedValue (axes eps) t s)
        (𝓝[>] (0 : ℝ)) (𝓝 (orderedValue lam t s)) := by
      first
      | simpa only [Function.comp_def, axes, add_zero] using
          (((continuous_orderedValue n t s).comp' hcaxes).continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun eps : ℝ => bodyVolume (t • body n + s • axisBody (axes eps)))
        =ᶠ[𝓝[>] (0 : ℝ)] fun eps => orderedValue (axes eps) t s := by
      first
      | filter_upwards [self_mem_nhdsWithin] with eps heps
        exact volume_sum_positive (fun i => add_pos_of_nonneg_of_pos (hlam i) heps)
          (fun i j hij => by
            change lam i + eps ≤ lam j + eps
            linarith [hmono hij]) ht hs
    exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

theorem orderedCoefficient_eq_choose {n i : ℕ} (lam : Fin n → ℝ) (hi : i ≤ n) :
    orderedCoefficient lam i =
      1 / (n.factorial : ℝ) * (n.choose i : ℝ) * upperProduct lam i := by
  first
  | have hchoose : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) =
        (n.factorial : ℝ) := by
      first
      | exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have h0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have h1 : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have h2 : ((n - i).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - i)
    unfold orderedCoefficient
    push_cast
    field_simp
    nlinarith [congrArg (fun q : ℝ => q * upperProduct lam i) hchoose]

theorem volume_sum_choose {n : ℕ} {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hmono : Monotone lam)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    bodyVolume (t • body n + s • axisBody lam) =
      1 / (n.factorial : ℝ) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * upperProduct lam i * t ^ (n - i) * s ^ i := by
  first
  | rw [volume_sum hlam hmono ht hs, orderedValue, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [orderedCoefficient_eq_choose lam (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    ring

end VolumePolynomials.AxisSimplex
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/AxisSimplexPolynomial.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinarySimplexRealization.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Realization from ordered positive ratios

The volume identity retains the binomial normalization used in Appendix A.
Both realizing bodies are literal diagonal images of the coordinate simplex.
The diagonal factors may differ by coordinate; this form also supports the
degenerate limiting construction without fractional powers of its parameter.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.BinarySimplex

open AxisSimplex SimplexCoordinates BinarySequences

def DecreasingRatios (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ i j : ℕ, i ≤ j → j < d → a (j + 1) / a j ≤ a (i + 1) / a i

def ratioAxes (d : ℕ) (a : ℕ → ℝ) (j : Fin d) : ℝ :=
  a (d - j.val) / a (d - j.val - 1)

theorem decreasingRatios_of_criterion {d : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) (hc : Criterion d a) : DecreasingRatios d a := by
  first
  | intro i j hij hjd
    exact ratios_antitone_on_interval (l := 0) (r := d)
      (fun k _ hkd => ha k hkd)
      (fun k hk hkd => by simpa only [pow_two] using hc.adjacent hk hkd)
      i j (Nat.zero_le _) hij hjd

theorem ratioAxes_pos {d : ℕ} {a : ℕ → ℝ} (ha : ∀ i ≤ d, 0 < a i) :
    ∀ j : Fin d, 0 < ratioAxes d a j := by
  first
  | intro j
    exact div_pos (ha _ (Nat.sub_le _ _)) (ha _ (by omega))

theorem ratioAxes_monotone {d : ℕ} {a : ℕ → ℝ} (hr : DecreasingRatios d a) :
    Monotone (ratioAxes d a) := by
  first
  | intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hval : i.val ≤ j.val := hij
    have h := hr (d - j.val - 1) (d - i.val - 1) (by omega) (by omega)
    have hei : d - i.val - 1 + 1 = d - i.val := by omega
    have hej : d - j.val - 1 + 1 = d - j.val := by omega
    simpa only [hei, hej, ratioAxes] using h

theorem upperProduct_succ {d i : ℕ} (lam : Fin d → ℝ) (hi : i < d) :
    upperProduct lam (i + 1) = lam ⟨d - i - 1, by omega⟩ * upperProduct lam i := by
  first
  | let j : Fin d := ⟨d - i - 1, by omega⟩
    have hset : Finset.univ.filter (fun k : Fin d => d - (i + 1) ≤ k.val) =
        insert j (Finset.univ.filter (fun k : Fin d => d - i ≤ k.val)) := by
      first
      | ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        have heq : k = j ↔ k.val = d - i - 1 := Fin.ext_iff
        rw [heq]
        omega
    have hj : j ∉ Finset.univ.filter (fun k : Fin d => d - i ≤ k.val) := by
      first
      | simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [j]
        omega
    simp only [upperProduct, hset, Finset.prod_insert hj, j]

theorem upperProduct_ratioAxes {d : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) :
    ∀ i : ℕ, i ≤ d → upperProduct (ratioAxes d a) i = a i / a 0 := by
  first
  | intro i
    induction i with
    | zero =>
        intro _
        rw [upperProduct_zero, div_self (ha 0 (Nat.zero_le _)).ne']
    | succ i ih =>
        intro hid
        rw [upperProduct_succ _ (by omega), ih (by omega)]
        have hnum : d - (d - i - 1) = i + 1 := by omega
        have hden : d - (d - i - 1) - 1 = i := by omega
        simp only [ratioAxes, hnum, hden, Nat.add_sub_cancel]
        field_simp [(ha i (by omega)).ne', (ha 0 (Nat.zero_le _)).ne']

theorem map_axisBody {d : ℕ} (k lam : Fin d → ℝ) :
    mapBody (diagonalMap k) (axisBody lam) = axisBody (fun i => k i * lam i) := by
  first
  | apply ConvexBody.ext
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      ext i
      simp only [diagonalMap_apply]
      ring
    · rintro ⟨y, hy, rfl⟩
      refine ⟨diagonalMap lam y, ⟨y, hy, rfl⟩, ?_⟩
      ext i
      simp only [diagonalMap_apply]
      ring

theorem volume_sum_diagonal {d : ℕ} (k lam : Fin d → ℝ) (t s : ℝ) :
    bodyVolume (t • axisBody k + s • axisBody (fun i => k i * lam i)) =
      |∏ i, k i| * bodyVolume (t • body d + s • axisBody lam) := by
  first
  | have hmap : t • axisBody k + s • axisBody (fun i => k i * lam i) =
        mapBody (diagonalMap k) (t • body d + s • axisBody lam) := by
      first
      | rw [mapBody_add, mapBody_smul, mapBody_smul, map_axisBody]
        rfl
    rw [hmap, bodyVolume_map, det_diagonalMap]

theorem realizes_ratio_axes {d : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) (hr : DecreasingRatios d a)
    (k : Fin d → ℝ) (hk : ∀ i, 0 < k i)
    (hprod : ∏ i, k i = (d.factorial : ℝ) * a 0) :
    Realizes d a (axisBody k) (axisBody (fun i => k i * ratioAxes d a i)) := by
  first
  | intro t s ht hs
    rw [volume_sum_diagonal, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hk i).le)),
      hprod, volume_sum_choose (fun i => (ratioAxes_pos ha i).le) (ratioAxes_monotone hr) ht hs]
    unfold value
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [upperProduct_ratioAxes ha i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    field_simp [hfac, (ha 0 (Nat.zero_le _)).ne']

def commonScale (d : ℕ) (b : ℝ) : ℝ := ((d.factorial : ℝ) * b) ^ ((d : ℝ)⁻¹)

theorem commonScale_pos {d : ℕ} {b : ℝ} (hb : 0 < b) : 0 < commonScale d b := by
  first
  | apply Real.rpow_pos_of_pos
    exact mul_pos (by exact_mod_cast Nat.factorial_pos d) hb

theorem commonScale_pow {d : ℕ} (hd : 0 < d) {b : ℝ} (hb : 0 ≤ b) :
    commonScale d b ^ d = (d.factorial : ℝ) * b :=
  Real.rpow_inv_natCast_pow (mul_nonneg (Nat.cast_nonneg _) hb) hd.ne'

/-- The positive part of Appendix A, as an actual realization by two
coordinate simplices. -/
theorem exists_positive_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) (hc : Criterion d a) :
    ∃ k lam : Fin d → ℝ, (∀ i, 0 < k i) ∧ (∀ i, 0 < lam i) ∧
      Realizes d a (axisBody k) (axisBody lam) := by
  first
  | let C := commonScale d (a 0)
    have hC : 0 < C := commonScale_pos (ha 0 (Nat.zero_le _))
    refine ⟨fun _ => C, fun i => C * ratioAxes d a i,
      fun _ => hC, fun i => mul_pos hC (ratioAxes_pos ha i), ?_⟩
    apply realizes_ratio_axes ha (decreasingRatios_of_criterion ha hc) _ (fun _ => hC)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      commonScale_pow hd (ha 0 (Nat.zero_le _)).le

theorem value_eq_zero {d : ℕ} {a : ℕ → ℝ} (ha : ∀ i ≤ d, a i = 0) (t s : ℝ) :
    value d a t s = 0 := by
  first
  | apply Finset.sum_eq_zero
    intro i hi
    rw [ha i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    ring

theorem zero_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, a i = 0) :
    Realizes d a (axisBody (fun _ => 0)) (axisBody (fun _ => 0)) := by
  first
  | have hz : axisBody (fun _ : Fin d => (0 : ℝ)) = (0 : Body d) := by
      first
      | have h := axisBody_scalar (fun _ : Fin d => (1 : ℝ)) 0
        simpa only [zero_mul, body_zero_smul] using h
    have hs0 (r : ℝ) : r • (0 : Body d) = 0 := by
      calc
        r • (0 : Body d) = (r * 0) • body d := by rw [← smul_smul, body_zero_smul]
        _ = 0 := by rw [mul_zero, body_zero_smul]
    intro t s ht hs
    simp only [hz, hs0, add_zero, value_eq_zero ha]
    have h := bodyVolume_smul (body d) (r := 0) le_rfl
    simpa only [body_zero_smul, zero_pow hd.ne', zero_mul] using h

end VolumePolynomials.BinarySimplex
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinarySimplexRealization.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinaryBoundarySequences.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Positive approximation of every allowed binary zero pattern

The support interval is derived from the separated-index inequalities. The
padding is the one in Appendix A. Its ratios are proved to be ordered for
all sufficiently small positive parameters, including a support consisting
of a single coefficient.
-/

open Set Filter
open scoped BigOperators Topology

namespace VolumePolynomials.BinarySimplex

open BinarySequences

structure IntervalSupport (d : ℕ) (a : ℕ → ℝ) where
  left : ℕ
  right : ℕ
  left_le_right : left ≤ right
  right_le_degree : right ≤ d
  positive : ∀ i, left ≤ i → i ≤ right → 0 < a i
  vanishes : ∀ i ≤ d, (i < left ∨ right < i) → a i = 0

theorem intervalSupport_of_criterion {d : ℕ} {a : ℕ → ℝ}
    (hc : Criterion d a) (hne : ∃ i ≤ d, a i ≠ 0) : Nonempty (IntervalSupport d a) := by
  first
  | classical
    let S := (Finset.range (d + 1)).filter (fun i => 0 < a i)
    have hS : S.Nonempty := by
      first
      | obtain ⟨i, hid, hi⟩ := hne
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
          lt_of_le_of_ne (hc.1 i hid) (Ne.symm hi)⟩⟩
    let l := S.min' hS
    let r := S.max' hS
    have hlS : l ∈ S := Finset.min'_mem S hS
    have hrS : r ∈ S := Finset.max'_mem S hS
    have hlr : l ≤ r := Finset.min'_le_max' S hS
    have hrd : r ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hrS).1)
    have hlpos : 0 < a l := (Finset.mem_filter.mp hlS).2
    have hrpos : 0 < a r := (Finset.mem_filter.mp hrS).2
    refine ⟨⟨l, r, hlr, hrd, ?_, ?_⟩⟩
    · intro i hli hir
      exact hc.noInternalZeros l i r hli hir hrd hlpos hrpos
    · intro i hid hout
      apply le_antisymm _ (hc.1 i hid)
      apply le_of_not_gt
      intro hipos
      have hiS : i ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hipos⟩
      have hli : l ≤ i := Finset.min'_le S i hiS
      have hir : i ≤ r := Finset.le_max' S i hiS
      rcases hout with h | h <;> omega

def padded (a : ℕ → ℝ) (l r : ℕ) (eps : ℝ) (i : ℕ) : ℝ :=
  if i < l then a l * eps ^ (l - i)
  else if r < i then a r * eps ^ (i - r)
  else a i

theorem padded_eq_left (a : ℕ → ℝ) {l r i : ℕ} (hlr : l ≤ r) (hi : i ≤ l) (eps : ℝ) :
    padded a l r eps i = a l * eps ^ (l - i) := by
  first
  | by_cases hil : i < l
    · simp only [padded, if_pos hil]
    · have heq : i = l := by omega
      subst i
      simp [padded, not_lt_of_ge hlr]

theorem padded_eq_right (a : ℕ → ℝ) {l r i : ℕ} (hlr : l ≤ r) (hi : r ≤ i) (eps : ℝ) :
    padded a l r eps i = a r * eps ^ (i - r) := by
  first
  | by_cases hri : r < i
    · simp only [padded, if_neg (by omega : ¬i < l), if_pos hri]
    · have heq : i = r := by omega
      subst i
      simp [padded, not_lt_of_ge hlr]

theorem padded_eq_middle (a : ℕ → ℝ) {l r i : ℕ}
    (hli : l ≤ i) (hir : i ≤ r) (eps : ℝ) : padded a l r eps i = a i := by
  first
  | simp only [padded, if_neg (not_lt_of_ge hli), if_neg (not_lt_of_ge hir)]

theorem IntervalSupport.padded_pos {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    {eps : ℝ} (heps : 0 < eps) : ∀ i ≤ d, 0 < padded a h.left h.right eps i := by
  first
  | intro i hid
    by_cases hil : i < h.left
    · rw [padded_eq_left a h.left_le_right hil.le]
      exact mul_pos (h.positive _ le_rfl h.left_le_right) (pow_pos heps _)
    by_cases hri : h.right < i
    · rw [padded_eq_right a h.left_le_right hri.le]
      exact mul_pos (h.positive _ h.left_le_right le_rfl) (pow_pos heps _)
    rw [padded_eq_middle a (by omega) (by omega)]
    exact h.positive i (by omega) (by omega)

theorem padded_ratio_left {a : ℕ → ℝ} {l r i : ℕ} (hlr : l ≤ r)
    (ha : 0 < a l) (hi : i < l) {eps : ℝ} (heps : 0 < eps) :
    padded a l r eps (i + 1) / padded a l r eps i = 1 / eps := by
  first
  | rw [padded_eq_left a hlr (by omega), padded_eq_left a hlr hi.le]
    have hpow : l - i = (l - (i + 1)) + 1 := by omega
    rw [hpow, pow_succ]
    field_simp [ha.ne', heps.ne', pow_ne_zero _ heps.ne']

theorem padded_ratio_middle (a : ℕ → ℝ) {l r i : ℕ}
    (hli : l ≤ i) (hir : i < r) (eps : ℝ) :
    padded a l r eps (i + 1) / padded a l r eps i = a (i + 1) / a i := by
  first
  | rw [padded_eq_middle a (by omega) (by omega), padded_eq_middle a hli hir.le]

theorem padded_ratio_right {a : ℕ → ℝ} {l r i : ℕ} (hlr : l ≤ r)
    (ha : 0 < a r) (hi : r ≤ i) {eps : ℝ} (heps : 0 < eps) :
    padded a l r eps (i + 1) / padded a l r eps i = eps := by
  first
  | rw [padded_eq_right a hlr (by omega), padded_eq_right a hlr hi]
    have hpow : i + 1 - r = (i - r) + 1 := by omega
    rw [hpow, pow_succ]
    field_simp [ha.ne', heps.ne', pow_ne_zero _ heps.ne']

theorem padded_decreasingRatios {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    (hc : Criterion d a) {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsmall : ∀ i : ℕ, h.left ≤ i → i < h.right →
      eps ≤ a (i + 1) / a i ∧ a (i + 1) / a i ≤ 1 / eps) :
    DecreasingRatios d (padded a h.left h.right eps) := by
  first
  | intro i j hij hjd
    have hrd := h.right_le_degree
    have hlpos := h.positive h.left le_rfl h.left_le_right
    have hrpos := h.positive h.right h.left_le_right le_rfl
    by_cases hjl : j < h.left
    · rw [padded_ratio_left h.left_le_right hlpos hjl heps,
        padded_ratio_left h.left_le_right hlpos (by omega) heps]
    by_cases hri : h.right ≤ i
    · rw [padded_ratio_right h.left_le_right hrpos hri heps,
        padded_ratio_right h.left_le_right hrpos (by omega) heps]
    by_cases hil : i < h.left
    · rw [padded_ratio_left h.left_le_right hlpos hil heps]
      by_cases hjr : j < h.right
      · rw [padded_ratio_middle a (by omega) hjr]
        exact (hsmall j (by omega) hjr).2
      · rw [padded_ratio_right h.left_le_right hrpos (by omega) heps]
        apply (le_div_iff₀ heps).mpr
        nlinarith
    have hli : h.left ≤ i := by omega
    have hir : i < h.right := by omega
    rw [padded_ratio_middle a hli hir]
    by_cases hjr : j < h.right
    · rw [padded_ratio_middle a (by omega) hjr]
      exact ratios_antitone_on_interval h.positive
        (fun k hlk hkr => hc.adjacent (by omega) (by omega)) i j hli hij hjr
    · rw [padded_ratio_right h.left_le_right hrpos (by omega) heps]
      exact (hsmall i hli hir).1

theorem eventually_padding_bounds {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), 0 < eps ∧ eps ≤ 1 ∧
      ∀ i : ℕ, h.left ≤ i → i < h.right →
        eps ≤ a (i + 1) / a i ∧ a (i + 1) / a i ≤ 1 / eps := by
  first
  | have hfinite : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        ∀ i : Fin d, h.left ≤ i.val → i.val < h.right →
          eps ≤ a (i.val + 1) / a i.val ∧ a (i.val + 1) / a i.val ≤ 1 / eps := by
      first
      | apply Filter.eventually_all.mpr
        intro i
        by_cases hli : h.left ≤ i.val
        · by_cases hir : i.val < h.right
          · have hratio : 0 < a (i.val + 1) / a i.val :=
              div_pos (h.positive _ (by omega) (by omega)) (h.positive _ hli hir.le)
            filter_upwards [(eventually_lt_nhds hratio).filter_mono nhdsWithin_le_nhds,
              (eventually_lt_nhds (one_div_pos.mpr hratio)).filter_mono nhdsWithin_le_nhds,
              self_mem_nhdsWithin] with eps he1 he2 hepos
            intro _ _
            refine ⟨he1.le, (le_div_iff₀ hepos).mpr ?_⟩
            have hm := (lt_div_iff₀ hratio).mp he2
            nlinarith
          · exact Filter.Eventually.of_forall (fun _ _ hi => False.elim (hir hi))
        · exact Filter.Eventually.of_forall (fun _ hi _ => False.elim (hli hi))
    filter_upwards [hfinite, self_mem_nhdsWithin,
      (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with eps hbounds heps heps1
    refine ⟨heps, heps1.le, ?_⟩
    intro i hli hir
    exact hbounds ⟨i, hir.trans_le h.right_le_degree⟩ hli hir

theorem eventually_padded_decreasingRatios {d : ℕ} {a : ℕ → ℝ}
    (h : IntervalSupport d a) (hc : Criterion d a) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      DecreasingRatios d (padded a h.left h.right eps) := by
  first
  | filter_upwards [eventually_padding_bounds h] with eps heps
    exact padded_decreasingRatios h hc heps.1 heps.2.1 heps.2.2

theorem continuous_padded (a : ℕ → ℝ) (l r i : ℕ) :
    Continuous (fun eps : ℝ => padded a l r eps i) := by
  first
  | unfold padded
    split_ifs <;> fun_prop

theorem IntervalSupport.padded_zero {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    {i : ℕ} (hi : i ≤ d) : padded a h.left h.right 0 i = a i := by
  first
  | by_cases hil : i < h.left
    · rw [padded_eq_left a h.left_le_right hil.le,
        zero_pow (by omega : h.left - i ≠ 0), mul_zero,
        h.vanishes i hi (Or.inl hil)]
    by_cases hri : h.right < i
    · rw [padded_eq_right a h.left_le_right hri.le,
        zero_pow (by omega : i - h.right ≠ 0), mul_zero,
        h.vanishes i hi (Or.inr hri)]
    exact padded_eq_middle a (by omega) (by omega) 0

theorem value_padded_tendsto {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a) (t s : ℝ) :
    Tendsto (fun eps : ℝ => value d (padded a h.left h.right eps) t s)
      (𝓝[>] (0 : ℝ)) (𝓝 (value d a t s)) := by
  first
  | have hc : Continuous (fun eps : ℝ => value d (padded a h.left h.right eps) t s) := by
      first
      | unfold value
        apply continuous_finsetSum
        intro i _
        exact (((continuous_padded a h.left h.right i).const_mul _).mul continuous_const).mul continuous_const
    have hz : value d (padded a h.left h.right 0) t s = value d a t s := by
      first
      | apply Finset.sum_congr rfl
        intro i hi
        rw [h.padded_zero (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    simpa only [hz] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

end VolumePolynomials.BinarySimplex
end -- closes the original EOF section from source line 10
end -- closes the original EOF section from source line 7
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinaryBoundarySequences.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinaryBoundaryRealization.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Degenerate simplex realizations

The two approximating simplices have axis lengths affine in the small
parameter. Their limits are exactly the two possibly degenerate simplices
in (A.3), with coordinate order reversed. Their volume identity passes to
the limit for every pair of nonnegative Minkowski weights.
-/

open Set MeasureTheory Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.BinarySimplex

open AxisSimplex BinarySequences

def leftAxes (d l : ℕ) (C eps : ℝ) (j : Fin d) : ℝ :=
  C * if d - j.val ≤ l then eps else 1

def rightAxes (d l r : ℕ) (C : ℝ) (a : ℕ → ℝ) (eps : ℝ) (j : Fin d) : ℝ :=
  if d - j.val ≤ l then C
  else if d - j.val ≤ r then C * (a (d - j.val) / a (d - j.val - 1))
  else C * eps

theorem card_last_axes {d l : ℕ} (hl : l ≤ d) :
    (Finset.univ.filter (fun j : Fin d => d - j.val ≤ l)).card = l := by
  first
  | by_cases hl0 : l = 0
    · subst l
      have he : Finset.univ.filter (fun j : Fin d => d - j.val ≤ 0) = ∅ := by
        first
        | apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j hj
          have h := (Finset.mem_filter.mp hj).2
          have hjlt := j.isLt
          omega
      simp only [he, Finset.card_empty]
    · have hlt : d - l < d := by omega
      let b : Fin d := ⟨d - l, hlt⟩
      have he : Finset.univ.filter (fun j : Fin d => d - j.val ≤ l) = Finset.Ici b := by
        first
        | ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
          change d - j.val ≤ l ↔ d - l ≤ j.val
          have hjlt := j.isLt
          omega
      rw [he, Fin.card_Ici]
      change d - (d - l) = l
      omega

theorem prod_leftAxes {d l : ℕ} (hl : l ≤ d) (C eps : ℝ) :
    ∏ j, leftAxes d l C eps j = C ^ d * eps ^ l := by
  first
  | simp only [leftAxes, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← Finset.prod_filter, Finset.prod_const, card_last_axes hl]

theorem leftAxes_pos {d l : ℕ} {C eps : ℝ} (hC : 0 < C) (heps : 0 < eps) :
    ∀ j : Fin d, 0 < leftAxes d l C eps j := by
  first
  | intro j
    unfold leftAxes
    split_ifs <;> positivity

theorem rightAxes_eq_ratio {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    {eps : ℝ} (heps : 0 < eps) (C : ℝ) (j : Fin d) :
    rightAxes d h.left h.right C a eps j =
      leftAxes d h.left C eps j * ratioAxes d (padded a h.left h.right eps) j := by
  first
  | have hjlt := j.isLt
    have hindex : d - j.val - 1 + 1 = d - j.val := by omega
    by_cases hjl : d - j.val ≤ h.left
    · have hr := padded_ratio_left h.left_le_right
        (h.positive _ le_rfl h.left_le_right) (i := d - j.val - 1) (by omega) heps
      rw [hindex] at hr
      simp only [rightAxes, leftAxes, if_pos hjl, ratioAxes, hr]
      field_simp [heps.ne']
    · by_cases hjr : d - j.val ≤ h.right
      · have hr := padded_ratio_middle a (l := h.left) (r := h.right)
          (i := d - j.val - 1) (by omega) (by omega) eps
        rw [hindex] at hr
        simp only [rightAxes, leftAxes, if_neg hjl, if_pos hjr, ratioAxes, hr, mul_one]
      · have hr := padded_ratio_right h.left_le_right
          (h.positive _ h.left_le_right le_rfl) (i := d - j.val - 1) (by omega) heps
        rw [hindex] at hr
        simp only [rightAxes, leftAxes, if_neg hjl, if_neg hjr, ratioAxes, hr, mul_one]

theorem padded_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (h : IntervalSupport d a) {eps : ℝ} (heps : 0 < eps)
    (hr : DecreasingRatios d (padded a h.left h.right eps)) :
    Realizes d (padded a h.left h.right eps)
      (axisBody (leftAxes d h.left (commonScale d (a h.left)) eps))
      (axisBody (rightAxes d h.left h.right (commonScale d (a h.left)) a eps)) := by
  first
  | let C := commonScale d (a h.left)
    have ha : 0 < a h.left := h.positive _ le_rfl h.left_le_right
    have hC : 0 < C := commonScale_pos ha
    have hprod : ∏ j, leftAxes d h.left C eps j =
        (d.factorial : ℝ) * padded a h.left h.right eps 0 := by
      first
      | rw [prod_leftAxes (h.left_le_right.trans h.right_le_degree), commonScale_pow hd ha.le,
          padded_eq_left a h.left_le_right (Nat.zero_le _), Nat.sub_zero]
        ring
    have hright : rightAxes d h.left h.right C a eps =
        fun j => leftAxes d h.left C eps j * ratioAxes d (padded a h.left h.right eps) j :=
      funext (rightAxes_eq_ratio h heps C)
    change Realizes d (padded a h.left h.right eps)
      (axisBody (leftAxes d h.left C eps)) (axisBody (rightAxes d h.left h.right C a eps))
    rw [hright]
    exact realizes_ratio_axes (h.padded_pos heps) hr _ (leftAxes_pos hC heps) hprod

theorem continuous_leftAxes (d l : ℕ) (C : ℝ) : Continuous (leftAxes d l C) := by
  first
  | apply continuous_pi
    intro j
    dsimp only [leftAxes]
    split_ifs <;> fun_prop

theorem continuous_rightAxes (d l r : ℕ) (C : ℝ) (a : ℕ → ℝ) :
    Continuous (rightAxes d l r C a) := by
  first
  | apply continuous_pi
    intro j
    dsimp only [rightAxes]
    split_ifs <;> fun_prop

set_option maxHeartbeats 1000000 in
/-- Formula (A.3), with no restriction on the support interval. -/
theorem boundary_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (h : IntervalSupport d a) (hc : Criterion d a) :
    Realizes d a
      (axisBody (leftAxes d h.left (commonScale d (a h.left)) 0))
      (axisBody (rightAxes d h.left h.right (commonScale d (a h.left)) a 0)) := by
  first
  | let C := commonScale d (a h.left)
    intro t s ht hs
    have hleft : Tendsto (fun eps : ℝ => bodyVolume
        (t • axisBody (leftAxes d h.left C eps) +
          s • axisBody (rightAxes d h.left h.right C a eps)))
        (𝓝[>] (0 : ℝ)) (𝓝 (bodyVolume
        (t • axisBody (leftAxes d h.left C 0) +
          s • axisBody (rightAxes d h.left h.right C a 0)))) := by
      first
      | have hK := (continuous_axisBody d).comp' (continuous_leftAxes d h.left C)
        have hL := (continuous_axisBody d).comp' (continuous_rightAxes d h.left h.right C a)
        have hsum : Continuous (fun eps : ℝ =>
            t • axisBody (leftAxes d h.left C eps) +
              s • axisBody (rightAxes d h.left h.right C a eps)) :=
          (hK.fun_const_smul t).fun_add (hL.fun_const_smul s)
        have hc : Continuous (fun eps : ℝ => bodyVolume
            (t • axisBody (leftAxes d h.left C eps) +
              s • axisBody (rightAxes d h.left h.right C a eps))) :=
          (continuous_bodyVolume d).comp hsum
        exact (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hright := value_padded_tendsto h t s
    have heq : (fun eps : ℝ => bodyVolume
        (t • axisBody (leftAxes d h.left C eps) +
          s • axisBody (rightAxes d h.left h.right C a eps)))
        =ᶠ[𝓝[>] (0 : ℝ)] fun eps => value d (padded a h.left h.right eps) t s := by
      first
      | filter_upwards [eventually_padded_decreasingRatios h hc, self_mem_nhdsWithin]
          with eps hrat heps
        exact padded_axis_realization hd h heps hrat t s ht hs
    exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

theorem boundary_axes_nonnegative {d : ℕ} {a : ℕ → ℝ}
    (h : IntervalSupport d a) {C : ℝ} (hC : 0 ≤ C) :
    (∀ j : Fin d, 0 ≤ leftAxes d h.left C 0 j) ∧
      (∀ j : Fin d, 0 ≤ rightAxes d h.left h.right C a 0 j) := by
  first
  | constructor
    · intro j
      unfold leftAxes
      split_ifs <;> positivity
    · intro j
      unfold rightAxes
      split_ifs with hjl hjr
      · exact hC
      · have hjlt := j.isLt
        exact mul_nonneg hC (div_nonneg
          (h.positive _ (by omega) hjr).le (h.positive _ (by omega) (by omega)).le)
      · simp only [mul_zero, le_refl]

/-- Full sufficiency in Proposition A.1: every admissible coefficient
sequence, including all zero patterns, is realized by two explicit axis
simplices. No positivity premise on the coefficients is retained. -/
theorem appendix_A_sufficiency {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (hc : Criterion d a) :
    ∃ k lam : Fin d → ℝ, (∀ i, 0 ≤ k i) ∧ (∀ i, 0 ≤ lam i) ∧
      Realizes d a (axisBody k) (axisBody lam) := by
  first
  | by_cases hz : ∀ i ≤ d, a i = 0
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => le_rfl, fun _ => le_rfl,
        zero_axis_realization hd hz⟩
    · have hne : ∃ i ≤ d, a i ≠ 0 := by simpa only [not_forall, exists_prop] using hz
      obtain ⟨h⟩ := intervalSupport_of_criterion hc hne
      let C := commonScale d (a h.left)
      have hC : 0 < C := commonScale_pos (h.positive _ le_rfl h.left_le_right)
      have hn := boundary_axes_nonnegative h hC.le
      exact ⟨leftAxes d h.left C 0, rightAxes d h.left h.right C a 0,
        hn.1, hn.2, boundary_axis_realization hd h hc⟩

end VolumePolynomials.BinarySimplex
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinaryBoundaryRealization.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinaryRealizationCriterion.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

namespace VolumePolynomials.BinarySimplex

/-- Proposition A.1, in the literal binomial normalization of the paper,
with all nonnegative weights and all degenerate zero patterns retained. -/
theorem appendix_A_realization_iff {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) :
    (∃ K L : Body d, Realizes d a K L) ↔ BinarySequences.Criterion d a := by
  first
  | constructor
    · rintro ⟨K, L, h⟩
      exact BinaryMixed.criterion_of_realizes hd h
    · intro h
      obtain ⟨k, lam, hk, hlam, hreal⟩ := appendix_A_sufficiency hd h
      exact ⟨AxisSimplex.axisBody k, AxisSimplex.axisBody lam, hreal⟩

end VolumePolynomials.BinarySimplex
end -- closes the original EOF section from source line 9
end -- closes the original EOF section from source line 6
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinaryRealizationCriterion.lean -/

/- BEGIN SOURCE: VolumePolynomials/BinarySemialgebraic.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The complete semialgebraic side of Theorem 1.1, in the actual homogeneous
coefficient space. The binary set is given by the finite quadratic
inequalities of Appendix A, with its normalization justified explicitly. -/

open Set MvPolynomial

namespace VolumePolynomials

def binaryCoordinatePolynomial (d : ℕ) (i : Fin (d + 1)) :
    MvPolynomial (MultiIndex 2 d) ℝ :=
  C (1 / (d.choose i.val : ℝ)) * X (binaryIndex d i)

theorem eval_binaryCoordinatePolynomial {d : ℕ} (c : Coefficients 2 d)
    (i : Fin (d + 1)) :
    MvPolynomial.eval c (binaryCoordinatePolynomial d i) = binaryNormalizedSequence c i.val := by
  first
  | rw [binaryNormalizedSequence_apply]
    simp only [binaryCoordinatePolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    ring

abbrev BinaryAdmissiblePair (d : ℕ) :=
  {p : Fin (d + 1) × Fin (d + 1) // 1 ≤ p.1.val ∧ p.1.val ≤ p.2.val ∧ p.2.val < d}

def binaryLeftPolynomial (d : ℕ) (p : BinaryAdmissiblePair d) :
    MvPolynomial (MultiIndex 2 d) ℝ :=
  binaryCoordinatePolynomial d ⟨p.1.1.val - 1, by have h := p.1.1.isLt; omega⟩ *
    binaryCoordinatePolynomial d ⟨p.1.2.val + 1, by have h := p.2.2.2; omega⟩

def binaryRightPolynomial (d : ℕ) (p : BinaryAdmissiblePair d) :
    MvPolynomial (MultiIndex 2 d) ℝ :=
  binaryCoordinatePolynomial d p.1.1 * binaryCoordinatePolynomial d p.1.2

theorem binaryCriterion_set_eq (d : ℕ) :
    {c : Coefficients 2 d | BinarySequences.Criterion d (binaryNormalizedSequence c)} =
      (⋂ i : Fin (d + 1), {c | 0 ≤ MvPolynomial.eval c (binaryCoordinatePolynomial d i)}) ∩
      (⋂ p : BinaryAdmissiblePair d,
        {c | MvPolynomial.eval c (binaryLeftPolynomial d p) ≤
          MvPolynomial.eval c (binaryRightPolynomial d p)}) := by
  first
  | ext c
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      eval_binaryCoordinatePolynomial, binaryLeftPolynomial, binaryRightPolynomial,
      MvPolynomial.eval_mul]
    constructor
    · intro h
      refine ⟨fun i => h.1 i.val (Nat.le_of_lt_succ i.isLt), ?_⟩
      intro p
      simpa only [eval_binaryCoordinatePolynomial] using
        h.2 p.1.1.val p.1.2.val p.2.1 p.2.2.1 p.2.2.2
    · rintro ⟨hn, hp⟩
      constructor
      · intro i hid
        exact hn ⟨i, Nat.lt_succ_of_le hid⟩
      · intro i j hi hij hjd
        let p : BinaryAdmissiblePair d :=
          ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hi, hij, hjd⟩
        simpa only [p, eval_binaryCoordinatePolynomial] using hp p

theorem isSemialgebraic_binaryCriterion (d : ℕ) :
    TauCeti.IsSemialgebraic
      {c : Coefficients 2 d | BinarySequences.Criterion d (binaryNormalizedSequence c)} := by
  first
  | rw [binaryCriterion_set_eq]
    apply TauCeti.IsSemialgebraic.inter
    · exact TauCeti.IsSemialgebraic.iInter (fun i =>
        TauCeti.isSemialgebraic_eval_nonneg (binaryCoordinatePolynomial d i))
    · exact TauCeti.IsSemialgebraic.iInter (fun p =>
        TauCeti.isSemialgebraic_eval_le (binaryLeftPolynomial d p) (binaryRightPolynomial d p))

theorem twoBody_realizable_iff {d : ℕ} (hd : 0 < d) (c : Coefficients 2 d) :
    c ∈ VolumeLocus 2 d ↔ BinarySequences.Criterion d (binaryNormalizedSequence c) := by
  first
  | rw [binary_volumeLocus_iff, BinarySimplex.appendix_A_realization_iff hd]

theorem isSemialgebraic_twoBody {d : ℕ} (hd : 0 < d) :
    TauCeti.IsSemialgebraic (VolumeLocus 2 d) := by
  first
  | have heq : VolumeLocus 2 d =
        {c | BinarySequences.Criterion d (binaryNormalizedSequence c)} := by
      first
      | ext c
        exact twoBody_realizable_iff hd c
    rw [heq]
    exact isSemialgebraic_binaryCriterion d

theorem isSemialgebraic_oneBody {d : ℕ} (hd : 0 < d) :
    TauCeti.IsSemialgebraic (VolumeLocus 1 d) := by
  first
  | have heq : VolumeLocus 1 d = {c | 0 ≤ c (oneIndex d)} := by
      first
      | ext c
        exact oneBody_realizable_iff hd c
    rw [heq]
    simpa only [MvPolynomial.eval_X] using
      TauCeti.isSemialgebraic_eval_nonneg (MvPolynomial.X (oneIndex d) : MvPolynomial (MultiIndex 1 d) ℝ)

theorem isSemialgebraic_volumeLocus_of_le_two {n d : ℕ}
    (hn : 1 ≤ n) (hd : 0 < d) (hn2 : n ≤ 2) :
    TauCeti.IsSemialgebraic (VolumeLocus n d) := by
  first
  | have h : n = 1 ∨ n = 2 := by omega
    rcases h with rfl | rfl
    · exact isSemialgebraic_oneBody hd
    · exact isSemialgebraic_twoBody hd

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/BinarySemialgebraic.lean -/

/- BEGIN SOURCE: VolumePolynomials/ExtraVariables.lean -/
section


@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Adding point bodies and retaining all ordinary coefficients

Renaming a homogeneous polynomial into the first coordinates is a polynomial
map of coefficient spaces. Its preimage of the larger realization locus is
exactly the original locus. This transfers nonsemialgebraicity to every
larger number of bodies without assuming an image theorem.
-/

open MvPolynomial Set
open scoped BigOperators Pointwise

namespace VolumePolynomials

def extraVariables {m d : ℕ} (k : ℕ) (c : Coefficients m d) : Coefficients (m + k) d :=
  coefficientsOfPolynomial (MvPolynomial.rename (Fin.castAdd k) (coefficientPolynomial c))

theorem extraVariables_homogeneous {m d : ℕ} (k : ℕ) (c : Coefficients m d) :
    (MvPolynomial.rename (Fin.castAdd k) (coefficientPolynomial c)).IsHomogeneous d :=
  (coefficientPolynomial_homogeneous c).rename_isHomogeneous

theorem evaluate_extraVariables {m d : ℕ} (k : ℕ) (c : Coefficients m d)
    (t : Fin (m + k) → ℝ) :
    evaluate (extraVariables k c) t = evaluate c (fun i => t (Fin.castAdd k i)) := by
  first
  | rw [evaluate_eq_polynomial_eval, extraVariables,
      coefficientPolynomial_coefficientsOfPolynomial _ (extraVariables_homogeneous k c),
      MvPolynomial.eval_rename, ← evaluate_eq_polynomial_eval]
    rfl

def extraPointBodies {m d : ℕ} (k : ℕ) (K : Fin m → Body d) : Fin (m + k) → Body d :=
  Fin.addCases K (fun _ => 0)

theorem weightedSum_extraPointBodies {m d : ℕ} (k : ℕ) (K : Fin m → Body d)
    (t : Fin (m + k) → ℝ) :
    weightedSum (extraPointBodies k K) t = weightedSum K (fun i => t (Fin.castAdd k i)) := by
  first
  | have hzero (r : ℝ) : r • (0 : Body d) = 0 := by
      apply ConvexBody.ext
      change r • ({0} : Set (Space d)) = {0}
      simp
    simp only [weightedSum, Fin.sum_univ_add, extraPointBodies,
      Fin.addCases_left, Fin.addCases_right, hzero, Finset.sum_const_zero, add_zero]

theorem weightedSum_zero_extraWeights {m k d : ℕ} (K : Fin (m + k) → Body d)
    (t : Fin m → ℝ) :
    weightedSum K (Fin.addCases t (fun _ : Fin k => 0)) =
      weightedSum (fun i => K (Fin.castAdd k i)) t := by
  first
  | simp only [weightedSum, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      body_zero_smul, Finset.sum_const_zero, add_zero]

theorem Realizes.extraPointBodies {m d : ℕ} {K : Fin m → Body d} {c : Coefficients m d}
    (h : Realizes K c) (k : ℕ) : Realizes (extraPointBodies k K) (extraVariables k c) := by
  first
  | intro t ht
    rw [evaluate_extraVariables, volumeFunction, weightedSum_extraPointBodies]
    exact h (fun i => t (Fin.castAdd k i)) (fun i => ht _)

theorem Realizes.discard_extra {m k d : ℕ} {K : Fin (m + k) → Body d}
    {c : Coefficients m d} (h : Realizes K (extraVariables k c)) :
    Realizes (fun i => K (Fin.castAdd k i)) c := by
  first
  | intro t ht
    have ht' : ∀ i, (0 : ℝ) ≤ Fin.addCases t (fun _ : Fin k => (0 : ℝ)) i := by
      first
      | intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simpa only [Fin.addCases_left] using ht j
        · intro j
          simp only [Fin.addCases_right, le_refl]
    have he := h (Fin.addCases t (fun _ : Fin k => 0)) ht'
    simpa only [evaluate_extraVariables, Fin.addCases_left, volumeFunction,
      weightedSum_zero_extraWeights] using he

theorem extraVariables_mem_iff {m k d : ℕ} (c : Coefficients m d) :
    extraVariables k c ∈ VolumeLocus (m + k) d ↔ c ∈ VolumeLocus m d := by
  first
  | constructor
    · rintro ⟨K, hK⟩
      exact ⟨_, hK.discard_extra⟩
    · rintro ⟨K, hK⟩
      exact ⟨_, hK.extraPointBodies k⟩

def extraVariableCoordinate {m d : ℕ} (k : ℕ) (β : MultiIndex (m + k) d) :
    MvPolynomial (MultiIndex m d) ℝ :=
  ∑ α : MultiIndex m d,
    if Finsupp.mapDomain (Fin.castAdd k) (exponent α) = exponent β then X α else 0

theorem extraVariableCoordinate_eval {m d : ℕ} (k : ℕ) (c : Coefficients m d)
    (β : MultiIndex (m + k) d) :
    MvPolynomial.eval c (extraVariableCoordinate k β) = extraVariables k c β := by
  first
  | classical
    simp only [extraVariableCoordinate, MvPolynomial.eval_sum, eval_X, map_zero,
      extraVariables, coefficientsOfPolynomial, coefficientPolynomial, map_sum,
      MvPolynomial.coeff_sum, rename_monomial, coeff_monomial]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs <;> simp

theorem not_semialgebraic_extraVariables {m k d : ℕ}
    (h : ¬ TauCeti.IsSemialgebraic (VolumeLocus m d)) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus (m + k) d) := by
  first
  | intro hlarge
    apply h
    have hs := hlarge.preimage_eval (extraVariableCoordinate (m := m) (d := d) k)
    have heq : (fun c β => MvPolynomial.eval c (extraVariableCoordinate k β)) ⁻¹'
        VolumeLocus (m + k) d = VolumeLocus m d := by
      first
      | ext c
        simpa only [Set.mem_preimage, funext (extraVariableCoordinate_eval k c)] using
          extraVariables_mem_iff (k := k) c
    rwa [heq] at hs

theorem not_semialgebraic_volumeLocus_of_three {n d : ℕ} (hn : 3 ≤ n)
    (h3 : ¬ TauCeti.IsSemialgebraic (VolumeLocus 3 d)) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus n d) := by
  first
  | have heq : 3 + (n - 3) = n := by omega
    rw [← heq]
    exact not_semialgebraic_extraVariables (k := n - 3) h3

end VolumePolynomials
end -- closes the original EOF section from source line 11
end -- closes the original EOF section from source line 8
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/ExtraVariables.lean -/

/- BEGIN SOURCE: VolumePolynomials/CoefficientMap.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The actual continuous coefficient map

Polynomial existence and uniqueness identify the coefficient vector of every
tuple of compact convex bodies. The definition chooses that uniquely determined
vector; it does not choose a polynomial approximation or assume mixed-volume
continuity. Continuity follows from volume continuity and the finite-dimensional
evaluation embedding proved before polynomial existence.
-/

open Set Topology

namespace VolumePolynomials

def coefficientMap {n d : ℕ} (K : Fin n → Body d) : Coefficients n d :=
  Classical.choose (exists_volume_polynomial K)

theorem coefficientMap_realizes {n d : ℕ} (K : Fin n → Body d) :
    Realizes K (coefficientMap K) :=
  Classical.choose_spec (exists_volume_polynomial K)

theorem Realizes.eq_coefficientMap {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) : c = coefficientMap K :=
  hc.unique (coefficientMap_realizes K)

theorem realizes_iff_eq_coefficientMap {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} : Realizes K c ↔ c = coefficientMap K :=
  ⟨Realizes.eq_coefficientMap, fun h => h.symm ▸ coefficientMap_realizes K⟩

theorem coefficientMap_nonnegative {n d : ℕ} (K : Fin n → Body d)
    (α : MultiIndex n d) : 0 ≤ coefficientMap K α :=
  (coefficientMap_realizes K).coefficients_nonnegative α

theorem evaluation_coefficientMap {n d : ℕ} (K : Fin n → Body d) :
    evaluationEmbedding n d (coefficientMap K) = volumeEvaluation K :=
  realizes_iff_evaluation_eq.mp (coefficientMap_realizes K)

theorem continuous_coefficientMap (n d : ℕ) :
    Continuous (coefficientMap (n := n) (d := d)) := by
  first
  | apply (isClosedEmbedding_evaluation n d).isEmbedding.continuous_iff.mpr
    have heq : evaluationEmbedding n d ∘ coefficientMap =
        (volumeEvaluation : (Fin n → Body d) → _) := by
      funext K
      exact evaluation_coefficientMap K
    rw [heq]
    exact continuous_volumeEvaluation n d

theorem range_coefficientMap (n d : ℕ) :
    Set.range (coefficientMap (n := n) (d := d)) = VolumeLocus n d := by
  first
  | ext c
    constructor
    · rintro ⟨K, rfl⟩
      exact ⟨K, coefficientMap_realizes K⟩
    · rintro ⟨K, hK⟩
      exact ⟨K, hK.eq_coefficientMap.symm⟩

theorem boundedVolumeLocus_eq_coefficientMap_image (n d : ℕ) (C : Set (Space d)) :
    boundedVolumeLocus n d C = coefficientMap '' boundedTuples n d C := by
  first
  | ext c
    constructor
    · rintro ⟨K, hK, hc⟩
      exact ⟨K, hK, hc.eq_coefficientMap.symm⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, hK, coefficientMap_realizes K⟩

/-- Proposition 2.4 for every Hausdorff-dense class of tuples, with its
coefficient image interpreted using the actual volume polynomial. -/
theorem closure_coefficientMap_image_of_dense {n d : ℕ} (hd : 0 < d)
    {S : Set (Fin n → Body d)} (hS : Dense S) :
    closure (coefficientMap '' S) = VolumeLocus n d := by
  first
  | apply Set.Subset.antisymm
    · apply closure_minimal _ (isClosed_volumeLocus n d hd)
      rintro c ⟨K, _, rfl⟩
      exact ⟨K, coefficientMap_realizes K⟩
    · rw [← range_coefficientMap]
      exact (continuous_coefficientMap n d).range_subset_closure_image_dense hS

end VolumePolynomials
end -- closes the original EOF section from source line 8
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/CoefficientMap.lean -/

/- BEGIN SOURCE: VolumePolynomials/VolumeLipschitz.lean -/
section

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# An explicit volume modulus on a bounded box

Coefficient nonnegativity bounds the volume added by a small Minkowski summand.
Hausdorff distance in `Space d` is the supremum norm, so its unit ball is a cube.
Combining these facts gives a rational uniform modulus for the effective nets.
This follows polynomiality; the qualitative continuity used to prove
polynomiality was established independently by dominated convergence.
-/

open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

def coordinateCube (d : ℕ) : Body d where
  carrier := Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
  convex' := convex_Icc _ _
  isCompact' := isCompact_Icc
  nonempty' := ⟨0, ⟨fun _ => neg_nonpos.mpr zero_le_one, fun _ => zero_le_one⟩⟩

/-- Every nonconstant power of a number in `[0,1]` is bounded by that number. -/
theorem bodyVolume_add_smul_sub_le {d : ℕ} (K L : Body d) {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    bodyVolume (K + h • L) - bodyVolume K ≤ h * bodyVolume (K + L) := by
  first
  | obtain ⟨c, hc, hr⟩ := exists_nonnegative_volume_polynomial ![K, L]
    have heval (s : ℝ) (hs : 0 ≤ s) :
        (∑ α : MultiIndex 2 d, c α * s ^ (α.1 1 : ℕ)) = bodyVolume (K + s • L) := by
      first
      | have hnonneg : ∀ i : Fin 2, 0 ≤ (![1, s] : Fin 2 → ℝ) i := by
          intro i
          fin_cases i <;> simp [hs]
        simpa [evaluate, volumeFunction, weightedSum, Fin.sum_univ_two,
          Fin.prod_univ_two] using hr ![1, s] hnonneg
    have heval0 : (∑ α : MultiIndex 2 d, c α * (0 : ℝ) ^ (α.1 1 : ℕ)) = bodyVolume K := by
      first
      | simpa only [body_zero_smul, add_zero] using heval 0 le_rfl
    have heval1 : (∑ α : MultiIndex 2 d, c α) = bodyVolume (K + L) := by
      first
      | simpa only [one_pow, mul_one, one_smul] using heval 1 zero_le_one
    rw [← heval h hh0, ← heval0, ← heval1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    by_cases hk : (α.1 1 : ℕ) = 0
    · simpa only [hk, pow_zero, mul_one, sub_self] using mul_nonneg hh0 (hc α)
    · simp only [zero_pow hk, mul_zero, sub_zero]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (pow_le_of_le_one hh0 hh1 hk) (hc α)

/-- Hausdorff control gives literal Minkowski containment in the coordinate cube. -/
theorem body_le_add_coordinateCube_of_dist_le {d : ℕ} (K L : Body d)
    {h : ℝ} (hh : 0 ≤ h) (hKL : dist K L ≤ h) : K ≤ L + h • coordinateCube d := by
  first
  | rcases hh.eq_or_lt with heq | hpos
    · have hz : h = 0 := heq.symm
      rw [hz] at hKL ⊢
      have hsame : K = L := dist_le_zero.mp hKL
      rw [hsame, body_zero_smul, add_zero]
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
      have hnorm : ‖x - y‖ ≤ h := by
        first
        | rw [← dist_eq_norm, ← hxy]
          exact (infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top).trans hKL
      let u : Space d := h⁻¹ • (x - y)
      have hu : u ∈ coordinateCube d := by
        first
        | have habs : ∀ i, |u i| ≤ 1 := by
            intro i
            have hi : |(x - y) i| ≤ h := by
              calc
                |(x - y) i| = ‖(x - y) i‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
                _ ≤ h := hnorm
            change |h⁻¹ * (x - y) i| ≤ 1
            rw [abs_mul, abs_inv, abs_of_pos hpos]
            calc
              h⁻¹ * |(x - y) i| ≤ h⁻¹ * h :=
                mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hpos.le)
              _ = 1 := inv_mul_cancel₀ hpos.ne'
          exact ⟨fun i => (abs_le.mp (habs i)).1, fun i => (abs_le.mp (habs i)).2⟩
      have hscaled : h • u = x - y := by
        first
        | simp only [u, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      exact Set.mem_add.mpr ⟨y, hy, x - y, ⟨u, hu, hscaled⟩, by abel⟩

theorem bodyVolume_add_coordinateCube_le {d : ℕ} (K : Body d) {R : ℝ}
    (hR : 0 ≤ R) (hK : (K : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R)) :
    bodyVolume (K + coordinateCube d) ≤ (2 * R + 2) ^ d := by
  first
  | have hsub : ((K + coordinateCube d : Body d) : Set (Space d)) ⊆
        Icc (fun _ => -(R + 1)) (fun _ => R + 1) := by
      first
      | rintro _ ⟨x, hx, y, hy, rfl⟩
        have hx' := hK hx
        change y ∈ Icc (fun _ : Fin d => (-1 : ℝ)) (fun _ => (1 : ℝ)) at hy
        constructor
        · intro i
          change -(R + 1) ≤ x i + y i
          linarith [hx'.1 i, hy.1 i]
        · intro i
          change x i + y i ≤ R + 1
          linarith [hx'.2 i, hy.2 i]
    have hbound := measureReal_mono hsub
      (show volume (Icc (fun _ : Fin d => -(R + 1)) (fun _ => R + 1)) ≠ ⊤ from
        isCompact_Icc.measure_lt_top.ne)
    have hbox : volume.real (Icc (fun _ : Fin d => -(R + 1)) (fun _ => R + 1)) =
        (2 * R + 2) ^ d := by
      first
      | rw [measureReal_def, Real.volume_Icc_pi_toReal
          (show (fun _ : Fin d => -(R + 1)) ≤ (fun _ => R + 1) from
            fun _ => by linarith)]
        simp only [show R + 1 - -(R + 1) = 2 * R + 2 by ring,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hbound.trans_eq hbox

/-- Explicit uniform continuity of volume on all convex bodies in the box,
including arbitrarily thin and lower-dimensional ones. -/
theorem abs_bodyVolume_sub_le_of_dist_le {d : ℕ} (K L : Body d) {R h : ℝ}
    (hR : 0 ≤ R) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hK : (K : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R))
    (hL : (L : Set (Space d)) ⊆ Icc (fun _ => -R) (fun _ => R))
    (hKL : dist K L ≤ h) :
    |bodyVolume K - bodyVolume L| ≤ h * (2 * R + 2) ^ d := by
  first
  | have hforward : bodyVolume K - bodyVolume L ≤ h * (2 * R + 2) ^ d := by
      first
      | calc
          _ ≤ bodyVolume (L + h • coordinateCube d) - bodyVolume L :=
            sub_le_sub_right (bodyVolume_mono (body_le_add_coordinateCube_of_dist_le K L hh0 hKL)) _
          _ ≤ h * bodyVolume (L + coordinateCube d) := bodyVolume_add_smul_sub_le L _ hh0 hh1
          _ ≤ h * (2 * R + 2) ^ d :=
            mul_le_mul_of_nonneg_left (bodyVolume_add_coordinateCube_le L hR hL) hh0
    have hreverse : bodyVolume L - bodyVolume K ≤ h * (2 * R + 2) ^ d := by
      first
      | calc
          _ ≤ bodyVolume (K + h • coordinateCube d) - bodyVolume K :=
            sub_le_sub_right (bodyVolume_mono (body_le_add_coordinateCube_of_dist_le L K hh0
              (by rwa [dist_comm]))) _
          _ ≤ h * bodyVolume (K + coordinateCube d) := bodyVolume_add_smul_sub_le K _ hh0 hh1
          _ ≤ h * (2 * R + 2) ^ d :=
            mul_le_mul_of_nonneg_left (bodyVolume_add_coordinateCube_le K hR hK) hh0
    exact abs_le.mpr ⟨by linarith, hforward⟩

end VolumePolynomials
end -- closes the original EOF section from source line 12
end -- closes the original EOF section from source line 9
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/VolumeLipschitz.lean -/

/- BEGIN SOURCE: VolumePolynomials/PolytopeDensity.lean -/
section

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The coefficient locus of full-dimensional polytopes

An inscribed finite convex hull followed by arbitrarily small cube addition
approximates every convex body by a full-dimensional polytope. Consequently the
closure of the coefficient locus of such tuples is the whole realization locus.
This gives the full-dimensional-polytope clause of the threshold theorem from
the corresponding nonsemialgebraicity theorem for arbitrary convex bodies.
-/

open Set Metric Topology
open scoped Pointwise

namespace VolumePolynomials
open PolytopeGeometry

theorem coordinateCube_isFiniteHull (d : ℕ) :
    IsFiniteHull (coordinateCube d : Set (Space d)) := by
  first
  | let V : Set (Space d) := Set.pi Set.univ (fun _ => ({-1, 1} : Set ℝ))
    refine ⟨V, Set.Finite.pi (fun _ => (Set.finite_singleton (1 : ℝ)).insert (-1)), ?_⟩
    change Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) = convexHull ℝ V
    dsimp only [V]
    rw [convexHull_pi]
    simp only [convexHull_pair, segment_eq_Icc (show (-1 : ℝ) ≤ 1 by norm_num)]
    ext x
    simp only [Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩,
      fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The interior condition is literal ambient interior, so every body obtained
here is full dimensional even when the original body is a point. -/
theorem interior_add_smul_coordinateCube_nonempty {d : ℕ} (P : Body d)
    {t : ℝ} (ht : 0 < t) :
    (interior ((P + t • coordinateCube d : Body d) : Set (Space d))).Nonempty := by
  first
  | obtain ⟨x, hx⟩ := P.nonempty
    refine ⟨x, mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨t, ht, ?_⟩)⟩
    intro y hy
    have hnorm : ‖y - x‖ ≤ t := by
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le
    let u : Space d := t⁻¹ • (y - x)
    have hu : u ∈ coordinateCube d := by
      have hi (i : Fin d) : |u i| ≤ 1 := by
        have hcoord : |(y - x) i| ≤ t := by
          calc
            |(y - x) i| = ‖(y - x) i‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖y - x‖ := norm_le_pi_norm (y - x) i
            _ ≤ t := hnorm
        change |t⁻¹ * (y - x) i| ≤ 1
        rw [abs_mul, abs_inv, abs_of_pos ht]
        calc
          t⁻¹ * |(y - x) i| ≤ t⁻¹ * t :=
            mul_le_mul_of_nonneg_left hcoord (inv_nonneg.mpr ht.le)
          _ = 1 := inv_mul_cancel₀ ht.ne'
      exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
    have hscale : t • u = y - x := by
      simp only [u, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    exact Set.mem_add.mpr ⟨x, hx, y - x, ⟨u, hu, hscale⟩, by abel⟩

def FullDimensionalPolytope {d : ℕ} (K : Body d) : Prop :=
  IsFiniteHull (K : Set (Space d)) ∧ (interior (K : Set (Space d))).Nonempty

theorem exists_near_fullDimensionalPolytope {d : ℕ} (K : Body d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Body d, FullDimensionalPolytope P ∧ dist P K < ε := by
  first
  | obtain ⟨P, hpoly, _, hPK⟩ := exists_inscribed_finiteHullBody K (half_pos hε)
    have hc : Continuous (fun t : ℝ => P + t • coordinateCube d) := by fun_prop
    obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := (0 : ℝ)))
      (ε / 2) (half_pos hε)
    let t : ℝ := δ / 2
    have ht : 0 < t := half_pos hδ
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      exact half_lt_self hδ
    let Q : Body d := P + t • coordinateCube d
    have hQP : dist Q P < ε / 2 := by
      simpa only [body_zero_smul, add_zero] using hnear htδ
    refine ⟨Q, ⟨?_, interior_add_smul_coordinateCube_nonempty P ht⟩, ?_⟩
    · exact hpoly.add ((coordinateCube_isFiniteHull d).smul t)
    · calc
        dist Q K ≤ dist Q P + dist P K := dist_triangle Q P K
        _ < ε / 2 + ε / 2 := add_lt_add hQP hPK
        _ = ε := by ring

theorem dense_fullDimensionalPolytopes (d : ℕ) :
    Dense {K : Body d | FullDimensionalPolytope K} := by
  first
  | rw [Metric.dense_iff]
    intro K ε hε
    obtain ⟨P, hP, hPK⟩ := exists_near_fullDimensionalPolytope K hε
    exact ⟨P, hPK, hP⟩

theorem dense_fullDimensionalPolytopeTuples (n d : ℕ) :
    Dense {K : Fin n → Body d | ∀ i, FullDimensionalPolytope (K i)} := by
  first
  | simpa [Set.pi] using
      dense_pi Set.univ (fun (_ : Fin n) _ => dense_fullDimensionalPolytopes d)

def FullDimensionalPolytopeLocus (n d : ℕ) : Set (Coefficients n d) :=
  {c | ∃ K : Fin n → Body d, (∀ i, FullDimensionalPolytope (K i)) ∧ Realizes K c}

theorem fullDimensionalPolytopeLocus_eq_image (n d : ℕ) :
    FullDimensionalPolytopeLocus n d =
      coefficientMap '' {K : Fin n → Body d | ∀ i, FullDimensionalPolytope (K i)} := by
  first
  | ext c
    constructor
    · rintro ⟨K, hK, hc⟩
      exact ⟨K, hK, hc.eq_coefficientMap.symm⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, hK, coefficientMap_realizes K⟩

theorem closure_fullDimensionalPolytopeLocus (n d : ℕ) (hd : 0 < d) :
    closure (FullDimensionalPolytopeLocus n d) = VolumeLocus n d := by
  first
  | rw [fullDimensionalPolytopeLocus_eq_image]
    exact closure_coefficientMap_image_of_dense hd (dense_fullDimensionalPolytopeTuples n d)

end VolumePolynomials
end -- closes the original EOF section from source line 7
end -- closes the original EOF section from source line 5
end -- closes the synthetic per-file scope
/- END SOURCE: VolumePolynomials/PolytopeDensity.lean -/

/- BEGIN SOURCE: TauCeti/Topology/LocallyConstant/Preconnected.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Locally constant functions on a preconnected set

A function that is locally constant along a preconnected set takes the same value everywhere on
it. Mathlib's `IsLocallyConstant.apply_eq_of_preconnectedSpace` says this for a locally constant
function on a preconnected *space*; the statement below is the relative form, for a preconnected
subset `s` of an ambient space, with local constancy expressed by the `𝓝[s]` neighbourhood filter
rather than by passing to the subtype.

## Main declarations

* `IsPreconnected.apply_eq_of_eventually_eq`: a function whose value is locally constant along a
  preconnected set is constant along it.

The example at the end of the file spells the statement out on the interval `[0, 1] ⊆ ℝ`, where it
says that a map into a discrete space continuous on `[0, 1]` cannot take two different values
there. That is the obstruction to extending a discrete-valued map off a closed subspace of a
space that is not totally disconnected.
-/

public section

open Filter Topology

namespace IsPreconnected

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A function that is locally constant along a preconnected set is constant along it.

This is `IsLocallyConstant.apply_eq_of_preconnectedSpace` transported to the subspace `s`, and
the special case of `IsPreconnected.induction₂` for the relation `f y = f x`. -/
theorem apply_eq_of_eventually_eq {Y : Type*} {f : X → Y} (hs : IsPreconnected s)
    (hf : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, f u = f t) {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b :=
  hs.induction₂ (fun x y => f y = f x) hf (fun _ _ _ _ _ _ hxy hyz => hyz.trans hxy)
    (fun _ _ _ _ => Eq.symm) hb ha

end IsPreconnected

/-- On the preconnected set `[0, 1] ⊆ ℝ`, a map into a discrete space that is continuous there
takes the same value at `0` and at `1`; continuity on a discrete-valued map is local constancy. -/
example {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y] {a b : Y} (hab : a ≠ b) :
    ¬ ∃ g : ℝ → Y, ContinuousOn g (Set.Icc 0 1) ∧ g 0 = a ∧ g 1 = b := by
  first
  | rintro ⟨g, hg, rfl, rfl⟩
    -- The singleton `{g t}` is open, so its preimage is a neighbourhood of `t` within `[0, 1]`.
    have h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᶠ u in 𝓝[Set.Icc (0 : ℝ) 1] t, g u = g t := fun t ht =>
      (hg t ht).preimage_mem_nhdsWithin ((isOpen_discrete {g t}).mem_nhds rfl)
    exact hab (isPreconnected_Icc.apply_eq_of_eventually_eq h (by norm_num) (by norm_num))
end -- closes the original EOF section from source line 33
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Topology/LocallyConstant/Preconnected.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/SignInvariant.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sign-invariant functions

A function `f` is *sign-invariant* on a set `s` when it has the same sign at any two points of
`s`, where the sign `SignType.sign` takes the values `-1`, `0` and `1`. In particular a function
that vanishes somewhere on `s` is sign-invariant on `s` only if it vanishes on all of `s`. This is
the invariance asked of the cells of a cylindrical algebraic decomposition adapted to a family of
polynomials: each polynomial of the family is sign-invariant on each cell.

The basic source of sign-invariance is connectedness: a function that is continuous and nowhere
zero on a preconnected set is sign-invariant there, since its sign is a continuous map to the
discrete space `SignType`.

Sign-invariance is preserved by restriction, by precomposition, and by the operations whose result
has a sign determined by the signs of the inputs: negation, products and powers.

A set on which each function of a family is sign-invariant lies inside or outside each set
described by a condition on their signs. If the sets of a cover each have this property, one sample
point from each of them realizes every sign vector that the functions take.

## Main declarations

* `TauCeti.SignInvariant`: sign-invariance of a function on a set.
* `TauCeti.signInvariant_iff_exists`: a sign-invariant function has a single sign on the set.
* `TauCeti.signInvariant_image`: sign-invariance on an image is sign-invariance of the
  composite.
* `TauCeti.SignInvariant.comp`, `TauCeti.SignInvariant.union`: precomposition with a map into
  the set, and unions of two sets that meet.
* `TauCeti.SignInvariant.neg`, `TauCeti.SignInvariant.mul`, `TauCeti.SignInvariant.pow`,
  `TauCeti.signInvariant_finsetProd`: negations, products, powers and finite products of
  sign-invariant functions are sign-invariant.
* `TauCeti.subset_or_disjoint_setOf_sign`: a set on which the functions are sign-invariant lies
  inside or outside each sign-condition set.
* `TauCeti.range_sign_sample_eq`: sample points of a cover by sets on which the functions are
  sign-invariant realize all their sign vectors.
* `IsPreconnected.signInvariant`: a continuous, nowhere-zero function on a preconnected set is
  sign-invariant.
* `IsPreconnected.signInvariant_of_eq_zero_iff`: a continuous function on a preconnected set that
  vanishes everywhere or nowhere there is sign-invariant.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1.
-/

public section

open Set

namespace TauCeti

variable {α β R : Type*}

section Preorder

variable [Zero R] [Preorder R] [DecidableLT R]

/-- A function `f` is sign-invariant on `s` if it has the same sign, possibly zero, at any two
points of `s`. -/
def SignInvariant (f : α → R) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, SignType.sign (f x) = SignType.sign (f y)

variable {f g : α → R} {s t : Set α}

theorem signInvariant_def :
    SignInvariant f s ↔ ∀ x ∈ s, ∀ y ∈ s, SignType.sign (f x) = SignType.sign (f y) :=
  Iff.rfl

/-- A function is sign-invariant on `s` exactly when a single sign is taken at every point of
`s`. -/
theorem signInvariant_iff_exists :
    SignInvariant f s ↔ ∃ σ : SignType, ∀ x ∈ s, SignType.sign (f x) = σ := by
  first
  | refine ⟨fun h ↦ ?_, fun ⟨σ, hσ⟩ x hx y hy ↦ (hσ x hx).trans (hσ y hy).symm⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨0, by simp⟩
    · exact ⟨SignType.sign (f x), fun y hy ↦ h y hy x hx⟩

theorem SignInvariant.mono (h : SignInvariant f t) (hst : s ⊆ t) : SignInvariant f s :=
  fun x hx y hy ↦ h x (hst hx) y (hst hy)

theorem SignInvariant.congr (h : SignInvariant f s) (hfg : EqOn f g s) : SignInvariant g s :=
  fun x hx y hy ↦ by rw [← hfg hx, ← hfg hy]; exact h x hx y hy

/-- Sign-invariance on an image is sign-invariance of the composite on the source set. -/
theorem signInvariant_image {u : β → α} {s : Set β} :
    SignInvariant f (u '' s) ↔ SignInvariant (f ∘ u) s := by
  first
  | simp [SignInvariant]

/-- Sign-invariance is preserved by precomposition with a map into the set. -/
theorem SignInvariant.comp (h : SignInvariant f t) {u : β → α} {s : Set β} (hu : MapsTo u s t) :
    SignInvariant (f ∘ u) s :=
  fun x hx y hy ↦ h (u x) (hu hx) (u y) (hu hy)

/-- Sign-invariance on two sets that meet is sign-invariance on their union. -/
theorem SignInvariant.union (hs : SignInvariant f s) (ht : SignInvariant f t)
    (hst : (s ∩ t).Nonempty) : SignInvariant f (s ∪ t) := by
  first
  | obtain ⟨z, hzs, hzt⟩ := hst
    have key : ∀ x ∈ s ∪ t, SignType.sign (f x) = SignType.sign (f z) := by
      rintro x (hx | hx)
      exacts [hs x hx z hzs, ht x hx z hzt]
    exact fun x hx y hy ↦ (key x hx).trans (key y hy).symm

/-- A function is sign-invariant on a set containing at most one point. -/
theorem _root_.Set.Subsingleton.signInvariant (hs : s.Subsingleton) : SignInvariant f s :=
  fun x hx y hy ↦ by rw [hs hx hy]

@[simp]
theorem signInvariant_empty : SignInvariant f ∅ :=
  subsingleton_empty.signInvariant

@[simp]
theorem signInvariant_singleton (a : α) : SignInvariant f {a} :=
  subsingleton_singleton.signInvariant

/-- A constant function is sign-invariant on every set. -/
@[simp]
theorem signInvariant_const (c : R) : SignInvariant (fun _ : α ↦ c) s :=
  fun _ _ _ _ ↦ rfl

/-! ### Sign conditions -/

section SignCondition

variable {ι : Type*} {f : ι → α → R}

/-- If each function `f i` is sign-invariant on `t`, then `t` lies inside or outside every set
described by a condition on the signs of the `f i`. -/
theorem subset_or_disjoint_setOf_sign (hf : ∀ i, SignInvariant (f i) t)
    (Φ : (ι → SignType) → Prop) :
    t ⊆ {x | Φ fun i ↦ SignType.sign (f i x)} ∨
      Disjoint t {x | Φ fun i ↦ SignType.sign (f i x)} := by
  first
  | by_cases h : ∃ x ∈ t, Φ fun i ↦ SignType.sign (f i x)
    · obtain ⟨x, hx, hΦ⟩ := h
      refine .inl fun y hy ↦ ?_
      rwa [mem_ofPred_eq, funext fun i ↦ hf i y hy x hx]
    · exact .inr <| disjoint_left.2 fun x hx hΦ ↦ h ⟨x, hx, hΦ⟩

/-- **Sample points realize all sign conditions.** Let the functions `f i` be sign-invariant on
each set of a family `𝒞` covering `α`, and pick a sample point `x E` in each `E ∈ 𝒞`. Then the
sign vectors of the `f i` at the sample points are exactly the sign vectors they take on `α`. -/
theorem range_sign_sample_eq {𝒞 : Set (Set α)} (h𝒞 : ⋃₀ 𝒞 = univ)
    (hf : ∀ i, ∀ E ∈ 𝒞, SignInvariant (f i) E) (x : 𝒞 → α) (hx : ∀ E : 𝒞, x E ∈ (E : Set α)) :
    (range fun E i ↦ SignType.sign (f i (x E))) = range fun y i ↦ SignType.sign (f i y) := by
  first
  | refine (range_comp_subset_range x fun y i ↦ SignType.sign (f i y)).antisymm ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨E, hE, hy⟩ := mem_sUnion.1 (h𝒞 ▸ mem_univ y)
    exact ⟨⟨E, hE⟩, funext fun i ↦ hf i E hE _ (hx ⟨E, hE⟩) y hy⟩

end SignCondition

end Preorder

/-! ### Algebraic operations

The sign of a negation, a product or a power is determined by the signs of its inputs, so these
operations preserve sign-invariance. -/

section AddGroup

variable [AddGroup R] [Preorder R] [DecidableLT R] [AddLeftStrictMono R] {f : α → R} {s : Set α}

/-- The negation of a sign-invariant function is sign-invariant. -/
theorem SignInvariant.neg (h : SignInvariant f s) : SignInvariant (fun x ↦ -f x) s :=
  fun x hx y hy ↦ by simp only [Left.sign_neg, h x hx y hy]

/-- A function is sign-invariant exactly when its negation is. -/
@[simp]
theorem signInvariant_neg_iff : SignInvariant (fun x ↦ -f x) s ↔ SignInvariant f s :=
  ⟨fun h ↦ by simpa using h.neg, SignInvariant.neg⟩

end AddGroup

section Ring

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {f g : α → R} {s : Set α}

/-- The product of two sign-invariant functions is sign-invariant. -/
theorem SignInvariant.mul (hf : SignInvariant f s) (hg : SignInvariant g s) :
    SignInvariant (fun x ↦ f x * g x) s :=
  fun x hx y hy ↦ by simp only [sign_mul, hf x hx y hy, hg x hx y hy]

/-- A power of a sign-invariant function is sign-invariant. -/
theorem SignInvariant.pow (hf : SignInvariant f s) (n : ℕ) :
    SignInvariant (fun x ↦ f x ^ n) s :=
  fun x hx y hy ↦ by simp only [sign_pow, hf x hx y hy]

end Ring

/-- A finite product of sign-invariant functions is sign-invariant. -/
theorem signInvariant_finsetProd [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {ι : Type*}
    {f : ι → α → R} {s : Set α} (I : Finset ι) (hf : ∀ i ∈ I, SignInvariant (f i) s) :
    SignInvariant (fun x ↦ ∏ i ∈ I, f i x) s := by
  first
  | intro x hx y hy
    simp only [← signHom_apply, map_prod]
    exact Finset.prod_congr rfl fun i hi ↦ hf i hi x hx y hy

/-- A function that is continuous and nowhere zero on a preconnected set is sign-invariant
there. -/
theorem _root_.IsPreconnected.signInvariant [Zero R] [LinearOrder R] [TopologicalSpace R]
    [OrderTopology R] [TopologicalSpace α] {f : α → R} {s : Set α} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) : SignInvariant f s :=
  fun _ hx _ hy ↦ hs.constant (f := fun x ↦ SignType.sign (f x))
    (fun z hz ↦ (continuousAt_sign_of_ne_zero (h0 z hz)).comp_continuousWithinAt (hf z hz)) hx hy

/-- A function that is continuous on a preconnected set, and vanishes either at every point of
the set or at none, is sign-invariant there. -/
theorem _root_.IsPreconnected.signInvariant_of_eq_zero_iff [Zero R] [LinearOrder R]
    [TopologicalSpace R] [OrderTopology R] [TopologicalSpace α] {f : α → R} {s : Set α}
    (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (h0 : ∀ x ∈ s, ∀ y ∈ s, f x = 0 ↔ f y = 0) : SignInvariant f s := by
  first
  | intro x hx y hy
    by_cases hfx : f x = 0
    · rw [hfx, (h0 x hx y hy).1 hfx]
    · exact hs.signInvariant hf (fun z hz hfz ↦ hfx ((h0 x hx z hz).2 hfz)) x hx y hy

/-- Local sign-invariance on relative neighborhoods implies sign-invariance on a preconnected
set. No continuity of the function itself is required. -/
theorem _root_.IsPreconnected.signInvariant_of_locally [Zero R] [Preorder R] [DecidableLT R]
    [TopologicalSpace α] {f : α → R} {s : Set α} (hs : IsPreconnected s)
    (hlocal : ∀ x ∈ s, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ SignInvariant f (s ∩ U)) :
    SignInvariant f s := by
  first
  | rw [signInvariant_def]
    refine fun x hx y hy ↦ hs.apply_eq_of_eventually_eq
      (f := fun a ↦ SignType.sign (f a)) (fun a ha ↦ ?_) hx hy
    obtain ⟨U, hU, haU, h⟩ := hlocal a ha
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds haU)] with b hb hbU
    exact h b ⟨hb, hbU⟩ a ⟨ha, haU⟩

end TauCeti
end -- closes the original EOF section from source line 60
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/SignInvariant.lean -/

/- BEGIN SOURCE: TauCeti/Topology/Connected/Prod.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Preconnected sets in a product with preconnected fibres

A subset of `X × Y` over a preconnected base need not be preconnected even when every vertical
fibre is: the fibres may fail to be linked to one another. They are linked as soon as the set
contains the graph of a continuous map `X → Y`, since that graph is preconnected and meets every
fibre. This is how one shows that the regions between continuous graphs over a connected base,
such as the sectors of a cylindrical stack, are connected.

## Main declarations

* `TauCeti.isPreconnected_of_isPreconnected_preimage_prodMk`: a set with preconnected fibres
  containing the graph of a continuous map over a preconnected base is preconnected.
-/

public section

open Set

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Over a preconnected base, a set `s ⊆ X × Y` is preconnected if each of its fibres
`{y | (x, y) ∈ s}` is preconnected and it contains the graph of a continuous map `f : X → Y`. -/
theorem isPreconnected_of_isPreconnected_preimage_prodMk [PreconnectedSpace X]
    {s : Set (X × Y)} {f : X → Y} (hf : Continuous f) (hfs : ∀ x, (x, f x) ∈ s)
    (hs : ∀ x, IsPreconnected (Prod.mk x ⁻¹' s)) : IsPreconnected s := by
  first
  | rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
    · rw [eq_empty_of_isEmpty s]
      exact isPreconnected_empty
    -- Every point is joined to `(x₀, f x₀)` through its fibre followed by the graph of `f`.
    refine isPreconnected_of_forall (x₀, f x₀) fun z hz ↦
      ⟨Prod.mk z.1 '' (Prod.mk z.1 ⁻¹' s) ∪ range fun x ↦ (x, f x), ?_, Or.inr ⟨x₀, rfl⟩,
        Or.inl ⟨z.2, hz, rfl⟩, ?_⟩
    · rintro _ (⟨y, hy, rfl⟩ | ⟨x, rfl⟩)
      exacts [hy, hfs x]
    · exact ((hs z.1).image _ (Continuous.prodMk_right z.1).continuousOn).union (z.1, f z.1)
        ⟨f z.1, hfs z.1, rfl⟩ ⟨z.1, rfl⟩ (isPreconnected_range (by fun_prop))

end TauCeti
end -- closes the original EOF section from source line 25
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Topology/Connected/Prod.lean -/

/- BEGIN SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Basic.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sections and sectors of a stack

A finite family of functions `θ₀ < θ₁ < … < θₖ₋₁` on a base `X` cuts the cylinder `X × α` into a
*stack*: the `k` *sections*, which are the graphs of the `θᵢ`, and the `k + 1` open *sectors*
between consecutive graphs, the lowest and highest sectors being unbounded. These are the cells
built over a base cell when a cylindrical algebraic decomposition is lifted by one dimension.

This file develops the stack geometry for arbitrary functions, independently of the polynomials
whose roots they will be. Sector `j` is defined as the set of points lying above exactly the first
`j` sections. When the functions are ordered pointwise this is the region between section `j - 1`
and section `j`, and the sections and sectors partition the cylinder. For continuous, strictly
ordered functions on a connected base, each sector carries a continuous section, so every part
projects onto the whole base, and every section and sector of a real stack is connected. Finally
`TauCeti.cylinder` places the cylinder over a subset `S` of the coordinate space inside the
coordinate space of one more dimension, with the distinguished coordinate first; it is a
topological embedding, so connectedness of stack cells transfers to their ambient images, the
cells `TauCeti.stackCells` of the stack in the ambient space.

## Main declarations

* `TauCeti.sectionSet`, `TauCeti.sectorSet`: the sections and sectors of a stack.
* `TauCeti.mem_sectorSet_iff_of_monotone`: for ordered functions, a sector is cut out by the two
  adjacent sections.
* `TauCeti.iUnion_sectionSet_union_iUnion_sectorSet`, `TauCeti.pairwise_disjoint_sectionSet`,
  `TauCeti.pairwise_disjoint_sectorSet`, `TauCeti.disjoint_sectionSet_sectorSet`: the sections and
  sectors partition the cylinder.
* `TauCeti.sectionSet_nonempty`, `TauCeti.sectorSet_nonempty`: over a nonempty base, every section
  and every sector of a strictly ordered stack is nonempty.
* `TauCeti.sectorSet_castSucc_succ_eq_image`, `TauCeti.sectorSet_zero_eq_image`,
  `TauCeti.sectorSet_last_eq_image`: a bounded sector is the image of `X × (0, 1)`, and the lowest
  and highest sectors are the images of `X × (-∞, 0)` and `X × (0, ∞)`, under explicit maps that
  are continuous whenever the functions of the stack are, for a topological ring `α` (continuous
  addition suffices for the two unbounded sectors).
* `TauCeti.exists_continuous_forall_mem_sectorSet`: every sector of a continuous strictly ordered
  stack contains the graph of a continuous function.
* `TauCeti.isConnected_sectionSet`, `TauCeti.isConnected_sectorSet`: over a connected base, the
  sections and sectors of a continuous strictly ordered real stack are connected.
* `TauCeti.cylinder`, `TauCeti.isEmbedding_cylinder`: the ambient cylinder embedding.
* `TauCeti.stackCells`: the ambient sections and sectors of a stack over a subset of `α ^ n`.
* `TauCeti.image_cylinder_sectionSet_comp`, `TauCeti.image_cylinder_sectorSet_comp`,
  `TauCeti.stackCells_comp`: ambient stack cells pull back along arbitrary base maps.
* `TauCeti.stackCells_inclusion`: restricting a stack to a subset of its base cuts each ambient
  cell down to the part lying over that subset.
* `TauCeti.sUnion_stackCells`, `TauCeti.pairwiseDisjoint_stackCells`,
  `TauCeti.isConnected_of_mem_stackCells`: the ambient cells of a stack partition the cylinder
  over its base, and over a connected base they are connected.
* `TauCeti.ordConnected_setOf_cons_mem_of_mem_stackCells`: every ambient cell meets each line
  parallel to the distinguished axis in an order-connected set.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1.
-/

public section

open Function Set Topology

namespace TauCeti

variable {X Y α : Type*} {k : ℕ}

/-! ### Sections and sectors -/

section Order

/-- The `i`-th section of the stack defined by `θ`: the graph `Function.graph (θ i)` of `θ i`
in the cylinder `X × α`. -/
def sectionSet (θ : Fin k → X → α) (i : Fin k) : Set (X × α) :=
  (θ i).graph

@[simp]
theorem mem_sectionSet {θ : Fin k → X → α} {i : Fin k} {z : X × α} :
    z ∈ sectionSet θ i ↔ θ i z.1 = z.2 :=
  Iff.rfl

/-- A section is the range of the graph map of its function. -/
theorem sectionSet_eq_range (θ : Fin k → X → α) (i : Fin k) :
    sectionSet θ i = range fun x ↦ (x, θ i x) := by
  first
  | ext ⟨x, t⟩
    simp

/-- Sections pull back along a change of base. -/
theorem sectionSet_comp (θ : Fin k → X → α) (f : Y → X) (i : Fin k) :
    sectionSet (fun i ↦ θ i ∘ f) i = Prod.map f id ⁻¹' sectionSet θ i :=
  (rfl)

/-- Each section lies over the whole base. -/
@[simp]
theorem fst_image_sectionSet (θ : Fin k → X → α) (i : Fin k) :
    Prod.fst '' sectionSet θ i = univ :=
  eq_univ_of_forall fun x ↦ ⟨(x, θ i x), rfl, rfl⟩

/-- Over a nonempty base, every section is nonempty. -/
@[simp]
theorem sectionSet_nonempty [Nonempty X] (θ : Fin k → X → α) (i : Fin k) :
    (sectionSet θ i).Nonempty := by
  first
  | rw [← image_nonempty (f := Prod.fst), fst_image_sectionSet]
    exact univ_nonempty

/-- Distinct sections of a stack whose functions are pointwise injective in the index are
disjoint. -/
theorem pairwise_disjoint_sectionSet {θ : Fin k → X → α}
    (hθ : ∀ x, Injective fun i ↦ θ i x) : Pairwise (Disjoint on sectionSet θ) := by
  first
  | refine fun i i' hii' ↦ disjoint_left.2 fun z hz hz' ↦ hii' (hθ z.1 ?_)
    simp only [mem_sectionSet] at hz hz'
    exact hz.trans hz'.symm

variable [LinearOrder α] {θ : Fin k → X → α}

/-- The `j`-th sector of the stack defined by `θ`, for `j ≤ k`: the points of `X × α` lying
strictly above the first `j` sections and strictly below the others. When there are no sections
the only sector is the whole cylinder. -/
def sectorSet (θ : Fin k → X → α) (j : Fin (k + 1)) : Set (X × α) :=
  {z | (∀ i : Fin k, i.castSucc < j → θ i z.1 < z.2) ∧
    ∀ i : Fin k, j ≤ i.castSucc → z.2 < θ i z.1}

@[simp]
theorem mem_sectorSet {j : Fin (k + 1)} {z : X × α} :
    z ∈ sectorSet θ j ↔ (∀ i : Fin k, i.castSucc < j → θ i z.1 < z.2) ∧
      ∀ i : Fin k, j ≤ i.castSucc → z.2 < θ i z.1 :=
  Iff.rfl

/-- A stack with no sections has the whole cylinder as its unique sector. -/
@[simp]
theorem sectorSet_fin_zero (θ : Fin 0 → X → α) (j : Fin 1) : sectorSet θ j = univ := by
  first
  | ext z
    simp

/-- Sectors pull back along a change of base. -/
theorem sectorSet_comp (θ : Fin k → X → α) (f : Y → X) (j : Fin (k + 1)) :
    sectorSet (fun i ↦ θ i ∘ f) j = Prod.map f id ⁻¹' sectorSet θ j :=
  (rfl)

/-- Each fibre of a sector is order-connected: it is an open interval of `α`, possibly
unbounded. -/
theorem ordConnected_preimage_mk_sectorSet (θ : Fin k → X → α) (j : Fin (k + 1)) (x : X) :
    (Prod.mk x ⁻¹' sectorSet θ j).OrdConnected :=
  ⟨fun _ ha _ hb _ ht ↦ ⟨fun i hi ↦ (ha.1 i hi).trans_le ht.1,
    fun i hi ↦ ht.2.trans_lt (hb.2 i hi)⟩⟩

/-- For pointwise monotone `θ`, a point lies in sector `j` exactly when it is above section
`j - 1` (if `0 < j`) and below section `j` (if `j < k`). -/
theorem mem_sectorSet_iff_of_monotone (hθ : ∀ x, Monotone fun i ↦ θ i x) {j : Fin (k + 1)}
    {z : X × α} :
    z ∈ sectorSet θ j ↔ (∀ i : Fin k, i.succ = j → θ i z.1 < z.2) ∧
      ∀ i : Fin k, i.castSucc = j → z.2 < θ i z.1 := by
  first
  | refine ⟨fun h ↦ ⟨fun i hi ↦ h.1 i (hi ▸ Fin.castSucc_lt_succ), fun i hi ↦ h.2 i hi.ge⟩,
      fun h ↦ ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩⟩
    · -- The section just below sector `j` lies above section `i`.
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero (Fin.ne_zero_of_lt hi)
      exact (hθ z.1 (Fin.castSucc_lt_succ_iff.1 hi)).trans_lt (h.1 j' rfl)
    · -- The section just above sector `j` lies below section `i`.
      obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 (hi.trans_lt (Fin.castSucc_lt_last i)).ne
      exact (h.2 j' rfl).trans_le (hθ z.1 (Fin.castSucc_le_castSucc_iff.1 hi))

/-- For pointwise monotone `θ`, the lowest sector lies below the lowest section. -/
theorem sectorSet_zero {θ : Fin (k + 1) → X → α} (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ 0 = {z | z.2 < θ 0 z.1} := by
  first
  | ext z
    rw [mem_sectorSet_iff_of_monotone hθ]
    exact ⟨fun h ↦ h.2 0 rfl, fun h ↦ ⟨fun i hi ↦ absurd hi (Fin.succ_ne_zero i),
      fun i hi ↦ by rwa [Fin.castSucc_eq_zero_iff.1 hi]⟩⟩

/-- For pointwise monotone `θ`, the highest sector lies above the highest section. -/
theorem sectorSet_last {θ : Fin (k + 1) → X → α} (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ (Fin.last (k + 1)) = {z | θ (Fin.last k) z.1 < z.2} := by
  first
  | ext z
    rw [mem_sectorSet_iff_of_monotone hθ]
    exact ⟨fun h ↦ h.1 _ (Fin.succ_last k), fun h ↦ ⟨fun i hi ↦ by rwa [Fin.succ_eq_last_succ.1 hi],
      fun i hi ↦ absurd hi (Fin.castSucc_ne_last i)⟩⟩

/-- For pointwise monotone `θ`, a bounded sector lies between two consecutive sections. -/
theorem sectorSet_castSucc_succ {θ : Fin (k + 1) → X → α} (hθ : ∀ x, Monotone fun i ↦ θ i x)
    (i : Fin k) :
    sectorSet θ i.castSucc.succ = {z | θ i.castSucc z.1 < z.2 ∧ z.2 < θ i.succ z.1} := by
  first
  | ext z
    rw [mem_sectorSet_iff_of_monotone hθ]
    refine ⟨fun h ↦ ⟨h.1 _ rfl, h.2 _ (Fin.succ_castSucc i).symm⟩,
      fun h ↦ ⟨fun i' hi ↦ ?_, fun i' hi ↦ ?_⟩⟩
    · rw [Fin.succ_inj.1 hi]
      exact h.1
    · rw [Fin.castSucc_inj.1 (hi.trans (Fin.succ_castSucc i))]
      exact h.2

/-- Distinct sectors of a stack are disjoint. -/
theorem pairwise_disjoint_sectorSet (θ : Fin k → X → α) :
    Pairwise (Disjoint on sectorSet θ) := by
  first
    -- The section with the index of the lower sector separates the two sectors.
  | suffices ∀ j j' : Fin (k + 1), j < j' → Disjoint (sectorSet θ j) (sectorSet θ j') from
      fun j j' h ↦ h.lt_or_gt.elim (this j j') fun h' ↦ (this j' j h').symm
    refine fun j j' hjj' ↦ disjoint_left.2 fun z hz hz' ↦ ?_
    let i : Fin k := ⟨j, by omega⟩
    exact (hz.2 i le_rfl).not_gt (hz'.1 i hjj')

/-- A section and a sector of a stack are disjoint. -/
theorem disjoint_sectionSet_sectorSet (θ : Fin k → X → α) (i : Fin k) (j : Fin (k + 1)) :
    Disjoint (sectionSet θ i) (sectorSet θ j) := by
  first
  | refine disjoint_left.2 fun z hz hz' ↦ ?_
    rw [mem_sectionSet] at hz
    rcases lt_or_ge i.castSucc j with h | h
    · exact (hz'.1 i h).ne hz
    · exact (hz'.2 i h).ne' hz

/-- For pointwise monotone `θ`, the sections and sectors cover the cylinder. -/
theorem iUnion_sectionSet_union_iUnion_sectorSet (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    (⋃ i, sectionSet θ i) ∪ ⋃ j, sectorSet θ j = univ := by
  first
  | refine eq_univ_of_forall fun z ↦ ?_
    by_cases hsec : ∃ i, θ i z.1 = z.2
    · obtain ⟨i, hi⟩ := hsec
      exact Or.inl (mem_iUnion.2 ⟨i, hi⟩)
    simp only [not_exists] at hsec
    refine Or.inr (mem_iUnion.2 ?_)
    by_cases habove : ∃ i, z.2 < θ i z.1
    · -- `z` lies in the sector just below the lowest section above it.
      have hne : (Finset.univ.filter fun i ↦ z.2 < θ i z.1).Nonempty := by
        obtain ⟨i, hi⟩ := habove
        exact ⟨i, by simpa using hi⟩
      let i₀ := (Finset.univ.filter fun i ↦ z.2 < θ i z.1).min' hne
      have hi₀ : z.2 < θ i₀ z.1 := by simpa using Finset.min'_mem _ hne
      refine ⟨i₀.castSucc, fun i hi ↦ ?_, fun i hi ↦ hi₀.trans_le (hθ z.1 (by simpa using hi))⟩
      refine lt_of_le_of_ne (not_lt.1 fun h ↦ ?_) (hsec i)
      exact (Fin.castSucc_lt_castSucc_iff.1 hi).not_ge
        (Finset.min'_le _ _ (by simpa using h))
    · -- `z` lies above every section.
      simp only [not_exists, not_lt] at habove
      exact ⟨Fin.last k, fun i _ ↦ lt_of_le_of_ne (habove i) (hsec i),
        fun i hi ↦ absurd hi (not_le.2 (Fin.castSucc_lt_last i))⟩

/-- For pointwise strictly monotone `θ` with values in a densely ordered type without endpoints,
each sector lies over the whole base. -/
theorem fst_image_sectorSet [Nonempty α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    Prod.fst '' sectorSet θ j = univ := by
  first
  | refine eq_univ_of_forall fun x ↦ ?_
    suffices ∃ t, (x, t) ∈ sectorSet θ j by
      obtain ⟨t, ht⟩ := this
      exact ⟨(x, t), ht, rfl⟩
    cases k with
    | zero => simp
    | succ k =>
      have hm : ∀ x, Monotone fun i ↦ θ i x := fun x ↦ (hθ x).monotone
      cases j using Fin.cases with
      | zero =>
        obtain ⟨t, ht⟩ := exists_lt (θ 0 x)
        exact ⟨t, by rw [sectorSet_zero hm]; exact ht⟩
      | succ j =>
        cases j using Fin.lastCases with
        | last =>
          obtain ⟨t, ht⟩ := exists_gt (θ (Fin.last k) x)
          exact ⟨t, by rw [Fin.succ_last, sectorSet_last hm]; exact ht⟩
        | cast i =>
          obtain ⟨t, ht⟩ := exists_between (hθ x i.castSucc_lt_succ)
          exact ⟨t, by rw [sectorSet_castSucc_succ hm]; exact ht⟩

/-- Over a nonempty base, every sector of a pointwise strictly monotone stack with values in a
densely ordered type without endpoints is nonempty. -/
theorem sectorSet_nonempty [Nonempty X] [Nonempty α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    (sectorSet θ j).Nonempty := by
  first
  | rw [← image_nonempty (f := Prod.fst), fst_image_sectorSet hθ j]
    exact univ_nonempty

/-! ### Parametrizations of the sectors -/

/-- For pointwise strictly monotone `θ` with values in an ordered field, the bounded sector between
sections `i` and `i + 1` is the image of `X × (0, 1)` under the map sending `(x, s)` to the point
`AffineMap.lineMap (θ i x) (θ (i + 1) x) s` of the fibre over `x`. When `α` is a topological ring,
`Continuous.lineMap` shows that this map is continuous whenever the functions of the stack are. -/
theorem sectorSet_castSucc_succ_eq_image [Field α] [IsStrictOrderedRing α]
    {θ : Fin (k + 1) → X → α} (hθ : ∀ x, StrictMono fun i ↦ θ i x) (i : Fin k) :
    sectorSet θ i.castSucc.succ =
      (fun z : X × α ↦ (z.1, AffineMap.lineMap (θ i.castSucc z.1) (θ i.succ z.1) z.2)) ''
        (univ ×ˢ Ioo 0 1) := by
  first
  | ext ⟨x, t⟩
    -- Each fibre is an open interval, which is the open segment between its endpoints.
    have h : t ∈ Ioo (θ i.castSucc x) (θ i.succ x) ↔
        t ∈ AffineMap.lineMap (θ i.castSucc x) (θ i.succ x) '' Ioo (0 : α) 1 := by
      rw [← openSegment_eq_image_lineMap, openSegment_eq_Ioo (hθ x i.castSucc_lt_succ)]
    rw [sectorSet_castSucc_succ fun x ↦ (hθ x).monotone, mem_ofPred_eq, ← mem_Ioo, h]
    simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, Prod.mk.injEq]
    exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨x, s, hs, rfl, h⟩, fun ⟨_, s, hs, rfl, h⟩ ↦ ⟨s, hs, h⟩⟩

/-- For pointwise monotone `θ` with values in an ordered additive group, the lowest sector is the
image of `X × (-∞, 0)` under the map translating the height `s` by `θ 0 x`. When addition on `α`
is continuous, this map is continuous whenever `θ 0` is. -/
theorem sectorSet_zero_eq_image [AddCommGroup α] [IsOrderedAddMonoid α] {θ : Fin (k + 1) → X → α}
    (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ 0 = (fun z : X × α ↦ (z.1, θ 0 z.1 + z.2)) '' (univ ×ˢ Iio 0) := by
  first
  | ext ⟨x, t⟩
    have h : t ∈ Iio (θ 0 x) ↔ t ∈ (θ 0 x + ·) '' Iio 0 := by
      rw [image_const_add_Iio, add_zero]
    rw [sectorSet_zero hθ, mem_ofPred_eq, ← mem_Iio, h]
    simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, Prod.mk.injEq]
    exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨x, s, hs, rfl, h⟩, fun ⟨_, s, hs, rfl, h⟩ ↦ ⟨s, hs, h⟩⟩

/-- For pointwise monotone `θ` with values in an ordered additive group, the highest sector is the
image of `X × (0, ∞)` under the map translating the height `s` by `θ k x`. When addition on `α`
is continuous, this map is continuous whenever `θ k` is. -/
theorem sectorSet_last_eq_image [AddCommGroup α] [IsOrderedAddMonoid α] {θ : Fin (k + 1) → X → α}
    (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ (Fin.last (k + 1)) =
      (fun z : X × α ↦ (z.1, θ (Fin.last k) z.1 + z.2)) '' (univ ×ˢ Ioi 0) := by
  first
  | ext ⟨x, t⟩
    have h : t ∈ Ioi (θ (Fin.last k) x) ↔ t ∈ (θ (Fin.last k) x + ·) '' Ioi 0 := by
      rw [image_const_add_Ioi, add_zero]
    rw [sectorSet_last hθ, mem_ofPred_eq, ← mem_Ioi, h]
    simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, Prod.mk.injEq]
    exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨x, s, hs, rfl, h⟩, fun ⟨_, s, hs, rfl, h⟩ ↦ ⟨s, hs, h⟩⟩

end Order

section Topology

variable [TopologicalSpace X] {θ : Fin k → X → α}

/-- A sector bounded by finitely many continuous functions is open in the cylinder.
The functions need not be ordered. -/
theorem isOpen_sectorSet [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    (hc : ∀ i, Continuous (θ i)) (j : Fin (k + 1)) : IsOpen (sectorSet θ j) := by
  first
  | simp only [sectorSet, ofPred_and, ofPred_forall]
    refine (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ ?_).inter
      (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ ?_)
    · exact isOpen_lt ((hc i).comp continuous_fst) continuous_snd
    · exact isOpen_lt continuous_snd ((hc i).comp continuous_fst)

/-- Over a preconnected base, the section of a continuous function is preconnected. -/
theorem isPreconnected_sectionSet [TopologicalSpace α] [PreconnectedSpace X] {i : Fin k}
    (hθ : Continuous (θ i)) : IsPreconnected (sectionSet θ i) := by
  first
  | rw [sectionSet_eq_range]
    exact isPreconnected_range (by fun_prop)

/-- Over a connected base, the section of a continuous function is connected. -/
theorem isConnected_sectionSet [TopologicalSpace α] [ConnectedSpace X] {i : Fin k}
    (hθ : Continuous (θ i)) : IsConnected (sectionSet θ i) := by
  first
  | rw [sectionSet_eq_range]
    exact isConnected_range (by fun_prop)

/-- Every sector of a stack of continuous, pointwise strictly ordered functions with values in
an ordered semitopological field contains the graph of a continuous function. -/
theorem exists_continuous_forall_mem_sectorSet [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [TopologicalSpace α] [IsSemitopologicalRing α] (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    ∃ σ : X → α, Continuous σ ∧ ∀ x, (x, σ x) ∈ sectorSet θ j := by
  first
  | cases k with
    | zero => exact ⟨fun _ ↦ 0, continuous_const, by simp⟩
    | succ k =>
      have hm : ∀ x, Monotone fun i ↦ θ i x := fun x ↦ (hθ x).monotone
      cases j using Fin.cases with
      | zero =>
        refine ⟨fun x ↦ θ 0 x - 1, by fun_prop, fun x ↦ ?_⟩
        simp [sectorSet_zero hm]
      | succ j =>
        cases j using Fin.lastCases with
        | last =>
          refine ⟨fun x ↦ θ (Fin.last k) x + 1, by fun_prop, fun x ↦ ?_⟩
          rw [Fin.succ_last, sectorSet_last hm]
          simp
        | cast i =>
          refine ⟨fun x ↦ (θ i.castSucc x + θ i.succ x) / 2, by fun_prop, fun x ↦ ?_⟩
          have h := hθ x i.castSucc_lt_succ
          rw [sectorSet_castSucc_succ hm, mem_ofPred_eq]
          constructor <;> linarith

variable {θ : Fin k → X → ℝ}

/-- Over a preconnected base, each sector of a stack of continuous, pointwise strictly ordered
real functions is preconnected. -/
theorem isPreconnected_sectorSet [PreconnectedSpace X] (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    IsPreconnected (sectorSet θ j) := by
  first
  | obtain ⟨σ, hσ, hσj⟩ := exists_continuous_forall_mem_sectorSet hc hθ j
    exact isPreconnected_of_isPreconnected_preimage_prodMk hσ hσj fun x ↦
      (ordConnected_preimage_mk_sectorSet θ j x).isPreconnected

/-- Over a connected base, each sector of a stack of continuous, pointwise strictly ordered real
functions is connected. -/
theorem isConnected_sectorSet [ConnectedSpace X] (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    IsConnected (sectorSet θ j) :=
  ⟨sectorSet_nonempty hθ j, isPreconnected_sectorSet hc hθ j⟩

end Topology

/-! ### The ambient cylinder -/

section Cylinder

variable {n : ℕ}

/-- The cylinder `S × α` over a set `S` of points of `α ^ n`, placed in `α ^ (n + 1)` with the
distinguished coordinate first. -/
def cylinder (S : Set (Fin n → α)) (z : S × α) : Fin (n + 1) → α :=
  Fin.cons z.2 z.1.val

variable {S : Set (Fin n → α)}

theorem cylinder_def (z : S × α) : cylinder S z = Fin.cons z.2 z.1.val :=
  (rfl)

@[simp]
theorem cylinder_apply_zero (z : S × α) : cylinder S z 0 = z.2 :=
  (rfl)

@[simp]
theorem cylinder_apply_succ (z : S × α) (i : Fin n) : cylinder S z i.succ = z.1.val i :=
  (rfl)

@[simp]
theorem tail_cylinder (z : S × α) : Fin.tail (cylinder S z) = z.1.val :=
  (rfl)

/-- Distinct points of the cylinder over `S` have distinct ambient images. -/
theorem cylinder_injective : Injective (cylinder S) := by
  first
  | intro z z' h
    have h₀ := congr_fun h 0
    have h₁ := congrArg Fin.tail h
    simp only [cylinder_apply_zero, tail_cylinder] at h₀ h₁
    exact Prod.ext (Subtype.ext h₁) h₀

/-- A point lies in the image of a subset `A` of the cylinder over `S` exactly when its last `n`
coordinates lie in `S` and, together with its distinguished coordinate, give a point of `A`. -/
theorem mem_image_cylinder {A : Set (S × α)} {y : Fin (n + 1) → α} :
    y ∈ cylinder S '' A ↔ ∃ h : Fin.tail y ∈ S, (⟨Fin.tail y, h⟩, y 0) ∈ A := by
  first
  | refine ⟨?_, fun ⟨h, hA⟩ ↦ ⟨_, hA, Fin.cons_self_tail y⟩⟩
    rintro ⟨z, hz, rfl⟩
    exact ⟨z.1.2, hz⟩

/-- Forgetting the distinguished coordinate of the image of a subset `A` of the cylinder over `S`
gives the projection of `A` to `S`, as a subset of `α ^ n`. -/
theorem image_tail_image_cylinder (A : Set (S × α)) :
    Fin.tail '' (cylinder S '' A) = Subtype.val '' (Prod.fst '' A) := by
  first
  | simp only [image_image, tail_cylinder]

/-- The cylinder over `S` fills exactly the points whose last `n` coordinates lie in `S`. -/
theorem range_cylinder : range (cylinder S) = {y : Fin (n + 1) → α | Fin.tail y ∈ S} := by
  first
  | ext y
    refine ⟨?_, fun hy ↦ ⟨(⟨Fin.tail y, hy⟩, y 0), Fin.cons_self_tail y⟩⟩
    rintro ⟨z, rfl⟩
    simp

variable [TopologicalSpace α]

/-- The cylinder map is continuous. -/
@[fun_prop]
theorem continuous_cylinder : Continuous (cylinder S) := by
  first
  | unfold cylinder
    fun_prop

/-- The cylinder over `S` is a topological embedding into `α ^ (n + 1)`. -/
theorem isEmbedding_cylinder : IsEmbedding (cylinder S) := by
  first
  | refine .of_comp continuous_cylinder (g := fun y ↦ (Fin.tail y, y 0)) (by fun_prop) ?_
    exact IsEmbedding.subtypeVal.prodMap .id

end Cylinder

/-! ### Stacks in the ambient space -/

section Ambient

variable {n : ℕ}

section Order

variable [LinearOrder α] {C : Set (Fin n → α)} {θ : Fin k → C → α}

/-- The cells of the stack over `C ⊆ α ^ n` defined by `θ`, as subsets of `α ^ (n + 1)`: the
images under `TauCeti.cylinder` of its `k` sections and its `k + 1` sectors. -/
def stackCells (C : Set (Fin n → α)) (θ : Fin k → C → α) : Set (Set (Fin (n + 1) → α)) :=
  range (fun i ↦ cylinder C '' sectionSet θ i) ∪ range fun j ↦ cylinder C '' sectorSet θ j

@[simp]
theorem mem_stackCells {E : Set (Fin (n + 1) → α)} :
    E ∈ stackCells C θ ↔
      (∃ i, cylinder C '' sectionSet θ i = E) ∨ ∃ j, cylinder C '' sectorSet θ j = E :=
  Iff.rfl

theorem image_cylinder_sectionSet_mem_stackCells (i : Fin k) :
    cylinder C '' sectionSet θ i ∈ stackCells C θ :=
  Or.inl ⟨i, rfl⟩

theorem image_cylinder_sectorSet_mem_stackCells (j : Fin (k + 1)) :
    cylinder C '' sectorSet θ j ∈ stackCells C θ :=
  Or.inr ⟨j, rfl⟩

/-- A stack has finitely many cells. -/
theorem finite_stackCells (C : Set (Fin n → α)) (θ : Fin k → C → α) :
    (stackCells C θ).Finite :=
  (finite_range _).union (finite_range _)

section Map

variable {m : ℕ} (θ : Fin k → C → α) (f : (Fin m → α) → Fin n → α)

omit [LinearOrder α] in
/-- Pullback of an ambient section along a base map. The height coordinate is unchanged. -/
theorem image_cylinder_sectionSet_comp (i : Fin k) :
    cylinder (f ⁻¹' C) '' sectionSet (fun i x ↦ θ i ⟨f x.1, x.2⟩) i =
      (fun y ↦ Fin.cons (y 0) (f (Fin.tail y))) ⁻¹' (cylinder C '' sectionSet θ i) := by
  first
  | ext y
    simp only [mem_image_cylinder, mem_sectionSet, mem_preimage, Fin.tail_cons, Fin.cons_zero]

/-- Pullback of an ambient sector along a base map, including either unbounded sector. -/
theorem image_cylinder_sectorSet_comp (j : Fin (k + 1)) :
    cylinder (f ⁻¹' C) '' sectorSet (fun i x ↦ θ i ⟨f x.1, x.2⟩) j =
      (fun y ↦ Fin.cons (y 0) (f (Fin.tail y))) ⁻¹' (cylinder C '' sectorSet θ j) := by
  first
  | ext y
    simp only [mem_image_cylinder, mem_sectorSet, mem_preimage, Fin.tail_cons, Fin.cons_zero]

/-- The cells of a pulled-back stack are precisely the inverse images of the original cells.
This holds even when the base map is not injective or surjective. -/
theorem stackCells_comp :
    stackCells (f ⁻¹' C) (fun i x ↦ θ i ⟨f x.1, x.2⟩) =
      (fun E ↦ (fun y ↦ Fin.cons (y 0) (f (Fin.tail y))) ⁻¹' E) '' stackCells C θ := by
  first
  | ext E
    simp only [mem_stackCells, mem_image]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨_, Or.inl ⟨i, rfl⟩, (image_cylinder_sectionSet_comp θ f i).symm⟩
      · exact ⟨_, Or.inr ⟨j, rfl⟩, (image_cylinder_sectorSet_comp θ f j).symm⟩
    · rintro ⟨E, (⟨i, rfl⟩ | ⟨j, rfl⟩), rfl⟩
      · exact Or.inl ⟨i, image_cylinder_sectionSet_comp θ f i⟩
      · exact Or.inr ⟨j, image_cylinder_sectorSet_comp θ f j⟩

end Map

section Restrict

variable {D : Set (Fin n → α)} (h : D ⊆ C)

omit [LinearOrder α] in
/-- Restricting the base of the cylinder from `C` to a subset `D` cuts the image of a subset of
the cylinder over `C` down to the points lying over `D`. -/
theorem image_cylinder_preimage_inclusion (A : Set (C × α)) :
    cylinder D '' (Prod.map (inclusion h) id ⁻¹' A) = cylinder C '' A ∩ Fin.tail ⁻¹' D := by
  first
  | ext y
    simp only [mem_image_cylinder, mem_inter_iff, mem_preimage, Prod.map_apply, inclusion_mk,
      id_eq]
    exact ⟨fun ⟨hD, hA⟩ ↦ ⟨⟨h hD, hA⟩, hD⟩, fun ⟨⟨_, hA⟩, hD⟩ ↦ ⟨hD, hA⟩⟩

variable (θ : Fin k → C → α)

omit [LinearOrder α] in
/-- A section of a stack restricted to a smaller base `D` is the part of the original section
lying over `D`. -/
theorem image_cylinder_sectionSet_inclusion (i : Fin k) :
    cylinder D '' sectionSet (fun i ↦ θ i ∘ inclusion h) i =
      cylinder C '' sectionSet θ i ∩ Fin.tail ⁻¹' D := by
  first
  | rw [sectionSet_comp, image_cylinder_preimage_inclusion]

/-- A sector of a stack restricted to a smaller base `D` is the part of the original sector lying
over `D`, including either unbounded sector. -/
theorem image_cylinder_sectorSet_inclusion (j : Fin (k + 1)) :
    cylinder D '' sectorSet (fun i ↦ θ i ∘ inclusion h) j =
      cylinder C '' sectorSet θ j ∩ Fin.tail ⁻¹' D := by
  first
  | rw [sectorSet_comp, image_cylinder_preimage_inclusion]

/-- The cells of a stack restricted to a smaller base `D` are the parts of the original cells
lying over `D`. -/
theorem stackCells_inclusion :
    stackCells D (fun i ↦ θ i ∘ inclusion h) = (· ∩ Fin.tail ⁻¹' D) '' stackCells C θ := by
  first
  | ext E
    simp only [mem_stackCells, mem_image]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨_, Or.inl ⟨i, rfl⟩, (image_cylinder_sectionSet_inclusion h θ i).symm⟩
      · exact ⟨_, Or.inr ⟨j, rfl⟩, (image_cylinder_sectorSet_inclusion h θ j).symm⟩
    · rintro ⟨E, (⟨i, rfl⟩ | ⟨j, rfl⟩), rfl⟩
      · exact Or.inl ⟨i, image_cylinder_sectionSet_inclusion h θ i⟩
      · exact Or.inr ⟨j, image_cylinder_sectorSet_inclusion h θ j⟩

end Restrict

/-- For pointwise strictly monotone `θ` with values in a densely ordered type without endpoints,
every cell of the stack over `C` lies over the whole of `C`. -/
theorem image_tail_of_mem_stackCells [Nonempty α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] (hθ : ∀ x, StrictMono fun i ↦ θ i x) {E : Set (Fin (n + 1) → α)}
    (hE : E ∈ stackCells C θ) : Fin.tail '' E = C := by
  first
  | rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rw [image_tail_image_cylinder]
    · rw [fst_image_sectionSet, Subtype.coe_image_univ]
    · rw [fst_image_sectorSet hθ, Subtype.coe_image_univ]

/-- If over each set in `𝒟` a pointwise strictly ordered stack is chosen, with values in a
densely ordered type without endpoints, then the projections of all the cells of these stacks are
exactly the sets in `𝒟`. -/
theorem image_image_tail_iUnion_stackCells [Nonempty α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] {𝒟 : Set (Set (Fin n → α))} {k : Set (Fin n → α) → ℕ}
    {θ : ∀ C : Set (Fin n → α), Fin (k C) → C → α}
    (hθ : ∀ C ∈ 𝒟, ∀ x, StrictMono fun i ↦ θ C i x) :
    image Fin.tail '' ⋃ C ∈ 𝒟, stackCells C (θ C) = 𝒟 := by
  first
  | ext D
    simp only [mem_image, mem_iUnion₂]
    constructor
    · rintro ⟨E, ⟨C, hC, hE⟩, rfl⟩
      rwa [image_tail_of_mem_stackCells (hθ C hC) hE]
    · intro hD
      exact ⟨_, ⟨D, hD, image_cylinder_sectorSet_mem_stackCells 0⟩,
        image_tail_of_mem_stackCells (hθ D hD) (image_cylinder_sectorSet_mem_stackCells 0)⟩

/-- For pointwise monotone `θ`, the cells of the stack over `C` cover the cylinder over `C`. -/
theorem sUnion_stackCells (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    ⋃₀ stackCells C θ = Fin.tail ⁻¹' C := by
  first
  | ext y
    refine ⟨fun ⟨E, hE, hy⟩ ↦ ?_, fun h ↦ ?_⟩
    · rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> exact (mem_image_cylinder.1 hy).1
    · -- The point of the cylinder over `C` above `y` lies in a section or a sector.
      have hz : ((⟨Fin.tail y, h⟩, y 0) : C × α) ∈ (⋃ i, sectionSet θ i) ∪ ⋃ j, sectorSet θ j := by
        rw [iUnion_sectionSet_union_iUnion_sectorSet hθ]
        exact mem_univ _
      rcases hz with hz | hz
      · obtain ⟨i, hi⟩ := mem_iUnion.1 hz
        exact ⟨_, image_cylinder_sectionSet_mem_stackCells i, mem_image_cylinder.2 ⟨h, hi⟩⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.1 hz
        exact ⟨_, image_cylinder_sectorSet_mem_stackCells j, mem_image_cylinder.2 ⟨h, hj⟩⟩

/-- For pointwise injective `θ`, distinct cells of the stack over `C` are disjoint. -/
theorem pairwiseDisjoint_stackCells (hθ : ∀ x, Injective fun i ↦ θ i x) :
    (stackCells C θ).PairwiseDisjoint id := by
  first
  | rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩) _ (⟨i', rfl⟩ | ⟨j', rfl⟩) hne <;>
      rw [onFun, id, id, disjoint_image_iff cylinder_injective]
    · exact pairwise_disjoint_sectionSet hθ fun h ↦ hne (h ▸ rfl)
    · exact disjoint_sectionSet_sectorSet θ i j'
    · exact (disjoint_sectionSet_sectorSet θ i' j).symm
    · exact pairwise_disjoint_sectorSet θ fun h ↦ hne (h ▸ rfl)

/-- Every cell of a stack meets each line parallel to the distinguished axis in an
order-connected set: a point or nothing for a section, an open interval for a sector. -/
theorem ordConnected_setOf_cons_mem_of_mem_stackCells {E : Set (Fin (n + 1) → α)}
    (hE : E ∈ stackCells C θ) (x : Fin n → α) : {t | Fin.cons t x ∈ E}.OrdConnected := by
  first
    -- Over `x ∈ C` the slice of `cylinder C '' A` is the fibre of `A` over `x`, else it is empty.
  | have key {A : Set (C × α)} (hA : ∀ x, (Prod.mk x ⁻¹' A).OrdConnected) :
        {t | Fin.cons t x ∈ cylinder C '' A}.OrdConnected := by
      by_cases hx : x ∈ C
      · convert hA ⟨x, hx⟩ using 1
        ext t
        simp only [mem_ofPred_eq, mem_preimage, mem_image_cylinder, Fin.tail_cons, Fin.cons_zero]
        exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hx, h⟩⟩
      · convert ordConnected_empty (α := α) using 1
        ext t
        simp only [mem_ofPred_eq, mem_image_cylinder, Fin.tail_cons, mem_empty_iff_false,
          iff_false]
        exact fun ⟨h, _⟩ ↦ hx h
    rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine key fun x ↦ ?_
      convert ordConnected_singleton (a := θ i x) using 1
      ext t
      simp [mem_sectionSet, eq_comm]
    · exact key (ordConnected_preimage_mk_sectorSet θ j)

end Order

/-- For continuous, pointwise strictly monotone real `θ` over a connected base, every cell of the
stack is connected. -/
theorem isConnected_of_mem_stackCells {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}
    (hC : IsConnected C) (hc : ∀ i, Continuous (θ i)) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) : IsConnected E := by
  first
  | have := isConnected_iff_connectedSpace.1 hC
    rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (isConnected_sectionSet (hc i)).image _ continuous_cylinder.continuousOn
    · exact (isConnected_sectorSet hc hθ j).image _ continuous_cylinder.continuousOn

end Ambient

end TauCeti
end -- closes the original EOF section from source line 71
end -- closes the synthetic per-file scope
/- END SOURCE: TauCeti/Geometry/RealAlgebraic/Stack/Basic.lean -/
