module

/- Exact source closure for the complete mixed-volume scalar section. -/
public import volume_polynomials.mixed_volume_basis_part02
public import TauCeti.Analysis.Convex.LogConcave
public import TauCeti.Analysis.SpecialFunctions.Pow.Integral
public import TauCeti.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Real
public import TauCeti.MeasureTheory.Integral.PrekopaLeindler
public import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic
public import TauCeti.Analysis.Convex.Measure
public import TauCeti.Data.List.PermanencesMinusVariations
public import TauCeti.Data.Set.Lattice
public import TauCeti.MeasureTheory.SetAlgebra
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.AlgebraicDependence
public import TauCeti.Analysis.Convex.Prod
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Section
public import TauCeti.MeasureTheory.Function.Monotone
public import TauCeti.MeasureTheory.Measure.Mod0MeasureIso
public import TauCeti.MeasureTheory.Group.Measure
public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Quantile
public import TauCeti.Analysis.MeanInequalities
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Equality
public import TauCeti.Analysis.Convex.Separation
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Homothety
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Interval.Set.Infinite
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
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Abel
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
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
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Join
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
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Data.List.Range
public import Mathlib.Order.Filter.Finite
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.LinearCombination
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
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Data.List.SignVariations
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Basic.Sign.Defs
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Tactic.Choose
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.StdBasis
public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.AuxLemma
meta import all Lean.Meta.Match.Match

set_option Elab.async false


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}


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

open Lean Elab Command in
run_cmd do
  -- These are nonserialized elaborator memoization caches only.
  modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env ({} : Lean.Meta.AuxLemmas)
  modifyEnv fun env => Lean.Meta.Match.matcherExt.setState env {}

