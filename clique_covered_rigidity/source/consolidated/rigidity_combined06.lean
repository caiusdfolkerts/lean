module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_combined02
import all consolidated.rigidity_combined02
public import consolidated.rigidity_combined03
import all consolidated.rigidity_combined03
public import consolidated.rigidity_combined04
import all consolidated.rigidity_combined04
public import consolidated.rigidity_combined05
import all consolidated.rigidity_combined05
public import consolidated.rigidity_combined_prepared
import all consolidated.rigidity_combined_prepared
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityTwistDifferential.lean -/





@[expose] public section

/-!
# Maurer–Cartan in actual six-coordinate Euclidean twists

The homogeneous affine matrix is represented as a continuous linear
endomorphism, whose ordinary composition is its associative multiplication.
The differential identity is then pulled back through the injective twist
embedding. No Maurer–Cartan hypothesis is imposed on the twist form.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter
open scoped Topology

abbrev HomogeneousVector := Fin 4 → ℝ
abbrev HomogeneousEndomorphism := HomogeneousVector →L[ℝ] HomogeneousVector

def matrixEndomorphism :
    Matrix (Fin 4) (Fin 4) ℝ ≃ₐ[ℝ] HomogeneousEndomorphism :=
  Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap HomogeneousVector)

def twistLieEmbedding : Twist →L[ℝ] HomogeneousEndomorphism :=
  (matrixEndomorphism.toLinearMap.comp twistLieLinear).toContinuousLinearMap

@[simp] theorem twistLieEmbedding_eq (X : Twist) :
    twistLieEmbedding X = matrixEndomorphism (twistLieMatrix X) := rfl

theorem twistLieEmbedding_injective : Function.Injective twistLieEmbedding := by
  intro X Y h
  exact twistLieMatrix_injective (matrixEndomorphism.injective h)

theorem twistLieEmbedding_bracket (X Y : Twist) :
    twistLieEmbedding (twistBracket X Y) =
      twistLieEmbedding X * twistLieEmbedding Y -
        twistLieEmbedding Y * twistLieEmbedding X := by
  simp only [twistLieEmbedding_eq, twistLieMatrix_commutator, map_sub, map_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Explicit local matrix data representing a twist one-form. The fields
record differentiability, actual inverse matrices and the literal
logarithmic-derivative equality; no differential identity is a field. -/
structure LocalTwistRepresentation (x : E) where
  frame : E → HomogeneousEndomorphism
  inverse : E → HomogeneousEndomorphism
  form : E → (E →L[ℝ] Twist)
  frame_contDiff : ContDiffAt ℝ 2 frame x
  inverse_differentiable : DifferentiableAt ℝ inverse x
  form_differentiable : DifferentiableAt ℝ form x
  inverse_right : ∀ᶠ y in 𝓝 x, frame y * inverse y = 1
  inverse_left : inverse x * frame x = 1
  represents : ∀ᶠ y in 𝓝 x, ∀ u : E,
    twistLieEmbedding (form y u) = spatialLogDerivative frame inverse y u

/-- If a twist form represents the spatial logarithmic derivative of an
actual twice differentiable local body map, it satisfies the actual
Euclidean Lie-bracket equation. -/
theorem twist_maurer_cartan
    (R S : E → HomogeneousEndomorphism) (θ : E → (E →L[ℝ] Twist)) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (hS : DifferentiableAt ℝ S x)
    (hθ : DifferentiableAt ℝ θ x)
    (hRS : ∀ᶠ y in 𝓝 x, R y * S y = 1)
    (hSR : S x * R x = 1)
    (hrep : ∀ᶠ y in 𝓝 x, ∀ u : E,
      twistLieEmbedding (θ y u) = spatialLogDerivative R S y u)
    (v w : E) :
    fderiv ℝ (fun y => θ y w) x v - fderiv ℝ (fun y => θ y v) x w =
      twistBracket (θ x v) (θ x w) := by
  have hpart (u : E) : DifferentiableAt ℝ (fun y => θ y u) x :=
    hθ.clm_apply (differentiableAt_const u)
  have hder (u z : E) :
      twistLieEmbedding (fderiv ℝ (fun y => θ y u) x z) =
        fderiv ℝ (fun y => spatialLogDerivative R S y u) x z := by
    have he : (fun y => twistLieEmbedding (θ y u)) =ᶠ[𝓝 x]
        (fun y => spatialLogDerivative R S y u) := hrep.mono fun y hy => hy u
    have hm := congrArg (fun D : E →L[ℝ] HomogeneousEndomorphism => D z)
      (he.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_fun_comp x twistLieEmbedding.differentiableAt (hpart u),
      twistLieEmbedding.fderiv] at hm
    exact hm
  apply twistLieEmbedding_injective
  rw [map_sub, twistLieEmbedding_bracket, hder, hder]
  have hx := hrep.self_of_nhds
  rw [hx v, hx w]
  exact spatial_maurer_cartan R S x hR hS hRS hSR v w

theorem LocalTwistRepresentation.maurer_cartan {x : E}
    (A : LocalTwistRepresentation x) (v w : E) :
    fderiv ℝ (fun y => A.form y w) x v - fderiv ℝ (fun y => A.form y v) x w =
      twistBracket (A.form x v) (A.form x w) :=
  twist_maurer_cartan A.frame A.inverse A.form x A.frame_contDiff
    A.inverse_differentiable A.form_differentiable A.inverse_right A.inverse_left
    A.represents v w

end Papers.Rigidity.Calculus

end
end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0001/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityBodyMotionRepresentation.lean -/










@[expose] public section

/-!
# Twist forms of actual smooth Euclidean body maps

The body map is an ordinary rotation and translation. Its homogeneous
matrix and inverse are explicit. Differentiating the actual orthogonality
identity proves that its logarithmic derivative is a Euclidean Lie matrix;
the six-coordinate twist is extracted by a fixed continuous linear map.
This constructs `LocalTwistRepresentation` without assuming a
Maurer--Cartan identity or assuming that an arbitrary one-form integrates.

The final construction applies these statements to the rotations and
translations already obtained from an actual surviving triangle.
-/

namespace Papers.Rigidity.Calculus.BodyMotion

noncomputable section

open Matrix Filter
open scoped Matrix Topology BigOperators

/-- Use the ordinary entrywise Pi norm on the finite matrix space. -/
local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedAddCommGroup (Matrix m n ℝ) :=
  inferInstanceAs (NormedAddCommGroup (m → n → ℝ))

local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedSpace ℝ (Matrix m n ℝ) :=
  inferInstanceAs (NormedSpace ℝ (m → n → ℝ))

abbrev RotationMatrix := Matrix (Fin 3) (Fin 3) ℝ
abbrev AffineMatrix := Matrix (Fin 4) (Fin 4) ℝ

def linearAffine (R : RotationMatrix) (t : Vec3) : AffineMatrix :=
  !![R 0 0, R 0 1, R 0 2, t 0;
     R 1 0, R 1 1, R 1 2, t 1;
     R 2 0, R 2 1, R 2 2, t 2;
     0, 0, 0, 0]

def linearAffineMap : (RotationMatrix × Vec3) →ₗ[ℝ] AffineMatrix where
  toFun X := linearAffine X.1 X.2
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [linearAffine]
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [linearAffine]

def bottomUnit : AffineMatrix :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1]

def affineMatrix (R : RotationMatrix) (t : Vec3) : AffineMatrix :=
  linearAffine R t + bottomUnit

theorem affineMatrix_mul (R S : RotationMatrix) (t u : Vec3) :
    affineMatrix R t * affineMatrix S u =
      affineMatrix (R * S) (R *ᵥ u + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affineMatrix, linearAffine, bottomUnit, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem linearAffine_mul_affineMatrix
    (D R : RotationMatrix) (v t : Vec3) :
    linearAffine D v * affineMatrix R t =
      linearAffine (D * R) (D *ᵥ t + v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affineMatrix, linearAffine, bottomUnit, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

@[simp] theorem affineMatrix_one_zero : affineMatrix 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [affineMatrix, linearAffine, bottomUnit]

def bodyLinear : (RotationMatrix × Vec3) →L[ℝ] HomogeneousEndomorphism :=
  (matrixEndomorphism.toLinearMap.comp linearAffineMap).toContinuousLinearMap

def bodyFrame (R : RotationMatrix) (t : Vec3) : HomogeneousEndomorphism :=
  matrixEndomorphism (affineMatrix R t)

theorem bodyFrame_eq_linear_add (R : RotationMatrix) (t : Vec3) :
    bodyFrame R t = bodyLinear (R, t) + matrixEndomorphism bottomUnit := by
  simp only [bodyFrame, affineMatrix, map_add]
  rfl

theorem bodyFrame_mul (R S : RotationMatrix) (t u : Vec3) :
    bodyFrame R t * bodyFrame S u = bodyFrame (R * S) (R *ᵥ u + t) := by
  rw [bodyFrame, bodyFrame, ← map_mul, affineMatrix_mul]
  rfl

@[simp] theorem bodyFrame_one_zero : bodyFrame 1 0 = 1 := by
  simp [bodyFrame]

theorem bodyFrame_inverse_right (R : RotationMatrix) (t : Vec3)
    (hR : Rᵀ * R = 1) :
    bodyFrame R t * bodyFrame Rᵀ (-(Rᵀ *ᵥ t)) = 1 := by
  have hRR : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  rw [bodyFrame_mul, hRR, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    hRR, Matrix.one_mulVec, neg_add_cancel, bodyFrame_one_zero]

theorem bodyFrame_inverse_left (R : RotationMatrix) (t : Vec3)
    (hR : Rᵀ * R = 1) :
    bodyFrame Rᵀ (-(Rᵀ *ᵥ t)) * bodyFrame R t = 1 := by
  rw [bodyFrame_mul, hR, add_neg_cancel, bodyFrame_one_zero]

def projectLieLinear : AffineMatrix →ₗ[ℝ] Twist where
  toFun M := (![M 2 1, M 0 2, M 1 0], ![M 0 3, M 1 3, M 2 3])
  map_add' M N := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp
  map_smul' c M := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp

def projectLie : HomogeneousEndomorphism →L[ℝ] Twist :=
  (projectLieLinear.comp matrixEndomorphism.symm.toLinearMap).toContinuousLinearMap

theorem twistLieMatrix_project_linearAffine (Ω : RotationMatrix) (v : Vec3)
    (hΩ : Ωᵀ = -Ω) :
    twistLieMatrix (projectLieLinear (linearAffine Ω v)) = linearAffine Ω v := by
  have h (i j : Fin 3) : Ω j i = -Ω i j :=
    congrFun (congrFun hΩ i) j
  have h00 := h 0 0
  have h11 := h 1 1
  have h22 := h 2 2
  have h01 := h 0 1
  have h02 := h 0 2
  have h12 := h 1 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistLieMatrix, projectLieLinear, linearAffine] <;> linarith

theorem twistLieEmbedding_project_linearAffine (Ω : RotationMatrix) (v : Vec3)
    (hΩ : Ωᵀ = -Ω) :
    twistLieEmbedding (projectLie (bodyLinear (Ω, v))) = bodyLinear (Ω, v) := by
  change matrixEndomorphism
      (twistLieMatrix (projectLieLinear
        (matrixEndomorphism.symm (matrixEndomorphism (linearAffine Ω v))))) =
    matrixEndomorphism (linearAffine Ω v)
  rw [matrixEndomorphism.symm_apply_apply, twistLieMatrix_project_linearAffine Ω v hΩ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_matrix_coordinate (R : E → RotationMatrix) (x u : E)
    (hR : DifferentiableAt ℝ R x) (i j : Fin 3) :
    fderiv ℝ (fun y => R y i j) x u = (fderiv ℝ R x u) i j := by
  rw [fderiv_apply (differentiableAt_pi.mp hR i) j, fderiv_apply hR i]
  rfl

/-- Differentiation of the actual row-Gram identity. -/
theorem derivative_row_gram (R : E → RotationMatrix) (x u : E)
    (hR : DifferentiableAt ℝ R x)
    (horth : ∀ᶠ y in 𝓝 x, R y * (R y)ᵀ = 1) :
    (fderiv ℝ R x u) * (R x)ᵀ + R x * (fderiv ℝ R x u)ᵀ = 0 := by
  ext i j
  have heq : (fun y => ∑ k : Fin 3, R y i k * R y j k) =ᶠ[𝓝 x]
      (fun _ => (1 : RotationMatrix) i j) := by
    filter_upwards [horth] with y hy
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
      congrFun (congrFun hy i) j
  have hz : fderiv ℝ (fun y => ∑ k : Fin 3, R y i k * R y j k) x = 0 := by
    rw [heq.fderiv_eq]
    exact fderiv_const_apply (𝕜 := ℝ) (x := x) _
  have hprod (k : Fin 3) : DifferentiableAt ℝ
      (fun y => R y i k * R y j k) x :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hR i) k).mul (differentiableAt_pi.mp (differentiableAt_pi.mp hR j) k)
  rw [fderiv_fun_sum (fun k _ => hprod k)] at hz
  have hzu := congrArg (fun L : E →L[ℝ] ℝ => L u) hz
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] at hzu
  have hcoord (k : Fin 3) :
      fderiv ℝ (fun y => R y i k * R y j k) x u =
        R x i k * (fderiv ℝ R x u) j k +
          R x j k * (fderiv ℝ R x u) i k := by
    rw [fderiv_fun_mul (differentiableAt_pi.mp (differentiableAt_pi.mp hR i) k) (differentiableAt_pi.mp (differentiableAt_pi.mp hR j) k)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, fderiv_matrix_coordinate R x u hR]
  simp_rw [hcoord] at hzu
  simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.zero_apply, Finset.sum_add_distrib, mul_comm, add_comm] using hzu

/-- The angular logarithmic derivative is skew because the actual
rotation matrices are orthogonal in a neighborhood. -/
theorem spatial_rotation_derivative_skew (R : E → RotationMatrix) (x u : E)
    (hR : DifferentiableAt ℝ R x)
    (horth : ∀ᶠ y in 𝓝 x, (R y)ᵀ * R y = 1) :
    ((fderiv ℝ R x u) * (R x)ᵀ)ᵀ =
      -((fderiv ℝ R x u) * (R x)ᵀ) := by
  have hrow : ∀ᶠ y in 𝓝 x, R y * (R y)ᵀ = 1 :=
    horth.mono fun _ hy => mul_eq_one_comm.mp hy
  have h := derivative_row_gram R x u hR hrow
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_of_add_eq_zero_right h

theorem bodyFrame_contDiffAt (R : E → RotationMatrix) (t : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x) :
    ContDiffAt ℝ 2 (fun y => bodyFrame (R y) (t y)) x := by
  simp_rw [bodyFrame_eq_linear_add]
  exact (bodyLinear.contDiff.contDiffAt.comp x (hR.prodMk ht)).add contDiffAt_const

theorem inverseFrame_contDiffAt (R : E → RotationMatrix) (t : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x) :
    ContDiffAt ℝ 2 (fun y => bodyFrame (R y)ᵀ (-((R y)ᵀ *ᵥ t y))) x := by
  apply bodyFrame_contDiffAt
  · apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact contDiffAt_pi.mp (contDiffAt_pi.mp hR j) i
  · apply contDiffAt_pi.mpr
    intro i
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact (ContDiffAt.sum fun j _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hR j) i).mul (contDiffAt_pi.mp ht j)).neg

theorem fderiv_bodyFrame (R : E → RotationMatrix) (t : E → Vec3) (x u : E)
    (hR : DifferentiableAt ℝ R x) (ht : DifferentiableAt ℝ t x) :
    fderiv ℝ (fun y => bodyFrame (R y) (t y)) x u =
      bodyLinear (fderiv ℝ R x u, fderiv ℝ t x u) := by
  simp_rw [bodyFrame_eq_linear_add]
  have hB : DifferentiableAt ℝ (fun y => bodyLinear (R y, t y)) x :=
    bodyLinear.differentiableAt.comp x (hR.prodMk ht)
  rw [fderiv_fun_add hB
    (differentiableAt_const (matrixEndomorphism bottomUnit)), fderiv_fun_comp x bodyLinear.differentiableAt (hR.prodMk ht),
    bodyLinear.fderiv, fderiv_const_apply, add_zero, hR.fderiv_prodMk ht]
  rfl

def bodyTwistForm (R : E → RotationMatrix) (t : E → Vec3)
    (x : E) : E →L[ℝ] Twist :=
  projectLie.comp
    (((ContinuousLinearMap.mul ℝ HomogeneousEndomorphism).flip
      (bodyFrame (R x)ᵀ (-((R x)ᵀ *ᵥ t x)))).comp
      (fderiv ℝ (fun y => bodyFrame (R y) (t y)) x))

theorem bodyTwistForm_apply (R : E → RotationMatrix) (t : E → Vec3) (x u : E) :
    bodyTwistForm R t x u = projectLie
      (spatialLogDerivative
        (fun y => bodyFrame (R y) (t y))
        (fun y => bodyFrame (R y)ᵀ (-((R y)ᵀ *ᵥ t y))) x u) := rfl

theorem bodyTwistForm_differentiableAt
    (R : E → RotationMatrix) (t : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x) :
    DifferentiableAt ℝ (bodyTwistForm R t) x := by
  have hB := bodyFrame_contDiffAt R t x hR ht
  have hD : DifferentiableAt ℝ
      (fderiv ℝ (fun y => bodyFrame (R y) (t y))) x :=
    (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hI := (inverseFrame_contDiffAt R t x hR ht).differentiableAt (by norm_num)
  unfold bodyTwistForm
  fun_prop

theorem bodyTwistForm_represents
    (R : E → RotationMatrix) (t : E → Vec3) (x u : E)
    (hR : DifferentiableAt ℝ R x) (ht : DifferentiableAt ℝ t x)
    (horth : ∀ᶠ y in 𝓝 x, (R y)ᵀ * R y = 1) :
    twistLieEmbedding (bodyTwistForm R t x u) =
      spatialLogDerivative
        (fun y => bodyFrame (R y) (t y))
        (fun y => bodyFrame (R y)ᵀ (-((R y)ᵀ *ᵥ t y))) x u := by
  let Ω := (fderiv ℝ R x u) * (R x)ᵀ
  let v := fderiv ℝ t x u - Ω *ᵥ t x
  have hlog : spatialLogDerivative
      (fun y => bodyFrame (R y) (t y))
      (fun y => bodyFrame (R y)ᵀ (-((R y)ᵀ *ᵥ t y))) x u =
        bodyLinear (Ω, v) := by
    rw [spatialLogDerivative, fderiv_bodyFrame R t x u hR ht]
    change matrixEndomorphism (linearAffine (fderiv ℝ R x u) (fderiv ℝ t x u)) *
        matrixEndomorphism (affineMatrix (R x)ᵀ (-((R x)ᵀ *ᵥ t x))) =
      matrixEndomorphism (linearAffine Ω v)
    rw [← map_mul, linearAffine_mul_affineMatrix]
    have hv : (fderiv ℝ R x u) *ᵥ (-((R x)ᵀ *ᵥ t x)) +
        fderiv ℝ t x u = v := by
      dsimp [v, Ω]
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
      abel
    rw [hv]
  rw [bodyTwistForm_apply, hlog]
  exact twistLieEmbedding_project_linearAffine Ω v
    (spatial_rotation_derivative_skew R x u hR horth)

/-- A proved constructor from actual local Euclidean body matrices. -/
def localTwistRepresentation
    (R : E → RotationMatrix) (t : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x)
    (horth : ∀ᶠ y in 𝓝 x, (R y)ᵀ * R y = 1) :
    LocalTwistRepresentation x where
  frame y := bodyFrame (R y) (t y)
  inverse y := bodyFrame (R y)ᵀ (-((R y)ᵀ *ᵥ t y))
  form := bodyTwistForm R t
  frame_contDiff := bodyFrame_contDiffAt R t x hR ht
  inverse_differentiable :=
    (inverseFrame_contDiffAt R t x hR ht).differentiableAt (by norm_num)
  form_differentiable := bodyTwistForm_differentiableAt R t x hR ht
  inverse_right := horth.mono fun y hy => bodyFrame_inverse_right (R y) (t y) hy
  inverse_left := bodyFrame_inverse_left (R x) (t x) horth.self_of_nhds
  represents := by
    filter_upwards [hR.eventually (by simp), ht.eventually (by simp),
      eventually_eventually_nhds.mpr horth] with y hRy hty horthY
    intro u
    exact bodyTwistForm_represents R t y u
      (hRy.differentiableAt (by norm_num))
      (hty.differentiableAt (by norm_num)) horthY

/-- A smooth length-preserving moving triangle supplies all data needed
for the actual Maurer--Cartan representation. -/
def triangleTwistRepresentation (p : Fin 3 → Vec3)
    (hp : NoncollinearTriangle p) (q : E → Fin 3 → Vec3) (x : E)
    (hq : ContDiffAt ℝ 2 q x)
    (hlen : ∀ᶠ y in 𝓝 x, ∀ i j,
      BarJoint.squaredDistance (q y) i j = BarJoint.squaredDistance p i j) :
    LocalTwistRepresentation x := by
  have hrot : ContDiff ℝ 2 (TriangleFrame.rotation p) :=
    TriangleFrame.rotation_contDiff p
  have htrans : ContDiff ℝ 2 (TriangleFrame.translation p) :=
    TriangleFrame.translation_contDiff p
  exact localTwistRepresentation
    (fun y => TriangleFrame.rotation p (q y))
    (fun y => TriangleFrame.translation p (q y)) x
    (hrot.contDiffAt.comp x hq)
    (htrans.contDiffAt.comp x hq)
    (hlen.mono fun y hy => TriangleFrame.rotation_orthogonal p (q y) hp hy)

def homogeneousPoint (p : Vec3) : HomogeneousVector := ![p 0, p 1, p 2, 1]

def homogeneousVelocity (v : Vec3) : HomogeneousVector := ![v 0, v 1, v 2, 0]

theorem homogeneousVelocity_injective : Function.Injective homogeneousVelocity := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  funext i
  fin_cases i
  · simpa [homogeneousVelocity] using h0
  · simpa [homogeneousVelocity] using h1
  · simpa [homogeneousVelocity] using h2

@[simp] theorem matrixEndomorphism_apply (M : AffineMatrix) (v : HomogeneousVector) :
    matrixEndomorphism M v = M *ᵥ v := rfl

theorem bodyFrame_homogeneousPoint (R : RotationMatrix) (t p : Vec3) :
    bodyFrame R t (homogeneousPoint p) = homogeneousPoint (R *ᵥ p + t) := by
  ext i
  fin_cases i <;>
    simp [bodyFrame, matrixEndomorphism_apply, affineMatrix, linearAffine,
      bottomUnit, homogeneousPoint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem bodyLinear_homogeneousPoint (D : RotationMatrix) (v p : Vec3) :
    bodyLinear (D, v) (homogeneousPoint p) = homogeneousVelocity (D *ᵥ p + v) := by
  change matrixEndomorphism (linearAffine D v) (homogeneousPoint p) = _
  ext i
  fin_cases i <;>
    simp [matrixEndomorphism_apply, linearAffine, homogeneousPoint,
      homogeneousVelocity, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem twistLieEmbedding_homogeneousPoint (X : Twist) (p : Vec3) :
    twistLieEmbedding X (homogeneousPoint p) =
      homogeneousVelocity (evaluateTwist p X) := by
  exact twistLieMatrix_mulVec X p

def pointActionLinear (p : Vec3) : (RotationMatrix × Vec3) →ₗ[ℝ] Vec3 where
  toFun X := X.1 *ᵥ p + X.2
  map_add' X Y := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]
    ring
  map_smul' c X := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_add, mul_assoc]

def pointAction (p : Vec3) : (RotationMatrix × Vec3) →L[ℝ] Vec3 :=
  (pointActionLinear p).toContinuousLinearMap

theorem fderiv_bodyPoint (R : E → RotationMatrix) (t : E → Vec3) (x u : E) (p : Vec3)
    (hR : DifferentiableAt ℝ R x) (ht : DifferentiableAt ℝ t x) :
    fderiv ℝ (fun y => R y *ᵥ p + t y) x u =
      (fderiv ℝ R x u) *ᵥ p + fderiv ℝ t x u := by
  have h := (pointAction p).hasFDerivAt.comp x
    (hR.hasFDerivAt.prodMk ht.hasFDerivAt)
  exact congrArg (fun L : E →L[ℝ] Vec3 => L u) h.fderiv

/-- The constructed form gives the actual velocity of every material
point of the moving body, not merely a formal Lie-algebra coordinate. -/
theorem bodyTwistForm_velocity
    (R : E → RotationMatrix) (t : E → Vec3) (x u : E) (p : Vec3)
    (hR : DifferentiableAt ℝ R x) (ht : DifferentiableAt ℝ t x)
    (horth : ∀ᶠ y in 𝓝 x, (R y)ᵀ * R y = 1) :
    fderiv ℝ (fun y => R y *ᵥ p + t y) x u =
      evaluateTwist (R x *ᵥ p + t x) (bodyTwistForm R t x u) := by
  have hrep := bodyTwistForm_represents R t x u hR ht horth
  have hproduct : twistLieEmbedding (bodyTwistForm R t x u) * bodyFrame (R x) (t x) =
      bodyLinear (fderiv ℝ R x u, fderiv ℝ t x u) := by
    rw [hrep, spatialLogDerivative, mul_assoc,
      bodyFrame_inverse_left (R x) (t x) horth.self_of_nhds, mul_one,
      fderiv_bodyFrame R t x u hR ht]
  have hpoint := congrArg
    (fun A : HomogeneousEndomorphism => A (homogeneousPoint p)) hproduct
  change twistLieEmbedding (bodyTwistForm R t x u)
      (bodyFrame (R x) (t x) (homogeneousPoint p)) =
    bodyLinear (fderiv ℝ R x u, fderiv ℝ t x u) (homogeneousPoint p) at hpoint
  rw [bodyFrame_homogeneousPoint, twistLieEmbedding_homogeneousPoint,
    bodyLinear_homogeneousPoint] at hpoint
  rw [fderiv_bodyPoint R t x u p hR ht]
  exact (homogeneousVelocity_injective hpoint).symm

/-- On a surviving triangle, the represented twist evaluates to the
literal derivative of each of its three moving vertices. -/
theorem triangleTwistRepresentation_velocity (p : Fin 3 → Vec3)
    (hp : NoncollinearTriangle p) (q : E → Fin 3 → Vec3) (x : E)
    (hq : ContDiffAt ℝ 2 q x)
    (hlen : ∀ᶠ y in 𝓝 x, ∀ i j,
      BarJoint.squaredDistance (q y) i j = BarJoint.squaredDistance p i j)
    (u : E) (i : Fin 3) :
    fderiv ℝ (fun y => q y i) x u =
      evaluateTwist (q x i)
        ((triangleTwistRepresentation p hp q x hq hlen).form x u) := by
  let R := fun y => TriangleFrame.rotation p (q y)
  let t := fun y => TriangleFrame.translation p (q y)
  have hrot : ContDiff ℝ 2 (TriangleFrame.rotation p) :=
    TriangleFrame.rotation_contDiff p
  have htrans : ContDiff ℝ 2 (TriangleFrame.translation p) :=
    TriangleFrame.translation_contDiff p
  have hR : ContDiffAt ℝ 2 R x := hrot.contDiffAt.comp x hq
  have ht : ContDiffAt ℝ 2 t x := htrans.contDiffAt.comp x hq
  have horth : ∀ᶠ y in 𝓝 x, (R y)ᵀ * R y = 1 :=
    hlen.mono fun y hy => TriangleFrame.rotation_orthogonal p (q y) hp hy
  have h := bodyTwistForm_velocity R t x u (p i)
    (hR.differentiableAt (by norm_num)) (ht.differentiableAt (by norm_num)) horth
  have hfun : (fun y => R y *ᵥ p i + t y) = (fun y => q y i) := by
    funext y
    exact TriangleFrame.bodyMap_at_triangle p (q y) hp i
  have hself : R x *ᵥ p i + t x = q x i := congrFun hfun x
  rw [hfun, hself] at h
  exact h

/-- The triangle form is the actual twist on every vertex of a surviving
rigid clique, including a clique consisting of exactly three vertices.
The proved infinitesimal-motion characterization and uniqueness on the
common triangle identify the twist. No finite body-motion realization is assumed. -/
theorem triangleTwistRepresentation_velocity_on_clique
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : G.IsClique (S : Set V))
    (f : Fin 3 ↪ V) (hf : ∀ i, f i ∈ S)
    (p : Fin 3 → Vec3) (hp : NoncollinearTriangle p)
    (q : E → BarJoint.Placement V 3) (x u : E)
    (hq : ContDiffAt ℝ 2 q x)
    (hlen : ∀ᶠ y in 𝓝 x, ∀ i j,
      BarJoint.squaredDistance (fun i => q y (f i)) i j =
        BarJoint.squaredDistance p i j)
    (hgeneral : GeneralPosition.InGeneralPosition (q x))
    (hmotion : BarJoint.IsInfinitesimalMotion G (q x) (fderiv ℝ q x u)) :
    let qtri := fun y i => q y (f i)
    let hqtri : ContDiffAt ℝ 2 qtri x := contDiffAt_pi.mpr (fun i => contDiffAt_pi.mp hq (f i))
    ∀ w ∈ S, (fderiv ℝ q x u) w =
      evaluateTwist (q x w)
        ((triangleTwistRepresentation p hp qtri x hqtri hlen).form x u) := by
  intro qtri hqtri
  let X := (triangleTwistRepresentation p hp qtri x hqtri hlen).form x u
  have htri (i : Fin 3) : (fderiv ℝ q x u) (f i) =
      evaluateTwist (q x (f i)) X := by
    have h := triangleTwistRepresentation_velocity p hp qtri x hqtri hlen u i
    have hD := fderiv_apply (hq.differentiableAt (by norm_num)) (f i)
    have hDu := congrArg (fun L : E →L[ℝ] Vec3 => L u) hD
    change fderiv ℝ (fun y => q y (f i)) x u = (fderiv ℝ q x u) (f i) at hDu
    rw [← hDu]
    exact h
  have himage : Finset.univ.image f ⊆ S := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact hf i
  have hthree : (Finset.univ.image f).card = 3 := by
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  have hcard : 3 ≤ S.card := by
    simpa only [hthree] using Finset.card_le_card himage
  obtain ⟨Y, hY⟩ := exists_twist_on_clique G (q x) (fderiv ℝ q x u)
    hgeneral hmotion S hcard hS
  have hYX : Y = X := by
    apply sub_eq_zero.mp
    apply twist_eq_zero_of_fixing_triangle (fun i => q x (f i))
      (GeneralPosition.InGeneralPosition.triangle (q x) hgeneral f) (Y - X)
    intro i
    rw [map_sub, sub_eq_zero]
    exact (hY (f i) (hf i)).symm.trans (htri i)
  intro w hw
  change fderiv ℝ q x u w = evaluateTwist (q x w) X
  rw [← hYX]
  exact hY w hw

end

end Papers.Rigidity.Calculus.BodyMotion

end
end BundleSource0002

section BundleSource0003
/- Source: Papers/RigidityGroundedFiber.lean -/




@[expose] public section

/-!
# A genuine configuration chart with one body grounded

The equations are the graph's actual squared bar lengths together with
the nine coordinates of a fixed noncollinear triangle.  On the bar-motion
kernel, those nine coordinate equations have rank exactly six.  A local
maximum-rank chart therefore removes the common Euclidean motions by
fixing an actual body, and has the expected tangent dimension.
-/

namespace Papers.Rigidity.Calculus

noncomputable section

variable {E F G : Type*}
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]

def prodKernelEquiv (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) :
    (A.prod B).ker ≃ₗ[ℝ] (B.domRestrict A.ker).ker where
  toFun x := ⟨⟨x.val, by
    have h := congrArg Prod.fst (LinearMap.mem_ker.mp x.property)
    exact h⟩, by
    have h := congrArg Prod.snd (LinearMap.mem_ker.mp x.property)
    exact h⟩
  invFun x := ⟨x.val.val, by
    rw [LinearMap.mem_ker]
    exact Prod.ext x.val.property x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_range_prod (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) :
    Module.finrank ℝ (A.prod B).range =
      Module.finrank ℝ A.range + Module.finrank ℝ (B.domRestrict A.ker).range := by
  have hker := (prodKernelEquiv A B).finrank_eq
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := E) (V₂ := F × G) (A.prod B)
  have h₂ := A.finrank_range_add_finrank_ker
  have h₃ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := A.ker) (V₂ := G) (B.domRestrict A.ker)
  omega

end
end Papers.Rigidity.Calculus

namespace Papers.Rigidity.BarJoint

noncomputable section

open Filter Matrix
open scoped Topology Classical BigOperators Matrix

variable {V : Type} [Fintype V]

def triangleRestriction (f : Fin 3 ↪ V) :
    Placement V 3 →ₗ[ℝ] (Fin 3 × Fin 3 → ℝ) :=
  LinearMap.pi fun a =>
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a.2).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : V => Fin 3 → ℝ) (f a.1))

@[simp] theorem triangleRestriction_apply (f : Fin 3 ↪ V)
    (p : Placement V 3) (a : Fin 3 × Fin 3) : triangleRestriction f p a = p (f a.1) a.2 := rfl

/-- The augmented equations literally fix the old triangle coordinates. -/
def groundedLengthMap (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (q : Placement V 3) : (V × V → ℝ) × (Fin 3 × Fin 3 → ℝ) :=
  (squaredLengthMap G q, triangleRestriction f q)

def GroundedBarMotions (G : SimpleGraph V) (f : Fin 3 ↪ V) (p : Placement V 3) :
    Submodule ℝ (Velocity V 3) :=
  (rigidityOperator G p).ker ⊓ (triangleRestriction f).ker

theorem groundedLengthMap_contDiff (G : SimpleGraph V) (f : Fin 3 ↪ V) :
    ContDiff ℝ 2 (groundedLengthMap G f) :=
  (squaredLengthMap_contDiff G).prodMk
    (LinearMap.toContinuousLinearMap (triangleRestriction f)).contDiff

theorem fderiv_groundedLengthMap (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (p : Placement V 3) :
    fderiv ℝ (groundedLengthMap G f) p =
      (fderiv ℝ (squaredLengthMap G) p).prod
        (LinearMap.toContinuousLinearMap (triangleRestriction f)) := by
  exact ((squaredLengthMap_hasFDerivAt G p).prodMk
    (LinearMap.toContinuousLinearMap (triangleRestriction f)).hasFDerivAt).fderiv.trans
      (by rw [fderiv_squaredLengthMap])

theorem ker_fderiv_groundedLengthMap (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (p : Placement V 3) :
    (fderiv ℝ (groundedLengthMap G f) p).ker = GroundedBarMotions G f p := by
  rw [fderiv_groundedLengthMap]
  change (LinearMap.prod (fderiv ℝ (squaredLengthMap G) p).toLinearMap
    (triangleRestriction f)).ker = _
  rw [LinearMap.ker_prod, ker_fderiv_squaredLengthMap]
  rfl

theorem restricted_triangle_range (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (hclique : ∀ i j : Fin 3, i ≠ j → G.Adj (f i) (f j))
    (p : Placement V 3) (hp : NoncollinearTriangle (p ∘ f)) :
    ((triangleRestriction f).domRestrict (rigidityOperator G p).ker).range =
      (triangleTwistOperator (p ∘ f)).range := by
  rw [triangleTwistOperator_range_eq_ker (p ∘ f) hp]
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    change triangleBarMatrix (p ∘ f) *ᵥ triangleRestriction f u.val = 0
    rw [triangleBarMatrix_mulVec]
    have hmotion := (isInfinitesimalMotion_iff G p u.val).mp u.property
    have hbar (i j : Fin 3) (hij : i ≠ j) :
        edgeConstraint (p ∘ f) (fun k => u.val (f k)) i j = 0 :=
      hmotion (f i) (f j) (hclique i j hij)
    simpa only [triangleRestriction_apply] using
      show ![edgeConstraint (p ∘ f) (fun k => u.val (f k)) 0 1,
        edgeConstraint (p ∘ f) (fun k => u.val (f k)) 0 2,
        edgeConstraint (p ∘ f) (fun k => u.val (f k)) 1 2] = 0 by
          simp [hbar 0 1 (by decide), hbar 0 2 (by decide), hbar 1 2 (by decide)]
  · intro y hy
    rw [← triangleTwistOperator_range_eq_ker (p ∘ f) hp] at hy
    obtain ⟨X, rfl⟩ := hy
    let u : (rigidityOperator G p).ker := ⟨fun v => evaluateTwist (p v) X, by
      rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
      intro v w _
      exact twist_preserves_bar X (p v) (p w)⟩
    exact ⟨u, rfl⟩

theorem restricted_triangle_rank (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (hclique : ∀ i j : Fin 3, i ≠ j → G.Adj (f i) (f j))
    (p : Placement V 3) (hp : NoncollinearTriangle (p ∘ f)) :
    Module.finrank ℝ
      ((triangleRestriction f).domRestrict (rigidityOperator G p).ker).range = 6 := by
  rw [restricted_triangle_range G f hclique p hp,
    LinearMap.finrank_range_of_inj (triangleTwistOperator_injective (p ∘ f) hp),
    finrank_twist]

theorem rank_fderiv_groundedLengthMap (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (hclique : ∀ i j : Fin 3, i ≠ j → G.Adj (f i) (f j))
    (p : Placement V 3) (hp : NoncollinearTriangle (p ∘ f)) :
    Module.finrank ℝ (fderiv ℝ (groundedLengthMap G f) p).range = rigidityRank G p + 6 := by
  rw [fderiv_groundedLengthMap]
  change Module.finrank ℝ
    ((fderiv ℝ (squaredLengthMap G) p).toLinearMap.prod (triangleRestriction f)).range = _
  rw [Calculus.finrank_range_prod, ker_fderiv_squaredLengthMap,
    rank_fderiv_squaredLengthMap, restricted_triangle_rank G f hclique p hp]

theorem groundedBarMotions_finrank_add_six (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (hclique : ∀ i j : Fin 3, i ≠ j → G.Adj (f i) (f j))
    (p : Placement V 3) (hp : NoncollinearTriangle (p ∘ f)) :
    Module.finrank ℝ (GroundedBarMotions G f p) + 6 =
      Module.finrank ℝ (rigidityOperator G p).ker := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := (rigidityOperator G p).ker) (V₂ := Fin 3 × Fin 3 → ℝ)
    ((triangleRestriction f).domRestrict (rigidityOperator G p).ker)
  have hker := (Calculus.prodKernelEquiv (rigidityOperator G p) (triangleRestriction f)).finrank_eq
  rw [LinearMap.ker_prod] at hker
  rw [restricted_triangle_rank G f hclique p hp] at h
  change Module.finrank ℝ
    ↥((rigidityOperator G p).ker ⊓ (triangleRestriction f).ker) + 6 =
      Module.finrank ℝ (rigidityOperator G p).ker
  rw [hker, add_comm]
  exact h

theorem isOpen_triangle_noncollinear (f : Fin 3 ↪ V) :
    IsOpen {p : Placement V 3 | NoncollinearTriangle (p ∘ f)} := by
  have hc : Continuous (fun p : Placement V 3 => ![p (f 1) - p (f 0), p (f 2) - p (f 0)]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  exact isOpen_setOfPred_linearIndependent.preimage hc

/-- The actual grounded local configuration manifold, with no manifold
existence or tangent-space condition assumed in the input. -/
def groundedLengthFiberChart (G : SimpleGraph V) (f : Fin 3 ↪ V)
    (hclique : ∀ i j : Fin 3, i ≠ j → G.Adj (f i) (f j))
    (p : Placement V 3) (hgen : IsRegularPlacement G p)
    (hp : NoncollinearTriangle (p ∘ f)) :
    Calculus.SmoothLevelChart (groundedLengthMap G f) p (GroundedBarMotions G f p) := by
  have hmax : ∀ᶠ q in 𝓝 p,
      Module.finrank ℝ (fderiv ℝ (groundedLengthMap G f) q).range ≤
        Module.finrank ℝ (fderiv ℝ (groundedLengthMap G f) p).range := by
    filter_upwards [(isOpen_triangle_noncollinear f).mem_nhds hp] with q hq
    rw [rank_fderiv_groundedLengthMap G f hclique q hq,
      rank_fderiv_groundedLengthMap G f hclique p hp, hgen]
    exact Nat.add_le_add_right (rigidityRank_le_genericRigidityRank G 3 q) 6
  have C := Calculus.maximumRankLevelChart (groundedLengthMap G f) p
    (groundedLengthMap_contDiff G f).contDiffAt hmax
  rw [ker_fderiv_groundedLengthMap] at C
  exact C

end
end Papers.Rigidity.BarJoint

end
end BundleSource0003

section BundleSource0004
/- Source: Papers/RigidityConfigurationTwists.lean -/




@[expose] public section

/-!
# Actual body twist forms on the grounded length fibre

All forms below are constructed from the genuine grounded configuration
chart. Their velocity interpretation is obtained by differentiating the
actual length equations. Agreement at shared vertices, grounding of a
chosen body, and injectivity of the tangent-to-body-form map are proved
from those equations and from the triangle construction.
-/

namespace Papers.Rigidity.Calculus.GroundedConfiguration

noncomputable section

open Filter Matrix BarJoint BodyMotion
open scoped Topology Classical BigOperators

variable {V B : Type} [Fintype V] [DecidableEq V]

theorem triangle_lengths_of_grounded_level
    (G : SimpleGraph V) (ground : Fin 3 ↪ V) (p q : Placement V 3)
    (hlevel : groundedLengthMap G ground q = groundedLengthMap G ground p)
    (f : Fin 3 ↪ V)
    (hf : ∀ i j, i ≠ j → G.Adj (f i) (f j)) :
    ∀ i j, squaredDistance (fun i => q (f i)) i j =
      squaredDistance (fun i => p (f i)) i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [squaredDistance]
  · have h := congrFun (congrArg Prod.fst hlevel) (f i, f j)
    simpa only [groundedLengthMap, squaredLengthMap, hf i j hij, if_true,
      squaredDistance] using h

/-- Differentiating the whole grounded level equation gives the literal
grounded bar-motion space at the moving placement. -/
theorem derivative_mem_groundedMotions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : SimpleGraph V) (ground : Fin 3 ↪ V) (p : Placement V 3)
    (q : E → Placement V 3) (x u : E) (hq : DifferentiableAt ℝ q x)
    (hlevel : ∀ᶠ y in 𝓝 x,
      groundedLengthMap G ground (q y) = groundedLengthMap G ground p) :
    fderiv ℝ q x u ∈ GroundedBarMotions G ground (q x) := by
  have hF : DifferentiableAt ℝ (groundedLengthMap G ground) (q x) :=
    (groundedLengthMap_contDiff G ground).differentiable (by norm_num) _
  have hzero : fderiv ℝ (fun y => groundedLengthMap G ground (q y)) x = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlevel]
    exact fderiv_const_apply (𝕜 := ℝ) (x := x) _
  rw [fderiv_fun_comp x hF hq] at hzero
  have hu := congrArg
    (fun L : E →L[ℝ] ((V × V → ℝ) × (Fin 3 × Fin 3 → ℝ)) => L u) hzero
  rw [← ker_fderiv_groundedLengthMap G ground (q x)]
  exact hu

variable (G : SimpleGraph V) (ground : Fin 3 ↪ V) (p : Placement V 3)
variable (C : SmoothLevelChart (groundedLengthMap G ground) p
  (GroundedBarMotions G ground p))
variable (S : B → Finset V) (hS : ∀ b, G.IsClique (S b : Set V))
variable (f : B → Fin 3 ↪ V) (hf : ∀ b i, f b i ∈ S b)
variable (hp : GeneralPosition.InGeneralPosition p)

def triangleMap (b : B) : GroundedBarMotions G ground p → Fin 3 → Vec3 :=
  fun y i => C.parametrization y (f b i)

theorem triangleMap_contDiffAt (b : B) :
    ContDiffAt ℝ 2 (triangleMap G ground p C f b) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_pi.mp C.smooth_parametrization (f b i)

include hS hf in
theorem triangleMap_lengths (b : B) :
    ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p), ∀ i j,
      squaredDistance (triangleMap G ground p C f b y) i j =
        squaredDistance (fun i => p (f b i)) i j := by
  filter_upwards [C.level] with y hy
  exact triangle_lengths_of_grounded_level G ground p (C.parametrization y) hy (f b)
    (fun i j hij => hS b (hf b i) (hf b j) (fun h => hij ((f b).injective h)))

/-- Every body representation is constructed from the actual moving
triangle; no representation or differential equation is an input. -/
def bodyRepresentation (b : B) :
    LocalTwistRepresentation (0 : GroundedBarMotions G ground p) :=
  triangleTwistRepresentation (fun i => p (f b i))
    (GeneralPosition.InGeneralPosition.triangle p hp (f b))
    (triangleMap G ground p C f b) 0
    (triangleMap_contDiffAt G ground p C f b)
    (triangleMap_lengths G ground p C S hS f hf b)

include hp in
theorem eventually_generalPosition :
    ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p),
      GeneralPosition.InGeneralPosition (C.parametrization y) := by
  apply C.smooth_parametrization.continuousAt.eventually
  rw [C.parametrization_zero]
  exact GeneralPosition.isOpen_generalPosition.mem_nhds hp

/-- The forms agree with the derivatives of all actual body vertices on
one common neighborhood. This includes every surviving triangle body. -/
theorem bodyRepresentation_velocity :
    ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p),
      ∀ u : GroundedBarMotions G ground p, ∀ b : B, ∀ w ∈ S b,
        (fderiv ℝ C.parametrization y u) w =
          evaluateTwist (C.parametrization y w)
            ((bodyRepresentation G ground p C S hS f hf hp b).form y u) := by
  filter_upwards [C.smooth_parametrization.eventually (by simp),
    eventually_generalPosition G ground p C hp,
    eventually_eventually_nhds.mpr C.level] with y hySmooth hyGeneral hyLevel
  intro u b w hw
  have hmotion := derivative_mem_groundedMotions G ground p C.parametrization y u
    (hySmooth.differentiableAt (by norm_num)) hyLevel
  have htriangle : ∀ᶠ z in 𝓝 y, ∀ i j,
      squaredDistance (triangleMap G ground p C f b z) i j =
        squaredDistance (fun i => p (f b i)) i j := by
    filter_upwards [hyLevel] with z hz
    exact triangle_lengths_of_grounded_level G ground p (C.parametrization z) hz (f b)
      (fun i j hij => hS b (hf b i) (hf b j) (fun h => hij ((f b).injective h)))
  have h := triangleTwistRepresentation_velocity_on_clique
    G (S b) (hS b) (f b) (hf b) (fun i => p (f b i))
    (GeneralPosition.InGeneralPosition.triangle p hp (f b))
    C.parametrization y u hySmooth htriangle hyGeneral hmotion.1 w hw
  exact h

/-- Shared original vertices enforce literal pair-pin compatibility of
the actual differential body forms. -/
theorem bodyRepresentation_sharedVertex :
    ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p),
      ∀ u : GroundedBarMotions G ground p, ∀ b c : B, ∀ w ∈ S b,
        w ∈ S c →
        evaluateTwist (C.parametrization y w)
            ((bodyRepresentation G ground p C S hS f hf hp b).form y u) =
          evaluateTwist (C.parametrization y w)
            ((bodyRepresentation G ground p C S hS f hf hp c).form y u) := by
  filter_upwards [bodyRepresentation_velocity G ground p C S hS f hf hp] with y hy
  intro u b c w hb hc
  exact (hy u b w hb).symm.trans (hy u c w hc)

/-- Fixing the coordinates of the ground triangle actually annihilates
the form of its containing body on a neighborhood. -/
theorem bodyRepresentation_grounded (b₀ : B) (hground : ∀ i, ground i ∈ S b₀) :
    ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p),
      ∀ u : GroundedBarMotions G ground p,
        (bodyRepresentation G ground p C S hS f hf hp b₀).form y u = 0 := by
  filter_upwards [bodyRepresentation_velocity G ground p C S hS f hf hp,
    C.smooth_parametrization.eventually (by simp),
    eventually_generalPosition G ground p C hp,
    eventually_eventually_nhds.mpr C.level] with y hyVelocity hySmooth hyGeneral hyLevel
  intro u
  have hmotion := derivative_mem_groundedMotions G ground p C.parametrization y u
    (hySmooth.differentiableAt (by norm_num)) hyLevel
  apply twist_eq_zero_of_fixing_triangle (fun i => C.parametrization y (ground i))
    (GeneralPosition.InGeneralPosition.triangle (C.parametrization y) hyGeneral ground)
  intro i
  rw [← hyVelocity u b₀ (ground i) (hground i)]
  have hzero := LinearMap.mem_ker.mp hmotion.2
  funext j
  exact congrFun hzero (i, j)

def bodyFormMap : GroundedBarMotions G ground p →ₗ[ℝ] (B → Twist) :=
  LinearMap.pi fun b =>
    ((bodyRepresentation G ground p C S hS f hf hp b).form 0).toLinearMap

/-- The body forms retain every tangent direction when the actual bodies
cover the vertex set. Their injectivity is not imposed as chart data. -/
theorem bodyFormMap_injective (hcover : ∀ w : V, ∃ b : B, w ∈ S b) :
    Function.Injective (bodyFormMap G ground p C S hS f hf hp) := by
  have hvel := (bodyRepresentation_velocity G ground p C S hS f hf hp).self_of_nhds
  have hD := C.tangent.hasFDerivAt.fderiv
  intro u v huv
  apply Subtype.ext
  funext w
  obtain ⟨b, hb⟩ := hcover w
  have hu := hvel u b w hb
  have hv := hvel v b w hb
  rw [hD, C.parametrization_zero] at hu hv
  have heq := congrFun huv b
  change (bodyRepresentation G ground p C S hS f hf hp b).form 0 u =
    (bodyRepresentation G ground p C S hS f hf hp b).form 0 v at heq
  exact hu.trans ((congrArg (evaluateTwist (p w)) heq).trans hv.symm)

include hS f hf in
/-- Instantiation with the actual configuration chart supplied by the
proved maximum-rank theorem. The only inputs are the graph, its real
generic placement, its actual covering cliques, and their chosen triangles. -/
theorem actual_grounded_body_forms
    (hregular : IsRegularPlacement G p)
    (hgroundClique : ∀ i j : Fin 3, i ≠ j → G.Adj (ground i) (ground j))
    (hcover : ∀ w : V, ∃ b : B, w ∈ S b)
    (b₀ : B) (hground : ∀ i, ground i ∈ S b₀) :
    let C := groundedLengthFiberChart G ground hgroundClique p hregular
      (GeneralPosition.InGeneralPosition.triangle p hp ground)
    ∃ A : B → LocalTwistRepresentation (0 : GroundedBarMotions G ground p),
      (∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p),
        ∀ u, ∀ b, ∀ w ∈ S b,
          (fderiv ℝ C.parametrization y u) w =
            evaluateTwist (C.parametrization y w) ((A b).form y u)) ∧
      (∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p),
        ∀ u, (A b₀).form y u = 0) ∧
      Function.Injective (fun u : GroundedBarMotions G ground p => fun b => (A b).form 0 u) := by
  intro Cactual
  refine ⟨bodyRepresentation G ground p Cactual S hS f hf hp, ?_, ?_, ?_⟩
  · exact bodyRepresentation_velocity G ground p Cactual S hS f hf hp
  · exact bodyRepresentation_grounded G ground p Cactual S hS f hf hp b₀ hground
  · exact bodyFormMap_injective G ground p Cactual S hS f hf hp hcover

end

end Papers.Rigidity.Calculus.GroundedConfiguration

end
end BundleSource0004

section BundleSource0005
/- Source: Papers/RigidityCofactorKernel.lean -/







@[expose] public section

/-!
# Literal cofactor kernel vectors for the common-pin argument

This module supplies an algebraic step of Proposition 4.1.
The construction uses the actual evaluation matrix, its Cramer cofactors,
and the original linear subspace. No kernel vector is postulated.
-/

namespace Papers.Rigidity.CofactorKernel

noncomputable section

open scoped BigOperators

section ModuleConstruction

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- Evaluation columns of the selected pivot vectors. -/
def pivotMatrix (L : M →ₗ[R] (ι → R)) (w : ι → M) : Matrix ι ι R :=
  fun i j => L (w j) i

/-- The explicit vector with distinguished coefficient `det A`. -/
def vector (L : M →ₗ[R] (ι → R)) (w : ι → M) (v : M) : M :=
  (pivotMatrix L w).det • v -
    ∑ i, Matrix.cramer (pivotMatrix L w) (L v) i • w i

theorem apply_sum_smul (L : M →ₗ[R] (ι → R)) (w : ι → M) (a : ι → R) :
    L (∑ i, a i • w i) = (pivotMatrix L w).mulVec a := by
  funext j
  simp [pivotMatrix, Matrix.mulVec, dotProduct, mul_comm]

/-- The actual evaluation operator annihilates the constructed vector. -/
theorem apply_vector_eq_zero (L : M →ₗ[R] (ι → R)) (w : ι → M) (v : M) :
    L (vector L w v) = 0 := by
  unfold vector
  rw [map_sub, map_smul, apply_sum_smul, Matrix.mulVec_cramer, sub_self]

/-- A dual coordinate normalized on the chosen vectors reads precisely
the determinant coefficient, hence proves nonvanishing when that pivot
minor is nonzero. The intended dual coordinate is the last basis coordinate. -/
theorem coordinate_vector (L : M →ₗ[R] (ι → R)) (w : ι → M) (v : M)
    (φ : M →ₗ[R] R) (hφw : ∀ i, φ (w i) = 0) (hφv : φ v = 1) :
    φ (vector L w v) = (pivotMatrix L w).det := by
  simp [vector, map_sum, map_smul, hφw, hφv]

theorem vector_ne_zero (L : M →ₗ[R] (ι → R)) (w : ι → M) (v : M)
    (φ : M →ₗ[R] R) (hφw : ∀ i, φ (w i) = 0) (hφv : φ v = 1)
    (hdet : (pivotMatrix L w).det ≠ 0) : vector L w v ≠ 0 := by
  intro hz
  have h := coordinate_vector L w v φ hφw hφv
  rw [hz, map_zero] at h
  exact hdet h.symm

theorem vector_mem (L : M →ₗ[R] (ι → R)) (w : ι → M) (v : M)
    (W : Submodule R M) (hw : ∀ i, w i ∈ W) (hv : v ∈ W) :
    vector L w v ∈ W := by
  apply W.sub_mem (W.smul_mem _ hv)
  exact W.sum_mem fun i _ => W.smul_mem _ (hw i)

end ModuleConstruction

section BasisConstruction

variable {k M ι : Type*} [Field k] [AddCommGroup M] [Module k M]
  [Fintype ι] [DecidableEq ι]

theorem surjective_of_pivot_det_ne_zero (L : M →ₗ[k] (ι → k)) (w : ι → M)
    (hdet : (pivotMatrix L w).det ≠ 0) : Function.Surjective L := by
  have hunit : IsUnit (pivotMatrix L w) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  intro y
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit y
  refine ⟨∑ i, c i • w i, ?_⟩
  rw [apply_sum_smul]
  exact hc

def basisVector (L : M →ₗ[k] (ι → k)) (b : Module.Basis (Option ι) k M) : M :=
  vector L (fun i => b (some i)) (b none)

theorem basisVector_coordinate (L : M →ₗ[k] (ι → k))
    (b : Module.Basis (Option ι) k M) :
    b.repr (basisVector L b) none =
      (pivotMatrix L (fun i => b (some i))).det := by
  exact coordinate_vector L (fun i => b (some i)) (b none) (b.coord none)
    (fun i => by simp [Module.Basis.coord_apply])
    (by simp [Module.Basis.coord_apply])

/-- The explicit Cramer vector spans the entire evaluation kernel on
its nonzero pivot chart. The kernel-line premise used in the two-pin
argument is therefore derived from an ordinary basis and determinant. -/
theorem kernel_vector_eq_smul_basisVector (L : M →ₗ[k] (ι → k))
    (b : Module.Basis (Option ι) k M)
    (hdet : (pivotMatrix L (fun i => b (some i))).det ≠ 0)
    (X : M) (hX : L X = 0) :
    ∃ a : k, X = a • basisVector L b := by
  let D := (pivotMatrix L (fun i => b (some i))).det
  let a := b.repr X none / D
  let Z := X - a • basisVector L b
  have hZL : L Z = 0 := by
    dsimp only [Z]
    rw [map_sub, map_smul, hX]
    change 0 - a • L (vector L (fun i => b (some i)) (b none)) = 0
    rw [apply_vector_eq_zero, smul_zero, sub_zero]
  have hZcoord : b.repr Z none = 0 := by
    change (b.coord none) Z = 0
    dsimp only [Z]
    rw [map_sub, map_smul]
    change b.repr X none - a * b.repr (basisVector L b) none = 0
    rw [basisVector_coordinate]
    dsimp only [a, D]
    rw [div_mul_cancel₀ _ hdet, sub_self]
  have hZexpand : (∑ i : ι, b.repr Z (some i) • b (some i)) = Z := by
    simpa only [Fintype.sum_option, hZcoord, zero_smul, add_zero, zero_add] using b.sum_repr Z
  have hmatrix : (pivotMatrix L (fun i => b (some i))).mulVec
      (fun i => b.repr Z (some i)) = 0 := by
    rw [← apply_sum_smul, hZexpand, hZL]
  have hcoordinates : (fun i => b.repr Z (some i)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmatrix
  have hZzero : Z = 0 := by
    rw [← hZexpand]
    apply Finset.sum_eq_zero
    intro i _
    rw [congrFun hcoordinates i, Pi.zero_apply, zero_smul]
  exact ⟨a, sub_eq_zero.mp hZzero⟩

theorem basisVector_ne_zero (L : M →ₗ[k] (ι → k))
    (b : Module.Basis (Option ι) k M)
    (hdet : (pivotMatrix L (fun i => b (some i))).det ≠ 0) :
    basisVector L b ≠ 0 := by
  intro h
  have hc := basisVector_coordinate L b
  rw [h, map_zero, Finsupp.zero_apply] at hc
  exact hdet hc.symm

end BasisConstruction

section TwistConstruction

open RB31E2E

variable {R : Type*} [CommRing R]

/-- The same actual twist evaluation is linear over a commutative ring,
so the cofactor construction applies directly over a polynomial ring. -/
def evaluation (p : RB31E2E.Vec3 R) : RB31E2E.Twist R →ₗ[R] RB31E2E.Vec3 R where
  toFun X := RB31E2E.Twist.eval X p
  map_add' X Y := by
    change (X.2 + Y.2) + RB31E2E.Vec3.cross (X.1 + Y.1) p =
      (X.2 + RB31E2E.Vec3.cross X.1 p) + (Y.2 + RB31E2E.Vec3.cross Y.1 p)
    rw [RB31E2E.Vec3.cross_add_left]
    abel
  map_smul' a X := by
    change a • X.2 + RB31E2E.Vec3.cross (a • X.1) p =
      a • (X.2 + RB31E2E.Vec3.cross X.1 p)
    rw [RB31E2E.Vec3.cross_smul_left, smul_add]

theorem cofactor_twist_fixes_pin (p : RB31E2E.Vec3 R) (w : Fin 3 → RB31E2E.Twist R) (v : RB31E2E.Twist R) :
    RB31E2E.Twist.eval (vector (evaluation p) w v) p = 0 :=
  apply_vector_eq_zero (evaluation p) w v

/-- Moving the pin along a stationary twist's own angular direction
preserves its actual velocity. This identity also applies after polynomial
or rational-function base change. -/
theorem eval_on_axis (X : RB31E2E.Twist R) (p : RB31E2E.Vec3 R) (t : R) :
    RB31E2E.Twist.eval X (p + t • X.1) = RB31E2E.Twist.eval X p := by
  funext i
  fin_cases i <;> simp [RB31E2E.Twist.eval, RB31E2E.Vec3.cross] <;> ring

end TwistConstruction

section AxisRigidity

open RB31E2E

variable {k : Type*} [Field k]

/-- Two twists fixing the same whole nontrivial rotation axis are
proportional. Only two distinct points of that axis are needed. The
nonzero angular-part premise is derived from the nonzero stationary twist. -/
theorem eq_smul_of_two_axis_pins (X Y : RB31E2E.Twist k) (p : RB31E2E.Vec3 k)
    (hX : X ≠ 0) (hXp : RB31E2E.Twist.eval X p = 0)
    (hYp : RB31E2E.Twist.eval Y p = 0)
    (hYaxis : RB31E2E.Twist.eval Y (p + X.1) = 0) :
    ∃ a : k, Y = a • X := by
  have hω := RB31E2E.Twist.angular_ne_zero_of_ne_zero_of_eval_eq_zero X p hX hXp
  have hcross : RB31E2E.Vec3.cross Y.1 X.1 = 0 := by
    simpa only [add_sub_cancel_left] using
      RB31E2E.Twist.cross_pin_sub_eq_zero Y p (p + X.1) hYp hYaxis
  have hswap : RB31E2E.Vec3.cross X.1 Y.1 = 0 := by
    have hanti : RB31E2E.Vec3.cross X.1 Y.1 = -RB31E2E.Vec3.cross Y.1 X.1 := by
      funext i
      fin_cases i <;> simp [RB31E2E.Vec3.cross] <;> ring
    rw [hanti, hcross, neg_zero]
  obtain ⟨a, ha⟩ := (RB31E2E.Vec3.cross_eq_zero_iff_eq_smul X.1 Y.1 hω).mp hswap
  refine ⟨a, Prod.ext ha ?_⟩
  have hx : X.2 = -RB31E2E.Vec3.cross X.1 p := by
    exact eq_neg_of_add_eq_zero_left hXp
  have hy : Y.2 = -RB31E2E.Vec3.cross Y.1 p := by
    exact eq_neg_of_add_eq_zero_left hYp
  change Y.2 = a • X.2
  rw [hy, ha, RB31E2E.Vec3.cross_smul_left, hx, smul_neg]

/-- The second axis point may be any nonzero scalar displacement. This
form permits keeping both pins inside a prescribed nonzero-minor chart. -/
theorem eq_smul_of_two_scaled_axis_pins (X Y : RB31E2E.Twist k) (p : RB31E2E.Vec3 k) (t : k)
    (ht : t ≠ 0) (hX : X ≠ 0) (hXp : RB31E2E.Twist.eval X p = 0)
    (hYp : RB31E2E.Twist.eval Y p = 0)
    (hYaxis : RB31E2E.Twist.eval Y (p + t • X.1) = 0) :
    ∃ a : k, Y = a • X := by
  have hscaled : t • RB31E2E.Vec3.cross Y.1 X.1 = 0 := by
    have hid : t • RB31E2E.Vec3.cross Y.1 X.1 =
        RB31E2E.Vec3.cross Y.1 ((p + t • X.1) - p) := by
      funext i
      fin_cases i <;> simp [RB31E2E.Vec3.cross] <;> ring
    rw [hid]
    exact RB31E2E.Twist.cross_pin_sub_eq_zero Y p (p + t • X.1) hYp hYaxis
  have hcross : RB31E2E.Vec3.cross Y.1 X.1 = 0 :=
    (smul_eq_zero.mp hscaled).resolve_left ht
  apply eq_smul_of_two_axis_pins X Y p hX hXp hYp
  have hid : RB31E2E.Twist.eval Y (p + X.1) = RB31E2E.Twist.eval Y p + RB31E2E.Vec3.cross Y.1 X.1 := by
    have hadd : RB31E2E.Vec3.cross Y.1 (p + X.1) =
        RB31E2E.Vec3.cross Y.1 p + RB31E2E.Vec3.cross Y.1 X.1 := by
      funext i
      fin_cases i <;> simp [RB31E2E.Vec3.cross] <;> ring
    change Y.2 + RB31E2E.Vec3.cross Y.1 (p + X.1) =
      (Y.2 + RB31E2E.Vec3.cross Y.1 p) + RB31E2E.Vec3.cross Y.1 X.1
    rw [hadd, add_assoc]
  rw [hid, hYp, hcross, add_zero]

end AxisRigidity

end

end Papers.Rigidity.CofactorKernel

end
end BundleSource0005

section BundleSource0006
/- Source: Papers/RigidityCofactorEigenvectors.lean -/







@[expose] public section

/-!
# Common generic pins force pointwise eigenvectors

The cofactor kernel line at a pin is unchanged when the pin moves a
short nonzero distance along its own rotation axis. A second body map
that fixes every such pin must consequently fix two points of that axis,
and its twist is proportional. The argument stays in the ordinary real
nonzero-minor chart and needs no assumption about an image's closure.

These eigenvector relations supply a step of Proposition 4.1.
-/

namespace Papers.Rigidity.CofactorKernel

noncomputable section

open RB31E2E
open scoped Topology

/-- A nonzero value of a continuous determinant remains nonzero at a
second point on every prescribed affine line. The displacement is
explicitly nonzero, even if the line's direction itself happens to vanish. -/
theorem exists_nonzero_axis_displacement (D : RB31E2E.Vec3 ℝ → ℝ) (hD : Continuous D)
    (p w : RB31E2E.Vec3 ℝ) (hp : D p ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ D (p + t • w) ≠ 0 := by
  have hcont : Continuous (fun t : ℝ => D (p + t • w)) :=
    hD.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, D (p + t • w) ≠ 0 :=
    (isOpen_ne_fun hcont continuous_const).mem_nhds (by simpa using hp)
  have hpunctured : ∀ᶠ t : ℝ in 𝓝[≠] 0, D (p + t • w) ≠ 0 :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htD, ht⟩ := (hpunctured.and self_mem_nhdsWithin).exists
  exact ⟨t, (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht), htD⟩

/-- Pointwise eigenvector conclusion for the actual first-body kernel
line and the actual linear second-body map. In the intended application
`D` and `C` are the pivot determinant and its explicit Cramer vector;
`hkernel` is the rank-three evaluation calculation, proved separately. -/
theorem common_pin_map_is_eigenvector
    (W : Submodule ℝ (RB31E2E.Twist ℝ)) (T : W →ₗ[ℝ] RB31E2E.Twist ℝ)
    (D : RB31E2E.Vec3 ℝ → ℝ) (hD : Continuous D) (C : RB31E2E.Vec3 ℝ → W)
    (hCfix : ∀ p, RB31E2E.Twist.eval (C p).val p = 0)
    (hCne : ∀ p, D p ≠ 0 → (C p).val ≠ 0)
    (hkernel : ∀ p, D p ≠ 0 → ∀ X : W, RB31E2E.Twist.eval X.val p = 0 →
      ∃ a : ℝ, X = a • C p)
    (hTfix : ∀ p, D p ≠ 0 → RB31E2E.Twist.eval (T (C p)) p = 0)
    (p : RB31E2E.Vec3 ℝ) (hp : D p ≠ 0) :
    ∃ a : ℝ, T (C p) = a • (C p).val := by
  obtain ⟨t, ht, hq⟩ := exists_nonzero_axis_displacement D hD p (C p).val.1 hp
  let q := p + t • (C p).val.1
  have hCq : RB31E2E.Twist.eval (C p).val q = 0 := by
    dsimp only [q]
    rw [eval_on_axis]
    exact hCfix p
  obtain ⟨b, hb⟩ := hkernel q hq (C p) hCq
  have hTq : RB31E2E.Twist.eval (T (C p)) q = 0 := by
    rw [hb, map_smul]
    change evaluation q (b • T (C q)) = 0
    rw [map_smul]
    change b • RB31E2E.Twist.eval (T (C q)) q = 0
    rw [hTfix q hq, smul_zero]
  exact eq_smul_of_two_scaled_axis_pins (C p).val (T (C p)) p t ht
    (hCne p hp) (hCfix p) (hTfix p hp) hTq

def restrictedEvaluation (W : Submodule ℝ (RB31E2E.Twist ℝ)) (p : RB31E2E.Vec3 ℝ) :
    W →ₗ[ℝ] RB31E2E.Vec3 ℝ := (evaluation p).comp W.subtype

def minor (W : Submodule ℝ (RB31E2E.Twist ℝ)) (b : Module.Basis (Option (Fin 3)) ℝ W)
    (p : RB31E2E.Vec3 ℝ) : ℝ :=
  (pivotMatrix (restrictedEvaluation W p) (fun i => b (some i))).det

def cofactor (W : Submodule ℝ (RB31E2E.Twist ℝ)) (b : Module.Basis (Option (Fin 3)) ℝ W)
    (p : RB31E2E.Vec3 ℝ) : W := basisVector (restrictedEvaluation W p) b

theorem minor_continuous (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) : Continuous (minor W b) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;>
    simp [pivotMatrix, restrictedEvaluation, evaluation, RB31E2E.Twist.eval, RB31E2E.Vec3.cross] <;> fun_prop

/-- For an actual four-dimensional first-body twist space the kernel
line, its nonvanishing and its nonzero-minor neighborhood are all supplied
by the displayed basis and its Cramer cofactors. Only the substantive
second-body common-pin identity remains as a hypothesis. -/
theorem cofactor_common_pin_map_is_eigenvector
    (W : Submodule ℝ (RB31E2E.Twist ℝ)) (b : Module.Basis (Option (Fin 3)) ℝ W)
    (T : W →ₗ[ℝ] RB31E2E.Twist ℝ)
    (hTfix : ∀ p, minor W b p ≠ 0 → RB31E2E.Twist.eval (T (cofactor W b p)) p = 0)
    (p : RB31E2E.Vec3 ℝ) (hp : minor W b p ≠ 0) :
    ∃ a : ℝ, T (cofactor W b p) = a • (cofactor W b p).val := by
  apply common_pin_map_is_eigenvector W T (minor W b) (minor_continuous W b)
    (cofactor W b) _ _ _ hTfix p hp
  · intro q
    exact apply_vector_eq_zero (restrictedEvaluation W q)
      (fun i => b (some i)) (b none)
  · intro q hq hz
    have hz' : cofactor W b q = 0 := Subtype.ext hz
    exact basisVector_ne_zero (restrictedEvaluation W q) b hq hz'
  · intro q hq X hX
    exact kernel_vector_eq_smul_basisVector (restrictedEvaluation W q) b hq X hX

end

end Papers.Rigidity.CofactorKernel

end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0006/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityPolynomialImageSpan.lean -/





@[expose] public section

/-!
# Actual polynomial images and their coefficient spans

These are the elementary algebraic steps needed by the cofactor-kernel
reconstruction of Proposition 4.1. They do not assume an irreducibility or
image-closure statement. The polynomial family is literal, and each span
is taken in the original finite coordinate vector space.

The span is computed from the literal polynomial image.
-/

namespace Papers.Rigidity.PolynomialImageSpan

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {k σ ι : Type*} [Field k] [Infinite k] [Fintype ι]

def evaluationVector (p : ι → MvPolynomial σ k) (x : σ → k) : ι → k :=
  fun i => MvPolynomial.eval x (p i)

def coefficientVector (p : ι → MvPolynomial σ k) (d : σ →₀ ℕ) : ι → k :=
  fun i => (p i).coeff d

theorem exists_evaluation_ne_zero (p : MvPolynomial σ k) (hp : p ≠ 0) :
    ∃ x : σ → k, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro x
  have hx : MvPolynomial.eval x p = 0 := by
    by_contra hx
    exact h ⟨x, hx⟩
  simpa only [map_zero] using hx

private theorem linearFunctional_pi [DecidableEq ι]
    (L : (ι → k) →ₗ[k] k) (v : ι → k) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  have hdecomp : (∑ i, v i • Pi.single i (1 : k)) = v := by
    funext j
    simp [Pi.single_apply]
  calc
    L v = L (∑ i, v i • Pi.single i (1 : k)) := congrArg L hdecomp.symm
    _ = ∑ i, L (Pi.single i 1) * v i := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- Apply an ordinary linear functional to the vector polynomial,
coefficient by coefficient. -/
def functionalPolynomial [DecidableEq ι]
    (p : ι → MvPolynomial σ k) (L : (ι → k) →ₗ[k] k) : MvPolynomial σ k :=
  ∑ i, MvPolynomial.C (L (Pi.single i 1)) * p i

theorem eval_functionalPolynomial [DecidableEq ι]
    (p : ι → MvPolynomial σ k) (L : (ι → k) →ₗ[k] k) (x : σ → k) :
    MvPolynomial.eval x (functionalPolynomial p L) = L (evaluationVector p x) := by
  rw [linearFunctional_pi]
  simp [functionalPolynomial, evaluationVector]

theorem coeff_functionalPolynomial [DecidableEq ι]
    (p : ι → MvPolynomial σ k) (L : (ι → k) →ₗ[k] k) (d : σ →₀ ℕ) :
    (functionalPolynomial p L).coeff d = L (coefficientVector p d) := by
  rw [linearFunctional_pi]
  simp [functionalPolynomial, coefficientVector, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul]

/-- Membership of every actual polynomial value in a subspace forces
membership of every coefficient vector. -/
theorem coefficientVector_mem_of_evaluationVector_mem
    (p : ι → MvPolynomial σ k) (H : Submodule k (ι → k))
    (h : ∀ x, evaluationVector p x ∈ H) (d : σ →₀ ℕ) :
    coefficientVector p d ∈ H := by
  classical
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff H _).mp
  intro L hL
  have hzero : functionalPolynomial p L = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_functionalPolynomial, map_zero]
    exact (Submodule.mem_dualAnnihilator L).mp hL _ (h x)
  have hc := congrArg (fun q : MvPolynomial σ k => q.coeff d) hzero
  simpa only [coeff_functionalPolynomial, MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

/-- The converse coefficient-to-value implication uses the actual
coefficient identity and ordinary polynomial extensionality. -/
theorem evaluationVector_mem_of_coefficientVector_mem
    (p : ι → MvPolynomial σ k) (H : Submodule k (ι → k))
    (h : ∀ d, coefficientVector p d ∈ H) (x : σ → k) :
    evaluationVector p x ∈ H := by
  classical
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff H _).mp
  intro L hL
  have hzero : functionalPolynomial p L = 0 := by
    ext d
    rw [coeff_functionalPolynomial, MvPolynomial.coeff_zero, Finsupp.zero_apply]
    exact (Submodule.mem_dualAnnihilator L).mp hL _ (h d)
  have he := congrArg (MvPolynomial.eval x) hzero
  simpa only [eval_functionalPolynomial, map_zero] using he

/-- The span of all actual values is exactly the coefficient span. This
is the bridge needed before extending that span to a rational function
field and applying generic-pin dimension arguments. -/
theorem span_evaluationVector_eq_span_coefficientVector
    (p : ι → MvPolynomial σ k) :
    Submodule.span k (Set.range (evaluationVector p)) =
      Submodule.span k (Set.range (coefficientVector p)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact evaluationVector_mem_of_coefficientVector_mem p
      (Submodule.span k (Set.range (coefficientVector p)))
      (fun d => Submodule.subset_span ⟨d, rfl⟩) x
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact coefficientVector_mem_of_evaluationVector_mem p
      (Submodule.span k (Set.range (evaluationVector p)))
      (fun x => Submodule.subset_span ⟨x, rfl⟩) d

/-- It is enough to inspect the actual values where one specified
nonzero polynomial does not vanish. Multiplication by that polynomial
replaces any appeal to an unspecified algebraic closure of the image. -/
theorem coefficientVector_mem_of_evaluationVector_mem_on_nonzero_chart
    (D : MvPolynomial σ k) (hD : D ≠ 0)
    (p : ι → MvPolynomial σ k) (H : Submodule k (ι → k))
    (h : ∀ x, MvPolynomial.eval x D ≠ 0 → evaluationVector p x ∈ H)
    (d : σ →₀ ℕ) : coefficientVector p d ∈ H := by
  classical
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff H _).mp
  intro L hL
  have hproduct : D * functionalPolynomial p L = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [MvPolynomial.eval_mul, eval_functionalPolynomial, map_zero]
    by_cases hx : MvPolynomial.eval x D = 0
    · rw [hx, zero_mul]
    · rw [(Submodule.mem_dualAnnihilator L).mp hL _ (h x hx), mul_zero]
  have hzero : functionalPolynomial p L = 0 := (mul_eq_zero.mp hproduct).resolve_left hD
  have hc := congrArg (fun q : MvPolynomial σ k => q.coeff d) hzero
  simpa only [coeff_functionalPolynomial, MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

/-- Restricting the parameter space to a genuine nonzero-minor chart
does not change the span of a polynomial image. -/
theorem span_evaluationVector_on_nonzero_chart
    (D : MvPolynomial σ k) (hD : D ≠ 0) (p : ι → MvPolynomial σ k) :
    Submodule.span k (Set.range (fun x : {x : σ → k // MvPolynomial.eval x D ≠ 0} =>
      evaluationVector p x.val)) =
        Submodule.span k (Set.range (coefficientVector p)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact evaluationVector_mem_of_coefficientVector_mem p
      (Submodule.span k (Set.range (coefficientVector p)))
      (fun d => Submodule.subset_span ⟨d, rfl⟩) x.val
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    apply coefficientVector_mem_of_evaluationVector_mem_on_nonzero_chart D hD p
    intro x hx
    exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

/-- If the nonzero polynomial coordinates of a family are simultaneously
eigenvector coordinates at every point, all diagonal eigenvalues agree.
The nonvanishing premises are substantive: in the intended application,
the basis is selected from actual image values, giving value one for the
corresponding coordinate polynomial at its basis witness. -/
theorem diagonal_eigenvalues_eq_of_polynomial_family
    (f : ι → MvPolynomial σ k) (hf : ∀ i, f i ≠ 0)
    (eigenvalue : ι → k)
    (h : ∀ x : σ → k, ∃ a : k, ∀ i,
      eigenvalue i * MvPolynomial.eval x (f i) =
        a * MvPolynomial.eval x (f i)) :
    ∀ i j, eigenvalue i = eigenvalue j := by
  intro i j
  have hnonzero : f i * f j ≠ 0 := mul_ne_zero (hf i) (hf j)
  have hwitness : ∃ x : σ → k, MvPolynomial.eval x (f i * f j) ≠ 0 := by
    by_contra hn
    apply hnonzero
    apply MvPolynomial.funext
    intro x
    have hz : MvPolynomial.eval x (f i * f j) = 0 := by
      by_contra hx
      exact hn ⟨x, hx⟩
    simpa only [map_zero] using hz
  obtain ⟨x, hx⟩ := hwitness
  have hi : MvPolynomial.eval x (f i) ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  have hj : MvPolynomial.eval x (f j) ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  obtain ⟨a, ha⟩ := h x
  exact (mul_right_cancel₀ hi (ha i)).trans (mul_right_cancel₀ hj (ha j)).symm

/-- The same eigenvalue conclusion holds when the pointwise identity is
known only on a nonzero pivot chart. A witness where `D fᵢ fⱼ` is nonzero
simultaneously justifies all three cancellations. -/
theorem diagonal_eigenvalues_eq_of_polynomial_family_on_nonzero_chart
    (D : MvPolynomial σ k) (hD : D ≠ 0)
    (f : ι → MvPolynomial σ k) (hf : ∀ i, f i ≠ 0)
    (eigenvalue : ι → k)
    (h : ∀ x : σ → k, MvPolynomial.eval x D ≠ 0 → ∃ a : k, ∀ i,
      eigenvalue i * MvPolynomial.eval x (f i) =
        a * MvPolynomial.eval x (f i)) :
    ∀ i j, eigenvalue i = eigenvalue j := by
  intro i j
  obtain ⟨x, hx⟩ := exists_evaluation_ne_zero (D * f i * f j)
    (mul_ne_zero (mul_ne_zero hD (hf i)) (hf j))
  have hDx : MvPolynomial.eval x D ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  have hi : MvPolynomial.eval x (f i) ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  have hj : MvPolynomial.eval x (f j) ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  obtain ⟨a, ha⟩ := h x hDx
  exact (mul_right_cancel₀ hi (ha i)).trans (mul_right_cancel₀ hj (ha j)).symm

end

end Papers.Rigidity.PolynomialImageSpan

end
end BundleSource0007

section BundleSource0008
/- Source: Papers/RigidityCofactorPolynomial.lean -/





@[expose] public section

/-!
# Polynomial coordinates of the actual common-pin kernel

The polynomials in this file are the literal determinants of the twist
evaluation matrix. Their values are proved to be the coordinates of the
Cramer kernel vector already constructed in the original twist space.
Thus the polynomial-image arguments apply to the actual kernel family,
without assuming an algebraic image or its closure has any prescribed
dimension.

These polynomial calculations supply the cofactor step of Proposition 4.1.
-/

namespace Papers.Rigidity.CofactorKernel

noncomputable section

open RB31E2E
open scoped BigOperators

abbrev PinPolynomial := MvPolynomial (Fin 3) ℝ

def polynomialTwist (X : RB31E2E.Twist ℝ) : RB31E2E.Twist PinPolynomial :=
  (fun i => MvPolynomial.C (X.1 i), fun i => MvPolynomial.C (X.2 i))

def polynomialEvaluation (X : RB31E2E.Twist ℝ) : Fin 3 → PinPolynomial :=
  RB31E2E.Twist.eval (polynomialTwist X) MvPolynomial.X

theorem eval_polynomialEvaluation (X : RB31E2E.Twist ℝ) (p : RB31E2E.Vec3 ℝ) (i : Fin 3) :
    MvPolynomial.eval p (polynomialEvaluation X i) = RB31E2E.Twist.eval X p i := by
  fin_cases i <;> simp [polynomialEvaluation, polynomialTwist, RB31E2E.Twist.eval, RB31E2E.Vec3.cross]

def polynomialPivot (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) : Matrix (Fin 3) (Fin 3) PinPolynomial :=
  fun i j => polynomialEvaluation (b (some j)).val i

def polynomialMinor (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) : PinPolynomial :=
  (polynomialPivot W b).det

def polynomialCofactorCoordinates (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) : Option (Fin 3) → PinPolynomial
  | none => polynomialMinor W b
  | some i => -Matrix.cramer (polynomialPivot W b)
      (polynomialEvaluation (b none).val) i

theorem eval_polynomialPivot (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : RB31E2E.Vec3 ℝ) :
    (polynomialPivot W b).map (MvPolynomial.eval p) =
      pivotMatrix (restrictedEvaluation W p) (fun i => b (some i)) := by
  ext i j
  exact eval_polynomialEvaluation (b (some j)).val p i

theorem eval_polynomialMinor (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : RB31E2E.Vec3 ℝ) :
    MvPolynomial.eval p (polynomialMinor W b) = minor W b p := by
  unfold polynomialMinor minor
  rw [(MvPolynomial.eval p).map_det]
  change ((polynomialPivot W b).map (MvPolynomial.eval p)).det = _
  rw [eval_polynomialPivot]

theorem eval_polynomialCramer (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : RB31E2E.Vec3 ℝ) (i : Fin 3) :
    MvPolynomial.eval p
      (Matrix.cramer (polynomialPivot W b) (polynomialEvaluation (b none).val) i) =
      Matrix.cramer (pivotMatrix (restrictedEvaluation W p) (fun j => b (some j)))
        (restrictedEvaluation W p (b none)) i := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, (MvPolynomial.eval p).map_det]
  change (((polynomialPivot W b).updateCol i
    (polynomialEvaluation (b none).val)).map (MvPolynomial.eval p)).det = _
  rw [Matrix.map_updateCol, eval_polynomialPivot]
  congr 2
  funext j
  exact eval_polynomialEvaluation (b none).val p j

theorem cofactor_coordinate_some (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : RB31E2E.Vec3 ℝ) (i : Fin 3) :
    b.repr (cofactor W b p) (some i) =
      -Matrix.cramer (pivotMatrix (restrictedEvaluation W p) (fun j => b (some j)))
        (restrictedEvaluation W p (b none)) i := by
  change (b.coord (some i)) (vector (restrictedEvaluation W p)
    (fun j => b (some j)) (b none)) = _
  simp [vector, Module.Basis.coord_apply, Finsupp.single_apply]

/-- Every displayed polynomial evaluates to the matching actual basis
coordinate of the stationary cofactor twist. -/
theorem eval_polynomialCofactorCoordinates (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : RB31E2E.Vec3 ℝ) (i : Option (Fin 3)) :
    MvPolynomial.eval p (polynomialCofactorCoordinates W b i) =
      b.repr (cofactor W b p) i := by
  cases i with
  | none =>
    change MvPolynomial.eval p (polynomialMinor W b) =
      b.repr (basisVector (restrictedEvaluation W p) b) none
    rw [eval_polynomialMinor, basisVector_coordinate]
    rfl
  | some i =>
    change MvPolynomial.eval p (-Matrix.cramer (polynomialPivot W b)
      (polynomialEvaluation (b none).val) i) = _
    rw [map_neg, eval_polynomialCramer, cofactor_coordinate_some]

theorem polynomialMinor_ne_zero_of_witness (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) {p : RB31E2E.Vec3 ℝ}
    (hp : minor W b p ≠ 0) : polynomialMinor W b ≠ 0 := by
  intro hz
  apply hp
  rw [← eval_polynomialMinor W b p, hz, map_zero]

end

end Papers.Rigidity.CofactorKernel

end
end BundleSource0008

section BundleSource0009
/- Source: Papers/RigidityPolynomialEigenvectors.lean -/





@[expose] public section

/-!
# A linear map on an actual polynomial eigenvector family

If every value of a polynomial family on a nonzero polynomial chart is
an eigenvector of one fixed linear map, that map is a single scalar on
the span of those actual values. The basis is selected from the image;
each coordinate polynomial is consequently nonzero at its own basis
witness. The integral-domain argument then forces all eigenvalues to
agree. No irreducibility, image closure, or assumed image dimension is
used.

These polynomial eigenvector identities support Proposition 4.1.
-/

namespace Papers.Rigidity.PolynomialImageSpan

noncomputable section

open Module MvPolynomial
open scoped BigOperators

variable {k σ ι : Type*} [Field k] [Infinite k] [Fintype ι]

/-- Pointwise eigenvectors in one actual polynomial family determine
one scalar on their full linear span. Zero families and zero spans are
included rather than excluded by an extra nondegeneracy assumption. -/
theorem scalar_on_span_of_polynomial_eigenvectors
    (D : MvPolynomial σ k) (hD : D ≠ 0)
    (p : ι → MvPolynomial σ k) (T : (ι → k) →ₗ[k] (ι → k))
    (heigen : ∀ x : σ → k, MvPolynomial.eval x D ≠ 0 →
      ∃ a : k, T (evaluationVector p x) = a • evaluationVector p x) :
    ∃ a : k, ∀ v ∈ Submodule.span k
      (Set.range (fun x : {x : σ → k // MvPolynomial.eval x D ≠ 0} =>
        evaluationVector p x.val)), T v = a • v := by
  classical
  let X := {x : σ → k // MvPolynomial.eval x D ≠ 0}
  let c : X → (ι → k) := fun x => evaluationVector p x.val
  let H := Submodule.span k (Set.range c)
  let S : Set H := Subtype.val ⁻¹' Set.range c
  have hspan : ⊤ ≤ Submodule.span k S := by
    rw [show Submodule.span k S = ⊤ from Submodule.span_span_coe_preimage]
  let b := Basis.ofSpan hspan
  let J := (linearIndepOn_empty k (id : H → H)).extend (Set.empty_subset S)
  let hb : Basis J k H := b
  letI : Fintype J := FiniteDimensional.fintypeBasisIndex hb
  have hbimage : ∀ j : J, ∃ x : X, (hb j).val = c x := by
    intro j
    have hm : hb j ∈ S := Basis.ofSpan_subset hspan (Set.mem_range_self j)
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, hx.symm⟩
  choose witness hwitness using hbimage
  have hpreserve : ∀ v ∈ H, T v ∈ H := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      obtain ⟨a, ha⟩ := heigen x.val x.property
      rw [ha]
      exact H.smul_mem a (Submodule.subset_span (Set.mem_range_self x))
    | zero => simpa only [map_zero] using H.zero_mem
    | add u v hu hv ihu ihv => simpa only [map_add] using H.add_mem ihu ihv
    | smul a v hv ih => simpa only [map_smul] using H.smul_mem a ih
  let TH : H →ₗ[k] H := (T.comp H.subtype).codRestrict H
    (fun u => hpreserve u.val u.property)
  have hbeigen : ∀ j : J, ∃ a : k, TH (hb j) = a • hb j := by
    intro j
    obtain ⟨a, ha⟩ := heigen (witness j).val (witness j).property
    refine ⟨a, Subtype.ext ?_⟩
    change T (hb j).val = a • (hb j).val
    rw [hwitness j]
    exact ha
  choose lam hlam using hbeigen
  have hdiagonal (u : H) (j : J) :
      hb.coord j (TH u) = lam j * hb.coord j u := by
    have hmaps : (hb.coord j).comp TH = lam j • hb.coord j := by
      apply hb.ext
      intro i
      change hb.coord j (TH (hb i)) = lam j * hb.coord j (hb i)
      rw [hlam, map_smul, smul_eq_mul]
      by_cases hij : i = j
      · subst i
        rfl
      · have hzero : hb.coord j (hb i) = 0 := by
          simp [Basis.coord_apply, Finsupp.single_apply, hij]
        rw [hzero, mul_zero, mul_zero]
    exact congrArg (fun F : H →ₗ[k] k => F u) hmaps
  choose L hL using fun j : J => LinearMap.exists_extend (hb.coord j)
  let f : J → MvPolynomial σ k := fun j => functionalPolynomial p (L j)
  have hfvalue (j : J) (x : X) :
      MvPolynomial.eval x.val (f j) =
        hb.coord j ⟨c x, Submodule.subset_span (Set.mem_range_self x)⟩ := by
    rw [show f j = functionalPolynomial p (L j) from rfl, eval_functionalPolynomial]
    have h := congrArg (fun A : H →ₗ[k] k =>
      A ⟨c x, Submodule.subset_span (Set.mem_range_self x)⟩) (hL j)
    exact h
  have hfne : ∀ j : J, f j ≠ 0 := by
    intro j hz
    have h := hfvalue j (witness j)
    have he : (⟨c (witness j), Submodule.subset_span (Set.mem_range_self (witness j))⟩ : H)
        = hb j := Subtype.ext (hwitness j).symm
    rw [hz, map_zero, he] at h
    exact (zero_ne_one : (0 : k) ≠ 1) (by
      simpa [Basis.coord_apply, Finsupp.single_apply] using h)
  have hpointwise : ∀ x : σ → k, MvPolynomial.eval x D ≠ 0 → ∃ a : k, ∀ j : J,
      lam j * MvPolynomial.eval x (f j) = a * MvPolynomial.eval x (f j) := by
    intro x hx
    let x' : X := ⟨x, hx⟩
    let u : H := ⟨c x', Submodule.subset_span (Set.mem_range_self x')⟩
    obtain ⟨a, ha⟩ := heigen x hx
    have hTu : TH u = a • u := Subtype.ext ha
    refine ⟨a, ?_⟩
    intro j
    change lam j * MvPolynomial.eval x'.val (f j) =
      a * MvPolynomial.eval x'.val (f j)
    rw [hfvalue j x']
    change lam j * hb.coord j u = a * hb.coord j u
    rw [← hdiagonal u j, hTu, map_smul, smul_eq_mul]
  have hequal := diagonal_eigenvalues_eq_of_polynomial_family_on_nonzero_chart
    D hD f hfne lam hpointwise
  rcases isEmpty_or_nonempty J with hJ | hJ
  · letI := hJ
    refine ⟨0, ?_⟩
    intro v hv
    have hvzero : (⟨v, hv⟩ : H) = 0 := by
      simpa using (hb.sum_repr (⟨v, hv⟩ : H)).symm
    have hvzero' : v = 0 := congrArg Subtype.val hvzero
    simp [hvzero']
  · letI := hJ
    let j₀ : J := Classical.choice hJ
    have hscalar : TH = lam j₀ • LinearMap.id := by
      apply hb.ext
      intro j
      simpa only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, hequal j j₀] using hlam j
    refine ⟨lam j₀, ?_⟩
    intro v hv
    have h := congrArg (fun A : H →ₗ[k] H => (A ⟨v, hv⟩).val) hscalar
    exact h

end

end Papers.Rigidity.PolynomialImageSpan

end
end BundleSource0009

section BundleSource0010
/- Source: Papers/RigidityCofactorScalar.lean -/




@[expose] public section

/-!
# One scalar on the actual common-pin kernel image

This combines the literal Cramer polynomial family with the two-axis-pin
argument. A linear map to a second body's twist space that fixes the
same generic new pins is a single scalar on the span of the first body's
actual stationary twists. The image span is explicitly defined from real
pins; no closure, irreducibility, or prescribed image dimension is assumed.

The scalar relation supplies the next step of Proposition 4.1.
-/

namespace Papers.Rigidity.CofactorKernel

noncomputable section

open RB31E2E

def cofactorImageSpan (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) : Submodule ℝ W :=
  Submodule.span ℝ (Set.range
    (fun p : {p : RB31E2E.Vec3 ℝ // minor W b p ≠ 0} => cofactor W b p.val))

theorem cofactor_mem_imageSpan (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : RB31E2E.Vec3 ℝ) (hp : minor W b p ≠ 0) :
    cofactor W b p ∈ cofactorImageSpan W b := by
  unfold cofactorImageSpan
  apply Submodule.subset_span
  exact ⟨⟨p, hp⟩, rfl⟩

theorem polynomialCoordinates_eq_equivFun (W : Submodule ℝ (RB31E2E.Twist ℝ))
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : RB31E2E.Vec3 ℝ) :
    PolynomialImageSpan.evaluationVector (polynomialCofactorCoordinates W b) p =
      b.equivFun (cofactor W b p) := by
  funext i
  rw [Module.Basis.equivFun_apply]
  exact eval_polynomialCofactorCoordinates W b p i

/-- A common-pin map has one scalar on the entire span of the actual
kernel family. The nonzero-minor witness is the genuine rank-three
evaluation condition for the selected four-dimensional twist basis. -/
theorem cofactor_common_pin_map_scalar
    (W : Submodule ℝ (RB31E2E.Twist ℝ)) (b : Module.Basis (Option (Fin 3)) ℝ W)
    (T : W →ₗ[ℝ] RB31E2E.Twist ℝ)
    (hwitness : ∃ p : RB31E2E.Vec3 ℝ, minor W b p ≠ 0)
    (hTfix : ∀ p, minor W b p ≠ 0 → RB31E2E.Twist.eval (T (cofactor W b p)) p = 0) :
    ∃ a : ℝ, ∀ X ∈ cofactorImageSpan W b, T X = a • X.val := by
  classical
  obtain ⟨R, hR⟩ := LinearMap.exists_extend (LinearMap.id : W →ₗ[ℝ] W)
  have hRval (X : W) : R X.val = X :=
    congrArg (fun A : W →ₗ[ℝ] W => A X) hR
  let A : (Option (Fin 3) → ℝ) →ₗ[ℝ] (Option (Fin 3) → ℝ) :=
    b.equivFun.toLinearMap.comp ((R.comp T).comp b.equivFun.symm.toLinearMap)
  have heigen (p : RB31E2E.Vec3 ℝ) (hp : minor W b p ≠ 0) :
      ∃ a : ℝ, A (b.equivFun (cofactor W b p)) =
        a • b.equivFun (cofactor W b p) := by
    obtain ⟨a, ha⟩ := cofactor_common_pin_map_is_eigenvector W b T hTfix p hp
    refine ⟨a, ?_⟩
    change b.equivFun (R (T (b.equivFun.symm (b.equivFun (cofactor W b p))))) = _
    rw [b.equivFun.symm_apply_apply, ha, map_smul, hRval, map_smul]
  obtain ⟨p₀, hp₀⟩ := hwitness
  obtain ⟨a, ha⟩ := PolynomialImageSpan.scalar_on_span_of_polynomial_eigenvectors
    (polynomialMinor W b) (polynomialMinor_ne_zero_of_witness W b hp₀)
    (polynomialCofactorCoordinates W b) A (by
      intro p hp
      rw [eval_polynomialMinor] at hp
      rw [polynomialCoordinates_eq_equivFun]
      exact heigen p hp)
  have hfamily (p : RB31E2E.Vec3 ℝ) (hp : minor W b p ≠ 0) :
      T (cofactor W b p) = a • (cofactor W b p).val := by
    have hpPoly : MvPolynomial.eval p (polynomialMinor W b) ≠ 0 := by
      rwa [eval_polynomialMinor]
    have hmem : PolynomialImageSpan.evaluationVector
        (polynomialCofactorCoordinates W b) p ∈ Submodule.span ℝ
          (Set.range (fun q : {q : RB31E2E.Vec3 ℝ //
            MvPolynomial.eval q (polynomialMinor W b) ≠ 0} =>
              PolynomialImageSpan.evaluationVector (polynomialCofactorCoordinates W b) q.val)) :=
      Submodule.subset_span ⟨⟨p, hpPoly⟩, rfl⟩
    have hvalue := ha _ hmem
    rw [polynomialCoordinates_eq_equivFun] at hvalue
    obtain ⟨c, hc⟩ := cofactor_common_pin_map_is_eigenvector W b T hTfix p hp
    have hA : A (b.equivFun (cofactor W b p)) =
        c • b.equivFun (cofactor W b p) := by
      change b.equivFun (R (T (b.equivFun.symm (b.equivFun (cofactor W b p))))) = _
      rw [b.equivFun.symm_apply_apply, hc, map_smul, hRval, map_smul]
    rw [hA] at hvalue
    have hcoordNe : b.equivFun (cofactor W b p) ≠ 0 := by
      intro hz
      have hcZero : cofactor W b p = 0 := b.equivFun.injective (by simpa using hz)
      exact basisVector_ne_zero (restrictedEvaluation W p) b hp hcZero
    have hca : c = a := (smul_left_injective ℝ hcoordNe) hvalue
    rwa [hca] at hc
  refine ⟨a, ?_⟩
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨p, rfl⟩ := hX
    exact hfamily p.val p.property
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, smul_zero]
  | add X Y hX hY ihX ihY =>
    rw [map_add, ihX, ihY, AddSubmonoid.coe_add, smul_add]
  | smul c X hX ih =>
    rw [map_smul, ih, SetLike.val_smul, smul_comm]

/-- In the intended body application the second body has a nonzero
relative twist on the surviving flex, so the common scalar cannot be zero. -/
theorem cofactor_common_pin_map_nonzero_scalar
    (W : Submodule ℝ (RB31E2E.Twist ℝ)) (b : Module.Basis (Option (Fin 3)) ℝ W)
    (T : W →ₗ[ℝ] RB31E2E.Twist ℝ)
    (hwitness : ∃ p : RB31E2E.Vec3 ℝ, minor W b p ≠ 0 ∧ T (cofactor W b p) ≠ 0)
    (hTfix : ∀ p, minor W b p ≠ 0 → RB31E2E.Twist.eval (T (cofactor W b p)) p = 0) :
    ∃ a : ℝ, a ≠ 0 ∧ ∀ X ∈ cofactorImageSpan W b, T X = a • X.val := by
  obtain ⟨p, hp, hTp⟩ := hwitness
  obtain ⟨a, ha⟩ := cofactor_common_pin_map_scalar W b T ⟨p, hp⟩ hTfix
  refine ⟨a, ?_, ha⟩
  intro hz
  apply hTp
  rw [ha _ (cofactor_mem_imageSpan W b p hp), hz, zero_smul]

end

end Papers.Rigidity.CofactorKernel

end
end BundleSource0010

section BundleSource0011
/- Source: Papers/RigidityCofactorImage.lean -/





@[expose] public section

/-!
# The dimension and center of the actual cofactor image span

The common-pin family consists of nonzero stationary twists on a genuine
open determinant chart. Its actual linear span therefore has dimension
at least three. In a four-dimensional body image it either fills that
image or is one of the three-dimensional finite/infinite center spaces.
This replaces the projective image-closure dimension argument in the
last case of Proposition 4.1 by a direct statement about actual twists.

The image calculation concerns the original relative-twist maps.
-/

namespace Papers.Rigidity.CofactorKernel

noncomputable section

open Matrix
open scoped Matrix BigOperators

theorem vendor_eval_eq_evaluateTwist (X : RB31E2E.Twist ℝ) (p : RB31E2E.Vec3 ℝ) :
    RB31E2E.Twist.eval X p = evaluateTwist p X := by
  funext i
  fin_cases i <;> simp [RB31E2E.Twist.eval, RB31E2E.Vec3.cross,
    evaluateTwist_apply, cross_apply]

/-- A four-dimensional twist space has a genuinely surjective evaluation
at some real pin. Otherwise the already-derived singular-space
classification would force its dimension to be three. -/
theorem exists_surjective_evaluation_of_finrank_four (W : Submodule ℝ Twist)
    (hW : Module.finrank ℝ W = 4) :
    ∃ p : Vec3, Function.Surjective (restrictedEvaluation W p) := by
  have hlarge : ∃ p : Vec3, 3 ≤ Module.finrank ℝ (restrictEvaluation W p).range := by
    by_contra hn
    have hsingular : SingularPinSpace W := by
      intro p
      by_contra hp
      exact hn ⟨p, by omega⟩
    have hthree := finrank_eq_three_of_singularPinSpace W hsingular (by omega)
    omega
  obtain ⟨p, hp⟩ := hlarge
  have hrank : Module.finrank ℝ (restrictEvaluation W p).range =
      Module.finrank ℝ Vec3 := by
    have hupper := Submodule.finrank_le (restrictEvaluation W p).range
    have hdim : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
    omega
  have hsurj : Function.Surjective (restrictEvaluation W p) :=
    LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hrank)
  have hmaps : restrictedEvaluation W p = restrictEvaluation W p := by
    apply LinearMap.ext
    intro X
    exact vendor_eval_eq_evaluateTwist X.val p
  exact ⟨p, by simpa only [hmaps] using hsurj⟩

/-- The basis and its nonzero pivot chart are derived from the actual
four-dimensional image. No generic-pivot or basis-minor premise is
needed when applying the cofactor analysis to a rank-four body map. -/
theorem exists_basis_nonzero_minor (W : Submodule ℝ Twist)
    (hW : Module.finrank ℝ W = 4) :
    ∃ b : Module.Basis (Option (Fin 3)) ℝ W, ∃ p : Vec3, minor W b p ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := exists_surjective_evaluation_of_finrank_four W hW
  let L := restrictedEvaluation W p
  choose w hw using fun i : Fin 3 => hp (Pi.single i 1)
  change ∀ i : Fin 3, L (w i) = (Pi.single i 1 : Vec3) at hw
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := Vec3) L
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, hW] at hnull
  have hdim : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
  rw [hdim] at hnull
  change 3 + Module.finrank ℝ L.ker = 4 at hnull
  have hpositive : 0 < Module.finrank ℝ L.ker := by omega
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := L.ker)).mp hpositive
  have hvval : (v : W) ≠ 0 := fun hz => hv (Subtype.ext hz)
  have hLv : L (v : W) = 0 := v.property
  let f : Option (Fin 3) → W := fun i => i.elim (v : W) w
  have hli : LinearIndependent ℝ f := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have he := congrArg L hc
    have hcSome : ∀ i : Fin 3, c (some i) = 0 := by
      intro i
      have hei := congrFun he i
      simpa [f, Fintype.sum_option, map_sum, map_smul, hLv, hw, Pi.single_apply] using hei
    have hcNone : c none = 0 := by
      have hzero : c none • (v : W) = 0 := by
        simpa [f, Fintype.sum_option, hcSome] using hc
      exact (smul_eq_zero.mp hzero).resolve_right hvval
    cases j with
    | none => exact hcNone
    | some i => exact hcSome i
  have hcard : Fintype.card (Option (Fin 3)) = Module.finrank ℝ W := by
    rw [hW]
    simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb (i : Option (Fin 3)) : b i = f i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i
  have hpivot : pivotMatrix L (fun i => b (some i)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    change L (b (some j)) i = _
    rw [hb]
    change L (w j) i = _
    rw [hw]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  refine ⟨b, p, ?_⟩
  change (pivotMatrix L (fun i => b (some i))).det ≠ 0
  rw [hpivot, Matrix.det_one]
  exact one_ne_zero

def cofactorTwistImageSpan (W : Submodule ℝ Twist)
    (b : Module.Basis (Option (Fin 3)) ℝ W) : Submodule ℝ Twist :=
  (cofactorImageSpan W b).map W.subtype

theorem cofactorTwistImageSpan_le (W : Submodule ℝ Twist)
    (b : Module.Basis (Option (Fin 3)) ℝ W) : cofactorTwistImageSpan W b ≤ W :=
  Submodule.map_subtype_le W (cofactorImageSpan W b)

theorem cofactor_stationary_on_chart (W : Submodule ℝ Twist)
    (b : Module.Basis (Option (Fin 3)) ℝ W) (p : Vec3) (hp : minor W b p ≠ 0) :
    ∃ X : cofactorTwistImageSpan W b, X ≠ 0 ∧ evaluateTwist p X.val = 0 := by
  let X : cofactorTwistImageSpan W b :=
    ⟨(cofactor W b p).val, cofactor W b p, cofactor_mem_imageSpan W b p hp, rfl⟩
  refine ⟨X, ?_, ?_⟩
  · intro hz
    have hzval : (cofactor W b p).val = 0 := congrArg Subtype.val hz
    exact basisVector_ne_zero (restrictedEvaluation W p) b hp (Subtype.ext hzval)
  · rw [← vendor_eval_eq_evaluateTwist]
    exact apply_vector_eq_zero (restrictedEvaluation W p)
      (fun i => b (some i)) (b none)

theorem cofactorTwistImageSpan_finrank_bounds (W : Submodule ℝ Twist)
    (b : Module.Basis (Option (Fin 3)) ℝ W)
    (hwitness : ∃ p : Vec3, minor W b p ≠ 0) :
    3 ≤ Module.finrank ℝ (cofactorTwistImageSpan W b) ∧
      Module.finrank ℝ (cofactorTwistImageSpan W b) ≤ 4 := by
  have hopen : IsOpen {p : Vec3 | minor W b p ≠ 0} :=
    isOpen_ne_fun (minor_continuous W b) continuous_const
  have hnonempty : ({p : Vec3 | minor W b p ≠ 0} : Set Vec3).Nonempty := hwitness
  have hlower := CommonPinLowRank.three_le_finrank_of_stationary_family_on_open
    (cofactorTwistImageSpan W b) _ hopen hnonempty (cofactor_stationary_on_chart W b)
  have hW : Module.finrank ℝ W = 4 := by
    rw [Module.finrank_eq_card_basis b]
    simp
  exact ⟨hlower, (Submodule.finrank_mono (cofactorTwistImageSpan_le W b)).trans hW.le⟩

/-- The complete span dichotomy required in the four-dimensional
common-pin argument, expressed in the original Euclidean twist space. -/
theorem cofactorTwistImageSpan_classification (W : Submodule ℝ Twist)
    (b : Module.Basis (Option (Fin 3)) ℝ W)
    (hwitness : ∃ p : Vec3, minor W b p ≠ 0) :
    cofactorTwistImageSpan W b = W ∨
      (∃! a : Vec3, cofactorTwistImageSpan W b = finiteCenterSpace a) ∨
        ∃ d : Vec3, d ≠ 0 ∧ cofactorTwistImageSpan W b = infiniteCenterSpace d := by
  have hbounds := cofactorTwistImageSpan_finrank_bounds W b hwitness
  by_cases hfour : Module.finrank ℝ (cofactorTwistImageSpan W b) = 4
  · left
    apply Submodule.eq_of_le_of_finrank_eq (cofactorTwistImageSpan_le W b)
    rw [hfour, Module.finrank_eq_card_basis b]
    simp
  · right
    have hthree : Module.finrank ℝ (cofactorTwistImageSpan W b) = 3 := by omega
    have hopen : IsOpen {p : Vec3 | minor W b p ≠ 0} :=
      isOpen_ne_fun (minor_continuous W b) continuous_const
    have hsingular := CommonPinLowRank.singularPinSpace_of_stationary_family_on_open
      (cofactorTwistImageSpan W b) hthree _ hopen hwitness
        (cofactor_stationary_on_chart W b)
    exact singularPinSpace_classification _ hsingular hbounds.1

end

end Papers.Rigidity.CofactorKernel

end
end BundleSource0011

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0011/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0011.json"

section BundleSource0012
/- Source: Papers/RigidityCofactorCoupled.lean -/



@[expose] public section

/-!
# From the actual joint-pin rank to the common cofactor family

The common-pin identity used by the cofactor argument is derived here
from the rank of the two bodies' actual combined evaluation operator.
A rank bound on any nonempty open pin set extends to every real pin by
the already-proved affine-matrix rank density theorem.

This module connects the cofactor calculations to Proposition 4.1.
-/

namespace Papers.Rigidity.CofactorKernel

noncomputable section

def jointPinOperator (W : Submodule ℝ Twist) (T : W →ₗ[ℝ] Twist) (p : Vec3) :
    W →ₗ[ℝ] (Vec3 × Vec3) :=
  (restrictEvaluation W p).prod ((evaluateTwist p).comp T)

def jointPinLinearPart (W : Submodule ℝ Twist) (T : W →ₗ[ℝ] Twist) :
    Vec3 →ₗ[ℝ] (W →ₗ[ℝ] (Vec3 × Vec3)) where
  toFun p := ((CommonPinLowRank.pointEvaluation p).comp W.subtype).prod
    ((CommonPinLowRank.pointEvaluation p).comp T)
  map_add' p q := by
    apply LinearMap.ext
    intro X
    apply Prod.ext <;> funext i <;> simp
  map_smul' a p := by
    apply LinearMap.ext
    intro X
    apply Prod.ext <;> funext i <;> simp

theorem jointPinOperator_eq_family (W : Submodule ℝ Twist)
    (T : W →ₗ[ℝ] Twist) (p : Vec3) :
    jointPinOperator W T p =
      AffineRank.family (jointPinOperator W T 0) (jointPinLinearPart W T) p := by
  apply LinearMap.ext
  intro X
  apply Prod.ext <;>
    simp [jointPinOperator, jointPinLinearPart, AffineRank.family,
      restrictEvaluation, evaluateTwist_apply]

/-- The joint-pin rank condition is a genuine generic condition: if it
holds on one nonempty real open set, it holds at every real pin. -/
theorem jointPin_rank_le_three_of_open (W : Submodule ℝ Twist)
    (T : W →ₗ[ℝ] Twist) (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hbound : ∀ p ∈ O, Module.finrank ℝ (jointPinOperator W T p).range ≤ 3) :
    ∀ p : Vec3, Module.finrank ℝ (jointPinOperator W T p).range ≤ 3 := by
  intro p
  by_contra hp
  have hlarge : 4 ≤ Module.finrank ℝ (jointPinOperator W T p).range := by omega
  have hdense := AffineRank.dense_setOf_le_rankAt
    (jointPinOperator W T 0) (jointPinLinearPart W T) 4
      ⟨p, by
        unfold AffineRank.rankAt
        rw [← jointPinOperator_eq_family W T p]
        exact hlarge⟩
  obtain ⟨q, hq, hqO⟩ := hdense.exists_mem_open hO hne
  have hqLarge : 4 ≤ Module.finrank ℝ (jointPinOperator W T q).range := by
    change 4 ≤ Module.finrank ℝ
      (AffineRank.family (jointPinOperator W T 0) (jointPinLinearPart W T) q).range at hq
    rwa [← jointPinOperator_eq_family W T q] at hq
  have hqSmall := hbound q hqO
  omega

/-- Once the first evaluation is onto, a combined operator of rank at
most three has precisely the same kernel as its first component. -/
theorem jointPin_ker_eq_first_of_rank_le_three (W : Submodule ℝ Twist)
    (T : W →ₗ[ℝ] Twist) (p : Vec3)
    (hsurj : Function.Surjective (restrictEvaluation W p))
    (hrank : Module.finrank ℝ (jointPinOperator W T p).range ≤ 3) :
    (jointPinOperator W T p).ker = (restrictEvaluation W p).ker := by
  have hle : (jointPinOperator W T p).ker ≤ (restrictEvaluation W p).ker := by
    intro X hX
    exact congrArg Prod.fst (show jointPinOperator W T p X = 0 from hX)
  have hfirst : Module.finrank ℝ (restrictEvaluation W p).range = 3 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp [Vec3]
  have hfirstNull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := Vec3) (restrictEvaluation W p)
  have hjointNull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := Vec3 × Vec3) (jointPinOperator W T p)
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

/-- The stationary Cramer twist of the first body also fixes the pin
in the second body. This is derived from the actual joint rank and is
not an additional common-kernel assumption. -/
theorem cofactor_second_stationary_of_joint_rank
    (W : Submodule ℝ Twist) (b : Module.Basis (Option (Fin 3)) ℝ W)
    (T : W →ₗ[ℝ] Twist) (p : Vec3) (hp : minor W b p ≠ 0)
    (hrank : Module.finrank ℝ (jointPinOperator W T p).range ≤ 3) :
    RB31E2E.Twist.eval (T (cofactor W b p)) p = 0 := by
  have hmaps : restrictedEvaluation W p = restrictEvaluation W p := by
    apply LinearMap.ext
    intro X
    exact vendor_eval_eq_evaluateTwist X.val p
  have hsurj : Function.Surjective (restrictEvaluation W p) := by
    rw [← hmaps]
    exact surjective_of_pivot_det_ne_zero (restrictedEvaluation W p)
      (fun i => b (some i)) hp
  have hker := jointPin_ker_eq_first_of_rank_le_three W T p hsurj hrank
  have hfirst : cofactor W b p ∈ (restrictEvaluation W p).ker := by
    rw [← hmaps]
    exact apply_vector_eq_zero (restrictedEvaluation W p)
      (fun i => b (some i)) (b none)
  have hjoint : jointPinOperator W T p (cofactor W b p) = 0 := by
    change cofactor W b p ∈ (jointPinOperator W T p).ker
    rwa [hker]
  rw [vendor_eval_eq_evaluateTwist]
  exact congrArg Prod.snd hjoint

/-- The rank-four algebraic branch of the deletion argument, with the
basis, the nonzero chart, the common stationary family and its actual
span all constructed. Its remaining use is the differential obstruction
for actual body motions, proved in the separate calculus modules. -/
theorem rankFour_jointPin_scalar_span
    (W : Submodule ℝ Twist) (hW : Module.finrank ℝ W = 4)
    (T : W →ₗ[ℝ] Twist) (hT : Function.Injective T)
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hbound : ∀ p ∈ O, Module.finrank ℝ (jointPinOperator W T p).range ≤ 3) :
    ∃ (b : Module.Basis (Option (Fin 3)) ℝ W) (a : ℝ), a ≠ 0 ∧
      (∀ X ∈ cofactorImageSpan W b, T X = a • X.val) ∧
      (cofactorTwistImageSpan W b = W ∨
        (∃! c : Vec3, cofactorTwistImageSpan W b = finiteCenterSpace c) ∨
          ∃ d : Vec3, d ≠ 0 ∧ cofactorTwistImageSpan W b = infiniteCenterSpace d) := by
  obtain ⟨b, p, hp⟩ := exists_basis_nonzero_minor W hW
  have hrank := jointPin_rank_le_three_of_open W T O hO hne hbound
  have hTfix : ∀ q, minor W b q ≠ 0 →
      RB31E2E.Twist.eval (T (cofactor W b q)) q = 0 := by
    intro q hq
    exact cofactor_second_stationary_of_joint_rank W b T q hq (hrank q)
  have hTp : T (cofactor W b p) ≠ 0 := by
    intro hz
    have hc : cofactor W b p = 0 := hT (by simpa only [map_zero] using hz)
    exact basisVector_ne_zero (restrictedEvaluation W p) b hp hc
  obtain ⟨a, ha, hscalar⟩ := cofactor_common_pin_map_nonzero_scalar W b T ⟨p, hp, hTp⟩ hTfix
  exact ⟨b, a, ha, hscalar, cofactorTwistImageSpan_classification W b ⟨p, hp⟩⟩

end

end Papers.Rigidity.CofactorKernel

end
end BundleSource0012

section BundleSource0013
/- Source: Papers/RigidityCofactorBodyForms.lean -/



@[expose] public section

/-!
# The cofactor conclusion in a fixed configuration tangent space

The algebraic common-pin result is transported through the injective
first-body map to the original four-dimensional tangent space. The
cofactor is the literal Cramer vector in one fixed tangent basis, so it
can subsequently be differentiated as the configuration varies.

The rank-one discrepancy and the center contained in its actual kernel
image are conclusions, not replacement hypotheses for the common-pin
rank bound. These body forms support Proposition 4.1.
-/

namespace Papers.Rigidity.CofactorKernel

noncomputable section

open scoped BigOperators

theorem basisVector_map
    {k M N ι : Type*} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [Fintype ι] [DecidableEq ι]
    (L : N →ₗ[k] (ι → k)) (e : M ≃ₗ[k] N)
    (b : Module.Basis (Option ι) k M) :
    basisVector L (b.map e) = e (basisVector (L.comp e.toLinearMap) b) := by
  simp [basisVector, vector, pivotMatrix, Module.Basis.map_apply,
    map_sub, map_smul, map_sum]
  rfl

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def bodyEvaluation (A : E →ₗ[ℝ] Twist) (p : Vec3) : E →ₗ[ℝ] Vec3 :=
  (evaluation p).comp A

def bodyMinor (A : E →ₗ[ℝ] Twist) (b : Module.Basis (Option (Fin 3)) ℝ E)
    (p : Vec3) : ℝ :=
  (pivotMatrix (bodyEvaluation A p) (fun i => b (some i))).det

def bodyCofactor (A : E →ₗ[ℝ] Twist) (b : Module.Basis (Option (Fin 3)) ℝ E)
    (p : Vec3) : E := basisVector (bodyEvaluation A p) b

def bodyJointPin (A B : E →ₗ[ℝ] Twist) (p : Vec3) : E →ₗ[ℝ] (Vec3 × Vec3) :=
  ((evaluateTwist p).comp A).prod ((evaluateTwist p).comp B)

theorem bodyMinor_rangeBasis (A : E →ₗ[ℝ] Twist) (hA : Function.Injective A)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p : Vec3) :
    minor A.range (b.map (LinearEquiv.ofInjective A hA)) p = bodyMinor A b p := rfl

theorem bodyCofactor_rangeBasis (A : E →ₗ[ℝ] Twist) (hA : Function.Injective A)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p : Vec3) :
    cofactor A.range (b.map (LinearEquiv.ofInjective A hA)) p =
      LinearEquiv.ofInjective A hA (bodyCofactor A b p) := by
  exact basisVector_map (restrictedEvaluation A.range p) (LinearEquiv.ofInjective A hA) b

/-- A regular pin supplies its own nonzero Cramer chart. In particular,
the final body-form conclusion need not assume a specially chosen basis. -/
theorem exists_bodyBasis_nonzero_minor_at [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4) (p : Vec3)
    (hsurj : Function.Surjective ((evaluateTwist p).comp A)) :
    ∃ b : Module.Basis (Option (Fin 3)) ℝ E, bodyMinor A b p ≠ 0 := by
  classical
  let L := bodyEvaluation A p
  have hL : Function.Surjective L := by
    intro v
    obtain ⟨u, hu⟩ := hsurj v
    refine ⟨u, ?_⟩
    change RB31E2E.Twist.eval (A u) p = v
    rw [vendor_eval_eq_evaluateTwist]
    exact hu
  choose w hw using fun i : Fin 3 => hL (Pi.single i 1)
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := E) (V₂ := Vec3) L
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, hdim] at hnull
  have hdimV : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
  rw [hdimV] at hnull
  change 3 + Module.finrank ℝ L.ker = 4 at hnull
  have hpositive : 0 < Module.finrank ℝ L.ker := by omega
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := L.ker)).mp hpositive
  have hvval : (v : E) ≠ 0 := fun hz => hv (Subtype.ext hz)
  have hLv : L (v : E) = 0 := v.property
  let f : Option (Fin 3) → E := fun i => i.elim (v : E) w
  have hli : LinearIndependent ℝ f := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have he := congrArg L hc
    have hcSome : ∀ i : Fin 3, c (some i) = 0 := by
      intro i
      have hei := congrFun he i
      simpa [f, Fintype.sum_option, map_sum, map_smul, hLv, hw, Pi.single_apply] using hei
    have hcNone : c none = 0 := by
      have hz : c none • (v : E) = 0 := by
        simpa [f, Fintype.sum_option, hcSome] using hc
      exact (smul_eq_zero.mp hz).resolve_right hvval
    cases j with
    | none => exact hcNone
    | some i => exact hcSome i
  have hcard : Fintype.card (Option (Fin 3)) = Module.finrank ℝ E := by
    rw [hdim]
    simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb (i : Option (Fin 3)) : b i = f i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i
  have hpivot : pivotMatrix L (fun i => b (some i)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    change L (b (some j)) i = _
    rw [hb]
    change L (w j) i = _
    rw [hw]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  refine ⟨b, ?_⟩
  change (pivotMatrix L (fun i => b (some i))).det ≠ 0
  rw [hpivot, Matrix.det_one]
  exact one_ne_zero

/-- For one fixed tangent basis with a nonzero pivot, the actual coupled
pin rank supplies a nonzero scalar, a discrepancy of rank at most one,
and a center space in its kernel whenever that discrepancy is nonzero. -/
theorem bodyForms_scalar_discrepancy_of_nonzero [FiniteDimensional ℝ E]
    (A B : E →ₗ[ℝ] Twist) (hA : Function.Injective A)
    (b : Module.Basis (Option (Fin 3)) ℝ E)
    (p₀ : Vec3) (hp₀ : bodyMinor A b p₀ ≠ 0)
    (hB : B (bodyCofactor A b p₀) ≠ 0)
    (hrank : ∀ p : Vec3, Module.finrank ℝ (bodyJointPin A B p).range ≤ 3) :
    ∃ a : ℝ, a ≠ 0 ∧
      (∀ p, bodyMinor A b p ≠ 0 → B (bodyCofactor A b p) = a • A (bodyCofactor A b p)) ∧
      Module.finrank ℝ (B - a • A).range ≤ 1 ∧
      (B - a • A ≠ 0 →
        (∃ c : Vec3, finiteCenterSpace c ≤ (B - a • A).ker.map A) ∨
        (∃ d : Vec3, d ≠ 0 ∧ infiniteCenterSpace d ≤ (B - a • A).ker.map A)) := by
  let W := A.range
  let e : E ≃ₗ[ℝ] W := LinearEquiv.ofInjective A hA
  let bW := b.map e
  let T : W →ₗ[ℝ] Twist := B.comp e.symm.toLinearMap
  have heval (u : E) : (e u).val = A u := rfl
  have heinv (X : W) : A (e.symm X) = X.val :=
    congrArg Subtype.val (e.apply_symm_apply X)
  have hminor (p : Vec3) : minor W bW p = bodyMinor A b p := rfl
  have hcofactor (p : Vec3) : cofactor W bW p = e (bodyCofactor A b p) :=
    bodyCofactor_rangeBasis A hA b p
  have hjoint (p : Vec3) :
      (jointPinOperator W T p).comp e.toLinearMap = bodyJointPin A B p := by
    apply LinearMap.ext
    intro u
    apply Prod.ext
    · rfl
    · change evaluateTwist p (B (e.symm (e u))) = evaluateTwist p (B u)
      rw [e.symm_apply_apply]
  have hrankW (p : Vec3) : Module.finrank ℝ (jointPinOperator W T p).range ≤ 3 := by
    rw [← LinearMap.range_comp_of_range_eq_top (jointPinOperator W T p) e.range,
      hjoint]
    exact hrank p
  have hTfix : ∀ p, minor W bW p ≠ 0 →
      RB31E2E.Twist.eval (T (cofactor W bW p)) p = 0 := by
    intro p hp
    exact cofactor_second_stationary_of_joint_rank W bW T p hp (hrankW p)
  have hpW : minor W bW p₀ ≠ 0 := by rwa [hminor]
  have hTne : T (cofactor W bW p₀) ≠ 0 := by
    intro hz
    apply hB
    rw [hcofactor] at hz
    change B (e.symm (e (bodyCofactor A b p₀))) = 0 at hz
    simpa only [e.symm_apply_apply] using hz
  obtain ⟨a, ha, hscalar⟩ := cofactor_common_pin_map_nonzero_scalar W bW T
    ⟨p₀, hpW, hTne⟩ hTfix
  let H := cofactorTwistImageSpan W bW
  let D : E →ₗ[ℝ] Twist := B - a • A
  have hHkernel : H ≤ D.ker.map A := by
    rintro X ⟨Y, hY, rfl⟩
    refine ⟨e.symm Y, ?_, heinv Y⟩
    change B (e.symm Y) - a • A (e.symm Y) = 0
    rw [heinv]
    change T Y - a • Y.val = 0
    rw [hscalar Y hY, sub_self]
  have hdimE : Module.finrank ℝ E = 4 := by
    rw [Module.finrank_eq_card_basis b]
    simp
  have hdimKernelImage : Module.finrank ℝ (D.ker.map A) = Module.finrank ℝ D.ker :=
    (Submodule.equivMapOfInjective A hA D.ker).finrank_eq.symm
  have hdimH : 3 ≤ Module.finrank ℝ H :=
    (cofactorTwistImageSpan_finrank_bounds W bW ⟨p₀, hpW⟩).1
  have hdimKernel := Submodule.finrank_mono hHkernel
  rw [hdimKernelImage] at hdimKernel
  have hrankD : Module.finrank ℝ D.range ≤ 1 := by
    have hnull := D.finrank_range_add_finrank_ker
    rw [hdimE] at hnull
    omega
  refine ⟨a, ha, ?_, hrankD, ?_⟩
  · intro p hp
    have h := hscalar (cofactor W bW p)
      (cofactor_mem_imageSpan W bW p (by rwa [hminor]))
    rw [hcofactor] at h
    change B (e.symm (e (bodyCofactor A b p))) = a • (e (bodyCofactor A b p)).val at h
    simpa only [e.symm_apply_apply, heval] using h
  · intro hD
    rcases cofactorTwistImageSpan_classification W bW ⟨p₀, hpW⟩ with hfull | hfinite | hinfinite
    · exfalso
      apply hD
      apply LinearMap.ext
      intro u
      have huH : A u ∈ H := by
        change A u ∈ cofactorTwistImageSpan W bW
        rw [hfull]
        exact ⟨u, rfl⟩
      obtain ⟨v, hv, hva⟩ := hHkernel huH
      have hvu : v = u := hA hva
      change D u = 0
      exact (congrArg D hvu).symm.trans (LinearMap.mem_ker.mp hv)
    · obtain ⟨c, hc, _⟩ := hfinite
      exact Or.inl ⟨c, by rw [← hc]; exact hHkernel⟩
    · obtain ⟨d, hd, hdc⟩ := hinfinite
      exact Or.inr ⟨d, hd, by rw [← hdc]; exact hHkernel⟩

/-- The rank-four/rank-four case is a direct specialization. -/
theorem bodyForms_scalar_discrepancy [FiniteDimensional ℝ E]
    (A B : E →ₗ[ℝ] Twist) (hA : Function.Injective A) (hB : Function.Injective B)
    (b : Module.Basis (Option (Fin 3)) ℝ E)
    (hwitness : ∃ p : Vec3, bodyMinor A b p ≠ 0)
    (hrank : ∀ p : Vec3, Module.finrank ℝ (bodyJointPin A B p).range ≤ 3) :
    ∃ a : ℝ, a ≠ 0 ∧
      (∀ p, bodyMinor A b p ≠ 0 → B (bodyCofactor A b p) = a • A (bodyCofactor A b p)) ∧
      Module.finrank ℝ (B - a • A).range ≤ 1 ∧
      (B - a • A ≠ 0 →
        (∃ c : Vec3, finiteCenterSpace c ≤ (B - a • A).ker.map A) ∨
        (∃ d : Vec3, d ≠ 0 ∧ infiniteCenterSpace d ≤ (B - a • A).ker.map A)) := by
  obtain ⟨p₀, hp₀⟩ := hwitness
  have hBvalue : B (bodyCofactor A b p₀) ≠ 0 := by
    intro hz
    have hc : bodyCofactor A b p₀ = 0 := hB (by simpa only [map_zero] using hz)
    exact basisVector_ne_zero (bodyEvaluation A p₀) b hp₀ hc
  exact bodyForms_scalar_discrepancy_of_nonzero A B hA b p₀ hp₀ hBvalue hrank

end

end Papers.Rigidity.CofactorKernel

end
end BundleSource0013

section BundleSource0014
/- Source: Papers/RigidityFixedCenterDifferential.lean -/




@[expose] public section

/-!
# Differentiating the fixed-center relation

This is the calculus step of Lemma 4.2 in an ordinary smooth coordinate
chart. It starts from actual functions for the body's rotation,
translation and moving center; differentiating the relation is proved,
not postulated. The final angular identification is stated explicitly.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter
open scoped Topology Matrix

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_apply_constant (D : E → (E →L[ℝ] F)) (x : E)
    (hD : DifferentiableAt ℝ D x) (u z : E) :
    fderiv ℝ (fun y => D y u) x z = fderiv ℝ D x z u := by
  rw [fderiv_clm_apply hD (differentiableAt_const u)]
  simp

/-- Equality of mixed second derivatives supplies the wedge relation
`dR ∧ db = 0` from `dt = -dR b`. -/
theorem fixed_center_mixed_relation
    (R : E → (F →L[ℝ] F)) (t b : E → F) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x)
    (hb : DifferentiableAt ℝ b x)
    (hfix : ∀ᶠ y in 𝓝 x, ∀ u : E,
      fderiv ℝ t y u = -(fderiv ℝ R y u) (b y)) (v w : E) :
    (fderiv ℝ R x v) (fderiv ℝ b x w) =
      (fderiv ℝ R x w) (fderiv ℝ b x v) := by
  have hDR : DifferentiableAt ℝ (fderiv ℝ R) x :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hDt : DifferentiableAt ℝ (fderiv ℝ t) x :=
    (ht.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hRpart (u : E) : DifferentiableAt ℝ (fun y => fderiv ℝ R y u) x :=
    hDR.clm_apply (differentiableAt_const u)
  have heq (u z : E) :
      fderiv ℝ (fderiv ℝ t) x z u =
        -((fderiv ℝ R x u) (fderiv ℝ b x z) +
          (fderiv ℝ (fderiv ℝ R) x z u) (b x)) := by
    have he : (fun y => fderiv ℝ t y u) =ᶠ[𝓝 x]
        (fun y => -(fderiv ℝ R y u) (b y)) :=
      hfix.mono fun y hy => hy u
    have h := congrArg (fun D : E →L[ℝ] F => D z) (he.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_apply_constant (fderiv ℝ t) x hDt,
      fderiv_fun_neg, fderiv_clm_apply (hRpart u) hb] at h
    simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      fderiv_apply_constant (fderiv ℝ R) x hDR] using h
  have hvw := heq v w
  have hwv := heq w v
  have hsR := hR.isSymmSndFDerivAt (by norm_num)
  have hst := ht.isSymmSndFDerivAt (by norm_num)
  rw [hst w v, hsR w v] at hvw
  have hsum := neg_injective (hvw.symm.trans hwv)
  exact add_right_cancel hsum

/-- If angular coordinates cover all three rotations, the actual body-frame
center derivative vanishes. The inverse rotation is represented by `A`,
and `e` is the invertible angular-coordinate map of the chart. -/
theorem fixed_body_center_derivative_eq_zero
    (R : E → (Vec3 →L[ℝ] Vec3)) (t b : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x)
    (hb : DifferentiableAt ℝ b x)
    (hfix : ∀ᶠ y in 𝓝 x, ∀ u : E,
      fderiv ℝ t y u = -(fderiv ℝ R y u) (b y))
    (A : Vec3 →ₗ[ℝ] Vec3) (e : E ≃ₗ[ℝ] Vec3)
    (hangular : ∀ v q, A ((fderiv ℝ R x v) q) = e v ⨯₃ q) :
    fderiv ℝ b x = 0 := by
  let D : Vec3 →ₗ[ℝ] Vec3 :=
    (fderiv ℝ b x).toLinearMap.comp e.symm.toLinearMap
  have hD : D = 0 := by
    apply linearMap_eq_zero_of_cross_integrability
    intro u v
    have hm := congrArg A (fixed_center_mixed_relation R t b x hR ht hb hfix
      (e.symm u) (e.symm v))
    change u ⨯₃ ((fderiv ℝ b x) (e.symm v)) =
      v ⨯₃ ((fderiv ℝ b x) (e.symm u))
    simpa only [hangular, LinearEquiv.apply_symm_apply] using hm
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun D : Vec3 →ₗ[ℝ] Vec3 => D (e v)) hD
  simpa [D] using h

/-- The spatial point `a = R b + t` has zero derivative as well. -/
theorem fixed_spatial_center_derivative_eq_zero
    (R : E → (Vec3 →L[ℝ] Vec3)) (t b : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x)
    (hb : DifferentiableAt ℝ b x)
    (hfix : ∀ᶠ y in 𝓝 x, ∀ u : E,
      fderiv ℝ t y u = -(fderiv ℝ R y u) (b y))
    (A : Vec3 →ₗ[ℝ] Vec3) (e : E ≃ₗ[ℝ] Vec3)
    (hangular : ∀ v q, A ((fderiv ℝ R x v) q) = e v ⨯₃ q) :
    fderiv ℝ (fun y => R y (b y) + t y) x = 0 := by
  have hRdiff := hR.differentiableAt (by norm_num)
  have htdiff := ht.differentiableAt (by norm_num)
  have hdb := fixed_body_center_derivative_eq_zero R t b x hR ht hb hfix A e hangular
  have hfixx := hfix.self_of_nhds
  rw [fderiv_fun_add (hRdiff.clm_apply hb) htdiff,
    fderiv_clm_apply hRdiff hb, hdb]
  ext v
  simp [hfixx]

end Papers.Rigidity.Calculus

end
end
end BundleSource0014

section BundleSource0015
/- Source: Papers/RigidityLieAlgebra.lean -/




@[expose] public section

/-!
# The Lie algebra obstruction used in Lemma 4.4

This file works with the actual bracket of spatial Euclidean twists. The
separate differential-geometric step deriving this identity from two smooth
body maps is not built into the definitions.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

def translationSpace : Submodule ℝ Twist :=
  (LinearMap.fst ℝ Vec3 Vec3).ker

def translationInclusion : Vec3 →ₗ[ℝ] Twist :=
  (0 : Vec3 →ₗ[ℝ] Vec3).prod (LinearMap.id : Vec3 →ₗ[ℝ] Vec3)

@[simp] theorem translationInclusion_apply (v : Vec3) :
    translationInclusion v = (0, v) := rfl

theorem translationInclusion_range : translationInclusion.range = translationSpace := by
  ext X
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · intro hX
    refine ⟨X.2, ?_⟩
    exact Prod.ext hX.symm rfl

theorem finrank_translationSpace : Module.finrank ℝ translationSpace = 3 := by
  have hi : Function.Injective translationInclusion := by
    intro x y h
    exact congrArg Prod.snd h
  have he := LinearMap.finrank_range_of_inj hi
  rw [translationInclusion_range] at he
  simpa [Vec3] using he

/-- In an abelian twist subspace with a nonzero rotation, the translational
kernel can only translate along its axis; hence the subspace has dimension at
most two. -/
theorem abelian_twist_finrank_le_two_of_rotation
    (W : Submodule ℝ Twist)
    (hcomm : ∀ X Y : W, twistBracket X.val Y.val = 0)
    (X : W) (hX : X.val.1 ≠ 0) : Module.finrank ℝ W ≤ 2 := by
  let A := angularProjection W
  have har : A.range ≤ Submodule.span ℝ {X.val.1} := by
    rintro v ⟨Y, rfl⟩
    rw [← ker_crossProduct_eq_span X.val.1 hX]
    exact congrArg Prod.fst (hcomm X Y)
  have harank : Module.finrank ℝ A.range ≤ 1 := by
    have h := Submodule.finrank_mono har
    rwa [finrank_span_singleton hX] at h
  let K := A.ker
  let T : K →ₗ[ℝ] Vec3 :=
    (LinearMap.snd ℝ Vec3 Vec3).comp (W.subtype.comp K.subtype)
  have hzero (Y : K) : Y.val.val.1 = 0 := Y.property
  have hi : Function.Injective T := by
    intro Y Z he
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((hzero Y).trans (hzero Z).symm) he
  have htr : T.range ≤ Submodule.span ℝ {X.val.1} := by
    rintro v ⟨Y, rfl⟩
    rw [← ker_crossProduct_eq_span X.val.1 hX]
    have h := congrArg Prod.snd (hcomm X Y.val)
    change X.val.1 ⨯₃ Y.val.val.2 = 0
    simpa [twistBracket, hzero Y] using h
  have hkrank : Module.finrank ℝ K ≤ 1 := by
    have ht := Submodule.finrank_mono htr
    rw [finrank_span_singleton hX, LinearMap.finrank_range_of_inj hi] at ht
    exact ht
  have hr := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := Vec3) A
  change Module.finrank ℝ A.ker ≤ 1 at hkrank
  omega

/-- The only three-dimensional abelian twist space is the translation space. -/
theorem abelian_twist_eq_translationSpace
    (W : Submodule ℝ Twist)
    (hcomm : ∀ X Y : W, twistBracket X.val Y.val = 0)
    (hdim : 3 ≤ Module.finrank ℝ W) : W = translationSpace := by
  have hangular (X : W) : X.val.1 = 0 := by
    by_contra hn
    have hsmall := abelian_twist_finrank_le_two_of_rotation W hcomm X hn
    omega
  have hle : W ≤ translationSpace := by
    intro X hX
    exact hangular ⟨X, hX⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hu := Submodule.finrank_mono hle
  rw [finrank_translationSpace] at hu ⊢
  omega

theorem abelian_twist_finrank_le_three
    (W : Submodule ℝ Twist)
    (hcomm : ∀ X Y : W, twistBracket X.val Y.val = 0) :
    Module.finrank ℝ W ≤ 3 := by
  by_cases hsmall : Module.finrank ℝ W < 3
  · omega
  · have he := abelian_twist_eq_translationSpace W hcomm (by omega)
    rw [he, finrank_translationSpace]

/-- There is no four-dimensional Euclidean twist space with the bracket
identity that unequal proportional Maurer--Cartan forms would force. -/
theorem no_four_dimensional_scalar_bracket
    (W : Submodule ℝ Twist) (hdim : 4 ≤ Module.finrank ℝ W)
    (α : W →ₗ[ℝ] ℝ)
    (hbracket : ∀ X Y : W,
      twistBracket X.val Y.val = α X • Y.val - α Y • X.val) : False := by
  classical
  let K := α.ker
  let U : Submodule ℝ Twist := K.map W.subtype
  have hUdim : 3 ≤ Module.finrank ℝ U := by
    have hrange : Module.finrank ℝ α.range ≤ 1 := by
      simpa using Submodule.finrank_le α.range
    have hr := α.finrank_range_add_finrank_ker
    have hi : Function.Injective (W.subtype.comp K.subtype) :=
      W.subtype_injective.comp K.subtype_injective
    have hmap : U = (W.subtype.comp K.subtype).range := by
      simp [U, LinearMap.range_comp]
    rw [hmap, LinearMap.finrank_range_of_inj hi]
    change 3 ≤ Module.finrank ℝ α.ker
    omega
  have hUcomm : ∀ X Y : U, twistBracket X.val Y.val = 0 := by
    intro X Y
    obtain ⟨x, hx, hxe⟩ := X.property
    obtain ⟨y, hy, hye⟩ := Y.property
    rw [← hxe, ← hye]
    change twistBracket x.val y.val = 0
    rw [hbracket x y]
    have hαx : α x = 0 := hx
    have hαy : α y = 0 := hy
    simp [hαx, hαy]
  have hU : U = translationSpace := abelian_twist_eq_translationSpace U hUcomm hUdim
  have hαne : α ≠ 0 := by
    intro he
    have hcomm : ∀ X Y : W, twistBracket X.val Y.val = 0 := by
      intro X Y
      simpa [he] using hbracket X Y
    have hb := abelian_twist_finrank_le_three W hcomm
    omega
  obtain ⟨X, hX⟩ : ∃ X : W, α X ≠ 0 := by
    by_contra hn
    have hz : ∀ X : W, α X = 0 := by simpa only [not_exists, not_not] using hn
    exact hαne (LinearMap.ext hz)
  have htrans (t : Vec3) : ∃ Y : W, α Y = 0 ∧ Y.val = (0, t) := by
    have ht : ((0 : Vec3), t) ∈ U := by
      rw [hU]
      rfl
    obtain ⟨Y, hY, he⟩ := ht
    exact ⟨Y, hY, he⟩
  have hcross (t : Vec3) : X.val.1 ⨯₃ t = α X • t := by
    obtain ⟨Y, hY, he⟩ := htrans t
    have hb := congrArg Prod.snd (hbracket X Y)
    simpa [twistBracket, he, hY] using hb
  have hangular : X.val.1 = 0 := by
    have h := hcross X.val.1
    rw [cross_self] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hX
  have h := hcross ![1, 0, 0]
  rw [hangular] at h
  have h0 := congrFun h 0
  simp at h0
  exact hX h0.symm

end Papers.Rigidity

end
end BundleSource0015

section BundleSource0016
/- Source: Papers/RigidityProportionalDifferential.lean -/





@[expose] public section

/-!
# Differentiating proportional actual body-motion forms

The derivative of the proportionality factor is retained.  The
Maurer--Cartan equations are obtained from the actual matrix
representations, rather than supplied as a separate integrability
assumption.  In dimension at least four, immersion and a nonzero scalar
proportionality force that scalar to equal one.
-/

namespace Papers.Rigidity.Calculus

noncomputable section

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_proportional_forms
    (θ₁ θ₂ : E → (E →L[ℝ] F)) (lam : E → ℝ) (x : E)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hlam : DifferentiableAt ℝ lam x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u, θ₂ y u = lam y • θ₁ y u) (u z : E) :
    fderiv ℝ (fun y => θ₂ y u) x z =
      lam x • fderiv ℝ (fun y => θ₁ y u) x z + fderiv ℝ lam x z • θ₁ x u := by
  have hpart : DifferentiableAt ℝ (fun y => θ₁ y u) x :=
    hθ₁.clm_apply (differentiableAt_const u)
  have he : (fun y => θ₂ y u) =ᶠ[𝓝 x] (fun y => lam y • θ₁ y u) :=
    hrel.mono fun y hy => hy u
  have h := congrArg (fun D : E →L[ℝ] F => D z) (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_fun_smul hlam hpart] at h
  exact h

/-- The actual scalar-bracket identity obtained by differentiating
proportional body forms, including the derivative of the scalar. -/
theorem proportional_forms_bracket_identity
    {x : E}
    (A₁ A₂ : LocalTwistRepresentation (E := E) x) (lam : E → ℝ)
    (hlam : DifferentiableAt ℝ lam x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u, A₂.form y u = lam y • A₁.form y u)
    (v w : E) :
    ((lam x)^2 - lam x) • twistBracket (A₁.form x v) (A₁.form x w) =
      fderiv ℝ lam x v • A₁.form x w - fderiv ℝ lam x w • A₁.form x v := by
  have hd (u z : E) := derivative_proportional_forms A₁.form A₂.form lam x
    A₁.form_differentiable hlam hrel u z
  have hpoint := hrel.self_of_nhds
  have hdiff :
      fderiv ℝ (fun y => A₂.form y w) x v -
          fderiv ℝ (fun y => A₂.form y v) x w =
        lam x • (fderiv ℝ (fun y => A₁.form y w) x v -
          fderiv ℝ (fun y => A₁.form y v) x w) +
          (fderiv ℝ lam x v • A₁.form x w - fderiv ℝ lam x w • A₁.form x v) := by
    rw [hd, hd, smul_sub]
    abel
  rw [A₁.maurer_cartan v w, A₂.maurer_cartan v w,
    hpoint v, hpoint w, twistBracket_smul_smul, ← pow_two] at hdiff
  rw [sub_smul]
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using hdiff

/-- Lemma 4.4 in a coordinate chart of an actual configuration manifold.
Both forms are represented by actual twice differentiable invertible
body matrices; no Maurer--Cartan equation is assumed in the statement. -/
theorem proportional_immersed_body_forms_eq_one
    [FiniteDimensional ℝ E] {x : E}
    (A₁ A₂ : LocalTwistRepresentation (E := E) x) (lam : E → ℝ)
    (hlam : DifferentiableAt ℝ lam x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u, A₂.form y u = lam y • A₁.form y u)
    (hlamne : lam x ≠ 0) (hinj : Function.Injective (A₁.form x))
    (hdim : 4 ≤ Module.finrank ℝ E) : lam x = 1 := by
  by_contra hnot
  let c : ℝ := (lam x)^2 - lam x
  have hc : c ≠ 0 := by
    have heq : c = lam x * (lam x - 1) := by dsimp [c]; ring
    rw [heq]
    exact mul_ne_zero hlamne (sub_ne_zero.mpr hnot)
  let W := (A₁.form x).toLinearMap.range
  let e : E ≃ₗ[ℝ] W := LinearEquiv.ofInjective (A₁.form x).toLinearMap hinj
  let α : W →ₗ[ℝ] ℝ :=
    c⁻¹ • ((fderiv ℝ lam x).toLinearMap.comp e.symm.toLinearMap)
  have hWdim : 4 ≤ Module.finrank ℝ W := by
    rw [← e.finrank_eq]
    exact hdim
  apply no_four_dimensional_scalar_bracket W hWdim α
  intro X Y
  have h := proportional_forms_bracket_identity A₁ A₂ lam hlam hrel (e.symm X) (e.symm Y)
  have heX : A₁.form x (e.symm X) = X.val := by
    exact congrArg Subtype.val (e.apply_symm_apply X)
  have heY : A₁.form x (e.symm Y) = Y.val := by
    exact congrArg Subtype.val (e.apply_symm_apply Y)
  rw [heX, heY] at h
  have hscaled := congrArg (fun Z : Twist => c⁻¹ • Z) h
  change c⁻¹ • (c • twistBracket X.val Y.val) = _ at hscaled
  change twistBracket X.val Y.val =
    (c⁻¹ * (fderiv ℝ lam x) (e.symm X)) • Y.val -
      (c⁻¹ * (fderiv ℝ lam x) (e.symm Y)) • X.val
  simpa only [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul,
    smul_eq_mul] using hscaled

end
end Papers.Rigidity.Calculus

end
end BundleSource0016

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0016/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0016.json"

section BundleSource0017
/- Source: Papers/RigidityAngularObstruction.lean -/




@[expose] public section

/-!
# The complete pointwise angular obstruction

The right side of the differentiated codimension-one distribution equation
lies in one fixed line. This file turns that literal line-valued identity
into the matrix-rank bound used in Lemma 4.3, retaining the arbitrary
derivative functional of the proportionality factor.
-/

noncomputable section
namespace Papers.Rigidity

open Matrix
open scoped Matrix

theorem scalarCrossMatrix_eq_zero_of_cross_range (c : ℝ) (g z : Vec3)
    (h : ∀ u v : Vec3, c • (u ⨯₃ v) + g ⨯₃ (u ⨯₃ v) ∈
      Submodule.span ℝ {z}) : c = 0 ∧ g = 0 := by
  let M := scalarCrossMatrix c g
  let Z := Submodule.span ℝ {z}
  have h0 : M *ᵥ ![1, 0, 0] ∈ Z := by
    have he := h ![0, 1, 0] ![0, 0, 1]
    simpa [M, scalarCrossMatrix_mulVec, cross_apply] using he
  have h1 : M *ᵥ ![0, 1, 0] ∈ Z := by
    have he := h ![0, 0, 1] ![1, 0, 0]
    simpa [M, scalarCrossMatrix_mulVec, cross_apply] using he
  have h2 : M *ᵥ ![0, 0, 1] ∈ Z := by
    have he := h ![1, 0, 0] ![0, 1, 0]
    simpa [M, scalarCrossMatrix_mulVec, cross_apply] using he
  have hrange : M.mulVecLin.range ≤ Z := by
    rintro _ ⟨v, rfl⟩
    have hv : v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
      ext i
      fin_cases i <;> simp
    change M *ᵥ v ∈ Z
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact Z.add_mem (Z.add_mem (Z.smul_mem _ h0) (Z.smul_mem _ h1)) (Z.smul_mem _ h2)
  have hZ : Module.finrank ℝ Z ≤ 1 := by
    change Module.finrank ℝ (Submodule.span ℝ {z}) ≤ 1
    exact finrank_span_le_card ({z} : Set Vec3)
  apply scalarCrossMatrix_eq_zero_of_rank_le_one
  exact (Submodule.finrank_mono hrange).trans hZ

/-- The scalar must be one even when its derivative is arbitrary and the
rank-three distribution is not integrable. This is the full pointwise
algebraic implication of the angular Maurer–Cartan equation. -/
theorem proportionality_eq_one_of_angular_maurer_cartan
    (a : ℝ) (ha : a ≠ 0) (q : Vec3 →ₗ[ℝ] ℝ) (z : Vec3)
    (h : ∀ u v : Vec3,
      (a ^ 2 - a) • (u ⨯₃ v) - q u • v + q v • u ∈
        Submodule.span ℝ {z}) : a = 1 := by
  classical
  let g : Vec3 := (dotProductEquiv ℝ (Fin 3)).symm q
  have hg (v : Vec3) : g ⬝ᵥ v = q v := by
    exact congrArg (fun f : Module.Dual ℝ Vec3 => f v)
      ((dotProductEquiv ℝ (Fin 3)).apply_symm_apply q)
  have hline : ∀ u v : Vec3,
      (a ^ 2 - a) • (u ⨯₃ v) + g ⨯₃ (u ⨯₃ v) ∈ Submodule.span ℝ {z} := by
    intro u v
    rw [cross_cross_eq_smul_sub_smul', dotProduct_comm u g, hg u, hg v]
    convert h u v using 1 <;> abel
  have hz := (scalarCrossMatrix_eq_zero_of_cross_range (a ^ 2 - a) g z hline).1
  have hf : a * (a - 1) = 0 := by nlinarith
  have hfactor := (mul_eq_zero.mp hf).resolve_left ha
  linarith

end Papers.Rigidity

end
end
end BundleSource0017

section BundleSource0018
/- Source: Papers/RigidityDistributionDifferential.lean -/




@[expose] public section

/-!
# Proportional body motions on a distribution

The distribution is the kernel of an ordinary differentiable one-form.
The discrepancy of the two actual body forms factors through this
one-form.  Differentiating the factorization retains its exterior
derivative, so no integrability of the distribution is assumed.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix
open scoped Topology Matrix

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_factored_forms
    (θ₁ θ₂ : E → (E →L[ℝ] F)) (lam : E → ℝ)
    (β : E → (E →L[ℝ] ℝ)) (Z : E → F) (x : E)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hlam : DifferentiableAt ℝ lam x)
    (hβ : DifferentiableAt ℝ β x) (hZ : DifferentiableAt ℝ Z x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u, θ₂ y u = lam y • θ₁ y u + β y u • Z y)
    (u z : E) (hu : β x u = 0) :
    fderiv ℝ (fun y => θ₂ y u) x z =
      lam x • fderiv ℝ (fun y => θ₁ y u) x z +
        fderiv ℝ lam x z • θ₁ x u + fderiv ℝ (fun y => β y u) x z • Z x := by
  have hpart : DifferentiableAt ℝ (fun y => θ₁ y u) x :=
    hθ₁.clm_apply (differentiableAt_const u)
  have hbpart : DifferentiableAt ℝ (fun y => β y u) x :=
    hβ.clm_apply (differentiableAt_const u)
  have he : (fun y => θ₂ y u) =ᶠ[𝓝 x]
      (fun y => lam y • θ₁ y u + β y u • Z y) := hrel.mono fun y hy => hy u
  have h := congrArg (fun D : E →L[ℝ] F => D z) (he.fderiv_eq (𝕜 := ℝ))
  have hleft : DifferentiableAt ℝ (fun y => lam y • θ₁ y u) x := hlam.smul hpart
  have hright : DifferentiableAt ℝ (fun y => β y u • Z y) x := hbpart.smul hZ
  rw [fderiv_fun_add hleft hright,
    fderiv_fun_smul hlam hpart, fderiv_fun_smul hbpart hZ] at h
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, hu, zero_smul, zero_add] using h

/-- Actual Maurer--Cartan gives a line-valued discrepancy even when the
distribution has nonzero exterior derivative. -/
theorem distribution_bracket_identity
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (lam : E → ℝ) (β : E → (E →L[ℝ] ℝ)) (Z : E → Twist)
    (hlam : DifferentiableAt ℝ lam x) (hβ : DifferentiableAt ℝ β x)
    (hZ : DifferentiableAt ℝ Z x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      A₂.form y u = lam y • A₁.form y u + β y u • Z y)
    (v w : E) (hv : β x v = 0) (hw : β x w = 0) :
    ((lam x)^2 - lam x) • twistBracket (A₁.form x v) (A₁.form x w) -
        fderiv ℝ lam x v • A₁.form x w + fderiv ℝ lam x w • A₁.form x v =
      (fderiv ℝ (fun y => β y w) x v - fderiv ℝ (fun y => β y v) x w) • Z x := by
  have hd (u z : E) (hu : β x u = 0) :=
    derivative_factored_forms A₁.form A₂.form lam β Z x A₁.form_differentiable
      hlam hβ hZ hrel u z hu
  have hpoint := hrel.self_of_nhds
  have hpv : A₂.form x v = lam x • A₁.form x v := by simp [hpoint, hv]
  have hpw : A₂.form x w = lam x • A₁.form x w := by simp [hpoint, hw]
  have hdiff :
      fderiv ℝ (fun y => A₂.form y w) x v -
          fderiv ℝ (fun y => A₂.form y v) x w =
        lam x • (fderiv ℝ (fun y => A₁.form y w) x v -
          fderiv ℝ (fun y => A₁.form y v) x w) +
          (fderiv ℝ lam x v • A₁.form x w - fderiv ℝ lam x w • A₁.form x v) +
          (fderiv ℝ (fun y => β y w) x v -
            fderiv ℝ (fun y => β y v) x w) • Z x := by
    rw [hd w v hw, hd v w hv, smul_sub, sub_smul]
    abel
  rw [A₁.maurer_cartan v w, A₂.maurer_cartan v w,
    hpv, hpw, twistBracket_smul_smul, ← pow_two] at hdiff
  rw [sub_smul]
  rw [hdiff]
  abel

/-- The pointwise conclusion of Lemma 4.3 on a smooth codimension-one
distribution. Its spherical angular coordinates cover all of `Vec3`;
the possibly moving center and the derivative of the distribution are
unrestricted. The three-dimensional case is included by taking `β = 0`.
Both forms come from actual invertible body maps. -/
theorem proportional_spherical_distribution_eq_one
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (lam : E → ℝ) (β : E → (E →L[ℝ] ℝ)) (Z : E → Twist)
    (hlam : DifferentiableAt ℝ lam x) (hβ : DifferentiableAt ℝ β x)
    (hZ : DifferentiableAt ℝ Z x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      A₂.form y u = lam y • A₁.form y u + β y u • Z y)
    (e : Vec3 →ₗ[ℝ] E) (heβ : ∀ u, β x (e u) = 0)
    (heang : ∀ u, (A₁.form x (e u)).1 = u)
    (hlamne : lam x ≠ 0) : lam x = 1 := by
  let q : Vec3 →ₗ[ℝ] ℝ := (fderiv ℝ lam x).toLinearMap.comp e
  apply proportionality_eq_one_of_angular_maurer_cartan (lam x) hlamne q (Z x).1
  intro u v
  have h := congrArg Prod.fst
    (distribution_bracket_identity A₁ A₂ lam β Z hlam hβ hZ hrel
      (e u) (e v) (heβ u) (heβ v))
  have heq : ((lam x)^2 - lam x) • (u ⨯₃ v) - q u • v + q v • u =
      (fderiv ℝ (fun y => β y (e v)) x (e u) -
        fderiv ℝ (fun y => β y (e u)) x (e v)) • (Z x).1 := by
    simpa only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, twistBracket,
      heang, q, LinearMap.comp_apply, ContinuousLinearMap.coe_coe] using h
  rw [heq]
  exact (Submodule.span ℝ {(Z x).1}).smul_mem _
    (Submodule.mem_span_singleton_self _)

/-- A linear map vanishing on the kernel of a nonzero scalar functional
factors through that functional, with the factor given by an actual
chosen transverse vector. -/
theorem factor_through_scalar_functional (β : E →L[ℝ] ℝ) (D : E →L[ℝ] F)
    (u₀ : E) (hu₀ : β u₀ ≠ 0) (hker : ∀ u, β u = 0 → D u = 0) (u : E) :
    D u = β u • ((β u₀)⁻¹ • D u₀) := by
  have hz : β (u - (β u / β u₀) • u₀) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu₀, sub_self]
  have hd := hker _ hz
  rw [map_sub, map_smul] at hd
  rw [sub_eq_zero] at hd
  simpa only [div_eq_mul_inv, smul_smul] using hd

end Papers.Rigidity.Calculus

end
end
end BundleSource0018

section BundleSource0019
/- Source: Papers/RigidityDistributionFactor.lean -/



@[expose] public section

/-!
# Constructing the transverse factor of a distribution

The factor in the differentiated codimension-one argument is an explicit
quotient evaluated at a fixed transverse vector. Its differentiability
is derived from the given smooth one-forms. This removes the auxiliary
factor from the hypotheses of the proportionality conclusion.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_differentiable_scalar_factor
    (D : E → (E →L[ℝ] F)) (β : E → (E →L[ℝ] ℝ)) (x u₀ : E)
    (hD : DifferentiableAt ℝ D x) (hβ : DifferentiableAt ℝ β x)
    (hu₀ : β x u₀ ≠ 0)
    (hker : ∀ᶠ y in 𝓝 x, ∀ u, β y u = 0 → D y u = 0) :
    ∃ Z : E → F, DifferentiableAt ℝ Z x ∧
      ∀ᶠ y in 𝓝 x, ∀ u, D y u = β y u • Z y := by
  let Z : E → F := fun y => (β y u₀)⁻¹ • D y u₀
  have hbpart : DifferentiableAt ℝ (fun y => β y u₀) x :=
    hβ.clm_apply (differentiableAt_const u₀)
  have hdpart : DifferentiableAt ℝ (fun y => D y u₀) x :=
    hD.clm_apply (differentiableAt_const u₀)
  refine ⟨Z, (hbpart.inv hu₀).smul hdpart, ?_⟩
  filter_upwards [hbpart.continuousAt.eventually_ne hu₀, hker] with y hy hk
  intro u
  exact factor_through_scalar_functional (β y) (D y) u₀ hy hk u

/-- The full local codimension-one proportionality conclusion, expressed
using the actual kernel distribution. The factor used in the proof is
constructed, not assumed. There is no involutivity or integrability
hypothesis on the distribution. -/
theorem proportional_spherical_kernel_eq_one
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (lam : E → ℝ) (β : E → (E →L[ℝ] ℝ))
    (hlam : DifferentiableAt ℝ lam x) (hβ : DifferentiableAt ℝ β x)
    (u₀ : E) (hu₀ : β x u₀ ≠ 0)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u, β y u = 0 →
      A₂.form y u = lam y • A₁.form y u)
    (e : Vec3 →ₗ[ℝ] E) (heβ : ∀ u, β x (e u) = 0)
    (heang : ∀ u, (A₁.form x (e u)).1 = u)
    (hlamne : lam x ≠ 0) : lam x = 1 := by
  let D : E → (E →L[ℝ] Twist) := fun y => A₂.form y - lam y • A₁.form y
  have hD : DifferentiableAt ℝ D x :=
    A₂.form_differentiable.sub (hlam.smul A₁.form_differentiable)
  have hker : ∀ᶠ y in 𝓝 x, ∀ u, β y u = 0 → D y u = 0 := by
    filter_upwards [hrel] with y hy
    intro u hu
    change A₂.form y u - lam y • A₁.form y u = 0
    exact sub_eq_zero.mpr (hy u hu)
  obtain ⟨Z, hZ, hz⟩ := exists_differentiable_scalar_factor D β x u₀ hD hβ hu₀ hker
  apply proportional_spherical_distribution_eq_one A₁ A₂ lam β Z hlam hβ hZ ?_
    e heβ heang hlamne
  filter_upwards [hz] with y hy
  intro u
  have h := hy u
  change A₂.form y u - lam y • A₁.form y u = β y u • Z y at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

/-- The full-dimensional spherical case, including the three-dimensional
manifold in Lemma 4.3. Surjectivity of angular coordinates is enough;
there is no codimension-one factor or auxiliary distribution. -/
theorem proportional_spherical_forms_eq_one
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (lam : E → ℝ) (hlam : DifferentiableAt ℝ lam x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u, A₂.form y u = lam y • A₁.form y u)
    (e : Vec3 →ₗ[ℝ] E) (heang : ∀ u, (A₁.form x (e u)).1 = u)
    (hlamne : lam x ≠ 0) : lam x = 1 := by
  apply proportional_spherical_distribution_eq_one A₁ A₂ lam (fun _ => 0)
    (fun _ => 0) hlam (differentiableAt_const (0 : E →L[ℝ] ℝ)) (differentiableAt_const (0 : Twist)) ?_
    e (by simp) heang hlamne
  filter_upwards [hrel] with y hy
  simpa using hy

end Papers.Rigidity.Calculus

end
end
end BundleSource0019

section BundleSource0020
/- Source: Papers/RigidityInfiniteCenterObstruction.lean -/




@[expose] public section

/-!
# Proportionality on an infinite-center twist space

The rank-three common-pin classification also permits a center at
infinity. Its twist space consists of rotations parallel to a nonzero
direction and translations perpendicular to it. On that translation
plane, a nonzero multiple of the quarter-turn plus any real scalar
identity is injective. Consequently its image cannot lie in the one line
allowed by the differentiated codimension-one discrepancy.

This proves the same proportionality obstruction directly in the
infinite-center chart, without a projective change of the Euclidean
configuration manifold.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix

def planarRotationScalar (d : Vec3) (c k : ℝ) : normalPlane d →ₗ[ℝ] Vec3 :=
  c • ((crossProduct d).comp (normalPlane d).subtype) - k • (normalPlane d).subtype

theorem planarRotationScalar_injective (d : Vec3) (hd : d ≠ 0)
    (c k : ℝ) (hc : c ≠ 0) : Function.Injective (planarRotationScalar d c k) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  change c • (d ⨯₃ u.val) - k • u.val = 0 at hu
  have he : c • (d ⨯₃ u.val) = k • u.val := sub_eq_zero.mp hu
  have hdot := congrArg (fun z : Vec3 => u.val ⬝ᵥ z) he
  have hk : k * (u.val ⬝ᵥ u.val) = 0 := by
    simpa only [dotProduct_smul, dot_cross_self, smul_eq_mul, mul_zero] using hdot.symm
  apply Subtype.ext
  change u.val = 0
  rcases mul_eq_zero.mp hk with hk | hn
  · have hcross : d ⨯₃ u.val = 0 := by
      rw [hk, zero_smul] at he
      exact (smul_eq_zero.mp he).resolve_left hc
    have hspan : u.val ∈ Submodule.span ℝ {d} := by
      rw [← ker_crossProduct_eq_span d hd]
      exact hcross
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hspan
    have huperp : d ⬝ᵥ u.val = 0 := u.property
    rw [← ht, dotProduct_smul] at huperp
    have hdd : d ⬝ᵥ d ≠ 0 := fun h => hd (dotProduct_self_eq_zero.mp h)
    have htzero : t = 0 := (mul_eq_zero.mp huperp).resolve_right hdd
    rw [← ht, htzero, zero_smul]
  · exact dotProduct_self_eq_zero.mp hn

/-- The actual infinite-center Lie space obeys the same line-valued
Maurer--Cartan obstruction as the finite-center rotation space. -/
theorem proportionality_eq_one_of_infiniteCenter_maurer_cartan
    (a : ℝ) (ha : a ≠ 0) (d : Vec3) (hd : d ≠ 0)
    (q : infiniteCenterSpace d →ₗ[ℝ] ℝ) (Z : Twist)
    (h : ∀ X Y : infiniteCenterSpace d,
      (a ^ 2 - a) • twistBracket X.val Y.val - q X • Y.val + q Y • X.val ∈
        Submodule.span ℝ {Z}) : a = 1 := by
  classical
  by_contra hne
  have hc : a ^ 2 - a ≠ 0 := by
    intro hz
    have hf : a * (a - 1) = 0 := by nlinarith
    have haone : a - 1 = 0 := (mul_eq_zero.mp hf).resolve_left ha
    exact hne (sub_eq_zero.mp haone)
  let r : infiniteCenterSpace d := ⟨(d, 0), by constructor <;> simp⟩
  let A := planarRotationScalar d (a ^ 2 - a) (q r)
  have hline : A.range ≤ Submodule.span ℝ {Z.2} := by
    rintro z ⟨u, rfl⟩
    let y : infiniteCenterSpace d := ⟨(0, u.val), by
      constructor
      · simp
      · have hu : d ⬝ᵥ u.val = 0 := u.property
        simpa only [dotProduct_comm] using hu⟩
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (h r y)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨s, ?_⟩
    have he := congrArg Prod.snd hs
    simpa [A, planarRotationScalar, r, y, twistBracket] using he
  have hdim : Module.finrank ℝ A.range = 2 := by
    rw [LinearMap.finrank_range_of_inj (planarRotationScalar_injective d hd _ _ hc)]
    exact finrank_normalPlane d hd
  have hsmall : Module.finrank ℝ (Submodule.span ℝ {Z.2}) ≤ 1 := by
    exact finrank_span_le_card ({Z.2} : Set Vec3)
  have hbound := (Submodule.finrank_mono hline).trans hsmall
  omega

namespace Calculus

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The distribution may move and need not be integrable. The body forms
are actual Maurer--Cartan forms, and the ordinary real translation-plane
argument removes the infinite-center case directly. -/
theorem proportional_infiniteCenter_distribution_eq_one
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (lam : E → ℝ) (β : E → (E →L[ℝ] ℝ)) (Z : E → Twist)
    (hlam : DifferentiableAt ℝ lam x) (hβ : DifferentiableAt ℝ β x)
    (hZ : DifferentiableAt ℝ Z x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      A₂.form y u = lam y • A₁.form y u + β y u • Z y)
    (d : Vec3) (hd : d ≠ 0) (e : infiniteCenterSpace d →ₗ[ℝ] E)
    (heβ : ∀ X, β x (e X) = 0)
    (heform : ∀ X, A₁.form x (e X) = X.val)
    (hlamne : lam x ≠ 0) : lam x = 1 := by
  let q : infiniteCenterSpace d →ₗ[ℝ] ℝ := (fderiv ℝ lam x).toLinearMap.comp e
  apply proportionality_eq_one_of_infiniteCenter_maurer_cartan (lam x) hlamne d hd q (Z x)
  intro X Y
  have he := distribution_bracket_identity A₁ A₂ lam β Z hlam hβ hZ hrel
    (e X) (e Y) (heβ X) (heβ Y)
  rw [heform X, heform Y] at he
  change ((lam x) ^ 2 - lam x) • twistBracket X.val Y.val -
    fderiv ℝ lam x (e X) • Y.val + fderiv ℝ lam x (e Y) • X.val ∈ _
  rw [he]
  exact (Submodule.span ℝ {Z x}).smul_mem _
    (Submodule.mem_span_singleton_self _)

end Calculus

end

end Papers.Rigidity

end
end BundleSource0020

section BundleSource0021
/- Source: Papers/RigidityRankOneDiscrepancy.lean -/






@[expose] public section

/-!
# The actual smooth factor of a rank-one body discrepancy

The common-pin algebra bounds the rank of the difference of two body
forms by one. At a point where this difference is nonzero, one fixed
output coordinate supplies a nonvanishing scalar one-form. Its kernel
is exactly the discrepancy kernel nearby, and the transverse factor is
the explicit quotient used in the differentiated argument.

Neither a smooth choice of the common-pin image subspace nor an
integrable distribution is assumed. These discrepancy identities support
Proposition 4.1.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix

theorem exists_twist_functional_ne_zero (X : Twist) (hX : X ≠ 0) :
    ∃ ℓ : Twist →L[ℝ] ℝ, ℓ X ≠ 0 := by
  classical
  by_cases hω : X.1 = 0
  · have hv : X.2 ≠ 0 := fun hv => hX (Prod.ext hω hv)
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => hv (funext h))
    exact ⟨(ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ Vec3 Vec3), hi⟩
  · obtain ⟨i, hi⟩ := not_forall.mp (fun h => hω (funext h))
    exact ⟨(ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ Vec3 Vec3), hi⟩

theorem kernel_coordinate_le_kernel_of_rank_le_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : E →ₗ[ℝ] Twist) (ℓ : Twist →ₗ[ℝ] ℝ) (u₀ : E)
    (hne : ℓ (D u₀) ≠ 0) (hrank : Module.finrank ℝ D.range ≤ 1) :
    ∀ u, ℓ (D u) = 0 → D u = 0 := by
  have hvalue : D u₀ ≠ 0 := fun hz => hne (by rw [hz, map_zero])
  have hle : Submodule.span ℝ {D u₀} ≤ D.range := by
    apply Submodule.span_le.mpr
    rintro z rfl
    exact ⟨u₀, rfl⟩
  have hlow := Submodule.finrank_mono hle
  rw [finrank_span_singleton hvalue] at hlow
  have hdim : Module.finrank ℝ D.range = 1 := by omega
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim
    (show D u₀ ∈ D.range from ⟨u₀, rfl⟩) hvalue
  intro u hu
  have hm : D u ∈ Submodule.span ℝ {D u₀} := by
    rw [← hspan]
    exact ⟨u, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hz : a * ℓ (D u₀) = 0 := by
    rw [← ha, map_smul, smul_eq_mul] at hu
    exact hu
  have ha0 : a = 0 := (mul_eq_zero.mp hz).resolve_right hne
  rw [← ha, ha0, zero_smul]

/-- A linear lift is constructed from the actual range inclusion. -/
theorem exists_linear_lift_of_le_range
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (A : E →ₗ[ℝ] F) (K : Submodule ℝ F) (hK : K ≤ A.range) :
    ∃ e : K →ₗ[ℝ] E, ∀ X, A (e X) = X.val := by
  obtain ⟨s, hs⟩ := A.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict A)
  let e : K →ₗ[ℝ] E := s.comp (Submodule.inclusion hK)
  refine ⟨e, ?_⟩
  intro X
  exact congrArg Subtype.val
    (congrArg (fun L : A.range →ₗ[ℝ] A.range => L (Submodule.inclusion hK X)) hs)

def finiteCenterRotations (c : Vec3) : Vec3 →ₗ[ℝ] finiteCenterSpace c :=
  ((LinearMap.id : Vec3 →ₗ[ℝ] Vec3).prod (-((crossProduct (R := ℝ)).flip c))).codRestrict
    (finiteCenterSpace c) (by
      intro u
      change -(u ⨯₃ c) + u ⨯₃ c = 0
      exact neg_add_cancel _)

namespace Calculus

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_differentiable_rank_one_factor
    (D : E → (E →L[ℝ] Twist)) (x : E)
    (hD : DifferentiableAt ℝ D x) (hne : D x ≠ 0)
    (hrank : ∀ᶠ y in 𝓝 x, Module.finrank ℝ (D y).toLinearMap.range ≤ 1) :
    ∃ (β : E → (E →L[ℝ] ℝ)) (Z : E → Twist),
      DifferentiableAt ℝ β x ∧ DifferentiableAt ℝ Z x ∧
      (∀ᶠ y in 𝓝 x, ∀ u, D y u = β y u • Z y) ∧
      (∀ u, β x u = 0 ↔ D x u = 0) := by
  classical
  have hu : ∃ u₀, D x u₀ ≠ 0 := by
    by_contra! h
    exact hne (ContinuousLinearMap.ext h)
  obtain ⟨u₀, hu₀⟩ := hu
  obtain ⟨ℓ, hℓ⟩ := exists_twist_functional_ne_zero (D x u₀) hu₀
  let β : E → (E →L[ℝ] ℝ) := fun y => ℓ.comp (D y)
  have hβ : DifferentiableAt ℝ β x := (differentiableAt_const ℓ).clm_comp hD
  have hβu : DifferentiableAt ℝ (fun y => β y u₀) x :=
    hβ.clm_apply (differentiableAt_const u₀)
  have hker : ∀ᶠ y in 𝓝 x, ∀ u, β y u = 0 → D y u = 0 := by
    filter_upwards [hrank, hβu.continuousAt.eventually_ne hℓ] with y hy hne_y
    exact kernel_coordinate_le_kernel_of_rank_le_one (D y).toLinearMap
      ℓ.toLinearMap u₀ hne_y hy
  obtain ⟨Z, hZ, hfactor⟩ := exists_differentiable_scalar_factor D β x u₀ hD hβ hℓ hker
  refine ⟨β, Z, hβ, hZ, hfactor, ?_⟩
  intro u
  refine ⟨hker.self_of_nhds u, ?_⟩
  intro hu
  change ℓ (D x u) = 0
  rw [hu, map_zero]

/-- The rank-one factor is derived from the actual discrepancy. If its
kernel contains a finite or infinite center twist space in the first
body, the differentiated body equations force the scalar to be one. -/
theorem proportional_center_discrepancy_eq_one
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (lam : E → ℝ) (hlam : DifferentiableAt ℝ lam x) (hlamne : lam x ≠ 0)
    (hne : A₂.form x - lam x • A₁.form x ≠ 0)
    (hrank : ∀ᶠ y in 𝓝 x, Module.finrank ℝ
      (A₂.form y - lam y • A₁.form y).toLinearMap.range ≤ 1)
    (hcenter :
      (∃ c : Vec3, finiteCenterSpace c ≤
        ((A₁.form x).toLinearMap.comp
          (A₂.form x - lam x • A₁.form x).toLinearMap.ker.subtype).range) ∨
      (∃ d : Vec3, d ≠ 0 ∧ infiniteCenterSpace d ≤
        ((A₁.form x).toLinearMap.comp
          (A₂.form x - lam x • A₁.form x).toLinearMap.ker.subtype).range)) :
    lam x = 1 := by
  let D : E → (E →L[ℝ] Twist) := fun y => A₂.form y - lam y • A₁.form y
  have hD : DifferentiableAt ℝ D x :=
    A₂.form_differentiable.sub (hlam.smul A₁.form_differentiable)
  obtain ⟨β, Z, hβ, hZ, hfactor, hker⟩ :=
    exists_differentiable_rank_one_factor D x hD hne hrank
  have hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      A₂.form y u = lam y • A₁.form y u + β y u • Z y := by
    filter_upwards [hfactor] with y hy
    intro u
    have he : A₂.form y u - lam y • A₁.form y u = β y u • Z y := hy u
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  let L : (D x).toLinearMap.ker →ₗ[ℝ] Twist :=
    (A₁.form x).toLinearMap.comp (D x).toLinearMap.ker.subtype
  rcases hcenter with ⟨c, hc⟩ | ⟨d, hd, hdcenter⟩
  · obtain ⟨s, hs⟩ := exists_linear_lift_of_le_range L (finiteCenterSpace c) hc
    let e : Vec3 →ₗ[ℝ] E :=
      (D x).toLinearMap.ker.subtype.comp (s.comp (finiteCenterRotations c))
    apply proportional_spherical_distribution_eq_one A₁ A₂ lam β Z hlam hβ hZ hrel e
    · intro u
      apply (hker _).mpr
      exact (s (finiteCenterRotations c u)).property
    · intro u
      exact congrArg Prod.fst (hs (finiteCenterRotations c u))
    · exact hlamne
  · obtain ⟨s, hs⟩ := exists_linear_lift_of_le_range L (infiniteCenterSpace d) hdcenter
    let e : infiniteCenterSpace d →ₗ[ℝ] E := (D x).toLinearMap.ker.subtype.comp s
    apply proportional_infiniteCenter_distribution_eq_one A₁ A₂ lam β Z hlam hβ hZ hrel
      d hd e
    · intro X
      apply (hker _).mpr
      exact (s X).property
    · exact hs
    · exact hlamne

end Calculus

end

end Papers.Rigidity

end
end BundleSource0021

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0021/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0021.json"

section BundleSource0022
/- Source: Papers/RigidityRankFourDifferential.lean -/



@[expose] public section

/-!
# Closing both ranks of the body-form discrepancy

The actual common-pin image can have dimension three or four. The
rank-three case gives a discrepancy of rank one; the rank-four case
gives zero discrepancy. These ranks can change with the configuration.
The proof below handles that change without an assumed constant-rank
submanifold: wherever the discrepancy is nonzero, the center obstruction
forces the scalar to be one. If the scalar were different from one at a
zero of the discrepancy, continuity would force the discrepancy to vanish
throughout a neighborhood. The full-dimensional Maurer--Cartan argument
then gives the same contradiction.

All body equations enter through actual LocalTwistRepresentation data.
The differential identities supply the rank-four branch of Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Literal local matrix representability of a given body form. -/
def HasLocalTwistRepresentation (θ : E → (E →L[ℝ] Twist)) (x : E) : Prop :=
  ∃ A : LocalTwistRepresentation (E := E) x, A.form = θ

/-- The actual first-body image of the discrepancy kernel contains a
finite or infinite center space. This property is supplied pointwise by
the cofactor classification, rather than by a chosen smooth distribution. -/
def CenterInDiscrepancyKernel (θ₁ θ₂ : E → (E →L[ℝ] Twist))
    (lam : E → ℝ) (x : E) : Prop :=
  (∃ c : Vec3, finiteCenterSpace c ≤
    ((θ₁ x).toLinearMap.comp (θ₂ x - lam x • θ₁ x).toLinearMap.ker.subtype).range) ∨
  (∃ d : Vec3, d ≠ 0 ∧ infiniteCenterSpace d ≤
    ((θ₁ x).toLinearMap.comp (θ₂ x - lam x • θ₁ x).toLinearMap.ker.subtype).range)

/-- A varying rank-one discrepancy between actual immersed body forms
cannot carry a scalar other than one. All ranks, kernels and center
spaces in the statement are the literal linear-algebraic objects. -/
theorem rankFour_discrepancy_scalar_eq_one
    [FiniteDimensional ℝ E]
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (lam : E → ℝ) (x : E)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hlam : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ lam y)
    (hlamne : lam x ≠ 0) (hinj : Function.Injective (θ₁ x))
    (hdim : 4 ≤ Module.finrank ℝ E)
    (hrank : ∀ᶠ y in 𝓝 x,
      Module.finrank ℝ (θ₂ y - lam y • θ₁ y).toLinearMap.range ≤ 1)
    (hcenter : ∀ᶠ y in 𝓝 x,
      θ₂ y - lam y • θ₁ y ≠ 0 → CenterInDiscrepancyKernel θ₁ θ₂ lam y) :
    lam x = 1 := by
  have hlamx : DifferentiableAt ℝ lam x := hlam.self_of_nhds
  have hnonzero : ∀ᶠ y in 𝓝 x,
      θ₂ y - lam y • θ₁ y ≠ 0 → lam y = 1 := by
    filter_upwards [hactual, hlam, hlamx.continuousAt.eventually_ne hlamne,
      eventually_eventually_nhds.mpr hrank, hcenter] with y hy hlamy hlamyne hranky hcy
    intro hD
    obtain ⟨A₁, hA₁⟩ := hy.1
    obtain ⟨A₂, hA₂⟩ := hy.2
    subst θ₁
    subst θ₂
    apply proportional_center_discrepancy_eq_one A₁ A₂ lam hlamy hlamyne
    · exact hD
    · exact hranky
    · exact hcy hD
  by_contra hnot
  have hzero : ∀ᶠ y in 𝓝 x, θ₂ y - lam y • θ₁ y = 0 := by
    filter_upwards [hnonzero, hlamx.continuousAt.eventually_ne hnot] with y hy hyne
    by_contra hn
    exact hyne (hy hn)
  obtain ⟨A₁, hA₁⟩ := hactual.self_of_nhds.1
  obtain ⟨A₂, hA₂⟩ := hactual.self_of_nhds.2
  have hrel : ∀ᶠ y in 𝓝 x, ∀ u, A₂.form y u = lam y • A₁.form y u := by
    filter_upwards [hzero] with y hy
    intro u
    rw [hA₁, hA₂]
    exact congrArg (fun L : E →L[ℝ] Twist => L u) (sub_eq_zero.mp hy)
  exact hnot (proportional_immersed_body_forms_eq_one A₁ A₂ lam hlamx hrel hlamne
    (by simpa only [hA₁] using hinj) hdim)

end Papers.Rigidity.Calculus

end
end
end BundleSource0022

section BundleSource0023
/- Source: Papers/RigiditySmoothCofactor.lean -/






@[expose] public section

/-!
# A smooth scalar from the actual stationary Cramer vector

One fixed tangent basis and one fixed regular pin produce a polynomial
Cramer vector in the entries of the first body's form. A nonzero output
coordinate then defines the scalar as an ordinary quotient. The common
pin rank theorem proves that this quotient is the pointwise algebraic
scalar and supplies the rank and center properties of its discrepancy.

This construction supplies the smooth choices in the rank-four branch.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix CofactorKernel
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem differentiableAt_det_three (M : E → Matrix (Fin 3) (Fin 3) ℝ) (x : E)
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
    DifferentiableAt ℝ (fun y => (M y).det) x := by
  simp only [Matrix.det_fin_three]
  have h₁ := ((hM 0 0).mul (hM 1 1)).mul (hM 2 2)
  have h₂ := ((hM 0 0).mul (hM 1 2)).mul (hM 2 1)
  have h₃ := ((hM 0 1).mul (hM 1 0)).mul (hM 2 2)
  have h₄ := ((hM 0 1).mul (hM 1 2)).mul (hM 2 0)
  have h₅ := ((hM 0 2).mul (hM 1 0)).mul (hM 2 1)
  have h₆ := ((hM 0 2).mul (hM 1 1)).mul (hM 2 0)
  exact ((((h₁.sub h₂).sub h₃).add h₄).add h₅).sub h₆

theorem bodyEvaluation_coordinate_differentiableAt
    (θ : E → (E →L[ℝ] Twist)) (x : E) (hθ : DifferentiableAt ℝ θ x)
    (p : Vec3) (u : E) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => bodyEvaluation (θ y).toLinearMap p u i) x := by
  exact (ContinuousLinearMap.proj i).differentiableAt.comp x
    ((evaluation p).toContinuousLinearMap.differentiableAt.comp x
      (hθ.clm_apply (differentiableAt_const u)))

theorem bodyMinor_differentiableAt
    (θ : E → (E →L[ℝ] Twist)) (x : E) (hθ : DifferentiableAt ℝ θ x)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p : Vec3) :
    DifferentiableAt ℝ (fun y => bodyMinor (θ y).toLinearMap b p) x := by
  apply differentiableAt_det_three
  intro i j
  exact bodyEvaluation_coordinate_differentiableAt θ x hθ p (b (some j)) i

theorem bodyCofactor_differentiableAt
    (θ : E → (E →L[ℝ] Twist)) (x : E) (hθ : DifferentiableAt ℝ θ x)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p : Vec3) :
    DifferentiableAt ℝ (fun y => bodyCofactor (θ y).toLinearMap b p) x := by
  have hcramer (i : Fin 3) : DifferentiableAt ℝ (fun y =>
      Matrix.cramer (pivotMatrix (bodyEvaluation (θ y).toLinearMap p)
        (fun j => b (some j))) (bodyEvaluation (θ y).toLinearMap p (b none)) i) x := by
    simp only [Matrix.cramer_apply]
    apply differentiableAt_det_three
    intro j k
    by_cases hk : k = i
    · simpa only [Matrix.updateCol_apply, hk, ite_true] using
        bodyEvaluation_coordinate_differentiableAt θ x hθ p (b none) j
    · simpa only [Matrix.updateCol_apply, hk, ite_false, pivotMatrix] using
        bodyEvaluation_coordinate_differentiableAt θ x hθ p (b (some k)) j
  have hsum : DifferentiableAt ℝ (fun y => ∑ i : Fin 3,
      Matrix.cramer (pivotMatrix (bodyEvaluation (θ y).toLinearMap p)
        (fun j => b (some j))) (bodyEvaluation (θ y).toLinearMap p (b none)) i •
        b (some i)) x := by
    exact DifferentiableAt.fun_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
        (hcramer i).smul_const (b (some i)))
  exact ((bodyMinor_differentiableAt θ x hθ b p).smul_const (b none)).sub hsum

/-- The actual common-pin scalar has a differentiable representative on
a whole neighborhood. The scalar, the rank bound, and the center in the
discrepancy kernel are all obtained from the coupled pin operators. -/
theorem exists_smooth_commonPin_scalar_of_nonzero [FiniteDimensional ℝ E]
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p₀ : Vec3)
    (hp₀ : bodyMinor (θ₁ x).toLinearMap b p₀ ≠ 0)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective (θ₁ y))
    (hsecond : θ₂ x (bodyCofactor (θ₁ x).toLinearMap b p₀) ≠ 0)
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p : Vec3,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∃ lam : E → ℝ,
      (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ lam y) ∧ lam x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, Module.finrank ℝ (θ₂ y - lam y • θ₁ y).toLinearMap.range ≤ 1) ∧
      (∀ᶠ y in 𝓝 x, θ₂ y - lam y • θ₁ y ≠ 0 →
        CenterInDiscrepancyKernel θ₁ θ₂ lam y) ∧
      (∀ᶠ y in 𝓝 x, ∀ p, bodyMinor (θ₁ y).toLinearMap b p ≠ 0 →
        θ₂ y (bodyCofactor (θ₁ y).toLinearMap b p) =
          lam y • θ₁ y (bodyCofactor (θ₁ y).toLinearMap b p)) := by
  obtain ⟨A₁, hA₁⟩ := hactual.self_of_nhds.1
  obtain ⟨A₂, hA₂⟩ := hactual.self_of_nhds.2
  have hd₁ : DifferentiableAt ℝ θ₁ x := by simpa only [hA₁] using A₁.form_differentiable
  have hd₂ : DifferentiableAt ℝ θ₂ x := by simpa only [hA₂] using A₂.form_differentiable
  let C : E → E := fun y => bodyCofactor (θ₁ y).toLinearMap b p₀
  have hC : DifferentiableAt ℝ C x := bodyCofactor_differentiableAt θ₁ x hd₁ b p₀
  have hCne : C x ≠ 0 := basisVector_ne_zero (bodyEvaluation (θ₁ x).toLinearMap p₀) b hp₀
  have hvalue : θ₁ x (C x) ≠ 0 := by
    intro hz
    exact hCne (hinj.self_of_nhds (by simpa only [map_zero] using hz))
  obtain ⟨ℓ, hℓ⟩ := exists_twist_functional_ne_zero (θ₁ x (C x)) hvalue
  let f₁ : E → ℝ := fun y => ℓ (θ₁ y (C y))
  let f₂ : E → ℝ := fun y => ℓ (θ₂ y (C y))
  let lam : E → ℝ := fun y => f₂ y / f₁ y
  have hf₁ : DifferentiableAt ℝ f₁ x := ℓ.differentiableAt.comp x (hd₁.clm_apply hC)
  have hpnear : ∀ᶠ y in 𝓝 x, bodyMinor (θ₁ y).toLinearMap b p₀ ≠ 0 :=
    (bodyMinor_differentiableAt θ₁ x hd₁ b p₀).continuousAt.eventually_ne hp₀
  have hfnear : ∀ᶠ y in 𝓝 x, f₁ y ≠ 0 := hf₁.continuousAt.eventually_ne hℓ
  have hsecondnear : ∀ᶠ y in 𝓝 x, θ₂ y (C y) ≠ 0 :=
    (hd₂.clm_apply hC).continuousAt.eventually_ne hsecond
  have hdata : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ lam y ∧ lam y ≠ 0 ∧
      Module.finrank ℝ (θ₂ y - lam y • θ₁ y).toLinearMap.range ≤ 1 ∧
      (θ₂ y - lam y • θ₁ y ≠ 0 → CenterInDiscrepancyKernel θ₁ θ₂ lam y) ∧
      (∀ p, bodyMinor (θ₁ y).toLinearMap b p ≠ 0 →
        θ₂ y (bodyCofactor (θ₁ y).toLinearMap b p) =
          lam y • θ₁ y (bodyCofactor (θ₁ y).toLinearMap b p)) := by
    filter_upwards [hactual, hinj, hrank, hpnear, hfnear, hsecondnear]
      with y hy hyinj hyrank hyp hyf hysecond
    obtain ⟨B₁, hB₁⟩ := hy.1
    obtain ⟨B₂, hB₂⟩ := hy.2
    have hdy₁ : DifferentiableAt ℝ θ₁ y := by simpa only [hB₁] using B₁.form_differentiable
    have hdy₂ : DifferentiableAt ℝ θ₂ y := by simpa only [hB₂] using B₂.form_differentiable
    have hCy : DifferentiableAt ℝ C y := bodyCofactor_differentiableAt θ₁ y hdy₁ b p₀
    have hfy₁ : DifferentiableAt ℝ f₁ y := ℓ.differentiableAt.comp y (hdy₁.clm_apply hCy)
    have hfy₂ : DifferentiableAt ℝ f₂ y := ℓ.differentiableAt.comp y (hdy₂.clm_apply hCy)
    obtain ⟨a, ha, hfamily, hsmall, hcenter⟩ := bodyForms_scalar_discrepancy_of_nonzero
      (θ₁ y).toLinearMap (θ₂ y).toLinearMap hyinj b p₀ hyp hysecond hyrank
    change ∀ p : Vec3, bodyMinor (θ₁ y).toLinearMap b p ≠ 0 →
      θ₂ y (bodyCofactor (θ₁ y).toLinearMap b p) =
        a • θ₁ y (bodyCofactor (θ₁ y).toLinearMap b p) at hfamily
    have he : f₂ y = a * f₁ y := by
      change ℓ (θ₂ y (bodyCofactor (θ₁ y).toLinearMap b p₀)) =
        a * ℓ (θ₁ y (bodyCofactor (θ₁ y).toLinearMap b p₀))
      rw [hfamily p₀ hyp, map_smul, smul_eq_mul]
    have hlama : lam y = a := by
      change f₂ y / f₁ y = a
      rw [he, mul_div_cancel_right₀ _ hyf]
    have hprod : DifferentiableAt ℝ (fun z => f₂ z * (f₁ z)⁻¹) y :=
      hfy₂.mul (hfy₁.inv hyf)
    have hquot : DifferentiableAt ℝ lam y := by
      simpa only [lam, div_eq_mul_inv] using hprod
    refine ⟨hquot, ?_, ?_, ?_, ?_⟩
    · rwa [hlama]
    · rw [hlama, ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul]
      exact hsmall
    · intro hD
      have hDlin : (θ₂ y).toLinearMap - a • (θ₁ y).toLinearMap ≠ 0 := by
        intro hz
        apply hD
        apply ContinuousLinearMap.coe_injective
        simpa only [hlama, ContinuousLinearMap.toLinearMap_sub,
          ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_zero] using hz
      have hc := hcenter hDlin
      simpa only [CenterInDiscrepancyKernel, hlama, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.toLinearMap_smul, LinearMap.range_comp,
        Submodule.range_subtype] using hc
    · simpa only [hlama] using hfamily
  exact ⟨lam, hdata.mono (fun _ h => h.1), hdata.self_of_nhds.2.1,
    hdata.mono (fun _ h => h.2.2.1), hdata.mono (fun _ h => h.2.2.2.1),
    hdata.mono (fun _ h => h.2.2.2.2)⟩

theorem exists_smooth_commonPin_scalar [FiniteDimensional ℝ E]
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p₀ : Vec3)
    (hp₀ : bodyMinor (θ₁ x).toLinearMap b p₀ ≠ 0)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective (θ₁ y) ∧ Function.Injective (θ₂ y))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p : Vec3,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∃ lam : E → ℝ,
      (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ lam y) ∧ lam x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, Module.finrank ℝ (θ₂ y - lam y • θ₁ y).toLinearMap.range ≤ 1) ∧
      (∀ᶠ y in 𝓝 x, θ₂ y - lam y • θ₁ y ≠ 0 →
        CenterInDiscrepancyKernel θ₁ θ₂ lam y) ∧
      (∀ᶠ y in 𝓝 x, ∀ p, bodyMinor (θ₁ y).toLinearMap b p ≠ 0 →
        θ₂ y (bodyCofactor (θ₁ y).toLinearMap b p) =
          lam y • θ₁ y (bodyCofactor (θ₁ y).toLinearMap b p)) := by
  have hsecond : θ₂ x (bodyCofactor (θ₁ x).toLinearMap b p₀) ≠ 0 := by
    intro hz
    have hc : bodyCofactor (θ₁ x).toLinearMap b p₀ = 0 := by
      apply hinj.self_of_nhds.2
      exact hz.trans (map_zero (θ₂ x)).symm
    exact basisVector_ne_zero (bodyEvaluation (θ₁ x).toLinearMap p₀) b hp₀ hc
  exact exists_smooth_commonPin_scalar_of_nonzero θ₁ θ₂ x b p₀ hp₀ hactual
    (hinj.mono fun _ h => h.1) hsecond hrank

/-- Only a nonzero value on the surviving stationary motion is required
of the second body. This also handles a rank-three second projection. -/
theorem actual_rankFour_commonPin_kernel_merges_of_nonzero [FiniteDimensional ℝ E]
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p₀ : Vec3)
    (hp₀ : bodyMinor (θ₁ x).toLinearMap b p₀ ≠ 0)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective (θ₁ y))
    (hsecond : θ₂ x (bodyCofactor (θ₁ x).toLinearMap b p₀) ≠ 0)
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p : Vec3,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∀ u : E, evaluateTwist p₀ (θ₁ x u) = 0 → θ₂ x u = θ₁ x u := by
  obtain ⟨lam, hlam, hlamne, hsmall, hcenter, hfamily⟩ :=
    exists_smooth_commonPin_scalar_of_nonzero θ₁ θ₂ x b p₀ hp₀ hactual hinj hsecond hrank
  have hdim : 4 ≤ Module.finrank ℝ E := by
    rw [Module.finrank_eq_card_basis b]
    norm_num
  have hone := rankFour_discrepancy_scalar_eq_one θ₁ θ₂ lam x hactual hlam hlamne
    hinj.self_of_nhds hdim hsmall hcenter
  have hcofactor : θ₂ x (bodyCofactor (θ₁ x).toLinearMap b p₀) =
      θ₁ x (bodyCofactor (θ₁ x).toLinearMap b p₀) := by
    simpa only [hone, one_smul] using hfamily.self_of_nhds p₀ hp₀
  intro u hu
  have heval : bodyEvaluation (θ₁ x).toLinearMap p₀ u = 0 := by
    change RB31E2E.Twist.eval (θ₁ x u) p₀ = 0
    rwa [vendor_eval_eq_evaluateTwist]
  obtain ⟨a, ha⟩ := kernel_vector_eq_smul_basisVector
    (bodyEvaluation (θ₁ x).toLinearMap p₀) b hp₀ u heval
  change u = a • bodyCofactor (θ₁ x).toLinearMap b p₀ at ha
  rw [ha, map_smul, map_smul, hcofactor]

/-- The common stationary twists at the selected regular pin are equal
in the two actual bodies. Smooth proportionality and both possible
center types have been eliminated from the hypotheses. -/
theorem actual_rankFour_commonPin_kernel_merges [FiniteDimensional ℝ E]
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (b : Module.Basis (Option (Fin 3)) ℝ E) (p₀ : Vec3)
    (hp₀ : bodyMinor (θ₁ x).toLinearMap b p₀ ≠ 0)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective (θ₁ y) ∧ Function.Injective (θ₂ y))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p : Vec3,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∀ u : E, evaluateTwist p₀ (θ₁ x u) = 0 → θ₂ x u = θ₁ x u := by
  obtain ⟨lam, hlam, hlamne, hsmall, hcenter, hfamily⟩ :=
    exists_smooth_commonPin_scalar θ₁ θ₂ x b p₀ hp₀ hactual hinj hrank
  have hdim : 4 ≤ Module.finrank ℝ E := by
    rw [Module.finrank_eq_card_basis b]
    norm_num
  have hone := rankFour_discrepancy_scalar_eq_one θ₁ θ₂ lam x hactual hlam hlamne
    hinj.self_of_nhds.1 hdim hsmall hcenter
  have hcofactor : θ₂ x (bodyCofactor (θ₁ x).toLinearMap b p₀) =
      θ₁ x (bodyCofactor (θ₁ x).toLinearMap b p₀) := by
    simpa only [hone, one_smul] using hfamily.self_of_nhds p₀ hp₀
  intro u hu
  have heval : bodyEvaluation (θ₁ x).toLinearMap p₀ u = 0 := by
    rw [bodyEvaluation, LinearMap.comp_apply]
    change RB31E2E.Twist.eval (θ₁ x u) p₀ = 0
    rwa [vendor_eval_eq_evaluateTwist]
  obtain ⟨a, ha⟩ := kernel_vector_eq_smul_basisVector
    (bodyEvaluation (θ₁ x).toLinearMap p₀) b hp₀ u heval
  change u = a • bodyCofactor (θ₁ x).toLinearMap b p₀ at ha
  rw [ha, map_smul, map_smul, hcofactor]

/-- The full local rank-four/rank-four merger at any regular pin. The
finite-dimensional tangent space and the original body forms are used
throughout; no image closure, proportionality factor, center, auxiliary
distribution, or chosen pivot is a hypothesis. -/
theorem actual_rankFour_regular_pin_merges [FiniteDimensional ℝ E]
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E) (hdim : Module.finrank ℝ E = 4)
    (p : Vec3) (hsurj : Function.Surjective
      ((evaluateTwist p).comp (θ₁ x).toLinearMap))
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective (θ₁ y) ∧ Function.Injective (θ₂ y))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ q : Vec3,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap q).range ≤ 3) :
    ∀ u : E, evaluateTwist p (θ₁ x u) = 0 → θ₂ x u = θ₁ x u := by
  obtain ⟨b, hp⟩ := exists_bodyBasis_nonzero_minor_at (θ₁ x).toLinearMap hdim p hsurj
  exact actual_rankFour_commonPin_kernel_merges θ₁ θ₂ x b p hp hactual hinj hrank

/-- The rank-three/rank-four case and the rank-four/rank-four case share
this single local endpoint. The second body only has to move nontrivially
in one actual stationary motion at the selected regular pin. -/
theorem actual_rankFour_regular_pin_merges_of_nonzero [FiniteDimensional ℝ E]
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E) (hdim : Module.finrank ℝ E = 4)
    (p : Vec3) (hsurj : Function.Surjective
      ((evaluateTwist p).comp (θ₁ x).toLinearMap))
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective (θ₁ y))
    (hmotion : ∃ v : E, evaluateTwist p (θ₁ x v) = 0 ∧ θ₂ x v ≠ 0)
    (hrank : ∀ᶠ y in 𝓝 x, ∀ q : Vec3,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap q).range ≤ 3) :
    ∀ u : E, evaluateTwist p (θ₁ x u) = 0 → θ₂ x u = θ₁ x u := by
  obtain ⟨b, hp⟩ := exists_bodyBasis_nonzero_minor_at (θ₁ x).toLinearMap hdim p hsurj
  obtain ⟨v, hv, hvmove⟩ := hmotion
  have heval : bodyEvaluation (θ₁ x).toLinearMap p v = 0 := by
    change RB31E2E.Twist.eval (θ₁ x v) p = 0
    rwa [vendor_eval_eq_evaluateTwist]
  obtain ⟨a, ha⟩ := kernel_vector_eq_smul_basisVector
    (bodyEvaluation (θ₁ x).toLinearMap p) b hp v heval
  have hsecond : θ₂ x (bodyCofactor (θ₁ x).toLinearMap b p) ≠ 0 := by
    intro hz
    apply hvmove
    change v = a • bodyCofactor (θ₁ x).toLinearMap b p at ha
    rw [ha, map_smul, hz, smul_zero]
  exact actual_rankFour_commonPin_kernel_merges_of_nonzero θ₁ θ₂ x b p hp hactual hinj
    hsecond hrank

end Papers.Rigidity.Calculus

end
end
end BundleSource0023

section BundleSource0024
/- Source: Papers/RigidityConfigurationLocalForms.lean -/




@[expose] public section

/-!
# Local body forms from the actual grounded graph fiber

The smooth cofactor argument requires actual matrix representations at
each nearby configuration. Those representations are constructed here
from the fixed old body triangles and the genuine length-fiber chart.
The form is independent of the point at which its differentiability is
certified. Its value at the central chart point is the original grounded
bar motion on every vertex of the body.

This module connects the graph motion spaces to the calculus of Proposition 4.1.
-/

namespace Papers.Rigidity.Calculus.GroundedConfiguration

noncomputable section

open Filter Matrix BarJoint BodyMotion
open scoped Topology Classical

variable {V B : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (ground : Fin 3 ↪ V) (p : Placement V 3)
variable (C : SmoothLevelChart (groundedLengthMap G ground) p
  (GroundedBarMotions G ground p))
variable (S : B → Finset V) (hS : ∀ b, G.IsClique (S b : Set V))
variable (f : B → Fin 3 ↪ V) (hf : ∀ b i, f b i ∈ S b)
variable (hp : GeneralPosition.InGeneralPosition p)

/-- The actual triangle construction certifies the same body form at
all nearby chart points. No differential identity is supplied as data. -/
theorem bodyRepresentation_locallyRepresented :
    ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p), ∀ b : B,
      HasLocalTwistRepresentation
        (bodyRepresentation G ground p C S hS f hf hp b).form y := by
  filter_upwards [C.smooth_parametrization.eventually (by simp),
    eventually_eventually_nhds.mpr C.level] with y hySmooth hyLevel
  intro b
  have hq : ContDiffAt ℝ 2 (triangleMap G ground p C f b) y := by
    apply contDiffAt_pi.mpr
    intro i
    exact contDiffAt_pi.mp hySmooth (f b i)
  have hlen : ∀ᶠ z in 𝓝 y, ∀ i j,
      squaredDistance (triangleMap G ground p C f b z) i j =
        squaredDistance (fun i => p (f b i)) i j := by
    filter_upwards [hyLevel] with z hz
    exact triangle_lengths_of_grounded_level G ground p (C.parametrization z) hz (f b)
      (fun i j hij => hS b (hf b i) (hf b j) (fun he => hij ((f b).injective he)))
  exact ⟨triangleTwistRepresentation (fun i => p (f b i))
    (GeneralPosition.InGeneralPosition.triangle p hp (f b))
    (triangleMap G ground p C f b) y hq hlen, rfl⟩

/-- At the original placement the chart tangent is the literal
inclusion of the grounded bar-motion kernel. -/
theorem bodyRepresentation_fit_at_zero
    (b : B) (u : GroundedBarMotions G ground p) (w : V) (hw : w ∈ S b) :
    evaluateTwist (p w)
      ((bodyRepresentation G ground p C S hS f hf hp b).form 0 u) = u.val w := by
  have hv := (bodyRepresentation_velocity G ground p C S hS f hf hp).self_of_nhds
    u b w hw
  rw [C.tangent.hasFDerivAt.fderiv, C.parametrization_zero] at hv
  exact hv.symm

/-- Rank four at the original point gives actual injectivity throughout
a neighborhood, by openness of injective finite-dimensional operators. -/
theorem bodyRepresentation_injective_eventually (b : B)
    (hinj : Function.Injective
      ((bodyRepresentation G ground p C S hS f hf hp b).form 0)) :
    ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p), Function.Injective
      ((bodyRepresentation G ground p C S hS f hf hp b).form y) := by
  exact (bodyRepresentation G ground p C S hS f hf hp b).form_differentiable.continuousAt.eventually
    (ContinuousLinearMap.isOpen_injective.mem_nhds hinj)

/-- The local common-pin conclusion for actual clique bodies in the
grounded graph configuration. The matrix representation and its local
smoothness, and the persistent first-body rank, are all constructed.
The remaining coupled-pin rank premise is the separate graph deletion
rank identity, not a Maurer--Cartan or center-space assumption. -/
theorem actual_grounded_rankFour_pin_merger
    (b₁ b₂ : B) (hdim : Module.finrank ℝ (GroundedBarMotions G ground p) = 4)
    (pin : Vec3)
    (hinj : Function.Injective
      ((bodyRepresentation G ground p C S hS f hf hp b₁).form 0))
    (hsurj : Function.Surjective ((evaluateTwist pin).comp
      ((bodyRepresentation G ground p C S hS f hf hp b₁).form 0).toLinearMap))
    (hmotion : ∃ v : GroundedBarMotions G ground p,
      evaluateTwist pin ((bodyRepresentation G ground p C S hS f hf hp b₁).form 0 v) = 0 ∧
        (bodyRepresentation G ground p C S hS f hf hp b₂).form 0 v ≠ 0)
    (hrank : ∀ᶠ y in 𝓝 (0 : GroundedBarMotions G ground p), ∀ q : Vec3,
      Module.finrank ℝ (CofactorKernel.bodyJointPin
        ((bodyRepresentation G ground p C S hS f hf hp b₁).form y).toLinearMap
        ((bodyRepresentation G ground p C S hS f hf hp b₂).form y).toLinearMap q).range ≤ 3) :
    ∀ u : GroundedBarMotions G ground p,
      evaluateTwist pin ((bodyRepresentation G ground p C S hS f hf hp b₁).form 0 u) = 0 →
        (bodyRepresentation G ground p C S hS f hf hp b₂).form 0 u =
          (bodyRepresentation G ground p C S hS f hf hp b₁).form 0 u := by
  apply actual_rankFour_regular_pin_merges_of_nonzero
    (bodyRepresentation G ground p C S hS f hf hp b₁).form
    (bodyRepresentation G ground p C S hS f hf hp b₂).form
    0 hdim pin hsurj
  · exact (bodyRepresentation_locallyRepresented G ground p C S hS f hf hp).mono
      (fun y hy => ⟨hy b₁, hy b₂⟩)
  · exact bodyRepresentation_injective_eventually G ground p C S hS f hf hp b₁ hinj
  · exact hmotion
  · exact hrank

end

end Papers.Rigidity.Calculus.GroundedConfiguration

end
end BundleSource0024

section BundleSource0025
/- Source: Papers/RigidityPinOpenRank.lean -/



@[expose] public section

/-!
# Propagating common-new-pin bounds from an actual generic neighborhood

A bound on the rank of an affine matrix on a nonempty open set holds
everywhere.  This supplies the generic-new-pin meaning needed in the
graph argument directly from the simultaneous regular-placement open
set.  The old body coordinates are held fixed throughout the argument.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix

theorem AffineRank.rankAt_le_of_on_open
    {P M N : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (A : M →ₗ[ℝ] N) (L : P →ₗ[ℝ] (M →ₗ[ℝ] N))
    (O : Set P) (hO : IsOpen O) (hne : O.Nonempty) (k : ℕ)
    (hbound : ∀ p ∈ O, AffineRank.rankAt A L p ≤ k) :
    ∀ p, AffineRank.rankAt A L p ≤ k := by
  intro p
  have hdense := AffineRank.dense_setOf_rankAt_le A L p
  obtain ⟨q, hq, hqO⟩ := hdense.exists_mem_open hO hne
  exact hq.trans (hbound q hqO)

def pinEvaluationLinearPart (W : Submodule ℝ Twist) :
    Vec3 →ₗ[ℝ] (W →ₗ[ℝ] Vec3) where
  toFun p := (CommonPinLowRank.pointEvaluation p).comp W.subtype
  map_add' p q := by ext X i; simp
  map_smul' a p := by ext X i; simp

theorem restrictEvaluation_eq_affineFamily (W : Submodule ℝ Twist) (p : Vec3) :
    restrictEvaluation W p =
      AffineRank.family (restrictEvaluation W 0) (pinEvaluationLinearPart W) p := by
  ext X i
  simp [restrictEvaluation, AffineRank.family, pinEvaluationLinearPart,
    evaluateTwist_apply]

/-- An actual rank bound in a nonempty generic pin window is the
universal singular-pin condition used by the twist classification. -/
theorem singularPinSpace_of_rank_le_two_on_open (W : Submodule ℝ Twist)
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hbound : ∀ p ∈ O, Module.finrank ℝ (restrictEvaluation W p).range ≤ 2) :
    SingularPinSpace W := by
  have h := AffineRank.rankAt_le_of_on_open
    (restrictEvaluation W 0) (pinEvaluationLinearPart W) O hO hne 2
    (by
      intro p hp
      unfold AffineRank.rankAt
      rw [← restrictEvaluation_eq_affineFamily W p]
      exact hbound p hp)
  intro p
  have hp := h p
  unfold AffineRank.rankAt at hp
  rwa [← restrictEvaluation_eq_affineFamily W p] at hp

/-- The full finite-or-infinite-center alternative follows from the
ordinary real neighborhood, without a supplied generic-point axiom. -/
theorem pin_space_classification_of_open_rank_bound (W : Submodule ℝ Twist)
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hbound : ∀ p ∈ O, Module.finrank ℝ (restrictEvaluation W p).range ≤ 2)
    (hdim : 3 ≤ Module.finrank ℝ W) :
    Module.finrank ℝ W = 3 ∧
      ((∃! a : Vec3, W = finiteCenterSpace a) ∨
        ∃ d : Vec3, d ≠ 0 ∧ W = infiniteCenterSpace d) := by
  have hW := singularPinSpace_of_rank_le_two_on_open W O hO hne hbound
  exact ⟨finrank_eq_three_of_singularPinSpace W hW hdim,
    singularPinSpace_classification W hW hdim⟩

end

end Papers.Rigidity

end
end BundleSource0025

section BundleSource0026
/- Source: Papers/RigidityCommonPinRankBound.lean -/




@[expose] public section

/-!
# Universal common-pin rank from the actual graph deletion loss

The new pin is varied while every surviving graph coordinate stays
fixed. The exact bar-kernel elimination identity gives a rank bound on
a nonempty open set of simultaneous regular placements. Affine-matrix
rank propagation extends it to every real pin. This is the graph-rank
input to the differential merger argument.

The bound applies to the actual common-pin family.
-/

namespace Papers.Rigidity.VertexPin.IncidentTetrahedra

noncomputable section

open BarJoint
open scoped Classical

variable {V B : Type} [Fintype V] [Fintype B] {G : SimpleGraph V} {v : V}

theorem commonPin_rank_le_of_deletionDrop
    (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hpGeneric : IsGenericPlacement p) (hp : T.NoncollinearAt p)
    (ht : T.TransverseAt p) (base : B) (k : ℕ)
    (hdrop : deletionRankDrop G v ≤ k + 3) :
    ∀ q : Vec3, Module.finrank ℝ (T.commonPinAt p hp base q).range ≤ k := by
  obtain ⟨O, hO, hpO, hwindow⟩ := T.exists_open_generic_pin_window p hpGeneric ht
  have hbound (q : Vec3) (hq : q ∈ O) :
      Module.finrank ℝ (T.commonPinAt p hp base q).range ≤ k := by
    have hid := T.rigidityRank_replace_identity p hp q (hwindow q hq).2 base
    have hrG := (hwindow q hq).1 G
    have hrD := generic_deletedPlacement p hpGeneric v (deletedGraph G v)
    rw [hrG, hrD] at hid
    unfold deletionRankDrop at hdrop
    omega
  have hall := AffineRank.rankAt_le_of_on_open
    (P := Vec3) (M := DeletedMotions G p v) (N := B → Vec3)
    (CommonPinLowRank.operator (T.relativeTwists p hp base) 0)
    (CommonPinLowRank.linearPart (T.relativeTwists p hp base))
    O hO ⟨p v, hpO⟩ k (by
      intro q hq
      unfold AffineRank.rankAt
      rw [← CommonPinLowRank.operator_eq_affineFamily (T.relativeTwists p hp base) q]
      change Module.finrank ℝ (T.commonPinAt p hp base q).range ≤ k
      exact hbound q hq)
  intro q
  have hq := hall q
  unfold AffineRank.rankAt at hq
  rw [← CommonPinLowRank.operator_eq_affineFamily (T.relativeTwists p hp base) q] at hq
  change Module.finrank ℝ (T.commonPinAt p hp base q).range ≤ k at hq
  exact hq

theorem commonPin_rank_le_three_of_drop_le_six
    (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hpGeneric : IsGenericPlacement p) (hp : T.NoncollinearAt p)
    (ht : T.TransverseAt p) (base : B) (hdrop : deletionRankDrop G v ≤ 6) :
    ∀ q : Vec3, Module.finrank ℝ (T.commonPinAt p hp base q).range ≤ 3 :=
  T.commonPin_rank_le_of_deletionDrop p hpGeneric hp ht base 3 hdrop

end

end Papers.Rigidity.VertexPin.IncidentTetrahedra

end
end BundleSource0026

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0026/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0026.json"

section BundleSource0027
/- Source: Papers/RigidityGenericPins.lean -/







@[expose] public section

/-!
# Polynomial propagation from a generic new pin

The coefficients of the body twists lie in a field `K` before the new pin is
chosen. Algebraic independence of the three new coordinates is used explicitly;
it is not replaced by an unexplained genericity predicate.
-/

namespace Papers.Rigidity

open Matrix MvPolynomial
open scoped Matrix

variable {K : Type*} [Field K] [Algebra K ℝ]

/-- A twist whose six coordinates belong to the pre-existing coefficient field. -/
abbrev CoefficientTwist (K : Type*) := (Fin 3 → K) × (Fin 3 → K)

def realTwist (X : CoefficientTwist K) : Twist :=
  (fun i => algebraMap K ℝ (X.1 i), fun i => algebraMap K ℝ (X.2 i))

/-- The actual new-pin velocity, as three polynomials in the pin coordinates. -/
noncomputable def pinVelocityPolynomial (X : CoefficientTwist K) : Fin 3 → MvPolynomial (Fin 3) K :=
  (fun i => C (X.2 i)) +
    (fun i => C (X.1 i)) ⨯₃ (fun i => MvPolynomial.X i)

theorem aeval_pinVelocityPolynomial (X : CoefficientTwist K) (p : Vec3) (i : Fin 3) :
    aeval p (pinVelocityPolynomial X i) = evaluateTwist p (realTwist X) i := by
  fin_cases i <;>
    simp [pinVelocityPolynomial, evaluateTwist_apply, realTwist, cross_apply]

/-- The determinant of the three velocities is the polynomial whose vanishing
records dependence of three evaluations. -/
noncomputable def pinDeterminantPolynomial (X Y Z : CoefficientTwist K) : MvPolynomial (Fin 3) K :=
  Matrix.det ![pinVelocityPolynomial X, pinVelocityPolynomial Y, pinVelocityPolynomial Z]

theorem aeval_pinDeterminantPolynomial (X Y Z : CoefficientTwist K) (p : Vec3) :
    aeval p (pinDeterminantPolynomial X Y Z) =
      evaluateTwist p (realTwist X) ⬝ᵥ
        (evaluateTwist p (realTwist Y) ⨯₃ evaluateTwist p (realTwist Z)) := by
  let M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K) :=
    ![pinVelocityPolynomial X, pinVelocityPolynomial Y, pinVelocityPolynomial Z]
  let N : Matrix (Fin 3) (Fin 3) ℝ :=
    ![evaluateTwist p (realTwist X), evaluateTwist p (realTwist Y),
      evaluateTwist p (realTwist Z)]
  have heval : M.map (aeval p) = N := by
    ext i j
    fin_cases i
    · exact aeval_pinVelocityPolynomial X p j
    · exact aeval_pinVelocityPolynomial Y p j
    · exact aeval_pinVelocityPolynomial Z p j
  calc
    aeval p (pinDeterminantPolynomial X Y Z) = (M.map (aeval p)).det :=
      (aeval p).map_det M
    _ = N.det := congrArg Matrix.det heval
    _ = _ := (triple_product_eq_det _ _ _).symm

noncomputable def pinCrossPolynomial (X Y : CoefficientTwist K) : Fin 3 → MvPolynomial (Fin 3) K :=
  pinVelocityPolynomial X ⨯₃ pinVelocityPolynomial Y

theorem aeval_pinCrossPolynomial (X Y : CoefficientTwist K) (p : Vec3) (i : Fin 3) :
    aeval p (pinCrossPolynomial X Y i) =
      (evaluateTwist p (realTwist X) ⨯₃ evaluateTwist p (realTwist Y)) i := by
  fin_cases i <;>
    simp [pinCrossPolynomial, cross_apply, aeval_pinVelocityPolynomial] <;> rfl

theorem cross_product_eq_zero_at_every_pin
    (p : Vec3) (hp : AlgebraicIndependent K p) (X Y : CoefficientTwist K)
    (h : evaluateTwist p (realTwist X) ⨯₃ evaluateTwist p (realTwist Y) = 0) :
    ∀ q : Vec3, evaluateTwist q (realTwist X) ⨯₃ evaluateTwist q (realTwist Y) = 0 := by
  have hz (i : Fin 3) : pinCrossPolynomial X Y i = 0 :=
    hp.eq_zero_of_aeval_eq_zero _
      ((aeval_pinCrossPolynomial X Y p i).trans (congrFun h i))
  intro q
  ext i
  rw [← aeval_pinCrossPolynomial X Y q i, hz i, map_zero, Pi.zero_apply]

/-- Any two independent twists defined before a generic new pin remain
independent when evaluated at that pin. -/
theorem independent_twists_evaluate_independently
    (p : Vec3) (hp : AlgebraicIndependent K p) (X Y : CoefficientTwist K)
    (hXY : LinearIndependent ℝ ![realTwist X, realTwist Y]) :
    LinearIndependent ℝ ![evaluateTwist p (realTwist X), evaluateTwist p (realTwist Y)] := by
  apply crossProduct_ne_zero_iff_linearIndependent.mp
  intro hz
  obtain ⟨q, hq⟩ := exists_pin_separating_independent_twists (realTwist X) (realTwist Y) hXY
  exact hq (cross_product_eq_zero_at_every_pin p hp X Y hz q)

theorem nonzero_twist_evaluates_nonzero
    (p : Vec3) (hp : AlgebraicIndependent K p) (X : CoefficientTwist K)
    (hX : realTwist X ≠ 0) : evaluateTwist p (realTwist X) ≠ 0 := by
  intro hz
  have hpoly (i : Fin 3) : pinVelocityPolynomial X i = 0 :=
    hp.eq_zero_of_aeval_eq_zero _
      ((aeval_pinVelocityPolynomial X p i).trans (congrFun hz i))
  obtain ⟨q, hq⟩ := exists_pin_detecting_nonzero_twist (realTwist X) hX
  apply hq
  ext i
  rw [← aeval_pinVelocityPolynomial X q i, hpoly i, map_zero, Pi.zero_apply]

/-- A rank-drop determinant at an algebraically independent new pin vanishes
identically, so it also vanishes at every real pin. -/
theorem triple_product_eq_zero_at_every_pin
    (p : Vec3) (hp : AlgebraicIndependent K p)
    (X Y Z : CoefficientTwist K)
    (h : evaluateTwist p (realTwist X) ⬝ᵥ
      (evaluateTwist p (realTwist Y) ⨯₃ evaluateTwist p (realTwist Z)) = 0) :
    ∀ q : Vec3, evaluateTwist q (realTwist X) ⬝ᵥ
      (evaluateTwist q (realTwist Y) ⨯₃ evaluateTwist q (realTwist Z)) = 0 := by
  have hz : pinDeterminantPolynomial X Y Z = 0 :=
    hp.eq_zero_of_aeval_eq_zero _ ((aeval_pinDeterminantPolynomial X Y Z p).trans h)
  intro q
  rw [← aeval_pinDeterminantPolynomial X Y Z q, hz, map_zero]

/-- The common-pin determinant identities used after vertex deletion follow
from the actual rank at an independent pin. No identities are assumed. -/
theorem generic_singular_pin_triple_identity
    (W : Submodule ℝ Twist) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hr : Module.finrank ℝ (restrictEvaluation W p).range ≤ 2)
    (X Y Z : CoefficientTwist K)
    (hX : realTwist X ∈ W) (hY : realTwist Y ∈ W) (hZ : realTwist Z ∈ W) :
    ∀ q : Vec3, evaluateTwist q (realTwist X) ⬝ᵥ
      (evaluateTwist q (realTwist Y) ⨯₃ evaluateTwist q (realTwist Z)) = 0 := by
  apply triple_product_eq_zero_at_every_pin p hp
  let E := restrictEvaluation W p
  exact triple_product_eq_zero_of_finrank_le_two E.range hr
    ⟨E ⟨realTwist X, hX⟩, ⟨realTwist X, hX⟩, rfl⟩
    ⟨E ⟨realTwist Y, hY⟩, ⟨realTwist Y, hY⟩, rfl⟩
    ⟨E ⟨realTwist Z, hZ⟩, ⟨realTwist Z, hZ⟩, rfl⟩

/-- Scalar extension of a family of twists defined over the coefficient field. -/
noncomputable def coefficientTwistSpan {I : Type*} (X : I → CoefficientTwist K) : Submodule ℝ Twist :=
  Submodule.span ℝ (Set.range fun i => realTwist (X i))

/-- The small-dimensional assertion of Lemma 3.4, for any basis with at most
two elements defined over the coefficient field: no nonzero motion fixes an
algebraically independent new pin. -/
theorem generic_pin_injective_of_basis_card_le_two
    {n : ℕ} (hn : n ≤ 2) (X : Fin n → CoefficientTwist K)
    (hX : LinearIndependent ℝ (fun i => realTwist (X i)))
    (p : Vec3) (hp : AlgebraicIndependent K p) :
    Function.Injective (restrictEvaluation (coefficientTwistSpan X) p) := by
  have hEval : LinearIndependent ℝ (fun i => evaluateTwist p (realTwist (X i))) := by
    interval_cases n
    · exact linearIndependent_empty_type
    · apply linearIndependent_unique_iff.mpr
      exact nonzero_twist_evaluates_nonzero p hp (X default) (hX.ne_zero default)
    · have hxpair : LinearIndependent ℝ ![realTwist (X 0), realTwist (X 1)] := by
        convert hX using 1
        funext i
        fin_cases i <;> rfl
      have he := independent_twists_evaluate_independently p hp (X 0) (X 1) hxpair
      convert he using 1
      funext i
      fin_cases i <;> rfl
  let b := Module.Basis.span hX
  apply LinearMap.injective_of_linearIndependent b.span_eq
  have hfun : (restrictEvaluation (coefficientTwistSpan X) p ∘ b) =
      (fun i => evaluateTwist p (realTwist (X i))) := by
    funext i
    change evaluateTwist p ((Module.Basis.span hX i : coefficientTwistSpan X) : Twist) = _
    rw [Module.Basis.coe_span_apply]
  exact (congrArg (fun f : Fin n → Vec3 => LinearIndependent ℝ f) hfun).mpr hEval

/-- Every coefficient-defined twist space of dimension at most two evaluates
injectively at a generic new pin. This removes the chosen-basis assumption. -/
theorem generic_pin_injective_of_finrank_le_two {I : Type*}
    (X : I → CoefficientTwist K)
    (hdim : Module.finrank ℝ (coefficientTwistSpan X) ≤ 2)
    (p : Vec3) (hp : AlgebraicIndependent K p) :
    Function.Injective (restrictEvaluation (coefficientTwistSpan X) p) := by
  classical
  obtain ⟨f, hf, hspan, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ
    (Set.range fun i => realTwist (X i))
  choose a ha using hf
  let Y := fun i => X (a i)
  have he : (fun i => realTwist (Y i)) = f := funext ha
  have hY : LinearIndependent ℝ (fun i => realTwist (Y i)) := he.symm ▸ hli
  have hspanY : coefficientTwistSpan Y = coefficientTwistSpan X := by
    unfold coefficientTwistSpan
    rw [he]
    exact hspan
  have hi := generic_pin_injective_of_basis_card_le_two hdim Y hY p hp
  exact (congrArg (fun W : Submodule ℝ Twist =>
    Function.Injective (restrictEvaluation W p)) hspanY).mp hi

theorem triple_product_zero_on_span {I : Type*} (X : I → Twist) (q : Vec3)
    (h : ∀ i j k, evaluateTwist q (X i) ⬝ᵥ
      (evaluateTwist q (X j) ⨯₃ evaluateTwist q (X k)) = 0)
    (A B C : Submodule.span ℝ (Set.range X)) :
    evaluateTwist q A.val ⬝ᵥ
      (evaluateTwist q B.val ⨯₃ evaluateTwist q C.val) = 0 := by
  let E := evaluateTwist q
  have hthird (i j : I) (Z : Submodule.span ℝ (Set.range X)) :
      E (X i) ⬝ᵥ (E (X j) ⨯₃ E Z.val) = 0 := by
    let F : Twist →ₗ[ℝ] ℝ :=
      (dotProductBilin ℝ ℝ (E (X i))).comp ((crossProduct (E (X j))).comp E)
    have hle : Submodule.span ℝ (Set.range X) ≤ F.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact h i j k
    exact hle Z.property
  have hsecond (i : I) (Y Z : Submodule.span ℝ (Set.range X)) :
      E (X i) ⬝ᵥ (E Y.val ⨯₃ E Z.val) = 0 := by
    let F : Twist →ₗ[ℝ] ℝ :=
      (dotProductBilin ℝ ℝ (E (X i))).comp
        (((crossProduct (R := ℝ)).flip (E Z.val)).comp E)
    have hle : Submodule.span ℝ (Set.range X) ≤ F.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hthird i j Z
    exact hle Y.property
  let F : Twist →ₗ[ℝ] ℝ :=
    (dotProductBilin ℝ ℝ (E B.val ⨯₃ E C.val)).comp E
  have hle : Submodule.span ℝ (Set.range X) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (E B.val ⨯₃ E C.val) ⬝ᵥ E (X i) = 0
    simpa only [dotProduct_comm] using hsecond i B C
  have hh : (E B.val ⨯₃ E C.val) ⬝ᵥ E A.val = 0 := hle A.property
  simpa only [dotProduct_comm] using hh

/-- The generic rank-two pin condition is equivalent to a universal pin
condition for twist spaces defined before the independent pin is chosen. -/
theorem singularPinSpace_of_generic_pin {I : Type*}
    (X : I → CoefficientTwist K) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hr : Module.finrank ℝ (restrictEvaluation (coefficientTwistSpan X) p).range ≤ 2) :
    SingularPinSpace (coefficientTwistSpan X) := by
  intro q
  apply finrank_le_two_of_triple_product_eq_zero
  intro x y z
  obtain ⟨A, hA⟩ := x.property
  obtain ⟨B, hB⟩ := y.property
  obtain ⟨C, hC⟩ := z.property
  rw [← hA, ← hB, ← hC]
  apply triple_product_zero_on_span (fun i => realTwist (X i)) q
  intro i j k
  exact generic_singular_pin_triple_identity (coefficientTwistSpan X) p hp hr
    (X i) (X j) (X k)
    (Submodule.subset_span ⟨i, rfl⟩)
    (Submodule.subset_span ⟨j, rfl⟩)
    (Submodule.subset_span ⟨k, rfl⟩) q

/-- Lemma 3.4's principal classification, with algebraic independence made
explicit and all affine finite and infinite centers retained. -/
theorem generic_pin_space_classification {I : Type*}
    (X : I → CoefficientTwist K) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hd : 3 ≤ Module.finrank ℝ (coefficientTwistSpan X))
    (hr : Module.finrank ℝ (restrictEvaluation (coefficientTwistSpan X) p).range ≤ 2) :
    (∃! a : Vec3, coefficientTwistSpan X = finiteCenterSpace a) ∨
      ∃ d : Vec3, d ≠ 0 ∧ coefficientTwistSpan X = infiniteCenterSpace d :=
  singularPinSpace_classification _ (singularPinSpace_of_generic_pin X p hp hr) hd

end Papers.Rigidity

end
end BundleSource0027

section BundleSource0028
/- Source: Papers/RigidityPinRankGap.lean -/



@[expose] public section

/-!
# A noninjective generic pin removes at least two relative degrees of freedom

This consequence of Lemma 3.4 supplies the linear-algebra part of an
alternative proof of the deletion bound `δ(v) ≥ 5`: once one incident
body triangle eliminates the three velocity coordinates of `v`, a pair
of incident bodies that does not merge has a noninjective relative-pin
evaluation.  The actual body/bar elimination identity remains separate.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix

theorem finiteCenterSpace_evaluation_rank (a p : Vec3) (hpa : p ≠ a) :
    Module.finrank ℝ (restrictEvaluation (finiteCenterSpace a) p).range = 2 := by
  have hd : p - a ≠ 0 := sub_ne_zero.mpr hpa
  have hle : (crossProduct (p - a)).range ≤
      (restrictEvaluation (finiteCenterSpace a) p).range := by
    rintro y ⟨w, rfl⟩
    let X : finiteCenterSpace a := ⟨(-w, w ⨯₃ a), by
      change w ⨯₃ a + (-w) ⨯₃ a = 0
      simp⟩
    refine ⟨X, ?_⟩
    ext i
    fin_cases i <;>
      simp [restrictEvaluation, evaluateTwist_apply, X, cross_apply] <;> ring
  apply le_antisymm (finiteCenterSpace_singular a p)
  rw [← finrank_range_crossProduct (p - a) hd]
  exact Submodule.finrank_mono hle

theorem infiniteCenterSpace_evaluation_rank (d : Vec3) (hd : d ≠ 0) (p : Vec3) :
    Module.finrank ℝ (restrictEvaluation (infiniteCenterSpace d) p).range = 2 := by
  have hle : normalPlane d ≤
      (restrictEvaluation (infiniteCenterSpace d) p).range := by
    intro v hv
    let X : infiniteCenterSpace d := ⟨(0, v), by
      constructor
      · simp
      · change v ⬝ᵥ d = 0
        change d ⬝ᵥ v = 0 at hv
        simpa only [dotProduct_comm] using hv⟩
    refine ⟨X, ?_⟩
    simp [X, restrictEvaluation, evaluateTwist_apply]
  apply le_antisymm (infiniteCenterSpace_singular d hd p)
  rw [← finrank_normalPlane d hd]
  exact Submodule.finrank_mono hle

/-- At a generic new pin, a noninjective evaluation can never have rank
zero or one.  This holds for every coefficient-defined twist space. -/
theorem two_le_generic_pin_rank_of_not_injective
    {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hnot : ¬ Function.Injective (restrictEvaluation (coefficientTwistSpan X) p)) :
    2 ≤ Module.finrank ℝ (restrictEvaluation (coefficientTwistSpan X) p).range := by
  by_contra hsmall
  have hrank : Module.finrank ℝ (restrictEvaluation (coefficientTwistSpan X) p).range ≤ 1 := by
    omega
  have hdim : 3 ≤ Module.finrank ℝ (coefficientTwistSpan X) := by
    by_contra hd
    have hd' : Module.finrank ℝ (coefficientTwistSpan X) ≤ 2 := by omega
    exact hnot (generic_pin_injective_of_finrank_le_two X hd' p hp)
  have hgenerator : ∃ i : I, realTwist (X i) ≠ 0 := by
    by_contra hzero
    have hz (i : I) : realTwist (X i) = 0 :=
      not_not.mp (not_exists.mp hzero i)
    have hbot : coefficientTwistSpan X = ⊥ := by
      unfold coefficientTwistSpan
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact hz i
    rw [hbot] at hdim
    simpa using hdim
  rcases generic_pin_space_classification X p hp hdim (by omega) with
    hfinite | ⟨d, hd, hWd⟩
  · obtain ⟨a, hWa, _⟩ := hfinite
    have hpa : p ≠ a := by
      intro heq
      obtain ⟨i, hi⟩ := hgenerator
      apply nonzero_twist_evaluates_nonzero p hp (X i) hi
      have hm : realTwist (X i) ∈ coefficientTwistSpan X :=
        Submodule.subset_span ⟨i, rfl⟩
      rw [hWa] at hm
      change evaluateTwist a (realTwist (X i)) = 0 at hm
      simpa only [heq] using hm
    rw [hWa, finiteCenterSpace_evaluation_rank a p hpa] at hrank
    omega
  · rw [hWd, infiniteCenterSpace_evaluation_rank d hd p] at hrank
    omega

end

end Papers.Rigidity

end
end BundleSource0028

section BundleSource0029
/- Source: Papers/RigidityCenterKernelFamily.lean -/





@[expose] public section

/-!
# Literal stationary families of three-dimensional center spaces

Finite centers use the rotations with angular part `p-c`; infinite
centers use the twists `(d,-d×p)`. The actual evaluation kernel is the
line generated by this displayed vector on its ordinary nonzero chart.
The coupled-pin rank bound therefore forces a second body's stationary
twist to be proportional, by moving the pin along that actual axis.

This module supplies the three-dimensional branch of Proposition 4.1.
No projective chart or image closure is assumed.
-/

namespace Papers.Rigidity.CenterKernelFamily

noncomputable section

open Matrix CofactorKernel
open scoped Matrix

def finiteVector (c p : Vec3) : finiteCenterSpace c := finiteCenterRotations c (p - c)

theorem finiteVector_fixes (c p : Vec3) : evaluateTwist p (finiteVector c p).val = 0 := by
  funext i
  fin_cases i <;> simp [finiteVector, finiteCenterRotations, evaluateTwist_apply, cross_apply] <;> ring

theorem finiteVector_ne_zero (c p : Vec3) (hp : p ≠ c) : (finiteVector c p).val ≠ 0 := by
  intro hz
  have h := congrArg Prod.fst hz
  change p - c = 0 at h
  exact hp (sub_eq_zero.mp h)

theorem finiteVector_kernel (c p : Vec3) (hp : p ≠ c)
    (X : finiteCenterSpace c) (hX : evaluateTwist p X.val = 0) :
    ∃ a : ℝ, X = a • finiteVector c p := by
  have hcenter : X.val.2 + X.val.1 ⨯₃ c = 0 := X.property
  have hpin : X.val.2 + X.val.1 ⨯₃ p = 0 := hX
  have he : X.val.1 ⨯₃ p = X.val.1 ⨯₃ c := add_left_cancel (hpin.trans hcenter.symm)
  have hcross : X.val.1 ⨯₃ (p - c) = 0 := by rw [map_sub, he, sub_self]
  have hspan : X.val.1 ∈ Submodule.span ℝ {p - c} := by
    rw [← ker_crossProduct_eq_span (p - c) (sub_ne_zero.mpr hp)]
    change (p - c) ⨯₃ X.val.1 = 0
    rw [← cross_anticomm X.val.1 (p - c), hcross, neg_zero]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  refine ⟨a, Subtype.ext (Prod.ext ha.symm ?_)⟩
  have ht : X.val.2 = -(X.val.1 ⨯₃ c) := eq_neg_of_add_eq_zero_left hcenter
  change X.val.2 = a • (-((p - c) ⨯₃ c))
  rw [ht, ← ha, map_smul, LinearMap.smul_apply, smul_neg]

def infiniteVector (d p : Vec3) : infiniteCenterSpace d :=
  ⟨(d, -(d ⨯₃ p)), by
    constructor
    · exact cross_self d
    · simp [neg_dotProduct, dotProduct_comm, dot_self_cross]⟩

theorem infiniteVector_fixes (d p : Vec3) : evaluateTwist p (infiniteVector d p).val = 0 := by
  change -(d ⨯₃ p) + d ⨯₃ p = 0
  exact neg_add_cancel _

theorem infiniteVector_ne_zero (d p : Vec3) (hd : d ≠ 0) :
    (infiniteVector d p).val ≠ 0 := by
  intro hz
  exact hd (congrArg Prod.fst hz)

theorem infiniteVector_kernel (d p : Vec3) (hd : d ≠ 0)
    (X : infiniteCenterSpace d) (hX : evaluateTwist p X.val = 0) :
    ∃ a : ℝ, X = a • infiniteVector d p := by
  have hspan : X.val.1 ∈ Submodule.span ℝ {d} := by
    rw [← ker_crossProduct_eq_span d hd]
    change d ⨯₃ X.val.1 = 0
    rw [← cross_anticomm X.val.1 d, X.property.1, neg_zero]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  refine ⟨a, Subtype.ext (Prod.ext ha.symm ?_)⟩
  have ht : X.val.2 = -(X.val.1 ⨯₃ p) := eq_neg_of_add_eq_zero_left hX
  change X.val.2 = a • (-(d ⨯₃ p))
  rw [ht, ← ha, map_smul, LinearMap.smul_apply, smul_neg]

theorem joint_kernel_eq_first_of_rank_two
    (W : Submodule ℝ Twist) (T : W →ₗ[ℝ] Twist) (p : Vec3)
    (hfirst : Module.finrank ℝ (restrictEvaluation W p).range = 2)
    (hjoint : Module.finrank ℝ (jointPinOperator W T p).range ≤ 2) :
    (jointPinOperator W T p).ker = (restrictEvaluation W p).ker := by
  have hle : (jointPinOperator W T p).ker ≤ (restrictEvaluation W p).ker := by
    intro X hX
    exact congrArg Prod.fst (show jointPinOperator W T p X = 0 from hX)
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := Vec3 × Vec3)
    (jointPinOperator W T p)
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := Vec3)
    (restrictEvaluation W p)
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

theorem second_fixes_of_joint_rank_two
    (W : Submodule ℝ Twist) (T : W →ₗ[ℝ] Twist) (p : Vec3)
    (hfirst : Module.finrank ℝ (restrictEvaluation W p).range = 2)
    (hjoint : Module.finrank ℝ (jointPinOperator W T p).range ≤ 2)
    (X : W) (hX : evaluateTwist p X.val = 0) : evaluateTwist p (T X) = 0 := by
  have hk := joint_kernel_eq_first_of_rank_two W T p hfirst hjoint
  have hmem : X ∈ (jointPinOperator W T p).ker := by
    rw [hk]
    exact hX
  exact congrArg Prod.snd (show jointPinOperator W T p X = 0 from hmem)

/-- Actual common-pin rank two gives pointwise proportionality on the
finite-center family, with a single ordinary affine coordinate chart. -/
theorem finite_pointwise_eigenvector (c : Vec3)
    (T : finiteCenterSpace c →ₗ[ℝ] Twist)
    (hrank : ∀ p, Module.finrank ℝ (jointPinOperator (finiteCenterSpace c) T p).range ≤ 2)
    (p : Vec3) (hp : p 0 - c 0 ≠ 0) :
    ∃ a : ℝ, T (finiteVector c p) = a • (finiteVector c p).val := by
  have hne (q : Vec3) (hq : q 0 - c 0 ≠ 0) : q ≠ c := by
    intro he
    exact hq (by rw [he, sub_self])
  apply common_pin_map_is_eigenvector (finiteCenterSpace c) T
    (fun q => q 0 - c 0) ((continuous_apply 0).sub continuous_const) (finiteVector c)
    (fun q => by rw [vendor_eval_eq_evaluateTwist]; exact finiteVector_fixes c q)
    (fun q hq => finiteVector_ne_zero c q (hne q hq))
    (fun q hq X hX => finiteVector_kernel c q (hne q hq) X
      (by rwa [vendor_eval_eq_evaluateTwist] at hX))
    (fun q hq => by
      rw [vendor_eval_eq_evaluateTwist]
      exact second_fixes_of_joint_rank_two (finiteCenterSpace c) T q
        (finiteCenterSpace_evaluation_rank c q (hne q hq)) (hrank q)
        (finiteVector c q) (finiteVector_fixes c q)) p hp

/-- The infinite-center family has a nonzero angular part at every pin. -/
theorem infinite_pointwise_eigenvector (d : Vec3) (hd : d ≠ 0)
    (T : infiniteCenterSpace d →ₗ[ℝ] Twist)
    (hrank : ∀ p, Module.finrank ℝ (jointPinOperator (infiniteCenterSpace d) T p).range ≤ 2)
    (p : Vec3) : ∃ a : ℝ, T (infiniteVector d p) = a • (infiniteVector d p).val := by
  apply common_pin_map_is_eigenvector (infiniteCenterSpace d) T (fun _ => 1) continuous_const
    (infiniteVector d)
    (fun q => by rw [vendor_eval_eq_evaluateTwist]; exact infiniteVector_fixes d q)
    (fun q _ => infiniteVector_ne_zero d q hd)
    (fun q _ X hX => infiniteVector_kernel d q hd X
      (by rwa [vendor_eval_eq_evaluateTwist] at hX))
    (fun q _ => by
      rw [vendor_eval_eq_evaluateTwist]
      exact second_fixes_of_joint_rank_two (infiniteCenterSpace d) T q
        (infiniteCenterSpace_evaluation_rank d hd q) (hrank q)
        (infiniteVector d q) (infiniteVector_fixes d q)) p one_ne_zero

end

end Papers.Rigidity.CenterKernelFamily

end
end BundleSource0029

section BundleSource0030
/- Source: Papers/RigidityCenterKernelScalar.lean -/




@[expose] public section

/-!
# One scalar on a rank-three center space

The displayed finite- and infinite-center stationary families have
polynomial coordinates. Pointwise proportionality from the common-pin
rank bound therefore has one scalar on their actual linear span. A
nonzero stationary family on an open set of pins spans at least three
dimensions; here it spans the whole center space.

The dimension-three configuration calculation retains centers at infinity
without an additional finite-chart hypothesis.
-/

namespace Papers.Rigidity.CenterKernelFamily

noncomputable section

open Matrix CofactorKernel PolynomialImageSpan
open scoped Matrix

def twistCoordinates : Twist ≃ₗ[ℝ] ((Fin 3 ⊕ Fin 3) → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) ℝ ℝ).symm

theorem stationary_family_span_eq_top
    (W : Submodule ℝ Twist) (hW : Module.finrank ℝ W = 3)
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty) (C : Vec3 → W)
    (hCne : ∀ p ∈ O, (C p).val ≠ 0)
    (hCfix : ∀ p ∈ O, evaluateTwist p (C p).val = 0) :
    Submodule.span ℝ (Set.range (fun p : O => C p.val)) = ⊤ := by
  let K := Submodule.span ℝ (Set.range (fun p : O => C p.val))
  let H := K.map W.subtype
  have hlower : 3 ≤ Module.finrank ℝ H := by
    apply CommonPinLowRank.three_le_finrank_of_stationary_family_on_open H O hO hne
    intro p hp
    let X : H := ⟨(C p).val, C p, Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩, rfl⟩
    refine ⟨X, ?_, hCfix p hp⟩
    intro hz
    exact hCne p hp (congrArg Subtype.val hz)
  have hdim : Module.finrank ℝ K = Module.finrank ℝ H :=
    (Submodule.equivMapOfInjective W.subtype Subtype.val_injective K).finrank_eq
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank ℝ K = Module.finrank ℝ W
  apply Nat.le_antisymm (Submodule.finrank_le K)
  calc
    Module.finrank ℝ W = 3 := hW
    _ ≤ Module.finrank ℝ H := hlower
    _ = Module.finrank ℝ K := hdim.symm

theorem scalar_on_polynomial_twist_family
    (W : Submodule ℝ Twist) (T : W →ₗ[ℝ] Twist)
    (D : PinPolynomial) (hD : D ≠ 0)
    (P : (Fin 3 ⊕ Fin 3) → PinPolynomial) (C : Vec3 → W)
    (hcoordinates : ∀ p, evaluationVector P p = twistCoordinates (C p).val)
    (heigen : ∀ p, MvPolynomial.eval p D ≠ 0 →
      ∃ a : ℝ, T (C p) = a • (C p).val) :
    ∃ a : ℝ, ∀ X ∈ Submodule.span ℝ
      (Set.range (fun p : {p : Vec3 // MvPolynomial.eval p D ≠ 0} => C p.val)),
      T X = a • X.val := by
  obtain ⟨R, hR⟩ := LinearMap.exists_extend T
  have hRval (X : W) : R X.val = T X :=
    congrArg (fun A : W →ₗ[ℝ] Twist => A X) hR
  let A : ((Fin 3 ⊕ Fin 3) → ℝ) →ₗ[ℝ] ((Fin 3 ⊕ Fin 3) → ℝ) :=
    twistCoordinates.toLinearMap.comp (R.comp twistCoordinates.symm.toLinearMap)
  obtain ⟨a, ha⟩ := scalar_on_span_of_polynomial_eigenvectors D hD P A (by
    intro p hp
    obtain ⟨c, hc⟩ := heigen p hp
    refine ⟨c, ?_⟩
    rw [hcoordinates]
    change twistCoordinates (R (twistCoordinates.symm (twistCoordinates (C p).val))) = _
    rw [twistCoordinates.symm_apply_apply, hRval, hc, map_smul])
  have hfamily (p : Vec3) (hp : MvPolynomial.eval p D ≠ 0) :
      T (C p) = a • (C p).val := by
    have hh := ha (evaluationVector P p) (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)
    rw [hcoordinates] at hh
    apply twistCoordinates.injective
    rw [map_smul]
    change twistCoordinates (R (twistCoordinates.symm (twistCoordinates (C p).val))) = _ at hh
    rw [twistCoordinates.symm_apply_apply, hRval] at hh
    exact hh
  refine ⟨a, ?_⟩
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨p, rfl⟩ := hX
    exact hfamily p.val p.property
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, smul_zero]
  | add X Y hX hY ihX ihY =>
    rw [map_add, ihX, ihY, AddSubmonoid.coe_add, smul_add]
  | smul c X hX ih =>
    rw [map_smul, ih, SetLike.val_smul, smul_comm]

def finitePolynomials (c : Vec3) : (Fin 3 ⊕ Fin 3) → PinPolynomial
  | .inl i => MvPolynomial.X i - MvPolynomial.C (c i)
  | .inr i => -RB31E2E.Vec3.cross
      (fun j => MvPolynomial.X j - MvPolynomial.C (c j))
      (fun j => MvPolynomial.C (c j)) i

theorem finitePolynomials_eval (c p : Vec3) :
    evaluationVector (finitePolynomials c) p = twistCoordinates (finiteVector c p).val := by
  funext j
  cases j with
  | inl i => simp [evaluationVector, finitePolynomials, twistCoordinates,
      finiteVector, finiteCenterRotations]
  | inr i =>
    fin_cases i <;> simp [evaluationVector, finitePolynomials, twistCoordinates,
      finiteVector, finiteCenterRotations, RB31E2E.Vec3.cross, cross_apply] <;> ring

def infinitePolynomials (d : Vec3) : (Fin 3 ⊕ Fin 3) → PinPolynomial
  | .inl i => MvPolynomial.C (d i)
  | .inr i => -RB31E2E.Vec3.cross (fun j => MvPolynomial.C (d j)) MvPolynomial.X i

theorem infinitePolynomials_eval (d p : Vec3) :
    evaluationVector (infinitePolynomials d) p = twistCoordinates (infiniteVector d p).val := by
  funext j
  cases j with
  | inl i => simp [evaluationVector, infinitePolynomials, twistCoordinates, infiniteVector]
  | inr i =>
    fin_cases i <;> simp [evaluationVector, infinitePolynomials, twistCoordinates,
      infiniteVector, RB31E2E.Vec3.cross, cross_apply]

theorem finite_scalar_of_joint_rank_two (c : Vec3)
    (T : finiteCenterSpace c →ₗ[ℝ] Twist)
    (hrank : ∀ p, Module.finrank ℝ (jointPinOperator (finiteCenterSpace c) T p).range ≤ 2) :
    ∃ a : ℝ, ∀ X : finiteCenterSpace c, T X = a • X.val := by
  let D : PinPolynomial := MvPolynomial.X (0 : Fin 3) - MvPolynomial.C (c 0)
  let O : Set Vec3 := {p | MvPolynomial.eval p D ≠ 0}
  have hO : IsOpen O := by
    have hc : Continuous (fun p : Vec3 => p 0 - c 0) :=
      (continuous_apply (0 : Fin 3)).sub continuous_const
    have ho : IsOpen {p : Vec3 | p 0 - c 0 ≠ 0} :=
      isOpen_ne_fun hc continuous_const
    simpa only [O, D, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] using ho
  have hne : O.Nonempty := by
    refine ⟨fun i => c i + 1, ?_⟩
    simp [O, D]
  have hD : D ≠ 0 := by
    intro hz
    obtain ⟨p, hp⟩ := hne
    exact hp (by rw [hz, map_zero])
  obtain ⟨a, ha⟩ := scalar_on_polynomial_twist_family (finiteCenterSpace c) T D hD
    (finitePolynomials c) (finiteVector c) (finitePolynomials_eval c)
    (by intro p hp; exact finite_pointwise_eigenvector c T hrank p (by simpa [D] using hp))
  have hspan := stationary_family_span_eq_top (finiteCenterSpace c)
    (finrank_finiteCenterSpace c) O hO hne (finiteVector c)
    (by
      intro p hp
      apply finiteVector_ne_zero c p
      intro he
      subst p
      simpa [O, D] using hp)
    (fun p _ => finiteVector_fixes c p)
  refine ⟨a, fun X => ha X ?_⟩
  exact hspan.ge (Submodule.mem_top)

theorem infinite_scalar_of_joint_rank_two (d : Vec3) (hd : d ≠ 0)
    (T : infiniteCenterSpace d →ₗ[ℝ] Twist)
    (hrank : ∀ p, Module.finrank ℝ (jointPinOperator (infiniteCenterSpace d) T p).range ≤ 2) :
    ∃ a : ℝ, ∀ X : infiniteCenterSpace d, T X = a • X.val := by
  let D : PinPolynomial := 1
  let O : Set Vec3 := {p | MvPolynomial.eval p D ≠ 0}
  have hO : IsOpen O := by simp [O, D]
  have hne : O.Nonempty := by simp [O, D]
  obtain ⟨a, ha⟩ := scalar_on_polynomial_twist_family (infiniteCenterSpace d) T D one_ne_zero
    (infinitePolynomials d) (infiniteVector d) (infinitePolynomials_eval d)
    (fun p _ => infinite_pointwise_eigenvector d hd T hrank p)
  have hspan := stationary_family_span_eq_top (infiniteCenterSpace d)
    (finrank_infiniteCenterSpace d hd) O hO hne (infiniteVector d)
    (fun p _ => infiniteVector_ne_zero d p hd) (fun p _ => infiniteVector_fixes d p)
  refine ⟨a, fun X => ha X ?_⟩
  exact hspan.ge (Submodule.mem_top)

/-- Both center types have the same scalar conclusion, stated in the
original twist space and without assuming a finite projective chart. -/
theorem center_scalar_of_joint_rank_two (W : Submodule ℝ Twist)
    (hW : SingularPinSpace W) (hdim : 3 ≤ Module.finrank ℝ W)
    (T : W →ₗ[ℝ] Twist)
    (hrank : ∀ p, Module.finrank ℝ (jointPinOperator W T p).range ≤ 2) :
    ∃ a : ℝ, ∀ X : W, T X = a • X.val := by
  rcases singularPinSpace_classification W hW hdim with ⟨c, hc, _⟩ | ⟨d, hd, hWd⟩
  · subst W
    exact finite_scalar_of_joint_rank_two c T hrank
  · subst W
    exact infinite_scalar_of_joint_rank_two d hd T hrank

end

end Papers.Rigidity.CenterKernelFamily

end
end BundleSource0030

section BundleSource0031
/- Source: Papers/RigiditySmoothScalar.lean -/



@[expose] public section

/-!
# A differentiable factor from pointwise scalar proportionality

An algebraic pointwise classification only gives existence of a scalar.
The scalar used in Maurer--Cartan must also be differentiable. Here it is
constructed as an actual coordinate quotient on a neighborhood where its
denominator remains nonzero.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix
open scoped Topology Matrix

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem differentiable_scalar_of_pointwise_proportional
    (θ₁ θ₂ : E → (E →L[ℝ] F)) (x u₀ : E) (ℓ : F →L[ℝ] ℝ)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hθ₂ : DifferentiableAt ℝ θ₂ x)
    (hne : ℓ (θ₁ x u₀) ≠ 0)
    (hprop : ∀ᶠ y in 𝓝 x, ∃ c : ℝ, c ≠ 0 ∧ ∀ u, θ₂ y u = c • θ₁ y u) :
    ∃ lam : E → ℝ, DifferentiableAt ℝ lam x ∧ lam x ≠ 0 ∧
      ∀ᶠ y in 𝓝 x, ∀ u, θ₂ y u = lam y • θ₁ y u := by
  let f₁ : E → ℝ := fun y => ℓ (θ₁ y u₀)
  let f₂ : E → ℝ := fun y => ℓ (θ₂ y u₀)
  let lam : E → ℝ := fun y => f₂ y / f₁ y
  have hf₁ : DifferentiableAt ℝ f₁ x :=
    ℓ.differentiableAt.comp x (hθ₁.clm_apply (differentiableAt_const u₀))
  have hf₂ : DifferentiableAt ℝ f₂ x :=
    ℓ.differentiableAt.comp x (hθ₂.clm_apply (differentiableAt_const u₀))
  have hfne : f₁ x ≠ 0 := hne
  have hnear : ∀ᶠ y in 𝓝 x, lam y ≠ 0 ∧ ∀ u, θ₂ y u = lam y • θ₁ y u := by
    filter_upwards [hf₁.continuousAt.eventually_ne hfne, hprop] with y hy hprop_y
    obtain ⟨c, hc, hθ⟩ := hprop_y
    have hf : f₂ y = c * f₁ y := by
      dsimp [f₂, f₁]
      rw [hθ u₀, map_smul, smul_eq_mul]
    have hlam : lam y = c := by
      dsimp [lam]
      rw [hf, mul_div_cancel_right₀ _ hy]
    exact ⟨by simpa [hlam] using hc, by simpa [hlam] using hθ⟩
  have hprod : DifferentiableAt ℝ (fun y => f₂ y * (f₁ y)⁻¹) x :=
    hf₂.mul (hf₁.inv hfne)
  have hquot : DifferentiableAt ℝ lam x := by
    simpa only [lam, div_eq_mul_inv] using hprod
  exact ⟨lam, hquot, hnear.self_of_nhds.1,
    hnear.mono fun _ hy => hy.2⟩

/-- Algebraically proportional spherical body forms must actually agree.
The differentiable scalar required by Lemma 4.3 is obtained from an
explicit nonvanishing angular coordinate. -/
theorem actual_spherical_forms_equal
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (hprop : ∀ᶠ y in 𝓝 x, ∃ c : ℝ, c ≠ 0 ∧
      ∀ u, A₂.form y u = c • A₁.form y u)
    (e : Vec3 →ₗ[ℝ] E) (heang : ∀ u, (A₁.form x (e u)).1 = u) :
    A₂.form x = A₁.form x := by
  let u₀ := e ![1, 0, 0]
  let ℓ : Twist →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 3)).comp (ContinuousLinearMap.fst ℝ Vec3 Vec3)
  have hne : ℓ (A₁.form x u₀) ≠ 0 := by
    change (A₁.form x (e ![1, 0, 0])).1 0 ≠ 0
    rw [heang]
    norm_num
  obtain ⟨lam, hlam, hlamne, hrel⟩ := differentiable_scalar_of_pointwise_proportional
    A₁.form A₂.form x u₀ ℓ A₁.form_differentiable A₂.form_differentiable hne hprop
  have hone := proportional_spherical_forms_eq_one A₁ A₂ lam hlam hrel e heang hlamne
  apply ContinuousLinearMap.ext
  intro u
  simpa [hone] using hrel.self_of_nhds u

end Papers.Rigidity.Calculus

end
end
end BundleSource0031

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0031/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0031.json"

section BundleSource0032
/- Source: Papers/RigidityRankThreeMerger.lean -/





@[expose] public section

/-!
# The full three-dimensional configuration merger

If two actual body projections on a three-dimensional configuration
chart are injective, the common-pin rank bound makes their entire forms
pointwise proportional. A coordinate quotient supplies the smooth
scalar. The finite- or infinite-center Maurer--Cartan obstruction then
forces equality. The argument uses actual stationary families and
retains both projective center types without a chart hypothesis.

The merger argument supplies the `δ(u)=5` branch of Proposition 4.1.
-/

namespace Papers.Rigidity

noncomputable section

open CofactorKernel CenterKernelFamily

theorem first_jointPin_rank_le (W : Submodule ℝ Twist) (T : W →ₗ[ℝ] Twist) (p : Vec3) :
    Module.finrank ℝ (restrictEvaluation W p).range ≤
      Module.finrank ℝ (jointPinOperator W T p).range := by
  have he : (LinearMap.fst ℝ Vec3 Vec3).comp (jointPinOperator W T p) =
      restrictEvaluation W p := by
    apply LinearMap.ext
    intro X
    rfl
  have h := Submodule.finrank_map_le (LinearMap.fst ℝ Vec3 Vec3)
    (jointPinOperator W T p).range
  rw [← LinearMap.range_comp, he] at h
  exact h

/-- A rank-three first-body image is a literal singular center space
when the actual joint-pin operator has rank at most two everywhere. -/
theorem rankThree_bodyForms_scalar
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A B : E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 3)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hrank : ∀ p, Module.finrank ℝ (bodyJointPin A B p).range ≤ 2) :
    SingularPinSpace A.range ∧ ∃ a : ℝ, a ≠ 0 ∧ ∀ u, B u = a • A u := by
  let W := A.range
  let e : E ≃ₗ[ℝ] W := LinearEquiv.ofInjective A hA
  let T : W →ₗ[ℝ] Twist := B.comp e.symm.toLinearMap
  have hjoint (p : Vec3) :
      (jointPinOperator W T p).comp e.toLinearMap = bodyJointPin A B p := by
    apply LinearMap.ext
    intro u
    apply Prod.ext
    · rfl
    · change evaluateTwist p (B (e.symm (e u))) = evaluateTwist p (B u)
      rw [e.symm_apply_apply]
  have hbound (p : Vec3) : Module.finrank ℝ (jointPinOperator W T p).range ≤ 2 := by
    rw [← LinearMap.range_comp_of_range_eq_top (jointPinOperator W T p) e.range, hjoint]
    exact hrank p
  have hsingular : SingularPinSpace W := fun p =>
    (first_jointPin_rank_le W T p).trans (hbound p)
  have hW : Module.finrank ℝ W = 3 := by
    rw [← e.finrank_eq]
    exact hdim
  obtain ⟨a, ha⟩ := center_scalar_of_joint_rank_two W hsingular hW.ge T hbound
  have hscalar (u : E) : B u = a • A u := by
    have h := ha (e u)
    change B (e.symm (e u)) = a • A u at h
    simpa only [e.symm_apply_apply] using h
  have hane : a ≠ 0 := by
    intro hz
    have hzero : B = 0 := by
      apply LinearMap.ext
      intro u
      change B u = 0
      simpa only [hz, zero_smul] using hscalar u
    have hBdim := LinearMap.finrank_range_of_inj hB
    rw [hzero, LinearMap.range_zero, finrank_bot, hdim] at hBdim
    omega
  exact ⟨hsingular, a, hane, hscalar⟩

namespace Calculus

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The entire actual body forms agree in a three-dimensional chart.
All proportionality, center selection, and scalar differentiability
have been derived from the actual coupled-pin rank condition. -/
theorem actual_rankThree_body_forms_equal
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E) (hdim : Module.finrank ℝ E = 3)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hinj₁ : Function.Injective (θ₁ x)) (hinj₂ : Function.Injective (θ₂ x))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 2) :
    θ₂ x = θ₁ x := by
  obtain ⟨A₁, hA₁⟩ := hactual.self_of_nhds.1
  obtain ⟨A₂, hA₂⟩ := hactual.self_of_nhds.2
  have hd₁ : DifferentiableAt ℝ θ₁ x := by simpa only [hA₁] using A₁.form_differentiable
  have hd₂ : DifferentiableAt ℝ θ₂ x := by simpa only [hA₂] using A₂.form_differentiable
  have hi₁ : ∀ᶠ y in 𝓝 x, Function.Injective (θ₁ y) :=
    hd₁.continuousAt.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hinj₁)
  have hi₂ : ∀ᶠ y in 𝓝 x, Function.Injective (θ₂ y) :=
    hd₂.continuousAt.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hinj₂)
  have hprop : ∀ᶠ y in 𝓝 x, ∃ a : ℝ, a ≠ 0 ∧ ∀ u, θ₂ y u = a • θ₁ y u := by
    filter_upwards [hi₁, hi₂, hrank] with y hy₁ hy₂ hyrank
    exact (rankThree_bodyForms_scalar (θ₁ y).toLinearMap (θ₂ y).toLinearMap
      hdim hy₁ hy₂ hyrank).2
  have hpositive : 0 < Module.finrank ℝ E := by omega
  obtain ⟨u₀, hu₀⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := E)).mp hpositive
  have hvalue : θ₁ x u₀ ≠ 0 := by
    intro hz
    exact hu₀ (hinj₁ (by simpa only [map_zero] using hz))
  obtain ⟨ℓ, hℓ⟩ := exists_twist_functional_ne_zero (θ₁ x u₀) hvalue
  obtain ⟨lam, hlam, hlamne, hrel⟩ := differentiable_scalar_of_pointwise_proportional
    θ₁ θ₂ x u₀ ℓ hd₁ hd₂ hℓ hprop
  have hrep : ∀ᶠ y in 𝓝 x, ∀ u, A₂.form y u = lam y • A₁.form y u := by
    simpa only [hA₁, hA₂] using hrel
  let W := (θ₁ x).toLinearMap.range
  have hW : Module.finrank ℝ W = 3 := by
    rw [LinearMap.finrank_range_of_inj hinj₁]
    exact hdim
  have hsingular : SingularPinSpace W :=
    (rankThree_bodyForms_scalar (θ₁ x).toLinearMap (θ₂ x).toLinearMap hdim hinj₁ hinj₂
      hrank.self_of_nhds).1
  have hone : lam x = 1 := by
    rcases singularPinSpace_classification W hsingular hW.ge with
      ⟨c, hc, _⟩ | ⟨d, hd, hWd⟩
    · have hle : finiteCenterSpace c ≤ (θ₁ x).toLinearMap.range := by
        change finiteCenterSpace c ≤ W
        rw [hc]
      obtain ⟨s, hs⟩ := exists_linear_lift_of_le_range (θ₁ x).toLinearMap
        (finiteCenterSpace c) hle
      let e : Vec3 →ₗ[ℝ] E := s.comp (finiteCenterRotations c)
      apply proportional_spherical_forms_eq_one A₁ A₂ lam hlam hrep e
      · intro u
        rw [hA₁]
        exact congrArg Prod.fst (hs (finiteCenterRotations c u))
      · exact hlamne
    · have hle : infiniteCenterSpace d ≤ (θ₁ x).toLinearMap.range := by
        change infiniteCenterSpace d ≤ W
        rw [hWd]
      obtain ⟨s, hs⟩ := exists_linear_lift_of_le_range (θ₁ x).toLinearMap
        (infiniteCenterSpace d) hle
      apply proportional_infiniteCenter_distribution_eq_one A₁ A₂ lam (fun _ => 0)
        (fun _ => 0) hlam (differentiableAt_const (0 : E →L[ℝ] ℝ)) (differentiableAt_const (0 : Twist))
        (by simpa only [ContinuousLinearMap.zero_apply, zero_smul, add_zero] using hrep)
        d hd s (by simp)
      · intro X
        rw [hA₁]
        exact hs X
      · exact hlamne
  apply ContinuousLinearMap.ext
  intro u
  simpa only [hone, one_smul] using hrel.self_of_nhds u

end Calculus

end

end Papers.Rigidity

end
end BundleSource0032

section BundleSource0033
/- Source: Papers/RigidityDeletedConfiguration.lean -/





@[expose] public section

/-!
# The deletion-rank bound on actual grounded configuration forms

An old configuration is restored to the full vertex set by retaining the
deleted vertex at its original position. Genericity is open, so this
restored placement stays generic along a neighborhood of the actual
grounded length fiber. The exact deletion identity then bounds all
common-pin operators there.

The differential triangle forms are identified with the twists extracted
from actual bar motions. Grounding removes the reference form, and the
two-body operator factors through the full common-pin operator. Hence
the coupled rank bound needed in the smooth cofactor proof is a theorem
of the graph's deletion loss, with no extra rank hypothesis.

The deleted-configuration charts supply the local data for Proposition 4.1.
-/

namespace Papers.Rigidity.VertexPin

noncomputable section

open BarJoint Calculus Calculus.GroundedConfiguration Matrix Filter
open scoped Classical Topology

variable {V B : Type} [Fintype V] [Fintype B]

def restoreDeletedPlacement (v : V) (pin : Vec3)
    (q : Placement (DeletedVertex v) 3) : Placement V 3 :=
  fun w => if hw : w = v then pin else q ⟨w, hw⟩

@[simp] theorem restoreDeletedPlacement_other (v : V) (pin : Vec3)
    (q : Placement (DeletedVertex v) 3) (w : DeletedVertex v) :
    restoreDeletedPlacement v pin q w.val = q w := by
  simp [restoreDeletedPlacement, w.property]

@[simp] theorem deletedPlacement_restore (v : V) (pin : Vec3)
    (q : Placement (DeletedVertex v) 3) :
    deletedPlacement (restoreDeletedPlacement v pin q) v = q := by
  funext w
  exact restoreDeletedPlacement_other v pin q w

@[simp] theorem restore_deletedPlacement (p : Placement V 3) (v : V) :
    restoreDeletedPlacement v (p v) (deletedPlacement p v) = p := by
  funext w
  by_cases hw : w = v <;> simp [restoreDeletedPlacement, deletedPlacement, hw]

theorem continuous_restoreDeletedPlacement (v : V) (pin : Vec3) :
    Continuous (restoreDeletedPlacement v pin) := by
  apply continuous_pi
  intro w
  by_cases hw : w = v
  · simpa [restoreDeletedPlacement, hw] using
      (continuous_const : Continuous (fun _ : Placement (DeletedVertex v) 3 => pin))
  · simpa [restoreDeletedPlacement, hw] using
      (continuous_apply (⟨w, hw⟩ : DeletedVertex v))

namespace IncidentTetrahedra

variable {G : SimpleGraph V} {v : V}

def triangleEmbedding (T : IncidentTetrahedra G v B) (b : B) : Fin 3 ↪ DeletedVertex v :=
  ⟨T.triangle b, T.injective b⟩

def triangleVertices (T : IncidentTetrahedra G v B) (b : B) : Finset (DeletedVertex v) :=
  Finset.univ.image (T.triangle b)

theorem triangleVertices_clique (T : IncidentTetrahedra G v B) (b : B) :
    (deletedGraph G v).IsClique (T.triangleVertices b : Set (DeletedVertex v)) := by
  intro w hw z hz hij
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
  exact T.clique b i j (fun h => hij (congrArg (T.triangle b) h))

theorem triangleEmbedding_mem (T : IncidentTetrahedra G v B) (b : B) (i : Fin 3) :
    T.triangleEmbedding b i ∈ T.triangleVertices b :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

def deletedGeneralPosition (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) : GeneralPosition.InGeneralPosition (deletedPlacement p v) :=
  GeneralPosition.InGeneralPosition.comp_embedding p hp ⟨Subtype.val, Subtype.val_injective⟩

variable (T : IncidentTetrahedra G v B) (p : Placement V 3)
variable (hp : GeneralPosition.InGeneralPosition p) (base : B)

abbrev IncidentGroundedMotions := GroundedBarMotions (deletedGraph G v)
  (T.triangleEmbedding base) (deletedPlacement p v)

variable (C : SmoothLevelChart
  (groundedLengthMap (deletedGraph G v) (T.triangleEmbedding base))
  (deletedPlacement p v) (T.IncidentGroundedMotions p base))

def incidentBodyRepresentation (b : B) :
    LocalTwistRepresentation (0 : T.IncidentGroundedMotions p base) :=
  bodyRepresentation (deletedGraph G v) (T.triangleEmbedding base) (deletedPlacement p v) C
    T.triangleVertices T.triangleVertices_clique T.triangleEmbedding T.triangleEmbedding_mem
    (deletedGeneralPosition p hp v) b

/-- Actual local representations of all incident forms are provided
uniformly on the original grounded configuration chart. -/
theorem incidentBodyRepresentation_locallyRepresented :
    ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base), ∀ b : B,
      HasLocalTwistRepresentation (T.incidentBodyRepresentation p hp base C b).form y :=
  bodyRepresentation_locallyRepresented (deletedGraph G v) (T.triangleEmbedding base)
    (deletedPlacement p v) C T.triangleVertices T.triangleVertices_clique T.triangleEmbedding
    T.triangleEmbedding_mem (deletedGeneralPosition p hp v)

/-- The literal two-body rank bound follows from `δ(v) ≤ 6` on a whole
neighborhood of the actual length fiber, uniformly over every new pin. -/
theorem incidentBody_joint_rank_le_of_deletionDrop
    (hpGeneric : IsGenericPlacement p) (k : ℕ) (hdrop : deletionRankDrop G v ≤ k + 3)
    (b₁ b₂ : B) :
    ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base), ∀ q : Vec3,
      Module.finrank ℝ (CofactorKernel.bodyJointPin
        ((T.incidentBodyRepresentation p hp base C b₁).form y).toLinearMap
        ((T.incidentBodyRepresentation p hp base C b₂).form y).toLinearMap q).range ≤ k := by
  let P : T.IncidentGroundedMotions p base → Placement V 3 :=
    fun y => restoreDeletedPlacement v (p v) (C.parametrization y)
  have hP : ContinuousAt P 0 :=
    (continuous_restoreDeletedPlacement v (p v)).continuousAt.comp
      C.smooth_parametrization.continuousAt
  have hP0 : P 0 = p := by simp [P, C.parametrization_zero]
  have hgeneric : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base),
      IsGenericPlacement (P y) := by
    apply hP.eventually
    rw [hP0]
    exact isOpen_isGenericPlacement.mem_nhds hpGeneric
  have hgeometry : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base),
      GeneralPosition.InGeneralPosition (P y) := by
    apply hP.eventually
    rw [hP0]
    exact GeneralPosition.isOpen_generalPosition.mem_nhds hp
  have hvelocity := bodyRepresentation_velocity (deletedGraph G v) (T.triangleEmbedding base)
    (deletedPlacement p v) C T.triangleVertices T.triangleVertices_clique T.triangleEmbedding
    T.triangleEmbedding_mem (deletedGeneralPosition p hp v)
  have hground := bodyRepresentation_grounded (deletedGraph G v) (T.triangleEmbedding base)
    (deletedPlacement p v) C T.triangleVertices T.triangleVertices_clique T.triangleEmbedding
    T.triangleEmbedding_mem (deletedGeneralPosition p hp v) base (T.triangleEmbedding_mem base)
  filter_upwards [hgeneric, hgeometry, hvelocity, hground,
    C.smooth_parametrization.eventually (by simp),
    eventually_eventually_nhds.mpr C.level] with y hgen hgeom hvel hzero hsmooth hlevel
  have hnoncol : T.NoncollinearAt (P y) :=
    GeneralPosition.InGeneralPosition.incident_noncollinear (P y) hgeom T
  have htrans : T.TransverseAt (P y) :=
    GeneralPosition.InGeneralPosition.incident_transverse (P y) hgeom T
  let F : T.IncidentGroundedMotions p base →ₗ[ℝ] DeletedMotions G (P y) v :=
    (fderiv ℝ C.parametrization y).toLinearMap.codRestrict _ (by
      intro u
      have hu := derivative_mem_groundedMotions (deletedGraph G v) (T.triangleEmbedding base)
        (deletedPlacement p v) C.parametrization y u
        (hsmooth.differentiableAt (by norm_num)) hlevel
      change (fderiv ℝ C.parametrization y) u ∈
        (rigidityOperator (deletedGraph G v)
          (deletedPlacement (restoreDeletedPlacement v (p v) (C.parametrization y)) v)).ker
      rw [deletedPlacement_restore]
      exact hu.1)
  have htwist (b : B) (u : T.IncidentGroundedMotions p base) :
      T.bodyTwist (P y) hnoncol b (F u) =
        (T.incidentBodyRepresentation p hp base C b).form y u := by
    apply sub_eq_zero.mp
    apply twist_eq_zero_of_fixing_triangle (T.trianglePoints (P y) b) (hnoncol b)
    intro i
    rw [map_sub, sub_eq_zero, T.bodyTwist_fit]
    have hv := hvel u b (T.triangle b i) (T.triangleEmbedding_mem b i)
    simpa only [F, LinearMap.codRestrict_apply, ContinuousLinearMap.coe_coe,
      P, trianglePoints, restoreDeletedPlacement_other, incidentBodyRepresentation] using hv
  intro q
  let L := T.commonPinAt (P y) hnoncol base q
  let π : (B → Vec3) →ₗ[ℝ] (Vec3 × Vec3) :=
    (LinearMap.proj b₁).prod (LinearMap.proj b₂)
  have hfactor : CofactorKernel.bodyJointPin
      ((T.incidentBodyRepresentation p hp base C b₁).form y).toLinearMap
      ((T.incidentBodyRepresentation p hp base C b₂).form y).toLinearMap q =
      π.comp (L.comp F) := by
    apply LinearMap.ext
    intro u
    have hbase : (T.incidentBodyRepresentation p hp base C base).form y u = 0 :=
      hzero u
    change
      (evaluateTwist q ((T.incidentBodyRepresentation p hp base C b₁).form y u),
        evaluateTwist q ((T.incidentBodyRepresentation p hp base C b₂).form y u)) =
      (evaluateTwist q (T.bodyTwist (P y) hnoncol b₁ (F u) -
        T.bodyTwist (P y) hnoncol base (F u)),
        evaluateTwist q (T.bodyTwist (P y) hnoncol b₂ (F u) -
          T.bodyTwist (P y) hnoncol base (F u)))
    simp only [htwist, hbase, sub_zero]
  rw [hfactor, LinearMap.range_comp]
  apply (Submodule.finrank_map_le π (L.comp F).range).trans
  apply (Submodule.finrank_mono (LinearMap.range_comp_le_range F L)).trans
  exact T.commonPin_rank_le_of_deletionDrop (P y) hgen hnoncol htrans base k hdrop q

theorem incidentBody_joint_rank_le_three
    (hpGeneric : IsGenericPlacement p) (hdrop : deletionRankDrop G v ≤ 6)
    (b₁ b₂ : B) :
    ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base), ∀ q : Vec3,
      Module.finrank ℝ (CofactorKernel.bodyJointPin
        ((T.incidentBodyRepresentation p hp base C b₁).form y).toLinearMap
        ((T.incidentBodyRepresentation p hp base C b₂).form y).toLinearMap q).range ≤ 3 :=
  T.incidentBody_joint_rank_le_of_deletionDrop p hp base C hpGeneric 3 hdrop b₁ b₂

/-- The dimension-three branch on the literal deleted graph fiber.
The only body-rank premises describe the actual two selected projections;
the common-pin rank and all local calculus data are consequences. -/
theorem incidentBody_rankThree_forms_equal
    (hpGeneric : IsGenericPlacement p) (hdrop : deletionRankDrop G v ≤ 5)
    (hdim : Module.finrank ℝ (T.IncidentGroundedMotions p base) = 3)
    (b₁ b₂ : B)
    (hinj₁ : Function.Injective ((T.incidentBodyRepresentation p hp base C b₁).form 0))
    (hinj₂ : Function.Injective ((T.incidentBodyRepresentation p hp base C b₂).form 0)) :
    (T.incidentBodyRepresentation p hp base C b₂).form 0 =
      (T.incidentBodyRepresentation p hp base C b₁).form 0 := by
  apply actual_rankThree_body_forms_equal
    (T.incidentBodyRepresentation p hp base C b₁).form
    (T.incidentBodyRepresentation p hp base C b₂).form 0 hdim
  · exact (T.incidentBodyRepresentation_locallyRepresented p hp base C).mono
      (fun y hy => ⟨hy b₁, hy b₂⟩)
  · exact hinj₁
  · exact hinj₂
  · exact T.incidentBody_joint_rank_le_of_deletionDrop p hp base C hpGeneric 2 hdrop b₁ b₂

/-- The rank-four local merger on the actual deleted graph. Its rank
bound, matrix representability, and local injectivity are all derived
from the graph and its genuine grounded chart. The regular pin and the
nonzero surviving second-body motion are the remaining pointwise data
to be selected in the minimal-counterexample argument. -/
theorem incidentBody_regular_pin_merges
    (hpGeneric : IsGenericPlacement p) (hdrop : deletionRankDrop G v ≤ 6)
    (hdim : Module.finrank ℝ (T.IncidentGroundedMotions p base) = 4)
    (b₁ b₂ : B) (pin : Vec3)
    (hinj : Function.Injective ((T.incidentBodyRepresentation p hp base C b₁).form 0))
    (hsurj : Function.Surjective ((evaluateTwist pin).comp
      ((T.incidentBodyRepresentation p hp base C b₁).form 0).toLinearMap))
    (hmotion : ∃ u : T.IncidentGroundedMotions p base,
      evaluateTwist pin ((T.incidentBodyRepresentation p hp base C b₁).form 0 u) = 0 ∧
        (T.incidentBodyRepresentation p hp base C b₂).form 0 u ≠ 0) :
    ∀ u : T.IncidentGroundedMotions p base,
      evaluateTwist pin ((T.incidentBodyRepresentation p hp base C b₁).form 0 u) = 0 →
        (T.incidentBodyRepresentation p hp base C b₂).form 0 u =
          (T.incidentBodyRepresentation p hp base C b₁).form 0 u := by
  apply actual_rankFour_regular_pin_merges_of_nonzero
    (T.incidentBodyRepresentation p hp base C b₁).form
    (T.incidentBodyRepresentation p hp base C b₂).form 0 hdim pin hsurj
  · exact (T.incidentBodyRepresentation_locallyRepresented p hp base C).mono
      (fun y hy => ⟨hy b₁, hy b₂⟩)
  · exact (T.incidentBodyRepresentation p hp base C b₁).form_differentiable.continuousAt.eventually
      (ContinuousLinearMap.isOpen_injective.mem_nhds hinj)
  · exact hmotion
  · exact T.incidentBody_joint_rank_le_three p hp base C hpGeneric hdrop b₁ b₂

end IncidentTetrahedra

end

end Papers.Rigidity.VertexPin

end
end BundleSource0033

section BundleSource0034
/- Source: Papers/RigidityThreeHinges.lean -/




@[expose] public section

/-!
# Three concurrent independent hinges glue actual rigid bodies

This elementary Euclidean argument supplies the small neighborhood case
without invoking a coning theorem.  Three pairwise hinge directions that
are linearly independent force all three body twists to agree.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix BigOperators Classical

theorem angular_parallel_of_fixing_two (X : Twist) (p q : Vec3) (hpq : q ≠ p)
    (hp : evaluateTwist p X = 0) (hq : evaluateTwist q X = 0) :
    ∃ c : ℝ, c • (q - p) = X.1 := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq
  have hc : X.1 ⨯₃ (q - p) = 0 := by
    ext i
    have hp' := congrFun hp i
    have hq' := congrFun hq i
    fin_cases i <;>
      simp [evaluateTwist_apply, cross_apply] at hp' hq' ⊢ <;> linarith
  have hc' : (q - p) ⨯₃ X.1 = 0 := by
    rw [← cross_anticomm X.1 (q - p), hc, neg_zero]
  apply Submodule.mem_span_singleton.mp
  rw [← ker_crossProduct_eq_span (q - p) hd]
  exact hc'

theorem twist_eq_zero_of_angular_zero_of_fixing (X : Twist) (p : Vec3)
    (hω : X.1 = 0) (hp : evaluateTwist p X = 0) : X = 0 := by
  apply Prod.ext hω
  simpa [evaluateTwist_apply, hω] using hp

/-- The infinitesimal three-hinge closure argument uses the literal
Euclidean evaluation equations, including the common pin. -/
theorem three_hinges_force_common_twist (p : Vec3) (q : Fin 3 → Vec3)
    (hq : LinearIndependent ℝ (fun i => q i - p)) (X Y Z : Twist)
    (hXY : evaluateTwist p X = evaluateTwist p Y)
    (hYZ : evaluateTwist p Y = evaluateTwist p Z)
    (h₀ : evaluateTwist (q 0) X = evaluateTwist (q 0) Y)
    (h₁ : evaluateTwist (q 1) Y = evaluateTwist (q 1) Z)
    (h₂ : evaluateTwist (q 2) Z = evaluateTwist (q 2) X) :
    X = Y ∧ Y = Z := by
  let D : Fin 3 → Twist := ![X - Y, Y - Z, Z - X]
  have hDp (i : Fin 3) : evaluateTwist p (D i) = 0 := by
    fin_cases i
    · simpa [D, map_sub] using sub_eq_zero.mpr hXY
    · simpa [D, map_sub] using sub_eq_zero.mpr hYZ
    · simpa [D, map_sub] using sub_eq_zero.mpr (hYZ.symm.trans hXY.symm)
  have hDq (i : Fin 3) : evaluateTwist (q i) (D i) = 0 := by
    fin_cases i
    · simpa [D, map_sub] using sub_eq_zero.mpr h₀
    · simpa [D, map_sub] using sub_eq_zero.mpr h₁
    · simpa [D, map_sub] using sub_eq_zero.mpr h₂
  have hparallel (i : Fin 3) : ∃ c : ℝ, c • (q i - p) = (D i).1 :=
    angular_parallel_of_fixing_two (D i) p (q i)
      (fun h => hq.ne_zero i (by simp [h])) (hDp i) (hDq i)
  choose c hc using hparallel
  have hsum : ∑ i : Fin 3, c i • (q i - p) = 0 := by
    simp only [hc, Fin.sum_univ_three]
    change (X.1 - Y.1) + (Y.1 - Z.1) + (Z.1 - X.1) = 0
    abel
  have hzero : ∀ i, c i = 0 := (Fintype.linearIndependent_iff.mp hq) c hsum
  have hDzero (i : Fin 3) : D i = 0 := by
    apply twist_eq_zero_of_angular_zero_of_fixing (D i) p _ (hDp i)
    rw [← hc i, hzero i, zero_smul]
  exact ⟨sub_eq_zero.mp (hDzero 0), sub_eq_zero.mp (hDzero 1)⟩

open BarJoint

variable {V : Type} [Fintype V]

/-- Three cliques meeting in three distinct hinges through a common
vertex form one ambient rigid cluster at generic placements. -/
theorem rigidCluster_union_three_hinged_cliques
    (G : SimpleGraph V) (S T U : Finset V) (v : V)
    (hS : G.IsClique (S : Set V)) (hT : G.IsClique (T : Set V))
    (hU : G.IsClique (U : Set V))
    (hcS : 3 ≤ S.card) (hcT : 3 ≤ T.card) (hcU : 3 ≤ U.card)
    (hvS : v ∈ S) (hvT : v ∈ T) (hvU : v ∈ U)
    (f : Fin 3 ↪ {w : V // w ≠ v})
    (h₀ : (f 0).val ∈ S ∩ T) (h₁ : (f 1).val ∈ T ∩ U)
    (h₂ : (f 2).val ∈ U ∩ S) :
    RigidCluster G (S ∪ T ∪ U) := by
  obtain ⟨p, hpGeneric, hpGeom⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  apply rigidCluster_of_motionRepresentation G (S ∪ T ∪ U) p hpGeneric
  intro u
  obtain ⟨X, hX⟩ := exists_twist_on_clique G p u.val hpGeom u.property S hcS hS
  obtain ⟨Y, hY⟩ := exists_twist_on_clique G p u.val hpGeom u.property T hcT hT
  obtain ⟨Z, hZ⟩ := exists_twist_on_clique G p u.val hpGeom u.property U hcU hU
  have hcommon := three_hinges_force_common_twist (p v) (fun i => p (f i).val)
    (by
      have h := (GeneralPosition.InGeneralPosition.star p hpGeom v f).neg
      change LinearIndependent ℝ (fun i : Fin 3 => -(p v - p (f i).val)) at h
      simpa only [neg_sub] using h) X Y Z
    ((hX v hvS).symm.trans (hY v hvT)) ((hY v hvT).symm.trans (hZ v hvU))
    ((hX _ (Finset.mem_inter.mp h₀).1).symm.trans (hY _ (Finset.mem_inter.mp h₀).2))
    ((hY _ (Finset.mem_inter.mp h₁).1).symm.trans (hZ _ (Finset.mem_inter.mp h₁).2))
    ((hZ _ (Finset.mem_inter.mp h₂).1).symm.trans (hX _ (Finset.mem_inter.mp h₂).2))
  refine ⟨X, ?_⟩
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases Finset.mem_union.mp hw with hw | hw
    · exact hX w hw
    · rw [hcommon.1]
      exact hY w hw
  · rw [hcommon.1, hcommon.2]
    exact hZ w hw

end

end Papers.Rigidity

end
end BundleSource0034

section BundleSource0035
/- Source: Papers/RigidityDegreeSix.lean -/



@[expose] public section

/-!
# The exact degree-six body classification

Three incident bodies would give three disjoint hinge directions after
their common vertex is removed.  The finite-set count below establishes
that configuration; the preceding module proves that its actual motions
glue.  This derives both alternatives of Lemma 3.3 directly from the
ordinary Euclidean framework.
-/

namespace Papers.Rigidity

noncomputable section

open BarJoint
open scoped Classical Matrix

private theorem pair_inter_pos_in_six {V : Type} (N A B C : Finset V)
    (hN : N.card ≤ 6) (hA : A ⊆ N) (hB : B ⊆ N) (hC : C ⊆ N)
    (hcA : 3 ≤ A.card) (hcB : 3 ≤ B.card) (hcC : 3 ≤ C.card)
    (hAB : (A ∩ B).card ≤ 1) (hAC : (A ∩ C).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) : 0 < (A ∩ B).card := by
  have hwhole : (A ∪ B ∪ C).card ≤ 6 :=
    (Finset.card_le_card (Finset.union_subset (Finset.union_subset hA hB) hC)).trans hN
  have hsplit₁ := Finset.card_union_add_card_inter A B
  have hsplit₂ := Finset.card_union_add_card_inter (A ∪ B) C
  have hinter : ((A ∪ B) ∩ C).card ≤ 2 := by
    have heq : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext x; simp only [Finset.mem_inter, Finset.mem_union]; tauto
    rw [heq]
    have h := Finset.card_union_le (A ∩ C) (B ∩ C)
    omega
  omega

/-- The only way three sets of at least three elements, with pairwise
intersections at most one, fit into six labels is a triangle of distinct
pairwise intersections. -/
private theorem three_sets_in_six {V : Type} (N A B C : Finset V)
    (hN : N.card ≤ 6) (hA : A ⊆ N) (hB : B ⊆ N) (hC : C ⊆ N)
    (hcA : 3 ≤ A.card) (hcB : 3 ≤ B.card) (hcC : 3 ≤ C.card)
    (hAB : (A ∩ B).card ≤ 1) (hAC : (A ∩ C).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) :
    ∃ a b c, a ∈ A ∩ B ∧ b ∈ B ∩ C ∧ c ∈ C ∩ A ∧
      a ≠ b ∧ b ≠ c ∧ c ≠ a := by
  have hwhole : (A ∪ B ∪ C).card ≤ 6 :=
    (Finset.card_le_card (Finset.union_subset (Finset.union_subset hA hB) hC)).trans hN
  have hsplit₁ := Finset.card_union_add_card_inter A B
  have hsplit₂ := Finset.card_union_add_card_inter (A ∪ B) C
  have hnoTriple (x : V) : ¬ (x ∈ A ∧ x ∈ B ∧ x ∈ C) := by
    rintro ⟨hxA, hxB, hxC⟩
    have hsub : (A ∪ B) ∩ C ⊆ {x} := by
      intro y hy
      obtain ⟨hyAB, hyC⟩ := Finset.mem_inter.mp hy
      apply Finset.mem_singleton.mpr
      rcases Finset.mem_union.mp hyAB with hyA | hyB
      · exact Finset.card_le_one_iff.mp hAC
          (Finset.mem_inter.mpr ⟨hyA, hyC⟩) (Finset.mem_inter.mpr ⟨hxA, hxC⟩)
      · exact Finset.card_le_one_iff.mp hBC
          (Finset.mem_inter.mpr ⟨hyB, hyC⟩) (Finset.mem_inter.mpr ⟨hxB, hxC⟩)
    have hi : ((A ∪ B) ∩ C).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp
    (pair_inter_pos_in_six N A B C hN hA hB hC hcA hcB hcC hAB hAC hBC)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp
    (pair_inter_pos_in_six N B C A hN hB hC hA hcB hcC hcA hBC
      (by simpa [Finset.inter_comm] using hAB) (by simpa [Finset.inter_comm] using hAC))
  obtain ⟨c, hc⟩ := Finset.card_pos.mp
    (pair_inter_pos_in_six N C A B hN hC hA hB hcC hcA hcB
      (by simpa [Finset.inter_comm] using hAC)
      (by simpa [Finset.inter_comm] using hBC) hAB)
  refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_⟩
  · intro h; subst b
    exact hnoTriple a ⟨(Finset.mem_inter.mp ha).1,
      (Finset.mem_inter.mp ha).2, (Finset.mem_inter.mp hb).2⟩
  · intro h; subst c
    exact hnoTriple b ⟨(Finset.mem_inter.mp hc).2,
      (Finset.mem_inter.mp hb).1, (Finset.mem_inter.mp hb).2⟩
  · intro h; subst a
    exact hnoTriple c ⟨(Finset.mem_inter.mp hc).2,
      (Finset.mem_inter.mp ha).2, (Finset.mem_inter.mp hc).1⟩

variable {V : Type} [Fintype V]

private theorem erased_body_subset_neighbors (C : MinimalCounterexample V) (v : V)
    (S : Finset V) (hS : IsBody C.graph S) (hvS : v ∈ S) :
    S.erase v ⊆ C.graph.neighborFinset v := by
  intro w hw
  obtain ⟨hwv, hwS⟩ := Finset.mem_erase.mp hw
  exact (C.graph.mem_neighborFinset v w).mpr (hS.2.1 hvS hwS hwv.symm)

private theorem erased_body_intersection_le_one (C : MinimalCounterexample V) (v : V)
    (S T : Finset V) (hS : IsBody C.graph S) (hT : IsBody C.graph T)
    (hvS : v ∈ S) (hvT : v ∈ T) (hne : S ≠ T) :
    (S.erase v ∩ T.erase v).card ≤ 1 := by
  have heq : S.erase v ∩ T.erase v = (S ∩ T).erase v := by
    ext w; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
  rw [heq, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hvS, hvT⟩)]
  have h := C.body_intersection_le_two S T hS hT hne
  omega

/-- A degree-six vertex cannot belong to three distinct bodies. -/
theorem MinimalCounterexample.not_three_bodies_of_degree_six
    (C : MinimalCounterexample V) (v : V) (hdegree : C.graph.degree v = 6)
    (S T U : Finset V) (hS : IsBody C.graph S) (hT : IsBody C.graph T)
    (hU : IsBody C.graph U) (hvS : v ∈ S) (hvT : v ∈ T) (hvU : v ∈ U)
    (hST : S ≠ T) (hSU : S ≠ U) (hTU : T ≠ U) : False := by
  have hcard (A : Finset V) (hA : IsBody C.graph A) (hvA : v ∈ A) :
      3 ≤ (A.erase v).card := by
    rw [Finset.card_erase_of_mem hvA]
    have h := hA.1
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hca⟩ := three_sets_in_six
    (C.graph.neighborFinset v) (S.erase v) (T.erase v) (U.erase v)
    (by simpa [C.graph.card_neighborFinset_eq_degree, hdegree])
    (erased_body_subset_neighbors C v S hS hvS)
    (erased_body_subset_neighbors C v T hT hvT)
    (erased_body_subset_neighbors C v U hU hvU)
    (hcard S hS hvS) (hcard T hT hvT) (hcard U hU hvU)
    (erased_body_intersection_le_one C v S T hS hT hvS hvT hST)
    (erased_body_intersection_le_one C v S U hS hU hvS hvU hSU)
    (erased_body_intersection_le_one C v T U hT hU hvT hvU hTU)
  have hav : a ≠ v := (Finset.mem_erase.mp (Finset.mem_inter.mp ha).1).1
  have hbv : b ≠ v := (Finset.mem_erase.mp (Finset.mem_inter.mp hb).1).1
  have hcv : c ≠ v := (Finset.mem_erase.mp (Finset.mem_inter.mp hc).1).1
  let f : Fin 3 ↪ {w : V // w ≠ v} :=
    { toFun := ![⟨a, hav⟩, ⟨b, hbv⟩, ⟨c, hcv⟩]
      inj' := by
        intro i j h
        have h' := congrArg Subtype.val h
        fin_cases i <;> fin_cases j <;> simp_all }
  have hcluster := rigidCluster_union_three_hinged_cliques C.graph S T U v
    hS.2.1 hT.2.1 hU.2.1 (by have h := hS.1; omega)
    (by have h := hT.1; omega) (by have h := hU.1; omega) hvS hvT hvU f
    (Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp ha).1,
      Finset.mem_of_mem_erase (Finset.mem_inter.mp ha).2⟩)
    (Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hb).1,
      Finset.mem_of_mem_erase (Finset.mem_inter.mp hb).2⟩)
    (Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hc).1,
      Finset.mem_of_mem_erase (Finset.mem_inter.mp hc).2⟩)
  have hSsub : S ⊆ S ∪ T ∪ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hTsub : T ⊆ S ∪ T ∪ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hsize : 4 ≤ (S ∪ T ∪ U).card := hS.1.trans (Finset.card_le_card hSsub)
  have hclique := C.rigidCluster_isClique (S ∪ T ∪ U) hsize hcluster
  have hUS := hS.2.2 _ hSsub hclique
  have hUT := hT.2.2 _ hTsub hclique
  exact hST (Finset.Subset.antisymm (hSsub.trans hUT) (hTsub.trans hUS))

/-- A degree-six vertex lies in exactly two maximal bodies. -/
theorem MinimalCounterexample.exactly_two_bodies_of_degree_six
    (C : MinimalCounterexample V) (v : V) (hdegree : C.graph.degree v = 6) :
    ∃ S T : Finset V, IsBody C.graph S ∧ IsBody C.graph T ∧
      v ∈ S ∧ v ∈ T ∧ S ≠ T ∧
        ∀ U : Finset V, IsBody C.graph U → v ∈ U → U = S ∨ U = T := by
  obtain ⟨S, T, hS, hT, hvS, hvT, hST⟩ := C.exists_two_bodies v
  refine ⟨S, T, hS, hT, hvS, hvT, hST, ?_⟩
  intro U hU hvU
  by_cases hUS : U = S
  · exact Or.inl hUS
  by_cases hUT : U = T
  · exact Or.inr hUT
  exact False.elim (C.not_three_bodies_of_degree_six v hdegree S T U hS hT hU
    hvS hvT hvU hST (Ne.symm hUS) (Ne.symm hUT))

/-- Both alternatives of Lemma 3.3, including the exact clique orders
and the shared-edge condition in type B. -/
theorem MinimalCounterexample.degree_six_body_classification
    (C : MinimalCounterexample V) (v : V) (hdegree : C.graph.degree v = 6) :
    ∃ S T : Finset V, IsBody C.graph S ∧ IsBody C.graph T ∧
      v ∈ S ∧ v ∈ T ∧ S ≠ T ∧
      (∀ U : Finset V, IsBody C.graph U → v ∈ U → U = S ∨ U = T) ∧
      ((S.card = 4 ∧ T.card = 4 ∧ S ∩ T = {v}) ∨
        (S.card = 5 ∧ T.card = 4 ∧ (S ∩ T).card = 2)) := by
  obtain ⟨S, T, hS, hT, hvS, hvT, hST, htwo⟩ := C.exactly_two_bodies_of_degree_six v hdegree
  have hunion : S ∪ T = VertexPin.closedNeighborhood C.graph v := by
    ext w
    constructor
    · intro hw
      by_cases hwv : w = v
      · exact (VertexPin.mem_closedNeighborhood _ _ _).mpr (Or.inl hwv)
      apply (VertexPin.mem_closedNeighborhood _ _ _).mpr
      apply Or.inr
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hS.2.1 hvS hw (Ne.symm hwv)
      · exact hT.2.1 hvT hw (Ne.symm hwv)
    · intro hw
      rcases (VertexPin.mem_closedNeighborhood _ _ _).mp hw with rfl | hw
      · exact Finset.mem_union_left _ hvS
      obtain ⟨U, hU, hvU, hwU⟩ := C.covered.edge_in_body hw
      rcases htwo U hU hvU with rfl | rfl
      · exact Finset.mem_union_left _ hwU
      · exact Finset.mem_union_right _ hwU
  have hucard : (S ∪ T).card = 7 := by
    rw [hunion, VertexPin.card_closedNeighborhood, hdegree]
  have hinter := C.body_intersection_le_two S T hS hT hST
  have hvinter : v ∈ S ∩ T := Finset.mem_inter.mpr ⟨hvS, hvT⟩
  have hinterpos : 0 < (S ∩ T).card := Finset.card_pos.mpr ⟨v, hvinter⟩
  have hsum := Finset.card_union_add_card_inter S T
  have hcS := hS.1
  have hcT := hT.1
  by_cases hfourS : S.card = 4
  · by_cases hfourT : T.card = 4
    · have hi : (S ∩ T).card = 1 := by omega
      have hiset' : S ∩ T = {v} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hvinter, ?_⟩
        intro w hw
        exact Finset.card_le_one_iff.mp (by omega) hw hvinter
      exact ⟨S, T, hS, hT, hvS, hvT, hST, htwo,
        Or.inl ⟨hfourS, hfourT, hiset'⟩⟩
    · have hfiveT : T.card = 5 := by omega
      have hi : (T ∩ S).card = 2 := by rw [Finset.inter_comm]; omega
      refine ⟨T, S, hT, hS, hvT, hvS, Ne.symm hST, ?_, Or.inr ⟨hfiveT, hfourS, hi⟩⟩
      intro U hU hvU
      exact (htwo U hU hvU).symm
  · have hfiveS : S.card = 5 := by omega
    have hfourT : T.card = 4 := by omega
    have hi : (S ∩ T).card = 2 := by omega
    exact ⟨S, T, hS, hT, hvS, hvT, hST, htwo, Or.inr ⟨hfiveS, hfourT, hi⟩⟩

end

end Papers.Rigidity

end
end BundleSource0035

section BundleSource0036
/- Source: Papers/RigidityTwoTriangles.lean -/



@[expose] public section

/-!
# Two actual incident tetrahedra cover a degree-six vertex

In the K4/K4 case the two surviving triangles are disjoint.  In the
K5/K4 case use the three vertices of the K5 outside the shared edge,
and the three surviving vertices of the K4.  This gives two actual
tetrahedra covering all six neighbors in both cases.
-/

namespace Papers.Rigidity.VertexPin

noncomputable section

open BarJoint Matrix
open scoped Classical Matrix

variable {V : Type} [Fintype V] {G : SimpleGraph V} {v : V}

def IncidentTetrahedra.ofTwoTriangles (A B : Finset V)
    (hA : A.card = 3) (hB : B.card = 3)
    (hAc : G.IsClique (A : Set V)) (hBc : G.IsClique (B : Set V))
    (hAs : ∀ w ∈ A, G.Adj v w) (hBs : ∀ w ∈ B, G.Adj v w)
    (hcover : ∀ w, G.Adj v w → w ∈ A ∨ w ∈ B) :
    IncidentTetrahedra G v (Fin 2) := by
  let S : Fin 2 → Finset V := ![A, B]
  have hc (b : Fin 2) : (S b).card = 3 := by fin_cases b <;> assumption
  have hcl (b : Fin 2) : G.IsClique (S b : Set V) := by fin_cases b <;> assumption
  have hs (b : Fin 2) (w : V) : w ∈ S b → G.Adj v w := by
    fin_cases b <;> first | exact hAs w | exact hBs w
  let e (b : Fin 2) : Fin 3 ≃ S b := (Finset.equivFinOfCardEq (hc b)).symm
  let tri (b : Fin 2) (i : Fin 3) : DeletedVertex v :=
    ⟨(e b i).val, (hs b (e b i).val (e b i).property).ne.symm⟩
  refine
    { triangle := tri
      injective := ?_
      clique := ?_
      spoke := ?_
      covers := ?_ }
  · intro b i j hij
    exact (e b).injective (Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) hij))
  · intro b i j hij
    exact hcl b (e b i).property (e b j).property
      (fun h => hij ((e b).injective (Subtype.ext h)))
  · intro b i
    exact hs b (e b i).val (e b i).property
  · intro w hw
    rcases hcover w hw with hw | hw
    · let w' : S 0 := ⟨w, hw⟩
      exact ⟨0, (e 0).symm w', congrArg Subtype.val ((e 0).apply_symm_apply w')⟩
    · let w' : S 1 := ⟨w, hw⟩
      exact ⟨1, (e 1).symm w', congrArg Subtype.val ((e 1).apply_symm_apply w')⟩

end
end Papers.Rigidity.VertexPin

namespace Papers.Rigidity

noncomputable section

open BarJoint VertexPin
open scoped Classical

variable {V : Type} [Fintype V]

/-- Both alternatives of the proved degree-six classification supply
the same actual two-triangle elimination model. -/
theorem MinimalCounterexample.two_incident_tetrahedra_of_degree_six
    (C : MinimalCounterexample V) (v : V) (hdegree : C.graph.degree v = 6) :
    Nonempty (IncidentTetrahedra C.graph v (Fin 2)) := by
  obtain ⟨S, T, hS, hT, hvS, hvT, hST, htwo, hcases⟩ :=
    C.degree_six_body_classification v hdegree
  have hcover (w : V) (hw : C.graph.Adj v w) : w ∈ S ∨ w ∈ T := by
    obtain ⟨U, hU, hvU, hwU⟩ := C.covered.edge_in_body hw
    rcases htwo U hU hvU with rfl | rfl
    · exact Or.inl hwU
    · exact Or.inr hwU
  have hTcard : (T.erase v).card = 3 := by
    have ht : T.card = 4 := hcases.elim (fun h => h.2.1) (fun h => h.2.1)
    rw [Finset.card_erase_of_mem hvT, ht]
  have hTclique : C.graph.IsClique (T.erase v : Set V) :=
    hT.2.1.subset (by intro w hw; exact Finset.mem_of_mem_erase hw)
  have hTspoke (w : V) (hw : w ∈ T.erase v) : C.graph.Adj v w :=
    hT.2.1 hvT (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
  rcases hcases with hA | hB
  · have hScard : (S.erase v).card = 3 := by
      rw [Finset.card_erase_of_mem hvS, hA.1]
    refine ⟨IncidentTetrahedra.ofTwoTriangles (S.erase v) (T.erase v)
      hScard hTcard ?_ hTclique ?_ hTspoke ?_⟩
    · exact hS.2.1.subset (by intro w hw; exact Finset.mem_of_mem_erase hw)
    · intro w hw
      exact hS.2.1 hvS (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
    · intro w hw
      rcases hcover w hw with hwS | hwT
      · exact Or.inl (Finset.mem_erase.mpr ⟨hw.ne.symm, hwS⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hw.ne.symm, hwT⟩)
  · have hshared : ((S ∩ T).erase v).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hvS, hvT⟩), hB.2.2]
      decide
    obtain ⟨w, hw⟩ := hshared
    obtain ⟨hwv, hwST⟩ := Finset.mem_erase.mp hw
    obtain ⟨hwS, hwT⟩ := Finset.mem_inter.mp hwST
    have hScard : ((S.erase v).erase w).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwv, hwS⟩),
        Finset.card_erase_of_mem hvS, hB.1]
    refine ⟨IncidentTetrahedra.ofTwoTriangles ((S.erase v).erase w) (T.erase v)
      hScard hTcard ?_ hTclique ?_ hTspoke ?_⟩
    · exact hS.2.1.subset (by
        intro z hz
        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
    · intro z hz
      have hz' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)
      exact hS.2.1 hvS hz'.2 hz'.1.symm
    · intro z hz
      rcases hcover z hz with hzS | hzT
      · by_cases hzw : z = w
        · subst z
          exact Or.inr (Finset.mem_erase.mpr ⟨hwv, hwT⟩)
        · exact Or.inl (Finset.mem_erase.mpr ⟨hzw,
            Finset.mem_erase.mpr ⟨hz.ne.symm, hzS⟩⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hz.ne.symm, hzT⟩)

end
end Papers.Rigidity

end
end BundleSource0036

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0036/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0036.json"

section BundleSource0037
/- Source: Papers/RigidityLowDegreeWitness.lean -/




@[expose] public section

/-!
# A degree-six rank-five vertex in the actual minimal counterexample

The full stress-prefix bound already forces such a vertex, before the
one-dimensional-flexibility conclusion.  This isolates the precise
local configuration needed in Proposition 3.5 and uses the literal
rank contributions whose sum has been proved to be the graph rank.
-/

namespace Papers.Rigidity.SupportedCode

theorem bound_mono {s a b : ℕ} (hs : 1 ≤ s) (hab : a ≤ b) :
    bound s a ≤ bound s b :=
  (monotone_nat_of_le_succ (fun r => bound_succ_mono s r hs)) hab

theorem three_le_degree_half_sub_bound (d δ : ℕ) (hd : 7 ≤ d) (hδ : 5 ≤ δ) :
    3 ≤ (d : ℝ) / 2 - bound 4 (d - δ) := by
  have hmono : bound 4 (d - δ) ≤ bound 4 (d - 5) :=
    bound_mono (by decide) (Nat.sub_le_sub_left hδ d)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 5 ≤ d by omega)
  have htwo : 2 ≤ k := by omega
  have hkpos : (0 : ℝ) < k + 4 := by positivity
  have hid : ((k + 5 : ℕ) : ℝ) / 2 - bound 4 k = 4 - 6 / (k + 4) := by
    unfold bound
    push_cast
    field_simp
    ring
  have hbase : 3 ≤ (d : ℝ) / 2 - bound 4 (d - 5) := by
    have hd' : d = k + 5 := by omega
    rw [hd']
    simp only [Nat.add_sub_cancel]
    rw [hid]
    have hfrac : (6 : ℝ) / (k + 4) ≤ 1 := by
      apply (div_le_iff₀ hkpos).mpr
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast htwo
      linarith
    linarith
  linarith

end Papers.Rigidity.SupportedCode

namespace Papers.Rigidity

noncomputable section

open BarJoint VertexPin SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- A concrete local obstruction is forced by the complete global
rank count: some degree-six vertex has deletion rank loss exactly five. -/
theorem MinimalCounterexample.exists_degree_six_drop_five (C : MinimalCounterexample V) :
    ∃ v : V, C.graph.degree v = 6 ∧ deletionRankDrop C.graph v = 5 := by
  by_contra hnone
  have hrc (v : V) : (3 : ℝ) ≤ rankContribution C.graph v := by
    have hdegree := C.connected.degree_ge v
    have hdrop := C.five_le_deletionRankDrop v
    have hbound := corollary_two_two_rankContribution C.graph v
    by_cases hsix : C.graph.degree v = 6
    · have hnot : deletionRankDrop C.graph v ≠ 5 :=
        fun heq => hnone ⟨v, hsix, heq⟩
      have hzero : C.graph.degree v - deletionRankDrop C.graph v = 0 := by omega
      rw [hzero, bound_zero, sub_zero, hsix] at hbound
      norm_num at hbound
      exact hbound
    · exact (three_le_degree_half_sub_bound (C.graph.degree v)
        (deletionRankDrop C.graph v) (by omega) hdrop).trans hbound
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hrc v)
  rw [sum_rankContribution] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have htotal := congrArg (fun n : ℕ => (n : ℝ)) C.rank_add_flexibility
  push_cast at htotal
  have hflex : (0 : ℝ) ≤ C.flexibility := Nat.cast_nonneg _
  nlinarith

end
end Papers.Rigidity

end
end BundleSource0037

section BundleSource0038
/- Source: Papers/RigidityRelativeMotion.lean -/




@[expose] public section

/-!
# The actual relative-motion dimension after vertex deletion

The relative twists on the incident tetrahedra determine every deleted
motion modulo common Euclidean motions.  This follows from the proved
rigidity of the neighbor-completed graph, not from a dimension assigned
to a hypothetical body framework.  Consequently the relative image has
dimension `f + δ(v) - 3`, exactly as used in Sections 3 and 4.
-/

namespace Papers.Rigidity.VertexPin.IncidentTetrahedra

noncomputable section

open BarJoint
open scoped Classical

variable {V B : Type} [Fintype V] [Fintype B]
variable {G : SimpleGraph V} {v : V}

def relativeTwistOperator (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (base : B) :
    DeletedMotions G p v →ₗ[ℝ] (B → Twist) :=
  LinearMap.pi (T.relativeTwists p hp base)

@[simp] theorem relativeTwistOperator_apply (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base b : B)
    (u : DeletedMotions G p v) :
    T.relativeTwistOperator p hp base u b =
      T.bodyTwist p hp b u - T.bodyTwist p hp base u := rfl

theorem bodyTwist_globalTwist (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (b : B) (X : Twist) :
    T.bodyTwist p hp b
      (globalTwistMotion (deletedGraph G v) (deletedPlacement p v) X) = X := by
  apply triangleTwistOperator_injective (T.trianglePoints p b) (hp b)
  ext a
  exact congrFun (T.bodyTwist_fit p hp b
    (globalTwistMotion (deletedGraph G v) (deletedPlacement p v) X) a.1) a.2

theorem globalTwist_mem_relativeTwist_ker (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base : B) (X : Twist) :
    globalTwistMotion (deletedGraph G v) (deletedPlacement p v) X ∈
      (T.relativeTwistOperator p hp base).ker := by
  rw [LinearMap.mem_ker]
  funext b
  simp only [relativeTwistOperator_apply, T.bodyTwist_globalTwist, sub_self, Pi.zero_apply]

/-- Vanishing relative twists make every neighbor move by the same
Euclidean twist, so the deleted motion preserves the neighbor clique. -/
theorem neighborCompletion_motion_of_relativeTwist_zero
    (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (base : B) (u : DeletedMotions G p v)
    (hu : T.relativeTwistOperator p hp base u = 0) :
    IsInfinitesimalMotion (neighborCompletion G v) (deletedPlacement p v) u.val := by
  have hbody (b : B) : T.bodyTwist p hp b u = T.bodyTwist p hp base u := by
    have hb := congrFun hu b
    simpa only [relativeTwistOperator_apply, Pi.zero_apply, sub_eq_zero] using hb
  have hneighbor (w : V) (hvw : G.Adj v w) :
      ∀ hw : w ≠ v, u.val ⟨w, hw⟩ = evaluateTwist (p w) (T.bodyTwist p hp base u) := by
    intro hw
    obtain ⟨b, i, rfl⟩ := T.covers w hvw
    have hfit := T.bodyTwist_fit p hp b u i
    rw [hbody] at hfit
    exact hfit.symm
  rw [isInfinitesimalMotion_iff]
  intro a b hab
  rcases (neighborCompletion_adj G v a b).mp hab with hold | ⟨_, ha, hb⟩
  · exact (isInfinitesimalMotion_iff (deletedGraph G v)
      (deletedPlacement p v) u.val).mp u.property a b hold
  · change edgeConstraint (deletedPlacement p v) u.val a b = 0
    change ∑ i : Fin 3, (p a.val i - p b.val i) *
      (u.val a i - u.val b i) = 0
    rw [hneighbor a.val ha a.property, hneighbor b.val hb b.property]
    exact twist_preserves_bar _ _ _

/-- The only kernel of the relative-body map consists of the actual
common Euclidean motions whenever the neighbor completion is rigid. -/
theorem ker_relativeTwistOperator (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base : B)
    (hgen : IsGenericPlacement (deletedPlacement p v))
    (hgeom : GeneralPosition.InGeneralPosition (deletedPlacement p v))
    (hH : IsGenericallyRigidInR3 (neighborCompletion G v)) :
    (T.relativeTwistOperator p hp base).ker =
      (globalTwistMotion (deletedGraph G v) (deletedPlacement p v)).range := by
  apply le_antisymm
  · intro u hu
    have hmotion := T.neighborCompletion_motion_of_relativeTwist_zero
      p hp base u (LinearMap.mem_ker.mp hu)
    have hclosed : (rigidityOperator (SimpleGraph.completeGraph (DeletedVertex v))
        (deletedPlacement p v)).ker =
        (rigidityOperator (neighborCompletion G v) (deletedPlacement p v)).ker :=
      ker_eq_of_le_of_genericRigidityRank_eq le_top hH _ hgen
    have hcomplete : IsInfinitesimalMotion (SimpleGraph.completeGraph (DeletedVertex v))
        (deletedPlacement p v) u.val := by
      change u.val ∈ (rigidityOperator _ _).ker
      rw [hclosed]
      exact hmotion
    obtain ⟨X, hX⟩ := exists_twist_of_completeMotion
      (deletedPlacement p v) u.val hgeom
      (⟨T.triangle base, T.injective base⟩ : Fin 3 ↪ DeletedVertex v) hcomplete
    exact ⟨X, Subtype.ext (funext fun w => (hX w).symm)⟩
  · rintro u ⟨X, rfl⟩
    exact T.globalTwist_mem_relativeTwist_ker p hp base X

theorem relativeTwist_rank_add_six (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base : B)
    (hgen : IsGenericPlacement (deletedPlacement p v))
    (hgeom : GeneralPosition.InGeneralPosition (deletedPlacement p v))
    (hH : IsGenericallyRigidInR3 (neighborCompletion G v)) :
    Module.finrank ℝ (T.relativeTwistOperator p hp base).range + 6 =
      Module.finrank ℝ (DeletedMotions G p v) := by
  have hcard : 3 ≤ Fintype.card (DeletedVertex v) := by
    simpa using Fintype.card_le_of_injective (T.triangle base) (T.injective base)
  have hcommon : Module.finrank ℝ
      (globalTwistMotion (deletedGraph G v) (deletedPlacement p v)).range = 6 := by
    rw [LinearMap.finrank_range_of_inj
      (globalTwistMotion_injective _ _ hgeom hcard), finrank_twist]
  have h := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := DeletedMotions G p v) (V₂ := B → Twist)
    (T.relativeTwistOperator p hp base)
  rwa [T.ker_relativeTwistOperator p hp base hgen hgeom hH, hcommon] at h

/-- This is the exact dimension asserted before Proposition 3.5 and
again for the grounded fiber in Proposition 4.1.  It is obtained from
the original graph's rank and the actual relative twist operator. -/
theorem minimalCounterexample_relativeTwist_dimension
    (C : MinimalCounterexample V) (v : V)
    (T : IncidentTetrahedra C.graph v B) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hgeom : GeneralPosition.InGeneralPosition p)
    (base : B) :
    Module.finrank ℝ (T.relativeTwistOperator p
      (GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T) base).range + 3 =
      C.flexibility + deletionRankDrop C.graph v := by
  let hp := GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T
  have ht := GeneralPosition.InGeneralPosition.incident_transverse p hgeom T
  have hg := generic_deletedPlacement p hgen v
  have hq := GeneralPosition.InGeneralPosition.comp_embedding p hgeom
    (⟨Subtype.val, Subtype.val_injective⟩ : DeletedVertex v ↪ V)
  have hrel := T.relativeTwist_rank_add_six p hp base hg hq
    (C.neighborCompletion_isGenericallyRigid v)
  have hold := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := Velocity (VertexPin.DeletedVertex v) 3) (V₂ := VertexPin.DeletedVertex v × VertexPin.DeletedVertex v → ℝ)
    (rigidityOperator (deletedGraph C.graph v)
    (deletedPlacement p v))
  have hdel := T.rigidityRank_deletion_identity p hp ht base
  have hf := C.rank_add_flexibility
  have hcard : Fintype.card (DeletedVertex v) + 1 = Fintype.card V := by
    have h := Fintype.card_subtype_compl (fun w : V => w = v)
    have hpositive : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    simp only [Fintype.card_subtype_eq] at h
    change Fintype.card (DeletedVertex v) = Fintype.card V - 1 at h
    omega
  have hdim : Module.finrank ℝ (Velocity (DeletedVertex v) 3) =
      3 * Fintype.card (DeletedVertex v) := by
    simp [Velocity, Point, Module.finrank_pi_fintype, Nat.mul_comm]
  rw [hdim] at hold
  change rigidityRank (deletedGraph C.graph v) (deletedPlacement p v) +
    Module.finrank ℝ (DeletedMotions C.graph p v) = _ at hold
  rw [hg] at hold
  rw [hgen, hg] at hdel
  unfold deletionRankDrop
  omega

end

end Papers.Rigidity.VertexPin.IncidentTetrahedra

end
end BundleSource0038

section BundleSource0039
/- Source: Papers/RigidityOneFlexibility.lean -/






@[expose] public section

/-!
# The minimal counterexample has exactly one flexibility mode

The global count first forces a degree-six vertex of deletion rank five.
Both degree-six body types admit two actual incident tetrahedra covering
all neighbors.  Their relative twist space has dimension `f + 2`, while
reintroducing the generic vertex evaluates it with rank two on an actual
open pin window.  The proved singular-pin classification makes that
space three-dimensional, hence `f = 1`.

This route treats both body types uniformly and retains all graph and
matrix hypotheses of Proposition 3.5.
-/

namespace Papers.Rigidity.VertexPin.IncidentTetrahedra

noncomputable section

open BarJoint Matrix
open scoped Classical Matrix

variable {V : Type} [Fintype V] {G : SimpleGraph V} {v : V}

def twoBodyRelativeTwist (T : IncidentTetrahedra G v (Fin 2))
    (p : Placement V 3) (hp : T.NoncollinearAt p) :
    DeletedMotions G p v →ₗ[ℝ] Twist :=
  T.bodyTwist p hp 1 - T.bodyTwist p hp 0

theorem ker_relativeTwistOperator_two (T : IncidentTetrahedra G v (Fin 2))
    (p : Placement V 3) (hp : T.NoncollinearAt p) :
    (T.relativeTwistOperator p hp 0).ker = (T.twoBodyRelativeTwist p hp).ker := by
  ext u
  constructor
  · intro hu
    exact congrFun (LinearMap.mem_ker.mp hu) 1
  · intro hu
    have h := LinearMap.mem_ker.mp hu
    rw [LinearMap.mem_ker]
    funext b
    fin_cases b
    · simp [relativeTwistOperator_apply]
    · exact h

theorem relativeTwist_rank_two (T : IncidentTetrahedra G v (Fin 2))
    (p : Placement V 3) (hp : T.NoncollinearAt p) :
    Module.finrank ℝ (T.relativeTwistOperator p hp 0).range =
      Module.finrank ℝ (T.twoBodyRelativeTwist p hp).range := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := DeletedMotions G p v) (V₂ := Fin 2 → Twist)
    (T.relativeTwistOperator p hp 0)
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := DeletedMotions G p v) (V₂ := Twist)
    (T.twoBodyRelativeTwist p hp)
  rw [T.ker_relativeTwistOperator_two p hp] at h₁
  omega

theorem ker_commonPinAt_two (T : IncidentTetrahedra G v (Fin 2))
    (p : Placement V 3) (hp : T.NoncollinearAt p) (q : Vec3) :
    (T.commonPinAt p hp 0 q).ker =
      ((evaluateTwist q).comp (T.twoBodyRelativeTwist p hp)).ker := by
  ext u
  constructor
  · intro hu
    have h := congrFun (LinearMap.mem_ker.mp hu) 1
    exact h
  · intro hu
    have h := LinearMap.mem_ker.mp hu
    rw [LinearMap.mem_ker]
    funext b
    fin_cases b
    · simp [commonPinAt, CommonPinLowRank.operator, relativeTwists]
    · exact h

/-- With two actual incident tetrahedra, the common-pin equations have
exactly the rank of evaluation on their actual relative twist image. -/
theorem commonPinAt_rank_two (T : IncidentTetrahedra G v (Fin 2))
    (p : Placement V 3) (hp : T.NoncollinearAt p) (q : Vec3) :
    Module.finrank ℝ (T.commonPinAt p hp 0 q).range =
      Module.finrank ℝ (restrictEvaluation (T.twoBodyRelativeTwist p hp).range q).range := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := DeletedMotions G p v) (V₂ := Fin 2 → Vec3)
    (T.commonPinAt p hp 0 q)
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := DeletedMotions G p v) (V₂ := Vec3)
    ((evaluateTwist q).comp (T.twoBodyRelativeTwist p hp))
  rw [T.ker_commonPinAt_two p hp q] at h₁
  have hr : ((evaluateTwist q).comp (T.twoBodyRelativeTwist p hp)).range =
      (restrictEvaluation (T.twoBodyRelativeTwist p hp).range q).range := by
    simp [restrictEvaluation, LinearMap.range_comp]
  rw [hr] at h₂
  omega

end
end Papers.Rigidity.VertexPin.IncidentTetrahedra

namespace Papers.Rigidity

noncomputable section

open BarJoint VertexPin
open scoped Classical

variable {V : Type} [Fintype V]

/-- Proposition 3.5: the actual generic bar framework of the selected
minimal counterexample has exactly one relative infinitesimal mode. -/
theorem MinimalCounterexample.flexibility_eq_one (C : MinimalCounterexample V) :
    C.flexibility = 1 := by
  obtain ⟨v, hdegree, hdrop⟩ := C.exists_degree_six_drop_five
  obtain ⟨T⟩ := C.two_incident_tetrahedra_of_degree_six v hdegree
  obtain ⟨p, hpGeneric, hpGeom⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  let hp := GeneralPosition.InGeneralPosition.incident_noncollinear p hpGeom T
  have ht := GeneralPosition.InGeneralPosition.incident_transverse p hpGeom T
  let W : Submodule ℝ Twist := (T.twoBodyRelativeTwist p hp).range
  have hdimension := T.minimalCounterexample_relativeTwist_dimension
    C v p hpGeneric hpGeom (0 : Fin 2)
  rw [T.relativeTwist_rank_two p hp, hdrop] at hdimension
  have hWdimension : Module.finrank ℝ W = C.flexibility + 2 := by
    dsimp [W]
    omega
  have hWlarge : 3 ≤ Module.finrank ℝ W := by
    rw [hWdimension]
    have hf := C.flexibility_pos
    omega
  obtain ⟨O, hO, hpO, hwindow⟩ := T.exists_open_generic_pin_window p hpGeneric ht
  have hrank (q : Vec3) (hq : q ∈ O) :
      Module.finrank ℝ (restrictEvaluation W q).range ≤ 2 := by
    have hid := T.rigidityRank_replace_identity p hp q (hwindow q hq).2 (0 : Fin 2)
    have hg := (hwindow q hq).1 C.graph
    have hd := generic_deletedPlacement p hpGeneric v (deletedGraph C.graph v)
    rw [hg, hd, T.commonPinAt_rank_two p hp q] at hid
    change Module.finrank ℝ (restrictEvaluation (T.twoBodyRelativeTwist p hp).range q).range ≤ 2
    unfold deletionRankDrop at hdrop
    omega
  have hdim := (pin_space_classification_of_open_rank_bound W O hO
    ⟨p v, hpO⟩ hrank hWlarge).1
  omega

end
end Papers.Rigidity

end
end BundleSource0039

section BundleSource0040
/- Source: Papers/RigidityGroundedIncident.lean -/




@[expose] public section

/-!
# Exact grounded motion and incident-body dictionaries

Grounding subtracts the actual twist of the reference triangle from a
deleted-graph motion.  Its images on every other body are precisely the
relative twists.  At the center of the genuine configuration chart the
body forms have these same images, without a supplied tangent or rank
identification.  Injectivity uses rigidity of the neighbor-completed
graph, not the false claim that incident bodies cover all old vertices.

The grounded space retains the motions of all old vertices.
-/

noncomputable section
namespace Papers.Rigidity.VertexPin.IncidentTetrahedra

open BarJoint Calculus Calculus.GroundedConfiguration
open scoped Classical

variable {V B : Type} [Fintype V] [Fintype B] {G : SimpleGraph V} {v : V}

def groundedDeletedInclusion (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (base : B) : T.IncidentGroundedMotions p base →ₗ[ℝ] DeletedMotions G p v :=
  (T.IncidentGroundedMotions p base).subtype.codRestrict _ (fun u => u.property.1)

@[simp] theorem groundedDeletedInclusion_val (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (base : B) (u : T.IncidentGroundedMotions p base) :
    (T.groundedDeletedInclusion p base u).val = u.val := rfl

theorem bodyTwist_grounded_base (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hn : T.NoncollinearAt p) (base : B) (u : T.IncidentGroundedMotions p base) :
    T.bodyTwist p hn base (T.groundedDeletedInclusion p base u) = 0 := by
  apply twist_eq_zero_of_fixing_triangle (T.trianglePoints p base) (hn base)
  intro i
  rw [T.bodyTwist_fit]
  funext j
  exact congrFun (LinearMap.mem_ker.mp u.property.2) (i, j)

def groundDeletedMotion (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hn : T.NoncollinearAt p) (base : B) :
    DeletedMotions G p v →ₗ[ℝ] T.IncidentGroundedMotions p base := by
  let F : DeletedMotions G p v →ₗ[ℝ] Velocity (DeletedVertex v) 3 :=
    (rigidityOperator (deletedGraph G v) (deletedPlacement p v)).ker.subtype -
      (globalTwistOperator (deletedPlacement p v)).comp (T.bodyTwist p hn base)
  exact F.codRestrict _ (by
    intro u
    refine ⟨Submodule.sub_mem _ u.property
      (globalTwist_isMotion (deletedGraph G v) (deletedPlacement p v)
        (T.bodyTwist p hn base u)), ?_⟩
    change (triangleRestriction (T.triangleEmbedding base)) (F u) = 0
    funext ij
    change u.val (T.triangle base ij.1) ij.2 -
      evaluateTwist (T.trianglePoints p base ij.1) (T.bodyTwist p hn base u) ij.2 = 0
    rw [T.bodyTwist_fit, sub_self])

@[simp] theorem groundDeletedMotion_val (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hn : T.NoncollinearAt p) (base : B)
    (u : DeletedMotions G p v) :
    (T.groundDeletedMotion p hn base u).val =
      u.val - globalTwistOperator (deletedPlacement p v) (T.bodyTwist p hn base u) := rfl

theorem groundedDeletedInclusion_ground (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hn : T.NoncollinearAt p) (base : B)
    (u : DeletedMotions G p v) :
    T.groundedDeletedInclusion p base (T.groundDeletedMotion p hn base u) =
      u - globalTwistMotion (deletedGraph G v) (deletedPlacement p v)
        (T.bodyTwist p hn base u) := by
  apply Subtype.ext
  rfl

theorem bodyTwist_groundDeletedMotion (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hn : T.NoncollinearAt p) (base b : B)
    (u : DeletedMotions G p v) :
    T.bodyTwist p hn b
        (T.groundedDeletedInclusion p base (T.groundDeletedMotion p hn base u)) =
      T.relativeTwists p hn base b u := by
  rw [T.groundedDeletedInclusion_ground, map_sub, T.bodyTwist_globalTwist]
  rfl

variable (T : IncidentTetrahedra G v B) (p : Placement V 3)
  (hp : GeneralPosition.InGeneralPosition p) (base : B)
variable (C : SmoothLevelChart
  (groundedLengthMap (deletedGraph G v) (T.triangleEmbedding base))
  (deletedPlacement p v) (T.IncidentGroundedMotions p base))

theorem incidentBodyForm_at_zero (b : B) (u : T.IncidentGroundedMotions p base) :
    (T.incidentBodyRepresentation p hp base C b).form 0 u =
      T.bodyTwist p (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) b
        (T.groundedDeletedInclusion p base u) := by
  apply triangleTwistOperator_injective (T.trianglePoints p b)
    (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T b)
  funext ij
  rw [triangleTwistOperator_apply, triangleTwistOperator_apply, T.bodyTwist_fit]
  exact congrFun (bodyRepresentation_fit_at_zero (deletedGraph G v)
    (T.triangleEmbedding base) (deletedPlacement p v) C T.triangleVertices
    T.triangleVertices_clique T.triangleEmbedding T.triangleEmbedding_mem
    (deletedGeneralPosition p hp v) b u (T.triangle b ij.1)
    (T.triangleEmbedding_mem b ij.1)) ij.2

/-- The full actual form image equals the original relative-twist
image, including all directions lost by grounding. -/
theorem incidentBodyForm_range_at_zero (b : B) :
    ((T.incidentBodyRepresentation p hp base C b).form 0).toLinearMap.range =
      (T.relativeTwists p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) base b).range := by
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  ext X
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨T.groundedDeletedInclusion p base u, ?_⟩
    rw [relativeTwists, LinearMap.sub_apply, T.bodyTwist_grounded_base, sub_zero]
    exact (T.incidentBodyForm_at_zero p hp base C b u).symm
  · rintro ⟨u, rfl⟩
    refine ⟨T.groundDeletedMotion p hn base u, ?_⟩
    exact (T.incidentBodyForm_at_zero p hp base C b
      (T.groundDeletedMotion p hn base u)).trans
      (T.bodyTwist_groundDeletedMotion p hn base b u)

def incidentBodyFormOperator : T.IncidentGroundedMotions p base →ₗ[ℝ] (B → Twist) :=
  LinearMap.pi fun b => ((T.incidentBodyRepresentation p hp base C b).form 0).toLinearMap

/-- Neighbor-completion rigidity supplies the required joint
injectivity although the incident bodies need not cover all old vertices. -/
theorem incidentBodyFormOperator_injective
    (hgen : IsGenericPlacement p)
    (hH : IsGenericallyRigidInR3 (neighborCompletion G v)) :
    Function.Injective (T.incidentBodyFormOperator p hp base C) := by
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro u hu
    have hforms := LinearMap.mem_ker.mp hu
    have hrelative : T.groundedDeletedInclusion p base u ∈
        (T.relativeTwistOperator p hn base).ker := by
      rw [LinearMap.mem_ker]
      funext b
      change T.bodyTwist p hn b (T.groundedDeletedInclusion p base u) -
        T.bodyTwist p hn base (T.groundedDeletedInclusion p base u) = 0
      rw [T.bodyTwist_grounded_base, sub_zero, ← T.incidentBodyForm_at_zero p hp base C]
      exact congrFun hforms b
    rw [T.ker_relativeTwistOperator p hn base (generic_deletedPlacement p hgen v)
      (deletedGeneralPosition p hp v) hH] at hrelative
    obtain ⟨X, hX⟩ := hrelative
    have hXzero : X = 0 := by
      have hh := congrArg (T.bodyTwist p hn base) hX
      rw [T.bodyTwist_globalTwist, T.bodyTwist_grounded_base] at hh
      exact hh
    change u = 0
    apply Subtype.ext
    have hh := congrArg Subtype.val hX
    simpa only [hXzero, map_zero, groundedDeletedInclusion_val,
      ZeroMemClass.coe_zero] using hh.symm
  · exact bot_le

end Papers.Rigidity.VertexPin.IncidentTetrahedra

namespace Papers.Rigidity

open BarJoint VertexPin
open scoped Classical

variable {V B : Type} [Fintype V] [Fintype B]

/-- The dimension of the actual grounded deleted configuration space
is the paper's `δ(v)-2`, obtained from the already derived flexibility
one and exact kernel dimensions. -/
theorem MinimalCounterexample.grounded_incident_finrank
    (M : MinimalCounterexample V) (v : V)
    (T : IncidentTetrahedra M.graph v B) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) (base : B) :
    Module.finrank ℝ (T.IncidentGroundedMotions p base) + 2 = deletionRankDrop M.graph v := by
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  have hg := generic_deletedPlacement p hgen v
  have hpd := GeneralPosition.InGeneralPosition.comp_embedding p hp
    (⟨Subtype.val, Subtype.val_injective⟩ : DeletedVertex v ↪ V)
  have hground := groundedBarMotions_finrank_add_six (deletedGraph M.graph v)
    (T.triangleEmbedding base) (T.clique base) (deletedPlacement p v) (hn base)
  have hrelative := T.relativeTwist_rank_add_six p hn base hg hpd
    (M.neighborCompletion_isGenericallyRigid v)
  have hdimension := T.minimalCounterexample_relativeTwist_dimension M v p hgen hp base
  rw [M.flexibility_eq_one] at hdimension
  change Module.finrank ℝ (T.IncidentGroundedMotions p base) + 6 =
    Module.finrank ℝ (DeletedMotions M.graph p v) at hground
  omega

end Papers.Rigidity

end
end
end BundleSource0040

section BundleSource0041
/- Source: Papers/RigidityIncidentBodyOwners.lean -/





@[expose] public section

/-!
# Incident tetrahedra with their actual maximal-body owners

Every surviving triangle is indexed together with its maximal clique.
All such triangles are retained, so the resulting family covers every
neighbor even when a body has more than four vertices.  Triangles with
the same owner give the same actual deleted-graph twist.  Conversely,
two distinct owners cannot agree on every full-graph motion at a generic
placement: such agreement would put their entire union in the ambient
rigidity closure, contrary to maximality.

The owner dictionary connects actual graph motions to Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity.VertexPin

open BarJoint
open scoped Classical

variable {V : Type} [Fintype V]

def OwnedIncidentTriangle (G : SimpleGraph V) (v : V) :=
  {a : Finset V × (Fin 3 ↪ DeletedVertex v) //
    IsBody G a.1 ∧ v ∈ a.1 ∧ ∀ i, (a.2 i).val ∈ a.1}

instance (G : SimpleGraph V) (v : V) : Fintype (OwnedIncidentTriangle G v) := by
  unfold OwnedIncidentTriangle
  infer_instance

def OwnedIncidentTriangle.owner {G : SimpleGraph V} {v : V}
    (b : OwnedIncidentTriangle G v) : Finset V := b.val.1

def OwnedIncidentTriangle.triangle {G : SimpleGraph V} {v : V}
    (b : OwnedIncidentTriangle G v) : Fin 3 ↪ DeletedVertex v := b.val.2

theorem exists_owned_triangle_through_neighbor (G : SimpleGraph V) (v : V)
    (hG : K4Covered G) (w : V) (hvw : G.Adj v w) :
    ∃ b : OwnedIncidentTriangle G v, ∃ i : Fin 3, (b.triangle i).val = w := by
  obtain ⟨S, hS, hvS, hwS⟩ := hG.edge_in_body hvw
  have hwv : w ≠ v := Ne.symm hvw.ne
  have hwold : w ∈ S.erase v := Finset.mem_erase.mpr ⟨hwv, hwS⟩
  have hcard : 2 ≤ ((S.erase v).erase w).card := by
    rw [Finset.card_erase_of_mem hwold, Finset.card_erase_of_mem hvS]
    have := hS.1
    omega
  obtain ⟨R, hR, hRcard⟩ := Finset.exists_subset_card_eq hcard
  have hwR : w ∉ R := fun hw => (Finset.mem_erase.mp (hR hw)).1 rfl
  let Q := insert w R
  have hQcard : Q.card = 3 := by simp [Q, hwR, hRcard]
  have hQold : Q ⊆ S.erase v := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hwold
    · exact (Finset.mem_erase.mp (hR hz)).2
  let e : Fin 3 ≃ Q := (Finset.equivFinOfCardEq hQcard).symm
  let f : Fin 3 ↪ DeletedVertex v :=
    ⟨fun i => ⟨(e i).val, (Finset.mem_erase.mp (hQold (e i).property)).1⟩,
      fun _ _ h => e.injective (Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) h))⟩
  let b : OwnedIncidentTriangle G v :=
    ⟨(S, f), hS, hvS, fun i => (Finset.mem_erase.mp (hQold (e i).property)).2⟩
  let wQ : Q := ⟨w, Finset.mem_insert_self w R⟩
  exact ⟨b, e.symm wQ, congrArg Subtype.val (e.apply_symm_apply wQ)⟩

/-- All actual owned triangles are used; no covering assumption about a
single arbitrarily selected triangle from each large body is made. -/
def ownedIncidentTetrahedra (G : SimpleGraph V) (v : V) (hG : K4Covered G) :
    IncidentTetrahedra G v (OwnedIncidentTriangle G v) where
  triangle b := b.triangle
  injective b := b.triangle.injective
  clique b i j hij := b.property.1.2.1 (b.property.2.2 i) (b.property.2.2 j)
    (fun h => hij (b.triangle.injective (Subtype.ext h)))
  spoke b i := b.property.1.2.1 b.property.2.1 (b.property.2.2 i)
    (Ne.symm (b.triangle i).property)
  covers := exists_owned_triangle_through_neighbor G v hG

namespace OwnedIncidentTriangle

variable {G : SimpleGraph V} {v : V}

def oldVertices (b : OwnedIncidentTriangle G v) : Finset (DeletedVertex v) :=
  Finset.univ.filter fun w => w.val ∈ b.owner

@[simp] theorem mem_oldVertices (b : OwnedIncidentTriangle G v) (w : DeletedVertex v) :
    w ∈ b.oldVertices ↔ w.val ∈ b.owner := by simp [oldVertices]

theorem oldVertices_card (b : OwnedIncidentTriangle G v) : 3 ≤ b.oldVertices.card := by
  let e : Fin 3 ↪ b.oldVertices :=
    ⟨fun i => ⟨b.triangle i, (b.mem_oldVertices _).mpr (b.property.2.2 i)⟩,
      fun _ _ h => b.triangle.injective (congrArg Subtype.val h)⟩
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective e e.injective

theorem oldVertices_clique (b : OwnedIncidentTriangle G v) :
    (deletedGraph G v).IsClique (b.oldVertices : Set (DeletedVertex v)) := by
  intro w hw z hz hne
  exact b.property.1.2.1 ((b.mem_oldVertices w).mp hw) ((b.mem_oldVertices z).mp hz)
    (fun he => hne (Subtype.ext he))

end OwnedIncidentTriangle

namespace IncidentTetrahedra

variable {G : SimpleGraph V} {v : V}

/-- A selected surviving triangle determines the twist on its entire
maximal body, including vertices outside that triangle. -/
theorem owned_bodyTwist_fit (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (b : OwnedIncidentTriangle G v) (u : DeletedMotions G p v)
    (w : DeletedVertex v) (hw : w.val ∈ b.owner) :
    u.val w = evaluateTwist (p w.val)
      ((ownedIncidentTetrahedra G v hG).bodyTwist p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hp
          (ownedIncidentTetrahedra G v hG)) b u) := by
  let T := ownedIncidentTetrahedra G v hG
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  have hpd : GeneralPosition.InGeneralPosition (deletedPlacement p v) :=
    GeneralPosition.InGeneralPosition.comp_embedding p hp
      ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨X, hX⟩ := exists_twist_on_clique (deletedGraph G v) (deletedPlacement p v)
    u.val hpd u.property b.oldVertices b.oldVertices_card b.oldVertices_clique
  have heq : T.bodyTwist p hn b u = X := by
    apply sub_eq_zero.mp
    apply twist_eq_zero_of_fixing_triangle (T.trianglePoints p b) (hn b)
    intro i
    have hXi : evaluateTwist (T.trianglePoints p b i) X = u.val (T.triangle b i) :=
      (hX (b.triangle i) ((b.mem_oldVertices _).mpr (b.property.2.2 i))).symm
    rw [map_sub, T.bodyTwist_fit, hXi, sub_self]
  rw [heq]
  exact hX w ((b.mem_oldVertices w).mpr hw)

theorem owned_bodyTwist_eq_of_owner_eq (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (b c : OwnedIncidentTriangle G v) (hbc : b.owner = c.owner)
    (u : DeletedMotions G p v) :
    (ownedIncidentTetrahedra G v hG).bodyTwist p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hp
          (ownedIncidentTetrahedra G v hG)) b u =
      (ownedIncidentTetrahedra G v hG).bodyTwist p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hp
          (ownedIncidentTetrahedra G v hG)) c u := by
  let T := ownedIncidentTetrahedra G v hG
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  apply sub_eq_zero.mp
  apply twist_eq_zero_of_fixing_triangle (T.trianglePoints p b) (hn b)
  intro i
  rw [map_sub, T.bodyTwist_fit]
  exact sub_eq_zero.mpr (owned_bodyTwist_fit hG p hp c u (b.triangle i)
    (by rw [← hbc]; exact b.property.2.2 i))

theorem owned_fullMotion_fit (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (b : OwnedIncidentTriangle G v) (u : (rigidityOperator G p).ker)
    (w : V) (hw : w ∈ b.owner) :
    u.val w = evaluateTwist (p w)
      ((ownedIncidentTetrahedra G v hG).bodyTwist p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hp
          (ownedIncidentTetrahedra G v hG)) b
        ((ownedIncidentTetrahedra G v hG).restrictFullMotion p u)) := by
  let T := ownedIncidentTetrahedra G v hG
  by_cases hwv : w = v
  · subst w
    exact T.fullMotion_at_vertex p
      (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T)
      (GeneralPosition.InGeneralPosition.incident_transverse p hp T) u b
  · exact owned_bodyTwist_fit hG p hp b (T.restrictFullMotion p u) ⟨w, hwv⟩ hw

end IncidentTetrahedra

/-- Distinct maximal bodies are separated by an actual full-graph
infinitesimal motion at every simultaneous maximum-rank placement in
geometric general position.  Ambient closure, including constraints
outside the two bodies, is used explicitly. -/
theorem MinimalCounterexample.owned_bodies_not_merged
    (C : MinimalCounterexample V) (v : V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (b c : OwnedIncidentTriangle C.graph v) (hne : b.owner ≠ c.owner) :
    let T := ownedIncidentTetrahedra C.graph v C.covered
    let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
    ∃ u : (rigidityOperator C.graph p).ker,
      T.bodyTwist p hn b (T.restrictFullMotion p u) ≠
        T.bodyTwist p hn c (T.restrictFullMotion p u) := by
  intro T hn
  by_contra hnone
  push_neg at hnone
  have hcluster : RigidCluster C.graph (b.owner ∪ c.owner) := by
    apply rigidCluster_of_motionRepresentation C.graph (b.owner ∪ c.owner) p hgen
    intro u
    refine ⟨T.bodyTwist p hn b (T.restrictFullMotion p u), ?_⟩
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact IncidentTetrahedra.owned_fullMotion_fit C.covered p hp b u w hw
    · rw [hnone u]
      exact IncidentTetrahedra.owned_fullMotion_fit C.covered p hp c u w hw
  have hcard : 4 ≤ (b.owner ∪ c.owner).card :=
    b.property.1.1.trans (Finset.card_le_card Finset.subset_union_left)
  have hclique := C.rigidCluster_isClique _ hcard hcluster
  have hb := b.property.1.2.2 _ Finset.subset_union_left hclique
  have hc := c.property.1.2.2 _ Finset.subset_union_right hclique
  exact hne (Finset.Subset.antisymm (Finset.subset_union_left.trans hc)
    (Finset.subset_union_right.trans hb))

end Papers.Rigidity.VertexPin

end
end
end BundleSource0041

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined06/block_0041/Consolidated/RigidityCombined06.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined06/checkpoint_0041.json"
