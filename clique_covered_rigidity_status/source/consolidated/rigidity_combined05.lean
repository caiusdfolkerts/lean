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
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityMaurerCartan.lean -/








@[expose] public section

/-!
# The actual Maurer–Cartan differential identity

For a twice differentiable map into an associative real normed algebra and
a differentiable local inverse, the spatial logarithmic derivative
`dR * R⁻¹` satisfies Maurer–Cartan. This proves the differential identity
from ordinary Fréchet derivatives and symmetry of the second derivative;
it is not assumed as an axiom or built into the meaning of a body motion.

The algebra can in particular be an algebra of continuous linear
endomorphisms. Relating the resulting identity to the cross-product
coordinates of an actual Euclidean body is a separate algebraic step.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter
open scoped Topology

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

def spatialLogDerivative (R S : E → A) (x v : E) : A :=
  fderiv ℝ R x v * S x

theorem derivative_local_inverse (R S : E → A) (x : E)
    (hR : DifferentiableAt ℝ R x) (hS : DifferentiableAt ℝ S x)
    (hRS : ∀ᶠ y in 𝓝 x, R y * S y = 1)
    (hSR : S x * R x = 1) (v : E) :
    fderiv ℝ S x v = -(S x * fderiv ℝ R x v * S x) := by
  have heq : fderiv ℝ (fun y => R y * S y) x = 0 := by
    exact (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hRS).trans (fderiv_const_apply (𝕜 := ℝ) (x := x) (1 : A))
  rw [fderiv_fun_mul' hR hS] at heq
  have hp := congrArg (fun F : E →L[ℝ] A => F v) heq
  change R x * fderiv ℝ S x v + fderiv ℝ R x v * S x = 0 at hp
  have hm := congrArg (fun z : A => S x * z) hp
  have hz : fderiv ℝ S x v + S x * fderiv ℝ R x v * S x = 0 := by
    simpa only [mul_add, ← mul_assoc, hSR, one_mul, mul_zero] using hm
  exact eq_neg_of_add_eq_zero_left hz

/-- The spatial Maurer–Cartan equation in ordinary coordinate directions. -/
theorem spatial_maurer_cartan (R S : E → A) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (hS : DifferentiableAt ℝ S x)
    (hRS : ∀ᶠ y in 𝓝 x, R y * S y = 1)
    (hSR : S x * R x = 1) (v w : E) :
    fderiv ℝ (fun y => spatialLogDerivative R S y w) x v -
        fderiv ℝ (fun y => spatialLogDerivative R S y v) x w =
      spatialLogDerivative R S x v * spatialLogDerivative R S x w -
        spatialLogDerivative R S x w * spatialLogDerivative R S x v := by
  have hRdiff : DifferentiableAt ℝ R x := hR.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ R) x :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hsymm := hR.isSymmSndFDerivAt (by norm_num)
  have hpartial (u : E) : DifferentiableAt ℝ (fun y => fderiv ℝ R y u) x :=
    hD.clm_apply (differentiableAt_const u)
  have hsecond (u z : E) :
      fderiv ℝ (fun y => fderiv ℝ R y u) x z =
        fderiv ℝ (fderiv ℝ R) x z u := by
    rw [fderiv_clm_apply hD (differentiableAt_const u)]
    simp
  have hlog (u z : E) :
      fderiv ℝ (fun y => spatialLogDerivative R S y u) x z =
        fderiv ℝ R x u * fderiv ℝ S x z +
          fderiv ℝ (fderiv ℝ R) x z u * S x := by
    unfold spatialLogDerivative
    rw [fderiv_fun_mul' (hpartial u) hS]
    change fderiv ℝ R x u * fderiv ℝ S x z +
      fderiv ℝ (fun y => fderiv ℝ R y u) x z * S x = _
    rw [hsecond]
  rw [hlog, hlog, hsymm v w,
    derivative_local_inverse R S x hRdiff hS hRS hSR v,
    derivative_local_inverse R S x hRdiff hS hRS hSR w]
  unfold spatialLogDerivative
  noncomm_ring

end Papers.Rigidity.Calculus

end
end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined05/block_0001/Consolidated/RigidityCombined05.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined05/checkpoint_0001.json"
