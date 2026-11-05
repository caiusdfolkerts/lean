module

public import PaperVerification.RankSpecialization
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Affine complexes over the literal rational function field

The universal entries are actual polynomials in one parameter. A complex
identity at every scalar parameter over an infinite field proves the
polynomial identity. Exactness at zero then proves the rank comparison at
every specialization and equality over `RatFunc K`.

This supporting source has not yet been compiled.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AffineMatrixComplex

open Matrix Polynomial

variable {K u v w : Type*} [Field K]
  [Fintype u] [Fintype v] [Fintype w]

def fiber (A₀ A₁ : Matrix w v K) (t : K) : Matrix w v K :=
  A₀+t • (A₁-A₀)

def universal (A₀ A₁ : Matrix w v K) : Matrix w v K[X] :=
  fun i j => C (A₀ i j)+X*C (A₁ i j-A₀ i j)

theorem eval_universal (A₀ A₁ : Matrix w v K) (t : K) :
    (universal A₀ A₁).map (Polynomial.evalRingHom t)=fiber A₀ A₁ t := by
  ext i j
  simp only [universal,Matrix.map_apply,Polynomial.coe_evalRingHom,
    Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
    fiber,Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]

@[simp] theorem eval_universal_zero (A₀ A₁ : Matrix w v K) :
    (universal A₀ A₁).map (Polynomial.evalRingHom 0)=A₀ := by
  rw [eval_universal]
  simp only [fiber,zero_smul,add_zero]

theorem universal_complex [Infinite K]
    (F₀ F₁ : Matrix w v K) (G₀ G₁ : Matrix v u K)
    (h : ∀ t,fiber F₀ F₁ t * fiber G₀ G₁ t=0) :
    universal F₀ F₁ * universal G₀ G₁=0 := by
  ext i j
  apply Polynomial.funext
  intro t
  have hm : (universal F₀ F₁ * universal G₀ G₁).map
      (Polynomial.evalRingHom t)=0 := by
    rw [Matrix.map_mul,eval_universal,eval_universal,h t]
  simpa only [Matrix.map_apply,Polynomial.coe_evalRingHom,Matrix.zero_apply,
    Polynomial.eval_zero] using congrArg (fun A : Matrix w u K => A i j) hm

theorem rank_specialization_le_zero [Infinite K]
    (F₀ F₁ : Matrix w v K) (G₀ G₁ : Matrix v u K)
    (h : ∀ t,fiber F₀ F₁ t * fiber G₀ G₁ t=0)
    (he : LinearMap.range G₀.mulVecLin=LinearMap.ker F₀.mulVecLin) (t : K) :
    (fiber F₀ F₁ t).rank ≤ F₀.rank := by
  have hzero : LinearMap.range
      ((universal G₀ G₁).map (Polynomial.evalRingHom 0)).mulVecLin=
      LinearMap.ker ((universal F₀ F₁).map (Polynomial.evalRingHom 0)).mulVecLin := by
    simpa only [eval_universal_zero] using he
  have hbound := RankSpecialization.rank_le_at_exact_fiber
    (universal F₀ F₁) (universal G₀ G₁) (universal_complex F₀ F₁ G₀ G₁ h)
    (Polynomial.evalRingHom 0) (Polynomial.evalRingHom t) hzero
  simpa only [eval_universal_zero,eval_universal] using hbound

theorem rank_generic_eq_zero [Infinite K]
    (F₀ F₁ : Matrix w v K) (G₀ G₁ : Matrix v u K)
    (h : ∀ t,fiber F₀ F₁ t * fiber G₀ G₁ t=0)
    (he : LinearMap.range G₀.mulVecLin=LinearMap.ker F₀.mulVecLin) :
    ((universal F₀ F₁).map (algebraMap K[X] (RatFunc K))).rank=F₀.rank := by
  apply le_antisymm
  · have hzero : LinearMap.range
        ((universal G₀ G₁).map (Polynomial.evalRingHom 0)).mulVecLin=
        LinearMap.ker ((universal F₀ F₁).map (Polynomial.evalRingHom 0)).mulVecLin := by
      simpa only [eval_universal_zero] using he
    have hbound := RankSpecialization.rank_le_at_exact_fiber_of_distinct_fields
      (universal F₀ F₁) (universal G₀ G₁) (universal_complex F₀ F₁ G₀ G₁ h)
      (Polynomial.evalRingHom 0) (algebraMap K[X] (RatFunc K)) hzero
    simpa only [eval_universal_zero] using hbound
  · have hbound := RankSpecialization.rank_specialization_le (L := RatFunc K)
      (universal F₀ F₁) (Polynomial.evalRingHom 0)
    simpa only [eval_universal_zero] using hbound

end PaperVerification.AffineMatrixComplex
