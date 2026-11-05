module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import Mathlib.LinearAlgebra.StdBasis

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
