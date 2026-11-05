module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring.Basic

/-!
# Congruence coordinates are actual exterior-power coordinates

The coefficient matrix below is obtained by evaluating the canonical
exterior pairing against coordinate covectors.  It is injective on the
genuine second exterior power.  Its transformation law identifies the
matrix congruence polynomials used in the orbit argument with the action
of a linear map on actual quadratic exterior elements.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators Matrix

variable {K ν ι : Type*} [CommRing K]

/-- Extract the coefficient of the oriented pair `(u,v)` from an actual
second exterior power.  Reversing the orientation changes its sign. -/
def orbitExteriorCoefficient (u v : ν) :
    (⋀[K]^2 (ν → K)) →ₗ[K] K :=
  exteriorPower.alternatingMapToDual K (ν → K) 2
    ![LinearMap.proj u, LinearMap.proj v]

/-- The full alternating coefficient matrix of a genuine exterior 2-form. -/
def orbitExteriorCoefficientMatrix (f : ⋀[K]^2 (ν → K)) : Matrix ν ν K :=
  fun u v => orbitExteriorCoefficient u v f

theorem orbitExteriorCoefficient_word (u v : ν) (w : Fin 2 → ν → K) :
    orbitExteriorCoefficient u v (exteriorPower.ιMulti K 2 w) =
      w 0 u * w 1 v - w 0 v * w 1 u := by
  simp only [orbitExteriorCoefficient,
    exteriorPower.alternatingMapToDual_apply_ιMulti,
    Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, LinearMap.proj_apply]

theorem orbitExteriorCoefficientMatrix_word (w : Fin 2 → ν → K) (u v : ν) :
    orbitExteriorCoefficientMatrix (exteriorPower.ιMulti K 2 w) u v =
      w 0 u * w 1 v - w 0 v * w 1 u :=
  orbitExteriorCoefficient_word u v w

theorem orbitExteriorCoefficientMatrix_diagonal (f : ⋀[K]^2 (ν → K)) (u : ν) :
    orbitExteriorCoefficientMatrix f u u = 0 := by
  have h : orbitExteriorCoefficient (K := K) u u = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply, orbitExteriorCoefficient_word,
      sub_self, LinearMap.zero_apply]
  exact congrArg (fun L : (⋀[K]^2 (ν → K)) →ₗ[K] K => L f) h

theorem orbitExteriorCoefficientMatrix_skew (f : ⋀[K]^2 (ν → K)) (u v : ν) :
    orbitExteriorCoefficientMatrix f v u = -orbitExteriorCoefficientMatrix f u v := by
  have h : orbitExteriorCoefficient (K := K) v u = -orbitExteriorCoefficient u v := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply, orbitExteriorCoefficient_word,
      LinearMap.neg_apply]
    ring
  exact congrArg (fun L : (⋀[K]^2 (ν → K)) →ₗ[K] K => L f) h

section FiniteCoordinates

variable [Fintype ν] [DecidableEq ν]

/-- No exterior information is lost by passing to the coefficient matrix. -/
theorem orbitExteriorCoefficientMatrix_injective :
    Function.Injective (orbitExteriorCoefficientMatrix (K := K) (ν := ν)) := by
  classical
  letI : LinearOrder ν := linearOrderOfSTO WellOrderingRel
  let b := Pi.basisFun K ν
  intro f g hfg
  apply (b.exteriorPower 2).repr.injective
  ext s
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  have hdual : exteriorPower.ιMultiDual K 2 b s =
      orbitExteriorCoefficient (a 0) (a 1) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, orbitExteriorCoefficient_word,
      Matrix.det_fin_two, Matrix.of_apply, b, Module.Basis.coord_apply,
      Pi.basisFun_repr, a]
  rw [hdual]
  exact congrArg (fun A : Matrix ν ν K => A (a 0) (a 1)) hfg

private theorem orbit_minor_mulVec (X : Matrix ν ν K) (x y : ν → K) (u v : ν) :
    (X.transpose *ᵥ x) u * (X.transpose *ᵥ y) v -
      (X.transpose *ᵥ x) v * (X.transpose *ᵥ y) u =
      ∑ i, ∑ j, (X i u * X j v) * (x i * y j - x j * y i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have h₁ : (∑ i, X i u * x i) * (∑ j, X j v * y j) =
      ∑ i, ∑ j, (X i u * X j v) * (x i * y j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h₂ : (∑ i, X i v * x i) * (∑ j, X j u * y j) =
      ∑ i, ∑ j, (X i u * X j v) * (x j * y i) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [h₁, h₂, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Pulling coordinate covectors through an exterior map gives the literal
double-sum matrix congruence expression. -/
theorem orbitExteriorCoefficient_map (X : Matrix ν ν K) (u v : ν) :
    (orbitExteriorCoefficient u v).comp
        (exteriorPower.map 2 (Matrix.toLin' X.transpose)) =
      ∑ i, ∑ j, (X i u * X j v) • orbitExteriorCoefficient i j := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, orbitExteriorCoefficient_word,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Function.comp_apply, Matrix.toLin'_apply]
  exact orbit_minor_mulVec X (w 0) (w 1) u v

/-- The precise orientation used by the paper's orbit polynomial map:
`Xᵀ A X` is the coefficient matrix of `Λ²(Xᵀ)(f)`. -/
theorem orbitExteriorCoefficientMatrix_map (X : Matrix ν ν K)
    (f : ⋀[K]^2 (ν → K)) :
    orbitExteriorCoefficientMatrix
        (exteriorPower.map 2 (Matrix.toLin' X.transpose) f) =
      X.transpose * orbitExteriorCoefficientMatrix f * X := by
  ext u v
  have h := congrArg (fun L : (⋀[K]^2 (ν → K)) →ₗ[K] K => L f)
    (orbitExteriorCoefficient_map X u v)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  change orbitExteriorCoefficient u v
      (exteriorPower.map 2 (Matrix.toLin' X.transpose) f) = _
  rw [h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    orbitExteriorCoefficientMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Literal linear combinations of coordinate wedges, with arbitrary
oriented slots.  This definition imposes no hidden spanning hypothesis. -/
def orbitTwoFormOfSlots [Fintype ι] (row col : ι → ν) (c : ι → K) :
    ⋀[K]^2 (ν → K) :=
  ∑ i, c i • exteriorPower.ιMulti K 2
    ![Pi.basisFun K ν (row i), Pi.basisFun K ν (col i)]

theorem orbitExteriorCoefficientMatrix_ofSlots [Fintype ι]
    (row col : ι → ν) (c : ι → K) (u v : ν) :
    orbitExteriorCoefficientMatrix (orbitTwoFormOfSlots row col c) u v =
      ∑ i, c i *
        ((Pi.basisFun K ν (row i)) u * (Pi.basisFun K ν (col i)) v -
          (Pi.basisFun K ν (row i)) v * (Pi.basisFun K ν (col i)) u) := by
  simp only [orbitExteriorCoefficientMatrix, orbitTwoFormOfSlots,
    map_sum, map_smul, smul_eq_mul, orbitExteriorCoefficient_word,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end FiniteCoordinates

end PaperVerification.AlternatingForms
