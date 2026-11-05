module

public import PaperVerification.DivergenceDegreeMatrices
public import PaperVerification.AffineMatrixComplex

/-!
# The actual polynomial parameter family of divergence operators

Both finite matrices are affine in the parameter. Their entries are still
coefficients of the original operators and the corrected actual relations.
Regularity and closedness therefore give a rank bound at every parameter and
an exact generic rank over the literal rational function field.

This source has not yet been compiled. These matrix conclusions do not by
themselves identify the actual homogeneous quotient or its group action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DivergenceDegrees

open MvPolynomial DivergenceCocycle
open WeightedPolynomialPieces
open scoped BigOperators

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "Der" => Derivation K P P

variable (L : LieRinehartSubalgebra P Der)
variable {r : ℕ} (b : Module.Basis (Fin r) P L) (ω : L →ₗ[P] P)

theorem operator_affine (t : K) (X : L) (p : P) :
    operator L ω t X p=operator L ω 0 X p+
      t • (operator L ω 1 X p-operator L ω 0 X p) := by
  simp only [operator_apply,functional_apply,zero_smul,sub_zero,one_smul,
    sub_self,zero_add,add_zero,Algebra.smul_def,MvPolynomial.algebraMap_eq,
    map_sub,map_one,map_zero]
  ring

theorem elementarySecond_affine (t : K) (i j : Fin r) (p : P) :
    elementarySecond L b ω t i j p=elementarySecond L b ω 0 i j p+
      t • (elementarySecond L b ω 1 i j p-elementarySecond L b ω 0 i j p) := by
  simp only [elementarySecond_apply,zero_smul,one_smul,sub_zero]
  rw [operator_affine L ω t (b j) p,operator_affine L ω t (b i) p]
  simp only [add_smul,sub_smul,smul_sub,smul_add,smul_assoc]
  abel

theorem elementaryCoordinates_affine (t : K) (i j : Fin r) (p : P) :
    elementaryCoordinates L b ω t i j p=elementaryCoordinates L b ω 0 i j p+
      t • (elementaryCoordinates L b ω 1 i j p-elementaryCoordinates L b ω 0 i j p) := by
  change (b.equivFun.restrictScalars K) (elementarySecond L b ω t i j p)=_
  rw [elementarySecond_affine,map_add,map_smul,map_sub]
  rfl

section Field

variable (w : ι → ℕ) [∀ i, NeZero (w i)] (δ : Fin r → ℕ)

theorem firstMatrix_affine (t : K) (d : ℕ) :
    firstMatrix w L b δ ω t d=
      AffineMatrixComplex.fiber (firstMatrix w L b δ ω 0 d)
        (firstMatrix w L b δ ω 1 d) t := by
  ext a c
  simp only [firstMatrix,operator_affine L ω t,coeff_add,coeff_sub,coeff_smul,
    AffineMatrixComplex.fiber,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply]

theorem secondMatrix_affine (t : K) (d : ℕ) :
    secondMatrix w L b δ ω t d=
      AffineMatrixComplex.fiber (secondMatrix w L b δ ω 0 d)
        (secondMatrix w L b δ ω 1 d) t := by
  ext a c
  simp only [secondMatrix,elementaryCoordinates_affine L b ω t,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,coeff_add,coeff_sub,coeff_smul,
    AffineMatrixComplex.fiber,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply]

variable [Infinite K]

theorem rank_firstMatrix_le_zero
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (hω : IsClosed L ω)
    (hregular : RingTheory.Sequence.IsWeaklyRegular P
      (List.ofFn fun i : Fin r => ω (b i))) (t : K) (d : ℕ) :
    (firstMatrix w L b δ ω t d).rank ≤ (firstMatrix w L b δ ω 0 d).rank := by
  rw [firstMatrix_affine]
  apply AffineMatrixComplex.rank_specialization_le_zero
    (firstMatrix w L b δ ω 0 d) (firstMatrix w L b δ ω 1 d)
    (secondMatrix w L b δ ω 0 d) (secondMatrix w L b δ ω 1 d)
  · intro a
    rw [←firstMatrix_affine,←secondMatrix_affine]
    exact matrix_complex w L b δ ω hfields hvalues hω a d
  · exact zero_matrix_exact w L b δ ω hfields hvalues hω hregular d

theorem rank_firstMatrix_generic_eq_zero
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (hω : IsClosed L ω)
    (hregular : RingTheory.Sequence.IsWeaklyRegular P
      (List.ofFn fun i : Fin r => ω (b i))) (d : ℕ) :
    ((AffineMatrixComplex.universal (firstMatrix w L b δ ω 0 d)
      (firstMatrix w L b δ ω 1 d)).map
        (algebraMap (Polynomial K) (RatFunc K))).rank=
      (firstMatrix w L b δ ω 0 d).rank := by
  apply AffineMatrixComplex.rank_generic_eq_zero
    (firstMatrix w L b δ ω 0 d) (firstMatrix w L b δ ω 1 d)
    (secondMatrix w L b δ ω 0 d) (secondMatrix w L b δ ω 1 d)
  · intro a
    rw [←firstMatrix_affine,←secondMatrix_affine]
    exact matrix_complex w L b δ ω hfields hvalues hω a d
  · exact zero_matrix_exact w L b δ ω hfields hvalues hω hregular d

end Field
end PaperVerification.DivergenceDegrees
