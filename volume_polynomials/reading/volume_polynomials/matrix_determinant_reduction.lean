module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

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
