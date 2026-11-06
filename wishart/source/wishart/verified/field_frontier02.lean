module

public import wishart.verified.field_analytic_union
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Logic.Equiv.Prod
public import tau_ceti.analysis.matrix.sqrt
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import tau_ceti.probability.distributions.gamma.basic
public import tau_ceti.measure_theory.measure.with_density
public import tau_ceti.probability.distributions.gaussian.density
public import tau_ceti.measure_theory.measure.pi_with_density
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Order.Floor.Ring

/- Generated ordinary proof stage. See audit/staged_field_frontier/FieldFrontier02/manifest.json. -/

@[expose] public section

set_option maxHeartbeats 400000
set_option maxRecDepth 1000
set_option maxErrors 1000

section CanonicalSource12
/- Source: Wishart/QuaternionSchur.lean -/



/-!
# Quaternion Schur complements and the regression matrix

The complex representation commutes with block decomposition after the literal
index-distribution equivalence.  The usual complex Schur determinant identity
therefore yields the Moore determinant identity.  The accompanying block
factorization is over the quaternion division ring itself.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion Matrix ComplexOrder Ring

namespace Wishart.QuaternionMatrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem complexRepresentation_fromBlocks
    (A : Matrix m m ℍ[ℝ]) (B : Matrix m n ℍ[ℝ])
    (C : Matrix n m ℍ[ℝ]) (D : Matrix n n ℍ[ℝ]) :
    (complexRepresentation (Matrix.fromBlocks A B C D)).submatrix
        (Equiv.sumProdDistrib m n (Fin 2)).symm
        (Equiv.sumProdDistrib m n (Fin 2)).symm =
      Matrix.fromBlocks (complexRepresentation A) (complexRepresentation B)
        (complexRepresentation C) (complexRepresentation D) := by
  ext i j
  rcases i with ⟨i,a⟩ | ⟨i,a⟩ <;> rcases j with ⟨j,b⟩ | ⟨j,b⟩ <;> rfl

theorem complex_det_fromBlocks
    (A : Matrix m m ℍ[ℝ]) (B : Matrix m n ℍ[ℝ])
    (C : Matrix n m ℍ[ℝ]) (D : Matrix n n ℍ[ℝ]) :
    (complexRepresentation (Matrix.fromBlocks A B C D)).det =
      (Matrix.fromBlocks (complexRepresentation A) (complexRepresentation B)
        (complexRepresentation C) (complexRepresentation D)).det := by
  rw [← complexRepresentation_fromBlocks,
    Matrix.det_submatrix_equiv_self]

theorem complex_det_schur {A : Matrix m m ℍ[ℝ]}
    (hA : IsUnit A) (B : Matrix m n ℍ[ℝ])
    (C : Matrix n m ℍ[ℝ]) (D : Matrix n n ℍ[ℝ]) :
    (complexRepresentation (Matrix.fromBlocks A B C D)).det =
      (complexRepresentation A).det *
        (complexRepresentation (D - C * A⁻¹ʳ * B)).det := by
  letI : Invertible (complexRepresentation A) :=
    (hA.map complexRepresentationStarAlgHom.toMonoidHom).invertible
  rw [complex_det_fromBlocks, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, complexRepresentation_sub,
    complexRepresentation_mul, complexRepresentation_mul,
    complexRepresentation_ringInverse hA]

theorem positiveDeterminant_schur {A : Matrix m m ℍ[ℝ]}
    (hA : PosDef A) (B : Matrix m n ℍ[ℝ]) (D : Matrix n n ℍ[ℝ])
    (hW : PosSemidef (D - Bᴴ * A⁻¹ʳ * B)) :
    positiveDeterminant (Matrix.fromBlocks A B Bᴴ D) =
      positiveDeterminant A * positiveDeterminant (D - Bᴴ * A⁻¹ʳ * B) := by
  unfold positiveDeterminant
  rw [complex_det_schur hA.isUnit]
  have hAr : (complexRepresentation A).det.im = 0 :=
    (RCLike.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg hA.posSemidef)).2
  have hWr : (complexRepresentation (D - Bᴴ * A⁻¹ʳ * B)).det.im = 0 :=
    (RCLike.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg hW)).2
  simp only [Complex.mul_re, hAr, hWr, zero_mul, sub_zero]
  exact Real.sqrt_mul hA.posSemidef.det_re_nonneg _

/-- Exact noncommutative block factorization around an invertible leading block. -/
theorem schur_factorization {A : Matrix m m ℍ[ℝ]}
    (hA : PosDef A) (B : Matrix m n ℍ[ℝ]) (D : Matrix n n ℍ[ℝ]) :
    Matrix.fromBlocks A B Bᴴ D =
      (Matrix.fromBlocks 1 (A⁻¹ʳ * B) 0 1)ᴴ *
        Matrix.fromBlocks A 0 0 (D - Bᴴ * A⁻¹ʳ * B) *
          Matrix.fromBlocks 1 (A⁻¹ʳ * B) 0 1 := by
  have hAi : (A⁻¹ʳ)ᴴ = A⁻¹ʳ := hA.ringInverse.isHermitian.eq
  have hAB : A * (A⁻¹ʳ * B) = B := by
    rw [← Matrix.mul_assoc, Ring.mul_inverse_cancel A hA.isUnit, Matrix.one_mul]
  have hBA : Bᴴ * A⁻¹ʳ * A = Bᴴ := by
    rw [Matrix.mul_assoc, Ring.inverse_mul_cancel A hA.isUnit, Matrix.mul_one]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, hAi, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, hAB, hBA]
  simp only [Matrix.mul_assoc]
  congr 1
  abel

theorem posDef_fromBlocks_zero_iff
    (A : Matrix m m ℍ[ℝ]) (D : Matrix n n ℍ[ℝ]) :
    PosDef (Matrix.fromBlocks A 0 0 D) ↔ PosDef A ∧ PosDef D := by
  rw [posDef_iff_quadratic, posDef_iff_quadratic, posDef_iff_quadratic]
  constructor
  · rintro ⟨hH, hQ⟩
    refine ⟨⟨hH.submatrix Sum.inl, fun x hx => ?_⟩,
      ⟨hH.submatrix Sum.inr, fun x hx => ?_⟩⟩
    · have hx' : Sum.elim x (0 : n → ℍ[ℝ]) ≠ 0 := by
        intro h
        apply hx
        exact congrArg (fun f => f ∘ Sum.inl) h
      simpa [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.zero_mulVec] using hQ (Sum.elim x 0) hx'
    · have hx' : Sum.elim (0 : m → ℍ[ℝ]) x ≠ 0 := by
        intro h
        apply hx
        exact congrArg (fun f => f ∘ Sum.inr) h
      simpa [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.zero_mulVec] using hQ (Sum.elim 0 x) hx'
  · rintro ⟨⟨hA, hQA⟩, ⟨hD, hQD⟩⟩
    refine ⟨?_, fun x hx => ?_⟩
    · simpa [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.eq, hD.eq]
    have hsplit : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by funext i; cases i <;> rfl
    have hquad : (star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x)).re =
        (star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl))).re +
          (star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr))).re := by
      rw [hsplit]
      simp [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
    rw [hquad]
    by_cases ha : x ∘ Sum.inl = 0
    · have hd : x ∘ Sum.inr ≠ 0 := by
        intro hd
        apply hx
        rw [hsplit, ha, hd]
        funext i
        cases i <;> rfl
      simpa [ha] using hQD _ hd
    · have hna : 0 < (star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl))).re := hQA _ ha
      by_cases hd : x ∘ Sum.inr = 0
      · simpa [hd] using hna
      · exact add_pos hna (hQD _ hd)

theorem posDef_schur_iff {A : Matrix m m ℍ[ℝ]}
    (hA : PosDef A) (B : Matrix m n ℍ[ℝ]) (D : Matrix n n ℍ[ℝ]) :
    PosDef (Matrix.fromBlocks A B Bᴴ D) ↔ PosDef (D - Bᴴ * A⁻¹ʳ * B) := by
  let R : Matrix (m ⊕ n) (m ⊕ n) ℍ[ℝ] := Matrix.fromBlocks 1 (A⁻¹ʳ * B) 0 1
  have hR : IsUnit R := by
    let U : (Matrix (m ⊕ n) (m ⊕ n) ℍ[ℝ])ˣ :=
      { val := R
        inv := Matrix.fromBlocks 1 (-(A⁻¹ʳ * B)) 0 1
        val_inv := by
          dsimp [R]
          rw [Matrix.fromBlocks_multiply]
          simp
        inv_val := by
          dsimp [R]
          rw [Matrix.fromBlocks_multiply]
          simp }
    exact U.isUnit
  rw [schur_factorization hA B D]
  change (complexRepresentation (Rᴴ * Matrix.fromBlocks A 0 0
    (D - Bᴴ * A⁻¹ʳ * B) * R)).PosDef ↔ _
  have hcR : IsUnit (complexRepresentation R) :=
    hR.map complexRepresentationStarAlgHom.toMonoidHom
  rw [complexRepresentation_congruence]
  exact hcR.posDef_star_left_conjugate_iff.trans
    ((posDef_fromBlocks_zero_iff A _).trans (and_iff_right hA))

/-- The actual full conditional matrix in Equation (23), on a sum index. -/
def regressionMatrix {q r : ℕ}
    (S : Matrix (Fin q) (Fin q) ℍ[ℝ])
    (W : Matrix (Fin r) (Fin r) ℍ[ℝ]) (Z : Matrix (Fin q) (Fin r) ℍ[ℝ]) :
    Matrix (Fin q ⊕ Fin r) (Fin q ⊕ Fin r) ℍ[ℝ] :=
  Matrix.fromBlocks S (sqrt S * Z) (Zᴴ * sqrt S) (W + Zᴴ * Z)

theorem regressionMatrix_posDef {q r : ℕ}
    {S : Matrix (Fin q) (Fin q) ℍ[ℝ]} {W : Matrix (Fin r) (Fin r) ℍ[ℝ]}
    (hS : PosDef S) (hW : PosDef W) (Z : Matrix (Fin q) (Fin r) ℍ[ℝ]) :
    PosDef (regressionMatrix S W Z) := by
  have hroot : (sqrt S)ᴴ = sqrt S := hS.sqrt.isHermitian.eq
  have hcancel : sqrt S * S⁻¹ʳ * sqrt S = 1 := by
    have hSi : S⁻¹ʳ = (sqrt S)⁻¹ʳ * (sqrt S)⁻¹ʳ := by
      calc
        S⁻¹ʳ = (sqrt S * sqrt S)⁻¹ʳ := congrArg Ring.inverse (sqrt_mul_self hS.posSemidef).symm
        _ = _ := Ring.inverse_mul (Or.inl hS.sqrt.isUnit)
    rw [hSi]
    simp only [← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hS.sqrt.isUnit,
      Matrix.one_mul, Ring.inverse_mul_cancel _ hS.sqrt.isUnit]
  unfold regressionMatrix
  rw [show Zᴴ * sqrt S = (sqrt S * Z)ᴴ by simp [hroot], posDef_schur_iff hS]
  convert hW using 1
  simp only [Matrix.conjTranspose_mul, hroot]
  rw [show Zᴴ * sqrt S * S⁻¹ʳ * (sqrt S * Z) = Zᴴ * Z by
    calc
      _ = Zᴴ * (sqrt S * S⁻¹ʳ * sqrt S) * Z := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcancel, Matrix.mul_one]]
  exact add_sub_cancel_right W (Zᴴ * Z)

end Wishart.QuaternionMatrix
end
end CanonicalSource12

section CanonicalSource13
/- Source: Wishart/FieldSchurDensity.lean -/




/-!
# The literal field Wishart density in Schur coordinates

The determinant, trace, positive support, and real Jacobian are computed for
the actual complex/quaternion block matrices.  The resulting factorization is
the one needed for arbitrary real shape, not just integer Gaussian samples.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal

namespace Wishart.FieldDensity

def rectangularNormSquare {F : Type*} [Norm F] {p q : ℕ}
    (Z : Matrix (Fin p) (Fin q) F) : ℝ := ∑ i, ∑ j, ‖Z i j‖ ^ 2

theorem power_exp_schur_factor {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (a b c s t u : ℝ) :
    (x * y) ^ a * Real.exp (-c * (s + t + u)) * x ^ b =
      (x ^ (a + b) * Real.exp (-c * s)) *
        (y ^ a * Real.exp (-c * t)) * Real.exp (-c * u) := by
  rw [Real.mul_rpow hx.le hy.le, Real.rpow_add hx]
  have he : -c * (s + t + u) = (-c * s + -c * t) + -c * u := by ring
  rw [he, Real.exp_add, Real.exp_add]
  ring

theorem trace_submatrix_equiv {F n m : Type*} [AddCommMonoid F]
    [Fintype n] [Fintype m] (e : n ≃ m) (A : Matrix m m F) :
    (A.submatrix e e).trace = A.trace :=
  e.sum_comp fun i => A i i

end Wishart.FieldDensity

namespace Wishart.ComplexMatrix
open Wishart.FieldDensity

variable {p q : ℕ}

theorem sqrt_inverse_sqrt {S : Matrix (Fin p) (Fin p) ℂ} (hS : S.PosDef) :
    CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ * CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) = 1 := by
  have hR : IsUnit (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ)) := (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit
  letI := hR.invertible
  have hsq := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hi : (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ = (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ))⁻¹ * (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ))⁻¹ := by
    calc
      (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ = (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ))⁻¹ := congrArg Inv.inv hsq.symm
      _ = _ := Matrix.mul_inv_rev _ _
  rw [hi]
  simp only [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul,
    Matrix.inv_mul_of_invertible]

theorem posDef_schur_iff {S : Matrix (Fin p) (Fin p) ℂ} (hS : S.PosDef)
    (B : Matrix (Fin p) (Fin q) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    (Matrix.fromBlocks S B Bᴴ D).PosDef ↔ (D - Bᴴ * (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ * B).PosDef := by
  letI := hS.isUnit.invertible
  have hd : (Matrix.fromBlocks S B Bᴴ D).det = S.det * (D - Bᴴ * (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ * B).det := by
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  constructor
  · intro h
    have hpsd := (Matrix.PosDef.fromBlocks₁₁ B D hS).mp h.posSemidef
    apply hpsd.posDef_iff_det_ne_zero.mpr
    intro hz
    have hn := h.det_pos.ne'
    rw [hd, hz, mul_zero] at hn
    exact hn rfl
  · intro h
    have hpsd := (Matrix.PosDef.fromBlocks₁₁ B D hS).mpr h.posSemidef
    apply hpsd.posDef_iff_det_ne_zero.mpr
    rw [hd]
    exact mul_ne_zero hS.det_pos.ne' h.det_pos.ne'

def schurInput (S : Hermitian p) (W : Hermitian q)
    (Z : Matrix (Fin p) (Fin q) ℂ) : Hermitian (p + q) :=
  Wishart.FieldHermitian.fromBlocks ℂ
    (S, CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z,
      ⟨(W : Matrix (Fin q) (Fin q) ℂ) + Zᴴ * Z,
        (WishartVerification.hermitian_matrix_coe W).add (Matrix.isHermitian_conjTranspose_mul_self Z)⟩)

theorem schur_remainder (S : Hermitian p)
    (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef)
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (W : Matrix (Fin q) (Fin q) ℂ) + Zᴴ * Z -
      (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z)ᴴ * (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ * (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z) = W := by
  have hroot := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (S : Matrix (Fin p) (Fin p) ℂ))).isHermitian
  simp only [Matrix.conjTranspose_mul, hroot.eq]
  have hc : Zᴴ * CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ * (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z) = Zᴴ * Z := by
    calc
      _ = Zᴴ * (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * (S : Matrix (Fin p) (Fin p) ℂ)⁻¹ * CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ)) * Z := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrt_inverse_sqrt hS, Matrix.mul_one]
  rw [hc, add_sub_cancel_right]

theorem schurInput_posDef_iff (S : Hermitian p)
    (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef)
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℂ).PosDef ↔
      (W : Matrix (Fin q) (Fin q) ℂ).PosDef := by
  let M := Matrix.fromBlocks (S : Matrix (Fin p) (Fin p) ℂ) (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z)
    (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z)ᴴ ((W : Matrix (Fin q) (Fin q) ℂ) + Zᴴ * Z)
  have hreindex : (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).PosDef ↔ M.PosDef := by
    constructor
    · intro h
      simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id] using h.submatrix finSumFinEquiv.injective
    · exact fun h => h.submatrix finSumFinEquiv.symm.injective
  change (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).PosDef ↔ _
  rw [hreindex, posDef_schur_iff hS, schur_remainder S hS W Z]

theorem realDeterminant_schurInput (S : Hermitian p)
    (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef)
    (W : Hermitian q) (hW : (W : Matrix (Fin q) (Fin q) ℂ).PosDef)
    (Z : Matrix (Fin p) (Fin q) ℂ) :
    realDeterminant (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) = realDeterminant (S : Matrix (Fin p) (Fin p) ℂ) * realDeterminant (W : Matrix (Fin q) (Fin q) ℂ) := by
  letI := hS.isUnit.invertible
  unfold schurInput Wishart.FieldHermitian.fromBlocks realDeterminant
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    schur_remainder S hS W Z, Complex.mul_re]
  have himS := (RCLike.nonneg_iff.mp hS.posSemidef.det_nonneg).2
  have himW := (RCLike.nonneg_iff.mp hW.posSemidef.det_nonneg).2
  change (S : Matrix (Fin p) (Fin p) ℂ).det.re * (W : Matrix (Fin q) (Fin q) ℂ).det.re -
    (S : Matrix (Fin p) (Fin p) ℂ).det.im * (W : Matrix (Fin q) (Fin q) ℂ).det.im = _
  change (S : Matrix (Fin p) (Fin p) ℂ).det.im = 0 at himS
  change (W : Matrix (Fin q) (Fin q) ℂ).det.im = 0 at himW
  rw [himS, himW, zero_mul, sub_zero]

theorem trace_schurInput (S : Hermitian p) (W : Hermitian q)
    (Z : Matrix (Fin p) (Fin q) ℂ) :
    (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℂ).trace.re =
      (S : Matrix (Fin p) (Fin p) ℂ).trace.re +
        (W : Matrix (Fin q) (Fin q) ℂ).trace.re + rectangularNormSquare Z := by
  change ((Matrix.fromBlocks (S : Matrix (Fin p) (Fin p) ℂ)
    (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z)
    (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z)ᴴ
    ((W : Matrix (Fin q) (Fin q) ℂ) + Zᴴ * Z)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm).trace.re = _
  rw [trace_submatrix_equiv]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  change Complex.reCLM
    ((∑ i, (S : Matrix (Fin p) (Fin p) ℂ) i i) +
      ∑ j, ((W : Matrix (Fin q) (Fin q) ℂ) j j + ∑ i, star (Z i j) * Z i j)) = _
  have hnorm (z : ℂ) : Complex.reCLM (star z * z) = ‖z‖ ^ 2 := by
    change (star z * z).re = _
    simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [map_add, map_sum, hnorm, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp [rectangularNormSquare, Complex.reCLM_apply, add_assoc]

theorem wishartWeight_schur (α : ℝ) (S : Hermitian p)
    (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef)
    (W : Hermitian q) (hW : (W : Matrix (Fin q) (Fin q) ℂ).PosDef)
    (Z : Matrix (Fin p) (Fin q) ℂ) :
    wishartWeight α 1 (schurInput S W Z) * ENNReal.ofReal (realDeterminant (S : Matrix (Fin p) (Fin p) ℂ) ^ (q : ℝ)) =
      wishartWeight α 1 S * wishartWeight (α - p) 1 W *
        ENNReal.ofReal (Real.exp (-rectangularNormSquare Z)) := by
  have hX := (schurInput_posDef_iff S hS W Z).mpr hW
  have hdS : 0 < realDeterminant (S : Matrix (Fin p) (Fin p) ℂ) := realDeterminant_pos hS
  have hdW : 0 < realDeterminant (W : Matrix (Fin q) (Fin q) ℂ) := realDeterminant_pos hW
  simp only [wishartWeight, if_pos hX, if_pos hS, if_pos hW, inv_one,
    Matrix.one_mul, realDeterminant_schurInput S hS W hW Z, trace_schurInput]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply congrArg ENNReal.ofReal
  have h := power_exp_schur_factor (realDeterminant_pos hS) (realDeterminant_pos hW)
    (α - (p + q : ℕ)) (q : ℝ) 1
    (S : Matrix (Fin p) (Fin p) ℂ).trace.re
    (W : Matrix (Fin q) (Fin q) ℂ).trace.re (rectangularNormSquare Z)
  convert h using 1 <;> push_cast <;> ring

theorem wishartWeight_schur_all (α : ℝ) (S : Hermitian p)
    (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef)
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℂ) :
    wishartWeight α 1 (schurInput S W Z) * ENNReal.ofReal (realDeterminant (S : Matrix (Fin p) (Fin p) ℂ) ^ (q : ℝ)) =
      wishartWeight α 1 S * wishartWeight (α - p) 1 W *
        ENNReal.ofReal (Real.exp (-rectangularNormSquare Z)) := by
  by_cases hW : (W : Matrix (Fin q) (Fin q) ℂ).PosDef
  · exact wishartWeight_schur α S hS W hW Z
  · have hX : ¬ (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℂ).PosDef :=
      fun h => hW ((schurInput_posDef_iff S hS W Z).mp h)
    simp only [wishartWeight, if_neg hX, if_neg hW, zero_mul, mul_zero]

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open Wishart.FieldDensity

variable {p q : ℕ}

theorem complexRepresentation_submatrix {n m : Type*}
    (A : Matrix m m ℍ[ℝ]) (e : n → m) :
    complexRepresentation (A.submatrix e e) =
      (complexRepresentation A).submatrix (fun i => (e i.1, i.2))
        (fun i => (e i.1, i.2)) := rfl

theorem positiveDeterminant_submatrix_equiv {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix m m ℍ[ℝ]) (e : n ≃ m) :
    positiveDeterminant (A.submatrix e e) = positiveDeterminant A := by
  unfold positiveDeterminant
  rw [complexRepresentation_submatrix]
  change Real.sqrt (((complexRepresentation A).submatrix
    (e.prodCongr (Equiv.refl (Fin 2))) (e.prodCongr (Equiv.refl (Fin 2)))).det.re) = _
  rw [Matrix.det_submatrix_equiv_self]

theorem PosDef.submatrix_equiv {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {A : Matrix m m ℍ[ℝ]} (hA : PosDef A) (e : n ≃ m) : PosDef (A.submatrix e e) := by
  unfold PosDef
  rw [complexRepresentation_submatrix]
  exact hA.submatrix (e.prodCongr (Equiv.refl (Fin 2))).injective

theorem sqrt_inverse_sqrt {S : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hS : PosDef S) :
    sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * (S : Matrix (Fin p) (Fin p) ℍ[ℝ])⁻¹ʳ * sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) = 1 := by
  rw [show (S : Matrix (Fin p) (Fin p) ℍ[ℝ])⁻¹ʳ = (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))⁻¹ʳ * (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))⁻¹ʳ by
    calc
        (S : Matrix (Fin p) (Fin p) ℍ[ℝ])⁻¹ʳ = (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))⁻¹ʳ := congrArg Ring.inverse (sqrt_mul_self hS.posSemidef).symm
        _ = _ := Ring.inverse_mul (Or.inl hS.sqrt.isUnit)]
  simp only [← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hS.sqrt.isUnit,
    Matrix.one_mul, Ring.inverse_mul_cancel _ hS.sqrt.isUnit]

def schurInput (S : Hermitian p) (W : Hermitian q)
    (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) : Hermitian (p + q) :=
  Wishart.FieldHermitian.fromBlocks ℍ[ℝ]
    (S, sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z,
      ⟨(W : Matrix (Fin q) (Fin q) ℍ[ℝ]) + Zᴴ * Z,
        (WishartVerification.hermitian_matrix_coe W).add (Matrix.isHermitian_conjTranspose_mul_self Z)⟩)

theorem schur_remainder (S : Hermitian p) (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    (W : Matrix (Fin q) (Fin q) ℍ[ℝ]) + Zᴴ * Z -
      (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z)ᴴ * (S : Matrix (Fin p) (Fin p) ℍ[ℝ])⁻¹ʳ * (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z) = W := by
  simp only [Matrix.conjTranspose_mul, hS.sqrt.isHermitian.eq]
  have hc : Zᴴ * sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * (S : Matrix (Fin p) (Fin p) ℍ[ℝ])⁻¹ʳ * (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z) = Zᴴ * Z := by
    calc
      _ = Zᴴ * (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * (S : Matrix (Fin p) (Fin p) ℍ[ℝ])⁻¹ʳ * sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ])) * Z := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrt_inverse_sqrt hS, Matrix.mul_one]
  rw [hc, add_sub_cancel_right]

theorem schurInput_posDef_iff (S : Hermitian p)
    (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    PosDef (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) ↔
      PosDef (W : Matrix (Fin q) (Fin q) ℍ[ℝ]) := by
  let M := Matrix.fromBlocks (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z)
    (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z)ᴴ ((W : Matrix (Fin q) (Fin q) ℍ[ℝ]) + Zᴴ * Z)
  have hreindex : PosDef (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) ↔ PosDef M := by
    constructor
    · intro h
      simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id] using h.submatrix_equiv finSumFinEquiv
    · exact fun h => h.submatrix_equiv finSumFinEquiv.symm
  change PosDef (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) ↔ _
  rw [hreindex, posDef_schur_iff hS, schur_remainder S hS W Z]

theorem positiveDeterminant_schurInput (S : Hermitian p)
    (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (W : Hermitian q) (hW : PosDef (W : Matrix (Fin q) (Fin q) ℍ[ℝ]))
    (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    positiveDeterminant (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) = positiveDeterminant (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * positiveDeterminant (W : Matrix (Fin q) (Fin q) ℍ[ℝ]) := by
  unfold schurInput Wishart.FieldHermitian.fromBlocks
  rw [positiveDeterminant_submatrix_equiv]
  rw [positiveDeterminant_schur hS _ _ (by simpa only [schur_remainder S hS W Z] using hW.posSemidef),
    schur_remainder S hS W Z]

theorem trace_schurInput (S : Hermitian p) (W : Hermitian q)
    (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]).trace.re =
      (S : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re +
        (W : Matrix (Fin q) (Fin q) ℍ[ℝ]).trace.re + rectangularNormSquare Z := by
  change ((Matrix.fromBlocks (S : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z)
    (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z)ᴴ
    ((W : Matrix (Fin q) (Fin q) ℍ[ℝ]) + Zᴴ * Z)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm).trace.re = _
  rw [trace_submatrix_equiv]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
    ((∑ i, (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) i i) +
      ∑ j, ((W : Matrix (Fin q) (Fin q) ℍ[ℝ]) j j + ∑ i, star (Z i j) * Z i j)) = _
  simp only [map_add, map_sum, Quaternion.star_mul_self,
    QuaternionAlgebra.re_coe, Quaternion.normSq_eq_norm_mul_self, ← pow_two,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have hSsum : (∑ i, (S : Matrix (Fin p) (Fin p) ℍ) i i).re =
      ∑ i, ((S : Matrix (Fin p) (Fin p) ℍ) i i).re :=
    map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ Finset.univ
  have hWsum : (∑ i, (W : Matrix (Fin q) (Fin q) ℍ) i i).re =
      ∑ i, ((W : Matrix (Fin q) (Fin q) ℍ) i i).re :=
    map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ Finset.univ
  rw [hSsum, hWsum]
  simp [rectangularNormSquare, QuaternionAlgebra.reₗ_apply, pow_two, add_assoc]

theorem wishartWeight_schur (α : ℝ) (S : Hermitian p)
    (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (W : Hermitian q) (hW : PosDef (W : Matrix (Fin q) (Fin q) ℍ[ℝ]))
    (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    wishartWeight α 1 (schurInput S W Z) * ENNReal.ofReal (positiveDeterminant (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (q : ℝ))) =
      wishartWeight α 1 S * wishartWeight (α - p) 1 W *
        ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z)) := by
  have hX := (schurInput_posDef_iff S hS W Z).mpr hW
  have hdS : 0 < positiveDeterminant (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) := hS.positiveDeterminant_pos
  have hdW : 0 < positiveDeterminant (W : Matrix (Fin q) (Fin q) ℍ[ℝ]) := hW.positiveDeterminant_pos
  simp only [wishartWeight, if_pos hX, if_pos hS, if_pos hW, Ring.inverse_one,
    Matrix.one_mul, positiveDeterminant_schurInput S hS W hW Z, trace_schurInput]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply congrArg ENNReal.ofReal
  have h := power_exp_schur_factor hS.positiveDeterminant_pos hW.positiveDeterminant_pos
    (2 * (α - (p + q : ℕ) + 1) - 1) (2 * (q : ℝ)) 2
    (S : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re
    (W : Matrix (Fin q) (Fin q) ℍ[ℝ]).trace.re (rectangularNormSquare Z)
  convert h using 1 <;> push_cast <;> ring

theorem wishartWeight_schur_all (α : ℝ) (S : Hermitian p)
    (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    wishartWeight α 1 (schurInput S W Z) * ENNReal.ofReal (positiveDeterminant (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (q : ℝ))) =
      wishartWeight α 1 S * wishartWeight (α - p) 1 W *
        ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z)) := by
  by_cases hW : PosDef (W : Matrix (Fin q) (Fin q) ℍ[ℝ])
  · exact wishartWeight_schur α S hS W hW Z
  · have hX : ¬ PosDef (schurInput S W Z : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) :=
      fun h => hW ((schurInput_posDef_iff S hS W Z).mp h)
    simp only [wishartWeight, if_neg hX, if_neg hW, zero_mul, mul_zero]

end Wishart.QuaternionMatrix
end
end CanonicalSource13

section CanonicalSource14
/- Source: Wishart/QuaternionFullColumnRank.lean -/



/-!
# The right-column rank convention for quaternion compressions

Quaternion matrices act on columns with coefficients on the right.
Consequently full column rank means injectivity of matrix-vector
multiplication. The general-semiring `Matrix.cRank` uses a left span of
columns and must not be substituted for this property. The faithful complex
representation gives an exact equivalence with ordinary complex column
injectivity, and hence the positivity and dimension facts used by whitening.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion Matrix ComplexOrder
namespace Wishart.QuaternionMatrix

variable {m n : Type*} [Fintype m] [Fintype n]

def FullColumnRank (B : Matrix m n ℍ[ℝ]) : Prop := Function.Injective B.mulVec

theorem fullColumnRank_iff_complexRepresentation (B : Matrix m n ℍ[ℝ]) :
    FullColumnRank B ↔ Function.Injective (complexRepresentation B).mulVec := by
  constructor
  · intro hB x y hxy
    have hq : B *ᵥ columnRepresentationInv x = B *ᵥ columnRepresentationInv y := by
      apply columnRepresentation_injective
      rw [columnRepresentation_mulVec, columnRepresentation_mulVec,
        columnRepresentation_representationInv, columnRepresentation_representationInv]
      exact hxy
    have h := congrArg columnRepresentation (hB hq)
    simpa only [columnRepresentation_representationInv] using h
  · intro hB x y hxy
    apply columnRepresentation_injective
    apply hB
    rw [← columnRepresentation_mulVec, ← columnRepresentation_mulVec, hxy]

theorem FullColumnRank.congruence_posDef {S : Matrix m m ℍ[ℝ]}
    (hS : PosDef S) {B : Matrix m n ℍ[ℝ]} (hB : FullColumnRank B) :
    PosDef (Bᴴ * S * B) := by
  unfold PosDef
  rw [complexRepresentation_congruence]
  exact Matrix.PosDef.conjTranspose_mul_mul_same hS
    ((fullColumnRank_iff_complexRepresentation B).mp hB)

theorem FullColumnRank.card_le {B : Matrix m n ℍ[ℝ]} (hB : FullColumnRank B) :
    Fintype.card n ≤ Fintype.card m := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (complexRepresentation B).mulVecLin)
    ((fullColumnRank_iff_complexRepresentation B).mp hB)
  simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_prod, Fintype.card_fin] at h
  omega

theorem fullColumnRank_of_orthonormal [DecidableEq n]
    (B : Matrix m n ℍ[ℝ]) (hB : Bᴴ * B = 1) : FullColumnRank B := by
  intro x y hxy
  have h := congrArg (fun z => Bᴴ *ᵥ z) hxy
  simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using h

theorem FullColumnRank.isUnit [DecidableEq n] {B : Matrix n n ℍ[ℝ]}
    (hB : FullColumnRank B) : IsUnit B :=
  isUnit_of_complexRepresentation_isUnit
    (Matrix.mulVec_injective_iff_isUnit.mp
      ((fullColumnRank_iff_complexRepresentation B).mp hB))

theorem fullColumnRank_of_isUnit [DecidableEq n] {B : Matrix n n ℍ[ℝ]}
    (hB : IsUnit B) : FullColumnRank B := Matrix.mulVec_injective_of_isUnit hB

theorem fullColumnRank_isUnit_iff [DecidableEq n] (B : Matrix n n ℍ[ℝ]) :
    FullColumnRank B ↔ IsUnit B :=
  ⟨FullColumnRank.isUnit, fullColumnRank_of_isUnit⟩

end Wishart.QuaternionMatrix
end
end CanonicalSource14

section CanonicalSource15
/- Source: Wishart/QuaternionRowSubmean.lean -/



/-!
# The quaternion rank-one row logarithm

The order of quaternion multiplication is retained throughout the row-pair
calculation. Its real quadratic expression has a global lower bound of one,
so the elementary quadratic lemma supplies the cross-term bound and the
four-dimensional submean inequality. The resulting determinant is the
positive determinant of the faithful complex representation; its equality
with the Moore spectral product is proved in the separate spectral layer.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix Quaternion RealInnerProductSpace BigOperators Classical Ring
namespace Wishart.QuaternionMatrix
open WishartVerification

variable {n : Type*} [Fintype n] [DecidableEq n]

def scalarRow (u : ℍ) (w : Matrix Unit n ℍ) : Matrix Unit n ℍ :=
  Matrix.of fun i j => u * w i j

@[simp] theorem scalarRow_apply (u : ℍ) (w : Matrix Unit n ℍ) (i : Unit) (j : n) :
    scalarRow u w i j = u * w i j := rfl

def rowPair (Q : Matrix n n ℍ) (a b : Matrix Unit n ℍ) : ℍ :=
  (a * Q⁻¹ʳ * bᴴ) () ()

@[simp] theorem rowPair_self_re (Q : Matrix n n ℍ) (a : Matrix Unit n ℍ) :
    (rowPair Q a a).re = rowQuadratic Q a := rfl

theorem rowPair_add_left (Q : Matrix n n ℍ) (a b c : Matrix Unit n ℍ) :
    rowPair Q (a + b) c = rowPair Q a c + rowPair Q b c := by
  simp only [rowPair, Matrix.add_mul, Matrix.add_apply]

theorem rowPair_add_right (Q : Matrix n n ℍ) (a b c : Matrix Unit n ℍ) :
    rowPair Q a (b + c) = rowPair Q a b + rowPair Q a c := by
  simp only [rowPair, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_apply]

theorem rowPair_scalar_left (Q : Matrix n n ℍ) (a b : Matrix Unit n ℍ) (u : ℍ) :
    rowPair Q (scalarRow u a) b = u * rowPair Q a b := by
  simp only [rowPair, Matrix.mul_apply, scalarRow_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem rowPair_scalar_right (Q : Matrix n n ℍ) (a b : Matrix Unit n ℍ) (u : ℍ) :
    rowPair Q a (scalarRow u b) = rowPair Q a b * star u := by
  simp only [rowPair, Matrix.mul_apply, scalarRow_apply, Matrix.conjTranspose_apply,
    star_mul, Finset.sum_mul, mul_assoc]

theorem rowPair_star {Q : Matrix n n ℍ} (hQ : PosDef Q)
    (a b : Matrix Unit n ℍ) : star (rowPair Q a b) = rowPair Q b a := by
  have h : (a * Q⁻¹ʳ * bᴴ)ᴴ = b * Q⁻¹ʳ * aᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQ.ringInverse.isHermitian.eq, Matrix.mul_assoc]
  simpa only [rowPair, Matrix.conjTranspose_apply] using congrArg (fun M => M () ()) h

theorem rowPair_self_real {Q : Matrix n n ℍ} (hQ : PosDef Q)
    (a : Matrix Unit n ℍ) : rowPair Q a a = (rowQuadratic Q a : ℍ) := by
  simpa only [rowPair, Matrix.diagonal_apply_eq] using
    congrArg (fun M => M () ()) (rowQuadratic_matrix hQ a)

theorem quaternion_scalar_quadratic (u : ℍ) (d : ℝ) :
    (u * ((d : ℍ) * star u)).re = d * ‖u‖ ^ 2 := by
  rw [← mul_assoc, Quaternion.mul_coe_eq_smul, smul_mul_assoc,
    Quaternion.re_smul, Quaternion.self_mul_star, Quaternion.re_coe,
    Quaternion.normSq_eq_norm_mul_self]
  ring

theorem quaternion_re_mul_eq_inner (β u : ℍ) :
    (u * β).re = inner ℝ (star β) (u) := by
  rw [Quaternion.inner_def, ← star_mul, Quaternion.re_star]

/-- The exact real quadratic arising from a quaternion row displacement. -/
theorem rowQuadratic_scalar_shift {Q : Matrix n n ℍ} (hQ : PosDef Q)
    (a v : Matrix Unit n ℍ) (u : ℍ) :
    rowQuadratic Q (a + scalarRow u v) =
      rowQuadratic Q a + 2 * inner ℝ (star (rowPair Q v a)) (u) +
        rowQuadratic Q v * ‖u‖ ^ 2 := by
  change (rowPair Q (a + scalarRow u v) (a + scalarRow u v)).re = _
  rw [rowPair_add_left, rowPair_add_right, rowPair_add_right,
    rowPair_scalar_right, rowPair_scalar_left, rowPair_scalar_left,
    rowPair_scalar_right]
  rw [← rowPair_star hQ v a, rowPair_self_real hQ v]
  simp only [Quaternion.re_add, rowPair_self_re]
  rw [← star_mul, Quaternion.re_star, quaternion_scalar_quadratic,
    quaternion_re_mul_eq_inner]
  ring

theorem ballSubmean_log_one_add_rowQuadratic {Q : Matrix n n ℍ} (hQ : PosDef Q)
    (a v : Matrix Unit n ℍ) :
    BallSubmean (fun u : ℍ => Real.log (1 + rowQuadratic Q (a + scalarRow u v))) := by
  have heq (u : ℍ) : 1 + rowQuadratic Q (a + scalarRow u v) =
      (1 + rowQuadratic Q a) + 2 * inner ℝ (star (rowPair Q v a)) (u) +
        rowQuadratic Q v * ‖u‖ ^ 2 := by
    rw [rowQuadratic_scalar_shift hQ]
    ring
  have h := ballSubmean_log_affineQuadratic_of_one_le
    (E := ℍ) (by simpa only [Quaternion.finrank_eq_four] using (by norm_num : 2 ≤ 4))
    (rowQuadratic_nonneg hQ v) (star (rowPair Q v a)) (fun u => by
      rw [← heq u]
      exact le_add_of_nonneg_right (rowQuadratic_nonneg hQ _))
  simpa only [heq] using h

theorem continuous_positiveDeterminant :
    Continuous (positiveDeterminant : Matrix n n ℍ → ℝ) := by
  exact Real.continuous_sqrt.comp
    ((Complex.continuous_re.comp (continuous_complexRepresentation.matrix_det)))

theorem positiveLogSubmean_rowDeterminant {Q : Matrix n n ℍ} (hQ : PosDef Q)
    (a v : Matrix Unit n ℍ) :
    PositiveLogSubmean (fun u : ℍ =>
      positiveDeterminant (Q + (a + scalarRow u v)ᴴ * (a + scalarRow u v))) := by
  have hpos (u : ℍ) : 0 <
      positiveDeterminant (Q + (a + scalarRow u v)ᴴ * (a + scalarRow u v)) := by
    rw [positiveDeterminant_rankOne hQ]
    exact mul_pos hQ.positiveDeterminant_pos
      (add_pos_of_pos_of_nonneg zero_lt_one (rowQuadratic_nonneg hQ _))
  refine ⟨hpos, continuous_positiveDeterminant.comp (by unfold scalarRow; fun_prop), ?_⟩
  have hlog : (fun u : ℍ => Real.log
      (positiveDeterminant (Q + (a + scalarRow u v)ᴴ * (a + scalarRow u v)))) =
      fun u => Real.log (positiveDeterminant Q) +
        Real.log (1 + rowQuadratic Q (a + scalarRow u v)) := by
    funext u
    rw [positiveDeterminant_rankOne hQ,
      Real.log_mul hQ.positiveDeterminant_pos.ne'
        (by have h := rowQuadratic_nonneg hQ (a + scalarRow u v); positivity)]
  rw [hlog]
  exact (BallSubmean.const _).add (ballSubmean_log_one_add_rowQuadratic hQ a v)

end Wishart.QuaternionMatrix
end
end CanonicalSource15

section CanonicalSource16
/- Source: Wishart/FieldScalarDensity.lean -/




/-!
# Actual scalar Gamma seeds for the complex and quaternion Wishart families

The one-dimensional field Hermitian space is identified with the real line.
The scalar laws are Gamma(α,1) and Gamma(2α,2), respectively.  All normalizers
are proved positive and finite against the actual chosen Hermitian Lebesgue
measure; no unproved matrix normalization is used.
-/

noncomputable section
open MeasureTheory.Measure
open MeasureTheory ProbabilityTheory Set
open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace WishartVerification.FieldDensity

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- Haar normalizations cancel from the normalized law under a linear
equivalence. This lemma also proves finiteness of the target raw density. -/
theorem normalized_transport_haar (e : E ≃L[ℝ] H)
    (μ : Measure E) (ν : Measure H) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    (f : E → ℝ≥0∞) (g : H → ℝ≥0∞) (hf : FiniteDensity μ f)
    (hcomp : ∀ x, g (e x) = f x) :
    FiniteDensity ν g ∧ normalized ν g = (normalized μ f).map e := by
  letI := isProbability_normalized hf
  let κ := (normalized μ f).map e
  haveI : IsProbabilityMeasure κ := by dsimp [κ]; infer_instance
  letI : IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  let c : NNReal := Measure.addHaarScalarFactor (μ.map e) ν
  have hmap : μ.map e = c • ν := Measure.isAddLeftInvariant_eq_smul _ _
  have hmap' : μ.map e = (c : ℝ≥0∞) • ν := hmap
  have hweight : (fun y => f (e.symm y)) = g := by
    funext y
    simpa only [e.apply_symm_apply] using (hcomp (e.symm y)).symm
  have hraw : (μ.withDensity f).map e = (c : ℝ≥0∞) • ν.withDensity g := by
    have h := e.toHomeomorph.toMeasurableEquiv.map_withDensity μ f
    change (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) at h
    rw [hweight, hmap', withDensity_smul_measure] at h
    exact h
  have hlaw : κ = ((normalizer μ f)⁻¹ * (c : ℝ≥0∞)) • ν.withDensity g := by
    dsimp [κ, normalized]
    rw [Measure.map_smul _ e.continuous.measurable.aemeasurable, hraw, smul_smul]
  obtain ⟨hg0, hgtop, hnorm⟩ :=
    WishartVerification.normalized_ennreal_density_of_probability κ ν g _ hlaw
  exact ⟨⟨pos_iff_ne_zero.mpr hg0, lt_top_iff_ne_top.mpr hgtop⟩, hnorm.symm⟩

/-- A constant density factor is absorbed by normalization. Both source and
target refer to their specified ordinary Haar reference measures. -/
theorem normalized_transport_haar_scaled (e : E ≃L[ℝ] H)
    (μ : Measure E) (ν : Measure H) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    (f : E → ℝ≥0∞) (g : H → ℝ≥0∞) (hf : FiniteDensity μ f)
    {a : ℝ≥0∞} (ha0 : 0 < a) (hatop : a < ⊤)
    (hcomp : ∀ x, g (e x) = a * f x) :
    FiniteDensity ν g ∧ normalized ν g = (normalized μ f).map e := by
  have ha := constant_mul hf ha0 hatop
  have h := normalized_transport_haar e μ ν (fun x => a * f x) g ha.2.1 hcomp
  exact ⟨h.1, by rw [h.2, ha.2.2]⟩

def gammaKernel (a r x : ℝ) : ℝ≥0∞ :=
  if 0 < x then ENNReal.ofReal (x ^ (a - 1) * Real.exp (-(r * x))) else 0

theorem measurable_gammaKernel (a r : ℝ) : Measurable (gammaKernel a r) := by
  unfold gammaKernel
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const

theorem gammaMeasure_eq_scaled_kernel {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    gammaMeasure a r = ENNReal.ofReal (r ^ a / Real.Gamma a) •
      volume.withDensity (gammaKernel a r) := by
  have hcoef : 0 ≤ r ^ a / Real.Gamma a :=
    div_nonneg (Real.rpow_nonneg hr.le _) (Real.Gamma_pos_of_pos ha).le
  have hpdf : gammaPDF a r =ᵐ[volume] fun x =>
      ENNReal.ofReal (r ^ a / Real.Gamma a) * gammaKernel a r x := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
    by_cases hxp : 0 < x
    · rw [gammaPDF, gammaPDFReal, if_pos hxp.le, gammaKernel, if_pos hxp]
      rw [mul_assoc, ENNReal.ofReal_mul hcoef]
    · have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx
      simp only [gammaPDF_of_neg hxn, gammaKernel, if_neg hxp, mul_zero]
  rw [gammaMeasure, withDensity_congr_ae hpdf]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

theorem finiteDensity_gammaKernel {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    FiniteDensity volume (gammaKernel a r) := by
  letI := isProbabilityMeasure_gammaMeasure ha hr
  obtain ⟨h0, htop, _⟩ :=
    WishartVerification.normalized_ennreal_density_of_probability
      (gammaMeasure a r) volume (gammaKernel a r) _ (gammaMeasure_eq_scaled_kernel ha hr)
  exact ⟨pos_iff_ne_zero.mpr h0, lt_top_iff_ne_top.mpr htop⟩

theorem normalized_gammaKernel {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    normalized volume (gammaKernel a r) = gammaMeasure a r := by
  letI := isProbabilityMeasure_gammaMeasure ha hr
  exact (WishartVerification.normalized_ennreal_density_of_probability
    (gammaMeasure a r) volume (gammaKernel a r) _
      (gammaMeasure_eq_scaled_kernel ha hr)).2.2.symm

end WishartVerification.FieldDensity

namespace Wishart.ComplexMatrix
open WishartVerification.FieldDensity

def scalarHermitian (t : ℝ) : Hermitian 1 :=
  ⟨Matrix.diagonal (fun _ : Fin 1 => (t : ℂ)), by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (t : ℂ) = (t : ℂ)
    simp⟩

def scalarHermitianLinearEquiv : ℝ ≃ₗ[ℝ] Hermitian 1 where
  toFun := scalarHermitian
  invFun X := (X.val 0 0).re
  left_inv t := by simp [scalarHermitian]
  right_inv X := by
    apply Subtype.ext
    funext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    have hstar : star (X.val 0 0) = X.val 0 0 :=
      congrFun (congrFun (WishartVerification.hermitian_matrix_coe X).eq 0) 0
    apply Complex.ext
    · simp [scalarHermitian]
    · have h := congrArg Complex.im hstar
      simp only [Complex.star_def, Complex.conj_im] at h
      simp only [scalarHermitian, Matrix.diagonal_apply_eq, Complex.ofReal_im]
      linarith
  map_add' a b := by
    apply Subtype.ext
    funext i j
    fin_cases i
    fin_cases j
    simp [scalarHermitian]
  map_smul' a b := by
    apply Subtype.ext
    funext i j
    fin_cases i
    fin_cases j
    simp [scalarHermitian]

def scalarHermitianCL : ℝ ≃L[ℝ] Hermitian 1 := scalarHermitianLinearEquiv.toContinuousLinearEquiv

@[simp] theorem scalarHermitianCL_apply (t : ℝ) : scalarHermitianCL t = scalarHermitian t := rfl

theorem scalarHermitian_posDef_iff (t : ℝ) :
    (scalarHermitian t : Matrix (Fin 1) (Fin 1) ℂ).PosDef ↔ 0 < t := by
  change (Matrix.diagonal (fun _ : Fin 1 => (t : ℂ))).PosDef ↔ _
  rw [Matrix.posDef_diagonal_iff]
  simp only [forall_const]
  exact ⟨fun h => (RCLike.pos_iff.mp h).1, fun h => RCLike.pos_iff.mpr ⟨h, rfl⟩⟩

theorem wishartWeight_scalarHermitian (α t : ℝ) :
    wishartWeight α 1 (scalarHermitian t) = gammaKernel α 1 t := by
  unfold wishartWeight gammaKernel
  rw [scalarHermitian_posDef_iff]
  by_cases ht : 0 < t
  · simp [ht, scalarHermitian, realDeterminant, Matrix.det_diagonal, Matrix.trace]
  · simp only [if_neg ht]

theorem finiteDensity_wishart_one {α : ℝ} (hα : 0 < α) :
    FiniteDensity (hermitianLebesgue 1) (wishartWeight α 1) :=
  (normalized_transport_haar (E := ℝ) (H := Hermitian 1) scalarHermitianCL volume (hermitianLebesgue 1)
    (gammaKernel α 1) (wishartWeight α 1)
      (finiteDensity_gammaKernel hα zero_lt_one) (wishartWeight_scalarHermitian α)).1

theorem wishartMeasure_one_eq_gamma {α : ℝ} (hα : 0 < α) :
    wishartMeasure α (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      (gammaMeasure α 1).map scalarHermitian := by
  have h := (normalized_transport_haar (E := ℝ) (H := Hermitian 1) scalarHermitianCL volume (hermitianLebesgue 1)
    (gammaKernel α 1) (wishartWeight α 1)
      (finiteDensity_gammaKernel hα zero_lt_one) (wishartWeight_scalarHermitian α)).2
  rw [normalized_gammaKernel hα zero_lt_one] at h
  exact h

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open WishartVerification.FieldDensity

def scalarHermitian (t : ℝ) : Hermitian 1 :=
  ⟨Matrix.diagonal (fun _ : Fin 1 => (t : ℍ[ℝ])), by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (t : ℍ[ℝ]) = (t : ℍ[ℝ])
    simp⟩

def scalarHermitianLinearEquiv : ℝ ≃ₗ[ℝ] Hermitian 1 where
  toFun := scalarHermitian
  invFun X := (X.val 0 0).re
  left_inv t := by simp [scalarHermitian]
  right_inv X := by
    apply Subtype.ext
    funext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    have hstar : star (X.val 0 0) = X.val 0 0 :=
      congrFun (congrFun (WishartVerification.hermitian_matrix_coe X).eq 0) 0
    exact (Quaternion.star_eq_self.mp hstar).symm
  map_add' a b := by
    apply Subtype.ext
    funext i j
    fin_cases i
    fin_cases j
    simp [scalarHermitian]
  map_smul' a b := by
    apply Subtype.ext
    funext i j
    fin_cases i
    fin_cases j
    simp [scalarHermitian, Quaternion.coe_mul_eq_smul]

def scalarHermitianCL : ℝ ≃L[ℝ] Hermitian 1 := scalarHermitianLinearEquiv.toContinuousLinearEquiv

@[simp] theorem scalarHermitianCL_apply (t : ℝ) : scalarHermitianCL t = scalarHermitian t := rfl

theorem scalarHermitian_posDef_iff (t : ℝ) :
    PosDef (scalarHermitian t : Matrix (Fin 1) (Fin 1) ℍ[ℝ]) ↔ 0 < t := by
  unfold PosDef scalarHermitian
  rw [complexRepresentation_diagonal, Matrix.posDef_diagonal_iff]
  simp only [forall_const]
  exact ⟨fun h => (RCLike.pos_iff.mp h).1, fun h => RCLike.pos_iff.mpr ⟨h, rfl⟩⟩

theorem wishartWeight_scalarHermitian (α t : ℝ) :
    wishartWeight α 1 (scalarHermitian t) = gammaKernel (2 * α) 2 t := by
  unfold wishartWeight gammaKernel
  rw [scalarHermitian_posDef_iff]
  by_cases ht : 0 < t
  · simp only [if_pos ht]
    rw [show positiveDeterminant (scalarHermitian t : Matrix (Fin 1) (Fin 1) ℍ[ℝ]) = t by
      simpa [scalarHermitian] using positiveDeterminant_diagonal
        (fun _ : Fin 1 => t) (fun _ => ht.le)]
    simp [scalarHermitian, Matrix.trace]
  · simp only [if_neg ht]

set_option backward.isDefEq.respectTransparency false in
theorem finiteDensity_wishart_one {α : ℝ} (hα : 0 < α) :
    FiniteDensity (hermitianLebesgue 1) (wishartWeight α 1) :=
  (normalized_transport_haar (E := ℝ) (H := Hermitian 1) scalarHermitianCL volume (hermitianLebesgue 1)
    (gammaKernel (2 * α) 2) (wishartWeight α 1)
      (finiteDensity_gammaKernel (mul_pos two_pos hα) two_pos)
        (by intro t; rw [scalarHermitianCL_apply]; exact wishartWeight_scalarHermitian α t)).1

set_option backward.isDefEq.respectTransparency false in
theorem wishartMeasure_one_eq_gamma {α : ℝ} (hα : 0 < α) :
    wishartMeasure α (1 : Matrix (Fin 1) (Fin 1) ℍ[ℝ]) =
      (gammaMeasure (2 * α) 2).map scalarHermitian := by
  have h := (normalized_transport_haar (E := ℝ) (H := Hermitian 1) scalarHermitianCL volume (hermitianLebesgue 1)
    (gammaKernel (2 * α) 2) (wishartWeight α 1)
      (finiteDensity_gammaKernel (mul_pos two_pos hα) two_pos)
        (by intro t; rw [scalarHermitianCL_apply]; exact wishartWeight_scalarHermitian α t)).2
  rw [normalized_gammaKernel (mul_pos two_pos hα) two_pos] at h
  exact h

end Wishart.QuaternionMatrix
end
end CanonicalSource16

section CanonicalSource17
/- Source: Wishart/FieldMatrixGaussianDensity.lean -/



/-!
# The actual normalized field Gaussian matrix density

The source consists of independent Gaussian rows with the exact variance
`1 / dim_R F` from Section 7. Its ordinary rectangular Lebesgue density is
proportional to `exp(-(dim_R F)/2 * ∑ᵢⱼ ‖Zᵢⱼ‖²)`.  The proportionality is
derived from the ordinary real Gaussian density and real-linear Haar changes
of coordinates; normalization and the full probability law are conclusions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical Quaternion Matrix ENNReal Matrix.Norms.Frobenius

namespace Wishart.FieldGaussian
open WishartVerification.FieldDensity Wishart.FieldDensity

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [StarModule ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

def rowKernel (q : ℕ) (z : Row F q) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(Module.finrank ℝ F : ℝ) / 2 * ‖z‖ ^ 2))

def matrixKernel {p q : ℕ} (Z : Matrix (Fin p) (Fin q) F) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(Module.finrank ℝ F : ℝ) / 2 * rectangularNormSquare Z))

theorem measurable_rowKernel (q : ℕ) : Measurable (rowKernel F q) := by
  unfold rowKernel
  fun_prop

theorem measurable_matrixKernel (p q : ℕ) :
    Measurable (matrixKernel F : Matrix (Fin p) (Fin q) F → ℝ≥0∞) := by
  unfold matrixKernel rectangularNormSquare
  fun_prop

theorem gaussianRowWithFactor_one_density (q : ℕ)
    (hF : 0 < Module.finrank ℝ F) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F) =
      (volume : Measure (Row F q)).withDensity (fun z => c * rowKernel F q z) := by
  have hb : 0 < (Module.finrank ℝ F : ℝ) := by exact_mod_cast hF
  have hs : standardDeviation F ≠ 0 := by
    unfold standardDeviation
    exact inv_ne_zero (Real.sqrt_pos.mpr hb).ne'
  let L := (LinearEquiv.smulOfNeZero ℝ (Row F q) (standardDeviation F) hs).toContinuousLinearEquiv
  let c₁ := ENNReal.ofReal |(LinearMap.det (L : Row F q →ₗ[ℝ] Row F q))⁻¹|
  let c₂ := ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ (Row F q) : ℝ) / 2))
  refine ⟨c₁ * c₂, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  have hL : (normalizedRowFactorCLM F (1 : Matrix (Fin q) (Fin q) F) : Row F q → Row F q) = L := by
    funext z
    ext j
    simp [normalizedRowFactorCLM, rowFactorCLM_apply, L, Matrix.one_apply]
  have hsymm (z : Row F q) : L.symm z = Real.sqrt (Module.finrank ℝ F) • z := by
    apply L.injective
    rw [L.apply_symm_apply]
    change z = standardDeviation F • (Real.sqrt (Module.finrank ℝ F) • z)
    rw [smul_smul, standardDeviation, inv_mul_cancel₀ (Real.sqrt_pos.mpr hb).ne', one_smul]
  have hnorm (z : Row F q) :
      ‖L.symm z‖ ^ 2 = (Module.finrank ℝ F : ℝ) * ‖z‖ ^ 2 := by
    rw [hsymm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt hb.le]
  unfold gaussianRowWithFactor
  rw [hL, TauCeti.Probability.stdGaussian_eq_withDensity_norm]
  have hmap := Measure.map_affine_withDensity (volume : Measure (Row F q)) L 0
    (fun z => ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ (Row F q) : ℝ) / 2) *
      Real.exp (-‖z‖ ^ 2 / 2)))
  simp only [zero_add, sub_zero] at hmap
  rw [hmap]
  apply congrArg ((volume : Measure (Row F q)).withDensity)
  funext z
  rw [hnorm]
  dsimp [c₁, c₂, rowKernel]
  rw [show -((Module.finrank ℝ F : ℝ) * ‖z‖ ^ 2) / 2 =
    -(Module.finrank ℝ F : ℝ) / 2 * ‖z‖ ^ 2 by ring]
  rw [ENNReal.ofReal_mul (by positivity)]
  exact (mul_assoc _ _ _).symm

def rowsMatrixLinearEquiv (p q : ℕ) :
    (Fin p → Row F q) ≃ₗ[ℝ] Matrix (Fin p) (Fin q) F where
  toFun := rowsMatrix F
  invFun Z i := WithLp.toLp 2 (Z i)
  left_inv z := by ext i j; rfl
  right_inv Z := by ext i j; rfl
  map_add' a b := rfl
  map_smul' r a := rfl

def rowsMatrixCL (p q : ℕ) :
    (Fin p → Row F q) ≃L[ℝ] Matrix (Fin p) (Fin q) F :=
  (rowsMatrixLinearEquiv F p q).toContinuousLinearEquiv

def matrixGaussian (p q : ℕ) : Measure (Matrix (Fin p) (Fin q) F) :=
  (Measure.pi (fun _ : Fin p => gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F))).map
    (rowsMatrix F)

instance matrixGaussian_isProbability (p q : ℕ) : IsProbabilityMeasure (matrixGaussian F p q) := by
  unfold matrixGaussian
  infer_instance

theorem matrixKernel_rowsMatrix (p q : ℕ) (z : Fin p → Row F q) :
    matrixKernel F (rowsMatrix F z) = ∏ i : Fin p, rowKernel F q (z i) := by
  simp only [matrixKernel, rowKernel]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _)]
  rw [← Real.exp_sum]
  congr 2
  simp only [PiLp.norm_sq_eq_of_L2, rectangularNormSquare, rowsMatrix, Matrix.of_apply]
  rw [Finset.mul_sum]

theorem normalized_product_rowKernel (p q : ℕ) (hF : 0 < Module.finrank ℝ F) :
    let μ := Measure.pi (fun _ : Fin p => (volume : Measure (Row F q)))
    let w := fun z : Fin p → Row F q => ∏ i, rowKernel F q (z i)
    FiniteDensity μ w ∧ normalized μ w =
      Measure.pi (fun _ : Fin p => gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)) := by
  dsimp only
  obtain ⟨c, hctop, hc⟩ := gaussianRowWithFactor_one_density F q hF
  have hrow : IsProbabilityMeasure ((volume : Measure (Row F q)).withDensity
      (fun z => c * rowKernel F q z)) := by rw [← hc]; infer_instance
  letI := hrow
  have hpi : Measure.pi (fun _ : Fin p => gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)) =
      c ^ p • (Measure.pi (fun _ : Fin p => (volume : Measure (Row F q)))).withDensity
        (fun z => ∏ i, rowKernel F q (z i)) := by
    simp_rw [hc]
    rw [TauCeti.pi_withDensity (fun _ : Fin p => (volume : Measure (Row F q)))
      (f := fun _ z => c * rowKernel F q z)
      (fun _ => measurable_const.mul (measurable_rowKernel F q))]
    have heq : (fun z : Fin p → Row F q => ∏ i, c * rowKernel F q (z i)) =
        c ^ p • (fun z : Fin p → Row F q => ∏ i, rowKernel F q (z i)) := by
      funext z
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Pi.smul_apply, smul_eq_mul]
    rw [heq, withDensity_smul' _ _ (ENNReal.pow_ne_top hctop)]
  obtain ⟨h0, htop, hnorm⟩ :=
    WishartVerification.normalized_ennreal_density_of_probability _ _ _ _ hpi
  exact ⟨⟨pos_iff_ne_zero.mpr h0, lt_top_iff_ne_top.mpr htop⟩, hnorm.symm⟩

/-- Use the algebra induced by the existing real scalar action, so the
Gaussian inner product and the rectangular Haar measure share one module. -/
@[reducible] local instance compatibleNormedAlgebra : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le

set_option backward.isDefEq.respectTransparency false in
local instance matrixBorelSpace (p q : ℕ) : BorelSpace (Matrix (Fin p) (Fin q) F) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → F))

set_option backward.isDefEq.respectTransparency false in
/-- The actual matrix Gaussian source is the normalized literal Gaussian
density against rectangular field Lebesgue measure. -/
theorem finiteDensity_matrixKernel_and_law (p q : ℕ) (hF : 0 < Module.finrank ℝ F) :
    FiniteDensity (Wishart.FieldHermitian.rectangularLebesgue F p q) (matrixKernel F) ∧
      normalized (Wishart.FieldHermitian.rectangularLebesgue F p q) (matrixKernel F) =
        matrixGaussian F p q := by
  letI : BorelSpace (Matrix (Fin p) (Fin q) F) := inferInstanceAs (BorelSpace (Fin p → Fin q → F))
  let μ := Measure.pi (fun _ : Fin p => (volume : Measure (Row F q)))
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp [μ]
    exact Measure.pi.isAddHaarMeasure (fun _ : Fin p => (volume : Measure (Row F q)))
  have hrow := normalized_product_rowKernel F p q hF
  have h := normalized_transport_haar (rowsMatrixCL F p q) μ
    (Wishart.FieldHermitian.rectangularLebesgue F p q)
    (fun z => ∏ i, rowKernel F q (z i)) (matrixKernel F) hrow.1
      (matrixKernel_rowsMatrix F p q)
  refine ⟨h.1, ?_⟩
  rw [h.2, hrow.2]
  rfl

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open WishartVerification.FieldDensity Wishart.FieldDensity

set_option backward.isDefEq.respectTransparency false in
theorem finiteDensity_standard_matrix_gaussian (p q : ℕ) :
    FiniteDensity (Wishart.FieldHermitian.rectangularLebesgue ℂ p q)
      (fun Z => ENNReal.ofReal (Real.exp (-rectangularNormSquare Z))) := by
  have h := (Wishart.FieldGaussian.finiteDensity_matrixKernel_and_law ℂ p q
    (by simp [Complex.finrank_real_complex])).1
  have hk : (Wishart.FieldGaussian.matrixKernel ℂ : Matrix (Fin p) (Fin q) ℂ → ℝ≥0∞) =
      (fun Z => ENNReal.ofReal (Real.exp (-rectangularNormSquare Z))) := by
    funext Z
    simp [Wishart.FieldGaussian.matrixKernel, Complex.finrank_real_complex]
  rw [hk] at h
  exact h

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open WishartVerification.FieldDensity Wishart.FieldDensity

set_option backward.isDefEq.respectTransparency false in
theorem finiteDensity_standard_matrix_gaussian (p q : ℕ) :
    FiniteDensity (Wishart.FieldHermitian.rectangularLebesgue ℍ[ℝ] p q)
      (fun Z => ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z))) := by
  have h := (Wishart.FieldGaussian.finiteDensity_matrixKernel_and_law ℍ[ℝ] p q
    (by simp [Quaternion.finrank_eq_four])).1
  have hk : (Wishart.FieldGaussian.matrixKernel ℍ[ℝ] : Matrix (Fin p) (Fin q) ℍ[ℝ] → ℝ≥0∞) =
      (fun Z => ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z))) := by
    funext Z
    norm_num [Wishart.FieldGaussian.matrixKernel, Quaternion.finrank_eq_four]
  rw [hk] at h
  exact h

end Wishart.QuaternionMatrix
end
end CanonicalSource17

section CanonicalSource18
/- Source: Wishart/PolynomialSubmeanAverage.lean -/



/-!
# Averaging submean functions with polynomial growth

The domination needed for Gaussian averaging is derived explicitly from the
norm moments of the noise and a polynomial bound on the joint function.
Neither continuity of the average nor Fubini is left as an assumption in the
resulting averaging theorem. The final radiality lemma uses an actual
measure-preserving transformation of the noise for each pair of radii.
-/

noncomputable section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace WishartVerification

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def JointPolynomialBound (F : E × V → ℝ) : Prop :=
  ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (z : E) (u : V), ‖F (z, u)‖ ≤ C * (1 + ‖z‖ + ‖u‖) ^ d

theorem integrable_norm_polynomial {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ) (C R : ℝ) (d : ℕ) :
    Integrable (fun z : E => C * (1 + ‖z‖ + R) ^ d) μ := by
  have h := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).add
    (HasAllFiniteMoments.const R)
  simpa only [Real.rpow_natCast] using
    ((h.rpow (show 0 ≤ (d : ℝ) by positivity)).const_mul C).integrable

theorem integrable_polynomial_section {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {F : E × V → ℝ} (hF : Continuous F) (hbound : JointPolynomialBound F) (u : V) :
    Integrable (fun z => F (z, u)) μ := by
  obtain ⟨d, C, hC, hb⟩ := hbound
  apply (integrable_norm_polynomial hμ C ‖u‖ d).mono'
    ((hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => hb z u

theorem continuous_integral_polynomial {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {F : E × V → ℝ} (hF : Continuous F) (hbound : JointPolynomialBound F) :
    Continuous (fun u => ∫ z, F (z, u) ∂μ) := by
  obtain ⟨d, C, hC, hb⟩ := hbound
  apply continuous_iff_continuousAt.mpr
  intro u
  apply continuousAt_of_dominated
    (bound := fun z => C * (1 + ‖z‖ + (‖u‖ + 1)) ^ d)
  · exact Filter.Eventually.of_forall fun v =>
      (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds u zero_lt_one] with v hv
    have hvnorm : ‖v‖ ≤ ‖u‖ + 1 := by
      have hd : ‖v - u‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hv
      calc
        ‖v‖ = ‖(v - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - u‖ + ‖u‖ := norm_add_le _ _
        _ ≤ ‖u‖ + 1 := by linarith
    exact Filter.Eventually.of_forall fun z => (hb z v).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (show 1 + ‖z‖ + ‖v‖ ≤ 1 + ‖z‖ + (‖u‖ + 1) by linarith) d) hC)
  · exact integrable_norm_polynomial hμ C (‖u‖ + 1) d
  · exact Filter.Eventually.of_forall fun z =>
      (hF.comp (continuous_const.prodMk continuous_id)).continuousAt

theorem integrable_polynomial_on_product_ball {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {F : E × V → ℝ} (hF : Continuous F) (hbound : JointPolynomialBound F)
    (u : V) {r : ℝ} (hr : 0 < r) :
    Integrable F (μ.prod (volume.restrict (ball u r))) := by
  obtain ⟨d, C, hC, hb⟩ := hbound
  letI : IsFiniteMeasure (volume.restrict (ball u r) : Measure V) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply ((integrable_norm_polynomial hμ C (‖u‖ + r) d).comp_fst
    (volume.restrict (ball u r))).mono' hF.aestronglyMeasurable
  have hball : ∀ᵐ w : E × V ∂μ.prod (volume.restrict (ball u r)), w.2 ∈ ball u r := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_ball)).mpr
    exact Filter.Eventually.of_forall fun z => ae_restrict_mem measurableSet_ball
  filter_upwards [hball] with w hw
  have hvnorm : ‖w.2‖ ≤ ‖u‖ + r := by
    have hd : ‖w.2 - u‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    calc
      ‖w.2‖ = ‖(w.2 - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖w.2 - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ ‖u‖ + r := by linarith
  exact (hb w.1 w.2).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (show 1 + ‖w.1‖ + ‖w.2‖ ≤ 1 + ‖w.1‖ + (‖u‖ + r) by linarith) d) hC)

/-- The submean property of a polynomial-growth average, with every
analytic interchange discharged by the explicit polynomial envelope. -/
theorem ballSubmean_integral_of_polynomial {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {F : E × V → ℝ} (hF : Continuous F) (hbound : JointPolynomialBound F)
    (hsub : ∀ᵐ z ∂μ, BallSubmean (fun u => F (z, u))) :
    BallSubmean (fun u => ∫ z, F (z, u) ∂μ) := by
  apply BallSubmean.integral μ (fun z u => F (z, u)) hsub
  · exact integrable_polynomial_section hμ hF hbound
  · intro u r hr
    exact integrable_polynomial_on_product_ball hμ hF hbound u hr
  · exact continuous_integral_polynomial hμ hF hbound

theorem radial_integral_of_noise_equivalences {μ : Measure E}
    {F : E × V → ℝ}
    (hphase : ∀ u v : V, ‖u‖ = ‖v‖ → ∃ T : E ≃ᵐ E,
      MeasurePreserving T μ μ ∧ ∀ z, F (z, u) = F (T z, v)) :
    ∀ u v : V, ‖u‖ = ‖v‖ → (∫ z, F (z, u) ∂μ) = ∫ z, F (z, v) ∂μ := by
  intro u v huv
  obtain ⟨T, hT, hF⟩ := hphase u v huv
  calc
    (∫ z, F (z, u) ∂μ) = ∫ z, F (T z, v) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hF)
    _ = ∫ z, F (z, v) ∂μ := hT.integral_comp' (fun z => F (z, v))

/-- The precise squared-radius conclusion of the one-row argument. In the
Wishart application the noise equivalences are left multiplication of the
Gaussian row by unit complex or quaternion scalars. -/
theorem monotone_integral_sqrt_smul_of_polynomial_submean [Nontrivial V]
    {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {F : E × V → ℝ} (hF : Continuous F) (hbound : JointPolynomialBound F)
    (hsub : ∀ᵐ z ∂μ, BallSubmean (fun u => F (z, u)))
    (hphase : ∀ u v : V, ‖u‖ = ‖v‖ → ∃ T : E ≃ᵐ E,
      MeasurePreserving T μ μ ∧ ∀ z, F (z, u) = F (T z, v)) (v : V) :
    MonotoneOn (fun t : ℝ => ∫ z, F (z, Real.sqrt t • v) ∂μ) (Ici 0) :=
  (ballSubmean_integral_of_polynomial hμ hF hbound hsub).monotoneOn_sqrt_smul
    (radial_integral_of_noise_equivalences hphase) v

end WishartVerification
end
end CanonicalSource18

section CanonicalSource19
/- Source: Wishart/FieldGaussianRadiality.lean -/



/-!
# Radiality of the actual complex and quaternion Gaussian row average

Equal scalar norms are related by a unitary left multiplier. The multiplier
preserves the actual Gaussian row law, including every singular rectangular
covariance factor, and leaves the row Gram matrix unchanged. This supplies
the concrete transformation required by the submean averaging theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical Matrix Quaternion BigOperators
namespace Wishart.FieldGaussian
open WishartVerification

theorem complex_mem_unitary_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z ∈ unitary ℂ := by
  apply Unitary.mem_iff_star_mul_self.mpr
  simpa only [Complex.star_def, hz, one_pow, Complex.ofReal_one] using Complex.conj_mul' z

theorem quaternion_mem_unitary_of_norm_one {z : ℍ} (hz : ‖z‖ = 1) : z ∈ unitary ℍ := by
  apply Unitary.mem_iff.mpr
  constructor
  · rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hz,
      one_mul, Quaternion.coe_one]
  · rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, hz,
      one_mul, Quaternion.coe_one]

section Algebra
variable {F : Type*} [NormedDivisionRing F] [StarRing F]

theorem exists_unitary_mul_of_norm_eq
    (hunit : ∀ z : F, ‖z‖ = 1 → z ∈ unitary F)
    (a b : F) (hab : ‖a‖ = ‖b‖) : ∃ u : unitary F, (u : F) * a = b := by
  by_cases ha : a = 0
  · have hb : b = 0 := norm_eq_zero.mp (by rw [← hab, ha, norm_zero])
    exact ⟨1, by simp only [ha, hb, OneMemClass.coe_one, one_mul]⟩
  · have hn : ‖b * a⁻¹‖ = 1 := by
      rw [norm_mul, norm_inv, ← hab, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha)]
    refine ⟨⟨b * a⁻¹, hunit _ hn⟩, ?_⟩
    change b * a⁻¹ * a = b
    rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]

end Algebra

section Rows
variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

def rowShift {m : ℕ} (z : Row F m) (a : F) (v : Row F m) : Row F m :=
  WithLp.toLp 2 fun i => z i + a * v i

@[simp] theorem rowShift_apply {m : ℕ} (z : Row F m) (a : F) (v : Row F m) (i : Fin m) :
    rowShift F z a v i = z i + a * v i := rfl

theorem rowShift_real {m : ℕ} (z v : Row F m) (t : ℝ) :
    rowShift F z (t • (1 : F)) v = z + t • v := by
  ext i
  change z i + (t • (1 : F)) * v i = z i + t • v i
  rw [smul_mul_assoc, one_mul]

def rowRadialIntegrand {m : ℕ} (A : Matrix (Fin m) (Fin m) F)
    (g : Matrix (Fin m) (Fin m) F → ℝ) (v : Row F m) (w : Row F m × F) : ℝ :=
  g (A + rowGram F (rowShift F w.1 w.2 v))

theorem rowRadialIntegrand_phase {m : ℕ}
    (A : Matrix (Fin m) (Fin m) F) (g : Matrix (Fin m) (Fin m) F → ℝ)
    (v z : Row F m) (u : unitary F) (a : F) :
    rowRadialIntegrand F A g v (rowPhase F u z, (u : F) * a) =
      rowRadialIntegrand F A g v (z, a) := by
  unfold rowRadialIntegrand rowShift
  rw [rowGram_phase_shift]

theorem continuous_rowRadialIntegrand {m : ℕ}
    (A : Matrix (Fin m) (Fin m) F) {g : Matrix (Fin m) (Fin m) F → ℝ}
    (hg : Continuous g) (v : Row F m) : Continuous (rowRadialIntegrand F A g v) := by
  unfold rowRadialIntegrand rowGram rowShift
  apply hg.comp
  fun_prop

/-- Radiality is proved from a concrete unitary phase transformation of the
Gaussian sample. No support condition on the direction or covariance is used. -/
theorem row_average_radial
    (hunit : ∀ z : F, ‖z‖ = 1 → z ∈ unitary F)
    {r m : ℕ} (R : Matrix (Fin r) (Fin m) F)
    (A : Matrix (Fin m) (Fin m) F) (g : Matrix (Fin m) (Fin m) F → ℝ)
    (v : Row F m) :
    ∀ a b : F, ‖a‖ = ‖b‖ →
      (∫ z, rowRadialIntegrand F A g v (z, a) ∂gaussianRowWithFactor F R) =
        ∫ z, rowRadialIntegrand F A g v (z, b) ∂gaussianRowWithFactor F R := by
  apply radial_integral_of_noise_equivalences
  intro a b hab
  obtain ⟨u, hu⟩ := exists_unitary_mul_of_norm_eq hunit a b hab
  refine ⟨(rowPhase F u).toHomeomorph.toMeasurableEquiv,
    measurePreserving_rowPhase F R u, ?_⟩
  intro z
  rw [← hu]
  exact (rowRadialIntegrand_phase F A g v z u a).symm

/-- The one-row comparison for the actual field Gaussian law. The remaining
premises describe the deterministic observable: continuous polynomial growth
and its proved scalar submean property. -/
theorem monotone_row_average
    (hunit : ∀ z : F, ‖z‖ = 1 → z ∈ unitary F)
    {r m : ℕ} (R : Matrix (Fin r) (Fin m) F)
    (A : Matrix (Fin m) (Fin m) F) (g : Matrix (Fin m) (Fin m) F → ℝ)
    (v : Row F m)
    (hg : Continuous (rowRadialIntegrand F A g v))
    (hbound : JointPolynomialBound (rowRadialIntegrand F A g v))
    (hsub : ∀ z, BallSubmean (fun a => rowRadialIntegrand F A g v (z, a))) :
    MonotoneOn (fun t : ℝ => ∫ z,
      g (A + rowGram F (z + Real.sqrt t • v)) ∂gaussianRowWithFactor F R) (Ici 0) := by
  have h := (ballSubmean_integral_of_polynomial (norm_allFiniteMoments F R) hg hbound
    (Filter.Eventually.of_forall hsub)).monotoneOn_sqrt_smul
      (row_average_radial F hunit R A g v) (1 : F)
  simpa only [rowRadialIntegrand, rowShift_real] using h

end Rows

theorem standardDeviation_complex : standardDeviation ℂ = (Real.sqrt 2)⁻¹ := by
  simp only [standardDeviation, Complex.finrank_real_complex, Nat.cast_ofNat]

theorem standardDeviation_quaternion : standardDeviation ℍ = (2 : ℝ)⁻¹ := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> norm_num
  simp only [standardDeviation, Quaternion.finrank_eq_four, Nat.cast_ofNat, hs]

theorem complex_row_average_radial {r m : ℕ} (R : Matrix (Fin r) (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (g : Matrix (Fin m) (Fin m) ℂ → ℝ) (v : Row ℂ m) :
    ∀ a b : ℂ, ‖a‖ = ‖b‖ →
      (∫ z, rowRadialIntegrand ℂ A g v (z, a) ∂gaussianRowWithFactor ℂ R) =
        ∫ z, rowRadialIntegrand ℂ A g v (z, b) ∂gaussianRowWithFactor ℂ R :=
  row_average_radial ℂ (fun _ => complex_mem_unitary_of_norm_one) R A g v

theorem quaternion_row_average_radial {r m : ℕ} (R : Matrix (Fin r) (Fin m) ℍ)
    (A : Matrix (Fin m) (Fin m) ℍ) (g : Matrix (Fin m) (Fin m) ℍ → ℝ) (v : Row ℍ m) :
    ∀ a b : ℍ, ‖a‖ = ‖b‖ →
      (∫ z, rowRadialIntegrand ℍ A g v (z, a) ∂gaussianRowWithFactor ℍ R) =
        ∫ z, rowRadialIntegrand ℍ A g v (z, b) ∂gaussianRowWithFactor ℍ R :=
  row_average_radial ℍ (fun _ => quaternion_mem_unitary_of_norm_one) R A g v

end Wishart.FieldGaussian
end
end CanonicalSource19

section CanonicalSource20
/- Source: Wishart/FieldRowCompression.lean -/



/-!
# Arbitrary overlapping compressions of a scalar row update

Compression is performed on the actual Hermitian matrix. The identity below
reduces it to a row update of the compressed background, and keeps quaternion
scalar multiplication on the left. In particular no disjointness, orthogonal
mean direction, or covariance-range condition enters the row calculation.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Matrix Quaternion RealInnerProductSpace ComplexOrder
namespace Wishart.FieldGaussian
open WishartVerification

section Algebra
variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]
variable {m k : ℕ}

def rowMatrix (z : Row F m) : Matrix Unit (Fin m) F := Matrix.of fun _ j => z j

@[simp] theorem rowMatrix_apply (z : Row F m) (i : Unit) (j : Fin m) :
    rowMatrix F z i j = z j := rfl

theorem rowGram_eq_matrix (z : Row F m) :
    rowGram F z = (rowMatrix F z)ᴴ * rowMatrix F z := by
  ext i j
  simp only [rowGram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    rowMatrix_apply, Fintype.sum_unique]

theorem rowMatrix_factor (B : Matrix (Fin m) (Fin k) F) (z : Row F m) :
    rowMatrix F (rowFactorCLM F B z) = rowMatrix F z * B := by
  ext i j
  simp only [rowMatrix_apply, rowFactorCLM_apply, Matrix.mul_apply]

def shiftedFactorRow (B : Matrix (Fin m) (Fin k) F) (z v : Row F m) (u : F) :
    Matrix Unit (Fin k) F :=
  rowMatrix F (rowFactorCLM F B z) +
    Matrix.of (fun _ j => u * rowFactorCLM F B v j)

theorem rowMatrix_shift_factor (B : Matrix (Fin m) (Fin k) F)
    (z v : Row F m) (u : F) :
    rowMatrix F (rowShift F z u v) * B = shiftedFactorRow F B z v u := by
  ext i j
  simp only [Matrix.mul_apply, rowMatrix_apply, rowShift_apply, add_mul,
    shiftedFactorRow, Matrix.add_apply, Matrix.of_apply, rowFactorCLM_apply,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem compressed_row_shift (A : Matrix (Fin m) (Fin m) F)
    (B : Matrix (Fin m) (Fin k) F) (D : Matrix (Fin k) (Fin k) F)
    (z v : Row F m) (u : F) :
    Bᴴ * (A + rowGram F (rowShift F z u v)) * B + D =
      (Bᴴ * A * B + D) + (shiftedFactorRow F B z v u)ᴴ * shiftedFactorRow F B z v u := by
  rw [rowGram_eq_matrix, ← rowMatrix_shift_factor, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

end Algebra

theorem positiveLogSubmean_complex_compressed_row {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hQ : (Bᴴ * A * B + D).PosDef)
    (z v : Row ℂ m) :
    PositiveLogSubmean (fun u : ℂ => ComplexMatrix.realDeterminant
      (Bᴴ * (A + rowGram ℂ (rowShift ℂ z u v)) * B + D)) := by
  have heq : (fun u : ℂ => ComplexMatrix.realDeterminant
      (Bᴴ * (A + rowGram ℂ (rowShift ℂ z u v)) * B + D)) =
      fun u => ComplexMatrix.realDeterminant ((Bᴴ * A * B + D) +
        (rowMatrix ℂ (rowFactorCLM ℂ B z) +
          ComplexMatrix.scalarRow u (rowMatrix ℂ (rowFactorCLM ℂ B v)))ᴴ *
        (rowMatrix ℂ (rowFactorCLM ℂ B z) +
          ComplexMatrix.scalarRow u (rowMatrix ℂ (rowFactorCLM ℂ B v)))) := by
    funext u
    rw [compressed_row_shift]
    rfl
  rw [heq]
  exact ComplexMatrix.positiveLogSubmean_rowDeterminant hQ _ _

theorem positiveLogSubmean_quaternion_compressed_row {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) ℍ) (B : Matrix (Fin m) (Fin k) ℍ)
    (D : Matrix (Fin k) (Fin k) ℍ) (hQ : QuaternionMatrix.PosDef (Bᴴ * A * B + D))
    (z v : Row ℍ m) :
    PositiveLogSubmean (fun u : ℍ => QuaternionMatrix.positiveDeterminant
      (Bᴴ * (A + rowGram ℍ (rowShift ℍ z u v)) * B + D)) := by
  have heq : (fun u : ℍ => QuaternionMatrix.positiveDeterminant
      (Bᴴ * (A + rowGram ℍ (rowShift ℍ z u v)) * B + D)) =
      fun u => QuaternionMatrix.positiveDeterminant ((Bᴴ * A * B + D) +
        (rowMatrix ℍ (rowFactorCLM ℍ B z) +
          QuaternionMatrix.scalarRow u (rowMatrix ℍ (rowFactorCLM ℍ B v)))ᴴ *
        (rowMatrix ℍ (rowFactorCLM ℍ B z) +
          QuaternionMatrix.scalarRow u (rowMatrix ℍ (rowFactorCLM ℍ B v)))) := by
    funext u
    rw [compressed_row_shift]
    rfl
  rw [heq]
  exact QuaternionMatrix.positiveLogSubmean_rowDeterminant hQ _ _

end Wishart.FieldGaussian
end
end CanonicalSource20

section CanonicalSource21
/- Source: Wishart/IdentityRegularization.lean -/



/-!
# Decreasing positive regularization in the submean argument

The approximation ε_n = exp(-n) is positive and tends to zero. A continuous
observable increasing along the regularization direction has an integrable
first-term bound on every ball. Thus a proved logarithmic submean inequality
for each positive regularization implies the ordinary submean inequality for
the possibly vanishing boundary function.
-/

noncomputable section
open Filter Topology Set
namespace WishartVerification

def positiveRidge (n : ℕ) : ℝ := Real.exp (-(n : ℝ))

theorem positiveRidge_pos (n : ℕ) : 0 < positiveRidge n := Real.exp_pos _

theorem positiveRidge_antitone : Antitone positiveRidge := by
  intro n m hnm
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (Nat.cast_le.mpr hnm)

theorem positiveRidge_tendsto : Tendsto positiveRidge atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem BallSubmean.of_positive_scalar_regularization
    (A : E → V) (hA : Continuous A) (I : V) {g : V → ℝ}
    (hg : Continuous g)
    (hmono : ∀ u, MonotoneOn (fun ε : ℝ => g (A u + ε • I)) (Ici 0))
    (hreg : ∀ ε : ℝ, 0 < ε →
      PositiveLogSubmean (fun u : E => g (A u + ε • I))) :
    BallSubmean (fun u : E => g (A u)) := by
  apply BallSubmean.of_nonnegative_antitone_limit
    (F := fun n u => g (A u + positiveRidge n • I))
    (fun n => (hreg (positiveRidge n) (positiveRidge_pos n)).toBallSubmean)
    (hg.comp hA)
  · intro n u
    exact (hreg (positiveRidge n) (positiveRidge_pos n)).positive u |>.le
  · intro u n m hnm
    exact hmono u (positiveRidge_pos m).le (positiveRidge_pos n).le
      (positiveRidge_antitone hnm)
  · intro u
    apply hg.continuousAt.tendsto.comp
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (positiveRidge_tendsto.smul_const I)

end WishartVerification
end
end CanonicalSource21

section CanonicalSource22
/- Source: Wishart/JointPolynomialClosure.lean -/



/-!
# Polynomial envelopes for finite spectral approximations

These elementary closure lemmas retain an actual natural-degree envelope
under nonnegative real powers, products, and finite maxima. They apply to the
continuous, nonsmooth approximants used in the singular row argument; no
smoothness of a real power at zero is asserted.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace WishartVerification
variable {E V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup V]

theorem JointPolynomialBound.const (c : ℝ) :
    JointPolynomialBound (fun _ : E × V => c) :=
  ⟨0, ‖c‖, norm_nonneg c, fun z u => by simp only [pow_zero, mul_one, le_refl]⟩

theorem JointPolynomialBound.mono {f g : E × V → ℝ}
    (hg : JointPolynomialBound g) (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    JointPolynomialBound f := by
  obtain ⟨d, C, hC, hb⟩ := hg
  exact ⟨d, C, hC, fun z u => (hfg (z, u)).trans (hb z u)⟩

theorem JointPolynomialBound.norm {f : E × V → ℝ} (hf : JointPolynomialBound f) :
    JointPolynomialBound (fun x => ‖f x‖) :=
  hf.mono (fun x => by simp only [norm_norm, le_refl])

theorem JointPolynomialBound.add {f g : E × V → ℝ}
    (hf : JointPolynomialBound f) (hg : JointPolynomialBound g) :
    JointPolynomialBound (fun x => f x + g x) := by
  obtain ⟨d, C, hC, hb⟩ := hf
  obtain ⟨e, D, hD, hc⟩ := hg
  refine ⟨d + e, C + D, add_nonneg hC hD, ?_⟩
  intro z u
  have hbase : 1 ≤ 1 + ‖z‖ + ‖u‖ := by linarith [norm_nonneg z, norm_nonneg u]
  have hde : (1 + ‖z‖ + ‖u‖) ^ d ≤ (1 + ‖z‖ + ‖u‖) ^ (d + e) :=
    pow_le_pow_right₀ hbase (Nat.le_add_right d e)
  have hed : (1 + ‖z‖ + ‖u‖) ^ e ≤ (1 + ‖z‖ + ‖u‖) ^ (d + e) :=
    pow_le_pow_right₀ hbase (Nat.le_add_left e d)
  calc
    ‖f (z, u) + g (z, u)‖ ≤ ‖f (z, u)‖ + ‖g (z, u)‖ := norm_add_le _ _
    _ ≤ C * (1 + ‖z‖ + ‖u‖) ^ d + D * (1 + ‖z‖ + ‖u‖) ^ e :=
      add_le_add (hb z u) (hc z u)
    _ ≤ C * (1 + ‖z‖ + ‖u‖) ^ (d + e) + D * (1 + ‖z‖ + ‖u‖) ^ (d + e) :=
      add_le_add (mul_le_mul_of_nonneg_left hde hC) (mul_le_mul_of_nonneg_left hed hD)
    _ = (C + D) * (1 + ‖z‖ + ‖u‖) ^ (d + e) := by ring

theorem JointPolynomialBound.mul {f g : E × V → ℝ}
    (hf : JointPolynomialBound f) (hg : JointPolynomialBound g) :
    JointPolynomialBound (fun x => f x * g x) := by
  obtain ⟨d, C, hC, hb⟩ := hf
  obtain ⟨e, D, hD, hc⟩ := hg
  refine ⟨d + e, C * D, mul_nonneg hC hD, ?_⟩
  intro z u
  rw [norm_mul]
  calc
    ‖f (z, u)‖ * ‖g (z, u)‖ ≤
        (C * (1 + ‖z‖ + ‖u‖) ^ d) * (D * (1 + ‖z‖ + ‖u‖) ^ e) :=
      mul_le_mul (hb z u) (hc z u) (norm_nonneg _) (by positivity)
    _ = (C * D) * (1 + ‖z‖ + ‖u‖) ^ (d + e) := by rw [pow_add]; ring

theorem JointPolynomialBound.rpow {f : E × V → ℝ}
    (hf : JointPolynomialBound f) {a : ℝ} (ha : 0 ≤ a) :
    JointPolynomialBound (fun x => f x ^ a) := by
  obtain ⟨d, C, hC, hb⟩ := hf
  let N : ℕ := ⌈a⌉₊
  refine ⟨d * N, (1 + C) ^ N, by positivity, ?_⟩
  intro z u
  let B := 1 + ‖z‖ + ‖u‖
  have hB : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg z, norm_nonneg u]
  have hBd : 1 ≤ B ^ d := one_le_pow₀ hB
  have hbig : 1 ≤ (1 + C) * B ^ d :=
    one_le_mul_of_one_le_of_one_le (by linarith) hBd
  have hbound : ‖f (z, u)‖ ≤ (1 + C) * B ^ d := by
    apply (hb z u).trans
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (zero_le_one.trans hB) d)
  calc
    ‖f (z, u) ^ a‖ ≤ ‖f (z, u)‖ ^ a := by
      simpa only [Real.norm_eq_abs] using Real.abs_rpow_le_abs_rpow (f (z, u)) a
    _ ≤ ((1 + C) * B ^ d) ^ a := Real.rpow_le_rpow (norm_nonneg _) hbound ha
    _ ≤ ((1 + C) * B ^ d) ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbig (Nat.le_ceil a)
    _ = (1 + C) ^ N * B ^ (d * N) := by
      rw [Real.rpow_natCast, mul_pow, ← pow_mul]

theorem JointPolynomialBound.finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → E × V → ℝ) (hf : ∀ i ∈ s, JointPolynomialBound (f i)) :
    JointPolynomialBound (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using JointPolynomialBound.const (E := E) (V := V) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem JointPolynomialBound.finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → E × V → ℝ) (hf : ∀ i ∈ s, JointPolynomialBound (f i)) :
    JointPolynomialBound (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using JointPolynomialBound.const (E := E) (V := V) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem JointPolynomialBound.finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E × V → ℝ) (hf : ∀ i, JointPolynomialBound (f i)) :
    JointPolynomialBound (fun x => finiteMaximum (fun i => f i x)) := by
  have hsum := JointPolynomialBound.finset_sum Finset.univ (fun i x => ‖f i x‖)
    (fun i _ => (hf i).norm)
  apply hsum.mono
  intro x
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => f i x)
  change ‖Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)‖ ≤ _
  rw [hmax, Real.norm_of_nonneg (show 0 ≤ ∑ j : ι, ‖f j x‖ from
    Finset.sum_nonneg (fun j _ => norm_nonneg (f j x)))]
  exact Finset.single_le_sum (fun j _ => norm_nonneg (f j x)) (Finset.mem_univ i)

theorem JointPolynomialBound.of_temperate [NormedSpace ℝ E] [NormedSpace ℝ V]
    {f : E × V → ℝ} (hf : f.HasTemperateGrowth) : JointPolynomialBound f := by
  obtain ⟨d, C, hb⟩ := hf.2 0
  refine ⟨d, max C 0, le_max_right _ _, ?_⟩
  intro z u
  have hnorm : 1 + ‖(z, u)‖ ≤ 1 + ‖z‖ + ‖u‖ := by
    rw [Prod.norm_def]
    have h := max_le (le_add_of_nonneg_right (norm_nonneg u))
      (le_add_of_nonneg_left (norm_nonneg z))
    linarith
  calc
    ‖f (z, u)‖ ≤ C * (1 + ‖(z, u)‖) ^ d := by simpa using hb (z, u)
    _ ≤ max C 0 * (1 + ‖z‖ + ‖u‖) ^ d :=
      mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) hnorm d)
        (by positivity) (le_max_right _ _)

end WishartVerification
end
end CanonicalSource22

section CanonicalSource23
/- Source: Wishart/FieldPolynomialRows.lean -/



/-!
# Polynomial envelopes for actual field row updates

The row displacement has a uniform linear norm bound in the Gaussian sample
and the field scalar. After an arbitrary fixed compression, the real trace
is a constant plus the squared norm of that compressed row. Every
nonnegative leading eigenvalue product is bounded by a power of this trace;
the last theorem turns this concrete estimate into the envelope required by
the averaging theorem.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Matrix Quaternion BigOperators
namespace Wishart.FieldGaussian
open WishartVerification

section Trace
variable (F : Type*) [AddCommMonoid F] [Module ℝ F] {k : ℕ}

def realTrace (re : F →ₗ[ℝ] ℝ) (A : Matrix (Fin k) (Fin k) F) : ℝ :=
  ∑ i, re (A i i)

theorem realTrace_add (re : F →ₗ[ℝ] ℝ) (A B : Matrix (Fin k) (Fin k) F) :
    realTrace F re (A + B) = realTrace F re A + realTrace F re B := by
  simp only [realTrace, Matrix.add_apply, map_add, Finset.sum_add_distrib]

end Trace

variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]
variable {m k : ℕ}

def rowScalar (u : F) (z : Row F m) : Row F m := WithLp.toLp 2 fun i => u * z i

@[simp] theorem rowScalar_apply (u : F) (z : Row F m) (i : Fin m) :
    rowScalar F u z i = u * z i := rfl

theorem norm_rowScalar (u : F) (z : Row F m) : ‖rowScalar F u z‖ = ‖u‖ * ‖z‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [rowScalar_apply, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg ‖u‖), Real.sqrt_sq (norm_nonneg u)]

theorem rowShift_eq_add (z v : Row F m) (u : F) :
    rowShift F z u v = z + rowScalar F u v := by
  ext i
  rfl

theorem norm_rowShift_le (z v : Row F m) (u : F) :
    ‖rowShift F z u v‖ ≤ ‖z‖ + ‖u‖ * ‖v‖ := by
  rw [rowShift_eq_add]
  exact (norm_add_le z (rowScalar F u v)).trans_eq
    (congrArg (fun a => ‖z‖ + a) (norm_rowScalar F u v))

theorem polynomial_rowShift_norm (v : Row F m) :
    JointPolynomialBound (fun w : Row F m × F => ‖rowShift F w.1 w.2 v‖) := by
  refine ⟨1, 1 + ‖v‖, by positivity, ?_⟩
  intro z u
  rw [norm_norm, pow_one]
  apply (norm_rowShift_le F z v u).trans
  nlinarith [norm_nonneg z, norm_nonneg u, norm_nonneg v,
    mul_nonneg (norm_nonneg z) (norm_nonneg v)]

theorem polynomial_compressedRow_norm (B : Matrix (Fin m) (Fin k) F) (v : Row F m) :
    JointPolynomialBound (fun w : Row F m × F =>
      ‖rowFactorCLM F B (rowShift F w.1 w.2 v)‖) := by
  have h := (JointPolynomialBound.const ‖rowFactorCLM F B‖).mul (polynomial_rowShift_norm F v)
  apply h.mono
  intro w
  rw [norm_norm, Real.norm_of_nonneg (mul_nonneg (norm_nonneg (rowFactorCLM F B))
    (norm_nonneg (rowShift F w.1 w.2 v)))]
  exact (rowFactorCLM F B).le_opNorm _

theorem realTrace_rowGram (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2) (z : Row F k) :
    realTrace F re (rowGram F z) = ‖z‖ ^ 2 := by
  simp only [realTrace, rowGram, Matrix.of_apply, hstar]
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin k => F) z).symm

theorem compressed_rowGram (B : Matrix (Fin m) (Fin k) F) (z : Row F m) :
    Bᴴ * rowGram F z * B = rowGram F (rowFactorCLM F B z) := by
  rw [rowGram_eq_matrix, rowGram_eq_matrix, rowMatrix_factor, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem realTrace_compressed_update (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (A : Matrix (Fin m) (Fin m) F) (B : Matrix (Fin m) (Fin k) F)
    (D : Matrix (Fin k) (Fin k) F) (z : Row F m) :
    realTrace F re (Bᴴ * (A + rowGram F z) * B + D) =
      realTrace F re (Bᴴ * A * B + D) + ‖rowFactorCLM F B z‖ ^ 2 := by
  rw [Matrix.mul_add, Matrix.add_mul, compressed_rowGram]
  have heq : Bᴴ * A * B + rowGram F (rowFactorCLM F B z) + D =
      (Bᴴ * A * B + D) + rowGram F (rowFactorCLM F B z) := by abel
  rw [heq, realTrace_add, realTrace_rowGram F re hstar]

theorem polynomial_realTrace_row_update (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (A : Matrix (Fin m) (Fin m) F) (B : Matrix (Fin m) (Fin k) F)
    (D : Matrix (Fin k) (Fin k) F) (v : Row F m) :
    JointPolynomialBound (fun w : Row F m × F =>
      realTrace F re (Bᴴ * (A + rowGram F (rowShift F w.1 w.2 v)) * B + D)) := by
  have h := (JointPolynomialBound.const (realTrace F re (Bᴴ * A * B + D))).add
    ((polynomial_compressedRow_norm F B v).rpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)))
  simpa only [realTrace_compressed_update F re hstar, Real.rpow_two] using h

/-- A leading-product bound by the actual trace supplies polynomial growth
on every row update. The spectral variational layer provides this inequality
for each leading eigenvalue product, including singular matrices. -/
theorem polynomial_of_le_trace_power (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (A : Matrix (Fin m) (Fin m) F) (B : Matrix (Fin m) (Fin k) F)
    (D : Matrix (Fin k) (Fin k) F) (v : Row F m) (j : ℕ)
    {L : Row F m × F → ℝ} (hL : ∀ w, 0 ≤ L w)
    (hle : ∀ w, L w ≤
      realTrace F re (Bᴴ * (A + rowGram F (rowShift F w.1 w.2 v)) * B + D) ^ j) :
    JointPolynomialBound L := by
  have h := (polynomial_realTrace_row_update F re hstar A B D v).rpow
    (show 0 ≤ (j : ℝ) by positivity)
  simp only [Real.rpow_natCast] at h
  apply h.mono
  intro w
  rw [Real.norm_of_nonneg (hL w), Real.norm_eq_abs]
  exact (hle w).trans (le_abs_self _)

end Wishart.FieldGaussian
end
end CanonicalSource23
