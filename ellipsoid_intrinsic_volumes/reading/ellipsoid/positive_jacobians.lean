module

public import Ellipsoid.CoefficientDefinitions
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The finite-dimensional positivity bridge

The coefficient Jacobian is generally not symmetric. The determinant argument
below uses its strictly positive quadratic form and a nonsingular homotopy to
the identity. It does not incorrectly apply a symmetric-matrix determinant
theorem directly to the Jacobian.
-/

noncomputable section

open Matrix Set
open scoped BigOperators MatrixOrder

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def symmetricPart (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

theorem symmetricPart_isHermitian (A : Matrix ι ι ℝ) :
    (symmetricPart A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  simp [symmetricPart, Matrix.transpose_apply, add_comm] <;> ring

theorem quadratic_symmetricPart (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (symmetricPart A *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
  have htranspose : x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mulVec, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [symmetricPart, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
    dotProduct_add, smul_eq_mul]
  rw [htranspose]
  ring

theorem quadratic_pos_of_symmetricPart_posDef {A : Matrix ι ι ℝ}
    (hA : (symmetricPart A).PosDef) {x : ι → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (A *ᵥ x) := by
  simpa only [star_trivial, quadratic_symmetricPart] using hA.dotProduct_mulVec_pos hx

theorem det_ne_zero_of_quadratic_pos {A : Matrix ι ι ℝ}
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) : A.det ≠ 0 := by
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    by_contra hne
    have h := hA (x - y) (sub_ne_zero.mpr hne)
    exact (lt_irrefl (0 : ℝ)) (by
      simpa only [Matrix.mulVec_sub, hxy, sub_self, dotProduct_zero] using h)
  have hu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp (A.isUnit_iff_isUnit_det.mp hu)

theorem det_pos_of_quadratic_pos {A : Matrix ι ι ℝ}
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) : 0 < A.det := by
  let H : ℝ → Matrix ι ι ℝ := fun t => (1 - t) • 1 + t • A
  have hH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (H t).det ≠ 0 := by
    apply det_ne_zero_of_quadratic_pos
    intro x hx
    have hxpos : 0 < x ⬝ᵥ x := by
      simpa only [star_trivial, Matrix.one_mulVec] using
        (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).dotProduct_mulVec_pos hx
    have hAx := hA x hx
    change 0 < x ⬝ᵥ (((1 - t) • 1 + t • A) *ᵥ x)
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hxpos.le,
      mul_nonneg ht.1 hAx.le]
  have hcont : Continuous (fun t => (H t).det) := by
    dsimp [H]
    fun_prop
  by_contra h
  have hA0 : A.det ≤ 0 := le_of_not_gt h
  have hzeroRange : (0 : ℝ) ∈ Icc (H 1).det (H 0).det := by
    constructor
    · simpa [H] using hA0
    · simp [H]
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzeroRange
  exact hH t ht hzero

theorem det_pos_of_symmetricPart_posDef {A : Matrix ι ι ℝ}
    (hA : (symmetricPart A).PosDef) : 0 < A.det :=
  det_pos_of_quadratic_pos fun _ hx => quadratic_pos_of_symmetricPart_posDef hA hx

theorem symmetricPart_diagonal_mul_submatrix (A : Matrix ι ι ℝ) (d : ι → ℝ)
    (s : Finset ι) :
    symmetricPart ((Matrix.diagonal d * A).submatrix
      (fun i : s => i.val) (fun i : s => i.val)) =
    (symmetricPart (Matrix.diagonal d * A)).submatrix
      (fun i : s => i.val) (fun i : s => i.val) := by
  ext i j
  rfl

theorem principal_minor_pos_of_diagonal_stability
    {A : Matrix ι ι ℝ} {d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hA : (symmetricPart (Matrix.diagonal d * A)).PosDef) (s : Finset ι) :
    0 < (A.submatrix (fun i : s => i.val) (fun i : s => i.val)).det := by
  have hs : ((symmetricPart (Matrix.diagonal d * A)).submatrix
      (fun i : s => i.val) (fun i : s => i.val)).PosDef :=
    hA.submatrix (e := fun i : s => i.val) (fun a b h => Subtype.ext h)
  have heq : (Matrix.diagonal d * A).submatrix (fun i : s => i.val) (fun i : s => i.val) =
      Matrix.diagonal (fun i : s => d i.val) *
        A.submatrix (fun i : s => i.val) (fun i : s => i.val) := by
    ext i j
    simp [Matrix.diagonal_mul]
  have hsmall : (symmetricPart ((Matrix.diagonal d * A).submatrix
      (fun i : s => i.val) (fun i : s => i.val))).PosDef := by
    rw [symmetricPart_diagonal_mul_submatrix]
    exact hs
  have hdet := det_pos_of_symmetricPart_posDef hsmall
  rw [heq, Matrix.det_mul, Matrix.det_diagonal] at hdet
  exact (mul_pos_iff_of_pos_left (Finset.prod_pos fun i _ => hd i.val)).mp hdet

/-- The strict Schur product lemma used in Lemma 3.1. Only the first
matrix's diagonal is required to be positive. -/
theorem posDef_hadamard_of_posSemidef_positive_diagonal
    {G R : Matrix ι ι ℝ} (hG : G.PosSemidef) (hdiag : ∀ i, 0 < G i i)
    (hR : R.PosDef) : (G ⊙ R).PosDef := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI := h
      have heq : G ⊙ R = (1 : Matrix ι ι ℝ) := Subsingleton.elim _ _
      rw [heq]
      exact Matrix.PosDef.one
  | inr h =>
      letI := h
      obtain ⟨c, hc, hcR⟩ := (CFC.exists_pos_algebraMap_le_iff R hR.isHermitian).2 (by
        intro t ht
        rw [hR.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
        obtain ⟨i, rfl⟩ := ht
        exact hR.eigenvalues_pos i)
      have hrem : (R - c • (1 : Matrix ι ι ℝ)).PosSemidef := by
        simpa only [Algebra.algebraMap_eq_smul_one] using (Matrix.le_iff.mp hcR)
      have hdiagPD : (Matrix.diagonal (fun i => c * G i i)).PosDef :=
        Matrix.PosDef.diagonal fun i => mul_pos hc (hdiag i)
      have heq : G ⊙ R = Matrix.diagonal (fun i => c * G i i) +
          G ⊙ (R - c • (1 : Matrix ι ι ℝ)) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply]
          ring
        · simp [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply, hij]
      rw [heq]
      exact hdiagPD.add_posSemidef (hG.hadamard hrem)

end EllipsoidVerification
