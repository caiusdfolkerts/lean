module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

/-!
# Explicit projective-frame normalization

An invertible row frame A gives coordinates x A⁻¹. If each coordinate of the
fourth frame point is nonzero, a diagonal rescaling makes that point the
all-ones vector. Cramer's rule supplies precisely these nonzero-coordinate
witnesses from the replacement frame determinants. The resulting projective
transformation is invertible and preserves all vanishing minors.
-/

namespace Papers.RationalityTen

open scoped BigOperators Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowFrameCoordinates (A : Matrix κ κ ℝ) (x : κ → ℝ) : κ → ℝ :=
  x ᵥ* A⁻¹

theorem rowFrameCoordinates_row (A : Matrix κ κ ℝ) (hA : A.det ≠ 0) (i : κ) :
    rowFrameCoordinates A (A.row i) = Pi.single i 1 := by
  ext j
  change (A * A⁻¹) i j = (Pi.single i (1 : ℝ) : κ → ℝ) j
  rw [Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem rowFrameCoordinates_cramer (A : Matrix κ κ ℝ) (hA : A.det ≠ 0)
    (x : κ → ℝ) (i : κ) :
    A.det * rowFrameCoordinates A x i = (A.updateRow i x).det := by
  have h := congrFun
    (Matrix.det_smul_inv_vecMul_eq_cramer_transpose A x
      (isUnit_iff_ne_zero.mpr hA)) i
  simpa [rowFrameCoordinates, Matrix.cramer_transpose_apply, smul_eq_mul] using h

theorem rowFrameCoordinates_ne_zero_of_replacement (A : Matrix κ κ ℝ)
    (hA : A.det ≠ 0) (x : κ → ℝ) (i : κ)
    (hreplace : (A.updateRow i x).det ≠ 0) :
    rowFrameCoordinates A x i ≠ 0 := by
  intro hz
  have h := rowFrameCoordinates_cramer A hA x i
  rw [hz, mul_zero] at h
  exact hreplace h.symm

/-- The explicit matrix normalizing a projective frame. -/
def projectiveFrameMatrix (A : Matrix κ κ ℝ) (d : κ → ℝ) : Matrix κ κ ℝ :=
  A⁻¹ * Matrix.diagonal (fun i => (rowFrameCoordinates A d i)⁻¹)

theorem vecMul_projectiveFrameMatrix (A : Matrix κ κ ℝ) (d x : κ → ℝ)
    (i : κ) :
    (x ᵥ* projectiveFrameMatrix A d) i =
      rowFrameCoordinates A x i * (rowFrameCoordinates A d i)⁻¹ := by
  unfold projectiveFrameMatrix rowFrameCoordinates
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_diagonal]

theorem projectiveFrameMatrix_det_ne_zero (A : Matrix κ κ ℝ)
    (hA : A.det ≠ 0) (d : κ → ℝ)
    (hd : ∀ i, rowFrameCoordinates A d i ≠ 0) :
    (projectiveFrameMatrix A d).det ≠ 0 := by
  unfold projectiveFrameMatrix
  rw [Matrix.det_mul]
  apply mul_ne_zero
  · exact (Matrix.isUnit_nonsing_inv_det A (isUnit_iff_ne_zero.mpr hA)).ne_zero
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hd i)

theorem projectiveFrameMatrix_basis (A : Matrix κ κ ℝ) (hA : A.det ≠ 0)
    (d : κ → ℝ) (hd : ∀ i, rowFrameCoordinates A d i ≠ 0) (i : κ) :
    rowFrameCoordinates A d i • (A.row i ᵥ* projectiveFrameMatrix A d) =
      Pi.single i 1 := by
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, vecMul_projectiveFrameMatrix,
    rowFrameCoordinates_row A hA i]
  by_cases hji : j = i
  · subst j
    simp [hd i]
  · simp [Pi.single_apply, hji, Ne.symm hji]

theorem projectiveFrameMatrix_fourth (A : Matrix κ κ ℝ) (d : κ → ℝ)
    (hd : ∀ i, rowFrameCoordinates A d i ≠ 0) :
    d ᵥ* projectiveFrameMatrix A d = fun _ => 1 := by
  ext i
  rw [vecMul_projectiveFrameMatrix]
  exact mul_inv_cancel₀ (hd i)

/-- Replacing each row by its product with a fixed matrix multiplies every
square minor by the determinant of that matrix. -/
theorem det_rows_vecMul (p : κ → κ → ℝ) (M : Matrix κ κ ℝ) :
    (Matrix.of (fun i => p i ᵥ* M)).det =
      (Matrix.of p).det * M.det := by
  have hrows : Matrix.of (fun i => p i ᵥ* M) = Matrix.of p * M := by
    ext i j
    rfl
  rw [hrows, Matrix.det_mul]

theorem det_rows_smul_vecMul (p : κ → κ → ℝ) (c : κ → ℝ)
    (M : Matrix κ κ ℝ) :
    (Matrix.of (fun i => c i • (p i ᵥ* M))).det =
      (∏ i, c i) * ((Matrix.of p).det * M.det) := by
  have hs : Matrix.of (fun i => c i • (p i ᵥ* M)) =
      Matrix.of (fun i j => c i * (p i ᵥ* M) j) := by
    ext i j
    rfl
  rw [hs]
  have h := Matrix.det_mul_column c (Matrix.of (fun i => p i ᵥ* M))
  simpa only [Matrix.of_apply,det_rows_vecMul] using h

/-- Nonzero independent row scalings and an invertible projective matrix
preserve precisely which square minors vanish. -/
theorem det_rows_smul_vecMul_zero_iff (p : κ → κ → ℝ) (c : κ → ℝ)
    (hc : ∀ i, c i ≠ 0) (M : Matrix κ κ ℝ) (hM : M.det ≠ 0) :
    (Matrix.of (fun i => c i • (p i ᵥ* M))).det = 0 ↔ (Matrix.of p).det = 0 := by
  rw [det_rows_smul_vecMul]
  have hcprod : (∏ i, c i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hc i
  simp [hcprod, hM]

/-- Independence is preserved by an invertible row-coordinate transformation
and nonzero individual scalings. -/
theorem independent_smul_vecMul {ι : Type*}
    (p : ι → κ → ℝ) (hp : LinearIndependent ℝ p)
    (c : ι → ℝ) (hc : ∀ i, c i ≠ 0)
    (M : Matrix κ κ ℝ) (hM : M.det ≠ 0) :
    LinearIndependent ℝ (fun i => c i • (p i ᵥ* M)) := by
  have hunit : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM)
  have hinj : Function.Injective M.vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hunit
  have hmap : LinearIndependent ℝ (fun i => p i ᵥ* M) :=
    hp.map' M.vecMulLinear (LinearMap.ker_eq_bot.mpr hinj)
  simpa only [Pi.smul_def', Pi.smul_apply, Units.smul_def, Units.val_mk0] using
    hmap.units_smul (fun i => Units.mk0 (c i) (hc i))

/-- Normalize an actual projective frame at arbitrary labels. The output
preserves every vanishing three-minor and every independent point pair. -/
theorem exists_normalized_projective_frame {ι : Type*}
    (p : ι → Fin 3 → ℝ) (b : Fin 3 → ι) (hb : Function.Injective b)
    (d : ι) (hd : ∀ i, b i ≠ d)
    (hA : (Matrix.of (fun i => p (b i))).det ≠ 0)
    (hreplace : ∀ i,
      ((Matrix.of (fun j => p (b j))).updateRow i (p d)).det ≠ 0) :
    ∃ q : ι → Fin 3 → ℝ,
      (∀ i, q (b i) = Pi.single i 1) ∧
      q d = (fun _ => 1) ∧
      (∀ a : Fin 3 → ι,
        (Matrix.of (fun i => q (a i))).det = 0 ↔
          (Matrix.of (fun i => p (a i))).det = 0) ∧
      (∀ i j, LinearIndependent ℝ ![p i, p j] →
        LinearIndependent ℝ ![q i, q j]) := by
  classical
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i => p (b i))
  let w := rowFrameCoordinates A (p d)
  have hw : ∀ i, w i ≠ 0 := fun i =>
    rowFrameCoordinates_ne_zero_of_replacement A hA (p d) i (hreplace i)
  let M := projectiveFrameMatrix A (p d)
  have hM : M.det ≠ 0 := projectiveFrameMatrix_det_ne_zero A hA (p d) hw
  let c : ι → ℝ := Function.extend b w (fun _ => 1)
  have hcb : ∀ i, c (b i) = w i := fun i => hb.extend_apply w (fun _ => 1) i
  have hcd : c d = 1 :=
    Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact hd i hi)
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    by_cases hi : ∃ j, b j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hcb]
      exact hw j
    · rw [show c i = 1 from Function.extend_apply' _ _ _ hi]
      exact one_ne_zero
  let q : ι → Fin 3 → ℝ := fun i => c i • (p i ᵥ* M)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro i
    change c (b i) • (p (b i) ᵥ* M) = _
    rw [hcb]
    exact projectiveFrameMatrix_basis A hA (p d) hw i
  · change c d • (p d ᵥ* M) = _
    rw [hcd, one_smul]
    exact projectiveFrameMatrix_fourth A (p d) hw
  · intro a
    exact det_rows_smul_vecMul_zero_iff
      (fun i => p (a i)) (fun i => c (a i)) (fun i => hc (a i)) M hM
  · intro i j hp
    have hc' : ∀ k : Fin 2, (![c i, c j] : Fin 2 → ℝ) k ≠ 0 := by
      intro k
      fin_cases k
      · exact hc i
      · exact hc j
    have hh := independent_smul_vecMul ![p i, p j] hp ![c i, c j] hc' M hM
    convert hh using 1
    ext k
    fin_cases k <;> rfl


theorem det_rows_smul_zero (p : κ → κ → ℝ) (c : κ → ℝ)
    (h : (Matrix.of p).det = 0) :
    (Matrix.of (fun i => c i • p i)).det = 0 := by
  have hs : Matrix.of (fun i => c i • p i) =
      Matrix.of (fun i j => c i * p i j) := by
    ext i j
    rfl
  rw [hs]
  have hh := Matrix.det_mul_column c (Matrix.of p)
  simpa only [Matrix.of_apply,h,mul_zero] using hh

/-- An independent projective point has a nonzero coordinate off the
specified coordinate point. -/
theorem independent_basis_point_has_other_coordinate (i : κ) (x : κ → ℝ)
    (hx : LinearIndependent ℝ ![Pi.single i 1, x]) :
    ∃ j, j ≠ i ∧ x j ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ j, j ≠ i → x j = 0 := by
    intro j hji
    by_contra hxj
    exact h ⟨j, hji, hxj⟩
  have hb : (Pi.single i (1 : ℝ) : κ → ℝ) ≠ 0 := by
    intro heq
    have hval := congrFun heq i
    simpa using hval
  have hsmul : x i • Pi.single i 1 = x := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_apply, hji, Ne.symm hji, hzero j hji]
  exact ((LinearIndependent.pair_iff' hb).mp hx) (x i) hsmul

theorem triple_zero_iff_of_selection_zero_iff {ι : Type*}
    (p q : ι → Fin 3 → ℝ)
    (h : ∀ a : Fin 3 → ι,
      (Matrix.of (fun i => q (a i))).det = 0 ↔
        (Matrix.of (fun i => p (a i))).det = 0)
    (i j k : ι) :
    (Matrix.of ![q i, q j, q k]).det = 0 ↔
      (Matrix.of ![p i, p j, p k]).det = 0 := by
  have hp : Matrix.of (fun a => p (![i,j,k] a)) =
      Matrix.of ![p i,p j,p k] := by
    ext a b
    fin_cases a <;> rfl
  have hq : Matrix.of (fun a => q (![i,j,k] a)) =
      Matrix.of ![q i,q j,q k] := by
    ext a b
    fin_cases a <;> rfl
  simpa only [hp, hq] using h ![i,j,k]


end Papers.RationalityTen
