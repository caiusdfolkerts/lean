module

public import Ellipsoid.RectangleCorner

@[expose] public section

noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixDerivative_mul (A B : Matrix ι ι ℝ) :
    matrixDerivative (A * B) = (matrixDerivative A).comp (matrixDerivative B) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, matrixDerivative_apply, Matrix.mulVec_mulVec]

theorem DiagonallyStable.sign_conjugate {A : Matrix ι ι ℝ} (hA : DiagonallyStable A)
    (s : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    DiagonallyStable (Matrix.diagonal s * A * Matrix.diagonal s) := by
  obtain ⟨d, hd, hpd⟩ := hA
  refine ⟨d, hd, ?_⟩
  have hinj : Function.Injective (Matrix.diagonal s : Matrix ι ι ℝ).mulVec := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (by rcases hs i with h | h <;> simp [h]) hi
  have h := hpd.conjTranspose_mul_mul_same hinj
  simp only [Matrix.diagonal_conjTranspose, star_trivial] at h
  convert h using 1
  ext i j
  simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    star_trivial, smul_eq_mul, Matrix.diagonal_apply]
  ring

def comparisonSigns (x y : ι → ℝ) : ι → ℝ :=
  fun i => if x i ≤ y i then 1 else -1

theorem comparisonSigns_values (x y : ι → ℝ) (i : ι) :
    comparisonSigns x y i = 1 ∨ comparisonSigns x y i = -1 := by
  unfold comparisonSigns
  split_ifs <;> simp

def comparisonWidths (x y : ι → ℝ) : ι → ℝ := fun i => |y i - x i|

theorem comparisonSigns_widths (x y : ι → ℝ) :
    x + (Matrix.diagonal (comparisonSigns x y) *ᵥ comparisonWidths x y) = y := by
  funext i
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, comparisonWidths, comparisonSigns]
  by_cases hi : x i ≤ y i
  · rw [if_pos hi, abs_of_nonneg (sub_nonneg.mpr hi)]
    ring
  · rw [if_neg hi, abs_of_neg (sub_neg.mpr (lt_of_not_ge hi))]
    ring

theorem comparison_box_maps {a b x y : ι → ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    {z : ι → ℝ} (hz : z ∈ Icc 0 (comparisonWidths x y)) :
    x + Matrix.diagonal (comparisonSigns x y) *ᵥ z ∈ Icc a b := by
  constructor <;> intro i
  all_goals
    have hz0 := hz.1 i
    have hz1 := hz.2 i
    simp only [Pi.zero_apply, comparisonWidths] at hz0 hz1
    simp only [Pi.add_apply, Matrix.mulVec_diagonal, comparisonSigns]
    by_cases hi : x i ≤ y i
    · rw [if_pos hi]
      rw [abs_of_nonneg (sub_nonneg.mpr hi)] at hz1
      nlinarith [hx.1 i, hx.2 i, hy.1 i, hy.2 i]
    · rw [if_neg hi]
      rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hi))] at hz1
      nlinarith [hx.1 i, hx.2 i, hy.1 i, hy.2 i]

set_option backward.isDefEq.respectTransparency false in
/-- Rectangle univalence in the form required by the coefficient proof.
The derivative is taken in a neighborhood of every point of the closed
rectangle; the conclusion includes all its faces and repeated-root data. -/
theorem injOn_rectangle_of_diagonal_stability
    {F : (ι → ℝ) → (ι → ℝ)} {A : (ι → ℝ) → Matrix ι ι ℝ} {a b : ι → ℝ}
    (hF : ∀ z ∈ Icc a b, HasFDerivAt F (matrixDerivative (A z)) z)
    (hA : ∀ z ∈ Icc a b, DiagonallyStable (A z)) : Set.InjOn F (Icc a b) := by
  intro x hx y hy hxy
  let S : Matrix ι ι ℝ := Matrix.diagonal (comparisonSigns x y)
  let T : (ι → ℝ) → (ι → ℝ) := fun z => x + S *ᵥ z
  let G : (ι → ℝ) → (ι → ℝ) := fun z => S *ᵥ F (T z)
  let B : (ι → ℝ) → Matrix ι ι ℝ := fun z => S * A (T z) * S
  have hT (z : ι → ℝ) : HasFDerivAt T (matrixDerivative S) z := by
    simpa [T] using (matrixDerivative S).hasFDerivAt.const_add x
  have hG (z : ι → ℝ) (hz : z ∈ Icc 0 (comparisonWidths x y)) :
      HasFDerivAt G (matrixDerivative (B z)) z := by
    have hTz := comparison_box_maps hx hy hz
    have h := (matrixDerivative S).hasFDerivAt.comp z ((hF (T z) hTz).comp z (hT z))
    simpa only [G, B, Function.comp_def, matrixDerivative_mul,
      ContinuousLinearMap.comp_assoc, matrixDerivative_apply] using h
  have hB (z : ι → ℝ) (hz : z ∈ Icc 0 (comparisonWidths x y)) : DiagonallyStable (B z) :=
    (hA (T z) (comparison_box_maps hx hy hz)).sign_conjugate
      (comparisonSigns x y) (comparisonSigns_values x y)
  have hw0 : (0 : ι → ℝ) ≤ comparisonWidths x y := fun i => abs_nonneg _
  have hGh : G (comparisonWidths x y) = G 0 := by
    have ht : T (comparisonWidths x y) = y := comparisonSigns_widths x y
    simp only [G, ht, T, Matrix.mulVec_zero, add_zero, hxy]
  have hw := rectangle_corner_order hw0 hG hB ⟨hw0, le_rfl⟩ hGh.le
  funext i
  have hi := congrFun hw i
  exact (sub_eq_zero.mp (abs_eq_zero.mp hi)).symm

end EllipsoidVerification
