module
public import Papers.IntrinsicChirotope
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

theorem rationalCoordinates_transpose {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : RationalCoordinates A) : RationalCoordinates A.transpose :=
  fun i j => hA j i

theorem rationalCoordinates_sub {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℝ}
    (hA : RationalCoordinates A) (hB : RationalCoordinates B) :
    RationalCoordinates (A-B) := fun i j => (hA i j).sub (hB i j)

theorem rationalCoordinates_mul {m n k : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hA : RationalCoordinates A) (hB : RationalCoordinates B) :
    RationalCoordinates (A*B) := by
  intro i j
  change RatScalar (∑ a, A i a * B a j)
  exact RatScalar.finset_sum Finset.univ _ fun a _ => (hA i a).mul (hB a j)

theorem rationalCoordinates_one (n : ℕ) :
    RationalCoordinates (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro i j
  by_cases h : i=j
  · subst j
    exact ⟨1,by simp⟩
  · exact ⟨0,by simp [Matrix.one_apply,h]⟩

theorem rationalCoordinates_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : RationalCoordinates A) : RatScalar A.det := by
  classical
  choose Q hQ using hA
  have hmap : (Rat.castHom ℝ).mapMatrix Q = A := by
    ext i j
    exact hQ i j
  refine ⟨Matrix.det Q,?_⟩
  exact ((Rat.castHom ℝ).map_det Q).trans (congrArg Matrix.det hmap)

theorem rationalCoordinates_adjugate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : RationalCoordinates A) : RationalCoordinates A.adjugate := by
  classical
  choose Q hQ using hA
  have hmap : (Rat.castHom ℝ).mapMatrix Q = A := by
    ext i j
    exact hQ i j
  intro i j
  refine ⟨Matrix.adjugate Q i j,?_⟩
  have h := (Rat.castHom ℝ).map_adjugate Q
  rw [hmap] at h
  exact congrFun (congrFun h i) j

theorem rationalCoordinates_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : RationalCoordinates A) :
    RationalCoordinates (@Inv.inv (Matrix (Fin n) (Fin n) ℝ) Matrix.inv A) := by
  intro i j
  have hd := rationalCoordinates_det hA
  have ha := rationalCoordinates_adjugate hA i j
  have h := ha.div hd
  simpa [Matrix.inv_def,Ring.inverse_eq_inv,div_eq_mul_inv,mul_comm] using h

/-- A spanning family of rows has a nonsingular Gram matrix. -/
theorem gram_isUnit {n k : ℕ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hB : Spans B) : IsUnit (B.transpose*B).det := by
  have hrank : (B.transpose*B).rank = k := by
    rw [Matrix.rank_transpose_mul_self,Matrix.rank_eq_finrank_span_row]
    change finrank ℝ (Submodule.span ℝ (Set.range B)) = k
    rw [hB]
    simp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mpr
  simpa using hrank

theorem mulVec_injective_of_spanning_rows {n k : ℕ}
    {B : Matrix (Fin n) (Fin k) ℝ} (hB : Spans B) :
    Function.Injective B.mulVec := by
  have hG := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (gram_isUnit hB))
  intro x y hxy
  apply hG
  simpa only [Matrix.mulVec_mulVec] using congrArg B.transpose.mulVec hxy

/-- The orthogonal projector onto the kernel of the transpose of the
Gale matrix. Its entries are rational functions of the actual entries. -/
def galeProjector {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - B * (B.transpose*B)⁻¹ * B.transpose

def galeChart {n k r : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (M : Matrix (Fin r) (Fin n) ℝ) : Matrix (Fin r) (Fin n) ℝ :=
  M * galeProjector B

theorem galeProjector_mul {n k : ℕ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hB : Spans B) : galeProjector B * B = 0 := by
  have h :
      (B * (B.transpose*B)⁻¹ * B.transpose) * B = B := by
    calc
      (B * (B.transpose*B)⁻¹ * B.transpose) * B =
          B * ((B.transpose*B)⁻¹ * (B.transpose*B)) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [Matrix.nonsing_inv_mul _ (gram_isUnit hB),Matrix.mul_one]
  rw [galeProjector,Matrix.sub_mul,Matrix.one_mul,h,sub_self]

theorem galeChart_mul {n k r : ℕ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hB : Spans B) (M : Matrix (Fin r) (Fin n) ℝ) :
    galeChart B M * B = 0 := by
  rw [galeChart,Matrix.mul_assoc,galeProjector_mul hB,Matrix.mul_zero]

theorem galeChart_self {n k r : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (A : Matrix (Fin r) (Fin n) ℝ)
    (hAB : A*B=0) : galeChart B A = A := by
  unfold galeChart galeProjector
  rw [Matrix.mul_sub,Matrix.mul_one]
  have h : A * (B * (B.transpose*B)⁻¹ * B.transpose) = 0 := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hAB,Matrix.zero_mul,Matrix.zero_mul]
  rw [h,sub_zero]

theorem galeChart_rational {n k r : ℕ}
    {B : Matrix (Fin n) (Fin k) ℝ} {M : Matrix (Fin r) (Fin n) ℝ}
    (hB : RationalCoordinates B) (hM : RationalCoordinates M) :
    RationalCoordinates (galeChart B M) := by
  exact rationalCoordinates_mul hM
    (rationalCoordinates_sub (rationalCoordinates_one n)
      (rationalCoordinates_mul
        (rationalCoordinates_mul hB
          (rationalCoordinates_inv
            (rationalCoordinates_mul (rationalCoordinates_transpose hB) hB)))
        (rationalCoordinates_transpose hB)))

theorem matrix_mul_continuousAt {X : Type*} [TopologicalSpace X]
    {m n k : ℕ} {A : X → Matrix (Fin m) (Fin n) ℝ}
    {B : X → Matrix (Fin n) (Fin k) ℝ} {x : X}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) :
    ContinuousAt (fun y => A y * B y) x := by
  have h : Continuous
      (fun z : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin k) ℝ =>
        z.1 * z.2) := continuous_fst.matrix_mul continuous_snd
  exact h.continuousAt.comp (hA.prodMk hB)

theorem galeChart_continuousAt {n k r : ℕ}
    {B : Matrix (Fin n) (Fin k) ℝ} (hB : Spans B)
    (A : Matrix (Fin r) (Fin n) ℝ) :
    ContinuousAt
      (fun z : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin r) (Fin n) ℝ =>
        galeChart z.1 z.2) (B,A) := by
  have hBt : Continuous
      (fun z : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin r) (Fin n) ℝ =>
        z.1.transpose) := continuous_fst.matrix_transpose
  have hG := hBt.matrix_mul continuous_fst
  have hinv : ContinuousAt
      (fun z : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin r) (Fin n) ℝ =>
        (z.1.transpose*z.1)⁻¹) (B,A) := by
    have hi : ContinuousAt (Inv.inv : Matrix (Fin k) (Fin k) ℝ → _) (B.transpose*B) :=
      continuousAt_matrix_inv (B.transpose*B) (by
        simpa only [Ring.inverse_eq_inv'] using
          (continuousAt_inv₀ (isUnit_iff_ne_zero.mp (gram_isUnit hB))))
    exact hi.comp_of_eq (hG.continuousAt (x := (B,A))) rfl
  exact matrix_mul_continuousAt continuous_snd.continuousAt
    (continuousAt_const.sub
      (matrix_mul_continuousAt
        (matrix_mul_continuousAt continuous_fst.continuousAt hinv)
        hBt.continuousAt))


end Papers.RationalityTen.ChirotopeDensity
