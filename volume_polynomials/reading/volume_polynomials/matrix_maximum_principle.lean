module
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

/-!
# The maximum principle for the finite Alexandrov operator

For a matrix with nonnegative off-diagonal entries and row sum one, every real
eigenvalue is at most one. Connectivity of its positive off-diagonal entries
makes the one-eigenspace consist precisely of constant vectors. This is the
part of Perron–Frobenius used by the finite Bochner argument; it is proved here
directly, including matrices with negative diagonal entries.
-/

namespace VolumePolynomials
open Finset Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_row_difference (A : Matrix ι ι ℝ) (hrow : ∀ i, ∑ j, A i j = 1)
    (x : ι → ℝ) (i : ι) :
    (A *ᵥ x) i - x i = ∑ j, A i j * (x j - x i) := by
  first
  | simp only [Matrix.mulVec, dotProduct, mul_sub, sum_sub_distrib,
      ← sum_mul, hrow, one_mul]

/-- No irreducibility hypothesis is required for the upper spectral bound. -/
theorem matrix_eigenvalue_le_one (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (r : ℝ) (x : ι → ℝ) (hx : x ≠ 0) (heig : A *ᵥ x = r • x) : r ≤ 1 := by
  first
  | classical
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      apply hx
      funext i
      exact not_not.mp (fun hi => h ⟨i, hi⟩)
    letI : Nonempty ι := ⟨j⟩
    obtain ⟨k, hk⟩ := Finite.exists_max (fun i => |x i|)
    have hkpos : 0 < |x k| := (abs_pos.mpr hj).trans_le (hk j)
    have hkne : x k ≠ 0 := abs_pos.mp hkpos
    have hnonpos : ∑ i, A k i * ((x i - x k) * x k) ≤ 0 := by
      apply sum_nonpos
      intro i _
      by_cases hik : k = i
      · subst i
        simp
      · have hprod : x i * x k ≤ (x k) ^ 2 := by
          calc
            x i * x k ≤ |x i * x k| := le_abs_self _
            _ = |x i| * |x k| := abs_mul _ _
            _ ≤ |x k| * |x k| := mul_le_mul_of_nonneg_right (hk i) (abs_nonneg _)
            _ = (x k) ^ 2 := by rw [← pow_two, sq_abs]
        apply mul_nonpos_of_nonneg_of_nonpos (hoff k i hik)
        nlinarith
    have heq : ∑ i, A k i * ((x i - x k) * x k) = (r - 1) * (x k) ^ 2 := by
      calc
        _ = (∑ i, A k i * (x i - x k)) * x k := by
          rw [sum_mul]
          exact sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)
        _ = ((A *ᵥ x) k - x k) * x k := by rw [matrix_row_difference A hrow]
        _ = (r - 1) * (x k) ^ 2 := by
          rw [heig]
          change (r * x k - x k) * x k = _
          ring
    rw [heq] at hnonpos
    by_contra h
    exact (not_lt_of_ge hnonpos)
      (mul_pos (sub_pos.mpr (lt_of_not_ge h)) (sq_pos_of_ne_zero hkne))

def MatrixPositiveEdge (A : Matrix ι ι ℝ) (i j : ι) : Prop := i ≠ j ∧ 0 < A i j

/-- At a maximal coordinate of a fixed vector, every positive edge leads to
another maximal coordinate. -/
theorem matrix_fixed_maximum_propagates (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (x : ι → ℝ) (hfix : A *ᵥ x = x) {i j : ι}
    (hmax : ∀ k, x k ≤ x i) (hij : MatrixPositiveEdge A i j) : x j = x i := by
  first
  | have hzero : ∑ k, A i k * (x k - x i) = 0 := by
      rw [← matrix_row_difference A hrow, hfix, sub_self]
    have hnonpos : ∀ k ∈ (univ : Finset ι), A i k * (x k - x i) ≤ 0 := by
      intro k _
      by_cases hik : i = k
      · subst k
        simp
      · exact mul_nonpos_of_nonneg_of_nonpos (hoff i k hik) (sub_nonpos.mpr (hmax k))
    have hjzero := (sum_eq_zero_iff_of_nonpos hnonpos).mp hzero j (mem_univ j)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hjzero).resolve_left hij.2.ne')

/-- Connectivity supplies the simplicity of the maximal eigenvalue. The
reachability predicate is an ordinary finite path in the positive-entry graph. -/
theorem matrix_fixed_eq_constant [Nonempty ι] (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j)
    (x : ι → ℝ) (hfix : A *ᵥ x = x) : ∃ c : ℝ, x = fun _ => c := by
  first
  | obtain ⟨k, hk⟩ := Finite.exists_max x
    refine ⟨x k, funext fun j => ?_⟩
    have hpath := hconn k j
    induction hpath with
    | refl => rfl
    | @tail a b hab hab' ih =>
        exact (matrix_fixed_maximum_propagates A hoff hrow x hfix
          (fun i => (hk i).trans_eq ih.symm) hab').trans ih

end VolumePolynomials
