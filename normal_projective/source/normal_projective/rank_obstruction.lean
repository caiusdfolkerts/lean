module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
/-!
# Rank obstruction for rooted normal–projective words

The transitions here are the matrix transitions induced by genuine rooted moves.
The geometric bridge is supplied separately; this algebraic module alone does not
assert a theorem about arbitrary polytope moves.
-/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators

namespace NormalProjective.RankObstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rank_add_le (A B : Matrix ι ι ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  have h := LinearMap.rank_add_le A.mulVecLin B.mulVecLin
  rw [← Matrix.mulVecLin_add] at h
  simp only [LinearMap.rank, ← Submodule.finrank_eq_rank] at h
  exact_mod_cast h

theorem rank_neg (A : Matrix ι ι ℝ) : (-A).rank = A.rank := by
  simpa using Matrix.rank_smul_of_mem_nonZeroDivisors A
    (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr (one_ne_zero : (1 : ℝ) ≠ 0)))

def outer (c : ι → ℝ) : Matrix ι ι ℝ := Matrix.vecMulVec (fun _ => 1) c

theorem outer_add (c e : ι → ℝ) : outer (c + e) = outer c + outer e :=
  Matrix.vecMulVec_add _ _ _

@[simp] theorem outer_zero : outer (0 : ι → ℝ) = 0 := by simp [outer]

theorem rank_outer_le (c : ι → ℝ) : (outer c).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le _ _

theorem diagonal_outer (w c : ι → ℝ) :
    Matrix.diagonal w * outer c = Matrix.vecMulVec w c := by
  ext i j
  simp [Matrix.diagonal_mul, outer, Matrix.vecMulVec]

/-- Counts each elementary rooted matrix operation, without combining blocks. -/
inductive RootedWord : Matrix ι ι ℝ → Matrix ι ι ℝ → ℕ → ℕ → Prop
  | nil (A) : RootedWord A A 0 0
  | projective {A B p q} (h : RootedWord A B p q) (c : ι → ℝ) :
      RootedWord A (B + outer c) (p + 1) q
  | normal {A B p q} (h : RootedWord A B p q)
      (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
      RootedWord A (Matrix.diagonal w * B) p (q + 1)

theorem RootedWord.projective_rank_error {A B : Matrix ι ι ℝ} {p q : ℕ}
    (h : RootedWord A B p q) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧
      ∃ R : Matrix ι ι ℝ, R.rank ≤ p ∧ B = Matrix.diagonal w * A + R := by
  induction h with
  | nil =>
      refine ⟨fun _ => 1, fun _ => zero_lt_one, 0, ?_, ?_⟩ <;> simp
  | @projective B p q h c ih =>
      obtain ⟨w, hw, R, hR, hB⟩ := ih
      refine ⟨w, hw, R + outer c, ?_, ?_⟩
      · exact (rank_add_le _ _).trans (Nat.add_le_add hR (rank_outer_le c))
      · rw [hB, add_assoc]
  | @normal B p q h v hv ih =>
      obtain ⟨w, hw, R, hR, hB⟩ := ih
      refine ⟨v * w, fun i => mul_pos (hv i) (hw i), Matrix.diagonal v * R, ?_, ?_⟩
      · exact (Matrix.rank_mul_le_right _ _).trans hR
      · rw [hB, mul_add, ← mul_assoc, Matrix.diagonal_mul_diagonal']
        rfl
 
/-- The stronger invariant charges a rank increase only at a normal operation. -/
theorem RootedWord.normal_rank_error {A B : Matrix ι ι ℝ} {p q : ℕ}
    (h : RootedWord A B p q) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧
      ∃ (R : Matrix ι ι ℝ) (c : ι → ℝ),
        R.rank ≤ q ∧ B = Matrix.diagonal w * A + R + outer c := by
  induction h with
  | nil =>
      refine ⟨fun _ => 1, fun _ => zero_lt_one, 0, 0, ?_, ?_⟩ <;> simp
  | @projective B p q h v ih =>
      obtain ⟨w, hw, R, c, hR, hB⟩ := ih
      refine ⟨w, hw, R, c + v, hR, ?_⟩
      rw [hB, outer_add, add_assoc]
  | @normal B p q h v hv ih =>
      obtain ⟨w, hw, R, c, hR, hB⟩ := ih
      refine ⟨v * w, fun i => mul_pos (hv i) (hw i),
        Matrix.diagonal v * R + Matrix.vecMulVec v c, 0, ?_, ?_⟩
      · exact (rank_add_le _ _).trans
          (Nat.add_le_add ((Matrix.rank_mul_le_right _ _).trans hR)
            (Matrix.rank_vecMulVec_le _ _))
      · rw [hB, mul_add, mul_add, diagonal_outer,
          ← mul_assoc, Matrix.diagonal_mul_diagonal', outer_zero, add_zero, add_assoc]
        rfl

theorem diagonal_error_rank {A R : Matrix ι ι ℝ} (w e : ι → ℝ)
    (hw : ∀ i, w i ≠ 0) (he : Matrix.diagonal e = Matrix.diagonal w * A + R) :
    ∃ z : ι → ℝ, (A - Matrix.diagonal z).rank ≤ R.rank := by
  let z : ι → ℝ := fun i => e i / w i
  have hid : Matrix.diagonal w * (A - Matrix.diagonal z) = -R := by
    have hprod : Matrix.diagonal w * Matrix.diagonal z = Matrix.diagonal e := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      dsimp [z]
      exact mul_div_cancel₀ _ (hw i)
    rw [mul_sub, hprod, he]
    abel
  have hdet : (Matrix.diagonal w).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  refine ⟨z, ?_⟩
  have hr := Matrix.rank_mul_eq_right_of_det_ne_zero (Matrix.diagonal w)
    (A - Matrix.diagonal z) hdet
  rw [hid, rank_neg] at hr
  exact le_of_eq hr.symm

theorem RootedWord.to_diagonal_projective_bound {A : Matrix ι ι ℝ}
    {e : ι → ℝ} {p q : ℕ} (h : RootedWord A (Matrix.diagonal e) p q) :
    ∃ z : ι → ℝ, (A - Matrix.diagonal z).rank ≤ p := by
  obtain ⟨w, hw, R, hR, he⟩ := h.projective_rank_error
  obtain ⟨z, hz⟩ := diagonal_error_rank w e (fun i => ne_of_gt (hw i)) he
  exact ⟨z, hz.trans hR⟩

theorem RootedWord.to_diagonal_normal_bound {A : Matrix ι ι ℝ}
    {e : ι → ℝ} {p q : ℕ} (h : RootedWord A (Matrix.diagonal e) p q) :
    ∃ z : ι → ℝ, (A - Matrix.diagonal z).rank ≤ q + 1 := by
  obtain ⟨w, hw, R, c, hR, he⟩ := h.normal_rank_error
  have he' : Matrix.diagonal e = Matrix.diagonal w * A + (R + outer c) := by
    rw [he, add_assoc]
  obtain ⟨z, hz⟩ := diagonal_error_rank w e (fun i => ne_of_gt (hw i)) he'
  exact ⟨z, hz.trans ((rank_add_le _ _).trans (Nat.add_le_add hR (rank_outer_le c)))⟩

def cyclicSucc (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val + 1 < n + 1 then ⟨i.val + 1, h⟩ else 0

theorem cyclicSucc_castSucc (n : ℕ) (i : Fin n) :
    cyclicSucc n i.castSucc = i.succ := by
  have h : i.val + 1 < n + 1 := by omega
  simp [cyclicSucc, h]
  rfl

def cyclicMatrix (n : ℕ) (ε : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => (if i = j then 1 else 0) + if cyclicSucc n i = j then ε else 0

theorem cyclic_minor_above (n : ℕ) (ε : ℝ) (e : Fin (n + 1) → ℝ)
    (i j : Fin n) (hij : i < j) :
    ((cyclicMatrix n ε - Matrix.diagonal e).submatrix Fin.castSucc Fin.succ) i j = 0 := by
  have hne : i.castSucc ≠ j.succ := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega
  have hne' : i.succ ≠ j.succ := by
    intro h
    exact (ne_of_lt hij) (Fin.succ_injective _ h)
  simp [Matrix.submatrix_apply, cyclicMatrix, Matrix.diagonal_apply,
    hne, cyclicSucc_castSucc, hne']

theorem cyclic_minor_diag (n : ℕ) (ε : ℝ) (e : Fin (n + 1) → ℝ)
    (i : Fin n) :
    ((cyclicMatrix n ε - Matrix.diagonal e).submatrix Fin.castSucc Fin.succ) i i = ε := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
  simp [Matrix.submatrix_apply, cyclicMatrix, Matrix.diagonal_apply,
    hne, cyclicSucc_castSucc]

theorem cyclic_rank_obstruction (n : ℕ) {ε : ℝ} (hε : ε ≠ 0)
    (e : Fin (n + 1) → ℝ) :
    n ≤ (cyclicMatrix n ε - Matrix.diagonal e).rank := by
  let M := (cyclicMatrix n ε - Matrix.diagonal e).submatrix Fin.castSucc Fin.succ
  have htri : M.IsLowerTriangular := by
    intro i j hij
    exact cyclic_minor_above n ε e i j hij
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular M htri]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simpa only [M, cyclic_minor_diag] using hε
  have hr : M.rank = n := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  calc
    n = M.rank := hr.symm
    _ ≤ (cyclicMatrix n ε - Matrix.diagonal e).rank := Matrix.rank_submatrix_le _ _ _

theorem cyclic_word_counts (n : ℕ) {ε : ℝ} (hε : ε ≠ 0)
    {e : Fin (n + 1) → ℝ} {p q : ℕ}
    (h : RootedWord (cyclicMatrix n ε) (Matrix.diagonal e) p q) :
    n ≤ p ∧ n ≤ q + 1 ∧ 2 * n - 1 ≤ p + q := by
  obtain ⟨zP, hzP⟩ := h.to_diagonal_projective_bound
  obtain ⟨zN, hzN⟩ := h.to_diagonal_normal_bound
  have hp := (cyclic_rank_obstruction n hε zP).trans hzP
  have hq := (cyclic_rank_obstruction n hε zN).trans hzN
  exact ⟨hp, hq, by omega⟩

end NormalProjective.RankObstruction

