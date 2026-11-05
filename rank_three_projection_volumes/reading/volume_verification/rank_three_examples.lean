module
public import VolumeVerification.MatrixInertia
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace VolumeVerification.RankThreeExamples

/-- Squared distances between distinct points on a line give positive hollow
rank-three matrices in every size at least three. Circle factorization then
provides the equivalent weighted circle representation used in the paper. -/
def squaredIndexMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((i.val : ℝ) - (j.val : ℝ)) ^ 2

theorem squaredIndexMatrix_diagonal (n : ℕ) (i : Fin n) :
    squaredIndexMatrix n i i = 0 := by simp [squaredIndexMatrix]

theorem squaredIndexMatrix_symmetric (n : ℕ) (i j : Fin n) :
    squaredIndexMatrix n i j = squaredIndexMatrix n j i := by
  unfold squaredIndexMatrix
  ring

theorem squaredIndexMatrix_positive (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    0 < squaredIndexMatrix n i j := by
  apply sq_pos_of_ne_zero
  intro hz
  apply hij
  apply Fin.ext
  exact_mod_cast sub_eq_zero.mp hz

theorem squaredIndexMatrix_rank_le (n : ℕ) : (squaredIndexMatrix n).rank ≤ 3 := by
  let L : Matrix (Fin n) (Fin 3) ℝ :=
    fun i => ![1, (i.val : ℝ), (i.val : ℝ)^2]
  let R : Matrix (Fin 3) (Fin n) ℝ :=
    fun k j => ![(j.val : ℝ)^2, -2 * (j.val : ℝ), 1] k
  have he : squaredIndexMatrix n = L * R := by
    ext i j
    change ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = ∑ k : Fin 3, L i k * R k j
    simp [Fin.sum_univ_succ, L, R]
    ring
  rw [he]
  exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_width L)

theorem squaredIndexMatrix_rank (n : ℕ) (hn : 3 ≤ n) :
    (squaredIndexMatrix n).rank = 3 := by
  let f : Fin 3 → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  have hm : (squaredIndexMatrix n).submatrix f f =
      (!![0,1,4; 1,0,1; 4,1,0] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.submatrix, squaredIndexMatrix, f]
  have hd : ((squaredIndexMatrix n).submatrix f f).det ≠ 0 := by
    rw [hm]
    norm_num [Matrix.det_fin_three]
  have hr := Matrix.rank_of_det_ne_zero hd
  have hle := Matrix.rank_submatrix_le (squaredIndexMatrix n) f f
  have hup := squaredIndexMatrix_rank_le n
  norm_num only [Fintype.card_fin] at hr
  omega

/-- The exact five-by-five example printed after Theorem 1.1. -/
def hexagonFive : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,3,4,3;
     1,0,1,3,4;
     3,1,0,1,3;
     4,3,1,0,1;
     3,4,3,1,0]

def hexagonB : Fin 5 → ℝ := ![2,1,-1,-2,-1]
def hexagonC : Fin 5 → ℝ := ![0,1,1,0,-1]

theorem hexagonFive_factorization (i j : Fin 5) :
    hexagonFive i j =
      2 - hexagonB i * hexagonB j / 2 - 3 * hexagonC i * hexagonC j / 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [hexagonFive, hexagonB, hexagonC]

theorem hexagonFive_diagonal (i : Fin 5) : hexagonFive i i = 0 := by
  fin_cases i <;> norm_num [hexagonFive]

theorem hexagonFive_symmetric (i j : Fin 5) : hexagonFive i j = hexagonFive j i := by
  fin_cases i <;> fin_cases j <;> norm_num [hexagonFive]

theorem hexagonFive_positive (i j : Fin 5) (hij : i ≠ j) : 0 < hexagonFive i j := by
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | norm_num [hexagonFive]

theorem hexagonFive_rank : hexagonFive.rank = 3 := by
  let L : Matrix (Fin 5) (Fin 3) ℝ := fun i => ![1, hexagonB i, hexagonC i]
  let R : Matrix (Fin 3) (Fin 5) ℝ :=
    fun k j => ![2, -hexagonB j / 2, -3 * hexagonC j / 2] k
  have he : hexagonFive = L * R := by
    ext i j
    rw [hexagonFive_factorization]
    change 2 - hexagonB i * hexagonB j / 2 - 3 * hexagonC i * hexagonC j / 2 =
      ∑ k : Fin 3, L i k * R k j
    simp [Fin.sum_univ_succ, L, R]
    ring
  have hup : hexagonFive.rank ≤ 3 := by
    rw [he]
    exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_width L)
  let f : Fin 3 → Fin 5 := fun i => ⟨i.val, by omega⟩
  have hm : hexagonFive.submatrix f f =
      (!![0,1,3; 1,0,1; 3,1,0] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.submatrix, hexagonFive, f]
  have hd : (hexagonFive.submatrix f f).det ≠ 0 := by
    rw [hm]
    norm_num [Matrix.det_fin_three]
  have hr := Matrix.rank_of_det_ne_zero hd
  have hle := Matrix.rank_submatrix_le hexagonFive f f
  norm_num only [Fintype.card_fin] at hr
  omega

theorem hexagonFive_signature :
    _root_.sigPos hexagonFive.toQuadraticForm' = 1 ∧
      _root_.sigNeg hexagonFive.toQuadraticForm' = 2 ∧
      Module.finrank ℝ hexagonFive.toQuadraticForm'.radical = 2 := by
  simpa using MatrixInertia.positive_hollow_rank_three_signature hexagonFive
    hexagonFive_symmetric hexagonFive_diagonal hexagonFive_positive hexagonFive_rank
    (0 : Fin 5) 1 2 (by decide) (by decide) (by decide)

end VolumeVerification.RankThreeExamples

