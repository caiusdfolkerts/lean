module
public import Papers.FixedCoordinateFlagDensity
public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section
noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- A two-dimensional column space in four coordinates is the common kernel
of a prescribed nonzero normal and one further independent normal. The first
normal is retained literally, as required by the relative flag argument. -/
theorem exists_second_normal {n : ℕ}
    (C : Matrix (Fin 4) (Fin n) ℝ) (a : Fin 4 → ℝ)
    (hC : C.rank = 2) (ha : a ≠ 0)
    (haC : ∀ j, a ⬝ᵥ C.col j = 0) :
    ∃ b : Fin 4 → ℝ, Spans (pair a b) ∧
      (Matrix.transpose (pair a b)) * C = 0 ∧
      C.mulVecLin.range = (Matrix.transpose (pair a b)).mulVecLin.ker := by
  classical
  let U := C.transpose.mulVecLin.ker
  have hdim : finrank ℝ U = 2 := by
    have h : C.transpose.rank + finrank ℝ C.transpose.mulVecLin.ker = 4 := by
      simpa [Matrix.rank] using C.transpose.mulVecLin.finrank_range_add_finrank_ker
    rw [Matrix.rank_transpose, hC] at h
    dsimp only [U]
    omega
  have hamem : a ∈ U := by
    change C.transpose.mulVec a = 0
    ext j
    change C.col j ⬝ᵥ a = 0
    rw [dotProduct_comm]
    exact haC j
  let aU : U := ⟨a, hamem⟩
  have haU : aU ≠ 0 := by
    intro h
    apply ha
    exact congrArg Subtype.val h
  obtain ⟨b, hLI⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ℝ) (M := U) (by omega) haU
  have hrows : (Matrix.transpose (pair a (b : Fin 4 → ℝ))).row = U.subtype ∘ ![aU, b] := by
    funext i j
    fin_cases i <;> rfl
  have hLIrows : LinearIndependent ℝ (Matrix.transpose (pair a (b : Fin 4 → ℝ))).row := by
    rw [hrows]
    exact hLI.map' U.subtype U.ker_subtype
  have hrank : (Matrix.transpose (pair a (b : Fin 4 → ℝ))).rank = 2 := by
    simpa using hLIrows.rank_matrix
  have hspan : Spans (pair a (b : Fin 4 → ℝ)) := by
    apply (spans_iff_matrix_rank _).mpr
    change Matrix.rank (pair a (b : Fin 4 → ℝ)) = 2
    exact (Matrix.rank_transpose (pair a (b : Fin 4 → ℝ))).symm.trans hrank
  have hb : C.transpose.mulVec (b : Fin 4 → ℝ) = 0 := b.property
  have hprod : (Matrix.transpose (pair a (b : Fin 4 → ℝ))) * C = 0 := by
    ext i j
    fin_cases i
    · change a ⬝ᵥ C.col j = 0
      exact haC j
    · change (b : Fin 4 → ℝ) ⬝ᵥ C.col j = 0
      rw [dotProduct_comm]
      exact congrFun hb j
  refine ⟨b, hspan, hprod, ?_⟩
  have hle : C.mulVecLin.range ≤ (Matrix.transpose (pair a (b : Fin 4 → ℝ))).mulVecLin.ker := by
    rintro _ ⟨v, rfl⟩
    change (Matrix.transpose (pair a (b : Fin 4 → ℝ))).mulVec (C.mulVec v) = 0
    rw [Matrix.mulVec_mulVec, hprod, Matrix.zero_mulVec]
  apply Submodule.eq_of_le_of_finrank_eq hle
  change C.rank = finrank ℝ (Matrix.transpose (pair a (b : Fin 4 → ℝ))).mulVecLin.ker
  have hdim' : (Matrix.transpose (pair a (b : Fin 4 → ℝ))).rank +
      finrank ℝ (Matrix.transpose (pair a (b : Fin 4 → ℝ))).mulVecLin.ker = 4 := by
    simpa [Matrix.rank] using
      (Matrix.transpose (pair a (b : Fin 4 → ℝ))).mulVecLin.finrank_range_add_finrank_ker
  omega

#print axioms exists_second_normal

end Papers.RationalityTen.FixedCoordinateFlagDensity
