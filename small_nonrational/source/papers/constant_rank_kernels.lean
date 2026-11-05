module
public import Papers.ChirotopeRanks
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

open Matrix Module Set

namespace Papers.RationalityTen

section ConstantRank

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- Discarding dependent equations changes no kernel when the row rank is
unchanged. This is used after the small-core perturbation preserves all
support-restricted ranks. -/
theorem kernel_row_restriction_eq
    (A : Matrix m n ℝ) (rows : k → m)
    (hrank : (A.submatrix rows id).rank = A.rank) :
    A.mulVecLin.ker = (A.submatrix rows id).mulVecLin.ker := by
  have hle : A.mulVecLin.ker ≤ (A.submatrix rows id).mulVecLin.ker := by
    intro x hx
    ext i
    have h := congrFun hx (rows i)
    simpa [Matrix.mulVecLin,Matrix.mulVec,Matrix.submatrix] using h
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hB := (A.submatrix rows id).mulVecLin.finrank_range_add_finrank_ker
  change A.rank + _ = _ at hA
  change (A.submatrix rows id).rank + _ = _ at hB
  omega

structure MatrixRowBasis (A : Matrix m n ℝ) where
  support : Finset m
  independent : LinearIndependent ℝ (fun i : support => A i.1)
  rank_eq : (A.submatrix (fun i : support => i.1) id).rank = A.rank

/-- A basis is selected from the actual rows, so every retained equation
keeps its original coordinate support. -/
theorem exists_matrixRowBasis (A : Matrix m n ℝ) : Nonempty (MatrixRowBasis A) := by
  classical
  have h0 : LinearIndepOn ℝ A.row (∅ : Set m) := by simp
  let T := h0.extend (Set.empty_subset (Set.univ : Set m))
  let B : Finset m := T.toFinite.toFinset
  have hBT : (↑B : Set m) = T := by simp [B]
  have hT : LinearIndepOn ℝ A.row T := h0.linearIndepOn_extend _
  have hB : LinearIndependent ℝ (fun i : B => A i.1) := by
    change LinearIndepOn ℝ A.row (↑B : Set m)
    rw [hBT]
    exact hT
  refine ⟨⟨B,hB,?_⟩⟩
  rw [Matrix.rank_eq_finrank_span_row,Matrix.rank_eq_finrank_span_row]
  apply congrArg (fun U : Submodule ℝ (n → ℝ) => finrank ℝ U)
  have hrange :
      Set.range (A.submatrix (fun i : B => i.1) id).row = A.row '' (↑B : Set m) :=
    ChirotopeDensity.range_restricted_family A.row (↑B : Set m)
  rw [hrange,hBT]
  change Submodule.span ℝ (A.row '' h0.extend (Set.empty_subset (Set.univ : Set m))) =
    Submodule.span ℝ (Set.range A.row)
  rw [h0.span_image_extend_eq_span_image,Set.image_univ]

theorem MatrixRowBasis.card_eq_rank {A : Matrix m n ℝ} (B : MatrixRowBasis A) :
    B.support.card = A.rank := by
  have h := B.independent.rank_matrix
  have hc : Fintype.card B.support = B.support.card := Fintype.card_coe B.support
  change (A.submatrix (fun i : B.support => i.1) id).rank = Fintype.card B.support at h
  rw [B.rank_eq,hc] at h
  exact h.symm

theorem kernel_row_restriction_eq_of_independent
    (A : Matrix m n ℝ) (rows : k → m)
    (hrows : LinearIndependent ℝ (fun i => A (rows i)))
    (hrank : A.rank = Fintype.card k) :
    A.mulVecLin.ker = (A.submatrix rows id).mulVecLin.ker := by
  apply kernel_row_restriction_eq
  calc
    (A.submatrix rows id).rank = Fintype.card k := hrows.rank_matrix
    _ = A.rank := hrank.symm

end ConstantRank

end Papers.RationalityTen
