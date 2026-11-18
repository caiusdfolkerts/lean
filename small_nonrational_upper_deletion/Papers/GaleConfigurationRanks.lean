module
public import Papers.RationalityTenRestrictedColumns
public import Papers.OrthogonalGaleCharts
public import Mathlib.LinearAlgebra.StdBasis
public import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

def SameSubsetRanks {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) : Prop :=
  ∀ S, subsetRank p S = subsetRank q S

theorem SameChirotope.sameSubsetRanks {n r : ℕ}
    {p q : Fin n → Fin r → ℝ} (h : SameChirotope p q)
    (hp : Spans p) : SameSubsetRanks p q :=
  fun S => h.subset_rank_eq hp (↑S : Set (Fin n))

theorem SameRepresentedType.sameSubsetRanks {n d : ℕ}
    {p q : Fin n → Fin d → ℝ} (h : SameRepresentedType p q) :
    SameSubsetRanks p q :=
  fun S => h.subset_rank_eq (↑S : Set (Fin n))

theorem rowIndependent_of_rank {r n : ℕ}
    {A : Matrix (Fin r) (Fin n) ℝ} (hA : A.rank = r) :
    LinearIndependent ℝ A.row := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  simpa [Set.finrank,Matrix.rank_eq_finrank_span_row] using hA.symm

/-- Complementary ranks of actual primal and Gale matrices, written using
the ranks of their labelled point subsets. -/
theorem matrix_gale_subset_rank_identity {r n k : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (hB : Spans B) (hexact : B.mulVecLin.range = A.mulVecLin.ker)
    (S : Finset (Fin n)) :
    subsetRank A.col S + k = S.card + subsetRank B Sᶜ := by
  classical
  have h := gale_subset_rank_identity A.mulVecLin B.mulVecLin
    (mulVec_injective_of_spanning_rows hB) hexact S
  rw [restricted_columns_range] at h
  have hright :
      finrank ℝ ((outsideRestriction (K := ℝ) S).comp B.mulVecLin).range =
        subsetRank B Sᶜ := by
    let C : Matrix {i : Fin n // i∉S} (Fin k) ℝ := fun i j => B i.1 j
    have hC : (outsideRestriction (K := ℝ) S).comp B.mulVecLin = C.mulVecLin := by
      ext x i
      rfl
    rw [hC]
    change C.rank = _
    rw [Matrix.rank_eq_finrank_span_row]
    unfold subsetRank
    apply congrArg (fun U : Submodule ℝ (Fin k → ℝ) => finrank ℝ U)
    apply congrArg (Submodule.span ℝ)
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.1,by simpa using i.2,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,by simpa using hi⟩,rfl⟩
  rw [hright] at h
  simpa [subsetRank] using h

theorem matrix_gale_preserves_subset_ranks {r n k : ℕ}
    (A A' : Matrix (Fin r) (Fin n) ℝ)
    (B B' : Matrix (Fin n) (Fin k) ℝ)
    (hB : Spans B) (hB' : Spans B')
    (hexact : B.mulVecLin.range = A.mulVecLin.ker)
    (hexact' : B'.mulVecLin.range = A'.mulVecLin.ker)
    (hranks : SameSubsetRanks B B') :
    SameSubsetRanks A.col A'.col := by
  intro S
  have h := matrix_gale_subset_rank_identity A B hB hexact S
  have h' := matrix_gale_subset_rank_identity A' B' hB' hexact' S
  have heq := hranks Sᶜ
  omega

theorem exact_of_matrix_dimensions {r n k : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (hA : LinearIndependent ℝ A.row) (hB : Spans B)
    (hAB : A*B=0) (hdim : k+r=n) :
    B.mulVecLin.range = A.mulVecLin.ker := by
  apply range_eq_kernel_of_dimensions A.mulVecLin B.mulVecLin
    hA.mulVec_surjective (mulVec_injective_of_spanning_rows hB)
  · apply LinearMap.ext
    intro x
    change A.mulVec (B.mulVec x) = 0
    rw [Matrix.mulVec_mulVec,hAB,Matrix.zero_mulVec]
  · simpa using hdim

end Papers.RationalityTen.ChirotopeDensity
