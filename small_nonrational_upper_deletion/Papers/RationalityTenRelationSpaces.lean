module
public import Papers.RationalityTenRestrictedColumns
public import Mathlib.LinearAlgebra.Basis.Basic
@[expose] public section
noncomputable section
open Matrix Module Set
open scoped BigOperators
namespace Papers.RationalityTen.ChirotopeDensity

/-- The full space of coefficient relations on the labelled subset S,
in its own coordinate space. -/
def facetRelationSpace {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : Submodule ℝ (S → ℝ) :=
  (((Matrix.of p).transpose.mulVecLin).comp (insideInjection (K := ℝ) S)).ker

theorem facetRelationSpace_finrank {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    finrank ℝ (facetRelationSpace p S) + subsetRank p S=S.card := by
  let L := (((Matrix.of p).transpose.mulVecLin).comp (insideInjection (K := ℝ) S))
  have h := L.finrank_range_add_finrank_ker
  have hrange : finrank ℝ L.range=subsetRank p S := by
    dsimp only [L]
    rw [restricted_columns_range]
    rfl
  have hdim : finrank ℝ (S→ℝ)=S.card := by simp
  have hker : finrank ℝ L.ker=finrank ℝ (facetRelationSpace p S) := rfl
  omega


end Papers.RationalityTen.ChirotopeDensity
