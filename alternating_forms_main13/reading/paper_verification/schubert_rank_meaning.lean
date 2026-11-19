module

public import PaperVerification.SchubertRankIdeals
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Determinantal flag equations and actual ranks over fields

For a coordinate projection, its image on the span of the matrix rows is
the span of the projected rows.  The dimension of that actual vector space
is below q exactly when the q-minor ideal vanishes.  The scheme-level
comparison uses the full ideals and therefore retains the nonreduced data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SchubertRankIdeals

variable {K : Type*} [Field K] {s n : ℕ}

/-- Dimension of the actual span of the coordinate-projected rows. -/
def coordinateProjectionRank (A : Matrix (Fin s) (Fin n) K)
    (C : Set (Fin n)) : ℕ :=
  Module.finrank K (Submodule.span K
    (Set.range fun i : Fin s ↦ fun c : C ↦ A i c.val))

/-- Restricted minors express precisely the ordinary projection-rank bound
on field-valued planes, for every minor size, including the boundary sizes. -/
theorem restrictedMinorIdeal_eq_bot_iff_projection_rank_lt
    (A : Matrix (Fin s) (Fin n) K) (q : ℕ) (C : Set (Fin n)) :
    restrictedMinorIdeal A q C = ⊥ ↔ coordinateProjectionRank A C < q := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let B : Matrix (Fin s) C K := A.submatrix id Subtype.val
  have hr : B.rank = coordinateProjectionRank A C := by
    exact Matrix.rank_eq_finrank_span_row B
  rw [← hr]
  constructor
  · intro hbot
    apply lt_of_not_ge
    intro hq
    obtain ⟨rows, cols, hdet⟩ := Matrix.le_rank_iff_exists_det_submatrix_ne_zero.mp hq
    have hz : (A.submatrix rows (fun i ↦ (cols i).val)).det ∈
        restrictedMinorIdeal A q C :=
      Ideal.subset_span ⟨rows, (fun i ↦ (cols i).val), (fun i ↦ (cols i).property), rfl⟩
    rw [hbot] at hz
    exact hdet (show (B.submatrix rows cols).det = 0 from hz)
  · intro hq
    apply bot_unique
    apply Ideal.span_le.mpr
    rintro z ⟨rows, cols, hcols, rfl⟩
    change (A.submatrix rows cols).det = 0
    by_contra hdet
    let c : Fin q → C := fun i ↦ ⟨cols i, hcols i⟩
    have hd : (B.submatrix rows c).det ≠ 0 := hdet
    have hle : q ≤ B.rank := by
      simpa [Matrix.rank_of_det_ne_zero hd] using Matrix.rank_submatrix_le B rows c
    exact (not_le_of_gt hq) hle

end PaperVerification.SchubertRankIdeals
