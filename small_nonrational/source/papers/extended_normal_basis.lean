module
public import Papers.RationalityTenSupportBasics
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
noncomputable section

open Matrix Module Set

namespace Papers.RationalityTen.ChirotopeDensity

/-- Any finite independent family of supporting normals can be included in
an invertible coordinate matrix. The returned injection identifies its
columns exactly; no rationality is assumed of the original realization. -/
theorem exists_invertible_matrix_containing_normals {r k : ℕ}
    (a : Fin k → Fin r → ℝ) (ha : LinearIndependent ℝ a) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, B.det ≠ 0 ∧
      ∃ e : Fin k → Fin r, Function.Injective e ∧ ∀ j, B.col (e j) = a j := by
  classical
  let hs := ha.linearIndepOn_id
  let I := hs.extend (Set.subset_univ (Set.range a))
  let b : Basis I ℝ (Fin r → ℝ) := Basis.extend hs
  letI : Fintype I := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card I = Fintype.card (Fin r) := by
    have h := Module.finrank_eq_card_basis b
    simpa only [Module.finrank_fintype_fun_eq_card] using h.symm
  let f : I ≃ Fin r := Fintype.equivOfCardEq hcard
  let b' : Basis (Fin r) ℝ (Fin r → ℝ) := b.reindex f
  let B : Matrix (Fin r) (Fin r) ℝ := fun i j => b' j i
  have hB : LinearIndependent ℝ B.col := b'.linearIndependent
  have hdet : B.det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hB)
  let e : Fin k → Fin r := fun j =>
    f ⟨a j, hs.subset_extend _ (Set.mem_range_self j)⟩
  refine ⟨B, hdet, e, ?_, ?_⟩
  · intro i j hij
    apply ha.injective
    have h := f.injective hij
    exact congrArg Subtype.val h
  · intro j
    change b' (e j) = a j
    dsimp only [b', e]
    rw [Basis.reindex_apply, Equiv.symm_apply_apply]
    exact Basis.extend_apply_self hs _

#print axioms exists_invertible_matrix_containing_normals

end Papers.RationalityTen.ChirotopeDensity
