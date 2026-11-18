/- Total unimodularity preserves every independent family under reduction
into every field. This supplies the actual regular-matroid identification. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsPivot
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.ZMod.Basic
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

/-- Full column independence is witnessed by an actual nonzero square minor. -/
theorem independent_cols_iff_minor {K I J : Type*} [Field K] [Fintype I]
    [Fintype J] [DecidableEq J] (M : Matrix I J K) :
    LinearIndependent K M.col ↔ ∃ f : J → I, (M.submatrix f id).det ≠ 0 := by
  classical
  constructor
  · intro h
    have hs : Submodule.span K (Set.range M.row) = ⊤ := by
      rw [← range_vecMulLinear]
      exact LinearMap.range_eq_top.mpr h.vecMul_surjective
    let b := Module.Basis.ofSpan hs.ge
    let e := b.indexEquiv (Pi.basisFun K J)
    let b' := b.reindex e
    have hr : Set.range b' ⊆ Set.range M.row := by
      rw [Module.Basis.range_reindex]
      exact Module.Basis.ofSpan_subset hs.ge
    have hex (j : J) : ∃ i, M.row i = b' j := hr ⟨j, rfl⟩
    choose f hf using hex
    have he : (M.submatrix f id).row = b' := by
      funext j
      exact hf j
    refine ⟨f, ?_⟩
    have hi : LinearIndependent K (M.submatrix f id).row := by
      rw [he]
      exact b'.linearIndependent
    exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hi)
  · rintro ⟨f, hf⟩
    let restrict : (I → K) →ₗ[K] (J → K) :=
      { toFun := fun x => x ∘ f, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
    apply LinearIndependent.of_comp restrict
    exact Matrix.linearIndependent_cols_of_det_ne_zero hf

/-- Every square minor of a TU matrix remains zero or a unit over every field. -/
theorem tu_minor_cast_nonzero_iff {K I J Z : Type*} [Field K]
    [Fintype Z] [DecidableEq Z] (M : Matrix I J ℤ) (hM : M.IsTotallyUnimodular)
    (f : Z → I) (g : Z → J) :
    ((M.map (fun z => (z : K))).submatrix f g).det ≠ 0 ↔
      (M.submatrix f g).det ≠ 0 := by
  obtain ⟨s, hs⟩ := (Matrix.isTotallyUnimodular_iff_fintype M).mp hM Z f g
  have hd : ((M.map (fun z => (z : K))).submatrix f g).det =
      ((M.submatrix f g).det : K) := (Int.cast_det _).symm
  rw [hd, ← hs]
  cases s <;> simp

/-- Literal independence of every finite selected family is identical over
all fields. In particular, reducing modulo two gives the same matroid. -/
theorem tu_independence_field_invariant {K F I J : Type*} [Field K] [Field F]
    [Fintype I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (hM : M.IsTotallyUnimodular) :
    LinearIndependent K (M.map (fun z => (z : K))).col ↔
      LinearIndependent F (M.map (fun z => (z : F))).col := by
  rw [independent_cols_iff_minor, independent_cols_iff_minor]
  apply exists_congr
  intro f
  rw [tu_minor_cast_nonzero_iff M hM, tu_minor_cast_nonzero_iff M hM]

/-- The correspondence applies to every subset of labels, not merely to
full bases, circuits, or the complete selected family. -/
theorem tu_selected_independence_field_invariant {K F I E J : Type*} [Field K] [Field F]
    [Fintype I] [Fintype J] [DecidableEq J]
    (M : Matrix I E ℤ) (hM : M.IsTotallyUnimodular) (g : J → E) :
    LinearIndependent K (fun j i => (M i (g j) : K)) ↔
      LinearIndependent F (fun j i => (M i (g j) : F)) :=
  tu_independence_field_invariant (M.submatrix id g) (hM.submatrix id g)

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.independent_cols_iff_minor
#print axioms Unimodular.SignedSums.tu_independence_field_invariant
#print axioms Unimodular.SignedSums.tu_selected_independence_field_invariant
