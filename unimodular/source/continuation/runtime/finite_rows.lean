module

public import Recovery.Unimodular.ProductVectorMatroid
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A finite column matroid needs only finitely many original rows

Rows are selected from the original matrix; no row operation is used. Thus the
reduction preserves total unimodularity automatically. This also covers TU
representations whose originally chosen row set is infinite.
-/

noncomputable section
open Set Submodule
open scoped BigOperators

namespace Unimodular.RepresentationBridge

theorem ofFamily_eq_row_restriction {K I J E : Type*} [Field K]
    (A : Matrix I E K) (f : J → I)
    (hspan : span K (Set.range (A.row ∘ f)) = span K (Set.range A.row)) :
    VectorMatroid.ofFamily (K := K) A.col =
      VectorMatroid.ofFamily (K := K) (A.submatrix f id).col := by
  apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
  intro S
  let restrict : (I → K) →ₗ[K] (J → K) :=
    { toFun := fun x j ↦ x (f j)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  constructor
  · intro h
    rw [linearIndepOn_iff'] at h ⊢
    intro t g ht hz
    apply h t g ht
    ext i
    have hrow : A.row i ∈ span K (Set.range (A.row ∘ f)) := by
      rw [hspan]
      exact subset_span ⟨i, rfl⟩
    have hsum : ∀ x ∈ span K (Set.range (A.row ∘ f)),
        ∑ e ∈ t, g e * x e = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          have hh := congrFun hz j
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Matrix.col_apply, Matrix.row_apply, Matrix.submatrix_apply,
            Function.comp_apply, id_eq, Pi.zero_apply] using hh
      | zero => simp
      | add x y _ _ hx hy =>
          simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
      | smul a x _ hx =>
          change (∑ e ∈ t, g e * (a * x e)) = 0
          calc
            _ = a * ∑ e ∈ t, g e * x e := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _
              ring
            _ = 0 := by rw [hx, mul_zero]
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
      Matrix.row_apply, Pi.zero_apply] using hsum (A.row i) hrow
  · intro h
    change LinearIndepOn K (restrict ∘ A.col) S at h
    exact h.of_comp restrict

/-- No finiteness assumption on the original row index type is needed. -/
theorem exists_finite_row_restriction {K I E : Type*} [Field K] [Fintype E]
    (A : Matrix I E K) :
    ∃ n : ℕ, ∃ f : Fin n → I,
      VectorMatroid.ofFamily (K := K) A.col =
        VectorMatroid.ofFamily (K := K) (A.submatrix f id).col := by
  classical
  let S := span K (Set.range A.row)
  letI : Module.Finite K S := inferInstance
  obtain ⟨b, hb, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  choose f hf using hb
  have he : A.row ∘ f = b := funext hf
  refine ⟨Module.finrank K S, f, ofFamily_eq_row_restriction A f ?_⟩
  rwa [he]

#print axioms exists_finite_row_restriction

end Unimodular.RepresentationBridge
