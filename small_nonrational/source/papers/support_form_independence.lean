module
public import Mathlib.Tactic.FinCases
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

/-!
# Independent affine supporting forms

Three distinct facets can be separated without constructing a polar body:
choose a point in each facet that is strictly inside the other two supporting
halfspaces. The evaluation matrix has zero diagonal and strictly positive
off-diagonal entries, hence positive determinant.

This file isolates the finite convexity and evaluation argument. The hypotheses
of the final lemma are concrete affine equalities and inequalities, not a
generic-rank assertion.
-/

namespace Papers.RationalityTen

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Finitely many nonnegative affine functions that are individually strictly
positive somewhere on a nonempty convex set are simultaneously strictly
positive at one point of that set. -/
theorem exists_all_affine_positive {ι : Type*} [Fintype ι]
    (S : Set V) (hS : Convex ℝ S) (hne : S.Nonempty)
    (f : ι → V →ᵃ[ℝ] ℝ)
    (hnonneg : ∀ i x, x ∈ S → 0 ≤ f i x)
    (hpositive : ∀ i, ∃ x ∈ S, 0 < f i x) :
    ∃ x ∈ S, ∀ i, 0 < f i x := by
  classical
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfinite : ∀ t : Finset ι, ∃ x ∈ S, ∀ i ∈ t, 0 < f i x := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, by simp⟩
    | @insert i t hit ih =>
        obtain ⟨x, hx, hxp⟩ := ih
        obtain ⟨y, hy, hyp⟩ := hpositive i
        refine ⟨midpoint ℝ x y, hS.midpoint_mem hx hy, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          rw [AffineMap.map_midpoint]
          have hm := midpoint_add_self ℝ (f i x) (f i y)
          have hx0 := hnonneg i x hx
          linarith
        · rw [AffineMap.map_midpoint]
          have hm := midpoint_add_self ℝ (f j x) (f j y)
          have hy0 := hnonneg j y hy
          have hxpos := hxp j hj
          linarith
  obtain ⟨x, hx, hxp⟩ := hfinite Finset.univ
  exact ⟨x, hx, fun i => hxp i (Finset.mem_univ i)⟩

/-- A real three-by-three matrix with zero diagonal and positive off-diagonal
entries has positive determinant. -/
theorem det_pos_of_zero_diagonal_positive_offDiagonal
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hdiag : ∀ i, A i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < A i j) :
    0 < A.det := by
  have hformula :
      A.det = A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 := by
    rw [Matrix.det_fin_three, hdiag 0, hdiag 1, hdiag 2]
    ring
  rw [hformula]
  exact add_pos
    (mul_pos (mul_pos (hoff 0 1 (by decide)) (hoff 1 2 (by decide)))
      (hoff 2 0 (by decide)))
    (mul_pos (mul_pos (hoff 0 2 (by decide)) (hoff 1 0 (by decide)))
      (hoff 2 1 (by decide)))

/-- A nonsingular finite evaluation matrix certifies independence of affine
forms. The matrix rows are evaluation points and its columns are the forms. -/
theorem affineForms_independent_of_evaluationMatrix {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (f : ι → V →ᵃ[ℝ] ℝ) (p : ι → V)
    (hdet : (Matrix.of (fun i j => f j (p i))).det ≠ 0) :
    LinearIndependent ℝ f := by
  let ev : (V →ᵃ[ℝ] ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun g i => g (p i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let A : Matrix ι ι ℝ := fun i j => f j (p i)
  apply LinearIndependent.of_comp ev
  change LinearIndependent ℝ A.col
  exact Matrix.linearIndependent_col_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))

/-- A zero/nonzero separation witness proves independence of two affine
forms without assuming a generic matrix rank. -/
theorem two_affineForms_independent_of_separating_evaluations
    (f g : V →ᵃ[ℝ] ℝ) (x y : V)
    (hfx : f x = 0) (hgx : g x ≠ 0) (hfy : f y ≠ 0) :
    LinearIndependent ℝ ![f, g] := by
  apply affineForms_independent_of_evaluationMatrix ![f, g] ![x, y]
  simpa [Matrix.det_fin_two, hfx] using
    (neg_ne_zero.mpr (mul_ne_zero hgx hfy))

/-- Affine forms admitting a zero-diagonal, positive off-diagonal evaluation
pattern are linearly independent. -/
theorem three_affineForms_independent_of_evaluations
    (f : Fin 3 → V →ᵃ[ℝ] ℝ) (p : Fin 3 → V)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i)) :
    LinearIndependent ℝ f := by
  let ev : (V →ᵃ[ℝ] ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun g i => g (p i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => f j (p i)
  have hdet : 0 < A.det :=
    det_pos_of_zero_diagonal_positive_offDiagonal A hzero hpositive
  apply LinearIndependent.of_comp ev
  change LinearIndependent ℝ A.col
  exact Matrix.linearIndependent_col_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet.ne'))

/-- A concrete convex support criterion for independence of three affine forms.
For actual distinct facets, the final witness condition follows from their
maximality: no distinct facet contains another. -/
theorem three_affineForms_independent_of_convex_supports
    (f : Fin 3 → V →ᵃ[ℝ] ℝ) (S : Fin 3 → Set V)
    (hconvex : ∀ i, Convex ℝ (S i))
    (hne : ∀ i, (S i).Nonempty)
    (hzero : ∀ i x, x ∈ S i → f i x = 0)
    (hnonneg : ∀ i j x, x ∈ S i → 0 ≤ f j x)
    (hwitness : ∀ i j, i ≠ j → ∃ x ∈ S i, 0 < f j x) :
    LinearIndependent ℝ f := by
  classical
  have hp : ∀ i, ∃ p ∈ S i, ∀ j, i ≠ j → 0 < f j p := by
    intro i
    obtain ⟨p, hp, hpp⟩ := exists_all_affine_positive
      (S i) (hconvex i) (hne i)
      (fun j : {j : Fin 3 // i ≠ j} => f j.1)
      (fun j x hx => hnonneg i j.1 x hx)
      (fun j => hwitness i j.1 j.2)
    exact ⟨p, hp, fun j hij => hpp ⟨j, hij⟩⟩
  choose p hmem hpos using hp
  exact three_affineForms_independent_of_evaluations f p
    (fun i => hzero i (p i) (hmem i)) hpos

/-- The same positive evaluation criterion for ordinary linear forms on an
arbitrary real module. -/
theorem three_linearForms_independent_of_evaluations
    (f : Fin 3 → V →ₗ[ℝ] ℝ) (p : Fin 3 → V)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i)) :
    LinearIndependent ℝ f := by
  let toAffine : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →ᵃ[ℝ] ℝ) :=
    { toFun := fun g => g.toAffineMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp toAffine
  exact three_affineForms_independent_of_evaluations
    (fun i => (f i).toAffineMap) p hzero hpositive


/-- A pair of independent equations together with a third equation that
does not vanish on their common witness is an independent triple.
This is the precise linear-algebra argument behind projection rule (iv). -/
theorem three_vectors_independent_of_pair_and_functional
    (x y z : V) (ell : V →ₗ[ℝ] ℝ)
    (hxy : LinearIndependent ℝ ![x,y])
    (hx : ell x = 0) (hy : ell y = 0) (hz : ell z ≠ 0) :
    LinearIndependent ℝ ![x,y,z] := by
  have hspan : Submodule.span ℝ (Set.range ![x,y]) ≤ ell.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact hx
    · exact hy
  have hzspan : z ∉ Submodule.span ℝ (Set.range ![x,y]) :=
    fun h => hz (hspan h)
  have hsnoc : Fin.snoc ![x,y] z = ![x,y,z] := by
    ext i
    fin_cases i <;> rfl
  simpa only [hsnoc] using hxy.finSnoc hzspan

/-- The same nonsingular evaluation matrix certifies independence of the
evaluated vectors, as well as independence of the evaluating forms. -/
theorem three_vectors_independent_of_evaluations
    (f : Fin 3 → V →ₗ[ℝ] ℝ) (p : Fin 3 → V)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i)) :
    LinearIndependent ℝ p := by
  let ev : V →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun x i => f i x
      map_add' := by intro x y; ext i; exact map_add (f i) x y
      map_smul' := by intro a x; ext i; exact map_smul (f i) a x }
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => f i (p j)
  have hdet : 0 < A.det :=
    det_pos_of_zero_diagonal_positive_offDiagonal A hzero
      (fun i j hij => hpositive j i hij.symm)
  apply LinearIndependent.of_comp ev
  change LinearIndependent ℝ A.col
  exact Matrix.linearIndependent_col_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet.ne'))

end Papers.RationalityTen
