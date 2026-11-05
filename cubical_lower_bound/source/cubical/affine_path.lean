/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Linear independence along an affine path

These elementary polynomial-minor lemmas are adapted from Bryan Gin-ge Chen's
`CombinatorialRigidity/Mathlib/LinearAlgebra/Matrix/Rank.lean`, commit
`021c2284bc387efee3c3b20a18eb5f769638b578` (Apache 2.0).
They are checked against this project's pinned Lean and Mathlib versions.
-/

namespace Matrix
variable {m n : Type*}

/-- **Linear independence of rows from a specialized nonzero minor.** Let `M : ι → κ → R` be
a (possibly rectangular) family of rows over an integral domain `R`, with `ι` finite. If there
is a column selection `e : ι → κ` and a ring homomorphism `φ : R →+* S` into a commutative ring
`S` such that the square submatrix `(i, j) ↦ M i (e j)` has a determinant whose
image under `φ` is nonzero, then the rows `M` are linearly independent over `R`.

This is the "a polynomial minor with a nonzero specialization is itself nonzero, hence the generic
rows are independent" reflection: a nonzero specialized minor det forces the `R`-det to be nonzero
(`φ 0 = 0`), so the chosen square submatrix has independent rows
(`linearIndependent_rows_of_det_ne_zero`), and the full rows are independent by composing with the
column-projection linear map `(κ → R) → (ι → R)` (`LinearIndependent.of_comp`). No coefficient-wise
reflection along `φ` is used — that would be false when `φ` has a nontrivial kernel; the argument
routes through the minor's determinant instead. -/
theorem linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    {ι κ R S : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R]
    [CommRing S] (M : ι → κ → R) (φ : R →+* S) (e : ι → κ)
    (hdet : φ (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0) :
    LinearIndependent R M := by
  have hRne : (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0 := fun h => hdet (by rw [h, map_zero])
  let f : (κ → R) →ₗ[R] (ι → R) := LinearMap.pi (fun i => LinearMap.proj (e i))
  refine LinearIndependent.of_comp f ?_
  have hcomp : (f ∘ M) = (fun i j : ι => M i (e j)) := by funext i j; rfl
  rw [hcomp]
  exact Matrix.linearIndependent_rows_of_det_ne_zero hRne

/-- **A matrix with linearly independent rows over a field has a nonsingular maximal minor.**
Let `M : Matrix m n K` over a field `K` with `m` and `n` finite. If the rows of `M` are linearly
independent, then there is a square column selection `e : m → n` such that the `m × m` submatrix
`(i, j) ↦ M i (e j)` has nonzero determinant.

This is the "full row rank ⟹ nonzero square minor" extraction: the columns `Mᵀ.row : n → (m → K)`
span a subspace of `K`-dimension `M.rank = #m` (`LinearIndependent.rank_matrix` + `rank_transpose`),
which is all of `m → K`, so `Mᵀ.row` is a spanning family. Extracting a linearly independent
spanning subfamily (`exists_linearIndependent'`) gives a basis, necessarily of size `#m`; reindexing
it by `m` yields `e : m → n` with `Mᵀ.row ∘ e` linearly independent, i.e. the transpose of the
selected minor has independent rows, i.e. the minor has nonzero determinant
(`linearIndependent_rows_iff_isUnit` + `det_transpose` + `isUnit_iff_ne_zero`). -/
theorem exists_submatrix_det_ne_zero_of_linearIndependent_rows
    {m n K : Type*} [Field K] [Fintype m] [DecidableEq m] [Finite n] {M : Matrix m n K}
    (h : LinearIndependent K M.row) :
    ∃ e : m → n, (Matrix.of (fun i j : m => M i (e j))).det ≠ 0 := by
  classical
  have : Fintype n := Fintype.ofFinite n
  -- The columns of `M` (= rows of `Mᵀ`) span all of `m → K`.
  have hrank : Module.finrank K (Submodule.span K (Set.range Mᵀ.row)) = Fintype.card m := by
    rw [← Mᵀ.rank_eq_finrank_span_row, rank_transpose, h.rank_matrix]
  have hspan : Submodule.span K (Set.range Mᵀ.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, Module.finrank_fintype_fun_eq_card])
  -- Extract a linearly independent spanning subfamily of the columns.
  obtain ⟨κ, a, _, hsp, hli⟩ := exists_linearIndependent' K Mᵀ.row
  rw [hspan] at hsp
  -- It is a basis of `m → K`, so it has exactly `#m` elements: `κ ≃ m`.
  let b : Module.Basis κ K (m → K) := Module.Basis.mk hli (by rw [hsp])
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = Fintype.card m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let em : m ≃ κ := (Fintype.equivOfCardEq hcard).symm
  refine ⟨a ∘ em, ?_⟩
  -- The transpose of the selected minor has rows `Mᵀ.row ∘ a ∘ em`, which are LI.
  set N : Matrix m m K := Matrix.of (fun i j : m => M i ((a ∘ em) j)) with hN
  have hrow : Nᵀ.row = Mᵀ.row ∘ a ∘ em := rfl
  have hLIN : LinearIndependent K Nᵀ.row := by rw [hrow]; exact hli.comp ⇑em em.injective
  have : IsUnit Nᵀ := Matrix.linearIndependent_row_iff_isUnit.mp hLIN
  rw [← Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mp (Nᵀ.isUnit_iff_isUnit_det.mp this)

/-- **Linear independence is cofinite along an affine path.** Let `A B : Matrix m n K` over a
field `K`. If the rows of `A + t₀ • B` are linearly independent for some `t₀ : K`, then the rows
of `A + t • B` are linearly independent for all but finitely many `t : K`.

The proof uses a maximal minor rather than the Gram determinant
`det ((A + t • B) * (A + t • B)ᵀ)`, which detects independence only over a linearly ordered field
(over `ℂ` the single row `(1, i)` is independent, while `1 + i² = 0`): a column selection `e`
witnessing the rows LI at `t₀` (`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) picks
out a *single* minor `Q := det (P selected on columns e) : Polynomial K` of the
polynomial-entry matrix `P := X • C(B) + C(A)`, whose evaluation at `t` is the specialized minor's
determinant (`(evalRingHom t).map_det`). `Q` is nonzero (nonzero at `t₀`), hence has finitely many
roots (`Polynomial.finite_setOfPred_isRoot`); at any non-root `t` the specialized minor is
nonsingular, so the rows are LI there too
(`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`). No infiniteness or characteristic
hypothesis on `K` is needed: the argument only uses that a nonzero univariate polynomial has
finitely many roots. -/
theorem finite_setOf_not_linearIndependent_rows_along_affine_path
    {K : Type*} [Field K] [Finite m] [Finite n] (A B : Matrix m n K) {t₀ : K}
    (h : LinearIndependent K (A + t₀ • B).row) :
    {t : K | ¬ LinearIndependent K (A + t • B).row}.Finite := by
  classical
  have : Fintype m := Fintype.ofFinite m
  have : Fintype n := Fintype.ofFinite n
  -- Column selection witnessing LI at `t₀`.
  obtain ⟨e, he⟩ := exists_submatrix_det_ne_zero_of_linearIndependent_rows h
  -- Polynomial-entry matrix `P` whose evaluation at `t` is `A + t • B`.
  let P : Matrix m n (Polynomial K) :=
    (Polynomial.X : Polynomial K) • B.map Polynomial.C + A.map Polynomial.C
  -- The single witnessing minor polynomial `Q := det (P selected on columns `e`)`.
  let Q : Polynomial K := (Matrix.of (fun i j : m => P i (e j))).det
  have hP_eval : ∀ t : K, P.map (Polynomial.evalRingHom t) = A + t • B := by
    intro t; ext i j
    change Polynomial.eval t (P i j) = (A + t • B) i j
    simp only [P, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hQ_eval : ∀ t : K, Q.eval t = (Matrix.of (fun i j : m => (A + t • B) i (e j))).det := by
    intro t
    change (Polynomial.evalRingHom t) Q = _
    rw [(Polynomial.evalRingHom t).map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    change Polynomial.eval t (P i (e j)) = (A + t • B) i (e j)
    have := congrFun (congrFun (hP_eval t) i) (e j)
    simpa [Matrix.map_apply] using this
  have hQ_ne : Q ≠ 0 := fun hQ0 => by
    have := hQ_eval t₀
    rw [hQ0, Polynomial.eval_zero] at this
    exact he this.symm
  -- The bad-`t` set is contained in `Q`'s finite root set.
  refine (Polynomial.finite_setOfPred_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_ofPred_eq] at ht
  rw [Set.mem_ofPred_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht (linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    (A + t • B).row (RingHom.id K) e (by rwa [RingHom.id_apply]))

end Matrix

/-- **Vector-form polynomial-along-line.** For a finite-dim `W`-vector space over a field `K` and
an affine family `t ↦ fun i => a i + t • b i : K → ι → W` (with `ι` finite), if the family
is linearly independent at some `t₀ : K`, then it is LI for all but finitely many `t : K`.

Vector analogue of `Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path`,
derived by pulling along a basis-induced isomorphism `W ≃ₗ[K] (Fin (finrank K W) → K)`. No
infiniteness or characteristic hypothesis on `K` is needed. -/
theorem LinearIndependent.finite_setOf_not_along_affine_path
    {K ι W : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W] [Module.Finite K W]
    {a b : ι → W} {t₀ : K}
    (h : LinearIndependent K (fun i => a i + t₀ • b i)) :
    {t : K | ¬ LinearIndependent K (fun i => a i + t • b i)}.Finite := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- Pick a basis of `W` and identify `W` with `Fin n → K`.
  let φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K) := (Module.finBasis K W).equivFun
  let A : Matrix ι (Fin (Module.finrank K W)) K := Matrix.of (fun i j => φ (a i) j)
  let B : Matrix ι (Fin (Module.finrank K W)) K := Matrix.of (fun i j => φ (b i) j)
  -- The affine matrix family `A + t • B` has rows `φ ∘ (a · + t • b ·)`.
  have h_row : ∀ t : K, (A + t • B).row = ⇑φ ∘ fun i => a i + t • b i := by
    intro t
    funext i j
    change A i j + t • B i j = φ (a i + t • b i) j
    rw [map_add, map_smul]
    rfl
  -- LI of the affine family ↔ LI of matrix rows, via the LinearEquiv `φ`.
  have h_iff : ∀ t : K,
      LinearIndependent K (fun i => a i + t • b i) ↔
      LinearIndependent K (A + t • B).row := by
    intro t
    rw [h_row t]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- Apply the matrix-form helper.
  refine (Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path A B
    ((h_iff t₀).mp h)).subset fun t ht => ?_
  rw [Set.mem_ofPred_eq] at ht ⊢
  rwa [← h_iff]

