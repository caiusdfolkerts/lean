module
public import VolumeVerification.MarkedPolynomialCone
public import VolumeVerification.PolygonMeasureObstruction
public import Mathlib.LinearAlgebra.Dimension.Free
@[expose] public section
set_option autoImplicit false

/-!
# A full-rank system of equations for the column space

The matrix W is constructed from the actual quotient by the column space.
Its full row rank, its kernel, and its row relations follow from that
construction.  No basis-size or rank hypothesis is added to the application.
-/
namespace VolumeVerification.ProjectionLinearRelations
open scoped BigOperators Matrix
open Module

theorem exists_relation_matrix {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hrank : P.rank = 3) :
    ∃ W : Matrix (Fin (n-3)) (Fin n) ℝ,
      W.rank = n-3 ∧
      (∀ y, W *ᵥ y = 0 ↔ y ∈ P.mulVecLin.range) ∧
      W * P = 0 := by
  classical
  let S : Submodule ℝ (Fin n → ℝ) := P.mulVecLin.range
  have hdim : finrank ℝ ((Fin n → ℝ) ⧸ S) = n-3 := by
    have h := S.finrank_quotient_add_finrank
    have hS : finrank ℝ S = 3 := hrank
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,hS] at h
    omega
  let e : ((Fin n → ℝ) ⧸ S) ≃ₗ[ℝ] (Fin (n-3) → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdim])
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin (n-3) → ℝ) :=
    e.toLinearMap.comp S.mkQ
  let W : Matrix (Fin (n-3)) (Fin n) ℝ := f.toMatrix'
  have hWmap : W.mulVecLin = f := by
    apply LinearMap.ext
    intro y
    change f.toMatrix' *ᵥ y = f y
    exact LinearMap.toMatrix'_mulVec f y
  have hsurj : Function.Surjective f :=
    e.surjective.comp S.mkQ_surjective
  have hWrank : W.rank = n-3 := by
    change finrank ℝ W.mulVecLin.range = n-3
    rw [hWmap,LinearMap.range_eq_top.mpr hsurj]
    simp
  have hker : ∀ y, W *ᵥ y = 0 ↔ y ∈ S := by
    intro y
    change f.toMatrix' *ᵥ y = 0 ↔ y ∈ S
    rw [LinearMap.toMatrix'_mulVec]
    change e (S.mkQ y) = 0 ↔ y ∈ S
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero S
  refine ⟨W,hWrank,hker,?_⟩
  ext k j
  have hc : (fun i => P i j) ∈ S := by
    refine ⟨Pi.single j 1,?_⟩
    ext i
    simp [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Pi.single_apply]
  exact congrFun ((hker _).mpr hc) k

theorem rows_in_kernel {m n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, P i j = P j i)
    (W : Matrix (Fin m) (Fin n) ℝ) (hWP : W*P = 0) (k : Fin m) :
    P *ᵥ W k = 0 := by
  ext i
  calc
    (P *ᵥ W k) i = (W*P) k i := by
      simp only [Matrix.mulVec,dotProduct,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      change P i j * W k j = W k j * P j i
      rw [hsym i j,mul_comm]
    _ = 0 := by rw [hWP]; rfl

theorem sum_permute {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (σ : Equiv.Perm ι) (f : ι → M) :
    ∑ i, f (σ i) = ∑ i, f i := by
  exact Equiv.sum_comp σ f

theorem reindex_columns_mulVec {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (y : Fin n → ℝ) :
    (W.submatrix id σ) *ᵥ y = W *ᵥ (fun i => y (σ.symm i)) := by
  ext k
  simpa [Matrix.submatrix,Matrix.mulVec,dotProduct] using
    sum_permute σ (fun i => W k i*y (σ.symm i))

theorem reindex_square_mulVec {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    (P.submatrix σ σ) *ᵥ (fun i => x (σ i)) =
      fun i => (P *ᵥ x) (σ i) := by
  ext i
  simpa [Matrix.submatrix,Matrix.mulVec,dotProduct] using
    sum_permute σ (fun j => P (σ i) j*x j)

theorem reindex_range_iff {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (y : Fin n → ℝ) :
    y ∈ (P.submatrix σ σ).mulVecLin.range ↔
      (fun i => y (σ.symm i)) ∈ P.mulVecLin.range := by
  constructor
  · rintro ⟨x,hx⟩
    change (P.submatrix σ σ) *ᵥ x = y at hx
    refine ⟨fun i => x (σ.symm i),?_⟩
    have he := reindex_square_mulVec P σ (fun i => x (σ.symm i))
    simp only [Equiv.symm_apply_apply] at he
    ext i
    have hi := congrFun he (σ.symm i)
    simpa [Matrix.mulVecLin_apply,hx] using hi.symm
  · rintro ⟨x,hx⟩
    refine ⟨fun i => x (σ i),?_⟩
    rw [Matrix.mulVecLin_apply,reindex_square_mulVec]
    ext i
    have hi := congrFun hx (σ i)
    simpa [Matrix.mulVecLin_apply] using hi

theorem reindex_relation_matrix {m n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin m) (Fin n) ℝ)
    (hker : ∀ y, W *ᵥ y = 0 ↔ y ∈ P.mulVecLin.range)
    (σ : Equiv.Perm (Fin n)) :
    ∀ y, (W.submatrix id σ) *ᵥ y = 0 ↔
      y ∈ (P.submatrix σ σ).mulVecLin.range := by
  intro y
  rw [reindex_columns_mulVec,hker,reindex_range_iff]

end VolumeVerification.ProjectionLinearRelations

