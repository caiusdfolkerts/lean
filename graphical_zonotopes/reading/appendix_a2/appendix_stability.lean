module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Papers.GraphicalZonotopes.AppendixPathMatrix

/-! # The upper-half-plane assertion in Proposition A.2

The determinant is the literal determinant of the displayed tridiagonal
matrix. Its nonvanishing follows from an injective weighted incidence map.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix

namespace GraphicalZonotopes.PathDeterminant

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A weighted Gram form has the expected sum-of-squares expansion, even
when its weights are complex. -/
theorem weightedGram_quadratic (B : Matrix ι κ ℂ) (t : ι → ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ ((Bᴴ * diagonal t * B) *ᵥ x) =
      ∑ i, t i * (Complex.normSq ((B *ᵥ x) i) : ℂ) := by
  calc
    _ = star (B *ᵥ x) ⬝ᵥ (diagonal t *ᵥ (B *ᵥ x)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
        vecMul_conjTranspose]
      have hxstar : star (star x) = x := by
        funext k
        change star (star (x k)) = x k
        exact _root_.star_star (x k)
      rw [hxstar]
    _ = _ := by
      simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro i hi
      change star ((B *ᵥ x) i) * (t i * (B *ᵥ x) i) = _
      rw [mul_left_comm]
      simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

/-- Positive imaginary weights make an injective weighted Gram matrix
nonsingular. The column-rank condition is an ordinary injectivity assertion.
-/
theorem weightedGram_det_ne_zero (B : Matrix ι κ ℂ)
    (hB : Function.Injective B.mulVec) (t : ι → ℂ)
    (ht : ∀ i, 0 < (t i).im) : (Bᴴ * diagonal t * B).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hy : B *ᵥ x ≠ 0 := by
    intro h
    apply hx
    apply hB
    simpa only [mulVec_zero] using h
  obtain ⟨j, hj⟩ : ∃ j, (B *ᵥ x) j ≠ 0 := by
    by_contra h
    apply hy
    ext j
    exact not_not.mp (not_exists.mp h j)
  have hsum : (∑ i, t i * (Complex.normSq ((B *ᵥ x) i) : ℂ)) = 0 := by
    rw [← weightedGram_quadratic, hker, dotProduct_zero]
  have him : ∑ i, (t i).im * Complex.normSq ((B *ᵥ x) i) = 0 := by
    have h := congrArg Complex.im hsum
    simpa using h
  have hp : 0 < ∑ i, (t i).im * Complex.normSq ((B *ᵥ x) i) := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (ht i).le (Complex.normSq_nonneg _)
    · exact ⟨j,mem_univ j,mul_pos (ht j) (Complex.normSq_pos.mpr hj)⟩
  exact (ne_of_gt hp) him

/-- The actual tridiagonal determinant is nonzero throughout the product
of open upper half planes, for every matrix size. -/
theorem tridiagonal_det_ne_zero (m : ℕ) (t : Fin (m+2) → ℂ)
    (ht : ∀ j, 0 < (t j).im) : (tridiagonal t).det ≠ 0 := by
  have h := weightedGram_det_ne_zero (incidence m)
    (incidence_mulVec_injective m) (t ∘ group m) (fun e => ht (group m e))
  rwa [incidence_conjTranspose,incidence_gram] at h

/-- The determinant polynomial in the paper's `m+2` independent variables. -/
def polynomial (R : Type*) [CommRing R] (m : ℕ) : MvPolynomial (Fin (m+2)) R :=
  (tridiagonal (fun j => MvPolynomial.X j)).det

/-- Real stability is stated directly by complex evaluation; there is no
finite sampling or additional spectral hypothesis in this predicate. -/
def IsRealStable {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ t : σ → ℂ, (∀ j, 0 < (t j).im) → MvPolynomial.eval₂ Complex.ofRealHom t p ≠ 0

theorem polynomial_eval (m : ℕ) (t : Fin (m+2) → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom t (polynomial ℝ m) = (tridiagonal t).det := by
  change (MvPolynomial.eval₂Hom Complex.ofRealHom t)
    (tridiagonal (fun j => MvPolynomial.X j)).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [MvPolynomial.coe_eval₂Hom, tridiagonal,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_zero]

theorem polynomial_realStable (m : ℕ) : IsRealStable (polynomial ℝ m) := by
  intro t ht
  rw [polynomial_eval]
  exact tridiagonal_det_ne_zero m t ht

variable {σ R : Type*} [CommRing R]

theorem homogeneous_det {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (MvPolynomial σ R))
    (hM : ∀ i j, (M i j).IsHomogeneous 1) : M.det.IsHomogeneous m := by
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  have hp := MvPolynomial.IsHomogeneous.prod (univ : Finset (Fin m))
    (fun i => M (s i) i) (fun _ => 1) (fun i _ => hM (s i) i)
  have hp' : (∏ i, M (s i) i).IsHomogeneous m := by simpa using hp
  simpa only [map_intCast] using hp'.C_mul (((Equiv.Perm.sign s : ℤ) : R))

theorem polynomial_homogeneous (R : Type*) [CommRing R] (m : ℕ) :
    (polynomial R m).IsHomogeneous m := by
  apply homogeneous_det
  intro i j
  unfold tridiagonal
  apply MvPolynomial.IsHomogeneous.sub
  · apply MvPolynomial.IsHomogeneous.sub
    · split_ifs
      · exact ((MvPolynomial.isHomogeneous_X _ _).add
          (MvPolynomial.isHomogeneous_X _ _)).add (MvPolynomial.isHomogeneous_X _ _)
      · exact MvPolynomial.isHomogeneous_zero _ _ _
    · split_ifs
      · exact MvPolynomial.isHomogeneous_X _ _
      · exact MvPolynomial.isHomogeneous_zero _ _ _
  · split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem polynomial_ne_zero (m : ℕ) : polynomial ℝ m ≠ 0 := by
  intro h
  have hs := polynomial_realStable m (fun _ => Complex.I) (fun _ => by simp)
  apply hs
  rw [h,MvPolynomial.eval₂_zero]

theorem polynomial_totalDegree (m : ℕ) : (polynomial ℝ m).totalDegree = m :=
  (polynomial_homogeneous ℝ m).totalDegree (polynomial_ne_zero m)

/-- The homogeneity, degree, and real-stability assertions of Proposition
A.2, for the literal determinant and with no restriction on its size.
The Newton-polytope and absolute-irreducibility assertions are separate.
-/
theorem proposition_A_2_stability (m : ℕ) :
    (polynomial ℝ m).IsHomogeneous m ∧
    (polynomial ℝ m).totalDegree = m ∧ IsRealStable (polynomial ℝ m) :=
  ⟨polynomial_homogeneous ℝ m,polynomial_totalDegree m,polynomial_realStable m⟩

end GraphicalZonotopes.PathDeterminant
