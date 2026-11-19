module

public import TauCeti.RingTheory.MvPolynomial.Dominant
public import TauCeti.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Choose

/-!
# Polynomial rank certificates from a dominant parametrization

This file contains general algebraic lemmas used to pass from an explicit pencil orbit
to a nonempty principal open set on which all relevant relation matrices have constant rank.
The orbit Jacobian and rank invariance must be proved by the application.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix

variable {K σ ι : Type*}

/-- A polynomial over an infinite domain that vanishes where a fixed nonzero polynomial
does not vanish is zero. -/
theorem polynomial_eq_zero_of_principal_open_vanish
    [CommRing K] [IsDomain K] [Infinite K]
    {g q : MvPolynomial σ K} (hg : g ≠ 0)
    (hq : ∀ x : σ → K, eval x g ≠ 0 → eval x q = 0) : q = 0 := by
  have hmul : g * q = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_mul, map_zero]
    by_cases hx : eval x g = 0
    · rw [hx, zero_mul]
    · rw [hq x hx, mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left hg

/-- A polynomial vanishing on a principal open subset of a parametrized image is zero,
provided the parametrization has a surjective Jacobian at one point. -/
theorem polynomial_eq_zero_of_dominant_open_vanish
    [CommRing K] [IsDomain K] [Infinite K] [Fintype σ] [Finite ι]
    {p : ι → MvPolynomial σ K} {v : σ → K}
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective)
    {g : MvPolynomial σ K} (hg : g ≠ 0)
    {q : MvPolynomial ι K}
    (hq : ∀ x : σ → K, eval x g ≠ 0 →
      eval (fun i ↦ eval x (p i)) q = 0) : q = 0 := by
  apply AlgebraicIndependent.eq_zero_of_aeval_eq_zero
    (TauCeti.algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt hJ) q
  apply polynomial_eq_zero_of_principal_open_vanish hg
  intro x hx
  rw [aeval_eq_bind₁, ← hq x hx]
  simpa only [aeval_eq_eval] using aeval_bind₁ x p q

section Matrices

variable [Field K] {m n : Type*} [Finite m] [Fintype n]

/-- Evaluating the polynomial minor is the minor of the evaluated matrix. -/
theorem polynomialMatrix_eval_minor
    (M : Matrix m n (MvPolynomial ι K)) (x : ι → K)
    {d : ℕ} (r : Fin d ↪ m) (c : Fin d ↪ n) :
    eval x (M.submatrix r c).det = ((M.map (eval x)).submatrix r c).det := by
  simpa only [Matrix.submatrix_map, RingHom.mapMatrix_apply] using
    RingHom.map_det (eval x) (M.submatrix r c)

/-- A rank upper bound on the image of a dominant parametrization, away from the
zero locus of a nonzero parameter polynomial, holds for every coefficient point. -/
theorem polynomialMatrix_rank_le_of_dominant_open
    [Infinite K] [Fintype σ] [Finite ι]
    (M : Matrix m n (MvPolynomial ι K))
    {p : ι → MvPolynomial σ K} {v : σ → K}
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective)
    {g : MvPolynomial σ K} (hg : g ≠ 0) {r : ℕ}
    (hbound : ∀ x : σ → K, eval x g ≠ 0 →
      (M.map (eval (fun i ↦ eval x (p i)))).rank ≤ r) :
    ∀ y : ι → K, (M.map (eval y)).rank ≤ r := by
  intro y
  apply Matrix.rank_le_iff_forall_det_submatrix_eq_zero.mpr
  intro rows cols
  have hminor : (M.submatrix rows cols).det = 0 := by
    apply polynomial_eq_zero_of_dominant_open_vanish hJ hg
    intro x hx
    rw [polynomialMatrix_eval_minor]
    exact Matrix.rank_le_iff_forall_det_submatrix_eq_zero.mp (hbound x hx) rows cols
  rw [← polynomialMatrix_eval_minor, hminor, map_zero]

/-- A maximal minor at a specified point gives an explicit principal open set
on which the rank is at least its value at that point. -/
theorem polynomialMatrix_exists_rank_lower_certificate
    (M : Matrix m n (MvPolynomial ι K)) (base : ι → K) :
    ∃ q : MvPolynomial ι K, eval base q ≠ 0 ∧
      ∀ y : ι → K, eval y q ≠ 0 →
        (M.map (eval base)).rank ≤ (M.map (eval y)).rank := by
  obtain ⟨rows, cols, hminor⟩ :=
    Matrix.le_rank_iff_exists_det_submatrix_ne_zero.mp
      (le_refl (M.map (eval base)).rank)
  refine ⟨(M.submatrix rows cols).det, ?_, ?_⟩
  · rw [polynomialMatrix_eval_minor]
    exact hminor
  · intro y hy
    apply Matrix.le_rank_iff_exists_det_submatrix_ne_zero.mpr
    refine ⟨rows, cols, ?_⟩
    rwa [← polynomialMatrix_eval_minor]

/-- Constant rank on a principal open subset of a dominant parametrized image yields
a nonempty principal open subset of the full coefficient space with that exact rank.
The witness polynomial is a maximal minor at the specified base point. -/
theorem polynomialMatrix_generic_rank_from_orbit
    [Infinite K] [Fintype σ] [Finite ι]
    (M : Matrix m n (MvPolynomial ι K))
    {p : ι → MvPolynomial σ K} {v : σ → K}
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective)
    {g : MvPolynomial σ K} (hg : g ≠ 0) (base : ι → K)
    (horbit : ∀ x : σ → K, eval x g ≠ 0 →
      (M.map (eval (fun i ↦ eval x (p i)))).rank = (M.map (eval base)).rank) :
    ∃ q : MvPolynomial ι K, eval base q ≠ 0 ∧
      ∀ y : ι → K, eval y q ≠ 0 →
        (M.map (eval y)).rank = (M.map (eval base)).rank := by
  obtain ⟨q, hbase, hlower⟩ := polynomialMatrix_exists_rank_lower_certificate M base
  refine ⟨q, hbase, fun y hy ↦ le_antisymm ?_ (hlower y hy)⟩
  exact polynomialMatrix_rank_le_of_dominant_open M hJ hg
    (fun x hx ↦ (horbit x hx).le) y

end Matrices

/-- A finite list of principal open certificates can be made simultaneous by
multiplying their witness polynomials. Nonemptiness is retained at the given point. -/
theorem exists_simultaneous_principal_certificate
    [CommRing K] [IsDomain K] {δ : Type*} [Fintype δ]
    (base : ι → K) (P : δ → (ι → K) → Prop)
    (h : ∀ d : δ, ∃ q : MvPolynomial ι K, eval base q ≠ 0 ∧
      ∀ y : ι → K, eval y q ≠ 0 → P d y) :
    ∃ q : MvPolynomial ι K, eval base q ≠ 0 ∧
      ∀ y : ι → K, eval y q ≠ 0 → ∀ d : δ, P d y := by
  classical
  choose q hbase hcert using h
  refine ⟨∏ d, q d, ?_, ?_⟩
  · simpa only [map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ,
      true_implies] using hbase
  · intro y hy d
    apply hcert d y
    have hy' : ∀ d : δ, eval y (q d) ≠ 0 := by
      simpa only [map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ,
        true_implies] using hy
    exact hy' d

end PaperVerification.AlternatingForms
