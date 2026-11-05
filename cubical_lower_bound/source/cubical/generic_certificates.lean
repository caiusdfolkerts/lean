import cubical.generic_rank

/-!
# Explicit polynomial certificates for simultaneous generic rank

The witnesses are nonzero polynomials. Every parameter choice outside
their zero sets satisfies all requested rank conditions, giving the
precise algebraic meaning of "for generic parameters".
-/

namespace Cubical

open Matrix

/-- A polynomial matrix that has one injective specialization has a
nonzero Gram-determinant polynomial. -/
theorem gramPolynomial_ne_zero
    {σ R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (A : Matrix R C (MvPolynomial σ ℝ))
    (hA : ∃ x : σ → ℝ, Function.Injective (evalMatrix A x).mulVec) :
    (Aᵀ * A).det ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ := hA
  have hne := (gram_det_ne_zero_iff (evalMatrix A x)).mpr hx
  rw [← eval_gram_det, hzero, map_zero] at hne
  exact hne rfl

/-- A single nonzero polynomial certifies every rank condition in two
finite families, without identifying their row or column index types. -/
theorem simultaneous_injective_certificate_pair
    {σ J K : Type*} [Fintype J] [Fintype K]
    {R C : J → Type*} {S D : K → Type*}
    [∀ j, Fintype (R j)] [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]
    [∀ k, Fintype (S k)] [∀ k, Fintype (D k)] [∀ k, DecidableEq (D k)]
    (A : ∀ j, Matrix (R j) (C j) (MvPolynomial σ ℝ))
    (B : ∀ k, Matrix (S k) (D k) (MvPolynomial σ ℝ))
    (hA : ∀ j, ∃ x : σ → ℝ, Function.Injective (evalMatrix (A j) x).mulVec)
    (hB : ∀ k, ∃ x : σ → ℝ, Function.Injective (evalMatrix (B k) x).mulVec) :
    ∃ P : MvPolynomial σ ℝ, P ≠ 0 ∧ ∀ x : σ → ℝ, MvPolynomial.eval x P ≠ 0 →
      (∀ j, Function.Injective (evalMatrix (A j) x).mulVec) ∧
      (∀ k, Function.Injective (evalMatrix (B k) x).mulVec) := by
  classical
  let P := (∏ j, ((A j)ᵀ * A j).det) * (∏ k, ((B k)ᵀ * B k).det)
  have hP : P ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun j _ => gramPolynomial_ne_zero (A j) (hA j))
    (Finset.prod_ne_zero_iff.mpr fun k _ => gramPolynomial_ne_zero (B k) (hB k))
  refine ⟨P, hP, ?_⟩
  intro x hx
  change MvPolynomial.eval x
    ((∏ j, ((A j)ᵀ * A j).det) * (∏ k, ((B k)ᵀ * B k).det)) ≠ 0 at hx
  rw [map_mul, mul_ne_zero_iff, map_prod, map_prod] at hx
  constructor
  · intro j
    apply (gram_det_ne_zero_iff _).mp
    rw [← eval_gram_det]
    exact Finset.prod_ne_zero_iff.mp hx.1 j (Finset.mem_univ j)
  · intro k
    apply (gram_det_ne_zero_iff _).mp
    rw [← eval_gram_det]
    exact Finset.prod_ne_zero_iff.mp hx.2 k (Finset.mem_univ k)

end Cubical
