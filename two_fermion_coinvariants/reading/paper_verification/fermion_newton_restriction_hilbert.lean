module

public import PaperVerification.FermionNewtonRestrictionDenominator

/-!
# The full Hilbert identity for Newton restriction

Every series coefficient is the dimension of the actual coordinate-homogeneous
numerator subspace. The identity follows from the proved Newton bases and the
proved change of each column degree; restriction surjectivity is not assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

theorem numeratorHilbertSeries
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    GradedHilbert.vectorHilbertSeries (K := F) (numeratorModule β δ σ) =
      (∑ i : Fin n, PowerSeries.X ^ columnNumeratorDegree δ σ i) *
        GradedHilbert.series (GradedHilbert.polynomialGrading (K := F) (fun _ : Fin n ↦ 1)) := by
  apply GradedHilbert.vectorHilbertSeries_eq_basis_sum (numeratorModule β δ σ)
    (newtonNumeratorBasis β δ σ hc hσ hβ) (columnNumeratorDegree δ σ)
  intro i k
  rw [newtonNumeratorBasis_apply]
  exact columnCommonNumerator_homogeneous β δ σ hc i k

theorem numeratorPiece_finite
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (e : ℕ) :
    Module.Finite F (GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ) e) := by
  apply GradedHilbert.vectorPiece_finite_of_polynomial_basis (numeratorModule β δ σ)
    (newtonNumeratorBasis β δ σ hc hσ hβ) (columnNumeratorDegree δ σ)
  intro i k
  rw [newtonNumeratorBasis_apply]
  exact columnCommonNumerator_homogeneous β δ σ hc i k

theorem columnNumeratorDegree_deleted_ne
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (q i : Fin n) (hi : i ≠ q) :
    columnNumeratorDegree (deletedMultiplicity δ q) σ i = columnNumeratorDegree δ σ i := by
  simp only [columnNumeratorDegree,deletedMultiplicity_ne δ q i hi]

theorem columnNumeratorDegree_deleted_self
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (q : Fin n) (hq : 0 < δ q) :
    columnNumeratorDegree (deletedMultiplicity δ q) σ q + 1 = columnNumeratorDegree δ σ q := by
  have hn := earlierNegative_card_le σ q
  simp only [columnNumeratorDegree,deletedMultiplicity_self]
  omega

theorem ordinaryPolynomialSeries_succ :
    (1 - PowerSeries.X) *
      GradedHilbert.series (GradedHilbert.polynomialGrading (K := F) (fun _ : Fin (n + 1) ↦ 1)) =
      GradedHilbert.series (GradedHilbert.polynomialGrading (K := F) (fun _ : Fin n ↦ 1)) := by
  rw [GradedHilbert.polynomial_series_eq_exponentSeries,
    GradedHilbert.polynomial_series_eq_exponentSeries,GradedHilbert.exponentSeries_succ]
  simpa only [pow_one,GradedHilbert.exponentSeries] using HilbertTowerCount.denominator_mul_towerSeries
    (GradedHilbert.exponentWeight (fun _ : Fin n ↦ 1)) 1 (by omega)
    (GradedHilbert.exponent_fibre_finite _ (by simp))

/-- The exact numerator version of the rational-field Hilbert identity in
Proposition 2.3. The incident denominator factors explain the displayed shift. -/
theorem numerator_restriction_hilbert_identity
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hc : Compatible δ σ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin (n + 1)), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) :
    GradedHilbert.vectorHilbertSeries (K := F) (numeratorModule β δ σ) -
      PowerSeries.X * GradedHilbert.vectorHilbertSeries (K := F)
        (numeratorModule β (deletedMultiplicity δ q) σ) =
      PowerSeries.X ^ (negativeNeighbours σ q).card *
        GradedHilbert.vectorHilbertSeries (K := F)
          (numeratorModule (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)) := by
  rw [numeratorHilbertSeries β δ σ hc hσ hβ,
    numeratorHilbertSeries β (deletedMultiplicity δ q) σ (Compatible.deleted δ σ hc q hq) hσ hβ,
    numeratorHilbertSeries (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)
      (Compatible.restricted δ σ hσ hc q hq) (fun i ↦ hσ (q.succAbove i))
      (subset_weights_restricted β hβ q)]
  let W : PowerSeries ℤ := ∑ i : Fin n,
    PowerSeries.X ^ columnNumeratorDegree (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) i
  let b := (negativeNeighbours σ q).card
  have hsum : (∑ i : Fin n, (PowerSeries.X : PowerSeries ℤ) ^ columnNumeratorDegree δ σ (q.succAbove i)) =
      PowerSeries.X ^ b * W := by
    simp_rw [columnNumeratorDegree_restriction δ σ hσ hc q hq, pow_add]
    exact (Finset.mul_sum _ _ _).symm
  have hdel : (∑ i : Fin (n + 1), (PowerSeries.X : PowerSeries ℤ) ^
      columnNumeratorDegree (deletedMultiplicity δ q) σ i) =
      PowerSeries.X ^ columnNumeratorDegree (deletedMultiplicity δ q) σ q +
        PowerSeries.X ^ b * W := by
    rw [Fin.sum_univ_succAbove _ q]
    simp_rw [columnNumeratorDegree_deleted_ne δ σ q _ (Fin.succAbove_ne q _)]
    rw [hsum]
  rw [Fin.sum_univ_succAbove _ q,hsum,hdel,
    ← columnNumeratorDegree_deleted_self δ σ q hq.1,pow_succ]
  calc
    _ = PowerSeries.X ^ b * W * ((1 - PowerSeries.X) *
        GradedHilbert.series (GradedHilbert.polynomialGrading (K := F) (fun _ : Fin (n + 1) ↦ 1))) := by ring
    _ = _ := by rw [ordinaryPolynomialSeries_succ]; exact mul_assoc _ _ _

theorem numerator_restriction_piece_dimension
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hc : Compatible δ σ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin (n + 1)), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) (e : ℕ) :
    Module.finrank F (GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ)
      (e + (negativeNeighbours σ q).card)) =
      Module.finrank F (GradedHilbert.vectorHomogeneousPiece
        (numeratorModule (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)) e) +
      if 1 ≤ e + (negativeNeighbours σ q).card then
        Module.finrank F (GradedHilbert.vectorHomogeneousPiece
          (numeratorModule β (deletedMultiplicity δ q) σ) (e + (negativeNeighbours σ q).card - 1))
      else 0 := by
  have h := congrArg (PowerSeries.coeff (e + (negativeNeighbours σ q).card))
    (numerator_restriction_hilbert_identity β δ σ hc hσ hβ q hq)
  have hX (p : PowerSeries ℤ) (d : ℕ) :
      PowerSeries.coeff d (PowerSeries.X * p) =
        if 1 ≤ d then PowerSeries.coeff (d - 1) p else 0 := by
    simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' p 1 d
  rw [map_sub,hX,PowerSeries.coeff_X_pow_mul'] at h
  simp only [if_pos (Nat.le_add_left _ _),Nat.add_sub_cancel,
    GradedHilbert.vectorHilbertSeries,PowerSeries.coeff_mk] at h
  split_ifs at h ⊢ <;> omega

end PaperVerification.Fermion.Newton
