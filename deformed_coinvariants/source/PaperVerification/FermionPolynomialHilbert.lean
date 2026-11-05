module

public import PaperVerification.FermionGradedHilbert
public import PaperVerification.HilbertTowerCount
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The Hilbert series of the weighted polynomial ring

The homogeneous basis is the literal monomial basis. A coordinate split gives
the complete generating-series identity, for all positive integer weights.
No rational-function formula is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.GradedHilbert

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def polynomialGrading (w : Fin n → ℕ) :
    TauCeti.InternalGrading K (MvPolynomial (Fin n) K) ℕ :=
  .ofDecomposition (weightedHomogeneousSubmodule K w)

@[simp] theorem polynomialGrading_piece (w : Fin n → ℕ) (e : ℕ) :
    (polynomialGrading (K := K) w).piece e = weightedHomogeneousSubmodule K w e := by
  simp only [polynomialGrading, TauCeti.InternalGrading.ofDecomposition_piece]

theorem polynomial_piece_finite (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (e : ℕ) :
    Module.Finite K ((polynomialGrading (K := K) w).piece e) := by
  rw [polynomialGrading_piece]
  exact Module.Finite.iff_fg.mpr
    (weightedHomogeneousSubmodule_fg K w (fun i ↦ (hw i).ne') e)

/-- Weighted degree written using ordinary exponent functions on the finite
variable set. -/
def exponentWeight (w : Fin n → ℕ) (a : Fin n → ℕ) : ℕ := ∑ i, a i * w i

def exponentFibreEquiv (w : Fin n → ℕ) (e : ℕ) :
    HilbertTowerCount.Fibre (exponentWeight w) e ≃
      {a : Fin n →₀ ℕ // Finsupp.weight w a = e} where
  toFun a := ⟨Finsupp.equivFunOnFinite.symm a.val, by
    simpa only [Finsupp.weight_eq_sum, Finsupp.coe_equivFunOnFinite_symm,
      nsmul_eq_mul, Nat.cast_id, exponentWeight] using a.property⟩
  invFun a := ⟨a.val, by
    simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, Nat.cast_id, exponentWeight] using a.property⟩
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm_apply_apply a.val

theorem exponent_fibre_finite (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (e : ℕ) :
    Finite (HilbertTowerCount.Fibre (exponentWeight w) e) := by
  letI := (Finsupp.finite_of_nat_weight_eq w (fun i ↦ (hw i).ne') e).to_subtype
  exact Finite.of_equiv _ (exponentFibreEquiv w e).symm

/-- Coefficient counting in the actual homogeneous polynomial subspace. -/
theorem polynomial_piece_finrank (w : Fin n → ℕ) (e : ℕ) :
    Module.finrank K ((polynomialGrading (K := K) w).piece e) =
      Nat.card (HilbertTowerCount.Fibre (exponentWeight w) e) := by
  rw [polynomialGrading_piece, weightedHomogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank K (restrictSupport K {a : Fin n →₀ ℕ | Finsupp.weight w a = e}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  exact (Nat.card_congr (exponentFibreEquiv w e)).symm

def exponentSeries (w : Fin n → ℕ) : PowerSeries ℤ :=
  HilbertTowerCount.basisSeries (exponentWeight w)

theorem polynomial_series_eq_exponentSeries (w : Fin n → ℕ) :
    series (polynomialGrading (K := K) w) = exponentSeries w := by
  ext e
  simp only [coeff_series, exponentSeries, HilbertTowerCount.basisSeries,
    PowerSeries.coeff_mk, polynomial_piece_finrank]

/-- Split the exponent at the first variable off from all the remaining
exponents. This includes every exponent, without an imposed bound. -/
def exponentTowerEquiv (w : Fin (n + 1) → ℕ) (e : ℕ) :
    HilbertTowerCount.Fibre (exponentWeight w) e ≃
      HilbertTowerCount.Towers (exponentWeight (fun i ↦ w i.succ)) (w 0) e where
  toFun a := ⟨(a.val 0, fun i ↦ a.val i.succ), by
    simpa only [exponentWeight, Fin.sum_univ_succ] using a.property⟩
  invFun a := ⟨Fin.cons a.val.1 a.val.2, by
    simpa only [exponentWeight, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      using a.property⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv _ := rfl

theorem exponentSeries_succ (w : Fin (n + 1) → ℕ) :
    exponentSeries w =
      HilbertTowerCount.towerSeries (exponentWeight (fun i ↦ w i.succ)) (w 0) := by
  ext e
  simp only [exponentSeries, HilbertTowerCount.basisSeries,
    HilbertTowerCount.towerSeries, PowerSeries.coeff_mk]
  exact congrArg (fun z : ℕ ↦ (z : ℤ)) (Nat.card_congr (exponentTowerEquiv w e))

theorem exponentSeries_zero (w : Fin 0 → ℕ) : exponentSeries w = 1 := by
  ext e
  cases e with
  | zero =>
    simp [exponentSeries, HilbertTowerCount.basisSeries,
      HilbertTowerCount.Fibre, exponentWeight]
  | succ e =>
    haveI : IsEmpty (HilbertTowerCount.Fibre (exponentWeight w) (e + 1)) :=
      ⟨fun a ↦ by simpa [exponentWeight] using a.property⟩
    simp [exponentSeries, HilbertTowerCount.basisSeries]

/-- The exact denominator identity for all finite numbers of variables and
all positive integer weights. -/
theorem denominator_mul_exponentSeries (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    (∏ i, (1 - PowerSeries.X ^ w i)) * exponentSeries w = 1 := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, exponentSeries_zero]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    calc
      _ = (∏ i : Fin n, (1 - PowerSeries.X ^ w i.succ)) *
          ((1 - PowerSeries.X ^ w 0) * exponentSeries w) := by
            rw [mul_assoc, mul_left_comm]
      _ = (∏ i : Fin n, (1 - PowerSeries.X ^ w i.succ)) *
          exponentSeries (fun i ↦ w i.succ) := by
            rw [exponentSeries_succ,
              HilbertTowerCount.denominator_mul_towerSeries
                (exponentWeight (fun i ↦ w i.succ)) (w 0) (hw 0)
                (exponent_fibre_finite _ (fun i ↦ hw i.succ))]
            rfl
      _ = 1 := ih (fun i ↦ w i.succ) (fun i ↦ hw i.succ)

theorem denominator_mul_polynomial_series (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    (∏ i, (1 - PowerSeries.X ^ w i)) * series (polynomialGrading (K := K) w) = 1 := by
  rw [polynomial_series_eq_exponentSeries]
  exact denominator_mul_exponentSeries w hw

end PaperVerification.GradedHilbert
