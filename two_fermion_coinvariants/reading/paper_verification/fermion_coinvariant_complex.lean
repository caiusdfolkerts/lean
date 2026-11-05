module

public import PaperVerification.FermionCoinvariantMoments
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The exact complex invariant ideals in Section 8.1

The primitive root and factorial-unit hypotheses
of the general field theorem are discharged here from the actual complex
exponential and characteristic zero. Neither is a premise of these results.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.Coinvariants

variable {n r a : ℕ}

theorem complex_primitive_unit (hr : 0<r) :
    ∃ ζ : ℂˣ,IsPrimitiveRoot (ζ : ℂ) r := by
  have h := Complex.isPrimitiveRoot_exp r hr.ne'
  obtain ⟨ζ,hζ⟩ := h.isUnit hr.ne'
  exact ⟨ζ,by simpa only [hζ] using h⟩

theorem complex_factorial_unit (n : ℕ) : IsUnit (n.factorial : ℂ) :=
  isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- All r≥2 and 1≤a≤r−1 from the printed opposite-character application. -/
theorem complex_positiveInvariantIdeal_eq_paired (hr : 2≤r) (ha : 1≤a) (har : a≤r-1) :
    positiveInvariantIdeal (R := ℂ) (n := n) (r := r) a (r-a)=
      pairedIdeal (fun _ : Fin n ↦ (1 : ℂ))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing ℂ n)^r)
        (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a)) := by
  have hr' : 0<r := by omega
  obtain ⟨ζ,hζ⟩ := complex_primitive_unit hr'
  exact positiveInvariantIdeal_eq_paired hr' (by omega) (by omega)
    (complex_factorial_unit n) ζ hζ

/-- The trivial-exterior-character case includes r=1, the original type A. -/
theorem complex_positiveInvariantIdeal_eq_strict (hr : 0<r) :
    positiveInvariantIdeal (R := ℂ) (n := n) (r := r) 0 0=
      strictIdeal (fun _ : Fin n ↦ (1 : ℂ))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing ℂ n)^r) := by
  obtain ⟨ζ,hζ⟩ := complex_primitive_unit hr
  exact positiveInvariantIdeal_eq_strict hr (complex_factorial_unit n) ζ hζ

def complexOppositeCoinvariantEquiv (hr : 2≤r) (ha : 1≤a) (har : a≤r-1) :
    CoinvariantAlgebra (R := ℂ) (n := n) (r := r) a (r-a) ≃ₐ[ℂ]
      PairedQuotient (fun _ : Fin n ↦ (1 : ℂ))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing ℂ n)^r)
        (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a)) :=
  quotientEquivOfIdealEq (complex_positiveInvariantIdeal_eq_paired hr ha har)

def complexTrivialColorCoinvariantEquiv (hr : 0<r) :
    CoinvariantAlgebra (R := ℂ) (n := n) (r := r) 0 0 ≃ₐ[ℂ]
      StrictQuotient (fun _ : Fin n ↦ (1 : ℂ))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing ℂ n)^r) :=
  quotientEquivOfIdealEq (complex_positiveInvariantIdeal_eq_strict hr)

end PaperVerification.Fermion.Coinvariants
