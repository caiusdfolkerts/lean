module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section

/-!
# Actual orders along coordinate boundary primes

The local ring is the literal localization at the principal coordinate
prime. Its DVR structure, its uniformizer, and the units in the other
coordinate directions are proved. The order is Mathlib's order of
vanishing defined from module length and its fraction-field extension,
rather than a newly defined exponent function.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open IsLocalRing
open scoped BigOperators Classical nonZeroDivisors

section PrincipalPrime

variable (R S : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime S P] [IsLocalRing S] [IsDomain S]

theorem maximalIdeal_eq_span_of_principalPrime (p : R) (hP : P = Ideal.span {p}) :
    maximalIdeal S = Ideal.span {algebraMap R S p} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P S, hP,
    Ideal.map_span, Set.image_singleton]

/-- A Noetherian domain localized at a nonzero principal prime is a DVR.
The conclusion is proved from the actual principal maximal ideal. -/
theorem principalPrimeLocalization_isDiscreteValuationRing
    (p : R) (hp : p ≠ 0) (hP : P = Ideal.span {p}) :
    IsDiscreteValuationRing S := by
  letI : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing P.primeCompl S inferInstance
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hp' : algebraMap R S p ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hp
  have hmax := maximalIdeal_eq_span_of_principalPrime R S P p hP
  have hnot : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    rw [hmax, Ideal.span_singleton_eq_bot]
    exact hp'
  have hprincipal : (maximalIdeal S).IsPrincipal := by
    rw [hmax]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE S hnot).out 5 1).mp hprincipal

theorem principalPrimeLocalization_generator_irreducible
    (p : R) (hp : p ≠ 0) (hP : P = Ideal.span {p}) :
    Irreducible (algebraMap R S p) := by
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact (map_ne_zero_iff _
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).mpr hp
  · exact maximalIdeal_eq_span_of_principalPrime R S P p hP

end PrincipalPrime

variable (k : Type*) [Field k] {n : ℕ}

/-- The actual prime ideal defining the i-th coordinate boundary. -/
def coordinatePrime (i : Fin n) : Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span {MvPolynomial.X i}

instance coordinatePrime_isPrime (i : Fin n) : (coordinatePrime k i).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (MvPolynomial.X_prime (R := k) (i := i))

abbrev coordinateBoundaryLocalRing (i : Fin n) :=
  Localization.AtPrime (coordinatePrime k i)

instance coordinateBoundaryLocalRing_isDomain (i : Fin n) :
    IsDomain (coordinateBoundaryLocalRing k i) :=
  IsLocalization.isDomain_of_atPrime _ (coordinatePrime k i)

instance coordinateBoundaryLocalRing_isDiscreteValuationRing (i : Fin n) :
    IsDiscreteValuationRing (coordinateBoundaryLocalRing k i) :=
  principalPrimeLocalization_isDiscreteValuationRing
    (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i)
    (coordinatePrime k i) (MvPolynomial.X i) (MvPolynomial.X_ne_zero i) rfl

def coordinateBoundaryParameter (i j : Fin n) : coordinateBoundaryLocalRing k i :=
  algebraMap (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i) (MvPolynomial.X j)

theorem coordinateBoundaryParameter_irreducible (i : Fin n) :
    Irreducible (coordinateBoundaryParameter k i i) :=
  principalPrimeLocalization_generator_irreducible
    (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i)
    (coordinatePrime k i) (MvPolynomial.X i) (MvPolynomial.X_ne_zero i) rfl

theorem coordinateBoundaryParameter_isUnit (i j : Fin n) (hij : i ≠ j) :
    IsUnit (coordinateBoundaryParameter k i j) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (S := coordinateBoundaryLocalRing k i) (I := coordinatePrime k i)
      (MvPolynomial.X j)).mpr
  change MvPolynomial.X j ∉ Ideal.span {MvPolynomial.X i}
  rw [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X]
  exact hij

variable (i : Fin n) (K : Type*) [Field K]
    [Algebra (coordinateBoundaryLocalRing k i) K]
    [IsFractionRing (coordinateBoundaryLocalRing k i) K]

/-- The literal order of the coordinate defining the boundary is one. -/
theorem ordFrac_X_i :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i i)) = WithZero.exp (1 : ℤ) :=
  Ring.ordFrac_irreducible (coordinateBoundaryParameter_irreducible k i)

theorem ordFrac_X_other (j : Fin n) (hij : i ≠ j) :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) = 1 :=
  Ring.ordFrac_of_isUnit (coordinateBoundaryParameter_isUnit k i j hij)

theorem ordFrac_coordinate_product :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (∏ j : Fin n, algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) = WithZero.exp (1 : ℤ) := by
  rw [map_prod]
  rw [Finset.prod_eq_single i]
  · exact ordFrac_X_i k i K
  · intro j hj hji
    exact ordFrac_X_other k i K j hji.symm
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The coefficient of a logarithmic volume relative to a regular
coordinate volume has the genuine order -1 at every boundary prime. -/
theorem ordFrac_inverse_coordinate_product :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      ((∏ j : Fin n, algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j))⁻¹) = WithZero.exp (-1 : ℤ) := by
  rw [map_inv₀, ordFrac_coordinate_product, WithZero.inv_exp]

/-- The familiar exponent formula is a consequence of actual DVR order,
and holds for all integral character exponents. -/
theorem ordFrac_coordinate_character (m : Fin n → ℤ) :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (∏ j : Fin n, (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) ^ m j) = WithZero.exp (m i) := by
  rw [map_prod]
  simp_rw [map_zpow₀]
  rw [Finset.prod_eq_single i]
  · rw [ordFrac_X_i, ← WithZero.exp_zsmul]
    simp
  · intro j hj hji
    rw [ordFrac_X_other k i K j hji.symm, one_zpow]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.principalPrimeLocalization_isDiscreteValuationRing
#print axioms PaperVerification.ToricSchemes.ordFrac_inverse_coordinate_product

