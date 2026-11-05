module

public import PaperVerification.PowerComplex
public import PaperVerification.PowerParameters
public import PaperVerification.FermionOrdinaryParameters
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The exact generic coefficient fiber

The coefficients here are independent polynomial indeterminates, embedded in
their fraction field. Every nonempty subset sum is proved nonzero in arbitrary
characteristic. The ordinary support theorem then proves regularity of the
actual weighted-power sequence, so exactness of the zero-slope complex is a
theorem and not an additional assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {R : Type*} [CommRing R] {n : ℕ}

def ordinaryPowerIdeal (c : Fin n → R) (m : ℕ) : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun j : Fin n => weightedPower c (m+j.val))

theorem tailHit_zero_eq_ordinaryPowerIdeal (c : Fin n → R) (m : ℕ) :
    tailHit c 0 m = (ordinaryPowerIdeal c m).restrictScalars R := by
  rw [tailHit_eq_firstTailHit]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, q, rfl⟩
    rw [reversed_zero_slope]
    exact (ordinaryPowerIdeal c m).mul_mem_right q (Ideal.subset_span ⟨j, rfl⟩)
  · intro p hp
    obtain ⟨v, hv⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    rw [← hv]
    apply Submodule.sum_mem
    intro j _
    have h : reversed c 0 (m+j.val) (v j) = v j * weightedPower c (m+j.val) := by
      rw [reversed_zero_slope, mul_comm]
    rw [← h]
    exact Submodule.subset_span ⟨j, v j, rfl⟩

variable (K : Type*) [Field K]

abbrev GenericCoefficientField (n : ℕ) := FractionRing (MvPolynomial (Fin n) K)

def genericCoefficient (n : ℕ) (i : Fin n) : GenericCoefficientField K n :=
  algebraMap (MvPolynomial (Fin n) K) (GenericCoefficientField K n) (X i)

theorem indeterminate_subset_sum_ne_zero (I : Finset (Fin n)) (hI : I.Nonempty) :
    (∑ i ∈ I, (X i : MvPolynomial (Fin n) K)) ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hI
  intro hz
  have h := congrArg (MvPolynomial.eval (fun j : Fin n => if j = i then (1 : K) else 0)) hz
  simpa [hi] using h

theorem genericCoefficient_subset_sum_ne_zero (I : Finset (Fin n)) (hI : I.Nonempty) :
    (∑ i ∈ I, genericCoefficient K n i) ≠ 0 := by
  change (∑ i ∈ I,
    algebraMap (MvPolynomial (Fin n) K) (GenericCoefficientField K n) (X i)) ≠ 0
  rw [← map_sum]
  exact (map_ne_zero_iff _ (IsFractionRing.injective
    (MvPolynomial (Fin n) K) (GenericCoefficientField K n))).mpr
      (indeterminate_subset_sum_ne_zero K I hI)

theorem genericCoefficient_subset_sum_unit (I : Finset (Fin n)) (hI : I.Nonempty) :
    IsUnit (∑ i ∈ I, genericCoefficient K n i) :=
  isUnit_iff_ne_zero.mpr (genericCoefficient_subset_sum_ne_zero K I hI)

theorem genericCoefficient_nonresonant (m : ℕ) :
    Nonresonant (genericCoefficient K n) 0 m := by
  intro I hI s _
  simpa only [zero_mul, add_zero] using genericCoefficient_subset_sum_ne_zero K I hI

theorem weightedPower_eq_powerMoment {F : Type*} [Field F] (c : Fin n → F) (m j : ℕ) :
    weightedPower c (m+j) = Fermion.powerMoment (fun _ => 1) c m j := by
  simp only [weightedPower, Fermion.powerMoment, Nat.one_mul]

theorem ordinaryPowerIdeal_eq_powerMomentIdeal {F : Type*} [Field F] (c : Fin n → F) (m : ℕ) :
    ordinaryPowerIdeal c m = Fermion.powerMomentIdeal (fun _ => 1) c m := by
  simp only [ordinaryPowerIdeal, Fermion.powerMomentIdeal, weightedPower_eq_powerMoment]

theorem generic_weighted_power_regular (m : ℕ) (hm : 0 < m) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) (GenericCoefficientField K n))
      (List.ofFn fun j : Fin n => weightedPower (genericCoefficient K n) (m+j.val)) := by
  simpa only [weightedPower_eq_powerMoment] using
    Fermion.powerMoments_isWeaklyRegular (fun _ : Fin n => 1)
      (genericCoefficient K n) m (fun _ => Nat.zero_lt_one) hm
      (genericCoefficient_subset_sum_unit K)

theorem generic_ordinary_quotient_finite (m : ℕ) :
    Module.Finite (GenericCoefficientField K n)
      (MvPolynomial (Fin n) (GenericCoefficientField K n) ⧸
        ordinaryPowerIdeal (genericCoefficient K n) m) := by
  rw [ordinaryPowerIdeal_eq_powerMomentIdeal]
  exact Fermion.powerMoment_quotient_finite (fun _ : Fin n => 1)
    (genericCoefficient K n) m (genericCoefficient_subset_sum_unit K)

theorem generic_zero_slope_exact (m : ℕ) (hm : 0 < m) :
    LinearMap.range (syzygyMap (genericCoefficient K n) 0 m) =
      LinearMap.ker (tailMap (genericCoefficient K n) 0 m) :=
  zero_slope_exact_of_regular _ _ (generic_weighted_power_regular K m hm)

end PaperVerification.PowerOperators
