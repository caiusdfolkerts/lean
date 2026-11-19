module

public import PaperVerification.AlternatingFormsOddIntegralBasis
public import PaperVerification.AlternatingFormsExteriorBaseChange
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Integral good bases remain bases after arbitrary base change

The source coefficient ring is a domain with the required factorial
inverted.  The target algebra is entirely arbitrary: it may have torsion,
nilpotents, or zero divisors.  The tensor-quotient equivalence identifies
the base-changed free basis with the same literal good exterior words.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]

def baseChangedGoodBasis (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    Module.Basis (GoodOddIndex k s) S (quotientDegree S k s) :=
  ((integralGoodBasis R k s hunit).baseChange S).map (quotientBaseChangeEquiv R S k s)

@[simp] theorem baseChangedGoodBasis_apply (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) (I : GoodOddIndex k s) :
    baseChangedGoodBasis R S k s hunit I = goodWord S k s I := by
  simp only [baseChangedGoodBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, integralGoodBasis_apply, goodWord,
    quotientBaseChangeEquiv_tmul_mk, powerMap_basis, one_smul]

/-- `ℤ[1/M!]`, with precisely `M=floor((k+1)/2)` as in the paper. -/
abbrev IntegralCoefficientRing (k : ℕ) :=
  Localization.Away (((k+1)/2).factorial : ℤ)

instance integralCoefficientRing_isDomain (k : ℕ) :
    IsDomain (IntegralCoefficientRing k) :=
  IsLocalization.Away.isDomain (S := IntegralCoefficientRing k)
    (x := (((k+1)/2).factorial : ℤ))
    (by exact_mod_cast Nat.factorial_ne_zero ((k+1)/2))

theorem integralCoefficientRing_factorial_unit (k : ℕ) :
    IsUnit (((k+1)/2).factorial : IntegralCoefficientRing k) := by
  simpa only [map_natCast, Int.cast_natCast] using
    (IsLocalization.Away.algebraMap_isUnit
      (S := IntegralCoefficientRing k) (((k+1)/2).factorial : ℤ))

/-- The integral good basis for the exact localization stated after
Theorem 7.1. -/
def paper_integral_good_basis (k s : ℕ) :
    Module.Basis (GoodOddIndex k s) (IntegralCoefficientRing k)
      (quotientDegree (IntegralCoefficientRing k) k s) :=
  integralGoodBasis (IntegralCoefficientRing k) k s
    (integralCoefficientRing_factorial_unit k)

/-- The same literal good-word basis for every algebra over the stated
integral coefficient ring, without any flatness or domain hypothesis. -/
def paper_integral_good_basis_after_base_change (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T] :
    Module.Basis (GoodOddIndex k s) T (quotientDegree T k s) :=
  baseChangedGoodBasis (IntegralCoefficientRing k) T k s
    (integralCoefficientRing_factorial_unit k)

@[simp] theorem paper_integral_good_basis_after_base_change_apply (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T]
    (I : GoodOddIndex k s) :
    paper_integral_good_basis_after_base_change k s T I = goodWord T k s I :=
  baseChangedGoodBasis_apply (IntegralCoefficientRing k) T k s _ I

end PaperVerification.AlternatingForms.IntegralOdd
