module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Ring

/-!
# A regular pair and the intersection of its two principal localizations

These statements use the actual principal ideal quotient, localization rings,
and fraction field. If x is regular and y remains regular modulo x, a power
of y cannot introduce divisibility by any power of x. In a domain, an element
of the fraction field that lies in both R[1/x] and R[1/y] therefore lies in R.

This is the algebraic extension argument needed for genuine global sections
on a homogeneous coordinate ring with a regular pair of degree-one elements.
It does not itself identify any projective sheaf or certify a paper theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.RegularPairLocalizationIntersection

variable {R : Type*} [CommRing R]

/-- Regularity in the literal principal-ideal quotient cancels one multiplier
from divisibility by the generator. -/
theorem dvd_of_regular_mod_span {x y r : R}
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (h : x ∣ y * r) : x ∣ r := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hy.left
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  simpa only [map_mul, mul_zero] using hz

/-- A regular element may be replaced by any power in this cancellation
statement, without assuming unique factorization or primality of its ideal. -/
theorem pow_dvd_mul_iff {x y : R} (hx : IsRegular x)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (a : ℕ) (r : R) : x ^ a ∣ y * r ↔ x ^ a ∣ r := by
  induction a generalizing r with
  | zero => simp
  | succ a ih =>
    constructor
    · intro h
      have hxdiv : x ∣ y * r := (dvd_pow_self x (Nat.succ_ne_zero a)).trans h
      obtain ⟨c, rfl⟩ := dvd_of_regular_mod_span hy hxdiv
      obtain ⟨d, hd⟩ := h
      have hc : y * c = x ^ a * d := hx.left (by
        change x * (y * c) = x * (x ^ a * d)
        calc
          x * (y * c) = y * (x * c) := by ring
          _ = x ^ (a + 1) * d := hd
          _ = x * (x ^ a * d) := by rw [pow_succ]; ring)
      obtain ⟨e, he⟩ := (ih c).mp ⟨d, hc⟩
      refine ⟨e, ?_⟩
      rw [he, pow_succ]
      ring
    · rintro ⟨c, hc⟩
      refine ⟨y * c, ?_⟩
      rw [hc]
      ring

/-- The exact power-divisibility consequence of a regular pair. -/
theorem pow_dvd_pow_mul_iff {x y : R} (hx : IsRegular x)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (a b : ℕ) (r : R) : x ^ a ∣ y ^ b * r ↔ x ^ a ∣ r := by
  apply pow_dvd_mul_iff hx
  simpa only [map_pow] using (IsRegular.pow b hy)

section FractionField

variable [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

theorem fractionMap_ne_zero {x : R} (hx : x ≠ 0) :
    algebraMap R F x ≠ 0 := by
  intro h
  exact hx ((IsFractionRing.injective R F) (h.trans (map_zero (algebraMap R F)).symm))

/-- Two genuine denominator representations with a regular pair force a
fraction to have denominator one. -/
theorem exists_eq_algebraMap_of_two_power_denominators
    {x y : R} (hx : x ≠ 0)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (z : F) (a b : ℕ) (r s : R)
    (hr : z * algebraMap R F (x ^ a) = algebraMap R F r)
    (hs : z * algebraMap R F (y ^ b) = algebraMap R F s) :
    ∃ q : R, algebraMap R F q = z := by
  have hrel : y ^ b * r = x ^ a * s := by
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, ← hr, ← hs]
    ring
  have hdiv : x ^ a ∣ r :=
    (pow_dvd_pow_mul_iff (isRegular_iff_ne_zero.mpr hx) hy a b r).mp ⟨s, hrel⟩
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, ?_⟩
  apply mul_right_cancel₀ (fractionMap_ne_zero (F := F) (pow_ne_zero a hx))
  calc
    algebraMap R F q * algebraMap R F (x ^ a) =
        algebraMap R F (x ^ a * q) := by rw [map_mul]; ring
    _ = algebraMap R F r := congrArg (algebraMap R F) hq.symm
    _ = z * algebraMap R F (x ^ a) := hr.symm

/-- The canonical homomorphism from the actual localization away from x to
its fraction field, induced by the original algebra map. -/
def awayToFraction (x : R) (hx : x ≠ 0) : Localization.Away x →+* F :=
  IsLocalization.Away.lift x (g := algebraMap R F)
    (isUnit_iff_ne_zero.mpr (fractionMap_ne_zero hx))

@[simp]
theorem awayToFraction_algebraMap (x : R) (hx : x ≠ 0) (r : R) :
    awayToFraction (F := F) x hx (algebraMap R (Localization.Away x) r) =
      algebraMap R F r := by
  exact IsLocalization.Away.lift_eq x _ r

/-- A fraction in the image of the actual principal localization has an
actual power-denominator representation. -/
theorem exists_power_denominator_of_mem_range
    (x : R) (hx : x ≠ 0) (z : F)
    (hz : z ∈ Set.range (awayToFraction (F := F) x hx)) :
    ∃ (a : ℕ) (r : R), z * algebraMap R F (x ^ a) = algebraMap R F r := by
  obtain ⟨t, rfl⟩ := hz
  refine ⟨(IsLocalization.Away.sec x t).2, (IsLocalization.Away.sec x t).1, ?_⟩
  have h := congrArg (awayToFraction (F := F) x hx) (IsLocalization.Away.sec_spec x t)
  simpa only [map_mul, awayToFraction_algebraMap] using h

/-- A regular pair recovers the original domain as the intersection of the
images of its two actual principal localizations inside the fraction field. -/
theorem intersection_range_eq (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hregular : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y)) :
    Set.range (awayToFraction (F := F) x hx) ∩
        Set.range (awayToFraction (F := F) y hy) =
      Set.range (algebraMap R F) := by
  ext z
  constructor
  · rintro ⟨hzx, hzy⟩
    obtain ⟨a, r, hr⟩ := exists_power_denominator_of_mem_range x hx z hzx
    obtain ⟨b, s, hs⟩ := exists_power_denominator_of_mem_range y hy z hzy
    exact exists_eq_algebraMap_of_two_power_denominators hx hregular z a b r s hr hs
  · rintro ⟨r, rfl⟩
    exact ⟨⟨algebraMap R (Localization.Away x) r, awayToFraction_algebraMap x hx r⟩,
      ⟨algebraMap R (Localization.Away y) r, awayToFraction_algebraMap y hy r⟩⟩

end FractionField
end PaperVerification.RegularPairLocalizationIntersection
