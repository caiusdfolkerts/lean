module

public import PaperVerification.FermionFrobenius
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# A one-dimensional socle gives the actual multiplication pairing

The nilpotent-ideal argument below proves that every nonzero principal ideal
meets the socle. Consequently a functional nonzero on a one-dimensional socle
separates all elements by multiplication. This supplies the elementary
Frobenius step after the determinant annihilator formula; no Gorenstein
assertion or Jacobian formula is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

section Ring

variable {A : Type*} [CommRing A]

/-- Every nonzero principal ideal meets the annihilator of a nilpotent ideal. -/
theorem exists_nonzero_annihilated_mul (m : Ideal A)
    (hm : IsNilpotent m) (a : A) (ha : a ≠ 0) :
    ∃ b : A, a * b ≠ 0 ∧ ∀ r ∈ m, r * (a * b) = 0 := by
  classical
  obtain ⟨N, hN⟩ := hm
  have hex : ∃ n : ℕ, m ^ n * Ideal.span {a} = ⊥ := by
    refine ⟨N, ?_⟩
    rw [hN, zero_mul]
    rfl
  let n := Nat.find hex
  have hn : m ^ n * Ideal.span {a} = ⊥ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero, one_mul] at hn
    exact ha (Ideal.span_singleton_eq_bot.mp hn)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : m ^ k * Ideal.span {a} ≠ ⊥ := by
    exact Nat.find_min hex (by change k < n; omega)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprev
  obtain ⟨b, hb, hbx⟩ := Ideal.mem_mul_span_singleton.mp hx
  refine ⟨b, ?_, ?_⟩
  · simpa only [mul_comm a b, hbx] using hx0
  · intro r hr
    have hrx : r * x ∈ m * (m ^ k * Ideal.span {a}) := Ideal.mul_mem_mul hr hx
    have hzero : m * (m ^ k * Ideal.span {a}) = ⊥ := by
      rw [← mul_assoc, ← pow_succ']
      simpa only [hk] using hn
    rw [hzero, Ideal.mem_bot] at hrx
    simpa only [mul_comm a b, hbx] using hrx

end Ring

section Field

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Multiplication followed by a linear functional, as an actual bilinear form. -/
def multiplicationPairing (ε : A →ₗ[K] K) : A →ₗ[K] A →ₗ[K] K :=
  (LinearMap.mul K A).compr₂ ε

@[simp]
theorem multiplicationPairing_apply (ε : A →ₗ[K] K) (a b : A) :
    multiplicationPairing ε a b = ε (a * b) := rfl

/-- A functional nonzero on a one-dimensional socle separates every element
of the original algebra by multiplication. -/
theorem multiplication_separating_of_socle
    (m : Ideal A) (hm : IsNilpotent m) (s : A)
    (hs : ∀ x : A, (∀ r ∈ m, r * x = 0) → ∃ c : K, x = c • s)
    (ε : A →ₗ[K] K) (hε : ε s ≠ 0) (a : A)
    (ha : ∀ b : A, ε (a * b) = 0) : a = 0 := by
  by_contra ha0
  obtain ⟨b, hab, hb⟩ := exists_nonzero_annihilated_mul m hm a ha0
  obtain ⟨c, hc⟩ := hs (a * b) hb
  have hc0 : c ≠ 0 := by
    intro h
    exact hab (by simpa only [h, zero_smul] using hc)
  have hprod : c * ε s = 0 := by
    simpa only [hc, map_smul, smul_eq_mul] using ha b
  exact mul_ne_zero hc0 hε hprod

/-- Finite-dimensionality turns the socle separation into a perfect pairing. -/
theorem multiplicationPairing_isPerfPair_of_socle [Module.Finite K A]
    (m : Ideal A) (hm : IsNilpotent m) (s : A)
    (hs : ∀ x : A, (∀ r ∈ m, r * x = 0) → ∃ c : K, x = c • s)
    (ε : A →ₗ[K] K) (hε : ε s ≠ 0) :
    (multiplicationPairing ε).IsPerfPair := by
  have hinj : Function.Injective (multiplicationPairing ε) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    apply multiplication_separating_of_socle m hm s hs ε hε a
    intro b
    exact LinearMap.congr_fun ha b
  have hflip : (multiplicationPairing ε).flip = multiplicationPairing ε := by
    ext a b
    exact congrArg ε (mul_comm b a)
  apply LinearMap.IsPerfPair.of_injective hinj
  rwa [hflip]

end Field

end PaperVerification.Fermion
