module

public import PaperVerification.ChernPerfectPairingBridge
public import PaperVerification.AlternatingFormsChernDimension

/-!
# Perfect duality for the actual Chern-relation quotient

The polynomial quotient and coefficient functional were defined independently.
The common-zero calculation, regular sequence theorem and graded dimension
calculation now close the dimension premise in the reflection argument.
Consequently the descended multiplication pairing is perfect over `ℚ`, for
all parameters `0 < s ≤ N` of Section 4.

The annihilator theorem characterizes the literal relation ideal by the actual
coefficient integral. No cohomology or Chow group is defined in this file.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

/-- The dimension of the literal quotient in the odd-pencil range. -/
theorem chernQuotientRing_finrank (s N : ℕ) :
    Module.finrank ℚ (ChernQuotientRing s N) = (2*(N-s)+s).choose s :=
  odd_chern_relation_quotient_finrank (K := ℚ) s N

/-- Every quotient class has a unique representative of ordinary total degree
at most `2*(N-s)` in the independent Chern variables. -/
theorem chernLowDegreeToQuotient_bijective {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    Function.Bijective (chernLowDegreeToQuotient s N) :=
  ⟨chernLowDegreeToQuotient_injective hs hsN,
    chernLowDegreeToQuotient_surjective_of_finrank hs hsN
      (chernQuotientRing_finrank s N)⟩

/-- The actual low-degree representative space is linearly equivalent to the
actual quotient; this does not identify either space with geometric cohomology. -/
def chernLowDegreeEquiv {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    restrictTotalDegree (Fin s) ℚ (2*(N-s)) ≃ₗ[ℚ] ChernQuotientRing s N :=
  LinearEquiv.ofBijective (chernLowDegreeToQuotient s N)
    (chernLowDegreeToQuotient_bijective hs hsN)

/-- Multiplication followed by the actual coefficient integral is nondegenerate. -/
theorem chernRingPairing_nondegenerate {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    (chernRingPairing hs hsN).Nondegenerate :=
  chernRingPairing_nondegenerate_of_finrank hs hsN (chernQuotientRing_finrank s N)

/-- Perfect duality, as an actual equivalence with the vector-space dual. -/
def chernRingPerfectPairing {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    ChernQuotientRing s N ≃ₗ[ℚ] Module.Dual ℚ (ChernQuotientRing s N) :=
  (chernRingPairing hs hsN).toDual (chernRingPairing_nondegenerate hs hsN)

@[simp] theorem chernRingPerfectPairing_apply {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (x y : ChernQuotientRing s N) :
    chernRingPerfectPairing hs hsN x y = chernRingIntegration hs hsN (x*y) := rfl

/-- A Chern polynomial belongs to the relation ideal exactly when every
product with it has zero coefficient integral. -/
theorem mem_chernRelationIdeal_iff_integration_mul_eq_zero
    {s N : ℕ} (hs : 0<s) (hsN : s≤N) (P : MvPolynomial (Fin s) ℚ) :
    P ∈ chernRelationIdeal (K := ℚ) s N ↔
      ∀ Q : MvPolynomial (Fin s) ℚ, chernCoefficientIntegration N (P*Q) = 0 := by
  constructor
  · intro hP Q
    exact chernCoefficientIntegration_ideal_zero hs hsN (P*Q)
      (Ideal.mul_mem_right _ _ hP)
  · intro hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (chernRingPairing_nondegenerate hs hsN).1
    intro q
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [chernRingPairing_mk]
    exact hP Q

/-- Every later root relation also belongs to the same finite-window ideal. -/
theorem chernCoefficientRelation_mem_chernRelationIdeal
    {s N n : ℕ} (hs : 0<s) (hsN : s≤N) (hn : 2*(N-s)+1≤n) :
    chernCoefficientRelation (K := ℚ) s n ∈ chernRelationIdeal (K := ℚ) s N := by
  rw [mem_chernRelationIdeal_iff_integration_mul_eq_zero hs hsN]
  intro Q
  rw [mul_comm]
  exact chernCoefficientRelation_annihilates hs hsN hn Q

end PaperVerification.AlternatingForms
