module

public import PaperVerification.ChernQuotientDuality

/-!
# A precise presentation criterion for the Chern algebra

This is an algebraic comparison theorem. Its target is an independently given
commutative rational algebra, its evaluation map is independently given, and
both its dimension and its trace identity are explicit hypotheses. Applying it
to the actual cohomology or Chow ring requires constructing that ring and proving
those geometric hypotheses; this theorem does not assume that application.

The criterion derives generation and all relations at once. It does not require
Poincaré duality of the target as an additional hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

/-- An independent finite-dimensional algebra with the correct tautological
integration identity is the actual Chern-relation quotient. The equivalence
agrees with the given evaluation map on every polynomial, not only on dimensions. -/
theorem chernPresentationCriterion
    {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    {H : Type*} [CommRing H] [Algebra ℚ H] [Module.Finite ℚ H]
    (τ : MvPolynomial (Fin s) ℚ →ₐ[ℚ] H) (trace : H →ₗ[ℚ] ℚ)
    (hdim : Module.finrank ℚ H = (2*(N-s)+s).choose s)
    (htrace : ∀ P : MvPolynomial (Fin s) ℚ,
      trace (τ P) = chernCoefficientIntegration N P) :
    ∃ e : ChernQuotientRing s N ≃ₐ[ℚ] H,
      ∀ P : MvPolynomial (Fin s) ℚ,
        e (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P) = τ P := by
  let T : restrictTotalDegree (Fin s) ℚ (2*(N-s)) →ₗ[ℚ] H :=
    τ.toLinearMap.comp (restrictTotalDegree (Fin s) ℚ (2*(N-s))).subtype
  have hker₁ : RingHom.ker τ.toRingHom ≤ chernRelationIdeal (K := ℚ) s N := by
    intro P hP
    change τ P = 0 at hP
    rw [mem_chernRelationIdeal_iff_integration_mul_eq_zero hs hsN]
    intro Q
    rw [← htrace, map_mul, hP, zero_mul, map_zero]
  have hinj : Function.Injective T := by
    intro P Q hPQ
    change τ (P : MvPolynomial (Fin s) ℚ) =
      τ (Q : MvPolynomial (Fin s) ℚ) at hPQ
    apply chernLowDegreeToQuotient_injective hs hsN
    apply Ideal.Quotient.eq.mpr
    apply hker₁
    change τ ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ)) = 0
    rw [map_sub,hPQ,sub_self]
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := T)
      (by rw [PaperVerification.finrank_restrictTotalDegree, hdim])).mp hinj
  have hker₂ : chernRelationIdeal (K := ℚ) s N ≤ RingHom.ker τ.toRingHom := by
    intro P hP
    change τ P = 0
    obtain ⟨Q,hQ⟩ := hsurj (τ P)
    change τ (Q : MvPolynomial (Fin s) ℚ) = τ P at hQ
    have hQmem : (Q : MvPolynomial (Fin s) ℚ) ∈
        chernRelationIdeal (K := ℚ) s N := by
      rw [mem_chernRelationIdeal_iff_integration_mul_eq_zero hs hsN]
      intro R
      have heq : τ ((Q : MvPolynomial (Fin s) ℚ)*R) = τ (P*R) := by
        rw [map_mul, map_mul, hQ]
      rw [← htrace, heq, htrace]
      exact chernCoefficientIntegration_ideal_zero hs hsN (P*R)
        (Ideal.mul_mem_right _ _ hP)
    have hQzero : Q = 0 := by
      apply chernLowDegreeToQuotient_injective hs hsN
      rw [map_zero, chernLowDegreeToQuotient_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hQmem
    rw [← hQ, hQzero]
    exact map_zero τ
  let f : ChernQuotientRing s N →ₐ[ℚ] H :=
    Ideal.Quotient.liftₐ (chernRelationIdeal (K := ℚ) s N) τ hker₂
  have hf_inj : Function.Injective f :=
    RingHom.lift_injective_of_ker_le_ideal
      (chernRelationIdeal (K := ℚ) s N) hker₂ hker₁
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨P,hP⟩ := hsurj x
    exact ⟨Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P, hP⟩
  exact ⟨AlgEquiv.ofBijective f ⟨hf_inj,hf_surj⟩, fun _ => rfl⟩

end PaperVerification.AlternatingForms
