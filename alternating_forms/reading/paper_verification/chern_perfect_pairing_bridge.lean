module

public import PaperVerification.ChernPairingReflection
public import PaperVerification.ChernRectangleBounds
public import PaperVerification.ChernFinite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# From the rectangle to the actual Chern quotient pairing

The root-exponent reflection proves injectivity of the low-degree coefficient
subspace into the literal quotient. Once the independent complete-intersection
dimension calculation is supplied, that injection is an isomorphism and the
coefficient integral gives a nondegenerate bilinear form on the quotient.

The dimension premise in the bridge theorem is explicit: this file does not
assume or redefine any cohomology, Chow group, or geometric integration map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open RectangularReflection

/-- The actual commutative ring quotient by the Section 4 relation ideal. -/
abbrev ChernQuotientRing (s N : ℕ) :=
  MvPolynomial (Fin s) ℚ ⧸ chernRelationIdeal (K := ℚ) s N

instance chernQuotientRing_finite (s N : ℕ) :
    Module.Finite ℚ (ChernQuotientRing s N) :=
  chern_relation_quotient_finite s (2*(N-s)+1) (by omega)

/-- Ordinary total degree bounds define an actual linear subspace of Chern
polynomials; this is its natural map to the actual ring quotient. -/
def chernLowDegreeToQuotient (s N : ℕ) :
    restrictTotalDegree (Fin s) ℚ (2*(N-s)) →ₗ[ℚ] ChernQuotientRing s N :=
  (Ideal.Quotient.mkₐ ℚ (chernRelationIdeal (K := ℚ) s N)).toLinearMap.comp
    (restrictTotalDegree (Fin s) ℚ (2*(N-s))).subtype

@[simp] theorem chernLowDegreeToQuotient_apply {s N : ℕ}
    (P : restrictTotalDegree (Fin s) ℚ (2*(N-s))) :
    chernLowDegreeToQuotient s N P =
      Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P := rfl

/-- The rectangle injects into the quotient by the nonzero coefficient pairing,
without using any dimension calculation. -/
theorem chernLowDegreeToQuotient_injective {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    Function.Injective (chernLowDegreeToQuotient s N) := by
  intro P Q hPQ
  simp only [chernLowDegreeToQuotient_apply] at hPQ
  apply Subtype.ext
  by_contra hne
  have hdiffne : (P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ) ≠ 0 :=
    sub_ne_zero.mpr hne
  have hmem : (P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ) ∈
      chernRelationIdeal (K := ℚ) s N := by
    apply Ideal.Quotient.eq.mp
    exact hPQ
  have hdegree : ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ)).totalDegree
      ≤ 2*(N-s) :=
    (mem_restrictTotalDegree (Fin s) (2*(N-s))
      ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ))).mp
        ((restrictTotalDegree (Fin s) ℚ (2*(N-s))).sub_mem P.property Q.property)
  have hbound : BoundedBy (uniformExponent (2*(N-s)))
      (elementarySubstitution s
        ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ))) :=
    elementarySubstitution_bounded_of_totalDegree
      (s := s) (c := 2*(N-s)) _ hdegree
  exact chernRectangular_not_mem_relationIdeal (s := s) (N := N)
    hs hsN _ hbound hdiffne hmem

/-- The normalized polynomial coefficient functional on the actual ring quotient. -/
def chernRingIntegration {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    ChernQuotientRing s N →ₗ[ℚ] ℚ :=
  (chernQuotientIntegration (K := ℚ) hs hsN).comp
    (Submodule.Quotient.restrictScalarsEquiv ℚ
      (chernRelationIdeal (K := ℚ) s N)).symm.toLinearMap

@[simp] theorem chernRingIntegration_mk {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (P : MvPolynomial (Fin s) ℚ) :
    chernRingIntegration hs hsN
      (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P) =
        chernCoefficientIntegration N P := rfl

/-- Multiplication followed by the descended coefficient functional. -/
def chernRingPairing {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    LinearMap.BilinForm ℚ (ChernQuotientRing s N) :=
  (LinearMap.mul ℚ (ChernQuotientRing s N)).compr₂ (chernRingIntegration hs hsN)

@[simp] theorem chernRingPairing_apply {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (x y : ChernQuotientRing s N) :
    chernRingPairing hs hsN x y = chernRingIntegration hs hsN (x*y) := rfl

@[simp] theorem chernRingPairing_mk {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (P Q : MvPolynomial (Fin s) ℚ) :
    chernRingPairing hs hsN
      (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P)
      (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) Q) =
        chernCoefficientIntegration N (P*Q) := by
  rw [chernRingPairing_apply, ← map_mul, chernRingIntegration_mk]

/-- Equal dimensions turn the independently proved rectangle injection into
surjectivity. The premise is the separate complete-intersection calculation. -/
theorem chernLowDegreeToQuotient_surjective_of_finrank {s N : ℕ}
    (hs : 0<s) (hsN : s≤N)
    (hdim : Module.finrank ℚ (ChernQuotientRing s N) = (2*(N-s)+s).choose s) :
    Function.Surjective (chernLowDegreeToQuotient s N) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := chernLowDegreeToQuotient s N) ?_).mp
    (chernLowDegreeToQuotient_injective hs hsN)
  rw [PaperVerification.finrank_restrictTotalDegree, hdim]

/-- The actual quotient coefficient pairing is nondegenerate once the
independent finite-dimensional quotient calculation has been established. -/
theorem chernRingPairing_nondegenerate_of_finrank {s N : ℕ}
    (hs : 0<s) (hsN : s≤N)
    (hdim : Module.finrank ℚ (ChernQuotientRing s N) = (2*(N-s)+s).choose s) :
    (chernRingPairing hs hsN).Nondegenerate := by
  have hsym : (chernRingPairing hs hsN).IsSymm := ⟨fun x y => by
    simp only [chernRingPairing_apply, mul_comm]⟩
  apply hsym.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  obtain ⟨P,rfl⟩ := chernLowDegreeToQuotient_surjective_of_finrank hs hsN hdim x
  by_contra hne
  have hpne : (P : MvPolynomial (Fin s) ℚ) ≠ 0 := by
    intro hz
    apply hne
    simp only [chernLowDegreeToQuotient_apply, hz, map_zero]
  have hpbound : BoundedBy (uniformExponent (2*(N-s)))
      (elementarySubstitution s (P : MvPolynomial (Fin s) ℚ)) :=
    elementarySubstitution_bounded_of_totalDegree
      (c := 2*(N-s)) (P : MvPolynomial (Fin s) ℚ)
      ((mem_restrictTotalDegree (Fin s) (2*(N-s))
        (P : MvPolynomial (Fin s) ℚ)).mp P.property)
  have hpair := hx (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N)
    (chernCoefficientReflection s N P))
  rw [chernLowDegreeToQuotient_apply, chernRingPairing_mk] at hpair
  exact chernCoefficientIntegration_reflection_ne_zero hs hsN P hpbound hpne hpair

end PaperVerification.AlternatingForms
