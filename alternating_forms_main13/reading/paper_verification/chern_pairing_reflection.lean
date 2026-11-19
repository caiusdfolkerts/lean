module

public import PaperVerification.RectangularReflection
public import PaperVerification.AlternatingFormsChernQuotientPairing

/-!
# Rectangular nondegeneracy of the actual Chern coefficient pairing

The coefficient integral is nondegenerate on symmetric polynomials whose
degree in each root is at most `2 * (N-s)`.  Reversing these root exponents
turns the product with the Vandermonde into its coefficient dual.  Its top
coefficient is therefore a nonzero sum of rational squares.

This is a statement about the independently defined polynomial integral.
It does not identify that integral with a geometric pushforward or define
the singular cohomology or Chow ring by the desired presentation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Finset
open RectangularReflection
open scoped BigOperators

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

theorem permutedPowerProduct_eq_monomial (a : σ → ℕ) (τ : Equiv.Perm σ) :
    (∏ i, (X (τ i) : MvPolynomial σ R)^a i) =
      monomial (Finsupp.equivFunOnFinite.symm (a ∘ τ.symm)) 1 := by
  have hp : (∏ i, (X (τ i) : MvPolynomial σ R)^a i) =
      ∏ i, (X i : MvPolynomial σ R)^a (τ.symm i) := by
    rw [← Equiv.prod_comp τ (fun i => (X i : MvPolynomial σ R)^a (τ.symm i))]
    simp
  rw [hp, prod_X_pow]
  apply congrArg (fun e : σ →₀ ℕ => monomial e (1 : R))
  ext i
  simp [Function.comp_def]

/-- Reflection reverses every exponent of an alternant, before any
regularity or nonvanishing statement is used. -/
theorem reflect_alternant (d : ℕ) (a : σ → ℕ) :
    reflect (uniformExponent d) (TauCeti.alternant σ R a) =
      TauCeti.alternant σ R (fun i => d-a i) := by
  rw [TauCeti.alternant_eq_sum, TauCeti.alternant_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [map_zsmul_unit]
  apply congrArg (fun p : MvPolynomial σ R => Equiv.Perm.sign τ • p)
  rw [permutedPowerProduct_eq_monomial, permutedPowerProduct_eq_monomial,
    reflect_monomial]
  apply congrArg (fun e : σ →₀ ℕ => monomial e (1 : R))
  ext i
  rfl

theorem boundedBy_alternant (d : ℕ) (a : σ → ℕ) (ha : ∀ i, a i ≤ d) :
    BoundedBy (uniformExponent d) (TauCeti.alternant σ R a) := by
  intro b hb
  have hcoeff := mem_support_iff.mp hb
  rw [TauCeti.coeff_alternant] at hcoeff
  obtain ⟨τ,hτ,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have heq := (Finset.mem_filter.mp hτ).2
  intro i
  obtain ⟨j,rfl⟩ := τ.surjective i
  have hj : b (τ j) = a j := congrFun heq j
  change b (τ j) ≤ d
  rw [hj]
  exact ha j

theorem expand_alternant (d : ℕ) (a : σ → ℕ) :
    expand d (TauCeti.alternant σ R a) =
      TauCeti.alternant σ R (fun i => d*a i) := by
  rw [TauCeti.alternant_def, TauCeti.alternant_def, AlgHom.map_det]
  congr 1
  ext i j
  simp [pow_mul]

theorem expandedVandermonde_bounded (s : ℕ) :
    BoundedBy (uniformExponent (2*(s-1)))
      (expand 2 (chernVandermonde (R := R) s)) := by
  rw [chernVandermonde, expand_alternant]
  apply boundedBy_alternant
  intro i
  exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)

/-- The reversal sign is an actual permutation sign; its nonvanishing
does not require a separate sign-convention calculation. -/
theorem reflect_expandedVandermonde (s : ℕ) :
    reflect (uniformExponent (2*(s-1)))
        (expand 2 (chernVandermonde (R := R) s)) =
      Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) •
        expand 2 (chernVandermonde (R := R) s) := by
  rw [chernVandermonde, expand_alternant, reflect_alternant]
  have hexp : (fun i : Fin s => 2*(s-1)-2*(s-1-i.val)) =
      (fun i : Fin s => 2*(s-1-i.val)) ∘ Fin.revPerm := by
    funext i
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    have hi := i.isLt
    omega
  rw [hexp, TauCeti.alternant_comp_perm]

theorem expandedVandermonde_ne_zero [Nontrivial R] (s : ℕ) :
    expand 2 (chernVandermonde (R := R) s) ≠ 0 := by
  rw [← map_zero (expand (R := R) (σ := Fin s) 2)]
  apply (expand_injective (R := R) (σ := Fin s) (by decide : 0<2)).ne
  exact TauCeti.alternant_ne_zero_of_injective (TauCeti.injective_staircase s)

section CoefficientNondegeneracy

variable {s N : ℕ}

/-- A nonzero symmetric polynomial in the rectangle has a nonzero
partner for the actual root-coordinate integration functional. -/
theorem chernIntegrationCoefficient_reflection_ne_zero
    (hs : 0<s) (hsN : s≤N) (p : MvPolynomial (Fin s) ℚ)
    (hbound : BoundedBy (uniformExponent (2*(N-s))) p) (hne : p≠0) :
    chernIntegrationCoefficient N
      (p * reflect (uniformExponent (2*(N-s))) p) ≠ 0 := by
  let v : MvPolynomial (Fin s) ℚ := expand 2 (chernVandermonde s)
  let ε : ℤˣ := Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))
  have ht : uniformExponent (σ := Fin s) (2*(N-s)) +
      uniformExponent (2*(s-1)) = chernTopExponent s N := by
    ext i
    simp only [Finsupp.add_apply, uniformExponent_apply, chernTopExponent_apply]
    omega
  have hb : BoundedBy (chernTopExponent s N) (p*v) := by
    rw [← ht]
    exact boundedBy_mul hbound (expandedVandermonde_bounded s)
  have hn : p*v≠0 := mul_ne_zero hne (expandedVandermonde_ne_zero s)
  have hpositive := coeff_self_mul_reflect_pos hb hn
  have hreflect : reflect (chernTopExponent s N) (p*v) =
      ε • (reflect (uniformExponent (2*(N-s))) p * v) := by
    rw [← ht, reflect_mul hbound (expandedVandermonde_bounded s),
      reflect_expandedVandermonde]
    simp only [mul_smul_comm]
    rfl
  rw [hreflect, mul_smul_comm, coeff_smul] at hpositive
  have hprod : p*v*(reflect (uniformExponent (2*(N-s))) p*v) =
      (p*reflect (uniformExponent (2*(N-s))) p)*v^2 := by ring
  rw [hprod] at hpositive
  intro hz
  change ((p*reflect (uniformExponent (2*(N-s))) p)*v^2).coeff
      (chernTopExponent s N) = 0 at hz
  rw [hz, smul_zero] at hpositive
  exact (lt_irrefl 0) hpositive


/-- Elementary substitution has its image in the actual symmetric subalgebra. -/
theorem elementarySubstitution_isSymmetric (P : MvPolynomial (Fin s) ℚ) :
    (elementarySubstitution s P).IsSymmetric := by
  apply (MvPolynomial.mem_symmetricSubalgebra _).mp
  simpa only [MvPolynomial.esymmAlgHom_apply, elementarySubstitution] using
    (MvPolynomial.esymmAlgHom (Fin s) ℚ s P).property

/-- The root reflection expressed back in independent Chern coordinates by
Mathlib's proved fundamental theorem of symmetric polynomials. -/
noncomputable def chernCoefficientReflection (s N : ℕ)
    (P : MvPolynomial (Fin s) ℚ) : MvPolynomial (Fin s) ℚ :=
  (MvPolynomial.esymmAlgEquiv (Fin s) ℚ (Fintype.card_fin s)).symm
    ⟨reflect (uniformExponent (2*(N-s))) (elementarySubstitution s P),
      reflect_isSymmetric (elementarySubstitution_isSymmetric P) _⟩

theorem chernCoefficientReflection_substitution (P : MvPolynomial (Fin s) ℚ) :
    elementarySubstitution s (chernCoefficientReflection s N P) =
      reflect (uniformExponent (2*(N-s))) (elementarySubstitution s P) := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin s) ℚ (Fintype.card_fin s)).apply_symm_apply
    ⟨reflect (uniformExponent (2*(N-s))) (elementarySubstitution s P),
      reflect_isSymmetric (elementarySubstitution_isSymmetric P) _⟩
  have hv := congrArg Subtype.val h
  change (MvPolynomial.esymmAlgHom (Fin s) ℚ s
    (chernCoefficientReflection s N P)).val = _ at hv
  simpa only [MvPolynomial.esymmAlgHom_apply, elementarySubstitution] using hv

/-- Reflection supplies a partner with nonzero normalized coefficient pairing
for every nonzero Chern polynomial with rectangular root support. -/
theorem chernCoefficientIntegration_reflection_ne_zero
    (hs : 0<s) (hsN : s≤N) (P : MvPolynomial (Fin s) ℚ)
    (hbound : BoundedBy (uniformExponent (2*(N-s))) (elementarySubstitution s P))
    (hne : P≠0) :
    chernCoefficientIntegration N (P * chernCoefficientReflection s N P) ≠ 0 := by
  unfold chernCoefficientIntegration
  change ((-1 : ℚ)^s.choose 2 / (s.factorial : ℚ)) *
    chernIntegrationCoefficient N
      (elementarySubstitution s (P * chernCoefficientReflection s N P)) ≠ 0
  rw [map_mul, chernCoefficientReflection_substitution]
  apply mul_ne_zero
  · exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))
  · apply chernIntegrationCoefficient_reflection_ne_zero hs hsN _ hbound
    exact fun h => hne ((elementarySubstitution_injective s)
      (h.trans (map_zero (elementarySubstitution s)).symm))

/-- No nonzero Chern polynomial supported in the root rectangle belongs to
the actual relation ideal. This is a proved injection into the quotient. -/
theorem chernRectangular_not_mem_relationIdeal
    (hs : 0<s) (hsN : s≤N) (P : MvPolynomial (Fin s) ℚ)
    (hbound : BoundedBy (uniformExponent (2*(N-s))) (elementarySubstitution s P))
    (hne : P≠0) : P ∉ chernRelationIdeal (K := ℚ) s N := by
  intro hP
  exact chernCoefficientIntegration_reflection_ne_zero hs hsN P hbound hne
    (chernCoefficientIntegration_ideal_zero hs hsN _
      ((chernRelationIdeal (K := ℚ) s N).mul_mem_right
        (chernCoefficientReflection s N P) hP))

end CoefficientNondegeneracy

end PaperVerification.AlternatingForms
